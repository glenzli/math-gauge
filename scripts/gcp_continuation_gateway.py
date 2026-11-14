"""Loopback adapter for native GCP generations with same-context continuation.

This evaluator-operated transport executes no candidate tools and makes no
scoring or attempt-selection decisions. See docs/gcp-continuation.md.
"""
from pathlib import Path
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from importlib.metadata import version
import argparse
import base64
import copy
import datetime
import hashlib
import json
import os
import queue
import re
import threading
import time

import httpx

OUT = SESSION = ADC = None
KEY = PROJECT = LOCATION = CANDIDATE_MODEL = THINKING_LEVEL = None
GUARD_MODELS = frozenset()
CAP = 262144
LIMIT = None
LOCK = threading.Lock()
MODEL_LOCK = threading.Lock()
CALLS = POSTS = INCOMING = REJECTIONS = 0
STARTED = None
SPENT = 0
TERMINAL = False
EXPECTED_TOOLS = set()
_CONFIGURED = False


def configure(args):
    """Configure exactly one physical attempt in this process; never resume it."""
    global OUT, SESSION, ADC, KEY, PROJECT, LOCATION, CANDIDATE_MODEL
    global THINKING_LEVEL, GUARD_MODELS, CAP, LIMIT, _CONFIGURED
    if _CONFIGURED:
        raise RuntimeError('One transport process belongs to one physical attempt')
    if args.deadline_seconds <= 0 or args.max_output_tokens <= 0:
        raise ValueError('Positive frozen deadline and per-generation budget required')
    if not re.fullmatch(r'[A-Za-z0-9._-]+', args.candidate_model):
        raise ValueError('A native model identifier is required')
    KEY = Path(args.key_file).read_text().strip()
    if not KEY:
        raise ValueError('Empty loopback transport credential')
    OUT, SESSION, ADC = Path(args.out), Path(args.session), Path(args.credential_file)
    if not ADC.is_file() or not (SESSION / 'input/task.md').is_file():
        raise ValueError('Original native task and existing GCP credential file required')
    OUT.mkdir(mode=0o700)
    PROJECT, LOCATION = args.project, args.location
    CANDIDATE_MODEL = args.candidate_model
    THINKING_LEVEL = args.thinking_level.upper()
    GUARD_MODELS = frozenset(args.guard_model)
    if CANDIDATE_MODEL in GUARD_MODELS:
        raise ValueError('Candidate and native safety-rater model identities overlap')
    CAP, LIMIT = args.max_output_tokens, args.deadline_seconds
    _CONFIGURED = True


def utc():
    return datetime.datetime.now(datetime.timezone.utc).isoformat()


def dump(path, value):
    with Path(path).open('x') as f:
        json.dump(value, f, ensure_ascii=False, indent=2)
        f.write('\n')


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def signature_bytes(value):
    """Compare opaque signatures as bytes, without changing their wire text."""
    if isinstance(value, list):
        return [signature_bytes(x) for x in value]
    if not isinstance(value, dict):
        return value
    result = {}
    for k, v in value.items():
        if k == 'thoughtSignature' and isinstance(v, str):
            result[k] = base64.b64decode(v + '=' * ((-len(v)) % 4), altchars=b'-_', validate=True)
        else:
            result[k] = signature_bytes(v)
    return result


def text_parts(value):
    if isinstance(value, dict):
        for k, v in value.items():
            if k == 'text' and isinstance(v, str):
                yield v
            else:
                yield from text_parts(v)
    elif isinstance(value, list):
        for item in value:
            yield from text_parts(item)


def function_responses(contents):
    return [p['functionResponse'] for c in contents for p in c.get('parts', [])
        if 'functionResponse' in p]


class TeeStream(httpx.SyncByteStream):
    def __init__(self, inner, path):
        self.inner, self.path = inner, path

    def __iter__(self):
        with self.path.open('xb') as f:
            for block in self.inner:
                f.write(block)
                f.flush()
                yield block

    def close(self):
        self.inner.close()


class CaptureTransport(httpx.BaseTransport):
    def __init__(self, inner, original, logical, model, lane):
        self.inner, self.original, self.logical = inner, original, logical
        self.model, self.lane = model, lane
        self.first_wire_tools = None
        self.hops = 0

    def handle_request(self, request):
        global POSTS
        if STARTED is not None and time.monotonic() - STARTED >= LIMIT:
            raise TimeoutError('Remaining cumulative attempt deadline reached')
        self.hops += 1
        if self.hops > 8:
            raise RuntimeError('Eight-hop safety bound reached for this generation')
        sdk_raw = request.read()
        body = json.loads(sdk_raw)
        # A continuation hop must retain the exact original model context/tools.
        assert signature_bytes(body.get('contents')) == signature_bytes(self.original.get('contents')), 'SDK changed model contents or signature bytes'
        def declarations(tools):
            # The official SDK combines separate Tool containers. Preserve every
            # declaration, its order and all schemas; no built-in network tool.
            assert all(set(t) == {'functionDeclarations'} for t in tools)
            return [d for t in tools for d in t['functionDeclarations']]
        def proto_schema(value, property_names=False):
            # Vertex's SDK represents protobuf int64 minLength as min_length/int.
            # Check that only this representation differs, then send the exact
            # native declarations rather than the SDK's schema serialization.
            if isinstance(value, list):
                return [proto_schema(x) for x in value]
            if not isinstance(value, dict):
                return value
            out = {}
            for key, item in value.items():
                name = 'minLength' if key == 'min_length' and not property_names else key
                out[name] = str(item) if name == 'minLength' and not property_names else proto_schema(item, key == 'properties')
            return out
        assert proto_schema(declarations(body.get('tools', []))) == proto_schema(declarations(self.original.get('tools', []))), 'SDK changed tool declaration semantics'
        sdk_body = body
        if self.lane == 'candidate':
            budget = sdk_body['generationConfig']['maxOutputTokens']
            thought = sdk_body['generationConfig']['thinkingConfig']
            assert thought.get('thinkingLevel', thought.get('thinking_level')) == THINKING_LEVEL
        # Forward the native original request, with only the declared output
        # budget and official SDK continuation token added. SDK field aliases
        # must never rewrite the agent's task, schemas or generation settings.
        body = copy.deepcopy(self.original)
        if self.lane == 'candidate':
            body['generationConfig']['maxOutputTokens'] = budget
        if sdk_body.get('continuationToken'):
            body['continuationToken'] = sdk_body['continuationToken']
        if self.first_wire_tools is None:
            self.first_wire_tools = copy.deepcopy(body.get('tools', []))
        else:
            assert body.get('tools', []) == self.first_wire_tools, 'Continuation changed wire tools'
        assert body.get('systemInstruction') == self.original.get('systemInstruction'), 'SDK changed system instruction'
        assert '/v1beta1/' in request.url.path, 'Cloud API version is not v1beta1'
        assert self.model + ':streamGenerateContent' in request.url.path
        if self.lane == 'candidate':
            assert body['generationConfig']['maxOutputTokens'] > 0
            assert body['generationConfig']['thinkingConfig']['thinkingLevel'] == THINKING_LEVEL
        with LOCK:
            POSTS += 1
            number = POSTS
        prefix = OUT / ('%03d-native' % number)
        prefix.with_suffix('.sdk-serialized-request.json').write_bytes(sdk_raw)
        raw = json.dumps(body, ensure_ascii=False, separators=(',', ':')).encode()
        prefix.with_suffix('.request.json').write_bytes(raw)
        dump(prefix.with_suffix('.dispatch.json'), {'utc': utc(), 'logical_generation': self.logical,
            'url': str(request.url), 'request_sha256': digest(raw),
            'contents_sha256': digest(json.dumps(body['contents'], sort_keys=True).encode()),
            'continuation_token_supplied': bool(body.get('continuationToken')),
            'continuation_token_sha256': digest(body['continuationToken'].encode()) if body.get('continuationToken') else None,
            'max_output_tokens': body.get('generationConfig', {}).get('maxOutputTokens'),
            'model': self.model, 'lane': self.lane,
            'authorization_headers_retained': False, 'fixture': False})
        request = httpx.Request(request.method, request.url,
            headers=[(k, v) for k, v in request.headers.raw if k.lower() != b'content-length'],
            content=raw, extensions=request.extensions)
        response = self.inner.handle_request(request)
        response.stream = TeeStream(response.stream, prefix.with_suffix('.response.sse'))
        dump(prefix.with_suffix('.status.json'), {'utc': utc(), 'status': response.status_code})
        return response

    def close(self):
        self.inner.close()


def generate(original, logical, output, model, lane):
    global SPENT, EXPECTED_TOOLS, TERMINAL
    cfg = copy.deepcopy(original.get('generationConfig', {}))
    remaining = CAP  # Per logical generation, not an attempt-wide token cap.
    assert remaining > 0
    if lane == 'candidate':
        cfg.update(maxOutputTokens=remaining, automaticContinuation=True)
    else:
        cfg['automaticContinuation'] = False
    for k in ('systemInstruction', 'tools', 'toolConfig', 'safetySettings', 'cachedContent', 'labels'):
        if k in original:
            cfg[k] = original[k]
    from google import genai
    from google.genai import types
    from google.oauth2.credentials import Credentials

    config = types.GenerateContentConfig.model_validate(cfg)
    credentials = Credentials.from_authorized_user_file(
        str(ADC), scopes=['https://www.googleapis.com/auth/cloud-platform'])
    inner = httpx.HTTPTransport(retries=0)
    project, location = PROJECT, LOCATION
    transport = CaptureTransport(inner, original, logical, model, lane)
    client = genai.Client(vertexai=True, project=project, location=location,
        credentials=credentials, http_options=types.HttpOptions(api_version='v1beta1',
            timeout=LIMIT * 1000, retry_options=types.HttpRetryOptions(attempts=1),
            client_args={'transport': transport, 'trust_env': False}))
    usage = None
    calls = set()
    reasons = []
    try:
        with (OUT / ('%03d-sdk-chunks.ndjson' % logical)).open('x') as f:
            for chunk in client.models.generate_content_stream(model=model,
                    contents=original['contents'], config=config):
                if STARTED is not None and time.monotonic() - STARTED >= LIMIT:
                    raise TimeoutError('Diagnostic deadline reached')
                data = chunk.model_dump(mode='json', by_alias=True, exclude_none=True)
                f.write(json.dumps(data, ensure_ascii=False) + '\n')
                f.flush()
                projected = {k: v for k, v in data.items() if k in {
                    'candidates', 'usageMetadata', 'modelVersion', 'responseId', 'promptFeedback', 'createTime'}}
                for candidate in projected.get('candidates', []):
                    if candidate.get('finishReason') == 'CONTINUATION':
                        candidate.pop('finishReason')
                    candidate.pop('continuationToken', None)
                    if candidate.get('finishReason'):
                        reasons.append(candidate['finishReason'])
                    for part in candidate.get('content', {}).get('parts', []):
                        if part.get('functionCall'):
                            calls.add(part['functionCall']['name'])
                if data.get('usageMetadata'):
                    usage = data['usageMetadata']
                output.put(projected)
        assert reasons and reasons[-1] in ('STOP', 'MAX_TOKENS'), 'No verified native finish reason'
        if lane == 'candidate':
            if usage:
                SPENT += int(usage.get('candidatesTokenCount', 0)) + int(usage.get('thoughtsTokenCount', 0))
            EXPECTED_TOOLS = calls
            TERMINAL = reasons[-1] == 'MAX_TOKENS'  # Only the native collector decides normal finality.
        dump(OUT / ('%03d-logical-result.json' % logical), {'utc': utc(),
            'finish_reasons': reasons, 'usage': usage, 'cumulative_output_tokens': SPENT,
            'next_tools': sorted(calls), 'model': model, 'lane': lane,
            'fixture': False})
    finally:
        client.close()


class Handler(BaseHTTPRequestHandler):
    protocol_version = 'HTTP/1.1'

    def send_error(self, code, message=None, explain=None):
        global REJECTIONS
        with LOCK:
            REJECTIONS += 1
            rejection = REJECTIONS
        dump(OUT / ('rejected-%03d.json' % rejection), {'utc': utc(), 'code': code, 'path': self.path, 'message': message, 'cloud_call_made_for_rejection': False})
        return super().send_error(code, message, explain)

    def log_message(self, *unused):
        pass

    def do_POST(self):
        global CALLS, STARTED, TERMINAL, INCOMING
        match = re.fullmatch(r'/v1beta/models/([A-Za-z0-9._-]+):streamGenerateContent\?alt=sse', self.path)
        if not match:
            self.send_error(404)
            return
        if self.headers.get('x-goog-api-key') != KEY and self.headers.get('Authorization') != 'Bearer ' + KEY:
            self.send_error(403)
            return
        model = match[1]
        if model not in {CANDIDATE_MODEL, *GUARD_MODELS}:
            self.send_error(404)
            return
        raw = self.rfile.read(int(self.headers.get('Content-Length', 0)))
        original = json.loads(raw)
        with LOCK:
            INCOMING += 1
            incoming = INCOMING
        (OUT / ('%03d-incoming-agy-request.json' % incoming)).write_bytes(raw)
        is_guard = not original.get('tools') and any(
            t.startswith('You are a safety and security rater overseeing Jetski')
            for t in text_parts(original.get('contents', [])))
        lane = 'native_safety_rater' if is_guard and model != CANDIDATE_MODEL else 'candidate'
        if (is_guard and model == CANDIDATE_MODEL) or (model != CANDIDATE_MODEL and not is_guard):
            self.send_error(400, 'Only the original native guard models may review tools')
            return
        if not MODEL_LOCK.acquire(timeout=30):
            self.send_error(409, 'A generation is already active')
            return
        try:
            if (TERMINAL or (SESSION.parent / 'native-terminal-seal.json').exists() or (SESSION.parent / 'no-native-terminal-seal.json').exists()) and lane == 'candidate':
                self.send_error(409, 'The native terminal or transport failure locked this attempt')
                return
            if lane == 'candidate':
                prompt = (SESSION / 'input/task.md').read_text()
                if not any(prompt in t for t in text_parts(original['contents'])):
                    self.send_error(400, 'This request is not the frozen attempt task')
                    return
                if EXPECTED_TOOLS and not EXPECTED_TOOLS.intersection(
                        r.get('name') for r in function_responses(original['contents'])):
                    self.send_error(400, 'Missing original tool responses')
                    return
            if STARTED is None:
                STARTED = time.monotonic()
            CALLS += 1
            logical = CALLS
            (OUT / ('%03d-agy-request.json' % logical)).write_bytes(raw)
            output = queue.Queue()
            def work():
                global TERMINAL
                try:
                    generate(original, logical, output, model, lane)
                except BaseException as error:
                    if lane == 'candidate':
                        TERMINAL = True
                    dump(OUT / ('%03d-error.json' % logical), {
                        'utc': utc(), 'type': type(error).__name__, 'message': str(error),
                        'model': model, 'lane': lane})
                    output.put(error)
                finally:
                    output.put(None)
            threading.Thread(target=work, daemon=True).start()
            self.send_response(200)
            self.send_header('Content-Type', 'text/event-stream')
            self.send_header('Cache-Control', 'no-cache')
            self.send_header('Connection', 'close')
            self.end_headers()
            while True:
                try:
                    value = output.get(timeout=10)
                except queue.Empty:
                    self.wfile.write(b': transport heartbeat\n\n')
                    self.wfile.flush()
                    continue
                if value is None:
                    break
                if isinstance(value, BaseException):
                    # Never synthesize a model answer, successful finish or continuation.
                    break
                self.wfile.write(b'data: ' + json.dumps(value, ensure_ascii=False).encode() + b'\n\n')
                self.wfile.flush()
        finally:
            self.close_connection = True
            MODEL_LOCK.release()


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out', required=True, help='New private operator evidence directory')
    parser.add_argument('--session', required=True, help='Existing isolated native session')
    parser.add_argument('--key-file', required=True, help='Existing local loopback credential file')
    parser.add_argument('--credential-file', required=True, help='Existing authorized-user GCP ADC file')
    parser.add_argument('--project', required=True)
    parser.add_argument('--location', required=True)
    parser.add_argument('--candidate-model', required=True)
    parser.add_argument('--guard-model', action='append', default=[])
    parser.add_argument('--thinking-level', required=True)
    parser.add_argument('--deadline-seconds', type=int, required=True)
    parser.add_argument('--max-output-tokens', type=int, default=262144)
    args = parser.parse_args(argv)
    sdk_version = version('google-genai')
    if sdk_version != '2.34.0':
        raise RuntimeError('This adapter requires the explicitly validated google-genai2.34.0')
    configure(args)
    server = ThreadingHTTPServer(('127.0.0.1', 0), Handler)
    dump(OUT / 'ready.json', {
        'utc': utc(), 'port': server.server_address[1], 'pid': os.getpid(),
        'cloud_api_version': 'v1beta1', 'sdk_version': sdk_version,
        'output_tokens_per_logical_generation': CAP, 'deadline_seconds': LIMIT,
        'fresh_context_retries': 0, 'credential_values_logged': False})
    print(json.dumps({'ready': str(OUT / 'ready.json')}), flush=True)
    try:
        server.serve_forever()
    finally:
        server.server_close()


if __name__ == '__main__':
    main()
