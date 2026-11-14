"""Offline transport checks; no model requests or real credentials are used."""
import copy
import importlib.metadata
import importlib.util
import json
from pathlib import Path
import queue
import tempfile
import time
from types import SimpleNamespace
import unittest
from unittest.mock import patch

try:
    import httpx
except ImportError:
    httpx = None

try:
    HAS_SDK = importlib.metadata.version('google-genai') == '2.34.0'
except importlib.metadata.PackageNotFoundError:
    HAS_SDK = False

SOURCE = Path(__file__).resolve().parents[1] / 'scripts/gcp_continuation_gateway.py'


@unittest.skipUnless(httpx is not None, 'Optional GCP transport dependency unavailable')
class ContinuationTransportTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        spec = importlib.util.spec_from_file_location('isolated_continuation_gateway', SOURCE)
        self.g = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(self.g)
        session = self.root / 'attempt/session'
        (session / 'input').mkdir(parents=True)
        (session / 'input/task.md').write_text('Original offline task')
        key, adc = self.root / 'key', self.root / 'synthetic-adc.json'
        key.write_text('offline-loopback-key')
        adc.write_text('{}')
        self.g.configure(SimpleNamespace(out=self.root / 'operator', session=session,
            key_file=key, credential_file=adc, project='offline-project', location='global',
            candidate_model='fixture-model', guard_model=['fixture-guard'],
            thinking_level='medium', deadline_seconds=120, max_output_tokens=262144))
        self.g.STARTED = time.monotonic()
        self.original = {
            'contents': [{'role': 'user', 'parts': [{'text': 'Original offline task'}]},
                         {'role': 'model', 'parts': [{'text': 'same context',
                                                     'thoughtSignature': '-_8='}]}],
            'systemInstruction': {'parts': [{'text': 'Original system instruction'}]},
            'tools': [{'functionDeclarations': [{'name': 'finish', 'parameters': {
                'type': 'OBJECT', 'properties': {'min_length': {'type': 'STRING',
                                                             'minLength': '1'}}}}]}],
            'generationConfig': {'maxOutputTokens': 65536,
                                 'thinkingConfig': {'thinkingLevel': 'MEDIUM'}},
        }

    def request(self, body):
        return httpx.Request('POST',
            'https://example.invalid/v1beta1/projects/offline/locations/global/'
            'publishers/google/models/fixture-model:streamGenerateContent', json=body)

    def test_exact_native_context_tools_and_signature_wire_are_preserved(self):
        received = []
        inner = httpx.MockTransport(lambda req: (received.append(json.loads(req.content))
                                                or httpx.Response(200, content=b'')))
        transport = self.g.CaptureTransport(inner, self.original, 1, 'fixture-model', 'candidate')
        sdk = copy.deepcopy(self.original)
        sdk['contents'][1]['parts'][0]['thoughtSignature'] = '+/8'
        sdk['tools'][0]['functionDeclarations'][0]['parameters']['properties']['min_length']['min_length'] = 1
        del sdk['tools'][0]['functionDeclarations'][0]['parameters']['properties']['min_length']['minLength']
        sdk['generationConfig']['maxOutputTokens'] = 262144
        sdk['continuationToken'] = 'opaque-checkpoint'
        response = transport.handle_request(self.request(sdk))
        response.close()
        expected = copy.deepcopy(self.original)
        expected['generationConfig']['maxOutputTokens'] = 262144
        expected['continuationToken'] = 'opaque-checkpoint'
        self.assertEqual(received, [expected])
        bad = copy.deepcopy(sdk)
        bad['contents'][0]['parts'][0]['text'] = 'changed task'
        with self.assertRaisesRegex(AssertionError, 'contents'):
            transport.handle_request(self.request(bad))
        self.assertEqual(len(received), 1)

    def test_property_names_are_not_reinterpreted_as_schema_aliases(self):
        inner = httpx.MockTransport(lambda _: self.fail('Invalid tool schema reached transport'))
        transport = self.g.CaptureTransport(inner, self.original, 1, 'fixture-model', 'candidate')
        bad = copy.deepcopy(self.original)
        props = bad['tools'][0]['functionDeclarations'][0]['parameters']['properties']
        props['minLength'] = props.pop('min_length')
        with self.assertRaisesRegex(AssertionError, 'tool declaration'):
            transport.handle_request(self.request(bad))

    def test_expired_deadline_and_ninth_hop_never_dispatch(self):
        inner = httpx.MockTransport(lambda _: self.fail('Budget failure reached transport'))
        transport = self.g.CaptureTransport(inner, self.original, 1, 'fixture-model', 'candidate')
        self.g.STARTED -= 121
        with self.assertRaises(TimeoutError):
            transport.handle_request(self.request(self.original))
        self.g.STARTED = time.monotonic()
        transport.hops = 8
        with self.assertRaisesRegex(RuntimeError, 'Eight-hop'):
            transport.handle_request(self.request(self.original))
        self.assertEqual(self.g.POSTS, 0)

    @unittest.skipUnless(HAS_SDK, 'Run with the pinned optional google-genai2.34.0 environment')
    def test_official_sdk_continues_context_then_allows_native_finalization(self):
        from google.oauth2.credentials import Credentials
        received = []

        def response(request):
            body = json.loads(request.content)
            received.append(body)
            number = len(received)
            if number == 1:
                part, reason, token = {'text': 'private state', 'thought': True}, 'CONTINUATION', 'b3BhcXVl'
            elif number == 2:
                part, reason, token = {'functionCall': {'name': 'finish', 'args': {}}}, 'STOP', None
            else:
                part, reason, token = {'text': 'Actual normal final'}, 'STOP', None
            candidate = {'index': 0, 'content': {'role': 'model', 'parts': [part]},
                         'finishReason': reason}
            if token:
                candidate['continuationToken'] = token
            data = {'candidates': [candidate], 'usageMetadata': {
                'promptTokenCount': 10, 'candidatesTokenCount': 2,
                'thoughtsTokenCount': 65536 if token else 0,
                'totalTokenCount': 65548 if token else 12}}
            return httpx.Response(200, headers={'content-type': 'text/event-stream'},
                                  content=b'data: ' + json.dumps(data).encode() + b'\n\n')

        with patch('google.oauth2.credentials.Credentials.from_authorized_user_file',
                   return_value=Credentials(token='offline-no-cloud-authority')), \
             patch.object(self.g.httpx, 'HTTPTransport', side_effect=lambda **_: httpx.MockTransport(response)):
            output = queue.Queue()
            self.g.generate(self.original, 1, output, 'fixture-model', 'candidate')
            self.assertFalse(self.g.TERMINAL, 'finish() must not block the actual native final')
            self.assertEqual(self.g.EXPECTED_TOOLS, {'finish'})
            deadline_origin = self.g.STARTED
            next_original = copy.deepcopy(self.original)
            next_original['contents'].append({'role': 'user', 'parts': [
                {'functionResponse': {'name': 'finish', 'response': {}}}]})
            self.g.generate(next_original, 2, output, 'fixture-model', 'candidate')
            self.assertEqual(self.g.STARTED, deadline_origin)
        self.assertEqual(len(received), 3)
        self.assertEqual(received[1]['contents'], self.original['contents'])
        self.assertEqual(received[1]['continuationToken'], 'b3BhcXVl')
        self.assertTrue(all(r['generationConfig']['maxOutputTokens'] == 262144 for r in received))
        projected = list(output.queue)
        self.assertFalse(any('continuationToken' in c or c.get('finishReason') == 'CONTINUATION'
                             for d in projected for c in d.get('candidates', [])))
        self.assertEqual(projected[-1]['candidates'][0]['content']['parts'][0]['text'], 'Actual normal final')

    @unittest.skipUnless(HAS_SDK, 'Run with the pinned optional google-genai2.34.0 environment')
    def test_actual429_remains_typed_and_has_no_transport_retry(self):
        from google.oauth2.credentials import Credentials
        from google.genai.errors import ClientError
        received = []

        def response(request):
            received.append(request)
            return httpx.Response(429, json={'error': {'code': 429,
                'status': 'RESOURCE_EXHAUSTED', 'message': 'offline quota fixture'}})

        with patch('google.oauth2.credentials.Credentials.from_authorized_user_file',
                   return_value=Credentials(token='offline-no-cloud-authority')), \
             patch.object(self.g.httpx, 'HTTPTransport', side_effect=lambda **_: httpx.MockTransport(response)):
            with self.assertRaises(ClientError) as caught:
                self.g.generate(self.original, 1, queue.Queue(), 'fixture-model', 'candidate')
        self.assertEqual(caught.exception.code, 429)
        self.assertEqual(len(received), 1)
        status = json.loads((self.g.OUT / '001-native.status.json').read_text())
        self.assertEqual(status['status'], 429)


if __name__ == '__main__':
    unittest.main()
