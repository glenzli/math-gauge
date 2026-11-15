"""Admit one native agent context, including its own context compaction.

This transport check neither rewrites messages nor exposes state to tools.
It is distinct from the SDK's continuation of one logical generation.
"""
from pathlib import Path
import hashlib
import json
import re


def _text_parts(contents):
    for content in contents:
        for part in content.get('parts', []):
            if isinstance(part.get('text'), str):
                yield part['text']


def _digest(value):
    return hashlib.sha256(value.encode()).hexdigest()


class NativeContextGuard:
    """One task file, native workspace and conversation per physical attempt."""

    def __init__(self, task_path):
        self.task_path = Path(task_path)
        self.work = (self.task_path.parent.parent / 'work').resolve()
        self.prompt_sha256 = None
        self.scope = None
        self.summary_sha256 = None

    def _scope(self, payload):
        system = payload.get('systemInstruction', payload.get('system_instruction', {}))
        text = '\n'.join(_text_parts([system]))
        block = re.search(r'<user_information>\s*(.*?)\s*</user_information>', text, re.S)
        if not block:
            raise ValueError('Missing native user-information scope')
        info = block.group(1)
        conversation = re.search(r'^Conversation ID:\s*(\S+)\s*$', info, re.M)
        cwd = re.search(r'^Command Working Directory:\s*(.+?)\s*$', info, re.M)
        if not conversation or not cwd or Path(cwd.group(1)).resolve() != self.work:
            raise ValueError('Native conversation/workspace scope mismatch')
        return conversation.group(1), str(self.work)

    @staticmethod
    def _summary(payload):
        contents = payload.get('contents', [])
        if not contents or contents[0].get('role') != 'user':
            return None
        parts = list(_text_parts(contents[:1]))
        if not parts or not parts[0].startswith('<CONTEXT_SUMMARY>'):
            return None
        end = parts[0].find('</CONTEXT_SUMMARY>')
        if end < 0:
            raise ValueError('Incomplete native context-summary wrapper')
        return parts[0][:end + len('</CONTEXT_SUMMARY>')]

    def validate(self, payload, *, expected_tools=()):
        """Validate without mutating the original native payload.

        A new native summary may omit previously executed tool responses.
        Repeating that same summary does not waive the next response check.
        """
        original_sha = _digest(json.dumps(payload, sort_keys=True, ensure_ascii=False))
        prompt_bytes = self.task_path.read_bytes()
        prompt = prompt_bytes.decode('utf-8')
        if not prompt.strip():
            raise ValueError('Nonempty frozen native task required')
        prompt_sha = hashlib.sha256(prompt_bytes).hexdigest()
        if self.prompt_sha256 is not None and prompt_sha != self.prompt_sha256:
            raise ValueError('Frozen native task file changed')
        scope = self._scope(payload)
        if self.scope is not None and scope != self.scope:
            raise ValueError('Native conversation/workspace changed within one attempt')
        summary = self._summary(payload)
        literal = any(prompt in text for text in _text_parts(payload.get('contents', [])))
        if self.scope is None:
            if summary is not None or not literal:
                raise ValueError('A fresh native context must first receive the exact frozen task')
        elif not literal and summary is None:
            raise ValueError('Missing frozen task or same-context native summary')
        summary_sha = _digest(summary) if summary is not None else None
        compacted = summary_sha is not None and summary_sha != self.summary_sha256
        responses = {part['functionResponse'].get('name')
                     for content in payload.get('contents', [])
                     for part in content.get('parts', []) if 'functionResponse' in part}
        if expected_tools and not compacted and not set(expected_tools).intersection(responses):
            raise ValueError('Missing original tool responses')
        self.prompt_sha256, self.scope = prompt_sha, scope
        if summary_sha is not None:
            self.summary_sha256 = summary_sha
        return {
            'schema': 'math-gauge.native-context-admission/v1',
            'mode': 'native-compaction' if compacted else 'native-summary-followup' if summary else 'original-task',
            'task_sha256': prompt_sha,
            'conversation_id': scope[0],
            'workspace': scope[1],
            'native_summary_sha256': summary_sha,
            'original_task_literal_present': literal,
            'tool_response_check_waived_for_new_native_summary': bool(compacted and expected_tools),
            'native_payload_canonical_sha256': original_sha,
            'native_payload_rewritten': False,
        }
