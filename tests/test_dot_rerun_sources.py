import hashlib
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from math_gauge import dot_rerun_sources as dot
from math_gauge import dot_rerun_evidence_replacement as replacement


class DotRerunSources(unittest.TestCase):
    def setUp(self):
        temp = tempfile.TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        self.root = Path(temp.name)
        self.count = 0
        fixed = dot.CAPTURE_LOSS | dot.DELIVERY_RECOVERY | {dot.REJECTION} | replacement.A1
        a1 = sorted(fixed | {f'FIXTURE{i}:A1' for i in range(39-len(fixed))})
        dataset = {'release_version': '1.0.0', 'dataset_sha256': dot.DATASET,
                   'selected_slot_ids': a1, 'cases': [
                       {'case_id': slot.removesuffix(':A1')} for slot in a1]}
        for target, kwargs in {
                'inspect_release_dataset': {'return_value': dataset},
                '_h_case_request': {'side_effect': lambda root, case: case['case_id']},
                '_h_message': {'side_effect': lambda case: 'Frozen test prompt for ' + case}}.items():
            mock = patch.object(dot, target, **kwargs)
            mock.start()
            self.addCleanup(mock.stop)
        self.prompt = self.put(b'Frozen synthetic continue invitation')
        mock = patch.object(dot, 'C003_PROMPT', self.prompt['sha256'])
        mock.start()
        self.addCleanup(mock.stop)
        self.man = dict(schema=dot.SCHEMA, model_id=dot.MODEL, dataset_sha256=dot.DATASET,
            source_benchmark_version='1.0.0', model_override=None, effort_override=None,
            backend_sku=None, fork_turns='none', isolation='instruction_only', slots={},
            c003_fixed_prompt=self.prompt, original_c003_rounds={}, rejection_retry_authorization=None, additional_capture_authorizations={})
        for key, scope in [('capture_recovery', 'capture_recovery'), ('delivery_recovery',
                'lean_delivery_recovery'), ('c003_file', 'c003_designated_file'), ('recapture', 'damaged_archive_exact_recapture')]:
            self.man[key + '_authorization'] = self.put(dict(scope=scope, post_observation=True,
                source=self.put(b'synthetic authorization')))
        for slot in a1:
            req = self.put(dict(schema='math-gauge.conversation/v1',
                messages=[dict(role='user', content='Frozen test prompt for ' + slot.removesuffix(':A1'))],
                parameters={'model': 'dot-native-default'}))
            status, recovery, basis = 'native_final', None, 'native_inline'
            if slot in dot.CAPTURE_LOSS:
                status, recovery = 'final_archive_lost', 'native_final'
            elif slot in dot.DELIVERY_RECOVERY:
                status, recovery = 'partial_native_final', 'native_final'
            elif slot == dot.REJECTION:
                status, basis = 'platform_rejected', 'nondelivery'
            if slot == 'MG-C003:A1':
                recovery, basis = 'partial_native_final', 'candidate_designated_file'
                self.c003_request = req
            calls = [self.call(slot, req, status)]
            if slot in dot.DAMAGED_ARCHIVES:
                calls.append(self.call(slot,req,'final_capture_damaged'))
            if recovery:
                calls.append(self.call(slot, req, recovery, designation=basis == 'candidate_designated_file'))
            self.row(slot, calls, basis)
        parent = 'MG-C003:A1'
        for slot in dot.C003_ROUNDS:
            self.man['original_c003_rounds'][slot] = self.call(slot, self.c003_request, 'partial_native_final')
            call = self.call(slot, self.c003_request, 'native_final', designation=True)
            preceding = self.man['slots'][parent]['physical_calls'][-1]['archive']
            dispatch = self.put(dict(context_id=call['context_id'], request_sha256=call['request']['sha256'],
                parent_answer_sha256=preceding['sha256'], invitation_sha256=self.prompt['sha256'],
                source=self.put(b'Synthetic dispatch observation')))
            self.row(slot, [call], 'candidate_designated_file', dict(parent=parent,
                parent_answer=preceding, invitation=self.prompt, dispatch=dispatch))
            parent = slot

    def put(self, obj):
        self.count += 1
        path = f'{self.count}.dat'
        raw = obj if isinstance(obj, bytes) else json.dumps(obj, sort_keys=True).encode()
        (self.root / path).write_bytes(raw)
        return dict(path=path, bytes=len(raw), sha256=hashlib.sha256(raw).hexdigest())

    def call(self, slot, request, status, designation=False):
        context = f'synthetic_context_{self.count}'
        terminal = self.put(b'Exact synthetic terminal') if status.endswith('native_final') else None
        archive = self.put(('Artifact ' + context).encode()+(b'\x08' if status == 'final_capture_damaged' else b'')) if status != 'final_archive_lost' else None
        if status == 'observed_native_final':
            declaration = self.put(dict(context_id=context, answer=archive,
              source=self.put(b'Compared fully observed terminal to exact file'),
              comparison='observed_full_final_matches_authored_file'))
        else:
            declaration = self.put(dict(context_id=context, answer=archive,
                source=self.put(('Candidate explicit designation ' + archive['sha256']).encode()))) if designation else None
        observation = self.put(dict(slot=slot, context_id=context, request_sha256=request['sha256'],
            status=status, source=self.put(b'Original observed event'),
            terminal_sha256=terminal and terminal['sha256'], archive_sha256=archive and archive['sha256'],
            designation_sha256=declaration and declaration['sha256']))
        return dict(request=request, context_id=context, status=status, terminal=terminal,
                    archive=archive, observation=observation, designation=declaration)

    def row(self, slot, calls, basis, replay=None):
        call = calls[-1]
        response = call['terminal'] if basis == 'native_inline' else (
            call['archive'] if basis in {'candidate_designated_file','observed_inline_bound_authored_file'} else None)
        review = self.put(dict(source=self.put(b'Mathematical review'), kind='ai', human_review='pending',
            observation_sha256=call['observation']['sha256'], response_sha256=response and response['sha256']))
        self.man['slots'][slot] = dict(physical_calls=calls, selection=basis, review=review, replay=replay)

    def validate(self):
        return dot.validate(self.root, self.root, self.man)

    def test_full_private_source_contract(self):
        out = self.validate()
        self.assertEqual(out['physical_calls'], 56)
        self.assertEqual(out['initial_slots'], 39)
        self.assertEqual(out['designated_file_deliveries'], 4)
        self.assertNotIn('slots', out)

    def test_policy_rejection_preserves_nondelivery(self):
        self.man['slots'][dot.REJECTION]['selection'] = 'native_inline'
        with self.assertRaisesRegex(ValueError, 'policy-rejected'):
            self.validate()

    def test_same_content_in_damaged_archive_does_not_certify_inline(self):
        row = self.man['slots']['MG-GP001:A1']
        previous, damaged, recovery = row['physical_calls']
        row['physical_calls'] = [previous,damaged, self.call('MG-GP001:A1', recovery['request'], 'partial_native_final')]
        with self.assertRaisesRegex(ValueError, 'Capture replacement'):
            self.validate()

    def test_c003_no_mixed_parents(self):
        row = self.man['slots']['MG-C003:R2']
        row['replay']['parent_answer'] = self.man['original_c003_rounds']['MG-C003:R1']['archive']
        with self.assertRaisesRegex(ValueError, 'immediately preceding'):
            self.validate()

    def test_c003_designation_bytes_cannot_be_repaired_after_capture(self):
        ref = self.man['slots']['MG-C003:A1']['physical_calls'][-1]['archive']
        (self.root / ref['path']).write_bytes(b'Post-hoc rewrite')
        with self.assertRaises(ValueError):
            self.validate()

    def test_one_authorized_unchanged_guarded_retry(self):
        self.man['rejection_retry_authorization'] = self.put(dict(
            scope='unchanged_guarded_platform_retry', post_observation=True,
            source=self.put(b'synthetic post-rejection authorization')))
        original = self.man['slots'][dot.REJECTION]['physical_calls'][0]
        replacement = self.call(dot.REJECTION, original['request'], 'native_final')
        self.row(dot.REJECTION, [original, replacement], 'native_inline')
        self.assertEqual(self.validate()['physical_calls'], 57)
        self.man['slots'][dot.REJECTION]['physical_calls'].append(replacement)
        with self.assertRaisesRegex(ValueError, 'Only the authorized replacement'):
            self.validate()

    def test_observed_native_final_bound_to_candidate_file_is_not_transport_receipt(self):
        slot = 'MG-GP001:A1'
        old, damaged, recovery = self.man['slots'][slot]['physical_calls']
        new = self.call(slot,recovery['request'],'observed_native_final')
        self.row(slot,[old,damaged,new],'observed_inline_bound_authored_file')
        out = self.validate()
        self.assertEqual(out['observed_inline_authored_file_deliveries'],1)
        self.assertEqual(out['physical_calls'],56)

    def test_only_authorized_additional_damaged_archive_recovers(self):
        slot = 'FIXTURE0:A1'
        prior = self.man['slots'][slot]['physical_calls'][0]
        self.row(slot,[self.call(slot,prior['request'],'final_capture_damaged'),
                       self.call(slot,prior['request'],'native_final')],'native_inline')
        with self.assertRaisesRegex(ValueError,'Only the authorized replacement'):
            self.validate()


    def replacement_ledger(self):
        original=self.put(self.man)
        prior=dot.validate(self.root,self.root,self.man,include_evaluator_bindings=True)
        source=self.put(dict(exclude_other_models=True,selected_new_c003_rounds=['A1','R1','R2','R3'],
            selected_new_a1=sorted(s[3:-3] for s in replacement.A1),
            messages=[dict(id='synthetic-1',text='exact scope'),dict(id='synthetic-2',text='no retry')]))
        auth=self.put(dict(scope='exact_c003_and_seven_missing_a1_clocks',source=source,model_id=dot.MODEL,
            original_ledger_sha256=original['sha256'],classification='user_adjudicated_system_evidence_failure',
            not_retry=True,best_of=False,preserve_original=True))
        slots={}
        for slot in sorted(replacement.A1)+list(replacement.C003):
            is_lean=slot in replacement.C003
            req=self.man['slots'][slot]['physical_calls'][-1]['request']
            call=self.call(slot,req,'native_final' if is_lean else 'observed_native_final',designation=is_lean)
            response=call['archive']
            review=self.put(dict(source=self.put(b'Synthetic mathematical review'),kind='ai',
                human_review='pending',observation_sha256=call['observation']['sha256'],response_sha256=response['sha256']))
            replay=None
            if slot in dot.C003_ROUNDS:
                parent=replacement.C003[replacement.C003.index(slot)-1]
                parent_answer=slots[parent]['call']['archive']
                dispatch=self.put(dict(context_id=call['context_id'],request_sha256=req['sha256'],
                   parent_answer_sha256=parent_answer['sha256'],invitation_sha256=self.prompt['sha256'],
                   source=self.put(b'Synthetic actual dispatch')))
                replay=dict(parent=parent,parent_answer=parent_answer,invitation=self.prompt,dispatch=dispatch)
            slots[slot]=dict(call=call,selection='candidate_designated_file' if is_lean else 'observed_inline_bound_authored_file',
                             review=review,replay=replay,prior_answer_sha256=prior['selected'][slot]['response']['sha256'],
                             readable_capture=None)
        return dict(schema=replacement.SCHEMA,model_id=dot.MODEL,source_benchmark_version='1.0.0',
                    base=original,authorization=auth,replacement_slots=slots),prior

    def test_replacement_exact_scope_and_unchanged_historical_basis(self):
        ledger,prior=self.replacement_ledger()
        out=dot.validate(self.root,self.root,ledger,include_evaluator_bindings=True)
        self.assertEqual(out['archived_first'],prior['first'])
        self.assertEqual({k:out['first'][k] for k in replacement.SLOTS},
                         {k:out['selected'][k] for k in replacement.SLOTS})
        self.assertEqual(out['physical_calls'],prior['physical_calls']+11)
        for slot in prior['selected']:
            if slot not in replacement.SLOTS:
                self.assertEqual(out['selected'][slot],prior['selected'][slot])
            else:
                self.assertEqual(out['effective_slots'][slot]['physical_calls'][:-1],
                                 self.man['slots'][slot]['physical_calls'])
        del ledger['replacement_slots']['MG-C003:R3']
        with self.assertRaisesRegex(ValueError,'entire C003 trajectory'):
            dot.validate(self.root,self.root,ledger)

    def test_replacement_c003_block_cross_trajectory(self):
        ledger,prior=self.replacement_ledger()
        replay=ledger['replacement_slots']['MG-C003:R2']['replay']
        replay['parent_answer']=prior['selected']['MG-C003:R1']['response']
        with self.assertRaisesRegex(ValueError,'borrowed earlier trajectory'):
            dot.validate(self.root,self.root,ledger)

    def test_lossy_capture_readable_projection_keeps_exact_raw_clock_bytes(self):
        replacement.check_readable_capture(b"alpha\x08eta and m",b"alpha\\beta and \\m")
        with self.assertRaisesRegex(ValueError,'reproduce the exact'):
            replacement.check_readable_capture(b"alpha\x08eta and n",b"alpha\\beta and m")
