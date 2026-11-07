"""Public detail judgments are a constrained projection, not a second scorer."""
import copy
import hashlib
import json
from pathlib import Path
import tempfile
import unittest
from math_gauge.records import load_public_task_scores, project_public_task_view, public_assessment_case_ids

ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT/'results/v0.6.0/gemini-3.8-flash-high/20261105'


class PublicTaskProjectionTests(unittest.TestCase):
    def fixture(self, folder):
        record = json.loads((BASE/'record.json').read_bytes())
        names = {'public-task-scores.json',record['assessment_policy']['path']}
        for key in ('assessment_results','strict_results','capability_results'):
            names.update(item['path'] for item in record[key].values())
        for name in names:
            (folder/name).write_bytes((BASE/name).read_bytes())
        return record

    def rebind(self, folder, record, data):
        raw = (json.dumps(data)+'\n').encode()
        (folder/'public-task-scores.json').write_bytes(raw)
        item = next(s for s in record['evidence'] if s['path']=='public-task-scores.json')
        item.update(bytes=len(raw),sha256=hashlib.sha256(raw).hexdigest())

    def test_projection_copies_exact_public_judgments_and_omits_private_fields(self):
        public = {'case_id':'public','completion':{'lower':.79,'upper':.79,'exact':.79},
                  'strict_pass':False,'response_sha256':'a'*64,'review_sha256':'b'*64,
                  'claim_assessment':{'private':'not exported'},'slot_id':'public:A1'}
        source = {'tasks':[dict(public,case_id='private'),public]}
        original=copy.deepcopy(source)
        projection=project_public_task_view(source,['public'],'c'*64)
        self.assertEqual(len(projection['tasks']),1)
        row=projection['tasks'][0]
        self.assertEqual(row,{k:public[k] for k in ('case_id','completion','strict_pass','response_sha256','review_sha256')})
        row['completion']['exact']=0
        self.assertEqual(source,original)
        with self.assertRaises(ValueError):project_public_task_view(source,['missing'],'c'*64)

    def test_selected_membership_keeps_mc_rmc_strict_distinct(self):
        record=json.loads((BASE/'record.json').read_bytes());data=load_public_task_scores(BASE,record)
        policy=json.loads((BASE/'assessment-policy.json').read_bytes())
        self.assertEqual(data['public_case_ids'],public_assessment_case_ids(policy))
        self.assertNotIn('MG-GR103',data['public_case_ids']);self.assertIn('MG-PS001',data['public_case_ids'])
        for condition in ('single_attempt','nonlogical_retry_3'):
            get=lambda mode:next(r for r in data['views'][mode][condition]['tasks'] if r['case_id']=='MG-PS001')
            self.assertEqual(get('capability')['completion']['exact'],.94)
            self.assertEqual(get('partial')['completion']['exact'],.79)
            self.assertIs(get('strict')['strict_pass'],False)
            # Strict completion is not binary credit; displays must use strict_pass.
            self.assertEqual(get('strict')['completion']['exact'],.94)

    def test_rehashed_private_extended_or_misbound_projection_is_rejected(self):
        for change in ('private','extra','binding','int_verdict'):
            with self.subTest(change=change),tempfile.TemporaryDirectory() as name:
                folder=Path(name);record=self.fixture(folder);data=load_public_task_scores(folder,record)
                view=data['views']['partial']['single_attempt'];row=view['tasks'][0]
                if change=='private':row['case_id']='MG-X-secret'
                if change=='extra':row['raw_answer']='not allowed'
                if change=='binding':view['source_report_sha256']='0'*64
                if change=='int_verdict':row['strict_pass']=1
                self.rebind(folder,record,data)
                with self.assertRaises(ValueError):load_public_task_scores(folder,record)

    def test_old_archive_without_optional_projection_remains_readable(self):
        record=json.loads((BASE/'record.json').read_bytes())
        record['evidence']=[s for s in record['evidence'] if s['path']!='public-task-scores.json']
        self.assertIsNone(load_public_task_scores(BASE,record))


if __name__=='__main__':unittest.main()
