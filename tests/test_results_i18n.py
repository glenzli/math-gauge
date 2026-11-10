"""Display filters and translations preserve mathematical evidence and unknowns."""
import copy
from pathlib import Path
import subprocess
import unittest

from scripts.render_results_site import build_data, is_fully_evaluated, render_content_rates
from scripts.results_i18n import javascript_catalog

ROOT = Path(__file__).resolve().parents[1]


class ResultsPresentationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.models = build_data()['models']

    def test_completed_filter_keeps_adjudicated_failures_and_rejects_missing_evidence(self):
        m = copy.deepcopy(next(m for m in self.models if m['id'] == 'terra-6.1-max'))
        self.assertNotEqual(m['trajectory']['state'], 'verified_complete')
        self.assertTrue(is_fully_evaluated(m))
        m['retry']['combined']['metrics']['overall']['exact'] = None
        self.assertFalse(is_fully_evaluated(m), 'Unresolved rounds must not disappear behind A1 coverage')
        m['retry']['combined']['metrics']['overall']['exact'] = 0
        self.assertTrue(is_fully_evaluated(m), 'A known zero is still a completed evaluation')
        m['evaluation_progress']['nonlogical_retry_3']['incomplete'] = True
        self.assertFalse(is_fully_evaluated(m))

    def test_absent_rate_review_stays_unknown_without_removing_other_models(self):
        models = copy.deepcopy(self.models[:2])
        models[0]['content_rates'] = None
        page = render_content_rates({'models': models})
        self.assertIn('data-model="'+models[0]['id']+'"', page)
        self.assertIn('data-model="'+models[1]['id']+'"', page)
        self.assertIn('data-rate-value=""', page)
        self.assertIsNone(models[0]['content_rates'])

    def test_translation_roundtrip_preserves_original_evidence(self):
        # Exercise the actual shipped translator on the same nodes across switches.
        script = (ROOT/'scripts/templates/results-i18n.js').read_text().replace('@@MG_MESSAGES@@', javascript_catalog())
        harness = r'''
const assert=require('node:assert/strict');
global.window={};global.NodeFilter={SHOW_TEXT:4};
global.MutationObserver=class{observe(){}takeRecords(){return []}};
const container=blocked=>({closest:selector=>selector==='[data-ui-prose]'?null:(blocked?{}:null)});
const texts=[{nodeValue:'模型排行榜',parentElement:container(false)},
 {nodeValue:'题目与要求：可靠数学能力',parentElement:container(true)}];
global.document={title:'方法与数据 · Math Gauge',documentElement:{lang:'zh-CN'},body:{},
 createTreeWalker(){let i=-1;return {nextNode(){return ++i<texts.length},get currentNode(){return texts[i]}}},
 querySelectorAll(){return []}};
'''
        assertions = r'''
for(let i=0;i<2;i++){
 window.MGI18n.apply('en');assert.equal(texts[0].nodeValue,'Model leaderboard');
 assert.equal(texts[1].nodeValue,'题目与要求：可靠数学能力');assert.equal(document.documentElement.lang,'en');
 window.MGI18n.apply('zh');assert.equal(texts[0].nodeValue,'模型排行榜');
 assert.equal(texts[1].nodeValue,'题目与要求：可靠数学能力');assert.equal(document.documentElement.lang,'zh-CN');
}
'''
        result = subprocess.run(['node','-e',harness+script+assertions],text=True,capture_output=True)
        self.assertEqual(result.returncode,0,result.stderr)


if __name__ == '__main__':
    unittest.main()
