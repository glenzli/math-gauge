"""Historical display data uses retained judgments, shared content and fixed UI."""
import copy
import hashlib
import json
from pathlib import Path
import re
import unittest

from scripts.results_editions import encoded, lazy_prose, prior_payload


class EditionDataTests(unittest.TestCase):
    def test_case_snapshot_uses_original_view_including_unknowns_without_mutating_current(self):
        current={'benchmark_version':'1.1.0','model':{'id':'fixture'},'case':{'id':'TX',
            'views':{'partial':{'single_attempt':{'completion':{'exact':2/3},'strict_pass':False,
                'response_sha256':'answer','review_sha256':'new-review'}}}}}
        old={'completion':{'exact':None,'lower':0,'upper':1},'strict_pass':None,
             'response_sha256':None,'review_sha256':None,'case_id':'TX'}
        projection={'fixture':{'views':{'partial':{'single_attempt':{'tasks':[old]}}}}}
        before=copy.deepcopy(current)
        result=prior_payload('models/fixture/cases/TX.html',current,{'benchmark_version':'1.0.0'},projection)
        self.assertEqual(current,before)
        self.assertEqual(result['benchmark_version'],'1.0.0')
        self.assertEqual(result['case']['views']['partial']['single_attempt'],
            {k:v for k,v in old.items() if k!='case_id'})
        old['completion']['exact']=0
        result=prior_payload('models/fixture/cases/TX.html',current,{'benchmark_version':'1.0.0'},projection)
        self.assertEqual(result['case']['views']['partial']['single_attempt']['completion']['exact'],0)

    def test_shared_math_prose_is_content_addressed_and_never_a_complete_ui_page(self):
        text='<p>Original <math><mi>x</mi></math> '+('数学原文 '*150)+'</p>'
        page='<main><div class="prose" data-original>'+text+'</div><button>Control</button></main>'
        files={}
        first=lazy_prose('models/one/cases/TX.html',page,files)
        second=lazy_prose('models/two/cases/TX.html',page,files)
        self.assertEqual(first,second)
        self.assertNotIn(text,first)
        self.assertIn('<button>Control</button>',first)
        self.assertEqual(len(files),2)
        script=next(value for path,value in files.items() if path.endswith('.js'))
        key=hashlib.sha256(text.encode()).hexdigest()
        self.assertIn('window.MGProseData("'+key+'",',script)
        self.assertNotIn('<main>',script)
        self.assertNotIn('Control',script)
        self.assertIn('data-original',first)

    def test_lazy_content_links_are_based_at_the_shared_asset(self):
        text='<p>'+('Original '*200)+'<a href="../../method.html#section">Method</a></p>'
        files={};lazy_prose('models/one/index.html','<div class="prose">'+text+'</div>',files)
        fragment=next(value for key,value in files.items() if key.endswith('.html'))
        self.assertIn('href="../../method.html#section"',fragment)

    def test_registration_data_cannot_become_literal_script_markup(self):
        value={'original':'</script><script>unsafe()</script>\u2028&'}
        literal=encoded(value)
        self.assertNotIn('<',literal)
        self.assertNotIn('\u2028',literal)
        self.assertEqual(json.loads(literal),value)


if __name__=='__main__':
    unittest.main()
