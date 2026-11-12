"""Evidence pages preserve selection, provenance, safe rendering and privacy."""
import copy
from html.parser import HTMLParser
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
from urllib.parse import unquote,urlsplit
from scripts.render_results_site import build_data,write_site
from scripts.results_details import EvidenceRenderer,build_detail_pages,public_evidence,source_link
from math_gauge.records import load_public_task_scores
from math_gauge.evidence_retention import read_bytes as retained_bytes

ROOT=Path(__file__).resolve().parents[1]


class Links(HTMLParser):
    def __init__(self,text):
        super().__init__();self.links=[];self.resources=[];self.feed(text)
    def handle_starttag(self,tag,attrs):
        a=dict(attrs)
        if tag=='a' and a.get('href'):self.links.append(a['href'])
        if tag in ('script','img','link') and (a.get('src') or a.get('href')):
            self.resources.append(a.get('src') or a['href'])


class SourceLinkTests(unittest.TestCase):
    def test_cold_or_alias_link_uses_original_git_location(self):
        with tempfile.TemporaryDirectory() as name:
            root=Path(name).resolve()
            location={'repository_root':str(root),'revision':'a'*40,
                      'git_path':'results/evidence-retention/原答 body.md',
                      'sha256':'b'*64,'bytes':17}
            with patch('scripts.results_details.source_location',return_value=location) as locate:
                value=source_link('results/logical/answer.md','models/model/index.html','原答 <&>',root=root)
            self.assertEqual(locate.call_args.args[0],root/'results/logical/answer.md')
            self.assertIn('/blob/'+('a'*40)+'/results/evidence-retention/%E5%8E%9F%E7%AD%94%20body.md',value)
            self.assertNotIn('/results/logical/',value)
            self.assertIn('原答 &lt;&amp;&gt;',value)

    def test_hot_link_remains_local_and_private_repository_is_rejected(self):
        with tempfile.TemporaryDirectory() as name:
            root=Path(name).resolve();(root/'.git').mkdir()
            source=root/'results/answer body.md';source.parent.mkdir();source.write_text('original\n')
            value=source_link('results/answer body.md','models/model/index.html','原答',root=root)
            self.assertIn('href="../../../results/answer%20body.md"',value)
            with self.assertRaisesRegex(ValueError,'escapes'):
                source_link('../math-gauge-private/answer.md','index.html','private',root=root)
            other={'repository_root':str(root/'other'),'revision':'a'*40,
                   'git_path':'private/answer.md','sha256':'b'*64,'bytes':1}
            with patch('scripts.results_details.source_location',return_value=other):
                with self.assertRaisesRegex(ValueError,'another repository'):
                    source_link('results/answer body.md','index.html','private',root=root)


class ResultDetailsTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.data=build_data();cls.pages=build_detail_pages(copy.deepcopy(cls.data),ROOT)

    def test_links_resolve_without_private_inventory_or_remote_runtime(self):
        generated=set(self.pages)|{'index.html','data.json'}
        for path,page in self.pages.items():
            with self.subTest(path=path):
                for marker in ('math-gauge-private/','MG-TXP','MG-BCP','MG-X'):
                    self.assertNotIn(marker,page)
                parsed=Links(page)
                for value in parsed.resources:self.assertFalse(urlsplit(value).scheme or value.startswith('//'),value)
                for value in parsed.links:
                    u=urlsplit(value)
                    if u.scheme or not u.path:continue
                    target=(ROOT/'site'/Path(path).parent/unquote(u.path)).resolve()
                    if target.is_relative_to(ROOT/'site'):
                        relative=str(target.relative_to(ROOT/'site'))
                        if relative.startswith('assets/'):continue
                        self.assertIn(relative,generated)
                    else:self.assertTrue(target.is_file(),str(target))

    def test_retry_uses_admitted_answer_and_original_failure_is_not_filled(self):
        folder=ROOT/'results/v0.6.0/deepseek-v4.1-flash-1017/20261109/sources/legacy-public-20261105'
        record=json.loads(retained_bytes(folder/'record.json'));scores=load_public_task_scores(folder,record);samples={}
        for c in ('single_attempt','nonlogical_retry_3'):
            task=next(r for r in scores['views']['partial'][c]['tasks'] if r['case_id']=='MG-GR021')
            samples[c]=public_evidence(folder,record,'MG-GR021',c,task)
        self.assertIsNone(samples['single_attempt']['source_row']['response'])
        self.assertEqual(samples['nonlogical_retry_3']['selected_record'],'MG-GR021:A1:attempt:3')
        self.assertTrue(any(s['path'].endswith('/attempts/3/answer.md') for s in samples['nonlogical_retry_3']['sources']))

    def test_markdown_math_are_readable_without_script_or_image_requests(self):
        renderer=EvidenceRenderer()
        token=renderer.add('Test $x^2$ and \\(a+b\\). $\\begin{psmallmatrix}1&2\\\\2&1\\end{psmallmatrix}$\n\n<script>alert(1)</script>\n\n![remote](https://example.com/pixel)\n\n[bad](javascript:alert(1))\n\n[Local theorem](/private/tmp/native-run/work/Main.lean:12)\n\n[External reference](https://example.com/theorem)')
        page=renderer.finish({'test':token})['test']
        self.assertIn('<math ',page);self.assertIn('<msup>',page)
        self.assertNotIn('<script>',page);self.assertNotIn('<img ',page);self.assertNotIn('href="javascript:',page)
        self.assertNotIn('katex-error',page)
        self.assertIn('Local theorem', page)
        self.assertNotIn('href="/private/tmp/', page)
        self.assertIn('href="https://example.com/theorem"', page)

    def test_replacement_uses_its_first_delivery_without_retired_credit(self):
        page=self.pages['models/deepseek-v4.1-flash-1017/cases/MG-PS001.html']
        payload=page.split('<script type="application/json" id="data">',1)[1].split('</script>',1)[0];data=json.loads(payload)
        for views in data['case']['views'].values():
            first, selected = views['single_attempt'], views['nonlogical_retry_3']
            self.assertEqual(first['completion']['exact'], 0)
            self.assertFalse(first['strict_pass'])
            self.assertIsNone(first['response_sha256'])
            self.assertEqual(selected['completion']['exact'], 1)
            self.assertTrue(selected['strict_pass'])
            self.assertIsNotNone(selected['response_sha256'])

    def test_stale_generated_pages_removed_and_unowned_files_preserved(self):
        with tempfile.TemporaryDirectory() as name:
            dest=Path(name);(dest/'generated-pages.json').write_text('["models/retired.html"]')
            (dest/'models').mkdir();(dest/'models/retired.html').write_text('retired generated output')
            (dest/'models/notes.txt').write_text('operator notes');write_site(dest)
            self.assertFalse((dest/'models/retired.html').exists())
            self.assertEqual((dest/'models/notes.txt').read_text(),'operator notes')


if __name__=='__main__':unittest.main()
