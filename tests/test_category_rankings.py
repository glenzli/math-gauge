"""Synthetic display-contract tests; no model calls or score recomputation."""
import copy
import hashlib
import json
import unittest

from scripts import results_rankings as rankings

MODES = rankings.SCORE_MODES
GROUPS = [dict(id='written',title='书面证明',weight=35),
          dict(id='lean',title='Lean',weight=35),
          dict(id='research',title='数学研究',weight=30)]


def metric(value, *, exact=True, adjudicated=1, lower=None, upper=None):
    return dict(exact=value if exact else None, confirmed=value,
        lower=value if lower is None else lower, upper=value if upper is None else upper,
        complete=exact, coverage=dict(planned=3,adjudicated=adjudicated,unknown=0 if exact else 3-adjudicated))


def model(mid, values):
    reports = {mode: {'metrics': {g['id']:copy.deepcopy(values[mode][g['id']]) for g in GROUPS}}
               for mode in MODES}
    # A1 deliberately differs; the helper must ask for the rule-selected report.
    return dict(id=mid,label=mid,combined={'metrics':{g['id']:metric(999)for g in GROUPS}},
        retry={'combined':reports['partial']},capability={'nonlogical_retry_3':reports['capability']},
        strict={'nonlogical_retry_3':reports['strict']})


def uniform(mid, source):
    return model(mid,{mode:{g['id']:source for g in GROUPS}for mode in MODES})


def selected(m, mode):
    return m['retry']['combined'] if mode=='partial' else m[mode]['nonlogical_retry_3']


def digest(data):
    return hashlib.sha256(json.dumps(data,sort_keys=True).encode()).hexdigest()


class CategoryRankingsTests(unittest.TestCase):
    def project(self, models, groups=GROUPS):
        return rankings.category_rankings(models,groups,result_selector=selected)

    def test_saved_rule_selected_metrics_metadata_and_inputs_remain_unchanged(self):
        models=[uniform('saved',metric(62.17261904761905,exact=False,adjudicated=1,lower=50.1,upper=80.2))]
        groups=copy.deepcopy(GROUPS);groups[0].update(title='冻结大类标题',weight=17)
        before=digest([models,groups]);calls=[]
        def selector(m,mode):calls.append((m['id'],mode));return selected(m,mode)
        boards=rankings.category_rankings(models,groups,result_selector=selector)
        self.assertEqual(digest([models,groups]),before)
        self.assertEqual(calls,[('saved',mode)for mode in MODES])
        self.assertEqual((boards[0]['title'],boards[0]['weight']),('冻结大类标题',17))
        for view in boards[0]['views'].values():
            self.assertEqual(view[0]['value'],62.17261904761905)
            self.assertEqual((view[0]['lower'],view[0]['upper']),(50.1,80.2))
            self.assertEqual(view[0]['status'],'partial')
        boards[0]['views']['partial'][0]['value']=7
        self.assertEqual(digest([models,groups]),before)

    def test_unknown_zero_known_zero_nonzero_partial_and_signed_scores_are_distinct(self):
        models=[uniform('unknown',metric(0,exact=False,adjudicated=0,lower=-20,upper=100)),
                uniform('measured-zero',metric(0)),uniform('known-zero-partial',metric(0,exact=False,adjudicated=1,lower=-5,upper=40)),
                uniform('argon-lean',metric(13.214285714285714,exact=False,adjudicated=0,lower=1.7857142857,upper=70.3571428572)),
                uniform('negative',metric(-2.5))]
        rows=self.project(models)[1]['views']['partial'];by_id={r['model_id']:r for r in rows}
        self.assertEqual([r['model_id']for r in rows],['argon-lean','known-zero-partial','measured-zero','negative','unknown'])
        self.assertEqual(by_id['argon-lean']['value'],13.214285714285714)
        self.assertTrue(by_id['argon-lean']['incomplete'])
        self.assertEqual(by_id['measured-zero']['value'],0)
        self.assertFalse(by_id['measured-zero']['incomplete'])
        self.assertEqual(by_id['known-zero-partial']['value'],0)
        self.assertEqual(by_id['negative']['value'],-2.5)
        self.assertEqual(by_id['negative']['rank'],4)
        self.assertIsNone(by_id['unknown']['value']);self.assertIsNone(by_id['unknown']['rank'])
        self.assertEqual(by_id['unknown']['status'],'unknown')
        self.assertEqual((by_id['unknown']['lower'],by_id['unknown']['upper']),(-20,100))

    def test_each_category_and_mode_has_its_own_order(self):
        values={'a':{'capability':[90,20,10],'partial':[10,80,20],'strict':[20,10,70]},
                'b':{'capability':[80,30,20],'partial':[70,20,10],'strict':[90,20,10]},
                'c':{'capability':[70,40,30],'partial':[20,10,80],'strict':[10,90,20]}}
        models=[model(mid,{mode:{g['id']:metric(v)for g,v in zip(GROUPS,m[mode])}for mode in MODES})
                for mid,m in values.items()]
        boards=self.project(models)
        expected=[{'capability':['a','b','c'],'partial':['b','c','a'],'strict':['b','a','c']},
                  {'capability':['c','b','a'],'partial':['a','b','c'],'strict':['c','b','a']},
                  {'capability':['c','b','a'],'partial':['c','a','b'],'strict':['a','c','b']}]
        for board,orders in zip(boards,expected):
            for mode,order in orders.items():
                self.assertEqual([r['model_id']for r in board['views'][mode]],order)
                self.assertEqual([r['rank']for r in board['views'][mode]],[1,2,3])

    def test_identical_published_precision_uses_competition_ties_without_changing_saved_values(self):
        models=[uniform('b',metric(80.004)),uniform('a',metric(80.003)),uniform('c',metric(79.99))]
        rows=self.project(models)[0]['views']['partial']
        self.assertEqual([(r['model_id'],r['rank'])for r in rows],[('a',1),('b',1),('c',3)])
        self.assertEqual([r['value']for r in rows],[80.003,80.004,79.99])


if __name__=='__main__':unittest.main()
