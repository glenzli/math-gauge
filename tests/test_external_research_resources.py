"""Foreign cumulative counters and separate admission, with synthetic resources."""
from copy import deepcopy
import unittest
from unittest.mock import patch

from scripts import results_independent_research_resources as resources
from scripts.cost_reference import independent_research_reference

PRICES = {'reference': {'rates_per_million': {'input': 2, 'cached_input': .2, 'cache_write': 3, 'output': 10}}}


def usage(factor, *, inclusive=False):
    return dict(input_tokens=(30 if inclusive else 10) * factor, output_tokens=4 * factor,
        cached_input_tokens=15 * factor, cache_write_input_tokens=5 * factor,
        reasoning_output_tokens=3 * factor)


def counted():
    return resources.summarize_external_cumulative([usage(n) for n in (1, 2, 3)],
        'reference', PRICES, 'input_excludes_cache')


class ExternalResourceTests(unittest.TestCase):
    def test_final_cumulative_counts_all_rounds_once_and_reasoning_is_an_output_subset(self):
        exclusive = counted()
        inclusive = resources.summarize_external_cumulative([usage(n, inclusive=True) for n in (1, 2, 3)],
            'reference', PRICES, 'input_includes_cache')
        self.assertEqual(inclusive, exclusive)
        self.assertEqual(exclusive['tokens']['total_tokens'], 102)
        self.assertEqual(exclusive['tokens']['reasoning_output_tokens'], 9)
        self.assertAlmostEqual(exclusive['total_usd'], (30 * 2 + 45 * .2 + 15 * 3 + 12 * 10) / 1e6)
        self.assertEqual(exclusive['coverage'], dict(planned=3, complete=3, partial=0, missing=0, not_run=0))

    def test_missing_rounds_or_a_counter_reset_cannot_become_complete_cost(self):
        for snapshots in ([usage(1), usage(2)], [usage(1), usage(3), usage(2)]):
            with self.assertRaises(ValueError):
                resources.summarize_external_cumulative(snapshots, 'reference', PRICES, 'input_excludes_cache')

    def test_resources_cannot_borrow_native_adoption_or_expose_private_fields(self):
        adopted = dict(models={'foreign': dict(round_dispatches=3)})
        document = dict(schema=resources.EXTERNAL_SCHEMA, edition='1.3.0', base_edition='1.2.0',
            pricing_basis=resources.PRICING_BASIS, external_adoption_sha256='a' * 64,
            source_evidence_sha256='b' * 64, review_overhead=resources.REVIEW_OVERHEAD,
            models={'foreign': counted()})
        self.assertEqual(resources.validate_external_public(document, adopted, 'a' * 64), document)
        for changed in (dict(document, external_adoption_sha256='c' * 64),
                        dict(document, manuscript='SYNTHETIC-PRIVATE-RESOURCE'),
                        dict(document, models={'native': counted()})):
            with self.assertRaises(ValueError):
                resources.validate_external_public(changed, adopted, 'a' * 64)

    def test_full_new_cost_is_added_once_without_changing_comparison_time(self):
        report = dict(metrics=dict(earned=dict(confirmed=40), overall=dict(exact=40, lower=40, upper=40)))
        model = dict(id='foreign', retry=dict(combined=report),
                     strict=dict(nonlogical_retry_3=report), capability=dict(nonlogical_retry_3=report))
        coverage = dict(planned=42, complete=42, partial=0, missing=0, not_run=0)
        delivery = dict(planned=39, active_final=38, complete=False)
        base = dict(benchmark_version='1.2.0', models=[dict(model_id='foreign', total_usd=7,
            known_usd=7, status='observed', coverage=coverage, seconds=123, scores={}, answer_delivery=delivery)])
        original = deepcopy(base)
        external = dict(models={'foreign': dict(round_dispatches=3)})
        resource = dict(models={'foreign': counted()}, source_evidence_sha256='b' * 64)
        with patch.object(resources, 'load_public', return_value=None), \
             patch.object(resources, 'load_external_public', return_value=resource):
            result = independent_research_reference('.', dict(benchmark_version='1.3.0', models=[model]),
                base, adoption=None, external_adoption=external)
        row = result['models'][0]
        self.assertAlmostEqual(row['total_usd'], 7 + counted()['total_usd'])
        self.assertEqual(row['coverage']['complete'], 45)
        self.assertEqual(row['seconds'], 123)
        self.assertEqual(row['answer_delivery'], delivery)
        self.assertIsNone(result['review_overhead']['total_usd'])
        self.assertEqual(base, original)


if __name__ == '__main__':
    unittest.main()
