"""Bind an independent research weighting policy to the selected credit sources."""

from pathlib import Path

from . import independent_research_value as value
from . import taste_v130 as flow


VERSION = '0.1.0'
SCHEMA = 'math-gauge.independent-research-item-weight-policy/v1'
POLICY_PATH = value.POLICY_PATH.with_name('item-weight-policy.json')


def load_policy(path, *, value_binding, strict_binding):
    """Return the selected relative weights and provenance for the public projection."""
    flow._need(value_binding is not None and value_binding['index_sha256'] is not None
               and strict_binding is not None and strict_binding['index_sha256'] is not None,
               'Item weights require both validated value and strict-credit indexes')
    sources = dict(value_policy_sha256=value_binding['policy_sha256'],
                   value_results_sha256=value_binding['index_sha256'],
                   strict_credit_policy_sha256=strict_binding['policy_sha256'],
                   strict_credit_results_sha256=strict_binding['index_sha256'])
    raw = Path(path).read_bytes()
    policy = value._json(raw)
    flow._need(value._fields(policy, ('schema', 'version', 'edition', 'status', 'item_weights', *sources))
               and policy['schema'] == SCHEMA and policy['version'] == VERSION
               and policy['edition'] == flow.EDITION and policy['status'] == 'local-user-selected-item-weights',
               'Invalid independent research item weight policy')
    weights = policy['item_weights']
    flow._need(value._fields(weights, value.AXES) and all(type(weight) is int and weight > 0 for weight in weights.values()),
               'Item weights must give positive integral weight to both research components')
    flow._need(all(policy[key] == digest for key, digest in sources.items()),
               'Item weights bind different value or strict-credit sources')
    return weights, dict(version=VERSION, policy_sha256=flow._sha(raw), **sources)
