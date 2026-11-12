"""Explicit historical mathematical fixtures, before submission provenance gates."""
import copy

def before_submission_policy(policy):
    policy = copy.deepcopy(policy)
    if policy.get('version') == '0.9.0':
        policy.update(version='0.8.0', capability_policy_version='0.2.0')
        policy.pop('submission_policy_version', None)
    return policy
