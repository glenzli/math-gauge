"""Bind native replay inputs that are separate from the portable request envelope."""
from .neutral_revision import load_policy
from .theorem_extension_calibration import document, read, require
from .dot_rerun_sources import REJECTION, _authorizes

SCHEMA = 'math-gauge.dot-neutral-replay-observation/v1'


def verify_replays(root, private_root, sources, neutral):
    """Validate completed native replay sources, never label forced work a final."""
    policy = load_policy(root, neutral['policy'])
    contexts = {call['context_id'] for row in sources['slots'].values() for call in row['physical_calls']}
    for row in neutral['rows']:
        base = sources['slots'][row['case_id']+':A1']
        continuation = row['continuation']
        status = continuation['status']
        require(status in {'reviewed','delivery_failed'}, 'Dot revision is not settled')
        found = []
        for ref in continuation.get('sources',[]):
            if ref['path'].endswith('.json'):
                original = document(private_root,ref)
                if original.get('schema') == SCHEMA:
                    found.append(original)
        require(len(found) == 1, 'Each selected Dot continuation needs one observed native replay')
        [obs] = found
        expected = {'schema','case_id','context_id','request','parent_answer','standards','invitation',
                    'source','status','answer','review','primary_correction','technical_recovery'}
        require(set(obs) == expected and obs['case_id'] == row['case_id']
                and isinstance(obs['context_id'],str) and obs['context_id'].strip()
                and obs['context_id'] not in contexts
                and read(private_root,obs['source'])
                and obs['request']['sha256'] == base['physical_calls'][-1]['request']['sha256']
                and read(private_root,obs['request']) == read(private_root,base['physical_calls'][-1]['request'])
                and obs['parent_answer']['sha256'] == row['first_response_sha256']
                and read(private_root,obs['parent_answer'])
                and all(read(private_root,obs[k]) == read(root,policy[k]) for k in ('standards','invitation')),
                'Native replay must use unchanged fixed task, exact accepted parent and common prompt only')
        contexts.add(obs['context_id'])
        technical = obs['technical_recovery']
        if technical is not None:
            require(set(technical) == {'authorization','original_context_id','original_parent',
                                      'original_archive','original_observation'},
                    'Original neutral capture cannot be discarded')
            _authorizes(private_root,technical['authorization'],'observed_damaged_neutral_recapture:'+row['case_id'])
            original_id = technical['original_context_id']
            require(isinstance(original_id,str) and original_id.strip() and original_id not in contexts
                    and bool(read(private_root,technical['original_observation'])),
                    'Keep the first physical neutral execution separately')
            contexts.add(original_id)
            old = read(private_root,technical['original_archive'])
            require(any(c < 32 and c not in (9,10,13) for c in old),
                    'Neutral evidence replacement needs proven archive corruption, not a second mathematical attempt')
            old_parent = read(private_root,technical['original_parent'])
            if technical['original_parent']['sha256'] != row['first_response_sha256']:
                root_parent = base['physical_calls'][0].get('archive')
                require(root_parent is not None and old_parent == read(private_root,root_parent),
                        'Original neutral trajectory lost its own prior parent')
        response = obs['answer']
        primary = document(private_root,obs['review'])
        if status == 'reviewed':
            require(obs['status']=='observed_full_native_final' and response == continuation['answer']
                    and obs['primary_correction'] is None and obs['review'] == continuation['review']
                    and primary['response_sha256']==response['sha256'],
                    'Neutral normal score must bind the actual final, never a workspace-only artifact')
        else:
            require(row['case_id']+':A1' == REJECTION and obs['status']=='platform_rejected_after_cutoff'
                    and response == continuation['cutoff_content']
                    and obs['review'] == continuation['cutoff_review']
                    and primary['content_sha256'] == response['sha256'],
                    'A policy-rejected continuation cannot become normal delivery')
            original = document(private_root,obs['primary_correction'])
            require(original['normal_native_final'] is False and original['answer_sha256']==response['sha256']
                    and original['answer_bytes']==response['bytes']
                    and original['RMC']==original['SMC']==0
                    and primary['capability_completion']['exact']==original['MC_if_forced_content_admitted']/100,
                    'Nonfinal MC must retain the independently adjudicated same-attempt original work only')
        read(private_root,response)
