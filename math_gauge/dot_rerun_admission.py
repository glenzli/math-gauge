"""Explicit additive public selection for a separately verified native Dot run."""
import hashlib
import json
from pathlib import Path

from .dot_rerun_sources import MODEL, DATASET
from .dot_rerun_evidence_replacement import REPLACEMENT
from .independent_research_external import policy_bindings
from .independent_research_native import validate_public_model
from .neutral_revision import CONDITION, MODES, load_public as load_neutral
from .theorem_extension_calibration import _hash, document, read, require

SELECTION = 'results/edition-admissions/v0.1.0/dot-20261125.json'
ARCHIVE = f'results/v1.0.0/{MODEL}/20261125/'
LABEL = 'Dot (261125)'


def load_public(root, *, historical=False):
    root = Path(root)
    path = root / SELECTION
    if not path.exists() and not path.is_symlink():
        return None
    require(path.is_file() and not path.is_symlink(), 'Unsafe Dot selection path')
    raw = path.read_bytes()
    ref = dict(path=SELECTION, bytes=len(raw), sha256=hashlib.sha256(raw).hexdigest())
    selection = document(root, ref)
    if historical and 'prior_selection' in selection:
        prior_ref = selection['prior_selection']
        require(prior_ref['path']==ARCHIVE+REPLACEMENT+'/prior-selection.json',
                'Historical lookup needs the exact selected original archive')
        selection = document(root,prior_ref)
        ref = dict(path=SELECTION, bytes=prior_ref['bytes'], sha256=prior_ref['sha256'])
    fixed = dict(schema='math-gauge.dot-additive-edition-admission/v1', model_id=MODEL,
                 source_benchmark_version='1.0.0', human_review='pending',
                 formal_comparison_eligible=False, new_candidate_calls=0)
    fields = set(fixed) | {'source', 'revised', 'research', 'paired_validation_sha256'}
    is_replacement = 'prior_selection' in selection
    require(set(selection) == fields | ({'prior_selection'} if is_replacement else set())
        and all(type(selection[k]) is type(v) and selection[k] == v for k, v in fixed.items())
        and _hash(selection['paired_validation_sha256']), 'Invalid Dot additive edition selection')
    result_dir = ARCHIVE+(REPLACEMENT+'/' if is_replacement else '')
    paths = {'source':'native-source.json','revised':'neutral-public.json','research':'independent-research-public.json'}
    require(all(selection[k]['path']==result_dir+name for k,name in paths.items()),
            'Dot selection must use its actual separate 1.0.0 archive')
    source = document(root, selection['source'])
    source_fields = dict(schema='math-gauge.dot-native-rerun-public-source/v1',
        model_id=MODEL, model_label=LABEL, record_id='20261125', dataset_sha256=DATASET,
        source_benchmark_version='1.0.0', backend_sku=None, model_override=None, effort_override=None,
        transport_import_validated=False, fork_turns='none', isolation='instruction_only')
    require(set(source) == set(source_fields) | {'first_recorded_dispatch_utc',
        'private_source_sha256', 'public_dispatch_observation_sha256', 'active_final',
        'forced_content', 'designated_file_rounds'}
        and all(type(source[k]) is type(v) and source[k] == v for k, v in source_fields.items())
        and all(_hash(source[k]) for k in ('private_source_sha256', 'public_dispatch_observation_sha256'))
        and all(type(source[k]) is int and 0 <= source[k] <= maximum for k,maximum in
                [('active_final',39), ('forced_content',39), ('designated_file_rounds',3)])
        and source['active_final'] + source['forced_content'] <= 39,
        'Native public source disclosed private evidence or changed delivery identity')
    from datetime import datetime, timedelta, timezone
    stamp = datetime.fromisoformat(source['first_recorded_dispatch_utc'].replace('Z','+00:00'))
    require(stamp.tzinfo is not None and stamp.utcoffset() == timedelta(0)
            and stamp.astimezone(timezone(timedelta(hours=8))).date().isoformat() == '2026-11-25',
            'Dot selection needs the original UTC dispatch, not its label')
    if is_replacement:
        prior_ref = selection['prior_selection']
        require(prior_ref['path']==result_dir+'prior-selection.json',
                'Replacement must retain the idempotent original public selection')
        prior = document(root,prior_ref)
        require(set(prior)==fields and all(type(prior[k]) is type(v) and prior[k]==v for k,v in fixed.items())
                and all(prior[k]['path']==ARCHIVE+name for k,name in paths.items()),
                'Replacement prior source is not the original same-model selection')
        old_source = document(root,prior['source'])
        old_neutral = load_neutral(root,prior['revised'])
        old_research = document(root,prior['research'])
        require(old_source.get('model_id')==MODEL and old_neutral['model_id']==MODEL
                and old_neutral['source_record']==prior['source'] and old_research['base_admission']==prior['revised']
                and old_research['base_reports']==old_neutral['scores']
                and all(source[k]==old_source[k] for k in ('first_recorded_dispatch_utc','public_dispatch_observation_sha256')),
                'Keep original test date, source identity and exact earlier evidence')
    revised = load_neutral(root, selection['revised'])
    require(revised['model_id'] == MODEL and revised['record_id'] == '20261125'
            and revised['source_record'] == selection['source']
            and revised['revision_counts']['pending'] == 0
            and revised['_scores']['partial']['model_label'] == LABEL,
            'Dot revision selected another or an unsettled native record')
    final = {mode: revised['_scores'][mode] for mode in MODES}
    base = {mode: {condition:document(root, item) for condition,item in refs.items()}
            for mode,refs in revised['base_reports'].items()}
    for mode in MODES:
        require(all(item['model_label'] == LABEL for item in base[mode].values())
                and final[mode]['model_label'] == LABEL and final[mode]['metrics']['overall']['exact'] is not None
                and base[mode][CONDITION]['metrics']['overall']['exact'] is not None,
                'Dot may not rank provisional selected arithmetic or another model')
        require(all(item.get('source_benchmark_version') == '1.0.0'
                and item.get('source_bindings', {}).get('dot_private_source_sha256')
                    == source['private_source_sha256']
                for condition,item in base[mode].items()),
                'Dot revision must derive from the separately verified native 1.0.0 run')
        if is_replacement:
            require(revised['base_reports'][mode]['single_attempt']['path']==
                    result_dir+'base/single_attempt-'+mode+'.json',
                    'Current first-attempt selector must point to the new effective first condition')
    research = document(root, selection['research'])
    require(set(research) == {'schema','edition','model_id','base_admission','base_reports',
                              'policy_bindings','research','private_research_sha256'}
            and research['schema'] == 'math-gauge.dot-independent-research-public/v1'
            and research['edition'] == '1.3.0' and research['model_id'] == MODEL
            and research['base_admission'] == selection['revised']
            and research['base_reports'] == revised['scores']
            and research['policy_bindings'] == policy_bindings(root)
            and _hash(research['private_research_sha256']),
            '1.3 native Dot research must bind this exact approved 1.2 parent')
    if is_replacement:
        require(all(research[k]==old_research[k] for k in ('private_research_sha256','research','policy_bindings')),
                'The original independent-research trajectory is outside the replacement scope')
    require(validate_public_model(research['research'])['source_sha256']
            == research['private_research_sha256'], 'Native research lost its private proof binding')
    require(all(v['exact'] is not None for v in research['research']['strict_credit'].values()),
            'Native research item is not settled in every mode')
    return dict(selection=ref, public_source=source, revised=revised, final=final,
                base=base, research=research,research_ref=selection['research'],
                paired_validation_sha256=selection['paired_validation_sha256'],
                prior_selection=selection.get('prior_selection'))
