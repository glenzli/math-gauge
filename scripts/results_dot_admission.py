"""Add one selected Dot row without replacing any archived cohort/model."""
from copy import deepcopy
import html
import json

from math_gauge.dot_rerun_admission import MODEL, LABEL
from math_gauge.neutral_revision import CONDITION


def add_edition_120(data, base_data, admission):
    if admission is None:
        return
    from scripts.render_results_site import selected_result, gap_diagnostics, evaluation_progress
    from scripts.results_rankings import category_rankings, set_published_scores, model_display_key
    from math_gauge.scoring import score_neutral_revision_delta
    from math_gauge.native_observations import require
    require(data['benchmark_version'] == '1.2.0' and not any(m['id'] == MODEL for m in data['models']),
            'Dot additive selection may not replace another model or edition')
    old_dot = next(m for m in base_data['models'] if m['id'] == 'dot-underlying-model-20261108')
    base, final, source = (admission[k] for k in ('base', 'final', 'public_source'))
    revised = admission['revised']
    delivery = dict(active_final=source['active_final'], forced_content=source['forced_content'],
                    blank=39-source['active_final']-source['forced_content'], planned=39)
    for key in ('capability', 'strict', 'partial'):
        summary = final[key].get('submission_summary', {})
        require(all(summary.get(k) == v for k, v in delivery.items()),
                'Dot public delivery counts differ from the rule-selected score')
    model = dict(id=MODEL, label=LABEL, short_label=LABEL, source_model_label=LABEL,
        logo=deepcopy(old_dot['logo']), theme=deepcopy(old_dot['theme']),
        harness={'name':'Dot native harness', 'model_override':None, 'effort_override':None},
        harness_display_name='Dot native harness', record_kind='native_harness', fully_evaluated=True,
        source_record=revised['source_record']['path'], test_order=dict(date='2026-11-25',
            started_at=source['first_recorded_dispatch_utc'], basis='first_recorded_dispatch',
            source_sha256=source['public_dispatch_observation_sha256']),
        presentation_eligibility=dict(status='listed', ranked=True), content_rates=None,
        answer_delivery=dict(delivery,delivered=delivery['active_final'],
                             undelivered=delivery['blank'], pending=0),
        combined=deepcopy(base['partial']['single_attempt']),
        retry={'combined':deepcopy(final['partial']), 'note_en':'Separate native execution; backend and effort unknown.',
               'note':'独立 Dot 原生运行，底层型号与推理强度未知。'},
        capability={'single_attempt':deepcopy(base['capability']['single_attempt']),CONDITION:deepcopy(final['capability'])},
        strict={'single_attempt':deepcopy(base['strict']['single_attempt']),CONDITION:deepcopy(final['strict'])},
        evaluation_progress={'single_attempt':evaluation_progress(base['partial']['single_attempt']),
                             CONDITION:evaluation_progress(final['partial'])},
        alignment_selfcheck=deepcopy(final['partial']['alignment_selfcheck']),
        lean_formalization_breakdown=deepcopy(final['partial']['lean_formalization_breakdown']),
        neutral_revision_delta=score_neutral_revision_delta(base, final),
        neutral_revision={k:deepcopy(revised[k]) for k in ('revision_counts','public_tasks','public_continuations','policy')}
                         | {'manifest':deepcopy(revised['_selection'])})
    set_published_scores(model)
    # Do not renumber incumbent display metadata (an original 1.3 baseline assertion).
    model['display_order'] = max(m['display_order'] for m in data['models']) + 1
    data['models'].append(model)
    data['edition_status']['completed_models'] = len(data['models'])
    data['gap_diagnostics'] = gap_diagnostics(data['models'])
    data['category_leaderboards'] = category_rankings(data['models'], data['policy']['groups'],
                                                     result_selector=selected_result)
    data['sources'].append(admission['selection'])


def add_edition_130(root, display_source, envelope, original, admission, board, abilities, categories):
    if admission is None:
        return
    from math_gauge import independent_research_value as value
    from math_gauge.independent_research_native import project_model
    from math_gauge.research_profile import VALUE_POLICY_PATH, load_policy, project_models
    from math_gauge.native_observations import require
    from scripts.preview_open_research_v130 import public_row
    from scripts.results_editions import chart_scenes
    require(not any(m['id']==MODEL for m in display_source['models']),
            'The original 1.3 source must not be rewritten to insert the new Dot record')
    require(all(k in board for k in ('item_weights','item_weight_binding','value_binding','strict_credit_binding')),
            'Dot independent result needs the existing settled 1.3 score construct')
    boards = dict(value=board['value_binding']['policy_sha256'],
                  strict_credit=board['strict_credit_binding']['policy_sha256'],
                  item_weight=board['item_weight_binding']['policy_sha256'])
    require(boards == admission['research']['policy_bindings'],
            'Dot and the retained leaderboard use different 1.3 policies')
    new_model = deepcopy(next(m for m in original['data']['models'] if m['id']==MODEL))
    envelope['data']['models'].append(new_model)
    from scripts.results_rankings import category_rankings
    from scripts.render_results_site import selected_result, gap_diagnostics
    combined = [*display_source['models'], deepcopy(new_model)]
    combined[-1].update(combined=admission['base']['partial']['single_attempt'],
        retry={'combined':admission['final']['partial']},
        capability={CONDITION:admission['final']['capability']},
        strict={CONDITION:admission['final']['strict']})
    categories_source = category_rankings(combined, display_source['policy']['groups'], result_selector=selected_result)
    envelope['data']['category_leaderboards'] = categories_source
    scene_data = dict(display_source, models=combined, category_leaderboards=categories_source,
                      gap_diagnostics=gap_diagnostics(combined))
    envelope['data']['chart_scenes'] = chart_scenes(scene_data)
    # Base group reweighting and the 2:1 item use the unmodified shared scorer.
    policy, _ = value.load_policy(root / value.POLICY_PATH)
    research = admission['research']['research']
    final = admission['final']
    result = project_model(dict(MC=final['capability'],RMC=final['partial'],SMC=final['strict']),
                           dict(policy,item_weights=board['item_weights']), research)
    board['rows'].append(public_row(MODEL,LABEL,result,kind='dot-native-independent-research'))
    board['dot_binding'] = dict(selection=admission['selection'], base=admission['revised']['_selection'],
                                research_source_sha256=research['source_sha256'])
    abilities['dot_binding'] = deepcopy(board['dot_binding'])
    categories[MODEL] = result['category_points']
    profile, _ = load_policy(root / VALUE_POLICY_PATH)
    denominators = json.loads((root / 'protocol/mathematical-taste/v1.3.0/policy.json').read_bytes())['new_axis_denominators']
    from math_gauge.dot_native_profiles import project_edition_130_abilities
    added_profile, profile_binding = project_edition_130_abilities(root, result, profile, denominators)
    if profile_binding is not None:
        added_profile['native_profile_binding'] = profile_binding
    # Current depth/open values are supplied solely by the separately reviewed
    # structural component. Never present the retired capacity injection here.
    for stage in ('first','revision'):
        for axis in ('depth_v130','open_research_v130'):
            metric = added_profile['stages'][stage].get(axis)
            if metric is not None:
                metric.update(lower=0, upper=100, exact=None, confirmed=0, base_metric=None, base_coverage=None)
                metric['task_metric'].update(lower=0, upper=100, exact=None, confirmed=0)
                metric['task_coverage'].update(reviewed=0, components_reviewed=0)
    abilities['by_model'][MODEL] = added_profile
    return research['normal_rounds']


def detail_page(admission, *, root=None):
    # No archived 1.1 details, private cases, or phantom timing rows for this run.
    timing = ''
    if root is not None:
        from math_gauge.dot_rerun_timings import detail_section
        timing = detail_section(root)
    heading = html.escape(LABEL)
    source = admission['public_source']
    selected_rounds = source['designated_file_rounds']
    links = []
    for version, prefix in [('1.2.0','../../downloads/'), ('1.3.0','../../versions/1.3.0/downloads/')]:
        for label, suffix in [('MC','-capability'), ('RMC',''), ('SMC','-strict')]:
            links.append(f'<li><a href="{prefix}{MODEL}-combined{suffix}-retry.json">{version} {label}</a></li>')
    return ('<!doctype html><html lang="en"><head><meta charset="utf-8">'
            '<meta name="viewport" content="width=device-width,initial-scale=1">'
            f'<title>{heading} · Math Gauge</title>'
            '<link rel="stylesheet" href="../../assets/results.css"></head>'
            '<body class="model-page" data-math-gauge-static-result="dot-20261125"><header class="topbar"><nav aria-label="Math Gauge">'
            '<a href="../../index.html">Math Gauge</a></nav></header>'
            f'<main><h1>{heading}</h1>'
            '<p>Separate Dot native run on the frozen 1.0.0 input set. Backend and effort unverified.</p>'
            '<p>Test date: 2026-11-25. AI review; human mathematical approval pending.</p>'
            f'<p>Rule-selected A1 deliveries: {source["active_final"]}/39. '
            f'C003 self-check rounds accepted by explicit file designation: {selected_rounds}/3. '
            'An accepted file is not a byte-certified inline transport receipt.</p>'
            '<p>Technical recovery did not select by grade. Original delivery incidents are retained separately.</p><ul>'
            + ''.join(links) + '</ul>' + timing + '<p><a href="../../index.html">Leaderboard</a></p></main></body></html>')
