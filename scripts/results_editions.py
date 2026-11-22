"""Publish assessment data for one shared UI, without copying a historical site.

The source score owner validates both editions. This module only projects their
public display values and gives the browser immutable, content-addressed data.
Original mathematical prose is shared between editions and loaded on demand.
"""
import copy
import hashlib
import html
import json
from pathlib import Path, PurePosixPath
import posixpath
import re

from math_gauge.records import evidence_bytes
from scripts.results_presentation import project_payload
from scripts.results_publication import prepare_publication, lazy_prose, data_literal as encoded
from scripts.results_harness import display_harness_labels
from scripts.results_eligibility import eligibility, ranked_models

DATA = re.compile(r'(<script\b[^>]*\bid="data"[^>]*>)([\s\S]*?)(</script>)')
JSON_SCRIPT = re.compile(r'<script\b[^>]*\bid="([^"]+)"[^>]*type="application/json"[^>]*>([\s\S]*?)</script>|<script\b[^>]*type="application/json"[^>]*\bid="([^"]+)"[^>]*>([\s\S]*?)</script>')
DEFER = re.compile(r'<script defer src="([^"]+)"></script>')


def relative(page, target):
    return posixpath.relpath(target, str(PurePosixPath(page).parent))


def chart_scenes(data):
    """Retain display geometry; never recompute mathematical scores in the UI."""
    scenes = {}
    for category in [None, *data['category_leaderboards']]:
        if category is None:
            rows = {mode: {m['id']: dict(m['retry']['combined']['metrics']['overall'],
                    value=m['retry']['combined']['metrics']['earned']['confirmed'])
                    if mode=='partial' else dict(m[mode]['nonlogical_retry_3']['metrics']['overall'],
                    value=m[mode]['nonlogical_retry_3']['metrics']['earned']['confirmed'])
                    for m in ranked_models(data['models'])} for mode in data['score_modes']}
            key = 'chart-groups'
        else:
            rows = {mode:{r['model_id']:r for r in view} for mode,view in category['views'].items()}
            key = 'category-chart-groups-'+category['id']
        values = [r['value'] for view in rows.values() for r in view.values() if r['value'] is not None]
        minimum = (min([0]+values)//20)*20
        span,zero = 100-minimum,-minimum/(100-minimum)*100
        bars = {}
        for mode,view in rows.items():
            for mid,row in view.items():
                v=row['value'];position=zero if v is None else (v-minimum)/span*100
                bars.setdefault(mid,{})[mode]={'value':v,'left':min(zero,position),'width':abs(position-zero),
                    'text':'—' if v is None else f'{v:.2f}',
                    'interval':f"完整分区间 {row['lower']:.2f}–{row['upper']:.2f}"}
        scenes[key]={'bars':bars,'zero':zero,'ticks':[
            {'position':(v-minimum)/span*100,'label':str(v)} for v in range(int(minimum),101,20)]}
    scenes['gap-groups']={'axis':data['gap_diagnostics']['axis'],
        'tables':data['gap_diagnostics']['tables']}
    return scenes


def prior_payload(page, current, old_data, projections):
    if page=='index.html':
        return project_payload(old_data)
    value=copy.deepcopy(current)
    value['benchmark_version']=old_data['benchmark_version']
    mid=value.get('model',{}).get('id')
    if mid is None:
        return value
    if mid not in projections:
        return {'benchmark_version':old_data['benchmark_version'],
                'edition_unavailable':True, 'model_id':mid}
    projection=projections[mid]
    if 'case' in value:
        cid=value['case']['id']
        for mode,conditions in projection['views'].items():
            for condition,view in conditions.items():
                original=next(row for row in view['tasks'] if row['case_id']==cid)
                value['case']['views'][mode][condition]={k:copy.deepcopy(original[k]) for k in
                    ('completion','strict_pass','response_sha256','review_sha256')}
        return value
    model=copy.deepcopy(next(m for m in old_data['models'] if m['id']==mid))
    model['public_claims']=value['model']['public_claims']
    cases=[]
    for case in value['cases']:
        row={k:copy.deepcopy(case[k]) for k in ('id','title','category_title')}
        row['views']={mode:{condition:{k:copy.deepcopy(next(t for t in view['tasks'] if t['case_id']==case['id'])[k])
                   for k in ('completion','strict_pass')} for condition,view in conditions.items()}
                   for mode,conditions in projection['views'].items()}
        cases.append(row)
    detail={k:old_data[k] for k in ('schema','benchmark_version','default_score_mode','score_modes',
        'default_attempt_condition','display_score_modes','policy')}
    detail.update(model=model,cases=cases)
    return project_payload(detail)


def retained_source_data(root, current, transition, manifests):
    """Reuse the original views already authenticated by the current source load.

    Read the retained reports directly. Do not reverse score differences or run
    the entire source validation a second time for the historical presentation.
    """
    from scripts.render_results_site import evaluation_progress, gap_diagnostics, is_fully_evaluated, selected_result
    from scripts.results_rankings import category_rankings, set_published_scores
    from math_gauge.current_assessment_admissions import selections, historical_display_source
    if selections(root):
        data = historical_display_source(root)
        if {model['id'] for model in data['models']} != set(manifests):
            raise ValueError('Historical display differs from the calibrated source cohort')
        for model in data['models']:
            actual = {'partial':{'single_attempt':model['combined'],
                                 'nonlogical_retry_3':model['retry']['combined']},
                      'capability':model['capability'], 'strict':model['strict']}
            expected = {mode:{condition:json.loads(evidence_bytes(root,ref))
                              for condition,ref in conditions.items()}
                        for mode,conditions in manifests[model['id']]['base_reports'].items()}
            if actual != display_harness_labels(expected):
                raise ValueError('Historical display altered original shared-scoring views')
        return data
    data=copy.deepcopy(current)
    data.pop('mathematical_profile',None)
    source=json.loads(evidence_bytes(root,transition['source_edition']))
    data['benchmark_version']=source['version']
    data['models']=[model for model in data['models'] if model['id'] in manifests]
    for model in data['models']:
        reports=manifests[model['id']]['base_reports']
        views={mode:{condition:json.loads(evidence_bytes(root,ref)) for condition,ref in conditions.items()}
               for mode,conditions in reports.items()}
        model['combined']=views['partial']['single_attempt']
        model['retry']['combined']=views['partial']['nonlogical_retry_3']
        model['capability'],model['strict']=views['capability'],views['strict']
        model.pop('tx_calibration',None)
        model['evaluation_progress']={c:evaluation_progress(v) for c,v in views['partial'].items()}
        model['fully_evaluated']=is_fully_evaluated(model)
        set_published_scores(model)
    data['gap_diagnostics']=gap_diagnostics(data['models'])
    data['category_leaderboards']=category_rankings(data['models'],data['policy']['groups'],result_selector=selected_result)
    fresh=[model for model in current['models'] if model['id'] not in manifests]
    fresh_roots=[str(Path(model['source_record']).parent)+'/' for model in fresh]
    data['sources']=[ref for ref in data['sources'] if not (
        any(ref['path'].startswith(prefix) for prefix in fresh_roots)
        or ref['path'].startswith('results/current-assessment-admissions/')
        or
        ref['path'].startswith(('results/edition-reassessments/','results/theorem-extension-reviews/'))
        or ref['path'].startswith('protocol/theorem-extension-calibration.'))]
    data['sources'].append(transition['source_edition'])
    return data


def _neutral_baseline(root, model, adoption):
    """Keep exact parent reports separate from admission display metadata."""
    from math_gauge.neutral_revision import document, require
    from math_gauge.current_assessment_admissions import project_score
    displayed = {'partial': {'single_attempt': model['combined'], 'nonlogical_retry_3': model['retry']['combined']},
                 'capability': model['capability'], 'strict': model['strict']}
    source = {mode: {condition: document(root, ref) for condition, ref in refs.items()}
              for mode, refs in adoption['base_reports'].items()}
    expected = ({mode: {condition: project_score(report) for condition, report in refs.items()}
                 for mode, refs in source.items()} if model.get('initial_assessment') is not None else source)
    if model.get('tx_review_amendment'):
        from math_gauge.theorem_extension_amendments import load_public as load_tx_amendment
        expected = load_tx_amendment(root,model['id'],original_baseline=source)['_baseline']
    require(displayed == expected, 'Neutral display lost its authenticated original or initial-admission projection')
    return source


def neutral_revision_data(root, base_data, *, transition=None):
    """Use the source owner's adopted reports, without recalculating task weights."""
    from math_gauge.neutral_revision import current_model_ids, load_transition, load_public
    from scripts.render_results_site import evaluation_progress, gap_diagnostics, selected_result
    from scripts.results_rankings import category_rankings, model_display_key, set_published_scores
    from scripts.results_revision_resources import load_public as load_resources, DATA_PATH, INDEX_PATH
    from scripts.results_revision_completion import load_completion
    from math_gauge.scoring import score_neutral_revision_delta
    transition = transition or load_transition(root)
    if transition is None:
        return copy.deepcopy(base_data)
    data = copy.deepcopy(base_data)
    selected_ids = current_model_ids(transition)
    original = {model['id']: model for model in base_data['models']}
    resources = load_resources(root)
    resource_models = {model['id']: model for model in resources['models']}
    data['models'] = []
    for mid, ref in transition['adoptions'].items():
        model = copy.deepcopy(original[mid])
        adopted = load_public(root, ref)
        baseline = _neutral_baseline(root, model, adopted)
        scores = adopted['_scores']
        from math_gauge.theorem_extension_amendments import load_public as load_tx_amendment, apply_model
        amendment = load_tx_amendment(root, mid, original_baseline=baseline, original_adoption=ref)
        if amendment is not None:
            baseline, scores = amendment['_baseline'], amendment['_revised']
            apply_model(model, amendment, revised=True)
        model['neutral_revision_delta'] = score_neutral_revision_delta(baseline, scores)
        model['retry']['combined'] = copy.deepcopy(scores['partial'])
        for mode in ('capability', 'strict'):
            model[mode]['nonlogical_retry_3'] = copy.deepcopy(scores[mode])
        model['evaluation_progress']['nonlogical_retry_3'] = evaluation_progress(scores['partial'])
        set_published_scores(model)
        model['neutral_revision'] = {key: copy.deepcopy(adopted[key]) for key in
            ('revision_counts', 'public_tasks', 'public_continuations', 'policy')}
        model['neutral_revision']['manifest'] = copy.deepcopy(ref)
        # This describes the new public revision reviews, not the source A1
        # reviewers or a guessed backend model for the coordinator.
        reviewers = [json.loads(evidence_bytes(root, row['review'])).get('reviewer_id')
                     for row in adopted['public_continuations']]
        model['neutral_revision']['reviewer_ids'] = sorted({value for value in reviewers
                                                           if isinstance(value, str) and value.strip()})
        model['revision_resources'] = copy.deepcopy(resource_models[mid])
        data['models'].append(model)
    data['benchmark_version'] = '1.2.0'
    data['edition_status'] = {'status': 'partial_adoption', 'completed_models': len(data['models']),
        'pending_models': sum(eligibility(mid)['ranked'] for mid in transition['pending_models']),
        'partial_test_models': sum(not eligibility(mid)['ranked'] for mid in transition['pending_models'])}
    pending = sorted(transition['pending_models'], key=lambda mid: model_display_key(original[mid]))
    data['pending_models'] = [{key: copy.deepcopy(original[mid][key]) for key in
                               ('id', 'label', 'display_order', 'presentation_eligibility') if key in original[mid]}
                              for mid in pending if eligibility(mid)['ranked']]
    data['partial_models'] = [{key: copy.deepcopy(model[key]) for key in
                               ('id', 'label', 'display_order', 'presentation_eligibility', 'ranking_values', 'answer_delivery')
                               if key in model}
                              for model in sorted(base_data['models'], key=model_display_key)
                              if model['id'] in selected_ids and not eligibility(model['id'])['ranked']]
    for model in data['partial_models']:
        model['score_values'] = {mode: selected_result(original[model['id']], mode)['metrics']['earned']['confirmed']
                                 for mode in data['score_modes']}
    data['diagnostic_source_edition'] = '1.1.0'
    if data.get('manuscript_observations') is not None:
        data['manuscript_observations']['models'] = [
            row for row in data['manuscript_observations']['models'] if row['id'] in selected_ids]
    # First-answer traits keep their authenticated 0.4.0 source. The revision
    # layer is separately reviewed and never substitutes main-score grades.
    if data.get('mathematical_profile') is not None:
        keys = ('id', 'label', 'short_label', 'theme', 'logo',
                'presentation_eligibility', 'display_order', 'ranking_values', 'ranking_complete')
        data['profile_models'] = [{key: copy.deepcopy(model[key]) for key in keys if key in model}
                                  for model in base_data['models'] if model['id'] in selected_ids]
        from math_gauge.mathematical_profile_corrections import apply_public
        corrected = apply_public(root, data['mathematical_profile'])
        if corrected is not None:
            data['mathematical_profile_baseline'] = corrected
        from math_gauge.mathematical_profile_revision import load_public_profiles as load_revised_profiles
        revised = load_revised_profiles(root, data['models'], transition=transition)
        if revised is not None:
            data['mathematical_profile_revision'] = revised
        from math_gauge.open_research import load_public as load_open_research
        research = load_open_research(root, benchmark_version='1.2.0')
        if research is not None:
            data['open_research'] = research
            data['sources'].append(research['source'])
        from math_gauge.formalization_profile import load_public as load_formalization_profile
        formalization = load_formalization_profile(root, benchmark_version='1.2.0')
        if formalization is not None:
            data['formalization_profile'] = formalization
            data['sources'].append(formalization['source'])
        # Authenticate full archived companions above, then project the current
        # edition's explicit cohort without modifying any source report.
        for key in ('mathematical_profile', 'mathematical_profile_baseline',
                    'mathematical_profile_revision', 'open_research', 'formalization_profile'):
            if data.get(key) is not None:
                data[key]['models'] = [row for row in data[key]['models'] if row['id'] in selected_ids]
    data['gap_diagnostics'] = gap_diagnostics(data['models'])
    data['category_leaderboards'] = category_rankings(data['models'], data['policy']['groups'], result_selector=selected_result)
    resource_source = INDEX_PATH if (Path(root)/INDEX_PATH).is_file() else DATA_PATH
    data['sources'].extend([transition['policy'], *transition['adoptions'].values(),
        {'path': resource_source, 'sha256': hashlib.sha256((Path(root)/resource_source).read_bytes()).hexdigest()}])
    completion = load_completion(root, transition=transition)
    if completion is not None:
        by_id = {row['id']: row for row in completion['models']}
        for model in data['models']:
            model['neutral_revision_completion'] = copy.deepcopy(by_id[model['id']])
        data['sources'].append(completion['source'])
    from math_gauge.theorem_extension_amendments import project_profile_completion, INDEX_PATH as TX_AMENDMENTS
    if any(model.get('tx_review_amendment') for model in data['models']):
        first, revised = {}, {}
        for model in data['models']:
            if model.get('tx_review_amendment'):
                amendment = load_tx_amendment(root, model['id'])
                first[model['id']] = amendment['_baseline']['strict']['nonlogical_retry_3']
                revised[model['id']] = amendment['_revised']['strict']
        for key in ('mathematical_profile', 'mathematical_profile_baseline'):
            project_profile_completion(data.get(key), first)
        project_profile_completion(data.get('mathematical_profile_revision'), revised)
        data['sources'].append({'path':TX_AMENDMENTS,
            'sha256':hashlib.sha256((Path(root)/TX_AMENDMENTS).read_bytes()).hexdigest()})
    from math_gauge.mathematical_profile_review_amendments import apply_public as apply_profile_review_amendments
    apply_profile_review_amendments(root,data)
    return data



def edition_supplemental(supplemental, *, historical, unavailable, timing, cost):
    """Install both edition-specific companions before any display controller runs."""
    extra = {} if unavailable else copy.deepcopy(supplemental)
    if historical:
        for name, value in (('timing-reference-data', timing), ('cost-reference-data', cost)):
            if name in extra:
                extra[name] = copy.deepcopy(value)
                for model in (extra[name] or {}).get('models', []):
                    if isinstance(model, dict):
                        model.pop('revision_resources', None)
                if name == 'timing-reference-data':
                    # The panel renderer adds route metadata independently of
                    # the version-specific timing document. Retain those exact
                    # page annotations while replacing its population and inputs.
                    for key in ('link_prefix', 'data_link'):
                        if key in supplemental[name]:
                            extra[name][key] = copy.deepcopy(supplemental[name][key])
    return extra


def prepare_edition_publication(files, root, current_data, *, base_data=None, base_timing=None,
                                base_cost=None, current_timing=None, current_cost=None):
    if current_data.get('benchmark_version') == '1.2.0':
        return prepare_neutral_publication(files, root, current_data, base_data=base_data,
            base_timing=base_timing, base_cost=base_cost, current_timing=current_timing,
            current_cost=current_cost)
    from math_gauge.editions import load_assessment_transition
    transition=load_assessment_transition(root)
    if transition is None:
        return prepare_publication(files,root)
    from scripts.cost_reference import build_reference as build_cost
    from scripts.timing_reference import build_reference as build_time
    root=Path(root);files=dict(files)
    old_projection={};manifests={}
    for m in current_data['models']:
        if m.get('initial_assessment'):
            continue
        manifest=json.loads(evidence_bytes(root,m['tx_calibration']['manifest']))
        manifests[m['id']]=manifest
        old_projection[m['id']]=json.loads(evidence_bytes(root,manifest['base_public_tasks']))
    old_data=retained_source_data(root,current_data,transition,manifests)
    # The retained snapshot loader returns its exact authenticated source.
    # Current publication choices are a separate display projection afterward.
    from scripts.render_results_site import gap_diagnostics, selected_result
    from scripts.results_rankings import category_rankings, set_model_display_order, set_published_scores
    themes = {model['id']: model['theme'] for model in current_data['models']}
    for model in old_data['models']:
        model['presentation_eligibility'] = eligibility(model['id'])
        if model['id'] in themes:
            model['theme'] = copy.deepcopy(themes[model['id']])
        set_published_scores(model)
    set_model_display_order(old_data['models'])
    old_data['gap_diagnostics'] = gap_diagnostics(old_data['models'])
    old_data['category_leaderboards'] = category_rankings(old_data['models'], old_data['policy']['groups'], result_selector=selected_result)
    versions=[current_data['benchmark_version'],old_data['benchmark_version']]
    old_time=build_time(root,display_data=old_data)
    old_cost=build_cost(root,display_data=old_data,timing_reference=old_time)
    for version,data in zip(versions,[current_data,old_data]):
        if version==versions[0]:continue
        prefix='versions/'+version+'/'
        files[prefix+'data.json']=json.dumps(display_harness_labels(data),ensure_ascii=False,indent=2)+'\n'
        files[prefix+'downloads/timing-reference.json']=json.dumps(old_time,ensure_ascii=False,indent=2)+'\n'
        if old_cost:files[prefix+'downloads/cost-reference.json']=json.dumps(old_cost,ensure_ascii=False,indent=2)+'\n'
        for model in data['models']:
            for mode,suffix in [('partial',''),('capability','-capability'),('strict','-strict')]:
                for condition,tail in [('single_attempt',''),('nonlogical_retry_3','-retry')]:
                    files[prefix+'downloads/'+model['id']+'-combined'+suffix+tail+'.json']=evidence_bytes(
                        root,manifests[model['id']]['base_reports'][mode][condition])
    files['assets/edition-loader.js']=(root/'scripts/templates/edition-loader.js').read_text()
    files['assets/records.js']=(root/'scripts/templates/records.js').read_text()
    prepared=prepare_publication(files,root)
    loader=next(name for name in prepared if name.startswith('assets/versioned/edition-loader.') and name.endswith('.js'))
    records=next(name for name in prepared if name.startswith('assets/versioned/records.') and name.endswith('.js'))
    scenes={v:chart_scenes(data) for v,data in zip(versions,[current_data,old_data])}
    catalog={'schema':'math-gauge.assessment-display-editions/v1','latest':versions[0],
        'source_task_version':'1.0.0','source_transition':json.loads((root/'benchmark.json').read_bytes())['assessment_transition'],
        'editions':[{'version':v,'kind':'current' if i==0 else 'before_tx_reassessment',
            'data':'data.json' if i==0 else 'versions/'+v+'/data.json'} for i,v in enumerate(versions)],
        'shared_ui':True,'copied_historical_html_pages':0}
    for page,value in list(prepared.items()):
        if not page.endswith('.html'):continue
        match=DATA.search(value)
        if match is None:continue
        current=json.loads(match[2]);prior=prior_payload(page,current,old_data,old_projection)
        supplemental={}
        for m in JSON_SCRIPT.finditer(value):
            name=m[1] or m[3]
            if name!='data':supplemental[name]=json.loads(m[2] or m[4])
        config={'schema':'math-gauge.edition-view-config/v1','latest':versions[0],'page':page,'versions':{},'scripts':DEFER.findall(value)}
        value=DEFER.sub('',value)
        value=DATA.sub(lambda m:m[1]+'{}'+m[3],value)
        value=JSON_SCRIPT.sub(lambda m:m[0][:m[0].find('>')+1]+'{}</script>',value)
        for index,(version,payload) in enumerate(zip(versions,[current,prior])):
            payload['edition_paths']={'download_prefix':'' if index==0 else 'versions/'+version+'/'}
            if page=='index.html':payload['chart_scenes']=scenes[version]
            extra=edition_supplemental(supplemental, historical=bool(index),
                unavailable=payload.get('edition_unavailable',False), timing=old_time, cost=old_cost)
            if page=='index.html' and extra.get('timing-reference-data'):
                extra['timing-reference-data']['data_link']=payload['edition_paths']['download_prefix']+'downloads/timing-reference.json'
            # Provider icons in old shared references were read before public
            # asset projection. Match the already projected route-relative logo.
            if index and page=='index.html' and old_cost:
                logos={m['id']:m['logo'] for m in current['models']}
                for model in extra['cost-reference-data']['models']:model['logo']=copy.deepcopy(logos[model['model_id']])
            envelope={'schema':'math-gauge.edition-page-data/v1','edition':version,'page':page,'data':payload,'supplemental':extra}
            body=encoded(envelope);key=hashlib.sha256(body.encode()).hexdigest()
            target='data/editions/'+version+'/'+page.removesuffix('.html')+'.json'
            script='assets/data/'+key+'.js'
            prepared[target]=body+'\n';prepared[script]='window.MGEditionData('+encoded(key)+','+body+');\n'
            config['versions'][version]={'key':key,'payload':relative(page,script),
                'label':{'zh':version,'en':version},
                'status':{'zh':'','en':''}}
        value=lazy_prose(page,value,prepared)
        if 'data-lazy-prose=' in value and relative(page,records) not in config['scripts']:
            config['scripts'].append(relative(page,records))
        value=value.replace('<main','<main data-edition-content',1)
        selector=('<label class="edition-switch"><span data-lang-content="zh">评价版</span>'
            '<span data-lang-content="en" hidden>Edition</span><select data-edition-select aria-label="Assessment edition"></select></label>')
        value=value.replace('</nav>',selector+'</nav>',1)
        config_html='<script type="application/json" id="edition-config">'+encoded(config)+'</script>'
        value=value.replace('</head>',config_html+'<script defer src="'+relative(page,loader)+'"></script></head>')
        value=value.replace('<html ','<html data-edition-loading ',1)
        prepared[page]=value
    prepared['editions.json']=json.dumps(catalog,ensure_ascii=False,indent=2)+'\n'
    return prepared


def _neutral_payload(page, base, data, projections):
    if page == 'index.html':
        result = project_payload(data)
        logos = {model['id']: model['logo'] for model in base['models']}
        for model in result['models']:
            model['logo'] = copy.deepcopy(logos[model['id']])
        return result
    result = copy.deepcopy(base)
    result['benchmark_version'] = '1.2.0'
    result['diagnostic_source_edition'] = '1.1.0'
    mid = base.get('model', {}).get('id')
    if mid is None:
        return result
    models = {model['id']: model for model in data['models']}
    if mid not in models:
        awaiting = {row['id'] for key in ('pending_models', 'partial_models') for row in data[key]}
        reason = ('continuation_pending' if eligibility(mid)['ranked'] else 'partial_test') if mid in awaiting else 'not_selected_for_edition'
        return {'benchmark_version': '1.2.0', 'model_id': mid, 'edition_unavailable': True,
                'edition_fallback': '1.1.0', 'edition_unavailable_reason': reason}
    model, projection = copy.deepcopy(models[mid]), projections[mid]
    def task_views(cid, target):
        for mode in data['score_modes']:
            task = next(row for row in projection['views'][mode]['nonlogical_retry_3']['tasks'] if row['case_id'] == cid)
            target[mode]['nonlogical_retry_3'] = {key: copy.deepcopy(task[key]) for key in
                ('completion', 'strict_pass', 'response_sha256', 'review_sha256', 'neutral_revision') if key in task}
    if 'case' in result:
        task_views(result['case']['id'], result['case']['views'])
        return result
    from scripts.results_presentation import model_view
    model['public_claims'] = copy.deepcopy(base['model']['public_claims'])
    result['model'] = model_view(model, model_page=True)
    result['model']['logo'] = copy.deepcopy(base['model']['logo'])
    for case in result['cases']:
        task_views(case['id'], case['views'])
    return result


def _neutral_evidence_sections(root, data):
    """Render only public continuation originals; private rows stay aggregate-only."""
    from scripts.results_details import EvidenceRenderer, source_link
    renderer, pages = EvidenceRenderer(), {}
    for model in data['models']:
        for row in model['neutral_revision']['public_continuations']:
            page = 'models/' + model['id'] + '/cases/' + row['case_id'] + '.html'
            answer = renderer.add(evidence_bytes(root, row['answer']).decode())
            review_raw = evidence_bytes(root, row['review']).decode()
            reviewer = json.loads(review_raw).get('reviewer_id')
            attribution = ('<p class="panel-desc"><span data-lang-content="zh">续答评审：</span>'
                '<span data-lang-content="en" hidden>Continuation reviewer: </span>'
                + html.escape(reviewer) + '</p>') if isinstance(reviewer, str) and reviewer.strip() else ''
            review = renderer.add('```json\n' + review_raw + '\n```')
            links = ' · '.join(source_link(Path(root)/row[key]['path'], page, label, root=root)
                for key, label in [('input', '续答输入 / Input'), ('answer', '完整续答 / Answer'), ('review', '续答评审 / Review')])
            pages[page] = ('<section class="panel" data-assessment-only="1.2.0"><div class="panel-head"><h2>'
                '<span data-lang-content="zh">1.2 · 中性续答</span><span data-lang-content="en" hidden>1.2 · Neutral continuation</span>'
                '</h2></div>'+attribution+'<p>'+links+'</p><div class="prose" data-original>'+answer+'</div>'
                '<details><summary><span data-lang-content="zh">续答原评</span><span data-lang-content="en" hidden>Original continuation review</span>'
                '</summary><div class="prose" data-original>'+review+'</div></details></section>')
    return renderer.finish(pages) if pages else {}


def prepare_neutral_publication(files, root, current_data, *, base_data, base_timing,
                                base_cost, current_timing, current_cost):
    """Extend the same UI to 1.2 while retaining independent 1.1 and 1.0 data."""
    from math_gauge.neutral_revision import load_public
    from scripts.results_revision_resources import load_public as load_resources
    root, files = Path(root), dict(files)
    if base_data is None or base_data['benchmark_version'] != '1.1.0':
        raise ValueError('Continuation publication requires its already authenticated 1.1 display')
    files['data.json'] = json.dumps(display_harness_labels(base_data), ensure_ascii=False, indent=2)+'\n'
    files['downloads/timing-reference.json'] = json.dumps(base_timing, ensure_ascii=False, indent=2)+'\n'
    files['downloads/cost-reference.json'] = json.dumps(base_cost, ensure_ascii=False, indent=2)+'\n'
    for model in base_data['models']:
        for mode, suffix in [('partial', ''), ('capability', '-capability'), ('strict', '-strict')]:
            for condition, tail in [('single_attempt', ''), ('nonlogical_retry_3', '-retry')]:
                score = (model['combined'] if condition == 'single_attempt' else model['retry']['combined']) if mode == 'partial' else model[mode][condition]
                files['downloads/'+model['id']+'-combined'+suffix+tail+'.json'] = json.dumps(score, ensure_ascii=False, indent=2)+'\n'
    prepared = prepare_edition_publication(files, root, base_data)
    notes_script = next(name for name in prepared if name.startswith('assets/versioned/edition-notes.') and name.endswith('.js'))
    # Move the full old six-view downloads without renaming their source reports.
    for name in list(prepared):
        if name == 'data.json' or name in {'downloads/timing-reference.json', 'downloads/cost-reference.json'} or re.fullmatch(r'downloads/[^/]+-combined(?:-capability|-strict)?(?:-retry)?\.json', name):
            prepared['versions/1.1.0/'+name] = prepared.pop(name)
    prepared['data.json'] = json.dumps(display_harness_labels(current_data), ensure_ascii=False, indent=2)+'\n'
    prepared['downloads/timing-reference.json'] = json.dumps(current_timing, ensure_ascii=False, indent=2)+'\n'
    prepared['downloads/cost-reference.json'] = json.dumps(current_cost, ensure_ascii=False, indent=2)+'\n'
    prepared['downloads/continuation-resources.json'] = json.dumps(load_resources(root), ensure_ascii=False, indent=2)+'\n'
    projections = {}
    for model in current_data['models']:
        adoption = load_public(root, model['neutral_revision']['manifest'])
        amendment = None
        if model.get('tx_review_amendment'):
            from math_gauge.theorem_extension_amendments import load_public as load_tx_amendment
            amendment = load_tx_amendment(root, model['id'])
        projections[model['id']] = (adoption['_public_tasks'] if amendment is None
                                    else amendment['_public_tasks']['revised'])
        for mode, suffix in [('partial', ''), ('capability', '-capability'), ('strict', '-strict')]:
            selected = adoption['scores'][mode] if amendment is None else amendment['revised'][mode]
            prepared['downloads/'+model['id']+'-combined'+suffix+'-retry.json'] = evidence_bytes(root, selected)
    scenes = chart_scenes(current_data)
    evidence_sections = _neutral_evidence_sections(root, current_data)
    config_pattern = re.compile(r'(<script type="application/json" id="edition-config">)([\s\S]*?)(</script>)')
    for page, value in list(prepared.items()):
        if not page.endswith('.html'):
            continue
        match = config_pattern.search(value)
        if match is None:
            continue
        config = json.loads(match[2])
        base_target = 'data/editions/1.1.0/'+page.removesuffix('.html')+'.json'
        base_envelope = json.loads(prepared[base_target])
        payload = _neutral_payload(page, base_envelope['data'], current_data, projections)
        payload['edition_paths'] = {'download_prefix': ''}
        if page == 'index.html':
            payload['chart_scenes'] = scenes
        extra = edition_supplemental(base_envelope['supplemental'], historical=True,
            unavailable=payload.get('edition_unavailable', False), timing=current_timing, cost=current_cost)
        if page == 'index.html':
            logos = {model['id']: model['logo'] for model in base_envelope['data']['models']}
            for name, id_key in [('timing-reference-data', 'id'), ('cost-reference-data', 'model_id')]:
                if extra.get(name):
                    for model in extra[name]['models']:
                        model['logo'] = copy.deepcopy(logos[model[id_key]])
        # Rewrite the 1.1 route annotation; the source report bytes are unchanged.
        base_envelope['data']['edition_paths'] = {'download_prefix': 'versions/1.1.0/'}
        if page=='index.html' and base_envelope['supplemental'].get('timing-reference-data'):
            base_envelope['supplemental']['timing-reference-data']['data_link'] = 'versions/1.1.0/downloads/timing-reference.json'
        for version, envelope in [('1.1.0', base_envelope), ('1.2.0', {
                'schema':'math-gauge.edition-page-data/v1','edition':'1.2.0','page':page,
                'data':payload,'supplemental':extra})]:
            body = encoded(envelope)
            key = hashlib.sha256(body.encode()).hexdigest()
            script = 'assets/data/'+key+'.js'
            prepared['data/editions/'+version+'/'+page.removesuffix('.html')+'.json'] = body+'\n'
            prepared[script] = 'window.MGEditionData('+encoded(key)+','+body+');\n'
            config['versions'][version] = {'key':key,'payload':relative(page,script),
                'label':{'zh':version,'en':version},'status':{'zh':'','en':''}}
        # Retain historical routes. A bare direct link for a model withdrawn
        # from this edition opens its available source, rather than a pending UI.
        config['latest'] = ('1.1.0' if payload.get('edition_unavailable_reason') ==
                            'not_selected_for_edition' else '1.2.0')
        config['scripts'].append(relative(page, notes_script))
        value = config_pattern.sub(lambda m:m[1]+encoded(config)+m[3], value)
        if page in evidence_sections:
            section = lazy_prose(page, evidence_sections[page], prepared)
            value = value.replace('</main>', section+'</main>', 1)
        prepared[page] = value
    catalog = json.loads(prepared['editions.json'])
    catalog['latest'] = '1.2.0'
    catalog['editions'][0].update(kind='before_neutral_revision', data='versions/1.1.0/data.json')
    catalog['editions'].insert(0, {'version':'1.2.0','kind':'current_partial_adoption','data':'data.json'})
    catalog['source_neutral_revision_transition'] = json.loads((root/'benchmark.json').read_bytes())['neutral_revision_transition']
    prepared['editions.json'] = json.dumps(catalog, ensure_ascii=False, indent=2)+'\n'
    return prepared
