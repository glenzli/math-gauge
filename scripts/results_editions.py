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
                    for m in data['models']} for mode in data['score_modes']}
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
    from scripts.results_rankings import category_rankings, published_value
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
        model['ranking_values']={mode:published_value(selected_result(model,mode)['metrics']['earned']['confirmed'])
                                 for mode in data['score_modes']}
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



def edition_supplemental(supplemental, *, historical, unavailable, timing, cost):
    """Install both edition-specific companions before any display controller runs."""
    extra = {} if unavailable else copy.deepcopy(supplemental)
    if historical:
        for name, value in (('timing-reference-data', timing), ('cost-reference-data', cost)):
            if name in extra:
                extra[name] = copy.deepcopy(value)
                if name == 'timing-reference-data':
                    # The panel renderer adds route metadata independently of
                    # the version-specific timing document. Retain those exact
                    # page annotations while replacing its population and inputs.
                    for key in ('link_prefix', 'data_link'):
                        if key in supplemental[name]:
                            extra[name][key] = copy.deepcopy(supplemental[name][key])
    return extra


def prepare_edition_publication(files, root, current_data):
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
