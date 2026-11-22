"""Add a local, unranked assessment edition to the existing shared homepage."""
import copy
import hashlib
import json
from pathlib import Path
import re
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from scripts.preview_open_research_v130 import baseline_data
from scripts.results_publication import atomic_write, data_literal

EDITION = '1.3.0'
BASE = '1.2.0'
CONFIG = re.compile(r'(<script type="application/json" id="edition-config">)([\s\S]*?)(</script>)')


def prepare_research_preview(files, root):
    root = Path(root)
    policy = root/'protocol/mathematical-taste/v1.3.0/policy.json'
    target = 'data/editions/1.2.0/index.json'
    if not policy.is_file() or target not in files or 'index.html' not in files or 'data.json' not in files:
        return files
    result = dict(files)
    original = json.loads(files[target])
    if original['edition'] != BASE or original['page'] != 'index.html':
        raise ValueError('Preview requires an authenticated existing homepage edition')
    envelope = copy.deepcopy(original)
    envelope['edition'] = EDITION
    envelope['data']['benchmark_version'] = EDITION
    board = baseline_data(json.loads(files['data.json']), policy_path=policy)
    source_models={m['id']:m for m in json.loads(files['data.json'])['models']}
    for row in board['rows']:
        model=source_models[row['id']]
        normal=model.get('answer_delivery',{}).get('active_final')
        unknown=0 if normal is not None else 39
        normal=normal or 0
        rounds={r['round']:r for r in model.get('alignment_selfcheck',{}).get('rounds',[])}
        for n in (1,2,3):
            record=rounds.get(n,{})
            flag=record.get('active_final')
            if flag is True or record.get('submission_classification')=='active_final':normal+=1
            elif flag is False or record.get('delivery_verified') is False:pass
            else:unknown+=1
        row['delivery']=dict(planned=45,normal=normal,unknown=unknown)
    envelope['data']['research_preview'] = board
    # Project new composite metrics from shared scoring, retaining all old payloads.
    from math_gauge.scoring import research_preview_contributions
    policy_data=json.loads(policy.read_bytes())
    source_policy=json.loads(files['data.json'])['policy']
    from scripts.results_rankings import set_published_scores
    from scripts.results_editions import chart_scenes
    envelope['data']['edition_paths'] = {'download_prefix':'versions/1.3.0/'}
    by_id = {row['id']: row for row in board['rows']}
    for model in envelope['data']['models']:
        row = by_id[model['id']]
        for mode, key in [('partial','RMC'),('capability','MC'),('strict','SMC')]:
            report = model['retry']['combined'] if mode == 'partial' else model[mode]['nonlogical_retry_3']
            value = row['strict_overall'] if mode == 'strict' else row['composites'][key]
            known = row['strict_confirmed'] if mode == 'strict' else row['confirmed'][key]
            source = copy.deepcopy(report['metrics']['earned'])
            report['contributions']=research_preview_contributions(report.get('contributions',{}),source_policy,policy_data)
            report['metrics']['earned'] = dict(source, **value, confirmed=known, complete=value['exact'] is not None,
                coverage=dict(unit='fixed_weighted_category',planned=4,adjudicated=3+int(value['exact'] is not None),unknown=int(value['exact'] is None)))
            report['metrics']['overall'] = dict(value, complete=value['exact'] is not None,
                coverage=copy.deepcopy(report['metrics']['earned']['coverage']))
            report['score_construct'] = 'independent-research-composite-v1.3.0-not-legacy-mode'
            report['base_edition'] = BASE
            suffix = {'partial':'','capability':'-capability','strict':'-strict'}[mode]
            download = dict(schema='math-gauge.independent-research-composite-display/v1',edition=EDITION,
                base_edition=BASE,model_id=model['id'],score_construct='composite-'+mode,
                metric=copy.deepcopy(report['metrics']['earned']),
                group_weights=dict(written=30,lean=30,research=30,independent_open_research=10),
                independent_research=copy.deepcopy(row),source_binding=copy.deepcopy(board['source_binding']),
                candidate_calls=0,rank_eligible=False)
            result['versions/1.3.0/downloads/'+model['id']+'-combined'+suffix+'-retry.json']=json.dumps(download,ensure_ascii=False,indent=2)+'\n'
        set_published_scores(model)
    scene_source = json.loads(files['data.json'])
    scene_source['models'] = envelope['data']['models']
    envelope['data']['chart_scenes']['chart-groups'] = chart_scenes(scene_source)['chart-groups']
    for group in envelope['data'].get('category_leaderboards', []):
        group['weight'] = 30
        if group['id'] == 'research': group['title'] = '辅助研究'
    for mode in envelope['data'].get('display_score_modes', []):
        original = mode['abbreviation']
        mode['abbreviation'] = original+('基准综合' if mode['id']=='capability' else '综合')
        mode['name'] = '1.3 '+mode['abbreviation']
    for group in envelope['data']['policy']['groups']:
        old=group['weight'];group['weight']=30
        if group['id']=='research':group['title']='辅助研究'
        for leaf in envelope['data']['policy']['subcategories']:
            if leaf['id'] in group['children']:leaf['weight']=leaf['weight']*30/old
    envelope['data']['score_construct'] = 'explicit-composite-30/30/30/10'
    envelope['data']['research_preview']['weight_frame'] = dict(written=30, lean=30, research=30, independent_open_research=10)
    envelope['data']['research_preview']['base_edition'] = BASE
    envelope['data']['research_preview']['condition'] = 'nonlogical_retry_3'
    result['versions/1.3.0/data.json']=json.dumps(envelope['data'],ensure_ascii=False,indent=2)+'\n'
    literal = data_literal(envelope)
    digest = hashlib.sha256(literal.encode()).hexdigest()
    payload = 'assets/data/'+digest+'.js'
    result['data/editions/1.3.0/index.json'] = literal+'\n'
    result[payload] = 'window.MGEditionData('+data_literal(digest)+','+literal+');\n'
    assets = {}
    for suffix in ('js','css'):
        name = 'research-preview.'+suffix
        text = (root/'scripts/templates'/name).read_text()
        path = 'assets/versioned/research-preview.'+hashlib.sha256(text.encode()).hexdigest()[:12]+'.'+suffix
        result['assets/'+name] = text
        result[path] = text
        assets[suffix] = path
    notes=(root/'scripts/templates/edition-notes.js').read_text()
    notes_path='assets/versioned/edition-notes.'+hashlib.sha256(notes.encode()).hexdigest()[:12]+'.js'
    result[notes_path]=notes;result['assets/edition-notes.js']=notes
    page = str(result['index.html'])
    match = CONFIG.search(page)
    if match is None:
        raise ValueError('Keep the existing edition loader and homepage')
    config = json.loads(match[2])
    config['versions'] = {EDITION: dict(key=digest, payload=payload,
        label=dict(zh=EDITION, en=EDITION), status=dict(zh='', en='')),
        **{k:v for k,v in config['versions'].items() if k != EDITION}}
    config['versions'] = dict(sorted(config['versions'].items(), key=lambda pair: tuple(map(int,pair[0].split('.'))), reverse=True))
    # Keep all historical payloads/controllers intact; the local latest entry is 1.3.
    config['scripts']=[notes_path if re.search(r'edition-notes\.[a-f0-9]+\.js$',p) else p for p in config['scripts']]
    config['latest'] = EDITION
    config['scripts'] = [p for p in config['scripts'] if not re.search(r'research-preview\.[a-f0-9]+\.js$',p)] + [assets['js']]
    page = CONFIG.sub(lambda m:m[1]+data_literal(config)+m[3],page)
    page = re.sub(r'\s*<link rel="stylesheet" href="assets/versioned/research-preview\.[a-f0-9]+\.css">\s*(?=</head>)','',page)
    page = page.replace('</head>','<link rel="stylesheet" href="'+assets['css']+'">\n</head>',1)
    result['index.html'] = page
    catalog = json.loads(result['editions.json'])
    catalog['latest'] = EDITION
    catalog['editions'] = [dict(version=EDITION,kind='local_unmeasured_preview',data='data/editions/1.3.0/index.json'),
        *[v for v in catalog['editions'] if v['version'] != EDITION]]
    result['editions.json'] = json.dumps(catalog,ensure_ascii=False,indent=2)+'\n'
    return result


def install_local(root):
    """Update only the new resources, original index and edition catalog; no full rebuild."""
    root = Path(root)
    site = root/'site'
    names = ('index.html','editions.json','data.json','data/editions/1.2.0/index.json')
    original = {name:(site/name).read_text() for name in names}
    prepared = prepare_research_preview(original,root)
    for name, text in prepared.items():
        if name not in original or text != original[name]:
            atomic_write(site/name,text)
    manifest = site/'generated-pages.json'
    owned = set(json.loads(manifest.read_text()))
    owned.update(prepared)
    atomic_write(manifest,json.dumps(sorted(owned),indent=2)+'\n')
    return {'edition':EDITION,'entry':'index.html?edition=1.3.0','candidate_calls':0,
            'historical_payloads_changed':False,'local_default_changed':True,'remote_published':False}


if __name__ == '__main__':
    print(json.dumps(install_local(Path(__file__).resolve().parents[1]),ensure_ascii=False))
