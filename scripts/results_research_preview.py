"""Add a local, unranked assessment edition to the existing shared homepage."""
import copy
import hashlib
import json
from pathlib import Path
import re
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from scripts.preview_open_research_v130 import ABILITY_FIELD, baseline_projection
from scripts.results_publication import atomic_write, data_literal
from scripts.results_research_baseline import (CURRENT_PATH, baseline_homepage,
    retain_publication_sources, select_baseline)
from math_gauge import independent_research_item_weights as item_weights
from math_gauge import independent_research_external as external
from math_gauge import independent_research_native as native
from math_gauge import independent_research_score_modes as modes
from math_gauge import independent_research_strict_credit as credit
from math_gauge import independent_research_value as value_revision
from math_gauge import legacy_taste_strict
from math_gauge import research_initiative
from math_gauge.research_profile import POLICY_PATH as PROFILE_POLICY_PATH, VALUE_POLICY_PATH

EDITION = '1.3.0'
BASE = '1.2.0'
CONFIG = re.compile(r'(<script type="application/json" id="edition-config">)([\s\S]*?)(</script>)')
CATEGORY_TEMPLATE = re.compile(r'<template id="independent-research-category-template">[\s\S]*?</template>\n?')


def _controller_match(name):
    return re.compile(r'(?:^|/)'+re.escape(name)+r'(?:\.[a-f0-9]+)?\.js$')


def _versioned_asset(result, root, name):
    text = (root/'scripts/templates'/name).read_text()
    stem, suffix = name.rsplit('.', 1)
    path = 'assets/versioned/'+stem+'.'+hashlib.sha256(text.encode()).hexdigest()[:12]+'.'+suffix
    result[path] = text
    return path


def _independent_category(data, group):
    from scripts.render_results_site import selected_result
    from scripts.results_rankings import category_rankings

    models = {model['id']: model for model in data['models']}

    def item(model, mode):
        return selected_result(model, mode)['metrics'][modes.ITEM]

    def exact_item(model, mode):
        metric = item(model, mode)
        # Known contributions still belong to the interval and overall score.
        # The category compares complete item values only.
        return {'metrics': {modes.ITEM: dict(metric, confirmed=metric['exact'])}}

    [board] = category_rankings(data['models'], [group], result_selector=exact_item)
    for mode, rows in board['views'].items():
        for row in rows:
            row['state'] = item(models[row['model_id']], mode)['state']
    return board


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
    from math_gauge.independent_research_adoption import PUBLIC_PATH
    adopted_path, overlay_path = root / PUBLIC_PATH, root / modes.PUBLIC_PATH
    legacy_taste_path = root / legacy_taste_strict.PUBLIC_PATH
    value_policy_path, value_path = root / value_revision.POLICY_PATH, root / value_revision.PUBLIC_PATH
    strict_policy_path, strict_path = root / credit.PATH, root / credit.PUBLIC_PATH
    item_weight_policy_path = root / item_weights.POLICY_PATH
    revised = value_policy_path.is_file()
    construct = 'independent-research-value-v0.2.0' if revised else 'independent-research-score-modes-v1.3.0'
    if strict_policy_path.is_file():
        construct = 'independent-research-strict-credit-v0.1.0'
    if item_weight_policy_path.is_file():
        construct = f'independent-research-item-weights-v{item_weights.VERSION}'
    adopted_bytes = adopted_path.read_bytes() if adopted_path.is_file() else None
    overlay_bytes = overlay_path.read_bytes() if overlay_path.is_file() else None
    adopted = json.loads(adopted_bytes) if adopted_bytes is not None else None
    baseline = select_baseline(files, root, adopted)
    envelope = baseline_homepage(original, baseline, root)
    envelope['edition'] = EDITION
    envelope['data']['benchmark_version'] = EDITION
    external_path = root / external.PUBLIC_PATH
    external_bytes = external_path.read_bytes() if external_path.is_file() else None
    external_index = external.load_public(root) if external_bytes is not None else None
    native_path = root / native.PUBLIC_PATH
    native_bytes = native_path.read_bytes() if native_path.is_file() else None
    native_index = native.load_public(root) if native_bytes is not None else None
    board, abilities, category_points = baseline_projection(baseline.data,
        policy_path=policy, profile_policy_path=root/(VALUE_POLICY_PATH if revised else PROFILE_POLICY_PATH),
        score_modes_policy_path=root/modes.POLICY_PATH,
        source_bytes=baseline.raw.encode(), adopted=adopted, adopted_bytes=adopted_bytes,
        overlay_bytes=overlay_bytes, legacy_taste_strict_policy_path=root/legacy_taste_strict.POLICY_PATH,
        legacy_taste_strict_bytes=legacy_taste_path.read_bytes() if legacy_taste_path.is_file() else None,
        value_policy_path=value_policy_path if revised else None,
        value_bytes=value_path.read_bytes() if value_path.is_file() else None,
        strict_credit_policy_path=strict_policy_path if strict_policy_path.is_file() else None,
        strict_credit_bytes=strict_path.read_bytes() if strict_path.is_file() else None,
        item_weight_policy_path=item_weight_policy_path if item_weight_policy_path.is_file() else None,
        external_bytes=external_bytes, native_bytes=native_bytes)
    source_models={m['id']:m for m in baseline.data['models']}
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
        if adopted and row['id'] in adopted['models']:
            normal += adopted['models'][row['id']]['normal_rounds']
        elif external_index and row['id'] in external_index['models']:
            normal += external_index['models'][row['id']]['normal_rounds']
        elif native_index and row['id'] in native_index['models']:
            normal += native_index['models'][row['id']]['normal_rounds']
        else:
            unknown += 3
        row['delivery']=dict(planned=45,normal=normal,unknown=unknown)
    envelope['data']['research_preview'] = board
    envelope['data'][ABILITY_FIELD] = abilities
    initiative = research_initiative.load_public(root, benchmark_version=EDITION)
    if initiative is not None:
        envelope['data']['research_initiative'] = initiative
    # Project new composite metrics from shared scoring, retaining all old payloads.
    from math_gauge.scoring import research_preview_contributions
    weights = board['weight_frame']
    policy_data = dict(legacy_group_weights={key: weights[key] / 100 for key in modes.BASE_GROUPS})
    source_policy=baseline.data['policy']
    from scripts.results_rankings import set_published_scores
    from scripts.results_editions import chart_scenes
    envelope['data']['edition_paths'] = {'download_prefix':'versions/1.3.0/'}
    by_id = {row['id']: row for row in board['rows']}
    for model in envelope['data']['models']:
        identifier = model['id']
        row = by_id[identifier]
        model_abilities = abilities['by_model'][identifier]
        download_abilities = dict(abilities, by_model={identifier: model_abilities})
        # Attach the official SMC coverage before writing any score-mode download.
        for mode, key in [('strict','SMC'),('partial','RMC'),('capability','MC')]:
            report = model['retry']['combined'] if mode == 'partial' else model[mode]['nonlogical_retry_3']
            value, known = row['composites'][key], row['confirmed'][key]
            item = row['score_modes'][key]['item']
            source = copy.deepcopy(report['metrics']['earned'])
            source_model = source_models[model['id']]
            source_report = source_model['retry']['combined'] if mode == 'partial' else source_model[mode]['nonlogical_retry_3']
            known_categories = sum(source_report['metrics'][g]['exact'] is not None for g in modes.BASE_GROUPS)
            known_categories += int(item['exact'] is not None)
            report['contributions']=research_preview_contributions(report.get('contributions',{}),source_policy,policy_data)
            item_coverage = dict(unit='three_round_research_task', planned=1,
                                 adjudicated=int(item['exact'] is not None), unknown=int(item['exact'] is None))
            report['metrics'][modes.ITEM] = dict(item, complete=item['exact'] is not None, coverage=item_coverage)
            for group, points in category_points[identifier][key].items():
                metadata = report['contributions'].get(group, {})
                if group == modes.ITEM:
                    metadata = dict(complete=item['exact'] is not None, coverage=item_coverage)
                report['contributions'][group] = dict(metadata, **points)
            report['metrics']['earned'] = dict(source, **value, confirmed=known, complete=value['exact'] is not None,
                coverage=dict(unit='fixed_weighted_category',planned=4,adjudicated=known_categories,unknown=4-known_categories))
            report['metrics']['overall'] = dict(value, complete=value['exact'] is not None,
                coverage=copy.deepcopy(report['metrics']['earned']['coverage']))
            if mode == 'strict':
                model_abilities['completion_v130']['coverage'] = copy.deepcopy(report['metrics']['overall']['coverage'])
            report['score_construct'] = construct
            report['base_edition'] = BASE
            suffix = {'partial':'','capability':'-capability','strict':'-strict'}[mode]
            download = dict(schema='math-gauge.independent-research-composite-display/v1',edition=EDITION,
                base_edition=BASE,model_id=model['id'],score_construct='composite-'+mode,
                metric=copy.deepcopy(report['metrics']['earned']),
                group_weights=weights, category_points=copy.deepcopy(category_points[identifier][key]),
                independent_research=copy.deepcopy(row),source_binding=copy.deepcopy(board['source_binding']),
                candidate_calls=0,rank_eligible=False)
            download[ABILITY_FIELD] = download_abilities
            if initiative is not None:
                download['research_initiative'] = dict(initiative,
                    models=[entry for entry in initiative['models'] if entry['id'] == identifier])
            if adopted:
                download['adoption_binding'] = copy.deepcopy(board['adoption'])
            if 'score_modes_binding' in board:
                download['score_modes_binding'] = copy.deepcopy(board['score_modes_binding'])
            if revised:
                download['value_binding'] = copy.deepcopy(board['value_binding'])
                download['item_weights'] = copy.deepcopy(board['item_weights'])
            if 'strict_credit_binding' in board:
                download['strict_credit_binding'] = copy.deepcopy(board['strict_credit_binding'])
            if 'item_weight_binding' in board:
                download['item_weight_binding'] = copy.deepcopy(board['item_weight_binding'])
            if 'external_binding' in board:
                download['external_binding'] = copy.deepcopy(board['external_binding'])
            if 'native_binding' in board:
                download['native_binding'] = copy.deepcopy(board['native_binding'])
            result['versions/1.3.0/downloads/'+model['id']+'-combined'+suffix+'-retry.json']=json.dumps(download,ensure_ascii=False,indent=2)+'\n'
        set_published_scores(model)
        if adopted or revised:
            comparable = all(v['exact'] is not None for v in row['composites'].values())
            model['ranking_complete'] = comparable
            if not comparable:
                model['ranking_values'] = dict.fromkeys(('strict', 'partial', 'capability'))
    data = envelope['data']
    for group in data['category_leaderboards']:
        group['weight'] = weights[group['id']]
        if group['id'] == 'research': group['title'] = '辅助研究'
    for mode in data.get('display_score_modes', []):
        mode['name'] = '1.3 '+mode['abbreviation']
    for group in data['policy']['groups']:
        old=group['weight'];group['weight']=weights[group['id']]
        if group['id']=='research':group['title']='辅助研究'
        for leaf in data['policy']['subcategories']:
            if leaf['id'] in group['children']:leaf['weight']=leaf['weight']*group['weight']/old
    item_group = dict(id=modes.ITEM, title=board['category']['zh'], weight=weights[modes.ITEM], children=[])
    item_board = _independent_category(data, item_group)
    data['policy']['groups'].append(item_group)
    data['category_leaderboards'].append(item_board)
    scene_source = copy.deepcopy(baseline.data)
    scene_source.update(models=data['models'], category_leaderboards=[item_board])
    scenes = chart_scenes(scene_source)
    item_chart = 'category-chart-groups-'+modes.ITEM
    for mode, rows in item_board['views'].items():
        for row in rows:
            scenes[item_chart]['bars'][row['model_id']][mode]['state'] = row['state']
    for key in ('chart-groups', item_chart):
        data['chart_scenes'][key] = scenes[key]
    envelope['data']['score_construct'] = construct
    envelope['data']['research_preview']['base_edition'] = BASE
    envelope['data']['research_preview']['condition'] = 'nonlogical_retry_3'
    supplemental = envelope.get('supplemental', {})
    if supplemental.get('cost-reference-data') is not None:
        from scripts.cost_reference import independent_research_reference
        supplemental['cost-reference-data'] = independent_research_reference(
            root, data, supplemental['cost-reference-data'], adoption=adopted, external_adoption=external_index,
            native_adoption=native_index)
        if baseline.retained:
            result['versions/1.3.0/downloads/cost-reference.json'] = json.dumps(
                supplemental['cost-reference-data'], ensure_ascii=False, indent=2)+'\n'
        if native_index:
            result['versions/1.3.0/downloads/native-results.json'] = native_path.read_text()
        native_resource_path = root / 'protocol/mathematical-taste/v1.3.0/native-resources.json'
        if native_resource_path.is_file():
            result['versions/1.3.0/downloads/native-resources.json'] = native_resource_path.read_text()
        resource_path = root / 'protocol/mathematical-taste/v1.3.0/independent-research-resources.json'
        if resource_path.is_file():
            result['versions/1.3.0/downloads/independent-research-resources.json'] = resource_path.read_text()
        external_resource_path = root / 'protocol/mathematical-taste/v1.3.0/external-resources.json'
        if external_resource_path.is_file():
            result['versions/1.3.0/downloads/external-resources.json'] = external_resource_path.read_text()
    if baseline.retained and supplemental.get('timing-reference-data') is not None:
        timing = supplemental['timing-reference-data']
        timing['data_link'] = 'versions/1.3.0/downloads/timing-reference.json'
        result[timing['data_link']] = json.dumps(timing, ensure_ascii=False, indent=2)+'\n'
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
    if 'id="category-leaderboards"' in page:
        from scripts.render_results_site import render_category_board
        tab, panel = render_category_board(data, item_board, subcategories=False)
        shell = '<template id="independent-research-category-template">'+tab+panel+'</template>\n'
        page = CATEGORY_TEMPLATE.sub('', page).replace('</main>', shell+'</main>', 1)
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
    for name in ('results-core', 'board-controls', 'home-results', 'mathematical-profile', 'cost-reference'):
        match_controller = _controller_match(name).search
        if any(match_controller(path) for path in config['scripts']):
            path = _versioned_asset(result, root, name+'.js')
            config['scripts'] = [path if match_controller(script) else script for script in config['scripts']]
    profile_style = re.compile(r'(?<=href=")assets/versioned/mathematical-profile\.[a-f0-9]+\.css(?=")')
    if profile_style.search(page):
        page = profile_style.sub(_versioned_asset(result, root, 'mathematical-profile.css'), page)
    config['latest'] = EDITION
    scripts = [path for path in config['scripts'] if not _controller_match('research-preview').search(path)]
    # The shared board controllers discover their controls on startup.
    insertion = next((i for i, path in enumerate(scripts) if _controller_match('board-controls').search(path)), len(scripts))
    scripts.insert(insertion, assets['js'])
    config['scripts'] = scripts
    page = CONFIG.sub(lambda m:m[1]+data_literal(config)+m[3],page)
    page = re.sub(r'\s*<link rel="stylesheet" href="assets/versioned/research-preview\.[a-f0-9]+\.css">\s*(?=</head>)','',page)
    page = page.replace('</head>','<link rel="stylesheet" href="'+assets['css']+'">\n</head>',1)
    result['index.html'] = page
    catalog = json.loads(result['editions.json'])
    catalog['latest'] = EDITION
    edition_kind = 'local_settled_configurations' if adopted else 'local_unmeasured_preview'
    catalog['editions'] = [dict(version=EDITION,kind=edition_kind,data='data/editions/1.3.0/index.json'),
        *[v for v in catalog['editions'] if v['version'] != EDITION]]
    result['editions.json'] = json.dumps(catalog,ensure_ascii=False,indent=2)+'\n'
    retain_publication_sources(result, baseline)
    return result


def install_local(root):
    """Update only the new resources, original index and edition catalog; no full rebuild."""
    root = Path(root)
    site = root/'site'
    names = ['index.html','editions.json','data.json','data/editions/1.2.0/index.json']
    if (site / CURRENT_PATH).is_file():
        names.append(CURRENT_PATH)
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
