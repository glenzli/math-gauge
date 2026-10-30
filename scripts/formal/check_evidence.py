#!/usr/bin/env python3
"""Verify retained author evidence offline, without Git, Lean or model calls.

Retained compiler reports bind checked-manifest.json through metadata-only
relocation receipts. Explicitly recompiled cases instead bind the current
manifest, fresh compiler output and a current independent semantic review.
The checked ledger remains immutable provenance, not current proof evidence.
"""
from __future__ import annotations

import argparse
from copy import deepcopy
from datetime import datetime
import hashlib
import json
from pathlib import Path
import re
import sys

try:
    from . import verify
except ImportError:  # Direct script invocation.
    import verify

BINDING_SCHEMA = 'math-gauge.formal-input-binding/v1'
LAYOUT_SCHEMA = 'math-gauge.layout/v1'
REQUIRED_EVALUATOR_FILES = {
    'formal/COVERAGE.md', 'formal/alignment.json',
    'formal/manifest.json', 'formal/input-binding.json',
}
HASH_FIELDS = ('files', 'source_hashes', 'artifacts', 'reviewed_sha256')


def relative_name(name):
    verify.require(isinstance(name, str) and bool(name), 'Evidence path must be text')
    path = Path(name)
    verify.require(not path.is_absolute() and '..' not in path.parts and
                   path.as_posix() == name, 'Unsafe evidence path: ' + name)
    return name


def load_layout(repo):
    layout = verify.load(verify.safe_relative(repo, 'verification/layout.json'))
    verify.require(layout.get('schema') == LAYOUT_SCHEMA, 'Invalid verification layout')
    verify.require(bool(re.fullmatch(r'[0-9a-f]{40}', layout.get('baseline_commit', ''))),
                   'Layout must name its original Git baseline')
    rows = layout.get('case_paths', [])
    verify.require(isinstance(rows, list) and bool(rows), 'Layout needs explicit case paths')
    ids = [row['id'] for row in rows]
    verify.require(len(ids) == len(set(ids)), 'Duplicate layout case id')
    for row in rows:
        relative_name(row['previous']); relative_name(row['current'])
        verify.require(Path(row['previous']).name == Path(row['current']).name == row['id'],
                       'Layout paths must preserve case identity')
        verify.require(bool(re.fullmatch(r'cases/(?:proofs|lean-audit|lean-construction|chapters)/' +
                                       re.escape(row['id']), row['current'])),
                       'Unexpected canonical case path')
    for field in ('previous', 'current'):
        verify.require(len({row[field] for row in rows}) == len(rows), 'Duplicate layout case path')
    prefixes = layout.get('path_prefixes', [])
    verify.require(isinstance(prefixes, list), 'Invalid layout prefix map')
    for row in prefixes:
        relative_name(row['previous']); relative_name(row['current'])
    return layout


def translate_path(name, layout):
    """Translate only an explicitly recorded repository path prefix."""
    relative_name(name)
    mappings = layout['case_paths'] + layout.get('path_prefixes', [])
    matches = [row for row in mappings
               if name == row['previous'] or name.startswith(row['previous'] + '/')]
    verify.require(bool(matches), 'Unmapped retained evidence path: ' + name)
    row = max(matches, key=lambda item: len(item['previous']))
    return row['current'] + name[len(row['previous']):]


def canonical_formalization(alignment):
    count = sum(item['status'] == 'complete' for item in alignment['items'])
    return {'status': 'complete' if count == len(alignment['items']) else 'partial',
            'complete_obligations': count, 'total_obligations': len(alignment['items']),
            'evidence': 'formal/manifest.json'}


def check_metadata_relocation(case_root, checked, current, alignment):
    """Reject all metadata edits except the explicit, derived migration rules."""
    expected = deepcopy(checked)
    verify.require(checked.get('path_base') in (None, 'suite'),
                   'Checked case must use the original suite path base')
    expected['path_base'] = 'case'
    prefix = checked['id'] + '/'

    def reroute(name):
        verify.require(isinstance(name, str) and name.startswith(prefix),
                       'Original author input must be case-owned')
        return relative_name(name[len(prefix):])

    for key in ('task', 'reference', 'rubric', 'group_contract'):
        expected[key] = reroute(checked[key])
    expected['solver_files'] = deepcopy(checked.get('solver_files', []))
    for row in expected['solver_files']:
        row['source'] = reroute(row['source'])

    evaluator = current.get('evaluator_files', [])
    verify.require(isinstance(evaluator, list) and all(isinstance(x, str) for x in evaluator)
                   and len(evaluator) == len(set(evaluator)), 'Invalid relocated evaluator files')
    retained = {reroute(name) for name in checked.get('evaluator_files', [])
                if name.startswith(prefix)}
    verify.require(REQUIRED_EVALUATOR_FILES <= set(evaluator) <= retained | REQUIRED_EVALUATOR_FILES,
                   'Evaluator relocation may retain case-owned files and add only current formal evidence')
    for name in evaluator:
        relative_name(name)
        # The receipt lists itself and is checked after it is written.
        if name != 'formal/input-binding.json':
            verify.safe_relative(case_root, name)
    expected['evaluator_files'] = evaluator
    expected.setdefault('review', {})['formalization'] = canonical_formalization(alignment)
    verify.require(current == expected,
                   'Case metadata changed outside allowed layout/formalization fields')
    return {
        'path_base': {'from': checked.get('path_base'), 'to': 'case'},
        'evaluator_files': {'from': checked.get('evaluator_files', []), 'to': evaluator},
        'formalization': {'from': checked.get('review', {}).get('formalization'),
                          'to': canonical_formalization(alignment)},
    }


def checked_ledger(repo, layout):
    ledger_path = verify.safe_relative(repo, 'verification/author/checked-ledger.json')
    expected = layout.get('migration', {}).get('checked_ledger_sha256')
    verify.require(isinstance(expected, str) and
                   bool(re.fullmatch(r'[0-9a-f]{64}', expected)) and
                   verify.digest(ledger_path) == expected,
                   'Checked ledger differs from the recorded migration identity')
    ledger = verify.load(ledger_path)
    verify.require(ledger.get('schema') == 'math-gauge.author-evidence-ledger/v1',
                   'Invalid checked author ledger')
    return ledger


def original_row(repo, layout, cid):
    ledger = checked_ledger(repo, layout)
    matches = [row for row in ledger['cases'] if row['id'] == cid]
    verify.require(len(matches) == 1, 'Checked ledger must contain the case exactly once')
    mapping = next(row for row in layout['case_paths'] if row['id'] == cid)
    verify.require(matches[0]['case_path'] == mapping['previous'],
                   'Checked ledger and layout baseline paths differ')
    return matches[0]


def expected_binding(repo, layout, mapping, baseline_row):
    """Construct a receipt only after checking the two immutable snapshots."""
    case_root = repo / mapping['current']; formal = case_root / 'formal'
    checked_path = verify.safe_relative(formal, 'checked-manifest.json')
    checked_case_path = verify.safe_relative(formal, 'checked-case.json')
    manifest_path = verify.safe_relative(formal, 'manifest.json')
    case_path = verify.safe_relative(case_root, 'case.json')
    checked = verify.load(checked_path); old_case = verify.load(checked_case_path)
    current, _, *_ = verify.validate_case(manifest_path)
    alignment = verify.load(formal / 'alignment.json')
    verify.require(verify.digest(checked_path) == baseline_row['manifest_sha256'],
                   'Checked manifest differs from the original evidence ledger')
    verify.require(verify.digest(checked_case_path) == checked['frozen_inputs']['case.json'],
                   'Checked case differs from the originally compiled input')
    verify.require(checked['case_id'] == old_case['id'] == mapping['id'] == current['case_id']
                   and checked['case_version'] == old_case['version'] == current['case_version']
                   == baseline_row['case_version'], 'Evidence case identity or version changed')
    changed = deepcopy(checked)
    changed['frozen_inputs']['case.json'] = verify.digest(case_path)
    verify.require(current == changed,
                   'Only the current case.json hash may change in the formal manifest')
    allowed = check_metadata_relocation(case_root, old_case, verify.load(case_path), alignment)
    for name, expected in checked['frozen_inputs'].items():
        target = checked_case_path if name == 'case.json' else verify.safe_relative(case_root, name)
        verify.require(verify.digest(target) == expected, 'Original mathematical input changed: ' + name)

    def identity(path, name):
        return {'path': name, 'sha256': verify.digest(path)}

    for filename, field in (('verification-report.json', 'verification_report_sha256'),
                            ('declarations.json', 'declarations_sha256')):
        verify.require(verify.digest(verify.safe_relative(formal, filename)) == baseline_row[field],
                       'Original compiler evidence changed: ' + filename)
    return {
        'schema': BINDING_SCHEMA, 'kind': 'metadata-only-layout-migration',
        'case_id': current['case_id'], 'case_version': current['case_version'],
        'baseline_commit': layout['baseline_commit'],
        'previous_case_path': mapping['previous'], 'current_case_path': mapping['current'],
        'checked_case': identity(checked_case_path, 'checked-case.json'),
        'checked_manifest': identity(checked_path, 'checked-manifest.json'),
        'current_case': identity(case_path, '../case.json'),
        'current_manifest': identity(manifest_path, 'manifest.json'),
        'verification_report': identity(formal / 'verification-report.json', 'verification-report.json'),
        'declarations': identity(formal / 'declarations.json', 'declarations.json'),
        'allowed_changes': allowed,
    }


def check_external_source_closure(report, config):
    """Validate saved closure identity without requiring the original cache machine."""
    closure = report.get('external_source_closure')
    verify.require(isinstance(closure, dict), 'Motivic report is missing external source closure')
    rows = closure.get('modules')
    verify.require(isinstance(rows, list) and bool(rows) and all(isinstance(row, dict) for row in rows),
                   'Invalid external source closure module rows')
    names = [row.get('module') for row in rows]
    verify.require(all(isinstance(name, str) and verify.MODULE_RE.fullmatch(name) for name in names)
                   and names == sorted(set(names))
                   and type(closure.get('module_count')) is int and closure['module_count'] == len(rows),
                   'External source closure count or module identity differs')
    encoded = json.dumps(rows, sort_keys=True, separators=(',', ':')).encode('utf-8')
    verify.require(closure.get('sha256') == hashlib.sha256(encoded).hexdigest(),
                   'External source closure digest differs from its module rows')
    known = set(names)
    direct = report.get('direct_external_imports')
    verify.require(isinstance(direct, list) and bool(direct)
                   and all(isinstance(row, dict) and row.get('module') in known for row in direct),
                   'External source closure omits a direct compiled import')
    for row in rows:
        verify.require(isinstance(row.get('sha256'), str)
                       and re.fullmatch(r'[0-9a-f]{64}', row['sha256']) is not None,
                       'Invalid external compiled module digest')
        if row.get('package') == 'lean-standard-library':
            continue
        verify.require(row.get('package') in config['packages']
                       and row.get('revision') == config['packages'][row['package']],
                       'External source closure package revision differs')
        verify.require(isinstance(row.get('source_git_blob'), str)
                       and re.fullmatch(r'[0-9a-f]{40}', row['source_git_blob']) is not None
                       and isinstance(row.get('source_sha256'), str)
                       and re.fullmatch(r'[0-9a-f]{64}', row['source_sha256']) is not None,
                       'External source closure lacks fixed source identity')
        imports = row.get('imports')
        verify.require(isinstance(imports, list) and all(isinstance(name, str) and name in known for name in imports),
                       'External source closure omits a transitive import')
        parts = row.get('compiled_parts')
        verify.require(isinstance(parts, dict) and parts.get('.olean') == row['sha256']
                       and all(isinstance(value, str) and re.fullmatch(r'[0-9a-f]{64}', value)
                               for value in parts.values()),
                       'External compiled parts differ from the module identity')
    by_name = {row['module']: row for row in rows}
    verify.require(all(row.get('sha256') == by_name[row['module']]['sha256'] for row in direct),
                   'Direct compiled import differs from the bound external closure')


def check_compiler_report(formal, current, checked, baseline_row, *,
                          manifest_name='checked-manifest.json'):
    """Check saved compiler output; do not access old machines or caches."""
    report = verify.load(verify.safe_relative(formal, 'verification-report.json'))
    verify.require(report.get('schema') == 'math-gauge.formal-verification/v1'
                   and report.get('case_id') == checked['case_id'] and report.get('status') == 'passed',
                   'Original compiler report did not pass for this case')
    verify.require(report['manifest_sha256'] == verify.digest(formal / manifest_name),
                   'Compiler report is not bound to the compiled manifest')
    for field in ('frozen_inputs', 'alignment', 'coverage'):
        verify.require(report.get(field) == checked.get(field),
                       'Original compiler report binding differs: ' + field)
    verify.require(report.get('fresh_output') is True and
                   report.get('source_side_oleans_reused') is False and
                   report.get('sibling_case_outputs_used') is False,
                   'Original compiler report must record fresh isolated compilation')
    verify.require(report.get('semantic_alignment_inferred') is False and
                   report.get('local_declaration_audit_scope') == 'all-explicit-case-modules',
                   'Compiler report does not record the complete local declaration audit')
    if baseline_row is not None:
        verify.require(report.get('started_utc') == baseline_row['compile_started_utc'] and
                       report.get('finished_utc') == baseline_row['compile_finished_utc'],
                       'Original compile timestamps changed')
    profile = verify.manifest_profile(checked)
    dependency = report['dependency']; config = verify.profile_config(profile)
    verify.require(dependency.get('verification_profile', verify.DEFAULT_PROFILE) == profile
                   and dependency['mathlib_revision'] == config['mathlib_revision'],
                   'Original compiler dependency profile differs')
    verify.require(config['lean_version'] in dependency['lean_version'] and
                   dependency.get('ambient_lean_path_excluded') is True and
                   dependency.get('dependency_project_build_excluded') is True,
                   'Original compiler dependency isolation differs')
    for field in verify.PROFILE_REVISION_FIELDS:
        if field in config:
            verify.require(dependency.get(field) == config[field],
                           'Original ' + verify.REVISION_LABELS[field] + ' revision differs')

    if profile == verify.MOTIVIC_PROFILE:
        check_external_source_closure(report, config)

    audit = report['audit']; summary = audit['summary']
    verify.require(summary.get('passed') is True and summary.get('unexpected_axioms') == []
                   and set(summary['axiom_union']) <= verify.ALLOWED_AXIOMS
                   and set(audit.get('allowed_axioms', [])) == verify.ALLOWED_AXIOMS,
                   'Forbidden axiom or incomplete original kernel audit')
    declarations = verify.load(verify.safe_relative(formal, 'declarations.json'))
    verify.require(declarations == audit['declarations'] and bool(declarations)
                   and len(declarations) == summary['declaration_count']
                   and len({row['name'] for row in declarations}) == len(declarations),
                   'Saved declaration inventory differs from the original kernel audit')
    modules = {row['module'] for row in current['modules']}
    verify.require(all(row['module'] in modules and row['kind'] != 'axiom' for row in declarations),
                   'Foreign module or local axiom in the original declaration inventory')
    verify.require(len(report['modules']) == len(checked['modules']),
                   'Original compiler module inventory differs')
    for source, command in zip(checked['modules'] + [checked['audit']],
                               report['modules'] + [audit['command']]):
        verify.require(source['module'] == command['module'] and
                       source['sha256'] == command['source_sha256'] and command['exit_code'] == 0,
                       'Original compiled source differs: ' + source['module'])
        log = verify.safe_relative(formal, command['log'])
        verify.require(verify.digest(log) == command['log_sha256'],
                       'Saved compiler log changed: ' + source['module'])
        if source['module'] == 'CurrentAudit':
            text = log.read_text(encoding='utf-8')
            actual_declarations = [json.loads(x) for x in re.findall(r'MATH_GAUGE_DECL (\{[^\r\n]*\})', text)]
            actual_summaries = [json.loads(x) for x in re.findall(r'MATH_GAUGE_AUDIT_SUMMARY (\{[^\r\n]*\})', text)]
            verify.require(actual_declarations == declarations and actual_summaries == [summary],
                           'Original audit log and reported inventory/summary differ')
    names = {(row['module'], row['name']) for row in declarations}
    names.update((row['module'], row['user_name']) for row in declarations if 'user_name' in row)
    alignment = verify.load(formal / 'alignment.json')
    for item in alignment['items']:
        for declaration in item['declarations']:
            verify.require((declaration['module'], declaration['name']) in names,
                           'Mapped declaration missing from kernel inventory: ' + declaration['name'])
    return report, declarations, alignment


def reviewed_target(repo, layout, case_root, name):
    """Old metadata hashes resolve to retained checked copies, never current bytes."""
    repo = Path(repo).resolve(); case_root = Path(case_root).resolve()
    relative_name(name)
    if name.startswith(('drafts/', 'cases/', 'results/', 'verification/')):
        target = verify.safe_relative(repo, translate_path(name, layout))
    else:
        target = verify.safe_relative(case_root, name)
    if target == case_root / 'case.json':
        return verify.safe_relative(case_root, 'formal/checked-case.json')
    if target == case_root / 'formal/manifest.json':
        return verify.safe_relative(case_root, 'formal/checked-manifest.json')
    return target


def check_review(repo, layout, case_root, baseline_row):
    repo = Path(repo).resolve(); case_root = Path(case_root).resolve()
    original = baseline_row['independent_semantic_review']
    path = verify.safe_relative(repo, translate_path(original['path'], layout))
    verify.require(verify.digest(path) == original['sha256'], 'Original independent semantic review changed')
    cid = baseline_row['id']
    if path.suffix == '.md':
        text = path.read_text(encoding='utf-8')
        verify.require(cid == 'MG-GR101' and
                       'Final semantic result: all six stages aligned; no open' in text and
                       text.count('Revised identities:') == 1,
                       'Unrecognized retained Markdown semantic review')
        # These are explicitly superseded source identities from the follow-up.
        # The earlier task/reference identities were not superseded.
        before, after = text.split('Revised identities:')
        hashes = dict(re.findall(r'- ([^:\n]+): ([0-9a-f]{64})', before))
        hashes.update(dict(re.findall(r'- ([^:\n]+): ([0-9a-f]{64})', after)))
        recorded_count = len(dict(re.findall(r'- ([^:\n]+): ([0-9a-f]{64})', after)))
        reviewer = 'author-lean-chapters'; status = 'passed'
        items = [{'id': f'S{i}'} for i in range(1, 7)]
    else:
        review = verify.load(path)
        if 'cases' in review:
            matches = [row for row in review['cases'] if row['case_id'] == cid]
            verify.require(len(matches) == 1, 'Grouped independent review identity differs')
            data = matches[0]
        else:
            data = review
        verify.require(data['case_id'] == cid and
                       data.get('case_version', baseline_row['case_version']) == baseline_row['case_version'],
                       'Independent review case identity or version differs')
        hashes = next((data[key] for key in HASH_FIELDS if key in data), None)
        verify.require(isinstance(hashes, dict) and bool(hashes), 'Independent review lacks source hashes')
        recorded_count = len(hashes)
        reviewer = review['reviewer']; status = data.get('status', data.get('verdict'))
        items = data.get('items', data.get('stage_reviews', []))
        # Supplementary evidence is checked when the original review binds it.
        frontier = data.get('external_frontier_assessment')
        if frontier:
            target = verify.safe_relative(repo, translate_path(frontier['path'], layout))
            verify.require(verify.digest(target) == frontier['sha256'],
                           'Independent semantic frontier evidence changed')
    for name, expected in hashes.items():
        verify.require(verify.digest(reviewed_target(repo, layout, case_root, name)) == expected,
                       'Independent semantic review source hash is stale: ' + cid + '/' + name)
    verify.require(status in {'passed', 'pass', 'passed-no-open-findings', 'partial'},
                   'Independent semantic review did not pass or declare partial coverage')
    ids = [item['id'] for item in items]
    verify.require(len(ids) == len(set(ids)) and set(ids) == set(original['stage_ids']) and
                   reviewer == original['reviewer'] and status == original['status'] and
                   recorded_count == original['bound_files_rechecked'],
                   'Independent semantic review differs from the checked ledger')
    return {'path': path.relative_to(repo).as_posix(), 'sha256': verify.digest(path),
            'reviewer': reviewer, 'status': status, 'bound_files_rechecked': len(hashes),
            'stage_ids': ids}


def evidence_time(value):
    verify.require(isinstance(value, str), 'Evidence timestamp must be text')
    result = datetime.fromisoformat(value)
    verify.require(result.utcoffset() is not None, 'Evidence timestamp must include a timezone')
    return result


def check_recompiled_review(repo, case_root, manifest, alignment, report, review_name):
    """Check current source identities; do not infer semantics from compilation."""
    relative_name(review_name)
    path = verify.safe_relative(repo, review_name)
    review = verify.load(path)
    verify.require(review.get('schema') == 'math-gauge.author-semantic-review/v1' and
                   review.get('case_id') == manifest['case_id'] and
                   review.get('case_version') == manifest['case_version'],
                   'Current independent semantic review identity differs')
    verify.require(review.get('reviewer_kind') == 'independent-ai' and
                   all(isinstance(review.get(key), str) and review[key].strip()
                       for key in ('reviewer', 'author')) and
                   review['reviewer'] != review['author'] and
                   review.get('human') == 'pending' and
                   review.get('compile_is_semantic_proof') is False,
                   'Current review must distinguish independent AI, author, compilation and pending human review')
    verify.require(evidence_time(review.get('reviewed_at_utc')) >= evidence_time(report['finished_utc']),
                   'Current semantic review predates its bound compiler report')
    hashes = review.get('files')
    required = set(manifest['frozen_inputs']) | {
        'formal/manifest.json', 'formal/alignment.json', 'formal/COVERAGE.md',
        'formal/verification-report.json', 'formal/declarations.json',
        'formal/' + manifest['audit']['source'],
    } | {'formal/' + row['source'] for row in manifest['modules']}
    verify.require(isinstance(hashes, dict) and required <= set(hashes),
                   'Current independent review must bind every input, module and compiler artifact')
    for name, expected in hashes.items():
        verify.require(verify.digest(verify.safe_relative(case_root, name)) == expected,
                       'Current independent semantic review source hash is stale: ' + name)
    items = review.get('items', [])
    ids = [item['id'] for item in items]
    verify.require(len(ids) == len(set(ids)) and set(ids) == {row['id'] for row in alignment['items']},
                   'Current independent review must cover every obligation exactly once')
    by_id = {item['id']: item for item in items}
    for item in alignment['items']:
        expected = 'passed' if item['status'] == 'complete' else 'partial'
        verify.require(by_id[item['id']].get('status') == expected,
                       'Current independent review and alignment coverage differ: ' + item['id'])
        checks = by_id[item['id']].get('checks')
        verify.require(isinstance(checks, list) and bool(checks) and
                       all(isinstance(check, str) and check.strip() for check in checks),
                       'Current independent review needs substantive per-obligation checks: ' + item['id'])
    status = 'passed' if all(item['status'] == 'complete' for item in alignment['items']) else 'partial'
    verify.require(review.get('status') == status,
                   'Current independent review must retain every partial obligation')
    return {'path': review_name, 'sha256': verify.digest(path), 'reviewer': review['reviewer'],
            'status': status, 'bound_files_rechecked': len(hashes), 'stage_ids': ids}


def check_recompiled_case(repo, layout, mapping, baseline_row, review_name, *, write_binding=False):
    """A new compilation replaces current evidence, without rewriting its provenance."""
    case_root = repo / mapping['current']; formal = case_root / 'formal'
    checked = verify.load(verify.safe_relative(formal, 'checked-manifest.json'))
    old_case = verify.load(verify.safe_relative(formal, 'checked-case.json'))
    verify.require(verify.digest(formal / 'checked-manifest.json') == baseline_row['manifest_sha256'] and
                   verify.digest(formal / 'checked-case.json') == checked['frozen_inputs']['case.json'],
                   'Recompiled evidence must preserve the original checked identities')
    current, _, *_ = verify.validate_case(formal / 'manifest.json')
    case = verify.load(case_root / 'case.json'); alignment = verify.load(formal / 'alignment.json')
    verify.require(checked['case_id'] == old_case['id'] == mapping['id'] == current['case_id'] and
                   checked['case_version'] == old_case['version'] == current['case_version'] ==
                   baseline_row['case_version'], 'Recompiled case identity or version changed')
    allowed = check_metadata_relocation(case_root, old_case, case, alignment)
    verify.require(case.get('review', {}).get('human') == 'pending',
                   'Recompilation cannot grant human approval')
    # Reference prose and author proofs may evolve. Candidate bytes, grading and
    # the stage contract stay fixed: this is evidence maintenance, not a new case.
    preserved = {case[key] for key in ('task', 'rubric', 'group_contract')}
    preserved.update(row['source'] for row in case.get('solver_files', []))
    preserved_hashes = {name: checked['frozen_inputs'][name] for name in sorted(preserved)}
    verify.require(all(current['frozen_inputs'][name] == expected
                       for name, expected in preserved_hashes.items()),
                   'Recompiled author evidence cannot change candidate inputs, rubric or stage contract')
    report, declarations, alignment = check_compiler_report(
        formal, current, current, None, manifest_name='manifest.json')
    verify.require(evidence_time(report['started_utc']) <= evidence_time(report['finished_utc']) and
                   evidence_time(report['started_utc']) > evidence_time(baseline_row['compile_finished_utc']),
                   'Recompiled evidence needs a new, ordered compilation interval')
    complete = [item['id'] for item in alignment['items'] if item['status'] == 'complete']
    incomplete = [{'id': item['id'], 'gaps': item['gaps']} for item in alignment['items']
                  if item['status'] != 'complete']
    verify.require(report.get('author_coverage') == {
        'items': len(alignment['items']), 'claimed_complete': len(complete),
        'declaration_inventory_verified': True, 'semantic_correctness_automatically_established': False,
    } and report.get('mathematical_or_human_review') is None,
        'Recompiled report must audit the current coverage without inferring semantic or human approval')
    review = check_recompiled_review(repo, case_root, current, alignment, report, review_name)
    binding = {
        'schema': BINDING_SCHEMA, 'kind': 'recompiled-author-evidence',
        'case_id': current['case_id'], 'case_version': current['case_version'],
        'baseline_commit': layout['baseline_commit'],
        'previous_case_path': mapping['previous'], 'current_case_path': mapping['current'],
        'checked_case': {'path': 'checked-case.json', 'sha256': verify.digest(formal / 'checked-case.json')},
        'checked_manifest': {'path': 'checked-manifest.json', 'sha256': verify.digest(formal / 'checked-manifest.json')},
        'prior_evidence': {
            'verification_report_sha256': baseline_row['verification_report_sha256'],
            'declarations_sha256': baseline_row['declarations_sha256'],
            'independent_semantic_review': baseline_row['independent_semantic_review'],
        },
        'current_case': {'path': '../case.json', 'sha256': verify.digest(case_root / 'case.json')},
        'current_manifest': {'path': 'manifest.json', 'sha256': verify.digest(formal / 'manifest.json')},
        'verification_report': {'path': 'verification-report.json', 'sha256': verify.digest(formal / 'verification-report.json')},
        'declarations': {'path': 'declarations.json', 'sha256': verify.digest(formal / 'declarations.json')},
        'independent_semantic_review': review,
        'preserved_inputs': preserved_hashes, 'allowed_metadata_changes': allowed,
    }
    binding_path = formal / 'input-binding.json'
    if write_binding:
        verify.save(binding_path, binding)
    else:
        verify.require(verify.load(verify.safe_relative(formal, 'input-binding.json')) == binding,
                       'Input binding differs from rechecked current compilation and review')
    return {
        'id': mapping['id'], 'case_version': current['case_version'],
        'case_path': mapping['current'], 'formal_status': 'partial' if incomplete else 'complete',
        'items': len(alignment['items']), 'complete_items': complete, 'incomplete_items': incomplete,
        'modules': len(current['modules']), 'declarations': len(declarations),
        'manifest_sha256': verify.digest(formal / 'manifest.json'),
        'checked_manifest_sha256': verify.digest(formal / 'checked-manifest.json'),
        'case_sha256': verify.digest(case_root / 'case.json'),
        'checked_case_sha256': verify.digest(formal / 'checked-case.json'),
        'input_binding_sha256': verify.digest(binding_path),
        'alignment_sha256': verify.digest(formal / 'alignment.json'),
        'verification_report_sha256': verify.digest(formal / 'verification-report.json'),
        'declarations_sha256': verify.digest(formal / 'declarations.json'),
        'compile_status': 'passed', 'compile_started_utc': report['started_utc'],
        'compile_finished_utc': report['finished_utc'],
        'verification_profile': verify.manifest_profile(current),
        'metadata_relocation': 'original checked identities retained as provenance; current evidence recompiled',
        'fresh_compilation_repeated': True,
        'independent_semantic_review': review, 'human_review': 'pending',
    }


def check_case(repo, layout, mapping, baseline_row, *, write_binding=False, recompiled_review=None):
    repo = Path(repo).resolve()
    case_root = repo / mapping['current']; formal = case_root / 'formal'
    if recompiled_review is not None:
        return check_recompiled_case(repo, layout, mapping, baseline_row, recompiled_review,
                                     write_binding=write_binding)
    if (formal / 'input-binding.json').exists():
        saved = verify.load(verify.safe_relative(formal, 'input-binding.json'))
        if saved.get('kind') == 'recompiled-author-evidence':
            return check_recompiled_case(repo, layout, mapping, baseline_row,
                                         saved['independent_semantic_review']['path'],
                                         write_binding=write_binding)
        verify.require(saved.get('kind') == 'metadata-only-layout-migration',
                       'Unknown author input binding kind')
    binding = expected_binding(repo, layout, mapping, baseline_row)
    current = verify.load(formal / 'manifest.json'); checked = verify.load(formal / 'checked-manifest.json')
    report, declarations, alignment = check_compiler_report(formal, current, checked, baseline_row)
    review = check_review(repo, layout, case_root, baseline_row)
    complete = [item['id'] for item in alignment['items'] if item['status'] == 'complete']
    incomplete = [{'id': item['id'], 'gaps': item['gaps']} for item in alignment['items']
                  if item['status'] != 'complete']
    verify.require(set(review['stage_ids']) == {item['id'] for item in alignment['items']},
                   'Independent semantic review does not cover every obligation')
    verify.require(not incomplete or review['status'] == 'partial',
                   'Partial obligations were mislabeled as semantic completion')
    verify.require(complete == baseline_row['complete_items'] and
                   incomplete == baseline_row['incomplete_items'], 'Original coverage claims changed')
    binding_path = formal / 'input-binding.json'
    if write_binding:
        verify.save(binding_path, binding)
    else:
        verify.require(verify.load(verify.safe_relative(formal, 'input-binding.json')) == binding,
                       'Input binding differs from rechecked metadata-only migration')
    return {
        'id': mapping['id'], 'case_version': current['case_version'],
        'case_path': mapping['current'], 'formal_status': 'partial' if incomplete else 'complete',
        'items': len(alignment['items']), 'complete_items': complete, 'incomplete_items': incomplete,
        'modules': len(current['modules']), 'declarations': len(declarations),
        'manifest_sha256': verify.digest(formal / 'manifest.json'),
        'checked_manifest_sha256': verify.digest(formal / 'checked-manifest.json'),
        'case_sha256': verify.digest(case_root / 'case.json'),
        'checked_case_sha256': verify.digest(formal / 'checked-case.json'),
        'input_binding_sha256': verify.digest(binding_path),
        'alignment_sha256': verify.digest(formal / 'alignment.json'),
        'verification_report_sha256': verify.digest(formal / 'verification-report.json'),
        'declarations_sha256': verify.digest(formal / 'declarations.json'),
        'compile_status': 'passed', 'compile_started_utc': report['started_utc'],
        'compile_finished_utc': report['finished_utc'],
        'verification_profile': verify.manifest_profile(current),
        'metadata_relocation': 'validated; original compiler report remains bound to checked manifest',
        'fresh_compilation_repeated': False,
        'independent_semantic_review': review, 'human_review': 'pending',
    }


def check_all(repo, *, write_bindings=False):
    repo = Path(repo).resolve(); layout = load_layout(repo)
    checked_path = verify.safe_relative(repo, 'verification/author/checked-ledger.json')
    baseline = checked_ledger(repo, layout)
    suite = verify.load(verify.safe_relative(repo, 'cases/suite.json'))
    verify.require(suite.get('schema') == 'math-gauge.suite/v1', 'Invalid canonical benchmark suite')
    suite_paths = {'cases/' + name for name in suite['cases']}
    verify.require(suite_paths == {row['current'] + '/case.json' for row in layout['case_paths']}
                   and len(suite['cases']) == len(layout['case_paths']),
                   'Canonical suite and evidence layout disagree')
    verify.require({row['id'] for row in baseline['cases']} ==
                   {row['id'] for row in layout['case_paths']} and
                   len(baseline['cases']) == len(layout['case_paths']),
                   'Layout must preserve every originally checked paper')
    rows = [check_case(repo, layout, mapping, original_row(repo, layout, mapping['id']),
                       write_binding=write_bindings) for mapping in layout['case_paths']]
    counts = {
        'papers': len(rows), 'fully_formalized_papers': sum(row['formal_status'] == 'complete' for row in rows),
        'items': sum(row['items'] for row in rows),
        'complete_items': sum(len(row['complete_items']) for row in rows),
        'modules': sum(row['modules'] for row in rows),
        'declarations_with_per_case_repetition': sum(row['declarations'] for row in rows),
    }
    recompiled = [row['id'] for row in rows if row['fresh_compilation_repeated']]
    if not recompiled:
        verify.require(counts == baseline['counts'], 'Author evidence totals changed during metadata relocation')
    else:
        verify.require(all(counts[key] == baseline['counts'][key] for key in ('papers', 'items')),
                       'Recompilation cannot change the paper or obligation inventory')
    result = {
        'schema': 'math-gauge.author-evidence-ledger/v2', 'checked_at_utc': verify.now(),
        'baseline_commit': layout['baseline_commit'],
        'compiler_inputs_baseline_commit': baseline['baseline_commit'],
        'checked_ledger': {'path': 'verification/author/checked-ledger.json',
                           'sha256': verify.digest(checked_path)},
        'layout': {'path': 'verification/layout.json',
                   'sha256': verify.digest(repo / 'verification/layout.json')},
        'scope': 'Current benchmark; original compilation, metadata relocation and independent semantic review are separate evidence',
        'candidate_model_calls': 0, 'human_approved': 0,
        'fresh_compilation_repeated': bool(recompiled),
        'counts': counts,
        'checks': [
            'Current v2 manifests bind the complete case, contract, candidate inputs, alignment and coverage',
            'Retained checked manifests and checked case metadata preserve original compiler inputs',
            'Only explicit path relocation, evaluator references and derived formalization metadata changed',
            'Original reports retain their hashes and timestamps and bind the checked manifests',
            'Every retained compiler log, complete local declaration audit and inventory matches its original report',
            'Only propext, Classical.choice and Quot.sound occur in the original collected axiom closure',
            'Every mapped declaration exists in the compiled local-module inventory',
            'Independent reviews and every recorded reviewed-source hash resolve through explicit layout mapping',
            'Original mathematical input and Lean source hashes are unchanged; partial obligations remain partial',
        ],
        'cases': rows,
    }
    if recompiled:
        result['recompiled_cases'] = recompiled
        result['checks'] = [
            'Every current manifest binds the complete case, contract, candidate inputs, alignment and coverage',
            'The checked ledger and checked manifests remain immutable provenance',
            'Unchanged cases retain every metadata-only migration and original evidence check',
            'Recompiled cases bind fresh isolated reports, complete declaration inventories and every compiler log to current source hashes',
            'Only propext, Classical.choice and Quot.sound occur in the collected axiom closures; local axioms are rejected',
            'Every mapped declaration exists in the compiled local-module inventory',
            'Recompiled cases retain original candidate inputs, rubric and stage contract',
            'Current independent AI reviews bind every current input, module, manifest and compiler artifact',
            'Coverage follows the source-bound independent review; compilation and human approval remain distinct',
        ]
    return result


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=Path(__file__).resolve().parents[2])
    parser.add_argument('--write', action='store_true', help='Rebuild the current ledger after all checks pass')
    parser.add_argument('--bind-all', action='store_true', help='Refresh validated input bindings; no compiler invocation')
    parser.add_argument('--bind-recompiled', metavar='CASE_ID',
                        help='Bind one already recompiled case and its current independent semantic review')
    parser.add_argument('--semantic-review', metavar='REPOSITORY_PATH',
                        help='Current source-bound independent review; required with --bind-recompiled')
    args = parser.parse_args(argv)
    if bool(args.bind_recompiled) != bool(args.semantic_review):
        parser.error('--bind-recompiled and --semantic-review are required together')
    try:
        if args.bind_recompiled:
            repo = args.root.resolve(); layout = load_layout(repo)
            mappings = [row for row in layout['case_paths'] if row['id'] == args.bind_recompiled]
            verify.require(len(mappings) == 1, 'Unknown recompiled case id')
            check_case(repo, layout, mappings[0], original_row(repo, layout, args.bind_recompiled),
                       write_binding=True, recompiled_review=args.semantic_review)
        result = check_all(args.root, write_bindings=args.bind_all)
        ledger = args.root / 'verification/author/ledger.json'
        if args.write:
            verify.save(ledger, result)
        elif not (args.bind_all or args.bind_recompiled):
            saved = verify.load(ledger)
            current = dict(result)
            saved.pop('checked_at_utc', None); current.pop('checked_at_utc', None)
            verify.require(saved == current, 'Saved ledger differs from rechecked evidence')
        print(json.dumps({'status': 'passed', 'counts': result['counts'], 'candidate_model_calls': 0,
                          'fresh_compilation_repeated': result['fresh_compilation_repeated']}))
        return 0
    except (OSError, ValueError, KeyError, StopIteration, verify.VerificationError) as error:
        print(str(error), file=sys.stderr)
        return 1


if __name__ == '__main__':
    raise SystemExit(main())
