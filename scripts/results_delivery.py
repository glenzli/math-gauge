"""Project operational A1 delivery counts, independently of mathematical credit."""
import hashlib
import json


def delivery_progress(record, result, *, record_sha256, projection=None, review_completion=None):
    if result.get('submission_summary') is not None:
        source=result['submission_summary']
        if source['planned']!=result['whole_task_counts']['planned']:
            raise ValueError('Submission progress changed the fixed A1 population')
        progress = dict(source,delivered=source['active_final'],undelivered=source['blank'],
                        method_version=result['submission_method_version'])
        if review_completion is not None:
            if review_completion['resolved_pending_count'] != source['pending_original_record_review']:
                raise ValueError('Source recovery belongs to another submission population')
            progress.update(pending_original_record_review=0, source_review_status='complete')
        return progress
    counts = result['whole_task_counts']
    planned, pending = counts['planned'], counts['unknown']
    coverage = result['coverage']
    summary = record.get('execution_summary', {})
    if 'source_reviewed_tasks' in coverage:
        delivered = coverage['source_reviewed_tasks']
    elif 'initial' in record.get('delivery_counts', {}):
        delivered = record['delivery_counts']['initial']
    elif 'delivered_initial_tasks' in summary or 'initial_answers' in summary:
        delivered = summary.get('delivered_initial_tasks', summary.get('initial_answers'))
    elif projection is not None:
        if projection['record_sha256'] != record_sha256:
            raise ValueError('Answer delivery projection binds a different retained record')
        if projection['planned'] != planned:
            raise ValueError('Answer delivery projection changed the task denominator')
        delivered = projection['delivered']
    else:
        delivered = None
    if delivered is not None and (type(delivered) is not int or not 0 <= delivered <= planned):
        raise ValueError('Delivered answers exceed the planned A1 population')
    if delivered is not None:
        # An ungraded answer can still be delivered; mathematical unknowns are not absences.
        pending = min(pending, planned - delivered)
    return {'planned': planned, 'delivered': delivered, 'pending': pending,
            'undelivered': None if delivered is None else planned - pending - delivered}


def load_legacy_projections(root):
    """Two legacy archives lack execution totals; bind their safe source projection."""
    path = root / 'site/answer-delivery.json'
    data = json.loads(path.read_bytes())
    if data.get('schema') != 'math-gauge.answer-delivery-projection/v1':
        raise ValueError('Unsupported answer delivery projection')
    for item in data['models'].values():
        folder = (root / item['record_path']).resolve()
        if not folder.is_relative_to(root.resolve()):
            raise ValueError('Answer delivery projection escapes the source repository')
        if hashlib.sha256((folder / 'record.json').read_bytes()).hexdigest() != item['record_sha256']:
            raise ValueError('Legacy delivery evidence binds a different retained record')
        tasks = json.loads((folder / 'public-task-scores.json').read_bytes())
        if tasks['views']['partial']['nonlogical_retry_3']['source_report_sha256'] != item['source_report_sha256']:
            raise ValueError('Legacy delivery evidence binds a different selected source report')
    return data['models']


def build_legacy_projections(root, private_root):
    """Export counts only, from already selected full source reports; no private IDs."""
    from math_gauge.records import selected_cli_records
    models = {}
    for model, folder in selected_cli_records(root):
        raw = (folder / 'record.json').read_bytes()
        record = json.loads(raw)
        if record.get('submission_evidence') is not None:
            continue
        if record.get('execution_summary'):
            continue
        private = private_root / folder.relative_to(root)
        private_record = json.loads((private / 'record.json').read_bytes())
        report = (private / private_record['assessment_results']['nonlogical_retry_3']['path']).read_bytes()
        public = json.loads((folder / 'public-task-scores.json').read_bytes())
        digest = hashlib.sha256(report).hexdigest()
        if public['views']['partial']['nonlogical_retry_3']['source_report_sha256'] != digest:
            raise ValueError('Delivery source is not the retained rule-selected report')
        tasks = json.loads(report)['tasks']
        # A sealed candidate engineering answer is a delivery even if its old prose was lost.
        if not all(t.get('response_sha256') or t['judgment_source'] == 'selected_sealed_engineering' for t in tasks):
            raise ValueError('Legacy delivery projection needs explicit evidence for missing answers')
        models[model] = {'record_path': str(folder.relative_to(root)),
                         'record_sha256': hashlib.sha256(raw).hexdigest(),
                         'source_report_sha256': digest, 'planned': len(tasks), 'delivered': len(tasks)}
    return {'schema': 'math-gauge.answer-delivery-projection/v1', 'benchmark_version': '0.6.0',
            'models': models}
