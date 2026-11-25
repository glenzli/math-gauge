"""Timing-only projection of the authorized Dot evidence replacement."""
from copy import deepcopy
from pathlib import Path
import hashlib
import json
import re

from . import dot_rerun_timings as old, timings
from .mathematical_profile import source_bytes
from .theorem_extension_calibration import require

FOLDER = old.DIRECTORY + '/evidence-replacement-v1'
INDEX = FOLDER + '/index.json'
REPORT = FOLDER + '/timings.json'
OLD_INDEX_SHA = '0d8f0315de0814a72f5c89f052c244f7fe86943848b3aa7366e0d42c2be5a392'
OLD_REPORT_SHA = 'e6af741e2008acc5dd21e679e2ad83ce2dbd67ab8a65c9267569b5e74d4005a2'
WRITTEN = frozenset('MG-'+x for x in ('GP001','GR021','AR002','BC001','PS001','GR022','GR023'))
A1 = 'MG-C003:A1'
ROUNDS = frozenset('MG-C003:R'+str(i) for i in (1,2,3))
SLOTS = {cid+':A1' for cid in WRITTEN} | {A1} | ROUNDS
# Retained root launch transcript brackets the invocation, not a measured clock.
CHAPTER_START_BOUNDS = ('2026-11-25T14:26:45Z','2026-11-25T14:27:27Z')
COST_BASIS = 'subscription_marginal_zero'
COST_NOTE = dict(marker='*', text=dict(
    zh='Dot (261125)：已付订阅内，本轮额外费用 $0；不是底层推理成本或订阅费用。',
    en='Dot (261125): $0 extra for this run under the existing subscription, not a measure of inference or subscription cost.'))


def _sha(raw):
    return hashlib.sha256(raw).hexdigest()


def _read_prior(root):
    raw = (Path(root)/old.INDEX_PATH).read_bytes()
    require(_sha(raw) == OLD_INDEX_SHA, 'Prior Dot timing index is not the preserved source')
    index = json.loads(raw)
    report = source_bytes(root,index['projection'])
    require(_sha(report) == OLD_REPORT_SHA, 'Prior Dot timing projection is not the preserved source')
    return json.loads(report)


def _events(raw, case):
    by_kind = {}
    for line in raw.splitlines():
        row = json.loads(line)
        if row['case'] != case:
            continue
        kind = row['event']
        if kind in ('dispatch_begin','dispatch_observation_start','dispatch_ack',
                    'dispatch_observation_ack','terminal_observed'):
            require(kind not in by_kind, 'Duplicate physical clock event')
            by_kind[kind] = row
    return by_kind


def read_receipt(slot, case, events_raw, sealed_raw, request, answer, *, prior_capture=None):
    """Private binding from terminal designation + raw sealed bytes to clocks.

    For an independently authenticated transport restoration, prior_capture is
    the exact originally designated byte sequence; stay explicit about its hash.
    The caller must bind the restored bytes to its applicable admission proof.
    """
    events = _events(events_raw,case)
    terminal = events['terminal_observed']
    end = timings._stamp(terminal['timestamp_utc'])
    physical_digest = _sha(prior_capture if prior_capture is not None else answer)
    require(physical_digest in re.findall(r'[a-f0-9]{64}',terminal['notes']),
            'Observed terminal belongs to another submission')
    digest = _sha(answer)
    item = dict(slot=slot, request_sha256=_sha(request), answer_sha256=digest,
                physical_capture_sha256=physical_digest, events_sha256=_sha(events_raw),
                native_work_seconds=None, sealed_sha256=None)
    if slot == A1:
        low, high = map(timings._stamp,CHAPTER_START_BOUNDS)
        require(low < high < end, 'Invalid chapter dispatch bracket')
        item.update(seconds=None,bounds_seconds=[(end-high).total_seconds(),(end-low).total_seconds()])
        return item
    start = timings._stamp((events.get('dispatch_begin') or events['dispatch_observation_start'])['timestamp_utc'])
    ack = timings._stamp((events.get('dispatch_ack') or events['dispatch_observation_ack'])['timestamp_utc'])
    require(start <= ack <= end, 'Out-of-order coordinator observations')
    item.update(seconds=(end-start).total_seconds(),bounds_seconds=None)
    if sealed_raw is not None:
        sealed = json.loads(sealed_raw)
        require(sealed.get('answer_sha256') == physical_digest, 'Seal and terminal capture disagree')
        if sealed.get('request_sha256') is not None:
            require(sealed['request_sha256'] == _sha(request), 'Seal uses different request bytes')
        sealed_start = timings._stamp(sealed.get('start_utc') or sealed.get('started_at_utc') or sealed.get('started_utc'))
        sealed_end = timings._stamp(sealed.get('finish_utc') or sealed.get('completion_utc') or sealed.get('finished_at_utc') or sealed.get('finished_utc') or sealed.get('sealed_utc'))
        require(start <= sealed_start <= sealed_end <= end, 'Native work falls outside coordinator observations')
        begin_ns = sealed.get('start_monotonic_ns',sealed.get('started_monotonic_ns'))
        end_ns = sealed.get('finish_monotonic_ns',sealed.get('completion_monotonic_ns',sealed.get('finished_monotonic_ns')))
        if begin_ns is not None or end_ns is not None:
            require(type(begin_ns) is int and type(end_ns) is int and end_ns >= begin_ns,
                    'Native monotonic clocks are not a compatible pair')
            sec=(end_ns-begin_ns)/1e9
        elif sealed.get('elapsed_monotonic_ns') is not None:
            sec=sealed['elapsed_monotonic_ns']/1e9
        else:
            sec=sealed.get('elapsed_monotonic_seconds',sealed.get('elapsed_seconds'))
        require(timings._seconds(sec) and abs(sec-(sealed_end-sealed_start).total_seconds())<0.25,
                'Native monotonic and UTC elapsed clocks disagree')
        item.update(native_work_seconds=sec,sealed_sha256=_sha(sealed_raw))
    require(slot not in {cid+':A1' for cid in WRITTEN} or item['sealed_sha256'] is not None,
            'A replacement written answer needs its same-call timing seal')
    return item


def _project(root, admission, receipt, receipt_sha):
    from scripts.timing_reference import daily_summary,summarize
    result = _read_prior(root)
    selected = {r['case_id']:r for r in
        admission['revised']['_public_tasks']['views']['strict'][old.CONDITION]['tasks']}
    payload = receipt['subjects']
    require(set(payload)==SLOTS,'Unexpected Dot replacement timing scope')
    require({r['case_id'] for r in result['rows']}==set(selected),'Replacement changed the public task cohort')
    require(receipt['private_ledger_sha256']==admission['public_source']['private_source_sha256'],
            'Clock ledger belongs to another exact scoring source')
    old_base_timed=sum(r['base_seconds'] is not None for r in result['rows'] if r['case_id']+':A1' in SLOTS)
    old_round_timed=sum(r['seconds'] is not None for r in result['public_selfcheck_rows'])
    for row in result['rows']:
        cid=row['case_id']; slot=cid+':A1'
        current=selected[cid]
        if slot in payload:
            clocks=payload[slot]
            require(current['response_sha256']==clocks['answer_sha256'],'Selected answer differs from timed submission')
            # Written replacements in this scoped operation have no selected neutral.
            require(not row['revision_selected'],'Replacement changed a preexisting neutral timing parent')
            row.update(answer_sha256=clocks['answer_sha256'],base_seconds=clocks['seconds'],
                       seconds=clocks['seconds'],method=old.METHOD if clocks['seconds'] is not None else None)
        else:
            require(current['response_sha256']==row['answer_sha256'],'Unapproved timing source change')
        row['strict_pass']=current['strict_pass']
    for row in result['public_selfcheck_rows']:
        clocks=payload[row['id']]
        row.update(answer_sha256=clocks['answer_sha256'],seconds=clocks['seconds'],method=old.METHOD)
    frame=result['shared_sample']; by_id={r['case_id']:r for r in result['rows']}
    result['summaries']=dict(daily=daily_summary([by_id[c] for c in frame['case_ids']],frame['weights']),
                             **{'MG-C003':summarize([by_id['MG-C003']])})
    delta=sum(r['seconds'] is not None for r in payload.values())-old_base_timed-old_round_timed
    for key in ('base42','all51'):
        row=result['coverage'][key]; row['timed']+=delta; row['unknown']-=delta
        require(row['unknown']>0,'Unknown-run totals are not authorized guesses')
    result.update(source_admission=admission['selection'],private_admission_sha256=receipt_sha,
                  private_ledger_sha256=receipt['private_ledger_sha256'])
    fixed=dict(benchmark_editions=['1.2.0','1.3.0'],basis=COST_BASIS,total_usd=0,
               authorization_sha256=receipt['authorization_sha256'])
    return result,fixed


def _public_receipt(private_receipt):
    """No raw timestamps, private access paths, messages or contexts in current companion."""
    return dict(private_ledger_sha256=private_receipt['private_ledger_sha256'],
                authorization_sha256=private_receipt['authorization_sha256'],
                subjects={k:{field:v[field] for field in ('answer_sha256','seconds','bounds_seconds','native_work_seconds')}
                          for k,v in private_receipt['subjects'].items()})


def _validate_receipt(receipt):
    require(set(receipt)=={'private_ledger_sha256','authorization_sha256','subjects'}
        and all(timings._sha(receipt[k]) for k in ('private_ledger_sha256','authorization_sha256')),
        'Invalid Dot replacement timing receipt')
    require(set(receipt['subjects'])==SLOTS,'Unexpected Dot evidence replacement timing scope')
    for k,r in receipt['subjects'].items():
        require(set(r)=={'answer_sha256','seconds','bounds_seconds','native_work_seconds'}
            and timings._sha(r['answer_sha256']) and
            (r['native_work_seconds'] is None or timings._seconds(r['native_work_seconds'])),
            'Public clocks exposed private or unrecognized timing material')
        if k==A1:
            b=r['bounds_seconds']
            require(r['seconds'] is None and r['native_work_seconds'] is None
                    and isinstance(b,list) and len(b)==2 and all(timings._seconds(x) for x in b)
                    and 0<b[0]<b[1] and abs((b[1]-b[0])-42)<0.001,
                    'Chapter A1 must stay bounded without a guessed value')
        else:
            require(r['bounds_seconds'] is None and timings._seconds(r['seconds']) and
                (r['native_work_seconds'] is None or r['native_work_seconds']<=r['seconds']),
                'Invalid observed-wall timing for the written or self-check slot')


def prepare(root, admission, private_receipt):
    receipt=_public_receipt(private_receipt); _validate_receipt(receipt)
    sha=_sha(old.encoded(private_receipt))
    result,cost=_project(root,admission,receipt,sha)
    raw=old.encoded(result)
    index=dict(schema='math-gauge.dot-replacement-timing-index/v1',model_id=old.MODEL,
               source_admission=admission['selection'],projection=old.reference(REPORT,raw),
               clock_receipt=receipt,private_clock_receipt_sha256=sha,marginal_cost=cost)
    return {INDEX:old.encoded(index),REPORT:raw}


def load_public(root, admission):
    filepath=Path(root)/INDEX
    if not filepath.is_file(): return None
    require(admission is not None,'Replacement clocks have no active Dot admission')
    raw=filepath.read_bytes(); idx=json.loads(raw)
    require(set(idx)=={'schema','model_id','source_admission','projection','clock_receipt',
                       'private_clock_receipt_sha256','marginal_cost'}
        and idx['schema']=='math-gauge.dot-replacement-timing-index/v1' and idx['model_id']==old.MODEL
        and idx['source_admission']==admission['selection'] and idx['projection']['path']==REPORT
        and timings._sha(idx['private_clock_receipt_sha256'])
        and idx['clock_receipt']['private_ledger_sha256']==admission['public_source']['private_source_sha256'],
        'Replacement clocks do not bind the current exact Dot source')
    _validate_receipt(idx['clock_receipt'])
    expected,cost=_project(root,admission,idx['clock_receipt'],idx['private_clock_receipt_sha256'])
    record=json.loads(source_bytes(root,idx['projection']))
    require(record==expected and idx['marginal_cost']==cost,'Replacement clock and cost projections are inconsistent')
    old.validate_public(record,admission,dict(policy=record['policy'],private_admission_sha256=idx['private_clock_receipt_sha256']))
    bracket=idx['clock_receipt']['subjects'][A1]['bounds_seconds']
    return dict(report=record,source=old.reference(INDEX,raw),chapter_bounds_seconds=bracket,cost=cost,
                clock_receipt=idx['clock_receipt'])
