"""Versioned source-bound offline controls and each actual AGY tool boundary.

Control fixtures authenticate local-tool behavior only. A retained different
model label is never rewritten into a same-model canary or backend attestation.
"""
import json

SCHEMA = 'math-gauge.agy-offline-control-qualification/v1'


def require(value, message):
    if not value:
        raise ValueError(message)


def validate_control(root, reference, execution, evidence):
    q = json.loads(evidence(root, reference))
    binary = execution.get('parent_identity', {}).get('executable_sha256')
    require(q.get('schema') == SCHEMA and q.get('version') == '0.1.0'
            and q.get('post_observation') is True and q.get('source_raw_bytes_rewritten') is False
            and q.get('scope') == 'native_local_file_and_network_boundary_only'
            and q.get('backend_model_attested') is False and q.get('old_model_labels_preserved') is True
            and q.get('real_model_service_calls') == 0
            and isinstance(binary, str) and q.get('native_binary_sha256') == binary,
            'Offline control qualification changed its measured scope or native binary')
    sources = q.get('sources', [])
    require(isinstance(sources, list) and sources
            and len(sources) == len({x['original_path'] for x in sources}),
            'Offline controls require their unique original source map')
    sources = {x['original_path']: x['evidence'] for x in sources}

    def original(item):
        require(item.get('path') in sources and all(item.get(k) == sources[item['path']].get(k)
                for k in ('sha256', 'bytes')), 'Offline control source bytes changed')
        return json.loads(evidence(root, sources[item['path']]))

    validation = json.loads(evidence(root, q['original_validation']))
    require(validation.get('passed') is True and validation.get('real_model_service_calls') == 0,
            'Offline control validation was not actually passed without cloud calls')
    kind = validation.get('schema')
    if kind == 'math-gauge.native-offline-capability-controls/v1':
        positive = original(validation['positive_control'])
        negative = original(validation['original_paired_control'])
        denial = original(validation['negative_control'])
        previous = original(validation['original_validation'])
        bypass = validation.get('bypass_negative_control', {})
        require(negative.get('passed') is False
                and previous.get('passed') is True and previous.get('real_model_service_calls') == 0
                and denial.get('schema') == 'math-gauge.offline-native-bypass-denial/v1'
                and denial.get('passed') is True and denial.get('real_model_service_calls') == 0
                and denial.get('native_unsandboxed_execution_refused') is True
                and denial.get('native_terminal_response_was_empty') is True
                and denial.get('marker_present') is False
                and denial.get('normal_final_not_claimed_for_negative_control') is True
                and validation.get('original_negative_empty_native_final_preserved') is True
                and validation.get('new_per_session_open_network_probes_required') is True
                and validation.get('reused_for_same_binary_different_model') is True
                and bypass.get('passed') is True
                and bypass.get('original_control_result_preserved') is True,
                'Split offline control lost the original negative outcome or reuse boundary')
    elif kind == 'math-gauge.neon-agy1513-registered-parent-endpoint-control/v1':
        positive = original(validation['positive_result'])
        negative = original(validation['negative_result_unchanged'])
        original(validation['source_boundary_summary'])
        reused = original(validation['reused_full_boundary_control'])
        endpoint = original(validation['endpoint_control'])
        outer = endpoint.get('production_parent_probe', {}).get('report', {})
        inner = endpoint.get('native_inner_endpoint_result', {})
        require(validation.get('native_cli_sha256') == binary
                and validation.get('negative_isolation_status_preserved') == 'failed'
                and validation.get('negative_native_SUCCESS_empty_response') is True
                and validation.get('negative_native_readfile_refused') is True
                and validation.get('negative_bypass_refused_without_execution') is True
                and reused.get('passed') is True and reused.get('real_model_service_calls') == 0
                and endpoint.get('passed') is True and endpoint.get('native_cli_sha256') == binary
                and endpoint.get('real_model_service_calls') == endpoint.get('sdk_http_requests')
                    == endpoint.get('sdk_cloud_dispatch_count') == endpoint.get('candidate_tasks_started') == 0
                and endpoint.get('collector_called') is False
                and outer.get('registered_connected') is True and outer.get('unregistered_denied') is True
                and outer.get('http_requests') == 0
                and inner.get('passed') is True and inner.get('connected') is False
                and inner.get('kernel_EPERM') is True and inner.get('http_requests') == 0
                and inner.get('port') == outer.get('registered_port'),
                'Registered parent endpoint control did not preserve candidate denial')
    else:
        raise ValueError('Unsupported retained offline control version')
    report, controlled = positive.get('report', {}), positive.get('execution', {})
    require(positive.get('passed') is True and positive.get('real_model_service_calls') == 0
            and positive.get('no_candidate_mathematics_submitted') is True
            and controlled.get('kind') == 'non_math_canary'
            and controlled.get('parent_identity', {}).get('executable_sha256') == binary
            and controlled.get('result_status') == 'SUCCESS' and controlled.get('tool_mismatch') is None
            and all(report.get(k) is True for k in ('all_denials_and_allows_passed',
                                                    'work_roundtrip', 'tool_network_denied'))
            and report.get('source_bytes_read') == 0
            and negative.get('real_model_service_calls') == 0,
            'Native positive/control binary or measured file/network boundary differs')
    return q


def validate_local_tools(root, data, execution, evidence):
    from .agy_evidence import LOCAL_TOOLS, TOOLS
    plan = json.loads(evidence(root, data['native_plan']))
    original = json.loads(evidence(root, data['native_execution']))
    boundary = data['local_tools']
    settings = json.loads(evidence(root, boundary['settings']))
    opened = json.loads(evidence(root, boundary['open_probe']))
    network = json.loads(evidence(root, boundary['network_probe']))
    audit = json.loads(evidence(root, boundary['artifact_audit']))
    require(original == execution and plan.get('local_tool_policy') == LOCAL_TOOLS
            and plan.get('tool_network_access') is False and plan.get('search_allowed') is False
            and settings.get('enableTerminalSandbox') is True
            and settings.get('toolPermission') == execution.get('permission_mode')
                == plan.get('expected_permission_mode') == 'proceed-in-sandbox'
            and {'read_url(*)','execute_url(*)','mcp(*)'} <= set(settings.get('permissions', {}).get('deny', []))
            and opened.get('passed') is True and network.get('passed') is True
            and audit.get('artifact_checks_passed') is True and not audit.get('credential_links_remaining')
            and all(e.get('name') in TOOLS for e in execution.get('tool_events', [])),
            'Actual AGY session lacks its original local-tool isolation boundary')
    require(opened.get('prompt_sha256') == data['candidate_input']['sha256']
            and opened.get('checks') and all(x.get('passed') is True for x in opened['checks'])
            and network.get('kind') == 'actual-network-connect'
            and network.get('result', {}).get('passed') is True
            and network.get('result', {}).get('errno') in {1,13},
            'Actual per-session open/network probe is absent or differs')
    validate_control(root, boundary['native_control'], execution, evidence)
    snapshot = json.loads(evidence(root, boundary['prelaunch_birth_snapshot']))
    require(snapshot.get('schema') == 'math-gauge.process-birth-snapshot/v1'
            and execution.get('process_identity_protocol') == 'pid+lstart-UTC/v1'
            and execution.get('prelaunch_process_snapshot', {}).get('sha256')
                == boundary['prelaunch_birth_snapshot']['sha256'],
            'Actual native process identities lost their birth-bound prelaunch source')
    reports = boundary.get('process_checks', [])
    require(len(reports) == len({(x.get('original_path'),x.get('pid')) for x in reports}),
            'Repeated registered process probe')
    probes = {(x['original_path'],x['pid']):json.loads(evidence(root,x['evidence'])) for x in reports}
    registered = [execution.get('parent_identity', {}), *execution.get('workers', [])]
    for process in registered:
        probe = probes.get((process.get('policy_evidence'),process.get('pid')))
        require(isinstance(process.get('birth_identity'), str) and process['birth_identity']
                and process.get('process_identity_verified_before_and_after_policy') is True
                and process.get('policy_evidence', '').startswith(data['original_attempt'] + '/session/runtime/')
                and probe and probe.get('kind') == 'live-pid-policy-query'
                and probe.get('pid') == process.get('pid') and probe.get('passed') is True
                and probe.get('prompt_sha256') == data['candidate_input']['sha256']
                and probe.get('checks') and all(x.get('passed') is True for x in probe['checks']),
                'Registered live process lacks its original birth/probe boundary')
    return data
