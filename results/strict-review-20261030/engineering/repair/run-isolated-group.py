"""One current-source Lean acceptance test; retain actual fixture artifacts."""
import hashlib
import io
import json
import shutil
import sys
import unittest
from pathlib import Path

REPO = Path('/Users/g4i/lab/math-gauge')
EVIDENCE = Path('/private/tmp/math-gauge-strict-20261030/engineering/repair')
sys.path.insert(0, str(REPO))
from tests.test_question_groups import QuestionGroupContracts


class CapturedGroupAcceptance(QuestionGroupContracts):
    def tearDown(self):
        # Preserve the actual verifier output before TestCase removes its own
        # temporary workspace; do not alter any source or receipt.
        run_path = getattr(self, 'run_path', None)
        if run_path and run_path.is_dir():
            shutil.copytree(run_path, EVIDENCE / 'isolated-group-run')


case = CapturedGroupAcceptance('test_nested_group_compiles_and_review_binds_real_audit')
stream = io.StringIO()
result = unittest.TextTestRunner(verbosity=2, stream=stream).run(unittest.TestSuite([case]))
log = stream.getvalue()
(EVIDENCE / 'isolated-group.log').write_text(log)
summary = {
    'schema': 'math-gauge.targeted-isolated-acceptance/v1',
    'command': 'PYTHONDONTWRITEBYTECODE=1 MATH_GAUGE_CANDIDATE_DEPENDENCIES=/private/tmp/math-gauge-benchmark-dependencies-20261030 python3 /private/tmp/math-gauge-strict-20261030/engineering/repair/run-isolated-group.py',
    'tests': result.testsRun, 'failures': len(result.failures),
    'errors': len(result.errors), 'skipped': len(result.skipped),
    'passed': result.wasSuccessful() and result.testsRun == 1 and not result.skipped,
    'candidate_model_requests': 0,
    'fixture_only': True,
    'scope': 'One actual macOS-isolated synthetic Lean project, including immutable background, alignment inventory, contract receipt/manifest binding and group review. No mathematical model score or chapter reference compilation.',
    'source_files_sha256': {str(p.relative_to(REPO)): hashlib.sha256(p.read_bytes()).hexdigest()
                            for p in [REPO/'math_gauge/execution.py', REPO/'math_gauge/review.py',
                                      REPO/'math_gauge/catalog.py', REPO/'tests/test_question_groups.py']},
    'log': str(EVIDENCE/'isolated-group.log'),
    'log_sha256': hashlib.sha256(log.encode()).hexdigest(),
    'artifacts': str(EVIDENCE/'isolated-group-run'),
}
(EVIDENCE / 'isolated-group.json').write_text(json.dumps(summary, ensure_ascii=False, indent=2)+'\n')
print(log, end='')
print(json.dumps(summary, ensure_ascii=False, indent=2))
sys.exit(0 if summary['passed'] else 1)
