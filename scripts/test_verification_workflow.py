"""Guard portable runner selection, job budgets, and checkpoint publication."""
from pathlib import Path
import re
import unittest


WORKFLOW = Path(__file__).resolve().parents[1] / '.github/workflows/verify.yml'


class WorkflowCheckpointTests(unittest.TestCase):
    def setUp(self):
        self.source = WORKFLOW.read_text()
        # This workflow has one job and a flat list of named steps. Keep these
        # indentation-sensitive checks independent of third-party YAML packages.
        self.job, steps = self.source.split('    steps:\n', 1)
        self.steps = {}
        for block in re.split(r'^      - name: ', steps, flags=re.MULTILINE)[1:]:
            name, body = block.split('\n', 1)
            self.assertNotIn(name, self.steps)
            self.steps[name] = body
        self.assertTrue(self.steps)

    def test_runner_is_selected_manually_with_portable_defaults(self):
        dispatch = self.job.split('  workflow_dispatch:\n', 1)[1].split('\npermissions:', 1)[0]
        inputs = dict(re.findall(
            r'^      ([a-z_]+):\n((?:^        .*\n)+)', dispatch, re.MULTILINE))
        self.assertIn("default: 'ubuntu-latest'\n", inputs['runner_label'])
        self.assertIn('type: string\n', inputs['runner_label'])
        self.assertIn("default: '2'\n", inputs['jobs'])
        self.assertIn('    runs-on: ${{ inputs.runner_label }}\n', self.job)
        self.assertNotRegex(self.source, r'(?m)^  (push|pull_request|pull_request_target):',
                            'Runner choice must remain a manual workflow input')

    def test_all_step_budgets_leave_room_under_the_job_limit(self):
        limit = re.findall(r'^    timeout-minutes: ([0-9]+)$', self.job, re.MULTILINE)
        self.assertEqual(len(limit), 1)
        total = 0
        for name, step in self.steps.items():
            with self.subTest(step=name):
                budgets = re.findall(r'^        timeout-minutes: ([0-9]+)$', step,
                                     re.MULTILINE)
                self.assertEqual(len(budgets), 1, 'Every step needs a bounded budget')
                total += int(budgets[0])
        self.assertLessEqual(total + 5, int(limit[0]),
                             'Reserve job overhead as well as packaging and uploads')

    def test_replay_soft_stop_precedes_actions_step_cancellation(self):
        replay = self.steps['Replay all modules and audit the final theorem']
        cutoff = re.search(r'timeout --signal=TERM --kill-after=([0-9]+)s ([0-9]+)m',
                           replay)
        self.assertIsNotNone(cutoff, 'Replay must stop before the job is cancelled')
        grace, minutes = map(int, cutoff.groups())
        step_minutes = int(re.search(r'timeout-minutes: ([0-9]+)', replay)[1])
        self.assertGreaterEqual(grace, 30, 'Give the runner time to stop compiler children')
        self.assertLess(minutes * 60 + grace, step_minutes * 60)
        self.assertNotIn('continue-on-error:', replay)
        self.assertNotIn('|| true', replay)

    def test_checkpoint_upload_is_first_and_runs_after_interrupted_replay(self):
        names = list(self.steps)
        package = names.index('Prepare verification evidence and checkpoint')
        checkpoint = names.index('Upload resumable compiled-module checkpoint')
        self.assertEqual(checkpoint, package + 1)
        self.assertGreater(names.index('Upload verification report and module timings'), checkpoint)
        self.assertGreater(names.index('Upload compiler diagnostics'), checkpoint)
        for name in (names[package], names[checkpoint]):
            self.assertIn("if: ${{ always() && steps.replay.outcome != 'skipped' }}",
                          self.steps[name])
        step = self.steps[names[checkpoint]]
        self.assertIn('name: proof-checkpoint\n', step)
        self.assertIn('path: .verification/artifacts/checkpoint.tar\n', step)
        self.assertIn('overwrite: false\n', step,
                      'A rerun must not delete its previously uploaded checkpoint')
        self.assertIn('if-no-files-found: error\n', step)


if __name__ == '__main__':
    unittest.main()
