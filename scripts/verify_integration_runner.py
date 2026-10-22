#!/usr/bin/env python3
"""Regression checks for integration subprocess failure reporting."""
import contextlib
import io
from pathlib import Path
import subprocess
import sys
import unittest

from verify_integration import DIAGNOSTIC_LIMIT, run_checked


class IntegrationRunner(unittest.TestCase):
    def invoke(self, code, **kwargs):
        return run_checked([sys.executable, '-c', code], Path.cwd(), **kwargs)

    def test_success_keeps_output_captured(self):
        diagnostics = io.StringIO()
        with contextlib.redirect_stderr(diagnostics):
            result = self.invoke("print('success')")
        self.assertEqual(result.stdout, 'success\n')
        self.assertEqual(diagnostics.getvalue(), '')

    def test_failure_reports_combined_output_and_preserves_exit(self):
        diagnostics = io.StringIO()
        with contextlib.redirect_stderr(diagnostics):
            with self.assertRaises(subprocess.CalledProcessError) as caught:
                self.invoke("import sys; print('stdout', flush=True); "
                            "print('source hash missing', file=sys.stderr); sys.exit(7)")
        self.assertEqual(caught.exception.returncode, 7)
        for expected in ('stdout', 'source hash missing', 'status 7', 'cwd:', '-c'):
            self.assertIn(expected, diagnostics.getvalue())

    def test_large_failure_output_is_bounded_and_keeps_tail(self):
        diagnostics = io.StringIO()
        with contextlib.redirect_stderr(diagnostics):
            with self.assertRaises(subprocess.CalledProcessError):
                self.invoke("print('x' * 50000); print('final diagnostic'); raise SystemExit(1)")
        self.assertIn('output truncated', diagnostics.getvalue())
        self.assertIn('final diagnostic', diagnostics.getvalue())
        self.assertLess(len(diagnostics.getvalue()), DIAGNOSTIC_LIMIT + 1000)

    def test_timeout_reports_partial_output_and_still_fails(self):
        diagnostics = io.StringIO()
        with contextlib.redirect_stderr(diagnostics):
            with self.assertRaises(subprocess.TimeoutExpired):
                self.invoke("import time; print('before timeout', flush=True); time.sleep(10)",
                            timeout=0.5)
        self.assertIn('timed out', diagnostics.getvalue())
        self.assertIn('before timeout', diagnostics.getvalue())

    def test_empty_failure_output_is_explicit(self):
        diagnostics = io.StringIO()
        with contextlib.redirect_stderr(diagnostics):
            with self.assertRaises(subprocess.CalledProcessError):
                self.invoke('raise SystemExit(1)')
        self.assertIn('[no subprocess output]', diagnostics.getvalue())


if __name__ == '__main__':
    unittest.main()
