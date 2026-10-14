"""Exercise suite exit-status controls without launching a JVM."""
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest


class SuiteRunnerTest(unittest.TestCase):
    def run_suite(self, *, exit_code=0, summary=True, tests=1, chunk="1", start="1"):
        with tempfile.TemporaryDirectory(prefix="rainbow-suite-control-") as directory:
            root = Path(directory)
            (root / "scripts").mkdir()
            runner = root / "scripts/run-suite-chunked.sh"
            shutil.copyfile(Path(__file__).with_name(runner.name), runner)
            (root / "test/rainbow").mkdir(parents=True)
            (root / "test/rainbow/control_test.clj").write_text("(ns rainbow.control-test)\n")
            (root / "bin").mkdir()
            lein = root / "bin/lein"
            lein.write_text("#!/bin/sh\n" +
                            (f"printf 'Ran {tests} tests containing {tests} assertions.\\n"
                             "0 failures, 0 errors.\\n'\n" if summary else "") +
                            f"exit {exit_code}\n")
            lein.chmod(0o755)
            results = root / "results.tsv"
            environment = dict(os.environ,
                               PATH=str(root / "bin") + os.pathsep + os.environ["PATH"],
                               RAINBOW_START_CHUNK=start, RAINBOW_MIN_FREE_PAGES="0",
                               RAINBOW_NS_FILTER="")
            result = subprocess.run(["bash", str(runner), chunk, str(results)],
                                    env=environment, capture_output=True, text=True, timeout=10)
            return result, results.read_text() if results.exists() else ""

    def test_success_requires_a_successful_child(self):
        result, table = self.run_suite()
        self.assertEqual(0, result.returncode, result.stderr)
        self.assertIn("\tPASS\t", table)
        result, table = self.run_suite(exit_code=7)
        self.assertEqual(1, result.returncode, result.stdout)
        self.assertIn("\tFAIL\t", table)
        self.assertIn("exit 7", result.stdout)

    def test_missing_summary_is_incomplete(self):
        result, table = self.run_suite(summary=False)
        self.assertEqual(2, result.returncode)
        self.assertIn("\tTERMINATED\t", table)

    def test_zero_executed_tests_is_not_a_pass(self):
        result, table = self.run_suite(tests=0)
        self.assertEqual(1, result.returncode)
        self.assertIn("\tFAIL\t", table)

    def test_invalid_chunks_and_empty_resumes_are_refused(self):
        for chunk, start in [("0", "1"), ("-1", "1"), ("abc", "1"),
                             ("08", "1"), ("1000000000", "1"), ("1", "0"), ("1", "2")]:
            with self.subTest(chunk=chunk, start=start):
                result, table = self.run_suite(chunk=chunk, start=start)
                self.assertEqual(2, result.returncode)
                self.assertEqual("", table)


if __name__ == "__main__":
    unittest.main()
