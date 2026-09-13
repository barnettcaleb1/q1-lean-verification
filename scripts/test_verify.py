"""Regression checks for failures that the verification gate must reject."""

from pathlib import Path
import hashlib
import json
import tempfile
import unittest

from verify import check_axioms, check_sources


class AuditParserTests(unittest.TestCase):
    def test_multiline_and_apostrophe(self):
        result = check_axioms("'Q1.example'₂' depends on axioms: [propext,\n Classical.choice, Quot.sound]\n", ["Q1.example'₂"])
        self.assertEqual(len(result), 1)

    def test_axiom_free(self):
        self.assertEqual(check_axioms("'Q1.a' does not depend on any axioms\n", ["Q1.a"]), {"Q1.a": set()})

    def test_rejects_admission(self):
        with self.assertRaises(ValueError):
            check_axioms("'Q1.a' depends on axioms: [sorryAx]\n", ["Q1.a"])

    def test_rejects_missing_extra_duplicate_and_diagnostic(self):
        line = "'Q1.a' depends on axioms: [propext]\n"
        for output, expected in [("", ["Q1.a"]), (line, []), (line * 2, ["Q1.a"]), (line + "warning: surprise\n", ["Q1.a"])]:
            with self.subTest(output=output), self.assertRaises(ValueError):
                check_axioms(output, expected)


class SourceManifestTests(unittest.TestCase):
    def test_rejects_changed_missing_and_extra_sources(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            (root / "Q1").mkdir()
            (root / "verification").mkdir()
            audit = "#print axioms Q1.a\n"
            (root / "Audit.lean").write_text(audit)
            (root / "verification/source-manifest.json").write_text(json.dumps({
                "files": {"Audit.lean": hashlib.sha256(audit.encode()).hexdigest()},
                "audited_declarations": ["Q1.a"]
            }))
            self.assertEqual(check_sources(root), ["Q1.a"])
            (root / "Audit.lean").write_text(audit + "\n")
            with self.assertRaises(ValueError):
                check_sources(root)
            (root / "Audit.lean").unlink()
            with self.assertRaises(ValueError):
                check_sources(root)
            (root / "Audit.lean").write_text(audit)
            (root / "Q1/Extra.lean").write_text("")
            with self.assertRaises(ValueError):
                check_sources(root)


if __name__ == "__main__":
    unittest.main()
