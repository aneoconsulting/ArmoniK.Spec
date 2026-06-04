"""Hermetic unit tests for scripts/check_proofs_sync.py."""
import contextlib
import io
import os
import sys
import tempfile
import unittest

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "scripts"))
import check_proofs_sync as cps  # noqa: E402

T = cps.Theorem


def write(d, name, text):
    path = os.path.join(d, name)
    with open(path, "w") as f:
        f.write(text)
    return path


class FindPairsTest(unittest.TestCase):
    def test_pairs_and_missing_base(self):
        with tempfile.TemporaryDirectory() as d:
            write(d, "FooTheorems.tla", "")
            write(d, "FooTheorems_proofs.tla", "")
            write(d, "Bar.tla", "")
            self.assertEqual(
                cps.find_pairs(d),
                [(os.path.join(d, "FooTheorems.tla"),
                  os.path.join(d, "FooTheorems_proofs.tla"))])
            write(d, "OrphanTheorems_proofs.tla", "")
            with self.assertRaises(FileNotFoundError):
                cps.find_pairs(d)


class ExtractTest(unittest.TestCase):
    def test_statements_exclude_proofs(self):
        src = (b"---- MODULE M ----\nEXTENDS Naturals\n"
               b"THEOREM A == ASSUME NEW x \\in Nat\n  PROVE  x \\in Nat\nOBVIOUS\n"
               b"LEMMA B == 1 = 1\nBY DEF Nat\n====\n")
        thms = cps.extract_theorems(src)
        self.assertEqual([(t.kind, t.name, t.statement) for t in thms], [
            ("THEOREM", "A", "ASSUME NEW x \\in Nat PROVE x \\in Nat"),
            ("LEMMA", "B", "1 = 1"),
        ])

    def test_top_comment_and_no_absorption(self):
        # Base-style module (no proofs) so the parser absorbs trailing comments.
        src = (b"---- MODULE M ----\n(* header *)\nEXTENDS Naturals\n"
               b"(* doc A *)\nTHEOREM A == 1 = 1\n"
               b"THEOREM B == 2 = 2\n"
               b"(* doc C *)\nTHEOREM C == 3 = 3\n====\n")
        thms = cps.extract_theorems(src)
        self.assertEqual([(t.name, t.statement, t.comment) for t in thms], [
            ("A", "1 = 1", "(* doc A *)"),   # header NOT attached
            ("B", "2 = 2", ""),              # no comment
            ("C", "3 = 3", "(* doc C *)"),   # not absorbed into B's statement
        ])


class CompareTest(unittest.TestCase):
    def setUp(self):
        self.proofs = [
            T("THEOREM", "A", "sA", "cA"),
            T("LEMMA", "B", "sB", "cB"),
        ]

    def test_identical(self):
        self.assertEqual(cps.compare(list(self.proofs), self.proofs), [])

    def test_missing_in_base(self):
        msgs = cps.compare([self.proofs[0]], self.proofs)
        self.assertTrue(any("missing in base" in m and "B" in m for m in msgs))

    def test_extra_in_base(self):
        base = list(self.proofs) + [T("THEOREM", "C", "sC", "cC")]
        msgs = cps.compare(base, self.proofs)
        self.assertTrue(any("extra in base" in m and "C" in m for m in msgs))

    def test_order_differs(self):
        msgs = cps.compare(list(reversed(self.proofs)), self.proofs)
        self.assertTrue(any("order differs" in m for m in msgs))

    def test_statement_differs(self):
        base = [self.proofs[0], T("LEMMA", "B", "OTHER", "cB")]
        msgs = cps.compare(base, self.proofs)
        self.assertTrue(any("B: statement differs" in m for m in msgs))

    def test_comment_differs(self):
        base = [self.proofs[0], T("LEMMA", "B", "sB", "OTHER")]
        msgs = cps.compare(base, self.proofs)
        self.assertTrue(any("B: top-comment differs" in m for m in msgs))


class MainTest(unittest.TestCase):
    BASE = ("---- MODULE XTheorems ----\nEXTENDS Naturals\n"
            "(* doc *)\nTHEOREM A == 1 = 1\n====\n")
    PROOFS = ("---- MODULE XTheorems_proofs ----\nEXTENDS Naturals, TLAPS\n"
              "(* doc *)\nTHEOREM A == 1 = 1\nOBVIOUS\n====\n")

    def _run(self, base_body):
        with tempfile.TemporaryDirectory() as d:
            write(d, "XTheorems.tla", base_body)
            write(d, "XTheorems_proofs.tla", self.PROOFS)
            with contextlib.redirect_stdout(io.StringIO()):
                return cps.main([d])

    def test_in_sync(self):
        self.assertEqual(self._run(self.BASE), 0)

    def test_out_of_sync(self):
        self.assertEqual(
            self._run(self.BASE.replace("1 = 1", "2 = 2")), 1)


if __name__ == "__main__":
    unittest.main()
