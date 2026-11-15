"""Unit tests of scripts/blueprint/check.py's graph checks, statuses and ready order (no Lean).

  python3 scripts/blueprint/test_check.py
"""

import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import check  # noqa: E402


def node(i, kind="lemma", deps=(), decl=None, review=False, **kw):
    n = {"id": i, "kind": kind, "statement": f"{i} holds", "deps": list(deps), "lane": "l",
         "owner": "unassigned", "branch": "", "acceptance": "check.py proves it", "human_review": review, **kw}
    if decl:
        n["decl"], n["module"] = decl, "M"
    return n


def proof(axioms):
    return {"found": True, "kind": "theorem", "proof": True, "predicate": False,
            "declared_in": "M", "axioms": axioms}


class Validate(unittest.TestCase):
    def errors(self, nodes):
        return check.validate({"node": nodes})[1]

    def test_ok(self):
        self.assertEqual(self.errors([node("a"), node("b", deps=["a"])]), [])

    def test_cycle(self):
        errs = self.errors([node("a", deps=["b"]), node("b", deps=["a"])])
        self.assertTrue(any(e.startswith("cycle") for e in errs), errs)

    def test_unknown_dep_and_duplicate(self):
        errs = self.errors([node("a", deps=["z"]), node("a")])
        self.assertTrue(any("unknown dep z" in e for e in errs))
        self.assertTrue(any("duplicate" in e for e in errs))

    def test_review_only_statements(self):
        self.assertTrue(self.errors([node("a", kind="lemma", review=True)]))
        self.assertTrue(self.errors([node("a", kind="obligation", review=True, contract="C",
                                          function="f", edge="E3")]))
        self.assertEqual(self.errors([node("a", kind="premise", review=True)]), [])

    def test_obligation_shape(self):
        self.assertTrue(self.errors([node("a", kind="obligation", contract="C", function="f", edge="E1")]))
        self.assertEqual(self.errors([node("a", kind="obligation", contract="C", function="f", edge="E8")]), [])

    def test_decl_needs_module(self):
        n = node("a")
        n["decl"] = "X"
        self.assertTrue(self.errors([n]))


class Status(unittest.TestCase):
    def st(self, n, info, failure=""):
        return check.classify(n, info, failure)[0]

    def test_statuses(self):
        n = node("a", decl="X")
        self.assertEqual(self.st(n, proof(["propext", "Quot.sound", "Classical.choice"])), "proved")
        self.assertEqual(self.st(n, proof([])), "proved")
        self.assertEqual(self.st(n, proof(["sorryAx", "propext"])), "sorry")
        self.assertEqual(self.st(n, proof(["Lean.ofReduceBool"])), "axioms")
        self.assertEqual(self.st(n, proof(["x._native.native_decide.ax_1_1"])), "axioms")
        self.assertEqual(self.st(n, {"found": False}), "missing")
        self.assertEqual(self.st(n, None, "module not built: ..."), "unbuilt")
        self.assertEqual(self.st(n, None, "lean failed: ..."), "missing")
        self.assertEqual(self.st(node("a"), None), "missing")
        pred = {"found": True, "kind": "def", "proof": False, "predicate": True, "declared_in": "M", "axioms": []}
        self.assertEqual(self.st(n, pred), "statement-only")
        data = dict(pred, predicate=False)
        self.assertEqual(self.st(n, data), "missing")
        self.assertEqual(self.st(node("a", kind="spec", decl="X"), data), "statement-only")
        self.assertEqual(self.st(node("t", kind="trusted"), None), "trusted")

    def test_ready_order(self):
        # p (premise, stated) <- a (proved) <- b (missing) <- c, d (missing); e (missing) <- nothing
        nodes = [node("p", kind="premise", decl="P", review=True), node("a", decl="A", deps=["p"]),
                 node("b", deps=["a"]), node("c", deps=["b"]), node("d", deps=["b"]), node("e")]
        res = {"P": {"found": True, "kind": "def", "proof": False, "predicate": True, "declared_in": "M",
                     "axioms": []}, "A": proof(["propext"])}
        rep = check.compute(nodes, res, {})
        self.assertEqual(rep["nodes"]["a"]["status"], "proved")
        self.assertEqual([r["id"] for r in rep["ready"]], ["b", "e"])
        self.assertEqual(rep["ready"][0]["unblocks"], 2)
        nodes[-1]["priority"] = "P0"
        rep = check.compute(nodes, res, {})
        self.assertEqual([r["id"] for r in rep["ready"]], ["e", "b"])


class Receipts(unittest.TestCase):
    def test_deliverable(self):
        d = node("d", kind="deliverable")
        self.assertEqual(check.classify(d, None, "")[0], "missing")
        d["receipt"] = {"sha": "abc", "check": "https://ci/1"}
        self.assertEqual(check.classify(d, None, "")[0], "delivered")
        self.assertTrue(check.satisfied(d, "delivered"))

    def test_receipt_rules(self):
        errs = check.validate({"node": [node("a", decl="A", receipt={"sha": "x", "check": "y"})]})[1]
        self.assertTrue(any("from the checker" in e for e in errs))
        errs = check.validate({"node": [node("d", kind="deliverable", receipt={"sha": "x"})]})[1]
        self.assertTrue(any("receipt is" in e for e in errs))
        n = node("a")
        del n["acceptance"]
        self.assertTrue(check.validate({"node": [n]})[1])

    def test_proved_gets_run_receipt(self):
        rep = check.compute([node("a", decl="A")], {"A": proof([])}, {}, {"sha": "s", "check": "c"})
        self.assertEqual(rep["nodes"]["a"]["receipt"], {"sha": "s", "check": "c"})


class Unbuilt(unittest.TestCase):
    def test_unbuilt_never_ready(self):
        nodes = [node("a", decl="A"), node("b", deps=["a"])]
        rep = check.compute(nodes, {}, {"M": "module not built: x"})
        self.assertEqual(rep["nodes"]["a"]["status"], "unbuilt")
        self.assertEqual(rep["ready"], [])


class Regression(unittest.TestCase):
    def test_proved_to_sorry_fails(self):
        base = {"nodes": {"a": {"status": "proved"}, "b": {"status": "missing"}}}
        now = {"nodes": {"a": {"status": "sorry", "reason": "depends on sorryAx"}, "b": {"status": "proved"}}}
        self.assertEqual(len(check.regressions(base, now)), 1)
        self.assertEqual(check.regressions(base, {"nodes": {"a": {"status": "proved"}, "b": {"status": "missing"}}}), [])

    def test_baseline_dropped_node_fails(self):
        with tempfile.TemporaryDirectory() as d:
            g = Path(d) / "g.toml"
            g.write_text('[[node]]\nid = "a"\nkind = "lemma"\nstatement = "a"\nlane = "l"\nhuman_review = false\n')
            b = Path(d) / "b.json"
            b.write_text(json.dumps({"nodes": {"gone": {"status": "proved"}, "a": {"status": "missing"}}}))
            p = subprocess.run([sys.executable, check.__file__, "--graph", str(g), "--no-lean",
                                "--baseline", str(b)], capture_output=True, text=True)
            self.assertNotEqual(p.returncode, 0)
            self.assertIn("gone", p.stderr)


if __name__ == "__main__":
    unittest.main()
