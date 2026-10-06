"""Synthetic-graph CI planner regressions; no Lean, downloads, or repo scans."""
import hashlib
from pathlib import Path
import tempfile
import unittest
from unittest import mock

import ci_plan


def plan(graph, generated=None, sizes=None):
    sizes = sizes or {module: 1 for module in graph}
    hashes = {module: hashlib.sha256(module.encode()).hexdigest() for module in graph}
    return ci_plan.make_plan(graph, sizes, graph if generated is None else generated, hashes)


def closure(graph, targets):
    found, pending = set(), list(targets)
    while pending:
        module = pending.pop()
        if module not in found:
            found.add(module)
            pending.extend(graph[module])
    return found


class PlannerTests(unittest.TestCase):
    def test_fixed_16_shards_and_largest_first_ties(self):
        graph = {f"Leaf{i:02d}": [] for i in range(18)}
        sizes = {module: 1 for module in graph}
        sizes["Leaf17"] = 100
        result = plan(graph, sizes=sizes)
        self.assertEqual(result["shard_count"], 16)
        self.assertEqual(len(result["shards"]), 16)
        self.assertEqual(result["shards"][0]["modules"], ["Leaf17"])
        self.assertEqual(result["shards"][1]["modules"], ["Leaf00", "Leaf15"])
        self.assertEqual(result["shards"][2]["modules"], ["Leaf01", "Leaf16"])

    def test_order_independence_and_stable_digest(self):
        graph = {"Base": [], "A": ["Base"], "B": ["Base"], "C": ["A", "B"]}
        reversed_graph = {module: list(reversed(graph[module])) for module in reversed(graph)}
        self.assertEqual(plan(graph), plan(reversed_graph))
        self.assertEqual(plan(graph)["shards"][0]["modules"], ["C"])
        self.assertEqual(plan(graph)["final_modules"], [])

    def test_maximal_targets_cover_dependencies_through_unlisted_helpers(self):
        graph = {"Data": [], "Helper": ["Data"], "Checker": ["Helper"], "Unrelated": []}
        result = plan(graph, {"Data", "Checker"})
        targets = [module for shard in result["shards"] for module in shard["modules"]]
        self.assertEqual(targets, ["Checker"])
        self.assertEqual(closure(graph, targets), {"Data", "Helper", "Checker"})
        self.assertEqual(result["final_modules"], ["Unrelated"])

    def test_fan_in_named_barriers_and_transitive_dependents_are_deferred(self):
        graph = {f"Leaf{i}": [] for i in range(8)}
        graph.update({"Join": list(graph), "Consumer": ["Join"], "Last": ["Consumer"],
                      "Case.Main": ["Leaf0"], "Field.Final": ["Leaf1"],
                      "Family.All": ["Leaf2"], "Wrapper": ["Case.Main"]})
        result = plan(graph)
        self.assertEqual(result["barrier_modules"], ["Case.Main", "Family.All", "Field.Final", "Join"])
        deferred = {"Join", "Consumer", "Last", "Case.Main", "Field.Final", "Family.All", "Wrapper"}
        self.assertEqual(set(result["deferred_generated_modules"]), deferred)
        targets = [module for shard in result["shards"] for module in shard["modules"]]
        self.assertEqual(set(targets), {f"Leaf{i}" for i in range(8)})
        self.assertFalse(closure(graph, targets) & deferred)

    def test_shard_estimates_count_shared_sources_only_once(self):
        graph = {"Base": []}
        graph.update({f"Leaf{i:02d}": ["Base"] for i in range(17)})
        sizes = {module: 1 for module in graph}
        sizes["Base"] = 10
        result = plan(graph, sizes=sizes)
        self.assertEqual(result["shards"][0]["modules"], ["Leaf00", "Leaf16"])
        for shard in result["shards"]:
            expected = sum(sizes[module] for module in closure(graph, shard["modules"]))
            self.assertEqual(shard["estimated_source_bytes"], expected)
        self.assertEqual(result["shards"][0]["estimated_source_bytes"], 12)

    def test_incomplete_graphs_and_cycles_fail_closed(self):
        for graph, generated, message in [({"A": ["Absent"]}, {"A"}, "Missing local import"),
                                           ({"A": ["B"], "B": ["A"]}, {"A"}, "cycle"),
                                           ({"A": []}, {"Absent"}, "Missing generated")]:
            with self.subTest(graph=graph):
                with self.assertRaisesRegex(ValueError, message):
                    plan(graph, generated)

    def test_source_hash_and_graph_changes_change_digest(self):
        graph = {"A": [], "B": []}
        original = plan(graph)["graph_sha256"]
        self.assertNotEqual(original, plan({"A": [], "B": ["A"]})["graph_sha256"])
        self.assertNotEqual(original, plan(graph, sizes={"A": 2, "B": 1})["graph_sha256"])
        hashes = {module: "changed" for module in graph}
        self.assertNotEqual(original, ci_plan.make_plan(graph, {"A": 1, "B": 1}, graph, hashes)["graph_sha256"])

    def test_metadata_units_match_all_materialized_families(self):
        def fixture(unit):
            return [("archive", "digest", {f"Sqpack/{unit}.lean": "source", "Roots.txt": "auxiliary"})]
        with mock.patch.object(ci_plan.release, "release_plan", side_effect=fixture) as planner:
            result = ci_plan.required_sources()
        self.assertEqual([call.args[0] for call in planner.call_args_list],
                         ["F", "FCOMMON", "U2G", "U2P", "U2R", "U5"])
        self.assertEqual(set(result),
                         {"Sqpack.F", "Sqpack.FCOMMON", "Sqpack.U2G", "Sqpack.U2P", "Sqpack.U2R", "Sqpack.U5"})

    def test_native_frontier_includes_shared_foundations_and_defers_large_aggregates(self):
        graph = {f"ElevenSquare.Data{i}": [] for i in range(8)}
        graph["ElevenSquare.Foundation"] = list(graph)
        for number in range(3):
            graph[f"ElevenSquare.Certificate{number}"] = ["ElevenSquare.Foundation"]
        graph["ElevenSquare.Aggregate"] = [f"ElevenSquare.Certificate{i}" for i in range(3)]
        graph["ElevenSquare.Public"] = ["ElevenSquare.Aggregate"]
        sizes = {module: 1 for module in graph}
        for number in range(3):
            sizes[f"ElevenSquare.Certificate{number}"] = 3
        with mock.patch.object(ci_plan, "NATIVE_CLOSURE_BYTE_CAP", 15):
            result = plan(graph, generated=set(), sizes=sizes)
        targets = {module for shard in result["shards"] for module in shard["modules"]}
        self.assertEqual(targets, {f"ElevenSquare.Certificate{i}" for i in range(3)})
        self.assertEqual(result["barrier_modules"], ["ElevenSquare.Aggregate"])
        self.assertEqual(result["deferred_native_modules"], ["ElevenSquare.Aggregate", "ElevenSquare.Public"])
        self.assertNotIn("ElevenSquare.Foundation", result["barrier_modules"])
        self.assertEqual(result["native_candidate_module_count"], 14)
        self.assertEqual(result["eligible_native_module_count"], 12)

    def test_native_wrappers_cannot_pull_generated_barriers(self):
        graph = {"Sqpack.Case.S0": [], "Sqpack.Case.Main": ["Sqpack.Case.S0"],
                 "ElevenSquare.Wrapper": ["Sqpack.Case.Main"],
                 "ElevenSquare.Independent": []}
        result = plan(graph, {"Sqpack.Case.S0", "Sqpack.Case.Main"})
        targets = {module for shard in result["shards"] for module in shard["modules"]}
        self.assertEqual(targets, {"Sqpack.Case.S0", "ElevenSquare.Independent"})
        self.assertEqual(set(result["deferred_native_modules"]), {"ElevenSquare.Wrapper"})
        self.assertFalse(closure(graph, targets) & set(result["barrier_modules"]))

    def test_returned_certificates_are_distributed_but_main_stays_in_final_replay(self):
        prefix = "Sqpack.S11Opt.Split.U2R.C1."
        graph = {prefix + "Data": [], prefix + "S0": [prefix + "Data"],
                 prefix + "Main": [prefix + "S0"],
                 "ElevenSquare.Returned": [prefix + "Main"]}
        result = plan(graph, {prefix + name for name in ("Data", "S0", "Main")})
        targets = {module for shard in result["shards"] for module in shard["modules"]}
        self.assertEqual(targets, {prefix + "S0"})
        self.assertEqual(set(result["final_modules"]), {prefix + "Main", "ElevenSquare.Returned"})
        self.assertEqual(closure(graph, targets) | set(result["final_modules"]), set(graph))

    def test_generated_u5_leaves_bypass_native_cap_but_not_aggregation_barriers(self):
        prefix = "ElevenSquare.Tasks.T07.Ext.Gen."
        data = prefix + "P2.Data"
        leaves = {prefix + f"P2.S{i}" for i in range(8)}
        graph = {data: []}
        graph.update({module: [data] for module in leaves})
        graph[prefix + "P2"] = sorted(leaves)
        graph["ElevenSquare.Capture"] = [prefix + "P2"]
        generated = set(graph) - {"ElevenSquare.Capture"}
        sizes = {module: 1 for module in graph}
        sizes[data] = 3
        with mock.patch.object(ci_plan, "NATIVE_CLOSURE_BYTE_CAP", 2):
            result = plan(graph, generated, sizes)
        targets = {module for shard in result["shards"] for module in shard["modules"]}
        self.assertEqual(targets, leaves)
        self.assertEqual(result["barrier_modules"], [prefix + "P2"])
        self.assertEqual(set(result["final_modules"]), {prefix + "P2", "ElevenSquare.Capture"})
        self.assertEqual(closure(graph, targets) | set(result["final_modules"]), set(graph))

    def test_bundles_and_originals_both_remain_in_complete_replay(self):
        original = "Sqpack.S11Opt.F04."
        bundled = "Sqpack.S11Opt.Bundled.F04."
        graph = {original + "Data": [], original + "Cov1": [original + "Data"],
                 bundled + "Leaves000": [original + "Data"],
                 bundled + "Leaves001": [original + "Data"],
                 bundled + "Coverage": [bundled + "Leaves000", bundled + "Leaves001"],
                 bundled + "Final": [bundled + "Coverage"],
                 "ElevenSquare.Baseline": [bundled + "Final"]}
        result = plan(graph, {original + "Data", original + "Cov1"})
        targets = {module for shard in result["shards"] for module in shard["modules"]}
        self.assertEqual(targets, {original + "Cov1", bundled + "Coverage"})
        self.assertEqual(result["generated_module_count"], 6)
        final = set(result["final_modules"])
        self.assertEqual(final, {bundled + "Final", "ElevenSquare.Baseline"})
        covered = closure(graph, targets)
        self.assertFalse(covered & final)
        self.assertEqual(covered | final, set(graph))

        changed = {module: "changed" if module == bundled + "Leaves000" else
                   hashlib.sha256(module.encode()).hexdigest() for module in graph}
        self.assertNotEqual(result["graph_sha256"], ci_plan.make_plan(
            graph, {module: 1 for module in graph},
            {original + "Data", original + "Cov1"}, changed)["graph_sha256"])

    def test_source_scan_checks_pins_and_missing_imports(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            (root / "ElevenSquare.lean").write_text("")
            source = root / "Sqpack.lean"
            source.write_text("-- import Sqpack.Absent\n")
            digest = ci_plan.release.sha256_file(source)
            graph, _, _ = ci_plan.read_graph(root, {"Sqpack": digest})
            self.assertEqual(graph["Sqpack"], [])
            with self.assertRaisesRegex(ValueError, "hash mismatch"):
                ci_plan.read_graph(root, {"Sqpack": "wrong"})
            source.write_text("import Sqpack.Absent\n")
            with self.assertRaisesRegex(ValueError, "Missing local import"):
                ci_plan.read_graph(root, {})
            source.unlink()
            with self.assertRaisesRegex(ValueError, "Missing or nonregular source"):
                ci_plan.read_graph(root, {})


if __name__ == "__main__":
    unittest.main()
