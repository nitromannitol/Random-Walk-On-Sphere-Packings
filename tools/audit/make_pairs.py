#!/usr/bin/env python3
"""Write the comparator pairs `SpherePackingsAudit/<Pair>/{Challenge,Solution}.lean, comparator.json`.

Each challenge imports only Mathlib (through the vocabulary modules) and restates one main result
with the bytes of its statement in the repository; each solution imports the repository and proves
it by `exact` of the corresponding theorem.
"""
import json
import pathlib

ROOT = pathlib.Path(__file__).resolve().parents[2]
V = "SpherePackingsAudit.Vocabulary."


def block(path: str, start: str, stop: str) -> str:
    text = (ROOT / path).read_text(encoding="utf-8")
    return text.split(start, 1)[1].split(stop, 1)[0].rstrip()


def main_statement(name: str) -> str:
    text = (ROOT / "SpherePackings/MainTheorems.lean").read_text(encoding="utf-8")
    i = text.index(f"theorem SpherePackings.{name} ")
    j = text.index(":= by\n", i)
    return text[i + len(f"theorem SpherePackings.{name} "):j].rstrip()


MAIN_OPENS = ("open MeasureTheory Metric Filter Set BouRabeeGwynne SpherePackings SpherePackings.Voronoi\n"
              "open scoped ENNReal NNReal Topology\n")

A = block("BouRabeeGwynne/TheoremAStatement.lean", "def TheoremAStatement : Prop :=\n", "\nend BouRabeeGwynne")
BA = block("BouRabeeGwynne/TheoremBStatement.lean", "def TheoremBPartAStatement : Prop :=\n", "\n\n")
BB = block("BouRabeeGwynne/TheoremBStatement.lean", "def TheoremBPartBStatement : Prop :=\n", "\n\n")


def indent(text: str, n: int = 2) -> str:
    return "\n".join((" " * n + l) if l else l for l in text.split("\n"))


PAIRS = [
    {"dir": "TheoremA", "name": "theoremA", "title": "Theorem A (`theorem:convergence-of-rw-trace`)",
     "vocab": ["BouRabeeGwynne.StoppedCurveLaws", "BouRabeeGwynne.Approximation", "BouRabeeGwynne.LipschitzDomain"],
     "opens": "open scoped ENNReal Topology\nopen MeasureTheory BouRabeeGwynne\n",
     "stmt": f":\n{A}", "solution_import": "SpherePackings.MainTheorems",
     "proof": "SpherePackings.theorem_A"},
    {"dir": "TheoremB", "name": "theoremB",
     "title": "Theorem B (`theorem:convergence-of-the-dirichlet-problem`), both alternatives",
     "vocab": ["BouRabeeGwynne.TheoremBStatement"],
     "opens": "open scoped Topology ENNReal\nopen BouRabeeGwynne\n",
     "stmt": f":\n  ({BA.strip()}) ∧\n  ({BB.strip()})", "solution_import": "SpherePackings.MainTheorems",
     "proof": "⟨SpherePackings.theorem_B_a, SpherePackings.theorem_B_b⟩"},
    {"dir": "Prop11", "name": "prop_1_1", "title": "Proposition 1.1 (`prop:min-max-edge-length`), cell bounds",
     "vocab": ["SpherePackings.Support.Voronoi.PoissonCells", "SpherePackings.Support.Poisson.Basic",
               "SpherePackings.Support.Voronoi.Basic"],
     "opens": "open MeasureTheory Metric Filter Set SpherePackings SpherePackings.Voronoi\nopen scoped ENNReal NNReal Topology\n", "stmt": main_statement("prop_1_1"), "main": "prop_1_1",
     "solution_import": "SpherePackings.MainTheorems"},
    {"dir": "Prop11TheoremsAB", "name": "prop_1_1_theorems_A_B",
     "title": "Proposition 1.1 (`prop:min-max-edge-length`), Theorems A and B for Poisson–Voronoi tilings",
     "vocab": ["SpherePackings.Support.Voronoi.PoissonTilings", "SpherePackings.Support.Voronoi.PoissonCells",
               "BouRabeeGwynne.TheoremBStatement", "BouRabeeGwynne.StoppedCurveLaws"],
     "opens": MAIN_OPENS, "stmt": main_statement("prop_1_1_theorems_A_B"), "main": "prop_1_1_theorems_A_B",
     "solution_import": "SpherePackings.MainTheorems"},
    {"dir": "Theorem61", "name": "theorem_6_1", "title": "Theorem 6.1 (`theorem:counter-example`)",
     "vocab": ["SpherePackings.Support.Counterexample.WalkLaw"],
     "opens": "open MeasureTheory Metric Filter Set BouRabeeGwynne SpherePackings\nopen scoped ENNReal NNReal Topology\n", "stmt": main_statement("theorem_6_1"), "main": "theorem_6_1",
     "solution_import": "SpherePackings.MainTheorems"},
    {"dir": "Theorem41", "name": "theorem_4_1", "title": "Theorem 4.1 (`theorem:general-clt`)",
     "vocab": ["SpherePackings.Support.Section4General.StoppedWalkLaw",
               "SpherePackings.Support.Section4General.AssumptionD", "BouRabeeGwynne.LipschitzDomain"],
     "opens": "open MeasureTheory Metric Filter Set BouRabeeGwynne SpherePackings\nopen scoped ENNReal NNReal Topology\n",
     "stmt": main_statement("theorem_4_1"), "main": "theorem_4_1",
     "solution_import": "SpherePackings.MainTheorems"},
]


def args_of(main: str) -> str:
    text = (ROOT / "SpherePackings/MainTheorems.lean").read_text(encoding="utf-8")
    i = text.index(f"theorem SpherePackings.{main} ")
    proof = text[text.index(":= by\n", i) + 6:].split("\n", 1)[0].strip()
    return proof.replace("exact ", "", 1)


def main() -> None:
    for p in PAIRS:
        d = ROOT / "SpherePackingsAudit" / p["dir"]
        d.mkdir(parents=True, exist_ok=True)
        imports = "\n".join(f"import {V}{m}" for m in p["vocab"])
        stmt = p["stmt"]
        if "main" in p:
            proof = args_of(p["main"]).replace("SpherePackings.Frozen.", "SpherePackings.Frozen.")
            # The solution proves the challenge from the main theorem.
            main_args = proof.split(" ", 1)
            proof = f"SpherePackings.{p['main']}" + (" " + main_args[1] if len(main_args) > 1 else "")
        else:
            proof = p["proof"]
        challenge = (f"{imports}\n\n/-!\n# Comparator challenge: {p['title']}\n\n"
                     "This file imports only Mathlib and the vocabulary modules of `SpherePackingsAudit/Vocabulary/`,\n"
                     "which copy verbatim, under their repository names, the repository declarations needed to read the\n"
                     "statement (`python3 tools/check_vocabulary.py`).  It ends with one `sorry`, the proof being checked.\n-/\n\n"
                     f"namespace SpherePackingsAudit\n\n{p['opens']}\n"
                     f"/-- {p['title']}. -/\ntheorem {p['name']} {stmt.lstrip() if not stmt.startswith(':') else stmt} := by\n  sorry\n\nend SpherePackingsAudit\n")
        solution = (f"import {p['solution_import']}\n\n/-!\n# Solution: {p['title']}\n\n"
                    "Proves the challenge statement from the repository's main theorem.  The vocabulary constants are\n"
                    "the repository's own declarations, of which the challenge's vocabulary modules are verbatim copies.\n-/\n\n"
                    f"namespace SpherePackingsAudit\n\n{p['opens']}\n"
                    f"/-- {p['title']}. -/\ntheorem {p['name']} {stmt.lstrip() if not stmt.startswith(':') else stmt} :=\n  {proof}\n\nend SpherePackingsAudit\n")
        (d / "Challenge.lean").write_text(challenge, encoding="utf-8")
        (d / "Solution.lean").write_text(solution, encoding="utf-8")
        cfg = {"challenge_module": f"SpherePackingsAudit.{p['dir']}.Challenge",
               "solution_module": f"SpherePackingsAudit.{p['dir']}.Solution",
               "theorem_names": [f"SpherePackingsAudit.{p['name']}"], "definition_names": [],
               "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"], "enable_nanoda": True}
        (d / "comparator.json").write_text(json.dumps(cfg, indent=2) + "\n")
        print(d.relative_to(ROOT))


if __name__ == "__main__":
    main()
