# Assumptions

**None.**  No result that the paper cites is taken as a hypothesis or as an axiom: every registered
statement in `ledger/manifest.yaml` is proved, and its axiom closure is exactly Lean's standard
axioms `propext`, `Classical.choice` and `Quot.sound` (`python3 tools/check_axioms.py`).

The paper cites results it does not prove in three places, none of which is used here:

| paper | cited result | status |
|---|---|---|
| Remark 1.2 (`remark:gmc`) | Berestycki, Theorem 3.26 (GMC mass bounds) | the remark is not formalized; Proposition 1.1 takes the mass bounds (1.4) as its hypothesis, as printed (on a neighbourhood of `closure U`) |
| Section 1.1, the curve metric (1.2) | Aizenman–Burchard, Section 2 | the metric is defined directly (Fréchet distance over increasing homeomorphisms of `[0,1]`) |
| proof of Theorem 4.1 | a Brownian exit estimate near a Lipschitz boundary (a source comment points to Mörters–Peres, Lemma 3.11) | not used: leobon12's proof of Theorem A, on which the proof of Theorem 4.1 is built, proves the needed Brownian estimates |

Assumption D is a hypothesis of Theorem 4.1 and of Proposition 4.2, as in the paper; it is formalized as
printed (`SpherePackings.AssumptionD`).
