# Comparator runs

The official `leanprover/comparator` was run on every pair in this directory on a local machine, on
the Lean sources published here (every module in the import closure of the six pairs is
byte-identical to the checkout of the run), with the Lean kernel and the independent `nanoda`
kernel both enabled (every committed `comparator.json` sets `"enable_nanoda": true`).  The
comparator workflow repeats the checks on GitHub-hosted runners.

| Tool | Revision |
|---|---|
| leanprover/comparator | `575674928e239f5bc452aab72d1dd7b0f1326494` |
| leanprover/lean4export | `v4.34.0-rc2` (`cacf989bd75f608700820f6afc595f32e7a99a4d`) |
| Zouuup/landrun | `811cfff51ceaf3d9843708aa6d22e9b84ccac8b4` |
| ammkrn/nanoda_lib | `6ae1f0cd962f081f6c423454c5da729d841236a7` |

Lean `v4.34.0-rc2`, Mathlib `a4c8ef0a69f52ec80525d5086bb3542f4660faaf`.

A pass means the comparator printed `nanoda kernel accepts the solution`, `Lean default kernel
accepts the solution` and `Your solution is okay!`: the solution proves a theorem whose statement and
full dependency closure match the challenge's, using only the permitted axioms.  The times are wall
clock for the whole comparator run (export of both modules, statement comparison, both kernels),
including any wait for the build lock that this machine shares with other projects.

## `TheoremA`

| Check | Result |
|---|---|
| Lean and nanoda kernels | passed (299 s) |

## `TheoremB`

| Check | Result |
|---|---|
| Lean and nanoda kernels | passed (266 s) |

## `Prop11`

| Check | Result |
|---|---|
| Lean and nanoda kernels | passed (95 s) |

## `Prop11TheoremsAB`

| Check | Result |
|---|---|
| Lean and nanoda kernels | passed (272 s) |

## `Theorem61`

| Check | Result |
|---|---|
| Lean and nanoda kernels | passed (273 s) |

## `Theorem41`

| Check | Result |
|---|---|
| Lean and nanoda kernels | passed (227 s) |

To reproduce one pair, from the repository root:

```
COMPARATOR_LANDRUN=<landrun> COMPARATOR_LEAN4EXPORT=<lean4export> COMPARATOR_NANODA=<nanoda_bin> \
  lake env <comparator>/.lake/build/bin/comparator SpherePackingsAudit/<Pair>/comparator.json
```
