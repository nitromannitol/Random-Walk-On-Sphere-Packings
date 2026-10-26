import Lean
import LeanExport.Basic
import LeanExport.Parse
import Lake.Check.Util

/-!
# Read-only exported ABI diagnostic

Compares independently exported environments using the same `ConstantInfo` equality and
closure traversal as the pinned Comparator. This executable adds no mathematical declarations
and changes neither environment. Its output is diagnostic evidence, not an acceptance verdict.
-/

set_option autoImplicit false

open Lean LeanExport

private def loadExport (path : String) : IO ExportedEnv := do
  let handle ← IO.FS.Handle.mk path .read
  parseStream (.ofHandle handle)

private def describe (label : String) (info : ConstantInfo) : IO Unit := do
  IO.println s!"{label}: name={info.name}; levels={info.levelParams}"
  IO.println s!"{label}.type={reprStr info.type}"
  IO.println s!"{label}.value={reprStr (info.value? (allowOpaque := true))}"
  if let .defnInfo d := info then
    let hints := match d.hints with
      | .opaque => "opaque"
      | .abbrev => "abbrev"
      | .regular n => s!"regular {n}"
    IO.println s!"{label}.hints={hints}"
    IO.println s!"{label}.safety={reprStr d.safety}; all={d.all}"
  IO.println s!"{label}.typeDependencies={info.type.getUsedConstants}"
  if let some value := info.value? (allowOpaque := true) then
    IO.println s!"{label}.valueDependencies={value.getUsedConstants}"

private def compareFields (name : Name) (a b : ConstantInfo) : IO Unit := do
  IO.println s!"COMPARE {name}: ConstantInfo={a == b}; type={a.type == b.type}"
  IO.println s!"levels={a.levelParams == b.levelParams}; value={a.value? true == b.value? true}"
  if let (.defnInfo x, .defnInfo y) := (a, b) then
    IO.println s!"hints={x.hints == y.hints}; safety={x.safety == y.safety}; all={x.all == y.all}"

/-- Read two pinned leanexport NDJSON files and inspect one dependency closure. -/
def main (args : List String) : IO Unit := do
  let [left, right] := args
    | throw <| IO.userError "usage: CompareExports.lean CHALLENGE.ndjson SOLUTION.ndjson"
  let a ← loadExport left
  let b ← loadExport right
  let root := `BouRabeeGwynne.cylinderCoordinates
  let focused := #[root, `BouRabeeGwynne.Euc, `EuclideanSpace, `PiLp,
    `WithLp, `WithLp.toLp, `WithLp.ofLp, `Option.casesOn, `Option.rec]
  for name in focused do
    match a.constMap[name]?, b.constMap[name]? with
    | some x, some y =>
      compareFields name x y
      describe "challenge" x
      describe "solution" y
    | _, _ => IO.println s!"MISSING {name}: challenge={a.constMap.contains name}; \
        solution={b.constMap.contains name}"
  let pending ← IO.mkRef #[root]
  let mut seen : Std.HashSet Name := {}
  let mut index := 0
  let mut mismatches := 0
  while index < (← pending.get).size do
    let name := (← pending.get)[index]!
    index := index + 1
    if seen.contains name then continue
    seen := seen.insert name
    match a.constMap[name]?, b.constMap[name]? with
    | some x, some y =>
      if x != y then
        mismatches := mismatches + 1
        if mismatches ≤ 40 then compareFields name x y
      Lake.Check.runForUsedConsts x fun n => pending.modify (·.push n)
      Lake.Check.runForUsedConsts y fun n => pending.modify (·.push n)
    | _, _ =>
      mismatches := mismatches + 1
      if mismatches ≤ 40 then IO.println s!"CLOSURE MISSING {name}"
  IO.println s!"CLOSURE checked={seen.size}; mismatches={mismatches}"
