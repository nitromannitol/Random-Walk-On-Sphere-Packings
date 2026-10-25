module

public import Lean

@[expose] public section
/-!
Dump the project declarations needed to state given theorems, with their source ranges.

Usage (from the repository root), with `MODULES` and `ROOTS` comma-separated lists:

    lake env lean --run tools/audit/DumpVocabulary.lean <MODULES> <ROOTS> <out.jsonl>

The needed declarations are the dependency closure of the roots' statements (for a definition
root, its body too) within the project (`BouRabeeGwynne`, `SpherePackings`), through the types
and values of the declarations reached.  A needed auxiliary constant (`foo._proof_1`, a
projection, ...) has no source range of its own; the declaration that generated it is then
needed, with its own closure.  For every declaration of each module containing a needed one,
one JSON line `{name, module, start, stop, needed}` is written.
-/
open Lean

def isProject (m : Name) : Bool :=
  (`BouRabeeGwynne).isPrefixOf m || (`SpherePackings).isPrefixOf m

def main (args : List String) : IO Unit := do
  let [mods, roots, out] := args | throw <| IO.userError "usage: MODULES ROOTS OUT"
  let mods := (mods.splitOn ",").map String.toName
  let roots := (roots.splitOn ",").map String.toName
  initSearchPath (← findSysroot)
  let env ← importModules (mods.map fun m => { module := m }).toArray {}
  let moduleNames := env.header.moduleNames
  let modOf (n : Name) : Option Name := (env.getModuleIdxFor? n).map fun i => moduleNames[i.toNat]!
  let ctx : Core.Context := { fileName := "", fileMap := default }
  let rangeOf (n : Name) : IO (Option DeclarationRanges) := do
    let (r, _) ← (findDeclarationRanges? n : CoreM _).toIO ctx { env }
    return r
  let mut pending : Array Name := #[]
  for r in roots do
    let some ci := env.find? r | throw <| IO.userError s!"unknown root {r}"
    pending := pending ++ ci.type.getUsedConstants
    if let .defnInfo d := ci then pending := pending ++ d.value.getUsedConstants
  let mut seen : NameSet := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    if seen.contains n then continue
    let some ci := env.find? n | continue
    let some m := modOf n | continue
    unless isProject m do continue
    seen := seen.insert n
    pending := pending ++ ci.type.getUsedConstants
    if let some v := ci.value? (allowOpaque := true) then
      pending := pending ++ v.getUsedConstants
    if let .inductInfo ii := ci then
      pending := pending ++ ii.ctors.toArray
    if let .ctorInfo c := ci then
      pending := pending.push c.induct
    if (← rangeOf n).isNone then
      let mut p := n.getPrefix
      while !p.isAnonymous do
        if (← rangeOf p).isSome then
          pending := pending.push p
          break
        p := p.getPrefix
  let mut neededMods : NameSet := {}
  for n in seen.toList do
    if let some m := modOf n then neededMods := neededMods.insert m
  let h ← IO.FS.Handle.mk out .write
  for (n, _) in env.constants.toList do
    let some m := modOf n | continue
    unless neededMods.contains m do continue
    if let some rg ← rangeOf n then
      let j := Json.mkObj [("name", toString n), ("module", toString m),
        ("start", rg.range.pos.line), ("stop", rg.range.endPos.line),
        ("needed", seen.contains n)]
      h.putStrLn j.compress
