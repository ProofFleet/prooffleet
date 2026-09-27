import Conjectures.C0002_erdos_discrepancy.src.ErdosDiscrepancy

/-!
# Measuring the declaration closure of the Erdős discrepancy theorem

`import` closure overstates what a proof uses: the EDP wrapper imports the stable surface
aggregators, which pull in most of `MoltResearch/`. This script measures the *declaration*
closure instead: every constant reachable from `MoltResearch.erdos_discrepancy` through the
constants its type and proof mention, which is what the kernel (and Palomar's exporter) actually
depends on. It prints one JSON object:

* `constants`: size of the closure, by root package (`Mathlib`, `Init`, `MoltResearch`, …);
* `projectModulesUsed`: every `MoltResearch.*` / `Conjectures.*` module contributing at least one
  constant, with the number of constants and of source lines those declarations span;
* `projectModulesImportedButUnused`: modules in the import closure contributing nothing.

Run after building the EDP closure (`lake build Conjectures`):

    lake env lean scripts/edp_dependency_closure.lean

It is a measurement, not a gate, and is not built by CI.
-/

open Lean Elab Command

/-- Every constant reachable from `root` through the constants mentioned by types and values. -/
def constantClosure (env : Environment) (root : Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut todo : Array Name := #[root]
  while !todo.isEmpty do
    let name := todo.back!
    todo := todo.pop
    unless seen.contains name do
      seen := seen.insert name
      if let some info := env.find? name then
        for used in info.getUsedConstantsAsSet do
          unless seen.contains used do
            todo := todo.push used
  return seen

def isProjectModule (module : Name) : Bool :=
  module.getRoot == `MoltResearch || module.getRoot == `Conjectures

#eval show CommandElabM Unit from do
  let env ← getEnv
  let root := `MoltResearch.erdos_discrepancy
  let closure := constantClosure env root
  let mut byPackage : Std.HashMap String Nat := {}
  let mut constantsPerModule : Std.HashMap Name Nat := {}
  let mut linesPerModule : Std.HashMap Name Nat := {}
  for name in closure do
    let module? := (env.getModuleIdxFor? name).map fun idx => env.header.moduleNames[idx.toNat]!
    let package := (module?.map (·.getRoot.toString)).getD "(this file)"
    byPackage := byPackage.insert package (byPackage.getD package 0 + 1)
    if let some module := module? then
      if isProjectModule module then
        constantsPerModule := constantsPerModule.insert module (constantsPerModule.getD module 0 + 1)
        if !name.isInternal then
          if let some ranges ← liftCoreM (findDeclarationRanges? name) then
            let span := ranges.range.endPos.line - ranges.range.pos.line + 1
            linesPerModule := linesPerModule.insert module (linesPerModule.getD module 0 + span)
  let imported := env.header.moduleNames.filter isProjectModule
  let unused := imported.filter (!constantsPerModule.contains ·)
  let used := (constantsPerModule.toArray.qsort (·.1.toString < ·.1.toString)).map fun (m, n) =>
    Json.mkObj [("module", toJson m.toString), ("constants", toJson n),
      ("declarationLines", toJson (linesPerModule.getD m 0))]
  let packages := (byPackage.toArray.qsort (·.2 > ·.2)).map fun (p, n) =>
    Json.mkObj [("package", toJson p), ("constants", toJson n)]
  let report := Json.mkObj [
    ("root", toJson root.toString),
    ("constants", Json.mkObj [("total", toJson closure.size), ("byPackage", Json.arr packages)]),
    ("projectModulesImported", toJson imported.size),
    ("projectModulesUsed", Json.arr used),
    ("projectModulesImportedButUnused",
      toJson ((unused.qsort (·.toString < ·.toString)).map (·.toString)))]
  logInfo m!"{report.pretty}"
