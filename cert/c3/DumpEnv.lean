/-
cert/c3/DumpEnv.lean — dump, for every constant defined in a `Zeta5.*` module, its kind, its
defining module, the structural hash of its TYPE and (for definitions) of its VALUE.

Run as:  LEAN_PATH=<lib dirs> lean --run DumpEnv.lean <out.tsv> <Module> [<Module> ...]
Theorems contribute only their type (proofs are expected to change); definitions, opaques,
inductives, constructors and recursors contribute everything that determines their meaning.
-/
import Lean
open Lean

def kindOf : ConstantInfo → String
  | .axiomInfo _ => "axiom" | .defnInfo _ => "def" | .thmInfo _ => "thm"
  | .opaqueInfo _ => "opaque" | .quotInfo _ => "quot" | .inductInfo _ => "induct"
  | .ctorInfo _ => "ctor" | .recInfo _ => "rec"

def valHash : ConstantInfo → String
  | .defnInfo v => toString v.value.hash
  | .opaqueInfo v => toString v.value.hash
  | .inductInfo v => toString (hash (v.ctors.map toString, v.numParams, v.numIndices))
  | .recInfo v => toString (hash (v.rules.map (fun r => r.rhs.hash)))
  | _ => "-"

unsafe def main (args : List String) : IO Unit := do
  let out :: mods := args | throw (IO.userError "usage")
  initSearchPath (← findSysroot)
  let env ← importModules (mods.toArray.map fun m => { module := m.toName }) {} 0
    (loadExts := false)
  let mut lines : Array String := #[]
  for (n, ci) in env.constants.map₁.toList do
    match env.getModuleIdxFor? n with
    | some i =>
      let m := env.header.moduleNames[i.toNat]!
      if (`Zeta5).isPrefixOf m then
        lines := lines.push s!"{n}\t{kindOf ci}\t{m}\t{ci.levelParams}\t{ci.type.hash}\t{valHash ci}"
    | none => pure ()
  lines := lines.qsort (· < ·)
  IO.FS.writeFile out ("\n".intercalate lines.toList ++ "\n")
  IO.println s!"wrote {lines.size} constants from {mods.length} root module(s) to {out}"
