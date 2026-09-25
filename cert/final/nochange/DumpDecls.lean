/-
cert/final/nochange/DumpDecls.lean — per-declaration fingerprint dump, for the
"no statement changed" check between main (9ce1320) and eq614 HEAD.

For every constant whose DEFINING MODULE is `Zeta5` or `Zeta5.*` (so private names,
auxiliary declarations and anything outside the `Zeta5` namespace are included), writes one
tab-separated line:

  name  kind  module  levelParams  typeHash32  valHash32  typeSer  valSer  extra

* typeHash32 / valHash32 : Lean's structural `Expr.hash` (as in cert/c3/DumpEnv.lean);
* typeSer / valSer : a complete serialisation of the Expr as a DAG table (every node:
  constructor tag, binder name and binder info, universe levels, literals, mdata keys,
  projection data); `compare.py` replaces these by their SHA-256, so equality of the
  digests is (up to SHA-256 collisions) syntactic equality of the stored Exprs;
* the "value" is: the body for `def`/`opaque`; the rule right-hand sides for `rec`;
  "-" for theorems (proofs may change), axioms, quot;
* extra : kind-specific metadata that determines meaning (definition safety and hints,
  inductive shape, constructor index/fields, recursor shape).

Run:  lake env lean --run cert/final/nochange/DumpDecls.lean <out.tsv> Zeta5
-/
import Lean
open Lean

namespace DD

structure S where
  ids : Std.HashMap Expr Nat := {}
  out : Array String := #[]

partial def ser (e : Expr) : StateM S Nat := do
  if let some i := (← get).ids.get? e then return i
  let s ← match e with
    | .bvar i => pure s!"B{i}"
    | .fvar f => pure s!"F{f.name}"
    | .mvar m => pure s!"M{m.name}"
    | .sort l => pure s!"S({l})"
    | .const n ls => pure s!"C{n}{ls}"
    | .app f a => do let x ← ser f; let y ← ser a; pure s!"A{x},{y}"
    | .lam n t b bi => do
        let x ← ser t; let y ← ser b; pure s!"L{n}:{repr bi}:{x},{y}"
    | .forallE n t b bi => do
        let x ← ser t; let y ← ser b; pure s!"P{n}:{repr bi}:{x},{y}"
    | .letE n t v b nd => do
        let x ← ser t; let y ← ser v; let z ← ser b; pure s!"E{n}:{nd}:{x},{y},{z}"
    | .lit (.natVal v) => pure s!"N{v}"
    | .lit (.strVal v) => pure s!"T{repr v}"
    | .mdata d b => do
        let x ← ser b; pure s!"D{d.entries.map (·.1)}:{x}"
    | .proj sn i b => do let x ← ser b; pure s!"J{sn}.{i}:{x}"
  let st ← get
  let i := st.out.size
  set { st with ids := st.ids.insert e i, out := st.out.push s }
  return i

def serialize (e : Expr) : String :=
  let (_, st) := (ser e).run {}
  ";".intercalate st.out.toList

def serializeMany (es : List Expr) : String :=
  "|".intercalate (es.map serialize)

def kindOf : ConstantInfo → String
  | .axiomInfo _ => "axiom" | .defnInfo _ => "def" | .thmInfo _ => "thm"
  | .opaqueInfo _ => "opaque" | .quotInfo _ => "quot" | .inductInfo _ => "induct"
  | .ctorInfo _ => "ctor" | .recInfo _ => "rec"

def hintsStr : ReducibilityHints → String
  | .opaque => "opaque" | .abbrev => "abbrev" | .regular h => s!"regular{h}"

def safetyStr : DefinitionSafety → String
  | .unsafe => "unsafe" | .safe => "safe" | .partial => "partial"

def valHash : ConstantInfo → String
  | .defnInfo v => toString v.value.hash
  | .opaqueInfo v => toString v.value.hash
  | .recInfo v => toString (hash (v.rules.map (fun r => r.rhs.hash)))
  | _ => "-"

def valSer : ConstantInfo → String
  | .defnInfo v => serialize v.value
  | .opaqueInfo v => serialize v.value
  | .recInfo v => serializeMany (v.rules.map (·.rhs))
  | _ => "-"

def extra : ConstantInfo → String
  | .defnInfo v => s!"safety={safetyStr v.safety} hints={hintsStr v.hints} all={v.all}"
  | .opaqueInfo v => s!"unsafe={v.isUnsafe} all={v.all}"
  | .axiomInfo v => s!"unsafe={v.isUnsafe}"
  | .thmInfo v => s!"all={v.all}"
  | .inductInfo v => s!"params={v.numParams} idx={v.numIndices} all={v.all} ctors={v.ctors} nested={v.numNested} rec={v.isRec} unsafe={v.isUnsafe} refl={v.isReflexive}"
  | .ctorInfo v => s!"induct={v.induct} cidx={v.cidx} params={v.numParams} fields={v.numFields} unsafe={v.isUnsafe}"
  | .recInfo v => s!"all={v.all} params={v.numParams} idx={v.numIndices} motives={v.numMotives} minors={v.numMinors} k={v.k} unsafe={v.isUnsafe} rules={v.rules.map (fun r => (r.ctor, r.nfields))}"
  | .quotInfo _ => "-"

end DD

open DD in
unsafe def main (args : List String) : IO Unit := do
  let out :: mods := args | throw (IO.userError "usage: <out.tsv> <Module>...")
  initSearchPath (← findSysroot)
  let env ← importModules (mods.toArray.map fun m => { module := m.toName }) {} 0
    (loadExts := false)
  let mut lines : Array String := #[]
  let mut nAll := 0
  for (n, ci) in env.constants.map₁.toList do
    nAll := nAll + 1
    match env.getModuleIdxFor? n with
    | some i =>
      let m := env.header.moduleNames[i.toNat]!
      if (`Zeta5).isPrefixOf m then
        lines := lines.push
          s!"{n}\t{kindOf ci}\t{m}\t{ci.levelParams}\t{ci.type.hash}\t{valHash ci}\t{serialize ci.type}\t{valSer ci}\t{extra ci}"
    | none => pure ()
  -- constants in the `Zeta5` namespace defined OUTSIDE the Zeta5 modules (should be none)
  let mut foreign : Array String := #[]
  for (n, _) in env.constants.map₁.toList do
    if (`Zeta5).isPrefixOf n then
      match env.getModuleIdxFor? n with
      | some i =>
        let m := env.header.moduleNames[i.toNat]!
        if !(`Zeta5).isPrefixOf m then foreign := foreign.push s!"{n} in {m}"
      | none => foreign := foreign.push s!"{n} (no module)"
  lines := lines.qsort (· < ·)
  IO.FS.writeFile out ("\n".intercalate lines.toList ++ "\n")
  IO.println s!"environment constants: {nAll}; modules: {env.header.moduleNames.size}"
  IO.println s!"wrote {lines.size} constants from Zeta5 modules to {out}"
  IO.println s!"Zeta5-namespace constants defined outside Zeta5 modules: {foreign.size} {foreign}"
