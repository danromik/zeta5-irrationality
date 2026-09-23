/-
cert/C3Walker.lean — independent dependency walker (certification of 2026-09-23; report in
docs/CERTIFICATION.md).

It shares no code with `Zeta5/Audit.lean` or with the walkers of earlier certification passes
(which are not published), and it is built differently:

  * the `Expr` traversal is ITERATIVE (explicit stack, no recursion), written from the `Expr`
    constructors, never `Expr.getUsedConstants` / `foldConsts`; shared sub-terms are visited
    once through a structural `Std.HashSet Expr`;
  * the constant walk is a BREADTH-FIRST worklist that records, for every constant reached, the
    constant it was first reached from — so each `sorry` leaf and each project axiom is printed
    with a SHORTEST provenance chain from the root, which a reader can check by hand;
  * it matches on the `ConstantInfo` constructor and NEVER calls `ConstantInfo.value?`
    (which returns `none` for theorems in Lean 4.34);
  * the successor relation is deliberately GENEROUS (a superset of
    `Lean.CollectAxioms.collect`): axiom types, `.proj` structure names, the `all` field of
    inductives and recursors, recursor rule right-hand sides and a constructor's inductive are
    all followed.  Its axiom set is compared with `Lean.collectAxioms` on every target;
  * it carries its OWN positive controls: a `sorry`ed lemma and a fresh `axiom` declared in this
    file, each used two levels down, must be found, with the right chain.

Run from the repository root, after `lake build` (about 8 minutes):
  lake env lean cert/C3Walker.lean
Expected output: cert/c3/C3Walker.out.
-/
import Zeta5

open Lean Elab Command

namespace C3

/-- All constant names occurring in `e` — iterative, explicit stack.  `.proj` contributes its
structure name as well (generous). -/
def constsOf (e : Expr) : Std.HashSet Name := Id.run do
  let mut seen : Std.HashSet Expr := {}
  let mut out : Std.HashSet Name := {}
  let mut stack : Array Expr := #[e]
  let mut fuel := 100000000
  while fuel > 0 do
    fuel := fuel - 1
    match stack.back? with
    | none => break
    | some x =>
      stack := stack.pop
      if seen.contains x then continue
      seen := seen.insert x
      match x with
      | .const n _ => out := out.insert n
      | .app f a => stack := (stack.push f).push a
      | .lam _ t b _ => stack := (stack.push t).push b
      | .forallE _ t b _ => stack := (stack.push t).push b
      | .letE _ t v b _ => stack := ((stack.push t).push v).push b
      | .mdata _ b => stack := stack.push b
      | .proj s _ b => out := out.insert s; stack := stack.push b
      | .bvar _ | .fvar _ | .mvar _ | .sort _ | .lit _ => pure ()
  return out

/-- Direct successors of a constant (generous). -/
def succs (ci : ConstantInfo) : Std.HashSet Name :=
  match ci with
  | .axiomInfo v => constsOf v.type
  | .defnInfo v => (constsOf v.type).union (constsOf v.value)
  | .thmInfo v => (constsOf v.type).union (constsOf v.value)
  | .opaqueInfo v => (constsOf v.type).union (constsOf v.value)
  | .quotInfo v => constsOf v.type
  | .inductInfo v => ((constsOf v.type).insertMany v.ctors).insertMany v.all
  | .ctorInfo v => (constsOf v.type).insert v.induct
  | .recInfo v =>
      v.rules.foldl (fun s r => s.union (constsOf r.rhs)) ((constsOf v.type).insertMany v.all)

structure Cone where
  parent : Std.HashMap Name Name := {}
  order : Array Name := #[]
  axioms : Array Name := #[]
  sorryLeaves : Array Name := #[]
  missing : Array Name := #[]

/-- Breadth-first walk from `root`. -/
def walk (env : Environment) (root : Name) : Cone := Id.run do
  let mut c : Cone := {}
  c := { c with parent := c.parent.insert root root, order := #[root] }
  let mut i := 0
  while h : i < c.order.size do
    let n := c.order[i]
    i := i + 1
    match env.find? n with
    | none => c := { c with missing := c.missing.push n }
    | some ci =>
      if ci matches .axiomInfo _ then c := { c with axioms := c.axioms.push n }
      let ss := succs ci
      -- a `sorry` leaf: `sorryAx` occurs directly in this constant's own type or value
      if ss.contains ``sorryAx && n != ``sorryAx then
        c := { c with sorryLeaves := c.sorryLeaves.push n }
      for s in ss.toArray.qsort (fun a b => a.toString < b.toString) do
        unless c.parent.contains s do
          c := { c with parent := c.parent.insert s n, order := c.order.push s }
  return c

/-- The chain root → … → n. -/
def chain (c : Cone) (n : Name) : List Name := Id.run do
  let mut out := [n]
  let mut cur := n
  for _ in [0:10000] do
    match c.parent.get? cur with
    | some p => if p == cur then break else out := p :: out; cur := p
    | none => break
  return out

def sortN (a : Array Name) : Array Name := a.qsort (fun x y => x.toString < y.toString)

/-- Keep only the `Zeta5.*` (and control) names of a chain, to keep it readable. -/
def showChain (l : List Name) : String :=
  let keep := l.filter (fun n => (`Zeta5).isPrefixOf n || (`C3ctl).isPrefixOf n
    || n == ``sorryAx || n.getRoot == `Zeta5)
  " → ".intercalate (keep.map toString) ++ s!"   [{l.length} links]"

end C3

/-- `#c3 f` : independent cone report with provenance chains, and the comparison with
`Lean.collectAxioms`. -/
elab "#c3 " i:ident : command => do
  let env ← getEnv
  let t := i.getId
  unless env.contains t do
    logError s!"#c3: unknown constant {t}"
    return
  let c := C3.walk env t
  let official ← liftCoreM (Lean.collectAxioms t)
  let mine := C3.sortN c.axioms
  let off := C3.sortN official
  let verdict := if mine == off then "AGREE" else s!"*** DISAGREE *** collectAxioms={off}"
  let mut msg := s!"=== C3 {t}\n  constants reached : {c.order.size}   (missing from env: {c.missing.size})\n  axioms ({mine.size}) : {mine.toList}\n  vs Lean.collectAxioms : {verdict}\n  sorry leaves ({c.sorryLeaves.size}) : {(C3.sortN c.sorryLeaves).toList}"
  for s in C3.sortN c.sorryLeaves do
    msg := msg ++ s!"\n    chain to sorry leaf  : {C3.showChain (C3.chain c s)}"
  for a in mine do
    if (`Zeta5).isPrefixOf a || (`C3ctl).isPrefixOf a then
      msg := msg ++ s!"\n    chain to axiom       : {C3.showChain (C3.chain c a)}"
  logInfo msg

/-! ## Positive controls — the walker must find these. -/

namespace C3ctl
theorem planted_sorry : (1 : ℕ) = 2 := sorry
theorem uses_sorry_1 : (2 : ℕ) = 1 := planted_sorry.symm
theorem uses_sorry_2 : (1 : ℕ) + 1 = 1 := by rw [show (1:ℕ) + 1 = 2 from rfl]; exact uses_sorry_1
axiom planted_axiom : ∀ n : ℕ, n = n + 0
theorem uses_axiom_1 (n : ℕ) : n + 0 = n := (planted_axiom n).symm
theorem uses_axiom_2 : (5 : ℕ) + 0 = 5 := uses_axiom_1 5
theorem clean : (2 : ℕ) + 2 = 4 := rfl
end C3ctl

#c3 C3ctl.uses_sorry_2
#c3 C3ctl.uses_axiom_2
#c3 C3ctl.clean

/-! ## The ConstantInfo.value? trap, run as a negative control. -/

/-- A walker built on `ConstantInfo.value?` — the broken design.  Run, not described. -/
def brokenWalk (env : Environment) (root : Name) : Nat × Bool := Id.run do
  let mut seen : Std.HashSet Name := {}
  let mut todo := #[root]
  let mut foundSorry := false
  let mut fuel := 10000000
  while fuel > 0 do
    fuel := fuel - 1
    match todo.back? with
    | none => break
    | some n =>
      todo := todo.pop
      if seen.contains n then continue
      seen := seen.insert n
      match env.find? n with
      | none => pure ()
      | some ci =>
        let cs := (C3.constsOf ci.type).union
          (match ci.value? with | some v => C3.constsOf v | none => {})
        if cs.contains ``sorryAx then foundSorry := true
        for s in cs do todo := todo.push s
  return (seen.size, foundSorry)

elab "#c3trap " i:ident : command => do
  let env ← getEnv
  let t := i.getId
  let (n, s) := brokenWalk env t
  let isThm := match env.find? t with | some (.thmInfo _) => true | _ => false
  let hasVal := match env.find? t with | some ci => ci.value?.isSome | none => false
  logInfo s!"TRAP {t}: theorem={isThm}  value?.isSome={hasVal}  broken walker visits {n} constants, finds sorry: {s}"

#c3trap Zeta5.zeta5_irrational
#c3trap C3ctl.uses_sorry_2

/-! ## The cones. -/

#c3 Zeta5.zeta5_irrational
#c3 Zeta5.theorem_1_1
#c3 Zeta5.theorem_2_1
-- the four interface statements that were the last to be proved (formerly `sorry`s)
#c3 Zeta5.outer_local_analysis
#c3 Zeta5.PrimeSum.eq_5_7_uniformity
#c3 Zeta5.CrudeBound.crude_entry_bound
#c3 Zeta5.Section3.entry_bounds_4_2_4_3
-- the shared lemma and the main new theorems
#c3 Zeta5.HermiteBasis.det_coeffMatrix_unimodular
#c3 Zeta5.OuterBasis.outer_local_core
#c3 Zeta5.Uniformity.eq_5_7_uniformity
#c3 Zeta5.Lemma33.lemma_3_3
#c3 Zeta5.InnerEntries.entry_bounds
-- the one remaining `sorry`: must report itself as its only sorry leaf
#c3 Zeta5.RealBound.eq_6_14

/-! ## Lean's own `#print axioms`, for the third opinion. -/

#print axioms Zeta5.zeta5_irrational
#print axioms Zeta5.theorem_1_1
#print axioms Zeta5.theorem_2_1
#print axioms Zeta5.outer_local_analysis
#print axioms Zeta5.PrimeSum.eq_5_7_uniformity
#print axioms Zeta5.CrudeBound.crude_entry_bound
#print axioms Zeta5.Section3.entry_bounds_4_2_4_3
#print axioms Zeta5.HermiteBasis.det_coeffMatrix_unimodular
#print axioms Zeta5.RealBound.eq_6_14
#print axioms C3ctl.uses_sorry_2
#print axioms C3ctl.uses_axiom_2
