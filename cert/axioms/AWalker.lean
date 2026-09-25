/-
cert/axioms/AWalker.lean — cert/final/FWalker.lean re-run on branch `axioms` (commit ca05d77),
after the two former axioms were replaced by theorems and one textbook axiom (the prime number
theorem, `Zeta5.Axioms.chebyshev_theta_asymptotic`).  The walker code (constsOf, succs, walk,
chain, #c3, #c3mod) and all five planted controls are copied verbatim from FWalker.lean; only
the target list changed: the new theorems `Zeta5.Hermite.pole_integral`,
`Zeta5.PNT.prime_riemann_sum`, the new axiom itself, and Propositions 2.2 and 5.2 were added,
and the `#c3mod` lines now locate the new declarations.

Run from the repository root, after `lake build`:
  lake env lean cert/axioms/AWalker.lean

FWalker.lean header follows.

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

Run from the repository root, after `lake build`:
  lake env lean cert/final/FWalker.lean
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


/-- `#c3mod f` : the module that defines `f`. -/
elab "#c3mod " i:ident : command => do
  let env ← getEnv
  let n := i.getId
  match env.getModuleIdxFor? n with
  | some k => logInfo s!"MODULE {n} : {env.header.moduleNames[k.toNat]!}"
  | none => logInfo s!"MODULE {n} : (current file or missing: contains={env.contains n})"

/-! ## Positive controls — the walker must find these. -/

namespace C3ctl
theorem planted_sorry : (1 : ℕ) = 2 := sorry
theorem uses_sorry_1 : (2 : ℕ) = 1 := planted_sorry.symm
theorem uses_sorry_2 : (1 : ℕ) + 1 = 1 := by rw [show (1:ℕ) + 1 = 2 from rfl]; exact uses_sorry_1
axiom planted_axiom : ∀ n : ℕ, n = n + 0
theorem uses_axiom_1 (n : ℕ) : n + 0 = n := (planted_axiom n).symm
theorem uses_axiom_2 : (5 : ℕ) + 0 = 5 := uses_axiom_1 5
theorem clean : (2 : ℕ) + 2 = 4 := rfl
-- a `sorry` inside an auxiliary `where` definition (compiled to a separate constant)
def hiddenVal : ℕ := aux + 1
where aux : ℕ := sorry
theorem uses_hidden : hiddenVal = hiddenVal := by
  have : hiddenVal = hiddenVal.aux + 1 := rfl
  exact rfl
theorem uses_hidden_2 : hiddenVal + 0 = hiddenVal := by
  show hiddenVal.aux + 1 + 0 = hiddenVal.aux + 1; rfl
-- a `sorry` reached only through a structure instance field (`.proj` / instance path)
structure Box where
  v : ℕ
  pf : v = 3
instance boxInst : Inhabited Box := ⟨⟨3, sorry⟩⟩
theorem uses_box : (default : Box).v = (default : Box).v := by
  have := (default : Box).pf
  rfl
theorem uses_box_2 : (default : Box).v = 3 := (default : Box).pf
end C3ctl

#c3 C3ctl.uses_sorry_2
#c3 C3ctl.uses_axiom_2
#c3 C3ctl.clean
#c3 C3ctl.uses_hidden_2
#c3 C3ctl.uses_box_2

/-! ## The cones. -/

#c3 Zeta5.zeta5_irrational
#c3 Zeta5.theorem_1_1
#c3 Zeta5.theorem_2_1
#c3 Zeta5.RealBound.eq_6_14
#c3 Zeta5.RealBound.prop_6_3
#c3 Zeta5.Sec6.Gram.eq_6_14_of_config
#c3 Zeta5.Sec6.configBound
#c3 Zeta5.Sec6.Num.eq_6_7_closed
#c3 Zeta5.Sec6.eq_6_7_closed
#c3 Zeta5.Sec6.rho_energy_ge
-- the former axioms (now theorems), the new axiom, and their consumers
#c3 Zeta5.Hermite.pole_integral
#c3 Zeta5.PNT.prime_riemann_sum
#c3 Zeta5.Axioms.chebyshev_theta_asymptotic
#c3 Zeta5.Positivity.prop_2_2
#c3 Zeta5.prop_2_2
#c3 Zeta5.PrimeSum.prop_5_2
#c3 Zeta5.prop_5_2
-- the 19 leaves of the §6 blueprint
#c3 Zeta5.Sec6.frullani_integrable
#c3 Zeta5.Sec6.frullani_cauchy
#c3 Zeta5.Sec6.gauss_pd
#c3 Zeta5.Sec6.swap_frullani
#c3 Zeta5.Sec6.cauchy_cnd
#c3 Zeta5.Sec6.intervalIntegrable_log_abs_sub_cos
#c3 Zeta5.Sec6.integral_log_abs_sub_cos_of_abs_le
#c3 Zeta5.Sec6.integral_log_abs_sub_cos_of_one_lt_abs
#c3 Zeta5.Sec6.arcsine_pot
#c3 Zeta5.Sec6.exists_nearest_cos
#c3 Zeta5.Sec6.integral_log_one_add_sq_div
#c3 Zeta5.Sec6.smooth_err_norm
#c3 Zeta5.Sec6.arcsine_smooth_err
#c3 Zeta5.Sec6.rho_cross
#c3 Zeta5.Sec6.Irho_double_sum
#c3 Zeta5.Sec6.pair_energy_ge
#c3 Zeta5.Sec6.kE_arc_comm
#c3 Zeta5.Sec6.kE_rhoM_expand
#c3 Zeta5.Sec6.integral_log_add_sq

/-! ## Where the moved statements live. -/

#c3mod Zeta5.zeta5_irrational
#c3mod Zeta5.RealBound.eq_6_14
#c3mod Zeta5.RealBound.prop_6_3
#c3mod Zeta5.RealBound.prop_6_3_of
#c3mod Zeta5.Axioms.chebyshev_theta_asymptotic
#c3mod Zeta5.Hermite.pole_integral
#c3mod Zeta5.PNT.prime_riemann_sum
-- the two removed axioms must be ABSENT from the environment (contains=false)
#c3mod Zeta5.Axioms.hermite_pole_integral
#c3mod Zeta5.Axioms.pnt_prime_riemann_sum

/-! ## Lean's own `#print axioms`. -/

#print axioms Zeta5.zeta5_irrational
#print axioms Zeta5.theorem_1_1
#print axioms Zeta5.theorem_2_1
#print axioms Zeta5.RealBound.eq_6_14
#print axioms Zeta5.RealBound.prop_6_3
#print axioms Zeta5.Hermite.pole_integral
#print axioms Zeta5.PNT.prime_riemann_sum
#print axioms Zeta5.prop_2_2
#print axioms Zeta5.prop_5_2
#print axioms C3ctl.uses_sorry_2
#print axioms C3ctl.uses_axiom_2
#print axioms C3ctl.uses_hidden_2
#print axioms C3ctl.uses_box_2
