/-
Zeta5/Audit.lean

THE ASSUMPTION REPORT, computed by Lean rather than by reading the files.

`#print axioms Zeta5.zeta5_irrational` reports *that* the theorem depends on `sorryAx`, but
not on *which* `sorry`s, and it prints the project's own `axiom` declarations mixed in with
Lean's three standard ones.  The metaprogram below separates the three kinds of assumption
and prints, for any declaration:

  (A) the standard Lean axioms it uses          — `propext`, `Classical.choice`, `Quot.sound`;
  (B) the explicit external axioms of this project (`Zeta5/Axioms.lean`), each of which is a
      standard fact of the literature that Mathlib lacks;
  (C) the `sorry`s it rests on — i.e. the steps of Fauzan's own argument that are NOT yet
      machine-checked.  These are the unfinished items; there is no hiding them, because
      Lean computes this list from the environment on every build.

THIS FILE CONTAINS NO `sorry`.

-------------------------------------------------------------------------------------------
CORRECTNESS OF THE WALKER, and how it is checked.

Two traps, both of which bit earlier versions of this file:

 1. `Lean.ConstantInfo.value?` returns `none` for theorems in Lean 4.34.  A walker built on
    it silently reports "depends on NO sorry" for a declaration whose `#print axioms` says
    `sorryAx`.  `usedConsts` below therefore matches on the constructor.

 2. Reachability must agree with Lean's own.  `visit` reproduces the match of
    `Lean.CollectAxioms.collect` (`src/lean/Lean/Util/CollectAxioms.lean` in the Lean toolchain)
    constructor for constructor, *including* `inductInfo → ctors`, which a naive walker
    omits.

The check is machine-run, not a claim: `visit` collects the axioms it reaches as well as the
`sorry` leaves, and `#assumption_report` compares that axiom set with the one returned by
Lean's own `Lean.collectAxioms` (the function behind `#print axioms`).  It prints
`walker agrees with Lean.collectAxioms` only when the two sets are equal, and
`*** WALKER DISAGREES ***`, with both sets, otherwise.  In particular, a walker that failed
to reach theorem bodies would not see `sorryAx` either, so the disagreement would be
printed.  `#print axioms Zeta5.zeta5_irrational` is kept at the bottom of the file as a
third, independent printout of the same information.
-/
import Zeta5.Checks
import Zeta5.Arithmetic

open Lean

namespace Zeta5.Audit

/-- The constants a declaration depends on, by the same case analysis as
`Lean.CollectAxioms.collect`.  `Lean.ConstantInfo.value?` is *not* usable here: it returns
`none` for theorems in Lean 4.34. -/
def usedConsts (ci : ConstantInfo) : Array Name :=
  match ci with
  | .axiomInfo v  => v.type.getUsedConstants
  | .defnInfo v   => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .thmInfo v    => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .opaqueInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .quotInfo _   => #[]
  | .ctorInfo v   => v.type.getUsedConstants
  | .recInfo v    => v.type.getUsedConstants
  | .inductInfo v => v.type.getUsedConstants ++ v.ctors.toArray

/-- The body of a constant, when it has one.  Used by `allSorries`. -/
def bodyOf (ci : ConstantInfo) : Option Expr :=
  match ci with
  | .defnInfo v => some v.value
  | .thmInfo v => some v.value
  | .opaqueInfo v => some v.value
  | _ => none

/-- The state of the walk: constants already seen, `sorry` leaves found, axioms found. -/
structure WalkState where
  seen : NameSet := {}
  sorries : Array Name := #[]
  axioms : Array Name := #[]

/-- Walk the dependency cone of `target`, recording

* every constant that mentions `sorryAx` in its own type or value (i.e. that *is* a `sorry`,
  as opposed to merely depending on one), and
* every `axiom` declaration reached.

The case analysis is `usedConsts`, i.e. Lean's own. -/
partial def visit (env : Environment) (target : Name) : StateM WalkState Unit := do
  if (← get).seen.contains target then return
  modify fun s => { s with seen := s.seen.insert target }
  match env.find? target with
  | none => return
  | some ci =>
    let consts := usedConsts ci
    if ci matches .axiomInfo _ then
      modify fun s => { s with axioms := s.axioms.push target }
    if consts.contains ``sorryAx then
      modify fun s => { s with sorries := s.sorries.push target }
    for c in consts do
      visit env c

/-- The result of the walk: the `sorry` leaves and the axioms, both sorted. -/
def walk (env : Environment) (target : Name) : Array Name × Array Name :=
  let ((), st) := (visit env target).run {}
  (st.sorries.qsort (fun a b => a.toString < b.toString),
   st.axioms.qsort (fun a b => a.toString < b.toString))

/-- The sorted list of direct `sorry`s in the dependency cone of `target`. -/
def sorryLeaves (env : Environment) (target : Name) : Array Name := (walk env target).1

/-- Every `sorry` declared anywhere in the `Zeta5` namespace. -/
def allSorries (env : Environment) : Array Name :=
  let res := env.constants.fold (init := (#[] : Array Name)) fun acc n ci =>
    if n.getRoot == `Zeta5 && !n.isInternal then
      match bodyOf ci with
      | some v => if v.getUsedConstants.contains ``sorryAx then acc.push n else acc
      | none => acc
    else acc
  res.qsort (fun a b => a.toString < b.toString)

/-- Lean's three standard axioms.  Anything else in the axiom list is either `sorryAx` or an
`axiom` declared by this project. -/
def standardAxioms : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]

end Zeta5.Audit

open Elab Command in
/-- `#assumption_report f` prints the complete list of assumptions under `f`, in three
groups: Lean's standard axioms, this project's explicit external axioms, and the `sorry`s
(the unfinished steps of the paper's own argument).  It also cross-checks its own walker
against `Lean.collectAxioms`, the function behind `#print axioms`. -/
elab "#assumption_report " i:ident : command => do
  let env ← getEnv
  let n := i.getId
  let (sorries, axs) := Zeta5.Audit.walk env n
  let official ← Lean.collectAxioms n
  let std := axs.filter (fun a => Zeta5.Audit.standardAxioms.contains a)
  let proj := axs.filter (fun a => a.getRoot == `Zeta5)
  let other := axs.filter (fun a =>
    !(Zeta5.Audit.standardAxioms.contains a) && a.getRoot != `Zeta5 && a != ``sorryAx)
  let fmt (a : Array Name) : String :=
    if a.isEmpty then "    (none)"
    else String.intercalate "\n" (a.toList.map (fun m => "    " ++ m.toString))
  let mine : NameSet := axs.foldl (fun s a => s.insert a) {}
  let theirs : NameSet := official.foldl (fun s a => s.insert a) {}
  let missing := official.filter (fun a => !mine.contains a)
  let extra := axs.filter (fun a => !theirs.contains a)
  let check :=
    if missing.isEmpty && extra.isEmpty then
      "  [self-check: walker agrees with Lean.collectAxioms, " ++ toString axs.size ++
        " axiom(s)]"
    else
      "  *** WALKER DISAGREES WITH Lean.collectAxioms ***\n" ++
      "    walker : " ++ toString axs.toList ++ "\n" ++
      "    Lean   : " ++ toString official.toList
  logInfo m!"\
ASSUMPTION REPORT for {n}

  (A) standard Lean axioms:
{fmt std}

  (B) explicit external axioms of this project (Zeta5/Axioms.lean):
{fmt proj}

  (C) sorry(s) — unfinished steps of the paper's own argument, {sorries.size} in all:
{fmt sorries}

  (D) any other axiom (must be empty):
{fmt other}

{check}"

open Elab Command in
/-- `#orphan_sorries f` lists the `sorry`s of the `Zeta5` namespace that `f` does *not*
rest on.  For `f = Zeta5.zeta5_irrational` these are the statements that the formalisation
transcribes but that Theorem 1.1, as assembled here, never consumes — i.e. the places where
the paper's own logical route would be short-circuited by a stronger downstream `sorry`. -/
elab "#orphan_sorries " i:ident : command => do
  let env ← getEnv
  let cone := Zeta5.Audit.sorryLeaves env i.getId
  let orphans := (Zeta5.Audit.allSorries env).filter (fun n => !cone.contains n)
  if orphans.isEmpty then
    logInfo m!"every sorry of the Zeta5 namespace is used by {i.getId}."
  else
    let body := String.intercalate "\n" (orphans.toList.map (fun m => "  " ++ m.toString))
    logInfo m!"{orphans.size} sorry(s) of the Zeta5 namespace are NOT used by \
{i.getId}:\n{body}"

open Elab Command in
/-- `#sorry_tree f` lists the `sorry`s that `f` transitively rests on. -/
elab "#sorry_tree " i:ident : command => do
  let env ← getEnv
  let n := i.getId
  let res := Zeta5.Audit.sorryLeaves env n
  if res.isEmpty then
    logInfo m!"{n} depends on NO sorry."
  else
    let body := String.intercalate "\n" (res.toList.map (fun m => "  " ++ m.toString))
    logInfo m!"{n} rests on {res.size} sorry(s):\n{body}"

/-! ## The machine-checked assumption list of Theorem 1.1

This is the list the ground rules of this formalization (README, "Ground rules") require:
one theorem, one explicit list of assumptions, computed by Lean.  It appears in the build log. -/

#assumption_report Zeta5.zeta5_irrational

/-! ### The same for the intermediate statements, and for the sorry-free islands. -/

#sorry_tree Zeta5.theorem_2_1
#sorry_tree Zeta5.prop_5_1
#sorry_tree Zeta5.prop_2_2
#sorry_tree Zeta5.prop_4_1
#sorry_tree Zeta5.prop_4_3
#sorry_tree Zeta5.prop_6_3
#sorry_tree Zeta5.prop_5_2
#sorry_tree Zeta5.eq_3_12
#sorry_tree Zeta5.eq_5_16_5_18
#sorry_tree Zeta5.eq_7_1
#sorry_tree Zeta5.Delta_natDegree
#sorry_tree Zeta5.Q_natDegree
#sorry_tree Zeta5.eq_2_9
#sorry_tree Zeta5.exists_innerAlloc
#sorry_tree Zeta5.stdAlloc
#sorry_tree Zeta5.theorem_1_1
#sorry_tree Zeta5.prop_4_1_of_entry_bounds
#sorry_tree Zeta5.lemma_4_2
#sorry_tree Zeta5.ell_lt_caseSplit
#sorry_tree Zeta5.lemma_3_1
#sorry_tree Zeta5.AppendixB.eq_5_16_5_17
#sorry_tree Zeta5.Tail.tail_bound_strong
#sorry_tree Zeta5.CrudeBound.eq_3_11
#sorry_tree Zeta5.PrimeSum.block1_le
#sorry_tree Zeta5.RealBound.prop_6_3_of
#sorry_tree Zeta5.AppendixB.eq_5_18

/-! ### Positive controls: the steps proved on 2026-09-23

The four statements that were `sorry`s until 2026-09-23, the shared lemma they use, and the
main new theorems behind them.  Each must print `depends on NO sorry`; `RealBound.eq_6_14`,
still open, is the negative control and must print `rests on 1 sorry(s)`. -/

#sorry_tree Zeta5.outer_local_analysis
#sorry_tree Zeta5.PrimeSum.eq_5_7_uniformity
#sorry_tree Zeta5.CrudeBound.crude_entry_bound
#sorry_tree Zeta5.Section3.entry_bounds_4_2_4_3
#sorry_tree Zeta5.HermiteBasis.det_coeffMatrix_unimodular
#sorry_tree Zeta5.OuterBasis.outer_local_core
#sorry_tree Zeta5.Uniformity.eq_5_7_uniformity
#sorry_tree Zeta5.Lemma33.lemma_3_3
#sorry_tree Zeta5.Lemma33.pullback
#sorry_tree Zeta5.InnerEntries.raabe_tau
#sorry_tree Zeta5.InnerEntries.general_bound
#sorry_tree Zeta5.InnerEntries.entry_bounds
#sorry_tree Zeta5.RealBound.eq_6_14

/-! ### Orphans

A `sorry` of the `Zeta5` namespace that Theorem 1.1 does *not* rest on would mean that the
formalisation had short-circuited the paper's own logical route: a transcribed statement
that nothing consumes.  There are none — every `sorry`
in the project is load-bearing for `Zeta5.zeta5_irrational`, which is what makes the list
printed by `#assumption_report` above complete. -/

#orphan_sorries Zeta5.zeta5_irrational

/-! ### The third, independent printout: Lean's own. -/

#print axioms Zeta5.zeta5_irrational
#print axioms Zeta5.theorem_1_1
