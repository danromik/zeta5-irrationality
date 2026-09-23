/-
cert/C3Attack.lean — attacks on the two axioms (certification of 2026-09-23; report in
docs/CERTIFICATION.md).

  (a) the degenerate instances that would make each axiom FALSE as formalised (Lean's junk
      values: the Bochner integral of a non-integrable function is 0, `tsum` of a non-summable
      family is 0) are exactly the ones the hypotheses exclude — the hypothesis each would need
      is proved REFUTABLE;
  (b) each axiom is non-vacuous: a concrete consequence is derived, sorry-free;
  (c) the compile-only `_unsafe_rec` auxiliaries found by the module scan are not in the cone,
      and neither is any `unsafe`/`partial` constant (fast native cone walk, used only for this
      membership question; the axiom/sorry walk is `C3Walker.lean`).

Run from the repository root, after `lake build` (about 2 minutes):
  lake env lean cert/C3Attack.lean
Expected output: cert/c3/C3Attack.out.
-/
import Zeta5

open MeasureTheory Set Filter Topology Lean Elab Command

namespace C3att

/-! ## (a) The guards. -/

-- `a = 0`: the integrand behaves like `1/(π y²)` at `0`, so the Bochner integral is the junk
-- value `0` and the right side is `-1/4`.  `a < 0` is similar.  The axiom's hypothesis is
-- `0 < a`; at `a = 0` and `a = -1` it is REFUTABLE, so the axiom cannot be instantiated there.
-- (`fail_if_success` cannot be used for this: Lean's error recovery turns the failed `by
-- norm_num` into a logged error rather than a tactic failure.)
theorem hermite_guard_zero : ¬ ((0 : ℝ) < 0) := lt_irrefl 0
theorem hermite_guard_neg : ¬ ((0 : ℝ) < -1) := by norm_num

-- PNT axiom with an empty or reversed interval, or `a < 0`: the hypotheses `a < b`, `0 ≤ a`
-- are refutable there.
theorem pnt_guard_empty : ¬ ((1 : ℝ) < 1) := lt_irrefl 1
theorem pnt_guard_neg : ¬ ((0 : ℝ) ≤ -1) := by norm_num

-- PNT axiom with an unbounded `φ` (here `1/y` on `[0,1]`): the boundedness hypothesis cannot be
-- discharged, since `|1/y|` is unbounded near `0`.
theorem unbounded_blocked : ¬ ∃ C : ℝ, ∀ y ∈ Icc (0 : ℝ) 1, |1 / y| ≤ C := by
  rintro ⟨C, hC⟩
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hC 1 ⟨by norm_num, le_refl _⟩)
  set y : ℝ := 1 / (C + 1) with hy
  have hy0 : 0 < y := by positivity
  have hy1 : y ≤ 1 := by rw [hy, div_le_one (by linarith)]; linarith
  have := hC y ⟨hy0.le, hy1⟩
  rw [hy, one_div_one_div, abs_of_pos (by linarith)] at this
  linarith

/-! ## (b) Non-vacuity: concrete consequences, sorry-free. -/

/-- Hermite at `a = 1`: `∫_0^∞ w(y)/(y²+1) dy = ζ(5) − 3/4`. -/
theorem hermite_at_one :
    ∫ y in Ioi (0 : ℝ), Zeta5.wt y / (y ^ 2 + 1 ^ 2) = Zeta5.zeta5 - 3 / 4 := by
  rw [Zeta5.Axioms.hermite_pole_integral 1 one_pos]
  unfold Zeta5.zeta5
  norm_num
  ring

/-- PNT axiom on `[1, 2]` with `φ ≡ 1`: `(θ(2X) − θ(X))/X → 1` (up to the floors). -/
theorem pnt_dyadic :
    Tendsto (fun X : ℝ =>
        (∑ p ∈ (Finset.Ioc ⌊(1 : ℝ) * X⌋₊ ⌊(2 : ℝ) * X⌋₊).filter Nat.Prime,
          (fun _ : ℝ => (1 : ℝ)) (p / X) * Real.log p) / X)
      atTop (𝓝 1) := by
  have h := Zeta5.Axioms.pnt_prime_riemann_sum 1 2 (by norm_num) (by norm_num)
    (fun _ => (1 : ℝ)) ⟨1, fun _ _ => by norm_num⟩ ⟨∅, fun _ _ _ => continuousAt_const⟩
  have hI : (∫ _ in (1 : ℝ)..2, (1 : ℝ)) = 1 := by norm_num
  rw [hI] at h
  exact h

end C3att

#print axioms C3att.hermite_at_one
#print axioms C3att.pnt_dyadic
#print axioms C3att.unbounded_blocked

/-! ## (c) No `unsafe` / `partial` constant, and none of the `_unsafe_rec` auxiliaries, in the
cone. -/

elab "#c3unsafe" : command => do
  let env ← getEnv
  let root := ``Zeta5.zeta5_irrational
  let mut seen : Std.HashSet Name := {}
  seen := seen.insert root
  let mut q : Array Name := #[root]
  let mut i := 0
  while h : i < q.size do
    let n := q[i]
    i := i + 1
    match env.find? n with
    | none => pure ()
    | some ci =>
      let es : Array Expr := match ci with
        | .defnInfo v => #[v.type, v.value] | .thmInfo v => #[v.type, v.value]
        | .opaqueInfo v => #[v.type, v.value]
        | .recInfo v => #[v.type] ++ v.rules.toArray.map (·.rhs)
        | _ => #[ci.type]
      let extra : Array Name := match ci with
        | .inductInfo v => v.ctors.toArray ++ v.all.toArray
        | .ctorInfo v => #[v.induct]
        | .recInfo v => v.all.toArray
        | _ => #[]
      for e in es do
        for c in e.getUsedConstants do
          unless seen.contains c do seen := seen.insert c; q := q.push c
      for c in extra do
        unless seen.contains c do seen := seen.insert c; q := q.push c
  let bad := q.filter fun n => match env.find? n with
    | some ci => ci.isUnsafe || ci.isPartial
    | none => false
  let recs := #[`Zeta5.AppendixB.ChainOK._unsafe_rec, `Zeta5.AppendixB.chainEnd._unsafe_rec,
    `Zeta5.AppendixB.chainVal._unsafe_rec, `Zeta5.Audit.visit._unsafe_rec,
    `Zeta5.RealBound.chainB._unsafe_rec]
  logInfo s!"cone size (native walk) {q.size}\nunsafe or partial constants in the cone ({bad.size}): {bad.toList}\n_unsafe_rec auxiliaries in the cone: {(recs.filter seen.contains).toList}\nkinds of the five: {recs.toList.map fun r => match env.find? r with | some ci => (ci.isUnsafe, ci.isPartial) | none => (false, false)}"

#c3unsafe
