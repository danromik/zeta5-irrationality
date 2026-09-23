/-
cert/C3Semantics.lean — what the main theorem states (certification of 2026-09-23; report in
docs/CERTIFICATION.md).

Is `Zeta5.zeta5_irrational` still "ζ(5) is irrational", with no hypotheses?

  * the TYPE of the constant is inspected as an `Expr`, not as pretty-printed text: it must be
    literally `Irrational Zeta5.zeta5`, with `Irrational` the root (Mathlib) constant;
  * the modules defining `Irrational` and every constant in the VALUE of `Zeta5.zeta5` are
    printed: none may be a Zeta5 module;
  * `(zeta5 : ℂ) = riemannZeta 5` is re-proved here, by a route different from the previous
    certification pass (`zeta_nat_eq_tsum_of_gt_one` and an index shift, not the `cpow` form);
  * the theorem is restated as "no rational number equals `riemannZeta 5`".

Run from the repository root, after `lake build` (about 2 minutes):
  lake env lean cert/C3Semantics.lean
Expected output: cert/c3/C3Semantics.out.
-/
import Zeta5

open Lean Elab Command

elab "#c3stmt" : command => do
  let env ← getEnv
  let some ci := env.find? ``Zeta5.zeta5_irrational | logError "missing"; return
  let expected : Expr := .app (.const ``Irrational []) (.const ``Zeta5.zeta5 [])
  let modOf (n : Name) : Name := match env.getModuleIdxFor? n with
    | some i => env.header.moduleNames[i.toNat]! | none => `none
  logInfo s!"kind: {if ci matches .thmInfo _ then "theorem" else "NOT A THEOREM"}; universe params: {ci.levelParams}\ntype as Expr == Irrational Zeta5.zeta5 : {ci.type == expected}\nraw type: {ci.type}\n`Irrational` is defined in module {modOf ``Irrational}\n`Zeta5.zeta5` is defined in module {modOf ``Zeta5.zeta5}"
  let some zi := env.find? ``Zeta5.zeta5 | logError "missing zeta5"; return
  match zi with
  | .defnInfo v =>
    let cs := v.value.getUsedConstants
    let mut s := s!"Zeta5.zeta5 is a def; raw value: {v.value}\nconstants in its value and their modules:"
    for c in cs do s := s ++ s!"\n   {c}  ←  {modOf c}"
    logInfo s
  | _ => logError "zeta5 is not a def"

#c3stmt

set_option pp.all true in
#check (Zeta5.zeta5_irrational)
#print Zeta5.zeta5
#print Irrational

-- `Irrational` is Mathlib's: its definition unfolds by `Iff.rfl`.
example (x : ℝ) : Irrational x ↔ x ∉ Set.range ((↑) : ℚ → ℝ) := Iff.rfl

namespace C3sem

open Complex

/-- ζ(5), as the project defines it, is Mathlib's `riemannZeta 5`.  Route: Mathlib's
`zeta_nat_eq_tsum_of_gt_one` (sum over `n ≥ 0` with `1/0^5 = 0`) and an index shift. -/
theorem zeta5_eq_riemannZeta : ((Zeta5.zeta5 : ℝ) : ℂ) = riemannZeta 5 := by
  have h5 : riemannZeta ((5 : ℕ) : ℂ) = ∑' n : ℕ, 1 / (n : ℂ) ^ (5 : ℕ) :=
    zeta_nat_eq_tsum_of_gt_one (by norm_num)
  have hsR : Summable (fun n : ℕ => 1 / (n : ℝ) ^ (5 : ℕ)) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hsC : Summable (fun n : ℕ => 1 / (n : ℂ) ^ (5 : ℕ)) := by
    have := (Complex.ofRealCLM.summable hsR)
    simpa [Function.comp_def] using this
  rw [show (5 : ℂ) = ((5 : ℕ) : ℂ) by norm_num, h5, hsC.tsum_eq_zero_add]
  simp only [Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, div_zero,
    zero_add]
  unfold Zeta5.zeta5
  rw [Complex.ofReal_tsum]
  push_cast
  rfl

/-- The theorem, read as: no rational number is `riemannZeta 5`. -/
theorem riemannZeta_five_not_rational (q : ℚ) : ((q : ℂ)) ≠ riemannZeta 5 := by
  intro h
  rw [← zeta5_eq_riemannZeta] at h
  have h' : ((q : ℝ) : ℂ) = ((Zeta5.zeta5 : ℝ) : ℂ) := by exact_mod_cast h
  exact Zeta5.zeta5_irrational ⟨q, Complex.ofReal_injective h'⟩

/-- A sanity bound, so that `zeta5` cannot be a degenerate value: `1 ≤ zeta5`. -/
theorem one_le_zeta5 : (1 : ℝ) ≤ Zeta5.zeta5 := by
  have hs : Summable (fun v : ℕ => 1 / ((v : ℝ) + 1) ^ 5) := by
    have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 5))
    simpa [Nat.cast_add, Nat.cast_one] using this
  unfold Zeta5.zeta5
  calc (1 : ℝ) = 1 / (((0 : ℕ) : ℝ) + 1) ^ 5 := by norm_num
    _ ≤ ∑' v : ℕ, 1 / ((v : ℝ) + 1) ^ 5 :=
        hs.le_tsum 0 (fun j _ => by positivity)

end C3sem

#print axioms C3sem.zeta5_eq_riemannZeta
#print axioms C3sem.one_le_zeta5
#print axioms C3sem.riemannZeta_five_not_rational
