/-
Zeta5/Sec6/ArcsinePot.lean  —  the arcsine potential (A.1) for a general interval.
-/
import Zeta5.Sec6.LogCos

namespace Zeta5
namespace Sec6

open Real MeasureTheory Set

noncomputable section

/-- **(A.1)**: for `a < b` and every
real `t`, with `m = (a+b)/2`, `r = (b−a)/2`,

`∫_0^π log|t − (m + r cos θ)| dθ = π · U^{ω_[a,b]}(t)`   (`Uarc`, both branches),

and the integrand is interval integrable.  Since `ω_[a,b]` is the push-forward of `dθ/π` under
`θ ↦ m + r cos θ` (`arcsine`, `integral_arcsine`), this is exactly the paper's (A.1).

Paper: (A.1) (p. 21) and its proof (p. 22).

Proof.  `t − (m + r cos θ) = r(x − cos θ)` with `x = (t − m)/r`, so off the single point
`θ = arccos x` the integrand is `log r + log|x − cos θ|`, and the integral is `π(log r + Psi x)`
by `integral_log_abs_sub_cos`.  Then `log r + Psi x = Uarc a b t`: `|x| ≤ 1 ↔ a ≤ t ≤ b`, and
for `|x| > 1`, `r(|x| + √(x²−1)) = |t − m| + √((t−a)(t−b))`. -/
theorem arcsine_pot {a b : ℝ} (hab : a < b) (t : ℝ) :
    IntervalIntegrable (fun θ => Real.log |t - ((a + b) / 2 + (b - a) / 2 * Real.cos θ)|)
        volume 0 π ∧
      ∫ θ in (0 : ℝ)..π, Real.log |t - ((a + b) / 2 + (b - a) / 2 * Real.cos θ)|
        = π * Uarc a b t := by
  set r : ℝ := (b - a) / 2 with hr
  set x : ℝ := (t - (a + b) / 2) / r with hx
  have hr0 : 0 < r := by rw [hr]; linarith
  have hkey : ∀ θ, t - ((a + b) / 2 + r * Real.cos θ) = r * (x - Real.cos θ) := by
    intro θ; rw [hx]; field_simp; ring
  -- a.e. equality with `log r + log|x − cos θ|`
  have hae : ∀ᵐ θ ∂(volume : Measure ℝ), θ ∈ Set.uIoc 0 π →
      Real.log |t - ((a + b) / 2 + r * Real.cos θ)| = Real.log r + Real.log |x - Real.cos θ| := by
    rw [ae_iff]
    refine measure_mono_null (t := {Real.arccos x}) ?_ (measure_singleton _)
    intro θ hθ
    simp only [Set.mem_ofPred_eq, Classical.not_imp] at hθ
    obtain ⟨hmem, hne⟩ := hθ
    have hθ' : θ ∈ Set.Icc 0 π := by
      rw [Set.uIoc_of_le Real.pi_pos.le] at hmem; exact ⟨hmem.1.le, hmem.2⟩
    by_contra hc
    apply hne
    have hcos : x - Real.cos θ ≠ 0 := by
      intro h0
      apply hc
      rw [Set.mem_singleton_iff, sub_eq_zero.1 h0, Real.arccos_cos hθ'.1 hθ'.2]
    rw [hkey, abs_mul, abs_of_pos hr0, Real.log_mul hr0.ne' (abs_ne_zero.2 hcos)]
  have hint0 := intervalIntegrable_log_abs_sub_cos x
  have hint1 : IntervalIntegrable (fun θ => Real.log r + Real.log |x - Real.cos θ|) volume 0 π :=
    intervalIntegrable_const.add hint0
  refine ⟨?_, ?_⟩
  · refine hint1.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr ?_)
    filter_upwards [hae] with θ h hm using (h hm).symm
  · rw [intervalIntegral.integral_congr_ae hae, intervalIntegral.integral_add intervalIntegrable_const hint0,
      intervalIntegral.integral_const, integral_log_abs_sub_cos, smul_eq_mul, sub_zero, ← mul_add]
    congr 1
    unfold Psi Uarc
    have habs : |x| ≤ 1 ↔ a ≤ t ∧ t ≤ b := by
      rw [hx, abs_div, abs_of_pos hr0, div_le_one hr0, abs_le, hr]
      constructor
      · rintro ⟨h1, h2⟩; constructor <;> linarith
      · rintro ⟨h1, h2⟩; constructor <;> linarith
    by_cases h : a ≤ t ∧ t ≤ b
    · rw [ite_eq_left (habs.2 h), ite_eq_left h, ← sub_eq_add_neg, ← Real.log_div hr0.ne' two_ne_zero, hr]
      · congr 1; ring
    · rw [ite_eq_right (fun h' => h (habs.1 h')), ite_eq_right h]
      have hx1 : 1 < |x| := lt_of_not_ge (fun h' => h (habs.1 h'))
      have hx2 : 0 ≤ x ^ 2 - 1 := by nlinarith [sq_abs x, abs_nonneg x]
      have hpos : 0 < (|x| + Real.sqrt (x ^ 2 - 1)) / 2 := by
        have := Real.sqrt_nonneg (x ^ 2 - 1); linarith
      rw [← Real.log_mul hr0.ne' hpos.ne']
      congr 1
      have e1 : r * |x| = |t - (a + b) / 2| := by
        rw [hx, abs_div, abs_of_pos hr0]; field_simp
      have e2 : r * Real.sqrt (x ^ 2 - 1) = Real.sqrt ((t - a) * (t - b)) := by
        rw [← Real.sqrt_sq hr0.le, ← Real.sqrt_mul (sq_nonneg r)]
        have hrx : r * x = t - (a + b) / 2 := by rw [hx]; field_simp
        have : r ^ 2 * (x ^ 2 - 1) = (r * x) ^ 2 - r ^ 2 := by ring
        rw [this, hrx, hr]; ring_nf
      rw [mul_div_assoc', mul_add, e1, e2]

end

end Sec6
end Zeta5
