/-
Zeta5/Sec6/LogCosOff.lean  —  LEAF: (A.1) off the interval, normalised (`|x| > 1`).
-/
import Zeta5.Sec6.Defs

namespace Zeta5
namespace Sec6

open Real MeasureTheory Set

noncomputable section

/-- **LEAF (medium).**  (A.1) off the interval, normalised:
`∫_0^π log|x − cos θ| dθ = π log((|x| + √(x²−1))/2)` for `|x| > 1`.

Paper: (A.1), second branch, and its proof on p. 22 (differentiation in `t` and the
normalisation `U(t) − log t → 0`).

Proof plan: circle-average route of the module docstring of `Sec6/LogCos.lean` with the *real* root
`ζ = x + sign(x)√(x²−1)`, `|ζ| = |x| + √(x²−1) > 1`, for which
`|x − cos θ| = |e^{iθ} − ζ|² / (2|ζ|)` (since `ζ` is real, `|ζ − e^{−iθ}| = |ζ − e^{iθ}|`),
so the circle average is `2 log|ζ| − log 2 − log|ζ|`.  (Alternative: `x = cosh u`, and
`d/du ∫_0^π log(cosh u − cos θ) dθ = ∫_0^π sinh u/(cosh u − cos θ) dθ = π`.) -/
theorem integral_log_abs_sub_cos_of_one_lt_abs {x : ℝ} (hx : 1 < |x|) :
    ∫ θ in (0 : ℝ)..π, Real.log |x - Real.cos θ|
      = π * Real.log ((|x| + Real.sqrt (x ^ 2 - 1)) / 2) := by
  set q := Real.sqrt (x ^ 2 - 1) with hq
  have hx2 : 0 ≤ x ^ 2 - 1 := by nlinarith [sq_abs x, abs_nonneg x]
  have hqq : q ^ 2 = x ^ 2 - 1 := Real.sq_sqrt hx2
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  -- the real root ζ
  set ζ : ℝ := if 0 < x then x + q else x - q with hζ
  have hζeq : ζ ^ 2 - 2 * x * ζ + 1 = 0 := by
    rw [hζ]; split_ifs <;> nlinarith
  have hζabs : |ζ| = |x| + q := by
    rw [hζ]; split_ifs with h
    · rw [abs_of_pos h, abs_of_pos (by linarith)]
    · have : x < 0 := by
        rcases lt_or_eq_of_le (not_lt.mp h) with h' | h'
        · exact h'
        · subst h'; simp at hx; linarith
      rw [abs_of_neg this, abs_of_neg (by linarith)]; ring
  have hr1 : 1 < |ζ| := by rw [hζabs]; linarith
  have hζ0 : ζ ≠ 0 := by intro h; rw [h] at hr1; simp at hr1; linarith
  have hne : ∀ θ : ℝ, x - Real.cos θ ≠ 0 := by
    intro θ h
    have : |x| = |Real.cos θ| := by rw [sub_eq_zero.mp h]
    linarith [Real.abs_cos_le_one θ]
  -- pointwise identity
  have hpt : ∀ θ : ℝ, Real.log |x - Real.cos θ|
      = 2 * Real.log ‖circleMap 0 1 θ - (ζ : ℂ)‖ - (Real.log 2 + Real.log |ζ|) := by
    intro θ
    have hsq : ‖circleMap 0 1 θ - (ζ : ℂ)‖ ^ 2 = 2 * ζ * (x - Real.cos θ) := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp only [Complex.sub_re, Complex.sub_im, circleMap_zero_re, circleMap_zero_im,
        Complex.ofReal_re, Complex.ofReal_im]
      nlinarith [Real.sin_sq_add_cos_sq θ]
    have habs : |x - Real.cos θ| = ‖circleMap 0 1 θ - (ζ : ℂ)‖ ^ 2 / (2 * |ζ|) := by
      rw [hsq]
      have : (2 * ζ * (x - Real.cos θ)) = |2 * ζ * (x - Real.cos θ)| := by
        refine (abs_of_pos ?_).symm
        have h1 := hsq ▸ (sq_nonneg ‖circleMap 0 1 θ - (ζ : ℂ)‖)
        rcases lt_or_eq_of_le h1 with h1 | h1
        · exact h1
        · exfalso; rcases mul_eq_zero.mp h1.symm with h2 | h2
          · rcases mul_eq_zero.mp h2 with h3 | h3
            · norm_num at h3
            · exact hζ0 h3
          · exact hne θ h2
      rw [this, abs_mul, abs_mul, abs_two]
      field_simp
    have hn : ‖circleMap 0 1 θ - (ζ : ℂ)‖ ≠ 0 := by
      intro h
      have := hsq; rw [h] at this
      have : 2 * ζ * (x - Real.cos θ) = 0 := by rw [← this]; norm_num
      rcases mul_eq_zero.mp this with h2 | h2
      · rcases mul_eq_zero.mp h2 with h3 | h3
        · norm_num at h3
        · exact hζ0 h3
      · exact hne θ h2
    rw [habs, Real.log_div (pow_ne_zero 2 hn) (by positivity), Real.log_pow,
      Real.log_mul two_ne_zero (abs_ne_zero.mpr hζ0)]
    push_cast; ring
  -- full-period integral
  have hint : CircleIntegrable (fun z : ℂ => Real.log ‖z - (ζ : ℂ)‖) 0 1 :=
    circleIntegrable_log_norm_sub_const 1
  have havg := circleAverage_log_norm_sub_const₂ (a := (ζ : ℂ)) (by simpa using hr1)
  rw [circleAverage_def, smul_eq_mul] at havg
  have hpi : (0:ℝ) < π := Real.pi_pos
  have hI : ∫ θ in (0:ℝ)..2 * π, Real.log ‖circleMap 0 1 θ - (ζ : ℂ)‖
      = 2 * π * Real.log |ζ| := by
    have := havg
    simp only [Complex.norm_real, Real.norm_eq_abs] at this
    field_simp at this
    linarith
  have hfull : ∫ θ in (0:ℝ)..2 * π, Real.log |x - Real.cos θ|
      = 2 * π * (Real.log |ζ| - Real.log 2) := by
    simp_rw [hpt]
    rw [intervalIntegral.integral_sub (hint.const_mul 2) intervalIntegrable_const,
      intervalIntegral.integral_const_mul, hI, intervalIntegral.integral_const]
    simp; ring
  -- halving
  have hcont : Continuous (fun θ : ℝ => Real.log |x - Real.cos θ|) := by
    refine Continuous.log (by fun_prop) (fun θ => abs_ne_zero.mpr (hne θ))
  have hhalf : ∫ θ in π..2 * π, Real.log |x - Real.cos θ|
      = ∫ θ in (0:ℝ)..π, Real.log |x - Real.cos θ| := by
    have := intervalIntegral.integral_comp_sub_left
      (fun θ => Real.log |x - Real.cos θ|) (a := 0) (b := π) (2 * π)
    simp only [Real.cos_two_pi_sub] at this
    rw [this]; ring_nf
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable (μ := volume) 0 π) (hcont.intervalIntegrable (μ := volume) π (2 * π))
  rw [hhalf, hfull] at hsplit
  have hlog : Real.log ((|x| + q) / 2) = Real.log |ζ| - Real.log 2 := by
    rw [← hζabs, Real.log_div (abs_ne_zero.mpr hζ0) two_ne_zero]
  rw [hlog]; linarith

end

end Sec6
end Zeta5
