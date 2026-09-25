/-
Zeta5/Sec6/Antideriv.lean  —  an explicit antiderivative for the smoothing error.
-/
import Zeta5.Sec6.Defs

namespace Zeta5
namespace Sec6

open Real MeasureTheory Set

noncomputable section

/-- `∫_0^X log(1 + b²/x²) dx = X log(1 + b²/X²) + 2b arctan(X/b)` for
`b > 0`, `X ≥ 0`, with integrability.

Proof.  `G(x) = x log(1 + b²/x²) + 2b arctan(x/b)` has `G'(x) = log(1 + b²/x²)` for `x > 0`
and is continuous on `ℝ` (write `x log(1 + b²/x²) = x log(x² + b²) − 2x log x`; `G 0 = 0` since
`b²/0 = 0` in Lean).  The derivative is nonnegative, hence integrable, and the fundamental
theorem of calculus gives `G X − G 0 = G X`. -/
theorem integral_log_one_add_sq_div {b X : ℝ} (hb : 0 < b) (hX : 0 ≤ X) :
    IntervalIntegrable (fun x => Real.log (1 + b ^ 2 / x ^ 2)) volume 0 X ∧
      ∫ x in (0 : ℝ)..X, Real.log (1 + b ^ 2 / x ^ 2)
        = X * Real.log (1 + b ^ 2 / X ^ 2) + 2 * b * Real.arctan (X / b) := by
  have hb2 : 0 < b ^ 2 := by positivity
  have key : ∀ x : ℝ, x * Real.log (1 + b ^ 2 / x ^ 2)
      = x * Real.log (x ^ 2 + b ^ 2) - 2 * (x * Real.log x) := by
    intro x
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · have hx2 : 0 < x ^ 2 := by positivity
      have : 1 + b ^ 2 / x ^ 2 = (x ^ 2 + b ^ 2) / x ^ 2 := by field_simp
      rw [this, Real.log_div (by positivity) hx2.ne', Real.log_pow]
      push_cast; ring
  set G : ℝ → ℝ := fun x => x * Real.log (1 + b ^ 2 / x ^ 2) + 2 * b * Real.arctan (x / b)
    with hG
  have hGeq : G = fun x => x * Real.log (x ^ 2 + b ^ 2) - 2 * (x * Real.log x)
      + 2 * b * Real.arctan (x / b) := by
    funext x; simp only [hG, key]
  have hcont : Continuous G := by
    rw [hGeq]
    have h1 : Continuous fun x : ℝ => Real.log (x ^ 2 + b ^ 2) :=
      ((continuous_pow 2).add continuous_const : Continuous fun x : ℝ => x ^ 2 + b ^ 2).log
        (fun x => ne_of_gt (by show (0:ℝ) < x ^ 2 + b ^ 2; have := sq_nonneg x; linarith))
    exact ((continuous_id.mul h1).sub (continuous_const.mul Real.continuous_mul_log)).add
      (continuous_const.mul (Real.continuous_arctan.comp (continuous_id.div_const b)))
  have hderiv : ∀ x ∈ Ioo (0 : ℝ) X, HasDerivAt G (Real.log (1 + b ^ 2 / x ^ 2)) x := by
    intro x hx
    have hx0 : 0 < x := hx.1
    rw [hGeq]
    have hq : x ^ 2 + b ^ 2 ≠ 0 := ne_of_gt (by have := sq_nonneg x; linarith)
    have d1 : HasDerivAt (fun x : ℝ => x ^ 2 + b ^ 2) (2 * x) x := by
      simpa using (hasDerivAt_pow 2 x).add_const (b ^ 2)
    have d2 := (hasDerivAt_id x).mul (d1.log hq)
    have d3 := Real.hasDerivAt_mul_log hx0.ne'
    have d4 : HasDerivAt (fun x : ℝ => Real.arctan (x / b)) (1 / (1 + (x / b) ^ 2) * (1 / b)) x :=
      ((hasDerivAt_id' x).div_const b).arctan
    refine ((d2.sub (d3.const_mul 2)).add (d4.const_mul (2 * b))).congr_deriv ?_
    have hlog : Real.log (1 + b ^ 2 / x ^ 2) = Real.log (x ^ 2 + b ^ 2) - 2 * Real.log x := by
      have hx2 : 0 < x ^ 2 := by positivity
      have : 1 + b ^ 2 / x ^ 2 = (x ^ 2 + b ^ 2) / x ^ 2 := by field_simp
      rw [this, Real.log_div hq hx2.ne', Real.log_pow]; push_cast; ring
    rw [hlog]
    simp only [id]
    field_simp
    ring
  have hnn : ∀ x ∈ Ioo (0 : ℝ) X, 0 ≤ Real.log (1 + b ^ 2 / x ^ 2) := fun x _ =>
    Real.log_nonneg (by have : 0 ≤ b ^ 2 / x ^ 2 := by positivity
                        linarith)
  have hint : IntervalIntegrable (fun x => Real.log (1 + b ^ 2 / x ^ 2)) volume 0 X :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hX).2
      (intervalIntegral.integrableOn_deriv_of_nonneg hcont.continuousOn hderiv hnn)
  refine ⟨hint, ?_⟩
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hX hcont.continuousOn hderiv hint]
  simp [hG]

end

end Sec6
end Zeta5
