/-
Zeta5/Sec6/SmoothErr.lean  —  LEAF: the normalised smoothing error of the Cauchy kernel
against the arcsine measure of `[−1,1]` (replaces the paper's mass bound and
`∫U^ρ dω_i − U^ρ(t_i) ≤ 60√ε`, p. 19).
-/
import Zeta5.Sec6.SmoothAux
import Zeta5.Sec6.Antideriv

namespace Zeta5
namespace Sec6

open Real MeasureTheory Set

noncomputable section

/-- **LEAF (medium).**  Normalised smoothing error: for every real `x` and `δ > 0`,

`∫_0^π ½ log(1 + δ²/(x − cos θ)²) dθ ≤ π (δ + π √(2δ))`,

with integrability.  (Numerically the ratio LHS/RHS is at most `0.23`,
`numerics/sec6/check_leaves.py`.)

Paper: replaces the arcsine mass bound `ω([x−r, x+r]) ≤ 4√(2r)/(π√L)` and its integration
in `r` (p. 19).

Proof plan.  Take `θ₀` from `exists_nearest_cos x`.  For `θ ∈ [0,π]`,
`|x − cos θ| ≥ |cos θ₀ − cos θ| ≥ 2(θ − θ₀)²/π²` (`cos_sub_cos_ge`).  With `b² = δπ²/2`,
i.e. `b = π√(δ/2)`: for `θ ≠ θ₀`, `δ/|x − cos θ| ≤ b²/(θ − θ₀)²`, and
`½ log(1 + A²) ≤ log(1 + A)` for `A ≥ 0` (as `1 + A² ≤ (1 + A)²`), so
`½ log(1 + δ²/(x − cos θ)²) ≤ log(1 + b²/(θ − θ₀)²)` for a.e. `θ` (all `θ ≠ θ₀`; when
`x = cos θ` Lean's `δ²/0 = 0` makes the left side `0`).  Then
`∫_0^π log(1 + b²/(θ−θ₀)²) dθ = ∫_{−θ₀}^{π−θ₀} log(1 + b²/u²) du ≤ ∫_{−π}^{π} = 2∫_0^π`
(`intervalIntegral.integral_comp_sub_right`, nonnegativity, evenness via
`intervalIntegral.integral_comp_neg`), and by `integral_log_one_add_sq_div`
`∫_0^π log(1 + b²/u²) du = π log(1 + b²/π²) + 2b arctan(π/b) ≤ b²/π + πb`
(`Real.log_le_sub_one_of_pos`, `Real.arctan_lt_pi_div_two`).  Total
`≤ 2b²/π + 2πb = πδ + π²√(2δ)`.  Integrability of the left side: it is measurable and
dominated a.e. by the integrable `θ ↦ log(1 + b²/(θ − θ₀)²)` (`IntervalIntegrable.mono_fun'`). -/
theorem smooth_err_norm (x : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    IntervalIntegrable (fun θ => Real.log (1 + δ ^ 2 / (x - Real.cos θ) ^ 2)) volume 0 π ∧
      ∫ θ in (0 : ℝ)..π, Real.log (1 + δ ^ 2 / (x - Real.cos θ) ^ 2) / 2
        ≤ π * (δ + π * Real.sqrt (2 * δ)) := by
  sorry

end

end Sec6
end Zeta5
