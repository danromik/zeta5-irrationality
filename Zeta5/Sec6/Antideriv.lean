/-
Zeta5/Sec6/Antideriv.lean  —  LEAF: an explicit antiderivative for the smoothing error.
-/
import Zeta5.Sec6.Defs

namespace Zeta5
namespace Sec6

open Real MeasureTheory Set

noncomputable section

/-- **LEAF (medium).**  `∫_0^X log(1 + b²/x²) dx = X log(1 + b²/X²) + 2b arctan(X/b)` for
`b > 0`, `X ≥ 0`, with integrability.

Proof plan.  `G(x) = x log(1 + b²/x²) + 2b arctan(x/b)`; for `x > 0`,
`G'(x) = log(1 + b²/x²) − 2b²/(x² + b²) + 2b²/(x² + b²) = log(1 + b²/x²)`
(`HasDerivAt.mul`, `HasDerivAt.log`, `Real.hasDerivAt_arctan`, `HasDerivAt.comp`).  `G` is
continuous on `[0, X]`: at `0`, `x log(1 + b²/x²) = x log(x² + b²) − 2x log x → 0`
(`Real.tendsto_log_mul_rpow_nhdsGT_zero` / `Real.continuous_mul_log`-type lemmas; in Lean
`G 0 = 0` since `b²/0 = 0`).  The derivative is `≥ 0`, so it is integrable
(`intervalIntegral.integrableOn_deriv_of_nonneg`), and
`intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le` gives `G X − G 0 = G X`. -/
theorem integral_log_one_add_sq_div {b X : ℝ} (hb : 0 < b) (hX : 0 ≤ X) :
    IntervalIntegrable (fun x => Real.log (1 + b ^ 2 / x ^ 2)) volume 0 X ∧
      ∫ x in (0 : ℝ)..X, Real.log (1 + b ^ 2 / x ^ 2)
        = X * Real.log (1 + b ^ 2 / X ^ 2) + 2 * b * Real.arctan (X / b) := by
  sorry

end

end Sec6
end Zeta5
