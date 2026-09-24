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
  sorry

end

end Sec6
end Zeta5
