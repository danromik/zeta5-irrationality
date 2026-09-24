/-
Zeta5/Sec6/SmoothArc.lean  —  LEAF: the smoothing error for one arcsine component `ω_[a,b]`.
-/
import Zeta5.Sec6.SmoothErr
import Zeta5.Sec6.ArcsinePot

namespace Zeta5
namespace Sec6

open Real MeasureTheory Set

noncomputable section

/-- **LEAF (medium; algebra on top of `arcsine_pot` and `smooth_err_norm`).**  The smoothed
potential of one arcsine component exceeds the true potential (A.1) by at most
`2ε/L + 2π√(ε/L)`, `L = b − a`, uniformly in `t ∈ ℝ`:

`∫_0^π kC ε (t − (m + r cos θ)) dθ ≤ π (U^{ω_[a,b]}(t) + 2ε/(b−a) + 2π √(ε/(b−a)))`.

(Numerically the error is at most `0.23` of the allowed one.)

Paper: p. 19, `∫U^ρ dω_i − U^ρ(t_i) ≤ ∑_j 8c_j√(2ε)/(π√(b_j−a_j))`, for one component.

Proof plan.  With `r = (b−a)/2`, `x = (t−m)/r`, `δ = ε/r = 2ε/(b−a)`: for `u ≠ 0`,
`kC ε u = log|u| + ½ log(1 + ε²/u²)` (`kC`, `Real.log_mul`, `Real.log_pow`), and
`u = t − (m + r cos θ) = r(x − cos θ)` gives `ε²/u² = δ²/(x − cos θ)²`.  The set of `θ ∈ [0,π]`
with `u = 0` has at most one point (`Real.injOn_cos`), so a.e. `kC ε u` equals
`log|t − (m + r cos θ)| + ½ log(1 + δ²/(x − cos θ)²)`; integrate
(`intervalIntegral.integral_congr_ae`, `intervalIntegral.integral_add` with the two
integrability statements of `arcsine_pot` and `smooth_err_norm`), and use
`δ + π√(2δ) = 2ε/(b−a) + 2π√(ε/(b−a))` (`Real.sqrt_mul_self`, `Real.sqrt_mul`). -/
theorem arcsine_smooth_err {a b : ℝ} (hab : a < b) (t : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∫ θ in (0 : ℝ)..π, kC ε (t - ((a + b) / 2 + (b - a) / 2 * Real.cos θ))
      ≤ π * (Uarc a b t + 2 * ε / (b - a) + 2 * π * Real.sqrt (ε / (b - a))) := by
  sorry

end

end Sec6
end Zeta5
