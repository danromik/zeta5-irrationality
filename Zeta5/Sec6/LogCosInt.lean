/-
Zeta5/Sec6/LogCosInt.lean  —  LEAF: integrability of `θ ↦ log|x − cos θ|` on `[0,π]`.
-/
import Zeta5.Sec6.Defs

namespace Zeta5
namespace Sec6

open Real MeasureTheory Set

noncomputable section

/-- **LEAF (medium).**  `θ ↦ log|x − cos θ|` is interval integrable on `[0,π]`, for every
real `x` (logarithmic singularity at the at most one zero `θ₀ = arccos x`; at `x = ±1` the
singularity is at an endpoint and is of type `log θ²`).

Paper: implicit in (A.1) (p. 21).

Proof plan: see the module docstring of `Sec6/LogCos.lean` (circle-average route: `circleIntegrable_log_norm_sub_const`
and the Joukowski factorisation; or bound `|log|x − cos θ||` near the zero using
`cos_sub_cos_ge` of `Sec6/SmoothAux.lean` — note that file imports only `Defs`, so either
duplicate the two-line Jordan bound here or use the circle route). -/
theorem intervalIntegrable_log_abs_sub_cos (x : ℝ) :
    IntervalIntegrable (fun θ => Real.log |x - Real.cos θ|) volume 0 π := by
  sorry

end

end Sec6
end Zeta5
