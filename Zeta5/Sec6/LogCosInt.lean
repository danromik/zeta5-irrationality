/-
Zeta5/Sec6/LogCosInt.lean  —  integrability of `θ ↦ log|x − cos θ|` on `[0,π]`.
-/
import Zeta5.Sec6.Defs

namespace Zeta5
namespace Sec6

open Real MeasureTheory Set

noncomputable section

/-- `θ ↦ log|x − cos θ|` is interval integrable on `[0,π]`, for every
real `x` (logarithmic singularity at the at most one zero `θ₀ = arccos x`; at `x = ±1` the
singularity is at an endpoint and is of type `log θ²`).

Paper: implicit in (A.1) (p. 21).

Proof.  `θ ↦ x − cos θ` is analytic, hence meromorphic, on `[0,π]`, and Mathlib's
`MeromorphicOn.intervalIntegrable_log_norm` applies. -/
theorem intervalIntegrable_log_abs_sub_cos (x : ℝ) :
    IntervalIntegrable (fun θ => Real.log |x - Real.cos θ|) volume 0 π := by
  have hmero : MeromorphicOn (fun θ : ℝ => x - Real.cos θ) (Set.uIcc 0 π) :=
    ((analyticOnNhd_const (v := x)).sub analyticOnNhd_cos).meromorphicOn
  simpa [Real.norm_eq_abs] using hmero.intervalIntegrable_log_norm

end

end Sec6
end Zeta5
