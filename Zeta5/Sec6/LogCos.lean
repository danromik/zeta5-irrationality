/-
Zeta5/Sec6/LogCos.lean  —  the normalised arcsine potential (A.1), both branches, from the
leaves of `LogCosInt.lean`, `LogCosOn.lean`, `LogCosOff.lean` (a Mathlib gap).  This file
contains no `sorry`; its docstring describes the two proof routes for the leaves.

`(1/π)∫_0^π log|x − cos θ| dθ = −log 2` for `|x| ≤ 1`, and
`= log((|x| + √(x²−1))/2)` for `|x| > 1`.  This is (A.1) for `[a,b] = [−1,1]`; the general
interval follows by scaling (`ArcsinePot.arcsine_pot`).

Two routes are available; either may be used for either case.
* **Circle averages (recommended; uniform in `x`).**  Mathlib:
  `circleAverage_log_norm_sub_const_eq_posLog : circleAverage (log ‖· − a‖) 0 1 = log⁺ ‖a‖`
  (`Mathlib/Analysis/SpecialFunctions/Integrals/PosLogEqCircleAverage.lean`), and
  `Real.circleAverage_def : circleAverage f c R = (2π)⁻¹ • ∫ θ in 0..2π, f (circleMap c R θ)`.
  Choose `ζ : ℂ` with `ζ + ζ⁻¹ = 2x`, `‖ζ‖ ≥ 1`: `ζ = x + sign(x)√(x²−1)` (real) if `|x| ≥ 1`,
  `ζ = x + i√(1−x²)` (`‖ζ‖ = 1`) if `|x| ≤ 1`.  Then for all `θ`
  `2ζ (x − cos θ) = (ζ − e^{iθ})(ζ − e^{−iθ})`, and `|ζ − e^{−iθ}| = |conj ζ − e^{iθ}|`,
  hence, off the (at most two) zeros,
  `log|x − cos θ| = log‖e^{iθ} − ζ‖ + log‖e^{iθ} − conj ζ‖ − log 2 − log‖ζ‖`.
  Average over `[0,2π]` (the two exceptional points are null; use
  `intervalIntegral.integral_congr_ae` or `Real.circleAverage_congr_codiscreteWithin`):
  `2 log⁺‖ζ‖ − log 2 − log‖ζ‖ = log‖ζ‖ − log 2`.  Finally
  `∫_0^{2π} = 2∫_0^π` because `cos(2π − θ) = cos θ` (`intervalIntegral.integral_comp_sub_left`
  and `intervalIntegral.integral_add_adjacent_intervals`), and `‖ζ‖ = |x| + √(x²−1)` resp. `1`.
  Integrability: `circleIntegrable_log_norm_sub_const` for each factor.
* **Real route for `|x| ≤ 1`.**  `x = cos φ`, `φ ∈ [0,π]`;
  `cos φ − cos θ = −2 sin((φ+θ)/2) sin((φ−θ)/2)` (`Real.cos_sub_cos`); then
  `integral_log_sin_zero_pi : ∫ x in 0..π, log (sin x) = −log 2 * π`, evenness and
  `π`-periodicity of `log|sin|` (`Function.Periodic.intervalIntegral_add_eq`), and
  `intervalIntegrable_log_sin`.
-/
import Zeta5.Sec6.LogCosInt
import Zeta5.Sec6.LogCosOn
import Zeta5.Sec6.LogCosOff

namespace Zeta5
namespace Sec6

open Real MeasureTheory Set

noncomputable section

/-- The normalised arcsine potential, both branches: `∫_0^π log|x − cos θ| dθ = π Psi(x)`. -/
theorem integral_log_abs_sub_cos (x : ℝ) :
    ∫ θ in (0 : ℝ)..π, Real.log |x - Real.cos θ| = π * Psi x := by
  unfold Psi
  split_ifs with hx
  · rw [integral_log_abs_sub_cos_of_abs_le hx]; ring
  · exact integral_log_abs_sub_cos_of_one_lt_abs (lt_of_not_ge hx)

end

end Sec6
end Zeta5
