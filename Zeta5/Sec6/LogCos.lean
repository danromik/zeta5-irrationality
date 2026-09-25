/-
Zeta5/Sec6/LogCos.lean  —  the normalised arcsine potential (A.1), both branches, from
`LogCosOn.lean` and `LogCosOff.lean` (Mathlib does not have this integral):

`(1/π)∫_0^π log|x − cos θ| dθ = −log 2` for `|x| ≤ 1`, and
`= log((|x| + √(x²−1))/2)` for `|x| > 1`.  This is (A.1) for `[a,b] = [−1,1]`; the general
interval follows by scaling (`ArcsinePot.arcsine_pot`).

* `|x| ≤ 1` (`LogCosOn.lean`): with `x = cos φ`,
  `cos φ − cos θ = −2 sin((φ+θ)/2) sin((φ−θ)/2)`, and `∫_0^π log sin = −π log 2` together with
  the `π`-periodicity of `log|sin|`.
* `|x| > 1` (`LogCosOff.lean`): with the real root `ζ = x + sign(x)√(x²−1)`, `|ζ| > 1`,
  `|x − cos θ| = |e^{iθ} − ζ|²/(2|ζ|)`, and Mathlib's circle average
  `circleAverage_log_norm_sub_const₂` gives `∫_0^{2π} log|e^{iθ} − ζ| dθ = 2π log|ζ|`; the
  integral over `[0,π]` is half of that over `[0,2π]`.
* Integrability (`LogCosInt.lean`) holds because `θ ↦ x − cos θ` is analytic, hence
  meromorphic.
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
