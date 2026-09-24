/-
Zeta5/Sec6/LogCosOn.lean  —  LEAF: (A.1) on the interval, normalised (`|x| ≤ 1`).
-/
import Zeta5.Sec6.Defs

namespace Zeta5
namespace Sec6

open Real MeasureTheory Set

noncomputable section

/-- **LEAF (medium).**  (A.1) on the interval, normalised:
`∫_0^π log|x − cos θ| dθ = −π log 2` for `|x| ≤ 1`.

Paper: (A.1), first branch, and its proof on p. 22 ("On the interval, the substitution
`t = m + r cos φ` and the identity `cos φ − cos θ = −2 sin((φ+θ)/2) sin((φ−θ)/2)` give the
constant `log(r/2)`").

Proof plan: see the module docstring of `Sec6/LogCos.lean` (either route). -/
theorem integral_log_abs_sub_cos_of_abs_le {x : ℝ} (hx : |x| ≤ 1) :
    ∫ θ in (0 : ℝ)..π, Real.log |x - Real.cos θ| = -(π * Real.log 2) := by
  sorry

end

end Sec6
end Zeta5
