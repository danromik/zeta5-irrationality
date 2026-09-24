/-
Zeta5/Sec6/Field.lean  —  (A.5): the closed form of the external field `V` of (6.1).
-/
import Zeta5.Sec6.Defs

namespace Zeta5
namespace Sec6

open Real MeasureTheory Set

noncomputable section

/-- **LEAF (easy–medium).**  For `t > 0` and every real `c`,

`∫_0^c log(t + u²) du = c log(t + c²) − 2c + 2√t arctan(c/√t)`.

Paper: "For `t > 0`, integration in (6.1) gives (A.5)" (p. 23).

Proof plan.  `F(u) = u log(t + u²) − 2u + 2√t arctan(u/√t)` has
`F'(u) = log(t + u²) + 2u²/(t + u²) − 2 + 2t/(t + u²) = log(t + u²)`
(`HasDerivAt.mul`, `HasDerivAt.log` with `t + u² > 0`, `Real.hasDerivAt_arctan`,
`HasDerivAt.comp`/`HasDerivAt.div_const`, and `√t² = t`: `Real.sq_sqrt`); the integrand is
continuous, so `intervalIntegral.integral_eq_sub_of_hasDerivAt` (with
`Continuous.intervalIntegrable`) gives `F c − F 0 = F c` (`Real.log` of `t`, times `0`, and
`arctan 0 = 0`). -/
theorem integral_log_add_sq {t : ℝ} (ht : 0 < t) (c : ℝ) :
    ∫ u in (0 : ℝ)..c, Real.log (t + u ^ 2)
      = c * Real.log (t + c ^ 2) - 2 * c + 2 * Real.sqrt t * Real.arctan (c / Real.sqrt t) := by
  sorry

/-- **(A.5)**: `V(t) = Vclosed t` for `t > 0`. -/
theorem Vfield_eq_Vclosed {t : ℝ} (ht : 0 < t) : Vfield t = Vclosed t := by
  unfold Vfield Vclosed
  rw [integral_log_add_sq ht 1, integral_log_add_sq ht (alpha : ℝ)]
  have ha : ((alpha : ℚ) : ℝ) = 3 / 40 := by norm_num [alpha]
  rw [ha, one_pow, add_comm t 1]
  ring

end

end Sec6
end Zeta5
