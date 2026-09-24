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
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hss : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht.le
  set F : ℝ → ℝ := fun u =>
    u * Real.log (t + u ^ 2) - 2 * u + 2 * Real.sqrt t * Real.arctan (u / Real.sqrt t) with hF
  have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) c, HasDerivAt F (Real.log (t + x ^ 2)) x := by
    intro x _
    have hpos : 0 < t + x ^ 2 := by positivity
    have h1 : HasDerivAt (fun u : ℝ => t + u ^ 2) (2 * x) x := by
      simpa using (hasDerivAt_pow 2 x).const_add t
    have h2 : HasDerivAt (fun u : ℝ => Real.log (t + u ^ 2)) (2 * x / (t + x ^ 2)) x :=
      h1.log hpos.ne'
    have h3 : HasDerivAt (fun u : ℝ => u * Real.log (t + u ^ 2))
        (1 * Real.log (t + x ^ 2) + x * (2 * x / (t + x ^ 2))) x := (hasDerivAt_id x).mul h2
    have h4 : HasDerivAt (fun u : ℝ => u / Real.sqrt t) (1 / Real.sqrt t) x :=
      (hasDerivAt_id x).div_const _
    have h5 : HasDerivAt (fun u : ℝ => Real.arctan (u / Real.sqrt t))
        (1 / (1 + (x / Real.sqrt t) ^ 2) * (1 / Real.sqrt t)) x := h4.arctan
    have h6 := (h3.sub ((hasDerivAt_id x).const_mul 2)).add (h5.const_mul (2 * Real.sqrt t))
    convert h6 using 1
    · funext u; simp [hF]
    · have hq : 1 + (x / Real.sqrt t) ^ 2 = (t + x ^ 2) / t := by
        rw [div_pow, hss]; field_simp
      rw [hq]
      field_simp
      ring
  have hint : IntervalIntegrable (fun u : ℝ => Real.log (t + u ^ 2)) volume 0 c := by
    apply Continuous.intervalIntegrable
    exact Continuous.log (by fun_prop) (fun u => by positivity)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp [hF]

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
