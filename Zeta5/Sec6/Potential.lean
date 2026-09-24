/-
Zeta5/Sec6/Potential.lean  —  Lemma 6.1's potential inequality in the form (6.7) consumed by
(6.9), for the closed forms `Urho` (A.1) and `Vclosed` (A.5), and its transfer to the field
`Vfield` of (6.1).
-/
import Zeta5.Sec6.Field
import Zeta5.Sec6.Num.Final

namespace Zeta5
namespace Sec6

open Real

noncomputable section

/-- The numerics' `U^ρ` (Table 1 as rationals) is `Urho`. -/
theorem Uclosed_eq_Urho (t : ℝ) : Num.Uclosed t = Urho t := by
  unfold Num.Uclosed Urho
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' := Finset.mem_range.1 hj
  have ha : ((Num.aQ j : ℚ) : ℝ) = RealBound.aT j := by
    interval_cases j <;> norm_num [Num.aQ, RealBound.aT]
  have hb : ((Num.bQ j : ℚ) : ℝ) = RealBound.bT j := by
    interval_cases j <;> norm_num [Num.bQ, RealBound.bT]
  have hc : ((Num.cQ j : ℚ) : ℝ) = RealBound.cT j := by
    interval_cases j <;> norm_num [Num.cQ, RealBound.cT]
  rw [ha, hb, hc]; rfl

/-- The numerics' `V` is `Vclosed` (the same closed form (A.5)). -/
theorem Num_Vclosed_eq (t : ℝ) : Num.Vclosed t = Vclosed t := rfl

/-- **(6.7)** for the closed forms: `2U^ρ(t) − V(t) + √t/K ≤ M₀ + √2/K` for `K ≥ 2`, `t ≥ 0`.
From the certified partition of `Zeta5/Sec6/Num/` (`Num.eq_6_7_closed`). -/
theorem eq_6_7_closed (K : ℝ) (hK : 2 ≤ K) (t : ℝ) (ht : 0 ≤ t) :
    2 * Urho t - Vclosed t + Real.sqrt t / K ≤ RealBound.M0 + Real.sqrt 2 / K := by
  have := Num.eq_6_7_closed K hK t ht
  rw [Uclosed_eq_Urho, Num_Vclosed_eq] at this
  unfold RealBound.M0
  linarith

/-- **(6.7)** for the field `V` of (6.1), on `t > 0` (the only range (6.13) uses). -/
theorem eq_6_7_field (K : ℝ) (hK : 2 ≤ K) (t : ℝ) (ht : 0 < t) :
    2 * Urho t - Vfield t + Real.sqrt t / K ≤ RealBound.M0 + Real.sqrt 2 / K := by
  rw [Vfield_eq_Vclosed ht]; exact eq_6_7_closed K hK t ht.le

end

end Sec6
end Zeta5
