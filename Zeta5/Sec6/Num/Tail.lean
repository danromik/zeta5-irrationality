/-
Zeta5/Sec6/Num/Tail.lean  —  the certified numerics of (6.2)/(6.7) (Lemma 6.1, Appendix A.3):
`t ≥ 4`: an analytic bound replacing (6.8) (`tail_bound_ge4`).

Imports only Mathlib (and the previous `Num` module).  No `native_decide`, no
`implemented_by`, no axiom: every finite computation is `decide +kernel`, i.e. checked by the
kernel.  THIS FILE CONTAINS NO `sorry`.  (Prepared by the numerics scout of the §6 blueprint;
namespace `Zeta5.Sec6.Num`.)
-/
import Zeta5.Sec6.Num.Cell

/-! # `t ≥ 4`: an analytic bound (the role of (6.8)), closed forms. -/

namespace Zeta5
namespace Sec6
namespace Num
open Real Finset

theorem UomR_le_log {a b t : ℝ} (ha : 0 < a) (hab : a < b) (hbt : b < t) :
    UomR a b t ≤ Real.log t := by
  unfold UomR
  rw [if_neg (by intro h; linarith [h.2])]
  have hf := outside_facts hab (Or.inr hbt)
  have hsq : Real.sqrt ((t - a) * (t - b)) ≤ t - (a + b) / 2 := by
    rw [Real.sqrt_le_left (by linarith)]; nlinarith [sq_nonneg (a - b)]
  apply Real.log_le_log (by linarith [Real.sqrt_nonneg ((t - a) * (t - b))])
  rw [abs_of_pos (by linarith)]; linarith

theorem tab_pos : ∀ j < 16, 0 < aQ j ∧ bQ j < 4 := by decide +kernel

theorem sum_cQ : ∑ j ∈ range 16, (cQ j : ℝ) = 37 / 40 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, cQ]; push_cast; norm_num

theorem Uclosed_le_log {t : ℝ} (ht : 4 ≤ t) : Uclosed t ≤ 37 / 40 * Real.log t := by
  unfold Uclosed
  rw [← sum_cQ, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j hj
  have hj' := Finset.mem_range.1 hj
  obtain ⟨h1, h2, _, h4⟩ := tab_facts j hj'
  obtain ⟨p1, p2⟩ := tab_pos j hj'
  apply mul_le_mul_of_nonneg_left _ (by exact_mod_cast h4)
  apply UomR_le_log (by exact_mod_cast p1) (by exact_mod_cast h1)
  have : (bQ j : ℝ) < 4 := by exact_mod_cast p2
  linarith

/-- For `t ≥ 4` and `K ≥ 2`: `2U - V + √t/K ≤ M₀` (crude; the true value is `≤ -10.9`). -/
theorem tail_bound_ge4 {t K : ℝ} (ht : 4 ≤ t) (hK : 2 ≤ K) :
    2 * Uclosed t - Vclosed t + Real.sqrt t / K ≤ -1329 / 200 := by
  have hU := Uclosed_le_log ht
  have ht0 : 0 < t := by linarith
  set s := Real.sqrt t with hs
  have hs2 : 2 ≤ s := by
    rw [hs, show (2 : ℝ) = Real.sqrt (2 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by linarith)
  have hs0 : 0 < s := by linarith
  have hss : s ^ 2 = t := by rw [hs, Real.sq_sqrt ht0.le]
  -- log t = 2 log s ≤ 2 (s - 1)
  have hlogt : Real.log t ≤ 2 * (s - 1) := by
    rw [← hss, Real.log_pow]; push_cast
    linarith [Real.log_le_sub_one_of_pos hs0]
  have hlog0 : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
  have h1 : Real.log t ≤ Real.log (1 + t) := Real.log_le_log ht0 (by linarith)
  have h2 : Real.log (t + (3 / 40) ^ 2) ≤ Real.log t + (3 / 40) ^ 2 / t := by
    have := Real.log_le_sub_one_of_pos (x := (t + (3 / 40) ^ 2) / t) (by positivity)
    rw [Real.log_div (by positivity) ht0.ne'] at this
    have e : (t + (3 / 40) ^ 2) / t - 1 = (3 / 40) ^ 2 / t := by field_simp; ring
    linarith
  have h3 : 0 ≤ arctan (1 / s) := arctan_nonneg.2 (by positivity)
  have h4 : arctan ((3 / 40) / s) ≤ (3 / 40) / s := arctan_le_self (by positivity)
  have h4' : s * arctan ((3 / 40) / s) ≤ 3 / 40 := by
    have := mul_le_mul_of_nonneg_left h4 hs0.le
    rwa [mul_div_cancel₀ _ hs0.ne'] at this
  have hpi : (3.14 : ℝ) < π := Real.pi_gt_d2
  have hK' : s / K ≤ s / 2 := div_le_div_of_nonneg_left hs0.le (by norm_num) hK
  have hinv : (3 / 40) ^ 2 / t ≤ (3 / 40) ^ 2 / 4 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) ht
  have hV : Vclosed t = Real.log (1 + t) - 6 * (3 / 40) * Real.log (t + (3 / 40) ^ 2) - 2
      + 12 * (3 / 40) + 2 * π * s + 2 * s * arctan (1 / s) - 12 * (s * arctan ((3 / 40) / s)) := by
    unfold Vclosed; rw [← hs]; ring
  rw [hV]
  have hps : 3.14 * s ≤ π * s := mul_le_mul_of_nonneg_right hpi.le hs0.le
  nlinarith [mul_nonneg hs0.le h3]

end Num
end Sec6
end Zeta5
