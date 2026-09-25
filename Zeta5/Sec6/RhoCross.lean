/-
Zeta5/Sec6/RhoCross.lean  —  the cross term `∫ kC ε (t − y) dρ(y) ≤ U^ρ(t) + O(√ε)`.
-/
import Zeta5.Sec6.SmoothArc
import Zeta5.Sec6.Measures

namespace Zeta5
namespace Sec6

open Real MeasureTheory Set Finset

noncomputable section

/-- For every real `t` and `ε > 0`,

`∫ kC ε (t − y) dρ(y) ≤ U^ρ(t) + 88√ε + 420ε`.

Paper: p. 19, `∫U^ρ dω_i − U^ρ(t_i) ≤ ∑_j 8c_j√(2ε)/(π√(b_j−a_j)) ≤ 60√ε` — the only place
where `b_j − a_j > 1/225` is used.

Proof.  `integral_rhoM` writes the left side as
`∑_{j<16} c_j π⁻¹ ∫_0^π kC ε (t − (m_j + r_j cos θ)) dθ`, and `arcsine_smooth_err` bounds the
`j`-th term by `c_j (Uarc a_j b_j t + 2ε/L_j + 2π√(ε/L_j))`, `L_j = b_j − a_j`.  With
`1/L_j < 225` (`RealBound.tab1_length`) and `√(1/L_j) < 15` (`RealBound.sqrt_len_gt`) the error
is at most `c_j (450ε + 95√ε)`; summing with `∑ c_j = λ = 37/40` gives `420ε + 88√ε`. -/
theorem rho_cross (t : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∫ y, kC ε (t - y) ∂rhoM ≤ Urho t + 88 * Real.sqrt ε + 420 * ε := by
  have hcont : Continuous (fun y => kC ε (t - y)) :=
    (continuous_kC hε.ne').comp (continuous_const.sub continuous_id)
  rw [integral_rhoM hcont]
  have hpi := Real.pi_pos
  have hpi2 : π < 3.15 := Real.pi_lt_d2
  have hsε : 0 ≤ Real.sqrt ε := Real.sqrt_nonneg ε
  have hterm : ∀ j ∈ range 16,
      RealBound.cT j * (π⁻¹ * ∫ θ in (0 : ℝ)..π, kC ε (t - (mid j + rad j * Real.cos θ)))
        ≤ RealBound.cT j * Uarc (RealBound.aT j) (RealBound.bT j) t
          + RealBound.cT j * (450 * ε + 95 * Real.sqrt ε) := by
    intro j hj
    have hj' : j < 16 := Finset.mem_range.1 hj
    have hc := RealBound.cT_pos j hj'
    have hab := RealBound.aT_lt_bT j hj'
    have hL := RealBound.tab1_length j hj'
    have hsL := RealBound.sqrt_len_gt j hj'
    have hE := arcsine_smooth_err hab t hε
    simp only [mid, rad]
    set L := RealBound.bT j - RealBound.aT j with hLdef
    have hL0 : 0 < L := by linarith
    have hI : π⁻¹ * ∫ θ in (0 : ℝ)..π,
        kC ε (t - ((RealBound.aT j + RealBound.bT j) / 2
          + (RealBound.bT j - RealBound.aT j) / 2 * Real.cos θ))
        ≤ Uarc (RealBound.aT j) (RealBound.bT j) t + 2 * ε / L
          + 2 * π * Real.sqrt (ε / L) := by
      rw [inv_mul_le_iff₀ hpi]; exact hE
    have h1 : 2 * ε / L ≤ 450 * ε := by
      rw [div_le_iff₀ hL0]; nlinarith
    have hsqL : 0 < Real.sqrt L := by linarith
    have h2 : Real.sqrt (ε / L) ≤ 15 * Real.sqrt ε := by
      rw [Real.sqrt_div' _ hL0.le, div_le_iff₀ hsqL]; nlinarith
    have h3 : 2 * π * Real.sqrt (ε / L) ≤ 95 * Real.sqrt ε := by
      have h4 : 2 * π * Real.sqrt (ε / L) ≤ 2 * π * (15 * Real.sqrt ε) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
      nlinarith
    rw [← mul_add]
    apply mul_le_mul_of_nonneg_left _ hc.le
    linarith
  calc ∑ j ∈ range 16, RealBound.cT j *
        (π⁻¹ * ∫ θ in (0 : ℝ)..π, kC ε (t - (mid j + rad j * Real.cos θ)))
      ≤ ∑ j ∈ range 16, (RealBound.cT j * Uarc (RealBound.aT j) (RealBound.bT j) t
          + RealBound.cT j * (450 * ε + 95 * Real.sqrt ε)) := Finset.sum_le_sum hterm
    _ = Urho t + (lam : ℝ) * (450 * ε + 95 * Real.sqrt ε) := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, RealBound.sum_cT, Urho]
    _ ≤ Urho t + 88 * Real.sqrt ε + 420 * ε := by
      norm_num [lam]; nlinarith

end

end Sec6
end Zeta5
