/-
Zeta5/Sec6/Measures.lean  —  elementary facts about the measures of `Sec6/Defs.lean`:
mass, support, and integrals against `arcsine`, `rhoM` and `pts`.

THIS FILE CONTAINS NO `sorry`.
-/
import Zeta5.Sec6.Defs

namespace Zeta5
namespace Sec6

open Real MeasureTheory Set Finset
open scoped NNReal ENNReal

noncomputable section

theorem measurable_cosMap (m r : ℝ) : Measurable (fun θ : ℝ => m + r * Real.cos θ) := by
  fun_prop

theorem continuous_cosMap (m r : ℝ) : Continuous (fun θ : ℝ => m + r * Real.cos θ) := by
  fun_prop

/-! ## The arcsine measure -/

theorem arcsine_univ (m r : ℝ) : arcsine m r univ = 1 := by
  unfold arcsine
  rw [Measure.smul_apply, Measure.map_apply (measurable_cosMap m r) MeasurableSet.univ,
    preimage_univ, Measure.restrict_apply_univ, Real.volume_Icc, sub_zero, ENNReal.smul_def,
    smul_eq_mul]
  change ENNReal.ofReal π⁻¹ * ENNReal.ofReal π = 1
  rw [← ENNReal.ofReal_mul (inv_nonneg.2 pi_pos.le), inv_mul_cancel₀ pi_pos.ne',
    ENNReal.ofReal_one]

instance (m r : ℝ) : IsProbabilityMeasure (arcsine m r) := ⟨arcsine_univ m r⟩

/-- `∫ f dω = (1/π)∫_0^π f(m + r cos θ) dθ`. -/
theorem integral_arcsine (m r : ℝ) {f : ℝ → ℝ} (hf : Measurable f) :
    ∫ x, f x ∂(arcsine m r) = π⁻¹ * ∫ θ in (0 : ℝ)..π, f (m + r * Real.cos θ) := by
  unfold arcsine
  rw [integral_smul_nnreal_measure,
    integral_map (measurable_cosMap m r).aemeasurable hf.aestronglyMeasurable,
    intervalIntegral.integral_of_le pi_pos.le, integral_Icc_eq_integral_Ioc, NNReal.smul_def,
    Real.coe_toNNReal _ (inv_nonneg.2 pi_pos.le), smul_eq_mul]

theorem integrable_arcsine (m r : ℝ) {f : ℝ → ℝ} (hf : Continuous f) :
    Integrable f (arcsine m r) := by
  unfold arcsine
  refine Integrable.smul_measure_nnreal ?_
  rw [integrable_map_measure hf.aestronglyMeasurable (measurable_cosMap m r).aemeasurable]
  exact (hf.comp (continuous_cosMap m r)).integrableOn_Icc

/-- The arcsine measure lives on `[m − |r|, m + |r|]`. -/
theorem arcsine_ae (m r : ℝ) : ∀ᵐ x ∂(arcsine m r), x ∈ Icc (m - |r|) (m + |r|) := by
  unfold arcsine
  refine Measure.ae_smul_measure ?_ _
  refine (ae_map_iff (measurable_cosMap m r).aemeasurable measurableSet_Icc).2 ?_
  refine Filter.Eventually.of_forall fun θ => ?_
  have h : |r * Real.cos θ| ≤ |r| := by
    rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (abs_cos_le_one θ)
  have h1 := neg_abs_le (r * Real.cos θ)
  have h2 := le_abs_self (r * Real.cos θ)
  constructor <;> linarith

/-! ## `ω_j` and `ρ` -/

theorem cT_nonneg (j : ℕ) : 0 ≤ RealBound.cT j := by
  by_cases hj : j < 16
  · exact (RealBound.cT_pos j hj).le
  · simp only [RealBound.cT]
    split <;> norm_num

theorem aT_le_bT {j : ℕ} (hj : j < 16) : RealBound.aT j ≤ RealBound.bT j :=
  (RealBound.aT_lt_bT j hj).le

theorem rad_nonneg {j : ℕ} (hj : j < 16) : 0 ≤ rad j := by
  unfold rad; linarith [aT_le_bT hj]

theorem mid_sub_rad {j : ℕ} (hj : j < 16) : mid j - |rad j| = RealBound.aT j := by
  rw [abs_of_nonneg (rad_nonneg hj)]; unfold mid rad; ring

theorem mid_add_rad {j : ℕ} (hj : j < 16) : mid j + |rad j| = RealBound.bT j := by
  rw [abs_of_nonneg (rad_nonneg hj)]; unfold mid rad; ring

theorem arc_ae {j : ℕ} (hj : j < 16) :
    ∀ᵐ x ∂(arc j), x ∈ Icc (RealBound.aT j) (RealBound.bT j) := by
  have := arcsine_ae (mid j) (rad j)
  rwa [mid_sub_rad hj, mid_add_rad hj] at this

/-- Every interval of Table 1 lies in `(0, 2)`. -/
theorem tab1_in_02 {j : ℕ} (hj : j < 16) : 0 < RealBound.aT j ∧ RealBound.bT j < 2 := by
  interval_cases j <;> norm_num [RealBound.aT, RealBound.bT]

theorem rhoM_univ : rhoM univ = ENNReal.ofReal (lam : ℝ) := by
  unfold rhoM
  rw [Measure.finsetSum_apply]
  have : ∀ j ∈ range 16, ((RealBound.cT j).toNNReal • arc j) univ
      = ENNReal.ofReal (RealBound.cT j) := by
    intro j _
    rw [Measure.smul_apply, arc, arcsine_univ, ENNReal.smul_def, smul_eq_mul, mul_one]; rfl
  rw [Finset.sum_congr rfl this, ← ENNReal.ofReal_sum_of_nonneg (fun j _ => cT_nonneg j),
    RealBound.sum_cT]

theorem rhoM_ae : ∀ᵐ x ∂rhoM, |x| ≤ 2 := by
  rw [ae_iff]
  unfold rhoM
  rw [Measure.finsetSum_apply]
  refine Finset.sum_eq_zero fun j hj => ?_
  have hj' := Finset.mem_range.1 hj
  obtain ⟨h0, h2⟩ := tab1_in_02 hj'
  have hnull : arc j {x | ¬ |x| ≤ 2} = 0 := by
    refine measure_mono_null ?_ (ae_iff.1 (arc_ae hj'))
    intro x hx hmem
    have hx' : 2 < |x| := lt_of_not_ge hx
    obtain ⟨h3, h4⟩ := hmem
    rw [abs_of_pos (by linarith)] at hx'
    linarith
  rw [Measure.smul_apply, hnull, smul_zero]

/-- `∫ f dρ = ∑_j c_j (1/π)∫_0^π f(m_j + r_j cos θ) dθ` for continuous `f`. -/
theorem integral_rhoM {f : ℝ → ℝ} (hf : Continuous f) :
    ∫ x, f x ∂rhoM
      = ∑ j ∈ range 16, RealBound.cT j * (π⁻¹ * ∫ θ in (0 : ℝ)..π, f (mid j + rad j * Real.cos θ)) := by
  unfold rhoM
  rw [integral_finsetSum_measure fun j _ =>
    (show Integrable f (arc j) from integrable_arcsine _ _ hf).smul_measure_nnreal]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_smul_nnreal_measure, NNReal.smul_def, Real.coe_toNNReal _ (cT_nonneg j),
    smul_eq_mul, arc, integral_arcsine _ _ hf.measurable]

/-! ## The empirical measure -/

theorem integral_pts {m : ℕ} {K : ℝ} (hK : 0 < K) (t : Fin m → ℝ) (f : ℝ → ℝ) :
    ∫ x, f x ∂(pts K t) = K⁻¹ * ∑ i, f (t i) := by
  unfold pts
  rw [integral_finsetSum_measure fun i _ =>
    (integrable_dirac (by simp)).smul_measure_nnreal, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_smul_nnreal_measure, NNReal.smul_def, Real.coe_toNNReal _ (inv_nonneg.2 hK.le),
    smul_eq_mul, integral_dirac]

theorem pts_univ {m : ℕ} (K : ℝ) (t : Fin m → ℝ) :
    pts K t univ = ENNReal.ofReal ((m : ℝ) / K) := by
  unfold pts
  rw [Measure.finsetSum_apply]
  simp only [Measure.smul_apply, measure_univ, ENNReal.smul_def, smul_eq_mul, mul_one]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, div_eq_mul_inv,
    ENNReal.ofReal_mul (Nat.cast_nonneg m), ENNReal.ofReal_natCast]
  rfl

theorem pts_ae {m : ℕ} (K : ℝ) (t : Fin m → ℝ) {R : ℝ} (hR : ∀ i, |t i| ≤ R) :
    ∀ᵐ x ∂(pts K t), |x| ≤ R := by
  rw [ae_iff]
  unfold pts
  rw [Measure.finsetSum_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [Measure.smul_apply, Measure.dirac_apply,
    Set.indicator_of_notMem (by simpa using hR i), smul_zero]

end

end Sec6
end Zeta5
