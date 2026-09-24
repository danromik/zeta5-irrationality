/-
Zeta5/Sec6/Bilinear.lean  —  LEAF: bilinear expansion of the kernel energy of `ρ`
(routine measure theory; no potential theory).
-/
import Zeta5.Sec6.Measures

namespace Zeta5
namespace Sec6

open Real MeasureTheory Set Finset

noncomputable section

theorem kE_rhoM_expand_intRho {f : ℝ → ℝ} (hf : Continuous f) :
    ∫ x, f x ∂rhoM = ∑ j ∈ range 16, RealBound.cT j * ∫ x, f x ∂(arc j) := by
  unfold rhoM
  rw [integral_finsetSum_measure fun j _ =>
    (show Integrable f (arc j) from integrable_arcsine _ _ hf).smul_measure_nnreal]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_smul_nnreal_measure, NNReal.smul_def, Real.coe_toNNReal _ (cT_nonneg j),
    smul_eq_mul]

theorem kE_rhoM_expand_kC_cont {ε : ℝ} (hε : 0 < ε) : Continuous (kC ε) := by
  unfold kC
  refine Continuous.div_const (Continuous.log (by fun_prop) fun x => ?_) _
  positivity

theorem kE_rhoM_expand_gcont {ε : ℝ} (hε : 0 < ε) (j : ℕ) :
    Continuous fun x => ∫ y, kC ε (x - y) ∂(arc j) := by
  have hk := kE_rhoM_expand_kC_cont hε
  have : (fun x => ∫ y, kC ε (x - y) ∂(arc j)) = fun x =>
      π⁻¹ * ∫ θ in (0 : ℝ)..π, kC ε (x - (mid j + rad j * Real.cos θ)) := by
    funext x
    rw [arc, integral_arcsine _ _ (f := fun y => kC ε (x - y))
      (hk.comp (by fun_prop : Continuous fun y => x - y)).measurable]
  rw [this]
  refine continuous_const.mul ?_
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun x θ => kC ε (x - (mid j + rad j * Real.cos θ)))
    (hk.comp (by fun_prop)) _ _

/-- **LEAF (medium; bilinearity).**  `I_k(ρ,ρ) = ∑_{i,j<16} c_i c_j I_k(ω_i, ω_j)`.

Proof plan.  Inner integral: for each `x`, `∫ kC ε (x − y) dρ(y) = ∑_j c_j ∫ kC ε (x−y) dω_j(y)`
(`integral_finsetSum_measure`, `integral_smul_nnreal_measure`, `integrable_arcsine`,
`Real.coe_toNNReal`, `cT_nonneg`) — the same computation as `integral_rhoM`, before applying
`integral_arcsine`.  Outer integral: the same expansion over `ρ` applied to the function
`x ↦ ∑_j c_j g_j(x)`, where each `g_j(x) = ∫ kC ε (x − y) dω_j(y)` is continuous (write it as
`π⁻¹ ∫_0^π kC ε (x − (m_j + r_j cos θ)) dθ` by `integral_arcsine` and use
`intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'`), so integrable against every `ω_i`; then `integral_finset_sum`,
`integral_const_mul`, and `Finset.mul_sum`. -/
theorem kE_rhoM_expand {ε : ℝ} (hε : 0 < ε) :
    kE ε rhoM rhoM = ∑ i ∈ range 16, ∑ j ∈ range 16,
      RealBound.cT i * RealBound.cT j * kE ε (arc i) (arc j) := by
  have hk := kE_rhoM_expand_kC_cont hε
  have hin : ∀ x, ∫ y, kC ε (x - y) ∂rhoM
      = ∑ j ∈ range 16, RealBound.cT j * ∫ y, kC ε (x - y) ∂(arc j) := fun x =>
    kE_rhoM_expand_intRho (hk.comp (by fun_prop))
  unfold kE
  simp_rw [hin]
  have hc : Continuous fun x => ∑ j ∈ range 16, RealBound.cT j * ∫ y, kC ε (x - y) ∂(arc j) :=
    continuous_finsetSum _ fun j _ => continuous_const.mul (kE_rhoM_expand_gcont hε j)
  rw [kE_rhoM_expand_intRho hc]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ =>
    (show Integrable _ (arc i) from
      integrable_arcsine _ _ (kE_rhoM_expand_gcont hε j)).const_mul _, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul]
  ring

end

end Sec6
end Zeta5
