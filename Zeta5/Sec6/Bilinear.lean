/-
Zeta5/Sec6/Bilinear.lean  —  LEAF: bilinear expansion of the kernel energy of `ρ`
(routine measure theory; no potential theory).
-/
import Zeta5.Sec6.Measures

namespace Zeta5
namespace Sec6

open Real MeasureTheory Set Finset

noncomputable section

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
  sorry

end

end Sec6
end Zeta5
