/-
Zeta5/Sec6/ArcComm.lean  —  LEAF: symmetry of the kernel energy between two arcsine components
(routine measure theory).
-/
import Zeta5.Sec6.Measures

namespace Zeta5
namespace Sec6

open Real MeasureTheory Set Finset

noncomputable section

private theorem kE_arc_comm_aux (m r m' r' : ℝ) {ε : ℝ} (hε : 0 < ε) :
    kE ε (arcsine m r) (arcsine m' r') = kE ε (arcsine m' r') (arcsine m r) := by
  have hc : Continuous (fun p : ℝ × ℝ => kC ε (p.1 - p.2)) :=
    (continuous_kC hε.ne').comp (continuous_fst.sub continuous_snd)
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod (isCompact_Icc (a := m' - |r'|) (b := m' + |r'|))
    |>.exists_bound_of_continuousOn (hc.continuousOn (s := Icc (m - |r|) (m + |r|) ×ˢ _)))
  have h1 : ∀ᵐ p ∂((arcsine m r).prod (arcsine m' r')), p.1 ∈ Icc (m - |r|) (m + |r|) :=
    Measure.quasiMeasurePreserving_fst.ae (arcsine_ae m r)
  have h2 : ∀ᵐ p ∂((arcsine m r).prod (arcsine m' r')), p.2 ∈ Icc (m' - |r'|) (m' + |r'|) :=
    Measure.quasiMeasurePreserving_snd.ae (arcsine_ae m' r')
  have hint : Integrable (Function.uncurry fun x y => kC ε (x - y))
      ((arcsine m r).prod (arcsine m' r')) := by
    refine Integrable.of_bound hc.aestronglyMeasurable C ?_
    filter_upwards [h1, h2] with p hp1 hp2
    exact hC p ⟨hp1, hp2⟩
  unfold kE
  rw [integral_integral_swap hint]
  simp_rw [kC_sub_comm ε]

/-- **LEAF (easy–medium).**  Symmetry of the kernel energy between two components:
`I_k(ω_i, ω_j) = I_k(ω_j, ω_i)`.

Proof plan.  By `integral_arcsine` (twice; the outer function
`x ↦ ∫ kC ε (x − y) dω(y)` is continuous: write it as
`π⁻¹ ∫_0^π kC ε (x − (m + r cos θ)) dθ` and use
`intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'`) both sides are
`π⁻² ∫_0^π∫_0^π` of a continuous function of `(θ, φ)`; swap with
`MeasureTheory.integral_integral_swap` (a continuous function on the compact `[0,π]²` is
integrable for the finite product measure: `ContinuousOn.integrableOn_compact`, or
`intervalIntegral`-level `integral_integral_swap` after `intervalIntegral.integral_of_le`), and
use `kC_sub_comm`. -/
theorem kE_arc_comm (i j : ℕ) {ε : ℝ} (hε : 0 < ε) :
    kE ε (arc i) (arc j) = kE ε (arc j) (arc i) :=
  kE_arc_comm_aux _ _ _ _ hε

end

end Sec6
end Zeta5
