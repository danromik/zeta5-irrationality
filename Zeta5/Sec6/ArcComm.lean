/-
Zeta5/Sec6/ArcComm.lean  —  symmetry of the kernel energy between two arcsine components.
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

/-- Symmetry of the kernel energy between two components:
`I_k(ω_i, ω_j) = I_k(ω_j, ω_i)`.

Proof.  `(x, y) ↦ kC ε (x − y)` is continuous, hence bounded on the product of the (compact)
supports and integrable for the product measure; Fubini (`integral_integral_swap`) and
`kC_sub_comm` give the symmetry. -/
theorem kE_arc_comm (i j : ℕ) {ε : ℝ} (hε : 0 < ε) :
    kE ε (arc i) (arc j) = kE ε (arc j) (arc i) :=
  kE_arc_comm_aux _ _ _ _ hε

end

end Sec6
end Zeta5
