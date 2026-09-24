/-
Zeta5/Sec6/ArcComm.lean  —  LEAF: symmetry of the kernel energy between two arcsine components
(routine measure theory).
-/
import Zeta5.Sec6.Measures

namespace Zeta5
namespace Sec6

open Real MeasureTheory Set Finset

noncomputable section

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
    kE ε (arc i) (arc j) = kE ε (arc j) (arc i) := by
  sorry

end

end Sec6
end Zeta5
