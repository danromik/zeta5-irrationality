/-
Zeta5/Sec6/RhoEnergy.lean  —  `I(ρ) ≤ I_k(ρ,ρ)`: the energy of `ρ` for the regularised kernel
is at least the value (A.2), from `kE_rhoM_expand`, `kE_arc_comm`, `pair_energy_ge` and
`Irho_double_sum`.
-/
import Zeta5.Sec6.PairEnergy
import Zeta5.Sec6.Bilinear
import Zeta5.Sec6.ArcComm
import Zeta5.Sec6.IrhoSum

namespace Zeta5
namespace Sec6

open Real MeasureTheory Set Finset

noncomputable section

/-- **`I(ρ) ≤ I_k(ρ,ρ)`** for every `ε > 0` ((A.2) with the kernel `kC ε ≥ log|·|`). -/
theorem rho_energy_ge {ε : ℝ} (hε : 0 < ε) : RealBound.Irho ≤ kE ε rhoM rhoM := by
  rw [kE_rhoM_expand hε, Irho_double_sum]
  refine Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => ?_
  have hi' := Finset.mem_range.1 hi
  have hj' := Finset.mem_range.1 hj
  have hc : 0 ≤ RealBound.cT i * RealBound.cT j := mul_nonneg (cT_nonneg i) (cT_nonneg j)
  refine mul_le_mul_of_nonneg_left ?_ hc
  rcases le_total i j with h | h
  · rw [max_eq_right h]; exact pair_energy_ge h hj' hε
  · rw [max_eq_left h, kE_arc_comm i j hε]; exact pair_energy_ge h hi' hε

end

end Sec6
end Zeta5
