/-
Zeta5/Sec6/RhoCross.lean  —  LEAF: the cross term `∫ kC ε (t − y) dρ(y) ≤ U^ρ(t) + O(√ε)`.
-/
import Zeta5.Sec6.SmoothArc
import Zeta5.Sec6.Measures

namespace Zeta5
namespace Sec6

open Real MeasureTheory Set Finset

noncomputable section

/-- **LEAF (easy–medium; finite bookkeeping).**  For every real `t` and `ε > 0`,

`∫ kC ε (t − y) dρ(y) ≤ U^ρ(t) + 88√ε + 420ε`.

(Numerically the error is at most `0.02` of the allowed one.)

Paper: p. 19, `∫U^ρ dω_i − U^ρ(t_i) ≤ ∑_j 8c_j√(2ε)/(π√(b_j−a_j)) ≤ 60√ε` — the only place
where `b_j − a_j > 1/225` is used.

Proof plan.  `integral_rhoM` (with `continuous_kC`, composed with `t − ·`) rewrites the left
side as `∑_{j<16} c_j π⁻¹ ∫_0^π kC ε (t − (mid j + rad j cos θ)) dθ`; `mid j`, `rad j` unfold
to `(a_j+b_j)/2`, `(b_j−a_j)/2`, so `arcsine_smooth_err` (with `RealBound.aT_lt_bT`) bounds
each term by `c_j (Uarc a_j b_j t + 2ε/L_j + 2π√(ε/L_j))` (`RealBound.cT_pos`,
`mul_le_mul_of_nonneg_left`, `π⁻¹ π = 1`).  Summing, `∑ c_j Uarc = Urho t` and, with
`1/L_j < 225` (`RealBound.tab1_length`) and `√(1/L_j) < 15` (`RealBound.sqrt_len_gt`),
the error is `≤ ∑ c_j (450ε + 30π√ε) = λ(450ε + 30π√ε) ≤ 420ε + 88√ε`
(`RealBound.sum_cT`, `λ = 37/40`, `Real.pi_lt_d2 : π < 3.15`). -/
theorem rho_cross (t : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∫ y, kC ε (t - y) ∂rhoM ≤ Urho t + 88 * Real.sqrt ε + 420 * ε := by
  sorry

end

end Sec6
end Zeta5
