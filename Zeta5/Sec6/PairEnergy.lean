/-
Zeta5/Sec6/PairEnergy.lean  —  LEAVES: the kernel energy of `ρ`, pair by pair.

Only the ON-interval branch of (A.1) is needed here, together with the nesting of Table 1.
-/
import Zeta5.Sec6.ArcsinePot
import Zeta5.Sec6.Measures

namespace Zeta5
namespace Sec6

open Real MeasureTheory Set Finset

noncomputable section

/-- **LEAF (medium).**  For nested components `i ≤ j < 16` (so `[a_i,b_i] ⊆ [a_j,b_j]`):

`log(L_j/4) ≤ I_k(ω_i, ω_j) = ∫∫ kC ε (x − y) dω_j(y) dω_i(x)`.

(Numerically e.g. `I_k(ω_0,ω_{15}) = −1.6636 ≥ −1.6786` at `ε = 10⁻³`.)

Paper: (A.2) (p. 22), "Nesting makes the potential of the `j`th interval constant on every
earlier interval", in the direction `≥` and for the regularised kernel.

Proof plan.
1. Nesting: `aT j ≤ aT i` and `bT i ≤ bT j` for `i ≤ j < 16` (induction on `j − i` from
   `RealBound.aT_strictAnti`, `RealBound.bT_strictMono`), so by `arc_ae` a.e. `x` under
   `arc i` lies in `[aT j, bT j]`.
2. For `x ∈ [aT j, bT j]`: `∫ kC ε (x − y) dω_j(y) ≥ log(L_j/4)`.  By `integral_arcsine`
   (`continuous_kC`) it is `π⁻¹ ∫_0^π kC ε (x − (m_j + r_j cos θ)) dθ`; pointwise
   `kC ε u ≥ log|u|` for `u ≠ 0` (`log_abs_le_kC`), and `u = 0` for at most one `θ ∈ [0,π]`
   (`Real.injOn_cos`), so `intervalIntegral.integral_mono_ae_restrict` (integrability:
   `(arcsine_pot _ x).1` and continuity) gives `≥ π⁻¹ ∫_0^π log|x − …| = Uarc a_j b_j x`
   (`(arcsine_pot _ x).2`), which is `log(L_j/4)` on the interval (`Uarc`, `if_pos`).
3. Integrate over `x ∼ ω_i` (a probability measure, `arcsine_univ`): `integral_mono_ae` with
   the constant function.  Integrability of `g(x) = ∫ kC ε (x − y) dω_j(y)`: it is continuous
   (write it as `π⁻¹ ∫_0^π kC ε (x − (m_j + r_j cos θ)) dθ` and use
   `intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'`), hence
   integrable (`integrable_arcsine`).  (Alternatively: `log(L_j/4) < 0`, so if `g` were not
   integrable the claim would hold trivially with `integral_undef`.) -/
theorem pair_energy_ge {i j : ℕ} (hij : i ≤ j) (hj : j < 16) {ε : ℝ} (hε : 0 < ε) :
    Real.log ((RealBound.bT j - RealBound.aT j) / 4) ≤ kE ε (arc i) (arc j) := by
  sorry

end

end Sec6
end Zeta5
