/-
Zeta5/Sec6/GaussPD.lean  —  LEAF: positive definiteness of the Gaussian kernel.

Role in the proof of (6.14): this is the first display of the proof of Lemma 6.2 (p. 18),
`J(s) = ∬ e^{-s|z-w|²} dν dν = (4s/π)∫(∫ e^{-2s|z-u|²} dν(z))² dA(u) ≥ 0`, on the real line
and for `ν = α − β` written out as three mutual energies (no signed measures).
-/
import Zeta5.Sec6.Defs

namespace Zeta5
namespace Sec6

open Real MeasureTheory Set

noncomputable section

/-- Completing the square (the only algebra behind Gaussian positive-definiteness):
`∫ e^{-2s(x-u)²} e^{-2s(y-u)²} du = √(π/(4s)) e^{-s(x-y)²}`.  (Proved.) -/
theorem gauss_conv {s : ℝ} (_hs : 0 < s) (x y : ℝ) :
    ∫ u, Real.exp (-(2 * s * (x - u) ^ 2)) * Real.exp (-(2 * s * (y - u) ^ 2))
      = Real.sqrt (π / (4 * s)) * Real.exp (-(s * (x - y) ^ 2)) := by
  have key : ∀ u, Real.exp (-(2 * s * (x - u) ^ 2)) * Real.exp (-(2 * s * (y - u) ^ 2))
      = Real.exp (-(s * (x - y) ^ 2)) * Real.exp (-(4 * s) * (u - (x + y) / 2) ^ 2) := by
    intro u; rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  simp_rw [key]
  rw [integral_const_mul, integral_sub_right_eq_self (fun u => Real.exp (-(4 * s) * u ^ 2)),
    integral_gaussian]
  ring

/-- **LEAF (medium).**  **The Gaussian kernel is positive definite** on differences of finite
measures on `ℝ`: `G_s(α,α) − 2G_s(α,β) + G_s(β,β) ≥ 0`, where
`G_s(μ,ν) = ∫∫ e^{-s(x−y)²} dν(y) dμ(x)` (`gaussE`).

Paper: Lemma 6.2, proof, first display (p. 18).

Proof plan.  Put `g_μ(u) = ∫ e^{-2s(x−u)²} dμ(x)`; `0 ≤ g_μ ≤ μ(ℝ)` and
`∫ g_μ du = μ(ℝ)√(π/(2s))` (Tonelli), so `g_μ g_ν` is integrable.
1. `gaussE s μ ν = √(4s/π) ∫ g_μ(u) g_ν(u) du` for all finite `μ, ν`: insert `gauss_conv`
   (note `√(π/(4s))⁻¹ = √(4s/π)`), then `MeasureTheory.integral_integral_swap` twice.  The
   triple integrand `(x,y,u) ↦ e^{-2s(x−u)²}e^{-2s(y−u)²}` is continuous (so strongly
   measurable) and bounded by `e^{-2s(x−u)²}`, whose integral over `μ ⊗ ν ⊗ volume` is
   `μ(ℝ)ν(ℝ)√(π/(2s)) < ∞` (`integral_gaussian`, `integrable_exp_neg_mul_sq`,
   `Integrable.comp_sub_right`); use `integrable_prod_iff` / `Integrable.mono'`.
2. Hence the combination equals `√(4s/π) ∫ (g_α − g_β)² du ≥ 0` (`integral_sub`,
   `integral_mul_left`, `integral_nonneg` with `sq_nonneg`).
Only finiteness of `α, β` is needed (no mass or support condition). -/
theorem gauss_pd (α β : Measure ℝ) [IsFiniteMeasure α] [IsFiniteMeasure β] {s : ℝ}
    (hs : 0 < s) :
    0 ≤ gaussE s α α - 2 * gaussE s α β + gaussE s β β := by
  sorry

end

end Sec6
end Zeta5
