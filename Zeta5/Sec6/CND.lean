/-
Zeta5/Sec6/CND.lean  —  LEAF: zero-mass energy for the Cauchy kernel (replaces Lemma 6.2).

Paper: Lemma 6.2 (p. 18), `I(ν) ≤ 0` for a compactly supported real measure of mass zero with
`∬|log|z−w|| d|ν| d|ν| < ∞`.  We need it only for `ν = σ − ρ`, and we apply it to the
Cauchy-regularised kernel `kC ε`, which is bounded on compacts: no diagonal, no
log-integrability hypothesis, no truncation/dominated-convergence step.
-/
import Zeta5.Sec6.Frullani
import Zeta5.Sec6.GaussPD
import Zeta5.Sec6.Swap
import Zeta5.Sec6.Measures

namespace Zeta5
namespace Sec6

open Real MeasureTheory Set

noncomputable section

/-- `kC ε d = log ε + ½∫_0^∞ frF ε s d ds` (from `frullani_cauchy`). -/
theorem kC_eq_frullani {ε : ℝ} (hε : 0 < ε) (d : ℝ) :
    kC ε d = Real.log ε + (∫ s in Ioi (0 : ℝ), frF ε s d) / 2 := by
  rw [frullani_cauchy hε d]
  unfold kC
  have h1 : d ^ 2 + ε ^ 2 = ε ^ 2 * (1 + d ^ 2 / ε ^ 2) := by field_simp; ring
  rw [h1, Real.log_mul (by positivity) (by positivity), Real.log_pow]
  push_cast; ring

/-- **LEAF (medium).**  **Conditional negative definiteness of `kC ε`**: for finite measures
`α, β` on `ℝ` of equal total mass carried by `[−R, R]`,

`I_k(α,α) − 2 I_k(α,β) + I_k(β,β) ≤ 0`,   `I_k(μ,ν) = ∫∫ kC ε (x−y) dν(y) dμ(x)` (`kE`).

Paper: Lemma 6.2 (p. 18), (6.5), for `ν = α − β`.

Proof plan (the paper's proof, with the kernel bounded).  Write `a = (α univ).toReal`,
`b = (β univ).toReal` (so `a = b` by `hmass`).
1. By `kC_eq_frullani`, `kC ε (x−y) = log ε + ½Φ(x−y)` with `Φ(d) = ∫_0^∞ frF ε s d ds`.
   All inner and outer integrands are continuous in `x`, `y` and bounded on `[−R,R]²`
   (`continuous_kC`; `x ↦ ∫ kC ε (x−y) dν(y)` is continuous, e.g. by
   `continuous_parametric_integral_of_continuous` after restricting `ν` to `Icc (−R) R`),
   so `integral_add`, `integral_const`, `integral_const_mul` give
   `kE ε μ ν = log ε · m_μ m_ν + ½ ∫∫ Φ(x−y) dν dμ`.
2. `swap_frullani` turns `∫∫ Φ(x−y)` into `∫_0^∞ H_{μν}(s) ds` with
   `H_{μν}(s) = ∫∫ frF ε s (x−y) dν dμ`, integrable on `Ioi 0`.
3. For `s > 0`, `frF ε s (x−y) = (e^{-sε²}/s)(1 − e^{-s(x−y)²})`, so
   `H_{μν}(s) = (e^{-sε²}/s)(m_μ m_ν − gaussE s μ ν)`.
4. The combination: `log ε (a² − 2ab + b²) = 0`, and
   `H_{αα} − 2H_{αβ} + H_{ββ} = (e^{-sε²}/s)((a−b)² − [G_s(α,α) − 2G_s(α,β) + G_s(β,β)])
   = −(e^{-sε²}/s)[…] ≤ 0` by `gauss_pd`.  Conclude with `integral_add`/`integral_sub`
   (integrability from step 2) and `setIntegral_nonpos`. -/
theorem cauchy_cnd (α β : Measure ℝ) [IsFiniteMeasure α] [IsFiniteMeasure β] {R : ℝ}
    (hα : ∀ᵐ x ∂α, |x| ≤ R) (hβ : ∀ᵐ x ∂β, |x| ≤ R) (hmass : α univ = β univ)
    {ε : ℝ} (hε : 0 < ε) :
    kE ε α α - 2 * kE ε α β + kE ε β β ≤ 0 := by
  sorry

end

end Sec6
end Zeta5
