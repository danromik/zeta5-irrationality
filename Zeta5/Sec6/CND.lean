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

/-- Auxiliary for `cauchy_cnd`: splitting a double integral of `a + b F(x−y)` for finite
measures carried by `[−R,R]` and continuous `F`. -/
private theorem cauchy_cnd_split (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {R : ℝ} (hμ : ∀ᵐ x ∂μ, |x| ≤ R) (hν : ∀ᵐ y ∂ν, |y| ≤ R) {F : ℝ → ℝ} (hF : Continuous F)
    (a b : ℝ) :
    ∫ x, ∫ y, (a + b * F (x - y)) ∂ν ∂μ
      = a * μ.real univ * ν.real univ + b * ∫ x, ∫ y, F (x - y) ∂ν ∂μ := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := -(2 * R)) (b := 2 * R)).exists_bound_of_continuousOn
    hF.continuousOn
  have hbd : ∀ x y : ℝ, |x| ≤ R → |y| ≤ R → ‖F (x - y)‖ ≤ M := by
    intro x y hx hy
    apply hM
    have := abs_sub x y
    have h2 := abs_le.1 (le_trans this (add_le_add hx hy))
    constructor <;> linarith [h2.1, h2.2]
  have hin : ∀ x, |x| ≤ R → Integrable (fun y => F (x - y)) ν := fun x hx =>
    Integrable.mono' (integrable_const M)
      (hF.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
      (hν.mono fun y hy => hbd x y hx hy)
  have hmeas : StronglyMeasurable (fun x => ∫ y, F (x - y) ∂ν) :=
    ((hF.comp continuous_sub).stronglyMeasurable).integral_prod_right'
      (f := fun p : ℝ × ℝ => F (p.1 - p.2))
  have hout : Integrable (fun x => ∫ y, F (x - y) ∂ν) μ :=
    Integrable.mono' (integrable_const (M * ν.real univ)) hmeas.aestronglyMeasurable
      (hμ.mono fun x hx => norm_integral_le_of_norm_le_const (hν.mono fun y hy => hbd x y hx hy))
  calc ∫ x, ∫ y, (a + b * F (x - y)) ∂ν ∂μ
      = ∫ x, (a * ν.real univ + b * ∫ y, F (x - y) ∂ν) ∂μ := by
        refine integral_congr_ae (hμ.mono fun x hx => ?_)
        simp only
        rw [integral_add (integrable_const _) ((hin x hx).const_mul b), integral_const,
          integral_const_mul, smul_eq_mul, mul_comm]
    _ = a * μ.real univ * ν.real univ + b * ∫ x, ∫ y, F (x - y) ∂ν ∂μ := by
        rw [integral_add (integrable_const _) (hout.const_mul b), integral_const,
          integral_const_mul, smul_eq_mul]
        ring

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
  set Φ : ℝ → ℝ := fun d => ∫ s in Ioi (0 : ℝ), frF ε s d with hΦdef
  have hΦc : Continuous Φ := by
    have : Φ = fun d => Real.log (1 + d ^ 2 / ε ^ 2) := funext fun d => frullani_cauchy hε d
    rw [this]
    exact ((continuous_const.add ((continuous_pow 2).div_const _)).log
      (fun d => ne_of_gt (by positivity : (0:ℝ) < 1 + d ^ 2 / ε ^ 2)))
  -- step 1
  have hk : ∀ (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν],
      (∀ᵐ x ∂μ, |x| ≤ R) → (∀ᵐ y ∂ν, |y| ≤ R) →
      kE ε μ ν = Real.log ε * μ.real univ * ν.real univ
        + (1 / 2) * ∫ s in Ioi (0 : ℝ), ∫ x, ∫ y, frF ε s (x - y) ∂ν ∂μ := by
    intro μ ν _ _ hμ hν
    have e1 : kE ε μ ν = ∫ x, ∫ y, (Real.log ε + (1 / 2) * Φ (x - y)) ∂ν ∂μ := by
      unfold kE
      congr 1; funext x; congr 1; funext y
      rw [kC_eq_frullani hε]; ring
    rw [e1, cauchy_cnd_split μ ν hμ hν hΦc, (swap_frullani μ ν hε hμ hν).2]
  -- step 3
  have hH : ∀ (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν],
      (∀ᵐ x ∂μ, |x| ≤ R) → (∀ᵐ y ∂ν, |y| ≤ R) → ∀ s, 0 < s →
      ∫ x, ∫ y, frF ε s (x - y) ∂ν ∂μ
        = Real.exp (-(s * ε ^ 2)) / s * μ.real univ * ν.real univ
          + (-(Real.exp (-(s * ε ^ 2)) / s)) * gaussE s μ ν := by
    intro μ ν _ _ hμ hν s hs
    have e1 : ∫ x, ∫ y, frF ε s (x - y) ∂ν ∂μ = ∫ x, ∫ y, (Real.exp (-(s * ε ^ 2)) / s
        + (-(Real.exp (-(s * ε ^ 2)) / s)) * (fun d => Real.exp (-(s * d ^ 2))) (x - y)) ∂ν ∂μ := by
      congr 1; funext x; congr 1; funext y
      unfold frF; ring
    rw [e1]
    exact cauchy_cnd_split μ ν hμ hν (F := fun d => Real.exp (-(s * d ^ 2))) (by fun_prop) _ _
  have hint := fun (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
      (hμ : ∀ᵐ x ∂μ, |x| ≤ R) (hν : ∀ᵐ y ∂ν, |y| ≤ R) => (swap_frullani μ ν hε hμ hν).1
  have hab : α.real univ = β.real univ := by simp [measureReal_def, hmass]
  rw [hk α α hα hα, hk α β hα hβ, hk β β hβ hβ, hab]
  have hcomb : (∫ s in Ioi (0 : ℝ), ∫ x, ∫ y, frF ε s (x - y) ∂α ∂α)
      - 2 * (∫ s in Ioi (0 : ℝ), ∫ x, ∫ y, frF ε s (x - y) ∂β ∂α)
      + (∫ s in Ioi (0 : ℝ), ∫ x, ∫ y, frF ε s (x - y) ∂β ∂β)
      = ∫ s in Ioi (0 : ℝ), ((∫ x, ∫ y, frF ε s (x - y) ∂α ∂α)
          - 2 * (∫ x, ∫ y, frF ε s (x - y) ∂β ∂α)
          + (∫ x, ∫ y, frF ε s (x - y) ∂β ∂β)) := by
    have h1 : IntegrableOn (fun s => (∫ x, ∫ y, frF ε s (x - y) ∂α ∂α)
        - 2 * (∫ x, ∫ y, frF ε s (x - y) ∂β ∂α)) (Ioi (0 : ℝ)) :=
      (hint α α hα hα).sub ((hint α β hα hβ).const_mul 2)
    have h2 : IntegrableOn (fun s => 2 * (∫ x, ∫ y, frF ε s (x - y) ∂β ∂α)) (Ioi (0 : ℝ)) :=
      (hint α β hα hβ).const_mul 2
    rw [integral_add h1 (hint β β hβ hβ), integral_sub (hint α α hα hα) h2, integral_const_mul]
  have hnp : (∫ s in Ioi (0 : ℝ), ((∫ x, ∫ y, frF ε s (x - y) ∂α ∂α)
          - 2 * (∫ x, ∫ y, frF ε s (x - y) ∂β ∂α)
          + (∫ x, ∫ y, frF ε s (x - y) ∂β ∂β))) ≤ 0 := by
    refine setIntegral_nonpos measurableSet_Ioi fun s hs => ?_
    have hs' : 0 < s := hs
    rw [hH α α hα hα s hs', hH α β hα hβ s hs', hH β β hβ hβ s hs', hab]
    have hc : 0 ≤ Real.exp (-(s * ε ^ 2)) / s := by positivity
    have hg := gauss_pd α β hs'
    nlinarith [mul_nonneg hc hg]
  nlinarith [hcomb, hnp]

end

end Sec6
end Zeta5
