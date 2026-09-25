/-
Zeta5/Sec6/Swap.lean  —  the Fubini–Tonelli step of the zero-mass energy argument.

Role in the proof of (6.14): the interchange `∬ L_{a,b}(|z−w|) dν dν = −½∫_a^b J(s)/s ds` in
the proof of Lemma 6.2 (p. 18), for the Cauchy kernel.  Because the kernel is bounded on the
(compact) supports, no truncation `a ↓ 0, b ↑ ∞` and no dominated convergence are needed.
-/
import Zeta5.Sec6.Defs

namespace Zeta5
namespace Sec6

open Real MeasureTheory Set

noncomputable section

/-- Pointwise bound for the Frullani integrand used in `swap_frullani`. -/
private lemma swap_frullani_bound {ε s d : ℝ} (hs : 0 < s) :
    ‖frF ε s d‖ ≤ d ^ 2 * Real.exp (-(ε ^ 2) * s) := by
  unfold frF
  have h1 : -(s * d ^ 2) + 1 ≤ Real.exp (-(s * d ^ 2)) := Real.add_one_le_exp _
  have h2 : Real.exp (-(s * d ^ 2)) ≤ 1 := by
    rw [Real.exp_le_one_iff]; have := sq_nonneg d; nlinarith
  have he : 0 < Real.exp (-(s * ε ^ 2)) := Real.exp_pos _
  have hnn : 0 ≤ Real.exp (-(s * ε ^ 2)) * (1 - Real.exp (-(s * d ^ 2))) / s := by
    apply div_nonneg _ hs.le; exact mul_nonneg he.le (by linarith)
  rw [Real.norm_eq_abs, abs_of_nonneg hnn, div_le_iff₀ hs]
  have : -(ε ^ 2) * s = -(s * ε ^ 2) := by ring
  rw [this]
  nlinarith [mul_le_mul_of_nonneg_left (show 1 - Real.exp (-(s * d ^ 2)) ≤ s * d ^ 2 by linarith) he.le]

/-- For finite measures `μ, ν` on `ℝ` carried by
`[−R, R]`, the `s`-integral of the Frullani integrand commutes with the double integral:

`∫∫ (∫_0^∞ frF ε s (x−y) ds) dν(y) dμ(x) = ∫_0^∞ (∫∫ frF ε s (x−y) dν(y) dμ(x)) ds`,

and the right-hand integrand is integrable on `(0,∞)`.

Paper: the interchange in the proof of Lemma 6.2 (p. 18): "These interchanges are justified by
the bounded Gaussian kernel and the finiteness of |ν|."

Proof.  On the supports `(x−y)² ≤ 4R²`, so by `swap_frullani_bound` the integrand
`(s, x, y) ↦ frF ε s (x − y)` is dominated on `(volume.restrict (Ioi 0)).prod (μ.prod ν)` by the
integrable function `4R² e^{-sε²}`; Fubini (`integral_prod`, `integral_integral_swap`) gives
both claims. -/
theorem swap_frullani (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν] {R ε : ℝ}
    (hε : 0 < ε) (hμ : ∀ᵐ x ∂μ, |x| ≤ R) (hν : ∀ᵐ y ∂ν, |y| ≤ R) :
    IntegrableOn (fun s => ∫ x, ∫ y, frF ε s (x - y) ∂ν ∂μ) (Ioi (0 : ℝ)) ∧
      ∫ x, ∫ y, (∫ s in Ioi (0 : ℝ), frF ε s (x - y)) ∂ν ∂μ
        = ∫ s in Ioi (0 : ℝ), ∫ x, ∫ y, frF ε s (x - y) ∂ν ∂μ := by
  classical
  set m : Measure ℝ := volume.restrict (Ioi (0 : ℝ)) with hm
  set F : ℝ × (ℝ × ℝ) → ℝ := fun q => frF ε q.1 (q.2.1 - q.2.2) with hF
  have hε2 : 0 < ε ^ 2 := by positivity
  have hmeas : Measurable F := by
    simp only [hF, frF]; fun_prop
  have hg : Integrable (fun q : ℝ × (ℝ × ℝ) =>
      ((4 * R ^ 2) * Real.exp (-(ε ^ 2) * q.1)) * (fun _ : ℝ × ℝ => (1 : ℝ)) q.2)
      (m.prod (μ.prod ν)) := by
    exact Integrable.mul_prod (L := ℝ) (f := fun s : ℝ => (4 * R ^ 2) * Real.exp (-(ε ^ 2) * s))
      (g := fun _ : ℝ × ℝ => (1 : ℝ))
      ((exp_neg_integrableOn_Ioi 0 hε2).const_mul _) (integrable_const (1 : ℝ))
  have hae : ∀ᵐ q ∂(m.prod (μ.prod ν)), q.1 ∈ Ioi (0 : ℝ) ∧ |q.2.1| ≤ R ∧ |q.2.2| ≤ R := by
    have h1 : ∀ᵐ q ∂(m.prod (μ.prod ν)), q.1 ∈ Ioi (0 : ℝ) :=
      Measure.QuasiMeasurePreserving.ae (Measure.quasiMeasurePreserving_fst)
        (ae_restrict_mem measurableSet_Ioi)
    have h2 : ∀ᵐ p ∂(μ.prod ν), |p.1| ≤ R ∧ |p.2| ≤ R := by
      have a := Measure.QuasiMeasurePreserving.ae
        (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := ν)) hμ
      have b := Measure.QuasiMeasurePreserving.ae
        (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := ν)) hν
      filter_upwards [a, b] with p ha hb using ⟨ha, hb⟩
    have h3 := Measure.QuasiMeasurePreserving.ae
      (Measure.quasiMeasurePreserving_snd (μ := m) (ν := μ.prod ν)) h2
    filter_upwards [h1, h3] with q hq1 hq3 using ⟨hq1, hq3⟩
  have hFi : Integrable F (m.prod (μ.prod ν)) := by
    refine hg.mono' hmeas.aestronglyMeasurable ?_
    filter_upwards [hae] with q ⟨hq, hx, hy⟩
    have hb := swap_frullani_bound (ε := ε) (d := q.2.1 - q.2.2) hq
    have hd : (q.2.1 - q.2.2) ^ 2 ≤ 4 * R ^ 2 := by
      have := abs_sub q.2.1 q.2.2
      have h0 : |q.2.1 - q.2.2| ≤ 2 * R := by linarith
      have h00 : 0 ≤ |q.2.1 - q.2.2| := abs_nonneg _
      calc (q.2.1 - q.2.2) ^ 2 = |q.2.1 - q.2.2| ^ 2 := (sq_abs _).symm
        _ ≤ (2 * R) ^ 2 := by gcongr
        _ = 4 * R ^ 2 := by ring
    simp only [hF, mul_one]
    exact hb.trans (mul_le_mul_of_nonneg_right hd (Real.exp_pos _).le)
  -- inner identities
  have hin : ∀ᵐ s ∂m, ∫ x, ∫ y, frF ε s (x - y) ∂ν ∂μ = ∫ p, F (s, p) ∂(μ.prod ν) := by
    filter_upwards [hFi.prod_right_ae] with s hs
    exact (integral_prod (fun p => F (s, p)) hs).symm
  have hout : ∫ x, ∫ y, (∫ s in Ioi (0 : ℝ), frF ε s (x - y)) ∂ν ∂μ
      = ∫ p, ∫ s, F (s, p) ∂m ∂(μ.prod ν) :=
    (integral_prod (fun p => ∫ s, F (s, p) ∂m) hFi.integral_prod_right).symm
  refine ⟨?_, ?_⟩
  · exact (hFi.integral_prod_left).congr (by filter_upwards [hin] with s hs using hs.symm)
  · rw [hout, integral_congr_ae hin]
    exact (MeasureTheory.integral_integral_swap (f := fun s p => F (s, p)) hFi).symm

end

end Sec6
end Zeta5
