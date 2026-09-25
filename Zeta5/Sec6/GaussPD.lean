/-
Zeta5/Sec6/GaussPD.lean  —  positive definiteness of the Gaussian kernel.

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
`∫ e^{-2s(x-u)²} e^{-2s(y-u)²} du = √(π/(4s)) e^{-s(x-y)²}`. -/
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

private lemma gpd_k_le_one {s : ℝ} (hs : 0 < s) (x u : ℝ) :
    ‖Real.exp (-(2 * s * (x - u) ^ 2))‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg (x - u)])

private lemma gpd_k_int {s : ℝ} (hs : 0 < s) (x : ℝ) :
    Integrable (fun u => Real.exp (-(2 * s * (x - u) ^ 2))) := by
  have := (integrable_exp_neg_mul_sq (b := 2 * s) (by linarith)).comp_sub_right x
  refine this.congr (Filter.Eventually.of_forall fun u => ?_)
  simp only; congr 1; ring

private lemma gpd_k_integral (s : ℝ) (x : ℝ) :
    ∫ u, Real.exp (-(2 * s * (x - u) ^ 2)) = ∫ u, Real.exp (-(2 * s) * u ^ 2) := by
  have : (fun u => Real.exp (-(2 * s * (x - u) ^ 2)))
      = fun u => Real.exp (-(2 * s) * (u - x) ^ 2) := by
    funext u; congr 1; ring
  rw [this, integral_sub_right_eq_self (fun u => Real.exp (-(2 * s) * u ^ 2))]

/-- `g_μ(u) = ∫ e^{-2s(x-u)²} dμ(x)`. -/
private def gpdG (s : ℝ) (μ : Measure ℝ) (u : ℝ) : ℝ :=
  ∫ x, Real.exp (-(2 * s * (x - u) ^ 2)) ∂μ

private lemma gpdG_cont {s : ℝ} (hs : 0 < s) (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Continuous (gpdG s μ) := by
  refine continuous_of_dominated (bound := fun _ => 1) ?_ ?_ (integrable_const 1) ?_
  · intro u
    exact (by fun_prop : Continuous fun x => Real.exp (-(2 * s * (x - u) ^ 2))).aestronglyMeasurable
  · intro u; exact Filter.Eventually.of_forall fun x => gpd_k_le_one hs x u
  · exact Filter.Eventually.of_forall fun x => by fun_prop

private lemma gpdG_bdd {s : ℝ} (hs : 0 < s) (μ : Measure ℝ) [IsFiniteMeasure μ] (u : ℝ) :
    ‖gpdG s μ u‖ ≤ μ.real univ := by
  have := norm_integral_le_of_norm_le_const (μ := μ)
    (f := fun x => Real.exp (-(2 * s * (x - u) ^ 2)))
    (Filter.Eventually.of_forall fun x => gpd_k_le_one hs x u)
  simpa [gpdG] using this

private lemma gpdG_int {s : ℝ} (hs : 0 < s) (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Integrable (gpdG s μ) := by
  have hF : Integrable (fun p : ℝ × ℝ => Real.exp (-(2 * s * (p.1 - p.2) ^ 2)))
      (μ.prod volume) := by
    rw [integrable_prod_iff
      (by fun_prop : Continuous fun p : ℝ × ℝ =>
        Real.exp (-(2 * s * (p.1 - p.2) ^ 2))).aestronglyMeasurable]
    refine ⟨Filter.Eventually.of_forall fun x => gpd_k_int hs x, ?_⟩
    simp_rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), gpd_k_integral]
    exact integrable_const _
  exact hF.integral_prod_right

private lemma gpd_repr {s : ℝ} (hs : 0 < s) (μ ν : Measure ℝ) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] :
    gaussE s μ ν = (Real.sqrt (π / (4 * s)))⁻¹ * ∫ u, gpdG s μ u * gpdG s ν u := by
  set c := Real.sqrt (π / (4 * s)) with hc_def
  have hc : c ≠ 0 := (Real.sqrt_pos.2 (by positivity)).ne'
  have inner : ∀ x, ∫ y, Real.exp (-(s * (x - y) ^ 2)) ∂ν
      = c⁻¹ * ∫ u, Real.exp (-(2 * s * (x - u) ^ 2)) * gpdG s ν u := by
    intro x
    have h1 : ∀ y, Real.exp (-(s * (x - y) ^ 2)) = c⁻¹ * ∫ u,
        Real.exp (-(2 * s * (x - u) ^ 2)) * Real.exp (-(2 * s * (y - u) ^ 2)) := by
      intro y; rw [gauss_conv hs x y, ← hc_def, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
    simp_rw [h1]
    rw [integral_const_mul]; congr 1
    rw [integral_integral_swap]
    · congr 1; funext u; unfold gpdG; rw [integral_const_mul]
    · refine (integrable_prod_iff' (by fun_prop : Continuous fun p : ℝ × ℝ =>
        Real.exp (-(2 * s * (x - p.2) ^ 2)) *
          Real.exp (-(2 * s * (p.1 - p.2) ^ 2))).aestronglyMeasurable).2 ⟨Filter.Eventually.of_forall fun u => ?_, ?_⟩
      · refine Integrable.of_bound (by fun_prop) 1 (Filter.Eventually.of_forall fun y => ?_)
        simp only
        rw [norm_mul]
        calc _ ≤ 1 * 1 := mul_le_mul (gpd_k_le_one hs x u) (gpd_k_le_one hs y u)
              (norm_nonneg _) zero_le_one
          _ = 1 := by ring
      · simp_rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), integral_const_mul]
        exact (gpd_k_int hs x).mul_bdd (gpdG_cont hs ν).aestronglyMeasurable
          (Filter.Eventually.of_forall fun u => gpdG_bdd hs ν u)
  unfold gaussE
  simp_rw [inner]
  rw [integral_const_mul]; congr 1
  rw [integral_integral_swap]
  · congr 1; funext u; unfold gpdG; rw [integral_mul_const]
  · refine (integrable_prod_iff' (by
      have := gpdG_cont hs ν
      fun_prop : Continuous fun p : ℝ × ℝ =>
        Real.exp (-(2 * s * (p.1 - p.2) ^ 2)) * gpdG s ν p.2).aestronglyMeasurable).2 ⟨Filter.Eventually.of_forall fun u => ?_, ?_⟩
    · refine Integrable.of_bound
        ((by fun_prop : Continuous fun x => Real.exp (-(2 * s * (x - u) ^ 2)) * gpdG s ν u)
          ).aestronglyMeasurable (ν.real univ)
        (Filter.Eventually.of_forall fun x => ?_)
      simp only
      rw [norm_mul]
      calc _ ≤ 1 * ν.real univ := mul_le_mul (gpd_k_le_one hs x u) (gpdG_bdd hs ν u)
            (norm_nonneg _) zero_le_one
        _ = ν.real univ := by ring
    · have : (fun u => ∫ x, ‖Real.exp (-(2 * s * (x - u) ^ 2)) * gpdG s ν u‖ ∂μ)
          = fun u => gpdG s μ u * |gpdG s ν u| := by
        funext u
        simp_rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
        rw [integral_mul_const]; rfl
      rw [this]
      exact (gpdG_int hs μ).mul_bdd (gpdG_cont hs ν).abs.aestronglyMeasurable
        (Filter.Eventually.of_forall fun u => by simpa using gpdG_bdd hs ν u)

private lemma gpd_prod_int {s : ℝ} (hs : 0 < s) (μ ν : Measure ℝ) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] : Integrable (fun u => gpdG s μ u * gpdG s ν u) :=
  (gpdG_int hs μ).mul_bdd (gpdG_cont hs ν).aestronglyMeasurable
    (Filter.Eventually.of_forall fun u => gpdG_bdd hs ν u)

/-- **The Gaussian kernel is positive definite** on differences of finite
measures on `ℝ`: `G_s(α,α) − 2G_s(α,β) + G_s(β,β) ≥ 0`, where
`G_s(μ,ν) = ∫∫ e^{-s(x−y)²} dν(y) dμ(x)` (`gaussE`).

Paper: Lemma 6.2, proof, first display (p. 18).

Proof.  Put `g_μ(u) = ∫ e^{-2s(x−u)²} dμ(x)`, which is continuous, bounded by `μ(ℝ)` and
integrable.  By `gauss_conv` and Fubini, `gaussE s μ ν = √(4s/π) ∫ g_μ(u) g_ν(u) du` for all
finite `μ, ν`, so the combination equals `√(4s/π) ∫ (g_α − g_β)² du ≥ 0`.
Only finiteness of `α, β` is needed (no mass or support condition). -/
theorem gauss_pd (α β : Measure ℝ) [IsFiniteMeasure α] [IsFiniteMeasure β] {s : ℝ}
    (hs : 0 < s) :
    0 ≤ gaussE s α α - 2 * gaussE s α β + gaussE s β β := by
  rw [gpd_repr hs, gpd_repr hs, gpd_repr hs]
  have e : ∫ u, (gpdG s α u - gpdG s β u) ^ 2
      = (∫ u, gpdG s α u * gpdG s α u) - 2 * (∫ u, gpdG s α u * gpdG s β u)
        + ∫ u, gpdG s β u * gpdG s β u := by
    have : (fun u => (gpdG s α u - gpdG s β u) ^ 2) = fun u =>
        (gpdG s α u * gpdG s α u - 2 * (gpdG s α u * gpdG s β u)) + gpdG s β u * gpdG s β u := by
      funext u; ring
    rw [this, integral_add, integral_sub, integral_const_mul]
    · exact gpd_prod_int hs α α
    · exact (gpd_prod_int hs α β).const_mul 2
    · exact (gpd_prod_int hs α α).sub ((gpd_prod_int hs α β).const_mul 2)
    · exact gpd_prod_int hs β β
  have hnn : 0 ≤ ∫ u, (gpdG s α u - gpdG s β u) ^ 2 :=
    integral_nonneg fun u => sq_nonneg _
  have hc : 0 ≤ (Real.sqrt (π / (4 * s)))⁻¹ := inv_nonneg.2 (Real.sqrt_nonneg _)
  have := mul_nonneg hc hnn
  rw [e] at this
  linarith

end

end Sec6
end Zeta5
