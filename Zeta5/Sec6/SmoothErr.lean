/-
Zeta5/Sec6/SmoothErr.lean  —  the normalised smoothing error of the Cauchy kernel
against the arcsine measure of `[−1,1]` (in place of the paper's mass bound and
`∫U^ρ dω_i − U^ρ(t_i) ≤ 60√ε`, p. 19).
-/
import Zeta5.Sec6.SmoothAux
import Zeta5.Sec6.Antideriv

namespace Zeta5
namespace Sec6

open Real MeasureTheory Set

noncomputable section

/-- Normalised smoothing error: for every real `x` and `δ > 0`,

`∫_0^π ½ log(1 + δ²/(x − cos θ)²) dθ ≤ π (δ + π √(2δ))`,

with integrability.

Paper: in place of the arcsine mass bound `ω([x−r, x+r]) ≤ 4√(2r)/(π√L)` and its integration
in `r` (p. 19).

Proof.  Take `θ₀` from `exists_nearest_cos x`, so that
`|x − cos θ| ≥ |cos θ₀ − cos θ| ≥ 2(θ − θ₀)²/π²` on `[0,π]` (`cos_sub_cos_ge`).  With
`b = π√(2δ)/2` (`b² = δπ²/2`) and `½ log(1 + A²) ≤ log(1 + A)` for `A ≥ 0`, this gives
`½ log(1 + δ²/(x − cos θ)²) ≤ log(1 + b²/(θ − θ₀)²)` for `θ ≠ θ₀`, which also yields
integrability.  The right side integrates over `[0,π]` to at most `2∫_0^π log(1 + b²/u²) du`,
and by `integral_log_one_add_sq_div` that is `≤ 2(b²/π + πb) = π(δ + π√(2δ))`. -/
theorem smooth_err_norm (x : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    IntervalIntegrable (fun θ => Real.log (1 + δ ^ 2 / (x - Real.cos θ) ^ 2)) volume 0 π ∧
      ∫ θ in (0 : ℝ)..π, Real.log (1 + δ ^ 2 / (x - Real.cos θ) ^ 2) / 2
        ≤ π * (δ + π * Real.sqrt (2 * δ)) := by
  have hpi := Real.pi_pos
  obtain ⟨θ₀, ⟨h0, h0'⟩, hnear⟩ := exists_nearest_cos x
  set b : ℝ := π * Real.sqrt (2 * δ) / 2 with hbdef
  have hs : 0 < Real.sqrt (2 * δ) := Real.sqrt_pos.2 (by linarith)
  have hsq : Real.sqrt (2 * δ) ^ 2 = 2 * δ := Real.sq_sqrt (by linarith)
  have hb : 0 < b := by positivity
  have hb2 : b ^ 2 = δ * π ^ 2 / 2 := by rw [hbdef, div_pow, mul_pow, hsq]; ring
  set g : ℝ → ℝ := fun u => Real.log (1 + b ^ 2 / u ^ 2) with hgdef
  set f : ℝ → ℝ := fun θ => Real.log (1 + δ ^ 2 / (x - Real.cos θ) ^ 2) with hfdef
  have gnn : ∀ u, 0 ≤ g u := fun u => Real.log_nonneg (by linarith [show 0 ≤ b ^ 2 / u ^ 2 by positivity])
  have fnn : ∀ θ, 0 ≤ f θ := fun θ => Real.log_nonneg (by linarith [show 0 ≤ δ ^ 2 / (x - Real.cos θ) ^ 2 by positivity])
  have geven : ∀ u, g (-u) = g u := fun u => by simp [hgdef]
  have gint : ∀ X, 0 ≤ X → IntervalIntegrable g volume 0 X := fun X hX =>
    (integral_log_one_add_sq_div hb hX).1
  have gval : ∀ X, 0 ≤ X → ∫ u in (0:ℝ)..X, g u = X * Real.log (1 + b ^ 2 / X ^ 2) + 2 * b * Real.arctan (X / b) :=
    fun X hX => (integral_log_one_add_sq_div hb hX).2
  -- pointwise bound
  have pt : ∀ θ ∈ Icc (0:ℝ) π, θ ≠ θ₀ → f θ ≤ 2 * g (θ - θ₀) := by
    intro θ ⟨h1, h2⟩ hne
    have hu : 0 < (θ - θ₀) ^ 2 := by
      have : θ - θ₀ ≠ 0 := sub_ne_zero.2 hne
      positivity
    have hc := cos_sub_cos_ge h1 h2 h0 h0'
    have hd : 2 * (θ - θ₀) ^ 2 / π ^ 2 ≤ |x - Real.cos θ| := hc.trans (hnear θ)
    have hdpos : 0 < |x - Real.cos θ| := lt_of_lt_of_le (by positivity) hd
    set d := |x - Real.cos θ|
    set A := δ / d
    have hA0 : 0 ≤ A := by positivity
    have hA : A ≤ b ^ 2 / (θ - θ₀) ^ 2 := by
      rw [hb2, div_le_div_iff₀ hdpos hu]
      have := mul_le_mul_of_nonneg_left hd (le_of_lt (show 0 < δ * π ^ 2 / 2 by positivity))
      have e : δ * π ^ 2 / 2 * (2 * (θ - θ₀) ^ 2 / π ^ 2) = δ * (θ - θ₀) ^ 2 := by
        field_simp
      linarith
    have hfA : f θ = Real.log (1 + A ^ 2) := by
      simp only [hfdef, A, div_pow, d, sq_abs]
    rw [hfA]
    calc Real.log (1 + A ^ 2) ≤ Real.log ((1 + A) ^ 2) :=
          Real.log_le_log (by positivity) (by nlinarith)
      _ = 2 * Real.log (1 + A) := by rw [Real.log_pow]; norm_num
      _ ≤ 2 * g (θ - θ₀) := by
          have := Real.log_le_log (by linarith) (show 1 + A ≤ 1 + b ^ 2 / (θ - θ₀) ^ 2 by linarith)
          simp only [hgdef]; linarith
  have ae_pt : ∀ᵐ θ ∂(volume.restrict (Icc (0:ℝ) π)), f θ ≤ 2 * g (θ - θ₀) := by
    have h1 : ∀ᵐ θ ∂(volume.restrict (Icc (0:ℝ) π)), θ ∈ Icc (0:ℝ) π :=
      ae_restrict_mem measurableSet_Icc
    have h2 : ∀ᵐ θ ∂(volume.restrict (Icc (0:ℝ) π)), θ ∉ ({θ₀} : Set ℝ) :=
      ae_restrict_of_ae ((Set.countable_singleton θ₀).ae_notMem volume)
    filter_upwards [h1, h2] with θ hθ hθ'
    exact pt θ hθ hθ'
  -- integrability of g on [-θ₀, 0]
  have gneg : IntervalIntegrable g volume (-θ₀) 0 := by
    have := (gint θ₀ h0).comp_mul_left (c := -1)
    have e : (fun x => g (-1 * x)) = g := by funext u; rw [neg_one_mul, geven]
    rw [e] at this
    simpa [div_neg, div_one] using this.symm
  have gshift : IntervalIntegrable (fun θ => g (θ - θ₀)) volume 0 π := by
    have hI : IntervalIntegrable g volume (-θ₀) (π - θ₀) := gneg.trans (gint _ (by linarith))
    have := hI.comp_sub_right θ₀
    simpa using this
  have hbound : IntervalIntegrable (fun θ => 2 * g (θ - θ₀)) volume 0 π := gshift.const_mul 2
  have hmeas : AEStronglyMeasurable f (volume.restrict (Set.uIoc (0:ℝ) π)) := by
    apply Measurable.aestronglyMeasurable
    simp only [hfdef]
    fun_prop
  have fint : IntervalIntegrable f volume 0 π := by
    refine hbound.mono_fun' hmeas ?_
    rw [Set.uIoc_of_le hpi.le]
    have := ae_restrict_of_ae_restrict_of_subset (Ioc_subset_Icc_self) ae_pt
    filter_upwards [this] with θ hθ
    rw [Real.norm_eq_abs, abs_of_nonneg (fnn θ)]; exact hθ
  refine ⟨fint, ?_⟩
  have step1 : ∫ θ in (0:ℝ)..π, f θ / 2 ≤ ∫ θ in (0:ℝ)..π, g (θ - θ₀) := by
    apply intervalIntegral.integral_mono_ae_restrict hpi.le (fint.div_const 2) gshift
    filter_upwards [ae_pt] with θ hθ
    linarith
  have step2 : ∫ θ in (0:ℝ)..π, g (θ - θ₀)
      = (∫ u in (0:ℝ)..θ₀, g u) + ∫ u in (0:ℝ)..(π - θ₀), g u := by
    rw [intervalIntegral.integral_comp_sub_right (fun u => g u) θ₀, zero_sub,
      ← intervalIntegral.integral_add_adjacent_intervals gneg (gint _ (by linarith))]
    congr 1
    have := intervalIntegral.integral_comp_neg (a := 0) (b := θ₀) (fun u => g u)
    simp only [geven, neg_zero] at this
    exact this.symm
  have mono : ∀ X, 0 ≤ X → X ≤ π → ∫ u in (0:ℝ)..X, g u ≤ ∫ u in (0:ℝ)..π, g u := fun X hX hXπ =>
    intervalIntegral.integral_mono_interval le_rfl hX hXπ
      (Filter.Eventually.of_forall (fun u => gnn u)) (gint π hpi.le)
  have step3 : ∫ u in (0:ℝ)..π, g u ≤ b ^ 2 / π + π * b := by
    rw [gval π hpi.le]
    have l1 : Real.log (1 + b ^ 2 / π ^ 2) ≤ b ^ 2 / π ^ 2 := by
      have := Real.log_le_sub_one_of_pos (show 0 < 1 + b ^ 2 / π ^ 2 by positivity)
      linarith
    have l2 : Real.arctan (π / b) ≤ π / 2 := (Real.arctan_lt_pi_div_two _).le
    have e : π * (b ^ 2 / π ^ 2) = b ^ 2 / π := by field_simp
    nlinarith [mul_le_mul_of_nonneg_left l1 hpi.le, mul_le_mul_of_nonneg_left l2 (show 0 ≤ 2 * b by positivity)]
  have final : 2 * (b ^ 2 / π + π * b) = π * (δ + π * Real.sqrt (2 * δ)) := by
    rw [hb2, hbdef]; field_simp
  have := mono θ₀ h0 h0'
  have := mono (π - θ₀) (by linarith) (by linarith)
  show ∫ θ in (0:ℝ)..π, f θ / 2 ≤ _
  linarith

end

end Sec6
end Zeta5
