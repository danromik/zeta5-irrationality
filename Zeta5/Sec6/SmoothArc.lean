/-
Zeta5/Sec6/SmoothArc.lean  —  the smoothing error for one arcsine component `ω_[a,b]`.
-/
import Zeta5.Sec6.SmoothErr
import Zeta5.Sec6.ArcsinePot

namespace Zeta5
namespace Sec6

open Real MeasureTheory Set

noncomputable section

/-- The smoothed
potential of one arcsine component exceeds the true potential (A.1) by at most
`2ε/L + 2π√(ε/L)`, `L = b − a`, uniformly in `t ∈ ℝ`:

`∫_0^π kC ε (t − (m + r cos θ)) dθ ≤ π (U^{ω_[a,b]}(t) + 2ε/(b−a) + 2π √(ε/(b−a)))`.

Paper: p. 19, `∫U^ρ dω_i − U^ρ(t_i) ≤ ∑_j 8c_j√(2ε)/(π√(b_j−a_j))`, for one component.

Proof.  With `r = (b−a)/2`, `x = (t−m)/r`, `δ = ε/r = 2ε/(b−a)`: for `u = r(x − cos θ) ≠ 0`,
`kC ε u = log|u| + ½ log(1 + δ²/(x − cos θ)²)`, which holds for all `θ ∈ (0,π]` except possibly
`θ = arccos x`.  Integrate, using `arcsine_pot` for the first term and `smooth_err_norm` for the
second, and `δ + π√(2δ) = 2ε/(b−a) + 2π√(ε/(b−a))`. -/
theorem arcsine_smooth_err {a b : ℝ} (hab : a < b) (t : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∫ θ in (0 : ℝ)..π, kC ε (t - ((a + b) / 2 + (b - a) / 2 * Real.cos θ))
      ≤ π * (Uarc a b t + 2 * ε / (b - a) + 2 * π * Real.sqrt (ε / (b - a))) := by
  set r : ℝ := (b - a) / 2 with hr
  set x : ℝ := (t - (a + b) / 2) / r with hx
  set δ : ℝ := ε / r with hδ
  have hr0 : 0 < r := by rw [hr]; linarith
  have hδ0 : 0 < δ := div_pos hε hr0
  have hkey : ∀ θ, t - ((a + b) / 2 + r * Real.cos θ) = r * (x - Real.cos θ) := by
    intro θ; rw [hx]; field_simp; ring
  obtain ⟨hI1, hE1⟩ := arcsine_pot hab t
  obtain ⟨hI2, hE2⟩ := smooth_err_norm x hδ0
  have hae : ∀ᵐ θ ∂(volume : Measure ℝ), θ ∈ Set.uIoc 0 π →
      kC ε (t - ((a + b) / 2 + r * Real.cos θ)) =
        Real.log |t - ((a + b) / 2 + r * Real.cos θ)|
          + Real.log (1 + δ ^ 2 / (x - Real.cos θ) ^ 2) / 2 := by
    rw [ae_iff]
    refine measure_mono_null (t := {Real.arccos x}) ?_ (measure_singleton _)
    intro θ hθ
    simp only [Set.mem_ofPred_eq, Classical.not_imp] at hθ
    obtain ⟨hmem, hne⟩ := hθ
    have hθ' : θ ∈ Set.Icc 0 π := by
      rw [Set.uIoc_of_le Real.pi_pos.le] at hmem; exact ⟨hmem.1.le, hmem.2⟩
    by_contra hc
    apply hne
    have hcos : x - Real.cos θ ≠ 0 := by
      intro h0
      apply hc
      rw [Set.mem_singleton_iff, sub_eq_zero.1 h0, Real.arccos_cos hθ'.1 hθ'.2]
    have hu : r * (x - Real.cos θ) ≠ 0 := mul_ne_zero hr0.ne' hcos
    rw [hkey]
    unfold kC
    set u := r * (x - Real.cos θ) with hu_def
    have hu2 : 0 < u ^ 2 := by positivity
    have hsplit : u ^ 2 + ε ^ 2 = u ^ 2 * (1 + δ ^ 2 / (x - Real.cos θ) ^ 2) := by
      rw [hu_def, hδ]; field_simp
    have hpos : 0 < 1 + δ ^ 2 / (x - Real.cos θ) ^ 2 := by positivity
    rw [hsplit, Real.log_mul hu2.ne' hpos.ne', Real.log_pow, Real.log_abs]
    push_cast; ring
  have hint2 : IntervalIntegrable (fun θ => Real.log (1 + δ ^ 2 / (x - Real.cos θ) ^ 2) / 2)
      volume 0 π := hI2.div_const 2
  rw [intervalIntegral.integral_congr_ae hae, intervalIntegral.integral_add hI1 hint2, hE1]
  have hsq : Real.sqrt (2 * δ) = 2 * Real.sqrt (ε / (b - a)) := by
    have : 2 * δ = 2 ^ 2 * (ε / (b - a)) := by rw [hδ, hr]; field_simp
    rw [this, Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
  have hδe : δ = 2 * ε / (b - a) := by rw [hδ, hr]; field_simp
  have hbound : π * (δ + π * Real.sqrt (2 * δ))
      = π * (2 * ε / (b - a) + 2 * π * Real.sqrt (ε / (b - a))) := by
    rw [hsq, hδe]; ring
  rw [hbound] at hE2
  linarith [hE2]

end

end Sec6
end Zeta5
