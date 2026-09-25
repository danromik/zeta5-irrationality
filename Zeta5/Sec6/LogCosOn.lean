/-
Zeta5/Sec6/LogCosOn.lean  —  (A.1) on the interval, normalised (`|x| ≤ 1`).
-/
import Zeta5.Sec6.Defs

namespace Zeta5
namespace Sec6

open Real MeasureTheory Set

noncomputable section

/-- (A.1) on the interval, normalised:
`∫_0^π log|x − cos θ| dθ = −π log 2` for `|x| ≤ 1`.

Paper: (A.1), first branch, and its proof on p. 22 ("On the interval, the substitution
`t = m + r cos φ` and the identity `cos φ − cos θ = −2 sin((φ+θ)/2) sin((φ−θ)/2)` give the
constant `log(r/2)`").

Proof.  With `φ = arccos x`, off a countable set
`log|x − cos θ| = log 2 + log sin(θ/2 + φ/2) + log sin(φ/2 − θ/2)`; after substitution the two
`log sin` integrals combine, by `π`-periodicity, into `∫_0^π log sin = −π log 2`. -/
theorem integral_log_abs_sub_cos_of_abs_le {x : ℝ} (hx : |x| ≤ 1) :
    ∫ θ in (0 : ℝ)..π, Real.log |x - Real.cos θ| = -(π * Real.log 2) := by
  obtain ⟨hx1, hx2⟩ := abs_le.1 hx
  set φ := Real.arccos x with hφ
  have hcos : Real.cos φ = x := Real.cos_arccos hx1 hx2
  have hA : ∀ a b : ℝ, IntervalIntegrable (fun θ : ℝ => Real.log (Real.sin (θ / 2 + φ / 2)))
      volume a b := by
    intro a b
    have h : AnalyticOnNhd ℝ (fun θ : ℝ => Real.sin (θ / 2 + φ / 2)) univ := by
      intro x _; fun_prop
    exact (h.mono (subset_univ _)).meromorphicOn.intervalIntegrable_log
  have hB : ∀ a b : ℝ, IntervalIntegrable (fun θ : ℝ => Real.log (Real.sin (φ / 2 - θ / 2)))
      volume a b := by
    intro a b
    have h : AnalyticOnNhd ℝ (fun θ : ℝ => Real.sin (φ / 2 - θ / 2)) univ := by
      intro x _; fun_prop
    exact (h.mono (subset_univ _)).meromorphicOn.intervalIntegrable_log
  have hper : Function.Periodic (fun u => Real.log (Real.sin u)) π := by
    intro u; simp [Real.sin_add_pi, Real.log_neg_eq_log]
  -- null exceptional set
  set S : Set ℝ := {θ | Real.sin (θ / 2 + φ / 2) = 0 ∨ Real.sin (φ / 2 - θ / 2) = 0} with hS
  have hScount : S.Countable := by
    have : S ⊆ range (fun n : ℤ => 2 * ((n : ℝ) * π) - φ) ∪
        range (fun n : ℤ => φ - 2 * ((n : ℝ) * π)) := by
      rintro θ (h | h)
      · obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.1 h
        left; exact ⟨n, by simp only; rw [hn]; ring⟩
      · obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.1 h
        right; exact ⟨n, by simp only; rw [hn]; ring⟩
    exact ((countable_range _).union (countable_range _)).mono this
  have hae : ∀ᵐ θ ∂(volume : Measure ℝ), θ ∉ S :=
    measure_eq_zero_iff_ae_notMem.1 (hScount.measure_zero volume)
  have h1 : ∫ θ in (0 : ℝ)..π, Real.log |x - Real.cos θ| =
      ∫ θ in (0 : ℝ)..π, (Real.log 2 + Real.log (Real.sin (θ / 2 + φ / 2)) +
        Real.log (Real.sin (φ / 2 - θ / 2))) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hae] with θ hθ _
    simp only [hS, mem_ofPred_eq, not_or] at hθ
    obtain ⟨ha, hb⟩ := hθ
    rw [Real.log_abs, ← hcos, Real.cos_sub_cos]
    have e1 : (φ + θ) / 2 = θ / 2 + φ / 2 := by ring
    have e2 : (φ - θ) / 2 = φ / 2 - θ / 2 := by ring
    rw [e1, e2, neg_mul, neg_mul, Real.log_neg_eq_log, Real.log_mul (by positivity) hb,
      Real.log_mul (by norm_num) ha]
  rw [h1, intervalIntegral.integral_add (((intervalIntegrable_const).add (hA _ _))) (hB _ _),
    intervalIntegral.integral_add intervalIntegrable_const (hA _ _),
    intervalIntegral.integral_comp_div_add (f := fun u => Real.log (Real.sin u)) two_ne_zero,
    intervalIntegral.integral_comp_sub_div (f := fun u => Real.log (Real.sin u)) two_ne_zero,
    intervalIntegral.integral_const]
  have hsum : (∫ u in (0:ℝ) / 2 + φ / 2..π / 2 + φ / 2, Real.log (Real.sin u)) +
      (∫ u in φ / 2 - π / 2..φ / 2 - 0 / 2, Real.log (Real.sin u)) =
      ∫ u in (0:ℝ)..π, Real.log (Real.sin u) := by
    have e : (0:ℝ) / 2 + φ / 2 = φ / 2 - 0 / 2 := by ring
    rw [e, add_comm, intervalIntegral.integral_add_adjacent_intervals
      (f := fun u => Real.log (Real.sin u)) (by exact intervalIntegrable_log_sin)
      (by exact intervalIntegrable_log_sin)]
    have := hper.intervalIntegral_add_eq (φ / 2 - π / 2) 0
    simp only [zero_add] at this
    rw [← this]; congr 1; ring
  have h2 := integral_log_sin_zero_pi
  simp only [smul_eq_mul, sub_zero]
  linarith [hsum]

end

end Sec6
end Zeta5
