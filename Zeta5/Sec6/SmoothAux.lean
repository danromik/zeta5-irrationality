/-
Zeta5/Sec6/SmoothAux.lean  —  elementary inequalities and one antiderivative for the
smoothing error (the role of the paper's mass bound and "60√ε", p. 19).
-/
import Zeta5.Sec6.Defs

namespace Zeta5
namespace Sec6

open Real MeasureTheory Set

noncomputable section

/-- Jordan's inequality on `[d, π − d]`: `sin x ≥ (2/π) d`. -/
theorem sin_ge_of_mem {x d : ℝ} (hd : 0 ≤ d) (h1 : d ≤ x) (h2 : d ≤ π - x) :
    2 / π * d ≤ Real.sin x := by
  have hpi := Real.pi_pos
  rcases le_total x (π / 2) with hu | hu
  · exact (Real.mul_le_sin hd (by linarith)).trans
      (Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) hu h1)
  · have := (Real.mul_le_sin hd (by linarith)).trans
      (Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) h2)
    rwa [Real.sin_pi_sub] at this

/-- **`|cos θ₀ − cos θ| ≥ 2(θ − θ₀)²/π²`** on `[0,π]²` (sharp at `(0,π)`).
From `cos θ₀ − cos θ = −2 sin((θ₀+θ)/2) sin((θ₀−θ)/2)` and Jordan's inequality. -/
theorem cos_sub_cos_ge {θ θ₀ : ℝ} (h1 : 0 ≤ θ) (h2 : θ ≤ π) (h3 : 0 ≤ θ₀) (h4 : θ₀ ≤ π) :
    2 * (θ - θ₀) ^ 2 / π ^ 2 ≤ |Real.cos θ₀ - Real.cos θ| := by
  have hpi := Real.pi_pos
  rw [Real.cos_sub_cos]
  set d := |θ₀ - θ| with hd
  have hd0 : 0 ≤ d := abs_nonneg _
  have hdd : d = θ₀ - θ ∨ d = -(θ₀ - θ) := abs_choice _
  have hdle : d ≤ π := by rcases hdd with h | h <;> linarith
  have hA : 2 / π * (d / 2) ≤ |Real.sin ((θ₀ - θ) / 2)| := by
    have hs : |Real.sin ((θ₀ - θ) / 2)| = Real.sin (d / 2) := by
      rcases hdd with h | h
      · rw [h, abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith))]
      · rw [show (θ₀ - θ) / 2 = -(d / 2) by rw [h]; ring, Real.sin_neg, abs_neg,
          abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith))]
    rw [hs]; exact sin_ge_of_mem (by linarith) le_rfl (by linarith)
  have hB : 2 / π * (d / 2) ≤ Real.sin ((θ₀ + θ) / 2) :=
    sin_ge_of_mem (by linarith) (by rcases hdd with h | h <;> linarith)
      (by rcases hdd with h | h <;> linarith)
  have hsq : (θ - θ₀) ^ 2 = d ^ 2 := by rw [hd, sq_abs]; ring
  have hB0 : 0 ≤ 2 / π * (d / 2) := by positivity
  rw [hsq, abs_mul, abs_mul, show |(-2 : ℝ)| = 2 by norm_num, abs_of_nonneg (hB0.trans hB)]
  have := mul_le_mul hB hA hB0 (hB0.trans hB)
  calc 2 * d ^ 2 / π ^ 2 = 2 * (2 / π * (d / 2) * (2 / π * (d / 2))) := by field_simp
    _ ≤ _ := by linarith

/-- The nearest point of `[−1,1]` in angle form: for every real `τ` there is
`θ₀ ∈ [0,π]` with `|cos θ₀ − cos θ| ≤ |τ − cos θ|` for all `θ`.

Proof.  `θ₀ = arccos c` with `c = max (−1) (min 1 τ)`, the nearest point of `[−1,1]` to `τ`;
`|c − y| ≤ |τ − y|` for `y ∈ [−1,1]` by cases on the position of `τ`. -/
theorem exists_nearest_cos (τ : ℝ) :
    ∃ θ₀ ∈ Icc (0 : ℝ) π, ∀ θ, |Real.cos θ₀ - Real.cos θ| ≤ |τ - Real.cos θ| := by
  set c := max (-1) (min 1 τ) with hc
  have hc1 : -1 ≤ c := le_max_left _ _
  have hc2 : c ≤ 1 := max_le (by norm_num) (min_le_left _ _)
  refine ⟨Real.arccos c, ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩, fun θ => ?_⟩
  rw [Real.cos_arccos hc1 hc2]
  have hy1 := Real.neg_one_le_cos θ
  have hy2 := Real.cos_le_one θ
  rcases le_total τ (-1) with h | h
  · have : c = -1 := by rw [hc, min_eq_right (by linarith), max_eq_left h]
    rw [this, abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith
  · rcases le_total τ 1 with h' | h'
    · have : c = τ := by rw [hc, min_eq_right h', max_eq_right h]
      rw [this]
    · have : c = 1 := by rw [hc, min_eq_left h', max_eq_right (by norm_num)]
      rw [this, abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; linarith

end

end Sec6
end Zeta5
