/-
Zeta5/Sec6/Num/Sound.lean  —  the interval arithmetic for (6.2)/(6.7) (Lemma 6.1, Appendix A.3):
one unconditional soundness theorem per enclosure of `Num/Eval.lean`.

Depends only on Mathlib and the preceding `Num` modules.  Every finite computation is
`decide +kernel`, i.e. checked by the kernel; there is no `native_decide` or `implemented_by`.
-/
import Zeta5.Sec6.Num.Eval

/-! # Soundness of the enclosures in `Eval.lean` -/

namespace Zeta5
namespace Sec6
namespace Num
open Real Finset

/-! ## Rounding -/

theorem rUp_ge (q : ℚ) : q ≤ rUp q := by
  unfold rUp; rw [le_div_iff₀ (by positivity)]; exact Int.le_ceil _
theorem rDn_le (q : ℚ) : rDn q ≤ q := by
  unfold rDn; rw [div_le_iff₀ (by positivity)]; exact Int.floor_le _
theorem rDn_nonneg {q : ℚ} (h : 0 ≤ q) : 0 ≤ rDn q := by
  unfold rDn
  apply div_nonneg _ (by positivity)
  exact_mod_cast Int.floor_nonneg.mpr (by positivity)
theorem oUp_ge (q : ℚ) : q ≤ oUp q := by
  unfold oUp; rw [le_div_iff₀ (by positivity)]; exact Int.le_ceil _
theorem oDn_le (q : ℚ) : oDn q ≤ q := by
  unfold oDn; rw [div_le_iff₀ (by positivity)]; exact Int.floor_le _

/-! ## A generic tail bound -/

theorem tail_bound {f : ℕ → ℝ} {a : ℝ} (hf : HasSum f a) (n : ℕ) (C r : ℝ) (hr0 : 0 ≤ r)
    (hr1 : r < 1) (hb : ∀ k, |f (k + n)| ≤ C * r ^ k) :
    |a - ∑ i ∈ range n, f i| ≤ C / (1 - r) := by
  have h1 : HasSum (fun k => f (k + n)) (a - ∑ i ∈ range n, f i) :=
    (hasSum_nat_add_iff' n).mpr hf
  have h2 : HasSum (fun k => C * r ^ k) (C * (1 - r)⁻¹) :=
    (hasSum_geometric_of_lt_one hr0 hr1).mul_left C
  have := h1.norm_le_of_bounded h2 (fun k => by simpa [Real.norm_eq_abs] using hb k)
  simpa [Real.norm_eq_abs, div_eq_mul_inv] using this

theorem sq_lt_one_of_abs {x : ℝ} (hx : |x| < 1) : x ^ 2 < 1 := by
  have h0 := abs_nonneg x
  rw [← sq_abs]; nlinarith

theorem pow_split (x : ℝ) (k n : ℕ) : |x| ^ (2 * (k + n) + 1) = |x| ^ (2 * n + 1) * (x ^ 2) ^ k := by
  rw [show 2 * (k + n) + 1 = (2 * n + 1) + 2 * k by ring, pow_add, pow_mul, sq_abs]

/-- `atanh` series for `log`. -/
theorem log_series_bound (z : ℝ) (hz : |z| < 1) (n : ℕ) :
    |(Real.log (1 + z) - Real.log (1 - z))
        - ∑ k ∈ range n, 2 * (1 / (2 * (k : ℝ) + 1)) * z ^ (2 * k + 1)|
      ≤ 2 * |z| ^ (2 * n + 1) / (1 - z ^ 2) := by
  have := tail_bound (hasSum_log_sub_log_of_abs_lt_one hz) n (2 * |z| ^ (2 * n + 1)) (z ^ 2)
    (sq_nonneg z) (sq_lt_one_of_abs hz) (fun k => by
      rw [abs_mul, abs_mul, abs_pow, pow_split]
      have h1 : |(2 : ℝ)| = 2 := by norm_num
      have h2 : |1 / (2 * ((k + n : ℕ) : ℝ) + 1)| ≤ 1 := by
        rw [abs_of_pos (by positivity)]
        rw [div_le_one (by positivity)]; have : (0 : ℝ) ≤ ((k + n : ℕ) : ℝ) := by positivity
        linarith
      rw [h1]
      have h3 : 0 ≤ |z| ^ (2 * n + 1) * (z ^ 2) ^ k := by positivity
      nlinarith [abs_nonneg (1 / (2 * ((k + n : ℕ) : ℝ) + 1))])
  exact this

theorem arctan_series_bound (x : ℝ) (hx : |x| < 1) (n : ℕ) :
    |arctan x - ∑ k ∈ range n, (-1) ^ k * x ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : ℝ)|
      ≤ |x| ^ (2 * n + 1) / (1 - x ^ 2) := by
  have := tail_bound (Real.hasSum_arctan (x := x) (by simpa using hx)) n (|x| ^ (2 * n + 1))
    (x ^ 2) (sq_nonneg x) (sq_lt_one_of_abs hx) (fun k => by
      rw [abs_div, abs_mul, abs_pow, abs_pow, abs_neg, abs_one, one_pow, one_mul, pow_split]
      rw [div_le_iff₀ (by positivity)]
      have h3 : 0 ≤ |x| ^ (2 * n + 1) * (x ^ 2) ^ k := by positivity
      have h4 : (1 : ℝ) ≤ |((2 * (k + n) + 1 : ℕ) : ℝ)| := by
        rw [abs_of_nonneg (by positivity)]; exact_mod_cast (by omega : 1 ≤ 2 * (k + n) + 1)
      nlinarith)
  exact this

theorem lser_cast (z : ℚ) (n : ℕ) :
    ((lser z n : ℚ) : ℝ) = ∑ k ∈ range n, 2 * (1 / (2 * (k : ℝ) + 1)) * (z : ℝ) ^ (2 * k + 1) := by
  induction n with
  | zero => simp [lser]
  | succ n ih => rw [lser, Finset.sum_range_succ, ← ih]; push_cast; ring

theorem aser_cast (x : ℚ) (n : ℕ) :
    ((aser x n : ℚ) : ℝ) = ∑ k ∈ range n, (-1) ^ k * (x : ℝ) ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : ℝ) := by
  induction n with
  | zero => simp [aser]
  | succ n ih => rw [aser, Finset.sum_range_succ, ← ih]; push_cast; ring

/-! ## Constants -/

theorem log_two_bounds : (L2lo : ℝ) < Real.log 2 ∧ Real.log 2 < (L2hi : ℝ) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := (1 : ℝ) / 2) (by norm_num) 70
  rw [show (1 : ℝ) - 1 / 2 = (2 : ℝ)⁻¹ by norm_num, Real.log_inv, abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  simp only [L2lo, L2hi]; push_cast
  constructor <;> linarith [h.1, h.2]

theorem pi_bounds : (PIlo : ℝ) < π ∧ π < (PIhi : ℝ) := by
  have h1 := Real.pi_gt_d20; have h2 := Real.pi_lt_d20
  simp only [PIlo, PIhi]; push_cast
  norm_num at h1 h2 ⊢
  exact ⟨h1, h2⟩

/-! ## `log` -/

theorem log_eq_series_form {y : ℝ} (hy : 0 < y) :
    Real.log y = Real.log (1 + (y - 1) / (y + 1)) - Real.log (1 - (y - 1) / (y + 1)) := by
  have h1 : 1 + (y - 1) / (y + 1) = 2 * y / (y + 1) := by field_simp; ring
  have h2 : 1 - (y - 1) / (y + 1) = 2 / (y + 1) := by field_simp; ring
  rw [h1, h2, ← Real.log_div (by positivity) (by positivity)]
  congr 1; field_simp

theorem log_reduce {q : ℚ} (hq : 0 < q) (k m : ℕ) :
    Real.log (q : ℝ) = Real.log (((q * 2 ^ m / 2 ^ k : ℚ) : ℝ)) + k * Real.log 2 - m * Real.log 2 := by
  have : (q : ℝ) = ((q * 2 ^ m / 2 ^ k : ℚ) : ℝ) * 2 ^ k / 2 ^ m := by
    push_cast; field_simp
  rw [this, Real.log_div (by positivity) (by positivity), Real.log_mul (by push_cast; positivity)
    (by positivity), Real.log_pow, Real.log_pow]

theorem logUpRaw_sound {q : ℚ} (hq : 0 < q) : Real.log (q : ℝ) ≤ (logUpRaw q : ℝ) := by
  have hL := log_two_bounds
  dsimp only [logUpRaw]
  split_ifs with h
  · obtain ⟨hy, hz⟩ := h
    set e := redExp q
    set y0 := q * 2 ^ e.2 / 2 ^ e.1 with hy0
    set y := rUp y0
    set z := (y - 1) / (y + 1) with hzdef
    have hy0p : 0 < y0 := by positivity
    have hyy : (y0 : ℝ) ≤ y := by exact_mod_cast rUp_ge y0
    have hyR : (0 : ℝ) < y := by exact_mod_cast hy
    have hzR : |(z : ℝ)| < 1 := by
      have : |z| < 1 := by linarith
      exact_mod_cast this
    have hs := log_series_bound _ hzR NLOG
    rw [abs_le] at hs
    have hlog : Real.log (y : ℝ) = Real.log (1 + (z : ℝ)) - Real.log (1 - (z : ℝ)) := by
      rw [log_eq_series_form hyR, hzdef]; push_cast; ring_nf
    have hmono : Real.log (y0 : ℝ) ≤ Real.log y :=
      Real.log_le_log (by exact_mod_cast hy0p) hyy
    rw [log_reduce hq e.1 e.2]
    have hk : (e.1 : ℝ) * Real.log 2 ≤ e.1 * L2hi :=
      mul_le_mul_of_nonneg_left hL.2.le (by positivity)
    have hm : (e.2 : ℝ) * L2lo ≤ e.2 * Real.log 2 :=
      mul_le_mul_of_nonneg_left hL.1.le (by positivity)
    have hcast : ((lser z NLOG + lerr z NLOG + e.1 * L2hi - e.2 * L2lo : ℚ) : ℝ)
        = (∑ k ∈ range NLOG, 2 * (1 / (2 * (k : ℝ) + 1)) * (z : ℝ) ^ (2 * k + 1))
          + 2 * |(z : ℝ)| ^ (2 * NLOG + 1) / (1 - (z : ℝ) ^ 2) + e.1 * (L2hi : ℝ)
          - e.2 * (L2lo : ℝ) := by
      rw [← lser_cast]; simp only [lerr]; push_cast; ring
    rw [hcast]
    linarith [hs.2]
  · have := Real.log_le_sub_one_of_pos (x := (q : ℝ)) (by exact_mod_cast hq)
    push_cast; linarith

theorem logUp_sound {q : ℚ} (hq : 0 < q) : Real.log (q : ℝ) ≤ (logUp q : ℝ) :=
  le_trans (logUpRaw_sound hq) (by exact_mod_cast oUp_ge _)

theorem logLoRaw_sound {q : ℚ} (hq : 0 < q) : (logLoRaw q : ℝ) ≤ Real.log (q : ℝ) := by
  have hL := log_two_bounds
  dsimp only [logLoRaw]
  split_ifs with h
  · obtain ⟨hy, hz⟩ := h
    set e := redExp q
    set y0 := q * 2 ^ e.2 / 2 ^ e.1 with hy0
    set y := rDn y0
    set z := (y - 1) / (y + 1) with hzdef
    have hyy : (y : ℝ) ≤ y0 := by exact_mod_cast rDn_le y0
    have hyR : (0 : ℝ) < y := by exact_mod_cast hy
    have hzR : |(z : ℝ)| < 1 := by
      have : |z| < 1 := by linarith
      exact_mod_cast this
    have hs := log_series_bound _ hzR NLOG
    rw [abs_le] at hs
    have hlog : Real.log (y : ℝ) = Real.log (1 + (z : ℝ)) - Real.log (1 - (z : ℝ)) := by
      rw [log_eq_series_form hyR, hzdef]; push_cast; ring_nf
    have hmono : Real.log (y : ℝ) ≤ Real.log y0 := Real.log_le_log hyR hyy
    rw [log_reduce hq e.1 e.2]
    have hk : (e.1 : ℝ) * L2lo ≤ e.1 * Real.log 2 :=
      mul_le_mul_of_nonneg_left hL.1.le (by positivity)
    have hm : (e.2 : ℝ) * Real.log 2 ≤ e.2 * L2hi :=
      mul_le_mul_of_nonneg_left hL.2.le (by positivity)
    have hcast : ((lser z NLOG - lerr z NLOG + e.1 * L2lo - e.2 * L2hi : ℚ) : ℝ)
        = (∑ k ∈ range NLOG, 2 * (1 / (2 * (k : ℝ) + 1)) * (z : ℝ) ^ (2 * k + 1))
          - 2 * |(z : ℝ)| ^ (2 * NLOG + 1) / (1 - (z : ℝ) ^ 2) + e.1 * (L2lo : ℝ)
          - e.2 * (L2hi : ℝ) := by
      rw [← lser_cast]; simp only [lerr]; push_cast; ring
    rw [hcast]
    linarith [hs.1]
  · have := Real.one_sub_inv_le_log_of_pos (x := (q : ℝ)) (by exact_mod_cast hq)
    push_cast; simpa [one_div] using this

theorem logLo_sound {q : ℚ} (hq : 0 < q) : (logLo q : ℝ) ≤ Real.log (q : ℝ) :=
  le_trans (by exact_mod_cast oDn_le _) (logLoRaw_sound hq)

/-! ## `arctan` -/

theorem arctan_eq_quarter (x : ℝ) (hx : 0 < x) :
    arctan x = π / 4 + arctan ((x - 1) / (x + 1)) := by
  have h1 : (1 : ℝ) * ((x - 1) / (x + 1)) < 1 := by
    rw [one_mul, div_lt_one (by linarith)]; linarith
  have := arctan_add h1
  rw [arctan_one] at this
  rw [this]; congr 1; field_simp; ring

theorem arctan_eq_half (x : ℝ) (hx : 0 < x) : arctan x = π / 2 - arctan (1 / x) := by
  rw [one_div, arctan_inv_of_pos hx]; ring

theorem aser_bounds (x : ℚ) (hx : |x| < 1) :
    (aser x NATAN : ℝ) - (aerr x NATAN : ℝ) ≤ arctan (x : ℝ) ∧
      arctan (x : ℝ) ≤ (aser x NATAN : ℝ) + (aerr x NATAN : ℝ) := by
  have hxR : |(x : ℝ)| < 1 := by exact_mod_cast hx
  have h := arctan_series_bound _ hxR NATAN
  rw [abs_le] at h
  have : (aerr x NATAN : ℝ) = |(x : ℝ)| ^ (2 * NATAN + 1) / (1 - (x : ℝ) ^ 2) := by
    simp only [aerr]; push_cast; ring
  rw [aser_cast, this]
  constructor <;> linarith [h.1, h.2]

theorem atanLoRaw_le (x : ℚ) (hx : 0 ≤ x) : (atanLoRaw x : ℝ) ≤ arctan (x : ℝ) := by
  have hP := pi_bounds
  have hd : (rDn x : ℝ) ≤ x := by exact_mod_cast rDn_le x
  have hd0 : (0 : ℚ) ≤ rDn x := rDn_nonneg hx
  have hmono : arctan (rDn x : ℝ) ≤ arctan (x : ℝ) := arctan_mono hd
  refine le_trans ?_ hmono
  dsimp only [atanLoRaw]
  set w := rDn x with hw
  split_ifs with h1 h2
  · have := (aser_bounds w (by rw [abs_of_nonneg hd0]; linarith)).1
    push_cast; linarith
  · have hw0 : (0 : ℝ) < w := by exact_mod_cast (show (0 : ℚ) < w by linarith)
    have hv : |(w - 1) / (w + 1)| < 1 := by
      rw [abs_div, abs_of_pos (by linarith : (0 : ℚ) < w + 1), div_lt_one (by linarith), abs_lt]
      constructor <;> linarith
    have := (aser_bounds _ hv).1
    rw [arctan_eq_quarter _ hw0]
    push_cast at this ⊢; linarith
  · have hw0 : (0 : ℝ) < w := by exact_mod_cast (show (0 : ℚ) < w by linarith)
    have hv : |1 / w| < 1 := by
      rw [abs_of_pos (one_div_pos.mpr (by linarith)), div_lt_one (by linarith)]; linarith
    have := (aser_bounds _ hv).2
    rw [arctan_eq_half _ hw0]
    push_cast at this ⊢; linarith

theorem atanLo_sound (x : ℚ) (hx : 0 ≤ x) : (atanLo x : ℝ) ≤ arctan (x : ℝ) :=
  le_trans (by exact_mod_cast oDn_le _) (atanLoRaw_le x hx)

theorem atanUpRaw_ge (x : ℚ) (hx : 0 ≤ x) : arctan (x : ℝ) ≤ (atanUpRaw x : ℝ) := by
  have hP := pi_bounds
  have hd : (x : ℝ) ≤ rUp x := by exact_mod_cast rUp_ge x
  have hd0 : (0 : ℚ) ≤ rUp x := le_trans hx (rUp_ge x)
  have hmono : arctan (x : ℝ) ≤ arctan (rUp x : ℝ) := arctan_mono hd
  refine le_trans hmono ?_
  dsimp only [atanUpRaw]
  set w := rUp x with hw
  split_ifs with h1 h2
  · have := (aser_bounds w (by rw [abs_of_nonneg hd0]; linarith)).2
    push_cast; linarith
  · have hw0 : (0 : ℝ) < w := by exact_mod_cast (show (0 : ℚ) < w by linarith)
    have hv : |(w - 1) / (w + 1)| < 1 := by
      rw [abs_div, abs_of_pos (by linarith : (0 : ℚ) < w + 1), div_lt_one (by linarith), abs_lt]
      constructor <;> linarith
    have := (aser_bounds _ hv).2
    rw [arctan_eq_quarter _ hw0]
    push_cast at this ⊢; linarith
  · have hw0 : (0 : ℝ) < w := by exact_mod_cast (show (0 : ℚ) < w by linarith)
    have hv : |1 / w| < 1 := by
      rw [abs_of_pos (one_div_pos.mpr (by linarith)), div_lt_one (by linarith)]; linarith
    have := (aser_bounds _ hv).1
    rw [arctan_eq_half _ hw0]
    push_cast at this ⊢; linarith

theorem atanUp_sound (x : ℚ) (hx : 0 ≤ x) : arctan (x : ℝ) ≤ (atanUp x : ℝ) :=
  le_trans (atanUpRaw_ge x hx) (by exact_mod_cast oUp_ge _)

/-! ## `√` -/

theorem sqrtLo_nonneg (q : ℚ) : 0 ≤ sqrtLo q := by
  dsimp only [sqrtLo]; split_ifs <;> positivity

theorem sqrtLo_sound {q : ℚ} (hq : 0 ≤ q) : (sqrtLo q : ℝ) ≤ Real.sqrt q := by
  dsimp only [sqrtLo]
  split_ifs with h
  · have h0 : (0 : ℝ) ≤ ((sqrtCand q : ℚ) / 2 ^ PREC : ℚ) := by positivity
    rw [Real.le_sqrt h0 (by exact_mod_cast hq)]; exact_mod_cast h
  · simp [Real.sqrt_nonneg]

theorem sqrtUp_sound {q : ℚ} (hq : 0 ≤ q) : Real.sqrt q ≤ (sqrtUp q : ℝ) := by
  dsimp only [sqrtUp]
  split_ifs with h
  · have h0 : (0 : ℝ) ≤ ((((sqrtCand q + 1 : ℕ) : ℚ) / 2 ^ PREC : ℚ) : ℝ) := by positivity
    rw [Real.sqrt_le_left h0]; exact_mod_cast h
  · have h0 : (0 : ℝ) ≤ ((q + 1 : ℚ) : ℝ) := by push_cast; positivity
    rw [Real.sqrt_le_left h0]; push_cast
    have : (0 : ℝ) ≤ q := by exact_mod_cast hq
    nlinarith

end Num
end Sec6
end Zeta5
