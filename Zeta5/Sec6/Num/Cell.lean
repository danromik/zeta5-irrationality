/-
Zeta5/Sec6/Num/Cell.lean  —  the interval arithmetic for (6.2)/(6.7) (Lemma 6.1, Appendix A.3):
the closed forms (A.1)/(A.5) (`UomR`, `Uclosed`, `Vclosed`), monotonicity of (A.1),
and the soundness of the cell checker (`cell_sound`, `chain_sound`).

Depends only on Mathlib and the preceding `Num` modules.  Every finite computation is
`decide +kernel`, i.e. checked by the kernel; there is no `native_decide` or `implemented_by`.
-/
import Zeta5.Sec6.Num.Sound

/-! # The closed forms, their monotonicity, and the cell / chain lemmas -/

namespace Zeta5
namespace Sec6
namespace Num
open Real Finset

/-- (A.1): the potential of the unit arcsine measure on `[a,b]` (closed form). -/
noncomputable def UomR (a b t : ℝ) : ℝ :=
  if a ≤ t ∧ t ≤ b then Real.log ((b - a) / 4)
  else Real.log ((|t - (a + b) / 2| + Real.sqrt ((t - a) * (t - b))) / 2)

/-- `U^ρ` via (A.1) and Table 1. -/
noncomputable def Uclosed (t : ℝ) : ℝ := ∑ j ∈ range 16, (cQ j : ℝ) * UomR (aQ j) (bQ j) t

/-- (A.5), with `α = 3/40` (at `t = 0` Lean's `1/0 = 0` makes the bracket term vanish,
matching `V(0) = -12α log α - 2 + 12α`). -/
noncomputable def Vclosed (t : ℝ) : ℝ :=
  Real.log (1 + t) - 6 * (3 / 40) * Real.log (t + (3 / 40) ^ 2) - 2 + 12 * (3 / 40)
    + 2 * Real.sqrt t * (π + arctan (1 / Real.sqrt t) - 6 * arctan ((3 / 40) / Real.sqrt t))

theorem outside_facts {a b t : ℝ} (hab : a < b) (h : t < a ∨ b < t) :
    (b - a) / 2 < |t - (a + b) / 2| ∧ 0 < (t - a) * (t - b) := by
  rcases h with h | h
  · rw [abs_of_neg (by linarith)]; constructor <;> nlinarith
  · rw [abs_of_pos (by linarith)]; constructor <;> nlinarith

/-- `U^{ω_[a,b]}` is nonincreasing on `(-∞, b]`. -/
theorem UomR_anti {a b t s : ℝ} (hab : a < b) (hts : t ≤ s) (hsb : s ≤ b) :
    UomR a b s ≤ UomR a b t := by
  unfold UomR
  by_cases hs : a ≤ s
  · rw [ite_eq_left ⟨hs, hsb⟩]
    by_cases ht : a ≤ t
    · rw [ite_eq_left ⟨ht, by linarith⟩]
    · rw [ite_eq_right (by tauto)]
      push Not at ht
      have h1 := outside_facts hab (Or.inl ht)
      apply Real.log_le_log (by linarith)
      have := Real.sqrt_nonneg ((t - a) * (t - b))
      linarith [h1.1]
  · push Not at hs
    rw [ite_eq_right (by intro h; linarith [h.1]), ite_eq_right (by intro h; linarith [h.1])]
    have h1 := outside_facts hab (Or.inl hs)
    have h2 := outside_facts hab (Or.inl (lt_of_le_of_lt hts hs))
    apply Real.log_le_log (by linarith [Real.sqrt_nonneg ((s - a) * (s - b))])
    have e1 : |s - (a + b) / 2| ≤ |t - (a + b) / 2| := by
      rw [abs_of_neg (by linarith), abs_of_neg (by linarith)]; linarith
    have e2 : Real.sqrt ((s - a) * (s - b)) ≤ Real.sqrt ((t - a) * (t - b)) :=
      Real.sqrt_le_sqrt (by nlinarith)
    linarith

/-- `U^{ω_[a,b]}` is nondecreasing on `[a, ∞)`. -/
theorem UomR_mono {a b t s : ℝ} (hab : a < b) (hat : a ≤ t) (hts : t ≤ s) :
    UomR a b t ≤ UomR a b s := by
  unfold UomR
  by_cases ht : t ≤ b
  · rw [ite_eq_left ⟨hat, ht⟩]
    by_cases hs : s ≤ b
    · rw [ite_eq_left ⟨by linarith, hs⟩]
    · rw [ite_eq_right (by tauto)]
      push Not at hs
      have h1 := outside_facts hab (Or.inr hs)
      apply Real.log_le_log (by linarith)
      have := Real.sqrt_nonneg ((s - a) * (s - b))
      linarith [h1.1]
  · push Not at ht
    rw [ite_eq_right (by intro h; linarith [h.2]), ite_eq_right (by intro h; linarith [h.2])]
    have h1 := outside_facts hab (Or.inr ht)
    apply Real.log_le_log (by linarith [Real.sqrt_nonneg ((t - a) * (t - b))])
    have e1 : |t - (a + b) / 2| ≤ |s - (a + b) / 2| := by
      rw [abs_of_pos (by linarith), abs_of_pos (by linarith)]; linarith
    have e2 : Real.sqrt ((t - a) * (t - b)) ≤ Real.sqrt ((s - a) * (s - b)) :=
      Real.sqrt_le_sqrt (by nlinarith)
    linarith

theorem UomUp_sound {a b t : ℚ} (hab : a < b) : UomR a b t ≤ (UomUp a b t : ℝ) := by
  have habR : (a : ℝ) < b := by exact_mod_cast hab
  by_cases h : a ≤ t ∧ t ≤ b
  · have h' : (a : ℝ) ≤ t ∧ (t : ℝ) ≤ b := by exact_mod_cast h
    rw [UomR, ite_eq_left h', UomUp, ite_eq_left h]
    have := logUp_sound (q := (b - a) / 4) (by linarith)
    push_cast at this; exact this
  · have h' : ¬ ((a : ℝ) ≤ t ∧ (t : ℝ) ≤ b) := by exact_mod_cast h
    rw [UomR, ite_eq_right h', UomUp, ite_eq_right h]
    have ho : (t : ℝ) < a ∨ (b : ℝ) < t := by
      by_contra hc; push Not at hc; exact h' ⟨hc.1, hc.2⟩
    have hf := outside_facts habR ho
    have hq0 : (0 : ℚ) ≤ (t - a) * (t - b) := by
      have : (0 : ℝ) ≤ ((t - a) * (t - b) : ℚ) := by push_cast; linarith [hf.2]
      exact_mod_cast this
    have hs := sqrtUp_sound hq0
    push_cast at hs
    have hX : 0 < (|(t : ℝ) - (a + b) / 2| + Real.sqrt ((t - a) * (t - b))) / 2 := by
      linarith [Real.sqrt_nonneg (((t : ℝ) - a) * (t - b)), hf.1]
    have hpos : (0 : ℚ) < (|t - (a + b) / 2| + sqrtUp ((t - a) * (t - b))) / 2 := by
      have : (0 : ℝ) < (((|t - (a + b) / 2| + sqrtUp ((t - a) * (t - b))) / 2 : ℚ) : ℝ) := by
        push_cast; linarith
      exact_mod_cast this
    refine le_trans (Real.log_le_log hX ?_) (logUp_sound hpos)
    push_cast; linarith

/-- Table 1 facts used by the cell lemma (kernel `decide`). -/
theorem tab_facts : ∀ j < 16, aQ j < bQ j ∧ aQ j ≤ aQ 0 ∧ bQ 0 ≤ bQ j ∧ 0 ≤ cQ j := by
  decide +kernel

theorem UUpR_cast (t : ℚ) (n : ℕ) :
    ((UUpR t n : ℚ) : ℝ) = ∑ j ∈ range n, (cQ j : ℝ) * (UomUp (aQ j) (bQ j) t : ℝ) := by
  induction n with
  | zero => simp [UUpR]
  | succ n ih => rw [UUpR, Finset.sum_range_succ, ← ih]; push_cast; ring

/-- The `U` half of (A.7): monotonicity on each side of `[a₁, b₁]`. -/
theorem Uclosed_le {l r : ℚ} {t : ℝ} (hl : (l : ℝ) ≤ t) (hr : t ≤ r)
    (hside : r ≤ bQ 0 ∨ aQ 0 ≤ l) :
    Uclosed t ≤ (UUp (if r ≤ bQ 0 then l else r) : ℝ) := by
  unfold Uclosed UUp
  rw [UUpR_cast]
  apply Finset.sum_le_sum
  intro j hj
  have hj' := Finset.mem_range.1 hj
  obtain ⟨h1, h2, h3, h4⟩ := tab_facts j hj'
  have h1R : (aQ j : ℝ) < bQ j := by exact_mod_cast h1
  have h4R : (0 : ℝ) ≤ cQ j := by exact_mod_cast h4
  apply mul_le_mul_of_nonneg_left _ h4R
  split_ifs with hrb
  · refine le_trans (UomR_anti h1R hl ?_) (UomUp_sound h1)
    have : (r : ℝ) ≤ bQ j := by exact_mod_cast (le_trans hrb h3)
    linarith
  · have hal : aQ 0 ≤ l := hside.resolve_left hrb
    refine le_trans (UomR_mono h1R ?_ hr) (UomUp_sound h1)
    have : (aQ j : ℝ) ≤ l := by exact_mod_cast (le_trans h2 hal)
    linarith

/-- The `V` half of (A.7), termwise. -/
theorem VLo_le {l r : ℚ} {t : ℝ} (hl0 : 0 ≤ l) (hlr : l < r) (hl : (l : ℝ) ≤ t) (hr : t ≤ r) :
    (VLo l r : ℝ) ≤ Vclosed t := by
  have hP := pi_bounds
  have hl0R : (0 : ℝ) ≤ l := by exact_mod_cast hl0
  have hr0 : (0 : ℚ) < r := by linarith
  have hr0R : (0 : ℝ) < r := by exact_mod_cast hr0
  have ht0 : 0 ≤ t := le_trans hl0R hl
  set sl := sqrtLo l with hsl
  set sr := sqrtUp r with hsr
  have hsl0 : (0 : ℝ) ≤ sl := by exact_mod_cast sqrtLo_nonneg l
  have hslt : (sl : ℝ) ≤ Real.sqrt t :=
    le_trans (sqrtLo_sound hl0) (Real.sqrt_le_sqrt hl)
  have hsrt : Real.sqrt t ≤ sr := le_trans (Real.sqrt_le_sqrt hr) (sqrtUp_sound hr0.le)
  have hsqr : 0 < Real.sqrt (r : ℝ) := Real.sqrt_pos.2 hr0R
  have hsr0 : (0 : ℝ) < sr := lt_of_lt_of_le hsqr (sqrtUp_sound hr0.le)
  have hsr0Q : (0 : ℚ) < sr := by exact_mod_cast hsr0
  -- term 1: log(1+t)
  have T1 : (logLo (1 + l) : ℝ) ≤ Real.log (1 + t) := by
    have := logLo_sound (q := 1 + l) (by linarith)
    push_cast at this
    exact le_trans this (Real.log_le_log (by linarith) (by linarith))
  -- term 2: log(t + α²)
  have T2 : Real.log (t + (3 / 40) ^ 2) ≤ (logUp (r + alphaQ ^ 2) : ℝ) := by
    have := logUp_sound (q := r + alphaQ ^ 2) (by positivity)
    simp only [alphaQ] at this; push_cast at this
    exact le_trans (Real.log_le_log (by positivity) (by linarith)) this
  -- term 3: √t · arctan(1/√t)
  have T3 : (sl : ℝ) * (max 0 (atanLo (1 / sr)) : ℚ) ≤ Real.sqrt t * arctan (1 / Real.sqrt t) := by
    rcases eq_or_lt_of_le ht0 with h0 | h0
    · have : (sl : ℝ) = 0 := by
        have := hslt; rw [← h0, Real.sqrt_zero] at this; linarith
      rw [this, zero_mul, ← h0, Real.sqrt_zero, zero_mul]
    · have hst : 0 < Real.sqrt t := Real.sqrt_pos.2 h0
      have hA : ((max 0 (atanLo (1 / sr)) : ℚ) : ℝ) ≤ arctan (1 / Real.sqrt t) := by
        push_cast
        apply max_le (arctan_nonneg.2 (by positivity))
        refine le_trans (atanLo_sound _ (by positivity)) (arctan_mono ?_)
        push_cast
        exact one_div_le_one_div_of_le hst hsrt
      apply mul_le_mul hslt hA (by positivity) hst.le
  -- term 4: √t · arctan(α/√t)
  have T4 : Real.sqrt t * arctan ((3 / 40) / Real.sqrt t)
      ≤ (sr : ℝ) * ((if sl = 0 then PIhi / 2 else atanUp (alphaQ / sl) : ℚ) : ℝ) := by
    have hat0 : 0 ≤ arctan ((3 / 40) / Real.sqrt t) :=
      arctan_nonneg.2 (by positivity)
    have hB : arctan ((3 / 40) / Real.sqrt t)
        ≤ ((if sl = 0 then PIhi / 2 else atanUp (alphaQ / sl) : ℚ) : ℝ) := by
      split_ifs with hz
      · push_cast; linarith [arctan_lt_pi_div_two ((3 / 40) / Real.sqrt t)]
      · have hslp : (0 : ℝ) < sl := lt_of_le_of_ne hsl0 (by exact_mod_cast (Ne.symm hz))
        have hslpQ : (0 : ℚ) < sl := by exact_mod_cast hslp
        refine le_trans (arctan_mono ?_) (atanUp_sound _ (by simp only [alphaQ]; positivity))
        simp only [alphaQ]; push_cast
        exact div_le_div_of_nonneg_left (by norm_num) hslp hslt
    exact mul_le_mul hsrt hB hat0 hsr0.le
  have hV : Vclosed t = Real.log (1 + t) - 6 * (3 / 40) * Real.log (t + (3 / 40) ^ 2) - 2
      + 12 * (3 / 40) + 2 * π * Real.sqrt t + 2 * (Real.sqrt t * arctan (1 / Real.sqrt t))
      - 12 * (Real.sqrt t * arctan ((3 / 40) / Real.sqrt t)) := by
    unfold Vclosed; ring
  have hpi : (PIlo : ℝ) * sl ≤ π * Real.sqrt t :=
    mul_le_mul hP.1.le hslt hsl0 Real.pi_pos.le
  rw [hV]
  simp only [VLo, alphaQ]
  rw [← hsl, ← hsr]
  simp only [alphaQ] at T2 T4
  push_cast at T1 T2 T3 T4 ⊢
  linarith [T1, T2, T3, T4, hpi]

theorem cell_sound {M l r : ℚ} (h : cellOK M l r = true) {t : ℝ} (hl : (l : ℝ) ≤ t)
    (hr : t ≤ r) : 2 * Uclosed t - Vclosed t ≤ (M : ℝ) := by
  simp only [cellOK, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h0, hlr⟩, hside⟩, hB⟩ := h
  have hU := Uclosed_le hl hr hside
  have hV := VLo_le h0 hlr hl hr
  have hB' : ((BUp l r : ℚ) : ℝ) ≤ (M : ℝ) := by exact_mod_cast hB
  simp only [BUp] at hB'
  push_cast at hB'
  linarith

theorem chain_sound (M : ℚ) : ∀ (L : List ℕ) (a b : ℕ), chainOK M (a :: b :: L) = true →
    ∀ t : ℝ, (a : ℝ) / 10 ^ 12 ≤ t → t ≤ (((b :: L).getLast (by simp) : ℕ) : ℝ) / 10 ^ 12 →
      2 * Uclosed t - Vclosed t ≤ (M : ℝ) := by
  intro L
  induction L with
  | nil =>
    intro a b h t h1 h2
    simp only [chainOK, Bool.and_true] at h
    exact cell_sound h (by push_cast; exact h1) (by push_cast; simpa using h2)
  | cons c L ih =>
    intro a b h t h1 h2
    rw [chainOK, Bool.and_eq_true] at h
    by_cases htb : t ≤ (b : ℝ) / 10 ^ 12
    · exact cell_sound h.1 (by push_cast; exact h1) (by push_cast; exact htb)
    · push Not at htb
      exact ih b c h.2 t htb.le (by simpa using h2)

end Num
end Sec6
end Zeta5
