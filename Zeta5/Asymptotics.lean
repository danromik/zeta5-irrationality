/-
Zeta5/Asymptotics.lean

The passage from (5.21) and (6.16) to (7.1), §7 p. 21.

`Interface.eq_7_1` is proved from these declarations, so this file is upstream of
`Interface.lean`.  It imports only `Basic.lean`.
-/
import Zeta5.Basic

namespace Zeta5

open Polynomial Finset

noncomputable section

/-- `Q_{K,M}(ζ(5)) = m_{K,M} · F_K(ζ(5))`, by (2.6). -/
lemma evalZeta5_Q (n M : ℕ) (Alloc : InnerAllocFamily n M) :
    evalZeta5 (Q n M Alloc) = (mKM n M Alloc : ℝ) * evalZeta5 (F n) := by
  rw [Q, evalZeta5_mul, evalZeta5_C]

/-- **`24 x log x + 200 x = o(x²)`.**  For every `ε > 0` there is an `X₀` beyond which
`24 x log x + 200 x ≤ ε x²`.

This is the entire analytic content of the passage from (5.21) and (6.16) to (7.1): the
error terms of (6.16) are of order `K log K`, and the two constants live on the `K²` scale.

The proof is elementary: `log x = log c + log(x/c) ≤ log c + x/c - 1` for any `c > 0`, with
`c` chosen so that `24/c = ε/4`. -/
theorem log_linear_le_quadratic (ε : ℝ) (hε : 0 < ε) :
    ∃ X₀ : ℝ, 0 < X₀ ∧ ∀ x : ℝ, X₀ ≤ x → 24 * x * Real.log x + 200 * x ≤ ε * x ^ 2 := by
  set c : ℝ := 96 / ε with hc
  have hc0 : 0 < c := by rw [hc]; positivity
  set C : ℝ := 24 * Real.log c + 176 with hC
  refine ⟨max 1 (4 * C / (3 * ε)), lt_of_lt_of_le one_pos (le_max_left _ _), fun x hx => ?_⟩
  have hx1 : (1 : ℝ) ≤ x := le_trans (le_max_left _ _) hx
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx1
  have hxC : 4 * C / (3 * ε) ≤ x := le_trans (le_max_right _ _) hx
  have hlog : Real.log x ≤ Real.log c + x / c - 1 := by
    have h1 : Real.log (x / c) ≤ x / c - 1 := Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_div (ne_of_gt hx0) (ne_of_gt hc0)] at h1
    linarith
  have hxc : x / c = ε * x / 96 := by rw [hc]; field_simp
  have step1 : 24 * x * Real.log x ≤ 24 * x * (Real.log c + x / c - 1) :=
    mul_le_mul_of_nonneg_left hlog (by positivity)
  have step2 : 24 * x * (Real.log c + x / c - 1)
      = 24 * Real.log c * x + ε / 4 * x ^ 2 - 24 * x := by rw [hxc]; ring
  have hCle : C ≤ 3 * ε / 4 * x := by
    have h4 : 4 * C ≤ x * (3 * ε) := (div_le_iff₀ (by positivity)).mp hxC
    linarith
  have step3 : (24 * Real.log c + 176) * x ≤ 3 * ε / 4 * x ^ 2 := by
    calc (24 * Real.log c + 176) * x = C * x := by rw [hC]
      _ ≤ 3 * ε / 4 * x * x := mul_le_mul_of_nonneg_right hCle (le_of_lt hx0)
      _ = 3 * ε / 4 * x ^ 2 := by ring
  linarith [step1, step2, step3]

/-- **(7.1)** (p. 21): `limsup_{K→∞, 40|K} K^{-2} log Q_{K,M}(ζ(5)) ≤ A_M + U`.

Stated in `ε`–`n₀` form with `K = 40n`, so `K² = 1600 n²`, exactly as `Zeta5.eq_7_1` states
it.  The three hypotheses are (5.21), (6.16) and the positivity `F_K(ζ(5)) > 0` (the first
assertion of (6.16), which Proposition 2.2 supplies). -/
theorem eq_7_1_of (M : ℕ) (Alloc : ∀ n, InnerAllocFamily n M)
    (Hm : ∀ δ : ℝ, 0 < δ → ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
        Real.log (mKM n M (Alloc n)) ≤ ((AM M : ℝ) + δ) * (K n : ℝ) ^ 2)
    (HF : ∀ n : ℕ, 0 < n → Real.log (evalZeta5 (F n))
        ≤ (Ubar : ℝ) * (K n : ℝ) ^ 2 + 24 * (K n : ℝ) * Real.log (K n : ℝ)
          + 200 * (K n : ℝ))
    (HFpos : ∀ n : ℕ, 0 < evalZeta5 (F n))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      Real.log (evalZeta5 (Q n M (Alloc n)))
        ≤ ((AM M : ℝ) + (Ubar : ℝ) + ε) * (1600 * (n : ℝ) ^ 2) := by
  obtain ⟨n₁, hn₁⟩ := Hm (ε / 2) (by linarith)
  obtain ⟨X₀, _hX₀pos, hX₀⟩ := log_linear_le_quadratic (ε / 2) (by linarith)
  obtain ⟨n₂, hn₂⟩ := exists_nat_gt (X₀ / 40)
  refine ⟨max n₁ (max n₂ 1), fun n hn => ?_⟩
  have hna : n₁ ≤ n := le_trans (le_max_left _ _) hn
  have hnb : n₂ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hnc : 1 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  have hK : ((K n : ℕ) : ℝ) = 40 * (n : ℝ) := by rw [K]; push_cast; ring
  have hKX : X₀ ≤ ((K n : ℕ) : ℝ) := by
    have h1 : (n₂ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnb
    have h2 : X₀ / 40 < (n : ℝ) := lt_of_lt_of_le hn₂ h1
    have h3 : X₀ < (n : ℝ) * 40 := (div_lt_iff₀ (by norm_num : (0:ℝ) < 40)).mp h2
    rw [hK]; linarith
  have hmpos : (0 : ℝ) < (mKM n M (Alloc n) : ℝ) := by
    exact_mod_cast mKM_pos n M (Alloc n)
  have hFp := HFpos n
  have hlogQ : Real.log (evalZeta5 (Q n M (Alloc n)))
      = Real.log (mKM n M (Alloc n)) + Real.log (evalZeta5 (F n)) := by
    rw [evalZeta5_Q, Real.log_mul (ne_of_gt hmpos) (ne_of_gt hFp)]
  have h1 := hn₁ n hna
  have h2 := HF n (by omega)
  have h3 := hX₀ ((K n : ℕ) : ℝ) hKX
  have hKsq : ((K n : ℕ) : ℝ) ^ 2 = 1600 * (n : ℝ) ^ 2 := by rw [hK]; ring
  rw [hlogQ]
  calc Real.log (mKM n M (Alloc n)) + Real.log (evalZeta5 (F n))
      ≤ ((AM M : ℝ) + ε / 2) * ((K n : ℕ) : ℝ) ^ 2
        + ((Ubar : ℝ) * ((K n : ℕ) : ℝ) ^ 2
            + 24 * ((K n : ℕ) : ℝ) * Real.log ((K n : ℕ) : ℝ) + 200 * ((K n : ℕ) : ℝ)) :=
        add_le_add h1 h2
    _ ≤ ((AM M : ℝ) + (Ubar : ℝ) + ε) * ((K n : ℕ) : ℝ) ^ 2 := by linarith
    _ = ((AM M : ℝ) + (Ubar : ℝ) + ε) * (1600 * (n : ℝ) ^ 2) := by rw [hKsq]

/-- **(5.21) from Proposition 5.2, (5.11)** (p. 17).

Proposition 5.2 gives the bound with the constant `I_out + 6λ/M + ∫_3^M R(x)x^{-3}dx`;
(5.16)–(5.18) then identify that constant as at most `A_M`.  That identification is the
hypothesis `hbound`; the (purely formal) passage is proved.  `Zeta5.Astar_eq` in
`Basic.lean` is the exact rational bookkeeping behind `hbound`. -/
theorem eq_5_21_of_prop_5_2 (M : ℕ) (Alloc : ∀ n, InnerAllocFamily n M)
    (H511 : ∀ δ : ℝ, 0 < δ → ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
        Real.log (mKM n M (Alloc n))
          ≤ ((Iout : ℝ) + 6 * (lam : ℝ) / (M : ℝ)
              + (∫ x in (3 : ℝ)..(M : ℝ), RR x / x ^ 3) + δ) * (K n : ℝ) ^ 2)
    (hbound : (Iout : ℝ) + 6 * (lam : ℝ) / (M : ℝ)
        + (∫ x in (3 : ℝ)..(M : ℝ), RR x / x ^ 3) ≤ (AM M : ℝ))
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      Real.log (mKM n M (Alloc n)) ≤ ((AM M : ℝ) + δ) * (K n : ℝ) ^ 2 := by
  obtain ⟨n₀, hn₀⟩ := H511 δ hδ
  refine ⟨n₀, fun n hn => le_trans (hn₀ n hn) ?_⟩
  exact mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)

end

end Zeta5
