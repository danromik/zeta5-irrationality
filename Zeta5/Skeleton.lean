/-
Zeta5/Skeleton.lean

The top-level deduction of the paper:  Theorem 2.1 ⟹ Theorem 1.1
(A. Fauzan, "ζ(5) is irrational", §1.1 p. 2 and "Proof of Theorem 1.1", p. 21).

THIS FILE CONTAINS NO `sorry`.

The argument is the one the audit called "airtight": an integer-valued polynomial of
degree at most `37n`, positive at `ξ` and smaller than `exp(-139 n²/5)`, multiplied by
`b^{37n}` where `ξ = a/b`, is a positive integer that is eventually `< 1`.  The decay is
quadratic in `n` and the height cost only linear, so no bound on the coefficients of the
polynomials is needed.
-/
import Zeta5.Basic

namespace Zeta5

open Polynomial Finset

noncomputable section

/-! ## The clearing-of-denominators step -/

/-- If `P ∈ ℤ[X]` has degree at most `d` and `b ≠ 0`, then `b^d · P(a/b)` is the integer
`∑_{i ≤ d} (coeff i) a^i b^{d-i}`. -/
theorem intValue_eq (P : Polynomial ℤ) (a b : ℤ) (hb : b ≠ 0) (d : ℕ)
    (hd : P.natDegree ≤ d) :
    ((∑ i ∈ range (d + 1), P.coeff i * a ^ i * b ^ (d - i) : ℤ) : ℝ)
      = (b : ℝ) ^ d * Polynomial.eval₂ (Int.castRingHom ℝ) ((a : ℝ) / (b : ℝ)) P := by
  have hbR : (b : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hb
  rw [Polynomial.eval₂_eq_sum_range' (Int.castRingHom ℝ) (Nat.lt_succ_of_le hd)
      ((a : ℝ) / (b : ℝ)), Finset.mul_sum]
  simp only [eq_intCast]
  push_cast
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hbd : (b : ℝ) ^ d = (b : ℝ) ^ i * (b : ℝ) ^ (d - i) := by
    rw [← pow_add, Nat.add_sub_cancel' hi']
  rw [hbd, div_pow]
  field_simp

/-! ## The abstract irrationality criterion -/

/-- **The deduction "Theorem 2.1 ⟹ Theorem 1.1"** in abstract form (paper, §1.1 p. 2).

If for every large `n` there is an integer polynomial of degree at most `37 n` whose value
at `ξ` lies strictly between `0` and `exp(-139 n²/5)`, then `ξ` is irrational. -/
theorem irrational_of_integerPolynomials (ξ : ℝ) (n₀ : ℕ)
    (H : ∀ n, n₀ ≤ n → ∃ P : Polynomial ℤ, P.natDegree ≤ 37 * n ∧
        0 < Polynomial.eval₂ (Int.castRingHom ℝ) ξ P ∧
        Polynomial.eval₂ (Int.castRingHom ℝ) ξ P < Real.exp (-(139 / 5 : ℝ) * (n : ℝ) ^ 2)) :
    Irrational ξ := by
  rintro ⟨q, rfl⟩
  -- write the rational number as `a / b` with `b > 0`
  obtain ⟨a, b, hb, hqab⟩ :
      ∃ a b : ℤ, 0 < b ∧ ((q : ℝ)) = (a : ℝ) / (b : ℝ) := by
    refine ⟨q.num, (q.den : ℤ), by exact_mod_cast q.pos, ?_⟩
    rw [Rat.cast_def]
    push_cast
    ring
  rw [hqab] at H
  have hbne : b ≠ 0 := by omega
  have hbpos : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hb1 : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hlog0 : 0 ≤ Real.log (b : ℝ) := Real.log_nonneg hb1
  -- choose `n` large enough that `37 n log b < 139 n² / 5`
  obtain ⟨n₁, hn₁⟩ := exists_nat_gt (185 * Real.log (b : ℝ) / 139)
  set n : ℕ := max n₀ (max 1 n₁) with hndef
  have hn0 : n₀ ≤ n := le_max_left _ _
  have hone : 1 ≤ n := le_trans (le_max_left 1 n₁) (le_max_right _ _)
  have hn1 : n₁ ≤ n := le_trans (le_max_right 1 n₁) (le_max_right _ _)
  obtain ⟨P, hdeg, hpos, hsmall⟩ := H n hn0
  -- the integer `A = b^{37n} P(a/b)`
  set A : ℤ := ∑ i ∈ range (37 * n + 1), P.coeff i * a ^ i * b ^ (37 * n - i) with hAdef
  have key : (A : ℝ) = (b : ℝ) ^ (37 * n) * Polynomial.eval₂ (Int.castRingHom ℝ)
      ((a : ℝ) / (b : ℝ)) P := intValue_eq P a b hbne (37 * n) hdeg
  -- `A` is a positive integer, hence `1 ≤ A`
  have hApos : (0 : ℝ) < (A : ℝ) := by
    rw [key]; exact mul_pos (pow_pos hbpos _) hpos
  have hA1 : (1 : ℝ) ≤ (A : ℝ) := by
    have hAz : (0 : ℤ) < A := by exact_mod_cast hApos
    exact_mod_cast hAz
  -- `A < exp (37 n log b - 139 n² / 5) < 1`
  have hbpow : (b : ℝ) ^ (37 * n) = Real.exp ((37 * n : ℕ) * Real.log (b : ℝ)) := by
    rw [← Real.log_pow, Real.exp_log (pow_pos hbpos _)]
  have hAlt : (A : ℝ) < Real.exp ((37 * (n : ℝ)) * Real.log (b : ℝ) - 139 / 5 * (n : ℝ) ^ 2) := by
    calc (A : ℝ) = (b : ℝ) ^ (37 * n) * Polynomial.eval₂ (Int.castRingHom ℝ)
              ((a : ℝ) / (b : ℝ)) P := key
      _ < (b : ℝ) ^ (37 * n) * Real.exp (-(139 / 5 : ℝ) * (n : ℝ) ^ 2) :=
          mul_lt_mul_of_pos_left hsmall (pow_pos hbpos _)
      _ = Real.exp ((37 * (n : ℝ)) * Real.log (b : ℝ) - 139 / 5 * (n : ℝ) ^ 2) := by
          rw [hbpow, ← Real.exp_add]
          push_cast
          ring_nf
  have hlogb : Real.log (b : ℝ) < 139 * (n : ℝ) / 185 := by
    have h2 : (n₁ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    have h3 : 185 * Real.log (b : ℝ) / 139 < (n : ℝ) := lt_of_lt_of_le hn₁ h2
    linarith
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hone
  have hneg : (37 * (n : ℝ)) * Real.log (b : ℝ) - 139 / 5 * (n : ℝ) ^ 2 < 0 := by
    nlinarith [mul_lt_mul_of_pos_left hlogb (by linarith : (0 : ℝ) < 37 * (n : ℝ))]
  have hfinal : (A : ℝ) < 1 := lt_of_lt_of_le hAlt (le_of_lt (Real.exp_lt_one_iff.2 hneg))
  linarith

/-! ## Theorem 2.1 and Theorem 1.1 in the paper's own objects -/

/-- The content of **Theorem 2.1** (p. 4) at the cutoff `M = 200` that the proof of
Theorem 1.1 uses: `Q_{40n,200} ∈ ℤ[X]`, `deg Q_{40n,200} = h = 37n`, `Q_{40n,200}(ζ(5)) > 0`,
and (2.7).

The degree is stated as an *equality*, as in the paper ("has degree `h`"), even though the
deduction of Theorem 1.1 only uses `≤`.

`Alloc` supplies the inner allocations of (4.4), on which `Q` depends. -/
def Theorem_2_1 (Alloc : ∀ n, InnerAllocFamily n 200) : Prop :=
  ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
    (∃ P : Polynomial ℤ, P.map (Int.castRingHom ℚ) = Q n 200 (Alloc n)) ∧
    (Q n 200 (Alloc n)).natDegree = h n ∧
    0 < evalZeta5 (Q n 200 (Alloc n)) ∧
    evalZeta5 (Q n 200 (Alloc n)) < Real.exp (-(139 / 5 : ℝ) * (n : ℝ) ^ 2)

/-- Transfer of evaluation along `ℤ[X] → ℚ[X]`. -/
lemma evalZeta5_map (P : Polynomial ℤ) :
    evalZeta5 (P.map (Int.castRingHom ℚ))
      = Polynomial.eval₂ (Int.castRingHom ℝ) zeta5 P := by
  have hstep : evalZeta5 (P.map (Int.castRingHom ℚ))
      = Polynomial.eval₂ (algebraMap ℚ ℝ) zeta5 (P.map (Int.castRingHom ℚ)) := by
    simp [evalZeta5, evalZeta5Hom, Polynomial.aeval_def]
  rw [hstep, Polynomial.eval₂_map]
  congr 1

/-- **Theorem 1.1** (p. 2).  `ζ(5)` is irrational, given Theorem 2.1 at `M = 200`.

This is the paper's "Proof of Theorem 1.1" on p. 21, and it is complete: no `sorry`. -/
theorem theorem_1_1 (Alloc : ∀ n, InnerAllocFamily n 200) (hT : Theorem_2_1 Alloc) :
    Irrational zeta5 := by
  obtain ⟨n₀, hn₀⟩ := hT
  refine irrational_of_integerPolynomials zeta5 n₀ ?_
  intro n hn
  obtain ⟨⟨P, hP⟩, hdeg, hpos, hsmall⟩ := hn₀ n hn
  have hinj : Function.Injective ((Int.castRingHom ℚ) : ℤ → ℚ) := by
    intro x y hxy
    simpa using hxy
  refine ⟨P, ?_, ?_, ?_⟩
  · have hnd : P.natDegree = (Q n 200 (Alloc n)).natDegree := by
      rw [← hP, Polynomial.natDegree_map_eq_of_injective hinj]
    rw [hnd, hdeg]
    simp [h]
  · rw [← evalZeta5_map, hP]; exact hpos
  · rw [← evalZeta5_map, hP]; exact hsmall

end

end Zeta5
