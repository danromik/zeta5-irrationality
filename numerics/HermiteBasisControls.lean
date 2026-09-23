-- Known-answer and must-fail controls for Zeta5.HermiteBasis.det_coeffMatrix_unimodular
-- (NOT part of the lake package).
-- Check from the repository root, after `lake build`:  lake env lean numerics/HermiteBasisControls.lean
-- Known answers computed independently in exact arithmetic (sympy, 2026-09-23):
--   p = 7, nodes u = (0, 1, 4) = (0², 1², 2²), multiplicities m = (1, 2, 1), rows in the order
--   (0,0), (1,0), (1,1), (2,0):  coefficient matrix [[4,9,6,1],[0,4,1,0],[0,4,5,1],[0,1,2,1]],
--   det = 36 = (1−0)^{1·2} (4−0)^{1·1} (4−1)^{2·1},  v_7 = 0.
--   MUST-FAIL: nodes (8, 1) over ℤ, both ≡ 1 (mod 7), m = (1, 1): rows X+1, X+8,
--   det = −7, v_7 = 1  (so the injectivity hypothesis `hu` cannot be dropped).
import Zeta5.HermiteBasis

open Polynomial

namespace Zeta5.HermiteBasis.Controls
/-- The multiplicities of the positive control. -/
abbrev m3 : Fin 3 → ℕ := ![1, 2, 1]
/-- Row labelling `Fin 4 ≃ Σ a, Fin (m3 a)`: `0 ↦ (0,0), 1 ↦ (1,0), 2 ↦ (1,1), 3 ↦ (2,0)`. -/
noncomputable abbrev σ4 : Fin 4 ≃ Σ a : Fin 3, Fin (m3 a) :=
  (finCongr (by decide)).trans finSigmaFinEquiv.symm

/-- The rational coefficient matrix `U` of the lemma, for the positive control. -/
noncomputable abbrev U4 : Matrix (Fin 4) (Fin 4) ℚ :=
  coeffMatrix fun k => (hermitePoly (fun c : Fin 3 => ((c : ℕ) : ℤ) ^ 2) m3
      (σ4 k).1 ((σ4 k).2 : ℕ)).map (Int.castRingHom ℚ)

/-- **Known answer 1**: the four rows, expanded. -/
theorem U4_rows : (fun k : Fin 4 => (hermitePoly (fun c : Fin 3 => ((c : ℕ) : ℤ) ^ 2) m3
      (σ4 k).1 ((σ4 k).2 : ℕ)).map (Int.castRingHom ℚ)) =
    ![((X + 1) ^ 2 * (X + 4) : ℚ[X]), X * (X + 4), X * (X + 4) * (X + 1), X * (X + 1) ^ 2] := by
  have e0 : (Finset.univ.erase (0 : Fin 3)) = {1, 2} := by decide
  have e1 : (Finset.univ.erase (1 : Fin 3)) = {0, 2} := by decide
  have e2 : (Finset.univ.erase (2 : Fin 3)) = {0, 1} := by decide
  -- the row labelling, evaluated (first the index `i`, then the class `a`, to avoid a
  -- dependent rewrite)
  have t0 : ((σ4 0).2 : ℕ) = 0 := by decide
  have t1 : ((σ4 1).2 : ℕ) = 0 := by decide
  have t2 : ((σ4 2).2 : ℕ) = 1 := by decide
  have t3 : ((σ4 3).2 : ℕ) = 0 := by decide
  have s0 : (σ4 0).1 = 0 := by decide
  have s1 : (σ4 1).1 = 1 := by decide
  have s2 : (σ4 2).1 = 1 := by decide
  have s3 : (σ4 3).1 = 2 := by decide
  funext k
  fin_cases k <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, t0, t1, t2, t3] <;>
    simp only [s0, s1, s2, s3, hermitePoly, e0, e1, e2, Finset.prod_pair (show (1 : Fin 3) ≠ 2 by decide),
      Finset.prod_pair (show (0 : Fin 3) ≠ 2 by decide),
      Finset.prod_pair (show (0 : Fin 3) ≠ 1 by decide)] <;>
    simp [m3, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]

/-- **Known answer 2**: the coefficient matrix, entry by entry (sympy gives the same). -/
theorem U4_eq : U4 = !![4, 9, 6, 1; 0, 4, 1, 0; 0, 4, 5, 1; 0, 1, 2, 1] := by
  rw [U4, U4_rows]
  have h0 : ((X + 1) ^ 2 * (X + 4) : ℚ[X]) = X ^ 3 + C 6 * X ^ 2 + C 9 * X + C 4 := by
    simp only [map_ofNat]; ring
  have h1 : (X * (X + 4) : ℚ[X]) = X ^ 2 + C 4 * X := by simp only [map_ofNat]; ring
  have h2 : (X * (X + 4) * (X + 1) : ℚ[X]) = X ^ 3 + C 5 * X ^ 2 + C 4 * X := by
    simp only [map_ofNat]; ring
  have h3 : (X * (X + 1) ^ 2 : ℚ[X]) = X ^ 3 + C 2 * X ^ 2 + X := by simp only [map_ofNat]; ring
  rw [h0, h2, h1, h3]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coeffMatrix, coeff_X, coeff_C, coeff_X_pow, coeff_C_mul]

/-- **Known answer 3**: `det U = 36 = 1^2 · 4 · 3^2`, prime to `7`. -/
theorem U4_det : U4.det = 36 := by
  rw [U4_eq]
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  norm_num

/-- **The lemma on this instance** (so its hypotheses are satisfiable and it is not vacuous);
its conclusion agrees with the known answer `U4_det`. -/
example : U4.det ≠ 0 ∧ padicValRat 7 U4.det = 0 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  refine det_coeffMatrix_unimodular (p := 7) (fun c : Fin 3 => ((c : ℕ) : ZMod 7) ^ 2)
    (sq_injective (M := 2) (by norm_num)) m3 σ4 _ fun k => ?_
  rw [hermitePoly_map]
  congr 1
  funext c
  simp

/-- The same conclusion recomputed from the known answer, independently of the lemma. -/
example : padicValRat 7 U4.det = 0 := by
  rw [U4_det]
  have : padicValRat 7 ((36 : ℤ) : ℚ) = 0 := by
    rw [padicValRat.of_int, padicValInt.eq_zero_of_not_dvd (by norm_num)]
    rfl
  simpa using this


/-- **MUST-FAIL control**: drop injectivity.  Nodes `8, 1` over `ℤ` collide mod `7`; every
other hypothesis of the lemma holds (with `u = (1, 1)` in `ZMod 7`), but the coefficient
matrix of the rows `X + 1`, `X + 8` has determinant `−7`, so `v_7(det U) = 1 ≠ 0`. -/
example : (coeffMatrix fun k : Fin 2 =>
      (hermitePoly (![8, 1] : Fin 2 → ℤ) ![1, 1] k 0).map (Int.castRingHom ℚ)).det = -7 ∧
    padicValRat 7 (-7) = 1 ∧
    (∀ k : Fin 2, (hermitePoly (![8, 1] : Fin 2 → ℤ) ![1, 1] k 0).map
      (Int.castRingHom (ZMod 7)) = hermitePoly (![1, 1] : Fin 2 → ZMod 7) ![1, 1] k 0) ∧
    ¬ Function.Injective (![1, 1] : Fin 2 → ZMod 7) := by
  have e0 : (Finset.univ.erase (0 : Fin 2)) = {1} := by decide
  have e1 : (Finset.univ.erase (1 : Fin 2)) = {0} := by decide
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Matrix.det_fin_two]
    simp [coeffMatrix, hermitePoly, e0, e1, coeff_X, coeff_one]
    norm_num
  · have : padicValRat 7 ((7 : ℤ) : ℚ) = 1 := by
      rw [padicValRat.of_int]
      norm_num [padicValInt]
    rw [padicValRat.neg]
    simpa using this
  · intro k
    rw [hermitePoly_map]
    congr 1
    funext c
    fin_cases c <;> decide
  · intro h
    exact absurd (h (a₁ := 0) (a₂ := 1) rfl) (by decide)

end Zeta5.HermiteBasis.Controls
