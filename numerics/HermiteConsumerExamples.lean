-- Usage examples for Zeta5.HermiteBasis.det_coeffMatrix_unimodular (NOT part of the Lake library).
-- Written before the lemma was proved, to check that its statement is the one both consumers
-- need: the outer basis (4.11) and the inner basis (4.5) each apply it with light glue.
-- Check from the repository root, after `lake build`:  lake env lean numerics/HermiteConsumerExamples.lean
import Zeta5.OuterRange
import Zeta5.Section3

/-! Examples (not part of the library): both consumers use
`Zeta5.HermiteBasis.det_coeffMatrix_unimodular` with only light glue. -/

open Polynomial

namespace Zeta5

/-- OUTER consumer: from integer rows reducing to the Hermite basis with nodes `c²` and
multiplicities `outerDim`, rows labelled by `eρ`, get `U` and a unit `c` with
`Δ_K = C c · det Gram(U)` and `rowPoly U k = row k`. -/
example (n p : ℕ) [Fact p.Prime] (eρ : OuterRows n p ≃ Fin (h n))
    (g : Fin (h n) → ℤ[X])
    (hg : ∀ k, (g k).map (Int.castRingHom (ZMod p)) =
       HermiteBasis.hermitePoly (fun c : Fin (mHalf p + 1) => (((c : ℕ) : ZMod p)) ^ 2)
         (fun c => outerDim n p (c : ℕ)) (eρ.symm k).1 ((eρ.symm k).2 : ℕ))
    (hdeg : ∀ k, ((g k).map (Int.castRingHom ℚ)).natDegree < h n) :
    ∃ U : Matrix (Fin (h n)) (Fin (h n)) ℚ, ∃ c : ℚ,
      padicValRat p c = 0 ∧ Delta n = Polynomial.C c * (OuterLocal.Gram n U).det ∧
      ∀ k, OuterLocal.rowPoly U k = (g k).map (Int.castRingHom ℚ) := by
  obtain ⟨h0, hv⟩ := HermiteBasis.det_coeffMatrix_unimodular _ HermiteBasis.sq_injective_half
    _ eρ.symm g hg
  exact ⟨_, _, OuterLocal.padicValRat_unimodular _ hv, OuterLocal.Delta_eq_of_basis _ h0,
    fun k => HermiteBasis.coeffMatrix_row_sum _ k (hdeg k)⟩

/-- INNER consumer: the basis (4.5), labelled by `A.Rows`, gives `B : Matrix A.Rows A.Rows`
and a unit `c ≠ 0` with `Δ_K = C c · det B` — the determinant half of
`entry_bounds_4_2_4_3`. -/
example (n M p : ℕ) [Fact p.Prime] (A : InnerAlloc n M p) (σ : Fin (h n) ≃ A.Rows) :
    ∃ (B : Matrix A.Rows A.Rows ℚ[X]) (c : ℚ),
      c ≠ 0 ∧ padicValRat p c = 0 ∧ Delta n = Polynomial.C c * B.det := by
  let u : Fin (mHalf p + 1) → ZMod p := fun c => ((c : ℕ) : ZMod p) ^ 2
  let uZ : Fin (mHalf p + 1) → ℤ := fun c => ((c : ℕ) : ℤ) ^ 2
  let m : Fin (mHalf p + 1) → ℕ := fun c => A.Ldim (c : ℕ)
  let g : Fin (h n) → ℤ[X] := fun k => HermiteBasis.hermitePoly uZ m (σ k).1 ((σ k).2 : ℕ)
  have hg : ∀ k, (g k).map (Int.castRingHom (ZMod p))
      = HermiteBasis.hermitePoly u m (σ k).1 ((σ k).2 : ℕ) := by
    intro k
    simp only [g, HermiteBasis.hermitePoly_map]
    congr 1
    funext c
    simp [uZ, u]
  obtain ⟨h0, hv⟩ := HermiteBasis.det_coeffMatrix_unimodular u HermiteBasis.sq_injective_half
    m σ g hg
  refine ⟨(OuterLocal.Gram n (HermiteBasis.coeffMatrix fun k => (g k).map (Int.castRingHom ℚ))).submatrix
      σ.symm σ.symm, _, inv_ne_zero (pow_ne_zero 2 h0), OuterLocal.padicValRat_unimodular _ hv, ?_⟩
  rw [Matrix.det_submatrix_equiv_self]
  exact OuterLocal.Delta_eq_of_basis _ h0

/-- INNER glue: the integer row maps to the paper's `A.rowPoly` (product over `range`). -/
example (n M p : ℕ) (A : InnerAlloc n M p) (a : Fin (mHalf p + 1)) (i : ℕ) :
    (HermiteBasis.hermitePoly (fun c : Fin (mHalf p + 1) => ((c : ℕ) : ℤ) ^ 2)
        (fun c => A.Ldim (c : ℕ)) a i).map (Int.castRingHom ℚ)
      = A.rowPoly (a : ℕ) i := by
  rw [HermiteBasis.hermitePoly_map, HermiteBasis.hermitePoly, InnerAlloc.rowPoly]
  congr 1
  · -- reindex `∏_{c ∈ univ.erase a}` over `Fin (m+1)` to `∏_{c ∈ (range (m+1)).erase a}` over `ℕ`
    have himg : (Finset.univ.erase a).image (fun c : Fin (mHalf p + 1) => (c : ℕ))
        = (Finset.range (mHalf p + 1)).erase (a : ℕ) := by
      ext x
      simp only [Finset.mem_image, Finset.mem_erase, Finset.mem_univ, and_true,
        Finset.mem_range]
      constructor
      · rintro ⟨c, hca, rfl⟩
        exact ⟨fun h => hca (Fin.ext h), c.isLt⟩
      · rintro ⟨hxa, hx⟩
        exact ⟨⟨x, hx⟩, fun h => hxa (by rw [← h]), rfl⟩
    rw [← himg, Finset.prod_image (fun x _ y _ h => Fin.ext h)]
    refine Finset.prod_congr rfl fun c _ => ?_
    simp

end Zeta5
