/-
Zeta5/HermiteBasisCore.lean

**Proof of the shared unimodularity lemma** `Zeta5.HermiteBasis.det_coeffMatrix_unimodular`.

This file imports only Mathlib and is imported by `Zeta5/HermiteBasis.lean`, which holds the
definitions `hermitePoly`, `coeffMatrix` and the (fixed) statement of the shared lemma.  Since
this file sits *below* `HermiteBasis.lean` in the import graph, it cannot mention those two
definitions; its statements are written with the definitions unfolded:

* `hermitePoly u m a i  =  (∏ c ∈ univ.erase a, (X + C (u c)) ^ m c) * (X + C (u a)) ^ i`,
* `coeffMatrix f        =  Matrix.of fun k i => (f k).coeff i`,

and `HermiteBasis.lean` closes its statements by applying the results below (the two sides are
definitionally equal).

## The argument (p. 10 of the paper, made precise)

1. **Over a field `F`, the Hermite family is linearly independent** (`hermite_sum_eq_zero`).
   Write `P_a = ∏_{c≠a} (X + u_c)^{m_c}` and suppose `∑_{(a,i)} v_{a,i} P_a (X+u_a)^i = 0`.
   Group by `a`: `∑_a P_a w_a = 0` with `w_a = ∑_{i<m_a} v_{a,i} (X+u_a)^i`, `deg w_a < m_a`.
   For `b ≠ a`, `(X+u_a)^{m_a} ∣ P_b`; hence `(X+u_a)^{m_a} ∣ P_a w_a`.  Because the nodes
   are pairwise distinct, `(X+u_a)^{m_a}` is coprime to `P_a`, so `(X+u_a)^{m_a} ∣ w_a`, and the
   degree bound forces `w_a = 0`.  Substituting `X ↦ X − u_a` turns `w_a` into
   `∑_i v_{a,i} X^i`, so every `v_{a,i} = 0`.
2. **Dimension count** (`det_coeffMatrix_hermite_ne_zero'`).  There are `hh = ∑_a m_a` rows
   (read off from `σ : Fin hh ≃ Σ a, Fin (m a)`), each of degree `∑_{c≠a} m_c + i < hh`.  If the
   `hh × hh` coefficient matrix were singular, a nonzero `v` with `v ᵥ* M = 0` would give a
   polynomial `∑_k v_k f_k` of degree `< hh` all of whose coefficients below `hh` vanish,
   i.e. a vanishing nontrivial combination, contradicting step 1.
3. **Reduction mod `p`** (`det_coeffMatrix_unimodular'`).  The rational coefficient matrix of
   the integer rows `g k` is the image of the integer matrix `Ug = (coeff (g k) i)`; its
   reduction mod `p` is (by `hg`) the Hermite coefficient matrix over the field `ZMod p`, whose
   determinant is nonzero by step 2.  So `(det Ug : ZMod p) ≠ 0`, i.e. `p ∤ det Ug`; hence
   `det Ug ≠ 0` and `v_p(det Ug) = 0`.
-/
import Mathlib

namespace Zeta5

namespace HermiteBasisCore

open Polynomial

section Field

variable {F : Type*} [Field F] {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- Distinct nodes give coprime factors: `(X + u_a)^n` is coprime to
`P_a = ∏_{c ≠ a} (X + u_c)^{m_c}`. -/
theorem X_add_C_pow_isCoprime_prod (u : κ → F) (hu : Function.Injective u) (m : κ → ℕ)
    (a : κ) (n : ℕ) :
    IsCoprime ((X + C (u a)) ^ n) (∏ c ∈ Finset.univ.erase a, (X + C (u c)) ^ m c) := by
  refine IsCoprime.prod_right fun c hc => IsCoprime.pow ?_
  have hca : a ≠ c := Ne.symm (Finset.ne_of_mem_erase hc)
  have hinj : Function.Injective (fun c => -u c) := fun x y h => hu (neg_injective h)
  have h := Polynomial.pairwise_coprime_X_sub_C hinj hca
  simpa [Function.onFun, sub_eq_add_neg] using h

/-- The degree of the Hermite polynomial: `∑_{c ≠ a} m_c + i`. -/
theorem natDegree_hermite (u : κ → F) (m : κ → ℕ) (a : κ) (i : ℕ) :
    ((∏ c ∈ Finset.univ.erase a, (X + C (u c)) ^ m c) * (X + C (u a)) ^ i).natDegree =
      (∑ c ∈ Finset.univ.erase a, m c) + i := by
  rw [Monic.natDegree_mul
      (monic_prod_of_monic _ _ fun c _ => (monic_X_add_C (u c)).pow (m c))
      ((monic_X_add_C (u a)).pow i),
    natDegree_prod_of_monic _ _ fun c _ => (monic_X_add_C (u c)).pow (m c),
    (monic_X_add_C (u a)).natDegree_pow, natDegree_X_add_C, mul_one]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [(monic_X_add_C (u c)).natDegree_pow, natDegree_X_add_C, mul_one]

/-- **Step 1: linear independence of the Hermite family, over a field.**  A vanishing
combination `∑_{(a,i)} v_{a,i} · ∏_{c≠a}(X+u_c)^{m_c}(X+u_a)^i = 0` has all `v_{a,i} = 0`,
provided the nodes `u` are pairwise distinct. -/
theorem hermite_sum_eq_zero (u : κ → F) (hu : Function.Injective u) (m : κ → ℕ)
    (v : (Σ a : κ, Fin (m a)) → F)
    (hv : ∑ r, C (v r) *
      ((∏ c ∈ Finset.univ.erase r.1, (X + C (u c)) ^ m c) * (X + C (u r.1)) ^ (r.2 : ℕ)) = 0) :
    v = 0 := by
  set P : κ → F[X] := fun a => ∏ c ∈ Finset.univ.erase a, (X + C (u c)) ^ m c with hP
  set w : κ → F[X] := fun a => ∑ i : Fin (m a), C (v ⟨a, i⟩) * (X + C (u a)) ^ (i : ℕ)
    with hw
  have hsum : ∑ a, P a * w a = 0 := by
    rw [← hv, Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [hP, hw, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hw0 : ∀ a, w a = 0 := by
    intro a
    have hdvd : (X + C (u a)) ^ m a ∣ P a * w a := by
      have h1 : P a * w a = -∑ b ∈ Finset.univ.erase a, P b * w b := by
        rw [eq_neg_iff_add_eq_zero,
          Finset.add_sum_erase _ (fun b => P b * w b) (Finset.mem_univ a)]
        exact hsum
      rw [h1, dvd_neg]
      refine Finset.dvd_sum fun b hb => Dvd.dvd.mul_right ?_ _
      exact Finset.dvd_prod_of_mem (fun c => (X + C (u c)) ^ m c)
        (Finset.mem_erase.mpr ⟨Ne.symm (Finset.ne_of_mem_erase hb), Finset.mem_univ a⟩)
    have hdvd' : (X + C (u a)) ^ m a ∣ w a :=
      (X_add_C_pow_isCoprime_prod u hu m a (m a)).dvd_of_dvd_mul_left hdvd
    by_contra hne
    have hm : 0 < m a := by
      rcases Nat.eq_zero_or_pos (m a) with h | h
      · exfalso
        apply hne
        simp only [hw]
        exact Finset.sum_eq_zero fun i _ => absurd i.isLt (by omega)
      · exact h
    have hle : (w a).natDegree ≤ m a - 1 := by
      refine natDegree_sum_le_of_forall_le _ _ fun i _ => ?_
      refine (natDegree_C_mul_le _ _).trans (natDegree_pow_le.trans ?_)
      rw [natDegree_X_add_C, mul_one]
      have := i.isLt
      omega
    have hdeg : (w a).natDegree < ((X + C (u a)) ^ m a).natDegree := by
      rw [(monic_X_add_C (u a)).natDegree_pow, natDegree_X_add_C, mul_one]
      omega
    exact hne (eq_zero_of_dvd_of_natDegree_lt hdvd' hdeg)
  funext r
  obtain ⟨a, i⟩ := r
  have hcomp : (w a).comp (X - C (u a)) = ∑ j : Fin (m a), C (v ⟨a, j⟩) * X ^ (j : ℕ) := by
    simp only [hw, sum_comp, mul_comp, C_comp, pow_comp, add_comp, X_comp, sub_add_cancel]
  rw [hw0 a, zero_comp] at hcomp
  have hc := congrArg (fun q => q.coeff (i : ℕ)) hcomp
  simp only [coeff_zero, finsetSum_coeff, coeff_C_mul_X_pow, Fin.val_inj] at hc
  rw [Finset.sum_ite_eq] at hc
  simpa using hc.symm

/-- **Step 2: over a field, the Hermite coefficient matrix is invertible.**  The rows are
labelled by `σ : Fin hh ≃ Σ a, Fin (m a)`; the matrix is `coeffMatrix` of the Hermite family,
unfolded. -/
theorem det_coeffMatrix_hermite_ne_zero' (u : κ → F) (hu : Function.Injective u) (m : κ → ℕ)
    {hh : ℕ} (σ : Fin hh ≃ Σ a : κ, Fin (m a)) :
    (Matrix.of fun (k : Fin hh) (i : Fin hh) =>
      ((∏ c ∈ Finset.univ.erase (σ k).1, (X + C (u c)) ^ m c) *
        (X + C (u (σ k).1)) ^ ((σ k).2 : ℕ)).coeff (i : ℕ)).det ≠ 0 := by
  set H : (Σ a : κ, Fin (m a)) → F[X] := fun r =>
    (∏ c ∈ Finset.univ.erase r.1, (X + C (u c)) ^ m c) * (X + C (u r.1)) ^ (r.2 : ℕ) with hH
  have hcard : hh = ∑ a, m a := by
    simpa [Fintype.card_sigma] using Fintype.card_congr σ
  have hdeg : ∀ r, (H r).natDegree < hh := by
    rintro ⟨a, i⟩
    simp only [hH]
    rw [natDegree_hermite, hcard, ← Finset.sum_erase_add _ _ (Finset.mem_univ a)]
    have := i.isLt
    omega
  intro hdet
  obtain ⟨v, hv0, hvM⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hdet
  apply hv0
  have hpoly : ∑ k, C (v k) * H (σ k) = 0 := by
    ext j
    rw [finsetSum_coeff, coeff_zero]
    simp only [coeff_C_mul]
    by_cases hj : j < hh
    · have := congrFun hvM ⟨j, hj⟩
      simpa [Matrix.vecMul, dotProduct, hH] using this
    · refine Finset.sum_eq_zero fun k _ => ?_
      rw [coeff_eq_zero_of_natDegree_lt (by have := hdeg (σ k); omega), mul_zero]
  have hv' : ∑ r, C ((v ∘ σ.symm) r) * H r = 0 := by
    rw [← hpoly, ← Equiv.sum_comp σ]
    simp
  have h0 := hermite_sum_eq_zero u hu m (v ∘ σ.symm) hv'
  funext k
  simpa using congrFun h0 (σ k)

end Field

/-- **Step 3: the shared unimodularity lemma, with the definitions unfolded.**  Integer rows
`g k` reducing mod `p` to a Hermite basis with pairwise distinct nodes have a rational
coefficient matrix `U` with `det U ≠ 0` and `v_p(det U) = 0`. -/
theorem det_coeffMatrix_unimodular' {p : ℕ} [Fact p.Prime] {κ : Type*} [Fintype κ]
    [DecidableEq κ] (u : κ → ZMod p) (hu : Function.Injective u) (m : κ → ℕ) {hh : ℕ}
    (σ : Fin hh ≃ Σ a : κ, Fin (m a)) (g : Fin hh → ℤ[X])
    (hg : ∀ k, (g k).map (Int.castRingHom (ZMod p)) =
      (∏ c ∈ Finset.univ.erase (σ k).1, (X + C (u c)) ^ m c) *
        (X + C (u (σ k).1)) ^ ((σ k).2 : ℕ)) :
    (Matrix.of fun (k : Fin hh) (i : Fin hh) =>
        ((g k).map (Int.castRingHom ℚ)).coeff (i : ℕ)).det ≠ 0 ∧
      padicValRat p (Matrix.of fun (k : Fin hh) (i : Fin hh) =>
        ((g k).map (Int.castRingHom ℚ)).coeff (i : ℕ)).det = 0 := by
  set Ug : Matrix (Fin hh) (Fin hh) ℤ := Matrix.of fun k i => (g k).coeff (i : ℕ) with hUg
  have hQ : (Matrix.of fun (k : Fin hh) (i : Fin hh) =>
      ((g k).map (Int.castRingHom ℚ)).coeff (i : ℕ)) = (Int.castRingHom ℚ).mapMatrix Ug := by
    ext k i
    simp [hUg, coeff_map]
  have hP : (Int.castRingHom (ZMod p)).mapMatrix Ug =
      Matrix.of fun (k : Fin hh) (i : Fin hh) =>
        ((∏ c ∈ Finset.univ.erase (σ k).1, (X + C (u c)) ^ m c) *
          (X + C (u (σ k).1)) ^ ((σ k).2 : ℕ)).coeff (i : ℕ) := by
    ext k i
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, hUg, Matrix.of_apply]
    rw [← hg k, coeff_map]
  have hdetQ : (Matrix.of fun (k : Fin hh) (i : Fin hh) =>
      ((g k).map (Int.castRingHom ℚ)).coeff (i : ℕ)).det = ((Ug.det : ℤ) : ℚ) := by
    rw [hQ, ← RingHom.map_det]
    simp
  have hdetP : ((Ug.det : ℤ) : ZMod p) ≠ 0 := by
    have h := det_coeffMatrix_hermite_ne_zero' u hu m σ
    rw [← hP, ← RingHom.map_det] at h
    simpa using h
  have hndvd : ¬ (p : ℤ) ∣ Ug.det := fun h =>
    hdetP ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h)
  refine ⟨?_, ?_⟩
  · rw [hdetQ]
    intro h0
    apply hdetP
    have : Ug.det = 0 := by exact_mod_cast h0
    rw [this, Int.cast_zero]
  · rw [hdetQ, padicValRat.of_int, padicValInt.eq_zero_of_not_dvd hndvd]
    rfl

end HermiteBasisCore

end Zeta5
