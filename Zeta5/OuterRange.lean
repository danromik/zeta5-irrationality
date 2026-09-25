/-
Zeta5/OuterRange.lean

**§4.2 of the paper (pp. 11–13): the outer range, and Proposition 4.3.**

The paper's text, verbatim, for the statements formalised here:

> Suppose that
>     `p ≥ 7,   p ≤ K < 3p,   p² > 2K,   2N < p,   5N ≤ 2p − 2`.               (4.9)
> These conditions hold when `K ≥ 200M²` and `K/3 < p ≤ K`. …
>     `G_K = A + p^{-1}L,   rank_{ℚ_p} L ≤ r_p = max(0, K + 4N − 2p + 2)`,     (4.10)
> where `L` is integral.  To see the rank bound, the polynomial quotient of `W t^{i+j}/D_tail`
> has degree at most `i + j + 6N − K`.  Hence `L_ij = 0` if `i + j < K − 6N + 2p − 3`.  Its
> first `h − r_p` rows and columns vanish.  Thus the rank bound holds over `ℚ_p`, not merely
> modulo `p`.
>
> … `q_{a,i}(t) = (t+a²)^i` for `0 ≤ i < ℓ−2`, `E_a(t)(t+a²)^{i−(ℓ−2)}` for
> `ℓ−2 ≤ i < ℓ−δ`.                                                            (4.11)
>
> … Thus valid nonpositive half-integer weights are
>     `w_{a,i} = min(0, i + 3δ − (ℓ+4)/2)` for `i < ℓ−2`,  `0` for `i ≥ ℓ−2`.   (4.12)
> A single zero-class pole has weight `−1/2`.  For two zero-class poles `p, 2p`, the rows
> `1, t+p²` give entry bounds `−3, −1, 0`, so the weights `−2, 0` are valid.
>
> Let `v = K − p⌊K/p⌋` and set `u = max(0, N+v−p+1)`, `t_p = min(N,v) + u`.
> Summing (4.12) and applying Lemma 4.2 gives the integer
>     `γ_p^out = −7(K−p) + 6t_p − 1 − min(r_p, p−1−N+u)`            for `K < 2p`,
>     `γ_p^out = −7(K−p) + 3 + 12N + 5t_p − min(r_p, p+u)`          for `K ≥ 2p`.   (4.14)
> For a class containing a removed pole, the counts used in this sum are
>     `ℓ` in a removed class      | 2  3  4  5  6
>     `−2 ∑_i w_{a,i}`            | 0  1  2  4  6
>     `#{i | w_{a,i} = 0}`        | 1  1  2  2  3
> An unremoved class has cost `7(ℓ−2)` and two zero weights.  The conditions `a ≤ v` and
> `a ≥ p−v` among `a ≤ N` give `t_p`, with overlap `u`.  The zero-class costs are `1` and `4`.
> These counts prove (4.14).
>
> **Proposition 4.3.**  Under (4.9), `v_p^G(Δ_K) ≥ γ_p^out`.  For `p > K`, one has
> `v_p^G(Δ_K) ≥ 0`.
>
> *Proof.*  The first assertion follows from (4.10) and Lemma 4.2.  If `p > K`, every pole is
> less than `p`.  Each square class contains at most two poles, and the same divided-difference
> argument makes its contribution integral.  The polynomial correction vanishes because
> `K + 4N + 1 < 2p`.  Thus the whole matrix is integral in a unimodular local basis.

WHAT THIS FILE PROVES.

*  **§A.  The rank hypothesis of Lemma 4.2, in a form that applies over `ℚ[X]`.**
   `Zeta5.lemma_4_2` (`Lemma42.lean`) is stated with `Matrix.rank L ≤ r`, which forces a
   *field*; `ℚ[X]` is not one.  The hypothesis is replaced here in three steps:
   - `lemma_4_2_of_vanishing`: the rank enters the proof of (4.13) through exactly one
     consequence — the complementary-minor terms taking more than `r` columns from `L`
     vanish — so that consequence becomes the hypothesis.  No field; any commutative ring.
   - `vanishing_of_zeroCols` / `lemma_4_2_of_zeroCols`: the paper's own reason for the rank
     bound ("its first `h − r_p` rows and columns vanish") supplies that consequence directly,
     by a zero column.  This is *stronger* than the rank bound, and it is correct in the
     **monomial** basis, which is where the paper proves it.
   - `vanishing_of_rank` / `lemma_4_2_of_rank_map` / `lemma_4_2_gauss_rank`: the literal
     statement `rank_{ℚ_p} L ≤ r_p` of (4.10), with the rank taken after an injective ring map
     into a field — for `ℚ[X]` the inclusion into `RatFunc ℚ`.  This is the "view the matrices
     over the fraction field `ℚ(X)`" resolution, and it is **the form §4.2 uses**: the
     vanishing-columns form does *not* survive the change of basis to (4.11) (see the
     docstring of `Zeta5.outer_local_analysis`, and the head of `Zeta5/OuterLocal.lean`).
   `lemma_4_2_gauss_of_vanishing` is the Gauss-valuation instance ("The same assertion holds
   for the Gauss valuation of polynomial entries", p. 12) with the half-integer weights
   carried as `W = 2w`.

*  **§B.  The rank bound (4.10) from the degree count.**  `zeroCols_of_lowDegree`,
   `card_compl_lt_filter`, `outer_column_cut`: `L_ij = 0` for `i + j < K − 6N + 2p − 3` forces
   the first `2p − 5N − 2` columns to vanish, that number is exactly the paper's `h − r_p`,
   and the complement has at most `r_p` elements.

*  **§C.  (4.9), and the residue-class counts.**  `OuterHyp` is (4.9) minus its lower bound
   `p ≤ K` (the second assertion of Proposition 4.3, `p > K`, satisfies all the rest —
   `outerHyp_of_gt` — so the whole of §D–§E is uniform in `m_K ∈ {0,1,2}`).  `eIdx` is
   `ℓ_K(a) − 2m_K = 1_{a≤v} + 1_{a≥p−v}` (`ell_closed`), and `sum_eIdx_mHalf`,
   `sum_eIdx_N`, `sum_eIdx_two_N` are the counts "the conditions `a ≤ v` and `a ≥ p − v` among
   `a ≤ N` give `t_p`, with overlap `u`" of p. 13.

*  **§D.  The weights (4.12) and the table on p. 13.**  `outerW` is (4.12) doubled.
   `table_removed` and `table_unremoved` prove the five printed columns
   (`−2∑w = 0,1,2,4,6`, `#{w=0} = 1,1,2,2,3`) and the unremoved-class line (cost `7(ℓ−2)`,
   two zero weights), by explicit computation.  `outerWZero` is the zero class ("costs `1`
   and `4`").

*  **§E.  The assembly (4.14).**  `outerRows_card` (the dimension identity
   `m_K + ∑_a (ℓ_a − δ_a) = h`), `sum_outerWeight_eq` (`∑ W` in closed form),
   `outerZeroCount_eq` (`z = p−1−N+u` resp. `p+u`, and `z = h` for `p > K`), and finally
   `gammaOut_eq` — `∑_ρ W_ρ − min(r_p, z) = γ_p^out` in both printed branches of (4.14) and
   in the range `p > K`.  This is the paper's "These counts prove (4.14)"; the audit checked
   it numerically over 1975 pairs `(K = 40n, p)`, here it is a theorem in `n` and `p`.

*  **§F.  The reduction.**  `prop_4_3_of_local_data_vanishing`, and its two corollaries
   `prop_4_3_of_local_data` (vanishing columns) and `prop_4_3_of_local_data_rank` (the literal
   `rank_{ℚ_p} L ≤ r_p` of (4.10), which is the one §4.2 uses): from the local data of §4.2 —
   the unimodular basis (4.11), the splitting (4.10), and the entry bound
   `v_p^G(A_{uv}) ≥ w_u + w_v` for the weights (4.12) — Proposition 4.3 follows.  This is the
   determinant half of the proof on p. 13.

*  **§G.  Proposition 4.3.**  `Outer.prop_4_3` and `Outer.prop_4_3_large` are derived
   from `outer_local_analysis` (proved in `Zeta5/OuterBasis.lean`),
   which is the *local* half: the construction of the basis (4.11), its `ℤ_p`-unimodularity, the entry bounds
   behind (4.12), and the divided-difference congruence.  Two `example`s check that the two
   theorems have *literally* the types of `Zeta5.prop_4_3` and `Zeta5.prop_4_3_large` in
   `Interface.lean`, which they prove (they sit in the namespace `Zeta5.Outer` so that both
   files can be imported together).

*  **§H.  Known-answer controls** against the exact determinants computed in the referee
   audit (see README, "Provenance"): `γ_p^out` is recomputed
   by Lean from `Zeta5.gammaOut` at all 37 primes of the audit's three exact tests
   (`K = 40, 80, 120`) and at `p > K`, and agrees with the stored values in every case.

`Zeta5.outer_local_analysis` (whose docstring states the paper
text it stands for) is proved from `Zeta5.OuterBasis.outer_local_core`
(`Zeta5/OuterBasis.lean`), which this file imports.
-/
import Zeta5.Lemma42
import Zeta5.Section41
import Zeta5.OuterLocal
import Zeta5.OuterBasis

namespace Zeta5

open Polynomial Finset

noncomputable section

/-! # §A.  Lemma 4.2 without the field hypothesis

`Zeta5.lemma_4_2` needs `Matrix.rank L ≤ r`, hence a field.  The rank enters its proof in
exactly one place: `mixCol_det_eq_zero`, i.e. "terms with `k > r` vanish".  Taking *that* as
the hypothesis makes the lemma available over any commutative ring, in particular over
`ℚ[X]` with the Gauss valuation, which is what §4.2 needs. -/

section Lemma42General

variable {F : Type*} [CommRing F] {hh : ℕ}

/-- **Lemma 4.2** (p. 12), with the rank hypothesis replaced by its only consequence.

Hypotheses as in `Zeta5.lemma_4_2`, except that `Matrix.rank L ≤ r` is replaced by
`hvanish`: every complementary-minor term of `det(A + p^{-1}L)` taking more than `r` columns
from `L` vanishes.  That is the paper's "Terms with `k > r` vanish", and it is all the proof
of (4.13) uses.  Over a field it follows from `rank L ≤ r` (`Zeta5.mixCol_det_eq_zero`); over
`ℚ[X]` it follows from the paper's stronger statement that the first `h − r_p` columns of `L`
vanish (`lemma_4_2_of_zeroCols`).

The conclusion is (4.13) verbatim: `v det(A + p^{-1}L) ≥ 2 ∑_i w_i − min(r, z)`. -/
theorem lemma_4_2_of_vanishing (V : ValFil F) (w : Fin hh → ℚ)
    (hw0 : ∀ i, w i ≤ 0) (hwhalf : ∀ i, ∃ k : ℤ, w i = (k : ℚ) / 2)
    (A L : Matrix (Fin hh) (Fin hh) F)
    (hA : ∀ i j, V.vge (A i j) (w i + w j))
    (pinv : F) (hpinv : V.vge pinv (-1))
    (hL : ∀ i j, V.vge (L i j) 0)
    (r : ℕ)
    (hvanish : ∀ t : Finset (Fin hh), r < (Finset.univ \ t).card →
      (mixCol A (pinv • L) t).det = 0)
    (z : ℕ) (hz : z = (Finset.univ.filter (fun i => w i = 0)).card) :
    V.vge (A + pinv • L).det (2 * ∑ i, w i - ((min r z : ℕ) : ℚ)) := by
  classical
  have hB : ∀ i j, V.vge ((pinv • L) i j) (-1) := by
    intro i j
    have := V.vge_mul hpinv (hL i j)
    simpa [Matrix.smul_apply, smul_eq_mul] using this
  rw [det_add_eq_sum_mixCol]
  refine V.vge_sum _ _ _ fun t _ => ?_
  set S : Finset (Fin hh) := Finset.univ \ t with hSdef
  by_cases hbig : r < S.card
  · rw [hvanish t hbig]
    exact V.vge_zero _
  rw [Nat.not_lt] at hbig
  rw [Matrix.det_apply']
  refine V.vge_sum _ _ _ fun σ _ => ?_
  refine V.vge_intUnit_mul ?_
  have hprod : V.vge (∏ i, mixCol A (pinv • L) t (σ i) i)
      (∑ i, if i ∈ t then w (σ i) + w i else (-1 : ℚ)) := by
    refine V.vge_prod _ _ _ fun i _ => ?_
    by_cases hi : i ∈ t
    · simp only [mixCol_apply, hi, ite_true]; exact hA _ _
    · simp only [mixCol_apply, hi, ite_false]; exact hB _ _
  refine V.vge_mono ?_ hprod
  have hsum : (∑ i, if i ∈ t then w (σ i) + w i else (-1 : ℚ))
      = 2 * (∑ i, w i) - ((S.card : ℚ) + ∑ i ∈ S.image σ, w i + ∑ i ∈ S, w i) := by
    have hfil1 : (Finset.univ.filter (fun i : Fin hh => i ∈ t)) = t := Finset.filter_univ_mem t
    have hfil2 : (Finset.univ.filter (fun i : Fin hh => ¬ i ∈ t)) = S := by
      ext i; simp [hSdef]
    have hsplit : (∑ i, if i ∈ t then w (σ i) + w i else (-1 : ℚ))
        = (∑ i ∈ t, (w (σ i) + w i)) + ∑ _i ∈ S, (-1 : ℚ) := by
      rw [Finset.sum_ite, hfil1, hfil2]
    have htot : ∑ i, (w (σ i) + w i) = 2 * ∑ i, w i := by
      rw [Finset.sum_add_distrib, Equiv.sum_comp σ w]; ring
    have hsub : ∑ i ∈ t, (w (σ i) + w i)
        = (∑ i, (w (σ i) + w i)) - ∑ i ∈ S, (w (σ i) + w i) := by
      rw [hSdef, Finset.sum_sdiff_eq_sub (Finset.subset_univ t)]
      ring
    have himg : ∑ i ∈ S, w (σ i) = ∑ i ∈ S.image σ, w i :=
      (Finset.sum_image (fun x _ y _ hxy => σ.injective hxy)).symm
    rw [hsplit, hsub, htot, Finset.sum_const, nsmul_eq_mul, Finset.sum_add_distrib, himg]
    ring
  rw [hsum]
  have hcardimg : (S.image σ).card = S.card := Finset.card_image_of_injective _ σ.injective
  have hloss := loss_le w hw0 hwhalf r z hz S (S.image σ) hcardimg.symm hbig
  linarith

/-- **"Terms with `k > r` vanish" from a supply of zero columns.**

If `L` has a set `C` of zero columns and at most `r` columns outside `C`, then every
complementary-minor term of `det(A + p^{-1}L)` that takes more than `r` columns from `L` must
take one of them from `C`, i.e. has a zero column, hence vanishes.  This needs no field, and
is the paper's own justification of (4.10): "Its first `h − r_p` rows and columns vanish." -/
lemma vanishing_of_zeroCols (A L : Matrix (Fin hh) (Fin hh) F) (pinv : F)
    (r : ℕ) (C : Finset (Fin hh)) (hC : ∀ i j, j ∈ C → L i j = 0) (hCr : Cᶜ.card ≤ r) :
    ∀ t : Finset (Fin hh), r < (Finset.univ \ t).card →
      (mixCol A (pinv • L) t).det = 0 := by
  classical
  intro t ht
  have hsplit : ((Finset.univ \ t).filter (fun j => j ∈ C)).card
      + ((Finset.univ \ t).filter (fun j => ¬ j ∈ C)).card = (Finset.univ \ t).card :=
    Finset.card_filter_add_card_filter_not _
  have hsub : ((Finset.univ \ t).filter (fun j => ¬ j ∈ C)) ⊆ Cᶜ := by
    intro j hj
    rw [Finset.mem_compl]
    exact (Finset.mem_filter.1 hj).2
  have hle : ((Finset.univ \ t).filter (fun j => ¬ j ∈ C)).card ≤ r :=
    le_trans (Finset.card_le_card hsub) hCr
  have hpos : 0 < ((Finset.univ \ t).filter (fun j => j ∈ C)).card := by omega
  obtain ⟨j, hj⟩ := Finset.card_pos.1 hpos
  have hjt : j ∉ t := (Finset.mem_sdiff.1 (Finset.mem_filter.1 hj).1).2
  have hjC : j ∈ C := (Finset.mem_filter.1 hj).2
  refine Matrix.det_eq_zero_of_column_eq_zero j ?_
  intro i
  simp [mixCol_apply, hjt, Matrix.smul_apply, hC i j hjC]

/-- **Lemma 4.2 with the paper's own reason for the rank bound.**

(4.10) is justified on p. 12 by "Its first `h − r_p` rows and columns vanish", which is
*stronger* than `rank L ≤ r_p`: a determinant with a zero column is zero, whatever the ring.
`C` is the set of vanishing columns and `r` bounds the number of the others. -/
theorem lemma_4_2_of_zeroCols (V : ValFil F) (w : Fin hh → ℚ)
    (hw0 : ∀ i, w i ≤ 0) (hwhalf : ∀ i, ∃ k : ℤ, w i = (k : ℚ) / 2)
    (A L : Matrix (Fin hh) (Fin hh) F)
    (hA : ∀ i j, V.vge (A i j) (w i + w j))
    (pinv : F) (hpinv : V.vge pinv (-1))
    (hL : ∀ i j, V.vge (L i j) 0)
    (r : ℕ) (C : Finset (Fin hh)) (hC : ∀ i j, j ∈ C → L i j = 0) (hCr : Cᶜ.card ≤ r)
    (z : ℕ) (hz : z = (Finset.univ.filter (fun i => w i = 0)).card) :
    V.vge (A + pinv • L).det (2 * ∑ i, w i - ((min r z : ℕ) : ℚ)) :=
  lemma_4_2_of_vanishing V w hw0 hwhalf A L hA pinv hpinv hL r
    (vanishing_of_zeroCols A L pinv r C hC hCr) z hz

end Lemma42General

section Lemma42Rank

variable {F E : Type*} [CommRing F] [Field E] {hh : ℕ}

/-- **"Terms with `k > r` vanish" from the rank bound `rank_{ℚ_p} L ≤ r` of (4.10).**

`φ` is an injective ring map into a field; the vanishing is proved there — where `Matrix.rank`
makes sense — and transported back, which is legitimate because the terms are *equal to zero*
and `φ` is injective.  For `ℚ[X]` one takes `φ = algebraMap ℚ[X] (RatFunc ℚ)`. -/
lemma vanishing_of_rank (φ : F →+* E) (hφ : Function.Injective φ)
    (A L : Matrix (Fin hh) (Fin hh) F) (pinv : F)
    (r : ℕ) (hrank : (L.map φ).rank ≤ r) :
    ∀ t : Finset (Fin hh), r < (Finset.univ \ t).card →
      (mixCol A (pinv • L) t).det = 0 := by
  classical
  intro t ht
  have hmapmix : (mixCol A (pinv • L) t).map φ
      = mixCol (A.map φ) (φ pinv • (L.map φ)) t := by
    ext i j
    by_cases hj : j ∈ t <;>
      simp [Matrix.map_apply, mixCol_apply, hj, Matrix.smul_apply, smul_eq_mul]
  have hzero : φ ((mixCol A (pinv • L) t).det) = 0 := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hmapmix]
    exact mixCol_det_eq_zero (A.map φ) (L.map φ) (φ pinv) hrank t ht
  exact hφ (by rw [hzero, map_zero])

/-- **Lemma 4.2 with the literal rank bound of (4.10), over a coefficient ring that need not
be a field.**

(4.10) reads `rank_{ℚ_p} L ≤ r_p`: the rank is taken *after* mapping the entries into a field.
`φ` is any injective ring map into a field — for `ℚ[X]` one takes the inclusion into
`RatFunc ℚ` (or into `ℚ_p[X] ⊂ ℚ_p(X)`, which is the paper's reading).  The vanishing of the
complementary-minor terms is proved in the field and transported back along `φ`, which is
legitimate because `φ` is injective and the terms are *equal to zero*, not merely small.

This removes the obstacle that `Matrix.rank ≤ r` forces a field, which `ℚ[X]` is not. -/
theorem lemma_4_2_of_rank_map (φ : F →+* E) (hφ : Function.Injective φ)
    (V : ValFil F) (w : Fin hh → ℚ)
    (hw0 : ∀ i, w i ≤ 0) (hwhalf : ∀ i, ∃ k : ℤ, w i = (k : ℚ) / 2)
    (A L : Matrix (Fin hh) (Fin hh) F)
    (hA : ∀ i j, V.vge (A i j) (w i + w j))
    (pinv : F) (hpinv : V.vge pinv (-1))
    (hL : ∀ i j, V.vge (L i j) 0)
    (r : ℕ) (hrank : (L.map φ).rank ≤ r)
    (z : ℕ) (hz : z = (Finset.univ.filter (fun i => w i = 0)).card) :
    V.vge (A + pinv • L).det (2 * ∑ i, w i - ((min r z : ℕ) : ℚ)) :=
  lemma_4_2_of_vanishing V w hw0 hwhalf A L hA pinv hpinv hL r
    (vanishing_of_rank φ hφ A L pinv r hrank) z hz

end Lemma42Rank

/-! ### The Gauss-valuation instance, with half-integer weights

Weights are half-integers, so — exactly as in §4.1 — we carry `W = 2w` as an integer.  The
conclusion of (4.13) is then `v_p^G(det) ≥ ∑_i W i − min(r,z)`, an integer bound, i.e.
`Zeta5.vGAtLeast`. -/

/-- **Lemma 4.2 for the Gauss valuation on `ℚ[X]`** — "The same assertion holds for the Gauss
valuation of polynomial entries" (p. 12), in the general rank case, with `W = 2w` the doubled
half-integer weights (4.12).  The rank hypothesis appears in its `hvanish` form; the two
corollaries below supply it from vanishing columns and from the literal rank bound. -/
theorem lemma_4_2_gauss_of_vanishing (p : ℕ) [Fact p.Prime] {hh : ℕ} (W : Fin hh → ℤ)
    (hW0 : ∀ i, W i ≤ 0)
    (A L : Matrix (Fin hh) (Fin hh) ℚ[X])
    (hA : ∀ i j, (gaussFil p).vge (A i j) (((W i + W j : ℤ) : ℚ) / 2))
    (pinv : ℚ[X]) (hpinv : (gaussFil p).vge pinv (-1))
    (hL : ∀ i j, vGAtLeast p (L i j) 0)
    (r : ℕ)
    (hvanish : ∀ t : Finset (Fin hh), r < (Finset.univ \ t).card →
      (mixCol A (pinv • L) t).det = 0)
    (z : ℕ) (hz : z = (Finset.univ.filter (fun i => W i = 0)).card) :
    vGAtLeast p (A + pinv • L).det ((∑ i, W i) - (min r z : ℕ)) := by
  classical
  have hmain := lemma_4_2_of_vanishing (gaussFil p) (fun i => ((W i : ℚ)) / 2)
    (fun i => by
      have : ((W i : ℚ)) ≤ 0 := by exact_mod_cast hW0 i
      linarith)
    (fun i => ⟨W i, rfl⟩) A L
    (fun i j => by
      refine (gaussFil p).vge_mono (le_of_eq ?_) (hA i j)
      push_cast; ring)
    pinv hpinv (fun i j => (gaussGe_intCast p (L i j) 0).2 (hL i j))
    r hvanish z (by
      rw [hz]
      refine congrArg Finset.card (Finset.filter_congr fun i _ => ?_)
      constructor
      · intro hWi
        rw [hWi]; norm_num
      · intro hWi
        have h2 : ((W i : ℚ)) = 0 := by linarith
        exact_mod_cast h2)
  have hval : 2 * ∑ i, ((W i : ℚ) / 2) - ((min r z : ℕ) : ℚ)
      = (((∑ i, W i) - (min r z : ℕ) : ℤ) : ℚ) := by
    push_cast
    rw [Finset.mul_sum]
    have : ∑ i, 2 * ((W i : ℚ) / 2) = ∑ i, ((W i : ℚ)) :=
      Finset.sum_congr rfl fun i _ => by ring
    rw [this]
  rw [hval] at hmain
  exact (gaussGe_intCast p _ _).1 hmain

/-- **Lemma 4.2 for the Gauss valuation, with the vanishing-columns form of the rank bound** —
the exact instance Proposition 4.3 uses. -/
theorem lemma_4_2_gauss_zeroCols (p : ℕ) [Fact p.Prime] {hh : ℕ} (W : Fin hh → ℤ)
    (hW0 : ∀ i, W i ≤ 0)
    (A L : Matrix (Fin hh) (Fin hh) ℚ[X])
    (hA : ∀ i j, (gaussFil p).vge (A i j) (((W i + W j : ℤ) : ℚ) / 2))
    (pinv : ℚ[X]) (hpinv : (gaussFil p).vge pinv (-1))
    (hL : ∀ i j, vGAtLeast p (L i j) 0)
    (r : ℕ) (C : Finset (Fin hh)) (hC : ∀ i j, j ∈ C → L i j = 0) (hCr : Cᶜ.card ≤ r)
    (z : ℕ) (hz : z = (Finset.univ.filter (fun i => W i = 0)).card) :
    vGAtLeast p (A + pinv • L).det ((∑ i, W i) - (min r z : ℕ)) :=
  lemma_4_2_gauss_of_vanishing p W hW0 A L hA pinv hpinv hL r
    (vanishing_of_zeroCols A L pinv r C hC hCr) z hz

/-- **Lemma 4.2 for the Gauss valuation, with (4.10) read literally**: `rank L ≤ r` computed
in the fraction field `RatFunc ℚ` of `ℚ[X]` — the "view the matrices over `ℚ(X)`" reading of
`rank_{ℚ_p} L ≤ r_p`.  `ℚ[X]` is not a field, so `Matrix.rank` cannot be applied to `L`
itself; mapping into `RatFunc ℚ` is what makes the paper's own phrase a Lean statement.

Proposition 4.3 uses `lemma_4_2_gauss_zeroCols` instead, because the paper proves the
*stronger* fact that the first `h − r_p` columns vanish; this corollary is the record that the
weaker, literal hypothesis also suffices. -/
theorem lemma_4_2_gauss_rank (p : ℕ) [Fact p.Prime] {hh : ℕ} (W : Fin hh → ℤ)
    (hW0 : ∀ i, W i ≤ 0)
    (A L : Matrix (Fin hh) (Fin hh) ℚ[X])
    (hA : ∀ i j, (gaussFil p).vge (A i j) (((W i + W j : ℤ) : ℚ) / 2))
    (pinv : ℚ[X]) (hpinv : (gaussFil p).vge pinv (-1))
    (hL : ∀ i j, vGAtLeast p (L i j) 0)
    (r : ℕ) (hrank : (L.map (algebraMap ℚ[X] (RatFunc ℚ))).rank ≤ r)
    (z : ℕ) (hz : z = (Finset.univ.filter (fun i => W i = 0)).card) :
    vGAtLeast p (A + pinv • L).det ((∑ i, W i) - (min r z : ℕ)) :=
  lemma_4_2_gauss_of_vanishing p W hW0 A L hA pinv hpinv hL r
    (vanishing_of_rank (algebraMap ℚ[X] (RatFunc ℚ)) (RatFunc.algebraMap_injective ℚ)
      A L pinv r hrank) z hz

/-! # §B.  The rank bound (4.10) from the degree count

"The polynomial quotient of `W t^{i+j}/D_tail` has degree at most `i + j + 6N − K`.  Hence
`L_ij = 0` if `i + j < K − 6N + 2p − 3`.  Its first `h − r_p` rows and columns vanish."

`μ(t^e)` is a `p`-adic integer for `e < 2p − 3`, so the correction `L` sees only monomials of
degree `≥ 2p − 3` in the polynomial part; with `deg ≤ i + j + 6N − K` this forces
`i + j ≥ K − 6N + 2p − 3`.  Since `i, j ≤ h − 1`, a column `j` with
`j < (K − 6N + 2p − 3) − (h − 1) = h − r_p` is identically zero. -/

/-- The columns `j < d` of `L` vanish, if `L i j = 0` whenever `i + j < c` and `d + hh ≤ c + 1`
(i.e. `d ≤ c − (hh − 1)`): for such a `j` and any `i ≤ hh − 1` one has `i + j < c`. -/
lemma zeroCols_of_lowDegree {F : Type*} [CommRing F] {hh c d : ℕ}
    (L : Matrix (Fin hh) (Fin hh) F)
    (hlow : ∀ i j : Fin hh, (i : ℕ) + (j : ℕ) < c → L i j = 0)
    (hd : d + hh ≤ c + 1) :
    ∀ i j : Fin hh, j ∈ (Finset.univ.filter (fun j : Fin hh => (j : ℕ) < d)) → L i j = 0 := by
  intro i j hj
  have hjd : (j : ℕ) < d := (Finset.mem_filter.1 hj).2
  have hi : (i : ℕ) < hh := i.2
  exact hlow i j (by omega)

/-- The complement of `{j : j < d}` in `Fin hh` has at most `hh - d` elements. -/
lemma card_compl_lt_filter (hh d : ℕ) :
    ((Finset.univ.filter (fun j : Fin hh => (j : ℕ) < d))ᶜ).card ≤ hh - d := by
  classical
  have hmem : ∀ j : Fin hh, j ∈ (Finset.univ.filter (fun j : Fin hh => (j : ℕ) < d))ᶜ →
      d ≤ (j : ℕ) := by
    intro j hj
    simp only [Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hj
    exact hj
  refine le_trans (Finset.card_le_card_of_injOn (fun j : Fin hh => (j : ℕ) - d) ?_ ?_)
    (le_of_eq (Finset.card_range (hh - d)))
  · intro j hj
    have h1 := hmem j hj
    have h2 : (j : ℕ) < hh := j.isLt
    show (j : ℕ) - d ∈ Finset.range (hh - d)
    exact Finset.mem_range.2 (by omega)
  · intro x hx y hy hxy
    have h1 := hmem x hx
    have h2 := hmem y hy
    dsimp only at hxy
    exact Fin.ext (by omega)

/-- **The two counts behind (4.10)**, as exact statements in `K, N, p`.

The paper: "the polynomial quotient of `W t^{i+j}/D_tail` has degree at most `i+j+6N−K`.
Hence `L_ij = 0` if `i + j < K − 6N + 2p − 3`.  Its first `h − r_p` rows and columns vanish."

The first conjunct says that the threshold `c = K − 6N + 2p − 3` of the degree condition cuts
off exactly the first `2p − 5N − 2` columns, i.e. `zeroCols_of_lowDegree` applies with
`d = 2p − 5N − 2` (its hypothesis is `d + h ≤ c + 1`).  The second says that `2p − 5N − 2` is
the paper's `h − r_p`, i.e. at most `r_p` columns survive, so `card_compl_lt_filter` gives
`#Cᶜ ≤ r_p`.  Both are identities in `K = 40n`, `N = 3n`, `h = 37n`. -/
lemma outer_column_cut (n p : ℕ) :
    (2 * (p : ℤ) - 5 * (N n : ℤ) - 2) + ((h n : ℤ) - 1)
        = (K n : ℤ) - 6 * (N n : ℤ) + 2 * (p : ℤ) - 3
      ∧ (h n : ℤ) ≤ (2 * (p : ℤ) - 5 * (N n : ℤ) - 2) + rOut n p := by
  have hr : (K n : ℤ) + 4 * (N n : ℤ) - 2 * (p : ℤ) + 2 ≤ rOut n p := le_max_right _ _
  refine ⟨?_, ?_⟩
  · simp only [h, K, N]; push_cast; ring
  · simp only [h, K, N] at hr ⊢; push_cast at hr ⊢; linarith

/-! # §C.  (4.9), and the residue-class counts

"Summing (4.12) and applying Lemma 4.2 gives the integer `γ_p^out` … The conditions `a ≤ v`
and `a ≥ p − v` among `a ≤ N` give `t_p`, with overlap `u`.  The zero-class costs are `1` and
`4`.  These counts prove (4.14)." (p. 13.)

Everything in this section is the bookkeeping behind that sentence, proved in closed form in
`n` and `p`.  The referee audit (see README, "Provenance") checked it numerically over 1975 pairs
`(K = 40n, p)` with `n ≤ 30`; here it is a theorem. -/

/-- **(4.9)** (p. 11) *without its lower bound* `p ≤ K`.  Verbatim, (4.9) reads
`p ≥ 7`, `p ≤ K < 3p`, `p² > 2K`, `2N < p`, `5N ≤ 2p − 2`; `OuterHyp` is everything but
`p ≤ K`, because the *second* assertion of Proposition 4.3 (`p > K`) satisfies all of it too
(`outerHyp_of_gt`, below), and the whole bookkeeping of §E is uniform in `m_K ∈ {0,1,2}`.
(4.9) itself is `OuterHyp n p` together with `p ≤ K n`. -/
structure OuterHyp (n p : ℕ) : Prop where
  /-- `p` is prime. -/
  prime : p.Prime
  /-- `p ≥ 7`. -/
  ge7 : 7 ≤ p
  /-- `K < 3p`. -/
  upper : K n < 3 * p
  /-- `p² > 2K`. -/
  sq : 2 * K n < p ^ 2
  /-- `2N < p`. -/
  twoN : 2 * N n < p
  /-- `5N ≤ 2p − 2`. -/
  fiveN : 5 * N n ≤ 2 * p - 2

namespace OuterHyp

variable {n p : ℕ}

lemma pos (hp : OuterHyp n p) : 0 < p := by have := hp.ge7; omega

lemma odd (hp : OuterHyp n p) : Odd p := hp.prime.odd_of_ne_two (by have := hp.ge7; omega)

/-- `p = 2m + 1` with `m = (p−1)/2`. -/
lemma two_mHalf (hp : OuterHyp n p) : 2 * mHalf p + 1 = p := by
  obtain ⟨k, hk⟩ := hp.odd
  have : mHalf p = k := by unfold mHalf; omega
  omega

/-- `N ≤ m`, from `2N < p = 2m+1`. -/
lemma N_le_mHalf (hp : OuterHyp n p) : N n ≤ mHalf p := by
  have := hp.two_mHalf; have := hp.twoN; omega

lemma vOut_lt (hp : OuterHyp n p) : vOut n p < p := Nat.mod_lt _ hp.pos

/-- `K = p m_K + v`. -/
lemma K_eq (_hp : OuterHyp n p) : p * mFloor p (K n) + vOut n p = K n :=
  Nat.div_add_mod (K n) p

/-- `m_K = 1` when `p ≤ K < 2p`. -/
lemma mFloor_eq_one (_hp : OuterHyp n p) (h1 : p ≤ K n) (h2 : K n < 2 * p) :
    mFloor p (K n) = 1 := by
  have hlo : 1 * p ≤ K n := by omega
  have hhi : K n < (1 + 1) * p := by omega
  exact Nat.div_eq_of_lt_le hlo hhi

/-- `m_K = 2` when `K ≥ 2p`; under (4.9) (`K < 3p`) there is no other case. -/
lemma mFloor_eq_two (hp : OuterHyp n p) (h2 : 2 * p ≤ K n) : mFloor p (K n) = 2 := by
  have hlo : 2 * p ≤ K n := h2
  have hhi : K n < (2 + 1) * p := by have := hp.upper; omega
  exact Nat.div_eq_of_lt_le hlo hhi

end OuterHyp

/-! ### The two indicators of `ell_closed` -/

/-- `ℓ_K(a) − 2m_K = 1_{a ≤ v} + 1_{a ≥ p−v}` (p. 10, `Zeta5.ell_closed`). -/
def eIdx (n p a : ℕ) : ℕ :=
  (if a ≤ vOut n p then 1 else 0) + (if p ≤ vOut n p + a then 1 else 0)

lemma eIdx_le_two (n p a : ℕ) : eIdx n p a ≤ 2 := by
  unfold eIdx; split <;> split <;> omega

lemma eIdx_eq_two_iff (n p a : ℕ) :
    eIdx n p a = 2 ↔ (a ≤ vOut n p ∧ p ≤ vOut n p + a) := by
  unfold eIdx; constructor
  · intro hh; by_cases h1 : a ≤ vOut n p <;> by_cases h2 : p ≤ vOut n p + a <;>
      simp [h1, h2] at hh ⊢
  · rintro ⟨h1, h2⟩; simp [h1, h2]

/-- `ℓ_K(a) = 2 m_K + e(a)` (p. 10). -/
lemma ell_eq_add_eIdx {n p a : ℕ} (ha1 : 1 ≤ a) (ha2 : 2 * a < p) :
    ell p (K n) a = 2 * mFloor p (K n) + eIdx n p a := by
  rw [ell_closed p (K n) a ha1 ha2]
  unfold eIdx vOut
  ring

private lemma card_le_v (A v : ℕ) : ((Icc 1 A).filter (fun a => a ≤ v)).card = min A v := by
  classical
  have hset : (Icc 1 A).filter (fun a => a ≤ v) = Icc 1 (min A v) := by
    ext a; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
  rw [hset, Nat.card_Icc]; omega

private lemma card_ge_v (A v p : ℕ) (hv : v < p) :
    ((Icc 1 A).filter (fun a => p ≤ v + a)).card = A + 1 - (p - v) := by
  classical
  have hset : (Icc 1 A).filter (fun a => p ≤ v + a) = Icc (p - v) A := by
    ext a; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
  rw [hset, Nat.card_Icc]

private lemma card_both_v (A v p : ℕ) (hv : v < p) :
    ((Icc 1 A).filter (fun a => a ≤ v ∧ p ≤ v + a)).card = min A v + 1 - (p - v) := by
  classical
  have hset : (Icc 1 A).filter (fun a => a ≤ v ∧ p ≤ v + a) = Icc (p - v) (min A v) := by
    ext a; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
  rw [hset, Nat.card_Icc]

/-- `∑_{a=1}^A e(a) = min(A,v) + (A + 1 − (p−v))`. -/
lemma sum_eIdx (n p A : ℕ) (hv : vOut n p < p) :
    ∑ a ∈ Icc 1 A, (eIdx n p a : ℤ)
      = (min A (vOut n p) : ℤ) + ((A + 1 - (p - vOut n p) : ℕ) : ℤ) := by
  classical
  have hterm : ∀ a ∈ Icc 1 A, ((eIdx n p a : ℕ) : ℤ)
      = (if a ≤ vOut n p then (1 : ℤ) else 0) + (if p ≤ vOut n p + a then (1 : ℤ) else 0) := by
    intro a _; unfold eIdx; split <;> split <;> norm_num
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib,
    ← Finset.sum_filter, ← Finset.sum_filter, Finset.sum_const, Finset.sum_const,
    card_le_v A (vOut n p), card_ge_v A (vOut n p) p hv]
  simp

/-- `∑_{a=1}^A 1_{e(a) = 2} = min(A,v) + 1 − (p−v)`: the overlap of the two conditions. -/
lemma sum_eIdx_two (n p A : ℕ) (hv : vOut n p < p) :
    ∑ a ∈ Icc 1 A, (if eIdx n p a = 2 then (1 : ℤ) else 0)
      = ((min A (vOut n p) + 1 - (p - vOut n p) : ℕ) : ℤ) := by
  classical
  have hterm : ∀ a ∈ Icc 1 A, (if eIdx n p a = 2 then (1 : ℤ) else 0)
      = (if (a ≤ vOut n p ∧ p ≤ vOut n p + a) then (1 : ℤ) else 0) := by
    intro a _
    by_cases hc : a ≤ vOut n p ∧ p ≤ vOut n p + a
    · rw [ite_eq_left ((eIdx_eq_two_iff n p a).2 hc), ite_eq_left hc]
    · rw [ite_eq_right (fun hcon => hc ((eIdx_eq_two_iff n p a).1 hcon)), ite_eq_right hc]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter, Finset.sum_const,
    card_both_v A (vOut n p) p hv]
  simp

/-- `∑_{a=1}^{m} e(a) = v`. -/
lemma sum_eIdx_mHalf {n p : ℕ} (hp : OuterHyp n p) :
    ∑ a ∈ Icc 1 (mHalf p), (eIdx n p a : ℤ) = (vOut n p : ℤ) := by
  rw [sum_eIdx n p (mHalf p) hp.vOut_lt]
  have h1 := hp.two_mHalf
  have h2 := hp.vOut_lt
  omega

/-- `∑_{a=1}^{N} e(a) = t_p = min(N,v) + u`. -/
lemma sum_eIdx_N {n p : ℕ} (hp : OuterHyp n p) :
    ∑ a ∈ Icc 1 (N n), (eIdx n p a : ℤ) = tOut n p := by
  rw [sum_eIdx n p (N n) hp.vOut_lt, tOut, uOut]
  have h2 := hp.vOut_lt
  omega

/-- `∑_{a=1}^{N} 1_{e(a)=2} = u`: "the overlap `u`" of p. 13.  Uses `2N < p`. -/
lemma sum_eIdx_two_N {n p : ℕ} (hp : OuterHyp n p) :
    ∑ a ∈ Icc 1 (N n), (if eIdx n p a = 2 then (1 : ℤ) else 0) = uOut n p := by
  rw [sum_eIdx_two n p (N n) hp.vOut_lt, uOut]
  have h2 := hp.vOut_lt
  have h3 := hp.twoN
  omega

/-- The removed classes are exactly `a ≤ N`, and `N ≤ m`: summing an `a`-indexed quantity
against `δ_a` is summing it over `a ≤ N`. -/
lemma sum_delta_mul {n p : ℕ} (hp : OuterHyp n p) (f : ℕ → ℤ) :
    ∑ a ∈ Icc 1 (mHalf p), (if a ≤ N n then (1 : ℤ) else 0) * f a
      = ∑ a ∈ Icc 1 (N n), f a := by
  classical
  have hset : (Icc 1 (mHalf p)).filter (fun a => a ≤ N n) = Icc 1 (N n) := by
    have := hp.N_le_mHalf
    ext a; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
  calc ∑ a ∈ Icc 1 (mHalf p), (if a ≤ N n then (1 : ℤ) else 0) * f a
      = ∑ a ∈ Icc 1 (mHalf p), (if a ≤ N n then f a else 0) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        split <;> ring
    _ = ∑ a ∈ (Icc 1 (mHalf p)).filter (fun a => a ≤ N n), f a := (Finset.sum_filter _ _).symm
    _ = ∑ a ∈ Icc 1 (N n), f a := by rw [hset]

lemma sum_delta {n p : ℕ} (hp : OuterHyp n p) :
    ∑ a ∈ Icc 1 (mHalf p), (if a ≤ N n then (1 : ℤ) else 0) = (N n : ℤ) := by
  have := sum_delta_mul hp (fun _ => (1 : ℤ))
  simp only [mul_one] at this
  rw [this, Finset.sum_const, Nat.card_Icc]
  simp

/-! # §D.  The weights (4.12) and the table on p. 13

Weights are half-integers, so `W = 2w` is carried as an integer throughout (the same
convention as §4.1 in `Section41.lean`).  (4.12) reads

    `w_{a,i} = min(0, i + 3δ − (ℓ+4)/2)` for `i < ℓ − 2`,   `w_{a,i} = 0` for `i ≥ ℓ − 2`,

so `W_{a,i} = 2 w_{a,i} = min(0, 2i + 6δ − ℓ − 4)` for `i < ℓ − 2` and `0` otherwise.  The
class has `ℓ − δ` rows, `i = 0, …, ℓ − δ − 1`, one for each *remaining* pole (4.11). -/

/-- **(4.12)**, doubled: `W_{a,i} = 2 w_{a,i}`, for a class with `ℓ = ℓ_K(a)` poles of which
`δ ∈ {0,1}` were removed. -/
def outerW (ℓ δ i : ℕ) : ℤ :=
  if i + 2 < ℓ then min 0 (2 * (i : ℤ) + 6 * (δ : ℤ) - (ℓ : ℤ) - 4) else 0

/-- The number of rows of a class, `ℓ − δ`: one for each remaining pole (4.11). -/
def outerRowCt (ℓ δ : ℕ) : ℕ := ℓ - δ

/-- `∑_i W_{a,i}` over one class — i.e. `−(−2 ∑_i w_{a,i})`, the "cost" of the p. 13 table
with the opposite sign. -/
def outerCost (ℓ δ : ℕ) : ℤ := ∑ i ∈ Finset.range (outerRowCt ℓ δ), outerW ℓ δ i

/-- `#{i | w_{a,i} = 0}` over one class, the last line of the p. 13 table. -/
def outerZeroCt (ℓ δ : ℕ) : ℕ :=
  ((Finset.range (outerRowCt ℓ δ)).filter (fun i => outerW ℓ δ i = 0)).card

/-- **The p. 13 table, removed classes** (`δ = 1`):

    `ℓ`                 | 2  3  4  5  6
    `−2 ∑_i w_{a,i}`    | 0  1  2  4  6
    `#{i | w_{a,i}=0}`  | 1  1  2  2  3

Computed from (4.12) alone.  (`outerCost = −(−2∑w)`.) -/
theorem table_removed :
    (outerCost 2 1 = 0 ∧ outerZeroCt 2 1 = 1)
      ∧ (outerCost 3 1 = -1 ∧ outerZeroCt 3 1 = 1)
      ∧ (outerCost 4 1 = -2 ∧ outerZeroCt 4 1 = 2)
      ∧ (outerCost 5 1 = -4 ∧ outerZeroCt 5 1 = 2)
      ∧ (outerCost 6 1 = -6 ∧ outerZeroCt 6 1 = 3) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩ <;> decide

/-- **The p. 13 table, unremoved classes** (`δ = 0`): "An unremoved class has cost `7(ℓ−2)`
and two zero weights." -/
theorem table_unremoved (ℓ : ℕ) (h2 : 2 ≤ ℓ) (h6 : ℓ ≤ 6) :
    outerCost ℓ 0 = -7 * ((ℓ : ℤ) - 2) ∧ outerZeroCt ℓ 0 = 2 := by
  interval_cases ℓ <;> exact ⟨by decide, by decide⟩

/-- The cost of one class in the branch `K < 2p` (`m_K = 1`, so `ℓ = 2 + e`, `e ∈ {0,1,2}`):
`∑_i W_{a,i} = −(7 − 6δ)e`.  For `δ = 0` this is `−7(ℓ−2)`, for `δ = 1` it is `−e`, i.e. the
saving of a removed class is `6(ℓ−2)`. -/
theorem outerCost_small (e δ : ℕ) (he : e ≤ 2) (hδ : δ ≤ 1) :
    outerCost (2 + e) δ = -(7 - 6 * (δ : ℤ)) * (e : ℤ) := by
  interval_cases e <;> interval_cases δ <;> decide

/-- The cost of one class in the branch `K ≥ 2p` (`m_K = 2`, so `ℓ = 4 + e`):
`∑_i W_{a,i} = −(7e + 14) + δ(5e + 12)`, i.e. the saving of a removed class is
`12 + 5(ℓ − 4)`. -/
theorem outerCost_large (e δ : ℕ) (he : e ≤ 2) (hδ : δ ≤ 1) :
    outerCost (4 + e) δ = -(7 * (e : ℤ) + 14) + (δ : ℤ) * (5 * (e : ℤ) + 12) := by
  interval_cases e <;> interval_cases δ <;> decide

/-- The number of zero weights in one class, branch `K < 2p`. -/
theorem outerZeroCt_small (e δ : ℕ) (he : e ≤ 2) (hδ : δ ≤ 1) :
    outerZeroCt (2 + e) δ = 2 - δ + δ * (if e = 2 then 1 else 0) := by
  interval_cases e <;> interval_cases δ <;> decide

/-- The number of zero weights in one class, branch `K ≥ 2p`. -/
theorem outerZeroCt_large (e δ : ℕ) (he : e ≤ 2) (hδ : δ ≤ 1) :
    outerZeroCt (4 + e) δ = 2 + δ * (if e = 2 then 1 else 0) := by
  interval_cases e <;> interval_cases δ <;> decide

/-- All the weights (4.12) are nonpositive — the hypothesis of Lemma 4.2. -/
theorem outerW_nonpos (ℓ δ i : ℕ) : outerW ℓ δ i ≤ 0 := by
  unfold outerW
  split
  · exact min_le_left _ _
  · exact le_rfl

/-- "A single zero-class pole has weight `−1/2`.  For two zero-class poles `p, 2p`, the rows
`1, t+p²` give entry bounds `−3,−1,0`, so the weights `−2,0` are valid." (p. 12.)  Doubled:
`W = −1` for one pole, `W = (−4, 0)` for two. -/
def outerWZero (mK i : ℕ) : ℤ := if mK ≤ 1 then -1 else (if i = 0 then -4 else 0)

theorem outerWZero_nonpos (mK i : ℕ) : outerWZero mK i ≤ 0 := by
  unfold outerWZero; split <;> [norm_num; (split <;> norm_num)]

/-- The zero class contributes `−1` (one pole) resp. `−4` (two poles): "The zero-class costs
are `1` and `4`." -/
theorem sum_outerWZero_one : ∑ i ∈ Finset.range 1, outerWZero 1 i = -1 := by decide

theorem sum_outerWZero_two : ∑ i ∈ Finset.range 2, outerWZero 2 i = -4 := by decide

/-- The zero class has no zero weight when there is one pole, and one when there are two. -/
theorem zeroCt_outerWZero_one :
    ((Finset.range 1).filter (fun i => outerWZero 1 i = 0)).card = 0 := by decide

theorem zeroCt_outerWZero_two :
    ((Finset.range 2).filter (fun i => outerWZero 2 i = 0)).card = 1 := by decide

/-- The `m_K = 0` line (`p > K`): a class has at most two poles, `i + 2 < ℓ` never happens,
and every weight is `0` — "the whole matrix is integral", p. 13. -/
theorem outerCost_none (e δ : ℕ) (he : e ≤ 2) (hδ : δ ≤ 1) : outerCost e δ = 0 := by
  interval_cases e <;> interval_cases δ <;> decide

theorem outerZeroCt_none (e δ : ℕ) (he : e ≤ 2) (hδ : δ ≤ 1) (hed : δ ≤ e) :
    (outerZeroCt e δ : ℤ) = (e : ℤ) - (δ : ℤ) := by
  revert hed; interval_cases e <;> interval_cases δ <;> decide

/-- `∑_i W_{a,i} = −7e + 6δe` in the branch `K < 2p` (`ℓ = 2 + e`). -/
theorem outerCost_small' (e δ : ℕ) (he : e ≤ 2) (hδ : δ ≤ 1) :
    outerCost (2 + e) δ = -7 * (e : ℤ) + 6 * ((δ : ℤ) * (e : ℤ)) := by
  rw [outerCost_small e δ he hδ]; ring

/-- `∑_i W_{a,i} = −7e − 14 + 5δe + 12δ` in the branch `K ≥ 2p` (`ℓ = 4 + e`). -/
theorem outerCost_large' (e δ : ℕ) (he : e ≤ 2) (hδ : δ ≤ 1) :
    outerCost (4 + e) δ = -7 * (e : ℤ) + -14 + 5 * ((δ : ℤ) * (e : ℤ)) + 12 * (δ : ℤ) := by
  rw [outerCost_large e δ he hδ]; ring

theorem outerZeroCt_small' (e δ : ℕ) (he : e ≤ 2) (hδ : δ ≤ 1) :
    (outerZeroCt (2 + e) δ : ℤ)
      = 2 - (δ : ℤ) + (δ : ℤ) * (if e = 2 then (1 : ℤ) else 0) := by
  interval_cases e <;> interval_cases δ <;> decide

theorem outerZeroCt_large' (e δ : ℕ) (he : e ≤ 2) (hδ : δ ≤ 1) :
    (outerZeroCt (4 + e) δ : ℤ) = 2 + (δ : ℤ) * (if e = 2 then (1 : ℤ) else 0) := by
  interval_cases e <;> interval_cases δ <;> decide

private lemma cast_delta (a A : ℕ) :
    (((if a ≤ A then 1 else 0 : ℕ)) : ℤ) = if a ≤ A then (1 : ℤ) else 0 := by
  split <;> norm_num

private lemma delta_le_one (a A : ℕ) : (if a ≤ A then 1 else 0 : ℕ) ≤ 1 := by split <;> omega

/-! # §E.  The class sums, and (4.14) -/

section Assembly

variable {n p : ℕ}

/-- Every `a ∈ [1,m]` has `1 ≤ a` and `2a < p`, so `ell_closed` applies. -/
private lemma ell_split (hp : OuterHyp n p) :
    ∀ a ∈ Icc 1 (mHalf p), ell p (K n) a = 2 * mFloor p (K n) + eIdx n p a := by
  intro a ha
  rw [Finset.mem_Icc] at ha
  exact ell_eq_add_eIdx ha.1 (two_mul_lt_of_le_mHalf hp.odd ha.2)

/-- **The class-cost sum in the branch `K < 2p`** (`m_K = 1`):
`∑_a ∑_i W_{a,i} = −7v + 6t_p`. -/
theorem sum_class_cost_one (hp : OuterHyp n p) (h1 : mFloor p (K n) = 1) :
    ∑ a ∈ Icc 1 (mHalf p), outerCost (ell p (K n) a) (if a ≤ N n then 1 else 0)
      = -7 * (vOut n p : ℤ) + 6 * tOut n p := by
  have hterm : ∀ a ∈ Icc 1 (mHalf p),
      outerCost (ell p (K n) a) (if a ≤ N n then 1 else 0)
        = -7 * (eIdx n p a : ℤ)
          + 6 * ((if a ≤ N n then (1 : ℤ) else 0) * (eIdx n p a : ℤ)) := by
    intro a ha
    have hl : ell p (K n) a = 2 + eIdx n p a := by rw [ell_split hp a ha, h1]
    rw [hl, outerCost_small' _ _ (eIdx_le_two n p a) (delta_le_one a (N n)), cast_delta]
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    sum_eIdx_mHalf hp, sum_delta_mul hp (fun a => (eIdx n p a : ℤ)), sum_eIdx_N hp]

/-- **The class-cost sum in the branch `K ≥ 2p`** (`m_K = 2`):
`∑_a ∑_i W_{a,i} = −7v − 14m + 5t_p + 12N`. -/
theorem sum_class_cost_two (hp : OuterHyp n p) (h2 : mFloor p (K n) = 2) :
    ∑ a ∈ Icc 1 (mHalf p), outerCost (ell p (K n) a) (if a ≤ N n then 1 else 0)
      = -7 * (vOut n p : ℤ) + -14 * (mHalf p : ℤ) + 5 * tOut n p + 12 * (N n : ℤ) := by
  have hterm : ∀ a ∈ Icc 1 (mHalf p),
      outerCost (ell p (K n) a) (if a ≤ N n then 1 else 0)
        = -7 * (eIdx n p a : ℤ) + -14
          + 5 * ((if a ≤ N n then (1 : ℤ) else 0) * (eIdx n p a : ℤ))
          + 12 * (if a ≤ N n then (1 : ℤ) else 0) := by
    intro a ha
    have hl : ell p (K n) a = 4 + eIdx n p a := by rw [ell_split hp a ha, h2]
    rw [hl, outerCost_large' _ _ (eIdx_le_two n p a) (delta_le_one a (N n)), cast_delta]
  rw [Finset.sum_congr rfl hterm]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_const, Nat.card_Icc,
    sum_eIdx_mHalf hp, sum_delta_mul hp (fun a => (eIdx n p a : ℤ)), sum_eIdx_N hp,
    sum_delta hp]
  simp only [Nat.add_sub_cancel, nsmul_eq_mul]
  ring

/-- **The class-cost sum in the branch `p > K`** (`m_K = 0`): every weight is `0`. -/
theorem sum_class_cost_none (hp : OuterHyp n p) (h0 : mFloor p (K n) = 0) :
    ∑ a ∈ Icc 1 (mHalf p), outerCost (ell p (K n) a) (if a ≤ N n then 1 else 0) = 0 := by
  refine Finset.sum_eq_zero fun a ha => ?_
  have hl : ell p (K n) a = eIdx n p a := by rw [ell_split hp a ha, h0]; ring
  rw [hl]
  exact outerCost_none _ _ (eIdx_le_two n p a) (delta_le_one a (N n))

/-- **The zero-weight count in the branch `K < 2p`**: `∑_a #{i | w_{a,i}=0} = 2m − N + u`. -/
theorem sum_class_zeros_one (hp : OuterHyp n p) (h1 : mFloor p (K n) = 1) :
    ∑ a ∈ Icc 1 (mHalf p), ((outerZeroCt (ell p (K n) a) (if a ≤ N n then 1 else 0) : ℕ) : ℤ)
      = 2 * (mHalf p : ℤ) - (N n : ℤ) + uOut n p := by
  have hterm : ∀ a ∈ Icc 1 (mHalf p),
      ((outerZeroCt (ell p (K n) a) (if a ≤ N n then 1 else 0) : ℕ) : ℤ)
        = 2 - (if a ≤ N n then (1 : ℤ) else 0)
          + (if a ≤ N n then (1 : ℤ) else 0) * (if eIdx n p a = 2 then (1 : ℤ) else 0) := by
    intro a ha
    have hl : ell p (K n) a = 2 + eIdx n p a := by rw [ell_split hp a ha, h1]
    rw [hl, outerZeroCt_small' _ _ (eIdx_le_two n p a) (delta_le_one a (N n)), cast_delta]
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_const, Nat.card_Icc,
    sum_delta hp, sum_delta_mul hp (fun a => if eIdx n p a = 2 then (1 : ℤ) else 0),
    sum_eIdx_two_N hp]
  simp only [Nat.add_sub_cancel, nsmul_eq_mul]
  ring

/-- **The zero-weight count in the branch `K ≥ 2p`**: `∑_a #{i | w_{a,i}=0} = 2m + u`. -/
theorem sum_class_zeros_two (hp : OuterHyp n p) (h2 : mFloor p (K n) = 2) :
    ∑ a ∈ Icc 1 (mHalf p), ((outerZeroCt (ell p (K n) a) (if a ≤ N n then 1 else 0) : ℕ) : ℤ)
      = 2 * (mHalf p : ℤ) + uOut n p := by
  have hterm : ∀ a ∈ Icc 1 (mHalf p),
      ((outerZeroCt (ell p (K n) a) (if a ≤ N n then 1 else 0) : ℕ) : ℤ)
        = 2 + (if a ≤ N n then (1 : ℤ) else 0) * (if eIdx n p a = 2 then (1 : ℤ) else 0) := by
    intro a ha
    have hl : ell p (K n) a = 4 + eIdx n p a := by rw [ell_split hp a ha, h2]
    rw [hl, outerZeroCt_large' _ _ (eIdx_le_two n p a) (delta_le_one a (N n)), cast_delta]
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc,
    sum_delta_mul hp (fun a => if eIdx n p a = 2 then (1 : ℤ) else 0), sum_eIdx_two_N hp]
  simp only [Nat.add_sub_cancel, nsmul_eq_mul]
  ring

/-- A class with a removed pole has at least one pole: `a ≤ N ≤ K`, so `a` itself is counted
by `ℓ_K(a)`. -/
lemma one_le_ell (p A a : ℕ) (ha1 : 1 ≤ a) (haA : a ≤ A) : 1 ≤ ell p A a := by
  classical
  exact Finset.card_pos.2
    ⟨a, Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨ha1, haA⟩, Or.inl rfl⟩⟩

lemma N_le_K (n : ℕ) : N n ≤ K n := by simp only [N, K]; omega

/-- In the branch `p > K` (`m_K = 0`) a removed class has `e(a) ≥ 1`, because `v = K`. -/
lemma one_le_eIdx_of_le_N (hp : OuterHyp n p) (h0 : mFloor p (K n) = 0) {a : ℕ}
    (ha : a ≤ N n) : 1 ≤ eIdx n p a := by
  have hKp : K n < p := by
    have h1 := hp.K_eq
    have h2 := hp.vOut_lt
    rw [h0] at h1
    omega
  have hv : vOut n p = K n := by
    unfold vOut
    exact Nat.mod_eq_of_lt hKp
  unfold eIdx
  rw [hv, ite_eq_left (le_trans ha (N_le_K n))]
  split <;> omega

/-- **The zero-weight count in the branch `p > K`**: every row is a zero weight, so the count
is `∑_a (ℓ_K(a) − δ_a) = v − N = K − N = h`. -/
theorem sum_class_zeros_none (hp : OuterHyp n p) (h0 : mFloor p (K n) = 0) :
    ∑ a ∈ Icc 1 (mHalf p), ((outerZeroCt (ell p (K n) a) (if a ≤ N n then 1 else 0) : ℕ) : ℤ)
      = (vOut n p : ℤ) - (N n : ℤ) := by
  have hterm : ∀ a ∈ Icc 1 (mHalf p),
      ((outerZeroCt (ell p (K n) a) (if a ≤ N n then 1 else 0) : ℕ) : ℤ)
        = (eIdx n p a : ℤ) - (if a ≤ N n then (1 : ℤ) else 0) := by
    intro a ha
    have hl : ell p (K n) a = eIdx n p a := by rw [ell_split hp a ha, h0]; ring
    have hed : (if a ≤ N n then 1 else 0 : ℕ) ≤ eIdx n p a := by
      by_cases hc : a ≤ N n
      · rw [ite_eq_left hc]; exact one_le_eIdx_of_le_N hp h0 hc
      · rw [ite_eq_right hc]; omega
    rw [hl, outerZeroCt_none _ _ (eIdx_le_two n p a) (delta_le_one a (N n)) hed, cast_delta]
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, sum_eIdx_mHalf hp, sum_delta hp]

/-! ### The rows of the basis (4.11), and the totals -/

/-- The number of rows of the class `a` in the basis (4.11): `ℓ_K(a) − δ_a` remaining poles
for an ordinary class `a ≥ 1`, and one row per zero-class pole (`m_K` of them) for `a = 0`. -/
def outerDim (n p a : ℕ) : ℕ :=
  if a = 0 then mFloor p (K n)
  else outerRowCt (ell p (K n) a) (if a ≤ N n then 1 else 0)

/-- The rows of the local basis (4.11), indexed by (class, index inside the class). -/
abbrev OuterRows (n p : ℕ) : Type := Σ a : Fin (mHalf p + 1), Fin (outerDim n p (a : ℕ))

/-- The doubled weight `W = 2w` of a row of (4.11): (4.12) for an ordinary class, and the
zero-class weights `−1` resp. `−2, 0` (doubled) for `a = 0`. -/
def outerWeight (n p : ℕ) (ρ : OuterRows n p) : ℤ :=
  if (ρ.1 : ℕ) = 0 then outerWZero (mFloor p (K n)) (ρ.2 : ℕ)
  else outerW (ell p (K n) (ρ.1 : ℕ)) (if (ρ.1 : ℕ) ≤ N n then 1 else 0) (ρ.2 : ℕ)

/-- `z`, the number of zero weights, as it enters (4.13). -/
def outerZeroCount (n p : ℕ) : ℕ :=
  (Finset.univ.filter (fun ρ : OuterRows n p => outerWeight n p ρ = 0)).card

theorem outerWeight_nonpos (n p : ℕ) (ρ : OuterRows n p) : outerWeight n p ρ ≤ 0 := by
  unfold outerWeight
  split
  · exact outerWZero_nonpos _ _
  · exact outerW_nonpos _ _ _

private lemma sum_range_succ_Icc {β : Type*} [AddCommMonoid β] (m : ℕ) (g : ℕ → β) :
    ∑ a ∈ Finset.range (m + 1), g a = g 0 + ∑ a ∈ Icc 1 m, g a := by
  rw [Finset.sum_range_succ' g m, add_comm]
  congr 1
  have hIcc : Icc 1 m = Ico 1 (m + 1) := by ext a; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [hIcc, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel]
  exact Finset.sum_congr rfl fun k _ => by rw [Nat.add_comm]

/-- A sum over the rows of (4.11), split into the zero class and the ordinary classes. -/
lemma sum_over_outerRows {β : Type*} [AddCommMonoid β] (n p : ℕ) (f : ℕ → ℕ → β) :
    ∑ ρ : OuterRows n p, f (ρ.1 : ℕ) (ρ.2 : ℕ)
      = (∑ i ∈ Finset.range (outerDim n p 0), f 0 i)
        + ∑ a ∈ Icc 1 (mHalf p), ∑ i ∈ Finset.range (outerDim n p a), f a i := by
  classical
  have h1 : ∑ ρ : OuterRows n p, f (ρ.1 : ℕ) (ρ.2 : ℕ)
      = ∑ a ∈ Finset.range (mHalf p + 1), ∑ i ∈ Finset.range (outerDim n p a), f a i := by
    rw [← Finset.univ_sigma_univ, Finset.sum_sigma,
      ← Fin.sum_univ_eq_sum_range
        (fun a => ∑ i ∈ Finset.range (outerDim n p a), f a i) (mHalf p + 1)]
    refine Finset.sum_congr rfl fun a _ => ?_
    exact Fin.sum_univ_eq_sum_range (fun i => f (a : ℕ) i) (outerDim n p (a : ℕ))
  rw [h1, sum_range_succ_Icc]

/-- `∑_ρ W_ρ`, split into the zero class and the (4.12) class costs. -/
lemma sum_outerWeight_split (n p : ℕ) :
    ∑ ρ : OuterRows n p, outerWeight n p ρ
      = (∑ i ∈ Finset.range (mFloor p (K n)), outerWZero (mFloor p (K n)) i)
        + ∑ a ∈ Icc 1 (mHalf p),
            outerCost (ell p (K n) a) (if a ≤ N n then 1 else 0) := by
  have hlhs : ∑ ρ : OuterRows n p, outerWeight n p ρ
      = ∑ ρ : OuterRows n p, (fun a i =>
          if a = 0 then outerWZero (mFloor p (K n)) i
          else outerW (ell p (K n) a) (if a ≤ N n then 1 else 0) i)
            (ρ.1 : ℕ) (ρ.2 : ℕ) := rfl
  rw [hlhs, sum_over_outerRows n p (fun a i =>
    if a = 0 then outerWZero (mFloor p (K n)) i
    else outerW (ell p (K n) a) (if a ≤ N n then 1 else 0) i)]
  congr 1
  refine Finset.sum_congr rfl fun a ha => ?_
  have ha0 : a ≠ 0 := by
    rw [Finset.mem_Icc] at ha; omega
  simp only [outerDim, ite_eq_right ha0, outerCost]

private lemma sum_ite_eq_card (k : ℕ) (g : ℕ → ℤ) :
    ∑ i ∈ Finset.range k, (if g i = 0 then (1 : ℤ) else 0)
      = ((((Finset.range k).filter (fun i => g i = 0)).card : ℕ) : ℤ) := by
  rw [Finset.card_filter]
  push_cast
  exact Finset.sum_congr rfl fun i _ => by split <;> norm_num

/-- `z`, split into the zero class and the (4.12) class zero-counts. -/
lemma outerZeroCount_split (n p : ℕ) :
    ((outerZeroCount n p : ℕ) : ℤ)
      = ((((Finset.range (mFloor p (K n))).filter
            (fun i => outerWZero (mFloor p (K n)) i = 0)).card : ℕ) : ℤ)
        + ∑ a ∈ Icc 1 (mHalf p),
            ((outerZeroCt (ell p (K n) a) (if a ≤ N n then 1 else 0) : ℕ) : ℤ) := by
  have hcard : ((outerZeroCount n p : ℕ) : ℤ)
      = ∑ ρ : OuterRows n p, (if outerWeight n p ρ = 0 then (1 : ℤ) else 0) := by
    unfold outerZeroCount
    rw [Finset.card_filter]
    push_cast
    exact Finset.sum_congr rfl fun ρ _ => by split <;> norm_num
  have hlhs : ∑ ρ : OuterRows n p, (if outerWeight n p ρ = 0 then (1 : ℤ) else 0)
      = ∑ ρ : OuterRows n p, (fun a i =>
          if (if a = 0 then outerWZero (mFloor p (K n)) i
              else outerW (ell p (K n) a) (if a ≤ N n then 1 else 0) i) = 0
            then (1 : ℤ) else 0) (ρ.1 : ℕ) (ρ.2 : ℕ) := rfl
  rw [hcard, hlhs, sum_over_outerRows n p (fun a i =>
    if (if a = 0 then outerWZero (mFloor p (K n)) i
        else outerW (ell p (K n) a) (if a ≤ N n then 1 else 0) i) = 0 then (1 : ℤ) else 0)]
  congr 1
  · exact sum_ite_eq_card _ _
  · refine Finset.sum_congr rfl fun a ha => ?_
    have ha0 : a ≠ 0 := by
      rw [Finset.mem_Icc] at ha; omega
    simp only [outerDim, ite_eq_right ha0]
    rw [sum_ite_eq_card]
    rfl

/-! ### The totals, and (4.14) -/

theorem sum_outerWZero_none : ∑ i ∈ Finset.range 0, outerWZero 0 i = 0 := by decide

theorem zeroCt_outerWZero_none :
    ((Finset.range 0).filter (fun i => outerWZero 0 i = 0)).card = 0 := by decide

/-- `r_p = 0` when `p > K`: "the polynomial correction vanishes because `K + 4N + 1 < 2p`"
(p. 13).  With `K = 40n`, `N = 3n` this is immediate from `K < p`. -/
lemma rOut_eq_zero_of_lt (n p : ℕ) (hlt : K n < p) : rOut n p = 0 := by
  have hK : K n = 40 * n := rfl
  have hN : N n = 3 * n := rfl
  have hltZ : ((40 * n : ℕ) : ℤ) < (p : ℤ) := by
    have : (40 * n : ℕ) < p := by rw [← hK]; exact hlt
    exact_mod_cast this
  have h1 : (K n : ℤ) + 4 * (N n : ℤ) - 2 * (p : ℤ) + 2 ≤ 0 := by
    rw [hK, hN]; push_cast at hltZ ⊢; omega
  exact max_eq_left h1

/-- **`∑_ρ W_ρ` in closed form**: the three branches `p > K`, `K < 2p`, `K ≥ 2p` of (4.14),
before the `min(r_p, z)` correction. -/
theorem sum_outerWeight_eq (hp : OuterHyp n p) :
    ∑ ρ : OuterRows n p, outerWeight n p ρ
      = if K n < p then 0
        else if K n < 2 * p then -7 * ((K n : ℤ) - (p : ℤ)) + 6 * tOut n p - 1
        else -7 * ((K n : ℤ) - (p : ℤ)) + 3 + 12 * (N n : ℤ) + 5 * tOut n p := by
  rw [sum_outerWeight_split]
  by_cases hK0 : K n < p
  · have h0 : mFloor p (K n) = 0 := Nat.div_eq_of_lt hK0
    rw [ite_eq_left hK0, sum_class_cost_none hp h0, h0, sum_outerWZero_none]
    norm_num
  · rw [ite_eq_right hK0]
    have hpK : p ≤ K n := by omega
    by_cases hK1 : K n < 2 * p
    · have h1 : mFloor p (K n) = 1 := hp.mFloor_eq_one hpK hK1
      have hv : (vOut n p : ℤ) = (K n : ℤ) - (p : ℤ) := by
        have hKe := hp.K_eq
        rw [h1] at hKe
        omega
      rw [ite_eq_left hK1, sum_class_cost_one hp h1, h1, sum_outerWZero_one, hv]
      ring
    · have h2 : mFloor p (K n) = 2 := hp.mFloor_eq_two (by omega)
      have hv : (vOut n p : ℤ) = (K n : ℤ) - 2 * (p : ℤ) := by
        have hKe := hp.K_eq
        rw [h2] at hKe
        omega
      have hm : 2 * (mHalf p : ℤ) + 1 = (p : ℤ) := by exact_mod_cast hp.two_mHalf
      rw [ite_eq_right hK1, sum_class_cost_two hp h2, h2, sum_outerWZero_two, hv]
      linarith

/-- **`z` in closed form**: `z = p − 1 − N + u` for `K < 2p` and `z = p + u` for `K ≥ 2p`
(p. 13), and `z = h` when `p > K` (every weight is then zero). -/
theorem outerZeroCount_eq (hp : OuterHyp n p) :
    ((outerZeroCount n p : ℕ) : ℤ)
      = if K n < p then (K n : ℤ) - (N n : ℤ)
        else if K n < 2 * p then (p : ℤ) - 1 - (N n : ℤ) + uOut n p
        else (p : ℤ) + uOut n p := by
  rw [outerZeroCount_split]
  by_cases hK0 : K n < p
  · have h0 : mFloor p (K n) = 0 := Nat.div_eq_of_lt hK0
    have hv : (vOut n p : ℤ) = (K n : ℤ) := by
      have hKe := hp.K_eq
      rw [h0] at hKe
      omega
    rw [ite_eq_left hK0, sum_class_zeros_none hp h0, h0, zeroCt_outerWZero_none, hv]
    norm_num
  · rw [ite_eq_right hK0]
    have hpK : p ≤ K n := by omega
    have hm : 2 * (mHalf p : ℤ) + 1 = (p : ℤ) := by exact_mod_cast hp.two_mHalf
    by_cases hK1 : K n < 2 * p
    · have h1 : mFloor p (K n) = 1 := hp.mFloor_eq_one hpK hK1
      rw [ite_eq_left hK1, sum_class_zeros_one hp h1, h1, zeroCt_outerWZero_one]
      push_cast
      linarith
    · have h2 : mFloor p (K n) = 2 := hp.mFloor_eq_two (by omega)
      rw [ite_eq_right hK1, sum_class_zeros_two hp h2, h2, zeroCt_outerWZero_two]
      push_cast
      linarith

/-- **(4.14)**: "Summing (4.12) and applying Lemma 4.2 gives the integer `γ_p^out`."

`∑_ρ W_ρ − min(r_p, z) = γ_p^out` in both printed branches — and also in the range `p > K`,
where both sides are `0`.  This is the paper's "These counts prove (4.14)". -/
theorem gammaOut_eq (hp : OuterHyp n p) :
    (∑ ρ : OuterRows n p, outerWeight n p ρ)
        - min (rOut n p) ((outerZeroCount n p : ℕ) : ℤ)
      = gammaOut n p := by
  rw [sum_outerWeight_eq hp, outerZeroCount_eq hp, gammaOut]
  by_cases hK0 : K n < p
  · rw [ite_eq_left hK0, ite_eq_left hK0, ite_eq_left hK0, rOut_eq_zero_of_lt n p hK0]
    have hNK : (N n : ℤ) ≤ (K n : ℤ) := by exact_mod_cast N_le_K n
    rw [min_eq_left (by linarith : (0 : ℤ) ≤ (K n : ℤ) - (N n : ℤ))]
    ring
  · rw [ite_eq_right hK0, ite_eq_right hK0, ite_eq_right hK0]
    by_cases hK1 : K n < 2 * p
    · rw [ite_eq_left hK1, ite_eq_left hK1, ite_eq_left hK1]
    · rw [ite_eq_right hK1, ite_eq_right hK1, ite_eq_right hK1]

/-- **The dimension identity of the outer range**: the basis (4.11) together with the
zero-class rows has exactly `h` elements,
`m_K + ∑_{a=1}^{m} (ℓ_K(a) − δ_a) = m_K + (K − m_K) − N = h`. -/
theorem outerRows_card (hp : OuterHyp n p) : Fintype.card (OuterRows n p) = h n := by
  classical
  have hsum : Fintype.card (OuterRows n p)
      = outerDim n p 0 + ∑ a ∈ Icc 1 (mHalf p), outerDim n p a := by
    rw [Fintype.card_sigma]
    simp only [Fintype.card_fin]
    rw [Fin.sum_univ_eq_sum_range (fun a => outerDim n p a) (mHalf p + 1), sum_range_succ_Icc]
  have hterm : ∀ a ∈ Icc 1 (mHalf p),
      ((outerDim n p a : ℕ) : ℤ)
        = (ell p (K n) a : ℤ) - (if a ≤ N n then (1 : ℤ) else 0) := by
    intro a ha
    rw [Finset.mem_Icc] at ha
    have ha0 : a ≠ 0 := by omega
    have hle : (if a ≤ N n then 1 else 0 : ℕ) ≤ ell p (K n) a := by
      by_cases hc : a ≤ N n
      · rw [ite_eq_left hc]; exact one_le_ell p (K n) a ha.1 (le_trans hc (N_le_K n))
      · rw [ite_eq_right hc]; omega
    simp only [outerDim, ite_eq_right ha0, outerRowCt]
    rw [Nat.cast_sub hle, cast_delta]
  have hmK : mFloor p (K n) ≤ K n := Nat.div_le_self _ _
  have hs : ∑ a ∈ Icc 1 (mHalf p), (ell p (K n) a : ℤ)
      = (K n : ℤ) - (mFloor p (K n) : ℤ) := by
    have h1 : ((∑ a ∈ Icc 1 (mHalf p), ell p (K n) a : ℕ) : ℤ)
        = ((K n - mFloor p (K n) : ℕ) : ℤ) := by
      rw [sum_ell p (K n) hp.two_mHalf]
    rw [Nat.cast_sub hmK] at h1
    rw [← h1]
    push_cast
    ring
  have hd : ∑ a ∈ Icc 1 (mHalf p), ((outerDim n p a : ℕ) : ℤ)
      = (K n : ℤ) - (mFloor p (K n) : ℤ) - (N n : ℤ) := by
    rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, hs, sum_delta hp]
  have hNK : N n ≤ K n := N_le_K n
  have hdim0 : outerDim n p 0 = mFloor p (K n) := by simp [outerDim]
  have hfinal : ((Fintype.card (OuterRows n p) : ℕ) : ℤ) = ((h n : ℕ) : ℤ) := by
    rw [hsum, hdim0]
    push_cast
    rw [hd, h_eq_K_sub_N n, Nat.cast_sub hNK]
    ring
  exact_mod_cast hfinal

end Assembly

/-! # §F.  The reduction: Proposition 4.3 from the local data of §4.2

The proof of Proposition 4.3 on p. 13 is one sentence — "The first assertion follows from
(4.10) and Lemma 4.2" — resting on the local analysis of pp. 11–12: the splitting (4.10), the
basis (4.11), its `ℤ_p`-unimodularity, and the entry bounds behind the weights (4.12).  This
section proves the *implication*; the local analysis itself is `outer_local_analysis` (§G),
proved in `Zeta5/OuterBasis.lean`. -/

section Reduction

variable {n p : ℕ}

/-- **Proposition 4.3, reduced to the local data of §4.2.**

Hypotheses, all of them parts of the paper's own proof:

* `Aq`, `L`, `pinv` are the splitting `G_K = A + p^{-1}L` of (4.10) in the basis (4.11),
  with `L` integral (`hL`) and satisfying `hvanish`, the one consequence of the rank bound
  `rank_{ℚ_p} L ≤ r_p` that Lemma 4.2 uses ("Terms with `k > r` vanish", p. 12);
* `eρ`, `hWe`: the rows of the matrix are the rows of (4.11) together with the zero-class
  rows, and `W` is twice the weight (4.12) assigned to each (`outerWeight`);
* `hA`: the entry bound `v_p^G(A_{uv}) ≥ w_u + w_v` of (4.12);
* `c`, `hcunit`, `hbasis`: the basis change is `ℤ_p`-unimodular, so `Δ_K` and
  `det(A + p^{-1}L)` differ by a `p`-adic unit.

Conclusion: `v_p^G(Δ_K) ≥ γ_p^out`, which is Proposition 4.3.  The two ingredients that make
it work are proved in this file: Lemma 4.2 in the form `lemma_4_2_gauss_of_vanishing` (§A),
and the identity `∑ W − min(r_p, z) = γ_p^out` of (4.14) (`gammaOut_eq`, §E).

The two corollaries below supply `hvanish` from the two forms of (4.10): the vanishing
columns (`prop_4_3_of_local_data`, correct in the **monomial** basis) and the literal rank
bound (`prop_4_3_of_local_data_rank`, which is the form that survives the change of basis to
(4.11) — see the note on (4.10) in `Zeta5/OuterLocal.lean`). -/
theorem prop_4_3_of_local_data_vanishing [hpf : Fact p.Prime] (hp : OuterHyp n p)
    (Aq L : Matrix (Fin (h n)) (Fin (h n)) ℚ[X])
    (W : Fin (h n) → ℤ) (eρ : OuterRows n p ≃ Fin (h n))
    (hWe : ∀ ρ, W (eρ ρ) = outerWeight n p ρ)
    (hA : ∀ i j, (gaussFil p).vge (Aq i j) (((W i + W j : ℤ) : ℚ) / 2))
    (pinv : ℚ[X]) (hpinv : (gaussFil p).vge pinv (-1))
    (hL : ∀ i j, vGAtLeast p (L i j) 0)
    (hvanish : ∀ t : Finset (Fin (h n)), (rOut n p).toNat < (Finset.univ \ t).card →
      (mixCol Aq (pinv • L) t).det = 0)
    (c : ℚ) (hcunit : padicValRat p c = 0)
    (hbasis : Delta n = Polynomial.C c * (Aq + pinv • L).det) :
    vGAtLeast p (Delta n) (gammaOut n p) := by
  classical
  have hWsum : ∑ i, W i = ∑ ρ : OuterRows n p, outerWeight n p ρ := by
    rw [← Equiv.sum_comp eρ W]
    exact Finset.sum_congr rfl fun ρ _ => hWe ρ
  have hW0 : ∀ i, W i ≤ 0 := by
    intro i
    have hi := hWe (eρ.symm i)
    rw [Equiv.apply_symm_apply] at hi
    rw [hi]
    exact outerWeight_nonpos n p _
  have hz : (Finset.univ.filter (fun i => W i = 0)).card = outerZeroCount n p := by
    rw [outerZeroCount, Finset.card_filter, Finset.card_filter,
      ← Equiv.sum_comp eρ (fun i => if W i = 0 then 1 else 0)]
    exact Finset.sum_congr rfl fun ρ _ => by rw [hWe ρ]
  have hdet := lemma_4_2_gauss_of_vanishing p W hW0 Aq L hA pinv hpinv hL (rOut n p).toNat
    hvanish (Finset.univ.filter (fun i => W i = 0)).card rfl
  have hrnn : (0 : ℤ) ≤ rOut n p := le_max_left _ _
  have hmin : (((min (rOut n p).toNat
        ((Finset.univ.filter (fun i => W i = 0)).card) : ℕ)) : ℤ)
      = min (rOut n p) ((outerZeroCount n p : ℕ) : ℤ) := by
    rw [hz, Nat.cast_min, Int.toNat_of_nonneg hrnn]
  rw [hmin, hWsum, gammaOut_eq hp] at hdet
  have hCc : vGAtLeast p (Polynomial.C c) 0 := by
    intro i hi
    rcases eq_or_ne i 0 with rfl | hne
    · rw [Polynomial.coeff_C_zero, hcunit]
    · rw [Polynomial.coeff_C, ite_eq_right hne] at hi
      exact absurd rfl hi
  rw [hbasis]
  simpa using vGAtLeast_mul hCc hdet

/-- **Proposition 4.3 from the local data, with (4.10) in its vanishing-columns form.**

This is the form the paper proves in the *monomial* basis ("Its first `h − r_p` rows and
columns vanish", p. 12).  It is kept because it is the paper's own justification of the rank
bound and is strictly stronger; but it is **not** the form that survives the change of basis
to (4.11), for which see `prop_4_3_of_local_data_rank`. -/
theorem prop_4_3_of_local_data [hpf : Fact p.Prime] (hp : OuterHyp n p)
    (Aq L : Matrix (Fin (h n)) (Fin (h n)) ℚ[X])
    (W : Fin (h n) → ℤ) (eρ : OuterRows n p ≃ Fin (h n))
    (hWe : ∀ ρ, W (eρ ρ) = outerWeight n p ρ)
    (hA : ∀ i j, (gaussFil p).vge (Aq i j) (((W i + W j : ℤ) : ℚ) / 2))
    (pinv : ℚ[X]) (hpinv : (gaussFil p).vge pinv (-1))
    (hL : ∀ i j, vGAtLeast p (L i j) 0)
    (C : Finset (Fin (h n))) (hC : ∀ i j, j ∈ C → L i j = 0)
    (hCr : Cᶜ.card ≤ (rOut n p).toNat)
    (c : ℚ) (hcunit : padicValRat p c = 0)
    (hbasis : Delta n = Polynomial.C c * (Aq + pinv • L).det) :
    vGAtLeast p (Delta n) (gammaOut n p) :=
  prop_4_3_of_local_data_vanishing hp Aq L W eρ hWe hA pinv hpinv hL
    (vanishing_of_zeroCols Aq L pinv (rOut n p).toNat C hC hCr) c hcunit hbasis

/-- **Proposition 4.3 from the local data, with (4.10) read literally**: `rank_{ℚ_p} L ≤ r_p`,
the rank computed after the inclusion `ℚ[X] ↪ ℚ(X)`.

This is the form of (4.10) that the paper states, and — unlike the vanishing-columns form —
it is the one that holds in the basis (4.11) in which the matrices of §4.2 actually live.
The degree count behind the vanishing columns is a statement about the *monomial* basis: in
the basis (4.11) every row has degree between `h − 6` and `h − 1`, so no column of `L`
vanishes, while the rank is unchanged by the (invertible) change of basis.  See the note on
(4.10) at the head of `Zeta5/OuterLocal.lean`. -/
theorem prop_4_3_of_local_data_rank [hpf : Fact p.Prime] (hp : OuterHyp n p)
    (Aq L : Matrix (Fin (h n)) (Fin (h n)) ℚ[X])
    (W : Fin (h n) → ℤ) (eρ : OuterRows n p ≃ Fin (h n))
    (hWe : ∀ ρ, W (eρ ρ) = outerWeight n p ρ)
    (hA : ∀ i j, (gaussFil p).vge (Aq i j) (((W i + W j : ℤ) : ℚ) / 2))
    (pinv : ℚ[X]) (hpinv : (gaussFil p).vge pinv (-1))
    (hL : ∀ i j, vGAtLeast p (L i j) 0)
    (hrank : (L.map (algebraMap ℚ[X] (RatFunc ℚ))).rank ≤ (rOut n p).toNat)
    (c : ℚ) (hcunit : padicValRat p c = 0)
    (hbasis : Delta n = Polynomial.C c * (Aq + pinv • L).det) :
    vGAtLeast p (Delta n) (gammaOut n p) :=
  prop_4_3_of_local_data_vanishing hp Aq L W eρ hWe hA pinv hpinv hL
    (vanishing_of_rank (algebraMap ℚ[X] (RatFunc ℚ)) (RatFunc.algebraMap_injective ℚ)
      Aq L pinv (rOut n p).toNat hrank) c hcunit hbasis

end Reduction

/-! # §G.  Proposition 4.3

The determinant half of the proof on p. 13 is `prop_4_3_of_local_data` above, and it is
complete.  The *local* half — the first three paragraphs of §4.2 — is
`outer_local_analysis`, proved in `Zeta5/OuterBasis.lean`. -/

section Prop43

/-- **The local analysis of §4.2 (pp. 11–12).**  Proved in `Zeta5/OuterBasis.lean`.

The paper's text that this stands for, verbatim:

> Choose `c_e ∈ ℤ_p` with `c_e ≡ pμ(t^e)` (mod `p`), taking `c_e = 0` for `e < 2p − 3`.
> Replace each polynomial moment by `μ_0(t^e) = μ(t^e) − c_e/p` and leave the simple-pole
> values unchanged.  The matrix then has the form
>     `G_K = A + p^{-1}L`,   `rank_{ℚ_p} L ≤ r_p = max(0, K + 4N − 2p + 2)`,          (4.10)
> where `L` is integral.  To see the rank bound, the polynomial quotient of `W t^{i+j}/D_tail`
> has degree at most `i + j + 6N − K`.  Hence `L_ij = 0` if `i + j < K − 6N + 2p − 3`.  Its
> first `h − r_p` rows and columns vanish.  Thus the rank bound holds over `ℚ_p`, not merely
> modulo `p`.
>
> For an ordinary square class `a`, let `ℓ = ℓ_K(a)` and `δ = 1_{a≤N}`.  There are `ℓ − δ`
> remaining poles in the class and exactly `ℓ − 2` of the original poles have `j > p`.  Let
> `Q_a` be the product of the remaining factors in the class, put `P_a = D_tail/Q_a`, and let
> `E_a` be the product of the factors with `j > p`.  Use the rows `P_a q_{a,i}`, where
>     `q_{a,i}(t) = (t+a²)^i`, `0 ≤ i < ℓ−2`;  `E_a(t)(t+a²)^{i−(ℓ−2)}`, `ℓ−2 ≤ i < ℓ−δ`. (4.11)
> Together with the zero-class rows, these form a unimodular basis.  Indeed, the local
> polynomials are monic of successive degrees, and the resultants of distinct class factors are
> units.
>
> Cross-class entries for `A` are integral, since their quotients are polynomials with integral
> coefficients.  Within a class, if either row index is at least `ℓ − 2`, all poles with
> `j > p` cancel.  The two possible remaining pole values at `a` and `p − a` are integral and
> congruent modulo `p`.  For their constant coefficients, use `H^{(5)}_{p−a} ≡ H^{(5)}_{a−1}`
> (mod `p`) in (2.3).  Their coefficients of `X` are also congruent.  The divided difference at
> the two nodes is therefore integral.  Polynomial numerators preserve this congruence.
>
> For two indices `i, j < ℓ − 2`, the residue part has valuation at least `i + j + 6δ − ℓ − 4`.
> The row factors supply `i + j`, the factor `W` supplies `5δ`, the node derivative loses
> `ℓ − δ − 1`, and a harmonic value loses at most `5`.  The polynomial part is integral.  Thus
> valid nonpositive half-integer weights are (4.12).
>
> A single zero-class pole has weight `−1/2`.  For two zero-class poles `p, 2p`, the rows
> `1, t + p²` give entry bounds `−3, −1, 0`, so the weights `−2, 0` are valid.

Formally: there are matrices `A`, `L` over `ℚ[X]`, an element `pinv` with `v_p^G(pinv) ≥ −1`
(the `p^{-1}` of (4.10)) and a rational unit `c` such that

* the rows of the matrices are the rows of (4.11) plus the zero-class rows (`eρ`), carrying
  the doubled weights (4.12) (`hWe`);
* the entry bound `v_p^G(A_{uv}) ≥ w_u + w_v` holds;
* `L` is integral and `rank_{ℚ_p} L ≤ r_p`, the rank computed after the inclusion
  `ℚ[X] ↪ ℚ(X)` — the literal hypothesis of (4.10);
* the basis change is `ℤ_p`-unimodular: `Δ_K = c · det(A + pinv·L)` with `v_p(c) = 0`.

WHAT IS *NOT* ASSUMED HERE, because it is proved in this file: the weights are not free
parameters but `Zeta5.outerWeight`, the literal (4.12); and the value of
`∑ W − min(r_p, z)` is *not* assumed to be `γ_p^out` — that is the theorem
`Zeta5.gammaOut_eq` of §E.  The rank hypothesis is discharged into Lemma 4.2 by
`Zeta5.lemma_4_2_gauss_rank` (§A), which needs no field structure on `ℚ[X]`.

**The rank form of (4.10).**  The statement uses the rank bound, not the vanishing-columns form
of (4.10) (a set `C` of columns of `L` that vanish, with at most `r_p` columns outside `C`).
The vanishing-columns form holds in the **monomial** basis, where the paper proves it, but not
in the basis (4.11), where the matrices of (4.10) live: every row of (4.11) is `P_a q_{a,i}` of
degree `h − (ℓ_a − δ_a) + i ∈ [h − 6, h − 1]`, so the degree count "`L_{ij} = 0` if
`i + j < K − 6N + 2p − 3`" never applies, and an exact computation of the paper's `L` in
the basis (4.11) at `K = 40` finds **zero** vanishing columns at `p = 17, 19, 23`, where
`h − r_p = 17, 21, 29` of them would be needed, while `rank_ℚ L = r_p` exactly (the referee
audit; see README, "Provenance").  See the head of `Zeta5/OuterLocal.lean`.

The proof (`Zeta5.OuterBasis.outer_local_core`) uses the congruence
`H^{(5)}_{p−a} ≡ H^{(5)}_{a−1} (mod p)` and the divided-difference integrality
(`Zeta5.OuterLocal.H5_congr`, `Zeta5.OuterLocal.muPole_congr`,
`Zeta5.OuterLocal.muPole_divided_difference`), and the factorisation `Δ_K = c · det(…)` with
`v_p(c) = 0` is `Zeta5.OuterLocal.Delta_eq_of_basis` with
`Zeta5.OuterLocal.padicValRat_unimodular`, built on `Zeta5.OuterLocal.gram_basis_change`
(`Gram(U) = U G_K Uᵀ`). -/
theorem outer_local_analysis (n p : ℕ) [Fact p.Prime] (hp : OuterHyp n p) :
    ∃ (Aq L : Matrix (Fin (h n)) (Fin (h n)) ℚ[X]) (W : Fin (h n) → ℤ)
      (eρ : OuterRows n p ≃ Fin (h n)) (pinv : ℚ[X]) (c : ℚ),
      (∀ ρ, W (eρ ρ) = outerWeight n p ρ)
      ∧ (∀ i j, (gaussFil p).vge (Aq i j) (((W i + W j : ℤ) : ℚ) / 2))
      ∧ (gaussFil p).vge pinv (-1)
      ∧ (∀ i j, vGAtLeast p (L i j) 0)
      ∧ (L.map (algebraMap ℚ[X] (RatFunc ℚ))).rank ≤ (rOut n p).toNat
      ∧ padicValRat p c = 0
      ∧ Delta n = Polynomial.C c * (Aq + pinv • L).det :=
  -- Proved in `Zeta5/OuterBasis.lean`: the basis (4.11) and the zero-class rows,
  -- their `ℤ_p`-unimodularity (via `HermiteBasis.det_coeffMatrix_unimodular`), the splitting
  -- (4.10) with `rank L ≤ r_p`, and the entry bounds behind (4.12).  `outerDim` and
  -- `outerWeight` are definitionally `OuterBasis.dimO` and `OuterBasis.wtO`.
  OuterBasis.outer_local_core n p ⟨hp.ge7, hp.upper, hp.sq, hp.twoN, hp.fiveN⟩
    (outerDim n p) rfl (outerWeight n p) (fun _ => rfl) (outerRows_card hp)

/-- Proposition 4.3 under `OuterHyp`, i.e. for both of its assertions at once. -/
theorem prop_4_3_of_outerHyp (n p : ℕ) (hprime : p.Prime) (hp : OuterHyp n p) :
    vGAtLeast p (Delta n) (gammaOut n p) := by
  have : Fact p.Prime := ⟨hprime⟩
  obtain ⟨Aq, L, W, eρ, pinv, c, hWe, hA, hpinv, hL, hrank, hcunit, hbasis⟩ :=
    outer_local_analysis n p hp
  exact prop_4_3_of_local_data_rank hp Aq L W eρ hWe hA pinv hpinv hL hrank c hcunit hbasis

namespace Outer

/-- **Proposition 4.3, first assertion** (p. 13).  Under (4.9) — `p ≥ 7`, `p ≤ K < 3p`,
`p² > 2K`, `2N < p`, `5N ≤ 2p − 2` — one has `v_p^G(Δ_K) ≥ γ_p^out`.

Literally the statement of `Zeta5.prop_4_3` in `Interface.lean`. -/
theorem prop_4_3 (n p : ℕ) (hprime : p.Prime) (h7 : 7 ≤ p) (_hpK : p ≤ K n)
    (hK3p : K n < 3 * p) (hp2 : 2 * K n < p ^ 2) (hN : 2 * N n < p)
    (hN5 : 5 * N n ≤ 2 * p - 2) :
    vGAtLeast p (Delta n) (gammaOut n p) :=
  prop_4_3_of_outerHyp n p hprime ⟨hprime, h7, hK3p, hp2, hN, hN5⟩

/-- For `p > K` the hypotheses (4.9) minus `p ≤ K` hold automatically (for `n ≥ 1`): with
`K = 40n`, `N = 3n` and `p > 40n ≥ 40` one gets `p ≥ 7`, `K < 3p`, `p² > 2K`, `2N < p` and
`5N ≤ 2p − 2`. -/
theorem outerHyp_of_gt {n p : ℕ} (hprime : p.Prime) (hn : 0 < n) (hpK : K n < p) :
    OuterHyp n p := by
  have hK : K n = 40 * n := rfl
  have hN : N n = 3 * n := rfl
  rw [hK] at hpK
  refine ⟨hprime, by omega, by rw [hK]; omega, ?_, by rw [hN]; omega, by rw [hN]; omega⟩
  rw [hK]
  have h41 : 41 ≤ p := by omega
  nlinarith [hpK, h41, hn]

/-- **Proposition 4.3, second assertion** (p. 13).  For `p > K`, `v_p^G(Δ_K) ≥ 0`.

Literally the statement of `Zeta5.prop_4_3_large` in `Interface.lean`.  Note `γ_p^out = 0`
for `p > K` by (5.1) ("For `p > K`, put `γ_p^out = 0`"), so this is the `p > K` instance of
`prop_4_3_of_outerHyp`; the degenerate case `n = 0` (`h = 0`, `Δ_K = 1`) is separate. -/
theorem prop_4_3_large (n p : ℕ) (hprime : p.Prime) (hpK : K n < p) :
    vGAtLeast p (Delta n) 0 := by
  have : Fact p.Prime := ⟨hprime⟩
  have hgam : gammaOut n p = 0 := by rw [gammaOut, ite_eq_left hpK]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hempty : IsEmpty (Fin (h 0)) := by
      have h0 : h 0 = 0 := rfl
      rw [h0]; infer_instance
    have _inst := hempty
    have hD : Delta 0 = 1 := by rw [Delta]; exact Matrix.det_isEmpty
    rw [hD]
    exact vGAtLeast_one
  · rw [← hgam]
    exact prop_4_3_of_outerHyp n p hprime (outerHyp_of_gt hprime hn hpK)

end Outer

/-! ### The two statements of `Interface.lean`, type-checked

`Zeta5.prop_4_3` and `Zeta5.prop_4_3_large` of `Interface.lean` are proved by
`Outer.prop_4_3` and `Outer.prop_4_3_large`.  The two `example`s below assert that the latter
have **exactly** the former's types, transcribed from `Interface.lean` character for character.
(They live in the namespace `Zeta5.Outer` so that this file and `Interface.lean` can be
imported together.) -/

example : ∀ (n p : ℕ), p.Prime → 7 ≤ p → p ≤ K n → K n < 3 * p → 2 * K n < p ^ 2 →
    2 * N n < p → 5 * N n ≤ 2 * p - 2 → vGAtLeast p (Delta n) (gammaOut n p) :=
  Outer.prop_4_3

example : ∀ (n p : ℕ), p.Prime → K n < p → vGAtLeast p (Delta n) 0 :=
  Outer.prop_4_3_large

end Prop43

/-! # §H.  Known-answer controls

`γ_p^out` as the definition `Zeta5.gammaOut` computes it, against the values the referee audit
(see README, "Provenance") obtained from **exact determinants**, confirmed there by an independent
second computation.  These are the 37 primes satisfying (4.9) at
`K = 40, 80, 120`, where the audit found `v_p^G(Δ_K) ≥ γ_p^out` with equality at 27 of them —
so a transcription error in `gammaOut`, `rOut`, `vOut`, `uOut` or `tOut` would show up here. -/

namespace OuterChecks

open Zeta5

/-! ### `K = 40` (`n = 1`, `N = 3`, `h = 37`): the six primes of (4.9).
Audit (exact determinants, two independent computations):
true `v_p^G(Δ_40) = −123, −113, −110, −60, −46, −4`;
`γ_p^out = −124, −114, −110, −60, −46, −4`. -/

example : gammaOut 1 17 = -124 := by decide
example : gammaOut 1 19 = -114 := by decide
example : gammaOut 1 23 = -110 := by decide
example : gammaOut 1 29 = -60 := by decide
example : gammaOut 1 31 = -46 := by decide
example : gammaOut 1 37 = -4 := by decide

/-! ### `K = 80` (`n = 2`, `N = 6`, `h = 74`): the thirteen primes of (4.9).
Audit: `γ_p^out = −281, −269, −228, −232, −238, −208, −154, −112, −98, −56, −28, −14, −2`. -/

example : gammaOut 2 29 = -281 := by decide
example : gammaOut 2 31 = -269 := by decide
example : gammaOut 2 37 = -228 := by decide
example : gammaOut 2 41 = -232 := by decide
example : gammaOut 2 43 = -238 := by decide
example : gammaOut 2 47 = -208 := by decide
example : gammaOut 2 53 = -154 := by decide
example : gammaOut 2 59 = -112 := by decide
example : gammaOut 2 61 = -98 := by decide
example : gammaOut 2 67 = -56 := by decide
example : gammaOut 2 71 = -28 := by decide
example : gammaOut 2 73 = -14 := by decide
example : gammaOut 2 79 = -2 := by decide

/-! ### `K = 120` (`n = 3`, `N = 9`, `h = 111`): the eighteen primes of (4.9).
This is the range that exercises `u > 0` (`p = 41, 43, 61`), i.e. the `ℓ = 6` row of the p. 13
table.  Audit: `γ_p^out = −410, −422, −402, −365, −346, −348, −342, −306, −288, −234, −206,
−164, −108, −80, −66, −38, −24, −8`. -/

example : gammaOut 3 41 = -410 := by decide
example : gammaOut 3 43 = -422 := by decide
example : gammaOut 3 47 = -402 := by decide
example : gammaOut 3 53 = -365 := by decide
example : gammaOut 3 59 = -346 := by decide
example : gammaOut 3 61 = -348 := by decide
example : gammaOut 3 67 = -342 := by decide
example : gammaOut 3 71 = -306 := by decide
example : gammaOut 3 73 = -288 := by decide
example : gammaOut 3 79 = -234 := by decide
example : gammaOut 3 83 = -206 := by decide
example : gammaOut 3 89 = -164 := by decide
example : gammaOut 3 97 = -108 := by decide
example : gammaOut 3 101 = -80 := by decide
example : gammaOut 3 103 = -66 := by decide
example : gammaOut 3 107 = -38 := by decide
example : gammaOut 3 109 = -24 := by decide
example : gammaOut 3 113 = -8 := by decide

/-! ### `p > K`: `γ_p^out = 0` (the second assertion of Proposition 4.3). -/

example : gammaOut 1 41 = 0 := by decide
example : gammaOut 2 83 = 0 := by decide
example : gammaOut 3 127 = 0 := by decide

/-! ### The `u > 0` regime really is exercised (as the referee audit observed). -/

example : uOut 2 41 = 5 := by decide
example : uOut 2 43 = 1 := by decide
example : uOut 3 41 = 7 := by decide
example : uOut 3 61 = 8 := by decide
example : uOut 1 17 = 0 := by decide

/-! ### The rank bound `r_p` of (4.10), as the audit computed `rank_ℚ L = r_p` exactly. -/

example : rOut 2 29 = 48 := by decide
example : rOut 3 41 = 76 := by decide
example : rOut 2 47 = 12 := by decide
example : rOut 2 53 = 0 := by decide

/-! ### The p. 13 table, restated as a single decidable claim. -/

example : (outerCost 2 1, outerCost 3 1, outerCost 4 1, outerCost 5 1, outerCost 6 1)
    = (0, -1, -2, -4, -6) := by decide

example : (outerZeroCt 2 1, outerZeroCt 3 1, outerZeroCt 4 1, outerZeroCt 5 1, outerZeroCt 6 1)
    = (1, 1, 2, 2, 3) := by decide

example : (outerCost 2 0, outerCost 3 0, outerCost 4 0, outerCost 5 0, outerCost 6 0)
    = (0, -7, -14, -21, -28) := by decide

example : (outerZeroCt 2 0, outerZeroCt 3 0, outerZeroCt 4 0, outerZeroCt 5 0, outerZeroCt 6 0)
    = (2, 2, 2, 2, 2) := by decide

/-! ## Axiom checks -/

#print axioms Zeta5.lemma_4_2_of_vanishing
#print axioms Zeta5.lemma_4_2_of_zeroCols
#print axioms Zeta5.lemma_4_2_of_rank_map
#print axioms Zeta5.lemma_4_2_gauss_zeroCols
#print axioms Zeta5.zeroCols_of_lowDegree
#print axioms Zeta5.card_compl_lt_filter
#print axioms Zeta5.table_removed
#print axioms Zeta5.table_unremoved
#print axioms Zeta5.sum_outerWeight_eq
#print axioms Zeta5.outerZeroCount_eq
#print axioms Zeta5.gammaOut_eq
#print axioms Zeta5.outerRows_card
#print axioms Zeta5.prop_4_3_of_local_data
#print axioms Zeta5.outer_local_analysis
#print axioms Zeta5.Outer.prop_4_3
#print axioms Zeta5.Outer.prop_4_3_large

end OuterChecks

end

end Zeta5
