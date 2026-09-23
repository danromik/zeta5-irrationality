/-
Zeta5/Lemma42.lean

**Lemma 4.2** of the paper (p. 12), formalised and proved, together with a machine-checked
counterexample showing that its half-integrality hypothesis cannot be dropped.

The paper's statement, verbatim:

> **Lemma 4.2.** Let `A` and `L` be `h × h` matrices.  Suppose that `v(A_ij) ≥ w_i + w_j`, where
> the `w_i` are nonpositive half-integers.  Let `r` be a nonnegative integer and assume that `L`
> is integral with rank at most `r`.  If exactly `z` weights are zero, then
>
>     v det(A + p^{-1} L) ≥ 2 ∑_i w_i - min(r, z).                     (4.13)
>
> The same assertion holds for the Gauss valuation of polynomial entries.

WHAT IS FORMALISED HERE, AND IN WHICH SETTING.

*  The valuation is **abstract**: a `Zeta5.ValFil F` on a commutative ring `F` is the predicate
   `v(x) ≥ c` for `c : ℚ` together with the six axioms actually used (`v(0) = ∞`, `v(1) ≥ 0`,
   monotonicity in `c`, the ultrametric inequality for `+`, additivity for `*`, invariance under
   `-`).  This is the honest minimum: the proof of (4.13) is a one-sided estimate and never needs
   equality in `v(xy) = v(x) + v(y)`, nor the value group, nor completeness.  The weights are
   genuine rationals, so the half-integrality hypothesis is a *hypothesis* and not built into the
   types — which is what makes the counterexample below expressible.
*  Two instances are provided: `Zeta5.padicFil p` (the `p`-adic valuation on `ℚ`), used for the
   counterexample, and `Zeta5.gaussFil p` (the Gauss valuation `v_p^G` on `ℚ[X]`, the "same
   assertion ... for the Gauss valuation" of the last line), which is the instance §4 uses and
   which is tied to `Zeta5.vGAtLeast` of `Basic.lean` by `Zeta5.gaussGe_intCast`.
*  `p^{-1}` is carried as an abstract element `pinv` with `v(pinv) ≥ -1`, which is all the proof
   uses.
*  "rank at most `r`" is `Matrix.rank L ≤ r`, which forces a **field**; that hypothesis is used
   in exactly one place (`mixCol_det_eq_zero`).  The `r = 0` case, which is the one Proposition
   4.1 needs, is therefore also given separately over a commutative ring
   (`lemma_4_2_rank_zero`, `lemma_4_2_rank_zero_gauss`), where it needs neither a field nor the
   half-integrality nor the nonpositivity of the weights.

THIS FILE CONTAINS NO `sorry`.

AUDIT CONTEXT.  The referee audit of the preprint (see README, "Provenance") proved Lemma 4.2
by hand and, in an independent verification, stress-tested it over `ℤ_7`, `ℤ_11` and `ℤ_3`
with 6000 random instances: no violation, and the bound is attained.  The same tests,
run with weights in `(1/4)ℤ` instead of `(1/2)ℤ`, produce violations — e.g. `p = 11`, `h = 3`,
`w = (-3/2, -1/4, -3/2)`, `r = 1`, `z = 0`, where the claimed bound is `-13/2` and the true
valuation is `-7`.  `lemma_4_2_needs_half_integers` below is a minimal witness of the same
phenomenon, checked by the kernel rather than by a random search.
-/
import Zeta5.Basic

namespace Zeta5

open Polynomial Finset

noncomputable section

/-! ## An abstract valuation, in `≥` form

`V.vge x c` reads "`v(x) ≥ c`".  Using the predicate rather than a `WithTop ℤ`-valued function
avoids all `⊤`-arithmetic and lets the weights be rationals. -/

/-- The axioms of a (nonarchimedean, ℚ-valued) valuation on `F`, in the form of the predicate
`v(x) ≥ c`.  Only these six facts are used in the proof of Lemma 4.2. -/
structure ValFil (F : Type*) [CommRing F] where
  /-- `v(x) ≥ c`. -/
  vge : F → ℚ → Prop
  /-- `v(0) = ∞`. -/
  vge_zero : ∀ c, vge 0 c
  /-- `v(1) ≥ 0`. -/
  vge_one : vge 1 0
  /-- A lower bound may be weakened. -/
  vge_mono : ∀ {x : F} {c c' : ℚ}, c' ≤ c → vge x c → vge x c'
  /-- The ultrametric inequality `v(x+y) ≥ min(v x, v y)`, in `≥` form. -/
  vge_add : ∀ {x y : F} {c : ℚ}, vge x c → vge y c → vge (x + y) c
  /-- `v(xy) ≥ v(x) + v(y)` (equality is never needed). -/
  vge_mul : ∀ {x y : F} {a b : ℚ}, vge x a → vge y b → vge (x * y) (a + b)
  /-- `v(-x) = v(x)`. -/
  vge_neg : ∀ {x : F} {c : ℚ}, vge x c → vge (-x) c

namespace ValFil

variable {F : Type*} [CommRing F] (V : ValFil F)

/-- A finite sum of elements of valuation `≥ c` has valuation `≥ c`. -/
lemma vge_sum {ι : Type*} (s : Finset ι) (f : ι → F) (c : ℚ) :
    (∀ i ∈ s, V.vge (f i) c) → V.vge (∑ i ∈ s, f i) c := by
  classical
  refine Finset.induction_on s (fun _ => by simpa using V.vge_zero c) ?_
  intro a s ha ih hall
  rw [Finset.sum_insert ha]
  exact V.vge_add (hall a (Finset.mem_insert_self _ _))
    (ih fun i hi => hall i (Finset.mem_insert_of_mem hi))

/-- A finite product: the valuations add. -/
lemma vge_prod {ι : Type*} (s : Finset ι) (f : ι → F) (c : ι → ℚ) :
    (∀ i ∈ s, V.vge (f i) (c i)) → V.vge (∏ i ∈ s, f i) (∑ i ∈ s, c i) := by
  classical
  refine Finset.induction_on s (fun _ => by simpa using V.vge_one) ?_
  intro a s ha ih hall
  rw [Finset.prod_insert ha, Finset.sum_insert ha]
  exact V.vge_mul (hall a (Finset.mem_insert_self _ _))
    (ih fun i hi => hall i (Finset.mem_insert_of_mem hi))

/-- Multiplying by the image of a unit of `ℤ` (a permutation sign) does not change the bound. -/
lemma vge_intUnit_mul {u : ℤˣ} {x : F} {c : ℚ} (h : V.vge x c) :
    V.vge (((u : ℤ) : F) * x) c := by
  rcases Int.units_eq_one_or u with hu | hu
  · rw [hu]; simpa using h
  · rw [hu]; simpa using V.vge_neg h

end ValFil

/-! ## The `p`-adic valuation on `ℚ` as a `ValFil` -/

/-- `v_p(x) ≥ c` for `x : ℚ`, with the convention `v_p(0) = ∞`. -/
def padicGe (p : ℕ) (x : ℚ) (c : ℚ) : Prop := x = 0 ∨ c ≤ (padicValRat p x : ℚ)

/-- The `p`-adic valuation on `ℚ`, as a `ValFil`. -/
def padicFil (p : ℕ) [Fact p.Prime] : ValFil ℚ where
  vge := padicGe p
  vge_zero := fun _ => Or.inl rfl
  vge_one := Or.inr (by simp [padicValRat.one])
  vge_mono := by
    rintro x c c' hle (rfl | h)
    · exact Or.inl rfl
    · exact Or.inr (le_trans hle h)
  vge_add := by
    rintro x y c hx hy
    by_cases hxy : x + y = 0
    · exact Or.inl hxy
    refine Or.inr ?_
    have hx' : (c : ℚ) ≤ (padicValRat p x : ℚ) ∨ x = 0 := hx.symm.imp id id
    rcases hx with (rfl | hx)
    · simpa using hy.resolve_left (by simpa using hxy)
    rcases hy with (rfl | hy)
    · simpa using (Or.inr hx : padicGe p x c).resolve_left (by simpa using hxy)
    have hmin := padicValRat.min_le_padicValRat_add (p := p) hxy
    have : (min (padicValRat p x) (padicValRat p y) : ℚ) ≤ (padicValRat p (x + y) : ℚ) := by
      exact_mod_cast hmin
    refine le_trans ?_ this
    exact le_min hx hy
  vge_mul := by
    rintro x y a b hx hy
    rcases hx with (rfl | hx)
    · exact Or.inl (by simp)
    rcases hy with (rfl | hy)
    · exact Or.inl (by simp)
    by_cases hx0 : x = 0
    · exact Or.inl (by simp [hx0])
    by_cases hy0 : y = 0
    · exact Or.inl (by simp [hy0])
    refine Or.inr ?_
    rw [padicValRat.mul hx0 hy0]
    push_cast
    linarith
  vge_neg := by
    rintro x c (rfl | h)
    · exact Or.inl (by simp)
    · exact Or.inr (by rwa [padicValRat.neg])

@[simp] lemma padicFil_vge (p : ℕ) [Fact p.Prime] (x c : ℚ) :
    (padicFil p).vge x c ↔ (x = 0 ∨ c ≤ (padicValRat p x : ℚ)) := Iff.rfl

/-! ## The Gauss valuation `v_p^G` on `ℚ[X]` as a `ValFil`

`v_p^G(A)` is the minimum of the `p`-adic valuations of the coefficients of `A` (p. 5 of the
paper).  `Zeta5.vGAtLeast` in `Basic.lean` is its integer-bound form; `gaussGe_intCast` below
identifies the two. -/

/-- `v_p^G(A) ≥ c` for a rational bound `c`. -/
def gaussGe (p : ℕ) [Fact p.Prime] (A : ℚ[X]) (c : ℚ) : Prop :=
  ∀ i, (padicFil p).vge (A.coeff i) c

/-- The Gauss valuation on `ℚ[X]`, as a `ValFil`.  This is the instance the paper means by
"the Gauss valuation of polynomial entries". -/
def gaussFil (p : ℕ) [Fact p.Prime] : ValFil ℚ[X] where
  vge := gaussGe p
  vge_zero := fun _ i => by rw [Polynomial.coeff_zero]; exact (padicFil p).vge_zero _
  vge_one := by
    intro i
    rw [Polynomial.coeff_one]
    split
    · exact (padicFil p).vge_one
    · exact (padicFil p).vge_zero _
  vge_mono := fun hle h i => (padicFil p).vge_mono hle (h i)
  vge_add := fun hx hy i => by
    rw [Polynomial.coeff_add]; exact (padicFil p).vge_add (hx i) (hy i)
  vge_mul := fun {x y a b} hx hy i => by
    rw [Polynomial.coeff_mul]
    refine (padicFil p).vge_sum _ _ _ fun q _ => ?_
    exact (padicFil p).vge_mul (hx q.1) (hy q.2)
  vge_neg := fun h i => by
    rw [Polynomial.coeff_neg]; exact (padicFil p).vge_neg (h i)

/-- The Gauss valuation `ValFil` is `Zeta5.vGAtLeast` when the bound is an integer. -/
lemma gaussGe_intCast (p : ℕ) [Fact p.Prime] (A : ℚ[X]) (c : ℤ) :
    (gaussFil p).vge A (c : ℚ) ↔ vGAtLeast p A c := by
  constructor
  · intro h i hi
    rcases h i with h0 | h0
    · exact absurd h0 hi
    · exact_mod_cast h0
  · intro h i
    by_cases hi : A.coeff i = 0
    · exact Or.inl hi
    · exact Or.inr (by exact_mod_cast h i hi)

/-! ## The combinatorial core: the loss `k + ∑_S w + ∑_T w` is at most `min(r, z)`

This is the paper's sentence "This expression increases by one at each zero weight and has
nonpositive increments after the zero weights.  Its maximum is `min(r, z)`." -/

section Loss

variable {hh : ℕ}

/-- A nonpositive half-integer is either `0` or `≤ -1/2`.  This, and only this, is where the
half-integrality hypothesis of Lemma 4.2 is used. -/
lemma le_neg_half_of_ne_zero {q : ℚ} (h0 : q ≤ 0) (hk : ∃ k : ℤ, q = (k : ℚ) / 2)
    (hne : q ≠ 0) : q ≤ -(1 / 2) := by
  obtain ⟨k, rfl⟩ := hk
  have hk0 : (k : ℚ) ≤ 0 := by linarith
  have hkZ : k ≤ 0 := by exact_mod_cast hk0
  have hkne : k ≠ 0 := by
    rintro rfl; simp at hne
  have : k ≤ -1 := by omega
  have : (k : ℚ) ≤ -1 := by exact_mod_cast this
  linarith

/-- The sum of the weights over a set `S` is at most `(#zeros in S - #S)/2`. -/
lemma sum_w_le (w : Fin hh → ℚ) (hw0 : ∀ i, w i ≤ 0) (hwhalf : ∀ i, ∃ k : ℤ, w i = (k : ℚ) / 2)
    (S : Finset (Fin hh)) :
    ∑ i ∈ S, w i ≤ (((S.filter (fun i => w i = 0)).card : ℚ) - S.card) / 2 := by
  classical
  have hsplit : ∑ i ∈ S.filter (fun i => w i = 0), w i
      + ∑ i ∈ S.filter (fun i => ¬ w i = 0), w i = ∑ i ∈ S, w i :=
    Finset.sum_filter_add_sum_filter_not S _ w
  have hzero : ∑ i ∈ S.filter (fun i => w i = 0), w i = 0 :=
    Finset.sum_eq_zero fun i hi => (Finset.mem_filter.1 hi).2
  have hneg : ∑ i ∈ S.filter (fun i => ¬ w i = 0), w i
      ≤ ∑ _i ∈ S.filter (fun i => ¬ w i = 0), (-(1 / 2) : ℚ) := by
    refine Finset.sum_le_sum fun i hi => ?_
    exact le_neg_half_of_ne_zero (hw0 i) (hwhalf i) (Finset.mem_filter.1 hi).2
  rw [Finset.sum_const, nsmul_eq_mul] at hneg
  have hcards : (S.filter (fun i => w i = 0)).card + (S.filter (fun i => ¬ w i = 0)).card
      = S.card := Finset.card_filter_add_card_filter_not _
  have hcardsQ : ((S.filter (fun i => w i = 0)).card : ℚ)
      + ((S.filter (fun i => ¬ w i = 0)).card : ℚ) = (S.card : ℚ) := by exact_mod_cast hcards
  rw [← hsplit, hzero, zero_add]
  linarith

/-- The count of zero weights inside `S` is at most `min (#S) z`. -/
lemma card_filter_zero_le (w : Fin hh → ℚ) (S : Finset (Fin hh)) (z : ℕ)
    (hz : z = (Finset.univ.filter (fun i => w i = 0)).card) :
    (S.filter (fun i => w i = 0)).card ≤ min S.card z := by
  classical
  refine le_min (Finset.card_filter_le _ _) ?_
  rw [hz]
  exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ S))

/-- **The loss bound.**  For any two `k`-element sets of indices with `k ≤ r`,
`k + ∑_S w + ∑_T w ≤ min(r, z)`.  This is the paper's maximisation of `k + 2∑_{i≤k} w_(i)`. -/
lemma loss_le (w : Fin hh → ℚ) (hw0 : ∀ i, w i ≤ 0) (hwhalf : ∀ i, ∃ k : ℤ, w i = (k : ℚ) / 2)
    (r z : ℕ) (hz : z = (Finset.univ.filter (fun i => w i = 0)).card)
    (S T : Finset (Fin hh)) (hST : S.card = T.card) (hSr : S.card ≤ r) :
    (S.card : ℚ) + ∑ i ∈ S, w i + ∑ i ∈ T, w i ≤ ((min r z : ℕ) : ℚ) := by
  classical
  have hS := sum_w_le w hw0 hwhalf S
  have hT := sum_w_le w hw0 hwhalf T
  have haS := card_filter_zero_le w S z hz
  have haT := card_filter_zero_le w T z hz
  have hminle : min S.card z ≤ min r z := min_le_min hSr le_rfl
  have haSQ : ((S.filter (fun i => w i = 0)).card : ℚ) ≤ ((min r z : ℕ) : ℚ) := by
    exact_mod_cast le_trans haS hminle
  have haT' : (T.filter (fun i => w i = 0)).card ≤ min r z := by
    refine le_trans haT ?_
    calc min T.card z = min S.card z := by rw [hST]
      _ ≤ min r z := hminle
  have haTQ : ((T.filter (fun i => w i = 0)).card : ℚ) ≤ ((min r z : ℕ) : ℚ) := by
    exact_mod_cast haT'
  have hSTQ : (S.card : ℚ) = (T.card : ℚ) := by exact_mod_cast hST
  linarith

end Loss

/-! ## The column-mixing expansion of `det (A + B)` -/

section Mix

variable {F : Type*} [CommRing F] {hh : ℕ}

open scoped Classical in
/-- `mixCol A B t` is the matrix whose `j`-th column is that of `A` if `j ∈ t` and that of `B`
otherwise.  The complementary-minor expansion of the paper is, in this form, the statement that
`det (A + B)` is the sum of `det (mixCol A B t)` over all `t`. -/
def mixCol (A B : Matrix (Fin hh) (Fin hh) F) (t : Finset (Fin hh)) :
    Matrix (Fin hh) (Fin hh) F :=
  Matrix.of fun i j => if j ∈ t then A i j else B i j

omit [CommRing F] in
open scoped Classical in
lemma mixCol_apply (A B : Matrix (Fin hh) (Fin hh) F) (t : Finset (Fin hh)) (i j : Fin hh) :
    mixCol A B t i j = if j ∈ t then A i j else B i j := rfl

/-- **The expansion by complementary minors** (paper, proof of Lemma 4.2), in the column form:
`det (A + B) = ∑_t det (mixCol A B t)`, the sum over all subsets `t` of the columns taken
from `A`.  Multilinearity in the columns, nothing more. -/
lemma det_add_eq_sum_mixCol (A B : Matrix (Fin hh) (Fin hh) F) :
    (A + B).det = ∑ t : Finset (Fin hh), (mixCol A B t).det := by
  classical
  have hterm : ∀ t : Finset (Fin hh), (mixCol A B t).det
      = ∑ σ : Equiv.Perm (Fin hh), ((Equiv.Perm.sign σ : ℤ) : F)
          * ((∏ i ∈ t, A (σ i) i) * ∏ i ∈ Finset.univ \ t, B (σ i) i) := by
    intro t
    rw [Matrix.det_apply']
    refine Finset.sum_congr rfl fun σ _ => ?_
    congr 1
    have hunion : t ∪ (Finset.univ \ t) = Finset.univ := by
      rw [Finset.union_sdiff_of_subset (Finset.subset_univ t)]
    have hdisj : Disjoint t (Finset.univ \ t) := Finset.disjoint_sdiff
    calc ∏ i, mixCol A B t (σ i) i
        = ∏ i ∈ t ∪ (Finset.univ \ t), mixCol A B t (σ i) i := by rw [hunion]
      _ = (∏ i ∈ t, mixCol A B t (σ i) i) * ∏ i ∈ Finset.univ \ t, mixCol A B t (σ i) i :=
          Finset.prod_union hdisj
      _ = (∏ i ∈ t, A (σ i) i) * ∏ i ∈ Finset.univ \ t, B (σ i) i := by
          congr 1
          · exact Finset.prod_congr rfl fun i hi => by
              simp only [mixCol_apply, hi, ite_true]
          · exact Finset.prod_congr rfl fun i hi => by
              simp only [mixCol_apply, (Finset.mem_sdiff.1 hi).2, ite_false]
  rw [Matrix.det_apply']
  have hexp : ∀ σ : Equiv.Perm (Fin hh), ∏ i, (A + B) (σ i) i
      = ∑ t : Finset (Fin hh), (∏ i ∈ t, A (σ i) i) * ∏ i ∈ Finset.univ \ t, B (σ i) i := by
    intro σ
    have := Finset.prod_add (fun i => A (σ i) i) (fun i => B (σ i) i) Finset.univ
    rw [Finset.powerset_univ] at this
    simpa [Matrix.add_apply] using this
  calc ∑ σ : Equiv.Perm (Fin hh), ((Equiv.Perm.sign σ : ℤ) : F) * ∏ i, (A + B) (σ i) i
      = ∑ σ : Equiv.Perm (Fin hh), ∑ t : Finset (Fin hh), ((Equiv.Perm.sign σ : ℤ) : F)
          * ((∏ i ∈ t, A (σ i) i) * ∏ i ∈ Finset.univ \ t, B (σ i) i) := by
        refine Finset.sum_congr rfl fun σ _ => ?_
        rw [hexp σ, Finset.mul_sum]
    _ = ∑ t : Finset (Fin hh), ∑ σ : Equiv.Perm (Fin hh), ((Equiv.Perm.sign σ : ℤ) : F)
          * ((∏ i ∈ t, A (σ i) i) * ∏ i ∈ Finset.univ \ t, B (σ i) i) := Finset.sum_comm
    _ = ∑ t : Finset (Fin hh), (mixCol A B t).det := by
        exact Finset.sum_congr rfl fun t _ => (hterm t).symm

end Mix

/-! ## The rank hypothesis: terms with more than `r` columns from `L` vanish -/

section Rank

variable {F : Type*} [Field F] {hh : ℕ}

/-- "Terms with `k > r` vanish" (paper, proof of Lemma 4.2).  If more than `rank L` of the
columns of `mixCol A (pinv • L) t` come from `L`, those columns are linearly dependent and the
determinant is zero. -/
lemma mixCol_det_eq_zero (A L : Matrix (Fin hh) (Fin hh) F) (pinv : F) {r : ℕ}
    (hrank : L.rank ≤ r) (t : Finset (Fin hh)) (ht : r < (Finset.univ \ t).card) :
    (mixCol A (pinv • L) t).det = 0 := by
  classical
  by_contra hdet
  set N := mixCol A (pinv • L) t with hN
  have hli : LinearIndependent F N.col := Matrix.linearIndependent_cols_of_det_ne_zero hdet
  set S : Finset (Fin hh) := Finset.univ \ t with hS
  have hli' : LinearIndependent F (fun j : {x // x ∈ S} => N.col (j : Fin hh)) :=
    hli.comp _ Subtype.val_injective
  have hcolmem : ∀ j : {x // x ∈ S},
      N.col (j : Fin hh) ∈ Submodule.span F (Set.range L.col) := by
    intro j
    have hj : (j : Fin hh) ∉ t := (Finset.mem_sdiff.1 j.2).2
    have hcol : N.col (j : Fin hh) = pinv • L.col (j : Fin hh) := by
      funext i
      simp [hN, Matrix.col_apply, mixCol_apply, hj, Matrix.smul_apply, smul_eq_mul]
    rw [hcol]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(j : Fin hh), rfl⟩)
  have hspanle : Submodule.span F (Set.range (fun j : {x // x ∈ S} => N.col (j : Fin hh)))
      ≤ Submodule.span F (Set.range L.col) := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact hcolmem j
  have hcard : Module.finrank F
      (Submodule.span F (Set.range (fun j : {x // x ∈ S} => N.col (j : Fin hh))))
      = Fintype.card {x // x ∈ S} := finrank_span_eq_card hli'
  have hmono := Submodule.finrank_mono hspanle
  rw [hcard, ← Matrix.rank_eq_finrank_span_cols, Fintype.card_coe] at hmono
  omega

end Rank

/-! ## Lemma 4.2 -/

section Main

variable {F : Type*} [CommRing F] {hh : ℕ}

/-- **Lemma 4.2 for `r = 0`** (p. 12), the case Proposition 4.1 uses.

With `r = 0` the correction `L` is absent and (4.13) reads `v det A ≥ 2 ∑_i w_i`.  This is pure
Leibniz: it needs neither a field, nor the nonpositivity of the weights, nor their
half-integrality. -/
theorem lemma_4_2_rank_zero (V : ValFil F) (w : Fin hh → ℚ) (A : Matrix (Fin hh) (Fin hh) F)
    (hA : ∀ i j, V.vge (A i j) (w i + w j)) :
    V.vge A.det (2 * ∑ i, w i) := by
  classical
  rw [Matrix.det_apply']
  refine V.vge_sum _ _ _ fun σ _ => ?_
  refine V.vge_intUnit_mul ?_
  have hprod : V.vge (∏ i, A (σ i) i) (∑ i, (w (σ i) + w i)) :=
    V.vge_prod _ _ _ fun i _ => hA _ _
  refine V.vge_mono (le_of_eq ?_) hprod
  rw [Finset.sum_add_distrib, Equiv.sum_comp σ w]
  ring

end Main

section MainField

variable {F : Type*} [Field F] {hh : ℕ}

/-- **Lemma 4.2** (p. 12), (4.13), in full.

`A, L` are `h × h` matrices over a valued field; `v(A_ij) ≥ w_i + w_j` with the `w_i` nonpositive
half-integers; `L` is integral of rank at most `r`; exactly `z` of the weights vanish.  Then

    v det(A + p^{-1} L) ≥ 2 ∑_i w_i - min(r, z).

`p^{-1}` appears only through an element `pinv` of valuation `≥ -1`. -/
theorem lemma_4_2 (V : ValFil F) (w : Fin hh → ℚ)
    (hw0 : ∀ i, w i ≤ 0) (hwhalf : ∀ i, ∃ k : ℤ, w i = (k : ℚ) / 2)
    (A L : Matrix (Fin hh) (Fin hh) F)
    (hA : ∀ i j, V.vge (A i j) (w i + w j))
    (pinv : F) (hpinv : V.vge pinv (-1))
    (hL : ∀ i j, V.vge (L i j) 0)
    (r : ℕ) (hrank : L.rank ≤ r)
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
  · rw [mixCol_det_eq_zero A L pinv hrank t hbig]
    exact V.vge_zero _
  rw [Nat.not_lt] at hbig
  rw [Matrix.det_apply']
  refine V.vge_sum _ _ _ fun σ _ => ?_
  refine V.vge_intUnit_mul ?_
  -- the Leibniz bound for one permutation
  have hprod : V.vge (∏ i, mixCol A (pinv • L) t (σ i) i)
      (∑ i, if i ∈ t then w (σ i) + w i else (-1 : ℚ)) := by
    refine V.vge_prod _ _ _ fun i _ => ?_
    by_cases hi : i ∈ t
    · simp only [mixCol_apply, hi, ite_true]; exact hA _ _
    · simp only [mixCol_apply, hi, ite_false]; exact hB _ _
  refine V.vge_mono ?_ hprod
  -- the arithmetic: the exponent of the term is `2∑w - (|S| + ∑_{σ(S)} w + ∑_S w)`
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

end MainField

/-! ## The Gauss-valuation form, for Proposition 4.1

"The same assertion holds for the Gauss valuation of polynomial entries" (p. 12).  For `r = 0`
— the case §4.1 uses, where the local basis (4.11) is unimodular and there is no `p^{-1}L`
correction — this is a statement about `Zeta5.vGAtLeast` directly.  `γ_p^in` of (4.8) is
literally `2 ∑_a ∑_i w_{a,i}`, so the bound below is the shape Proposition 4.1 asserts. -/

/-- **Lemma 4.2 for the Gauss valuation, `r = 0`.**  If every entry of the `h × h` matrix `G`
over `ℚ[X]` satisfies `v_p^G(G_ij) ≥ (W i + W j)/2` — the weights are half-integers, carried as
the integers `W = 2w` exactly as in `Zeta5.InnerAlloc.w2` — then
`v_p^G(det G) ≥ ∑_i W i`, i.e. `≥ 2 ∑_i w_i`. -/
theorem lemma_4_2_rank_zero_gauss (p : ℕ) [Fact p.Prime] {hh : ℕ} (W : Fin hh → ℤ)
    (G : Matrix (Fin hh) (Fin hh) ℚ[X])
    (hG : ∀ i j, (gaussFil p).vge (G i j) ((W i + W j : ℤ) / 2 : ℚ)) :
    vGAtLeast p G.det (∑ i, W i) := by
  classical
  have h := lemma_4_2_rank_zero (gaussFil p) (fun i => ((W i : ℚ)) / 2) G (by
    intro i j
    have := hG i j
    refine (gaussFil p).vge_mono (le_of_eq ?_) this
    push_cast
    ring)
  have hval : 2 * ∑ i, ((W i : ℚ) / 2) = ((∑ i, W i : ℤ) : ℚ) := by
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => by ring
  rw [hval] at h
  exact (gaussGe_intCast p G.det (∑ i, W i)).1 h

/-! ## Concrete `2`-adic computations

Shared by the counterexample and by the sharpness control below.  (`Nat.fact_prime_two` supplies
the `Fact (Nat.Prime 2)` instance.) -/

section Concrete

/-- `v_2(1/2) = -1`. -/
lemma padicValRat_two_half : padicValRat 2 (1 / 2 : ℚ) = -1 := by
  have hc : ((2 : ℕ) : ℚ) = (2 : ℚ) := by norm_num
  have hp2 : padicValRat 2 (2 : ℚ) = 1 := by
    rw [← hc]; exact padicValRat.self (by norm_num)
  rw [one_div, padicValRat.inv, hp2]

/-- `v_2(9/4) = -2`. -/
lemma padicValRat_two_nineQuarters : padicValRat 2 (9 / 4 : ℚ) = -2 := by
  have h9 : (9 : ℚ) ≠ 0 := by norm_num
  have h4 : (4 : ℚ) ≠ 0 := by norm_num
  rw [show (9 / 4 : ℚ) = (9 : ℚ) / (4 : ℚ) by norm_num, padicValRat.div h9 h4]
  have e9 : padicValRat 2 (9 : ℚ) = 0 := by
    have hc : ((9 : ℕ) : ℚ) = (9 : ℚ) := by norm_num
    rw [← hc, padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd (by decide)]
    rfl
  have e4 : padicValRat 2 (4 : ℚ) = 2 := by
    have hc : ((4 : ℕ) : ℚ) = (4 : ℚ) := by norm_num
    rw [← hc, padicValRat.of_nat, show (4 : ℕ) = 2 ^ 2 by norm_num, padicValNat.prime_pow]
    rfl
  rw [e9, e4]
  norm_num

/-- Every entry of the `2 × 2` identity matrix over `ℚ` has `2`-adic valuation `≥ c` for any
`c ≤ 0`: the diagonal entries are `1` (valuation `0`) and the rest are `0`. -/
lemma padicFil_two_one_entries (c : ℚ) (hc : c ≤ 0) (i j : Fin 2) :
    (padicFil 2).vge ((1 : Matrix (Fin 2) (Fin 2) ℚ) i j) c := by
  by_cases hij : i = j
  · subst hij
    refine Or.inr ?_
    simp only [Matrix.one_apply_eq, padicValRat.one]
    simpa using hc
  · exact Or.inl (Matrix.one_apply_ne hij)

/-- `det (I + (1/2) I) = (3/2)² = 9/4` for `2 × 2` matrices over `ℚ`. -/
lemma det_one_add_half_smul_one :
    ((1 : Matrix (Fin 2) (Fin 2) ℚ) + (1 / 2 : ℚ) • 1).det = 9 / 4 := by
  have hM : ((1 : Matrix (Fin 2) (Fin 2) ℚ) + (1 / 2 : ℚ) • 1) = !![3 / 2, 0; 0, 3 / 2] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.smul_apply] <;> norm_num
  rw [hM, Matrix.det_fin_two_of]
  norm_num

/-- `Matrix.rank L ≤ 2` for every `2 × 2` matrix. -/
lemma rank_le_two (L : Matrix (Fin 2) (Fin 2) ℚ) : L.rank ≤ 2 :=
  le_trans (Matrix.rank_le_card_width _) (by simp)

end Concrete

/-! ## The half-integrality hypothesis cannot be dropped

A machine-checked witness.  Take `p = 2`, `h = 2`, `w = (-1/4, -1/4)`, `A = L = I`,
`pinv = 1/2`, `r = 2`.  Every hypothesis of `lemma_4_2` holds **except** that `-1/4` is not a
half-integer; `z = 0`, so the claimed bound would be `2(-1/4-1/4) - min(2,0) = -1`, while

    det (A + 2^{-1} L) = (3/2)² = 9/4,     v_2(9/4) = -2 < -1.

The mechanism is exactly the one the paper's proof relies on: the loss `k + 2∑_{i≤k} w_(i)`
has increment `1 + 2w_(k)`, which is `≤ 0` for a nonzero half-integer weight but `+1/2` for
`w = -1/4`, so at `k = 2` the loss is `+1` and the maximum is no longer `min(r,z) = 0`.
(The audit's random search found the same failure at `p = 11`, `h = 3`,
`w = (-3/2,-1/4,-3/2)`, `r = 1`: claimed bound `-13/2`, true valuation `-7`.)

Compare `lemma_4_2_attained` below: the *same* `A`, `L`, `pinv` with the half-integer weights
`w = (-1/2,-1/2)` satisfy Lemma 4.2 with equality. -/
theorem lemma_4_2_needs_half_integers :
    ∃ (w : Fin 2 → ℚ) (A L : Matrix (Fin 2) (Fin 2) ℚ) (pinv : ℚ) (r z : ℕ),
      -- every hypothesis of `lemma_4_2` except half-integrality:
      (∀ i, w i ≤ 0)
      ∧ (∀ i j, (padicFil 2).vge (A i j) (w i + w j))
      ∧ (padicFil 2).vge pinv (-1)
      ∧ (∀ i j, (padicFil 2).vge (L i j) 0)
      ∧ L.rank ≤ r
      ∧ z = (Finset.univ.filter (fun i => w i = 0)).card
      -- half-integrality fails:
      ∧ (¬ ∀ i, ∃ k : ℤ, w i = (k : ℚ) / 2)
      -- and so does the conclusion (4.13):
      ∧ ¬ (padicFil 2).vge (A + pinv • L).det (2 * ∑ i, w i - ((min r z : ℕ) : ℚ)) := by
  classical
  refine ⟨fun _ => -(1 / 4), 1, 1, 1 / 2, 2, 0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; norm_num
  · exact fun i j => padicFil_two_one_entries _ (by norm_num) i j
  · exact Or.inr (by rw [padicValRat_two_half]; norm_num)
  · exact fun i j => padicFil_two_one_entries _ le_rfl i j
  · exact rank_le_two _
  · symm
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro i _
    norm_num
  · intro hcon
    obtain ⟨k, hk⟩ := hcon 0
    have hk2 : (2 * k : ℤ) = -1 := by
      have : ((2 * k : ℤ) : ℚ) = -1 := by push_cast; linarith
      exact_mod_cast this
    omega
  · rw [det_one_add_half_smul_one]
    intro hcon
    rcases hcon with h0 | h0
    · norm_num at h0
    · rw [padicValRat_two_nineQuarters] at h0
      norm_num at h0

/-- **Known-answer control: `lemma_4_2` applies, and its bound is sharp.**

The same `p = 2`, the same matrices `A = L = I` and the same `p^{-1} = 1/2` as in
`lemma_4_2_needs_half_integers`, but with the *half-integer* weights `w = (-1/2, -1/2)`.  Now
every hypothesis holds, `lemma_4_2` applies, and the bound it delivers,
`2∑w - min(r,z) = -2`, equals the true valuation `v_2(det) = v_2(9/4) = -2`.

Two things are checked at once: that the hypotheses of `lemma_4_2` are satisfiable (so the
theorem is not vacuous) and that (4.13) cannot be improved.  This matches the audit's finding
that in 6000 random trials the minimum observed slack was `0`. -/
theorem lemma_4_2_attained :
    (padicFil 2).vge (((1 : Matrix (Fin 2) (Fin 2) ℚ) + (1 / 2 : ℚ) • 1).det)
        (2 * ∑ _i : Fin 2, (-(1 / 2) : ℚ) - ((min 2 0 : ℕ) : ℚ))
      ∧ 2 * ∑ _i : Fin 2, (-(1 / 2) : ℚ) - ((min 2 0 : ℕ) : ℚ) = -2
      ∧ padicValRat 2 (((1 : Matrix (Fin 2) (Fin 2) ℚ) + (1 / 2 : ℚ) • 1).det) = -2 := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · refine lemma_4_2 (padicFil 2) (fun _ => -(1 / 2)) (fun _ => by norm_num)
      (fun _ => ⟨-1, by norm_num⟩) 1 1 (fun i j => padicFil_two_one_entries _ (by norm_num) i j)
      (1 / 2) (Or.inr (by rw [padicValRat_two_half]; norm_num))
      (fun i j => padicFil_two_one_entries _ le_rfl i j) 2 (rank_le_two _) 0 ?_
    symm
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro i _
    norm_num
  · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    norm_num
  · rw [det_one_add_half_smul_one, padicValRat_two_nineQuarters]

/-! ## `#print axioms`

The results of this file must depend on nothing but `propext`, `Classical.choice`, `Quot.sound`;
in particular no `sorryAx`. -/

#print axioms Zeta5.lemma_4_2
#print axioms Zeta5.lemma_4_2_rank_zero
#print axioms Zeta5.lemma_4_2_rank_zero_gauss
#print axioms Zeta5.lemma_4_2_needs_half_integers
#print axioms Zeta5.lemma_4_2_attained
#print axioms Zeta5.det_add_eq_sum_mixCol
#print axioms Zeta5.mixCol_det_eq_zero
#print axioms Zeta5.loss_le
#print axioms Zeta5.gaussGe_intCast

end

end Zeta5
