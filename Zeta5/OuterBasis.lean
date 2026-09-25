/-
Zeta5/OuterBasis.lean

**The local analysis of §4.2 (pp. 11–12): the basis (4.11), the splitting (4.10), and the entry
bounds behind the weights (4.12).**  This file proves `Zeta5.outer_local_analysis`
(`OuterRange.lean`), as `Zeta5.OuterBasis.outer_local_core`; `OuterRange.lean` imports this file
and applies `outer_local_core` with `outerDim`, `outerWeight` (definitionally `dimO`, `wtO`
below, by `rfl`) and `outerRows_card`.

THIS FILE CONTAINS NO `sorry` AND NO `axiom`.  `#print axioms Zeta5.OuterBasis.outer_local_core`
is `[propext, Classical.choice, Quot.sound]`: the shared lemma
`Zeta5.HermiteBasis.det_coeffMatrix_unimodular` it uses is itself proved.

## The paper's argument, and where each step is

The hypotheses are `Zeta5.OuterHyp` ((4.9) without `p ≤ K`), carried here as `Hyp` plus
`[Fact p.Prime]`; they are used only through `p ≥ 7`, `K < 3p`, `2K < p²`, `2N < p`,
`5N ≤ 2p − 2`.  Nothing uses `K ≥ 200M²`.

* **Classes (§1).**  `cls p r ∈ [0, (p−1)/2]` is the class of `r` (`r ≡ ±cls r`); `Tset c` are
  the tail poles `N < r ≤ K` of class `c` (the "remaining" poles), `Pset a` the tail poles
  outside class `a` (roots of `P_a = D_tail/Q_a`), `Eset a` the poles of class `a` above `p`
  (roots of `E_a`), `Cset a` those `≤ p`.  Proved: `card_Tset` (`|T_c| = m_K` for `c = 0`,
  `ℓ_K(c) − δ_c` otherwise — "There are `ℓ − δ` remaining poles in the class"), `card_Eset`
  ("exactly `ℓ − 2` of the original poles have `j > p`"), `Cset_subset` (the survivors of
  `E_a` are among `a, p − a`), `Tset_zero_one`/`Tset_zero_two` (the zero class is `{p}` or
  `{p, 2p}`).
* **Rows (§2).**  `rowR R n p a i = P_a · q_{a,i}` over any commutative ring `R`, with
  `q_{a,i} = (t+a²)^i` for `i < ℓ−2`, `E_a (t+a²)^{i−(ℓ−2)}` otherwise (4.11), and the
  zero-class rows `P_0·1`, `P_0·(t+p²)` (p. 12).  `rowR_hermite'`: modulo `p` the row `(a,i)`
  is exactly `hermitePoly (c ↦ c²) dimO a i` — the tail factors regroup by class, `E_a ≡ (t+a²)^{ℓ−2}`
  and `t + p² ≡ t`.  With `HermiteBasis.det_coeffMatrix_unimodular` this is "Together with the
  zero-class rows, these form a unimodular basis".
* **The moments (§3).**  `muMono_vge_neg_one` (`v_p(μ(t^e)) ≥ −1`, von Staudt–Clausen),
  `muMono_int_small` (`μ(t^e) ∈ ℤ_p` for `e < 2p−3`: "if `p − 1` divides `2e + 2`, the first
  three possible multiples of `p − 1` are canceled respectively by the factors `2e + 3, 2e + 4,
  2e + 5`", `p_dvd_three_factors`), `exists_int_approx`, and `mu0_int`: with the integers
  `c_e` of `cCoef` (`c_e = 0` for `e < 2p−3`), `μ_0(t^e) = μ(t^e) − c_e/p ∈ ℤ_p` for every `e`.
* **The splitting (4.10) (§3, §5).**  `muOver = muOver0 + p^{-1}·muL` (`muOver_split`), hence
  `Gram(U) = A + p^{-1}L` (`Gram_split`).  `L = U L_0 Uᵀ` (`Lq_eq`); in the monomial basis
  `L_0[i,j] = 0` for `i + j < K − 6N + 2p − 3` (`L0_eq_zero`: "the polynomial quotient of
  `W t^{i+j}/D_tail` has degree at most `i + j + 6N − K`"), so its first `h − r_p` columns
  vanish and `rank L ≤ rank L_0 ≤ r_p` (`rank_L0`, `rank_Lq`), the rank taken in `ℚ(X)`.
  `L` is integral (`muL_int`).
* **The entry bounds (§4, §6–§8).**  Every entry of `A` in the basis is
  `C(poly part) + resSum`; the polynomial part is integral (`polyPart_int`: the quotient by the
  monic integer `D_tail` has integer coefficients and every `μ_0(t^e)` is integral).  The residue
  part is computed by `resSum_formula` (partial fractions of `F/∏_{r∈S}(t+r²)`) and bounded case
  by case, exactly as on p. 12:
  - `resSum_cross`: cross-class entries have no residues ("their quotients are polynomials with
    integral coefficients");
  - `resSum_2a`: both indices `< ℓ−2`: valuation `≥ i + j + 6δ − ℓ − 4` — the row factors give
    `i + j`, `W` gives `5δ` (`vge_W_eval`), the node derivative loses exactly `ℓ − δ − 1`
    (`val_node_derivative`, from `v_p(s² − r²) = 1`, `val_sq_sub_sq`, which uses `p² > 2K`),
    and a pole value loses at most `5` (`muPole_vge_neg_five`);
  - `resSum_2b`: a row index `≥ ℓ − 2`: the poles `j > p` cancel and what is left is the divided
    difference at `a, p − a` (`pairSum_vge`), integral by `OuterLocal.muPole_divided_difference`
    (which needs the `−1/4 + 1/(2j)` tail of (2.3), the audit's finding) together with
    `(F(x) − F(y))/(x − y) ∈ ℤ` for integer `F` ("Polynomial numerators preserve this
    congruence");
  - `resSum_zero`: the zero class: one pole — weight `−1/2`; two poles `p, 2p` with rows
    `1, t + p²` — entry bounds `−3, −1, 0` (valuations `v_p(3p²) = 2`, `v_p^G(μ(1/(t+r²))) ≥ −1`
    for `p ∣ r`), so the weights `−2, 0` are valid.
  `entry_bound` assembles these into `v_p^G(A_{uv}) ≥ w_u + w_v` for the weights (4.12).
* **Assembly (§9).**  `outer_local_core`.

## Known-answer controls (exact arithmetic)

`numerics/outerbasis/ob_control.sage` rebuilds, with *the definitions of
this file* (`cls`, `Tset`, `Eset`, `dimO`, the rows, `c_e`, `muOver0`, `muL`), every intermediate
statement of the decomposition and checks it exactly: the counts, the reduction mod `p` to the
Hermite basis, `v_p(det U) = 0`, `μ_0` integral, the three `muPole` bounds, the residue formula,
each of the four entry-bound cases separately and the final bound `v_p^G(A_{uv}) ≥ w_u + w_v`
(all `h(h+1)/2` entries), `L_0` zero pattern, `L = U L_0 Uᵀ`, and `rank L ≤ r_p`.  Results:
0 failures at `K = 40` (`p = 17, 19, 23, 29, 31, 37` and `p = 41, 43 > K`), at `K = 80`
(all 13 primes of (4.9) and `p = 83 > K`) and at `K = 120` (`p = 41, 43, 61, 113, 127`);
`rank L = r_p` exactly wherever computed.  MUST-FAIL control
(`numerics/outerbasis/ob_mustfail.sage`): deleting the `+1/(2j)` of (2.3) makes the
divided-difference case fail (13 failures at `K = 40`,
`p = 17, 23`), so the checks are not vacuous.
-/
import Zeta5.OuterLocal
import Zeta5.HermiteBasis
import Zeta5.Arithmetic

namespace Zeta5

namespace OuterBasis

open Polynomial Finset

noncomputable section

/-! # §0.  The hypotheses (4.9) minus `p ≤ K` (the fields of `Zeta5.OuterHyp` other than
primality, which is carried as a `Fact`). -/

/-- `OuterHyp` without its primality field. -/
structure Hyp (n p : ℕ) : Prop where
  ge7 : 7 ≤ p
  upper : K n < 3 * p
  sq : 2 * K n < p ^ 2
  twoN : 2 * N n < p
  fiveN : 5 * N n ≤ 2 * p - 2

/-! # §1.  Square classes, the tail poles, and the counts -/

/-- The square class of `r` modulo `p`: the unique `c ∈ [0, (p−1)/2]` with `r ≡ ±c (mod p)`. -/
def cls (p r : ℕ) : ℕ := if r % p ≤ mHalf p then r % p else p - r % p

/-- The tail poles `N < r ≤ K` (the roots `−r²` of `D_tail`). -/
def tail (n : ℕ) : Finset ℕ := Ioc (N n) (K n)

/-- The tail poles of class `c`: the "remaining" poles of the class. -/
def Tset (n p c : ℕ) : Finset ℕ := (tail n).filter (fun r => cls p r = c)

/-- The tail poles outside the class `a`: the roots of `P_a = D_tail/Q_a`. -/
def Pset (n p a : ℕ) : Finset ℕ := (tail n).filter (fun r => cls p r ≠ a)

/-- The poles of class `a` with `j > p`: the roots of `E_a`. -/
def Eset (n p a : ℕ) : Finset ℕ := (Tset n p a).filter (fun r => p < r)

/-- The poles of class `a` with `j ≤ p`: those that survive `E_a`. -/
def Cset (n p a : ℕ) : Finset ℕ := (Tset n p a).filter (fun r => ¬ p < r)

/-- The number of rows of the class `a`: `m_K` for the zero class, `ℓ_K(a) − δ_a` otherwise.
(This is `Zeta5.outerDim`, unfolded.) -/
def dimO (n p a : ℕ) : ℕ :=
  if a = 0 then mFloor p (K n) else ell p (K n) a - (if a ≤ N n then 1 else 0)

/-- The doubled weight (4.12) of the row `(a, i)` (this is `Zeta5.outerWeight`, unfolded). -/
def wtO (n p a i : ℕ) : ℤ :=
  if a = 0 then (if mFloor p (K n) ≤ 1 then -1 else if i = 0 then -4 else 0)
  else if i + 2 < ell p (K n) a then
    min 0 (2 * (i : ℤ) + 6 * (((if a ≤ N n then 1 else 0 : ℕ)) : ℤ) - (ell p (K n) a : ℤ) - 4)
  else 0

/-! # §2.  The rows (4.11), over any commutative ring -/

section Rows

variable (R : Type*) [CommRing R]

/-- The linear factor `t + x²`. -/
def linR (x : ℕ) : R[X] := X + C ((x : R) ^ 2)

/-- `∏_{r ∈ s} (t + r²)`. -/
def prodR (s : Finset ℕ) : R[X] := ∏ r ∈ s, linR R r

/-- The local polynomial `q_{a,i}` of (4.11), and the zero-class rows `1, t + p²`. -/
def qR (n p a i : ℕ) : R[X] :=
  if a = 0 then (if i = 0 then 1 else linR R p)
  else if i + 2 < ell p (K n) a then linR R a ^ i
  else prodR R (Eset n p a) * linR R a ^ (i - (ell p (K n) a - 2))

/-- The row `P_a q_{a,i}` of (4.11). -/
def rowR (n p a i : ℕ) : R[X] := prodR R (Pset n p a) * qR R n p a i

end Rows

/-! # §3.  The splitting (4.10) of the functional -/

/-- `∑_e P_e w_e`: the polynomial part of `μ` with moment sequence `w`. -/
def muPolyW (w : ℕ → ℚ) (P : ℚ[X]) : ℚ := ∑ e ∈ P.support, P.coeff e * w e

/-- The integers `c_e` of p. 11: `c_e ≡ pμ(t^e) (mod p)`, `c_e = 0` for `e < 2p − 3`. -/
def cCoef (p e : ℕ) : ℤ :=
  if e < 2 * p - 3 then 0
  else Classical.epsilon (fun c : ℤ => padicGe p (muMono e - (c : ℚ) / p) 0)

/-- `μ_0(t^e) = μ(t^e) − c_e/p`. -/
def mu0 (p e : ℕ) : ℚ := muMono e - (cCoef p e : ℚ) / p

/-- The functional of the matrix `A` of (4.10): polynomial moments replaced by `μ_0`, the
simple-pole values unchanged. -/
def muOver0 (n p : ℕ) (A : ℚ[X]) : ℚ[X] :=
  C (muPolyW (mu0 p) (A /ₘ Dtail n)) + ∑ r ∈ Ioc (N n) (K n), C (residue n A r) * muPole r

/-- The functional of the matrix `L` of (4.10): `∑_e c_e [t^e](A /ₘ D_tail)`. -/
def muL (n p : ℕ) (A : ℚ[X]) : ℚ[X] := C (muPolyW (fun e => (cCoef p e : ℚ)) (A /ₘ Dtail n))

/-- The matrix `A` of (4.10) in the basis with rows `U`. -/
def Aq (n p : ℕ) (U : Matrix (Fin (h n)) (Fin (h n)) ℚ) : Matrix (Fin (h n)) (Fin (h n)) ℚ[X] :=
  Matrix.of fun u v =>
    muOver0 n p ((D (N n)) ^ 5 * (OuterLocal.rowPoly U u * OuterLocal.rowPoly U v))

/-- The matrix `L` of (4.10) in the basis with rows `U`. -/
def Lq (n p : ℕ) (U : Matrix (Fin (h n)) (Fin (h n)) ℚ) : Matrix (Fin (h n)) (Fin (h n)) ℚ[X] :=
  Matrix.of fun u v =>
    muL n p ((D (N n)) ^ 5 * (OuterLocal.rowPoly U u * OuterLocal.rowPoly U v))

/-- The matrix `L` of (4.10) in the monomial basis. -/
def L0 (n p : ℕ) : Matrix (Fin (h n)) (Fin (h n)) ℚ[X] :=
  Matrix.of fun i j => muL n p ((D (N n)) ^ 5 * (X ^ (i : ℕ) * X ^ (j : ℕ)))

/-! # §1 (proofs).  Classes and counts -/

section ClassLemmas

variable {n p : ℕ}

lemma Hyp.pos (hp : Hyp n p) : 0 < p := by have := hp.ge7; omega

lemma Hyp.two_mHalf [hpr : Fact p.Prime] (hp : Hyp n p) : 2 * mHalf p + 1 = p := by
  have hodd : Odd p := hpr.out.odd_of_ne_two (by have := hp.ge7; omega)
  obtain ⟨k, hk⟩ := hodd
  unfold mHalf; omega

lemma Hyp.N_lt (hp : Hyp n p) : N n < p := by have := hp.twoN; omega

lemma Hyp.N_le_mHalf [Fact p.Prime] (hp : Hyp n p) : N n ≤ mHalf p := by
  have := hp.two_mHalf; have := hp.twoN; omega

lemma N_le_K (n : ℕ) : N n ≤ K n := by simp only [N, K]; omega

lemma cls_le (hm : 2 * mHalf p + 1 = p) (r : ℕ) : cls p r ≤ mHalf p := by
  have := Nat.mod_lt r (show 0 < p by omega)
  unfold cls; split_ifs <;> omega

lemma cls_eq_zero_iff (hm : 2 * mHalf p + 1 = p) (r : ℕ) : cls p r = 0 ↔ p ∣ r := by
  have := Nat.mod_lt r (show 0 < p by omega)
  rw [Nat.dvd_iff_mod_eq_zero]; unfold cls; split_ifs <;> omega

lemma cls_eq_iff (hm : 2 * mHalf p + 1 = p) {c : ℕ} (hc1 : 1 ≤ c) (hcm : c ≤ mHalf p) (r : ℕ) :
    cls p r = c ↔ (r % p = c ∨ r % p = p - c) := by
  have := Nat.mod_lt r (show 0 < p by omega)
  unfold cls; split_ifs <;> omega

lemma cls_of_le (hm : 2 * mHalf p + 1 = p) {r : ℕ} (hr : r ≤ mHalf p) : cls p r = r := by
  have h : r % p = r := Nat.mod_eq_of_lt (by omega)
  unfold cls; rw [h]; simp [hr]

lemma cls_sub (hm : 2 * mHalf p + 1 = p) {a : ℕ} (ha1 : 1 ≤ a) (ha : a ≤ mHalf p) :
    cls p (p - a) = a := by
  have h : (p - a) % p = p - a := Nat.mod_eq_of_lt (by omega)
  unfold cls; rw [h]; split_ifs <;> omega

/-- `r ≡ ±cls(r)`, so the squares agree modulo `p`. -/
lemma cls_sq (hm : 2 * mHalf p + 1 = p) (r : ℕ) :
    ((r : ZMod p)) ^ 2 = (((cls p r : ℕ) : ZMod p)) ^ 2 := by
  have hr : ((r : ZMod p)) = (((r % p : ℕ) : ZMod p)) := (ZMod.natCast_mod r p).symm
  have hlt := Nat.mod_lt r (show 0 < p by omega)
  unfold cls
  split_ifs with h
  · rw [hr]
  · rw [hr, Nat.cast_sub hlt.le, ZMod.natCast_self]
    ring

/-- Two numbers of the same class have squares congruent modulo `p`. -/
lemma dvd_sq_sub_sq (hm : 2 * mHalf p + 1 = p) {r s : ℕ} (hrs : cls p r = cls p s) :
    (p : ℤ) ∣ (s : ℤ) ^ 2 - (r : ℤ) ^ 2 := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [cls_sq hm s, cls_sq hm r, hrs, sub_self]

lemma add_mod_eq_zero_iff (hp0 : 0 < p) {j a : ℕ} (ha1 : 1 ≤ a) (hap : a < p) :
    (j + a) % p = 0 ↔ j % p = p - a := by
  have h1 : (j + a) % p = (j % p + a) % p := by rw [Nat.add_mod, Nat.mod_eq_of_lt hap]
  have hr := Nat.mod_lt j hp0
  rw [h1]
  by_cases hlt : j % p + a < p
  · rw [Nat.mod_eq_of_lt hlt]; omega
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega

/-- `ℓ_A(a)` counts the `j ≤ A` of class `a`. -/
lemma ell_eq_card_cls (hm : 2 * mHalf p + 1 = p) (A : ℕ) {a : ℕ} (ha1 : 1 ≤ a)
    (ha : a ≤ mHalf p) : ell p A a = ((Icc 1 A).filter (fun j => cls p j = a)).card := by
  unfold ell
  congr 1
  refine Finset.filter_congr fun j _ => ?_
  have hap : a < p := by omega
  rw [Nat.mod_eq_of_lt hap, add_mod_eq_zero_iff (by omega) ha1 hap, cls_eq_iff hm ha1 ha]

lemma mem_Tset {c r : ℕ} : r ∈ Tset n p c ↔ (N n < r ∧ r ≤ K n) ∧ cls p r = c := by
  simp [Tset, tail]

lemma mem_Pset {a r : ℕ} : r ∈ Pset n p a ↔ (N n < r ∧ r ≤ K n) ∧ cls p r ≠ a := by
  simp [Pset, tail]

lemma Pset_eq_sdiff (a : ℕ) : Pset n p a = tail n \ Tset n p a := by
  ext r
  simp only [Pset, Tset, Finset.mem_filter, Finset.mem_sdiff]
  tauto

lemma Tset_subset_tail (c : ℕ) : Tset n p c ⊆ tail n := Finset.filter_subset _ _

/-- **The class counts**: the class `c` has exactly `dimO c` tail poles. -/
lemma card_Tset [Fact p.Prime] (hp : Hyp n p) {c : ℕ} (hc : c ≤ mHalf p) :
    (Tset n p c).card = dimO n p c := by
  have hm := hp.two_mHalf
  have hNp := hp.N_lt
  rcases Nat.eq_zero_or_pos c with rfl | hc1
  · -- the zero class: the multiples of `p` in `(N, K]`, all of which are `> N`
    simp only [dimO, ite_true, mFloor]
    rw [← Nat.Ioc_filter_dvd_card_eq_div]
    congr 1
    ext r
    simp only [Tset, tail, Finset.mem_filter, Finset.mem_Ioc, cls_eq_zero_iff hm]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨by omega, h2⟩, h3⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      have := Nat.le_of_dvd h1 h3
      exact ⟨⟨by omega, h2⟩, h3⟩
  · have hdim : dimO n p c = ell p (K n) c - (if c ≤ N n then 1 else 0) := by
      simp [dimO, Nat.pos_iff_ne_zero.1 hc1]
    rw [hdim, ell_eq_card_cls hm (K n) hc1 hc]
    have hsplit : (Icc 1 (K n)).filter (fun j => cls p j = c)
        = (Icc 1 (N n)).filter (fun j => cls p j = c) ∪ Tset n p c := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_union, Tset, tail,
        Finset.mem_Ioc]
      have := N_le_K n
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        by_cases hj : j ≤ N n
        · exact Or.inl ⟨⟨h1, hj⟩, h3⟩
        · exact Or.inr ⟨⟨by omega, h2⟩, h3⟩
      · rintro (⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩)
        · exact ⟨⟨h1, by omega⟩, h3⟩
        · exact ⟨⟨by omega, h2⟩, h3⟩
    have hdisj : Disjoint ((Icc 1 (N n)).filter (fun j => cls p j = c)) (Tset n p c) := by
      rw [Finset.disjoint_left]
      intro j hj1 hj2
      simp only [Finset.mem_filter, Finset.mem_Icc] at hj1
      rw [mem_Tset] at hj2
      omega
    have hsmall : ((Icc 1 (N n)).filter (fun j => cls p j = c)).card
        = (if c ≤ N n then 1 else 0) := by
      have hNm := hp.N_le_mHalf
      split_ifs with hcN
      · rw [Finset.card_eq_one]
        refine ⟨c, ?_⟩
        ext j
        simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton]
        constructor
        · rintro ⟨⟨h1, h2⟩, h3⟩
          rw [cls_of_le hm (by omega)] at h3
          exact h3
        · rintro rfl
          exact ⟨⟨hc1, hcN⟩, cls_of_le hm hc⟩
      · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro j hj
        simp only [Finset.mem_Icc] at hj
        rw [cls_of_le hm (by omega)]
        omega
    rw [hsplit, Finset.card_union_of_disjoint hdisj, hsmall]
    omega

/-- The number of poles of class `a` above `p` is `ℓ − 2` (truncated). -/
lemma card_Eset [Fact p.Prime] (hp : Hyp n p) {a : ℕ} (ha1 : 1 ≤ a) (ha : a ≤ mHalf p) :
    (Eset n p a).card = ell p (K n) a - 2 := by
  have hm := hp.two_mHalf
  have hNp := hp.N_lt
  rw [ell_eq_card_cls hm (K n) ha1 ha]
  set F := (Icc 1 (K n)).filter (fun j => cls p j = a) with hF
  have hsplit := Finset.card_filter_add_card_filter_not (s := F) (fun j => p < j)
  have hE : F.filter (fun j => p < j) = Eset n p a := by
    ext j
    simp only [hF, Eset, Tset, tail, Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩; exact ⟨⟨⟨by omega, h2⟩, h3⟩, h4⟩
    · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩; exact ⟨⟨⟨by omega, h2⟩, h3⟩, h4⟩
  have hsub : F.filter (fun j => ¬ p < j) ⊆ {a, p - a} := by
    intro j hj
    simp only [hF, Finset.mem_filter, Finset.mem_Icc] at hj
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hj
    have hjp : j ≠ p := by
      rintro rfl
      have := (cls_eq_zero_iff hm j).2 (dvd_refl _)
      omega
    have hmod : j % p = j := Nat.mod_eq_of_lt (by omega)
    rw [cls_eq_iff hm ha1 ha, hmod] at h3
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact h3
  rw [hE] at hsplit
  by_cases hpK : p ≤ K n
  · have hfull : F.filter (fun j => ¬ p < j) = {a, p - a} := by
      refine Finset.Subset.antisymm hsub ?_
      intro j hj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj
      simp only [hF, Finset.mem_filter, Finset.mem_Icc]
      rcases hj with rfl | rfl
      · exact ⟨⟨⟨ha1, by omega⟩, cls_of_le hm ha⟩, by omega⟩
      · exact ⟨⟨⟨by omega, by omega⟩, cls_sub hm ha1 ha⟩, by omega⟩
    have h2 : ({a, p - a} : Finset ℕ).card = 2 := Finset.card_pair (by omega)
    rw [hfull, h2] at hsplit
    omega
  · have hE0 : Eset n p a = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro j hj
      simp only [Eset, Tset, tail, Finset.mem_filter, Finset.mem_Ioc] at hj
      omega
    have hle : (F.filter (fun j => ¬ p < j)).card ≤ 2 :=
      le_trans (Finset.card_le_card hsub) (Finset.card_le_two)
    rw [hE0, Finset.card_empty] at hsplit ⊢
    omega

/-- The poles of class `a` that survive `E_a` are among `a` and `p − a`. -/
lemma Cset_subset [Fact p.Prime] (hp : Hyp n p) {a : ℕ} (ha1 : 1 ≤ a) (ha : a ≤ mHalf p) :
    Cset n p a ⊆ {a, p - a} := by
  have hm := hp.two_mHalf
  intro j hj
  simp only [Cset, Tset, tail, Finset.mem_filter, Finset.mem_Ioc] at hj
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hj
  have hjp : j ≠ p := by
    rintro rfl
    have := (cls_eq_zero_iff hm j).2 (dvd_refl _)
    omega
  have hmod : j % p = j := Nat.mod_eq_of_lt (by omega)
  rw [cls_eq_iff hm ha1 ha, hmod] at h3
  simp only [Finset.mem_insert, Finset.mem_singleton]
  exact h3

lemma mem_Cset_of {a r : ℕ} (hr : r ∈ Cset n p a) :
    1 ≤ r ∧ r ≤ p := by
  simp only [Cset, Tset, tail, Finset.mem_filter, Finset.mem_Ioc] at hr
  omega

/-- The zero class when `m_K = 1`: the single pole `p`. -/
lemma Tset_zero_one [Fact p.Prime] (hp : Hyp n p) (h1 : mFloor p (K n) = 1) :
    Tset n p 0 = {p} := by
  have hm := hp.two_mHalf
  have hNp := hp.N_lt
  have hp0 := hp.pos
  have hK : p ≤ K n ∧ K n < 2 * p := by
    unfold mFloor at h1
    constructor
    · by_contra hcon
      rw [Nat.div_eq_of_lt (by omega)] at h1
      omega
    · by_contra hcon
      have : 2 ≤ K n / p := (Nat.le_div_iff_mul_le hp0).2 (by linarith)
      omega
  ext r
  rw [mem_Tset, cls_eq_zero_iff hm, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨h1, h2⟩, ⟨t, rfl⟩⟩
    have ht1 : 1 ≤ t := by
      rcases Nat.eq_zero_or_pos t with rfl | ht
      · simp at h1
      · exact ht
    have ht2 : t < 2 := by
      by_contra hcon
      have : p * 2 ≤ p * t := Nat.mul_le_mul_left p (by omega)
      omega
    have : t = 1 := by omega
    subst this; ring
  · rintro rfl
    exact ⟨⟨hNp, hK.1⟩, dvd_refl _⟩

/-- The zero class when `m_K = 2`: the two poles `p, 2p`. -/
lemma Tset_zero_two [Fact p.Prime] (hp : Hyp n p) (h2 : mFloor p (K n) = 2) :
    Tset n p 0 = {p, 2 * p} := by
  have hm := hp.two_mHalf
  have hNp := hp.N_lt
  have hp0 := hp.pos
  have hK : 2 * p ≤ K n := by
    unfold mFloor at h2
    by_contra hcon
    have : K n / p < 2 := (Nat.div_lt_iff_lt_mul hp0).2 (by linarith)
    omega
  have hK3 := hp.upper
  ext r
  rw [mem_Tset, cls_eq_zero_iff hm, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨h1, h2⟩, ⟨t, rfl⟩⟩
    have ht1 : 1 ≤ t := by
      rcases Nat.eq_zero_or_pos t with rfl | ht
      · simp at h1
      · exact ht
    have ht2 : t < 3 := by
      by_contra hcon
      have : p * 3 ≤ p * t := Nat.mul_le_mul_left p (by omega)
      omega
    interval_cases t
    · left; ring
    · right; ring
  · rintro (rfl | rfl)
    · exact ⟨⟨hNp, by omega⟩, dvd_refl _⟩
    · exact ⟨⟨by omega, hK⟩, dvd_mul_left _ _⟩

lemma mFloor_le_two (hp : Hyp n p) : mFloor p (K n) ≤ 2 := by
  have hp0 := hp.pos
  unfold mFloor
  have := hp.upper
  have : K n / p < 3 := (Nat.div_lt_iff_lt_mul hp0).2 (by linarith)
  omega

end ClassLemmas

/-! # §2 (proofs).  The rows: reduction, monicity, and the Hermite basis modulo `p` -/

section RowLemmas

variable {R : Type*} [CommRing R]

lemma linR_map {S : Type*} [CommRing S] (f : R →+* S) (x : ℕ) :
    (linR R x).map f = linR S x := by
  simp [linR]

lemma prodR_map {S : Type*} [CommRing S] (f : R →+* S) (s : Finset ℕ) :
    (prodR R s).map f = prodR S s := by
  simp [prodR, Polynomial.map_prod, linR_map]

lemma qR_map {S : Type*} [CommRing S] (f : R →+* S) (n p a i : ℕ) :
    (qR R n p a i).map f = qR S n p a i := by
  unfold qR
  split_ifs <;> simp [prodR_map, linR_map, Polynomial.map_mul, Polynomial.map_pow]

lemma linR_monic (x : ℕ) : (linR R x).Monic := monic_X_add_C _

lemma prodR_monic (s : Finset ℕ) : (prodR R s).Monic :=
  monic_prod_of_monic _ _ fun r _ => linR_monic r

lemma rowR_map' {S : Type*} [CommRing S] (f : R →+* S) (n p a i : ℕ) :
    (rowR R n p a i).map f = rowR S n p a i := by
  simp [rowR, Polynomial.map_mul, prodR_map, qR_map]

lemma qR_monic (n p a i : ℕ) : (qR R n p a i).Monic := by
  unfold qR
  split_ifs
  · exact monic_one
  · exact linR_monic _
  · exact (linR_monic _).pow _
  · exact (prodR_monic _).mul ((linR_monic _).pow _)

/-- A product of linear factors from a single class is a power, modulo `p`. -/
lemma prodR_zmod_of_cls {p : ℕ} (hm : 2 * mHalf p + 1 = p) (s : Finset ℕ) (c : ℕ)
    (hs : ∀ r ∈ s, cls p r = c) :
    prodR (ZMod p) s = (X + C (((c : ℕ) : ZMod p) ^ 2)) ^ s.card := by
  rw [prodR, ← Finset.prod_const]
  refine Finset.prod_congr rfl fun r hr => ?_
  rw [linR, cls_sq hm r, hs r hr]

end RowLemmas

theorem rowR_hermite' {n p : ℕ} [Fact p.Prime] (hp : Hyp n p) (a : Fin (mHalf p + 1)) (i : ℕ)
    (hi : i < dimO n p a) :
    rowR (ZMod p) n p a i
      = HermiteBasis.hermitePoly (fun c : Fin (mHalf p + 1) => (((c : ℕ) : ZMod p)) ^ 2)
          (fun c => dimO n p (c : ℕ)) a i := by
  have hm := hp.two_mHalf
  unfold rowR HermiteBasis.hermitePoly
  congr 1
  · -- `P_a ≡ ∏_{c ≠ a} (t + c²)^{m_c}`: group the tail factors by class
    let g : ℕ → Fin (mHalf p + 1) := fun r => ⟨cls p r, Nat.lt_succ_of_le (cls_le hm r)⟩
    have hg : ∀ r, g r = a ↔ cls p r = (a : ℕ) := fun r => by
      simp only [g, Fin.ext_iff]
    rw [prodR, ← Finset.prod_fiberwise_of_maps_to (s := Pset n p a) (t := Finset.univ.erase a)
      (g := g) ?maps]
    · refine Finset.prod_congr rfl fun c hc => ?_
      have hca : c ≠ a := (Finset.mem_erase.1 hc).1
      have hfib : (Pset n p a).filter (fun r => g r = c) = Tset n p c := by
        ext r
        simp only [Pset, Tset, Finset.mem_filter, g, Fin.ext_iff]
        constructor
        · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
        · rintro ⟨h1, h3⟩
          refine ⟨⟨h1, ?_⟩, h3⟩
          rw [h3]
          exact fun h => hca (Fin.ext h)
      rw [hfib, ← prodR, prodR_zmod_of_cls hm _ c (fun r hr => (mem_Tset.1 hr).2),
        card_Tset hp (Nat.lt_succ_iff.1 c.isLt)]
    · intro r hr
      rw [Finset.mem_erase]
      refine ⟨fun h => ?_, Finset.mem_univ _⟩
      rw [mem_Pset] at hr
      exact hr.2 ((hg r).1 h)
  · -- `q_{a,i} ≡ (t + a²)^i`
    unfold qR
    by_cases ha0 : (a : ℕ) = 0
    · rw [ite_eq_left ha0]
      have hi' : i < mFloor p (K n) := by simpa [dimO, ha0] using hi
      have h2 := mFloor_le_two hp
      split_ifs with hi0
      · subst hi0; simp
      · have hi1 : i = 1 := by omega
        subst hi1
        simp [linR, ha0]
    · rw [ite_eq_right ha0]
      split_ifs with hi2
      · rfl
      · have ha1 : 1 ≤ (a : ℕ) := Nat.pos_of_ne_zero ha0
        have ham : (a : ℕ) ≤ mHalf p := Nat.lt_succ_iff.1 a.isLt
        rw [prodR_zmod_of_cls hm _ (a : ℕ) (fun r hr => by
              simp only [Eset, Finset.mem_filter] at hr
              exact (mem_Tset.1 hr.1).2),
          card_Eset hp ha1 ham, linR, ← pow_add]
        congr 1
        omega

/-! # §3 (proofs).  The moments: `v_p(μ(t^e)) ≥ −1`, integrality for `e < 2p − 3`, and
the choice of `c_e` -/

section Moments

variable {p : ℕ} [hpr : Fact p.Prime]

omit hpr in
lemma padicGe_of_le {x : ℚ} {c : ℤ} (h : c ≤ padicValRat p x) : padicGe p x c :=
  Or.inr (by exact_mod_cast h)

omit hpr in
lemma padicValRat_ne_zero_unit {m : ℕ} (_hm0 : 0 < m) (hmp : ¬ p ∣ m) :
    padicValRat p (m : ℚ) = 0 := by
  rw [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hmp]; rfl

omit hpr in
/-- The factor `(2e+3)(2e+4)(2e+5)` of (2.2) is divisible by `p` whenever `B_{2e+2}` has a
pole at `p` and `e < 2p − 3`: "if `p − 1` divides `2e + 2`, the first three possible
multiples of `p − 1` are canceled respectively by the factors `2e+3, 2e+4, 2e+5`" (p. 11). -/
lemma p_dvd_three_factors (h7 : 7 ≤ p) {e : ℕ} (he : e < 2 * p - 3)
    (hdvd : (p - 1) ∣ 2 * (e + 1)) :
    p ∣ (2 * e + 3) * (2 * e + 4) * (2 * e + 5) := by
  obtain ⟨k, hk⟩ := hdvd
  have hk4 : k < 4 := by
    by_contra hcon
    have h4 : 4 ≤ k := by omega
    have : (p - 1) * 4 ≤ (p - 1) * k := Nat.mul_le_mul_left (p - 1) h4
    omega
  have hk0 : k ≠ 0 := by
    rintro rfl
    simp at hk
  interval_cases k
  · exact absurd rfl hk0
  · have : 2 * e + 3 = p := by omega
    rw [this]; exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (dvd_refl p) _) _
  · have : 2 * e + 4 = 2 * p := by omega
    rw [this]; exact Dvd.dvd.mul_right (Dvd.dvd.mul_left (dvd_mul_left p 2) _) _
  · have : 2 * e + 5 = 3 * p := by omega
    rw [this]; exact Dvd.dvd.mul_left (dvd_mul_left p 3) _

/-- `muMono e = ((−1)^e (2e+3)(2e+4)(2e+5)) · B_{2e+2} / 24`. -/
lemma muMono_eq' (e : ℕ) :
    muMono e = ((-1 : ℚ) ^ e * (((2 * e + 3) * (2 * e + 4) * (2 * e + 5) : ℕ) : ℚ))
      * _root_.bernoulli (2 * (e + 1)) / 24 := by
  rw [muMono, show 2 * e + 2 = 2 * (e + 1) by ring]
  push_cast
  ring

lemma padicValRat_24 (h7 : 7 ≤ p) : padicValRat p (24 : ℚ) = 0 := by
  have := padicValRat_ne_zero_unit (p := p) (m := 24) (by norm_num)
    (not_dvd_24 hpr.out h7)
  simpa using this

/-- **`v_p(μ(t^e)) ≥ −1`** (p. 11, "The polynomial moments satisfy `v_p(μ(t^e)) ≥ −1`"). -/
lemma muMono_vge_neg_one (h7 : 7 ≤ p) (e : ℕ) : (padicFil p).vge (muMono e) (-1) := by
  rw [muMono_eq']
  refine OuterLocal.vge_div_unit ?_ (padicValRat_24 h7)
  have hB : (padicFil p).vge (_root_.bernoulli (2 * (e + 1))) (-1) := by
    have := neg_one_le_padicValRat_bernoulli p (e + 1)
    exact padicGe_of_le (by exact_mod_cast this)
  have hA : (padicFil p).vge ((-1 : ℚ) ^ e * (((2 * e + 3) * (2 * e + 4) * (2 * e + 5) : ℕ) : ℚ)) 0 :=
    (OuterLocal.PInt.pow (by simpa using (OuterLocal.PInt.intCast (p := p) (-1))) e).mul
      (OuterLocal.PInt.natCast _)
  simpa using (padicFil p).vge_mul hA hB

/-- **`μ(t^e) ∈ ℤ_p` for `e < 2p − 3`** (p. 11, "They are integral for `e < 2p − 3`"). -/
lemma muMono_int_small (h7 : 7 ≤ p) {e : ℕ} (he : e < 2 * p - 3) :
    (padicFil p).vge (muMono e) 0 := by
  rw [muMono_eq']
  refine OuterLocal.vge_div_unit ?_ (padicValRat_24 h7)
  by_cases hdvd : (p - 1) ∣ 2 * (e + 1)
  · have hB : (padicFil p).vge (_root_.bernoulli (2 * (e + 1))) (-1) := by
      have := neg_one_le_padicValRat_bernoulli p (e + 1)
      exact padicGe_of_le (by exact_mod_cast this)
    have h3 : (padicFil p).vge ((((2 * e + 3) * (2 * e + 4) * (2 * e + 5) : ℕ) : ℤ) : ℚ) 1 := by
      have h := OuterLocal.PCong.zero_of_dvd (p := p)
        (z := (((2 * e + 3) * (2 * e + 4) * (2 * e + 5) : ℕ) : ℤ))
        (Int.natCast_dvd_natCast.2 (p_dvd_three_factors h7 he hdvd))
      rwa [OuterLocal.PCong, sub_zero] at h
    have h3' : (padicFil p).vge ((((2 * e + 3) * (2 * e + 4) * (2 * e + 5) : ℕ)) : ℚ) 1 := by
      simpa using h3
    have hsgn : (padicFil p).vge ((-1 : ℚ) ^ e) 0 :=
      OuterLocal.PInt.pow (by simpa using (OuterLocal.PInt.intCast (p := p) (-1))) e
    have := (padicFil p).vge_mul ((padicFil p).vge_mul hsgn h3') hB
    exact (padicFil p).vge_mono (by norm_num) this
  · have hB : (padicFil p).vge (_root_.bernoulli (2 * (e + 1))) 0 :=
      padicGe_of_le (by exact_mod_cast padicValRat_bernoulli_nonneg p hdvd)
    have hA : (padicFil p).vge ((-1 : ℚ) ^ e * (((2 * e + 3) * (2 * e + 4) * (2 * e + 5) : ℕ) : ℚ)) 0 :=
      (OuterLocal.PInt.pow (by simpa using (OuterLocal.PInt.intCast (p := p) (-1))) e).mul
        (OuterLocal.PInt.natCast _)
    simpa using (padicFil p).vge_mul hA hB

/-- A `p`-integral rational is congruent to an integer modulo `p`. -/
lemma exists_int_approx {x : ℚ} (hx : padicGe p x 0) : ∃ c : ℤ, padicGe p (x - c) 1 := by
  rcases eq_or_ne x 0 with rfl | hx0
  · exact ⟨0, Or.inl (by simp)⟩
  have hv : (0 : ℤ) ≤ padicValRat p x := by
    rcases hx with h | h
    · exact absurd h hx0
    · exact_mod_cast h
  have hden : ¬ p ∣ x.den := by
    intro hd
    have hnum : ¬ (p : ℤ) ∣ x.num := by
      intro hn
      have hcop := x.reduced
      have h1 : p ∣ x.num.natAbs := by
        have := Int.natAbs_dvd_natAbs.2 hn
        simpa using this
      have hg := Nat.dvd_gcd h1 hd
      rw [hcop.gcd_eq_one] at hg
      exact hpr.out.one_lt.ne' (Nat.dvd_one.1 hg)
    rw [padicValRat_def] at hv
    have h1 : padicValInt p x.num = 0 := padicValInt.eq_zero_of_not_dvd hnum
    have h2 : 1 ≤ padicValNat p x.den := one_le_padicValNat_of_dvd x.den_nz hd
    rw [h1] at hv
    omega
  have hunit : (x.den : ZMod p) ≠ 0 := by
    rwa [Ne, ZMod.natCast_eq_zero_iff]
  set d' : ZMod p := ((x.den : ZMod p))⁻¹ with hd'
  refine ⟨x.num * (d'.val : ℤ), ?_⟩
  have hden0 : (x.den : ℚ) ≠ 0 := by exact_mod_cast x.den_nz
  have hx_eq : x - ((x.num * (d'.val : ℤ) : ℤ) : ℚ)
      = ((x.num - x.num * (d'.val : ℤ) * (x.den : ℤ) : ℤ) : ℚ) / (x.den : ℚ) := by
    rw [eq_div_iff hden0, sub_mul, Rat.mul_den_eq_num]
    push_cast
    ring
  have hdvd : (p : ℤ) ∣ x.num - x.num * (d'.val : ℤ) * (x.den : ℤ) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [ZMod.natCast_zmod_val, hd', mul_assoc, inv_mul_cancel₀ hunit]
    ring
  have hnum : (padicFil p).vge ((x.num - x.num * (d'.val : ℤ) * (x.den : ℤ) : ℤ) : ℚ) 1 := by
    have h := OuterLocal.PCong.zero_of_dvd (p := p) hdvd
    rwa [OuterLocal.PCong, sub_zero] at h
  rw [hx_eq]
  exact OuterLocal.vge_div_unit hnum (padicValRat_ne_zero_unit x.den_pos hden)

omit hpr in
lemma cCoef_small {e : ℕ} (he : e < 2 * p - 3) : cCoef p e = 0 := by
  simp [cCoef, he]

/-- **`μ_0(t^e) = μ(t^e) − c_e/p ∈ ℤ_p`** for every `e`: the defining property of `c_e`. -/
lemma mu0_int (h7 : 7 ≤ p) (e : ℕ) : (padicFil p).vge (mu0 p e) 0 := by
  by_cases he : e < 2 * p - 3
  · rw [mu0, cCoef_small he]
    simpa using muMono_int_small h7 he
  · have hex : ∃ c : ℤ, padicGe p (muMono e - (c : ℚ) / p) 0 := by
      have hpx : (padicFil p).vge ((p : ℚ) * muMono e) 0 := by
        have hpv : (padicFil p).vge (p : ℚ) 1 := by
          have h := OuterLocal.PCong.p_congr_zero (p := p)
          rwa [OuterLocal.PCong, sub_zero] at h
        have := (padicFil p).vge_mul hpv (muMono_vge_neg_one h7 e)
        simpa using this
      obtain ⟨c, hc⟩ := exists_int_approx hpx
      refine ⟨c, ?_⟩
      have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hpr.out.ne_zero
      have heq : muMono e - (c : ℚ) / p = ((p : ℚ) * muMono e - c) / p := by
        field_simp
      rw [heq]
      have hvp : padicValRat p (p : ℚ) = 1 := padicValRat.self hpr.out.one_lt
      rcases hc with h0 | hc
      · exact Or.inl (by rw [h0, zero_div])
      · refine Or.inr ?_
        have hne : (p : ℚ) * muMono e - c ≠ 0 := by
          intro h; rw [h] at hc; norm_num at hc
        rw [padicValRat.div hne hp0, hvp]
        push_cast
        linarith
    rw [mu0, cCoef, ite_eq_right he]
    exact Classical.epsilon_spec hex

end Moments

/-! # §4 (proofs).  Integrality of the polynomial parts, and of `L` -/

section Integrality

variable {n p : ℕ}

lemma D_eq_prodR (m : ℕ) : D m = prodR ℚ (Icc 1 m) := rfl

lemma Dtail_eq_prodR (n : ℕ) : Dtail n = prodR ℚ (tail n) := rfl

/-- The entry numerator `W·f·g` of two rows is the image of an integer polynomial. -/
lemma entryNum_map (a i b j : ℕ) :
    (D (N n)) ^ 5 * (rowR ℚ n p a i * rowR ℚ n p b j)
      = (prodR ℤ (Icc 1 (N n)) ^ 5 * (rowR ℤ n p a i * rowR ℤ n p b j)).map
          (Int.castRingHom ℚ) := by
  simp [Polynomial.map_mul, Polynomial.map_pow, rowR_map', prodR_map, D_eq_prodR]

/-- Division by the monic integer polynomial `D_tail` keeps integer coefficients. -/
lemma divByMonic_map_int (Az : ℤ[X]) :
    (Az.map (Int.castRingHom ℚ)) /ₘ Dtail n
      = (Az /ₘ prodR ℤ (tail n)).map (Int.castRingHom ℚ) := by
  rw [Polynomial.map_divByMonic _ (prodR_monic _), prodR_map, Dtail_eq_prodR]

lemma muPolyW_int_of_int [Fact p.Prime] (w : ℕ → ℚ) (hw : ∀ e, (padicFil p).vge (w e) 0)
    (Qz : ℤ[X]) : (padicFil p).vge (muPolyW w (Qz.map (Int.castRingHom ℚ))) 0 := by
  unfold muPolyW
  refine (padicFil p).vge_sum _ _ _ fun e _ => ?_
  rw [Polynomial.coeff_map]
  have := (padicFil p).vge_mul (OuterLocal.PInt.intCast (p := p) (Qz.coeff e)) (hw e)
  simpa using this

/-- **The polynomial part of an entry of `A` is integral** — "The polynomial part is
integral" (p. 12): the quotient by `D_tail` has integer coefficients and every `μ_0(t^e)` is
integral. -/
lemma polyPart_int [Fact p.Prime] (hp : Hyp n p) (a i b j : ℕ) :
    (gaussFil p).vge
      (C (muPolyW (mu0 p) (((D (N n)) ^ 5 * (rowR ℚ n p a i * rowR ℚ n p b j)) /ₘ Dtail n))) 0 := by
  rw [entryNum_map, divByMonic_map_int]
  exact OuterLocal.gaussGe_C (muPolyW_int_of_int _ (mu0_int hp.ge7) _)

end Integrality

/-! # §5 (proofs).  The rank bound (4.10): `L = U L_0 Uᵀ` and `L_0` has `h − r_p` zero
columns -/

section Rank

lemma muPolyW_eq_sum (w : ℕ → ℚ) (P : ℚ[X]) {s : Finset ℕ} (hs : P.support ⊆ s) :
    muPolyW w P = ∑ e ∈ s, P.coeff e * w e :=
  Finset.sum_subset hs fun e _he hes => by
    rw [Polynomial.notMem_support_iff.1 hes, zero_mul]

lemma muPolyW_add (w : ℕ → ℚ) (P R : ℚ[X]) :
    muPolyW w (P + R) = muPolyW w P + muPolyW w R := by
  classical
  have h1 : muPolyW w (P + R)
      = ∑ e ∈ (P + R).support ∪ (P.support ∪ R.support), (P + R).coeff e * w e :=
    muPolyW_eq_sum w (P + R) Finset.subset_union_left
  have h2 : muPolyW w P
      = ∑ e ∈ (P + R).support ∪ (P.support ∪ R.support), P.coeff e * w e :=
    muPolyW_eq_sum w P (Finset.Subset.trans Finset.subset_union_left Finset.subset_union_right)
  have h3 : muPolyW w R
      = ∑ e ∈ (P + R).support ∪ (P.support ∪ R.support), R.coeff e * w e :=
    muPolyW_eq_sum w R (Finset.Subset.trans Finset.subset_union_right Finset.subset_union_right)
  rw [h1, h2, h3, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun e _ => by rw [coeff_add]; ring

lemma muPolyW_C_mul (w : ℕ → ℚ) (a : ℚ) (P : ℚ[X]) :
    muPolyW w (C a * P) = a * muPolyW w P := by
  have hsub : (C a * P).support ⊆ P.support := by
    intro e he
    rw [Polynomial.mem_support_iff] at he ⊢
    intro hcon
    exact he (by rw [coeff_C_mul, hcon, mul_zero])
  rw [muPolyW_eq_sum w (C a * P) hsub, muPolyW_eq_sum w P Finset.Subset.rfl, Finset.mul_sum]
  exact Finset.sum_congr rfl fun e _ => by rw [coeff_C_mul]; ring

lemma muL_add (n p : ℕ) (A B : ℚ[X]) : muL n p (A + B) = muL n p A + muL n p B := by
  rw [muL, muL, muL, Polynomial.add_divByMonic, muPolyW_add, C_add]

lemma muL_C_mul (n p : ℕ) (a : ℚ) (A : ℚ[X]) : muL n p (C a * A) = C a * muL n p A := by
  have hdiv : (C a * A) /ₘ Dtail n = C a * (A /ₘ Dtail n) := by
    rw [← Polynomial.smul_eq_C_mul, Polynomial.smul_divByMonic, Polynomial.smul_eq_C_mul]
  rw [muL, muL, hdiv, muPolyW_C_mul, C_mul]

lemma muL_zero (n p : ℕ) : muL n p 0 = 0 := by
  have h := muL_C_mul n p 0 0
  simpa using h

lemma muL_sum {ι : Type*} (n p : ℕ) (s : Finset ι) (A : ι → ℚ[X]) :
    muL n p (∑ i ∈ s, A i) = ∑ i ∈ s, muL n p (A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, muL_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, muL_add, ih]

/-- **The basis change for `L`**: `L = U L_0 Uᵀ` (the same computation as
`Zeta5.OuterLocal.gram_basis_change`, for the functional `muL`). -/
theorem Lq_eq (n p : ℕ) (U : Matrix (Fin (h n)) (Fin (h n)) ℚ) :
    Lq n p U = (U.map C) * L0 n p * (U.map C).transpose := by
  classical
  refine Matrix.ext fun u v => ?_
  have hexp : (D (N n)) ^ 5 * (OuterLocal.rowPoly U u * OuterLocal.rowPoly U v)
      = ∑ i : Fin (h n), ∑ j : Fin (h n),
          C (U u i * U v j) * ((D (N n)) ^ 5 * (X ^ (i : ℕ) * X ^ (j : ℕ))) := by
    rw [OuterLocal.rowPoly, OuterLocal.rowPoly, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul]; ring
  have hlhs : Lq n p U u v
      = ∑ i : Fin (h n), ∑ j : Fin (h n), C (U u i * U v j) * L0 n p i j := by
    rw [Lq, Matrix.of_apply, hexp, muL_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [muL_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [muL_C_mul, L0, Matrix.of_apply]
  have hrhs : ((U.map C) * L0 n p * (U.map C).transpose) u v
      = ∑ j : Fin (h n), ∑ i : Fin (h n), C (U u i) * L0 n p i j * C (U v j) := by
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rfl
  have hcomm : ∑ i : Fin (h n), ∑ j : Fin (h n), C (U u i * U v j) * L0 n p i j
      = ∑ j : Fin (h n), ∑ i : Fin (h n), C (U u i * U v j) * L0 n p i j :=
    Finset.sum_comm (f := fun (i j : Fin (h n)) => C (U u i * U v j) * L0 n p i j)
  rw [hlhs, hcomm, hrhs]
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul]; ring

lemma D_pow_mul_natDegree (m e : ℕ) : ((D m) ^ 5 * X ^ e).natDegree = 5 * m + e := by
  rw [Monic.natDegree_mul ((D_monic m).pow 5) (monic_X_pow e), (D_monic m).natDegree_pow,
    D_natDegree, natDegree_X_pow]

/-- **"`L_ij = 0` if `i + j < K − 6N + 2p − 3`"** (p. 12): the polynomial quotient of
`W t^{i+j}/D_tail` has degree `i + j + 6N − K`, and `c_e = 0` for `e < 2p − 3`. -/
theorem L0_eq_zero {n p : ℕ} (hp2 : 2 ≤ p) (i j : Fin (h n))
    (hij : (i : ℕ) + (j : ℕ) + 6 * N n + 3 < K n + 2 * p) : L0 n p i j = 0 := by
  rw [L0, Matrix.of_apply, muL, ← pow_add]
  have hdeg : ((D (N n)) ^ 5 * X ^ ((i : ℕ) + (j : ℕ)) /ₘ Dtail n).natDegree
      = 5 * N n + ((i : ℕ) + (j : ℕ)) - h n := by
    rw [Polynomial.natDegree_divByMonic _ (Dtail_monic n), D_pow_mul_natDegree,
      Functional.Dtail_natDegree]
  have hsum : muPolyW (fun e => (cCoef p e : ℚ))
      ((D (N n)) ^ 5 * X ^ ((i : ℕ) + (j : ℕ)) /ₘ Dtail n) = 0 := by
    unfold muPolyW
    refine Finset.sum_eq_zero fun e he => ?_
    have hle : e ≤ ((D (N n)) ^ 5 * X ^ ((i : ℕ) + (j : ℕ)) /ₘ Dtail n).natDegree :=
      Polynomial.le_natDegree_of_mem_supp e he
    have he' : e < 2 * p - 3 := by
      rw [hdeg] at hle
      have hN : N n = 3 * n := rfl
      have hK : K n = 40 * n := rfl
      have hh : h n = 37 * n := rfl
      omega
    simp [cCoef_small he']
  rw [hsum, C_0]

/-- A matrix with a set `S` of zero columns has rank at most the number of other columns. -/
lemma rank_le_of_zero_cols {F : Type*} [Field F] {hh : ℕ} (M : Matrix (Fin hh) (Fin hh) F)
    (S : Finset (Fin hh)) (hS : ∀ i j, j ∈ S → M i j = 0) : M.rank ≤ Sᶜ.card := by
  classical
  have hM : M = M * Matrix.diagonal (fun j => if j ∈ S then (0 : F) else 1) := by
    ext i j
    rw [Matrix.mul_diagonal]
    by_cases hj : j ∈ S
    · rw [ite_eq_left hj, mul_zero, hS i j hj]
    · rw [ite_eq_right hj, mul_one]
  calc M.rank = (M * Matrix.diagonal (fun j => if j ∈ S then (0 : F) else 1)).rank := by
        rw [← hM]
    _ ≤ (Matrix.diagonal (fun j => if j ∈ S then (0 : F) else 1)).rank :=
        Matrix.rank_mul_le_right _ _
    _ = Sᶜ.card := by
        rw [Matrix.rank_diagonal, Fintype.card_subtype]
        congr 1
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl]
        split_ifs with hj <;> simp [hj]

/-- **The rank bound of (4.10) in the monomial basis**: the first `h − r_p` columns of `L_0`
vanish. -/
theorem rank_L0 {n p : ℕ} (hp : Hyp n p) :
    ((L0 n p).map (algebraMap ℚ[X] (RatFunc ℚ))).rank ≤ (rOut n p).toNat := by
  classical
  set d := 2 * p - 5 * N n - 2 with hd
  let S : Finset (Fin (h n)) := Finset.univ.filter (fun j => (j : ℕ) < d)
  have hS : ∀ i j, j ∈ S → ((L0 n p).map (algebraMap ℚ[X] (RatFunc ℚ))) i j = 0 := by
    intro i j hj
    have hjd : (j : ℕ) < d := (Finset.mem_filter.1 hj).2
    have hi := i.isLt
    rw [Matrix.map_apply, L0_eq_zero (by have := hp.ge7; omega) i j ?_, map_zero]
    have h5 := hp.fiveN
    have hN : N n = 3 * n := rfl
    have hK : K n = 40 * n := rfl
    have hh : h n = 37 * n := rfl
    omega
  refine le_trans (rank_le_of_zero_cols _ S hS) ?_
  have hcard : Sᶜ.card ≤ h n - d := by
    have hmem : ∀ j : Fin (h n), j ∈ Sᶜ → d ≤ (j : ℕ) := by
      intro j hj
      simp only [S, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and,
        not_lt] at hj
      exact hj
    refine le_trans (Finset.card_le_card_of_injOn (fun j : Fin (h n) => (j : ℕ) - d) ?_ ?_)
      (le_of_eq (Finset.card_range (h n - d)))
    · intro j hj
      have h1 := hmem j hj
      have h2 : (j : ℕ) < h n := j.isLt
      show (j : ℕ) - d ∈ Finset.range (h n - d)
      exact Finset.mem_range.2 (by omega)
    · intro x hx y hy hxy
      have h1 := hmem x hx
      have h2 := hmem y hy
      dsimp only at hxy
      exact Fin.ext (by omega)
  have hr : ((K n : ℤ) + 4 * N n - 2 * p + 2) ≤ rOut n p := le_max_right _ _
  have hr0 : (0 : ℤ) ≤ rOut n p := le_max_left _ _
  have h5 := hp.fiveN
  have hN : N n = 3 * n := rfl
  have hK : K n = 40 * n := rfl
  have hh : h n = 37 * n := rfl
  have : ((h n - d : ℕ) : ℤ) ≤ rOut n p := by
    push_cast [hN, hK, hh] at hr ⊢
    omega
  omega

end Rank

/-! # §6 (proofs).  Partial fractions of `F/∏_{r∈S}(t+r²)`, and `p`-adic tools -/

section Residues

open Functional

/-- The residue part of `μ_X(A/D_tail)`. -/
def resSum (n : ℕ) (A : ℚ[X]) : ℚ[X] := ∑ r ∈ Ioc (N n) (K n), C (residue n A r) * muPole r

lemma muOver0_eq (n p : ℕ) (A : ℚ[X]) :
    muOver0 n p A = C (muPolyW (mu0 p) (A /ₘ Dtail n)) + resSum n A := rfl

lemma linR_eval_node (s r : ℕ) : (linR ℚ s).eval (node r) = (s : ℚ) ^ 2 - (r : ℚ) ^ 2 := by
  simp only [linR, eval_add, eval_X, eval_C, node]; ring

lemma prodR_eval_node (S : Finset ℕ) (r : ℕ) :
    (prodR ℚ S).eval (node r) = ∏ s ∈ S, ((s : ℚ) ^ 2 - (r : ℚ) ^ 2) := by
  rw [prodR, eval_prod]
  exact Finset.prod_congr rfl fun s _ => linR_eval_node s r

lemma sq_sub_sq_ne_zero {s r : ℕ} (h : s ≠ r) : (s : ℚ) ^ 2 - (r : ℚ) ^ 2 ≠ 0 := by
  intro hc
  have h1 : ((s ^ 2 : ℕ) : ℚ) = ((r ^ 2 : ℕ) : ℚ) := by push_cast; linarith
  have h2 : s ^ 2 = r ^ 2 := by exact_mod_cast h1
  exact h (Nat.pow_left_injective (by norm_num) h2)

/-- **Partial fractions for `F/∏_{r∈S}(t+r²)`**: written over `D_tail` as
`(F·∏_{r∉S}(t+r²))/D_tail`, the residue at `−r²` is `F(−r²)/∏_{s∈S, s≠r}(s²−r²)` for `r ∈ S`,
and `0` otherwise. -/
lemma residue_formula {n : ℕ} {S : Finset ℕ} (hS : S ⊆ tail n) (F : ℚ[X]) {r : ℕ}
    (hr : r ∈ tail n) :
    residue n (F * prodR ℚ (tail n \ S)) r
      = if r ∈ S then F.eval (node r) / ∏ s ∈ S.erase r, ((s : ℚ) ^ 2 - (r : ℚ) ^ 2) else 0 := by
  classical
  rw [residue_eq n _ hr, cof_eval, eval_mul, prodR_eval_node]
  split_ifs with hrS
  · have hsplit : (Ioc (N n) (K n)).erase r = (tail n \ S) ∪ S.erase r := by
      ext s
      simp only [tail, Finset.mem_erase, Finset.mem_union, Finset.mem_sdiff]
      constructor
      · rintro ⟨hsr, hs⟩
        by_cases hsS : s ∈ S
        · exact Or.inr ⟨hsr, hsS⟩
        · exact Or.inl ⟨hs, hsS⟩
      · rintro (⟨hs, hsS⟩ | ⟨hsr, hsS⟩)
        · exact ⟨fun h => hsS (h ▸ hrS), hs⟩
        · exact ⟨hsr, hS hsS⟩
    have hdisj : Disjoint (tail n \ S) (S.erase r) := by
      rw [Finset.disjoint_left]
      intro s h1 h2
      exact (Finset.mem_sdiff.1 h1).2 (Finset.mem_of_mem_erase h2)
    have hne : ∏ s ∈ tail n \ S, ((s : ℚ) ^ 2 - (r : ℚ) ^ 2) ≠ 0 := by
      rw [Finset.prod_ne_zero_iff]
      intro s hs
      apply sq_sub_sq_ne_zero
      rintro rfl
      exact (Finset.mem_sdiff.1 hs).2 hrS
    rw [hsplit, Finset.prod_union hdisj, mul_comm (∏ s ∈ tail n \ S, _),
      mul_div_mul_right _ _ hne]
  · have hmem : r ∈ tail n \ S := Finset.mem_sdiff.2 ⟨hr, hrS⟩
    rw [Finset.prod_eq_zero hmem (by ring), mul_zero, zero_div]

/-- **The residue part of `μ_X(F/∏_{r∈S}(t+r²))`**. -/
lemma resSum_formula {n : ℕ} {S : Finset ℕ} (hS : S ⊆ tail n) (F : ℚ[X]) :
    resSum n (F * prodR ℚ (tail n \ S))
      = ∑ r ∈ S, C (F.eval (node r) / ∏ s ∈ S.erase r, ((s : ℚ) ^ 2 - (r : ℚ) ^ 2)) * muPole r := by
  classical
  unfold resSum
  have hterm : ∀ r ∈ Ioc (N n) (K n), C (residue n (F * prodR ℚ (tail n \ S)) r) * muPole r
      = if r ∈ S then
          C (F.eval (node r) / ∏ s ∈ S.erase r, ((s : ℚ) ^ 2 - (r : ℚ) ^ 2)) * muPole r
        else 0 := by
    intro r hr
    rw [residue_formula hS F hr]
    split_ifs <;> simp
  have hinter : Ioc (N n) (K n) ∩ S = S := Finset.inter_eq_right.2 hS
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_mem, hinter]

/-- A product over a set `T` of polynomials evaluated … : `prodR s * prodR t = prodR (s ∪ t)`
for disjoint `s, t`. -/
lemma prodR_mul_prodR {s t : Finset ℕ} (h : Disjoint s t) :
    prodR ℚ s * prodR ℚ t = prodR ℚ (s ∪ t) := by
  rw [prodR, prodR, prodR, Finset.prod_union h]

end Residues

section PadicTools

variable {p : ℕ} [hpr : Fact p.Prime]

lemma vge_pow {x : ℚ} {c : ℚ} (hx : (padicFil p).vge x c) (k : ℕ) :
    (padicFil p).vge (x ^ k) (k * c) := by
  induction k with
  | zero => simp only [pow_zero, Nat.cast_zero, zero_mul]; exact (padicFil p).vge_one
  | succ k ih =>
      rw [pow_succ]
      have := (padicFil p).vge_mul ih hx
      refine (padicFil p).vge_mono (le_of_eq ?_) this
      push_cast; ring

lemma vge_div_val {x d : ℚ} {c : ℚ} {k : ℤ} (hx : (padicFil p).vge x c) (hd : d ≠ 0)
    (hk : padicValRat p d = k) : (padicFil p).vge (x / d) (c - k) := by
  rcases hx with h0 | hx
  · exact Or.inl (by rw [h0, zero_div])
  · by_cases hx0 : x = 0
    · exact Or.inl (by rw [hx0, zero_div])
    · refine Or.inr ?_
      rw [padicValRat.div hx0 hd, hk]
      push_cast
      linarith

lemma vge_int (z : ℤ) : (padicFil p).vge (z : ℚ) 0 := OuterLocal.PInt.intCast z

lemma vge_nat_sq_sub (s r : ℕ) : (padicFil p).vge ((s : ℚ) ^ 2 - (r : ℚ) ^ 2) 0 := by
  have := vge_int (p := p) ((s : ℤ) ^ 2 - (r : ℤ) ^ 2)
  push_cast at this
  exact this

lemma vge_prodR_eval (S : Finset ℕ) (r : ℕ) :
    (padicFil p).vge ((prodR ℚ S).eval (Functional.node r)) 0 := by
  rw [prodR_eval_node]
  have := (padicFil p).vge_prod S (fun s => (s : ℚ) ^ 2 - (r : ℚ) ^ 2) (fun _ => 0)
    (fun s _ => vge_nat_sq_sub s r)
  simpa using this

/-- The value at a node of a polynomial with integer coefficients is an integer. -/
lemma eval_node_map_int (Fz : ℤ[X]) (r : ℕ) :
    (Fz.map (Int.castRingHom ℚ)).eval (Functional.node r)
      = ((Fz.eval (-(r : ℤ) ^ 2) : ℤ) : ℚ) := by
  have hnode : Functional.node r = ((-(r : ℤ) ^ 2 : ℤ) : ℚ) := by
    simp [Functional.node]
  rw [hnode, Polynomial.eval_intCast_map]
  simp

lemma vge_eval_node_int (Fz : ℤ[X]) (r : ℕ) :
    (padicFil p).vge ((Fz.map (Int.castRingHom ℚ)).eval (Functional.node r)) 0 := by
  rw [eval_node_map_int]; exact vge_int _

omit hpr in
lemma padicValNat_le_one_of_lt_sq {v : ℕ} (hv1 : 1 ≤ v) (hv : v < p ^ 2) :
    padicValNat p v ≤ 1 := by
  by_contra! hc
  have h2 : p ^ 2 ∣ v := (Nat.pow_dvd_pow p hc).trans pow_padicValNat_dvd
  have := Nat.le_of_dvd (by omega) h2
  omega

lemma vge_one_div_pow {v : ℕ} (hv1 : 1 ≤ v) (hv : v < p ^ 2) (k : ℕ) :
    (padicFil p).vge (1 / (v : ℚ) ^ k) (-(k : ℚ)) := by
  refine Or.inr ?_
  have hval : padicValRat p (v : ℚ) = padicValNat p v := padicValRat.of_nat
  rw [one_div, padicValRat.inv, padicValRat.pow, hval]
  have := padicValNat_le_one_of_lt_sq (p := p) hv1 hv
  generalize padicValNat p v = t at this ⊢
  have h' : (t : ℚ) ≤ 1 := by exact_mod_cast this
  have hk : (0 : ℚ) ≤ k := by positivity
  push_cast
  nlinarith [h', hk]

omit hpr in
lemma padicValRat_four (h7 : 7 ≤ p) : padicValRat p (4 : ℚ) = 0 := by
  have := padicValRat_ne_zero_unit (p := p) (m := 4) (by norm_num)
    (fun hd => by have := Nat.le_of_dvd (by norm_num) hd; omega)
  simpa using this

omit hpr in
lemma padicValRat_two (h7 : 7 ≤ p) : padicValRat p (2 : ℚ) = 0 := by
  have := padicValRat_ne_zero_unit (p := p) (m := 2) (by norm_num)
    (fun hd => by have := Nat.le_of_dvd (by norm_num) hd; omega)
  simpa using this

/-- `v_p(1/(2r)) ≥ −1` for `1 ≤ r < p²`. -/
lemma vge_inv_two_mul (h7 : 7 ≤ p) {r : ℕ} (hr1 : 1 ≤ r) (hr : r < p ^ 2) :
    (padicFil p).vge (1 / (2 * (r : ℚ))) (-1) := by
  have h1 := vge_one_div_pow (p := p) hr1 hr 1
  have h2 : (padicFil p).vge (1 / (2 : ℚ)) 0 := OuterLocal.PInt.inv_of_unit (padicValRat_two h7)
  have := (padicFil p).vge_mul h2 h1
  have heq : 1 / (2 : ℚ) * (1 / (r : ℚ) ^ 1) = 1 / (2 * (r : ℚ)) := by
    rw [pow_one, one_div_mul_one_div]
  rw [heq] at this
  simpa using this

lemma gauss_affine {α β c : ℚ} (h1 : (padicFil p).vge α c) (h2 : (padicFil p).vge β c) :
    (gaussFil p).vge (C α * X + C β) c := by
  have hX := (gaussFil p).vge_mul (OuterLocal.gaussGe_C h1) OuterLocal.gaussGe_X
  refine (gaussFil p).vge_add ?_ (OuterLocal.gaussGe_C h2)
  simpa using hX

/-- `v_p^G(μ_X(1/(t+r²))) ≥ −5` for `1 ≤ r < p²`: "a harmonic value loses at most `5`". -/
lemma muPole_vge_neg_five (h7 : 7 ≤ p) {r : ℕ} (hr1 : 1 ≤ r) (hr : r < p ^ 2) :
    (gaussFil p).vge (muPole r) (-5) := by
  rw [Functional.muPole_eq]
  have hH : (padicFil p).vge (H5 r) (-5) := by
    unfold H5
    refine (padicFil p).vge_sum _ _ _ fun v hv => ?_
    rw [Finset.mem_Icc] at hv
    have := vge_one_div_pow (p := p) (v := v) hv.1 (by omega) 5
    simpa using this
  have hr4 : (padicFil p).vge ((r : ℚ) ^ 4) 0 := by
    have := vge_int (p := p) ((r : ℤ) ^ 4)
    push_cast at this
    exact this
  refine gauss_affine ((padicFil p).vge_mono (by norm_num) hr4) ?_
  have t1 : (padicFil p).vge (-((r : ℚ) ^ 4 * H5 r)) (-5) := by
    have := (padicFil p).vge_neg ((padicFil p).vge_mul hr4 hH)
    simpa using this
  have t2 : (padicFil p).vge (1 / 4 : ℚ) (-5) :=
    (padicFil p).vge_mono (by norm_num) (OuterLocal.PInt.inv_of_unit (padicValRat_four h7))
  have t3 : (padicFil p).vge (1 / (2 * (r : ℚ))) (-5) :=
    (padicFil p).vge_mono (by norm_num) (vge_inv_two_mul h7 hr1 hr)
  have key := (padicFil p).vge_add ((padicFil p).vge_add t1 ((padicFil p).vge_neg t2)) t3
  convert key using 1
  ring

end PadicTools

/-! # §7 (proofs).  The valuations: pole values, node separations, the factor `W` -/

section Valuations

variable {n p : ℕ} [hpr : Fact p.Prime]

open Functional

/-- `μ_X(1/(t+r²))` is integral for `1 ≤ r < p`. -/
lemma muPole_vge_zero (h7 : 7 ≤ p) {r : ℕ} (hr1 : 1 ≤ r) (hr : r < p) :
    (gaussFil p).vge (muPole r) 0 := by
  rw [Functional.muPole_eq]
  have hr4 : (padicFil p).vge ((r : ℚ) ^ 4) 0 := by
    have := vge_int (p := p) ((r : ℤ) ^ 4)
    push_cast at this
    exact this
  refine gauss_affine hr4 ?_
  have hH : (padicFil p).vge (H5 r) 0 := OuterLocal.PInt.H5 hr
  have t1 : (padicFil p).vge (-((r : ℚ) ^ 4 * H5 r)) 0 := by
    have := (padicFil p).vge_neg ((padicFil p).vge_mul hr4 hH)
    simpa using this
  have t2 : (padicFil p).vge (1 / 4 : ℚ) 0 := OuterLocal.PInt.inv_of_unit (padicValRat_four h7)
  have t3 : (padicFil p).vge (1 / (2 * (r : ℚ))) 0 := by
    have h1 : (padicFil p).vge (1 / (r : ℚ) ^ 1) 0 := OuterLocal.PInt.inv_pow_natCast hr1 hr 1
    have h2 : (padicFil p).vge (1 / (2 : ℚ)) 0 := OuterLocal.PInt.inv_of_unit (padicValRat_two h7)
    have := (padicFil p).vge_mul h2 h1
    have heq : 1 / (2 : ℚ) * (1 / (r : ℚ) ^ 1) = 1 / (2 * (r : ℚ)) := by
      rw [pow_one, one_div_mul_one_div]
    rw [heq] at this
    simpa using this
  have key := (padicFil p).vge_add ((padicFil p).vge_add t1 ((padicFil p).vge_neg t2)) t3
  convert key using 1
  ring

/-- `v_p^G(μ_X(1/(t+r²))) ≥ −1` for the zero-class poles `r = p, 2p` (`p ∣ r`, `r < p²`). -/
lemma muPole_vge_neg_one (h7 : 7 ≤ p) {r : ℕ} (hr1 : 1 ≤ r) (hr : r < p ^ 2) (hpr' : p ∣ r) :
    (gaussFil p).vge (muPole r) (-1) := by
  rw [Functional.muPole_eq]
  have hr1' : (padicFil p).vge ((r : ℚ)) 1 := by
    have h := OuterLocal.PCong.zero_of_dvd (p := p) (z := (r : ℤ)) (Int.natCast_dvd_natCast.2 hpr')
    rw [OuterLocal.PCong, sub_zero] at h
    simpa using h
  have hr4 : (padicFil p).vge ((r : ℚ) ^ 4) 4 := by
    have := vge_pow hr1' 4
    simpa using this
  refine gauss_affine ((padicFil p).vge_mono (by norm_num) hr4) ?_
  have hH : (padicFil p).vge ((r : ℚ) ^ 4 * H5 r) (-1) := by
    unfold H5
    rw [Finset.mul_sum]
    refine (padicFil p).vge_sum _ _ _ fun v hv => ?_
    rw [Finset.mem_Icc] at hv
    have h5 := vge_one_div_pow (p := p) (v := v) hv.1 (by omega) 5
    have := (padicFil p).vge_mul hr4 h5
    exact (padicFil p).vge_mono (by norm_num) this
  have t1 : (padicFil p).vge (-((r : ℚ) ^ 4 * H5 r)) (-1) := (padicFil p).vge_neg hH
  have t2 : (padicFil p).vge (1 / 4 : ℚ) (-1) :=
    (padicFil p).vge_mono (by norm_num) (OuterLocal.PInt.inv_of_unit (padicValRat_four h7))
  have t3 : (padicFil p).vge (1 / (2 * (r : ℚ))) (-1) := vge_inv_two_mul h7 hr1 hr
  have key := (padicFil p).vge_add ((padicFil p).vge_add t1 ((padicFil p).vge_neg t2)) t3
  convert key using 1
  ring

omit hpr in
lemma padicValInt_le_one' {z : ℤ} (hz : z ≠ 0) (hlt : z.natAbs < p ^ 2) :
    padicValInt p z ≤ 1 := by
  unfold padicValInt
  exact padicValNat_le_one_of_lt_sq (by omega) hlt

lemma one_le_padicValInt' {z : ℤ} (hz : z ≠ 0) (hd : (p : ℤ) ∣ z) : 1 ≤ padicValInt p z := by
  unfold padicValInt
  exact one_le_padicValNat_of_dvd (by omega) (Int.natCast_dvd.1 hd)

lemma vge_one_of_dvd {z : ℤ} (hd : (p : ℤ) ∣ z) : (padicFil p).vge (z : ℚ) 1 := by
  have h := OuterLocal.PCong.zero_of_dvd (p := p) hd
  rwa [OuterLocal.PCong, sub_zero] at h

/-- **Distinct poles of one ordinary class differ by exactly one power of `p`**:
`v_p(s² − r²) = 1` (uses `p² > 2K`). -/
lemma val_sq_sub_sq (hp : Hyp n p) {a r s : ℕ} (ha1 : 1 ≤ a) (hr : r ∈ Tset n p a)
    (hs : s ∈ Tset n p a) (hrs : s ≠ r) : padicValRat p ((s : ℚ) ^ 2 - (r : ℚ) ^ 2) = 1 := by
  have hm := hp.two_mHalf
  rw [mem_Tset] at hr hs
  have hK2 := hp.sq
  have h7 := hp.ge7
  generalize hP : p ^ 2 = P at hK2
  have hxy : (s : ℚ) ^ 2 - (r : ℚ) ^ 2 = ((((s : ℤ) - r) * ((s : ℤ) + r) : ℤ) : ℚ) := by
    push_cast; ring
  have hdvd : (p : ℤ) ∣ ((s : ℤ) - r) * ((s : ℤ) + r) := by
    have := dvd_sq_sub_sq hm (hr.2.trans hs.2.symm)
    convert this using 1; ring
  have hx0 : ((s : ℤ) - r) ≠ 0 := by omega
  have hy0 : ((s : ℤ) + r) ≠ 0 := by omega
  have hprime := Nat.prime_iff_prime_int.1 hpr.out
  have hnotboth : ¬ ((p : ℤ) ∣ ((s : ℤ) - r) ∧ (p : ℤ) ∣ ((s : ℤ) + r)) := by
    rintro ⟨h1, h2⟩
    have h3 : (p : ℤ) ∣ 2 * (s : ℤ) := by
      have := dvd_add h1 h2; convert this using 1; ring
    have hps : p ∣ s := by
      rcases hprime.dvd_or_dvd h3 with h | h
      · exfalso
        have := Int.le_of_dvd (by norm_num) h
        omega
      · exact Int.natCast_dvd_natCast.1 h
    have := (cls_eq_zero_iff hm s).2 hps
    omega
  have hx1 : padicValInt p ((s : ℤ) - r) ≤ 1 :=
    padicValInt_le_one' hx0 (by rw [hP]; omega)
  have hy1 : padicValInt p ((s : ℤ) + r) ≤ 1 :=
    padicValInt_le_one' hy0 (by rw [hP]; omega)
  rw [hxy, padicValRat.of_int, padicValInt.mul hx0 hy0]
  rcases hprime.dvd_or_dvd hdvd with h | h
  · have h1 := one_le_padicValInt' hx0 h
    have h2 : padicValInt p ((s : ℤ) + r) = 0 :=
      padicValInt.eq_zero_of_not_dvd (fun h' => hnotboth ⟨h, h'⟩)
    omega
  · have h1 := one_le_padicValInt' hy0 h
    have h2 : padicValInt p ((s : ℤ) - r) = 0 :=
      padicValInt.eq_zero_of_not_dvd (fun h' => hnotboth ⟨h', h⟩)
    omega

lemma val_prod_eq_card {T : Finset ℕ} (f : ℕ → ℚ)
    (hf : ∀ s ∈ T, f s ≠ 0 ∧ padicValRat p (f s) = 1) :
    (∏ s ∈ T, f s) ≠ 0 ∧ padicValRat p (∏ s ∈ T, f s) = T.card := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | insert a T ha ih =>
      obtain ⟨h1, h2⟩ := ih (fun s hs => hf s (Finset.mem_insert_of_mem hs))
      obtain ⟨h3, h4⟩ := hf a (Finset.mem_insert_self _ _)
      rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
      refine ⟨mul_ne_zero h3 h1, ?_⟩
      rw [padicValRat.mul h3 h1, h4, h2]
      push_cast; ring

/-- The node derivative of an ordinary class: `v_p(∏_{s ∈ T_a, s ≠ r}(s² − r²)) = |T_a| − 1`
exactly — "the node derivative loses `ℓ − δ − 1`". -/
lemma val_node_derivative (hp : Hyp n p) {a r : ℕ} (ha1 : 1 ≤ a) (hr : r ∈ Tset n p a) :
    (∏ s ∈ (Tset n p a).erase r, ((s : ℚ) ^ 2 - (r : ℚ) ^ 2)) ≠ 0 ∧
      padicValRat p (∏ s ∈ (Tset n p a).erase r, ((s : ℚ) ^ 2 - (r : ℚ) ^ 2))
        = ((Tset n p a).card - 1 : ℕ) := by
  rw [← Finset.card_erase_of_mem hr]
  refine val_prod_eq_card _ fun s hs => ?_
  obtain ⟨hsr, hsT⟩ := Finset.mem_erase.1 hs
  exact ⟨sq_sub_sq_ne_zero hsr, val_sq_sub_sq hp ha1 hr hsT hsr⟩

/-- **The factor `W = D_N⁵` supplies `5δ`** at a pole of the class `a`. -/
lemma vge_W_eval (hp : Hyp n p) {a r : ℕ} (ha1 : 1 ≤ a) (ha : a ≤ mHalf p)
    (hr : r ∈ Tset n p a) :
    (padicFil p).vge (((D (N n)) ^ 5).eval (node r))
      (5 * (((if a ≤ N n then 1 else 0 : ℕ)) : ℚ)) := by
  classical
  have hm := hp.two_mHalf
  rw [eval_pow, D_eq_prodR, prodR_eval_node]
  split_ifs with haN
  · have hmem : a ∈ Icc 1 (N n) := Finset.mem_Icc.2 ⟨ha1, haN⟩
    rw [← Finset.mul_prod_erase _ _ hmem]
    have h1 : (padicFil p).vge ((a : ℚ) ^ 2 - (r : ℚ) ^ 2) 1 := by
      have hc : cls p r = cls p a := by rw [(mem_Tset.1 hr).2, cls_of_le hm ha]
      have := vge_one_of_dvd (p := p) (dvd_sq_sub_sq hm hc)
      push_cast at this
      exact this
    have h2 : (padicFil p).vge (∏ x ∈ (Icc 1 (N n)).erase a, ((x : ℚ) ^ 2 - (r : ℚ) ^ 2)) 0 := by
      have := (padicFil p).vge_prod ((Icc 1 (N n)).erase a)
        (fun s => (s : ℚ) ^ 2 - (r : ℚ) ^ 2) (fun _ => 0) (fun s _ => vge_nat_sq_sub s r)
      simpa using this
    have := vge_pow ((padicFil p).vge_mul h1 h2) 5
    refine (padicFil p).vge_mono (le_of_eq ?_) this
    push_cast; ring
  · have h0 := (padicFil p).vge_prod (Icc 1 (N n))
      (fun s => (s : ℚ) ^ 2 - (r : ℚ) ^ 2) (fun _ => 0) (fun s _ => vge_nat_sq_sub s r)
    have h0' : (padicFil p).vge (∏ s ∈ Icc 1 (N n), ((s : ℚ) ^ 2 - (r : ℚ) ^ 2)) 0 := by
      simpa using h0
    have := vge_pow h0' 5
    refine (padicFil p).vge_mono (le_of_eq ?_) this
    push_cast; ring

end Valuations

/-! # §8 (proofs).  The entry bounds, case by case (p. 12) -/

section Cases

variable {n p : ℕ} [hpr : Fact p.Prime]

open Functional

omit hpr in
/-- **Cross-class entries**: "their quotients are polynomials with integral coefficients" —
`W·(P_a q)(P_b q')` is divisible by `D_tail`, so it has no residues at all. -/
lemma resSum_cross {a b : ℕ} (hab : a ≠ b) (i j : ℕ) :
    resSum n ((D (N n)) ^ 5 * (rowR ℚ n p a i * rowR ℚ n p b j)) = 0 := by
  classical
  have hunion : Pset n p a ∪ Pset n p b = tail n := by
    ext r
    simp only [Pset, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    · intro h
      by_cases hra : cls p r = a
      · exact Or.inr ⟨h, fun hrb => hab (hra ▸ hrb)⟩
      · exact Or.inl ⟨h, hra⟩
  have hui := Finset.prod_union_inter (s₁ := Pset n p a) (s₂ := Pset n p b) (f := linR ℚ)
  change prodR ℚ _ * prodR ℚ _ = prodR ℚ _ * prodR ℚ _ at hui
  rw [hunion] at hui
  have heq : (D (N n)) ^ 5 * (rowR ℚ n p a i * rowR ℚ n p b j)
      = ((D (N n)) ^ 5 * qR ℚ n p a i * qR ℚ n p b j * prodR ℚ (Pset n p a ∩ Pset n p b))
          * prodR ℚ (tail n \ ∅) := by
    rw [Finset.sdiff_empty]
    unfold rowR
    linear_combination (-((D (N n)) ^ 5 * qR ℚ n p a i * qR ℚ n p b j)) * hui
  rw [heq, resSum_formula (Finset.empty_subset _)]
  simp

omit hpr in
lemma qR_ord_small {a i : ℕ} (ha0 : a ≠ 0) (hi : i + 2 < ell p (K n) a) :
    qR ℚ n p a i = linR ℚ a ^ i := by
  simp [qR, ha0, hi]

omit hpr in
lemma qR_ord_large {a i : ℕ} (ha0 : a ≠ 0) (hi : ¬ i + 2 < ell p (K n) a) :
    qR ℚ n p a i = prodR ℚ (Eset n p a) * linR ℚ a ^ (i - (ell p (K n) a - 2)) := by
  simp [qR, ha0, hi]

/-- **Within a class, both indices `< ℓ − 2`**: "the residue part has valuation at least
`i + j + 6δ − ℓ − 4`.  The row factors supply `i + j`, the factor `W` supplies `5δ`, the node
derivative loses `ℓ − δ − 1`, and a harmonic value loses at most `5`" (p. 12). -/
lemma resSum_2a (hp : Hyp n p) {a i j : ℕ} (ha1 : 1 ≤ a) (ha : a ≤ mHalf p)
    (hi : i + 2 < ell p (K n) a) (hj : j + 2 < ell p (K n) a) :
    (gaussFil p).vge (resSum n ((D (N n)) ^ 5 * (rowR ℚ n p a i * rowR ℚ n p a j)))
      ((i : ℚ) + j + 6 * (((if a ≤ N n then 1 else 0 : ℕ)) : ℚ) - (ell p (K n) a : ℚ) - 4) := by
  classical
  have hm := hp.two_mHalf
  have ha0 : a ≠ 0 := by omega
  have heq : (D (N n)) ^ 5 * (rowR ℚ n p a i * rowR ℚ n p a j)
      = ((D (N n)) ^ 5 * prodR ℚ (Pset n p a) * linR ℚ a ^ (i + j))
          * prodR ℚ (tail n \ Tset n p a) := by
    rw [← Pset_eq_sdiff]
    unfold rowR
    rw [qR_ord_small ha0 hi, qR_ord_small ha0 hj, pow_add]
    ring
  rw [heq, resSum_formula (Tset_subset_tail a)]
  refine (gaussFil p).vge_sum _ _ _ fun r hr => ?_
  -- the numerator
  have hrT := mem_Tset.1 hr
  have hnum : (padicFil p).vge
      (((D (N n)) ^ 5 * prodR ℚ (Pset n p a) * linR ℚ a ^ (i + j)).eval (node r))
      (5 * (((if a ≤ N n then 1 else 0 : ℕ)) : ℚ) + 0 + ((i + j : ℕ) : ℚ)) := by
    have e3 : (linR ℚ a ^ (i + j)).eval (node r) = ((a : ℚ) ^ 2 - (r : ℚ) ^ 2) ^ (i + j) := by
      rw [eval_pow, linR_eval_node]
    rw [eval_mul, eval_mul, e3]
    have hlin : (padicFil p).vge ((a : ℚ) ^ 2 - (r : ℚ) ^ 2) 1 := by
      have hc : cls p r = cls p a := by rw [hrT.2, cls_of_le hm ha]
      have := vge_one_of_dvd (p := p) (dvd_sq_sub_sq hm hc)
      push_cast at this
      exact this
    have h3 := vge_pow hlin (i + j)
    exact (padicFil p).vge_mul ((padicFil p).vge_mul (vge_W_eval hp ha1 ha hr)
      (vge_prodR_eval _ r)) (by simpa using h3)
  obtain ⟨hden0, hdenv⟩ := val_node_derivative hp ha1 hr
  have hdiv := vge_div_val hnum hden0 hdenv
  have hpole := muPole_vge_neg_five hp.ge7 (r := r) (by omega) (by
    have := hp.sq; nlinarith [hrT.1.2])
  have hterm := (gaussFil p).vge_mul (OuterLocal.gaussGe_C hdiv) hpole
  refine (gaussFil p).vge_mono (le_of_eq ?_) hterm
  -- the arithmetic: `5δ + (i+j) − (|T_a| − 1) − 5 = i + j + 6δ − ℓ − 4`
  have hcard := card_Tset hp ha
  have hdim : dimO n p a = ell p (K n) a - (if a ≤ N n then 1 else 0) := by
    simp [dimO, ha0]
  have hpos : 1 ≤ (Tset n p a).card := Finset.card_pos.2 ⟨r, hr⟩
  have h1 : 1 ≤ ell p (K n) a - (if a ≤ N n then 1 else 0) := by
    rw [← hdim, ← hcard]; exact hpos
  have hδ : (if a ≤ N n then 1 else 0 : ℕ) ≤ ell p (K n) a := by omega
  rw [hcard, hdim, Nat.cast_sub h1, Nat.cast_sub hδ]
  push_cast
  ring

/-- **The divided difference** (p. 12): a partial-fraction sum over at most the two nodes
`a, p − a` of an ordinary class, with an integer numerator, is integral.  With both nodes
present this is "The two possible remaining pole values at `a` and `p − a` are integral and
congruent modulo `p` … The divided difference at the two nodes is therefore integral.
Polynomial numerators preserve this congruence." -/
lemma pairSum_vge (hp : Hyp n p) {a : ℕ} (ha1 : 1 ≤ a) (ha : a ≤ mHalf p) (Fz : ℤ[X])
    {S : Finset ℕ} (hS : S ⊆ {a, p - a}) :
    (gaussFil p).vge (∑ r ∈ S, C ((Fz.map (Int.castRingHom ℚ)).eval (node r)
        / ∏ s ∈ S.erase r, ((s : ℚ) ^ 2 - (r : ℚ) ^ 2)) * muPole r) 0 := by
  classical
  have hm := hp.two_mHalf
  have h7 := hp.ge7
  have hne : a ≠ p - a := by omega
  have hapos : 1 ≤ p - a := by omega
  have hap : a < p := by omega
  have hpap : p - a < p := by omega
  have hsingle : ∀ x, 1 ≤ x → x < p →
      (gaussFil p).vge (C ((Fz.map (Int.castRingHom ℚ)).eval (node x)) * muPole x) 0 := by
    intro x hx1 hxp
    have := (gaussFil p).vge_mul (OuterLocal.gaussGe_C (vge_eval_node_int (p := p) Fz x))
      (muPole_vge_zero h7 hx1 hxp)
    simpa using this
  by_cases h1 : a ∈ S <;> by_cases h2 : p - a ∈ S
  · -- both nodes: the divided difference
    have hSeq : S = {a, p - a} := by
      refine Finset.Subset.antisymm hS ?_
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact h1
      · exact h2
    subst hSeq
    have he1 : ({a, p - a} : Finset ℕ).erase a = {p - a} :=
      Finset.erase_insert (by simp [hne])
    have he2 : ({a, p - a} : Finset ℕ).erase (p - a) = {a} := by
      rw [Finset.erase_insert_of_ne hne, Finset.erase_singleton, Finset.insert_empty]
    rw [Finset.sum_pair hne, he1, he2, Finset.prod_singleton, Finset.prod_singleton]
    set Fa := (Fz.map (Int.castRingHom ℚ)).eval (node a) with hFa
    set Fb := (Fz.map (Int.castRingHom ℚ)).eval (node (p - a)) with hFb
    set d : ℚ := (((p - a : ℕ) : ℚ)) ^ 2 - (a : ℚ) ^ 2 with hd
    have hd0 : d ≠ 0 := sq_sub_sq_ne_zero (Ne.symm hne)
    have hneg : (a : ℚ) ^ 2 - (((p - a : ℕ) : ℚ)) ^ 2 = -d := by rw [hd]; ring
    have key : C (Fa / d) * muPole a + C (Fb / ((a : ℚ) ^ 2 - (((p - a : ℕ) : ℚ)) ^ 2))
          * muPole (p - a)
        = C Fa * (C d⁻¹ * (muPole a - muPole (p - a))) + C ((Fa - Fb) / d) * muPole (p - a) := by
      rw [hneg]
      simp only [div_eq_mul_inv, inv_neg, mul_neg, C_mul, C_neg, C_sub]
      ring
    rw [key]
    have hDD : (gaussFil p).vge (C d⁻¹ * (muPole a - muPole (p - a))) 0 := by
      have := OuterLocal.muPole_divided_difference (p := p) h7 ha1 (by omega)
      exact (gaussGe_intCast p _ 0).2 (by simpa [hd] using this)
    have hT1 := (gaussFil p).vge_mul (OuterLocal.gaussGe_C (vge_eval_node_int (p := p) Fz a)) hDD
    have hint : (padicFil p).vge ((Fa - Fb) / d) 0 := by
      obtain ⟨k, hk⟩ := Polynomial.sub_dvd_eval_sub (-(a : ℤ) ^ 2) (-((p - a : ℕ) : ℤ) ^ 2) Fz
      have hq : (Fa - Fb) / d = (k : ℚ) := by
        rw [hFa, hFb, eval_node_map_int, eval_node_map_int, ← Int.cast_sub, hk, div_eq_iff hd0,
          hd]
        push_cast
        ring
      rw [hq]
      exact vge_int k
    have hT2 := (gaussFil p).vge_mul (OuterLocal.gaussGe_C hint) (muPole_vge_zero h7 hapos hpap)
    have := (gaussFil p).vge_add hT1 hT2
    simpa using this
  · have hSeq : S = {a} := by
      refine Finset.Subset.antisymm ?_ (Finset.singleton_subset_iff.2 h1)
      intro x hx
      have := hS hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
      rcases this with rfl | rfl
      · rfl
      · exact absurd hx h2
    subst hSeq
    rw [Finset.sum_singleton, Finset.erase_singleton, Finset.prod_empty, div_one]
    exact hsingle a ha1 hap
  · have hSeq : S = {p - a} := by
      refine Finset.Subset.antisymm ?_ (Finset.singleton_subset_iff.2 h2)
      intro x hx
      have := hS hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
      rcases this with rfl | rfl
      · exact absurd hx h1
      · rfl
    subst hSeq
    rw [Finset.sum_singleton, Finset.erase_singleton, Finset.prod_empty, div_one]
    exact hsingle (p - a) hapos hpap
  · have hSeq : S = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro x hx
      have := hS hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with rfl | rfl
      · exact h1 hx
      · exact h2 hx
    subst hSeq
    rw [Finset.sum_empty]
    exact (gaussFil p).vge_zero _

/-- **Within a class, a row index `≥ ℓ − 2`**: "all poles with `j > p` cancel", and what is
left is the divided difference at `a, p − a`, which is integral. -/
lemma resSum_2b (hp : Hyp n p) {a i j : ℕ} (ha1 : 1 ≤ a) (ha : a ≤ mHalf p)
    (hi : ¬ i + 2 < ell p (K n) a) :
    (gaussFil p).vge (resSum n ((D (N n)) ^ 5 * (rowR ℚ n p a i * rowR ℚ n p a j))) 0 := by
  classical
  have ha0 : a ≠ 0 := by omega
  set i' := i - (ell p (K n) a - 2) with hi'
  have hdisj : Disjoint (Pset n p a) (Eset n p a) := by
    rw [Finset.disjoint_left]
    intro r h1 h2
    simp only [Pset, Eset, Tset, Finset.mem_filter] at h1 h2
    exact h1.2 h2.1.2
  have hunion : Pset n p a ∪ Eset n p a = tail n \ Cset n p a := by
    ext r
    simp only [Pset, Eset, Cset, Tset, Finset.mem_union, Finset.mem_filter, Finset.mem_sdiff]
    tauto
  have heq : (D (N n)) ^ 5 * (rowR ℚ n p a i * rowR ℚ n p a j)
      = ((D (N n)) ^ 5 * prodR ℚ (Pset n p a) * linR ℚ a ^ i' * qR ℚ n p a j)
          * prodR ℚ (tail n \ Cset n p a) := by
    unfold rowR
    rw [qR_ord_large ha0 hi, ← hunion, ← prodR_mul_prodR hdisj]
    ring
  have hF : (D (N n)) ^ 5 * prodR ℚ (Pset n p a) * linR ℚ a ^ i' * qR ℚ n p a j
      = (prodR ℤ (Icc 1 (N n)) ^ 5 * prodR ℤ (Pset n p a) * linR ℤ a ^ i'
          * qR ℤ n p a j).map (Int.castRingHom ℚ) := by
    simp [Polynomial.map_mul, Polynomial.map_pow, prodR_map, linR_map, qR_map, D_eq_prodR]
  have hCt : Cset n p a ⊆ tail n :=
    (Finset.filter_subset _ _).trans (Tset_subset_tail a)
  rw [heq, resSum_formula hCt, hF]
  exact pairSum_vge hp ha1 ha _ (Cset_subset hp ha1 ha)

lemma val_three_p_sq (h7 : 7 ≤ p) :
    padicValRat p ((((2 * p : ℕ)) : ℚ) ^ 2 - (p : ℚ) ^ 2) = 2 := by
  have h3 : padicValRat p (3 : ℚ) = 0 := by
    have := padicValRat_ne_zero_unit (p := p) (m := 3) (by norm_num)
      (fun hd => by have := Nat.le_of_dvd (by norm_num) hd; omega)
    simpa using this
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hpr.out.ne_zero
  have heq : (((2 * p : ℕ)) : ℚ) ^ 2 - (p : ℚ) ^ 2 = 3 * (p : ℚ) ^ 2 := by push_cast; ring
  rw [heq, padicValRat.mul (by norm_num) (pow_ne_zero 2 hp0), h3, padicValRat.pow,
    padicValRat.self hpr.out.one_lt]
  ring

lemma val_three_p_sq' (h7 : 7 ≤ p) :
    padicValRat p ((p : ℚ) ^ 2 - (((2 * p : ℕ)) : ℚ) ^ 2) = 2 := by
  rw [show (p : ℚ) ^ 2 - (((2 * p : ℕ)) : ℚ) ^ 2 = -((((2 * p : ℕ)) : ℚ) ^ 2 - (p : ℚ) ^ 2) by ring,
    padicValRat.neg, val_three_p_sq h7]

lemma vge_WP_eval (S : Finset ℕ) (r : ℕ) :
    (padicFil p).vge (((D (N n)) ^ 5 * prodR ℚ S).eval (node r)) 0 := by
  rw [eval_mul, eval_pow, D_eq_prodR]
  have := (padicFil p).vge_mul (vge_pow (vge_prodR_eval (p := p) (Icc 1 (N n)) r) 5)
    (vge_prodR_eval (p := p) S r)
  simpa using this

/-- **The zero class** (p. 12): "A single zero-class pole has weight `−1/2`.  For two
zero-class poles `p, 2p`, the rows `1, t + p²` give entry bounds `−3, −1, 0`, so the weights
`−2, 0` are valid." -/
lemma resSum_zero (hp : Hyp n p) {i j : ℕ} (hi : i < mFloor p (K n)) (hj : j < mFloor p (K n)) :
    (gaussFil p).vge (resSum n ((D (N n)) ^ 5 * (rowR ℚ n p 0 i * rowR ℚ n p 0 j)))
      (((wtO n p 0 i + wtO n p 0 j : ℤ) : ℚ) / 2) := by
  classical
  have h7 := hp.ge7
  have hle2 := mFloor_le_two hp
  have hq0 : qR ℚ n p 0 0 = 1 := by simp [qR]
  have hq1 : qR ℚ n p 0 1 = linR ℚ p := by simp [qR]
  have hP : Pset n p 0 = tail n \ Tset n p 0 := Pset_eq_sdiff 0
  have hpsq : p < p ^ 2 := by nlinarith
  have h2psq : 2 * p < p ^ 2 := by nlinarith
  have hmuP : (gaussFil p).vge (muPole p) (-1) :=
    muPole_vge_neg_one h7 (by omega) hpsq (dvd_refl p)
  have hmu2P : (gaussFil p).vge (muPole (2 * p)) (-1) :=
    muPole_vge_neg_one h7 (by omega) h2psq (dvd_mul_left p 2)
  have hdiag : (D (N n)) ^ 5 * (rowR ℚ n p 0 0 * rowR ℚ n p 0 0)
      = ((D (N n)) ^ 5 * prodR ℚ (Pset n p 0)) * prodR ℚ (tail n \ Tset n p 0) := by
    unfold rowR; rw [hq0, ← hP]; ring
  rcases (show mFloor p (K n) = 1 ∨ mFloor p (K n) = 2 by omega) with h1 | h2
  · -- one zero-class pole, `p`: weight `−1/2`
    have hi0 : i = 0 := by omega
    have hj0 : j = 0 := by omega
    subst hi0 hj0
    have hw : wtO n p 0 0 = -1 := by simp [wtO, h1]
    rw [hw, hdiag, resSum_formula (Tset_subset_tail 0), Tset_zero_one hp h1,
      Finset.sum_singleton, Finset.erase_singleton, Finset.prod_empty, div_one]
    have := (gaussFil p).vge_mul
      (OuterLocal.gaussGe_C (vge_WP_eval (p := p) (n := n) (Pset n p 0) p)) hmuP
    refine (gaussFil p).vge_mono (by norm_num) this
  · -- two zero-class poles, `p` and `2p`: weights `−2, 0`
    have hT := Tset_zero_two hp h2
    have hpT : p ∈ tail n := Tset_subset_tail 0 (by rw [hT]; simp)
    have h2pT : 2 * p ∈ tail n := Tset_subset_tail 0 (by rw [hT]; simp)
    have hne : p ≠ 2 * p := by omega
    have hdisj : Disjoint (Pset n p 0) {p} := by
      rw [Finset.disjoint_singleton_right, hP, hT]
      simp
    have hU : Pset n p 0 ∪ {p} = tail n \ {2 * p} := by
      rw [hP, hT]
      ext r
      simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro (⟨h1, h2⟩ | rfl)
        · exact ⟨h1, fun h => h2 (Or.inr h)⟩
        · exact ⟨hpT, hne⟩
      · rintro ⟨h1, h2⟩
        by_cases hrp : r = p
        · exact Or.inr hrp
        · exact Or.inl ⟨h1, fun h => h.elim hrp h2⟩
    have hPp : prodR ℚ (Pset n p 0) * linR ℚ p = prodR ℚ (tail n \ {2 * p}) := by
      rw [← hU, ← prodR_mul_prodR hdisj, prodR, prodR, Finset.prod_singleton]
    have hS2 : ({2 * p} : Finset ℕ) ⊆ tail n := Finset.singleton_subset_iff.2 h2pT
    have hw0 : wtO n p 0 0 = -4 := by simp [wtO, h2]
    have hw1 : wtO n p 0 1 = 0 := by simp [wtO, h2]
    -- the off-diagonal entry `(1, t+p²)`
    have hoff : (gaussFil p).vge
        (resSum n ((D (N n)) ^ 5 * (rowR ℚ n p 0 0 * rowR ℚ n p 0 1))) (-1) := by
      have heq : (D (N n)) ^ 5 * (rowR ℚ n p 0 0 * rowR ℚ n p 0 1)
          = ((D (N n)) ^ 5 * prodR ℚ (Pset n p 0)) * prodR ℚ (tail n \ {2 * p}) := by
        unfold rowR; rw [hq0, hq1, ← hPp]; ring
      rw [heq, resSum_formula hS2, Finset.sum_singleton, Finset.erase_singleton,
        Finset.prod_empty, div_one]
      have := (gaussFil p).vge_mul
        (OuterLocal.gaussGe_C (vge_WP_eval (p := p) (n := n) (Pset n p 0) (2 * p))) hmu2P
      simpa using this
    rw [h2] at hi hj
    interval_cases i <;> interval_cases j
    · -- `(1, 1)`: entry bound `−3`
      rw [hw0, hdiag, resSum_formula (Tset_subset_tail 0), hT, Finset.sum_pair hne]
      have he1 : ({p, 2 * p} : Finset ℕ).erase p = {2 * p} :=
        Finset.erase_insert (by simp [hne])
      have he2 : ({p, 2 * p} : Finset ℕ).erase (2 * p) = {p} := by
        rw [Finset.erase_insert_of_ne hne, Finset.erase_singleton, Finset.insert_empty]
      rw [he1, he2, Finset.prod_singleton, Finset.prod_singleton]
      have t1 := (gaussFil p).vge_mul (OuterLocal.gaussGe_C (vge_div_val
        (vge_WP_eval (p := p) (n := n) (Pset n p 0) p) (sq_sub_sq_ne_zero hne.symm)
        (val_three_p_sq h7))) hmuP
      have t2 := (gaussFil p).vge_mul (OuterLocal.gaussGe_C (vge_div_val
        (vge_WP_eval (p := p) (n := n) (Pset n p 0) (2 * p)) (sq_sub_sq_ne_zero hne)
        (val_three_p_sq' h7))) hmu2P
      have := (gaussFil p).vge_add t1 ((gaussFil p).vge_mono (le_refl _) t2)
      refine (gaussFil p).vge_mono (by norm_num) this
    · -- `(1, t+p²)`: entry bound `−1`
      rw [hw0, hw1]
      exact (gaussFil p).vge_mono (by norm_num) hoff
    · -- `(t+p², 1)`
      rw [hw0, hw1, mul_comm (rowR ℚ n p 0 1)]
      exact (gaussFil p).vge_mono (by norm_num) hoff
    · -- `(t+p², t+p²)`: entry bound `0`
      rw [hw1]
      have heq : (D (N n)) ^ 5 * (rowR ℚ n p 0 1 * rowR ℚ n p 0 1)
          = ((D (N n)) ^ 5 * prodR ℚ (Pset n p 0) * linR ℚ p) * prodR ℚ (tail n \ {2 * p}) := by
        unfold rowR; rw [hq1, ← hPp]; ring
      rw [heq, resSum_formula hS2, Finset.sum_singleton, Finset.erase_singleton,
        Finset.prod_empty, div_one]
      have hlin : (padicFil p).vge ((linR ℚ p).eval (node (2 * p))) 2 := by
        rw [linR_eval_node]
        refine Or.inr ?_
        rw [val_three_p_sq' h7]
        norm_num
      have hF : (padicFil p).vge
          (((D (N n)) ^ 5 * prodR ℚ (Pset n p 0) * linR ℚ p).eval (node (2 * p))) (0 + 2) := by
        rw [eval_mul]
        exact (padicFil p).vge_mul (vge_WP_eval _ _) hlin
      have := (gaussFil p).vge_mul (OuterLocal.gaussGe_C hF) hmu2P
      refine (gaussFil p).vge_mono (by norm_num) this

end Cases

/-! # The five components of `outer_local_core` -/

/-- (4.10) splitting of the functional. -/
theorem muOver_split (n p : ℕ) (hp0 : p ≠ 0) (A : ℚ[X]) :
    muOver n A = muOver0 n p A + C (1 / (p : ℚ)) * muL n p A := by
  unfold muOver muOver0 muL muPolyW mu0 muPoly
  rw [add_right_comm, ← C_mul, ← C_add, Finset.mul_sum, ← Finset.sum_add_distrib]
  congr 2
  refine Finset.sum_congr rfl fun e _ => ?_
  field_simp
  ring

theorem Gram_split (n p : ℕ) (hp0 : p ≠ 0) (U : Matrix (Fin (h n)) (Fin (h n)) ℚ) :
    OuterLocal.Gram n U = Aq n p U + C (1 / (p : ℚ)) • Lq n p U := by
  ext u v : 1
  simp only [OuterLocal.Gram, OuterLocal.Bil, Aq, Lq, Matrix.add_apply, Matrix.smul_apply,
    Matrix.of_apply, smul_eq_mul]
  exact muOver_split n p hp0 _

theorem rank_Lq {n p : ℕ} [Fact p.Prime] (hp : Hyp n p) (U : Matrix (Fin (h n)) (Fin (h n)) ℚ) :
    ((Lq n p U).map (algebraMap ℚ[X] (RatFunc ℚ))).rank ≤ (rOut n p).toNat := by
  rw [Lq_eq, Matrix.map_mul, Matrix.map_mul]
  refine le_trans (Matrix.rank_mul_le_left _ _) ?_
  refine le_trans (Matrix.rank_mul_le_right _ _) ?_
  exact rank_L0 hp

/-- The rows reduce modulo `p` to the Hermite basis. -/
theorem rowR_hermite {n p : ℕ} [Fact p.Prime] (hp : Hyp n p) (a : Fin (mHalf p + 1)) (i : ℕ)
    (hi : i < dimO n p a) :
    rowR (ZMod p) n p a i
      = HermiteBasis.hermitePoly (fun c : Fin (mHalf p + 1) => (((c : ℕ) : ZMod p)) ^ 2)
          (fun c => dimO n p (c : ℕ)) a i :=
  rowR_hermite' hp a i hi

theorem rowR_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (n p a i : ℕ) :
    (rowR R n p a i).map f = rowR S n p a i :=
  rowR_map' f n p a i

theorem rowR_monic (R : Type*) [CommRing R] (n p a i : ℕ) : (rowR R n p a i).Monic :=
  (prodR_monic _).mul (qR_monic _ _ _ _)

lemma wtO_nonpos (n p a i : ℕ) : wtO n p a i ≤ 0 := by
  unfold wtO
  split_ifs <;> norm_num

/-- **The entry bound behind (4.12)**: `v_p^G(A_{uv}) ≥ w_u + w_v` for every pair of rows of
the basis (4.11) and the zero-class rows (doubled weights `W = 2w`). -/
theorem entry_bound {n p : ℕ} [Fact p.Prime] (hp : Hyp n p) {a i b j : ℕ}
    (ha : a ≤ mHalf p) (hi : i < dimO n p a) (hb : b ≤ mHalf p) (hj : j < dimO n p b) :
    (gaussFil p).vge (muOver0 n p ((D (N n)) ^ 5 * (rowR ℚ n p a i * rowR ℚ n p b j)))
      (((wtO n p a i + wtO n p b j : ℤ) : ℚ) / 2) := by
  have hw0 : (((wtO n p a i + wtO n p b j : ℤ) : ℚ) / 2) ≤ 0 := by
    have h1 := wtO_nonpos n p a i
    have h2 := wtO_nonpos n p b j
    have h3 : ((wtO n p a i + wtO n p b j : ℤ) : ℚ) ≤ 0 := by exact_mod_cast (by omega)
    linarith
  rw [muOver0_eq]
  refine (gaussFil p).vge_add ((gaussFil p).vge_mono hw0 (polyPart_int hp a i b j)) ?_
  by_cases hab : a = b
  · subst hab
    by_cases ha0 : a = 0
    · subst ha0
      have hi' : i < mFloor p (K n) := by simpa [dimO] using hi
      have hj' : j < mFloor p (K n) := by simpa [dimO] using hj
      exact resSum_zero hp hi' hj'
    · have ha1 : 1 ≤ a := by omega
      by_cases hi2 : i + 2 < ell p (K n) a
      · by_cases hj2 : j + 2 < ell p (K n) a
        · -- both indices `< ℓ − 2`
          refine (gaussFil p).vge_mono ?_ (resSum_2a hp ha1 ha hi2 hj2)
          have hwi : wtO n p a i ≤ 2 * (i : ℤ) + 6 * (((if a ≤ N n then 1 else 0 : ℕ)) : ℤ)
              - (ell p (K n) a : ℤ) - 4 := by
            simp only [wtO, ha0, hi2, ↓reduceIte]; exact min_le_right _ _
          have hwj : wtO n p a j ≤ 2 * (j : ℤ) + 6 * (((if a ≤ N n then 1 else 0 : ℕ)) : ℤ)
              - (ell p (K n) a : ℤ) - 4 := by
            simp only [wtO, ha0, hj2, ↓reduceIte]; exact min_le_right _ _
          have hint : wtO n p a i + wtO n p a j ≤ 2 * ((i : ℤ) + j
              + 6 * (((if a ≤ N n then 1 else 0 : ℕ)) : ℤ) - (ell p (K n) a : ℤ) - 4) := by
            linarith
          have hq : ((wtO n p a i + wtO n p a j : ℤ) : ℚ) ≤ ((2 * ((i : ℤ) + j
              + 6 * (((if a ≤ N n then 1 else 0 : ℕ)) : ℤ) - (ell p (K n) a : ℤ) - 4) : ℤ) : ℚ) := by
            exact_mod_cast hint
          push_cast at hq ⊢
          linarith
        · -- the column index is `≥ ℓ − 2`
          rw [mul_comm (rowR ℚ n p a i)]
          exact (gaussFil p).vge_mono hw0 (resSum_2b hp ha1 ha hj2)
      · exact (gaussFil p).vge_mono hw0 (resSum_2b hp ha1 ha hi2)
  · rw [resSum_cross hab]
    exact (gaussFil p).vge_zero _

/-- `L` is integral. -/
theorem muL_int {n p : ℕ} [Fact p.Prime] (a i b j : ℕ) :
    vGAtLeast p (muL n p ((D (N n)) ^ 5 * (rowR ℚ n p a i * rowR ℚ n p b j))) 0 := by
  rw [← gaussGe_intCast, muL, entryNum_map, divByMonic_map_int]
  exact OuterLocal.gaussGe_C (muPolyW_int_of_int _ (fun e => OuterLocal.PInt.intCast _) _)

/-! # §9.  Assembly -/

/-- **The local analysis of §4.2**, in the form `Zeta5.outer_local_analysis` needs, with the
row count and weight function passed as parameters (`OuterRange.lean` instantiates them by
`outerDim` and `outerWeight`, which are definitionally `dimO` and `wtO`). -/
theorem outer_local_core (n p : ℕ) [Fact p.Prime] (hp : Hyp n p)
    (dim : ℕ → ℕ) (hdim : dim = dimO n p)
    (wt : (Σ a : Fin (mHalf p + 1), Fin (dim (a : ℕ))) → ℤ)
    (hwt : ∀ ρ, wt ρ = wtO n p (ρ.1 : ℕ) (ρ.2 : ℕ))
    (hcard : Fintype.card (Σ a : Fin (mHalf p + 1), Fin (dim (a : ℕ))) = h n) :
    ∃ (Aq L : Matrix (Fin (h n)) (Fin (h n)) ℚ[X]) (W : Fin (h n) → ℤ)
      (eρ : (Σ a : Fin (mHalf p + 1), Fin (dim (a : ℕ))) ≃ Fin (h n)) (pinv : ℚ[X]) (c : ℚ),
      (∀ ρ, W (eρ ρ) = wt ρ)
      ∧ (∀ i j, (gaussFil p).vge (Aq i j) (((W i + W j : ℤ) : ℚ) / 2))
      ∧ (gaussFil p).vge pinv (-1)
      ∧ (∀ i j, vGAtLeast p (L i j) 0)
      ∧ (L.map (algebraMap ℚ[X] (RatFunc ℚ))).rank ≤ (rOut n p).toNat
      ∧ padicValRat p c = 0
      ∧ Delta n = Polynomial.C c * (Aq + pinv • L).det := by
  subst hdim
  classical
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  let eρ := Fintype.equivFinOfCardEq hcard
  let σ := eρ.symm
  let g : Fin (h n) → ℤ[X] := fun k => rowR ℤ n p (σ k).1 (σ k).2
  have hg : ∀ k, (g k).map (Int.castRingHom (ZMod p))
      = HermiteBasis.hermitePoly (fun c : Fin (mHalf p + 1) => (((c : ℕ) : ZMod p)) ^ 2)
          (fun c => dimO n p (c : ℕ)) (σ k).1 ((σ k).2 : ℕ) := by
    intro k
    rw [rowR_map]
    exact rowR_hermite hp (σ k).1 (σ k).2 (σ k).2.isLt
  obtain ⟨h0, hv⟩ := HermiteBasis.det_coeffMatrix_unimodular
    (fun c : Fin (mHalf p + 1) => (((c : ℕ) : ZMod p)) ^ 2) HermiteBasis.sq_injective_half
    (fun c => dimO n p (c : ℕ)) σ g hg
  set U := HermiteBasis.coeffMatrix fun k => (g k).map (Int.castRingHom ℚ) with hU
  -- the row polynomials of `U` are the rows (4.11)
  have hcardsum : ∑ c : Fin (mHalf p + 1), dimO n p (c : ℕ) = h n := by
    rw [← hcard, Fintype.card_sigma]
    simp
  have hdeg : ∀ k, ((g k).map (Int.castRingHom ℚ)).natDegree < h n := by
    intro k
    have hmon := rowR_monic ℤ n p (σ k).1 (σ k).2
    rw [Monic.natDegree_map hmon]
    rw [← Monic.natDegree_map hmon (Int.castRingHom (ZMod p)), hg k,
      HermiteBasis.hermitePoly_natDegree]
    have hs := Finset.add_sum_erase (Finset.univ) (fun c : Fin (mHalf p + 1) => dimO n p (c : ℕ))
      (Finset.mem_univ (σ k).1)
    have := (σ k).2.isLt
    omega
  have hrow : ∀ k, OuterLocal.rowPoly U k = rowR ℚ n p (σ k).1 (σ k).2 := by
    intro k
    have := HermiteBasis.coeffMatrix_row_sum (fun k => (g k).map (Int.castRingHom ℚ)) k (hdeg k)
    rw [OuterLocal.rowPoly, ← hU] at *
    rw [this, rowR_map]
  refine ⟨Aq n p U, Lq n p U, fun k => wtO n p (σ k).1 (σ k).2, eρ, C (1 / (p : ℚ)),
    (U.det ^ 2)⁻¹, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ρ
    have hρ : σ (eρ ρ) = ρ := eρ.symm_apply_apply ρ
    show wtO n p (σ (eρ ρ)).1 (σ (eρ ρ)).2 = wt ρ
    rw [hρ]
    exact (hwt ρ).symm
  · intro i j
    simp only [Aq, Matrix.of_apply, hrow]
    exact entry_bound hp (Nat.lt_succ_iff.1 (σ i).1.isLt) (σ i).2.isLt
      (Nat.lt_succ_iff.1 (σ j).1.isLt) (σ j).2.isLt
  · refine OuterLocal.gaussGe_C (Or.inr ?_)
    rw [one_div, padicValRat.inv, padicValRat.self (Fact.out : p.Prime).one_lt]
    norm_num
  · intro i j
    simp only [Lq, Matrix.of_apply, hrow]
    exact muL_int _ _ _ _
  · exact rank_Lq hp U
  · exact OuterLocal.padicValRat_unimodular U hv
  · rw [OuterLocal.Delta_eq_of_basis U h0, Gram_split n p hp0 U]

/-! # Axiom checks -/

section Audit

#print axioms Zeta5.OuterBasis.outer_local_core
#print axioms Zeta5.OuterBasis.entry_bound
#print axioms Zeta5.OuterBasis.rank_Lq
#print axioms Zeta5.OuterBasis.muL_int
#print axioms Zeta5.OuterBasis.rowR_hermite
#print axioms Zeta5.OuterBasis.Gram_split
#print axioms Zeta5.OuterBasis.mu0_int

end Audit

end

end OuterBasis

end Zeta5
