/-
Zeta5/OuterLocal.lean

**The `p`-adic local analysis of §4.2 (pp. 11–12): arithmetic used by `outer_local_analysis`.**

`Zeta5/OuterRange.lean` reduces Proposition 4.3 to the local statement
`Zeta5.outer_local_analysis`, proved in `Zeta5/OuterBasis.lean`.  This file proves the
congruence `H^{(5)}_{p−a} ≡ H^{(5)}_{a−1} (mod p)` for `p ≥ 7`, the divided-difference
integrality, the `p`-adic toolkit they need, and the change-of-basis identity that turns the
basis (4.11) into a determinant.

WHAT IS PROVED HERE:

*  **§1.  A `p`-adic congruence calculus on `ℚ`** (`PInt`, `PCong`) built on
   `Zeta5.padicFil` of `Lemma42.lean`: the ring rules, and the two concrete facts
   `v_p((z : ℚ)) ≥ 1` for `p ∣ z` and `v_p((v : ℚ)) = 0` for `0 < v < p`.

*  **§2.  The harmonic congruences.**
   - `H5_p_sub_one_congr_zero`: `H^{(5)}_{p−1} = ∑_{v=1}^{p−1} v^{−5} ≡ 0 (mod p)` for
     every prime `p ≥ 7`.  The proof is the elementary pairing `v ↔ p − v`, which needs no
     primitive root: `v^{−5} + (p−v)^{−5}` has numerator `v⁵ + (p−v)⁵`, divisible by
     `v + (p−v) = p`.
   - `H5_congr`: **`H^{(5)}_{p−a} ≡ H^{(5)}_{a−1} (mod p)`**, the congruence the paper cites
     on p. 12, for `1 ≤ a < p`.

*  **§3.  The pole-value congruence, with the `−1/4 + 1/(2j)` tail.**
   `muPole_congr`: `v_p^G(μ_X(1/(t+a²)) − μ_X(1/(t+(p−a)²))) ≥ 1`, i.e. "The two possible
   remaining pole values at `a` and `p − a` are integral and congruent modulo `p`" (p. 12).

   This is the point the referee audit of the preprint singles out
   (see README, "Provenance"): the paper cites
   only `H^{(5)}_{p−a} ≡ H^{(5)}_{a−1}`, and **that congruence alone is not enough**.  The
   difference of the two values of (2.3) is
   `a⁴(H^{(5)}_{p−a} − H^{(5)}_a) + 1/(2a) + 1/(2a) ≡ −a⁴·a^{−5} + 1/a = 0`,
   so it is exactly the `+1/(2j)` of the tail of (2.3) that cancels the `−a^{−1}` coming from
   the harmonic congruence; the `−1/4` cancels against itself.  `muPole_tail_is_needed`
   (with `neg_inv_not_congr_zero`) records the failure of the truncated form, so the rôle of
   the tail is machine-checked and not merely asserted.

*  **§4.  The divided difference.**  `node_sub_valuation`: `v_p((p−a)² − a²) = 1` exactly, for
   `1 ≤ a ≤ (p−1)/2` — "distinct near poles differ by a `p`-adic unit", the separation of the
   two nodes of a class that survives `E_a`.  `divided_difference_int`: a difference quotient
   of two `p`-integral, `p`-congruent values at two nodes separated by exactly `p` is
   `p`-integral.  `muPole_divided_difference`: the two combined — "The divided difference at
   the two nodes is therefore integral."

*  **§5.  The change of basis.**  `muOver` is `ℚ`-linear (`Functional.lean`), so the entries
   of `G_K` are the Gram matrix of the `ℚ`-bilinear form `Bil f g = μ_X(W f g/D_tail)` in the
   monomial basis.  `gram_basis_change` is `Gram(U) = U G_K Uᵀ` for any `U` over `ℚ`, and
   `Delta_eq_of_basis` is the consequence Proposition 4.3 needs:
   `Δ_K = (det U)^{-2} · det Gram(U)`, with `padicValRat_unimodular` giving
   `v_p((det U)^{-2}) = 0` when `U` is `ℤ_p`-unimodular.  This is "The basis change is
   unimodular, which proves the proposition" made into an identity.

The entry bounds behind the weights (4.12) and the unimodularity of the basis (4.11) are
proved in `Zeta5/OuterBasis.lean`.

A NOTE ON (4.10).  `Zeta5.outer_local_analysis` states the rank bound of (4.10) in its
literal form `rank_{ℚ_p} L ≤ r_p`, which `Zeta5.lemma_4_2_gauss_rank` (`OuterRange.lean`)
consumes, not in the "vanishing columns" form — a set `C` of columns on which `L` vanishes,
with at most `r_p` columns outside `C`.  That form is correct in the **monomial** basis,
which is where the paper proves it ("Its first `h − r_p` rows and columns vanish"), but it is
**false in the basis (4.11)**, where the matrices of (4.10) live: every row of (4.11) has
degree between `h − 6` and `h − 1`, so the degree count that makes columns vanish never
applies, and an exact computation of the paper's `L` in the basis (4.11) at `K = 40` finds
**zero** vanishing columns at `p = 17, 19, 23` (where `h − r_p = 17, 21, 29` of them would be
needed), while `rank_ℚ L = r_p` exactly (the referee audit).
-/
import Zeta5.Lemma42
import Zeta5.Functional
import Zeta5.HermiteBasis

namespace Zeta5

open Polynomial Finset

noncomputable section

namespace OuterLocal

/-! # §1.  A `p`-adic congruence calculus on `ℚ`

`Zeta5.padicFil p` of `Lemma42.lean` is the `p`-adic valuation on `ℚ` packaged as a
`ValFil`, i.e. as the predicate `v_p(x) ≥ c` with `v_p(0) = ∞`.  `PInt p x` is `v_p(x) ≥ 0`
("`x ∈ ℤ_p`") and `PCong p x y` is `v_p(x − y) ≥ 1` ("`x ≡ y (mod p)`"). -/

variable {p : ℕ} [Fact p.Prime]

/-- `x ∈ ℤ_p`. -/
def PInt (p : ℕ) [Fact p.Prime] (x : ℚ) : Prop := (padicFil p).vge x 0

/-- `x ≡ y (mod p)`, for `x, y ∈ ℚ` (with the convention `v_p(0) = ∞`, so `0 ≡ 0`). -/
def PCong (p : ℕ) [Fact p.Prime] (x y : ℚ) : Prop := (padicFil p).vge (x - y) 1

/-! ### The ring rules -/

theorem PInt.zero : PInt p 0 := (padicFil p).vge_zero _

theorem PInt.one : PInt p 1 := (padicFil p).vge_one

theorem PInt.add {x y : ℚ} (hx : PInt p x) (hy : PInt p y) : PInt p (x + y) :=
  (padicFil p).vge_add hx hy

theorem PInt.neg {x : ℚ} (hx : PInt p x) : PInt p (-x) := (padicFil p).vge_neg hx

theorem PInt.sub {x y : ℚ} (hx : PInt p x) (hy : PInt p y) : PInt p (x - y) := by
  rw [PInt, sub_eq_add_neg]; exact hx.add hy.neg

theorem PInt.mul {x y : ℚ} (hx : PInt p x) (hy : PInt p y) : PInt p (x * y) :=
  (padicFil p).vge_mono (by norm_num) ((padicFil p).vge_mul hx hy)

theorem PInt.pow {x : ℚ} (hx : PInt p x) (k : ℕ) : PInt p (x ^ k) := by
  induction k with
  | zero => rw [PInt, pow_zero]; exact PInt.one
  | succ k ih => rw [PInt, pow_succ]; exact ih.mul hx

theorem PInt.sum {ι : Type*} (s : Finset ι) (f : ι → ℚ) (hf : ∀ i ∈ s, PInt p (f i)) :
    PInt p (∑ i ∈ s, f i) := (padicFil p).vge_sum s f 0 hf

theorem PCong.refl (x : ℚ) : PCong p x x := by
  rw [PCong, sub_self]; exact (padicFil p).vge_zero _

theorem PCong.symm {x y : ℚ} (h : PCong p x y) : PCong p y x := by
  have hn := (padicFil p).vge_neg h
  have heq : -(x - y) = y - x := by ring
  rw [heq] at hn
  exact hn

theorem PCong.trans {x y z : ℚ} (h1 : PCong p x y) (h2 : PCong p y z) : PCong p x z := by
  have ha := (padicFil p).vge_add h1 h2
  have heq : x - y + (y - z) = x - z := by ring
  rw [heq] at ha
  exact ha

theorem PCong.add {x y z w : ℚ} (h1 : PCong p x z) (h2 : PCong p y w) :
    PCong p (x + y) (z + w) := by
  have ha := (padicFil p).vge_add h1 h2
  have heq : x - z + (y - w) = x + y - (z + w) := by ring
  rw [heq] at ha
  exact ha

theorem PCong.neg {x y : ℚ} (h : PCong p x y) : PCong p (-x) (-y) := by
  have hn := (padicFil p).vge_neg h
  have heq : -(x - y) = -x - -y := by ring
  rw [heq] at hn
  exact hn

theorem PCong.sub {x y z w : ℚ} (h1 : PCong p x z) (h2 : PCong p y w) :
    PCong p (x - y) (z - w) := by
  have ha := (padicFil p).vge_add h1 ((padicFil p).vge_neg h2)
  have heq : x - z + -(y - w) = x - y - (z - w) := by ring
  rw [heq] at ha
  exact ha

/-- `x ≡ z`, `y ≡ w`, and `x, w ∈ ℤ_p`, give `xy ≡ zw`: `xy − zw = x(y−w) + (x−z)w`. -/
theorem PCong.mul {x y z w : ℚ} (hx : PInt p x) (hw : PInt p w)
    (h1 : PCong p x z) (h2 : PCong p y w) : PCong p (x * y) (z * w) := by
  have t1 : (padicFil p).vge (x * (y - w)) 1 :=
    (padicFil p).vge_mono (by norm_num) ((padicFil p).vge_mul hx h2)
  have t2 : (padicFil p).vge ((x - z) * w) 1 :=
    (padicFil p).vge_mono (by norm_num) ((padicFil p).vge_mul h1 hw)
  have ha := (padicFil p).vge_add t1 t2
  have heq : x * (y - w) + (x - z) * w = x * y - z * w := by ring
  rw [heq] at ha
  exact ha

/-- A `p`-congruence is preserved by multiplication by a `p`-adic integer. -/
theorem PCong.mul_left {c x y : ℚ} (hc : PInt p c) (h : PCong p x y) :
    PCong p (c * x) (c * y) := by
  have t1 : (padicFil p).vge (c * (x - y)) 1 :=
    (padicFil p).vge_mono (by norm_num) ((padicFil p).vge_mul hc h)
  have heq : c * (x - y) = c * x - c * y := by ring
  rw [heq] at t1
  exact t1

theorem PCong.sum {ι : Type*} (s : Finset ι) (f g : ι → ℚ) (h : ∀ i ∈ s, PCong p (f i) (g i)) :
    PCong p (∑ i ∈ s, f i) (∑ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.sum_empty, Finset.sum_empty]
      exact PCong.refl 0
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact (h a (Finset.mem_insert_self _ _)).add
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- `x ≡ y (mod p)` and `y ∈ ℤ_p` give `x ∈ ℤ_p`. -/
theorem PInt.of_PCong {x y : ℚ} (h : PCong p x y) (hy : PInt p y) : PInt p x := by
  have h0 : (padicFil p).vge (x - y) 0 := (padicFil p).vge_mono (by norm_num) h
  have ha := (padicFil p).vge_add h0 hy
  have heq : x - y + y = x := by ring
  rw [heq] at ha
  exact ha

/-! ### The two concrete inputs -/

omit [Fact p.Prime] in
theorem padicValRat_natCast (p v : ℕ) : padicValRat p (v : ℚ) = padicValNat p v := by
  have hc : ((v : ℕ) : ℚ) = ((v : ℤ) : ℚ) := by push_cast; ring
  rw [hc, padicValRat.of_int]
  simp [padicValInt]

/-- Every integer is a `p`-adic integer. -/
theorem PInt.intCast (z : ℤ) : PInt p (z : ℚ) := by
  rcases eq_or_ne ((z : ℚ)) 0 with h | h
  · exact Or.inl h
  · refine Or.inr ?_
    rw [padicValRat.of_int]
    positivity

theorem PInt.natCast (v : ℕ) : PInt p (v : ℚ) := by
  have : ((v : ℕ) : ℚ) = ((v : ℤ) : ℚ) := by push_cast; ring
  rw [this]; exact PInt.intCast _

/-- `p ∣ z` gives `v_p(z) ≥ 1`, i.e. `z ≡ 0 (mod p)`. -/
theorem PCong.zero_of_dvd {z : ℤ} (hz : (p : ℤ) ∣ z) : PCong p ((z : ℚ)) 0 := by
  unfold PCong
  rw [sub_zero]
  rcases eq_or_ne z 0 with rfl | hz0
  · exact Or.inl (by norm_num)
  refine Or.inr ?_
  rw [padicValRat.of_int]
  have hdvd : p ∣ z.natAbs := by
    have : ((p : ℤ)).natAbs ∣ z.natAbs := Int.natAbs_dvd_natAbs.2 hz
    simpa using this
  have hne : z.natAbs ≠ 0 := Int.natAbs_ne_zero.2 hz0
  have h1 : 1 ≤ padicValNat p z.natAbs := one_le_padicValNat_of_dvd hne hdvd
  have : (1 : ℤ) ≤ (padicValInt p z : ℤ) := by
    unfold padicValInt
    exact_mod_cast h1
  exact_mod_cast this

omit [Fact p.Prime] in
/-- For `0 < v < p` the natural number `v` is a `p`-adic unit. -/
theorem padicValRat_natCast_eq_zero {v : ℕ} (hv0 : 0 < v) (hvp : v < p) :
    padicValRat p (v : ℚ) = 0 := by
  rw [padicValRat_natCast]
  have : ¬ p ∣ v := fun hd => by
    have := Nat.le_of_dvd hv0 hd
    omega
  simp [padicValNat.eq_zero_of_not_dvd this]

/-- Dividing by a `p`-adic unit does not change a lower bound. -/
theorem vge_div_unit {x y : ℚ} {c : ℚ} (hx : (padicFil p).vge x c)
    (hy : padicValRat p y = 0) : (padicFil p).vge (x / y) c := by
  have hinv : (padicFil p).vge y⁻¹ 0 := by
    refine Or.inr ?_
    rw [padicValRat.inv, hy]
    norm_num
  have := (padicFil p).vge_mul hx hinv
  rw [div_eq_mul_inv]
  simpa using this

/-- A `p`-adic unit `u` with `v_p(u) = 0` has `1/u ∈ ℤ_p`. -/
theorem PInt.inv_of_unit {y : ℚ} (hy : padicValRat p y = 0) : PInt p (1 / y) := by
  have h1 : (padicFil p).vge (1 : ℚ) 0 := (padicFil p).vge_one
  exact vge_div_unit h1 hy

theorem padicValRat_natCast_pow_eq_zero {v : ℕ} (hv0 : 0 < v) (hvp : v < p) (k : ℕ) :
    padicValRat p ((v : ℚ) ^ k) = 0 := by
  rw [padicValRat.pow, padicValRat_natCast_eq_zero hv0 hvp]
  ring

/-- `1/v^k ∈ ℤ_p` for `0 < v < p`. -/
theorem PInt.inv_pow_natCast {v : ℕ} (hv0 : 0 < v) (hvp : v < p) (k : ℕ) :
    PInt p (1 / (v : ℚ) ^ k) := PInt.inv_of_unit (padicValRat_natCast_pow_eq_zero hv0 hvp k)

/-! # §2.  The harmonic congruences

`H^{(5)}_j = ∑_{v=1}^j v^{−5}` (§2.1).  The two statements the local analysis of §4.2 needs
are `H^{(5)}_{p−1} ≡ 0` and, from it, `H^{(5)}_{p−a} ≡ H^{(5)}_{a−1} (mod p)` — the
congruence the paper cites on p. 12.

The proof uses no primitive root: it is the pairing `v ↔ p − v`, under which
`v^{−5} + (p−v)^{−5}` has numerator `v⁵ + (p−v)⁵`, divisible by `v + (p−v) = p`, over a
denominator `(v(p−v))⁵` that is a `p`-adic unit. -/

/-- `H^{(5)}_j ∈ ℤ_p` for `j < p`: every summand `v^{−5}` with `1 ≤ v ≤ j < p` is a unit. -/
theorem PInt.H5 {j : ℕ} (hj : j < p) : PInt p (Zeta5.H5 j) := by
  rw [PInt, Zeta5.H5]
  refine PInt.sum _ _ fun v hv => ?_
  rw [Finset.mem_Icc] at hv
  exact PInt.inv_pow_natCast (by omega) (by omega) 5

omit [Fact p.Prime] in
/-- `H^{(5)}_a = H^{(5)}_{a−1} + a^{−5}` for `a ≥ 1`. -/
theorem H5_succ {a : ℕ} (ha : 1 ≤ a) :
    Zeta5.H5 a = Zeta5.H5 (a - 1) + 1 / (a : ℚ) ^ 5 := by
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
  rw [Zeta5.H5, Zeta5.H5, Nat.add_sub_cancel,
    Finset.sum_Icc_succ_top (by omega : 1 ≤ b + 1)]

/-- **The pairing.**  `v^{−5} + (p−v)^{−5} ≡ 0 (mod p)` for `0 < v < p`. -/
theorem inv_pow_five_pair {v : ℕ} (hv0 : 0 < v) (hvp : v < p) :
    PCong p (1 / (v : ℚ) ^ 5 + 1 / ((p - v : ℕ) : ℚ) ^ 5) 0 := by
  set w : ℕ := p - v with hwdef
  have hw0 : 0 < w := by omega
  have hwp : w < p := by omega
  have hvw : v + w = p := by omega
  have hx0 : ((v : ℚ)) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hy0 : ((w : ℚ)) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  -- the numerator `v⁵ + w⁵` is divisible by `v + w = p`
  have hz : (p : ℤ) ∣ ((v : ℤ) ^ 5 + (w : ℤ) ^ 5) := by
    refine ⟨(v : ℤ) ^ 4 - (v : ℤ) ^ 3 * (w : ℤ) + (v : ℤ) ^ 2 * (w : ℤ) ^ 2
        - (v : ℤ) * (w : ℤ) ^ 3 + (w : ℤ) ^ 4, ?_⟩
    have hp : (p : ℤ) = (v : ℤ) + (w : ℤ) := by exact_mod_cast hvw.symm
    rw [hp]; ring
  have hnum : (padicFil p).vge ((v : ℚ) ^ 5 + (w : ℚ) ^ 5) 1 := by
    have h := PCong.zero_of_dvd (p := p) hz
    rw [PCong, sub_zero] at h
    have hcast : ((((v : ℤ) ^ 5 + (w : ℤ) ^ 5 : ℤ)) : ℚ) = (v : ℚ) ^ 5 + (w : ℚ) ^ 5 := by
      push_cast; ring
    rwa [hcast] at h
  -- the denominator `(vw)⁵` is a unit
  have hden : padicValRat p ((v : ℚ) ^ 5 * (w : ℚ) ^ 5) = 0 := by
    rw [padicValRat.mul (pow_ne_zero _ hx0) (pow_ne_zero _ hy0),
      padicValRat_natCast_pow_eq_zero hv0 hvp, padicValRat_natCast_pow_eq_zero hw0 hwp]
    ring
  have hq : 1 / (v : ℚ) ^ 5 + 1 / ((w : ℕ) : ℚ) ^ 5
      = ((v : ℚ) ^ 5 + (w : ℚ) ^ 5) / ((v : ℚ) ^ 5 * (w : ℚ) ^ 5) := by
    field_simp
    ring
  rw [PCong, sub_zero, hq]
  exact vge_div_unit hnum hden

/-- **`H^{(5)}_{p−1} = ∑_{v=1}^{p−1} v^{−5} ≡ 0 (mod p)`** for every prime `p ≥ 7`.

This is the fact the paper's p. 12 appeals to ("a consequence of `∑_{v=1}^{p−1} v^{−5} ≡ 0`").
`p ≥ 7` enters only through `p ≠ 2`, which makes the factor `2` of the pairing a unit; for
`p = 2, 3, 5` the statement is anyway degenerate or false. -/
theorem H5_p_sub_one_congr_zero (hp7 : 7 ≤ p) : PCong p (Zeta5.H5 (p - 1)) 0 := by
  classical
  -- reindexing `v ↦ p − v` on `Icc 1 (p−1)`
  have hrefl : ∑ v ∈ Icc 1 (p - 1), 1 / (((p - v : ℕ)) : ℚ) ^ 5
      = ∑ v ∈ Icc 1 (p - 1), 1 / ((v : ℕ) : ℚ) ^ 5 := by
    refine Finset.sum_nbij' (i := fun v => p - v) (j := fun v => p - v) ?_ ?_ ?_ ?_ ?_
    · intro a ha; rw [Finset.mem_Icc] at ha ⊢; omega
    · intro a ha; rw [Finset.mem_Icc] at ha ⊢; omega
    · intro a ha; rw [Finset.mem_Icc] at ha; omega
    · intro a ha; rw [Finset.mem_Icc] at ha; omega
    · intro a _; rfl
  have hpair : PCong p (∑ v ∈ Icc 1 (p - 1),
      (1 / ((v : ℕ) : ℚ) ^ 5 + 1 / (((p - v : ℕ)) : ℚ) ^ 5)) 0 := by
    have := PCong.sum (p := p) (Icc 1 (p - 1))
      (fun v => 1 / ((v : ℕ) : ℚ) ^ 5 + 1 / (((p - v : ℕ)) : ℚ) ^ 5) (fun _ => 0) ?_
    · simpa using this
    · intro v hv
      rw [Finset.mem_Icc] at hv
      exact inv_pow_five_pair (by omega) (by omega)
  have hsplit : ∑ v ∈ Icc 1 (p - 1),
      (1 / ((v : ℕ) : ℚ) ^ 5 + 1 / (((p - v : ℕ)) : ℚ) ^ 5) = 2 * Zeta5.H5 (p - 1) := by
    rw [Finset.sum_add_distrib, hrefl, Zeta5.H5]
    ring
  rw [hsplit] at hpair
  have h2 : padicValRat p (2 : ℚ) = 0 := by
    have := padicValRat_natCast_eq_zero (p := p) (v := 2) (by norm_num) (by omega)
    simpa using this
  have hdiv : (padicFil p).vge (2 * Zeta5.H5 (p - 1) / 2) 1 := by
    refine vge_div_unit ?_ h2
    rw [PCong, sub_zero] at hpair
    exact hpair
  have heq : 2 * Zeta5.H5 (p - 1) / 2 = Zeta5.H5 (p - 1) := by ring
  rw [heq] at hdiv
  rw [PCong, sub_zero]
  exact hdiv

/-- **`H^{(5)}_{p−a} ≡ H^{(5)}_{a−1} (mod p)`** (p. 12), for `1 ≤ a < p` and `p ≥ 7`.

`H^{(5)}_{p−1} − H^{(5)}_{p−a} = ∑_{w=1}^{a−1}(p−w)^{−5}`, and pairing each `(p−w)^{−5}`
with `w^{−5}` turns that into `−H^{(5)}_{a−1}` modulo `p`; `H^{(5)}_{p−1} ≡ 0` finishes. -/
theorem H5_congr (hp7 : 7 ≤ p) {a : ℕ} (ha1 : 1 ≤ a) (hap : a < p) :
    PCong p (Zeta5.H5 (p - a)) (Zeta5.H5 (a - 1)) := by
  classical
  -- `H^{(5)}_{p−1} − H^{(5)}_{p−a} = ∑_{v ∈ Ioc (p−a) (p−1)} v^{−5}`
  have hIcc : ∀ j : ℕ, Zeta5.H5 j = ∑ v ∈ Ioc 0 j, 1 / ((v : ℕ) : ℚ) ^ 5 := by
    intro j
    rw [Zeta5.H5]
    congr 1
  have hcons := Finset.sum_Ioc_consecutive (fun v : ℕ => 1 / ((v : ℕ) : ℚ) ^ 5)
    (by omega : (0 : ℕ) ≤ p - a) (by omega : p - a ≤ p - 1)
  -- reindex `v ↦ p − v : Ioc (p−a) (p−1) → Icc 1 (a−1)`
  have hre : ∑ v ∈ Ioc (p - a) (p - 1), 1 / ((v : ℕ) : ℚ) ^ 5
      = ∑ w ∈ Icc 1 (a - 1), 1 / (((p - w : ℕ)) : ℚ) ^ 5 := by
    refine Finset.sum_nbij' (i := fun v => p - v) (j := fun w => p - w) ?_ ?_ ?_ ?_ ?_
    · intro v hv; rw [Finset.mem_Ioc] at hv; rw [Finset.mem_Icc]; omega
    · intro w hw; rw [Finset.mem_Icc] at hw; rw [Finset.mem_Ioc]; omega
    · intro v hv; rw [Finset.mem_Ioc] at hv; omega
    · intro w hw; rw [Finset.mem_Icc] at hw; omega
    · intro v hv
      rw [Finset.mem_Ioc] at hv
      have : p - (p - v) = v := by omega
      rw [this]
  have hT : ∑ w ∈ Icc 1 (a - 1), 1 / (((p - w : ℕ)) : ℚ) ^ 5
      = Zeta5.H5 (p - 1) - Zeta5.H5 (p - a) := by
    rw [← hre, hIcc (p - 1), hIcc (p - a), ← hcons]
    ring
  -- the paired sum over `Icc 1 (a−1)`
  have hS : PCong p (∑ w ∈ Icc 1 (a - 1),
      (1 / ((w : ℕ) : ℚ) ^ 5 + 1 / (((p - w : ℕ)) : ℚ) ^ 5)) 0 := by
    have := PCong.sum (p := p) (Icc 1 (a - 1))
      (fun w => 1 / ((w : ℕ) : ℚ) ^ 5 + 1 / (((p - w : ℕ)) : ℚ) ^ 5) (fun _ => 0) ?_
    · simpa using this
    · intro w hw
      rw [Finset.mem_Icc] at hw
      exact inv_pow_five_pair (by omega) (by omega)
  have hSval : ∑ w ∈ Icc 1 (a - 1),
      (1 / ((w : ℕ) : ℚ) ^ 5 + 1 / (((p - w : ℕ)) : ℚ) ^ 5)
      = Zeta5.H5 (a - 1) + (Zeta5.H5 (p - 1) - Zeta5.H5 (p - a)) := by
    rw [Finset.sum_add_distrib, hT]
    rfl
  rw [hSval] at hS
  have hH := H5_p_sub_one_congr_zero (p := p) hp7
  -- `H5(p−a) − H5(a−1) = H5(p−1) − S`
  rw [PCong, sub_zero] at hS hH
  have hd := (padicFil p).vge_add hH ((padicFil p).vge_neg hS)
  have heq : Zeta5.H5 (p - 1)
      + -(Zeta5.H5 (a - 1) + (Zeta5.H5 (p - 1) - Zeta5.H5 (p - a)))
      = Zeta5.H5 (p - a) - Zeta5.H5 (a - 1) := by ring
  rw [heq] at hd
  exact hd

/-! # §3.  The pole-value congruence, and the rôle of the `−1/4 + 1/(2j)` tail

"Within a class, if either row index is at least `ℓ − 2`, all poles with `j > p` cancel.  The
two possible remaining pole values at `a` and `p − a` are integral and congruent modulo `p`.
For their constant coefficients, use `H^{(5)}_{p−a} ≡ H^{(5)}_{a−1} (mod p)` in (2.3).  Their
coefficients of `X` are also congruent." (p. 12.)

(2.3) is `μ_X(1/(t+j²)) = j⁴(X − H^{(5)}_j) − 1/4 + 1/(2j)`.  The `X`-coefficients are
`a⁴` and `(p−a)⁴`, congruent because `p − a ≡ −a`.  The constant coefficients differ by
`a⁴(H^{(5)}_{p−a} − H^{(5)}_a) + 1/(2a) + 1/(2a)`, and `H^{(5)}_{p−a} ≡ H^{(5)}_{a−1}`
turns the first term into `−a⁴·a^{−5} = −1/a`, which is cancelled **only** by the `+1/(2j)`
of the tail.  `muPole_tail_is_needed` below is that statement, with
`neg_inv_not_congr_zero` recording that `−1/a` is indeed not `0` modulo `p`. -/

/-- `v_p(x^k) ≥ v_p(y^k)`-style transport: congruences may be raised to powers. -/
theorem PCong.pow {x y : ℚ} (hx : PInt p x) (hy : PInt p y) (h : PCong p x y) (k : ℕ) :
    PCong p (x ^ k) (y ^ k) := by
  induction k with
  | zero => rw [pow_zero, pow_zero]; exact PCong.refl 1
  | succ k ih =>
      rw [pow_succ, pow_succ]
      exact PCong.mul (hx.pow k) hy ih h

/-- `p ≡ 0 (mod p)`. -/
theorem PCong.p_congr_zero : PCong p ((p : ℚ)) 0 := by
  have h : PCong p (((p : ℤ) : ℚ)) 0 := PCong.zero_of_dvd (dvd_refl _)
  simpa using h

/-- `p − a ≡ −a (mod p)`. -/
theorem PCong.natCast_sub {a : ℕ} (hap : a ≤ p) :
    PCong p (((p - a : ℕ) : ℚ)) (-(a : ℚ)) := by
  have hc : ((p - a : ℕ) : ℚ) = (p : ℚ) - (a : ℚ) := by
    rw [Nat.cast_sub hap]
  have h := PCong.p_congr_zero (p := p)
  rw [PCong, sub_zero] at h
  rw [PCong, hc]
  have heq : (p : ℚ) - (a : ℚ) - -(a : ℚ) = (p : ℚ) := by ring
  rw [heq]
  exact h

/-- The `X`-coefficients of the two pole values are congruent: `(p−a)⁴ ≡ a⁴ (mod p)`. -/
theorem pow_four_congr {a : ℕ} (hap : a ≤ p) :
    PCong p ((((p - a : ℕ) : ℚ)) ^ 4) (((a : ℚ)) ^ 4) := by
  have h := PCong.pow (p := p) (PInt.natCast _) (PInt.natCast (p := p) a).neg
    (PCong.natCast_sub hap) 4
  have heq : (-(a : ℚ)) ^ 4 = ((a : ℚ)) ^ 4 := by ring
  rwa [heq] at h

/-- `1/(2(p−a)) ≡ −1/(2a) (mod p)`: the tail terms of the two pole values. -/
theorem inv_two_mul_congr (hp7 : 7 ≤ p) {a : ℕ} (ha1 : 1 ≤ a) (hap : a < p) :
    PCong p (1 / (2 * (((p - a : ℕ)) : ℚ))) (-(1 / (2 * (a : ℚ)))) := by
  set b : ℕ := p - a with hbdef
  have hb1 : 1 ≤ b := by omega
  have hbp : b < p := by omega
  have hab : a + b = p := by omega
  have ha0 : ((a : ℚ)) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hb0 : ((b : ℚ)) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hden : padicValRat p ((2 : ℚ) * (a : ℚ) * (b : ℚ)) = 0 := by
    have h2 : padicValRat p ((2 : ℚ)) = 0 := by
      have := padicValRat_natCast_eq_zero (p := p) (v := 2) (by norm_num) (by omega)
      simpa using this
    have hne2 : ((2 : ℚ)) ≠ 0 := by norm_num
    rw [padicValRat.mul (by positivity) hb0, padicValRat.mul hne2 ha0, h2,
      padicValRat_natCast_eq_zero ha1 hap, padicValRat_natCast_eq_zero hb1 hbp]
    ring
  have hp : ((p : ℚ)) = (a : ℚ) + (b : ℚ) := by exact_mod_cast hab.symm
  have hq : 1 / (2 * ((b : ℕ) : ℚ)) - -(1 / (2 * (a : ℚ)))
      = ((p : ℚ)) / ((2 : ℚ) * (a : ℚ) * (b : ℚ)) := by
    rw [hp]; field_simp; ring
  have hnum : (padicFil p).vge ((p : ℚ)) 1 := by
    have h := PCong.p_congr_zero (p := p)
    rwa [PCong, sub_zero] at h
  rw [PCong, hq]
  exact vge_div_unit hnum hden

/-- **The truncated pole value is `≡ −1/a`, not `≡ 0`.**

This is the exact content of the referee audit's finding on p. 12
(see the head of this file): the congruence `H^{(5)}_{p−a} ≡ H^{(5)}_{a−1}`
that the paper cites accounts only for the `j⁴(X − H^{(5)}_j)` part of (2.3), and that part
alone leaves a residue `−1/a`.  It is the `+1/(2j)` of the tail that cancels it. -/
theorem muPole_tail_is_needed (hp7 : 7 ≤ p) {a : ℕ} (ha1 : 1 ≤ a) (hap : a < p) :
    PCong p (-((a : ℚ) ^ 4 * Zeta5.H5 a) + (((p - a : ℕ) : ℚ)) ^ 4 * Zeta5.H5 (p - a))
      (-(1 / (a : ℚ))) := by
  set b : ℕ := p - a with hbdef
  have hb1 : 1 ≤ b := by omega
  have hbp : b < p := by omega
  have ha0 : ((a : ℚ)) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  -- `H^{(5)}_b ≡ H^{(5)}_a − a^{−5}`
  have hH : PCong p (Zeta5.H5 b) (Zeta5.H5 a - 1 / (a : ℚ) ^ 5) := by
    have h := H5_congr (p := p) hp7 ha1 hap
    have hs := H5_succ ha1
    rw [← hbdef] at h
    have heq : Zeta5.H5 (a - 1) = Zeta5.H5 a - 1 / (a : ℚ) ^ 5 := by rw [hs]; ring
    rwa [heq] at h
  -- `b⁴ H^{(5)}_b ≡ a⁴(H^{(5)}_a − a^{−5}) = a⁴H^{(5)}_a − 1/a`
  have hprod : PCong p (((b : ℕ) : ℚ) ^ 4 * Zeta5.H5 b)
      ((a : ℚ) ^ 4 * (Zeta5.H5 a - 1 / (a : ℚ) ^ 5)) :=
    PCong.mul ((PInt.natCast (p := p) b).pow 4)
      ((PInt.H5 (p := p) (by omega)).sub (PInt.inv_pow_natCast ha1 hap 5))
      (pow_four_congr (by omega)) hH
  have hstep : PCong p (-((a : ℚ) ^ 4 * Zeta5.H5 a) + ((b : ℕ) : ℚ) ^ 4 * Zeta5.H5 b)
      (-((a : ℚ) ^ 4 * Zeta5.H5 a) + (a : ℚ) ^ 4 * (Zeta5.H5 a - 1 / (a : ℚ) ^ 5)) :=
    PCong.add (PCong.refl _) hprod
  have hval : -((a : ℚ) ^ 4 * Zeta5.H5 a) + (a : ℚ) ^ 4 * (Zeta5.H5 a - 1 / (a : ℚ) ^ 5)
      = -(1 / (a : ℚ)) := by
    field_simp
    ring
  rwa [hval] at hstep

/-- `−1/a` is a `p`-adic unit for `1 ≤ a < p`, hence **not** `≡ 0 (mod p)`. -/
theorem neg_inv_not_congr_zero {a : ℕ} (ha1 : 1 ≤ a) (hap : a < p) :
    ¬ PCong p (-(1 / (a : ℚ))) 0 := by
  have ha0 : ((a : ℚ)) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hne : -(1 / (a : ℚ)) ≠ 0 := by
    simp [ha0]
  have hv : padicValRat p (-(1 / (a : ℚ))) = 0 := by
    rw [padicValRat.neg, one_div, padicValRat.inv, padicValRat_natCast_eq_zero ha1 hap]
    ring
  intro hc
  rw [PCong, sub_zero] at hc
  rcases hc with h0 | h0
  · exact hne h0
  · rw [hv] at h0
    norm_num at h0

/-! ### The Gauss valuation of a constant and of `X` -/

/-- `v_p^G(C c) ≥ b` whenever `v_p(c) ≥ b`. -/
theorem gaussGe_C {c b : ℚ} (h : (padicFil p).vge c b) : (gaussFil p).vge (C c) b := by
  intro i
  rcases eq_or_ne i 0 with rfl | hi
  · rw [Polynomial.coeff_C_zero]; exact h
  · have hz : ((C c : ℚ[X]).coeff i) = 0 := by simp [Polynomial.coeff_C, hi]
    rw [hz]; exact (padicFil p).vge_zero _

/-- `v_p^G(X) ≥ 0`. -/
theorem gaussGe_X : (gaussFil p).vge (X : ℚ[X]) 0 := by
  intro i
  rcases eq_or_ne i 1 with rfl | hi
  · rw [Polynomial.coeff_X_one]; exact (padicFil p).vge_one
  · rw [Polynomial.coeff_X_of_ne_one hi]; exact (padicFil p).vge_zero _

/-- **The two pole values at `a` and `p − a` are congruent modulo `p`** (p. 12), with the
`−1/4 + 1/(2j)` tail of (2.3) included, which is what makes the congruence true.

`v_p^G(μ_X(1/(t+a²)) − μ_X(1/(t+(p−a)²))) ≥ 1`. -/
theorem muPole_congr (hp7 : 7 ≤ p) {a : ℕ} (ha1 : 1 ≤ a) (hap : a < p) :
    vGAtLeast p (muPole a - muPole (p - a)) 1 := by
  set b : ℕ := p - a with hbdef
  have ha0 : ((a : ℚ)) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hb0 : ((b : ℚ)) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  -- (2.3) in normal form
  have hdiff : muPole a - muPole b
      = C ((a : ℚ) ^ 4 - ((b : ℕ) : ℚ) ^ 4) * X
        + C ((-((a : ℚ) ^ 4 * Zeta5.H5 a) + ((b : ℕ) : ℚ) ^ 4 * Zeta5.H5 b)
              + (1 / (2 * (a : ℚ)) - 1 / (2 * ((b : ℕ) : ℚ)))) := by
    simp only [Functional.muPole_eq, map_sub, map_add, map_neg]
    ring
  -- the `X`-coefficient
  have hX : (padicFil p).vge ((a : ℚ) ^ 4 - ((b : ℕ) : ℚ) ^ 4) 1 := by
    have h := (pow_four_congr (p := p) (a := a) (by omega)).symm
    rwa [PCong] at h
  -- the constant coefficient
  have hconst : (padicFil p).vge
      ((-((a : ℚ) ^ 4 * Zeta5.H5 a) + ((b : ℕ) : ℚ) ^ 4 * Zeta5.H5 b)
        + (1 / (2 * (a : ℚ)) - 1 / (2 * ((b : ℕ) : ℚ)))) 1 := by
    have h1 := muPole_tail_is_needed (p := p) hp7 ha1 hap
    have h2 := inv_two_mul_congr (p := p) hp7 ha1 hap
    rw [← hbdef] at h1 h2
    have hsum : PCong p
        ((-((a : ℚ) ^ 4 * Zeta5.H5 a) + ((b : ℕ) : ℚ) ^ 4 * Zeta5.H5 b)
          + (-(1 / (2 * (a : ℚ))) - 1 / (2 * ((b : ℕ) : ℚ))))
        ((-(1 / (a : ℚ))) + (-(1 / (2 * (a : ℚ))) - -(1 / (2 * (a : ℚ))))) :=
      PCong.add h1 (PCong.sub (PCong.refl _) h2)
    have hzero : (-(1 / (a : ℚ))) + (-(1 / (2 * (a : ℚ))) - -(1 / (2 * (a : ℚ))))
        = -(1 / (a : ℚ)) := by ring
    rw [hzero] at hsum
    -- now add `1/(2a) + 1/(2a) = 1/a` back
    have hfix : (-((a : ℚ) ^ 4 * Zeta5.H5 a) + ((b : ℕ) : ℚ) ^ 4 * Zeta5.H5 b)
        + (1 / (2 * (a : ℚ)) - 1 / (2 * ((b : ℕ) : ℚ)))
        = ((-((a : ℚ) ^ 4 * Zeta5.H5 a) + ((b : ℕ) : ℚ) ^ 4 * Zeta5.H5 b)
          + (-(1 / (2 * (a : ℚ))) - 1 / (2 * ((b : ℕ) : ℚ)))) - (-(1 / (a : ℚ))) := by
      field_simp
      ring
    rw [PCong] at hsum
    rw [hfix]
    exact hsum
  rw [← gaussGe_intCast]
  rw [hdiff]
  have h1 : (gaussFil p).vge (C ((a : ℚ) ^ 4 - ((b : ℕ) : ℚ) ^ 4) * X) 1 :=
    (gaussFil p).vge_mono (by norm_num) ((gaussFil p).vge_mul (gaussGe_C hX) gaussGe_X)
  have h2 := gaussGe_C hconst
  have := (gaussFil p).vge_add h1 h2
  exact (gaussFil p).vge_mono (by norm_num) this

/-! # §4.  The divided difference at the two remaining nodes

"At `x = c + pz`, every near denominator factor supplies a factor `p` and a simple integer
pole in `z`. … distinct near poles differ by a `p`-adic unit" (p. 11) and "The divided
difference at the two nodes is therefore integral" (p. 12).

The two nodes of an ordinary class that survive the factor `E_a` are `−a²` and `−(p−a)²`;
their separation is `(p−a)² − a² = p(p−2a)`, of valuation exactly `1` because `0 < p−2a < p`.
A difference quotient of two `p`-integral values that are congruent modulo `p`, taken across
a separation of valuation `1`, is therefore `p`-integral. -/

/-- **The two nodes of a class differ by exactly `p`**: `v_p((p−a)² − a²) = 1`, for `1 ≤ a`
and `2a < p`.  (The nodes of (2.4) are `−j²`, so the separation is `(p−a)² − a²`.) -/
theorem node_sub_valuation {a : ℕ} (ha1 : 1 ≤ a) (ha2 : 2 * a < p) :
    padicValRat p ((((p - a : ℕ) : ℚ)) ^ 2 - ((a : ℚ)) ^ 2) = 1 := by
  have hp1 : 1 < p := by omega
  have hfac : (((p - a : ℕ) : ℚ)) ^ 2 - ((a : ℚ)) ^ 2
      = ((p : ℚ)) * (((p - 2 * a : ℕ)) : ℚ) := by
    rw [Nat.cast_sub (by omega : a ≤ p), Nat.cast_sub (by omega : 2 * a ≤ p)]
    push_cast
    ring
  have hp0 : ((p : ℚ)) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hc0 : (((p - 2 * a : ℕ)) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  rw [hfac, padicValRat.mul hp0 hc0, padicValRat.self hp1,
    padicValRat_natCast_eq_zero (by omega) (by omega)]
  ring

/-- **The divided difference is integral.**  If `f(x) ≡ f(y) (mod p)` and the two nodes are
separated by exactly `p` (`v_p(x − y) = 1`), then `(f(x) − f(y))/(x − y) ∈ ℤ_p`. -/
theorem divided_difference_int {fx fy x y : ℚ} (hc : PCong p fx fy)
    (hxy : padicValRat p (x - y) = 1) : PInt p ((fx - fy) / (x - y)) := by
  have hne : x - y ≠ 0 := by
    intro h
    rw [h] at hxy
    simp at hxy
  have hinv : (padicFil p).vge (x - y)⁻¹ (-1) := by
    refine Or.inr ?_
    rw [padicValRat.inv, hxy]
    norm_num
  have hmul := (padicFil p).vge_mul hc hinv
  rw [PInt, div_eq_mul_inv]
  exact (padicFil p).vge_mono (by norm_num) hmul

/-- **"The divided difference at the two nodes is therefore integral."** (p. 12.)

The two remaining pole values of an ordinary class, `μ_X(1/(t+a²))` and
`μ_X(1/(t+(p−a)²))`, divided by the separation `(p−a)² − a²` of their nodes, have
`v_p^G ≥ 0`.  This combines `muPole_congr` (§3) with `node_sub_valuation`. -/
theorem muPole_divided_difference (hp7 : 7 ≤ p) {a : ℕ} (ha1 : 1 ≤ a) (ha2 : 2 * a < p) :
    vGAtLeast p
      (C ((((p - a : ℕ) : ℚ)) ^ 2 - ((a : ℚ)) ^ 2)⁻¹ * (muPole a - muPole (p - a))) 0 := by
  have hsep := node_sub_valuation (p := p) ha1 ha2
  have hinv : (padicFil p).vge ((((p - a : ℕ) : ℚ)) ^ 2 - ((a : ℚ)) ^ 2)⁻¹ (-1) := by
    refine Or.inr ?_
    rw [padicValRat.inv, hsep]
    norm_num
  have hnum : (gaussFil p).vge (muPole a - muPole (p - a)) 1 :=
    (gaussGe_intCast p _ 1).2 (muPole_congr hp7 ha1 (by omega))
  have := (gaussFil p).vge_mul (gaussGe_C hinv) hnum
  rw [← gaussGe_intCast]
  exact (gaussFil p).vge_mono (by norm_num) this

/-! # §5.  The change of basis, and the determinant

"Use the rows `P_a q_{a,i}` … Together with the zero-class rows, these form a unimodular
basis" (p. 12), and "The basis change is unimodular, which proves the proposition" (p. 11).

`muOver` is `ℚ`-linear (`Functional.muOver_add`, `Functional.muOver_C_mul`), so the entries
`μ_X(D_N⁵t^{i+j}/D_tail)` of (2.4) are the Gram matrix of the `ℚ`-bilinear form
`Bil f g = μ_X(D_N⁵ f g/D_tail)` in the monomial basis.  Changing basis by a matrix `U` over
`ℚ` therefore replaces `G_K` by `U G_K Uᵀ`, whose determinant is `(det U)² Δ_K`.  That is
the identity Proposition 4.3 needs: with `c = (det U)^{-2}`, `Δ_K = c · det Gram(U)` and
`v_p(c) = 0` exactly when `U` is `ℤ_p`-unimodular. -/

section Basis

variable {ι : Type*}

theorem muOver_zero (n : ℕ) : muOver n 0 = 0 := by
  have h := Functional.muOver_C_mul n 0 0
  simpa using h

theorem muOver_sum (n : ℕ) (s : Finset ι) (A : ι → ℚ[X]) :
    muOver n (∑ i ∈ s, A i) = ∑ i ∈ s, muOver n (A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, muOver_zero]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, Functional.muOver_add, ih]

/-- **The bilinear form behind (2.4)**: `Bil f g = μ_X(D_N(t)⁵ f(t) g(t)/D_tail(t))`, so that
`G_K = [Bil(t^i, t^j)]` is its Gram matrix in the monomial basis. -/
def Bil (n : ℕ) (f g : ℚ[X]) : ℚ[X] := muOver n ((D (N n)) ^ 5 * (f * g))

theorem G_eq_Bil (n : ℕ) (i j : Fin (h n)) :
    G n i j = Bil n (X ^ (i : ℕ)) (X ^ (j : ℕ)) := by
  rw [G, Bil, entryNum, pow_add]

/-- The polynomial of the `u`-th row of a basis change `U`: `f_u = ∑_i U_{ui} t^i`. -/
def rowPoly {hh : ℕ} (U : Matrix (Fin hh) (Fin hh) ℚ) (u : Fin hh) : ℚ[X] :=
  ∑ i, C (U u i) * X ^ (i : ℕ)

/-- The Gram matrix of `Bil` in the basis `f_u = ∑_i U_{ui} t^i`. -/
def Gram (n : ℕ) (U : Matrix (Fin (h n)) (Fin (h n)) ℚ) :
    Matrix (Fin (h n)) (Fin (h n)) ℚ[X] :=
  Matrix.of fun u v => Bil n (rowPoly U u) (rowPoly U v)

/-- **The basis change**: `Gram(U) = U G_K Uᵀ`, for any `U` over `ℚ`. -/
theorem gram_basis_change (n : ℕ) (U : Matrix (Fin (h n)) (Fin (h n)) ℚ) :
    Gram n U = (U.map C) * G n * (U.map C).transpose := by
  classical
  refine Matrix.ext fun u v => ?_
  have hexp : (D (N n)) ^ 5 * (rowPoly U u * rowPoly U v)
      = ∑ i : Fin (h n), ∑ j : Fin (h n),
          C (U u i * U v j) * ((D (N n)) ^ 5 * (X ^ (i : ℕ) * X ^ (j : ℕ))) := by
    rw [rowPoly, rowPoly, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul]; ring
  have hlhs : Gram n U u v
      = ∑ i : Fin (h n), ∑ j : Fin (h n), C (U u i * U v j) * G n i j := by
    rw [Gram, Matrix.of_apply, Bil, hexp, muOver_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [muOver_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Functional.muOver_C_mul, G, entryNum, pow_add]
  have hrhs : ((U.map C) * G n * (U.map C).transpose) u v
      = ∑ j : Fin (h n), ∑ i : Fin (h n), C (U u i) * G n i j * C (U v j) := by
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rfl
  have hcomm : ∑ i : Fin (h n), ∑ j : Fin (h n), C (U u i * U v j) * G n i j
      = ∑ j : Fin (h n), ∑ i : Fin (h n), C (U u i * U v j) * G n i j :=
    Finset.sum_comm (f := fun (i j : Fin (h n)) => C (U u i * U v j) * G n i j)
  rw [hlhs, hcomm, hrhs]
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul]; ring

/-- `det Gram(U) = (det U)² Δ_K`. -/
theorem det_Gram (n : ℕ) (U : Matrix (Fin (h n)) (Fin (h n)) ℚ) :
    (Gram n U).det = C (U.det ^ 2) * Delta n := by
  have hmapdet : (U.map C).det = C U.det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  rw [gram_basis_change, Matrix.det_mul, Matrix.det_mul, hmapdet, Matrix.det_transpose,
    hmapdet, Delta, map_pow]
  ring

/-- **`Δ_K = (det U)^{-2} · det Gram(U)`.**

This is the determinant half of "The basis change is unimodular, which proves the
proposition" (p. 11): it produces exactly the datum `c` and the identity
`Δ_K = C c · det(…)` that `Zeta5.outer_local_analysis` asks for, out of any basis change `U`
with `det U ≠ 0`. -/
theorem Delta_eq_of_basis {n : ℕ} (U : Matrix (Fin (h n)) (Fin (h n)) ℚ) (hU : U.det ≠ 0) :
    Delta n = C ((U.det ^ 2)⁻¹) * (Gram n U).det := by
  rw [det_Gram, ← mul_assoc, ← map_mul, inv_mul_cancel₀ (pow_ne_zero 2 hU), map_one, one_mul]

/-- **`ℤ_p`-unimodularity of the basis makes `c = (det U)^{-2}` a `p`-adic unit**, which is
the other half of what `Zeta5.outer_local_analysis` asks for. -/
theorem padicValRat_unimodular {p : ℕ} [Fact p.Prime] {n : ℕ}
    (U : Matrix (Fin (h n)) (Fin (h n)) ℚ) (hv : padicValRat p U.det = 0) :
    padicValRat p ((U.det ^ 2)⁻¹) = 0 := by
  rw [padicValRat.inv, padicValRat.pow, hv]
  ring

end Basis

/-! # §6.  Known-answer controls, and axiom checks

The statements of §§2–4 agree with exact rational arithmetic (computed outside Lean) at
`p = 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43` and, where an `a` occurs, at every
`1 ≤ a ≤ (p−1)/2`.  What the computation found:

* `v_p(H^{(5)}_{p−1}) = 1` at `p = 7` and `= 2` at every larger prime in the list (the
  Wolstenholme-type strengthening; `H5_p_sub_one_congr_zero` claims only `≥ 1`, which is
  all §4.2 uses and all the pairing proof gives);
* `H^{(5)}_{p−a} ≡ H^{(5)}_{a−1} (mod p)`: **no failure**, at any `p` or `a`;
* the **full** pole difference `μ_X(1/(t+a²)) − μ_X(1/(t+(p−a)²))` of (2.3) has
  `v_p ≥ 1` in **both** coefficients, at every `p` and `a` — `muPole_congr`;
* the **truncated** difference, with the `−1/4 + 1/(2j)` tail of (2.3) dropped, has
  `v_p = 0` exactly (so it is *not* `≡ 0`), and becomes `≥ 1` after adding `1/a` — which is
  `muPole_tail_is_needed` together with `neg_inv_not_congr_zero` (the audit's observation
  on p. 12);
* `v_p((p−a)² − a²) = 1` exactly, at every `p` and every `1 ≤ a ≤ (p−1)/2` —
  `node_sub_valuation`.
-/

section Audit

#print axioms Zeta5.OuterLocal.inv_pow_five_pair
#print axioms Zeta5.OuterLocal.H5_p_sub_one_congr_zero
#print axioms Zeta5.OuterLocal.H5_congr
#print axioms Zeta5.OuterLocal.muPole_tail_is_needed
#print axioms Zeta5.OuterLocal.neg_inv_not_congr_zero
#print axioms Zeta5.OuterLocal.muPole_congr
#print axioms Zeta5.OuterLocal.node_sub_valuation
#print axioms Zeta5.OuterLocal.divided_difference_int
#print axioms Zeta5.OuterLocal.muPole_divided_difference
#print axioms Zeta5.OuterLocal.gram_basis_change
#print axioms Zeta5.OuterLocal.det_Gram
#print axioms Zeta5.OuterLocal.Delta_eq_of_basis
#print axioms Zeta5.OuterLocal.padicValRat_unimodular

end Audit

end OuterLocal

end

end Zeta5
