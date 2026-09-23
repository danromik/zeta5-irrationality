/-
Zeta5/HermiteBasis.lean

**THE SHARED UNIMODULARITY LEMMA: a Hermite-interpolation basis modulo `p` is `ℤ_p`-unimodular.**

This file imports only Mathlib and `Zeta5/HermiteBasisCore.lean` (which holds the proofs).
It is imported by `Zeta5/OuterLocal.lean` and `Zeta5/OuterBasis.lean` (for
`Zeta5.outer_local_analysis`, basis (4.11)) and by `Zeta5/Section3.lean` and
`Zeta5/InnerEntries.lean` (for `Zeta5.Section3.entry_bounds_4_2_4_3`, basis (4.5)).

## The paper's text

p. 10 (inner range, Proposition 4.1):

> For `a = 0, 1, …, m` and `0 ≤ i < L_a`, take the row polynomial
>     `E_{a,i}(t) = ∏_{0≤c≤m, c≠a} (t + c²)^{L_c} (t + a²)^i.`                         (4.5)
> The factors `t + c²` are pairwise coprime modulo `p`.  In the Chinese remainder
> decomposition by their powers, the polynomials in (4.5) give triangular local bases whose
> diagonal entries are units.  They therefore form a `ℤ_p`-unimodular basis of the
> polynomials of degree less than `h`.

p. 12 (outer range, Proposition 4.3):

> For an ordinary square class `a`, let `ℓ = ℓ_K(a)` and `δ = 1_{a≤N}`.  There are `ℓ − δ`
> remaining poles in the class and exactly `ℓ − 2` of the original poles have `j > p`.  Let
> `Q_a` be the product of the remaining factors in the class, put `P_a = D_tail/Q_a`, and let
> `E_a` be the product of the factors with `j > p`.  Use the rows `P_a q_{a,i}`, where
>     `q_{a,i}(t) = (t+a²)^i`,                  `0 ≤ i < ℓ−2`,
>     `q_{a,i}(t) = E_a(t)(t+a²)^{i−(ℓ−2)}`,    `ℓ−2 ≤ i < ℓ−δ`.                       (4.11)
> Together with the zero-class rows, these form a unimodular basis.  Indeed, the local
> polynomials are monic of successive degrees, and the resultants of distinct class factors
> are units.
> [...] For two zero-class poles `p, 2p`, the rows `1, t + p²` give entry bounds `−3, −1, 0`.

## Why one lemma serves both

Both bases have **integer** coefficients (every factor is a monic `t + j²`, `j ∈ ℤ`), and both
reduce modulo `p` to a Hermite-interpolation basis with pairwise distinct nodes:

* (4.5): nodes `−c²`, `0 ≤ c ≤ m = (p−1)/2`, pairwise distinct mod `p`; the row `(a,i)` is
  *literally* `∏_{c≠a}(t+c²)^{L_c}(t+a²)^i`, with multiplicities `m_c = L_c`, `∑ L_c = h`.
* (4.11): every tail factor `t + j²` with `j ≡ ±c (mod p)` reduces to `t + c²` (for the zero
  class, `t + (kp)² ≡ t`).  `P_a` is the product of all tail factors *outside* class `a`, so
  `P_a ≡ ∏_{c≠a}(t+c²)^{m_c}` with `m_c` the number of tail poles in class `c` (`= outerDim`),
  and `q_{a,i} ≡ (t+a²)^i` (because `E_a ≡ (t+a²)^{ℓ−2}`); the zero-class rows `P_0·1`,
  `P_0·(t+p²)` reduce to `P̄_0·t⁰`, `P̄_0·t¹`.  So the row `(a,i)` reduces to
  `∏_{c≠a}(t+c²)^{m_c}(t+a²)^i`, with `∑ m_c = K − N = h`.

The proof over `𝔽_p` is short: if `∑_a u_a(t)·P̄_a = 0` with `deg u_a < m_a`, reduce modulo
`(t + u_a)^{m_a}`; every `P̄_b` with `b ≠ a` vanishes there and `P̄_a` is coprime to
`t + u_a`, so `(t+u_a)^{m_a} ∣ u_a`, hence `u_a = 0`.  The `h` polynomials have degree `< h`,
so their `h × h` coefficient matrix is invertible over `𝔽_p`; an integer matrix whose
reduction mod `p` is invertible has determinant prime to `p`.

## What is here

* `hermitePoly u m a i = (∏_{c≠a} (X + C (u c))^(m c)) * (X + C (u a))^i` — the Hermite
  basis polynomial (the node is `−u c`, matching the paper's `t + c²`).
* `coeffMatrix f` — the `hh × hh` matrix whose row `k` holds the coefficients of
  `t⁰, …, t^{hh−1}` in `f k`, i.e. the basis change from the monomial basis.
* **`det_coeffMatrix_unimodular`** — THE SHARED LEMMA (PROVED 2026-09-23, no `sorry`; the proof
  is in `Zeta5/HermiteBasisCore.lean`, imported here): for integer polynomials
  `g k` reducing mod `p` to the Hermite basis (rows labelled by `σ : Fin hh ≃ Σ a, Fin (m a)`),
  the rational coefficient matrix `U` has `det U ≠ 0` and `v_p(det U) = 0`.  This is exactly
  the pair of hypotheses of `Zeta5.OuterLocal.Delta_eq_of_basis` (`U.det ≠ 0`) and
  `Zeta5.OuterLocal.padicValRat_unimodular` (`padicValRat p U.det = 0`).
* Decomposition (all PROVED, via `Zeta5/HermiteBasisCore.lean`): `hermite_linearIndependent` (the core
  `𝔽_p` statement, over any field) ⇒ `det_coeffMatrix_hermite_ne_zero` (the coefficient
  matrix over the field is invertible) ⇒ `det_coeffMatrix_unimodular` (reduce the integer
  matrix mod `p`: `(coeffMatrix g).map (Int.castRingHom (ZMod p))` is the Hermite coefficient
  matrix by `hg` and `Polynomial.coeff_map`; `RingHom.map_det`; `ZMod.intCast_zmod_eq_zero_iff_dvd`;
  `padicValRat.of_int`).  The statements of all three were fixed before the proof was written;
  `HermiteBasisCore.lean` states them with `hermitePoly`/`coeffMatrix` unfolded (it sits below
  this file in the import graph), and the proofs here are one-line applications.
* Proved glue (no `sorry`), for the consumers: `hermitePoly_map`, `hermitePoly_monic`,
  `hermitePoly_natDegree`, `coeffMatrix_row_sum` (`∑_i C(U_{ki}) X^i = f k` when
  `deg f k < hh`, i.e. `Zeta5.OuterLocal.rowPoly U k = f k`), and `sq_injective` (the nodes
  `c²`, `0 ≤ c ≤ M`, are pairwise distinct in `ZMod p` when `2M < p`).

## How the consumers use it

*Outer, `Zeta5.outer_local_analysis`.*  `κ = Fin (mHalf p + 1)`, `u c = ((c : ℕ) : ZMod p)^2`
(injective by `sq_injective_half`), `m c = outerDim n p c`, so `Σ a, Fin (m a)` is literally
`OuterRows n p`; `σ = eρ.symm`; `g k ∈ ℤ[X]` the integer form of the row `P_a q_{a,i}`
(`(a,i) = eρ.symm k`).  With `U = coeffMatrix fun k => (g k).map (Int.castRingHom ℚ)`, this lemma
gives `U.det ≠ 0` and `v_p(U.det) = 0`; `OuterLocal.Delta_eq_of_basis U` gives
`Δ_K = C ((det U)^{-2}) · det (Gram n U)`, `OuterLocal.padicValRat_unimodular` gives the unit
`c`, and `coeffMatrix_row_sum` identifies `OuterLocal.rowPoly U k` with the row polynomial, so
`Gram n U` is the Gram matrix of `Bil` in the basis (4.11).

*Inner, `Zeta5.Section3.entry_bounds_4_2_4_3`.*  `κ = Fin (mHalf p + 1)`, the same `u`,
`m c = A.Ldim c`, so `Σ a, Fin (m a)` is literally `A.Rows`; `σ : Fin (h n) ≃ A.Rows` from
`Fintype.card A.Rows = h n` (the dimension identity); `g k = hermitePoly (fun c => ((c : ℕ) : ℤ)^2)
m (σ k).1 (σ k).2`, for which `hg` is `hermitePoly_map` and `(g k).map (Int.castRingHom ℚ)` is
`A.rowPoly` after reindexing the product from `Fin` to `range`.  Then
`B = (Gram n U).submatrix σ.symm σ.symm` (`Matrix.det_submatrix_equiv_self`) and
`c = (det U)^{-2}`.

Both recipes, and the `Fin`-to-`range` reindexing of `A.rowPoly`, are written out and
compile in `numerics/HermiteConsumerExamples.lean` (not part of the package; from the
repository root, check with `lake env lean numerics/HermiteConsumerExamples.lean`).

## Numerical sanity of the statement (exact integer arithmetic, 2026-09-23)

`numerics/hermite_check.py` (output `numerics/hermite_check.out`): random primes
`2 ≤ p ≤ 101`, random distinct nodes, random multiplicities `0..5`, random integer lifts (each
linear factor lifted separately by `+ p·ℤ`, plus `p·(random polynomial)` of degree up to
`hh + 3`), random `σ`: `p ∤ det U` in **1500/1500** cases.  MUST-FAIL control (two nodes equal
mod `p`, both multiplicities `≥ 1`): `p ∣ det U` in **1000/1000** cases.  Known-answer control:
the paper's basis (4.11), built as in the exact-determinant computation of the referee audit
(see README, "Provenance"), at `K = 40, 80, 120` and every prime satisfying (4.9): every row
reduces mod `p` *exactly* to `hermitePoly`
with `u_c = c²`, `m_c = #`tail poles in class `c`, and `v_p(det U) = 0`, at **37/37** primes
(plus 18/18 primes `p > K`); inner basis (4.5) with random `L_c`: **300/300**.
-/
import Mathlib
import Zeta5.HermiteBasisCore

namespace Zeta5

namespace HermiteBasis

open Polynomial

noncomputable section

/-! # Definitions -/

section Defs

variable {R : Type*} [CommRing R] {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- **The Hermite-interpolation basis polynomial** of class `a` and index `i`:
`∏_{c ≠ a} (X + u_c)^{m_c} · (X + u_a)^i`.

With `u_c = c²` and `m_c = L_c` this is the paper's `E_{a,i}` of (4.5) (p. 10); modulo `p`, with
`m_c` the number of tail poles in the class `c`, it is the reduction of the row `P_a q_{a,i}`
of (4.11) (p. 12).  The basis consists of the `(a, i)` with `0 ≤ i < m_a`. -/
def hermitePoly (u : κ → R) (m : κ → ℕ) (a : κ) (i : ℕ) : R[X] :=
  (∏ c ∈ Finset.univ.erase a, (X + C (u c)) ^ m c) * (X + C (u a)) ^ i

end Defs

/-- **The basis-change matrix from the monomial basis**: row `k` holds the coefficients of
`t⁰, t¹, …, t^{hh−1}` in `f k`.  (Only these coefficients enter; for `deg f k < hh` they
determine `f k`, see `coeffMatrix_row_sum`.) -/
def coeffMatrix {S : Type*} [Semiring S] {hh : ℕ} (f : Fin hh → S[X]) :
    Matrix (Fin hh) (Fin hh) S :=
  Matrix.of fun k i => (f k).coeff (i : ℕ)

/-! # THE SHARED LEMMA -/

/-- **THE SHARED UNIMODULARITY LEMMA** (pp. 10 and 12): *a basis that reduces modulo `p` to a
Hermite-interpolation basis with pairwise distinct nodes is `ℤ_p`-unimodular.*

Hypotheses: `p` prime; nodes `u : κ → ZMod p` pairwise distinct; multiplicities `m`; the
`hh = ∑ m` rows are labelled by `σ : Fin hh ≃ Σ a, Fin (m a)`; the row `k` is an integer
polynomial `g k` whose reduction mod `p` is `hermitePoly u m a i`, `(a, i) = σ k`.  No degree
hypothesis is needed (only the coefficients of `t⁰, …, t^{hh−1}` enter `U`, and the reduction
has degree `< hh`).

Conclusion: the rational coefficient matrix `U` of the rows has `det U ≠ 0` and
`v_p(det U) = 0` — exactly the hypotheses of `Zeta5.OuterLocal.Delta_eq_of_basis` and
`Zeta5.OuterLocal.padicValRat_unimodular`.

Checked numerically before being stated (see the file header): 1500/1500 random cases,
1000/1000 must-fail controls, and the paper's basis (4.11) at 37/37 primes of (4.9). -/
theorem det_coeffMatrix_unimodular {p : ℕ} [Fact p.Prime] {κ : Type*} [Fintype κ]
    [DecidableEq κ] (u : κ → ZMod p) (hu : Function.Injective u) (m : κ → ℕ) {hh : ℕ}
    (σ : Fin hh ≃ Σ a : κ, Fin (m a)) (g : Fin hh → ℤ[X])
    (hg : ∀ k, (g k).map (Int.castRingHom (ZMod p)) = hermitePoly u m (σ k).1 ((σ k).2 : ℕ)) :
    (coeffMatrix fun k => (g k).map (Int.castRingHom ℚ)).det ≠ 0 ∧
      padicValRat p (coeffMatrix fun k => (g k).map (Int.castRingHom ℚ)).det = 0 :=
  HermiteBasisCore.det_coeffMatrix_unimodular' u hu m σ g hg

/-! # The decomposition (proved in `Zeta5/HermiteBasisCore.lean`) -/

/-- **Core, over a field**: the Hermite-interpolation family with pairwise distinct nodes is
linearly independent.  (Proof: if `∑_a v_a(t) P̄_a = 0` with `deg v_a < m_a`, reduce modulo
`(X + u_a)^{m_a}`: `P̄_b` vanishes there for `b ≠ a` and `P̄_a` is coprime to `X + u_a`, so
`(X + u_a)^{m_a} ∣ v_a`, hence `v_a = 0`; and `(X + u_a)^i`, `i < m_a`, are independent.) -/
theorem hermite_linearIndependent {F : Type*} [Field F] {κ : Type*} [Fintype κ]
    [DecidableEq κ] (u : κ → F) (hu : Function.Injective u) (m : κ → ℕ) :
    LinearIndependent F (fun r : (Σ a : κ, Fin (m a)) => hermitePoly u m r.1 (r.2 : ℕ)) := by
  rw [Fintype.linearIndependent_iff]
  intro v hv
  have h0 := HermiteBasisCore.hermite_sum_eq_zero u hu m v
    (by simpa only [smul_eq_C_mul, hermitePoly] using hv)
  exact fun r => congrFun h0 r

/-- **Over a field, the coefficient matrix of the Hermite basis is invertible**: the `hh`
polynomials are linearly independent and have degree `< hh = ∑ m`. -/
theorem det_coeffMatrix_hermite_ne_zero {F : Type*} [Field F] {κ : Type*} [Fintype κ]
    [DecidableEq κ] (u : κ → F) (hu : Function.Injective u) (m : κ → ℕ) {hh : ℕ}
    (σ : Fin hh ≃ Σ a : κ, Fin (m a)) :
    (coeffMatrix fun k => hermitePoly u m (σ k).1 ((σ k).2 : ℕ)).det ≠ 0 :=
  HermiteBasisCore.det_coeffMatrix_hermite_ne_zero' u hu m σ

/-! # Proved glue for the consumers -/

section Glue

variable {R : Type*} [CommRing R] {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- Reduction commutes with `hermitePoly`: `(hermitePoly u m a i).map f = hermitePoly (f ∘ u) m a i`.
(For the inner basis (4.5): take `u c = c²` over `ℤ` and `f = Int.castRingHom (ZMod p)` or
`Int.castRingHom ℚ`.) -/
theorem hermitePoly_map {S : Type*} [CommRing S] (f : R →+* S) (u : κ → R) (m : κ → ℕ)
    (a : κ) (i : ℕ) :
    (hermitePoly u m a i).map f = hermitePoly (fun c => f (u c)) m a i := by
  simp [hermitePoly, Polynomial.map_mul, Polynomial.map_prod, Polynomial.map_pow]

theorem hermitePoly_monic [Nontrivial R] (u : κ → R) (m : κ → ℕ) (a : κ) (i : ℕ) :
    (hermitePoly u m a i).Monic :=
  (monic_prod_of_monic _ _ fun c _ => (monic_X_add_C (u c)).pow (m c)).mul
    ((monic_X_add_C (u a)).pow i)

/-- `deg hermitePoly u m a i = ∑_{c ≠ a} m_c + i`, which is `< ∑_c m_c` for `i < m_a`. -/
theorem hermitePoly_natDegree [Nontrivial R] (u : κ → R) (m : κ → ℕ) (a : κ) (i : ℕ) :
    (hermitePoly u m a i).natDegree = (∑ c ∈ Finset.univ.erase a, m c) + i := by
  rw [hermitePoly, Monic.natDegree_mul
      (monic_prod_of_monic _ _ fun c _ => (monic_X_add_C (u c)).pow (m c))
      ((monic_X_add_C (u a)).pow i),
    natDegree_prod_of_monic _ _ fun c _ => (monic_X_add_C (u c)).pow (m c),
    (monic_X_add_C (u a)).natDegree_pow, natDegree_X_add_C, mul_one]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [(monic_X_add_C (u c)).natDegree_pow, natDegree_X_add_C, mul_one]

end Glue

/-- **The rows of `coeffMatrix f` are the `f k`**: `∑_i C(U_{ki}) X^i = f k` when
`deg f k < hh`.  This is `Zeta5.OuterLocal.rowPoly (coeffMatrix f) k = f k`. -/
theorem coeffMatrix_row_sum {S : Type*} [Semiring S] {hh : ℕ} (f : Fin hh → S[X]) (k : Fin hh)
    (hk : (f k).natDegree < hh) :
    ∑ i : Fin hh, C (coeffMatrix f k i) * X ^ (i : ℕ) = f k := by
  simp only [coeffMatrix, Matrix.of_apply]
  rw [Fin.sum_univ_eq_sum_range (fun i => C ((f k).coeff i) * X ^ i) hh]
  conv_rhs => rw [(f k).as_sum_range' hh hk]
  simp only [C_mul_X_pow_eq_monomial]

/-- **The nodes are pairwise distinct mod `p`**: `c ↦ c² (mod p)` is injective on
`{0, …, M}` when `2M < p` (p. 10: "The factors `t + c²` are pairwise coprime modulo `p`").
If `c² ≡ c'²` then `p ∣ (c − c')(c + c')`; `|c − c'| ≤ M < p` and `0 ≤ c + c' ≤ 2M < p`. -/
theorem sq_injective {p : ℕ} [hp : Fact p.Prime] {M : ℕ} (hM : 2 * M < p) :
    Function.Injective (fun c : Fin (M + 1) => (((c : ℕ) : ZMod p)) ^ 2) := by
  intro c c' hcc
  simp only at hcc
  have hfac : (((c : ℕ) : ZMod p) - ((c' : ℕ) : ZMod p)) *
      (((c : ℕ) : ZMod p) + ((c' : ℕ) : ZMod p)) = 0 := by
    linear_combination hcc
  have hc := c.isLt
  have hc' := c'.isLt
  rcases mul_eq_zero.1 hfac with h | h
  · have h' : ((c : ℕ) : ZMod p) = ((c' : ℕ) : ZMod p) := sub_eq_zero.1 h
    rw [ZMod.natCast_eq_natCast_iff'] at h'
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h'
    exact Fin.ext h'
  · have h' : (((c : ℕ) + (c' : ℕ) : ℕ) : ZMod p) = 0 := by push_cast; exact h
    rw [ZMod.natCast_eq_zero_iff] at h'
    have hlt : (c : ℕ) + (c' : ℕ) < p := by omega
    have h0 : (c : ℕ) + (c' : ℕ) = 0 := Nat.eq_zero_of_dvd_of_lt h' hlt
    exact Fin.ext (by omega)

/-- `sq_injective` at `M = (p − 1)/2` (`= Zeta5.mHalf p`), the range of classes in both
(4.5) and (4.11). -/
theorem sq_injective_half {p : ℕ} [hp : Fact p.Prime] :
    Function.Injective (fun c : Fin ((p - 1) / 2 + 1) => (((c : ℕ) : ZMod p)) ^ 2) :=
  sq_injective (by have := hp.out.two_le; omega)

/-! # Axiom audit for this file -/

section Audit

#print axioms Zeta5.HermiteBasis.det_coeffMatrix_unimodular
#print axioms Zeta5.HermiteBasis.hermite_linearIndependent
#print axioms Zeta5.HermiteBasis.det_coeffMatrix_hermite_ne_zero
#print axioms Zeta5.HermiteBasis.hermitePoly_map
#print axioms Zeta5.HermiteBasis.hermitePoly_monic
#print axioms Zeta5.HermiteBasis.hermitePoly_natDegree
#print axioms Zeta5.HermiteBasis.coeffMatrix_row_sum
#print axioms Zeta5.HermiteBasis.sq_injective
#print axioms Zeta5.HermiteBasis.sq_injective_half

end Audit

end

end HermiteBasis

end Zeta5
