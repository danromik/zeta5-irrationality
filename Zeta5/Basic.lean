/-
Copyright (c) 2026.  Lean 4 formalisation of

    A. Fauzan, "ζ(5) is irrational", 17 September 2026.

This file contains only definitions (and facts that follow from them immediately).

Reference for every definition is the paper, by equation number.

A NOTE ON THE TWO ROLES OF `Polynomial ℚ`.
The paper uses two different indeterminates:

*  `t`, the variable of the rational functions the functional is applied to
   (`D_m(t)`, `t^e`, `1/(t+j^2)`);
*  `X`, the formal variable of the target ring `ℚ[X]` in which `μ_X` takes its values.

Both are modelled here by `Polynomial ℚ`.  They are *different copies*: a
`Polynomial ℚ` in the argument of `mu…` is a polynomial in `t`, a `Polynomial ℚ` in
the result is a polynomial in `X`.  Every definition below says which is meant.
-/
import Mathlib

namespace Zeta5

open Polynomial Finset

noncomputable section

/-! ## §2.1, equation (2.1): the parameters

`K = 40n`, `N = 3n`, `h = 37n`, `α = 3/40`, `λ = 37/40`, `H = 1 + 2α = 23/20`. -/

/-- `K = 40 n`, (2.1). -/
def K (n : ℕ) : ℕ := 40 * n

/-- `N = 3 n`, (2.1). -/
def N (n : ℕ) : ℕ := 3 * n

/-- `h = 37 n = K - N`, the size of the Hankel matrix, (2.1). -/
def h (n : ℕ) : ℕ := 37 * n

/-- `α = 3/40`, (2.1). -/
def alpha : ℚ := 3 / 40

/-- `λ = 37/40`, (2.1). -/
def lam : ℚ := 37 / 40

/-- `H = 1 + 2α = 23/20`, (2.1). -/
def Hcst : ℚ := 23 / 20

lemma h_eq_K_sub_N (n : ℕ) : h n = K n - N n := by
  simp [h, K, N]; omega

lemma Hcst_eq : Hcst = 1 + 2 * alpha := by norm_num [Hcst, alpha]

lemma lam_eq : lam = 1 - alpha := by norm_num [lam, alpha]

lemma Hcst_eq_lam_add : Hcst = lam + 3 * alpha := by norm_num [Hcst, lam, alpha]

/-! ## §2.1: `D_m` and `H^{(5)}_j` -/

/-- `D_m(t) = ∏_{j=1}^m (t + j²)`, §2.1.  A polynomial in `t`. -/
def D (m : ℕ) : ℚ[X] := ∏ j ∈ Icc 1 m, (X + C ((j : ℚ) ^ 2))

@[simp] lemma D_zero : D 0 = 1 := by simp [D]

lemma D_monic (m : ℕ) : (D m).Monic := by
  refine monic_prod_of_monic _ _ fun j _ => ?_
  exact monic_X_add_C _

@[simp] lemma D_natDegree (m : ℕ) : (D m).natDegree = m := by
  classical
  rw [D, natDegree_prod (Icc 1 m) (fun j : ℕ => (X + C ((j : ℚ) ^ 2)))
        (fun j _ => (monic_X_add_C ((j : ℚ) ^ 2)).ne_zero)]
  have hdeg : ∀ j ∈ Icc 1 m, (X + C ((j : ℚ) ^ 2)).natDegree = 1 :=
    fun j _ => natDegree_X_add_C _
  rw [Finset.sum_congr rfl hdeg]
  simp

lemma D_ne_zero (m : ℕ) : D m ≠ 0 := (D_monic m).ne_zero

/-- `H^{(5)}_j = ∑_{v=1}^j v^{-5}`, §2.1 (`H^{(5)}_0 = 0`). -/
def H5 (j : ℕ) : ℚ := ∑ v ∈ Icc 1 j, (1 : ℚ) / (v : ℚ) ^ 5

@[simp] lemma H5_zero : H5 0 = 0 := by simp [H5]

/-! ## §2.1, equations (2.2)–(2.3): the functional `μ_X` on the basis

The set `{t^e}_{e≥0} ∪ {1/(t+j²)}_{j≥1}` is a basis of the space of rational functions
with simple poles among the negative integer squares, so (2.2)–(2.3) *define* a unique
`ℚ`-linear functional with values in `ℚ[X]`.  Only the pole values depend on `X`, and
that dependence is affine. -/

/-- (2.2): `μ_X(t^e) = (-1)^e B_{2e+2}(2e+3)(2e+4)(2e+5)/24`, a rational number
(no `X`).  Mathlib's `bernoulli` uses the convention `bernoulli 1 = -1/2`, which is the
convention the paper states on p. 3. -/
def muMono (e : ℕ) : ℚ :=
  (-1) ^ e * _root_.bernoulli (2 * e + 2) * (2 * e + 3) * (2 * e + 4) * (2 * e + 5) / 24

/-- (2.3): `μ_X(1/(t+j²)) = j⁴(X - H^{(5)}_j) - 1/4 + 1/(2j)`, an affine polynomial in `X`. -/
def muPole (j : ℕ) : ℚ[X] :=
  C ((j : ℚ) ^ 4) * (X - C (H5 j)) - C (1 / 4) + C (1 / (2 * (j : ℚ)))

/-- Only the simple-pole values depend on `X`, and that dependence is affine (§2.1). -/
lemma muPole_degree_le (j : ℕ) : (muPole j).natDegree ≤ 1 := by
  unfold muPole
  compute_degree

/-- `μ` restricted to polynomials in `t` (the paper writes `μ` for this restriction);
its values do not involve `X`. -/
def muPoly (P : ℚ[X]) : ℚ := ∑ e ∈ P.support, P.coeff e * muMono e

@[simp] lemma muPoly_zero : muPoly 0 = 0 := by simp [muPoly]

/-! ## §2.3: the tail denominator and the residue decomposition

After the cancellation `D_N^6 / D_K = D_N^5 / D_tail` (p. 4, §2.3), the entries of `G_K`
are `μ_X` applied to `W(t) t^{i+j} / D_tail(t)` with `W = D_N^5`.  Since `D_tail` is monic
with the `K - N` distinct simple roots `-r²`, `N < r ≤ K`, polynomial division plus simple
partial fractions gives the value of `μ_X` explicitly. -/

/-- `D_tail = D_K / D_N = ∏_{N < j ≤ K} (t + j²)`, §2.3.  A polynomial in `t`. -/
def Dtail (n : ℕ) : ℚ[X] := ∏ j ∈ Ioc (N n) (K n), (X + C ((j : ℚ) ^ 2))

lemma Dtail_monic (n : ℕ) : (Dtail n).Monic :=
  monic_prod_of_monic _ _ fun _j _ => monic_X_add_C _

lemma D_mul_Dtail (n : ℕ) : D (N n) * Dtail n = D (K n) := by
  classical
  rw [D, D, Dtail, ← Finset.prod_union]
  · congr 1
    ext j
    simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> constructor <;> first
        | omega
        | (simp [K, N] at *; omega)
    · rintro ⟨h1, h2⟩
      by_cases hj : j ≤ N n
      · exact Or.inl ⟨h1, hj⟩
      · exact Or.inr ⟨by omega, h2⟩
  · simp only [Finset.disjoint_left, Finset.mem_Icc, Finset.mem_Ioc]
    rintro j ⟨_, h2⟩ ⟨h3, _⟩
    omega

/-- The residue of `A(t)/D_tail(t)` at the simple pole `t = -r²`, i.e. the coefficient of
`1/(t + r²)` in the simple-partial-fraction expansion (§2.1, "polynomial division and
simple partial fractions"). -/
def residue (n : ℕ) (A : ℚ[X]) (r : ℕ) : ℚ :=
  (A %ₘ Dtail n).eval (-(r : ℚ) ^ 2) / (derivative (Dtail n)).eval (-(r : ℚ) ^ 2)

/-- `μ_X` applied to `A(t)/D_tail(t)`: the polynomial part contributes `muPoly`, each
simple pole `-r²` contributes `residue · muPole r`.  This is the extension described after
(2.3). -/
def muOver (n : ℕ) (A : ℚ[X]) : ℚ[X] :=
  C (muPoly (A /ₘ Dtail n)) + ∑ r ∈ Ioc (N n) (K n), C (residue n A r) * muPole r

/-! ## §2.1, equations (2.4)–(2.6): the matrix, the determinant, the normalisations -/

/-- The numerator of the `(i,j)` entry of `G_K` after the cancellation of `D_N`:
`D_N(t)^5 t^{i+j}`.  (The paper writes the entry as `μ_X(D_N(t)^6 t^{i+j}/D_K(t))`; by
`D_mul_Dtail` the two rational functions are equal.) -/
def entryNum (n : ℕ) (i j : ℕ) : ℚ[X] := (D (N n)) ^ 5 * X ^ (i + j)

/-- (2.4): the `h × h` Hankel matrix `G_K(X) = [μ_X(D_N(t)^6 t^{i+j} / D_K(t))]_{0≤i,j<h}`,
with entries in `ℚ[X]`. -/
def G (n : ℕ) : Matrix (Fin (h n)) (Fin (h n)) ℚ[X] :=
  fun i j => muOver n (entryNum n i j)

/-- `G_K` is a Hankel matrix: the entry depends only on `i + j`. -/
lemma G_hankel (n : ℕ) (i j i' j' : Fin (h n)) (hij : (i : ℕ) + j = (i' : ℕ) + j') :
    G n i j = G n i' j' := by
  simp [G, entryNum, hij]

/-- (2.4): `Δ_K(X) = det G_K(X)`. -/
def Delta (n : ℕ) : ℚ[X] := (G n).det

/-- "Only the simple-pole values depend on `X`, and that dependence is affine" (p. 3):
every value of `μ_X` on the rational functions of (2.4) is a polynomial of degree ≤ 1. -/
lemma muOver_natDegree_le (n : ℕ) (A : ℚ[X]) : (muOver n A).natDegree ≤ 1 := by
  classical
  refine le_trans (Polynomial.natDegree_add_le _ _) ?_
  refine max_le (le_trans (Polynomial.natDegree_C _).le (by norm_num)) ?_
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun r _ => ?_
  exact le_trans (Polynomial.natDegree_C_mul_le _ _) (muPole_degree_le r)

/-- Every entry of `G_K` is affine in `X` (2.4). -/
lemma G_natDegree_le (n : ℕ) (i j : Fin (h n)) : (G n i j).natDegree ≤ 1 :=
  muOver_natDegree_le n _

/-- `deg Δ_K ≤ h`: the determinant of an `h × h` matrix of affine entries.
Together with (2.9) (`[X^h]Δ_K ≠ 0`) this gives `deg Δ_K = h` exactly. -/
lemma Delta_natDegree_le (n : ℕ) : (Delta n).natDegree ≤ h n := by
  classical
  rw [Delta, Matrix.det_apply']
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun σ _ => ?_
  refine le_trans (Polynomial.natDegree_mul_le) ?_
  have h1 : (((Equiv.Perm.sign σ : ℤ) : ℚ[X])).natDegree = 0 := by simp
  rw [h1, zero_add]
  refine le_trans (Polynomial.natDegree_prod_le _ _) ?_
  calc ∑ i : Fin (h n), (G n (σ i) i).natDegree
      ≤ ∑ _i : Fin (h n), 1 := Finset.sum_le_sum fun i _ => G_natDegree_le n _ _
    _ = h n := by simp

/-- (2.5): `S_K = (K!)^{2h} 4^{h-1} / ((N!)^{12h} ∏_{i=1}^{h-1} ((2i)!)²)`. -/
def S (n : ℕ) : ℚ :=
  ((K n).factorial : ℚ) ^ (2 * h n) * 4 ^ (h n - 1) /
    (((N n).factorial : ℚ) ^ (12 * h n) * ∏ i ∈ Icc 1 (h n - 1), (((2 * i).factorial : ℚ)) ^ 2)

lemma S_pos (n : ℕ) : 0 < S n := by
  unfold S
  apply div_pos
  · apply mul_pos
    · exact pow_pos (by exact_mod_cast Nat.factorial_pos _) _
    · positivity
  · apply mul_pos
    · exact pow_pos (by exact_mod_cast Nat.factorial_pos _) _
    · refine Finset.prod_pos fun i _hi => ?_
      exact pow_pos (by exact_mod_cast Nat.factorial_pos _) _

/-- (2.5): `F_K = S_K Δ_K`. -/
def F (n : ℕ) : ℚ[X] := C (S n) * Delta n

/-! ## §4: the local data

`ℓ_A(a) = #{1 ≤ j ≤ A : j ≡ ±a (mod p)}` and `m_A = ⌊A/p⌋` (p. 10). -/

/-- `ℓ_A(a) = #{1 ≤ j ≤ A : j ≡ a or -a (mod p)}`, p. 10. -/
def ell (p A a : ℕ) : ℕ :=
  ((Icc 1 A).filter (fun j => j % p = a % p ∨ (j + a) % p = 0)).card

/-- `m_A = ⌊A/p⌋`, p. 10. -/
def mFloor (p A : ℕ) : ℕ := A / p

/-! ### §4.1, (4.4)–(4.8): the inner allocation and `γ_p^in`

The paper fixes `L_0 = 4M+10`, `m = (p-1)/2`, `b_a = 3 ℓ_N(a)`, defines `T, E` by
`mT + E = h - L_0 + 3(N - m_N)` with `0 ≤ E < m`, gives `ε_a = 1` to the first `E`
classes in decreasing order of `ℓ_K(a)` (ties arbitrary), and sets
`L_a = T - b_a + ε_a`, `Z_a = T + ε_a`.

The tie-breaking is not canonical, so rather than making an arbitrary choice we record the
allocation as *data satisfying the paper's conditions*.  The only property of the ordering
that the proof of Proposition 4.1 uses is `hExtraOrder` below ("the definition of the
extras gives `ℓ_K(a) ≥ ℓ_K(c)`", p. 11). -/

/-- `L_0 = 4M + 10`, p. 10. -/
def L0 (M : ℕ) : ℕ := 4 * M + 10

/-- `m = (p-1)/2`, p. 10. -/
def mHalf (p : ℕ) : ℕ := (p - 1) / 2

/-- `b_a = 3 ℓ_N(a)`, p. 10. -/
def bCoef (n p a : ℕ) : ℕ := 3 * ell p (N n) a

/-- **(4.1)**: `p` is an *inner* prime for the parameters `(n, M)`:
`K ∈ 40ℤ_{>0}`, `K ≥ 200M²`, `K/M < p ≤ K/3`, with `M ≥ 40`.

Note `K n = 40 n` is automatic; positivity of `n` follows from `200 M² ≤ K n`. -/
structure IsInnerPrime (n M p : ℕ) : Prop where
  /-- `p` is prime. -/
  prime : p.Prime
  /-- `M ≥ 40`. -/
  cutoff : 40 ≤ M
  /-- `K ≥ 200 M²`. -/
  size : 200 * M ^ 2 ≤ K n
  /-- `K/M < p`. -/
  lower : K n < p * M
  /-- `p ≤ K/3`. -/
  upper : 3 * p ≤ K n

/-- (4.1) forces `p > 200 M ≥ 8000` (paper, p. 10: "Then `p > 200M` and `p² > 5K`"). -/
lemma IsInnerPrime.gt_200M {n M p : ℕ} (hp : IsInnerPrime n M p) : 200 * M < p := by
  have hM0 : 0 < M := lt_of_lt_of_le (by norm_num) hp.cutoff
  have h1 : 200 * M * M < p * M := by
    calc 200 * M * M = 200 * M ^ 2 := by ring
      _ ≤ K n := hp.size
      _ < p * M := hp.lower
  exact lt_of_mul_lt_mul_right h1 (Nat.zero_le M)

/-- Hence the number of nonzero residue classes `m = (p-1)/2` is positive. -/
lemma IsInnerPrime.mHalf_pos {n M p : ℕ} (hp : IsInnerPrime n M p) : 0 < mHalf p := by
  have := hp.gt_200M
  have := hp.cutoff
  unfold mHalf
  omega

/-- An allocation of rows to residue classes as prescribed by (4.4) on p. 10, for
parameters `n` (so `K = 40n`), cutoff `M` and inner prime `p`. -/
structure InnerAlloc (n M p : ℕ) where
  /-- `T` of (4.4). -/
  T : ℤ
  /-- `E` of (4.4). -/
  E : ℕ
  /-- The extras `ε_a ∈ {0,1}` of (4.4). -/
  eps : ℕ → ℕ
  /-- (4.4): `0 ≤ E < m`. -/
  hE : E < mHalf p
  /-- (4.4): `m T + E = h - L_0 + 3(N - m_N)`. -/
  hTE : (mHalf p : ℤ) * T + E
      = (h n : ℤ) - L0 M + 3 * ((N n : ℤ) - mFloor p (N n))
  /-- `ε_a ∈ {0,1}`. -/
  hEps01 : ∀ a, eps a = 0 ∨ eps a = 1
  /-- Exactly `E` classes get an extra row. -/
  hEpsSum : ∑ a ∈ Icc 1 (mHalf p), eps a = E
  /-- "the first `E` classes in decreasing order of `ℓ_K(a)`": the only consequence used. -/
  hExtraOrder : ∀ a ∈ Icc 1 (mHalf p), ∀ c ∈ Icc 1 (mHalf p),
      eps a = 1 → eps c = 0 → ell p (K n) c ≤ ell p (K n) a

namespace InnerAlloc

variable {n M p : ℕ}

/-- `L_a = T - b_a + ε_a`, p. 10 (the number of rows assigned to the class `t = -a²`). -/
def L (A : InnerAlloc n M p) (a : ℕ) : ℤ := A.T - bCoef n p a + A.eps a

/-- `Z_a = L_a + b_a = T + ε_a`, p. 10. -/
def Z (A : InnerAlloc n M p) (a : ℕ) : ℤ := A.T + A.eps a

lemma Z_eq (A : InnerAlloc n M p) (a : ℕ) : A.Z a = A.L a + bCoef n p a := by
  simp [Z, L]; ring

/-- Twice the ordinary row weight `w_{a,i} = i + b_a - (ℓ_K(a)+4)/2` of (4.6), `a > 0`.
Weights are half-integers, so we carry `2 w` as an integer throughout. -/
def w2 (_A : InnerAlloc n M p) (a i : ℕ) : ℤ :=
  2 * i + 2 * bCoef n p a - (ell p (K n) a : ℤ) - 4

/-- Twice the zero-class row weight
`w_{0,i} = min(2i + 6m_N - m_K + 1/2, min_{1≤c≤m}(Z_c - (ℓ_K(c)+4)/2))` of (4.7). -/
def w2zero (A : InnerAlloc n M p) (i : ℕ) : ℤ :=
  min (4 * i + 12 * (mFloor p (N n) : ℤ) - 2 * (mFloor p (K n) : ℤ) + 1)
    (((Icc 1 (mHalf p)).inf' (by
        refine Finset.nonempty_Icc.2 ?_
        have := A.hE
        omega)
      (fun c => 2 * A.Z c - (ell p (K n) c : ℤ) - 4)))

/-- (4.8): `γ_p^in = 2 ∑_{a=0}^{m} ∑_{i=0}^{L_a-1} w_{a,i}`, an integer.

The `a = 0` block has `L_0 = 4M+10` rows (p. 10).  For `a ≥ 1` the number of rows is `L_a`,
which the paper proves to be nonnegative; `Int.toNat` truncates at `0`, so this definition
agrees with the paper exactly where `L_a ≥ 0`, which is where Proposition 4.1 places it. -/
def gammaIn (A : InnerAlloc n M p) : ℤ :=
  (∑ i ∈ range (L0 M), A.w2zero i)
    + ∑ a ∈ Icc 1 (mHalf p), ∑ i ∈ range (A.L a).toNat, A.w2 a i

end InnerAlloc

/-! ### §4.2, (4.10) and (4.14): the outer range and `γ_p^out` -/

/-- (4.10): the rank bound `r_p = max(0, K + 4N - 2p + 2)`. -/
def rOut (n p : ℕ) : ℤ := max 0 ((K n : ℤ) + 4 * N n - 2 * p + 2)

/-- `v = K - p⌊K/p⌋ = K mod p`, p. 13. -/
def vOut (n p : ℕ) : ℕ := K n % p

/-- `u = max(0, N + v - p + 1)`, p. 13. -/
def uOut (n p : ℕ) : ℤ := max 0 ((N n : ℤ) + vOut n p - p + 1)

/-- `t_p = min(N, v) + u`, p. 13. -/
def tOut (n p : ℕ) : ℤ := min (N n : ℤ) (vOut n p) + uOut n p

/-- (4.14): the outer local bound `γ_p^out`, and `γ_p^out = 0` for `p > K` (§5, p. 13). -/
def gammaOut (n p : ℕ) : ℤ :=
  if K n < p then 0
  else if K n < 2 * p then
    -7 * ((K n : ℤ) - p) + 6 * tOut n p - 1 - min (rOut n p) ((p : ℤ) - 1 - N n + uOut n p)
  else
    -7 * ((K n : ℤ) - p) + 3 + 12 * N n + 5 * tOut n p - min (rOut n p) ((p : ℤ) + uOut n p)

/-! ## §5, (5.1)–(5.3), (2.6): the normalisation -/

/-- `v_p(S_K)`, the `p`-adic valuation of the constant (2.5).

Formula (5.3) of the paper expresses this by Legendre's formula,
`v_p(S_K) = 2h ∑_{a≥1}⌊K/p^a⌋ - 12h ∑_{a≥1}⌊N/p^a⌋ - 2∑_{i=1}^{h-1}∑_{a≥1}⌊2i/p^a⌋
+ (h-1)v_p(4)`.  We take the valuation itself as the definition, which is what (5.1)
actually needs; (5.3) is then a lemma about it that no statement here depends on. -/
def vS (n p : ℕ) : ℤ := padicValRat p (S n)

/-- A choice of allocation (4.4) for every inner prime.

The allocation exists only for inner primes: for `p = 2` one has `m = (p-1)/2 = 0` and the
condition `0 ≤ E < m` of (4.4) is unsatisfiable, so `InnerAlloc n M 2` is empty.  Indexing
the family by `IsInnerPrime` is what keeps the statements below from being vacuous. -/
def InnerAllocFamily (n M : ℕ) : Type := ∀ p, IsInnerPrime n M p → InnerAlloc n M p

open scoped Classical in
/-- (5.1): the exponent `L_p(K,M)`.

The three branches are the paper's: `pM ≤ K` (small primes, bound (3.12)),
`pM > K` and `3p ≤ K` (inner range, Proposition 4.1), `3p > K` (outer range,
Proposition 4.3).  In the second branch the hypotheses of `IsInnerPrime` are exactly
`pM > K`, `3p ≤ K` together with the standing assumptions `p` prime, `M ≥ 40`,
`K ≥ 200M²`; when those standing assumptions fail the definition falls through to the
outer branch, which is harmless because `L_p` is only ever used under them. -/
noncomputable def Lp (n M : ℕ) (Alloc : InnerAllocFamily n M) (p : ℕ) : ℤ :=
  if p * M ≤ K n then
    -6 * (h n : ℤ) * (Nat.log p (5 * K n)) - (h n : ℤ) * padicValNat p 24
  else if hin : IsInnerPrime n M p then
    vS n p + (Alloc p hin).gammaIn
  else vS n p + gammaOut n p

/-- (5.2): `m_{K,M} = ∏_{p ≤ 2h} p^{-L_p(K,M)}`, a positive rational. -/
noncomputable def mKM (n M : ℕ) (Alloc : InnerAllocFamily n M) : ℚ :=
  ∏ p ∈ (range (2 * h n + 1)).filter Nat.Prime, (p : ℚ) ^ (-(Lp n M Alloc p))

/-- (2.6): `Q_{K,M}(X) = m_{K,M} F_K(X)`. -/
noncomputable def Q (n M : ℕ) (Alloc : InnerAllocFamily n M) : ℚ[X] :=
  C (mKM n M Alloc) * F n

lemma mKM_pos (n M : ℕ) (Alloc : InnerAllocFamily n M) : 0 < mKM n M Alloc := by
  refine Finset.prod_pos fun p hp => ?_
  have hp' : Nat.Prime p := (Finset.mem_filter.1 hp).2
  have hp0 : (0 : ℚ) < p := by exact_mod_cast hp'.pos
  exact zpow_pos hp0 _

/-! ## The value `ζ(5)`

The paper's `ζ(5)` is `∑_{v≥1} v^{-5}`. -/

/-- `ζ(5) = ∑_{v ≥ 1} v^{-5}`. -/
def zeta5 : ℝ := ∑' v : ℕ, (1 : ℝ) / ((v : ℝ) + 1) ^ 5

/-- Evaluation `ℚ[X] → ℝ` at the real number `ζ(5)`, as a ring homomorphism. -/
def evalZeta5Hom : ℚ[X] →+* ℝ := (Polynomial.aeval (zeta5 : ℝ)).toRingHom

/-- Evaluation of a `ℚ[X]` at the real number `ζ(5)`. -/
def evalZeta5 (P : ℚ[X]) : ℝ := evalZeta5Hom P

@[simp] lemma evalZeta5_C (q : ℚ) : evalZeta5 (C q) = (q : ℝ) := by
  simp [evalZeta5, evalZeta5Hom]

@[simp] lemma evalZeta5_mul (P R : ℚ[X]) :
    evalZeta5 (P * R) = evalZeta5 P * evalZeta5 R := by
  simp [evalZeta5, evalZeta5Hom]

/-! ## §2.4, (2.10): the positive weight

`w(y) = (2π)⁴ y⁵ ∑_{ℓ≥1} ℓ⁴ e^{-2πℓy} / 12`. -/

/-- (2.10): the weight `w(y) = (2π)⁴y⁵ (∑_{ℓ≥1} ℓ⁴ e^{-2πℓy})/12`, positive on `(0,∞)`. -/
def wt (y : ℝ) : ℝ :=
  (2 * Real.pi) ^ 4 * y ^ 5 / 12 *
    ∑' l : ℕ, ((l : ℝ) + 1) ^ 4 * Real.exp (-(2 * Real.pi * ((l : ℝ) + 1) * y))

/-! ## §5.1, (5.4)–(5.6): the limiting functions in the variable `x = K/p`

These are the functions that convert the discrete inner exponents into integrals.
Everything here is a literal transcription of p. 14; the variables are real. -/

/-- `ℓ(x,z) = ⌊x - z⌋ + ⌊x + z⌋ + 1`, p. 14 (the continuous form of `ℓ_A(a)`). -/
def ellR (x z : ℝ) : ℝ := (⌊x - z⌋ : ℝ) + (⌊x + z⌋ : ℝ) + 1

/-- `b(x,z) = 3 ℓ(αx, z)`, p. 14 (the continuous form of `b_a = 3ℓ_N(a)`). -/
def bR (x z : ℝ) : ℝ := 3 * ellR ((alpha : ℝ) * x) z

/-- `T = ⌊2Hx⌋`, p. 14. -/
def TR (x : ℝ) : ℝ := (⌊2 * (Hcst : ℝ) * x⌋ : ℝ)

/-- `s = Hx - T/2`, p. 14. -/
def sR (x : ℝ) : ℝ := (Hcst : ℝ) * x - TR x / 2

/-- `q = ⌊2x⌋`, p. 14. -/
def qR (x : ℝ) : ℝ := (⌊2 * x⌋ : ℝ)

/-- `n₊ = (2x - q)/2`, p. 14. -/
def nPlus (x : ℝ) : ℝ := (2 * x - qR x) / 2

/-- **(5.4)**: `Γ(x) = ∫_0^{1/2}(T - b(x,z))(T + b(x,z) - ℓ(x,z) - 5) dz
+ s(2T - q - 5) + (s - n₊)₊`. -/
def Gam (x : ℝ) : ℝ :=
  (∫ z in (0 : ℝ)..(1 / 2 : ℝ), (TR x - bR x z) * (TR x + bR x z - ellR x z - 5))
    + sR x * (2 * TR x - qR x - 5) + max 0 (sR x - nPlus x)

/-- `J(u) = mu - m(m+1)/4` with `m = ⌊2u⌋`, (5.5). -/
def JR (u : ℝ) : ℝ := (⌊2 * u⌋ : ℝ) * u - (⌊2 * u⌋ : ℝ) * ((⌊2 * u⌋ : ℝ) + 1) / 4

/-- **(5.5)**: `𝒩(x) = 2λx⌊x⌋ - 12λx⌊αx⌋ - 2J(λx)` (the limiting form of `v_p(S_K)/p`). -/
def NR (x : ℝ) : ℝ :=
  2 * (lam : ℝ) * x * (⌊x⌋ : ℝ) - 12 * (lam : ℝ) * x * (⌊(alpha : ℝ) * x⌋ : ℝ)
    - 2 * JR ((lam : ℝ) * x)

/-- **(5.6)**: `R(x) = -Γ(x) - 𝒩(x)`.  This is the integrand of (5.11). -/
def RR (x : ℝ) : ℝ := -Gam x - NR x

/-! ## The Gauss valuation `v_p^G` of §3

`v_p^G(A)` is the minimum of the `p`-adic valuations of the coefficients of `A ∈ ℚ_p[X]`,
with `v_p^G(0) = +∞` (p. 5).  We only ever need lower bounds for it, so we use the
predicate form, which avoids `ℤ∞`. -/

/-- `v_p^G(A) ≥ c`: every nonzero coefficient of `A` has `p`-adic valuation at least `c`. -/
def vGAtLeast (p : ℕ) (A : ℚ[X]) (c : ℤ) : Prop :=
  ∀ i, A.coeff i ≠ 0 → c ≤ padicValRat p (A.coeff i)

/-! ## The constants of §§5–7

`A_*`, `A_M` of (5.19)–(5.20), `U` of (6.4), and `I_out` of (5.10). -/

/-- (5.10): `I_out = 127751/96000`. -/
def Iout : ℚ := 127751 / 96000

/-- (5.18): `∫_3^{20} R(x)/x³ dx = 322437603634266857629/7535670527041937280000`
(evaluated exactly in Appendix B). -/
def I320 : ℚ := 322437603634266857629 / 7535670527041937280000

/-- (5.16): `∫_{20}^∞ R(x)/x³ dx ≤ -2689/48000`. -/
def I20inf : ℚ := -2689 / 48000

/-- (5.19): `A_* = 9928298118277006344769 / 7535670527041937280000`. -/
def Astar : ℚ := 9928298118277006344769 / 7535670527041937280000

/-- The bookkeeping behind (5.21): `A_* = I_out + ∫_3^{20}R/x³ + (-2689/48000)`,
i.e. (5.19) is exactly what (5.10), (5.18) and (5.16) combine to.  A known-answer control
on the three constants: it is an exact identity between the printed rationals. -/
lemma Astar_eq : Astar = Iout + I320 + I20inf := by
  norm_num [Astar, Iout, I320, I20inf]

/-- (5.20): `A_M = A_* + 7λ/M - (2923/240 - 1/4)/M² + 32/M³`. -/
def AM (M : ℕ) : ℚ := Astar + 7 * lam / M - (2923 / 240 - 1 / 4) / (M : ℚ) ^ 2 + 32 / (M : ℚ) ^ 3

/-- (6.4): `U = -2733991/2000000`. -/
def Ubar : ℚ := -2733991 / 2000000

/-- (7.2), first inequality: `-1600 (A_200 + U) > 139/5`.
This is a decidable inequality between explicit rationals, and it is true. -/
lemma eq_7_2_M200 : -1600 * (AM 200 + Ubar) > 139 / 5 := by
  norm_num [AM, Astar, Ubar, lam]

/-- (7.2), second inequality: `-1600 (A_100000 + U) > 7907/100`. -/
lemma eq_7_2_M100000 : -1600 * (AM 100000 + Ubar) > 7907 / 100 := by
  norm_num [AM, Astar, Ubar, lam]

end

end Zeta5
