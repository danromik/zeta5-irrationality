/-
Zeta5/LocalFunctional.lean

§§A–E OF THE PAPER'S SECTION 3 (pp. 5–7): the local rational functional.

These declarations are in a separate file because `Zeta5/InnerEntries.lean`, which proves
`Zeta5.Section3.entry_bounds_4_2_4_3`, needs `τ`, `τ^ext`, `Tpoly`, `resid` and Lemma 3.1,
and `Section3.lean` imports `InnerEntries.lean`.  `Section3.lean` imports this file.

Contents, in the paper's order:

  §A  p. 5      the functional `L` (`Lfun`) with `L(x^k) = B_k`, and `τ(P) = L(P''')/24`.
  §B  p. 6      `τ(x^d) = κ_d`, and the identities (3.2) and (3.3).
  §C  pp. 5–7   `d(r)`, the pole values, and the extension `τ^ext_Y` (`tauExt`, `tauExtOf`).
  §D  p. 6      the pullback identity (3.1), for monomials and at the poles.
  §E  p. 6      Lemma 3.1 (3.4), for every partial sum.
-/
import Zeta5.Arithmetic

namespace Zeta5

open Polynomial Finset

noncomputable section

/-! # §A.  The Bernoulli functional `L` and the functional `τ` (p. 5)

The paper (p. 5) introduces the linear functional `L` on `ℚ[x]` with `L(x^k) = B_k`, the
Bernoulli numbers with the convention `B_1 = -1/2` fixed on p. 3 — which is Mathlib's
`bernoulli`.  Then

    τ(P) = L(P''')/24 .
-/

/-- **p. 5**: the linear functional `L` on `ℚ[x]` with `L(x^k) = B_k`, the umbral Bernoulli
evaluation.  (Mathlib's `bernoulli` has `bernoulli 1 = -1/2`, the paper's convention.) -/
def Lfun (P : ℚ[X]) : ℚ := ∑ k ∈ range (P.natDegree + 1), P.coeff k * _root_.bernoulli k

/-- `L` may be computed over any range that covers the degree. -/
lemma Lfun_eq_range (P : ℚ[X]) {n : ℕ} (hn : P.natDegree < n) :
    Lfun P = ∑ k ∈ range n, P.coeff k * _root_.bernoulli k := by
  have hsub : range (P.natDegree + 1) ⊆ range n := by
    intro k hk
    simp only [Finset.mem_range] at hk ⊢
    omega
  have hzero : ∀ k ∈ range n, k ∉ range (P.natDegree + 1) →
      P.coeff k * _root_.bernoulli k = 0 := by
    intro k _ hk
    simp only [Finset.mem_range, not_lt] at hk
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]
  exact Finset.sum_subset hsub hzero

@[simp] lemma Lfun_zero : Lfun 0 = 0 := by simp [Lfun]

@[simp] lemma Lfun_monomial (k : ℕ) (a : ℚ) :
    Lfun (monomial k a) = a * _root_.bernoulli k := by
  rw [Lfun_eq_range (monomial k a) (n := k + 1)
    (lt_of_le_of_lt (natDegree_monomial_le a) (by omega))]
  simp [Polynomial.coeff_monomial]

lemma Lfun_add (P Q : ℚ[X]) : Lfun (P + Q) = Lfun P + Lfun Q := by
  set n := max (max P.natDegree Q.natDegree) (P + Q).natDegree + 1 with hn
  rw [Lfun_eq_range P (n := n) (by omega), Lfun_eq_range Q (n := n) (by omega),
    Lfun_eq_range (P + Q) (n := n) (by omega), ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun k _ => by rw [Polynomial.coeff_add]; ring)

lemma Lfun_neg (P : ℚ[X]) : Lfun (-P) = - Lfun P := by
  rw [Lfun_eq_range (-P) (n := P.natDegree + 1) (by simp),
    Lfun, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl (fun k _ => by rw [Polynomial.coeff_neg]; ring)

lemma Lfun_sub (P Q : ℚ[X]) : Lfun (P - Q) = Lfun P - Lfun Q := by
  rw [sub_eq_add_neg, Lfun_add, Lfun_neg, sub_eq_add_neg]

lemma Lfun_C_mul (a : ℚ) (P : ℚ[X]) : Lfun (C a * P) = a * Lfun P := by
  rw [Lfun_eq_range (C a * P) (n := P.natDegree + 1)
      (lt_of_le_of_lt (le_trans (Polynomial.natDegree_C_mul_le a P) le_rfl) (by omega)),
    Lfun, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun k _ => by rw [Polynomial.coeff_C_mul]; ring)

lemma Lfun_sum {ι : Type*} (s : Finset ι) (f : ι → ℚ[X]) :
    Lfun (∑ i ∈ s, f i) = ∑ i ∈ s, Lfun (f i) := by
  classical
  refine Finset.induction_on s (by simp) ?_
  intro a s ha ih
  rw [Finset.sum_insert ha, Finset.sum_insert ha, Lfun_add, ih]

/-- **p. 5**: `τ(P) = L(P''')/24`. -/
def tau (P : ℚ[X]) : ℚ := Lfun (derivative (derivative (derivative P))) / 24

@[simp] lemma tau_zero : tau 0 = 0 := by simp [tau]

lemma tau_add (P Q : ℚ[X]) : tau (P + Q) = tau P + tau Q := by
  simp only [tau, derivative_add, Lfun_add]; ring

lemma tau_neg (P : ℚ[X]) : tau (-P) = - tau P := by
  simp only [tau, derivative_neg, Lfun_neg]; ring

lemma tau_sub (P Q : ℚ[X]) : tau (P - Q) = tau P - tau Q := by
  rw [sub_eq_add_neg, tau_add, tau_neg, sub_eq_add_neg]

lemma tau_C_mul (a : ℚ) (P : ℚ[X]) : tau (C a * P) = a * tau P := by
  simp only [tau, derivative_C_mul, Lfun_C_mul]; ring

lemma tau_sum {ι : Type*} (s : Finset ι) (f : ι → ℚ[X]) :
    tau (∑ i ∈ s, f i) = ∑ i ∈ s, tau (f i) := by
  classical
  refine Finset.induction_on s (by simp) ?_
  intro a s ha ih
  rw [Finset.sum_insert ha, Finset.sum_insert ha, tau_add, ih]

/-! # §B.  `τ(x^d) = κ_d`, and the identities (3.2) and (3.3) (p. 6) -/

/-- **§3.1, p. 6**: `τ(z^d) = κ_d = d(d-1)(d-2)B_{d-3}/24`, with `κ_0 = κ_1 = κ_2 = 0`.
(`kappa` is the paper's `κ_d`, already in `Arithmetic.lean`.) -/
lemma tau_monomial (d : ℕ) (a : ℚ) : tau (monomial d a) = a * kappa d := by
  match d with
  | 0 => simp [tau, kappa]
  | 1 => simp [tau, kappa]
  | 2 => simp [tau, kappa]
  | (e + 3) =>
    have hd : derivative (derivative (derivative (monomial (e + 3) a)))
        = monomial e (a * ((e : ℚ) + 3) * ((e : ℚ) + 2) * ((e : ℚ) + 1)) := by
      simp only [derivative_monomial]
      push_cast
      try ring
    rw [tau, hd, Lfun_monomial, kappa]
    have h3 : ¬ (e + 3 < 3) := by omega
    rw [ite_eq_right h3]
    have hn : ((e + 3) * (e + 3 - 1) * (e + 3 - 2) : ℕ) = (e + 3) * (e + 2) * (e + 1) := by
      congr 1
    have he : (e + 3 - 3) = e := by omega
    rw [hn, he]
    push_cast
    ring

lemma tau_X_pow (d : ℕ) : tau (X ^ d) = kappa d := by
  have hm : (X : ℚ[X]) ^ d = monomial d (1 : ℚ) := by
    rw [← Polynomial.C_mul_X_pow_eq_monomial, map_one, one_mul]
  rw [hm, tau_monomial, one_mul]

/-- `τ(P) = ∑_d P_d κ_d`, over any range covering the degree (the formula of p. 6,
"`τ(∑ f_d z^d) = ∑ f_d κ_d`"). -/
lemma tau_eq_sum (P : ℚ[X]) {n : ℕ} (hn : P.natDegree < n) :
    tau P = ∑ d ∈ range n, P.coeff d * kappa d := by
  conv_lhs => rw [Polynomial.as_sum_range' P n hn]
  rw [tau_sum]
  exact Finset.sum_congr rfl (fun d _ => tau_monomial d (P.coeff d))

/-- `L(g(x+1)) = L(g(x)) + g'(0)`: the difference identity for `L`.  This is
`B_n(1) - B_n(0) = n·0^{n-1}`, i.e. DLMF (24.4.1); Mathlib proves it as `sum_bernoulli`. -/
lemma Lfun_comp_one_add (P : ℚ[X]) :
    Lfun (P.comp (X + 1)) = Lfun P + (derivative P).eval 0 := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [Polynomial.add_comp, Lfun_add, Lfun_add, hp, hq, derivative_add, Polynomial.eval_add]
    ring
  | monomial k a =>
    rw [Polynomial.monomial_comp, Lfun_C_mul, Lfun_monomial]
    -- `L((X+1)^k) = B_k + [k = 1]`
    have hdeg : ((X : ℚ[X]) + 1).natDegree = 1 := by
      simp
    have hpow : (((X : ℚ[X]) + 1) ^ k).natDegree < k + 1 := by
      have := Polynomial.natDegree_pow ((X : ℚ[X]) + 1) k
      rw [this, hdeg]
      omega
    have hL : Lfun (((X : ℚ[X]) + 1) ^ k) = _root_.bernoulli k + (if k = 1 then 1 else 0) := by
      rw [Lfun_eq_range _ hpow, Finset.sum_range_succ]
      have hcoef : ∀ j, (((X : ℚ[X]) + 1) ^ k).coeff j = (k.choose j : ℚ) := fun j =>
        Polynomial.coeff_X_add_one_pow ℚ k j
      simp only [hcoef, Nat.choose_self, Nat.cast_one, one_mul]
      rw [_root_.sum_bernoulli k]
      ring
    rw [hL]
    -- `(d/dx) (a x^k) at 0` is `a` if `k = 1` and `0` otherwise
    have hder : (derivative (monomial k a)).eval 0 = a * (if k = 1 then 1 else 0) := by
      rw [Polynomial.derivative_monomial]
      match k with
      | 0 => simp
      | 1 => simp
      | (e + 2) =>
        have : (e + 2 - 1) = e + 1 := by omega
        rw [this]
        simp [Polynomial.eval_monomial]
    rw [hder]
    ring

/-- `L(g(-1-x)) = L(g(x))`: the reflection identity for `L`.  This is
`B_n(1) = (-1)^n B_n`, i.e. DLMF (24.4.3); it follows from Mathlib's `sum_bernoulli`
together with `bernoulli_eq_zero_of_odd`. -/
lemma Lfun_comp_neg_one_sub (P : ℚ[X]) : Lfun (P.comp (-1 - X)) = Lfun P := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => rw [Polynomial.add_comp, Lfun_add, Lfun_add, hp, hq]
  | monomial k a =>
    rw [Polynomial.monomial_comp, Lfun_C_mul, Lfun_monomial]
    have hneg : ((-1 : ℚ[X]) - X) = -(X + 1) := by ring
    have hdeg : ((X : ℚ[X]) + 1).natDegree = 1 := by
      simp
    have hpow : (((X : ℚ[X]) + 1) ^ k).natDegree < k + 1 := by
      rw [Polynomial.natDegree_pow, hdeg]; omega
    have hL1 : Lfun (((X : ℚ[X]) + 1) ^ k) = _root_.bernoulli k + (if k = 1 then 1 else 0) := by
      rw [Lfun_eq_range _ hpow, Finset.sum_range_succ]
      have hcoef : ∀ j, (((X : ℚ[X]) + 1) ^ k).coeff j = (k.choose j : ℚ) := fun j =>
        Polynomial.coeff_X_add_one_pow ℚ k j
      simp only [hcoef, Nat.choose_self, Nat.cast_one, one_mul]
      rw [_root_.sum_bernoulli k]
      ring
    have hL : Lfun (((-1 : ℚ[X]) - X) ^ k)
        = (-1) ^ k * (_root_.bernoulli k + (if k = 1 then 1 else 0)) := by
      rw [hneg, neg_pow, ← hL1]
      have : ((-1 : ℚ[X]) ^ k) = C ((-1 : ℚ) ^ k) := by
        rw [map_pow]; norm_num
      rw [this, Lfun_C_mul]
    rw [hL]
    -- `(-1)^k (B_k + [k=1]) = B_k`
    match k with
    | 0 => norm_num
    | 1 => norm_num [_root_.bernoulli_one]
    | (e + 2) =>
      have hne : e + 2 ≠ 1 := by omega
      rw [ite_eq_right hne, add_zero]
      rcases Nat.even_or_odd (e + 2) with hev | hod
      · rw [hev.neg_one_pow, one_mul]
      · rw [_root_.bernoulli_eq_zero_of_odd hod (by omega)]
        ring

/-- **(3.2)** (p. 6): `τ_X(g(-1-x)) = -τ_X(g(x))`, the reflection identity, for the
polynomial part.  (For the simple poles it holds because `d(-1-r) = d(r)`; see
`dIdx_neg_one_sub` below.) -/
theorem eq_3_2 (P : ℚ[X]) : tau (P.comp (-1 - X)) = - tau P := by
  have hstep : ∀ Q : ℚ[X], derivative (Q.comp (-1 - X)) = -((derivative Q).comp (-1 - X)) := by
    intro Q
    rw [Polynomial.derivative_comp]
    simp
  have e2 : derivative (derivative (P.comp (-1 - X)))
      = (derivative (derivative P)).comp (-1 - X) := by
    rw [hstep, derivative_neg, hstep, neg_neg]
  have e3 : derivative (derivative (derivative (P.comp (-1 - X))))
      = -((derivative (derivative (derivative P))).comp (-1 - X)) := by
    rw [e2, hstep]
  rw [tau, e3, Lfun_neg, Lfun_comp_neg_one_sub, tau]
  ring

/-- **(3.3)** (p. 6): `τ_X(g(x+1) - g(x)) = g⁗(0)/24`, for `g` regular at zero (here: for a
polynomial, which is the case the paper's proofs use). -/
theorem eq_3_3 (P : ℚ[X]) :
    tau (P.comp (X + 1) - P)
      = (derivative (derivative (derivative (derivative P)))).eval 0 / 24 := by
  have hstep : ∀ Q : ℚ[X], derivative (Q.comp (X + 1)) = (derivative Q).comp (X + 1) := by
    intro Q
    rw [Polynomial.derivative_comp]
    simp
  have f3 : derivative (derivative (derivative (P.comp (X + 1))))
      = (derivative (derivative (derivative P))).comp (X + 1) := by
    rw [hstep, hstep, hstep]
  rw [tau, derivative_sub, derivative_sub, derivative_sub, f3, Lfun_sub, Lfun_comp_one_add]
  ring

/-! # §C.  `d(r)`, the pole values, and the extension `τ^ext_Y` to `𝓑_T` (pp. 5, 7) -/

/-- **p. 5**: `d(r) = r` for `r ≥ 0`, `d(r) = -r-1` for `r < 0`. -/
def dIdx (r : ℤ) : ℕ := if 0 ≤ r then r.toNat else (-r - 1).toNat

@[simp] lemma dIdx_natCast (j : ℕ) : dIdx (j : ℤ) = j := by simp [dIdx]

lemma dIdx_neg_natCast (j : ℕ) (hj : 1 ≤ j) : dIdx (-(j : ℤ)) = j - 1 := by
  have hj' : (1 : ℤ) ≤ (j : ℤ) := by exact_mod_cast hj
  unfold dIdx
  rw [ite_eq_right (by omega)]
  omega

/-- `d(-1-r) = d(r)`: the symmetry of the index that makes the reflection identity (3.2)
hold at the simple poles as well (p. 6). -/
lemma dIdx_neg_one_sub (r : ℤ) : dIdx (-1 - r) = dIdx r := by
  unfold dIdx
  split_ifs <;> omega

/-- **p. 7**: the extension of `τ` to `𝓑_T = 𝓐 ⊕ ⨁_ν ℚ_p·(z-r_ν)⁻¹`,

    `τ^ext_Y(f + ∑_ν c_ν/(z-r_ν)) = τ(f) + ∑_ν c_ν (H^{(5)}_{d(r_ν)} - Y)`.

Taking `Y = X` and `f` a polynomial, this is the `τ_X` of p. 5:
`τ_X(1/(x-r)) = H^{(5)}_{d(r)} - X`, extended "by polynomial division and simple partial
fractions". -/
def tauExt (Y : ℚ[X]) (P : ℚ[X]) (s : Finset ℤ) (c : ℤ → ℚ) : ℚ[X] :=
  C (tau P) + ∑ r ∈ s, C (c r) * (C (H5 (dIdx r)) - Y)

lemma tau_X_eq_zero : tau (X : ℚ[X]) = 0 := by
  have hm : (X : ℚ[X]) = monomial 1 (1 : ℚ) := by
    rw [← Polynomial.C_mul_X_pow_eq_monomial, map_one, one_mul, pow_one]
  rw [hm, tau_monomial, kappa_one, mul_zero]

/-! # §D.  The pullback identity (3.1) (p. 6)

    `μ_X(R) = τ_X(x⁵ R(-x²))`.

"For monomials this follows from three differentiations.  For a pole, use
`x⁵/(j²-x²) = -x³ - j²x - (j⁴/2)(1/(x-j) + 1/(x+j))` and
`H^{(5)}_j - H^{(5)}_{j-1} = j^{-5}`."  Both halves are proved exactly below. -/

/-- `κ_{2e+5} = (2e+5)(2e+4)(2e+3)B_{2e+2}/24`, with the natural subtractions resolved. -/
lemma kappa_two_mul_add_five (e : ℕ) :
    kappa (2 * e + 5)
      = ((2 * (e : ℚ) + 5) * (2 * (e : ℚ) + 4) * (2 * (e : ℚ) + 3))
          * _root_.bernoulli (2 * e + 2) / 24 := by
  rw [kappa, ite_eq_right (by omega)]
  have h1 : (2 * e + 5 - 1) = 2 * e + 4 := by omega
  have h2 : (2 * e + 5 - 2) = 2 * e + 3 := by omega
  have h3 : (2 * e + 5 - 3) = 2 * e + 2 := by omega
  rw [h1, h2, h3]
  push_cast
  ring

/-- **(3.1) for the monomials of (2.2)**: `μ(t^e) = τ(x⁵·(-x²)^e)`.

Both sides are `(-1)^e (2e+5)(2e+4)(2e+3)B_{2e+2}/24`; this is the "three differentiations"
of p. 6, and it identifies the paper's `μ(t^e)` of (2.2) with the pullback. -/
theorem eq_3_1_mono (e : ℕ) : muMono e = tau (X ^ 5 * (-(X ^ 2)) ^ e) := by
  have hx : (X : ℚ[X]) ^ 5 * (-(X ^ 2)) ^ e = C ((-1 : ℚ) ^ e) * X ^ (2 * e + 5) := by
    rw [neg_pow, ← pow_mul]
    have : ((-1 : ℚ[X]) ^ e) = C ((-1 : ℚ) ^ e) := by rw [map_pow]; norm_num
    rw [this]
    ring
  rw [hx, tau_C_mul, tau_X_pow, kappa_two_mul_add_five, muMono]
  ring

/-- **The partial fraction displayed on p. 6**,

    `x⁵/(j² - x²) = -x³ - j²x - (j⁴/2)(1/(x-j) + 1/(x+j))`,

with the denominators cleared: multiply through by `(x-j)(x+j) = x² - j²` and use
`(x²-j²)/(x-j) = x+j`, `(x²-j²)/(x+j) = x-j`.  It is an exact polynomial identity. -/
theorem eq_3_1_partialFraction (j : ℚ) :
    -(2 * X ^ 5)
      = 2 * (X ^ 2 - C j ^ 2) * (-(X ^ 3) - C j ^ 2 * X)
        + (-(C j ^ 4)) * (X + C j) + (-(C j ^ 4)) * (X - C j) := by
  ring

/-- `H^{(5)}_j - H^{(5)}_{j-1} = j^{-5}` (p. 6). -/
lemma H5_succ_sub (j : ℕ) (hj : 1 ≤ j) : H5 j = H5 (j - 1) + 1 / ((j : ℚ)) ^ 5 := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  rw [H5, H5, Finset.sum_Icc_succ_top (by omega)]

/-- **(3.1) at the simple poles of (2.3)**: `μ_X(1/(t+j²)) = τ_X(x⁵/(j²-x²))`.

The right-hand side is the value of `τ_X` on the partial fraction of p. 6
(`eq_3_1_partialFraction`): polynomial part `-x³ - j²x`, simple poles at `x = ±j` with
residue `-j⁴/2` at each.  Since `d(j) = j` and `d(-j) = j-1`, and
`H^{(5)}_{j-1} = H^{(5)}_j - j^{-5}`, the value is
`-1/4 - (j⁴/2)(H^{(5)}_j + H^{(5)}_{j-1} - 2X) = j⁴(X - H^{(5)}_j) - 1/4 + 1/(2j)`,
which is exactly `μ_X(1/(t+j²))` of (2.3). -/
theorem eq_3_1_pole (j : ℕ) (hj : 1 ≤ j) :
    muPole j
      = tauExt X (-(X ^ 3) - C ((j : ℚ) ^ 2) * X) {(j : ℤ), -(j : ℤ)}
          (fun _ => -((j : ℚ) ^ 4) / 2) := by
  have hj0 : ((j : ℚ)) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hj' : (1 : ℤ) ≤ (j : ℤ) := by exact_mod_cast hj
  have hne : ((j : ℤ)) ≠ -(j : ℤ) := by omega
  have hH := H5_succ_sub j hj
  have htau : tau (-(X ^ 3) - C ((j : ℚ) ^ 2) * X) = -(1 / 4) := by
    rw [tau_sub, tau_neg, tau_X_pow, kappa_three, tau_C_mul, tau_X_eq_zero, mul_zero, sub_zero]
  -- both sides are affine in `X`; put each in the normal form `C a * X + C b`
  have hL : muPole j
      = C ((j : ℚ) ^ 4) * X + C (-(((j : ℚ) ^ 4) * H5 j) + (-(1 / 4)) + 1 / (2 * (j : ℚ))) := by
    rw [muPole, map_add, map_add, map_neg, map_neg, map_mul]
    ring
  have hrel : (C ((j : ℚ) ^ 4) : ℚ[X]) = -2 * C (-((j : ℚ) ^ 4) / 2) := by
    have h2 : (C (-2 : ℚ) : ℚ[X]) = -2 := by
      rw [map_neg, map_ofNat]
    rw [← h2, ← map_mul]
    congr 1
    ring
  have hR : tauExt X (-(X ^ 3) - C ((j : ℚ) ^ 2) * X) {(j : ℤ), -(j : ℤ)}
        (fun _ => -((j : ℚ) ^ 4) / 2)
      = C ((j : ℚ) ^ 4) * X
        + C (-(1 / 4) + ((-((j : ℚ) ^ 4) / 2) * H5 j + (-((j : ℚ) ^ 4) / 2) * H5 (j - 1))) := by
    rw [tauExt, Finset.sum_pair hne, htau, dIdx_natCast, dIdx_neg_natCast j hj,
      map_add, map_add, map_mul, map_mul, hrel]
    ring
  have hscalar : (-(((j : ℚ) ^ 4) * H5 j) + (-(1 / 4)) + 1 / (2 * (j : ℚ)))
      = (-(1 / 4) + ((-((j : ℚ) ^ 4) / 2) * H5 j + (-((j : ℚ) ^ 4) / 2) * H5 (j - 1))) := by
    rw [hH]
    field_simp
    ring
  rw [hL, hR, hscalar]

/-! # §E.  Lemma 3.1 (p. 6)

> **Lemma 3.1.**  Let `T(z) = ∏_{ν=1}^t (z - r_ν)`, where the `r_ν` are distinct integers,
> `r_ν - r_η ∈ ℤ_p^×` for `ν ≠ η`, and `d(r_ν) < p`.  Let `Y ∈ ℤ_p[X]`.  For polynomials
> `U_j ∈ ℤ_p[z]` with `deg U_0 ≤ p+1`,
>
>     τ^ext_Y ( ∑_{j ≥ 0} p^j U_j(z) / T(z) )  ∈  ℤ_p[X].                       (3.4)

The proof on p. 6 is: divide, `U/T = P + ∑_ν c_ν/(z - r_ν)` with `c_ν = U(r_ν)/T'(r_ν)`;
`T` is monic with `ℤ_p` coefficients so `P` and the remainder stay in `ℤ_p[z]`; `T'(r_ν)` is
a `p`-adic unit by the hypothesis `r_ν - r_η ∈ ℤ_p^×`, so `c_ν ∈ ℤ_p`; the principal-part
values `H^{(5)}_{d(r_ν)} - Y` are integral because `d(r_ν) < p`; `τ(P_0) ∈ ℤ_p` because
`deg P_0 ≤ p+1` (that is `κ_d ∈ ℤ_p` for `d ≤ p+1`); and for `j ≥ 1` the factor `p^j`
absorbs the one power of `p` that `τ` can lose (`v_p(κ_d) ≥ -1`, von Staudt–Clausen).

SCOPE NOTE.  The series `∑_{j≥0} p^j U_j` is an element of the Tate algebra
`𝓐 = ℚ_p⟨z⟩`, which is not formalised here.  `lemma_3_1` below is (3.4) for every partial
sum `∑_{j≤J} p^j U_j`, with `J` arbitrary — i.e. the whole arithmetic content, uniformly in
`J`.  The passage from the partial sums to the sum of the series is the *analytic* wrapper
(`‖τ^ext_Y‖ ≤ p` on `𝓑_T`, `𝓑_T` complete, `ℤ_p[X]` closed in `ℚ_p[X]`), and is the only
part of Lemma 3.1 not formalized.  Nothing downstream uses more than the partial sums:
in §4 the far factors are expanded to the finite order that the entry bound needs. -/

section Lemma31

variable {p : ℕ} [hpf : Fact p.Prime]

/-- `v_p^G(A) ≥ 0` says exactly that every coefficient of `A` is a `p`-adic integer. -/
lemma vGAtLeast_zero_iff (A : ℚ[X]) :
    vGAtLeast p A 0 ↔ ∀ i, padicNorm p (A.coeff i) ≤ 1 := by
  rw [vGAtLeast_iff]
  simp

lemma vGAtLeast_C {a : ℚ} (ha : padicNorm p a ≤ 1) : vGAtLeast p (C a) 0 := by
  rw [vGAtLeast_zero_iff]
  intro i
  rcases eq_or_ne i 0 with rfl | hi
  · simpa using ha
  · rw [Polynomial.coeff_C, ite_eq_right hi, padicNorm.zero]
    norm_num

lemma vGAtLeast_add {A B : ℚ[X]} {c : ℤ} (hA : vGAtLeast p A c) (hB : vGAtLeast p B c) :
    vGAtLeast p (A + B) c := by
  rw [vGAtLeast_iff] at hA hB ⊢
  intro i
  rw [Polynomial.coeff_add]
  exact le_trans padicNorm.nonarchimedean (max_le (hA i) (hB i))

lemma vGAtLeast_neg {A : ℚ[X]} {c : ℤ} (hA : vGAtLeast p A c) : vGAtLeast p (-A) c := by
  rw [vGAtLeast_iff] at hA ⊢
  intro i
  rw [Polynomial.coeff_neg, padicNorm.neg]
  exact hA i

lemma vGAtLeast_sub {A B : ℚ[X]} {c : ℤ} (hA : vGAtLeast p A c) (hB : vGAtLeast p B c) :
    vGAtLeast p (A - B) c := by
  rw [sub_eq_add_neg]
  exact vGAtLeast_add hA (vGAtLeast_neg hB)

lemma padicNorm_pow (x : ℚ) (k : ℕ) : padicNorm p (x ^ k) = padicNorm p x ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, padicNorm.mul, ih, pow_succ]

lemma padicNorm_prod {ι : Type*} (s : Finset ι) (f : ι → ℚ)
    (h : ∀ i ∈ s, padicNorm p (f i) = 1) : padicNorm p (∏ i ∈ s, f i) = 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, padicNorm.mul, h a (Finset.mem_insert_self a s),
      ih (fun i hi => h i (Finset.mem_insert_of_mem hi)), one_mul]

/-- The value of a `ℤ_p`-integral polynomial at a `p`-adic integer is a `p`-adic integer. -/
lemma padicNorm_eval_le_one {A : ℚ[X]} (hA : vGAtLeast p A 0) {x : ℚ}
    (hx : padicNorm p x ≤ 1) : padicNorm p (A.eval x) ≤ 1 := by
  rw [Polynomial.eval_eq_sum_range]
  refine padicNorm.sum_le' (fun i _ => ?_) zero_le_one
  rw [padicNorm.mul, padicNorm_pow]
  have h1 := (vGAtLeast_zero_iff A).1 hA i
  have h2 : padicNorm p x ^ i ≤ 1 := pow_le_one₀ (padicNorm.nonneg _) hx
  nlinarith [padicNorm.nonneg (p := p) (A.coeff i), pow_nonneg (padicNorm.nonneg (p := p) x) i]

/-- The valuation subring `{x ∈ ℚ : v_p(x) ≥ 0}` of `ℚ`; used only to transport the
division algorithm by a monic polynomial into `ℤ_p[z]`. -/
def ZpSub (p : ℕ) [Fact p.Prime] : Subring ℚ where
  carrier := {x : ℚ | padicNorm p x ≤ 1}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' := fun hx hy => le_trans padicNorm.nonarchimedean (max_le hx hy)
  neg_mem' := fun hx => by simpa only [Set.mem_ofPred_eq, padicNorm.neg] using hx
  mul_mem' := fun hx hy => by
    simp only [Set.mem_ofPred_eq, padicNorm.mul] at *
    exact (mul_le_of_le_one_left (padicNorm.nonneg _) hx).trans hy

lemma coeffs_subset_ZpSub {A : ℚ[X]} (h : vGAtLeast p A 0) :
    (↑A.coeffs : Set ℚ) ⊆ ZpSub p := by
  intro x hx
  obtain ⟨i, _, rfl⟩ := Polynomial.mem_coeffs_iff.1 hx
  exact (vGAtLeast_zero_iff A).1 h i

/-- **Division by a monic `ℤ_p`-integral polynomial stays in `ℤ_p[z]`** — the step
"polynomial division ... has norm at most one from `ℤ_p[z]`" of p. 6.  Proved by carrying
the division out in `(ℤ_p ∩ ℚ)[z]` and mapping back. -/
lemma vGAtLeast_divMod_of_monic {T U : ℚ[X]} (hTm : T.Monic) (hT : vGAtLeast p T 0)
    (hU : vGAtLeast p U 0) :
    vGAtLeast p (U /ₘ T) 0 ∧ vGAtLeast p (U %ₘ T) 0 := by
  classical
  set R := ZpSub p with hRdef
  set T' : R[X] := T.toSubring R (coeffs_subset_ZpSub hT) with hT'def
  set U' : R[X] := U.toSubring R (coeffs_subset_ZpSub hU) with hU'def
  have hT'm : T'.Monic := (Polynomial.monic_toSubring T R _).2 hTm
  have hTmap : T'.map (Subring.subtype R) = T := Polynomial.map_toSubring _ _ _
  have hUmap : U'.map (Subring.subtype R) = U := Polynomial.map_toSubring _ _ _
  have hdiv : (U' /ₘ T').map (Subring.subtype R) = U /ₘ T := by
    rw [Polynomial.map_divByMonic (Subring.subtype R) hT'm, hTmap, hUmap]
  have hmod : (U' %ₘ T').map (Subring.subtype R) = U %ₘ T := by
    rw [Polynomial.map_modByMonic (Subring.subtype R) hT'm, hTmap, hUmap]
  constructor
  · rw [vGAtLeast_zero_iff]
    intro i
    rw [← hdiv, Polynomial.coeff_map]
    exact ((U' /ₘ T').coeff i).2
  · rw [vGAtLeast_zero_iff]
    intro i
    rw [← hmod, Polynomial.coeff_map]
    exact ((U' %ₘ T').coeff i).2

/-- **p. 6**: `T(z) = ∏_{ν}(z - r_ν)` for a finite set of integer roots. -/
def Tpoly (s : Finset ℤ) : ℚ[X] := ∏ r ∈ s, (X - C ((r : ℚ)))

lemma Tpoly_monic (s : Finset ℤ) : (Tpoly s).Monic :=
  monic_prod_of_monic _ _ (fun _ _ => monic_X_sub_C _)

lemma vGAtLeast_X_sub_intC (r : ℤ) : vGAtLeast p (X - C ((r : ℚ))) 0 := by
  rw [vGAtLeast_zero_iff]
  intro i
  rw [Polynomial.coeff_sub]
  refine le_trans padicNorm.sub (max_le ?_ ?_)
  · rw [Polynomial.coeff_X]
    split_ifs <;> simp
  · rw [Polynomial.coeff_C]
    split_ifs with hi
    · exact padicNorm.of_int r
    · rw [padicNorm.zero]; norm_num

lemma Tpoly_vGAtLeast (s : Finset ℤ) : vGAtLeast p (Tpoly s) 0 := by
  classical
  have := vGAtLeast_prod (p := p) s (fun r => X - C ((r : ℚ))) (fun _ => 0)
    (fun r _ => vGAtLeast_X_sub_intC r)
  simpa [Tpoly] using this

/-- `T'(r) = ∏_{q ≠ r}(r - q)` at a root `r` of `T` (p. 6). -/
lemma Tpoly_derivative_eval {s : Finset ℤ} {r : ℤ} (hr : r ∈ s) :
    (derivative (Tpoly s)).eval ((r : ℚ)) = ∏ q ∈ s.erase r, ((r : ℚ) - (q : ℚ)) := by
  classical
  have hfac : Tpoly s = (X - C ((r : ℚ))) * Tpoly (s.erase r) :=
    (Finset.mul_prod_erase s (fun q : ℤ => X - C ((q : ℚ))) hr).symm
  rw [hfac, derivative_mul, derivative_sub, derivative_X, derivative_C]
  simp [Tpoly, Polynomial.eval_prod]

/-- **p. 6**: the residue `c_ν = R(r_ν)/T'(r_ν)` of `U/T` at the simple pole `z = r_ν`,
where `R = U %ₘ T` is the remainder. -/
def resid (s : Finset ℤ) (U : ℚ[X]) (r : ℤ) : ℚ :=
  (U %ₘ Tpoly s).eval ((r : ℚ)) / (derivative (Tpoly s)).eval ((r : ℚ))

lemma Tpoly_eval_root {s : Finset ℤ} {r : ℤ} (hr : r ∈ s) : (Tpoly s).eval ((r : ℚ)) = 0 := by
  classical
  rw [Tpoly, Polynomial.eval_prod]
  exact Finset.prod_eq_zero hr (by simp)

/-- **Faithfulness check.**  The paper displays the residue as `c_ν = U(r_ν)/T'(r_ν)`
(p. 6), with `U` itself and not the remainder `R = U %ₘ T`.  The two agree, because
`U = T·(U /ₘ T) + R` and `T(r_ν) = 0`.  (`resid` is defined with `R` because that is what
the proof's "polynomial division and partial fractions" produces.) -/
lemma resid_eq_eval {s : Finset ℤ} (U : ℚ[X]) {r : ℤ} (hr : r ∈ s) :
    resid s U r = U.eval ((r : ℚ)) / (derivative (Tpoly s)).eval ((r : ℚ)) := by
  have hU : U = Tpoly s * (U /ₘ Tpoly s) + U %ₘ Tpoly s := by
    rw [add_comm]
    exact (Polynomial.modByMonic_add_div U (Tpoly s)).symm
  have : U.eval ((r : ℚ)) = (U %ₘ Tpoly s).eval ((r : ℚ)) := by
    conv_lhs => rw [hU]
    rw [Polynomial.eval_add, Polynomial.eval_mul, Tpoly_eval_root hr, zero_mul, zero_add]
  rw [resid, this]

/-- `τ^ext_Y(U/T)`: apply `τ^ext_Y` to the decomposition `U/T = (U /ₘ T) + ∑_ν c_ν/(z-r_ν)`
of p. 6 ("Polynomial division and partial fractions give `U/T = P + ∑ c_ν/(z - r_ν)`"). -/
def tauExtOf (Y : ℚ[X]) (s : Finset ℤ) (U : ℚ[X]) : ℚ[X] :=
  tauExt Y (U /ₘ Tpoly s) s (resid s U)

lemma tauExtOf_add (Y : ℚ[X]) (s : Finset ℤ) (U V : ℚ[X]) :
    tauExtOf Y s (U + V) = tauExtOf Y s U + tauExtOf Y s V := by
  have hmono := Tpoly_monic s
  simp only [tauExtOf, tauExt, resid, Polynomial.add_divByMonic, Polynomial.add_modByMonic,
    Polynomial.eval_add, tau_add, map_add, add_div, add_mul]
  rw [Finset.sum_add_distrib]
  ring

lemma tauExtOf_C_mul (Y : ℚ[X]) (s : Finset ℤ) (a : ℚ) (U : ℚ[X]) :
    tauExtOf Y s (C a * U) = C a * tauExtOf Y s U := by
  have hdiv : (C a * U) /ₘ Tpoly s = C a * (U /ₘ Tpoly s) := by
    rw [← Polynomial.smul_eq_C_mul, ← Polynomial.smul_eq_C_mul, Polynomial.smul_divByMonic]
  have hmod : (C a * U) %ₘ Tpoly s = C a * (U %ₘ Tpoly s) := by
    rw [← Polynomial.smul_eq_C_mul, ← Polynomial.smul_eq_C_mul, Polynomial.smul_modByMonic]
  have hres : ∀ r : ℤ, resid s (C a * U) r = a * resid s U r := by
    intro r
    rw [resid, resid, hmod, Polynomial.eval_mul, Polynomial.eval_C, mul_div_assoc]
  simp only [tauExtOf, tauExt, hdiv, tau_C_mul, hres, map_mul, Finset.mul_sum, mul_add]
  congr 1
  exact Finset.sum_congr rfl (fun r _ => by ring)

/-- The principal-part half of Lemma 3.1: under the lemma's hypotheses the residue terms
`∑_ν c_ν (H^{(5)}_{d(r_ν)} - Y)` lie in `ℤ_p[X]`. -/
lemma residPart_vGAtLeast {s : Finset ℤ}
    (hunit : ∀ r ∈ s, ∀ q ∈ s, r ≠ q → ¬ ((p : ℤ) ∣ (r - q)))
    (hd : ∀ r ∈ s, dIdx r < p)
    {Y : ℚ[X]} (hY : vGAtLeast p Y 0) {U : ℚ[X]} (hU : vGAtLeast p U 0) :
    vGAtLeast p (∑ r ∈ s, C (resid s U r) * (C (H5 (dIdx r)) - Y)) 0 := by
  classical
  refine vGAtLeast_sum (fun r hr => ?_)
  have hres : padicNorm p (resid s U r) ≤ 1 := by
    rw [resid, padicNorm.div, Tpoly_derivative_eval hr]
    have hden : padicNorm p (∏ q ∈ s.erase r, ((r : ℚ) - (q : ℚ))) = 1 := by
      refine padicNorm_prod _ _ (fun q hq => ?_)
      have hq' : q ∈ s := Finset.mem_of_mem_erase hq
      have hqr : r ≠ q := fun h => (Finset.ne_of_mem_erase hq) h.symm
      have hcast : ((r : ℚ) - (q : ℚ)) = (((r - q : ℤ)) : ℚ) := by push_cast; ring
      rw [hcast, padicNorm.int_eq_one_iff]
      exact hunit r hr q hq' hqr
    rw [hden, div_one]
    exact padicNorm_eval_le_one ((vGAtLeast_divMod_of_monic (Tpoly_monic s)
      (Tpoly_vGAtLeast s) hU).2) (padicNorm.of_int r)
  have h1 : vGAtLeast p (C (resid s U r)) 0 := vGAtLeast_C hres
  have hH5 : padicNorm p (H5 (dIdx r)) ≤ 1 := by
    rw [H5]
    refine padicNorm.sum_le' (fun v hv => ?_) zero_le_one
    simp only [Finset.mem_Icc] at hv
    have hvp : ¬ p ∣ v := by
      intro hdvd
      have := Nat.le_of_dvd (by omega) hdvd
      have := hd r hr
      omega
    have hv1 : padicNorm p ((v : ℚ)) = 1 := (padicNorm.nat_eq_one_iff v).2 hvp
    rw [padicNorm.div, padicNorm.one, padicNorm_pow, hv1, one_pow, div_one]
  have h2 : vGAtLeast p (C (H5 (dIdx r)) - Y) 0 := vGAtLeast_sub (vGAtLeast_C hH5) hY
  simpa using vGAtLeast_mul h1 h2

/-- **Lemma 3.1, the `j = 0` term**: if `U ∈ ℤ_p[z]` has `deg U ≤ p+1`, then
`τ^ext_Y(U/T) ∈ ℤ_p[X]`.  ("In the `j = 0` term the polynomial quotient has degree at most
`p+1`, so it too has integral value.") -/
theorem tauExtOf_vGAtLeast_zero (h7 : 7 ≤ p) {s : Finset ℤ}
    (hunit : ∀ r ∈ s, ∀ q ∈ s, r ≠ q → ¬ ((p : ℤ) ∣ (r - q)))
    (hd : ∀ r ∈ s, dIdx r < p)
    {Y : ℚ[X]} (hY : vGAtLeast p Y 0) {U : ℚ[X]} (hU : vGAtLeast p U 0)
    (hdeg : U.natDegree ≤ p + 1) :
    vGAtLeast p (tauExtOf Y s U) 0 := by
  have hquot := (vGAtLeast_divMod_of_monic (Tpoly_monic s) (Tpoly_vGAtLeast s) hU).1
  have hqdeg : (U /ₘ Tpoly s).natDegree ≤ p + 1 := by
    rw [Polynomial.natDegree_divByMonic U (Tpoly_monic s)]
    omega
  have htau : padicNorm p (tau (U /ₘ Tpoly s)) ≤ 1 := by
    rw [tau_eq_sum (U /ₘ Tpoly s) (n := p + 2) (by omega)]
    refine padicNorm.sum_le' (fun d hd' => ?_) zero_le_one
    rw [padicNorm.mul]
    have h1 := (vGAtLeast_zero_iff _).1 hquot d
    have hdp : d ≤ p + 1 := by
      simp only [Finset.mem_range] at hd'
      omega
    have h2 : padicNorm p (kappa d) ≤ 1 :=
      padicNorm_le_one_of_nonneg (padicValRat_kappa_nonneg p h7 hdp)
    nlinarith [padicNorm.nonneg (p := p) ((U /ₘ Tpoly s).coeff d),
      padicNorm.nonneg (p := p) (kappa d)]
  rw [tauExtOf, tauExt]
  exact vGAtLeast_add (vGAtLeast_C htau) (residPart_vGAtLeast hunit hd hY hU)

/-- **Lemma 3.1, the general term**: for `U ∈ ℤ_p[z]` of any degree,
`v_p^G(τ^ext_Y(U/T)) ≥ -1`.  ("Its analytic part can lose one power of `p`.") -/
theorem tauExtOf_vGAtLeast_neg_one (h7 : 7 ≤ p) {s : Finset ℤ}
    (hunit : ∀ r ∈ s, ∀ q ∈ s, r ≠ q → ¬ ((p : ℤ) ∣ (r - q)))
    (hd : ∀ r ∈ s, dIdx r < p)
    {Y : ℚ[X]} (hY : vGAtLeast p Y 0) {U : ℚ[X]} (hU : vGAtLeast p U 0) :
    vGAtLeast p (tauExtOf Y s U) (-1) := by
  have hquot := (vGAtLeast_divMod_of_monic (Tpoly_monic s) (Tpoly_vGAtLeast s) hU).1
  have htau : padicNorm p (tau (U /ₘ Tpoly s)) ≤ (p : ℚ) := by
    rw [tau_eq_sum (U /ₘ Tpoly s) (n := (U /ₘ Tpoly s).natDegree + 1) (by omega)]
    have hp0 : (0 : ℚ) ≤ (p : ℚ) := by positivity
    refine padicNorm.sum_le' (fun d _ => ?_) hp0
    rw [padicNorm.mul]
    have h1 := (vGAtLeast_zero_iff _).1 hquot d
    have h2 : padicNorm p (kappa d) ≤ (p : ℚ) :=
      padicNorm_le_of_neg_one_le (neg_one_le_padicValRat_kappa p h7 d)
    nlinarith [padicNorm.nonneg (p := p) ((U /ₘ Tpoly s).coeff d),
      padicNorm.nonneg (p := p) (kappa d)]
  have htauV : vGAtLeast p (C (tau (U /ₘ Tpoly s))) (-1) := by
    intro i hi
    rcases eq_or_ne i 0 with rfl | hne
    · rw [Polynomial.coeff_C_zero]
      exact neg_one_le_padicValRat_of_padicNorm_le htau
    · rw [Polynomial.coeff_C, ite_eq_right hne] at hi
      exact absurd rfl hi
  rw [tauExtOf, tauExt]
  exact vGAtLeast_add htauV
    (vGAtLeast_mono (by norm_num) (residPart_vGAtLeast hunit hd hY hU))

/-- **LEMMA 3.1** (p. 6), equation **(3.4)**, for every partial sum of the series.

`T(z) = ∏_{r ∈ s}(z - r)` with `s` a finite set of integers; `r - q ∈ ℤ_p^×` for distinct
`r, q ∈ s`; `d(r) < p` for `r ∈ s`; `Y ∈ ℤ_p[X]`; `U_j ∈ ℤ_p[z]` with `deg U_0 ≤ p+1`.
Then

    τ^ext_Y ( (∑_{j ≤ J} p^j U_j) / T )  ∈  ℤ_p[X],   for every J.

See the SCOPE NOTE above: the only part of the printed statement not covered is the passage
from the partial sums to the limit in the Tate algebra. -/
theorem lemma_3_1 (h7 : 7 ≤ p) {s : Finset ℤ}
    (hunit : ∀ r ∈ s, ∀ q ∈ s, r ≠ q → ¬ ((p : ℤ) ∣ (r - q)))
    (hd : ∀ r ∈ s, dIdx r < p)
    {Y : ℚ[X]} (hY : vGAtLeast p Y 0)
    (J : ℕ) (U : ℕ → ℚ[X]) (hU : ∀ j, vGAtLeast p (U j) 0)
    (hU0 : (U 0).natDegree ≤ p + 1) :
    vGAtLeast p (tauExtOf Y s (∑ j ∈ range (J + 1), C ((p : ℚ) ^ j) * U j)) 0 := by
  classical
  -- `∑_{j ≤ J} p^j U_j = U_0 + p · V` with `V = ∑_{1 ≤ j ≤ J} p^{j-1} U_j ∈ ℤ_p[z]`.
  set V : ℚ[X] := ∑ j ∈ range J, C ((p : ℚ) ^ j) * U (j + 1) with hV
  have hVint : vGAtLeast p V 0 := by
    refine vGAtLeast_sum (fun j _ => ?_)
    have hpj : padicNorm p (((p : ℚ)) ^ j) ≤ 1 := by
      rw [padicNorm_pow]
      have : padicNorm p ((p : ℚ)) ≤ 1 := by
        have := padicNorm.of_int (p := p) (p : ℤ)
        simpa using this
      exact pow_le_one₀ (padicNorm.nonneg _) this
    simpa using vGAtLeast_mul (vGAtLeast_C hpj) (hU (j + 1))
  have hsplit : (∑ j ∈ range (J + 1), C ((p : ℚ) ^ j) * U j) = U 0 + C ((p : ℚ)) * V := by
    rw [Finset.sum_range_succ' (fun j => C ((p : ℚ) ^ j) * U j) J, hV, Finset.mul_sum]
    simp only [pow_zero, map_one, one_mul]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← mul_assoc, ← map_mul, ← pow_succ']
  rw [hsplit, tauExtOf_add, tauExtOf_C_mul]
  refine vGAtLeast_add (tauExtOf_vGAtLeast_zero h7 hunit hd hY (hU 0) hU0) ?_
  have hCp : vGAtLeast p (C ((p : ℚ))) 1 := by
    intro i hi
    rcases eq_or_ne i 0 with rfl | hne
    · rw [Polynomial.coeff_C_zero]
      have hp1 : padicValRat p ((p : ℚ)) = 1 := by
        have : ((p : ℚ)) = ((p : ℤ) : ℚ) := by push_cast; ring
        rw [this, padicValRat.of_int]
        simp [padicValInt]
      omega
    · rw [Polynomial.coeff_C, ite_eq_right hne] at hi
      exact absurd rfl hi
  have := vGAtLeast_mul hCp (tauExtOf_vGAtLeast_neg_one h7 hunit hd hY hVint)
  simpa using this

/-! ### Extracting a power of `p` -/

/-- `v_p^G(p^E) = E` for an integer exponent `E`. -/
lemma vGAtLeast_C_zpow_p (E : ℤ) : vGAtLeast p (C ((p : ℚ) ^ E)) E := by
  intro i hi
  rcases eq_or_ne i 0 with rfl | hne
  · have : padicValRat p (((p : ℚ)) ^ E) = E := by
      rw [padicValRat.zpow, padicValRat.self hpf.out.one_lt, mul_one]
    rw [Polynomial.coeff_C_zero, this]
  · rw [Polynomial.coeff_C, ite_eq_right hne] at hi
    exact absurd rfl hi

/-- Extracting the power of `p` that the substitution `x = c + pz` produces:
if `A ∈ ℤ_p[X]` then `v_p^G(p^E A) ≥ E`. -/
lemma vGAtLeast_zpow_mul {A : ℚ[X]} {E : ℤ} (hA : vGAtLeast p A 0) :
    vGAtLeast p (C ((p : ℚ) ^ E) * A) E := by
  simpa using vGAtLeast_mul (vGAtLeast_C_zpow_p E) hA

end Lemma31

end

end Zeta5
