/-
Zeta5/Lemma33.lean

**LEMMA 3.3** (p. 8) of

    A. Fauzan, "ζ(5) is irrational", 17 September 2026,

together with the pullback bookkeeping (3.1) that turns the entries of (3.11) into values of
`τ_X` on rational functions with the `2K` integer poles `0 < |r| ≤ K`.  This file discharges
`Zeta5.CrudeBound.crude_entry_bound`.  It contains NO `sorry` and NO `axiom`.

PAPER STATEMENT (p. 8, checked against the page image):

> **Lemma 3.3.**  Let `A` be integer-valued on `ℤ_p`, with `deg A ≤ d`, and put
> `g(x) = (K!)² A(x) / ∏_{-K≤r≤K, r≠0}(x-r)`.  Then
>
>     v_p^G(τ_X(g)) ≥ -6⌊log_p max(2K, d+1)⌋ - v_p(24).                            (3.10)

Here `τ_X(g)` is `tauExtOf X (poles K) ((K!)²A)` (polynomial division by
`T(x) = ∏_{0<|r|≤K}(x-r)`, then `τ` on the quotient and `c_r ↦ c_r(H^{(5)}_{d(r)} - X)` on the
simple poles, p. 5–6).  The hypothesis used is `A(ℤ) ⊂ ℤ_p`, which the paper's `A(ℤ_p) ⊂ ℤ_p`
implies.

CONTENTS.

  §1  `poles K`, `T = Tpoly (poles K)`; `D_K(-x²) = (-1)^K T(x)` (`D_comp_neg_sq`) and
      `x·T(x) = P_{2K+1}(x+K)` (`X_mul_Tpoly`).
  §2  **(3.1)** for every `μ_X(B/D_tail)`: `muOver n B = (-1)^K τ_X(x⁵B(-x²)D_N(-x²)/T)`
      (`pullback`), by linearity from `eq_3_1_mono` and `eq_3_1_pole` over the partial-fraction
      basis of `Functional.lean`.  PROVED.
  §3  `p`-adic bookkeeping with `padicNorm` (multiplicative, `|0|_p = 0`), which avoids the trap
      `padicValRat p 0 = 0`: `v_p(C(n,k)) ≤ ⌊log_p n⌋` (Mathlib's
      `Nat.factorization_choose_le_log`), `v_p(H^{(5)}_m) ≥ -5⌊log_p m⌋`.
  §4  The pole terms, as in the paper: `c_r = (K!)²A(r)/T'(r)`, `r·T'(r) = ±(K+r)!(K-r)!`
      (`deriv_Tpoly_eval`), hence `v_p(c_r) ≥ -⌊log_p 2K⌋` (`padicNorm_factorial_sq_div_deriv`),
      and the pole terms have `v_p^G ≥ -⌊log_p 2K⌋ - 5⌊log_p K⌋` (`residue_part_bound`).
  §5  The polynomial part.  HERE THE ROUTE DIFFERS FROM THE PAPER'S.  The paper bounds the
      values of the polynomial part `P` on `ℤ_p` by a two-scale estimate
      (`P(ℤ_p) ⊂ p^{-L₀-M₀}ℤ_p`, via (3.8) and `F_r`) and then applies (3.9).  Here instead
      `A = ∑_k a_k C(x+K,k)` with `a_k ∈ ℤ_p` (the binomial basis at `-K`; `padic_binom_coeffs`)
      and each `C(x+K,k)` is treated exactly:
        * `k ≤ 2K`: the quotient by `T` is a constant, and `τ` of a constant is `0`;
        * `k = 2K+1+m`: `C(x+K,k) = T(x)·xΠ_m(x)/k!` with `Π_j(x) = ∏_{i<j}(x-K-1-i)`
          (`binom_shift_large`), and `τ(xΠ_m) = [x⁴]S` for `S(x+1)-S(x) = xΠ_m(x)`, by the
          difference identity (3.3) in the form `τ(ΔS) = S⁗(0)/24 = [x⁴]S`
          (`tau_diff_eq_coeff_four`, `tau_X_mul_Pi`).  The result is
          `(K!)²τ = (K!)²/k!·([x⁴]Π_{m+2}/(m+2) + (K+1+m)/(m+1)·[x⁴]Π_{m+1})`, and
          `(K!)²/k!·[x⁴]Π_j = ±K!(K+j)!/k!·e₄(1/(K+1),…,1/(K+j))` is an integer over `C(k,K)`
          times a coefficient with `v_p ≥ -4⌊log_p(K+j)⌋` (`padicNorm_Pi_coeff_four`).
      Total: `v_p ≥ -6⌊log_p max(2K,d+1)⌋` for the polynomial part (`poly_part_bound`).  The
      `-v_p(24)` of (3.10) is not needed: `τ(ΔS) = [x⁴]S` loses nothing at `2` and `3`.
  §6  **Lemma 3.3**: `lemma_3_3_strong` (bound `-6⌊log_p B⌋` for any `B ≥ max(2K,d+1)`) and
      `lemma_3_3` (the printed (3.10)).
  §7  The entries of (3.11): `entry_pullback` and `entry_bound`, which `CrudeBound.lean` applies.

KNOWN-ANSWER CONTROLS, run before the proof (exact rational arithmetic, `numerics/lemma33/`):
the no-`24` bound on every basis element `C(x+K,k)`, `k ≤ d`, for `K ≤ 8`, three `d` per `K`,
`p ≤ 13` (126 cases, min slack 0, never violated); `τ(ΔS) = [x⁴]S` on 30 random `S`; the
closed forms above for `K ≤ 5`, all `k < 5K`; the pullback (3.1) against the definition of
`muOver` for `(N,K) ∈ {(1,3),(1,4),(2,5)}`; and the target itself at `n = 1` (`K = 40`) on all
703 entries of (3.11), `p ∈ {2,3,5,7,11,13,37,41,43,199,211}`: min slack 0 (at `p = 211 > 5K`).
-/
import Zeta5.LocalFunctional

namespace Zeta5

open Polynomial Finset

noncomputable section

namespace Lemma33

/-! # §1.  The pole set `{0 < |r| ≤ K}` and `T(x) = ∏_{0<|r|≤K}(x - r)` -/

/-- The `2K` integer poles `r ∈ [-K, K]`, `r ≠ 0`, of `g(x) = (K!)²A(x)/∏_{0<|r|≤K}(x-r)`. -/
def poles (K : ℕ) : Finset ℤ := (Finset.Icc (-(K : ℤ)) (K : ℤ)).erase 0

lemma mem_poles {K : ℕ} {q : ℤ} : q ∈ poles K ↔ q ≠ 0 ∧ -(K : ℤ) ≤ q ∧ q ≤ (K : ℤ) := by
  simp [poles, Finset.mem_erase, Finset.mem_Icc]

lemma poles_zero : poles 0 = ∅ := by
  ext q; simp only [mem_poles, Finset.notMem_empty, iff_false]; push_cast; omega

lemma poles_succ (K : ℕ) :
    poles (K + 1) = insert ((K : ℤ) + 1) (insert (-((K : ℤ) + 1)) (poles K)) := by
  ext q; simp only [Finset.mem_insert, mem_poles]; push_cast; omega

lemma Tpoly_poles_zero : Tpoly (poles 0) = 1 := by
  simp [Tpoly, poles_zero]

lemma Tpoly_poles_succ (K : ℕ) :
    Tpoly (poles (K + 1))
      = (X - C ((K : ℚ) + 1)) * ((X + C ((K : ℚ) + 1)) * Tpoly (poles K)) := by
  have h1 : ((K : ℤ) + 1) ∉ insert (-((K : ℤ) + 1)) (poles K) := by
    simp only [Finset.mem_insert, mem_poles]; omega
  have h2 : (-((K : ℤ) + 1)) ∉ poles K := by
    simp only [mem_poles]; omega
  rw [Tpoly, poles_succ, Finset.prod_insert h1, Finset.prod_insert h2]
  push_cast
  rw [map_neg, sub_neg_eq_add]
  rfl

/-- `D_K(-x²) = (-1)^K ∏_{0<|r|≤K}(x - r)` (p. 9: "`D_K(-x²) = (-1)^K ∏(x-r)`"). -/
lemma D_comp_neg_sq (K : ℕ) : (D K).comp (-(X ^ 2)) = C ((-1 : ℚ) ^ K) * Tpoly (poles K) := by
  induction K with
  | zero => simp [Tpoly_poles_zero]
  | succ K ih =>
    have hD : D (K + 1) = D K * (X + C (((K + 1 : ℕ) : ℚ) ^ 2)) := by
      rw [D, D, Finset.prod_Icc_succ_top (by omega)]
    have hc : (C (((K + 1 : ℕ) : ℚ) ^ 2) : ℚ[X]) = C ((K : ℚ) + 1) ^ 2 := by
      push_cast; rw [map_pow]
    rw [hD, Polynomial.mul_comp, ih, Tpoly_poles_succ, Polynomial.add_comp, Polynomial.X_comp,
      Polynomial.C_comp, hc, pow_succ (-1 : ℚ) K, map_mul]
    simp only [map_neg, map_one]
    ring

/-- `x · T(x) = x(x-1)⋯` shifted: `∏_{-K ≤ r ≤ K}(x - r) = P_{2K+1}(x + K)`. -/
lemma X_mul_Tpoly (K : ℕ) :
    X * Tpoly (poles K) = (descPochhammer ℚ (2 * K + 1)).comp (X + C (K : ℚ)) := by
  induction K with
  | zero => simp [Tpoly_poles_zero]
  | succ K ih =>
    have e1 : descPochhammer ℚ (2 * (K + 1) + 1)
        = X * (descPochhammer ℚ (2 * K + 1)).comp (X - 1)
          * (X - (((2 * K + 1 + 1 : ℕ)) : ℚ[X])) := by
      rw [show 2 * (K + 1) + 1 = (2 * K + 1) + 1 + 1 by ring, descPochhammer_succ_right,
        descPochhammer_succ_left]
    have hsh : ((X - 1 : ℚ[X]).comp (X + C (((K + 1 : ℕ) : ℚ)))) = X + C (K : ℚ) := by
      rw [Polynomial.sub_comp, Polynomial.X_comp, Polynomial.one_comp]
      push_cast
      rw [map_add, map_one]
      ring
    rw [e1, Polynomial.mul_comp, Polynomial.mul_comp, Polynomial.X_comp, Polynomial.comp_assoc,
      hsh, ← ih, Tpoly_poles_succ, Polynomial.sub_comp, Polynomial.X_comp,
      Polynomial.natCast_comp]
    push_cast
    simp only [map_add, map_one, map_natCast]
    ring

lemma Tpoly_poles_monic (K : ℕ) : (Tpoly (poles K)).Monic := Tpoly_monic _

lemma Tpoly_poles_natDegree (K : ℕ) : (Tpoly (poles K)).natDegree = 2 * K := by
  induction K with
  | zero => simp [Tpoly_poles_zero]
  | succ K ih =>
    rw [Tpoly_poles_succ, (monic_X_sub_C _).natDegree_mul
      ((monic_X_add_C _).mul (Tpoly_poles_monic K)),
      (monic_X_add_C _).natDegree_mul (Tpoly_poles_monic K), ih, natDegree_X_sub_C,
      natDegree_X_add_C]
    ring

/-! # §2.  The pullback identity (3.1) for the rational functions of (3.11)

`μ_X(R) = τ_X(x⁵R(-x²))` (3.1).  For `R = B/D_tail` the pullback is
`x⁵B(-x²)/D_tail(-x²) = (-1)^K x⁵B(-x²)D_N(-x²)/T(x)`, because
`D_tail(-x²)D_N(-x²) = D_K(-x²) = (-1)^K T(x)` (`D_comp_neg_sq`).  Both sides are `ℚ`-linear
in `B`; by the partial-fraction basis of `Functional.lean` it suffices to check them on
`B = P·D_tail` (the monomials, `eq_3_1_mono`) and on the cofactors `B = D_tail/(t+r²)` (the
poles, `eq_3_1_pole`). -/

/-- The pullback numerator of `B/D_tail` over the denominator `T(x) = ∏_{0<|r|≤K}(x-r)`,
up to the sign `(-1)^K`: `x⁵B(-x²)D_N(-x²)`. -/
def pb (n : ℕ) (B : ℚ[X]) : ℚ[X] := X ^ 5 * B.comp (-(X ^ 2)) * (D (N n)).comp (-(X ^ 2))

lemma pb_add (n : ℕ) (A B : ℚ[X]) : pb n (A + B) = pb n A + pb n B := by
  simp only [pb, Polynomial.add_comp]; ring

lemma pb_C_mul (n : ℕ) (a : ℚ) (B : ℚ[X]) : pb n (C a * B) = C a * pb n B := by
  simp only [pb, Polynomial.mul_comp, Polynomial.C_comp]; ring

lemma pb_zero (n : ℕ) : pb n 0 = 0 := by simp [pb]

lemma pb_sum {ι : Type*} (n : ℕ) (t : Finset ι) (f : ι → ℚ[X]) :
    pb n (∑ i ∈ t, f i) = ∑ i ∈ t, pb n (f i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [pb_zero]
  | insert a t ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, pb_add, ih]

lemma tauExtOf_zero (Y : ℚ[X]) (s : Finset ℤ) : tauExtOf Y s 0 = 0 := by
  have h := tauExtOf_C_mul Y s 0 0
  simpa using h

lemma tauExtOf_sum {ι : Type*} (Y : ℚ[X]) (s : Finset ℤ) (t : Finset ι) (f : ι → ℚ[X]) :
    tauExtOf Y s (∑ i ∈ t, f i) = ∑ i ∈ t, tauExtOf Y s (f i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [tauExtOf_zero]
  | insert a t ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, tauExtOf_add, ih]

lemma muOver_zero' (n : ℕ) : muOver n 0 = 0 := by
  have h := Functional.muOver_C_mul n 0 0
  simpa using h

lemma muOver_sum' {ι : Type*} (n : ℕ) (t : Finset ι) (f : ι → ℚ[X]) :
    muOver n (∑ i ∈ t, f i) = ∑ i ∈ t, muOver n (f i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [muOver_zero']
  | insert a t ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Functional.muOver_add, ih]

/-- (3.1) on the polynomial part: `τ(x⁵P(-x²)) = μ(P)`, from the monomial case
`eq_3_1_mono` by linearity. -/
lemma tau_pull_eq_muPoly (P : ℚ[X]) : tau (X ^ 5 * P.comp (-(X ^ 2))) = muPoly P := by
  conv_lhs => rw [P.as_sum_support_C_mul_X_pow]
  rw [Polynomial.sum_comp, Finset.mul_sum, tau_sum, muPoly]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_pow_comp,
    show (X : ℚ[X]) ^ 5 * (C (P.coeff e) * (-(X ^ 2)) ^ e)
      = C (P.coeff e) * (X ^ 5 * (-(X ^ 2)) ^ e) by ring,
    tau_C_mul, ← eq_3_1_mono]

/-- If `T ∣ U` then `τ_X(U/T)` is `τ` of the quotient: all residues vanish. -/
lemma tauExtOf_mul_Tpoly (Y : ℚ[X]) (s : Finset ℤ) (U : ℚ[X]) :
    tauExtOf Y s (U * Tpoly s) = C (tau U) := by
  have hdiv : (U * Tpoly s) /ₘ Tpoly s = U := by
    rw [mul_comm]; exact Polynomial.mul_divByMonic_cancel_left U (Tpoly_monic s)
  have hmod : (U * Tpoly s) %ₘ Tpoly s = 0 := by
    rw [mul_comm]
    exact (Polynomial.modByMonic_eq_zero_iff_dvd (Tpoly_monic s)).2 ⟨U, rfl⟩
  simp [tauExtOf, tauExt, hdiv, resid, hmod]

/-- `D_tail(-x²)·D_N(-x²) = (-1)^K T(x)`. -/
lemma Dtail_comp_mul (n : ℕ) :
    (Dtail n).comp (-(X ^ 2)) * (D (N n)).comp (-(X ^ 2))
      = C ((-1 : ℚ) ^ K n) * Tpoly (poles (K n)) := by
  rw [← D_comp_neg_sq, ← D_mul_Dtail n, Polynomial.mul_comp, mul_comm]

/-- (3.1) on `B = P·D_tail`. -/
lemma pullback_poly (n : ℕ) (P : ℚ[X]) :
    C ((-1 : ℚ) ^ K n) * tauExtOf X (poles (K n)) (pb n (P * Dtail n)) = muOver n (P * Dtail n) := by
  have hpb : pb n (P * Dtail n)
      = (C ((-1 : ℚ) ^ K n) * (X ^ 5 * P.comp (-(X ^ 2)))) * Tpoly (poles (K n)) := by
    rw [pb, Polynomial.mul_comp]
    linear_combination (X ^ 5 * P.comp (-(X ^ 2))) * Dtail_comp_mul n
  rw [hpb, tauExtOf_mul_Tpoly, tau_C_mul, tau_pull_eq_muPoly, Functional.muOver_poly, ← map_mul,
    ← mul_assoc, ← mul_pow]
  norm_num

/-- (3.1) on the cofactor `B = D_tail/(t + r²)`, i.e. at the simple pole `t = -r²`. -/
lemma pullback_cof (n : ℕ) {r : ℕ} (hr : r ∈ Ioc (N n) (K n)) :
    C ((-1 : ℚ) ^ K n) * tauExtOf X (poles (K n)) (pb n (Functional.cof n r))
      = muOver n (Functional.cof n r) := by
  rw [Functional.muOver_cof n hr]
  obtain ⟨hr1, hr2⟩ := Finset.mem_Ioc.1 hr
  have hr0 : 1 ≤ r := by omega
  have hrQ : (r : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  set s := poles (K n) with hs
  have hRs : (r : ℤ) ∈ s := mem_poles.2 ⟨by omega, by omega, by omega⟩
  have hnRs : -(r : ℤ) ∈ s.erase (r : ℤ) :=
    Finset.mem_erase.2 ⟨by omega, mem_poles.2 ⟨by omega, by omega, by omega⟩⟩
  set Tr := Tpoly ((s.erase (r : ℤ)).erase (-(r : ℤ))) with hTr
  have hT : Tpoly s = (X - C (r : ℚ)) * ((X + C (r : ℚ)) * Tr) := by
    rw [Tpoly, ← Finset.mul_prod_erase s _ hRs, ← Finset.mul_prod_erase (s.erase (r : ℤ)) _ hnRs]
    push_cast
    rw [map_neg, sub_neg_eq_add]
    rfl
  -- `Tr` does not vanish at `±r`
  have hTr_ne : ∀ x : ℤ, (x = r ∨ x = -(r : ℤ)) → Tr.eval (x : ℚ) ≠ 0 := by
    intro x hx
    rw [hTr, Tpoly, Polynomial.eval_prod]
    refine Finset.prod_ne_zero_iff.2 fun q hq => ?_
    have hq1 := Finset.ne_of_mem_erase hq
    have hq2 := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hq)
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    intro h0
    have : (x : ℚ) = (q : ℚ) := by linarith
    have hxq : x = q := by exact_mod_cast this
    rcases hx with rfl | rfl <;> omega
  have hTr_r : Tr.eval (r : ℚ) ≠ 0 := by
    have := hTr_ne (r : ℤ) (Or.inl rfl); simpa using this
  have hTr_nr : Tr.eval (-(r : ℚ)) ≠ 0 := by
    have := hTr_ne (-(r : ℤ)) (Or.inr rfl); push_cast at this; exact this
  -- the pullback numerator is `-(-1)^K x⁵ Tr`
  have hU : pb n (Functional.cof n r) = C (-(-1 : ℚ) ^ K n) * (X ^ 5 * Tr) := by
    have hcof := Functional.cof_mul n hr
    have h1 : (X + C ((r : ℚ) ^ 2)).comp (-(X ^ 2)) * pb n (Functional.cof n r)
        = X ^ 5 * (C ((-1 : ℚ) ^ K n) * Tpoly s) := by
      rw [← Dtail_comp_mul, ← hcof, pb, Polynomial.mul_comp]; ring
    have h2 : (X + C ((r : ℚ) ^ 2)).comp (-(X ^ 2)) = -((X - C (r : ℚ)) * (X + C (r : ℚ))) := by
      rw [Polynomial.add_comp, Polynomial.X_comp, Polynomial.C_comp, map_pow]; ring
    rw [h2, hT] at h1
    have hne : (X - C (r : ℚ)) * (X + C (r : ℚ)) ≠ 0 :=
      mul_ne_zero (X_sub_C_ne_zero _) (X_add_C_ne_zero _)
    refine mul_left_cancel₀ hne ?_
    rw [map_neg]
    linear_combination -h1
  -- polynomial division by `T`
  set W : ℚ[X] := C ((-1 : ℚ) ^ K n) * (-(X ^ 3) - C ((r : ℚ) ^ 2) * X) with hW
  set Rm : ℚ[X] := C ((-1 : ℚ) ^ K n * (-((r : ℚ) ^ 4))) * (X * Tr) with hRm
  have hTrm : Tr.Monic := Tpoly_monic _
  have hdegT : (Tpoly s).natDegree = Tr.natDegree + 2 := by
    rw [hT, (monic_X_sub_C _).natDegree_mul ((monic_X_add_C _).mul hTrm),
      (monic_X_add_C _).natDegree_mul hTrm, natDegree_X_sub_C, natDegree_X_add_C]
    ring
  have hdegR : Rm.natDegree ≤ Tr.natDegree + 1 := by
    refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
    refine le_trans Polynomial.natDegree_mul_le ?_
    have := Polynomial.natDegree_X_le (R := ℚ)
    omega
  have hdm := Polynomial.div_modByMonic_unique (f := pb n (Functional.cof n r)) W Rm
    (Tpoly_monic s) ⟨by
      rw [hU, hT, hW, hRm]
      simp only [map_mul, map_neg, map_pow]
      ring,
      Polynomial.degree_lt_degree (by omega)⟩
  -- the derivative of `T` at `±r`
  have hTd : derivative (Tpoly s)
      = (X + C (r : ℚ)) * Tr + (X - C (r : ℚ)) * (Tr + (X + C (r : ℚ)) * derivative Tr) := by
    rw [hT, derivative_mul, derivative_mul]
    simp only [derivative_sub, derivative_add, derivative_X, derivative_C]
    ring
  have hTd_r : (derivative (Tpoly s)).eval (r : ℚ) = 2 * (r : ℚ) * Tr.eval (r : ℚ) := by
    rw [hTd]; simp only [eval_add, eval_mul, eval_sub, eval_X, eval_C]; ring
  have hTd_nr : (derivative (Tpoly s)).eval (-(r : ℚ)) = -2 * (r : ℚ) * Tr.eval (-(r : ℚ)) := by
    rw [hTd]; simp only [eval_add, eval_mul, eval_sub, eval_X, eval_C]; ring
  -- the residues
  have hres_r : resid s (pb n (Functional.cof n r)) (r : ℤ)
      = (-1 : ℚ) ^ K n * (-((r : ℚ) ^ 4) / 2) := by
    rw [resid, hdm.2]
    push_cast
    rw [hTd_r, hRm]
    simp only [eval_mul, eval_C, eval_X]
    field_simp
  have hres_nr : resid s (pb n (Functional.cof n r)) (-(r : ℤ))
      = (-1 : ℚ) ^ K n * (-((r : ℚ) ^ 4) / 2) := by
    rw [resid, hdm.2]
    push_cast
    rw [hTd_nr, hRm]
    simp only [eval_mul, eval_C, eval_X]
    field_simp
  have hres_other : ∀ q ∈ s, q ∉ ({(r : ℤ), -(r : ℤ)} : Finset ℤ) →
      resid s (pb n (Functional.cof n r)) q = 0 := by
    intro q hq hq'
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hq'
    have hmem : q ∈ (s.erase (r : ℤ)).erase (-(r : ℤ)) :=
      Finset.mem_erase.2 ⟨hq'.2, Finset.mem_erase.2 ⟨hq'.1, hq⟩⟩
    rw [resid, hdm.2, hRm]
    simp only [eval_mul, eval_C, eval_X, hTr, Tpoly_eval_root hmem, mul_zero, zero_div]
  have hsub : ({(r : ℤ), -(r : ℤ)} : Finset ℤ) ⊆ s := by
    intro q hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl
    · exact hRs
    · exact Finset.mem_of_mem_erase hnRs
  have hne : (r : ℤ) ≠ -(r : ℤ) := by omega
  -- assemble
  rw [eq_3_1_pole r hr0, tauExtOf, tauExt, tauExt, hdm.1,
    ← Finset.sum_subset hsub (fun q hq hq' => by rw [hres_other q hq hq', map_zero, zero_mul]),
    Finset.sum_pair hne, Finset.sum_pair hne, hres_r, hres_nr, hW, tau_C_mul]
  have hsq : (C ((-1 : ℚ) ^ K n) : ℚ[X]) * C ((-1 : ℚ) ^ K n) = 1 := by
    rw [← map_mul, ← mul_pow]; norm_num
  simp only [map_mul]
  linear_combination (C (tau (-(X ^ 3) - C ((r : ℚ) ^ 2) * X))
    + C (-((r : ℚ) ^ 4) / 2) * (C (H5 (dIdx (r : ℤ))) - X)
    + C (-((r : ℚ) ^ 4) / 2) * (C (H5 (dIdx (-(r : ℤ)))) - X)) * hsq

/-- **(3.1)** for every `μ_X(B/D_tail)`: `μ_X(B/D_tail) = τ_X(x⁵B(-x²)/D_tail(-x²))`, with
`x⁵B(-x²)/D_tail(-x²) = (-1)^K pb(B)/T`. -/
theorem pullback (n : ℕ) (B : ℚ[X]) :
    muOver n B = C ((-1 : ℚ) ^ K n) * tauExtOf X (poles (K n)) (pb n B) := by
  conv_rhs => rw [Functional.partial_fractions n B]
  conv_lhs => rw [Functional.partial_fractions n B]
  rw [Functional.muOver_add, muOver_sum', pb_add, pb_sum, tauExtOf_add, tauExtOf_sum, mul_add,
    Finset.mul_sum, pullback_poly]
  congr 1
  refine Finset.sum_congr rfl fun r hr => ?_
  rw [pb_C_mul, tauExtOf_C_mul, Functional.muOver_C_mul, ← pullback_cof n hr]
  ring

/-! # §3.  `p`-adic bookkeeping

All bounds are stated with `padicNorm`, which is multiplicative and non-archimedean and has
`|0|_p = 0`; this sidesteps the trap that `padicValRat p 0 = 0` (not `+∞`).  A bound
`|x|_p ≤ p^e` says `v_p(x) ≥ -e`. -/

section Bounds

variable {p : ℕ} [hp : Fact p.Prime]

omit hp in
lemma one_le_p_rat (hp' : p.Prime) : (1 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp'.one_lt.le

lemma p_pow_mono {a b : ℕ} (hab : a ≤ b) : (p : ℚ) ^ a ≤ (p : ℚ) ^ b :=
  pow_le_pow_right₀ (one_le_p_rat hp.out) hab

omit hp in
lemma padicNorm_natCast_eq {n : ℕ} (hn : n ≠ 0) :
    padicNorm p (n : ℚ) = (p : ℚ) ^ (-(padicValNat p n : ℤ)) := by
  rw [padicNorm.eq_zpow_of_nonzero (Nat.cast_ne_zero.2 hn), padicValRat.of_nat]

/-- `v_p(n) ≤ e` gives `|1/n|_p ≤ p^e`. -/
lemma padicNorm_one_div_le {n e : ℕ} (hn : n ≠ 0) (h : padicValNat p n ≤ e) :
    padicNorm p (1 / (n : ℚ)) ≤ (p : ℚ) ^ e := by
  rw [padicNorm.div, padicNorm.one, padicNorm_natCast_eq hn, one_div, ← zpow_neg, neg_neg,
    zpow_natCast]
  exact p_pow_mono h

/-- `|1/n|_p ≤ p^{⌊log_p n⌋}`. -/
lemma padicNorm_one_div_le_log {n : ℕ} (hn : n ≠ 0) :
    padicNorm p (1 / (n : ℚ)) ≤ (p : ℚ) ^ (Nat.log p n) :=
  padicNorm_one_div_le hn (padicValNat_le_nat_log n)

/-- `|t / C(n,k)|_p ≤ p^{⌊log_p n⌋}` for an integer `t` and `k ≤ n`: a binomial coefficient
has `v_p(C(n,k)) ≤ ⌊log_p n⌋` (Kummer; `Nat.factorization_choose_le_log`). -/
lemma padicNorm_div_choose_le {x : ℚ} (hx : padicNorm p x ≤ 1) {n k : ℕ} (hk : k ≤ n) :
    padicNorm p (x / (n.choose k : ℚ)) ≤ (p : ℚ) ^ (Nat.log p n) := by
  have hc : n.choose k ≠ 0 := (Nat.choose_pos hk).ne'
  have hv : padicValNat p (n.choose k) ≤ Nat.log p n := by
    rw [← Nat.factorization_def _ hp.out]; exact Nat.factorization_choose_le_log
  rw [div_eq_mul_one_div, padicNorm.mul]
  calc padicNorm p x * padicNorm p (1 / (n.choose k : ℚ))
      ≤ 1 * (p : ℚ) ^ (Nat.log p n) :=
        mul_le_mul hx (padicNorm_one_div_le hc hv) (padicNorm.nonneg _)
          zero_le_one
    _ = _ := one_mul _

/-- `|H^{(5)}_m|_p ≤ p^{5⌊log_p m⌋}`, i.e. `v_p(H^{(5)}_m) ≥ -5⌊log_p m⌋` (p. 9). -/
lemma padicNorm_H5_le (m : ℕ) : padicNorm p (H5 m) ≤ (p : ℚ) ^ (5 * Nat.log p m) := by
  rw [H5]
  refine padicNorm.sum_le' (fun v hv => ?_) (by positivity)
  obtain ⟨hv1, hvm⟩ := Finset.mem_Icc.1 hv
  have hv0 : v ≠ 0 := by omega
  rw [show (1 : ℚ) / (v : ℚ) ^ 5 = (1 / (v : ℚ)) ^ 5 by ring, padicNorm_pow]
  calc padicNorm p (1 / (v : ℚ)) ^ 5 ≤ ((p : ℚ) ^ (Nat.log p v)) ^ 5 :=
        pow_le_pow_left₀ (padicNorm.nonneg _) (padicNorm_one_div_le_log hv0) 5
    _ = (p : ℚ) ^ (5 * Nat.log p v) := by rw [← pow_mul, mul_comm]
    _ ≤ _ := p_pow_mono (Nat.mul_le_mul_left 5 (Nat.log_mono_right hvm))

/-- A constant with `|x|_p ≤ p^e` has `v_p^G ≥ -e`. -/
lemma vGAtLeast_C_of_padicNorm_le {x : ℚ} {e : ℕ} (h : padicNorm p x ≤ (p : ℚ) ^ e) :
    vGAtLeast p (C x) (-(e : ℤ)) := by
  rw [vGAtLeast_iff_padicNorm]
  intro i
  rw [neg_neg, zpow_natCast, Polynomial.coeff_C]
  split_ifs
  · exact h
  · rw [padicNorm.zero]; positivity

lemma vGAtLeast_X : vGAtLeast p (X : ℚ[X]) 0 := by
  rw [vGAtLeast_iff_padicNorm]
  intro i
  rw [Polynomial.coeff_X]
  split_ifs <;> simp

end Bounds

/-! # §4.  The residues: `v_p(c_r) ≥ -⌊log_p 2K⌋` and the pole terms

`c_r = (K!)²A(r)/T'(r)`, and `r·T'(r) = ∏_{-K≤q≤K, q≠r}(r-q) = ±(K+r)!(K-r)!`, so
`(K!)²/T'(r) = ±r·C(2K,K+r)/C(2K,K)` — the paper's `c_r = ±(K!)²rA(r)/((K+r)!(K-r)!)`. -/

/-- `∏_{0≤i≤M, i≠a}(a - i) = (-1)^{M-a} a! (M-a)!`. -/
lemma prod_range_erase_sub (a M : ℕ) (h : a ≤ M) :
    ∏ i ∈ (range (M + 1)).erase a, ((a : ℚ) - i)
      = (-1) ^ (M - a) * (a.factorial : ℚ) * ((M - a).factorial : ℚ) := by
  induction M, h using Nat.le_induction with
  | base =>
    have hset : (range (a + 1)).erase a = range a := by
      ext i; simp only [Finset.mem_erase, Finset.mem_range]; omega
    rw [hset, Nat.sub_self, pow_zero, Nat.factorial_zero, Nat.cast_one, one_mul, mul_one]
    clear hset
    induction a with
    | zero => simp
    | succ a ih =>
      rw [Finset.prod_range_succ', Nat.factorial_succ]
      have : ∀ i ∈ range a, (((a + 1 : ℕ) : ℚ) - ((i + 1 : ℕ) : ℚ)) = (a : ℚ) - i := by
        intro i _; push_cast; ring
      rw [Finset.prod_congr rfl this, ih]
      push_cast; ring
  | succ M hM ih =>
    have hset : (range (M + 1 + 1)).erase a = insert (M + 1) ((range (M + 1)).erase a) := by
      ext i; simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_insert]; omega
    have hnot : M + 1 ∉ (range (M + 1)).erase a := by simp
    rw [hset, Finset.prod_insert hnot, ih, show M + 1 - a = (M - a) + 1 by omega,
      Nat.factorial_succ]
    have hc : ((M - a : ℕ) : ℚ) = (M : ℚ) - a := by rw [Nat.cast_sub hM]
    push_cast
    rw [hc]
    ring

/-- `r·T'(r) = (-1)^{2K-a} a!(2K-a)!` with `a = r + K`. -/
lemma deriv_Tpoly_eval (K : ℕ) {r : ℤ} (hr : r ∈ poles K) :
    (r : ℚ) * (derivative (Tpoly (poles K))).eval (r : ℚ)
      = (-1) ^ (2 * K - (r + K).toNat) * (((r + K).toNat).factorial : ℚ)
          * ((2 * K - (r + K).toNat).factorial : ℚ) := by
  rw [Tpoly_derivative_eval hr]
  obtain ⟨hr0, hr1, hr2⟩ := mem_poles.1 hr
  have h0mem : (0 : ℤ) ∈ (Finset.Icc (-(K : ℤ)) K).erase r :=
    Finset.mem_erase.2 ⟨fun h => hr0 h.symm, Finset.mem_Icc.2 ⟨by omega, by omega⟩⟩
  have hset : ((Finset.Icc (-(K : ℤ)) K).erase r).erase 0 = (poles K).erase r := by
    rw [poles, Finset.erase_right_comm]
  have h1 : ∏ q ∈ (Finset.Icc (-(K : ℤ)) K).erase r, ((r : ℚ) - q)
      = (r : ℚ) * ∏ q ∈ (poles K).erase r, ((r : ℚ) - q) := by
    rw [← Finset.mul_prod_erase _ _ h0mem, hset]; simp
  rw [← h1]
  set a := (r + K).toNat with ha_def
  have ha : (a : ℤ) = r + K := Int.toNat_of_nonneg (by omega)
  have h2 : ∏ q ∈ (Finset.Icc (-(K : ℤ)) K).erase r, ((r : ℚ) - q)
      = ∏ i ∈ (range (2 * K + 1)).erase a, ((a : ℚ) - i) := by
    refine Finset.prod_nbij' (fun q => (q + K).toNat) (fun i => (i : ℤ) - K) ?_ ?_ ?_ ?_ ?_
    · intro q hq
      simp only [Finset.mem_erase, Finset.mem_Icc, Finset.mem_range] at hq ⊢
      omega
    · intro i hi
      simp only [Finset.mem_erase, Finset.mem_Icc, Finset.mem_range] at hi ⊢
      omega
    · intro q hq
      simp only [Finset.mem_erase, Finset.mem_Icc] at hq
      omega
    · intro i hi
      simp only [Finset.mem_erase, Finset.mem_range] at hi
      omega
    · intro q hq
      simp only [Finset.mem_erase, Finset.mem_Icc] at hq
      have hq' : (((q + K).toNat : ℕ) : ℤ) = q + K := Int.toNat_of_nonneg (by omega)
      have e1 : ((a : ℕ) : ℚ) = (((a : ℕ) : ℤ) : ℚ) := by norm_cast
      have e2 : (((q + K).toNat : ℕ) : ℚ) = ((((q + K).toNat : ℕ) : ℤ) : ℚ) := by norm_cast
      rw [e1, e2, ha, hq']
      push_cast; ring
  rw [h2, prod_range_erase_sub a (2 * K) (by omega)]

section Residues

variable {p : ℕ} [hp : Fact p.Prime]

/-- **The residue bound** (p. 8): `|(K!)²/T'(r)|_p ≤ p^{⌊log_p 2K⌋}`, i.e.
`v_p(c_r) ≥ -L₀` once `A(r) ∈ ℤ`. -/
lemma padicNorm_factorial_sq_div_deriv (K : ℕ) {r : ℤ} (hr : r ∈ poles K) :
    padicNorm p (((K.factorial : ℚ)) ^ 2 / (derivative (Tpoly (poles K))).eval (r : ℚ))
      ≤ (p : ℚ) ^ (Nat.log p (2 * K)) := by
  obtain ⟨hr0, hr1, hr2⟩ := mem_poles.1 hr
  have hd := deriv_Tpoly_eval K hr
  set a := (r + K).toNat with ha_def
  have ha2K : a ≤ 2 * K := by omega
  set c : ℚ := (-1) ^ (2 * K - a) with hc_def
  have hc2 : c * c = 1 := by rw [hc_def, ← mul_pow]; norm_num
  have hrQ : (r : ℚ) ≠ 0 := Int.cast_ne_zero.2 hr0
  set T' := (derivative (Tpoly (poles K))).eval (r : ℚ) with hT'
  have hfa : (a.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  have hfb : ((2 * K - a).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  have hT'ne : T' ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hd
    have : c * (a.factorial : ℚ) * ((2 * K - a).factorial : ℚ) ≠ 0 := by
      refine mul_ne_zero (mul_ne_zero ?_ hfa) hfb
      rw [hc_def]; exact pow_ne_zero _ (by norm_num)
    exact this hd.symm
  have hchoose1 := Nat.cast_choose ℚ ha2K
  have hchoose2 := Nat.cast_choose ℚ (show K ≤ 2 * K by omega)
  rw [show 2 * K - K = K by omega] at hchoose2
  have hf2K : (((2 * K).factorial : ℚ)) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  have hfK : ((K.factorial : ℚ)) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  set Q : ℚ := ((K.factorial : ℚ)) ^ 2 / ((a.factorial : ℚ) * ((2 * K - a).factorial : ℚ))
    with hQ
  have hkey1 : ((K.factorial : ℚ)) ^ 2 / T' = (r : ℚ) * c * Q := by
    rw [div_eq_iff hT'ne]
    calc ((K.factorial : ℚ)) ^ 2
        = (c * c) * (Q * ((a.factorial : ℚ) * ((2 * K - a).factorial : ℚ))) := by
          rw [hc2, hQ, div_mul_cancel₀ _ (mul_ne_zero hfa hfb), one_mul]
      _ = (r : ℚ) * c * Q * T' := by linear_combination (-(c * Q)) * hd
  have hkey2 : Q = (((2 * K).choose a : ℕ) : ℚ) / (((2 * K).choose K : ℕ) : ℚ) := by
    rw [hQ, hchoose1, hchoose2]
    field_simp
  have hkey : ((K.factorial : ℚ)) ^ 2 / T'
      = (r : ℚ) * c * ((((2 * K).choose a : ℕ) : ℚ) / (((2 * K).choose K : ℕ) : ℚ)) := by
    rw [hkey1, hkey2]
  rw [hkey, padicNorm.mul, padicNorm.mul]
  have hr1' : padicNorm p (r : ℚ) ≤ 1 := padicNorm.of_int r
  have hc1 : padicNorm p c = 1 := by
    rw [hc_def, padicNorm_pow, padicNorm.neg, padicNorm.one, one_pow]
  rw [hc1, mul_one]
  calc padicNorm p (r : ℚ) * padicNorm p ((((2 * K).choose a : ℕ) : ℚ) / ((2 * K).choose K : ℚ))
      ≤ 1 * (p : ℚ) ^ (Nat.log p (2 * K)) :=
        mul_le_mul hr1' (padicNorm_div_choose_le (padicNorm.of_nat _) (by omega))
          (padicNorm.nonneg _) zero_le_one
    _ = _ := one_mul _

lemma dIdx_le_of_mem_poles {K : ℕ} {r : ℤ} (hr : r ∈ poles K) : dIdx r ≤ K := by
  obtain ⟨hr0, hr1, hr2⟩ := mem_poles.1 hr
  unfold dIdx
  split_ifs <;> omega

/-- **The pole terms** (p. 9): for `U` with `p`-integral values at the poles,
`v_p^G((K!)² ∑_r c_r(H^{(5)}_{d(r)} - X)) ≥ -⌊log_p 2K⌋ - 5⌊log_p K⌋`. -/
theorem residue_part_bound (K : ℕ) (U : ℚ[X])
    (hU : ∀ r ∈ poles K, padicNorm p (U.eval (r : ℚ)) ≤ 1) :
    vGAtLeast p (C (((K.factorial : ℚ)) ^ 2)
        * ∑ r ∈ poles K, C (resid (poles K) U r) * (C (H5 (dIdx r)) - X))
      (-((Nat.log p (2 * K) + 5 * Nat.log p K : ℕ) : ℤ)) := by
  rw [Finset.mul_sum]
  refine vGAtLeast_sum fun r hr => ?_
  rw [← mul_assoc, ← map_mul]
  have h1 : vGAtLeast p (C (((K.factorial : ℚ)) ^ 2 * resid (poles K) U r))
      (-(Nat.log p (2 * K) : ℤ)) := by
    refine vGAtLeast_C_of_padicNorm_le ?_
    rw [resid_eq_eval U hr, mul_div_left_comm, padicNorm.mul]
    calc padicNorm p (U.eval (r : ℚ))
          * padicNorm p (((K.factorial : ℚ)) ^ 2 / (derivative (Tpoly (poles K))).eval (r : ℚ))
        ≤ 1 * (p : ℚ) ^ (Nat.log p (2 * K)) :=
          mul_le_mul (hU r hr) (padicNorm_factorial_sq_div_deriv K hr)
            (padicNorm.nonneg _) zero_le_one
      _ = _ := one_mul _
  have h2 : vGAtLeast p (C (H5 (dIdx r)) - X) (-(5 * Nat.log p K : ℕ) : ℤ) := by
    refine vGAtLeast_sub (vGAtLeast_C_of_padicNorm_le ?_) (vGAtLeast.mono vGAtLeast_X (by omega))
    exact le_trans (padicNorm_H5_le _)
      (p_pow_mono (Nat.mul_le_mul_left 5 (Nat.log_mono_right (dIdx_le_of_mem_poles hr))))
  refine vGAtLeast.mono (vGAtLeast_mul h1 h2) ?_
  push_cast
  omega

end Residues

/-! # §5.  The polynomial part: `τ(P)` through the binomial basis at `-K`

Write `A(x) = ∑_k a_k C(x+K, k)` with `a_k ∈ ℤ`.  For `k ≤ 2K` the quotient of `C(x+K,k)` by
`T` is a constant, so `τ` kills it.  For `k = 2K+1+m`, `C(x+K,k) = T(x)·x·Π_m(x)/k!` with
`Π_j(x) = ∏_{i<j}(x-K-1-i)`, and `τ(xΠ_m) = [x⁴]S` where `S(x+1) - S(x) = xΠ_m(x)` — this is
the difference identity (3.3), `τ(ΔS) = S⁗(0)/24 = [x⁴]S`.  Then

    (K!)² τ(C(x+K,k)/T) = (K!)²/k! · ( [x⁴]Π_{m+2}/(m+2) + (K+1+m)/(m+1) · [x⁴]Π_{m+1} ),

and `(K!)²/k! · [x⁴]Π_j = ±K!(K+j)!/k! · e₄(1/(K+1), …, 1/(K+j))` has
`v_p ≥ -⌊log_p k⌋ - 4⌊log_p(K+j)⌋`: the factorial ratio is an integer over `C(k, K)`. -/

/-- `Π_j(x) = P_j(x - a) = (x-a)(x-a-1)⋯(x-a-j+1)`. -/
def Pi (a j : ℕ) : ℚ[X] := (descPochhammer ℚ j).comp (X - C (a : ℚ))

/-- `τ(S(x+1) - S(x)) = [x⁴]S`: the difference identity (3.3) read off at the coefficient. -/
lemma tau_diff_eq_coeff_four (S : ℚ[X]) : tau (S.comp (X + 1) - S) = S.coeff 4 := by
  rw [eq_3_3, ← Polynomial.coeff_zero_eq_eval_zero]
  simp only [Polynomial.coeff_derivative]
  norm_num
  ring

lemma descPoch_diff (j : ℕ) :
    (descPochhammer ℚ (j + 1)).comp (X + 1) - descPochhammer ℚ (j + 1)
      = C ((j : ℚ) + 1) * descPochhammer ℚ j := by
  have h1 : (descPochhammer ℚ (j + 1)).comp (X + 1) = (X + 1) * descPochhammer ℚ j := by
    rw [descPochhammer_succ_left, Polynomial.mul_comp, Polynomial.X_comp, Polynomial.comp_assoc]
    rw [show ((X - 1 : ℚ[X]).comp (X + 1)) = X by
      rw [Polynomial.sub_comp, Polynomial.X_comp, Polynomial.one_comp]; ring, Polynomial.comp_X]
  rw [h1, descPochhammer_succ_right]
  rw [map_add, map_one, map_natCast]
  ring

lemma Pi_diff (a j : ℕ) :
    (Pi a (j + 1)).comp (X + 1) - Pi a (j + 1) = C ((j : ℚ) + 1) * Pi a j := by
  have hsh : ((X - C (a : ℚ)).comp (X + 1)) = (X + 1).comp (X - C (a : ℚ)) := by
    simp only [Polynomial.sub_comp, Polynomial.add_comp, Polynomial.X_comp, Polynomial.C_comp,
      Polynomial.one_comp]
    ring
  simp only [Pi]
  rw [Polynomial.comp_assoc, hsh, ← Polynomial.comp_assoc, ← Polynomial.sub_comp,
    descPoch_diff, Polynomial.mul_comp, Polynomial.C_comp]

lemma X_mul_Pi (a m : ℕ) : X * Pi a m = Pi a (m + 1) + C ((a : ℚ) + m) * Pi a m := by
  simp only [Pi]
  rw [descPochhammer_succ_right, Polynomial.mul_comp, Polynomial.sub_comp,
    Polynomial.X_comp, Polynomial.natCast_comp]
  simp only [map_add, map_natCast]
  ring

/-- `τ(xΠ_m) = [x⁴]Π_{m+2}/(m+2) + (a+m)/(m+1)·[x⁴]Π_{m+1}`. -/
lemma tau_X_mul_Pi (a m : ℕ) :
    tau (X * Pi a m) = (Pi a (m + 2)).coeff 4 / ((m : ℚ) + 2)
      + ((a : ℚ) + m) / ((m : ℚ) + 1) * (Pi a (m + 1)).coeff 4 := by
  set S : ℚ[X] := C (1 / ((m : ℚ) + 2)) * Pi a (m + 2)
    + C (((a : ℚ) + m) / ((m : ℚ) + 1)) * Pi a (m + 1) with hS
  have hm2 : ((m : ℚ) + 2) ≠ 0 := by positivity
  have hm1 : ((m : ℚ) + 1) ≠ 0 := by positivity
  have hdiff : S.comp (X + 1) - S = X * Pi a m := by
    have e2 := Pi_diff a (m + 1)
    have e1 := Pi_diff a m
    rw [hS, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.mul_comp, Polynomial.C_comp,
      Polynomial.C_comp, X_mul_Pi]
    push_cast at e2
    rw [show m + 2 = m + 1 + 1 by ring]
    have : C (1 / ((m : ℚ) + 2)) * C ((m : ℚ) + 1 + 1) = (1 : ℚ[X]) := by
      rw [← map_mul, show (1 / ((m : ℚ) + 2)) * ((m : ℚ) + 1 + 1) = 1 by field_simp; ring,
        map_one]
    have h' : C (((a : ℚ) + m) / ((m : ℚ) + 1)) * C ((m : ℚ) + 1) = C ((a : ℚ) + m) := by
      rw [← map_mul, div_mul_cancel₀ _ hm1]
    linear_combination C (1 / ((m : ℚ) + 2)) * e2
      + C (((a : ℚ) + m) / ((m : ℚ) + 1)) * e1 + Pi a (m + 1) * this + Pi a m * h'
  rw [← hdiff, tau_diff_eq_coeff_four, hS, Polynomial.coeff_add, Polynomial.coeff_C_mul,
    Polynomial.coeff_C_mul]
  ring

lemma Pi_eq_prod (a j : ℕ) : Pi a j = ∏ i ∈ range j, (X - C ((a : ℚ) + i)) := by
  induction j with
  | zero => simp [Pi]
  | succ j ih =>
    rw [Pi, descPochhammer_succ_right, Polynomial.mul_comp, ← Pi, ih, Finset.prod_range_succ,
      Polynomial.sub_comp, Polynomial.X_comp, Polynomial.natCast_comp]
    simp only [map_add, map_natCast]
    ring

section PolyPart

variable {p : ℕ} [hp : Fact p.Prime]

/-- `|K!(K+j)!/k!|_p ≤ p^{⌊log_p k⌋}` when `K ≤ k ≤ 2K + j`: it is an integer over `C(k,K)`. -/
lemma padicNorm_factorial_ratio (K j k : ℕ) (hKk : K ≤ k) (hjk : k - K ≤ K + j) :
    padicNorm p ((K.factorial : ℚ) * ((K + j).factorial : ℚ) / (k.factorial : ℚ))
      ≤ (p : ℚ) ^ (Nat.log p k) := by
  obtain ⟨t, ht⟩ := Nat.factorial_dvd_factorial hjk
  have hkey : (K.factorial : ℚ) * ((K + j).factorial : ℚ) / (k.factorial : ℚ)
      = ((t : ℕ) : ℚ) / (k.choose K : ℚ) := by
    rw [ht, Nat.cast_choose ℚ hKk]
    have h1 : (k.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
    have h2 : (K.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
    have h3 : ((k - K).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
    push_cast
    field_simp
  rw [hkey]
  exact padicNorm_div_choose_le (padicNorm.of_nat _) hKk

/-- The weighted Gauss bound for `F_j(x) = ∏_{i<j}(1 - x/(K+1+i))`:
`|[x⁴]F_j|_p ≤ p^{4⌊log_p(K+j)⌋}`. -/
lemma padicNorm_F_coeff_four (K j : ℕ) :
    padicNorm p ((∏ i ∈ range j, (1 - C (((K : ℚ) + 1 + i))⁻¹ * X)).coeff 4)
      ≤ (p : ℚ) ^ (4 * Nat.log p (K + j)) := by
  set ℓ := Nat.log p (K + j) with hℓ
  set F := ∏ i ∈ range j, (1 - C (((K : ℚ) + 1 + i))⁻¹ * X) with hF
  have hp0 : (0 : ℚ) < (p : ℚ) := by exact_mod_cast hp.out.pos
  have hG : F.comp (C ((p : ℚ) ^ ℓ) * X)
      = ∏ i ∈ range j, (1 - C ((p : ℚ) ^ ℓ * (((K : ℚ) + 1 + i))⁻¹) * X) := by
    rw [hF, Polynomial.prod_comp]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Polynomial.sub_comp, Polynomial.one_comp, Polynomial.mul_comp, Polynomial.C_comp,
      Polynomial.X_comp, map_mul]
    ring
  have hGint : vGAtLeast p (F.comp (C ((p : ℚ) ^ ℓ) * X)) 0 := by
    rw [hG]
    have := vGAtLeast_prod (p := p) (range j)
      (fun i => (1 - C ((p : ℚ) ^ ℓ * (((K : ℚ) + 1 + i))⁻¹) * X)) (fun _ => 0) (fun i hi => by
        have hi' := Finset.mem_range.1 hi
        have hb : ((K : ℚ) + 1 + i) = ((K + 1 + i : ℕ) : ℚ) := by push_cast; ring
        have hnorm : padicNorm p ((p : ℚ) ^ ℓ * (((K : ℚ) + 1 + i))⁻¹) ≤ 1 := by
          rw [hb, padicNorm.mul, padicNorm_pow, padicNorm.padicNorm_p_of_prime]
          have hb0 : (K + 1 + i) ≠ 0 := by omega
          have h1 := padicNorm_one_div_le_log (p := p) hb0
          rw [one_div] at h1
          have h2 : (p : ℚ) ^ (Nat.log p (K + 1 + i)) ≤ (p : ℚ) ^ ℓ :=
            p_pow_mono (Nat.log_mono_right (by omega))
          have h3 : ((p : ℚ)⁻¹) ^ ℓ * (p : ℚ) ^ ℓ = 1 := by
            rw [← mul_pow, inv_mul_cancel₀ hp0.ne', one_pow]
          have h4 : (0 : ℚ) ≤ ((p : ℚ)⁻¹) ^ ℓ := by positivity
          calc ((p : ℚ)⁻¹) ^ ℓ * padicNorm p (((K + 1 + i : ℕ) : ℚ))⁻¹
              ≤ ((p : ℚ)⁻¹) ^ ℓ * (p : ℚ) ^ ℓ := mul_le_mul_of_nonneg_left (le_trans h1 h2) h4
            _ = 1 := h3
        have hc : vGAtLeast p (C ((p : ℚ) ^ ℓ * (((K : ℚ) + 1 + i))⁻¹) * X) 0 := by
          simpa using vGAtLeast_mul (vGAtLeast_C hnorm) vGAtLeast_X
        exact vGAtLeast_sub (by simpa using vGAtLeast_C (p := p) (a := 1) (by simp)) hc)
    simpa using this
  have hcoef := (vGAtLeast_zero_iff _).1 hGint 4
  rw [Polynomial.comp_C_mul_X_coeff, padicNorm.mul, padicNorm_pow, padicNorm_pow,
    padicNorm.padicNorm_p_of_prime] at hcoef
  have hpos : (0 : ℚ) < ((p : ℚ)⁻¹ ^ ℓ) ^ 4 := by positivity
  have hinv : ((p : ℚ)⁻¹ ^ ℓ) ^ 4 * (p : ℚ) ^ (4 * ℓ) = 1 := by
    rw [← pow_mul, mul_comm ℓ 4, ← mul_pow, inv_mul_cancel₀ hp0.ne', one_pow]
  have hpp : (0 : ℚ) ≤ (p : ℚ) ^ (4 * ℓ) := by positivity
  nlinarith [mul_le_mul_of_nonneg_right hcoef hpp, padicNorm.nonneg (p := p) (F.coeff 4)]

/-- `|(K!)²/k! · [x⁴]Π_j|_p ≤ p^{⌊log_p k⌋ + 4⌊log_p(K+j)⌋}` for `Π_j = Pi (K+1) j`. -/
lemma padicNorm_Pi_coeff_four (K j k : ℕ) (hKk : K ≤ k) (hjk : k - K ≤ K + j) :
    padicNorm p (((K.factorial : ℚ)) ^ 2 / (k.factorial : ℚ) * (Pi (K + 1) j).coeff 4)
      ≤ (p : ℚ) ^ (Nat.log p k + 4 * Nat.log p (K + j)) := by
  have hb : ∀ i : ℕ, ((K : ℚ) + 1 + i) ≠ 0 := fun i => by positivity
  have hfac : ∀ i : ℕ, (X - C (((K + 1 : ℕ) : ℚ) + i))
      = C (-((K : ℚ) + 1 + i)) * (1 - C (((K : ℚ) + 1 + i))⁻¹ * X) := by
    intro i
    rw [mul_sub, mul_one, ← mul_assoc, ← map_mul,
      show -((K : ℚ) + 1 + i) * ((K : ℚ) + 1 + i)⁻¹ = -1 by field_simp]
    push_cast
    simp only [map_neg, map_one]
    ring
  have hprodK : ∀ j : ℕ, (K.factorial : ℚ) * ∏ i ∈ range j, ((K : ℚ) + 1 + i)
      = ((K + j).factorial : ℚ) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Finset.prod_range_succ, ← mul_assoc, ih, ← add_assoc, Nat.factorial_succ]
      push_cast; ring
  rw [Pi_eq_prod, Finset.prod_congr rfl (fun i _ => hfac i), Finset.prod_mul_distrib,
    ← map_prod, Polynomial.coeff_C_mul]
  have hneg : ∏ i ∈ range j, (-((K : ℚ) + 1 + i)) = (-1) ^ j * ∏ i ∈ range j, ((K : ℚ) + 1 + i) := by
    rw [Finset.prod_congr rfl (fun (i : ℕ) _ =>
        show -((K : ℚ) + 1 + (i : ℚ)) = (-1) * ((K : ℚ) + 1 + (i : ℚ)) by ring),
      Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
  rw [hneg]
  have hre : ((K.factorial : ℚ)) ^ 2 / (k.factorial : ℚ)
        * ((-1) ^ j * ∏ i ∈ range j, ((K : ℚ) + 1 + i))
      = (-1) ^ j * ((K.factorial : ℚ) * ((K + j).factorial : ℚ) / (k.factorial : ℚ)) := by
    rw [← hprodK j]; ring
  rw [← mul_assoc, hre, padicNorm.mul, padicNorm.mul, padicNorm_pow, padicNorm.neg,
    padicNorm.one, one_pow, one_mul, pow_add]
  exact mul_le_mul (padicNorm_factorial_ratio K j k hKk hjk) (padicNorm_F_coeff_four K j)
    (padicNorm.nonneg _) (by positivity)

/-- For `k = 2K+1+m`: `C(x+K, k) = T(x) · (x Π_m(x)/k!)`. -/
lemma binom_shift_large (K m : ℕ) :
    (binomPoly (2 * K + 1 + m)).comp (X + C (K : ℚ))
      = Tpoly (poles K) * (C (((2 * K + 1 + m).factorial : ℚ))⁻¹ * (X * Pi (K + 1) m)) := by
  rw [binomPoly, Polynomial.mul_comp, Polynomial.C_comp, ← descPochhammer_mul,
    Polynomial.mul_comp, ← X_mul_Tpoly, Polynomial.comp_assoc, Pi]
  have hsh : ((X - (((2 * K + 1 : ℕ)) : ℚ[X])).comp (X + C (K : ℚ))) = X - C (((K + 1 : ℕ)) : ℚ) := by
    rw [Polynomial.sub_comp, Polynomial.X_comp, Polynomial.natCast_comp]
    push_cast
    rw [map_add, map_one, map_natCast]
    ring
  rw [hsh]
  ring

lemma quot_large (K m : ℕ) :
    (binomPoly (2 * K + 1 + m)).comp (X + C (K : ℚ)) /ₘ Tpoly (poles K)
      = C (((2 * K + 1 + m).factorial : ℚ))⁻¹ * (X * Pi (K + 1) m) := by
  rw [binom_shift_large]
  exact Polynomial.mul_divByMonic_cancel_left _ (Tpoly_poles_monic K)

lemma tau_quot_small (K k : ℕ) (hk : k ≤ 2 * K) :
    tau ((binomPoly k).comp (X + C (K : ℚ)) /ₘ Tpoly (poles K)) = 0 := by
  have hdeg : ((binomPoly k).comp (X + C (K : ℚ)) /ₘ Tpoly (poles K)).natDegree = 0 := by
    rw [Polynomial.natDegree_divByMonic _ (Tpoly_poles_monic K), Polynomial.natDegree_comp,
      binomPoly_natDegree, natDegree_X_add_C, Tpoly_poles_natDegree]
    omega
  rw [Polynomial.eq_C_of_natDegree_eq_zero hdeg]
  simp [tau]

/-- **The polynomial part**, one binomial basis element at a time:
`|(K!)² τ(C(x+K,k)/T)|_p ≤ p^{6⌊log_p B⌋}` for `k + 1 ≤ B`. -/
lemma poly_part_bound (K k B : ℕ) (hkB : k + 1 ≤ B) :
    padicNorm p (((K.factorial : ℚ)) ^ 2
        * tau ((binomPoly k).comp (X + C (K : ℚ)) /ₘ Tpoly (poles K)))
      ≤ (p : ℚ) ^ (6 * Nat.log p B) := by
  rcases le_or_gt k (2 * K) with hk | hk
  · rw [tau_quot_small K k hk, mul_zero, padicNorm.zero]; positivity
  obtain ⟨m, rfl⟩ : ∃ m, k = 2 * K + 1 + m := ⟨k - (2 * K + 1), by omega⟩
  rw [quot_large, tau_C_mul, tau_X_mul_Pi]
  set k := 2 * K + 1 + m with hk_def
  set A2 := (Pi (K + 1) (m + 2)).coeff 4
  set A1 := (Pi (K + 1) (m + 1)).coeff 4
  have e : ((K.factorial : ℚ)) ^ 2 * (((k.factorial : ℚ))⁻¹
        * (A2 / ((m : ℚ) + 2) + (((K + 1 : ℕ) : ℚ) + m) / ((m : ℚ) + 1) * A1))
      = (1 / ((m + 2 : ℕ) : ℚ)) * (((K.factorial : ℚ)) ^ 2 / (k.factorial : ℚ) * A2)
        + ((((K + 1 + m : ℕ)) : ℚ) * (1 / ((m + 1 : ℕ) : ℚ)))
          * (((K.factorial : ℚ)) ^ 2 / (k.factorial : ℚ) * A1) := by
    push_cast; ring
  rw [e]
  refine le_trans padicNorm.nonarchimedean (max_le ?_ ?_)
  · rw [padicNorm.mul]
    have h1 := padicNorm_one_div_le_log (p := p) (show m + 2 ≠ 0 by omega)
    have h2 := padicNorm_Pi_coeff_four (p := p) K (m + 2) k (by omega) (by omega)
    calc padicNorm p (1 / ((m + 2 : ℕ) : ℚ))
          * padicNorm p (((K.factorial : ℚ)) ^ 2 / (k.factorial : ℚ) * A2)
        ≤ (p : ℚ) ^ (Nat.log p (m + 2)) * (p : ℚ) ^ (Nat.log p k + 4 * Nat.log p (K + (m + 2))) :=
          mul_le_mul h1 h2 (padicNorm.nonneg _) (by positivity)
      _ = (p : ℚ) ^ (Nat.log p (m + 2) + (Nat.log p k + 4 * Nat.log p (K + (m + 2)))) := by
          rw [← pow_add]
      _ ≤ _ := by
          refine p_pow_mono ?_
          have := Nat.log_mono_right (b := p) (show m + 2 ≤ B by omega)
          have := Nat.log_mono_right (b := p) (show k ≤ B by omega)
          have := Nat.log_mono_right (b := p) (show K + (m + 2) ≤ B by omega)
          omega
  · rw [padicNorm.mul, padicNorm.mul]
    have h0 := padicNorm.of_nat (p := p) (K + 1 + m)
    have h1 := padicNorm_one_div_le_log (p := p) (show m + 1 ≠ 0 by omega)
    have h2 := padicNorm_Pi_coeff_four (p := p) K (m + 1) k (by omega) (by omega)
    calc padicNorm p (((K + 1 + m : ℕ)) : ℚ) * padicNorm p (1 / ((m + 1 : ℕ) : ℚ))
          * padicNorm p (((K.factorial : ℚ)) ^ 2 / (k.factorial : ℚ) * A1)
        ≤ 1 * (p : ℚ) ^ (Nat.log p (m + 1))
            * (p : ℚ) ^ (Nat.log p k + 4 * Nat.log p (K + (m + 1))) := by
          refine mul_le_mul (mul_le_mul h0 h1 (padicNorm.nonneg _) zero_le_one) h2
            (padicNorm.nonneg _) (by positivity)
      _ = (p : ℚ) ^ (Nat.log p (m + 1) + (Nat.log p k + 4 * Nat.log p (K + (m + 1)))) := by
          rw [one_mul, ← pow_add]
      _ ≤ _ := by
          refine p_pow_mono ?_
          have := Nat.log_mono_right (b := p) (show m + 1 ≤ B by omega)
          have := Nat.log_mono_right (b := p) (show k ≤ B by omega)
          have := Nat.log_mono_right (b := p) (show K + (m + 1) ≤ B by omega)
          omega

end PolyPart

/-! # §6.  Lemma 3.3 -/

lemma divByMonic_sum_C_mul {ι : Type*} (t : Finset ι) (c : ι → ℚ) (f : ι → ℚ[X]) (T : ℚ[X]) :
    (∑ i ∈ t, C (c i) * f i) /ₘ T = ∑ i ∈ t, C (c i) * (f i /ₘ T) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Polynomial.add_divByMonic, ih]
    congr 1
    rw [← Polynomial.smul_eq_C_mul, ← Polynomial.smul_eq_C_mul, Polynomial.smul_divByMonic]

lemma mem_ZpSub {p : ℕ} [Fact p.Prime] {x : ℚ} : x ∈ ZpSub p ↔ padicNorm p x ≤ 1 := Iff.rfl

/-- **§3.3, p. 8**: *"If `A(ℤ_p) ⊂ ℤ_p` and `deg A ≤ d`, then the coefficients in its
expansion in `C(x,k)` are integral.  Indeed, they are the forward differences of `A` at
zero."*  The `p`-local form of `Zeta5.integer_binom_coeffs`: `p`-integral values at the
naturals give `p`-integral binomial coefficients (the same triangular recursion). -/
theorem padic_binom_coeffs {p : ℕ} [Fact p.Prime] (d : ℕ) (P : ℚ[X]) (hP : P.natDegree ≤ d)
    (hint : ∀ m : ℕ, padicNorm p (P.eval ((m : ℕ) : ℚ)) ≤ 1) :
    ∃ c : ℕ → ℚ, (∀ k, padicNorm p (c k) ≤ 1) ∧
      P = ∑ k ∈ range (d + 1), C (c k) * binomPoly k := by
  obtain ⟨c, hc⟩ := exists_binom_expansion d P hP
  have heval : ∀ k : ℕ, k ≤ d →
      P.eval ((k : ℕ) : ℚ) = (∑ j ∈ range k, c j * (k.choose j : ℚ)) + c k := by
    intro k hk
    have h1 : P.eval ((k : ℕ) : ℚ) = ∑ j ∈ range (d + 1), c j * (k.choose j : ℚ) := by
      conv_lhs => rw [hc]
      rw [Polynomial.eval_finsetSum]
      exact Finset.sum_congr rfl fun j _ => by
        rw [Polynomial.eval_mul, Polynomial.eval_C, binomPoly_eval_nat]
    have hsub : range (k + 1) ⊆ range (d + 1) := by
      intro x hx
      rw [Finset.mem_range] at hx ⊢
      omega
    have h2 : ∑ j ∈ range (k + 1), c j * (k.choose j : ℚ)
        = ∑ j ∈ range (d + 1), c j * (k.choose j : ℚ) := by
      refine Finset.sum_subset hsub ?_
      intro x _ hnx
      have hx1 : k < x := by
        by_contra hcon
        exact hnx (Finset.mem_range.2 (by omega))
      rw [Nat.choose_eq_zero_of_lt hx1]
      simp
    rw [h1, ← h2, Finset.sum_range_succ, Nat.choose_self]
    push_cast
    ring
  have key : ∀ k, k ≤ d → c k ∈ ZpSub p := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hkd
      have hsum : (∑ j ∈ range k, c j * (k.choose j : ℚ)) ∈ ZpSub p :=
        Subring.sum_mem _ fun j hj => by
          have hjk := Finset.mem_range.1 hj
          exact Subring.mul_mem _ (ih j hjk (by omega)) (mem_ZpSub.2 (padicNorm.of_nat _))
      have hrec : c k = P.eval ((k : ℕ) : ℚ) - ∑ j ∈ range k, c j * (k.choose j : ℚ) := by
        rw [heval k hkd]; ring
      rw [hrec]
      exact Subring.sub_mem _ (mem_ZpSub.2 (hint k)) hsum
  refine ⟨fun k => if k ≤ d then c k else 0, fun k => ?_, ?_⟩
  · show padicNorm p (if k ≤ d then c k else 0) ≤ 1
    split_ifs with h
    · exact mem_ZpSub.1 (key k h)
    · simp
  · conv_lhs => rw [hc]
    refine Finset.sum_congr rfl fun k hk => ?_
    show C (c k) * binomPoly k = C (if k ≤ d then c k else 0) * binomPoly k
    rw [ite_eq_left_iff.2 (fun h => absurd (by have := Finset.mem_range.1 hk; omega) h)]

/-- **Lemma 3.3, in the strong form proved here**: for `A` with `A(ℤ) ⊂ ℤ_p` (which is
implied by the paper's `A(ℤ_p) ⊂ ℤ_p`) and `deg A ≤ d`, and any `B ≥ max(2K, d+1)`,
`v_p^G((K!)² τ_X(A/T)) ≥ -6⌊log_p B⌋`. -/
theorem lemma_3_3_strong {p : ℕ} [Fact p.Prime] (K d B : ℕ) (h2K : 2 * K ≤ B)
    (hdB : d + 1 ≤ B) (A : ℚ[X]) (hdeg : A.natDegree ≤ d)
    (hint : ∀ z : ℤ, padicNorm p (A.eval (z : ℚ)) ≤ 1) :
    vGAtLeast p (C (((K.factorial : ℚ)) ^ 2) * tauExtOf X (poles K) A)
      (-6 * (Nat.log p B : ℤ)) := by
  classical
  -- the binomial expansion of `A` around `-K`, with integer coefficients (p. 8)
  have hint' : ∀ m : ℕ, padicNorm p ((A.comp (X - C (K : ℚ))).eval ((m : ℕ) : ℚ)) ≤ 1 := by
    intro m
    have hw := hint ((m : ℤ) - K)
    rw [Polynomial.eval_comp, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    push_cast at hw
    exact hw
  have hdeg' : (A.comp (X - C (K : ℚ))).natDegree ≤ d := by
    rw [Polynomial.natDegree_comp, natDegree_X_sub_C, mul_one]; exact hdeg
  obtain ⟨c, hcp, hc⟩ := padic_binom_coeffs d _ hdeg' hint'
  have hA : A = ∑ k ∈ range (d + 1), C (c k) * (binomPoly k).comp (X + C (K : ℚ)) := by
    have h := congrArg (fun P => P.comp (X + C (K : ℚ))) hc
    simp only [Polynomial.comp_assoc, Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp,
      add_sub_cancel_right, Polynomial.comp_X, Polynomial.sum_comp, Polynomial.mul_comp] at h
    exact h
  -- split `τ_X(A/T)` into the polynomial part and the pole terms
  have hsplit : C (((K.factorial : ℚ)) ^ 2) * tauExtOf X (poles K) A
      = C (((K.factorial : ℚ)) ^ 2 * tau (A /ₘ Tpoly (poles K)))
        + C (((K.factorial : ℚ)) ^ 2)
          * ∑ r ∈ poles K, C (resid (poles K) A r) * (C (H5 (dIdx r)) - X) := by
    rw [tauExtOf, tauExt, mul_add, map_mul]
  rw [hsplit]
  refine vGAtLeast_add ?_ ?_
  · -- the polynomial part
    have := vGAtLeast_C_of_padicNorm_le (p := p) (e := 6 * Nat.log p B) (x :=
      ((K.factorial : ℚ)) ^ 2 * tau (A /ₘ Tpoly (poles K))) (by
        have hq : A /ₘ Tpoly (poles K) = ∑ k ∈ range (d + 1),
            C (c k) * ((binomPoly k).comp (X + C (K : ℚ)) /ₘ Tpoly (poles K)) := by
          conv_lhs => rw [hA]
          exact divByMonic_sum_C_mul _ _ _ _
        rw [hq, tau_sum, Finset.mul_sum]
        refine padicNorm.sum_le' (fun k hk => ?_) (by positivity)
        rw [tau_C_mul, mul_left_comm, padicNorm.mul]
        have h1 := poly_part_bound (p := p) K k B (by
          have := Finset.mem_range.1 hk; omega)
        calc padicNorm p (c k) * padicNorm p (((K.factorial : ℚ)) ^ 2
              * tau ((binomPoly k).comp (X + C (K : ℚ)) /ₘ Tpoly (poles K)))
            ≤ 1 * (p : ℚ) ^ (6 * Nat.log p B) :=
              mul_le_mul (hcp k) h1 (padicNorm.nonneg _) zero_le_one
          _ = _ := one_mul _)
    refine vGAtLeast.mono this ?_
    push_cast; omega
  · -- the pole terms
    refine vGAtLeast.mono (residue_part_bound K A (fun r _ => hint r)) ?_
    have := Nat.log_mono_right (b := p) h2K
    have := Nat.log_mono_right (b := p) (show K ≤ B by omega)
    push_cast
    omega

/-- **Lemma 3.3 as printed** (p. 8), **(3.10)**: for `A` integer-valued on `ℤ_p` (here: the
weaker `A(ℤ) ⊂ ℤ_p`) with `deg A ≤ d`, and `g(x) = (K!)²A(x)/∏_{-K≤r≤K, r≠0}(x-r)`,

    `v_p^G(τ_X(g)) ≥ -6⌊log_p max(2K, d+1)⌋ - v_p(24)`.

Here `τ_X(g)` is `tauExtOf X (poles K) ((K!)²A)`: polynomial division by
`T(x) = ∏_{0<|r|≤K}(x-r)` and simple partial fractions (p. 6). -/
theorem lemma_3_3 {p : ℕ} [Fact p.Prime] (K d : ℕ) (A : ℚ[X]) (hdeg : A.natDegree ≤ d)
    (hint : ∀ z : ℤ, padicNorm p (A.eval (z : ℚ)) ≤ 1) :
    vGAtLeast p (tauExtOf X (poles K) (C (((K.factorial : ℚ)) ^ 2) * A))
      (-6 * (Nat.log p (max (2 * K) (d + 1)) : ℤ) - (padicValNat p 24 : ℤ)) := by
  rw [tauExtOf_C_mul]
  exact vGAtLeast.mono (lemma_3_3_strong K d _ (le_max_left _ _) (le_max_right _ _) A hdeg hint)
    (by omega)

/-! # §7.  The entries of (3.11) -/

/-- `f(t) = (D_N(t)/(N!)²)³ Q(t)`, the shape of the basis `f_i` of p. 9 (`CrudeBound.fb` is
`fbq n (qb i)`). -/
def fbq (n : ℕ) (Q : ℚ[X]) : ℚ[X] := C ((((N n).factorial : ℚ)) ^ 6)⁻¹ * (D (N n)) ^ 3 * Q

/-- **(3.1) at the entries of (3.11)**:
`(K!)² μ_X(f₁f₂/D_K) = (-1)^K τ_X((K!)² x⁵ f₁(-x²) f₂(-x²) / ∏_{0<|r|≤K}(x-r))`. -/
theorem entry_pullback (n : ℕ) (Q1 Q2 : ℚ[X]) :
    C ((((K n).factorial : ℚ)) ^ 2 * ((((N n).factorial : ℚ)) ^ 12)⁻¹)
        * muOver n ((D (N n)) ^ 5 * (Q1 * Q2))
      = C ((-1 : ℚ) ^ K n) * tauExtOf X (poles (K n)) (C ((((K n).factorial : ℚ)) ^ 2)
          * (X ^ 5 * ((fbq n Q1).comp (-(X ^ 2)) * (fbq n Q2).comp (-(X ^ 2))))) := by
  have hN : (((N n).factorial : ℚ)) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  have hpb : pb n ((D (N n)) ^ 5 * (Q1 * Q2))
      = C ((((N n).factorial : ℚ)) ^ 12)
          * (X ^ 5 * ((fbq n Q1).comp (-(X ^ 2)) * (fbq n Q2).comp (-(X ^ 2)))) := by
    have hu : C ((((N n).factorial : ℚ)) ^ 12) * C ((((N n).factorial : ℚ)) ^ 6)⁻¹
        * C ((((N n).factorial : ℚ)) ^ 6)⁻¹ = (1 : ℚ[X]) := by
      rw [← map_mul, ← map_mul, show (((N n).factorial : ℚ)) ^ 12
        * ((((N n).factorial : ℚ)) ^ 6)⁻¹ * ((((N n).factorial : ℚ)) ^ 6)⁻¹ = 1 by
          field_simp, map_one]
    simp only [pb, fbq, Polynomial.mul_comp, Polynomial.pow_comp, Polynomial.C_comp]
    linear_combination (-(X ^ 5 * ((D (N n)).comp (-(X ^ 2))) ^ 6 * Q1.comp (-(X ^ 2))
      * Q2.comp (-(X ^ 2)))) * hu
  rw [pullback, hpb, tauExtOf_C_mul, tauExtOf_C_mul]
  have hk : C ((((K n).factorial : ℚ)) ^ 2 * ((((N n).factorial : ℚ)) ^ 12)⁻¹)
      * C ((((N n).factorial : ℚ)) ^ 12) = C ((((K n).factorial : ℚ)) ^ 2) := by
    rw [← map_mul, inv_mul_cancel_right₀ (pow_ne_zero _ hN)]
  linear_combination (C ((-1 : ℚ) ^ K n) * tauExtOf X (poles (K n))
    (X ^ 5 * ((fbq n Q1).comp (-(X ^ 2)) * (fbq n Q2).comp (-(X ^ 2))))) * hk

/-- **Lemma 3.3 at an entry of (3.11)** (pp. 8–9): if the pullback numerator
`A = x⁵f₁(-x²)f₂(-x²)` is integer-valued with `deg A ≤ d` and `max(2K, d+1) ≤ 5K`, then
`v_p^G((K!)² μ_X(f₁f₂/D_K)) ≥ -6⌊log_p 5K⌋ - v_p(24)`. -/
theorem entry_bound {p : ℕ} [Fact p.Prime] (n : ℕ) (Q1 Q2 : ℚ[X]) (d : ℕ)
    (hdeg : (X ^ 5 * ((fbq n Q1).comp (-(X ^ 2)) * (fbq n Q2).comp (-(X ^ 2)))).natDegree ≤ d)
    (hint : ∀ z : ℤ, ∃ w : ℤ,
      (X ^ 5 * ((fbq n Q1).comp (-(X ^ 2)) * (fbq n Q2).comp (-(X ^ 2)))).eval (z : ℚ) = (w : ℚ))
    (hB : max (2 * K n) (d + 1) ≤ 5 * K n) :
    vGAtLeast p (C ((((K n).factorial : ℚ)) ^ 2 * ((((N n).factorial : ℚ)) ^ 12)⁻¹)
        * muOver n ((D (N n)) ^ 5 * (Q1 * Q2)))
      (-6 * (Nat.log p (5 * K n) : ℤ) - (padicValNat p 24 : ℤ)) := by
  rw [entry_pullback, tauExtOf_C_mul]
  have hint' : ∀ z : ℤ, padicNorm p ((X ^ 5 * ((fbq n Q1).comp (-(X ^ 2))
      * (fbq n Q2).comp (-(X ^ 2)))).eval (z : ℚ)) ≤ 1 := by
    intro z
    obtain ⟨w, hw⟩ := hint z
    rw [hw]; exact padicNorm.of_int w
  have hmain := lemma_3_3_strong (p := p) (K n) d (5 * K n) (le_trans (le_max_left _ _) hB)
    (le_trans (le_max_right _ _) hB) _ hdeg hint'
  have hsign : vGAtLeast p (C ((-1 : ℚ) ^ K n)) 0 := by
    refine vGAtLeast_C ?_
    rw [padicNorm_pow, padicNorm.neg, padicNorm.one, one_pow]
  refine vGAtLeast.mono (vGAtLeast_mul hsign hmain) ?_
  omega

/-! # Known-answer controls

Small cases, re-derived by Lean from the definitions.  The exact-arithmetic controls that
guided the proof (the closed form of `τ` on the binomial basis, the pullback (3.1) against the
definition of `muOver`, and the entry bound at `n = 1` on all 703 entries of (3.11) for
`p ∈ {2,3,5,7,11,13,37,41,43,199,211}`) are in `numerics/lemma33/` and are summarised in the
head of this file. -/

section Controls

/-- The pole set at `K = 2` is `{±1, ±2}`. -/
example : poles 2 = {-2, -1, 1, 2} := by decide

/-- `T(x) = x² - 1` at `K = 1`. -/
example : Tpoly (poles 1) = X ^ 2 - 1 := by
  rw [Tpoly_poles_succ, Tpoly_poles_zero]
  simp only [Nat.cast_zero, zero_add, map_one]
  ring

/-- `r·T'(r)` at `K = 2`, `r = 1`: `T = (x²-1)(x²-4)`, `T'(1) = 2·1·(1-4) = -6`, and the
closed form `(-1)^{2K-a} a!(2K-a)!` with `a = r+K = 3` gives `(-1)·3!·1! = -6`. -/
example : (1 : ℚ) * (derivative (Tpoly (poles 2))).eval 1 = -6 := by
  have h := deriv_Tpoly_eval 2 (r := 1) (by decide)
  norm_num [Nat.factorial] at h ⊢
  exact h

example : (derivative (Tpoly (poles 2))).eval 1 = -6 := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, Tpoly_poles_succ, Tpoly_poles_succ, Tpoly_poles_zero]
  simp only [derivative_mul, derivative_sub, derivative_add, derivative_X, derivative_C,
    derivative_one, eval_add, eval_mul, eval_sub, eval_X, eval_C, eval_one]
  norm_num

/-- `∏_{i ∈ {0,2,3}}(1 - i) = 2 = (-1)^{3-1}·1!·2!`. -/
example : ∏ i ∈ (range (3 + 1)).erase 1, (((1 : ℕ) : ℚ) - i) = 2 := by
  rw [prod_range_erase_sub 1 3 (by norm_num)]
  norm_num [Nat.factorial]

/-- `τ(ΔS) = [x⁴]S` at `S = x⁴`: `ΔS = 4x³ + 6x² + 4x + 1` and `τ(ΔS) = 4κ₃ = 1`. -/
example : tau (((X : ℚ[X]) ^ 4).comp (X + 1) - X ^ 4) = 1 := by
  rw [tau_diff_eq_coeff_four]; simp

example : tau (4 * X ^ 3 + 6 * X ^ 2 + 4 * X + 1 : ℚ[X]) = 1 := by
  have h4 : (4 : ℚ[X]) = C 4 := (map_ofNat C 4).symm
  have h6 : (6 : ℚ[X]) = C 6 := (map_ofNat C 6).symm
  have h1 : (1 : ℚ[X]) = C 1 * X ^ 0 := by simp
  rw [h4, h6, h1, tau_add, tau_add, tau_add, tau_C_mul, tau_C_mul, tau_C_mul, tau_C_mul,
    tau_X_pow, tau_X_pow, tau_X_eq_zero, tau_X_pow, kappa_three]
  norm_num [kappa]

end Controls

end Lemma33

/-! # Audit trail -/

section
#print axioms Zeta5.Lemma33.pullback
#print axioms Zeta5.Lemma33.lemma_3_3_strong
#print axioms Zeta5.Lemma33.lemma_3_3
#print axioms Zeta5.Lemma33.entry_pullback
#print axioms Zeta5.Lemma33.entry_bound
end

end

end Zeta5
