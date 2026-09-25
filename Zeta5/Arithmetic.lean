/-
Zeta5/Arithmetic.lean

Part of the Lean formalisation of

    A. Fauzan, "ζ(5) is irrational", 17 September 2026.

Elementary arithmetic infrastructure for the paper, and the assembly of Theorem 2.1 from five
statements of the paper, taken as hypotheses.

Contents, in the order the paper uses them:

  §A  (5.3), p. 13: Legendre's formula for `v_p(S_K)`, including the `(h-1) v_p(4)` term.
  §B  §3.3, p. 8:  integer-valued polynomials and the binomial basis, and (3.12).
  §C  §3.1, p. 6:  von Staudt–Clausen, `v_p(B_{2k}) ≥ -1` and `κ_d ∈ ℤ_p` for `d ≤ p+1`.
  §D  §7, p. 21:   the assembly — Theorem 2.1 from Prop 5.1, (2.9), Prop 2.2, (5.21), (6.16).
  §E  (7.2), p. 21: the final margin `A_200 + U < -139/8000`, exact rational arithmetic.

The hypotheses of the §D theorems transcribe the paper's own statements, so that the §D
results are unconditional implications.

IMPORTS.  This file must not import `Zeta5.Interface`: `Zeta5/Section3.lean`, which proves
`Interface.prop_4_1`, imports this file.  The non-local dependencies are
`Theorem_2_1`/`theorem_1_1` (Skeleton) and `eq_7_1_of` / `log_linear_le_quadratic`
(Asymptotics).  Names of `Interface.lean` occur below only in prose.
-/
import Zeta5.Skeleton
import Zeta5.Asymptotics
import Zeta5.Functional
import Zeta5.Section41
import Zeta5.Normalization

namespace Zeta5

open Polynomial Finset

noncomputable section

/-! # §A. (5.3): Legendre's formula for `v_p(S_K)`

The paper's (5.3) (p. 13) reads

    v_p(S_K) = 2h ∑_{a≥1} ⌊K/p^a⌋ − 12h ∑_{a≥1} ⌊N/p^a⌋
               − 2 ∑_{i=1}^{h−1} ∑_{a≥1} ⌊2i/p^a⌋ + (h−1) v_p(4),

i.e. Legendre's formula `v_p(m!) = ∑_{a≥1} ⌊m/p^a⌋` applied to each factorial of (2.5).
All three sums over `a` are finite: every factorial occurring in (2.5) has argument at most
`2K`, so every term with `p^a > 2K` vanishes.  We cut them off at `⌊log_p 2K⌋ + 1`. -/

/-- The uniform cutoff in the finite form of (5.3): beyond it every term of every sum in
(5.3) is zero, because every factorial in (2.5) has argument at most `2K`. -/
def legBound (n p : ℕ) : ℕ := Nat.log p (2 * K n) + 1

/-- **Legendre's formula** (Mathlib's `padicValNat_factorial`) with the uniform cutoff of
(5.3): `v_p(m!) = ∑_{a=1}^{legBound-1} ⌊m/p^a⌋` for every `m ≤ 2K`. -/
lemma padicValNat_factorial_legBound {n p m : ℕ} [Fact p.Prime] (hm : m ≤ 2 * K n) :
    padicValNat p m.factorial = ∑ a ∈ Finset.Ico 1 (legBound n p), m / p ^ a :=
  padicValNat_factorial (Nat.lt_succ_of_le (Nat.log_mono_right hm))

/-- The numerator of (2.5), `(K!)^{2h} · 4^{h-1}`, as a natural number. -/
def Snum (n : ℕ) : ℕ := (K n).factorial ^ (2 * h n) * 4 ^ (h n - 1)

/-- The denominator of (2.5), `(N!)^{12h} · ∏_{i=1}^{h-1}((2i)!)²`, as a natural number. -/
def Sden (n : ℕ) : ℕ :=
  (N n).factorial ^ (12 * h n) * ∏ i ∈ Icc 1 (h n - 1), ((2 * i).factorial) ^ 2

lemma Snum_ne_zero (n : ℕ) : Snum n ≠ 0 :=
  Nat.mul_ne_zero (pow_ne_zero _ (Nat.factorial_ne_zero _)) (pow_ne_zero _ (by norm_num))

lemma Sden_ne_zero (n : ℕ) : Sden n ≠ 0 :=
  Nat.mul_ne_zero (pow_ne_zero _ (Nat.factorial_ne_zero _))
    (Finset.prod_ne_zero_iff.2 fun _ _ => pow_ne_zero _ (Nat.factorial_ne_zero _))

/-- (2.5) as a quotient of two natural numbers. -/
lemma S_eq_div (n : ℕ) : S n = (Snum n : ℚ) / (Sden n : ℚ) := by
  unfold S Snum Sden
  push_cast
  ring

/-- `v_p` of a finite product of nonzero naturals is the sum of the `v_p`. -/
lemma padicValNat_prod {p : ℕ} (hp : p.Prime) {s : Finset ℕ} {f : ℕ → ℕ}
    (hf : ∀ i ∈ s, f i ≠ 0) :
    padicValNat p (∏ i ∈ s, f i) = ∑ i ∈ s, padicValNat p (f i) := by
  have h1 : (∏ i ∈ s, f i).factorization = ∑ i ∈ s, (f i).factorization :=
    Nat.factorization_prod hf
  have h2 := congrArg (fun F : ℕ →₀ ℕ => F p) h1
  simpa [Nat.factorization_def _ hp, Finsupp.finsetSum_apply] using h2

lemma vS_eq_sub (n p : ℕ) [Fact p.Prime] :
    vS n p = (padicValNat p (Snum n) : ℤ) - (padicValNat p (Sden n) : ℤ) := by
  have hnum : ((Snum n : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (Snum_ne_zero n)
  have hden : ((Sden n : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (Sden_ne_zero n)
  rw [vS, S_eq_div, padicValRat.div hnum hden, padicValRat.of_nat, padicValRat.of_nat]

lemma padicValNat_Snum (n p : ℕ) [Fact p.Prime] :
    padicValNat p (Snum n)
      = 2 * h n * padicValNat p ((K n).factorial) + (h n - 1) * padicValNat p 4 := by
  rw [Snum, padicValNat.mul (pow_ne_zero _ (Nat.factorial_ne_zero _))
      (pow_ne_zero _ (by norm_num)), padicValNat.pow, padicValNat.pow]

lemma padicValNat_Sden (n p : ℕ) (hp : p.Prime) :
    padicValNat p (Sden n)
      = 12 * h n * padicValNat p ((N n).factorial)
        + ∑ i ∈ Icc 1 (h n - 1), 2 * padicValNat p ((2 * i).factorial) := by
  have : Fact p.Prime := ⟨hp⟩
  rw [Sden, padicValNat.mul (pow_ne_zero _ (Nat.factorial_ne_zero _))
      (Finset.prod_ne_zero_iff.2 fun _ _ => pow_ne_zero _ (Nat.factorial_ne_zero _)),
    padicValNat.pow, padicValNat_prod hp fun _ _ => pow_ne_zero _ (Nat.factorial_ne_zero _)]
  simp [padicValNat.pow]

/-- **(5.3)** (p. 13).  Legendre's formula applied to (2.5), with all three sums over `a`
truncated at the uniform cutoff `legBound n p`, beyond which every term is zero.

The `(h-1) v_p(4)` term is the contribution of the factor `4^{h-1}` of (2.5); it is zero
unless `p = 2`, and at `p = 2` it equals `2(h-1)`. -/
theorem vS_eq (n p : ℕ) (hp : p.Prime) :
    vS n p
      = 2 * (h n : ℤ) * (∑ a ∈ Finset.Ico 1 (legBound n p), ((K n / p ^ a : ℕ) : ℤ))
        - 12 * (h n : ℤ) * (∑ a ∈ Finset.Ico 1 (legBound n p), ((N n / p ^ a : ℕ) : ℤ))
        - 2 * (∑ i ∈ Icc 1 (h n - 1),
              ∑ a ∈ Finset.Ico 1 (legBound n p), ((2 * i / p ^ a : ℕ) : ℤ))
        + ((h n - 1 : ℕ) : ℤ) * (padicValNat p 4 : ℤ) := by
  have : Fact p.Prime := ⟨hp⟩
  have hKle : K n ≤ 2 * K n := by omega
  have hNle : N n ≤ 2 * K n := by simp only [N, K]; omega
  have hin : ∀ i ∈ Icc 1 (h n - 1),
      padicValNat p ((2 * i).factorial) = ∑ a ∈ Finset.Ico 1 (legBound n p), 2 * i / p ^ a := by
    intro i hi
    have hi2 := (Finset.mem_Icc.1 hi).2
    refine padicValNat_factorial_legBound ?_
    simp only [h, K] at hi2 ⊢
    omega
  have hsum : ∑ i ∈ Icc 1 (h n - 1), 2 * padicValNat p ((2 * i).factorial)
      = ∑ i ∈ Icc 1 (h n - 1), 2 * ∑ a ∈ Finset.Ico 1 (legBound n p), 2 * i / p ^ a :=
    Finset.sum_congr rfl fun i hi => by rw [hin i hi]
  rw [vS_eq_sub, padicValNat_Snum, padicValNat_Sden n p hp, hsum,
    padicValNat_factorial_legBound hKle, padicValNat_factorial_legBound hNle]
  push_cast
  simp only [Finset.mul_sum]
  ring

/-! # §B. §3.3 (p. 8): integer-valued polynomials and the binomial basis

The paper says: *"We use the binomial basis for integer-valued polynomials.  If `A(ℤ_p) ⊂ ℤ_p`
and `deg A ≤ d`, then the coefficients in its expansion in `C(x,k)` are integral.  Indeed,
they are the forward differences of `A` at zero."*

`integer_binom_coeffs` below is exactly that statement, proved, over `ℚ` (the strongest
version: integrality is only assumed at the *nonnegative* integers).

The other ingredient of §3.3 is the Vandermonde bound (3.8),
`v_p(A(x) − A(y)) ≥ v_p(x − y) − ⌊log_p max(1,d)⌋`.  It is deliberately *not* stated here as
a Lean lemma: written with `padicValRat`, whose value at `0` is `0` rather than `+∞`, the
inequality is false whenever `A(x) = A(y)` with `x ≢ y`, so a faithful statement needs the
`v_p(0) = +∞` convention of `vGAtLeast`, which applies to polynomial coefficients and not to
a single value.  What §5 consumes is Lemma 3.3's output (3.12), proved in
`Zeta5/CrudeBound.lean`. -/

/-- The binomial polynomial `C(X,k) = X(X-1)⋯(X-k+1)/k!`.  `descPochhammer ℚ k` is the
falling factorial `X(X-1)⋯(X-k+1)`. -/
def binomPoly (k : ℕ) : ℚ[X] := C (((k.factorial : ℚ))⁻¹) * descPochhammer ℚ k

@[simp] lemma binomPoly_zero : binomPoly 0 = 1 := by simp [binomPoly]

/-- `C(m,k)` really is the value of `binomPoly k` at the natural number `m`. -/
@[simp] lemma binomPoly_eval_nat (k m : ℕ) :
    (binomPoly k).eval ((m : ℕ) : ℚ) = (m.choose k : ℚ) := by
  rw [binomPoly, Polynomial.eval_mul, Polynomial.eval_C,
    descPochhammer_eval_eq_descFactorial, Nat.descFactorial_eq_factorial_mul_choose]
  push_cast
  exact inv_mul_cancel_left₀ (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero k)) _

lemma binomPoly_natDegree (k : ℕ) : (binomPoly k).natDegree = k := by
  rw [binomPoly,
    Polynomial.natDegree_C_mul (inv_ne_zero (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero k))),
    descPochhammer_natDegree]

lemma binomPoly_coeff_self (k : ℕ) : (binomPoly k).coeff k = ((k.factorial : ℚ))⁻¹ := by
  have hlead : (descPochhammer ℚ k).coeff k = 1 := by
    have hm := monic_descPochhammer ℚ k
    rw [Polynomial.Monic, Polynomial.leadingCoeff, descPochhammer_natDegree] at hm
    exact hm
  rw [binomPoly, Polynomial.coeff_C_mul, hlead, mul_one]

/-- Every polynomial of degree at most `d` is a `ℚ`-combination of `C(X,0), …, C(X,d)`. -/
theorem exists_binom_expansion : ∀ (d : ℕ) (P : ℚ[X]), P.natDegree ≤ d →
    ∃ c : ℕ → ℚ, P = ∑ k ∈ range (d + 1), C (c k) * binomPoly k := by
  intro d
  induction d with
  | zero =>
      intro P hP
      refine ⟨fun _ => P.coeff 0, ?_⟩
      rw [Finset.sum_range_one, binomPoly_zero, mul_one]
      exact Polynomial.eq_C_of_natDegree_le_zero hP
  | succ d ih =>
      intro P hP
      set a : ℚ := P.coeff (d + 1) * (((d + 1).factorial : ℚ)) with ha
      set R : ℚ[X] := P - C a * binomPoly (d + 1) with hR
      have hBdeg : (C a * binomPoly (d + 1)).natDegree ≤ d + 1 := by
        refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
        rw [binomPoly_natDegree]
      have hdegR : R.natDegree ≤ d := by
        rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
        intro m hm
        rcases lt_or_eq_of_le (Nat.succ_le_of_lt hm) with hlt | heq
        · have hP0 : P.coeff m = 0 :=
            Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hP hlt)
          have hB0 : (C a * binomPoly (d + 1)).coeff m = 0 :=
            Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hBdeg hlt)
          rw [hR, Polynomial.coeff_sub, hP0, hB0, sub_zero]
        · subst heq
          rw [hR, Polynomial.coeff_sub, Polynomial.coeff_C_mul, binomPoly_coeff_self, ha]
          field_simp
          ring
      obtain ⟨c, hc⟩ := ih R hdegR
      refine ⟨Function.update c (d + 1) a, ?_⟩
      have hsum : ∑ k ∈ range (d + 1), C (Function.update c (d + 1) a k) * binomPoly k
          = ∑ k ∈ range (d + 1), C (c k) * binomPoly k :=
        Finset.sum_congr rfl fun k hk => by
          have hne : k ≠ d + 1 := by have := Finset.mem_range.1 hk; omega
          rw [Function.update_of_ne hne]
      rw [Finset.sum_range_succ, hsum, Function.update_self, ← hc, hR]
      ring

/-- **§3.3, p. 8** (the elementary half).  *"If `A(ℤ_p) ⊂ ℤ_p` and `deg A ≤ d`, then the
coefficients in its expansion in `C(x,k)` are integral."*

Proved here in the strongest form: a polynomial over `ℚ` of degree at most `d` that takes
integer values at every *natural number* has integer coefficients in the binomial basis.
The proof is the paper's own reason ("they are the forward differences of `A` at zero"),
carried out as the triangular recursion `c_k = A(k) − ∑_{j<k} c_j C(k,j)`. -/
theorem integer_binom_coeffs (d : ℕ) (P : ℚ[X]) (hP : P.natDegree ≤ d)
    (hint : ∀ m : ℕ, ∃ z : ℤ, P.eval ((m : ℕ) : ℚ) = (z : ℚ)) :
    ∃ c : ℕ → ℤ, P = ∑ k ∈ range (d + 1), C ((c k : ℚ)) * binomPoly k := by
  obtain ⟨c, hc⟩ := exists_binom_expansion d P hP
  -- the value of `P` at a natural number `k ≤ d`, in the binomial basis
  have heval : ∀ k : ℕ, k ≤ d →
      P.eval ((k : ℕ) : ℚ)
        = (∑ j ∈ range k, c j * (k.choose j : ℚ)) + c k := by
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
  -- every coefficient with index `≤ d` is an integer, by induction on the index
  have key : ∀ (B : ℕ), ∀ k, k < B → ∃ z : ℤ, (k ≤ d → c k = (z : ℚ)) := by
    intro B
    induction B with
    | zero => intro k hk; exact absurd hk (Nat.not_lt_zero k)
    | succ B ih =>
        intro k hk
        rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hlt | hBk
        · exact ih k hlt
        · subst hBk
          by_cases hkd : k ≤ d
          · have hcj : ∀ j ∈ range k, c j ∈ (Int.castRingHom ℚ).range := by
              intro j hj
              have hjk : j < k := Finset.mem_range.1 hj
              obtain ⟨z, hz⟩ := ih j hjk
              exact ⟨z, by simpa using (hz (by omega)).symm⟩
            have hsum : (∑ j ∈ range k, c j * (k.choose j : ℚ))
                ∈ (Int.castRingHom ℚ).range :=
              Subring.sum_mem _ fun j hj =>
                Subring.mul_mem _ (hcj j hj) ⟨(k.choose j : ℤ), by simp⟩
            have hPk : P.eval ((k : ℕ) : ℚ) ∈ (Int.castRingHom ℚ).range := by
              obtain ⟨z, hz⟩ := hint k
              exact ⟨z, by simpa using hz.symm⟩
            have hck : c k ∈ (Int.castRingHom ℚ).range := by
              have hrec : c k
                  = P.eval ((k : ℕ) : ℚ) - ∑ j ∈ range k, c j * (k.choose j : ℚ) := by
                rw [heval k hkd]; ring
              rw [hrec]
              exact Subring.sub_mem _ hPk hsum
            obtain ⟨z, hz⟩ := hck
            exact ⟨z, fun _ => by simpa using hz.symm⟩
          · exact ⟨0, fun hh => absurd hh hkd⟩
  have key' : ∀ k, ∃ z : ℤ, (k ≤ d → c k = (z : ℚ)) :=
    fun k => key (k + 1) k (Nat.lt_succ_self k)
  choose cz hcz using key'
  refine ⟨cz, ?_⟩
  rw [hc]
  exact Finset.sum_congr rfl fun k hk => by
    rw [hcz k (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))]

/-! ### (3.12)

`Zeta5.eq_3_12`, `v_p^G(F_K) ≥ -6h⌊log_p(5K)⌋ - h v_p(24)`, the output of Lemma 3.3, is
proved in `Zeta5/CrudeBound.lean` from (3.11) and Lemma 3.3. -/

/-- (5.1), first branch: for `pM ≤ K` the exponent `L_p(K,M)` is exactly the right-hand
side of (3.12).  A transcription check tying `Lp` to `eq_3_12`. -/
lemma Lp_small_eq (n M p : ℕ) (Alloc : InnerAllocFamily n M) (hpM : p * M ≤ K n) :
    Lp n M Alloc p
      = -6 * (h n : ℤ) * (Nat.log p (5 * K n) : ℤ) - (h n : ℤ) * (padicValNat p 24 : ℤ) := by
  rw [Lp, ite_eq_left_of_eq_true _ _ (eq_true hpM)]

/-! # §C. §3.1 (p. 6): von Staudt–Clausen

The paper writes, for `p ≥ 7` and `d ≥ 3`,

    κ_d = d(d-1)(d-2) B_{d-3} / 24,      κ_0 = κ_1 = κ_2 = 0,

and asserts: *"The von Staudt–Clausen theorem implies `v_p(κ_d) ≥ -1`.  Moreover `κ_d ∈ ℤ_p`
for `d ≤ p+1`."*  Mathlib has von Staudt–Clausen (`Bernoulli.vonStaudt_clausen`) together
with the exact valuation `v_p(B_{2k}) = -1` when `(p-1) ∣ 2k`; both assertions are derived
from it below. -/

lemma padicNorm_le_one_of_nonneg {p : ℕ} [hp : Fact p.Prime] {x : ℚ}
    (hx : 0 ≤ padicValRat p x) : padicNorm p x ≤ 1 := by
  rcases eq_or_ne x 0 with rfl | h0
  · simp
  · have hp1 : (1 : ℚ) < (p : ℚ) := by exact_mod_cast hp.out.one_lt
    rw [padicNorm.eq_zpow_of_nonzero h0, zpow_le_one_iff_right₀ hp1]
    linarith

lemma padicValRat_nonneg_of_padicNorm_le_one {p : ℕ} [hp : Fact p.Prime] {x : ℚ}
    (hx : padicNorm p x ≤ 1) : 0 ≤ padicValRat p x := by
  rcases eq_or_ne x 0 with rfl | h0
  · simp
  · have hp1 : (1 : ℚ) < (p : ℚ) := by exact_mod_cast hp.out.one_lt
    rw [padicNorm.eq_zpow_of_nonzero h0, zpow_le_one_iff_right₀ hp1] at hx
    linarith

lemma padicNorm_le_of_neg_one_le {p : ℕ} [hp : Fact p.Prime] {x : ℚ}
    (hx : -1 ≤ padicValRat p x) : padicNorm p x ≤ (p : ℚ) := by
  have hp1 : (1 : ℚ) < (p : ℚ) := by exact_mod_cast hp.out.one_lt
  rcases eq_or_ne x 0 with rfl | h0
  · simp
  · rw [padicNorm.eq_zpow_of_nonzero h0]
    calc (p : ℚ) ^ (-padicValRat p x) ≤ (p : ℚ) ^ (1 : ℤ) := by
          rw [zpow_le_zpow_iff_right₀ hp1]; linarith
      _ = (p : ℚ) := zpow_one _

lemma neg_one_le_padicValRat_of_padicNorm_le {p : ℕ} [hp : Fact p.Prime] {x : ℚ}
    (hx : padicNorm p x ≤ (p : ℚ)) : -1 ≤ padicValRat p x := by
  have hp1 : (1 : ℚ) < (p : ℚ) := by exact_mod_cast hp.out.one_lt
  rcases eq_or_ne x 0 with rfl | h0
  · simp
  · rw [padicNorm.eq_zpow_of_nonzero h0] at hx
    have hx' : (p : ℚ) ^ (-padicValRat p x) ≤ (p : ℚ) ^ (1 : ℤ) := by rwa [zpow_one]
    rw [zpow_le_zpow_iff_right₀ hp1] at hx'
    linarith

/-- `p` does not divide a prime `q ≠ p`, so `1/q` is a `p`-adic unit. -/
lemma padicNorm_one_div_prime {p q : ℕ} [hp : Fact p.Prime] (hq : q.Prime) (hne : p ≠ q) :
    padicNorm p ((1 : ℚ) / (q : ℚ)) = 1 := by
  have hnd : ¬ p ∣ q := (Nat.Prime.coprime_iff_not_dvd hp.out).1
    ((Nat.coprime_primes hp.out hq).2 hne)
  have hq1 : padicNorm p ((q : ℕ) : ℚ) = 1 := (padicNorm.nat_eq_one_iff q).2 hnd
  rw [padicNorm.div, padicNorm.one, hq1, div_one]

/-- **von Staudt–Clausen, the `p`-integral branch.**  If `p - 1 ∤ 2k` then `B_{2k} ∈ ℤ_p`.

Mathlib's `Bernoulli.vonStaudt_clausen` says `B_{2k} + ∑_{q prime, (q-1)|2k} 1/q ∈ ℤ`.
Under the hypothesis `p` is not one of those `q`, so every reciprocal in the sum is a
`p`-adic unit and `B_{2k}` is the difference of two `p`-integral rationals. -/
theorem padicValRat_bernoulli_nonneg (p : ℕ) [hp : Fact p.Prime] {k : ℕ}
    (hk : ¬ ((p - 1) ∣ 2 * k)) : 0 ≤ padicValRat p (_root_.bernoulli (2 * k)) := by
  obtain ⟨m, hm⟩ := Bernoulli.vonStaudt_clausen k
  set T : ℚ := ∑ q ∈ (range (2 * k + 2)).filter (fun q => q.Prime ∧ (q - 1) ∣ 2 * k),
      (1 : ℚ) / (q : ℚ) with hT
  have hB : _root_.bernoulli (2 * k) = ((m : ℤ) : ℚ) - T := by
    rw [hm]; ring
  have hTnorm : padicNorm p T ≤ 1 := by
    refine padicNorm.sum_le' (fun q hq => ?_) (by norm_num)
    obtain ⟨_, hq2, hq3⟩ := Finset.mem_filter.1 hq
    have hne : p ≠ q := by rintro rfl; exact hk hq3
    rw [padicNorm_one_div_prime hq2 hne]
  have hmnorm : padicNorm p ((m : ℤ) : ℚ) ≤ 1 := padicNorm.of_int m
  refine padicValRat_nonneg_of_padicNorm_le_one ?_
  rw [hB]
  exact le_trans padicNorm.sub (max_le hmnorm hTnorm)

/-- **von Staudt–Clausen**, in the form §3.1 quotes it (p. 6): `v_p(B_{2k}) ≥ -1`. -/
theorem neg_one_le_padicValRat_bernoulli (p : ℕ) [hp : Fact p.Prime] (k : ℕ) :
    -1 ≤ padicValRat p (_root_.bernoulli (2 * k)) := by
  by_cases hk : (p - 1) ∣ 2 * k
  · rcases Nat.eq_zero_or_pos k with rfl | hk0
    · norm_num [_root_.bernoulli_zero]
    · rw [Bernoulli.padicValRat_bernoulli hk0 hk]
  · exact le_trans (by norm_num) (padicValRat_bernoulli_nonneg p hk)

/-- `p ≥ 7` does not divide `2`. -/
lemma not_dvd_two {p : ℕ} (h7 : 7 ≤ p) : ¬ p ∣ 2 := fun hd => by
  have := Nat.le_of_dvd (by norm_num) hd
  omega

/-- `p ≥ 7` prime does not divide `24 = 2³·3`, so `v_p(24) = 0` — the second ingredient of
"`κ_d ∈ ℤ_p` for `d ≤ p+1`". -/
lemma not_dvd_24 {p : ℕ} (hp : p.Prime) (h7 : 7 ≤ p) : ¬ p ∣ 24 := by
  intro hd
  have hd' : p ∣ 8 * 3 := by norm_num at hd ⊢; exact hd
  rcases (Nat.Prime.dvd_mul hp).1 hd' with h | h
  · have h2 : p ∣ 2 := hp.dvd_of_dvd_pow (show p ∣ 2 ^ 3 by norm_num; exact h)
    have := Nat.le_of_dvd (by norm_num) h2
    omega
  · have := Nat.le_of_dvd (by norm_num) h
    omega

lemma padicNorm_24 {p : ℕ} [hp : Fact p.Prime] (h7 : 7 ≤ p) : padicNorm p (24 : ℚ) = 1 := by
  have hcast : ((24 : ℕ) : ℚ) = (24 : ℚ) := by norm_num
  rw [← hcast, padicNorm.nat_eq_one_iff]
  exact not_dvd_24 hp.out h7

lemma padicNorm_two {p : ℕ} [hp : Fact p.Prime] (h7 : 7 ≤ p) : padicNorm p (2 : ℚ) = 1 := by
  have hcast : ((2 : ℕ) : ℚ) = (2 : ℚ) := by norm_num
  rw [← hcast, padicNorm.nat_eq_one_iff]
  exact not_dvd_two h7

/-- `B_1 = -1/2` is a `p`-adic unit for `p ≥ 7`. -/
lemma padicNorm_bernoulli_one {p : ℕ} [hp : Fact p.Prime] (h7 : 7 ≤ p) :
    padicNorm p (_root_.bernoulli 1) = 1 := by
  rw [_root_.bernoulli_one, show (-1 : ℚ) / 2 = -(1 / 2) by ring, padicNorm.neg,
    padicNorm.div, padicNorm.one, padicNorm_two h7, div_one]

/-- An odd natural number is at least `1`. -/
lemma one_le_of_odd {m : ℕ} (ho : Odd m) : 1 ≤ m := by
  rcases Nat.eq_zero_or_pos m with rfl | hpos
  · simp [Nat.odd_iff] at ho
  · exact hpos

/-- `padicNorm p (B_m) ≤ p` for every `m`, when `p ≥ 7`: the three cases `m` even,
`m = 1`, and `m` odd `> 1` (where `B_m = 0`). -/
lemma padicNorm_bernoulli_le (p : ℕ) [hp : Fact p.Prime] (h7 : 7 ≤ p) (m : ℕ) :
    padicNorm p (_root_.bernoulli m) ≤ (p : ℚ) := by
  have hp1 : (1 : ℚ) < (p : ℚ) := by exact_mod_cast hp.out.one_lt
  rcases Nat.even_or_odd m with he | ho
  · obtain ⟨k, hk⟩ := he
    have hm2 : m = 2 * k := by omega
    subst hm2
    exact padicNorm_le_of_neg_one_le (neg_one_le_padicValRat_bernoulli p k)
  · rcases eq_or_lt_of_le (one_le_of_odd ho) with h1 | h1
    · rw [← h1, padicNorm_bernoulli_one h7]
      linarith
    · rw [_root_.bernoulli_eq_zero_of_odd ho h1, padicNorm.zero]
      linarith

/-- `padicNorm p (B_m) ≤ 1` when `m + 1 < p`, i.e. `m ≤ p - 2`: then `(p-1) ∤ m` unless
`m = 0`, so von Staudt–Clausen never produces a pole. -/
lemma padicNorm_bernoulli_le_one (p : ℕ) [hp : Fact p.Prime] (h7 : 7 ≤ p) {m : ℕ}
    (hm : m + 1 < p) : padicNorm p (_root_.bernoulli m) ≤ 1 := by
  rcases Nat.even_or_odd m with he | ho
  · obtain ⟨k, hk⟩ := he
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · have hm0 : m = 0 := by omega
      rw [hm0, _root_.bernoulli_zero, padicNorm.one]
    · have hnd : ¬ ((p - 1) ∣ 2 * k) := by
        intro hdvd
        have := Nat.le_of_dvd (by omega) hdvd
        omega
      have hm2 : m = 2 * k := by omega
      subst hm2
      exact padicNorm_le_one_of_nonneg (padicValRat_bernoulli_nonneg p hnd)
  · rcases eq_or_lt_of_le (one_le_of_odd ho) with h1 | h1
    · rw [← h1, padicNorm_bernoulli_one h7]
    · rw [_root_.bernoulli_eq_zero_of_odd ho h1, padicNorm.zero]
      norm_num

/-- §3.1, p. 6: `κ_d = d(d-1)(d-2) B_{d-3}/24` for `d ≥ 3`, and `κ_0 = κ_1 = κ_2 = 0`. -/
def kappa (d : ℕ) : ℚ :=
  if d < 3 then 0
  else ((d * (d - 1) * (d - 2) : ℕ) : ℚ) * _root_.bernoulli (d - 3) / 24

@[simp] lemma kappa_zero : kappa 0 = 0 := by simp [kappa]
@[simp] lemma kappa_one : kappa 1 = 0 := by simp [kappa]
@[simp] lemma kappa_two : kappa 2 = 0 := by simp [kappa]

/-- Known-answer control: `κ_3 = 3·2·1·B_0/24 = 1/4`. -/
lemma kappa_three : kappa 3 = 1 / 4 := by
  norm_num [kappa, _root_.bernoulli_zero]

/-- **§3.1, p. 6**: *"The von Staudt–Clausen theorem implies `v_p(κ_d) ≥ -1`."*
(For `p ≥ 7`, where `v_p(24) = 0`.) -/
theorem neg_one_le_padicValRat_kappa (p : ℕ) [hp : Fact p.Prime] (h7 : 7 ≤ p) (d : ℕ) :
    -1 ≤ padicValRat p (kappa d) := by
  refine neg_one_le_padicValRat_of_padicNorm_le ?_
  have hp0 : (0 : ℚ) ≤ (p : ℚ) := by positivity
  rw [kappa]
  split_ifs with hd
  · simp
  · rw [padicNorm.div, padicNorm.mul, padicNorm_24 h7, div_one]
    have h1 : padicNorm p (((d * (d - 1) * (d - 2) : ℕ) : ℚ)) ≤ 1 := padicNorm.of_nat _
    have h1' : 0 ≤ padicNorm p (((d * (d - 1) * (d - 2) : ℕ) : ℚ)) := padicNorm.nonneg _
    have h2 : padicNorm p (_root_.bernoulli (d - 3)) ≤ (p : ℚ) :=
      padicNorm_bernoulli_le p h7 _
    have h2' : 0 ≤ padicNorm p (_root_.bernoulli (d - 3)) := padicNorm.nonneg _
    nlinarith

/-- **§3.1, p. 6**: *"Moreover `κ_d ∈ ℤ_p` for `d ≤ p+1`."*

This is the degree restriction of Lemma 3.1 (`deg U_0 ≤ p+1`), the one that "prevents this
loss in the initial term" (p. 6).  The reason is that for `d ≤ p+1` the index `d-3` of the
Bernoulli number is at most `p-2 < p-1`, so `(p-1) ∤ (d-3)` unless `d = 3`, and von
Staudt–Clausen gives no pole. -/
theorem padicValRat_kappa_nonneg (p : ℕ) [hp : Fact p.Prime] (h7 : 7 ≤ p) {d : ℕ}
    (hd : d ≤ p + 1) : 0 ≤ padicValRat p (kappa d) := by
  refine padicValRat_nonneg_of_padicNorm_le_one ?_
  rw [kappa]
  split_ifs with hlt
  · simp
  · rw [padicNorm.div, padicNorm.mul, padicNorm_24 h7, div_one]
    have h1 : padicNorm p (((d * (d - 1) * (d - 2) : ℕ) : ℚ)) ≤ 1 := padicNorm.of_nat _
    have h1' : 0 ≤ padicNorm p (((d * (d - 1) * (d - 2) : ℕ) : ℚ)) := padicNorm.nonneg _
    have hm : (d - 3) + 1 < p := by omega
    have h2 : padicNorm p (_root_.bernoulli (d - 3)) ≤ 1 :=
      padicNorm_bernoulli_le_one p h7 hm
    have h2' : 0 ≤ padicNorm p (_root_.bernoulli (d - 3)) := padicNorm.nonneg _
    nlinarith

/-! # §D. The assembly of Theorem 2.1

The paper's "Proof of Theorem 2.1" (p. 21) combines five statements:

*  Proposition 5.1 — `Q_{K,M} ∈ ℤ[X]`;
*  (2.9)          — the leading coefficient of `Δ_K` is nonzero, hence `deg Δ_K = h`;
*  Proposition 2.2 — `Δ_K(ζ(5)) > 0`;
*  (5.21)          — `limsup K^{-2} log m_{K,M} ≤ A_M`;
*  Proposition 6.3, (6.16) — `log F_K(ζ(5)) ≤ U K² + 24K log K + 200K`.

Everything in this section is proved from those five, taken as hypotheses.  The only genuine
analytic content is `log_linear_le_quadratic`: `24K log K + 200K = o(K²)`. -/

/-! ### Inputs from `Zeta5/Asymptotics.lean`

`Q_{K,M}(ζ(5)) = m_{K,M}·F_K(ζ(5))` (`evalZeta5_Q`), the estimate `24x log x + 200x = o(x²)`
(`log_linear_le_quadratic`), (7.1) from its three inputs (`eq_7_1_of`) and (5.21) from
Proposition 5.2 (`eq_5_21_of_prop_5_2`) are in `Zeta5/Asymptotics.lean`, which imports only
`Basic.lean`, so that `Interface.lean` can use them.  `eq_7_1_of` is used below in
`theorem_2_1_of`. -/

/-- **(2.7)/(2.8) from (7.1)**, with (7.1) and the positivity of `Q_{K,M}(ζ(5))` as
hypotheses.  This is `Zeta5.decay_of_margin` with its input made explicit; `c` is the
exponent constant (`139/5` for (2.7), `7907/100` for (2.8)) and `hc` is (7.2). -/
theorem decay_of_margin_of (M : ℕ) (Alloc : ∀ n, InnerAllocFamily n M)
    (H71 : ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
        Real.log (evalZeta5 (Q n M (Alloc n)))
          ≤ ((AM M : ℝ) + (Ubar : ℝ) + ε) * (1600 * (n : ℝ) ^ 2))
    (HQpos : ∀ n : ℕ, 0 < evalZeta5 (Q n M (Alloc n)))
    (c : ℚ) (hc : c < -1600 * (AM M + Ubar)) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      evalZeta5 (Q n M (Alloc n)) < Real.exp (-(c : ℝ) * (n : ℝ) ^ 2) := by
  set b : ℝ := (AM M : ℝ) + (Ubar : ℝ) with hbdef
  have hb : 1600 * b < -(c : ℝ) := by
    have hr : ((c : ℚ) : ℝ) < ((-1600 * (AM M + Ubar) : ℚ) : ℝ) := by exact_mod_cast hc
    push_cast at hr
    rw [hbdef]
    linarith
  set ε : ℝ := (-(c : ℝ) - 1600 * b) / 3200 with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; linarith
  obtain ⟨n₁, hn₁⟩ := H71 ε hεpos
  refine ⟨max n₁ 1, fun n hn => ?_⟩
  have hna : n₁ ≤ n := le_trans (le_max_left _ _) hn
  have hnb : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnb
  have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 := by nlinarith
  have hQpos : 0 < evalZeta5 (Q n M (Alloc n)) := HQpos n
  have hlog := hn₁ n hna
  have hsum : (AM M : ℝ) + (Ubar : ℝ) + ε = b + ε := by rw [hbdef]
  rw [hsum] at hlog
  have hkey : (b + ε) * (1600 * (n : ℝ) ^ 2) < -(c : ℝ) * (n : ℝ) ^ 2 := by
    have h1 : 1600 * (b + ε) < -(c : ℝ) := by rw [hεdef]; linarith
    nlinarith
  have hlt := lt_of_le_of_lt hlog hkey
  calc evalZeta5 (Q n M (Alloc n))
      = Real.exp (Real.log (evalZeta5 (Q n M (Alloc n)))) := (Real.exp_log hQpos).symm
    _ < Real.exp (-(c : ℝ) * (n : ℝ) ^ 2) := Real.exp_lt_exp.2 hlt

/-- `deg Δ_K = h` from the nonvanishing of the leading coefficient (2.9) and the bound
`Delta_natDegree_le` of `Basic.lean`. -/
theorem Delta_natDegree_of {n : ℕ} (H29 : (Delta n).coeff (h n) ≠ 0) :
    (Delta n).natDegree = h n :=
  le_antisymm (Delta_natDegree_le n) (Polynomial.le_natDegree_of_ne_zero H29)

/-- `deg Q_{K,M} = h` from (2.9). -/
theorem Q_natDegree_of {n M : ℕ} (Alloc : InnerAllocFamily n M)
    (H29 : (Delta n).coeff (h n) ≠ 0) : (Q n M Alloc).natDegree = h n := by
  have hm : mKM n M Alloc ≠ 0 := ne_of_gt (mKM_pos n M Alloc)
  have hs : S n ≠ 0 := ne_of_gt (S_pos n)
  rw [Q, F, ← mul_assoc, ← map_mul, Polynomial.natDegree_C_mul (mul_ne_zero hm hs)]
  exact Delta_natDegree_of H29

/-- `F_K(ζ(5)) > 0` from `Δ_K(ζ(5)) > 0` (Proposition 2.2) and `S_K > 0`. -/
theorem F_pos_of {n : ℕ} (H22 : 0 < evalZeta5 (Delta n)) : 0 < evalZeta5 (F n) := by
  rw [F, evalZeta5_mul, evalZeta5_C]
  exact mul_pos (by exact_mod_cast S_pos n) H22

/-- `Q_{K,M}(ζ(5)) > 0` from Proposition 2.2. -/
theorem Q_pos_of {n M : ℕ} (Alloc : InnerAllocFamily n M) (H22 : 0 < evalZeta5 (Delta n)) :
    0 < evalZeta5 (Q n M Alloc) := by
  rw [Q, evalZeta5_mul, evalZeta5_C]
  exact mul_pos (by exact_mod_cast mKM_pos n M Alloc) (F_pos_of H22)

/-- **Theorem 2.1** (p. 4) at `M = 200`, in the form `Skeleton.lean` consumes, derived from
the paper's five inputs taken as hypotheses:

* `H51`  — Proposition 5.1, `Q_{K,200} ∈ ℤ[X]` for `K ≥ 200·200²`;
* `H29`  — (2.9), the leading coefficient of `Δ_K` is nonzero;
* `H22`  — Proposition 2.2, `Δ_K(ζ(5)) > 0`;
* `H521` — (5.21), `limsup K^{-2} log m_{K,200} ≤ A_200`;
* `H616` — Proposition 6.3, (6.16).

The margin (7.2) enters through `eq_7_2_M200`, proved in `Basic.lean`. -/
theorem theorem_2_1_of (Alloc : ∀ n, InnerAllocFamily n 200)
    (H51 : ∀ n : ℕ, 200 * 200 ^ 2 ≤ K n →
        ∃ P : Polynomial ℤ, P.map (Int.castRingHom ℚ) = Q n 200 (Alloc n))
    (H29 : ∀ n : ℕ, (Delta n).coeff (h n) ≠ 0)
    (H22 : ∀ n : ℕ, 0 < evalZeta5 (Delta n))
    (H521 : ∀ δ : ℝ, 0 < δ → ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
        Real.log (mKM n 200 (Alloc n)) ≤ ((AM 200 : ℝ) + δ) * (K n : ℝ) ^ 2)
    (H616 : ∀ n : ℕ, 0 < n → Real.log (evalZeta5 (F n))
        ≤ (Ubar : ℝ) * (K n : ℝ) ^ 2 + 24 * (K n : ℝ) * Real.log (K n : ℝ)
          + 200 * (K n : ℝ)) :
    Theorem_2_1 Alloc := by
  have hFpos : ∀ n : ℕ, 0 < evalZeta5 (F n) := fun n => F_pos_of (H22 n)
  have hQpos : ∀ n : ℕ, 0 < evalZeta5 (Q n 200 (Alloc n)) :=
    fun n => Q_pos_of (Alloc n) (H22 n)
  have H71 : ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      Real.log (evalZeta5 (Q n 200 (Alloc n)))
        ≤ ((AM 200 : ℝ) + (Ubar : ℝ) + ε) * (1600 * (n : ℝ) ^ 2) :=
    fun ε hε => eq_7_1_of 200 Alloc H521 H616 hFpos ε hε
  obtain ⟨n₁, hn₁⟩ := decay_of_margin_of 200 Alloc H71 hQpos (139 / 5)
    (by have := eq_7_2_M200; linarith)
  refine ⟨max n₁ 200000, fun n hn => ?_⟩
  have hna : n₁ ≤ n := le_trans (le_max_left _ _) hn
  have hnb : 200000 ≤ n := le_trans (le_max_right _ _) hn
  have hK : 200 * 200 ^ 2 ≤ K n := by simp only [K]; omega
  refine ⟨H51 n hK, Q_natDegree_of (Alloc n) (H29 n), hQpos n, ?_⟩
  simpa using hn₁ n hna

/-- **Theorem 1.1** from the same five inputs: `ζ(5)` is irrational.

This is the paper's argument with its five inputs made explicit as hypotheses. -/
theorem zeta5_irrational_of (Alloc : ∀ n, InnerAllocFamily n 200)
    (H51 : ∀ n : ℕ, 200 * 200 ^ 2 ≤ K n →
        ∃ P : Polynomial ℤ, P.map (Int.castRingHom ℚ) = Q n 200 (Alloc n))
    (H29 : ∀ n : ℕ, (Delta n).coeff (h n) ≠ 0)
    (H22 : ∀ n : ℕ, 0 < evalZeta5 (Delta n))
    (H521 : ∀ δ : ℝ, 0 < δ → ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
        Real.log (mKM n 200 (Alloc n)) ≤ ((AM 200 : ℝ) + δ) * (K n : ℝ) ^ 2)
    (H616 : ∀ n : ℕ, 0 < n → Real.log (evalZeta5 (F n))
        ≤ (Ubar : ℝ) * (K n : ℝ) ^ 2 + 24 * (K n : ℝ) * Real.log (K n : ℝ)
          + 200 * (K n : ℝ)) :
    Irrational zeta5 :=
  theorem_1_1 Alloc (theorem_2_1_of Alloc H51 H29 H22 H521 H616)

/-! # §E. (7.2): the final margin, as exact rational arithmetic

The whole proof turns on a margin of about 1.3 % between two constants of size about 1.36.
Everything here is an exact identity or inequality between the rational numbers the paper
prints, checked by `norm_num` on `ℚ`. -/

/-- `A_200`, exactly as printed in Appendix B.3 (p. 28). -/
def A200printed : ℚ := 127125602969131786927559 / 94195881588024216000000

/-- `A_100000`, in the corrected form (the audit found a digit dropped in B.3, p. 28). -/
def A100000printed : ℚ :=
  7756864096839411316755964319057 / 5887242599251513500000000000000

/-- **Known-answer control.**  `A_M` of (5.20), evaluated at `M = 200` from `A_*` of (5.19)
and `λ = 37/40`, is exactly the rational number printed in B.3. -/
theorem AM_200_eq : AM 200 = A200printed := by
  norm_num [AM, Astar, lam, A200printed]

/-- **Known-answer control** at `M = 100000` (what Corollary 1.2 uses). -/
theorem AM_100000_eq : AM 100000 = A100000printed := by
  norm_num [AM, Astar, lam, A100000printed]

/-- **(7.2), the inequality the whole paper turns on**, from the paper's printed exact
values: `A_200 + U < -139/8000`.

Multiplying by `-1600` this is `-1600(A_200 + U) > 139/5`, the exponent of (2.7).  Note
`139/8000 = 0.0173750` and `A_200 + U = -0.0174078…`: the margin is `1.29 %` of `|U|`. -/
theorem A200_add_Ubar_lt : A200printed + Ubar < -139 / 8000 := by
  norm_num [A200printed, Ubar]

/-- The exact value of `A_200 + U`. -/
theorem A200_add_Ubar_exact :
    A200printed + Ubar = -1639743280230170235469 / 94195881588024216000000 := by
  norm_num [A200printed, Ubar]

/-- The exact margin in (7.2) at `M = 200`:
`-1600(A_200 + U) - 139/5 = 3089837638249482469/58872425992515135000 ≈ 0.0524836`. -/
theorem margin_200_exact :
    -1600 * (A200printed + Ubar) - 139 / 5
      = 3089837638249482469 / 58872425992515135000 := by
  norm_num [A200printed, Ubar]

/-- The exact margin in (7.2) at `M = 100000` (Corollary 1.2):
`-1600(A_100000 + U) - 7907/100 = 29873543950273155160680943/3679526624532195937500000000`. -/
theorem margin_100000_exact :
    -1600 * (A100000printed + Ubar) - 7907 / 100
      = 29873543950273155160680943 / 3679526624532195937500000000 := by
  norm_num [A100000printed, Ubar]

/-! # Known-answer controls for this file

Facts computed by hand and re-derived by Lean from the definitions alone. -/

section Controls

/-- (2.1): `K 1 = 40`, so `legBound 1 2 = ⌊log_2 80⌋ + 1 = 7` (`2^6 = 64 ≤ 80 < 128`). -/
example : legBound 1 2 = 7 := by norm_num [legBound, K]

/-- `legBound 1 3 = ⌊log_3 80⌋ + 1 = 4` (`3^3 = 27 ≤ 80 < 81`). -/
example : legBound 1 3 = 4 := by norm_num [legBound, K]

/-- `C(X,0) = 1`, `deg C(X,1) = 1`, and `C(3,2) = 3`, `C(5,3) = 10`. -/
example : binomPoly 0 = 1 := binomPoly_zero
example : (binomPoly 1).natDegree = 1 := binomPoly_natDegree 1
example : (binomPoly 2).eval ((3 : ℕ) : ℚ) = 3 := by
  rw [binomPoly_eval_nat]; norm_num [Nat.choose]
example : (binomPoly 3).eval ((5 : ℕ) : ℚ) = 10 := by
  rw [binomPoly_eval_nat]; norm_num [Nat.choose]

/-- `C(X,k)` has leading coefficient `1/k!`; at `k = 3` that is `1/6`. -/
example : (binomPoly 3).coeff 3 = 1 / 6 := by
  rw [binomPoly_coeff_self]; norm_num [Nat.factorial]

/-- §3.1: `κ_3 = 3·2·1·B_0/24 = 1/4`. -/
example : kappa 3 = 1 / 4 := kappa_three

/-- §3.1: `κ_4 = 4·3·2·B_1/24 = -1/2` (with the paper's convention `B_1 = -1/2`). -/
example : kappa 4 = -1 / 2 := by
  norm_num [kappa, _root_.bernoulli_one]

/-- (5.20) at `M = 200` reproduces the value printed in B.3. -/
example : AM 200 = A200printed := AM_200_eq

/-- (7.2): the margin is positive. -/
example : A200printed + Ubar < -139 / 8000 := A200_add_Ubar_lt

end Controls

/-! # Axiom checks

The assembly theorems of §D are unconditional implications, with their five inputs explicit
as hypotheses. -/

#print axioms Zeta5.vS_eq
#print axioms Zeta5.integer_binom_coeffs
#print axioms Zeta5.exists_binom_expansion
#print axioms Zeta5.neg_one_le_padicValRat_bernoulli
#print axioms Zeta5.padicValRat_kappa_nonneg
#print axioms Zeta5.neg_one_le_padicValRat_kappa
#print axioms Zeta5.log_linear_le_quadratic
#print axioms Zeta5.eq_7_1_of
#print axioms Zeta5.theorem_2_1_of
#print axioms Zeta5.zeta5_irrational_of
#print axioms Zeta5.A200_add_Ubar_lt
#print axioms Zeta5.AM_200_eq
#print axioms Zeta5.Lp_small_eq

end

end Zeta5
