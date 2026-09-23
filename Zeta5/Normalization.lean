/-
Zeta5/Normalization.lean

Part of the Lean formalisation of

    A. Fauzan, "ζ(5) is irrational", 17 September 2026.

**PROPOSITION 5.1 (p. 14), THE STRUCTURAL KEYSTONE.**

    Proposition 5.1.  The polynomial `Q_{K,M} = m_{K,M} F_K` belongs to `ℤ[X]`.

    Proof.  At every prime `p ≤ 2h`, the assertion follows from (3.12) and Propositions
    4.1 and 4.3.  At `p > 2h`, all factorials in `S_K` are units, and `Δ_K` is integral by
    Proposition 4.3.  Thus every coefficient of `Q_{K,M}` is integral at every prime.  □

In the paper Proposition 5.1 is a *conclusion*, the output of §§3–5.1.  Before this file it
was **assumed** in `Interface.lean`, which made Propositions 4.1 and 4.3 and (3.12) orphans:
`Zeta5.zeta5_irrational` did not depend on them at all.  This file carries out the paper's
one-paragraph proof, so that `Interface.prop_5_1` is no longer a `sorry` and §§3–4 become
load-bearing.

WHAT IS PROVED HERE, with no `sorry`:

  §1  The Gauss valuation `v_p^G` of §3 (p. 5): monotonicity, its characterisation by
      `padicNorm`, `v_p^G(AB) ≥ v_p^G(A) + v_p^G(B)`, the exact rule for `C c · A`, and
      the integrality criterion "`v_p^G(A) ≥ 0` for every prime `p` ⟹ `A ∈ ℤ[X]`".
  §2  `v_p` of a finite product of rationals, and hence **`v_p(m_{K,M})`** exactly:
      `-L_p(K,M)` for `p ≤ 2h`, and `0` for `p > 2h`, from (5.2).
  §4  `v_p(S_K) = 0` for `p > 2h` — the paper's "all factorials in `S_K` are units".
  §5  **`prop_5_1_of`**: Proposition 5.1 from (3.12), Propositions 4.1, 4.3 and 4.3-large,
      taken as explicit hypotheses.  `Interface.prop_5_1` is this applied to the four.

WHAT WAS *MOVED* HERE AND HAS MOVED ON: **`eq_3_12`** — (3.12), the output of Lemma 3.3 —
was declared in `Arithmetic.lean`, then here; it now lives in `Zeta5/CrudeBound.lean`, where
it is proved rather than assumed.  See §3 below.

THIS FILE CONTAINS NO `sorry`.  (It used to contain exactly one, `eq_3_12`; that statement
now lives, proved, in `Zeta5/CrudeBound.lean` — see §3 below.)

CONVENTION (README): nothing here is proved by weakening a statement.  Every hypothesis of
`prop_5_1_of` is the verbatim statement of the paper result it stands for, as declared in
`Interface.lean`.
-/
import Zeta5.Basic

namespace Zeta5

open Polynomial Finset

noncomputable section

/-! # §1.  The Gauss valuation `v_p^G`

`v_p^G(A)` is the minimum of the `p`-adic valuations of the coefficients of `A` (p. 5), with
`v_p^G(0) = +∞`.  `Basic.vGAtLeast p A c` is the predicate `v_p^G(A) ≥ c`, which avoids `ℤ∞`
and is all that §§3–5 ever need. -/

/-- `v_p^G` is monotone: a lower bound may always be weakened. -/
theorem vGAtLeast.mono {p : ℕ} {A : ℚ[X]} {c c' : ℤ} (hA : vGAtLeast p A c) (hc : c' ≤ c) :
    vGAtLeast p A c' := fun i hi => le_trans hc (hA i hi)

/-- `v_p^G(A) ≥ c` says exactly that every coefficient of `A` has `p`-adic norm at most
`p^{-c}`.  The zero coefficients, excluded from `vGAtLeast` because `padicValRat p 0 = 0`
rather than `+∞`, are included here: `padicNorm p 0 = 0 ≤ p^{-c}`. -/
theorem vGAtLeast_iff_padicNorm {p : ℕ} [hp : Fact p.Prime] {A : ℚ[X]} {c : ℤ} :
    vGAtLeast p A c ↔ ∀ i, padicNorm p (A.coeff i) ≤ (p : ℚ) ^ (-c) := by
  have hp1 : (1 : ℚ) < (p : ℚ) := by exact_mod_cast hp.out.one_lt
  have hp0 : (0 : ℚ) < (p : ℚ) := lt_trans zero_lt_one hp1
  constructor
  · intro hA i
    rcases eq_or_ne (A.coeff i) 0 with h0 | h0
    · rw [h0, padicNorm.zero]
      positivity
    · rw [padicNorm.eq_zpow_of_nonzero h0, zpow_le_zpow_iff_right₀ hp1]
      exact neg_le_neg (hA i h0)
  · intro hA i h0
    have hi := hA i
    rw [padicNorm.eq_zpow_of_nonzero h0, zpow_le_zpow_iff_right₀ hp1] at hi
    linarith

/-- **`v_p^G(AB) ≥ v_p^G(A) + v_p^G(B)`.**  The coefficients of `AB` are sums of products of
coefficients of `A` and `B`; `padicNorm` is multiplicative and non-archimedean. -/
theorem vGAtLeast_mul {p : ℕ} [hp : Fact p.Prime] {A B : ℚ[X]} {a b : ℤ}
    (hA : vGAtLeast p A a) (hB : vGAtLeast p B b) : vGAtLeast p (A * B) (a + b) := by
  have hp1 : (1 : ℚ) < (p : ℚ) := by exact_mod_cast hp.out.one_lt
  have hp0 : (0 : ℚ) < (p : ℚ) := lt_trans zero_lt_one hp1
  rw [vGAtLeast_iff_padicNorm] at hA hB ⊢
  intro k
  rw [Polynomial.coeff_mul]
  refine padicNorm.sum_le' (fun ij _ => ?_) (by positivity)
  rw [padicNorm.mul]
  calc padicNorm p (A.coeff ij.1) * padicNorm p (B.coeff ij.2)
      ≤ (p : ℚ) ^ (-a) * (p : ℚ) ^ (-b) :=
        mul_le_mul (hA _) (hB _) (padicNorm.nonneg _) (by positivity)
    _ = (p : ℚ) ^ (-(a + b)) := by rw [← zpow_add₀ (ne_of_gt hp0)]; ring_nf

/-- The exact rule for a scalar multiple: `v_p^G(cA) = v_p(c) + v_p^G(A)` for `c ≠ 0`.
(Only `≥` is used below, but the proof gives equality coefficient by coefficient.) -/
theorem vGAtLeast_C_mul {p : ℕ} [hp : Fact p.Prime] {c : ℚ} (hc : c ≠ 0) {A : ℚ[X]} {a : ℤ}
    (hA : vGAtLeast p A a) : vGAtLeast p (C c * A) (padicValRat p c + a) := by
  intro i hi
  rw [Polynomial.coeff_C_mul] at hi ⊢
  have hAi : A.coeff i ≠ 0 := fun h0 => hi (by rw [h0, mul_zero])
  rw [padicValRat.mul hc hAi]
  have := hA i hAi
  omega

/-- A rational number that is `p`-integral at every prime is an integer.

If `q.den > 1`, pick a prime `p ∣ q.den`; then `p ∤ q.num` because `q` is in lowest terms,
so `v_p(q) = -v_p(q.den) ≤ -1 < 0`. -/
theorem isInt_of_forall_padicValRat_nonneg {q : ℚ}
    (hq : ∀ p : ℕ, p.Prime → 0 ≤ padicValRat p q) : ∃ z : ℤ, (z : ℚ) = q := by
  refine ⟨q.num, ?_⟩
  have hden : q.den = 1 := by
    by_contra hd
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hd
    have : Fact p.Prime := ⟨hp⟩
    have h1 : 1 ≤ padicValNat p q.den := one_le_padicValNat_of_dvd q.den_nz hpd
    have hnum : ¬ (p : ℤ) ∣ q.num := by
      intro hdv
      have hpn : p ∣ q.num.natAbs := by
        have hh := Int.natAbs_dvd_natAbs.mpr hdv
        simpa using hh
      have hg : Nat.gcd q.num.natAbs q.den = 1 := q.reduced
      have hp1 : p ∣ 1 := hg ▸ Nat.dvd_gcd hpn hpd
      have hle := Nat.le_of_dvd Nat.one_pos hp1
      have h2le := hp.two_le
      omega
    have h2 : padicValInt p q.num = 0 := padicValInt.eq_zero_of_not_dvd hnum
    have h3 := hq p hp
    rw [padicValRat_def, h2] at h3
    omega
  exact (Rat.den_eq_one_iff q).1 hden

/-- **The integrality criterion.**  `v_p^G(A) ≥ 0` at every prime `p` implies `A ∈ ℤ[X]`. -/
theorem exists_intPoly_of_vG {A : ℚ[X]} (hA : ∀ p : ℕ, p.Prime → vGAtLeast p A 0) :
    ∃ P : Polynomial ℤ, P.map (Int.castRingHom ℚ) = A := by
  refine (Polynomial.mem_lifts (f := Int.castRingHom ℚ) A).1
    ((Polynomial.lifts_iff_coeff_lifts (f := Int.castRingHom ℚ) A).2 fun i => ?_)
  rcases eq_or_ne (A.coeff i) 0 with h0 | h0
  · exact ⟨0, by simp [h0]⟩
  · obtain ⟨z, hz⟩ := isInt_of_forall_padicValRat_nonneg (fun p hp => hA p hp i h0)
    exact ⟨z, by simpa using hz⟩

/-! # §2.  `v_p` of a finite product, and `v_p(m_{K,M})` -/

/-- `v_p` of a finite product of nonzero rationals is the sum of the `v_p`. -/
theorem padicValRat_finsetProd {p : ℕ} [Fact p.Prime] (s : Finset ℕ) (f : ℕ → ℚ) :
    (∀ i ∈ s, f i ≠ 0) →
      padicValRat p (∏ i ∈ s, f i) = ∑ i ∈ s, padicValRat p (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      intro hf
      rw [Finset.prod_insert ha, Finset.sum_insert ha,
        padicValRat.mul (hf a (Finset.mem_insert_self a s))
          (Finset.prod_ne_zero_iff.2 fun i hi => hf i (Finset.mem_insert_of_mem hi)),
        ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

/-- `v_p(q) = 0` for a prime `q ≠ p`. -/
theorem padicValRat_prime_ne {p q : ℕ} [Fact p.Prime] (hq : q.Prime) (hne : q ≠ p) :
    padicValRat p ((q : ℕ) : ℚ) = 0 := by
  rw [padicValRat.of_nat]
  have hz : padicValNat p q = 0 := by
    refine padicValNat.eq_zero_of_not_dvd fun hd => hne ?_
    exact ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) hq).1 hd).symm
  rw [hz]
  rfl

/-- **`v_p(m_{K,M})`, from (5.2)** (p. 13): `m_{K,M} = ∏_{p ≤ 2h} p^{-L_p(K,M)}`, so its
`p`-adic valuation is `-L_p(K,M)` when `p ≤ 2h`, and `0` otherwise. -/
theorem padicValRat_mKM (n M p : ℕ) (hp : p.Prime) (Alloc : InnerAllocFamily n M) :
    padicValRat p (mKM n M Alloc) = if p ≤ 2 * h n then -(Lp n M Alloc p) else 0 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hne : ∀ q ∈ (range (2 * h n + 1)).filter Nat.Prime,
      ((q : ℚ) ^ (-(Lp n M Alloc q)) : ℚ) ≠ 0 := by
    intro q hq
    have hq' : Nat.Prime q := (Finset.mem_filter.1 hq).2
    exact zpow_ne_zero _ (Nat.cast_ne_zero.2 hq'.pos.ne')
  have hterm : ∀ q ∈ (range (2 * h n + 1)).filter Nat.Prime,
      padicValRat p ((q : ℚ) ^ (-(Lp n M Alloc q)))
        = if q = p then -(Lp n M Alloc p) else 0 := by
    intro q hq
    have hq' : Nat.Prime q := (Finset.mem_filter.1 hq).2
    rw [padicValRat.zpow]
    by_cases hqp : q = p
    · subst hqp
      simp [padicValRat.self hq'.one_lt]
    · simp [hqp, padicValRat_prime_ne hq' hqp]
  rw [mKM, padicValRat_finsetProd ((range (2 * h n + 1)).filter Nat.Prime)
        (fun q => ((q : ℚ) ^ (-(Lp n M Alloc q)))) hne,
    Finset.sum_congr rfl hterm]
  simp only [Finset.sum_ite_eq']
  by_cases hple : p ≤ 2 * h n
  · have hmem : p ∈ (range (2 * h n + 1)).filter Nat.Prime :=
      Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), hp⟩
    simp [hmem, hple]
  · have hmem : p ∉ (range (2 * h n + 1)).filter Nat.Prime := by
      intro hmem
      have hr := Finset.mem_range.1 (Finset.mem_filter.1 hmem).1
      omega
    simp [hmem, hple]

/-! # §3.  (3.12) has MOVED to `Zeta5/CrudeBound.lean`

`Zeta5.eq_3_12` — `v_p^G(F_K) ≥ -6h⌊log_p 5K⌋ - h v_p(24)`, the output of Lemma 3.3 — used
to be declared here, as a `sorry`, because `prop_5_1_of` needs it and `Arithmetic.lean`
(where it first stood) sits *below* `Interface.lean`.  It is now **proved**, from (3.11) and
Lemma 3.3, in `Zeta5/CrudeBound.lean`, which sits between `Section3.lean` and
`Interface.lean`: the proof needs `τ`, `τ^ext` and the pullback identity (3.1), all of which
are declared in `Section3.lean`, i.e. *below* this file.  The statement is unchanged, and
still carries the name `Zeta5.eq_3_12`; `Interface.prop_5_1` consumes it exactly as before.

`prop_5_1_of` below is unaffected: it takes (3.12) as the explicit hypothesis `H312`. -/

/-! # §4.  `v_p(S_K) = 0` for `p > 2h`

The paper's "At `p > 2h`, all factorials in `S_K` are units".  Every factorial occurring in
(2.5) has argument `K = 40n`, `N = 3n` or `2i ≤ 2h - 2`, all `< 2h < p`; and `p > 2h ≥ 74`
does not divide the remaining factor `4^{h-1}`. -/

/-- `v_p(m!) = 0` when `m < p`: the paper's "all factorials in `S_K` are units". -/
theorem padicValRat_factorial_eq_zero {p m : ℕ} (hp : p.Prime) (hm : m < p) :
    padicValRat p ((m.factorial : ℕ) : ℚ) = 0 := by
  have : Fact p.Prime := ⟨hp⟩
  rw [padicValRat.of_nat]
  have hz : padicValNat p (m.factorial) = 0 :=
    padicValNat.eq_zero_of_not_dvd fun hd => absurd (hp.dvd_factorial.mp hd) (by omega)
  rw [hz]
  rfl

/-- **`v_p(S_K) = 0` for `p > 2h`** (p. 14, second sentence of the proof of Proposition 5.1).
`S_K` of (2.5) is built from `K!`, `N!`, the `(2i)!` with `i ≤ h-1`, and `4^{h-1}`; for
`p > 2h = 74n` every one of them is a `p`-adic unit. -/
theorem vS_eq_zero_of_two_h_lt (n p : ℕ) (hp : p.Prime) (hn : 0 < n) (h2h : 2 * h n < p) :
    vS n p = 0 := by
  have : Fact p.Prime := ⟨hp⟩
  have h2h' : 2 * (37 * n) < p := by simpa [h] using h2h
  have hKp : K n < p := by simp only [K]; omega
  have hNp : N n < p := by simp only [N]; omega
  have hfacne : ∀ m : ℕ, ((m.factorial : ℕ) : ℚ) ≠ 0 := fun m =>
    Nat.cast_ne_zero.2 (Nat.factorial_ne_zero m)
  have hfacK : padicValRat p (((K n).factorial : ℕ) : ℚ) = 0 :=
    padicValRat_factorial_eq_zero hp hKp
  have hfacN : padicValRat p (((N n).factorial : ℕ) : ℚ) = 0 :=
    padicValRat_factorial_eq_zero hp hNp
  have hfac4 : padicValRat p (4 : ℚ) = 0 := by
    have hc : ((4 : ℕ) : ℚ) = (4 : ℚ) := by norm_num
    rw [← hc, padicValRat.of_nat]
    have hz : padicValNat p 4 = 0 := by
      refine padicValNat.eq_zero_of_not_dvd fun hd => ?_
      have hle := Nat.le_of_dvd (by norm_num) hd
      omega
    rw [hz]
    rfl
  have hprodne : (∏ i ∈ Icc 1 (h n - 1), (((2 * i).factorial : ℕ) : ℚ) ^ 2) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (hfacne _)
  have hprod :
      padicValRat p (∏ i ∈ Icc 1 (h n - 1), (((2 * i).factorial : ℕ) : ℚ) ^ 2) = 0 := by
    rw [padicValRat_finsetProd (Icc 1 (h n - 1))
      (fun i => (((2 * i).factorial : ℕ) : ℚ) ^ 2) (fun i _ => pow_ne_zero _ (hfacne _))]
    refine Finset.sum_eq_zero fun i hi => ?_
    have hi2 : i ≤ h n - 1 := (Finset.mem_Icc.1 hi).2
    have hi1 : 1 ≤ i := (Finset.mem_Icc.1 hi).1
    have hi' : 2 * i < p := by simp only [h] at hi2; omega
    rw [padicValRat.pow, padicValRat_factorial_eq_zero hp hi', mul_zero]
  have hnum0 : (((K n).factorial : ℕ) : ℚ) ^ (2 * h n) * (4 : ℚ) ^ (h n - 1) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (hfacne _)) (pow_ne_zero _ (by norm_num))
  have hden0 : (((N n).factorial : ℕ) : ℚ) ^ (12 * h n)
      * (∏ i ∈ Icc 1 (h n - 1), (((2 * i).factorial : ℕ) : ℚ) ^ 2) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (hfacne _)) hprodne
  rw [vS, S, padicValRat.div hnum0 hden0,
    padicValRat.mul (pow_ne_zero _ (hfacne _)) (pow_ne_zero _ (by norm_num : (4 : ℚ) ≠ 0)),
    padicValRat.mul (pow_ne_zero _ (hfacne _)) hprodne]
  simp only [padicValRat.pow, hfacK, hfacN, hfac4, hprod, mul_zero, add_zero, sub_self]

/-! # §5.  Proposition 5.1

`Q_{K,M} = m_{K,M} F_K` with `F_K = S_K Δ_K` (2.5)–(2.6).  At a prime `p`,

    v_p^G(Q_{K,M}) = v_p(m_{K,M}) + v_p^G(F_K),

and `v_p(m_{K,M}) = -L_p(K,M)` for `p ≤ 2h`, `= 0` for `p > 2h` (`padicValRat_mKM`).  So the
claim is `v_p^G(F_K) ≥ L_p(K,M)` for `p ≤ 2h` and `v_p^G(F_K) ≥ 0` for `p > 2h`, branch by
branch of (5.1):

| branch of (5.1)     | `L_p(K,M)`                  | what clears it                   |
|---------------------|-----------------------------|----------------------------------|
| `pM ≤ K`            | `-6h⌊log_p 5K⌋ - h v_p(24)` | (3.12), **about `F_K` itself**   |
| `pM > K`, `3p ≤ K`  | `v_p(S_K) + γ_p^in`         | Proposition 4.1 (× `C S_K`)      |
| `3p > K`, `p ≤ K`   | `v_p(S_K) + γ_p^out`        | Proposition 4.3 (× `C S_K`)      |
| `3p > K`, `p > K`   | `v_p(S_K) + 0`              | Proposition 4.3, 2nd assertion   |
| `p > 2h`            | (not in the product)        | `v_p(S_K) = 0` and Prop. 4.3     |

THE POINT THE AUDIT FLAGS.  The first branch is a statement about `F_K`, not about `Δ_K`,
and it correctly *omits* `v_p(S_K)`: (3.12) already bounds `v_p^G(F_K) = v_p(S_K) +
v_p^G(Δ_K)` as a whole.  Adding `v_p(S_K)` there would be a double count.  The formalisation
below keeps the asymmetry exactly as the paper has it: `H312` is applied to `F n`, the other
three to `Delta n` and then multiplied by `C (S n)`. -/

/-- The hypotheses of (4.9) that do not mention `p ≤ K`, for an outer prime `3p > K`.

From `K = 40n`, `N = 3n` and `K ≥ 200M² ≥ 320000` (so `n ≥ 8000`) one gets `p ≥ 13n + 1`,
whence `p ≥ 7`, `p² > 2K`, `2N < p` and `5N ≤ 2p - 2`. -/
theorem outer_hypotheses {n p : ℕ} (hn : 8000 ≤ n) (h3p : K n < 3 * p) :
    7 ≤ p ∧ 2 * K n < p ^ 2 ∧ 2 * N n < p ∧ 5 * N n ≤ 2 * p - 2 := by
  have h3p' : 40 * n < 3 * p := by simpa [K] using h3p
  have hp13 : 13 * n + 1 ≤ p := by omega
  have hmul : (13 * n + 1) * (13 * n + 1) ≤ p * p := Nat.mul_le_mul hp13 hp13
  have hnn : 8000 * n ≤ n * n := Nat.mul_le_mul hn (le_refl n)
  refine ⟨by omega, ?_, by simp only [N]; omega, by simp only [N]; omega⟩
  simp only [K]
  rw [pow_two]
  nlinarith [hmul, hnn, hn]

/-- **Proposition 5.1** (p. 14), from its four inputs taken as explicit hypotheses, each the
verbatim statement of the corresponding declaration in `Interface.lean`:

* `H312` — (3.12), `v_p^G(F_K) ≥ -6h⌊log_p 5K⌋ - h v_p(24)`, at every prime;
* `H41`  — Proposition 4.1, `v_p^G(Δ_K) ≥ γ_p^in` at every inner prime, for any allocation;
* `H43`  — Proposition 4.3, first assertion, `v_p^G(Δ_K) ≥ γ_p^out` under (4.9);
* `H43L` — Proposition 4.3, second assertion, `v_p^G(Δ_K) ≥ 0` for `p > K`.

The proof is the paper's paragraph, made prime-by-prime explicit. -/
theorem prop_5_1_of (n M : ℕ) (hM : 40 ≤ M) (hK : 200 * M ^ 2 ≤ K n)
    (Alloc : InnerAllocFamily n M)
    (H312 : ∀ p : ℕ, p.Prime → vGAtLeast p (F n)
        (-6 * (h n : ℤ) * (Nat.log p (5 * K n) : ℤ) - (h n : ℤ) * (padicValNat p 24 : ℤ)))
    (H41 : ∀ (p : ℕ) (_hp : IsInnerPrime n M p) (A : InnerAlloc n M p),
        vGAtLeast p (Delta n) A.gammaIn)
    (H43 : ∀ p : ℕ, p.Prime → 7 ≤ p → p ≤ K n → K n < 3 * p → 2 * K n < p ^ 2 →
        2 * N n < p → 5 * N n ≤ 2 * p - 2 → vGAtLeast p (Delta n) (gammaOut n p))
    (H43L : ∀ p : ℕ, p.Prime → K n < p → vGAtLeast p (Delta n) 0) :
    ∃ P : Polynomial ℤ, P.map (Int.castRingHom ℚ) = Q n M Alloc := by
  -- (4.1) forces `K ≥ 200·40² = 320000`, i.e. `n ≥ 8000`.
  have hMsq : 200 * 40 ^ 2 ≤ 200 * M ^ 2 :=
    Nat.mul_le_mul (le_refl 200) (Nat.pow_le_pow_left hM 2)
  have hn8000 : 8000 ≤ n := by
    have h1 : (320000 : ℕ) ≤ 40 * n := by simpa [K] using le_trans hMsq hK
    omega
  have hn : 0 < n := by omega
  have hSne : S n ≠ 0 := ne_of_gt (S_pos n)
  have hmne : mKM n M Alloc ≠ 0 := ne_of_gt (mKM_pos n M Alloc)
  refine exists_intPoly_of_vG fun p hp => ?_
  have : Fact p.Prime := ⟨hp⟩
  have hm := padicValRat_mKM n M p hp Alloc
  by_cases hple : p ≤ 2 * h n
  · -- `p ≤ 2h`: the three branches of (5.1).
    have hF : vGAtLeast p (F n) (Lp n M Alloc p) := by
      rw [Lp]
      split_ifs with h1 h2
      · -- `pM ≤ K`: (3.12), about `F_K` itself, with no `v_p(S_K)`.
        exact H312 p hp
      · -- `pM > K`, `3p ≤ K`: Proposition 4.1.
        exact vGAtLeast_C_mul hSne (H41 p h2 (Alloc p h2))
      · -- `3p > K`: Proposition 4.3.
        have hlow : K n < p * M := by omega
        have h3p : K n < 3 * p := by
          by_contra hcon
          exact h2 ⟨hp, hM, hK, hlow, by omega⟩
        by_cases hpK : K n < p
        · have hout : gammaOut n p = 0 := by simp [gammaOut, hpK]
          rw [hout]
          exact vGAtLeast_C_mul hSne (H43L p hp hpK)
        · rw [Nat.not_lt] at hpK
          obtain ⟨h7, hp2, hN2, hN5⟩ := outer_hypotheses hn8000 h3p
          exact vGAtLeast_C_mul hSne (H43 p hp h7 hpK h3p hp2 hN2 hN5)
    refine (vGAtLeast_C_mul hmne hF).mono ?_
    rw [hm]
    simp only [hple, reduceIte]
    omega
  · -- `p > 2h`: all factorials in `S_K` are units, and `p > K`, so Proposition 4.3 applies.
    rw [Nat.not_le] at hple
    have hvS : padicValRat p (S n) = 0 := vS_eq_zero_of_two_h_lt n p hp hn hple
    have hpK : K n < p := by
      have h2h' : 2 * (37 * n) < p := by simpa [h] using hple
      simp only [K]
      omega
    have hF : vGAtLeast p (F n) 0 := by
      have hh := vGAtLeast_C_mul hSne (H43L p hp hpK)
      rw [hvS, zero_add] at hh
      exact hh
    refine (vGAtLeast_C_mul hmne hF).mono ?_
    rw [hm]
    simp only [show ¬ p ≤ 2 * h n from by omega, reduceIte]
    omega

/-! # Known-answer controls for this file

Facts computed by hand and re-derived by Lean from the definitions alone. -/

section Controls

/-- The smallest parameters allowed by (4.1) with `M = 40`: `K = 320000`, `N = 24000`,
`h = 296000`, and the smallest integer `p` with `3p > K` is `106667`.  The four conditions
of (4.9) that `outer_hypotheses` produces then read `7 ≤ 106667`,
`640000 < 106667² = 11377848889`, `48000 < 106667` and `120000 ≤ 213332`. -/
example : 7 ≤ 106667 ∧ 2 * K 8000 < 106667 ^ 2 ∧ 2 * N 8000 < 106667
    ∧ 5 * N 8000 ≤ 2 * 106667 - 2 :=
  outer_hypotheses (le_refl 8000) (by norm_num [K])

/-- The same four numbers, computed directly rather than through `outer_hypotheses`:
a control on `outer_hypotheses` itself. -/
example : K 8000 = 320000 ∧ N 8000 = 24000 ∧ h 8000 = 296000 ∧ 2 * h 8000 = 592000 := by
  norm_num [K, N, h]

/-- Control on `padicValRat_mKM`: above `2h` the factor `m_{K,M}` is a `p`-adic unit,
because the product (5.2) runs only over `p ≤ 2h`. -/
example (n M p : ℕ) (hp : p.Prime) (Alloc : InnerAllocFamily n M) (hple : 2 * h n < p) :
    padicValRat p (mKM n M Alloc) = 0 := by
  rw [padicValRat_mKM n M p hp Alloc]
  simp only [show ¬ p ≤ 2 * h n from by omega, reduceIte]

/-- Control on `isInt_of_forall_padicValRat_nonneg` in the direction it is used: a rational
that is `p`-integral at every prime really is an integer.  Contrapositive check at `1/6`,
whose `3`-adic valuation is `-1`. -/
example : padicValRat 3 (1 / 6 : ℚ) < 0 := by
  have h3 : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have h6 : ((6 : ℕ) : ℚ) = (6 : ℚ) := by norm_num
  rw [padicValRat.div one_ne_zero (by norm_num), padicValRat.one, ← h6, padicValRat.of_nat]
  have : padicValNat 3 6 = 1 := by decide +kernel
  rw [this]
  norm_num

end Controls

/-! # `#print axioms`: what is actually proved in this file

Everything here — including `prop_5_1_of`, the whole content of Proposition 5.1 — depends on
no `sorryAx`.  `prop_5_1_of` is an unconditional implication: its four paper
inputs are explicit hypotheses. -/

#print axioms Zeta5.prop_5_1_of
#print axioms Zeta5.exists_intPoly_of_vG
#print axioms Zeta5.isInt_of_forall_padicValRat_nonneg
#print axioms Zeta5.vGAtLeast_mul
#print axioms Zeta5.vGAtLeast_C_mul
#print axioms Zeta5.padicValRat_mKM
#print axioms Zeta5.vS_eq_zero_of_two_h_lt
#print axioms Zeta5.outer_hypotheses

end

end Zeta5
