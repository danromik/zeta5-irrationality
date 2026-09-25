/-
Zeta5/Section3.lean

Part of the Lean formalisation of

    A. Fauzan, "ζ(5) is irrational", 17 September 2026.

**SECTION 3 OF THE PAPER**: the local rational functional.

The paper's §3 produces the entry bound that Proposition 4.1 consumes.  §§A–E of the list
below are in `Zeta5/LocalFunctional.lean`, so that `Zeta5/InnerTate.lean`,
`Zeta5/InnerGeneral.lean` and `Zeta5/InnerEntries.lean` can use them; §§F–G are in this file.

Contents, in the paper's order:

  §A  p. 5      the functional `L` (`Lfun`) with `L(x^k) = B_k`, and `τ(P) = L(P''')/24`.
  §B  p. 6      `τ(x^d) = κ_d`, and the identities **(3.2)** (reflection) and **(3.3)**
                (difference) — proved from Mathlib's `sum_bernoulli` and
                `bernoulli_eq_zero_of_odd`, so DLMF (24.4.1)/(24.4.3) are NOT assumed.
  §C  p. 5–7    `d(r)`, the pole values `τ_X(1/(x-r)) = H^{(5)}_{d(r)} - X`, and the
                extension `τ^ext_Y` to `𝓑_T` (`tauExt`, `tauExtOf`).
  §D  p. 6      the pullback identity **(3.1)** `μ_X(R) = τ_X(x⁵R(-x²))`, proved exactly
                — both for monomials (2.2) and at the poles (2.3), together with the
                displayed partial fraction of p. 6.
  §E  p. 6      **Lemma 3.1** (3.4), proved: the division algorithm over `ℤ_p`, the residues
                `c_ν = R(r_ν)/T'(r_ν)`, the integrality of `H^{(5)}_{d(r_ν)}` and of
                `τ(P_0)` for `deg P_0 ≤ p+1`, and the `p^j` absorption for `j ≥ 1`.
                See the SCOPE NOTE there: the statement is proved for every partial sum
                `∑_{j ≤ J} p^j U_j`, uniformly in `J`; only the passage to the limit in
                the Tate algebra `ℚ_p⟨z⟩` is not formalised.
  §F  p. 7      **Lemma 3.2** (3.7), the distribution formula — why it is not stated as an
                equation here, and what of it §4 actually uses.
  §G  pp. 10–11 the per-entry valuation bounds **(4.2)** and **(4.3)**, DERIVED from
                Lemma 3.1; the verification that Lemma 3.1's hypotheses really hold for
                §4's data (near poles, harmonic indices, both degrees `≤ p+1`); two
                proved ingredients of the unimodularity sentence (pairwise coprimality
                of the `t + c²` mod `p`, and `deg E_{a,i} < h`); and **Proposition 4.1**.

§4's bookkeeping, `Section3.entry_bounds_4_2_4_3` (the Gram matrix in the basis (4.5) has
the entry bounds Lemmas 3.1/3.2 give, and the basis change is unimodular), is proved in
`Zeta5/InnerEntries.lean`, with `Zeta5/InnerTate.lean` and `Zeta5/InnerGeneral.lean`.
-/
import Zeta5.LocalFunctional
import Zeta5.HermiteBasis
import Zeta5.InnerEntries

namespace Zeta5

open Polynomial Finset

noncomputable section

/-! # §F.  Lemma 3.2 (p. 7): the distribution formula

> **Lemma 3.2.**  For every rational function `g` with polynomial part and simple integer
> poles, `τ_X(g) = p^{-4} ∑_{a=0}^{p-1} τ^ext_Y(g(a+px))`.                       (3.7)
> Integer poles on the right use `τ_Y`, and far poles use (3.5).

with `Y = p⁵X + C_p`, `C_p = ∑_{a=1}^{p-1} τ^an(1/(x + a/p)) ∈ p⁵ℤ_p` of (3.6).

WHAT IS AND IS NOT HERE.  (3.7) is an identity between values of `τ` on the Tate algebra
`𝓐 = ℚ_p⟨z⟩`: its right-hand side evaluates the *far* poles `a/p` by the convergent
series (3.5), an object that exists only in `𝓐`.  Neither `𝓐` nor `C_p` is formalised, so
(3.7) is not stated here as an equation.  What §4 actually uses from it is only the shape
of its summands, and that is exactly what `eq_4_2_of_lemma_3_1` and `eq_4_3_of_lemma_3_1`
below take as their hypothesis `hshape` and convert into the printed exponents of (4.2)
and (4.3).  The three ingredients of Lemma 3.2's own proof that are purely algebraic —
the reflection (3.2), the difference identity (3.3), and `τ(z^d) = κ_d` — are proved in
§B (`Zeta5/LocalFunctional.lean`); Raabe's multiplication theorem (DLMF 24.4.18), which
supplies the exponent `p^{-4}`, is not in Mathlib for `ℚ[X]` and is proved in `Zeta5/InnerTate.lean`
(`InnerEntries.raabe_tau`: `p⁴τ(P) = ∑_{a<p} τ(P(a+pz))`, from `sum_bernoulli`).
The use §4 makes of (3.7) is proved without the Tate algebra:
`InnerEntries.general_bound` (in `InnerGeneral.lean`) gives the valuation bound that (3.7)
together with Lemma 3.1 yields for a whole summand, by exact finite identities. -/

/-! # §G.  The per-entry valuation bounds (4.2), (4.3) (p. 10), and Proposition 4.1 -/

namespace Section3

open Polynomial

/-- **(4.2)** (p. 10), DERIVED FROM LEMMA 3.1.

> "If a row polynomial has a zero of order `ν_i(a)` at `t = -a²`, substitution `x = c + pz`
> in (3.1), for `c = a, p-a`, gives `ν_i(a) + ν_j(a) + 6ℓ_N(a) - ℓ_K(a) - 4` as a lower
> valuation for that summand of (3.7)."

`hshape` is the sentence "substitution `x = c + pz` in (3.1) … gives": after the indicated
power of `p` is extracted, what is left is `τ^ext_Y` of a rational function of the form
Lemma 3.1 applies to — the paper checks its hypotheses on p. 11 ("every near denominator
factor supplies a factor `p` and a simple integer pole in `z`; near poles have absolute
sizes at most `M+1`, and distinct near poles differ by a `p`-adic unit; their harmonic
indices are less than `p`; far factors are units times convergent series in `pz`",
and "Both degrees are at most `p+1`").  The conclusion is the printed exponent, with no
slack anywhere: the `-4` is exactly the `p^{-4}` of (3.7) and the `0` of (3.4). -/
theorem eq_4_2_of_lemma_3_1 {p : ℕ} [Fact p.Prime] (h7 : 7 ≤ p) {s : Finset ℤ}
    (hunit : ∀ r ∈ s, ∀ q ∈ s, r ≠ q → ¬ ((p : ℤ) ∣ (r - q)))
    (hd : ∀ r ∈ s, dIdx r < p)
    {Y : ℚ[X]} (hY : vGAtLeast p Y 0)
    (J : ℕ) (U : ℕ → ℚ[X]) (hU : ∀ j, vGAtLeast p (U j) 0) (hU0 : (U 0).natDegree ≤ p + 1)
    (nui nuj lN lK : ℕ) (summand : ℚ[X])
    (hshape : summand
        = C ((p : ℚ) ^ ((nui : ℤ) + (nuj : ℤ) + 6 * (lN : ℤ) - (lK : ℤ) - 4))
            * tauExtOf Y s (∑ j ∈ Finset.range (J + 1), C ((p : ℚ) ^ j) * U j)) :
    vGAtLeast p summand ((nui : ℤ) + (nuj : ℤ) + 6 * (lN : ℤ) - (lK : ℤ) - 4) := by
  rw [hshape]
  exact vGAtLeast_zpow_mul (lemma_3_1 h7 hunit hd hY J U hU hU0)

/-- **(4.3)** (p. 10), DERIVED FROM LEMMA 3.1.

> "At `c = 0` the corresponding bound is `2ν_i(0) + 2ν_j(0) + 12m_N - 2m_K + 1`."

Same derivation as (4.2); only the extracted power of `p` differs, because at the zero
class both `±a` collapse and the denominators are counted by `m_N`, `m_K` instead of
`ℓ_N`, `ℓ_K`. -/
theorem eq_4_3_of_lemma_3_1 {p : ℕ} [Fact p.Prime] (h7 : 7 ≤ p) {s : Finset ℤ}
    (hunit : ∀ r ∈ s, ∀ q ∈ s, r ≠ q → ¬ ((p : ℤ) ∣ (r - q)))
    (hd : ∀ r ∈ s, dIdx r < p)
    {Y : ℚ[X]} (hY : vGAtLeast p Y 0)
    (J : ℕ) (U : ℕ → ℚ[X]) (hU : ∀ j, vGAtLeast p (U j) 0) (hU0 : (U 0).natDegree ≤ p + 1)
    (nui nuj mN mK : ℕ) (summand : ℚ[X])
    (hshape : summand
        = C ((p : ℚ) ^ (2 * (nui : ℤ) + 2 * (nuj : ℤ) + 12 * (mN : ℤ) - 2 * (mK : ℤ) + 1))
            * tauExtOf Y s (∑ j ∈ Finset.range (J + 1), C ((p : ℚ) ^ j) * U j)) :
    vGAtLeast p summand
      (2 * (nui : ℤ) + 2 * (nuj : ℤ) + 12 * (mN : ℤ) - 2 * (mK : ℤ) + 1) := by
  rw [hshape]
  exact vGAtLeast_zpow_mul (lemma_3_1 h7 hunit hd hY J U hU hU0)

/-! ### Lemma 3.1's hypotheses really hold in the inner range (p. 11)

Three of the four hypotheses of Lemma 3.1 are verified here for the data §4 feeds it.  The
fourth, `Y ∈ ℤ_p[X]`, is `Y = p⁵X + C_p` with `C_p ∈ p⁵ℤ_p` of (3.6) — an analytic
statement about the series (3.5), not available here. -/

/-- **p. 11**: *"near poles have absolute sizes at most `M+1`, and distinct near poles differ
by a `p`-adic unit.  Their harmonic indices are less than `p`."*

Both of Lemma 3.1's hypotheses on the root set `s` follow from the single bound `|r| ≤ M+1`,
because an inner prime has `p > 200M` (`IsInnerPrime.gt_200M`): two distinct integers of
absolute size at most `M+1` differ by at most `2M+2 < p` and not by `0`, so their difference
is a `p`-adic unit; and `d(r) ≤ M+1 < p`. -/
theorem lemma_3_1_hyps_of_near {n M p : ℕ} (hp : IsInnerPrime n M p)
    (s : Finset ℤ) (hs : ∀ r ∈ s, |r| ≤ (M : ℤ) + 1) :
    (∀ r ∈ s, ∀ q ∈ s, r ≠ q → ¬ ((p : ℤ) ∣ (r - q))) ∧ (∀ r ∈ s, dIdx r < p) := by
  have h200 : 200 * M < p := hp.gt_200M
  have hM : 40 ≤ M := hp.cutoff
  have h200Z : (200 : ℤ) * (M : ℤ) < (p : ℤ) := by exact_mod_cast h200
  constructor
  · intro r hr q hq hrq hdvd
    have h1 := hs r hr
    have h2 := hs q hq
    have habs : |r - q| ≤ 2 * (M : ℤ) + 2 := by
      have := abs_sub r q
      omega
    have hne : r - q ≠ 0 := sub_ne_zero.2 hrq
    have hple : (p : ℤ) ≤ |r - q| := Int.le_of_dvd (abs_pos.2 hne) ((dvd_abs _ _).2 hdvd)
    omega
  · intro r hr
    have h1 := abs_le.1 (hs r hr)
    have hpZ : (M : ℤ) + 1 < (p : ℤ) := by omega
    unfold dIdx
    split_ifs with hnn
    · omega
    · omega

/-- **p. 11**, first half of *"Both degrees are at most `p + 1`"*: the leading-numerator
degree `ν_i(c) + ν_j(c) + 6ℓ_N(c)` of an ordinary summand satisfies Lemma 3.1's hypothesis
`deg U_0 ≤ p+1`.  (Chain of p. 11: `≤ 2(T+1) < 23M/5 + 2 ≤ p+1`.) -/
theorem ordinary_degree_le_p_add_one {n M p : ℕ} (hp : IsInnerPrime n M p)
    (A : InnerAlloc n M p) {a i a' i' c : ℕ} (hi : i < A.Ldim a) (hi' : i' < A.Ldim a')
    (hc1 : 1 ≤ c) (hc2 : c ≤ mHalf p) :
    (A.nu a i c : ℤ) + (A.nu a' i' c : ℤ) + 6 * (ell p (N n) c : ℤ) ≤ (p : ℤ) + 1 := by
  have h1 := degree_bound_ordinary hp A hi hi' hc1 hc2
  have h2 := two_T_add_one_lt hp A
  have h3 := (degrees_le_p_add_one (n := n) (M := M) (p := p) hp).1
  have h4 : (2 * ((A.T : ℚ) + 1)) < (p : ℚ) + 1 := lt_of_lt_of_le h2 h3
  have h5 : 2 * (A.T + 1) < (p : ℤ) + 1 := by exact_mod_cast h4
  omega

/-- **p. 11**, second half of *"Both degrees are at most `p + 1`"*: the zero summand's
degree `5 + 2ν_i(0) + 2ν_j(0) + 12m_N` likewise.
(Chain of p. 11: `≤ 5 + 4L₀ + 12m_N ≤ 169M/10 + 45 ≤ p+1`.) -/
theorem zero_degree_le_p_add_one {n M p : ℕ} (hp : IsInnerPrime n M p)
    (A : InnerAlloc n M p) {a i a' i' : ℕ} (hi : i < A.Ldim a) (hi' : i' < A.Ldim a') :
    5 + 2 * A.nu a i 0 + 2 * A.nu a' i' 0 + 12 * mFloor p (N n) ≤ p + 1 := by
  have h1 := degree_bound_zero A hi hi'
  have h2 := zero_degree_le (n := n) (M := M) (p := p) hp
  have h3 := (degrees_le_p_add_one (n := n) (M := M) (p := p) hp).2
  have h4 : ((5 + 4 * L0 M + 12 * mFloor p (N n) : ℕ) : ℚ) ≤ (p : ℚ) + 1 := le_trans h2 h3
  have h5 : 5 + 4 * L0 M + 12 * mFloor p (N n) ≤ p + 1 := by exact_mod_cast h4
  omega

/-! ### Two ingredients of the unimodularity sentence (p. 10)

> "The factors `t + c²` are pairwise coprime modulo `p`.  In the Chinese remainder
> decomposition by their powers, the polynomials in (4.5) give triangular local bases whose
> diagonal entries are units.  They therefore form a `ℤ_p`-unimodular basis of the
> polynomials of degree less than `h`."

The coprimality and the degree bound are proved here; the Chinese-remainder/triangularity
step is part of `entry_bounds_4_2_4_3` below. -/

/-- **p. 10**: *"The factors `t + c²` are pairwise coprime modulo `p`."*

For distinct `c, c'` in `{0, …, m}` with `m = (p-1)/2` one has `c² ≢ c'² (mod p)`, because
`p` divides neither `c - c'` (nonzero, of absolute size at most `m < p`) nor `c + c'`
(positive and at most `2m ≤ p-1 < p`).  This is where `m = (p-1)/2` is used: the map
`c ↦ c²` is injective exactly on that range. -/
theorem sq_ne_sq_mod {p : ℕ} (hp : p.Prime) {c c' : ℕ} (hc : c ≤ mHalf p)
    (hc' : c' ≤ mHalf p) (hne : c ≠ c') :
    ¬ ((p : ℤ) ∣ ((c : ℤ) ^ 2 - (c' : ℤ) ^ 2)) := by
  intro hdvd
  have hp2 := hp.two_le
  have hmHalf : mHalf p = (p - 1) / 2 := rfl
  have hm2 : 2 * mHalf p ≤ p - 1 := by rw [hmHalf]; omega
  have hcZ : (c : ℤ) ≤ (mHalf p : ℤ) := by exact_mod_cast hc
  have hc'Z : (c' : ℤ) ≤ (mHalf p : ℤ) := by exact_mod_cast hc'
  have hm2Z : 2 * (mHalf p : ℤ) ≤ (p : ℤ) - 1 := by
    have : (2 * mHalf p : ℤ) ≤ ((p - 1 : ℕ) : ℤ) := by exact_mod_cast hm2
    have hp1 : ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 := by omega
    omega
  have hneZ : (c : ℤ) ≠ (c' : ℤ) := by exact_mod_cast hne
  have hfac : ((c : ℤ) ^ 2 - (c' : ℤ) ^ 2) = ((c : ℤ) - (c' : ℤ)) * ((c : ℤ) + (c' : ℤ)) := by
    ring
  rw [hfac] at hdvd
  have hpI : Prime ((p : ℤ)) := Nat.prime_iff_prime_int.1 hp
  rcases (hpI.dvd_mul).1 hdvd with h1 | h1
  · have hne0 : (c : ℤ) - (c' : ℤ) ≠ 0 := sub_ne_zero.2 hneZ
    have := Int.le_of_dvd (abs_pos.2 hne0) ((dvd_abs _ _).2 h1)
    have habs := abs_sub (c : ℤ) (c' : ℤ)
    have h0 : (0 : ℤ) ≤ (c : ℤ) := Int.natCast_nonneg c
    have h0' : (0 : ℤ) ≤ (c' : ℤ) := Int.natCast_nonneg c'
    rw [abs_of_nonneg h0, abs_of_nonneg h0'] at habs
    omega
  · have hpos : (0 : ℤ) < (c : ℤ) + (c' : ℤ) := by
      have h0 : (0 : ℤ) ≤ (c : ℤ) := Int.natCast_nonneg c
      have h0' : (0 : ℤ) ≤ (c' : ℤ) := Int.natCast_nonneg c'
      rcases Nat.eq_zero_or_pos c with rfl | hcp
      · have : c' ≠ 0 := fun h => hne (by omega)
        have : (0 : ℤ) < (c' : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero this
        omega
      · have : (0 : ℤ) < (c : ℤ) := by exact_mod_cast hcp
        omega
    have := Int.le_of_dvd hpos h1
    omega

/-- **p. 10**: the row polynomials (4.5) really are *"polynomials of degree less than `h`"*:
`deg E_{a,i} = (h - L_a) + i < h`, using the dimension identity `L₀ + ∑_a L_a = h`. -/
theorem rowPoly_natDegree_lt {n M p : ℕ} (hp : IsInnerPrime n M p) (A : InnerAlloc n M p)
    {a i : ℕ} (ha : a ≤ mHalf p) (hi : i < A.Ldim a) :
    (A.rowPoly a i).natDegree < h n := by
  classical
  have hmem : a ∈ Finset.range (mHalf p + 1) := Finset.mem_range.2 (by omega)
  -- degrees of the individual factors
  have hdeg : ∀ c : ℕ, ((X + C (((c : ℚ)) ^ 2)) ^ A.Ldim c).natDegree = A.Ldim c := by
    intro c
    rw [Polynomial.natDegree_pow, Polynomial.natDegree_X_add_C, mul_one]
  have hne : ∀ c : ℕ, ((X + C (((c : ℚ)) ^ 2)) ^ A.Ldim c) ≠ 0 :=
    fun c => pow_ne_zero _ (Polynomial.monic_X_add_C _).ne_zero
  have hprod : (∏ c ∈ (Finset.range (mHalf p + 1)).erase a,
        (X + C (((c : ℚ)) ^ 2)) ^ A.Ldim c).natDegree
      = ∑ c ∈ (Finset.range (mHalf p + 1)).erase a, A.Ldim c := by
    rw [Polynomial.natDegree_prod _ _ (fun c _ => hne c)]
    exact Finset.sum_congr rfl (fun c _ => hdeg c)
  have htot : (A.rowPoly a i).natDegree
      = (∑ c ∈ (Finset.range (mHalf p + 1)).erase a, A.Ldim c) + i := by
    rw [InnerAlloc.rowPoly, Polynomial.natDegree_mul, hprod, Polynomial.natDegree_pow,
      Polynomial.natDegree_X_add_C, mul_one]
    · exact Finset.prod_ne_zero_iff.2 (fun c _ => hne c)
    · exact pow_ne_zero _ (Polynomial.monic_X_add_C _).ne_zero
  -- the dimension identity, in `ℕ` over `range (m+1)`
  have hdim : ∑ c ∈ Finset.range (mHalf p + 1), A.Ldim c = h n := by
    have hZ : ((∑ c ∈ Finset.range (mHalf p + 1), A.Ldim c : ℕ) : ℤ) = (h n : ℤ) := by
      rw [Nat.cast_sum, Finset.sum_range_succ' (fun c => ((A.Ldim c : ℕ) : ℤ)) (mHalf p)]
      have hstep : ∀ k ∈ Finset.range (mHalf p), ((A.Ldim (k + 1) : ℕ) : ℤ) = A.L (k + 1) :=
        fun k hk => A.Ldim_cast hp (by omega) (by
          simp only [Finset.mem_range] at hk; omega)
      rw [Finset.sum_congr rfl hstep]
      have hIcc : ∑ k ∈ Finset.range (mHalf p), A.L (k + 1)
          = ∑ a ∈ Finset.Icc 1 (mHalf p), A.L a := by
        have hset : Finset.Icc 1 (mHalf p) = Finset.Ico 1 (mHalf p + 1) := by
          ext b; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
        rw [hset, Finset.sum_Ico_eq_sum_range]
        simp only [Nat.add_sub_cancel]
        exact (Finset.sum_congr rfl (fun k _ => by rw [Nat.add_comm])).symm
      rw [hIcc, InnerAlloc.Ldim_zero]
      have := dimension_identity hp A
      omega
    exact_mod_cast hZ
  have herase : (∑ c ∈ (Finset.range (mHalf p + 1)).erase a, A.Ldim c) + A.Ldim a = h n := by
    rw [Finset.sum_erase_add _ _ hmem]
    exact hdim
  omega

/-- **§4's bookkeeping**, proved in `Zeta5/InnerEntries.lean`.

PAPER STATEMENT (Proposition 4.1's proof, p. 11), verbatim, in three pieces:

> "For `a = 0, 1, …, m` and `0 ≤ i < L_a`, take the row polynomial
> `E_{a,i}(t) = ∏_{0≤c≤m, c≠a}(t+c²)^{L_c}(t+a²)^i`.                              (4.5)
> The factors `t + c²` are pairwise coprime modulo `p`.  In the Chinese remainder
> decomposition by their powers, the polynomials in (4.5) give triangular local bases whose
> diagonal entries are units.  They therefore form a `ℤ_p`-unimodular basis of the
> polynomials of degree less than `h`."
>
> "Lemmas 3.1 and 3.2 therefore prove (4.2) and (4.3) for the entire summands."
>
> "Thus each entry in the new basis has valuation at least the sum of its two row weights."

That is: there is a matrix `B` — the Gram matrix of the paper's bilinear form in the basis
(4.5) — with `Δ_K = c · det B` for a `p`-adic unit `c` (unimodularity), whose `(u,v)` entry
has Gauss valuation at least `w_u + w_v`, the weights (4.6)–(4.7) carried here as
`A.rowW = 2w`.

PROOF (`Zeta5.InnerEntries.entry_bounds`).  `B` is the Gram matrix
of `Bil` in the basis (4.5); `c = (det U)^{-2}` with `U` the integer coefficient matrix of the
rows, a `p`-adic unit by `HermiteBasis.det_coeffMatrix_unimodular`; the entry exponent is
`min((4.3), min_c (4.2))`.  Lemma 3.2 is not formalised as an identity in the Tate algebra;
its role is played by two exact finite statements: Raabe's multiplication theorem for `τ`
(`InnerEntries.raabe_tau`, proved from `sum_bernoulli`) and a per-class estimate
(`InnerEntries.class_bound`) that replaces the convergent far-pole series by a truncated
inverse with an explicit remainder of valuation `≥ n − 1`.  See the headers of
`InnerTate.lean`, `InnerGeneral.lean`, `InnerEntries.lean`.

The ingredients the paper invokes are proved: Lemma 3.1 (`Zeta5.lemma_3_1`), the pullback (3.1)
(`Zeta5.eq_3_1_mono`, `Zeta5.eq_3_1_pole`), the identities (3.2), (3.3), the conversion of
the distribution-formula summands into the printed exponents of (4.2) and (4.3)
(`eq_4_2_of_lemma_3_1`, `eq_4_3_of_lemma_3_1`), the degree bounds `≤ p+1`
(`Zeta5.degree_bound_ordinary`, `Zeta5.degree_bound_zero`, `Zeta5.degrees_le_p_add_one`),
the weight comparisons (`Zeta5.weight_comparison`, `Zeta5.zero_source_bound`), the
dimension identity and `L_a > 3/2` (`Zeta5.dimension_identity`, `Zeta5.L_gt_three_halves`),
the p. 10 inequality `b_a < 6αx+3` (`Zeta5.ell_lt_caseSplit`), `Σ_u W_u = γ_p^in`
(`Zeta5.InnerAlloc.sum_rowW`), and the determinant reduction
(`Zeta5.prop_4_1_of_entry_bounds`, `Zeta5.lemma_4_2`).

The degree-`≤ p+1` check that the audit flags is `InnerEntries.uW_le`. -/
theorem entry_bounds_4_2_4_3 (n M p : ℕ) (_hp : IsInnerPrime n M p) (A : InnerAlloc n M p) :
    ∃ (B : Matrix A.Rows A.Rows ℚ[X]) (entry : A.Rows → A.Rows → ℤ) (c : ℚ),
      (∀ u v, vGAtLeast p (B u v) (entry u v)) ∧
      (∀ u v, A.rowW u + A.rowW v ≤ 2 * entry u v) ∧
      c ≠ 0 ∧ padicValRat p c = 0 ∧ Delta n = C c * B.det :=
  InnerEntries.entry_bounds n M p _hp A

/-- **PROPOSITION 4.1** (p. 11): *"Under (4.1), `v_p^G(Δ_K) ≥ γ_p^in`."*

This has exactly the type of `Zeta5.prop_4_1` in `Interface.lean`, which is proved by it.
It rests on `entry_bounds_4_2_4_3` above (proved in `Zeta5/InnerEntries.lean`), and
otherwise only on `Zeta5.prop_4_1_of_entry_bounds` and
`Zeta5.InnerAlloc.sum_rowW`. -/
theorem prop_4_1 (n M p : ℕ) (hp : IsInnerPrime n M p) (A : InnerAlloc n M p) :
    vGAtLeast p (Delta n) A.gammaIn := by
  classical
  obtain ⟨B, entry, c, hentry, hweights, hc0, hcunit, hbasis⟩ :=
    entry_bounds_4_2_4_3 n M p hp A
  exact prop_4_1_of_entry_bounds hp.prime A B A.rowW entry hentry hweights A.sum_rowW
    c hc0 hcunit hbasis

end Section3

/-! # Known-answer controls

Every number checked here is also computed in the audit (`docs/zeta5-audit.pdf`). -/

section Controls

/-- `κ₃ = 3·2·1·B₀/24 = 1/4`, hence `τ(-x³) = -1/4`: the constant that appears in (2.3). -/
example : tau (-(X ^ 3) : ℚ[X]) = -(1 / 4) := by
  rw [tau_neg, tau_X_pow, kappa_three]

/-- `τ(x⁵) = κ₅ = 5·4·3·B₂/24 = 5/12`, and this is `μ(t⁰) = 5/12` of (2.2) — the first
entry of the audit's table `μ(t^e) = 5/12, 7/24, 1/2, 11/8, 65/12, 691/24, …`. -/
example : tau (X ^ 5 : ℚ[X]) = 5 / 12 := by
  rw [tau_X_pow]
  norm_num [kappa, _root_.bernoulli_two]

example : muMono 0 = 5 / 12 := by norm_num [muMono, _root_.bernoulli_two]

/-- `μ_X(1/(t+1)) = X - 3/4`; at `X = ζ(5)` this is the audit's
`μ_{ζ(5)}(1/(t+1)) = ζ(5) - 3/4 = 0.28692775514336992633…`. -/
example (q : ℚ) : (muPole 1).eval q = q - 3 / 4 := by
  norm_num [muPole, H5]
  ring

/-- **(3.3)** at `g = x⁴`: `τ(g(x+1) - g(x)) = g⁗(0)/24 = 24/24 = 1`. -/
example : tau ((X ^ 4 : ℚ[X]).comp (X + 1) - X ^ 4) = 1 := by
  rw [eq_3_3]
  norm_num [Polynomial.derivative_X_pow]

/-- **(3.2)** at `g = x³`: `τ(g(-1-x)) = -τ(g) = -κ₃ = -1/4`. -/
example : tau ((X ^ 3 : ℚ[X]).comp (-1 - X)) = -(1 / 4) := by
  rw [eq_3_2, tau_X_pow, kappa_three]

/-- `d(0) = d(-1) = 0`, `d(3) = 3`, `d(-3) = 2`: the index of p. 5.  The coincidence
`d(0) = d(-1)` is exactly why (3.3) "requires `g` regular at zero": at `g = 1/x` both
`τ_X(1/(x+1))` and `τ_X(1/x)` equal `-X`. -/
example : dIdx 0 = 0 ∧ dIdx (-1) = 0 ∧ dIdx 3 = 3 ∧ dIdx (-3) = 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

end Controls

/-! # Axiom checks -/

section
#print axioms Zeta5.eq_3_2
#print axioms Zeta5.eq_3_3
#print axioms Zeta5.eq_3_1_mono
#print axioms Zeta5.eq_3_1_pole
#print axioms Zeta5.eq_3_1_partialFraction
#print axioms Zeta5.lemma_3_1
#print axioms Zeta5.resid_eq_eval
#print axioms Zeta5.Section3.lemma_3_1_hyps_of_near
#print axioms Zeta5.Section3.ordinary_degree_le_p_add_one
#print axioms Zeta5.Section3.zero_degree_le_p_add_one
#print axioms Zeta5.Section3.sq_ne_sq_mod
#print axioms Zeta5.Section3.rowPoly_natDegree_lt
#print axioms Zeta5.Section3.eq_4_2_of_lemma_3_1
#print axioms Zeta5.Section3.eq_4_3_of_lemma_3_1
#print axioms Zeta5.Section3.entry_bounds_4_2_4_3
#print axioms Zeta5.Section3.prop_4_1
end

end

end Zeta5
