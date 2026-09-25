# What is proved, and deviations from the paper

This file is the detailed companion to the README. It lists, section by section of A. Fauzan's
preprint "ζ(5) is irrational" (17 September 2026, Zenodo v1), the statements of the paper that
the Lean development proves and the Lean names that prove them, and it gives the complete list
of the places where the formal statement or proof differs from the paper. The README's
"Deviations" section summarizes this list; each item below cites the README item it expands,
where there is one. All names are in the namespace `Zeta5` unless written in full. Page and
equation numbers refer to the preprint.

Every declaration named below depends only on `propext`, `Classical.choice` and `Quot.sound`,
except those through which Proposition 5.2 passes, which depend also on the prime number
theorem `Axioms.chebyshev_theta_asymptotic` (`Zeta5/Axioms.lean`).

---

## 1. What is proved, by section of the paper

`Zeta5/Interface.lean` states, for each numbered result that the proof of Theorem 1.1 uses,
one declaration whose type transcribes the printed statement, and proves it by citing the
file where the proof is. Its names are in the root namespace (`prop_2_2`, `prop_4_1`,
`prop_4_3`, `prop_4_3_large`, `prop_5_1`, `prop_5_2`, `eq_2_9`, `eq_5_16_5_18`, `eq_5_21`,
`prop_6_3`, `eq_7_1`, `theorem_2_1`, `zeta5_irrational`).

### §1 and §2: the criterion, the functional, positivity

* **Theorem 1.1 from Theorem 2.1** (§1.1): `theorem_1_1` (`Skeleton.lean`), the integrality
  criterion applied to the integer polynomials Q_{K,M} at ζ(5). The main theorem is
  `zeta5_irrational : Irrational zeta5` (`Interface.lean`), with
  `zeta5 = ∑' v : ℕ, 1 / ((v : ℝ) + 1) ^ 5` (`Basic.lean`).
* **The functional μ_X** (§2, `Functional.lean`): partial fractions and their uniqueness
  (`Functional.partial_fractions`, `Functional.partial_fraction_unique`); μ_X is affine in X
  (`Functional.muOver_eq_affine`, and [X]G_K = V diag(d) Vᵀ via `Functional.G_eq_affine`);
  (2.2) in the form (2e+5)! ζ(2e+2)/(12(2π)^{2e+2}) by Euler's formula
  (`Functional.muMono_eq_zeta`).
* **(2.9)**, the leading coefficient of Δ_K, and **deg Δ_K = h**: `eq_2_9`, `eq_2_9_ne_zero`,
  `Delta_natDegree`.
* **The pole integral of p. 5**: `Hermite.pole_integral`, ∫₀^∞ w(y)/(y² + a²) dy =
  a⁴ζ(5, a) − 1/(2a) − 1/4 for a > 0 (deviation 1).
* **Proposition 2.2** (§2.4, `Positivity.lean`): (2.10) for every rational function in the
  domain of μ_X (`prop_2_2_moment`), and positive definiteness of G_K(ζ(5)) (`prop_2_2`);
  hence Δ_K(ζ(5)) > 0 (`delta_pos`).

### §3: the local functional

* **(3.1)–(3.3)** (`LocalFunctional.lean`): `eq_3_1_mono`, `eq_3_1_pole`, `eq_3_2`, `eq_3_3`;
  τ(x^d) = κ_d, and κ_d ∈ ℤ_p for d ≤ p + 1 by von Staudt–Clausen (`Arithmetic.lean`).
* **(3.1) for every rational function μ_X(B/D_tail)**, i.e. on the whole domain of μ_X:
  `Lemma33.pullback`, `InnerEntries.pullback`. The extension τ^ext of p. 6 is `tauExtOf`.
* **Lemma 3.1**, for partial sums: `lemma_3_1` (deviation 2).
* **Lemma 3.2**: the polynomial case of (3.7), for every m ≥ 1, is `InnerEntries.raabe_tau`
  (m⁴τ(P) = Σ_{a<m} τ(P(a + mz))). The rest of Lemma 3.2 is replaced (deviation 3).
* **Lemma 3.3** (p. 8), as printed: `Lemma33.lemma_3_3`; the version without the term
  −v_p(24): `Lemma33.lemma_3_3_strong` (deviation 4).
* **(3.11)**, including the recovery of S_K: `CrudeBound.eq_3_11`; Lemma 3.3 at the entries of
  (3.11): `CrudeBound.crude_entry_bound`; **(3.12)**: `CrudeBound.eq_3_12`. Integer-valued
  polynomials in the binomial basis: `integer_binom_coeffs`.

### §4.1: the inner range

* **The counts ℓ_A(a)** and the inequality of p. 10 in strict form: `ell_lt` (`Counting.lean`)
  and `ell_lt_caseSplit` (`Section41.lean`), two proofs of the same statement; in the paper's
  variables, `bCoef_lt_real` (deviation 6). **L_a ≥ 0**: `InnerAlloc.L_nonneg`.
* **The allocation (4.4)** and its existence: `InnerAlloc` (`Basic.lean`), `exists_TE`,
  `exists_innerAlloc_of_inner`, `exists_innerAlloc`. The weights (4.6)–(4.8) and γ_p^in:
  `InnerAlloc.gammaIn`; the weight comparisons of p. 11: `weight_comparison`.
* **Unimodularity of the basis (4.5)**: from `HermiteBasis.det_coeffMatrix_unimodular`
  (deviation 5).
* **The entry bounds (4.2)/(4.3)** for the whole summands: `InnerEntries.entry_bounds`, with
  the general local bound `InnerEntries.general_bound` and the per-class bound
  `InnerEntries.class_bound`; the degree hypothesis ≤ p + 1 is `InnerEntries.uW_le`. The
  interface form is `Section3.entry_bounds_4_2_4_3`.
* **Proposition 4.1**: `Section3.prop_4_1`, restated as `prop_4_1`.

### §4.2: the outer range

* **Lemma 4.2 (4.13)**: `lemma_4_2` over an abstract valued field (deviation 8), and the
  determinant-vanishing form used by Proposition 4.3, `vanishing_of_rank`.
* **The congruence H^{(5)}_{p−a} ≡ H^{(5)}_{a−1} (mod p)**: `OuterLocal.H5_congr`; the
  divided-difference integrality of p. 12: `OuterLocal.muPole_divided_difference`
  (deviation 10).
* **(4.10) with rank L ≤ r_p, the basis (4.11) and its unimodularity, and the entry bounds
  behind (4.12)**: `OuterBasis.outer_local_core`, restated as `outer_local_analysis`
  (`OuterRange.lean`) (deviations 9, 11). The weights of (4.12), doubled, are
  `OuterBasis.wtO`.
* **The table of p. 13 and (4.14)**: `table_removed`, `table_unremoved`, and the assembly
  `prop_4_3_of_local_data_vanishing`.
* **Proposition 4.3**, both assertions: `Outer.prop_4_3` and `Outer.prop_4_3_large`, restated
  as `prop_4_3` and `prop_4_3_large`.

### §5: integrality and the prime sum

* **Legendre's formula for v_p(S_K)** (5.3): `vS_eq`; v_p(m_{K,M}): `padicValRat_mKM`.
* **Proposition 5.1**: `prop_5_1_of` (`Normalization.lean`), restated as `prop_5_1`.
* **(5.7) and the two displays of §5.2**, with C = 400M²: `Uniformity.eq_5_7_uniformity`,
  restated as `PrimeSum.eq_5_7_uniformity` (deviation 12). The regularity sentence of p. 14:
  `PrimeSum.RR_reg`; the bound on R: `PrimeSum.RR_bddOn` (deviation 13).
* **The partial summation of p. 15**: `PNT.prime_riemann_sum`, from θ(x) ~ x through
  `PNT.theta_scaled` (deviation 14); used by `PrimeSum.tendsto_primeSum`.
* **Proposition 5.2 (5.11)**: `PrimeSum.prop_5_2`, restated as `prop_5_2`, from the
  three-range decomposition of log m_{K,M} along (5.1).
* **(5.12)–(5.14)**: `AppendixB.eq_5_14`, `Tail.eq_5_14`; **(5.15)–(5.17)**, the integrations
  by parts: `Tail.integration_by_parts`, `Tail.tail_bound`, `AppendixB.eq_5_16_5_17`
  (deviation 17).
* **(5.18)–(5.21)**: `AppendixB.eq_5_18`, `AppendixB.eq_5_16_5_18` and `eq_5_21` (deviation 16).

### §6: the real bound

* **(6.4)/(A.10)** from Table 1 with certified logarithm enclosures: `RealBound.eq_6_4`,
  `RealBound.A10_Cstar` (deviation 24). The constants of (6.14) are `RealBound.Irho` and
  `RealBound.M0` (deviation 18).
* **(6.10)–(6.13)** (`Sec6/Gram.lean`): Andréief's identity `Sec6.Gram.andreief`, (6.10)
  `Sec6.Gram.eq_6_10`, (6.12) `Sec6.Gram.eq_6_12_lower` and `Sec6.Gram.eq_6_12_upper`, (6.13)
  `Sec6.Gram.gram_bound`, and (6.14) from any sufficiently good configuration bound,
  `Sec6.Gram.eq_6_14_of_config` (deviation 21).
* **(6.11)**, as printed: `RealBound.eq_6_11` (deviation 24).
* **The configuration bound (6.6)–(6.9)**: `Sec6.configBound`, with `Sec6.eq_6_6_cauchy`
  (`Sec6/Energy.lean`), for the regularized kernel `Sec6.kC` (deviations 19, 20).
* **Lemma 6.2** for the regularized kernel: `Sec6.cauchy_cnd` (`Sec6/CND.lean`, with
  `Frullani.lean`, `GaussPD.lean`, `Swap.lean`) (deviation 19).
* **(6.2), (6.7), (6.8); Lemma 6.1**: `Sec6.Num.eq_6_7_closed` on the closed forms of U^ρ and
  V, transferred to the field V of (6.1) as `Sec6.eq_6_7_closed` (`Sec6/Potential.lean`)
  (deviation 22).
* **(6.14)** and **Proposition 6.3 (6.16)**: `RealBound.eq_6_14` and `RealBound.prop_6_3`
  (`Sec6/Final.lean`, whose module docstring gives the route), restated as `prop_6_3`.
  (6.15): `RealBound.eq_6_15`; (6.14) ∧ (6.15) ⇒ (6.16) with the exact K² log K cancellation:
  `RealBound.prop_6_3_of`, `RealBound.K2logK_cancel`.

### §7: conclusion

* **(7.1)** from (5.21) and (6.16): `eq_7_1_of` (`Asymptotics.lean`), restated as `eq_7_1`.
* **(7.2)**, the exact margins at M = 200 and M = 100000: `margin_200_exact`,
  `margin_100000_exact`; (2.7) and (2.8): `decay_2_7`, `decay_2_8`.
* **Theorem 2.1** from its inputs: `theorem_2_1_of` (`Arithmetic.lean`); at M = 200:
  `theorem_2_1`, with the allocation family `stdAlloc`.

### Appendix A

* **Table 1** and its nesting: `RealBound.tab1_nested`; the certified logarithms
  `RealBound.log_two_bounds`, `RealBound.logLen0`–`logLen15` (deviation 24).
* **(A.1)**, the arcsine potential, on every interval: `Sec6/ArcsinePot.lean`, with
  `Sec6/LogCos*.lean` (deviation 23).
* **(A.2)**, as I(ρ) ≤ I_k(ρ, ρ) for the regularized kernel: `Sec6.rho_energy_ge`
  (`Sec6/RhoEnergy.lean`) (deviation 18).
* **(A.5)**, the closed form of the field V: `Sec6.Vfield_eq_Vclosed`, with
  `Sec6.integral_log_add_sq` (`Sec6/Field.lean`).
* **Table 2** tiles [0, 2]: `RealBound.table2_tiles` (deviation 22).
* The regularization constant ≤ 60 of p. 19: `RealBound.reg_const_le_sixty` (deviation 20).

### Appendix B

* **(B.1)**, the 143 affine pieces of (B.2), and **Tables 3 and 4**, by exact rational
  arithmetic: `AppendixB.lean` (`AppendixB.table3_3`, …). (5.8)–(5.10) with I_out computed:
  `AppendixB.eq_5_10` (deviation 15).
* `AppendixBCheck.lean` checks at the type level that `AppendixB.lean` proves the statements
  in `Interface.lean`.

---

## 2. Deviations from the paper

At each place below, a step is proved by a different argument from the paper's, or a statement
is formalized in a different form: equivalent, stronger, or (where said) weaker but sufficient
for its use. Each is recorded in the docstring of the declaration concerned.

### §2

1. **The pole integral of p. 5** (README 8). `Hermite.pole_integral` does not use Hermite's
   formula (DLMF 25.11.29) or the four integrations by parts; neither is formalized. It expands
   w as its defining series, rescales each term (u = 2π(l + 1)y/a), sums over l with the
   Mittag-Leffler expansion Σ_l 2u/(u² + (2π(l + 1))²) = 1/(eᵘ − 1) − 1/u + 1/2 (from
   Mathlib's `cot_series_rep'`), expands 1/(eᵘ − 1) geometrically and evaluates the Laplace
   integrals ∫₀^∞ uᵐe^{−cu} du = m!/c^{m+1}. Every sum–integral interchange is for nonnegative
   terms.

### §3

2. **Lemma 3.1 for partial sums.** `lemma_3_1` proves (3.4) for every partial sum
   Σ_{j≤J} p^j U_j, not for the series in the Tate algebra ℚ_p⟨z⟩, which is not formalized.
   This is weaker than the paper's lemma. Proposition 4.1 is proved through
   `InnerEntries.general_bound` (deviation 3), not through Lemma 3.1.
3. **Lemma 3.2 (3.7), with its far poles** (README 1). The Tate-algebra extension, (3.5), the
   parameter Y = p⁵X + C_p of (3.6), and (3.7) for rational functions with far poles are not
   formalized. What Proposition 4.1 needs from them is proved directly: the pole terms of
   τ^ext_X(W/Q) are bounded directly (v_p(c_r) ≥ u_a − t_a + 1, v_p(H^{(5)}) ≥ −5); the
   polynomial part goes through `InnerEntries.raabe_tau` (the polynomial case of (3.7), for
   every m ≥ 1) and `InnerEntries.class_bound`, where the far-pole series is replaced by a
   truncated inverse with an explicit remainder of valuation ≥ n − 1. Together they give the
   general local bound v_p^G(τ^ext_X(W/Q)) ≥ min_a(u_a − t_a) − 4
   (`InnerEntries.general_bound`).
4. **Lemma 3.3, polynomial part** (README 2). `Lemma33.lemma_3_3` is Lemma 3.3 as printed,
   for every prime p and every K and d, with τ_X = `tauExtOf X`. The hypothesis "A
   integer-valued on ℤ_p" is taken as v_p(A(z)) ≥ 0 for all z ∈ ℤ, which is equivalent (ℤ is
   dense in ℤ_p). The pole terms are bounded as in the paper (v_p(c_r) ≥ −⌊log_p 2K⌋,
   v_p(H^{(5)}) ≥ −5⌊log_p K⌋). The polynomial part does not use the two-scale estimate
   P(ℤ_p) ⊂ p^{−L₀−M₀}ℤ_p, (3.8) or (3.9), which are not formalized: A is expanded in the
   binomial basis C(x + K, k) and τ of each quotient is computed exactly from (3.3). The term
   −v_p(24) of (3.10) is not needed (`Lemma33.lemma_3_3_strong`).

### §4.1

5. **Unimodularity of (4.5) and (4.11)** (README 3). The paper's two justifications
   ("triangular local bases whose diagonal entries are units", p. 10; "the local polynomials
   are monic of successive degrees, and the resultants of distinct class factors are units",
   p. 12) are replaced by one lemma, `HermiteBasis.det_coeffMatrix_unimodular`: a basis of
   integer polynomials that reduces mod p to a Hermite-interpolation basis
   ∏_{c≠a}(t + u_c)^{m_c}(t + u_a)^i with distinct nodes is ℤ_p-unimodular. Its proof uses
   linear independence of the Hermite family over 𝔽_p, a dimension count, and reduction of the
   determinant mod p.
6. **The inequality b_a ≤ 6αx + 3 on p. 10** (README 4). The paper states it after (4.4)
   without proof; it does not follow from (4.4). It is a statement about ℓ_N, equivalent to
   p·ℓ_N(a) ≤ 2N + p, and is proved in the strict form p·ℓ_A(a) < 2A + p, once from the closed
   form of ℓ_A (`ell_lt`, `Counting.lean`) and once by a case split on A mod p
   (`ell_lt_caseSplit`, `Section41.lean`); `Checks.lean` checks that the two statements are the
   same. In the paper's variables it is `bCoef_lt_real`, b_a < 6αx + 3. The bound
   ℓ_A(a) ≤ 2⌊A/p⌋ + 2 gives only b_a ≤ 6αx + 6, which does not make the L_a of (4.4) provably
   nonnegative (`naive_chain`, `naive_bound_insufficient`); on every residue class the naive
   route is blocked (`ell_naive_attained`, `naive_not_enough`).
7. **Notation.** `InnerAlloc.L A a` is the paper's L_a of (4.4); in particular `InnerAlloc.L A 0`
   is not the paper's L₀ = 4M + 10, which is `L0 M` (`Basic.lean`). `InnerAlloc.gammaIn` uses
   `L0 M`.

### §4.2

8. **Lemma 4.2.** `lemma_4_2` is stated over an abstract valued field and takes an element
   `pinv` with valuation ≥ −1 in place of p⁻¹; this is more general, and every instantiation
   satisfies it. Proposition 4.3 uses the determinant-vanishing form `vanishing_of_rank` (a
   determinant taking more than r columns from a rank-≤ r matrix vanishes), through
   `prop_4_3_of_local_data_vanishing`.
9. **(4.10)** (README 6). `outer_local_analysis` states (4.10) in its rank form,
   rank L ≤ r_p, as printed. The vanishing L_ij = 0 for i + j < K − 6N + 2p − 3 is proved in the
   monomial basis (`OuterBasis.L0_eq_zero`), and L = U L₀ Uᵀ transports the rank bound to the
   basis (4.11), which Proposition 4.3 uses. In the basis (4.11) itself, L has in general no
   vanishing columns (e.g. K = 40, p = 17, 19, 23).
10. **The divided-difference step on p. 12** (README 5). The paper cites only
    H^{(5)}_{p−a} ≡ H^{(5)}_{a−1} (mod p) (`OuterLocal.H5_congr`); that congruence alone
    leaves a residue −1/a (`OuterLocal.muPole_tail_is_needed`). The proof also uses the term
    −1/4 + 1/(2j) of the pole values (2.3) (`OuterLocal.muPole_divided_difference`).
11. **Hypotheses of the §4.2 local analysis.** `OuterBasis.outer_local_core` uses only
    `OuterHyp`, which is (4.9) without p ≤ K: p prime, p ≥ 7, K < 3p, 2K < p², 2N < p,
    5N ≤ 2p − 2. Nothing in it uses K ≥ 200M². The weights `OuterBasis.wtO` are twice those of
    (4.12): min(0, 2i + 6δ − ℓ − 4) for i < ℓ − 2, else 0; for the zero class −1 for one pole
    and −4, 0 for two.

### §5

12. **(5.7) and the two displays of §5.2.** `PrimeSum.eq_5_7_uniformity` bundles the two
    halves of (5.7) and the sum of the two §5.2 displays into one existential over a single
    constant C, and `Uniformity.eq_5_7_uniformity` proves it with C = 400M². A shared constant
    is at least as strong as separate ones. The p. 14 transition remark is used as the identity
    I(T + 1) − I(T) = T − x − 2.
13. **The bound on R.** `PrimeSum.RR_bddOn` proves |R| ≤ 200M² on [3, M], weaker than the
    paper's |R| ≤ 6λM + 13/8; nothing downstream needs the sharper constant.
14. **Partial summation on p. 15** (README 9). `PNT.prime_riemann_sum` (for 0 ≤ a < b and φ
    bounded on [a, b] and continuous off a finite set,
    X⁻¹ Σ_{aX<p≤bX} φ(p/X) log p → ∫_a^b φ) is proved from θ(x) ~ x by a Darboux-type sandwich,
    not by Abel's identity: θ(cX)/X → c (`PNT.theta_scaled`); for each ε a uniform partition of
    [a, b] whose oscillations ω_j satisfy Σ ω_j h ≤ ε (small balls around the exceptional set,
    uniform continuity off them); on each piece the prime sum is compared with
    φ(y_{j+1})(θ(y_{j+1}X) − θ(y_jX)); telescoping.
15. **(5.8)/(5.9)** are written as nested `if`s. They differ from the paper only at y ≤ 1/3,
    y = 1/2 and y = 1, which lie outside (1/3, 2λ) or form a null set at a Table 4 endpoint.
16. **(5.16)–(5.21) hypotheses.** `eq_5_21` and `eq_5_16_5_18` assume 40 ∣ M and M > 0, as in
    the paper.
17. **(5.16)–(5.17)** (README 7). `AppendixB.eq_5_16_5_17` proves the combined bound
    ∫_{20}^{M} R(x) x^{−3} dx ≤ −2689/48000 + λ/M − (2923/240 − 1/4)/M² + 32/M³ that (5.18)
    uses (through ∫_3^M = ∫_3^{20} + ∫_{20}^M), not the two improper integrals separately. It
    is implied by their conjunction, so formally weaker than the printed pair; the proof
    reproduces the constant of (5.16).

### §6 and Appendix A

18. **I(ρ) and M₀ in (6.14)** (README 11). `RealBound.eq_6_14` is stated with `RealBound.Irho`,
    the closed form (A.2), and `RealBound.M0 = −1329/200` as defined real numbers, not as the
    logarithmic energy ∬ log|t − u| dρ dρ and the conclusion of Lemma 6.1. (A.10)/(6.4) is
    proved from them. The proof of (6.14) connects them to the energy argument through
    Irho ≤ I_k(ρ, ρ) for the regularized kernel (`Sec6.rho_energy_ge`) and (6.2)/(6.7) for the
    closed forms of U^ρ and V (`Sec6.Num.eq_6_7_closed`). The equality of Irho with the
    singular energy is not stated.
19. **Regularization of (6.6)–(6.9)** (README 10). The paper replaces each point t_i by the
    uniform measure on a circle of radius ε in ℂ and applies Lemma 6.2 to log|z − w|. Here the
    points stay on the real line and the kernel is regularized: kC ε(x) = ½ log(x² + ε²)
    (`Sec6.kC`), which is ≥ log|x| and continuous, with ε = (16K)⁻². The zero-mass inequality
    of Lemma 6.2 is proved for kC ε (`Sec6.cauchy_cnd`) from a Frullani representation and
    positive definiteness of the Gaussian kernel, for finite measures on a bounded interval.
    Singular integrals are reduced to one-dimensional integrals in θ for the arcsine measures
    θ ↦ m + r cos θ. Lemma 6.2 for the singular kernel is not formalized. The configuration
    bound obtained (`Sec6.configBound`) is 2h log K + 20h, in place of the paper's
    (120 + √2)h + 2h log K.
20. **The smoothing error** (README 10). It is bounded by π(δ + π√(2δ)) per arcsine component
    (`Sec6.smooth_err_norm`), via the nearest point of [−1, 1] in angle form and
    ∫₀^X log(1 + b²/x²) dx, for a total of 88√ε + 420ε, in place of the paper's mass bound and
    60√ε (p. 19). The paper's regularization constant ≤ 60 is proved
    (`RealBound.reg_const_le_sixty`) but not used.
21. **(6.10)–(6.13)** (README 12). The factor 1/h! of (6.10) is kept through to (6.14); the
    paper keeps it in (6.13) and discards it (log h! ≥ 0) when taking logarithms. The bound
    ∫₀^∞(1 + y)⁵e^{−y/K} dy ≤ 326K⁶ replaces the constant 652. With these,
    `Sec6.Gram.eq_6_14_of_config` accepts any configuration bound up to
    (λM₀ − I(ρ))K² + 3h log K + 131h; the paper's own (6.9) constants are admissible
    (`Sec6.Gram.paper_6_9_admissible`). The upper half of (6.12) is proved by sum–integral
    comparison for an increasing function, in place of "decreasing in t, then evaluate at
    t = 0". Andréief's identity (6.10) is proved via a double permutation sum.
22. **(6.2) on [0, 2]** (README 13). The bound ℬ(l, r) of (A.9) on the 684 cells of Table 2 is
    not formalized. `Sec6/Num/` evaluates the closed forms (A.1) and (A.5) of 2U^ρ − V with
    certified rational interval arithmetic on a partition of 1049 cells of [0, 2], generated by
    `numerics/sec6/gen_lean.py`, and two cells of [2, 4], each checked by `decide +kernel`
    against M₀ − 3/10; t ≥ 4 is covered by an analytic bound (`Sec6.Num.tail_bound_ge4`) in
    place of (6.8). That Table 2 tiles [0, 2] is proved (`RealBound.table2_tiles`) but not used.
23. **(A.1)** is proved in normalized form, (1/π)∫₀^π log|x − cos θ| dθ, and then scaled: on
    [−1, 1] from the product formula for cos φ − cos θ and ∫₀^π log sin = −π log 2; off it from
    Mathlib's circle average of log‖· − a‖ (`circleAverage_log_norm_sub_const₂`).
24. **Elementary bounds proved by a different estimate.** The logarithm enclosures behind
    Table 1 and (A.10) use the Taylor series of log(1 − x) with Mathlib's remainder
    (`Real.abs_log_sub_add_sum_range_le`), after reducing the argument to [2/3, 4/3] by a power
    of two, in place of the paper's remainder 2z^{2m+1}/((2m + 1)(1 − z²)) of (A.3).
    `RealBound.eq_6_11` proves (6.11) as printed using Σ_{ℓ≥1} ℓ⁴qˡ ≤ 24q/(1 − q)⁵ in place of
    the exact closed form; this gives the constant 32π⁴ ≈ 3117.1, below the printed 8192.

---

## 3. Known limitations

* **Parts of the paper not formalized**, because the formal proof goes around them: the
  Tate-algebra part of Lemma 3.2 and the series form of Lemma 3.1 (deviations 2, 3); (3.8) and
  (3.9) (deviation 4); Hermite's formula DLMF 25.11.29 and the integrations by parts of p. 5
  (deviation 1); Lemma 6.2 for the singular kernel (deviation 19); the bound (A.9) on the cells
  of Table 2 (deviation 22); the identification of `RealBound.Irho` with the singular energy of
  ρ (deviation 18).
* **The prime number theorem** is an axiom (`Axioms.chebyshev_theta_asymptotic`), because
  Mathlib v4.34.0 does not prove θ(x) ~ x.
* **Linter warnings.** `lake build` reports 17 style warnings: 14 "automatically included
  section variable(s) unused" (in `InnerTate.lean`, `InnerGeneral.lean`, `InnerEntries.lean`)
  and 3 "Variable name … is not explicitly referenced" (`ha` in
  `InnerEntries.comp_X_sub_C_phi_near`, `hC0` in `PrimeSum.block2_le` and
  `PrimeSum.block3_le`). Silencing them would change the signatures of those theorems, so they
  are left as they are. None affects soundness.
