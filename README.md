# ζ(5) is irrational: a Lean 4 formalization of A. Fauzan's proof

[![Lean Action CI](https://github.com/danromik/zeta5-irrationality/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/danromik/zeta5-irrationality/actions/workflows/lean_action_ci.yml)

This repository contains a complete formalization, in Lean 4 with the Mathlib library, of the
proof in A. Fauzan's preprint *"ζ(5) is irrational"* (17 September 2026). The development
follows the paper section by section: it defines the paper's objects (the functional μ_X, the
Hankel matrices G_K and their determinants Δ_K, the normalized polynomials Q_{K,M}, the
allocations of §4, the limiting functions of §5, the measure and constants of Appendix A),
states its propositions and lemmas, and proves them up to Theorem 1.1. There is no `sorry`.
The one external input is the prime number theorem, which Mathlib does not contain; it is
stated as an axiom in its textbook form.

The development has 70 Lean files under `Zeta5/` (about 29,400 lines) and builds with
Lean 4.34.0 and Mathlib v4.34.0.

## The result

```lean
-- Zeta5/Basic.lean
/-- `ζ(5) = ∑_{v ≥ 1} v^{-5}`. -/
def zeta5 : ℝ := ∑' v : ℕ, (1 : ℝ) / ((v : ℝ) + 1) ^ 5

-- Zeta5/Interface.lean
theorem zeta5_irrational : Irrational zeta5 :=
  theorem_1_1 stdAlloc (theorem_2_1 stdAlloc)
```

Both declarations are in the namespace `Zeta5`. The theorem has no hypotheses. `Irrational` is
Mathlib's predicate (`Irrational x` means `x ∉ Set.range ((↑) : ℚ → ℝ)`), and `∑'` is Mathlib's
sum of a summable series.

`#print axioms Zeta5.zeta5_irrational` gives

```
'Zeta5.zeta5_irrational' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Zeta5.Axioms.chebyshev_theta_asymptotic]
```

`propext`, `Classical.choice` and `Quot.sound` are the standard axioms of Lean's logic, used
throughout Mathlib. The fourth is the prime number theorem:

```lean
-- Zeta5/Axioms.lean
axiom chebyshev_theta_asymptotic :
    Tendsto (fun x : ℝ => Chebyshev.theta x / x) atTop (nhds 1)
```

that is, θ(x) ~ x, where θ(x) = Σ_{p ≤ x, p prime} log p is Mathlib's `Chebyshev.theta`
(Hadamard, de la Vallée Poussin, 1896; e.g. Apostol, *Introduction to Analytic Number Theory*,
Thm. 4.4 with Ch. 13; the paper cites DLMF 27.12.2–27.12.4 on p. 15). Mathlib v4.34.0 defines θ
and proves Chebyshev-type bounds but not θ(x) ~ x. The axiom is used only in Proposition 5.2,
through `Zeta5.PNT.prime_riemann_sum`. `Zeta5/Axioms.lean` is the only file that declares an
axiom.

What Lean checks is therefore the implication: the prime number theorem implies that ζ(5) is
irrational.

## How to check it

You need a Unix-like shell (macOS, Linux, or WSL on Windows), `git`, and about 8 GB of disk
space, mostly for the compiled Mathlib library.

1. **Install elan**, the Lean toolchain manager (<https://github.com/leanprover/elan>):

   ```sh
   curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
   ```

   elan reads `lean-toolchain` and installs Lean 4.34.0 automatically.

2. **Clone the repository and download the compiled Mathlib:**

   ```sh
   git clone https://github.com/danromik/zeta5-irrationality.git
   cd zeta5-irrationality
   lake exe cache get
   ```

   Without `lake exe cache get`, `lake build` compiles Mathlib from source, which takes hours.

3. **Build:**

   ```sh
   lake build
   ```

   A clean build of the project takes about 7 minutes on a 12-core machine; the modules in
   `Zeta5/Sec6/Num/` need up to about 8 GB of memory. The output contains no
   `declaration uses 'sorry'` warning, 17 linter warnings (14 "automatically included section variable(s) unused", 3 "Variable name …
   is not explicitly referenced"), and ends with `Build completed successfully (8995 jobs).`

4. **Check the statement.** `cert/Check.lean` restates the theorem and the axiom using only
   Mathlib names, so that the check does not depend on any definition or notation of this
   project:

   ```lean
   import Zeta5
   open Filter

   example : Irrational (∑' v : ℕ, (1 : ℝ) / ((v : ℝ) + 1) ^ 5) :=
     Zeta5.zeta5_irrational

   example : Tendsto (fun x : ℝ => Chebyshev.theta x / x) atTop (nhds 1) :=
     Zeta5.Axioms.chebyshev_theta_asymptotic

   #print axioms Zeta5.zeta5_irrational
   ```

   `lake env lean cert/Check.lean` compiles it and prints

   ```
   'Zeta5.zeta5_irrational' depends on axioms: [propext,
    Classical.choice,
    Quot.sound,
    Zeta5.Axioms.chebyshev_theta_asymptotic]
   ```

5. **Kernel replay.** `lake env leanchecker --verbose Zeta5` loads the compiled modules in a
   fresh process and re-checks every declaration with Lean's kernel alone, so that no code in
   the project can have added a declaration without kernel checking. It takes about 50 minutes.

6. **Browse (optional).** In VS Code with the "Lean 4" extension, open the repository folder.
   `Zeta5/Interface.lean` states each numbered result of the paper that the proof of
   Theorem 1.1 uses and is a good place to start.

`docs/CERTIFICATION.md` summarizes what these steps establish and what must be trusted.

## Map from the paper to the files

All files are in `Zeta5/`; `Zeta5.lean` imports all of them. `Interface.lean` has, for each
numbered statement of the paper that Theorem 1.1 goes through, one declaration whose type
transcribes the printed statement, so the transcription can be checked against the paper
without reading any proof.

| Paper | File | Contents |
|---|---|---|
| Definitions throughout | `Basic.lean` | The parameters (2.1), D_m, H^{(5)}_j, μ_X (2.2)–(2.3), G_K, Δ_K, F_K, S_K (2.4)–(2.6), the weight w of (2.10), the allocations and weights of §4, the functions of §5, ζ(5), the margins (7.2). |
| §1.1, Theorem 2.1 ⟹ Theorem 1.1 | `Skeleton.lean` | The irrationality criterion. |
| §2 | `Functional.lean` | μ_X is well defined, affine in X, with leading coefficient (2.9); deg Δ_K = h; (2.2) via Euler's formula for ζ at even integers. |
| §2.4, the pole integral of p. 5 | `Hermite.lean` | ∫₀^∞ w(y)/(y²+a²) dy = a⁴ζ(5,a) − 1/(2a) − 1/4 for a > 0. |
| §2.4, Proposition 2.2 | `Positivity.lean` | (2.10) and positive definiteness of G_K(ζ(5)). |
| §3.1–3.2 | `LocalFunctional.lean` | The functionals L and τ, τ(x^d) = κ_d, (3.1)–(3.3), the extension τ^ext, Lemma 3.1 for partial sums. |
| §3.2, Proposition 4.1 | `Section3.lean` | (4.2)/(4.3) and the assembly of Proposition 4.1. |
| §3.3, Lemma 3.3 | `Lemma33.lean` | Lemma 3.3 and the pullback (3.1). |
| §3.3, (3.11)–(3.12) | `CrudeBound.lean` | The basis q_i, f_i, (3.11), (3.12). |
| §3.1, §3.3, §5, §7 | `Arithmetic.lean` | Von Staudt–Clausen, integer-valued polynomials, Legendre's formula for v_p(S_K) (5.3), Theorem 2.1 from its inputs, the margin (7.2). |
| §4.1 | `Counting.lean` | The counts ℓ_A(a), the inequality of p. 10, L_a ≥ 0. |
| §4.1 | `Section41.lean` | The allocation (4.4) and its existence, the bounds on T, the weights (4.6)–(4.8), Proposition 4.1 from the entry bounds. |
| §4.1, entry bounds for (4.5) | `InnerTate.lean`, `InnerGeneral.lean`, `InnerEntries.lean` | Raabe's multiplication theorem for τ, the per-class bound, the general local bound, the entry bounds (4.2)/(4.3). |
| §4.1–4.2, unimodularity | `HermiteBasisCore.lean`, `HermiteBasis.lean` | A basis reducing mod p to a Hermite-interpolation basis is ℤ_p-unimodular. |
| §4.2, Lemma 4.2 | `Lemma42.lean` | Lemma 4.2 (4.13). |
| §4.2 | `OuterLocal.lean` | H^{(5)}_{p−a} ≡ H^{(5)}_{a−1} (mod p) and the divided-difference integrality of p. 12. |
| §4.2, (4.10)–(4.12) | `OuterBasis.lean` | The basis (4.11), (4.10) with rank L ≤ r_p, the entry bounds behind (4.12). |
| §4.2, Proposition 4.3 | `OuterRange.lean` | The table on p. 13, (4.14), Proposition 4.3. |
| §5, Proposition 5.1 | `Normalization.lean` | The Gauss valuation, v_p(m_{K,M}), Proposition 5.1. |
| §5.1–5.2, (5.7) | `Uniformity.lean` | (5.7) and the two displays of §5.2, with C = 400M². |
| §5, partial summation (p. 15) | `PNT.lean` | X⁻¹ Σ_{aX<p≤bX} φ(p/X) log p → ∫_a^b φ for φ bounded and continuous off a finite set, from θ(x) ~ x. |
| §5, Proposition 5.2 | `PrimeSum.lean` | The three-range decomposition of log m_{K,M} and (5.11). |
| §5.3, (5.15)–(5.17) | `Tail.lean` | The two integrations by parts. |
| Appendix B, (5.8)–(5.18) | `AppendixB.lean` | (B.1), the 143 affine pieces of (B.2), Tables 3 and 4, (5.10), (5.18). |
| §6, Appendix A | `RealBound.lean` | Table 1, (A.10)/(6.4), Table 2's tiling, (6.11), (6.15), (6.16) from (6.14). |
| §6, (6.14), Proposition 6.3 | `Sec6/Final.lean` | `RealBound.eq_6_14` and `RealBound.prop_6_3`; the module docstring gives the route. |
| §6, Appendix A, shared data | `Sec6/Defs.lean`, `Sec6/Measures.lean` | The regularized kernel, its energy, the arcsine measures and ρ, U^ρ, the field V of (6.1) and its closed form (A.5), the configuration bound. |
| §6.2, (6.10)–(6.13) | `Sec6/Gram.lean` | Andréief's identity (6.10), (6.12), (6.13), and (6.14) from a configuration bound. |
| §6.1, (6.6)–(6.9) | `Sec6/Energy.lean` | The configuration bound. |
| §6.1, Lemma 6.2 | `Sec6/CND.lean`, `Frullani.lean`, `GaussPD.lean`, `Swap.lean` | The zero-mass energy inequality for the regularized kernel. |
| §6.1, the cross term | `Sec6/RhoCross.lean`, `SmoothArc.lean`, `SmoothErr.lean`, `SmoothAux.lean`, `Antideriv.lean` | The smoothing error and the cross term. |
| Appendix A, (A.1) | `Sec6/LogCos.lean`, `LogCosInt.lean`, `LogCosOn.lean`, `LogCosOff.lean`, `ArcsinePot.lean` | The arcsine potential. |
| Appendix A, (A.2) | `Sec6/RhoEnergy.lean`, `PairEnergy.lean`, `ArcComm.lean`, `Bilinear.lean`, `IrhoSum.lean` | I(ρ) ≤ I_k(ρ, ρ) for the regularized kernel. |
| Appendix A, (A.5) | `Sec6/Field.lean` | The closed form of V. |
| §6.1, (6.2), (6.7), (6.8); Lemma 6.1 | `Sec6/Potential.lean`, `Sec6/Num/*.lean` | 2U^ρ − V ≤ M₀ by certified interval arithmetic (`decide +kernel`) on 1049 cells of [0, 2] and 2 of [2, 4], and an analytic bound for t ≥ 4. |
| §7, (5.21), (7.1) | `Asymptotics.lean` | (5.21) from (5.11), (7.1) from (5.21) and (6.16). |
| §7, Theorems 2.1 and 1.1 | `Interface.lean` | The named statements, Theorem 2.1 at M = 200, `zeta5_irrational`. |
| — | `Axioms.lean` | The prime number theorem θ(x) ~ x. |
| — | `Checks.lean`, `AppendixBCheck.lean` | Known-answer controls on the definitions; type-level checks that `AppendixB.lean` proves the statements in `Interface.lean`. |

## Deviations from the paper

The formal proof passes through the paper's intermediate statements. At the places below, a
step is proved by a different argument from the paper's, or a statement is formalized in a
different but equivalent or stronger form. Each is recorded in the docstring of the
declaration concerned; `docs/STATUS.md` has the full list.

1. **Lemma 3.2 (3.7), with its far poles.** The Tate algebra ℚ_p⟨z⟩, (3.5) and C_p of (3.6)
   are not formalized. The valuation bound that Proposition 4.1 needs from (3.7) is proved
   directly: Raabe's multiplication theorem m⁴τ(P) = Σ_{a<m} τ(P(a + mz))
   (`InnerEntries.raabe_tau`) for the polynomial part, and a truncated inverse of the far-pole
   factor with explicit remainder (`InnerEntries.class_bound`) for the far poles.
2. **Lemma 3.3, polynomial part.** Lemma 3.3 is proved as printed (`Lemma33.lemma_3_3`). For the
   polynomial part, the numerator is expanded in the binomial basis C(x + K, k) and τ of each
   quotient is computed exactly, in place of the two-scale estimate and (3.8)–(3.9). The term
   −v_p(24) of (3.10) is shown to be unnecessary (`Lemma33.lemma_3_3_strong`).
3. **Unimodularity of (4.5) and (4.11).** Both are derived from one lemma,
   `HermiteBasis.det_coeffMatrix_unimodular`: a basis of integer polynomials that reduces mod p
   to a Hermite-interpolation basis with distinct nodes is ℤ_p-unimodular.
4. **The inequality b_a ≤ 6αx + 3 on p. 10.** The paper states it after (4.4) without proof;
   it does not follow from (4.4). It is equivalent to p·ℓ_N(a) ≤ 2N + p and is proved in strict
   form (`ell_lt`, `bCoef_lt_real`). The weaker bound from ℓ_N(a) ≤ 2⌊N/p⌋ + 2 does not suffice
   (`naive_bound_insufficient`).
5. **The divided-difference step on p. 12** uses, besides the congruence the paper cites, the
   term −1/4 + 1/(2j) of the pole values (2.3) (`OuterLocal.muPole_divided_difference`); the
   congruence alone leaves a residue −1/a (`OuterLocal.muPole_tail_is_needed`).
6. **(4.10).** The vanishing L_ij = 0 for i + j < K − 6N + 2p − 3 is proved in the monomial
   basis (`OuterBasis.L0_eq_zero`), and rank L ≤ r_p is transported to the basis (4.11), which
   Proposition 4.3 uses.
7. **(5.16)–(5.17)** are proved in the combined form that (5.18) uses, a bound on
   ∫_{20}^{M} R(x) x^{−3} dx (`AppendixB.eq_5_16_5_17`).
8. **The pole integral of p. 5** (`Hermite.pole_integral`) is proved without Hermite's formula
   and the four integrations by parts: w is expanded as its defining series, each term is
   rescaled, the sum is evaluated with the Mittag-Leffler expansion of the cotangent (Mathlib's
   `cot_series_rep'`), and the remaining Laplace integrals give a⁴ζ(5, a).
9. **Partial summation (p. 15)** (`PNT.prime_riemann_sum`) is proved from θ(x) ~ x by a
   Darboux-type sandwich over a uniform partition of [a, b].
10. **(6.6)–(6.9).** The paper regularizes the points by circles of radius ε in ℂ and applies
    Lemma 6.2 to log|z − w|. Here the points stay on the real line and the kernel is
    regularized, kC ε(x) = ½ log(x² + ε²) ≥ log|x|, with ε = (16K)⁻². The zero-mass inequality
    is proved for kC ε from a Frullani representation and positive definiteness of the Gaussian
    kernel. The smoothing error is bounded directly, in place of the mass bound and 60√ε of
    p. 19. The configuration bound obtained is 2h log K + 20h (the paper: (120 + √2)h + 2h log K).
11. **(A.2)** is used as the inequality I(ρ) ≤ I_k(ρ, ρ) for the regularized kernel
    (`Sec6.rho_energy_ge`); `Irho` in the statement of (6.14) is the closed form (A.2).
12. **(6.10)–(6.13).** The factor 1/h! of (6.10) is kept to (6.14), and ∫₀^∞(1+y)⁵e^{−y/K}dy ≤
    326K⁶ replaces the constant 652.
13. **(6.2) on [0, 2]** is proved by certified interval arithmetic on the closed forms (A.1) and
    (A.5), on a partition of 1049 cells generated by `numerics/sec6/gen_lean.py`, each checked
    by `decide +kernel`, in place of the bound (A.9) on the 684 cells of Table 2. That Table 2
    tiles [0, 2] is proved (`RealBound.table2_tiles`); (A.9) is not formalized. For t ≥ 2,
    two certified cells cover [2, 4] and an analytic bound covers t ≥ 4, in place of (6.8).

## Ground rules

Lean docstrings that mention "the README" refer to this section.

* **Nothing internal to the paper's argument is an axiom.** Every proposition, lemma,
  equation, computation and table of the paper that the proof uses is proved in Lean.
* **Only standard external facts may be axioms**, declared in `Zeta5/Axioms.lean` with the
  precise statement, a citation, and the reason Mathlib lacks it.
* **Finite computations are proved**, by exact rational arithmetic (`norm_num`, `decide`) or
  certified enclosures. The files in `Zeta5/` contain no `native_decide`, `implemented_by` or
  `extern`.
* **Statements transcribe the printed ones.** Where a formal statement differs from the printed
  one, its docstring says how and in which direction.
* **Known-answer controls.** `Zeta5/Checks.lean` evaluates definitions at values computed by
  hand from the paper.

## Provenance

The Lean code and the documentation were written by Claude (Anthropic), using the models
Claude Opus 5 and Claude Opus 5.5, working as multi-agent workflows in Claude Code directed by
Dan Romik, in September 2026. The formalization was written without consulting any other
formalization of the preprint.

`docs/zeta5-audit.pdf` (source `docs/zeta5-audit.tex`) is a referee-style audit of the preprint
made before the formalization, cited in docstrings as "the audit". It identifies the
inequality of p. 10 (deviation 4) as asserted without proof and supplies a proof.

The validity of what Lean checks does not depend on how the proofs were produced. To accept
the result, a reader needs to trust Lean's kernel and check two statements: that of
`cert/Check.lean` (with Mathlib's definitions of `Irrational` and `tsum`), and the axiom (with
Mathlib's definition of `Chebyshev.theta`). Whether the intermediate statements in
`Zeta5/Interface.lean` transcribe the paper's bears on the claim that this is Fauzan's proof,
not on the correctness of the theorem.

## Reference

Aabir Fauzan, "ζ(5) is irrational", preprint, 17 September 2026. Zenodo,
[doi:10.5281/zenodo.22826418](https://doi.org/10.5281/zenodo.22826418) (all versions). The
formalization follows version v1,
[doi:10.5281/zenodo.22826419](https://doi.org/10.5281/zenodo.22826419); page and equation
numbers refer to v1. The preprint is not included here.

## Further documentation

* `docs/CERTIFICATION.md`: what the checks establish and what must be trusted.
* `docs/STATUS.md`: what is proved, section by section, and the complete list of deviations.
* `docs/lean-status.pdf` (source `docs/lean-status.tex`): a typeset summary.
* `docs/zeta5-audit.pdf`: the referee audit of the preprint.
* `cert/Check.lean`: the statement check (not part of `lake build`).
* `numerics/`: exact-arithmetic and numerical tests used during development to check
  intermediate statements before they were formalized (Python with `sympy`, `mpmath`, `numpy`;
  the `outerbasis/` scripts use SageMath). They are not part of the verification.
