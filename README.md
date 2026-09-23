# ζ(5) is irrational: a Lean 4 formalization of A. Fauzan's preprint

[![Lean Action CI](https://github.com/danromik/zeta5-irrationality/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/danromik/zeta5-irrationality/actions/workflows/lean_action_ci.yml)

This repository contains a formalization, in the Lean 4 proof assistant with the Mathlib
library, of the proof in A. Fauzan's preprint *"ζ(5) is irrational"* (dated 17 September
2026). The Lean development follows the paper section by section. It defines the paper's
objects (the functional μ_X, the Hankel matrices G_K and their determinants Δ_K, the
normalized polynomials Q_{K,M}, the allocations of §4, the limiting functions of §5, the
constants of Appendix A), states the paper's propositions and lemmas, and proves them, up to
Theorem 1.1. Two classical results that Mathlib does not yet contain are entered as axioms.
One inequality of the paper, (6.14), is left as an explicitly marked unproved step (a
`sorry`). Every other statement on the paper's route to Theorem 1.1 is proved in Lean. Three
of the proved steps use a different argument from the paper's (see
[Deviations from the paper](#deviations-from-the-paper)). The development has 32 Lean files,
about 24,000 lines, and builds with Lean 4.34.0 and Mathlib v4.34.0.

## The result

**Lean verifies an implication.** Lean checks a proof that ζ(5) is irrational **assuming**
three statements:

1. **Hermite's integral formula** for the Hurwitz zeta function (DLMF 25.11.29), in the form
   displayed on p. 5 of the paper. This is the axiom `Zeta5.Axioms.hermite_pole_integral`.
2. **The prime number theorem**, in the Riemann-sum form that the proof of Proposition 5.2
   uses. This is the axiom `Zeta5.Axioms.pnt_prime_riemann_sum`.
3. **The paper's inequality (6.14)**, the logarithmic-energy bound of §6. This is the unproved
   theorem `Zeta5.RealBound.eq_6_14`.

(1) and (2) are classical results that are not yet in Mathlib. (3) is a claim of the paper
itself, and the paper's proof of it has not been formalized. So this repository contains a
machine-checked proof of the implication

> (1) and (2) and (3) ⟹ ζ(5) is irrational,

not a machine-checked proof that ζ(5) is irrational.

### The main theorem

Both declarations are in the namespace `Zeta5`:

```lean
-- Zeta5/Basic.lean
/-- `ζ(5) = ∑_{v ≥ 1} v^{-5}`. -/
def zeta5 : ℝ := ∑' v : ℕ, (1 : ℝ) / ((v : ℝ) + 1) ^ 5

-- Zeta5/Interface.lean
theorem zeta5_irrational : Irrational zeta5 :=
  theorem_1_1 stdAlloc (theorem_2_1 stdAlloc)
```

The theorem has no hypotheses. `Irrational` is Mathlib's predicate
(`Irrational x` means `x ∉ Set.range ((↑) : ℚ → ℝ)`), and `∑'` is Mathlib's sum of a
summable series. `theorem_1_1` (`Zeta5/Skeleton.lean`) is the deduction "Theorem 2.1 ⟹
Theorem 1.1". `theorem_2_1` (`Zeta5/Interface.lean`) assembles Theorem 2.1 at M = 200 from
Propositions 2.2 and 5.1, (2.9) and (2.7). `stdAlloc` is a choice of the allocations (4.4),
and their existence is proved. Separately, `cert/C3Semantics.lean` proves
`((zeta5 : ℝ) : ℂ) = riemannZeta 5`, where `riemannZeta` is Mathlib's Riemann zeta function,
with no `sorry` and no axiom of this project. That file is not part of the build.

### The one unproved step: (6.14)

In the paper's notation (K = 40n, N = 3n, h = 37n, λ = 37/40), (6.14) is the upper bound

    log Δ_K(ζ(5)) ≤ 2h(h + 6N − K) log K + (λM₀ − I(ρ))K² + 18h log K + 160h

for the Hankel determinant Δ_K of (2.4) evaluated at ζ(5). In Lean:

```lean
-- Zeta5/RealBound.lean, namespace Zeta5.RealBound
theorem eq_6_14 (n : ℕ) (hn : 0 < n) (hΔpos : 0 < evalZeta5 (Delta n)) :
    Real.log (evalZeta5 (Delta n))
      ≤ 2 * (h n : ℝ) * ((h n : ℝ) + 6 * (N n : ℝ) - (K n : ℝ)) * Real.log (K n : ℝ)
        + ((lam : ℝ) * M0 - Irho) * (K n : ℝ) ^ 2
        + 18 * (h n : ℝ) * Real.log (K n : ℝ) + 160 * (h n : ℝ) := by
  sorry
```

Here `M0 = -1329/200`, and `Irho` is the closed form (A.2) of the logarithmic energy I(ρ),
computed from the entries of Table 1. The hypothesis `0 < Δ_K(ζ(5))` follows from
Proposition 2.2 and is proved (`Zeta5.delta_pos`).

**(6.14) is where the paper's analytic estimate lives, and it is the one unformalized step.**
The paper's proof of it uses:

* Andréief's identity (6.10), which writes Δ_K(ζ(5)) as an h-fold integral. It also uses the
  comparison of the resulting discrete energy with the continuous one: the Riemann-sum
  bound (6.12) and the scaling (6.13).
* Lemma 6.1, the potential inequality (6.2), 2U^ρ(t) − V(t) ≤ M₀. For t ∈ [0, 2] the paper
  verifies it through Appendix A, by evaluating (A.9) on the 684 dyadic cells of Table 2.
* Lemma 6.2 (I(ν) ≤ 0 for a signed measure ν of total mass zero), applied as in (6.6)–(6.9).
* The identification of the closed form (A.2) with the logarithmic energy of ρ.

None of this is formalized. Everything downstream of (6.14) is proved: Proposition 6.3, i.e.
(6.16) from (6.14) and (6.15) (`Zeta5.RealBound.prop_6_3_of`), then (7.1), Theorem 2.1 and
Theorem 1.1. (6.15) and the margin (7.2) are proved as well. The following finite parts of
Appendix A are also proved: Table 1's verifications, and (A.10)/(6.4), λM₀ − I(ρ) + C_* ≤ Ū,
from certified rational enclosures of the logarithms involved (`Zeta5.RealBound.eq_6_4`).
The fact that Table 2's 684 cells tile [0, 2] is proved too (`Zeta5.RealBound.table2_tiles`),
but the main proof does not use it, because the evaluations on those cells belong to (6.14).

As a consistency check of the transcription, the Lean statement of (6.14) was evaluated at
n = 1, 2, 3 (K = 40, 80, 120). The exact values of Δ_K(ζ(5)) came from the referee audit
described under [Provenance](#provenance). The inequality holds with a large margin
(`cert/c3/eq_6_14_control.py`, `cert/c3/eq_6_14_control.out`). This check says nothing
about large K.

### The two axioms

Both axioms are in `Zeta5/Axioms.lean`, the only file of the project that declares any axiom.
Each docstring gives the precise statement, a literature citation, and the reason Mathlib
lacks it.

* **`hermite_pole_integral`.** For a > 0,
  ∫₀^∞ w(y)/(y² + a²) dy = a⁴ ζ(5, a) − 1/(2a) − 1/4. Here
  w(y) = (2π)⁴ y⁵ Σ_{ℓ≥1} ℓ⁴ e^{−2πℓy}/12 is the weight of (2.10), and
  ζ(5, a) = Σ_{k≥0} (k + a)^{−5}. This is the display on p. 5 of the paper, which the paper
  derives from Hermite's formula (DLMF 25.11.29) by four integrations by parts. Those
  integrations by parts are not formalized, so the axiom is Hermite's formula already carried
  through them. It is used only for Proposition 2.2.
* **`pnt_prime_riemann_sum`.** For 0 ≤ a < b and φ bounded on [a, b] and continuous off a
  finite set, X⁻¹ Σ_{aX < p ≤ bX, p prime} φ(p/X) log p → ∫_a^b φ(y) dy as X → ∞. This is the
  prime number theorem (θ(x) ~ x) combined with partial summation, in the form the paper
  invokes on p. 15. The partial-summation step is not formalized. It is used only for
  Proposition 5.2.

Both axioms are stated for general parameters, and neither contains information specific to
the paper's construction. The only definition of this project that either one mentions is the
explicit weight w of (2.10), written out above. Both were checked numerically: the first to
about 40 digits at values of a from 0.01 to 1000, and the second on several test functions up
to X = 10⁷ (`cert/c3/axioms_numeric.py` and its output). It was also checked in Lean that the
second axiom implies (θ(2X) − θ(X))/X → 1, so it is not vacuous (`cert/C3Attack.lean`; see
`docs/CERTIFICATION.md`).

### The assumption report

Every `lake build` compiles `Zeta5/Audit.lean`. That file walks the dependency graph of
`Zeta5.zeta5_irrational` and prints its assumptions, sorted by kind. Verbatim:

```
info: Zeta5/Audit.lean:203:0: ASSUMPTION REPORT for Zeta5.zeta5_irrational

  (A) standard Lean axioms:
    Classical.choice
    Quot.sound
    propext

  (B) explicit external axioms of this project (Zeta5/Axioms.lean):
    Zeta5.Axioms.hermite_pole_integral
    Zeta5.Axioms.pnt_prime_riemann_sum

  (C) sorry(s) — unfinished steps of the paper's own argument, 1 in all:
    Zeta5.RealBound.eq_6_14

  (D) any other axiom (must be empty):
    (none)

  [self-check: walker agrees with Lean.collectAxioms, 6 axiom(s)]
```

The last line records that the walker's result agrees with Lean's own `Lean.collectAxioms`.
The build then prints

```
info: Zeta5/Audit.lean:262:0: every sorry of the Zeta5 namespace is used by Zeta5.zeta5_irrational.
```

So the project contains no other `sorry`. Lean's built-in `#print axioms` gives the same list.
In it, `sorryAx` stands for the `sorry` in (6.14):

```
'Zeta5.zeta5_irrational' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 Zeta5.Axioms.hermite_pole_integral,
 Zeta5.Axioms.pnt_prime_riemann_sum]
```

`propext`, `Classical.choice` and `Quot.sound` are the three standard axioms of Lean's logic
(propositional extensionality, the axiom of choice, and soundness of quotients). Essentially
all of Mathlib uses them.

`Audit.lean` also reports, for each named intermediate statement, whether it depends on the
`sorry`. Only Theorem 2.1, Proposition 6.3 and (7.1) do, through (6.14). For example,
Propositions 2.2, 4.1, 4.3, 5.1 and 5.2, (2.9), (3.12) and (5.16)–(5.18) all print
`depends on NO sorry`, and `Zeta5.theorem_1_1` (Theorem 2.1 ⟹ Theorem 1.1) depends only on
the three standard axioms.

### What is machine-checked

Everything on the paper's route to Theorem 1.1 apart from (6.14) is machine-checked. That
covers §2 (the functional μ_X, (2.9), and Proposition 2.2 modulo Hermite's formula), §3
(Lemma 3.3, (3.11), (3.12)) and §4 (Propositions 4.1 and 4.3 with both p-adic local
analyses). It covers §5 (Propositions 5.1 and 5.2, the latter modulo the prime number
theorem; (5.7) with an explicit uniform constant; the tail estimates (5.15)–(5.17); all of
Appendix B), the part of §6 downstream of (6.14), and §7. The finite computations the paper
relies on outside (6.14) are carried out in Lean by exact rational arithmetic and certified
enclosures, not assumed. These are Appendix B's 143 intervals and its Tables 3 and 4, Table 1
and the constants of Appendix A.4, and the margin (7.2).

## How to check it yourself

You need a Unix-like shell (macOS, Linux, or WSL on Windows), `git`, and about 8 GB of disk
space. Most of that space is for the compiled Mathlib library.

1. **Install elan**, the Lean toolchain manager (instructions at
   <https://github.com/leanprover/elan>). On macOS and Linux:

   ```sh
   curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
   ```

   You do not need to choose a Lean version: elan reads the file `lean-toolchain` and installs
   Lean 4.34.0 automatically.

2. **Clone the repository:**

   ```sh
   git clone https://github.com/danromik/zeta5-irrationality.git
   cd zeta5-irrationality
   ```

3. **Download the compiled Mathlib library:**

   ```sh
   lake exe cache get
   ```

   Without this step, `lake build` would compile Mathlib from source, which takes hours. The
   exact Mathlib commit is pinned in `lake-manifest.json`.

4. **Build the formalization:**

   ```sh
   lake build
   ```

   This compiles the 32 files of this project. It took about four to five minutes on the
   machine used for development. What to look for in the output:
   * the assumption report shown above, among many `info:` lines (the other `info:` lines are
     `#print axioms` checks on intermediate results, and they are expected);
   * exactly one warning `declaration uses 'sorry'`, at `Zeta5/RealBound.lean` (this is
     (6.14));
   * about 250 other warnings, all of them Mathlib deprecation notices and style lints
     (`if_pos`/`if_neg` deprecations, unused `simp` arguments, and similar), which do not
     affect correctness;
   * the final line `Build completed successfully`.

   Running `lake build` again after a successful build replays the stored messages, including
   the assumption report, without recompiling.

5. **Ask Lean directly.** Create a file `Check.lean` in the repository root containing

   ```lean
   import Zeta5
   #check @Zeta5.zeta5_irrational
   #print Zeta5.zeta5
   #print axioms Zeta5.zeta5_irrational
   ```

   and run `lake env lean Check.lean`. The output is

   ```
   Zeta5.zeta5_irrational : Irrational Zeta5.zeta5
   def Zeta5.zeta5 : ℝ :=
   ∑' (v : ℕ), 1 / (↑v + 1) ^ 5
   'Zeta5.zeta5_irrational' depends on axioms: [propext,
    sorryAx,
    Classical.choice,
    Quot.sound,
    Zeta5.Axioms.hermite_pole_integral,
    Zeta5.Axioms.pnt_prime_riemann_sum]
   ```

   `#print axioms` works the same way for any declaration of the project.

6. **Browse interactively (optional).** Install [VS Code](https://code.visualstudio.com/) and
   its "Lean 4" extension, run step 3 first, then open the repository folder
   (File → Open Folder). When you open a file, Lean checks it and shows its messages in the
   "Lean Infoview" panel. Put the cursor on `#print axioms Zeta5.zeta5_irrational` at the end
   of `Zeta5/Audit.lean` to see its output. Hovering over a name shows its type and docstring.
   Ctrl-click (Cmd-click on macOS) on a name jumps to its definition. `Zeta5/Interface.lean`
   is a good file to start reading: it states each numbered result of the paper that the proof
   of Theorem 1.1 uses.

7. **Kernel replay (optional, about 25 minutes).** `lake env leanchecker --verbose Zeta5`
   re-checks every declaration of every module with Lean's kernel, independently of the
   elaborator. The recorded run is `cert/c3/leanchecker.out`.

## Map from the paper to the files

All files are in `Zeta5/`, and `Zeta5.lean` imports all of them. `Interface.lean` is the table
of contents. For each numbered statement of the paper that Theorem 1.1 goes through, it has
one declaration whose type is a transcription of the printed statement, so the transcription
can be checked against the paper without reading any proof.

| Paper | File | Contents |
|---|---|---|
| Definitions throughout | `Basic.lean` | Definitions only: the parameters (2.1), D_m, H^{(5)}_j, μ_X (2.2)–(2.3), G_K, Δ_K, F_K, S_K (2.4)–(2.6), the weight w of (2.10), the allocations and weights of §4, the functions of §5, and ζ(5) itself. Also the exact margins (7.2). |
| §1.1, Theorem 2.1 ⟹ Theorem 1.1 | `Skeleton.lean` | The irrationality criterion: integer polynomials of degree ≤ 37n, positive at ξ and smaller than exp(−139n²/5). |
| §2 | `Functional.lean` | μ_X is well defined (partial fractions, uniqueness), affine in X, and has leading coefficient (2.9), so deg Δ_K = h. It also identifies (2.2) with values of ζ at even integers via Euler's formula. |
| §2.4, Proposition 2.2 | `Positivity.lean` | (2.10) and positive definiteness of G_K(ζ(5)). Uses the axiom `hermite_pole_integral`. |
| §3.1–3.2 | `LocalFunctional.lean` | The functionals L and τ, τ(x^d) = κ_d, (3.1)–(3.3), the extension τ^ext, and Lemma 3.1 for partial sums. |
| §3.2 and Proposition 4.1 | `Section3.lean` | What is and is not formalized of Lemma 3.2, the derivation of (4.2)/(4.3), and the statement and assembly of Proposition 4.1. |
| §3.3, Lemma 3.3 | `Lemma33.lean` | Lemma 3.3 as printed, and the pullback (3.1) for every μ_X(B/D_tail). |
| §3.3, (3.11)–(3.12) | `CrudeBound.lean` | The basis q_i, f_i, the determinant identity (3.11), and the crude bound (3.12). |
| §3.1, §3.3, §5, §7 | `Arithmetic.lean` | Von Staudt–Clausen, integer-valued polynomials and the binomial basis, Legendre's formula for v_p(S_K) (5.3), Theorem 2.1 from its inputs (as an implication), and the margin (7.2). |
| §4.1 | `Counting.lean` | The counts ℓ_A(a), **the p. 10 inequality**, and L_a ≥ 0. |
| §4.1 | `Section41.lean` | The allocation (4.4) and its existence, the bounds on T, the weights (4.6)–(4.8), the dimension identity, and Proposition 4.1 from the entry bounds. |
| §4.1, entry bounds for (4.5) | `InnerTate.lean`, `InnerGeneral.lean`, `InnerEntries.lean` | Raabe's multiplication theorem for τ, the per-class bound with a truncated inverse, the general local bound, and the entry bounds (4.2)/(4.3) in the basis (4.5). |
| §4.1 and §4.2, unimodularity | `HermiteBasisCore.lean`, `HermiteBasis.lean` | A basis that reduces mod p to a Hermite-interpolation basis is ℤ_p-unimodular. Used for both (4.5) and (4.11). |
| §4.2, Lemma 4.2 | `Lemma42.lean` | Lemma 4.2 (4.13) over an abstract valued field, with a counterexample showing that half-integrality is needed. |
| §4.2 | `OuterLocal.lean` | A p-adic congruence calculus, the congruence H^{(5)}_{p−a} ≡ H^{(5)}_{a−1} (mod p), and the divided-difference integrality of p. 12. |
| §4.2, (4.10)–(4.12) | `OuterBasis.lean` | The basis (4.11), the splitting (4.10) with rank L ≤ r_p, and the entry bounds behind the weights (4.12). |
| §4.2, Proposition 4.3 | `OuterRange.lean` | The table on p. 13, (4.14), and Proposition 4.3 (both assertions). |
| §5, Proposition 5.1 | `Normalization.lean` | The Gauss valuation, v_p(m_{K,M}), and Proposition 5.1 prime by prime. |
| §5.1–5.2, (5.7) | `Uniformity.lean` | (5.7) and the two displays of §5.2, with the explicit constant C = 400M². |
| §5, Proposition 5.2 | `PrimeSum.lean` | The three-range decomposition of log m_{K,M} and (5.11). Uses the axiom `pnt_prime_riemann_sum`. |
| §5.3, (5.15)–(5.17) | `Tail.lean` | The two integrations by parts, on finite intervals. |
| Appendix B, (5.8)–(5.18) | `AppendixB.lean` | (B.1), the 143 affine pieces of (B.2), Tables 3 and 4, (5.10), and (5.18) exactly. |
| §6 and Appendix A | `RealBound.lean` | Table 1, (A.10)/(6.4), Table 2's tiling, (6.11), (6.15), and (6.16) from (6.14). **Contains the one `sorry`, `eq_6_14`.** |
| §7, (5.21) and (7.1) | `Asymptotics.lean` | (5.21) from (5.11), and (7.1) from (5.21) and (6.16). |
| §7, Theorems 2.1 and 1.1 | `Interface.lean` | The named statements, Theorem 2.1 at M = 200, and `zeta5_irrational`. |
| (not in the paper) | `Axioms.lean` | The two axioms. |
| (not in the paper) | `Audit.lean` | The assumption report, recomputed on every build. |
| (not in the paper) | `Checks.lean`, `AppendixBCheck.lean` | Known-answer controls on the definitions (values computed by hand from the paper and re-derived by Lean), and type-level checks that `AppendixB.lean` proves exactly the statement in `Interface.lean`. |

## Deviations from the paper

The formal proof follows the paper's argument through the same intermediate statements. It
differs from the paper at the places listed here. `docs/STATUS.md` lists these and some smaller
differences of form, and each one is also recorded in the docstring of the declaration
concerned.

### Three steps proved by a different route

In each case, the statement the rest of the proof needs is proved, but the paper's own proof of
that step is bypassed rather than checked line by line.

1. **Lemma 3.2, the distribution formula (3.7), with its far poles.** The Tate algebra
   ℚ_p⟨z⟩, the far-pole expansion (3.5) and the constant C_p of (3.6) are not formalized, and
   (3.7) is not stated as an equation. What Proposition 4.1 needs from it is a valuation bound
   on each entry of the Gram matrix in the basis (4.5), and that bound is proved directly by
   exact finite identities. The polynomial case of (3.7) is Raabe's multiplication theorem,
   m⁴τ(P) = Σ_{a<m} τ(P(a + mz)), proved from Mathlib's Bernoulli-number identities
   (`Zeta5.InnerEntries.raabe_tau`). The far poles are handled by a *truncated* inverse of the
   far-pole factor with an explicit remainder (`Zeta5.InnerEntries.class_bound`). Together
   these give `Zeta5.InnerEntries.general_bound`. Lemma 3.1 is proved for every partial sum
   Σ_{j≤J} p^j U_j rather than for series in the Tate algebra (`Zeta5.lemma_3_1`), but the
   main proof no longer uses it.
2. **The polynomial part of the proof of Lemma 3.3.** Lemma 3.3 is proved as printed
   (`Zeta5.Lemma33.lemma_3_3`), and its pole terms are handled as in the paper. For the
   polynomial part, the paper uses a two-scale estimate and the bounds (3.8)–(3.9). Instead,
   the numerator is expanded in the binomial basis C(x + K, k), and τ of each quotient is
   computed exactly. (3.8) and (3.9) are not formalized. The proof also shows that the term
   −v_p(24) in (3.10) is unnecessary (`Zeta5.Lemma33.lemma_3_3_strong`).
3. **Unimodularity of the local bases (4.5) (p. 10) and (4.11) (p. 12).** The paper gives two
   different justifications: triangular local bases with unit diagonal entries, and local
   polynomials that are monic of successive degrees with unit resultants. Both are replaced by
   one lemma, `Zeta5.HermiteBasis.det_coeffMatrix_unimodular`. It says that a basis of integer
   polynomials that reduces mod p to a Hermite-interpolation basis with distinct nodes is
   ℤ_p-unimodular. The proof shows that the Hermite family is linearly independent over 𝔽_p
   and then counts dimensions.

### A gap in the paper, filled: the inequality b_a ≤ 6αx + 3 on p. 10

Immediately after (4.4), the paper writes "From (4.4), 2Hx − 21/20 < T < 2Hx,
b_a ≤ 6αx + 3" and gives no proof of the last inequality. That inequality does not follow
from (4.4). It is a statement about the residue counts ℓ_N(a), equivalent to
p·ℓ_N(a) ≤ 2N + p. The proof needs it: the naive bound ℓ_N(a) ≤ 2⌊N/p⌋ + 2 gives only
b_a ≤ 6αx + 6. With that bound, the paper's chain gives T − b_a > 2λx − 141/20, which is −3/2
at x = 3, and the nonnegativity of the dimensions L_a fails
(`Zeta5.naive_bound_insufficient`).

The inequality is proved here in strict form, twice: once by a divisibility argument, and once
by the explicit case split on N mod p.

* `Zeta5.ell_lt` (`Counting.lean`): p·ℓ_A(a) < 2A + p for 1 ≤ a and 2a < p, by the
  divisibility argument. This is the version the main proof uses.
* `Zeta5.ell_lt_caseSplit` (`Section41.lean`): the same statement, by the case split.
* `Zeta5.bCoef_lt_real` (`Section41.lean`): b_a < 6αx + 3, in the paper's variables.
* `Zeta5.InnerAlloc.L_nonneg` (`Counting.lean`): L_a ≥ 0, the conclusion the paper draws from
  the inequality.

### Other points where the formal proof adds to or restates the paper

* **The divided-difference step on p. 12.** The paper cites only the congruence
  H^{(5)}_{p−a} ≡ H^{(5)}_{a−1} (mod p). By itself, that congruence leaves a residue −1/a
  (`Zeta5.OuterLocal.muPole_tail_is_needed`). The proof
  (`Zeta5.OuterLocal.muPole_divided_difference`) also uses the −1/4 + 1/(2j) term of the pole
  values (2.3). The paper's conclusion is unaffected.
* **The rank bound in (4.10).** The paper's vanishing statement ("L_ij = 0 if
  i + j < K − 6N + 2p − 3. Its first h − r_p rows and columns vanish") refers to the monomial
  basis. It is proved in that basis (`Zeta5.OuterBasis.L0_eq_zero`), and the bound
  rank L ≤ r_p is then transported to the basis (4.11) that the weights (4.12) use. In the
  basis (4.11), L need not have any vanishing columns. Proposition 4.3 uses the rank form
  (`Zeta5.vanishing_of_rank`). Lemma 4.2 as printed is also proved (`Zeta5.lemma_4_2`), but
  the main proof does not use it.
* **(6.14) is stated with I(ρ) as the number (A.2)** and M₀ as −1329/200, as described
  above. The identification of (A.2) with the logarithmic energy of ρ is part of what the
  `sorry` stands for.
* **(5.16) and (5.17)** are proved in the combined form that (5.18) uses, a bound on
  ∫_{20}^{M} R(x) x^{−3} dx (`Zeta5.AppendixB.eq_5_16_5_17`). This form avoids improper
  integrals. The two separate statements of p. 16 are not stated.

## Ground rules

These rules governed the formalization, and the Lean docstrings that mention "the README"
refer to this section.

* **Nothing internal to the paper's argument is axiomatized.** Every proposition, lemma,
  equation, computation and table of the paper that the proof uses is either proved in Lean or
  left as a named `sorry`. The assumption report lists every `sorry`, and currently there is
  one.
* **Only standard external facts may be axioms.** Each one is declared in `Zeta5/Axioms.lean`
  with (i) its precise statement, (ii) a literature citation, and (iii) the reason Mathlib
  lacks it. Where an axiom is stronger than the bare citation (both current axioms are, as
  explained above), the docstring says so.
* **Finite computations are never axioms.** Every finite verification the proof uses is
  carried out in Lean by exact rational arithmetic (`norm_num`, `decide`) or certified
  enclosures. The files in `Zeta5/` contain no `native_decide`, `implemented_by` or `extern`.
* **Statements are never weakened.** Each formal statement transcribes the printed one. When
  a formal statement differs from the printed one, its docstring says how and in which
  direction (see [Deviations from the paper](#deviations-from-the-paper)). Once, an early
  transcription turned out to be false: it placed the vanishing columns of §4.2 in the
  basis (4.11). It was corrected to match the printed statement, not weakened to become
  provable.
* **The assumption list is computed, not asserted.** `Zeta5/Audit.lean` recomputes it from the
  Lean environment on every build, checks its own dependency walker against
  `Lean.collectAxioms`, and checks that no `sorry` in the project is missing from the list.
* **Known-answer controls.** Definitions are tested against values computed by hand from the
  paper (`Zeta5/Checks.lean`). Intermediate statements were tested numerically, including
  must-fail controls, before they were formalized (`numerics/`).

## Provenance

The Lean code and the documentation in this repository were written by Claude (Anthropic),
using the models Claude Opus 5 and Claude Opus 5.5. Claude worked as multi-agent workflows in
Claude Code, directed by Dan Romik, in September 2026.

Before the formalization, Claude carried out a referee-style audit of the preprint (22 pages,
dated 22 September 2026). It is included as `docs/zeta5-audit.pdf` (source
`docs/zeta5-audit.tex`). Its verdict is that the preprint as written is not a complete proof:
one load-bearing step, the inequality b_a ≤ 6αx + 3 on p. 10, is asserted without proof. The
audit supplies a proof of that step, and it found no other error. The audit is cited in
docstrings and scripts as "the audit" or "the referee audit". Its exact values of
log Δ_K(ζ(5)) at K = 40, 80, 120 are in `cert/c3/delta_K_values.json`. The audit predates the
formalization. Some steps it could only test numerically, such as Proposition 4.1, are now
proved in Lean.

Lean checks every step of every proof. Beyond trust in Lean's kernel and in Mathlib, the
validity of what is proved therefore does not depend on trusting how the proofs were produced.
Only two things need human review:

* **The faithfulness of the statements:** whether the formal statements say what the paper
  says. These are the definitions in `Zeta5/Basic.lean`, the statements in
  `Zeta5/Interface.lean`, and the statement of (6.14).
* **The assumption list:** whether the two axioms are correct statements of known results, and
  whether nothing else is assumed.

`docs/CERTIFICATION.md` describes how these were checked: a clean rebuild, independent
dependency walkers, a kernel replay, attacks on the axioms, a check of the main statement at
the level of Lean terms, and spot checks of statements against the preprint.

## Reference

Aabir Fauzan, "ζ(5) is irrational", preprint, 17 September 2026. Zenodo,
[doi:10.5281/zenodo.22826418](https://doi.org/10.5281/zenodo.22826418) (all versions). The
formalization and the audit follow version v1,
[doi:10.5281/zenodo.22826419](https://doi.org/10.5281/zenodo.22826419). All page and equation
numbers in this repository refer to v1. The preprint itself is not included here.

## Further documentation

* `docs/STATUS.md`: the detailed status. It covers what is proved, section by section; the
  assumption list with the axioms' docstrings summarized; the complete list of deviations; and
  what remains to be done for (6.14).
* `docs/CERTIFICATION.md`: the adversarial certification of the current state. It checks that
  the main theorem is faithfully stated and that it depends on exactly the assumptions listed
  above.
* `docs/lean-status.pdf` (source `docs/lean-status.tex`): a readable summary of what the
  formalization proves and assumes.
* `docs/zeta5-audit.pdf` (source `docs/zeta5-audit.tex`): the referee audit of the preprint.
  It gives a section-by-section and lemma-by-lemma assessment, the exact determinant data, and
  a proof of the inequality on p. 10.
* `cert/`: the Lean and Python scripts used by the certification, with their recorded outputs
  (see `cert/README.md`). They are not part of `lake build`.
* `numerics/`: exact-arithmetic known-answer controls, run before the corresponding Lean
  proofs were written. The Python scripts use `sympy`, `mpmath` and `numpy`, and the
  `outerbasis/` scripts use SageMath. The two `.lean` files there are run with
  `lake env lean numerics/<file>.lean` and are not part of `lake build`.
