# ζ(5) is irrational: a Lean 4 formalization of A. Fauzan's preprint

[![Lean Action CI](https://github.com/danromik/zeta5-irrationality/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/danromik/zeta5-irrationality/actions/workflows/lean_action_ci.yml)

> **Update, branch `axioms` (2026-09-24): one axiom, the prime number theorem as stated in
> textbooks.** The two former axioms of `Zeta5/Axioms.lean`, each stronger than its citation,
> are now theorems with the identical statements. `Zeta5.Hermite.pole_integral`
> (`Zeta5/Hermite.lean`, formerly the axiom `hermite_pole_integral`) is proved from Mathlib
> alone, with no axiom. `Zeta5.PNT.prime_riemann_sum` (`Zeta5/PNT.lean`, formerly the axiom
> `pnt_prime_riemann_sum`) is proved from the single new axiom
> `Zeta5.Axioms.chebyshev_theta_asymptotic`, θ(x)/x → 1 with Mathlib's own `Chebyshev.theta`.
> `Zeta5.zeta5_irrational` now rests on Lean's three standard axioms and that one axiom. This
> state has **not yet been re-certified**; the certification described below is of the
> previous state (see the addendum in `docs/CERTIFICATION.md`).
>
> **Update, branch `eq614` (2026-09-24): (6.14) is proved; the project has no `sorry`.**
> `Zeta5.RealBound.eq_6_14` (statement unchanged) is proved in `Zeta5/Sec6/Final.lean`
> through the §6 blueprint of 19 leaf statements in `Zeta5/Sec6/*.lean`, all of which are
> now proved. `lake build` completes with no `declaration uses 'sorry'` warning, and the
> assumption report of `Zeta5/Audit.lean` lists **no `sorry`**: `Zeta5.zeta5_irrational`
> rested on Lean's three standard axioms and the two external axioms that `Zeta5/Axioms.lean`
> then declared, and on nothing else. The §6 proof takes a different route from the paper at several places
> (a real-line regularisation of the kernel instead of circles, and its own certified
> partition instead of Table 2); see [(6.14): how it is proved](#614-how-it-is-proved). This
> state was re-certified on 2026-09-24 (`docs/CERTIFICATION.md`): five independent
> dependency checks, a kernel replay of all 70 modules, a kernel-level comparison with the
> 2026-09-23 state showing that no statement or definition changed, and checks of the §6
> statements against the preprint.

This repository contains a formalization, in the Lean 4 proof assistant with the Mathlib
library, of the proof in A. Fauzan's preprint *"ζ(5) is irrational"* (dated 17 September
2026). The Lean development follows the paper section by section. It defines the paper's
objects (the functional μ_X, the Hankel matrices G_K and their determinants Δ_K, the
normalized polynomials Q_{K,M}, the allocations of §4, the limiting functions of §5, the
constants of Appendix A), states the paper's propositions and lemmas, and proves them, up to
Theorem 1.1. One classical result that Mathlib does not yet contain, the prime number theorem,
is entered as an axiom.
Every statement on the paper's route to Theorem 1.1 is proved in Lean; there is no `sorry`.
(Until 2026-09-24 one inequality of the paper, (6.14), was an explicitly marked unproved step.)
Several of the proved steps use a different argument from the paper's (see
[Deviations from the paper](#deviations-from-the-paper)). The development has 71 Lean files
under `Zeta5/` (37 of them in `Zeta5/Sec6/`, the proof of (6.14)), about 29,700 lines, and
builds with Lean 4.34.0 and Mathlib v4.34.0.

## The result

**Lean verifies an implication.** Lean checks a proof that ζ(5) is irrational **assuming**
one statement:

* **The prime number theorem**, in Chebyshev's form θ(x) ~ x, where
  θ(x) = Σ_{p ≤ x} log p. This is the axiom `Zeta5.Axioms.chebyshev_theta_asymptotic`,
  stated with Mathlib's own `Chebyshev.theta`.

It is a classical result that is not yet in Mathlib, and not a claim of the paper. So this
repository contains a machine-checked proof of the implication

> the prime number theorem ⟹ ζ(5) is irrational.

Until 2026-09-24 there were two further assumptions. The paper's inequality (6.14) was a
`sorry`; it is now proved (see [(6.14): how it is proved](#614-how-it-is-proved)). And the
axioms were two stronger statements: Hermite's integral formula already carried through the
integrations by parts of p. 5, and the prime number theorem already carried through partial
summation. Both are now theorems (see [The axiom](#the-axiom)).

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

### (6.14): how it is proved

In the paper's notation (K = 40n, N = 3n, h = 37n, λ = 37/40), (6.14) is the upper bound

    log Δ_K(ζ(5)) ≤ 2h(h + 6N − K) log K + (λM₀ − I(ρ))K² + 18h log K + 160h

for the Hankel determinant Δ_K of (2.4) evaluated at ζ(5). In Lean:

```lean
-- Zeta5/Sec6/Final.lean, namespace Zeta5.RealBound
theorem eq_6_14 (n : ℕ) (hn : 0 < n) (hΔpos : 0 < evalZeta5 (Delta n)) :
    Real.log (evalZeta5 (Delta n))
      ≤ 2 * (h n : ℝ) * ((h n : ℝ) + 6 * (N n : ℝ) - (K n : ℝ)) * Real.log (K n : ℝ)
        + ((lam : ℝ) * M0 - Irho) * (K n : ℝ) ^ 2
        + 18 * (h n : ℝ) * Real.log (K n : ℝ) + 160 * (h n : ℝ)
```

Here `M0 = -1329/200`, and `Irho` is the closed form (A.2) of the logarithmic energy I(ρ),
computed from the entries of Table 1. The hypothesis `0 < Δ_K(ζ(5))` follows from
Proposition 2.2 and is proved (`Zeta5.delta_pos`). The statement is the one that was a
`sorry` until 2026-09-24 (it was then in `Zeta5/RealBound.lean`), unchanged.
`#print axioms Zeta5.RealBound.eq_6_14` gives `[propext, Classical.choice, Quot.sound]`.
(Until the Hermite axiom was replaced by a theorem, it also listed
`Zeta5.Axioms.hermite_pole_integral`, which entered through Proposition 2.2's integral
representation of the moments, used by (6.10).)

The proof is in `Zeta5/Sec6/` (the route, with every step, is in the module docstring of
`Zeta5/Sec6/Final.lean`):

* **The Gram integral, (6.10)–(6.13)** (`Sec6/Gram.lean`). Andréief's identity (6.10) writes
  Δ_K(ζ(5)) as an h-fold integral; with (6.11), the Riemann-sum bound (6.12) and the
  scaling (6.13), (6.14) follows from any *configuration bound* of the shape of (6.9).
  ∫₀^∞(1+y)⁵e^{−y/K}dy ≤ 326K⁶ replaces the paper's constant 652. The factor 1/h! of (6.10)
  is kept through to (6.14). (The paper keeps it in (6.13) and discards it, as log h! ≥ 0,
  only when it takes logarithms.) This factor lets `eq_6_14_of_config` accept any
  configuration bound up to 3h log K + 131h. The bound actually proved, 2h log K + 20h,
  would give (6.14) without it.
* **The configuration bound (6.6)–(6.9)** (`Sec6/Energy.lean`), with the constant 20h where
  the paper has (120+√2)h. **Deviation:** the paper regularises the points by circles of
  radius ε in ℂ and applies Lemma 6.2 to the kernel log|z − w|. Here the points stay Dirac
  masses on the real line and the kernel is regularised instead:
  kC ε(x) = ½ log(x² + ε²) ≥ log|x|. The zero-mass argument of Lemma 6.2 (a Frullani
  representation and positive definiteness of the Gaussian kernel) is proved for kC ε
  (`Sec6/CND.lean`, `Frullani.lean`, `GaussPD.lean`, `Swap.lean`). Since kC ε is bounded on
  compacts, the log-integrability hypothesis and the limit step of Lemma 6.2 are not needed.
  The smoothing error is bounded in a different way from the paper's mass bound and "60√ε"
  of p. 19 (`SmoothErr.lean`, `SmoothArc.lean`, `RhoCross.lean`).
* **The arcsine potential (A.1) and the energy (A.2)** (`LogCos*.lean`, `ArcsinePot.lean`,
  `PairEnergy.lean`, `RhoEnergy.lean`). (A.1) is proved for every interval, on the interval
  from ∫₀^π log sin θ dθ = −π log 2 and off it from Mathlib's circle averages. (A.2) is used as
  the inequality I(ρ) ≤ I_k(ρ, ρ) for the regularised kernel, which is what the argument needs.
* **The potential inequality (6.2)/(6.7), Lemma 6.1** (`Sec6/Num/`, `Potential.lean`,
  `Field.lean`). **Deviation:** the paper verifies (6.2) on [0, 2] by the bound ℬ(l, r) of
  (A.9) on the 684 cells of Table 2. That route is not used. Instead the closed forms (A.1)
  and (A.5) of 2U^ρ − V are evaluated with certified interval arithmetic on the
  formalization's own partition: 1049 cells on [0, 2] and 2 on [2, 4], each checked by the
  kernel (`decide +kernel`), and an analytic bound for t ≥ 4 in place of (6.8). The partition
  is generated by `numerics/sec6/gen_lean.py`. (A.5), the closed form of the field V of (6.1),
  is proved (`Field.lean`).

The statements of the 19 leaves were fixed before any of them was proved, and were tested
numerically (`numerics/sec6/check_leaves.py`: 133 checks, 7 of them must-fail controls).
Sixteen leaves are tested directly. The two branches of (A.1),
`integral_log_abs_sub_cos_of_abs_le` and `integral_log_abs_sub_cos_of_one_lt_abs`, are tested
together through `integral_log_abs_sub_cos`. The bilinear expansion `kE_rhoM_expand` has no
test of its own. The Lean kernel checks all of them. Downstream of
(6.14), Proposition 6.3, i.e. (6.16) from (6.14) and (6.15) (`Zeta5.RealBound.prop_6_3_of`),
then (7.1), Theorem 2.1 and Theorem 1.1 are proved, as are (6.15), the margin (7.2), Table 1's
verifications and (A.10)/(6.4), λM₀ − I(ρ) + C_* ≤ Ū (`Zeta5.RealBound.eq_6_4`). The fact that
Table 2's 684 cells tile [0, 2] is also proved (`Zeta5.RealBound.table2_tiles`), but the main
proof does not use it, and (A.9) is not formalized.

Before it was proved, the Lean statement of (6.14) was evaluated at n = 1, 2, 3 (K = 40, 80,
120) as a consistency check of the transcription. The exact values of Δ_K(ζ(5)) came from the
referee audit described under [Provenance](#provenance). The inequality holds with a large
margin (`cert/c3/eq_6_14_control.py`, `cert/c3/eq_6_14_control.out`).

### The axiom

`Zeta5/Axioms.lean` is the only file of the project that declares any axiom, and it now
declares one. Its docstring gives the precise statement, a literature citation, and the reason
Mathlib lacks it.

* **`chebyshev_theta_asymptotic`.** θ(x)/x → 1 as x → ∞, where θ is Mathlib's
  `Chebyshev.theta`, θ(x) = Σ_{p ≤ x, p prime} log p. This is the prime number theorem
  (Hadamard, de la Vallée Poussin, 1896) in Chebyshev's form, as stated in textbooks (e.g.
  Apostol, *Introduction to Analytic Number Theory*, Thm. 4.4 with Ch. 13); the paper cites it
  as DLMF 27.12.2–27.12.4 (p. 15). It mentions no definition of this project. Mathlib v4.34.0
  has θ, ψ and Chebyshev-type bounds, but no proof of θ(x) ~ x or ψ(x) ~ x. It is used only
  for Proposition 5.2, through `Zeta5.PNT.prime_riemann_sum`.

The two axioms that the project declared until 2026-09-24 are now theorems, with the
identical statements:

* **`Zeta5.Hermite.pole_integral`** (`Zeta5/Hermite.lean`), formerly the axiom
  `hermite_pole_integral`: for a > 0, ∫₀^∞ w(y)/(y² + a²) dy = a⁴ ζ(5, a) − 1/(2a) − 1/4,
  with w the weight of (2.10) and ζ(5, a) = Σ_{k≥0} (k + a)^{−5}. This is the display on p. 5
  of the paper, which the paper derives from Hermite's formula (DLMF 25.11.29) by four
  integrations by parts. The Lean proof uses **no axiom**, and it does not follow the paper:
  it expands w, substitutes u = 2πl·y/a in each term, sums over l with the Mittag-Leffler
  expansion of the cotangent (Mathlib's `cot_series_rep'`), and evaluates the remaining Laplace
  integrals as a geometric series; every interchange of a sum with an integral is for
  nonnegative terms. It is used only for Proposition 2.2.
* **`Zeta5.PNT.prime_riemann_sum`** (`Zeta5/PNT.lean`), formerly the axiom
  `pnt_prime_riemann_sum`: for 0 ≤ a < b and φ bounded on [a, b] and continuous off a finite
  set, X⁻¹ Σ_{aX < p ≤ bX, p prime} φ(p/X) log p → ∫_a^b φ(y) dy as X → ∞. This is the
  partial-summation step of p. 15. It is proved from `chebyshev_theta_asymptotic` by a
  Darboux-type sandwich: a uniform partition of [a, b] on which the oscillations of φ have small
  total weight, and on each piece the prime sum is compared with θ(vX) − θ(uX).

That each theorem has the same type as the axiom it replaces was checked in Lean on the
integrated build: the old `Axioms.lean` of commit `bfd4249`, re-declared in a scratch namespace
on top of `import Zeta5`, gives types syntactically equal (`Expr ==`) to those of the two
theorems, and equal by `rfl`.
Numerical sanity checks are in `numerics/axioms/` (see `numerics/README.md`); the checks of the
former axioms made at the certification of 2026-09-23 (`cert/c3/axioms_numeric.py`) refer to
the old statements, which are the statements of the two theorems.

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
    Zeta5.Axioms.chebyshev_theta_asymptotic

  (C) sorry(s) — unfinished steps of the paper's own argument, 0 in all:
    (none)

  (D) any other axiom (must be empty):
    (none)

  [self-check: walker agrees with Lean.collectAxioms, 4 axiom(s)]
```

The last line records that the walker's result agrees with Lean's own `Lean.collectAxioms`.
The build then prints

```
info: Zeta5/Audit.lean:275:0: every sorry of the Zeta5 namespace is used by Zeta5.zeta5_irrational.
```

(vacuously: there is none). Lean's built-in `#print axioms` gives the same list, with no
`sorryAx`:

```
'Zeta5.zeta5_irrational' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Zeta5.Axioms.chebyshev_theta_asymptotic]
```

`propext`, `Classical.choice` and `Quot.sound` are the three standard axioms of Lean's logic
(propositional extensionality, the axiom of choice, and soundness of quotients). Essentially
all of Mathlib uses them.

`Audit.lean` also reports, for each named intermediate statement, whether it depends on a
`sorry`. All of them, including Theorem 2.1, Proposition 6.3, (6.14) and (7.1), print
`depends on NO sorry`, and `Zeta5.theorem_1_1` (Theorem 2.1 ⟹ Theorem 1.1) depends only on
the three standard axioms. At its end it prints the axioms of the two former axioms, now
theorems: `Zeta5.Hermite.pole_integral` depends only on the three standard axioms, and
`Zeta5.PNT.prime_riemann_sum` on those and `Zeta5.Axioms.chebyshev_theta_asymptotic`.

### What is machine-checked

Everything on the paper's route to Theorem 1.1 is machine-checked. That
covers §2 (the functional μ_X, (2.9), and Proposition 2.2, including the pole integral of
p. 5), §3
(Lemma 3.3, (3.11), (3.12)) and §4 (Propositions 4.1 and 4.3 with both p-adic local
analyses). It covers §5 (Propositions 5.1 and 5.2, the latter modulo the prime number
theorem; (5.7) with an explicit uniform constant; the tail estimates (5.15)–(5.17); all of
Appendix B), §6 including (6.14) (by the route described above), and §7. The finite
computations are carried out in Lean by exact rational arithmetic and certified enclosures,
not assumed. These are Appendix B's 143 intervals and its Tables 3 and 4, Table 1 and the
constants of Appendix A.4, the certified partition for (6.2)/(6.7), and the margin (7.2).

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

   This compiles the 71 files of this project and the root file. A clean rebuild of the
   project on top of the Mathlib cache takes about 8 minutes on a 12-core machine (four clean
   builds on 2026-09-24, before `Hermite.lean` and `PNT.lean` were added, took 7 min 26 s to
   8 min 1 s). The numerical modules
   `Zeta5/Sec6/Num/` need up to about 8 GB of memory. What to look for in the output:
   * the assumption report shown above, among many `info:` lines (the other `info:` lines are
     `#print axioms` checks on intermediate results, and they are expected);
   * no warning `declaration uses 'sorry'`;
   * 17 warnings, all of them style lints that do not affect correctness: 14 "automatically
     included section variable(s) unused" and 3 "Variable name … is not explicitly
     referenced". Removing them would change the signatures of the theorems concerned, so
     they are left as they are;
   * the final line `Build completed successfully (8996 jobs).`

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
    Classical.choice,
    Quot.sound,
    Zeta5.Axioms.chebyshev_theta_asymptotic]
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

7. **Kernel replay (optional, about 50 minutes).** `lake env leanchecker --verbose Zeta5`
   re-checks every declaration of every module with Lean's kernel, independently of the
   elaborator. The recorded run of 2026-09-24 (all 70 modules of the state before the axiom
   reduction, exit 0) is `cert/final/leanchecker.out`.

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
| §2.4, the pole integral of p. 5 | `Hermite.lean` | `Hermite.pole_integral`, ∫₀^∞ w(y)/(y²+a²) dy = a⁴ζ(5,a) − 1/(2a) − 1/4, proved with no axiom via the Mittag-Leffler expansion of the cotangent (formerly the axiom `hermite_pole_integral`). |
| §2.4, Proposition 2.2 | `Positivity.lean` | (2.10) and positive definiteness of G_K(ζ(5)). Uses `Hermite.pole_integral`. |
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
| §5, the prime number theorem in partial-summation form | `PNT.lean` | `PNT.prime_riemann_sum`, the prime Riemann sums X⁻¹Σ φ(p/X) log p → ∫φ, from θ(x) ~ x by a Darboux-type sandwich (formerly the axiom `pnt_prime_riemann_sum`). |
| §5, Proposition 5.2 | `PrimeSum.lean` | The three-range decomposition of log m_{K,M} and (5.11). Uses `PNT.prime_riemann_sum`. |
| §5.3, (5.15)–(5.17) | `Tail.lean` | The two integrations by parts, on finite intervals. |
| Appendix B, (5.8)–(5.18) | `AppendixB.lean` | (B.1), the 143 affine pieces of (B.2), Tables 3 and 4, (5.10), and (5.18) exactly. |
| §6 and Appendix A | `RealBound.lean` | Table 1, (A.10)/(6.4), Table 2's tiling, (6.11), (6.15), and (6.16) from (6.14). |
| §6, (6.14) and Proposition 6.3 | `Sec6/Final.lean` | `RealBound.eq_6_14` and `RealBound.prop_6_3` (same names and types as in the 2026-09-23 `RealBound.lean`), assembled; the module docstring gives the whole route. |
| §6 and Appendix A, shared data | `Sec6/Defs.lean`, `Sec6/Measures.lean` | The regularised kernel kC ε, its energy kE, the arcsine measures and ρ, U^ρ, the field V of (6.1) and its closed form (A.5), the configuration bound of (6.9); elementary facts about the measures. |
| §6.2, (6.10)–(6.13) | `Sec6/Gram.lean` | Andréief's identity (6.10), (6.12), (6.13) with 326K⁶, and (6.14) from a configuration bound. |
| §6.1, (6.6)–(6.9) | `Sec6/Energy.lean` | The configuration bound (6.9') for the regularised kernel, from (6.6'). |
| §6.1, Lemma 6.2 for kC ε | `Sec6/CND.lean`, `Frullani.lean`, `GaussPD.lean`, `Swap.lean` | The zero-mass energy inequality, from a Frullani representation and positive definiteness of the Gaussian kernel. |
| §6.1, the cross term | `Sec6/RhoCross.lean`, `SmoothArc.lean`, `SmoothErr.lean`, `SmoothAux.lean`, `Antideriv.lean` | The smoothing error π(δ + π√(2δ)) per arcsine component, and the cross term with 88√ε + 420ε. |
| Appendix A, (A.1) | `Sec6/LogCos.lean`, `LogCosInt.lean`, `LogCosOn.lean`, `LogCosOff.lean`, `ArcsinePot.lean` | The arcsine potential, on the interval and off it. |
| Appendix A, (A.2) | `Sec6/RhoEnergy.lean`, `PairEnergy.lean`, `ArcComm.lean`, `Bilinear.lean`, `IrhoSum.lean` | I(ρ) ≤ I_k(ρ, ρ) for the regularised kernel (`rho_energy_ge`). |
| Appendix A, (A.5) | `Sec6/Field.lean` | The closed form of V. |
| §6.1, (6.2), (6.7), (6.8); Lemma 6.1 | `Sec6/Potential.lean`, `Sec6/Num/*.lean` | 2U^ρ − V ≤ M₀: certified interval arithmetic on 1049 cells of [0, 2] and 2 of [2, 4] (`Num/Cell`, `Eval`, `Sound`, `Seg1`–`Seg6`, `Final`, all cells `decide +kernel`), the tail t ≥ 4 (`Num/Tail`), and the transfer to V (`Potential.lean`). |
| §7, (5.21) and (7.1) | `Asymptotics.lean` | (5.21) from (5.11), and (7.1) from (5.21) and (6.16). |
| §7, Theorems 2.1 and 1.1 | `Interface.lean` | The named statements, Theorem 2.1 at M = 200, and `zeta5_irrational`. |
| (not in the paper) | `Axioms.lean` | The one axiom, the prime number theorem θ(x) ~ x. |
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
  above. The proof uses (A.2) only through the inequality I(ρ) ≤ I_k(ρ, ρ) for the
  regularised kernel (`Zeta5.Sec6.rho_energy_ge`).
* **§6 by a different route.** The energy step (6.6)–(6.9) regularises the kernel on the real
  line instead of the points by circles in ℂ, and bounds the smoothing error differently;
  (6.2) on [0, 2] is proved on the formalization's own certified partition instead of by (A.9)
  on Table 2; the Gram step keeps the 1/h! of (6.10) and uses 326K⁶ in place of 652. See
  [(6.14): how it is proved](#614-how-it-is-proved) and the module docstring of
  `Zeta5/Sec6/Final.lean`.
* **(5.16) and (5.17)** are proved in the combined form that (5.18) uses, a bound on
  ∫_{20}^{M} R(x) x^{−3} dx (`Zeta5.AppendixB.eq_5_16_5_17`). This form avoids improper
  integrals. The two separate statements of p. 16 are not stated.

## Ground rules

These rules governed the formalization, and the Lean docstrings that mention "the README"
refer to this section.

* **Nothing internal to the paper's argument is axiomatized.** Every proposition, lemma,
  equation, computation and table of the paper that the proof uses is either proved in Lean or
  left as a named `sorry`. The assumption report lists every `sorry`, and currently there are
  none.
* **Only standard external facts may be axioms.** Each one is declared in `Zeta5/Axioms.lean`
  with (i) its precise statement, (ii) a literature citation, and (iii) the reason Mathlib
  lacks it. Where an axiom is stronger than the bare citation, the docstring says so. (Both
  axioms declared until 2026-09-24 were, and both are now theorems. The one current axiom,
  `chebyshev_theta_asymptotic`, is the textbook statement of the prime number theorem, with
  nothing added.)
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
* **The assumption list:** whether the axiom is a correct statement of a known result (the
  prime number theorem), and whether nothing else is assumed.

`docs/CERTIFICATION.md` describes how these were checked, most recently on 2026-09-24 (before
the axiom reduction; the reduced state is pending re-certification, see its addendum): clean
rebuilds, independent dependency walkers, a scan of the compiled `.olean` files, a kernel
replay, a kernel-level comparison of every statement and definition with the previous
certified state, attacks on the axioms, a check of the main statement at the level of Lean
terms, and checks of statements against the preprint.

**Independence.** The formalization was written without consulting any other formalization of
the preprint. The Claude Code transcripts of the project were scanned for web access
(`docs/CERTIFICATION.md`, §8). The sessions of 2026-09-24, which proved (6.14) and
re-certified the result, made no web access of any kind. Earlier sessions used web searches
for literature and citation lookups. One of those searches, made on 2026-09-23 to locate the
preprint, returned among its results a link to another Lean formalization of the preprint.
That link was never opened, and nothing from it was used.

## Reference

Aabir Fauzan, "ζ(5) is irrational", preprint, 17 September 2026. Zenodo,
[doi:10.5281/zenodo.22826418](https://doi.org/10.5281/zenodo.22826418) (all versions). The
formalization and the audit follow version v1,
[doi:10.5281/zenodo.22826419](https://doi.org/10.5281/zenodo.22826419). All page and equation
numbers in this repository refer to v1. The preprint itself is not included here.

## Further documentation

* `docs/STATUS.md`: the detailed status. It covers what is proved, section by section; the
  assumption list with the axioms' docstrings summarized; the complete list of deviations; and
  what remains to be done.
* `docs/CERTIFICATION.md`: the adversarial certification of the present state (2026-09-24,
  no `sorry`). It checks that the main theorem is faithfully stated and that it depends on
  exactly the two axioms then declared and Lean's standard axioms. It also records the earlier
  certification of 2026-09-23, when (6.14) was still a `sorry`, and, in an addendum, the
  axiom reduction of 2026-09-24 (pending certification).
* `docs/lean-status.pdf` (source `docs/lean-status.tex`): a readable summary of what the
  formalization proves and assumes (2026-09-24, before the axiom reduction: it still describes
  the two former axioms).
* `docs/zeta5-audit.pdf` (source `docs/zeta5-audit.tex`): the referee audit of the preprint.
  It gives a section-by-section and lemma-by-lemma assessment, the exact determinant data, and
  a proof of the inequality on p. 10.
* `cert/`: the Lean and Python scripts used by the certifications, with their recorded outputs:
  `cert/final/` for 2026-09-24, `cert/*.lean` and `cert/c3/` for 2026-09-23 (see
  `cert/README.md`). They are not part of `lake build`.
* `numerics/`: exact-arithmetic known-answer controls, run before the corresponding Lean
  proofs were written. The Python scripts use `sympy`, `mpmath` and `numpy`, and the
  `outerbasis/` scripts use SageMath. The two `.lean` files there are run with
  `lake env lean numerics/<file>.lean` and are not part of `lake build`.
