# Verification

This file states what a reader must trust to accept that `Zeta5.zeta5_irrational` proves ζ(5)
irrational, and how to check the rest.

## What must be trusted

1. **Lean's kernel** (Lean 4.34.0), and a build made by the reader from the sources.
2. **The statement.** `cert/Check.lean` states, using only Mathlib names,

   ```lean
   example : Irrational (∑' v : ℕ, (1 : ℝ) / ((v : ℝ) + 1) ^ 5) :=
     Zeta5.zeta5_irrational
   ```

   The Mathlib definitions involved are `Irrational` and `tsum` (`∑'`).
3. **The axiom.** The only axiom of the project, besides Lean's `propext`, `Classical.choice`
   and `Quot.sound`, is `Zeta5.Axioms.chebyshev_theta_asymptotic`, restated in
   `cert/Check.lean` as

   ```lean
   example : Tendsto (fun x : ℝ => Chebyshev.theta x / x) atTop (nhds 1) :=
     Zeta5.Axioms.chebyshev_theta_asymptotic
   ```

   This is the prime number theorem θ(x) ~ x. The Mathlib definition involved is
   `Chebyshev.theta` (`Mathlib/NumberTheory/Chebyshev.lean`),
   θ(x) = Σ_{p ∈ (0, ⌊x⌋₊], p prime} log p.

Nothing else needs to be read. In particular, the correctness of the theorem does not depend on
any other definition, statement or proof of the project.

## How to check

From the repository root, after `lake exe cache get`:

1. `lake build` compiles every module. It reports no `declaration uses 'sorry'`.
2. `lake env lean cert/Check.lean` compiles the two restatements above. Because they are
   written with Mathlib names, they do not depend on any name or notation defined in the
   project. It prints

   ```
   'Zeta5.zeta5_irrational' depends on axioms: [propext,
    Classical.choice,
    Quot.sound,
    Zeta5.Axioms.chebyshev_theta_asymptotic]
   ```

3. `lake env leanchecker --verbose Zeta5` loads the compiled modules in a fresh process and
   re-checks every declaration with the kernel alone. This rules out declarations that code in
   the project might have added to the environment without kernel checking during the build.

## Results

On 24–25 September 2026 (Lean 4.34.0, Mathlib v4.34.0, macOS, 12 cores), for commit `d8238e5`:

* A build from scratch (with `.lake/build` removed) completed in 6 min 40 s with
  `Build completed successfully (8995 jobs)` and no `sorry` warning.
* `cert/Check.lean` compiled and printed the axiom list above.
* `leanchecker` replayed all 70 modules of the project and the root module, and exited with
  status 0 (55 minutes).

## Scope

Lean establishes the implication: the prime number theorem implies that ζ(5) is irrational.
That the formal proof follows Fauzan's argument is a separate matter, documented in the README
(the map from the paper to the files, and the list of deviations) and in the docstrings of
`Zeta5/Interface.lean`, which transcribe the paper's numbered statements.
