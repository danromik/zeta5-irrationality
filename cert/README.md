# Certification scripts

These scripts check, independently of the project's own audit metaprogram
(`Zeta5/Audit.lean`), what the main theorem `Zeta5.zeta5_irrational : Irrational Zeta5.zeta5`
states and what its proof rests on. The findings are written up in
[`../docs/CERTIFICATION.md`](../docs/CERTIFICATION.md). None of these files is part of the Lake
library: nothing imports them, and `lake build` does not compile them.

The Lean scripts share no code with `Zeta5/Audit.lean`. Each one runs a check that a flawed
audit could get wrong, with its own positive or negative controls (a planted `sorry` and a
planted `axiom` that must be found; a deliberately broken walker that must give the wrong
answer).

## Running them

From the repository root, after `lake exe cache get` and `lake build`:

| command | what it checks | time | recorded output |
|---|---|---|---|
| `lake env lean cert/C3Walker.lean` | independent breadth-first dependency walker (iterative `Expr` traversal, never `ConstantInfo.value?`, successor relation a superset of `Lean.CollectAxioms.collect`): the axioms and `sorry` leaves of 16 declarations, with shortest provenance chains, compared with `Lean.collectAxioms`; planted `sorry`/`axiom` controls; the `value?` trap run as a negative control | 4–8 min | `c3/C3Walker.out` |
| `lake env lean cert/C3Scan.lean` | scan keyed on the *defining module*: every `axiom` in the environment; for the 3 272 declarations of the Zeta5 modules, axioms, `sorryAx` mentions, `unsafe`/`partial`/`opaque`; `sorry` carriers in the cone and orphans; direct users of each project axiom; per-module census | 3–10 min | `c3/C3Scan.out` |
| `lake env lean cert/C3Semantics.lean` | the statement as an `Expr` (literally `Irrational Zeta5.zeta5`, no hypotheses, Mathlib's `Irrational`); the modules of every constant in the definition of `zeta5`; a sorry-free proof that `zeta5 = riemannZeta 5` | ~1 min | `c3/C3Semantics.out` |
| `lake env lean cert/C3Attack.lean` | attacks on the two axioms: their degenerate instances are blocked by refutable hypotheses; each is non-vacuous (a consequence derived sorry-free); no `unsafe`/`partial` constant in the cone | ~1 min | `c3/C3Attack.out` |
| `lake env leanchecker --verbose Zeta5` | kernel replay of every declaration of every Zeta5 module (`leanchecker` ships with Lean 4.34) | ~25 min | `c3/leanchecker.out` |
| `python3 cert/c3/axioms_numeric.py` | both axioms numerically: Hermite's formula to 40 digits at 8 values of `a` from 0.01 to 1000, with the weight taken from the Lean definition; prime Riemann sums for 4 test functions up to X = 10⁷ (needs `mpmath`, `numpy`) | ~1 min | `c3/axioms_numeric.out` |
| `python3 cert/c3/eq_6_14_control.py [<delta.json>]` | known-answer control for the one `sorry`, (6.14): `Irho`, `M0`, `lam` parsed from the Lean source; checks (6.14) at K = 40, 80, 120 against the exact values of `log Δ_K(ζ(5))` in `c3/delta_K_values.json`, or in another file given as argument (needs `mpmath`) | seconds | `c3/eq_6_14_control.out` |
| `lake env lean --run cert/c3/DumpEnv.lean <out.tsv> Zeta5` | writes, for every constant defined in a Zeta5 module, its kind, module, universe parameters and the hashes of its type and (for definitions) value; two such dumps compared line by line show whether any statement or definition changed between two builds | ~1 min | — |

`c3/clean-build.log` is the log of the clean rebuild that the certification started from
(`.lake/build` deleted, then `lake build`); it includes the full output of `Zeta5/Audit.lean`.

## Notes on the recorded outputs

* The last line of each of the four `c3/C3*.out` files records the command and its running
  time. These four files were regenerated from the repository root on 2026-09-23 and are identical to
  the outputs quoted in `CERTIFICATION.md`, apart from the file name and line number in
  `C3Walker.lean`'s own warning about its planted `sorry`.
* `eq_6_14_control.py` reads the exact values of log Δ_K(ζ(5)) at K = 40, 80, 120 from
  `c3/delta_K_values.json`. These values come from the referee audit of the preprint
  (`docs/zeta5-audit.pdf`, "The direct computations"). The file also records log F_K and
  log S_K, and log F_K is the column printed in the audit's table of exact determinant data.
  Running `python3 cert/c3/eq_6_14_control.py` from the repository root reproduces
  `eq_6_14_control.out` exactly.
* `CERTIFICATION.md` §5 also reports a comparison with a snapshot of the sources taken before
  the last four interface statements were proved. The snapshot and the comparison script are
  not published, so that comparison cannot be re-run from here; `DumpEnv.lean` is the tool that
  produced the per-declaration hashes.
* `C3` in the file names stands for the third certification pass. Earlier passes, against
  earlier states of the development, are not included.
