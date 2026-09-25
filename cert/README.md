# Certification scripts

These scripts check two things about the main theorem
`Zeta5.zeta5_irrational : Irrational Zeta5.zeta5`: what it states, and what its proof rests
on. They do this independently of the project's own audit metaprogram (`Zeta5/Audit.lean`).
The findings are written up in [`../docs/CERTIFICATION.md`](../docs/CERTIFICATION.md). None of
these files is part of the Lake library. Nothing imports them, and `lake build` does not
compile them.

There are two sets:

* **`final/`** belongs to the certification of **2026-09-24** (branch `eq614`, code commit
  `808618b`, no `sorry`). This is the current certification.
* **`C3*.lean` and `c3/`** belong to the certification of **2026-09-23** (`main`, `9ce1320`,
  one `sorry`, `eq_6_14`). The scripts still run against the present build. Their recorded
  outputs in `c3/` refer to the 2026-09-23 state: 33 modules, 3 272 declarations, and
  `eq_6_14` as the one `sorry` leaf and as the negative control. The same scripts re-run on
  2026-09-24, where re-running was useful, are recorded in `final/`.

The Lean scripts share no code with `Zeta5/Audit.lean`. Each one runs a check that a flawed
audit could get wrong, and each has its own controls, which must give the wrong answer or
must be found:
* a planted `sorry`;
* a planted `axiom`;
* a `sorry` hidden in a `where` auxiliary or in an instance field;
* a reference to a missing name;
* a deliberately broken walker.

## The 2026-09-24 certification (`final/`)

From the repository root, after `lake exe cache get` and `lake build`:

| command | what it checks | time | recorded output |
|---|---|---|---|
| `lake build` after `rm -rf .lake/build` | clean build; includes the output of `Zeta5/Audit.lean` | ~8 min | `final/clean-build.log`; three more clean builds by the certifiers: `final/head-wt-build.log`, `final/cone-wt-build.log`, `final/fidelity/clone-build.log` |
| `lake build` after the comment-only edits of the re-certification commit, then `DumpDecls.lean` | the declarations are byte-identical to those of `808618b` | ~5 min | `final/rebuild-after-comments.log`, `final/nochange/dump-after-comments.out` |
| `lake env lean cert/final/FWalker.lean` | the 2026-09-23 walker (`C3Walker.lean`), copied verbatim, with 37 targets (the §6 statements and all 19 blueprint leaves) and five planted controls; agreement with `Lean.collectAxioms`; shortest provenance chains | ~12 min | `final/FWalker.out` |
| `lake env lean cert/final/FScan.lean` | sections [1]–[5] of `C3Scan.lean`, copied verbatim, for all 3 862 declarations of the 70 Zeta5 modules; [6], a walk from every Zeta5 declaration at once, with a planted control; per-module census | ~8 min | `final/FScan.out` |
| `lake env lean --run cert/final/FOlean.lean --control Zeta5 Zeta5.zeta5_irrational Zeta5.theorem_1_1 Zeta5.theorem_2_1 Zeta5.RealBound.eq_6_14 Zeta5.RealBound.prop_6_3` | reads every `.olean` with `readModuleData` (no `importModules`, no `Environment`, no `collectAxioms`) and follows every stored version of a duplicated name; synthetic planted control | ~40 s | `final/FOlean.out`, `final/FOlean-conewt.out` (a second build; identical apart from the timing line) |
| `lake env leanchecker --verbose Zeta5` | kernel replay of every declaration of all 70 Zeta5 modules | ~50 min | `final/leanchecker.out` |
| `python3 cert/final/source_scan.py` | comments and strings removed, then a search for forbidden constructs in the 70 library sources | seconds | `final/source_scan.out` |
| `lake env lean cert/C3Semantics.lean`, `lake env lean cert/C3Attack.lean` | the 2026-09-23 checks of the statement and of the axioms, re-run on this build | ~30 s | `final/C3Semantics.out`, `final/C3Attack.out` |
| `lake env lean --run cert/final/nochange/DumpDecls.lean <out.tsv> Zeta5` | for every constant of a Zeta5 module: kind, module, universe parameters, a full serialisation of its type and value, and kind-specific metadata | ~1 min | `final/nochange/main-9ce1320.tsv.gz`, `final/nochange/head-808618b.tsv.gz` (checksums of the uncompressed files in `dumps.sha256`) |
| `python3 cert/final/nochange/compare.py <main.tsv> <head.tsv>` and `alpha_check.py` | SHA-256 comparison of two dumps; α-equivalence of the entries that differ | seconds | `final/nochange/compare.out`, `final/nochange/alpha.out` |
| `lake env lean cert/final/nochange/KeyStatements.lean` | `pp.all` types and values of the key declarations; the main statement checked with `Expr.equal` | ~1 min | `final/nochange/key_main.out`, `final/nochange/key_head.out` |
| `lake env lean cert/final/fidelity/Fidelity.lean` | (6.14) and (6.16) as stated; non-vacuity through `delta_pos`; axioms; spot-checked leaf statements | ~1 min | `final/fidelity/Fidelity.out` |
| `lake env lean cert/final/fidelity/Cone.lean` | membership of named §6 declarations in the cone of the main theorem | ~1 min | `final/fidelity/Cone.out` |
| `python3 cert/final/fidelity/constants.py pp17-25.txt` | Table 1 from the PDF text against the Lean `aT`, `bT`, `cT`; `Irho`, `M0`, `C_*`, (6.4) to 40 digits (needs `mpmath`) | seconds | `final/fidelity/constants.out` |
| `python3 cert/final/fidelity/count_cells.py` | the certified cells of `Sec6/Num` tile [0, 2] contiguously, and their bounds | seconds | `final/fidelity/count_cells.out` |
| `python3 cert/final/fidelity/leaf_stmts.py` | the statements of the 19 leaves and of the §6 definitions are unchanged since the blueprint commit `4dea216` | seconds | `final/fidelity/leaf_stmts.out` |
| `cd numerics/sec6 && python3 check_leaves.py` | numerical leaf tests, re-run | ~10 s | `final/fidelity/check_leaves.rerun.out` (identical to `numerics/sec6/check_leaves.out`) |

### Notes

* The certifiers ran the scripts in their own clean builds of `808618b`, in scratch
  directories (a `git worktree`, a `git archive` and a `git clone`). This is why some
  recorded outputs contain absolute scratch paths. Those builds had sources identical to the
  repository (`diff -rq` printed nothing).
* `constants.py` needs the text of pp. 17–25 of the preprint, which is not included here.
  Make it with `pdftotext -layout -f 17 -l 25 <preprint.pdf> pp17-25.txt`. The page images
  that the certifiers read, and the transcript scan of `docs/CERTIFICATION.md` §8, are not
  published either.
* `main-9ce1320.tsv.gz` and `head-808618b.tsv.gz` allow the comparison of
  `CERTIFICATION.md` §5 to be repeated without rebuilding `main`. `gunzip` them and run
  `compare.py` and `alpha_check.py`.

## The 2026-09-23 certification (`C3*.lean`, `c3/`)

| command | what it checks | time | recorded output |
|---|---|---|---|
| `lake env lean cert/C3Walker.lean` | independent breadth-first dependency walker: iterative `Expr` traversal, never `ConstantInfo.value?`, and a successor relation that is a superset of `Lean.CollectAxioms.collect`. Gives the axioms and `sorry` leaves of 16 declarations, with shortest provenance chains, compared with `Lean.collectAxioms`; planted `sorry` and `axiom` controls; the `value?` trap run as a negative control | 4–12 min | `c3/C3Walker.out` |
| `lake env lean cert/C3Scan.lean` | scan keyed on the *defining module*: every `axiom` in the environment; for the declarations of the Zeta5 modules, axioms, `sorryAx` mentions, and `unsafe`/`partial`/`opaque`; `sorry` carriers in the cone, and orphans; direct users of each project axiom; per-module census | 3–10 min | `c3/C3Scan.out` |
| `lake env lean cert/C3Semantics.lean` | the statement as an `Expr` (literally `Irrational Zeta5.zeta5`, no hypotheses, Mathlib's `Irrational`); the modules of every constant in the definition of `zeta5`; a sorry-free proof that `zeta5 = riemannZeta 5` | ~1 min | `c3/C3Semantics.out` |
| `lake env lean cert/C3Attack.lean` | attacks on the two axioms: their degenerate instances are blocked by refutable hypotheses; each is non-vacuous (a consequence derived sorry-free); no `unsafe` or `partial` constant in the cone | ~1 min | `c3/C3Attack.out` |
| `lake env leanchecker --verbose Zeta5` | kernel replay (33 modules then) | ~25 min then | `c3/leanchecker.out` |
| `python3 cert/c3/axioms_numeric.py` | both axioms numerically: Hermite's formula to 40 digits at 8 values of `a` from 0.01 to 1000, with the weight taken from the Lean definition; prime Riemann sums for 4 test functions up to X = 10⁷ (needs `mpmath`, `numpy`) | ~1 min | `c3/axioms_numeric.out` |
| `python3 cert/c3/eq_6_14_control.py [<delta.json>]` | known-answer control for (6.14), then a `sorry`: `Irho`, `M0` and `lam` parsed from the Lean source, then (6.14) checked at K = 40, 80, 120 against the exact values of `log Δ_K(ζ(5))` in `c3/delta_K_values.json` (needs `mpmath`) | seconds | `c3/eq_6_14_control.out` (reproduced exactly on 2026-09-24) |
| `lake env lean --run cert/c3/DumpEnv.lean <out.tsv> Zeta5` | per-declaration hashes of type and value (superseded by `final/nochange/DumpDecls.lean`, which records full serialisations) | ~1 min | — |

`c3/clean-build.log` is the log of the clean rebuild that the 2026-09-23 certification started
from. `eq_6_14_control.py` should be run from the repository root. It reads the constants
`Irho`, `M0` and `lam` from `Zeta5/RealBound.lean`, where they are still defined. The
2026-09-23 report also compared the sources with a snapshot taken before the last four
interface statements were proved. That snapshot and its comparison script are not published.
`C3` in the file names stands for the third certification pass. Earlier passes are not
included.
