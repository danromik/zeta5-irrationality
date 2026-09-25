# Adversarial certification of the Zeta5 Lean development

**Date:** 2026-09-24 · **Toolchain:** Lean 4.34.0, Mathlib v4.34.0 · **State certified:**
branch `eq614`, code commit `808618b` (69 modules under `Zeta5/` plus the root file, 70 in all;
**no `sorry`**)

*This certification was carried out by Claude (Anthropic) in a workflow run separate from the
runs that wrote the proofs (see README, 'Provenance'). In this document, "the certifiers" means
the three independent certification agents of that run, one each for the dependency cone, the
statements and the fidelity of the statements. The run's final agent collected their reports,
ran a further clean build, and wrote this document.*

*The scripts are in `cert/final/`, together with their recorded outputs, and `cert/README.md`
gives the commands to re-run them from the repository root. The certification of the previous
state (2026-09-23, when (6.14) was still a `sorry`) is summarised at the end, under
[Earlier certification (2026-09-23)](#earlier-certification-2026-09-23). Its scripts are
`cert/C3*.lean` and `cert/c3/`.*

*Note on the commit that adds this document.* The same commit edits the module comments
(`/- … -/`) of `Zeta5/Sec6/Final.lean` and `Zeta5/Sec6/Gram.lean` (see §7). It changes no Lean
declaration. A rebuild of that commit and a per-declaration dump
(`cert/final/nochange/DumpDecls.lean`) give output byte-identical to the dump of `808618b`
(§5.3).

**The claim under attack.** *"`Zeta5.zeta5_irrational` faithfully states that ζ(5) is
irrational, and depends only on Lean's standard axioms and on the two axioms in
`Zeta5/Axioms.lean`. There is no `sorry`."* In particular, `Zeta5.RealBound.eq_6_14`, the
paper's (6.14), was the one `sorry` of the certified 2026-09-23 state. It is now proved, and
its statement is unchanged.

**Verdict in one line.** **The claim holds.** Five independent methods agree, name for name,
that `Zeta5.zeta5_irrational` depends on exactly `[propext, Classical.choice, Quot.sound,
Zeta5.Axioms.hermite_pole_integral, Zeta5.Axioms.pnt_prime_riemann_sum]`, with no `sorryAx`
and no other axiom. The methods are:
* Lean's `#print axioms`;
* a breadth-first walker with planted controls;
* a module-keyed scan of all 3 862 project declarations;
* the project's audit metaprogram;
* a reader that walks the compiled `.olean` files directly, bypassing Lean's environment.

A full kernel replay of all 70 modules passed. A kernel-level comparison with the certified
2026-09-23 state shows two things. None of its 3 272 declarations changed its statement or
definition: the only differences are hygienic binder names in 16 compiler-generated auxiliary
lemmas. Every addition is in the new `Zeta5/Sec6/` modules. The statements of (6.14) and
(6.16) match the preprint term for term. The certifiers found **no defect** that affects the
assumption list or any statement. They did find documentation defects, all of which are
corrected in this commit (§7).

---

## 0. What was run, and where the evidence is

| # | check | tool | result |
|---|---|---|---|
| 1 | clean builds | `.lake/build` deleted, `lake build`, four times on identical sources | exit 0, 8994 jobs, 0 errors, **0** `sorry` warnings, 17 lint warnings |
| 2a | own walker | `cert/final/FWalker.lean` (the 2026-09-23 walker, new targets and controls) | 0 `sorry` leaves, 5 axioms, agrees with `collectAxioms` on 37 targets and 5 controls |
| 2b | `#print axioms` | Lean's own | same 5 axioms |
| 2c | module-keyed scan | `cert/final/FScan.lean` | 2 axioms and 0 `sorryAx` mentions among 3 862 declarations of 70 modules; 0 orphans; the union cone of all 3 862 reaches only the same 5 axioms |
| 2d | project audit | `Zeta5/Audit.lean`, in every clean-build log | same; "(C) … 0 in all" |
| 2e | direct `.olean` reader | `cert/final/FOlean.lean` (no `importModules`, no `Environment`, no `collectAxioms`) | same cone (69 102 constants), same 5 axioms, 0 `sorryAx` |
| 2f | kernel replay | `lake env leanchecker --verbose Zeta5` | all 70 modules replayed, exit 0 (52 min) |
| 2g | trusted base and sources | `git status` in every package; `cert/final/source_scan.py` | packages unmodified; no forbidden construct in the 70 source files |
| 3 | axioms | unchanged since 2026-09-23 (byte-identical kernel terms, §5) | the attacks of 2026-09-23 still apply; each axiom still has one direct user |
| 4 | the statement | `cert/final/nochange/KeyStatements.lean` | type is `Expr.equal` to `Irrational Zeta5.zeta5`; `zeta5` unchanged |
| 5 | kernel-level diff vs 2026-09-23 (`main`, `9ce1320`) | `cert/final/nochange/DumpDecls.lean`, `compare.py`, `alpha_check.py` | 0 changed statements or definitions; 0 removed; 590 added, all in `Sec6` |
| 6 | fidelity of §6 | `cert/final/fidelity/` (PDF pages 17–25 read as images) | (6.14) and (6.16) faithful, non-vacuous; constants re-derived from the PDF |
| 7 | independence | scan of the Claude Code transcripts (not published) | no web access in the 2026-09-24 sessions |

---

## 1. Clean builds

**The build in the repository.** In the repository checkout, `.lake/build` held no `.olean`
files: a certifier had emptied it at 17:44. The final agent confirmed that no other Lean or
Lake process was running and ran `lake build`. The run began at 20:28:52 PDT and took
7 min 34 s (453.7 s wall). It ended with

```
✔ [8993/8994] Built Zeta5 (12s)
Build completed successfully (8994 jobs).
```

and exit status 0. The log is `cert/final/clean-build.log`. All 70 Zeta5 modules were compiled
from source (8994 jobs in all, the rest being Mathlib and the other packages, which are
replayed from the cache).

**Three further clean builds** were made from the same sources by the certifiers, in
separate directories: a `git worktree` of `808618b`, a `git archive` of it, and a `git clone`.
They took 7 min 36 s, 7 min 26 s and 8 min 1 s. All three ended with `Build completed
successfully (8994 jobs).` and exit 0, and none printed `declaration uses 'sorry'`. The logs
are `cert/final/head-wt-build.log`, `cone-wt-build.log` and `fidelity/clone-build.log`. In
each case `diff -rq` against the repository's `Zeta5/` printed nothing.

**Errors: 0. `declaration uses 'sorry'` warnings: 0.** There are 17 warnings, all of them
style lints:
* 14 "automatically included section variable(s) unused". These are an instance hypothesis
  `hpf` in `InnerTate` (2), `InnerGeneral` (4) and `InnerEntries` (8).
* 3 "Variable name … is not explicitly referenced". These are `ha` in
  `InnerGeneral.comp_X_sub_C_phi_near`, and `hC0` in `PrimeSum.block2_le` and `block3_le`.

Clearing them would change the signatures of those theorems. Commit `808618b` removed the
other 250 warnings of the first `eq614` builds (deprecations and unused `simp` arguments) and
changed proofs only (§5).

**Sources are clean.** `cert/final/source_scan.py` strips comments and string literals, then
searches the 70 library sources (28 972 lines by its count). The following constructs each
occur **zero** times:
* `sorry`, `admit`, `native_decide`, `implemented_by`, `extern`, `unsafe`, `opaque`;
* `skipKernelTC`, `ofReduceBool`/`ofReduceNat`, `trustCompiler`, `csimp`;
* `set_option`, `macro`, `macro_rules`, `syntax`, `notation`, `attribute`;
* `run_cmd`, `#eval`, `initialize`, `open private`, `export`, `debug.*`.

The only hits are expected ones (`cert/final/source_scan.out`):
* `axiom` twice, both in `Zeta5/Axioms.lean`;
* `elab` 3 times and `partial def` once, all in `Zeta5/Audit.lean` (its report commands and
  its walker, which is not in the cone);
* `sorryAx` 3 times, as name literals in `Audit.lean`;
* `decide +kernel` in the certified cells of `Sec6/Num`, which brings in no axiom.

`Zeta5.lean` imports every `.lean` file under `Zeta5/`.

**The trusted base is unmodified.** `lean-toolchain` is `v4.34.0`, and there is no
`lakefile.lean`. All nine packages in `.lake/packages` are at the revisions pinned in
`lake-manifest.json`, with zero locally modified files. `Zeta5/Axioms.lean`, `lakefile.toml`,
`lean-toolchain` and `lake-manifest.json` are unchanged since `9ce1320`.

---

## 2. Five independent dependency checks, all agreeing

### 2.1 The walker — `cert/final/FWalker.lean`

This is the walker of the 2026-09-23 certification (`cert/C3Walker.lean`), copied verbatim.
Only the target list and the controls are new. It shares no code with `Zeta5/Audit.lean`.
* The `Expr` traversal is iterative and never calls `ConstantInfo.value?`.
* The successor relation is a superset of `Lean.CollectAxioms.collect`.
* The walk is breadth-first with parent pointers, so it prints the shortest provenance chain
  to each axiom and each `sorry`.

Two planted controls are new. One hides a `sorry` inside a `where` auxiliary, and the other
hides one inside an instance field. Output (`lake env lean cert/final/FWalker.lean`,
11 min 32 s), abridged: the control blocks are compressed onto fewer lines, long chains are
wrapped, and the other targets are omitted:

```
=== C3 C3ctl.uses_sorry_2
  axioms (1) : [sorryAx]            vs Lean.collectAxioms : AGREE
  sorry leaves (1) : [C3ctl.planted_sorry]
    chain to sorry leaf  : C3ctl.uses_sorry_2 → C3ctl.uses_sorry_1 → C3ctl.planted_sorry   [3 links]
=== C3 C3ctl.uses_axiom_2
  axioms (1) : [C3ctl.planted_axiom]   AGREE
=== C3 C3ctl.clean
  axioms (0) : []   AGREE   sorry leaves (0) : []
=== C3 C3ctl.uses_hidden_2
  sorry leaves (1) : [C3ctl.hiddenVal.aux]    chain [2 links]   AGREE
=== C3 C3ctl.uses_box_2
  sorry leaves (1) : [C3ctl.boxInst]          chain [2 links]   AGREE
=== C3 Zeta5.zeta5_irrational
  constants reached : 69102   (missing from env: 0)
  axioms (5) : [Classical.choice, Quot.sound, Zeta5.Axioms.hermite_pole_integral, Zeta5.Axioms.pnt_prime_riemann_sum, propext]
  vs Lean.collectAxioms : AGREE
  sorry leaves (0) : []
    chain to axiom : Zeta5.zeta5_irrational → Zeta5.theorem_2_1 → Zeta5.Q_pos → Zeta5.F_pos → Zeta5.delta_pos
                     → Zeta5.prop_2_2 → Zeta5.Positivity.prop_2_2 → Zeta5.Positivity.quadForm_eq_integral
                     → Zeta5.Positivity.prop_2_2_moment → Zeta5.Positivity.integral_pole_term
                     → Zeta5.Positivity.integral_wt_div_pole → Zeta5.Axioms.hermite_pole_integral   [12 links]
    chain to axiom : Zeta5.zeta5_irrational → Zeta5.theorem_2_1 → Zeta5.decay_2_7 → Zeta5.decay_of_margin
                     → Zeta5.eq_7_1 → Zeta5.eq_5_21 → Zeta5.prop_5_2 → Zeta5.PrimeSum.prop_5_2
                     → Zeta5.PrimeSum.tendsto_P2 → Zeta5.PrimeSum.tendsto_primeSum
                     → Zeta5.Axioms.pnt_prime_riemann_sum   [11 links]
=== C3 Zeta5.RealBound.eq_6_14
  constants reached : 60002   axioms (4) : [Classical.choice, Quot.sound, Zeta5.Axioms.hermite_pole_integral, propext]
  AGREE   sorry leaves (0) : []
    chain to axiom : Zeta5.RealBound.eq_6_14 → Zeta5.Sec6.Gram.eq_6_14_of_config → Zeta5.Sec6.Gram.gram_bound
                     → Zeta5.Sec6.Gram.eq_6_10 → Zeta5.Sec6.Gram.evalZeta5_G → Zeta5.Positivity.prop_2_2_moment
                     → Zeta5.Positivity.integral_pole_term → Zeta5.Positivity.integral_wt_div_pole
                     → Zeta5.Axioms.hermite_pole_integral
MODULE Zeta5.RealBound.eq_6_14 : Zeta5.Sec6.Final
MODULE Zeta5.RealBound.prop_6_3 : Zeta5.Sec6.Final
MODULE Zeta5.zeta5_irrational : Zeta5.Interface
```

The other targets all report `AGREE` and `sorry leaves (0)`: `theorem_1_1` (3 standard axioms
only), `theorem_2_1`, `RealBound.prop_6_3`, `Sec6.Gram.eq_6_14_of_config`, `Sec6.configBound`,
`Sec6.Num.eq_6_7_closed`, `Sec6.eq_6_7_closed`, `Sec6.rho_energy_ge`, and each of the 19
blueprint leaves. The full record is `cert/final/FWalker.out`.

What this output shows:
* **Every planted control is caught, with the right chain.** That includes the two new ways
  of hiding a `sorry`.
* **(6.14) is proved.** It was the `sorry` leaf of the 2026-09-23 run, whose chain was
  `… → eq_7_1 → prop_6_3 → RealBound.prop_6_3 → RealBound.eq_6_14`. Its own cone now
  contains no `sorry`. Its only non-standard axiom is Hermite's, which it reaches through
  Andréief's identity (6.10) and Proposition 2.2's moment representation.
* **The two project axioms still enter at exactly one place each**, by the same chains as on
  2026-09-23.

### 2.2 `#print axioms` — Lean's own

The following is from the same run and from `Audit.lean:279` in every clean-build log,
verbatim:

```
'Zeta5.zeta5_irrational' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Zeta5.Axioms.hermite_pole_integral,
 Zeta5.Axioms.pnt_prime_riemann_sum]
'Zeta5.theorem_1_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta5.RealBound.eq_6_14' depends on axioms: [propext, Classical.choice, Quot.sound, Zeta5.Axioms.hermite_pole_integral]
'Zeta5.RealBound.prop_6_3' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Zeta5.Axioms.hermite_pole_integral]
'C3ctl.uses_sorry_2' depends on axioms: [sorryAx]
'C3ctl.uses_axiom_2' depends on axioms: [C3ctl.planted_axiom]
```

*A caveat about methods (a) and (d).* In Lean 4.34, `#print axioms` and `Lean.collectAxioms`
do not walk the bodies of *imported* declarations. They read a per-declaration list of axioms
that was computed when each `.olean` was written (`exportedAxiomsExt`; see `collect` in
`Lean/Util/CollectAxioms.lean` of the toolchain). Only the walker (§2.1), the scan (§2.3) and
the `.olean` reader (§2.5) walk the proof terms themselves. All five methods agree, so the
stored lists match the bodies.

### 2.3 Module-keyed scan — `cert/final/FScan.lean` (verbatim, abridged where marked)

```
[1] constants in environment: 786934
    axiom declarations (17): [Classical.choice, Lean.ofReduceBool, Lean.ofReduceNat, Lean.trustCompiler, Quot.lcInv, Quot.sound, Zeta5.Axioms.hermite_pole_integral, Zeta5.Axioms.pnt_prime_riemann_sum, isScalarObj, lcAny, lcCast, lcErased, lcProof, lcUnreachable, lcVoid, propext, sorryAx]
[2] Zeta5 modules: 70; declarations defined in them: 3862
    axiom declarations (2): [Zeta5.Axioms.hermite_pole_integral, Zeta5.Axioms.pnt_prime_riemann_sum]
    declarations whose own type/value mentions sorryAx (0): []
    unsafe (0): []
    partial (10): [… five as on 2026-09-23, and Zeta5.Sec6.Num.{UUpR, aser, chainOK, isqrtIter, lser}._unsafe_rec]
    opaque (1): [Zeta5.Audit.visit]
[3] cone of Zeta5.zeta5_irrational: 69102 constants
    sorry carriers in the cone (0): []
    ... of which OUTSIDE the Zeta5 modules (0): []
    Zeta5 sorry carriers NOT in the cone, i.e. orphans (0): []
[4] direct users in the cone of each project axiom:
    Zeta5.Axioms.hermite_pole_integral  (1): [Zeta5.Positivity.integral_wt_div_pole]
    Zeta5.Axioms.pnt_prime_riemann_sum  (1): [Zeta5.PrimeSum.tendsto_primeSum]
[6] union cone of ALL 3862 Zeta5-module declarations: 74601 constants
    axioms reached (5): [Classical.choice, Quot.sound, Zeta5.Axioms.hermite_pole_integral, Zeta5.Axioms.pnt_prime_riemann_sum, propext]
    sorry carriers (0): []
[6-control] same walk + planted FScanCtl.uses_both: 74605 constants
    axioms reached (7): [Classical.choice, FScanCtl.planted_axiom, Quot.sound, …, propext, sorryAx]
    sorry carriers (1): [FScanCtl.planted_sorry]
```

The scan is keyed on the **defining module**, not on the namespace, so it includes internal
names and declarations placed in a foreign namespace. Of the 3 862 declarations the project
defines, exactly two are axioms and **none** mentions `sorryAx`. Section [6] is new. It walks
from *every* project declaration at once, including those outside the cone of the main
theorem (`Audit`, `Checks`, `AppendixBCheck`, the unused lemmas). It reaches only the same
five axioms. So no declaration anywhere in the project uses `sorryAx` or any other axiom.

`Lean.ofReduceBool` (`native_decide`), `ofReduceNat` and `trustCompiler` exist in core Lean as
always, but they are not reached. The ten `partial` constants are compile-only `_unsafe_rec`
auxiliaries of well-founded definitions. None of them is in the cone (§2.5: "unsafe/partial
constants in the cone (0)"). The per-module census (reached/defined) is in
`cert/final/FScan.out`. Every module of 2026-09-23 has the same count as then, except
`RealBound`: it had 140/320 and now has 151/318, because `eq_6_14` and `prop_6_3` moved to
`Sec6.Final` and the proof of (6.14) uses more of it. The 37 `Sec6` modules have 403 of their
592 declarations in the cone.

### 2.4 The project's own audit, from the clean-build logs (verbatim)

```
info: Zeta5/Audit.lean:203:0: ASSUMPTION REPORT for Zeta5.zeta5_irrational

  (A) standard Lean axioms:
    Classical.choice
    Quot.sound
    propext

  (B) explicit external axioms of this project (Zeta5/Axioms.lean):
    Zeta5.Axioms.hermite_pole_integral
    Zeta5.Axioms.pnt_prime_riemann_sum

  (C) sorry(s) — unfinished steps of the paper's own argument, 0 in all:
    (none)

  (D) any other axiom (must be empty):
    (none)

  [self-check: walker agrees with Lean.collectAxioms, 5 axiom(s)]
```

This is the same answer, name for name. Every `#sorry_tree` line says `depends on NO sorry`,
including the former negative control `Zeta5.RealBound.eq_6_14` and the five §6 controls
(`Sec6.Gram.eq_6_14_of_config`, `Sec6.Num.eq_6_7_closed`, `Sec6.eq_6_7_closed`,
`Sec6.configBound`, `Sec6.rho_energy_ge`). The report is identical in all four clean-build
logs. Two weaknesses of `Audit.lean` are noted in §7. Neither affects this answer.

### 2.5 Reading the `.olean` files directly — `cert/final/FOlean.lean`

This check is new. It uses `readModuleData` on every `.olean` in the search path (for
module-system files, all three parts) and builds its own constant table. It does not use
`importModules`, `Environment.find?` or `collectAxioms`. It walks with `getUsedConstants`, and
when a name is stored by more than one module it follows **every** stored version. So a
`sorry` could not hide in a proof that the environment would drop on import. (`lake env lean
--run cert/final/FOlean.lean --control Zeta5 Zeta5.zeta5_irrational …`, 38 s, same output on
two of the clean builds.)

```
modules read: 10814; constants in table: 786934; names stored by two different modules: 1020, …
Zeta5 modules read: 70; constants stored in them: 3863
  axioms (2): [Zeta5.Axioms.hermite_pole_integral, Zeta5.Axioms.pnt_prime_riemann_sum]
  sorryAx mentions (0): []
  unsafe (0): []
=== Zeta5.zeta5_irrational  (defined in (some Zeta5.Interface))
  constants reached: 69102
  axioms (5): [Classical.choice, Quot.sound, Zeta5.Axioms.hermite_pole_integral, Zeta5.Axioms.pnt_prime_riemann_sum, propext]
  sorryAx carriers (0): []
  referenced but in no olean read (0): []
  unsafe/partial constants in the cone (0): []
--- CONTROL (must report sorryAx, ctl.ax, ctl.s, ctl.missing, and the first target's axioms):
=== ctl.top  (defined in (some ctl))
  axioms (7): [Classical.choice, Quot.sound, Zeta5.Axioms.hermite_pole_integral, Zeta5.Axioms.pnt_prime_riemann_sum, ctl.ax, propext, sorryAx]
  sorryAx carriers (1): [ctl.s]
  referenced but in no olean read (1): [ctl.missing]
```

The count is 3 863 rather than 3 862 because one Zeta5 name is stored twice (§7, item 6). The
reader finds no `sorryAx` and no extra axiom in either stored version.

### 2.6 Kernel replay — `leanchecker`

`lake env leanchecker --verbose Zeta5` replays every declaration of every module whose name
begins with `Zeta5` through the kernel. It starts from the environment that the module's
imports give. It ran on the `git archive` build and covered **all 70 modules**
(`cert/final/leanchecker.out`: 70 `replaying` lines), ending with

```
lake env leanchecker --verbose Zeta5  491.69s user 2827.96s system 105% cpu 52:32.54 total
EXIT 0
```

**No module failed the replay.** (An earlier attempt on another build failed only because a
certifier had deleted that build's directory while it ran. Its output was discarded.)

---

## 3. The axioms

**No axiom is new, and neither changed.** At the level of kernel terms, both axioms are
byte-identical to those of 2026-09-23 (§5: `identical-to-main=True`). No axiom declaration
was added anywhere (§2.3 [2], §5). `Zeta5/Axioms.lean` is unchanged since `9ce1320`.
Therefore the attacks on the axioms made on 2026-09-23 still apply unchanged. They are
summarised at the end of this document:
* each axiom is blocked at its degenerate points, by hypotheses that are proved refutable;
* each is non-vacuous, since consequences of it were derived without `sorry`;
* each is true: Hermite's formula checked to 40 digits at eight values of `a`, and the prime
  Riemann sum at four test functions up to X = 10⁷.

`cert/C3Attack.lean` was re-run against this build (`cert/final/C3Attack.out`, exit 0). The
two non-vacuity consequences `C3att.hermite_at_one` and `C3att.pnt_dyadic` still depend on
exactly one project axiom each. `unbounded_blocked` uses no project axiom. The native walk
reaches the same 69 102 constants, with `unsafe or partial constants in the cone (0)`.

What is new is that the **§6 proof uses Hermite's axiom a second time**, through
Proposition 2.2's moment representation (`Positivity.prop_2_2_moment`), which Andréief's
identity (6.10) needs. It does so through the same single direct user,
`Positivity.integral_wt_div_pole` (§2.3 [4]). So the axiom is used in the one form that the
2026-09-23 attacks examined.

---

## 4. Is the statement still "ζ(5) is irrational"?

`cert/final/nochange/KeyStatements.lean` checks these facts on `Expr`s, and its output for
both `main` and HEAD is recorded in `key_main.out` and `key_head.out`:

```
zeta5_irrational: kind thm = true; levelParams = []; type == `Irrational Zeta5.zeta5` (Expr.equal): true; Irrational from some (Mathlib.NumberTheory.Real.Irrational)
```

* The theorem has no hypotheses and no universe parameters.
* `Irrational` is Mathlib's.
* The `pp.all` type and value of `zeta5`, and of `Delta`, `G`, `RealBound.Irho`,
  `RealBound.M0`, `K`, `N`, `h`, `lam` and `evalZeta5`, are identical on `main` and HEAD.

`diff key_main.out key_head.out` differs in two lines only: the defining modules of `eq_6_14`
and `prop_6_3`. `zeta5 = riemannZeta 5` was proved sorry-free on 2026-09-23
(`cert/C3Semantics.lean`), and every definition it involves is unchanged (§5). A re-run of
`cert/C3Semantics.lean` against this build is recorded in `cert/final/C3Semantics.out`
(11 s, exit 0). The statement is `Irrational Zeta5.zeta5` as an `Expr`, and
`C3sem.zeta5_eq_riemannZeta` depends on the three standard axioms only.
`C3sem.riemannZeta_five_not_rational : ∀ q : ℚ, (q : ℂ) ≠ riemannZeta 5` now depends on
`[propext, Classical.choice, Quot.sound, Zeta5.Axioms.hermite_pole_integral,
Zeta5.Axioms.pnt_prime_riemann_sum]`, with no `sorryAx`..

---

## 5. Were any statements changed? Kernel-level comparison with 2026-09-23

### 5.1 Method

The certifiers built `main` (`9ce1320`, the certified 2026-09-23 state) and `808618b` in two
separate `git worktree`s. Both used the same `.lake/packages` and an identical
`lake-manifest.json`, and Mathlib was not rebuilt. `cert/final/nochange/DumpDecls.lean` then
dumped **every constant whose defining module is `Zeta5.*`** in each environment. For each
constant it records:
* name, kind, module and universe parameters;
* a complete DAG serialisation of its **type** and of its **value** (for definitions and
  opaques, the body; for recursors, the rule right-hand sides), including binder names and
  binder info, levels, literals, `mdata` and projections;
* kind-specific metadata: safety and reducibility hints for definitions, the shape of
  inductives, and the fields of constructors and recursors.

`compare.py` hashes the serialisations with SHA-256 and compares the two dumps.
`alpha_check.py` decides whether the entries that differ are α-equivalent. The dumps are in
`cert/final/nochange/` (`main-9ce1320.tsv.gz`, `head-808618b.tsv.gz`, checksums in
`dumps.sha256`).

### 5.2 Result (verbatim from `compare.out` and `alpha.out`)

```
main: 3272 constants in Zeta5 modules; HEAD: 3862
removed (on main, not on HEAD): 0
common: 3272; changed kind/lparams/type/value/extra: 16
  CHANGED thm    Zeta5.InnerEntries.class_bound._proof_1_3  fields=['tsha']  …   [all 16 are *._proof_1_N]
common but defining module changed: 2
  MOVED   thm    Zeta5.RealBound.eq_6_14  Zeta5.RealBound -> Zeta5.Sec6.Final
  MOVED   thm    Zeta5.RealBound.prop_6_3  Zeta5.RealBound -> Zeta5.Sec6.Final
added on HEAD: 590  by kind: {'def': 93, 'thm': 497}
added constants in modules that existed on main:
all axioms on HEAD (Zeta5 modules):
  Zeta5.Axioms.hermite_pole_integral [Zeta5.Axioms] identical-to-main=True
  Zeta5.Axioms.pnt_prime_riemann_sum [Zeta5.Axioms] identical-to-main=True
16 constants with differing serialisation; 0 not alpha-equivalent
```

* **No statement and no definition changed.** All 3 272 declarations of the certified state
  are present, with the same kind and universe parameters. Every definition, opaque and
  recursor value is byte-identical, and so is every metadata field. Every type is identical,
  with 16 exceptions. These are compiler-generated auxiliary lemmas (`_proof_1_N` of
  `class_bound`, `rowW_le_halfB`, `tau_Tate`, `vge_H5`, `lemma_3_1`, `tau_monomial` and
  others), which are abstracted from inside proofs that the lint commit `808618b` edited.
  Their types differ only in hygienic binder names, for example `…_hyg.2819` against
  `…_hyg.2820`. They are α-equivalent, and Lean's own `Expr.hash`, which ignores binder
  names, is unchanged for all of them.
* **`eq_6_14` and `prop_6_3` moved** from `RealBound` to `Sec6.Final`, with identical types
  and the same names. No other constant changed its module.
* **All 590 additions are in the 36 new `Zeta5.Sec6.*` modules.** (The 37th, `Sec6.Final`,
  holds only the two moved theorems.) No module of 2026-09-23 gained a declaration. No axiom,
  opaque or `unsafe` declaration was added. The only `partial` additions are five compiler
  `_unsafe_rec` artifacts in `Sec6.Num.Eval`, and no other constant references them.
* **Everything outside the Zeta5 modules is the same:** 783 072 constants in both
  environments. No `Zeta5`-namespace constant is defined outside the Zeta5 modules.
* **Controls.** Three edits were planted in a copy of the HEAD dump:
  * a literal in `M0`'s value changed from 1329 to 1328;
  * the type of `zeta5_irrational` altered;
  * `lam` deleted.

  All three were reported: `REMOVED def Zeta5.lam`, `CHANGED def Zeta5.RealBound.M0
  fields=['vsha']`, `CHANGED thm Zeta5.zeta5_irrational fields=['tsha']`. `alpha_check`
  flagged both edited entries as `GENUINELY DIFFERENT`. The SHA-256 comparison also catches
  the hygienic renamings that `Expr.hash` misses, which serves as a natural positive
  control.

This settles more strongly than any text diff could that no statement was changed to make it
provable (README, 'Ground rules'). The comparison also rules out a change of meaning through
a definition, an instance or a notation.

### 5.3 The commit that adds this document

After the documentation changes of §7, the final agent rebuilt the tree and dumped it again
with `DumpDecls.lean`. The incremental rebuild succeeded (8994 jobs, 17 warnings, no `sorry`;
`cert/final/rebuild-after-comments.log`). It recompiled `Sec6.Gram`, `Sec6.Energy`,
`Sec6.Final` and their dependents. The new dump of its 3 862 constants has SHA-256
`dda2e28613bfc4b6ca531ceb34c298a0d052588782fa954f72420a2b646a5f8d`. That is the checksum of
the dump of `808618b` (`dumps.sha256`), and `cmp` confirms that the two files are identical
(`cert/final/nochange/dump-after-comments.out`). So the commit that adds this document
certifies the same declarations as `808618b`.

---

## 6. Fidelity of the §6 statements

All page references are to the preprint (v1). Pages 17–25 were rendered and read as images,
not as extracted text.

**(6.14), p. 20.** The paper states

    log Δ_K(ζ(5)) ≤ 2h(h+6N−K) log K + (λM₀ − I(ρ))K² + 18h log K + 160h.

`Zeta5.RealBound.eq_6_14` prints as

```
∀ (n : ℕ), 0 < n → 0 < evalZeta5 (Delta n) →
  Real.log (evalZeta5 (Delta n)) ≤
    2 * ↑(h n) * (↑(h n) + 6 * ↑(N n) - ↑(K n)) * Real.log ↑(K n) +
      (↑lam * RealBound.M0 - RealBound.Irho) * ↑(K n) ^ 2 + 18 * ↑(h n) * Real.log ↑(K n) + 160 * ↑(h n)
```

Here K = 40n, N = 3n, h = 37n and λ = 37/40, so the statement matches the paper **term for
term**. It is textually identical to the statement that was a `sorry` at `9ce1320`.

**(6.16), p. 20.** `prop_6_3` states `log F_K(ζ(5)) ≤ ŪK² + 24K log K + 200K`, with
`Ubar = −2733991/2000000`, as in (6.4). The positivity half of (6.16) is `Zeta5.F_pos`.

**Not vacuous.** The hypothesis `0 < Δ_K(ζ(5))` is discharged by
`delta_pos : ∀ n, 0 < evalZeta5 (Delta n)`, which follows from Proposition 2.2. An `example`
applying `eq_6_14 n hn (delta_pos n)` typechecks, and `Zeta5.prop_6_3` is
`fun n hn => RealBound.prop_6_3 n hn (delta_pos n)` (`cert/final/fidelity/Fidelity.out`).

**Constants, from the PDF** (`cert/final/fidelity/constants.py`):
* Table 1, parsed from the PDF text, equals the Lean `aT`, `bT`, `cT` in all 16 rows.
* Σc = 0.925 = λ.
* `Irho` = (A.2) = −2.126593445147050403…, the same as the independent double sum
  Σ c_j c_k log(L_max(j,k)/4).
* `M0` = −6.645, and λM₀ − I(ρ) = −4.02003155485….
* C_* = 2.65303599034…, and λM₀ − I(ρ) + C_* = −1.36699556451 ≤ Ū = −1.3669955.

The definitions `Vfield`, `Vclosed` and `Uarc` match (6.1), (A.5) and (A.1). `Irho` is (A.2)
with weights S_{j+1}² − S_j².

**The route, checked against the code.** The documented constants of the §6 route are what
the Lean statements say:
* the parameter is ε = ((16K)⁻¹)²;
* (6.9') ends in `2h log K + 20h` (`configBound`);
* `eq_6_14_of_config` accepts `(λM₀−I)K² + 3h log K + 131h`, and `paper_6_9_admissible`
  holds;
* the cross-term bound is `88√ε + 420ε`, and `smooth_err_norm` gives `π(δ + π√(2δ))`;
* `integral_g_le` gives ≤ 326K⁶, and `gram_bound` keeps the h! of (6.10);
* `tail_bound_ge4` covers t ≥ 4.

`count_cells.py` finds 1049 cells on [0, 2], all with bound −1329/200, which tile [0, 2]
contiguously, and 2 cells on [2, 4] with bound M₀ − 3/10 = −1389/200. Re-running
`numerics/sec6/gen_lean.py` in a scratch copy regenerates `Num/Seg1`–`Seg6` and
`Num/Final.lean` byte for byte.

The statements are in the cone of `zeta5_irrational` as documented
(`cert/final/fidelity/Cone.out`):
* in the cone: `eq_6_14`, `configBound`, `cauchy_cnd`, `Num.eq_6_7_closed`, `Gram.andreief`,
  `rho_energy_ge`;
* proved but not used, as the documentation says: `reg_const_le_sixty`, `table2_tiles`,
  `paper_6_9_admissible`.

**The 19 leaves.** `leaf_stmts.py` compares the statements at `4dea216`, where they were
`sorry`s, with HEAD. There is no change in any of the 19, nor in `eq_6_14`, `prop_6_3`,
`configBound`, `eq_6_14_of_config` or the §6 definitions. `Sec6/Defs.lean` has no diff at
all. The count of `sorry`s is 19 at `4dea216` and 0 at HEAD.

**Spot-checks: each statement means what its docstring says.**
* `cauchy_cnd`: for finite α, β carried by [−R, R] with α(ℝ) = β(ℝ) and ε > 0,
  kE ε α α − 2 kE ε α β + kE ε β β ≤ 0. This is the zero-mass energy inequality for kC ε.
* `arcsine_pot`: for a < b,
  ∫₀^π log|t − ((a+b)/2 + (b−a)/2 cos θ)| dθ = π·Uarc a b t, with integrability. This is
  (A.1) for the push-forward of dθ/π.
* `eq_6_6_cauchy`: for injective t with m = λK,
  m log ε + 2Σ_{i<j} log|t_i − t_j| ≤ 2KΣU^ρ(t_i) − K²I(ρ) + 2Km(88√ε + 420ε).
  `configBound_of_log` handles coincident points, where the product is 0.
* `Gram.andreief`: m!·det(∫φ_iφ_j w dμ) = ∫ det(φ_i(x_k))² ∏w(x_k) dμ^m, for σ-finite μ.
  `eq_6_10`: h!·Δ = ∫_{(0,∞)^h} (∏_{i<j}(y_j² − y_i²))² ∏ fW(y_k).
* `Num.cell_sound`: `cellOK M l r = true` and l ≤ t ≤ r imply 2·Uclosed t − Vclosed t ≤ M.
  `Uclosed_eq_Urho` and `Num_Vclosed_eq` (`rfl`) connect it to the §6 definitions.

**Numerical tests.** `python3 numerics/sec6/check_leaves.py` gives 133 PASS and 0 FAIL, with 7
must-fail controls, and its output is byte-identical to the committed `check_leaves.out`. It
includes `PASS max_{t in (0,4]} 2U^rho - V <= M0 max=-6.649897 M0=-6.645`.

---

## 7. Defects and caveats found, and how they were resolved

None of these affects the assumption list or any statement.

1. **The certification documents described the old state** (doc issue). `cert/README.md`
   and this file were written for 2026-09-23: 33 modules, a 25-minute `leanchecker` run,
   `eq_6_14` as the one `sorry` and as the negative control. The README, `STATUS.md` and
   `docs/lean-status.pdf` said so. *Resolved:* this document and `cert/README.md` were
   rewritten, the 2026-09-23 material was kept in its own section, and README, `STATUS.md`
   and `lean-status.tex`/`.pdf` were updated.
2. **Stale warning counts** (doc issue). `STATUS.md` said "267 warnings", and the README said
   "about 270 warnings, all of them Mathlib deprecation notices". The clean build of
   `808618b` has 17 warnings, none of them a deprecation. *Resolved:* both files now give
   the 17 warnings and their kinds, and the build time of the clean builds.
3. **"The factor 1/h! of (6.10), which the paper drops"** (doc issue, in the README,
   `STATUS.md` deviation 21, and the module comments of `Sec6/Final.lean` and
   `Sec6/Gram.lean`). This was imprecise. The paper keeps 1/h! in (6.13) and discards it
   implicitly (log h! ≥ 0) only when it takes logarithms for (6.14). Nor is the factor
   needed with the configuration bound Lean proves: 2h log K + 20h gives a linear constant of
   about 46.8h, well under 160h. It is what lets `eq_6_14_of_config` accept 3h log K + 131h.
   *Resolved:* the wording was corrected in all four places. In the Lean files only the
   module comments changed (§5.3).
4. **"Every leaf statement was tested numerically, with must-fail controls"** (doc issue,
   `Sec6/Final.lean` module comment, README, `STATUS.md`). This overstated the tests. In
   `check_leaves.py`:
   * `kE_rhoM_expand` has no test of its own;
   * the two branches of (A.1) are tested together, through `integral_log_abs_sub_cos`;
   * there are 7 must-fail controls in all, not one per leaf.

   *Resolved:* the wording in all three places now says exactly this.
5. **`Audit.lean` is weaker than the module-keyed scans** (note, not changed). Its
   `allSorries` skips internal names (`!n.isInternal`) and checks only bodies. Its orphan
   message ("every sorry of the Zeta5 namespace is used by …") also prints when there are no
   sorries at all. The module-keyed scan and the `.olean` reader (§§2.3, 2.5) have neither
   limitation, and they found no `sorryAx` anywhere. Changing `Audit.lean` would change
   project definitions, which the ground rules forbid for this pass. The limitation is
   recorded here and in `STATUS.md` §7.
6. **A duplicated theorem name** (note, not changed). `Zeta5.vGAtLeast_mul` is declared in
   both `Section41.lean` and `Normalization.lean`, with the same type. Lean 4.34 accepts the
   duplicate on import (`subsumesInfo`) and keeps one proof, so a walker based on the
   environment sees only one of the two. The `.olean` reader follows both stored versions and
   finds no `sorryAx` and no extra axiom in either. The other 8 Zeta5 names stored twice are
   equation lemmas (`.eq_1`) that are identical in both modules.
7. **The shared build directory was emptied during the certification** (process note).
   A certifier running a clean build wiped `.lake/build` of the repository checkout. The
   other certifiers noticed, did not build there, and used their own clean builds of
   identical sources (§1). *Resolved:* the final agent rebuilt the checkout from scratch
   (§1).
8. **17 lint warnings remain** (note). Clearing them would change theorem signatures (§1).

---

## 8. Independence: no other formalization was consulted

The ground rules of the project forbid consulting other formalizations of Fauzan's proof. The
user asked for a check, so the Claude Code transcripts of the project were scanned for tool
calls that reach the network: `WebSearch`, `WebFetch`, any `mcp__*` tool, `curl`/`wget` in
shell commands, and `ToolSearch` loads of web tools.

* **The sessions of 2026-09-24** (the §6 blueprint `4dea216`, the proofs `b5b712e`, the lint
  clean-up `808618b`, and this certification) are 59 transcripts, from 20:51 UTC on
  2026-09-24 onwards. They made **no web access of any kind**: zero `WebSearch`, `WebFetch`
  or MCP calls, and no `ToolSearch` query for a web tool. The only shell commands that
  matched the pattern were a `git clone` of the local repository and the transcript scans
  themselves.
* **The earlier sessions** (up to 2026-09-24 00:01 UTC, the work that produced the
  2026-09-23 state) made 205 web calls, for literature and citation lookups (DLMF, Crossref,
  Springer and the like). No tool call named another formalization. One exposure did occur.
  On 2026-09-23 a research agent on the Lemma 6.1 track searched for the preprint itself
  ("Hankel determinant zeta(5) irrational Fauzan 2026 preprint Zenodo"). The results listed
  the title and address of another public Lean formalization of the preprint. The agent never
  fetched that address and never mentioned it. The address occurs nowhere in this
  repository or in the project's notes.

The transcripts are not part of the repository, so this scan cannot be re-run from here. Its
result is recorded here and in the README ('Provenance').

---

## 9. Verdict

> There is a Lean 4 formalisation, machine-checked against Mathlib v4.34.0 from clean
> rebuilds of all 70 of its modules, of a single theorem `Zeta5.zeta5_irrational :
> Irrational Zeta5.zeta5`.
>
> The theorem has no hypotheses. `Irrational` is Mathlib's, and `Zeta5.zeta5` is the real
> number ∑_{n≥1} n⁻⁵, which was proved equal to Mathlib's `riemannZeta 5`.
>
> Five independent methods agree on what the proof rests on:
> * Lean's `#print axioms`;
> * the project's audit metaprogram;
> * a dependency walker validated on planted controls;
> * a scan of all 3 862 project declarations, keyed on their defining module, with a walk
>   from all of them at once;
> * a reader that walks the compiled `.olean` files without using Lean's environment.
>
> A kernel replay of every module by `leanchecker` passed.
>
> The proof rests on Lean's three standard axioms and on **two** explicit external axioms,
> and on **no `sorry`**:
> * Hermite's integral formula for the Hurwitz zeta function at s = 5, carried through four
>   unformalised integrations by parts;
> * the prime number theorem in partial-summation ("prime Riemann sum") form.
>
> Both axioms are true classical statements, each blocked at its degenerate points and each
> used at exactly one place in a dependency cone of 69 102 constants.
>
> A. Fauzan's inequality (6.14) was the only unproved step on 2026-09-23. It is now proved
> with its statement unchanged, by a route that differs from the paper's in places (a
> regularised kernel on the real line, and a certified partition of the formalisation's own).
> Its statement and that of (6.16) match the preprint term for term.
>
> A kernel-level comparison with the certified state of 2026-09-23 shows that no statement or
> definition changed. All additions are in the new §6 modules. No axiom was added or altered.
>
> The correct way to report the result is: **"ζ(5) is irrational, machine-checked
> conditional on two external results entered as axioms — Hermite's integral formula (in the
> integrated-by-parts form of p. 5) and the prime number theorem in partial-summation
> form."** Both axioms are slightly stronger than their bare citations (`STATUS.md` §2 (B)).
> Nothing internal to Fauzan's argument is assumed. It is never correct to say "modulo
> standard facts" without naming the two axioms.

---

## Scripts (none is part of `lake build`)

Run from the repository root, after `lake exe cache get` and `lake build`:

```
lake env lean cert/final/FWalker.lean          # own BFS walker, chains, 5 planted controls, 37 targets (~12 min)
lake env lean cert/final/FScan.lean            # module-keyed scan, union cone of all declarations, census (~8 min)
lake env lean --run cert/final/FOlean.lean --control Zeta5 Zeta5.zeta5_irrational Zeta5.theorem_1_1 \
    Zeta5.theorem_2_1 Zeta5.RealBound.eq_6_14 Zeta5.RealBound.prop_6_3   # direct .olean reader (~40 s)
lake env leanchecker --verbose Zeta5           # kernel replay of all 70 modules (~50 min)
python3 cert/final/source_scan.py              # forbidden constructs in the sources
lake env lean --run cert/final/nochange/DumpDecls.lean <out.tsv> Zeta5   # per-declaration dump
python3 cert/final/nochange/compare.py <main.tsv> <head.tsv>             # compare two dumps
python3 cert/final/nochange/alpha_check.py <main.tsv> <head.tsv>         # α-equivalence of differences
lake env lean cert/final/nochange/KeyStatements.lean                     # key statements as Exprs
lake env lean cert/final/fidelity/Fidelity.lean   # (6.14)/(6.16) as stated, non-vacuity, axioms
lake env lean cert/final/fidelity/Cone.lean       # cone membership of named §6 declarations
python3 cert/final/fidelity/constants.py pp17-25.txt   # Table 1 and the constants (needs the PDF text, see the script)
python3 cert/final/fidelity/count_cells.py        # the certified cells tile [0,2]
python3 cert/final/fidelity/leaf_stmts.py         # leaf statements unchanged since 4dea216
```

`cert/README.md` lists the recorded outputs. The scripts of the 2026-09-23 certification
(`cert/C3*.lean`, `cert/c3/`) still run against the present build. Their recorded outputs
refer to the 2026-09-23 state.

---

## Earlier certification (2026-09-23)

*This section summarises the certification of the state of 2026-09-23 (`main`, `9ce1320`: 32
modules, one `sorry`, `Zeta5.RealBound.eq_6_14`). Its scripts are `cert/C3Walker.lean`,
`cert/C3Scan.lean`, `cert/C3Semantics.lean` and `cert/C3Attack.lean`, and its outputs are in
`cert/c3/`. Counts in this section refer to that state. The results about the axioms (§E.2)
and about the statement (§E.3) still apply without change, because `Axioms.lean` and every
definition involved are byte-identical at the kernel level (§5).*

### E.1 Verdict then

The claim was that the proof depends only on the two axioms and on the one listed `sorry`,
and it held. Five methods agreed that the theorem rested on the three standard axioms, the two
project axioms and exactly one `sorry`, `RealBound.eq_6_14`: `C3Walker` (62 097 constants),
`#print axioms`, `C3Scan` (3 272 declarations, 1 `sorryAx` carrier), `Audit.lean`, and
`leanchecker` (33 modules, 25 min, exit 0).

A walker built on `ConstantInfo.value?` was run as a negative control. It reached only 1 472
constants and reported no `sorry`. The four interface statements proved last
(`outer_local_analysis`, `PrimeSum.eq_5_7_uniformity`, `CrudeBound.crude_entry_bound`,
`Section3.entry_bounds_4_2_4_3`) were closed with no `sorryAx` below them. A kernel-level
comparison with a pre-release snapshot (not published) found no changed statement or
definition. The clean build took 4 min 26 s and had 249 warnings, one of them the `sorry`.

### E.2 The axioms: false, vacuous, too strong?

**`hermite_pole_integral`**: `∀ a > 0, ∫_0^∞ w(y)/(y²+a²) dy = a⁴ζ(5,a) − 1/(2a) − 1/4`.
* *Route to `False`?* Lean's junk values could make the formal statement false only where the
  integrand is not integrable or the Hurwitz sum is not summable. Both happen only for
  a ≤ 0, and the hypothesis `0 < a` is proved refutable at a = 0 and a = −1
  (`hermite_guard_zero`, `hermite_guard_neg`). For a > 0 the formal equation is the
  classical, true one.
* *True?* It was recomputed with independent code: `w` from the Lean definition via
  `∑ℓ⁴qˡ = q(1+11q+11q²+q³)/(1−q)⁵`, and Hurwitz ζ from mpmath at 40 digits. At a = 0.01,
  0.2, 0.7, 1, 1.5, 4, 25 and 1000, |LHS − RHS| < 10⁻³⁹. At a = 1 both sides equal
  ζ(5) − 3/4.
* *Vacuous?* No. `C3att.hermite_at_one : ∫_0^∞ w(y)/(y²+1) dy = zeta5 − 3/4` is derived from
  it without `sorry`.
* *Too strong?* No. It has one direct user (`Positivity.integral_wt_div_pole`).
  `theorem_1_1`, the step that deduces irrationality, uses no project axiom.
* *Caveat:* it is DLMF 25.11.29 after the four integrations by parts of p. 5, which are not
  formalised.

**`pnt_prime_riemann_sum`**: `X⁻¹∑_{⌊aX⌋<p≤⌊bX⌋} φ(p/X) log p → ∫_a^b φ`, for 0 ≤ a < b and
φ bounded on [a, b] and continuous off a finite set.
* *Route to `False`?* φ is bounded and a.e. continuous, so the Bochner integral is the
  Riemann integral and never a junk 0. The sum evaluates φ only on (a, b]. The degenerate
  cases a = b and a < 0 are blocked by refutable hypotheses (`pnt_guard_empty`,
  `pnt_guard_neg`), and an unbounded φ cannot meet the hypotheses (`unbounded_blocked`).
* *True?* It was tested with a numpy sieve to 3·10⁷ on y² over [1/2, 3/2], cos 3y over
  [0, 2], a two-jump step function and frac(5y), at X = 10⁵, 10⁶ and 10⁷. All four
  converge to ∫φ at the expected rate.
* *Vacuous?* No. `C3att.pnt_dyadic : (θ(2X) − θ(X))/X → 1` is derived from it.
* *Too strong?* No. It has one direct user (`PrimeSum.tendsto_primeSum`).
* *Caveat:* it is the partial-summation corollary of the PNT, not θ(x) ~ x itself.

**Interaction.** The two axioms share no constant and no hypothesis. Each is a true classical
statement, so together they are consistent relative to Mathlib.

(Scripts: `cert/C3Attack.lean`, `cert/c3/axioms_numeric.py`; outputs `cert/c3/C3Attack.out`,
`cert/c3/axioms_numeric.out`.)

### E.3 The statement — `cert/C3Semantics.lean`

* The type of `zeta5_irrational` is syntactically
  `.app (.const Irrational []) (.const Zeta5.zeta5 [])`.
* `Irrational` is defined in `Mathlib.NumberTheory.Real.Irrational`.
* `zeta5` is the `tsum` (unconditional summation filter) of `1/(v+1)⁵`, and every constant in
  its definition comes from `Init` or Mathlib.
* `zeta5 = riemannZeta 5` is proved without `sorry`, via `zeta_nat_eq_tsum_of_gt_one`, an
  index shift and `Complex.ofReal_tsum`. So is `1 ≤ zeta5`, which rules out a junk 0.
* `riemannZeta_five_not_rational : ∀ q : ℚ, (q : ℂ) ≠ riemannZeta 5` follows from the
  theorem, with exactly its assumptions.

### E.4 PDF spot-checks of statements proved before 2026-09-23 (still accurate; statements unchanged)

1. `Lemma33.lemma_3_3` is Lemma 3.3 (p. 8) as printed, for every prime p, every K and every d.
   The hypothesis "integer-valued on ℤ_p" is taken as `∀ z : ℤ, |A(z)|_p ≤ 1`, which is
   equivalent by density.
2. `InnerEntries.raabe_tau` is (3.7) for polynomials (p. 7), for every m ≥ 1.
3. `OuterBasis.L0_eq_zero` and `rank_L0` are the rank argument of (4.10), pp. 11–12. The
   hypothesis `i + j + 6N + 3 < K + 2p` is literally i + j < K − 6N + 2p − 3. The resulting
   rank bound is slightly sharper than printed.
4. `HermiteBasis.det_coeffMatrix_unimodular` gives the unimodularity of (4.5) (p. 10) and of
   (4.11) (p. 12). The conclusion is the same, and the proof is different.
5. `Uniformity.eq_5_7_uniformity` is (5.7) and the two §5.2 displays (pp. 14–15), bundled with
   one constant C = 400M². The definitions `Gam`, `NR`, `R0`, `dRank` and `Tout` were
   re-read against (5.4), (5.5), (5.8) and (5.9).

No weakened statement was found.

### E.5 The then-remaining `sorry`, tested

`cert/c3/eq_6_14_control.py` parses `Irho`, `M0` and `lam` from the Lean source and evaluates
(6.14) at K = 40, 80, 120, using exact values of log Δ_K(ζ(5)) from the referee audit
(`cert/c3/delta_K_values.json`). It held at all three, with slack 7876, 16535 and 25524, and
`Irho` agreed with the audit's (A.2) to 25 digits. This was a consistency check of the
transcription. (6.14) is now proved.

### E.6 Defects found then

* One sentence of `STATUS.md` §1 overstated what was formalised. It said "every arithmetic
  part", where the correct claim is "every arithmetic statement the proof uses"; three of the
  paper's proofs are bypassed. The sentence was corrected.
* A stray scratch file sat at the package root. It was not imported and not built, and it was
  removed.

Neither affected the assumption list. The report then was: *"ζ(5) is irrational,
machine-checked conditional on one explicitly named unproved statement of the paper — (6.14) —
plus Hermite's integral formula and the prime number theorem in partial-summation form."*
That report is superseded by §9.
