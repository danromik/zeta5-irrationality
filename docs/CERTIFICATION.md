# Adversarial certification of the Zeta5 Lean development

**Date:** 2026-09-23 · **Toolchain:** Lean 4.34.0, Mathlib v4.34.0 · **State certified:** the
state described in `STATUS.md`

*This certification was carried out by Claude (Anthropic), in a run separate from the one that
developed the proofs (see README, 'Provenance'); "I" below is the certifier. The scripts are in `cert/`, their
recorded outputs in `cert/c3/`, and `cert/README.md` gives the commands to re-run them from the
repository root. Earlier certification passes, against earlier states of the development, are
not published.*

*Note added for publication.* After this certification, comments and docstrings in the Lean
sources were edited for public release; no Lean code was changed. A per-declaration dump of the
rebuilt project (`cert/c3/DumpEnv.lean`), compared with the dump of the certified build, shows
no change of kind, module, universe parameters, type or value in any of the 3 228 declarations
the two have in common (the certified dump did not include the 44 declarations of
`Zeta5/Audit.lean`). Line numbers and byte-level comparisons of source files quoted below refer
to the certified state, and some line numbers differ by one or two in the published sources.

**The claim under attack.** *"`Zeta5.zeta5_irrational` faithfully states that ζ(5) is
irrational, and depends only on the two axioms in `Zeta5/Axioms.lean` and the sorries that
`STATUS.md` lists"*, where `STATUS.md` lists **one** `sorry`: `Zeta5.RealBound.eq_6_14`.

**Verdict in one line.** **The claim holds.** Five independent methods agree that the theorem
rests on Lean's three standard axioms, the two axioms of `Axioms.lean`, and exactly one
`sorry`, `RealBound.eq_6_14`. The four interface statements that were proved last
(`STATUS.md` §3) are **closed in the strict sense**: `#print axioms` shows no `sorryAx` for any
of them. The statement is Mathlib's `Irrational` applied to `∑_{n≥1} n⁻⁵`, which I proved equal
to `riemannZeta 5`. Checked at the level of kernel terms against a snapshot taken before those
four proofs were written, none of the 2 185 declarations of the snapshot changed its statement
or definition; the only differences are seven auxiliary lemmas inside two proofs, which were
renumbered. No axiom was added. I found no defect that affects the result. One sentence of
`STATUS.md` overstated what is formalised (§7; since corrected).

---

## 0. What was run, and where the evidence is

| # | check | tool | result |
|---|---|---|---|
| 1 | clean build | `.lake/build` deleted, `lake build` | exit 0, 0 errors, **1** `sorry` warning |
| 2a | dependency walk | `cert/C3Walker.lean`, my own walker | 1 `sorry` leaf, 6 axioms, agrees with `collectAxioms` on 16 cones |
| 2b | `#print axioms` | Lean's own | same |
| 2c | module-keyed scan | `cert/C3Scan.lean` | 2 axioms and 1 `sorry` carrier among 3 272 Zeta5 declarations; 0 orphans |
| 2d | project audit | `Zeta5/Audit.lean`, output from my clean build | same |
| 2e | kernel replay | `leanchecker Zeta5` (ships with Lean 4.34) | all 33 modules re-checked by the kernel, exit 0 |
| 2f | trusted base | `git status` in every `.lake/packages/*` | 0 modified files; Mathlib at tag `v4.34.0` |
| 3 | axiom attacks | `cert/C3Attack.lean`, `cert/c3/axioms_numeric.py` | no route to `False` and no trivial route to the theorem; both axioms confirmed numerically |
| 4 | statement | `cert/C3Semantics.lean` | type is literally `Irrational Zeta5.zeta5`; `zeta5 = riemannZeta 5` proved sorry-free |
| 5a | kernel-level diff vs a pre-release snapshot | `cert/c3/DumpEnv.lean` (the snapshot and the comparison script are not published) | 0 changed statements, 0 changed definitions |
| 5b | text diff of six statements vs the same snapshot | (not published) | 6/6 statements byte-identical |
| 5c | PDF spot-checks | pp. 7, 8, 10–15 page images | 5/5 faithful |
| + | known-answer control for the last `sorry` | `cert/c3/eq_6_14_control.py` | (6.14) holds at K = 40, 80, 120 |

Every output quoted below is in `cert/c3/*.out` or `cert/c3/clean-build.log`, except those of
checks 5a and 5b, which need the unpublished snapshot.

---

## 1. Clean build

`.lake/build` held only Zeta5 artifacts (264 files; Mathlib and the other packages live in
`.lake/packages`). I **deleted it** (`rm -rf`; afterwards no Zeta5 artifact existed anywhere
under `.lake` outside `packages`), confirmed that no other Lean or Lake process was running,
and ran `lake build`.

Start 10:38:15, end 10:42:41 (4 min 26 s), **exit 0**. All 32 modules and the root were
recompiled from source; every `.olean` carries a timestamp between 10:38:29 and 10:42:27, and
no Lake artifact cache is configured (`LAKE_CACHE_DIR` unset, no user-level Lake cache). Every
`Built` line, verbatim:

```
✔ [8924/8957] Built Zeta5.Basic (11s)
✔ [8925/8957] Built Zeta5.HermiteBasisCore (11s)
✔ [8926/8957] Built Zeta5.Axioms (16s)
ℹ [8927/8957] Built Zeta5.HermiteBasis (17s)
ℹ [8928/8957] Built Zeta5.Normalization (18s)
✔ [8929/8957] Built Zeta5.Asymptotics (19s)
ℹ [8930/8957] Built Zeta5.Functional (19s)
ℹ [8931/8957] Built Zeta5.Lemma42 (19s)
✔ [8932/8957] Built Zeta5.Skeleton (19s)
✔ [8933/8957] Built Zeta5.Tail (20s)
✔ [8934/8957] Built Zeta5.Counting (22s)
⚠ [8935/8957] Built Zeta5.RealBound (32s)
ℹ [8936/8957] Built Zeta5.OuterLocal (16s)
ℹ [8937/8957] Built Zeta5.Positivity (23s)
ℹ [8938/8957] Built Zeta5.Section41 (20s)
ℹ [8939/8957] Built Zeta5.Arithmetic (14s)
⚠ [8940/8957] Built Zeta5.AppendixB (37s)
⚠ [8941/8957] Built Zeta5.LocalFunctional (17s)
ℹ [8942/8957] Built Zeta5.OuterBasis (18s)
ℹ [8943/8957] Built Zeta5.Uniformity (26s)
⚠ [8944/8957] Built Zeta5.InnerTate (15s)
⚠ [8945/8957] Built Zeta5.OuterRange (16s)
ℹ [8946/8957] Built Zeta5.Lemma33 (17s)
⚠ [8947/8957] Built Zeta5.InnerGeneral (15s)
⚠ [8948/8957] Built Zeta5.PrimeSum (22s)
⚠ [8949/8957] Built Zeta5.InnerEntries (15s)
ℹ [8950/8957] Built Zeta5.Section3 (13s)
⚠ [8951/8957] Built Zeta5.CrudeBound (14s)
✔ [8952/8957] Built Zeta5.Interface (14s)
ℹ [8953/8957] Built Zeta5.AppendixBCheck (14s)
ℹ [8954/8957] Built Zeta5.Checks (14s)
ℹ [8955/8957] Built Zeta5.Audit (60s)
✔ [8956/8957] Built Zeta5 (13s)
Build completed successfully (8957 jobs).
```

**Errors: 0.** **`declaration uses 'sorry'` warnings: exactly one**, verbatim:

```
warning: Zeta5/RealBound.lean:856:8: declaration uses `sorry`
```

There are 249 warnings in all. The other 248 are lints: 194 deprecations (171 "has been
deprecated: Use … instead", 23 "Prefer using … instead"), 14 unused section variables, 14
unused simp arguments, 9 "try `simp` instead of `simpa`", 7 unused tactics, 3 unreachable
tactics, 3 unused variable names, 3 "Try this", and 1 deprecation with no replacement. None of
them affects soundness. These counts agree with `STATUS.md` (1 + 248).

**Sources are clean.** `grep` over `Zeta5/*.lean`: the only `axiom` declarations are the two
lines of `Axioms.lean`. There is no `native_decide`, `implemented_by`, `@[extern]`, `unsafe`,
`#exit`, `debug.skipKernelTC`, `set_option`, `macro`/`elab`/`syntax`/`notation` outside
`Audit.lean`, `run_cmd`, `#eval`, or `opaque`. `lakefile.toml` sets only four benign
`leanOptions` (`pp.unicode.fun`, `relaxedAutoImplicit = false`,
`weak.linter.mathlibStandardSet = false`, `maxSynthPendingDepth = 3`). A stray scratch file
at the package root (not imported, not built; a single `example` applying
`OuterBasis.outer_local_core`) was not part of the library; it has since been removed.

**Dependencies are unmodified.** All nine packages in `.lake/packages` (`mathlib`,
`batteries`, `aesop`, `Qq`, `plausible`, `importGraph`, `LeanSearchClient`, `Cli`,
`proofwidgets`) are git checkouts with **zero modified tracked files**. Mathlib is at tag
`v4.34.0` (`5ed2965256430c3649e86755f9576b54eca72435`), the revision `lake-manifest.json` pins.
So nothing in the trusted base was edited locally.

---

## 2. Five independent dependency checks, all agreeing

### 2.1 My own walker — `cert/C3Walker.lean`

This walker is written from scratch. It shares no code with `Zeta5/Audit.lean` or with the
walkers of earlier certification passes (not published), and it is built differently from
them:

* the `Expr` traversal is **iterative**, using an explicit stack and written out from the
  `Expr` constructors. It never calls `getUsedConstants`/`foldConsts`, and a structural
  `HashSet Expr` makes each shared sub-term visit once;
* the constant walk is **breadth-first**, and it records a parent pointer for every constant,
  so each `sorry` leaf and each project axiom is printed with a **shortest provenance chain**;
* it matches on the `ConstantInfo` constructor and **never calls `ConstantInfo.value?`**;
* its successor relation is **deliberately generous**, a superset of
  `Lean.CollectAxioms.collect`: it also follows axiom types, `.proj` structure names, the
  `all` fields, recursor rule right-hand sides, and a constructor's inductive type;
* it has **built-in positive controls**, all defined in the file: a planted `sorry` and a
  planted `axiom`, each used two levels down.

Output, verbatim (`lake env lean cert/C3Walker.lean`, exit 0, 4–8 min):

```
=== C3 C3ctl.uses_sorry_2
  constants reached : 327   (missing from env: 0)
  axioms (1) : [sorryAx]
  vs Lean.collectAxioms : AGREE
  sorry leaves (1) : [C3ctl.planted_sorry]
    chain to sorry leaf  : C3ctl.uses_sorry_2 → C3ctl.uses_sorry_1 → C3ctl.planted_sorry   [3 links]
=== C3 C3ctl.uses_axiom_2
  constants reached : 36   (missing from env: 0)
  axioms (1) : [C3ctl.planted_axiom]
  vs Lean.collectAxioms : AGREE
  sorry leaves (0) : []
    chain to axiom       : C3ctl.uses_axiom_2 → C3ctl.uses_axiom_1 → C3ctl.planted_axiom   [3 links]
=== C3 C3ctl.clean
  constants reached : 32   (missing from env: 0)
  axioms (0) : []
  vs Lean.collectAxioms : AGREE
  sorry leaves (0) : []
TRAP Zeta5.zeta5_irrational: theorem=true  value?.isSome=false  broken walker visits 1472 constants, finds sorry: false
TRAP C3ctl.uses_sorry_2: theorem=true  value?.isSome=false  broken walker visits 30 constants, finds sorry: false
=== C3 Zeta5.zeta5_irrational
  constants reached : 62097   (missing from env: 0)
  axioms (6) : [Classical.choice, Quot.sound, Zeta5.Axioms.hermite_pole_integral, Zeta5.Axioms.pnt_prime_riemann_sum, propext, sorryAx]
  vs Lean.collectAxioms : AGREE
  sorry leaves (1) : [Zeta5.RealBound.eq_6_14]
    chain to sorry leaf  : Zeta5.zeta5_irrational → Zeta5.theorem_2_1 → Zeta5.decay_2_7 → Zeta5.decay_of_margin → Zeta5.eq_7_1 → Zeta5.prop_6_3 → Zeta5.RealBound.prop_6_3 → Zeta5.RealBound.eq_6_14   [8 links]
    chain to axiom       : Zeta5.zeta5_irrational → Zeta5.theorem_2_1 → Zeta5.Q_pos → Zeta5.F_pos → Zeta5.delta_pos → Zeta5.prop_2_2 → Zeta5.Positivity.prop_2_2 → Zeta5.Positivity.quadForm_eq_integral → Zeta5.Positivity.prop_2_2_moment → Zeta5.Positivity.integral_pole_term → Zeta5.Positivity.integral_wt_div_pole → Zeta5.Axioms.hermite_pole_integral   [12 links]
    chain to axiom       : Zeta5.zeta5_irrational → Zeta5.theorem_2_1 → Zeta5.decay_2_7 → Zeta5.decay_of_margin → Zeta5.eq_7_1 → Zeta5.eq_5_21 → Zeta5.prop_5_2 → Zeta5.PrimeSum.prop_5_2 → Zeta5.PrimeSum.tendsto_P2 → Zeta5.PrimeSum.tendsto_primeSum → Zeta5.Axioms.pnt_prime_riemann_sum   [11 links]
=== C3 Zeta5.theorem_1_1
  constants reached : 18322   (missing from env: 0)
  axioms (3) : [Classical.choice, Quot.sound, propext]
  vs Lean.collectAxioms : AGREE
  sorry leaves (0) : []
=== C3 Zeta5.theorem_2_1
  constants reached : 62071   (missing from env: 0)
  axioms (6) : [Classical.choice, Quot.sound, Zeta5.Axioms.hermite_pole_integral, Zeta5.Axioms.pnt_prime_riemann_sum, propext, sorryAx]
  vs Lean.collectAxioms : AGREE
  sorry leaves (1) : [Zeta5.RealBound.eq_6_14]
=== C3 Zeta5.outer_local_analysis                 constants reached : 32684   axioms (3) : [Classical.choice, Quot.sound, propext]   AGREE   sorry leaves (0)
=== C3 Zeta5.PrimeSum.eq_5_7_uniformity           constants reached : 36305   axioms (3) : [Classical.choice, Quot.sound, propext]   AGREE   sorry leaves (0)
=== C3 Zeta5.CrudeBound.crude_entry_bound         constants reached : 18976   axioms (3) : [Classical.choice, Quot.sound, propext]   AGREE   sorry leaves (0)
=== C3 Zeta5.Section3.entry_bounds_4_2_4_3        constants reached : 32248   axioms (3) : [Classical.choice, Quot.sound, propext]   AGREE   sorry leaves (0)
=== C3 Zeta5.HermiteBasis.det_coeffMatrix_unimodular constants reached : 23635 axioms (3) : [Classical.choice, Quot.sound, propext]   AGREE   sorry leaves (0)
=== C3 Zeta5.OuterBasis.outer_local_core          constants reached : 32564   axioms (3) : [Classical.choice, Quot.sound, propext]   AGREE   sorry leaves (0)
=== C3 Zeta5.Uniformity.eq_5_7_uniformity         constants reached : 36304   axioms (3) : [Classical.choice, Quot.sound, propext]   AGREE   sorry leaves (0)
=== C3 Zeta5.Lemma33.lemma_3_3                    constants reached : 17970   axioms (3) : [Classical.choice, Quot.sound, propext]   AGREE   sorry leaves (0)
=== C3 Zeta5.InnerEntries.entry_bounds            constants reached : 32247   axioms (3) : [Classical.choice, Quot.sound, propext]   AGREE   sorry leaves (0)
=== C3 Zeta5.RealBound.eq_6_14
  constants reached : 18043   (missing from env: 0)
  axioms (4) : [Classical.choice, Quot.sound, propext, sorryAx]
  vs Lean.collectAxioms : AGREE
  sorry leaves (1) : [Zeta5.RealBound.eq_6_14]
    chain to sorry leaf  : Zeta5.RealBound.eq_6_14   [1 links]
```

(The nine one-line entries are compressed from the three-line blocks in
`cert/c3/C3Walker.out`; nothing else is edited. The `theorem_2_1` chains are the
`zeta5_irrational` chains with the first link removed.)

What this output shows:

* **Both positive controls are found, with the correct chains.** A walker that misses a
  planted `sorry` or a planted axiom would fail here, before it ever reached the project.
* **The `value?` trap is real, and it was run rather than just described.** A walker built on
  `ConstantInfo.value?` gets `none` for every theorem, reaches only 1 472 constants, and
  reports **no `sorry`** for both `zeta5_irrational` and the planted control. Mine reaches 62 097.
* **The generous walk reaches exactly the axioms that `Lean.collectAxioms` reports**, on all
  16 cones. So no axiom is hidden behind any traversal subtlety.
* **The provenance chains are checkable by hand.** Hermite's axiom enters only through
  Proposition 2.2 (the positivity of Δ_K(ζ(5))). The PNT axiom enters only through
  Proposition 5.2 → (5.21) → (7.1) → the decay (2.7). The `sorry` enters only through
  Proposition 6.3 → (7.1) → (2.7).

### 2.2 `#print axioms` — Lean's own (same run, verbatim)

```
'Zeta5.zeta5_irrational' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 Zeta5.Axioms.hermite_pole_integral,
 Zeta5.Axioms.pnt_prime_riemann_sum]
'Zeta5.theorem_1_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta5.theorem_2_1' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 Zeta5.Axioms.hermite_pole_integral,
 Zeta5.Axioms.pnt_prime_riemann_sum]
'Zeta5.outer_local_analysis' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta5.PrimeSum.eq_5_7_uniformity' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta5.CrudeBound.crude_entry_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta5.Section3.entry_bounds_4_2_4_3' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta5.HermiteBasis.det_coeffMatrix_unimodular' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta5.RealBound.eq_6_14' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'C3ctl.uses_sorry_2' depends on axioms: [sorryAx]
'C3ctl.uses_axiom_2' depends on axioms: [C3ctl.planted_axiom]
```

**The four interface statements proved last are closed in the strict sense** that the ground
rules of this formalization require (README, 'Ground rules'): `outer_local_analysis`,
`PrimeSum.eq_5_7_uniformity`, `CrudeBound.crude_entry_bound` and
`Section3.entry_bounds_4_2_4_3` show **no `sorryAx`**, and neither does the shared lemma
`HermiteBasis.det_coeffMatrix_unimodular`. None of them was closed by pushing the `sorry` down
a level; that is the whole content of "no `sorryAx`".

### 2.3 Module-keyed environment scan — `cert/C3Scan.lean` (verbatim)

```
[1] constants in environment: 786344
    axiom declarations (17): [Classical.choice, Lean.ofReduceBool, Lean.ofReduceNat, Lean.trustCompiler, Quot.lcInv, Quot.sound, Zeta5.Axioms.hermite_pole_integral, Zeta5.Axioms.pnt_prime_riemann_sum, isScalarObj, lcAny, lcCast, lcErased, lcProof, lcUnreachable, lcVoid, propext, sorryAx]
[2] Zeta5 modules: 33; declarations defined in them: 3272
    axiom declarations (2): [Zeta5.Axioms.hermite_pole_integral, Zeta5.Axioms.pnt_prime_riemann_sum]
    declarations whose own type/value mentions sorryAx (1): [Zeta5.RealBound.eq_6_14]
    unsafe (0): []
    partial (5): [Zeta5.AppendixB.ChainOK._unsafe_rec, Zeta5.AppendixB.chainEnd._unsafe_rec, Zeta5.AppendixB.chainVal._unsafe_rec, Zeta5.Audit.visit._unsafe_rec, Zeta5.RealBound.chainB._unsafe_rec]
    opaque (1): [Zeta5.Audit.visit]
[3] cone of Zeta5.zeta5_irrational: 62097 constants
    sorry carriers in the cone (1): [Zeta5.RealBound.eq_6_14]
    ... of which OUTSIDE the Zeta5 modules (0): []
    Zeta5 sorry carriers NOT in the cone, i.e. orphans (0): []
[4] direct users in the cone of each project axiom:
    Zeta5.Axioms.hermite_pole_integral  (1): [Zeta5.Positivity.integral_wt_div_pole]
    Zeta5.Axioms.pnt_prime_riemann_sum  (1): [Zeta5.PrimeSum.tendsto_primeSum]
```

The scan is keyed on the **defining module**, not on the namespace, so internal names and
declarations parked in a foreign namespace are included. Of the 3 272 declarations the
project defines, **exactly two are axioms and exactly one mentions `sorryAx`**. The cone
contains **no** `sorry` carrier from Mathlib or core. `Lean.ofReduceBool` (`native_decide`),
`ofReduceNat` and `trustCompiler` exist in core Lean as always, but they are **not in the cone**
(the cone's axiom set is exactly the six above). The five `partial` constants are
compile-only `_unsafe_rec` auxiliaries of well-founded or `partial` definitions.
`cert/C3Attack.lean` confirms by a separate walk that **none of them, and no `unsafe` or
`partial` constant at all, is in the cone** (`unsafe or partial constants in the cone (0)`).
Each project axiom has exactly one direct user in the whole cone.

The per-module census (reached / defined) is identical to the one `STATUS.md` §4 reports,
number for number: AppendixB 281/311, Arithmetic 55/80, Asymptotics 6/6, Axioms 2/2, Basic
127/162, Counting 49/50, CrudeBound 64/83, Functional 92/132, HermiteBasis 14/18,
HermiteBasisCore 11/11, InnerEntries 176/180, InnerGeneral 52/53, InnerTate 78/87, Interface
27/30, Lemma33 142/154, Lemma42 40/66, LocalFunctional 86/115, Normalization 39/39,
OuterBasis 298/331, OuterLocal 98/107, OuterRange 144/172, Positivity 64/92, PrimeSum
133/156, RealBound 140/320, Section3 2/33, Section41 104/148, Skeleton 8/15, Tail 63/65,
Uniformity 166/209. `Audit`, `AppendixBCheck` and `Checks` are at 0 by design.

### 2.4 The project's own audit, from my clean-build log (verbatim)

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

It is the same answer name for name, and so are the twelve `depends on NO sorry` controls and
the negative control `Zeta5.RealBound.eq_6_14 rests on 1 sorry(s)` (the last `#sorry_tree`
lines of `Audit.lean`). I found no defect in `Audit.lean`. Compared with the pre-release
snapshot, its only change is those thirteen appended `#sorry_tree` lines.

### 2.5 Kernel replay — `leanchecker`

Lean 4.34 ships `leanchecker`, formerly lean4checker. It takes every declaration of a module
and replays it through the kernel, starting from the environment the module's imports give.
This catches "environment hacking", i.e. a declaration that reached the `.olean` without
passing the kernel. Command, from the repository root:
`lake env leanchecker --verbose Zeta5`. It checks every module whose name starts with
`Zeta5`, so all 33 were covered, in 25 min 25 s:

```
replaying Zeta5            replaying Zeta5.Checks          replaying Zeta5.Normalization
replaying Zeta5.Counting   replaying Zeta5.HermiteBasis    replaying Zeta5.Tail
replaying Zeta5.Positivity replaying Zeta5.InnerTate       replaying Zeta5.InnerGeneral
replaying Zeta5.Section41  replaying Zeta5.OuterLocal      replaying Zeta5.CrudeBound
replaying Zeta5.InnerEntries replaying Zeta5.AppendixB     replaying Zeta5.RealBound
replaying Zeta5.Lemma33    replaying Zeta5.Basic           replaying Zeta5.Section3
replaying Zeta5.Functional replaying Zeta5.Lemma42         replaying Zeta5.Audit
replaying Zeta5.Axioms     replaying Zeta5.Interface       replaying Zeta5.AppendixBCheck
replaying Zeta5.LocalFunctional replaying Zeta5.HermiteBasisCore replaying Zeta5.Asymptotics
replaying Zeta5.Uniformity replaying Zeta5.Skeleton        replaying Zeta5.OuterBasis
replaying Zeta5.Arithmetic replaying Zeta5.OuterRange
replaying Zeta5.PrimeSum
EXIT 0
```

(Rearranged into columns; the file `cert/c3/leanchecker.out` has one line per module.)
**No module failed the replay.**

---

## 3. The axioms: false, vacuous, too strong, or new?

**No axiom is new.** `Axioms.lean` is byte-identical to the pre-release snapshot. At the
kernel level (§5.1), both axioms have the same type hash as in the snapshot. No axiom was added
anywhere: none in the sources, none among the 1 050 declarations added since the snapshot, and
the environment scan finds the same two.

### 3.1 `hermite_pole_integral` — `∀ a > 0, ∫_0^∞ w(y)/(y²+a²) dy = a⁴ζ(5,a) − 1/(2a) − 1/4`

* **Route to `False`?** The formal statement could only be false where Lean's junk values
  apply. That happens if the integrand fails to be integrable (then the Bochner integral is
  `0`) or if the Hurwitz sum fails to be summable (then `tsum` is `0`). Both happen only for
  `a ≤ 0`: at `a = 0`, `w(y) → 1/π` makes the integrand `~ 1/(πy²)`. The hypothesis is
  `0 < a`, and I proved it refutable at `a = 0` and at `a = −1` (`hermite_guard_zero`,
  `hermite_guard_neg`). For `a > 0` the integrand is bounded near `0` and decays
  exponentially, and `∑(k+a)^{-5}` converges, so the formal equation is the classical one.
  The classical statement is true, so it cannot yield `False`.
* **True?** I recomputed it numerically with **my own code**. `w` comes from the Lean
  definition via the closed form `∑ℓ⁴qˡ = q(1+11q+11q²+q³)/(1−q)⁵`, and the Hurwitz zeta
  function comes from mpmath (40 digits). Eight values of `a` spanning five orders of
  magnitude:

  | `a` | LHS = RHS (28 digits shown) | LHS − RHS |
  |---|---|---|
  | 0.01 | 49.75000000987538672252948526 | −7.4e−40 |
  | 0.2 | 2.250680833198177347423515722 | 0.0 |
  | 0.7 | 0.483399773201377749446428785 | −1.7e−41 |
  | 1 | 0.2869277551433699263313654865 (= ζ(5) − 3/4) | 0.0 |
  | 1.5 | 0.1495162394792844802953376975 | 5.7e−42 |
  | 4 | 0.02500737431586986510939992395 | −2.2e−42 |
  | 25 | 0.0006659220390451200740660177086 | 6.1e−42 |
  | 1000 | 0.0000004166663750004999986250054166 | 8.7e−41 |

  As a further check, `∫_0^∞ w = 5/12` to 40 digits, which matches the large-`a` asymptotics
  of the right-hand side.
* **Vacuous?** No. `C3att.hermite_at_one : ∫_0^∞ w(y)/(y²+1) dy = zeta5 − 3/4` is derived
  from it and depends on `[propext, Classical.choice, Quot.sound, hermite_pole_integral]`.
* **Strong enough to give the theorem trivially?** No. It has one direct user in the whole
  cone (`Positivity.integral_wt_div_pole`), reached by a 12-link chain through
  Proposition 2.2. The step that actually deduces irrationality, `theorem_1_1`, uses no
  project axiom and no `sorry` (§2.2).
* **Caveat, as its docstring says.** It is Hermite's formula (DLMF 25.11.29) after the four
  integrations by parts of p. 5, which are not formalised. So it is slightly more than a
  verbatim citation.

### 3.2 `pnt_prime_riemann_sum` — `X⁻¹∑_{⌊aX⌋<p≤⌊bX⌋} φ(p/X) log p → ∫_a^b φ`

The hypotheses are `0 ≤ a < b`, `φ` bounded on `[a,b]`, and `φ` continuous at every point of
`[a,b]` outside a finite set.

* **Route to `False`?** Lean's junk values would make the statement false only if `∫_a^b φ`
  were a junk `0`. That cannot happen. `φ` is continuous on the measurable set
  `[a,b] ∖ D` and `D` is finite, so `φ` is a.e.-strongly measurable on `(a,b]`, and it is
  bounded there, so it is integrable. The Bochner integral is therefore the Riemann integral.
  The sum evaluates `φ` only at points `p/X ∈ (a, b]`, since `⌊aX⌋ + 1 > aX` and
  `⌊bX⌋ ≤ bX`. So nothing about `φ` off `[a,b]` can be exploited. A single exceptional point
  `d ∈ D` is hit by at most one prime for each `X`, which contributes at most `log(bX)/X → 0`.
  The degenerate instances are blocked by refutable hypotheses (`pnt_guard_empty` for
  `a = b`, `pnt_guard_neg` for `a < 0`). An unbounded `φ` such as `1/y` on `[0,1]` cannot
  meet the boundedness hypothesis (`unbounded_blocked`, proved sorry-free). With every junk
  value excluded, the formal statement is the classical theorem: for Riemann-integrable `φ`,
  PNT plus Abel summation give it. It is true, so it cannot yield `False`.
* **True?** I tested four test functions, with a numpy sieve to 3·10⁷:

  | `φ` on `[a,b]` | X = 10⁵ | 10⁶ | 10⁷ | `∫_a^b φ` |
  |---|---|---|---|---|
  | `y²` on `[1/2, 3/2]` | 1.082574 | 1.083031 | 1.082999 | 1.083333 |
  | `cos 3y` on `[0, 2]` | −0.094050 | −0.093309 | −0.093194 | −0.093138 |
  | `1_{y<0.7} − 2·1_{y>1.3}` on `[0.2, 2]` (two jumps) | −0.901171 | −0.900281 | −0.899858 | −0.900000 |
  | `frac(5y)` on `[0, 1]` (four jumps) | 0.499787 | 0.499404 | 0.499645 | 0.500000 |

  All four converge at the expected (slow, Chebyshev-type) rate.
* **Vacuous?** No. `C3att.pnt_dyadic : (θ(2X) − θ(X))/X → 1` (floors included) is derived
  from it with `φ ≡ 1` on `[1,2]`. It depends on
  `[propext, Classical.choice, Quot.sound, pnt_prime_riemann_sum]`.
* **Strong enough to give the theorem trivially?** No. It has one direct user in the cone
  (`PrimeSum.tendsto_primeSum`), 11 links from the root, and `theorem_1_1` does not use it.
* **Caveat, as its docstring says.** It is the **partial-summation corollary** of the PNT, not
  `θ(x) ~ x` itself: the Abel-summation step and the Darboux sandwich are absorbed into it.
  Every hypothesis it needs about Fauzan's functions is discharged inside `PrimeSum.lean`.

### 3.3 Can the two axioms interact?

They share no constant and no hypothesis. One is an identity between real integrals and
sums; the other is a limit of prime sums. Each is a true classical statement, so their
conjunction is consistent with Mathlib (relative to the consistency of Mathlib itself).

---

## 4. Is the statement still "ζ(5) is irrational"? — `cert/C3Semantics.lean`

These checks are made on `Expr`s, not on pretty-printed text (verbatim):

```
kind: theorem; universe params: []
type as Expr == Irrational Zeta5.zeta5 : true
raw type: Irrational Zeta5.zeta5
`Irrational` is defined in module Mathlib.NumberTheory.Real.Irrational
`Zeta5.zeta5` is defined in module Zeta5.Basic
Zeta5.zeta5 is a def; raw value: tsum.{0, 0} Real Nat Real.instAddCommMonoid (…) (fun (v : Nat) =>
  HDiv.hDiv … (OfNat.ofNat Real 1 …) (HPow.hPow Real Nat Real … (HAdd.hAdd … (Nat.cast Real … v)
  (OfNat.ofNat Real 1 …)) (OfNat.ofNat Nat 5 …))) (SummationFilter.unconditional.{0} Nat)
constants in its value and their modules:   [26 constants, every one from Init.* or Mathlib.*]
def Irrational : ℝ → Prop := fun x => x ∉ Set.range Rat.cast
'C3sem.zeta5_eq_riemannZeta' depends on axioms: [propext, Classical.choice, Quot.sound]
'C3sem.one_le_zeta5' depends on axioms: [propext, Classical.choice, Quot.sound]
'C3sem.riemannZeta_five_not_rational' depends on axioms: [propext, sorryAx, Classical.choice,
  Quot.sound, Zeta5.Axioms.hermite_pole_integral, Zeta5.Axioms.pnt_prime_riemann_sum]
```

* **No hypotheses and no universe parameters.** The type is *syntactically*
  `.app (.const Irrational []) (.const Zeta5.zeta5 [])`.
* **`Irrational` is Mathlib's** (defined in `Mathlib.NumberTheory.Real.Irrational`, and it
  unfolds by `Iff.rfl` to `x ∉ Set.range ((↑) : ℚ → ℝ)`), not a local redefinition.
* **`zeta5` is the actual sum `∑_{v≥0} 1/(v+1)⁵`.** Every constant in its definition comes from
  `Init` or Mathlib. The sum is Mathlib's `tsum` with the **unconditional** summation filter,
  which is the ordinary sum of a summable series.
* **`zeta5 = riemannZeta 5`, proved sorry-free.** The proof uses Mathlib's
  `zeta_nat_eq_tsum_of_gt_one` (a sum over `n ≥ 0` in which the `n = 0` term is `1/0⁵ = 0`),
  an index shift `Summable.tsum_eq_zero_add`, and `Complex.ofReal_tsum`.
  `one_le_zeta5 : 1 ≤ zeta5` is also proved, sorry-free, which rules out the junk value `0`.
* **Restated as number theory:**
  `riemannZeta_five_not_rational : ∀ q : ℚ, (q : ℂ) ≠ riemannZeta 5` follows from the theorem.
  It carries the theorem's assumptions exactly, as it must.

---

## 5. Were any statements changed?

### 5.1 Kernel-level comparison with a pre-release snapshot

The snapshot is a copy of the Lean sources taken before the four interface statements of
`STATUS.md` §3 were proved, when they (and `eq_6_14`) were still `sorry`s. It is **not
published**, so this comparison cannot be re-run from the repository; the method and its
output are recorded here. I extracted the snapshot into a scratch directory, never over the
project, and compiled it with `lean` directly into a separate library directory, using
Mathlib's compiled `.olean`s **read-only**. All 22 snapshot modules built, with exactly the
five `sorry` warnings of that state (RealBound:856, OuterRange:1363, Section3:1068,
PrimeSum:1183, CrudeBound:569). That is a control: the snapshot is the expected starting
state.

`cert/c3/DumpEnv.lean` then dumped, for **every** constant defined in a `Zeta5.*` module of
each environment, its kind, module and universe parameters, the structural hash of its
**type**, and, for definitions, opaques, inductives and recursors, the hash of its **value**.
Theorems contribute only their type, since proofs are expected to change. A short comparison
script then gave, verbatim (abridged only where marked):

```
snapshot decls 2185, current decls 3228, common 2178, removed 7, added 1050
TYPE/kind/univ changed (9):   [all nine are auto-generated `_simp_1_k` / `_proof_1_k`
                               auxiliaries of Zeta5.PrimeSum.block2_le and
                               Zeta5.Section3.rowPoly_natDegree_lt — see below]
VALUE changed (defs/opaque/inductive/rec) (0):
moved module (116): {('Zeta5.Section3', 'Zeta5.LocalFunctional'): 115, ('Zeta5.Section3', 'Zeta5.InnerEntries'): 1}
removed (7):                  [likewise, all `_proof_1_k` / `_simp_1_k` of the same two theorems]
added, kinds: {'thm': 982, 'def': 65, 'induct': 1, 'ctor': 1, 'rec': 1}
added axioms: []
  Zeta5.zeta5_irrational                     type-hash snap              939628043 cur              939628043  SAME
  Zeta5.outer_local_analysis                 type-hash snap             3921940189 cur             3921940189  SAME
  Zeta5.PrimeSum.eq_5_7_uniformity           type-hash snap             1002121070 cur             1002121070  SAME
  Zeta5.CrudeBound.crude_entry_bound         type-hash snap             2199357807 cur             2199357807  SAME
  Zeta5.Section3.entry_bounds_4_2_4_3        type-hash snap             2879116297 cur             2879116297  SAME
  Zeta5.RealBound.eq_6_14                    type-hash snap             3516290794 cur             3516290794  SAME
  Zeta5.zeta5                                type-hash snap             4024430794 cur             4024430794  SAME
  Zeta5.wt                                   type-hash snap             3468892319 cur             3468892319  SAME
  Zeta5.Axioms.hermite_pole_integral         type-hash snap             3169839243 cur             3169839243  SAME
  Zeta5.Axioms.pnt_prime_riemann_sum         type-hash snap              418062367 cur              418062367  SAME
```

The only differences are **renumbered auxiliary lemmas inside two proofs**. I checked this
directly: for `block2_le` and for `rowPoly_natDegree_lt`, the multiset of
(type-hash, universe-parameters) over all their `_proof_1_*`/`_simp_1_*` auxiliaries is
**identical** before and after (10 = 10 and 9 = 9). Only the numbering shifted, because
elaboration of those two proofs now sees different imports. Both parent theorems have
unchanged types. The one declaration that moved to `InnerEntries` is
`Zeta5.InnerAlloc.rowPoly.eq_1`, an equation lemma that Lean generates the first time it is
needed, with its type unchanged. The 115 that moved to `LocalFunctional` are §§A–E of the old
`Section3.lean`. They were moved verbatim: I confirmed that the 739 moved lines are a
byte-for-byte substring of `LocalFunctional.lean`, in the same `import Zeta5.Arithmetic /
namespace Zeta5 / open Polynomial Finset / noncomputable section` context, and the kernel
comparison shows their types and values unchanged.

**Consequence: of the 2 185 declarations of the snapshot, 2 178 are present
with identical types (and, for definitions, identical bodies), and the other 7 are
renumbered auxiliary lemmas inside two proofs. No statement changed and no definition
changed its body.** That includes every definition the interface
statements mention (`OuterHyp`, `outerWeight`, `rOut`, `gammaOut`, `Gf`, `vGAtLeast`, `Gam`,
`NR`, `vS`, `InnerAllocFamily`, `AppendixB.Tout`, `InnerAlloc`, `Delta`, `evalZeta5`, `lam`,
`M0`, `Irho`, `zeta5`, …). This settles the ground rule that no statement is changed to make
it provable (README, 'Ground rules') more strongly than any text diff can, because it also
rules out a change of meaning through a definition, an instance, or a notation.

### 5.2 Text comparison of the statements with the snapshot

Together with the snapshot, the statement blocks of the six declarations below were recorded
with SHA-256 checksums. Each statement was re-extracted from the current sources and compared
with the recorded one (like the snapshot, the recorded blocks and the script are not
published):

```
Zeta5.outer_local_analysis        OuterRange.lean:1371  statement text identical: True   baseline sha ok: True   full block identical: False
Zeta5.PrimeSum.eq_5_7_uniformity  PrimeSum.lean:1184    statement text identical: True   baseline sha ok: True   full block identical: False
Zeta5.CrudeBound.crude_entry_bound CrudeBound.lean:562  statement text identical: True   baseline sha ok: True   full block identical: False
Zeta5.Section3.entry_bounds_4_2_4_3 Section3.lean:344   statement text identical: True   baseline sha ok: True   full block identical: False
Zeta5.RealBound.eq_6_14           RealBound.lean:856    statement text identical: True   baseline sha ok: True   full block identical: True
Zeta5.zeta5_irrational            Interface.lean:459    statement text identical: True   baseline sha ok: True   full block identical: True
```

(`baseline sha ok` means the recorded block matches its recorded checksum.) All six
statements are **byte-identical** to the recorded ones. For the four statements proved since
the snapshot, the block differs only after `:=`, where `by sorry` became a one-line
application of the new result:

| statement | new proof term |
|---|---|
| `outer_local_analysis` | `OuterBasis.outer_local_core n p ⟨hp.ge7, hp.upper, hp.sq, hp.twoN, hp.fiveN⟩ (outerDim n p) rfl (outerWeight n p) (fun _ => rfl) (outerRows_card hp)` |
| `PrimeSum.eq_5_7_uniformity` | `Uniformity.eq_5_7_uniformity M hM Alloc` |
| `CrudeBound.crude_entry_bound` | `Lemma33.entry_bound n (qb i) (qb j) _ (pullNum_natDegree_le n i j hi hj) (pullNum_int n i j) (max_two_K_le_five_K n hn)` |
| `Section3.entry_bounds_4_2_4_3` | `InnerEntries.entry_bounds n M p _hp A` |

The eq_6_14 block and the zeta5_irrational block (whose proof is
`theorem_1_1 stdAlloc (theorem_2_1 stdAlloc)`) are byte-identical including their proofs. The
line-by-line diff of the pre-existing files shows the same thing. `CrudeBound`, `OuterRange`,
`PrimeSum` and `Section3` changed only in imports, comments and docstrings, the proof term
replacing `sorry`, one appended `#print axioms`, and (in `Section3`) the verbatim move.
`OuterLocal` changed by one import line. `Interface` changed only in comments. `Audit` changed
only in the appended `#sorry_tree` lines. The root `Zeta5.lean` gained nine imports.
`Axioms.lean`, `Basic.lean`, `RealBound.lean` and the other 13 pre-existing files are
byte-identical.

**No interface statement's hypotheses are unsatisfiable, so none of them is closed
vacuously.** `OuterHyp n p` holds, for example, at `n = 5` (K = 200) for the 28 primes 67, …, 199.
`IsInnerPrime n 40 p` holds at `n = 8000` (K = 320 000), for example at `p = 8009`. (The final
theorem has no hypotheses, so vacuity could not have affected soundness anyway.)

### 5.3 Five newly proved statements against the PDF page images

I read these against the rendered pages, not the garbled text extraction.

1. **`Lemma33.lemma_3_3` = Lemma 3.3, p. 8.** The page reads: *A* integer-valued on ℤ_p,
   deg *A* ≤ *d*, *g*(*x*) = (K!)²*A*(*x*)/∏_{−K≤r≤K, r≠0}(*x*−*r*), and then
   v_p^G(τ_X(g)) ≥ −6⌊log_p max(2K, d+1)⌋ − v_p(24). The Lean statement is
   `vGAtLeast p (tauExtOf X (poles K) (C ((K!)²) * A)) (-6 * Nat.log p (max (2K) (d+1)) - padicValNat p 24)`.
   Here `poles K = [−K, K] ∖ {0}`, `tauExtOf` is polynomial division plus simple partial
   fractions followed by `τ^ext_X` (p. 7: `τ(f) + ∑c_ν(H⁽⁵⁾_{d(r_ν)} − X)`), `Nat.log` is
   ⌊log_p⌋, and `vGAtLeast` is v_p^G ≥ (Basic.lean:496). The hypothesis "integer-valued on
   ℤ_p" is stated as `∀ z : ℤ, |A(z)|_p ≤ 1`, which is equivalent by density of ℤ in ℤ_p.
   The Lean holds for every prime *p*, *K* and *d*. **Faithful, not weakened.**
2. **`InnerEntries.raabe_tau` = (3.7) for polynomials, p. 7.** The page says: "For
   polynomials, (3.7) follows from Bernoulli multiplication". For a polynomial *g*, (3.7)
   reads τ(g) = p⁻⁴∑_{a<p} τ(g(a+px)). The Lean is `m⁴ τ(P) = ∑_{a<m} τ(P(a + m z))` for
   every `m ≥ 1`. **Faithful, and more general** (any *m*, not only *m* = *p*). What is *not*
   formalised is (3.7) for rational functions with far poles, i.e. Lemma 3.2 proper; see §7.
3. **`OuterBasis.L0_eq_zero` and `rank_L0` = the rank argument of (4.10), pp. 11–12.** The
   page says: "the polynomial quotient of Wt^{i+j}/D_tail has degree at most i+j+6N−K. Hence
   L_ij = 0 if i+j < K−6N+2p−3. Its first h−r_p rows and columns vanish", with
   r_p = max(0, K+4N−2p+2). The Lean `L0_eq_zero` has hypothesis
   `i + j + 6N + 3 < K + 2p`, which is **literally i + j < K − 6N + 2p − 3**. `rank_L0` then
   makes the first `d = 2p − 5N − 2` columns vanish. That is at least the page's h − r_p =
   2p − 7N − 2, so the bound `rank ≤ h − d ≤ r_p` is **slightly sharper than printed**. The
   transport to the basis (4.11) is `L = U L₀ Uᵀ` (`rank_Lq`). **Faithful.**
4. **`HermiteBasis.det_coeffMatrix_unimodular` = the unimodularity of (4.5), p. 10, and of
   (4.11), p. 12.** The page says: "The factors t+c² are pairwise coprime modulo p … the
   polynomials in (4.5) give triangular local bases whose diagonal entries are units. They
   therefore form a ℤ_p-unimodular basis", and on p. 12: "these form a unimodular basis". The
   Lean statement: if integer polynomials `g_k` reduce mod *p* to the Hermite-interpolation
   basis `∏_{c≠a}(t+u_c)^{m_c}(t+u_a)^i` with pairwise distinct nodes `u`, then their
   coefficient matrix `U` has `det U ≠ 0` and `v_p(det U) = 0`. For (4.5) the nodes are
   `u_c = c²`, `0 ≤ c ≤ (p−1)/2`, which are distinct mod *p*. **Same conclusion, a different
   (cleaner) proof**, as `STATUS.md` deviation 16 says.
5. **`Uniformity.eq_5_7_uniformity` (literally the type of `PrimeSum.eq_5_7_uniformity`) =
   (5.7) and the two §5.2 displays, pp. 14–15.** For fixed *M* there is one constant *C* such
   that the following three bounds hold.
   * For every inner prime (`IsInnerPrime`: *p* prime, *M* ≥ 40, K ≥ 200M², K/M < p ≤ K/3,
     which is (4.1)): |γ_p^in − pΓ(K/p)| ≤ C.
   * For every inner prime: |v_p(S_K) − p𝒩(K/p)| ≤ C.
   * For every prime with K < 3p ≤ 6h: |−(v_p(S_K) + γ_p^out) − K·T_out(p/K)| ≤ C.

   I re-read each definition against the page. `Gam` is (5.4), including
   `s(2T−q−5) + (s−n₊)₊`. `NR` is (5.5), `2λx⌊x⌋ − 12λx⌊αx⌋ − 2J(λx)` with
   `J(u) = mu − m(m+1)/4`, `m = ⌊2u⌋`. `R0` is (5.8), all three branches. `dRank` is (5.9).
   `Tout = R0 − d − 2λ⌊1/y⌋ + ∑_{j=1}^5(2λ−jy)₊`, which is the sum of the two p. 15 displays
   (`−γ_p^out = K(R₀ − d) + O(1)` and `−v_p(S_K) = K(−2λ⌊1/y⌋ + ∑(2λ−jy)₊) + O(1)`).
   **Faithful.** The bundling into one shared *C* is at least as strong as the three separate
   O(1) claims. The proof supplies `C = 400M²`.

**No weakened statement was found.**

---

## 6. The one remaining `sorry`, tested against exact data

`RealBound.eq_6_14` is (6.14), p. 20, stated for **every** `n > 0` (K = 40n) under
Δ_K(ζ(5)) > 0. Because `sorryAx` proves anything, a false instance at small *n* would make the
whole development hollow. So I tested it. `cert/c3/eq_6_14_control.py` parses `Irho`, `M0`
and `lam` **from the Lean source** of `RealBound.lean`, not from the paper. It takes
log Δ_K(ζ(5)) from the exact computation in the referee audit of the preprint. There Δ_K is
computed exactly in ℚ[X] and evaluated at ζ(5) with thousands of digits (`docs/zeta5-audit.pdf`,
"The direct computations"). The values are recorded in `cert/c3/delta_K_values.json`.

```
Irho (from the Lean definition) = -2.126593445147050403253601   audit (A.2): -2.1265934451470504033
lam*M0 - Irho = -4.0200315548529495967   audit: -4.0200315549
n=1 K=  40: Delta_K(zeta5)>0: True   log Delta =    -1836.876   RHS(6.14) =     6039.399   holds: True   slack = 7876.3
n=2 K=  80: Delta_K(zeta5)>0: True   log Delta =    -5129.992   RHS(6.14) =    11404.856   holds: True   slack = 16534.8
n=3 K= 120: Delta_K(zeta5)>0: True   log Delta =    -8259.556   RHS(6.14) =    17263.997   holds: True   slack = 25523.6
```

(6.14) **holds** at every *K* for which exact data exist, and the Lean constant `Irho` agrees
with the referee audit's independent (A.2) value to 25 digits. The slack is large because the
positive `h log K` terms dominate at small *K*. So this is a **consistency check, not evidence
for the asymptotic regime** that (6.16) actually uses. The referee audit of the preprint
re-derived (6.14)'s bookkeeping and certified (6.2) numerically (sup(2U^ρ − V) = −6.6498939 ≤ M₀ =
−6.645, slack 4.9·10⁻³), but (6.14) remains **unproved in Lean**. It is Fauzan's own claim and
the analytic heart of §6.

---

## 7. Defects and caveats found

None of these affects the assumption list or the statement.

1. **`STATUS.md` §1 overstated slightly** (corrected since, with the wording suggested below).
   It said "Every arithmetic part of the paper (§§2–5 and Appendix B) is now
   machine-checked". What is machine-checked is **every arithmetic
   statement the proof of Theorem 1.1 uses**. Several of the paper's own intermediate
   statements are *bypassed* rather than checked:
   * Lemma 3.2 / (3.7) for rational functions with far poles, with (3.5) and (3.6)
     (deviation 7);
   * the two-scale part of the proof of Lemma 3.3, with (3.8) and (3.9) (deviation 5);
   * Lemma 3.1 in its Tate-algebra form (deviation 2).

   Lemma 3.1 and Lemma 4.2 are proved but not in the cone. The deviations list says all this;
   the headline sentence should too. Suggested wording: *"every arithmetic statement that the
   proof of Theorem 1.1 uses (§§2–5, Appendix B) is machine-checked; three of the paper's own
   proofs (Lemma 3.2, the polynomial part of Lemma 3.3, the unimodularity arguments) are
   replaced by different arguments."*
2. **A stray scratch file** sat at the package root. It was harmless (not built, not
   imported, one `example`), but it should be deleted so that nobody mistakes it for part of
   the library. It has since been removed.
3. **Strict closure.** Confirmed, with no exception: each of the four interface statements
   proved last is closed with no `sorryAx` below it, not decomposed.
4. **Future changes.** The `leanchecker` replay should be re-run, and a kernel-level
   comparison against this state made (with `cert/c3/DumpEnv.lean`), whenever a future change
   touches existing files.

---

## 8. Verdict

> There is a Lean 4 formalisation, machine-checked against Mathlib v4.34.0 from a clean
> rebuild of all 32 of its modules, of a single theorem `Zeta5.zeta5_irrational : Irrational
> Zeta5.zeta5`. It has no hypotheses. `Irrational` is Mathlib's, and `Zeta5.zeta5` is the real
> number ∑_{n≥1} n⁻⁵, proved within the same development, with no unproved input, to equal
> Mathlib's `riemannZeta 5`. Five independent methods agree on what its proof rests on:
> Lean's own `collectAxioms`, the project's audit metaprogram, a dependency walker written
> from scratch for this certification (validated on planted controls), a scan of all 3 272
> declarations keyed on their defining module, and a full kernel replay of every module by
> Lean's `leanchecker`. The proof rests on Lean's three standard axioms, on **two** explicit
> external axioms, and on **one** named `sorry`. The first axiom is Hermite's integral formula
> for the Hurwitz zeta function at s = 5, carried through four unformalised integrations by
> parts. The second is the prime number theorem in partial-summation ("prime Riemann sum")
> form. Both are true classical statements: they were re-verified numerically here, to 40
> digits and at four test functions respectively. Neither can be instantiated at a
> degenerate point, and each is used at exactly one place in a 62 097-constant dependency
> cone. The `sorry` is A. Fauzan's inequality (6.14), the logarithmic-energy upper bound for
> Δ_K(ζ(5)) in §6, together with the potential theory and Appendix A behind it. It is the
> only unproved step of the paper's own argument that the formal proof uses. It is consistent
> with exact values of Δ_K(ζ(5)) at K = 40, 80, 120, but it is not proved. Everything else —
> §§2–5 of the paper and Appendix B, including Lemma 3.3, the unimodular bases and entry
> bounds of Propositions 4.1 and 4.3, the uniformity (5.7), and Proposition 5.2 modulo the
> prime number theorem — is proved with no `sorry`. Some of the paper's intermediate proofs
> are replaced by different arguments. A kernel-level comparison with a pre-release snapshot
> shows that no previously existing statement or definition changed. The correct way to report the
> result is: **"ζ(5) is irrational, machine-checked conditional on one explicitly named
> unproved statement of the paper — (6.14) — plus Hermite's integral formula and the prime
> number theorem in partial-summation form."** It is never correct to say "modulo standard
> facts".

---

## Scripts (none is part of `lake build`)

Run from the repository root, after `lake build`:

```
lake env lean cert/C3Walker.lean       # own BFS walker, provenance chains, planted controls, value? trap, 16 cones (4-8 min)
lake env lean cert/C3Scan.lean         # all axioms; module-keyed sorry/unsafe/partial/opaque scan; orphans; axiom users; census (3-10 min)
lake env lean cert/C3Semantics.lean    # statement as Expr; modules of Irrational/zeta5; zeta5 = riemannZeta 5
lake env lean cert/C3Attack.lean       # guards refutable; non-vacuity of both axioms; no unsafe/partial in the cone
lake env leanchecker --verbose Zeta5   # kernel replay of every Zeta5 module (~25 min)
python3 cert/c3/axioms_numeric.py      # Hermite at 8 values of a (40 digits); PNT at 4 test functions (needs mpmath, numpy)
python3 cert/c3/eq_6_14_control.py               # Irho from the Lean source; (6.14) at K = 40, 80, 120
lake env lean --run cert/c3/DumpEnv.lean <out.tsv> Zeta5   # per-declaration type/value hashes, for comparing two builds
```

Outputs: `cert/c3/*.out`, `cert/c3/clean-build.log`, `cert/c3/leanchecker.out`. The snapshot,
the statement records and the comparison script used in §5 are not published.
