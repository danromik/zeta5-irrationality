# Development status and deviations from the paper

> **Branch `axioms`, 2026-09-24: the two axioms are reduced to one textbook statement.**
> `Zeta5.Axioms.hermite_pole_integral` is now the theorem `Zeta5.Hermite.pole_integral`
> (`Zeta5/Hermite.lean`), proved with **no axiom**; `Zeta5.Axioms.pnt_prime_riemann_sum` is
> now the theorem `Zeta5.PNT.prime_riemann_sum` (`Zeta5/PNT.lean`), proved from the single
> new axiom `Zeta5.Axioms.chebyshev_theta_asymptotic` (the prime number theorem as
> `θ(x)/x → 1`, with Mathlib's `Chebyshev.theta`). Both theorems have exactly the types of the
> axioms they replace, and no other statement changed. `zeta5_irrational` rests on the three
> standard Lean axioms and that one axiom (§1, §2 (B)). **This state is pending
> re-certification**: §4 and §8 describe the certification of the previous state (code commit
> `808618b`), and their counts refer to it.
>
> **Branch `eq614`, 2026-09-24: (6.14) is proved, and the project contains no `sorry`.**
> `Zeta5.RealBound.eq_6_14` and `prop_6_3` (same names and types as before) are proved in
> `Zeta5/Sec6/Final.lean` through the §6 blueprint (commit `4dea216`), whose 19 leaf
> statements in `Zeta5/Sec6/*.lean` are all proved, statements unchanged. `lake build`
> reports no `declaration uses 'sorry'` warning, and the assumption report lists **no
> `sorry`**: only the three standard Lean axioms and the two axioms that `Zeta5/Axioms.lean`
> then declared.
> The §6 route and its deviations from the paper are in §2 (C) and §6 (deviations 19–23)
> below. This state (code commit `808618b`) was re-certified on 2026-09-24
> (`CERTIFICATION.md`, scripts and outputs in `cert/final/`). The numbers in §4 and §8 come
> from that certification, except where they are marked as from the 2026-09-23 one.

This file records, for a reader who wants to check the formalization against A. Fauzan's
preprint "ζ(5) IS IRRATIONAL" (17 September 2026): what the Lean development proves, what it
assumes, where the formal proof takes a different route from the paper, and what remains to
be done. The independent certification of the assumption list is in
[`CERTIFICATION.md`](CERTIFICATION.md); a typeset summary is in `lean-status.pdf`.

**State:** 2026-09-24 · **Toolchain:** Lean 4.34.0, Mathlib v4.34.0 · 71 modules under
`Zeta5/` (37 of them in `Zeta5/Sec6/`) plus the root file, 29 699 lines of Lean.

**Build.** A clean `lake build` (`.lake/build` deleted, Mathlib from the cache) takes about
8 minutes on a 12-core machine and ends with

```
Build completed successfully (8996 jobs).
```

(8994 jobs before `Hermite.lean` and `PNT.lean` were added.) The four clean builds of
2026-09-24, made before the axiom reduction, took 7 min 26 s to 8 min 1 s. The `Zeta5/Sec6/Num/`
modules need up to about 8 GB of memory. The build has zero errors and **no**
`declaration uses 'sorry'` warning. There are 17 warnings, all of them style lints:
* 14 "automatically included section variable(s) unused" (in `InnerTate`, `InnerGeneral`
  and `InnerEntries`);
* 3 "Variable name … is not explicitly referenced": `ha` in
  `InnerGeneral.comp_X_sub_C_phi_near`, and `hC0` in `PrimeSum.block2_le` and `block3_le`.
  The axiom reduction added no warning (the incremental build after it reports the same 17).

Silencing them would change the signatures of those theorems, so they are left as they are.
None affects soundness. The first `eq614` builds had 267 deprecation and style warnings.
Commit `808618b` removed the others and changed only proofs.

---

## 1. The shape of the thing

There is **one theorem**:

```lean
theorem Zeta5.zeta5_irrational : Irrational zeta5
```

with `zeta5 : ℝ := ∑' v : ℕ, 1 / ((v : ℝ) + 1) ^ 5`, i.e. `ζ(5)`. It is Theorem 1.1 of the
paper, and the whole of the paper's route to it — Theorem 2.1, Propositions 2.2, 4.1, 4.3,
5.1, 5.2, 6.3, Lemma 3.3, and (2.7), (2.9), (3.1), (3.11), (3.12), (4.4), (4.10)–(4.14),
(5.1)–(5.3), (5.7), (5.16)–(5.21), (7.1), (7.2) — is wired up in Lean below it, with no
statement short-circuited. (Lemmas 3.1 and 4.2 are proved too, but the proofs of
Propositions 4.1 and 4.3 go around them; see §4 and deviation 7.)

**It rests on one external axiom, the prime number theorem `θ(x) ~ x`, and on nothing else:
no `sorry`.** The last `sorry`,
`Zeta5.RealBound.eq_6_14` — the paper's (6.14), the logarithmic-energy upper bound for
`Δ_K(ζ(5))` in §6 — was proved on 2026-09-24 (§2 (C)). **Every statement that the proof of
Theorem 1.1 uses is machine-checked**, conditional only on the prime number theorem in
Chebyshev's form `θ(x) ~ x` (for Proposition 5.2). The partial summation that turns it into
the prime Riemann sums of Proposition 5.2 is proved (`PNT.prime_riemann_sum`), and so is the
pole integral of p. 5 that Proposition 2.2 (and, through (6.10), §6) uses
(`Hermite.pole_integral`); until 2026-09-24 those two were axioms. At three places the formal proof takes a different route from the paper's
own proof — Lemma 3.2 (the distribution formula, with the far poles), the polynomial part of
the proof of Lemma 3.3, and the unimodularity arguments — so the paper's proofs of those three
steps are bypassed rather than checked; §6 of the paper is also proved partly by a different
route (the kernel regularisation, the smoothing error, and (6.2) on the formalisation's own
partition instead of Table 2) (see the deviations list, §6).

Verbatim build output (`Zeta5/Audit.lean`, recomputed from the Lean environment on every
build):

```
ASSUMPTION REPORT for Zeta5.zeta5_irrational

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
...
every sorry of the Zeta5 namespace is used by Zeta5.zeta5_irrational.
'Zeta5.zeta5_irrational' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Zeta5.Axioms.chebyshev_theta_asymptotic]
'Zeta5.theorem_1_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta5.Hermite.pole_integral' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta5.PNT.prime_riemann_sum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Zeta5.Axioms.chebyshev_theta_asymptotic]
```

There is no `sorryAx`. The walker and Lean's `collectAxioms` agree on that. The independent
checks of §4 agreed on the previous state (commit `808618b`, with the two former axioms in
place of the one above); they have not yet been re-run on the reduced state.

### The ground rules these lists follow

The ground rules of this formalization (README, 'Ground rules'):

* **Anything internal to Fauzan's argument is proved or a `sorry`, never an axiom.** The one
  axiom mentions no object of the paper at all, only Mathlib's `Chebyshev.theta`. (Of the two
  former axioms, the only object of the paper that either mentioned was the explicit weight
  `w` of (2.10).)
* **A finite explicit computation is never an axiom.** Appendix B's exact rational integrals
  (143 pieces, 17 Table-3 rows, 11 Table-4 rows) and Appendix A's Table-1 evaluations and
  Table-2 tiling are *proved*, by `norm_num`/`decide`/explicit rational arithmetic.
* **No statement is changed to make it provable.** The statements of the interface theorems
  were fixed before the proofs were written. The certification of 2026-09-23 compared them,
  and every definition they mention, with a snapshot taken before the last proofs were
  filled in. It found no change. The certification of 2026-09-24 compared all 3 272
  declarations of the 2026-09-23 state (`main`, `9ce1320`) with `808618b` at the level of
  kernel terms. No statement or definition changed (`CERTIFICATION.md` §5). One interface statement was reformulated earlier, before
  its proof was written, because its first formulation was false for the paper's own data;
  the new form is the paper's (4.10) as printed (deviation 3).

---

## 2. The assumption list

### (B) The one external axiom — `Zeta5/Axioms.lean`, the only `axiom` in the project

Its docstring has the precise statement, a literature citation, and why Mathlib lacks it.

| axiom | statement | citation | why not Mathlib |
|---|---|---|---|
| `Zeta5.Axioms.chebyshev_theta_asymptotic` | `Tendsto (fun x : ℝ => Chebyshev.theta x / x) atTop (nhds 1)`, i.e. `θ(x)/x → 1`, with Mathlib's `θ x = ∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, log p` | the prime number theorem (Hadamard, de la Vallée Poussin 1896) in Chebyshev's form; Apostol, *Introduction to Analytic Number Theory*, Thm. 4.4 with the PNT of Ch. 13; the paper's own citation is [9, §27.12] (DLMF 27.12.2–27.12.4), "We use only its asymptotic form" (p. 15) | `Mathlib/NumberTheory/Chebyshev.lean` (v4.34.0) defines `θ`, `ψ` and proves Chebyshev-type bounds (`θ x ≤ log 4 · x`, `ψ − θ = O(√x)`, lower bounds), but not `θ(x) ~ x` or `ψ(x) ~ x` |

**It is the textbook statement, with nothing added.** It mentions no definition of this
project. Numerical sanity check: `θ(x)/x = 0.95625, …, 0.99952` at `x = 10³, …, 10⁷`
(`numerics/axioms/pnt_theta.py`). Its one direct user is `PNT.theta_scaled` in
`Zeta5/PNT.lean`.

**The two former axioms (until 2026-09-24), now theorems with identical statements.** Each
was stronger than its citation, and each docstring said so:

| former axiom | now | proved from | route |
|---|---|---|---|
| `hermite_pole_integral`: for `a > 0`, `∫_0^∞ w(y)/(y²+a²) dy = a⁴ζ(5,a) − 1/(2a) − 1/4` (the p. 5 display: DLMF 25.11.29 carried through four integrations by parts) | `Zeta5.Hermite.pole_integral` (`Zeta5/Hermite.lean`) | Mathlib alone; `#print axioms` gives `[propext, Classical.choice, Quot.sound]` | not the paper's (deviation 24): expand `w`, substitute `u = 2π(l+1)y/a` termwise, sum over `l` with the Mittag-Leffler series `∑_l 2u/(u²+(2π(l+1))²) = 1/(eᵘ−1) − 1/u + 1/2` (from Mathlib's `cot_series_rep'`), expand `1/(eᵘ−1)` geometrically and use `∫_0^∞ uᵐe^{-cu} du = m!/c^{m+1}`; every sum–integral interchange is for nonnegative terms |
| `pnt_prime_riemann_sum`: for `0 ≤ a < b`, `φ` bounded on `[a,b]` and continuous off a finite set, `X^{-1}∑_{aX<p≤bX} φ(p/X) log p → ∫_a^b φ` (the PNT carried through partial summation and a Darboux sandwich) | `Zeta5.PNT.prime_riemann_sum` (`Zeta5/PNT.lean`) | `chebyshev_theta_asymptotic` | the partial summation of p. 15, as a Darboux-type sandwich (deviation 25): `θ(cX)/X → c`; for each `ε` a uniform partition of `[a,b]` whose oscillations `ω_j` satisfy `∑ω_j h ≤ ε` (small balls around the finite exceptional set; uniform continuity off them); on each piece the prime sum is `φ(y_{j+1})(θ(y_{j+1}X) − θ(y_jX))` up to `ω_j` times the mass; telescoping |

The type identity was checked in Lean on the integrated build: the old `Axioms.lean` of
commit `bfd4249`, re-declared in a scratch namespace over `import Zeta5`, gives types that are
syntactically equal (`Expr ==`) to those of the two theorems, and equal by `rfl`. The use
sites changed only the constant they cite: `Positivity.integral_wt_div_pole` now uses
`Hermite.pole_integral`, and `PrimeSum.tendsto_primeSum` uses `PNT.prime_riemann_sum`.
`Sec6/Gram.lean` reaches `Hermite.pole_integral` through `Positivity.prop_2_2_moment`, so §6
now depends on no project axiom. The numerical checks of the former axioms made in 2026-09-23
(`cert/c3/axioms_numeric.py`: the pole integral to 40 digits at eight values of `a`; the prime
Riemann sums on several test functions up to `X = 10⁷`) apply unchanged to the theorems, whose
statements are the same; `numerics/axioms/hermite_full_chain.py` checks each link of the new
Hermite proof.

### (C) Unfinished steps: none. How (6.14) was proved

Until 2026-09-24 the one `sorry` was `Zeta5.RealBound.eq_6_14`, **(6.14)**, p. 20:
`log Δ_K(ζ(5)) ≤ 2h(h+6N−K)log K + (λM₀ − I(ρ))K² + 18h log K + 160h`, under `Δ_K(ζ(5)) > 0`.
It is now proved in `Zeta5/Sec6/Final.lean`, with its statement unchanged (it was moved from
`RealBound.lean` by the blueprint commit, same name and type). `#print axioms` gives

```
'Zeta5.RealBound.eq_6_14' depends on axioms: [propext, Classical.choice, Quot.sound]
```

(Until the axiom reduction it also listed `Zeta5.Axioms.hermite_pole_integral`, which entered
through Proposition 2.2's moment representation `Positivity.prop_2_2_moment`, used by (6.10).) The route, in the module docstring of `Zeta5/Sec6/Final.lean`:

| step | paper | Lean | notes |
|---|---|---|---|
| (6.14) from a configuration bound | (6.10)–(6.13), p. 20 | `Sec6/Gram.lean` (`andreief`, `eq_6_10`, `eq_6_12_lower/upper`, `gram_bound`, `eq_6_14_of_config`) | Andréief's identity via a double permutation sum; any configuration constant `A ≤ (λM₀ − I(ρ))K² + 3h log K + 131h` suffices (deviation 21) |
| configuration bound (6.6)–(6.9) | pp. 18–19 | `Sec6/Energy.lean` (`configBound`, `eq_6_6_cauchy`) | for the kernel `kC ε x = ½log(x²+ε²)`, `ε = (16K)⁻²`; `20h` in place of `(120+√2)h` (deviation 19) |
| Lemma 6.2 for `kC ε` | p. 18 | `CND.lean` (`cauchy_cnd`), `Frullani.lean`, `GaussPD.lean`, `Swap.lean` | zero-mass energy `≤ 0` from a Frullani representation of `kC ε` and positive definiteness of the Gaussian kernel, for finite measures on a bounded interval |
| cross term `∫U^ρ dσ_ε` | p. 19 | `RhoCross.lean`, `SmoothArc.lean`, `SmoothErr.lean`, `SmoothAux.lean`, `Antideriv.lean` | smoothing error `π(δ + π√(2δ))` per arcsine component, total `88√ε + 420ε` (deviation 20) |
| (A.1), arcsine potential | App. A | `LogCos.lean`, `LogCosInt.lean`, `LogCosOn.lean`, `LogCosOff.lean`, `ArcsinePot.lean` | on the interval via `∫_0^π log sin = −π log 2`; off it via Mathlib's `circleAverage_log_norm_sub_const₂` |
| (A.2), energy of `ρ` | App. A | `RhoEnergy.lean` (`rho_energy_ge`), `PairEnergy.lean`, `ArcComm.lean`, `Bilinear.lean`, `IrhoSum.lean` | proved as `Irho ≤ I_k(ρ,ρ)` for the regularised kernel, which is what (6.6) needs |
| (A.5), field `V` of (6.1) | App. A | `Field.lean` (`Vfield_eq_Vclosed`, `integral_log_add_sq`) | |
| (6.2), (6.7), (6.8); Lemma 6.1 | §6.1, App. A.3 | `Potential.lean`, `Num/*.lean` (`Num.eq_6_7_closed`) | not by (A.9) on Table 2: a certified partition of its own, 1049 cells on `[0,2]`, 2 on `[2,4]`, analytic tail for `t ≥ 4`, every cell `decide +kernel` (deviation 22) |

The 19 leaf statements (marked `LEAF` in the route in `Sec6/Final.lean`) were fixed in the
blueprint commit `4dea216` and tested numerically (`numerics/sec6/check_leaves.py`, output
`check_leaves.out`: 133 checks, 7 of them must-fail controls). Sixteen leaves are tested
directly. The two branches of (A.1) are tested together through `integral_log_abs_sub_cos`.
`kE_rhoM_expand`, a bilinear expansion, has no test of its own. The leaves were then proved
in parallel, and none of their statements changed (`cert/final/fidelity/leaf_stmts.out`). `Num/` is generated by `numerics/sec6/gen_lean.py`. The
certified partition uses no `native_decide`: every finite check is `decide +kernel`.

Before it was proved, (6.14) was checked against exact values of `Δ_K(ζ(5))` at `K = 40, 80,
120`, where it holds with large slack (`CERTIFICATION.md` §6).

---

## 3. How the four large interface statements were proved

Four interface statements, and one lemma shared by two of them, were the last to be proved.
**Each is closed in the strict sense: `#print axioms` shows no `sorryAx`.** Verbatim
(`lake env lean`). The `eq_6_14` line is from 2026-09-24. On 2026-09-23 it read
`[propext, sorryAx, Classical.choice, Quot.sound]`.

```
'Zeta5.outer_local_analysis' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta5.PrimeSum.eq_5_7_uniformity' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta5.CrudeBound.crude_entry_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta5.Section3.entry_bounds_4_2_4_3' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta5.RealBound.eq_6_14' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta5.OuterBasis.outer_local_core' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta5.Uniformity.eq_5_7_uniformity' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta5.Lemma33.entry_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta5.Lemma33.lemma_3_3' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta5.InnerEntries.entry_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta5.HermiteBasis.det_coeffMatrix_unimodular' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta5.prop_4_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta5.prop_4_3' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta5.prop_5_2' depends on axioms: [propext, Classical.choice, Quot.sound, Zeta5.Axioms.chebyshev_theta_asymptotic]
'Zeta5.eq_3_12' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Every intermediate statement below was tested numerically, in exact arithmetic, before it was
proved; the scripts and their outputs are in `numerics/` (see `numerics/README.md`).

| statement | paper | proved in (lines) | how |
|---|---|---|---|
| **shared lemma** `HermiteBasis.det_coeffMatrix_unimodular` | p. 10 "triangular local bases whose diagonal entries are units … a `ℤ_p`-unimodular basis"; p. 12 "Together with the zero-class rows, these form a unimodular basis" | `HermiteBasis.lean` (291), `HermiteBasisCore.lean` (216) | *A basis of integer polynomials that reduces mod `p` to a Hermite-interpolation basis `∏_{c≠a}(t+u_c)^{m_c}(t+u_a)^i` with distinct nodes is `ℤ_p`-unimodular.* Linear independence of the Hermite family over any field (coprimality of the class factors), a dimension count, and reduction of the determinant mod `p`. Used by **both** local analyses. Controls (`numerics/hermite_check.py`, `numerics/HermiteBasisControls.lean`): 1500/1500 random cases, 1000/1000 must-fail, the paper's basis (4.11) at 37/37 primes of (4.9), (4.5) at 300/300 |
| `outer_local_analysis` (§4.2, (4.10)–(4.12)) | pp. 11–12 | `OuterBasis.lean` (1943) | The paper's argument, step by step: square classes and the counts `ℓ−δ` remaining / `ℓ−2` above `p`; the rows `P_aq_{a,i}` of (4.11) and the zero-class rows, reduced mod `p` to the Hermite basis; `v_p(μ(t^e)) ≥ −1` and integrality for `e < 2p−3` (the "first three multiples of `p−1`" cancellation); `μ = μ₀ + p^{-1}μ_L`, so `Gram = A + p^{-1}L`; **`L = U L₀ Uᵀ` with `L₀[i,j] = 0` for `i+j < K−6N+2p−3` in the monomial basis**, hence `rank L ≤ r_p` — exactly p. 12's reason, applied in the basis where it is valid (deviation 3); and the four entry-bound cases (cross-class, both indices `< ℓ−2`, one index `≥ ℓ−2` via the divided difference at `a, p−a`, zero class). Controls (`numerics/outerbasis/`): every intermediate statement checked exactly at every prime of (4.9) for K = 40 and 80 and at four of them for K = 120, plus a few primes `p > K` (0 failures, `rank L = r_p` wherever computed); must-fail control without the `+1/(2j)` of (2.3): 13 failures |
| `PrimeSum.eq_5_7_uniformity` ((5.7) and the two §5.2 displays) | pp. 14–15 | `Uniformity.lean` (1396) | With the explicit constant `C = 400M²`. Inner `γ`: the per-class contribution rewritten as the (5.4) integrand at `z = a/p` plus the extras; an elementary Riemann-sum estimate with two breakpoint cells (`riemann`); the extras' sum `Eq + min(E,U)` exactly; the p. 14 transition remark as the identity `I(T+1) − I(T) = T − x − 2`. `v_p(S_K)`: Legendre with `p² > 2K` and `0 ≤ pJ(h/p) − ∑⌊2i/p⌋ ≤ ⌊2h/p⌋`. Outer: `K·T(p/K)` is an explicit integer, closed by `omega` in each of the three ranges. Controls (`numerics/uniformity/`) over every prime of the ranges at `M = 40` (K = 160 000, 320 000) and `M = 50` (K = 520 000): observed errors of the three conjuncts in `[−151, 149]`, `[3, 37]`, `[−10, 2]` at `M = 40` and `[−191, 183]`, `[3, 46]`, `[−10, 2]` at `M = 50` — far inside `400M²` |
| `CrudeBound.crude_entry_bound` (Lemma 3.3 at the entries of (3.11)) | pp. 8–9 | `Lemma33.lean` (1155) | **Lemma 3.3 itself is proved, in the paper's form** (`lemma_3_3`), together with the pullback (3.1) for every `μ_X(B/D_tail)` (`pullback`). Pole terms as in the paper (`v_p(c_r) ≥ −⌊log_p 2K⌋` via `c_r = ±rA(r)C(2K,K+r)/C(2K,K)`; `v_p(H⁽⁵⁾) ≥ −5⌊log_p K⌋`). The polynomial part by a **different route** from the paper's (deviation 5): the binomial basis `C(x+K,k)`, with `τ` of each quotient computed exactly from (3.3). Controls (`numerics/lemma33/`): 703/703 entries at K = 40 for 11 primes, min slack 0 |
| `Section3.entry_bounds_4_2_4_3` (Prop. 4.1's basis (4.5) and entry bounds) | pp. 10–11 | `InnerTate.lean` (573), `InnerGeneral.lean` (607), `InnerEntries.lean` (1060), with `LocalFunctional.lean` (770) | `B` is the Gram matrix in the basis (4.5), `c = (det U)^{-2}` a `p`-adic unit by the shared lemma. The entry bound `min((4.3), min_c (4.2))` comes from a general local bound `v_p^G(τ^ext_X(W/Q)) ≥ min_a(u_a − t_a) − 4` (`general_bound`), proved from Raabe's multiplication theorem for `τ` (`raabe_tau`: `m⁴τ(P) = ∑_{a<m}τ(P(a+mz))`, from Mathlib's `sum_bernoulli`) and a per-class estimate using a *truncated* inverse of the far-pole factor (`class_bound`) — a finite replacement for the Tate-algebra part of Lemma 3.2 (deviation 7). The degree-`≤ p+1` hypothesis is checked by `uW_le`. Controls (`numerics/inner_entries/`): all 703 entries at K = 40, p = 13 and all 2775 at K = 80, p = 23, for two values of `L₀`: 0 failures |

**Consequences.** Propositions 4.1, 4.3, 5.1 and 5.2 and (3.12) are fully proved (5.2 modulo
the PNT axiom). The §4.1 combinatorics (`Section41.lean`, including the repair of the p. 10
gap, deviation 18) and the §4.2 local lemmas (`OuterLocal.lean`) are load-bearing: 104/148 and
98/107 of their declarations are in the dependency cone of the main theorem (census in §4).

---

## 4. The audit metaprogram, and the independent checks

`Zeta5/Audit.lean` walks the dependency cone of a declaration and reports (A) standard Lean
axioms, (B) this project's own axioms, (C) the `sorry` leaves. It runs on every build. It
defends against two traps that a naive dependency walker falls into:
`Lean.ConstantInfo.value?` returns `none` for theorems in Lean 4.34 (so a walker built on it
silently reports "no sorry"), and reachability must match `Lean.CollectAxioms.collect`
constructor for constructor. It checks itself against `Lean.collectAxioms` on every build
(`[self-check: walker agrees …]`), and `#orphan_sorries` checks that every `sorry` in the
namespace is in the cone.

`Audit.lean` also carries `#sorry_tree` controls. For the last-proved statements they all
print `depends on NO sorry` (the four interface statements of §3, the shared lemma,
`outer_local_core`, `Uniformity.eq_5_7_uniformity`, `Lemma33.lemma_3_3`, `Lemma33.pullback`,
`InnerEntries.raabe_tau`, `general_bound`, `entry_bounds`). `Zeta5.RealBound.eq_6_14`, the
negative control until 2026-09-23 (`rests on 1 sorry(s)`), now prints `depends on NO sorry`,
as do the §6 controls `Sec6.Gram.eq_6_14_of_config`, `Sec6.Num.eq_6_7_closed`,
`Sec6.eq_6_7_closed`, `Sec6.configBound` and `Sec6.rho_energy_ge`.

**Independent checks** (2026-09-24, on commit `808618b`, i.e. **before** the axiom
reduction: the two axioms named below are the former ones, and the counts do not include
`Hermite.lean` and `PNT.lean`; not yet re-run on the reduced state; scripts and recorded outputs in
`cert/final/`, which share no code with `Audit.lean`; full report in `CERTIFICATION.md`):

* `cert/final/FScan.lean` is a scan keyed on the defining module. It covers **all 3 862
  declarations defined in the 70 `Zeta5*` modules**:
  * `axiom` declarations (2): `hermite_pole_integral`, `pnt_prime_riemann_sum`;
  * declarations mentioning `sorryAx`: 0; `unsafe`: 0;
  * sorry carriers in the cone: 0; orphans: 0.

  A walk from all 3 862 declarations at once reaches the same five axioms and no `sorry`, so
  nothing anywhere in the project uses `sorryAx`. `Lean.ofReduceBool`, `ofReduceNat` and
  `trustCompiler` exist in core Lean, as always, but are not in the cone. The cone's axiom
  set is exactly `Lean.collectAxioms`'s five.
* `cert/final/FWalker.lean` is an independent breadth-first walker with planted positive
  controls. It reaches 69 102 constants from `zeta5_irrational` and finds no `sorry` leaf.
  It agrees with `Lean.collectAxioms` on 37 targets, among them `eq_6_14`, `prop_6_3` and
  all 19 §6 leaves.
* `cert/final/FOlean.lean` reads every compiled `.olean` directly, without `importModules`
  or `collectAxioms`. It gives the same 69 102 constants, the same five axioms and no
  `sorryAx`.
* `leanchecker` replayed all 70 modules through the kernel (exit 0).
* Per-module census (`FScan.lean`), declarations reached / defined:
  * AppendixB 281/311, Arithmetic 55/80, Asymptotics 6/6, Axioms 2/2, Basic 127/162,
    Counting 49/50, CrudeBound 64/83, Functional 92/132;
  * HermiteBasis 14/18, HermiteBasisCore 11/11, InnerEntries 176/180, InnerGeneral 52/53,
    InnerTate 78/87, Interface 27/30, Lemma33 142/154, Lemma42 40/66;
  * LocalFunctional 86/115, Normalization 39/39, OuterBasis 298/331, OuterLocal 98/107,
    OuterRange 144/172, Positivity 64/92, PrimeSum 133/156, RealBound 151/318;
  * Section3 2/33, Section41 104/148, Skeleton 8/15, Tail 63/65, Uniformity 166/209;
  * the 37 `Sec6` modules: 403 of 592 in all (`cert/final/FScan.out` lists them one by one);
  * Audit, AppendixBCheck and Checks: 0, by design.
* Cone membership:
  * On 2026-09-23, 72 of 82 named declarations were in the cone. Among them are the four
    interface statements of §3, `ell_lt` (the repair of the p. 10 inequality), the p. 12
    congruence `H5_congr`, `muPole_divided_difference`, `muPole_tail_is_needed`,
    `vanishing_of_rank` and both axioms.
  * 10 are proved but not reached:
    * `ell_lt_caseSplit`, the *second* proof of the p. 10 inequality (`Checks.lean` shows
      by `rfl` that it is the same statement as the in-cone `ell_lt`);
    * `L_gt_three_halves`, **`lemma_3_1`**, `eq_3_2`, `integer_binom_coeffs`, `Lp_small_eq`;
    * **`lemma_4_2`**, the abstract-field form (the route used is `vanishing_of_rank` →
      `prop_4_3_of_local_data_vanishing`);
    * `lemma_4_2_gauss_rank`, `RealBound.eq_6_11`, `RealBound.table2_tiles`.

    So Lemma 3.1 and Lemma 4.2 in their paper forms are *proved but not load-bearing*.
    Proposition 4.1 goes through `general_bound`, and Proposition 4.3 through
    `vanishing_of_rank`.
  * On 2026-09-24, `eq_6_14`, `Sec6.configBound`, `Sec6.cauchy_cnd`, `Sec6.Num.eq_6_7_closed`,
    `Sec6.Gram.andreief` and `Sec6.rho_energy_ge` are in the cone.
    `RealBound.reg_const_le_sixty`, `RealBound.table2_tiles` and
    `Sec6.Gram.paper_6_9_admissible` are not (`cert/final/fidelity/Cone.out`).
* A source scan (`cert/final/source_scan.py`, comments and strings removed) finds:
  * exactly two `axiom` lines, both in `Axioms.lean`;
  * no `sorry`, `admit`, `native_decide`, `implemented_by`, `extern`, `unsafe`, `opaque`,
    `set_option`, `macro`, `syntax`, `notation` or `#eval`;
  * no `debug.skipKernelTC`.

  The only `elab` and `partial def` are the report commands of `Audit.lean`.

---

## 5. What is proved, with no `sorry` (by section of the paper)

`#print axioms` gives `[propext, Classical.choice, Quot.sound]` for everything below unless
an axiom is named.

* **§1–2, top and bottom.** `theorem_1_1` (Theorem 2.1 ⇒ Theorem 1.1); the assembly of
  Theorem 2.1 from its inputs; (2.7)/(2.8) from (7.1)+(7.2); the exact (7.2) margins at
  `M = 200` and `M = 100000`.
* **§2 (`Functional.lean`).** (2.9), the exact leading coefficient of `Δ_K`, hence
  `deg Δ_K = h`; `[X]G_K = V diag(d) Vᵀ`; partial fractions and uniqueness; (2.2) via Euler.
* **§2.4 (`Positivity.lean`, `Hermite.lean`).** Proposition 2.2: (2.10) for every rational
  function in the domain of `μ_X`, and positive definiteness of `G_K(ζ(5))`; the pole integral
  of p. 5 (`Hermite.pole_integral`, a different route from the paper's, deviation 24). No axiom
  since 2026-09-24 (before, modulo `hermite_pole_integral`).
* **§3.** Lemma 3.1 (for partial sums, deviation 2; proved but not in the cone, §4); (3.1)–(3.3);
  **(3.1) for every `μ_X(B/D_tail)`** (`Lemma33.pullback`, `InnerEntries.pullback`); **Lemma 3.3**
  (`Lemma33.lemma_3_3`, and `lemma_3_3_strong` without the `−v_p(24)`); (3.11) including the
  recovery of `S_K`; the p. 9 binomial identities; **(3.12)**; von Staudt–Clausen and
  `κ_d ∈ ℤ_p` for `d ≤ p+1`; **Raabe for `τ`** (`raabe_tau`), the polynomial case of (3.7).
* **§4.1.** The allocation (4.4) and its existence; `p·ℓ_A(a) < 2A + p`, the repair of the gap
  in the p. 10 inequality `b_a ≤ 6αx + 3` (deviation 18; two independent proofs, `ell_lt` and
  `ell_lt_caseSplit`); `L_a ≥ 0`; (4.8); **the unimodularity of (4.5)**; **the entry bounds
  (4.2)/(4.3) for the whole summands**; the p. 11 weight comparisons; **Proposition 4.1**.
* **§4.2.** Lemma 4.2 (4.13) over an abstract valued field (proved, not in the cone), and the
  rank form actually used, `vanishing_of_rank` (a determinant taking more than `r` columns from
  a rank-`≤ r` matrix vanishes); **the splitting (4.10) with `rank L ≤ r_p`**; **the basis
  (4.11) and its unimodularity**; the `H⁽⁵⁾` congruence and the divided-difference integrality
  of p. 12; **the entry bounds behind (4.12)**; the p. 13 table and (4.14); **Proposition 4.3**,
  both assertions.
* **§5.** Proposition 5.1; `log m_{K,M}` split along (5.1); the branch-1 estimate;
  **(5.7) and the two §5.2 displays, with an explicit uniform constant**; the p. 14 regularity
  sentence (`RR_reg`); the partial summation of p. 15 (`PNT.prime_riemann_sum`,
  `Zeta5/PNT.lean`, deviation 25); **Proposition 5.2 (5.11)** — modulo the prime number theorem
  `chebyshev_theta_asymptotic` (before 2026-09-24, modulo `pnt_prime_riemann_sum`).
* **Appendix B, §5.3 (`AppendixB.lean`, `Tail.lean`).** (5.8)–(5.10) with `I_out` computed;
  (5.12)–(5.14); (5.15)–(5.17) in finite-interval form (deviation 4); (5.18) exactly; (5.19)–(5.21).
* **§6 and Appendix A (`RealBound.lean`).** (6.11) as printed; (6.15); `prop_6_3_of`, i.e.
  (6.14) ∧ (6.15) ⇒ (6.16) with the exact `K² log K` cancellation; (A.10)/(6.4) from Table 1
  with certified logarithm enclosures; Table 2's 684-cell tiling of `[0,2]` (not in the cone).
* **§6 and Appendix A (`Sec6/`), since 2026-09-24.** **(6.14)** and **Proposition 6.3**
  (`Sec6/Final.lean`); Andréief's identity (6.10), (6.12), (6.13) (`Gram.lean`); the
  configuration bound (6.6)–(6.9) for the regularised kernel (`Energy.lean`); Lemma 6.2 for
  that kernel (`CND.lean`); (A.1) for every interval (`ArcsinePot.lean`), (A.2) as a lower
  bound for the regularised energy (`RhoEnergy.lean`), (A.5) (`Field.lean`); (6.2) and (6.7)
  for the closed forms on the whole half-line (`Num/`), transferred to the field `V` of (6.1)
  (`Potential.lean`). (Modulo `hermite_pole_integral` through (6.10) until 2026-09-24; now
  with no axiom.)
* **§7.** (7.1) from (5.21) and (6.16).

---

## 6. Faithfulness, and deviations from the paper

**Statements checked against the PDF page images** (pp. 5–15, 18–20):

* `Lemma33.lemma_3_3` is Lemma 3.3 (p. 8) as printed: `v_p^G(τ_X(g)) ≥ −6⌊log_p max(2K,d+1)⌋ −
  v_p(24)` for `g = (K!)²A(x)/∏_{0<|r|≤K}(x−r)`, `deg A ≤ d`, where `τ_X` is `tauExtOf X`
  (polynomial division plus simple partial fractions, p. 6). The hypothesis "`A` integer-valued
  on `ℤ_p`" is taken as `v_p(A(z)) ≥ 0` for all `z ∈ ℤ`, which is equivalent (ℤ is dense in
  `ℤ_p` and `A` is continuous), so the Lean lemma is at least as strong as the paper's. It
  holds for every prime `p`, every `K`, every `d`. **Not weakened.**
* `Lemma33.pullback` / `InnerEntries.pullback` are (3.1) (p. 6) for every rational function
  `B/D_tail`, i.e. the whole domain of `μ_X` as the project defines it (`muOver`).
* `raabe_tau` is the polynomial case of (3.7) (p. 7, "For polynomials, (3.7) follows from
  Bernoulli multiplication"), for every `m ≥ 1`, not only `m = p`.
* `outer_local_core` has literally the type of `outer_local_analysis` with `outerDim`,
  `outerWeight` unfolded (`rfl`); the weights `wtO` are the doubled (4.12) (`min(0, 2i + 6δ −
  ℓ − 4)` for `i < ℓ−2`, else `0`; zero class `−1` for one pole, `−4, 0` for two), matching
  p. 12 exactly.
* `Uniformity.eq_5_7_uniformity` has literally the type of `PrimeSum.eq_5_7_uniformity`, whose
  three conjuncts are (5.7)'s two halves and the sum of the two §5.2 displays (pp. 14–15).
* `InnerEntries.entry_bounds` has literally the type of `entry_bounds_4_2_4_3`: `Δ_K = c·det B`
  with `v_p(c) = 0` and `v_p^G(B_{uv}) ≥ e_{uv}`, `w_u + w_v ≤ 2e_{uv}` — "each entry in the new
  basis has valuation at least the sum of its two row weights. … The basis change is
  unimodular" (p. 11).

**No weakened statement was found.**

**Deliberate deviations**, each recorded in the relevant docstring:

1. **`eq_6_14` is stated with `I(ρ)` and `M₀` as defined real numbers**, the closed form
   (A.2) and `−1329/200`, not as the logarithmic energy `∬log|t−u|dρ dρ` and not as a
   conclusion of Lemma 6.1. (A.10)/(6.4) is proved from them. Since 2026-09-24 the proof of
   `eq_6_14` connects them to the energy argument: `Irho ≤ I_k(ρ,ρ)` for the regularised
   kernel (`Sec6.rho_energy_ge`, deviation 19) and (6.2)/(6.7) for the closed forms of `U^ρ`
   and `V` with `M₀ = −1329/200` (`Sec6/Num/`, deviation 22). The equality of `Irho` with the
   singular energy `∬log|t−u|dρ dρ` is not stated.
2. **`lemma_3_1` proves (3.4) for every partial sum `∑_{j≤J}p^jU_j`, not for the series** in
   the Tate algebra `ℚ_p⟨z⟩`, which is not formalised. A proved lemma weaker than the paper's.
   (It is also bypassed: Proposition 4.1's proof goes through `general_bound`, deviation 7.)
3. **`outer_local_analysis` states the literal rank form of (4.10), `rank L ≤ r_p`.** An
   earlier formulation of this interface statement, as a set of vanishing columns of `L` in
   the basis (4.11), was **false** for the paper's own `L` (no vanishing columns at `K = 40`,
   `p = 17, 19, 23`; found in the referee audit of the preprint, see README, 'Provenance'), and
   was replaced by the rank form before the proof was written. The proof shows why:
   `OuterBasis` proves `rank L ≤ r_p` exactly as p. 12 argues — the vanishing is in the
   **monomial** basis (`L0_eq_zero`), and `L = U L₀ Uᵀ` transports the rank bound to (4.11).
   The statement proved is (4.10) as printed.
4. **`AppendixB.eq_5_16_5_17` proves the difference form** `∫_20^M R x^{-3} ≤ −2689/48000 +
   λ/M − (2923/240−1/4)/M² + 32/M³` rather than the two separate improper integrals (5.16) and
   (5.17): implied by their conjunction, so formally weaker than p. 16, and exactly what
   `∫_3^M = ∫_3^20 + ∫_20^M` consumes. The proof reproduces (5.16)'s constant internally.
5. **Lemma 3.3 is proved by a different route from the paper's.** The pole terms follow the
   paper. The polynomial part does **not** use the paper's two-scale estimate
   `P(ℤ_p) ⊂ p^{−L₀−M₀}ℤ_p`, the Vandermonde bound (3.8) or the `τ`-bound (3.9): instead
   `A = ∑a_kC(x+K,k)` and `τ` of each quotient is computed exactly (`τ(ΔS) = [x⁴]S`). So
   **(3.8) and (3.9) are not formalised** and the paper's proof of Lemma 3.3 is not checked
   line by line — its *statement* is. The proof also shows the `−v_p(24)` is unnecessary
   (`lemma_3_3_strong`).
6. **`eq_5_7_uniformity` bundles three paper claims into one existential over one constant
   `C`**, proved with `C = 400M²`. Proving the bundled form with a shared constant is at least
   as strong as proving each separately. The true constant is about `4M` (controls).
7. **Lemma 3.2 (3.7) is not formalised as stated.** The Tate-algebra extension `ℬ_T`, (3.5),
   the parameter `Y = p⁵X + C_p` of (3.6), and (3.7) for rational functions with far poles do
   not appear in Lean. Proposition 4.1 is proved **without** them: the pole terms of
   `τ^ext_X(W/Q)` are bounded directly (`v_p(c_r) ≥ u_a − t_a + 1`, `v_p(H⁽⁵⁾) ≥ −5`), and the
   polynomial part through `raabe_tau` (the polynomial half of (3.7), the paper's own
   justification of it) and `class_bound`, where the far-pole series is replaced by a truncated
   inverse with an explicit remainder of valuation `≥ n−1`. A reader should not say
   "Lemma 3.2 is formalised"; what is formalised is everything Proposition 4.1 uses it for.
8. **`bCoef_lt_real` proves `b_a < 6αx + 3` where the paper prints `≤`.** Strictly stronger
   (see deviation 18 for why a proof was needed at all).
9. **`lemma_4_2` takes `pinv` with `v(pinv) ≥ −1`** rather than literally `p^{-1}`; more
   general, and the instantiations satisfy it.
10. **`eq_5_21` and `eq_5_16_5_18` are stated with `40 ∣ M`, `M > 0`**, as printed.
11. **(5.8)/(5.9) are written as nested `if`s**, differing from the paper only at `y ≤ 1/3`,
    `y = 1/2`, `y = 1` — outside `(1/3, 2λ)` or a null set at a Table-4 endpoint.
12. **Naming trap, not an error:** `InnerAlloc.L 0` is *not* the paper's `L₀ = 4M+10`;
    `gammaIn` correctly uses `range (L0 M)`.
13. Two places where **more** was done than the paper asks: `RealBound`'s log remainder, and
    (6.11) via `∑ℓ⁴q^ℓ ≤ 24q/(1−q)⁵` — the statement proved is the printed one.
14. **Do not misquote** `PrimeSum.RR_bddOn`: it proves `|R| ≤ 200M²` on `[3,M]`, far weaker
    than the paper's `|R| ≤ 6λM + 13/8`; nothing downstream needs the sharp constant.
15. **The p. 12 divided-difference step needs more than the paper says.** The paper cites
    only `H⁽⁵⁾_{p−a} ≡ H⁽⁵⁾_{a−1} (mod p)`; that alone leaves a residue `−1/a`
    (`OuterLocal.muPole_tail_is_needed`, machine-checked). The proof uses the `−1/4 + 1/(2j)`
    tail of (2.3) as well (`muPole_divided_difference`), and the must-fail control confirms it
    is essential (13 failures at `K = 40` without `+1/(2j)`, `numerics/outerbasis/`). A point
    the author may want to revise, not an error in the result.
16. **Unimodularity by one argument for both bases.** The paper's two justifications —
    "triangular local bases whose diagonal entries are units" (p. 10) and "the local
    polynomials are monic of successive degrees, and the resultants of distinct class factors
    are units" (p. 12) — are replaced by one: the basis reduces mod `p` to a Hermite
    interpolation basis with distinct nodes, which is linearly independent over `𝔽_p`. Same
    conclusion, different proof.
17. **The §4.2 local analysis holds under weaker hypotheses than printed:** `OuterHyp` (which
    is (4.9) without `p ≤ K`) is all `OuterBasis` uses — `p` prime, `p ≥ 7`, `K < 3p`,
    `2K < p²`, `2N < p`, `5N ≤ 2p−2` — and nothing uses `K ≥ 200M²`. Direction of strength.
18. **A gap on p. 10, repaired.** The paper asserts `b_a ≤ 6αx + 3` (the line after (4.4)) with
    no proof, attributing it to (4.4); it is in fact a statement about `ℓ_N`, equivalent to
    `p·ℓ_N(a) ≤ 2N + p`. The naive bound `ℓ_A(a) ≤ 2⌊A/p⌋ + 2` gives only `b_a ≤ 6αx + 6`,
    which is not enough: the dimensions `L_a` of (4.4) would not be provably nonnegative
    (`naive_chain`, `naive_bound_insufficient`), and on every residue class one of two
    obstacles blocks the naive route (`ell_naive_attained`, `naive_not_enough`). The inequality
    is proved here in the strict form `p·ℓ_A(a) < 2A + p` by the case split on `v_A = A mod p`
    (`Zeta5.ell_lt_caseSplit`, `Section41.lean`), and independently from the closed form of
    `ℓ_A` (`Zeta5.ell_lt`, `Counting.lean`, the one in the dependency cone); `Checks.lean`
    verifies by `rfl` that the two statements are identical. In the paper's variables it is
    `bCoef_lt_real`. A point the author may want to revise, not an error in the result.

Deviations in the proof of (6.14) (`Zeta5/Sec6/`, 2026-09-24; each also recorded in the module
docstrings of `Sec6/Final.lean`, `Sec6/Defs.lean`, `Sec6/Energy.lean`, `Sec6/Gram.lean`,
`Sec6/SmoothErr.lean` and `Sec6/Num/Final.lean`):

19. **Kernel regularisation on the real line instead of circles.** The paper replaces each
    point `t_i` by the uniform measure on a circle of radius `ε` in `ℂ` and applies Lemma 6.2
    to `log|z − w|`, with its log-integrability hypothesis and a limiting argument. Here the
    points stay Dirac masses and the kernel is regularised: `kC ε x = ½log(x²+ε²)`, which is
    `≥ log|x|`, continuous, and `log ε` at `0`. The zero-mass argument of Lemma 6.2 (Frullani
    representation plus Gaussian positive definiteness) is proved for `kC ε` directly
    (`cauchy_cnd`); every singular integral is a one-dimensional integral in `θ` for the
    arcsine measures `θ ↦ m + r cos θ`. Lemma 6.2 for the singular kernel is **not**
    formalised. The resulting (6.9') has `2h log K + 20h` where the paper has `(120+√2)h`.
20. **The smoothing error** is bounded by `π(δ + π√(2δ))` per arcsine component
    (`smooth_err_norm`), via the nearest point of `[−1,1]` in angle form and
    `∫_0^X log(1+b²/x²)dx`, instead of the paper's mass bound and `60√ε` (p. 19); the paper's
    regularisation constant `≤ 60` (`RealBound.reg_const_le_sixty`) is proved but not used.
21. **The Gram step** keeps the factor `1/h!` of (6.10) through to (6.14). (The paper keeps it
    in (6.13) and discards it, as `log h! ≥ 0`, only when it takes logarithms.) It uses
    `∫_0^∞(1+y)⁵e^{−y/K}dy ≤ 326K⁶` in place of the paper's constant `652`. The `1/h!` is what
    lets `eq_6_14_of_config` accept configuration bounds up to `3h log K + 131h`. The bound
    actually proved (`2h log K + 20h`) would give (6.14) without it; the upper half of
    (6.12) is proved by sum–integral comparison for an increasing function, avoiding the
    paper's "decreasing in `t`, then evaluate at `t = 0`". The paper's own (6.9) constants
    are admissible for `eq_6_14_of_config` (`paper_6_9_admissible`).
22. **(6.2) is not proved by Appendix A's route.** The bound `ℬ(l,r)` of (A.9) on the 684
    cells of Table 2 is not formalised; Table 2 is used only for the proved (and unused)
    tiling statement. Instead `Sec6/Num/` evaluates the closed forms (A.1)/(A.5) of
    `2U^ρ − V` with certified rational interval arithmetic on the formalisation's own
    partition — 1049 cells on `[0,2]`, 2 on `[2,4]` against `M₀ − 3/10` — each checked by
    `decide +kernel`, and proves `t ≥ 4` by an analytic bound (`tail_bound_ge4`) replacing
    (6.8).
23. **(A.1)** is proved in normalised form (`(1/π)∫_0^π log|x − cos θ|dθ`) and scaled: on
    `[−1,1]` from the product formula for `cos φ − cos θ` and `∫_0^π log sin = −π log 2`, off
    it from Mathlib's circle average of `log‖· − a‖`.

24. **The pole integral of p. 5 is proved by a different route from the paper's** (since
    2026-09-24; `Hermite.pole_integral`, formerly the axiom `hermite_pole_integral`, same
    statement). The paper derives it from Hermite's formula (DLMF 25.11.29) by four
    integrations by parts. Neither Hermite's formula nor those integrations by parts is
    formalised. Instead the proof expands `w`, substitutes termwise, and sums with the
    Mittag-Leffler expansion of the cotangent (Mathlib's `cot_series_rep'`), with no axiom
    (§2 (B)).
25. **The partial summation of p. 15 is proved as a Darboux-type sandwich** (since
    2026-09-24; `PNT.prime_riemann_sum`, formerly the axiom `pnt_prime_riemann_sum`, same
    statement), not by Abel's identity: `φ` is compared, piece by piece of a uniform
    partition, with its value at the right endpoint, and the prime sums over the pieces are
    differences `θ(vX) − θ(uX)` (§2 (B)).

---

## 7. What to do next, in value order

1. **Re-certify the reduced state** (branch `axioms`): re-run the dependency checks of §4 and
   `CERTIFICATION.md` on it. Several of the certification scripts name the former axioms
   (`cert/final/FScan.lean`, `FWalker.lean`, `fidelity/Fidelity.lean`, `cert/C3Scan.lean`,
   `cert/C3Attack.lean`) and must be updated to the new names first.
2. *Done 2026-09-24:* `pnt_prime_riemann_sum` reduced to `θ(x) ~ x`, and
   `hermite_pole_integral` proved outright (not merely reduced to DLMF 25.11.29). The one
   remaining axiom is the prime number theorem itself; removing it would mean proving the PNT
   in Lean, which Mathlib v4.34.0 does not do.
3. **Points the author may want to revise**, found by the formalization and the referee audit:
   * the p. 10 inequality `b_a ≤ 6αx+3` (deviation 18);
   * the p. 12 divided-difference step, which needs the `+1/(2j)` tail (deviation 15);
   * the phrasing of the rank argument for (4.10) (deviation 3).
4. **Minor, found by the 2026-09-24 certification; none affects soundness**
   (`CERTIFICATION.md` §7):
   * `Audit.lean`'s sorry list skips internal names. The module-keyed scans of `cert/final/`
     cover them.
   * Its orphan message prints even when there is no `sorry` at all.
   * `Zeta5.vGAtLeast_mul` is proved twice, with the same statement, in `Section41.lean` and
     `Normalization.lean`. Both proofs are sorry-free.

   Fixing any of these would change a definition or remove a theorem. Under the ground rules
   they are therefore recorded here rather than changed.

---

## 8. Certification

*The certification below is of the state before the axiom reduction (two axioms). The
reduced state (one axiom) is pending re-certification; see the addendum in
`CERTIFICATION.md`.*

An adversarial certification of the then-present state was made on 2026-09-24, on code commit
`808618b` (`CERTIFICATION.md`; scripts and outputs in `cert/final/`). Its verdict: **the
claim holds.** `Zeta5.zeta5_irrational : Irrational Zeta5.zeta5` rests on `propext`,
`Classical.choice` and `Quot.sound` and on the two axioms then in `Axioms.lean`. It uses **no**
`sorry`, and nothing else is in the dependency cone.

* **Clean builds.** Four independent clean builds of the same sources all succeeded: 8994
  jobs, 0 errors, no `sorry` warning, 17 lint warnings. Each took 7½–8 minutes.
* **Five independent dependency checks agree name for name:**
  * `#print axioms`;
  * the walker `cert/final/FWalker.lean`, which builds shortest provenance chains and
    catches planted `sorry`, axiom, `where`-auxiliary and instance-field controls;
  * a module-keyed scan of all 3 862 Zeta5 declarations, with a walk from all of them at
    once (`cert/final/FScan.lean`);
  * `Audit.lean` in the clean-build logs;
  * `cert/final/FOlean.lean`, which reads the `.olean` files directly and does not use
    Lean's environment or `collectAxioms`.

  The cone has 69 102 constants. In Lean 4.34, `#print axioms` and `collectAxioms` read
  axiom lists that were stored when the `.olean` files were written. The three walkers
  traverse the proof terms themselves.
* **Kernel replay.** `leanchecker` replayed all 70 modules through the kernel (52 min, exit 0).
* **No statement changed.** Every one of the 3 272 declarations of the 2026-09-23 state
  (`main`, `9ce1320`) is still present, with the same kind, universe parameters, type and
  value. The only exceptions are 16 compiler-generated `_proof_1_N` lemmas, whose types
  differ only in hygienic binder names (they are α-equivalent). `eq_6_14` and `prop_6_3`
  moved from `RealBound` to `Sec6.Final` with identical types. All 590 new declarations are
  in the new `Sec6` modules. No axiom was added, and both axioms are identical.
* **Fidelity of §6.**
  * `eq_6_14` and `prop_6_3` match (6.14) and (6.16) of the PDF term for term.
  * Their hypothesis `0 < Δ_K(ζ(5))` is discharged by `delta_pos`.
  * Table 1, `Irho`, `M0` and (6.4) were re-checked against the PDF.
  * The 19 leaf statements are unchanged since the blueprint.
  * `gen_lean.py` regenerates `Num/` byte for byte.
  * `check_leaves.py` gives 133 PASS and 0 FAIL.
* **Defects found:** none that affects soundness or any statement. The documentation issues
  found (stale descriptions of the 2026-09-23 state and stale warning counts, the wording
  about the 1/h! of (6.10), and an overstatement about the numerical tests of the leaves)
  have been corrected. The minor points of §7 item 4 are recorded.

The certification of 2026-09-23 (32 modules, `eq_6_14` the one `sorry`) is summarised in
`CERTIFICATION.md`, "Earlier certification (2026-09-23)". Its results about the two axioms
and about the meaning of the main statement still applied on 2026-09-24 before the axiom
reduction. After it, every definition that the main statement uses is unchanged, and the two
statements it examined as axioms are now theorems with the same types.

**How to report this result (2026-09-24, after the axiom reduction, pending its
re-certification):** *"ζ(5) is irrational, machine-checked conditional on one external result
entered as an axiom: the prime number theorem, in Chebyshev's form θ(x) ~ x."* Nothing
internal to Fauzan's argument is assumed. (As certified before the reduction, the result was
conditional on two stronger axioms: Hermite's integral formula in the integrated-by-parts form
of p. 5, and the prime number theorem in partial-summation form.) (Before 2026-09-24 the result had to be reported as conditional also on
(6.14), Fauzan's own claim.)
