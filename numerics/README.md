# Numerical controls

Before each of the four large interface statements of the development (`docs/STATUS.md` §3)
was proved in Lean, it was broken into intermediate lemma statements, and each of those was
tested in **exact arithmetic** against the paper's own data. The scripts in this folder are
those tests, with their recorded outputs. Nothing in the Lean library depends on them: they
are evidence that the statements being proved are the right ones, not part of the proof.

Two kinds of test appear throughout:

* **known-answer controls** compute the quantity a Lean statement is about directly from the
  definitions (in the same form as the Lean definitions, not from the paper's closed forms)
  and check the claimed bound at every case that can be enumerated;
* **must-fail controls** break one hypothesis, or strengthen the conclusion by one unit, and
  check that the test then *fails*. They show that a test can fail, and which hypotheses are
  really needed.

**Requirements.** Python 3 with `sympy`, `numpy` and `mpmath`; [SageMath](https://www.sagemath.org/)
for the `.sage` scripts; for the two `.lean` files, the Lean project built with `lake build`.
All commands below are run from the repository root. Sage writes a preparsed `*.sage.py` file
next to each `.sage` script; those are ignored by git.

---

## Hermite basis unimodularity — `hermite_check.py`, `HermiteBasisControls.lean`, `HermiteConsumerExamples.lean`

For `Zeta5.HermiteBasis.det_coeffMatrix_unimodular`: integer polynomials that reduce mod `p` to
a Hermite-interpolation basis `∏_{c≠a}(X+u_c)^{m_c}(X+u_a)^i` with distinct nodes have a
coefficient matrix `U` with `det U ≠ 0` and `v_p(det U) = 0`. This one lemma replaces the
paper's two unimodularity arguments (pp. 10 and 12).

```
python3 numerics/hermite_check.py                       # about 20 s  -> hermite_check.out
lake env lean numerics/HermiteBasisControls.lean        # no output = success
lake env lean numerics/HermiteConsumerExamples.lean     # no output = success
```

* `hermite_check.py`, exact integer arithmetic, fixed random seed. Part A: 1500 random
  instances with random integer lifts (1500/1500 unimodular). Part B, must-fail: two nodes
  equal mod `p` (1000/1000 have `p | det U`). Part C, known answer: the paper's outer basis
  (4.11) at `K = 40, 80, 120` and every prime of (4.9), 37 primes in all, and 18 primes with
  `p > K`: every row reduces mod `p` exactly to the Hermite basis, and `v_p(det U) = 0`. Part D:
  the inner basis (4.5) with nodes `c²`, 300/300.
* `HermiteBasisControls.lean` (not part of the library): a known answer machine-checked in Lean
  (`p = 7`, nodes `0, 1, 4`, `det U = 36`), the lemma applied to it, and a must-fail instance
  (nodes `8` and `1`, which collide mod 7: `det U = −7`), showing that the injectivity
  hypothesis cannot be dropped.
* `HermiteConsumerExamples.lean` (not part of the library): the two places that use the lemma,
  the outer basis (4.11) and the inner basis (4.5), each apply it with light glue. Written
  before the lemma was proved, to check that its statement is the one both consumers need.

## Outer-range basis control at K = 40, 80, 120 — `outerbasis/`

For `outer_local_analysis` (§4.2, (4.10)–(4.12)) and its proof in `Zeta5/OuterBasis.lean`.
`ob_control.sage` builds, with the same definitions as the Lean file, the square classes, the
rows (4.11) and the zero-class rows, and checks at each given prime: the class counts; the
reduction of every row mod `p` to the Hermite basis; unimodularity; `v_p(μ(t^e)) ≥ −1` and the
integrality of `μ₀`; the valuations of the pole terms; **every entry bound** behind (4.12); the
vanishing pattern `L₀[i,j] = 0` for `i + j < K − 6N + 2p − 3` in the monomial basis;
`L = U L₀ Uᵀ`; `rank L ≤ r_p`; and the residue formula.

```
sage numerics/outerbasis/ob_control.sage 40 17 19 23 29 31 37 41 43     # -> ob_control_K40.out
sage numerics/outerbasis/ob_control.sage 80 29 31 41 43 53 79 83         # -> ob_control_K80.out
sage numerics/outerbasis/ob_control.sage 80 37 47 59 61 67 71 73         # -> ob_control_K80b.out
sage numerics/outerbasis/ob_control.sage 120 41 43 61 113 127            # -> ob_control_K120.out
sage numerics/outerbasis/ob_mustfail.sage 40 17 23                       # -> ob_mustfail_K40.out
```

Results: 0 failures at every prime tested — all primes of (4.9) for `K = 40` and `K = 80`, four
of them for `K = 120`, and a few primes `p > K` — and `rank L = r_p` wherever computed. The
must-fail variant `ob_mustfail.sage` differs only in dropping the `+1/(2j)` term of (2.3) from
the pole terms: it gives 13 failures of the entry bounds at `K = 40`, which is why the p. 12
divided-difference step needs that term (`docs/STATUS.md`, deviation 15). The `K = 40` runs
take seconds; running time grows quickly with `K`, and the `K = 120` run is by far the
slowest.

## Inner-range entry bounds — `inner_entries/`

For `Section3.entry_bounds_4_2_4_3` (Proposition 4.1's basis (4.5) and entry bounds) and its
proof in `InnerTate.lean`, `InnerGeneral.lean`, `InnerEntries.lean`. `core.py` implements
`τ`, the extended functional `τ^ext_X` and `p`-adic valuations in exact rational arithmetic.

```
python3 numerics/inner_entries/test_general.py
python3 numerics/inner_entries/test_controls.py
python3 numerics/inner_entries/test_largeE2.py          # these three, in this order -> controls_python.out
sage numerics/inner_entries/kac_inner.sage 40 13 3      # -> kac_40_13_L3_full.out
sage numerics/inner_entries/kac_inner.sage 40 13 4      # -> kac_40_13_L4_full.out
sage numerics/inner_entries/kac_inner.sage 80 23 3      # -> kac_80_23_L3_full.out
sage numerics/inner_entries/kac_inner.sage 80 23 4      # -> kac_80_23_L4_full.out
```

* `test_general.py`, random instances at `p = 7, 11, 13`: Raabe's formula
  `p⁴τ(P) = ∑_{a<p} τ(P(a+pz))` (T1), the residue bound (T2), the per-class bound (T3) and the
  general bound `v_p^G(τ^ext_X(W/Q)) ≥ min_a(u_a − t_a) − 4` (T4): 0 failures, and T4 is
  attained with equality in most instances.
* `test_controls.py`: control C1 (degree above `p + 1` in one class) produced no failures in
  these instances, so it does not show that the degree hypothesis is needed; C2 (dropping the
  hypothesis that same-class poles differ by a unit multiple of `p`) fails in 119 of 120
  instances; C3 (claiming `E + 1` instead of `E`) fails wherever `E` is attained.
* `test_largeE.py` (imported by, and printed first by, `test_largeE2.py`): the regime where
  every class has many more zeros than poles, with the same `E + 1` must-fail check.
* `kac_inner.sage`, known answer on the paper's basis (4.5), for every entry: the pullback
  identity (T5), the class-count exponent equals `min((4.3), min_c (4.2))` (T6), the valuation
  bound (T4) and the weight comparison (TW). The arguments are `K p L₀`, where `L₀`, the size
  of the zero class, is left free. 0 failures in all 6956
  entries (703 + 703 at `K = 40`, `p = 13`; 2775 + 2775 at `K = 80`, `p = 23`).

## Uniformity constants — `uniformity/`

For `PrimeSum.eq_5_7_uniformity` ((5.7) and the two §5.2 displays) and its proof in
`Uniformity.lean`, where the uniform constant is `C = 400M²`.

```
python3 numerics/uniformity/controls.py 40 4000 8000    # M = 40, K = 160 000 and 320 000, ~1.5 min -> controls_M40_K160000_K320000.out
python3 numerics/uniformity/controls.py 50 13000        # M = 50, K = 520 000, ~3.5 min -> controls_M50_K520000.out
python3 numerics/uniformity/substubs.py 40 8000         # ~2 min -> substubs_M40_K320000.out
```

* `controls.py` computes, exactly and from definitions written as in `Zeta5/Basic.lean` and
  `Zeta5/AppendixB.lean`, the three errors of the statement over **every** prime of the
  relevant ranges: `E1 = γ_p^in − pΓ(K/p)` and `E2 = v_p(S_K) − p𝒩(K/p)` over the inner
  primes, `E3 = −(v_p(S_K) + γ_p^out) − K·T_out(p/K)` over `K/3 < p ≤ 2h`. Observed ranges:
  `E1 ∈ [−151, 149]`, `E2 ∈ [3, 37]`, `E3 ∈ [−10, 2]` at `M = 40`, and `[−191, 183]`, `[3, 46]`,
  `[−10, 2]` at `M = 50` — the true constant is about `4M`, far inside `400M²`. (`K = 160 000`
  is below the paper's size condition `K ≥ 200M²` and is included as an extra case.)
* `substubs.py` checks the intermediate statements of `Uniformity.lean` (the Riemann-sum error
  `ρ`, the zero block, the split of `Γ`, the identity `I(T+1) − I(T) = T − x − 2`, the sum over
  the `ε` classes, the Legendre gap) at `K = 320 000`, and the outer-range identities for all
  `n < 400`.

## Lemma 3.3 — `lemma33/`

For `CrudeBound.crude_entry_bound` and `Lemma33.lemma_3_3` (Lemma 3.3, p. 8, and its use at the
entries of (3.11)).

```
python3 numerics/lemma33/entries_n1.py      # ~6 s -> entries_n1_full.txt
python3 numerics/lemma33/l33check2.py       # -> l33check2.out
python3 numerics/lemma33/pullback_check.py  # -> pullback_check.out
python3 numerics/lemma33/l33check.py        # ~20 s -> l33check.out
```

* `entries_n1.py`: every entry of (3.11) at `n = 1` (`K = 40`, `h = 37`, 703 entries), computed
  exactly from the `t`-side definition of `μ_X`, against the bound of Lemma 3.3 at 11 primes
  from 2 to 211: no violation; the minimum slack is 0 (at `p = 211`), so the bound is sharp
  there.
* `l33check.py` and `l33check2.py`: the route the Lean proof takes for the polynomial part
  (`docs/STATUS.md`, deviation 5) — the binomial basis `C(x+K, k)`, the identity
  `τ(ΔS) = [x⁴]S`, and closed forms of the quotients — and Lemma 3.3 without the `−v_p(24)`
  term for `2 ≤ K ≤ 8`, three degrees `d` and the primes up to 13 (no violation).
* `pullback_check.py`: the pullback (3.1), `μ_X(B/D_tail) = ±τ^ext_X(x⁵B(−x²)D_N(−x²))`, on
  random `B`: 0 mismatches.
