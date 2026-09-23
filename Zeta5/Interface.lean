/-
Zeta5/Interface.lean

THE PAPER'S NAMED STATEMENTS, one Lean declaration each, and the assembly of Theorem 2.1
and Theorem 1.1 from them.

This file is the table of contents of the formalisation: every numbered statement of
Fauzan's paper that Theorem 1.1 goes through has a declaration here whose *type* is a
faithful transcription of the printed statement, so that a reader can check the
transcription against the PDF without reading any proof.

CONVENTION (see README): nothing here is proved by weakening a statement; where the formal
statement records only part of a paper statement, the docstring says which part, and the
rest is a separate named `sorry`.

THIS FILE CONTAINS **NO** `sorry` (since 2026-09-23).  Every
statement below is discharged by a proof elsewhere in the project:

  (2.9)   leading coefficient of `Δ_K`         ← `Zeta5.Functional.eq_2_9`
  Prop. 2.2  (2.10) and the "Hence" clause     ← `Zeta5.Positivity.prop_2_2_moment`,
                                                 `Zeta5.Positivity.prop_2_2`, modulo the
                                                 single external axiom
                                                 `Zeta5.Axioms.hermite_pole_integral`
  Prop. 4.1  the inner range                   ← `Zeta5.Section3.prop_4_1`
  Prop. 4.3  the outer range (both assertions) ← `Zeta5.Outer.prop_4_3`,
                                                 `Zeta5.Outer.prop_4_3_large`
  Prop. 5.1  integrality of `Q_{K,M}`          ← `Zeta5.prop_5_1_of` (Normalization.lean)
                                                 applied to (3.12) and Props 4.1, 4.3
  (3.12)  the crude valuation bound            ← `Zeta5.CrudeBound.eq_3_12'`
  Prop. 5.2  (5.11), the prime-sum bound       ← `Zeta5.PrimeSum.prop_5_2`, modulo the
                                                 external axiom
                                                 `Zeta5.Axioms.pnt_prime_riemann_sum`
  (5.16)–(5.18) the constant bookkeeping       ← `Zeta5.AppendixB.eq_5_16_5_18`
  (5.21)  `limsup K^{-2}log m_{K,M} ≤ A_M`     ← `eq_5_21_of_prop_5_2` (Asymptotics.lean)
  Prop. 6.3  (6.16), the real bound            ← `Zeta5.RealBound.prop_6_3`
  (7.1)   the combination of (5.21) and (6.16) ← `eq_7_1_of` (Asymptotics.lean)
  existence of the allocation (4.4)            ← `Zeta5.exists_innerAlloc_of_inner`
  Theorem 2.1, Theorem 1.1, (2.7), (2.8)       ← proved below and in `Skeleton.lean`

Exactly ONE of those proofs still bottoms out in a
`sorry`, and it is the whole of what Theorem 1.1 still assumes beyond `Zeta5/Axioms.lean`:

  `Zeta5.RealBound.eq_6_14`                 (6.14), the logarithmic-energy bound

Four further steps, `sorry`s until 2026-09-23, are now PROVED, statements unchanged:

  `Zeta5.CrudeBound.crude_entry_bound`      Lemma 3.3 at the `h²` entries of (3.11)
                                            ← `Zeta5/Lemma33.lean`
  `Zeta5.Section3.entry_bounds_4_2_4_3`     the §4.1 basis (4.5) and the bounds (4.2)/(4.3)
                                            ← `Zeta5/InnerTate.lean`, `InnerGeneral.lean`,
                                              `InnerEntries.lean`
  `Zeta5.outer_local_analysis`              the §4.2 local data (4.10)–(4.12)
                                            ← `Zeta5/OuterBasis.lean`
  `Zeta5.PrimeSum.eq_5_7_uniformity`        (5.7) and the two §5.2 displays
                                            ← `Zeta5/Uniformity.lean`

with the shared unimodularity lemma `Zeta5.HermiteBasis.det_coeffMatrix_unimodular`
(`Zeta5/HermiteBasis.lean`, `HermiteBasisCore.lean`) used by both local analyses.

`Zeta5/Audit.lean` recomputes that list from the environment on every build
(`#assumption_report Zeta5.zeta5_irrational`) and also checks that no `sorry` in the project
is an orphan — i.e. that the list is complete.

IMPORT DISCIPLINE.  A file that proves one of the statements below must NOT import this
file, or the import graph cycles.  `Arithmetic.lean` used to import it and no longer does;
`Section3.lean` (which proves Prop. 4.1) imports `LocalFunctional.lean` (which imports
`Arithmetic.lean`) and `InnerEntries.lean`, and this file imports `Section3.lean`.
-/
import Zeta5.Skeleton
import Zeta5.Counting
import Zeta5.Asymptotics
import Zeta5.Functional
import Zeta5.Section41
import Zeta5.Normalization
import Zeta5.Positivity
import Zeta5.Section3
import Zeta5.CrudeBound
import Zeta5.OuterRange
import Zeta5.PrimeSum
import Zeta5.AppendixB
import Zeta5.RealBound

namespace Zeta5

open Polynomial Finset

noncomputable section

/-! ## §2.4: Proposition 2.2 -/

/-- **Proposition 2.2**, (2.10) (p. 5).  For every rational function `R` in the domain of `μ_X`,
`μ_{ζ(5)}(R) = ∫_0^∞ R(y²) w(y) dy` with `w(y) = (2π)⁴y⁵ ∑_{ℓ≥1} ℓ⁴ e^{-2πℓy}/12`.

The domain of `μ_X` is realised here by `muOver n A = μ_X(A(t)/D_tail(t))`, which covers every
rational function occurring in (2.4).

**PROVED** in `Zeta5/Positivity.lean`: the series for `w` and its convergence, the
interchange of `∑` and `∫`, the moment identity `∫_0^∞ y^{2e}w = μ(t^e)` (via Mathlib's
`hasSum_zeta_nat` for Euler's formula), the pole values including both correction terms
`−1/4 + 1/(2j)`, integrability throughout, and the ℚ-linearity of `μ_X` through polynomial
division and simple partial fractions.  The single external input is Hermite's formula for
the Hurwitz zeta function, `Zeta5.Axioms.hermite_pole_integral`. -/
theorem prop_2_2_moment (n : ℕ) (A : ℚ[X]) :
    evalZeta5 (muOver n A)
      = ∫ y in Set.Ioi (0 : ℝ),
          (Polynomial.aeval (y ^ 2 : ℝ) A / Polynomial.aeval (y ^ 2 : ℝ) (Dtail n)) * wt y :=
  Zeta5.Positivity.prop_2_2_moment n A

/-- **Proposition 2.2**, the "Hence" clause (p. 5): `G_K(ζ(5))` is positive definite.

The paper derives it from (2.10) by the displayed computation
`∫_0^∞ D_N(y²)⁶q(y²)²/D_K(y²) · w(y) dy > 0` for `0 ≠ q` of degree `< h`.

**PROVED** in `Zeta5/Positivity.lean`: the matrix is real symmetric because it is
Hankel; the quadratic form at `x ≠ 0` is that integral with `q = ∑ x_i X^i ≠ 0`; the integrand
is `≥ 0` on `(0,∞)` and vanishes only on the finite root set of `y ↦ q(y²)`, so the integral
is strictly positive. -/
theorem prop_2_2 (n : ℕ) : Matrix.PosDef ((G n).map evalZeta5) :=
  Zeta5.Positivity.prop_2_2 n

/-- Consequence of Proposition 2.2: `Δ_K(ζ(5)) > 0`. -/
theorem delta_pos (n : ℕ) : 0 < evalZeta5 (Delta n) := by
  have hdet : 0 < ((G n).map evalZeta5).det := (prop_2_2 n).det_pos
  have hmap : evalZeta5 (Delta n) = ((G n).map evalZeta5).det := by
    rw [Delta, evalZeta5]
    exact RingHom.map_det evalZeta5Hom (G n)
  rw [hmap]
  exact hdet

/-- `F_K(ζ(5)) > 0` (this is the first assertion of (6.16)). -/
theorem F_pos (n : ℕ) : 0 < evalZeta5 (F n) := by
  rw [F, evalZeta5_mul, evalZeta5_C]
  exact mul_pos (by exact_mod_cast S_pos n) (delta_pos n)

/-- `Q_{K,M}(ζ(5)) > 0`: the positivity claim of Theorem 2.1. -/
theorem Q_pos (n M : ℕ) (Alloc : InnerAllocFamily n M) :
    0 < evalZeta5 (Q n M Alloc) := by
  rw [Q, evalZeta5_mul, evalZeta5_C]
  exact mul_pos (by exact_mod_cast mKM_pos n M Alloc) (F_pos n)

/-! ## §2.3: the degree, (2.9) -/

/-- `D_N(-j²) ≠ 0` for `j > N`: the poles of `D_tail` are not roots of `D_N`. -/
lemma D_eval_ne_zero (m j : ℕ) (hj : m < j) : (D m).eval (-((j : ℚ)) ^ 2) ≠ 0 := by
  rw [D, Polynomial.eval_prod]
  refine Finset.prod_ne_zero_iff.2 fun i hi => ?_
  simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
  have hi' : i ≤ m := (Finset.mem_Icc.1 hi).2
  have hij : (i : ℚ) < (j : ℚ) := by exact_mod_cast lt_of_le_of_lt hi' hj
  have hi0 : (0 : ℚ) ≤ (i : ℚ) := by positivity
  intro hcon
  nlinarith [hcon]

/-- **(2.9)** (p. 4).  `[X^h] Δ_K(X) = (-1)^{h(h-1)/2} ∏_{j=N+1}^{K} j⁴ D_N(-j²)⁵`.

This is the exact leading coefficient, obtained from
`[X]G_K = V diag(j⁴D_N(-j²)⁵/D'_tail(-j²)) Vᵀ` and the Vandermonde identity (§2.3). -/
theorem eq_2_9 (n : ℕ) :
    (Delta n).coeff (h n)
      = (-1) ^ (h n * (h n - 1) / 2) *
          ∏ j ∈ Ioc (N n) (K n), ((j : ℚ) ^ 4 * ((D (N n)).eval (-((j : ℚ)) ^ 2)) ^ 5) :=
  Zeta5.Functional.eq_2_9 n

/-- (2.9) is nonzero, as the paper states (`≠ 0` at the end of (2.9)). -/
theorem eq_2_9_ne_zero (n : ℕ) : (Delta n).coeff (h n) ≠ 0 := by
  rw [eq_2_9 n]
  refine mul_ne_zero (by positivity) (Finset.prod_ne_zero_iff.2 fun j hj => ?_)
  have hjN : N n < j := (Finset.mem_Ioc.1 hj).1
  have hj0 : j ≠ 0 := by omega
  have hjQ : ((j : ℚ)) ≠ 0 := Nat.cast_ne_zero.2 hj0
  exact mul_ne_zero (pow_ne_zero _ hjQ) (pow_ne_zero _ (D_eval_ne_zero (N n) j hjN))

/-- "`deg Δ_K = h` exactly" (p. 4), from (2.9) and `Delta_natDegree_le`. -/
theorem Delta_natDegree (n : ℕ) : (Delta n).natDegree = h n :=
  le_antisymm (Delta_natDegree_le n) (Polynomial.le_natDegree_of_ne_zero (eq_2_9_ne_zero n))

/-- The degree claim of Theorem 2.1: `deg Q_{K,M} = h`. -/
theorem Q_natDegree (n M : ℕ) (Alloc : InnerAllocFamily n M) :
    (Q n M Alloc).natDegree = h n := by
  have hm : mKM n M Alloc ≠ 0 := ne_of_gt (mKM_pos n M Alloc)
  have hs : S n ≠ 0 := ne_of_gt (S_pos n)
  rw [Q, F, ← mul_assoc, ← map_mul, Polynomial.natDegree_C_mul (mul_ne_zero hm hs)]
  exact Delta_natDegree n

/-! ## §4: the local determinant estimates -/

/-- **Proposition 4.1** (p. 11).  Under (4.1) — `K ∈ 40ℤ_{>0}`, `K ≥ 200M²`,
`K/M < p ≤ K/3` — one has `v_p^G(Δ_K) ≥ γ_p^in`, for any allocation satisfying (4.4).

This is the one substantial argument of the paper that the audit could read but not
cross-check against a computed determinant, because (4.1) forces `p > 8000` and a matrix
of size `≥ 296000`.  It is the primary target of this formalisation.

The one step of its proof that the audit found unproved in the paper — `b_a ≤ 6αx + 3`,
p. 10, and the nonnegativity of the `L_a` that it is used for — is proved, with no `sorry`,
as `Zeta5.ell_lt` and `Zeta5.InnerAlloc.L_nonneg` in `Counting.lean`.

*No longer a `sorry`* (since 2026-09-22).  It is `Zeta5.Section3.prop_4_1`, which derives
it from the entry bound and the unimodularity of the basis (4.5) —
`Zeta5.Section3.entry_bounds_4_2_4_3`, formerly a `sorry`, PROVED (2026-09-23) in
`Zeta5/InnerEntries.lean` — by the sorry-free
`Zeta5.prop_4_1_of_entry_bounds`, `Zeta5.lemma_4_2` and `Zeta5.InnerAlloc.sum_rowW`. -/
theorem prop_4_1 (n M p : ℕ) (hp : IsInnerPrime n M p) (A : InnerAlloc n M p) :
    vGAtLeast p (Delta n) A.gammaIn :=
  Zeta5.Section3.prop_4_1 n M p hp A

/-- **Proposition 4.3, first assertion** (p. 13).  Under (4.9) — `p ≥ 7`, `p ≤ K < 3p`,
`p² > 2K`, `2N < p`, `5N ≤ 2p - 2` — one has `v_p^G(Δ_K) ≥ γ_p^out`.

*No longer a `sorry`* (since 2026-09-22): it is `Zeta5.Outer.prop_4_3`, which derives it
from the §4.2 local analysis (`Zeta5.outer_local_analysis`, formerly a `sorry`, PROVED
(2026-09-23) in `Zeta5/OuterBasis.lean`) together with the rank bound (4.10),
weights (4.12), p. 13 table and assembly (4.14) of `Zeta5/OuterRange.lean`. -/
theorem prop_4_3 (n p : ℕ) (hp : p.Prime) (h7 : 7 ≤ p) (hpK : p ≤ K n)
    (hK3p : K n < 3 * p) (hp2 : 2 * K n < p ^ 2) (hN : 2 * N n < p)
    (hN5 : 5 * N n ≤ 2 * p - 2) :
    vGAtLeast p (Delta n) (gammaOut n p) :=
  Zeta5.Outer.prop_4_3 n p hp h7 hpK hK3p hp2 hN hN5

/-- **Proposition 4.3, second assertion** (p. 13).  For `p > K`, `v_p^G(Δ_K) ≥ 0`.

*No longer a `sorry`* (since 2026-09-22): it is `Zeta5.Outer.prop_4_3_large`. -/
theorem prop_4_3_large (n p : ℕ) (hp : p.Prime) (hpK : K n < p) :
    vGAtLeast p (Delta n) 0 :=
  Zeta5.Outer.prop_4_3_large n p hp hpK

/-! ## §5: integrality and the arithmetic constant -/

/-- **Proposition 5.1** (p. 14).  `Q_{K,M} = m_{K,M} F_K` belongs to `ℤ[X]`.

*No longer a `sorry`.*  This is the paper's own proof, carried out prime by prime in
`Zeta5.prop_5_1_of` (`Normalization.lean`) and applied here to its four inputs: (3.12) for
`pM ≤ K`, Proposition 4.1 for the inner range, and the two assertions of Proposition 4.3 for
the outer range and for `p > K` (which also covers `p > 2h`, where `v_p(S_K) = 0`).

This is what makes §§3–4 load-bearing: `eq_3_12`, `prop_4_1`, `prop_4_3` and `prop_4_3_large`
are now in the dependency cone of `Zeta5.zeta5_irrational`. -/
theorem prop_5_1 (n M : ℕ) (hM : 40 ≤ M) (hK : 200 * M ^ 2 ≤ K n)
    (Alloc : InnerAllocFamily n M) :
    ∃ P : Polynomial ℤ, P.map (Int.castRingHom ℚ) = Q n M Alloc :=
  prop_5_1_of n M hM hK Alloc (fun p hp => eq_3_12 n p hp)
    (fun p hpin A => prop_4_1 n M p hpin A)
    (fun p hp h7 hpK hK3p hp2 hN hN5 => prop_4_3 n p hp h7 hpK hK3p hp2 hN hN5)
    (fun p hp hpK => prop_4_3_large n p hp hpK)

/-- **Proposition 5.2**, (5.11) (p. 15).  For each fixed integer `M ≥ 40`,

`limsup_{K→∞, 40|K} K^{-2} log m_{K,M} ≤ I_out + 6λ/M + ∫_3^M R(x) x^{-3} dx`.

Stated in `ε`–`n₀` form with `K = 40n` (equivalent to the printed `limsup ≤ …`, since
`limsup a_K ≤ c` iff for every `ε > 0` all but finitely many `a_K` are `≤ c + ε`).  Note the
hypothesis is `M ≥ 40`, not `40 | M`: the divisibility is needed only later, in (5.17) and
hence (5.21).

*No longer a `sorry`*: it is `Zeta5.PrimeSum.prop_5_2`.  The paper's proof (p. 15) is carried
out there: `log m_{K,M} = Σ_{p≤2h}(−L_p)log p` is split along the three branches of (5.1);
(3.12) contributes `O(K^{3/2}log K) = o(K²)` for `p ≤ √(5K)`; the logarithmic factor
`⌊log_p 5K⌋` is exactly `1` for `√(5K) < p ≤ K/M`, where the prime number theorem gives the
contribution `6λK²/M + o(K²)`; and for a bounded piecewise continuous `f` on `[3,M]`, partial
summation and the prime number theorem give
`K^{-2}∑_{K/M<p≤K/3} p f(K/p) log p → ∫_3^M f(x)x^{-3}dx`, applied with `f = R` via (5.7),
the same argument in `y = p/K` giving (5.10) for the outer range.

`PrimeSum.lean` proves all of that.  It rests on

*  the **prime number theorem**, `Zeta5.Axioms.pnt_prime_riemann_sum`, in the
   partial-summation form the proof consumes — allowed by the ground rules of this
   formalization (README, "Ground rules"), and the only
   external input of Proposition 5.2; and
*  `Zeta5.PrimeSum.eq_5_7_uniformity`, which is **(5.7)** together with the two
   displays of §5.2 for the outer range — i.e. exactly the three assertions §5 makes with an
   informal justification rather than a proof, with the `O_M(1)` constants now quantified
   *outside* `K` and `p`, which is the uniformity the audit singled out as the paper's
   weakest point.  Formerly a `sorry` (never an axiom, being *Fauzan's* claim); PROVED
   (2026-09-23), with the explicit constant `C = 400 M²`, in
   `Zeta5/Uniformity.lean`.  The p. 14 sentence "these functions are bounded and piecewise
   polynomial on each compact subinterval of `[3,∞)`" is **not** assumed: it is proved, as
   `Zeta5.PrimeSum.RR_reg`. -/
theorem prop_5_2 (M : ℕ) (hM : 40 ≤ M) (Alloc : ∀ n, InnerAllocFamily n M)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      Real.log (mKM n M (Alloc n))
        ≤ ((Iout : ℝ) + 6 * (lam : ℝ) / (M : ℝ)
            + (∫ x in (3 : ℝ)..(M : ℝ), RR x / x ^ 3) + ε) * (K n : ℝ) ^ 2 :=
  PrimeSum.prop_5_2 M hM Alloc ε hε

/-- **(5.16)–(5.18)** (pp. 16–17).  For `M ∈ 40ℤ_{>0}`, the constant produced by
Proposition 5.2 is at most `A_M`:

`I_out + 6λ/M + ∫_3^M R(x) x^{-3} dx ≤ A_M`.

This is the constant-bookkeeping half of the passage from (5.11) to (5.21).  Writing
`∫_3^M = ∫_3^{20} + ∫_{20}^∞ - ∫_M^∞`, the paper supplies (5.18) for `∫_3^{20}` (exact),
(5.16) for `∫_{20}^∞` (`≤ -2689/48000`) and (5.17) for `∫_M^∞`
(`≥ -λ/M + (2923/240 - 1/4)/M² - 32/M³`, and this is where `40 | M` is used, via
`𝒫(M) = 𝒞(M) = 0`).  Adding them gives exactly `A_M` as defined in (5.20).  `Zeta5.Astar_eq` in `Basic.lean` is the exact rational identity
`A_* = I_out + ∫_3^{20} + (-2689/48000)` that sits behind it, and it is proved.

Split off from `eq_5_21` so that `Zeta5.prop_5_2` is actually *used*:
before the split, (5.21) was a `sorry` of its own and Proposition 5.2 was an orphan in the
dependency graph.

*No longer a `sorry`* (since 2026-09-22): it is `Zeta5.AppendixB.eq_5_16_5_18`, which
proves the whole of Appendix B — (5.8)–(5.10) and `I_out`, the 143 exact pieces of (B.2),
(5.12)–(5.13), the seventeen rows of Table 3 and (5.18) — from Basic.lean's definitions,
and, since 2026-09-23, on no `sorry` at all: its former residue
`Zeta5.AppendixB.eq_5_16_5_17` (the tail integrals) is proved in `Zeta5/Tail.lean`. -/
theorem eq_5_16_5_18 (M : ℕ) (hM : 40 ∣ M) (hM0 : 0 < M) :
    (Iout : ℝ) + 6 * (lam : ℝ) / (M : ℝ)
      + (∫ x in (3 : ℝ)..(M : ℝ), RR x / x ^ 3) ≤ (AM M : ℝ) :=
  Zeta5.AppendixB.eq_5_16_5_18 M hM hM0

/-- **(5.21)** (p. 17): `limsup_{K→∞, 40|K} K^{-2} log m_{K,M} ≤ A_M` for `M ∈ 40ℤ_{>0}`.

It follows from Proposition 5.2 together with (5.16)–(5.18); `Astar_eq` in `Basic.lean` is the
exact rational bookkeeping `A_* = I_out + ∫_3^{20} + (-2689/48000)` behind it.

The hypothesis is `40 ∣ M` with `M > 0`, exactly as printed (`M ∈ 40ℤ_{>0}`): (5.17), which
is what produces the `1/M`, `1/M²`, `1/M³` terms of `A_M`, uses `𝒫(M) = 𝒞(M) = 0`, which the
paper establishes only for `40 | M`.  (An earlier version of this file stated it for all
`M ≥ 40`; that is stronger than anything the paper proves.) -/
theorem eq_5_21 (M : ℕ) (hM : 40 ∣ M) (hM0 : 0 < M) (Alloc : ∀ n, InnerAllocFamily n M)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      Real.log (mKM n M (Alloc n)) ≤ ((AM M : ℝ) + ε) * (K n : ℝ) ^ 2 :=
  eq_5_21_of_prop_5_2 M Alloc
    (fun δ hδ => prop_5_2 M (Nat.le_of_dvd hM0 hM) Alloc δ hδ)
    (eq_5_16_5_18 M hM hM0) ε hε

/-! ## §6: the real bound -/

/-- **Proposition 6.3**, (6.16) (p. 20).  For every `K ∈ 40ℤ_{>0}`,
`0 < F_K(ζ(5))` and `log F_K(ζ(5)) ≤ U K² + 24 K log K + 200 K`, with
`U = -2733991/2000000`.

(The first assertion is `F_pos`, proved above from Proposition 2.2.)

*No longer a `sorry`* (since 2026-09-22): it is `Zeta5.RealBound.prop_6_3`, fed with
`Δ_K(ζ(5)) > 0` (`delta_pos`, from Proposition 2.2 — the paper's own hypothesis for it).
`RealBound.lean` proves (6.15) and the passage (6.14) ⇒ (6.16) outright, and rests on the
single remaining `sorry` `Zeta5.RealBound.eq_6_14`. -/
theorem prop_6_3 (n : ℕ) (hn : 0 < n) :
    Real.log (evalZeta5 (F n))
      ≤ (Ubar : ℝ) * (K n : ℝ) ^ 2 + 24 * (K n : ℝ) * Real.log (K n : ℝ)
        + 200 * (K n : ℝ) :=
  Zeta5.RealBound.prop_6_3 n hn (delta_pos n)

/-! ## §7: the combination -/

/-- **(7.1)** (p. 21).  `limsup_{K→∞, 40|K} K^{-2} log Q_{K,M}(ζ(5)) ≤ A_M + U`
for `M ∈ 40ℤ_{>0}`.

Stated in `ε`–`n₀` form with `K = 40n`, so `K² = 1600 n²`.  It follows from `eq_5_21`
and `prop_6_3` because `24 K log K + 200 K = o(K²)`; that last step is elementary
analysis, proved in `Asymptotics.lean` (`eq_7_1_of`).  Not a `sorry`. -/
theorem eq_7_1 (M : ℕ) (hM : 40 ∣ M) (hM0 : 0 < M) (Alloc : ∀ n, InnerAllocFamily n M)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      Real.log (evalZeta5 (Q n M (Alloc n)))
        ≤ ((AM M : ℝ) + (Ubar : ℝ) + ε) * (1600 * (n : ℝ) ^ 2) :=
  eq_7_1_of M Alloc (fun δ hδ => eq_5_21 M hM hM0 Alloc δ hδ) (fun n hn => prop_6_3 n hn)
    (fun n => F_pos n) ε hε

/-- **Existence of the allocation (4.4)** (p. 10).  "Define integers `T, E` by
`mT + E = h - L_0 + 3(N - m_N)`, `0 ≤ E < m`.  Give `ε_a = 1` to the first `E` classes in
decreasing order of `ℓ_K(a)`.  Ties may be ordered arbitrarily."

A finite construction — Euclidean division by `m = (p-1)/2 > 0` (`IsInnerPrime.mHalf_pos`)
followed by a sort of `{1,…,m}` by `ℓ_K` — which the paper performs in one sentence. -/
theorem exists_innerAlloc (n M p : ℕ) (hp : IsInnerPrime n M p) :
    Nonempty (InnerAlloc n M p) :=
  exists_innerAlloc_of_inner hp

/-! ## Theorem 2.1, assembled

Everything below is proved from the statements above; it introduces no new `sorry`. -/

/-- **Theorem 2.1, first sentence** (p. 4), in the paper's generality: for every `M ≥ 40` and
every `K = 40n` with `K ≥ 200M²`, the polynomial `Q_{K,M}` belongs to `ℤ[X]`, has degree `h`,
and satisfies `Q_{K,M}(ζ(5)) > 0`. -/
theorem theorem_2_1_integral_degree_pos (n M : ℕ) (hM : 40 ≤ M) (hK : 200 * M ^ 2 ≤ K n)
    (Alloc : InnerAllocFamily n M) :
    (∃ P : Polynomial ℤ, P.map (Int.castRingHom ℚ) = Q n M Alloc)
      ∧ (Q n M Alloc).natDegree = h n
      ∧ 0 < evalZeta5 (Q n M Alloc) :=
  ⟨prop_5_1 n M hM hK Alloc, Q_natDegree n M Alloc, Q_pos n M Alloc⟩

/-- The decay statements (2.7) and (2.8) come from (7.1) and the corresponding line of (7.2).

`c` is the exponent constant (`139/5` for (2.7), `7907/100` for (2.8)); the hypothesis is
exactly the inequality of (7.2). -/
theorem decay_of_margin (M : ℕ) (hM : 40 ∣ M) (hM0 : 0 < M)
    (Alloc : ∀ n, InnerAllocFamily n M) (c : ℚ) (hc : c < -1600 * (AM M + Ubar)) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      evalZeta5 (Q n M (Alloc n)) < Real.exp (-(c : ℝ) * (n : ℝ) ^ 2) := by
  set b : ℝ := (AM M : ℝ) + (Ubar : ℝ) with hbdef
  have hb : 1600 * b < -(c : ℝ) := by
    have hr : ((c : ℚ) : ℝ) < ((-1600 * (AM M + Ubar) : ℚ) : ℝ) := by exact_mod_cast hc
    push_cast at hr
    rw [hbdef]
    linarith
  set ε : ℝ := (-(c : ℝ) - 1600 * b) / 3200 with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; linarith
  obtain ⟨n₁, hn₁⟩ := eq_7_1 M hM hM0 Alloc ε hεpos
  refine ⟨max n₁ 1, fun n hn => ?_⟩
  have hna : n₁ ≤ n := le_trans (le_max_left _ _) hn
  have hnb : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnb
  have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 := by nlinarith
  have hQpos : 0 < evalZeta5 (Q n M (Alloc n)) := Q_pos n M (Alloc n)
  have hlog := hn₁ n hna
  have hsum : (AM M : ℝ) + (Ubar : ℝ) + ε = b + ε := by rw [hbdef]
  rw [hsum] at hlog
  have hkey : (b + ε) * (1600 * (n : ℝ) ^ 2) < -(c : ℝ) * (n : ℝ) ^ 2 := by
    have h1 : 1600 * (b + ε) < -(c : ℝ) := by rw [hεdef]; linarith
    nlinarith
  have hlt := lt_of_le_of_lt hlog hkey
  calc evalZeta5 (Q n M (Alloc n))
      = Real.exp (Real.log (evalZeta5 (Q n M (Alloc n)))) := (Real.exp_log hQpos).symm
    _ < Real.exp (-(c : ℝ) * (n : ℝ) ^ 2) := Real.exp_lt_exp.2 hlt

/-- **(2.7)**: `Q_{40n,200}(ζ(5)) < exp(-139 n²/5)` for all large `n`. -/
theorem decay_2_7 (Alloc : ∀ n, InnerAllocFamily n 200) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      evalZeta5 (Q n 200 (Alloc n)) < Real.exp (-(139 / 5 : ℝ) * (n : ℝ) ^ 2) := by
  have h := decay_of_margin 200 (by norm_num) (by norm_num) Alloc (139 / 5) (by
    have := eq_7_2_M200; linarith)
  simpa using h

/-- **(2.8)**: `Q_{40n,100000}(ζ(5)) < exp(-7907 n²/100)` for all large `n`.
Not needed for Theorem 1.1; it is what Appendix C uses for Corollary 1.2. -/
theorem decay_2_8 (Alloc : ∀ n, InnerAllocFamily n 100000) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      evalZeta5 (Q n 100000 (Alloc n)) < Real.exp (-(7907 / 100 : ℝ) * (n : ℝ) ^ 2) := by
  have h := decay_of_margin 100000 (by norm_num) (by norm_num) Alloc (7907 / 100) (by
    have := eq_7_2_M100000; linarith)
  simpa using h

/-- **Theorem 2.1** (p. 4) at `M = 200`, assembled from Propositions 5.1, 2.2, (2.9)
and (2.7).  This is the paper's "Proof of Theorem 2.1" on p. 21. -/
theorem theorem_2_1 (Alloc : ∀ n, InnerAllocFamily n 200) : Theorem_2_1 Alloc := by
  obtain ⟨n₁, hn₁⟩ := decay_2_7 Alloc
  refine ⟨max n₁ 200000, fun n hn => ?_⟩
  have hna : n₁ ≤ n := le_trans (le_max_left _ _) hn
  have hnb : 200000 ≤ n := le_trans (le_max_right _ _) hn
  have hK : 200 * 200 ^ 2 ≤ K n := by simp only [K]; omega
  exact ⟨prop_5_1 n 200 (by norm_num) hK (Alloc n), Q_natDegree n 200 (Alloc n),
    Q_pos n 200 (Alloc n), hn₁ n hna⟩

/-- A choice of allocations (4.4) at `M = 200`, from `exists_innerAlloc`. -/
def stdAlloc : ∀ n, InnerAllocFamily n 200 :=
  fun n p hp => (exists_innerAlloc n 200 p hp).some

/-- **Theorem 1.1**: `ζ(5)` is irrational.

Depends exactly on the one `sorry` listed at the top of this file (`RealBound.eq_6_14`) and
the two axioms of `Zeta5/Axioms.lean`; `#print axioms` shows
`sorryAx`.  The deduction from Theorem 2.1 (`Zeta5.theorem_1_1` in `Skeleton.lean`) and
the assembly of Theorem 2.1 above are complete. -/
theorem zeta5_irrational : Irrational zeta5 :=
  theorem_1_1 stdAlloc (theorem_2_1 stdAlloc)

end

end Zeta5
