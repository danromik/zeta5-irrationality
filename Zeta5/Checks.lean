/-
Zeta5/Checks.lean

KNOWN-ANSWER CONTROLS for the definitions in `Zeta5/Basic.lean`.

A formalisation is only as good as its definitions: a `sorry`-free proof of a mistranscribed
statement is worthless.  Every control below is a fact computed by hand from the paper and
then re-derived by Lean from the definition alone.  This file contains no `sorry`.
-/
import Zeta5.Counting
import Zeta5.Skeleton
import Zeta5.Interface

namespace Zeta5.Checks

open Polynomial Finset Zeta5

/-! ## (2.1): the parameters -/

example : K 1 = 40 := rfl
example : N 1 = 3 := rfl
example : h 1 = 37 := rfl
example : h 1 = K 1 - N 1 := rfl
example : alpha = 3 / 40 := rfl
example : lam = 37 / 40 := rfl
example : Hcst = 1 + 2 * alpha := by norm_num [Hcst, alpha]
/-- `λ = 1 - α`, and `H = λ + 3α`: the two relations §5 uses. -/
example : lam + alpha = 1 := by norm_num [lam, alpha]

/-! ## §2.1: `D_m` and `H^{(5)}_j` -/

/-- `D_2(t) = (t+1)(t+4) = t² + 5t + 4`: pinned by its degree and three values. -/
example : (D 2).natDegree = 2 := D_natDegree 2
example : (D 2).eval 0 = 4 := by norm_num [D, Finset.prod_Icc_succ_top]
example : (D 2).eval 1 = 10 := by norm_num [D, Finset.prod_Icc_succ_top]
example : (D 2).eval (-1) = 0 := by norm_num [D, Finset.prod_Icc_succ_top]

/-- `D_3(-1) = 0`: the roots of `D_m` are the `-j²`, `1 ≤ j ≤ m`. -/
example : (D 3).eval (-1) = 0 := by
  simp [D, Finset.prod_Icc_succ_top]

/-- `D_3(-9) = 0` (the pole `j = 3`). -/
example : (D 3).eval (-9) = 0 := by
  norm_num [D, Finset.prod_Icc_succ_top]

/-- `D_3(1) = 2 · 5 · 10 = 100`. -/
example : (D 3).eval 1 = 100 := by
  norm_num [D, Finset.prod_Icc_succ_top]

/-- `H^{(5)}_2 = 1 + 1/32 = 33/32`. -/
example : H5 2 = 33 / 32 := by
  norm_num [H5, Finset.sum_Icc_succ_top]

/-- `H^{(5)}_3 = 33/32 + 1/243 = 8051/7776`. -/
example : H5 3 = 8051 / 7776 := by
  norm_num [H5, Finset.sum_Icc_succ_top]

/-! ## (2.3): the pole values

`μ_X(1/(t+j²)) = j⁴(X - H^{(5)}_j) - 1/4 + 1/(2j)`.
At `j = 1`: `X - 1 - 1/4 + 1/2 = X - 3/4`. -/
example : (muPole 1).eval 0 = -3 / 4 := by
  norm_num [muPole, H5, Finset.Icc_self]
example : (muPole 1).eval 1 = 1 / 4 := by
  norm_num [muPole, H5, Finset.Icc_self]

/-- At `j = 2`: `16(X - 33/32) - 1/4 + 1/4 = 16X - 33/2`. -/
example : (muPole 2).eval 0 = -33 / 2 := by
  norm_num [muPole, H5, Finset.sum_Icc_succ_top]
example : (muPole 2).eval 1 = -1 / 2 := by
  norm_num [muPole, H5, Finset.sum_Icc_succ_top]

/-- The `X`-dependence is affine, for every `j`. -/
example (j : ℕ) : (muPole j).natDegree ≤ 1 := muPole_degree_le j

/-! ## §2.3: the tail denominator

`D_tail = D_K / D_N`, i.e. `D_N · D_tail = D_K`. -/
example (n : ℕ) : D (N n) * Dtail n = D (K n) := D_mul_Dtail n

/-! ## §4, p. 10: the class counts `ℓ_A(a)` and `m_A`

`ℓ_A(a) = #{1 ≤ j ≤ A : j ≡ ±a (mod p)}`.

For `p = 5`, `A = 10`, `a = 1`: `j ∈ {1,4,6,9}`, so `ℓ = 4 = 2⌊10/5⌋`. -/
example : ell 5 10 1 = 4 := by decide

/-- `p = 5`, `A = 10`, `a = 2`: `j ∈ {2,3,7,8}`, so `ℓ = 4`. -/
example : ell 5 10 2 = 4 := by decide

/-- `p = 5`, `A = 12`, `a = 1`: `j ∈ {1,4,6,9,11}`, so `ℓ = 5 = 2⌊12/5⌋ + 1`
(`v = 12 mod 5 = 2 ≥ a = 1`, so the first indicator fires). -/
example : ell 5 12 1 = 5 := by decide

/-- `p = 5`, `A = 12`, `a = 2`: `j ∈ {2,3,7,8,12}`, so `ℓ = 5`. -/
example : ell 5 12 2 = 5 := by decide

/-- `m_A = ⌊A/p⌋`. -/
example : mFloor 5 12 = 2 := rfl

/-- The identity `ℓ_A(a) = 2 m_A + 1_{a ≤ v} + 1_{a ≥ p - v}` behind the repair of the
line after (4.4) in `Counting.lean`, at `p = 5`, `A = 12` (`v = 2`): for `a = 2` exactly
the *first* indicator fires (`a = 2 ≤ 2 = v`, while `a = 2 ≥ 3 = p - v` is false), giving
`4 + 1 = 5`. -/
example : ell 5 12 2 = 2 * mFloor 5 12 + 1 := by decide

/-! ## §4.1, p. 10: `L_0` and `m` -/

example : L0 200 = 810 := rfl
example : mHalf 8081 = 4040 := rfl

/-! ## §4.2, p. 13: the outer data at a sample prime

Take `n = 1`, so `K = 40`, `N = 3`, and `p = 17`.
`v = 40 mod 17 = 6`; `u = max(0, 3 + 6 - 17 + 1) = 0`; `t_p = min(3,6) + 0 = 3`;
`r_p = max(0, 40 + 12 - 34 + 2) = 20`.
Since `K = 40 ≥ 2p = 34`, the second branch of (4.14) applies:
`-7(40-17) + 3 + 36 + 15 - min(20, 17) = -161 + 54 - 17 = -124`. -/
example : vOut 1 17 = 6 := rfl
example : uOut 1 17 = 0 := by norm_num [uOut, vOut, N, K]
example : tOut 1 17 = 3 := by norm_num [tOut, uOut, vOut, N, K]
example : rOut 1 17 = 20 := by norm_num [rOut, N, K]
example : gammaOut 1 17 = -124 := by
  norm_num [gammaOut, rOut, tOut, uOut, vOut, N, K]

/-- For `p > K` the outer bound is `0` (§5, p. 13). -/
example : gammaOut 1 41 = 0 := by norm_num [gammaOut, K]

/-! ## (4.1): an inner prime forces `p > 200 M`

The repair of the line after (4.4) in `Counting.lean`, and the whole of §4.1, rest on this. -/
example (n M p : ℕ) (hp : IsInnerPrime n M p) : 200 * M < p := hp.gt_200M

example (n M p : ℕ) (hp : IsInnerPrime n M p) : 0 < mHalf p := hp.mHalf_pos

/-! ## (5.19)–(5.20), (6.4), (7.2): the two constants and the margin

`A_200 ≈ 1.3495876977` and `U = -1.3669955`, so `A_200 + U ≈ -0.0174078`,
and `-1600 (A_200 + U) ≈ 27.85 > 139/5 = 27.8`. -/
example : Ubar = -2733991 / 2000000 := rfl

/-- The audit's value `A_200 = 1.3495876977…`: check the first ten decimals. -/
example : (13495876977 : ℚ) / 10 ^ 10 < AM 200 ∧ AM 200 < (13495876978 : ℚ) / 10 ^ 10 := by
  constructor <;> norm_num [AM, Astar, lam]

/-- The audit's value `A_200 + U = -0.0174078…` (margin `1.29 %`). -/
example : (-174079 : ℚ) / 10 ^ 7 < AM 200 + Ubar ∧ AM 200 + Ubar < (-174078 : ℚ) / 10 ^ 7 := by
  constructor <;> norm_num [AM, Astar, Ubar, lam]

/-- (7.2) at `M = 200`, which is what Theorem 1.1 needs. -/
example : -1600 * (AM 200 + Ubar) > 139 / 5 := eq_7_2_M200

/-- (7.2) at `M = 100000`, which Corollary 1.2 needs. -/
example : -1600 * (AM 100000 + Ubar) > 7907 / 100 := eq_7_2_M100000

/-- The margin is genuinely tight: the printed exponent `139/5` in (2.7) is only
`0.05` below the true value `-1600(A_200 + U) = 27.85…`. -/
example : -1600 * (AM 200 + Ubar) < 2786 / 100 := by
  norm_num [AM, Astar, Ubar, lam]

/-! ## (2.5): positivity of `S_K` -/

example (n : ℕ) : 0 < S n := S_pos n

/-! ## (2.4): `deg Δ_K ≤ h`, from the affine entries -/

example (n : ℕ) : (Delta n).natDegree ≤ h n := Delta_natDegree_le n
example (n : ℕ) (i j : Fin (h n)) : (G n i j).natDegree ≤ 1 := G_natDegree_le n i j

/-! ## (5.10), (5.18), (5.16), (5.19): the bookkeeping of `A_*`

`A_* = I_out + ∫_3^{20}R/x³ + (-2689/48000)`: an exact identity between the four printed
rationals, and the reason (5.21) has the shape it has. -/

example : Astar = Iout + I320 + I20inf := Astar_eq
example : Iout = 127751 / 96000 := rfl
example : I320 = 322437603634266857629 / 7535670527041937280000 := rfl

/-! ## §4.1, p. 10: the inequality the paper asserts without proof

`ell_eq` and `ell_lt` of `Counting.lean`.  Controls computed by hand from the definition. -/

/-- `ell_eq` at `p = 5`, `A = 12`, `a = 1`: `⌊16/5⌋ + ⌊13/5⌋ = 3 + 2 = 5`. -/
example : ell 5 12 1 = (12 + 5 - 1) / 5 + (12 + 1) / 5 := by decide
example : ell 5 12 1 = 5 := by decide

/-- `p ℓ_A(a) < 2A + p` at `p = 5`, `A = 12`, `a = 1`: `25 < 29`. -/
example : 5 * ell 5 12 1 < 2 * 12 + 5 := by decide

/-- The tightest case reachable at small parameters: `p = 7`, `A = 4` (so `v = 4 ≥ (p+1)/2`),
`a = 3 = (p-1)/2`.  Then `ℓ = #{3,4} = 2` and `pℓ = 14 < 15 = 2A + p`: slack exactly `1`.
This is the case where *both* indicators of `ℓ = 2m_A + 1_{a≤v} + 1_{a≥p-v}` fire, i.e. the
case the paper's omitted argument has to handle. -/
example : ell 7 4 3 = 2 := by decide
example : 7 * ell 7 4 3 = 14 := by decide
example : 7 * ell 7 4 3 < 2 * 4 + 7 := by decide

/-- `p ∣ A`: `ℓ = 2⌊A/p⌋` and the slack in `b_a ≤ 6αx + 3` is exactly `3`
(here `p ℓ = 20`, `2A + p = 25`, and `3·20 = 60 < 75 = 6A + 3p`). -/
example : ell 5 10 1 = 4 := by decide
example : 3 * (5 * ell 5 10 1) + 15 = 6 * 10 + 3 * 5 := by decide

example (p A a : ℕ) (ha1 : 1 ≤ a) (ha2 : 2 * a < p) : p * ell p A a < 2 * A + p :=
  ell_lt p A a ha1 ha2

/-- **Two independent proofs of the same repair.**  `Counting.ell_lt` argues directly from
`ell_eq`; `Section41.ell_lt_caseSplit` argues from the closed form by the case split on
`v_A = A mod p` that the audit used on p. 10.  That the two theorems have the *same*
statement is checked here by Lean, not by eye. -/
example : @Zeta5.ell_lt = @Zeta5.ell_lt_caseSplit := rfl

/-- The closed form itself, `ℓ_A(a) = 2m_A + 1_{a ≤ v_A} + 1_{a ≥ p - v_A}`. -/
example (p A a : ℕ) (ha1 : 1 ≤ a) (ha2 : 2 * a < p) :
    ell p A a = 2 * mFloor p A + (if a ≤ A % p then 1 else 0)
      + (if p ≤ A % p + a then 1 else 0) :=
  ell_closed p A a ha1 ha2

/-- **The naive bound is attained** (so the sharp bound is not a triviality): at `p = 7`,
`A = 6`, `a = 1` one has `ℓ = 2⌊6/7⌋ + 2 = 2`. -/
example : ell 7 6 1 = 2 * mFloor 7 6 + 2 := ell_naive_attained

/-- **…and the naive bound cannot reach the target** on the complementary residues:
for `2 v_A ≤ p`, `2A + p ≤ p(2m_A + 2)`.  Together with the line above: no argument that
treats the classes `+a` and `-a` separately can prove the paper's inequality. -/
example (p A : ℕ) (hv : 2 * (A % p) ≤ p) : 2 * A + p ≤ p * (2 * mFloor p A + 2) :=
  naive_not_enough p A hv

/-! ## What is actually proved, with no `sorry`

`#print axioms` on the completed parts: these must show `propext, Classical.choice, Quot.sound`
and **not** `sorryAx`. -/

#print axioms Zeta5.theorem_1_1
#print axioms Zeta5.irrational_of_integerPolynomials
#print axioms Zeta5.ell_lt
#print axioms Zeta5.InnerAlloc.L_nonneg
#print axioms Zeta5.Delta_natDegree_le
#print axioms Zeta5.eq_7_2_M200
#print axioms Zeta5.Astar_eq

-- And, for contrast, the two statements that are still conditional: these DO show `sorryAx`,
-- and that is the honest state of the formalisation.
#print axioms Zeta5.theorem_2_1
#print axioms Zeta5.zeta5_irrational

end Zeta5.Checks
