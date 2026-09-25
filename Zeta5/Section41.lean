/-
Zeta5/Section41.lean

**§4.1 of the paper (pp. 10–11), the inner prime range.**

Reference: A. Fauzan, "ζ(5) is irrational", 17 September 2026.  Under (4.1), `p > 8000`,
so the matrix whose determinant Proposition 4.1 bounds has size `h ≥ 296000`.

CONTENTS.

(a) THE COUNTING FUNCTIONS `ℓ_A(a)` and `m_A = ⌊A/p⌋` of p. 10 and their closed form
    `ℓ_A(a) = 2 m_A + 1_{a ≤ v_A} + 1_{a ≥ p - v_A}`, `v_A = A mod p`.        — proved.

(b) THE INEQUALITY `b_a ≤ 6αx + 3`.  The paper asserts `b_a ≤ 6αx + 3` on p. 10 with no proof and a
    wrong attribution ("From (4.4)"; it is a statement about `ℓ_N`, not about (4.4)).  It is
    proved here by the case split on `v_N` (`ell_lt_caseSplit`, `bCoef_lt_real`), and the
    NECESSITY of that case split is machine-checked from both sides:
      * for `2 v_A > p` the naive bound `ℓ_A(a) ≤ 2m_A + 2` is ATTAINED
        (`ell_eq_naive_of_large_v`, `ell_naive_attained`);
      * for `2 v_A ≤ p` the naive bound is TOO WEAK — it gives only `p ℓ_A(a) ≤ 2A + 2p - 2v_A`
        and `2A + 2p - 2v_A ≥ 2A + p` (`naive_not_enough`).
    So on every residue one of the two obstacles occurs and the target `p ℓ_N(a) < 2N + p`
    can never be reached without looking at `v_N`.  In the paper's variables the naive bound
    gives only `b_a ≤ 6αx + 6`, whence `T - b_a > 2λx - 141/20`, which is `-3/2` at `x = 3`
    (`naive_chain`, `naive_bound_insufficient`): the dimensions would not be provably
    nonnegative and Proposition 4.1 would collapse.                           — proved.

(c) THE ALLOCATION (4.4): existence *and* uniqueness of `T, E` with `mT + E = h - L₀ +
    3(N - m_N)`, `0 ≤ E < m` (`exists_TE`, `unique_TE`), and the two bounds
    `2Hx - 21/20 < T < 2Hx` under (4.1) (`T_gt`, `T_lt`).  The full allocation of (4.4),
    including the extras `ε_a`, also exists (`exists_innerAlloc_of_inner`; this proves
    `Zeta5.exists_innerAlloc` of `Interface.lean`).                           — proved.

(d) NONNEGATIVITY of `L_a = T - b_a + ε_a` through the paper's chain
    `T - b_a > 2λx - 81/20 ≥ 3/2` for `x ≥ 3` (`T_sub_bCoef_gt`, `two_lam_bound`,
    `L_gt_three_halves`), and the dimension identity `L₀ + ∑_a L_a = h`
    (`dimension_identity`, resting on `∑_{a=1}^m ℓ_A(a) = A - m_A`, `sum_ell`).
                                                                              — proved.

(e) THE WEIGHTS (4.6), (4.7) and `γ_p^in` (4.8) are the definitions `InnerAlloc.w2`,
    `InnerAlloc.w2zero`, `InnerAlloc.gammaIn` of `Basic.lean` (carried as `2w`, since the
    weights are half-integers); `InnerAlloc.sum_rowW` checks that (4.8) really is the sum of
    the row weights over the rows of (4.5).  The basis (4.5) itself is `InnerAlloc.rowPoly`
    and the orders `ν_i(c)` are `InnerAlloc.nu` (`pow_nu_dvd_rowPoly` checks that `ν` is an
    order of vanishing).  The two degree bounds of p. 11,
    `ν_i(c) + ν_j(c) + 6ℓ_N(c) ≤ 2(T+1) < 23M/5 + 2` and
    `5 + 2ν_i(0) + 2ν_j(0) + 12 m_N ≤ 5 + 4L₀ + 12 m_N ≤ 169M/10 + 45`,
    and the fact that both are `≤ p + 1` when `p > 200M`.  Two of the weight comparisons of
    p. 11 are also proved: the ordinary-source one `Z_c - Z_a + 1 + (ℓ_K(a)-ℓ_K(c))/2 ≥ 0`
    (`weight_comparison`, resting on "the counts `ℓ_K` take two consecutive values",
    `ell_two_consecutive`, and on the field `hExtraOrder`), and the zero-source one
    `2L₀ + 6m_N - m_K + 1/2 ≥ 7M + 41/2` (`zero_source_bound`).               — proved.

(f) PROPOSITION 4.1 itself (`Prop_4_1`, the statement of `Zeta5.prop_4_1`).  Its proof on
    p. 11 has two halves:
      (i)  an ENTRY BOUND: in the unimodular basis (4.5), the `(u,v)` entry has Gauss
           valuation at least `w_u + w_v` — this is the local analysis of §3 (Lemmas 3.1,
           3.2, the distribution formula and the near/far pole bookkeeping); it is proved
           in `InnerEntries.lean` and enters `prop_4_1_of_entry_bounds` as a hypothesis;
      (ii) a REDUCTION: from the entry bound and the unimodularity of (4.5) the determinant
           bound `v_p^G(Δ_K) ≥ 2 ∑ w = γ_p^in` follows (`vGAtLeast_det`,
           `prop_4_1_of_entry_bounds`).                                       — proved.
    The reduction is the `L = 0` case of Lemma 4.2 (p. 12); the general case, with the
    rank-`r` correction `p^{-1}L` and the `min(r,z)` loss, is what §4.2 needs for
    Proposition 4.3.  (`Zeta5/Lemma42.lean` treats the general case; this file does not
    import it and proves the `L = 0` case directly.)
-/
import Zeta5.Counting

namespace Zeta5

open Polynomial Finset

noncomputable section

/-! # (a) The counting functions `ℓ_A(a)` and `m_A` (p. 10)

`ℓ_A(a) = #{1 ≤ j ≤ A : j ≡ a or -a (mod p)}` and `m_A = ⌊A/p⌋` are `Zeta5.ell` and
`Zeta5.mFloor` of `Basic.lean`.  `Counting.lean` already proves
`ℓ_A(a) = ⌊(A+p-a)/p⌋ + ⌊(A+a)/p⌋` (`ell_eq`); we turn that into the closed form in which
the case split of (b) is visible. -/

/-- `x / p ∈ {0,1}` when `x < 2p`. -/
private lemma div_eq_ite_of_lt_two_mul {p x : ℕ} (hp : 0 < p) (hx : x < 2 * p) :
    x / p = if p ≤ x then 1 else 0 := by
  split_ifs with hle
  · rw [Nat.div_eq_sub_div hp hle, Nat.div_eq_of_lt (show x - p < p by omega)]
  · exact Nat.div_eq_of_lt (by omega)

/-- **The closed form of `ℓ_A(a)`** (p. 10).  With `v_A = A mod p`,

`ℓ_A(a) = 2 m_A + 1_{a ≤ v_A} + 1_{a ≥ p - v_A}`

for `1 ≤ a` with `2a < p` (i.e. `1 ≤ a ≤ (p-1)/2` for odd `p`).  The second indicator is
written `p ≤ v_A + a`, which is `a ≥ p - v_A` without truncated subtraction. -/
theorem ell_closed (p A a : ℕ) (ha1 : 1 ≤ a) (ha2 : 2 * a < p) :
    ell p A a = 2 * mFloor p A
      + (if a ≤ A % p then 1 else 0) + (if p ≤ A % p + a then 1 else 0) := by
  have hp : 0 < p := by omega
  have hap : a < p := by omega
  have hv : A % p < p := Nat.mod_lt _ hp
  have hA : p * (A / p) + A % p = A := Nat.div_add_mod A p
  have h1 : (A + a) / p = A / p + (if p ≤ A % p + a then 1 else 0) := by
    have he : A + a = p * (A / p) + (A % p + a) := by omega
    rw [he, Nat.mul_add_div hp,
      div_eq_ite_of_lt_two_mul (x := A % p + a) hp (by omega)]
  have h2 : (A + p - a) / p = A / p + (if a ≤ A % p then 1 else 0) := by
    have he : A + p - a = p * (A / p) + (A % p + p - a) := by omega
    have hiff : (p ≤ A % p + p - a) = (a ≤ A % p) := by simp only [eq_iff_iff]; omega
    rw [he, Nat.mul_add_div hp,
      div_eq_ite_of_lt_two_mul (x := A % p + p - a) hp (by omega)]
    simp only [hiff]
  rw [ell_eq p A a ha1 ha2, h1, h2]
  simp only [mFloor]
  ring

/-- The naive bound: each of the two classes `±a` meets `[1,A]` in at most `m_A + 1` points,
so `ℓ_A(a) ≤ 2 m_A + 2`. -/
theorem ell_le_naive (p A a : ℕ) (ha1 : 1 ≤ a) (ha2 : 2 * a < p) :
    ell p A a ≤ 2 * mFloor p A + 2 := by
  rw [ell_closed p A a ha1 ha2]
  split_ifs <;> omega

/-- **The naive bound is attained**, so no bound better than `ℓ_A(a) ≤ 2m_A + 2` follows from
counting the two classes separately: `ℓ_6(1) = 2 = 2⌊6/7⌋ + 2` at `p = 7`. -/
theorem ell_naive_attained : ell 7 6 1 = 2 * mFloor 7 6 + 2 := by
  rw [ell_closed 7 6 1 (by norm_num) (by norm_num)]
  norm_num [mFloor]

/-- **Necessity of the case split, part 1.**  Whenever `v_A > p/2` — which is half of all
residues — the naive bound is attained at every class `a ≥ p - v_A`.  So it cannot be
sharpened to `2m_A + 1` for all `a`. -/
theorem ell_eq_naive_of_large_v {p A a : ℕ} (ha1 : 1 ≤ a) (ha2 : 2 * a < p)
    (hav : a ≤ A % p) (hpa : p ≤ A % p + a) : ell p A a = 2 * mFloor p A + 2 := by
  rw [ell_closed p A a ha1 ha2, ite_eq_left hav, ite_eq_left hpa]

/-- **Necessity of the case split, part 2.**  In the complementary range `2 v_A ≤ p` the
naive bound is *too weak to reach the target*: from `ℓ_A(a) ≤ 2m_A + 2` alone one gets only
`p ℓ_A(a) ≤ 2A + 2p - 2v_A`, and `2A + 2p - 2v_A ≥ 2A + p`.

Together with part 1 this says: on every residue `v_A` one of the two obstacles occurs, so
`p ℓ_A(a) < 2A + p` — the paper's `b_a ≤ 6αx + 3` — can never be obtained from the naive
bound; the case split on `v_A` is unavoidable. -/
theorem naive_not_enough (p A : ℕ) (hv : 2 * (A % p) ≤ p) :
    2 * A + p ≤ p * (2 * mFloor p A + 2) := by
  have hA : p * (A / p) + A % p = A := Nat.div_add_mod A p
  simp only [mFloor]
  have hexp : p * (2 * (A / p) + 2) = 2 * (p * (A / p)) + 2 * p := by ring
  rw [hexp]
  omega

/-- **"The counts `ℓ_K` take two consecutive values"** (p. 11).  For `1 ≤ a, a'` with
`2a < p`, `2a' < p` the values `ℓ_A(a)` differ by at most one.

Both indicators of `ell_closed` can fire only when `2 v_A > p`, and then the first one
always fires (since `a ≤ (p-1)/2 < v_A`); when `2 v_A < p` the second never fires.  So the
possible values are `{2m_A, 2m_A+1}` or `{2m_A+1, 2m_A+2}`, never all three. -/
theorem ell_two_consecutive (p A a a' : ℕ) (ha1 : 1 ≤ a) (ha2 : 2 * a < p)
    (ha1' : 1 ≤ a') (ha2' : 2 * a' < p) : ell p A a ≤ ell p A a' + 1 := by
  rw [ell_closed p A a ha1 ha2, ell_closed p A a' ha1' ha2']
  split_ifs <;> omega

/-! # (b) The gap: `b_a ≤ 6αx + 3` (p. 10)

The paper writes, immediately after (4.4),

    "From (4.4),   2Hx - 21/20 < T < 2Hx,   b_a ≤ 6αx + 3."

The second inequality does not follow from (4.4) — it is a statement about `ℓ_N` — and no
proof is given.  Since `x = K/p` and `αx = N/p`, it says `p · ℓ_N(a) ≤ 2N + p`.

`Counting.ell_lt` proves the strict form by a divisibility argument.  Here is the proof of
the audit, the explicit case split on `v_A = A mod p`. -/

/-- **`p · ℓ_A(a) < 2A + p`, by the case split on `v_A = A mod p`** (the audit's proof).

Case `2v_A < p` (i.e. `v_A ≤ (p-1)/2`): the indicator `a ≥ p - v_A` cannot fire, because it
would force `a ≥ p - v_A > p/2 > a`.  Only one extra point is possible, and it costs `p`,
which the term `2v_A` pays for since then `v_A ≥ a ≥ 1`.

Case `2v_A ≥ p`: both indicators may fire, costing `2p`, but the deficit `2v_A - p` absorbs
it: `a ≤ v_A` and `p ≤ v_A + a` with `2a < p` give `p < 2v_A`. -/
theorem ell_lt_caseSplit (p A a : ℕ) (ha1 : 1 ≤ a) (ha2 : 2 * a < p) :
    p * ell p A a < 2 * A + p := by
  have hp : 0 < p := by omega
  have hA : p * (A / p) + A % p = A := Nat.div_add_mod A p
  have hv : A % p < p := Nat.mod_lt _ hp
  rw [ell_closed p A a ha1 ha2, mFloor]
  -- the two indicators contribute at most `2v + p` after multiplication by `p`
  have key : p * ((if a ≤ A % p then 1 else 0) + (if p ≤ A % p + a then 1 else 0))
      < 2 * (A % p) + p := by
    by_cases hsmall : 2 * (A % p) < p
    · -- `v_A ≤ (p-1)/2`: the second indicator `a ≥ p - v_A` cannot fire, since it would
      -- force `a ≥ p - v_A > p/2 > a`; the single extra point is paid for by `2 v_A ≥ 2a`
      split_ifs with h1 h2 h2 <;> omega
    · -- `2 v_A ≥ p`: the deficit absorbs the second indicator
      split_ifs with h1 h2 h2 <;> omega
  have hexp : p * (2 * (A / p) + (if a ≤ A % p then 1 else 0)
        + (if p ≤ A % p + a then 1 else 0))
      = 2 * (p * (A / p))
        + p * ((if a ≤ A % p then 1 else 0) + (if p ≤ A % p + a then 1 else 0)) := by
    ring
  rw [hexp]
  have : 2 * (p * (A / p)) + (2 * (A % p) + p) = 2 * A + p := by omega
  omega

/-! ## `b_a = 3ℓ_N(a)` in the paper's real variable `x = K/p` -/

/-- `x = K/p`, the variable of p. 10 and of §5. -/
def xVal (n p : ℕ) : ℚ := (K n : ℚ) / (p : ℚ)

lemma xVal_pos {n M p : ℕ} (hp : IsInnerPrime n M p) : 0 < xVal n p := by
  have hp0 : (0 : ℚ) < (p : ℚ) := by exact_mod_cast hp.prime.pos
  have hK : 0 < K n := by
    have := hp.upper
    have := hp.prime.pos
    omega
  have : (0 : ℚ) < (K n : ℚ) := by exact_mod_cast hK
  exact div_pos this hp0

/-- `x ≥ 3`, i.e. `p ≤ K/3`, which is the right half of (4.1). -/
lemma three_le_xVal {n M p : ℕ} (hp : IsInnerPrime n M p) : 3 ≤ xVal n p := by
  have hp0 : (0 : ℚ) < (p : ℚ) := by exact_mod_cast hp.prime.pos
  have h3 : (3 : ℚ) * (p : ℚ) ≤ (K n : ℚ) := by exact_mod_cast hp.upper
  rw [xVal, le_div_iff₀ hp0]
  linarith

/-- `x < M`, i.e. `K/M < p`, which is the left half of (4.1). -/
lemma xVal_lt_M {n M p : ℕ} (hp : IsInnerPrime n M p) : xVal n p < (M : ℚ) := by
  have hp0 : (0 : ℚ) < (p : ℚ) := by exact_mod_cast hp.prime.pos
  have hl : (K n : ℚ) < (p : ℚ) * (M : ℚ) := by exact_mod_cast hp.lower
  rw [xVal, div_lt_iff₀ hp0]
  linarith

/-- `α x = N/p`, the identity behind "`b_a ≤ 6αx + 3` is `p ℓ_N(a) ≤ 2N + p`". -/
lemma alpha_xVal (n p : ℕ) : alpha * xVal n p = (N n : ℚ) / (p : ℚ) := by
  rw [alpha, xVal, K, N]
  push_cast
  ring

/-- **`b_a < 6αx + 3`** (p. 10, the asserted inequality), for `1 ≤ a` with `2a < p`.
Proved from `ell_lt_caseSplit`; `Counting.bCoef_lt` is the same inequality in integer form. -/
theorem bCoef_lt_real (n p a : ℕ) (hp0 : 0 < p) (ha1 : 1 ≤ a) (ha2 : 2 * a < p) :
    (bCoef n p a : ℚ) < 6 * alpha * xVal n p + 3 := by
  have hpQ : (0 : ℚ) < (p : ℚ) := by exact_mod_cast hp0
  have hint : p * ell p (N n) a < 2 * N n + p := ell_lt_caseSplit p (N n) a ha1 ha2
  have hQ : (p : ℚ) * (ell p (N n) a : ℚ) < 2 * (N n : ℚ) + (p : ℚ) := by exact_mod_cast hint
  have hell : (ell p (N n) a : ℚ) < 2 * ((N n : ℚ) / (p : ℚ)) + 1 := by
    rw [show 2 * ((N n : ℚ) / (p : ℚ)) + 1 = (2 * (N n : ℚ) + (p : ℚ)) / (p : ℚ) by
      field_simp]
    rw [lt_div_iff₀ hpQ]
    linarith
  have hb : (bCoef n p a : ℚ) = 3 * (ell p (N n) a : ℚ) := by
    rw [bCoef]; push_cast; ring
  rw [hb, show (6 : ℚ) * alpha * xVal n p = 6 * (alpha * xVal n p) by ring, alpha_xVal]
  linarith

/-! # (c) The allocation (4.4): existence, uniqueness, and `2Hx - 21/20 < T < 2Hx` -/

/-- The right-hand side of (4.4): `h - L₀ + 3(N - m_N)`. -/
def allocTarget (n M p : ℕ) : ℤ :=
  (h n : ℤ) - L0 M + 3 * ((N n : ℤ) - mFloor p (N n))

/-- **Existence in (4.4)**: for `m > 0` there are integers `T, E` with `mT + E =
h - L₀ + 3(N - m_N)` and `0 ≤ E < m`.  This is Euclidean division by `m = (p-1)/2`. -/
theorem exists_TE (n M p : ℕ) (hm : 0 < mHalf p) :
    ∃ (T : ℤ) (E : ℕ), (E : ℤ) < mHalf p ∧
      (mHalf p : ℤ) * T + E = allocTarget n M p := by
  have hm' : (0 : ℤ) < (mHalf p : ℤ) := by exact_mod_cast hm
  refine ⟨allocTarget n M p / (mHalf p : ℤ),
    (allocTarget n M p % (mHalf p : ℤ)).toNat, ?_, ?_⟩
  · rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))]
    exact Int.emod_lt_of_pos _ hm'
  · rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))]
    exact Int.mul_ediv_add_emod _ _

/-- **Uniqueness in (4.4)**: `T` and `E` are determined by `mT + E = target`, `0 ≤ E < m`. -/
theorem unique_TE {m : ℤ} (hm : 0 < m) {T T' : ℤ} {E E' : ℤ}
    (hE : 0 ≤ E) (hE' : 0 ≤ E') (hEm : E < m) (hEm' : E' < m)
    (heq : m * T + E = m * T' + E') : T = T' ∧ E = E' := by
  have hdvd : m * (T - T') = E' - E := by ring_nf; linarith
  have habs : |E' - E| < m := by
    rw [abs_lt]; constructor <;> linarith
  have hTT : T = T' := by
    by_contra hne
    have h1 : 1 ≤ |T - T'| := by
      rcases lt_trichotomy T T' with hlt | heq' | hgt
      · rw [abs_of_nonpos (by linarith)]; omega
      · exact absurd heq' hne
      · rw [abs_of_nonneg (by linarith)]; omega
    have : m ≤ |m * (T - T')| := by
      rw [abs_mul, abs_of_pos hm]
      nlinarith
    rw [hdvd] at this
    linarith
  refine ⟨hTT, ?_⟩
  rw [hTT] at heq
  linarith

/-! ### The two bounds on `T`

`2Hx - 21/20 < T < 2Hx`, "from (4.4)".  Both are consequences of (4.4) together with (4.1);
the second uses the paper's remark that `(2L₀ + 6m_N)/(p-1) < 1/20` follows from (4.1). -/

section TBounds

variable {n M p : ℕ}

/-- `2m + 1 = p`, `m ≥ 100M`, `40 m_N < 3M` and `23K = 20(h + 3N)`: the elementary
consequences of (4.1) that the bounds of §4.1 rest on. -/
lemma inner_facts (hp : IsInnerPrime n M p) :
    2 * mHalf p + 1 = p ∧ 100 * M ≤ mHalf p ∧ 40 * mFloor p (N n) < 3 * M ∧
      23 * K n = 20 * (h n + 3 * N n) := by
  have h2m := hp.two_mHalf
  have hgt := hp.gt_200M
  have hp0 : 0 < p := hp.prime.pos
  refine ⟨h2m, by omega, ?_, by simp only [K, h, N]; ring⟩
  -- `p · m_N ≤ N` and `40 N = 3 K < 3 p M` give `40 m_N < 3 M`
  have hmN : p * mFloor p (N n) ≤ N n := by
    rw [mFloor, mul_comm]; exact Nat.div_mul_le_self _ _
  have hKN : 40 * N n = 3 * K n := by simp only [K, N]; ring
  have hlow : K n < p * M := hp.lower
  have hstep : p * (40 * mFloor p (N n)) < p * (3 * M) := by
    calc p * (40 * mFloor p (N n)) = 40 * (p * mFloor p (N n)) := by ring
      _ ≤ 40 * N n := by omega
      _ = 3 * K n := hKN
      _ < 3 * (p * M) := by omega
      _ = p * (3 * M) := by ring
  exact lt_of_mul_lt_mul_left hstep (Nat.zero_le p)

/-- **`T < 2Hx`** (p. 10).  Equivalent integer form: `10 p T < 23 K`. -/
theorem T_lt_int (hp : IsInnerPrime n M p) (A : InnerAlloc n M p) :
    10 * (p : ℤ) * A.T < 23 * (K n : ℤ) := by
  obtain ⟨h2m, hmM, hmN, hK⟩ := inner_facts hp
  have hM := hp.cutoff
  set m : ℕ := mHalf p with hmdef
  have hm0 : 0 < m := hp.mHalf_pos
  have hmZ : (0 : ℤ) < (m : ℤ) := by exact_mod_cast hm0
  have hpZ : (0 : ℤ) < (p : ℤ) := by exact_mod_cast hp.prime.pos
  have h2mZ : 2 * (m : ℤ) + 1 = (p : ℤ) := by exact_mod_cast h2m
  have hKZ : 23 * (K n : ℤ) = 20 * ((h n : ℤ) + 3 * (N n : ℤ)) := by exact_mod_cast hK
  have hEZ : (0 : ℤ) ≤ (A.E : ℤ) := Int.natCast_nonneg _
  have hmNZ : (0 : ℤ) ≤ (mFloor p (N n) : ℤ) := Int.natCast_nonneg _
  have hTE := A.hTE
  -- `P = h + 3N < p · L₀`, since `p M > K = 40n` and `P = 46n`
  have hP : (h n : ℤ) + 3 * (N n : ℤ) < (p : ℤ) * (L0 M : ℤ) := by
    have hlow : (K n : ℤ) < (p : ℤ) * (M : ℤ) := by exact_mod_cast hp.lower
    have hL0 : (L0 M : ℤ) = 4 * (M : ℤ) + 10 := by simp only [L0]; push_cast; ring
    have hPn : (h n : ℤ) + 3 * (N n : ℤ) = 46 * (n : ℤ) := by
      simp only [h, N]; push_cast; ring
    have hKn : (K n : ℤ) = 40 * (n : ℤ) := by simp only [K]; push_cast; ring
    rw [hPn, hL0]
    nlinarith [hpZ, hlow, hKn]
  -- multiply the goal by `m > 0`
  have key : (m : ℤ) * (10 * (p : ℤ) * A.T) < (m : ℤ) * (23 * (K n : ℤ)) := by
    have hmT : (m : ℤ) * A.T
        = (h n : ℤ) + 3 * (N n : ℤ) - (L0 M : ℤ) - 3 * (mFloor p (N n) : ℤ) - (A.E : ℤ) := by
      linarith [hTE]
    have hexp : (m : ℤ) * (10 * (p : ℤ) * A.T) = 10 * (p : ℤ) * ((m : ℤ) * A.T) := by ring
    rw [hexp, hmT, hKZ, ← h2mZ]
    nlinarith [hP, hEZ, hpZ, h2mZ, mul_nonneg (le_of_lt hpZ) hEZ]
  exact lt_of_mul_lt_mul_left key (le_of_lt hmZ)

/-- **`2Hx - 21/20 < T`** (p. 10).  Equivalent integer form: `46 K - 21 p < 20 p T`.
The paper's "`(2L₀ + 6m_N)/(p-1) < 1/20` follows from (4.1)" is the step
`20(L₀ + 3m_N) < m + 20` below. -/
theorem T_gt_int (hp : IsInnerPrime n M p) (A : InnerAlloc n M p) :
    46 * (K n : ℤ) - 21 * (p : ℤ) < 20 * (p : ℤ) * A.T := by
  obtain ⟨h2m, hmM, hmN, hK⟩ := inner_facts hp
  have hM := hp.cutoff
  set m : ℕ := mHalf p with hmdef
  have hm0 : 0 < m := hp.mHalf_pos
  have hmZ : (0 : ℤ) < (m : ℤ) := by exact_mod_cast hm0
  have hpZ : (0 : ℤ) < (p : ℤ) := by exact_mod_cast hp.prime.pos
  have h2mZ : 2 * (m : ℤ) + 1 = (p : ℤ) := by exact_mod_cast h2m
  have hKZ : 23 * (K n : ℤ) = 20 * ((h n : ℤ) + 3 * (N n : ℤ)) := by exact_mod_cast hK
  have hEZ : (0 : ℤ) ≤ (A.E : ℤ) := Int.natCast_nonneg _
  have hEm : (A.E : ℤ) < (m : ℤ) := by exact_mod_cast A.hE
  have hPnn : (0 : ℤ) ≤ (h n : ℤ) + 3 * (N n : ℤ) := by positivity
  have hTE := A.hTE
  -- the paper's `(2L₀ + 6m_N)/(p-1) < 1/20`
  have hslack : 20 * ((L0 M : ℤ) + 3 * (mFloor p (N n) : ℤ)) < (m : ℤ) + 20 := by
    have : 20 * (L0 M + 3 * mFloor p (N n)) < m + 20 := by
      simp only [L0]; omega
    exact_mod_cast this
  have key : (m : ℤ) * (46 * (K n : ℤ) - 21 * (p : ℤ))
      < (m : ℤ) * (20 * (p : ℤ) * A.T) := by
    have hmT : (m : ℤ) * A.T
        = (h n : ℤ) + 3 * (N n : ℤ) - (L0 M : ℤ) - 3 * (mFloor p (N n) : ℤ) - (A.E : ℤ) := by
      linarith [hTE]
    have hexp : (m : ℤ) * (20 * (p : ℤ) * A.T) = 20 * (p : ℤ) * ((m : ℤ) * A.T) := by ring
    have h46 : 46 * (K n : ℤ) = 40 * ((h n : ℤ) + 3 * (N n : ℤ)) := by linarith [hKZ]
    rw [hexp, hmT, h46, ← h2mZ]
    nlinarith [hslack, hEZ, hEm, hmZ, hPnn]
  exact lt_of_mul_lt_mul_left key (le_of_lt hmZ)

/-- **`T < 2Hx`** in the paper's variables. -/
theorem T_lt (hp : IsInnerPrime n M p) (A : InnerAlloc n M p) :
    (A.T : ℚ) < 2 * Hcst * xVal n p := by
  have hpQ : (0 : ℚ) < (p : ℚ) := by exact_mod_cast hp.prime.pos
  have hint : (10 : ℚ) * (p : ℚ) * (A.T : ℚ) < 23 * (K n : ℚ) := by
    exact_mod_cast T_lt_int hp A
  rw [xVal, Hcst, show (2 : ℚ) * (23 / 20) * ((K n : ℚ) / (p : ℚ))
      = 23 * (K n : ℚ) / (10 * (p : ℚ)) by field_simp; ring,
    lt_div_iff₀ (by positivity)]
  linarith

/-- **`2Hx - 21/20 < T`** in the paper's variables. -/
theorem T_gt (hp : IsInnerPrime n M p) (A : InnerAlloc n M p) :
    2 * Hcst * xVal n p - 21 / 20 < (A.T : ℚ) := by
  have hpQ : (0 : ℚ) < (p : ℚ) := by exact_mod_cast hp.prime.pos
  have hint : (46 : ℚ) * (K n : ℚ) - 21 * (p : ℚ) < 20 * (p : ℚ) * (A.T : ℚ) := by
    exact_mod_cast T_gt_int hp A
  rw [xVal, Hcst, show (2 : ℚ) * (23 / 20) * ((K n : ℚ) / (p : ℚ)) - 21 / 20
      = (46 * (K n : ℚ) - 21 * (p : ℚ)) / (20 * (p : ℚ)) by field_simp; ring,
    div_lt_iff₀ (by positivity)]
  linarith

end TBounds

/-! # (d) Nonnegativity of the dimensions, and `L₀ + ∑_a L_a = h` -/

/-- The paper's chain, p. 10: `T - b_a > 2Hx - 21/20 - (6αx + 3) = 2λx - 81/20`,
using `H - 3α = λ` (i.e. `23/20 - 9/40 = 37/40`). -/
theorem T_sub_bCoef_gt {n M p : ℕ} (hp : IsInnerPrime n M p) (A : InnerAlloc n M p)
    {a : ℕ} (ha1 : 1 ≤ a) (ha2 : a ≤ mHalf p) :
    2 * lam * xVal n p - 81 / 20 < (A.T : ℚ) - (bCoef n p a : ℚ) := by
  have h2a : 2 * a < p := two_mul_lt_of_le_mHalf hp.odd ha2
  have hb := bCoef_lt_real n p a hp.prime.pos ha1 h2a
  have hT := T_gt hp A
  have hHl : 2 * Hcst * xVal n p - 21 / 20 - (6 * alpha * xVal n p + 3)
      = 2 * lam * xVal n p - 81 / 20 := by
    rw [Hcst, alpha, lam]; ring
  linarith [hHl]

/-- `2λx - 81/20 ≥ 3/2` for `x ≥ 3`: `2λ·3 - 81/20 = 111/20 - 81/20 = 3/2`. -/
theorem two_lam_bound {x : ℚ} (hx : 3 ≤ x) : (3 : ℚ) / 2 ≤ 2 * lam * x - 81 / 20 := by
  rw [lam]; linarith

/-- **`L_a > 0`, in the paper's own chain** (p. 10): `L_a ≥ T - b_a > 2λx - 81/20 ≥ 3/2`.

`Counting.InnerAlloc.L_nonneg` proves `L_a ≥ 0` by the integer route; this is the paper's
real-variable route, and it gives the stronger `L_a > 3/2`. -/
theorem L_gt_three_halves {n M p : ℕ} (hp : IsInnerPrime n M p) (A : InnerAlloc n M p)
    {a : ℕ} (ha1 : 1 ≤ a) (ha2 : a ≤ mHalf p) : (3 : ℚ) / 2 < (A.L a : ℚ) := by
  have h1 := T_sub_bCoef_gt hp A ha1 ha2
  have h2 := two_lam_bound (three_le_xVal (M := M) hp)
  have heps : (0 : ℚ) ≤ (A.eps a : ℚ) := by positivity
  have hL : (A.L a : ℚ) = (A.T : ℚ) - (bCoef n p a : ℚ) + (A.eps a : ℚ) := by
    simp only [InnerAlloc.L]; push_cast; ring
  rw [hL]
  linarith

/-! ### The counterfactual: why the case split is needed

With the naive bound `ℓ_N(a) ≤ 2m_N + 2` — which is attained, `ell_naive_attained` — one gets
only `b_a ≤ 6αx + 6`, and the paper's chain then yields `T - b_a > 2λx - 141/20`, which is
`-3/2` at `x = 3`.  The dimensions would not be provably nonnegative and Proposition 4.1
would collapse. -/

/-- What the naive bound gives: `b_a ≤ 6αx + 6`. -/
theorem bCoef_le_naive_real (n p a : ℕ) (hp0 : 0 < p) (ha1 : 1 ≤ a) (ha2 : 2 * a < p) :
    (bCoef n p a : ℚ) ≤ 6 * alpha * xVal n p + 6 := by
  have hpQ : (0 : ℚ) < (p : ℚ) := by exact_mod_cast hp0
  have hnaive : ell p (N n) a ≤ 2 * mFloor p (N n) + 2 := ell_le_naive p (N n) a ha1 ha2
  have hmN : (p : ℚ) * (mFloor p (N n) : ℚ) ≤ (N n : ℚ) := by
    have : p * mFloor p (N n) ≤ N n := by
      rw [mFloor, mul_comm]; exact Nat.div_mul_le_self _ _
    exact_mod_cast this
  have hmNq : (mFloor p (N n) : ℚ) ≤ (N n : ℚ) / (p : ℚ) := by
    rw [le_div_iff₀ hpQ]; linarith
  have hb : (bCoef n p a : ℚ) = 3 * (ell p (N n) a : ℚ) := by
    rw [bCoef]; push_cast; ring
  have hnq : (ell p (N n) a : ℚ) ≤ 2 * (mFloor p (N n) : ℚ) + 2 := by exact_mod_cast hnaive
  rw [hb, show (6 : ℚ) * alpha * xVal n p = 6 * (alpha * xVal n p) by ring, alpha_xVal]
  linarith

/-- The chain that the naive bound supports, and only that one. -/
theorem naive_chain {x T b : ℚ} (hT : 2 * Hcst * x - 21 / 20 < T)
    (hb : b ≤ 6 * alpha * x + 6) : 2 * lam * x - 141 / 20 < T - b := by
  have : 2 * Hcst * x - 21 / 20 - (6 * alpha * x + 6) = 2 * lam * x - 141 / 20 := by
    rw [Hcst, alpha, lam]; ring
  linarith

/-- **The naive bound is not enough**: at `x = 3`, the endpoint of the inner range, the naive
chain gives `T - b_a > -3/2`, whereas the sharp chain gives `T - b_a > 3/2`. -/
theorem naive_bound_insufficient :
    2 * lam * 3 - 141 / 20 = -(3 / 2) ∧ 2 * lam * 3 - 81 / 20 = 3 / 2 := by
  constructor <;> (rw [lam]; norm_num)

/-! ### The dimension identity `L₀ + ∑_{a=1}^m L_a = h`

The one counting input is `∑_{a=1}^m ℓ_A(a) = A - m_A`: the classes `±a`, `1 ≤ a ≤ m`,
partition the nonzero residues mod `p`. -/

private lemma card_filter_le_v (m v : ℕ) :
    ((Icc 1 m).filter (fun a => a ≤ v)).card = min m v := by
  have hset : (Icc 1 m).filter (fun a => a ≤ v) = Icc 1 (min m v) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  rw [hset, Nat.card_Icc]
  omega

private lemma card_filter_ge_v (m v p : ℕ) (hv : v < p) :
    ((Icc 1 m).filter (fun a => p ≤ v + a)).card = m + 1 - (p - v) := by
  have hset : (Icc 1 m).filter (fun a => p ≤ v + a) = Icc (p - v) m := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  rw [hset, Nat.card_Icc]

/-- **`∑_{a=1}^{m} ℓ_A(a) = A - m_A`** for odd `p = 2m+1`: every `j ∈ [1,A]` with `p ∤ j`
lies in exactly one of the `m` classes `{a, -a}`. -/
theorem sum_ell (p A : ℕ) (hp : 2 * mHalf p + 1 = p) :
    ∑ a ∈ Icc 1 (mHalf p), ell p A a = A - mFloor p A := by
  set m : ℕ := mHalf p with hmdef
  have hp0 : 0 < p := by omega
  have hA : p * (A / p) + A % p = A := Nat.div_add_mod A p
  have hv : A % p < p := Nat.mod_lt _ hp0
  have hterm : ∀ a ∈ Icc 1 m, ell p A a
      = 2 * mFloor p A + (if a ≤ A % p then 1 else 0) + (if p ≤ A % p + a then 1 else 0) := by
    intro a ha
    rw [Finset.mem_Icc] at ha
    exact ell_closed p A a ha.1 (by omega)
  rw [Finset.sum_congr rfl hterm]
  have hsplit : ∑ a ∈ Icc 1 m,
        (2 * mFloor p A + (if a ≤ A % p then 1 else 0) + (if p ≤ A % p + a then 1 else 0))
      = (∑ _a ∈ Icc 1 m, 2 * mFloor p A)
        + (∑ a ∈ Icc 1 m, (if a ≤ A % p then 1 else 0))
        + ∑ a ∈ Icc 1 m, (if p ≤ A % p + a then 1 else 0) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  have hcard : (Icc 1 m).card = m := by rw [Nat.card_Icc]; omega
  rw [hsplit, Finset.sum_const, hcard,
    ← Finset.sum_filter, ← Finset.sum_filter, Finset.sum_const, Finset.sum_const,
    card_filter_le_v m (A % p), card_filter_ge_v m (A % p) p hv]
  simp only [smul_eq_mul, mul_one, mFloor]
  -- the remaining identity is linear in the atom `Y = m ⌊A/p⌋`
  obtain ⟨Y, hY⟩ : ∃ Y, m * (A / p) = Y := ⟨_, rfl⟩
  have hA' : A = 2 * Y + (A / p) + A % p := by
    calc A = p * (A / p) + A % p := hA.symm
      _ = (2 * m + 1) * (A / p) + A % p := by rw [hp]
      _ = 2 * (m * (A / p)) + (A / p) + A % p := by ring
      _ = 2 * Y + (A / p) + A % p := by rw [hY]
  have hmul : m * (2 * (A / p)) = 2 * Y := by rw [← hY]; ring
  rw [hmul]
  omega

/-- **`L₀ + ∑_{a=1}^m L_a = h`** (p. 10), over `ℤ`. -/
theorem dimension_identity {n M p : ℕ} (hp : IsInnerPrime n M p) (A : InnerAlloc n M p) :
    (L0 M : ℤ) + ∑ a ∈ Icc 1 (mHalf p), A.L a = (h n : ℤ) := by
  have hsum : ∑ a ∈ Icc 1 (mHalf p), ell p (N n) a = N n - mFloor p (N n) :=
    sum_ell p (N n) hp.two_mHalf
  have hmN : mFloor p (N n) ≤ N n := by
    calc mFloor p (N n) ≤ p * mFloor p (N n) := Nat.le_mul_of_pos_left _ hp.prime.pos
      _ ≤ N n := by rw [mFloor, mul_comm]; exact Nat.div_mul_le_self _ _
  have hsumZ : ∑ a ∈ Icc 1 (mHalf p), (bCoef n p a : ℤ)
      = 3 * ((N n : ℤ) - (mFloor p (N n) : ℤ)) := by
    have hstep : ∀ a ∈ Icc 1 (mHalf p),
        ((bCoef n p a : ℕ) : ℤ) = 3 * ((ell p (N n) a : ℕ) : ℤ) := by
      intro a _; simp [bCoef]
    have hcast : ((∑ a ∈ Icc 1 (mHalf p), ell p (N n) a : ℕ) : ℤ)
        = ∑ a ∈ Icc 1 (mHalf p), ((ell p (N n) a : ℕ) : ℤ) := by push_cast; ring
    rw [Finset.sum_congr rfl hstep, ← Finset.mul_sum, ← hcast, hsum, Nat.cast_sub hmN]
  have hepsZ : ∑ a ∈ Icc 1 (mHalf p), (A.eps a : ℤ) = (A.E : ℤ) := by
    exact_mod_cast congrArg (fun k : ℕ => (k : ℤ)) A.hEpsSum
  have hcard : (Icc 1 (mHalf p)).card = mHalf p := by rw [Nat.card_Icc]; omega
  have hexpand : ∑ a ∈ Icc 1 (mHalf p), A.L a
      = (mHalf p : ℤ) * A.T - 3 * ((N n : ℤ) - (mFloor p (N n) : ℤ)) + (A.E : ℤ) := by
    simp only [InnerAlloc.L]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hsumZ, hepsZ, Finset.sum_const,
      hcard, nsmul_eq_mul]
  rw [hexpand]
  have hTE := A.hTE
  linarith [hTE]

/-! # (e) The basis (4.5), the orders `ν`, the weights (4.6)–(4.8), and the degree bounds -/

namespace InnerAlloc

variable {n M p : ℕ}

/-- The number of basis rows assigned to the class `t = -a²` (p. 10): `L₀ = 4M + 10` for the
zero class, `L_a = T - b_a + ε_a` for `a ≥ 1`.

`Int.toNat` is exact here, because `L_a ≥ 0` (`Counting.InnerAlloc.L_nonneg`, and, with the
paper's own chain, `L_gt_three_halves` above). -/
def Ldim (A : InnerAlloc n M p) (a : ℕ) : ℕ := if a = 0 then L0 M else (A.L a).toNat

@[simp] lemma Ldim_zero (A : InnerAlloc n M p) : A.Ldim 0 = L0 M := by simp [Ldim]

/-- For an ordinary class the truncation in `Ldim` does nothing: `L_a ≥ 0`. -/
lemma Ldim_cast (hp : IsInnerPrime n M p) (A : InnerAlloc n M p) {a : ℕ}
    (ha1 : 1 ≤ a) (ha2 : a ≤ mHalf p) : (A.Ldim a : ℤ) = A.L a := by
  have hL := L_nonneg hp A ha1 ha2
  have ha : a ≠ 0 := by omega
  simp only [Ldim, ite_eq_right ha]
  exact Int.toNat_of_nonneg hL

/-- **(4.5)**: the row polynomial
`E_{a,i}(t) = ∏_{0 ≤ c ≤ m, c ≠ a} (t + c²)^{L_c} · (t + a²)^i`. -/
def rowPoly (A : InnerAlloc n M p) (a i : ℕ) : ℚ[X] :=
  (∏ c ∈ (range (mHalf p + 1)).erase a, (X + C ((c : ℚ) ^ 2)) ^ A.Ldim c)
    * (X + C ((a : ℚ) ^ 2)) ^ i

/-- The order of vanishing `ν_i(c)` of the row polynomial `E_{a,i}` of (4.5) at `t = -c²`:
`i` at its own class, `L_c` at every other class.  (This is the paper's `ν_i(a)` of (4.2),
read off (4.5).) -/
def nu (A : InnerAlloc n M p) (a i c : ℕ) : ℕ := if c = a then i else A.Ldim c

/-- `ν` really is an order of vanishing: `(t+c²)^{ν_i(c)}` divides `E_{a,i}`. -/
lemma pow_nu_dvd_rowPoly (A : InnerAlloc n M p) (a i c : ℕ) (hc : c ∈ range (mHalf p + 1)) :
    (X + C ((c : ℚ) ^ 2)) ^ A.nu a i c ∣ A.rowPoly a i := by
  unfold nu rowPoly
  by_cases hca : c = a
  · subst hca
    rw [ite_eq_left rfl]
    exact Dvd.dvd.mul_left dvd_rfl _
  · rw [ite_eq_right hca]
    refine Dvd.dvd.mul_right ?_ _
    exact Finset.dvd_prod_of_mem (fun d : ℕ => (X + C ((d : ℚ) ^ 2)) ^ A.Ldim d)
      (Finset.mem_erase.2 ⟨hca, hc⟩)

/-- `ν_i(c) ≤ L_c`: the orders never exceed the dimension of the class.  (For `c = a` this is
the row range `0 ≤ i < L_a` of (4.5).) -/
lemma nu_le (A : InnerAlloc n M p) {a i c : ℕ} (hi : i < A.Ldim a) : A.nu a i c ≤ A.Ldim c := by
  unfold nu
  split_ifs with hca
  · subst hca; omega
  · exact le_rfl

end InnerAlloc

/-! ### The rows of (4.5) and the identity `∑ rows 2w = γ_p^in` (4.8) -/

namespace InnerAlloc

variable {n M p : ℕ}

/-- The index set of the basis (4.5): the pairs `(a,i)` with `0 ≤ a ≤ m` and `0 ≤ i < L_a`. -/
abbrev Rows (A : InnerAlloc n M p) : Type := Σ a : Fin (mHalf p + 1), Fin (A.Ldim (a : ℕ))

/-- Twice the weight of the row `(a,i)`: (4.7) for the zero class, (4.6) for `a ≥ 1`.
(Weights are half-integers; `2w` is an integer.) -/
def rowW (A : InnerAlloc n M p) (r : A.Rows) : ℤ :=
  if (r.1 : ℕ) = 0 then A.w2zero (r.2 : ℕ) else A.w2 (r.1 : ℕ) (r.2 : ℕ)

/-- **(4.8) is the sum of the row weights**: `∑_{(a,i)} 2 w_{a,i} = γ_p^in`.

This is what makes the hypothesis `hgamma` of `prop_4_1_of_entry_bounds` the paper's own
definition rather than an assumption about an unspecified number. -/
lemma sum_rowW (A : InnerAlloc n M p) : ∑ r : A.Rows, A.rowW r = A.gammaIn := by
  classical
  have h1 : ∑ r : A.Rows, A.rowW r
      = ∑ a ∈ range (mHalf p + 1),
          ∑ i ∈ range (A.Ldim a), (if a = 0 then A.w2zero i else A.w2 a i) := by
    rw [← Finset.univ_sigma_univ, Finset.sum_sigma,
      ← Fin.sum_univ_eq_sum_range
        (fun a => ∑ i ∈ range (A.Ldim a), (if a = 0 then A.w2zero i else A.w2 a i))
        (mHalf p + 1)]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    exact Fin.sum_univ_eq_sum_range
      (fun i => if (a : ℕ) = 0 then A.w2zero i else A.w2 (a : ℕ) i) (A.Ldim (a : ℕ))
  have h2 := Finset.sum_range_succ'
    (fun a => ∑ i ∈ range (A.Ldim a), (if a = 0 then A.w2zero i else A.w2 a i)) (mHalf p)
  have h3 : ∀ k : ℕ, ∑ i ∈ range (A.Ldim (k + 1)),
        (if k + 1 = 0 then A.w2zero i else A.w2 (k + 1) i)
      = ∑ i ∈ range (A.L (k + 1)).toNat, A.w2 (k + 1) i := by
    intro k
    simp [Ldim]
  have h5 : ∑ k ∈ range (mHalf p), ∑ i ∈ range (A.L (k + 1)).toNat, A.w2 (k + 1) i
      = ∑ a ∈ Icc 1 (mHalf p), ∑ i ∈ range (A.L a).toNat, A.w2 a i := by
    have hIcc : Icc 1 (mHalf p) = Ico 1 (mHalf p + 1) := by
      ext a; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
    rw [hIcc,
      Finset.sum_Ico_eq_sum_range (fun a => ∑ i ∈ range (A.L a).toNat, A.w2 a i) 1
        (mHalf p + 1)]
    simp only [Nat.add_sub_cancel]
    exact Finset.sum_congr rfl (fun k _ => by rw [Nat.add_comm])
  rw [h1, h2]
  simp only [h3]
  rw [h5, gammaIn, add_comm]
  simp [Ldim]

end InnerAlloc

/-- **First degree bound of p. 11**: for an ordinary class `1 ≤ c ≤ m` and any two rows
`(a,i)`, `(a',i')` of the basis (4.5),

`ν_i(c) + ν_j(c) + 6 ℓ_N(c) ≤ 2(T + 1)`.

The proof is the paper's: `ν ≤ L_c`, `L_c = T - b_c + ε_c ≤ T - b_c + 1`, and
`6 ℓ_N(c) = 2 b_c`. -/
theorem degree_bound_ordinary {n M p : ℕ} (hp : IsInnerPrime n M p) (A : InnerAlloc n M p)
    {a i a' i' c : ℕ} (hi : i < A.Ldim a) (hi' : i' < A.Ldim a')
    (hc1 : 1 ≤ c) (hc2 : c ≤ mHalf p) :
    (A.nu a i c : ℤ) + (A.nu a' i' c : ℤ) + 6 * (ell p (N n) c : ℤ) ≤ 2 * (A.T + 1) := by
  have h1 : (A.nu a i c : ℤ) ≤ (A.Ldim c : ℤ) := by exact_mod_cast A.nu_le hi
  have h2 : (A.nu a' i' c : ℤ) ≤ (A.Ldim c : ℤ) := by exact_mod_cast A.nu_le hi'
  have hL : (A.Ldim c : ℤ) = A.L c := A.Ldim_cast hp hc1 hc2
  have heps : (A.eps c : ℤ) ≤ 1 := by
    rcases A.hEps01 c with h | h <;> simp [h]
  have hLexp : A.L c = A.T - (bCoef n p c : ℤ) + (A.eps c : ℤ) := by
    simp only [InnerAlloc.L]
  have hb : (bCoef n p c : ℤ) = 3 * (ell p (N n) c : ℤ) := by simp [bCoef]
  rw [hL, hLexp] at h1 h2
  linarith

/-- `2(T + 1) < 23M/5 + 2` (p. 11), from `T < 2Hx` and `x < M`. -/
theorem two_T_add_one_lt {n M p : ℕ} (hp : IsInnerPrime n M p) (A : InnerAlloc n M p) :
    2 * ((A.T : ℚ) + 1) < 23 / 5 * (M : ℚ) + 2 := by
  have h1 := T_lt hp A
  have h2 := xVal_lt_M hp
  have h3 : (0 : ℚ) < xVal n p := xVal_pos (M := M) hp
  rw [Hcst] at h1
  nlinarith

/-- **Second degree bound of p. 11**: `5 + 2ν_i(0) + 2ν_j(0) + 12 m_N ≤ 5 + 4L₀ + 12 m_N`,
because `ν_i(0) ≤ L₀`. -/
theorem degree_bound_zero {n M p : ℕ} (A : InnerAlloc n M p) {a i a' i' : ℕ}
    (hi : i < A.Ldim a) (hi' : i' < A.Ldim a') :
    5 + 2 * A.nu a i 0 + 2 * A.nu a' i' 0 + 12 * mFloor p (N n)
      ≤ 5 + 4 * L0 M + 12 * mFloor p (N n) := by
  have h1 := A.nu_le (c := 0) hi
  have h2 := A.nu_le (c := 0) hi'
  rw [InnerAlloc.Ldim_zero] at h1 h2
  omega

/-- `5 + 4L₀ + 12 m_N ≤ 169M/10 + 45` (p. 11): `4L₀ = 16M + 40` and `12 m_N < 9M/10`. -/
theorem zero_degree_le {n M p : ℕ} (hp : IsInnerPrime n M p) :
    ((5 + 4 * L0 M + 12 * mFloor p (N n) : ℕ) : ℚ) ≤ 169 / 10 * (M : ℚ) + 45 := by
  obtain ⟨-, -, hmN, -⟩ := inner_facts hp
  have hmNQ : (40 : ℚ) * (mFloor p (N n) : ℚ) < 3 * (M : ℚ) := by exact_mod_cast hmN
  have hL0 : ((L0 M : ℕ) : ℚ) = 4 * (M : ℚ) + 10 := by push_cast [L0]; ring
  push_cast
  rw [hL0]
  linarith

/-- **Both degrees are at most `p + 1`** (p. 11), because `p > 200M` and `M ≥ 40`. -/
theorem degrees_le_p_add_one {n M p : ℕ} (hp : IsInnerPrime n M p) :
    23 / 5 * (M : ℚ) + 2 ≤ (p : ℚ) + 1 ∧ 169 / 10 * (M : ℚ) + 45 ≤ (p : ℚ) + 1 := by
  have h200 : (200 : ℚ) * (M : ℚ) < (p : ℚ) := by exact_mod_cast hp.gt_200M
  have hM : (40 : ℚ) ≤ (M : ℚ) := by exact_mod_cast hp.cutoff
  constructor <;> linarith

/-! ### The weight comparisons of p. 11

"It remains to check each assigned weight against every source in the distribution formula."
Two of the paper's comparisons are pure consequences of the definitions and of `hExtraOrder`,
and are proved here.  (The remaining comparisons need the distribution formula of §3.) -/

/-- **The ordinary-source comparison** (p. 11): `Z_c - Z_a + 1 + (ℓ_K(a) - ℓ_K(c))/2 ≥ 0`,
doubled so as to stay in `ℤ`.

The paper's own argument: `Z_b = T + ε_b`, so `Z_c - Z_a ∈ {-1,0,1}`; `ℓ_K` takes two
consecutive values (`ell_two_consecutive`), so `ℓ_K(a) - ℓ_K(c) ≥ -1`; and "in the only case
`Z_a = T+1`, `Z_c = T` that needs an ordering, the definition of the extras gives
`ℓ_K(a) ≥ ℓ_K(c)`" — which is the field `InnerAlloc.hExtraOrder`. -/
theorem weight_comparison {n M p : ℕ} (hp : IsInnerPrime n M p) (A : InnerAlloc n M p)
    {a c : ℕ} (ha1 : 1 ≤ a) (ha2 : a ≤ mHalf p) (hc1 : 1 ≤ c) (hc2 : c ≤ mHalf p) :
    0 ≤ 2 * A.Z c - 2 * A.Z a + 2 + (ell p (K n) a : ℤ) - (ell p (K n) c : ℤ) := by
  have hcons : ell p (K n) c ≤ ell p (K n) a + 1 :=
    ell_two_consecutive p (K n) c a hc1 (two_mul_lt_of_le_mHalf hp.odd hc2)
      ha1 (two_mul_lt_of_le_mHalf hp.odd ha2)
  have hconsZ : (ell p (K n) c : ℤ) ≤ (ell p (K n) a : ℤ) + 1 := by exact_mod_cast hcons
  have hmem_a : a ∈ Icc 1 (mHalf p) := Finset.mem_Icc.2 ⟨ha1, ha2⟩
  have hmem_c : c ∈ Icc 1 (mHalf p) := Finset.mem_Icc.2 ⟨hc1, hc2⟩
  simp only [InnerAlloc.Z]
  rcases A.hEps01 a with hea | hea
  · rw [hea]
    have hc0 : (0 : ℤ) ≤ (A.eps c : ℤ) := Int.natCast_nonneg _
    push_cast
    linarith
  · rcases A.hEps01 c with hec | hec
    · have hord := A.hExtraOrder a hmem_a c hmem_c hea hec
      have hordZ : (ell p (K n) c : ℤ) ≤ (ell p (K n) a : ℤ) := by exact_mod_cast hord
      rw [hea, hec]
      push_cast
      linarith
    · rw [hea, hec]
      push_cast
      linarith

/-- **The zero-source bound** (p. 11): "at the zero source, the half-weight of any ordinary
row is `2L₀ + 6m_N - m_K + 1/2 ≥ 7M + 41/2`".  Doubled to stay in `ℤ`:
`4L₀ + 12 m_N - 2 m_K + 1 ≥ 14M + 41`.

With `4L₀ = 16M + 40` this is `2M + 12 m_N ≥ 2 m_K`, which holds because `m_K = ⌊x⌋ < M`. -/
theorem zero_source_bound {n M p : ℕ} (hp : IsInnerPrime n M p) :
    14 * (M : ℤ) + 41
      ≤ 4 * (L0 M : ℤ) + 12 * (mFloor p (N n) : ℤ) - 2 * (mFloor p (K n) : ℤ) + 1 := by
  have hpos : 0 < p := hp.prime.pos
  have hl : K n < M * p := by rw [Nat.mul_comm]; exact hp.lower
  have hmK : mFloor p (K n) < M := by
    rw [mFloor, Nat.div_lt_iff_lt_mul hpos]
    exact hl
  have hmKZ : (mFloor p (K n) : ℤ) < (M : ℤ) := by exact_mod_cast hmK
  have hmNZ : (0 : ℤ) ≤ (mFloor p (N n) : ℤ) := Int.natCast_nonneg _
  have hL0 : (L0 M : ℤ) = 4 * (M : ℤ) + 10 := by simp only [L0]; push_cast; ring
  rw [hL0]
  linarith

/-! # (f) Proposition 4.1

The proof on p. 11 consists of

  (i)  the LOCAL ANALYSIS (§3, Lemmas 3.1 and 3.2, together with the near/far pole
       bookkeeping and the degree bounds of (e) above), which produces the ENTRY BOUND
       `v_p^G(A_{uv}) ≥ w_u + w_v` in the basis (4.5).  It is proved in `InnerEntries.lean`
       and enters here as the hypothesis `hentry`/`hweights` of `prop_4_1_of_entry_bounds`;

  (ii) the REDUCTION "every determinant term has valuation at least `2 ∑ w`; the basis change
       is unimodular", which is proved below.

The reduction is the `L = 0` case of Lemma 4.2 (p. 12).  The general case of Lemma 4.2 (a
rank-`r` correction `p^{-1} L` and a loss `min(r,z)`) is used only in §4.2, for
Proposition 4.3, and is not needed here.

Weights are half-integers, so throughout this section `W` denotes `2w`; the entry hypothesis
is `W u + W v ≤ 2 · (entry valuation)` and the conclusion is `v_p^G(det) ≥ ∑_u W u`, which is
`2 ∑_u w_u = γ_p^in` of (4.8). -/

section GaussValuation

variable {p : ℕ} [hpf : Fact p.Prime]

private lemma p_pos_rat : (0 : ℚ) < (p : ℚ) := by exact_mod_cast hpf.out.pos

private lemma zpow_p_pos (c : ℤ) : (0 : ℚ) < (p : ℚ) ^ (-c) := zpow_pos p_pos_rat _

/-- `padicNorm p q ≤ p^{-c}` is exactly `v_p(q) ≥ c` (with `v_p(0) = +∞`). -/
private lemma padicNorm_le_iff {q : ℚ} {c : ℤ} :
    padicNorm p q ≤ (p : ℚ) ^ (-c) ↔ (q = 0 ∨ c ≤ padicValRat p q) := by
  have hp1 : (1 : ℚ) < (p : ℚ) := by exact_mod_cast hpf.out.one_lt
  constructor
  · intro hle
    by_cases h0 : q = 0
    · exact Or.inl h0
    · refine Or.inr ?_
      rw [padicNorm.eq_zpow_of_nonzero h0] at hle
      have := (zpow_le_zpow_iff_right₀ hp1).1 hle
      omega
  · rintro (rfl | hc)
    · rw [padicNorm.zero]
      exact le_of_lt (zpow_p_pos _)
    · by_cases h0 : q = 0
      · rw [h0, padicNorm.zero]; exact le_of_lt (zpow_p_pos _)
      · rw [padicNorm.eq_zpow_of_nonzero h0]
        exact (zpow_le_zpow_iff_right₀ hp1).2 (by omega)

/-- The Gauss-valuation bound `v_p^G(A) ≥ c` of §3, in multiplicative form. -/
lemma vGAtLeast_iff (A : ℚ[X]) (c : ℤ) :
    vGAtLeast p A c ↔ ∀ i, padicNorm p (A.coeff i) ≤ (p : ℚ) ^ (-c) := by
  constructor
  · intro h i
    refine padicNorm_le_iff.2 ?_
    by_cases h0 : A.coeff i = 0
    · exact Or.inl h0
    · exact Or.inr (h i h0)
  · intro h i hi
    rcases padicNorm_le_iff.1 (h i) with h1 | h1
    · exact absurd h1 hi
    · exact h1

omit hpf in
lemma vGAtLeast_mono {A : ℚ[X]} {c c' : ℤ} (hcc : c' ≤ c) (h : vGAtLeast p A c) :
    vGAtLeast p A c' := fun i hi => le_trans hcc (h i hi)

/-- An integer constant is a `p`-adic integer: `v_p^G(k) ≥ 0`. -/
lemma vGAtLeast_intCast (k : ℤ) : vGAtLeast p ((k : ℚ[X])) 0 := by
  rw [vGAtLeast_iff]
  intro i
  rw [← Polynomial.C_eq_intCast]
  rcases eq_or_ne i 0 with rfl | hi
  · simpa using padicNorm.of_int (p := p) k
  · rw [Polynomial.coeff_C, ite_eq_right hi, padicNorm.zero]
    exact le_of_lt (zpow_p_pos _)

lemma vGAtLeast_one : vGAtLeast p (1 : ℚ[X]) 0 := by
  simpa using vGAtLeast_intCast (p := p) 1

/-- `v_p^G(AB) ≥ v_p^G(A) + v_p^G(B)`. -/
lemma vGAtLeast_mul {A B : ℚ[X]} {c d : ℤ} (hA : vGAtLeast p A c) (hB : vGAtLeast p B d) :
    vGAtLeast p (A * B) (c + d) := by
  rw [vGAtLeast_iff] at hA hB ⊢
  intro i
  rw [Polynomial.coeff_mul]
  refine padicNorm.sum_le' (fun x _ => ?_) (le_of_lt (zpow_p_pos _))
  rw [padicNorm.mul]
  have hstep : padicNorm p (A.coeff x.1) * padicNorm p (B.coeff x.2)
      ≤ (p : ℚ) ^ (-c) * (p : ℚ) ^ (-d) :=
    mul_le_mul (hA _) (hB _) (padicNorm.nonneg _) (le_of_lt (zpow_p_pos _))
  refine le_trans hstep (le_of_eq ?_)
  rw [← zpow_add₀ (ne_of_gt p_pos_rat)]
  congr 1
  ring

/-- `v_p^G(∑ f) ≥ min v_p^G(f)` (nonarchimedean). -/
lemma vGAtLeast_sum {ι : Type*} {s : Finset ι} {F : ι → ℚ[X]} {c : ℤ}
    (h : ∀ i ∈ s, vGAtLeast p (F i) c) : vGAtLeast p (∑ i ∈ s, F i) c := by
  rw [vGAtLeast_iff]
  intro k
  rw [Polynomial.finsetSum_coeff]
  exact padicNorm.sum_le' (fun i hi => (vGAtLeast_iff _ _).1 (h i hi) k)
    (le_of_lt (zpow_p_pos _))

/-- `v_p^G(∏ f) ≥ ∑ v_p^G(f)`. -/
lemma vGAtLeast_prod {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℚ[X]) (c : ι → ℤ) :
    (∀ i ∈ s, vGAtLeast p (f i) (c i)) → vGAtLeast p (∏ i ∈ s, f i) (∑ i ∈ s, c i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · intro _
    simpa using vGAtLeast_one (p := p)
  · intro a s ha ih h
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact vGAtLeast_mul (h a (Finset.mem_insert_self a s))
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

/-- **The reduction, in the abstract** (the `L = 0` case of Lemma 4.2, p. 12).

If every entry of a square matrix over `ℚ[X]` satisfies `W u + W v ≤ 2 v_p^G(A_{uv})` — the
half-integer weight bound `v_p^G(A_{uv}) ≥ w_u + w_v` with `W = 2w` — then

`v_p^G(det A) ≥ ∑_u W u = 2 ∑_u w_u`.

The proof is exactly the paper's sentence "every determinant term has valuation at least
`2 ∑ w_{a,i}`": each permutation term is a product of `d` entries, and `∑_i (W(σ i) + W i)
= 2 ∑ W` because `σ` is a bijection. -/
theorem vGAtLeast_det {ι : Type*} [DecidableEq ι] [Fintype ι]
    (B : Matrix ι ι ℚ[X]) (entry : ι → ι → ℤ) (W : ι → ℤ)
    (hB : ∀ u v, vGAtLeast p (B u v) (entry u v))
    (hW : ∀ u v, W u + W v ≤ 2 * entry u v) :
    vGAtLeast p B.det (∑ u, W u) := by
  classical
  rw [Matrix.det_apply']
  refine vGAtLeast_sum (fun σ _ => ?_)
  have hprod : vGAtLeast p (∏ i, B (σ i) i) (∑ i, entry (σ i) i) :=
    vGAtLeast_prod _ _ _ (fun i _ => hB _ _)
  have hsign : vGAtLeast p (((Equiv.Perm.sign σ : ℤ) : ℚ[X])) 0 :=
    vGAtLeast_intCast _
  have hmul := vGAtLeast_mul hsign hprod
  refine vGAtLeast_mono ?_ hmul
  rw [zero_add]
  -- `2 ∑ W = ∑ (W (σ i) + W i) ≤ ∑ 2 · entry (σ i) i`
  have hperm : ∑ i, W (σ i) = ∑ i, W i := Equiv.sum_comp σ W
  have hle : ∑ i, (W (σ i) + W i) ≤ ∑ i, 2 * entry (σ i) i :=
    Finset.sum_le_sum (fun i _ => hW (σ i) i)
  rw [Finset.sum_add_distrib, hperm, ← Finset.mul_sum] at hle
  linarith

end GaussValuation

/-- **Proposition 4.1** (p. 11), stated: *"Under (4.1), `v_p^G(Δ_K) ≥ γ_p^in`."*

This is the statement of `Zeta5.prop_4_1` in `Interface.lean`, spelled out here so that this
file does not import `Interface.lean`. -/
def Prop_4_1 (n M p : ℕ) : Prop :=
  IsInnerPrime n M p → ∀ A : InnerAlloc n M p, vGAtLeast p (Delta n) A.gammaIn

/-- **Proposition 4.1** (p. 11), reduced to its local input.

Hypotheses, all of them parts of the paper's own proof:

* `B` is the matrix of the bilinear form in the basis (4.5), `entry u v` a lower bound for
  the Gauss valuation of its `(u,v)` entry — the output of §3 (Lemmas 3.1, 3.2, the
  distribution formula, and the degree bounds `degree_bound_ordinary`,
  `degree_bound_zero`, `degrees_le_p_add_one` above);
* `hweights`: `W u + W v ≤ 2 · entry u v`, i.e. `v_p^G(A_{uv}) ≥ w_u + w_v` for the
  half-integer weights (4.6)–(4.7) carried as `W = 2w`;
* `hgamma`: `∑_u W u = γ_p^in`, which is (4.8) (see `InnerAlloc.sum_rowW`);
* `hbasis`: the basis change is `ℤ_p`-unimodular, so `Δ_K` and `det B` differ by a `p`-adic
  unit.

Conclusion: `v_p^G(Δ_K) ≥ γ_p^in`, which is Proposition 4.1.

(`hc0` is not used in the proof — when `c = 0` both sides are trivial — but it is part of
the statement "the basis change is unimodular", so it is kept.) -/
theorem prop_4_1_of_entry_bounds {n M p : ℕ} (hprime : p.Prime)
    {ι : Type} [DecidableEq ι] [Fintype ι]
    (A : InnerAlloc n M p)
    (B : Matrix ι ι ℚ[X]) (W : ι → ℤ) (entry : ι → ι → ℤ)
    (hentry : ∀ u v, vGAtLeast p (B u v) (entry u v))
    (hweights : ∀ u v, W u + W v ≤ 2 * entry u v)
    (hgamma : ∑ u, W u = A.gammaIn)
    (c : ℚ) (_hc0 : c ≠ 0) (hcunit : padicValRat p c = 0)
    (hbasis : Delta n = Polynomial.C c * B.det) :
    vGAtLeast p (Delta n) A.gammaIn := by
  have : Fact p.Prime := ⟨hprime⟩
  have hdet : vGAtLeast p B.det A.gammaIn := by
    rw [← hgamma]
    exact vGAtLeast_det B entry W hentry hweights
  have hC : vGAtLeast p (Polynomial.C c) 0 := by
    intro i hi
    rcases eq_or_ne i 0 with rfl | hne
    · rw [Polynomial.coeff_C_zero, hcunit]
    · rw [Polynomial.coeff_C, ite_eq_right hne] at hi
      exact absurd rfl hi
  rw [hbasis]
  simpa using vGAtLeast_mul hC hdet

/-! ### Existence of the allocation (4.4), in full

This proves `Zeta5.exists_innerAlloc` of `Interface.lean`.  The paper's one-sentence
construction — "Define integers `T, E` by (4.4).  Give `ε_a = 1` to the first `E` classes
in decreasing order of `ℓ_K(a)`.  Ties may be ordered arbitrarily." — is Euclidean division by `m = (p-1)/2 > 0` followed by a choice of `E`
maximisers of `ℓ_K`. -/

/-- "The first `E` elements in decreasing order of `f`": a subset of size `E` every element
of which has `f`-value at least that of every element outside.  Ties are arbitrary, which is
exactly the freedom the paper reserves. -/
theorem exists_top_subset {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℕ) :
    ∀ E, E ≤ s.card → ∃ S ⊆ s, S.card = E ∧ ∀ a ∈ S, ∀ c ∈ s \ S, f c ≤ f a := by
  intro E
  induction E with
  | zero => intro _; exact ⟨∅, Finset.empty_subset _, rfl, by simp⟩
  | succ E ih =>
    intro hE
    obtain ⟨S, hSs, hScard, hStop⟩ := ih (by omega)
    have hne : (s \ S).Nonempty := by
      rw [← Finset.card_pos, Finset.card_sdiff, Finset.inter_eq_left.2 hSs, hScard]
      omega
    obtain ⟨b, hb, hbmax⟩ := Finset.exists_max_image (s \ S) f hne
    have hbs : b ∈ s := (Finset.mem_sdiff.1 hb).1
    have hbS : b ∉ S := (Finset.mem_sdiff.1 hb).2
    refine ⟨insert b S, Finset.insert_subset hbs hSs, ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem hbS, hScard]
    · intro a ha c hc
      have hcsub : c ∈ s \ S := by
        rw [Finset.mem_sdiff] at hc ⊢
        exact ⟨hc.1, fun hcS => hc.2 (Finset.mem_insert_of_mem hcS)⟩
      rcases Finset.mem_insert.1 ha with rfl | ha'
      · exact hbmax c hcsub
      · exact hStop a ha' c hcsub

/-- **Existence of the allocation (4.4)** (p. 10).  This is exactly the statement of
`Zeta5.exists_innerAlloc` in `Interface.lean`. -/
theorem exists_innerAlloc_of_inner {n M p : ℕ} (hp : IsInnerPrime n M p) :
    Nonempty (InnerAlloc n M p) := by
  classical
  obtain ⟨T, E, hElt, hTE⟩ := exists_TE n M p hp.mHalf_pos
  have hEnat : E < mHalf p := by exact_mod_cast hElt
  have hcard : (Icc 1 (mHalf p)).card = mHalf p := by rw [Nat.card_Icc]; omega
  obtain ⟨S, hSs, hScard, hStop⟩ :=
    exists_top_subset (Icc 1 (mHalf p)) (fun a => ell p (K n) a) E (by omega)
  refine ⟨⟨T, E, fun a => if a ∈ S then 1 else 0, hEnat, hTE, ?_, ?_, ?_⟩⟩
  · intro a; by_cases hmem : a ∈ S <;> simp [hmem]
  · rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one,
      Finset.filter_mem_eq_inter, Finset.inter_eq_right.2 hSs, hScard]
  · intro a _ha c hc hepsa hepsc
    have haS : a ∈ S := by by_contra hmem; simp [hmem] at hepsa
    have hcS : c ∉ S := by intro hmem; simp [hmem] at hepsc
    exact hStop a haS c (Finset.mem_sdiff.2 ⟨hc, hcS⟩)

/-! # Known-answer controls for this file

Small cases computed by hand from the *definitions* and re-derived by Lean, as a check
against mistranscribed statements. -/

namespace Section41Checks

open Zeta5

/-- `ℓ_9(2) = #{2,5,9} = 3` at `p = 7`, straight from the definition of `ell`. -/
example : ell 7 9 2 = 3 := by decide

/-- ... and the closed form agrees: `2⌊9/7⌋ + 1_{2 ≤ 2} + 1_{2 ≥ 5} = 2 + 1 + 0 = 3`. -/
example : 2 * mFloor 7 9 + (if 2 ≤ 9 % 7 then 1 else 0) + (if 7 ≤ 9 % 7 + 2 then 1 else 0)
    = 3 := by decide

/-- `ℓ_12(1) = #{1,4,6,9,11} = 5` at `p = 5`. -/
example : ell 5 12 1 = 5 := by decide

/-- `ℓ_12(2) = #{2,3,7,8,12} = 5` at `p = 5`. -/
example : ell 5 12 2 = 5 := by decide

/-- `∑_{a=1}^{2} ℓ_12(a) = 10 = 12 - ⌊12/5⌋`: the identity `sum_ell`, checked by hand. -/
example : ell 5 12 1 + ell 5 12 2 = 12 - mFloor 5 12 := by decide

/-- The attained case of the naive bound, computed from the definition rather than from the
closed form: `ℓ_6(1) = 2 = 2⌊6/7⌋ + 2`. -/
example : ell 7 6 1 = 2 := by decide

/-- **Cross-check on the inequality of p. 10.**  `Counting.ell_lt` (divisibility argument) and
`ell_lt_caseSplit` (case split on `v_A`) prove *the same statement* by different routes; both
type-check against the same signature. -/
example : ∀ p A a : ℕ, 1 ≤ a → 2 * a < p → p * ell p A a < 2 * A + p := ell_lt

example : ∀ p A a : ℕ, 1 ≤ a → 2 * a < p → p * ell p A a < 2 * A + p := ell_lt_caseSplit

/-- `H - 3α = λ` and `H = 1 + 2α`, the two identities the chain `T - b_a > 2λx - 81/20`
uses. -/
example : Hcst - 3 * alpha = lam := by norm_num [Hcst, alpha, lam]

/-- `2λ·3 - 81/20 = 3/2` exactly: the inner range `x ≥ 3` is tight for the sharp bound. -/
example : 2 * lam * 3 - 81 / 20 = 3 / 2 := by norm_num [lam]

/-! ## Axiom checks

`#print axioms` shows only the three standard axioms for each theorem below. -/

#print axioms ell_closed
#print axioms ell_lt_caseSplit
#print axioms ell_naive_attained
#print axioms ell_eq_naive_of_large_v
#print axioms naive_not_enough
#print axioms exists_TE
#print axioms unique_TE
#print axioms T_lt
#print axioms T_gt
#print axioms L_gt_three_halves
#print axioms dimension_identity
#print axioms InnerAlloc.sum_rowW
#print axioms ell_two_consecutive
#print axioms weight_comparison
#print axioms zero_source_bound
#print axioms degree_bound_ordinary
#print axioms degrees_le_p_add_one
#print axioms vGAtLeast_det
#print axioms prop_4_1_of_entry_bounds
#print axioms exists_innerAlloc_of_inner

end Section41Checks

end

end Zeta5
