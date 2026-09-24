/-
Zeta5/RealBound.lean  —  §6 and Appendix A of the paper: the real determinant.

This file proves everything that Proposition 6.3 (6.16) needs apart from (6.14):

  * all of Table 1's finite verifications (p. 21);
  * the constants of Appendix A.4: **(A.10)** and hence **(6.4)**, from certified
    rational enclosures of the eighteen logarithms involved — no numerical constant is
    assumed anywhere in this file;
  * the regularisation constant `≤ 60` of p. 19 (the only use of `b_j - a_j > 1/225`);
  * that Table 2's 684 dyadic cells tile `[0,2]` (pp. 23–25);
  * the factorial estimates of p. 20 and hence **(6.15)**, whose `K²` coefficient is
    *exactly* `C_*` of (6.3);
  * the elementary weight bound **(6.11)**;
  * the exact cancellation of the `K² log K` terms of (6.14) and (6.15), and the passage
    from `λM₀ - I(ρ) + C_*` to `Ū`, i.e. **(6.16) from (6.14) and (6.15)**.

(6.14) itself (`Zeta5.RealBound.eq_6_14`) and Proposition 6.3 (`Zeta5.RealBound.prop_6_3`)
are stated and proved in `Zeta5/Sec6/Final.lean` (same names, same types): their proofs need
the §6 machinery of `Zeta5/Sec6/`, which imports this file.  **This file contains no `sorry`
and declares no `axiom`.**

Everything here was cross-checked against the independent numerics of the referee audit
(see README, "Provenance"):
  I(ρ)  = -2.126593445147050403253600969…
  C_*   =  2.653035990340488661129250336…
  λM₀ - I(ρ) + C_* = -1.366995564512460935617…  ≤  Ū = -1.3669955.

CONVENTION.  Real numbers are written as exact rational literals; every inequality
between them is closed by `norm_num`, and every inequality involving `Real.log` is
closed from a *certified* Taylor enclosure (`Real.abs_log_sub_add_sum_range_le`),
so no numerical constant is assumed.
-/
import Zeta5.Basic

namespace Zeta5
namespace RealBound

open Real Finset

noncomputable section

/-! ## A.1  Table 1: the sixteen arcsine components

`Table 1 gives 10¹²a_j, 10¹²b_j and 10¹²c_j` (p. 22).  All entries are integers; the
functions below are `0` outside `0 ≤ j ≤ 15` (the paper's `j = 1, …, 16`). -/

/-- `a_j` of Table 1 (`a_{j+1}` in the paper's 1-based numbering). -/
def aT : ℕ → ℝ
  | 0 => 3906748086 / 10 ^ 12
  | 1 => 2312248264 / 10 ^ 12
  | 2 => 1402286665 / 10 ^ 12
  | 3 => 881725356 / 10 ^ 12
  | 4 => 578197906 / 10 ^ 12
  | 5 => 396324613 / 10 ^ 12
  | 6 => 283911191 / 10 ^ 12
  | 7 => 212206188 / 10 ^ 12
  | 8 => 165097686 / 10 ^ 12
  | 9 => 133347132 / 10 ^ 12
  | 10 => 111522114 / 10 ^ 12
  | 11 => 96349355 / 10 ^ 12
  | 12 => 85815639 / 10 ^ 12
  | 13 => 78667711 / 10 ^ 12
  | 14 => 74129565 / 10 ^ 12
  | 15 => 71741310 / 10 ^ 12
  | _ => 0

/-- `b_j` of Table 1. -/
def bT : ℕ → ℝ
  | 0 => 8992695531 / 10 ^ 12
  | 1 => 15340997855 / 10 ^ 12
  | 2 => 25730180724 / 10 ^ 12
  | 3 => 41909578246 / 10 ^ 12
  | 4 => 65851089563 / 10 ^ 12
  | 5 => 99481037884 / 10 ^ 12
  | 6 => 144325727458 / 10 ^ 12
  | 7 => 201105762729 / 10 ^ 12
  | 8 => 269345996903 / 10 ^ 12
  | 9 => 347089554156 / 10 ^ 12
  | 10 => 430806704415 / 10 ^ 12
  | 11 => 515561896511 / 10 ^ 12
  | 12 => 595448778546 / 10 ^ 12
  | 13 => 664241383483 / 10 ^ 12
  | 14 => 716160577112 / 10 ^ 12
  | 15 => 746637295669 / 10 ^ 12
  | _ => 0

/-- `c_j` of Table 1, the mass of the `j`-th arcsine component. -/
def cT : ℕ → ℝ
  | 0 => 10515596180 / 10 ^ 12
  | 1 => 29471737793 / 10 ^ 12
  | 2 => 42934365099 / 10 ^ 12
  | 3 => 58204231966 / 10 ^ 12
  | 4 => 69037621310 / 10 ^ 12
  | 5 => 78873099189 / 10 ^ 12
  | 6 => 84856120711 / 10 ^ 12
  | 7 => 88396082127 / 10 ^ 12
  | 8 => 88303382125 / 10 ^ 12
  | 9 => 85472321255 / 10 ^ 12
  | 10 => 78899184238 / 10 ^ 12
  | 11 => 70353471918 / 10 ^ 12
  | 12 => 58838976615 / 10 ^ 12
  | 13 => 44421321106 / 10 ^ 12
  | 14 => 30462865791 / 10 ^ 12
  | 15 => 5959622577 / 10 ^ 12
  | _ => 0

/-- `S_j = ∑_{i ≤ j} c_i` of (A.2) (here `S_m = ∑_{i < m} cT i`, so `cS 16 = λ`). -/
def cS (m : ℕ) : ℝ := ∑ i ∈ range m, cT i

/-- The weight `S_j² - S_{j-1}²` of (A.2). -/
def wT (m : ℕ) : ℝ := cS (m + 1) ^ 2 - cS m ^ 2

/-! ### The finite verifications of p. 21

"Direct summation gives `∑ c_j = 37/40`.  The intervals satisfy
`0 < a₁₆ < ⋯ < a₁ < b₁ < ⋯ < b₁₆ < 2`, `b_j - a_j > 1/225`." -/

/-- **`∑_{j=1}^{16} c_j = 37/40 = λ`** (p. 21), exactly. -/
theorem sum_cT : ∑ j ∈ range 16, cT j = (lam : ℝ) := by
  norm_num [Finset.sum_range_succ, cT, lam]

/-- `cS 16 = λ`: the total mass of `ρ` is `λ`, as Lemma 6.1 requires. -/
theorem cS_sixteen : cS 16 = (lam : ℝ) := by unfold cS; exact sum_cT

/-- Every `c_j` is positive: `ρ` is a positive measure. -/
theorem cT_pos : ∀ j < 16, 0 < cT j := by
  intro j hj
  interval_cases j <;> norm_num [cT]

/-- **Nesting**, `a_{j+1} < a_j` (p. 21: `a₁₆ < ⋯ < a₁`). -/
theorem aT_strictAnti : ∀ j, j + 1 < 16 → aT (j + 1) < aT j := by
  intro j hj
  have hj' : j < 15 := by omega
  interval_cases j <;> norm_num [aT]

/-- **Nesting**, `b_j < b_{j+1}` (p. 21: `b₁ < ⋯ < b₁₆`). -/
theorem bT_strictMono : ∀ j, j + 1 < 16 → bT j < bT (j + 1) := by
  intro j hj
  have hj' : j < 15 := by omega
  interval_cases j <;> norm_num [bT]

/-- **`b_j - a_j > 1/225`** (p. 21), the length bound that controls the regularisation
error in (6.6).  The smallest length is `b₁ - a₁ = 0.005085947445`. -/
theorem tab1_length : ∀ j < 16, 1 / 225 < bT j - aT j := by
  intro j hj
  interval_cases j <;> norm_num [aT, bT]

/-- **`0 < a₁₆`** (p. 21): `supp ρ ⊆ [a₁₆, b₁₆] ⊂ (0, 2)`. -/
theorem aT_last_pos : 0 < aT 15 := by norm_num [aT]

/-- **`b₁₆ < 2`** (p. 21). -/
theorem bT_last_lt_two : bT 15 < 2 := by norm_num [bT]

/-- `a₁ < b₁`: the innermost interval is nondegenerate. -/
theorem aT_lt_bT : ∀ j < 16, aT j < bT j := by
  intro j hj
  interval_cases j <;> norm_num [aT, bT]

/-- Every interval is contained in the next: `[a_j, b_j] ⊆ [a_{j+1}, b_{j+1}]`. -/
theorem tab1_nested : ∀ j, j + 1 < 16 → aT (j + 1) < aT j ∧ bT j < bT (j + 1) :=
  fun j hj => ⟨aT_strictAnti j hj, bT_strictMono j hj⟩

/-! ## A.2  Certified logarithm enclosures

Every logarithm below is enclosed by the Taylor series of `log(1-x)` at `x = 1 - y`
with an explicit remainder (`Real.abs_log_sub_add_sum_range_le`), after reducing the
argument to `[2/3, 4/3]` by a power of two.  This plays the role of the paper's (A.3);
we use Mathlib's remainder rather than the paper's `2z^{2m+1}/((2m+1)(1-z²))`, which is
sharper but not available. -/

/-- `log 2` to `10⁻²⁰`, from the series at `x = 1/2` with 70 terms
(remainder `2⁻⁷⁰ ≤ 1.7·10⁻²¹`).  Mathlib's `Real.log_two_near_10` is only `10⁻¹⁰`,
which is not enough for (A.10). -/
theorem log_two_bounds :
    (69314718055994530941 / 10 ^ 20 : ℝ) < Real.log 2 ∧ Real.log 2 < (69314718055994530942 / 10 ^ 20 : ℝ) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := (1 : ℝ) / 2) (by norm_num) 70
  rw [show (1 : ℝ) - 1 / 2 = (2 : ℝ)⁻¹ by norm_num, Real.log_inv, abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

/-- `log((b_1 - a_1)/4)`, the `j = 1` term of (A.2).
`(b - a)/4 = 1017189489/781250000/2^10`. -/
theorem logLen0 : (-33337841532116411511 / 5000000000000000000 : ℝ) < Real.log ((bT 0 - aT 0) / 4)
    ∧ Real.log ((bT 0 - aT 0) / 4) < (-66675683064232823001 / 10000000000000000000 : ℝ) := by
  have hv : (bT 0 - aT 0) / 4 = (1017189489 / 781250000 : ℝ) / 2 ^ (10 : ℕ) := by norm_num [aT, bT]
  rw [hv, Real.log_div (by norm_num) (by positivity), Real.log_pow]
  have h := Real.abs_log_sub_add_sum_range_le (x := (1 : ℝ) - (1017189489 / 781250000 : ℝ)) (by norm_num) 35
  rw [show (1 : ℝ) - ((1 : ℝ) - (1017189489 / 781250000 : ℝ)) = (1017189489 / 781250000 : ℝ) by ring, abs_le] at h
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith [h.1, h.2, log_two_bounds.1, log_two_bounds.2]

/-- `log((b_2 - a_2)/4)`, the `j = 2` term of (A.2).
`(b - a)/4 = 13028749591/15625000000/2^8`. -/
theorem logLen1 : (-71586140217784334567 / 12500000000000000000 : ℝ) < Real.log ((bT 1 - aT 1) / 4)
    ∧ Real.log ((bT 1 - aT 1) / 4) < (-143172280435568669107 / 25000000000000000000 : ℝ) := by
  have hv : (bT 1 - aT 1) / 4 = (13028749591 / 15625000000 : ℝ) / 2 ^ (8 : ℕ) := by norm_num [aT, bT]
  rw [hv, Real.log_div (by norm_num) (by positivity), Real.log_pow]
  have h := Real.abs_log_sub_add_sum_range_le (x := (1 : ℝ) - (13028749591 / 15625000000 : ℝ)) (by norm_num) 35
  rw [show (1 : ℝ) - ((1 : ℝ) - (13028749591 / 15625000000 : ℝ)) = (13028749591 / 15625000000 : ℝ) by ring, abs_le] at h
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith [h.1, h.2, log_two_bounds.1, log_two_bounds.2]

/-- `log((b_3 - a_3)/4)`, the `j = 3` term of (A.2).
`(b - a)/4 = 24327894059/31250000000/2^7`. -/
theorem logLen2 : (-255121302221531270197 / 50000000000000000000 : ℝ) < Real.log ((bT 2 - aT 2) / 4)
    ∧ Real.log ((bT 2 - aT 2) / 4) < (-510242604443062540287 / 100000000000000000000 : ℝ) := by
  have hv : (bT 2 - aT 2) / 4 = (24327894059 / 31250000000 : ℝ) / 2 ^ (7 : ℕ) := by norm_num [aT, bT]
  rw [hv, Real.log_div (by norm_num) (by positivity), Real.log_pow]
  have h := Real.abs_log_sub_add_sum_range_le (x := (1 : ℝ) - (24327894059 / 31250000000 : ℝ)) (by norm_num) 35
  rw [show (1 : ℝ) - ((1 : ℝ) - (24327894059 / 31250000000 : ℝ)) = (24327894059 / 31250000000 : ℝ) by ring, abs_le] at h
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith [h.1, h.2, log_two_bounds.1, log_two_bounds.2]

/-- `log((b_4 - a_4)/4)`, the `j = 4` term of (A.2).
`(b - a)/4 = 4102785289/3125000000/2^7`. -/
theorem logLen3 : (-228989923263168470097 / 50000000000000000000 : ℝ) < Real.log ((bT 3 - aT 3) / 4)
    ∧ Real.log ((bT 3 - aT 3) / 4) < (-457979846526336939887 / 100000000000000000000 : ℝ) := by
  have hv : (bT 3 - aT 3) / 4 = (4102785289 / 3125000000 : ℝ) / 2 ^ (7 : ℕ) := by norm_num [aT, bT]
  rw [hv, Real.log_div (by norm_num) (by positivity), Real.log_pow]
  have h := Real.abs_log_sub_add_sum_range_le (x := (1 : ℝ) - (4102785289 / 3125000000 : ℝ)) (by norm_num) 35
  rw [show (1 : ℝ) - ((1 : ℝ) - (4102785289 / 3125000000 : ℝ)) = (4102785289 / 3125000000 : ℝ) by ring, abs_le] at h
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith [h.1, h.2, log_two_bounds.1, log_two_bounds.2]

/-- `log((b_5 - a_5)/4)`, the `j = 5` term of (A.2).
`(b - a)/4 = 65272891657/62500000000/2^6`. -/
theorem logLen4 : (-51443410317916746019 / 12500000000000000000 : ℝ) < Real.log ((bT 4 - aT 4) / 4)
    ∧ Real.log ((bT 4 - aT 4) / 4) < (-205773641271666984023 / 50000000000000000000 : ℝ) := by
  have hv : (bT 4 - aT 4) / 4 = (65272891657 / 62500000000 : ℝ) / 2 ^ (6 : ℕ) := by norm_num [aT, bT]
  rw [hv, Real.log_div (by norm_num) (by positivity), Real.log_pow]
  have h := Real.abs_log_sub_add_sum_range_le (x := (1 : ℝ) - (65272891657 / 62500000000 : ℝ)) (by norm_num) 35
  rw [show (1 : ℝ) - ((1 : ℝ) - (65272891657 / 62500000000 : ℝ)) = (65272891657 / 62500000000 : ℝ) by ring, abs_le] at h
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith [h.1, h.2, log_two_bounds.1, log_two_bounds.2]

/-- `log((b_6 - a_6)/4)`, the `j = 6` term of (A.2).
`(b - a)/4 = 99084713271/125000000000/2^5`. -/
theorem logLen5 : (-36980744662550153871 / 10000000000000000000 : ℝ) < Real.log ((bT 5 - aT 5) / 4)
    ∧ Real.log ((bT 5 - aT 5) / 4) < (-73961489325100307721 / 20000000000000000000 : ℝ) := by
  have hv : (bT 5 - aT 5) / 4 = (99084713271 / 125000000000 : ℝ) / 2 ^ (5 : ℕ) := by norm_num [aT, bT]
  rw [hv, Real.log_div (by norm_num) (by positivity), Real.log_pow]
  have h := Real.abs_log_sub_add_sum_range_le (x := (1 : ℝ) - (99084713271 / 125000000000 : ℝ)) (by norm_num) 35
  rw [show (1 : ℝ) - ((1 : ℝ) - (99084713271 / 125000000000 : ℝ)) = (99084713271 / 125000000000 : ℝ) by ring, abs_le] at h
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith [h.1, h.2, log_two_bounds.1, log_two_bounds.2]

/-- `log((b_7 - a_7)/4)`, the `j = 7` term of (A.2).
`(b - a)/4 = 144041816267/125000000000/2^5`. -/
theorem logLen6 : (-33239459919382025261 / 10000000000000000000 : ℝ) < Real.log ((bT 6 - aT 6) / 4)
    ∧ Real.log ((bT 6 - aT 6) / 4) < (-66478919838764050501 / 20000000000000000000 : ℝ) := by
  have hv : (bT 6 - aT 6) / 4 = (144041816267 / 125000000000 : ℝ) / 2 ^ (5 : ℕ) := by norm_num [aT, bT]
  rw [hv, Real.log_div (by norm_num) (by positivity), Real.log_pow]
  have h := Real.abs_log_sub_add_sum_range_le (x := (1 : ℝ) - (144041816267 / 125000000000 : ℝ)) (by norm_num) 35
  rw [show (1 : ℝ) - ((1 : ℝ) - (144041816267 / 125000000000 : ℝ)) = (144041816267 / 125000000000 : ℝ) by ring, abs_le] at h
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith [h.1, h.2, log_two_bounds.1, log_two_bounds.2]

/-- `log((b_8 - a_8)/4)`, the `j = 8` term of (A.2).
`(b - a)/4 = 200893556541/250000000000/2^4`. -/
theorem logLen7 : (-74781861044053440217 / 25000000000000000000 : ℝ) < Real.log ((bT 7 - aT 7) / 4)
    ∧ Real.log ((bT 7 - aT 7) / 4) < (-74781861044053440191 / 25000000000000000000 : ℝ) := by
  have hv : (bT 7 - aT 7) / 4 = (200893556541 / 250000000000 : ℝ) / 2 ^ (4 : ℕ) := by norm_num [aT, bT]
  rw [hv, Real.log_div (by norm_num) (by positivity), Real.log_pow]
  have h := Real.abs_log_sub_add_sum_range_le (x := (1 : ℝ) - (200893556541 / 250000000000 : ℝ)) (by norm_num) 35
  rw [show (1 : ℝ) - ((1 : ℝ) - (200893556541 / 250000000000 : ℝ)) = (200893556541 / 250000000000 : ℝ) by ring, abs_le] at h
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith [h.1, h.2, log_two_bounds.1, log_two_bounds.2]

/-- `log((b_9 - a_9)/4)`, the `j = 9` term of (A.2).
`(b - a)/4 = 269180899217/250000000000/2^4`. -/
theorem logLen8 : (-67466649968081073817 / 25000000000000000000 : ℝ) < Real.log ((bT 8 - aT 8) / 4)
    ∧ Real.log ((bT 8 - aT 8) / 4) < (-67466649968081073791 / 25000000000000000000 : ℝ) := by
  have hv : (bT 8 - aT 8) / 4 = (269180899217 / 250000000000 : ℝ) / 2 ^ (4 : ℕ) := by norm_num [aT, bT]
  rw [hv, Real.log_div (by norm_num) (by positivity), Real.log_pow]
  have h := Real.abs_log_sub_add_sum_range_le (x := (1 : ℝ) - (269180899217 / 250000000000 : ℝ)) (by norm_num) 35
  rw [show (1 : ℝ) - ((1 : ℝ) - (269180899217 / 250000000000 : ℝ)) = (269180899217 / 250000000000 : ℝ) by ring, abs_le] at h
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith [h.1, h.2, log_two_bounds.1, log_two_bounds.2]

/-- `log((b_10 - a_10)/4)`, the `j = 10` term of (A.2).
`(b - a)/4 = 21684762939/31250000000/2^3`. -/
theorem logLen9 : (-122242553633070925763 / 50000000000000000000 : ℝ) < Real.log ((bT 9 - aT 9) / 4)
    ∧ Real.log ((bT 9 - aT 9) / 4) < (-244485107266141851323 / 100000000000000000000 : ℝ) := by
  have hv : (bT 9 - aT 9) / 4 = (21684762939 / 31250000000 : ℝ) / 2 ^ (3 : ℕ) := by norm_num [aT, bT]
  rw [hv, Real.log_div (by norm_num) (by positivity), Real.log_pow]
  have h := Real.abs_log_sub_add_sum_range_le (x := (1 : ℝ) - (21684762939 / 31250000000 : ℝ)) (by norm_num) 35
  rw [show (1 : ℝ) - ((1 : ℝ) - (21684762939 / 31250000000 : ℝ)) = (21684762939 / 31250000000 : ℝ) by ring, abs_le] at h
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith [h.1, h.2, log_two_bounds.1, log_two_bounds.2]

/-- `log((b_11 - a_11)/4)`, the `j = 11` term of (A.2).
`(b - a)/4 = 430695182301/500000000000/2^3`. -/
theorem logLen10 : (-111432451692316965063 / 50000000000000000000 : ℝ) < Real.log ((bT 10 - aT 10) / 4)
    ∧ Real.log ((bT 10 - aT 10) / 4) < (-222864903384633930023 / 100000000000000000000 : ℝ) := by
  have hv : (bT 10 - aT 10) / 4 = (430695182301 / 500000000000 : ℝ) / 2 ^ (3 : ℕ) := by norm_num [aT, bT]
  rw [hv, Real.log_div (by norm_num) (by positivity), Real.log_pow]
  have h := Real.abs_log_sub_add_sum_range_le (x := (1 : ℝ) - (430695182301 / 500000000000 : ℝ)) (by norm_num) 35
  rw [show (1 : ℝ) - ((1 : ℝ) - (430695182301 / 500000000000 : ℝ)) = (430695182301 / 500000000000 : ℝ) by ring, abs_le] at h
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith [h.1, h.2, log_two_bounds.1, log_two_bounds.2]

/-- `log((b_12 - a_12)/4)`, the `j = 12` term of (A.2).
`(b - a)/4 = 128866386789/125000000000/2^3`. -/
theorem logLen11 : (-102448958635874242913 / 50000000000000000000 : ℝ) < Real.log ((bT 11 - aT 11) / 4)
    ∧ Real.log ((bT 11 - aT 11) / 4) < (-204897917271748485723 / 100000000000000000000 : ℝ) := by
  have hv : (bT 11 - aT 11) / 4 = (128866386789 / 125000000000 : ℝ) / 2 ^ (3 : ℕ) := by norm_num [aT, bT]
  rw [hv, Real.log_div (by norm_num) (by positivity), Real.log_pow]
  have h := Real.abs_log_sub_add_sum_range_le (x := (1 : ℝ) - (128866386789 / 125000000000 : ℝ)) (by norm_num) 35
  rw [show (1 : ℝ) - ((1 : ℝ) - (128866386789 / 125000000000 : ℝ)) = (128866386789 / 125000000000 : ℝ) by ring, abs_le] at h
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith [h.1, h.2, log_two_bounds.1, log_two_bounds.2]

/-- `log((b_13 - a_13)/4)`, the `j = 13` term of (A.2).
`(b - a)/4 = 595362962907/500000000000/2^3`. -/
theorem logLen12 : (-95243919942577987763 / 50000000000000000000 : ℝ) < Real.log ((bT 12 - aT 12) / 4)
    ∧ Real.log ((bT 12 - aT 12) / 4) < (-190487839885155975423 / 100000000000000000000 : ℝ) := by
  have hv : (bT 12 - aT 12) / 4 = (595362962907 / 500000000000 : ℝ) / 2 ^ (3 : ℕ) := by norm_num [aT, bT]
  rw [hv, Real.log_div (by norm_num) (by positivity), Real.log_pow]
  have h := Real.abs_log_sub_add_sum_range_le (x := (1 : ℝ) - (595362962907 / 500000000000 : ℝ)) (by norm_num) 35
  rw [show (1 : ℝ) - ((1 : ℝ) - (595362962907 / 500000000000 : ℝ)) = (595362962907 / 500000000000 : ℝ) by ring, abs_le] at h
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith [h.1, h.2, log_two_bounds.1, log_two_bounds.2]

/-- `log((b_14 - a_14)/4)`, the `j = 14` term of (A.2).
`(b - a)/4 = 166040678943/125000000000/2^3`. -/
theorem logLen13 : (-89776123338644796613 / 50000000000000000000 : ℝ) < Real.log ((bT 13 - aT 13) / 4)
    ∧ Real.log ((bT 13 - aT 13) / 4) < (-179552246677289591923 / 100000000000000000000 : ℝ) := by
  have hv : (bT 13 - aT 13) / 4 = (166040678943 / 125000000000 : ℝ) / 2 ^ (3 : ℕ) := by norm_num [aT, bT]
  rw [hv, Real.log_div (by norm_num) (by positivity), Real.log_pow]
  have h := Real.abs_log_sub_add_sum_range_le (x := (1 : ℝ) - (166040678943 / 125000000000 : ℝ)) (by norm_num) 35
  rw [show (1 : ℝ) - ((1 : ℝ) - (166040678943 / 125000000000 : ℝ)) = (166040678943 / 125000000000 : ℝ) by ring, abs_le] at h
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith [h.1, h.2, log_two_bounds.1, log_two_bounds.2]

/-- `log((b_15 - a_15)/4)`, the `j = 15` term of (A.2).
`(b - a)/4 = 716086447547/1000000000000/2^2`. -/
theorem logLen14 : (-43006218590799913371 / 25000000000000000000 : ℝ) < Real.log ((bT 14 - aT 14) / 4)
    ∧ Real.log ((bT 14 - aT 14) / 4) < (-86012437181599826691 / 50000000000000000000 : ℝ) := by
  have hv : (bT 14 - aT 14) / 4 = (716086447547 / 1000000000000 : ℝ) / 2 ^ (2 : ℕ) := by norm_num [aT, bT]
  rw [hv, Real.log_div (by norm_num) (by positivity), Real.log_pow]
  have h := Real.abs_log_sub_add_sum_range_le (x := (1 : ℝ) - (716086447547 / 1000000000000 : ℝ)) (by norm_num) 35
  rw [show (1 : ℝ) - ((1 : ℝ) - (716086447547 / 1000000000000 : ℝ)) = (716086447547 / 1000000000000 : ℝ) by ring, abs_le] at h
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith [h.1, h.2, log_two_bounds.1, log_two_bounds.2]

/-- `log((b_16 - a_16)/4)`, the `j = 16` term of (A.2).
`(b - a)/4 = 746565554359/1000000000000/2^2`. -/
theorem logLen15 : (-41964155284003248171 / 25000000000000000000 : ℝ) < Real.log ((bT 15 - aT 15) / 4)
    ∧ Real.log ((bT 15 - aT 15) / 4) < (-83928310568006496291 / 50000000000000000000 : ℝ) := by
  have hv : (bT 15 - aT 15) / 4 = (746565554359 / 1000000000000 : ℝ) / 2 ^ (2 : ℕ) := by norm_num [aT, bT]
  rw [hv, Real.log_div (by norm_num) (by positivity), Real.log_pow]
  have h := Real.abs_log_sub_add_sum_range_le (x := (1 : ℝ) - (746565554359 / 1000000000000 : ℝ)) (by norm_num) 35
  rw [show (1 : ℝ) - ((1 : ℝ) - (746565554359 / 1000000000000 : ℝ)) = (746565554359 / 1000000000000 : ℝ) by ring, abs_le] at h
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith [h.1, h.2, log_two_bounds.1, log_two_bounds.2]

/-! ## A.4  The energy `I(ρ)` and the norm constant `C_*`

`(A.2)`:  `I(ρ) = ∑_{j=1}^{16} (S_j² - S_{j-1}²) log((b_j - a_j)/4)`, which is (A.1)
plus the nesting (`the potential of the j-th interval is constant on every earlier
interval`, p. 22).  `(6.3)`:  `C_* = -2λ + 12αλ(1 - log α) + 3λ² - 2λ² log(2λ)`. -/

/-- **(A.2)** (p. 22): the logarithmic energy of `ρ`, evaluated by the nesting. -/
def Irho : ℝ := ∑ j ∈ range 16, wT j * Real.log ((bT j - aT j) / 4)

/-- **(6.3)** (p. 17): `C_* = -2λ + 12αλ(1 - log α) + 3λ² - 2λ² log(2λ)`. -/
def Cstar : ℝ :=
  -2 * (lam : ℝ) + 12 * (alpha : ℝ) * (lam : ℝ) * (1 - Real.log (alpha : ℝ))
    + 3 * (lam : ℝ) ^ 2 - 2 * (lam : ℝ) ^ 2 * Real.log (2 * (lam : ℝ))

/-- **`M₀ = -1329/200`** of (6.2). -/
def M0 : ℝ := -1329 / 200

theorem wT_val0 : wT 0 = (276444407552076481 / 2500000000000000000000 : ℝ) := by
  norm_num [wT, cS, Finset.sum_range_succ, cT]

theorem wT_val1 : wT 1 = (1488409115247409372329 / 1000000000000000000000000 : ℝ) := by
  norm_num [wT, cS, Finset.sum_range_succ, cT]

theorem wT_val2 : wT 2 = (1055404259743817139291 / 200000000000000000000000 : ℝ) := by
  norm_num [wT, cS, Finset.sum_range_succ, cT]

theorem wT_val3 : wT 3 = (652026011717750304813 / 50000000000000000000000 : ℝ) := by
  norm_num [wT, cS, Finset.sum_range_succ, cT]

theorem wT_val4 : wT 4 = (1212609516209410227783 / 50000000000000000000000 : ℝ) := by
  norm_num [wT, cS, Finset.sum_range_succ, cT]

theorem wT_val5 : wT 5 = (7874693439238125629853 / 200000000000000000000000 : ℝ) := by
  norm_num [wT, cS, Finset.sum_range_succ, cT]

theorem wT_val6 : wT 6 = (11250723841514726902227 / 200000000000000000000000 : ℝ) := by
  norm_num [wT, cS, Finset.sum_range_succ, cT]

theorem wT_val7 : wT 7 = (73915179740055157667121 / 1000000000000000000000000 : ℝ) := by
  norm_num [wT, cS, Finset.sum_range_succ, cT]

theorem wT_val8 : wT 8 = (5724212864942206439 / 64000000000000000000 : ℝ) := by
  norm_num [wT, cS, Finset.sum_range_succ, cT]

theorem wT_val9 : wT 9 = (4057052429519671935601 / 40000000000000000000000 : ℝ) := by
  norm_num [wT, cS, Finset.sum_range_succ, cT]

theorem wT_val10 : wT 10 = (13324378841571167621503 / 125000000000000000000000 : ℝ) := by
  norm_num [wT, cS, Finset.sum_range_succ, cT]

theorem wT_val11 : wT 11 = (51538073291163213039 / 488281250000000000000 : ℝ) := by
  norm_num [wT, cS, Finset.sum_range_succ, cT]

theorem wT_val12 : wT 12 = (19175309507686616048151 / 200000000000000000000000 : ℝ) := by
  norm_num [wT, cS, Finset.sum_range_succ, cT]

theorem wT_val13 : wT 13 = (19242580043687170786687 / 250000000000000000000000 : ℝ) := by
  norm_num [wT, cS, Finset.sum_range_succ, cT]

theorem wT_val14 : wT 14 = (11013044231138638563501 / 200000000000000000000000 : ℝ) := by
  norm_num [wT, cS, Finset.sum_range_succ, cT]

theorem wT_val15 : wT 15 = (10989784666189711879071 / 1000000000000000000000000 : ℝ) := by
  norm_num [wT, cS, Finset.sum_range_succ, cT]

/-- `log α = log(3/40) = log(6/5) - 4 log 2`, certified. -/
theorem log_alpha_bounds : (-259026716544582661147 / 100000000000000000000 : ℝ) < Real.log ((alpha : ℝ))
    ∧ Real.log ((alpha : ℝ)) < (-129513358272291330571 / 50000000000000000000 : ℝ) := by
  have hv : ((alpha : ℝ)) = (6 / 5 : ℝ) / 2 ^ (4 : ℕ) := by norm_num [alpha]
  rw [hv, Real.log_div (by norm_num) (by positivity), Real.log_pow]
  have h := Real.abs_log_sub_add_sum_range_le (x := (1 : ℝ) - 6 / 5) (by norm_num) 35
  rw [show (1 : ℝ) - ((1 : ℝ) - 6 / 5) = (6 / 5 : ℝ) by ring, abs_le] at h
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith [h.1, h.2, log_two_bounds.1, log_two_bounds.2]

/-- `log(2λ) = log(37/20) = log(37/40) + log 2`, certified. -/
theorem log_twolam_bounds : (15379640977255836273 / 25000000000000000000 : ℝ) < Real.log (2 * (lam : ℝ))
    ∧ Real.log (2 * (lam : ℝ)) < (30759281954511672547 / 50000000000000000000 : ℝ) := by
  have hv : 2 * ((lam : ℝ)) = (37 / 40 : ℝ) * 2 ^ (1 : ℕ) := by norm_num [lam]
  rw [hv, Real.log_mul (by norm_num) (by positivity), Real.log_pow]
  have h := Real.abs_log_sub_add_sum_range_le (x := (1 : ℝ) - 37 / 40) (by norm_num) 35
  rw [show (1 : ℝ) - ((1 : ℝ) - 37 / 40) = (37 / 40 : ℝ) by ring, abs_le] at h
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith [h.1, h.2, log_two_bounds.1, log_two_bounds.2]

/-- **(A.10)**, first line (p. 26):
`-2126593445148/10¹² < I(ρ) < -2126593445147/10¹²`.

Known-answer control (audit, two independent computations):
`I(ρ) = -2.126593445147050403253600969…`. -/
theorem A10_Irho : (-2126593445148 / 10 ^ 12 : ℝ) < Irho
    ∧ Irho < (-2126593445147 / 10 ^ 12 : ℝ) := by
  simp only [Irho, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    wT_val0, wT_val1, wT_val2, wT_val3, wT_val4, wT_val5, wT_val6, wT_val7,
    wT_val8, wT_val9, wT_val10, wT_val11, wT_val12, wT_val13, wT_val14, wT_val15]
  constructor <;>
    linarith [logLen0.1, logLen0.2, logLen1.1, logLen1.2, logLen2.1, logLen2.2,
      logLen3.1, logLen3.2, logLen4.1, logLen4.2, logLen5.1, logLen5.2,
      logLen6.1, logLen6.2, logLen7.1, logLen7.2, logLen8.1, logLen8.2,
      logLen9.1, logLen9.2, logLen10.1, logLen10.2, logLen11.1, logLen11.2,
      logLen12.1, logLen12.2, logLen13.1, logLen13.2, logLen14.1, logLen14.2,
      logLen15.1, logLen15.2]

/-- **(A.10)**, second line (p. 26):
`2653035990340/10¹² < C_* < 2653035990341/10¹²`.

Known-answer control: `C_* = 2.653035990340488661129250336…`. -/
theorem A10_Cstar : (2653035990340 / 10 ^ 12 : ℝ) < Cstar
    ∧ Cstar < (2653035990341 / 10 ^ 12 : ℝ) := by
  have h1 := log_alpha_bounds
  have h2 := log_twolam_bounds
  simp only [Cstar, lam, alpha] at *
  constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2]

/-- **(6.4)** (p. 17), the conclusion of Lemma 6.1 that Proposition 6.3 uses:
`λM₀ - I(ρ) + C_* ≤ Ū = -2733991/2000000 < -136699/100000`.

`λM₀ = -49173/8000` exactly (p. 26). -/
theorem eq_6_4 : (lam : ℝ) * M0 - Irho + Cstar ≤ (Ubar : ℝ) := by
  have h1 := A10_Irho.1
  have h2 := A10_Cstar.2
  simp only [lam, M0, Ubar] at *
  push_cast at *
  linarith

/-- The second half of (6.4): `Ū < -136699/100000`. -/
theorem Ubar_lt : (Ubar : ℝ) < -136699 / 100000 := by
  norm_num [Ubar]

/-- `λM₀ = -49173/8000`, the exact rational of p. 26. -/
theorem lam_mul_M0 : (lam : ℝ) * M0 = -49173 / 8000 := by
  norm_num [lam, M0]

/-! ## §6.1  The regularisation constant `60√ε`

p. 19: "A unit arcsine measure on an interval of length `L` assigns at most
`4√(2r)/(π√L)` to the intersection with any interval of radius `r`. … Integrating the
preceding mass bound in `r` therefore gives
`∫U^ρ dω_i - U^ρ(t_i) ≤ ∑_j 8c_j√(2ε)/(π√(b_j-a_j)) ≤ 60√ε`."

The second inequality is a finite verification, and it is **the only place where the
hypothesis `b_j - a_j > 1/225` of Lemma 6.1 is used**.  The audit's value for the exact
sum is `9.4247`; the crude bound below gives `49.968 ≤ 60`. -/

/-- `√(b_j - a_j) > 1/15` for every `j`, from `b_j - a_j > 1/225` (`tab1_length`). -/
theorem sqrt_len_gt : ∀ j < 16, (1 : ℝ) / 15 < Real.sqrt (bT j - aT j) := by
  intro j hj
  have h := tab1_length j hj
  have h0 : (0 : ℝ) ≤ 1 / 15 := by norm_num
  rw [show (1 : ℝ) / 15 = Real.sqrt ((1 / 15) ^ 2) by
    rw [Real.sqrt_sq (by norm_num)]]
  exact Real.sqrt_lt_sqrt (by positivity) (by linarith)

/-- **`∑_j 8c_j√2/(π√(b_j-a_j)) ≤ 60`** (p. 19), the constant of the regularisation
bound `(6.6)`.  Uses `b_j - a_j > 1/225` and `∑ c_j = λ = 37/40`, together with
`√2 < 1.41422` and `π > 3.141592`. -/
theorem reg_const_le_sixty :
    ∑ j ∈ range 16, 8 * cT j * Real.sqrt 2 / (Real.pi * Real.sqrt (bT j - aT j)) ≤ 60 := by
  have hpi : (3.141592 : ℝ) < Real.pi := Real.pi_gt_d6
  have hs2 : Real.sqrt 2 < 1.41422 := by
    have : Real.sqrt 2 < Real.sqrt (1.41422 ^ 2) := by
      apply Real.sqrt_lt_sqrt (by norm_num); norm_num
    rwa [Real.sqrt_sq (by norm_num)] at this
  have hterm : ∀ j ∈ range 16,
      8 * cT j * Real.sqrt 2 / (Real.pi * Real.sqrt (bT j - aT j)) ≤ 55 * cT j := by
    intro j hj
    have hj' : j < 16 := Finset.mem_range.1 hj
    have hc : 0 < cT j := cT_pos j hj'
    have hsq : (1 : ℝ) / 15 < Real.sqrt (bT j - aT j) := sqrt_len_gt j hj'
    have hden : (0 : ℝ) < Real.pi * Real.sqrt (bT j - aT j) := by
      have := Real.pi_pos; nlinarith
    have h1 : (3.141592 : ℝ) * (1 / 15) ≤ Real.pi * Real.sqrt (bT j - aT j) :=
      mul_le_mul hpi.le hsq.le (by norm_num) (le_of_lt Real.pi_pos)
    rw [div_le_iff₀ hden]
    have h2 := mul_le_mul_of_nonneg_left hs2.le hc.le
    have h3 := mul_le_mul_of_nonneg_left h1 hc.le
    nlinarith [h2, h3, hc.le]
  calc ∑ j ∈ range 16, 8 * cT j * Real.sqrt 2 / (Real.pi * Real.sqrt (bT j - aT j))
      ≤ ∑ j ∈ range 16, 55 * cT j := Finset.sum_le_sum hterm
    _ = 55 * ∑ j ∈ range 16, cT j := by rw [Finset.mul_sum]
    _ = 55 * (lam : ℝ) := by rw [sum_cT]
    _ ≤ 60 := by norm_num [lam]

/-! ## §6.3  Proposition 6.3 from (6.14) and (6.15)

"The `K² log K` terms in (6.14) and (6.15) cancel.  The remaining quadratic coefficient
is `λM₀ - I(ρ) + C_*`, bounded by `Ū` in Lemma 6.1." (p. 20) -/

/-- The cancellation asserted on p. 20, **exactly**:
`2h(h + 6N - K) + (2λ - 12αλ - 2λ²)K² = 1110n² - 1110n² = 0`.

(Equivalently `2λ(λ + 6α - 1) = 111/160` is the `K²log K` coefficient of (6.14) and
`-(111/160)` that of (6.15); the audit records the same identity.) -/
theorem K2logK_cancel (n : ℕ) :
    2 * (h n : ℝ) * ((h n : ℝ) + 6 * (N n : ℝ) - (K n : ℝ))
      + (2 * (lam : ℝ) - 12 * (alpha : ℝ) * (lam : ℝ) - 2 * (lam : ℝ) ^ 2)
          * (K n : ℝ) ^ 2 = 0 := by
  simp only [h, K, N, lam, alpha]
  push_cast
  ring

/-- **Proposition 6.3**, (6.16) (p. 20), from its two inputs (6.14) and (6.15).

`h14` is (6.14), the bound on `log Δ_K(ζ(5))` coming from the Gram integral (6.10), the
elementary bounds (6.11)–(6.12), the scaling (6.13) and the configuration bound (6.9).
`h15` is (6.15), the factorial estimate for `log S_K`.  Everything else — the exact
cancellation of the `K²log K` terms, the passage from `λM₀ - I(ρ) + C_*` to `Ū`
(this is `eq_6_4`, proved above from Table 1), and the enlargements
`24h log K ≤ 24K log K`, `166h ≤ 200K` — is proved here. -/
theorem prop_6_3_of (n : ℕ) (hn : 0 < n) (hΔpos : 0 < evalZeta5 (Delta n))
    (h14 : Real.log (evalZeta5 (Delta n))
        ≤ 2 * (h n : ℝ) * ((h n : ℝ) + 6 * (N n : ℝ) - (K n : ℝ)) * Real.log (K n : ℝ)
          + ((lam : ℝ) * M0 - Irho) * (K n : ℝ) ^ 2
          + 18 * (h n : ℝ) * Real.log (K n : ℝ) + 160 * (h n : ℝ))
    (h15 : Real.log ((S n : ℝ))
        ≤ (2 * (lam : ℝ) - 12 * (alpha : ℝ) * (lam : ℝ) - 2 * (lam : ℝ) ^ 2)
              * (K n : ℝ) ^ 2 * Real.log (K n : ℝ)
          + Cstar * (K n : ℝ) ^ 2
          + 6 * (h n : ℝ) * Real.log (K n : ℝ) + 6 * (h n : ℝ)) :
    Real.log (evalZeta5 (F n))
      ≤ (Ubar : ℝ) * (K n : ℝ) ^ 2 + 24 * (K n : ℝ) * Real.log (K n : ℝ)
        + 200 * (K n : ℝ) := by
  have hS : (0 : ℝ) < (S n : ℝ) := by exact_mod_cast S_pos n
  have hFeq : evalZeta5 (F n) = (S n : ℝ) * evalZeta5 (Delta n) := by
    rw [F, evalZeta5_mul, evalZeta5_C]
  rw [hFeq, Real.log_mul (ne_of_gt hS) (ne_of_gt hΔpos)]
  have hx1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hK : (K n : ℝ) = 40 * (n : ℝ) := by simp only [K]; push_cast; ring
  have hN : (N n : ℝ) = 3 * (n : ℝ) := by simp only [N]; push_cast; ring
  have hh : (h n : ℝ) = 37 * (n : ℝ) := by simp only [h]; push_cast; ring
  have hlogK : 0 ≤ Real.log (K n : ℝ) := Real.log_nonneg (by rw [hK]; linarith)
  have hK2 : (0 : ℝ) ≤ (K n : ℝ) ^ 2 := sq_nonneg _
  have e1 : ((lam : ℝ) * M0 - Irho + Cstar) * (K n : ℝ) ^ 2
      ≤ (Ubar : ℝ) * (K n : ℝ) ^ 2 := mul_le_mul_of_nonneg_right eq_6_4 hK2
  have e2 : (0 : ℝ) ≤ (n : ℝ) * Real.log (K n : ℝ) :=
    mul_nonneg (by linarith) hlogK
  simp only [hK, hN, hh] at h14 h15 e1 e2 hlogK ⊢
  simp only [lam, alpha] at h14 h15 e1
  push_cast at h14 h15 e1 ⊢
  linarith [h14, h15, e1, e2, hx1, hlogK]

/-! ## §6.2  The factorial estimates of p. 20

"The factorial inequalities `m log m - m + 1 ≤ log(m!) ≤ m log m - m + log m + 2`
and summation of `log((2i)!)` give `-2∑_{i=1}^{h-1} log((2i)!) ≤ -2h²log(2h) + 3h² +
4h log(2h)`."  All three are proved here by induction; no Stirling formula is needed. -/

/-- `log x ≥ 1 - 1/x` for `x > 0`. -/
theorem one_sub_inv_le_log {x : ℝ} (hx : 0 < x) : 1 - 1 / x ≤ Real.log x := by
  have h := Real.log_le_sub_one_of_pos (x := 1 / x) (by positivity)
  rw [one_div, Real.log_inv] at h
  have : (1 : ℝ) / x = x⁻¹ := one_div x
  linarith [h]

/-- `m log m - m + 1 ≤ log (m !)` for `m ≥ 1` (p. 20). -/
theorem log_factorial_ge : ∀ m : ℕ, 1 ≤ m →
    (m : ℝ) * Real.log m - m + 1 ≤ Real.log (m.factorial) := by
  intro m
  induction m with
  | zero => intro h; omega
  | succ k ih =>
    intro _
    rcases Nat.eq_or_lt_of_le (Nat.one_le_iff_ne_zero.2 (Nat.succ_ne_zero k)) with h1 | h1
    · -- k + 1 = 1
      have hk : k = 0 := by omega
      subst hk; norm_num
    · have hk1 : 1 ≤ k := by omega
      have hkpos : (0 : ℝ) < k := by exact_mod_cast hk1
      have hih := ih hk1
      have hfac : ((k + 1).factorial : ℝ) = ((k : ℝ) + 1) * (k.factorial : ℝ) := by
        rw [Nat.factorial_succ]; push_cast; ring
      have hpos1 : (0 : ℝ) < (k : ℝ) + 1 := by linarith
      have hpos2 : (0 : ℝ) < (k.factorial : ℝ) := by
        exact_mod_cast Nat.factorial_pos k
      rw [hfac, Real.log_mul (ne_of_gt hpos1) (ne_of_gt hpos2)]
      -- need : k*(log(k+1)-log k) ≤ 1
      have hkey : Real.log ((k : ℝ) + 1) - Real.log k ≤ 1 / k := by
        have := Real.log_le_sub_one_of_pos (x := ((k : ℝ) + 1) / k) (by positivity)
        rw [Real.log_div (ne_of_gt hpos1) (ne_of_gt hkpos)] at this
        have he : ((k : ℝ) + 1) / k - 1 = 1 / k := by field_simp; ring
        linarith [this, he]
      have hmul : (k : ℝ) * (Real.log ((k : ℝ) + 1) - Real.log k) ≤ 1 := by
        have := mul_le_mul_of_nonneg_left hkey hkpos.le
        rw [mul_one_div, div_self (ne_of_gt hkpos)] at this
        linarith
      push_cast
      linarith [hih, hmul]

/-- `log (m !) ≤ m log m - m + log m + 2` for `m ≥ 1` (p. 20). -/
theorem log_factorial_le : ∀ m : ℕ, 1 ≤ m →
    Real.log (m.factorial) ≤ (m : ℝ) * Real.log m - m + Real.log m + 2 := by
  intro m
  induction m with
  | zero => intro h; omega
  | succ k ih =>
    intro _
    rcases Nat.eq_or_lt_of_le (Nat.one_le_iff_ne_zero.2 (Nat.succ_ne_zero k)) with h1 | h1
    · have hk : k = 0 := by omega
      subst hk; norm_num
    · have hk1 : 1 ≤ k := by omega
      have hkpos : (0 : ℝ) < k := by exact_mod_cast hk1
      have hih := ih hk1
      have hfac : ((k + 1).factorial : ℝ) = ((k : ℝ) + 1) * (k.factorial : ℝ) := by
        rw [Nat.factorial_succ]; push_cast; ring
      have hpos1 : (0 : ℝ) < (k : ℝ) + 1 := by linarith
      have hpos2 : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
      rw [hfac, Real.log_mul (ne_of_gt hpos1) (ne_of_gt hpos2)]
      -- need : 1 ≤ (k+1)(log(k+1) - log k)
      have hkey : 1 / ((k : ℝ) + 1) ≤ Real.log ((k : ℝ) + 1) - Real.log k := by
        have := one_sub_inv_le_log (x := ((k : ℝ) + 1) / k) (by positivity)
        rw [Real.log_div (ne_of_gt hpos1) (ne_of_gt hkpos)] at this
        have he : (1 : ℝ) - 1 / (((k : ℝ) + 1) / k) = 1 / ((k : ℝ) + 1) := by
          field_simp; ring
        linarith [this, he]
      have hmul : 1 ≤ ((k : ℝ) + 1) * (Real.log ((k : ℝ) + 1) - Real.log k) := by
        have := mul_le_mul_of_nonneg_left hkey hpos1.le
        rw [mul_one_div, div_self (ne_of_gt hpos1)] at this
        linarith
      push_cast
      nlinarith [hih, hmul]

/-- `∑_{i=1}^{m} log((2i)!) ≥ (H² - 2H) log(2H) - (3/2)H²` with `H = m+1`;
i.e. `-2∑_{i=1}^{h-1} log((2i)!) ≤ -2h²log(2h) + 3h² + 4h log(2h)` (p. 20). -/
theorem sum_log_fact : ∀ m : ℕ,
    (((m : ℝ) + 1) ^ 2 - 2 * ((m : ℝ) + 1)) * Real.log (2 * ((m : ℝ) + 1))
        - (3 / 2) * ((m : ℝ) + 1) ^ 2
      ≤ ∑ i ∈ Finset.Icc 1 m, Real.log ((2 * i).factorial) := by
  intro m
  induction m with
  | zero =>
    simp only [Nat.cast_zero, zero_add]
    norm_num
    have : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    linarith
  | succ k ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ k + 1)]
    set H : ℝ := (k : ℝ) + 1 with hHdef
    have hH1 : (1 : ℝ) ≤ H := by
      rw [hHdef]; have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k; linarith
    have hHpos : (0 : ℝ) < H := by linarith
    have hfac := log_factorial_ge (2 * (k + 1)) (by omega)
    have hcast : ((2 * (k + 1) : ℕ) : ℝ) = 2 * H := by rw [hHdef]; push_cast; ring
    rw [hcast] at hfac
    have hlog1 : Real.log (2 * (H + 1)) - Real.log (2 * H) ≤ 1 / H := by
      have hx := Real.log_le_sub_one_of_pos (x := (2 * (H + 1)) / (2 * H)) (by positivity)
      rw [Real.log_div (by positivity) (by positivity)] at hx
      have he : (2 * (H + 1)) / (2 * H) - 1 = 1 / H := by field_simp; ring
      linarith
    have hmul : H ^ 2 * (Real.log (2 * (H + 1)) - Real.log (2 * H)) ≤ H := by
      have hx := mul_le_mul_of_nonneg_left hlog1 (by positivity : (0 : ℝ) ≤ H ^ 2)
      have he : H ^ 2 * (1 / H) = H := by field_simp
      linarith
    have hpos : 0 < Real.log (2 * (H + 1)) := Real.log_pos (by linarith)
    have hgoal : ((k : ℝ) + 1 + 1) = H + 1 := by rw [hHdef]
    push_cast
    rw [hgoal]
    linarith [ih, hfac, hmul, hpos]

/-! ## §6.2  Equation (6.15)

"It follows from (2.5) that
`log S_K ≤ (2λ - 12αλ - 2λ²)K² log K + C_*K² + 6h log K + 6h`." (p. 20) -/

/-- The decomposition of `log S_K` from (2.5). -/
theorem log_S_eq (n : ℕ) (hn : 0 < n) :
    Real.log ((S n : ℝ))
      = 2 * (h n : ℝ) * Real.log ((K n).factorial : ℝ)
        + ((h n : ℝ) - 1) * (2 * Real.log 2)
        - 12 * (h n : ℝ) * Real.log ((N n).factorial : ℝ)
        - 2 * ∑ i ∈ Finset.Icc 1 (h n - 1), Real.log (((2 * i).factorial : ℝ)) := by
  have hh1 : 1 ≤ h n := by simp only [h]; omega
  have hKf : (0 : ℝ) < ((K n).factorial : ℝ) := by exact_mod_cast (K n).factorial_pos
  have hNf : (0 : ℝ) < ((N n).factorial : ℝ) := by exact_mod_cast (N n).factorial_pos
  have hff : ∀ i ∈ Finset.Icc 1 (h n - 1), (0 : ℝ) < (((2 * i).factorial : ℕ) : ℝ) := by
    intro i _; exact_mod_cast (2 * i).factorial_pos
  have hprod : (0 : ℝ) < ∏ i ∈ Finset.Icc 1 (h n - 1), (((2 * i).factorial : ℝ)) ^ 2 :=
    Finset.prod_pos (fun i hi => pow_pos (hff i hi) 2)
  have hSval : ((S n : ℚ) : ℝ)
      = ((K n).factorial : ℝ) ^ (2 * h n) * 4 ^ (h n - 1)
        / (((N n).factorial : ℝ) ^ (12 * h n)
            * ∏ i ∈ Finset.Icc 1 (h n - 1), (((2 * i).factorial : ℝ)) ^ 2) := by
    rw [S]; push_cast; ring
  have hnum : (0 : ℝ) < ((K n).factorial : ℝ) ^ (2 * h n) * 4 ^ (h n - 1) := by positivity
  have hden : (0 : ℝ) < ((N n).factorial : ℝ) ^ (12 * h n)
      * ∏ i ∈ Finset.Icc 1 (h n - 1), (((2 * i).factorial : ℝ)) ^ 2 :=
    mul_pos (pow_pos hNf _) hprod
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]; norm_num
  rw [hSval, Real.log_div (ne_of_gt hnum) (ne_of_gt hden),
    Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (ne_of_gt hprod),
    Real.log_prod (fun i hi => ne_of_gt (pow_pos (hff i hi) 2))]
  simp only [Real.log_pow, ← Finset.mul_sum]
  rw [h4]
  have hc : ((h n - 1 : ℕ) : ℝ) = (h n : ℝ) - 1 := by
    have := Nat.cast_sub (R := ℝ) hh1; simpa using this
  rw [hc]
  push_cast
  ring

/-- **(6.15)** (p. 20).  `log S_K ≤ (2λ - 12αλ - 2λ²)K² log K + C_*K² + 6h log K + 6h`.

The `K²` coefficient is **exactly** `C_*` of (6.3): the audit records the same symbolic
identity (`the K² coefficient of (6.15) is exactly C_* of (6.3), symbolic difference 0`).
Proved here from (2.5), the two factorial inequalities and `sum_log_fact`, with
`log N = log α + log K` and `log 2h = log 2λ + log K`. -/
theorem eq_6_15 (n : ℕ) (hn : 0 < n) :
    Real.log ((S n : ℝ))
      ≤ (2 * (lam : ℝ) - 12 * (alpha : ℝ) * (lam : ℝ) - 2 * (lam : ℝ) ^ 2)
            * (K n : ℝ) ^ 2 * Real.log (K n : ℝ)
        + Cstar * (K n : ℝ) ^ 2
        + 6 * (h n : ℝ) * Real.log (K n : ℝ) + 6 * (h n : ℝ) := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hK : ((K n : ℕ) : ℝ) = 40 * (n : ℝ) := by simp only [K]; push_cast; ring
  have hN : ((N n : ℕ) : ℝ) = 3 * (n : ℝ) := by simp only [N]; push_cast; ring
  have hh : ((h n : ℕ) : ℝ) = 37 * (n : ℝ) := by simp only [h]; push_cast; ring
  have hh1 : 1 ≤ h n := by simp only [h]; omega
  have hKpos : (0 : ℝ) < ((K n : ℕ) : ℝ) := by rw [hK]; linarith
  -- `log N = log α + log K` and `log 2h = log 2λ + log K`
  have hNK : ((N n : ℕ) : ℝ) = ((alpha : ℝ)) * ((K n : ℕ) : ℝ) := by
    rw [hN, hK]; simp only [alpha]; push_cast; ring
  have hlogN : Real.log ((N n : ℕ) : ℝ)
      = Real.log ((alpha : ℝ)) + Real.log ((K n : ℕ) : ℝ) := by
    rw [hNK, Real.log_mul (by norm_num [alpha]) (ne_of_gt hKpos)]
  have h2hK : 2 * ((h n : ℕ) : ℝ) = (2 * (lam : ℝ)) * ((K n : ℕ) : ℝ) := by
    rw [hh, hK]; simp only [lam]; push_cast; ring
  have hlog2h : Real.log (2 * ((h n : ℕ) : ℝ))
      = Real.log (2 * (lam : ℝ)) + Real.log ((K n : ℕ) : ℝ) := by
    rw [h2hK, Real.log_mul (by norm_num [lam]) (ne_of_gt hKpos)]
  -- the three estimates, multiplied by their (nonnegative) coefficients
  have hKfac := log_factorial_le (K n) (by simp only [K]; omega)
  have hNfac := log_factorial_ge (N n) (by simp only [N]; omega)
  have hSum := sum_log_fact (h n - 1)
  have hhc : ((h n - 1 : ℕ) : ℝ) + 1 = ((h n : ℕ) : ℝ) := by
    rw [Nat.cast_sub hh1]; ring
  rw [hhc] at hSum
  rw [hlogN] at hNfac
  rw [hlog2h] at hSum
  have e1 : 2 * ((h n : ℕ) : ℝ) * Real.log ((K n).factorial : ℝ)
      ≤ 2 * ((h n : ℕ) : ℝ) * (((K n : ℕ) : ℝ) * Real.log ((K n : ℕ) : ℝ)
          - ((K n : ℕ) : ℝ) + Real.log ((K n : ℕ) : ℝ) + 2) :=
    mul_le_mul_of_nonneg_left hKfac (by positivity)
  have e2 : 12 * ((h n : ℕ) : ℝ) * (((N n : ℕ) : ℝ)
        * (Real.log ((alpha : ℝ)) + Real.log ((K n : ℕ) : ℝ)) - ((N n : ℕ) : ℝ) + 1)
      ≤ 12 * ((h n : ℕ) : ℝ) * Real.log ((N n).factorial : ℝ) :=
    mul_le_mul_of_nonneg_left hNfac (by positivity)
  -- numeric inputs
  have hL2 := log_two_bounds.2
  have hL2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hLL := log_twolam_bounds.2
  have f1 : (n : ℝ) * Real.log 2 ≤ (n : ℝ) * 0.6931472 :=
    mul_le_mul_of_nonneg_left (by norm_num at hL2 ⊢; linarith) (by linarith)
  have f2 : (n : ℝ) * Real.log (2 * (lam : ℝ)) ≤ (n : ℝ) * 0.6151857 :=
    mul_le_mul_of_nonneg_left (by norm_num at hLL ⊢; linarith) (by linarith)
  rw [log_S_eq n hn]
  simp only [Cstar]
  simp only [hK, hN, hh] at e1 e2 hSum f1 f2 ⊢
  simp only [lam, alpha] at e1 e2 hSum f1 f2 ⊢
  push_cast at e1 e2 hSum f1 f2 ⊢
  nlinarith [e1, e2, hSum, f1, f2, hL2pos, hn1]

/-! ## §6.2  (6.14) and Proposition 6.3

`eq_6_14` ((6.14), p. 20) and `prop_6_3` ((6.16), p. 20) are stated and proved in
`Zeta5/Sec6/Final.lean`, with the same names (`Zeta5.RealBound.eq_6_14`,
`Zeta5.RealBound.prop_6_3`) and types as they had here.  `prop_6_3` is
`prop_6_3_of n hn hΔpos (eq_6_14 n hn hΔpos) (eq_6_15 n hn)`. -/

/-! ## A.3  Table 2 (pp. 24–25): the 684 dyadic cells

"Define `A₀ = 0`, `A_j = a_{17-j}` (`1 ≤ j ≤ 16`), `A₁₇ = q₋`, `A₁₈ = q₊`,
`A_{18+j} = b_j` (`1 ≤ j ≤ 16`), `A₃₅ = 2`.  A row `(j,d,k)` in Table 2 denotes
`[A_j + (A_{j+1}-A_j)k/2^d, A_j + (A_{j+1}-A_j)(k+1)/2^d]`. … These intervals partition
`[0,2]`." (pp. 23–24)

Both halves of "partition `[0,2]`" are proved here: the endpoints `A_j` increase from `0`
to `2` (`AA_strictMono`, `AA_zero`, `AA_last`), and for each of the 35 gaps the listed
dyadic cells tile `[0,1]` in order (`table2_tiles`).  What is *not* proved is (A.9),
the inequality `ℬ(l,r) < -6645002/10⁶` on each cell: the formalisation proves (6.2) by its own
certified partition instead (`Zeta5/Sec6/Num/`). -/

/-- `q₋ = 59205077/10¹⁰` of p. 23. -/
def qminus : ℝ := 59205077 / 10 ^ 10

/-- `q₊ = 59205079/10¹⁰` of p. 23. -/
def qplus : ℝ := 59205079 / 10 ^ 10

/-- The 36 endpoints `A_0, …, A_{35}` of the partition (p. 23). -/
def AA : ℕ → ℝ
  | 0 => 0
  | 1 => aT 15
  | 2 => aT 14
  | 3 => aT 13
  | 4 => aT 12
  | 5 => aT 11
  | 6 => aT 10
  | 7 => aT 9
  | 8 => aT 8
  | 9 => aT 7
  | 10 => aT 6
  | 11 => aT 5
  | 12 => aT 4
  | 13 => aT 3
  | 14 => aT 2
  | 15 => aT 1
  | 16 => aT 0
  | 17 => qminus
  | 18 => qplus
  | 19 => bT 0
  | 20 => bT 1
  | 21 => bT 2
  | 22 => bT 3
  | 23 => bT 4
  | 24 => bT 5
  | 25 => bT 6
  | 26 => bT 7
  | 27 => bT 8
  | 28 => bT 9
  | 29 => bT 10
  | 30 => bT 11
  | 31 => bT 12
  | 32 => bT 13
  | 33 => bT 14
  | 34 => bT 15
  | 35 => 2
  | _ => 0

@[simp] theorem AA_zero : AA 0 = 0 := rfl

@[simp] theorem AA_last : AA 35 = 2 := rfl

/-- `0 = A₀ < A₁ < ⋯ < A₃₅ = 2`: the endpoints of (A.8) are strictly increasing.
The three nontrivial comparisons beyond Table 1's nesting are `a₁ < q₋`, `q₊ < b₁` and
`b₁₆ < 2`. -/
theorem AA_strictMono : ∀ j, j + 1 < 36 → AA j < AA (j + 1) := by
  intro j hj
  have hj' : j < 35 := by omega
  interval_cases j <;> norm_num [AA, aT, bT, qminus, qplus]

/-- The rows of Table 2, gap by gap, ordered by left endpoint: `(d, k)` denotes the
dyadic interval `[k/2^d, (k+1)/2^d]` of the normalised gap. -/
def t2 : ℕ → List (ℕ × ℕ)
  | 0 => [(1, 0), (2, 2), (2, 3)]
  | 1 => [(0, 0)]
  | 2 => [(0, 0)]
  | 3 => [(0, 0)]
  | 4 => [(0, 0)]
  | 5 => [(0, 0)]
  | 6 => [(0, 0)]
  | 7 => [(0, 0)]
  | 8 => [(0, 0)]
  | 9 => [(1, 0), (1, 1)]
  | 10 => [(1, 0), (1, 1)]
  | 11 => [(1, 0), (1, 1)]
  | 12 => [(1, 0), (2, 2), (2, 3)]
  | 13 => [(2, 0), (2, 1), (2, 2), (2, 3)]
  | 14 => [(2, 0), (2, 1), (2, 2), (2, 3)]
  | 15 => [(1, 0), (2, 2), (2, 3)]
  | 16 => [(0, 0)]
  | 17 => [(0, 0)]
  | 18 => [(0, 0)]
  | 19 => [(3, 0), (4, 2), (4, 3), (3, 2), (3, 3), (1, 1)]
  | 20 => [(4, 0), (4, 1), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (4, 6), (4, 7), (3, 4), (3, 5), (2, 3)]
  | 21 => [(4, 0), (5, 2), (5, 3), (5, 4), (6, 10), (6, 11), (6, 12), (6, 13), (6, 14), (6, 15), (6, 16), (6, 17), (6, 18), (6, 19), (5, 10), (5, 11), (5, 12), (5, 13), (4, 7), (4, 8), (4, 9), (3, 5), (2, 3)]
  | 22 => [(4, 0), (5, 2), (5, 3), (6, 8), (6, 9), (6, 10), (6, 11), (6, 12), (6, 13), (6, 14), (6, 15), (6, 16), (6, 17), (6, 18), (6, 19), (6, 20), (6, 21), (6, 22), (6, 23), (5, 12), (5, 13), (5, 14), (5, 15), (4, 8), (4, 9), (3, 5), (3, 6), (3, 7)]
  | 23 => [(5, 0), (5, 1), (5, 2), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11), (6, 12), (6, 13), (7, 28), (7, 29), (7, 30), (7, 31), (7, 32), (7, 33), (7, 34), (7, 35), (7, 36), (7, 37), (6, 19), (6, 20), (6, 21), (6, 22), (6, 23), (6, 24), (6, 25), (6, 26), (6, 27), (5, 14), (5, 15), (5, 16), (5, 17), (4, 9), (4, 10), (4, 11), (3, 6), (3, 7)]
  | 24 => [(5, 0), (5, 1), (5, 2), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11), (7, 24), (7, 25), (7, 26), (7, 27), (7, 28), (7, 29), (7, 30), (7, 31), (7, 32), (7, 33), (7, 34), (7, 35), (7, 36), (7, 37), (7, 38), (7, 39), (7, 40), (7, 41), (7, 42), (7, 43), (6, 22), (6, 23), (6, 24), (6, 25), (6, 26), (6, 27), (6, 28), (6, 29), (5, 15), (5, 16), (5, 17), (5, 18), (5, 19), (4, 10), (4, 11), (3, 6), (3, 7)]
  | 25 => [(5, 0), (5, 1), (5, 2), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11), (7, 24), (7, 25), (7, 26), (7, 27), (7, 28), (7, 29), (7, 30), (7, 31), (7, 32), (7, 33), (7, 34), (7, 35), (7, 36), (7, 37), (7, 38), (7, 39), (7, 40), (7, 41), (7, 42), (7, 43), (7, 44), (7, 45), (7, 46), (7, 47), (6, 24), (6, 25), (6, 26), (6, 27), (6, 28), (6, 29), (6, 30), (6, 31), (5, 16), (5, 17), (5, 18), (5, 19), (4, 10), (4, 11), (4, 12), (4, 13), (3, 7)]
  | 26 => [(5, 0), (5, 1), (5, 2), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11), (7, 24), (7, 25), (7, 26), (7, 27), (7, 28), (7, 29), (7, 30), (7, 31), (7, 32), (7, 33), (7, 34), (7, 35), (7, 36), (7, 37), (7, 38), (7, 39), (7, 40), (7, 41), (7, 42), (7, 43), (7, 44), (7, 45), (7, 46), (7, 47), (7, 48), (7, 49), (6, 25), (6, 26), (6, 27), (6, 28), (6, 29), (6, 30), (6, 31), (6, 32), (6, 33), (5, 17), (5, 18), (5, 19), (5, 20), (5, 21), (4, 11), (4, 12), (4, 13), (3, 7)]
  | 27 => [(5, 0), (5, 1), (5, 2), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11), (7, 24), (7, 25), (7, 26), (7, 27), (7, 28), (7, 29), (7, 30), (7, 31), (7, 32), (7, 33), (7, 34), (7, 35), (7, 36), (7, 37), (7, 38), (7, 39), (7, 40), (7, 41), (7, 42), (7, 43), (7, 44), (7, 45), (7, 46), (7, 47), (7, 48), (7, 49), (7, 50), (7, 51), (6, 26), (6, 27), (6, 28), (6, 29), (6, 30), (6, 31), (6, 32), (6, 33), (5, 17), (5, 18), (5, 19), (5, 20), (5, 21), (4, 11), (4, 12), (4, 13), (4, 14), (4, 15)]
  | 28 => [(5, 0), (5, 1), (5, 2), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11), (7, 24), (7, 25), (7, 26), (7, 27), (7, 28), (7, 29), (7, 30), (7, 31), (7, 32), (7, 33), (7, 34), (7, 35), (7, 36), (7, 37), (7, 38), (7, 39), (7, 40), (7, 41), (7, 42), (7, 43), (7, 44), (7, 45), (7, 46), (7, 47), (7, 48), (7, 49), (7, 50), (7, 51), (7, 52), (7, 53), (6, 27), (6, 28), (6, 29), (6, 30), (6, 31), (6, 32), (6, 33), (6, 34), (6, 35), (5, 18), (5, 19), (5, 20), (5, 21), (5, 22), (5, 23), (4, 12), (4, 13), (4, 14), (4, 15)]
  | 29 => [(5, 0), (5, 1), (5, 2), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11), (6, 12), (7, 26), (7, 27), (7, 28), (7, 29), (7, 30), (7, 31), (7, 32), (7, 33), (7, 34), (7, 35), (7, 36), (7, 37), (7, 38), (7, 39), (7, 40), (7, 41), (7, 42), (7, 43), (7, 44), (7, 45), (7, 46), (7, 47), (7, 48), (7, 49), (7, 50), (7, 51), (7, 52), (7, 53), (6, 27), (6, 28), (6, 29), (6, 30), (6, 31), (6, 32), (6, 33), (6, 34), (6, 35), (6, 36), (6, 37), (5, 19), (5, 20), (5, 21), (5, 22), (5, 23), (5, 24), (5, 25), (4, 13), (4, 14), (4, 15)]
  | 30 => [(5, 0), (5, 1), (5, 2), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11), (6, 12), (6, 13), (6, 14), (7, 30), (7, 31), (7, 32), (7, 33), (7, 34), (7, 35), (7, 36), (7, 37), (7, 38), (7, 39), (7, 40), (7, 41), (7, 42), (7, 43), (7, 44), (7, 45), (7, 46), (7, 47), (7, 48), (7, 49), (7, 50), (7, 51), (6, 26), (6, 27), (6, 28), (6, 29), (6, 30), (6, 31), (6, 32), (6, 33), (6, 34), (6, 35), (6, 36), (6, 37), (6, 38), (6, 39), (5, 20), (5, 21), (5, 22), (5, 23), (5, 24), (5, 25), (4, 13), (4, 14), (4, 15)]
  | 31 => [(5, 0), (5, 1), (5, 2), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11), (6, 12), (6, 13), (6, 14), (6, 15), (6, 16), (6, 17), (6, 18), (6, 19), (6, 20), (6, 21), (6, 22), (6, 23), (6, 24), (6, 25), (6, 26), (6, 27), (6, 28), (6, 29), (6, 30), (6, 31), (6, 32), (6, 33), (6, 34), (6, 35), (6, 36), (6, 37), (6, 38), (6, 39), (5, 20), (5, 21), (5, 22), (5, 23), (5, 24), (5, 25), (5, 26), (5, 27), (4, 14), (4, 15)]
  | 32 => [(5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (6, 10), (6, 11), (6, 12), (6, 13), (6, 14), (6, 15), (6, 16), (6, 17), (6, 18), (6, 19), (6, 20), (6, 21), (6, 22), (6, 23), (6, 24), (6, 25), (6, 26), (6, 27), (6, 28), (6, 29), (6, 30), (6, 31), (6, 32), (6, 33), (6, 34), (6, 35), (6, 36), (6, 37), (5, 19), (5, 20), (5, 21), (5, 22), (5, 23), (5, 24), (5, 25), (5, 26), (5, 27), (5, 28), (5, 29), (4, 15)]
  | 33 => [(4, 0), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (5, 12), (5, 13), (5, 14), (5, 15), (5, 16), (5, 17), (5, 18), (5, 19), (5, 20), (5, 21), (5, 22), (5, 23), (5, 24), (5, 25), (5, 26), (5, 27), (5, 28), (5, 29), (4, 15)]
  | 34 => [(10, 0), (10, 1), (10, 2), (10, 3), (10, 4), (10, 5), (10, 6), (10, 7), (10, 8), (10, 9), (9, 5), (9, 6), (9, 7), (9, 8), (9, 9), (9, 10), (9, 11), (9, 12), (9, 13), (8, 7), (8, 8), (8, 9), (8, 10), (8, 11), (7, 6), (7, 7), (7, 8), (7, 9), (6, 5), (6, 6), (6, 7), (5, 4), (5, 5), (4, 3), (4, 4), (4, 5), (3, 3), (2, 2), (2, 3)]
  | _ => []

/-- Two rows abut: `(k+1)/2^d = k'/2^{d'}`, written without division. -/
def abutB (c c' : ℕ × ℕ) : Bool := (c.2 + 1) * 2 ^ c'.1 == c'.2 * 2 ^ c.1

/-- Every consecutive pair in the list abuts. -/
def chainB : List (ℕ × ℕ) → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => abutB a b && chainB (b :: rest)

/-- A list of rows tiles the normalised gap `[0,1]`: it is nonempty, starts at `0`,
ends at `1`, and every consecutive pair abuts. -/
def tilesUnitB (l : List (ℕ × ℕ)) : Bool :=
  match l with
  | [] => false
  | c :: _ =>
      (c.2 == 0) && ((List.getLastD l (0, 0)).2 + 1 == 2 ^ (List.getLastD l (0, 0)).1)
        && chainB l

/-- **Table 2's cells tile `[0,2]`** (p. 24): for each of the 35 gaps `[A_j, A_{j+1}]`,
the listed dyadic cells cover the normalised gap `[0,1]` exactly, with no overlap and no
hole.  A finite verification, closed by `decide` in exact integer arithmetic. -/
theorem table2_tiles : ∀ j < 35, tilesUnitB (t2 j) = true := by decide

/-- **There are 684 cells** (audit: "684 listed dyadic intervals"). -/
theorem table2_card : ((List.range 35).map (fun j => (t2 j).length)).sum = 684 := by decide

/-- Abutting rows really do abut as real intervals. -/
theorem abut_real {c c' : ℕ × ℕ} (hc : abutB c c' = true) :
    ((c.2 : ℝ) + 1) / 2 ^ c.1 = (c'.2 : ℝ) / 2 ^ c'.1 := by
  have h : ((c.2 + 1) * 2 ^ c'.1 : ℕ) = ((c'.2 * 2 ^ c.1 : ℕ)) := by
    simpa [abutB] using hc
  have h' : ((c.2 : ℝ) + 1) * 2 ^ c'.1 = (c'.2 : ℝ) * 2 ^ c.1 := by exact_mod_cast h
  field_simp at h' ⊢
  linarith

/-! ## §6.2  (6.11): the elementary bound on the weight

`w(y) ≤ 8192(1+y)⁵e^{-2πy}` (`y > 0`), "follows from `∑_{ℓ≥1}ℓ⁴q^ℓ =
q(1+11q+11q²+q³)/(1-q)⁵` and `1 - e^{-u} ≥ u/(1+u)`" (pp. 19–20).

We use the weaker but sufficient `∑_{ℓ≥1}ℓ⁴q^ℓ ≤ 24q/(1-q)⁵`, from
`ℓ⁴ ≤ ℓ(ℓ+1)(ℓ+2)(ℓ+3) = 24·C(ℓ+3,4)` and Mathlib's
`tsum_choose_mul_geometric_of_norm_lt_one`.  The constant this produces is `32π⁴ = 3117.1`,
well below the printed `8192` — the audit records the same (`the author's own route gives
32π⁴ = 3117.09, itself far below 8192`). -/

theorem choose_four_id (l : ℕ) :
    24 * (l + 4).choose 4 = (l + 1) * (l + 2) * (l + 3) * (l + 4) := by
  have h := Nat.choose_mul_factorial_mul_factorial (show 4 ≤ l + 4 by omega)
  have hsub : l + 4 - 4 = l := by omega
  rw [hsub] at h
  have hf : (l + 4).factorial = (l + 1) * (l + 2) * (l + 3) * (l + 4) * l.factorial := by
    rw [show l + 4 = (l + 3) + 1 from rfl, Nat.factorial_succ,
      show l + 3 = (l + 2) + 1 from rfl, Nat.factorial_succ,
      show l + 2 = (l + 1) + 1 from rfl, Nat.factorial_succ, Nat.factorial_succ]
    ring
  rw [hf] at h
  have h24 : Nat.factorial 4 = 24 := rfl
  rw [h24] at h
  have hpos : 0 < l.factorial := Nat.factorial_pos l
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  calc 24 * (l + 4).choose 4 * l.factorial
      = (l + 4).choose 4 * 24 * l.factorial := by ring
    _ = (l + 1) * (l + 2) * (l + 3) * (l + 4) * l.factorial := h

/-- **(6.11)** (p. 19): `w(y) ≤ 8192(1+y)⁵e^{-2πy}` for `y > 0`. -/
theorem eq_6_11 (y : ℝ) (hy : 0 < y) :
    wt y ≤ 8192 * (1 + y) ^ 5 * Real.exp (-(2 * Real.pi * y)) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hpi4 : Real.pi < 4 := Real.pi_lt_four
  set u : ℝ := 2 * Real.pi * y with hudef
  have hupos : 0 < u := by rw [hudef]; positivity
  set q : ℝ := Real.exp (-u) with hqdef
  have hq0 : 0 < q := Real.exp_pos _
  have hqlt : q < 1 := by rw [hqdef]; exact Real.exp_lt_one_iff.2 (by linarith)
  have hnorm : ‖q‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos hq0]; exact hqlt
  have hsummaj : Summable (fun l : ℕ => (24 * q) * ((((l + 4).choose 4 : ℕ) : ℝ) * q ^ l)) :=
    (summable_choose_mul_geometric_of_norm_lt_one 4 hnorm).mul_left _
  have hle : ∀ l : ℕ, ((l : ℝ) + 1) ^ 4 * Real.exp (-(2 * Real.pi * ((l : ℝ) + 1) * y))
      ≤ (24 * q) * ((((l + 4).choose 4 : ℕ) : ℝ) * q ^ l) := by
    intro l
    have hexp : Real.exp (-(2 * Real.pi * ((l : ℝ) + 1) * y)) = q ^ (l + 1) := by
      rw [hqdef, ← Real.exp_nat_mul]
      congr 1
      rw [hudef]; push_cast; ring
    rw [hexp]
    have hch : ((l : ℝ) + 1) ^ 4 ≤ 24 * (((l + 4).choose 4 : ℕ) : ℝ) := by
      have h := choose_four_id l
      have h' : (24 : ℝ) * (((l + 4).choose 4 : ℕ) : ℝ)
          = ((l : ℝ) + 1) * ((l : ℝ) + 2) * ((l : ℝ) + 3) * ((l : ℝ) + 4) := by
        exact_mod_cast congrArg (fun m : ℕ => (m : ℝ)) h
      rw [h']
      have key : ((l : ℝ) + 1) * ((l : ℝ) + 2) * ((l : ℝ) + 3) * ((l : ℝ) + 4)
          - ((l : ℝ) + 1) ^ 4 = ((l : ℝ) + 1) * (6 * (l : ℝ) ^ 2 + 23 * (l : ℝ) + 23) := by
        ring
      have hp : (0 : ℝ) ≤ ((l : ℝ) + 1) * (6 * (l : ℝ) ^ 2 + 23 * (l : ℝ) + 23) := by
        positivity
      linarith
    have hqpow : (0 : ℝ) < q ^ (l + 1) := pow_pos hq0 _
    calc ((l : ℝ) + 1) ^ 4 * q ^ (l + 1)
        ≤ (24 * (((l + 4).choose 4 : ℕ) : ℝ)) * q ^ (l + 1) := by nlinarith [hqpow]
      _ = (24 * q) * ((((l + 4).choose 4 : ℕ) : ℝ) * q ^ l) := by rw [pow_succ]; ring
  have hnn : ∀ l : ℕ, 0 ≤ ((l : ℝ) + 1) ^ 4 * Real.exp (-(2 * Real.pi * ((l : ℝ) + 1) * y)) :=
    fun l => by positivity
  have hsum : Summable (fun l : ℕ => ((l : ℝ) + 1) ^ 4 * Real.exp (-(2 * Real.pi * ((l : ℝ) + 1) * y)) ) :=
    hsummaj.of_nonneg_of_le hnn hle
  have hts : ∑' l : ℕ, ((l : ℝ) + 1) ^ 4 * Real.exp (-(2 * Real.pi * ((l : ℝ) + 1) * y))
      ≤ 24 * q / (1 - q) ^ 5 := by
    refine le_trans (hsum.tsum_le_tsum hle hsummaj) ?_
    rw [tsum_mul_left, tsum_choose_mul_geometric_of_norm_lt_one 4 hnorm]
    norm_num [div_eq_mul_inv]
  -- the geometric factor: `1 - e^{-u} ≥ u/(1+u)`
  have hexpge : 1 + u ≤ Real.exp u := by linarith [Real.add_one_le_exp u]
  have hq_le : q ≤ 1 / (1 + u) := by
    rw [hqdef, Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos u) (by linarith)]
    linarith
  have h1 : q * (1 + u) ≤ 1 := by
    have := mul_le_mul_of_nonneg_right hq_le (by linarith : (0:ℝ) ≤ 1 + u)
    rwa [one_div, inv_mul_cancel₀ (by linarith : (1:ℝ) + u ≠ 0)] at this
  have hkey : u ≤ (1 - q) * (1 + u) := by nlinarith [h1]
  have hgeo : (1 : ℝ) / (1 - q) ^ 5 ≤ (1 + u) ^ 5 / u ^ 5 := by
    have hlt : (0 : ℝ) < 1 - q := by linarith
    have hbase : (1 : ℝ) / (1 - q) ≤ (1 + u) / u := by
      rw [div_le_div_iff₀ hlt hupos]
      nlinarith [hkey]
    have := pow_le_pow_left₀ (by positivity) hbase 5
    rwa [div_pow, div_pow, one_pow] at this
  have hTle : ∑' l : ℕ, ((l : ℝ) + 1) ^ 4 * Real.exp (-(2 * Real.pi * ((l : ℝ) + 1) * y))
      ≤ 24 * q * ((1 + u) ^ 5 / u ^ 5) := by
    refine le_trans hts ?_
    have h24 : (0 : ℝ) ≤ 24 * q := by positivity
    have : 24 * q / (1 - q) ^ 5 = 24 * q * (1 / (1 - q) ^ 5) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left hgeo h24
  -- assemble
  have hA : (2 * Real.pi) ^ 4 * y ^ 5 / 12 * (24 * q * ((1 + u) ^ 5 / u ^ 5))
      = q * (1 + u) ^ 5 / Real.pi := by
    rw [hudef]; field_simp; ring
  have hB : 1 + u ≤ 2 * Real.pi * (1 + y) := by
    rw [hudef]; nlinarith [hpi, Real.pi_gt_three]
  have hB5 : (1 + u) ^ 5 ≤ (2 * Real.pi * (1 + y)) ^ 5 := by gcongr
  have hsq : Real.pi ^ 2 < 16 := by nlinarith [hpi, hpi4]
  have hpi4' : Real.pi ^ 4 < 256 := by nlinarith [hsq, sq_nonneg Real.pi]
  have hfin : q * (1 + u) ^ 5 / Real.pi ≤ 8192 * (1 + y) ^ 5 * q := by
    rw [div_le_iff₀ hpi]
    have h1 : q * (1 + u) ^ 5 ≤ q * (2 * Real.pi * (1 + y)) ^ 5 :=
      mul_le_mul_of_nonneg_left hB5 hq0.le
    have hy5 : (0 : ℝ) < (1 + y) ^ 5 := by positivity
    have hprod : (0 : ℝ) ≤ q * (1 + y) ^ 5 * Real.pi * (256 - Real.pi ^ 4) :=
      mul_nonneg (mul_nonneg (mul_pos hq0 hy5).le hpi.le) (by linarith)
    nlinarith [h1, hprod]
  calc wt y
      = (2 * Real.pi) ^ 4 * y ^ 5 / 12
          * ∑' l : ℕ, ((l : ℝ) + 1) ^ 4 * Real.exp (-(2 * Real.pi * ((l : ℝ) + 1) * y)) := rfl
    _ ≤ (2 * Real.pi) ^ 4 * y ^ 5 / 12 * (24 * q * ((1 + u) ^ 5 / u ^ 5)) := by
        exact mul_le_mul_of_nonneg_left hTle (by positivity)
    _ = q * (1 + u) ^ 5 / Real.pi := hA
    _ ≤ 8192 * (1 + y) ^ 5 * q := hfin


/-! ## What this file does and does not establish

**Sorry-free** (`#print axioms` below shows `[propext, Classical.choice, Quot.sound]` for
each): the whole of Table 1 and its finite verifications (`sum_cT`, `aT_strictAnti`,
`bT_strictMono`, `tab1_length`, `aT_last_pos`, `bT_last_lt_two`); the certified logarithm
enclosures (`log_two_bounds`, `logLen0`–`logLen15`, `log_alpha_bounds`,
`log_twolam_bounds`); **(A.10)** (`A10_Irho`, `A10_Cstar`) and hence **(6.4)**
(`eq_6_4`); the regularisation constant `≤ 60` (`reg_const_le_sixty`); Table 2's tiling
of `[0,2]` and its cell count 684 (`AA_strictMono`, `table2_tiles`, `table2_card`); the
factorial estimates (`log_factorial_ge`, `log_factorial_le`, `sum_log_fact`) and
**(6.15)** (`eq_6_15`); **(6.11)** (`eq_6_11`); and the derivation of **(6.16)** from
(6.14) and (6.15) (`prop_6_3_of`, with the exact cancellation `K2logK_cancel`).

**Not here**: (6.14) and Proposition 6.3 themselves, which are in `Zeta5/Sec6/Final.lean`
(Andréief's identity (6.10), the Riemann-sum bound (6.12), the scaling (6.13), the
zero-mass energy argument and the configuration bound (6.6)/(6.9), and the potential
inequality (6.2)).

**No `axiom` is declared by this file.** -/

section AuditPrints

#print axioms A10_Irho
#print axioms A10_Cstar
#print axioms eq_6_4
#print axioms eq_6_15
#print axioms eq_6_11
#print axioms table2_tiles
#print axioms prop_6_3_of

end AuditPrints

end

end RealBound
end Zeta5
