/-
Zeta5/PrimeSum.lean

**Proposition 5.2, (5.11)** (p. 15):  for each fixed integer `M ≥ 40`,

  `limsup_{K→∞, 40|K} K^{-2} log m_{K,M} ≤ I_out + 6λ/M + ∫_3^M R(x) x^{-3} dx`.

This file is the machinery; `Zeta5.Interface.prop_5_2` is a one-line application of
`Zeta5.PrimeSum.prop_5_2` below.

THE SHAPE OF THE ARGUMENT (p. 15).  `log m_{K,M} = Σ_{p ≤ 2h} (−L_p(K,M)) log p`, and the
three branches of (5.1) split that sum into three blocks:

*  `p ≤ K/M`   — branch 1, bound (3.12).  Here `−L_p = 6h⌊log_p 5K⌋ log p + h v_p(24) log p`.
   The primes `p ≤ √(5K)` contribute `O(K^{3/2} log K) = o(K²)` because `⌊log_p A⌋ log p ≤
   log A`; for `√(5K) < p ≤ K/M` the logarithmic factor `⌊log_p 5K⌋` is exactly `1`, so the
   block is `6h θ(K/M) + o(K²) = 6λK²/M + o(K²)` by the prime number theorem.
*  `K/M < p ≤ K/3` — branch 2, the inner range.  By (5.7), `−L_p = p R(K/p) + O_M(1)`, and
   partial summation against the prime number theorem turns `Σ p R(K/p) log p` into
   `K² ∫_3^M R(x) x^{-3} dx`.
*  `K/3 < p ≤ 2h` — branch 3, the outer range.  By the two displays of §5.2,
   `−L_p = K T(p/K) + O(1)` with `T` the integrand of (5.10), and the same partial summation
   in the variable `y = p/K` turns `Σ K T(p/K) log p` into `K² I_out`.

WHAT IS ASSUMED HERE, AND WHY.

*  `Zeta5.Axioms.pnt_prime_riemann_sum` — the prime number theorem in the partial-summation
   form the proof consumes.  Allowed by the ground rules of this formalization (README,
   "Ground rules"); see its docstring.
*  `Zeta5.PrimeSum.eq_5_7_uniformity` — the conjunction of the four statements of §§5.1–5.2
   that the paper asserts with an informal justification rather than a proof: (5.7) (two
   halves), and the two displays of §5.2 for the outer range.  Formerly the single `sorry`
   of this file; now **proved** (with `C = 400 M²`) in `Zeta5/Uniformity.lean`, which this
   file imports.  Its statement is unchanged.

Everything else — the exact decomposition of `log m_{K,M}`, the three-way split, the whole
branch-1 estimate, the regularity of `T` needed to feed the axiom, the change of variables
`x = 1/y`, and the assembly — is proved.

IMPORT DISCIPLINE.  This file must not import `Zeta5.Interface`, which imports it.
-/
import Zeta5.Basic
import Zeta5.Axioms
import Zeta5.AppendixB
import Zeta5.Uniformity

namespace Zeta5
namespace PrimeSum

open Finset Filter Set MeasureTheory
open scoped Topology

noncomputable section

/-! ## 0.  The prime index sets

`PS n` is the index set of the product (5.2), `{p prime : p ≤ 2h}`.  `B1`, `B2`, `B3` are the
three branches of (5.1): `pM ≤ K`, `K/M < p ≤ K/3`, `K/3 < p`. -/

/-- `{p prime : p ≤ 2h}` — the index set of the product (5.2). -/
def PS (n : ℕ) : Finset ℕ := (range (2 * h n + 1)).filter Nat.Prime

/-- Branch 1 of (5.1): `pM ≤ K`. -/
def B1 (n M : ℕ) : Finset ℕ := (PS n).filter (fun p => p * M ≤ K n)

/-- The complement of branch 1. -/
def Bnot (n M : ℕ) : Finset ℕ := (PS n).filter (fun p => ¬ (p * M ≤ K n))

/-- Branch 2 of (5.1): the inner range `K/M < p ≤ K/3`. -/
def B2 (n M : ℕ) : Finset ℕ := (Bnot n M).filter (fun p => 3 * p ≤ K n)

/-- Branch 3 of (5.1): the outer range `K/3 < p`. -/
def B3 (n M : ℕ) : Finset ℕ := (Bnot n M).filter (fun p => ¬ (3 * p ≤ K n))

lemma sum_split (n M : ℕ) (f : ℕ → ℝ) :
    ∑ p ∈ PS n, f p = (∑ p ∈ B1 n M, f p) + (∑ p ∈ B2 n M, f p) + (∑ p ∈ B3 n M, f p) := by
  classical
  have h1 : (∑ p ∈ B1 n M, f p) + (∑ p ∈ Bnot n M, f p) = ∑ p ∈ PS n, f p :=
    Finset.sum_filter_add_sum_filter_not (PS n) (fun p => p * M ≤ K n) f
  have h2 : (∑ p ∈ B2 n M, f p) + (∑ p ∈ B3 n M, f p) = ∑ p ∈ Bnot n M, f p :=
    Finset.sum_filter_add_sum_filter_not (Bnot n M) (fun p => 3 * p ≤ K n) f
  rw [← h1, ← h2]; ring

/-! ## 1.  `log m_{K,M}` as a sum over primes -/

/-- `log m_{K,M} = Σ_{p ≤ 2h} (−L_p(K,M)) log p`: the logarithm of (5.2). -/
lemma log_mKM (n M : ℕ) (Alloc : InnerAllocFamily n M) :
    Real.log ((mKM n M Alloc : ℚ) : ℝ)
      = ∑ p ∈ PS n, ((-(Lp n M Alloc p) : ℤ) : ℝ) * Real.log (p : ℝ) := by
  classical
  have hcast : ((mKM n M Alloc : ℚ) : ℝ)
      = ∏ p ∈ PS n, ((p : ℝ)) ^ (-(Lp n M Alloc p)) := by
    rw [mKM, PS]
    push_cast
    rfl
  rw [hcast, Real.log_prod]
  · refine Finset.sum_congr rfl fun p _ => ?_
    exact Real.log_zpow _ _
  · intro p hp
    have hp' : Nat.Prime p := (Finset.mem_filter.1 hp).2
    have : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp'.pos
    exact (zpow_pos this _).ne'

/-! ## 2.  The three branches as intervals of primes -/

lemma K_div_forty (n : ℕ) : K n / 40 = n := by
  simp [K, Nat.mul_div_cancel_left n (by norm_num : 0 < 40)]

lemma le_two_h_of_le_K {n p : ℕ} (hp : p ≤ K n) : p ≤ 2 * h n := by
  simp only [K] at hp; simp only [h]; omega

lemma mem_B1 {n M p : ℕ} (hM : 40 ≤ M) : p ∈ B1 n M ↔ p.Prime ∧ p ≤ K n / M := by
  have hM0 : 0 < M := lt_of_lt_of_le (by norm_num) hM
  constructor
  · intro hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_filter.1 hp
    exact ⟨(Finset.mem_filter.1 hp1).2, (Nat.le_div_iff_mul_le hM0).2 hp2⟩
  · rintro ⟨hprime, hle⟩
    have hle40 : p ≤ n := by
      calc p ≤ K n / M := hle
        _ ≤ K n / 40 := Nat.div_le_div_left hM (by norm_num)
        _ = n := K_div_forty n
    refine Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_range.2 ?_, hprime⟩,
      (Nat.le_div_iff_mul_le hM0).1 hle⟩
    simp only [h]; omega

lemma mem_B2 {n M p : ℕ} (hM : 40 ≤ M) :
    p ∈ B2 n M ↔ p.Prime ∧ K n / M < p ∧ p ≤ K n / 3 := by
  have hM0 : 0 < M := lt_of_lt_of_le (by norm_num) hM
  constructor
  · intro hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_filter.1 hp
    obtain ⟨hp3, hp4⟩ := Finset.mem_filter.1 hp1
    refine ⟨(Finset.mem_filter.1 hp3).2, (Nat.div_lt_iff_lt_mul hM0).2 (by omega), ?_⟩
    exact (Nat.le_div_iff_mul_le (by norm_num : 0 < 3)).2 (by omega)
  · rintro ⟨hprime, hlo, hhi⟩
    have hhi' : p * 3 ≤ K n := (Nat.le_div_iff_mul_le (by norm_num : 0 < 3)).1 hhi
    have hleK : p ≤ K n := by omega
    refine Finset.mem_filter.2 ⟨Finset.mem_filter.2
      ⟨Finset.mem_filter.2 ⟨Finset.mem_range.2 ?_, hprime⟩, ?_⟩, by omega⟩
    · have := le_two_h_of_le_K hleK; omega
    · have := (Nat.div_lt_iff_lt_mul hM0).1 hlo; omega

lemma mem_B3 {n M p : ℕ} (hM : 40 ≤ M) :
    p ∈ B3 n M ↔ p.Prime ∧ K n / 3 < p ∧ p ≤ 2 * h n := by
  have hM0 : 0 < M := lt_of_lt_of_le (by norm_num) hM
  constructor
  · intro hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_filter.1 hp
    obtain ⟨hp3, _hp4⟩ := Finset.mem_filter.1 hp1
    obtain ⟨hp5, hp6⟩ := Finset.mem_filter.1 hp3
    exact ⟨hp6, (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 3)).2 (by omega),
      by have := Finset.mem_range.1 hp5; omega⟩
  · rintro ⟨hprime, hlo, hhi⟩
    have hlo' : K n < p * 3 := (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 3)).1 hlo
    refine Finset.mem_filter.2 ⟨Finset.mem_filter.2
      ⟨Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), hprime⟩, ?_⟩, by omega⟩
    · have : p * 3 ≤ p * M := Nat.mul_le_mul_left p (by omega)
      omega

/-! ## 3.  Matching the branches with the index set of the axiom -/

lemma floor_inv_mul (m j : ℕ) : ⌊(1 / (m : ℝ)) * (j : ℝ)⌋₊ = j / m := by
  rw [show (1 / (m : ℝ)) * (j : ℝ) = (j : ℝ) / (m : ℝ) by ring, Nat.floor_div_natCast,
    Nat.floor_natCast]

lemma floor_zero_mul (x : ℝ) : ⌊(0 : ℝ) * x⌋₊ = 0 := by simp

/-- `⌊(37/20) K⌋ = 2h`: the top of the product (5.2) in the variable `y = p/K`
(`2h/K = 74n/40n = 37/20 = 2λ`). -/
lemma floor_two_lam_K (n : ℕ) : ⌊(37 / 20 : ℝ) * ((K n : ℕ) : ℝ)⌋₊ = 2 * h n := by
  have : (37 / 20 : ℝ) * ((K n : ℕ) : ℝ) = ((2 * h n : ℕ) : ℝ) := by
    simp only [K, h]; push_cast; ring
  rw [this, Nat.floor_natCast]

lemma B1_eq (n M : ℕ) (hM : 40 ≤ M) :
    B1 n M
      = (Finset.Ioc ⌊(0 : ℝ) * ((K n : ℕ) : ℝ)⌋₊
          ⌊(1 / (M : ℝ)) * ((K n : ℕ) : ℝ)⌋₊).filter Nat.Prime := by
  rw [floor_zero_mul, floor_inv_mul]
  ext p
  rw [mem_B1 hM, Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · rintro ⟨hprime, hle⟩; exact ⟨⟨hprime.pos, hle⟩, hprime⟩
  · rintro ⟨⟨_, hle⟩, hprime⟩; exact ⟨hprime, hle⟩

lemma B2_eq (n M : ℕ) (hM : 40 ≤ M) :
    B2 n M
      = (Finset.Ioc ⌊(1 / (M : ℝ)) * ((K n : ℕ) : ℝ)⌋₊
          ⌊(1 / ((3 : ℕ) : ℝ)) * ((K n : ℕ) : ℝ)⌋₊).filter Nat.Prime := by
  rw [floor_inv_mul, floor_inv_mul]
  ext p
  rw [mem_B2 hM, Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · rintro ⟨hprime, h1, h2⟩; exact ⟨⟨h1, h2⟩, hprime⟩
  · rintro ⟨⟨h1, h2⟩, hprime⟩; exact ⟨hprime, h1, h2⟩

lemma B3_eq (n M : ℕ) (hM : 40 ≤ M) :
    B3 n M
      = (Finset.Ioc ⌊(1 / ((3 : ℕ) : ℝ)) * ((K n : ℕ) : ℝ)⌋₊
          ⌊(37 / 20 : ℝ) * ((K n : ℕ) : ℝ)⌋₊).filter Nat.Prime := by
  rw [floor_inv_mul, floor_two_lam_K]
  ext p
  rw [mem_B3 hM, Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · rintro ⟨hprime, h1, h2⟩; exact ⟨⟨h1, h2⟩, hprime⟩
  · rintro ⟨⟨h1, h2⟩, hprime⟩; exact ⟨hprime, h1, h2⟩

/-! ## 4.  The prime number theorem, applied -/

lemma tendsto_K : Tendsto (fun n : ℕ => ((K n : ℕ) : ℝ)) atTop atTop := by
  refine tendsto_atTop_mono (fun n => ?_) (tendsto_natCast_atTop_atTop (R := ℝ))
  have : (n : ℕ) ≤ K n := by simp only [K]; omega
  exact_mod_cast this

/-- The axiom `Zeta5.Axioms.pnt_prime_riemann_sum`, transported to the sequence `K = 40n`. -/
lemma tendsto_primeSum (a b : ℝ) (ha : 0 ≤ a) (hab : a < b) (φ : ℝ → ℝ)
    (hbdd : ∃ C : ℝ, ∀ y ∈ Icc a b, |φ y| ≤ C)
    (hpc : ∃ D : Finset ℝ, ∀ y ∈ Icc a b, y ∉ D → ContinuousAt φ y) :
    Tendsto
      (fun n : ℕ =>
        (∑ p ∈ (Finset.Ioc ⌊a * ((K n : ℕ) : ℝ)⌋₊ ⌊b * ((K n : ℕ) : ℝ)⌋₊).filter Nat.Prime,
            φ ((p : ℝ) / ((K n : ℕ) : ℝ)) * Real.log p) / ((K n : ℕ) : ℝ))
      atTop (𝓝 (∫ y in a..b, φ y)) :=
  (Axioms.pnt_prime_riemann_sum a b ha hab φ hbdd hpc).comp tendsto_K

/-! ## 5.  Branch 1: the small primes and the prime number theorem

`−L_p = 6h⌊log_p 5K⌋ + h v_p(24)` there.  `⌊log_p A⌋ log p ≤ log A` always, and
`⌊log_p 5K⌋ = 1` as soon as `p² > 5K`, so the block is `6h θ(K/M)` up to
`O(K^{3/2} log K) + O(K)`. -/

/-- `⌊log_p A⌋ · log p ≤ log A`, from `p^{⌊log_p A⌋} ≤ A`. -/
lemma natLog_mul_log_le {p A : ℕ} (hp : 2 ≤ p) (hA : A ≠ 0) :
    (Nat.log p A : ℝ) * Real.log (p : ℝ) ≤ Real.log (A : ℝ) := by
  have hple : (p : ℝ) ^ (Nat.log p A) ≤ (A : ℝ) := by
    exact_mod_cast Nat.pow_log_le_self p hA
  have hp0 : (0 : ℝ) < (p : ℝ) := by
    have : (0 : ℕ) < p := by omega
    exact_mod_cast this
  calc (Nat.log p A : ℝ) * Real.log (p : ℝ) = Real.log ((p : ℝ) ^ (Nat.log p A)) :=
        (Real.log_pow _ _).symm
    _ ≤ Real.log (A : ℝ) := Real.log_le_log (by positivity) hple

/-- For `p ≤ A` and `2 ≤ p`, `⌊log_p A⌋ ≥ 1`. -/
lemma one_le_natLog {p A : ℕ} (hp : 2 ≤ p) (hpA : p ≤ A) : 1 ≤ Nat.log p A :=
  Nat.log_pos (by omega) hpA

/-- If `A < p²` then `⌊log_p A⌋ ≤ 1`. -/
lemma natLog_le_one {p A : ℕ} (hA : A ≠ 0) (h : A < p ^ 2) : Nat.log p A ≤ 1 :=
  Nat.lt_succ_iff.1 (Nat.log_lt_of_lt_pow hA h)

/-- `Σ_p v_p(24) log p ≤ 2 log 24` over any set of primes: only `p = 2, 3` contribute. -/
lemma sum_padicVal24_le {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) :
    ∑ p ∈ S, (padicValNat p 24 : ℝ) * Real.log (p : ℝ) ≤ 2 * Real.log 24 := by
  classical
  set T := S.filter (fun p => p = 2 ∨ p = 3) with hTdef
  have hsub : T ⊆ S := Finset.filter_subset _ _
  have hzero : ∀ p ∈ S, p ∉ T → (padicValNat p 24 : ℝ) * Real.log (p : ℝ) = 0 := by
    intro p hpS hpT
    have hne : ¬ (p = 2 ∨ p = 3) := fun hc => hpT (Finset.mem_filter.2 ⟨hpS, hc⟩)
    have hp := hS p hpS
    have hnd : ¬ (p ∣ 24) := by
      intro hd
      rw [show (24 : ℕ) = 2 ^ 3 * 3 by norm_num, hp.dvd_mul] at hd
      rcases hd with hd | hd
      · exact hne (Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1
          (hp.dvd_of_dvd_pow hd)))
      · exact hne (Or.inr ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 hd))
    rw [padicValNat.eq_zero_of_not_dvd hnd]
    simp
  rw [← Finset.sum_subset hsub hzero]
  have hTsub : T ⊆ ({2, 3} : Finset ℕ) := by
    intro p hp
    rcases (Finset.mem_filter.1 hp).2 with h | h <;> simp [h]
  have hTcard : (T.card : ℝ) ≤ 2 := by
    have h1 : T.card ≤ ({2, 3} : Finset ℕ).card := Finset.card_le_card hTsub
    have h2 : ({2, 3} : Finset ℕ).card = 2 := by decide
    have : T.card ≤ 2 := by omega
    exact_mod_cast this
  have hterm : ∀ p ∈ T, (padicValNat p 24 : ℝ) * Real.log (p : ℝ) ≤ Real.log 24 := by
    intro p hp
    have hpp := hS p (hsub hp)
    have hdvd : p ^ (padicValNat p 24) ∣ 24 := pow_padicValNat_dvd
    have hle : ((p : ℝ)) ^ (padicValNat p 24) ≤ 24 := by
      have : p ^ (padicValNat p 24) ≤ 24 := Nat.le_of_dvd (by norm_num) hdvd
      exact_mod_cast this
    have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpp.pos
    calc (padicValNat p 24 : ℝ) * Real.log (p : ℝ)
        = Real.log ((p : ℝ) ^ (padicValNat p 24)) := (Real.log_pow _ _).symm
      _ ≤ Real.log 24 := Real.log_le_log (by positivity) hle
  have hlog24 : (0 : ℝ) ≤ Real.log 24 := Real.log_nonneg (by norm_num)
  calc ∑ p ∈ T, (padicValNat p 24 : ℝ) * Real.log (p : ℝ)
      ≤ T.card • Real.log 24 := Finset.sum_le_card_nsmul _ _ _ hterm
    _ = (T.card : ℝ) * Real.log 24 := by rw [nsmul_eq_mul]
    _ ≤ 2 * Real.log 24 := mul_le_mul_of_nonneg_right hTcard hlog24

/-! ### The three prime-sum abbreviations -/

/-- `θ` over branch 1: `Σ_{p ≤ K/M} log p`. -/
def S1 (n M : ℕ) : ℝ := ∑ p ∈ B1 n M, Real.log (p : ℝ)
/-- `Σ_{K/M < p ≤ K/3} log p`. -/
def S2 (n M : ℕ) : ℝ := ∑ p ∈ B2 n M, Real.log (p : ℝ)
/-- `Σ_{K/3 < p ≤ 2h} log p`. -/
def S3 (n M : ℕ) : ℝ := ∑ p ∈ B3 n M, Real.log (p : ℝ)

/-- Branch 1 of (5.1), as a real number: `−L_p = 6h⌊log_p 5K⌋ + h v_p(24)`. -/
lemma negLp_of_B1 {n M p : ℕ} (Alloc : InnerAllocFamily n M) (hp : p ∈ B1 n M) :
    ((-(Lp n M Alloc p) : ℤ) : ℝ)
      = 6 * (h n : ℝ) * (Nat.log p (5 * K n) : ℝ) + (h n : ℝ) * (padicValNat p 24 : ℝ) := by
  have hmem : p * M ≤ K n := (Finset.mem_filter.1 hp).2
  obtain ⟨v, hv⟩ : ∃ v : ℕ, padicValNat p 24 = v := ⟨_, rfl⟩
  rw [Lp, ite_eq_left hmem, hv]
  push_cast
  ring

/-- **The branch-1 estimate.**  `Σ_{p ≤ K/M}(−L_p) log p ≤ 6h θ(K/M) + O(K^{3/2}log K) + O(K)`;
the `O(K^{3/2} log K)` is the paper's `p ≤ √(5K)` term. -/
lemma block1_le {n M : ℕ} (hM : 40 ≤ M) (hn : 0 < n) (Alloc : InnerAllocFamily n M) :
    ∑ p ∈ B1 n M, ((-(Lp n M Alloc p) : ℤ) : ℝ) * Real.log (p : ℝ)
      ≤ 6 * (h n : ℝ) * S1 n M
        + 6 * (h n : ℝ) * ((Nat.sqrt (5 * K n) : ℝ) + 1) * Real.log ((5 * K n : ℕ) : ℝ)
        + 2 * (h n : ℝ) * Real.log 24 := by
  classical
  have hK0 : 0 < K n := by simp only [K]; omega
  have hA0 : (5 * K n) ≠ 0 := by omega
  have hh0 : (0 : ℝ) ≤ (h n : ℝ) := by positivity
  have hlogA : (0 : ℝ) ≤ Real.log ((5 * K n : ℕ) : ℝ) := by
    refine Real.log_nonneg ?_
    have : (1 : ℕ) ≤ 5 * K n := by omega
    exact_mod_cast this
  -- pointwise bound
  have key : ∀ p ∈ B1 n M,
      ((-(Lp n M Alloc p) : ℤ) : ℝ) * Real.log (p : ℝ)
        ≤ 6 * (h n : ℝ) * Real.log (p : ℝ)
          + 6 * (h n : ℝ) * (if p * p ≤ 5 * K n then Real.log ((5 * K n : ℕ) : ℝ) else 0)
          + (h n : ℝ) * ((padicValNat p 24 : ℝ) * Real.log (p : ℝ)) := by
    intro p hp
    have hprime : p.Prime := (mem_B1 hM).1 hp |>.1
    have hple : p ≤ K n / M := (mem_B1 hM).1 hp |>.2
    have hp2 : 2 ≤ p := hprime.two_le
    have hpK : p ≤ 5 * K n := by
      have : K n / M ≤ K n := Nat.div_le_self _ _
      omega
    have hlogp : (0 : ℝ) ≤ Real.log (p : ℝ) := by
      refine Real.log_nonneg ?_
      have : (1 : ℕ) ≤ p := by omega
      exact_mod_cast this
    have hbig := natLog_mul_log_le (p := p) (A := 5 * K n) hp2 hA0
    have hone : 1 ≤ Nat.log p (5 * K n) := one_le_natLog hp2 hpK
    have hmain : (Nat.log p (5 * K n) : ℝ) * Real.log (p : ℝ)
        ≤ Real.log (p : ℝ)
          + (if p * p ≤ 5 * K n then Real.log ((5 * K n : ℕ) : ℝ) else 0) := by
      by_cases hsq : p * p ≤ 5 * K n
      · rw [ite_eq_left hsq]
        have h1 : (1 : ℝ) ≤ (Nat.log p (5 * K n) : ℝ) := by exact_mod_cast hone
        nlinarith [hbig, hlogp]
      · rw [ite_eq_right hsq]
        have hlt : 5 * K n < p ^ 2 := by
          rw [pow_two]; omega
        have : Nat.log p (5 * K n) = 1 :=
          le_antisymm (natLog_le_one hA0 hlt) hone
        rw [this]
        simp
    rw [negLp_of_B1 Alloc hp]
    have hexp : (6 * (h n : ℝ) * (Nat.log p (5 * K n) : ℝ)
        + (h n : ℝ) * (padicValNat p 24 : ℝ)) * Real.log (p : ℝ)
        = 6 * (h n : ℝ) * ((Nat.log p (5 * K n) : ℝ) * Real.log (p : ℝ))
          + (h n : ℝ) * ((padicValNat p 24 : ℝ) * Real.log (p : ℝ)) := by ring
    rw [hexp]
    have := mul_le_mul_of_nonneg_left hmain (by positivity : (0 : ℝ) ≤ 6 * (h n : ℝ))
    linarith
  -- sum up
  refine le_trans (Finset.sum_le_sum key) ?_
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum]
  have hS1 : ∑ p ∈ B1 n M, Real.log (p : ℝ) = S1 n M := rfl
  rw [hS1]
  have hcount : ∑ p ∈ B1 n M,
      (if p * p ≤ 5 * K n then Real.log ((5 * K n : ℕ) : ℝ) else 0)
      ≤ ((Nat.sqrt (5 * K n) : ℝ) + 1) * Real.log ((5 * K n : ℕ) : ℝ) := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    refine mul_le_mul_of_nonneg_right ?_ hlogA
    have hsub : (B1 n M).filter (fun p => p * p ≤ 5 * K n)
        ⊆ Finset.range (Nat.sqrt (5 * K n) + 1) := by
      intro p hp
      have := (Finset.mem_filter.1 hp).2
      exact Finset.mem_range.2 (by have := Nat.le_sqrt.2 this; omega)
    have hc : ((B1 n M).filter (fun p => p * p ≤ 5 * K n)).card ≤ Nat.sqrt (5 * K n) + 1 := by
      have := Finset.card_le_card hsub
      simpa using this
    have : (((B1 n M).filter (fun p => p * p ≤ 5 * K n)).card : ℝ)
        ≤ ((Nat.sqrt (5 * K n) : ℝ) + 1) := by exact_mod_cast hc
    exact this
  have hpad : ∑ p ∈ B1 n M, (padicValNat p 24 : ℝ) * Real.log (p : ℝ) ≤ 2 * Real.log 24 :=
    sum_padicVal24_le (fun p hp => ((mem_B1 hM).1 hp).1)
  have h1 : 6 * (h n : ℝ) * (∑ p ∈ B1 n M,
      (if p * p ≤ 5 * K n then Real.log ((5 * K n : ℕ) : ℝ) else 0))
      ≤ 6 * (h n : ℝ) * (((Nat.sqrt (5 * K n) : ℝ) + 1) * Real.log ((5 * K n : ℕ) : ℝ)) :=
    mul_le_mul_of_nonneg_left hcount (by positivity)
  have h2 : (h n : ℝ) * (∑ p ∈ B1 n M, (padicValNat p 24 : ℝ) * Real.log (p : ℝ))
      ≤ (h n : ℝ) * (2 * Real.log 24) := mul_le_mul_of_nonneg_left hpad hh0
  nlinarith [h1, h2]

/-! ## 6.  The three prime-counting limits, and the `o(K²)` error of branch 1 -/

lemma tendsto_log_div_id : Tendsto (fun v : ℝ => Real.log v / v) atTop (𝓝 0) :=
  Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero

lemma tendsto_log_div_sqrt : Tendsto (fun t : ℝ => Real.log t / Real.sqrt t) atTop (𝓝 0) := by
  have h := tendsto_log_div_id.comp Real.tendsto_sqrt_atTop
  have h2 : Tendsto (fun t : ℝ => 2 * (Real.log (Real.sqrt t) / Real.sqrt t)) atTop (𝓝 0) := by
    simpa using h.const_mul (2 : ℝ)
  refine h2.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  rw [Real.log_sqrt ht]
  ring

lemma tendsto_5K : Tendsto (fun n : ℕ => ((5 * K n : ℕ) : ℝ)) atTop atTop := by
  refine tendsto_atTop_mono (fun n => ?_) (tendsto_natCast_atTop_atTop (R := ℝ))
  have : (n : ℕ) ≤ 5 * K n := by simp only [K]; omega
  exact_mod_cast this

/-- The `o(K²)` error of the branch-1 estimate: `6h(√(5K)+1)log(5K) + 2h log 24`. -/
def ErrNum (n : ℕ) : ℝ :=
  6 * (h n : ℝ) * ((Nat.sqrt (5 * K n) : ℝ) + 1) * Real.log ((5 * K n : ℕ) : ℝ)
    + 2 * (h n : ℝ) * Real.log 24

/-- `6h(√(5K)+1)log(5K) + 2h log 24 = o(K²)`: the paper's `O(K^{3/2}log K) = o(K²)`. -/
lemma tendsto_ErrNum : Tendsto (fun n : ℕ => ErrNum n / ((K n : ℕ) : ℝ) ^ 2) atTop (𝓝 0) := by
  set g : ℝ → ℝ := fun t =>
    30 * (Real.log t / Real.sqrt t) + 30 * (Real.log t / t) + 10 * Real.log 24 / t with hg
  have hgt : Tendsto g atTop (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => 30 * (Real.log t / Real.sqrt t)) atTop (𝓝 0) := by
      simpa using tendsto_log_div_sqrt.const_mul (30 : ℝ)
    have h2 : Tendsto (fun t : ℝ => 30 * (Real.log t / t)) atTop (𝓝 0) := by
      simpa using tendsto_log_div_id.const_mul (30 : ℝ)
    have h3 : Tendsto (fun t : ℝ => 10 * Real.log 24 / t) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds (x := 10 * Real.log 24) (f := atTop (α := ℝ))).div_atTop
        tendsto_id
    simpa [hg] using (h1.add h2).add h3
  have hcomp : Tendsto (fun n : ℕ => g ((5 * K n : ℕ) : ℝ)) atTop (𝓝 0) := hgt.comp tendsto_5K
  refine squeeze_zero' ?_ ?_ hcomp
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hK : (0 : ℝ) < ((K n : ℕ) : ℝ) := by
      have : 0 < K n := by simp only [K]; omega
      exact_mod_cast this
    have hlog : (0 : ℝ) ≤ Real.log ((5 * K n : ℕ) : ℝ) := by
      refine Real.log_nonneg ?_
      have : (1 : ℕ) ≤ 5 * K n := by simp only [K]; omega
      exact_mod_cast this
    have h24 : (0 : ℝ) ≤ Real.log 24 := Real.log_nonneg (by norm_num)
    have hh : (0 : ℝ) ≤ (h n : ℝ) := by positivity
    have hs : (0 : ℝ) ≤ (Nat.sqrt (5 * K n) : ℝ) := by positivity
    have : (0 : ℝ) ≤ ErrNum n := by
      unfold ErrNum; positivity
    positivity
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hK0 : 0 < K n := by simp only [K]; omega
    have hKR : (0 : ℝ) < ((K n : ℕ) : ℝ) := by exact_mod_cast hK0
    set t : ℝ := ((5 * K n : ℕ) : ℝ) with htdef
    have ht0 : (0 : ℝ) < t := by
      rw [htdef]
      have : 0 < 5 * K n := by omega
      exact_mod_cast this
    have htK : t = 5 * ((K n : ℕ) : ℝ) := by rw [htdef]; push_cast; ring
    have hsq0 : (0 : ℝ) < Real.sqrt t := Real.sqrt_pos.2 ht0
    have hsqsq : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht0.le
    have hlog : (0 : ℝ) ≤ Real.log t := by
      refine Real.log_nonneg ?_
      rw [htK]
      have : (1 : ℝ) ≤ ((K n : ℕ) : ℝ) := by
        have : (1 : ℕ) ≤ K n := by omega
        exact_mod_cast this
      linarith
    have h24 : (0 : ℝ) ≤ Real.log 24 := Real.log_nonneg (by norm_num)
    have hnat : (Nat.sqrt (5 * K n) : ℝ) ≤ Real.sqrt t := by
      have hsqle : ((Nat.sqrt (5 * K n) : ℝ)) ^ 2 ≤ t := by
        rw [htdef]
        have hn2 : Nat.sqrt (5 * K n) ^ 2 ≤ 5 * K n := by
          have := Nat.sqrt_le' (5 * K n)
          nlinarith [Nat.sqrt_le' (5 * K n)]
        exact_mod_cast hn2
      calc (Nat.sqrt (5 * K n) : ℝ)
          = Real.sqrt (((Nat.sqrt (5 * K n) : ℝ)) ^ 2) := (Real.sqrt_sq (by positivity)).symm
        _ ≤ Real.sqrt t := Real.sqrt_le_sqrt hsqle
    have hhK : (h n : ℝ) ≤ ((K n : ℕ) : ℝ) := by
      have : h n ≤ K n := by simp only [h, K]; omega
      exact_mod_cast this
    -- the numerator bound
    have hnum : ErrNum n
        ≤ 6 * ((K n : ℕ) : ℝ) * (Real.sqrt t + 1) * Real.log t
          + 2 * ((K n : ℕ) : ℝ) * Real.log 24 := by
      unfold ErrNum
      have hA : 6 * (h n : ℝ) * ((Nat.sqrt (5 * K n) : ℝ) + 1) * Real.log ((5 * K n : ℕ) : ℝ)
          ≤ 6 * ((K n : ℕ) : ℝ) * (Real.sqrt t + 1) * Real.log t := by
        rw [← htdef]
        have hpos1 : (0 : ℝ) ≤ (Nat.sqrt (5 * K n) : ℝ) + 1 := by positivity
        have e1 : (h n : ℝ) * ((Nat.sqrt (5 * K n) : ℝ) + 1)
            ≤ ((K n : ℕ) : ℝ) * (Real.sqrt t + 1) := by
          calc (h n : ℝ) * ((Nat.sqrt (5 * K n) : ℝ) + 1)
              ≤ ((K n : ℕ) : ℝ) * ((Nat.sqrt (5 * K n) : ℝ) + 1) :=
                mul_le_mul_of_nonneg_right hhK hpos1
            _ ≤ ((K n : ℕ) : ℝ) * (Real.sqrt t + 1) :=
                mul_le_mul_of_nonneg_left (by linarith) (le_of_lt hKR)
        have e2 := mul_le_mul_of_nonneg_right e1 hlog
        nlinarith [e2]
      have hB : 2 * (h n : ℝ) * Real.log 24 ≤ 2 * ((K n : ℕ) : ℝ) * Real.log 24 := by
        nlinarith [hhK, h24]
      linarith
    have hKt : ((K n : ℕ) : ℝ) = t / 5 := by rw [htK]; ring
    have hgoal : (6 * ((K n : ℕ) : ℝ) * (Real.sqrt t + 1) * Real.log t
          + 2 * ((K n : ℕ) : ℝ) * Real.log 24) / ((K n : ℕ) : ℝ) ^ 2 = g t := by
      rw [hg, hKt]
      field_simp
      nlinarith [hsqsq, hsq0, ht0]
    calc ErrNum n / ((K n : ℕ) : ℝ) ^ 2
        ≤ (6 * ((K n : ℕ) : ℝ) * (Real.sqrt t + 1) * Real.log t
            + 2 * ((K n : ℕ) : ℝ) * Real.log 24) / ((K n : ℕ) : ℝ) ^ 2 := by
          apply div_le_div_of_nonneg_right hnum (by positivity)
      _ = g t := hgoal

/-! ## 7.  The three prime-counting limits -/

lemma tendsto_theta_of (a b : ℝ) (ha : 0 ≤ a) (hab : a < b) (Bs : ℕ → Finset ℕ)
    (hB : ∀ n, Bs n
      = (Finset.Ioc ⌊a * ((K n : ℕ) : ℝ)⌋₊ ⌊b * ((K n : ℕ) : ℝ)⌋₊).filter Nat.Prime) :
    Tendsto (fun n : ℕ => (∑ p ∈ Bs n, Real.log (p : ℝ)) / ((K n : ℕ) : ℝ)) atTop
      (𝓝 (b - a)) := by
  have h := tendsto_primeSum a b ha hab (fun _ => (1 : ℝ))
    ⟨1, fun y _ => by norm_num⟩ ⟨∅, fun y _ _ => continuousAt_const⟩
  simp only [one_mul] at h
  rw [intervalIntegral.integral_const, smul_eq_mul, mul_one] at h
  refine Filter.Tendsto.congr (fun n => ?_) h
  rw [hB n]

lemma tendsto_S1 {M : ℕ} (hM : 40 ≤ M) :
    Tendsto (fun n : ℕ => S1 n M / ((K n : ℕ) : ℝ)) atTop (𝓝 (1 / (M : ℝ))) := by
  have hM0 : (0 : ℝ) < (M : ℝ) := by
    have : 0 < M := by omega
    exact_mod_cast this
  have h := tendsto_theta_of 0 (1 / (M : ℝ)) le_rfl (by positivity) (fun n => B1 n M)
    (fun n => B1_eq n M hM)
  simpa [S1] using h

lemma tendsto_S2 {M : ℕ} (hM : 40 ≤ M) :
    Tendsto (fun n : ℕ => S2 n M / ((K n : ℕ) : ℝ)) atTop
      (𝓝 (1 / ((3 : ℕ) : ℝ) - 1 / (M : ℝ))) := by
  have hM0 : (0 : ℝ) < (M : ℝ) := by
    have : 0 < M := by omega
    exact_mod_cast this
  have hlt : 1 / (M : ℝ) < 1 / ((3 : ℕ) : ℝ) := by
    have h3 : ((3 : ℕ) : ℝ) < (M : ℝ) := by
      have : (3 : ℕ) < M := by omega
      exact_mod_cast this
    have : (0 : ℝ) < ((3 : ℕ) : ℝ) := by norm_num
    exact one_div_lt_one_div_of_lt this h3
  have h := tendsto_theta_of (1 / (M : ℝ)) (1 / ((3 : ℕ) : ℝ)) (by positivity) hlt
    (fun n => B2 n M) (fun n => B2_eq n M hM)
  simpa [S2] using h

lemma tendsto_S3 {M : ℕ} (hM : 40 ≤ M) :
    Tendsto (fun n : ℕ => S3 n M / ((K n : ℕ) : ℝ)) atTop
      (𝓝 ((37 / 20 : ℝ) - 1 / ((3 : ℕ) : ℝ))) := by
  have h := tendsto_theta_of (1 / ((3 : ℕ) : ℝ)) (37 / 20 : ℝ) (by positivity) (by norm_num)
    (fun n => B3 n M) (fun n => B3_eq n M hM)
  simpa [S3] using h

/-! ## 8.  The regularity of the outer integrand `T` of §B.2

Table 4 (`Zeta5.AppendixB.qout_0 … qout_10`) exhibits `T` as an affine function on each of
eleven open intervals covering `(1/3, 2λ)`; that gives both hypotheses the prime-number-theorem
axiom needs, with no new assumption. -/

/-- A function that is affine on an open interval is continuous at its interior points. -/
lemma continuousAt_of_affine {f : ℝ → ℝ} {l r b c : ℝ}
    (hf : ∀ y : ℝ, l < y → y < r → f y = b + c * y) {y : ℝ} (h1 : l < y) (h2 : y < r) :
    ContinuousAt f y := by
  have hmem : Ioo l r ∈ 𝓝 y := Ioo_mem_nhds h1 h2
  have heq : (fun z : ℝ => b + c * z) =ᶠ[𝓝 y] f := by
    filter_upwards [hmem] with z hz
    exact (hf z hz.1 hz.2).symm
  exact ContinuousAt.congr (by fun_prop) heq

/-- `T` is bounded on `[1/3, 2λ]`. -/
lemma Tout_bdd : ∀ y ∈ Icc (1 / ((3 : ℕ) : ℝ)) (37 / 20 : ℝ), |AppendixB.Tout y| ≤ 200 := by
  intro y hy
  obtain ⟨hy1, hy2⟩ := hy
  have h3 : ((3 : ℕ) : ℝ) = 3 := by norm_num
  rw [h3] at hy1
  have hy0 : (0 : ℝ) < y := by linarith
  have hfl0 : (0 : ℝ) ≤ ((⌊1 / y⌋ : ℤ) : ℝ) := by
    have : (0 : ℤ) ≤ ⌊1 / y⌋ := Int.le_floor.2 (by push_cast; positivity)
    exact_mod_cast this
  have hfl3 : ((⌊1 / y⌋ : ℤ) : ℝ) ≤ 3 := by
    have hle : (1 : ℝ) / y ≤ 3 := by
      rw [div_le_iff₀ hy0]; linarith
    have : ⌊1 / y⌋ ≤ 3 := by
      have h' : (⌊1 / y⌋ : ℝ) ≤ 3 := le_trans (Int.floor_le _) hle
      exact_mod_cast h'
    exact_mod_cast this
  have ha : ((alpha : ℚ) : ℝ) = 3 / 40 := by norm_num [alpha]
  have hl : ((lam : ℚ) : ℝ) = 37 / 40 := by norm_num [lam]
  have b1a : min ((alpha : ℚ) : ℝ) (1 - 2 * y) ≤ 3 / 40 := by rw [← ha]; exact min_le_left _ _
  have b1b : (-3 : ℝ) ≤ min ((alpha : ℚ) : ℝ) (1 - 2 * y) :=
    le_min (by rw [ha]; norm_num) (by linarith)
  have b2a : (0 : ℝ) ≤ max 0 (1 + ((alpha : ℚ) : ℝ) - 3 * y) := le_max_left _ _
  have b2b : max 0 (1 + ((alpha : ℚ) : ℝ) - 3 * y) ≤ 2 :=
    max_le (by norm_num) (by rw [ha]; linarith)
  have b3a : min ((alpha : ℚ) : ℝ) (1 - y) ≤ 3 / 40 := by rw [← ha]; exact min_le_left _ _
  have b3b : (-3 : ℝ) ≤ min ((alpha : ℚ) : ℝ) (1 - y) :=
    le_min (by rw [ha]; norm_num) (by linarith)
  have b4a : (0 : ℝ) ≤ max 0 (1 + ((alpha : ℚ) : ℝ) - 2 * y) := le_max_left _ _
  have b4b : max 0 (1 + ((alpha : ℚ) : ℝ) - 2 * y) ≤ 2 :=
    max_le (by norm_num) (by rw [ha]; linarith)
  have b5a : (0 : ℝ) ≤ max 0 (1 + 4 * ((alpha : ℚ) : ℝ) - 2 * y) := le_max_left _ _
  have b5b : max 0 (1 + 4 * ((alpha : ℚ) : ℝ) - 2 * y) ≤ 2 :=
    max_le (by norm_num) (by rw [ha]; linarith)
  have b6a : (0 : ℝ) ≤ max 0 (1 + 4 * ((alpha : ℚ) : ℝ) - 3 * y
      - max 0 (1 + ((alpha : ℚ) : ℝ) - 3 * y)) := le_max_left _ _
  have b6b : max 0 (1 + 4 * ((alpha : ℚ) : ℝ) - 3 * y
      - max 0 (1 + ((alpha : ℚ) : ℝ) - 3 * y)) ≤ 2 :=
    max_le (by norm_num) (by rw [ha] at *; linarith)
  have c1a : (0 : ℝ) ≤ max 0 (2 * ((lam : ℚ) : ℝ) - y) := le_max_left _ _
  have c1b : max 0 (2 * ((lam : ℚ) : ℝ) - y) ≤ 2 := max_le (by norm_num) (by rw [hl]; linarith)
  have c2a : (0 : ℝ) ≤ max 0 (2 * ((lam : ℚ) : ℝ) - 2 * y) := le_max_left _ _
  have c2b : max 0 (2 * ((lam : ℚ) : ℝ) - 2 * y) ≤ 2 :=
    max_le (by norm_num) (by rw [hl]; linarith)
  have c3a : (0 : ℝ) ≤ max 0 (2 * ((lam : ℚ) : ℝ) - 3 * y) := le_max_left _ _
  have c3b : max 0 (2 * ((lam : ℚ) : ℝ) - 3 * y) ≤ 2 :=
    max_le (by norm_num) (by rw [hl]; linarith)
  have c4a : (0 : ℝ) ≤ max 0 (2 * ((lam : ℚ) : ℝ) - 4 * y) := le_max_left _ _
  have c4b : max 0 (2 * ((lam : ℚ) : ℝ) - 4 * y) ≤ 2 :=
    max_le (by norm_num) (by rw [hl]; linarith)
  have c5a : (0 : ℝ) ≤ max 0 (2 * ((lam : ℚ) : ℝ) - 5 * y) := le_max_left _ _
  have c5b : max 0 (2 * ((lam : ℚ) : ℝ) - 5 * y) ≤ 2 :=
    max_le (by norm_num) (by rw [hl]; linarith)
  rw [abs_le]
  simp only [AppendixB.Tout, AppendixB.R0, AppendixB.dRank]
  rw [ha, hl] at *
  split_ifs <;> constructor <;> linarith

/-- `T` is continuous off the twelve endpoints of Table 4. -/
lemma Tout_piecewise :
    ∃ D : Finset ℝ, ∀ y ∈ Icc (1 / ((3 : ℕ) : ℝ)) (37 / 20 : ℝ), y ∉ D →
      ContinuousAt AppendixB.Tout y := by
  classical
  refine ⟨{1/3, 43/120, 37/100, 13/30, 37/80, 1/2, 43/80, 37/60, 13/20, 37/40, 1, 37/20}, ?_⟩
  intro y hy hyD
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hyD
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11⟩ := hyD
  obtain ⟨hy1, hy2⟩ := hy
  have h3 : ((3 : ℕ) : ℝ) = 3 := by norm_num
  rw [h3] at hy1
  have hlo : (1/3 : ℝ) < y := lt_of_le_of_ne hy1 (Ne.symm e0)
  have hhi : y < (37/20 : ℝ) := lt_of_le_of_ne hy2 e11
  by_cases c0 : y < (43/120 : ℝ)
  · exact continuousAt_of_affine AppendixB.qout_0 hlo c0
  push Not at c0
  have c0' : (43/120 : ℝ) < y := lt_of_le_of_ne c0 (Ne.symm e1)
  by_cases c1 : y < (37/100 : ℝ)
  · exact continuousAt_of_affine AppendixB.qout_1 c0' c1
  push Not at c1
  have c1' : (37/100 : ℝ) < y := lt_of_le_of_ne c1 (Ne.symm e2)
  by_cases c2 : y < (13/30 : ℝ)
  · exact continuousAt_of_affine AppendixB.qout_2 c1' c2
  push Not at c2
  have c2' : (13/30 : ℝ) < y := lt_of_le_of_ne c2 (Ne.symm e3)
  by_cases c3 : y < (37/80 : ℝ)
  · exact continuousAt_of_affine AppendixB.qout_3 c2' c3
  push Not at c3
  have c3' : (37/80 : ℝ) < y := lt_of_le_of_ne c3 (Ne.symm e4)
  by_cases c4 : y < (1/2 : ℝ)
  · exact continuousAt_of_affine AppendixB.qout_4 c3' c4
  push Not at c4
  have c4' : (1/2 : ℝ) < y := lt_of_le_of_ne c4 (Ne.symm e5)
  by_cases c5 : y < (43/80 : ℝ)
  · exact continuousAt_of_affine AppendixB.qout_5 c4' c5
  push Not at c5
  have c5' : (43/80 : ℝ) < y := lt_of_le_of_ne c5 (Ne.symm e6)
  by_cases c6 : y < (37/60 : ℝ)
  · exact continuousAt_of_affine AppendixB.qout_6 c5' c6
  push Not at c6
  have c6' : (37/60 : ℝ) < y := lt_of_le_of_ne c6 (Ne.symm e7)
  by_cases c7 : y < (13/20 : ℝ)
  · exact continuousAt_of_affine AppendixB.qout_7 c6' c7
  push Not at c7
  have c7' : (13/20 : ℝ) < y := lt_of_le_of_ne c7 (Ne.symm e8)
  by_cases c8 : y < (37/40 : ℝ)
  · exact continuousAt_of_affine AppendixB.qout_8 c7' c8
  push Not at c8
  have c8' : (37/40 : ℝ) < y := lt_of_le_of_ne c8 (Ne.symm e9)
  by_cases c9 : y < (1 : ℝ)
  · exact continuousAt_of_affine AppendixB.qout_9 c8' c9
  push Not at c9
  have c9' : (1 : ℝ) < y := lt_of_le_of_ne c9 (Ne.symm e10)
  exact continuousAt_of_affine AppendixB.qout_10 c9' hhi

/-! ## 9.  The inner integrand in the variable `y = p/K`, and the substitution `x = 1/y`

The paper works the inner range in `x = K/p`; the axiom is stated in `y = p/K`.  The two are
related by `p R(K/p) = K · φ(p/K)` with `φ(y) = y R(1/y)`, and by the change of variables
`x = 1/y`, which turns `∫_{1/M}^{1/3} φ(y) dy` into `∫_3^M R(x) x^{-3} dx`. -/

/-- `φ_in(y) = y R(1/y)`: the inner limiting integrand in the variable `y = p/K`. -/
def phiIn (y : ℝ) : ℝ := y * RR (1 / y)

/-- **The change of variables `x = 1/y`**: `∫_{1/M}^{1/3} y R(1/y) dy = ∫_3^M R(x) x^{-3} dx`. -/
lemma integral_inv_subst {M : ℕ} (hM : 40 ≤ M) :
    (∫ y in (1 / (M : ℝ))..(1 / ((3 : ℕ) : ℝ)), phiIn y)
      = ∫ x in (3 : ℝ)..(M : ℝ), RR x / x ^ 3 := by
  have h3 : ((3 : ℕ) : ℝ) = 3 := by norm_num
  rw [h3]
  have h3M : (3 : ℝ) < (M : ℝ) := by
    have : (3 : ℕ) < M := by omega
    exact_mod_cast this
  have hM0 : (0 : ℝ) < (M : ℝ) := by linarith
  have hlo : (0 : ℝ) < 1 / (M : ℝ) := by positivity
  have hle : 1 / (M : ℝ) ≤ (1 / 3 : ℝ) := by
    rw [div_le_div_iff₀ hM0 (by norm_num)]; linarith
  set s : Set ℝ := Ioo (1 / (M : ℝ)) (1 / 3 : ℝ) with hs
  have hspos : ∀ y ∈ s, (0 : ℝ) < y := by
    intro y hy; exact lt_trans hlo hy.1
  have himg : (fun y : ℝ => y⁻¹) '' s = Ioo (3 : ℝ) (M : ℝ) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hy0 : (0 : ℝ) < y := hspos y hy
      constructor
      · rw [lt_inv_comm₀ (by norm_num) hy0]
        simpa using hy.2
      · rw [inv_lt_comm₀ hy0 hM0]
        simpa [one_div] using hy.1
    · rintro ⟨hx1, hx2⟩
      have hx0 : (0 : ℝ) < x := by linarith
      refine ⟨x⁻¹, ⟨?_, ?_⟩, by simp [inv_inv]⟩
      · rw [one_div, inv_lt_inv₀ hM0 hx0]; exact hx2
      · rw [one_div, inv_lt_inv₀ hx0 (by norm_num)]; exact hx1
  have hderiv : ∀ y ∈ s, HasDerivWithinAt (fun z : ℝ => z⁻¹) (-((y : ℝ) ^ 2)⁻¹) s y := by
    intro y hy
    exact (hasDerivAt_inv (ne_of_gt (hspos y hy))).hasDerivWithinAt
  have hinj : InjOn (fun y : ℝ => y⁻¹) s := by
    intro u hu v hv huv
    have hu0 : (0 : ℝ) < u := hspos u hu
    have hv0 : (0 : ℝ) < v := hspos v hv
    simpa [inv_inj] using huv
  have hsub := MeasureTheory.integral_image_eq_integral_abs_deriv_smul
    (f := fun y : ℝ => y⁻¹) (f' := fun y : ℝ => -((y : ℝ) ^ 2)⁻¹) (s := s)
    measurableSet_Ioo hderiv hinj (fun x : ℝ => RR x / x ^ 3)
  rw [himg] at hsub
  rw [intervalIntegral.integral_of_le hle, intervalIntegral.integral_of_le (le_of_lt h3M),
    MeasureTheory.integral_Ioc_eq_integral_Ioo, MeasureTheory.integral_Ioc_eq_integral_Ioo,
    hsub]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo (fun y hy => ?_)
  have hy0 : (0 : ℝ) < y := hspos y hy
  have habs : |-((y : ℝ) ^ 2)⁻¹| = ((y : ℝ) ^ 2)⁻¹ := by
    rw [abs_neg, abs_of_pos (by positivity)]
  simp only [phiIn, one_div, smul_eq_mul, habs]
  rw [inv_pow]
  field_simp

/-! ## 9b.  `R` is bounded and continuous off a finite set on `[3,M]`

The paper's sentence after (5.6), p. 14: *"These functions are bounded and piecewise
polynomial on each compact subinterval of `[3,∞)`."*  This section **proves** it, in the form
the prime-number-theorem axiom needs, from Appendix B's closed form `Gam_eq` for `Γ`. -/

/-- `⌊·⌋ : ℝ → ℝ` is continuous away from the integers. -/
lemma continuousAt_floorR {x : ℝ} (h : Int.fract x ≠ 0) :
    ContinuousAt (fun z : ℝ => (⌊z⌋ : ℝ)) x := by
  have hne : x ≠ (⌊x⌋ : ℝ) := by
    intro hc
    refine h ?_
    simp only [Int.fract]
    linarith [hc]
  exact (_root_.continuousOn_floor ⌊x⌋).continuousAt
    (Ico_mem_nhds ((Int.floor_le x).lt_of_ne (Ne.symm hne)) (Int.lt_floor_add_one x))

lemma continuousAt_floor_mul {c x : ℝ} (h : Int.fract (c * x) ≠ 0) :
    ContinuousAt (fun z : ℝ => (⌊c * z⌋ : ℝ)) x :=
  (continuousAt_floorR h).comp (by fun_prop)

lemma continuousAt_fract_mul {c x : ℝ} (h : Int.fract (c * x) ≠ 0) :
    ContinuousAt (fun z : ℝ => Int.fract (c * z)) x := by
  have : ContinuousAt (fun z : ℝ => c * z - (⌊c * z⌋ : ℝ)) x :=
    (by fun_prop : ContinuousAt (fun z : ℝ => c * z) x).sub (continuousAt_floor_mul h)
  exact this

lemma continuousAt_d0_fract {c x : ℝ} (h : Int.fract (c * x) ≠ 0) :
    ContinuousAt (fun z : ℝ => AppendixB.d0 (Int.fract (c * z))) x := by
  have hf := continuousAt_fract_mul h
  exact (hf.min ((continuousAt_const).sub hf))

lemma continuousAt_e0_fract {c x : ℝ} (h0 : Int.fract (c * x) ≠ 0)
    (h1 : Int.fract (c * x) ≠ 1 / 2) :
    ContinuousAt (fun z : ℝ => AppendixB.e0 (Int.fract (c * z))) x := by
  have hf := continuousAt_fract_mul h0
  rcases lt_or_gt_of_ne h1 with hlt | hgt
  · have hev : ∀ᶠ z in 𝓝 x, Int.fract (c * z) < 1 / 2 := hf (Iio_mem_nhds hlt)
    refine ContinuousAt.congr (f := fun _ : ℝ => (1 : ℝ)) continuousAt_const ?_
    filter_upwards [hev] with z hz
    rw [AppendixB.e0, ite_eq_left (le_of_lt hz)]
  · have hev : ∀ᶠ z in 𝓝 x, 1 / 2 < Int.fract (c * z) := hf (Ioi_mem_nhds hgt)
    refine ContinuousAt.congr (f := fun _ : ℝ => (-1 : ℝ)) continuousAt_const ?_
    filter_upwards [hev] with z hz
    rw [AppendixB.e0, ite_eq_right (not_le.2 hz)]

/-- `fract(2u) ≠ 0` rules out both `u ∈ ℤ` and `{u} = 1/2`. -/
lemma fract_ne_of_two {u : ℝ} (h : Int.fract (2 * u) ≠ 0) :
    Int.fract u ≠ 0 ∧ Int.fract u ≠ 1 / 2 := by
  constructor
  · intro hc
    refine h ?_
    have hu : u = ((⌊u⌋ : ℤ) : ℝ) := by
      have := Int.fract (α := ℝ) u
      rw [Int.fract] at hc; linarith [hc]
    rw [hu, show (2 : ℝ) * ((⌊u⌋ : ℤ) : ℝ) = (((2 * ⌊u⌋ : ℤ)) : ℝ) by push_cast; ring,
      Int.fract_intCast]
  · intro hc
    refine h ?_
    have hu : 2 * u = (((2 * ⌊u⌋ + 1 : ℤ)) : ℝ) := by
      rw [Int.fract] at hc
      push_cast
      linarith
    rw [hu, Int.fract_intCast]

/-- The finite set of `x ∈ [a,b]` at which `c·x` is an integer. -/
def latticeFinset (c a b : ℝ) : Finset ℝ :=
  (Finset.Icc ⌈c * a⌉ ⌊c * b⌋).image (fun k : ℤ => (k : ℝ) / c)

lemma mem_latticeFinset {c a b x : ℝ} (hc : 0 < c) (hx : x ∈ Icc a b)
    (h : Int.fract (c * x) = 0) : x ∈ latticeFinset c a b := by
  obtain ⟨hxa, hxb⟩ := hx
  have hk : ((⌊c * x⌋ : ℤ) : ℝ) = c * x := by
    rw [Int.fract] at h; linarith
  refine Finset.mem_image.2 ⟨⌊c * x⌋, Finset.mem_Icc.2 ⟨?_, ?_⟩, ?_⟩
  · refine Int.ceil_le.2 ?_
    rw [hk]
    exact mul_le_mul_of_nonneg_left hxa (le_of_lt hc)
  · refine Int.le_floor.2 ?_
    rw [hk]
    exact mul_le_mul_of_nonneg_left hxb (le_of_lt hc)
  · rw [hk]
    field_simp

/-- **`R` is continuous off a finite subset of `[3,M]`.**  `R = −Γ − 𝒩`, and through
`Zeta5.AppendixB.Gam_eq` both are built from `⌊2Hz⌋`, `⌊2z⌋`, `⌊z⌋`, `⌊αz⌋`, `⌊2λz⌋` and from
`e({z}), d₀({z}), e({αz}), d₀({αz})`; all of these are continuous at every `x` at which none of
`2x, 2αx, 2Hx, 2λx` is an integer. -/
lemma RR_piecewise (M : ℕ) :
    ∃ D : Finset ℝ, ∀ x ∈ Icc (3 : ℝ) (M : ℝ), x ∉ D → ContinuousAt RR x := by
  classical
  have ha : (0 : ℝ) < 2 * ((alpha : ℚ) : ℝ) := by norm_num [alpha]
  have hH : (0 : ℝ) < 2 * ((Hcst : ℚ) : ℝ) := by norm_num [Hcst]
  have hl : (0 : ℝ) < 2 * ((lam : ℚ) : ℝ) := by norm_num [lam]
  refine ⟨latticeFinset 2 3 (M : ℝ) ∪ latticeFinset (2 * ((alpha : ℚ) : ℝ)) 3 (M : ℝ)
      ∪ latticeFinset (2 * ((Hcst : ℚ) : ℝ)) 3 (M : ℝ)
      ∪ latticeFinset (2 * ((lam : ℚ) : ℝ)) 3 (M : ℝ), ?_⟩
  intro x hx hxD
  simp only [Finset.mem_union, not_or] at hxD
  obtain ⟨⟨⟨d2, dα⟩, dH⟩, dl⟩ := hxD
  have h2 : Int.fract (2 * x) ≠ 0 := fun hc => d2 (mem_latticeFinset (by norm_num) hx hc)
  have h2a : Int.fract (2 * ((alpha : ℚ) : ℝ) * x) ≠ 0 := fun hc =>
    dα (mem_latticeFinset ha hx (by rw [mul_assoc] at hc ⊢; exact hc))
  have h2H : Int.fract (2 * ((Hcst : ℚ) : ℝ) * x) ≠ 0 := fun hc =>
    dH (mem_latticeFinset hH hx (by rw [mul_assoc] at hc ⊢; exact hc))
  have h2l : Int.fract (2 * ((lam : ℚ) : ℝ) * x) ≠ 0 := fun hc =>
    dl (mem_latticeFinset hl hx (by rw [mul_assoc] at hc ⊢; exact hc))
  obtain ⟨hf0, hf1⟩ := fract_ne_of_two h2
  have hαx : Int.fract (((alpha : ℚ) : ℝ) * x) ≠ 0
      ∧ Int.fract (((alpha : ℚ) : ℝ) * x) ≠ 1 / 2 := by
    refine fract_ne_of_two ?_
    rw [← mul_assoc]; exact h2a
  -- the continuous ingredients
  have cTR : ContinuousAt TR x := by
    have := continuousAt_floor_mul (c := 2 * ((Hcst : ℚ) : ℝ)) h2H
    exact this
  have cqR : ContinuousAt qR x := continuousAt_floor_mul (c := 2) h2
  have cflx : ContinuousAt (fun z : ℝ => (⌊z⌋ : ℝ)) x := continuousAt_floorR hf0
  have cflα : ContinuousAt (fun z : ℝ => (⌊((alpha : ℚ) : ℝ) * z⌋ : ℝ)) x :=
    continuousAt_floor_mul hαx.1
  have cfll : ContinuousAt (fun z : ℝ => (⌊2 * (((lam : ℚ) : ℝ) * z)⌋ : ℝ)) x := by
    have := continuousAt_floor_mul (c := 2 * ((lam : ℚ) : ℝ)) h2l
    simpa [mul_assoc] using this
  have cdF : ContinuousAt AppendixB.dF x := by
    have hh := continuousAt_d0_fract (c := 1) (x := x) (by simpa using hf0)
    simp only [one_mul] at hh
    exact hh
  have ceF : ContinuousAt AppendixB.eF x := by
    have hh := continuousAt_e0_fract (c := 1) (x := x) (by simpa using hf0) (by simpa using hf1)
    simp only [one_mul] at hh
    exact hh
  have cdG : ContinuousAt AppendixB.dG x := by
    have hh := continuousAt_d0_fract (c := ((alpha : ℚ) : ℝ)) (x := x) hαx.1
    exact hh
  have ceG : ContinuousAt AppendixB.eG x := by
    have hh := continuousAt_e0_fract (c := ((alpha : ℚ) : ℝ)) (x := x) hαx.1 hαx.2
    exact hh
  have csR : ContinuousAt sR x := by
    have : ContinuousAt (fun z : ℝ => ((Hcst : ℚ) : ℝ) * z - TR z / 2) x :=
      (by fun_prop : ContinuousAt (fun z : ℝ => ((Hcst : ℚ) : ℝ) * z) x).sub
        (cTR.div_const 2)
    exact this
  have cnP : ContinuousAt nPlus x := by
    have : ContinuousAt (fun z : ℝ => (2 * z - qR z) / 2) x :=
      (((by fun_prop : ContinuousAt (fun z : ℝ => 2 * z) x).sub cqR).div_const 2)
    exact this
  have cUU : ContinuousAt AppendixB.UU x := by
    have : ContinuousAt (fun z : ℝ =>
        TR z - 6 * ((alpha : ℚ) : ℝ) * z + 6 * AppendixB.eG z * AppendixB.dG z) x :=
      (cTR.sub (by fun_prop : ContinuousAt
        (fun z : ℝ => 6 * ((alpha : ℚ) : ℝ) * z) x)).add
        ((continuousAt_const.mul ceG).mul cdG)
    exact this
  have cVV : ContinuousAt AppendixB.VV x := by
    have : ContinuousAt (fun z : ℝ =>
        TR z + 6 * ((alpha : ℚ) : ℝ) * z - 2 * z - 5
          - 6 * AppendixB.eG z * AppendixB.dG z + 2 * AppendixB.eF z * AppendixB.dF z) x :=
      ((((cTR.add (by fun_prop : ContinuousAt
        (fun z : ℝ => 6 * ((alpha : ℚ) : ℝ) * z) x)).sub
        (by fun_prop : ContinuousAt (fun z : ℝ => 2 * z) x)).sub continuousAt_const).sub
        ((continuousAt_const.mul ceG).mul cdG)).add
        ((continuousAt_const.mul ceF).mul cdF)
    exact this
  have cGam : ContinuousAt Gam x := by
    have hfun : Gam = fun z : ℝ =>
        AppendixB.UU z * AppendixB.VV z * (1/2)
          + (3 * AppendixB.eG z * AppendixB.UU z - 3 * AppendixB.eG z * AppendixB.VV z - 9)
              * AppendixB.dG z
          + (-(AppendixB.eF z * AppendixB.UU z)) * AppendixB.dF z
          + (3 * AppendixB.eF z * AppendixB.eG z) * min (AppendixB.dG z) (AppendixB.dF z)
          + sR z * (2 * TR z - qR z - 5) + max 0 (sR z - nPlus z) := by
      funext z; exact AppendixB.Gam_eq z
    rw [hfun]
    exact ((((((cUU.mul cVV).mul continuousAt_const).add
      (((((continuousAt_const.mul ceG).mul cUU).sub
        ((continuousAt_const.mul ceG).mul cVV)).sub continuousAt_const).mul cdG)).add
      (((ceF.mul cUU).neg).mul cdF)).add
      (((continuousAt_const.mul ceF).mul ceG).mul (cdG.min cdF))).add
      (csR.mul (((continuousAt_const.mul cTR).sub cqR).sub continuousAt_const))).add
      (continuousAt_const.max (csR.sub cnP))
  have cNR : ContinuousAt NR x := by
    have hfun : NR = fun z : ℝ =>
        2 * ((lam : ℚ) : ℝ) * z * (⌊z⌋ : ℝ)
          - 12 * ((lam : ℚ) : ℝ) * z * (⌊((alpha : ℚ) : ℝ) * z⌋ : ℝ)
          - 2 * ((⌊2 * (((lam : ℚ) : ℝ) * z)⌋ : ℝ) * (((lam : ℚ) : ℝ) * z)
              - (⌊2 * (((lam : ℚ) : ℝ) * z)⌋ : ℝ)
                  * ((⌊2 * (((lam : ℚ) : ℝ) * z)⌋ : ℝ) + 1) / 4) := by
      funext z; rw [NR, JR]
    rw [hfun]
    exact (((by fun_prop : ContinuousAt
      (fun z : ℝ => 2 * ((lam : ℚ) : ℝ) * z) x).mul cflx).sub
      ((by fun_prop : ContinuousAt (fun z : ℝ => 12 * ((lam : ℚ) : ℝ) * z) x).mul cflα)).sub
      (continuousAt_const.mul
        ((cfll.mul (by fun_prop : ContinuousAt (fun z : ℝ => ((lam : ℚ) : ℝ) * z) x)).sub
          (((cfll.mul (cfll.add continuousAt_const))).div_const 4)))
  have hRfun : RR = fun z : ℝ => -Gam z - NR z := by funext z; rfl
  rw [hRfun]
  exact (cGam.neg).sub cNR

lemma abs_mul_le' {a b A B : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) : |a * b| ≤ A * B := by
  have hA : 0 ≤ A := le_trans (abs_nonneg a) ha
  rw [abs_mul]
  exact mul_le_mul ha hb (abs_nonneg b) hA

lemma floor_nonneg_R {a : ℝ} (ha : 0 ≤ a) : (0 : ℝ) ≤ (⌊a⌋ : ℝ) := by
  exact_mod_cast Int.floor_nonneg.2 ha

/-- **`R` is bounded on `[3,M]`**, with the crude explicit bound `200 M²`. -/
lemma RR_bddOn (M : ℕ) (hM : 40 ≤ M) :
    ∀ x ∈ Icc (3 : ℝ) (M : ℝ), |RR x| ≤ 200 * (M : ℝ) ^ 2 := by
  intro x hx
  obtain ⟨hx3, hxM⟩ := hx
  have hMR : (40 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have hM2 : 40 * (M : ℝ) ≤ (M : ℝ) ^ 2 := by nlinarith [hMR]
  have hax : |x| ≤ (M : ℝ) := abs_le.2 ⟨by linarith, hxM⟩
  have hHc : ((Hcst : ℚ) : ℝ) = 23 / 20 := by norm_num [Hcst]
  have hal : ((alpha : ℚ) : ℝ) = 3 / 40 := by norm_num [alpha]
  have hlm : ((lam : ℚ) : ℝ) = 37 / 40 := by norm_num [lam]
  have hTR1 : TR x ≤ 2 * ((Hcst : ℚ) : ℝ) * x := Int.floor_le _
  have hTR2 : (0 : ℝ) ≤ TR x := floor_nonneg_R (by rw [hHc]; linarith)
  have hqR1 : qR x ≤ 2 * x := Int.floor_le _
  have hqR2 : (0 : ℝ) ≤ qR x := floor_nonneg_R (by linarith)
  have hfl1 : ((⌊x⌋ : ℤ) : ℝ) ≤ x := Int.floor_le _
  have hfl2 : (0 : ℝ) ≤ ((⌊x⌋ : ℤ) : ℝ) := floor_nonneg_R hx0
  have hfa1 : ((⌊((alpha : ℚ) : ℝ) * x⌋ : ℤ) : ℝ) ≤ ((alpha : ℚ) : ℝ) * x := Int.floor_le _
  have hfa2 : (0 : ℝ) ≤ ((⌊((alpha : ℚ) : ℝ) * x⌋ : ℤ) : ℝ) :=
    floor_nonneg_R (by rw [hal]; linarith)
  have hfl3 : ((⌊2 * (((lam : ℚ) : ℝ) * x)⌋ : ℤ) : ℝ) ≤ 2 * (((lam : ℚ) : ℝ) * x) :=
    Int.floor_le _
  have hfl4 : (0 : ℝ) ≤ ((⌊2 * (((lam : ℚ) : ℝ) * x)⌋ : ℤ) : ℝ) :=
    floor_nonneg_R (by rw [hlm]; linarith)
  have hTRlow : 2 * ((Hcst : ℚ) : ℝ) * x < TR x + 1 := Int.lt_floor_add_one _
  have hqRlow : 2 * x < qR x + 1 := Int.lt_floor_add_one _
  have aTR : |TR x| ≤ 3 * (M : ℝ) := by
    rw [hHc] at hTR1
    exact abs_le.2 ⟨by linarith, by linarith⟩
  have aqR : |qR x| ≤ 3 * (M : ℝ) := abs_le.2 ⟨by linarith, by linarith⟩
  have asR : |sR x| ≤ 1 / 2 := by
    rw [sR, abs_le]; constructor <;> linarith
  have anP : |nPlus x| ≤ 1 / 2 := by
    rw [nPlus, abs_le]; constructor <;> linarith
  have adF : |AppendixB.dF x| ≤ 1 / 2 :=
    abs_le.2 ⟨by linarith [AppendixB.dF_nonneg x], AppendixB.dF_le x⟩
  have adG : |AppendixB.dG x| ≤ 1 / 2 :=
    abs_le.2 ⟨by linarith [AppendixB.dG_nonneg x], AppendixB.dG_le x⟩
  have aeF : |AppendixB.eF x| ≤ 1 := by
    rw [AppendixB.eF, AppendixB.e0]; split_ifs <;> norm_num
  have aeG : |AppendixB.eG x| ≤ 1 := by
    rw [AppendixB.eG, AppendixB.e0]; split_ifs <;> norm_num
  have amin : |min (AppendixB.dG x) (AppendixB.dF x)| ≤ 1 / 2 := by
    have h1 : (0 : ℝ) ≤ min (AppendixB.dG x) (AppendixB.dF x) :=
      le_min (AppendixB.dG_nonneg x) (AppendixB.dF_nonneg x)
    exact abs_le.2 ⟨by linarith, le_trans (min_le_left _ _) (AppendixB.dG_le x)⟩
  have amax : |max 0 (sR x - nPlus x)| ≤ 1 := by
    have h1 : (0 : ℝ) ≤ max 0 (sR x - nPlus x) := le_max_left _ _
    have hs := abs_le.1 asR
    have hn := abs_le.1 anP
    have h2 : max 0 (sR x - nPlus x) ≤ 1 :=
      max_le (by norm_num) (by linarith [hs.2, hn.1])
    exact abs_le.2 ⟨by linarith, h2⟩
  have aeGdG : |AppendixB.eG x * AppendixB.dG x| ≤ 1 * (1 / 2) := abs_mul_le' aeG adG
  have aeFdF : |AppendixB.eF x * AppendixB.dF x| ≤ 1 * (1 / 2) := abs_mul_le' aeF adF
  have aUU : |AppendixB.UU x| ≤ 10 * (M : ℝ) := by
    have h1 := abs_le.1 aTR
    have h2 := abs_le.1 aeGdG
    rw [AppendixB.UU, hal, abs_le]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, hx0, hxM, hMR]
  have aVV : |AppendixB.VV x| ≤ 10 * (M : ℝ) := by
    have h1 := abs_le.1 aTR
    have h2 := abs_le.1 aeGdG
    have h3 := abs_le.1 aeFdF
    rw [AppendixB.VV, hal, abs_le]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, hx0, hxM, hMR]
  have t1 : |AppendixB.UU x * AppendixB.VV x * (1 / 2)|
      ≤ (10 * (M : ℝ)) * (10 * (M : ℝ)) * (1 / 2) :=
    abs_mul_le' (abs_mul_le' aUU aVV) (by norm_num)
  have aeGUU : |AppendixB.eG x * AppendixB.UU x| ≤ 1 * (10 * (M : ℝ)) := abs_mul_le' aeG aUU
  have aeGVV : |AppendixB.eG x * AppendixB.VV x| ≤ 1 * (10 * (M : ℝ)) := abs_mul_le' aeG aVV
  have abrk : |3 * AppendixB.eG x * AppendixB.UU x - 3 * AppendixB.eG x * AppendixB.VV x - 9|
      ≤ 60 * (M : ℝ) + 9 := by
    have h1 := abs_le.1 aeGUU
    have h2 := abs_le.1 aeGVV
    rw [abs_le]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have t2 : |(3 * AppendixB.eG x * AppendixB.UU x - 3 * AppendixB.eG x * AppendixB.VV x - 9)
      * AppendixB.dG x| ≤ (60 * (M : ℝ) + 9) * (1 / 2) := abs_mul_le' abrk adG
  have aeFUU : |AppendixB.eF x * AppendixB.UU x| ≤ 1 * (10 * (M : ℝ)) := abs_mul_le' aeF aUU
  have t3 : |(-(AppendixB.eF x * AppendixB.UU x)) * AppendixB.dF x|
      ≤ (1 * (10 * (M : ℝ))) * (1 / 2) := by
    refine abs_mul_le' ?_ adF
    rw [abs_neg]; exact aeFUU
  have aeFeG : |3 * AppendixB.eF x * AppendixB.eG x| ≤ 3 := by
    have hprod := abs_mul_le' aeF aeG
    rw [show (3 : ℝ) * AppendixB.eF x * AppendixB.eG x
        = 3 * (AppendixB.eF x * AppendixB.eG x) by ring, abs_mul,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
    linarith [hprod]
  have t4 : |(3 * AppendixB.eF x * AppendixB.eG x) * min (AppendixB.dG x) (AppendixB.dF x)|
      ≤ 3 * (1 / 2) := abs_mul_le' aeFeG amin
  have alin : |2 * TR x - qR x - 5| ≤ 9 * (M : ℝ) + 5 := by
    have h1 := abs_le.1 aTR
    have h2 := abs_le.1 aqR
    rw [abs_le]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have t5 : |sR x * (2 * TR x - qR x - 5)| ≤ (1 / 2) * (9 * (M : ℝ) + 5) :=
    abs_mul_le' asR alin
  have aGam : |Gam x| ≤ 90 * (M : ℝ) ^ 2 := by
    rw [AppendixB.Gam_eq x, abs_le]
    have h1 := abs_le.1 t1
    have h2 := abs_le.1 t2
    have h3 := abs_le.1 t3
    have h4 := abs_le.1 t4
    have h5 := abs_le.1 t5
    have h6 := abs_le.1 amax
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2,
      h5.1, h5.2, h6.1, h6.2, hMR, hM2]
  have aflx : |((⌊x⌋ : ℤ) : ℝ)| ≤ (M : ℝ) := abs_le.2 ⟨by linarith, by linarith⟩
  have afla : |((⌊((alpha : ℚ) : ℝ) * x⌋ : ℤ) : ℝ)| ≤ (M : ℝ) := by
    have hb : ((alpha : ℚ) : ℝ) * x ≤ (M : ℝ) := by rw [hal]; linarith
    exact abs_le.2 ⟨by linarith, le_trans hfa1 hb⟩
  have aflm : |((⌊2 * (((lam : ℚ) : ℝ) * x)⌋ : ℤ) : ℝ)| ≤ 2 * (M : ℝ) := by
    have hb : 2 * (((lam : ℚ) : ℝ) * x) ≤ 2 * (M : ℝ) := by rw [hlm]; linarith
    exact abs_le.2 ⟨by linarith, le_trans hfl3 hb⟩
  have n1 : |2 * ((lam : ℚ) : ℝ) * x * ((⌊x⌋ : ℤ) : ℝ)| ≤ (2 * (M : ℝ)) * (M : ℝ) := by
    refine abs_mul_le' ?_ aflx
    rw [hlm, show (2 : ℝ) * (37 / 40) * x = (37 / 20) * x by ring, abs_mul,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 37 / 20)]
    linarith [hax, hMR]
  have n2 : |12 * ((lam : ℚ) : ℝ) * x * ((⌊((alpha : ℚ) : ℝ) * x⌋ : ℤ) : ℝ)|
      ≤ (12 * (M : ℝ)) * (M : ℝ) := by
    refine abs_mul_le' ?_ afla
    rw [hlm, show (12 : ℝ) * (37 / 40) * x = (111 / 10) * x by ring, abs_mul,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 111 / 10)]
    linarith [hax, hMR]
  have n3 : |((⌊2 * (((lam : ℚ) : ℝ) * x)⌋ : ℤ) : ℝ) * (((lam : ℚ) : ℝ) * x)|
      ≤ (2 * (M : ℝ)) * (M : ℝ) := by
    refine abs_mul_le' aflm ?_
    rw [hlm, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 37 / 40)]
    linarith [hax, hMR]
  have n4 : |((⌊2 * (((lam : ℚ) : ℝ) * x)⌋ : ℤ) : ℝ)
      * (((⌊2 * (((lam : ℚ) : ℝ) * x)⌋ : ℤ) : ℝ) + 1) / 4|
      ≤ ((2 * (M : ℝ)) * (2 * (M : ℝ) + 1)) / 4 := by
    have hb : |((⌊2 * (((lam : ℚ) : ℝ) * x)⌋ : ℤ) : ℝ) + 1| ≤ 2 * (M : ℝ) + 1 := by
      have h := abs_le.1 aflm
      rw [abs_le]; constructor <;> linarith [h.1, h.2]
    have hprod := abs_mul_le' aflm hb
    rw [abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ (4 : ℝ))]
    exact div_le_div_of_nonneg_right hprod (by norm_num)
  have aNR : |NR x| ≤ 30 * (M : ℝ) ^ 2 := by
    rw [NR, JR, abs_le]
    have h1 := abs_le.1 n1
    have h2 := abs_le.1 n2
    have h3 := abs_le.1 n3
    have h4 := abs_le.1 n4
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2, hMR, hM2]
  have hRRx : RR x = -Gam x - NR x := rfl
  rw [hRRx, abs_le]
  have hg := abs_le.1 aGam
  have hn := abs_le.1 aNR
  constructor <;> linarith [hg.1, hg.2, hn.1, hn.2, hMR, hM2]

/-! ## 10.  (5.7) and its §5.2 companions

What follows is exactly the list of assertions that §§5.1–5.2 make without proof.  They are
proved in `Zeta5/Uniformity.lean`; the theorem below applies that proof. -/

/-- The paper's sentence after (5.6), p. 14: *"These functions are bounded and piecewise
polynomial on each compact subinterval of `[3,∞)`."*  Formalised for `R` on `[3,M]` as
"bounded, and continuous off a finite set" — which is what a Riemann sum needs, and which is
implied by (but weaker than) "piecewise polynomial". -/
def RegR (M : ℕ) : Prop :=
  (∃ C : ℝ, ∀ x ∈ Icc (3 : ℝ) (M : ℝ), |RR x| ≤ C)
    ∧ (∃ D : Finset ℝ, ∀ x ∈ Icc (3 : ℝ) (M : ℝ), x ∉ D → ContinuousAt RR x)

/-- **The paper's p. 14 sentence, PROVED**: *"These functions are bounded and piecewise
polynomial on each compact subinterval of `[3,∞)`."*  Not assumed. -/
lemma RR_reg (M : ℕ) (hM : 40 ≤ M) : RegR M :=
  ⟨⟨200 * (M : ℝ) ^ 2, RR_bddOn M hM⟩, RR_piecewise M⟩

/-- **(5.7) (p. 14) and the two displays of §5.2 (p. 15), with the `O_M(1)` made explicit.**

THE PAPER'S CLAIMS, VERBATIM.

*  p. 14, **(5.7)**: *"For fixed `M`, uniformly in the inner range,*
   `γ_p^in = pΓ(K/p) + O_M(1),     v_p(S_K) = p𝒩(K/p) + O_M(1).`"
   → the first two conjuncts.  "Uniformly in the inner range" is rendered by putting
   the constant `C` **outside** the quantifiers over `K = 40n` and over the primes `p`
   satisfying (4.1) — which is exactly the uniformity the audit singled out as the paper's
   weakest point, and exactly what a referee needs written down.

*  p. 15, §5.2: *"Formula (4.14) gives* `−γ_p^out = K(R₀(p/K) − d(p/K)) + O(1)`*"* and
   *"The scalar contribution in this range is* `−v_p(S_K) = K(−2λ⌊1/y⌋ + Σ_{j=1}^5 (2λ−jy)_+)
   + O(1)`*"*.  Added together these are the third conjunct, with
   `T = R₀ − d − 2λ⌊1/y⌋ + Σ_{j=1}^5(2λ−jy)_+ = Zeta5.AppendixB.Tout` the integrand of (5.10).

NOTHING ELSE IS ASSUMED.  In particular the p. 14 sentence "these functions are bounded and
piecewise polynomial on each compact subinterval of `[3,∞)`" is **proved**, as `RR_reg`.

WHY THIS IS PROVED AND NOT AN AXIOM.  It is Fauzan's own claim about his own functions, not
a standard external fact; the ground rules of this formalization (README, "Ground rules")
forbid axiomatising it.  The paper justifies it
in one informal paragraph (p. 14: *"Each interval on which these counts are constant has its
number of grid points equal to its length times `p`, up to an error bounded by two.  There are
`O(M)` such intervals, and all dimensions and weights are `O(M)`.  The reserved zero block and
the change from `p/2` to `(p−1)/2` alter the number of allocated rows by `O_M(1)`.  Altering
that number changes the weight sum by `O_M(1)`.  If `2Hx` crosses an integer, allocating one
extra row to every ordinary class gives exactly the next base allocation.  The estimate is
therefore uniform at these transitions as well."*).

EVIDENCE THAT IT IS TRUE (from the final verification of the referee audit of the preprint,
README, "Provenance"; these figures supersede that audit's earlier estimates): `γ_p^in` was
computed **exactly** from (4.4)–(4.8) — including the zero block (4.7) and the
`ε`-ordering — by a cell decomposition validated against a
brute-force loop over `a = 1..(p−1)/2`, and compared with `pΓ(K/p)` in exact rational
arithmetic over every prime of the inner range at `K = 160 000, 320 000, 400 000, 640 000,
1 000 000` (`M = 40`) and `K = 520 000` (`M = 50`):
`|γ_p^in − pΓ(K/p)| ≤ 3.7 M`, uniformly in `K`, of both signs.  Restricted to primes with
`2Hx` within `0.02` of an integer — the transitions — the worst error is `+147.5`, no worse
than globally, and `Γ` was shown to be *exactly* continuous across `2Hx ∈ ℤ`.
`|v_p(S_K) − p𝒩(K/p)| ≤ 37` over the inner range, and
`|−(v_p(S_K)+γ_p^out) − K·T(p/K)| ≤ 10` over `K/3 < p ≤ 2h`, at `K = 320 000`.

PROOF: `Zeta5.Uniformity.eq_5_7_uniformity` (`Zeta5/Uniformity.lean`), with the explicit
constant `C = 400 M²` (the true constant is about `4M`; only existence is used). -/
theorem eq_5_7_uniformity (M : ℕ) (hM : 40 ≤ M) (Alloc : ∀ n, InnerAllocFamily n M) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ (n p : ℕ) (hp : IsInnerPrime n M p),
          |(((Alloc n) p hp).gammaIn : ℝ) - (p : ℝ) * Gam (((K n : ℕ) : ℝ) / (p : ℝ))| ≤ C)
      ∧ (∀ (n p : ℕ), IsInnerPrime n M p →
          |((vS n p : ℤ) : ℝ) - (p : ℝ) * NR (((K n : ℕ) : ℝ) / (p : ℝ))| ≤ C)
      ∧ (∀ (n p : ℕ), 0 < n → p.Prime → K n < 3 * p → p ≤ 2 * h n →
          |(-(((vS n p : ℤ) : ℝ) + ((gammaOut n p : ℤ) : ℝ)))
              - ((K n : ℕ) : ℝ) * AppendixB.Tout ((p : ℝ) / ((K n : ℕ) : ℝ))| ≤ C) :=
  Uniformity.eq_5_7_uniformity M hM Alloc

/-! ## 11.  The regularity of `φ_in` from the regularity of `R` -/

lemma phiIn_bdd {M : ℕ} (hM : 40 ≤ M) (hreg : RegR M) :
    ∃ C : ℝ, ∀ y ∈ Icc (1 / (M : ℝ)) (1 / ((3 : ℕ) : ℝ)), |phiIn y| ≤ C := by
  obtain ⟨⟨C, hC⟩, -⟩ := hreg
  have h3 : ((3 : ℕ) : ℝ) = 3 := by norm_num
  have h3M : (3 : ℝ) < (M : ℝ) := by
    have : (3 : ℕ) < M := by omega
    exact_mod_cast this
  refine ⟨|C|, fun y hy => ?_⟩
  obtain ⟨hy1, hy2⟩ := hy
  rw [h3] at hy2
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by positivity) hy1
  have hmem : 1 / y ∈ Icc (3 : ℝ) (M : ℝ) := by
    constructor
    · rw [le_div_iff₀ hy0]; linarith
    · rw [div_le_iff₀ hy0]
      have := hy1
      rw [div_le_iff₀ (by linarith : (0:ℝ) < (M:ℝ))] at this
      nlinarith [this, hy0]
  have h1 := hC _ hmem
  have hyle : y ≤ 1 := by linarith
  calc |phiIn y| = |y| * |RR (1 / y)| := by rw [phiIn, abs_mul]
    _ ≤ 1 * |C| := by
        refine mul_le_mul (by rw [abs_of_pos hy0]; linarith) (le_trans h1 (le_abs_self C))
          (abs_nonneg _) (by norm_num)
    _ = |C| := one_mul _

lemma phiIn_pc {M : ℕ} (hM : 40 ≤ M) (hreg : RegR M) :
    ∃ D : Finset ℝ, ∀ y ∈ Icc (1 / (M : ℝ)) (1 / ((3 : ℕ) : ℝ)), y ∉ D →
      ContinuousAt phiIn y := by
  classical
  obtain ⟨-, ⟨D, hD⟩⟩ := hreg
  have h3 : ((3 : ℕ) : ℝ) = 3 := by norm_num
  have h3M : (3 : ℝ) < (M : ℝ) := by
    have : (3 : ℕ) < M := by omega
    exact_mod_cast this
  refine ⟨D.image (fun d => 1 / d), fun y hy hyD => ?_⟩
  obtain ⟨hy1, hy2⟩ := hy
  rw [h3] at hy2
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by positivity) hy1
  have hmem : 1 / y ∈ Icc (3 : ℝ) (M : ℝ) := by
    constructor
    · rw [le_div_iff₀ hy0]; linarith
    · rw [div_le_iff₀ hy0]
      have := hy1
      rw [div_le_iff₀ (by linarith : (0:ℝ) < (M:ℝ))] at this
      nlinarith [this, hy0]
  have hnot : (1 / y) ∉ D := by
    intro hcon
    exact hyD (Finset.mem_image.2 ⟨1 / y, hcon, by field_simp⟩)
  have hRR : ContinuousAt RR (1 / y) := hD _ hmem hnot
  have hinv : ContinuousAt (fun z : ℝ => 1 / z) y := by
    exact (continuousAt_const.div continuousAt_id (ne_of_gt hy0))
  exact ContinuousAt.mul continuousAt_id (hRR.comp hinv)

/-! ## 12.  The inner and outer blocks -/

/-- `Σ_{K/M<p≤K/3} φ_in(p/K) log p`. -/
def P2 (n M : ℕ) : ℝ := ∑ p ∈ B2 n M, phiIn ((p : ℝ) / ((K n : ℕ) : ℝ)) * Real.log (p : ℝ)
/-- `Σ_{K/3<p≤2h} T(p/K) log p`. -/
def P3 (n M : ℕ) : ℝ :=
  ∑ p ∈ B3 n M, AppendixB.Tout ((p : ℝ) / ((K n : ℕ) : ℝ)) * Real.log (p : ℝ)

lemma three_lt_M {M : ℕ} (hM : 40 ≤ M) : (3 : ℝ) < (M : ℝ) := by
  have : (3 : ℕ) < M := by omega
  exact_mod_cast this

lemma inv_M_lt_inv_three {M : ℕ} (hM : 40 ≤ M) : 1 / (M : ℝ) < 1 / ((3 : ℕ) : ℝ) := by
  have h3 : ((3 : ℕ) : ℝ) = 3 := by norm_num
  rw [h3]
  have := three_lt_M hM
  rw [div_lt_div_iff₀ (by linarith) (by norm_num)]
  linarith

/-- The inner Riemann sum converges to `∫_3^M R(x)x^{-3}dx`: the paper's display on p. 15. -/
lemma tendsto_P2 {M : ℕ} (hM : 40 ≤ M) (hreg : RegR M) :
    Tendsto (fun n : ℕ => P2 n M / ((K n : ℕ) : ℝ)) atTop
      (𝓝 (∫ x in (3 : ℝ)..(M : ℝ), RR x / x ^ 3)) := by
  have h := tendsto_primeSum (1 / (M : ℝ)) (1 / ((3 : ℕ) : ℝ)) (by positivity)
    (inv_M_lt_inv_three hM) phiIn (phiIn_bdd hM hreg) (phiIn_pc hM hreg)
  rw [integral_inv_subst hM] at h
  refine Filter.Tendsto.congr (fun n => ?_) h
  rw [P2, B2_eq n M hM]

/-- The outer Riemann sum converges to `I_out`: (5.10), via Appendix B's `eq_5_10`. -/
lemma tendsto_P3 {M : ℕ} (hM : 40 ≤ M) :
    Tendsto (fun n : ℕ => P3 n M / ((K n : ℕ) : ℝ)) atTop (𝓝 ((Iout : ℚ) : ℝ)) := by
  have h3 : ((3 : ℕ) : ℝ) = 3 := by norm_num
  have h := tendsto_primeSum (1 / ((3 : ℕ) : ℝ)) (37 / 20 : ℝ) (by positivity)
    (by rw [h3]; norm_num) AppendixB.Tout ⟨200, Tout_bdd⟩ Tout_piecewise
  rw [h3] at h
  rw [AppendixB.eq_5_10] at h
  refine Filter.Tendsto.congr (fun n => ?_) h
  rw [P3, B3_eq n M hM, h3]

lemma log_nonneg_of_prime {p : ℕ} (hp : p.Prime) : (0 : ℝ) ≤ Real.log (p : ℝ) := by
  refine Real.log_nonneg ?_
  have : (1 : ℕ) ≤ p := hp.one_lt.le.trans' (by norm_num)
  exact_mod_cast this

/-- **The inner block.**  Via (5.7), `Σ_{K/M<p≤K/3}(−L_p)log p ≤ K·P₂ + 2C·θ`. -/
lemma block2_le {n M : ℕ} (hM : 40 ≤ M) (hK : 200 * M ^ 2 ≤ K n)
    (Alloc : ∀ n, InnerAllocFamily n M) {C : ℝ} (hC0 : 0 ≤ C)
    (hin1 : ∀ (n p : ℕ) (hp : IsInnerPrime n M p),
        |(((Alloc n) p hp).gammaIn : ℝ) - (p : ℝ) * Gam (((K n : ℕ) : ℝ) / (p : ℝ))| ≤ C)
    (hin2 : ∀ (n p : ℕ), IsInnerPrime n M p →
        |((vS n p : ℤ) : ℝ) - (p : ℝ) * NR (((K n : ℕ) : ℝ) / (p : ℝ))| ≤ C) :
    ∑ p ∈ B2 n M, ((-(Lp n M (Alloc n) p) : ℤ) : ℝ) * Real.log (p : ℝ)
      ≤ ((K n : ℕ) : ℝ) * P2 n M + 2 * C * S2 n M := by
  have hM0 : 0 < M := by omega
  have hK0 : 0 < K n := by nlinarith [hK, Nat.zero_le (M ^ 2), sq_nonneg M]
  have hKR : (0 : ℝ) < ((K n : ℕ) : ℝ) := by exact_mod_cast hK0
  rw [P2, S2, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum (fun p hp => ?_)
  obtain ⟨hprime, hlo, hhi⟩ := (mem_B2 hM).1 hp
  have hlo' : K n < p * M := (Nat.div_lt_iff_lt_mul hM0).1 hlo
  have hhi' : 3 * p ≤ K n := by
    have := (Nat.le_div_iff_mul_le (by norm_num : 0 < 3)).1 hhi; omega
  have hin : IsInnerPrime n M p := ⟨hprime, hM, hK, hlo', hhi'⟩
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hprime.pos
  have hLp : Lp n M (Alloc n) p = vS n p + ((Alloc n) p hin).gammaIn := by
    rw [Lp, ite_eq_right (by omega), dite_eq_left hin]
  have hRR : RR (((K n : ℕ) : ℝ) / (p : ℝ))
      = -Gam (((K n : ℕ) : ℝ) / (p : ℝ)) - NR (((K n : ℕ) : ℝ) / (p : ℝ)) := rfl
  have hbound : ((-(Lp n M (Alloc n) p) : ℤ) : ℝ)
      ≤ (p : ℝ) * RR (((K n : ℕ) : ℝ) / (p : ℝ)) + 2 * C := by
    have h1 := abs_le.1 (hin1 n p hin)
    have h2 := abs_le.1 (hin2 n p hin)
    rw [hLp]
    push_cast
    rw [hRR]
    nlinarith [h1.1, h1.2, h2.1, h2.2]
  have hphi : ((K n : ℕ) : ℝ) * phiIn ((p : ℝ) / ((K n : ℕ) : ℝ))
      = (p : ℝ) * RR (((K n : ℕ) : ℝ) / (p : ℝ)) := by
    rw [phiIn, one_div_div]
    field_simp
  have hlog : (0 : ℝ) ≤ Real.log (p : ℝ) := log_nonneg_of_prime hprime
  calc ((-(Lp n M (Alloc n) p) : ℤ) : ℝ) * Real.log (p : ℝ)
      ≤ ((p : ℝ) * RR (((K n : ℕ) : ℝ) / (p : ℝ)) + 2 * C) * Real.log (p : ℝ) :=
        mul_le_mul_of_nonneg_right hbound hlog
    _ = ((K n : ℕ) : ℝ) * (phiIn ((p : ℝ) / ((K n : ℕ) : ℝ)) * Real.log (p : ℝ))
          + 2 * C * Real.log (p : ℝ) := by rw [← mul_assoc, hphi]; ring

/-- **The outer block.**  Via the two displays of §5.2, `Σ_{K/3<p≤2h}(−L_p)log p ≤ K·P₃ + C·θ`. -/
lemma block3_le {n M : ℕ} (hM : 40 ≤ M) (hn : 0 < n)
    (Alloc : ∀ n, InnerAllocFamily n M) {C : ℝ} (hC0 : 0 ≤ C)
    (hout : ∀ (n p : ℕ), 0 < n → p.Prime → K n < 3 * p → p ≤ 2 * h n →
        |(-(((vS n p : ℤ) : ℝ) + ((gammaOut n p : ℤ) : ℝ)))
            - ((K n : ℕ) : ℝ) * AppendixB.Tout ((p : ℝ) / ((K n : ℕ) : ℝ))| ≤ C) :
    ∑ p ∈ B3 n M, ((-(Lp n M (Alloc n) p) : ℤ) : ℝ) * Real.log (p : ℝ)
      ≤ ((K n : ℕ) : ℝ) * P3 n M + C * S3 n M := by
  rw [P3, S3, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum (fun p hp => ?_)
  obtain ⟨hprime, hlo, hhi⟩ := (mem_B3 hM).1 hp
  have hlo' : K n < p * 3 := (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 3)).1 hlo
  have hlo3 : K n < 3 * p := by omega
  have hnotB1 : ¬ (p * M ≤ K n) := by
    have : p * 3 ≤ p * M := Nat.mul_le_mul_left p (by omega)
    omega
  have hnotin : ¬ IsInnerPrime n M p := fun hcon => by
    have := hcon.upper; omega
  have hLp : Lp n M (Alloc n) p = vS n p + gammaOut n p := by
    rw [Lp, ite_eq_right hnotB1, dite_eq_right hnotin]
  have hbound : ((-(Lp n M (Alloc n) p) : ℤ) : ℝ)
      ≤ ((K n : ℕ) : ℝ) * AppendixB.Tout ((p : ℝ) / ((K n : ℕ) : ℝ)) + C := by
    have h1 := abs_le.1 (hout n p hn hprime hlo3 hhi)
    rw [hLp]
    push_cast
    linarith [h1.2]
  have hlog : (0 : ℝ) ≤ Real.log (p : ℝ) := log_nonneg_of_prime hprime
  calc ((-(Lp n M (Alloc n) p) : ℤ) : ℝ) * Real.log (p : ℝ)
      ≤ (((K n : ℕ) : ℝ) * AppendixB.Tout ((p : ℝ) / ((K n : ℕ) : ℝ)) + C) * Real.log (p : ℝ) :=
        mul_le_mul_of_nonneg_right hbound hlog
    _ = ((K n : ℕ) : ℝ) * (AppendixB.Tout ((p : ℝ) / ((K n : ℕ) : ℝ)) * Real.log (p : ℝ))
          + C * Real.log (p : ℝ) := by ring

/-! ## 13.  Proposition 5.2 -/

/-- **Proposition 5.2, (5.11)** (p. 15).  For each fixed integer `M ≥ 40`,

`limsup_{K→∞, 40|K} K^{-2} log m_{K,M} ≤ I_out + 6λ/M + ∫_3^M R(x) x^{-3} dx`,

stated in `ε`–`n₀` form with `K = 40n` (equivalent to the printed `limsup ≤ …`).

The proof is the paper's own: `log m_{K,M} = Σ_{p≤2h}(−L_p)log p` splits along the three
branches of (5.1); branch 1 is `6h θ(K/M) + O(K^{3/2}log K) + O(K)`; branches 2 and 3 are
turned into `K²∫_3^M R x^{-3}` and `K² I_out` by (5.7), the §5.2 displays and partial
summation against the prime number theorem. -/
theorem prop_5_2 (M : ℕ) (hM : 40 ≤ M) (Alloc : ∀ n, InnerAllocFamily n M)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      Real.log ((mKM n M (Alloc n) : ℚ) : ℝ)
        ≤ (((Iout : ℚ) : ℝ) + 6 * ((lam : ℚ) : ℝ) / (M : ℝ)
            + (∫ x in (3 : ℝ)..(M : ℝ), RR x / x ^ 3) + ε) * ((K n : ℕ) : ℝ) ^ 2 := by
  obtain ⟨C, hC0, hin1, hin2, hout⟩ := eq_5_7_uniformity M hM Alloc
  have hreg : RegR M := RR_reg M hM
  have hM0 : (0 : ℝ) < (M : ℝ) := by
    have : 0 < M := by omega
    exact_mod_cast this
  have tinv : Tendsto (fun n : ℕ => 1 / ((K n : ℕ) : ℝ)) atTop (𝓝 0) := by
    simp only [one_div]
    exact tendsto_inv_atTop_zero.comp tendsto_K
  have p1 := (tendsto_S1 hM).const_mul (111 / 20 : ℝ)
  have p2 := tendsto_ErrNum
  have p3 := tendsto_P2 hM hreg
  have p4 : Tendsto
      (fun n : ℕ => (2 * C) * ((S2 n M / ((K n : ℕ) : ℝ)) * (1 / ((K n : ℕ) : ℝ))))
      atTop (𝓝 0) := by
    have hh := ((tendsto_S2 hM).mul tinv).const_mul (2 * C)
    simpa only [mul_zero] using hh
  have p5 := tendsto_P3 (M := M) hM
  have p6 : Tendsto
      (fun n : ℕ => C * ((S3 n M / ((K n : ℕ) : ℝ)) * (1 / ((K n : ℕ) : ℝ))))
      atTop (𝓝 0) := by
    have hh := ((tendsto_S3 hM).mul tinv).const_mul C
    simpa only [mul_zero] using hh
  have hV := (((((p1.add p2).add p3).add p4).add p5).add p6)
  have hlt0 : (111 / 20 : ℝ) * (1 / (M : ℝ)) + 0
        + (∫ x in (3 : ℝ)..(M : ℝ), RR x / x ^ 3) + 0 + ((Iout : ℚ) : ℝ) + 0
      < ((Iout : ℚ) : ℝ) + 6 * ((lam : ℚ) : ℝ) / (M : ℝ)
          + (∫ x in (3 : ℝ)..(M : ℝ), RR x / x ^ 3) + ε := by
    have hlam : ((lam : ℚ) : ℝ) = 37 / 40 := by norm_num [lam]
    rw [hlam, show 6 * (37 / 40 : ℝ) / (M : ℝ) = (111 / 20 : ℝ) * (1 / (M : ℝ)) by ring]
    linarith
  have hstep := hV.eventually_lt_const hlt0
  have hfinal : ∀ᶠ n : ℕ in atTop,
      Real.log ((mKM n M (Alloc n) : ℚ) : ℝ)
        ≤ (((Iout : ℚ) : ℝ) + 6 * ((lam : ℚ) : ℝ) / (M : ℝ)
            + (∫ x in (3 : ℝ)..(M : ℝ), RR x / x ^ 3) + ε) * ((K n : ℕ) : ℝ) ^ 2 := by
    filter_upwards [eventually_ge_atTop (5 * M ^ 2), eventually_gt_atTop 0, hstep]
      with n hn1 hn2 hlt
    have hK : 200 * M ^ 2 ≤ K n := by simp only [K]; omega
    have hKv : ((K n : ℕ) : ℝ) = 40 * (n : ℝ) := by simp only [K]; push_cast; ring
    have hhv : ((h n : ℕ) : ℝ) = 37 * (n : ℝ) := by simp only [h]; push_cast; ring
    have hnne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    have hKpos : (0 : ℝ) < ((K n : ℕ) : ℝ) := by
      rw [hKv]
      have : (0 : ℝ) < (n : ℝ) := by
        have : 0 < n := hn2
        exact_mod_cast this
      linarith
    have hsum : Real.log ((mKM n M (Alloc n) : ℚ) : ℝ)
        = (∑ p ∈ B1 n M, ((-(Lp n M (Alloc n) p) : ℤ) : ℝ) * Real.log (p : ℝ))
          + (∑ p ∈ B2 n M, ((-(Lp n M (Alloc n) p) : ℤ) : ℝ) * Real.log (p : ℝ))
          + (∑ p ∈ B3 n M, ((-(Lp n M (Alloc n) p) : ℤ) : ℝ) * Real.log (p : ℝ)) := by
      rw [log_mKM n M (Alloc n), sum_split n M]
    have hb1 := block1_le hM hn2 (Alloc n)
    have hb2 := block2_le hM hK Alloc hC0 hin1 hin2
    have hb3 := block3_le hM hn2 Alloc hC0 hout
    have hUbound : Real.log ((mKM n M (Alloc n) : ℚ) : ℝ)
        ≤ 6 * ((h n : ℕ) : ℝ) * S1 n M + ErrNum n
          + (((K n : ℕ) : ℝ) * P2 n M + 2 * C * S2 n M)
          + (((K n : ℕ) : ℝ) * P3 n M + C * S3 n M) := by
      rw [hsum]
      unfold ErrNum
      linarith [hb1, hb2, hb3]
    have hid : 6 * ((h n : ℕ) : ℝ) * S1 n M + ErrNum n
          + (((K n : ℕ) : ℝ) * P2 n M + 2 * C * S2 n M)
          + (((K n : ℕ) : ℝ) * P3 n M + C * S3 n M)
        = ((111 / 20 : ℝ) * (S1 n M / ((K n : ℕ) : ℝ))
            + ErrNum n / ((K n : ℕ) : ℝ) ^ 2
            + P2 n M / ((K n : ℕ) : ℝ)
            + (2 * C) * ((S2 n M / ((K n : ℕ) : ℝ)) * (1 / ((K n : ℕ) : ℝ)))
            + P3 n M / ((K n : ℕ) : ℝ)
            + C * ((S3 n M / ((K n : ℕ) : ℝ)) * (1 / ((K n : ℕ) : ℝ))))
          * ((K n : ℕ) : ℝ) ^ 2 := by
      rw [hKv, hhv]
      field_simp
      ring
    rw [hid] at hUbound
    refine le_trans hUbound ?_
    exact mul_le_mul_of_nonneg_right (le_of_lt hlt) (by positivity)
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 hfinal
  exact ⟨n₀, fun n hn => hn₀ n hn⟩

end

end PrimeSum
end Zeta5
