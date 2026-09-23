/-
Zeta5/Uniformity.lean

**(5.7) (p. 14) and the two displays of §5.2 (p. 15), with the `O_M(1)` made uniform.**

This file proves `Zeta5.PrimeSum.eq_5_7_uniformity`.  Its statement lives, unchanged, in
`PrimeSum.lean`, which imports this file; `eq_5_7_uniformity` below has literally the same
type.  The constant is explicit: `C = 400 M²` (the true size is about `4M`; the statement
only asks for existence).

THE ROUTE.

*  Inner `γ` (first conjunct, §5).  For `1 ≤ a ≤ m = (p-1)/2` the class `a` contributes
   `L_a(L_a + 2b_a - ℓ_K(a) - 5)` with `L_a = T - b_a + ε_a`; this is
   `F_T(a) + ε_a(2T - ℓ_K(a) - 4)` with `F_T(a) = (T - b_a)(T + b_a - ℓ_K(a) - 5)`
   (`gammaIn_expand`).
   -  `ℓ_A(a) = ℓ(A/p, a/p)` exactly (`ell_eq_ellR`), so `F_T(a)` is the integrand of (5.4)
      at `z = a/p`.  Off the two breakpoints `z = d_f, d_g` that integrand is the polynomial in
      two indicators of Appendix B.1 (`integrand_eq`, the computation inside
      `AppendixB.Gam_eq`, for a general `T`).  At fixed `x` there are only these two
      breakpoints in `z ∈ (0,1/2)`, so the Riemann sum is elementary: grid counts against
      lengths (`count_lt`), plus `O(M²)` for each of the two breakpoint cells
      (`sum_exceptional`).  This is `riemann`: `|∑_a F_T(a) - p I(T)| ≤ 250 M²`, where
      `I(T)` is the closed form of the `z`-integral.
   -  The extras: `ℓ_K(a) ∈ {q, q+1}` (`ellK_mem`) and "the first `E` classes in decreasing
      order of `ℓ_K`" (the field `hExtraOrder`, whatever the tie-breaking) give
      `∑ ε_a ℓ_K(a) = Eq + min(E, U)` exactly (`eps_ell_sum`), with
      `U = #{a : ℓ_K(a) = q+1} = K - m_K - mq` (`U_eq`), which is `p n₊` up to `1/2`.
   -  The transition remark of p. 14 ("if `2Hx` crosses an integer, allocating one extra row
      to every ordinary class gives exactly the next base allocation") is the identity
      `IT_succ`: `I(T+1) - I(T) = T - x - 2`.  By `T_lt`/`T_gt` the discrete `T` is `⌊2Hx⌋`
      or `⌊2Hx⌋ - 1` (`T_cases`); in the second case `E < m` forces `ps = O(M)` and the
      identity closes the gap (`assembly`).
   -  The zero block has `L₀ = 4M+10` rows of weight `O(M)` (`Z0_bound`).
*  `v_p(S_K)` (second conjunct, §3): Legendre with `p² > 2K` (`vS_large`) and
   `pJ(h/p) - ∑_{i<h} ⌊2i/p⌋ ∈ [0, ⌊2h/p⌋]` (`Gs_bound`, by induction on `h`).  Bound `4M`.
*  Outer range (third conjunct, §4): `K·T(p/K)` is an explicit integer (`K_mul_Tout`), the
   floor sum is handled by `Gs_bound` again (`S5_sub_Gs`), and the rest of the comparison with
   `-(v_p(S_K) + γ_p^out)` is linear integer arithmetic with `min`/`max`, closed by `omega` in
   each of the three ranges `K/3 < p < K/2`, `K/2 < p < K`, `p > K` (`outer_core`; `p = K/2`
   and `p = K` are excluded because `20n`, `40n` are not prime).  Bound `30`.

KNOWN-ANSWER CONTROLS (exact rational arithmetic, `numerics/uniformity/`):
over every prime of the relevant ranges at `K = 160 000` and `K = 320 000`, `M = 40`,
`γ_p^in - pΓ(K/p) ∈ [-151, 149]`, `v_p(S_K) - p𝒩(K/p) ∈ [3, 37]`,
`-(v_p(S_K)+γ_p^out) - K T(p/K) ∈ [-10, 2]`; every intermediate statement of this file
(`riemann`, `Gam_split`, `IT_succ`, `eps_ell_sum`, `U_eq`, `T_cases`, `Z0_bound`, `delta_eq`,
`Gs_bound`, the bound of `assembly`) was tested there before it was proved.

Nothing here is assumed: no axiom, no `sorry`.
-/
import Zeta5.Arithmetic
import Zeta5.AppendixB

namespace Zeta5
namespace Uniformity

open Finset

noncomputable section

/-! ## §1.  Floors of quotients of naturals -/

/-- `⌊a/b⌋` computed in `ℝ` is the natural-number quotient. -/
lemma floor_natDiv (a b : ℕ) : ⌊((a : ℝ) / (b : ℝ))⌋ = ((a / b : ℕ) : ℤ) := by
  rw [← Nat.floor_div_eq_div (K := ℝ) a b]
  exact (Int.natCast_floor_eq_floor (by positivity)).symm

/-! ## §2.  The floor sum `∑_{i=1}^{h-1} ⌊2i/p⌋` -/

/-- `∑_{i=1}^{h-1} ⌊2i/p⌋`, the sum in (5.3) at `a = 1`. -/
def Gs (hh p : ℕ) : ℕ := ∑ i ∈ Icc 1 (hh - 1), 2 * i / p

/-- `pJ(h/p) = m h - p m(m+1)/4` with `m = ⌊2h/p⌋`. -/
def fG (hh p : ℕ) : ℝ :=
  ((2 * hh / p : ℕ) : ℝ) * hh - (p : ℝ) * ((2 * hh / p : ℕ) : ℝ) * (((2 * hh / p : ℕ) : ℝ) + 1) / 4


lemma Gs_eq_range (hh p : ℕ) : Gs hh p = ∑ i ∈ range hh, 2 * i / p := by
  rcases Nat.eq_zero_or_pos hh with rfl | hpos
  · simp [Gs]
  · rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hpos]
    simp only [mul_zero, Nat.zero_div, zero_add, Gs]
    congr 1

/-- Induction on `h`: `D(h) = pJ(h/p) - ∑_{i<h}⌊2i/p⌋` is unchanged when `⌊2h/p⌋` is, and
increases by `h + 1 - p(m+1)/2 ∈ [0,1)` when `⌊2h/p⌋` steps from `m` to `m+1`. -/
lemma Gs_bound_range (p : ℕ) (hp : 2 ≤ p) : ∀ hh : ℕ,
    0 ≤ fG hh p - ((∑ i ∈ range hh, 2 * i / p : ℕ) : ℝ) ∧
      fG hh p - ((∑ i ∈ range hh, 2 * i / p : ℕ) : ℝ) ≤ ((2 * hh / p : ℕ) : ℝ) := by
  intro hh
  induction hh with
  | zero => simp [fG]
  | succ k ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have hp0 : 0 < p := by omega
    obtain ⟨m, hm⟩ : ∃ m, 2 * k / p = m := ⟨_, rfl⟩
    obtain ⟨m', hm'⟩ : ∃ m', 2 * (k + 1) / p = m' := ⟨_, rfl⟩
    have a1 : p * m ≤ 2 * k := by rw [← hm, mul_comm]; exact Nat.div_mul_le_self _ _
    have a2 : 2 * k < p * (m + 1) := by rw [← hm, mul_comm]; exact Nat.lt_mul_div_succ _ hp0
    have b1 : p * m' ≤ 2 * (k + 1) := by rw [← hm', mul_comm]; exact Nat.div_mul_le_self _ _
    have b2 : 2 * (k + 1) < p * (m' + 1) := by
      rw [← hm', mul_comm]; exact Nat.lt_mul_div_succ _ hp0
    have c1 : m ≤ m' := by
      by_contra hc
      push Not at hc
      have : p * (m' + 1) ≤ p * m := Nat.mul_le_mul_left _ hc
      omega
    have c2 : m' ≤ m + 1 := by
      by_contra hc
      push Not at hc
      have : p * (m + 2) ≤ p * m' := Nat.mul_le_mul_left _ hc
      have : p * (m + 2) = p * (m + 1) + p := by ring
      omega
    rw [Finset.sum_range_succ, Nat.cast_add, hm]
    obtain ⟨S, hS⟩ : ∃ S, (∑ i ∈ range k, 2 * i / p) = S := ⟨_, rfl⟩
    rw [hS] at ih1 ih2 ⊢
    have hfk : fG k p = (m : ℝ) * k - (p : ℝ) * m * ((m : ℝ) + 1) / 4 := by
      simp only [fG, hm]
    have hfk1 : fG (k + 1) p = (m' : ℝ) * ((k : ℝ) + 1) - (p : ℝ) * m' * ((m' : ℝ) + 1) / 4 := by
      simp only [fG, hm']; push_cast; ring
    rw [hfk] at ih1 ih2
    rw [hfk1, hm']
    rw [hm] at ih2
    rcases (show m' = m ∨ m' = m + 1 by omega) with h | h
    · subst h
      constructor <;> nlinarith
    · subst h
      have e1 : (2 * (k : ℝ)) < (p : ℝ) * ((m : ℝ) + 1) := by exact_mod_cast a2
      have e2 : (p : ℝ) * ((m : ℝ) + 1) ≤ 2 * ((k : ℝ) + 1) := by exact_mod_cast b1
      push_cast
      constructor <;> nlinarith

/-- The paper's `∑_{i=1}^{h-1} ⌊2i/p⌋ = pJ(h/p) + O_M(1)` (p. 14), with the error made
explicit: `0 ≤ pJ(h/p) - ∑ ≤ ⌊2h/p⌋`. -/
lemma Gs_bound (hh p : ℕ) (hp : 2 ≤ p) :
    0 ≤ fG hh p - (Gs hh p : ℝ) ∧ fG hh p - (Gs hh p : ℝ) ≤ ((2 * hh / p : ℕ) : ℝ) := by
  rw [Gs_eq_range]; exact Gs_bound_range p hp hh

/-! ## §3.  Legendre's formula (5.3) when `p² > 2K`, and the second conjunct -/

/-- Legendre's sum `∑_{a≥1}⌊m/p^a⌋` collapses to `⌊m/p⌋` when `m ≤ 2K < p²`. -/
lemma leg_single {n p m : ℕ} (hp : p.Prime) (h1 : p ≤ 2 * K n) (h2 : 2 * K n < p ^ 2)
    (hm : m ≤ 2 * K n) :
    ∑ a ∈ Finset.Ico 1 (legBound n p), m / p ^ a = m / p := by
  have hlog : 1 ≤ Nat.log p (2 * K n) :=
    Nat.le_log_of_pow_le hp.one_lt (by simpa using h1)
  have hB : 1 < legBound n p := by unfold legBound; omega
  rw [Finset.sum_eq_sum_Ico_succ_bot hB, pow_one, Finset.sum_eq_zero, add_zero]
  intro a ha
  rw [Finset.mem_Ico] at ha
  apply Nat.div_eq_of_lt
  calc m ≤ 2 * K n := hm
    _ < p ^ 2 := h2
    _ ≤ p ^ a := Nat.pow_le_pow_right hp.pos ha.1

/-- **(5.3) for `p² > 2K`**: `v_p(S_K) = 2h⌊K/p⌋ - 12h⌊N/p⌋ - 2∑_{i=1}^{h-1}⌊2i/p⌋`. -/
lemma vS_large (n p : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) (h1 : p ≤ 2 * K n)
    (h2 : 2 * K n < p ^ 2) :
    vS n p = 2 * (h n : ℤ) * ((K n / p : ℕ) : ℤ) - 12 * (h n : ℤ) * ((N n / p : ℕ) : ℤ)
      - 2 * (Gs (h n) p : ℤ) := by
  rw [vS_eq n p hp]
  have hK : K n ≤ 2 * K n := by omega
  have hN : N n ≤ 2 * K n := by simp only [N, K]; omega
  have eK := leg_single hp h1 h2 hK
  have eN := leg_single hp h1 h2 hN
  have hi : ∀ i ∈ Icc 1 (h n - 1),
      ∑ a ∈ Finset.Ico 1 (legBound n p), ((2 * i / p ^ a : ℕ) : ℤ) = ((2 * i / p : ℕ) : ℤ) := by
    intro i hi
    have hi2 : 2 * i ≤ 2 * K n := by
      simp only [Finset.mem_Icc, h, K] at hi ⊢; omega
    rw [← leg_single hp h1 h2 hi2]; push_cast; rfl
  rw [Finset.sum_congr rfl hi]
  have h4 : padicValNat p 4 = 0 := by
    apply padicValNat.eq_zero_of_not_dvd
    intro hd
    have h22 : p ∣ 2 ^ 2 := by norm_num; exact hd
    have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h22)
    omega
  have eK' : ∑ a ∈ Finset.Ico 1 (legBound n p), ((K n / p ^ a : ℕ) : ℤ) = ((K n / p : ℕ) : ℤ) := by
    rw [← eK]; push_cast; rfl
  have eN' : ∑ a ∈ Finset.Ico 1 (legBound n p), ((N n / p ^ a : ℕ) : ℤ) = ((N n / p : ℕ) : ℤ) := by
    rw [← eN]; push_cast; rfl
  rw [eK', eN', h4, Gs]
  push_cast
  ring

/-- **Second half of (5.7)**: `|v_p(S_K) - p𝒩(K/p)| ≤ 4M` at every inner prime.  In fact
`v_p(S_K) - p𝒩(K/p) = 2(pJ(h/p) - ∑⌊2i/p⌋) ∈ [0, 2⌊2h/p⌋]`. -/
theorem vS_inner_bound (M : ℕ) (hM : 40 ≤ M) (n p : ℕ) (hp : IsInnerPrime n M p) :
    |((vS n p : ℤ) : ℝ) - (p : ℝ) * NR (((K n : ℕ) : ℝ) / (p : ℝ))| ≤ 4 * (M : ℝ) := by
  have h200 := hp.gt_200M
  have hlow := hp.lower
  have hup := hp.upper
  have hp3 : 3 ≤ p := by omega
  have h1 : p ≤ 2 * K n := by omega
  have h2 : 2 * K n < p ^ 2 := by
    have : K n * 200 < p * p := by nlinarith
    nlinarith
  rw [vS_large n p hp.prime hp3 h1 h2]
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.prime.pos
  set x : ℝ := ((K n : ℕ) : ℝ) / (p : ℝ) with hx
  have hfx : ⌊x⌋ = ((K n / p : ℕ) : ℤ) := floor_natDiv _ _
  have hax : (alpha : ℝ) * x = ((N n : ℕ) : ℝ) / (p : ℝ) := by
    rw [hx]; simp only [alpha, K, N]; push_cast; field_simp
  have hlx : (lam : ℝ) * x = ((h n : ℕ) : ℝ) / (p : ℝ) := by
    rw [hx]; simp only [lam, K, h]; push_cast; field_simp
  have h2lx : 2 * ((lam : ℝ) * x) = ((2 * h n : ℕ) : ℝ) / (p : ℝ) := by
    rw [hlx]; push_cast; ring
  have hfax : ⌊(alpha : ℝ) * x⌋ = ((N n / p : ℕ) : ℤ) := by rw [hax]; exact floor_natDiv _ _
  have hf2lx : ⌊2 * ((lam : ℝ) * x)⌋ = ((2 * h n / p : ℕ) : ℤ) := by
    rw [h2lx]; exact floor_natDiv _ _
  have hlx' : (lam : ℝ) * x * (p : ℝ) = ((h n : ℕ) : ℝ) := by
    rw [hlx]; field_simp
  have hpNR : (p : ℝ) * NR x = 2 * (h n : ℝ) * ((K n / p : ℕ) : ℝ)
      - 12 * (h n : ℝ) * ((N n / p : ℕ) : ℝ) - 2 * fG (h n) p := by
    unfold NR JR fG
    rw [hfx, hfax, hf2lx]
    simp only [Int.cast_natCast]
    linear_combination (2 * ((K n / p : ℕ) : ℝ) - 12 * ((N n / p : ℕ) : ℝ)
      - 2 * ((2 * h n / p : ℕ) : ℝ)) * hlx'
  rw [hpNR]
  obtain ⟨g1, g2⟩ := Gs_bound (h n) p (by omega)
  have hm' : ((2 * h n / p : ℕ) : ℝ) ≤ 2 * (M : ℝ) := by
    have : 2 * h n / p ≤ 2 * M := by
      apply Nat.div_le_of_le_mul
      simp only [h, K] at hlow ⊢
      nlinarith
    exact_mod_cast this
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast]
  rw [abs_le]
  constructor <;> nlinarith

/-! ## §4.  Third conjunct: the outer range -/

/-- `K R₀(p/K)` as an integer. -/
def R0Z (n p : ℕ) : ℤ :=
  if 2 * p < K n then
    8 * (K n : ℤ) - 9 * p - 8 * (N n : ℤ) - 5 * min (N n : ℤ) ((K n : ℤ) - 2 * p)
      - 5 * max 0 ((K n : ℤ) + N n - 3 * p)
  else if p < K n then
    7 * ((K n : ℤ) - p) - 6 * min (N n : ℤ) ((K n : ℤ) - p)
      - 6 * max 0 ((K n : ℤ) + N n - 2 * p) + max 0 ((K n : ℤ) + 4 * N n - 2 * p)
  else 0

/-- `K d(p/K)` as an integer. -/
def dZ (n p : ℕ) : ℤ :=
  if 2 * p < K n then max 0 ((K n : ℤ) + 4 * N n - 3 * p - max 0 ((K n : ℤ) + N n - 3 * p))
  else 0

/-- `∑_{j=1}^5 K(2λ - j p/K)_+` as an integer. -/
def S5 (n p : ℕ) : ℤ := ∑ j ∈ Icc (1 : ℕ) 5, max 0 (2 * (h n : ℤ) - ((j : ℕ) : ℤ) * (p : ℤ))

/-- `K T(p/K)` as an integer. -/
def ToutZ (n p : ℕ) : ℤ := R0Z n p - dZ n p - 2 * (h n : ℤ) * ((K n / p : ℕ) : ℤ) + S5 n p


lemma S5_expand (n p : ℕ) : S5 n p = max 0 (2 * (h n : ℤ) - p) + max 0 (2 * (h n : ℤ) - 2 * p)
    + max 0 (2 * (h n : ℤ) - 3 * p) + max 0 (2 * (h n : ℤ) - 4 * p)
    + max 0 (2 * (h n : ℤ) - 5 * p) := by
  simp [S5, Finset.sum_Icc_succ_top]

/-- `K·T(p/K)` is the integer `ToutZ n p`: (5.8), (5.9) and the scalar part of (5.10),
multiplied through by `K = 40n`. -/
lemma K_mul_Tout (n p : ℕ) (hn : 0 < n) (hp : 0 < p) :
    ((K n : ℕ) : ℝ) * AppendixB.Tout ((p : ℝ) / ((K n : ℕ) : ℝ)) = ((ToutZ n p : ℤ) : ℝ) := by
  have hK0 : (0 : ℝ) < ((K n : ℕ) : ℝ) := by
    have : 0 < K n := by simp only [K]; omega
    exact_mod_cast this
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  set Kr : ℝ := ((K n : ℕ) : ℝ) with hKr
  set y : ℝ := (p : ℝ) / Kr with hy
  have hKy : Kr * y = (p : ℝ) := by rw [hy]; field_simp
  have hα : Kr * (alpha : ℝ) = ((N n : ℕ) : ℝ) := by
    rw [hKr]; simp only [alpha, K, N]; push_cast; ring
  have hlm : Kr * (lam : ℝ) = ((h n : ℕ) : ℝ) := by
    rw [hKr]; simp only [lam, K, h]; push_cast; ring
  obtain ⟨qK, hq⟩ : ∃ q, K n / p = q := ⟨_, rfl⟩
  have hfl : (⌊1 / y⌋ : ℝ) = (qK : ℝ) := by
    have : 1 / y = Kr / (p : ℝ) := by rw [hy]; field_simp
    rw [this, hKr, floor_natDiv, hq]; simp
  have hy2 : y < 1 / 2 ↔ 2 * p < K n := by
    rw [hy, div_lt_iff₀ hK0]
    constructor
    · intro h1; have : (2 * p : ℝ) < K n := by linarith
      exact_mod_cast this
    · intro h1; have : ((2 * p : ℕ) : ℝ) < K n := by exact_mod_cast h1
      push_cast at this; linarith
  have hy1 : y < 1 ↔ p < K n := by
    rw [hy, div_lt_iff₀ hK0, one_mul]
    exact Nat.cast_lt
  have mx : ∀ t : ℝ, Kr * max 0 t = max 0 (Kr * t) := fun t => by
    rw [mul_max_of_nonneg _ _ hK0.le, mul_zero]
  have mn : ∀ a b : ℝ, Kr * min a b = min (Kr * a) (Kr * b) := fun a b =>
    mul_min_of_nonneg _ _ hK0.le
  have e1 : Kr * min (alpha : ℝ) (1 - 2 * y) = min ((N n : ℕ) : ℝ) (Kr - 2 * (p : ℝ)) := by
    rw [mn]; congr 1; linear_combination (-2) * hKy
  have e2 : Kr * max 0 (1 + (alpha : ℝ) - 3 * y) = max 0 (Kr + ((N n : ℕ) : ℝ) - 3 * (p : ℝ)) := by
    rw [mx]; congr 1; linear_combination hα - 3 * hKy
  have e3 : Kr * max 0 (1 + 4 * (alpha : ℝ) - 3 * y - max 0 (1 + (alpha : ℝ) - 3 * y))
      = max 0 (Kr + 4 * ((N n : ℕ) : ℝ) - 3 * (p : ℝ) - max 0 (Kr + ((N n : ℕ) : ℝ) - 3 * (p : ℝ))) := by
    rw [mx]; congr 1; linear_combination 4 * hα - 3 * hKy - e2
  have f1 : Kr * min (alpha : ℝ) (1 - y) = min ((N n : ℕ) : ℝ) (Kr - (p : ℝ)) := by
    rw [mn]; congr 1; linear_combination (-1) * hKy
  have f2 : Kr * max 0 (1 + (alpha : ℝ) - 2 * y) = max 0 (Kr + ((N n : ℕ) : ℝ) - 2 * (p : ℝ)) := by
    rw [mx]; congr 1; linear_combination hα - 2 * hKy
  have f3 : Kr * max 0 (1 + 4 * (alpha : ℝ) - 2 * y)
      = max 0 (Kr + 4 * ((N n : ℕ) : ℝ) - 2 * (p : ℝ)) := by
    rw [mx]; congr 1; linear_combination 4 * hα - 2 * hKy
  have g1 : Kr * max 0 (2 * (lam : ℝ) - y) = max 0 (2 * ((h n : ℕ) : ℝ) - (p : ℝ)) := by
    rw [mx]; congr 1; linear_combination 2 * hlm - hKy
  have g2 : Kr * max 0 (2 * (lam : ℝ) - 2 * y) = max 0 (2 * ((h n : ℕ) : ℝ) - 2 * (p : ℝ)) := by
    rw [mx]; congr 1; linear_combination 2 * hlm - 2 * hKy
  have g3 : Kr * max 0 (2 * (lam : ℝ) - 3 * y) = max 0 (2 * ((h n : ℕ) : ℝ) - 3 * (p : ℝ)) := by
    rw [mx]; congr 1; linear_combination 2 * hlm - 3 * hKy
  have g4 : Kr * max 0 (2 * (lam : ℝ) - 4 * y) = max 0 (2 * ((h n : ℕ) : ℝ) - 4 * (p : ℝ)) := by
    rw [mx]; congr 1; linear_combination 2 * hlm - 4 * hKy
  have g5 : Kr * max 0 (2 * (lam : ℝ) - 5 * y) = max 0 (2 * ((h n : ℕ) : ℝ) - 5 * (p : ℝ)) := by
    rw [mx]; congr 1; linear_combination 2 * hlm - 5 * hKy
  unfold AppendixB.Tout AppendixB.R0 AppendixB.dRank ToutZ R0Z dZ
  rw [S5_expand, hq, hfl]
  by_cases c2 : 2 * p < K n
  · have c1 : p < K n := by omega
    have c2' := hy2.2 c2
    simp only [c2', c2, ↓reduceIte]
    push_cast
    linear_combination (-9) * hKy + (-8) * hα + (-5) * e1 + (-5) * e2 - e3
      - 2 * (qK : ℝ) * hlm + g1 + g2 + g3 + g4 + g5
  · by_cases c1 : p < K n
    · have c2' : ¬ y < 1 / 2 := fun h => c2 (hy2.1 h)
      have c1' := hy1.2 c1
      simp only [c2', c1', c2, c1, ↓reduceIte]
      push_cast
      linear_combination (-7) * hKy + (-6) * f1 + (-6) * f2 + f3
        - 2 * (qK : ℝ) * hlm + g1 + g2 + g3 + g4 + g5
    · have c2' : ¬ y < 1 / 2 := fun h => c2 (hy2.1 h)
      have c1' : ¬ y < 1 := fun h => c1 (hy1.1 h)
      simp only [c2', c1', c2, c1, ↓reduceIte]
      push_cast
      linear_combination (- 2 * (qK : ℝ)) * hlm + g1 + g2 + g3 + g4 + g5

lemma S5_two_eq (n p : ℕ) (hp : 0 < p) (h6 : 2 * h n < 6 * p) :
    (S5 n p : ℝ) * 2 = 4 * ((2 * h n / p : ℕ) : ℝ) * (h n : ℝ)
      - (p : ℝ) * ((2 * h n / p : ℕ) : ℝ) * (((2 * h n / p : ℕ) : ℝ) + 1) := by
  obtain ⟨m, hm⟩ : ∃ m, 2 * h n / p = m := ⟨_, rfl⟩
  have a1 : p * m ≤ 2 * h n := by rw [← hm, mul_comm]; exact Nat.div_mul_le_self _ _
  have a2 : 2 * h n < p * (m + 1) := by rw [← hm, mul_comm]; exact Nat.lt_mul_div_succ _ hp
  have hm5 : m ≤ 5 := by
    by_contra hc
    push Not at hc
    have : p * 6 ≤ p * m := Nat.mul_le_mul_left _ hc
    omega
  rw [hm]
  have key : (S5 n p) * 2 = 4 * (m : ℤ) * (h n : ℤ) - (p : ℤ) * m * (m + 1) := by
    have hS : S5 n p = max 0 (2 * (h n : ℤ) - p) + max 0 (2 * (h n : ℤ) - 2 * p)
        + max 0 (2 * (h n : ℤ) - 3 * p) + max 0 (2 * (h n : ℤ) - 4 * p)
        + max 0 (2 * (h n : ℤ) - 5 * p) := by
      simp [S5, Finset.sum_Icc_succ_top]
    rw [hS]
    interval_cases m <;> push_cast <;> omega
  have := congrArg (fun z : ℤ => (z : ℝ)) key
  push_cast at this
  linarith

/-- `∑_{j≤5}(2h - jp)_+ = 2pJ(h/p)` when `⌊2h/p⌋ ≤ 5`, so it exceeds `2∑⌊2i/p⌋` by at
most `10`. -/
lemma S5_sub_Gs (n p : ℕ) (hp : 2 ≤ p) (h6 : 2 * h n < 6 * p) :
    0 ≤ S5 n p - 2 * (Gs (h n) p : ℤ) ∧ S5 n p - 2 * (Gs (h n) p : ℤ) ≤ 10 := by
  have e := S5_two_eq n p (by omega) h6
  obtain ⟨g1, g2⟩ := Gs_bound (h n) p hp
  have hm5 : ((2 * h n / p : ℕ) : ℝ) ≤ 5 := by
    have : 2 * h n / p ≤ 5 := by
      apply Nat.le_of_lt_succ
      rw [Nat.div_lt_iff_lt_mul (by omega)]
      omega
    exact_mod_cast this
  unfold fG at g1 g2
  have r1 : (0 : ℝ) ≤ ((S5 n p - 2 * (Gs (h n) p : ℤ) : ℤ) : ℝ) := by
    push_cast; nlinarith
  have r2 : ((S5 n p - 2 * (Gs (h n) p : ℤ) : ℤ) : ℝ) ≤ 10 := by
    push_cast; nlinarith
  exact ⟨by exact_mod_cast r1, by exact_mod_cast r2⟩

lemma not_prime_mul_even {p c : ℕ} (hp : p.Prime) (h14 : 3 ≤ p) (he : p = 2 * c) : False := by
  have h2 : (2 : ℕ) ∣ p := ⟨c, he⟩
  rcases hp.eq_one_or_self_of_dvd 2 h2 with h | h <;> omega

/-- The outer comparison in `ℤ`, with the floor sum abstracted as `G` and `∑_j(2h-jp)_+`
as `S`: `|γ_p^out + K R₀ - K d| ≤ 20` in each of the three ranges, by `omega`. -/
theorem outer_core (n p : ℕ) (hn : 0 < n) (hp : p.Prime) (h3 : K n < 3 * p)
    (h2 : p ≤ 2 * h n) (G S : ℤ) (hS1 : 0 ≤ S - 2 * G) (hS2 : S - 2 * G ≤ 10) :
    |(-((2 * (h n : ℤ) * ((K n / p : ℕ) : ℤ) - 12 * (h n : ℤ) * ((N n / p : ℕ) : ℤ) - 2 * G)
        + gammaOut n p))
      - (R0Z n p - dZ n p - 2 * (h n : ℤ) * ((K n / p : ℕ) : ℤ) + S)| ≤ 30 := by
  have hK : K n = 40 * n := rfl
  have hN : N n = 3 * n := rfl
  have hh : h n = 37 * n := rfl
  have hp3 : 14 ≤ p := by omega
  have hqN : N n / p = 0 := Nat.div_eq_of_lt (by omega)
  rw [hqN]
  have hdm := Nat.mod_add_div (K n) p
  rcases lt_trichotomy (2 * p) (K n) with c | c | c
  · -- `1/3 < y < 1/2`
    have hq : K n / p = 2 := Nat.div_eq_of_lt_le (by omega) (by omega)
    rw [hq] at hdm ⊢
    have hv : vOut n p = K n - 2 * p := by unfold vOut; omega
    have n1 : ¬ K n < p := by omega
    have n2 : ¬ K n < 2 * p := by omega
    simp only [gammaOut, tOut, uOut, rOut, hv, R0Z, dZ, n1, n2, c, ↓reduceIte]
    rw [hK, hN, hh] at *
    push_cast [Nat.cast_sub (show 2 * p ≤ 40 * n by omega)]
    rw [abs_le]; constructor <;> omega
  · exact (not_prime_mul_even hp (by omega) (show p = 2 * (10 * n) by omega)).elim
  · rcases lt_trichotomy p (K n) with d | d | d
    · -- `1/2 < y < 1`
      have hq : K n / p = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
      rw [hq] at hdm ⊢
      have hv : vOut n p = K n - p := by unfold vOut; omega
      have n1 : ¬ K n < p := by omega
      have n3 : ¬ 2 * p < K n := by omega
      simp only [gammaOut, tOut, uOut, rOut, hv, R0Z, dZ, n1, c, n3, d, ↓reduceIte]
      rw [hK, hN, hh] at *
      push_cast [Nat.cast_sub (show p ≤ 40 * n by omega)]
      rw [abs_le]; constructor <;> omega
    · exact (not_prime_mul_even hp (by omega) (show p = 2 * (20 * n) by omega)).elim
    · -- `y > 1`
      have hq : K n / p = 0 := Nat.div_eq_of_lt d
      rw [hq]
      clear hdm
      have n3 : ¬ 2 * p < K n := by omega
      have n4 : ¬ p < K n := by omega
      simp only [gammaOut, R0Z, dZ, d, n3, n4, ↓reduceIte]
      rw [hK, hN, hh] at *
      push_cast
      rw [abs_le]; constructor <;> omega

/-- **The two §5.2 displays together** (third conjunct): for `K/3 < p ≤ 2h`,
`|-(v_p(S_K) + γ_p^out) - K T(p/K)| ≤ 30`. -/
theorem outer_bound (n p : ℕ) (hn : 0 < n) (hp : p.Prime) (h3 : K n < 3 * p)
    (h2 : p ≤ 2 * h n) :
    |(-(((vS n p : ℤ) : ℝ) + ((gammaOut n p : ℤ) : ℝ)))
        - ((K n : ℕ) : ℝ) * AppendixB.Tout ((p : ℝ) / ((K n : ℕ) : ℝ))| ≤ 30 := by
  have hK : K n = 40 * n := rfl
  have hh : h n = 37 * n := rfl
  have h3' : 40 * n < 3 * p := by rw [← hK]; exact h3
  have h2'' : p ≤ 74 * n := by rw [← show 2 * h n = 74 * n by rw [hh]; ring]; exact h2
  have hp3 : 3 ≤ p := by omega
  have h1 : p ≤ 2 * K n := by rw [hK]; omega
  have h2' : 2 * K n < p ^ 2 := by
    rw [hK]
    have hn1 : (1 : ℕ) ≤ n := hn
    nlinarith
  have hS := S5_sub_Gs n p (by omega) (by rw [hh]; omega)
  have core := outer_core n p hn hp h3 h2 (Gs (h n) p) (S5 n p) hS.1 hS.2
  rw [← vS_large n p hp hp3 h1 h2'] at core
  rw [K_mul_Tout n p hn hp.pos]
  have hcast : ((-(vS n p + gammaOut n p) - ToutZ n p : ℤ) : ℝ)
      = (-(((vS n p : ℤ) : ℝ) + ((gammaOut n p : ℤ) : ℝ))) - ((ToutZ n p : ℤ) : ℝ) := by
    push_cast; ring
  rw [← hcast]
  exact_mod_cast core

/-! ## §5.  First conjunct: `γ_p^in = pΓ(K/p) + O_M(1)` -/

open AppendixB in
/-- `U = T - 6αx + 6 e_g d_g`, for a general `T` (`AppendixB.UU` is `T = ⌊2Hx⌋`). -/
def UUT (x T : ℝ) : ℝ := T - 6 * (alpha : ℝ) * x + 6 * eG x * dG x

open AppendixB in
/-- `V = T + 6αx - 2x - 5 - 6 e_g d_g + 2 e_f d_f`, for a general `T`. -/
def VVT (x T : ℝ) : ℝ := T + 6 * (alpha : ℝ) * x - 2 * x - 5 - 6 * eG x * dG x + 2 * eF x * dF x

open AppendixB in
/-- The closed form of `∫_0^{1/2} (T - b(x,z))(T + b(x,z) - ℓ(x,z) - 5) dz` (Appendix B.1),
for a general `T`. -/
def IT (x T : ℝ) : ℝ :=
  UUT x T * VVT x T * (1/2)
    + (3 * eG x * UUT x T - 3 * eG x * VVT x T - 9) * dG x
    + (-(eF x * UUT x T)) * dF x
    + (3 * eF x * eG x) * min (dG x) (dF x)


/-- (5.4) in closed form, with the integral written as `I(⌊2Hx⌋)` (`AppendixB.Gam_eq`). -/
lemma Gam_split (x : ℝ) :
    Gam x = IT x (TR x) + sR x * (2 * TR x - qR x - 5) + max 0 (sR x - nPlus x) := by
  rw [AppendixB.Gam_eq]; rfl

/-- **The transition identity** (p. 14: "allocating one extra row to every ordinary class
gives exactly the next base allocation"): `I(T+1) - I(T) = T - x - 2`. -/
lemma IT_succ (x T : ℝ) : IT x (T + 1) - IT x T = T - x - 2 := by
  unfold IT UUT VVT; ring

/-- `ℓ_A(a) = ℓ(A/p, a/p)` (p. 14, "note that `ℓ_A(a) = ℓ(A/p, a/p)`"). -/
lemma ell_eq_ellR (p A a : ℕ) (ha1 : 1 ≤ a) (ha2 : 2 * a < p) :
    ((ell p A a : ℕ) : ℝ) = ellR ((A : ℝ) / (p : ℝ)) ((a : ℝ) / (p : ℝ)) := by
  have hp : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have e1 : (A : ℝ) / p - (a : ℝ) / p = ((A + p - a : ℕ) : ℝ) / p - 1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; field_simp; ring
  have e2 : (A : ℝ) / p + (a : ℝ) / p = ((A + a : ℕ) : ℝ) / p := by push_cast; ring
  unfold ellR
  rw [e1, e2, Int.floor_sub_one, floor_natDiv, floor_natDiv, ell_eq p A a ha1 ha2]
  simp only [Int.cast_sub, Int.cast_natCast, Int.cast_one, Nat.cast_add]
  ring

/-- The number of grid points `a/p`, `1 ≤ a ≤ m`, below `c ∈ [0, 1/2]` is `pc` up to `1`. -/
lemma count_lt (m : ℕ) (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1 / 2) :
    |(((Icc 1 m).filter (fun a : ℕ => (a : ℝ) / ((2 * m + 1 : ℕ) : ℝ) < c)).card : ℝ)
        - ((2 * m + 1 : ℕ) : ℝ) * c| ≤ 1 := by
  set P : ℝ := ((2 * m + 1 : ℕ) : ℝ) with hPdef
  have hP : 0 < P := by rw [hPdef]; positivity
  have hPm : P = 2 * (m : ℝ) + 1 := by rw [hPdef]; push_cast; ring
  have hPc0 : 0 ≤ P * c := by positivity
  have hkle : ⌈P * c⌉₊ ≤ m + 1 := by
    rw [Nat.ceil_le]; push_cast; rw [hPm]; nlinarith
  have hfilt : (Icc 1 m).filter (fun a : ℕ => (a : ℝ) / P < c) = Ico 1 ⌈P * c⌉₊ := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ico]
    rw [div_lt_iff₀ hP, Nat.lt_ceil, mul_comm]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩
      exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩
      refine ⟨⟨h1, ?_⟩, h3⟩
      have : a < ⌈P * c⌉₊ := Nat.lt_ceil.2 h3
      omega
  rw [hfilt, Nat.card_Ico]
  have hc1' : P * c ≤ (⌈P * c⌉₊ : ℝ) := Nat.le_ceil _
  have hc2' : (⌈P * c⌉₊ : ℝ) < P * c + 1 := Nat.ceil_lt_add_one hPc0
  rcases Nat.eq_zero_or_pos ⌈P * c⌉₊ with h0 | hpos
  · rw [h0] at hc1' ⊢
    simp only [Nat.zero_sub, Nat.cast_zero, zero_sub, abs_neg]
    push_cast at hc1'
    rw [abs_le]; constructor <;> linarith
  · rw [Nat.cast_sub hpos]
    push_cast
    rw [abs_le]; constructor <;> linarith

/-- The discrete integrand `F_T(a) = (T - b_a)(T + b_a - ℓ_K(a) - 5)`. -/
def FT (n p : ℕ) (T : ℝ) (a : ℕ) : ℝ :=
  (T - 3 * (ell p (N n) a : ℝ)) * (T + 3 * (ell p (N n) a : ℝ) - (ell p (K n) a : ℝ) - 5)


open AppendixB in
/-- The integrand of (5.4) off the breakpoints `z = d_f, d_g`, for a general `T` (the
computation inside `AppendixB.Gam_eq`). -/
lemma integrand_eq (x T z : ℝ) (hz0 : 0 < z) (hz1 : z < 1 / 2) (hf : z ≠ dF x)
    (hg : z ≠ dG x) :
    (T - bR x z) * (T + bR x z - ellR x z - 5)
      = UUT x T * VVT x T
        + (3 * eG x * UUT x T - 3 * eG x * VVT x T - 9) * (if z < dG x then (1 : ℝ) else 0)
        + (-(eF x * UUT x T)) * (if z < dF x then (1 : ℝ) else 0)
        + (3 * eF x * eG x)
            * ((if z < dG x then (1 : ℝ) else 0) * (if z < dF x then (1 : ℝ) else 0)) := by
  have hfe := ellR_eq x z hz0 hz1 hf
  have hge := ellR_eq ((alpha : ℝ) * x) z hz0 hz1 hg
  have hegsq : eG x * eG x = 1 := e0_sq _
  rw [bR, hge, hfe]
  simp only [UUT, VVT, eF, eG, dF, dG] at hegsq ⊢
  by_cases hgz : z < d0 (Int.fract ((alpha : ℝ) * x)) <;>
    by_cases hfz : z < d0 (Int.fract x) <;>
      simp only [hgz, hfz, ↓reduceIte] <;>
      first
        | linear_combination (-9 : ℝ) * hegsq
        | ring

lemma abs_e0 (u : ℝ) : |AppendixB.e0 u| = 1 := by
  unfold AppendixB.e0; split <;> norm_num

/-- Two sums over a grid that agree off at most two grid points differ by at most twice the
pointwise bound. -/
lemma sum_exceptional (s : Finset ℕ) (f g : ℕ → ℝ) (P d1 d2 B : ℝ) (hP : 0 < P) (hB : 0 ≤ B)
    (heq : ∀ a ∈ s, (a : ℝ) / P ≠ d1 → (a : ℝ) / P ≠ d2 → f a = g a)
    (hb : ∀ a ∈ s, |f a - g a| ≤ B) :
    |∑ a ∈ s, f a - ∑ a ∈ s, g a| ≤ 2 * B := by
  rw [← Finset.sum_sub_distrib]
  set E := s.filter (fun a : ℕ => (a : ℝ) / P = d1 ∨ (a : ℝ) / P = d2) with hE
  have hsub : ∑ a ∈ s, (f a - g a) = ∑ a ∈ E, (f a - g a) := by
    rw [hE, Finset.sum_filter]
    refine Finset.sum_congr rfl fun a ha => ?_
    split_ifs with h
    · rfl
    · push Not at h
      rw [heq a ha h.1 h.2, sub_self]
  rw [hsub]
  have h1 : ∀ d : ℝ, (s.filter (fun a : ℕ => (a : ℝ) / P = d)).card ≤ 1 := by
    intro d
    rw [Finset.card_le_one]
    intro a ha b hb
    rw [Finset.mem_filter] at ha hb
    have hab : (a : ℝ) / P = (b : ℝ) / P := ha.2.trans hb.2.symm
    rw [div_left_inj' hP.ne'] at hab
    exact_mod_cast hab
  have hcard : E.card ≤ 2 := by
    have hsubset : E ⊆ s.filter (fun a : ℕ => (a : ℝ) / P = d1) ∪ s.filter (fun a : ℕ => (a : ℝ) / P = d2) := by
      intro a ha
      rw [hE, Finset.mem_filter] at ha
      rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
      rcases ha.2 with h | h
      · exact Or.inl ⟨ha.1, h⟩
      · exact Or.inr ⟨ha.1, h⟩
    refine le_trans (Finset.card_le_card hsubset) (le_trans (Finset.card_union_le _ _) ?_)
    have := h1 d1
    have := h1 d2
    omega
  calc |∑ a ∈ E, (f a - g a)| ≤ ∑ a ∈ E, |f a - g a| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a ∈ E, B := Finset.sum_le_sum fun a ha => hb a (Finset.mem_filter.1 ha).1
    _ = (E.card : ℝ) * B := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 2 * B := by
      have : (E.card : ℝ) ≤ 2 := by exact_mod_cast hcard
      nlinarith

lemma ell_le_real (p A a : ℕ) (ha1 : 1 ≤ a) (ha2 : 2 * a < p) (c : ℝ)
    (hA : (A : ℝ) ≤ (p : ℝ) * c) : (ell p A a : ℝ) < 2 * c + 1 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have h1 := ell_lt p A a ha1 ha2
  have h1' : (p : ℝ) * (ell p A a : ℝ) < 2 * (A : ℝ) + p := by exact_mod_cast h1
  have : (p : ℝ) * (ell p A a : ℝ) < (p : ℝ) * (2 * c + 1) := by nlinarith
  exact lt_of_mul_lt_mul_left this hp0.le

/-- The indicator `1_{z < c}`. -/
def ind (z c : ℝ) : ℝ := if z < c then 1 else 0

lemma ind_nonneg (z c : ℝ) : 0 ≤ ind z c := by unfold ind; split <;> norm_num
lemma ind_le_one (z c : ℝ) : ind z c ≤ 1 := by unfold ind; split <;> norm_num

open AppendixB in
/-- The coefficient of `1_{z<d_g}` in the integrand. -/
def cc1 (x T : ℝ) : ℝ := 3 * eG x * UUT x T - 3 * eG x * VVT x T - 9
open AppendixB in
/-- The coefficient of `1_{z<d_f}` in the integrand. -/
def cc2 (x T : ℝ) : ℝ := -(eF x * UUT x T)
open AppendixB in
/-- The coefficient of `1_{z<d_g}1_{z<d_f}` in the integrand. -/
def cc3 (x : ℝ) : ℝ := 3 * eF x * eG x

open AppendixB in
/-- The integrand of (5.4) off its two breakpoints, as a polynomial in two indicators. -/
def Rfun (x T z : ℝ) : ℝ :=
  UUT x T * VVT x T + cc1 x T * ind z (dG x) + cc2 x T * ind z (dF x)
    + cc3 x * (ind z (dG x) * ind z (dF x))

open AppendixB in
lemma IT_eq_cc (x T : ℝ) :
    IT x T = UUT x T * VVT x T * (1 / 2) + cc1 x T * dG x + cc2 x T * dF x
      + cc3 x * min (dG x) (dF x) := rfl

open AppendixB in
lemma integrand_eq_Rfun (x T z : ℝ) (hz0 : 0 < z) (hz1 : z < 1 / 2) (hf : z ≠ dF x)
    (hg : z ≠ dG x) :
    (T - bR x z) * (T + bR x z - ellR x z - 5) = Rfun x T z :=
  integrand_eq x T z hz0 hz1 hf hg

open AppendixB in
lemma closed_bounds (M : ℕ) (hM : 40 ≤ M) (x T : ℝ) (hx0 : 0 ≤ x) (hxM : x ≤ M)
    (hT0 : 0 ≤ T) (hT : T ≤ 3 * (M : ℝ)) :
    |UUT x T| ≤ 4 * M ∧ |VVT x T| ≤ 6 * M ∧ |cc1 x T| ≤ 31 * M ∧ |cc2 x T| ≤ 4 * M
      ∧ |cc3 x| ≤ 3 := by
  have hM' : (40 : ℝ) ≤ M := by exact_mod_cast hM
  have hα : (alpha : ℝ) = 3 / 40 := by norm_num [alpha]
  have heg : |eG x| = 1 := abs_e0 _
  have hef : |eF x| = 1 := abs_e0 _
  have hegdg : |eG x * dG x| ≤ 1 / 2 := by
    rw [abs_mul, heg, abs_of_nonneg (dG_nonneg x)]; linarith [dG_le x]
  have hefdf : |eF x * dF x| ≤ 1 / 2 := by
    rw [abs_mul, hef, abs_of_nonneg (dF_nonneg x)]; linarith [dF_le x]
  have g1 := abs_le.1 hegdg
  have g2 := abs_le.1 hefdf
  have hU : |UUT x T| ≤ 4 * M := by
    rw [UUT, hα, abs_le]; constructor <;> nlinarith
  have hV : |VVT x T| ≤ 6 * M := by
    rw [VVT, hα, abs_le]; constructor <;> nlinarith
  refine ⟨hU, hV, ?_, ?_, ?_⟩
  · have h1 : |3 * eG x * UUT x T| ≤ 12 * M := by
      rw [abs_mul, abs_mul, heg]; norm_num; linarith
    have h2 : |3 * eG x * VVT x T| ≤ 18 * M := by
      rw [abs_mul, abs_mul, heg]; norm_num; linarith
    unfold cc1
    calc |3 * eG x * UUT x T - 3 * eG x * VVT x T - 9|
        ≤ |3 * eG x * UUT x T - 3 * eG x * VVT x T| + |(9 : ℝ)| := abs_sub _ _
      _ ≤ |3 * eG x * UUT x T| + |3 * eG x * VVT x T| + |(9 : ℝ)| := by
          gcongr; exact abs_sub _ _
      _ ≤ 31 * M := by rw [show |(9 : ℝ)| = 9 by norm_num]; linarith
  · rw [cc2, abs_neg, abs_mul, hef, one_mul]; exact hU
  · rw [cc3, abs_mul, abs_mul, hef, heg]; norm_num

lemma Rfun_bound (M : ℕ) (hM : 40 ≤ M) (x T z : ℝ) (hx0 : 0 ≤ x) (hxM : x ≤ M)
    (hT0 : 0 ≤ T) (hT : T ≤ 3 * (M : ℝ)) : |Rfun x T z| ≤ 25 * (M : ℝ) ^ 2 := by
  have hM' : (40 : ℝ) ≤ M := by exact_mod_cast hM
  obtain ⟨hU, hV, h1, h2, h3⟩ := closed_bounds M hM x T hx0 hxM hT0 hT
  have hUV : |UUT x T * VVT x T| ≤ 24 * (M : ℝ) ^ 2 := by
    rw [abs_mul]
    calc |UUT x T| * |VVT x T| ≤ (4 * (M : ℝ)) * (6 * (M : ℝ)) :=
          mul_le_mul hU hV (abs_nonneg _) (by positivity)
      _ = 24 * (M : ℝ) ^ 2 := by ring
  have i1 := ind_nonneg z (AppendixB.dG x)
  have i2 := ind_le_one z (AppendixB.dG x)
  have j1 := ind_nonneg z (AppendixB.dF x)
  have j2 := ind_le_one z (AppendixB.dF x)
  have t1 : |cc1 x T * ind z (AppendixB.dG x)| ≤ 31 * M := by
    rw [abs_mul, abs_of_nonneg i1]; nlinarith [abs_nonneg (cc1 x T)]
  have t2 : |cc2 x T * ind z (AppendixB.dF x)| ≤ 4 * M := by
    rw [abs_mul, abs_of_nonneg j1]; nlinarith [abs_nonneg (cc2 x T)]
  have t3 : |cc3 x * (ind z (AppendixB.dG x) * ind z (AppendixB.dF x))| ≤ 3 := by
    rw [abs_mul, abs_of_nonneg (mul_nonneg i1 j1)]
    have : ind z (AppendixB.dG x) * ind z (AppendixB.dF x) ≤ 1 := by nlinarith
    nlinarith [abs_nonneg (cc3 x), mul_nonneg i1 j1]
  unfold Rfun
  calc _ ≤ |UUT x T * VVT x T| + |cc1 x T * ind z (AppendixB.dG x)|
        + |cc2 x T * ind z (AppendixB.dF x)|
        + |cc3 x * (ind z (AppendixB.dG x) * ind z (AppendixB.dF x))| := by
        refine le_trans (abs_add_le _ _) ?_
        gcongr
        refine le_trans (abs_add_le _ _) ?_
        gcongr
        exact abs_add_le _ _
    _ ≤ 25 * (M : ℝ) ^ 2 := by nlinarith

lemma FT_bound (M n p : ℕ) (hM : 40 ≤ M) (hp : IsInnerPrime n M p) (T : ℝ)
    (hT0 : 0 ≤ T) (hT : T ≤ 3 * (M : ℝ)) {a : ℕ} (ha1 : 1 ≤ a) (ha2 : 2 * a < p) :
    |FT n p T a| ≤ 24 * (M : ℝ) ^ 2 := by
  have hM' : (40 : ℝ) ≤ M := by exact_mod_cast hM
  have hlow : ((K n : ℕ) : ℝ) < (p : ℝ) * M := by exact_mod_cast hp.lower
  have lN := ell_le_real p (N n) a ha1 ha2 ((3 / 40) * M) (by
    have : ((N n : ℕ) : ℝ) * 40 = 3 * ((K n : ℕ) : ℝ) := by
      simp only [K, N]; push_cast; ring
    linarith)
  have lK := ell_le_real p (K n) a ha1 ha2 M (by linarith)
  have lN0 : (0 : ℝ) ≤ (ell p (N n) a : ℝ) := by positivity
  have lK0 : (0 : ℝ) ≤ (ell p (K n) a : ℝ) := by positivity
  simp only [FT]
  rw [abs_mul]
  have b1 : |T - 3 * (ell p (N n) a : ℝ)| ≤ 4 * M := by
    rw [abs_le]; constructor <;> linarith
  have b2 : |T + 3 * (ell p (N n) a : ℝ) - (ell p (K n) a : ℝ) - 5| ≤ 6 * M := by
    rw [abs_le]; constructor <;> linarith
  calc _ ≤ (4 * (M : ℝ)) * (6 * (M : ℝ)) := mul_le_mul b1 b2 (abs_nonneg _) (by positivity)
    _ = 24 * (M : ℝ) ^ 2 := by ring

lemma FT_eq_Rfun (n p : ℕ) (T : ℝ) {a : ℕ} (ha1 : 1 ≤ a) (ha2 : 2 * a < p)
    (h1 : (a : ℝ) / p ≠ AppendixB.dF (((K n : ℕ) : ℝ) / (p : ℝ)))
    (h2 : (a : ℝ) / p ≠ AppendixB.dG (((K n : ℕ) : ℝ) / (p : ℝ))) :
    FT n p T a = Rfun (((K n : ℕ) : ℝ) / (p : ℝ)) T ((a : ℝ) / p) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hz0 : 0 < (a : ℝ) / p := by
    have : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
    positivity
  have hz1 : (a : ℝ) / p < 1 / 2 := by
    rw [div_lt_iff₀ hp0]
    have : (2 * a : ℝ) < p := by exact_mod_cast ha2
    linarith
  have hαx : (alpha : ℝ) * (((K n : ℕ) : ℝ) / (p : ℝ)) = ((N n : ℕ) : ℝ) / (p : ℝ) := by
    simp only [alpha, K, N]; push_cast; field_simp
  have eK := ell_eq_ellR p (K n) a ha1 ha2
  have eN := ell_eq_ellR p (N n) a ha1 ha2
  rw [← hαx] at eN
  rw [← integrand_eq_Rfun _ T _ hz0 hz1 h1 h2, FT, eK, eN, bR]

lemma sum_Rfun (m : ℕ) (P x T : ℝ) :
    ∑ a ∈ Icc 1 m, Rfun x T ((a : ℝ) / P)
      = (m : ℝ) * (UUT x T * VVT x T)
        + cc1 x T * (((Icc 1 m).filter (fun a : ℕ => (a : ℝ) / P < AppendixB.dG x)).card : ℝ)
        + cc2 x T * (((Icc 1 m).filter (fun a : ℕ => (a : ℝ) / P < AppendixB.dF x)).card : ℝ)
        + cc3 x * (((Icc 1 m).filter
            (fun a : ℕ => (a : ℝ) / P < min (AppendixB.dG x) (AppendixB.dF x))).card : ℝ) := by
  simp only [Rfun, ind, AppendixB.ind_mul_ind]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_const, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
    Finset.sum_boole, Finset.sum_boole, Finset.sum_boole, Nat.card_Icc, nsmul_eq_mul]
  simp

lemma D_bound (M : ℕ) (m : ℕ) (p UV c1 c2 c3 dg df mn Ng Nf Nmn : ℝ) (hpm : p = 2 * (m : ℝ) + 1)
    (hUV : |UV| ≤ 24 * (M : ℝ) ^ 2) (h1 : |c1| ≤ 31 * M) (h2 : |c2| ≤ 4 * M) (h3 : |c3| ≤ 3)
    (e1 : |Ng - p * dg| ≤ 1) (e2 : |Nf - p * df| ≤ 1) (e3 : |Nmn - p * mn| ≤ 1) :
    |(m : ℝ) * UV + c1 * Ng + c2 * Nf + c3 * Nmn - p * (UV * (1 / 2) + c1 * dg + c2 * df + c3 * mn)|
      ≤ 12 * (M : ℝ) ^ 2 + 31 * M + 4 * M + 3 := by
  have hD : (m : ℝ) * UV + c1 * Ng + c2 * Nf + c3 * Nmn
      - p * (UV * (1 / 2) + c1 * dg + c2 * df + c3 * mn)
      = -UV / 2 + c1 * (Ng - p * dg) + c2 * (Nf - p * df) + c3 * (Nmn - p * mn) := by
    rw [hpm]; ring
  have t0 : |-UV / 2| ≤ 12 * (M : ℝ) ^ 2 := by
    rw [abs_div, abs_neg, abs_two]; linarith
  have t1 : |c1 * (Ng - p * dg)| ≤ 31 * M := by
    rw [abs_mul]; nlinarith [abs_nonneg c1, abs_nonneg (Ng - p * dg)]
  have t2 : |c2 * (Nf - p * df)| ≤ 4 * M := by
    rw [abs_mul]; nlinarith [abs_nonneg c2, abs_nonneg (Nf - p * df)]
  have t3 : |c3 * (Nmn - p * mn)| ≤ 3 := by
    rw [abs_mul]; nlinarith [abs_nonneg c3, abs_nonneg (Nmn - p * mn)]
  rw [hD]
  calc _ ≤ |-UV / 2| + |c1 * (Ng - p * dg)| + |c2 * (Nf - p * df)| + |c3 * (Nmn - p * mn)| := by
        refine le_trans (abs_add_le _ _) ?_
        gcongr
        refine le_trans (abs_add_le _ _) ?_
        gcongr
        exact abs_add_le _ _
    _ ≤ _ := by linarith

/-- **The Riemann sum** (p. 14: "each interval on which these counts are constant has its
number of grid points equal to its length times `p`, up to an error bounded by two"):
`|∑_{a=1}^m F_T(a) - p I(T)| ≤ 250 M²` for `0 ≤ T ≤ 3M`. -/
theorem riemann (M n p : ℕ) (hM : 40 ≤ M) (hp : IsInnerPrime n M p) (T : ℝ)
    (hT0 : 0 ≤ T) (hT : T ≤ 3 * (M : ℝ)) :
    |(∑ a ∈ Icc 1 (mHalf p), FT n p T a) - (p : ℝ) * IT (((K n : ℕ) : ℝ) / (p : ℝ)) T|
      ≤ 250 * (M : ℝ) ^ 2 := by
  have h2m := hp.two_mHalf
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.prime.pos
  have hM' : (40 : ℝ) ≤ M := by exact_mod_cast hM
  have hlow : ((K n : ℕ) : ℝ) < (p : ℝ) * M := by exact_mod_cast hp.lower
  set x : ℝ := ((K n : ℕ) : ℝ) / (p : ℝ) with hx
  have hx0 : 0 ≤ x := by positivity
  have hxM : x ≤ M := by rw [hx, div_le_iff₀ hp0]; linarith
  -- (A)+(B)
  have hAB : |∑ a ∈ Icc 1 (mHalf p), FT n p T a
      - ∑ a ∈ Icc 1 (mHalf p), Rfun x T ((a : ℝ) / p)| ≤ 2 * (49 * (M : ℝ) ^ 2) := by
    refine sum_exceptional (Icc 1 (mHalf p)) (fun a => FT n p T a)
      (fun a => Rfun x T ((a : ℝ) / p)) (p : ℝ) (AppendixB.dF x) (AppendixB.dG x)
      (49 * (M : ℝ) ^ 2) hp0 (by positivity) ?_ ?_
    · intro a ha h1 h2
      rw [Finset.mem_Icc] at ha
      exact FT_eq_Rfun n p T ha.1 (two_mul_lt_of_le_mHalf hp.odd ha.2) h1 h2
    · intro a ha
      rw [Finset.mem_Icc] at ha
      have b1 := FT_bound M n p hM hp T hT0 hT ha.1 (two_mul_lt_of_le_mHalf hp.odd ha.2)
      have b2 := Rfun_bound M hM x T ((a : ℝ) / p) hx0 hxM hT0 hT
      calc |FT n p T a - Rfun x T ((a : ℝ) / p)|
          ≤ |FT n p T a| + |Rfun x T ((a : ℝ) / p)| := abs_sub _ _
        _ ≤ 49 * (M : ℝ) ^ 2 := by linarith
  -- (C)+(D)
  have cnt : ∀ c : ℝ, 0 ≤ c → c ≤ 1 / 2 →
      |(((Icc 1 (mHalf p)).filter (fun a : ℕ => (a : ℝ) / (p : ℝ) < c)).card : ℝ)
        - (p : ℝ) * c| ≤ 1 := by
    intro c h0 h1
    have := count_lt (mHalf p) c h0 h1
    have hc : ((2 * mHalf p + 1 : ℕ) : ℝ) = (p : ℝ) := by rw [h2m]
    rw [hc] at this
    exact this
  have hpm : (p : ℝ) = 2 * (mHalf p : ℝ) + 1 := by
    have : ((2 * mHalf p + 1 : ℕ) : ℝ) = (p : ℝ) := by rw [h2m]
    rw [← this]; push_cast; ring
  have hdg0 := AppendixB.dG_nonneg x
  have hdg1 := AppendixB.dG_le x
  have hdf0 := AppendixB.dF_nonneg x
  have hdf1 := AppendixB.dF_le x
  have e1 := cnt _ hdg0 hdg1
  have e2 := cnt _ hdf0 hdf1
  have e3 := cnt _ (le_min hdg0 hdf0) (le_trans (min_le_left _ _) hdg1)
  obtain ⟨hU, hV, h1, h2, h3⟩ := closed_bounds M hM x T hx0 hxM hT0 hT
  have hUV : |UUT x T * VVT x T| ≤ 24 * (M : ℝ) ^ 2 := by
    rw [abs_mul]
    calc |UUT x T| * |VVT x T| ≤ (4 * (M : ℝ)) * (6 * (M : ℝ)) :=
          mul_le_mul hU hV (abs_nonneg _) (by positivity)
      _ = 24 * (M : ℝ) ^ 2 := by ring
  have hDb : |∑ a ∈ Icc 1 (mHalf p), Rfun x T ((a : ℝ) / p) - (p : ℝ) * IT x T|
      ≤ 12 * (M : ℝ) ^ 2 + 31 * M + 4 * M + 3 := by
    rw [sum_Rfun, IT_eq_cc]
    exact D_bound M (mHalf p) _ _ _ _ _ _ _ _ _ _ _ hpm hUV h1 h2 h3 e1 e2 e3
  calc _ ≤ |∑ a ∈ Icc 1 (mHalf p), FT n p T a
        - ∑ a ∈ Icc 1 (mHalf p), Rfun x T ((a : ℝ) / p)|
        + |∑ a ∈ Icc 1 (mHalf p), Rfun x T ((a : ℝ) / p) - (p : ℝ) * IT x T| :=
        abs_sub_le _ _ _
    _ ≤ 250 * (M : ℝ) ^ 2 := by nlinarith

/-- `q = ⌊2K/p⌋`. -/
def qN (n p : ℕ) : ℕ := 2 * K n / p

/-- The classes with the larger value `q + 1` of `ℓ_K`. -/
def Top (n p : ℕ) : Finset ℕ := (Icc 1 (mHalf p)).filter (fun a => ell p (K n) a = qN n p + 1)


/-- `ℓ_K(a) ∈ {q, q+1}` for `1 ≤ a ≤ m`, `q = ⌊2K/p⌋`. -/
lemma ellK_mem {n M p : ℕ} (hp : IsInnerPrime n M p) {a : ℕ} (ha : a ∈ Icc 1 (mHalf p)) :
    ell p (K n) a = qN n p ∨ ell p (K n) a = qN n p + 1 := by
  rw [Finset.mem_Icc] at ha
  have h2m := hp.two_mHalf
  have hp0 : 0 < p := hp.prime.pos
  have hcl := ell_closed p (K n) a ha.1 (by omega)
  have hv : K n % p < p := Nat.mod_lt _ hp0
  have hdm : p * (K n / p) + K n % p = K n := Nat.div_add_mod _ _
  have hq : qN n p = 2 * (K n / p) + 2 * (K n % p) / p := by
    have h2K : 2 * K n = 2 * (K n % p) + p * (2 * (K n / p)) := by
      calc 2 * K n = 2 * (p * (K n / p) + K n % p) := by rw [hdm]
        _ = 2 * (K n % p) + p * (2 * (K n / p)) := by ring
    unfold qN
    rw [h2K, Nat.add_mul_div_left _ _ hp0]
    ring
  rw [hq, hcl]
  unfold mFloor
  by_cases hc : p ≤ 2 * (K n % p)
  · have h1 : 2 * (K n % p) / p = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
    rw [h1]
    split_ifs <;> omega
  · have h0 : 2 * (K n % p) / p = 0 := Nat.div_eq_of_lt (by omega)
    rw [h0]
    split_ifs <;> omega

/-- `#{a : ℓ_K(a) = q+1} = K - m_K - mq`, from `∑_a ℓ_K(a) = K - m_K` (`sum_ell`). -/
lemma U_eq {n M p : ℕ} (hp : IsInnerPrime n M p) :
    ((Top n p).card : ℝ) = (K n : ℝ) - (mFloor p (K n) : ℝ) - (mHalf p : ℝ) * (qN n p : ℝ) := by
  have hsum := sum_ell p (K n) hp.two_mHalf
  have hterm : ∀ a ∈ Icc 1 (mHalf p), ell p (K n) a
      = qN n p + (if ell p (K n) a = qN n p + 1 then 1 else 0) := by
    intro a ha
    rcases ellK_mem hp ha with h | h <;> simp [h]
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc,
    ← Finset.card_filter] at hsum
  have hmK : mFloor p (K n) ≤ K n := by
    unfold mFloor; exact Nat.div_le_self _ _
  have hc : ((K n - mFloor p (K n) : ℕ) : ℝ) = (K n : ℝ) - (mFloor p (K n) : ℝ) :=
    Nat.cast_sub hmK
  have hcast := congrArg (fun t : ℕ => (t : ℝ)) hsum
  simp only [smul_eq_mul, Nat.add_sub_cancel] at hcast
  rw [hc] at hcast
  push_cast at hcast
  unfold Top
  linarith

/-- "The extras go first to the classes with the larger value of `ℓ`" (p. 14):
`∑_a ε_a ℓ_K(a) = Eq + min(E, U)`, whatever the tie-breaking. -/
lemma eps_ell_sum {n M p : ℕ} (hp : IsInnerPrime n M p) (A : InnerAlloc n M p) :
    (∑ a ∈ Icc 1 (mHalf p), (A.eps a : ℝ) * (ell p (K n) a : ℝ))
      = (A.E : ℝ) * (qN n p : ℝ) + min (A.E : ℝ) ((Top n p).card : ℝ) := by
  set S := Icc 1 (mHalf p) with hS
  set P := S.filter (fun a => A.eps a = 1) with hP
  have hPS : P ⊆ S := Finset.filter_subset _ _
  have hTS : Top n p ⊆ S := Finset.filter_subset _ _
  -- the sum over `S` is the sum over `P`
  have h1 : (∑ a ∈ S, (A.eps a : ℝ) * (ell p (K n) a : ℝ)) = ∑ a ∈ P, (ell p (K n) a : ℝ) := by
    rw [hP, Finset.sum_filter]
    refine Finset.sum_congr rfl fun a _ => ?_
    rcases A.hEps01 a with h | h <;> simp [h]
  -- `#P = E`
  have hcardP : P.card = A.E := by
    rw [← A.hEpsSum, hP, Finset.card_filter]
    refine Finset.sum_congr rfl fun a _ => ?_
    rcases A.hEps01 a with h | h <;> simp [h]
  -- nested
  have hnest : P ⊆ Top n p ∨ Top n p ⊆ P := by
    by_contra hcon
    rw [not_or, Finset.not_subset, Finset.not_subset] at hcon
    obtain ⟨⟨a, haP, haT⟩, ⟨c, hcT, hcP⟩⟩ := hcon
    have haS := hPS haP
    have hcS := hTS hcT
    have hea : A.eps a = 1 := (Finset.mem_filter.1 haP).2
    have hec : A.eps c = 0 := by
      rcases A.hEps01 c with h | h
      · exact h
      · exact absurd (Finset.mem_filter.2 ⟨hcS, h⟩) hcP
    have hord := A.hExtraOrder a haS c hcS hea hec
    have hcq : ell p (K n) c = qN n p + 1 := (Finset.mem_filter.1 hcT).2
    have haq : ell p (K n) a ≠ qN n p + 1 := fun h => haT (Finset.mem_filter.2 ⟨haS, h⟩)
    rcases ellK_mem hp haS with h | h
    · omega
    · exact haq h
  -- the sum over `P`
  have h2 : (∑ a ∈ P, (ell p (K n) a : ℝ))
      = (P.card : ℝ) * (qN n p : ℝ) + ((P ∩ Top n p).card : ℝ) := by
    have hterm : ∀ a ∈ P, (ell p (K n) a : ℝ)
        = (qN n p : ℝ) + (if a ∈ Top n p then 1 else 0) := by
      intro a ha
      have haS := hPS ha
      rcases ellK_mem hp haS with h | h
      · have : a ∉ Top n p := fun hT => by
          have := (Finset.mem_filter.1 hT).2; omega
        simp [h, this]
      · have : a ∈ Top n p := Finset.mem_filter.2 ⟨haS, h⟩
        simp [h, this]
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
      Finset.sum_boole, Finset.filter_mem_eq_inter]
  rw [h1, h2, hcardP]
  rcases hnest with hsub | hsub
  · rw [Finset.inter_eq_left.2 hsub, hcardP]
    have : (A.E : ℝ) ≤ ((Top n p).card : ℝ) := by
      rw [← hcardP]; exact_mod_cast Finset.card_le_card hsub
    rw [min_eq_left this]
  · rw [Finset.inter_eq_right.2 hsub]
    have : ((Top n p).card : ℝ) ≤ (A.E : ℝ) := by
      rw [← hcardP]; exact_mod_cast Finset.card_le_card hsub
    rw [min_eq_right this]

/-- The zero block `∑_{i<L₀} 2w_{0,i}` of (4.8). -/
def Z0 {n M p : ℕ} (A : InnerAlloc n M p) : ℤ := ∑ i ∈ range (L0 M), A.w2zero i


lemma sum_range_affine (N : ℕ) (c : ℤ) :
    ∑ i ∈ range N, (2 * (i : ℤ) + c) = (N : ℤ) * ((N : ℤ) - 1) + (N : ℤ) * c := by
  induction N with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

/-- (4.8) summed over each class: `γ_p^in = Z₀ + ∑_a (F_T(a) + ε_a(2T - ℓ_K(a) - 4))`. -/
lemma gammaIn_expand {n M p : ℕ} (hp : IsInnerPrime n M p) (A : InnerAlloc n M p) :
    (A.gammaIn : ℝ) = (Z0 A : ℝ) + ∑ a ∈ Icc 1 (mHalf p),
      (FT n p (A.T : ℝ) a + (A.eps a : ℝ) * (2 * (A.T : ℝ) - (ell p (K n) a : ℝ) - 4)) := by
  have hcls : ∀ a ∈ Icc 1 (mHalf p), ∑ i ∈ range (A.L a).toNat, A.w2 a i
      = A.L a * (A.L a + 2 * (bCoef n p a : ℤ) - (ell p (K n) a : ℤ) - 5) := by
    intro a ha
    rw [Finset.mem_Icc] at ha
    have hL := InnerAlloc.L_nonneg hp A ha.1 ha.2
    have hw : ∀ i ∈ range (A.L a).toNat, A.w2 a i
        = 2 * (i : ℤ) + (2 * (bCoef n p a : ℤ) - (ell p (K n) a : ℤ) - 4) := by
      intro i _; simp only [InnerAlloc.w2]; ring
    rw [Finset.sum_congr rfl hw, sum_range_affine, Int.toNat_of_nonneg hL]
    ring
  have hγ : A.gammaIn = Z0 A + ∑ a ∈ Icc 1 (mHalf p),
      A.L a * (A.L a + 2 * (bCoef n p a : ℤ) - (ell p (K n) a : ℤ) - 5) := by
    rw [InnerAlloc.gammaIn, Z0, Finset.sum_congr rfl hcls]
  rw [hγ]
  push_cast
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  have he : (A.eps a : ℝ) * (A.eps a : ℝ) = (A.eps a : ℝ) := by
    rcases A.hEps01 a with h | h <;> simp [h]
  simp only [InnerAlloc.L, FT, bCoef]
  push_cast
  linear_combination he

/-- The reserved zero block contributes `O(M²)`: `L₀ = 4M+10` rows of weight in `[-3M, 18M]`. -/
lemma Z0_bound (M : ℕ) (hM : 40 ≤ M) {n p : ℕ} (hp : IsInnerPrime n M p)
    (A : InnerAlloc n M p) : |(Z0 A : ℝ)| ≤ 80 * (M : ℝ) ^ 2 := by
  obtain ⟨h2m, hmM, hmN, _⟩ := inner_facts hp
  have hTgt := T_gt_int hp A
  have hlow := hp.lower
  have hup := hp.upper
  have hp0 : 0 < p := hp.prime.pos
  -- `m_K < M`
  have hmK : mFloor p (K n) < M := by
    unfold mFloor; rw [Nat.div_lt_iff_lt_mul hp0]; linarith
  -- `T ≥ 0`
  have hT0 : 0 ≤ A.T := by
    have hK3 : (3 : ℤ) * p ≤ K n := by exact_mod_cast hup
    have hpZ : (0 : ℤ) < p := by exact_mod_cast hp0
    by_contra hneg
    push Not at hneg
    have : 20 * (p : ℤ) * A.T ≤ 0 := by nlinarith
    linarith
  -- `ℓ_K(c) ≤ 2M`
  have hell : ∀ c ∈ Icc 1 (mHalf p), (ell p (K n) c : ℤ) ≤ 2 * M := by
    intro c hc
    rw [Finset.mem_Icc] at hc
    have h1 := ell_lt p (K n) c hc.1 (two_mul_lt_of_le_mHalf hp.odd hc.2)
    have h2 : p * ell p (K n) c < p * (2 * M + 1) := by nlinarith
    have := Nat.lt_of_mul_lt_mul_left h2
    omega
  have hw : ∀ i ∈ range (L0 M), -3 * (M : ℤ) ≤ A.w2zero i ∧ A.w2zero i ≤ 18 * M := by
    intro i hi
    rw [Finset.mem_range] at hi
    unfold L0 at hi
    unfold InnerAlloc.w2zero
    constructor
    · refine le_min ?_ ?_
      · omega
      · refine Finset.le_inf' _ _ fun c hc => ?_
        have := hell c hc
        simp only [InnerAlloc.Z]
        have : (0 : ℤ) ≤ (A.eps c : ℤ) := by positivity
        omega
    · refine le_trans (min_le_left _ _) ?_
      omega
  have hsum : |(Z0 A : ℤ)| ≤ (L0 M : ℤ) * (18 * M) := by
    unfold Z0
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have : ∀ i ∈ range (L0 M), |A.w2zero i| ≤ 18 * (M : ℤ) := by
      intro i hi
      obtain ⟨a1, a2⟩ := hw i hi
      rw [abs_le]; constructor <;> omega
    refine le_trans (Finset.sum_le_sum this) ?_
    simp
  have hsumR : |(Z0 A : ℝ)| ≤ ((L0 M : ℕ) : ℝ) * (18 * M) := by
    have := (Int.cast_le (R := ℝ)).2 hsum
    push_cast at this
    exact this
  have hL0 : ((L0 M : ℕ) : ℝ) = 4 * M + 10 := by unfold L0; push_cast; ring
  rw [hL0] at hsumR
  have hM' : (40 : ℝ) ≤ M := by exact_mod_cast hM
  nlinarith

/-- By `T_lt`/`T_gt`, `2Hx - 21/20 < T < 2Hx`, so `⌊2Hx⌋ ∈ {T, T+1}`. -/
lemma T_cases {n M p : ℕ} (hp : IsInnerPrime n M p) (A : InnerAlloc n M p) :
    TR (((K n : ℕ) : ℝ) / (p : ℝ)) = (A.T : ℝ)
      ∨ TR (((K n : ℕ) : ℝ) / (p : ℝ)) = (A.T : ℝ) + 1 := by
  have h1 := T_lt_int hp A
  have h2 := T_gt_int hp A
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.prime.pos
  have r1 : (10 : ℝ) * p * A.T < 23 * (K n : ℝ) := by exact_mod_cast h1
  have r2 : (46 : ℝ) * (K n : ℝ) - 21 * p < 20 * p * A.T := by exact_mod_cast h2
  set y : ℝ := 2 * (Hcst : ℝ) * (((K n : ℕ) : ℝ) / (p : ℝ)) with hy
  have hy' : y * (p : ℝ) = 23 / 10 * (K n : ℝ) := by
    rw [hy]; simp only [Hcst]; push_cast; field_simp; ring
  have a1 : (A.T : ℝ) < y := by nlinarith
  have a2 : y < (A.T : ℝ) + 21 / 20 := by nlinarith
  unfold TR
  rw [← hy]
  rcases lt_or_ge y ((A.T : ℝ) + 1) with c | c
  · left
    have : ⌊y⌋ = A.T := Int.floor_eq_iff.2 ⟨a1.le, c⟩
    rw [this]
  · right
    have : ⌊y⌋ = A.T + 1 := Int.floor_eq_iff.2 ⟨by push_cast; linarith, by push_cast; linarith⟩
    rw [this]; push_cast; ring

lemma sub_min_eq (a b : ℝ) : a - min a b = max 0 (a - b) := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, max_eq_left (by linarith)]; ring
  · rw [min_eq_right h, max_eq_right (by linarith)]

/-- **The assembly of (5.7), first half, in abstract real variables.**  Both transition cases
`⌊2Hx⌋ = T` and `⌊2Hx⌋ = T + 1` are handled; in the second the identity
`I(T+1) = I(T) + T - x - 2` (`IT_succ`) is the paper's "allocating one extra row to every
ordinary class gives exactly the next base allocation". -/
lemma assembly (p m T E q U x Hx Z0 SF IT0 ITR TR s np γ Γ δ : ℝ)
    (hp : p = 2 * m + 1) (hp0 : 0 < p)
    (hγ : γ = Z0 + SF + (E * (2 * T - 4) - (E * q + min E U)))
    (hΓ : Γ = ITR + s * (2 * TR - q - 5) + max 0 (s - np))
    (hTR : TR = T ∨ TR = T + 1)
    (hITR : ITR = IT0 + (TR - T) * (T - x - 2))
    (hs : s = Hx - TR / 2) (hs0 : 0 ≤ s)
    (hnp : np = (2 * x - q) / 2) (hnp0 : 0 ≤ np) (hnp1 : np ≤ 1 / 2)
    (hδ : E - p * (Hx - T / 2) = δ) (hEm : E ≤ m - 1)
    (hU : |U - p * np| ≤ 1 / 2) :
    |γ - p * Γ| ≤ |Z0| + |SF - p * IT0| + |δ| * (|2 * T - q| + 9) + 1 := by
  have hpmax : p * max 0 (s - np) = max 0 (p * s - p * np) := by
    rw [mul_max_of_nonneg _ _ hp0.le, mul_zero, mul_sub]
  have hmaxnn : 0 ≤ max 0 (s - np) := le_max_left _ _
  have hmaxle : max 0 (s - np) ≤ s := max_le hs0 (by linarith)
  have hq5 : |2 * T - q - 5| ≤ |2 * T - q| + 5 := by
    refine le_trans (abs_sub _ _) ?_; norm_num
  have hq3 : |2 * T - q - 3| ≤ |2 * T - q| + 5 := by
    refine le_trans (abs_sub _ _) ?_; norm_num
  have hδa := abs_nonneg δ
  rcases hTR with h | h
  · -- `⌊2Hx⌋ = T`
    have hps : p * s = E - δ := by rw [hs, h]; linarith
    have hA := sub_min_eq E U
    have hB : p * max 0 (s - np) = max 0 (E - δ - p * np) := by rw [hpmax, hps]
    have hid : γ - p * Γ = Z0 + (SF - p * IT0) + δ * (2 * T - q - 5)
        + (max 0 (E - U) - max 0 (E - δ - p * np)) := by
      rw [hγ, hΓ, hITR, h]
      linear_combination hA - (2 * T - q - 5) * hps - hB
    have hW : |max 0 (E - U) - max 0 (E - δ - p * np)| ≤ |δ| + 1 / 2 := by
      have := abs_max_sub_max_le_abs (E - U) (E - δ - p * np) 0
      rw [max_comm (E - U), max_comm (E - δ - p * np)] at this
      refine le_trans this ?_
      have : E - U - (E - δ - p * np) = δ - (U - p * np) := by ring
      rw [this]
      refine le_trans (abs_sub _ _) ?_
      linarith
    have hprod : |δ * (2 * T - q - 5)| ≤ |δ| * (|2 * T - q| + 5) := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left hq5 hδa
    rw [hid]
    calc _ ≤ |Z0| + |SF - p * IT0| + |δ * (2 * T - q - 5)|
          + |max 0 (E - U) - max 0 (E - δ - p * np)| := by
          refine le_trans (abs_add_le _ _) ?_
          gcongr
          refine le_trans (abs_add_le _ _) ?_
          gcongr
          exact abs_add_le _ _
      _ ≤ _ := by linarith
  · -- `⌊2Hx⌋ = T + 1`: the transition
    have hps : p * s = E - δ - p / 2 := by rw [hs, h]; linarith
    have hps0 : 0 ≤ p * s := mul_nonneg hp0.le hs0
    have hpsδ : p * s ≤ |δ| := by
      have : p * s ≤ -δ - 3 / 2 := by rw [hps, hp]; linarith
      linarith [neg_abs_le δ]
    have hx : p * x = p * np + p * q / 2 := by rw [hnp]; ring
    have hid : γ - p * Γ = Z0 + (SF - p * IT0) + δ * (2 * T - q - 3) - δ
        + (p * np - min E U) - p * s - p * max 0 (s - np) := by
      rw [hγ, hΓ, hITR, h]
      linear_combination hx - (2 * T - q - 4) * hps
    have hmin1 : min E U - p * np ≤ 1 / 2 := by
      have := (abs_le.1 hU).2
      linarith [min_le_right E U]
    have hmin2 : -|δ| - 1 / 2 ≤ min E U - p * np := by
      have h1 : -|δ| - 1 / 2 + p * np ≤ E := by
        have : p * np ≤ p / 2 := by nlinarith
        linarith [neg_abs_le δ]
      have h2 : -|δ| - 1 / 2 + p * np ≤ U := by
        have := (abs_le.1 hU).1
        linarith
      have := le_min h1 h2
      linarith
    have hM1 : |p * np - min E U| ≤ |δ| + 1 / 2 := by
      rw [abs_le]; constructor <;> linarith
    have hM2 : |p * s| ≤ |δ| := by rw [abs_of_nonneg hps0]; exact hpsδ
    have hM3 : |p * max 0 (s - np)| ≤ |δ| := by
      rw [abs_of_nonneg (mul_nonneg hp0.le hmaxnn)]
      nlinarith
    have hprod : |δ * (2 * T - q - 3)| ≤ |δ| * (|2 * T - q| + 5) := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left hq3 hδa
    rw [hid]
    calc _ ≤ |Z0| + |SF - p * IT0| + |δ * (2 * T - q - 3)| + |δ| + |p * np - min E U|
          + |p * s| + |p * max 0 (s - np)| := by
          refine le_trans (abs_sub _ _) ?_
          gcongr
          refine le_trans (abs_sub _ _) ?_
          gcongr
          refine le_trans (abs_add_le _ _) ?_
          gcongr
          refine le_trans (abs_sub _ _) ?_
          gcongr
          refine le_trans (abs_add_le _ _) ?_
          gcongr
          exact abs_add_le _ _
      _ ≤ _ := by linarith

lemma qN_bounds (n p : ℕ) (hp0 : 0 < p) :
    2 * mFloor p (K n) ≤ qN n p ∧ qN n p ≤ 2 * mFloor p (K n) + 1 := by
  have hv : K n % p < p := Nat.mod_lt _ hp0
  have hdm : p * (K n / p) + K n % p = K n := Nat.div_add_mod _ _
  have hq : qN n p = 2 * (K n / p) + 2 * (K n % p) / p := by
    have h2K : 2 * K n = 2 * (K n % p) + p * (2 * (K n / p)) := by
      calc 2 * K n = 2 * (p * (K n / p) + K n % p) := by rw [hdm]
        _ = 2 * (K n % p) + p * (2 * (K n / p)) := by ring
    unfold qN
    rw [h2K, Nat.add_mul_div_left _ _ hp0]
    ring
  have h1 : 2 * (K n % p) / p ≤ 1 := by
    apply Nat.le_of_lt_succ
    rw [Nat.div_lt_iff_lt_mul hp0]
    omega
  unfold mFloor
  rw [hq]
  generalize 2 * (K n % p) / p = r at h1 ⊢
  omega

/-- `0 ≤ T ≤ 3M` at an inner prime. -/
lemma T_bounds {M n p : ℕ} (hp : IsInnerPrime n M p) (A : InnerAlloc n M p) :
    0 ≤ (A.T : ℝ) ∧ (A.T : ℝ) ≤ 3 * (M : ℝ) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.prime.pos
  have hlow : ((K n : ℕ) : ℝ) < (p : ℝ) * M := by exact_mod_cast hp.lower
  have hup : (3 : ℝ) * p ≤ ((K n : ℕ) : ℝ) := by exact_mod_cast hp.upper
  have rT1 : (10 : ℝ) * p * (A.T : ℝ) < 23 * ((K n : ℕ) : ℝ) := by exact_mod_cast T_lt_int hp A
  have rT2 : (46 : ℝ) * ((K n : ℕ) : ℝ) - 21 * p < 20 * p * (A.T : ℝ) := by
    exact_mod_cast T_gt_int hp A
  constructor
  · by_contra hneg
    push Not at hneg
    have : 20 * (p : ℝ) * (A.T : ℝ) < 0 := by
      have := mul_neg_of_pos_of_neg (show (0 : ℝ) < 20 * p by positivity) hneg
      linarith
    linarith
  · by_contra hbig
    push Not at hbig
    have : (p : ℝ) * (3 * M) < (p : ℝ) * (A.T : ℝ) := mul_lt_mul_of_pos_left hbig hp0
    nlinarith

lemma delta_bound (M : ℕ) (hM : 40 ≤ M) (T mN : ℝ) (hT0 : 0 ≤ T) (hT : T ≤ 3 * (M : ℝ))
    (hmN0 : 0 ≤ mN) (hmN : 40 * mN < 3 * M) :
    |T / 2 - ((L0 M : ℕ) : ℝ) - 3 * mN| ≤ 6 * M := by
  have hM' : (40 : ℝ) ≤ M := by exact_mod_cast hM
  have hL0 : ((L0 M : ℕ) : ℝ) = 4 * M + 10 := by unfold L0; push_cast; ring
  rw [hL0, abs_le]; constructor <;> linarith

lemma U_near {M n p : ℕ} (hp : IsInnerPrime n M p) :
    |((Top n p).card : ℝ) - (p : ℝ) * ((2 * (((K n : ℕ) : ℝ) / (p : ℝ)) - (qN n p : ℝ)) / 2)|
      ≤ 1 / 2 := by
  have hp0N : 0 < p := hp.prime.pos
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp0N
  have h2m := hp.two_mHalf
  have hpm : (p : ℝ) = 2 * (mHalf p : ℝ) + 1 := by
    have : ((2 * mHalf p + 1 : ℕ) : ℝ) = (p : ℝ) := by rw [h2m]
    rw [← this]; push_cast; ring
  obtain ⟨qb1, qb2⟩ := qN_bounds n p hp0N
  have qb1' : 2 * (mFloor p (K n) : ℝ) ≤ (qN n p : ℝ) := by exact_mod_cast qb1
  have qb2' : (qN n p : ℝ) ≤ 2 * (mFloor p (K n) : ℝ) + 1 := by exact_mod_cast qb2
  have hid : (p : ℝ) * ((2 * (((K n : ℕ) : ℝ) / (p : ℝ)) - (qN n p : ℝ)) / 2)
      = ((K n : ℕ) : ℝ) - (p : ℝ) * (qN n p : ℝ) / 2 := by field_simp
  rw [hid, U_eq hp, hpm, abs_le]
  constructor <;> linarith

lemma delta_eq {M n p : ℕ} (hp : IsInnerPrime n M p) (A : InnerAlloc n M p) :
    (A.E : ℝ) - (p : ℝ) * ((Hcst : ℝ) * (((K n : ℕ) : ℝ) / (p : ℝ)) - (A.T : ℝ) / 2)
      = (A.T : ℝ) / 2 - ((L0 M : ℕ) : ℝ) - 3 * (mFloor p (N n) : ℝ) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.prime.pos
  have h2m := hp.two_mHalf
  have hpm : (p : ℝ) = 2 * (mHalf p : ℝ) + 1 := by
    have : ((2 * mHalf p + 1 : ℕ) : ℝ) = (p : ℝ) := by rw [h2m]
    rw [← this]; push_cast; ring
  have hTEr : (mHalf p : ℝ) * (A.T : ℝ) + (A.E : ℝ)
      = (h n : ℝ) - (L0 M : ℝ) + 3 * ((N n : ℝ) - (mFloor p (N n) : ℝ)) := by
    exact_mod_cast A.hTE
  have hHx : (p : ℝ) * ((Hcst : ℝ) * (((K n : ℕ) : ℝ) / (p : ℝ))) = (h n : ℝ) + 3 * (N n : ℝ) := by
    simp only [Hcst, h, N, K]; push_cast; field_simp; ring
  rw [mul_sub, hHx]
  rw [hpm]
  linarith

lemma gamma_eq {M n p : ℕ} (hp : IsInnerPrime n M p) (A : InnerAlloc n M p) :
    (A.gammaIn : ℝ) = (Z0 A : ℝ) + ∑ a ∈ Icc 1 (mHalf p), FT n p (A.T : ℝ) a
      + ((A.E : ℝ) * (2 * (A.T : ℝ) - 4)
        - ((A.E : ℝ) * (qN n p : ℝ) + min (A.E : ℝ) ((Top n p).card : ℝ))) := by
  have hepsE : ∑ a ∈ Icc 1 (mHalf p), (A.eps a : ℝ) = (A.E : ℝ) := by
    exact_mod_cast congrArg (fun k : ℕ => (k : ℝ)) A.hEpsSum
  rw [gammaIn_expand hp A, Finset.sum_add_distrib, ← eps_ell_sum hp A, ← hepsE,
    Finset.sum_mul, ← Finset.sum_sub_distrib]
  have : ∀ a ∈ Icc 1 (mHalf p), (A.eps a : ℝ) * (2 * (A.T : ℝ) - (ell p (K n) a : ℝ) - 4)
      = (A.eps a : ℝ) * (2 * (A.T : ℝ) - 4) - (A.eps a : ℝ) * (ell p (K n) a : ℝ) :=
    fun a _ => by ring
  rw [Finset.sum_congr rfl this]
  ring

lemma qR_eq (n p : ℕ) : qR (((K n : ℕ) : ℝ) / (p : ℝ)) = (qN n p : ℝ) := by
  unfold qR
  have : 2 * (((K n : ℕ) : ℝ) / (p : ℝ)) = ((2 * K n : ℕ) : ℝ) / (p : ℝ) := by push_cast; ring
  rw [this, floor_natDiv]; rfl

/-- **First half of (5.7)**: `|γ_p^in - pΓ(K/p)| ≤ 400 M²` at every inner prime, for every
allocation satisfying (4.4).  (Measured: `≤ 3.8 M`.) -/
theorem gamma_inner_bound (M : ℕ) (hM : 40 ≤ M) (n p : ℕ) (hp : IsInnerPrime n M p)
    (A : InnerAlloc n M p) :
    |(A.gammaIn : ℝ) - (p : ℝ) * Gam (((K n : ℕ) : ℝ) / (p : ℝ))| ≤ 400 * (M : ℝ) ^ 2 := by
  have hM' : (40 : ℝ) ≤ M := by exact_mod_cast hM
  have h2m := hp.two_mHalf
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.prime.pos
  have hpm : (p : ℝ) = 2 * (mHalf p : ℝ) + 1 := by
    have : ((2 * mHalf p + 1 : ℕ) : ℝ) = (p : ℝ) := by rw [h2m]
    rw [← this]; push_cast; ring
  obtain ⟨hT0, hT3⟩ := T_bounds hp A
  set x : ℝ := ((K n : ℕ) : ℝ) / (p : ℝ) with hx
  have hq := qR_eq n p
  have hq1 : (qN n p : ℝ) ≤ 2 * x := by
    rw [← hq]; unfold qR; exact Int.floor_le _
  have hq2 : 2 * x < (qN n p : ℝ) + 1 := by
    rw [← hq]; unfold qR; exact Int.lt_floor_add_one _
  have hlow : ((K n : ℕ) : ℝ) < (p : ℝ) * M := by exact_mod_cast hp.lower
  have hxM : x < M := by rw [hx, div_lt_iff₀ hp0]; linarith
  have hq0 : (0 : ℝ) ≤ (qN n p : ℝ) := by positivity
  have hqb : |2 * (A.T : ℝ) - (qN n p : ℝ)| ≤ 7 * M := by
    rw [abs_le]; constructor <;> linarith
  obtain ⟨_, _, hmN, _⟩ := inner_facts hp
  have hmN' : 40 * (mFloor p (N n) : ℝ) < 3 * M := by exact_mod_cast hmN
  have hδb := delta_bound M hM (A.T : ℝ) (mFloor p (N n) : ℝ) hT0 hT3 (by positivity) hmN'
  have hEm : (A.E : ℝ) ≤ (mHalf p : ℝ) - 1 := by
    have := A.hE
    have : (A.E : ℝ) + 1 ≤ (mHalf p : ℝ) := by exact_mod_cast this
    linarith
  have hΓ := Gam_split x
  rw [hq] at hΓ
  have hITR : IT x (TR x) = IT x (A.T : ℝ) + (TR x - (A.T : ℝ)) * ((A.T : ℝ) - x - 2) := by
    rcases T_cases hp A with h | h
    · rw [h]; ring
    · rw [h]; have := IT_succ x (A.T : ℝ); linarith
  have hs0 : 0 ≤ sR x := by
    unfold sR TR
    have := Int.floor_le (2 * (Hcst : ℝ) * x)
    linarith
  have hnp : nPlus x = (2 * x - (qN n p : ℝ)) / 2 := by unfold nPlus; rw [hq]
  have hnp0 : 0 ≤ nPlus x := by rw [hnp]; linarith
  have hnp1 : nPlus x ≤ 1 / 2 := by rw [hnp]; linarith
  have hU := U_near hp
  rw [← hx, ← hnp] at hU
  have key := assembly (p : ℝ) (mHalf p : ℝ) (A.T : ℝ) (A.E : ℝ) (qN n p : ℝ)
    ((Top n p).card : ℝ) x ((Hcst : ℝ) * x) (Z0 A : ℝ)
    (∑ a ∈ Icc 1 (mHalf p), FT n p (A.T : ℝ) a) (IT x (A.T : ℝ)) (IT x (TR x)) (TR x)
    (sR x) (nPlus x) (A.gammaIn : ℝ) (Gam x) _ hpm hp0 (gamma_eq hp A) hΓ (T_cases hp A) hITR
    rfl hs0 hnp hnp0 hnp1 (delta_eq hp A) hEm hU
  have hZ := Z0_bound M hM hp A
  have hR := riemann M n p hM hp (A.T : ℝ) hT0 hT3
  have hprod : |(A.T : ℝ) / 2 - ((L0 M : ℕ) : ℝ) - 3 * (mFloor p (N n) : ℝ)|
      * (|2 * (A.T : ℝ) - (qN n p : ℝ)| + 9) ≤ 6 * M * (7 * M + 9) :=
    mul_le_mul hδb (by linarith) (by positivity) (by positivity)
  have hfin : 80 * (M : ℝ) ^ 2 + 250 * (M : ℝ) ^ 2 + 6 * M * (7 * M + 9) + 1
      ≤ 400 * (M : ℝ) ^ 2 := by nlinarith
  linarith

/-! ## §6.  The three conjuncts together: `Zeta5.PrimeSum.eq_5_7_uniformity` -/

/-- **(5.7) and the two displays of §5.2, with `C = 400 M²`.**  The statement is literally
that of `Zeta5.PrimeSum.eq_5_7_uniformity`. -/
theorem eq_5_7_uniformity (M : ℕ) (hM : 40 ≤ M) (Alloc : ∀ n, InnerAllocFamily n M) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ (n p : ℕ) (hp : IsInnerPrime n M p),
          |(((Alloc n) p hp).gammaIn : ℝ) - (p : ℝ) * Gam (((K n : ℕ) : ℝ) / (p : ℝ))| ≤ C)
      ∧ (∀ (n p : ℕ), IsInnerPrime n M p →
          |((vS n p : ℤ) : ℝ) - (p : ℝ) * NR (((K n : ℕ) : ℝ) / (p : ℝ))| ≤ C)
      ∧ (∀ (n p : ℕ), 0 < n → p.Prime → K n < 3 * p → p ≤ 2 * h n →
          |(-(((vS n p : ℤ) : ℝ) + ((gammaOut n p : ℤ) : ℝ)))
              - ((K n : ℕ) : ℝ) * AppendixB.Tout ((p : ℝ) / ((K n : ℕ) : ℝ))| ≤ C) := by
  have hM' : (40 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  refine ⟨400 * (M : ℝ) ^ 2, by positivity, ?_, ?_, ?_⟩
  · intro n p hp
    exact gamma_inner_bound M hM n p hp _
  · intro n p hp
    refine le_trans (vS_inner_bound M hM n p hp) ?_
    nlinarith
  · intro n p hn hp h3 h2
    refine le_trans (outer_bound n p hn hp h3 h2) ?_
    nlinarith

end

end Uniformity
end Zeta5

#print axioms Zeta5.Uniformity.eq_5_7_uniformity
#print axioms Zeta5.Uniformity.gamma_inner_bound
#print axioms Zeta5.Uniformity.vS_inner_bound
#print axioms Zeta5.Uniformity.outer_bound
