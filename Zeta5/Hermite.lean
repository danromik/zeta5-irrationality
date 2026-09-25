/-
Zeta5/Hermite.lean

**Hermite's pole integral at `s = 5`, proved outright (no axiom).**  (Used by
`Zeta5.Positivity`, i.e. by Proposition 2.2.)

`Zeta5.Hermite.pole_integral` has exactly the type of the former axiom
`Zeta5.Axioms.hermite_pole_integral` (removed 2026-09-24), the display in the middle of p. 5
of the paper:

  `∫_0^∞ w(y)/(y²+a²) dy = a⁴ ζ(5,a) − 1/(2a) − 1/4`   (`a > 0`).

This file imports only Mathlib and `Zeta5.Basic`.  The route avoids Hermite's formula and the
four integrations by parts of p. 5 altogether.  With `b_l = 2π(l+1)`:

1. (Tonelli) `∫ w/(y²+a²) = ∑_l ∫ T_l`, `T_l(y) = b_l⁴ y⁵ e^{-b_l y}/(12(y²+a²))`.
2. (substitution `u = b_l y / a`) `∫ T_l = ∫ R_l`, `R_l(u) = (a⁴/12) u⁵e^{-au}/(u²+b_l²)`.
3. (Tonelli + Mittag-Leffler for `coth`, from Mathlib's `cot_series_rep'` at `x = iu/2π`)
   `∑_l ∫ R_l = (a⁴/24) ∫ u⁴e^{-au} (1/(e^u−1) − 1/u + 1/2) du`.
4. (geometric series + Tonelli + `∫u^m e^{-cu} = m!/c^{m+1}`) the last integral is
   `24 ∑_{k≥0}(k+1+a)^{-5} − 6/a⁴ + 12/a⁵`, which rearranges to the right side.

Every sum–integral interchange is Tonelli for nonnegative terms
(`integral_tsum_of_summable_integral_norm`), with the summable majorant
`∫ R_l ≤ 10/(a²(2π)²(l+1)²)`.  Numerical control: `numerics/axioms/hermite_full_chain.py`.
-/
import Mathlib
import Zeta5.Basic

namespace Zeta5
namespace Hermite

open MeasureTheory Set Real

lemma ml_summable (u : ℝ) (hu : 0 ≤ u) :
    Summable (fun n : ℕ => 2 * u / (u ^ 2 + (2 * π * ((n : ℝ) + 1)) ^ 2)) := by
  have hpi : (0 : ℝ) < 2 * π := by have := Real.pi_pos; positivity
  have hs : Summable (fun n : ℕ => (2 * u / (2 * π) ^ 2) * (1 / ((n : ℝ) + 1) ^ 2)) := by
    have h := Real.summable_one_div_nat_pow.mpr (show 1 < 2 by norm_num)
    have h1 : Summable (fun l : ℕ => 1 / (((l + 1 : ℕ) : ℝ)) ^ 2) := (summable_nat_add_iff 1).2 h
    refine (h1.congr fun l => ?_).mul_left _
    push_cast; ring
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hs
  have hb : 0 < (2 * π * ((n : ℝ) + 1)) ^ 2 := by positivity
  calc 2 * u / (u ^ 2 + (2 * π * ((n : ℝ) + 1)) ^ 2)
      ≤ 2 * u / (2 * π * ((n : ℝ) + 1)) ^ 2 :=
        div_le_div_of_nonneg_left (by positivity) hb (by nlinarith)
    _ = (2 * u / (2 * π) ^ 2) * (1 / ((n : ℝ) + 1) ^ 2) := by
        field_simp

open Complex in
lemma ml_tsum (u : ℝ) (hu : 0 < u) :
    ∑' n : ℕ, 2 * u / (u ^ 2 + (2 * π * ((n : ℝ) + 1)) ^ 2)
      = 1 / (Real.exp u - 1) - 1 / u + 1 / 2 := by
  have hpi : (0 : ℝ) < π := Real.pi_pos
  set x : ℂ := I * ((u / (2 * π) : ℝ) : ℂ) with hxdef
  have hxim : x.im = u / (2 * π) := by
    simp only [x, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hxim_ne : x.im ≠ 0 := by rw [hxim]; positivity
  have hx : x ∈ Complex.integerComplement := by
    rintro ⟨n, hn⟩
    apply hxim_ne
    rw [← hn]; simp
  have h := cot_series_rep' hx
  have hterm : ∀ n : ℕ, 1 / (x - (n + 1)) + 1 / (x + (n + 1))
      = (-2 * π * I) * (((2 * u / (u ^ 2 + (2 * π * ((n : ℝ) + 1)) ^ 2)) : ℝ) : ℂ) := by
    intro n
    have h1 : x - (n + 1) ≠ 0 := by
      intro h0; apply hxim_ne; have := congrArg Complex.im h0; simpa using this
    have h2 : x + (n + 1) ≠ 0 := by
      intro h0; apply hxim_ne; have := congrArg Complex.im h0; simpa using this
    have h3 : ((u ^ 2 + (2 * π * ((n : ℝ) + 1)) ^ 2 : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (show (u ^ 2 + (2 * π * ((n : ℝ) + 1)) ^ 2 : ℝ) ≠ 0 by positivity)
    have hpi' : ((π : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpi.ne'
    push_cast at h3
    have hprod : (x - (n + 1)) * (x + (n + 1))
        = -((u : ℂ) ^ 2 + (2 * (π : ℂ) * ((n : ℂ) + 1)) ^ 2) / (4 * (π : ℂ) ^ 2) := by
      simp only [x]
      push_cast
      field_simp
      ring_nf
      rw [I_sq]
      ring
    rw [div_add_div _ _ h1 h2, hprod]
    simp only [x]
    push_cast
    field_simp
    ring_nf
  have hsum := ml_summable u hu.le
  rw [tsum_congr hterm, tsum_mul_left, ← Complex.ofReal_tsum] at h
  have hE : 1 < Real.exp u := Real.one_lt_exp_iff.mpr hu
  have hcot : (π : ℂ) * Complex.cot ((π : ℂ) * x) - 1 / x
      = (-2 * π * I) * (((1 / (Real.exp u - 1) - 1 / u + 1 / 2 : ℝ)) : ℂ) := by
    rw [Complex.cot_eq_exp_ratio]
    have h2 : 2 * I * ((π : ℂ) * x) = ((-u : ℝ) : ℂ) := by
      simp only [x]
      push_cast
      field_simp
      ring_nf
      rw [I_sq]
      ring
    rw [h2, ← Complex.ofReal_exp, Real.exp_neg]
    have hE1 : ((Real.exp u : ℝ) : ℂ) - 1 ≠ 0 := by
      exact_mod_cast (show Real.exp u - 1 ≠ 0 by linarith)
    have hE0 : ((Real.exp u : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.exp_pos u).ne'
    have hu0 : (u : ℂ) ≠ 0 := by exact_mod_cast hu.ne'
    have hpi' : ((π : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpi.ne'
    simp only [x]
    push_cast
    field_simp
    ring_nf
    rw [I_sq]
    have hE2 : (-1 + Complex.exp (u : ℂ)) ≠ 0 := by
      rw [← Complex.ofReal_exp]; intro h0; apply hE1; rw [← h0]; ring
    field_simp
    ring
  rw [hcot] at h
  have hne : (-2 * (π : ℂ) * I) ≠ 0 := by
    have hpi' : ((π : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpi.ne'
    simp [hpi', I_ne_zero]
  exact_mod_cast (mul_left_cancel₀ hne h).symm


/-! ## Generic tools -/

lemma integrableOn_pow_mul_exp (m : ℕ) {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun y : ℝ => y ^ m * Real.exp (-(c * y))) (Ioi 0) := by
  have hm : (-1 : ℝ) < (m : ℝ) := lt_of_lt_of_le neg_one_lt_zero (Nat.cast_nonneg m)
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := (m : ℝ)) (b := c)
    hm one_pos hc
  refine h.congr_fun (fun y hy => ?_) measurableSet_Ioi
  have h1 : (y : ℝ) ^ ((m : ℕ) : ℝ) = y ^ m := Real.rpow_natCast y m
  have h2 : (y : ℝ) ^ (1 : ℝ) = y := Real.rpow_one y
  simp only [h1, h2, neg_mul]

lemma integral_pow_mul_exp (m : ℕ) {c : ℝ} (hc : 0 < c) :
    ∫ y in Ioi (0 : ℝ), y ^ m * Real.exp (-(c * y))
      = (Nat.factorial m : ℝ) / c ^ (m + 1) := by
  have hpos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have key := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (m : ℝ) + 1) (r := c) hpos hc
  have hlhs : ∫ y in Ioi (0 : ℝ), y ^ ((m : ℝ) + 1 - 1) * Real.exp (-(c * y))
      = ∫ y in Ioi (0 : ℝ), y ^ m * Real.exp (-(c * y)) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun y hy => ?_)
    have : ((m : ℝ) + 1 - 1) = (m : ℝ) := by ring
    rw [this, Real.rpow_natCast]
  rw [hlhs] at key
  rw [key, Real.Gamma_nat_eq_factorial]
  have hcast : (m : ℝ) + 1 = ((m + 1 : ℕ) : ℝ) := by push_cast; ring
  rw [hcast, Real.rpow_natCast]
  rw [div_pow, one_pow]
  field_simp

lemma integrableOn_of_le {f g : ℝ → ℝ} (hg : IntegrableOn g (Ioi 0))
    (hf : ContinuousOn f (Ioi 0)) (h0 : ∀ y, 0 < y → 0 ≤ f y)
    (h : ∀ y, 0 < y → f y ≤ g y) : IntegrableOn f (Ioi 0) :=
  Integrable.mono' hg (hf.aestronglyMeasurable measurableSet_Ioi)
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun y hy => by
      rw [Real.norm_of_nonneg (h0 y hy)]; exact h y hy))

/-- Tonelli for a series of nonnegative integrable functions on `(0,∞)`. -/
lemma integral_tsum_of_nonneg {F : ℕ → ℝ → ℝ} (hint : ∀ n, IntegrableOn (F n) (Ioi 0))
    (hnn : ∀ n y, 0 < y → 0 ≤ F n y)
    (hsum : Summable fun n => ∫ y in Ioi (0 : ℝ), F n y) :
    ∫ y in Ioi (0 : ℝ), ∑' n, F n y = ∑' n, ∫ y in Ioi (0 : ℝ), F n y := by
  refine (integral_tsum_of_summable_integral_norm hint (hsum.congr fun n => ?_)).symm
  refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
  exact (Real.norm_of_nonneg (hnn n y hy)).symm

lemma summable_inv_succ_sq : Summable (fun l : ℕ => 1 / ((l : ℝ) + 1) ^ 2) := by
  have h := Real.summable_one_div_nat_pow.mpr (show 1 < 2 by norm_num)
  have h1 : Summable (fun l : ℕ => 1 / (((l + 1 : ℕ) : ℝ)) ^ 2) := (summable_nat_add_iff 1).2 h
  exact h1.congr fun l => by push_cast; ring

/-! ## The `u`-side terms `R_l` -/

variable {a : ℝ}

/-- `R_l(u) = (a⁴/12) u⁵ e^{-au}/(u² + (2π(l+1))²)`. -/
noncomputable def RR (a : ℝ) (l : ℕ) (u : ℝ) : ℝ :=
  a ^ 4 / 12 * (u ^ 5 * Real.exp (-(a * u)) / (u ^ 2 + (2 * π * ((l : ℝ) + 1)) ^ 2))

lemma RR_nonneg (ha : 0 < a) (l : ℕ) {u : ℝ} (hu : 0 < u) : 0 ≤ RR a l u := by
  unfold RR; positivity

lemma RR_le (ha : 0 < a) (l : ℕ) {u : ℝ} (hu : 0 < u) :
    RR a l u ≤ a ^ 4 / 12 / (2 * π * ((l : ℝ) + 1)) ^ 2 * (u ^ 5 * Real.exp (-(a * u))) := by
  have hb : 0 < (2 * π * ((l : ℝ) + 1)) ^ 2 := by have := Real.pi_pos; positivity
  unfold RR
  have h1 : u ^ 5 * Real.exp (-(a * u)) / (u ^ 2 + (2 * π * ((l : ℝ) + 1)) ^ 2)
      ≤ u ^ 5 * Real.exp (-(a * u)) / (2 * π * ((l : ℝ) + 1)) ^ 2 :=
    div_le_div_of_nonneg_left (by positivity) hb (by nlinarith)
  calc a ^ 4 / 12 * (u ^ 5 * Real.exp (-(a * u)) / (u ^ 2 + (2 * π * ((l : ℝ) + 1)) ^ 2))
      ≤ a ^ 4 / 12 * (u ^ 5 * Real.exp (-(a * u)) / (2 * π * ((l : ℝ) + 1)) ^ 2) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = _ := by ring

lemma RR_integrable (ha : 0 < a) (l : ℕ) : IntegrableOn (RR a l) (Ioi (0 : ℝ)) := by
  refine integrableOn_of_le ((integrableOn_pow_mul_exp 5 ha).const_mul _) ?_
    (fun u hu => RR_nonneg ha l hu) (fun u hu => RR_le ha l hu)
  have hb : ∀ u : ℝ, u ^ 2 + (2 * π * ((l : ℝ) + 1)) ^ 2 ≠ 0 := fun u => by
    have := Real.pi_pos; positivity
  unfold RR
  exact (Continuous.continuousOn (by fun_prop (disch := exact hb _)))

lemma RR_summable (ha : 0 < a) : Summable (fun l => ∫ u in Ioi (0 : ℝ), RR a l u) := by
  have hpi : (0 : ℝ) < 2 * π := by have := Real.pi_pos; positivity
  refine Summable.of_nonneg_of_le
    (fun l => setIntegral_nonneg measurableSet_Ioi (fun u hu => RR_nonneg ha l hu))
    (fun l => setIntegral_mono_on (RR_integrable ha l)
      ((integrableOn_pow_mul_exp 5 ha).const_mul _) measurableSet_Ioi
      (fun u hu => RR_le ha l hu))
    ((summable_inv_succ_sq.mul_left (10 / (a ^ 2 * (2 * π) ^ 2))).congr fun l => ?_)
  rw [integral_const_mul, integral_pow_mul_exp 5 ha]
  have hl : (0 : ℝ) < (l : ℝ) + 1 := by positivity
  norm_num [Nat.factorial]
  field_simp
  ring


/-! ## The `y`-side terms `T_l` -/

/-- `T_l(y) = (2π)⁴/12 · (l+1)⁴ y⁵ e^{-2π(l+1)y}/(y² + a²)`, the `l`-th term of `w(y)/(y²+a²)`. -/
noncomputable def TT (a : ℝ) (l : ℕ) (y : ℝ) : ℝ :=
  (2 * π) ^ 4 / 12 * (((l : ℝ) + 1) ^ 4 *
    (y ^ 5 * Real.exp (-(2 * π * ((l : ℝ) + 1) * y)) / (y ^ 2 + a ^ 2)))

lemma TT_nonneg (ha : 0 < a) (l : ℕ) {y : ℝ} (hy : 0 < y) : 0 ≤ TT a l y := by
  unfold TT; have := Real.pi_pos; positivity

lemma TT_le (ha : 0 < a) (l : ℕ) {y : ℝ} (hy : 0 < y) :
    TT a l y ≤ (2 * π) ^ 4 / 12 * ((l : ℝ) + 1) ^ 4 / a ^ 2 *
      (y ^ 5 * Real.exp (-((2 * π * ((l : ℝ) + 1)) * y))) := by
  have hpi := Real.pi_pos
  unfold TT
  have h1 : y ^ 5 * Real.exp (-(2 * π * ((l : ℝ) + 1) * y)) / (y ^ 2 + a ^ 2)
      ≤ y ^ 5 * Real.exp (-(2 * π * ((l : ℝ) + 1) * y)) / a ^ 2 :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith)
  calc (2 * π) ^ 4 / 12 * (((l : ℝ) + 1) ^ 4 *
        (y ^ 5 * Real.exp (-(2 * π * ((l : ℝ) + 1) * y)) / (y ^ 2 + a ^ 2)))
      ≤ (2 * π) ^ 4 / 12 * (((l : ℝ) + 1) ^ 4 *
        (y ^ 5 * Real.exp (-(2 * π * ((l : ℝ) + 1) * y)) / a ^ 2)) := by
        gcongr
    _ = _ := by ring

lemma TT_integrable (ha : 0 < a) (l : ℕ) : IntegrableOn (TT a l) (Ioi (0 : ℝ)) := by
  have hb : 0 < 2 * π * ((l : ℝ) + 1) := by have := Real.pi_pos; positivity
  refine integrableOn_of_le ((integrableOn_pow_mul_exp 5 hb).const_mul _) ?_
    (fun y hy => TT_nonneg ha l hy) (fun y hy => TT_le ha l hy)
  have hd : ∀ y : ℝ, y ^ 2 + a ^ 2 ≠ 0 := fun y => by positivity
  unfold TT
  exact (Continuous.continuousOn (by fun_prop (disch := exact hd _)))

/-- The substitution `u = 2π(l+1)y/a`: `∫ T_l = ∫ R_l`. -/
lemma integral_TT_eq (ha : 0 < a) (l : ℕ) :
    ∫ y in Ioi (0 : ℝ), TT a l y = ∫ u in Ioi (0 : ℝ), RR a l u := by
  have hpi := Real.pi_pos
  have hb : 0 < 2 * π * ((l : ℝ) + 1) := by positivity
  have hc : 0 < 2 * π * ((l : ℝ) + 1) / a := by positivity
  have hsub := integral_comp_mul_left_Ioi (RR a l) 0 hc
  rw [mul_zero, smul_eq_mul] at hsub
  have hpt : ∀ y : ℝ, TT a l y
      = (2 * π * ((l : ℝ) + 1) / a) * RR a l ((2 * π * ((l : ℝ) + 1) / a) * y) := by
    intro y
    unfold TT RR
    have hac : a * ((2 * π * ((l : ℝ) + 1) / a) * y) = 2 * π * ((l : ℝ) + 1) * y := by
      field_simp
    rw [hac]
    have hd : y ^ 2 + a ^ 2 ≠ 0 := by positivity
    have hd2 : ((2 * π * ((l : ℝ) + 1) / a) * y) ^ 2 + (2 * π * ((l : ℝ) + 1)) ^ 2 ≠ 0 := by
      positivity
    field_simp
  simp_rw [hpt]
  rw [integral_const_mul, hsub]
  field_simp

lemma TT_summable (ha : 0 < a) : Summable (fun l => ∫ y in Ioi (0 : ℝ), TT a l y) :=
  (RR_summable ha).congr fun l => (integral_TT_eq ha l).symm

lemma wt_div_eq_tsum (a y : ℝ) : wt y / (y ^ 2 + a ^ 2) = ∑' l : ℕ, TT a l y := by
  unfold wt TT
  rw [← tsum_mul_left, ← tsum_div_const]
  refine tsum_congr fun l => ?_
  ring

/-- **Left side**: `∫ w(y)/(y²+a²) dy = ∑_l ∫ R_l`. -/
lemma lhs_eq (ha : 0 < a) :
    ∫ y in Ioi (0 : ℝ), wt y / (y ^ 2 + a ^ 2) = ∑' l : ℕ, ∫ u in Ioi (0 : ℝ), RR a l u := by
  simp_rw [wt_div_eq_tsum a]
  rw [integral_tsum_of_nonneg (TT_integrable ha) (fun l y hy => TT_nonneg ha l hy)
    (TT_summable ha)]
  exact tsum_congr fun l => integral_TT_eq ha l


/-! ## Summing the `R_l` under the integral: the Mittag-Leffler step -/

lemma RR_tsum (a : ℝ) {u : ℝ} (hu : 0 < u) :
    ∑' l : ℕ, RR a l u
      = a ^ 4 / 24 * (u ^ 4 * Real.exp (-(a * u)) * (1 / (Real.exp u - 1) - 1 / u + 1 / 2)) := by
  have h : ∀ l : ℕ, RR a l u = (a ^ 4 / 24 * (u ^ 4 * Real.exp (-(a * u))))
      * (2 * u / (u ^ 2 + (2 * π * ((l : ℝ) + 1)) ^ 2)) := by
    intro l; unfold RR; ring
  rw [tsum_congr h, tsum_mul_left, ml_tsum u hu]
  ring

lemma sum_integral_RR (ha : 0 < a) :
    ∑' l : ℕ, ∫ u in Ioi (0 : ℝ), RR a l u
      = ∫ u in Ioi (0 : ℝ),
          a ^ 4 / 24 * (u ^ 4 * Real.exp (-(a * u)) * (1 / (Real.exp u - 1) - 1 / u + 1 / 2)) := by
  rw [← integral_tsum_of_nonneg (RR_integrable ha) (fun l u hu => RR_nonneg ha l hu)
    (RR_summable ha)]
  exact setIntegral_congr_fun measurableSet_Ioi fun u hu => RR_tsum a hu

/-! ## The Hurwitz side: `∫ u⁴e^{-au}/(e^u−1) du = 24 ∑_{k≥0} (k+1+a)^{-5}` -/

lemma summable_inv_succ_pow {p : ℕ} (hp : 1 < p) :
    Summable (fun l : ℕ => 1 / ((l : ℝ) + 1) ^ p) := by
  have h := Real.summable_one_div_nat_pow.mpr hp
  have h1 : Summable (fun l : ℕ => 1 / (((l + 1 : ℕ) : ℝ)) ^ p) := (summable_nat_add_iff 1).2 h
  exact h1.congr fun l => by push_cast; ring

lemma summable_hurwitz_tail (ha : 0 < a) :
    Summable (fun k : ℕ => 1 / ((k : ℝ) + 1 + a) ^ 5) := by
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
    (summable_inv_succ_pow (p := 5) (by norm_num))
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hk.le (by linarith) 5)

/-- `Q(u) = u⁴e^{-au}/(e^u − 1)`. -/
noncomputable def QQ (a : ℝ) (u : ℝ) : ℝ := u ^ 4 * Real.exp (-(a * u)) / (Real.exp u - 1)

lemma QQ_eq_tsum (a : ℝ) {u : ℝ} (hu : 0 < u) :
    QQ a u = ∑' k : ℕ, u ^ 4 * Real.exp (-(((k : ℝ) + 1 + a) * u)) := by
  have hr0 : 0 ≤ Real.exp (-u) := (Real.exp_pos _).le
  have hr1 : Real.exp (-u) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hg := (hasSum_geometric_of_lt_one hr0 hr1).mul_left (u ^ 4 * Real.exp (-(a * u)) * Real.exp (-u))
  have hterm : ∀ k : ℕ, u ^ 4 * Real.exp (-(((k : ℝ) + 1 + a) * u))
      = u ^ 4 * Real.exp (-(a * u)) * Real.exp (-u) * Real.exp (-u) ^ k := by
    intro k
    rw [← Real.exp_nat_mul, mul_assoc, mul_assoc, ← Real.exp_add, ← Real.exp_add]
    congr 2; ring
  rw [tsum_congr hterm, hg.tsum_eq]
  unfold QQ
  have hE : 1 < Real.exp u := Real.one_lt_exp_iff.mpr hu
  have hE1 : Real.exp u - 1 ≠ 0 := by linarith
  have hE2 : 1 - (Real.exp u)⁻¹ ≠ 0 := by
    have : (Real.exp u)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hE
    linarith
  rw [Real.exp_neg u]
  field_simp

lemma QQ_nonneg (_ha : 0 < a) {u : ℝ} (hu : 0 < u) : 0 ≤ QQ a u := by
  have hE : 1 < Real.exp u := Real.one_lt_exp_iff.mpr hu
  unfold QQ
  exact div_nonneg (by positivity) (by linarith)

lemma QQ_le (_ha : 0 < a) {u : ℝ} (hu : 0 < u) : QQ a u ≤ u ^ 3 * Real.exp (-(a * u)) := by
  have hE : u ≤ Real.exp u - 1 := by linarith [Real.add_one_le_exp u]
  unfold QQ
  rw [div_le_iff₀ (by linarith)]
  have h0 : 0 ≤ u ^ 3 * Real.exp (-(a * u)) := by positivity
  calc u ^ 4 * Real.exp (-(a * u)) = u ^ 3 * Real.exp (-(a * u)) * u := by ring
    _ ≤ u ^ 3 * Real.exp (-(a * u)) * (Real.exp u - 1) := mul_le_mul_of_nonneg_left hE h0

lemma QQ_integrable (ha : 0 < a) : IntegrableOn (QQ a) (Ioi (0 : ℝ)) := by
  refine integrableOn_of_le (integrableOn_pow_mul_exp 3 ha) ?_
    (fun u hu => QQ_nonneg ha hu) (fun u hu => QQ_le ha hu)
  have hd : ∀ u ∈ Ioi (0 : ℝ), Real.exp u - 1 ≠ 0 := fun u hu => by
    have := Real.one_lt_exp_iff.mpr (show 0 < u from hu); linarith
  unfold QQ
  exact ContinuousOn.div (by fun_prop) (by fun_prop) hd

lemma integral_QQ (ha : 0 < a) :
    ∫ u in Ioi (0 : ℝ), QQ a u = 24 * ∑' k : ℕ, 1 / ((k : ℝ) + 1 + a) ^ 5 := by
  have hc : ∀ k : ℕ, 0 < (k : ℝ) + 1 + a := fun k => by positivity
  have hint : ∀ k : ℕ, ∫ u in Ioi (0 : ℝ), u ^ 4 * Real.exp (-(((k : ℝ) + 1 + a) * u))
      = 24 * (1 / ((k : ℝ) + 1 + a) ^ 5) := by
    intro k
    rw [integral_pow_mul_exp 4 (hc k)]
    norm_num [Nat.factorial]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi (fun u hu => QQ_eq_tsum a hu)]
  rw [integral_tsum_of_nonneg (fun k => integrableOn_pow_mul_exp 4 (hc k))
    (fun k u hu => by positivity)
    (by simp_rw [hint]; exact (summable_hurwitz_tail ha).mul_left 24)]
  rw [tsum_congr hint, tsum_mul_left]

/-! ## The Laplace-transform form of the right side -/

lemma laplace_rhs (ha : 0 < a) :
    ∫ u in Ioi (0 : ℝ),
        a ^ 4 / 24 * (u ^ 4 * Real.exp (-(a * u)) * (1 / (Real.exp u - 1) - 1 / u + 1 / 2))
      = a ^ 4 * (∑' k : ℕ, 1 / ((k : ℝ) + a) ^ 5) - 1 / (2 * a) - 1 / 4 := by
  have hpt : ∀ u ∈ Ioi (0 : ℝ),
      a ^ 4 / 24 * (u ^ 4 * Real.exp (-(a * u)) * (1 / (Real.exp u - 1) - 1 / u + 1 / 2))
      = a ^ 4 / 24 * ((QQ a u - u ^ 3 * Real.exp (-(a * u)))
          + 1 / 2 * (u ^ 4 * Real.exp (-(a * u)))) := by
    intro u hu
    have hu0 : u ≠ 0 := ne_of_gt hu
    have hE : 1 < Real.exp u := Real.one_lt_exp_iff.mpr hu
    have hE1 : Real.exp u - 1 ≠ 0 := by linarith
    unfold QQ
    field_simp
  have i1 : IntegrableOn (fun u => QQ a u - u ^ 3 * Real.exp (-(a * u))) (Ioi (0 : ℝ)) :=
    (QQ_integrable ha).sub (integrableOn_pow_mul_exp 3 ha)
  have i2 : IntegrableOn (fun u : ℝ => 1 / 2 * (u ^ 4 * Real.exp (-(a * u)))) (Ioi (0 : ℝ)) :=
    (integrableOn_pow_mul_exp 4 ha).const_mul _
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul,
    integral_add i1 i2,
    integral_sub (QQ_integrable ha) (integrableOn_pow_mul_exp 3 ha), integral_const_mul,
    integral_QQ ha, integral_pow_mul_exp 3 ha, integral_pow_mul_exp 4 ha]
  have hs : Summable (fun k : ℕ => 1 / ((k : ℝ) + a) ^ 5) := by
    rw [← summable_nat_add_iff 1]
    exact (summable_hurwitz_tail ha).congr fun k => by push_cast; ring
  rw [hs.tsum_eq_zero_add]
  have hsh : ∑' k : ℕ, 1 / (((k + 1 : ℕ) : ℝ) + a) ^ 5 = ∑' k : ℕ, 1 / ((k : ℝ) + 1 + a) ^ 5 :=
    tsum_congr fun k => by push_cast; ring
  rw [hsh]
  norm_num [Nat.factorial]
  field_simp
  ring

/-! ## The theorem -/

open MeasureTheory Set in
/-- **Hermite's pole integral at `s = 5`, proved outright** (no axiom).  Same statement as the
former axiom `Zeta5.Axioms.hermite_pole_integral`. -/
theorem pole_integral (a : ℝ) (ha : 0 < a) :
    ∫ y in Ioi (0 : ℝ), wt y / (y ^ 2 + a ^ 2)
      = a ^ 4 * (∑' k : ℕ, 1 / ((k : ℝ) + a) ^ 5) - 1 / (2 * a) - 1 / 4 := by
  rw [lhs_eq ha, sum_integral_RR ha, laplace_rhs ha]

end Hermite
end Zeta5
