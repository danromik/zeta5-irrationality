/-
Zeta5/Positivity.lean

§2.4 of the paper: **Proposition 2.2** (p. 5), the positive integral representation.

  (2.10)  `μ_{ζ(5)}(R) = ∫_0^∞ R(y²) w(y) dy`,  `w(y) = (2π)⁴y⁵ ∑_{ℓ≥1} ℓ⁴e^{-2πℓy}/12`,
          and hence `G_K(ζ(5))` is positive definite.

WHAT IS PROVED HERE, AND WHAT IS ASSUMED.

*  The convergence of the series for `w`, the interchange of `∑` and `∫`, the moment
   identity `∫_0^∞ y^{2e}w(y) dy = (2e+5)!ζ(2e+2)/(12(2π)^{2e+2}) = μ(t^e)` (i.e. (2.2)),
   the positivity `w > 0` on `(0,∞)`, the integrability of every integrand occurring in
   (2.4), the passage from the pole integral to (2.3) *including both correction terms*
   `−1/4 + 1/(2j)`, the ℚ-linearity of `μ_X` through polynomial division and simple partial
   fractions, and the final Gram-matrix argument: **all proved, no `sorry`.**
*  The single external input is `Zeta5.Axioms.hermite_pole_integral`: Hermite's formula for
   the Hurwitz zeta function at `s = 5` (DLMF 25.11.29), in the form the paper's p. 5
   display gives it, i.e. already transported through the four integrations by parts.  See
   the docstring there; the four integrations by parts are *not* formalised.

Euler's formula for `ζ(2m)` is NOT assumed: it is Mathlib's `hasSum_zeta_nat`, already used
by `Zeta5.Functional.muMono_eq_zeta`, which is what identifies the Bernoulli form (2.2) with
the moment `(2e+5)!ζ(2e+2)/(12(2π)^{2e+2})`.

POSITION IN THE DEPENDENCY GRAPH.  This file imports `Zeta5.Functional` and `Zeta5.Axioms`
only, so it sits *below* `Zeta5.Interface`, which discharges its `prop_2_2_moment` and
`prop_2_2` from here.
-/
import Zeta5.Functional
import Zeta5.Axioms

namespace Zeta5

open Polynomial Finset MeasureTheory Set
open scoped Matrix

noncomputable section

namespace Positivity

/-! ## 1.  The series defining the weight `w`

`w(y) = (2π)⁴y⁵ ∑_{ℓ≥1} ℓ⁴e^{-2πℓy}/12`.  We index the series by `l = ℓ - 1 ≥ 0` and carry
an extra factor `y^k` throughout, because every integrand of (2.4) is a combination of
`y^k w(y)` and `w(y)/(y²+j²)`. -/

/-- `y^k` times the `ℓ = l+1` term of the series (2.10). -/
def wterm (k l : ℕ) (y : ℝ) : ℝ :=
  (2 * Real.pi) ^ 4 / 12 * ((l : ℝ) + 1) ^ 4 * y ^ (k + 5) *
    Real.exp (-(2 * Real.pi * ((l : ℝ) + 1) * y))

lemma wterm_nonneg (k l : ℕ) {y : ℝ} (hy : 0 ≤ y) : 0 ≤ wterm k l y := by
  have h1 : (0 : ℝ) ≤ (2 * Real.pi) ^ 4 / 12 := by positivity
  have h2 : (0 : ℝ) ≤ ((l : ℝ) + 1) ^ 4 := by positivity
  have h3 : (0 : ℝ) ≤ y ^ (k + 5) := pow_nonneg hy _
  have h4 : (0 : ℝ) ≤ Real.exp (-(2 * Real.pi * ((l : ℝ) + 1) * y)) := (Real.exp_pos _).le
  exact mul_nonneg (mul_nonneg (mul_nonneg h1 h2) h3) h4

lemma wterm_pos (k l : ℕ) {y : ℝ} (hy : 0 < y) : 0 < wterm k l y := by
  have h1 : (0 : ℝ) < (2 * Real.pi) ^ 4 / 12 := by positivity
  have h2 : (0 : ℝ) < ((l : ℝ) + 1) ^ 4 := by positivity
  have h3 : (0 : ℝ) < y ^ (k + 5) := pow_pos hy _
  have h4 : (0 : ℝ) < Real.exp (-(2 * Real.pi * ((l : ℝ) + 1) * y)) := Real.exp_pos _
  exact mul_pos (mul_pos (mul_pos h1 h2) h3) h4

lemma continuous_wterm (k l : ℕ) : Continuous (wterm k l) := by
  unfold wterm
  fun_prop

lemma measurable_wterm (k l : ℕ) : Measurable (wterm k l) := (continuous_wterm k l).measurable

/-- `e^{-2πℓy} = (e^{-2πy})^ℓ`. -/
lemma exp_eq_pow (l : ℕ) (y : ℝ) :
    Real.exp (-(2 * Real.pi * ((l : ℝ) + 1) * y))
      = Real.exp (-(2 * Real.pi * y)) ^ (l + 1) := by
  rw [← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

lemma summable_wterm (k : ℕ) {y : ℝ} (hy : 0 < y) : Summable (fun l => wterm k l y) := by
  have hr : ‖Real.exp (-(2 * Real.pi * y))‖ < 1 := by
    rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_lt_one_iff]
    have := Real.pi_pos
    nlinarith
  have h0 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 4 hr
  have h1 : Summable
      (fun l : ℕ => (((l + 1 : ℕ) : ℝ)) ^ 4 * Real.exp (-(2 * Real.pi * y)) ^ (l + 1)) :=
    (summable_nat_add_iff 1).2 h0
  have h2 := h1.mul_left ((2 * Real.pi) ^ 4 / 12 * y ^ (k + 5))
  refine h2.congr fun l => ?_
  rw [wterm, exp_eq_pow]
  push_cast
  ring

/-- The series (2.10), with the extra factor `y^k`.  Unconditional: for `y ≤ 0` both sides
are `0`, because `tsum` of a non-summable family is `0`. -/
lemma pow_mul_wt_eq_tsum (k : ℕ) (y : ℝ) : y ^ k * wt y = ∑' l : ℕ, wterm k l y := by
  have h : ∀ l : ℕ, wterm k l y
      = (y ^ k * ((2 * Real.pi) ^ 4 * y ^ 5 / 12))
        * (((l : ℝ) + 1) ^ 4 * Real.exp (-(2 * Real.pi * ((l : ℝ) + 1) * y))) := by
    intro l
    rw [wterm, pow_add]
    ring
  rw [tsum_congr h, tsum_mul_left, wt]
  ring

lemma wt_eq_tsum (y : ℝ) : wt y = ∑' l : ℕ, wterm 0 l y := by
  have := pow_mul_wt_eq_tsum 0 y
  simpa using this

lemma wt_nonneg {y : ℝ} (hy : 0 ≤ y) : 0 ≤ wt y := by
  rw [wt_eq_tsum]
  exact tsum_nonneg fun l => wterm_nonneg 0 l hy

/-- **"The weight is positive"** (p. 5, first line of the proof of Proposition 2.2). -/
lemma wt_pos {y : ℝ} (hy : 0 < y) : 0 < wt y := by
  rw [wt_eq_tsum]
  have hs := summable_wterm 0 hy
  have h1 : wterm 0 0 y ≤ ∑' l : ℕ, wterm 0 l y :=
    hs.le_tsum 0 fun j _ => wterm_nonneg 0 j hy.le
  exact lt_of_lt_of_le (wterm_pos 0 0 hy) h1

/-! ## 2.  The elementary Laplace integral `∫_0^∞ y^m e^{-cy} dy = m!/c^{m+1}` -/

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

/-! ## 3.  The term-by-term integrals -/

lemma integrableOn_wterm (k l : ℕ) : IntegrableOn (wterm k l) (Ioi 0) := by
  have hc : (0 : ℝ) < 2 * Real.pi * ((l : ℝ) + 1) := by
    have := Real.pi_pos; positivity
  have h : IntegrableOn (fun y : ℝ => (2 * Real.pi) ^ 4 / 12 * ((l : ℝ) + 1) ^ 4 *
      (y ^ (k + 5) * Real.exp (-((2 * Real.pi * ((l : ℝ) + 1)) * y)))) (Ioi 0) :=
    MeasureTheory.Integrable.const_mul (integrableOn_pow_mul_exp (k + 5) hc) _
  refine h.congr_fun (fun y _ => ?_) measurableSet_Ioi
  rw [wterm]
  ring

/-- A purely algebraic rearrangement used twice below (kept abstract so that `2π` stays an
opaque atom). -/
lemma algebra_helper {c L : ℝ} (F : ℝ) (hc : 0 < c) (hL : 0 < L) (a : ℕ) :
    c ^ 4 / 12 * L ^ 4 * F / (c * L) ^ (a + 4) = F / (12 * c ^ a) * (1 / L ^ a) := by
  have h1 : (c * L) ^ (a + 4) = (c ^ a * c ^ 4) * (L ^ a * L ^ 4) := by
    rw [mul_pow, pow_add, pow_add]
  rw [h1]
  have hc' : c ≠ 0 := ne_of_gt hc
  have hL' : L ≠ 0 := ne_of_gt hL
  have h2 : c ^ a ≠ 0 := pow_ne_zero _ hc'
  have h3 : L ^ a ≠ 0 := pow_ne_zero _ hL'
  have h4 : c ^ 4 ≠ 0 := pow_ne_zero _ hc'
  have h5 : L ^ 4 ≠ 0 := pow_ne_zero _ hL'
  field_simp

lemma integral_wterm (k l : ℕ) :
    ∫ y in Ioi (0 : ℝ), wterm k l y
      = (2 * Real.pi) ^ 4 / 12 * ((l : ℝ) + 1) ^ 4 * (Nat.factorial (k + 5) : ℝ)
          / (2 * Real.pi * ((l : ℝ) + 1)) ^ (k + 6) := by
  have hc : (0 : ℝ) < 2 * Real.pi * ((l : ℝ) + 1) := by
    have := Real.pi_pos; positivity
  have h : ∀ y : ℝ, wterm k l y
      = ((2 * Real.pi) ^ 4 / 12 * ((l : ℝ) + 1) ^ 4)
        * (y ^ (k + 5) * Real.exp (-((2 * Real.pi * ((l : ℝ) + 1)) * y))) := by
    intro y
    rw [wterm]
    ring
  simp_rw [h]
  rw [integral_const_mul, integral_pow_mul_exp (k + 5) hc]
  ring

/-- The integral of the `(l+1)`-st term, in the form
`(k+5)!/(12(2π)^{k+2}) · (l+1)^{-(k+2)}`.  At `k = 2e` this is the `l`-th summand of
`(2e+5)!ζ(2e+2)/(12(2π)^{2e+2})`. -/
lemma integral_wterm_eq (k l : ℕ) :
    ∫ y in Ioi (0 : ℝ), wterm k l y
      = (Nat.factorial (k + 5) : ℝ) / (12 * (2 * Real.pi) ^ (k + 2))
        * (1 / ((l : ℝ) + 1) ^ (k + 2)) := by
  have hpi : (0 : ℝ) < 2 * Real.pi := by have := Real.pi_pos; positivity
  have hl : (0 : ℝ) < (l : ℝ) + 1 := by positivity
  rw [integral_wterm, show k + 6 = (k + 2) + 4 by omega]
  exact algebra_helper _ hpi hl (k + 2)

lemma integral_wterm_even (e l : ℕ) :
    ∫ y in Ioi (0 : ℝ), wterm (2 * e) l y
      = (Nat.factorial (2 * e + 5) : ℝ) / (12 * (2 * Real.pi) ^ (2 * e + 2))
        * (1 / ((l : ℝ) + 1) ^ (2 * e + 2)) :=
  integral_wterm_eq (2 * e) l

lemma summable_one_div_succ_pow {p : ℕ} (hp : 1 < p) :
    Summable (fun l : ℕ => 1 / ((l : ℝ) + 1) ^ p) := by
  have h := Real.summable_one_div_nat_pow.mpr hp
  have h1 : Summable (fun l : ℕ => 1 / (((l + 1 : ℕ) : ℝ)) ^ p) := (summable_nat_add_iff 1).2 h
  refine h1.congr fun l => ?_
  push_cast
  ring

lemma summable_integral_wterm_even (e : ℕ) :
    Summable (fun l : ℕ => ∫ y in Ioi (0 : ℝ), wterm (2 * e) l y) := by
  have h := (summable_one_div_succ_pow (p := 2 * e + 2) (by omega)).mul_left
    ((Nat.factorial (2 * e + 5) : ℝ) / (12 * (2 * Real.pi) ^ (2 * e + 2)))
  exact h.congr fun l => (integral_wterm_even e l).symm

/-! ## 4.  Measurability and integrability of a pointwise-convergent series -/

/-- A series of measurable functions that converges pointwise on a measurable set `s` is
a.e.-strongly measurable for the restricted measure.  (Mathlib has `integral_tsum`, which
computes `∫ ∑'`, but no lemma producing measurability or integrability of `∑'` itself.) -/
lemma aestronglyMeasurable_tsum_restrict {F : ℕ → ℝ → ℝ} {s : Set ℝ} (hs : MeasurableSet s)
    (hmeas : ∀ l, Measurable (F l)) (hsum : ∀ y ∈ s, Summable (fun l => F l y)) :
    AEStronglyMeasurable (fun y => ∑' l, F l y) (volume.restrict s) := by
  classical
  have hGmeas : Measurable (Set.indicator s (fun y => ∑' l, F l y)) := by
    refine measurable_of_tendsto_metrizable' Filter.atTop
      (f := fun m : ℕ => Set.indicator s (fun y => ∑ l ∈ Finset.range m, F l y))
      (fun m => (Finset.measurable_sum _ (fun l _ => hmeas l)).indicator hs) ?_
    rw [tendsto_pi_nhds]
    intro y
    by_cases hy : y ∈ s
    · have h1 : ∀ m : ℕ, Set.indicator s (fun y => ∑ l ∈ Finset.range m, F l y) y
          = ∑ l ∈ Finset.range m, F l y := by
        intro m; simp [hy]
      have h2 : Set.indicator s (fun y => ∑' l, F l y) y = ∑' l, F l y := by
        simp [hy]
      simp only [h1, h2]
      exact (hsum y hy).hasSum.tendsto_sum_nat
    · have h1 : ∀ m : ℕ, Set.indicator s (fun y => ∑ l ∈ Finset.range m, F l y) y = 0 := by
        intro m; simp [hy]
      have h2 : Set.indicator s (fun y => ∑' l, F l y) y = 0 := by
        simp [hy]
      simp only [h1, h2]
      exact tendsto_const_nhds
  refine hGmeas.aestronglyMeasurable.congr ?_
  filter_upwards [ae_restrict_mem hs] with y hy
  simp [hy]

/-- Integrability of a nonnegative pointwise-convergent series whose term integrals are
summable. -/
lemma integrableOn_tsum {F : ℕ → ℝ → ℝ} {s : Set ℝ} (hs : MeasurableSet s)
    (hmeas : ∀ l, Measurable (F l)) (hnonneg : ∀ l, ∀ y ∈ s, 0 ≤ F l y)
    (hptwise : ∀ y ∈ s, Summable (fun l => F l y))
    (hint : ∀ l, IntegrableOn (F l) s)
    (hS : Summable (fun l => ∫ y in s, F l y)) :
    IntegrableOn (fun y => ∑' l, F l y) s := by
  refine ⟨aestronglyMeasurable_tsum_restrict hs hmeas hptwise, ?_⟩
  have hnonneg' : ∀ l, 0 ≤ᵐ[volume.restrict s] F l := by
    intro l
    filter_upwards [ae_restrict_mem hs] with y hy using hnonneg l y hy
  rw [hasFiniteIntegral_iff_ofReal]
  · have hcongr : ∫⁻ y in s, ENNReal.ofReal (∑' l, F l y)
        = ∫⁻ y in s, ∑' l, ENNReal.ofReal (F l y) := by
      refine lintegral_congr_ae ?_
      filter_upwards [ae_restrict_mem hs] with y hy
      exact ENNReal.ofReal_tsum_of_nonneg (fun l => hnonneg l y hy) (hptwise y hy)
    rw [hcongr, lintegral_tsum (fun l => ((hmeas l).ennreal_ofReal).aemeasurable)]
    have hval : ∀ l, ∫⁻ y in s, ENNReal.ofReal (F l y)
        = ENNReal.ofReal (∫ y in s, F l y) :=
      fun l => (ofReal_integral_eq_lintegral_ofReal (hint l) (hnonneg' l)).symm
    simp_rw [hval]
    rw [← ENNReal.ofReal_tsum_of_nonneg
      (fun l => integral_nonneg_of_ae (hnonneg' l)) hS]
    exact ENNReal.ofReal_lt_top
  · filter_upwards [ae_restrict_mem hs] with y hy
    exact tsum_nonneg fun l => hnonneg l y hy

/-! ## 5.  The moment identity: `∫_0^∞ y^{2e}w(y) dy = μ(t^e)` -/

lemma integrableOn_pow_mul_wt (k : ℕ) :
    IntegrableOn (fun y : ℝ => y ^ k * wt y) (Ioi 0) := by
  have hk : ∀ y : ℝ, y ^ k * wt y = ∑' l, wterm k l y := pow_mul_wt_eq_tsum k
  simp_rw [hk]
  -- the summability of the term integrals, for a general `k`
  have hS : Summable (fun l : ℕ => ∫ y in Ioi (0 : ℝ), wterm k l y) := by
    have h := (summable_one_div_succ_pow (p := k + 2) (by omega)).mul_left
      ((Nat.factorial (k + 5) : ℝ) / (12 * (2 * Real.pi) ^ (k + 2)))
    exact h.congr fun l => (integral_wterm_eq k l).symm
  exact integrableOn_tsum measurableSet_Ioi (measurable_wterm k)
    (fun l y hy => wterm_nonneg k l (le_of_lt hy))
    (fun y hy => summable_wterm k hy) (integrableOn_wterm k) hS

lemma integrableOn_wt : IntegrableOn wt (Ioi 0) := by
  have := integrableOn_pow_mul_wt 0
  simpa using this

/-- **The moment identity of Proposition 2.2** (p. 5, first display of the proof):
`∫_0^∞ y^{2e}w(y) dy = (2e+5)!ζ(2e+2)/(12(2π)^{2e+2}) = μ(t^e)`, the value (2.2). -/
theorem integral_pow_mul_wt (e : ℕ) :
    ∫ y in Ioi (0 : ℝ), y ^ (2 * e) * wt y = ((muMono e : ℚ) : ℝ) := by
  have hk : ∀ y : ℝ, y ^ (2 * e) * wt y = ∑' l, wterm (2 * e) l y :=
    pow_mul_wt_eq_tsum (2 * e)
  have hnorm : ∀ l : ℕ, ∫ y in Ioi (0 : ℝ), ‖wterm (2 * e) l y‖
      = ∫ y in Ioi (0 : ℝ), wterm (2 * e) l y := by
    intro l
    refine setIntegral_congr_fun measurableSet_Ioi (fun y hy => ?_)
    exact Real.norm_of_nonneg (wterm_nonneg _ _ (le_of_lt hy))
  have hsum : Summable (fun l : ℕ => ∫ y in Ioi (0 : ℝ), ‖wterm (2 * e) l y‖) := by
    refine (summable_integral_wterm_even e).congr fun l => (hnorm l).symm
  have hswap := integral_tsum_of_summable_integral_norm
    (μ := volume.restrict (Ioi (0 : ℝ))) (F := fun l => wterm (2 * e) l)
    (fun l => integrableOn_wterm (2 * e) l) hsum
  simp_rw [hk]
  rw [← hswap]
  -- now: `∑' l, ∫ wterm = μ(t^e)`
  have hval : ∑' l : ℕ, ∫ y in Ioi (0 : ℝ), wterm (2 * e) l y
      = (Nat.factorial (2 * e + 5) : ℝ) / (12 * (2 * Real.pi) ^ (2 * e + 2))
        * ∑' l : ℕ, (1 / ((l : ℝ) + 1) ^ (2 * e + 2)) := by
    rw [← tsum_mul_left]
    exact tsum_congr fun l => integral_wterm_even e l
  rw [hval, Functional.muMono_eq_zeta e]
  have hpi : (12 : ℝ) * (2 * Real.pi) ^ (2 * e + 2) ≠ 0 := by
    have := Real.pi_pos; positivity
  field_simp

/-! ## 6.  The pole integral: `∫_0^∞ w(y)/(y²+j²) dy = μ_{ζ(5)}(1/(t+j²))`

This is where `Zeta5.Axioms.hermite_pole_integral` enters, and the only place. -/

lemma integrableOn_wt_div_pole {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun y : ℝ => wt y / (y ^ 2 + a ^ 2)) (Ioi 0) := by
  have ha2 : (0 : ℝ) < a ^ 2 := pow_pos ha 2
  have hw := integrableOn_wt
  have hg : IntegrableOn (fun y : ℝ => (a ^ 2)⁻¹ * wt y) (Ioi 0) :=
    MeasureTheory.Integrable.const_mul hw ((a ^ 2)⁻¹)
  have hcont : Continuous (fun y : ℝ => (y ^ 2 + a ^ 2)⁻¹) := by
    refine Continuous.inv₀ (by fun_prop) (fun y => ?_)
    have : (0 : ℝ) < y ^ 2 + a ^ 2 := by nlinarith [sq_nonneg y]
    exact ne_of_gt this
  refine Integrable.mono' hg ?_ ?_
  · simp_rw [div_eq_mul_inv]
    exact hw.aestronglyMeasurable.mul hcont.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hy0 : (0 : ℝ) < y := hy
    have hwt : 0 ≤ wt y := wt_nonneg hy0.le
    have hden : (0 : ℝ) < y ^ 2 + a ^ 2 := by nlinarith [sq_nonneg y]
    have hle : a ^ 2 ≤ y ^ 2 + a ^ 2 := by nlinarith [sq_nonneg y]
    rw [Real.norm_of_nonneg (div_nonneg hwt hden.le), div_le_iff₀ hden]
    have hc : (0 : ℝ) ≤ (a ^ 2)⁻¹ * wt y := mul_nonneg (inv_nonneg.2 ha2.le) hwt
    have h1 : (a ^ 2)⁻¹ * wt y * (a ^ 2) ≤ (a ^ 2)⁻¹ * wt y * (y ^ 2 + a ^ 2) :=
      mul_le_mul_of_nonneg_left hle hc
    have h2 : (a ^ 2)⁻¹ * wt y * (a ^ 2) = wt y := by field_simp
    linarith

/-- `H^{(5)}` as a sum over `range`. -/
lemma H5_eq_sum_range (m : ℕ) :
    ((H5 m : ℚ) : ℝ) = ∑ i ∈ Finset.range m, 1 / ((i : ℝ) + 1) ^ 5 := by
  induction m with
  | zero => simp [H5]
  | succ m ih =>
      have hstep : H5 (m + 1) = H5 m + 1 / ((m : ℚ) + 1) ^ 5 := by
        rw [H5, H5, Finset.sum_Icc_succ_top (by omega)]
        push_cast
        ring
      rw [hstep, Finset.sum_range_succ, ← ih]
      push_cast
      ring

/-- `ζ(5, m+1) = ζ(5) − H^{(5)}_m`: the Hurwitz zeta value at a positive integer. -/
lemma tsum_hurwitz (m : ℕ) :
    ∑' k : ℕ, 1 / ((k : ℝ) + ((m : ℝ) + 1)) ^ 5 = zeta5 - ((H5 m : ℚ) : ℝ) := by
  have hsummable : Summable (fun v : ℕ => 1 / ((v : ℝ) + 1) ^ 5) :=
    summable_one_div_succ_pow (by omega)
  have hsplit := hsummable.sum_add_tsum_nat_add m
  have hshift : (∑' i : ℕ, 1 / (((i + m : ℕ) : ℝ) + 1) ^ 5)
      = ∑' k : ℕ, 1 / ((k : ℝ) + ((m : ℝ) + 1)) ^ 5 := by
    refine tsum_congr fun i => ?_
    push_cast
    ring_nf
  rw [hshift] at hsplit
  rw [H5_eq_sum_range]
  have hz : zeta5 = ∑' v : ℕ, 1 / ((v : ℝ) + 1) ^ 5 := rfl
  rw [hz]
  linarith [hsplit]

lemma evalZeta5_muPole (j : ℕ) :
    evalZeta5 (muPole j)
      = (j : ℝ) ^ 4 * (zeta5 - ((H5 j : ℚ) : ℝ)) - 1 / 4 + 1 / (2 * (j : ℝ)) := by
  rw [muPole, evalZeta5]
  simp only [map_add, map_sub, map_mul, evalZeta5Hom, RingHom.coe_coe,
    AlgHom.toRingHom_eq_coe, aeval_C, aeval_X, eq_ratCast]
  push_cast
  ring

/-- **The pole values of Proposition 2.2** (p. 5): `∫_0^∞ w(y)/(y²+j²) dy` equals the value
(2.3) of `μ_{ζ(5)}(1/(t+j²))`, *including both correction terms* `−1/4 + 1/(2j)`.

The Hurwitz-zeta value at `a = j` is `ζ(5) − H^{(5)}_{j−1} = ζ(5) − H^{(5)}_j + j^{-5}`, and
the extra `j⁴·j^{-5} = 1/j` is exactly what turns the `−1/(2j)` of the general formula into
the `+1/(2j)` printed in (2.3). -/
theorem integral_wt_div_pole (j : ℕ) (hj : 0 < j) :
    ∫ y in Ioi (0 : ℝ), wt y / (y ^ 2 + (j : ℝ) ^ 2) = evalZeta5 (muPole j) := by
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  have hja : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
  rw [Axioms.hermite_pole_integral _ hja]
  have hz : ∑' k : ℕ, 1 / ((k : ℝ) + ((m + 1 : ℕ) : ℝ)) ^ 5 = zeta5 - ((H5 m : ℚ) : ℝ) := by
    have := tsum_hurwitz m
    rw [← this]
    refine tsum_congr fun k => ?_
    push_cast
    ring
  rw [hz, evalZeta5_muPole]
  have hH : ((H5 (m + 1) : ℚ) : ℝ) = ((H5 m : ℚ) : ℝ) + 1 / ((m : ℝ) + 1) ^ 5 := by
    rw [H5_eq_sum_range, H5_eq_sum_range, Finset.sum_range_succ]
  rw [hH]
  have hm : ((m : ℝ) + 1) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-! ## 7.  Polynomial division and partial fractions, evaluated on `(0,∞)` -/

lemma aeval_X_add_C_sq (r : ℕ) (y : ℝ) :
    aeval (y ^ 2 : ℝ) (X + C ((r : ℚ) ^ 2)) = y ^ 2 + (r : ℝ) ^ 2 := by
  simp only [map_add, aeval_X, aeval_C, eq_ratCast]
  push_cast
  ring

/-- `D_m(y²) > 0`. -/
lemma aeval_D_pos (m : ℕ) (y : ℝ) : 0 < aeval (y ^ 2 : ℝ) (D m) := by
  rw [D, map_prod]
  refine Finset.prod_pos fun r hr => ?_
  have hr1 : 1 ≤ r := (Finset.mem_Icc.1 hr).1
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr1
  rw [aeval_X_add_C_sq]
  positivity

/-- `D_tail(y²) > 0`. -/
lemma aeval_Dtail_pos (n : ℕ) (y : ℝ) : 0 < aeval (y ^ 2 : ℝ) (Dtail n) := by
  rw [Dtail, map_prod]
  refine Finset.prod_pos fun r hr => ?_
  have hr1 : 1 ≤ r := by have := (Finset.mem_Ioc.1 hr).1; omega
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr1
  rw [aeval_X_add_C_sq]
  positivity

/-- `Q_r(y²)/D_tail(y²) = 1/(y²+r²)`: the basis element `1/(t+r²)` at `t = y²`. -/
lemma aeval_cof_div (n : ℕ) {r : ℕ} (hr : r ∈ Finset.Ioc (N n) (K n)) (y : ℝ) :
    aeval (y ^ 2 : ℝ) (Functional.cof n r) / aeval (y ^ 2 : ℝ) (Dtail n)
      = 1 / (y ^ 2 + (r : ℝ) ^ 2) := by
  have hr1 : 1 ≤ r := by have := (Finset.mem_Ioc.1 hr).1; omega
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr1
  have hden : (0 : ℝ) < y ^ 2 + (r : ℝ) ^ 2 := by positivity
  have hmul := congrArg (aeval (y ^ 2 : ℝ)) (Functional.cof_mul n hr)
  rw [map_mul, aeval_X_add_C_sq] at hmul
  have hD := aeval_Dtail_pos n y
  rw [← hmul]
  rw [← hmul] at hD
  have hcof : aeval (y ^ 2 : ℝ) (Functional.cof n r) ≠ 0 := by
    intro hcon
    rw [hcon, mul_zero] at hD
    exact lt_irrefl _ hD
  field_simp

/-- **Polynomial division and simple partial fractions at `t = y²`** (§2.1, the sentence
after (2.3)): `A(y²)/D_tail(y²) = (A /ₘ D_tail)(y²) + ∑_r c_r/(y²+r²)`. -/
lemma integrand_decomp (n : ℕ) (A : ℚ[X]) (y : ℝ) :
    aeval (y ^ 2 : ℝ) A / aeval (y ^ 2 : ℝ) (Dtail n)
      = aeval (y ^ 2 : ℝ) (A /ₘ Dtail n)
        + ∑ r ∈ Ioc (N n) (K n), ((residue n A r : ℚ) : ℝ) / (y ^ 2 + (r : ℝ) ^ 2) := by
  have hD := aeval_Dtail_pos n y
  have hpf := congrArg (aeval (y ^ 2 : ℝ)) (Functional.partial_fractions n A)
  rw [map_add, map_mul, map_sum] at hpf
  rw [hpf, add_div, mul_div_assoc, div_self (ne_of_gt hD), mul_one, Finset.sum_div]
  congr 1
  refine Finset.sum_congr rfl fun r hr => ?_
  rw [map_mul, aeval_C, eq_ratCast, mul_div_assoc, aeval_cof_div n hr]
  ring

/-! ## 8.  Integrability and value of the two kinds of integrand -/

lemma aeval_eq_sum_pow (P : ℚ[X]) (y : ℝ) :
    aeval (y ^ 2 : ℝ) P
      = ∑ i ∈ Finset.range (P.natDegree + 1), ((P.coeff i : ℚ) : ℝ) * y ^ (2 * i) := by
  rw [Polynomial.aeval_eq_sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.smul_def, eq_ratCast, ← pow_mul]

lemma integrableOn_aeval_mul_wt (P : ℚ[X]) :
    IntegrableOn (fun y : ℝ => aeval (y ^ 2 : ℝ) P * wt y) (Ioi 0) := by
  have hdecomp : ∀ y : ℝ, aeval (y ^ 2 : ℝ) P * wt y
      = ∑ i ∈ Finset.range (P.natDegree + 1),
          ((P.coeff i : ℚ) : ℝ) * (y ^ (2 * i) * wt y) := by
    intro y
    rw [aeval_eq_sum_pow, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp_rw [hdecomp]
  refine integrable_finsetSum _ fun i _ => ?_
  exact MeasureTheory.Integrable.const_mul (integrableOn_pow_mul_wt (2 * i)) _

/-- The polynomial part of (2.10): `∫_0^∞ P(y²)w(y) dy = μ(P)`. -/
lemma integral_aeval_mul_wt (P : ℚ[X]) :
    ∫ y in Ioi (0 : ℝ), aeval (y ^ 2 : ℝ) P * wt y = ((muPoly P : ℚ) : ℝ) := by
  have hdecomp : ∀ y : ℝ, aeval (y ^ 2 : ℝ) P * wt y
      = ∑ i ∈ Finset.range (P.natDegree + 1),
          ((P.coeff i : ℚ) : ℝ) * (y ^ (2 * i) * wt y) := by
    intro y
    rw [aeval_eq_sum_pow, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp_rw [hdecomp]
  rw [integral_finsetSum _ (fun i _ =>
    MeasureTheory.Integrable.const_mul (integrableOn_pow_mul_wt (2 * i)) _)]
  rw [Functional.muPoly_eq_sum P Polynomial.supp_subset_range_natDegree_succ]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_const_mul, integral_pow_mul_wt i]

lemma integrableOn_pole_term (n : ℕ) (A : ℚ[X]) {r : ℕ} (hr : r ∈ Finset.Ioc (N n) (K n)) :
    IntegrableOn
      (fun y : ℝ => ((residue n A r : ℚ) : ℝ) / (y ^ 2 + (r : ℝ) ^ 2) * wt y) (Ioi 0) := by
  have hr1 : 1 ≤ r := by have := (Finset.mem_Ioc.1 hr).1; omega
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr1
  have h : ∀ y : ℝ, ((residue n A r : ℚ) : ℝ) / (y ^ 2 + (r : ℝ) ^ 2) * wt y
      = ((residue n A r : ℚ) : ℝ) * (wt y / (y ^ 2 + (r : ℝ) ^ 2)) := by
    intro y; ring
  simp_rw [h]
  exact MeasureTheory.Integrable.const_mul (integrableOn_wt_div_pole hrR) _

lemma integral_pole_term (n : ℕ) (A : ℚ[X]) {r : ℕ} (hr : r ∈ Finset.Ioc (N n) (K n)) :
    ∫ y in Ioi (0 : ℝ), ((residue n A r : ℚ) : ℝ) / (y ^ 2 + (r : ℝ) ^ 2) * wt y
      = ((residue n A r : ℚ) : ℝ) * evalZeta5 (muPole r) := by
  have hr1 : 1 ≤ r := by have := (Finset.mem_Ioc.1 hr).1; omega
  have h : ∀ y : ℝ, ((residue n A r : ℚ) : ℝ) / (y ^ 2 + (r : ℝ) ^ 2) * wt y
      = ((residue n A r : ℚ) : ℝ) * (wt y / (y ^ 2 + (r : ℝ) ^ 2)) := by
    intro y; ring
  simp_rw [h]
  rw [integral_const_mul, integral_wt_div_pole r hr1]

/-! ## 9.  Proposition 2.2, (2.10) -/

lemma evalZeta5_add (P R : ℚ[X]) : evalZeta5 (P + R) = evalZeta5 P + evalZeta5 R := by
  simp [evalZeta5]

lemma evalZeta5_sum {ι : Type*} (s : Finset ι) (f : ι → ℚ[X]) :
    evalZeta5 (∑ i ∈ s, f i) = ∑ i ∈ s, evalZeta5 (f i) := by
  simp [evalZeta5]

lemma evalZeta5_muOver (n : ℕ) (A : ℚ[X]) :
    evalZeta5 (muOver n A)
      = ((muPoly (A /ₘ Dtail n) : ℚ) : ℝ)
        + ∑ r ∈ Ioc (N n) (K n), ((residue n A r : ℚ) : ℝ) * evalZeta5 (muPole r) := by
  rw [muOver, evalZeta5_add, evalZeta5_C, evalZeta5_sum]
  congr 1
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [evalZeta5_mul, evalZeta5_C]

/-- Every integrand of (2.4) is integrable on `(0,∞)`. -/
lemma integrableOn_moment (n : ℕ) (A : ℚ[X]) :
    IntegrableOn
      (fun y : ℝ => (aeval (y ^ 2 : ℝ) A / aeval (y ^ 2 : ℝ) (Dtail n)) * wt y) (Ioi 0) := by
  have hsplit : ∀ y : ℝ,
      (aeval (y ^ 2 : ℝ) A / aeval (y ^ 2 : ℝ) (Dtail n)) * wt y
        = aeval (y ^ 2 : ℝ) (A /ₘ Dtail n) * wt y
          + ∑ r ∈ Ioc (N n) (K n),
              ((residue n A r : ℚ) : ℝ) / (y ^ 2 + (r : ℝ) ^ 2) * wt y := by
    intro y
    rw [integrand_decomp n A y, add_mul, Finset.sum_mul]
  simp_rw [hsplit]
  refine (integrableOn_aeval_mul_wt (A /ₘ Dtail n)).add ?_
  exact integrable_finsetSum _ fun r hr => integrableOn_pole_term n A hr

/-- **Proposition 2.2, (2.10)** (p. 5).  For every rational function of (2.4),
`μ_{ζ(5)}(A(t)/D_tail(t)) = ∫_0^∞ (A(y²)/D_tail(y²)) w(y) dy`.

Proved from the moment identity `∫ y^{2e}w = μ(t^e)` (`integral_pow_mul_wt`), the pole
integrals `∫ w/(y²+j²) = μ_{ζ(5)}(1/(t+j²))` (`integral_wt_div_pole`), and the ℚ-linearity
of `μ_X`, i.e. polynomial division and simple partial fractions
(`Functional.partial_fractions`).  "Linearity proves (2.10)", p. 5. -/
theorem prop_2_2_moment (n : ℕ) (A : ℚ[X]) :
    evalZeta5 (muOver n A)
      = ∫ y in Ioi (0 : ℝ),
          (aeval (y ^ 2 : ℝ) A / aeval (y ^ 2 : ℝ) (Dtail n)) * wt y := by
  have hsplit : ∀ y : ℝ,
      (aeval (y ^ 2 : ℝ) A / aeval (y ^ 2 : ℝ) (Dtail n)) * wt y
        = aeval (y ^ 2 : ℝ) (A /ₘ Dtail n) * wt y
          + ∑ r ∈ Ioc (N n) (K n),
              ((residue n A r : ℚ) : ℝ) / (y ^ 2 + (r : ℝ) ^ 2) * wt y := by
    intro y
    rw [integrand_decomp n A y, add_mul, Finset.sum_mul]
  simp_rw [hsplit]
  rw [integral_add (integrableOn_aeval_mul_wt (A /ₘ Dtail n))
    (integrable_finsetSum _ fun r hr => integrableOn_pole_term n A hr)]
  rw [integral_finsetSum _ (fun r hr => integrableOn_pole_term n A hr)]
  rw [integral_aeval_mul_wt, evalZeta5_muOver]
  congr 1
  exact Finset.sum_congr rfl fun r hr => (integral_pole_term n A hr).symm

/-! ## 10.  Proposition 2.2, the "Hence" clause: `G_K(ζ(5))` is positive definite

The paper's display, for `0 ≠ q` real of degree `< h`:
`∫_0^∞ D_N(y²)⁶q(y²)²/D_K(y²) · w(y) dy > 0`, which is the quadratic form of `G_K(ζ(5))` at
the coefficient vector of `q`.  Here the cancellation `D_N⁶/D_K = D_N⁵/D_tail` of §2.3 is
already built into `entryNum`. -/

lemma aeval_entryNum (n : ℕ) (i j : ℕ) (y : ℝ) :
    aeval (y ^ 2 : ℝ) (entryNum n i j)
      = aeval (y ^ 2 : ℝ) (D (N n)) ^ 5 * (y ^ 2) ^ (i + j) := by
  rw [entryNum, map_mul, map_pow, map_pow, aeval_X]

/-- The paper's integrand at the coefficient vector `x`, expanded over the matrix entries. -/
lemma quad_pointwise (n : ℕ) (x : Fin (h n) → ℝ) (y : ℝ) :
    aeval (y ^ 2 : ℝ) (D (N n)) ^ 5 / aeval (y ^ 2 : ℝ) (Dtail n)
        * (∑ i : Fin (h n), x i * (y ^ 2) ^ (i : ℕ)) ^ 2 * wt y
      = ∑ i : Fin (h n), ∑ j : Fin (h n),
          x i * x j
            * ((aeval (y ^ 2 : ℝ) (entryNum n i j) / aeval (y ^ 2 : ℝ) (Dtail n)) * wt y) := by
  have hDt : aeval (y ^ 2 : ℝ) (Dtail n) ≠ 0 := ne_of_gt (aeval_Dtail_pos n y)
  have hs : (∑ i : Fin (h n), x i * (y ^ 2) ^ (i : ℕ)) ^ 2
      = ∑ i : Fin (h n), ∑ j : Fin (h n),
          (x i * (y ^ 2) ^ (i : ℕ)) * (x j * (y ^ 2) ^ (j : ℕ)) := by
    rw [sq, Finset.sum_mul_sum]
  rw [hs, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [aeval_entryNum, pow_add]
  field_simp
  -- `field_simp` closes it

lemma integrableOn_quadForm (n : ℕ) (x : Fin (h n) → ℝ) :
    IntegrableOn (fun y : ℝ =>
      aeval (y ^ 2 : ℝ) (D (N n)) ^ 5 / aeval (y ^ 2 : ℝ) (Dtail n)
        * (∑ i : Fin (h n), x i * (y ^ 2) ^ (i : ℕ)) ^ 2 * wt y) (Ioi 0) := by
  simp_rw [quad_pointwise n x]
  refine integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => ?_
  exact MeasureTheory.Integrable.const_mul (integrableOn_moment n (entryNum n i j)) _

/-- The quadratic form of `G_K(ζ(5))` is the paper's integral. -/
lemma quadForm_eq_integral (n : ℕ) (x : Fin (h n) → ℝ) :
    star x ⬝ᵥ (((G n).map evalZeta5) *ᵥ x)
      = ∫ y in Ioi (0 : ℝ),
          aeval (y ^ 2 : ℝ) (D (N n)) ^ 5 / aeval (y ^ 2 : ℝ) (Dtail n)
            * (∑ i : Fin (h n), x i * (y ^ 2) ^ (i : ℕ)) ^ 2 * wt y := by
  have hdot : star x ⬝ᵥ (((G n).map evalZeta5) *ᵥ x)
      = ∑ i : Fin (h n), ∑ j : Fin (h n),
          x i * x j * evalZeta5 (muOver n (entryNum n i j)) := by
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial,
      Matrix.map_apply, G, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [hdot]
  have hterm : ∀ i j : Fin (h n),
      x i * x j * evalZeta5 (muOver n (entryNum n i j))
        = ∫ y in Ioi (0 : ℝ), x i * x j
            * ((aeval (y ^ 2 : ℝ) (entryNum n i j) / aeval (y ^ 2 : ℝ) (Dtail n)) * wt y) := by
    intro i j
    rw [integral_const_mul, ← prop_2_2_moment]
  simp_rw [hterm]
  have hinner : ∀ i : Fin (h n),
      (∑ j : Fin (h n), ∫ y in Ioi (0 : ℝ), x i * x j
          * ((aeval (y ^ 2 : ℝ) (entryNum n i j) / aeval (y ^ 2 : ℝ) (Dtail n)) * wt y))
        = ∫ y in Ioi (0 : ℝ), ∑ j : Fin (h n), x i * x j
            * ((aeval (y ^ 2 : ℝ) (entryNum n i j) / aeval (y ^ 2 : ℝ) (Dtail n)) * wt y) := by
    intro i
    refine (integral_finsetSum _ (fun j _ => ?_)).symm
    exact MeasureTheory.Integrable.const_mul (integrableOn_moment n (entryNum n i j)) _
  rw [Finset.sum_congr rfl (fun i _ => hinner i)]
  have houter :
      (∑ i : Fin (h n), ∫ y in Ioi (0 : ℝ), ∑ j : Fin (h n), x i * x j
          * ((aeval (y ^ 2 : ℝ) (entryNum n i j) / aeval (y ^ 2 : ℝ) (Dtail n)) * wt y))
        = ∫ y in Ioi (0 : ℝ), ∑ i : Fin (h n), ∑ j : Fin (h n), x i * x j
            * ((aeval (y ^ 2 : ℝ) (entryNum n i j) / aeval (y ^ 2 : ℝ) (Dtail n)) * wt y) := by
    refine (integral_finsetSum _ (fun i _ => ?_)).symm
    refine integrable_finsetSum _ (fun j _ => ?_)
    exact MeasureTheory.Integrable.const_mul (integrableOn_moment n (entryNum n i j)) _
  rw [houter]
  exact setIntegral_congr_fun measurableSet_Ioi (fun y _ => (quad_pointwise n x y).symm)

/-- **Proposition 2.2, "Hence `G_K(ζ(5))` is positive definite"** (p. 5).

The matrix is real symmetric (it is Hankel), and for `0 ≠ x` the quadratic form is
`∫_0^∞ D_N(y²)⁵q(y²)²/D_tail(y²) · w(y) dy` with `q = ∑ x_i X^i ≠ 0`; the integrand is
`≥ 0` on `(0,∞)` and vanishes only at the finitely many `y > 0` with `q(y²) = 0`. -/
theorem prop_2_2 (n : ℕ) : Matrix.PosDef ((G n).map evalZeta5) := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · unfold Matrix.IsHermitian
    ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.map_apply, star_trivial]
    exact congrArg evalZeta5 (G_hankel n j i i j (Nat.add_comm _ _))
  · intro x hx
    rw [quadForm_eq_integral n x]
    classical
    -- the paper's `q`, a nonzero real polynomial of degree `< h`
    set P : ℝ[X] := ∑ i : Fin (h n), C (x i) * X ^ (i : ℕ) with hPdef
    have hPeval : ∀ z : ℝ, P.eval z = ∑ i : Fin (h n), x i * z ^ (i : ℕ) := by
      intro z
      rw [hPdef]
      simp [Polynomial.eval_finsetSum]
    have hPcoeff : ∀ k : Fin (h n), P.coeff (k : ℕ) = x k := by
      intro k
      rw [hPdef, Polynomial.finsetSum_coeff]
      rw [Finset.sum_eq_single k]
      · simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
      · intro b _ hbk
        have hne : ¬ ((k : ℕ) = (b : ℕ)) := fun hc => hbk (Fin.ext hc.symm)
        simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, hne]
      · intro hcon
        exact absurd (Finset.mem_univ k) hcon
    obtain ⟨k, hk⟩ : ∃ k : Fin (h n), x k ≠ 0 := by
      by_contra hc
      refine hx (funext fun k => ?_)
      by_contra hkk
      exact hc ⟨k, hkk⟩
    have hPne : P ≠ 0 := by
      intro h0
      apply hk
      rw [← hPcoeff k, h0, Polynomial.coeff_zero]
    -- the zero set of `y ↦ q(y²)` is finite
    have hP2 : P.comp (X ^ 2 : ℝ[X]) ≠ 0 := by
      intro hcon
      refine hPne (Polynomial.eq_zero_of_infinite_isRoot P ?_)
      refine Set.Infinite.mono ?_ (Set.Ioi_infinite (0 : ℝ))
      intro r hr
      have h1 : (P.comp (X ^ 2 : ℝ[X])).eval (Real.sqrt r) = 0 := by rw [hcon]; simp
      rw [Polynomial.eval_comp] at h1
      simp only [Polynomial.eval_pow, Polynomial.eval_X] at h1
      rw [Real.sq_sqrt (le_of_lt hr)] at h1
      exact h1
    have hZfin : {y : ℝ | P.eval (y ^ 2) = 0}.Finite := by
      have heq : {y : ℝ | P.eval (y ^ 2) = 0}
          = {y : ℝ | (P.comp (X ^ 2 : ℝ[X])).IsRoot y} := by
        ext y
        simp [Polynomial.IsRoot, Polynomial.eval_comp]
      rw [heq, ← Set.not_infinite]
      exact fun hinf => hP2 (Polynomial.eq_zero_of_infinite_isRoot _ hinf)
    -- the integrand
    set Fq : ℝ → ℝ := fun y =>
      aeval (y ^ 2 : ℝ) (D (N n)) ^ 5 / aeval (y ^ 2 : ℝ) (Dtail n)
        * (∑ i : Fin (h n), x i * (y ^ 2) ^ (i : ℕ)) ^ 2 * wt y with hFq
    have hFqpos : ∀ y : ℝ, 0 < y → P.eval (y ^ 2) ≠ 0 → 0 < Fq y := by
      intro y hy hne
      have h1 : (0 : ℝ) < aeval (y ^ 2 : ℝ) (D (N n)) ^ 5 := pow_pos (aeval_D_pos _ y) 5
      have h2 : (0 : ℝ) < aeval (y ^ 2 : ℝ) (Dtail n) := aeval_Dtail_pos n y
      have h3 : (0 : ℝ) < (∑ i : Fin (h n), x i * (y ^ 2) ^ (i : ℕ)) ^ 2 := by
        have hne' : (∑ i : Fin (h n), x i * (y ^ 2) ^ (i : ℕ)) ≠ 0 := by
          rw [← hPeval]; exact hne
        exact lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hne'))
      have h4 : (0 : ℝ) < wt y := wt_pos hy
      rw [hFq]
      exact mul_pos (mul_pos (div_pos h1 h2) h3) h4
    have hFqnn : ∀ y : ℝ, 0 < y → 0 ≤ Fq y := by
      intro y hy
      have h1 : (0 : ℝ) < aeval (y ^ 2 : ℝ) (D (N n)) ^ 5 := pow_pos (aeval_D_pos _ y) 5
      have h2 : (0 : ℝ) < aeval (y ^ 2 : ℝ) (Dtail n) := aeval_Dtail_pos n y
      have h4 : (0 : ℝ) ≤ wt y := wt_nonneg hy.le
      rw [hFq]
      exact mul_nonneg (mul_nonneg (div_pos h1 h2).le (sq_nonneg _)) h4
    have hae : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] Fq := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy using hFqnn y hy
    rw [integral_pos_iff_support_of_nonneg_ae hae (integrableOn_quadForm n x)]
    -- the support has infinite measure
    have hsub : Ioi (0 : ℝ) \ {y : ℝ | P.eval (y ^ 2) = 0} ⊆ Function.support Fq := by
      intro y hy
      exact ne_of_gt (hFqpos y hy.1 hy.2)
    have hZmeas : MeasurableSet {y : ℝ | P.eval (y ^ 2) = 0} := hZfin.measurableSet
    have h1 : (volume.restrict (Ioi (0 : ℝ))) (Ioi 0 \ {y : ℝ | P.eval (y ^ 2) = 0})
        = volume ((Ioi (0 : ℝ) \ {y : ℝ | P.eval (y ^ 2) = 0}) ∩ Ioi 0) :=
      Measure.restrict_apply (measurableSet_Ioi.diff hZmeas)
    have h2 : (Ioi (0 : ℝ) \ {y : ℝ | P.eval (y ^ 2) = 0}) ∩ Ioi 0
        = Ioi (0 : ℝ) \ {y : ℝ | P.eval (y ^ 2) = 0} := by
      ext y; constructor
      · rintro ⟨hy, _⟩; exact hy
      · intro hy; exact ⟨hy, hy.1⟩
    have h3 : volume (Ioi (0 : ℝ) \ {y : ℝ | P.eval (y ^ 2) = 0}) = volume (Ioi (0 : ℝ)) :=
      measure_sdiff_null (hZfin.measure_zero volume)
    have h4 : (volume.restrict (Ioi (0 : ℝ))) (Ioi 0 \ {y : ℝ | P.eval (y ^ 2) = 0}) = ⊤ := by
      rw [h1, h2, h3, Real.volume_Ioi]
    refine lt_of_lt_of_le ?_ (measure_mono hsub)
    rw [h4]
    simp

/-! ## 11.  Axiom audit

These `#print axioms` lines appear in the build log.  Everything up to and including the
moment identity is proved from `[propext, Classical.choice, Quot.sound]` alone; the two
statements of Proposition 2.2 add exactly one named external input,
`Zeta5.Axioms.hermite_pole_integral`, and **no `sorryAx`**. -/

#print axioms Zeta5.Positivity.wt_pos
#print axioms Zeta5.Positivity.integral_pow_mul_exp
#print axioms Zeta5.Positivity.integral_pow_mul_wt
#print axioms Zeta5.Positivity.integrableOn_pow_mul_wt
#print axioms Zeta5.Positivity.integrand_decomp
#print axioms Zeta5.Positivity.integral_aeval_mul_wt
#print axioms Zeta5.Positivity.integral_wt_div_pole
#print axioms Zeta5.Positivity.prop_2_2_moment
#print axioms Zeta5.Positivity.prop_2_2

end Positivity

end

end Zeta5
