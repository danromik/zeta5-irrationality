/-
Zeta5/AppendixB.lean

**Appendix B: the exact arithmetic integrals.**

This file proves the `Zeta5.eq_5_16_5_18` interface statement outright.  Everything that
Appendix B calls a *computation* is computed here: no finite rational verification is
assumed.

Contents, in the paper's numbering.  Everything is PROVED, with **no `sorry`**; the §5.3
analysis behind (5.14)–(5.17) is in `Zeta5/Tail.lean` and is instantiated here.

* (B.1), §B.1   the `z`-integral of (5.4) in closed form, by fractional parts and minima
                (`Gam_eq`), from the displayed identity `ℓ(x,z) - 2x = e(f)(1_{z<d₀(f)} -
                2d₀(f))` (`ellR_eq`) and the three integrals `∫1`, `∫1_{z<c}`,
                `∫1_{z<c}1_{z<c'}` (`integral_expand`).
* (5.12)–(5.13) `R(x) = x F(x) + Q(x)` (`RR_closed`); hence `R` is measurable and bounded on
                compacts, so `R x^{-3}` is interval-integrable on every `[a,b] ⊆ (0,∞)`
                (`intervalIntegrable_RR_div`) — the assertion the paper makes right after
                (5.6).
* §B.1          the quadratic-coefficient cancellation
                `2λ - 12λα + 2(H² - H - λ²) - 18α² + 6α = 0` (`quadratic_coeff_cancels`),
                the reason `R` is affine and not quadratic on each interval of (B.2).
* (B.2)         `R` is affine on each interval of (B.2), with slope and intercept computed
                from the five integer parts and the four branch choices (`RR_affine`,
                `RR_affine_on`), instantiated at each of the **143** intervals (`p3_0`, …,
                `p19_6`).
* (B.3), Table 3  the exact rational integral over a chain of pieces (`chain_integral`);
                the seventeen unit-interval rows of **Table 3** (`table3_3`, …,
                `table3_19`); and
                `∫_3^20 R(x)x^{-3}dx = 322437603634266857629/7535670527041937280000`
                = `Zeta5.I320`, i.e. **(5.18)** (`eq_5_18`).
* (5.8)–(5.10), §B.2, Table 4  the outer integrand (`R0`, `dRank`, `Tout`), its eleven
                affine pieces (`qout_0`, …, `qout_10`) and
                `I_out = ∫_{1/3}^{2λ} T(y) dy = 127751/96000` = `Zeta5.Iout` (`eq_5_10`).
* (5.14)        `-1/2 ≤ Q(x) ≤ 13/8` (`eq_5_14`), from `Zeta5.Tail.eq_5_14`.
* (5.16)–(5.17) the tail estimates, combined as `∫_20^M R x^{-3} ≤ …` (`eq_5_16_5_17`),
                from `Zeta5.Tail.tail_bound`: the two integrations by parts (5.15) on the
                finite interval `[20,M]`, plus the sup bounds `𝒞 ≤ 16` and `Q ≤ 13/8`.
                See its docstring for the verbatim paper statement.
* (5.19)–(5.21), §B.3  the assembly `I_out + 6λ/M + ∫_3^M R x^{-3} ≤ A_M` (`eq_5_16_5_18`,
                which is `Zeta5.eq_5_16_5_18` of `Interface.lean` verbatim — see
                `Zeta5/AppendixBCheck.lean`), and the printed constants of §B.3:
                `A_200`, `A_100000` and both exact margins of (7.2).

`Zeta5/AppendixBCheck.lean` type-checks this file's `eq_5_16_5_18` against the interface
statement it discharges, and prints the axiom dependencies.

This file imports only `Zeta5.Basic` and `Zeta5.Tail`, so `Interface.lean` may import it
without a cycle.  `Zeta5/Tail.lean` holds the §5.3 analysis — the two integrations by parts
of (5.15) and the sup bounds — against an abstract remainder `Q`; it is applied here to the
concrete `Qcl` of (5.13).
-/
import Zeta5.Basic
import Zeta5.Tail

namespace Zeta5.AppendixB

open MeasureTheory intervalIntegral Set

noncomputable section

/-! ## §0.  Two elementary integrals

`∫_l^r (a x + b) x^{-3} dx` for `0 < l ≤ r`, and the integral of an indicator on `(0,1/2)`.
These are the only two integrations the appendix performs. -/

/-- The antiderivative of `(a x + b)/x³`. -/
def aff_prim (a b x : ℝ) : ℝ := -(2 * a * x + b) / (2 * x ^ 2)

lemma hasDerivAt_aff_prim (a b x : ℝ) (hx : x ≠ 0) :
    HasDerivAt (aff_prim a b) ((a * x + b) / x ^ 3) x := by
  have hu : HasDerivAt (fun y : ℝ => -(2 * a * y + b)) (-(2 * a)) x := by
    have h := ((hasDerivAt_id x).const_mul (2 * a)).add_const b
    simp only [id_eq, mul_one] at h
    exact h.neg
  have hv : HasDerivAt (fun y : ℝ => 2 * y ^ 2) (4 * x) x := by
    have h := (hasDerivAt_pow 2 x).const_mul (2 : ℝ)
    norm_num at h
    convert h using 1
    ring
  have hne : (2 : ℝ) * x ^ 2 ≠ 0 := by positivity
  have h := hu.div hv hne
  refine h.congr_deriv ?_
  field_simp
  ring

/-- `∫_l^r (a x + b) x^{-3} dx = a(1/l - 1/r) + (b/2)(1/l² - 1/r²)` for `0 < l ≤ r`.

This is the only antiderivative Appendix B needs: `R` is affine on each of its pieces and
the weight is `x^{-3}`. -/
theorem integral_affine_div_cube (a b l r : ℝ) (hl : 0 < l) (hlr : l ≤ r) :
    (∫ x in l..r, (a * x + b) / x ^ 3)
      = a * (1 / l - 1 / r) + b / 2 * (1 / l ^ 2 - 1 / r ^ 2) := by
  have hr : (0:ℝ) < r := lt_of_lt_of_le hl hlr
  have hmem : ∀ x ∈ uIcc l r, x ≠ 0 := by
    intro x hx
    rw [Set.uIcc_of_le hlr] at hx
    exact ne_of_gt (lt_of_lt_of_le hl hx.1)
  have hderiv : ∀ x ∈ uIcc l r, HasDerivAt (aff_prim a b) ((a * x + b) / x ^ 3) x :=
    fun x hx => hasDerivAt_aff_prim a b x (hmem x hx)
  have hcont : ContinuousOn (fun x : ℝ => (a * x + b) / x ^ 3) (uIcc l r) := by
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro x hx; exact pow_ne_zero _ (hmem x hx)
  have hint : IntervalIntegrable (fun x : ℝ => (a * x + b) / x ^ 3) volume l r :=
    hcont.intervalIntegrable
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp only [aff_prim]
  field_simp
  ring

/-- `∫_0^{1/2} 1_{z < c} dz = c` for `0 ≤ c ≤ 1/2`. -/
theorem integral_indicator_half (c : ℝ) (h0 : 0 ≤ c) (h1 : c ≤ 1 / 2) :
    (∫ z in (0:ℝ)..(1/2 : ℝ), (if z < c then (1:ℝ) else 0)) = c := by
  have hle : (0:ℝ) ≤ 1/2 := by norm_num
  rw [intervalIntegral.integral_of_le hle]
  have hfun : (fun z : ℝ => if z < c then (1:ℝ) else 0)
      = Set.indicator (Set.Iio c) (fun _ => (1:ℝ)) := by
    funext z; simp [Set.indicator_apply]
  rw [hfun, MeasureTheory.setIntegral_indicator measurableSet_Iio]
  have hset : Set.Ioc (0:ℝ) (1/2) ∩ Set.Iio c = Set.Ioo 0 c := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Iio, Set.mem_Ioo]
    constructor
    · rintro ⟨⟨hz0, _⟩, hzc⟩; exact ⟨hz0, hzc⟩
    · rintro ⟨hz0, hzc⟩; exact ⟨⟨hz0, le_trans (le_of_lt hzc) h1⟩, hzc⟩
  rw [hset, MeasureTheory.setIntegral_const, MeasureTheory.measureReal_def, Real.volume_Ioo]
  simp [ENNReal.toReal_ofReal h0]

lemma intervalIntegrable_ind (c : ℝ) :
    IntervalIntegrable (fun z : ℝ => if z < c then (1:ℝ) else 0) volume 0 (1/2) := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]
  have hmeas : Measurable (fun z : ℝ => if z < c then (1:ℝ) else 0) :=
    Measurable.ite (measurableSet_lt measurable_id measurable_const)
      measurable_const measurable_const
  refine MeasureTheory.Integrable.mono' (g := fun _ => (1:ℝ)) ?_ hmeas.aestronglyMeasurable ?_
  · exact MeasureTheory.integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  · filter_upwards with z
    by_cases h : z < c <;> simp [h]

/-- The product of two `Iio`-indicators is the indicator of the smaller. -/
lemma ind_mul_ind (z a b : ℝ) :
    (if z < a then (1:ℝ) else 0) * (if z < b then (1:ℝ) else 0)
      = if z < min a b then (1:ℝ) else 0 := by
  by_cases ha : z < a <;> by_cases hb : z < b <;>
    simp [ha, hb, lt_min_iff, and_comm]

/-- The one integral Appendix B.1 performs: the `z`-integral of a function that is an
affine-in-indicators expression, `∫_0^{1/2}`. -/
lemma integral_expand (c0 c1 c2 c3 df dg : ℝ)
    (hdf : 0 ≤ df) (hdf2 : df ≤ 1/2) (hdg : 0 ≤ dg) (hdg2 : dg ≤ 1/2) :
    (∫ z in (0:ℝ)..(1/2 : ℝ),
        (c0 + c1 * (if z < dg then (1:ℝ) else 0) + c2 * (if z < df then (1:ℝ) else 0)
          + c3 * ((if z < dg then (1:ℝ) else 0) * (if z < df then (1:ℝ) else 0))))
      = c0 * (1/2) + c1 * dg + c2 * df + c3 * min dg df := by
  have hmin0 : 0 ≤ min dg df := le_min hdg hdf
  have hmin2 : min dg df ≤ 1/2 := le_trans (min_le_left _ _) hdg2
  simp only [ind_mul_ind]
  have i1 := (intervalIntegrable_ind dg).const_mul c1
  have i2 := (intervalIntegrable_ind df).const_mul c2
  have i3 := (intervalIntegrable_ind (min dg df)).const_mul c3
  have i0 : IntervalIntegrable (fun _ : ℝ => c0) volume 0 (1/2) := intervalIntegrable_const
  rw [intervalIntegral.integral_add (((i0.add i1)).add i2) i3,
      intervalIntegral.integral_add (i0.add i1) i2,
      intervalIntegral.integral_add i0 i1,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const,
      integral_indicator_half dg hdg hdg2, integral_indicator_half df hdf hdf2,
      integral_indicator_half _ hmin0 hmin2]
  simp only [smul_eq_mul, sub_zero]
  ring

/-! ## §B.1.  The formula for `ℓ` by fractional parts (the display before (B.1))

For `0 ≤ u < 1` set `d₀(u) = min(u, 1-u)` and `e(u) = 1` if `u ≤ 1/2`, `-1` otherwise.
With `f = {x}`, for every `z ∈ (0,1/2)` other than `z = d₀(f)`,

`ℓ(x,z) - 2x = e(f)(1_{z < d₀(f)} - 2 d₀(f))`. -/

/-- `d₀(u) = min(u, 1-u)`, p. 26. -/
def d0 (u : ℝ) : ℝ := min u (1 - u)

/-- `e(u) = 1` for `u ≤ 1/2`, `-1` for `u > 1/2`, p. 26. -/
def e0 (u : ℝ) : ℝ := if u ≤ 1/2 then 1 else -1

lemma d0_nonneg {u : ℝ} (h : 0 ≤ u) (h1 : u < 1) : 0 ≤ d0 u :=
  le_min h (by linarith)

lemma d0_le_half (u : ℝ) : d0 u ≤ 1/2 := by
  rcases le_total u (1/2) with h | h
  · exact le_trans (min_le_left _ _) h
  · exact le_trans (min_le_right _ _) (by linarith)

lemma d0_fract_nonneg (x : ℝ) : 0 ≤ d0 (Int.fract x) :=
  d0_nonneg (Int.fract_nonneg x) (Int.fract_lt_one x)

lemma e0_sq (u : ℝ) : e0 u * e0 u = 1 := by
  unfold e0; split <;> norm_num

/-- The display before (B.1) (p. 26): for almost every `z ∈ (0,1/2)`,
`ℓ(x,z) = 2x + e({x})(1_{z < d₀({x})} - 2 d₀({x}))`. -/
theorem ellR_eq (x z : ℝ) (hz0 : 0 < z) (hz1 : z < 1/2) (hne : z ≠ d0 (Int.fract x)) :
    ellR x z
      = 2 * x + e0 (Int.fract x) *
          ((if z < d0 (Int.fract x) then (1:ℝ) else 0) - 2 * d0 (Int.fract x)) := by
  have hf0 : (0:ℝ) ≤ Int.fract x := Int.fract_nonneg x
  have hf1 : Int.fract x < 1 := Int.fract_lt_one x
  have hx : (⌊x⌋ : ℝ) + Int.fract x = x := Int.floor_add_fract x
  rcases le_or_gt (Int.fract x) (1/2) with hA | hB
  · have hd : d0 (Int.fract x) = Int.fract x := min_eq_left (by linarith)
    have he : e0 (Int.fract x) = 1 := ite_eq_left hA
    rw [hd] at hne ⊢
    rw [he]
    rcases lt_or_gt_of_ne hne with hzf | hzf
    · have h1 : ⌊x - z⌋ = ⌊x⌋ := by
        rw [Int.floor_eq_iff]; constructor <;> [linarith; linarith]
      have h2 : ⌊x + z⌋ = ⌊x⌋ := by
        rw [Int.floor_eq_iff]; constructor <;> [linarith; linarith]
      simp only [ellR, h1, h2, ite_eq_left hzf]
      linarith
    · have h1 : ⌊x - z⌋ = ⌊x⌋ - 1 := by
        rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
      have h2 : ⌊x + z⌋ = ⌊x⌋ := by
        rw [Int.floor_eq_iff]; constructor <;> [linarith; linarith]
      simp only [ellR, h1, h2, ite_eq_right (not_lt.2 (le_of_lt hzf))]
      push_cast
      linarith
  · have hd : d0 (Int.fract x) = 1 - Int.fract x := min_eq_right (by linarith)
    have he : e0 (Int.fract x) = -1 := ite_eq_right (by push Not; linarith)
    rw [hd] at hne ⊢
    rw [he]
    rcases lt_or_gt_of_ne hne with hzf | hzf
    · have h1 : ⌊x - z⌋ = ⌊x⌋ := by
        rw [Int.floor_eq_iff]; constructor <;> [linarith; linarith]
      have h2 : ⌊x + z⌋ = ⌊x⌋ := by
        rw [Int.floor_eq_iff]; constructor <;> [linarith; linarith]
      simp only [ellR, h1, h2, ite_eq_left hzf]
      linarith
    · have h1 : ⌊x - z⌋ = ⌊x⌋ := by
        rw [Int.floor_eq_iff]; constructor <;> [linarith; linarith]
      have h2 : ⌊x + z⌋ = ⌊x⌋ + 1 := by
        rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
      simp only [ellR, h1, h2, ite_eq_right (not_lt.2 (le_of_lt hzf))]
      push_cast
      linarith

/-! ## §B.1.  (B.1) and the closed form of `Γ`

The `z`-integral in (5.4) is evaluated by the two identities (B.1).  Writing
`A(z) = ℓ(x,z) - 2x`, `B(z) = ℓ(αx,z) - 2αx` (the notation of §5.3), the integrand of (5.4)
is `(U - 3e_g B̂)(V + 3e_g B̂ - e_f Â)` with `Â, B̂` the two indicators, and the integral is
the displayed rational expression.  Compare `∫B² = d_g(1-2d_g)` and
`∫AB = e_f e_g (min(d_f,d_g) - 2 d_f d_g)` of (B.1): the present form is the same statement,
expanded. -/

/-- `d₀({x})`. -/
def dF (x : ℝ) : ℝ := d0 (Int.fract x)
/-- `e({x})`. -/
def eF (x : ℝ) : ℝ := e0 (Int.fract x)
/-- `d₀({αx})`. -/
def dG (x : ℝ) : ℝ := d0 (Int.fract ((alpha : ℝ) * x))
/-- `e({αx})`. -/
def eG (x : ℝ) : ℝ := e0 (Int.fract ((alpha : ℝ) * x))

/-- `U = T - 6αx + 6 e_g d_g`: the part of `T - b(x,z)` not carried by the indicator. -/
def UU (x : ℝ) : ℝ := TR x - 6 * (alpha : ℝ) * x + 6 * eG x * dG x
/-- `V = T + 6αx - 2x - 5 - 6 e_g d_g + 2 e_f d_f`. -/
def VV (x : ℝ) : ℝ :=
  TR x + 6 * (alpha : ℝ) * x - 2 * x - 5 - 6 * eG x * dG x + 2 * eF x * dF x

lemma dF_nonneg (x : ℝ) : 0 ≤ dF x := d0_fract_nonneg x
lemma dF_le (x : ℝ) : dF x ≤ 1/2 := d0_le_half _
lemma dG_nonneg (x : ℝ) : 0 ≤ dG x := d0_fract_nonneg _
lemma dG_le (x : ℝ) : dG x ≤ 1/2 := d0_le_half _

/-- **(5.4) evaluated**: the closed form of `Γ(x)`.  This is (B.1) in expanded form:
the `z`-integral of (5.4) has an integrand that, off the two breakpoints `z = d_f`, `z = d_g`,
is a polynomial in the two indicators `1_{z<d_f}`, `1_{z<d_g}`, and the three integrals
`∫1 = 1/2`, `∫1_{z<c} = c`, `∫1_{z<c}1_{z<c'} = min(c,c')` finish it. -/
theorem Gam_eq (x : ℝ) :
    Gam x = UU x * VV x * (1/2)
        + (3 * eG x * UU x - 3 * eG x * VV x - 9) * dG x
        + (-(eF x * UU x)) * dF x
        + (3 * eF x * eG x) * min (dG x) (dF x)
        + sR x * (2 * TR x - qR x - 5) + max 0 (sR x - nPlus x) := by
  have hcong : (∫ z in (0 : ℝ)..(1 / 2 : ℝ),
        (TR x - bR x z) * (TR x + bR x z - ellR x z - 5))
      = ∫ z in (0 : ℝ)..(1 / 2 : ℝ),
          (UU x * VV x
            + (3 * eG x * UU x - 3 * eG x * VV x - 9) * (if z < dG x then (1:ℝ) else 0)
            + (-(eF x * UU x)) * (if z < dF x then (1:ℝ) else 0)
            + (3 * eF x * eG x)
                * ((if z < dG x then (1:ℝ) else 0) * (if z < dF x then (1:ℝ) else 0))) := by
    refine intervalIntegral.integral_congr_ae ?_
    have h1 : ∀ᵐ z : ℝ, z ≠ dF x := by
      rw [MeasureTheory.ae_iff]
      simp
    have h2 : ∀ᵐ z : ℝ, z ≠ dG x := by
      rw [MeasureTheory.ae_iff]
      simp
    have h3 : ∀ᵐ z : ℝ, z ≠ (1/2 : ℝ) := by
      rw [MeasureTheory.ae_iff]
      simp
    filter_upwards [h1, h2, h3] with z hz1 hz2 hz3 hzmem
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1/2)] at hzmem
    have hzlt : z < 1/2 := lt_of_le_of_ne hzmem.2 hz3
    have hf := ellR_eq x z hzmem.1 hzlt hz1
    have hg := ellR_eq ((alpha : ℝ) * x) z hzmem.1 hzlt hz2
    have hegsq : eG x * eG x = 1 := e0_sq _
    have hIg : (if z < dG x then (1:ℝ) else 0) * (if z < dG x then (1:ℝ) else 0)
        = (if z < dG x then (1:ℝ) else 0) := by
      by_cases h : z < dG x <;> simp [h]
    show (TR x - bR x z) * (TR x + bR x z - ellR x z - 5) = _
    rw [bR, hg, hf]
    simp only [UU, VV, eF, eG, dF, dG] at hegsq ⊢
    clear hIg
    by_cases hgz : z < d0 (Int.fract ((alpha : ℝ) * x)) <;>
      by_cases hfz : z < d0 (Int.fract x) <;>
        simp only [hgz, hfz, ite_true, ite_false] <;>
        first
          | linear_combination (-9 : ℝ) * hegsq
          | ring
  rw [Gam, hcong,
    integral_expand (UU x * VV x) (3 * eG x * UU x - 3 * eG x * VV x - 9)
      (-(eF x * UU x)) (3 * eF x * eG x) (dF x) (dG x)
      (dF_nonneg x) (dF_le x) (dG_nonneg x) (dG_le x)]

/-! ## §B.1 continued.  `R` is affine on each interval of (B.2)

On an interval of (B.2) none of `x`, `αx`, `2x`, `2Hx`, `2λx` crosses an integer and none of
the branches of `d₀`, `e`, `min`, `(·)₊` changes.  Every ingredient of `Γ` and `𝒩` is then a
*quadratic* polynomial in `x`, and `R = -Γ - 𝒩` is **affine**: the `x²` terms cancel, which is
exactly the identity `quadratic_coeff_cancels` of §B.1. -/

/-- §B.1: `2λ - 12λα + 2(H² - H - λ²) - 18α² + 6α = 0`.  The paper's reason why `R` is affine,
and not merely quadratic, on each interval of (B.2). -/
theorem quadratic_coeff_cancels :
    2 * lam - 12 * lam * alpha + 2 * (Hcst ^ 2 - Hcst - lam ^ 2) - 18 * alpha ^ 2 + 6 * alpha
      = 0 := by
  norm_num [lam, alpha, Hcst]

lemma TR_eq {x : ℝ} {k : ℤ} (h1 : (k:ℝ) ≤ 2 * (Hcst:ℝ) * x) (h2 : 2 * (Hcst:ℝ) * x < k + 1) :
    TR x = (k : ℝ) := by
  rw [TR, Int.floor_eq_iff.2 ⟨h1, h2⟩]

lemma qR_eq {x : ℝ} {j : ℤ} (h1 : (j:ℝ) ≤ 2 * x) (h2 : 2 * x < j + 1) : qR x = (j : ℝ) := by
  rw [qR, Int.floor_eq_iff.2 ⟨h1, h2⟩]

lemma fract_eq {x : ℝ} {n : ℤ} (h1 : (n:ℝ) ≤ x) (h2 : x < n + 1) : Int.fract x = x - n := by
  rw [Int.fract, Int.floor_eq_iff.2 ⟨h1, h2⟩]

/-- `e({x}) = 1` and `d₀({x}) = x - n` when `n ≤ x ≤ n + 1/2`. -/
lemma e_d_of_le {x : ℝ} {n : ℤ} (h1 : (n:ℝ) ≤ x) (h2 : x ≤ (n:ℝ) + 1/2) :
    e0 (Int.fract x) = 1 ∧ d0 (Int.fract x) = x - n := by
  have hfr : Int.fract x = x - n := fract_eq h1 (by linarith)
  refine ⟨?_, ?_⟩
  · rw [hfr, e0, ite_eq_left (by linarith)]
  · rw [hfr, d0, min_eq_left (by linarith)]

/-- `e({x}) = -1` and `d₀({x}) = n + 1 - x` when `n + 1/2 < x < n + 1`. -/
lemma e_d_of_gt {x : ℝ} {n : ℤ} (h1 : (n:ℝ) + 1/2 < x) (h2 : x < (n:ℝ) + 1) :
    e0 (Int.fract x) = -1 ∧ d0 (Int.fract x) = (n:ℝ) + 1 - x := by
  have hfr : Int.fract x = x - n := fract_eq (by linarith) h2
  refine ⟨?_, ?_⟩
  · rw [hfr, e0, ite_eq_right (by push Not; linarith)]
  · rw [hfr, d0, min_eq_right (by linarith)]; ring

/-- The affine slope of `R` on an interval of (B.2), from the integer parts and the branches. -/
def affA (n m k j i ef eg : ℤ) (dm ts : Bool) : ℝ :=
  (4 * (lam:ℝ) - 2 * (lam:ℝ) * n + 12 * (lam:ℝ) * m)
    + ((Hcst:ℝ) * ((j:ℝ) - k) - (k:ℝ) * ((Hcst:ℝ) - 1))
    + (if ts then -((Hcst:ℝ) - 1) else 0)
    + ((lam:ℝ) + 2 * (lam:ℝ) * i)
    + (9 * (eg:ℝ) * (alpha:ℝ) - 36 * (eg:ℝ) * (alpha:ℝ) * ((1 - (eg:ℝ))/2 - (eg:ℝ) * m))
    + 6 * ((eg:ℝ) * ((1 - (eg:ℝ))/2 - (eg:ℝ) * m)
        + (ef:ℝ) * (alpha:ℝ) * ((1 - (ef:ℝ))/2 - (ef:ℝ) * n))
    + (if dm then -3 * (eg:ℝ) else -3 * (ef:ℝ) * (alpha:ℝ))

/-- The affine intercept of `R` on an interval of (B.2). -/
def affB (n m k j i ef eg : ℤ) (dm ts : Bool) : ℝ :=
  -((k:ℝ) * ((j:ℝ) - k)) / 2
    + (if ts then -((j:ℝ) - k) / 2 else 0)
    - ((i:ℝ) + (i:ℝ)^2) / 2
    + 9 * ((1 - (eg:ℝ))/2 - (eg:ℝ) * m) - 18 * ((1 - (eg:ℝ))/2 - (eg:ℝ) * m)^2
    + 6 * (ef:ℝ) * (eg:ℝ) * ((1 - (ef:ℝ))/2 - (ef:ℝ) * n) * ((1 - (eg:ℝ))/2 - (eg:ℝ) * m)
    + (if dm then -3 * (ef:ℝ) * (eg:ℝ) * ((1 - (ef:ℝ))/2 - (ef:ℝ) * n)
        else -3 * (ef:ℝ) * (eg:ℝ) * ((1 - (eg:ℝ))/2 - (eg:ℝ) * m))

/-- **`R` is affine on each interval of (B.2)**, with slope `affA` and intercept `affB`.

The hypotheses are exactly the statement that `x` lies strictly inside one of the `143`
intervals: the five integer parts `⌊x⌋, ⌊αx⌋, ⌊2Hx⌋, ⌊2x⌋, ⌊2λx⌋` are `n, m, k, j, i`, the
two signs `e({x}), e({αx})` are `ef, eg`, and the two remaining branches — which of `d₀({x})`,
`d₀({αx})` is smaller, and the sign of `τ - σ` — are `dm` and `ts`. -/
theorem RR_affine (x : ℝ) (n m k j i ef eg : ℤ) (dm ts : Bool)
    (hn : (n:ℝ) ≤ x) (hn' : x < (n:ℝ) + 1)
    (hm : (m:ℝ) ≤ (alpha:ℝ) * x) (hm' : (alpha:ℝ) * x < (m:ℝ) + 1)
    (hk : (k:ℝ) ≤ 2 * (Hcst:ℝ) * x) (hk' : 2 * (Hcst:ℝ) * x < (k:ℝ) + 1)
    (hj : (j:ℝ) ≤ 2 * x) (hj' : 2 * x < (j:ℝ) + 1)
    (hi : (i:ℝ) ≤ 2 * (lam:ℝ) * x) (hi' : 2 * (lam:ℝ) * x < (i:ℝ) + 1)
    (hef : (ef = 1 ∧ x ≤ (n:ℝ) + 1/2) ∨ (ef = -1 ∧ (n:ℝ) + 1/2 < x))
    (heg : (eg = 1 ∧ (alpha:ℝ) * x ≤ (m:ℝ) + 1/2)
            ∨ (eg = -1 ∧ (m:ℝ) + 1/2 < (alpha:ℝ) * x))
    (hdm : if dm then (ef:ℝ) * x + ((1 - (ef:ℝ))/2 - (ef:ℝ) * n)
                      ≤ (eg:ℝ) * (alpha:ℝ) * x + ((1 - (eg:ℝ))/2 - (eg:ℝ) * m)
           else (eg:ℝ) * (alpha:ℝ) * x + ((1 - (eg:ℝ))/2 - (eg:ℝ) * m)
                      ≤ (ef:ℝ) * x + ((1 - (ef:ℝ))/2 - (ef:ℝ) * n))
    (hts : if ts then (0:ℝ) ≤ 2 * ((Hcst:ℝ) - 1) * x + (j:ℝ) - k
           else 2 * ((Hcst:ℝ) - 1) * x + (j:ℝ) - k ≤ 0) :
    RR x = affA n m k j i ef eg dm ts * x + affB n m k j i ef eg dm ts := by
  have hTR : TR x = (k : ℝ) := TR_eq hk hk'
  have hqR : qR x = (j : ℝ) := qR_eq hj hj'
  have hfln : ⌊x⌋ = n := Int.floor_eq_iff.2 ⟨hn, hn'⟩
  have hflm : ⌊(alpha:ℝ) * x⌋ = m := Int.floor_eq_iff.2 ⟨hm, hm'⟩
  have hfli : ⌊2 * ((lam:ℝ) * x)⌋ = i := by
    rw [← mul_assoc]; exact Int.floor_eq_iff.2 ⟨hi, hi'⟩
  have hefv : (ef:ℝ) = 1 ∨ (ef:ℝ) = -1 := by
    rcases hef with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> norm_num
  have hegv : (eg:ℝ) = 1 ∨ (eg:ℝ) = -1 := by
    rcases heg with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> norm_num
  -- the two signs and the two `d₀`
  have hF : eF x = (ef:ℝ) ∧ dF x = (ef:ℝ) * x + ((1 - (ef:ℝ))/2 - (ef:ℝ) * n) := by
    rcases hef with ⟨rfl, h⟩ | ⟨rfl, h⟩
    · obtain ⟨he, hd⟩ := e_d_of_le hn h
      refine ⟨by rw [eF, he]; norm_num, by rw [dF, hd]; push_cast; ring⟩
    · obtain ⟨he, hd⟩ := e_d_of_gt h hn'
      refine ⟨by rw [eF, he]; norm_num, by rw [dF, hd]; push_cast; ring⟩
  have hG : eG x = (eg:ℝ) ∧ dG x = (eg:ℝ) * (alpha:ℝ) * x + ((1 - (eg:ℝ))/2 - (eg:ℝ) * m) := by
    rcases heg with ⟨rfl, h⟩ | ⟨rfl, h⟩
    · obtain ⟨he, hd⟩ := e_d_of_le hm h
      refine ⟨by rw [eG, he]; norm_num, by rw [dG, hd]; push_cast; ring⟩
    · obtain ⟨he, hd⟩ := e_d_of_gt h hm'
      refine ⟨by rw [eG, he]; norm_num, by rw [dG, hd]; push_cast; ring⟩
  obtain ⟨heF, hdF⟩ := hF
  obtain ⟨heG, hdG⟩ := hG
  -- the `min` branch
  have hmin : min (dG x) (dF x)
      = if dm then (ef:ℝ) * x + ((1 - (ef:ℝ))/2 - (ef:ℝ) * n)
        else (eg:ℝ) * (alpha:ℝ) * x + ((1 - (eg:ℝ))/2 - (eg:ℝ) * m) := by
    rw [hdF, hdG]
    cases dm with
    | false => simp only [Bool.false_eq_true, ite_false] at hdm ⊢; exact min_eq_left hdm
    | true => simp only [ite_true] at hdm ⊢; exact min_eq_right hdm
  -- the positive part
  have hsR : sR x = (Hcst:ℝ) * x - (k:ℝ) / 2 := by rw [sR, hTR]
  have hsn : sR x - nPlus x = ((Hcst:ℝ) - 1) * x + ((j:ℝ) - k) / 2 := by
    rw [sR, nPlus, hTR, hqR]; ring
  have hmax : max 0 (sR x - nPlus x)
      = if ts then ((Hcst:ℝ) - 1) * x + ((j:ℝ) - k) / 2 else 0 := by
    rw [hsn]
    cases ts with
    | false =>
      simp only [Bool.false_eq_true, ite_false] at hts ⊢
      exact max_eq_left (by linarith)
    | true =>
      simp only [ite_true] at hts ⊢
      exact max_eq_right (by linarith)
  -- assemble
  rw [RR, Gam_eq, NR, JR]
  simp only [UU, VV]
  rw [hmin, hmax, hsR]
  simp only [hdF, hdG, heF, heG, hTR, hqR, hfln, hflm, hfli, affA, affB]
  rcases hefv with h1 | h1 <;> rcases hegv with h2 | h2 <;> cases dm <;> cases ts <;>
    · rw [h1, h2]
      simp only [Bool.false_eq_true, ite_true, ite_false]
      push_cast [lam, alpha, Hcst]
      ring

/-! ## §B.2 (B.2)–(B.3).  From the pieces to the integral

`Cert` bundles the sixteen rational certificates that place `x` strictly inside one interval
of (B.2) and fix the branches; it is a decidable statement about rational numbers, discharged
for each of the `143` intervals by `norm_num`. -/

/-- An affine inequality valid at both endpoints of an interval is valid inside it. -/
lemma affine_le_of_endpoints {p q c d l r x : ℝ}
    (hl : p * l + c ≤ q * l + d) (hr : p * r + c ≤ q * r + d) (h1 : l ≤ x) (h2 : x ≤ r) :
    p * x + c ≤ q * x + d := by
  rcases le_or_gt p q with h | h
  · have hmul : (q - p) * l ≤ (q - p) * x :=
      mul_le_mul_of_nonneg_left h1 (by linarith)
    linarith
  · have hmul : (q - p) * r ≤ (q - p) * x :=
      mul_le_mul_of_nonpos_left h2 (by linarith)
    linarith

/-- The certificate of one interval of (B.2): the integer parts and the branch choices,
verified at the two endpoints. -/
def Cert (l r : ℝ) (n m k j i ef eg : ℤ) (dm ts : Bool) (A B : ℝ) : Prop :=
  ((n:ℝ) ≤ l ∧ r ≤ (n:ℝ) + 1)
  ∧ ((m:ℝ) ≤ (alpha:ℝ) * l ∧ (alpha:ℝ) * r ≤ (m:ℝ) + 1)
  ∧ ((k:ℝ) ≤ 2 * (Hcst:ℝ) * l ∧ 2 * (Hcst:ℝ) * r ≤ (k:ℝ) + 1)
  ∧ ((j:ℝ) ≤ 2 * l ∧ 2 * r ≤ (j:ℝ) + 1)
  ∧ ((i:ℝ) ≤ 2 * (lam:ℝ) * l ∧ 2 * (lam:ℝ) * r ≤ (i:ℝ) + 1)
  ∧ ((ef = 1 ∧ r ≤ (n:ℝ) + 1/2) ∨ (ef = -1 ∧ (n:ℝ) + 1/2 ≤ l))
  ∧ ((eg = 1 ∧ (alpha:ℝ) * r ≤ (m:ℝ) + 1/2) ∨ (eg = -1 ∧ (m:ℝ) + 1/2 ≤ (alpha:ℝ) * l))
  ∧ (if dm then
        ((ef:ℝ) * l + ((1 - (ef:ℝ))/2 - (ef:ℝ) * n)
            ≤ (eg:ℝ) * (alpha:ℝ) * l + ((1 - (eg:ℝ))/2 - (eg:ℝ) * m))
        ∧ ((ef:ℝ) * r + ((1 - (ef:ℝ))/2 - (ef:ℝ) * n)
            ≤ (eg:ℝ) * (alpha:ℝ) * r + ((1 - (eg:ℝ))/2 - (eg:ℝ) * m))
      else
        ((eg:ℝ) * (alpha:ℝ) * l + ((1 - (eg:ℝ))/2 - (eg:ℝ) * m)
            ≤ (ef:ℝ) * l + ((1 - (ef:ℝ))/2 - (ef:ℝ) * n))
        ∧ ((eg:ℝ) * (alpha:ℝ) * r + ((1 - (eg:ℝ))/2 - (eg:ℝ) * m)
            ≤ (ef:ℝ) * r + ((1 - (ef:ℝ))/2 - (ef:ℝ) * n)))
  ∧ (if ts then (0:ℝ) ≤ 2 * ((Hcst:ℝ) - 1) * l + (j:ℝ) - k
        ∧ (0:ℝ) ≤ 2 * ((Hcst:ℝ) - 1) * r + (j:ℝ) - k
      else 2 * ((Hcst:ℝ) - 1) * l + (j:ℝ) - k ≤ 0
        ∧ 2 * ((Hcst:ℝ) - 1) * r + (j:ℝ) - k ≤ 0)
  ∧ A = affA n m k j i ef eg dm ts ∧ B = affB n m k j i ef eg dm ts

/-- From the certificate of an interval of (B.2): `R` is affine there. -/
theorem RR_affine_on {l r : ℝ} {n m k j i ef eg : ℤ} {dm ts : Bool} {A B : ℝ}
    (h : Cert l r n m k j i ef eg dm ts A B) :
    ∀ x : ℝ, l < x → x < r → RR x = A * x + B := by
  obtain ⟨⟨c1, c2⟩, ⟨c3, c4⟩, ⟨c5, c6⟩, ⟨c7, c8⟩, ⟨c9, c10⟩, cef, ceg, cdm, cts, cA, cB⟩ := h
  have hal : (0:ℝ) < (alpha:ℝ) := by norm_num [alpha]
  have hlamp : (0:ℝ) < (lam:ℝ) := by norm_num [lam]
  have hHp : (0:ℝ) < (Hcst:ℝ) := by norm_num [Hcst]
  intro x hx1 hx2
  have mal : (alpha:ℝ) * l < (alpha:ℝ) * x := by nlinarith
  have mar : (alpha:ℝ) * x < (alpha:ℝ) * r := by nlinarith
  have mHl : 2 * (Hcst:ℝ) * l < 2 * (Hcst:ℝ) * x := by nlinarith
  have mHr : 2 * (Hcst:ℝ) * x < 2 * (Hcst:ℝ) * r := by nlinarith
  have mll : 2 * (lam:ℝ) * l < 2 * (lam:ℝ) * x := by nlinarith
  have mlr : 2 * (lam:ℝ) * x < 2 * (lam:ℝ) * r := by nlinarith
  rw [cA, cB]
  refine RR_affine x n m k j i ef eg dm ts (by linarith) (by linarith) (by linarith)
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    (by linarith) (by linarith) ?_ ?_ ?_ ?_
  · rcases cef with ⟨he, hb⟩ | ⟨he, hb⟩
    · exact Or.inl ⟨he, by linarith⟩
    · exact Or.inr ⟨he, by linarith⟩
  · rcases ceg with ⟨he, hb⟩ | ⟨he, hb⟩
    · exact Or.inl ⟨he, by linarith⟩
    · exact Or.inr ⟨he, by linarith⟩
  · cases dm with
    | false =>
      simp only [Bool.false_eq_true, ite_false] at cdm ⊢
      obtain ⟨u, v⟩ := cdm
      exact affine_le_of_endpoints u v hx1.le hx2.le
    | true =>
      simp only [ite_true] at cdm ⊢
      obtain ⟨u, v⟩ := cdm
      exact affine_le_of_endpoints u v hx1.le hx2.le
  · cases ts with
    | false =>
      simp only [Bool.false_eq_true, ite_false] at cts ⊢
      obtain ⟨u, v⟩ := cts
      have := affine_le_of_endpoints (p := 2 * ((Hcst:ℝ) - 1)) (q := 0)
        (c := (j:ℝ) - k) (d := 0) (by linarith) (by linarith) hx1.le hx2.le
      linarith
    | true =>
      simp only [ite_true] at cts ⊢
      obtain ⟨u, v⟩ := cts
      have := affine_le_of_endpoints (p := 0) (q := 2 * ((Hcst:ℝ) - 1))
        (c := 0) (d := (j:ℝ) - k) (by linarith) (by linarith) hx1.le hx2.le
      linarith

/-! ### Integrating `R x^{-3}` over a chain of pieces -/

/-- `R(x)/x³` is interval-integrable on a piece on which `R` is affine. -/
theorem piece_integrable {l r A B : ℝ} (hl : 0 < l) (hlr : l ≤ r)
    (hp : ∀ x : ℝ, l < x → x < r → RR x = A * x + B) :
    IntervalIntegrable (fun x => RR x / x ^ 3) volume l r := by
  have hcont : ContinuousOn (fun x : ℝ => (A * x + B) / x ^ 3) (uIcc l r) := by
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro y hy
    rw [Set.uIcc_of_le hlr] at hy
    exact pow_ne_zero _ (ne_of_gt (lt_of_lt_of_le hl hy.1))
  refine (hcont.intervalIntegrable).congr_uIoo ?_
  intro y hy
  rw [Set.uIoo_of_le hlr] at hy
  simp only [hp y hy.1 hy.2]

/-- The exact integral over a piece on which `R` is affine. -/
theorem piece_value {l r A B : ℝ} (hl : 0 < l) (hlr : l ≤ r)
    (hp : ∀ x : ℝ, l < x → x < r → RR x = A * x + B) :
    (∫ x in l..r, RR x / x ^ 3) = A * (1/l - 1/r) + B / 2 * (1/l^2 - 1/r^2) := by
  have hne : ∀ᵐ y : ℝ, y ≠ r := by
    rw [MeasureTheory.ae_iff]
    simp
  rw [intervalIntegral.integral_congr_ae
    (g := fun x : ℝ => (A * x + B) / x ^ 3) ?_, integral_affine_div_cube A B l r hl hlr]
  filter_upwards [hne] with y hyr hymem
  rw [Set.uIoc_of_le hlr] at hymem
  rw [hp y hymem.1 (lt_of_le_of_ne hymem.2 hyr)]

/-- The right endpoint of a chain of pieces starting at `lo`. -/
def chainEnd : ℝ → List (ℝ × ℝ × ℝ) → ℝ
  | lo, [] => lo
  | _, (r, _, _) :: ps => chainEnd r ps

/-- The exact value of `∫ R x^{-3}` over a chain of pieces, as (B.3). -/
def chainVal : ℝ → List (ℝ × ℝ × ℝ) → ℝ
  | _, [] => 0
  | lo, (r, A, B) :: ps => (A * (1/lo - 1/r) + B / 2 * (1/lo^2 - 1/r^2)) + chainVal r ps

/-- The hypothesis of `chain_integral`: each piece is positive, ordered, and carries an
affine formula for `R`. -/
def ChainOK : ℝ → List (ℝ × ℝ × ℝ) → Prop
  | _, [] => True
  | lo, (r, A, B) :: ps =>
      0 < lo ∧ lo ≤ r ∧ (∀ x : ℝ, lo < x → x < r → RR x = A * x + B) ∧ ChainOK r ps

/-- **(B.3)**: the integral of `R x^{-3}` over a chain of pieces is the corresponding
rational sum. -/
theorem chain_integral : ∀ (ps : List (ℝ × ℝ × ℝ)) (lo : ℝ), 0 < lo → ChainOK lo ps →
    IntervalIntegrable (fun x => RR x / x ^ 3) volume lo (chainEnd lo ps)
      ∧ (∫ x in lo..(chainEnd lo ps), RR x / x ^ 3) = chainVal lo ps := by
  intro ps
  induction ps with
  | nil =>
    intro lo _ _
    refine ⟨?_, ?_⟩
    · simp [chainEnd]
    · simp [chainEnd, chainVal]
  | cons p ps ih =>
    obtain ⟨r, A, B⟩ := p
    intro lo hlo hok
    obtain ⟨_, hlr, hp, hrest⟩ := hok
    have hr : 0 < r := lt_of_lt_of_le hlo hlr
    obtain ⟨i2, v2⟩ := ih r hr hrest
    have i1 := piece_integrable hlo hlr hp
    have v1 := piece_value hlo hlr hp
    refine ⟨?_, ?_⟩
    · simp only [chainEnd]
      exact i1.trans i2
    · simp only [chainEnd, chainVal]
      rw [← intervalIntegral.integral_add_adjacent_intervals i1 i2, v1, v2]


/-! ## §B.1/§B.2.  The 143 intervals of (B.2) and Table 3

Below, `p{j}_{i}` is the `i`-th interval of (B.2) inside `[j, j+1]`, with the slope and
intercept of `R` there; `table3_{j}` is the corresponding row of **Table 3** (p. 27).
The endpoints are exactly the `x ∈ (3,20)` with `cx ∈ ℤ` for some
`c ∈ {2, 2α, 2λ, 2H, 4α, 2(1-α), 2(1+α)}` (note `2λ = 2(1-α)`), together with `3` and `20`:
`143` intervals, as the paper states.  All of this is *computed*, not assumed. -/

/-! ### Table 3, row `j = 3`: the 10 intervals of (B.2) inside `[3,4]` -/

lemma p3_0 : ∀ x : ℝ, (3 : ℝ) < x → x < (70/23 : ℝ) →
    RR x = (18/5 : ℝ) * x + (-6 : ℝ) :=
  RR_affine_on (l := (3 : ℝ)) (r := (70/23 : ℝ)) (n := 3) (m := 0) (k := 6)
    (j := 6) (i := 5) (ef := 1) (eg := 1)
    (dm := true) (ts := true)
    (A := (18/5 : ℝ)) (B := (-6 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p3_1 : ∀ x : ℝ, (70/23 : ℝ) < x → x < (120/37 : ℝ) →
    RR x = (49/20 : ℝ) * x + (-5/2 : ℝ) :=
  RR_affine_on (l := (70/23 : ℝ)) (r := (120/37 : ℝ)) (n := 3) (m := 0) (k := 7)
    (j := 6) (i := 5) (ef := 1) (eg := 1)
    (dm := true) (ts := false)
    (A := (49/20 : ℝ)) (B := (-5/2 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p3_2 : ∀ x : ℝ, (120/37 : ℝ) < x → x < (140/43 : ℝ) →
    RR x = (283/40 : ℝ) * x + (-35/2 : ℝ) :=
  RR_affine_on (l := (120/37 : ℝ)) (r := (140/43 : ℝ)) (n := 3) (m := 0) (k := 7)
    (j := 6) (i := 6) (ef := 1) (eg := 1)
    (dm := false) (ts := false)
    (A := (283/40 : ℝ)) (B := (-35/2 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p3_3 : ∀ x : ℝ, (140/43 : ℝ) < x → x < (10/3 : ℝ) →
    RR x = (283/40 : ℝ) * x + (-35/2 : ℝ) :=
  RR_affine_on (l := (140/43 : ℝ)) (r := (10/3 : ℝ)) (n := 3) (m := 0) (k := 7)
    (j := 6) (i := 6) (ef := 1) (eg := 1)
    (dm := false) (ts := false)
    (A := (283/40 : ℝ)) (B := (-35/2 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p3_4 : ∀ x : ℝ, (10/3 : ℝ) < x → x < (80/23 : ℝ) →
    RR x = (277/40 : ℝ) * x + (-17 : ℝ) :=
  RR_affine_on (l := (10/3 : ℝ)) (r := (80/23 : ℝ)) (n := 3) (m := 0) (k := 7)
    (j := 6) (i := 6) (ef := 1) (eg := 1)
    (dm := false) (ts := true)
    (A := (277/40 : ℝ)) (B := (-17 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p3_5 : ∀ x : ℝ, (80/23 : ℝ) < x → x < (7/2 : ℝ) →
    RR x = (231/40 : ℝ) * x + (-13 : ℝ) :=
  RR_affine_on (l := (80/23 : ℝ)) (r := (7/2 : ℝ)) (n := 3) (m := 0) (k := 8)
    (j := 6) (i := 6) (ef := 1) (eg := 1)
    (dm := false) (ts := false)
    (A := (231/40 : ℝ)) (B := (-13 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p3_6 : ∀ x : ℝ, (7/2 : ℝ) < x → x < (160/43 : ℝ) →
    RR x = (271/40 : ℝ) * x + (-33/2 : ℝ) :=
  RR_affine_on (l := (7/2 : ℝ)) (r := (160/43 : ℝ)) (n := 3) (m := 0) (k := 8)
    (j := 7) (i := 6) (ef := -1) (eg := 1)
    (dm := false) (ts := true)
    (A := (271/40 : ℝ)) (B := (-33/2 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p3_7 : ∀ x : ℝ, (160/43 : ℝ) < x → x < (140/37 : ℝ) →
    RR x = (71/20 : ℝ) * x + (-9/2 : ℝ) :=
  RR_affine_on (l := (160/43 : ℝ)) (r := (140/37 : ℝ)) (n := 3) (m := 0) (k := 8)
    (j := 7) (i := 6) (ef := -1) (eg := 1)
    (dm := true) (ts := true)
    (A := (71/20 : ℝ)) (B := (-9/2 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p3_8 : ∀ x : ℝ, (140/37 : ℝ) < x → x < (90/23 : ℝ) →
    RR x = (27/5 : ℝ) * x + (-23/2 : ℝ) :=
  RR_affine_on (l := (140/37 : ℝ)) (r := (90/23 : ℝ)) (n := 3) (m := 0) (k := 8)
    (j := 7) (i := 7) (ef := -1) (eg := 1)
    (dm := true) (ts := true)
    (A := (27/5 : ℝ)) (B := (-23/2 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p3_9 : ∀ x : ℝ, (90/23 : ℝ) < x → x < (4 : ℝ) →
    RR x = (17/4 : ℝ) * x + (-7 : ℝ) :=
  RR_affine_on (l := (90/23 : ℝ)) (r := (4 : ℝ)) (n := 3) (m := 0) (k := 9)
    (j := 7) (i := 7) (ef := -1) (eg := 1)
    (dm := true) (ts := false)
    (A := (17/4 : ℝ)) (B := (-7 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

/-- **Table 3**, row `j = 3` (p. 27):
`∫_{3}^{4} R(x) x^(-3) dx = 26807/161280`. -/
theorem table3_3 :
    IntervalIntegrable (fun x => RR x / x ^ 3) volume (3:ℝ) (4:ℝ)
      ∧ (∫ x in (3:ℝ)..(4:ℝ), RR x / x ^ 3) = (26807/161280 : ℝ) := by
  have h := chain_integral [((70/23 : ℝ), (18/5 : ℝ), (-6 : ℝ)), ((120/37 : ℝ), (49/20 : ℝ), (-5/2 : ℝ)), ((140/43 : ℝ), (283/40 : ℝ), (-35/2 : ℝ)), ((10/3 : ℝ), (283/40 : ℝ), (-35/2 : ℝ)), ((80/23 : ℝ), (277/40 : ℝ), (-17 : ℝ)), ((7/2 : ℝ), (231/40 : ℝ), (-13 : ℝ)), ((160/43 : ℝ), (271/40 : ℝ), (-33/2 : ℝ)), ((140/37 : ℝ), (71/20 : ℝ), (-9/2 : ℝ)), ((90/23 : ℝ), (27/5 : ℝ), (-23/2 : ℝ)), ((4 : ℝ), (17/4 : ℝ), (-7 : ℝ))] (3:ℝ) (by norm_num)
    ⟨by norm_num, by norm_num, p3_0, by norm_num, by norm_num, p3_1, by norm_num, by norm_num, p3_2, by norm_num, by norm_num, p3_3, by norm_num, by norm_num, p3_4, by norm_num, by norm_num, p3_5, by norm_num, by norm_num, p3_6, by norm_num, by norm_num, p3_7, by norm_num, by norm_num, p3_8, by norm_num, by norm_num, p3_9, trivial⟩
  simp only [chainEnd] at h
  exact ⟨h.1, by rw [h.2]; norm_num [chainVal]⟩

/-! ### Table 3, row `j = 4`: the 8 intervals of (B.2) inside `[4,5]` -/

lemma p4_0 : ∀ x : ℝ, (4 : ℝ) < x → x < (180/43 : ℝ) →
    RR x = (17/5 : ℝ) * x + (-11 : ℝ) :=
  RR_affine_on (l := (4 : ℝ)) (r := (180/43 : ℝ)) (n := 4) (m := 0) (k := 9)
    (j := 8) (i := 7) (ef := 1) (eg := 1)
    (dm := true) (ts := true)
    (A := (17/5 : ℝ)) (B := (-11 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p4_1 : ∀ x : ℝ, (180/43 : ℝ) < x → x < (160/37 : ℝ) →
    RR x = (17/5 : ℝ) * x + (-11 : ℝ) :=
  RR_affine_on (l := (180/43 : ℝ)) (r := (160/37 : ℝ)) (n := 4) (m := 0) (k := 9)
    (j := 8) (i := 7) (ef := 1) (eg := 1)
    (dm := true) (ts := true)
    (A := (17/5 : ℝ)) (B := (-11 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p4_2 : ∀ x : ℝ, (160/37 : ℝ) < x → x < (100/23 : ℝ) →
    RR x = (321/40 : ℝ) * x + (-31 : ℝ) :=
  RR_affine_on (l := (160/37 : ℝ)) (r := (100/23 : ℝ)) (n := 4) (m := 0) (k := 9)
    (j := 8) (i := 8) (ef := 1) (eg := 1)
    (dm := false) (ts := true)
    (A := (321/40 : ℝ)) (B := (-31 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p4_3 : ∀ x : ℝ, (100/23 : ℝ) < x → x < (9/2 : ℝ) →
    RR x = (55/8 : ℝ) * x + (-26 : ℝ) :=
  RR_affine_on (l := (100/23 : ℝ)) (r := (9/2 : ℝ)) (n := 4) (m := 0) (k := 10)
    (j := 8) (i := 8) (ef := 1) (eg := 1)
    (dm := false) (ts := false)
    (A := (55/8 : ℝ)) (B := (-26 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p4_4 : ∀ x : ℝ, (9/2 : ℝ) < x → x < (200/43 : ℝ) →
    RR x = (63/8 : ℝ) * x + (-61/2 : ℝ) :=
  RR_affine_on (l := (9/2 : ℝ)) (r := (200/43 : ℝ)) (n := 4) (m := 0) (k := 10)
    (j := 9) (i := 8) (ef := -1) (eg := 1)
    (dm := false) (ts := true)
    (A := (63/8 : ℝ)) (B := (-61/2 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p4_5 : ∀ x : ℝ, (200/43 : ℝ) < x → x < (110/23 : ℝ) →
    RR x = (93/20 : ℝ) * x + (-31/2 : ℝ) :=
  RR_affine_on (l := (200/43 : ℝ)) (r := (110/23 : ℝ)) (n := 4) (m := 0) (k := 10)
    (j := 9) (i := 8) (ef := -1) (eg := 1)
    (dm := true) (ts := true)
    (A := (93/20 : ℝ)) (B := (-31/2 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p4_6 : ∀ x : ℝ, (110/23 : ℝ) < x → x < (180/37 : ℝ) →
    RR x = (7/2 : ℝ) * x + (-10 : ℝ) :=
  RR_affine_on (l := (110/23 : ℝ)) (r := (180/37 : ℝ)) (n := 4) (m := 0) (k := 11)
    (j := 9) (i := 8) (ef := -1) (eg := 1)
    (dm := true) (ts := false)
    (A := (7/2 : ℝ)) (B := (-10 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p4_7 : ∀ x : ℝ, (180/37 : ℝ) < x → x < (5 : ℝ) →
    RR x = (107/20 : ℝ) * x + (-19 : ℝ) :=
  RR_affine_on (l := (180/37 : ℝ)) (r := (5 : ℝ)) (n := 4) (m := 0) (k := 11)
    (j := 9) (i := 9) (ef := -1) (eg := 1)
    (dm := true) (ts := false)
    (A := (107/20 : ℝ)) (B := (-19 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

/-- **Table 3**, row `j = 4` (p. 27):
`∫_{4}^{5} R(x) x^(-3) dx = 37383/704000`. -/
theorem table3_4 :
    IntervalIntegrable (fun x => RR x / x ^ 3) volume (4:ℝ) (5:ℝ)
      ∧ (∫ x in (4:ℝ)..(5:ℝ), RR x / x ^ 3) = (37383/704000 : ℝ) := by
  have h := chain_integral [((180/43 : ℝ), (17/5 : ℝ), (-11 : ℝ)), ((160/37 : ℝ), (17/5 : ℝ), (-11 : ℝ)), ((100/23 : ℝ), (321/40 : ℝ), (-31 : ℝ)), ((9/2 : ℝ), (55/8 : ℝ), (-26 : ℝ)), ((200/43 : ℝ), (63/8 : ℝ), (-61/2 : ℝ)), ((110/23 : ℝ), (93/20 : ℝ), (-31/2 : ℝ)), ((180/37 : ℝ), (7/2 : ℝ), (-10 : ℝ)), ((5 : ℝ), (107/20 : ℝ), (-19 : ℝ))] (4:ℝ) (by norm_num)
    ⟨by norm_num, by norm_num, p4_0, by norm_num, by norm_num, p4_1, by norm_num, by norm_num, p4_2, by norm_num, by norm_num, p4_3, by norm_num, by norm_num, p4_4, by norm_num, by norm_num, p4_5, by norm_num, by norm_num, p4_6, by norm_num, by norm_num, p4_7, trivial⟩
  simp only [chainEnd] at h
  exact ⟨h.1, by rw [h.2]; norm_num [chainVal]⟩

/-! ### Table 3, row `j = 5`: the 8 intervals of (B.2) inside `[5,6]` -/

lemma p5_0 : ∀ x : ℝ, (5 : ℝ) < x → x < (220/43 : ℝ) →
    RR x = (9/2 : ℝ) * x + (-24 : ℝ) :=
  RR_affine_on (l := (5 : ℝ)) (r := (220/43 : ℝ)) (n := 5) (m := 0) (k := 11)
    (j := 10) (i := 9) (ef := 1) (eg := 1)
    (dm := true) (ts := true)
    (A := (9/2 : ℝ)) (B := (-24 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p5_1 : ∀ x : ℝ, (220/43 : ℝ) < x → x < (120/23 : ℝ) →
    RR x = (9/2 : ℝ) * x + (-24 : ℝ) :=
  RR_affine_on (l := (220/43 : ℝ)) (r := (120/23 : ℝ)) (n := 5) (m := 0) (k := 11)
    (j := 10) (i := 9) (ef := 1) (eg := 1)
    (dm := true) (ts := true)
    (A := (9/2 : ℝ)) (B := (-24 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p5_2 : ∀ x : ℝ, (120/23 : ℝ) < x → x < (200/37 : ℝ) →
    RR x = (67/20 : ℝ) * x + (-18 : ℝ) :=
  RR_affine_on (l := (120/23 : ℝ)) (r := (200/37 : ℝ)) (n := 5) (m := 0) (k := 12)
    (j := 10) (i := 9) (ef := 1) (eg := 1)
    (dm := true) (ts := false)
    (A := (67/20 : ℝ)) (B := (-18 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p5_3 : ∀ x : ℝ, (200/37 : ℝ) < x → x < (11/2 : ℝ) →
    RR x = (319/40 : ℝ) * x + (-43 : ℝ) :=
  RR_affine_on (l := (200/37 : ℝ)) (r := (11/2 : ℝ)) (n := 5) (m := 0) (k := 12)
    (j := 10) (i := 10) (ef := 1) (eg := 1)
    (dm := false) (ts := false)
    (A := (319/40 : ℝ)) (B := (-43 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p5_4 : ∀ x : ℝ, (11/2 : ℝ) < x → x < (240/43 : ℝ) →
    RR x = (359/40 : ℝ) * x + (-97/2 : ℝ) :=
  RR_affine_on (l := (11/2 : ℝ)) (r := (240/43 : ℝ)) (n := 5) (m := 0) (k := 12)
    (j := 11) (i := 10) (ef := -1) (eg := 1)
    (dm := false) (ts := true)
    (A := (359/40 : ℝ)) (B := (-97/2 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p5_5 : ∀ x : ℝ, (240/43 : ℝ) < x → x < (130/23 : ℝ) →
    RR x = (23/4 : ℝ) * x + (-61/2 : ℝ) :=
  RR_affine_on (l := (240/43 : ℝ)) (r := (130/23 : ℝ)) (n := 5) (m := 0) (k := 12)
    (j := 11) (i := 10) (ef := -1) (eg := 1)
    (dm := true) (ts := true)
    (A := (23/4 : ℝ)) (B := (-61/2 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p5_6 : ∀ x : ℝ, (130/23 : ℝ) < x → x < (220/37 : ℝ) →
    RR x = (23/5 : ℝ) * x + (-24 : ℝ) :=
  RR_affine_on (l := (130/23 : ℝ)) (r := (220/37 : ℝ)) (n := 5) (m := 0) (k := 13)
    (j := 11) (i := 10) (ef := -1) (eg := 1)
    (dm := true) (ts := false)
    (A := (23/5 : ℝ)) (B := (-24 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p5_7 : ∀ x : ℝ, (220/37 : ℝ) < x → x < (6 : ℝ) →
    RR x = (129/20 : ℝ) * x + (-35 : ℝ) :=
  RR_affine_on (l := (220/37 : ℝ)) (r := (6 : ℝ)) (n := 5) (m := 0) (k := 13)
    (j := 11) (i := 11) (ef := -1) (eg := 1)
    (dm := true) (ts := false)
    (A := (129/20 : ℝ)) (B := (-35 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

/-- **Table 3**, row `j = 5` (p. 27):
`∫_{5}^{6} R(x) x^(-3) dx = 37523/8236800`. -/
theorem table3_5 :
    IntervalIntegrable (fun x => RR x / x ^ 3) volume (5:ℝ) (6:ℝ)
      ∧ (∫ x in (5:ℝ)..(6:ℝ), RR x / x ^ 3) = (37523/8236800 : ℝ) := by
  have h := chain_integral [((220/43 : ℝ), (9/2 : ℝ), (-24 : ℝ)), ((120/23 : ℝ), (9/2 : ℝ), (-24 : ℝ)), ((200/37 : ℝ), (67/20 : ℝ), (-18 : ℝ)), ((11/2 : ℝ), (319/40 : ℝ), (-43 : ℝ)), ((240/43 : ℝ), (359/40 : ℝ), (-97/2 : ℝ)), ((130/23 : ℝ), (23/4 : ℝ), (-61/2 : ℝ)), ((220/37 : ℝ), (23/5 : ℝ), (-24 : ℝ)), ((6 : ℝ), (129/20 : ℝ), (-35 : ℝ))] (5:ℝ) (by norm_num)
    ⟨by norm_num, by norm_num, p5_0, by norm_num, by norm_num, p5_1, by norm_num, by norm_num, p5_2, by norm_num, by norm_num, p5_3, by norm_num, by norm_num, p5_4, by norm_num, by norm_num, p5_5, by norm_num, by norm_num, p5_6, by norm_num, by norm_num, p5_7, trivial⟩
  simp only [chainEnd] at h
  exact ⟨h.1, by rw [h.2]; norm_num [chainVal]⟩

/-! ### Table 3, row `j = 6`: the 10 intervals of (B.2) inside `[6,7]` -/

lemma p6_0 : ∀ x : ℝ, (6 : ℝ) < x → x < (260/43 : ℝ) →
    RR x = (28/5 : ℝ) * x + (-41 : ℝ) :=
  RR_affine_on (l := (6 : ℝ)) (r := (260/43 : ℝ)) (n := 6) (m := 0) (k := 13)
    (j := 12) (i := 11) (ef := 1) (eg := 1)
    (dm := true) (ts := true)
    (A := (28/5 : ℝ)) (B := (-41 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p6_1 : ∀ x : ℝ, (260/43 : ℝ) < x → x < (140/23 : ℝ) →
    RR x = (28/5 : ℝ) * x + (-41 : ℝ) :=
  RR_affine_on (l := (260/43 : ℝ)) (r := (140/23 : ℝ)) (n := 6) (m := 0) (k := 13)
    (j := 12) (i := 11) (ef := 1) (eg := 1)
    (dm := true) (ts := true)
    (A := (28/5 : ℝ)) (B := (-41 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p6_2 : ∀ x : ℝ, (140/23 : ℝ) < x → x < (240/37 : ℝ) →
    RR x = (89/20 : ℝ) * x + (-34 : ℝ) :=
  RR_affine_on (l := (140/23 : ℝ)) (r := (240/37 : ℝ)) (n := 6) (m := 0) (k := 14)
    (j := 12) (i := 11) (ef := 1) (eg := 1)
    (dm := true) (ts := false)
    (A := (89/20 : ℝ)) (B := (-34 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p6_3 : ∀ x : ℝ, (240/37 : ℝ) < x → x < (13/2 : ℝ) →
    RR x = (363/40 : ℝ) * x + (-64 : ℝ) :=
  RR_affine_on (l := (240/37 : ℝ)) (r := (13/2 : ℝ)) (n := 6) (m := 0) (k := 14)
    (j := 12) (i := 12) (ef := 1) (eg := 1)
    (dm := false) (ts := false)
    (A := (363/40 : ℝ)) (B := (-64 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p6_4 : ∀ x : ℝ, (13/2 : ℝ) < x → x < (280/43 : ℝ) →
    RR x = (403/40 : ℝ) * x + (-141/2 : ℝ) :=
  RR_affine_on (l := (13/2 : ℝ)) (r := (280/43 : ℝ)) (n := 6) (m := 0) (k := 14)
    (j := 13) (i := 12) (ef := -1) (eg := 1)
    (dm := false) (ts := true)
    (A := (403/40 : ℝ)) (B := (-141/2 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p6_5 : ∀ x : ℝ, (280/43 : ℝ) < x → x < (150/23 : ℝ) →
    RR x = (137/20 : ℝ) * x + (-99/2 : ℝ) :=
  RR_affine_on (l := (280/43 : ℝ)) (r := (150/23 : ℝ)) (n := 6) (m := 0) (k := 14)
    (j := 13) (i := 12) (ef := -1) (eg := 1)
    (dm := true) (ts := true)
    (A := (137/20 : ℝ)) (B := (-99/2 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p6_6 : ∀ x : ℝ, (150/23 : ℝ) < x → x < (20/3 : ℝ) →
    RR x = (57/10 : ℝ) * x + (-42 : ℝ) :=
  RR_affine_on (l := (150/23 : ℝ)) (r := (20/3 : ℝ)) (n := 6) (m := 0) (k := 15)
    (j := 13) (i := 12) (ef := -1) (eg := 1)
    (dm := true) (ts := false)
    (A := (57/10 : ℝ)) (B := (-42 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p6_7 : ∀ x : ℝ, (20/3 : ℝ) < x → x < (160/23 : ℝ) →
    RR x = (69/10 : ℝ) * x + (-50 : ℝ) :=
  RR_affine_on (l := (20/3 : ℝ)) (r := (160/23 : ℝ)) (n := 6) (m := 0) (k := 15)
    (j := 13) (i := 12) (ef := -1) (eg := -1)
    (dm := true) (ts := true)
    (A := (69/10 : ℝ)) (B := (-50 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p6_8 : ∀ x : ℝ, (160/23 : ℝ) < x → x < (300/43 : ℝ) →
    RR x = (23/4 : ℝ) * x + (-42 : ℝ) :=
  RR_affine_on (l := (160/23 : ℝ)) (r := (300/43 : ℝ)) (n := 6) (m := 0) (k := 16)
    (j := 13) (i := 12) (ef := -1) (eg := -1)
    (dm := true) (ts := false)
    (A := (23/4 : ℝ)) (B := (-42 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p6_9 : ∀ x : ℝ, (300/43 : ℝ) < x → x < (7 : ℝ) →
    RR x = (23/4 : ℝ) * x + (-42 : ℝ) :=
  RR_affine_on (l := (300/43 : ℝ)) (r := (7 : ℝ)) (n := 6) (m := 0) (k := 16)
    (j := 13) (i := 12) (ef := -1) (eg := -1)
    (dm := true) (ts := false)
    (A := (23/4 : ℝ)) (B := (-42 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

/-- **Table 3**, row `j = 6` (p. 27):
`∫_{6}^{7} R(x) x^(-3) dx = -120923/6552000`. -/
theorem table3_6 :
    IntervalIntegrable (fun x => RR x / x ^ 3) volume (6:ℝ) (7:ℝ)
      ∧ (∫ x in (6:ℝ)..(7:ℝ), RR x / x ^ 3) = (-120923/6552000 : ℝ) := by
  have h := chain_integral [((260/43 : ℝ), (28/5 : ℝ), (-41 : ℝ)), ((140/23 : ℝ), (28/5 : ℝ), (-41 : ℝ)), ((240/37 : ℝ), (89/20 : ℝ), (-34 : ℝ)), ((13/2 : ℝ), (363/40 : ℝ), (-64 : ℝ)), ((280/43 : ℝ), (403/40 : ℝ), (-141/2 : ℝ)), ((150/23 : ℝ), (137/20 : ℝ), (-99/2 : ℝ)), ((20/3 : ℝ), (57/10 : ℝ), (-42 : ℝ)), ((160/23 : ℝ), (69/10 : ℝ), (-50 : ℝ)), ((300/43 : ℝ), (23/4 : ℝ), (-42 : ℝ)), ((7 : ℝ), (23/4 : ℝ), (-42 : ℝ))] (6:ℝ) (by norm_num)
    ⟨by norm_num, by norm_num, p6_0, by norm_num, by norm_num, p6_1, by norm_num, by norm_num, p6_2, by norm_num, by norm_num, p6_3, by norm_num, by norm_num, p6_4, by norm_num, by norm_num, p6_5, by norm_num, by norm_num, p6_6, by norm_num, by norm_num, p6_7, by norm_num, by norm_num, p6_8, by norm_num, by norm_num, p6_9, trivial⟩
  simp only [chainEnd] at h
  exact ⟨h.1, by rw [h.2]; norm_num [chainVal]⟩

/-! ### Table 3, row `j = 7`: the 8 intervals of (B.2) inside `[7,8]` -/

lemma p7_0 : ∀ x : ℝ, (7 : ℝ) < x → x < (260/37 : ℝ) →
    RR x = (49/10 : ℝ) * x + (-49 : ℝ) :=
  RR_affine_on (l := (7 : ℝ)) (r := (260/37 : ℝ)) (n := 7) (m := 0) (k := 16)
    (j := 14) (i := 12) (ef := 1) (eg := -1)
    (dm := true) (ts := true)
    (A := (49/10 : ℝ)) (B := (-49 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p7_1 : ∀ x : ℝ, (260/37 : ℝ) < x → x < (170/23 : ℝ) →
    RR x = (27/4 : ℝ) * x + (-62 : ℝ) :=
  RR_affine_on (l := (260/37 : ℝ)) (r := (170/23 : ℝ)) (n := 7) (m := 0) (k := 16)
    (j := 14) (i := 13) (ef := 1) (eg := -1)
    (dm := true) (ts := true)
    (A := (27/4 : ℝ)) (B := (-62 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p7_2 : ∀ x : ℝ, (170/23 : ℝ) < x → x < (320/43 : ℝ) →
    RR x = (28/5 : ℝ) * x + (-107/2 : ℝ) :=
  RR_affine_on (l := (170/23 : ℝ)) (r := (320/43 : ℝ)) (n := 7) (m := 0) (k := 17)
    (j := 14) (i := 13) (ef := 1) (eg := -1)
    (dm := true) (ts := false)
    (A := (28/5 : ℝ)) (B := (-107/2 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p7_3 : ∀ x : ℝ, (320/43 : ℝ) < x → x < (15/2 : ℝ) →
    RR x = (19/8 : ℝ) * x + (-59/2 : ℝ) :=
  RR_affine_on (l := (320/43 : ℝ)) (r := (15/2 : ℝ)) (n := 7) (m := 0) (k := 17)
    (j := 14) (i := 13) (ef := 1) (eg := -1)
    (dm := false) (ts := false)
    (A := (19/8 : ℝ)) (B := (-59/2 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p7_4 : ∀ x : ℝ, (15/2 : ℝ) < x → x < (280/37 : ℝ) →
    RR x = (27/8 : ℝ) * x + (-37 : ℝ) :=
  RR_affine_on (l := (15/2 : ℝ)) (r := (280/37 : ℝ)) (n := 7) (m := 0) (k := 17)
    (j := 15) (i := 13) (ef := -1) (eg := -1)
    (dm := false) (ts := true)
    (A := (27/8 : ℝ)) (B := (-37 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p7_5 : ∀ x : ℝ, (280/37 : ℝ) < x → x < (180/23 : ℝ) →
    RR x = (8 : ℝ) * x + (-72 : ℝ) :=
  RR_affine_on (l := (280/37 : ℝ)) (r := (180/23 : ℝ)) (n := 7) (m := 0) (k := 17)
    (j := 15) (i := 14) (ef := -1) (eg := -1)
    (dm := true) (ts := true)
    (A := (8 : ℝ)) (B := (-72 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p7_6 : ∀ x : ℝ, (180/23 : ℝ) < x → x < (340/43 : ℝ) →
    RR x = (137/20 : ℝ) * x + (-63 : ℝ) :=
  RR_affine_on (l := (180/23 : ℝ)) (r := (340/43 : ℝ)) (n := 7) (m := 0) (k := 18)
    (j := 15) (i := 14) (ef := -1) (eg := -1)
    (dm := true) (ts := false)
    (A := (137/20 : ℝ)) (B := (-63 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p7_7 : ∀ x : ℝ, (340/43 : ℝ) < x → x < (8 : ℝ) →
    RR x = (137/20 : ℝ) * x + (-63 : ℝ) :=
  RR_affine_on (l := (340/43 : ℝ)) (r := (8 : ℝ)) (n := 7) (m := 0) (k := 18)
    (j := 15) (i := 14) (ef := -1) (eg := -1)
    (dm := true) (ts := false)
    (A := (137/20 : ℝ)) (B := (-63 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

/-- **Table 3**, row `j = 7` (p. 27):
`∫_{7}^{8} R(x) x^(-3) dx = -10025233/356428800`. -/
theorem table3_7 :
    IntervalIntegrable (fun x => RR x / x ^ 3) volume (7:ℝ) (8:ℝ)
      ∧ (∫ x in (7:ℝ)..(8:ℝ), RR x / x ^ 3) = (-10025233/356428800 : ℝ) := by
  have h := chain_integral [((260/37 : ℝ), (49/10 : ℝ), (-49 : ℝ)), ((170/23 : ℝ), (27/4 : ℝ), (-62 : ℝ)), ((320/43 : ℝ), (28/5 : ℝ), (-107/2 : ℝ)), ((15/2 : ℝ), (19/8 : ℝ), (-59/2 : ℝ)), ((280/37 : ℝ), (27/8 : ℝ), (-37 : ℝ)), ((180/23 : ℝ), (8 : ℝ), (-72 : ℝ)), ((340/43 : ℝ), (137/20 : ℝ), (-63 : ℝ)), ((8 : ℝ), (137/20 : ℝ), (-63 : ℝ))] (7:ℝ) (by norm_num)
    ⟨by norm_num, by norm_num, p7_0, by norm_num, by norm_num, p7_1, by norm_num, by norm_num, p7_2, by norm_num, by norm_num, p7_3, by norm_num, by norm_num, p7_4, by norm_num, by norm_num, p7_5, by norm_num, by norm_num, p7_6, by norm_num, by norm_num, p7_7, trivial⟩
  simp only [chainEnd] at h
  exact ⟨h.1, by rw [h.2]; norm_num [chainVal]⟩

/-! ### Table 3, row `j = 8`: the 8 intervals of (B.2) inside `[8,9]` -/

lemma p8_0 : ∀ x : ℝ, (8 : ℝ) < x → x < (300/37 : ℝ) →
    RR x = (6 : ℝ) * x + (-71 : ℝ) :=
  RR_affine_on (l := (8 : ℝ)) (r := (300/37 : ℝ)) (n := 8) (m := 0) (k := 18)
    (j := 16) (i := 14) (ef := 1) (eg := -1)
    (dm := true) (ts := true)
    (A := (6 : ℝ)) (B := (-71 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p8_1 : ∀ x : ℝ, (300/37 : ℝ) < x → x < (190/23 : ℝ) →
    RR x = (157/20 : ℝ) * x + (-86 : ℝ) :=
  RR_affine_on (l := (300/37 : ℝ)) (r := (190/23 : ℝ)) (n := 8) (m := 0) (k := 18)
    (j := 16) (i := 15) (ef := 1) (eg := -1)
    (dm := true) (ts := true)
    (A := (157/20 : ℝ)) (B := (-86 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p8_2 : ∀ x : ℝ, (190/23 : ℝ) < x → x < (360/43 : ℝ) →
    RR x = (67/10 : ℝ) * x + (-153/2 : ℝ) :=
  RR_affine_on (l := (190/23 : ℝ)) (r := (360/43 : ℝ)) (n := 8) (m := 0) (k := 19)
    (j := 16) (i := 15) (ef := 1) (eg := -1)
    (dm := true) (ts := false)
    (A := (67/10 : ℝ)) (B := (-153/2 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p8_3 : ∀ x : ℝ, (360/43 : ℝ) < x → x < (17/2 : ℝ) →
    RR x = (139/40 : ℝ) * x + (-99/2 : ℝ) :=
  RR_affine_on (l := (360/43 : ℝ)) (r := (17/2 : ℝ)) (n := 8) (m := 0) (k := 19)
    (j := 16) (i := 15) (ef := 1) (eg := -1)
    (dm := false) (ts := false)
    (A := (139/40 : ℝ)) (B := (-99/2 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p8_4 : ∀ x : ℝ, (17/2 : ℝ) < x → x < (320/37 : ℝ) →
    RR x = (179/40 : ℝ) * x + (-58 : ℝ) :=
  RR_affine_on (l := (17/2 : ℝ)) (r := (320/37 : ℝ)) (n := 8) (m := 0) (k := 19)
    (j := 17) (i := 15) (ef := -1) (eg := -1)
    (dm := false) (ts := true)
    (A := (179/40 : ℝ)) (B := (-58 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p8_5 : ∀ x : ℝ, (320/37 : ℝ) < x → x < (200/23 : ℝ) →
    RR x = (91/10 : ℝ) * x + (-98 : ℝ) :=
  RR_affine_on (l := (320/37 : ℝ)) (r := (200/23 : ℝ)) (n := 8) (m := 0) (k := 19)
    (j := 17) (i := 16) (ef := -1) (eg := -1)
    (dm := true) (ts := true)
    (A := (91/10 : ℝ)) (B := (-98 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p8_6 : ∀ x : ℝ, (200/23 : ℝ) < x → x < (380/43 : ℝ) →
    RR x = (159/20 : ℝ) * x + (-88 : ℝ) :=
  RR_affine_on (l := (200/23 : ℝ)) (r := (380/43 : ℝ)) (n := 8) (m := 0) (k := 20)
    (j := 17) (i := 16) (ef := -1) (eg := -1)
    (dm := true) (ts := false)
    (A := (159/20 : ℝ)) (B := (-88 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p8_7 : ∀ x : ℝ, (380/43 : ℝ) < x → x < (9 : ℝ) →
    RR x = (159/20 : ℝ) * x + (-88 : ℝ) :=
  RR_affine_on (l := (380/43 : ℝ)) (r := (9 : ℝ)) (n := 8) (m := 0) (k := 20)
    (j := 17) (i := 16) (ef := -1) (eg := -1)
    (dm := true) (ts := false)
    (A := (159/20 : ℝ)) (B := (-88 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

/-- **Table 3**, row `j = 8` (p. 27):
`∫_{8}^{9} R(x) x^(-3) dx = -110029309/3348864000`. -/
theorem table3_8 :
    IntervalIntegrable (fun x => RR x / x ^ 3) volume (8:ℝ) (9:ℝ)
      ∧ (∫ x in (8:ℝ)..(9:ℝ), RR x / x ^ 3) = (-110029309/3348864000 : ℝ) := by
  have h := chain_integral [((300/37 : ℝ), (6 : ℝ), (-71 : ℝ)), ((190/23 : ℝ), (157/20 : ℝ), (-86 : ℝ)), ((360/43 : ℝ), (67/10 : ℝ), (-153/2 : ℝ)), ((17/2 : ℝ), (139/40 : ℝ), (-99/2 : ℝ)), ((320/37 : ℝ), (179/40 : ℝ), (-58 : ℝ)), ((200/23 : ℝ), (91/10 : ℝ), (-98 : ℝ)), ((380/43 : ℝ), (159/20 : ℝ), (-88 : ℝ)), ((9 : ℝ), (159/20 : ℝ), (-88 : ℝ))] (8:ℝ) (by norm_num)
    ⟨by norm_num, by norm_num, p8_0, by norm_num, by norm_num, p8_1, by norm_num, by norm_num, p8_2, by norm_num, by norm_num, p8_3, by norm_num, by norm_num, p8_4, by norm_num, by norm_num, p8_5, by norm_num, by norm_num, p8_6, by norm_num, by norm_num, p8_7, trivial⟩
  simp only [chainEnd] at h
  exact ⟨h.1, by rw [h.2]; norm_num [chainVal]⟩

/-! ### Table 3, row `j = 9`: the 8 intervals of (B.2) inside `[9,10]` -/

lemma p9_0 : ∀ x : ℝ, (9 : ℝ) < x → x < (210/23 : ℝ) →
    RR x = (71/10 : ℝ) * x + (-97 : ℝ) :=
  RR_affine_on (l := (9 : ℝ)) (r := (210/23 : ℝ)) (n := 9) (m := 0) (k := 20)
    (j := 18) (i := 16) (ef := 1) (eg := -1)
    (dm := true) (ts := true)
    (A := (71/10 : ℝ)) (B := (-97 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p9_1 : ∀ x : ℝ, (210/23 : ℝ) < x → x < (340/37 : ℝ) →
    RR x = (119/20 : ℝ) * x + (-173/2 : ℝ) :=
  RR_affine_on (l := (210/23 : ℝ)) (r := (340/37 : ℝ)) (n := 9) (m := 0) (k := 21)
    (j := 18) (i := 16) (ef := 1) (eg := -1)
    (dm := true) (ts := false)
    (A := (119/20 : ℝ)) (B := (-173/2 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p9_2 : ∀ x : ℝ, (340/37 : ℝ) < x → x < (400/43 : ℝ) →
    RR x = (39/5 : ℝ) * x + (-207/2 : ℝ) :=
  RR_affine_on (l := (340/37 : ℝ)) (r := (400/43 : ℝ)) (n := 9) (m := 0) (k := 21)
    (j := 18) (i := 17) (ef := 1) (eg := -1)
    (dm := true) (ts := false)
    (A := (39/5 : ℝ)) (B := (-207/2 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p9_3 : ∀ x : ℝ, (400/43 : ℝ) < x → x < (19/2 : ℝ) →
    RR x = (183/40 : ℝ) * x + (-147/2 : ℝ) :=
  RR_affine_on (l := (400/43 : ℝ)) (r := (19/2 : ℝ)) (n := 9) (m := 0) (k := 21)
    (j := 18) (i := 17) (ef := 1) (eg := -1)
    (dm := false) (ts := false)
    (A := (183/40 : ℝ)) (B := (-147/2 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p9_4 : ∀ x : ℝ, (19/2 : ℝ) < x → x < (220/23 : ℝ) →
    RR x = (223/40 : ℝ) * x + (-83 : ℝ) :=
  RR_affine_on (l := (19/2 : ℝ)) (r := (220/23 : ℝ)) (n := 9) (m := 0) (k := 21)
    (j := 19) (i := 17) (ef := -1) (eg := -1)
    (dm := false) (ts := true)
    (A := (223/40 : ℝ)) (B := (-83 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p9_5 : ∀ x : ℝ, (220/23 : ℝ) < x → x < (360/37 : ℝ) →
    RR x = (177/40 : ℝ) * x + (-72 : ℝ) :=
  RR_affine_on (l := (220/23 : ℝ)) (r := (360/37 : ℝ)) (n := 9) (m := 0) (k := 22)
    (j := 19) (i := 17) (ef := -1) (eg := -1)
    (dm := false) (ts := false)
    (A := (177/40 : ℝ)) (B := (-72 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p9_6 : ∀ x : ℝ, (360/37 : ℝ) < x → x < (420/43 : ℝ) →
    RR x = (181/20 : ℝ) * x + (-117 : ℝ) :=
  RR_affine_on (l := (360/37 : ℝ)) (r := (420/43 : ℝ)) (n := 9) (m := 0) (k := 22)
    (j := 19) (i := 18) (ef := -1) (eg := -1)
    (dm := true) (ts := false)
    (A := (181/20 : ℝ)) (B := (-117 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p9_7 : ∀ x : ℝ, (420/43 : ℝ) < x → x < (10 : ℝ) →
    RR x = (181/20 : ℝ) * x + (-117 : ℝ) :=
  RR_affine_on (l := (420/43 : ℝ)) (r := (10 : ℝ)) (n := 9) (m := 0) (k := 22)
    (j := 19) (i := 18) (ef := -1) (eg := -1)
    (dm := true) (ts := false)
    (A := (181/20 : ℝ)) (B := (-117 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

/-- **Table 3**, row `j = 9` (p. 27):
`∫_{9}^{10} R(x) x^(-3) dx = -2278419487/64465632000`. -/
theorem table3_9 :
    IntervalIntegrable (fun x => RR x / x ^ 3) volume (9:ℝ) (10:ℝ)
      ∧ (∫ x in (9:ℝ)..(10:ℝ), RR x / x ^ 3) = (-2278419487/64465632000 : ℝ) := by
  have h := chain_integral [((210/23 : ℝ), (71/10 : ℝ), (-97 : ℝ)), ((340/37 : ℝ), (119/20 : ℝ), (-173/2 : ℝ)), ((400/43 : ℝ), (39/5 : ℝ), (-207/2 : ℝ)), ((19/2 : ℝ), (183/40 : ℝ), (-147/2 : ℝ)), ((220/23 : ℝ), (223/40 : ℝ), (-83 : ℝ)), ((360/37 : ℝ), (177/40 : ℝ), (-72 : ℝ)), ((420/43 : ℝ), (181/20 : ℝ), (-117 : ℝ)), ((10 : ℝ), (181/20 : ℝ), (-117 : ℝ))] (9:ℝ) (by norm_num)
    ⟨by norm_num, by norm_num, p9_0, by norm_num, by norm_num, p9_1, by norm_num, by norm_num, p9_2, by norm_num, by norm_num, p9_3, by norm_num, by norm_num, p9_4, by norm_num, by norm_num, p9_5, by norm_num, by norm_num, p9_6, by norm_num, by norm_num, p9_7, trivial⟩
  simp only [chainEnd] at h
  exact ⟨h.1, by rw [h.2]; norm_num [chainVal]⟩

/-! ### Table 3, row `j = 10`: the 8 intervals of (B.2) inside `[10,11]` -/

lemma p10_0 : ∀ x : ℝ, (10 : ℝ) < x → x < (440/43 : ℝ) →
    RR x = (69/10 : ℝ) * x + (-114 : ℝ) :=
  RR_affine_on (l := (10 : ℝ)) (r := (440/43 : ℝ)) (n := 10) (m := 0) (k := 23)
    (j := 20) (i := 18) (ef := 1) (eg := -1)
    (dm := true) (ts := true)
    (A := (69/10 : ℝ)) (B := (-114 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p10_1 : ∀ x : ℝ, (440/43 : ℝ) < x → x < (380/37 : ℝ) →
    RR x = (147/40 : ℝ) * x + (-81 : ℝ) :=
  RR_affine_on (l := (440/43 : ℝ)) (r := (380/37 : ℝ)) (n := 10) (m := 0) (k := 23)
    (j := 20) (i := 18) (ef := 1) (eg := -1)
    (dm := false) (ts := true)
    (A := (147/40 : ℝ)) (B := (-81 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p10_2 : ∀ x : ℝ, (380/37 : ℝ) < x → x < (240/23 : ℝ) →
    RR x = (221/40 : ℝ) * x + (-100 : ℝ) :=
  RR_affine_on (l := (380/37 : ℝ)) (r := (240/23 : ℝ)) (n := 10) (m := 0) (k := 23)
    (j := 20) (i := 19) (ef := 1) (eg := -1)
    (dm := false) (ts := true)
    (A := (221/40 : ℝ)) (B := (-100 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p10_3 : ∀ x : ℝ, (240/23 : ℝ) < x → x < (21/2 : ℝ) →
    RR x = (35/8 : ℝ) * x + (-88 : ℝ) :=
  RR_affine_on (l := (240/23 : ℝ)) (r := (21/2 : ℝ)) (n := 10) (m := 0) (k := 24)
    (j := 20) (i := 19) (ef := 1) (eg := -1)
    (dm := false) (ts := false)
    (A := (35/8 : ℝ)) (B := (-88 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p10_4 : ∀ x : ℝ, (21/2 : ℝ) < x → x < (460/43 : ℝ) →
    RR x = (43/8 : ℝ) * x + (-197/2 : ℝ) :=
  RR_affine_on (l := (21/2 : ℝ)) (r := (460/43 : ℝ)) (n := 10) (m := 0) (k := 24)
    (j := 21) (i := 19) (ef := -1) (eg := -1)
    (dm := false) (ts := true)
    (A := (43/8 : ℝ)) (B := (-197/2 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p10_5 : ∀ x : ℝ, (460/43 : ℝ) < x → x < (400/37 : ℝ) →
    RR x = (43/8 : ℝ) * x + (-197/2 : ℝ) :=
  RR_affine_on (l := (460/43 : ℝ)) (r := (400/37 : ℝ)) (n := 10) (m := 0) (k := 24)
    (j := 21) (i := 19) (ef := -1) (eg := -1)
    (dm := false) (ts := true)
    (A := (43/8 : ℝ)) (B := (-197/2 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p10_6 : ∀ x : ℝ, (400/37 : ℝ) < x → x < (250/23 : ℝ) →
    RR x = (10 : ℝ) * x + (-297/2 : ℝ) :=
  RR_affine_on (l := (400/37 : ℝ)) (r := (250/23 : ℝ)) (n := 10) (m := 0) (k := 24)
    (j := 21) (i := 20) (ef := -1) (eg := -1)
    (dm := true) (ts := true)
    (A := (10 : ℝ)) (B := (-297/2 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p10_7 : ∀ x : ℝ, (250/23 : ℝ) < x → x < (11 : ℝ) →
    RR x = (177/20 : ℝ) * x + (-136 : ℝ) :=
  RR_affine_on (l := (250/23 : ℝ)) (r := (11 : ℝ)) (n := 10) (m := 0) (k := 25)
    (j := 21) (i := 20) (ef := -1) (eg := -1)
    (dm := true) (ts := false)
    (A := (177/20 : ℝ)) (B := (-136 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

/-- **Table 3**, row `j = 10` (p. 27):
`∫_{10}^{11} R(x) x^(-3) dx = -282415081/7724640000`. -/
theorem table3_10 :
    IntervalIntegrable (fun x => RR x / x ^ 3) volume (10:ℝ) (11:ℝ)
      ∧ (∫ x in (10:ℝ)..(11:ℝ), RR x / x ^ 3) = (-282415081/7724640000 : ℝ) := by
  have h := chain_integral [((440/43 : ℝ), (69/10 : ℝ), (-114 : ℝ)), ((380/37 : ℝ), (147/40 : ℝ), (-81 : ℝ)), ((240/23 : ℝ), (221/40 : ℝ), (-100 : ℝ)), ((21/2 : ℝ), (35/8 : ℝ), (-88 : ℝ)), ((460/43 : ℝ), (43/8 : ℝ), (-197/2 : ℝ)), ((400/37 : ℝ), (43/8 : ℝ), (-197/2 : ℝ)), ((250/23 : ℝ), (10 : ℝ), (-297/2 : ℝ)), ((11 : ℝ), (177/20 : ℝ), (-136 : ℝ))] (10:ℝ) (by norm_num)
    ⟨by norm_num, by norm_num, p10_0, by norm_num, by norm_num, p10_1, by norm_num, by norm_num, p10_2, by norm_num, by norm_num, p10_3, by norm_num, by norm_num, p10_4, by norm_num, by norm_num, p10_5, by norm_num, by norm_num, p10_6, by norm_num, by norm_num, p10_7, trivial⟩
  simp only [chainEnd] at h
  exact ⟨h.1, by rw [h.2]; norm_num [chainVal]⟩

/-! ### Table 3, row `j = 11`: the 8 intervals of (B.2) inside `[11,12]` -/

lemma p11_0 : ∀ x : ℝ, (11 : ℝ) < x → x < (480/43 : ℝ) →
    RR x = (8 : ℝ) * x + (-147 : ℝ) :=
  RR_affine_on (l := (11 : ℝ)) (r := (480/43 : ℝ)) (n := 11) (m := 0) (k := 25)
    (j := 22) (i := 20) (ef := 1) (eg := -1)
    (dm := true) (ts := true)
    (A := (8 : ℝ)) (B := (-147 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p11_1 : ∀ x : ℝ, (480/43 : ℝ) < x → x < (260/23 : ℝ) →
    RR x = (191/40 : ℝ) * x + (-111 : ℝ) :=
  RR_affine_on (l := (480/43 : ℝ)) (r := (260/23 : ℝ)) (n := 11) (m := 0) (k := 25)
    (j := 22) (i := 20) (ef := 1) (eg := -1)
    (dm := false) (ts := true)
    (A := (191/40 : ℝ)) (B := (-111 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p11_2 : ∀ x : ℝ, (260/23 : ℝ) < x → x < (420/37 : ℝ) →
    RR x = (29/8 : ℝ) * x + (-98 : ℝ) :=
  RR_affine_on (l := (260/23 : ℝ)) (r := (420/37 : ℝ)) (n := 11) (m := 0) (k := 26)
    (j := 22) (i := 20) (ef := 1) (eg := -1)
    (dm := false) (ts := false)
    (A := (29/8 : ℝ)) (B := (-98 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p11_3 : ∀ x : ℝ, (420/37 : ℝ) < x → x < (23/2 : ℝ) →
    RR x = (219/40 : ℝ) * x + (-119 : ℝ) :=
  RR_affine_on (l := (420/37 : ℝ)) (r := (23/2 : ℝ)) (n := 11) (m := 0) (k := 26)
    (j := 22) (i := 21) (ef := 1) (eg := -1)
    (dm := false) (ts := false)
    (A := (219/40 : ℝ)) (B := (-119 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p11_4 : ∀ x : ℝ, (23/2 : ℝ) < x → x < (500/43 : ℝ) →
    RR x = (259/40 : ℝ) * x + (-261/2 : ℝ) :=
  RR_affine_on (l := (23/2 : ℝ)) (r := (500/43 : ℝ)) (n := 11) (m := 0) (k := 26)
    (j := 23) (i := 21) (ef := -1) (eg := -1)
    (dm := false) (ts := true)
    (A := (259/40 : ℝ)) (B := (-261/2 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p11_5 : ∀ x : ℝ, (500/43 : ℝ) < x → x < (270/23 : ℝ) →
    RR x = (259/40 : ℝ) * x + (-261/2 : ℝ) :=
  RR_affine_on (l := (500/43 : ℝ)) (r := (270/23 : ℝ)) (n := 11) (m := 0) (k := 26)
    (j := 23) (i := 21) (ef := -1) (eg := -1)
    (dm := false) (ts := true)
    (A := (259/40 : ℝ)) (B := (-261/2 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p11_6 : ∀ x : ℝ, (270/23 : ℝ) < x → x < (440/37 : ℝ) →
    RR x = (213/40 : ℝ) * x + (-117 : ℝ) :=
  RR_affine_on (l := (270/23 : ℝ)) (r := (440/37 : ℝ)) (n := 11) (m := 0) (k := 27)
    (j := 23) (i := 21) (ef := -1) (eg := -1)
    (dm := false) (ts := false)
    (A := (213/40 : ℝ)) (B := (-117 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p11_7 : ∀ x : ℝ, (440/37 : ℝ) < x → x < (12 : ℝ) →
    RR x = (199/20 : ℝ) * x + (-172 : ℝ) :=
  RR_affine_on (l := (440/37 : ℝ)) (r := (12 : ℝ)) (n := 11) (m := 0) (k := 27)
    (j := 23) (i := 22) (ef := -1) (eg := -1)
    (dm := true) (ts := false)
    (A := (199/20 : ℝ)) (B := (-172 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

/-- **Table 3**, row `j = 11` (p. 27):
`∫_{11}^{12} R(x) x^(-3) dx = -3236921227/87524236800`. -/
theorem table3_11 :
    IntervalIntegrable (fun x => RR x / x ^ 3) volume (11:ℝ) (12:ℝ)
      ∧ (∫ x in (11:ℝ)..(12:ℝ), RR x / x ^ 3) = (-3236921227/87524236800 : ℝ) := by
  have h := chain_integral [((480/43 : ℝ), (8 : ℝ), (-147 : ℝ)), ((260/23 : ℝ), (191/40 : ℝ), (-111 : ℝ)), ((420/37 : ℝ), (29/8 : ℝ), (-98 : ℝ)), ((23/2 : ℝ), (219/40 : ℝ), (-119 : ℝ)), ((500/43 : ℝ), (259/40 : ℝ), (-261/2 : ℝ)), ((270/23 : ℝ), (259/40 : ℝ), (-261/2 : ℝ)), ((440/37 : ℝ), (213/40 : ℝ), (-117 : ℝ)), ((12 : ℝ), (199/20 : ℝ), (-172 : ℝ))] (11:ℝ) (by norm_num)
    ⟨by norm_num, by norm_num, p11_0, by norm_num, by norm_num, p11_1, by norm_num, by norm_num, p11_2, by norm_num, by norm_num, p11_3, by norm_num, by norm_num, p11_4, by norm_num, by norm_num, p11_5, by norm_num, by norm_num, p11_6, by norm_num, by norm_num, p11_7, trivial⟩
  simp only [chainEnd] at h
  exact ⟨h.1, by rw [h.2]; norm_num [chainVal]⟩

/-! ### Table 3, row `j = 12`: the 8 intervals of (B.2) inside `[12,13]` -/

lemma p12_0 : ∀ x : ℝ, (12 : ℝ) < x → x < (520/43 : ℝ) →
    RR x = (91/10 : ℝ) * x + (-184 : ℝ) :=
  RR_affine_on (l := (12 : ℝ)) (r := (520/43 : ℝ)) (n := 12) (m := 0) (k := 27)
    (j := 24) (i := 22) (ef := 1) (eg := -1)
    (dm := true) (ts := true)
    (A := (91/10 : ℝ)) (B := (-184 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p12_1 : ∀ x : ℝ, (520/43 : ℝ) < x → x < (280/23 : ℝ) →
    RR x = (47/8 : ℝ) * x + (-145 : ℝ) :=
  RR_affine_on (l := (520/43 : ℝ)) (r := (280/23 : ℝ)) (n := 12) (m := 0) (k := 27)
    (j := 24) (i := 22) (ef := 1) (eg := -1)
    (dm := false) (ts := true)
    (A := (47/8 : ℝ)) (B := (-145 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p12_2 : ∀ x : ℝ, (280/23 : ℝ) < x → x < (460/37 : ℝ) →
    RR x = (189/40 : ℝ) * x + (-131 : ℝ) :=
  RR_affine_on (l := (280/23 : ℝ)) (r := (460/37 : ℝ)) (n := 12) (m := 0) (k := 28)
    (j := 24) (i := 22) (ef := 1) (eg := -1)
    (dm := false) (ts := false)
    (A := (189/40 : ℝ)) (B := (-131 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p12_3 : ∀ x : ℝ, (460/37 : ℝ) < x → x < (25/2 : ℝ) →
    RR x = (263/40 : ℝ) * x + (-154 : ℝ) :=
  RR_affine_on (l := (460/37 : ℝ)) (r := (25/2 : ℝ)) (n := 12) (m := 0) (k := 28)
    (j := 24) (i := 23) (ef := 1) (eg := -1)
    (dm := false) (ts := false)
    (A := (263/40 : ℝ)) (B := (-154 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p12_4 : ∀ x : ℝ, (25/2 : ℝ) < x → x < (540/43 : ℝ) →
    RR x = (303/40 : ℝ) * x + (-333/2 : ℝ) :=
  RR_affine_on (l := (25/2 : ℝ)) (r := (540/43 : ℝ)) (n := 12) (m := 0) (k := 28)
    (j := 25) (i := 23) (ef := -1) (eg := -1)
    (dm := false) (ts := true)
    (A := (303/40 : ℝ)) (B := (-333/2 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p12_5 : ∀ x : ℝ, (540/43 : ℝ) < x → x < (290/23 : ℝ) →
    RR x = (303/40 : ℝ) * x + (-333/2 : ℝ) :=
  RR_affine_on (l := (540/43 : ℝ)) (r := (290/23 : ℝ)) (n := 12) (m := 0) (k := 28)
    (j := 25) (i := 23) (ef := -1) (eg := -1)
    (dm := false) (ts := true)
    (A := (303/40 : ℝ)) (B := (-333/2 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p12_6 : ∀ x : ℝ, (290/23 : ℝ) < x → x < (480/37 : ℝ) →
    RR x = (257/40 : ℝ) * x + (-152 : ℝ) :=
  RR_affine_on (l := (290/23 : ℝ)) (r := (480/37 : ℝ)) (n := 12) (m := 0) (k := 29)
    (j := 25) (i := 23) (ef := -1) (eg := -1)
    (dm := false) (ts := false)
    (A := (257/40 : ℝ)) (B := (-152 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p12_7 : ∀ x : ℝ, (480/37 : ℝ) < x → x < (13 : ℝ) →
    RR x = (221/20 : ℝ) * x + (-212 : ℝ) :=
  RR_affine_on (l := (480/37 : ℝ)) (r := (13 : ℝ)) (n := 12) (m := 0) (k := 29)
    (j := 25) (i := 24) (ef := -1) (eg := -1)
    (dm := true) (ts := false)
    (A := (221/20 : ℝ)) (B := (-212 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

/-- **Table 3**, row `j = 12` (p. 27):
`∫_{12}^{13} R(x) x^(-3) dx = -3350220001/90899827200`. -/
theorem table3_12 :
    IntervalIntegrable (fun x => RR x / x ^ 3) volume (12:ℝ) (13:ℝ)
      ∧ (∫ x in (12:ℝ)..(13:ℝ), RR x / x ^ 3) = (-3350220001/90899827200 : ℝ) := by
  have h := chain_integral [((520/43 : ℝ), (91/10 : ℝ), (-184 : ℝ)), ((280/23 : ℝ), (47/8 : ℝ), (-145 : ℝ)), ((460/37 : ℝ), (189/40 : ℝ), (-131 : ℝ)), ((25/2 : ℝ), (263/40 : ℝ), (-154 : ℝ)), ((540/43 : ℝ), (303/40 : ℝ), (-333/2 : ℝ)), ((290/23 : ℝ), (303/40 : ℝ), (-333/2 : ℝ)), ((480/37 : ℝ), (257/40 : ℝ), (-152 : ℝ)), ((13 : ℝ), (221/20 : ℝ), (-212 : ℝ))] (12:ℝ) (by norm_num)
    ⟨by norm_num, by norm_num, p12_0, by norm_num, by norm_num, p12_1, by norm_num, by norm_num, p12_2, by norm_num, by norm_num, p12_3, by norm_num, by norm_num, p12_4, by norm_num, by norm_num, p12_5, by norm_num, by norm_num, p12_6, by norm_num, by norm_num, p12_7, trivial⟩
  simp only [chainEnd] at h
  exact ⟨h.1, by rw [h.2]; norm_num [chainVal]⟩

/-! ### Table 3, row `j = 13`: the 10 intervals of (B.2) inside `[13,14]` -/

lemma p13_0 : ∀ x : ℝ, (13 : ℝ) < x → x < (560/43 : ℝ) →
    RR x = (51/5 : ℝ) * x + (-225 : ℝ) :=
  RR_affine_on (l := (13 : ℝ)) (r := (560/43 : ℝ)) (n := 13) (m := 0) (k := 29)
    (j := 26) (i := 24) (ef := 1) (eg := -1)
    (dm := true) (ts := true)
    (A := (51/5 : ℝ)) (B := (-225 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p13_1 : ∀ x : ℝ, (560/43 : ℝ) < x → x < (300/23 : ℝ) →
    RR x = (279/40 : ℝ) * x + (-183 : ℝ) :=
  RR_affine_on (l := (560/43 : ℝ)) (r := (300/23 : ℝ)) (n := 13) (m := 0) (k := 29)
    (j := 26) (i := 24) (ef := 1) (eg := -1)
    (dm := false) (ts := true)
    (A := (279/40 : ℝ)) (B := (-183 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p13_2 : ∀ x : ℝ, (300/23 : ℝ) < x → x < (40/3 : ℝ) →
    RR x = (233/40 : ℝ) * x + (-168 : ℝ) :=
  RR_affine_on (l := (300/23 : ℝ)) (r := (40/3 : ℝ)) (n := 13) (m := 0) (k := 30)
    (j := 26) (i := 24) (ef := 1) (eg := -1)
    (dm := false) (ts := false)
    (A := (233/40 : ℝ)) (B := (-168 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p13_3 : ∀ x : ℝ, (40/3 : ℝ) < x → x < (310/23 : ℝ) →
    RR x = (145/8 : ℝ) * x + (-184 : ℝ) :=
  RR_affine_on (l := (40/3 : ℝ)) (r := (310/23 : ℝ)) (n := 13) (m := 1) (k := 30)
    (j := 26) (i := 24) (ef := 1) (eg := 1)
    (dm := false) (ts := true)
    (A := (145/8 : ℝ)) (B := (-184 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p13_4 : ∀ x : ℝ, (310/23 : ℝ) < x → x < (580/43 : ℝ) →
    RR x = (679/40 : ℝ) * x + (-337/2 : ℝ) :=
  RR_affine_on (l := (310/23 : ℝ)) (r := (580/43 : ℝ)) (n := 13) (m := 1) (k := 31)
    (j := 26) (i := 24) (ef := 1) (eg := 1)
    (dm := false) (ts := false)
    (A := (679/40 : ℝ)) (B := (-337/2 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p13_5 : ∀ x : ℝ, (580/43 : ℝ) < x → x < (27/2 : ℝ) →
    RR x = (679/40 : ℝ) * x + (-337/2 : ℝ) :=
  RR_affine_on (l := (580/43 : ℝ)) (r := (27/2 : ℝ)) (n := 13) (m := 1) (k := 31)
    (j := 26) (i := 24) (ef := 1) (eg := 1)
    (dm := false) (ts := false)
    (A := (679/40 : ℝ)) (B := (-337/2 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p13_6 : ∀ x : ℝ, (27/2 : ℝ) < x → x < (500/37 : ℝ) →
    RR x = (719/40 : ℝ) * x + (-182 : ℝ) :=
  RR_affine_on (l := (27/2 : ℝ)) (r := (500/37 : ℝ)) (n := 13) (m := 1) (k := 31)
    (j := 27) (i := 24) (ef := -1) (eg := 1)
    (dm := false) (ts := true)
    (A := (719/40 : ℝ)) (B := (-182 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p13_7 : ∀ x : ℝ, (500/37 : ℝ) < x → x < (320/23 : ℝ) →
    RR x = (793/40 : ℝ) * x + (-207 : ℝ) :=
  RR_affine_on (l := (500/37 : ℝ)) (r := (320/23 : ℝ)) (n := 13) (m := 1) (k := 31)
    (j := 27) (i := 25) (ef := -1) (eg := 1)
    (dm := false) (ts := true)
    (A := (793/40 : ℝ)) (B := (-207 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p13_8 : ∀ x : ℝ, (320/23 : ℝ) < x → x < (600/43 : ℝ) →
    RR x = (747/40 : ℝ) * x + (-191 : ℝ) :=
  RR_affine_on (l := (320/23 : ℝ)) (r := (600/43 : ℝ)) (n := 13) (m := 1) (k := 32)
    (j := 27) (i := 25) (ef := -1) (eg := 1)
    (dm := false) (ts := false)
    (A := (747/40 : ℝ)) (B := (-191 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p13_9 : ∀ x : ℝ, (600/43 : ℝ) < x → x < (14 : ℝ) →
    RR x = (309/20 : ℝ) * x + (-146 : ℝ) :=
  RR_affine_on (l := (600/43 : ℝ)) (r := (14 : ℝ)) (n := 13) (m := 1) (k := 32)
    (j := 27) (i := 25) (ef := -1) (eg := 1)
    (dm := true) (ts := false)
    (A := (309/20 : ℝ)) (B := (-146 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

/-- **Table 3**, row `j = 13` (p. 27):
`∫_{13}^{14} R(x) x^(-3) dx = 7424224373/2217983040000`. -/
theorem table3_13 :
    IntervalIntegrable (fun x => RR x / x ^ 3) volume (13:ℝ) (14:ℝ)
      ∧ (∫ x in (13:ℝ)..(14:ℝ), RR x / x ^ 3) = (7424224373/2217983040000 : ℝ) := by
  have h := chain_integral [((560/43 : ℝ), (51/5 : ℝ), (-225 : ℝ)), ((300/23 : ℝ), (279/40 : ℝ), (-183 : ℝ)), ((40/3 : ℝ), (233/40 : ℝ), (-168 : ℝ)), ((310/23 : ℝ), (145/8 : ℝ), (-184 : ℝ)), ((580/43 : ℝ), (679/40 : ℝ), (-337/2 : ℝ)), ((27/2 : ℝ), (679/40 : ℝ), (-337/2 : ℝ)), ((500/37 : ℝ), (719/40 : ℝ), (-182 : ℝ)), ((320/23 : ℝ), (793/40 : ℝ), (-207 : ℝ)), ((600/43 : ℝ), (747/40 : ℝ), (-191 : ℝ)), ((14 : ℝ), (309/20 : ℝ), (-146 : ℝ))] (13:ℝ) (by norm_num)
    ⟨by norm_num, by norm_num, p13_0, by norm_num, by norm_num, p13_1, by norm_num, by norm_num, p13_2, by norm_num, by norm_num, p13_3, by norm_num, by norm_num, p13_4, by norm_num, by norm_num, p13_5, by norm_num, by norm_num, p13_6, by norm_num, by norm_num, p13_7, by norm_num, by norm_num, p13_8, by norm_num, by norm_num, p13_9, trivial⟩
  simp only [chainEnd] at h
  exact ⟨h.1, by rw [h.2]; norm_num [chainVal]⟩

/-! ### Table 3, row `j = 14`: the 8 intervals of (B.2) inside `[14,15]` -/

lemma p14_0 : ∀ x : ℝ, (14 : ℝ) < x → x < (520/37 : ℝ) →
    RR x = (73/5 : ℝ) * x + (-160 : ℝ) :=
  RR_affine_on (l := (14 : ℝ)) (r := (520/37 : ℝ)) (n := 14) (m := 1) (k := 32)
    (j := 28) (i := 25) (ef := 1) (eg := 1)
    (dm := true) (ts := true)
    (A := (73/5 : ℝ)) (B := (-160 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p14_1 : ∀ x : ℝ, (520/37 : ℝ) < x → x < (330/23 : ℝ) →
    RR x = (769/40 : ℝ) * x + (-225 : ℝ) :=
  RR_affine_on (l := (520/37 : ℝ)) (r := (330/23 : ℝ)) (n := 14) (m := 1) (k := 32)
    (j := 28) (i := 26) (ef := 1) (eg := 1)
    (dm := false) (ts := true)
    (A := (769/40 : ℝ)) (B := (-225 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p14_2 : ∀ x : ℝ, (330/23 : ℝ) < x → x < (620/43 : ℝ) →
    RR x = (723/40 : ℝ) * x + (-417/2 : ℝ) :=
  RR_affine_on (l := (330/23 : ℝ)) (r := (620/43 : ℝ)) (n := 14) (m := 1) (k := 33)
    (j := 28) (i := 26) (ef := 1) (eg := 1)
    (dm := false) (ts := false)
    (A := (723/40 : ℝ)) (B := (-417/2 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p14_3 : ∀ x : ℝ, (620/43 : ℝ) < x → x < (29/2 : ℝ) →
    RR x = (723/40 : ℝ) * x + (-417/2 : ℝ) :=
  RR_affine_on (l := (620/43 : ℝ)) (r := (29/2 : ℝ)) (n := 14) (m := 1) (k := 33)
    (j := 28) (i := 26) (ef := 1) (eg := 1)
    (dm := false) (ts := false)
    (A := (723/40 : ℝ)) (B := (-417/2 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p14_4 : ∀ x : ℝ, (29/2 : ℝ) < x → x < (540/37 : ℝ) →
    RR x = (763/40 : ℝ) * x + (-223 : ℝ) :=
  RR_affine_on (l := (29/2 : ℝ)) (r := (540/37 : ℝ)) (n := 14) (m := 1) (k := 33)
    (j := 29) (i := 26) (ef := -1) (eg := 1)
    (dm := false) (ts := true)
    (A := (763/40 : ℝ)) (B := (-223 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p14_5 : ∀ x : ℝ, (540/37 : ℝ) < x → x < (340/23 : ℝ) →
    RR x = (837/40 : ℝ) * x + (-250 : ℝ) :=
  RR_affine_on (l := (540/37 : ℝ)) (r := (340/23 : ℝ)) (n := 14) (m := 1) (k := 33)
    (j := 29) (i := 27) (ef := -1) (eg := 1)
    (dm := false) (ts := true)
    (A := (837/40 : ℝ)) (B := (-250 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p14_6 : ∀ x : ℝ, (340/23 : ℝ) < x → x < (640/43 : ℝ) →
    RR x = (791/40 : ℝ) * x + (-233 : ℝ) :=
  RR_affine_on (l := (340/23 : ℝ)) (r := (640/43 : ℝ)) (n := 14) (m := 1) (k := 34)
    (j := 29) (i := 27) (ef := -1) (eg := 1)
    (dm := false) (ts := false)
    (A := (791/40 : ℝ)) (B := (-233 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p14_7 : ∀ x : ℝ, (640/43 : ℝ) < x → x < (15 : ℝ) →
    RR x = (331/20 : ℝ) * x + (-185 : ℝ) :=
  RR_affine_on (l := (640/43 : ℝ)) (r := (15 : ℝ)) (n := 14) (m := 1) (k := 34)
    (j := 29) (i := 27) (ef := -1) (eg := 1)
    (dm := true) (ts := false)
    (A := (331/20 : ℝ)) (B := (-185 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

/-- **Table 3**, row `j = 14` (p. 27):
`∫_{14}^{15} R(x) x^(-3) dx = 16775764609/955086612480`. -/
theorem table3_14 :
    IntervalIntegrable (fun x => RR x / x ^ 3) volume (14:ℝ) (15:ℝ)
      ∧ (∫ x in (14:ℝ)..(15:ℝ), RR x / x ^ 3) = (16775764609/955086612480 : ℝ) := by
  have h := chain_integral [((520/37 : ℝ), (73/5 : ℝ), (-160 : ℝ)), ((330/23 : ℝ), (769/40 : ℝ), (-225 : ℝ)), ((620/43 : ℝ), (723/40 : ℝ), (-417/2 : ℝ)), ((29/2 : ℝ), (723/40 : ℝ), (-417/2 : ℝ)), ((540/37 : ℝ), (763/40 : ℝ), (-223 : ℝ)), ((340/23 : ℝ), (837/40 : ℝ), (-250 : ℝ)), ((640/43 : ℝ), (791/40 : ℝ), (-233 : ℝ)), ((15 : ℝ), (331/20 : ℝ), (-185 : ℝ))] (14:ℝ) (by norm_num)
    ⟨by norm_num, by norm_num, p14_0, by norm_num, by norm_num, p14_1, by norm_num, by norm_num, p14_2, by norm_num, by norm_num, p14_3, by norm_num, by norm_num, p14_4, by norm_num, by norm_num, p14_5, by norm_num, by norm_num, p14_6, by norm_num, by norm_num, p14_7, trivial⟩
  simp only [chainEnd] at h
  exact ⟨h.1, by rw [h.2]; norm_num [chainVal]⟩

/-! ### Table 3, row `j = 15`: the 8 intervals of (B.2) inside `[15,16]` -/

lemma p15_0 : ∀ x : ℝ, (15 : ℝ) < x → x < (560/37 : ℝ) →
    RR x = (157/10 : ℝ) * x + (-200 : ℝ) :=
  RR_affine_on (l := (15 : ℝ)) (r := (560/37 : ℝ)) (n := 15) (m := 1) (k := 34)
    (j := 30) (i := 27) (ef := 1) (eg := 1)
    (dm := true) (ts := true)
    (A := (157/10 : ℝ)) (B := (-200 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p15_1 : ∀ x : ℝ, (560/37 : ℝ) < x → x < (350/23 : ℝ) →
    RR x = (813/40 : ℝ) * x + (-270 : ℝ) :=
  RR_affine_on (l := (560/37 : ℝ)) (r := (350/23 : ℝ)) (n := 15) (m := 1) (k := 34)
    (j := 30) (i := 28) (ef := 1) (eg := 1)
    (dm := false) (ts := true)
    (A := (813/40 : ℝ)) (B := (-270 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p15_2 : ∀ x : ℝ, (350/23 : ℝ) < x → x < (660/43 : ℝ) →
    RR x = (767/40 : ℝ) * x + (-505/2 : ℝ) :=
  RR_affine_on (l := (350/23 : ℝ)) (r := (660/43 : ℝ)) (n := 15) (m := 1) (k := 35)
    (j := 30) (i := 28) (ef := 1) (eg := 1)
    (dm := false) (ts := false)
    (A := (767/40 : ℝ)) (B := (-505/2 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p15_3 : ∀ x : ℝ, (660/43 : ℝ) < x → x < (31/2 : ℝ) →
    RR x = (767/40 : ℝ) * x + (-505/2 : ℝ) :=
  RR_affine_on (l := (660/43 : ℝ)) (r := (31/2 : ℝ)) (n := 15) (m := 1) (k := 35)
    (j := 30) (i := 28) (ef := 1) (eg := 1)
    (dm := false) (ts := false)
    (A := (767/40 : ℝ)) (B := (-505/2 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p15_4 : ∀ x : ℝ, (31/2 : ℝ) < x → x < (360/23 : ℝ) →
    RR x = (807/40 : ℝ) * x + (-268 : ℝ) :=
  RR_affine_on (l := (31/2 : ℝ)) (r := (360/23 : ℝ)) (n := 15) (m := 1) (k := 35)
    (j := 31) (i := 28) (ef := -1) (eg := 1)
    (dm := false) (ts := true)
    (A := (807/40 : ℝ)) (B := (-268 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p15_5 : ∀ x : ℝ, (360/23 : ℝ) < x → x < (580/37 : ℝ) →
    RR x = (761/40 : ℝ) * x + (-250 : ℝ) :=
  RR_affine_on (l := (360/23 : ℝ)) (r := (580/37 : ℝ)) (n := 15) (m := 1) (k := 36)
    (j := 31) (i := 28) (ef := -1) (eg := 1)
    (dm := false) (ts := false)
    (A := (761/40 : ℝ)) (B := (-250 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p15_6 : ∀ x : ℝ, (580/37 : ℝ) < x → x < (680/43 : ℝ) →
    RR x = (167/8 : ℝ) * x + (-279 : ℝ) :=
  RR_affine_on (l := (580/37 : ℝ)) (r := (680/43 : ℝ)) (n := 15) (m := 1) (k := 36)
    (j := 31) (i := 29) (ef := -1) (eg := 1)
    (dm := false) (ts := false)
    (A := (167/8 : ℝ)) (B := (-279 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p15_7 : ∀ x : ℝ, (680/43 : ℝ) < x → x < (16 : ℝ) →
    RR x = (353/20 : ℝ) * x + (-228 : ℝ) :=
  RR_affine_on (l := (680/43 : ℝ)) (r := (16 : ℝ)) (n := 15) (m := 1) (k := 36)
    (j := 31) (i := 29) (ef := -1) (eg := 1)
    (dm := true) (ts := false)
    (A := (353/20 : ℝ)) (B := (-228 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

/-- **Table 3**, row `j = 15` (p. 27):
`∫_{15}^{16} R(x) x^(-3) dx = 369043847/30810528000`. -/
theorem table3_15 :
    IntervalIntegrable (fun x => RR x / x ^ 3) volume (15:ℝ) (16:ℝ)
      ∧ (∫ x in (15:ℝ)..(16:ℝ), RR x / x ^ 3) = (369043847/30810528000 : ℝ) := by
  have h := chain_integral [((560/37 : ℝ), (157/10 : ℝ), (-200 : ℝ)), ((350/23 : ℝ), (813/40 : ℝ), (-270 : ℝ)), ((660/43 : ℝ), (767/40 : ℝ), (-505/2 : ℝ)), ((31/2 : ℝ), (767/40 : ℝ), (-505/2 : ℝ)), ((360/23 : ℝ), (807/40 : ℝ), (-268 : ℝ)), ((580/37 : ℝ), (761/40 : ℝ), (-250 : ℝ)), ((680/43 : ℝ), (167/8 : ℝ), (-279 : ℝ)), ((16 : ℝ), (353/20 : ℝ), (-228 : ℝ))] (15:ℝ) (by norm_num)
    ⟨by norm_num, by norm_num, p15_0, by norm_num, by norm_num, p15_1, by norm_num, by norm_num, p15_2, by norm_num, by norm_num, p15_3, by norm_num, by norm_num, p15_4, by norm_num, by norm_num, p15_5, by norm_num, by norm_num, p15_6, by norm_num, by norm_num, p15_7, trivial⟩
  simp only [chainEnd] at h
  exact ⟨h.1, by rw [h.2]; norm_num [chainVal]⟩

/-! ### Table 3, row `j = 16`: the 10 intervals of (B.2) inside `[16,17]` -/

lemma p16_0 : ∀ x : ℝ, (16 : ℝ) < x → x < (370/23 : ℝ) →
    RR x = (84/5 : ℝ) * x + (-244 : ℝ) :=
  RR_affine_on (l := (16 : ℝ)) (r := (370/23 : ℝ)) (n := 16) (m := 1) (k := 36)
    (j := 32) (i := 29) (ef := 1) (eg := 1)
    (dm := true) (ts := true)
    (A := (84/5 : ℝ)) (B := (-244 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p16_1 : ∀ x : ℝ, (370/23 : ℝ) < x → x < (600/37 : ℝ) →
    RR x = (313/20 : ℝ) * x + (-451/2 : ℝ) :=
  RR_affine_on (l := (370/23 : ℝ)) (r := (600/37 : ℝ)) (n := 16) (m := 1) (k := 37)
    (j := 32) (i := 29) (ef := 1) (eg := 1)
    (dm := true) (ts := false)
    (A := (313/20 : ℝ)) (B := (-451/2 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p16_2 : ∀ x : ℝ, (600/37 : ℝ) < x → x < (700/43 : ℝ) →
    RR x = (811/40 : ℝ) * x + (-601/2 : ℝ) :=
  RR_affine_on (l := (600/37 : ℝ)) (r := (700/43 : ℝ)) (n := 16) (m := 1) (k := 37)
    (j := 32) (i := 30) (ef := 1) (eg := 1)
    (dm := false) (ts := false)
    (A := (811/40 : ℝ)) (B := (-601/2 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p16_3 : ∀ x : ℝ, (700/43 : ℝ) < x → x < (33/2 : ℝ) →
    RR x = (811/40 : ℝ) * x + (-601/2 : ℝ) :=
  RR_affine_on (l := (700/43 : ℝ)) (r := (33/2 : ℝ)) (n := 16) (m := 1) (k := 37)
    (j := 32) (i := 30) (ef := 1) (eg := 1)
    (dm := false) (ts := false)
    (A := (811/40 : ℝ)) (B := (-601/2 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p16_4 : ∀ x : ℝ, (33/2 : ℝ) < x → x < (380/23 : ℝ) →
    RR x = (851/40 : ℝ) * x + (-317 : ℝ) :=
  RR_affine_on (l := (33/2 : ℝ)) (r := (380/23 : ℝ)) (n := 16) (m := 1) (k := 37)
    (j := 33) (i := 30) (ef := -1) (eg := 1)
    (dm := false) (ts := true)
    (A := (851/40 : ℝ)) (B := (-317 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p16_5 : ∀ x : ℝ, (380/23 : ℝ) < x → x < (50/3 : ℝ) →
    RR x = (161/8 : ℝ) * x + (-298 : ℝ) :=
  RR_affine_on (l := (380/23 : ℝ)) (r := (50/3 : ℝ)) (n := 16) (m := 1) (k := 38)
    (j := 33) (i := 30) (ef := -1) (eg := 1)
    (dm := false) (ts := false)
    (A := (161/8 : ℝ)) (B := (-298 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p16_6 : ∀ x : ℝ, (50/3 : ℝ) < x → x < (720/43 : ℝ) →
    RR x = (799/40 : ℝ) * x + (-591/2 : ℝ) :=
  RR_affine_on (l := (50/3 : ℝ)) (r := (720/43 : ℝ)) (n := 16) (m := 1) (k := 38)
    (j := 33) (i := 30) (ef := -1) (eg := 1)
    (dm := false) (ts := true)
    (A := (799/40 : ℝ)) (B := (-591/2 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p16_7 : ∀ x : ℝ, (720/43 : ℝ) < x → x < (620/37 : ℝ) →
    RR x = (67/4 : ℝ) * x + (-483/2 : ℝ) :=
  RR_affine_on (l := (720/43 : ℝ)) (r := (620/37 : ℝ)) (n := 16) (m := 1) (k := 38)
    (j := 33) (i := 30) (ef := -1) (eg := 1)
    (dm := true) (ts := true)
    (A := (67/4 : ℝ)) (B := (-483/2 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p16_8 : ∀ x : ℝ, (620/37 : ℝ) < x → x < (390/23 : ℝ) →
    RR x = (93/5 : ℝ) * x + (-545/2 : ℝ) :=
  RR_affine_on (l := (620/37 : ℝ)) (r := (390/23 : ℝ)) (n := 16) (m := 1) (k := 38)
    (j := 33) (i := 31) (ef := -1) (eg := 1)
    (dm := true) (ts := true)
    (A := (93/5 : ℝ)) (B := (-545/2 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p16_9 : ∀ x : ℝ, (390/23 : ℝ) < x → x < (17 : ℝ) →
    RR x = (349/20 : ℝ) * x + (-253 : ℝ) :=
  RR_affine_on (l := (390/23 : ℝ)) (r := (17 : ℝ)) (n := 16) (m := 1) (k := 39)
    (j := 33) (i := 31) (ef := -1) (eg := 1)
    (dm := true) (ts := false)
    (A := (349/20 : ℝ)) (B := (-253 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

/-- **Table 3**, row `j = 16` (p. 27):
`∫_{16}^{17} R(x) x^(-3) dx = 651380108633/86461373856000`. -/
theorem table3_16 :
    IntervalIntegrable (fun x => RR x / x ^ 3) volume (16:ℝ) (17:ℝ)
      ∧ (∫ x in (16:ℝ)..(17:ℝ), RR x / x ^ 3) = (651380108633/86461373856000 : ℝ) := by
  have h := chain_integral [((370/23 : ℝ), (84/5 : ℝ), (-244 : ℝ)), ((600/37 : ℝ), (313/20 : ℝ), (-451/2 : ℝ)), ((700/43 : ℝ), (811/40 : ℝ), (-601/2 : ℝ)), ((33/2 : ℝ), (811/40 : ℝ), (-601/2 : ℝ)), ((380/23 : ℝ), (851/40 : ℝ), (-317 : ℝ)), ((50/3 : ℝ), (161/8 : ℝ), (-298 : ℝ)), ((720/43 : ℝ), (799/40 : ℝ), (-591/2 : ℝ)), ((620/37 : ℝ), (67/4 : ℝ), (-483/2 : ℝ)), ((390/23 : ℝ), (93/5 : ℝ), (-545/2 : ℝ)), ((17 : ℝ), (349/20 : ℝ), (-253 : ℝ))] (16:ℝ) (by norm_num)
    ⟨by norm_num, by norm_num, p16_0, by norm_num, by norm_num, p16_1, by norm_num, by norm_num, p16_2, by norm_num, by norm_num, p16_3, by norm_num, by norm_num, p16_4, by norm_num, by norm_num, p16_5, by norm_num, by norm_num, p16_6, by norm_num, by norm_num, p16_7, by norm_num, by norm_num, p16_8, by norm_num, by norm_num, p16_9, trivial⟩
  simp only [chainEnd] at h
  exact ⟨h.1, by rw [h.2]; norm_num [chainVal]⟩

/-! ### Table 3, row `j = 17`: the 8 intervals of (B.2) inside `[17,18]` -/

lemma p17_0 : ∀ x : ℝ, (17 : ℝ) < x → x < (740/43 : ℝ) →
    RR x = (83/5 : ℝ) * x + (-270 : ℝ) :=
  RR_affine_on (l := (17 : ℝ)) (r := (740/43 : ℝ)) (n := 17) (m := 1) (k := 39)
    (j := 34) (i := 31) (ef := 1) (eg := 1)
    (dm := true) (ts := true)
    (A := (83/5 : ℝ)) (B := (-270 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p17_1 : ∀ x : ℝ, (740/43 : ℝ) < x → x < (640/37 : ℝ) →
    RR x = (83/5 : ℝ) * x + (-270 : ℝ) :=
  RR_affine_on (l := (740/43 : ℝ)) (r := (640/37 : ℝ)) (n := 17) (m := 1) (k := 39)
    (j := 34) (i := 31) (ef := 1) (eg := 1)
    (dm := true) (ts := true)
    (A := (83/5 : ℝ)) (B := (-270 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p17_2 : ∀ x : ℝ, (640/37 : ℝ) < x → x < (400/23 : ℝ) →
    RR x = (849/40 : ℝ) * x + (-350 : ℝ) :=
  RR_affine_on (l := (640/37 : ℝ)) (r := (400/23 : ℝ)) (n := 17) (m := 1) (k := 39)
    (j := 34) (i := 32) (ef := 1) (eg := 1)
    (dm := false) (ts := true)
    (A := (849/40 : ℝ)) (B := (-350 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p17_3 : ∀ x : ℝ, (400/23 : ℝ) < x → x < (35/2 : ℝ) →
    RR x = (803/40 : ℝ) * x + (-330 : ℝ) :=
  RR_affine_on (l := (400/23 : ℝ)) (r := (35/2 : ℝ)) (n := 17) (m := 1) (k := 40)
    (j := 34) (i := 32) (ef := 1) (eg := 1)
    (dm := false) (ts := false)
    (A := (803/40 : ℝ)) (B := (-330 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p17_4 : ∀ x : ℝ, (35/2 : ℝ) < x → x < (760/43 : ℝ) →
    RR x = (843/40 : ℝ) * x + (-695/2 : ℝ) :=
  RR_affine_on (l := (35/2 : ℝ)) (r := (760/43 : ℝ)) (n := 17) (m := 1) (k := 40)
    (j := 35) (i := 32) (ef := -1) (eg := 1)
    (dm := false) (ts := true)
    (A := (843/40 : ℝ)) (B := (-695/2 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p17_5 : ∀ x : ℝ, (760/43 : ℝ) < x → x < (410/23 : ℝ) →
    RR x = (357/20 : ℝ) * x + (-581/2 : ℝ) :=
  RR_affine_on (l := (760/43 : ℝ)) (r := (410/23 : ℝ)) (n := 17) (m := 1) (k := 40)
    (j := 35) (i := 32) (ef := -1) (eg := 1)
    (dm := true) (ts := true)
    (A := (357/20 : ℝ)) (B := (-581/2 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p17_6 : ∀ x : ℝ, (410/23 : ℝ) < x → x < (660/37 : ℝ) →
    RR x = (167/10 : ℝ) * x + (-270 : ℝ) :=
  RR_affine_on (l := (410/23 : ℝ)) (r := (660/37 : ℝ)) (n := 17) (m := 1) (k := 41)
    (j := 35) (i := 32) (ef := -1) (eg := 1)
    (dm := true) (ts := false)
    (A := (167/10 : ℝ)) (B := (-270 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p17_7 : ∀ x : ℝ, (660/37 : ℝ) < x → x < (18 : ℝ) →
    RR x = (371/20 : ℝ) * x + (-303 : ℝ) :=
  RR_affine_on (l := (660/37 : ℝ)) (r := (18 : ℝ)) (n := 17) (m := 1) (k := 41)
    (j := 35) (i := 33) (ef := -1) (eg := 1)
    (dm := true) (ts := false)
    (A := (371/20 : ℝ)) (B := (-303 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

/-- **Table 3**, row `j = 17` (p. 27):
`∫_{17}^{18} R(x) x^(-3) dx = 472851276229/119820121344000`. -/
theorem table3_17 :
    IntervalIntegrable (fun x => RR x / x ^ 3) volume (17:ℝ) (18:ℝ)
      ∧ (∫ x in (17:ℝ)..(18:ℝ), RR x / x ^ 3) = (472851276229/119820121344000 : ℝ) := by
  have h := chain_integral [((740/43 : ℝ), (83/5 : ℝ), (-270 : ℝ)), ((640/37 : ℝ), (83/5 : ℝ), (-270 : ℝ)), ((400/23 : ℝ), (849/40 : ℝ), (-350 : ℝ)), ((35/2 : ℝ), (803/40 : ℝ), (-330 : ℝ)), ((760/43 : ℝ), (843/40 : ℝ), (-695/2 : ℝ)), ((410/23 : ℝ), (357/20 : ℝ), (-581/2 : ℝ)), ((660/37 : ℝ), (167/10 : ℝ), (-270 : ℝ)), ((18 : ℝ), (371/20 : ℝ), (-303 : ℝ))] (17:ℝ) (by norm_num)
    ⟨by norm_num, by norm_num, p17_0, by norm_num, by norm_num, p17_1, by norm_num, by norm_num, p17_2, by norm_num, by norm_num, p17_3, by norm_num, by norm_num, p17_4, by norm_num, by norm_num, p17_5, by norm_num, by norm_num, p17_6, by norm_num, by norm_num, p17_7, trivial⟩
  simp only [chainEnd] at h
  exact ⟨h.1, by rw [h.2]; norm_num [chainVal]⟩

/-! ### Table 3, row `j = 18`: the 8 intervals of (B.2) inside `[18,19]` -/

lemma p18_0 : ∀ x : ℝ, (18 : ℝ) < x → x < (780/43 : ℝ) →
    RR x = (177/10 : ℝ) * x + (-321 : ℝ) :=
  RR_affine_on (l := (18 : ℝ)) (r := (780/43 : ℝ)) (n := 18) (m := 1) (k := 41)
    (j := 36) (i := 33) (ef := 1) (eg := 1)
    (dm := true) (ts := true)
    (A := (177/10 : ℝ)) (B := (-321 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p18_1 : ∀ x : ℝ, (780/43 : ℝ) < x → x < (420/23 : ℝ) →
    RR x = (177/10 : ℝ) * x + (-321 : ℝ) :=
  RR_affine_on (l := (780/43 : ℝ)) (r := (420/23 : ℝ)) (n := 18) (m := 1) (k := 41)
    (j := 36) (i := 33) (ef := 1) (eg := 1)
    (dm := true) (ts := true)
    (A := (177/10 : ℝ)) (B := (-321 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p18_2 : ∀ x : ℝ, (420/23 : ℝ) < x → x < (680/37 : ℝ) →
    RR x = (331/20 : ℝ) * x + (-300 : ℝ) :=
  RR_affine_on (l := (420/23 : ℝ)) (r := (680/37 : ℝ)) (n := 18) (m := 1) (k := 42)
    (j := 36) (i := 33) (ef := 1) (eg := 1)
    (dm := true) (ts := false)
    (A := (331/20 : ℝ)) (B := (-300 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p18_3 : ∀ x : ℝ, (680/37 : ℝ) < x → x < (37/2 : ℝ) →
    RR x = (847/40 : ℝ) * x + (-385 : ℝ) :=
  RR_affine_on (l := (680/37 : ℝ)) (r := (37/2 : ℝ)) (n := 18) (m := 1) (k := 42)
    (j := 36) (i := 34) (ef := 1) (eg := 1)
    (dm := false) (ts := false)
    (A := (847/40 : ℝ)) (B := (-385 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p18_4 : ∀ x : ℝ, (37/2 : ℝ) < x → x < (800/43 : ℝ) →
    RR x = (887/40 : ℝ) * x + (-807/2 : ℝ) :=
  RR_affine_on (l := (37/2 : ℝ)) (r := (800/43 : ℝ)) (n := 18) (m := 1) (k := 42)
    (j := 37) (i := 34) (ef := -1) (eg := 1)
    (dm := false) (ts := true)
    (A := (887/40 : ℝ)) (B := (-807/2 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p18_5 : ∀ x : ℝ, (800/43 : ℝ) < x → x < (430/23 : ℝ) →
    RR x = (379/20 : ℝ) * x + (-687/2 : ℝ) :=
  RR_affine_on (l := (800/43 : ℝ)) (r := (430/23 : ℝ)) (n := 18) (m := 1) (k := 42)
    (j := 37) (i := 34) (ef := -1) (eg := 1)
    (dm := true) (ts := true)
    (A := (379/20 : ℝ)) (B := (-687/2 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p18_6 : ∀ x : ℝ, (430/23 : ℝ) < x → x < (700/37 : ℝ) →
    RR x = (89/5 : ℝ) * x + (-322 : ℝ) :=
  RR_affine_on (l := (430/23 : ℝ)) (r := (700/37 : ℝ)) (n := 18) (m := 1) (k := 43)
    (j := 37) (i := 34) (ef := -1) (eg := 1)
    (dm := true) (ts := false)
    (A := (89/5 : ℝ)) (B := (-322 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p18_7 : ∀ x : ℝ, (700/37 : ℝ) < x → x < (19 : ℝ) →
    RR x = (393/20 : ℝ) * x + (-357 : ℝ) :=
  RR_affine_on (l := (700/37 : ℝ)) (r := (19 : ℝ)) (n := 18) (m := 1) (k := 43)
    (j := 37) (i := 35) (ef := -1) (eg := 1)
    (dm := true) (ts := false)
    (A := (393/20 : ℝ)) (B := (-357 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

/-- **Table 3**, row `j = 18` (p. 27):
`∫_{18}^{19} R(x) x^(-3) dx = 4930060867/4724197793280`. -/
theorem table3_18 :
    IntervalIntegrable (fun x => RR x / x ^ 3) volume (18:ℝ) (19:ℝ)
      ∧ (∫ x in (18:ℝ)..(19:ℝ), RR x / x ^ 3) = (4930060867/4724197793280 : ℝ) := by
  have h := chain_integral [((780/43 : ℝ), (177/10 : ℝ), (-321 : ℝ)), ((420/23 : ℝ), (177/10 : ℝ), (-321 : ℝ)), ((680/37 : ℝ), (331/20 : ℝ), (-300 : ℝ)), ((37/2 : ℝ), (847/40 : ℝ), (-385 : ℝ)), ((800/43 : ℝ), (887/40 : ℝ), (-807/2 : ℝ)), ((430/23 : ℝ), (379/20 : ℝ), (-687/2 : ℝ)), ((700/37 : ℝ), (89/5 : ℝ), (-322 : ℝ)), ((19 : ℝ), (393/20 : ℝ), (-357 : ℝ))] (18:ℝ) (by norm_num)
    ⟨by norm_num, by norm_num, p18_0, by norm_num, by norm_num, p18_1, by norm_num, by norm_num, p18_2, by norm_num, by norm_num, p18_3, by norm_num, by norm_num, p18_4, by norm_num, by norm_num, p18_5, by norm_num, by norm_num, p18_6, by norm_num, by norm_num, p18_7, trivial⟩
  simp only [chainEnd] at h
  exact ⟨h.1, by rw [h.2]; norm_num [chainVal]⟩

/-! ### Table 3, row `j = 19`: the 7 intervals of (B.2) inside `[19,20]` -/

lemma p19_0 : ∀ x : ℝ, (19 : ℝ) < x → x < (820/43 : ℝ) →
    RR x = (94/5 : ℝ) * x + (-376 : ℝ) :=
  RR_affine_on (l := (19 : ℝ)) (r := (820/43 : ℝ)) (n := 19) (m := 1) (k := 43)
    (j := 38) (i := 35) (ef := 1) (eg := 1)
    (dm := true) (ts := true)
    (A := (94/5 : ℝ)) (B := (-376 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p19_1 : ∀ x : ℝ, (820/43 : ℝ) < x → x < (440/23 : ℝ) →
    RR x = (94/5 : ℝ) * x + (-376 : ℝ) :=
  RR_affine_on (l := (820/43 : ℝ)) (r := (440/23 : ℝ)) (n := 19) (m := 1) (k := 43)
    (j := 38) (i := 35) (ef := 1) (eg := 1)
    (dm := true) (ts := true)
    (A := (94/5 : ℝ)) (B := (-376 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p19_2 : ∀ x : ℝ, (440/23 : ℝ) < x → x < (720/37 : ℝ) →
    RR x = (353/20 : ℝ) * x + (-354 : ℝ) :=
  RR_affine_on (l := (440/23 : ℝ)) (r := (720/37 : ℝ)) (n := 19) (m := 1) (k := 44)
    (j := 38) (i := 35) (ef := 1) (eg := 1)
    (dm := true) (ts := false)
    (A := (353/20 : ℝ)) (B := (-354 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p19_3 : ∀ x : ℝ, (720/37 : ℝ) < x → x < (39/2 : ℝ) →
    RR x = (891/40 : ℝ) * x + (-444 : ℝ) :=
  RR_affine_on (l := (720/37 : ℝ)) (r := (39/2 : ℝ)) (n := 19) (m := 1) (k := 44)
    (j := 38) (i := 36) (ef := 1) (eg := 1)
    (dm := false) (ts := false)
    (A := (891/40 : ℝ)) (B := (-444 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p19_4 : ∀ x : ℝ, (39/2 : ℝ) < x → x < (840/43 : ℝ) →
    RR x = (931/40 : ℝ) * x + (-927/2 : ℝ) :=
  RR_affine_on (l := (39/2 : ℝ)) (r := (840/43 : ℝ)) (n := 19) (m := 1) (k := 44)
    (j := 39) (i := 36) (ef := -1) (eg := 1)
    (dm := false) (ts := true)
    (A := (931/40 : ℝ)) (B := (-927/2 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p19_5 : ∀ x : ℝ, (840/43 : ℝ) < x → x < (450/23 : ℝ) →
    RR x = (401/20 : ℝ) * x + (-801/2 : ℝ) :=
  RR_affine_on (l := (840/43 : ℝ)) (r := (450/23 : ℝ)) (n := 19) (m := 1) (k := 44)
    (j := 39) (i := 36) (ef := -1) (eg := 1)
    (dm := true) (ts := true)
    (A := (401/20 : ℝ)) (B := (-801/2 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

lemma p19_6 : ∀ x : ℝ, (450/23 : ℝ) < x → x < (20 : ℝ) →
    RR x = (189/10 : ℝ) * x + (-378 : ℝ) :=
  RR_affine_on (l := (450/23 : ℝ)) (r := (20 : ℝ)) (n := 19) (m := 1) (k := 45)
    (j := 39) (i := 36) (ef := -1) (eg := 1)
    (dm := true) (ts := false)
    (A := (189/10 : ℝ)) (B := (-378 : ℝ))
    (by norm_num [Cert, alpha, lam, Hcst, affA, affB])

/-- **Table 3**, row `j = 19` (p. 27):
`∫_{19}^{20} R(x) x^(-3) dx = -15199801/11563552000`. -/
theorem table3_19 :
    IntervalIntegrable (fun x => RR x / x ^ 3) volume (19:ℝ) (20:ℝ)
      ∧ (∫ x in (19:ℝ)..(20:ℝ), RR x / x ^ 3) = (-15199801/11563552000 : ℝ) := by
  have h := chain_integral [((820/43 : ℝ), (94/5 : ℝ), (-376 : ℝ)), ((440/23 : ℝ), (94/5 : ℝ), (-376 : ℝ)), ((720/37 : ℝ), (353/20 : ℝ), (-354 : ℝ)), ((39/2 : ℝ), (891/40 : ℝ), (-444 : ℝ)), ((840/43 : ℝ), (931/40 : ℝ), (-927/2 : ℝ)), ((450/23 : ℝ), (401/20 : ℝ), (-801/2 : ℝ)), ((20 : ℝ), (189/10 : ℝ), (-378 : ℝ))] (19:ℝ) (by norm_num)
    ⟨by norm_num, by norm_num, p19_0, by norm_num, by norm_num, p19_1, by norm_num, by norm_num, p19_2, by norm_num, by norm_num, p19_3, by norm_num, by norm_num, p19_4, by norm_num, by norm_num, p19_5, by norm_num, by norm_num, p19_6, trivial⟩
  simp only [chainEnd] at h
  exact ⟨h.1, by rw [h.2]; norm_num [chainVal]⟩


/-- Gluing two adjacent exact integrals. -/
lemma add_adj {a b c va vb : ℝ}
    (ia : IntervalIntegrable (fun x => RR x / x ^ 3) volume a b)
    (ib : IntervalIntegrable (fun x => RR x / x ^ 3) volume b c)
    (ha : (∫ x in a..b, RR x / x ^ 3) = va) (hb : (∫ x in b..c, RR x / x ^ 3) = vb) :
    IntervalIntegrable (fun x => RR x / x ^ 3) volume a c
      ∧ (∫ x in a..c, RR x / x ^ 3) = va + vb :=
  ⟨ia.trans ib, by rw [← intervalIntegral.integral_add_adjacent_intervals ia ib, ha, hb]⟩

/-- **(5.18)** (p. 17) and (B.3) (p. 26): the seventeen rows of Table 3 sum to
`∫_3^20 R(x) x^(-3) dx = 322437603634266857629/7535670527041937280000 = I320`. -/
theorem eq_5_18 :
    IntervalIntegrable (fun x => RR x / x ^ 3) volume (3:ℝ) (20:ℝ)
      ∧ (∫ x in (3:ℝ)..(20:ℝ), RR x / x ^ 3) = (I320 : ℝ) := by
  have k4 := add_adj table3_3.1 table3_4.1 table3_3.2 table3_4.2
  have k5 := add_adj k4.1 table3_5.1 k4.2 table3_5.2
  have k6 := add_adj k5.1 table3_6.1 k5.2 table3_6.2
  have k7 := add_adj k6.1 table3_7.1 k6.2 table3_7.2
  have k8 := add_adj k7.1 table3_8.1 k7.2 table3_8.2
  have k9 := add_adj k8.1 table3_9.1 k8.2 table3_9.2
  have k10 := add_adj k9.1 table3_10.1 k9.2 table3_10.2
  have k11 := add_adj k10.1 table3_11.1 k10.2 table3_11.2
  have k12 := add_adj k11.1 table3_12.1 k11.2 table3_12.2
  have k13 := add_adj k12.1 table3_13.1 k12.2 table3_13.2
  have k14 := add_adj k13.1 table3_14.1 k13.2 table3_14.2
  have k15 := add_adj k14.1 table3_15.1 k14.2 table3_15.2
  have k16 := add_adj k15.1 table3_16.1 k15.2 table3_16.2
  have k17 := add_adj k16.1 table3_17.1 k16.2 table3_17.2
  have k18 := add_adj k17.1 table3_18.1 k17.2 table3_18.2
  have k19 := add_adj k18.1 table3_19.1 k18.2 table3_19.2
  exact ⟨k19.1, by rw [k19.2]; norm_num [I320]⟩

/-! ## §5.3.  (5.12)–(5.13): `R(x) = x F(x) + Q(x)`

The closed form of `R` in terms of fractional parts only.  It is the starting point of §5.3
(and the reason `R(x) = O(x)`), and it gives at once that `R` is measurable and bounded on
compacts, hence `R x^{-3}` interval-integrable — which is the assertion the paper makes in
the sentence after (5.6). -/

/-- **(5.12)**: `F(x) = 4λ + 2λ{x} - 12λ{αx}`. -/
def Fcl (x : ℝ) : ℝ :=
  4 * (lam:ℝ) + 2 * (lam:ℝ) * Int.fract x - 12 * (lam:ℝ) * Int.fract ((alpha:ℝ) * x)

/-- **(5.13)**: `Q(x) = (τ(τ-σ) - (τ-σ)_+ + η(1-η))/2 + 9∫B² - 3∫AB`, with
`τ = {2Hx}`, `σ = {2x}`, `η = {2λx}`, `∫B² = d_g(1-2d_g)` and
`∫AB = e_f e_g (min(d_f,d_g) - 2d_f d_g)` by (B.1). -/
def Qcl (x : ℝ) : ℝ :=
  (Int.fract (2 * (Hcst:ℝ) * x) * (Int.fract (2 * (Hcst:ℝ) * x) - Int.fract (2 * x))
      - max 0 (Int.fract (2 * (Hcst:ℝ) * x) - Int.fract (2 * x))
      + Int.fract (2 * (lam:ℝ) * x) * (1 - Int.fract (2 * (lam:ℝ) * x))) / 2
    + 9 * (dG x * (1 - 2 * dG x))
    - 3 * (eF x * eG x * (min (dF x) (dG x) - 2 * dF x * dG x))

lemma max_zero_half (a : ℝ) : max 0 (a / 2) = max 0 a / 2 := by
  rcases le_total 0 a with h | h
  · rw [max_eq_right (by linarith), max_eq_right h]
  · rw [max_eq_left (by linarith), max_eq_left h, zero_div]

/-- **(5.12)–(5.13)** (p. 16): `R(x) = x F(x) + Q(x)`. -/
theorem RR_closed (x : ℝ) : RR x = x * Fcl x + Qcl x := by
  have hegsq : eG x * eG x = 1 := e0_sq _
  have hT : TR x = 2 * (Hcst:ℝ) * x - Int.fract (2 * (Hcst:ℝ) * x) := by
    rw [TR, ← Int.self_sub_fract]
  have hq : qR x = 2 * x - Int.fract (2 * x) := by rw [qR, ← Int.self_sub_fract]
  have hfx : ((⌊x⌋ : ℤ) : ℝ) = x - Int.fract x := (Int.self_sub_fract x).symm
  have hgx : ((⌊(alpha:ℝ) * x⌋ : ℤ) : ℝ) = (alpha:ℝ) * x - Int.fract ((alpha:ℝ) * x) :=
    (Int.self_sub_fract _).symm
  have hlx : ((⌊2 * ((lam:ℝ) * x)⌋ : ℤ) : ℝ)
      = 2 * (lam:ℝ) * x - Int.fract (2 * (lam:ℝ) * x) := by
    rw [show 2 * ((lam:ℝ) * x) = 2 * (lam:ℝ) * x by ring]
    exact (Int.self_sub_fract _).symm
  have hs : sR x = Int.fract (2 * (Hcst:ℝ) * x) / 2 := by rw [sR, hT]; ring
  have hn : nPlus x = Int.fract (2 * x) / 2 := by rw [nPlus, hq]; ring
  have hmax : max 0 (sR x - nPlus x)
      = max 0 (Int.fract (2 * (Hcst:ℝ) * x) - Int.fract (2 * x)) / 2 := by
    rw [hs, hn, show Int.fract (2 * (Hcst:ℝ) * x) / 2 - Int.fract (2 * x) / 2
        = (Int.fract (2 * (Hcst:ℝ) * x) - Int.fract (2 * x)) / 2 by ring, max_zero_half]
  rw [RR, Gam_eq, NR, JR]
  simp only [UU, VV]
  rw [hmax, hs, hT, hq, hfx, hgx, hlx]
  simp only [Fcl, Qcl, min_comm (dG x) (dF x), lam, alpha, Hcst]
  push_cast
  linear_combination (-18 * (dG x) ^ 2) * hegsq

/-! ### `R` is measurable and bounded on compacts -/

lemma measurable_e0 : Measurable e0 :=
  Measurable.ite (measurableSet_le measurable_id measurable_const)
    measurable_const measurable_const

lemma measurable_d0 : Measurable d0 := by
  unfold d0; fun_prop

lemma measurable_dF : Measurable dF := measurable_d0.comp measurable_fract
lemma measurable_eF : Measurable eF := measurable_e0.comp measurable_fract
lemma measurable_dG : Measurable dG :=
  measurable_d0.comp (measurable_fract.comp (measurable_const_mul _))
lemma measurable_eG : Measurable eG :=
  measurable_e0.comp (measurable_fract.comp (measurable_const_mul _))

lemma measurable_Fcl : Measurable Fcl := by unfold Fcl; fun_prop

lemma measurable_Qcl : Measurable Qcl := by
  unfold Qcl
  have h1 : Measurable fun x : ℝ => dG x := measurable_dG
  have h2 : Measurable fun x : ℝ => dF x := measurable_dF
  have h3 : Measurable fun x : ℝ => eF x := measurable_eF
  have h4 : Measurable fun x : ℝ => eG x := measurable_eG
  fun_prop

lemma measurable_RR : Measurable RR := by
  have : RR = fun x => x * Fcl x + Qcl x := funext RR_closed
  rw [this]
  have h1 : Measurable Fcl := measurable_Fcl
  have h2 : Measurable Qcl := measurable_Qcl
  fun_prop

lemma abs_Fcl_le (x : ℝ) : |Fcl x| ≤ 17 := by
  have hl : ((lam : ℚ) : ℝ) = 37/40 := by norm_num [lam]
  have h1 := Int.fract_nonneg x
  have h2 := Int.fract_lt_one x
  have h3 := Int.fract_nonneg ((alpha:ℝ) * x)
  have h4 := Int.fract_lt_one ((alpha:ℝ) * x)
  rw [Fcl, hl, abs_le]
  constructor <;> linarith

lemma abs_Qcl_le (x : ℝ) : |Qcl x| ≤ 10 := by
  have t0 := Int.fract_nonneg (2 * (Hcst:ℝ) * x)
  have t1 := Int.fract_lt_one (2 * (Hcst:ℝ) * x)
  have s0 := Int.fract_nonneg (2 * x)
  have s1 := Int.fract_lt_one (2 * x)
  have e0' := Int.fract_nonneg (2 * (lam:ℝ) * x)
  have e1 := Int.fract_lt_one (2 * (lam:ℝ) * x)
  have dg0 : 0 ≤ dG x := dG_nonneg x
  have dg1 : dG x ≤ 1/2 := dG_le x
  have df0 : 0 ≤ dF x := dF_nonneg x
  have df1 : dF x ≤ 1/2 := dF_le x
  have hmn0 : 0 ≤ min (dF x) (dG x) := le_min df0 dg0
  have hmn1 : min (dF x) (dG x) ≤ 1/2 := le_trans (min_le_left _ _) df1
  have hpp0 : 0 ≤ max 0 (Int.fract (2 * (Hcst:ℝ) * x) - Int.fract (2 * x)) := le_max_left _ _
  have hpp1 : max 0 (Int.fract (2 * (Hcst:ℝ) * x) - Int.fract (2 * x)) ≤ 1 :=
    max_le (by norm_num) (by linarith)
  have hef : eF x = 1 ∨ eF x = -1 := by
    unfold eF e0; split <;> simp
  have heg : eG x = 1 ∨ eG x = -1 := by
    unfold eG e0; split <;> simp
  rw [Qcl, abs_le]
  rcases hef with h | h <;> rcases heg with h' | h' <;> rw [h, h'] <;>
    constructor <;> nlinarith [mul_nonneg df0 dg0, sq_nonneg (dG x), sq_nonneg (dF x)]

/-- **(5.14)** (p. 16): `-1/2 ≤ Q(x) ≤ 13/8`.

The paper's derivation — "Each squared integral is at most 1/8, and Cauchy–Schwarz bounds
the absolute value of the mixed integral by 1/8.  The first numerator in (5.13) lies between
−1/4 and 1/4" — is carried out in `Zeta5/Tail.lean` for the raw ingredients
(`Zeta5.Tail.eq_5_14`); here it is instantiated at the concrete `Qcl` of (5.13). -/
theorem eq_5_14 (x : ℝ) : -(1 / 2) ≤ Qcl x ∧ Qcl x ≤ 13 / 8 := by
  have hef : eF x = 1 ∨ eF x = -1 := by unfold eF e0; split <;> simp
  have heg : eG x = 1 ∨ eG x = -1 := by unfold eG e0; split <;> simp
  rw [Qcl]
  exact Zeta5.Tail.eq_5_14 (Int.fract_nonneg _) (Int.fract_lt_one _) (Int.fract_nonneg _)
    (Int.fract_lt_one _) (Int.fract_nonneg _) (Int.fract_lt_one _)
    (dF_nonneg x) (dF_le x) (dG_nonneg x) (dG_le x) hef heg

/-- `F` of (5.12) is the `Zeta5.Tail.Fc` that `Zeta5/Tail.lean` does the analysis with:
the two definitions are the same expression. -/
lemma Fcl_eq_Fc (x : ℝ) : Fcl x = Zeta5.Tail.Fc x := rfl

/-- `R(x)/x³` is interval-integrable on every `[a,b]` with `0 < a ≤ b`: the assertion the
paper makes in the sentence after (5.6) ("These functions are bounded and piecewise
polynomial on each compact subinterval of `[3,∞)`").  Proved here from (5.12)–(5.13). -/
theorem intervalIntegrable_RR_div {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun x => RR x / x ^ 3) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  have hmeas : Measurable fun x : ℝ => RR x / x ^ 3 :=
    measurable_RR.div (measurable_id.pow_const 3)
  refine MeasureTheory.Integrable.mono' (g := fun _ => (b * 17 + 10) / a ^ 3) ?_
    hmeas.aestronglyMeasurable ?_
  · exact MeasureTheory.integrableOn_const
      (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  · filter_upwards [MeasureTheory.ae_restrict_mem (measurableSet_Ioc (a := a) (b := b))]
      with y hy
    obtain ⟨hy1, hy2⟩ := hy
    have hy0 : 0 < y := lt_trans ha hy1
    have hnum : |RR y| ≤ b * 17 + 10 := by
      rw [RR_closed y]
      have h1 : |y * Fcl y| ≤ b * 17 := by
        rw [abs_mul, abs_of_pos hy0]
        exact mul_le_mul hy2 (abs_Fcl_le y) (abs_nonneg _) (le_trans (le_of_lt hy0) hy2)
      have h2 := abs_Qcl_le y
      exact le_trans (abs_add_le _ _) (by linarith)
    have hy3 : (0:ℝ) < y ^ 3 := by positivity
    have ha3 : (0:ℝ) < a ^ 3 := by positivity
    have hcube : a ^ 3 ≤ y ^ 3 := by gcongr
    have hbig : (0:ℝ) ≤ b * 17 + 10 := by nlinarith
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hy3, div_le_iff₀ hy3]
    have hfrac : (0:ℝ) ≤ (b * 17 + 10) / a ^ 3 := div_nonneg hbig (le_of_lt ha3)
    have hstep : (b * 17 + 10) / a ^ 3 * a ^ 3 ≤ (b * 17 + 10) / a ^ 3 * y ^ 3 :=
      mul_le_mul_of_nonneg_left hcube hfrac
    rw [div_mul_cancel₀ _ (ne_of_gt ha3)] at hstep
    linarith

/-! ## §5.3.  The tail estimates (5.16)–(5.17), and the assembly (5.19)–(5.21)

This is the one statement of Appendix B that is **not** a finite computation: it is the pair
of genuinely analytic tail bounds of §5.3, obtained there from the two integrations by parts
(5.15) applied to the periodic decomposition (5.12)–(5.13).  The analysis lives in
`Zeta5/Tail.lean`; here it is instantiated at `Qcl`. -/

/-- **(5.16)–(5.17)** (p. 16), combined.  **Proved**, from `Zeta5.Tail.tail_bound`.

Paper statement, verbatim.  With `A(z) = ℓ(x,z) - 2x`, `B(z) = ℓ(αx,z) - 2αx`,
`f = {x}`, `g = {αx}`, `τ = {2Hx}`, `σ = {2x}`, `η = {2λx}`, (5.12)–(5.13) write
`R(x) = x F(x) + Q(x)` with `F = 4λ + 2λf - 12λg` and
`Q = (τ(τ-σ) - (τ-σ)_+ + η(1-η))/2 + 9∫B² - 3∫AB`, so that `-1/2 ≤ Q ≤ 13/8` (5.14).
With `𝒫(x) = 74g(1-g) - λf(1-f)`, `𝒫̄ = 2923/240`, `G₀(v) = v(1-v)(2v-1)/6` and
`𝒞(x) = (74/α)G₀(g) - λG₀(f)`, one has `𝒫' = F + λ`, `𝒞' = 𝒫 - 𝒫̄` away from the
breakpoints, and `|𝒞(x)| ≤ 118511/(4320√3) < 16`.  Two integrations by parts give

  `∫_T^∞ R(x)x^{-3} dx = -λ/T - 𝒫(T)/T² + 𝒫̄/T² - 2𝒞(T)/T³`
                       ` + 6∫_T^∞ 𝒞(x)x^{-4} dx + ∫_T^∞ Q(x)x^{-3} dx`                  (5.15)

whence, at `T = 20` where `𝒫(20) = 37/2` and `𝒞(20) = 0`,

  `∫_20^∞ R(x)x^{-3} dx ≤ -2689/48000`                                                  (5.16)

and, for `40 | M` where `𝒫(M) = 𝒞(M) = 0`,

  `∫_M^∞ R(x)x^{-3} dx ≥ -λ/M + (2923/240 - 1/4)/M² - 32/M³`.                           (5.17)

Subtracting, `∫_20^M = ∫_20^∞ - ∫_M^∞` gives the statement below.

**How it is proved.**  The improper integral `∫_T^∞` is never formed: since (5.16) and
(5.17) are used only through their difference, (5.15) is proved in `Zeta5/Tail.lean` as an
identity on the **finite** interval `[T,X]`,
`∫_T^X (F(x)/x² - 6𝒞(x)/x⁴) dx = W(X) - W(T)` with `W(x) = (λx² + (𝒫(x)-𝒫̄)x + 2𝒞(x))/x³`,
by the fundamental theorem of calculus in its right-derivative form — `𝒫` and `𝒞` are
continuous and have right-derivatives `F + λ` and `𝒫 - 𝒫̄` at *every* point, breakpoints
included, because `x ↦ {cx}` does.  `𝒞 ≤ 16` comes from `max_{[0,1]}|G₀| = 1/(36√3)`, proved
there as the rational bound `|G₀| ≤ 161/10000`; `Q ≤ 13/8` is (5.14) (`eq_5_14` above).
`Zeta5.Tail.tail_bound_strong` in fact gives the stronger
`≤ -2689/48000 + λ/M - (2923/240 + 13/16)/M² - 32/M³`. -/
theorem eq_5_16_5_17 (M : ℕ) (hM : 40 ∣ M) (hM0 : 0 < M) :
    (∫ x in (20:ℝ)..(M:ℝ), RR x / x ^ 3)
      ≤ (I20inf : ℝ) + (lam : ℝ) / (M:ℝ)
          - (2923/240 - 1/4) / (M:ℝ) ^ 2 + 32 / (M:ℝ) ^ 3 := by
  have hfun : ∀ x : ℝ, RR x / x ^ 3 = (x * Zeta5.Tail.Fc x + Qcl x) / x ^ 3 := by
    intro x
    rw [RR_closed x, Fcl_eq_Fc x]
  rw [intervalIntegral.integral_congr (fun x _ => hfun x)]
  have hI : ((I20inf : ℚ) : ℝ) = -2689 / 48000 := by norm_num [I20inf]
  have h := Zeta5.Tail.tail_bound measurable_Qcl (fun x => (eq_5_14 x).1)
    (fun x => (eq_5_14 x).2) hM hM0
  linarith [h]

/-- **(5.16)–(5.18)** (pp. 16–17), the statement `Zeta5.eq_5_16_5_18` of `Interface.lean`:
for `M ∈ 40ℤ_{>0}`,

`I_out + 6λ/M + ∫_3^M R(x) x^{-3} dx ≤ A_M`.

Everything here is proved: (5.16)–(5.17) is `eq_5_16_5_17`, (5.18) is the computed
`eq_5_18`, the bookkeeping `A_* = I_out + ∫_3^20 + (-2689/48000)` is `Zeta5.Astar_eq`, and
the split `∫_3^M = ∫_3^20 + ∫_20^M` uses the integrability produced by the piecewise
computation. -/
theorem eq_5_16_5_18 (M : ℕ) (hM : 40 ∣ M) (hM0 : 0 < M) :
    (Iout : ℝ) + 6 * (lam : ℝ) / (M : ℝ)
      + (∫ x in (3 : ℝ)..(M : ℝ), RR x / x ^ 3) ≤ (AM M : ℝ) := by
  obtain ⟨i1, v1⟩ := eq_5_18
  have v2 := eq_5_16_5_17 M hM hM0
  have hM40 : 40 ≤ M := Nat.le_of_dvd hM0 hM
  have hMR : (40:ℝ) ≤ (M:ℝ) := by exact_mod_cast hM40
  have i2 : IntervalIntegrable (fun x => RR x / x ^ 3) volume (20:ℝ) (M:ℝ) :=
    intervalIntegrable_RR_div (by norm_num) (by linarith)
  have hsplit : (∫ x in (3:ℝ)..(M:ℝ), RR x / x ^ 3)
      = (∫ x in (3:ℝ)..(20:ℝ), RR x / x ^ 3) + (∫ x in (20:ℝ)..(M:ℝ), RR x / x ^ 3) :=
    (intervalIntegral.integral_add_adjacent_intervals i1 i2).symm
  have hAM : (AM M : ℝ)
      = (Astar : ℝ) + 7 * (lam : ℝ) / (M:ℝ)
          - (2923/240 - 1/4) / (M:ℝ) ^ 2 + 32 / (M:ℝ) ^ 3 := by
    rw [AM]; push_cast; ring
  have hAstar : (Astar : ℝ) = (Iout : ℝ) + (I320 : ℝ) + (I20inf : ℝ) := by
    have := Astar_eq
    exact_mod_cast congrArg (fun q : ℚ => (q : ℝ)) this
  have key : 7 * (lam:ℝ) / (M:ℝ) = 6 * (lam:ℝ) / (M:ℝ) + (lam:ℝ) / (M:ℝ) := by ring
  rw [hsplit, v1, hAM, hAstar, key]
  linarith [v2]

/-- The value of `A_M` at the two cutoffs of §B.3 (p. 28), exactly as printed. -/
theorem AM_200_eq_B3 : AM 200 = 127125602969131786927559 / 94195881588024216000000 := by
  norm_num [AM, Astar, lam]

theorem AM_100000_eq_B3 :
    AM 100000 = 7756864096839411316755964319057 / 5887242599251513500000000000000 := by
  norm_num [AM, Astar, lam]

/-- **§B.3** (p. 28), the first exact margin of (7.2). -/
theorem margin_200 :
    -1600 * (AM 200 + Ubar) - 139 / 5
      = 3089837638249482469 / 58872425992515135000 := by
  norm_num [AM, Astar, Ubar, lam]

/-- **§B.3** (p. 28), the second exact margin of (7.2). -/
theorem margin_100000 :
    -1600 * (AM 100000 + Ubar) - 7907 / 100
      = 29873543950273155160680943 / 3679526624532195937500000000 := by
  norm_num [AM, Astar, Ubar, lam]

/-- §B.3 (p. 28): `A_100000 + U < -79/1600`, as (C.7) requires. -/
theorem AM_100000_add_Ubar_lt : AM 100000 + Ubar < -79 / 1600 := by
  norm_num [AM, Astar, Ubar, lam]

/-! ## §B.2.  The outer integral: (5.8), (5.9), Table 4 and `I_out = 127751/96000`

(5.8) and (5.9) are transcribed with the paper's three ranges written as nested `if`s.  The
values at `y ≤ 1/3`, `y = 1/2` and `y = 1` are irrelevant: the integration range of (5.10) is
`(1/3, 2λ)` and the two exceptional points form a null set (and are endpoints of pieces of
Table 4, so they never occur in an open piece). -/

/-- **(5.8)** (p. 15): the residue contribution `R₀(y)` in the outer range. -/
def R0 (y : ℝ) : ℝ :=
  if y < 1/2 then
    8 - 9*y - 8*(alpha:ℝ) - 5 * min (alpha:ℝ) (1 - 2*y) - 5 * max 0 (1 + (alpha:ℝ) - 3*y)
  else if y < 1 then
    7*(1-y) - 6 * min (alpha:ℝ) (1-y) - 6 * max 0 (1 + (alpha:ℝ) - 2*y)
      + max 0 (1 + 4*(alpha:ℝ) - 2*y)
  else 0

/-- **(5.9)** (p. 15): the rank correction `d(y)`, supported in `(1/3,1/2)`. -/
def dRank (y : ℝ) : ℝ :=
  if y < 1/2 then max 0 (1 + 4*(alpha:ℝ) - 3*y - max 0 (1 + (alpha:ℝ) - 3*y)) else 0

/-- §B.2 (p. 27): the outer integrand
`T(y) = R₀(y) - d(y) - 2λ⌊1/y⌋ + Σ_{j=1}^5 (2λ - jy)_+`. -/
def Tout (y : ℝ) : ℝ :=
  R0 y - dRank y - 2*(lam:ℝ) * (⌊1/y⌋ : ℝ)
    + max 0 (2*(lam:ℝ) - y) + max 0 (2*(lam:ℝ) - 2*y) + max 0 (2*(lam:ℝ) - 3*y)
    + max 0 (2*(lam:ℝ) - 4*y) + max 0 (2*(lam:ℝ) - 5*y)

/-- `∫_l^r (b + cy) dy = b(r-l) + c(r²-l²)/2`. -/
lemma integral_affine_plain (b c l r : ℝ) :
    (∫ y in l..r, (b + c * y)) = b * (r - l) + c * (r^2 - l^2) / 2 := by
  rw [intervalIntegral.integral_add intervalIntegrable_const
    ((intervalIntegral.intervalIntegrable_id).const_mul c),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
    integral_id]
  simp only [smul_eq_mul]
  ring

/-- `T` is integrable and has the exact integral on a piece where it is affine. -/
lemma piece_out {l r b c : ℝ} (hlr : l ≤ r)
    (hp : ∀ y : ℝ, l < y → y < r → Tout y = b + c * y) :
    IntervalIntegrable Tout volume l r
      ∧ (∫ y in l..r, Tout y) = b * (r - l) + c * (r^2 - l^2) / 2 := by
  have hcont : ContinuousOn (fun y : ℝ => b + c * y) (uIcc l r) := by fun_prop
  have hEq : Set.EqOn (fun y : ℝ => b + c * y) Tout (uIoo l r) := by
    intro y hy
    rw [Set.uIoo_of_le hlr] at hy
    exact (hp y hy.1 hy.2).symm
  refine ⟨(hcont.intervalIntegrable).congr_uIoo hEq, ?_⟩
  have hne : ∀ᵐ t : ℝ, t ≠ r := by
    rw [MeasureTheory.ae_iff]
    simp
  rw [intervalIntegral.integral_congr_ae (g := fun y : ℝ => b + c * y) ?_,
    integral_affine_plain]
  filter_upwards [hne] with t htr htmem
  rw [Set.uIoc_of_le hlr] at htmem
  rw [hp t htmem.1 (lt_of_le_of_ne htmem.2 htr)]

/-- Gluing two adjacent exact integrals of `T`. -/
lemma add_adj_out {a b c va vb : ℝ}
    (ia : IntervalIntegrable Tout volume a b) (ib : IntervalIntegrable Tout volume b c)
    (ha : (∫ y in a..b, Tout y) = va) (hb : (∫ y in b..c, Tout y) = vb) :
    IntervalIntegrable Tout volume a c ∧ (∫ y in a..c, Tout y) = va + vb :=
  ⟨ia.trans ib, by rw [← intervalIntegral.integral_add_adjacent_intervals ia ib, ha, hb]⟩

/-! ### Table 4 (p. 27): the eleven affine pieces of the outer integrand -/

lemma qout_0 : ∀ y : ℝ, (1/3 : ℝ) < y → y < (43/120 : ℝ) → Tout y = (279/40 : ℝ) + (-9 : ℝ) * y := by
  intro y h1 h2
  have hy : (0:ℝ) < y := by linarith
  have ha : ((alpha : ℚ) : ℝ) = 3/40 := by norm_num [alpha]
  have hl : ((lam : ℚ) : ℝ) = 37/40 := by norm_num [lam]
  have hfl : ⌊1/y⌋ = (2:ℤ) := by
    refine Int.floor_eq_iff.2 ⟨?_, ?_⟩
    · push_cast; rw [le_div_iff₀ hy]; linarith
    · push_cast; rw [div_lt_iff₀ hy]; linarith
  have b1 : ((alpha:ℚ):ℝ) ≤ 1 - 2*y := by rw [ha]; linarith
  have b2 : (0:ℝ) ≤ 1 + ((alpha:ℚ):ℝ) - 3*y := by rw [ha]; linarith
  have b3 : (0:ℝ) ≤ 1 + 4*((alpha:ℚ):ℝ) - 3*y - (1 + ((alpha:ℚ):ℝ) - 3*y) := by rw [ha]; linarith
  have c1 : (0:ℝ) ≤ 2*((lam:ℚ):ℝ) - y := by rw [hl]; linarith
  have c2 : (0:ℝ) ≤ 2*((lam:ℚ):ℝ) - 2*y := by rw [hl]; linarith
  have c3 : (0:ℝ) ≤ 2*((lam:ℚ):ℝ) - 3*y := by rw [hl]; linarith
  have c4 : (0:ℝ) ≤ 2*((lam:ℚ):ℝ) - 4*y := by rw [hl]; linarith
  have c5 : (0:ℝ) ≤ 2*((lam:ℚ):ℝ) - 5*y := by rw [hl]; linarith
  simp only [Tout, R0, dRank, hfl, ite_eq_left (show y < (1:ℝ)/2 by linarith), min_eq_left b1, max_eq_right b2, max_eq_right b3, max_eq_right c1, max_eq_right c2, max_eq_right c3, max_eq_right c4, max_eq_right c5]
  simp only [alpha, lam]
  push_cast
  ring

lemma qout_1 : ∀ y : ℝ, (43/120 : ℝ) < y → y < (37/100 : ℝ) → Tout y = (451/40 : ℝ) + (-21 : ℝ) * y := by
  intro y h1 h2
  have hy : (0:ℝ) < y := by linarith
  have ha : ((alpha : ℚ) : ℝ) = 3/40 := by norm_num [alpha]
  have hl : ((lam : ℚ) : ℝ) = 37/40 := by norm_num [lam]
  have hfl : ⌊1/y⌋ = (2:ℤ) := by
    refine Int.floor_eq_iff.2 ⟨?_, ?_⟩
    · push_cast; rw [le_div_iff₀ hy]; linarith
    · push_cast; rw [div_lt_iff₀ hy]; linarith
  have b1 : ((alpha:ℚ):ℝ) ≤ 1 - 2*y := by rw [ha]; linarith
  have b2 : 1 + ((alpha:ℚ):ℝ) - 3*y ≤ 0 := by rw [ha]; linarith
  have b3 : (0:ℝ) ≤ 1 + 4*((alpha:ℚ):ℝ) - 3*y - 0 := by rw [ha]; linarith
  have c1 : (0:ℝ) ≤ 2*((lam:ℚ):ℝ) - y := by rw [hl]; linarith
  have c2 : (0:ℝ) ≤ 2*((lam:ℚ):ℝ) - 2*y := by rw [hl]; linarith
  have c3 : (0:ℝ) ≤ 2*((lam:ℚ):ℝ) - 3*y := by rw [hl]; linarith
  have c4 : (0:ℝ) ≤ 2*((lam:ℚ):ℝ) - 4*y := by rw [hl]; linarith
  have c5 : (0:ℝ) ≤ 2*((lam:ℚ):ℝ) - 5*y := by rw [hl]; linarith
  simp only [Tout, R0, dRank, hfl, ite_eq_left (show y < (1:ℝ)/2 by linarith), min_eq_left b1, max_eq_left b2, max_eq_right b3, max_eq_right c1, max_eq_right c2, max_eq_right c3, max_eq_right c4, max_eq_right c5]
  simp only [alpha, lam]
  push_cast
  ring

lemma qout_2 : ∀ y : ℝ, (37/100 : ℝ) < y → y < (13/30 : ℝ) → Tout y = (377/40 : ℝ) + (-16 : ℝ) * y := by
  intro y h1 h2
  have hy : (0:ℝ) < y := by linarith
  have ha : ((alpha : ℚ) : ℝ) = 3/40 := by norm_num [alpha]
  have hl : ((lam : ℚ) : ℝ) = 37/40 := by norm_num [lam]
  have hfl : ⌊1/y⌋ = (2:ℤ) := by
    refine Int.floor_eq_iff.2 ⟨?_, ?_⟩
    · push_cast; rw [le_div_iff₀ hy]; linarith
    · push_cast; rw [div_lt_iff₀ hy]; linarith
  have b1 : ((alpha:ℚ):ℝ) ≤ 1 - 2*y := by rw [ha]; linarith
  have b2 : 1 + ((alpha:ℚ):ℝ) - 3*y ≤ 0 := by rw [ha]; linarith
  have b3 : (0:ℝ) ≤ 1 + 4*((alpha:ℚ):ℝ) - 3*y - 0 := by rw [ha]; linarith
  have c1 : (0:ℝ) ≤ 2*((lam:ℚ):ℝ) - y := by rw [hl]; linarith
  have c2 : (0:ℝ) ≤ 2*((lam:ℚ):ℝ) - 2*y := by rw [hl]; linarith
  have c3 : (0:ℝ) ≤ 2*((lam:ℚ):ℝ) - 3*y := by rw [hl]; linarith
  have c4 : (0:ℝ) ≤ 2*((lam:ℚ):ℝ) - 4*y := by rw [hl]; linarith
  have c5 : 2*((lam:ℚ):ℝ) - 5*y ≤ 0 := by rw [hl]; linarith
  simp only [Tout, R0, dRank, hfl, ite_eq_left (show y < (1:ℝ)/2 by linarith), min_eq_left b1, max_eq_left b2, max_eq_right b3, max_eq_right c1, max_eq_right c2, max_eq_right c3, max_eq_right c4, max_eq_left c5]
  simp only [alpha, lam]
  push_cast
  ring

lemma qout_3 : ∀ y : ℝ, (13/30 : ℝ) < y → y < (37/80 : ℝ) → Tout y = (429/40 : ℝ) + (-19 : ℝ) * y := by
  intro y h1 h2
  have hy : (0:ℝ) < y := by linarith
  have ha : ((alpha : ℚ) : ℝ) = 3/40 := by norm_num [alpha]
  have hl : ((lam : ℚ) : ℝ) = 37/40 := by norm_num [lam]
  have hfl : ⌊1/y⌋ = (2:ℤ) := by
    refine Int.floor_eq_iff.2 ⟨?_, ?_⟩
    · push_cast; rw [le_div_iff₀ hy]; linarith
    · push_cast; rw [div_lt_iff₀ hy]; linarith
  have b1 : ((alpha:ℚ):ℝ) ≤ 1 - 2*y := by rw [ha]; linarith
  have b2 : 1 + ((alpha:ℚ):ℝ) - 3*y ≤ 0 := by rw [ha]; linarith
  have b3 : 1 + 4*((alpha:ℚ):ℝ) - 3*y - 0 ≤ 0 := by rw [ha]; linarith
  have c1 : (0:ℝ) ≤ 2*((lam:ℚ):ℝ) - y := by rw [hl]; linarith
  have c2 : (0:ℝ) ≤ 2*((lam:ℚ):ℝ) - 2*y := by rw [hl]; linarith
  have c3 : (0:ℝ) ≤ 2*((lam:ℚ):ℝ) - 3*y := by rw [hl]; linarith
  have c4 : (0:ℝ) ≤ 2*((lam:ℚ):ℝ) - 4*y := by rw [hl]; linarith
  have c5 : 2*((lam:ℚ):ℝ) - 5*y ≤ 0 := by rw [hl]; linarith
  simp only [Tout, R0, dRank, hfl, ite_eq_left (show y < (1:ℝ)/2 by linarith), min_eq_left b1, max_eq_left b2, max_eq_left b3, max_eq_right c1, max_eq_right c2, max_eq_right c3, max_eq_right c4, max_eq_left c5]
  simp only [alpha, lam]
  push_cast
  ring

lemma qout_4 : ∀ y : ℝ, (37/80 : ℝ) < y → y < (1/2 : ℝ) → Tout y = (17/4 : ℝ) + (-5 : ℝ) * y := by
  intro y h1 h2
  have hy : (0:ℝ) < y := by linarith
  have ha : ((alpha : ℚ) : ℝ) = 3/40 := by norm_num [alpha]
  have hl : ((lam : ℚ) : ℝ) = 37/40 := by norm_num [lam]
  have hfl : ⌊1/y⌋ = (2:ℤ) := by
    refine Int.floor_eq_iff.2 ⟨?_, ?_⟩
    · push_cast; rw [le_div_iff₀ hy]; linarith
    · push_cast; rw [div_lt_iff₀ hy]; linarith
  have b1 : (1:ℝ) - 2*y ≤ ((alpha:ℚ):ℝ) := by rw [ha]; linarith
  have b2 : 1 + ((alpha:ℚ):ℝ) - 3*y ≤ 0 := by rw [ha]; linarith
  have b3 : 1 + 4*((alpha:ℚ):ℝ) - 3*y - 0 ≤ 0 := by rw [ha]; linarith
  have c1 : (0:ℝ) ≤ 2*((lam:ℚ):ℝ) - y := by rw [hl]; linarith
  have c2 : (0:ℝ) ≤ 2*((lam:ℚ):ℝ) - 2*y := by rw [hl]; linarith
  have c3 : (0:ℝ) ≤ 2*((lam:ℚ):ℝ) - 3*y := by rw [hl]; linarith
  have c4 : 2*((lam:ℚ):ℝ) - 4*y ≤ 0 := by rw [hl]; linarith
  have c5 : 2*((lam:ℚ):ℝ) - 5*y ≤ 0 := by rw [hl]; linarith
  simp only [Tout, R0, dRank, hfl, ite_eq_left (show y < (1:ℝ)/2 by linarith), min_eq_right b1, max_eq_left b2, max_eq_left b3, max_eq_right c1, max_eq_right c2, max_eq_right c3, max_eq_left c4, max_eq_left c5]
  simp only [alpha, lam]
  push_cast
  ring

lemma qout_5 : ∀ y : ℝ, (1/2 : ℝ) < y → y < (43/80 : ℝ) → Tout y = (51/10 : ℝ) + (-3 : ℝ) * y := by
  intro y h1 h2
  have hy : (0:ℝ) < y := by linarith
  have ha : ((alpha : ℚ) : ℝ) = 3/40 := by norm_num [alpha]
  have hl : ((lam : ℚ) : ℝ) = 37/40 := by norm_num [lam]
  have hfl : ⌊1/y⌋ = (1:ℤ) := by
    refine Int.floor_eq_iff.2 ⟨?_, ?_⟩
    · push_cast; rw [le_div_iff₀ hy]; linarith
    · push_cast; rw [div_lt_iff₀ hy]; linarith
  have b1 : ((alpha:ℚ):ℝ) ≤ 1 - y := by rw [ha]; linarith
  have b2 : (0:ℝ) ≤ 1 + ((alpha:ℚ):ℝ) - 2*y := by rw [ha]; linarith
  have b3 : (0:ℝ) ≤ 1 + 4*((alpha:ℚ):ℝ) - 2*y := by rw [ha]; linarith
  have c1 : (0:ℝ) ≤ 2*((lam:ℚ):ℝ) - y := by rw [hl]; linarith
  have c2 : (0:ℝ) ≤ 2*((lam:ℚ):ℝ) - 2*y := by rw [hl]; linarith
  have c3 : (0:ℝ) ≤ 2*((lam:ℚ):ℝ) - 3*y := by rw [hl]; linarith
  have c4 : 2*((lam:ℚ):ℝ) - 4*y ≤ 0 := by rw [hl]; linarith
  have c5 : 2*((lam:ℚ):ℝ) - 5*y ≤ 0 := by rw [hl]; linarith
  simp only [Tout, R0, dRank, hfl, ite_eq_right (show ¬ (y < (1:ℝ)/2) by push Not; linarith), ite_eq_left (show y < (1:ℝ) by linarith), min_eq_left b1, max_eq_right b2, max_eq_right b3, max_eq_right c1, max_eq_right c2, max_eq_right c3, max_eq_left c4, max_eq_left c5]
  simp only [alpha, lam]
  push_cast
  ring

lemma qout_6 : ∀ y : ℝ, (43/80 : ℝ) < y → y < (37/60 : ℝ) → Tout y = (231/20 : ℝ) + (-15 : ℝ) * y := by
  intro y h1 h2
  have hy : (0:ℝ) < y := by linarith
  have ha : ((alpha : ℚ) : ℝ) = 3/40 := by norm_num [alpha]
  have hl : ((lam : ℚ) : ℝ) = 37/40 := by norm_num [lam]
  have hfl : ⌊1/y⌋ = (1:ℤ) := by
    refine Int.floor_eq_iff.2 ⟨?_, ?_⟩
    · push_cast; rw [le_div_iff₀ hy]; linarith
    · push_cast; rw [div_lt_iff₀ hy]; linarith
  have b1 : ((alpha:ℚ):ℝ) ≤ 1 - y := by rw [ha]; linarith
  have b2 : 1 + ((alpha:ℚ):ℝ) - 2*y ≤ 0 := by rw [ha]; linarith
  have b3 : (0:ℝ) ≤ 1 + 4*((alpha:ℚ):ℝ) - 2*y := by rw [ha]; linarith
  have c1 : (0:ℝ) ≤ 2*((lam:ℚ):ℝ) - y := by rw [hl]; linarith
  have c2 : (0:ℝ) ≤ 2*((lam:ℚ):ℝ) - 2*y := by rw [hl]; linarith
  have c3 : (0:ℝ) ≤ 2*((lam:ℚ):ℝ) - 3*y := by rw [hl]; linarith
  have c4 : 2*((lam:ℚ):ℝ) - 4*y ≤ 0 := by rw [hl]; linarith
  have c5 : 2*((lam:ℚ):ℝ) - 5*y ≤ 0 := by rw [hl]; linarith
  simp only [Tout, R0, dRank, hfl, ite_eq_right (show ¬ (y < (1:ℝ)/2) by push Not; linarith), ite_eq_left (show y < (1:ℝ) by linarith), min_eq_left b1, max_eq_left b2, max_eq_right b3, max_eq_right c1, max_eq_right c2, max_eq_right c3, max_eq_left c4, max_eq_left c5]
  simp only [alpha, lam]
  push_cast
  ring

lemma qout_7 : ∀ y : ℝ, (37/60 : ℝ) < y → y < (13/20 : ℝ) → Tout y = (97/10 : ℝ) + (-12 : ℝ) * y := by
  intro y h1 h2
  have hy : (0:ℝ) < y := by linarith
  have ha : ((alpha : ℚ) : ℝ) = 3/40 := by norm_num [alpha]
  have hl : ((lam : ℚ) : ℝ) = 37/40 := by norm_num [lam]
  have hfl : ⌊1/y⌋ = (1:ℤ) := by
    refine Int.floor_eq_iff.2 ⟨?_, ?_⟩
    · push_cast; rw [le_div_iff₀ hy]; linarith
    · push_cast; rw [div_lt_iff₀ hy]; linarith
  have b1 : ((alpha:ℚ):ℝ) ≤ 1 - y := by rw [ha]; linarith
  have b2 : 1 + ((alpha:ℚ):ℝ) - 2*y ≤ 0 := by rw [ha]; linarith
  have b3 : (0:ℝ) ≤ 1 + 4*((alpha:ℚ):ℝ) - 2*y := by rw [ha]; linarith
  have c1 : (0:ℝ) ≤ 2*((lam:ℚ):ℝ) - y := by rw [hl]; linarith
  have c2 : (0:ℝ) ≤ 2*((lam:ℚ):ℝ) - 2*y := by rw [hl]; linarith
  have c3 : 2*((lam:ℚ):ℝ) - 3*y ≤ 0 := by rw [hl]; linarith
  have c4 : 2*((lam:ℚ):ℝ) - 4*y ≤ 0 := by rw [hl]; linarith
  have c5 : 2*((lam:ℚ):ℝ) - 5*y ≤ 0 := by rw [hl]; linarith
  simp only [Tout, R0, dRank, hfl, ite_eq_right (show ¬ (y < (1:ℝ)/2) by push Not; linarith), ite_eq_left (show y < (1:ℝ) by linarith), min_eq_left b1, max_eq_left b2, max_eq_right b3, max_eq_right c1, max_eq_right c2, max_eq_left c3, max_eq_left c4, max_eq_left c5]
  simp only [alpha, lam]
  push_cast
  ring

lemma qout_8 : ∀ y : ℝ, (13/20 : ℝ) < y → y < (37/40 : ℝ) → Tout y = (42/5 : ℝ) + (-10 : ℝ) * y := by
  intro y h1 h2
  have hy : (0:ℝ) < y := by linarith
  have ha : ((alpha : ℚ) : ℝ) = 3/40 := by norm_num [alpha]
  have hl : ((lam : ℚ) : ℝ) = 37/40 := by norm_num [lam]
  have hfl : ⌊1/y⌋ = (1:ℤ) := by
    refine Int.floor_eq_iff.2 ⟨?_, ?_⟩
    · push_cast; rw [le_div_iff₀ hy]; linarith
    · push_cast; rw [div_lt_iff₀ hy]; linarith
  have b1 : ((alpha:ℚ):ℝ) ≤ 1 - y := by rw [ha]; linarith
  have b2 : 1 + ((alpha:ℚ):ℝ) - 2*y ≤ 0 := by rw [ha]; linarith
  have b3 : 1 + 4*((alpha:ℚ):ℝ) - 2*y ≤ 0 := by rw [ha]; linarith
  have c1 : (0:ℝ) ≤ 2*((lam:ℚ):ℝ) - y := by rw [hl]; linarith
  have c2 : (0:ℝ) ≤ 2*((lam:ℚ):ℝ) - 2*y := by rw [hl]; linarith
  have c3 : 2*((lam:ℚ):ℝ) - 3*y ≤ 0 := by rw [hl]; linarith
  have c4 : 2*((lam:ℚ):ℝ) - 4*y ≤ 0 := by rw [hl]; linarith
  have c5 : 2*((lam:ℚ):ℝ) - 5*y ≤ 0 := by rw [hl]; linarith
  simp only [Tout, R0, dRank, hfl, ite_eq_right (show ¬ (y < (1:ℝ)/2) by push Not; linarith), ite_eq_left (show y < (1:ℝ) by linarith), min_eq_left b1, max_eq_left b2, max_eq_left b3, max_eq_right c1, max_eq_right c2, max_eq_left c3, max_eq_left c4, max_eq_left c5]
  simp only [alpha, lam]
  push_cast
  ring

lemma qout_9 : ∀ y : ℝ, (37/40 : ℝ) < y → y < (1 : ℝ) → Tout y = (1 : ℝ) + (-2 : ℝ) * y := by
  intro y h1 h2
  have hy : (0:ℝ) < y := by linarith
  have ha : ((alpha : ℚ) : ℝ) = 3/40 := by norm_num [alpha]
  have hl : ((lam : ℚ) : ℝ) = 37/40 := by norm_num [lam]
  have hfl : ⌊1/y⌋ = (1:ℤ) := by
    refine Int.floor_eq_iff.2 ⟨?_, ?_⟩
    · push_cast; rw [le_div_iff₀ hy]; linarith
    · push_cast; rw [div_lt_iff₀ hy]; linarith
  have b1 : (1:ℝ) - y ≤ ((alpha:ℚ):ℝ) := by rw [ha]; linarith
  have b2 : 1 + ((alpha:ℚ):ℝ) - 2*y ≤ 0 := by rw [ha]; linarith
  have b3 : 1 + 4*((alpha:ℚ):ℝ) - 2*y ≤ 0 := by rw [ha]; linarith
  have c1 : (0:ℝ) ≤ 2*((lam:ℚ):ℝ) - y := by rw [hl]; linarith
  have c2 : 2*((lam:ℚ):ℝ) - 2*y ≤ 0 := by rw [hl]; linarith
  have c3 : 2*((lam:ℚ):ℝ) - 3*y ≤ 0 := by rw [hl]; linarith
  have c4 : 2*((lam:ℚ):ℝ) - 4*y ≤ 0 := by rw [hl]; linarith
  have c5 : 2*((lam:ℚ):ℝ) - 5*y ≤ 0 := by rw [hl]; linarith
  simp only [Tout, R0, dRank, hfl, ite_eq_right (show ¬ (y < (1:ℝ)/2) by push Not; linarith), ite_eq_left (show y < (1:ℝ) by linarith), min_eq_right b1, max_eq_left b2, max_eq_left b3, max_eq_right c1, max_eq_left c2, max_eq_left c3, max_eq_left c4, max_eq_left c5]
  simp only [lam]
  push_cast
  ring

lemma qout_10 : ∀ y : ℝ, (1 : ℝ) < y → y < (37/20 : ℝ) → Tout y = (37/20 : ℝ) + (-1 : ℝ) * y := by
  intro y h1 h2
  have hy : (0:ℝ) < y := by linarith
  have ha : ((alpha : ℚ) : ℝ) = 3/40 := by norm_num [alpha]
  have hl : ((lam : ℚ) : ℝ) = 37/40 := by norm_num [lam]
  have hfl : ⌊1/y⌋ = (0:ℤ) := by
    refine Int.floor_eq_iff.2 ⟨?_, ?_⟩
    · push_cast; rw [le_div_iff₀ hy]; linarith
    · push_cast; rw [div_lt_iff₀ hy]; linarith
  have c1 : (0:ℝ) ≤ 2*((lam:ℚ):ℝ) - y := by rw [hl]; linarith
  have c2 : 2*((lam:ℚ):ℝ) - 2*y ≤ 0 := by rw [hl]; linarith
  have c3 : 2*((lam:ℚ):ℝ) - 3*y ≤ 0 := by rw [hl]; linarith
  have c4 : 2*((lam:ℚ):ℝ) - 4*y ≤ 0 := by rw [hl]; linarith
  have c5 : 2*((lam:ℚ):ℝ) - 5*y ≤ 0 := by rw [hl]; linarith
  simp only [Tout, R0, dRank, hfl, ite_eq_right (show ¬ (y < (1:ℝ)/2) by push Not; linarith), ite_eq_right (show ¬ (y < (1:ℝ)) by push Not; linarith), max_eq_right c1, max_eq_left c2, max_eq_left c3, max_eq_left c4, max_eq_left c5]
  simp only [lam]
  push_cast
  ring

/-- **(5.10)** (p. 15) and **Table 4** (p. 27): the eleven affine pieces of the outer
integrand integrate to `I_out = 127751/96000`.

This is a known-answer control on `Zeta5.Iout`, which `Basic.lean` posits as the printed
rational: here it is *computed* from (5.8)–(5.9). -/
theorem eq_5_10 :
    (∫ y in (1/3 : ℝ)..(37/20 : ℝ), Tout y) = (Iout : ℝ) := by
  have c0 := piece_out (by norm_num) qout_0
  have c1 := piece_out (by norm_num) qout_1
  have c2 := piece_out (by norm_num) qout_2
  have c3 := piece_out (by norm_num) qout_3
  have c4 := piece_out (by norm_num) qout_4
  have c5 := piece_out (by norm_num) qout_5
  have c6 := piece_out (by norm_num) qout_6
  have c7 := piece_out (by norm_num) qout_7
  have c8 := piece_out (by norm_num) qout_8
  have c9 := piece_out (by norm_num) qout_9
  have c10 := piece_out (by norm_num) qout_10
  have k1 := add_adj_out c0.1 c1.1 c0.2 c1.2
  have k2 := add_adj_out k1.1 c2.1 k1.2 c2.2
  have k3 := add_adj_out k2.1 c3.1 k2.2 c3.2
  have k4 := add_adj_out k3.1 c4.1 k3.2 c4.2
  have k5 := add_adj_out k4.1 c5.1 k4.2 c5.2
  have k6 := add_adj_out k5.1 c6.1 k5.2 c6.2
  have k7 := add_adj_out k6.1 c7.1 k6.2 c7.2
  have k8 := add_adj_out k7.1 c8.1 k7.2 c8.2
  have k9 := add_adj_out k8.1 c9.1 k8.2 c9.2
  have k10 := add_adj_out k9.1 c10.1 k9.2 c10.2
  rw [k10.2]
  norm_num [Iout]

end

end Zeta5.AppendixB
