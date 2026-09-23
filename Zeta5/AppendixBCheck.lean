/-
Zeta5/AppendixBCheck.lean

Known-answer controls tying `Zeta5/AppendixB.lean` to `Zeta5/Interface.lean`.

The first `example` is the whole point of the file: it type-checks
`Zeta5.AppendixB.eq_5_16_5_18` **against the statement of `Zeta5.eq_5_16_5_18` in
`Interface.lean`, verbatim**.  If the two statements ever drift apart, this file stops
compiling.  `Interface.lean` proves `eq_5_16_5_18` by `Zeta5.AppendixB.eq_5_16_5_18`, and
since 2026-09-23 the whole of Appendix B — (5.16)–(5.17) included, via `Zeta5/Tail.lean` —
is `sorry`-free.

This file contains no `sorry`.
-/
import Zeta5.Interface
import Zeta5.AppendixB

namespace Zeta5.AppendixBCheck

open Zeta5

/-- **The statement check.**  `AppendixB.eq_5_16_5_18` has exactly the type of the
interface `sorry` `Zeta5.eq_5_16_5_18`: the `example` below states the latter's type and
is proved by the former. -/
example : ∀ (M : ℕ), 40 ∣ M → 0 < M →
    (Iout : ℝ) + 6 * (lam : ℝ) / (M : ℝ)
      + (∫ x in (3 : ℝ)..(M : ℝ), RR x / x ^ 3) ≤ (AM M : ℝ) :=
  fun M hM hM0 => Zeta5.AppendixB.eq_5_16_5_18 M hM hM0

/-- And, the other way round, the interface statement proves the Appendix B one: the two are
interchangeable. -/
example : ∀ (M : ℕ), 40 ∣ M → 0 < M →
    (Iout : ℝ) + 6 * (lam : ℝ) / (M : ℝ)
      + (∫ x in (3 : ℝ)..(M : ℝ), RR x / x ^ 3) ≤ (AM M : ℝ) :=
  fun M hM hM0 => Zeta5.eq_5_16_5_18 M hM hM0

/-- (5.21) follows from Proposition 5.2 and the Appendix B bound directly, without going
through the interface statement `Zeta5.eq_5_16_5_18`. -/
theorem eq_5_21_via_AppendixB (M : ℕ) (hM : 40 ∣ M) (hM0 : 0 < M)
    (Alloc : ∀ n, InnerAllocFamily n M) (ε : ℝ) (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      Real.log (mKM n M (Alloc n)) ≤ ((AM M : ℝ) + ε) * (K n : ℝ) ^ 2 :=
  eq_5_21_of_prop_5_2 M Alloc
    (fun δ hδ => prop_5_2 M (Nat.le_of_dvd hM0 hM) Alloc δ hδ)
    (Zeta5.AppendixB.eq_5_16_5_18 M hM hM0) ε hε

/-! ## Known-answer controls on the Appendix B computation itself -/

open Zeta5.AppendixB

/-- (5.18) is the constant `I320` that `Basic.lean` posits. -/
example : (∫ x in (3:ℝ)..(20:ℝ), RR x / x ^ 3) = (I320 : ℝ) := eq_5_18.2

/-- (5.10): `I_out` is *computed* from (5.8)–(5.9), not posited. -/
example : (∫ y in (1/3 : ℝ)..(37/20 : ℝ), Tout y) = (Iout : ℝ) := eq_5_10

/-- The seventeen rows of Table 3 (p. 27) sum to (5.18), exactly. -/
example :
    (26807/161280 : ℚ) + 37383/704000 + 37523/8236800 + (-120923/6552000)
      + (-10025233/356428800) + (-110029309/3348864000) + (-2278419487/64465632000)
      + (-282415081/7724640000) + (-3236921227/87524236800) + (-3350220001/90899827200)
      + 7424224373/2217983040000 + 16775764609/955086612480 + 369043847/30810528000
      + 651380108633/86461373856000 + 472851276229/119820121344000
      + 4930060867/4724197793280 + (-15199801/11563552000) = I320 := by
  norm_num [I320]

/-- Table 3, row `j = 14`, is `16775764609/955086612480` — *not* `167757646109/955086612480`,
which a first pass off the rendered page image produced and a 600-dpi render refuted.  The
computed value settles it. -/
example : (∫ x in (14:ℝ)..(15:ℝ), RR x / x ^ 3) = (16775764609/955086612480 : ℝ) :=
  (table3_14).2

/-- Table 4 (p. 27), the eleven `(b,c)` rows, integrate to `127751/96000`. -/
example :
    (279/40 * (43/120 - 1/3) + (-9) * ((43/120:ℚ)^2 - (1/3)^2)/2)
    + (451/40 * (37/100 - 43/120) + (-21) * ((37/100:ℚ)^2 - (43/120)^2)/2)
    + (377/40 * (13/30 - 37/100) + (-16) * ((13/30:ℚ)^2 - (37/100)^2)/2)
    + (429/40 * (37/80 - 13/30) + (-19) * ((37/80:ℚ)^2 - (13/30)^2)/2)
    + (17/4 * (1/2 - 37/80) + (-5) * ((1/2:ℚ)^2 - (37/80)^2)/2)
    + (51/10 * (43/80 - 1/2) + (-3) * ((43/80:ℚ)^2 - (1/2)^2)/2)
    + (231/20 * (37/60 - 43/80) + (-15) * ((37/60:ℚ)^2 - (43/80)^2)/2)
    + (97/10 * (13/20 - 37/60) + (-12) * ((13/20:ℚ)^2 - (37/60)^2)/2)
    + (42/5 * (37/40 - 13/20) + (-10) * ((37/40:ℚ)^2 - (13/20)^2)/2)
    + (1 * (1 - 37/40) + (-2) * ((1:ℚ)^2 - (37/40)^2)/2)
    + (37/20 * (37/20 - 1) + (-1) * ((37/20:ℚ)^2 - 1^2)/2) = Iout := by
  norm_num [Iout]

/-- The quadratic coefficient of §B.1 cancels, so `R` is affine and not quadratic on the
pieces of (B.2). -/
example :
    2 * lam - 12 * lam * alpha + 2 * (Hcst ^ 2 - Hcst - lam ^ 2) - 18 * alpha ^ 2 + 6 * alpha
      = 0 := quadratic_coeff_cancels

/-- The exact margins of §B.3 (p. 28). -/
example : -1600 * (AM 200 + Ubar) - 139 / 5
    = 3089837638249482469 / 58872425992515135000 := margin_200

example : -1600 * (AM 100000 + Ubar) - 7907 / 100
    = 29873543950273155160680943 / 3679526624532195937500000000 := margin_100000

/-! ## The dependency report for Appendix B

`AppendixB.eq_5_16_5_18` is **`sorry`-free** (2026-09-23): `eq_5_16_5_17` is now proved from
`Zeta5.Tail.tail_bound`, and `eq_5_18`, `eq_5_10` and all the piece lemmas always were. -/

/-- (5.12)–(5.13): `R(x) = x F(x) + Q(x)`, proved. -/
example (x : ℝ) : RR x = x * Fcl x + Qcl x := RR_closed x

/-- `R(x)/x³` is interval-integrable on every `[a,b] ⊆ (0,∞)`, proved. -/
example : IntervalIntegrable (fun x => RR x / x ^ 3) MeasureTheory.volume (20:ℝ) (200:ℝ) :=
  intervalIntegrable_RR_div (by norm_num) (by norm_num)

#print axioms Zeta5.AppendixB.RR_closed
#print axioms Zeta5.AppendixB.intervalIntegrable_RR_div
#print axioms Zeta5.AppendixB.eq_5_18
#print axioms Zeta5.AppendixB.eq_5_10
#print axioms Zeta5.AppendixB.Gam_eq
#print axioms Zeta5.AppendixB.RR_affine
#print axioms Zeta5.AppendixB.eq_5_16_5_18

end Zeta5.AppendixBCheck
