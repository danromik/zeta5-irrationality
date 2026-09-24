/-
Zeta5/Sec6/Frullani.lean  —  LEAVES: the Frullani representation of the Cauchy kernel.

Role in the proof of (6.14): replaces the identity `½∫_0^∞ (e^{-s} - e^{-sr²})/s ds = log r`
in the proof of Lemma 6.2 (p. 18).  With the Cauchy-regularised kernel `kC ε d = ½log(d²+ε²)`
the relevant identity is

    ∫_0^∞ e^{-sε²}(1 - e^{-sd²})/s ds = log(1 + d²/ε²)          (ε > 0, d ∈ ℝ),

i.e. `kC ε d = log ε + ½ ∫_0^∞ frF ε s d ds` (`CND.kC_eq_frullani`).
-/
import Zeta5.Sec6.Defs

namespace Zeta5
namespace Sec6

open Real MeasureTheory Set

noncomputable section

/-- **LEAF (easy–medium).**  The Frullani integrand `s ↦ e^{-sε²}(1-e^{-sd²})/s` is
integrable on `(0,∞)`.

Paper: implicit in the proof of Lemma 6.2 (p. 18).

Proof plan.  Pointwise for `s > 0`: `0 ≤ frF ε s d ≤ d² e^{-sε²}`, because
`0 ≤ 1 - e^{-x} ≤ x` for `x = sd² ≥ 0` (`Real.add_one_le_exp` applied to `-x`, and
`Real.exp_le_one_iff`/`Real.exp_nonpos`).  The majorant `s ↦ d² e^{-ε² s}` is integrable on
`Ioi 0` (`integrableOn_Ioi_exp_neg_mul`-type lemmas, e.g. `exp_neg_integrableOn_Ioi 0 hε'`
with `hε' : 0 < ε²`, then `.const_mul`).  Conclude with `Integrable.mono'`; measurability from
`ContinuousOn.aestronglyMeasurable` on `Ioi 0` (the integrand is continuous there; note Lean's
`x/0 = 0` makes it `0` at `s = 0`, which is irrelevant on `Ioi 0`). -/
theorem frullani_integrable {ε : ℝ} (hε : 0 < ε) (d : ℝ) :
    IntegrableOn (fun s => frF ε s d) (Ioi (0 : ℝ)) := by
  have hε2 : 0 < ε ^ 2 := by positivity
  have hmaj : IntegrableOn (fun s : ℝ => d ^ 2 * Real.exp (-(ε ^ 2) * s)) (Ioi (0 : ℝ)) :=
    (exp_neg_integrableOn_Ioi 0 hε2).const_mul _
  refine hmaj.mono' ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    intro s hs
    have hs0 : s ≠ 0 := ne_of_gt hs
    unfold frF
    exact (ContinuousAt.div (by fun_prop) continuousAt_id hs0).continuousWithinAt
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall ?_)
    intro s hs
    have hs0 : (0 : ℝ) < s := hs
    have hx : 0 ≤ s * d ^ 2 := by positivity
    have h1 : 0 ≤ 1 - Real.exp (-(s * d ^ 2)) := by
      have := Real.exp_le_one_iff.2 (neg_nonpos.2 hx); linarith
    have h2 : 1 - Real.exp (-(s * d ^ 2)) ≤ s * d ^ 2 := by
      have := Real.add_one_le_exp (-(s * d ^ 2)); linarith
    have hE := Real.exp_pos (-(s * ε ^ 2))
    unfold frF
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), div_le_iff₀ hs0]
    have : -(ε ^ 2) * s = -(s * ε ^ 2) := by ring
    rw [this]
    nlinarith [mul_le_mul_of_nonneg_left h2 hE.le]

/-- **LEAF (easy–medium).**  **Frullani's integral for the Cauchy kernel**:
`∫_0^∞ e^{-sε²}(1 - e^{-sd²})/s ds = log(1 + d²/ε²)`.

Paper: the displayed identity `½∫_0^∞ (e^{-s}-e^{-sr²})/s ds = log r` in the proof of
Lemma 6.2 (p. 18), in the form needed for the kernel `½log(d²+ε²)`.

Proof plan.  Mathlib has Frullani's theorem: `Frullani.integral_Ioi_eq`
(`Mathlib/Analysis/SpecialFunctions/FrullaniIntegral.lean`):
`∫ x in Ioi 0, x⁻¹ • (f (a*x) - f (b*x)) = log (b/a) • (L - R)` for `f` locally integrable on
`Ioi 0`, `f → L` at `0⁺`, `f → R` at `+∞`, `0 < a, b`, and the integrand integrable.
Take `f = fun x => exp (-x)`, `a = ε²`, `b = ε² + d²`, `L = 1`, `R = 0`
(`Real.tendsto_exp_neg_atTop_nhds_zero`, continuity of `exp` at `0`).  Rewrite
`frF ε s d = s⁻¹ • (f (ε² * s) - f ((ε² + d²) * s))` (`Real.exp_add`, `ring`); integrability is
`frullani_integrable` (transported along this pointwise identity on `Ioi 0` with
`integrableOn_congr_fun`/`setIntegral_congr_fun`).  Finally
`log ((ε² + d²)/ε²) = log (1 + d²/ε²)` by `field_simp`. -/
theorem frullani_cauchy {ε : ℝ} (hε : 0 < ε) (d : ℝ) :
    ∫ s in Ioi (0 : ℝ), frF ε s d = Real.log (1 + d ^ 2 / ε ^ 2) := by
  have hε2 : 0 < ε ^ 2 := by positivity
  have hb : 0 < ε ^ 2 + d ^ 2 := by positivity
  have hpt : ∀ s ∈ Ioi (0 : ℝ), frF ε s d =
      s⁻¹ • ((fun x => Real.exp (-x)) (ε ^ 2 * s) - (fun x => Real.exp (-x)) ((ε ^ 2 + d ^ 2) * s)) := by
    intro s _
    simp only [frF, smul_eq_mul]
    have : Real.exp (-((ε ^ 2 + d ^ 2) * s)) = Real.exp (-(s * ε ^ 2)) * Real.exp (-(s * d ^ 2)) := by
      rw [← Real.exp_add]; ring_nf
    rw [this]; ring_nf
  rw [setIntegral_congr_fun measurableSet_Ioi hpt]
  have hloc : LocallyIntegrableOn (fun x : ℝ => Real.exp (-x)) (Ioi 0) :=
    (Real.continuous_exp.comp continuous_neg).continuousOn.locallyIntegrableOn measurableSet_Ioi
  rw [Frullani.integral_Ioi_eq (L := (1:ℝ)) (R := 0) hloc hε2 hb]
  · simp only [sub_zero, smul_eq_mul, mul_one]
    congr 1
    field_simp
  · have : Filter.Tendsto (fun x : ℝ => Real.exp (-x)) (nhds 0) (nhds 1) := by
      have := ((Real.continuous_exp.comp continuous_neg).tendsto 0)
      simpa [Function.comp_def] using this
    exact this.mono_left nhdsWithin_le_nhds
  · exact Real.tendsto_exp_neg_atTop_nhds_zero
  · exact (integrableOn_congr_fun hpt measurableSet_Ioi).mp (frullani_integrable hε d)

end

end Sec6
end Zeta5
