/-
Zeta5/Sec6/Defs.lean  —  the shared definitions of the proof of (6.14).

The route is described in the module docstring of `Zeta5/Sec6/Final.lean`.  (6.14) is reduced
to a *configuration bound* (the paper's (6.9)) by the Gram-integral argument (6.10)–(6.13)
(`Zeta5/Sec6/Gram.lean`).  The configuration bound is proved not by the paper's Lemma 6.2 for
the singular kernel `log|z-w|` on `ℂ` with circle regularisation, but by the same zero-mass
energy argument for the **Cauchy-regularised kernel on the real line**

    kC ε x = ½ log (x² + ε²)   ( = log |x + iε| ),

which is continuous, `≥ log|x|` for `x ≠ 0`, equal to `log ε` at `0`, and conditionally
negative definite (`cauchy_cnd`).  The points `t_i` are kept as Dirac masses; the arcsine
measures are push-forwards of `dθ/π` on `[0,π]` under `θ ↦ m + r cos θ`, so every singular
integral that occurs is a one-dimensional integral in `θ`.
-/
import Zeta5.RealBound

namespace Zeta5
namespace Sec6

open Real MeasureTheory Set Finset Polynomial
open scoped NNReal ENNReal

noncomputable section

/-! ## 1. The external field `V` -/

/-- **(6.1)**: `V(t) = 2π√t + ∫_0^1 log(t+u²)du − 6∫_0^α log(t+u²)du`. -/
def Vfield (t : ℝ) : ℝ :=
  2 * π * Real.sqrt t + (∫ u in (0 : ℝ)..1, Real.log (t + u ^ 2))
    - 6 * ∫ u in (0 : ℝ)..(alpha : ℝ), Real.log (t + u ^ 2)

/-- **(A.5)**, the closed form of `V` for `t > 0` (with `α = 3/40` written out).
(At `t = 0`, Lean's `1/0 = 0` makes the bracket term vanish.) -/
def Vclosed (t : ℝ) : ℝ :=
  Real.log (1 + t) - 6 * (3 / 40) * Real.log (t + (3 / 40) ^ 2) - 2 + 12 * (3 / 40)
    + 2 * Real.sqrt t * (π + arctan (1 / Real.sqrt t) - 6 * arctan ((3 / 40) / Real.sqrt t))

/-! ## 2. The arcsine potential (A.1) -/

/-- **(A.1)**, the potential `U^{ω_[a,b]}(t)` of the unit arcsine measure of `[a,b]`, in
closed form (`Real.sqrt` of a negative number is `0`, so the formula is total). -/
def Uarc (a b t : ℝ) : ℝ :=
  if a ≤ t ∧ t ≤ b then Real.log ((b - a) / 4)
  else Real.log ((|t - (a + b) / 2| + Real.sqrt ((t - a) * (t - b))) / 2)

/-- `U^ρ(t) = ∑_j c_j U^{ω_[a_j,b_j]}(t)`, in closed form (Table 1). -/
def Urho (t : ℝ) : ℝ :=
  ∑ j ∈ range 16, RealBound.cT j * Uarc (RealBound.aT j) (RealBound.bT j) t

/-- The normalised arcsine potential: `(1/π)∫_0^π log|x − cos θ| dθ = Psi x`
(`integral_log_abs_sub_cos`). -/
def Psi (x : ℝ) : ℝ :=
  if |x| ≤ 1 then -Real.log 2 else Real.log ((|x| + Real.sqrt (x ^ 2 - 1)) / 2)

/-! ## 3. The Cauchy-regularised kernel and its energies -/

/-- The Cauchy-regularised logarithmic kernel `½ log(x² + ε²) = log|x + iε|`. -/
def kC (ε x : ℝ) : ℝ := Real.log (x ^ 2 + ε ^ 2) / 2

/-- The mutual kernel energy `I_k(μ,ν) = ∫∫ kC ε (x − y) dν(y) dμ(x)` (iterated). -/
def kE (ε : ℝ) (μ ν : Measure ℝ) : ℝ := ∫ x, ∫ y, kC ε (x - y) ∂ν ∂μ

/-- The Frullani integrand: `∫_0^∞ frF ε s d ds = log(1 + d²/ε²)` (`frullani_cauchy`). -/
def frF (ε s d : ℝ) : ℝ := Real.exp (-(s * ε ^ 2)) * (1 - Real.exp (-(s * d ^ 2))) / s

/-- The Gaussian mutual energy `G_s(μ,ν) = ∫∫ e^{-s(x−y)²} dν(y) dμ(x)`. -/
def gaussE (s : ℝ) (μ ν : Measure ℝ) : ℝ :=
  ∫ x, ∫ y, Real.exp (-(s * (x - y) ^ 2)) ∂ν ∂μ

/-! ## 4. The measures -/

/-- The unit arcsine measure of `[m − r, m + r]`: the push-forward of `dθ/π` on `[0,π]`
under `θ ↦ m + r cos θ`.  (Its density is `1/(π√((t−a)(b−t)))`; that is never used.) -/
def arcsine (m r : ℝ) : Measure ℝ :=
  (Real.toNNReal π⁻¹) • (volume.restrict (Icc (0 : ℝ) π)).map (fun θ => m + r * Real.cos θ)

/-- Midpoint `(a_j + b_j)/2` of the `j`-th interval of Table 1. -/
def mid (j : ℕ) : ℝ := (RealBound.aT j + RealBound.bT j) / 2

/-- Half-length `(b_j − a_j)/2` of the `j`-th interval of Table 1. -/
def rad (j : ℕ) : ℝ := (RealBound.bT j - RealBound.aT j) / 2

/-- `ω_j = ω_[a_j,b_j]`. -/
def arc (j : ℕ) : Measure ℝ := arcsine (mid j) (rad j)

/-- **The measure `ρ = ∑_j c_j ω_[a_j,b_j]`** of Appendix A.1. -/
def rhoM : Measure ℝ := ∑ j ∈ range 16, (Real.toNNReal (RealBound.cT j)) • arc j

/-- The empirical measure `σ = K⁻¹ ∑_i δ_{t_i}` of a configuration. -/
def pts {m : ℕ} (K : ℝ) (t : Fin m → ℝ) : Measure ℝ :=
  ∑ i, (Real.toNNReal K⁻¹) • Measure.dirac (t i)

instance (m r : ℝ) : IsFiniteMeasure (arcsine m r) := by
  unfold arcsine
  have := Measure.isFiniteMeasure_map (volume.restrict (Icc (0 : ℝ) π))
    (fun θ => m + r * Real.cos θ)
  infer_instance

instance (j : ℕ) : IsFiniteMeasure (arc j) := by unfold arc; infer_instance

instance : IsFiniteMeasure rhoM := by unfold rhoM; infer_instance

instance {m : ℕ} (K : ℝ) (t : Fin m → ℝ) : IsFiniteMeasure (pts K t) := by
  unfold pts; infer_instance

/-! ## 5. The Gram side (the interface between (6.9) and (6.10)–(6.13)) -/

/-- The weight of (6.10), in the form the matrix entries carry it:
`D_N(y²)⁵/D_tail(y²)·w(y)`  (`= D_N(y²)⁶/D_K(y²)·w(y)` by `D_mul_Dtail`). -/
def fW (n : ℕ) (y : ℝ) : ℝ :=
  aeval (y ^ 2 : ℝ) (D (N n)) ^ 5 / aeval (y ^ 2 : ℝ) (Dtail n) * wt y

/-- **The configuration bound**, in exponentiated ("product") form: the form in which (6.9)
is consumed by (6.13).  Coincident points are harmless (the product is `0`).  The paper's
(6.9) is `ConfigBound n ((λM₀ − I(ρ))K² + (120+√2)h + 2h log K)`. -/
def ConfigBound (n : ℕ) (A : ℝ) : Prop :=
  ∀ t : Fin (h n) → ℝ, (∀ i, 0 < t i) →
    (∏ i, ∏ j ∈ Ioi i, (t j - t i)) ^ 2
        * Real.exp (-(K n : ℝ) * ∑ i, Vfield (t i) + ∑ i, Real.sqrt (t i))
      ≤ Real.exp A

/-! ## 6. Elementary facts about the kernel -/

theorem kC_zero (ε : ℝ) : kC ε 0 = Real.log ε := by
  unfold kC
  rw [show (0 : ℝ) ^ 2 + ε ^ 2 = ε ^ 2 by ring, Real.log_pow]; push_cast; ring

theorem kC_neg (ε x : ℝ) : kC ε (-x) = kC ε x := by
  unfold kC; rw [neg_sq]

theorem kC_sub_comm (ε x y : ℝ) : kC ε (x - y) = kC ε (y - x) := by
  rw [← kC_neg, neg_sub]

/-- NB the hypothesis `x ≠ 0` is necessary: `log |0| = 0 > log ε = kC ε 0` for `ε < 1`. -/
theorem log_abs_le_kC {ε x : ℝ} (hx : x ≠ 0) : Real.log |x| ≤ kC ε x := by
  unfold kC
  have hax : 0 < |x| := abs_pos.2 hx
  have h1 : Real.log (|x| ^ 2) ≤ Real.log (x ^ 2 + ε ^ 2) :=
    Real.log_le_log (by positivity) (by rw [sq_abs]; nlinarith [sq_nonneg ε])
  rw [Real.log_pow] at h1; push_cast at h1; linarith

theorem continuous_kC {ε : ℝ} (hε : ε ≠ 0) : Continuous (kC ε) := by
  unfold kC
  have hpos : ∀ x : ℝ, x ^ 2 + ε ^ 2 ≠ 0 := fun x => by positivity
  exact ((continuous_pow 2).add continuous_const).log hpos |>.div_const 2

end

end Sec6
end Zeta5
