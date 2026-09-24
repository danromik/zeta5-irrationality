/-
Zeta5/Sec6/Swap.lean  —  LEAF: the Fubini–Tonelli step of the zero-mass energy argument.

Role in the proof of (6.14): the interchange `∬ L_{a,b}(|z−w|) dν dν = −½∫_a^b J(s)/s ds` in
the proof of Lemma 6.2 (p. 18), for the Cauchy kernel.  Because the kernel is bounded on the
(compact) supports, no truncation `a ↓ 0, b ↑ ∞` and no dominated convergence are needed.
-/
import Zeta5.Sec6.Defs

namespace Zeta5
namespace Sec6

open Real MeasureTheory Set

noncomputable section

/-- **LEAF (medium–hard; pure measure theory).**  For finite measures `μ, ν` on `ℝ` carried by
`[−R, R]`, the `s`-integral of the Frullani integrand commutes with the double integral:

`∫∫ (∫_0^∞ frF ε s (x−y) ds) dν(y) dμ(x) = ∫_0^∞ (∫∫ frF ε s (x−y) dν(y) dμ(x)) ds`,

and the right-hand integrand is integrable on `(0,∞)`.

Paper: the interchange in the proof of Lemma 6.2 (p. 18): "These interchanges are justified by
the bounded Gaussian kernel and the finiteness of |ν|."

Proof plan.  Pointwise `0 ≤ frF ε s d ≤ d² e^{-sε²}` for `s > 0` (as in
`frullani_integrable`); on the supports `d² = (x−y)² ≤ 4R²`, so `frF ε s (x−y)` is dominated
on `(volume.restrict (Ioi 0)).prod (μ.prod ν)` by `4R² e^{-sε²}`, which is integrable there
(`exp_neg_integrableOn_Ioi`, finiteness of `μ, ν`; use `Integrable.mono'` with the a.e. bound,
obtained from `hμ, hν` via `Measure.QuasiMeasurePreserving`/`ae_prod`-type lemmas or by
first replacing `μ, ν` by their restrictions to `Icc (−R) R`, which does not change any of the
integrals: `Measure.restrict_eq_self_of_ae_mem`).  The integrand
`(s, x, y) ↦ frF ε s (x − y)` is measurable (it is continuous on `Ioi 0 × ℝ × ℝ`; or use
`Measurable` lemmas for `exp`, `div`: `fun_prop`/`measurability`).  Then apply
`MeasureTheory.integral_integral_swap` twice (first `y ↔ s` inside, for a.e. `x`, then
`x ↔ s`), or `integral_prod` / `integral_prod_symm` on the triple product.  Integrability of
`s ↦ ∫∫ frF` is `Integrable.integral_prod_left`-type (or the bound `4R² μ(ℝ)ν(ℝ) e^{-sε²}`). -/
theorem swap_frullani (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν] {R ε : ℝ}
    (hε : 0 < ε) (hμ : ∀ᵐ x ∂μ, |x| ≤ R) (hν : ∀ᵐ y ∂ν, |y| ≤ R) :
    IntegrableOn (fun s => ∫ x, ∫ y, frF ε s (x - y) ∂ν ∂μ) (Ioi (0 : ℝ)) ∧
      ∫ x, ∫ y, (∫ s in Ioi (0 : ℝ), frF ε s (x - y)) ∂ν ∂μ
        = ∫ s in Ioi (0 : ℝ), ∫ x, ∫ y, frF ε s (x - y) ∂ν ∂μ := by
  sorry

end

end Sec6
end Zeta5
