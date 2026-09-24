/-
Zeta5/Sec6/ArcsinePot.lean  —  LEAF: the arcsine potential (A.1) for a general interval.
-/
import Zeta5.Sec6.LogCos

namespace Zeta5
namespace Sec6

open Real MeasureTheory Set

noncomputable section

/-- **LEAF (easy–medium; algebra on top of `LogCos`).**  **(A.1)**: for `a < b` and every
real `t`, with `m = (a+b)/2`, `r = (b−a)/2`,

`∫_0^π log|t − (m + r cos θ)| dθ = π · U^{ω_[a,b]}(t)`   (`Uarc`, both branches),

and the integrand is interval integrable.  Since `ω_[a,b]` is the push-forward of `dθ/π` under
`θ ↦ m + r cos θ` (`arcsine`, `integral_arcsine`), this is exactly the paper's (A.1).

Paper: (A.1) (p. 21) and its proof (p. 22).

Proof plan.  `t − (m + r cos θ) = r (x − cos θ)` with `x = (t − m)/r`, `r > 0`.  For
`x ≠ cos θ`, `log|r(x − cos θ)| = log r + log|x − cos θ|` (`Real.log_mul`, `abs_mul`); the
exceptional set `{θ ∈ [0,π] : cos θ = x}` has at most one point (`Real.injOn_cos`), hence is
null, so the two integrands agree a.e. (`intervalIntegral.integral_congr_ae`; the integrability
transfers by `IntervalIntegrable.congr`/`.add` of `intervalIntegrable_log_abs_sub_cos` and a
constant).  Thus the integral is `π log r + π Psi x` (`integral_log_abs_sub_cos`).  Then check
`log r + Psi x = Uarc a b t`:
* `|x| ≤ 1 ↔ a ≤ t ∧ t ≤ b`, and `log r − log 2 = log((b−a)/4)`;
* for `|x| > 1`: `r(|x| + √(x²−1)) = |t − m| + √((t−m)² − r²)` and `(t−m)² − r² = (t−a)(t−b)`,
  so `log r + log((|x|+√(x²−1))/2) = log((|t−m| + √((t−a)(t−b)))/2)`
  (`Real.sqrt_mul_self`, `Real.sqrt_mul`, `abs_div`, `Real.log_mul`). -/
theorem arcsine_pot {a b : ℝ} (hab : a < b) (t : ℝ) :
    IntervalIntegrable (fun θ => Real.log |t - ((a + b) / 2 + (b - a) / 2 * Real.cos θ)|)
        volume 0 π ∧
      ∫ θ in (0 : ℝ)..π, Real.log |t - ((a + b) / 2 + (b - a) / 2 * Real.cos θ)|
        = π * Uarc a b t := by
  sorry

end

end Sec6
end Zeta5
