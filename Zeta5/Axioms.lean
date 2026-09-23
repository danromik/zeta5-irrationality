/-
Zeta5/Axioms.lean

The *only* place in this project where an `axiom` is declared.

RULES (the ground rules of this formalization; see README, "Ground rules").  Nothing
internal to Fauzan's argument may appear here: his propositions, lemmas, computations and
tables must be proved.  A finite, explicit computation is never an acceptable axiom.  What
may appear here is a standard EXTERNAL fact that Mathlib does not have, and every
declaration carries

  (i)   the precise statement,
  (ii)  a literature citation,
  (iii) one sentence on why Mathlib lacks it.

`#print axioms` on any theorem will name exactly the ones it uses.
-/
import Zeta5.Basic

namespace Zeta5
namespace Axioms

open MeasureTheory Set in
/-- **Hermite's integral formula for the Hurwitz zeta function, at `s = 5`.**
(Used by `Zeta5.Positivity`, i.e. by Proposition 2.2.)

(i) STATEMENT.  For every real `a > 0`, with `w = Zeta5.wt` the weight of (2.10),
`w(y) = (2π)⁴y⁵ ∑_{ℓ≥1} ℓ⁴e^{-2πℓy}/12`,

  `∫_0^∞ w(y)/(y² + a²) dy = a⁴ ζ(5,a) − 1/(2a) − 1/4`,

where `ζ(5,a) = ∑_{k≥0}(k+a)^{-5}` is the Hurwitz zeta function.  This is the display in
the middle of p. 5 of the paper (the line beginning "Hermite's integral formula [9,
(25.11.29)], with `a > 0`, yields").

(ii) CITATION.  DLMF 25.11.29 — the reference the paper itself gives — is Hermite's formula

  `ζ(s,a) = a^{-s}/2 + a^{1-s}/(s−1) + 2∫_0^∞ sin(s arctan(t/a)) (a²+t²)^{-s/2}/(e^{2πt}−1) dt`,

valid for `a > 0`, `s ≠ 1` (equivalently Whittaker–Watson §13.2; Erdélyi et al., *Higher
Transcendental Functions* I §1.10 (6)).  At `s = 5` its integrand is
`Im((a−it)^{-5})/(e^{2πt}−1)`, and the statement assumed here is that formula transported
through the four integrations by parts of p. 5: with `f(y) = (e^{2πy}−1)^{-1}` one has
`w(y) = y⁵f⁗(y)/12`, the four boundary products are `O(y)` at `0` and exponentially small
at infinity, and `(d/dy)⁴(y⁵/(y²+a²)) = 24a⁴Im((a−iy)^{-5})`, whence
`∫_0^∞ w(y)/(y²+a²) dy = 2a⁴∫_0^∞ Im((a−iy)^{-5})/(e^{2πy}−1) dy = a⁴(ζ(5,a) − a^{-5}/2 − a^{-4}/4)`.
NOTE: those four integrations by parts are *not* formalised; they are absorbed into
this axiom, which is therefore slightly stronger than DLMF 25.11.29 alone.

Known-answer control (numerical quadrature at 25 significant digits, both sides): equality
at `a = 0.3, 1, 2, 2.5, 6`; at `a = 1` both sides are `0.286927755143369926… = ζ(5) − 3/4`.
The referee audit of the preprint (see README, "Provenance") independently checked the integer cases
`a = 1,…,6` to 24 digits.

(iii) WHY NOT MATHLIB.  Mathlib has the Hurwitz zeta function (`HurwitzZeta.hurwitzZeta`)
and its functional equation, but no Hermite/Abel–Plana integral representation of it, and
no theory of the Eisenstein-type weight `w`. -/
axiom hermite_pole_integral (a : ℝ) (ha : 0 < a) :
    ∫ y in Ioi (0 : ℝ), wt y / (y ^ 2 + a ^ 2)
      = a ^ 4 * (∑' k : ℕ, 1 / ((k : ℝ) + a) ^ 5) - 1 / (2 * a) - 1 / 4

open Filter Finset Set in
/-- **The prime number theorem, in the partial-summation ("prime Riemann sum") form that
Proposition 5.2 consumes.**  (Used by `Zeta5.PrimeSum`, i.e. by Proposition 5.2.)

(i) STATEMENT.  Let `0 ≤ a < b` and let `φ : ℝ → ℝ` be bounded on `[a,b]` and continuous at
every point of `[a,b]` outside some finite set.  Then

  `(1/X) · Σ_{p prime, aX < p ≤ bX} φ(p/X) log p  ⟶  ∫_a^b φ(y) dy`   as `X → ∞`.

This is exactly the fact Fauzan invokes on p. 15 in the sentence *"For a bounded piecewise
continuous function `f` on `[3,M]`, partial summation and the prime number theorem give
`K^{-2} Σ_{K/M<p≤K/3} p f(K/p) log p ⟶ ∫_3^M f(x)x^{-3}dx`"* (put `φ(y) = y f(1/y)` and
`X = K`; the substitution `x = 1/y` is carried out in Lean, in
`Zeta5.PrimeSum.integral_inv_subst`), and again in the sentence *"The same argument in the
variable `y = p/K` gives (5.10) for the outer range"* (put `φ = T` of §B.2 directly).
Taking `a = 0` and `φ ≡ 1` it specialises to the prime number theorem itself in Chebyshev's
form, `θ(x) = Σ_{p ≤ x} log p ~ x`, which is how `Zeta5.PrimeSum` uses it for the range
`p ≤ K/M` and for all the `O_M(1)·θ` error terms.

(ii) CITATION.  The prime number theorem, Hadamard and de la Vallée Poussin (1896), in the
form `θ(x) ~ x`; the paper's own citation for it is [9, §27.12] (DLMF 27.12.2–27.12.4, "We
use only its asymptotic form", p. 15).  The passage from `θ(x) ~ x` to the displayed
Riemann-sum limit is Abel summation together with the Darboux criterion — a bounded function
with finitely many discontinuities is Riemann integrable, so it is squeezed between step
functions whose prime sums telescope into differences `θ(uX) − θ(vX)`.  Standard references:
Apostol, *Introduction to Analytic Number Theory*, Thm. 4.4 and §4.3 (Abel's identity, Thm.
4.2); Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, I.0 §2 and I.3.

NOTE: this is *more* than the bare prime number theorem.  It is the PNT already
transported through Abel summation and the Darboux sandwich, i.e. the "partial summation"
half of the sentence quoted above is absorbed into the axiom.  The ground rules of this
formalization (README, "Ground rules") allow the prime number theorem in whatever form the
proof actually consumes (Chebyshev `ψ`, `θ`, or the partial-summation corollary), and this
is the partial-summation corollary, stated precisely.  It contains no information about
Fauzan's functions `Γ`, `𝒩`, `R`, `R₀`, `d` or `T`: the hypotheses on `φ` are discharged,
for `T`, from Appendix B's Table 4 inside
`Zeta5.PrimeSum` (`Tout_bdd`, `Tout_piecewise`).

(iii) WHY NOT MATHLIB.  Mathlib has Chebyshev-type bounds only — `Nat.primorial_le_4_pow`
(`∏_{p ≤ n} p ≤ 4^n`, i.e. `θ(n) ≤ n log 4`) and `Nat.primeCounting` — and, as of
Mathlib v4.34.0, no proof of `ψ(x) ~ x` or `θ(x) ~ x`, hence none of its partial-summation
corollaries either. -/
axiom pnt_prime_riemann_sum (a b : ℝ) (ha : 0 ≤ a) (hab : a < b) (φ : ℝ → ℝ)
    (hbdd : ∃ C : ℝ, ∀ y ∈ Icc a b, |φ y| ≤ C)
    (hpc : ∃ D : Finset ℝ, ∀ y ∈ Icc a b, y ∉ D → ContinuousAt φ y) :
    Tendsto
      (fun X : ℝ =>
        (∑ p ∈ (Finset.Ioc ⌊a * X⌋₊ ⌊b * X⌋₊).filter Nat.Prime,
            φ ((p : ℝ) / X) * Real.log p) / X)
      atTop (nhds (∫ y in a..b, φ y))

end Axioms
end Zeta5
