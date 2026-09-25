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

open Filter in
/-- **The prime number theorem, in Chebyshev's form `θ(x) ~ x`.**  (Used by `Zeta5.PNT`,
hence by `Zeta5.PrimeSum`, i.e. by Proposition 5.2.)

(i) STATEMENT.  `θ(x)/x → 1` as `x → ∞`, where `θ(x) = Σ_{p ≤ x, p prime} log p` is
Mathlib's own `Chebyshev.theta` (`Mathlib/NumberTheory/Chebyshev.lean`:
`θ x = ∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, log p`).  This is the textbook statement with nothing
added: it mentions no function, constant or definition of this project.

(ii) CITATION.  The prime number theorem, Hadamard and de la Vallée Poussin (1896), in
Chebyshev's form `θ(x) ~ x`; e.g. Apostol, *Introduction to Analytic Number Theory*, Thm. 4.4
(equivalence of `π(x) ~ x/log x`, `ψ(x) ~ x` and `θ(x) ~ x`) together with the prime number
theorem of Ch. 13.  The paper's own citation for it is [9, §27.12] (DLMF 27.12.2–27.12.4,
"We use only its asymptotic form", p. 15).  The passage from `θ(x) ~ x` to the prime
Riemann sums that Proposition 5.2 consumes (the "partial summation" of p. 15) is *proved*,
in `Zeta5.PNT.prime_riemann_sum`.

Numerical sanity check (`numerics/axioms/pnt_theta.py`): `θ(x)/x = 0.95625, 0.98960,
0.99685, 0.99848, 0.99952` at `x = 10³,…,10⁷`.

(iii) WHY NOT MATHLIB.  As of Mathlib v4.34.0, `Mathlib/NumberTheory/Chebyshev.lean` defines
`θ` and `ψ` and proves Chebyshev-type bounds (`θ x ≤ log 4 · x`, `ψ − θ = O(√x)`, lower
bounds), but not `θ(x) ~ x` or `ψ(x) ~ x`. -/
axiom chebyshev_theta_asymptotic :
    Tendsto (fun x : ℝ => Chebyshev.theta x / x) atTop (nhds 1)

end Axioms
end Zeta5
