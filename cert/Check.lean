/-
The main theorem and the axiom, restated using only Mathlib names. If this file compiles, the
theorem proves exactly the statement written here, independently of any definition or notation
in this project.

Run from the repository root, after `lake build`:
  lake env lean cert/Check.lean
-/
import Zeta5

open Filter

/-- ζ(5) is irrational. -/
example : Irrational (∑' v : ℕ, (1 : ℝ) / ((v : ℝ) + 1) ^ 5) :=
  Zeta5.zeta5_irrational

/-- The axiom is the prime number theorem θ(x) ~ x, with Mathlib's `Chebyshev.theta`. -/
example : Tendsto (fun x : ℝ => Chebyshev.theta x / x) atTop (nhds 1) :=
  Zeta5.Axioms.chebyshev_theta_asymptotic

#print axioms Zeta5.zeta5_irrational
