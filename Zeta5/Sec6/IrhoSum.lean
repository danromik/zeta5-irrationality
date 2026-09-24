/-
Zeta5/Sec6/IrhoSum.lean  —  LEAF: (A.2) as a double sum over pairs of components.
-/
import Zeta5.Sec6.Defs

namespace Zeta5
namespace Sec6

open Real Finset

noncomputable section

private lemma Irho_double_sum_aux (c f : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ range n, ∑ j ∈ range n, c i * c j * f (max i j)
      = ∑ m ∈ range n, ((∑ i ∈ range (m + 1), c i) ^ 2 - (∑ i ∈ range m, c i) ^ 2) * f m := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : ∀ i ∈ range n, c i * c n * f (max i n) = c i * c n * f n := by
      intro i hi
      rw [max_eq_right (le_of_lt (mem_range.mp hi))]
    have h2 : ∀ j ∈ range n, c n * c j * f (max n j) = c n * c j * f n := by
      intro j hj
      rw [max_eq_left (le_of_lt (mem_range.mp hj))]
    simp only [sum_range_succ (fun j => _ * c j * f (max _ j)), sum_add_distrib]
    rw [sum_range_succ (fun i => ∑ j ∈ range n, c i * c j * f (max i j)),
      sum_range_succ (fun i => c i * c n * f (max i n)), ih, sum_congr rfl h1, sum_congr rfl h2,
      sum_range_succ _ n, sum_range_succ c n, max_self, ← sum_mul, ← sum_mul, ← mul_sum,
      ← sum_mul]
    ring

/-- **LEAF (easy–medium; finite algebra).**  **(A.2) as a double sum**:

`I(ρ) = ∑_{i,j<16} c_i c_j log(L_{max(i,j)}/4)`,   `L_m = b_m − a_m`,

which is the definition `RealBound.Irho = ∑_m (S_{m+1}² − S_m²) log(L_m/4)` regrouped.

Paper: (A.2) (p. 22): "Nesting makes the potential of the `j`th interval constant on every
earlier interval.  Therefore `I(ρ) = ∑ (S_j² − S_{j−1}²) log((b_j − a_j)/4)`."

Proof plan.  Prove, for every `f : ℕ → ℝ` and `n`, by induction on `n`
(`Finset.sum_range_succ` in both indices):
`∑_{i<n} ∑_{j<n} c_i c_j f(max i j) = ∑_{m<n} (S_{m+1}² − S_m²) f(m)` with
`S_m = RealBound.cS m = ∑_{i<m} c_i`.  The step `n → n+1` adds the terms with `i = n` or
`j = n`, all with `max = n` (`max_eq_left`/`max_eq_right`, `Finset.mem_range`), totalling
`(2 c_n S_n + c_n²) f(n) = (S_{n+1}² − S_n²) f(n)`.  Apply with `n = 16`,
`f m = log((bT m − aT m)/4)`, and unfold `RealBound.Irho`, `RealBound.wT`. -/
theorem Irho_double_sum :
    RealBound.Irho = ∑ i ∈ range 16, ∑ j ∈ range 16,
      RealBound.cT i * RealBound.cT j
        * Real.log ((RealBound.bT (max i j) - RealBound.aT (max i j)) / 4) := by
  rw [Irho_double_sum_aux RealBound.cT
    (fun m => Real.log ((RealBound.bT m - RealBound.aT m) / 4)) 16]
  rfl

end

end Sec6
end Zeta5
