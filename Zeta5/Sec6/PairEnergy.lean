/-
Zeta5/Sec6/PairEnergy.lean  —  the kernel energy of `ρ`, pair by pair.

Only the on-interval branch of (A.1) is needed here, together with the nesting of Table 1.
-/
import Zeta5.Sec6.ArcsinePot
import Zeta5.Sec6.Measures

namespace Zeta5
namespace Sec6

open Real MeasureTheory Set Finset

noncomputable section

private lemma pairEnergyGe_nest {i j : ℕ} (hij : i ≤ j) (hj : j < 16) :
    RealBound.aT j ≤ RealBound.aT i ∧ RealBound.bT i ≤ RealBound.bT j := by
  induction j, hij using Nat.le_induction with
  | base => exact ⟨le_rfl, le_rfl⟩
  | succ k hik ih =>
    obtain ⟨h1, h2⟩ := ih (by omega)
    exact ⟨(RealBound.aT_strictAnti k hj).le.trans h1, h2.trans (RealBound.bT_strictMono k hj).le⟩

private lemma pairEnergyGe_inner {j : ℕ} (hj : j < 16) {ε : ℝ} (hε : 0 < ε) {x : ℝ}
    (hx : x ∈ Icc (RealBound.aT j) (RealBound.bT j)) :
    Real.log ((RealBound.bT j - RealBound.aT j) / 4) ≤ ∫ y, kC ε (x - y) ∂(arc j) := by
  have hab := RealBound.aT_lt_bT j hj
  have hcont : Continuous (kC ε) := continuous_kC hε.ne'
  rw [arc, integral_arcsine _ _ (f := fun y => kC ε (x - y))
    ((hcont.comp (continuous_const.sub continuous_id)).measurable)]
  obtain ⟨hI, hE⟩ := arcsine_pot hab x
  have hU : Uarc (RealBound.aT j) (RealBound.bT j) x
      = Real.log ((RealBound.bT j - RealBound.aT j) / 4) := by
    unfold Uarc; simp only [show _ ∧ _ from hx, and_self, ite_true]
  have hr0 : 0 < rad j := by unfold rad; linarith
  have hmono : (∫ θ in (0 : ℝ)..π,
        Real.log |x - ((RealBound.aT j + RealBound.bT j) / 2
          + (RealBound.bT j - RealBound.aT j) / 2 * Real.cos θ)|)
      ≤ ∫ θ in (0 : ℝ)..π, kC ε (x - (mid j + rad j * Real.cos θ)) := by
    refine intervalIntegral.integral_mono_ae_restrict pi_pos.le hI ?_ ?_
    · exact (hcont.comp (continuous_const.sub (continuous_cosMap _ _))).intervalIntegrable _ _
    · rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Icc, ae_iff]
      refine measure_mono_null (t := {Real.arccos ((x - mid j) / rad j)}) ?_ (measure_singleton _)
      intro θ hθ
      simp only [Set.mem_ofPred_eq, Classical.not_imp] at hθ
      obtain ⟨hmem, hne⟩ := hθ
      rw [Set.mem_singleton_iff]
      by_contra hc
      apply hne
      have hu : x - (mid j + rad j * Real.cos θ) ≠ 0 := by
        intro h0
        apply hc
        have : Real.cos θ = (x - mid j) / rad j := by
          field_simp; linarith
        rw [← this, Real.arccos_cos hmem.1 hmem.2]
      have := log_abs_le_kC (ε := ε) hu
      simpa [mid, rad] using this
  rw [hE, hU] at hmono
  have hpi := pi_pos
  calc Real.log ((RealBound.bT j - RealBound.aT j) / 4)
      = π⁻¹ * (π * Real.log ((RealBound.bT j - RealBound.aT j) / 4)) := by
        field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hmono (inv_nonneg.2 hpi.le)

/-- For nested components `i ≤ j < 16` (so `[a_i,b_i] ⊆ [a_j,b_j]`):

`log(L_j/4) ≤ I_k(ω_i, ω_j) = ∫∫ kC ε (x − y) dω_j(y) dω_i(x)`.

Paper: (A.2) (p. 22), "Nesting makes the potential of the `j`th interval constant on every
earlier interval", in the direction `≥` and for the regularised kernel.

Proof.  By nesting (from `RealBound.aT_strictAnti`, `RealBound.bT_strictMono`), `ω_i`-a.e. `x`
lies in `[a_j, b_j]`.  For such `x`, `∫ kC ε (x − y) dω_j(y) ≥ U^{ω_j}(x) = log(L_j/4)`, from
`kC ε u ≥ log|u|` (`u ≠ 0`, which fails for at most one `θ`) and `arcsine_pot`.  Integrate
against the probability measure `ω_i`; if the inner integral is not integrable, the left side
`log(L_j/4) ≤ 0` still bounds Lean's value `0`. -/
theorem pair_energy_ge {i j : ℕ} (hij : i ≤ j) (hj : j < 16) {ε : ℝ} (hε : 0 < ε) :
    Real.log ((RealBound.bT j - RealBound.aT j) / 4) ≤ kE ε (arc i) (arc j) := by
  obtain ⟨hn1, hn2⟩ := pairEnergyGe_nest hij hj
  have hi : i < 16 := lt_of_le_of_lt hij hj
  have hae : ∀ᵐ x ∂(arc i), Real.log ((RealBound.bT j - RealBound.aT j) / 4)
      ≤ ∫ y, kC ε (x - y) ∂(arc j) := by
    filter_upwards [arc_ae hi] with x hx
    exact pairEnergyGe_inner hj hε ⟨hn1.trans hx.1, hx.2.trans hn2⟩
  unfold kE
  by_cases hint : Integrable (fun x => ∫ y, kC ε (x - y) ∂(arc j)) (arc i)
  · calc Real.log ((RealBound.bT j - RealBound.aT j) / 4)
        = ∫ _x, Real.log ((RealBound.bT j - RealBound.aT j) / 4) ∂(arc i) := by
          rw [integral_const]; simp [arc]
      _ ≤ _ := integral_mono_ae (integrable_const _) hint hae
  · rw [integral_undef hint]
    have hab := RealBound.aT_lt_bT j hj
    obtain ⟨h0, h2⟩ := tab1_in_02 hj
    apply Real.log_nonpos <;> linarith

end

end Sec6
end Zeta5
