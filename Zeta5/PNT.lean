/-
Zeta5/PNT.lean

The prime-number-theorem input of Proposition 5.2, derived from the bare prime number
theorem in Chebyshev's form `θ(x) ~ x`.

(Used by `Zeta5.PrimeSum`, i.e. by Proposition 5.2.)

`Zeta5.PNT.prime_riemann_sum` is proved here from the axiom
`Zeta5.Axioms.chebyshev_theta_asymptotic` (the prime number theorem as `θ(x)/x → 1`, with
Mathlib's own `Chebyshev.theta`) by a Darboux-type sandwich:

1.  `θ(cX)/X → c` for every `c ≥ 0` (`theta_scaled`);
2.  a bounded function continuous off a finite set `D` has, for every `ε`, a uniform
    partition of `[a,b]` whose oscillations `ω_j` satisfy `Σ ω_j h ≤ ε`
    (`partition_osc`: small balls around `D` have small total length, and off them the
    function is uniformly continuous at a compact set, `IsCompact.uniformContinuousAt_of_continuousAt`);
3.  on each piece `(y_j, y_{j+1}]` the prime sum is `φ(y_{j+1}) (θ(y_{j+1}X) − θ(y_jX))`
    and the integral is `φ(y_{j+1}) h`, each up to `ω_j` times the mass (`piece_bound`);
4.  the prime sum over `(aX, bX]` telescopes into the pieces (`sum_Ioc_telescope`).
-/
import Mathlib
import Zeta5.Basic
import Zeta5.Axioms

namespace Zeta5
namespace PNT

open Filter Finset Set MeasureTheory Topology

/-! ## 1. Scaled Chebyshev function -/

lemma theta_scaled (c : ℝ) (hc : 0 ≤ c) :
    Tendsto (fun X : ℝ => Chebyshev.theta (c * X) / X) atTop (nhds c) := by
  rcases hc.eq_or_lt with rfl | hc
  · simp [Chebyshev.theta_zero]
  · have h1 : Tendsto (fun X : ℝ => c * X) atTop atTop := tendsto_id.const_mul_atTop hc
    have h2 := (Axioms.chebyshev_theta_asymptotic.comp h1).const_mul c
    rw [mul_one] at h2
    refine h2.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with X hX
    simp only [Function.comp]
    field_simp

lemma theta_sub (u v : ℝ) (huv : u ≤ v) :
    Chebyshev.theta v - Chebyshev.theta u
      = ∑ p ∈ (Finset.Ioc ⌊u⌋₊ ⌊v⌋₊).filter Nat.Prime, Real.log p := by
  unfold Chebyshev.theta
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter,
    ← Finset.sum_Ioc_consecutive _ (Nat.zero_le ⌊u⌋₊) (Nat.floor_mono huv)]
  ring

/-! ## 2. Telescoping of sums over consecutive `Ioc` blocks -/

lemma sum_Ioc_telescope (F : ℕ → ℕ) (hF : Monotone F) (g : ℕ → ℝ) (N : ℕ) :
    ∑ i ∈ Finset.Ioc (F 0) (F N), g i
      = ∑ j ∈ Finset.range N, ∑ i ∈ Finset.Ioc (F j) (F (j + 1)), g i := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih,
      Finset.sum_Ioc_consecutive _ (hF (Nat.zero_le n)) (hF (Nat.le_succ n))]

/-! ## 3. Integrability -/

lemma intervalIntegrable_of_bdd_pc (a b : ℝ) (hab : a ≤ b) (φ : ℝ → ℝ)
    (hbdd : ∃ C : ℝ, ∀ y ∈ Icc a b, |φ y| ≤ C)
    (hpc : ∃ D : Finset ℝ, ∀ y ∈ Icc a b, y ∉ D → ContinuousAt φ y) :
    IntervalIntegrable φ volume a b := by
  obtain ⟨C, hC⟩ := hbdd
  obtain ⟨D, hD⟩ := hpc
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
  have hcont : ContinuousOn φ (Icc a b \ (D : Set ℝ)) := fun y hy =>
    (hD y hy.1 hy.2).continuousWithinAt
  have hmeas : AEStronglyMeasurable φ (volume.restrict (Icc a b \ (D : Set ℝ))) :=
    hcont.aestronglyMeasurable (measurableSet_Icc.diff D.finite_toSet.measurableSet)
  have hnull : volume (D : Set ℝ) = 0 := D.finite_toSet.measure_zero _
  rw [Measure.restrict_congr_set (sdiff_null_ae_eq_self hnull)] at hmeas
  refine IntegrableOn.of_bound measure_Icc_lt_top hmeas C ?_
  exact (ae_restrict_mem measurableSet_Icc).mono fun y hy => by
    simpa [Real.norm_eq_abs] using hC y hy

/-! ## 4. The Darboux-type partition lemma -/

lemma partition_osc (a b : ℝ) (hab : a < b) (φ : ℝ → ℝ) (C : ℝ)
    (hC : ∀ y ∈ Icc a b, |φ y| ≤ C) (D : Finset ℝ)
    (hD : ∀ y ∈ Icc a b, y ∉ D → ContinuousAt φ y) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, 0 < N ∧ ∃ ω : ℕ → ℝ, (∀ j, 0 ≤ ω j) ∧
      (∀ j < N, ∀ y ∈ Icc (a + (j : ℝ) * ((b - a) / N)) (a + ((j + 1 : ℕ) : ℝ) * ((b - a) / N)),
          |φ y - φ (a + ((j + 1 : ℕ) : ℝ) * ((b - a) / N))| ≤ ω j) ∧
      ∑ j ∈ Finset.range N, ω j * ((b - a) / N) ≤ ε := by
  classical
  have hba : 0 < b - a := sub_pos.2 hab
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hC a ⟨le_rfl, hab.le⟩)
  set m : ℕ := D.card with hm
  set η : ℝ := ε / (8 * (C + 1) * ((m : ℝ) + 1)) with hη
  have hη0 : 0 < η := by positivity
  set ε' : ℝ := ε / (4 * (b - a)) with hε'
  have hε'0 : 0 < ε' := by positivity
  set U : Set ℝ := ⋃ d ∈ D, Metric.ball d η with hU
  set Kc : Set ℝ := Icc a b \ U with hKc
  have hKcpt : IsCompact Kc :=
    isCompact_Icc.diff (isOpen_biUnion fun d _ => Metric.isOpen_ball)
  have hKcont : ∀ x ∈ Kc, ContinuousAt φ x := by
    intro x hx
    refine hD x hx.1 fun hxD => hx.2 ?_
    exact Set.mem_biUnion hxD (Metric.mem_ball_self hη0)
  have hUC := hKcpt.uniformContinuousAt_of_continuousAt φ hKcont
    (Metric.dist_mem_uniformity hε'0)
  obtain ⟨δ, hδ0, hδ⟩ := Metric.mem_uniformity_dist.1 hUC
  obtain ⟨N, hN⟩ := exists_nat_gt ((b - a) / δ)
  have hNpos : 0 < N := by
    have : 0 < (b - a) / δ := div_pos hba hδ0
    exact_mod_cast this.trans hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  set h : ℝ := (b - a) / N with hh
  have hh0 : 0 < h := div_pos hba hNr
  have hNh : (N : ℝ) * h = b - a := by rw [hh]; field_simp
  have hhδ : h < δ := by
    rw [div_lt_iff₀ hδ0] at hN
    rw [hh, div_lt_iff₀ hNr]; linarith
  let good : ℕ → Prop := fun j => ∃ x ∈ Kc, x ∈ Icc (a + (j : ℝ) * h) (a + ((j + 1 : ℕ) : ℝ) * h)
  -- pieces lie in `[a,b]`
  have hpiece : ∀ j < N, ∀ z ∈ Icc (a + (j : ℝ) * h) (a + ((j + 1 : ℕ) : ℝ) * h), z ∈ Icc a b := by
    intro j hj z hz
    have hjN : ((j + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast hj
    have h1 : 0 ≤ (j : ℝ) * h := by positivity
    have h2 : ((j + 1 : ℕ) : ℝ) * h ≤ N * h := mul_le_mul_of_nonneg_right hjN hh0.le
    exact ⟨by linarith [hz.1], by linarith [hz.2]⟩
  refine ⟨N, hNpos, fun j => if good j then 2 * ε' else 2 * C, ?_, ?_, ?_⟩
  · intro j; dsimp only; split_ifs <;> positivity
  · intro j hj z hz
    have hzab := hpiece j hj z hz
    have heab := hpiece j hj _ ⟨by push_cast; linarith, le_rfl⟩
    dsimp only
    split_ifs with hg
    · obtain ⟨x, hxK, hx⟩ := hg
      have hcast : ((j + 1 : ℕ) : ℝ) * h = (j : ℝ) * h + h := by push_cast; ring
      rw [hcast] at hx hz
      have d1 : dist x z < δ := by
        rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hx.1, hx.2, hz.1, hz.2]
      have d2 : dist x (a + ((j + 1 : ℕ) : ℝ) * h) < δ := by
        rw [hcast, Real.dist_eq, abs_lt]; constructor <;> linarith [hx.1, hx.2]
      have e1 := hδ d1
      have e2 := hδ d2
      simp only [Set.mem_ofPred_eq] at e1 e2
      have f1 : |φ x - φ z| < ε' := by rw [← Real.dist_eq]; exact e1 hxK
      have f2 : |φ x - φ (a + ((j + 1 : ℕ) : ℝ) * h)| < ε' := by
        rw [← Real.dist_eq]; exact e2 hxK
      have f1' := abs_lt.1 f1
      have f2' := abs_lt.1 f2
      show |φ z - φ (a + ((j + 1 : ℕ) : ℝ) * h)| ≤ 2 * ε'
      rw [abs_le]; constructor <;> linarith [f1'.1, f1'.2, f2'.1, f2'.2]
    · have g1 := abs_le.1 (hC z hzab)
      have g2 := abs_le.1 (hC _ heab)
      rw [abs_le]; constructor <;> linarith [g1.1, g1.2, g2.1, g2.2]
  · -- the sum estimate
    set B := (Finset.range N).filter (fun j => ¬ good j) with hB
    have hdisj : (B : Set ℕ).PairwiseDisjoint
        (fun j => Ioc (a + (j : ℝ) * h) (a + ((j + 1 : ℕ) : ℝ) * h)) := by
      intro i _ k _ hik
      rw [Function.onFun, Set.disjoint_left]
      intro z hz1 hz2
      apply hik
      have h1 : (i : ℝ) * h < ((k + 1 : ℕ) : ℝ) * h := by linarith [hz1.1, hz2.2]
      have h2 : (k : ℝ) * h < ((i + 1 : ℕ) : ℝ) * h := by linarith [hz2.1, hz1.2]
      have h1' := lt_of_mul_lt_mul_right h1 hh0.le
      have h2' := lt_of_mul_lt_mul_right h2 hh0.le
      have : i < k + 1 := by exact_mod_cast h1'
      have : k < i + 1 := by exact_mod_cast h2'
      omega
    have hsubU : (⋃ j ∈ B, Ioc (a + (j : ℝ) * h) (a + ((j + 1 : ℕ) : ℝ) * h)) ⊆ U := by
      intro z hz
      simp only [Set.mem_iUnion] at hz
      obtain ⟨j, hjB, hzj⟩ := hz
      rw [hB, Finset.mem_filter, Finset.mem_range] at hjB
      have hzI : z ∈ Icc (a + (j : ℝ) * h) (a + ((j + 1 : ℕ) : ℝ) * h) := ⟨hzj.1.le, hzj.2⟩
      by_contra hzU
      exact hjB.2 ⟨z, ⟨hpiece j hjB.1 z hzI, hzU⟩, hzI⟩
    have hvolB : volume (⋃ j ∈ B, Ioc (a + (j : ℝ) * h) (a + ((j + 1 : ℕ) : ℝ) * h))
        = ENNReal.ofReal ((B.card : ℝ) * h) := by
      rw [measure_biUnion_finset hdisj (fun j _ => measurableSet_Ioc)]
      have : ∀ j ∈ B, volume (Ioc (a + (j : ℝ) * h) (a + ((j + 1 : ℕ) : ℝ) * h))
          = ENNReal.ofReal h := by
        intro j _
        rw [Real.volume_Ioc]; congr 1; push_cast; ring
      rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul,
        ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    have hvolU : volume U ≤ ENNReal.ofReal ((m : ℝ) * (2 * η)) := by
      calc volume U ≤ ∑ d ∈ D, volume (Metric.ball d η) := measure_biUnion_finset_le _ _
        _ = ENNReal.ofReal ((m : ℝ) * (2 * η)) := by
          simp only [Real.volume_ball, Finset.sum_const, nsmul_eq_mul]
          rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    have hBh : (B.card : ℝ) * h ≤ (m : ℝ) * (2 * η) := by
      have := (hvolB ▸ measure_mono hsubU).trans hvolU
      exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 this
    have hsplit : ∑ j ∈ Finset.range N, (if good j then 2 * ε' else 2 * C) * h
        ≤ ∑ j ∈ Finset.range N, (2 * ε' * h + if ¬ good j then 2 * C * h else 0) := by
      refine Finset.sum_le_sum fun j _ => ?_
      by_cases hg : good j
      · simp [hg]
      · simp only [hg, ite_false, not_false_eq_true, ite_true]
        nlinarith
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, ← hB] at hsplit
    have hA : (N : ℝ) * (2 * ε' * h) = ε / 2 := by
      have : (N : ℝ) * (2 * ε' * h) = 2 * ε' * (N * h) := by ring
      rw [this, hNh, hε']; field_simp; ring
    have hηeq : η * (8 * (C + 1) * ((m : ℝ) + 1)) = ε := by rw [hη]; field_simp
    have hCm : C * m ≤ (C + 1) * ((m : ℝ) + 1) := by nlinarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)]
    have hBC : (B.card : ℝ) * (2 * C * h) ≤ ε / 2 := by
      have : (B.card : ℝ) * (2 * C * h) = 2 * C * ((B.card : ℝ) * h) := by ring
      rw [this]
      have h1 : 2 * C * ((B.card : ℝ) * h) ≤ 2 * C * ((m : ℝ) * (2 * η)) :=
        mul_le_mul_of_nonneg_left hBh (by positivity)
      have h2 : 4 * η * (C * m) ≤ 4 * η * ((C + 1) * ((m : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left hCm (by positivity)
      nlinarith
    dsimp only
    linarith

/-! ## 5. One piece -/

lemma piece_bound (φ : ℝ → ℝ) (u v X c w : ℝ) (hu : 0 ≤ u) (huv : u ≤ v) (hX : 0 < X)
    (hosc : ∀ y ∈ Icc u v, |φ y - c| ≤ w) (hint : IntervalIntegrable φ volume u v) :
    |(∑ p ∈ (Finset.Ioc ⌊u * X⌋₊ ⌊v * X⌋₊).filter Nat.Prime,
          φ ((p : ℝ) / X) * Real.log p) / X - ∫ y in u..v, φ y|
      ≤ w * ((Chebyshev.theta (v * X) - Chebyshev.theta (u * X)) / X)
        + |c| * |(Chebyshev.theta (v * X) - Chebyshev.theta (u * X)) / X - (v - u)|
        + w * (v - u) := by
  set P := (Finset.Ioc ⌊u * X⌋₊ ⌊v * X⌋₊).filter Nat.Prime with hP
  have huvX : u * X ≤ v * X := mul_le_mul_of_nonneg_right huv hX.le
  have hT : Chebyshev.theta (v * X) - Chebyshev.theta (u * X) = ∑ p ∈ P, Real.log p :=
    theta_sub _ _ huvX
  rw [hT]
  set Q := ∑ p ∈ P, φ ((p : ℝ) / X) * Real.log p with hQdef
  set T := ∑ p ∈ P, Real.log (p : ℝ) with hTdef
  have hmem : ∀ p ∈ P, (p : ℝ) / X ∈ Icc u v := by
    intro p hp
    rw [hP, Finset.mem_filter, Finset.mem_Ioc] at hp
    obtain ⟨⟨h1, h2⟩, _⟩ := hp
    have h1' : u * X < p := (Nat.floor_lt (by positivity)).1 h1
    have h2' : (p : ℝ) ≤ v * X := (Nat.le_floor_iff (by nlinarith)).1 h2
    constructor
    · rw [le_div_iff₀ hX]; linarith
    · rw [div_le_iff₀ hX]; linarith
  have hQ : |Q - c * T| ≤ w * T := by
    have : Q - c * T = ∑ p ∈ P, (φ ((p : ℝ) / X) - c) * Real.log p := by
      rw [hQdef, hTdef, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun p _ => by ring
    rw [this, Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p hp => ?_)
    rw [abs_mul, abs_of_nonneg (Real.log_natCast_nonneg p)]
    exact mul_le_mul_of_nonneg_right (hosc _ (hmem p hp)) (Real.log_natCast_nonneg p)
  have hI : |(∫ y in u..v, φ y) - c * (v - u)| ≤ w * (v - u) := by
    have : (∫ y in u..v, φ y) - c * (v - u) = ∫ y in u..v, (φ y - c) := by
      rw [intervalIntegral.integral_sub hint intervalIntegrable_const,
        intervalIntegral.integral_const, smul_eq_mul]; ring
    rw [this]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := u) (b := v)
      (f := fun y => φ y - c) (C := w) (fun y hy => by
        rw [Set.uIoc_of_le huv] at hy
        rw [Real.norm_eq_abs]
        exact hosc y ⟨hy.1.le, hy.2⟩)
    rwa [abs_of_nonneg (sub_nonneg.2 huv), Real.norm_eq_abs] at this
  have key : Q / X - ∫ y in u..v, φ y
      = (Q - c * T) / X + c * (T / X - (v - u)) + (c * (v - u) - ∫ y in u..v, φ y) := by
    field_simp; ring
  rw [key]
  have e1 : |(Q - c * T) / X| ≤ w * (T / X) := by
    rw [abs_div, abs_of_pos hX, mul_div_assoc']
    exact div_le_div_of_nonneg_right hQ hX.le
  have e2 : |c * (T / X - (v - u))| = |c| * |T / X - (v - u)| := abs_mul _ _
  have e3 : |c * (v - u) - ∫ y in u..v, φ y| ≤ w * (v - u) := by rw [abs_sub_comm]; exact hI
  have t1 := abs_add_le ((Q - c * T) / X + c * (T / X - (v - u)))
    (c * (v - u) - ∫ y in u..v, φ y)
  have t2 := abs_add_le ((Q - c * T) / X) (c * (T / X - (v - u)))
  linarith

/-! ## 6. The prime Riemann sum -/

open Filter Finset Set in
/-- The prime number theorem in the partial-summation form used by Proposition 5.2 (p. 15). -/
theorem prime_riemann_sum (a b : ℝ) (ha : 0 ≤ a) (hab : a < b) (φ : ℝ → ℝ)
    (hbdd : ∃ C : ℝ, ∀ y ∈ Icc a b, |φ y| ≤ C)
    (hpc : ∃ D : Finset ℝ, ∀ y ∈ Icc a b, y ∉ D → ContinuousAt φ y) :
    Tendsto
      (fun X : ℝ =>
        (∑ p ∈ (Finset.Ioc ⌊a * X⌋₊ ⌊b * X⌋₊).filter Nat.Prime,
            φ ((p : ℝ) / X) * Real.log p) / X)
      atTop (nhds (∫ y in a..b, φ y)) := by
  have hII := intervalIntegrable_of_bdd_pc a b hab.le φ hbdd hpc
  obtain ⟨C, hC⟩ := hbdd
  obtain ⟨D, hD⟩ := hpc
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨N, hN, ω, hω0, hωosc, hωsum⟩ :=
    partition_osc a b hab φ C hC D hD (ε / 4) (by positivity)
  set h : ℝ := (b - a) / N with hh
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hh0 : 0 < h := div_pos (sub_pos.2 hab) hNr
  set y : ℕ → ℝ := fun j => a + (j : ℝ) * h with hy
  have hy_le : ∀ i k : ℕ, i ≤ k → y i ≤ y k := by
    intro i k hik
    simp only [hy]
    have : (i : ℝ) ≤ k := by exact_mod_cast hik
    nlinarith
  have hy0 : y 0 = a := by simp [hy]
  have hyN : y N = b := by simp only [hy, hh]; field_simp; ring
  have hy_nonneg : ∀ j, 0 ≤ y j := fun j => by simp only [hy]; positivity
  have hy_succ : ∀ j, y j ≤ y (j + 1) := fun j => hy_le _ _ (Nat.le_succ j)
  have hypiece : ∀ j, y (j + 1) - y j = h := by intro j; simp only [hy]; push_cast; ring
  have hint_piece : ∀ j < N, IntervalIntegrable φ volume (y j) (y (j + 1)) := by
    intro j hj
    apply hII.mono_set
    rw [Set.uIcc_of_le hab.le, Set.uIcc_of_le (hy_succ j)]
    apply Set.Icc_subset_Icc
    · rw [← hy0]; exact hy_le _ _ (Nat.zero_le _)
    · rw [← hyN]; exact hy_le _ _ hj
  have hIsum : ∫ t in a..b, φ t = ∑ j ∈ range N, ∫ t in (y j)..(y (j + 1)), φ t := by
    rw [intervalIntegral.sum_integral_adjacent_intervals hint_piece, hy0, hyN]
  have hSsum : ∀ X : ℝ, 0 < X →
      ∑ p ∈ (Finset.Ioc ⌊a * X⌋₊ ⌊b * X⌋₊).filter Nat.Prime, φ ((p : ℝ) / X) * Real.log p
        = ∑ j ∈ range N, ∑ p ∈ (Finset.Ioc ⌊y j * X⌋₊ ⌊y (j + 1) * X⌋₊).filter Nat.Prime,
            φ ((p : ℝ) / X) * Real.log p := by
    intro X hX
    simp only [Finset.sum_filter]
    have hmono : Monotone (fun j : ℕ => ⌊y j * X⌋₊) := fun i k hik =>
      Nat.floor_mono (mul_le_mul_of_nonneg_right (hy_le i k hik) hX.le)
    have := sum_Ioc_telescope (fun j => ⌊y j * X⌋₊) hmono
      (fun p => if p.Prime then φ ((p : ℝ) / X) * Real.log p else 0) N
    simp only [hy0, hyN] at this
    exact this
  set L : ℝ := ∑ j ∈ range N, (ω j * (y (j + 1) - y j)
      + |φ (y (j + 1))| * |(y (j + 1) - y j) - (y (j + 1) - y j)|
      + ω j * (y (j + 1) - y j)) with hL
  have hLlt : L < ε := by
    have : L = 2 * ∑ j ∈ range N, ω j * h := by
      rw [hL, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [hypiece]; simp; ring
    rw [this]; linarith
  have hRlim : Tendsto (fun X : ℝ => ∑ j ∈ range N,
      (ω j * ((Chebyshev.theta (y (j + 1) * X) - Chebyshev.theta (y j * X)) / X)
        + |φ (y (j + 1))| *
            |(Chebyshev.theta (y (j + 1) * X) - Chebyshev.theta (y j * X)) / X
              - (y (j + 1) - y j)|
        + ω j * (y (j + 1) - y j))) atTop (nhds L) := by
    apply tendsto_finsetSum
    intro j _
    have hT : Tendsto (fun X : ℝ =>
        (Chebyshev.theta (y (j + 1) * X) - Chebyshev.theta (y j * X)) / X)
        atTop (nhds (y (j + 1) - y j)) := by
      have := (theta_scaled _ (hy_nonneg (j + 1))).sub (theta_scaled _ (hy_nonneg j))
      exact this.congr fun X => by ring
    exact ((hT.const_mul _).add ((hT.sub_const _).abs.const_mul _)).add tendsto_const_nhds
  filter_upwards [hRlim.eventually (gt_mem_nhds hLlt), eventually_gt_atTop 0] with X hR hX
  rw [Real.dist_eq, hSsum X hX, hIsum, Finset.sum_div, ← Finset.sum_sub_distrib]
  refine lt_of_le_of_lt ((Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum fun j hj => ?_)) hR
  exact piece_bound φ (y j) (y (j + 1)) X (φ (y (j + 1))) (ω j) (hy_nonneg j) (hy_succ j) hX
    (fun t ht => hωosc j (mem_range.1 hj) t ht) (hint_piece j (mem_range.1 hj))

end PNT
end Zeta5
