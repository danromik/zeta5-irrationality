/-
Zeta5/Sec6/Energy.lean  —  §6.1 of the paper: the configuration bound (6.6)–(6.9), via the
Cauchy-regularised kernel, from `cauchy_cnd`, `rho_cross`, `rho_energy_ge` and
`eq_6_7_field`.

The regularisation differs from the paper's (circles of radius `ε` around the `t_i`, p. 18):
the points stay Dirac masses and the kernel is regularised,
`kC ε x = ½ log(x² + ε²) ≥ log|x|` (`x ≠ 0`), `kC ε 0 = log ε`.  Zero-mass energy for
`σ − ρ`, `σ = K⁻¹∑δ_{t_i}` (`cauchy_cnd`), then gives

  (6.6')  `h log ε + 2∑_{i<j} log|t_i − t_j| ≤ 2K∑U^ρ(t_i) − K² I(ρ) + 2Kh(88√ε + 420ε)`,

and with (6.7) and `ε = (16K)⁻²`:

  (6.9')  `2∑_{i<j} log|t_i − t_j| − K∑V(t_i) + ∑√t_i ≤ (λM₀ − I(ρ))K² + 2h log K + 20h`,

sharper than the paper's (6.9) (`(120+√2)h` there).
-/
import Zeta5.Sec6.CND
import Zeta5.Sec6.RhoCross
import Zeta5.Sec6.RhoEnergy
import Zeta5.Sec6.Potential
import Zeta5.Sec6.Gram

namespace Zeta5
namespace Sec6

open Real MeasureTheory Set Finset

noncomputable section

/-- A symmetric double sum over `Fin m`: diagonal plus twice the strict upper triangle. -/
theorem sum_sum_symm {m : ℕ} (g : Fin m → Fin m → ℝ) (hg : ∀ i j, g i j = g j i) :
    ∑ i, ∑ j, g i j = ∑ i, g i i + 2 * ∑ i, ∑ j ∈ Ioi i, g i j := by
  have hsplit : ∀ i j, g i j = (if i < j then g i j else 0) + (if i = j then g i j else 0)
      + (if j < i then g i j else 0) := by
    intro i j
    rcases lt_trichotomy i j with hl | he | hl
    · simp [hl, hl.ne, not_lt.2 hl.le]
    · subst he; simp
    · simp [hl, hl.ne', not_lt.2 hl.le]
  have e1 : ∀ i, ∑ j, (if i < j then g i j else 0) = ∑ j ∈ Ioi i, g i j := by
    intro i; rw [← Finset.sum_filter, Finset.filter_lt_eq_Ioi]
  have e2 : ∀ i, ∑ j, (if i = j then g i j else 0) = g i i := by
    intro i; rw [Finset.sum_ite_eq]; simp
  have e3 : ∑ i, ∑ j, (if j < i then g i j else 0) = ∑ i, ∑ j ∈ Ioi i, g i j := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← e1 i]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs
    · exact hg j i
    · rfl
  calc ∑ i, ∑ j, g i j
      = ∑ i, ∑ j, ((if i < j then g i j else 0) + (if i = j then g i j else 0)
          + (if j < i then g i j else 0)) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hsplit i j
    _ = ∑ i, ∑ j ∈ Ioi i, g i j + ∑ i, g i i + ∑ i, ∑ j, (if j < i then g i j else 0) := by
        simp only [Finset.sum_add_distrib, e1, e2]
    _ = _ := by rw [e3]; ring

/-- `I_k(σ,σ) = K⁻² ∑_{i,j} kC ε (t_i − t_j)`. -/
theorem kE_pts_pts {m : ℕ} {K : ℝ} (hK : 0 < K) (ε : ℝ) (t : Fin m → ℝ) :
    kE ε (pts K t) (pts K t) = (∑ i, ∑ j, kC ε (t i - t j)) / K ^ 2 := by
  unfold kE
  simp only [integral_pts hK]
  rw [← Finset.mul_sum]
  field_simp

/-- `I_k(σ,ρ) = K⁻¹ ∑_i ∫ kC ε (t_i − y) dρ(y)`. -/
theorem kE_pts_rho {m : ℕ} {K : ℝ} (hK : 0 < K) (ε : ℝ) (t : Fin m → ℝ) :
    kE ε (pts K t) rhoM = K⁻¹ * ∑ i, ∫ y, kC ε (t i - y) ∂rhoM := by
  unfold kE
  simp only [integral_pts hK]

/-- **(6.6')**, the discrete bound for the Cauchy kernel (distinct points). -/
theorem eq_6_6_cauchy {m : ℕ} {K : ℝ} (hK : 0 < K) (hm : (m : ℝ) = (lam : ℝ) * K)
    (t : Fin m → ℝ) (ht : Function.Injective t) {ε : ℝ} (hε : 0 < ε) :
    m * Real.log ε + 2 * ∑ i, ∑ j ∈ Ioi i, Real.log |t i - t j|
      ≤ 2 * K * ∑ i, Urho (t i) - K ^ 2 * RealBound.Irho
        + 2 * K * m * (88 * Real.sqrt ε + 420 * ε) := by
  set R : ℝ := 2 + ∑ i, |t i| with hRdef
  have hsum0 : 0 ≤ ∑ i, |t i| := Finset.sum_nonneg fun j _ => abs_nonneg (t j)
  have hR : ∀ i, |t i| ≤ R := fun i => by
    have := Finset.single_le_sum (fun j _ => abs_nonneg (t j)) (Finset.mem_univ i)
    linarith
  have hR2 : 2 ≤ R := by linarith
  have hαR := pts_ae K t hR
  have hβR : ∀ᵐ x ∂rhoM, |x| ≤ R := rhoM_ae.mono fun x hx => hx.trans hR2
  have hmass : pts K t univ = rhoM univ := by
    rw [pts_univ, rhoM_univ, hm, mul_div_assoc, div_self hK.ne', mul_one]
  have hcnd := cauchy_cnd (pts K t) rhoM hαR hβR hmass hε
  rw [kE_pts_pts hK, kE_pts_rho hK] at hcnd
  have hrho := rho_energy_ge hε
  set E : ℝ := 88 * Real.sqrt ε + 420 * ε with hE
  set S : ℝ := ∑ i, ∑ j, kC ε (t i - t j) with hSdef
  set X : ℝ := ∑ i, ∫ y, kC ε (t i - y) ∂rhoM with hXdef
  set U : ℝ := ∑ i, Urho (t i) with hUdef
  have hcross : X ≤ U + m * E := by
    calc X ≤ ∑ i, (Urho (t i) + E) := Finset.sum_le_sum fun i _ => by
          have := rho_cross (t i) hε; rw [hE]; linarith
      _ = U + m * E := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
  have hS : m * Real.log ε + 2 * ∑ i, ∑ j ∈ Ioi i, Real.log |t i - t j| ≤ S := by
    rw [hSdef, sum_sum_symm (fun i j => kC ε (t i - t j)) (fun i j => kC_sub_comm ε _ _)]
    simp only [sub_self, kC_zero, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    have : ∑ i, ∑ j ∈ Ioi i, Real.log |t i - t j| ≤ ∑ i, ∑ j ∈ Ioi i, kC ε (t i - t j) :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j hj =>
        log_abs_le_kC (sub_ne_zero.2 (ht.ne (ne_of_lt (Finset.mem_Ioi.1 hj))))
    linarith
  have hK2 : 0 < K ^ 2 := by positivity
  have h1 : S / K ^ 2 ≤ 2 * (K⁻¹ * X) - kE ε rhoM rhoM := by linarith
  have h2 : S ≤ 2 * K * X - K ^ 2 * kE ε rhoM rhoM := by
    have := mul_le_mul_of_nonneg_left h1 hK2.le
    have e1 : K ^ 2 * (S / K ^ 2) = S := by field_simp
    have e2 : K ^ 2 * (2 * (K⁻¹ * X) - kE ε rhoM rhoM)
        = 2 * K * X - K ^ 2 * kE ε rhoM rhoM := by field_simp
    linarith
  have h3 : 2 * K * X ≤ 2 * K * (U + m * E) :=
    mul_le_mul_of_nonneg_left hcross (by positivity)
  have h4 : K ^ 2 * RealBound.Irho ≤ K ^ 2 * kE ε rhoM rhoM :=
    mul_le_mul_of_nonneg_left hrho hK2.le
  nlinarith [hS, h2, h3, h4]

/-- **(6.9')**, log form, distinct points, with `ε = (16K)⁻²` and (6.7). -/
theorem config_log (n : ℕ) (hn : 0 < n) (t : Fin (h n) → ℝ) (ht : ∀ i, 0 < t i)
    (hinj : Function.Injective t) :
    2 * ∑ i, ∑ j ∈ Ioi i, Real.log |t j - t i|
        - (K n : ℝ) * ∑ i, Vfield (t i) + ∑ i, Real.sqrt (t i)
      ≤ ((lam : ℝ) * RealBound.M0 - RealBound.Irho) * (K n : ℝ) ^ 2
        + 2 * (h n : ℝ) * Real.log (K n : ℝ) + 20 * (h n : ℝ) := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hK40 : ((K n : ℕ) : ℝ) = 40 * (n : ℝ) := by simp only [K]; push_cast; ring
  have hh37 : ((h n : ℕ) : ℝ) = 37 * (n : ℝ) := by simp only [h]; push_cast; ring
  set Kr : ℝ := ((K n : ℕ) : ℝ) with hKr
  set m : ℝ := ((h n : ℕ) : ℝ) with hmdef
  have hKpos : 0 < Kr := by rw [hK40]; linarith
  have hK2 : 2 ≤ Kr := by rw [hK40]; linarith
  have hm : m = (lam : ℝ) * Kr := by rw [hh37, hK40]; simp only [lam]; push_cast; ring
  have hmpos : 0 ≤ m := by rw [hh37]; linarith
  set ε : ℝ := ((16 * Kr)⁻¹) ^ 2 with hεdef
  have hε : 0 < ε := by positivity
  have hsq : Real.sqrt ε = (16 * Kr)⁻¹ := Real.sqrt_sq (by positivity)
  have hlogε : Real.log ε = -2 * (4 * Real.log 2 + Real.log Kr) := by
    rw [hεdef, Real.log_pow, Real.log_inv, Real.log_mul (by norm_num) hKpos.ne',
      show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
    push_cast; ring
  have h66 := eq_6_6_cauchy hKpos hm t hinj hε
  rw [hsq, hlogε, ← hmdef] at h66
  -- (6.7), summed over the configuration and multiplied by `K`
  have h67s : ∑ i, (2 * Urho (t i) - Vfield (t i) + Real.sqrt (t i) / Kr)
      ≤ ∑ _i : Fin (h n), (RealBound.M0 + Real.sqrt 2 / Kr) :=
    Finset.sum_le_sum fun i _ => eq_6_7_field Kr hK2 (t i) (ht i)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← hmdef] at h67s
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.sum_div] at h67s
  have h67K : 2 * Kr * ∑ i, Urho (t i) - Kr * ∑ i, Vfield (t i) + ∑ i, Real.sqrt (t i)
      ≤ m * Kr * RealBound.M0 + m * Real.sqrt 2 := by
    have := mul_le_mul_of_nonneg_left h67s hKpos.le
    have e : Kr * (2 * ∑ i, Urho (t i) - ∑ i, Vfield (t i) + (∑ i, Real.sqrt (t i)) / Kr)
        = 2 * Kr * ∑ i, Urho (t i) - Kr * ∑ i, Vfield (t i) + ∑ i, Real.sqrt (t i) := by
      field_simp
    have e' : Kr * (m * (RealBound.M0 + Real.sqrt 2 / Kr))
        = m * Kr * RealBound.M0 + m * Real.sqrt 2 := by
      field_simp
    linarith
  have habs : ∑ i, ∑ j ∈ Ioi i, Real.log |t j - t i|
      = ∑ i, ∑ j ∈ Ioi i, Real.log |t i - t j| := by
    simp_rw [abs_sub_comm]
  rw [habs]
  -- the error term `2Km(88/(16K) + 420/(16K)²) = 11m + (105/32)m/K ≤ 12m`
  have hE : 2 * Kr * m * (88 * (16 * Kr)⁻¹ + 420 * ε) ≤ 12 * m := by
    have e : 2 * Kr * m * (88 * (16 * Kr)⁻¹ + 420 * ε) = 11 * m + 105 / 32 * m / Kr := by
      rw [hεdef]; field_simp; ring
    rw [e]
    have : 105 / 32 * m / Kr ≤ m := by
      rw [div_le_iff₀ hKpos]; nlinarith
    linarith
  -- numerics: `log 2 < 0.6931471808`, `√2 < 1.415`
  have hl2 : m * Real.log 2 ≤ m * 0.6931471808 :=
    mul_le_mul_of_nonneg_left Real.log_two_lt_d9.le hmpos
  have hs2' : Real.sqrt 2 < 1.415 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hs2 : m * Real.sqrt 2 ≤ m * 1.415 := mul_le_mul_of_nonneg_left hs2'.le hmpos
  have hlam : m * Kr * RealBound.M0 = (lam : ℝ) * RealBound.M0 * Kr ^ 2 := by rw [hm]; ring
  nlinarith [h66, h67K, hE, hl2, hs2, hlam]

/-- **The configuration bound** (the paper's (6.9), with the sharper constant `20h`). -/
theorem configBound (n : ℕ) (hn : 0 < n) :
    ConfigBound n (((lam : ℝ) * RealBound.M0 - RealBound.Irho) * (K n : ℝ) ^ 2
      + 2 * (h n : ℝ) * Real.log (K n : ℝ) + 20 * (h n : ℝ)) :=
  Gram.configBound_of_log n _ fun t ht hinj => config_log n hn t ht hinj

end

end Sec6
end Zeta5
