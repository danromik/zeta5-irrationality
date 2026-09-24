/-
Zeta5/Sec6/Gram.lean  —  §6.2 of the paper: (6.10)–(6.13) and the bookkeeping of (6.14),
from a configuration bound.  THIS FILE CONTAINS NO `sorry`.

Everything is stated in the ORIGINAL variable `y` (no `h`-fold change of variables); the
paper's `t = (y/K)²` appears only as an argument of `Vfield` and of the configuration bound
`ConfigBound` (`Sec6/Defs.lean`).

* **(6.10)** Andréief's identity (`andreief`, `eq_6_10`), via the double permutation sum
  `m!·det M = ∑_σ∑_τ sgn σ sgn τ ∏_k M_{σk,τk}` (no symmetrisation needed), applied to the
  moment matrix through `Positivity.prop_2_2_moment` (Proposition 2.2).
* **(6.12)** both halves (`eq_6_12_lower`, `eq_6_12_upper`) by sum–integral comparison for the
  increasing function `s ↦ log(t + (s/K)²)`; the upper half avoids the paper's "decreasing in
  `t`, then evaluate at `t = 0`" and gives `≤ 2 log m + 2`.
* **(6.11) + (6.12)** give the one-point bound `fW_le`; **(6.13)** is `integrand_le` and
  `gram_bound`, with `∫_0^∞ (1+y)⁵e^{-y/K} dy ≤ 326K⁶` (`integral_g_le`) in place of the
  paper's `652 = ∫_0^∞ t^{-1/2}(1+√t)⁵e^{-√t}dt` (the paper's `4096·652` is our `8192·326`).
* **(6.14)** from any configuration bound `A ≤ (λM₀−I(ρ))K² + 3h log K + 131h`
  (`eq_6_14_of_config`), using the factor `1/h!` of (6.10) (`log h! ≥ h log h − h + 1`), which
  the paper drops; the paper's own (6.9) constants are admissible (`paper_6_9_admissible`).
-/
import Zeta5.Positivity
import Zeta5.Sec6.Defs

namespace Zeta5
namespace Sec6
namespace Gram

open Real Finset MeasureTheory Set Polynomial
open scoped Matrix

noncomputable section

/-! ## 0. The one-variable data -/

-- `fW`, `Vfield` and `ConfigBound` are defined in `Zeta5/Sec6/Defs.lean`.

/-- Log form ⇒ product form (for the energy side, which naturally proves the log form
for pairwise distinct points). -/
theorem configBound_of_log (n : ℕ) (A : ℝ)
    (hlog : ∀ t : Fin (h n) → ℝ, (∀ i, 0 < t i) → Function.Injective t →
      2 * ∑ i, ∑ j ∈ Ioi i, Real.log |t j - t i|
        - (K n : ℝ) * ∑ i, Vfield (t i) + ∑ i, Real.sqrt (t i) ≤ A) :
    ConfigBound n A := by
  intro t ht
  by_cases hinj : Function.Injective t
  · have hl := hlog t ht hinj
    have hsq : (∏ i, ∏ j ∈ Ioi i, (t j - t i)) ^ 2
        = Real.exp (2 * ∑ i, ∑ j ∈ Ioi i, Real.log |t j - t i|) := by
      rw [Finset.mul_sum, Real.exp_sum, ← Finset.prod_pow]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [Finset.mul_sum, Real.exp_sum, ← Finset.prod_pow]
      refine Finset.prod_congr rfl fun j hj => ?_
      have hne : t j - t i ≠ 0 :=
        sub_ne_zero.2 (hinj.ne (ne_of_gt (Finset.mem_Ioi.1 hj)))
      rw [show 2 * Real.log |t j - t i| = Real.log |t j - t i| + Real.log |t j - t i| by ring,
        Real.exp_add, Real.exp_log (abs_pos.2 hne), ← sq, sq_abs]
    rw [hsq, ← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith)
  · have : ∃ a b, t a = t b ∧ a ≠ b := by
      unfold Function.Injective at hinj; push Not at hinj; exact hinj
    obtain ⟨a, b, hab, hne⟩ := this
    have hz : (∏ i, ∏ j ∈ Ioi i, (t j - t i)) = 0 := by
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · exact Finset.prod_eq_zero (Finset.mem_univ a)
          (Finset.prod_eq_zero (Finset.mem_Ioi.2 hlt) (by rw [hab, sub_self]))
      · exact Finset.prod_eq_zero (Finset.mem_univ b)
          (Finset.prod_eq_zero (Finset.mem_Ioi.2 hlt) (by rw [hab, sub_self]))
    rw [hz]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul]
    exact (Real.exp_pos _).le

/-! ## 1. (6.10): Andréief / Heine -/

/-- Pure algebra: `m!·det M = ∑_σ ∑_τ sgn σ sgn τ ∏_k M_{σk,τk}`. -/
theorem factorial_mul_det {m : ℕ} (M : Matrix (Fin m) (Fin m) ℝ) :
    (m.factorial : ℝ) * M.det
      = ∑ σ : Equiv.Perm (Fin m), ∑ τ : Equiv.Perm (Fin m),
          ((Equiv.Perm.sign σ : ℤ) : ℝ) * ((Equiv.Perm.sign τ : ℤ) : ℝ)
            * ∏ k, M (σ k) (τ k) := by
  rw [Finset.sum_comm]
  have key : ∀ τ : Equiv.Perm (Fin m),
      ∑ σ : Equiv.Perm (Fin m), ((Equiv.Perm.sign σ : ℤ) : ℝ) * ((Equiv.Perm.sign τ : ℤ) : ℝ)
          * ∏ k, M (σ k) (τ k) = M.det := by
    intro τ
    have h1 := Matrix.det_permute' τ M
    rw [Matrix.det_apply'] at h1
    simp only [Matrix.submatrix_apply, id] at h1
    have hs : ((Equiv.Perm.sign τ : ℤ) : ℝ) * ((Equiv.Perm.sign τ : ℤ) : ℝ) = 1 := by
      rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]; simp
    calc _ = ((Equiv.Perm.sign τ : ℤ) : ℝ) *
          ∑ σ : Equiv.Perm (Fin m), ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ k, M (σ k) (τ k) := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun σ _ => by ring
      _ = M.det := by rw [h1, ← mul_assoc, hs, one_mul]
  simp_rw [key]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]

/-- **Andréief's identity**, weighted form, for any σ-finite measure. -/
theorem andreief {α : Type*} [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ]
    {m : ℕ} (φ : Fin m → α → ℝ) (w : α → ℝ)
    (hint : ∀ i j, Integrable (fun x => φ i x * φ j x * w x) μ) :
    (m.factorial : ℝ) * (Matrix.of fun i j => ∫ x, φ i x * φ j x * w x ∂μ).det
      = ∫ x : Fin m → α,
          (Matrix.of fun i k => φ i (x k)).det ^ 2 * ∏ k, w (x k)
          ∂(Measure.pi fun _ => μ) := by
  rw [factorial_mul_det]
  simp only [Matrix.of_apply]
  -- product of integrals = integral of product
  have hprod : ∀ σ τ : Equiv.Perm (Fin m),
      ∏ k, ∫ x, φ (σ k) x * φ (τ k) x * w x ∂μ
        = ∫ x : Fin m → α, ∏ k, (φ (σ k) (x k) * φ (τ k) (x k) * w (x k))
            ∂(Measure.pi fun _ => μ) :=
    fun σ τ => (integral_fintype_prod_eq_prod
      (f := fun k (x : α) => φ (σ k) x * φ (τ k) x * w x)).symm
  have hI : ∀ σ τ : Equiv.Perm (Fin m), Integrable
      (fun x : Fin m → α => ∏ k, (φ (σ k) (x k) * φ (τ k) (x k) * w (x k)))
      (Measure.pi fun _ => μ) :=
    fun σ τ => Integrable.fintype_prod (f := fun k (x : α) => φ (σ k) x * φ (τ k) x * w x)
      (fun k => hint (σ k) (τ k))
  simp_rw [hprod, ← integral_const_mul]
  have hinner : ∀ σ : Equiv.Perm (Fin m),
      ∑ τ : Equiv.Perm (Fin m), ∫ x : Fin m → α,
          ((Equiv.Perm.sign σ : ℤ) : ℝ) * ((Equiv.Perm.sign τ : ℤ) : ℝ)
            * ∏ k, (φ (σ k) (x k) * φ (τ k) (x k) * w (x k)) ∂(Measure.pi fun _ => μ)
        = ∫ x : Fin m → α, ∑ τ : Equiv.Perm (Fin m),
          ((Equiv.Perm.sign σ : ℤ) : ℝ) * ((Equiv.Perm.sign τ : ℤ) : ℝ)
            * ∏ k, (φ (σ k) (x k) * φ (τ k) (x k) * w (x k)) ∂(Measure.pi fun _ => μ) :=
    fun σ => (integral_finsetSum _ (fun τ _ => (hI σ τ).const_mul _)).symm
  rw [Finset.sum_congr rfl (fun σ _ => hinner σ)]
  rw [← integral_finsetSum _ (fun σ _ => integrable_finsetSum _
      (fun τ _ => (hI σ τ).const_mul _))]
  congr 1
  funext x
  rw [Matrix.det_apply', sq, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp only [Matrix.of_apply, Finset.prod_mul_distrib]
  ring

/-- Entries of `G_K(ζ(5))` as integrals (from `Positivity.prop_2_2_moment`). -/
theorem evalZeta5_G (n : ℕ) (i j : Fin (h n)) :
    evalZeta5 (G n i j)
      = ∫ y in Ioi (0 : ℝ), (y ^ 2) ^ (i : ℕ) * (y ^ 2) ^ (j : ℕ) * fW n y := by
  rw [G, Positivity.prop_2_2_moment]
  refine setIntegral_congr_fun measurableSet_Ioi (fun y _ => ?_)
  simp only [Positivity.aeval_entryNum, fW, pow_add]
  ring

theorem integrableOn_G_entry (n : ℕ) (i j : ℕ) :
    IntegrableOn (fun y : ℝ => (y ^ 2) ^ i * (y ^ 2) ^ j * fW n y) (Ioi 0) := by
  refine (Positivity.integrableOn_moment n (entryNum n i j)).congr_fun (fun y _ => ?_)
    measurableSet_Ioi
  simp only [Positivity.aeval_entryNum, fW, pow_add]
  ring

/-- **(6.10)** in the variable `y`. -/
theorem eq_6_10 (n : ℕ) :
    ((h n).factorial : ℝ) * evalZeta5 (Delta n)
      = ∫ y : Fin (h n) → ℝ,
          (∏ i, ∏ j ∈ Ioi i, (y j ^ 2 - y i ^ 2)) ^ 2 * ∏ k, fW n (y k)
          ∂(Measure.pi fun _ => volume.restrict (Ioi (0 : ℝ))) := by
  have hdet : evalZeta5 (Delta n) = ((G n).map evalZeta5).det := by
    simp only [Delta, evalZeta5]
    exact RingHom.map_det _ _
  have hM : (G n).map evalZeta5 = Matrix.of fun (i j : Fin (h n)) =>
      ∫ y, (y ^ 2) ^ (i : ℕ) * (y ^ 2) ^ (j : ℕ) * fW n y ∂(volume.restrict (Ioi (0 : ℝ))) := by
    ext i j
    simp only [Matrix.map_apply, Matrix.of_apply]
    exact evalZeta5_G n i j
  rw [hdet, hM, andreief (volume.restrict (Ioi (0 : ℝ)))
    (fun i y => (y ^ 2) ^ (i : ℕ)) (fW n) (fun i j => integrableOn_G_entry n i j)]
  congr 1
  funext y
  congr 2
  have : (Matrix.of fun (i k : Fin (h n)) => (y k ^ 2) ^ (i : ℕ))
      = (Matrix.vandermonde (fun k => y k ^ 2)).transpose := by
    ext i k; simp [Matrix.vandermonde_apply]
  rw [this, Matrix.det_transpose, Matrix.det_vandermonde]

/-! ## 2. (6.12) and the one-point bound -/

/-- `L(t,a) := ∫_0^a log(t+u²) du`. -/
abbrev Lint (t a : ℝ) : ℝ := ∫ u in (0 : ℝ)..a, Real.log (t + u ^ 2)

/-- `∑_{j=1}^m f j = ∑_{i<m} f (i+1)`. -/
theorem sum_Icc_one_eq_range (m : ℕ) (f : ℕ → ℝ) :
    ∑ j ∈ Finset.Icc 1 m, f j = ∑ i ∈ range m, f (i + 1) := by
  induction m with
  | zero => simp
  | succ k ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

/-- `K·∫_0^{m/K} log(t+u²)du = ∫_0^m log(t+(s/K)²)ds`. -/
theorem K_mul_Lint (Kn m : ℕ) (hK : 0 < Kn) (t : ℝ) :
    (Kn : ℝ) * Lint t ((m : ℝ) / Kn) = ∫ s in (0 : ℝ)..(m : ℝ), Real.log (t + (s / Kn) ^ 2) := by
  have hc : (Kn : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
  rw [intervalIntegral.integral_comp_div (fun u => Real.log (t + u ^ 2)) hc]
  simp [Lint, smul_eq_mul]

theorem G_monoOn {t : ℝ} (ht : 0 < t) {Kn : ℝ} (hK : 0 < Kn) :
    MonotoneOn (fun s : ℝ => Real.log (t + (s / Kn) ^ 2)) (Ici 0) := by
  intro a ha b hb hab
  have ha' : (0 : ℝ) ≤ a := ha
  have h1 : a / Kn ≤ b / Kn := div_le_div_of_nonneg_right hab hK.le
  have h0 : 0 ≤ a / Kn := div_nonneg ha' hK.le
  exact Real.log_le_log (by positivity) (by nlinarith)

theorem G_continuous {t : ℝ} (ht : 0 < t) (Kn : ℝ) :
    Continuous (fun s : ℝ => Real.log (t + (s / Kn) ^ 2)) :=
  (continuous_const.add ((continuous_id.div_const _).pow 2)).log
    (fun s => by have := sq_nonneg (s / Kn); exact (by positivity : t + (s / Kn) ^ 2 ≠ 0))

/-- **(6.12)**, lower half (right-endpoint Riemann sum of an increasing function). -/
theorem eq_6_12_lower (Kn m : ℕ) (hK : 0 < Kn) {t : ℝ} (ht : 0 < t) :
    (Kn : ℝ) * Lint t ((m : ℝ) / Kn)
      ≤ ∑ j ∈ Icc 1 m, Real.log (t + ((j : ℝ) / Kn) ^ 2) := by
  have hKR : (0 : ℝ) < Kn := by exact_mod_cast hK
  rw [K_mul_Lint Kn m hK t, sum_Icc_one_eq_range]
  have hmono := (G_monoOn ht hKR).mono (fun x (hx : x ∈ Icc (0 : ℝ) (0 + m)) => hx.1)
  have := MonotoneOn.integral_le_sum hmono
  simpa using this

/-- **(6.12)**, upper half: `∑_{j≤m} log(t+(j/K)²) − K∫_0^{m/K} ≤ 2 log m + 2 ≤ 2 log K + 2`. -/
theorem eq_6_12_upper (Kn m : ℕ) (hm : 1 ≤ m) (hmK : m ≤ Kn) {t : ℝ} (ht : 0 < t) :
    ∑ j ∈ Icc 1 m, Real.log (t + ((j : ℝ) / Kn) ^ 2) - (Kn : ℝ) * Lint t ((m : ℝ) / Kn)
      ≤ 2 * Real.log Kn + 2 := by
  have hK : 0 < Kn := by omega
  have hKR : (0 : ℝ) < Kn := by exact_mod_cast hK
  set G : ℝ → ℝ := fun s => Real.log (t + (s / Kn) ^ 2) with hGdef
  have hGc : Continuous G := G_continuous ht _
  rw [K_mul_Lint Kn m hK t, sum_Icc_one_eq_range]
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [Finset.sum_range_succ]
  -- the middle terms: ∑_{i<m'} G(1+i) ≤ ∫_1^{1+m'} G
  have hmono := (G_monoOn ht hKR).mono
    (fun x (hx : x ∈ Icc (1 : ℝ) (1 + m')) => (show (0:ℝ) ≤ x by linarith [hx.1]))
  have hmid := MonotoneOn.sum_le_integral hmono
  -- split ∫_0^{m'+1} = ∫_0^1 + ∫_1^{m'+1}
  have hsplit : ∫ s in (0 : ℝ)..((m' + 1 : ℕ) : ℝ), G s
      = (∫ s in (0 : ℝ)..1, G s) + ∫ s in (1 : ℝ)..(1 + (m' : ℝ)), G s := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hGc.intervalIntegrable _ _)
      (hGc.intervalIntegrable _ _)]
    push_cast; ring_nf
  -- ∫_0^1 G ≥ G 1 - 2
  have hfirst : G 1 - 2 ≤ ∫ s in (0 : ℝ)..1, G s := by
    have hint : IntervalIntegrable (fun s : ℝ => G 1 + 2 * Real.log s) volume 0 1 :=
      intervalIntegrable_const.add (intervalIntegral.intervalIntegrable_log'.const_mul 2)
    have hval : ∫ s in (0 : ℝ)..1, (G 1 + 2 * Real.log s) = G 1 - 2 := by
      rw [intervalIntegral.integral_add intervalIntegrable_const
        (intervalIntegral.intervalIntegrable_log'.const_mul 2),
        intervalIntegral.integral_const, intervalIntegral.integral_const_mul, integral_log]
      simp; ring
    rw [← hval, intervalIntegral.integral_of_le zero_le_one,
      intervalIntegral.integral_of_le zero_le_one]
    refine setIntegral_mono_on hint.1 (hGc.intervalIntegrable 0 1).1 measurableSet_Ioc ?_
    intro s hs
    obtain ⟨hs0, hs1⟩ := hs
    have hlog : 2 * Real.log s = Real.log (s ^ 2) := by rw [Real.log_pow]; norm_num
    simp only [hGdef]
    rw [hlog, ← Real.log_mul (by positivity) (by positivity)]
    apply Real.log_le_log (by positivity)
    have hs2 : s ^ 2 ≤ 1 := by nlinarith
    have : (s / Kn) ^ 2 = s ^ 2 * (1 / Kn) ^ 2 := by ring
    rw [this]
    nlinarith [sq_nonneg (1 / (Kn : ℝ))]
  -- G(m'+1) - G(1) ≤ 2 log (m'+1) ≤ 2 log K
  have hM1 : (1 : ℝ) ≤ (m' : ℝ) + 1 := by have := (Nat.cast_nonneg m' : (0:ℝ) ≤ m'); linarith
  have hlast : G ((m' : ℝ) + 1) ≤ G 1 + 2 * Real.log Kn := by
    have hMK : (m' : ℝ) + 1 ≤ Kn := by exact_mod_cast hmK
    have h2 : 2 * Real.log ((m' : ℝ) + 1) ≤ 2 * Real.log Kn := by
      have := Real.log_le_log (by linarith) hMK; linarith
    have h3 : G ((m' : ℝ) + 1) ≤ G 1 + 2 * Real.log ((m' : ℝ) + 1) := by
      simp only [hGdef]
      rw [show 2 * Real.log ((m' : ℝ) + 1) = Real.log (((m' : ℝ) + 1) ^ 2) by
        rw [Real.log_pow]; norm_num, ← Real.log_mul (by positivity) (by positivity)]
      apply Real.log_le_log (by positivity)
      have : (((m' : ℝ) + 1) / Kn) ^ 2 = ((m' : ℝ) + 1) ^ 2 * (1 / Kn) ^ 2 := by ring
      rw [this]
      have hM2 : (1 : ℝ) ≤ ((m' : ℝ) + 1) ^ 2 := by nlinarith
      nlinarith [sq_nonneg (1 / (Kn : ℝ))]
    linarith
  rw [hsplit]
  have hmid' : ∑ i ∈ range m', G ((i + 1 : ℕ) : ℝ) ≤ ∫ s in (1 : ℝ)..(1 + (m' : ℝ)), G s := by
    refine le_trans (le_of_eq ?_) hmid
    exact Finset.sum_congr rfl fun i _ => by
      simp only [hGdef]; push_cast; ring_nf
  have hlast' : G (((m' + 1 : ℕ) : ℝ)) ≤ G 1 + 2 * Real.log Kn := by push_cast; exact hlast
  simp only [hGdef] at hmid' hlast' hfirst ⊢
  linarith

/-- `log D_m(y²) = 2m log K + ∑_{j≤m} log((y/K)² + (j/K)²)`. -/
theorem log_aeval_D (m Kn : ℕ) (hK : 0 < Kn) (y : ℝ) :
    Real.log (aeval (y ^ 2 : ℝ) (D m))
      = 2 * (m : ℝ) * Real.log Kn
        + ∑ j ∈ Icc 1 m, Real.log ((y / Kn) ^ 2 + ((j : ℝ) / Kn) ^ 2) := by
  have hKR : (0 : ℝ) < Kn := by exact_mod_cast hK
  rw [D, map_prod]
  simp_rw [Positivity.aeval_X_add_C_sq]
  have hj : ∀ j ∈ Finset.Icc 1 m, y ^ 2 + (j : ℝ) ^ 2
      = (Kn : ℝ) ^ 2 * ((y / Kn) ^ 2 + ((j : ℝ) / Kn) ^ 2) := fun j _ => by
    field_simp
  have hpos : ∀ j ∈ Finset.Icc 1 m, (0 : ℝ) < (y / Kn) ^ 2 + ((j : ℝ) / Kn) ^ 2 := fun j hj => by
    have : (1 : ℝ) ≤ j := by exact_mod_cast (Finset.mem_Icc.1 hj).1
    positivity
  rw [Finset.prod_congr rfl hj, Real.log_prod (fun j hj' => by
      have := hpos j hj'; positivity)]
  rw [Finset.sum_congr rfl (fun j hj' => Real.log_mul (by positivity) (hpos j hj').ne'),
    Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc, Real.log_pow]
  simp only [nsmul_eq_mul, Nat.add_sub_cancel]
  push_cast
  ring

/-- One-point bound, from (6.11) + (6.12):
`fW(y) ≤ 8192 e¹² K^{12N−2K+12} (1+y)⁵ e^{−K V((y/K)²)}`, exponent kept real. -/
theorem fW_le (n : ℕ) (hn : 0 < n) {y : ℝ} (hy : 0 < y) :
    fW n y ≤ Real.exp (Real.log 8192 + 12
        + (12 * (N n : ℝ) - 2 * (K n : ℝ) + 12) * Real.log (K n : ℝ)
        - (K n : ℝ) * Vfield ((y / (K n : ℝ)) ^ 2)) * (1 + y) ^ 5 := by
  have hKn : 0 < K n := by simp only [K]; omega
  have hKR : (0 : ℝ) < (K n : ℝ) := by exact_mod_cast hKn
  have hN1 : 1 ≤ N n := by simp only [N]; omega
  have hNK : N n ≤ K n := by simp only [N, K]; omega
  set t : ℝ := (y / (K n : ℝ)) ^ 2 with htdef
  have ht : 0 < t := by positivity
  have hDN := Positivity.aeval_D_pos (N n) y
  have hDK := Positivity.aeval_D_pos (K n) y
  have hDt := Positivity.aeval_Dtail_pos n y
  -- D_N⁵/D_tail = D_N⁶/D_K
  have hDKeq : aeval (y ^ 2 : ℝ) (D (K n)) = aeval (y ^ 2 : ℝ) (D (N n)) * aeval (y ^ 2 : ℝ) (Dtail n) := by
    rw [← D_mul_Dtail, map_mul]
  set R : ℝ := aeval (y ^ 2 : ℝ) (D (N n)) ^ 6 / aeval (y ^ 2 : ℝ) (D (K n)) with hR
  have hRpos : 0 < R := by positivity
  have hfW : fW n y = R * wt y := by
    simp only [fW, hR, hDKeq]
    field_simp
  -- log R
  have hlogR : Real.log R = 6 * Real.log (aeval (y ^ 2 : ℝ) (D (N n)))
      - Real.log (aeval (y ^ 2 : ℝ) (D (K n))) := by
    rw [hR, Real.log_div (by positivity) hDK.ne', Real.log_pow]; push_cast; ring
  rw [log_aeval_D (N n) (K n) hKn y, log_aeval_D (K n) (K n) hKn y] at hlogR
  have hup := eq_6_12_upper (K n) (N n) hN1 hNK ht
  have hlo := eq_6_12_lower (K n) (K n) hKn ht
  have hNK' : ((N n : ℕ) : ℝ) / (K n : ℝ) = (alpha : ℝ) := by
    simp only [N, K, alpha]; push_cast; field_simp
  have hKK : ((K n : ℕ) : ℝ) / (K n : ℝ) = 1 := div_self hKR.ne'
  rw [hNK'] at hup
  rw [hKK] at hlo
  have hsq : Real.sqrt t = y / (K n : ℝ) := by
    rw [htdef, Real.sqrt_sq (by positivity)]
  have hKy : (K n : ℝ) * Real.sqrt t = y := by rw [hsq]; field_simp
  have hV : (K n : ℝ) * Vfield t = 2 * π * y + (K n : ℝ) * Lint t 1
      - 6 * ((K n : ℝ) * Lint t (alpha : ℝ)) := by
    simp only [Vfield, Lint]; rw [← hKy]; ring
  have hLR : Real.log R ≤ 12 + (12 * (N n : ℝ) - 2 * (K n : ℝ) + 12) * Real.log (K n : ℝ)
      - (K n : ℝ) * Vfield t + 2 * π * y := by
    rw [hlogR, hV]; linarith
  have hw := RealBound.eq_6_11 y hy
  have hexpR : R = Real.exp (Real.log R) := (Real.exp_log hRpos).symm
  have h8192 : (8192 : ℝ) = Real.exp (Real.log 8192) := (Real.exp_log (by norm_num)).symm
  calc fW n y = R * wt y := hfW
    _ ≤ R * (8192 * (1 + y) ^ 5 * Real.exp (-(2 * π * y))) :=
        mul_le_mul_of_nonneg_left hw hRpos.le
    _ = Real.exp (Real.log 8192 + (Real.log R - 2 * π * y)) * (1 + y) ^ 5 := by
        rw [Real.exp_add, Real.exp_sub, ← hexpR, ← h8192, Real.exp_neg]; field_simp
    _ ≤ _ := by
        gcongr
        linarith

theorem fW_nonneg (n : ℕ) {y : ℝ} (hy : 0 < y) : 0 ≤ fW n y := by
  unfold fW
  exact mul_nonneg (div_nonneg (pow_nonneg (Positivity.aeval_D_pos _ _).le _)
    (Positivity.aeval_Dtail_pos _ _).le) (Positivity.wt_nonneg hy.le)

/-! ## 3. The h-point bound and integration -/

/-- `∏_{i<j} c = c^{h(h−1)/2}`, in the form used: `∏_{i<j}(K²(t_j−t_i)) = K^{h(h−1)}∏(t_j−t_i)`. -/
theorem prod_pairs_scale {m : ℕ} (c : ℝ) (t : Fin m → ℝ) :
    (∏ i, ∏ j ∈ Ioi i, (c * (t j - t i))) ^ 2
      = c ^ (m * (m - 1)) * (∏ i, ∏ j ∈ Ioi i, (t j - t i)) ^ 2 := by
  have hi : ∀ i : Fin m, ∏ j ∈ Ioi i, (c * (t j - t i))
      = c ^ (#(Ioi i)) * ∏ j ∈ Ioi i, (t j - t i) := fun i => by
    rw [prod_mul_distrib, prod_const]
  simp_rw [hi]
  rw [prod_mul_distrib, prod_pow_eq_pow_sum, mul_pow, ← pow_mul]
  congr 2
  simp_rw [Fin.card_Ioi]
  rw [Fin.sum_univ_eq_sum_range (fun i => m - 1 - i) m, Finset.sum_range_reflect (fun i => i) m,
    Finset.sum_range_id_mul_two]

/-- Pointwise bound for the (6.10) integrand, given a configuration bound. -/
theorem integrand_le (n : ℕ) (hn : 0 < n) (A : ℝ) (hA : ConfigBound n A)
    (y : Fin (h n) → ℝ) (hy : ∀ k, 0 < y k) :
    (∏ i, ∏ j ∈ Ioi i, (y j ^ 2 - y i ^ 2)) ^ 2 * ∏ k, fW n (y k)
      ≤ Real.exp ((h n : ℝ) * (Real.log 8192 + 12)
          + (2 * (h n : ℝ) * ((h n : ℝ) - 1)
              + (h n : ℝ) * (12 * (N n : ℝ) - 2 * (K n : ℝ) + 12)) * Real.log (K n : ℝ)
          + A)
        * ∏ k, ((1 + y k) ^ 5 * Real.exp (-(y k / (K n : ℝ)))) := by
  have hKn : 0 < K n := by simp only [K]; omega
  have hKR : (0 : ℝ) < (K n : ℝ) := by exact_mod_cast hKn
  have hh1 : 1 ≤ h n := by simp only [h]; omega
  set Kr : ℝ := (K n : ℝ) with hKr
  set t : Fin (h n) → ℝ := fun k => (y k / Kr) ^ 2 with htdef
  have ht : ∀ k, 0 < t k := fun k => by have := hy k; positivity
  have hsq : ∀ k, Real.sqrt (t k) = y k / Kr := fun k => by
    rw [htdef]; exact Real.sqrt_sq (by have := hy k; positivity)
  set c0 : ℝ := Real.log 8192 + 12 + (12 * (N n : ℝ) - 2 * Kr + 12) * Real.log Kr with hc0
  -- Vandermonde scaling
  have hdiff : ∀ i j : Fin (h n), y j ^ 2 - y i ^ 2 = Kr ^ 2 * (t j - t i) := fun i j => by
    simp only [htdef]; field_simp
  have hVan : (∏ i, ∏ j ∈ Ioi i, (y j ^ 2 - y i ^ 2)) ^ 2
      = (Kr ^ 2) ^ (h n * (h n - 1)) * (∏ i, ∏ j ∈ Ioi i, (t j - t i)) ^ 2 := by
    simp_rw [hdiff]; exact prod_pairs_scale _ _
  have hpow : (Kr ^ 2) ^ (h n * (h n - 1))
      = Real.exp (2 * (h n : ℝ) * ((h n : ℝ) - 1) * Real.log Kr) := by
    rw [← Real.exp_log (by positivity : (0:ℝ) < (Kr ^ 2) ^ (h n * (h n - 1))),
      Real.log_pow, Real.log_pow]
    congr 1
    rw [Nat.cast_mul, Nat.cast_sub hh1]; push_cast; ring
  -- one-point bounds
  have hf : ∏ k, fW n (y k) ≤ ∏ k, (Real.exp (c0 - Kr * Vfield (t k)) * (1 + y k) ^ 5) :=
    Finset.prod_le_prod₀ (fun k _ => fW_nonneg n (hy k)) (fun k _ => by
      have := fW_le n hn (hy k); simpa [hc0, htdef] using this)
  have hfe : ∏ k, (Real.exp (c0 - Kr * Vfield (t k)) * (1 + y k) ^ 5)
      = Real.exp ((h n : ℝ) * c0 - Kr * ∑ k, Vfield (t k)) * ∏ k, (1 + y k) ^ 5 := by
    rw [Finset.prod_mul_distrib, ← Real.exp_sum, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Finset.mul_sum]
  -- configuration bound
  have hcfg := hA t ht
  have hcfg' : (∏ i, ∏ j ∈ Ioi i, (t j - t i)) ^ 2 * Real.exp (-Kr * ∑ i, Vfield (t i))
      ≤ Real.exp A * Real.exp (-∑ k, y k / Kr) := by
    have e : Real.exp (-Kr * ∑ i, Vfield (t i) + ∑ i, Real.sqrt (t i))
        = Real.exp (-Kr * ∑ i, Vfield (t i)) * Real.exp (∑ k, y k / Kr) := by
      rw [Real.exp_add]; simp_rw [hsq]
    rw [e, ← mul_assoc] at hcfg
    have hpos := Real.exp_pos (∑ k, y k / Kr)
    rw [Real.exp_neg]
    exact (le_mul_inv_iff₀ hpos).2 hcfg
  have hP : 0 ≤ ∏ k, (1 + y k) ^ 5 := Finset.prod_nonneg fun k _ => by
    have := hy k; positivity
  have hsqnn : 0 ≤ (∏ i, ∏ j ∈ Ioi i, (t j - t i)) ^ 2 := sq_nonneg _
  have hRHS : ∏ k, ((1 + y k) ^ 5 * Real.exp (-(y k / Kr)))
      = (∏ k, (1 + y k) ^ 5) * Real.exp (-∑ k, y k / Kr) := by
    rw [Finset.prod_mul_distrib, ← Real.exp_sum, Finset.sum_neg_distrib]
  rw [hVan, hRHS, hpow]
  calc Real.exp (2 * (h n : ℝ) * ((h n : ℝ) - 1) * Real.log Kr)
          * (∏ i, ∏ j ∈ Ioi i, (t j - t i)) ^ 2 * ∏ k, fW n (y k)
      ≤ Real.exp (2 * (h n : ℝ) * ((h n : ℝ) - 1) * Real.log Kr)
          * (∏ i, ∏ j ∈ Ioi i, (t j - t i)) ^ 2
          * (Real.exp ((h n : ℝ) * c0 - Kr * ∑ k, Vfield (t k)) * ∏ k, (1 + y k) ^ 5) := by
        rw [← hfe]; gcongr
    _ = Real.exp (2 * (h n : ℝ) * ((h n : ℝ) - 1) * Real.log Kr + (h n : ℝ) * c0)
          * ((∏ i, ∏ j ∈ Ioi i, (t j - t i)) ^ 2 * Real.exp (-Kr * ∑ i, Vfield (t i)))
          * ∏ k, (1 + y k) ^ 5 := by
        have e1 : Real.exp ((h n : ℝ) * c0 - Kr * ∑ k, Vfield (t k))
            = Real.exp ((h n : ℝ) * c0) * Real.exp (-Kr * ∑ i, Vfield (t i)) := by
          rw [← Real.exp_add]; ring_nf
        rw [e1, Real.exp_add]; ring
    _ ≤ Real.exp (2 * (h n : ℝ) * ((h n : ℝ) - 1) * Real.log Kr + (h n : ℝ) * c0)
          * (Real.exp A * Real.exp (-∑ k, y k / Kr)) * ∏ k, (1 + y k) ^ 5 := by
        gcongr
    _ = _ := by
        rw [hc0]
        rw [show ∀ a b c d : ℝ, Real.exp a * (Real.exp b * c) * d = Real.exp (a + b) * (d * c)
          from fun a b c d => by rw [Real.exp_add]; ring]
        congr 2
        ring

/-- `∫_0^∞ (1+y)⁵ e^{−y/K} dy = ∑_k C(5,k) k! K^{k+1} ≤ 326 K⁶` (`= 652/2`; K ≥ 1). -/
theorem integral_g_le (Kn : ℝ) (hK : 1 ≤ Kn) :
    ∫ y in Ioi (0 : ℝ), (1 + y) ^ 5 * Real.exp (-(y / Kn)) ≤ 326 * Kn ^ 6 := by
  have hK0 : 0 < Kn := by linarith
  have hc : 0 < (Kn)⁻¹ := inv_pos.2 hK0
  have hexp : ∀ y : ℝ, (1 + y) ^ 5 * Real.exp (-(y / Kn))
      = ∑ k ∈ range 6, ((Nat.choose 5 k : ℝ)) * (y ^ k * Real.exp (-(Kn⁻¹ * y))) := by
    intro y
    rw [add_comm, add_pow, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [div_eq_inv_mul]; ring
  simp_rw [hexp]
  rw [integral_finsetSum _ (fun k _ =>
    (Positivity.integrableOn_pow_mul_exp k hc).const_mul _)]
  simp_rw [integral_const_mul, Positivity.integral_pow_mul_exp _ hc, inv_pow, div_inv_eq_mul]
  have hp : ∀ k ∈ range 6, Kn ^ (k + 1) ≤ Kn ^ 6 := fun k hk =>
    pow_le_pow_right₀ hK (by have := Finset.mem_range.1 hk; omega)
  calc ∑ k ∈ range 6, (Nat.choose 5 k : ℝ) * ((Nat.factorial k : ℝ) * Kn ^ (k + 1))
      ≤ ∑ k ∈ range 6, (Nat.choose 5 k : ℝ) * ((Nat.factorial k : ℝ) * Kn ^ 6) :=
        Finset.sum_le_sum fun k hk => by have := hp k hk; gcongr
    _ = 326 * Kn ^ 6 := by
        simp [Finset.sum_range_succ, Nat.choose, Nat.factorial]; ring

theorem integrableOn_g (Kn : ℝ) (hK : 0 < Kn) :
    IntegrableOn (fun y : ℝ => (1 + y) ^ 5 * Real.exp (-(y / Kn))) (Ioi 0) := by
  have hc : 0 < (Kn)⁻¹ := inv_pos.2 hK
  have hexp : ∀ y : ℝ, (1 + y) ^ 5 * Real.exp (-(y / Kn))
      = ∑ k ∈ range 6, ((Nat.choose 5 k : ℝ)) * (y ^ k * Real.exp (-(Kn⁻¹ * y))) := by
    intro y
    rw [add_comm, add_pow, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [div_eq_inv_mul]; ring
  simp_rw [hexp]
  exact integrable_finsetSum _ fun k _ =>
    (Positivity.integrableOn_pow_mul_exp k hc).const_mul _

/-- **(6.13) + integration**: the Gram integral bound. -/
theorem gram_bound (n : ℕ) (hn : 0 < n) (A : ℝ) (hA : ConfigBound n A) :
    ((h n).factorial : ℝ) * evalZeta5 (Delta n)
      ≤ Real.exp ((h n : ℝ) * (Real.log 8192 + 12)
          + (2 * (h n : ℝ) * ((h n : ℝ) - 1)
              + (h n : ℝ) * (12 * (N n : ℝ) - 2 * (K n : ℝ) + 12)) * Real.log (K n : ℝ)
          + A)
        * (326 * (K n : ℝ) ^ 6) ^ (h n) := by
  have hKpos : (0 : ℝ) < (K n : ℝ) := by
    have : 0 < K n := by simp only [K]; omega
    exact_mod_cast this
  set C := Real.exp ((h n : ℝ) * (Real.log 8192 + 12)
          + (2 * (h n : ℝ) * ((h n : ℝ) - 1)
              + (h n : ℝ) * (12 * (N n : ℝ) - 2 * (K n : ℝ) + 12)) * Real.log (K n : ℝ)
          + A) with hC
  set g : ℝ → ℝ := fun y => (1 + y) ^ 5 * Real.exp (-(y / (K n : ℝ))) with hg
  have hpos : ∀ᵐ y ∂(Measure.pi fun _ : Fin (h n) => volume.restrict (Ioi (0 : ℝ))),
      ∀ k, 0 < y k :=
    ae_all_iff.2 fun k =>
      (Measure.tendsto_eval_ae_ae (i := k)).eventually (ae_restrict_mem measurableSet_Ioi)
  rw [eq_6_10]
  have hint : Integrable (fun y : Fin (h n) → ℝ => C * ∏ k, g (y k))
      (Measure.pi fun _ => volume.restrict (Ioi (0 : ℝ))) :=
    (Integrable.fintype_prod (f := fun _ => g)
      (fun _ => integrableOn_g _ hKpos)).const_mul C
  calc _ ≤ ∫ y : Fin (h n) → ℝ, C * ∏ k, g (y k)
          ∂(Measure.pi fun _ => volume.restrict (Ioi (0 : ℝ))) := by
        refine integral_mono_of_nonneg ?_ hint ?_
        · filter_upwards [hpos] with y hy
          exact mul_nonneg (sq_nonneg _) (Finset.prod_nonneg fun k _ => fW_nonneg n (hy k))
        · filter_upwards [hpos] with y hy
          exact integrand_le n hn A hA y hy
    _ = C * (∫ y in Ioi (0 : ℝ), g y) ^ (h n) := by
        rw [integral_const_mul, integral_fintype_prod_eq_pow, Fintype.card_fin]
    _ ≤ C * (326 * (K n : ℝ) ^ 6) ^ (h n) := by
        gcongr
        · exact setIntegral_nonneg measurableSet_Ioi fun y hy => by
            have : (0:ℝ) < y := hy
            positivity
        · exact integral_g_le _ (by
            have : 1 ≤ K n := by simp only [K]; omega
            exact_mod_cast this)

/-! ## 4. Bookkeeping: (6.14) from a configuration bound -/

/-- **(6.14) from any configuration bound with `≤ 3h log K + 131h` lower-order terms.**
Uses `log h! ≥ h log h − h + 1` (`RealBound.log_factorial_ge`), which returns one
`h log K`; the paper's (6.9) has `2h log K + (120+√2)h`, well inside. -/
theorem eq_6_14_of_config (n : ℕ) (hn : 0 < n) (hΔpos : 0 < evalZeta5 (Delta n)) (A : ℝ)
    (hA : ConfigBound n A)
    (hAle : A ≤ ((lam : ℝ) * RealBound.M0 - RealBound.Irho) * (K n : ℝ) ^ 2
      + 3 * (h n : ℝ) * Real.log (K n : ℝ) + 131 * (h n : ℝ)) :
    Real.log (evalZeta5 (Delta n))
      ≤ 2 * (h n : ℝ) * ((h n : ℝ) + 6 * (N n : ℝ) - (K n : ℝ)) * Real.log (K n : ℝ)
        + ((lam : ℝ) * RealBound.M0 - RealBound.Irho) * (K n : ℝ) ^ 2
        + 18 * (h n : ℝ) * Real.log (K n : ℝ) + 160 * (h n : ℝ) := by
  have hg := gram_bound n hn A hA
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hK : ((K n : ℕ) : ℝ) = 40 * (n : ℝ) := by simp only [K]; push_cast; ring
  have hN : ((N n : ℕ) : ℝ) = 3 * (n : ℝ) := by simp only [N]; push_cast; ring
  have hh : ((h n : ℕ) : ℝ) = 37 * (n : ℝ) := by simp only [h]; push_cast; ring
  have hKpos : (0 : ℝ) < (K n : ℝ) := by rw [hK]; linarith
  have hfac : (0 : ℝ) < ((h n).factorial : ℝ) := by exact_mod_cast (h n).factorial_pos
  have hP : (0 : ℝ) < (326 * (K n : ℝ) ^ 6) ^ (h n) := by positivity
  set E := (h n : ℝ) * (Real.log 8192 + 12)
          + (2 * (h n : ℝ) * ((h n : ℝ) - 1)
              + (h n : ℝ) * (12 * (N n : ℝ) - 2 * (K n : ℝ) + 12)) * Real.log (K n : ℝ)
          + A with hE
  -- take logs of the Gram bound
  have hlog : Real.log ((h n).factorial : ℝ) + Real.log (evalZeta5 (Delta n))
      ≤ E + (h n : ℝ) * (Real.log 326 + 6 * Real.log (K n : ℝ)) := by
    have := Real.log_le_log (mul_pos hfac hΔpos) hg
    rw [Real.log_mul hfac.ne' hΔpos.ne', Real.log_mul (Real.exp_pos _).ne' hP.ne',
      Real.log_exp, Real.log_pow, Real.log_mul (by norm_num) (by positivity),
      Real.log_pow] at this
    push_cast at this
    linarith
  -- log h! ≥ h log h − h + 1, and log h = log(37/40) + log K
  have hfg := RealBound.log_factorial_ge (h n) (by simp only [h]; omega)
  have hhK : ((h n : ℕ) : ℝ) = (37 / 40 : ℝ) * (K n : ℝ) := by rw [hh, hK]; ring
  have hlogh : Real.log ((h n : ℕ) : ℝ) = Real.log (37 / 40 : ℝ) + Real.log (K n : ℝ) := by
    rw [hhK, Real.log_mul (by norm_num) hKpos.ne']
  rw [hlogh] at hfg
  -- numerics: log 8192 = 13 log 2, log 326 ≤ 9 log 2, log 2 < 0.6931471808, log(37/40) ≥ -3/37
  have h8192 : Real.log 8192 = 13 * Real.log 2 := by
    rw [show (8192 : ℝ) = 2 ^ 13 by norm_num, Real.log_pow]; norm_num
  have h326 : Real.log 326 ≤ 9 * Real.log 2 := by
    have : (9 : ℝ) * Real.log 2 = Real.log ((2 : ℝ) ^ 9) := by rw [Real.log_pow]; norm_num
    rw [this]; exact Real.log_le_log (by norm_num) (by norm_num)
  have hl2 := Real.log_two_lt_d9
  have hl37 : -(3 / 37 : ℝ) ≤ Real.log (37 / 40 : ℝ) := by
    have := RealBound.one_sub_inv_le_log (x := (37 / 40 : ℝ)) (by norm_num)
    norm_num at this ⊢; linarith
  have hhnn : (0 : ℝ) ≤ (h n : ℝ) := by positivity
  have e1 := mul_le_mul_of_nonneg_left h326 hhnn
  have e2 := mul_le_mul_of_nonneg_left hl2.le hhnn
  have e3 := mul_le_mul_of_nonneg_left hl37 hhnn
  rw [hE, h8192] at hlog
  nlinarith [hlog, hfg, hAle, e1, e2, e3, hhnn]

/-- The paper's (6.9) constants are admissible for `eq_6_14_of_config`. -/
theorem paper_6_9_admissible (n : ℕ) (hn : 0 < n) :
    ((lam : ℝ) * RealBound.M0 - RealBound.Irho) * (K n : ℝ) ^ 2
        + (120 + Real.sqrt 2) * (h n : ℝ) + 2 * (h n : ℝ) * Real.log (K n : ℝ)
      ≤ ((lam : ℝ) * RealBound.M0 - RealBound.Irho) * (K n : ℝ) ^ 2
        + 3 * (h n : ℝ) * Real.log (K n : ℝ) + 131 * (h n : ℝ) := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hK : ((K n : ℕ) : ℝ) = 40 * (n : ℝ) := by simp only [K]; push_cast; ring
  have hh : ((h n : ℕ) : ℝ) = 37 * (n : ℝ) := by simp only [h]; push_cast; ring
  have hlogK : 0 ≤ Real.log (K n : ℝ) := Real.log_nonneg (by rw [hK]; linarith)
  have hs2 : Real.sqrt 2 ≤ 2 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hhnn : (0 : ℝ) ≤ (h n : ℝ) := by positivity
  nlinarith [mul_nonneg hhnn hlogK, mul_le_mul_of_nonneg_right hs2 hhnn]

end

end Gram
end Sec6
end Zeta5
