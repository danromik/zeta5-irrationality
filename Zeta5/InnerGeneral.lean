/-
Zeta5/InnerGeneral.lean

PART 2 OF THE PROOF OF `Zeta5.Section3.entry_bounds_4_2_4_3`.

**The general local bound.**  For a numerator `W` and a finite set `S` of integer poles,
with `Q = ∏_{r∈S}(x − r)`:

    v_p^G(τ^ext_X(W/Q)) ≥ min_{a mod p} (u_a − t_a) − 4,

where `u_a` is the number of zeros of `W` in the class `a` (the power of `p` that the near
zeros supply at `x = a + pz`) and `t_a = #{r ∈ S : r ≡ a}`.  Hypotheses: distinct poles in the
same class differ by `p` times a unit, `d(r) < p²`, and `u_a ≤ p + 1` ("both degrees are at
most `p+1`", p. 11).  This is (4.2)/(4.3) "for the entire summands" (p. 11) in a form
independent of the paper's specific rational functions; `InnerEntries.lean` instantiates it.

Proof: `τ^ext_X(W/Q) = τ(P) + ∑_r c_r (H^{(5)}_{d(r)} − X)` with `P = W div Q`.
* Pole terms: `v_p(c_r) ≥ u_a − t_a + 1` (`resid_vge`), `v_p(H^{(5)}_{d(r)}) ≥ −5`.
* Polynomial part: `p⁴τ(P) = ∑_{a<p} τ(P(a+pz))` (`raabe_tau`), and each summand has
  valuation `≥ min_b(u_b − t_b)` by `class_bound`, applied to the exact identity obtained by
  substituting `x = a + pz` into the partial-fraction decomposition
  `W = P·Q + ∑_r c_r Q/(x−r)` and splitting `Q` into near and far factors (`class_identity`).

Checked numerically before being formalised (exact rational arithmetic, `p = 7, 11, 13, 17`,
random `W`, `S` satisfying the hypotheses, `E` from `−5` to `9`): no failure in 360 random
instances, the bound attained with equality in most of them, and the claim with `E + 1` in
place of `E` failing whenever it is attained; violating the unit-difference hypothesis makes
it fail in 119/120 instances.  On the paper's own entries (basis (4.5), K = 80, p = 23,
all 2775 entries, and K = 40, p = 13, all 703 entries) the exponent `min_a(u_a − t_a) − 4`
coincides exactly with `min((4.3), min_c (4.2))` and the true valuation never falls below it.
-/
import Zeta5.InnerTate

namespace Zeta5

namespace InnerEntries

open Polynomial Finset

noncomputable section

section General

variable {p : ℕ} [hpf : Fact p.Prime]

/-- The substitution `x = a + p z`. -/
def phi (p a : ℕ) : ℚ[X] := C (a : ℚ) + C (p : ℚ) * X

/-- **The class-`a` factorisation of a numerator**: at `x = a + pz`,
`W(a+pz) = p^u · U(z) · N_f(z)` with `U` integral of degree `≤ d` and `N_f` of Tate decay
`0`.  (For a product of linear factors `x − y`, `u` counts the `y ≡ a (mod p)`.) -/
def ClassFact (p a : ℕ) (W : ℚ[X]) (u d : ℕ) : Prop :=
  ∃ U Nf : ℚ[X], W.comp (C (a : ℚ) + C (p : ℚ) * X) = C ((p : ℚ) ^ u) * U * Nf ∧
    vGAtLeast p U 0 ∧ U.natDegree ≤ d ∧ Tate p Nf 0

/-! ### Partial fractions for `Q = ∏_{r∈S}(x − r)` -/

lemma Tpoly_natDegree (S : Finset ℤ) : (Tpoly S).natDegree = S.card := by
  rw [Tpoly, natDegree_prod_of_monic _ _ (fun r _ => monic_X_sub_C _),
    Finset.sum_congr rfl (fun r _ => natDegree_X_sub_C ((r : ℤ) : ℚ))]
  simp

lemma Tpoly_erase_eval_self {S : Finset ℤ} {r : ℤ} (hr : r ∈ S) :
    (Tpoly (S.erase r)).eval (r : ℚ) = (derivative (Tpoly S)).eval (r : ℚ) := by
  rw [Tpoly_derivative_eval hr, Tpoly, eval_prod]
  simp [eval_sub]

lemma Tpoly_derivative_eval_ne_zero {S : Finset ℤ} {r : ℤ} (hr : r ∈ S) :
    (derivative (Tpoly S)).eval (r : ℚ) ≠ 0 := by
  rw [Tpoly_derivative_eval hr]
  refine Finset.prod_ne_zero_iff.2 fun q hq => sub_ne_zero.2 ?_
  exact Int.cast_injective.ne (Finset.ne_of_mem_erase hq).symm

/-- Polynomial division and simple partial fractions for `Q = ∏_{r∈S}(x−r)`:
`W = (W div Q)·Q + ∑_r c_r ∏_{s≠r}(x−s)`, `c_r = resid S W r`. -/
theorem Tpoly_partial_fraction (S : Finset ℤ) (W : ℚ[X]) :
    W = (W /ₘ Tpoly S) * Tpoly S + ∑ r ∈ S, C (resid S W r) * Tpoly (S.erase r) := by
  classical
  have hrem : W %ₘ Tpoly S = ∑ r ∈ S, C (resid S W r) * Tpoly (S.erase r) := by
    rcases S.eq_empty_or_nonempty with rfl | hne
    · simp [Tpoly]
    have hcard : 0 < S.card := Finset.card_pos.2 hne
    refine Polynomial.eq_of_natDegree_lt_card_of_eval_eq' _ _
      (S.image (fun r : ℤ => (r : ℚ))) ?_ ?_
    · intro x hx
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hx
      rw [Polynomial.eval_finsetSum, Finset.sum_eq_single r]
      · rw [eval_mul, eval_C, resid, Tpoly_erase_eval_self hr,
          div_mul_cancel₀ _ (Tpoly_derivative_eval_ne_zero hr)]
      · intro s _ hsr
        rw [eval_mul, Tpoly_eval_root (Finset.mem_erase.2 ⟨fun h => hsr h.symm, hr⟩), mul_zero]
      · intro h; exact absurd hr h
    · rw [Finset.card_image_of_injective _ Int.cast_injective]
      refine max_lt ?_ ?_
      · have hne1 : Tpoly S ≠ 1 := by
          intro h
          have := Tpoly_natDegree S
          rw [h, natDegree_one] at this
          omega
        have := natDegree_modByMonic_lt W (Tpoly_monic S) hne1
        rwa [Tpoly_natDegree] at this
      · refine lt_of_le_of_lt (natDegree_sum_le_of_forall_le _ _ (n := S.card - 1)
          fun r hr => ?_) (by omega)
        refine le_trans (natDegree_C_mul_le _ _) ?_
        rw [Tpoly_natDegree, Finset.card_erase_of_mem hr]
  calc W = W %ₘ Tpoly S + Tpoly S * (W /ₘ Tpoly S) := (modByMonic_add_div W _).symm
    _ = _ := by rw [hrem]; ring

/-! ### The residue bound -/

lemma padicNorm_prod' {ι : Type*} (s : Finset ι) (f : ι → ℚ) :
    padicNorm p (∏ i ∈ s, f i) = ∏ i ∈ s, padicNorm p (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, padicNorm.mul, ih]

lemma padicNorm_ge_of_not_sq_dvd {z : ℤ} (hz : ¬ ((p : ℤ) ^ 2 ∣ z)) :
    (p : ℚ) ^ (-1 : ℤ) ≤ padicNorm p (z : ℚ) := by
  have hz0 : z ≠ 0 := by rintro rfl; exact hz (dvd_zero _)
  have hq0 : (z : ℚ) ≠ 0 := Int.cast_ne_zero.2 hz0
  rw [padicNorm.eq_zpow_of_nonzero hq0, padicValRat.of_int]
  apply zpow_le_zpow_right₀ (le_of_lt p_one_lt_q)
  have : padicValInt p z ≤ 1 := by
    by_contra hcon
    push Not at hcon
    exact hz ((padicValInt_dvd_iff 2 z).2 (Or.inr (by omega)))
  have : (padicValInt p z : ℤ) ≤ 1 := by exact_mod_cast this
  omega

lemma padicNorm_eq_one_of_not_dvd {z : ℤ} (hz : ¬ ((p : ℤ) ∣ z)) : padicNorm p (z : ℚ) = 1 :=
  (padicNorm.int_eq_one_iff z).2 hz

/-- `v_p(H^{(5)}_d) ≥ −5` for `d < p²`: every `v ≤ d` has `v_p(v) ≤ 1`. -/
lemma vge_H5 {d : ℕ} (hd : d < p ^ 2) : vge p (H5 d) (-5) := by
  unfold H5
  refine vge_sum fun v hv => ?_
  simp only [Finset.mem_Icc] at hv
  have hv0 : v ≠ 0 := by omega
  have hvq : (v : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hv0
  have hval : padicValNat p v ≤ 1 := by
    by_contra hcon
    push Not at hcon
    have hdvd : p ^ 2 ∣ v := (padicValNat_dvd_iff_le hv0).2 hcon
    have := Nat.le_of_dvd (by omega) hdvd
    omega
  have hpv : padicValRat p (v : ℚ) ≤ 1 := by
    rw [padicValRat.of_nat]; exact_mod_cast hval
  refine vge_iff_val.2 (Or.inr ?_)
  rw [padicValRat.div one_ne_zero (pow_ne_zero _ hvq), padicValRat.one, padicValRat.pow]
  push_cast
  linarith

/-- The class representative: `r = (r mod p) + p·⌊r/p⌋`. -/
lemma int_decomp (r : ℤ) :
    (r : ℚ) = (((r % (p : ℤ)).toNat : ℕ) : ℚ) + (p : ℚ) * ((r / (p : ℤ) : ℤ) : ℚ) := by
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hpf.out.ne_zero
  have hnn : 0 ≤ r % (p : ℤ) := Int.emod_nonneg _ hp0
  have h1 : (((r % (p : ℤ)).toNat : ℕ) : ℤ) = r % (p : ℤ) := Int.toNat_of_nonneg hnn
  have h2 : r % (p : ℤ) + (p : ℤ) * (r / (p : ℤ)) = r := by
    have := Int.emod_add_ediv_mul r (p : ℤ)
    linarith [mul_comm (r / (p : ℤ)) (p : ℤ)]
  have h3 : ((((r % (p : ℤ)).toNat : ℕ) : ℤ) : ℚ) + ((p : ℤ) : ℚ) * ((r / (p : ℤ) : ℤ) : ℚ)
      = (r : ℚ) := by
    rw [h1]; exact_mod_cast h2
  push_cast at h3
  linarith

/-- **The residue bound**: `v_p(c_r) ≥ u − t + 1`, where `u` is the class count of the
numerator and `t` the number of poles in the class of `r`. -/
theorem resid_vge {S : Finset ℤ} {W : ℚ[X]} {r : ℤ} (hr : r ∈ S) {u d : ℕ}
    (hW : ClassFact p (r % (p : ℤ)).toNat W u d)
    (hS : ∀ s ∈ S, s ≠ r → (p : ℤ) ∣ r - s → ¬ ((p : ℤ) ^ 2 ∣ r - s)) :
    vge p (resid S W r)
      ((u : ℤ) - ((S.filter (fun s => s % (p : ℤ) = r % (p : ℤ))).card : ℤ) + 1) := by
  classical
  obtain ⟨U, Nf, hcomp, hU, _, hNf⟩ := hW
  set a : ℕ := (r % (p : ℤ)).toNat with ha
  set r' : ℤ := r / (p : ℤ) with hr'
  -- the numerator at `r`
  have hWr : W.eval (r : ℚ) = (p : ℚ) ^ u * (U.eval (r' : ℚ) * Nf.eval (r' : ℚ)) := by
    have h1 : W.eval (r : ℚ) = (W.comp (C (a : ℚ) + C (p : ℚ) * X)).eval (r' : ℚ) := by
      rw [eval_comp]
      simp only [eval_add, eval_C, eval_mul, eval_X]
      rw [int_decomp (p := p) r]
    rw [h1, hcomp]
    simp only [eval_mul, eval_C]
    ring
  have hWv : vge p (W.eval (r : ℚ)) u := by
    rw [hWr]
    have hUe : vge p (U.eval (r' : ℚ)) 0 :=
      vge_zero_iff.2 (padicNorm_eval_le_one hU (padicNorm.of_int r'))
    have hNe : vge p (Nf.eval (r' : ℚ)) 0 :=
      vge_zero_iff.2 (padicNorm_eval_le_one (vGAtLeast_of_Tate hNf) (padicNorm.of_int r'))
    simpa using vge_mul (vge_pow_p (p := p) u) (vge_mul hUe hNe)
  -- the denominator `Q'(r)` has `|Q'(r)|_p ≥ p^{-(t-1)}`
  set t : ℕ := (S.filter (fun s => s % (p : ℤ) = r % (p : ℤ))).card with ht
  have hrmem : r ∈ S.filter (fun s => s % (p : ℤ) = r % (p : ℤ)) :=
    Finset.mem_filter.2 ⟨hr, rfl⟩
  have ht1 : 1 ≤ t := Finset.card_pos.2 ⟨r, hrmem⟩
  have hQ : (p : ℚ) ^ (-((t : ℤ) - 1)) ≤ padicNorm p ((derivative (Tpoly S)).eval (r : ℚ)) := by
    rw [Tpoly_derivative_eval hr, padicNorm_prod']
    have hfac : ∀ s ∈ S.erase r,
        (if s % (p : ℤ) = r % (p : ℤ) then (p : ℚ) ^ (-1 : ℤ) else 1)
          ≤ padicNorm p ((r : ℚ) - (s : ℚ)) := by
      intro s hs
      have hsr : s ≠ r := Finset.ne_of_mem_erase hs
      have hsS : s ∈ S := Finset.mem_of_mem_erase hs
      have hcast : ((r : ℚ) - (s : ℚ)) = (((r - s : ℤ)) : ℚ) := by push_cast; ring
      rw [hcast]
      split_ifs with hcl
      · have hdvd : (p : ℤ) ∣ r - s := by
          rw [Int.dvd_iff_emod_eq_zero, Int.sub_emod, hcl, sub_self, Int.zero_emod]
        exact padicNorm_ge_of_not_sq_dvd (hS s hsS hsr hdvd)
      · have hndvd : ¬ (p : ℤ) ∣ r - s := by
          intro hdvd
          apply hcl
          have := Int.emod_emod_of_dvd r (dvd_refl (p : ℤ))
          rw [Int.dvd_iff_emod_eq_zero, Int.sub_emod] at hdvd
          have hpz : (p : ℤ) ≠ 0 := by exact_mod_cast hpf.out.ne_zero
          have h0 := Int.emod_nonneg r hpz
          have h1 := Int.emod_nonneg s hpz
          have h2 := Int.emod_lt_of_pos r (by exact_mod_cast hpf.out.pos : (0 : ℤ) < p)
          have h3 := Int.emod_lt_of_pos s (by exact_mod_cast hpf.out.pos : (0 : ℤ) < p)
          have hx : (r % (p : ℤ) - s % (p : ℤ)) % (p : ℤ) = 0 := hdvd
          have hdv : (p : ℤ) ∣ r % (p : ℤ) - s % (p : ℤ) := Int.dvd_of_emod_eq_zero hx
          obtain ⟨k, hk⟩ := hdv
          have : k = 0 := by
            by_contra hk0
            rcases lt_or_gt_of_ne hk0 with hneg | hpos
            · have : (p : ℤ) * k ≤ -(p : ℤ) := by nlinarith
              omega
            · have : (p : ℤ) ≤ (p : ℤ) * k := by nlinarith
              omega
          subst this
          omega
        rw [padicNorm_eq_one_of_not_dvd hndvd]
    have hle := Finset.prod_le_prod₀ (fun s _ => by
      split_ifs
      · exact le_of_lt (zpow_p_pos _)
      · exact zero_le_one) hfac
    refine le_trans (le_of_eq ?_) hle
    rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const, ← zpow_natCast,
      ← zpow_mul]
    congr 1
    have hc : ((S.erase r).filter (fun s => s % (p : ℤ) = r % (p : ℤ))).card = t - 1 := by
      rw [Finset.filter_erase, Finset.card_erase_of_mem hrmem]
    rw [hc]
    push_cast [ht1]
    ring
  -- combine
  unfold vge
  rw [resid_eq_eval _ hr, padicNorm.div]
  have hQpos : (0 : ℚ) < (p : ℚ) ^ (-((t : ℤ) - 1)) := zpow_p_pos _
  calc padicNorm p (W.eval (r : ℚ)) / padicNorm p ((derivative (Tpoly S)).eval (r : ℚ))
      ≤ (p : ℚ) ^ (-(u : ℤ)) / (p : ℚ) ^ (-((t : ℤ) - 1)) :=
        div_le_div₀ (le_of_lt (zpow_p_pos _)) hWv hQpos hQ
    _ = (p : ℚ) ^ (-((u : ℤ) - (t : ℤ) + 1)) := by
        rw [← zpow_sub₀ (ne_of_gt p_pos_q)]
        congr 1
        ring

/-! ### Near and far factors at `x = a + pz` -/

/-- The poles in the class `a`. -/
def nearSet (p a : ℕ) (S : Finset ℤ) : Finset ℤ := S.filter (fun r => r % (p : ℤ) = a)

/-- The poles outside the class `a`. -/
def farSet (p a : ℕ) (S : Finset ℤ) : Finset ℤ := S.filter (fun r => ¬ (r % (p : ℤ) = a))

/-- The monic near-pole polynomial `T(z) = ∏_{r ≡ a}(z − ⌊r/p⌋)`. -/
def Tn (p a : ℕ) (S : Finset ℤ) : ℚ[X] :=
  ∏ r ∈ nearSet p a S, (X - C (((r / (p : ℤ) : ℤ)) : ℚ))

/-- The far-pole polynomial `D(z) = ∏_{r ≢ a}((a − r) + pz)`. -/
def Df (p a : ℕ) (S : Finset ℤ) : ℚ[X] :=
  ∏ r ∈ farSet p a S, (C ((a : ℚ) - (r : ℚ)) + C (p : ℚ) * X)

lemma comp_X_sub_C_phi (a : ℕ) (r : ℤ) :
    (X - C (r : ℚ)).comp (phi p a) = C ((a : ℚ) - (r : ℚ)) + C (p : ℚ) * X := by
  simp only [phi, sub_comp, X_comp, C_comp, map_sub]
  ring

lemma comp_X_sub_C_phi_near {a : ℕ} (ha : a < p) {r : ℤ} (hr : r % (p : ℤ) = a) :
    (X - C (r : ℚ)).comp (phi p a) = C (p : ℚ) * (X - C (((r / (p : ℤ) : ℤ)) : ℚ)) := by
  rw [comp_X_sub_C_phi]
  have hdec := int_decomp (p := p) r
  have ha' : ((r % (p : ℤ)).toNat : ℕ) = a := by
    rw [hr]; simp
  rw [ha'] at hdec
  rw [hdec, mul_sub, ← C_mul]
  simp only [map_sub, map_add, map_mul]
  ring

lemma Tn_monic (a : ℕ) (S : Finset ℤ) : (Tn p a S).Monic :=
  monic_prod_of_monic _ _ fun _ _ => monic_X_sub_C _

lemma Tn_natDegree (a : ℕ) (S : Finset ℤ) : (Tn p a S).natDegree = (nearSet p a S).card := by
  rw [Tn, natDegree_prod_of_monic _ _ (fun r _ => monic_X_sub_C _),
    Finset.sum_congr rfl (fun r _ => natDegree_X_sub_C (((r / (p : ℤ) : ℤ)) : ℚ))]
  simp

lemma Tn_int (a : ℕ) (S : Finset ℤ) : vGAtLeast p (Tn p a S) 0 := by
  classical
  have := vGAtLeast_prod (p := p) (nearSet p a S)
    (fun r => X - C (((r / (p : ℤ) : ℤ)) : ℚ)) (fun _ => 0)
    (fun r _ => vGAtLeast_X_sub_intC _)
  simpa [Tn] using this

lemma Df_Tate (a : ℕ) (S : Finset ℤ) : Tate p (Df p a S) 0 := by
  classical
  refine Tate_prod fun r _ => Tate_lin ?_
  have : ((a : ℚ) - (r : ℚ)) = (((a : ℤ) - r : ℤ) : ℚ) := by push_cast; ring
  rw [this]
  exact vge_intCast _

/-- If `p ∣ a − r` with `0 ≤ a < p`, then `r mod p = a`. -/
lemma emod_eq_of_dvd_sub {a : ℕ} (ha : a < p) {r : ℤ} (hdvd : (p : ℤ) ∣ (a : ℤ) - r) :
    r % (p : ℤ) = a := by
  have h1 : (p : ℤ) ∣ r - (a : ℤ) := by
    have := dvd_neg.2 hdvd
    rwa [neg_sub] at this
  have h2 : r % (p : ℤ) = (a : ℤ) % (p : ℤ) :=
    Int.emod_eq_emod_iff_emod_sub_eq_zero.2 (Int.emod_eq_zero_of_dvd h1)
  rw [h2, Int.emod_eq_of_lt (by positivity) (by exact_mod_cast ha)]

lemma Df_coeff_zero {a : ℕ} (ha : a < p) (S : Finset ℤ) :
    padicNorm p ((Df p a S).coeff 0) = 1 := by
  classical
  rw [Df, coeff_zero_prod, padicNorm_prod']
  refine Finset.prod_eq_one fun r hr => ?_
  have hr' : ¬ (r % (p : ℤ) = a) := (Finset.mem_filter.1 hr).2
  simp only [coeff_add, coeff_C_zero, coeff_C_mul, coeff_X_zero, mul_zero, add_zero]
  have : ((a : ℚ) - (r : ℚ)) = (((a : ℤ) - r : ℤ) : ℚ) := by push_cast; ring
  rw [this]
  exact padicNorm_eq_one_of_not_dvd fun hdvd => hr' (emod_eq_of_dvd_sub ha hdvd)

/-- `Q(a + pz) = p^t · T(z) · D(z)`. -/
lemma comp_Tpoly {a : ℕ} (ha : a < p) (S : Finset ℤ) :
    (Tpoly S).comp (phi p a)
      = C ((p : ℚ) ^ (nearSet p a S).card) * Tn p a S * Df p a S := by
  classical
  rw [Tpoly, Polynomial.prod_comp,
    ← Finset.prod_filter_mul_prod_filter_not S (fun r => r % (p : ℤ) = a)]
  congr 1
  · rw [Tn, nearSet, Finset.prod_congr rfl fun r hr =>
      comp_X_sub_C_phi_near (p := p) ha (Finset.mem_filter.1 hr).2,
      Finset.prod_mul_distrib, Finset.prod_const, map_pow]
  · rw [Df, farSet]
    exact Finset.prod_congr rfl fun r _ => comp_X_sub_C_phi a r

/-- `P(a+pz)` is `p`-integral when `P` is. -/
lemma vGAtLeast_comp_phi {P : ℚ[X]} (hP : vGAtLeast p P 0) (a : ℕ) :
    vGAtLeast p (P.comp (phi p a)) 0 := by
  classical
  have hphi : vGAtLeast p (phi p a) 0 :=
    vGAtLeast_of_Tate (Tate_lin (vge_natCast a))
  conv_lhs => rw [P.as_sum_range_C_mul_X_pow]
  rw [Polynomial.sum_comp]
  refine vGAtLeast_sum fun k _ => ?_
  rw [mul_comp, C_comp, X_pow_comp]
  have hpow : vGAtLeast p ((phi p a) ^ k) 0 := by
    have := vGAtLeast_prod (p := p) (Finset.range k) (fun _ => phi p a) (fun _ => 0)
      (fun _ _ => hphi)
    simpa using this
  have hc : vGAtLeast p (C (P.coeff k)) 0 :=
    vGAtLeast_C ((vGAtLeast_zero_iff P).1 hP k)
  simpa using vGAtLeast_mul hc hpow

/-! ### The per-class identity -/

/-- **The class-`a` identity**: substituting `x = a + pz` in `W = P·Q + ∑_r c_r Q/(x−r)` and
dividing by `p^t`,

    `P(a+pz)·T·D = p^e(U·N_f − D·R) − T·F`,   `e = u − t`,

with `R = ∑_{r≡a} c_r p^{−(e+1)} T/(z−r')` and `F = ∑_{r≢a} c_r D/((a−r)+pz)`. -/
theorem class_identity {a : ℕ} (ha : a < p) (S : Finset ℤ) (W U Nf : ℚ[X]) (u : ℕ)
    (hcomp : W.comp (phi p a) = C ((p : ℚ) ^ u) * U * Nf) :
    (W /ₘ Tpoly S).comp (phi p a) * Tn p a S * Df p a S
      = C ((p : ℚ) ^ ((u : ℤ) - (nearSet p a S).card))
          * (U * Nf - Df p a S *
              ∑ r ∈ nearSet p a S, C (resid S W r *
                (p : ℚ) ^ (-((u : ℤ) - (nearSet p a S).card + 1))) * Tn p a (S.erase r))
        - Tn p a S * ∑ r ∈ farSet p a S, C (resid S W r) * Df p a (S.erase r) := by
  classical
  set t : ℕ := (nearSet p a S).card with ht
  set e : ℤ := (u : ℤ) - t with he
  set π : ℚ[X] := (W /ₘ Tpoly S).comp (phi p a) with hπ
  have hp0 : (p : ℚ) ≠ 0 := ne_of_gt p_pos_q
  -- the partial-fraction decomposition, composed with `x = a + pz`
  have hcompW : W.comp (phi p a) = π * (Tpoly S).comp (phi p a)
      + ∑ r ∈ S, C (resid S W r) * (Tpoly (S.erase r)).comp (phi p a) := by
    conv_lhs => rw [Tpoly_partial_fraction S W]
    rw [add_comp, mul_comp, Polynomial.sum_comp]
    congr 1
    exact Finset.sum_congr rfl fun r _ => by rw [mul_comp, C_comp]
  rw [comp_Tpoly ha S, hcomp,
    ← Finset.sum_filter_add_sum_filter_not S (fun r => r % (p : ℤ) = a)] at hcompW
  have hnear : ∀ r ∈ S.filter (fun r => r % (p : ℤ) = a),
      C (resid S W r) * (Tpoly (S.erase r)).comp (phi p a)
        = C (resid S W r) * (C ((p : ℚ) ^ (t - 1)) * Tn p a (S.erase r) * Df p a S) := by
    intro r hr
    have hr' : r ∈ nearSet p a S := hr
    have hrnf : r ∉ farSet p a S := fun h => (Finset.mem_filter.1 h).2 (Finset.mem_filter.1 hr).2
    have hfar : farSet p a (S.erase r) = farSet p a S := by
      show (S.erase r).filter _ = _
      rw [Finset.filter_erase]
      exact Finset.erase_eq_of_notMem hrnf
    have hcard : (nearSet p a (S.erase r)).card = t - 1 := by
      show ((S.erase r).filter _).card = _
      rw [Finset.filter_erase]
      exact Finset.card_erase_of_mem hr'
    have hDf : Df p a (S.erase r) = Df p a S := by
      simp only [Df, hfar]
    rw [comp_Tpoly ha, hcard, hDf]
  have hfar : ∀ r ∈ S.filter (fun r => ¬ (r % (p : ℤ) = a)),
      C (resid S W r) * (Tpoly (S.erase r)).comp (phi p a)
        = C (resid S W r) * (C ((p : ℚ) ^ t) * Tn p a S * Df p a (S.erase r)) := by
    intro r hr
    have hrnn : r ∉ nearSet p a S := fun h => (Finset.mem_filter.1 hr).2 (Finset.mem_filter.1 h).2
    have hnr : nearSet p a (S.erase r) = nearSet p a S := by
      show (S.erase r).filter _ = _
      rw [Finset.filter_erase]
      exact Finset.erase_eq_of_notMem hrnn
    have hTn : Tn p a (S.erase r) = Tn p a S := by
      simp only [Tn, hnr]
    rw [comp_Tpoly ha, hnr, hTn]
  rw [Finset.sum_congr rfl hnear, Finset.sum_congr rfl hfar] at hcompW
  -- scalar identities
  have hA : C ((p : ℚ) ^ t) * C ((p : ℚ) ^ e) = C ((p : ℚ) ^ u) := by
    rw [← C_mul, ← zpow_natCast, ← zpow_natCast, ← zpow_add₀ hp0, he]
    congr 2
    ring
  have hB : C ((p : ℚ) ^ t) * (C ((p : ℚ) ^ e) * (Df p a S *
        ∑ r ∈ nearSet p a S, C (resid S W r * (p : ℚ) ^ (-((u : ℤ) - t + 1)))
          * Tn p a (S.erase r)))
      = ∑ r ∈ S.filter (fun r => r % (p : ℤ) = a),
          C (resid S W r) * (C ((p : ℚ) ^ (t - 1)) * Tn p a (S.erase r) * Df p a S) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r hr => ?_
    have ht1 : 1 ≤ t := Finset.card_pos.2 ⟨r, hr⟩
    have hsc : (p : ℚ) ^ t * ((p : ℚ) ^ e * (resid S W r * (p : ℚ) ^ (-((u : ℤ) - t + 1))))
        = resid S W r * (p : ℚ) ^ (t - 1) := by
      rw [← zpow_natCast (p : ℚ) t, ← zpow_natCast (p : ℚ) (t - 1)]
      have hpow : (p : ℚ) ^ (t : ℤ) * (p : ℚ) ^ e * (p : ℚ) ^ (-((u : ℤ) - t + 1))
          = (p : ℚ) ^ (((t - 1 : ℕ) : ℤ)) := by
        rw [← zpow_add₀ hp0, ← zpow_add₀ hp0, he]
        congr 1
        push_cast [ht1]
        ring
      calc (p : ℚ) ^ (t : ℤ) * ((p : ℚ) ^ e * (resid S W r * (p : ℚ) ^ (-((u : ℤ) - t + 1))))
          = resid S W r * ((p : ℚ) ^ (t : ℤ) * (p : ℚ) ^ e
              * (p : ℚ) ^ (-((u : ℤ) - t + 1))) := by ring
        _ = _ := by rw [hpow]
    calc C ((p : ℚ) ^ t) * (C ((p : ℚ) ^ e) * (Df p a S *
          (C (resid S W r * (p : ℚ) ^ (-((u : ℤ) - t + 1))) * Tn p a (S.erase r))))
        = C ((p : ℚ) ^ t * ((p : ℚ) ^ e * (resid S W r * (p : ℚ) ^ (-((u : ℤ) - t + 1)))))
            * (Tn p a (S.erase r) * Df p a S) := by
          simp only [C_mul]; ring
      _ = C (resid S W r * (p : ℚ) ^ (t - 1)) * (Tn p a (S.erase r) * Df p a S) := by rw [hsc]
      _ = _ := by simp only [C_mul]; ring
  have hC : C ((p : ℚ) ^ t) * (Tn p a S *
        ∑ r ∈ farSet p a S, C (resid S W r) * Df p a (S.erase r))
      = ∑ r ∈ S.filter (fun r => ¬ (r % (p : ℤ) = a)),
          C (resid S W r) * (C ((p : ℚ) ^ t) * Tn p a S * Df p a (S.erase r)) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun r _ => by ring
  have hne : (C ((p : ℚ) ^ t) : ℚ[X]) ≠ 0 := by
    rw [Ne, C_eq_zero]; exact pow_ne_zero _ hp0
  apply mul_left_cancel₀ hne
  have e1 : C ((p : ℚ) ^ t) * (π * Tn p a S * Df p a S)
      = C ((p : ℚ) ^ u) * U * Nf
        - ∑ r ∈ S.filter (fun r => r % (p : ℤ) = a),
            C (resid S W r) * (C ((p : ℚ) ^ (t - 1)) * Tn p a (S.erase r) * Df p a S)
        - ∑ r ∈ S.filter (fun r => ¬ (r % (p : ℤ) = a)),
            C (resid S W r) * (C ((p : ℚ) ^ t) * Tn p a S * Df p a (S.erase r)) := by
    rw [hcompW]; ring
  rw [e1]
  linear_combination (-(U * Nf)) * hA + hB + hC

/-! ### The per-class bound and the general bound -/

lemma vGAtLeast_C_of_vge {x : ℚ} {c : ℤ} (hx : vge p x c) : vGAtLeast p (C x) c := by
  refine vGAtLeast_iff_vge.2 fun i => ?_
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simpa using hx
  · rw [coeff_C, ite_eq_right (by omega)]
    exact vge_zero _

/-- **Each summand of the distribution formula**: `v_p(τ(P(a+pz))) ≥ min(u − t, f + 2)`,
where `v_p(c_r) ≥ f` at the far poles. -/
theorem class_tau_bound (h7 : 7 ≤ p) (S : Finset ℤ) (W : ℚ[X]) (hWint : vGAtLeast p W 0)
    {a : ℕ} (ha : a < p) {u : ℕ} (hW : ClassFact p a W u (p + 1)) (f : ℤ)
    (hfar : ∀ r ∈ farSet p a S, vge p (resid S W r) f)
    (hnear : ∀ r ∈ nearSet p a S,
      vge p (resid S W r) ((u : ℤ) - (nearSet p a S).card + 1)) :
    vge p (tau ((W /ₘ Tpoly S).comp (phi p a)))
      (min ((u : ℤ) - (nearSet p a S).card) (f + 2)) := by
  classical
  obtain ⟨U, Nf, hcomp, hU, hUdeg, hNf⟩ := hW
  set t : ℕ := (nearSet p a S).card with ht
  have hid := class_identity (p := p) ha S W U Nf u hcomp
  refine class_bound h7 (Tn_monic a S) (Tn_int a S) hU hUdeg hNf (Df_Tate a S)
    (Df_coeff_zero ha S) ?_ ?_ ?_ ?_ hid
  · -- `R` is integral
    refine vGAtLeast_sum fun r hr => ?_
    have hc : vge p (resid S W r * (p : ℚ) ^ (-((u : ℤ) - t + 1))) 0 := by
      have := vge_mul (hnear r hr) (vge_zpow_p (p := p) (-((u : ℤ) - t + 1)))
      exact vge_mono (le_of_eq (by ring)) this
    simpa using vGAtLeast_mul (vGAtLeast_C_of_vge hc) (Tn_int a (S.erase r))
  · -- `deg R < deg T`
    rcases (nearSet p a S).eq_empty_or_nonempty with hemp | hne
    · rw [hemp, Finset.sum_empty]
      rw [degree_zero]
      exact bot_lt_iff_ne_bot.2 fun h => (Tn_monic (p := p) a S).ne_zero (degree_eq_bot.1 h)
    · have ht1 : 1 ≤ t := Finset.card_pos.2 hne
      refine degree_lt_degree ?_
      rw [Tn_natDegree]
      refine lt_of_le_of_lt (natDegree_sum_le_of_forall_le _ _ (n := t - 1) fun r hr => ?_)
        (by omega)
      refine le_trans (natDegree_C_mul_le _ _) ?_
      rw [Tn_natDegree]
      show ((S.erase r).filter _).card ≤ _
      rw [Finset.filter_erase]
      exact le_of_eq (Finset.card_erase_of_mem hr)
  · -- `F` has Tate decay `f`
    refine Tate_sum fun r hr => ?_
    simpa using Tate_C_mul (hfar r hr) (Df_Tate (p := p) a (S.erase r))
  · exact vGAtLeast_comp_phi
      (vGAtLeast_divMod_of_monic (Tpoly_monic S) (Tpoly_vGAtLeast S) hWint).1 a

lemma toNat_emod_lt (r : ℤ) : (r % (p : ℤ)).toNat < p := by
  have hp0 : (0 : ℤ) < p := by exact_mod_cast hpf.out.pos
  have h1 := Int.emod_lt_of_pos r hp0
  have h2 := Int.emod_nonneg r (ne_of_gt hp0)
  omega

lemma toNat_emod_cast (r : ℤ) : (((r % (p : ℤ)).toNat : ℕ) : ℤ) = r % (p : ℤ) := by
  have hp0 : (0 : ℤ) < p := by exact_mod_cast hpf.out.pos
  exact Int.toNat_of_nonneg (Int.emod_nonneg r (ne_of_gt hp0))

/-- **The general local bound** (see the file header). -/
theorem general_bound (h7 : 7 ≤ p) (S : Finset ℤ) (W : ℚ[X]) (hWint : vGAtLeast p W 0)
    (u : ℕ → ℕ) (hW : ∀ a < p, ClassFact p a W (u a) (p + 1))
    (hS : ∀ r ∈ S, ∀ s ∈ S, r ≠ s → (p : ℤ) ∣ r - s → ¬ ((p : ℤ) ^ 2 ∣ r - s))
    (hd : ∀ r ∈ S, dIdx r < p ^ 2)
    (E : ℤ)
    (hE : ∀ a < p, E + 4 ≤ (u a : ℤ) - ((S.filter (fun r => r % (p : ℤ) = a)).card : ℤ)) :
    vGAtLeast p (tauExtOf X S W) E := by
  classical
  -- every residue satisfies `v_p(c_r) ≥ E + 5`, and the class bound `u − t + 1`
  have hres : ∀ r ∈ S, vge p (resid S W r)
      ((u (r % (p : ℤ)).toNat : ℤ)
        - ((S.filter (fun s => s % (p : ℤ) = r % (p : ℤ))).card : ℤ) + 1) := by
    intro r hr
    exact resid_vge hr (hW _ (toNat_emod_lt r)) fun s hs hsr => hS r hr s hs (Ne.symm hsr)
  have hres5 : ∀ r ∈ S, vge p (resid S W r) (E + 5) := by
    intro r hr
    refine vge_mono ?_ (hres r hr)
    have := hE _ (toNat_emod_lt (p := p) r)
    rw [toNat_emod_cast] at this
    omega
  rw [tauExtOf, tauExt]
  refine vGAtLeast_add (vGAtLeast_C_of_vge ?_) (vGAtLeast_sum fun r hr => ?_)
  · -- the polynomial part, through Raabe and the class bounds
    set P : ℚ[X] := W /ₘ Tpoly S
    have hraabe := raabe_tau p hpf.out.pos P
    have hsum : vge p (∑ a ∈ Finset.range p, tau (P.comp (C (a : ℚ) + C (p : ℚ) * X))) (E + 4) := by
      refine vge_sum fun a ha => ?_
      have hap : a < p := Finset.mem_range.1 ha
      have hb := class_tau_bound h7 S W hWint hap (hW a hap) (E + 5)
        (fun r hr => hres5 r (Finset.mem_of_mem_filter r hr))
        (fun r hr => by
          have hra : r % (p : ℤ) = a := (Finset.mem_filter.1 hr).2
          have h1 := hres r (Finset.mem_of_mem_filter r hr)
          have hta : (r % (p : ℤ)).toNat = a := by rw [hra]; simp
          rw [hta] at h1
          have hfil : S.filter (fun s => s % (p : ℤ) = r % (p : ℤ)) = nearSet p a S := by
            simp only [nearSet, hra]
          rwa [hfil] at h1)
      refine vge_mono ?_ hb
      have := hE a hap
      have hfil : (S.filter (fun r => r % (p : ℤ) = a)) = nearSet p a S := rfl
      rw [hfil] at this
      omega
    have htau : tau P = (p : ℚ) ^ (-4 : ℤ)
        * ∑ a ∈ Finset.range p, tau (P.comp (C (a : ℚ) + C (p : ℚ) * X)) := by
      rw [← hraabe, ← mul_assoc, ← zpow_natCast, ← zpow_add₀ (ne_of_gt p_pos_q)]
      norm_num
    rw [htau]
    refine vge_mono (le_of_eq (by ring)) (vge_mul (vge_zpow_p (p := p) (-4)) hsum)
  · -- the pole terms
    have hH : vGAtLeast p (C (H5 (dIdx r)) - X) (-5) := by
      refine vGAtLeast_sub (vGAtLeast_C_of_vge (vge_H5 (hd r hr))) ?_
      have hX : vGAtLeast p (X : ℚ[X]) 0 := by simpa using vGAtLeast_X_pow (p := p) 1
      exact vGAtLeast_mono (by norm_num) hX
    have := vGAtLeast_mul (vGAtLeast_C_of_vge (hres5 r hr)) hH
    refine vGAtLeast_mono (le_of_eq (by ring)) this

end General

end

end InnerEntries

end Zeta5
