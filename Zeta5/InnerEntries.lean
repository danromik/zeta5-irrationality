/-
Zeta5/InnerEntries.lean

PART 3 (ASSEMBLY) OF THE PROOF OF `Zeta5.Section3.entry_bounds_4_2_4_3` — Proposition 4.1's
proof, pp. 10–11: the basis (4.5) is `ℤ_p`-unimodular, and each entry of the Gram matrix in
that basis has valuation at least the sum of its two row weights.

* `pullback` — the pullback identity (3.1) for every rational function `A/D_tail`:
  `μ_X(A/D_tail) = τ^ext_X(W/Q)` with `W = (−1)^h x⁵ A(−x²)` and
  `Q = ∏_{N<j≤K}(x−j)(x+j)`.
* `gram_entry_bound` — `v_p^G(Bil(E_u, E_v)) ≥ min((4.3), min_c (4.2))`, from
  `InnerGeneral.general_bound` with the class counts of `W`.
* `entry_weights` — the three weight comparisons of p. 11.
* `entry_bounds` — the target, with the unimodular basis change from
  `HermiteBasis.det_coeffMatrix_unimodular`.
-/
import Zeta5.InnerGeneral
import Zeta5.OuterLocal
import Zeta5.HermiteBasis

namespace Zeta5

namespace InnerEntries

open Polynomial Finset

noncomputable section

/-! # §1.  The pullback identity (3.1) for `A/D_tail` -/

/-- The `2h` integer poles `±j`, `N < j ≤ K`, of `x⁵R(−x²)` for `R = A/D_tail`. -/
def poleSet (n : ℕ) : Finset ℤ :=
  (Ioc (N n) (K n)).image (fun j : ℕ => (j : ℤ)) ∪ (Ioc (N n) (K n)).image (fun j : ℕ => -(j : ℤ))

/-- The pullback numerator `W_A = (−1)^h x⁵ A(−x²)`. -/
def pbI (n : ℕ) (A : ℚ[X]) : ℚ[X] := C ((-1 : ℚ) ^ h n) * (X ^ 5 * A.comp (-(X ^ 2)))

lemma pbI_add (n : ℕ) (A B : ℚ[X]) : pbI n (A + B) = pbI n A + pbI n B := by
  simp only [pbI, add_comp]; ring

lemma pbI_C_mul (n : ℕ) (c : ℚ) (A : ℚ[X]) : pbI n (C c * A) = C c * pbI n A := by
  simp only [pbI, mul_comp, C_comp]; ring

lemma pbI_sum {ι : Type*} (n : ℕ) (t : Finset ι) (f : ι → ℚ[X]) :
    pbI n (∑ i ∈ t, f i) = ∑ i ∈ t, pbI n (f i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [pbI]
  | insert a t ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, pbI_add, ih]

lemma tauExtOf_zero' (Y : ℚ[X]) (s : Finset ℤ) : tauExtOf Y s 0 = 0 := by
  have := tauExtOf_C_mul Y s 0 0
  simpa using this

lemma tauExtOf_sum' {ι : Type*} (Y : ℚ[X]) (s : Finset ℤ) (t : Finset ι) (f : ι → ℚ[X]) :
    tauExtOf Y s (∑ i ∈ t, f i) = ∑ i ∈ t, tauExtOf Y s (f i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [tauExtOf_zero']
  | insert a t ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, tauExtOf_add, ih]

lemma mem_poleSet {n : ℕ} {q : ℤ} :
    q ∈ poleSet n ↔ ∃ j ∈ Ioc (N n) (K n), q = (j : ℤ) ∨ q = -(j : ℤ) := by
  simp only [poleSet, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro (⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩)
    · exact ⟨j, hj, Or.inl rfl⟩
    · exact ⟨j, hj, Or.inr rfl⟩
  · rintro ⟨j, hj, rfl | rfl⟩
    · exact Or.inl ⟨j, hj, rfl⟩
    · exact Or.inr ⟨j, hj, rfl⟩

lemma poleSet_disjoint (n : ℕ) :
    Disjoint ((Ioc (N n) (K n)).image (fun j : ℕ => (j : ℤ)))
      ((Ioc (N n) (K n)).image (fun j : ℕ => -(j : ℤ))) := by
  rw [Finset.disjoint_left]
  intro q hq1 hq2
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hq1
  obtain ⟨j', hj', hjj⟩ := Finset.mem_image.1 hq2
  simp only [Finset.mem_Ioc] at hj hj'
  omega

/-- `Q(x) = ∏_{r∈S}(x−r) = ∏_{N<j≤K}(x−j)(x+j)`. -/
lemma Tpoly_poleSet (n : ℕ) :
    Tpoly (poleSet n) = ∏ j ∈ Ioc (N n) (K n), ((X - C (j : ℚ)) * (X + C (j : ℚ))) := by
  rw [Tpoly, poleSet, Finset.prod_union (poleSet_disjoint n),
    Finset.prod_image (fun x _ y _ h => by exact_mod_cast h),
    Finset.prod_image (fun x _ y _ h => by simpa using h), ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  push_cast
  rw [map_neg, sub_neg_eq_add]

/-- **`D_tail(−x²) = (−1)^h Q(x)`**. -/
lemma Dtail_comp_neg_sq (n : ℕ) :
    (Dtail n).comp (-(X ^ 2)) = C ((-1 : ℚ) ^ h n) * Tpoly (poleSet n) := by
  rw [Tpoly_poleSet, Dtail, Polynomial.prod_comp, ← Functional.card_poles n, map_pow,
    ← Finset.prod_const, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [add_comp, X_comp, C_comp, map_pow, map_neg, map_one]
  ring

lemma sign_sq (n : ℕ) : (C ((-1 : ℚ) ^ h n) : ℚ[X]) * C ((-1 : ℚ) ^ h n) = 1 := by
  rw [← map_mul, ← mul_pow]; norm_num

/-- (3.1) on the polynomial part: `τ(x⁵P(−x²)) = μ(P)`, by linearity from `eq_3_1_mono`. -/
lemma tau_pull_eq_muPoly (P : ℚ[X]) : tau (X ^ 5 * P.comp (-(X ^ 2))) = muPoly P := by
  conv_lhs => rw [P.as_sum_support_C_mul_X_pow]
  rw [Polynomial.sum_comp, Finset.mul_sum, tau_sum, muPoly]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_pow_comp,
    show (X : ℚ[X]) ^ 5 * (C (P.coeff e) * (-(X ^ 2)) ^ e)
      = C (P.coeff e) * (X ^ 5 * (-(X ^ 2)) ^ e) by ring,
    tau_C_mul, ← eq_3_1_mono]

/-- If `Q ∣ U` then `τ_X(U/Q)` is `τ` of the quotient: all residues vanish. -/
lemma tauExtOf_mul_Tpoly (Y : ℚ[X]) (s : Finset ℤ) (U : ℚ[X]) :
    tauExtOf Y s (U * Tpoly s) = C (tau U) := by
  have hdiv : (U * Tpoly s) /ₘ Tpoly s = U := by
    rw [mul_comm]; exact Polynomial.mul_divByMonic_cancel_left U (Tpoly_monic s)
  have hmod : (U * Tpoly s) %ₘ Tpoly s = 0 := by
    rw [mul_comm]
    exact (Polynomial.modByMonic_eq_zero_iff_dvd (Tpoly_monic s)).2 ⟨U, rfl⟩
  simp [tauExtOf, tauExt, hdiv, resid, hmod]

/-- (3.1) on `A = P·D_tail`. -/
lemma pullback_poly (n : ℕ) (P : ℚ[X]) :
    tauExtOf X (poleSet n) (pbI n (P * Dtail n)) = muOver n (P * Dtail n) := by
  have hpb : pbI n (P * Dtail n) = (X ^ 5 * P.comp (-(X ^ 2))) * Tpoly (poleSet n) := by
    rw [pbI, mul_comp, Dtail_comp_neg_sq]
    linear_combination (X ^ 5 * P.comp (-(X ^ 2)) * Tpoly (poleSet n)) * sign_sq n
  rw [hpb, tauExtOf_mul_Tpoly, tau_pull_eq_muPoly, Functional.muOver_poly]

/-- (3.1) on the cofactor `A = D_tail/(t + r²)`, i.e. at the simple pole `t = −r²`. -/
lemma pullback_cof (n : ℕ) {r : ℕ} (hr : r ∈ Ioc (N n) (K n)) :
    tauExtOf X (poleSet n) (pbI n (Functional.cof n r)) = muOver n (Functional.cof n r) := by
  classical
  rw [Functional.muOver_cof n hr]
  obtain ⟨hr1, hr2⟩ := Finset.mem_Ioc.1 hr
  have hr0 : 1 ≤ r := by omega
  set s := poleSet n with hs
  have hRs : (r : ℤ) ∈ s := mem_poleSet.2 ⟨r, hr, Or.inl rfl⟩
  have hnRs : -(r : ℤ) ∈ s.erase (r : ℤ) :=
    Finset.mem_erase.2 ⟨by omega, mem_poleSet.2 ⟨r, hr, Or.inr rfl⟩⟩
  set Tr := Tpoly ((s.erase (r : ℤ)).erase (-(r : ℤ))) with hTr
  have hT : Tpoly s = (X - C (r : ℚ)) * ((X + C (r : ℚ)) * Tr) := by
    rw [Tpoly, ← Finset.mul_prod_erase s _ hRs, ← Finset.mul_prod_erase (s.erase (r : ℤ)) _ hnRs]
    push_cast
    rw [map_neg, sub_neg_eq_add]
    rfl
  have hTr_ne : ∀ x : ℤ, (x = r ∨ x = -(r : ℤ)) → Tr.eval (x : ℚ) ≠ 0 := by
    intro x hx
    rw [hTr, Tpoly, Polynomial.eval_prod]
    refine Finset.prod_ne_zero_iff.2 fun q hq => ?_
    have hq1 := Finset.ne_of_mem_erase hq
    have hq2 := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hq)
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    intro h0
    have : (x : ℚ) = (q : ℚ) := by linarith
    have hxq : x = q := by exact_mod_cast this
    rcases hx with rfl | rfl <;> omega
  have hTr_r : Tr.eval (r : ℚ) ≠ 0 := by
    have := hTr_ne (r : ℤ) (Or.inl rfl); simpa using this
  have hTr_nr : Tr.eval (-(r : ℚ)) ≠ 0 := by
    have := hTr_ne (-(r : ℤ)) (Or.inr rfl); push_cast at this; exact this
  -- the pullback numerator is `−x⁵ Tr`
  have hU : pbI n (Functional.cof n r) = -(X ^ 5 * Tr) := by
    have hcof := Functional.cof_mul n hr
    have h1 : (X + C ((r : ℚ) ^ 2)).comp (-(X ^ 2)) * (Functional.cof n r).comp (-(X ^ 2))
        = C ((-1 : ℚ) ^ h n) * Tpoly s := by
      rw [← mul_comp, hcof, Dtail_comp_neg_sq]
    have h2 : (X + C ((r : ℚ) ^ 2)).comp (-(X ^ 2)) = -((X - C (r : ℚ)) * (X + C (r : ℚ))) := by
      rw [Polynomial.add_comp, Polynomial.X_comp, Polynomial.C_comp, map_pow]; ring
    rw [h2, hT] at h1
    have hne : (X - C (r : ℚ)) * (X + C (r : ℚ)) ≠ 0 :=
      mul_ne_zero (X_sub_C_ne_zero _) (X_add_C_ne_zero _)
    have h3 : (Functional.cof n r).comp (-(X ^ 2)) = -(C ((-1 : ℚ) ^ h n) * Tr) := by
      refine mul_left_cancel₀ hne ?_
      linear_combination -h1
    rw [pbI, h3]
    linear_combination (-(X ^ 5 * Tr)) * sign_sq n
  -- polynomial division by `Q`
  set Wq : ℚ[X] := -(X ^ 3) - C ((r : ℚ) ^ 2) * X with hWq
  set Rm : ℚ[X] := C (-((r : ℚ) ^ 4)) * (X * Tr) with hRm
  have hTrm : Tr.Monic := Tpoly_monic _
  have hdegT : (Tpoly s).natDegree = Tr.natDegree + 2 := by
    rw [hT, (monic_X_sub_C _).natDegree_mul ((monic_X_add_C _).mul hTrm),
      (monic_X_add_C _).natDegree_mul hTrm, natDegree_X_sub_C, natDegree_X_add_C]
    ring
  have hdegR : Rm.natDegree ≤ Tr.natDegree + 1 := by
    refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
    refine le_trans Polynomial.natDegree_mul_le ?_
    have := Polynomial.natDegree_X_le (R := ℚ)
    omega
  have hdm := Polynomial.div_modByMonic_unique (f := pbI n (Functional.cof n r)) Wq Rm
    (Tpoly_monic s) ⟨by
      rw [hU, hT, hWq, hRm]
      simp only [map_neg, map_pow]
      ring,
      Polynomial.degree_lt_degree (by omega)⟩
  have hTd : derivative (Tpoly s)
      = (X + C (r : ℚ)) * Tr + (X - C (r : ℚ)) * (Tr + (X + C (r : ℚ)) * derivative Tr) := by
    rw [hT, derivative_mul, derivative_mul]
    simp only [derivative_sub, derivative_add, derivative_X, derivative_C]
    ring
  have hTd_r : (derivative (Tpoly s)).eval (r : ℚ) = 2 * (r : ℚ) * Tr.eval (r : ℚ) := by
    rw [hTd]; simp only [eval_add, eval_mul, eval_sub, eval_X, eval_C]; ring
  have hTd_nr : (derivative (Tpoly s)).eval (-(r : ℚ)) = -2 * (r : ℚ) * Tr.eval (-(r : ℚ)) := by
    rw [hTd]; simp only [eval_add, eval_mul, eval_sub, eval_X, eval_C]; ring
  have hrQ : (r : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hres_r : resid s (pbI n (Functional.cof n r)) (r : ℤ) = -((r : ℚ) ^ 4) / 2 := by
    rw [resid, hdm.2]
    push_cast
    rw [hTd_r, hRm]
    simp only [eval_mul, eval_C, eval_X]
    field_simp
  have hres_nr : resid s (pbI n (Functional.cof n r)) (-(r : ℤ)) = -((r : ℚ) ^ 4) / 2 := by
    rw [resid, hdm.2]
    push_cast
    rw [hTd_nr, hRm]
    simp only [eval_mul, eval_C, eval_X]
    field_simp
  have hres_other : ∀ q ∈ s, q ∉ ({(r : ℤ), -(r : ℤ)} : Finset ℤ) →
      resid s (pbI n (Functional.cof n r)) q = 0 := by
    intro q hq hq'
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hq'
    have hmem : q ∈ (s.erase (r : ℤ)).erase (-(r : ℤ)) :=
      Finset.mem_erase.2 ⟨hq'.2, Finset.mem_erase.2 ⟨hq'.1, hq⟩⟩
    rw [resid, hdm.2, hRm]
    simp only [eval_mul, eval_C, eval_X, hTr, Tpoly_eval_root hmem, mul_zero, zero_div]
  have hsub : ({(r : ℤ), -(r : ℤ)} : Finset ℤ) ⊆ s := by
    intro q hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl
    · exact hRs
    · exact Finset.mem_of_mem_erase hnRs
  have hne : (r : ℤ) ≠ -(r : ℤ) := by omega
  rw [eq_3_1_pole r hr0, tauExtOf, tauExt, tauExt, hdm.1,
    ← Finset.sum_subset hsub (fun q hq hq' => by rw [hres_other q hq hq', map_zero, zero_mul]),
    Finset.sum_pair hne, Finset.sum_pair hne, hres_r, hres_nr]

/-- **(3.1)** (p. 6), `μ_X(R) = τ_X(x⁵R(−x²))`, for every `R = A/D_tail`: the right side is
`τ_X` extended "by polynomial division and simple partial fractions", i.e. `tauExtOf X`, and
`D_tail(−x²) = (−1)^h ∏_{N<j≤K}(x−j)(x+j)`. -/
theorem pullback (n : ℕ) (A : ℚ[X]) :
    muOver n A
      = tauExtOf X (poleSet n) (C ((-1 : ℚ) ^ h n) * (X ^ 5 * A.comp (-(X ^ 2)))) := by
  change muOver n A = tauExtOf X (poleSet n) (pbI n A)
  conv_rhs => rw [Functional.partial_fractions n A]
  conv_lhs => rw [Functional.partial_fractions n A]
  rw [Functional.muOver_add, OuterLocal.muOver_sum, pbI_add, pbI_sum, tauExtOf_add,
    tauExtOf_sum', pullback_poly]
  congr 1
  refine Finset.sum_congr rfl fun r hr => ?_
  rw [pbI_C_mul, tauExtOf_C_mul, Functional.muOver_C_mul, pullback_cof n hr]

/-! # §2.  The source bounds (4.2), (4.3) and the entry exponent -/

variable {n M p : ℕ}

/-- The lower valuation that the source `c` gives for the entry `(u, v)`:
**(4.3)** `2ν_u(0) + 2ν_v(0) + 12m_N − 2m_K + 1` at `c = 0`, and
**(4.2)** `ν_u(c) + ν_v(c) + 6ℓ_N(c) − ℓ_K(c) − 4` at an ordinary `c`. -/
def srcBound (A : InnerAlloc n M p) (u v : A.Rows) (c : ℕ) : ℤ :=
  if c = 0 then
    2 * (A.nu u.1 u.2 0 : ℤ) + 2 * (A.nu v.1 v.2 0 : ℤ) + 12 * (mFloor p (N n) : ℤ)
      - 2 * (mFloor p (K n) : ℤ) + 1
  else
    (A.nu u.1 u.2 c : ℤ) + (A.nu v.1 v.2 c : ℤ) + 6 * (ell p (N n) c : ℤ)
      - (ell p (K n) c : ℤ) - 4

/-- The entry exponent: the minimum of the source bounds over all sources `0 ≤ c ≤ m`. -/
def entry (A : InnerAlloc n M p) (u v : A.Rows) : ℤ :=
  (range (mHalf p + 1)).inf' ⟨0, Finset.mem_range.2 (Nat.succ_pos _)⟩ (srcBound A u v)

/-! ### Class factorisations of the pulled-back Gram numerator -/

section Counts

variable [hpf : Fact p.Prime]

/-- `[y ≡ a (mod p)]`. -/
def indic (p a : ℕ) (y : ℤ) : ℕ := if y % (p : ℤ) = a then 1 else 0

/-- The number of the two roots `±c` of `c² − x²` that lie in the class `a`. -/
def qcount (p a : ℕ) (c : ℕ) : ℕ := indic p a (c : ℤ) + indic p a (-(c : ℤ))

lemma emod_eq_iff_dvd {a : ℕ} (ha : a < p) (x : ℤ) : x % (p : ℤ) = a ↔ (p : ℤ) ∣ x - a := by
  have haa : (a : ℤ) % (p : ℤ) = a :=
    Int.emod_eq_of_lt (Int.natCast_nonneg a) (by exact_mod_cast ha)
  rw [Int.dvd_iff_emod_eq_zero, ← Int.emod_eq_emod_iff_emod_sub_eq_zero, haa]

lemma indic_eq_dvd {a : ℕ} (ha : a < p) (y : ℤ) :
    indic p a y = if (p : ℤ) ∣ y - a then 1 else 0 := by
  unfold indic
  by_cases h : (p : ℤ) ∣ y - a
  · rw [if_pos h, if_pos ((emod_eq_iff_dvd ha y).2 h)]
  · rw [if_neg h, if_neg fun h' => h ((emod_eq_iff_dvd ha y).1 h')]

lemma CF_congr {a : ℕ} {W : ℚ[X]} {u d u' d' : ℕ} (h : ClassFact p a W u d) (hu : u = u')
    (hd : d = d') : ClassFact p a W u' d' := by
  subst hu; subst hd; exact h

lemma CF_mono {a : ℕ} {W : ℚ[X]} {u d d' : ℕ} (h : ClassFact p a W u d) (hd : d ≤ d') :
    ClassFact p a W u d' := by
  obtain ⟨U, Nf, e, hU, hdeg, hN⟩ := h
  exact ⟨U, Nf, e, hU, le_trans hdeg hd, hN⟩

lemma CF_one (a : ℕ) : ClassFact p a 1 0 0 :=
  ⟨1, 1, by simp, vGAtLeast_one, by simp, Tate_one⟩

lemma CF_C (a : ℕ) {c : ℚ} (hc : vge p c 0) : ClassFact p a (C c) 0 0 :=
  ⟨C c, 1, by simp, vGAtLeast_C_of_vge hc, by simp, Tate_one⟩

lemma CF_mul {a : ℕ} {W1 W2 : ℚ[X]} {u1 d1 u2 d2 : ℕ} (h1 : ClassFact p a W1 u1 d1)
    (h2 : ClassFact p a W2 u2 d2) : ClassFact p a (W1 * W2) (u1 + u2) (d1 + d2) := by
  obtain ⟨U1, N1, e1, hU1, hd1, hN1⟩ := h1
  obtain ⟨U2, N2, e2, hU2, hd2, hN2⟩ := h2
  refine ⟨U1 * U2, N1 * N2, ?_, by simpa using vGAtLeast_mul hU1 hU2,
    le_trans natDegree_mul_le (add_le_add hd1 hd2), by simpa using Tate_mul hN1 hN2⟩
  rw [mul_comp, e1, e2, pow_add, C_mul]
  ring

lemma CF_pow {a : ℕ} {W : ℚ[X]} {u d : ℕ} (h : ClassFact p a W u d) (k : ℕ) :
    ClassFact p a (W ^ k) (k * u) (k * d) := by
  induction k with
  | zero => simpa using CF_one (p := p) a
  | succ k ih =>
    rw [pow_succ]
    exact CF_congr (CF_mul ih h) (by ring) (by ring)

lemma CF_prod {ι : Type*} [DecidableEq ι] {a : ℕ} (s : Finset ι) (f : ι → ℚ[X])
    (u d : ι → ℕ) (h : ∀ i ∈ s, ClassFact p a (f i) (u i) (d i)) :
    ClassFact p a (∏ i ∈ s, f i) (∑ i ∈ s, u i) (∑ i ∈ s, d i) := by
  induction s using Finset.induction_on with
  | empty => simpa using CF_one (p := p) a
  | insert b s hb ih =>
    rw [Finset.prod_insert hb, Finset.sum_insert hb, Finset.sum_insert hb]
    exact CF_mul (h b (Finset.mem_insert_self b s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- A linear factor `x − y`: near (`u = 1`, `U = z − ⌊y/p⌋`) or far (`u = 0`, `N_f = (a−y)+pz`). -/
lemma CF_X_sub_C {a : ℕ} (ha : a < p) (y : ℤ) :
    ClassFact p a (X - C (y : ℚ)) (indic p a y) (indic p a y) := by
  unfold indic
  split_ifs with hy
  · refine ⟨X - C (((y / (p : ℤ) : ℤ)) : ℚ), 1, ?_, vGAtLeast_X_sub_intC _,
      by rw [natDegree_X_sub_C], Tate_one⟩
    have := comp_X_sub_C_phi_near (p := p) ha hy
    simp only [phi] at this
    rw [this]
    simp
  · refine ⟨1, C ((a : ℚ) - (y : ℚ)) + C (p : ℚ) * X, ?_, vGAtLeast_one, by simp, Tate_lin ?_⟩
    · have := comp_X_sub_C_phi (p := p) a y
      simp only [phi] at this
      rw [this]
      simp
    · have : ((a : ℚ) - (y : ℚ)) = (((a : ℤ) - y : ℤ) : ℚ) := by push_cast; ring
      rw [this]
      exact vge_intCast _

lemma vge_neg_one_pow (k : ℕ) : vge p ((-1 : ℚ) ^ k) 0 := by
  have := vge_intCast (p := p) ((-1 : ℤ) ^ k)
  simpa using this

/-- `c² − x² = −(x − c)(x + c)`. -/
lemma quad_eq (c : ℕ) :
    (X + C ((c : ℚ) ^ 2)).comp (-(X ^ 2))
      = C (-1 : ℚ) * ((X - C (((c : ℤ)) : ℚ)) * (X - C (((-(c : ℤ)) : ℤ) : ℚ))) := by
  rw [add_comp, X_comp, C_comp]
  simp only [Int.cast_neg, Int.cast_natCast, map_neg, map_pow, map_one]
  ring

lemma CF_quad {a : ℕ} (ha : a < p) (c : ℕ) :
    ClassFact p a ((X + C ((c : ℚ) ^ 2)).comp (-(X ^ 2))) (qcount p a c) (qcount p a c) := by
  rw [quad_eq]
  have h1 : vge p (-1 : ℚ) 0 := by simpa using vge_neg_one_pow (p := p) 1
  exact CF_congr (CF_mul (CF_C a h1) (CF_mul (CF_X_sub_C ha (c : ℤ)) (CF_X_sub_C ha (-(c : ℤ)))))
    (by simp [qcount]) (by simp [qcount])

lemma quad_int (c : ℕ) : vGAtLeast p ((X + C ((c : ℚ) ^ 2)).comp (-(X ^ 2))) 0 := by
  rw [quad_eq]
  have h1 : vge p (-1 : ℚ) 0 := by simpa using vge_neg_one_pow (p := p) 1
  have := vGAtLeast_mul (vGAtLeast_C_of_vge h1)
    (vGAtLeast_mul (vGAtLeast_X_sub_intC (p := p) (c : ℤ)) (vGAtLeast_X_sub_intC (p := p) (-(c : ℤ))))
  simpa using this

lemma vGAtLeast_pow' {W : ℚ[X]} (h : vGAtLeast p W 0) (k : ℕ) : vGAtLeast p (W ^ k) 0 := by
  induction k with
  | zero => simpa using vGAtLeast_one (p := p)
  | succ k ih => simpa [pow_succ] using vGAtLeast_mul ih h

lemma vGAtLeast_prod' {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℚ[X])
    (h : ∀ i ∈ s, vGAtLeast p (f i) 0) : vGAtLeast p (∏ i ∈ s, f i) 0 := by
  have := vGAtLeast_prod (p := p) s f (fun _ => 0) h
  simpa using this

/-- `E_{a,i} = ∏_{0≤c≤m}(t + c²)^{ν_i(c)}`. -/
lemma rowPoly_eq_prod (A : InnerAlloc n M p) {a : ℕ} (ha : a ≤ mHalf p) (i : ℕ) :
    A.rowPoly a i = ∏ c ∈ range (mHalf p + 1), (X + C ((c : ℚ) ^ 2)) ^ (A.nu a i c) := by
  have hmem : a ∈ range (mHalf p + 1) := Finset.mem_range.2 (by omega)
  rw [InnerAlloc.rowPoly, ← Finset.prod_erase_mul _ _ hmem]
  congr 1
  · refine Finset.prod_congr rfl fun c hc => ?_
    rw [InnerAlloc.nu, if_neg (Finset.ne_of_mem_erase hc)]
  · rw [InnerAlloc.nu, if_pos rfl]

/-- `E(−x²) = ∏_c (c² − x²)^{ν(c)}`. -/
lemma rowPoly_comp (A : InnerAlloc n M p) {a : ℕ} (ha : a ≤ mHalf p) (i : ℕ) :
    (A.rowPoly a i).comp (-(X ^ 2))
      = ∏ c ∈ range (mHalf p + 1), ((X + C ((c : ℚ) ^ 2)).comp (-(X ^ 2))) ^ (A.nu a i c) := by
  rw [rowPoly_eq_prod A ha, Polynomial.prod_comp]
  exact Finset.prod_congr rfl fun c _ => by rw [pow_comp]

lemma D_comp (m : ℕ) :
    (D m).comp (-(X ^ 2)) = ∏ j ∈ Icc 1 m, (X + C ((j : ℚ) ^ 2)).comp (-(X ^ 2)) := by
  rw [D, Polynomial.prod_comp]

/-- The pulled-back Gram numerator `W = (−1)^h x⁵ D_N(−x²)⁵ E_u(−x²) E_v(−x²)`, as a product
of the factors whose class counts are known. -/
lemma gramNum_eq (A : InnerAlloc n M p) (u v : A.Rows) :
    pbI n (D (N n) ^ 5 * (A.rowPoly u.1 u.2 * A.rowPoly v.1 v.2))
      = C ((-1 : ℚ) ^ h n) * (X ^ 5
          * ((∏ j ∈ Icc 1 (N n), (X + C ((j : ℚ) ^ 2)).comp (-(X ^ 2))) ^ 5
            * ((∏ c ∈ range (mHalf p + 1),
                  ((X + C ((c : ℚ) ^ 2)).comp (-(X ^ 2))) ^ (A.nu u.1 u.2 c))
              * ∏ c ∈ range (mHalf p + 1),
                  ((X + C ((c : ℚ) ^ 2)).comp (-(X ^ 2))) ^ (A.nu v.1 v.2 c)))) := by
  have hu : (u.1 : ℕ) ≤ mHalf p := by have := u.1.isLt; omega
  have hv : (v.1 : ℕ) ≤ mHalf p := by have := v.1.isLt; omega
  rw [pbI, mul_comp, mul_comp, pow_comp, D_comp, rowPoly_comp A hu, rowPoly_comp A hv]

/-- The class count of the numerator at the class `a`. -/
def uW (A : InnerAlloc n M p) (u v : A.Rows) (a : ℕ) : ℕ :=
  5 * indic p a 0 + (5 * ∑ j ∈ Icc 1 (N n), qcount p a j
    + (∑ c ∈ range (mHalf p + 1), A.nu u.1 u.2 c * qcount p a c
      + ∑ c ∈ range (mHalf p + 1), A.nu v.1 v.2 c * qcount p a c))

lemma CF_gramNum (A : InnerAlloc n M p) (u v : A.Rows) {a : ℕ} (ha : a < p) :
    ClassFact p a (pbI n (D (N n) ^ 5 * (A.rowPoly u.1 u.2 * A.rowPoly v.1 v.2)))
      (uW A u v a) (uW A u v a) := by
  classical
  rw [gramNum_eq]
  have hq : ∀ c : ℕ, ClassFact p a ((X + C ((c : ℚ) ^ 2)).comp (-(X ^ 2)))
      (qcount p a c) (qcount p a c) := fun c => CF_quad ha c
  have hD := CF_pow (CF_prod (Icc 1 (N n)) _ _ _ fun j _ => hq j) 5
  have hEu := CF_prod (range (mHalf p + 1)) _ _ _ fun c _ => CF_pow (hq c) (A.nu u.1 u.2 c)
  have hEv := CF_prod (range (mHalf p + 1)) _ _ _ fun c _ => CF_pow (hq c) (A.nu v.1 v.2 c)
  have hX : ClassFact p a (X ^ 5) (5 * indic p a 0) (5 * indic p a 0) := by
    have := CF_pow (CF_X_sub_C (p := p) ha 0) 5
    simpa using this
  have hs := CF_C (p := p) a (vge_neg_one_pow (p := p) (h n))
  exact CF_congr (CF_mul hs (CF_mul hX (CF_mul hD (CF_mul hEu hEv)))) (by simp [uW])
    (by simp [uW])

lemma gramNum_int (A : InnerAlloc n M p) (u v : A.Rows) :
    vGAtLeast p (pbI n (D (N n) ^ 5 * (A.rowPoly u.1 u.2 * A.rowPoly v.1 v.2))) 0 := by
  classical
  rw [gramNum_eq]
  have hq : ∀ c : ℕ, vGAtLeast p ((X + C ((c : ℚ) ^ 2)).comp (-(X ^ 2))) 0 := fun c => quad_int c
  have hs : vGAtLeast p (C ((-1 : ℚ) ^ h n)) 0 := vGAtLeast_C_of_vge (vge_neg_one_pow _)
  have hX : vGAtLeast p ((X : ℚ[X]) ^ 5) 0 := vGAtLeast_X_pow 5
  have hD := vGAtLeast_pow' (vGAtLeast_prod' (Icc 1 (N n)) _ fun j _ => hq j) 5
  have hEu := vGAtLeast_prod' (range (mHalf p + 1)) _ fun c _ => vGAtLeast_pow' (hq c)
    (A.nu u.1 u.2 c)
  have hEv := vGAtLeast_prod' (range (mHalf p + 1)) _ fun c _ => vGAtLeast_pow' (hq c)
    (A.nu v.1 v.2 c)
  have := vGAtLeast_mul hs (vGAtLeast_mul hX (vGAtLeast_mul hD (vGAtLeast_mul hEu hEv)))
  simpa only [add_zero] using this

/-! ### Counting: the class counts are the paper's `ℓ_A(a)` and `m_A` -/

/-- An integer multiple of `p` strictly between `−p` and `p` is `0`. -/
lemma eq_zero_of_dvd_of_lt {x : ℤ} (h : (p : ℤ) ∣ x) (h1 : -(p : ℤ) < x) (h2 : x < p) :
    x = 0 := by
  obtain ⟨k, rfl⟩ := h
  have hp : (0 : ℤ) < p := by exact_mod_cast hpf.out.pos
  rcases lt_trichotomy k 0 with hk | hk | hk
  · have : (p : ℤ) * k ≤ -(p : ℤ) := by nlinarith
    omega
  · simp [hk]
  · have : (p : ℤ) ≤ (p : ℤ) * k := by nlinarith
    omega

/-- `Σ_{j=1}^{A} #{roots ±j in class 0} = 2⌊A/p⌋`. -/
lemma sum_qcount_zero (A' : ℕ) : ∑ j ∈ Icc 1 A', qcount p 0 j = 2 * (A' / p) := by
  classical
  have hp0 : 0 < p := hpf.out.pos
  have hq : ∀ j : ℕ, qcount p 0 j = 2 * (if p ∣ j then 1 else 0) := by
    intro j
    unfold qcount
    rw [indic_eq_dvd hp0, indic_eq_dvd hp0]
    have e1 : ((p : ℤ) ∣ (j : ℤ) - ((0 : ℕ) : ℤ)) ↔ p ∣ j := by
      simp [Int.natCast_dvd_natCast]
    have e2 : ((p : ℤ) ∣ -(j : ℤ) - ((0 : ℕ) : ℤ)) ↔ p ∣ j := by
      simp [dvd_neg, Int.natCast_dvd_natCast]
    by_cases hj : p ∣ j
    · rw [if_pos (e1.2 hj), if_pos (e2.2 hj), if_pos hj]
    · rw [if_neg (fun h => hj (e1.1 h)), if_neg (fun h => hj (e2.1 h)), if_neg hj]
  rw [Finset.sum_congr rfl fun j _ => hq j, ← Finset.mul_sum, ← Finset.card_filter]
  congr 1
  have : Icc 1 A' = Ioc 0 A' := by ext x; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  rw [this, Nat.Ioc_filter_dvd_card_eq_div]

/-- `Σ_{j=1}^{A} #{roots ±j in class a} = ℓ_A(a)` for an ordinary class `1 ≤ a < p`. -/
lemma sum_qcount_eq_ell (h7 : 7 ≤ p) {a : ℕ} (ha1 : 1 ≤ a) (ha : a < p) (A' : ℕ) :
    ∑ j ∈ Icc 1 A', qcount p a j = ell p A' a := by
  classical
  unfold ell
  rw [Finset.card_filter]
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold qcount
  rw [indic_eq_dvd ha, indic_eq_dvd ha]
  have e1 : (p : ℤ) ∣ (j : ℤ) - a ↔ j % p = a % p := by
    rw [← Nat.ModEq, Nat.modEq_iff_dvd, ← dvd_neg, neg_sub]
  have e2 : (p : ℤ) ∣ -(j : ℤ) - a ↔ (j + a) % p = 0 := by
    rw [← Nat.dvd_iff_mod_eq_zero, ← Int.natCast_dvd_natCast,
      show -(j : ℤ) - a = -((j + a : ℕ) : ℤ) by push_cast; ring, dvd_neg]
  have hdis : ¬ ((p : ℤ) ∣ (j : ℤ) - a ∧ (p : ℤ) ∣ -(j : ℤ) - a) := by
    rintro ⟨h1, h2⟩
    have h3 : (p : ℤ) ∣ 2 * (a : ℤ) := by
      have := dvd_add h1 h2
      have h4 : (j : ℤ) - a + (-(j : ℤ) - a) = -(2 * (a : ℤ)) := by ring
      rw [h4, dvd_neg] at this
      exact this
    rcases (Nat.prime_iff_prime_int.1 hpf.out).dvd_or_dvd h3 with h5 | h5
    · have := Int.le_of_dvd (by norm_num) h5
      omega
    · have h6 : p ∣ a := Int.natCast_dvd_natCast.1 h5
      have := Nat.le_of_dvd (by omega) h6
      omega
  by_cases h1 : (p : ℤ) ∣ (j : ℤ) - a
  · have h2 : ¬ (p : ℤ) ∣ -(j : ℤ) - a := fun h2 => hdis ⟨h1, h2⟩
    rw [if_pos h1, if_neg h2, if_pos (Or.inl (e1.1 h1))]
  · by_cases h2 : (p : ℤ) ∣ -(j : ℤ) - a
    · rw [if_neg h1, if_pos h2, if_pos (Or.inr (e2.1 h2))]
    · rw [if_neg h1, if_neg h2, if_neg]
      rintro (h | h)
      · exact h1 (e1.2 h)
      · exact h2 (e2.2 h)

/-- The classes `a` and `p − a` see the same roots `±c`, swapped. -/
lemma qcount_symm {a : ℕ} (ha1 : 1 ≤ a) (ha : a < p) (c : ℕ) :
    qcount p (p - a) c = qcount p a c := by
  have hpa : p - a < p := by omega
  unfold qcount
  rw [indic_eq_dvd hpa, indic_eq_dvd hpa, indic_eq_dvd ha, indic_eq_dvd ha]
  have hc : ((p - a : ℕ) : ℤ) = (p : ℤ) - a := by
    rw [Nat.cast_sub (le_of_lt ha)]
  have e1 : (p : ℤ) ∣ (c : ℤ) - ((p - a : ℕ) : ℤ) ↔ (p : ℤ) ∣ -(c : ℤ) - a := by
    rw [hc, show (c : ℤ) - ((p : ℤ) - a) = ((c : ℤ) + a) - p by ring, dvd_sub_self_right,
      show -(c : ℤ) - a = -((c : ℤ) + a) by ring, dvd_neg]
  have e2 : (p : ℤ) ∣ -(c : ℤ) - ((p - a : ℕ) : ℤ) ↔ (p : ℤ) ∣ (c : ℤ) - a := by
    rw [hc, show -(c : ℤ) - ((p : ℤ) - a) = -((c : ℤ) - a) - p by ring, dvd_sub_self_right,
      dvd_neg]
  by_cases h1 : (p : ℤ) ∣ -(c : ℤ) - a <;> by_cases h2 : (p : ℤ) ∣ (c : ℤ) - a <;>
    simp [h1, h2, e1, e2] <;> omega

/-- The roots `±c`, `0 ≤ c ≤ m`, in the class `a ∈ [1, m]`: only `c = a`. -/
lemma qcount_low {a c : ℕ} (hodd : 2 * mHalf p + 1 = p) (ha1 : 1 ≤ a) (ham : a ≤ mHalf p)
    (hc : c ≤ mHalf p) : qcount p a c = if c = a then 1 else 0 := by
  have ha : a < p := by omega
  unfold qcount
  rw [indic_eq_dvd ha, indic_eq_dvd ha]
  have h2 : ¬ (p : ℤ) ∣ -(c : ℤ) - a := by
    intro h
    have := eq_zero_of_dvd_of_lt h (by omega) (by omega)
    omega
  rw [if_neg h2, add_zero]
  by_cases hca : c = a
  · rw [if_pos (by rw [hca]; simp), if_pos hca]
  · rw [if_neg, if_neg hca]
    intro h
    have := eq_zero_of_dvd_of_lt h (by omega) (by omega)
    omega

/-- The roots `±c`, `0 ≤ c ≤ m`, in the class `0`: only `c = 0`, twice. -/
lemma qcount_zero {c : ℕ} (hodd : 2 * mHalf p + 1 = p) (hc : c ≤ mHalf p) :
    qcount p 0 c = if c = 0 then 2 else 0 := by
  have hp0 : 0 < p := by omega
  unfold qcount
  rw [indic_eq_dvd hp0, indic_eq_dvd hp0]
  by_cases hc0 : c = 0
  · subst hc0; simp
  · have h1 : ¬ (p : ℤ) ∣ (c : ℤ) - ((0 : ℕ) : ℤ) := by
      intro h
      have := eq_zero_of_dvd_of_lt h (by omega) (by omega)
      omega
    have h2 : ¬ (p : ℤ) ∣ -(c : ℤ) - ((0 : ℕ) : ℤ) := by
      intro h
      have := eq_zero_of_dvd_of_lt h (by omega) (by omega)
      omega
    rw [if_neg h1, if_neg h2, if_neg hc0]

lemma sum_nu_qcount_low (hodd : 2 * mHalf p + 1 = p) (f : ℕ → ℕ) {a : ℕ} (ha1 : 1 ≤ a)
    (ham : a ≤ mHalf p) : ∑ c ∈ range (mHalf p + 1), f c * qcount p a c = f a := by
  rw [Finset.sum_eq_single a]
  · rw [qcount_low hodd ha1 ham ham, if_pos rfl, mul_one]
  · intro c hc hca
    rw [qcount_low hodd ha1 ham (by simp only [Finset.mem_range] at hc; omega), if_neg hca,
      mul_zero]
  · intro h; exact absurd (Finset.mem_range.2 (by omega)) h

lemma sum_nu_qcount_zero (hodd : 2 * mHalf p + 1 = p) (f : ℕ → ℕ) :
    ∑ c ∈ range (mHalf p + 1), f c * qcount p 0 c = 2 * f 0 := by
  rw [Finset.sum_eq_single 0]
  · rw [qcount_zero hodd (Nat.zero_le _), if_pos rfl]; ring
  · intro c hc hc0
    rw [qcount_zero hodd (by simp only [Finset.mem_range] at hc; omega), if_neg hc0, mul_zero]
  · intro h; exact absurd (Finset.mem_range.2 (Nat.succ_pos _)) h

lemma indic_zero_self : indic p 0 0 = 1 := by simp [indic]

lemma indic_zero_of_pos {a : ℕ} (ha1 : 1 ≤ a) : indic p a 0 = 0 := by
  unfold indic
  rw [if_neg]
  simp only [Int.zero_emod]
  omega

/-- The poles `±j`, `N < j ≤ K`, in the class `a`. -/
lemma card_poleSet_filter (a : ℕ) :
    ((poleSet n).filter (fun r => r % (p : ℤ) = a)).card
      = ∑ j ∈ Ioc (N n) (K n), qcount p a j := by
  classical
  rw [poleSet, Finset.filter_union,
    Finset.card_union_of_disjoint (Finset.disjoint_filter_filter (poleSet_disjoint n)),
    Finset.filter_image, Finset.filter_image,
    Finset.card_image_of_injective _ (fun x y h => by exact_mod_cast h),
    Finset.card_image_of_injective _ (fun x y h => by simpa using h),
    Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
  rfl

lemma sum_Icc_split {N' K' : ℕ} (hNK : N' ≤ K') (g : ℕ → ℕ) :
    ∑ j ∈ Icc 1 K', g j = ∑ j ∈ Icc 1 N', g j + ∑ j ∈ Ioc N' K', g j := by
  classical
  rw [← Finset.sum_union]
  · congr 1
    ext x
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]
    omega
  · rw [Finset.disjoint_left]
    intro x h1 h2
    simp only [Finset.mem_Icc, Finset.mem_Ioc] at h1 h2
    omega

lemma N_le_K (n : ℕ) : N n ≤ K n := by simp only [N, K]; omega

/-! ### The exponent at every class, and the degree condition -/

variable {n M : ℕ}

lemma uW_zero (hodd : 2 * mHalf p + 1 = p) (A : InnerAlloc n M p) (u v : A.Rows) :
    uW A u v 0 = 5 + (5 * (2 * (N n / p)) + (2 * A.nu u.1 u.2 0 + 2 * A.nu v.1 v.2 0)) := by
  rw [uW, indic_zero_self, sum_qcount_zero, sum_nu_qcount_zero hodd, sum_nu_qcount_zero hodd]

lemma uW_low (h7 : 7 ≤ p) (hodd : 2 * mHalf p + 1 = p) (A : InnerAlloc n M p) (u v : A.Rows)
    {a : ℕ} (ha1 : 1 ≤ a) (ham : a ≤ mHalf p) :
    uW A u v a = 5 * ell p (N n) a + (A.nu u.1 u.2 a + A.nu v.1 v.2 a) := by
  rw [uW, indic_zero_of_pos ha1, sum_qcount_eq_ell h7 ha1 (by omega),
    sum_nu_qcount_low hodd (fun c => A.nu u.1 u.2 c) ha1 ham,
    sum_nu_qcount_low hodd (fun c => A.nu v.1 v.2 c) ha1 ham]
  ring

lemma uW_symm (A : InnerAlloc n M p) (u v : A.Rows) {a : ℕ} (ha1 : 1 ≤ a) (ha : a < p) :
    uW A u v (p - a) = uW A u v a := by
  have hpa1 : 1 ≤ p - a := by omega
  unfold uW
  rw [indic_zero_of_pos ha1, indic_zero_of_pos hpa1]
  simp only [qcount_symm ha1 ha]

lemma tcount_symm {a : ℕ} (ha1 : 1 ≤ a) (ha : a < p) :
    ((poleSet n).filter (fun r => r % (p : ℤ) = (p - a : ℕ))).card
      = ((poleSet n).filter (fun r => r % (p : ℤ) = a)).card := by
  rw [card_poleSet_filter, card_poleSet_filter]
  simp only [qcount_symm ha1 ha]

lemma tcount_zero :
    2 * (K n / p) = 2 * (N n / p) + ((poleSet n).filter (fun r => r % (p : ℤ) = (0 : ℕ))).card := by
  rw [card_poleSet_filter, ← sum_qcount_zero, ← sum_qcount_zero]
  exact sum_Icc_split (N_le_K n) _

lemma tcount_low (h7 : 7 ≤ p) {a : ℕ} (ha1 : 1 ≤ a) (ha : a < p) :
    ell p (K n) a = ell p (N n) a + ((poleSet n).filter (fun r => r % (p : ℤ) = a)).card := by
  rw [card_poleSet_filter, ← sum_qcount_eq_ell h7 ha1 ha, ← sum_qcount_eq_ell h7 ha1 ha]
  exact sum_Icc_split (N_le_K n) _

/-- The exponent `min_a(u_a − t_a) − 4` dominates the entry exponent at every class. -/
theorem entry_le_class (hp : IsInnerPrime n M p) (A : InnerAlloc n M p) (u v : A.Rows)
    {a : ℕ} (ha : a < p) :
    entry A u v + 4
      ≤ (uW A u v a : ℤ) - (((poleSet n).filter (fun r => r % (p : ℤ) = a)).card : ℤ) := by
  have h7 : 7 ≤ p := by have := hp.gt_200M; have := hp.cutoff; omega
  have hodd : 2 * mHalf p + 1 = p := hp.two_mHalf
  -- the ordinary case, for a class `c ∈ [1, m]`
  have hlow : ∀ c : ℕ, 1 ≤ c → c ≤ mHalf p →
      entry A u v + 4
        ≤ (uW A u v c : ℤ) - (((poleSet n).filter (fun r => r % (p : ℤ) = c)).card : ℤ) := by
    intro c hc1 hcm
    have hle : entry A u v ≤ srcBound A u v c :=
      Finset.inf'_le _ (Finset.mem_range.2 (by omega))
    have ht := tcount_low (n := n) h7 hc1 (by omega : c < p)
    rw [uW_low h7 hodd A u v hc1 hcm]
    unfold srcBound at hle
    rw [if_neg (by omega)] at hle
    push_cast
    have htZ : (ell p (K n) c : ℤ) = (ell p (N n) c : ℤ)
        + (((poleSet n).filter (fun r => r % (p : ℤ) = c)).card : ℤ) := by exact_mod_cast ht
    linarith
  rcases Nat.eq_zero_or_pos a with rfl | ha1
  · have hle : entry A u v ≤ srcBound A u v 0 :=
      Finset.inf'_le _ (Finset.mem_range.2 (Nat.succ_pos _))
    unfold srcBound at hle
    rw [if_pos rfl] at hle
    rw [uW_zero hodd A u v]
    have ht := tcount_zero (n := n) (p := p)
    simp only [mFloor] at hle
    generalize K n / p = mK at ht hle
    generalize N n / p = mN at ht hle ⊢
    generalize ((poleSet n).filter (fun r => r % (p : ℤ) = ((0 : ℕ) : ℤ))).card = t at ht ⊢
    have htZ : 2 * (mK : ℤ) = 2 * (mN : ℤ) + (t : ℤ) := by exact_mod_cast ht
    push_cast
    linarith
  · by_cases ham : a ≤ mHalf p
    · exact hlow a ha1 ham
    · have hc1 : 1 ≤ p - a := by omega
      have hcm : p - a ≤ mHalf p := by omega
      have h := hlow (p - a) hc1 hcm
      rw [uW_symm A u v ha1 ha, tcount_symm ha1 ha] at h
      exact h

/-- **"Both degrees are at most `p + 1`"** (p. 11), for the class counts of the numerator. -/
theorem uW_le (hp : IsInnerPrime n M p) (A : InnerAlloc n M p) (u v : A.Rows) {a : ℕ}
    (ha : a < p) : uW A u v a ≤ p + 1 := by
  have h7 : 7 ≤ p := by have := hp.gt_200M; have := hp.cutoff; omega
  have hodd : 2 * mHalf p + 1 = p := hp.two_mHalf
  have hiu : (u.2 : ℕ) < A.Ldim u.1 := u.2.isLt
  have hiv : (v.2 : ℕ) < A.Ldim v.1 := v.2.isLt
  have hlow : ∀ c : ℕ, 1 ≤ c → c ≤ mHalf p → uW A u v c ≤ p + 1 := by
    intro c hc1 hcm
    rw [uW_low h7 hodd A u v hc1 hcm]
    have h1 := degree_bound_ordinary hp A hiu hiv hc1 hcm
    have h2 := two_T_add_one_lt hp A
    have h3 := (degrees_le_p_add_one (n := n) (M := M) (p := p) hp).1
    have h4 : (2 * ((A.T : ℚ) + 1)) < (p : ℚ) + 1 := lt_of_lt_of_le h2 h3
    have h5 : 2 * (A.T + 1) < (p : ℤ) + 1 := by exact_mod_cast h4
    have : ((5 * ell p (N n) c + (A.nu u.1 u.2 c + A.nu v.1 v.2 c) : ℕ) : ℤ) ≤ (p : ℤ) + 1 := by
      push_cast
      have : (0 : ℤ) ≤ (ell p (N n) c : ℤ) := Int.natCast_nonneg _
      linarith
    exact_mod_cast this
  rcases Nat.eq_zero_or_pos a with rfl | ha1
  · rw [uW_zero hodd A u v]
    have h1 := degree_bound_zero A hiu hiv
    have h2 := zero_degree_le (n := n) (M := M) (p := p) hp
    have h3 := (degrees_le_p_add_one (n := n) (M := M) (p := p) hp).2
    have h4 : ((5 + 4 * L0 M + 12 * mFloor p (N n) : ℕ) : ℚ) ≤ (p : ℚ) + 1 := le_trans h2 h3
    have h5 : 5 + 4 * L0 M + 12 * mFloor p (N n) ≤ p + 1 := by exact_mod_cast h4
    simp only [mFloor] at h1 h5
    omega
  · by_cases ham : a ≤ mHalf p
    · exact hlow a ha1 ham
    · have h := hlow (p - a) (by omega) (by omega)
      rwa [uW_symm A u v ha1 ha] at h

/-- `K < p²`: the inner range has `K < pM` and `200M < p`. -/
lemma K_lt_sq (hp : IsInnerPrime n M p) : 2 * K n < p ^ 2 := by
  have h1 := hp.lower
  have h2 := hp.gt_200M
  nlinarith

lemma poleSet_abs {q : ℤ} (hq : q ∈ poleSet n) : |q| ≤ K n := by
  obtain ⟨j, hj, rfl | rfl⟩ := mem_poleSet.1 hq <;> simp only [Finset.mem_Ioc] at hj <;>
    simp [abs_of_nonneg, hj.2]

/-- Distinct poles in the same class differ by `p` times a unit: `|r − s| ≤ 2K < p²`. -/
lemma poleSet_sep (hp : IsInnerPrime n M p) :
    ∀ r ∈ poleSet n, ∀ s ∈ poleSet n, r ≠ s → (p : ℤ) ∣ r - s → ¬ ((p : ℤ) ^ 2 ∣ r - s) := by
  intro r hr s hs hrs _ hsq
  have h1 := poleSet_abs hr
  have h2 := poleSet_abs hs
  have hK := K_lt_sq hp
  have hne : r - s ≠ 0 := sub_ne_zero.2 hrs
  have hle := Int.le_of_dvd (abs_pos.2 hne) ((dvd_abs _ _).2 hsq)
  have habs : |r - s| ≤ 2 * (K n : ℤ) := by
    have := abs_sub r s
    linarith
  have hKZ : 2 * (K n : ℤ) < (p : ℤ) ^ 2 := by exact_mod_cast hK
  linarith

/-- The harmonic indices of the poles are `< p²` (so `v_p(H^{(5)}_{d(r)}) ≥ −5`). -/
lemma poleSet_dIdx (hp : IsInnerPrime n M p) : ∀ r ∈ poleSet n, dIdx r < p ^ 2 := by
  intro r hr
  have h1 := abs_le.1 (poleSet_abs hr)
  have hK := K_lt_sq hp
  have hKZ : 2 * (K n : ℤ) < ((p ^ 2 : ℕ) : ℤ) := by exact_mod_cast hK
  unfold dIdx
  split_ifs <;> omega

end Counts

/-- **(4.2) and (4.3) for the entire summands** (p. 11): the Gram entry of the basis (4.5)
has Gauss valuation at least the entry exponent.

`Bil(E_u, E_v) = μ_X(D_N⁵E_uE_v/D_tail) = τ^ext_X(W/Q)` by the pullback (3.1); the general
local bound applies with the class counts `uW` of `W` (`CF_gramNum`), which are
`≤ p + 1` (`uW_le`), and the exponent `min_a(u_a − t_a) − 4` dominates
`min((4.3), min_c (4.2))` at every class (`entry_le_class`). -/
theorem gram_entry_bound (hp : IsInnerPrime n M p) (A : InnerAlloc n M p) (u v : A.Rows) :
    vGAtLeast p (OuterLocal.Bil n (A.rowPoly u.1 u.2) (A.rowPoly v.1 v.2)) (entry A u v) := by
  haveI : Fact p.Prime := ⟨hp.prime⟩
  have h7 : 7 ≤ p := by have := hp.gt_200M; have := hp.cutoff; omega
  rw [OuterLocal.Bil, pullback]
  exact general_bound h7 (poleSet n) (pbI n (D (N n) ^ 5 * (A.rowPoly u.1 u.2 * A.rowPoly v.1 v.2)))
    (gramNum_int A u v) (uW A u v)
    (fun a ha => CF_mono (CF_gramNum A u v ha) (uW_le hp A u v ha))
    (poleSet_sep hp) (poleSet_dIdx hp) (entry A u v) (fun a ha => entry_le_class hp A u v ha)

/-- The half of the source bound `srcBound` that belongs to one row: at `c = 0`,
`2ν(0) + 6m_N − m_K + 1/2`, and at an ordinary `c`, `ν(c) + b_c − (ℓ_K(c)+4)/2` — doubled. -/
def halfB (A : InnerAlloc n M p) (u : A.Rows) (c : ℕ) : ℤ :=
  if c = 0 then 4 * (A.nu u.1 u.2 0 : ℤ) + 12 * (mFloor p (N n) : ℤ) - 2 * (mFloor p (K n) : ℤ) + 1
  else 2 * (A.nu u.1 u.2 c : ℤ) + 6 * (ell p (N n) c : ℤ) - (ell p (K n) c : ℤ) - 4

lemma two_srcBound (A : InnerAlloc n M p) (u v : A.Rows) (c : ℕ) :
    2 * srcBound A u v c = halfB A u c + halfB A v c := by
  unfold srcBound halfB
  split_ifs <;> ring

/-- **Every assigned weight is at most the half-weight at every source** (p. 11): the three
comparisons "at an ordinary source `c`, a row from another ordinary block `a` has half-weight
`Z_c − (ℓ_K(c)+4)/2`" (`weight_comparison`), "Formula (4.7) treats the zero-block rows at
every ordinary source", and "at the zero source, the half-weight of any ordinary row is
`2L₀ + 6m_N − m_K + 1/2 ≥ 7M + 41/2`, larger than every ordinary assigned weight"
(`zero_source_bound`). -/
theorem rowW_le_halfB (hp : IsInnerPrime n M p) (A : InnerAlloc n M p) (u : A.Rows) {c : ℕ}
    (hc : c ≤ mHalf p) : A.rowW u ≤ halfB A u c := by
  obtain ⟨a, i⟩ := u
  have hi := i.isLt
  have ha := a.isLt
  have hb : ∀ d : ℕ, (bCoef n p d : ℤ) = 3 * (ell p (N n) d : ℤ) := fun d => by simp [bCoef]
  have hLc : ∀ d : ℕ, 1 ≤ d → d ≤ mHalf p → (A.Ldim d : ℤ) = A.L d :=
    fun d h1 h2 => A.Ldim_cast hp h1 h2
  have hZ : ∀ d : ℕ, A.Z d = A.L d + bCoef n p d := fun d => A.Z_eq d
  unfold InnerAlloc.rowW halfB
  by_cases ha0 : (a : ℕ) = 0
  · -- the zero block
    rw [if_pos ha0]
    unfold InnerAlloc.w2zero
    by_cases hc0 : c = 0
    · subst hc0
      rw [if_pos rfl]
      have hnu : A.nu (a : ℕ) (i : ℕ) 0 = (i : ℕ) := by simp [InnerAlloc.nu, ha0]
      rw [hnu]
      exact min_le_left _ _
    · rw [if_neg hc0]
      have hnu : A.nu (a : ℕ) (i : ℕ) c = A.Ldim c := by
        simp [InnerAlloc.nu, ha0, Ne.symm hc0, hc0]
      rw [hnu, hLc c (by omega) hc]
      refine le_trans (min_le_right _ _) ?_
      refine le_trans (Finset.inf'_le _ (Finset.mem_Icc.2 ⟨by omega, hc⟩)) ?_
      rw [hZ c, hb c]
      linarith
  · -- an ordinary block `a ≥ 1`
    rw [if_neg ha0]
    unfold InnerAlloc.w2
    have ha1 : 1 ≤ (a : ℕ) := by omega
    have ham : (a : ℕ) ≤ mHalf p := by omega
    have hiL : ((i : ℕ) : ℤ) + 1 ≤ A.L a := by
      have : (i : ℕ) + 1 ≤ A.Ldim a := hi
      have h2 := hLc a ha1 ham
      omega
    by_cases hc0 : c = 0
    · subst hc0
      rw [if_pos rfl]
      have hnu : A.nu (a : ℕ) (i : ℕ) 0 = A.Ldim 0 := by simp [InnerAlloc.nu, Ne.symm ha0]
      rw [hnu, InnerAlloc.Ldim_zero]
      have hzs := zero_source_bound hp
      -- `2(T + 1) < 23M/5 + 2`
      have hT := two_T_add_one_lt hp A
      have hTZ : 2 * (A.T + 1) < 5 * (M : ℤ) + 2 := by
        have hM : (0 : ℚ) ≤ (M : ℚ) := by positivity
        have : (2 * ((A.T : ℚ) + 1)) < 5 * (M : ℚ) + 2 := by linarith
        exact_mod_cast this
      have hepsa : (A.eps a : ℤ) ≤ 1 := by rcases A.hEps01 a with h | h <;> simp [h]
      have hLa : A.L a = A.T - bCoef n p a + A.eps a := rfl
      have hell : (0 : ℤ) ≤ (ell p (K n) a : ℤ) := Int.natCast_nonneg _
      have hM0 : (0 : ℤ) ≤ (M : ℤ) := Int.natCast_nonneg _
      linarith
    · rw [if_neg hc0]
      by_cases hca : c = (a : ℕ)
      · subst hca
        have hnu : A.nu (a : ℕ) (i : ℕ) (a : ℕ) = (i : ℕ) := by simp [InnerAlloc.nu]
        rw [hnu, hb]
        linarith
      · have hnu : A.nu (a : ℕ) (i : ℕ) c = A.Ldim c := by simp [InnerAlloc.nu, hca]
        rw [hnu, hLc c (by omega) hc]
        have hwc := weight_comparison hp A ha1 ham (by omega : 1 ≤ c) hc
        rw [hZ c, hZ a] at hwc
        rw [hb a] at hwc ⊢
        rw [hb c] at hwc
        linarith

/-- **The weight comparisons of p. 11**: `w_u + w_v ≤` the entry exponent, doubled. -/
theorem entry_weights (hp : IsInnerPrime n M p) (A : InnerAlloc n M p) (u v : A.Rows) :
    A.rowW u + A.rowW v ≤ 2 * entry A u v := by
  obtain ⟨c, hc, hceq⟩ := Finset.exists_mem_eq_inf' (s := range (mHalf p + 1))
    ⟨0, Finset.mem_range.2 (Nat.succ_pos _)⟩ (srcBound A u v)
  rw [entry, hceq, two_srcBound]
  have hc' : c ≤ mHalf p := by simp only [Finset.mem_range] at hc; omega
  exact add_le_add (rowW_le_halfB hp A u hc') (rowW_le_halfB hp A v hc')

/-! # §3.  The unimodular basis change, and the target -/

/-- `L₀ + ∑_{a=1}^m L_a = h` over `range (m+1)`, in `ℕ` (the dimension identity). -/
theorem sum_Ldim (hp : IsInnerPrime n M p) (A : InnerAlloc n M p) :
    ∑ c ∈ range (mHalf p + 1), A.Ldim c = h n := by
  have hZ : ((∑ c ∈ range (mHalf p + 1), A.Ldim c : ℕ) : ℤ) = (h n : ℤ) := by
    rw [Nat.cast_sum, Finset.sum_range_succ' (fun c => ((A.Ldim c : ℕ) : ℤ)) (mHalf p)]
    have hstep : ∀ k ∈ range (mHalf p), ((A.Ldim (k + 1) : ℕ) : ℤ) = A.L (k + 1) :=
      fun k hk => A.Ldim_cast hp (by omega) (by simp only [Finset.mem_range] at hk; omega)
    rw [Finset.sum_congr rfl hstep]
    have hIcc : ∑ k ∈ range (mHalf p), A.L (k + 1) = ∑ a ∈ Icc 1 (mHalf p), A.L a := by
      have hset : Icc 1 (mHalf p) = Ico 1 (mHalf p + 1) := by
        ext b; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
      rw [hset, Finset.sum_Ico_eq_sum_range]
      simp only [Nat.add_sub_cancel]
      exact (Finset.sum_congr rfl (fun k _ => by rw [Nat.add_comm])).symm
    rw [hIcc, InnerAlloc.Ldim_zero]
    have := dimension_identity hp A
    omega
  exact_mod_cast hZ

/-- The index set `A.Rows` of (4.5) has exactly `h` elements. -/
theorem card_rows (hp : IsInnerPrime n M p) (A : InnerAlloc n M p) :
    Fintype.card A.Rows = h n := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range (fun c => A.Ldim c) (mHalf p + 1)]
  exact sum_Ldim hp A

/-- The integer Hermite row `hermitePoly (c ↦ c²) L a i`, mapped to `ℚ`, is the paper's row
`E_{a,i}` of (4.5). -/
theorem hermite_row_eq (A : InnerAlloc n M p) (a : Fin (mHalf p + 1)) (i : ℕ) :
    (HermiteBasis.hermitePoly (fun c : Fin (mHalf p + 1) => ((c : ℕ) : ℤ) ^ 2)
        (fun c => A.Ldim (c : ℕ)) a i).map (Int.castRingHom ℚ)
      = A.rowPoly (a : ℕ) i := by
  rw [HermiteBasis.hermitePoly_map, HermiteBasis.hermitePoly, InnerAlloc.rowPoly]
  congr 1
  have himg : (Finset.univ.erase a).image (fun c : Fin (mHalf p + 1) => (c : ℕ))
      = (Finset.range (mHalf p + 1)).erase (a : ℕ) := by
    ext x
    simp only [Finset.mem_image, Finset.mem_erase, Finset.mem_univ, and_true,
      Finset.mem_range]
    constructor
    · rintro ⟨c, hca, rfl⟩
      exact ⟨fun h => hca (Fin.ext h), c.isLt⟩
    · rintro ⟨hxa, hx⟩
      exact ⟨⟨x, hx⟩, fun h => hxa (by rw [← h]), rfl⟩
  rw [← himg, Finset.prod_image (fun x _ y _ h => Fin.ext h)]
  refine Finset.prod_congr rfl fun c _ => ?_
  simp

/-- The rows have degree `< h`: `deg E_{a,i} = ∑_{c≠a} L_c + i < ∑_c L_c = h`. -/
theorem hermite_row_natDegree_lt (hp : IsInnerPrime n M p) (A : InnerAlloc n M p)
    (a : Fin (mHalf p + 1)) (i : Fin (A.Ldim (a : ℕ))) :
    ((HermiteBasis.hermitePoly (fun c : Fin (mHalf p + 1) => ((c : ℕ) : ℤ) ^ 2)
        (fun c => A.Ldim (c : ℕ)) a (i : ℕ)).map (Int.castRingHom ℚ)).natDegree < h n := by
  rw [Polynomial.natDegree_map_eq_of_injective (RingHom.injective_int _),
    HermiteBasis.hermitePoly_natDegree]
  have hsum : ∑ c : Fin (mHalf p + 1), A.Ldim (c : ℕ) = h n := by
    rw [Fin.sum_univ_eq_sum_range (fun c => A.Ldim c) (mHalf p + 1)]
    exact sum_Ldim hp A
  have hsplit := Finset.sum_erase_add (Finset.univ : Finset (Fin (mHalf p + 1)))
    (fun c => A.Ldim (c : ℕ)) (Finset.mem_univ a)
  have hi := i.isLt
  omega

/-- **`Zeta5.Section3.entry_bounds_4_2_4_3`**, proved.

`B` is the Gram matrix of `Bil` in the basis (4.5), obtained from the monomial basis by the
integer coefficient matrix `U` of the rows; `U` is `ℤ_p`-unimodular by the shared lemma
`HermiteBasis.det_coeffMatrix_unimodular` (the rows reduce mod `p` to the Hermite basis with
the pairwise distinct nodes `−c²`), so `c = (det U)^{-2}` is a `p`-adic unit and
`Δ_K = c · det B` (`OuterLocal.Delta_eq_of_basis`).  The entry bound is `gram_entry_bound`,
the weights `entry_weights`. -/
theorem entry_bounds (n M p : ℕ) (hp : IsInnerPrime n M p) (A : InnerAlloc n M p) :
    ∃ (B : Matrix A.Rows A.Rows ℚ[X]) (entry : A.Rows → A.Rows → ℤ) (c : ℚ),
      (∀ u v, vGAtLeast p (B u v) (entry u v)) ∧
      (∀ u v, A.rowW u + A.rowW v ≤ 2 * entry u v) ∧
      c ≠ 0 ∧ padicValRat p c = 0 ∧ Delta n = C c * B.det := by
  classical
  haveI : Fact p.Prime := ⟨hp.prime⟩
  let σ : Fin (h n) ≃ A.Rows := (Fintype.equivFinOfCardEq (card_rows hp A)).symm
  let u : Fin (mHalf p + 1) → ZMod p := fun c => ((c : ℕ) : ZMod p) ^ 2
  let uZ : Fin (mHalf p + 1) → ℤ := fun c => ((c : ℕ) : ℤ) ^ 2
  let m : Fin (mHalf p + 1) → ℕ := fun c => A.Ldim (c : ℕ)
  let g : Fin (h n) → ℤ[X] := fun k => HermiteBasis.hermitePoly uZ m (σ k).1 ((σ k).2 : ℕ)
  have hg : ∀ k, (g k).map (Int.castRingHom (ZMod p))
      = HermiteBasis.hermitePoly u m (σ k).1 ((σ k).2 : ℕ) := by
    intro k
    simp only [g, HermiteBasis.hermitePoly_map]
    congr 1
    funext c
    simp [uZ, u]
  obtain ⟨h0, hv⟩ := HermiteBasis.det_coeffMatrix_unimodular u HermiteBasis.sq_injective_half
    m σ g hg
  set U := HermiteBasis.coeffMatrix fun k => (g k).map (Int.castRingHom ℚ) with hU
  have hrow : ∀ k, OuterLocal.rowPoly U k = A.rowPoly ((σ k).1 : ℕ) ((σ k).2 : ℕ) := by
    intro k
    rw [OuterLocal.rowPoly, hU, HermiteBasis.coeffMatrix_row_sum _ k
      (hermite_row_natDegree_lt hp A (σ k).1 (σ k).2)]
    exact hermite_row_eq A (σ k).1 (σ k).2
  refine ⟨(OuterLocal.Gram n U).submatrix σ.symm σ.symm, entry A, (U.det ^ 2)⁻¹, ?_,
    entry_weights hp A, inv_ne_zero (pow_ne_zero 2 h0),
    OuterLocal.padicValRat_unimodular _ hv, ?_⟩
  · intro x y
    have hx := hrow (σ.symm x)
    have hy := hrow (σ.symm y)
    rw [Equiv.apply_symm_apply] at hx hy
    rw [Matrix.submatrix_apply, OuterLocal.Gram, Matrix.of_apply, hx, hy]
    exact gram_entry_bound hp A x y
  · rw [Matrix.det_submatrix_equiv_self]
    exact OuterLocal.Delta_eq_of_basis _ h0

/-! # Known-answer controls and the axiom audit for the three `Inner*` files

The counting definitions against hand computation, at `p = 7`:
`5 ≡ −2`, so of the roots `±5` exactly one (`−5`) lies in the class `2`; both `±7` lie in the
class `0`; and `∑_{j=1}^{9} #{±j ≡ 2} = #{2, 5, 9} = 3 = ℓ_9(2)`, the value `Section41Checks`
computes for `ell 7 9 2` from the definition of `ell`. -/

example : qcount 7 2 5 = 1 := by decide

example : qcount 7 0 7 = 2 := by decide

example : ∑ j ∈ Icc 1 9, qcount 7 2 j = 3 := by decide

example : ∑ j ∈ Icc 1 9, qcount 7 2 j = ell 7 9 2 := by decide

/-- ... and the same value through the proved identity `sum_qcount_eq_ell`. -/
example : ∑ j ∈ Icc 1 9, qcount 7 2 j = ell 7 9 2 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  exact sum_qcount_eq_ell (le_refl 7) (by norm_num) (by norm_num) 9

section Audit

#print axioms Zeta5.InnerEntries.raabe_tau
#print axioms Zeta5.InnerEntries.class_bound
#print axioms Zeta5.InnerEntries.general_bound
#print axioms Zeta5.InnerEntries.pullback
#print axioms Zeta5.InnerEntries.gram_entry_bound
#print axioms Zeta5.InnerEntries.entry_weights
#print axioms Zeta5.InnerEntries.entry_bounds

end Audit

end

end InnerEntries

end Zeta5
