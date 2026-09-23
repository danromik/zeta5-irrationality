/-
Zeta5/Functional.lean

§2 of the paper: the functional `μ_X` of (2.2)–(2.3), the algebra that makes it
well defined, its affine dependence on `X`, and the exact leading coefficient (2.9).

Everything lives in the namespace `Zeta5.Functional`, so that nothing here can clash with
declarations in other files.  Nothing from `Zeta5.Basic` is redefined.

Contents.

* **(a)** `partial_fractions`, `muOver_poly`, `muOver_cof`, `muOver_add`, `muOver_smul`,
  `partial_fraction_unique`:  the statement that `{t^e}_{e≥0} ∪ {1/(t+j²)}_{j>N}` is a basis
  of the space of rational functions `A(t)/D_tail(t)`, so that (2.2)–(2.3) really do *define*
  `μ_X` on the rational functions of (2.4).  This is the content of the paper's one-sentence
  "extended by polynomial division and simple partial fractions" (the audit found the wording
  loose but the content correct).
* **(b)** `muOver_coeff_one`, `muOver_eq_affine`, `G_eq_affine`, `Delta_coeff_h`:
  `μ_X(R)` is affine in `X` with `[X]μ_X(R) = ∑_r c_r r⁴` over the residues `c_r`; hence
  `G_K(X) = A X + B` and `[X^h]Δ_K = det A`.  (`deg Δ_K ≤ h` is `Delta_natDegree_le`
  in `Basic.lean`.)
* **(c)** `eq_2_9`:  the exact leading coefficient
  `[X^h]Δ_K = (-1)^{h(h-1)/2} ∏_{j=N+1}^{K} j⁴ D_N(-j²)⁵`, via
  `det(Vᵀ diag(d) V) = det(V)² ∏ d` with `V` the Vandermonde matrix in the distinct nodes
  `-j²`.  **This discharges the former `sorry` `Zeta5.eq_2_9` of `Interface.lean`**, whose proof
  term is now `Zeta5.Functional.eq_2_9 n`.
* **(d)** `muMono_eq_zeta`:  (2.2) equals `(2e+5)! ζ(2e+2)/(12(2π)^{2e+2})`, by Euler's
  formula (Mathlib's `hasSum_zeta_nat`).  This is the known-answer control that ties the
  Bernoulli form of (2.2) to the moment interpretation of Proposition 2.2.

THIS FILE CONTAINS NO `sorry`.

POSITION IN THE DEPENDENCY GRAPH.  Nothing here uses anything from `Interface.lean`, and
this file now sits ABOVE it: `Interface.lean` imports `Zeta5.Functional` and proves
`Zeta5.eq_2_9` by `Zeta5.Functional.eq_2_9 n`.  (This rewiring was done on
2026-09-22; before it this file imported `Zeta5.Interface` and carried a `rfl` check
`eq_2_9_matches_interface : @Zeta5.eq_2_9 = @Zeta5.Functional.eq_2_9`, which is now
subsumed by the fact that Lean accepts `Zeta5.Functional.eq_2_9 n` as the proof term of
`Zeta5.eq_2_9`.)  Consequently `Zeta5.eq_2_9`, `Zeta5.eq_2_9_ne_zero`,
`Zeta5.Delta_natDegree`, `Zeta5.Q_natDegree` and the degree half of `Zeta5.theorem_2_1`
are `sorry`-free.
-/
import Zeta5.Basic

namespace Zeta5

open Polynomial Finset

noncomputable section

namespace Functional

/-! ## §2.3: the poles of `D_N^5/D_tail`, their cofactors and residues

`D_tail = ∏_{N < j ≤ K}(t + j²)` has exactly `K - N = h` simple roots `-j²`, and they are
distinct.  All of §2.3 rests on this. -/

/-- The node attached to the index `r`: the simple pole `t = -r²` of `1/D_tail`. -/
def node (r : ℕ) : ℚ := -((r : ℚ) ^ 2)

/-- `#{N < r ≤ K} = h`. -/
lemma card_poles (n : ℕ) : #(Ioc (N n) (K n)) = h n := by
  rw [Nat.card_Ioc, h_eq_K_sub_N]

/-- `deg D_tail = h`. -/
lemma Dtail_natDegree (n : ℕ) : (Dtail n).natDegree = h n := by
  classical
  rw [Dtail, natDegree_prod (Ioc (N n) (K n)) (fun j : ℕ => (X + C ((j : ℚ) ^ 2)))
        (fun j _ => (monic_X_add_C ((j : ℚ) ^ 2)).ne_zero)]
  rw [Finset.sum_congr rfl (fun j (_ : j ∈ Ioc (N n) (K n)) => natDegree_X_add_C ((j : ℚ) ^ 2))]
  simp [card_poles n]

/-- The nodes are pairwise distinct: `-r² = -s²` with `r, s ≥ 1` forces `r = s`. -/
lemma node_inj {r s : ℕ} (hr : 1 ≤ r) (hs : 1 ≤ s) (hrs : node r = node s) : r = s := by
  have h2 : ((r : ℚ)) ^ 2 = ((s : ℚ)) ^ 2 := by
    have := hrs; unfold node at this; linarith
  have h3 : ((r ^ 2 : ℕ) : ℚ) = ((s ^ 2 : ℕ) : ℚ) := by push_cast; exact h2
  have h4 : r ^ 2 = s ^ 2 := by exact_mod_cast h3
  nlinarith [h4]

/-- On the index set `Ioc (N n) (K n)` the node map is injective. -/
lemma node_injOn (n : ℕ) : Set.InjOn node (Ioc (N n) (K n) : Finset ℕ) := by
  intro r hr s hs hrs
  simp only [Finset.coe_Ioc, Set.mem_Ioc] at hr hs
  exact node_inj (by omega) (by omega) hrs

/-- `Q_r(t) = D_tail(t)/(t + r²) = ∏_{s ≠ r}(t + s²)`, the cofactor of the simple pole `-r²`.
This is the polynomial the basis element `1/(t+r²)` corresponds to. -/
def cof (n r : ℕ) : ℚ[X] := ∏ s ∈ (Ioc (N n) (K n)).erase r, (X + C ((s : ℚ) ^ 2))

lemma cof_mul (n : ℕ) {r : ℕ} (hr : r ∈ Ioc (N n) (K n)) :
    (X + C ((r : ℚ) ^ 2)) * cof n r = Dtail n := by
  rw [cof, Dtail]
  exact Finset.mul_prod_erase (Ioc (N n) (K n)) (fun j : ℕ => (X + C ((j : ℚ) ^ 2))) hr

/-- `D_tail(-r²) = 0` for every pole index `r`. -/
lemma Dtail_eval_node (n : ℕ) {r : ℕ} (hr : r ∈ Ioc (N n) (K n)) :
    (Dtail n).eval (node r) = 0 := by
  rw [← cof_mul n hr]
  simp only [eval_mul, eval_add, eval_X, eval_C, node, neg_add_cancel, zero_mul]

/-- `Q_r(-r²) = ∏_{s ≠ r}(s² - r²)`. -/
lemma cof_eval (n r : ℕ) :
    (cof n r).eval (node r)
      = ∏ s ∈ (Ioc (N n) (K n)).erase r, ((s : ℚ) ^ 2 - (r : ℚ) ^ 2) := by
  rw [cof, eval_prod]
  refine Finset.prod_congr rfl fun s _ => ?_
  simp only [eval_add, eval_X, eval_C, node]
  ring

/-- `Q_s(-r²) = 0` for `s ≠ r`: the cofactors vanish at the other nodes. -/
lemma cof_eval_of_ne (n : ℕ) {r s : ℕ} (hr : r ∈ Ioc (N n) (K n)) (hsr : s ≠ r) :
    (cof n s).eval (node r) = 0 := by
  have hmem : r ∈ (Ioc (N n) (K n)).erase s := Finset.mem_erase.2 ⟨Ne.symm hsr, hr⟩
  rw [cof, eval_prod]
  exact Finset.prod_eq_zero hmem
    (by simp only [eval_add, eval_X, eval_C, node, neg_add_cancel])

/-- `Q_r(-r²) ≠ 0`: the poles are simple. -/
lemma cof_eval_ne_zero (n : ℕ) {r : ℕ} (hr : r ∈ Ioc (N n) (K n)) :
    (cof n r).eval (node r) ≠ 0 := by
  rw [cof_eval]
  refine Finset.prod_ne_zero_iff.2 fun s hs => ?_
  have hsr : s ≠ r := (Finset.mem_erase.1 hs).1
  have hsmem : s ∈ Ioc (N n) (K n) := (Finset.mem_erase.1 hs).2
  have hs1 : 1 ≤ s := by simp only [Finset.mem_Ioc] at hsmem; omega
  have hr1 : 1 ≤ r := by simp only [Finset.mem_Ioc] at hr; omega
  intro hcon
  exact hsr (node_inj hs1 hr1 (by unfold node; linarith))

/-- `D_N(-r²) ≠ 0` for `r > N`: the poles of `1/D_tail` are not zeros of the numerator
`W = D_N⁵`.  (This duplicates the `sorry`-free `Zeta5.D_eval_ne_zero` of `Interface.lean`,
so that nothing in this file depends on `Interface.lean`; see the header.) -/
lemma D_eval_node_ne_zero (m j : ℕ) (hj : m < j) : (D m).eval (node j) ≠ 0 := by
  rw [D, Polynomial.eval_prod]
  refine Finset.prod_ne_zero_iff.2 fun i hi => ?_
  simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C, node]
  have hi' : i ≤ m := (Finset.mem_Icc.1 hi).2
  have hij : (i : ℚ) < (j : ℚ) := by exact_mod_cast lt_of_le_of_lt hi' hj
  have hi0 : (0 : ℚ) ≤ (i : ℚ) := by positivity
  intro hcon
  nlinarith [hcon]

/-- `D'_tail(-r²) = Q_r(-r²)`: the derivative of a product at a simple root. -/
lemma derivative_Dtail_eval (n : ℕ) {r : ℕ} (hr : r ∈ Ioc (N n) (K n)) :
    (derivative (Dtail n)).eval (node r) = (cof n r).eval (node r) := by
  rw [Dtail, derivative_prod_finset, Polynomial.eval_finsetSum]
  rw [Finset.sum_eq_single r]
  · simp only [derivative_add, derivative_X, derivative_C, add_zero, mul_one, cof]
  · intro b _hb hbr
    have hmem : r ∈ (Ioc (N n) (K n)).erase b := Finset.mem_erase.2 ⟨Ne.symm hbr, hr⟩
    rw [eval_mul, eval_prod, Finset.prod_eq_zero hmem
      (by simp only [eval_add, eval_X, eval_C, node, neg_add_cancel]), zero_mul]
  · intro hcon; exact absurd hr hcon

/-! ### The residues

`residue n A r` of `Basic.lean` is defined as `(A %ₘ D_tail)(-r²)/D'_tail(-r²)`.  The
remainder may be dropped, and the derivative replaced by the cofactor. -/

lemma modByMonic_eval_node (n : ℕ) (A : ℚ[X]) {r : ℕ} (hr : r ∈ Ioc (N n) (K n)) :
    (A %ₘ Dtail n).eval (node r) = A.eval (node r) := by
  conv_rhs => rw [← modByMonic_add_div A (Dtail n)]
  simp [Dtail_eval_node n hr]

/-- `c_r = A(-r²)/Q_r(-r²)`, the residue in its usable form. -/
theorem residue_eq (n : ℕ) (A : ℚ[X]) {r : ℕ} (hr : r ∈ Ioc (N n) (K n)) :
    residue n A r = A.eval (node r) / (cof n r).eval (node r) := by
  have hnode : (-(r : ℚ) ^ 2) = node r := rfl
  rw [residue, hnode, modByMonic_eval_node n A hr, derivative_Dtail_eval n hr]

/-! ## (a) Polynomial division and simple partial fractions

`A/D_tail = (A /ₘ D_tail) + ∑_r c_r/(t + r²)`, in the equivalent polynomial form
`A = (A /ₘ D_tail)·D_tail + ∑_r c_r Q_r`.  Together with `partial_fraction_unique` this is
the basis property that makes `μ_X` well defined by (2.2)–(2.3). -/

/-- A polynomial of degree `< h` is determined by its values at the `h` nodes. -/
lemma eq_of_natDegree_lt_of_eval_nodes (n : ℕ) {P R : ℚ[X]}
    (hP : P.natDegree < h n) (hR : R.natDegree < h n)
    (heval : ∀ r ∈ Ioc (N n) (K n), P.eval (node r) = R.eval (node r)) : P = R := by
  refine Polynomial.eq_of_natDegree_lt_card_of_eval_eq' P R
    ((Ioc (N n) (K n)).image node) (fun x hx => ?_) ?_
  · obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hx
    exact heval r hr
  · rw [Finset.card_image_of_injOn (node_injOn n), card_poles n]
    exact max_lt hP hR

/-- **Polynomial division and simple partial fractions** (§2.1, the sentence after (2.3), and
§2.3).  Every `A(t)/D_tail(t)` is the sum of a polynomial and `∑_r c_r/(t + r²)` with
`c_r = residue n A r`; here in the equivalent polynomial form.

This is what makes `muOver` (the extension of (2.2)–(2.3) used in `Basic.lean`) legitimate. -/
theorem partial_fractions (n : ℕ) (A : ℚ[X]) :
    A = (A /ₘ Dtail n) * Dtail n
        + ∑ r ∈ Ioc (N n) (K n), C (residue n A r) * cof n r := by
  by_cases hn : n = 0
  · subst hn
    simp [Dtail, N, K]
  · have hh : 0 < h n := by
      have : 0 < n := Nat.pos_of_ne_zero hn
      simp only [h]; omega
    have hDne1 : Dtail n ≠ 1 := by
      intro hcon
      have := Dtail_natDegree n
      rw [hcon] at this
      simp at this
      omega
    -- the remainder and the sum are two polynomials of degree `< h` agreeing at the nodes
    have hrem : A %ₘ Dtail n
        = ∑ r ∈ Ioc (N n) (K n), C (residue n A r) * cof n r := by
      refine eq_of_natDegree_lt_of_eval_nodes n ?_ ?_ ?_
      · have := Polynomial.natDegree_modByMonic_lt A (Dtail_monic n) hDne1
        rwa [Dtail_natDegree n] at this
      · have hb : ∀ r ∈ Ioc (N n) (K n),
            (C (residue n A r) * cof n r).natDegree ≤ h n - 1 := by
          intro r hr
          refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
          rw [cof]
          refine le_trans (Polynomial.natDegree_prod_le _ _) ?_
          rw [Finset.sum_congr rfl
            (fun s (_ : s ∈ (Ioc (N n) (K n)).erase r) => natDegree_X_add_C ((s : ℚ) ^ 2))]
          simp [Finset.card_erase_of_mem hr, card_poles n]
        exact lt_of_le_of_lt (Polynomial.natDegree_sum_le_of_forall_le _ _ hb) (by omega)
      · intro r hr
        rw [modByMonic_eval_node n A hr, Polynomial.eval_finsetSum]
        rw [Finset.sum_eq_single r]
        · rw [eval_mul, eval_C, residue_eq n A hr]
          field_simp [cof_eval_ne_zero n hr]
        · intro s _hs hsr
          rw [eval_mul, cof_eval_of_ne n hr hsr, mul_zero]
        · intro hcon; exact absurd hr hcon
    calc A = A %ₘ Dtail n + Dtail n * (A /ₘ Dtail n) := (modByMonic_add_div A (Dtail n)).symm
      _ = (A /ₘ Dtail n) * Dtail n
            + ∑ r ∈ Ioc (N n) (K n), C (residue n A r) * cof n r := by
          rw [hrem]; ring


/-! ### Linear independence: the decomposition is unique

If a polynomial times `D_tail` plus a combination of the cofactors `Q_r` vanishes, all the
data vanish.  Divided through by `D_tail`, this says exactly that
`{t^e}_{e≥0} ∪ {1/(t+r²)}_{N<r≤K}` is linearly independent over `ℚ`. -/

/-- `(∑_s c_s Q_s)(-r²) = c_r Q_r(-r²)`: at a node only its own cofactor survives. -/
lemma eval_cof_sum (n : ℕ) (c : ℕ → ℚ) {r : ℕ} (hr : r ∈ Ioc (N n) (K n)) :
    (∑ s ∈ Ioc (N n) (K n), C (c s) * cof n s).eval (node r)
      = c r * (cof n r).eval (node r) := by
  rw [Polynomial.eval_finsetSum, Finset.sum_eq_single r]
  · rw [eval_mul, eval_C]
  · intro s _hs hsr
    rw [eval_mul, cof_eval_of_ne n hr hsr, mul_zero]
  · intro hcon; exact absurd hr hcon

/-- **Linear independence of the basis of §2.1** (the property that makes (2.2)–(2.3) a
*definition*).  In polynomial form: the polynomial part and the residues of a
`P + ∑_r c_r/(t+r²)` are uniquely determined. -/
theorem partial_fraction_unique (n : ℕ) (P P' : ℚ[X]) (c c' : ℕ → ℚ)
    (hEq : P * Dtail n + ∑ r ∈ Ioc (N n) (K n), C (c r) * cof n r
         = P' * Dtail n + ∑ r ∈ Ioc (N n) (K n), C (c' r) * cof n r) :
    P = P' ∧ ∀ r ∈ Ioc (N n) (K n), c r = c' r := by
  have hc : ∀ r ∈ Ioc (N n) (K n), c r = c' r := by
    intro r hr
    have hev := congrArg (Polynomial.eval (node r)) hEq
    simp only [eval_add, eval_mul, Dtail_eval_node n hr, mul_zero, zero_add,
      eval_cof_sum n c hr, eval_cof_sum n c' hr] at hev
    exact mul_right_cancel₀ (cof_eval_ne_zero n hr) hev
  refine ⟨?_, hc⟩
  have hsum : ∑ r ∈ Ioc (N n) (K n), C (c r) * cof n r
      = ∑ r ∈ Ioc (N n) (K n), C (c' r) * cof n r :=
    Finset.sum_congr rfl fun r hr => by rw [hc r hr]
  rw [hsum] at hEq
  have : P * Dtail n = P' * Dtail n := by linear_combination hEq
  exact mul_right_cancel₀ (Dtail_monic n).ne_zero this

/-! ### `μ_X` is ℚ-linear in the rational function

The paper says "extended by linearity"; this is that extension, for the concrete realisation
`muOver n A = μ_X(A(t)/D_tail(t))` used in `Basic.lean`.  `prop_2_2` (positive definiteness)
uses exactly this. -/

lemma muPoly_eq_sum (P : ℚ[X]) {s : Finset ℕ} (hs : P.support ⊆ s) :
    muPoly P = ∑ e ∈ s, P.coeff e * muMono e :=
  Finset.sum_subset hs fun e _he hes => by
    rw [Polynomial.notMem_support_iff.1 hes, zero_mul]

lemma muPoly_add (P R : ℚ[X]) : muPoly (P + R) = muPoly P + muPoly R := by
  classical
  have h1 : muPoly (P + R)
      = ∑ e ∈ (P + R).support ∪ (P.support ∪ R.support), (P + R).coeff e * muMono e :=
    muPoly_eq_sum (P + R) Finset.subset_union_left
  have h2 : muPoly P
      = ∑ e ∈ (P + R).support ∪ (P.support ∪ R.support), P.coeff e * muMono e :=
    muPoly_eq_sum P (Finset.Subset.trans Finset.subset_union_left Finset.subset_union_right)
  have h3 : muPoly R
      = ∑ e ∈ (P + R).support ∪ (P.support ∪ R.support), R.coeff e * muMono e :=
    muPoly_eq_sum R (Finset.Subset.trans Finset.subset_union_right Finset.subset_union_right)
  rw [h1, h2, h3, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun e _ => by rw [coeff_add]; ring

lemma muPoly_C_mul (a : ℚ) (P : ℚ[X]) : muPoly (C a * P) = a * muPoly P := by
  have hsub : (C a * P).support ⊆ P.support := by
    intro e he
    rw [Polynomial.mem_support_iff] at he ⊢
    intro hcon
    exact he (by rw [coeff_C_mul, hcon, mul_zero])
  rw [muPoly_eq_sum (C a * P) hsub, muPoly_eq_sum P Finset.Subset.rfl, Finset.mul_sum]
  exact Finset.sum_congr rfl fun e _ => by rw [coeff_C_mul]; ring

lemma residue_add (n : ℕ) (A B : ℚ[X]) (r : ℕ) :
    residue n (A + B) r = residue n A r + residue n B r := by
  rw [residue, residue, residue, Polynomial.add_modByMonic, eval_add]
  ring

lemma residue_C_mul (n : ℕ) (a : ℚ) (A : ℚ[X]) (r : ℕ) :
    residue n (C a * A) r = a * residue n A r := by
  rw [residue, residue, ← Polynomial.smul_eq_C_mul, Polynomial.smul_modByMonic,
    Polynomial.eval_smul, smul_eq_mul]
  ring

/-- `μ_X` is additive in the rational function (§2.1, "extended by linearity"). -/
theorem muOver_add (n : ℕ) (A B : ℚ[X]) :
    muOver n (A + B) = muOver n A + muOver n B := by
  rw [muOver, muOver, muOver, Polynomial.add_divByMonic, muPoly_add, C_add]
  have hterm : ∀ r ∈ Ioc (N n) (K n), C (residue n (A + B) r) * muPole r
      = C (residue n A r) * muPole r + C (residue n B r) * muPole r := by
    intro r _
    rw [residue_add, C_add]
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
  ring

/-- `μ_X` is ℚ-homogeneous in the rational function. -/
theorem muOver_C_mul (n : ℕ) (a : ℚ) (A : ℚ[X]) :
    muOver n (C a * A) = C a * muOver n A := by
  have hdiv : (C a * A) /ₘ Dtail n = C a * (A /ₘ Dtail n) := by
    rw [← Polynomial.smul_eq_C_mul, Polynomial.smul_divByMonic, Polynomial.smul_eq_C_mul]
  rw [muOver, muOver, hdiv, muPoly_C_mul, C_mul]
  have hterm : ∀ r ∈ Ioc (N n) (K n),
      C (residue n (C a * A) r) * muPole r = C a * (C (residue n A r) * muPole r) := by
    intro r _
    rw [residue_C_mul, C_mul]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  ring

/-! ### `μ_X` on the basis elements

`μ_X` of a polynomial is `muPoly` (2.2), and `μ_X` of `1/(t+r²)` — realised as the numerator
`Q_r` over `D_tail` — is `muPole r` (2.3).  These two, with linearity, pin `muOver` down. -/

/-- (2.2): on a polynomial `P(t) = P(t)·D_tail(t)/D_tail(t)`, `μ_X` is `muPoly P`. -/
theorem muOver_poly (n : ℕ) (P : ℚ[X]) : muOver n (P * Dtail n) = C (muPoly P) := by
  have hdiv : (P * Dtail n) /ₘ Dtail n = P := by
    rw [mul_comm]
    exact Polynomial.mul_divByMonic_cancel_left P (Dtail_monic n)
  have hres : ∀ r ∈ Ioc (N n) (K n), C (residue n (P * Dtail n) r) * muPole r = 0 := by
    intro r _
    have : (P * Dtail n) %ₘ Dtail n = 0 := by
      rw [mul_comm]
      exact (Polynomial.modByMonic_eq_zero_iff_dvd (Dtail_monic n)).2 ⟨P, rfl⟩
    rw [residue, this]
    simp
  rw [muOver, hdiv, Finset.sum_congr rfl hres, Finset.sum_const_zero, add_zero]

/-- (2.3): on the basis element `1/(t+r²)`, realised as `Q_r/D_tail`, `μ_X` is `muPole r`. -/
theorem muOver_cof (n : ℕ) {r : ℕ} (hr : r ∈ Ioc (N n) (K n)) :
    muOver n (cof n r) = muPole r := by
  have hlt : (cof n r).natDegree < (Dtail n).natDegree := by
    rw [Dtail_natDegree n, cof]
    refine lt_of_le_of_lt (Polynomial.natDegree_prod_le _ _) ?_
    rw [Finset.sum_congr rfl
      (fun s (_ : s ∈ (Ioc (N n) (K n)).erase r) => natDegree_X_add_C ((s : ℚ) ^ 2))]
    simp only [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_erase_of_mem hr, card_poles n]
    have : 0 < h n := by
      have := card_poles n
      have hne : (Ioc (N n) (K n)).Nonempty := ⟨r, hr⟩
      rw [← this]
      exact Finset.card_pos.2 hne
    omega
  have hdiv : cof n r /ₘ Dtail n = 0 :=
    (Polynomial.divByMonic_eq_zero_iff (Dtail_monic n)).2 (Polynomial.degree_lt_degree hlt)
  have hres : ∀ s ∈ Ioc (N n) (K n),
      C (residue n (cof n r) s) * muPole s = if s = r then muPole r else 0 := by
    intro s hs
    by_cases hsr : s = r
    · subst hsr
      rw [residue_eq n _ hs, div_self (cof_eval_ne_zero n hs), C_1, one_mul]
      simp
    · rw [residue_eq n _ hs, cof_eval_of_ne n hs (fun hc => hsr hc.symm), zero_div, C_0,
        zero_mul]
      simp [hsr]
  rw [muOver, hdiv, Finset.sum_congr rfl hres, Finset.sum_ite_eq' (Ioc (N n) (K n)) r]
  simp [muPoly, hr]

/-! ## (b) `μ_X` is affine in `X`, so `G_K(X) = A X + B` and `[X^h]Δ_K = det A` -/

/-- (2.3) in normal form: `μ_X(1/(t+j²)) = j⁴·X + (-(j⁴H^{(5)}_j) - 1/4 + 1/(2j))`. -/
lemma muPole_eq (j : ℕ) :
    muPole j
      = C ((j : ℚ) ^ 4) * X + C (-((j : ℚ) ^ 4 * H5 j) - 1 / 4 + 1 / (2 * (j : ℚ))) := by
  simp only [muPole, C_add, C_sub, C_neg, C_mul]
  ring

lemma muPole_coeff_zero (j : ℕ) :
    (muPole j).coeff 0 = -((j : ℚ) ^ 4 * H5 j) - 1 / 4 + 1 / (2 * (j : ℚ)) := by
  rw [muPole_eq, coeff_add, coeff_C_mul, coeff_X_zero, coeff_C]
  norm_num

lemma muPole_coeff_one (j : ℕ) : (muPole j).coeff 1 = (j : ℚ) ^ 4 := by
  rw [muPole_eq, coeff_add, coeff_C_mul, coeff_X_one, coeff_C]
  norm_num

/-- `[X] μ_X(A/D_tail) = ∑_r c_r r⁴`, the `X`-coefficient of `μ_X`: only the poles
contribute, each with its residue times `j⁴` (from (2.3)). -/
theorem muOver_coeff_one (n : ℕ) (A : ℚ[X]) :
    (muOver n A).coeff 1 = ∑ r ∈ Ioc (N n) (K n), residue n A r * (r : ℚ) ^ 4 := by
  rw [muOver, coeff_add, Polynomial.finsetSum_coeff]
  simp only [coeff_C, coeff_C_mul, muPole_coeff_one]
  norm_num

/-- `μ_X(R) = [X^0] + [X^1]·X`: the value is an affine polynomial in `X` (p. 3). -/
theorem muOver_eq_affine (n : ℕ) (A : ℚ[X]) :
    muOver n A = C ((muOver n A).coeff 0) + C ((muOver n A).coeff 1) * X := by
  have hd : (muOver n A).degree ≤ 1 :=
    Polynomial.natDegree_le_iff_degree_le.1 (muOver_natDegree_le n A)
  conv_lhs => rw [Polynomial.eq_X_add_C_of_degree_le_one hd]
  ring

/-- `[X] G_K`: the matrix of `X`-coefficients of the Hankel matrix (2.4). -/
def Gcoef (n : ℕ) : Matrix (Fin (h n)) (Fin (h n)) ℚ :=
  Matrix.of fun i j => (G n i j).coeff 1

/-- `[X⁰] G_K`. -/
def Gconst (n : ℕ) : Matrix (Fin (h n)) (Fin (h n)) ℚ :=
  Matrix.of fun i j => (G n i j).coeff 0

/-- **`G_K(X) = A X + B`** (p. 3: "the entries are affine in `X`"). -/
theorem G_eq_affine (n : ℕ) :
    G n = (X : ℚ[X]) • (Gcoef n).map C + (Gconst n).map C := by
  ext i j
  have key : G n i j = C ((G n i j).coeff 0) + C ((G n i j).coeff 1) * X :=
    muOver_eq_affine n (entryNum n i j)
  have hrhs : ((X : ℚ[X]) • (Gcoef n).map C + (Gconst n).map C) i j
      = X * C ((G n i j).coeff 1) + C ((G n i j).coeff 0) := rfl
  rw [hrhs]
  conv_lhs => rw [key]
  ring_nf

/-- **`[X^h] Δ_K = det([X]G_K)`.**  With `Delta_natDegree_le` (`Basic.lean`) this is the
whole of the degree statement of §2.3 except for the evaluation of the determinant, which
is (2.9) below. -/
theorem Delta_coeff_h (n : ℕ) : (Delta n).coeff (h n) = (Gcoef n).det := by
  have h1 := Polynomial.coeff_det_X_add_C_card (Gcoef n) (Gconst n)
  rw [Fintype.card_fin] at h1
  rw [Delta, G_eq_affine n]
  exact h1


/-! ## (c) The exact leading coefficient (2.9)

`[X]G_K = Vᵀ diag(d) V` with `V` the Vandermonde matrix in the `h` distinct nodes `-r²`,
`N < r ≤ K`, and `d_r = r⁴ D_N(-r²)⁵/D'_tail(-r²)`.  Hence
`det [X]G_K = (det V)² ∏_r d_r`, and the product of the `D'_tail(-r²)` is
`(-1)^{h(h-1)/2}(det V)²`, which leaves exactly (2.9). -/

lemma node_eq (r : ℕ) : node r = -((r : ℚ)) ^ 2 := rfl

/-- `d_r = r⁴ D_N(-r²)⁵/D'_tail(-r²)`, the diagonal of the factorisation of `[X]G_K`. -/
def dCoef (n r : ℕ) : ℚ :=
  (r : ℚ) ^ 4 * ((D (N n)).eval (node r)) ^ 5 / (cof n r).eval (node r)

/-- The `(i,j)` entry of `[X]G_K` in closed form: `∑_r d_r (-r²)^{i+j}`. -/
theorem Gcoef_apply (n : ℕ) (i j : Fin (h n)) :
    Gcoef n i j = ∑ r ∈ Ioc (N n) (K n), dCoef n r * node r ^ ((i : ℕ) + (j : ℕ)) := by
  have hG : Gcoef n i j = (muOver n (entryNum n i j)).coeff 1 := rfl
  rw [hG, muOver_coeff_one]
  refine Finset.sum_congr rfl fun r hr => ?_
  rw [residue_eq n _ hr, entryNum, dCoef]
  simp only [eval_mul, eval_pow, eval_X]
  ring

/-- `d_r` written exactly as the paper writes it in §2.3, with `D'_tail(-r²)` in the
denominator (`residue`/`cof` use the cofactor, which is the same number). -/
lemma dCoef_eq_derivative (n : ℕ) {r : ℕ} (hr : r ∈ Ioc (N n) (K n)) :
    dCoef n r = (r : ℚ) ^ 4 * ((D (N n)).eval (node r)) ^ 5
        / (derivative (Dtail n)).eval (node r) := by
  rw [dCoef, derivative_Dtail_eval n hr]

/-- **The `d_j` of (2.9) are nonzero**: `D_N(-j²) ≠ 0` for `j > N` (the cancellation
`D_N⁶/D_K = D_N⁵/D_tail` leaves exactly the `K - N` simple poles `-j²`, `N < j ≤ K`, and
none of them is a zero of the numerator).  This is why `[X]G_K` is nonsingular. -/
theorem dCoef_ne_zero (n : ℕ) {r : ℕ} (hr : r ∈ Ioc (N n) (K n)) : dCoef n r ≠ 0 := by
  rw [dCoef]
  refine div_ne_zero (mul_ne_zero ?_ ?_) (cof_eval_ne_zero n hr)
  · refine pow_ne_zero _ (Nat.cast_ne_zero.2 ?_)
    simp only [Finset.mem_Ioc] at hr
    omega
  · exact pow_ne_zero _ (D_eval_node_ne_zero (N n) r (Finset.mem_Ioc.1 hr).1)

/-! ### Reindexing the `h` poles by `Fin h` -/

/-- The `i`-th pole index, `N + 1 + i`. -/
def idx (n : ℕ) (i : Fin (h n)) : ℕ := N n + 1 + (i : ℕ)

lemma idx_inj (n : ℕ) : Function.Injective (idx n) := by
  intro i j hij
  have : (i : ℕ) = (j : ℕ) := by unfold idx at hij; omega
  exact Fin.ext this

lemma idx_ge_one (n : ℕ) (i : Fin (h n)) : 1 ≤ idx n i := by
  unfold idx; omega

lemma image_idx (n : ℕ) :
    (Finset.univ : Finset (Fin (h n))).image (idx n) = Ioc (N n) (K n) := by
  ext r
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_Ioc]
  constructor
  · rintro ⟨i, rfl⟩
    have hi := i.isLt
    simp only [idx, h, K, N] at hi ⊢
    omega
  · rintro ⟨h1, h2⟩
    have hlt : r - N n - 1 < h n := by
      simp only [h, K, N] at h1 h2 ⊢
      omega
    refine ⟨⟨r - N n - 1, hlt⟩, ?_⟩
    simp only [idx]
    omega

lemma sum_poles (n : ℕ) (g : ℕ → ℚ) :
    ∑ r ∈ Ioc (N n) (K n), g r = ∑ i : Fin (h n), g (idx n i) := by
  rw [← image_idx n, Finset.sum_image (fun x _ y _ hxy => idx_inj n hxy)]

lemma prod_poles (n : ℕ) (g : ℕ → ℚ) :
    ∏ r ∈ Ioc (N n) (K n), g r = ∏ i : Fin (h n), g (idx n i) := by
  rw [← image_idx n, Finset.prod_image (fun x _ y _ hxy => idx_inj n hxy)]

lemma prod_erase_poles (n : ℕ) (g : ℕ → ℚ) (i₀ : Fin (h n)) :
    ∏ r ∈ (Ioc (N n) (K n)).erase (idx n i₀), g r
      = ∏ i ∈ (Finset.univ : Finset (Fin (h n))).erase i₀, g (idx n i) := by
  rw [← image_idx n, ← Finset.image_erase (idx_inj n),
    Finset.prod_image (fun x _ y _ hxy => idx_inj n hxy)]

/-- The nodes, indexed by `Fin h`: `v_i = -(N+1+i)²`. -/
def vNode (n : ℕ) (i : Fin (h n)) : ℚ := node (idx n i)

/-- The diagonal, indexed by `Fin h`. -/
def dFin (n : ℕ) (i : Fin (h n)) : ℚ := dCoef n (idx n i)

lemma vNode_inj (n : ℕ) : Function.Injective (vNode n) := by
  intro i j hij
  exact idx_inj n (node_inj (idx_ge_one n i) (idx_ge_one n j) hij)

/-! ### `[X]G_K = Vᵀ diag(d) V` -/

theorem Gcoef_factor (n : ℕ) :
    Gcoef n = (Matrix.vandermonde (vNode n)).transpose * Matrix.diagonal (dFin n)
                * Matrix.vandermonde (vNode n) := by
  ext i j
  rw [Gcoef_apply, sum_poles, Matrix.mul_assoc, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.transpose_apply, Matrix.diagonal_mul, Matrix.vandermonde_apply,
    Matrix.vandermonde_apply, pow_add]
  simp only [vNode, dFin]
  ring

theorem det_Gcoef (n : ℕ) :
    (Gcoef n).det
      = (Matrix.vandermonde (vNode n)).det ^ 2 * ∏ i : Fin (h n), dFin n i := by
  rw [Gcoef_factor, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal]
  ring

/-! ### The off-diagonal product and its sign -/

/-- `∑_{i<m} #{j : j > i} = m(m-1)/2`. -/
lemma sum_card_Ioi (m : ℕ) : ∑ i : Fin m, #(Finset.Ioi i) = m * (m - 1) / 2 := by
  have h1 : ∀ i : Fin m, #(Finset.Ioi i) = m - 1 - (i : ℕ) := fun i => Fin.card_Ioi i
  rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => h1 i),
    Fin.sum_univ_eq_sum_range (fun k => m - 1 - k) m]
  exact (Finset.sum_range_reflect (fun k => k) m).trans (Finset.sum_range_id m)

/-- **`∏_i ∏_{k ≠ i}(v_i - v_k) = (-1)^{m(m-1)/2} (∏_{i<j}(v_j - v_i))²`.**
The sign bookkeeping behind (2.9). -/
theorem prod_offDiag (m : ℕ) (v : Fin m → ℚ) :
    (∏ i : Fin m, ∏ k ∈ (Finset.univ : Finset (Fin m)).erase i, (v i - v k))
      = (-1) ^ (m * (m - 1) / 2)
        * (∏ i : Fin m, ∏ j ∈ Finset.Ioi i, (v j - v i)) ^ 2 := by
  have hsplit : ∀ i : Fin m,
      (Finset.univ : Finset (Fin m)).erase i = Finset.Iio i ∪ Finset.Ioi i := by
    intro i
    ext k
    simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_union, Finset.mem_Iio,
      Finset.mem_Ioi]
    constructor
    · intro hk
      rcases lt_or_gt_of_ne hk with hlt | hgt
      · exact Or.inl hlt
      · exact Or.inr hgt
    · rintro (hlt | hgt)
      · exact ne_of_lt hlt
      · exact ne_of_gt hgt
  have hdisj : ∀ i : Fin m, Disjoint (Finset.Iio i) (Finset.Ioi i) := by
    intro i
    refine Finset.disjoint_left.2 fun k hk1 hk2 => ?_
    rw [Finset.mem_Iio] at hk1
    rw [Finset.mem_Ioi] at hk2
    exact absurd (hk1.trans hk2) (lt_irrefl _)
  have hstep : ∀ i ∈ (Finset.univ : Finset (Fin m)),
      (∏ k ∈ (Finset.univ : Finset (Fin m)).erase i, (v i - v k))
        = (∏ k ∈ Finset.Iio i, (v i - v k)) * ∏ k ∈ Finset.Ioi i, (v i - v k) := by
    intro i _
    rw [hsplit i, Finset.prod_union (hdisj i)]
  have hA : (∏ i : Fin m, ∏ k ∈ Finset.Iio i, (v i - v k))
      = ∏ i : Fin m, ∏ j ∈ Finset.Ioi i, (v j - v i) := by
    refine Finset.prod_comm' ?_
    intro x y
    simp only [Finset.mem_univ, true_and, and_true, Finset.mem_Iio, Finset.mem_Ioi]
  have hBstep : ∀ i ∈ (Finset.univ : Finset (Fin m)),
      (∏ k ∈ Finset.Ioi i, (v i - v k))
        = (-1 : ℚ) ^ #(Finset.Ioi i) * ∏ k ∈ Finset.Ioi i, (v k - v i) := by
    intro i _
    rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k _ => by ring
  have hB : (∏ i : Fin m, ∏ k ∈ Finset.Ioi i, (v i - v k))
      = (-1 : ℚ) ^ (m * (m - 1) / 2) * ∏ i : Fin m, ∏ j ∈ Finset.Ioi i, (v j - v i) := by
    rw [Finset.prod_congr rfl hBstep, Finset.prod_mul_distrib,
      Finset.prod_pow_eq_pow_sum, sum_card_Ioi m]
  rw [Finset.prod_congr rfl hstep, Finset.prod_mul_distrib, hA, hB]
  ring

/-! ### Putting the determinant together -/

/-- `∏_r D'_tail(-r²) = (-1)^{h(h-1)/2}(det V)²`. -/
theorem prod_cof_eval (n : ℕ) :
    (∏ i : Fin (h n), (cof n (idx n i)).eval (node (idx n i)))
      = (-1) ^ (h n * (h n - 1) / 2) * (Matrix.vandermonde (vNode n)).det ^ 2 := by
  have h1 : ∀ i ∈ (Finset.univ : Finset (Fin (h n))),
      (cof n (idx n i)).eval (node (idx n i))
        = ∏ k ∈ (Finset.univ : Finset (Fin (h n))).erase i, (vNode n i - vNode n k) := by
    intro i _
    rw [cof_eval, prod_erase_poles n _ i]
    refine Finset.prod_congr rfl fun k _ => ?_
    simp only [vNode, node_eq]
    ring
  rw [Finset.prod_congr rfl h1, prod_offDiag, Matrix.det_vandermonde]

/-- The numerator of (2.9): `∏_{j=N+1}^K j⁴ D_N(-j²)⁵`. -/
def num29 (n : ℕ) : ℚ :=
  ∏ j ∈ Ioc (N n) (K n), ((j : ℚ) ^ 4 * ((D (N n)).eval (node j)) ^ 5)

lemma num29_eq (n : ℕ) :
    num29 n = ∏ j ∈ Ioc (N n) (K n), ((j : ℚ) ^ 4 * ((D (N n)).eval (-((j : ℚ)) ^ 2)) ^ 5) :=
  rfl

lemma idx_mem (n : ℕ) (i : Fin (h n)) : idx n i ∈ Ioc (N n) (K n) := by
  rw [← image_idx n]
  exact Finset.mem_image_of_mem _ (Finset.mem_univ i)

/-- `(∏_r D'_tail(-r²)) · (∏_r d_r) = ∏_r r⁴ D_N(-r²)⁵`. -/
theorem prod_dFin_mul (n : ℕ) :
    ((-1 : ℚ) ^ (h n * (h n - 1) / 2) * (Matrix.vandermonde (vNode n)).det ^ 2)
      * (∏ i : Fin (h n), dFin n i) = num29 n := by
  rw [← prod_cof_eval, ← Finset.prod_mul_distrib, num29,
    prod_poles n (fun r => (r : ℚ) ^ 4 * ((D (N n)).eval (node r)) ^ 5)]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hne : (cof n (idx n i)).eval (node (idx n i)) ≠ 0 :=
    cof_eval_ne_zero n (idx_mem n i)
  rw [dFin, dCoef]
  field_simp

/-- **(2.9)** (p. 4): `[X^h]Δ_K = (-1)^{h(h-1)/2} ∏_{j=N+1}^K j⁴ D_N(-j²)⁵`.

This is literally the statement of the former `sorry` `Zeta5.eq_2_9` in `Interface.lean`,
which is now proved by this theorem (`Zeta5.eq_2_9 n := Zeta5.Functional.eq_2_9 n`). -/
theorem eq_2_9 (n : ℕ) :
    (Delta n).coeff (h n)
      = (-1) ^ (h n * (h n - 1) / 2) *
          ∏ j ∈ Ioc (N n) (K n), ((j : ℚ) ^ 4 * ((D (N n)).eval (-((j : ℚ)) ^ 2)) ^ 5) := by
  have hsq : ((-1 : ℚ) ^ (h n * (h n - 1) / 2)) * ((-1 : ℚ) ^ (h n * (h n - 1) / 2)) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  rw [← num29_eq, Delta_coeff_h, det_Gcoef, ← prod_dFin_mul n]
  linear_combination (-((Matrix.vandermonde (vNode n)).det ^ 2
    * ∏ i : Fin (h n), dFin n i)) * hsq


/-! ### Consequences of (2.9): the degree is exactly `h`

These are the statements `Zeta5.eq_2_9_ne_zero`, `Zeta5.Delta_natDegree`,
`Zeta5.Q_natDegree` of `Interface.lean`.  Those `Interface.lean`
versions are themselves `sorry`-free, being derived from `Zeta5.eq_2_9 = this file's
`eq_2_9`; the duplicates here are kept because this file must stay self-contained. -/

theorem eq_2_9_ne_zero (n : ℕ) : (Delta n).coeff (h n) ≠ 0 := by
  rw [eq_2_9 n]
  refine mul_ne_zero (by positivity) (Finset.prod_ne_zero_iff.2 fun j hj => ?_)
  have hjN : N n < j := (Finset.mem_Ioc.1 hj).1
  have hjQ : ((j : ℚ)) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  exact mul_ne_zero (pow_ne_zero _ hjQ) (pow_ne_zero _ (D_eval_node_ne_zero (N n) j hjN))

/-- **`deg Δ_K = h` exactly** (p. 4), now with no `sorry` anywhere underneath. -/
theorem Delta_natDegree (n : ℕ) : (Delta n).natDegree = h n :=
  le_antisymm (Delta_natDegree_le n) (Polynomial.le_natDegree_of_ne_zero (eq_2_9_ne_zero n))

/-- **`deg Q_{K,M} = h` exactly** — the degree claim of Theorem 2.1, which Theorem 1.1
needs. -/
theorem Q_natDegree (n M : ℕ) (Alloc : InnerAllocFamily n M) :
    (Q n M Alloc).natDegree = h n := by
  have hm : mKM n M Alloc ≠ 0 := ne_of_gt (mKM_pos n M Alloc)
  have hs : S n ≠ 0 := ne_of_gt (S_pos n)
  rw [Q, F, ← mul_assoc, ← map_mul, Polynomial.natDegree_C_mul (mul_ne_zero hm hs)]
  exact Delta_natDegree n

/-! ## (d) (2.2) is the moment `(2e+5)! ζ(2e+2)/(12(2π)^{2e+2})`

The paper gives (2.2) in Bernoulli form; Proposition 2.2 needs it in moment form.  Euler's
formula `ζ(2k) = (-1)^{k+1}2^{2k-1}π^{2k}B_{2k}/(2k)!` is `Mathlib.hasSum_zeta_nat`, so the
identification is a theorem, not an assumption. -/

/-- Mathlib's `hasSum_zeta_nat` sums `n^{-2k}` over all `n : ℕ` (the `n = 0` term being `0`);
shift the index to the project's convention `∑_{v≥0}(v+1)^{-s}` (cf. `Zeta5.zeta5`). -/
lemma tsum_shift {k : ℕ} (hk : k ≠ 0) {a : ℝ}
    (hs : HasSum (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ k) a) :
    ∑' v : ℕ, (1 : ℝ) / ((v : ℝ) + 1) ^ k = a := by
  have h1 := (hasSum_nat_add_iff' (f := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ k) 1).2 hs
  rw [Finset.sum_range_one] at h1
  simp only [Nat.cast_zero, zero_pow hk, div_zero, sub_zero] at h1
  have h2 : (fun n : ℕ => (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ k)
      = fun v : ℕ => (1 : ℝ) / ((v : ℝ) + 1) ^ k := by
    funext v
    push_cast
    ring
  rw [h2] at h1
  exact h1.tsum_eq

/-- **(2.2) in moment form.**  The Bernoulli expression the paper writes for `μ(t^e)` equals
`(2e+5)! ζ(2e+2)/(12(2π)^{2e+2})`, which is `∫_0^∞ y^{2e} w(y) dy` for the weight `w` of
(2.10).  A known-answer control on (2.2) and on the `B_1 = -1/2` convention. -/
theorem muMono_eq_zeta (e : ℕ) :
    ((muMono e : ℚ) : ℝ)
      = (Nat.factorial (2 * e + 5) : ℝ)
          * (∑' v : ℕ, (1 : ℝ) / ((v : ℝ) + 1) ^ (2 * e + 2))
          / (12 * (2 * Real.pi) ^ (2 * e + 2)) := by
  have hk : e + 1 ≠ 0 := Nat.succ_ne_zero e
  have hzeta := hasSum_zeta_nat hk
  rw [show 2 * (e + 1) = 2 * e + 2 by ring] at hzeta
  rw [show 2 * e + 2 - 1 = 2 * e + 1 by omega] at hzeta
  have hsum : ∑' v : ℕ, (1 : ℝ) / ((v : ℝ) + 1) ^ (2 * e + 2)
      = (-1 : ℝ) ^ (e + 1 + 1) * 2 ^ (2 * e + 1) * Real.pi ^ (2 * e + 2)
          * ((_root_.bernoulli (2 * e + 2) : ℚ) : ℝ)
        / (Nat.factorial (2 * e + 2) : ℝ) :=
    tsum_shift (by omega) hzeta
  have hfac : (Nat.factorial (2 * e + 5) : ℝ)
      = ((2 * e + 5 : ℕ) : ℝ) * ((2 * e + 4 : ℕ) : ℝ) * ((2 * e + 3 : ℕ) : ℝ)
        * (Nat.factorial (2 * e + 2) : ℝ) := by
    have h5 : Nat.factorial (2 * e + 5) = (2 * e + 5) * Nat.factorial (2 * e + 4) := by
      rw [show 2 * e + 5 = (2 * e + 4) + 1 by omega, Nat.factorial_succ]
    have h4 : Nat.factorial (2 * e + 4) = (2 * e + 4) * Nat.factorial (2 * e + 3) := by
      rw [show 2 * e + 4 = (2 * e + 3) + 1 by omega, Nat.factorial_succ]
    have h3 : Nat.factorial (2 * e + 3) = (2 * e + 3) * Nat.factorial (2 * e + 2) := by
      rw [show 2 * e + 3 = (2 * e + 2) + 1 by omega, Nat.factorial_succ]
    rw [h5, h4, h3]
    push_cast
    ring
  have hneg : ((-1 : ℝ)) ^ (e + 1 + 1) = (-1 : ℝ) ^ e := by
    rw [pow_succ, pow_succ]
    ring
  have h2pow : (2 : ℝ) ^ (2 * e + 2) = 2 ^ (2 * e + 1) * 2 := by
    rw [show 2 * e + 2 = (2 * e + 1) + 1 by omega, pow_succ]
  have hfacne : (Nat.factorial (2 * e + 2) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero _
  have hpine : (Real.pi : ℝ) ^ (2 * e + 2) ≠ 0 := pow_ne_zero _ Real.pi_ne_zero
  rw [hsum, hfac, hneg, mul_pow, h2pow]
  simp only [muMono]
  push_cast
  field_simp
  ring

/-! ## Axiom audit

These `#print axioms` lines appear in the build log.  Everything in this file is proved
from `[propext, Classical.choice, Quot.sound]` only — no `sorryAx`, without exception. -/

#print axioms Zeta5.Functional.partial_fractions
#print axioms Zeta5.Functional.partial_fraction_unique
#print axioms Zeta5.Functional.muOver_add
#print axioms Zeta5.Functional.muOver_C_mul
#print axioms Zeta5.Functional.muOver_poly
#print axioms Zeta5.Functional.muOver_cof
#print axioms Zeta5.Functional.muOver_coeff_one
#print axioms Zeta5.Functional.Delta_coeff_h
#print axioms Zeta5.Functional.Gcoef_factor
#print axioms Zeta5.Functional.prod_offDiag
#print axioms Zeta5.Functional.eq_2_9
#print axioms Zeta5.Functional.Delta_natDegree
#print axioms Zeta5.Functional.Q_natDegree
#print axioms Zeta5.Functional.muMono_eq_zeta

end Functional

end

end Zeta5
