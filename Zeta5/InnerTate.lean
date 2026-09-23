/-
Zeta5/InnerTate.lean

PART 1 OF THE PROOF OF `Zeta5.Section3.entry_bounds_4_2_4_3` (Proposition 4.1, pp. 10–11).

The finite replacement for the Tate-algebra part of Lemma 3.2 (p. 7).

The paper evaluates `τ_X(g)` through the distribution formula (3.7),
`τ_X(g) = p^{-4} ∑_{a<p} τ^ext_Y(g(a+px))`, in which the far poles of `g(a+px)` are expanded
as convergent series in the Tate algebra `ℚ_p⟨z⟩`.  Here nothing infinite is formed.  Two
exact finite statements replace it:

* **`raabe_tau`** — the polynomial half of (3.7): `m⁴ τ(P) = ∑_{a<m} τ(P(a + m z))` for every
  polynomial `P` and every `m ≥ 1` (Raabe's multiplication theorem, DLMF 24.4.18, after three
  differentiations).  Proved here from the difference identity `L(P(x+1)) = L(P) + P'(0)`
  (`Lfun_comp_one_add`, i.e. Mathlib's `sum_bernoulli`) by a uniqueness argument: the defect
  `Λ(P) = ∑_a L(P(a+mz)) − m L(P)` is shift-invariant, hence vanishes on every
  `(x+1)^{k+1} − x^{k+1}`, hence on every `x^k` by induction.  No axiom.
* **`class_bound`** — the per-class estimate: if the polynomial `π = P(a+pz)` satisfies an
  exact polynomial identity `π·T·D = p^e (U·N_f − D·R) − T·F`, where `T` is the monic
  near-pole polynomial, `D` the far-pole polynomial (unit constant term, `v_p([z^k]D) ≥ k`),
  `U` the near-zero polynomial (`deg U ≤ p+1`), `N_f` the far-zero polynomial and `F` the
  far-pole partial-fraction numerator, then `v_p(τ(π)) ≥ min(e, f+2)` where
  `v_p([z^k]F) ≥ f + k`.  The proof multiplies by a *truncated* inverse `I_n` of `D`
  (`D·I_n = 1 − q^n` with `v_p(q^n) ≥ n`, an exact geometric-series identity) and takes `n`
  large; the error term has valuation `≥ n − 1`, so a single finite `n` suffices.

This is the finite form of "far factors are units times convergent series in `pz`" (p. 11)
together with Lemma 3.1's degree argument.
-/
import Zeta5.LocalFunctional

namespace Zeta5

namespace InnerEntries

open Polynomial Finset

noncomputable section

/-! # §1.  `v_p(x) ≥ c`, multiplicatively, and coefficient profiles -/

section Val

variable {p : ℕ} [hpf : Fact p.Prime]

/-- `v_p(x) ≥ c`, with the convention `v_p(0) = +∞`, in the multiplicative form
`|x|_p ≤ p^{-c}`. -/
def vge (p : ℕ) (x : ℚ) (c : ℤ) : Prop := padicNorm p x ≤ (p : ℚ) ^ (-c)

/-- **Tate-type decay** of the coefficients of a polynomial in `z`:
`v_p([z^k]F) ≥ f + k` for every `k`.  (The far factors `(a − r) + pz` and their products
have this property with `f = 0`: "units times convergent series in `pz`", p. 11.) -/
def Tate (p : ℕ) (F : ℚ[X]) (f : ℤ) : Prop := ∀ k : ℕ, vge p (F.coeff k) (f + k)

omit hpf in
lemma vGAtLeast_iff_vge {A : ℚ[X]} {c : ℤ} [Fact p.Prime] :
    vGAtLeast p A c ↔ ∀ i, vge p (A.coeff i) c := vGAtLeast_iff A c

lemma p_pos_q : (0 : ℚ) < (p : ℚ) := by exact_mod_cast hpf.out.pos

lemma p_one_lt_q : (1 : ℚ) < (p : ℚ) := by exact_mod_cast hpf.out.one_lt

lemma zpow_p_pos (c : ℤ) : (0 : ℚ) < (p : ℚ) ^ c := zpow_pos p_pos_q c

lemma vge_zero (c : ℤ) : vge p 0 c := by
  unfold vge
  rw [padicNorm.zero]
  exact le_of_lt (zpow_p_pos _)

lemma vge_mono {x : ℚ} {c c' : ℤ} (h : c' ≤ c) (hx : vge p x c) : vge p x c' :=
  le_trans hx (zpow_le_zpow_right₀ (le_of_lt p_one_lt_q) (by omega))

lemma vge_mul {x y : ℚ} {c d : ℤ} (hx : vge p x c) (hy : vge p y d) :
    vge p (x * y) (c + d) := by
  unfold vge at *
  rw [padicNorm.mul, neg_add, zpow_add₀ (ne_of_gt p_pos_q)]
  exact mul_le_mul hx hy (padicNorm.nonneg _) (le_of_lt (zpow_p_pos _))

lemma vge_add {x y : ℚ} {c : ℤ} (hx : vge p x c) (hy : vge p y c) : vge p (x + y) c :=
  le_trans padicNorm.nonarchimedean (max_le hx hy)

lemma vge_neg {x : ℚ} {c : ℤ} (hx : vge p x c) : vge p (-x) c := by
  unfold vge at *
  rwa [padicNorm.neg]

lemma vge_sub {x y : ℚ} {c : ℤ} (hx : vge p x c) (hy : vge p y c) : vge p (x - y) c := by
  rw [sub_eq_add_neg]
  exact vge_add hx (vge_neg hy)

lemma vge_sum {ι : Type*} {s : Finset ι} {f : ι → ℚ} {c : ℤ} (h : ∀ i ∈ s, vge p (f i) c) :
    vge p (∑ i ∈ s, f i) c :=
  padicNorm.sum_le' (fun i hi => h i hi) (le_of_lt (zpow_p_pos _))

lemma vge_zero_iff {x : ℚ} : vge p x 0 ↔ padicNorm p x ≤ 1 := by
  simp [vge]

lemma vge_intCast (k : ℤ) : vge p (k : ℚ) 0 := vge_zero_iff.2 (padicNorm.of_int k)

lemma vge_natCast (k : ℕ) : vge p (k : ℚ) 0 := by
  have := vge_intCast (p := p) (k : ℤ)
  simpa using this

lemma vge_one : vge p 1 0 := by simpa using vge_natCast (p := p) 1

lemma vge_p : vge p (p : ℚ) 1 := by
  unfold vge
  rw [padicNorm.padicNorm_p_of_prime, zpow_neg_one]

lemma vge_zpow_p (e : ℤ) : vge p ((p : ℚ) ^ e) e := by
  unfold vge
  have hne : ((p : ℚ) ^ e) ≠ 0 := ne_of_gt (zpow_p_pos e)
  rw [padicNorm.eq_zpow_of_nonzero hne, padicValRat.zpow, padicValRat.self hpf.out.one_lt,
    mul_one]

lemma vge_pow_p (e : ℕ) : vge p ((p : ℚ) ^ e) e := by
  have := vge_zpow_p (p := p) (e : ℤ)
  simpa using this

lemma vge_of_norm_eq_one {x : ℚ} (hx : padicNorm p x = 1) : vge p x 0 :=
  vge_zero_iff.2 (le_of_eq hx)

lemma vge_inv_of_norm_eq_one {x : ℚ} (hx : padicNorm p x = 1) : vge p x⁻¹ 0 := by
  refine vge_zero_iff.2 (le_of_eq ?_)
  rw [inv_eq_one_div, padicNorm.div, padicNorm.one, hx, div_one]

/-- `v_p(x) ≥ c` iff `x = 0` or `c ≤ v_p(x)`. -/
lemma vge_iff_val {x : ℚ} {c : ℤ} : vge p x c ↔ x = 0 ∨ c ≤ padicValRat p x := by
  constructor
  · intro h
    by_cases h0 : x = 0
    · exact Or.inl h0
    · refine Or.inr ?_
      unfold vge at h
      rw [padicNorm.eq_zpow_of_nonzero h0] at h
      have := (zpow_le_zpow_iff_right₀ p_one_lt_q).1 h
      omega
  · rintro (rfl | h)
    · exact vge_zero c
    · by_cases h0 : x = 0
      · rw [h0]; exact vge_zero c
      · unfold vge
        rw [padicNorm.eq_zpow_of_nonzero h0]
        exact (zpow_le_zpow_iff_right₀ p_one_lt_q).2 (by omega)

/-! ### Tate decay -/

lemma Tate_mono {F : ℚ[X]} {f f' : ℤ} (h : f' ≤ f) (hF : Tate p F f) : Tate p F f' :=
  fun k => vge_mono (by omega) (hF k)

lemma Tate_mul {F G : ℚ[X]} {f g : ℤ} (hF : Tate p F f) (hG : Tate p G g) :
    Tate p (F * G) (f + g) := by
  intro k
  rw [coeff_mul]
  refine vge_sum fun x hx => ?_
  have hk : x.1 + x.2 = k := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
  refine vge_mono ?_ (vge_mul (hF x.1) (hG x.2))
  have : ((x.1 : ℕ) : ℤ) + ((x.2 : ℕ) : ℤ) = (k : ℤ) := by exact_mod_cast hk
  omega

lemma Tate_add {F G : ℚ[X]} {f : ℤ} (hF : Tate p F f) (hG : Tate p G f) : Tate p (F + G) f :=
  fun k => by rw [coeff_add]; exact vge_add (hF k) (hG k)

lemma Tate_neg {F : ℚ[X]} {f : ℤ} (hF : Tate p F f) : Tate p (-F) f :=
  fun k => by rw [coeff_neg]; exact vge_neg (hF k)

lemma Tate_sub {F G : ℚ[X]} {f : ℤ} (hF : Tate p F f) (hG : Tate p G f) : Tate p (F - G) f :=
  fun k => by rw [coeff_sub]; exact vge_sub (hF k) (hG k)

lemma Tate_zero (f : ℤ) : Tate p 0 f := fun k => by rw [coeff_zero]; exact vge_zero _

lemma Tate_sum {ι : Type*} {s : Finset ι} {F : ι → ℚ[X]} {f : ℤ}
    (h : ∀ i ∈ s, Tate p (F i) f) : Tate p (∑ i ∈ s, F i) f := by
  intro k
  rw [finsetSum_coeff]
  exact vge_sum fun i hi => h i hi k

lemma Tate_C {c : ℚ} {e : ℤ} (hc : vge p c e) : Tate p (C c) e := by
  intro k
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simpa using hc
  · rw [coeff_C, if_neg (by omega)]
    exact vge_zero _

lemma Tate_one : Tate p 1 0 := by
  simpa using Tate_C (p := p) vge_one

lemma Tate_C_mul {c : ℚ} {e f : ℤ} {F : ℚ[X]} (hc : vge p c e) (hF : Tate p F f) :
    Tate p (C c * F) (e + f) := Tate_mul (Tate_C hc) hF

lemma Tate_pow {F : ℚ[X]} (hF : Tate p F 0) (k : ℕ) : Tate p (F ^ k) 0 := by
  induction k with
  | zero => simpa using Tate_one (p := p)
  | succ k ih => simpa [pow_succ] using Tate_mul ih hF

lemma Tate_prod {ι : Type*} [DecidableEq ι] {s : Finset ι} {F : ι → ℚ[X]}
    (h : ∀ i ∈ s, Tate p (F i) 0) : Tate p (∏ i ∈ s, F i) 0 := by
  induction s using Finset.induction_on with
  | empty => simpa using Tate_one (p := p)
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    simpa using Tate_mul (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- A far factor `b + pz` with `b ∈ ℤ_p` has Tate decay `0`. -/
lemma Tate_lin {b : ℚ} (hb : vge p b 0) : Tate p (C b + C (p : ℚ) * X) 0 := by
  intro k
  rw [coeff_add, coeff_C, coeff_C_mul, coeff_X]
  rcases k with _ | _ | k
  · simpa using hb
  · simpa using vge_p (p := p)
  · simp only [if_neg (show k + 1 + 1 ≠ 0 by omega), if_neg (show 1 ≠ k + 1 + 1 by omega),
      mul_zero, add_zero]
    exact vge_zero _

lemma vGAtLeast_of_Tate {F : ℚ[X]} {f : ℤ} (hF : Tate p F f) : vGAtLeast p F f :=
  vGAtLeast_iff_vge.2 fun k => vge_mono (by omega) (hF k)

lemma vGAtLeast_X_pow (j : ℕ) : vGAtLeast p ((X : ℚ[X]) ^ j) 0 := by
  refine vGAtLeast_iff_vge.2 fun i => ?_
  rw [coeff_X_pow]
  split_ifs
  · exact vge_one
  · exact vge_zero _

/-- `v_p^G(A) ≥ c` and `T` monic integral give `v_p^G(A div T) ≥ c`. -/
lemma vGAtLeast_divByMonic {A T : ℚ[X]} {c : ℤ} (hT : T.Monic) (hTint : vGAtLeast p T 0)
    (hA : vGAtLeast p A c) : vGAtLeast p (A /ₘ T) c := by
  have hsplit : A = C ((p : ℚ) ^ c) * (C ((p : ℚ) ^ (-c)) * A) := by
    rw [← mul_assoc, ← C_mul, ← zpow_add₀ (ne_of_gt p_pos_q), add_neg_cancel, zpow_zero, C_1,
      one_mul]
  have hint : vGAtLeast p (C ((p : ℚ) ^ (-c)) * A) 0 := by
    simpa using vGAtLeast_mul (vGAtLeast_C_zpow_p (p := p) (-c)) hA
  have hdiv := (vGAtLeast_divMod_of_monic hT hTint hint).1
  rw [hsplit, ← smul_eq_C_mul, smul_divByMonic, smul_eq_C_mul]
  simpa using vGAtLeast_mul (vGAtLeast_C_zpow_p (p := p) c) hdiv

/-! ### Bounds for `τ` -/

lemma vge_kappa (h7 : 7 ≤ p) (d : ℕ) : vge p (kappa d) (-1) := by
  unfold vge
  simpa using padicNorm_le_of_neg_one_le (neg_one_le_padicValRat_kappa p h7 d)

lemma vge_kappa_of_le (h7 : 7 ≤ p) {d : ℕ} (hd : d ≤ p + 1) : vge p (kappa d) 0 :=
  vge_zero_iff.2 (padicNorm_le_one_of_nonneg (padicValRat_kappa_nonneg p h7 hd))

/-- `τ` of an integral polynomial loses at most one power of `p` (`‖τ‖ ≤ p`, p. 6). -/
theorem tau_int (h7 : 7 ≤ p) {V : ℚ[X]} (hV : vGAtLeast p V 0) : vge p (tau V) (-1) := by
  rw [tau_eq_sum V (lt_add_one _)]
  refine vge_sum fun d _ => ?_
  simpa using vge_mul (vGAtLeast_iff_vge.1 hV d) (vge_kappa h7 d)

/-- `τ` of an integral polynomial of degree `≤ p+1` is integral (`κ_d ∈ ℤ_p`, `d ≤ p+1`). -/
theorem tau_int_of_deg (h7 : 7 ≤ p) {V : ℚ[X]} (hV : vGAtLeast p V 0)
    (hdeg : V.natDegree ≤ p + 1) : vge p (tau V) 0 := by
  rw [tau_eq_sum V (n := p + 2) (by omega)]
  refine vge_sum fun d hd => ?_
  have hd' : d ≤ p + 1 := by simp only [Finset.mem_range] at hd; omega
  simpa using vge_mul (vGAtLeast_iff_vge.1 hV d) (vge_kappa_of_le h7 hd')

/-- `v_p^G(V) ≥ c` gives `v_p(τ(V)) ≥ c − 1`. -/
theorem tau_vGAtLeast (h7 : 7 ≤ p) {V : ℚ[X]} {c : ℤ} (hV : vGAtLeast p V c) :
    vge p (tau V) (c - 1) := by
  have hsplit : V = C ((p : ℚ) ^ c) * (C ((p : ℚ) ^ (-c)) * V) := by
    rw [← mul_assoc, ← C_mul, ← zpow_add₀ (ne_of_gt p_pos_q), add_neg_cancel, zpow_zero, C_1,
      one_mul]
  have hint : vGAtLeast p (C ((p : ℚ) ^ (-c)) * V) 0 := by
    simpa using vGAtLeast_mul (vGAtLeast_C_zpow_p (p := p) (-c)) hV
  rw [hsplit, tau_C_mul]
  have := vge_mul (vge_zpow_p (p := p) c) (tau_int h7 hint)
  refine vge_mono (le_of_eq ?_) this
  ring

/-- `τ` of a polynomial with Tate decay `f`: `v_p(τ(F)) ≥ f + 2` (the `κ_d` vanish for
`d ≤ 2` and have `v_p ≥ -1` in general). -/
theorem tau_Tate (h7 : 7 ≤ p) {F : ℚ[X]} {f : ℤ} (hF : Tate p F f) : vge p (tau F) (f + 2) := by
  rw [tau_eq_sum F (lt_add_one _)]
  refine vge_sum fun d _ => ?_
  by_cases hd : d < 3
  · have hk : kappa d = 0 := by simp [kappa, hd]
    rw [hk, mul_zero]
    exact vge_zero _
  · refine vge_mono ?_ (vge_mul (hF d) (vge_kappa h7 d))
    push_neg at hd
    have : (3 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
    omega

end Val

/-! # §2.  Raabe's multiplication theorem for `τ` (the polynomial half of (3.7)) -/

section Raabe

/-- The defect of the distribution relation for `L`:
`Λ_m(P) = ∑_{a<m} L(P(a + m z)) − m·L(P)`. -/
def LamD (m : ℕ) (P : ℚ[X]) : ℚ :=
  ∑ a ∈ range m, Lfun (P.comp (C (a : ℚ) + C (m : ℚ) * X)) - (m : ℚ) * Lfun P

lemma LamD_add (m : ℕ) (P Q : ℚ[X]) : LamD m (P + Q) = LamD m P + LamD m Q := by
  simp only [LamD, add_comp, Lfun_add, Finset.sum_add_distrib]
  ring

lemma LamD_C_mul (m : ℕ) (c : ℚ) (P : ℚ[X]) : LamD m (C c * P) = c * LamD m P := by
  simp only [LamD, mul_comp, C_comp, Lfun_C_mul, ← Finset.mul_sum]
  ring

lemma LamD_sub (m : ℕ) (P Q : ℚ[X]) : LamD m (P - Q) = LamD m P - LamD m Q := by
  have h := LamD_C_mul m (-1) Q
  have hneg : C (-1 : ℚ) * Q = -Q := by rw [map_neg, map_one, neg_one_mul]
  rw [hneg] at h
  rw [sub_eq_add_neg, LamD_add, h]
  ring

lemma LamD_sum {ι : Type*} (m : ℕ) (s : Finset ι) (f : ι → ℚ[X]) :
    LamD m (∑ i ∈ s, f i) = ∑ i ∈ s, LamD m (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp [LamD]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, LamD_add, ih]

/-- `Λ_m` in terms of its values on monomials, over any range covering the degree. -/
lemma LamD_eq_sum (m : ℕ) (P : ℚ[X]) {N : ℕ} (hN : P.natDegree < N) :
    LamD m P = ∑ j ∈ range N, P.coeff j * LamD m (X ^ j) := by
  conv_lhs => rw [P.as_sum_range_C_mul_X_pow' hN]
  rw [LamD_sum]
  exact Finset.sum_congr rfl fun j _ => LamD_C_mul m _ _

/-- **`Λ_m` is shift-invariant**: `Λ_m(P(x+1)) = Λ_m(P)`.  The sum over `a` telescopes to
`L(G(x+1)) − L(G)` with `G(x) = P(mx)`, which is `G'(0) = m P'(0)` by the difference
identity; the same `m P'(0)` comes out of `m·L(P(x+1)) = m(L(P) + P'(0))`. -/
lemma LamD_shift (m : ℕ) (P : ℚ[X]) : LamD m (P.comp (X + 1)) = LamD m P := by
  set f : ℕ → ℚ := fun a => Lfun (P.comp (C (a : ℚ) + C (m : ℚ) * X)) with hf
  have hsh : ∀ a : ℕ, Lfun ((P.comp (X + 1)).comp (C (a : ℚ) + C (m : ℚ) * X)) = f (a + 1) := by
    intro a
    simp only [hf, comp_assoc, add_comp, X_comp, one_comp]
    congr 2
    push_cast
    rw [map_add, map_one]
    ring
  have htel : ∑ a ∈ range m, f (a + 1) = ∑ a ∈ range m, f a + (f m - f 0) := by
    have := Finset.sum_range_sub f m
    rw [Finset.sum_sub_distrib] at this
    linarith
  -- `f m - f 0 = m P'(0)`
  set G : ℚ[X] := P.comp (C (m : ℚ) * X) with hG
  have hGm : P.comp (C ((m : ℕ) : ℚ) + C (m : ℚ) * X) = G.comp (X + 1) := by
    rw [hG, comp_assoc, mul_comp, C_comp, X_comp, mul_add, mul_one, add_comm]
  have hG0 : P.comp (C ((0 : ℕ) : ℚ) + C (m : ℚ) * X) = G := by
    rw [hG]
    simp
  have hdiff : f m - f 0 = (m : ℚ) * (derivative P).eval 0 := by
    simp only [hf]
    rw [hGm, hG0, Lfun_comp_one_add, hG, derivative_comp]
    simp [derivative_mul, eval_comp]
  have hL := Lfun_comp_one_add P
  simp only [LamD]
  rw [Finset.sum_congr rfl fun a _ => hsh a, htel, hdiff, hL]
  ring

/-- `Λ_m(x^k) = 0` for every `k`, by strong induction: apply shift-invariance to `x^{k+1}`. -/
lemma LamD_X_pow (m : ℕ) (k : ℕ) : LamD m (X ^ k) = 0 := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    have hsh := LamD_shift m ((X : ℚ[X]) ^ (k + 1))
    have hcomp : ((X : ℚ[X]) ^ (k + 1)).comp (X + 1) = (X + 1) ^ (k + 1) := by
      simp
    rw [hcomp] at hsh
    have hdeg1 : ((X + 1 : ℚ[X]) ^ (k + 1)).natDegree < k + 2 := by
      have h1 : (X + 1 : ℚ[X]).natDegree = 1 := by
        simpa using natDegree_X_add_C (1 : ℚ)
      have : ((X + 1 : ℚ[X]) ^ (k + 1)).natDegree = k + 1 := by
        rw [natDegree_pow, h1, mul_one]
      omega
    have hdeg2 : ((X : ℚ[X]) ^ (k + 1)).natDegree < k + 2 := by
      rw [natDegree_X_pow]; omega
    rw [LamD_eq_sum m _ hdeg1, LamD_eq_sum m _ hdeg2] at hsh
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ] at hsh
    have hlow : ∀ j ∈ range k, ((X + 1 : ℚ[X]) ^ (k + 1)).coeff j * LamD m (X ^ j) = 0 := by
      intro j hj
      rw [ih j (Finset.mem_range.1 hj), mul_zero]
    have hlow2 : ∀ j ∈ range k, ((X : ℚ[X]) ^ (k + 1)).coeff j * LamD m (X ^ j) = 0 := by
      intro j hj
      rw [ih j (Finset.mem_range.1 hj), mul_zero]
    rw [Finset.sum_eq_zero hlow, Finset.sum_eq_zero hlow2] at hsh
    rw [coeff_X_add_one_pow, coeff_X_add_one_pow, coeff_X_pow, coeff_X_pow, Nat.choose_self,
      Nat.choose_succ_self_right] at hsh
    simp only [if_neg (show k ≠ k + 1 by omega), ↓reduceIte, Nat.cast_one, one_mul,
      zero_mul, zero_add] at hsh
    have hk : ((k + 1 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    have : ((k + 1 : ℕ) : ℚ) * LamD m (X ^ k) = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_left hk

/-- **The distribution relation for `L`** (Raabe for the Bernoulli numbers):
`m·L(P) = ∑_{a<m} L(P(a + m z))`. -/
theorem Lfun_distribution (m : ℕ) (P : ℚ[X]) :
    (m : ℚ) * Lfun P = ∑ a ∈ range m, Lfun (P.comp (C (a : ℚ) + C (m : ℚ) * X)) := by
  have h : LamD m P = 0 := by
    rw [LamD_eq_sum m P (lt_add_one _)]
    exact Finset.sum_eq_zero fun j _ => by rw [LamD_X_pow, mul_zero]
  simp only [LamD] at h
  linarith

/-- The third derivative of `P(a + m z)` is `m³ P'''(a + m z)`. -/
lemma derivative3_comp_lin (m a : ℚ) (P : ℚ[X]) :
    derivative (derivative (derivative (P.comp (C a + C m * X))))
      = C (m ^ 3) * (derivative (derivative (derivative P))).comp (C a + C m * X) := by
  have hstep : ∀ Q : ℚ[X], derivative (Q.comp (C a + C m * X))
      = C m * (derivative Q).comp (C a + C m * X) := by
    intro Q
    rw [derivative_comp]
    simp
  simp only [hstep, derivative_C_mul]
  rw [show (m ^ 3 : ℚ) = m * m * m by ring, C_mul, C_mul]
  ring

/-- **Raabe for `τ`**: `m⁴ τ(P) = ∑_{a<m} τ(P(a + m z))`.  This is the statement of (3.7) for
polynomials ("For polynomials, (3.7) follows from Bernoulli multiplication [9, (24.4.18)]
after three differentiations", p. 7). -/
theorem raabe_tau (m : ℕ) (hm : 0 < m) (P : ℚ[X]) :
    ((m : ℚ)) ^ 4 * tau P = ∑ a ∈ range m, tau (P.comp (C (a : ℚ) + C (m : ℚ) * X)) := by
  have _ := hm
  simp only [tau, derivative3_comp_lin, Lfun_C_mul]
  rw [← Finset.sum_div, ← Finset.mul_sum, ← Lfun_distribution m]
  ring

end Raabe

/-! # §3.  The per-class estimate -/

section ClassBound

variable {p : ℕ} [hpf : Fact p.Prime]

lemma sum_divByMonic {ι : Type*} (s : Finset ι) (f : ι → ℚ[X]) (T : ℚ[X]) :
    (∑ i ∈ s, f i) /ₘ T = ∑ i ∈ s, (f i /ₘ T) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, add_divByMonic, ih]

lemma C_mul_divByMonic (c : ℚ) (A T : ℚ[X]) : (C c * A) /ₘ T = C c * (A /ₘ T) := by
  rw [← smul_eq_C_mul, ← smul_eq_C_mul, smul_divByMonic]

/-- **Lemma 3.1's core, for one class**: `U ∈ ℤ_p[z]` of degree `≤ p+1`, `G` of Tate decay `0`,
`T` monic integral; then `τ((U·G) div T) ∈ ℤ_p`.  Write `G = ∑_j g_j z^j` with
`v_p(g_j) ≥ j`: the `j = 0` term has quotient degree `≤ p+1`, and for `j ≥ 1` the factor `g_j`
absorbs the one power of `p` that `τ` can lose. -/
theorem tau_mul_divByMonic (h7 : 7 ≤ p) {T U G : ℚ[X]} (hT : T.Monic)
    (hTint : vGAtLeast p T 0) (hU : vGAtLeast p U 0) (hUdeg : U.natDegree ≤ p + 1)
    (hG : Tate p G 0) : vge p (tau ((U * G) /ₘ T)) 0 := by
  have hexp : U * G = ∑ j ∈ range (G.natDegree + 1), C (G.coeff j) * (X ^ j * U) := by
    conv_lhs => rw [G.as_sum_range_C_mul_X_pow]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hexp, sum_divByMonic, tau_sum]
  refine vge_sum fun j _ => ?_
  rw [C_mul_divByMonic, tau_C_mul]
  have hint : vGAtLeast p ((X ^ j * U) /ₘ T) 0 :=
    (vGAtLeast_divMod_of_monic hT hTint (by simpa using vGAtLeast_mul (vGAtLeast_X_pow j) hU)).1
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · have hdeg : ((X ^ 0 * U) /ₘ T).natDegree ≤ p + 1 := by
      rw [natDegree_divByMonic _ hT]
      simp only [pow_zero, one_mul]
      omega
    simpa using vge_mul (hG 0) (tau_int_of_deg h7 hint hdeg)
  · refine vge_mono ?_ (vge_mul (hG j) (tau_int h7 hint))
    have : (1 : ℤ) ≤ (j : ℤ) := by exact_mod_cast hj
    omega

/-- **The per-class estimate** (the finite form of Lemma 3.1 applied to one summand of (3.7)).

`π` is the polynomial `P(a + pz)`, `P` the polynomial part of `g`; `T` the monic product of the
near poles in `z`; `D` the product of the far pole factors `(a − r) + pz`; `U` the near zeros
(degree `≤ p+1`); `N_f` the far zeros; `R` the near partial-fraction numerator (degree
`< deg T`); `F` the far partial-fraction numerator. -/
theorem class_bound (h7 : 7 ≤ p) {π T U Nf D R F : ℚ[X]} {e f : ℤ}
    (hT : T.Monic) (hTint : vGAtLeast p T 0)
    (hU : vGAtLeast p U 0) (hUdeg : U.natDegree ≤ p + 1)
    (hNf : Tate p Nf 0) (hD : Tate p D 0) (hD0 : padicNorm p (D.coeff 0) = 1)
    (hR : vGAtLeast p R 0) (hRdeg : R.degree < T.degree)
    (hF : Tate p F f) (hπ : vGAtLeast p π 0)
    (hid : π * T * D = C ((p : ℚ) ^ e) * (U * Nf - D * R) - T * F) :
    vge p (tau π) (min e (f + 2)) := by
  classical
  set d0 : ℚ := D.coeff 0 with hd0
  have hd0ne : d0 ≠ 0 := by
    intro h
    rw [h, padicNorm.zero] at hD0
    exact zero_ne_one hD0
  -- `D = d₀(1 − q)` with `q` of Tate decay `0` and no constant term
  set q : ℚ[X] := 1 - C d0⁻¹ * D with hq
  have hDq : D = C d0 * (1 - q) := by
    rw [hq, sub_sub_cancel, ← mul_assoc, ← C_mul, mul_inv_cancel₀ hd0ne, C_1, one_mul]
  have hqT : Tate p q 0 := by
    refine Tate_sub Tate_one ?_
    simpa using Tate_C_mul (vge_inv_of_norm_eq_one hD0) hD
  have hq0 : q.coeff 0 = 0 := by
    rw [hq, coeff_sub, coeff_one_zero, coeff_C_mul, inv_mul_cancel₀ hd0ne, sub_self]
  -- the truncation order
  set n : ℕ := (max e (f + 2)).toNat + 2 with hn
  have hn1 : max e (f + 2) + 1 ≤ (n : ℤ) - 1 := by
    have := Int.self_le_toNat (max e (f + 2))
    rw [hn]; push_cast; omega
  -- the truncated inverse `I = d₀⁻¹ ∑_{k<n} q^k`, with `D·I = 1 − q^n`
  set I : ℚ[X] := C d0⁻¹ * ∑ k ∈ range n, q ^ k with hI
  have hDI : D * I = 1 - q ^ n := by
    rw [hDq, hI]
    have : C d0 * (1 - q) * (C d0⁻¹ * ∑ k ∈ range n, q ^ k)
        = (C d0 * C d0⁻¹) * ((1 - q) * ∑ k ∈ range n, q ^ k) := by ring
    rw [this, ← C_mul, mul_inv_cancel₀ hd0ne, C_1, one_mul, mul_neg_geom_sum]
  have hIT : Tate p I 0 := by
    simpa using Tate_C_mul (vge_inv_of_norm_eq_one hD0) (Tate_sum fun k _ => Tate_pow hqT k)
  -- `v_p^G(q^n) ≥ n`
  have hqn : vGAtLeast p (q ^ n) n := by
    refine vGAtLeast_iff_vge.2 fun k => ?_
    have hdvd : X ^ n ∣ q ^ n := pow_dvd_pow_of_dvd (X_dvd_iff.2 hq0) n
    obtain ⟨s, hs⟩ := hdvd
    by_cases hk : k < n
    · have : (q ^ n).coeff k = 0 := by
        rw [hs, coeff_X_pow_mul', if_neg (by omega)]
      rw [this]
      exact vge_zero _
    · have hk' : (n : ℤ) ≤ (k : ℤ) := by push_neg at hk; exact_mod_cast hk
      exact vge_mono (by omega) (Tate_pow hqT n k)
  -- the main identity: `π = p^e((U·N_f I) div T + (q^n R) div T) + (π q^n − F I)`
  have hmain : π = C ((p : ℚ) ^ e) * ((U * (Nf * I)) /ₘ T + (q ^ n * R) /ₘ T)
      + (π * q ^ n - F * I) := by
    have h1 : π * T = C ((p : ℚ) ^ e) * (U * (Nf * I) - R + q ^ n * R)
        + T * (π * q ^ n - F * I) := by
      have hmulI : π * T * D * I = (C ((p : ℚ) ^ e) * (U * Nf - D * R) - T * F) * I := by
        rw [hid]
      have e1 : π * T * D * I = π * T * (1 - q ^ n) := by rw [mul_assoc (π * T), hDI]
      have e2 : (C ((p : ℚ) ^ e) * (U * Nf - D * R) - T * F) * I
          = C ((p : ℚ) ^ e) * (U * (Nf * I) - (D * I) * R) - T * (F * I) := by ring
      rw [e1, e2, hDI] at hmulI
      linear_combination hmulI
    have h2 : π = (π * T) /ₘ T := by
      rw [mul_comm]; exact (mul_divByMonic_cancel_left π hT).symm
    have hR0 : R /ₘ T = 0 := (divByMonic_eq_zero_iff hT).2 hRdeg
    calc π = (π * T) /ₘ T := h2
      _ = (C ((p : ℚ) ^ e) * (U * (Nf * I) - R + q ^ n * R) + T * (π * q ^ n - F * I)) /ₘ T := by
          rw [h1]
      _ = C ((p : ℚ) ^ e) * ((U * (Nf * I)) /ₘ T + (q ^ n * R) /ₘ T)
          + (π * q ^ n - F * I) := by
          rw [add_divByMonic, mul_divByMonic_cancel_left _ hT, C_mul_divByMonic,
            add_divByMonic, sub_divByMonic, hR0, sub_zero]
  -- valuations of the four pieces
  have A1 : vge p (tau ((U * (Nf * I)) /ₘ T)) 0 :=
    tau_mul_divByMonic h7 hT hTint hU hUdeg (by simpa using Tate_mul hNf hIT)
  have A2 : vge p (tau ((q ^ n * R) /ₘ T)) ((n : ℤ) - 1) := by
    refine tau_vGAtLeast h7 (vGAtLeast_divByMonic hT hTint ?_)
    simpa using vGAtLeast_mul hqn hR
  have A3 : vge p (tau (π * q ^ n)) ((n : ℤ) - 1) :=
    tau_vGAtLeast h7 (by simpa using vGAtLeast_mul hπ hqn)
  have A4 : vge p (tau (F * I)) (f + 2) := tau_Tate h7 (by simpa using Tate_mul hF hIT)
  rw [hmain, tau_add, tau_C_mul, tau_add, tau_sub]
  refine vge_add ?_ (vge_sub ?_ ?_)
  · have h12 : vge p (tau ((U * (Nf * I)) /ₘ T) + tau ((q ^ n * R) /ₘ T)) 0 :=
      vge_add A1 (vge_mono (by omega) A2)
    refine vge_mono ?_ (by simpa using vge_mul (vge_zpow_p (p := p) e) h12)
    exact min_le_left _ _
  · exact vge_mono (by omega) A3
  · exact vge_mono (min_le_right _ _) A4

end ClassBound

end

end InnerEntries

end Zeta5
