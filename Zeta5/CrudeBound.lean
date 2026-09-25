/-
Zeta5/CrudeBound.lean

**(3.12), THE CRUDE SMALL-PRIME BOUND** (p. 9) of

    A. Fauzan, "ζ(5) is irrational", 17 September 2026.

    v_p^G(F_K) ≥ -6h⌊log_p(5K)⌋ - h v_p(24)     for every prime p.                  (3.12)

The paper's derivation, in one sentence (p. 9): *"We apply Lemma 3.3 in a basis that becomes
integer-valued under `t = -x²` … The triangular change of basis gives (3.11).  The pullback
numerator has degree at most `12N + 4h + 1`.  Thus `max(2K, d+1) ≤ 5K`, and Lemma 3.3 proves
(3.12)."*

This file carries out that sentence.  Its contents, in the paper's order:

  §1   p. 9   the basis `q_0 = 1`, `q_i(t) = (-1)^i 2t D_{i-1}(t)/(2i)!` and
              `f_i(t) = (D_N(t)/(N!)²)³ q_i(t)`, with `deg q_i = i` and `lead q_i`.
  §1b  p. 9   the two printed binomial identities that make the basis integer-valued under
              `t = -x²`: `q_i(-z²) = C(z+i,2i) + C(z+i-1,2i)` (`qb_pullback_int`) and
              `D_N(-z²)/(N!)² = C(N-z,N)C(N+z,N)` (`D_pullback_int`), hence
              `fb_pullback_int`.  PROVED.
  §2   p. 9   **(3.11)**, `F_K(X) = det[(K!)² μ_X(f_i f_j/D_K)]_{0≤i,j<h}`.  PROVED — the
              triangular change of basis.  This is a genuine identity, not a definition:
              the constant `S_K` of (2.5) is *recovered* from the leading coefficients of
              the `q_i`, `S_K = ((K!)²/(N!)¹²)^h · (∏_{i<h} lead q_i)²`
              (`S_eq_change_of_basis`).  A known-answer control on (2.5) itself, and on the
              index range `0 ≤ i,j < h` of (3.11): with an `(h+1)×(h+1)` matrix the identity
              would be false.
  §3   p. 9   Lemma 3.3's two hypotheses for the entries of (3.11): the pullback numerator
              `A_{ij}(x) = x⁵f_i(-x²)f_j(-x²)` is integer-valued (`pullNum_int`) and has
              degree at most `12N + 4h + 1` (`pullNum_natDegree_le`), whence
              `max(2K, d+1) ≤ 5K` (`max_two_K_le_five_K`).  PROVED.
  §6   pp. 8–9 `crude_entry_bound`: Lemma 3.3 (3.10) at the entries of (3.11), transported
              through the pullback identity (3.1).  PROVED (2026-09-23), by
              `Zeta5.Lemma33.entry_bound` of `Zeta5/Lemma33.lean`, which proves Lemma 3.3
              itself (`Zeta5.Lemma33.lemma_3_3`) and the pullback (3.1) for every
              `μ_X(B/D_tail)` (`Zeta5.Lemma33.pullback`).  Then the assembly
              `eq_3_12'` = `eq_3_12`, by `Zeta5.vGAtLeast_det`.  PROVED.

-/
import Zeta5.Section3
import Zeta5.Lemma33

namespace Zeta5

open Polynomial Finset Functional

noncomputable section

namespace CrudeBound

/-! # §1.  The basis `q_i`, `f_i` of §3.3 (p. 9)

> Define `q_0(t) = 1`, `q_i(t) = (-1)^i 2t D_{i-1}(t)/(2i)!` `(i ≥ 1)`,
> `f_i(t) = (D_N(t)/(N!)²)³ q_i(t)`.
-/

/-- **p. 9**: `q_0(t) = 1` and `q_i(t) = (-1)^i 2 t D_{i-1}(t)/(2i)!` for `i ≥ 1`. -/
def qb (i : ℕ) : ℚ[X] :=
  if i = 0 then 1 else C ((-1 : ℚ) ^ i * 2 / ((2 * i).factorial : ℚ)) * (X * D (i - 1))

/-- The leading coefficient of `q_i`: `1` at `i = 0`, `(-1)^i 2/(2i)!` afterwards. -/
def qlead (i : ℕ) : ℚ := if i = 0 then 1 else (-1 : ℚ) ^ i * 2 / ((2 * i).factorial : ℚ)

lemma qlead_ne_zero (i : ℕ) : qlead i ≠ 0 := by
  unfold qlead
  split_ifs with h0
  · exact one_ne_zero
  · exact div_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) (by norm_num))
      (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _))

lemma X_mul_D_natDegree (m : ℕ) : ((X : ℚ[X]) * D m).natDegree = m + 1 := by
  rw [Polynomial.natDegree_mul Polynomial.X_ne_zero (D_ne_zero _), Polynomial.natDegree_X,
    D_natDegree]
  omega

lemma X_mul_D_monic (m : ℕ) : ((X : ℚ[X]) * D m).Monic := Polynomial.monic_X.mul (D_monic m)

/-- `deg q_i = i`. -/
@[simp] lemma qb_natDegree (i : ℕ) : (qb i).natDegree = i := by
  unfold qb
  split_ifs with h0
  · subst h0; simp
  · rw [Polynomial.natDegree_C_mul (by
      have : ((2 * i).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
      exact div_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) (by norm_num)) this),
      X_mul_D_natDegree]
    omega

/-- `[t^i] q_i = lead q_i`. -/
lemma qb_coeff_self (i : ℕ) : (qb i).coeff i = qlead i := by
  unfold qb qlead
  split_ifs with h0
  · subst h0; simp
  · rw [Polynomial.coeff_C_mul]
    have hd : ((X : ℚ[X]) * D (i - 1)).natDegree = i := by
      rw [X_mul_D_natDegree]; omega
    have hmon := (X_mul_D_monic (i - 1)).coeff_natDegree
    rw [hd] at hmon
    rw [hmon, mul_one]

lemma qb_ne_zero (i : ℕ) : qb i ≠ 0 := fun h0 =>
  qlead_ne_zero i (by rw [← qb_coeff_self, h0, Polynomial.coeff_zero])

/-- `q_i` expanded in the monomial basis, over any range covering `i`. -/
lemma qb_expand (i m : ℕ) (him : i < m) :
    qb i = ∑ k ∈ range m, C ((qb i).coeff k) * X ^ k := by
  conv_lhs => rw [Polynomial.as_sum_range' (qb i) m (by rw [qb_natDegree]; exact him)]
  exact Finset.sum_congr rfl fun k _ => (Polynomial.C_mul_X_pow_eq_monomial).symm

/-- **p. 9**: `f_i(t) = (D_N(t)/(N!)²)³ q_i(t)`. -/
def fb (n i : ℕ) : ℚ[X] := C ((((N n).factorial : ℚ)) ^ 6)⁻¹ * (D (N n)) ^ 3 * qb i

/-- The rational function `f_i f_j / D_K` of (3.11), put over the denominator `D_tail`
that `muOver` uses: `f_i f_j / D_K = ((N!)^{-12} D_N⁵ q_i q_j)/D_tail`, because
`f_i f_j = D_N⁶ q_i q_j/(N!)¹²` and `D_N · D_tail = D_K`.  An exact polynomial identity. -/
lemma fb_mul_over_DK (n i j : ℕ) :
    fb n i * fb n j * Dtail n
      = C ((((N n).factorial : ℚ)) ^ 12)⁻¹ * ((D (N n)) ^ 5 * (qb i * qb j)) * D (K n) := by
  have hDK := D_mul_Dtail n
  have hc : ((((N n).factorial : ℚ)) ^ 6)⁻¹ * ((((N n).factorial : ℚ)) ^ 6)⁻¹
      = ((((N n).factorial : ℚ)) ^ 12)⁻¹ := by
    rw [← mul_inv, ← pow_add]
  rw [fb, fb, ← hDK]
  rw [show (C ((((N n).factorial : ℚ)) ^ 6)⁻¹ * D (N n) ^ 3 * qb i)
        * (C ((((N n).factorial : ℚ)) ^ 6)⁻¹ * D (N n) ^ 3 * qb j) * Dtail n
      = C (((((N n).factorial : ℚ)) ^ 6)⁻¹ * ((((N n).factorial : ℚ)) ^ 6)⁻¹)
        * (D (N n) ^ 6 * (qb i * qb j)) * Dtail n by rw [map_mul]; ring]
  rw [hc]
  ring

/-! # §1b.  The basis is integer-valued under `t = -x²` (p. 9)

> *"For `i ≥ 1`, the identity `q_i(-x²) = C(x+i, 2i) + C(x+i-1, 2i)` shows that `q_i(-x²)` is
> integer-valued.  The same is true of `q_0 = 1`.  Together with
> `D_N(-x²)/(N!)² = C(N-x, N) C(N+x, N)`, this proves that `f_i(-x²)` is integer-valued for
> every `i ≥ 0`."*

Both printed identities are proved below, in the equivalent divisibility form: the binomial
coefficients `C(y, m)` are the values `P_m(y)/m!` of the descending Pochhammer polynomial,
and `m! ∣ P_m(y)` for every integer `y` (`factorial_dvd_descPochhammer_eval`, from Mathlib's
`Ring.choose` on the binomial ring `ℤ`). -/

/-- `m! ∣ (y)(y-1)⋯(y-m+1)` for every integer `y`: the value of a binomial coefficient. -/
lemma factorial_dvd_descPochhammer_eval (m : ℕ) (y : ℤ) :
    (m.factorial : ℤ) ∣ (descPochhammer ℤ m).eval y := by
  refine ⟨Ring.choose y m, ?_⟩
  have hh := Ring.descPochhammer_eq_factorial_smul_choose (R := ℤ) y m
  rw [← Polynomial.eval_eq_smeval] at hh
  rw [hh, nsmul_eq_mul]

/-- `∏_{j=1}^m (j + y) = P_m(m + y)`, the ascending product as a descending Pochhammer. -/
lemma prod_Icc_add_eq_descPochhammer (m : ℕ) (y : ℤ) :
    ∏ j ∈ Icc 1 m, ((j : ℤ) + y) = (descPochhammer ℤ m).eval ((m : ℤ) + y) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.prod_Icc_succ_top (by omega), ih, descPochhammer_succ_left]
    simp only [Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_comp,
      Polynomial.eval_sub, Polynomial.eval_one]
    have hsub : ((m : ℤ) + 1 + y) - 1 = (m : ℤ) + y := by ring
    push_cast
    rw [hsub]
    ring

/-- `m! ∣ ∏_{j=1}^m (j + y)` for every integer `y`. -/
lemma factorial_dvd_prod_Icc_add (m : ℕ) (y : ℤ) :
    (m.factorial : ℤ) ∣ ∏ j ∈ Icc 1 m, ((j : ℤ) + y) := by
  rw [prod_Icc_add_eq_descPochhammer]
  exact factorial_dvd_descPochhammer_eval m _

/-- `P_{2e+1}(z+e) = z ∏_{j=1}^{e}(z² - j²)`: the odd descending Pochhammer, centred. -/
lemma descPochhammer_odd_eval (e : ℕ) (z : ℤ) :
    (descPochhammer ℤ (2 * e + 1)).eval (z + (e : ℤ))
      = z * ∏ j ∈ Icc 1 e, (z ^ 2 - (j : ℤ) ^ 2) := by
  induction e with
  | zero => simp [descPochhammer_one]
  | succ e ih =>
    have harg : (2 * (e + 1) + 1) = (2 * e + 1) + 1 + 1 := by omega
    rw [harg, descPochhammer_succ_left]
    simp only [Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_comp,
      Polynomial.eval_sub, Polynomial.eval_one]
    rw [descPochhammer_succ_right]
    simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_natCast]
    have h1 : (z + ((e : ℤ) + 1)) - 1 = z + (e : ℤ) := by ring
    push_cast
    rw [h1, ih, Finset.prod_Icc_succ_top (by omega)]
    push_cast
    ring

/-- **p. 9**, first identity: `q_i(-z²) = C(z+i,2i) + C(z+i-1,2i) ∈ ℤ` for every integer `z`.

Here in divisibility form: `(2i)! · q_i(-z²) = P_{2i}(z+i) + P_{2i}(z+i-1)`, and each of the
two descending Pochhammer values is divisible by `(2i)!`. -/
lemma qb_pullback_int (i : ℕ) (z : ℤ) :
    ∃ w : ℤ, ((qb i).comp (-(X ^ 2) : ℚ[X])).eval (z : ℚ) = (w : ℚ) := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · exact ⟨1, by simp [qb]⟩
  obtain ⟨e, rfl⟩ : ∃ e, i = e + 1 := ⟨i - 1, by omega⟩
  have hfac2 : (((2 * e + 2).factorial : ℚ)) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  -- `(2i)! q_i(-z²) = P_{2i}(z+i) + P_{2i}(z+i-1)`, over `ℤ`
  have hsum : (descPochhammer ℤ (2 * e + 2)).eval (z + (e : ℤ) + 1)
        + (descPochhammer ℤ (2 * e + 2)).eval (z + (e : ℤ))
      = 2 * z * (descPochhammer ℤ (2 * e + 1)).eval (z + (e : ℤ)) := by
    have hL : (descPochhammer ℤ (2 * e + 2)).eval (z + (e : ℤ) + 1)
        = (z + (e : ℤ) + 1) * (descPochhammer ℤ (2 * e + 1)).eval (z + (e : ℤ)) := by
      rw [show (2 * e + 2) = (2 * e + 1) + 1 from by omega, descPochhammer_succ_left]
      simp only [Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_comp,
        Polynomial.eval_sub, Polynomial.eval_one]
      rw [show (z + (e : ℤ) + 1) - 1 = z + (e : ℤ) from by ring]
    have hR : (descPochhammer ℤ (2 * e + 2)).eval (z + (e : ℤ))
        = (descPochhammer ℤ (2 * e + 1)).eval (z + (e : ℤ)) * (z - (e : ℤ) - 1) := by
      rw [show (2 * e + 2) = (2 * e + 1) + 1 from by omega, descPochhammer_succ_right]
      simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
        Polynomial.eval_natCast]
      push_cast
      ring_nf
    rw [hL, hR]; ring
  obtain ⟨w1, hw1⟩ := factorial_dvd_descPochhammer_eval (2 * e + 2) (z + (e : ℤ) + 1)
  obtain ⟨w2, hw2⟩ := factorial_dvd_descPochhammer_eval (2 * e + 2) (z + (e : ℤ))
  refine ⟨w1 + w2, ?_⟩
  -- the same identity in `ℚ`, with `q_i(-z²)` written out
  have hDcomp : ((D e).comp (-(X ^ 2) : ℚ[X])).eval (z : ℚ)
      = ∏ j ∈ Icc 1 e, (-((z : ℚ) ^ 2) + (j : ℚ) ^ 2) := by
    rw [D, Polynomial.eval_comp]
    simp only [Polynomial.eval_prod, Polynomial.eval_add, Polynomial.eval_X,
      Polynomial.eval_C, Polynomial.eval_neg, Polynomial.eval_pow]
  have hprodQ : ∏ j ∈ Icc 1 e, (-((z : ℚ) ^ 2) + (j : ℚ) ^ 2)
      = (-1 : ℚ) ^ e * ∏ j ∈ Icc 1 e, ((z : ℚ) ^ 2 - (j : ℚ) ^ 2) := by
    rw [Finset.prod_congr rfl (fun j (_ : j ∈ Icc 1 e) =>
        show (-((z : ℚ) ^ 2) + (j : ℚ) ^ 2)
          = (-1 : ℚ) * ((z : ℚ) ^ 2 - (j : ℚ) ^ 2) from by ring),
      Finset.prod_mul_distrib, Finset.prod_const, Nat.card_Icc]
    simp
  have hee : ((-1 : ℚ)) ^ (e * 2) = 1 := by rw [mul_comm, pow_mul]; norm_num
  have hval : ((qb (e + 1)).comp (-(X ^ 2) : ℚ[X])).eval (z : ℚ)
      * (((2 * e + 2).factorial : ℚ))
      = 2 * (z : ℚ) * ((z : ℚ) * ∏ j ∈ Icc 1 e, ((z : ℚ) ^ 2 - (j : ℚ) ^ 2)) := by
    rw [qb, ite_eq_right (by omega)]
    simp only [Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_comp, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_neg, Polynomial.eval_pow, Polynomial.eval_X]
    rw [Nat.add_sub_cancel, hDcomp, hprodQ,
      show 2 * (e + 1) = 2 * e + 2 from by omega, pow_succ]
    field_simp
    linear_combination ((z : ℚ) ^ 2 *
      ∏ j ∈ Icc 1 e, ((z : ℚ) ^ 2 - (j : ℚ) ^ 2)) * hee
  -- and the integrality
  have hZ : (w1 + w2) * ((2 * e + 2).factorial : ℤ)
      = 2 * z * (z * ∏ j ∈ Icc 1 e, ((z : ℤ) ^ 2 - (j : ℤ) ^ 2)) := by
    rw [← descPochhammer_odd_eval, ← hsum, hw1, hw2]; ring
  have hQ : ((w1 + w2 : ℤ) : ℚ) * (((2 * e + 2).factorial : ℚ))
      = 2 * (z : ℚ) * ((z : ℚ) * ∏ j ∈ Icc 1 e, ((z : ℚ) ^ 2 - (j : ℚ) ^ 2)) := by
    have hc := congrArg (fun t : ℤ => (t : ℚ)) hZ
    push_cast at hc ⊢
    exact hc
  exact mul_right_cancel₀ hfac2 (hval.trans hQ.symm)

/-- **p. 9**, second identity: `D_m(-z²)/(m!)² = C(m-z,m) C(m+z,m) ∈ ℤ` for every integer
`z`.  In divisibility form: `D_m(-z²) = (∏_{j=1}^m (j-z))(∏_{j=1}^m (j+z))` and `m!` divides
each factor. -/
lemma D_pullback_int (m : ℕ) (z : ℤ) :
    ∃ w : ℤ, ((D m).comp (-(X ^ 2) : ℚ[X])).eval (z : ℚ)
      = (w : ℚ) * ((m.factorial : ℚ)) ^ 2 := by
  obtain ⟨w1, hw1⟩ := factorial_dvd_prod_Icc_add m (-z)
  obtain ⟨w2, hw2⟩ := factorial_dvd_prod_Icc_add m z
  refine ⟨w1 * w2, ?_⟩
  have hD : ((D m).comp (-(X ^ 2) : ℚ[X])).eval (z : ℚ)
      = ∏ j ∈ Icc 1 m, (-((z : ℚ) ^ 2) + (j : ℚ) ^ 2) := by
    rw [D, Polynomial.eval_comp]
    simp only [Polynomial.eval_prod, Polynomial.eval_add, Polynomial.eval_X,
      Polynomial.eval_C, Polynomial.eval_neg, Polynomial.eval_pow]
  have hsplit : ∏ j ∈ Icc 1 m, (-((z : ℚ) ^ 2) + (j : ℚ) ^ 2)
      = (∏ j ∈ Icc 1 m, ((j : ℚ) + (-(z : ℚ)))) * (∏ j ∈ Icc 1 m, ((j : ℚ) + (z : ℚ))) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun j _ => by ring
  have hc1 : (∏ j ∈ Icc 1 m, ((j : ℚ) + (-(z : ℚ))))
      = ((∏ j ∈ Icc 1 m, ((j : ℤ) + (-z)) : ℤ) : ℚ) := by
    push_cast
    exact Finset.prod_congr rfl fun j _ => by ring
  have hc2 : (∏ j ∈ Icc 1 m, ((j : ℚ) + (z : ℚ)))
      = ((∏ j ∈ Icc 1 m, ((j : ℤ) + z) : ℤ) : ℚ) := by
    push_cast
    exact Finset.prod_congr rfl fun j _ => by ring
  rw [hD, hsplit, hc1, hc2, hw1, hw2]
  push_cast
  ring

/-- **p. 9**: *"this proves that `f_i(-x²)` is integer-valued for every `i ≥ 0`"*. -/
lemma fb_pullback_int (n i : ℕ) (z : ℤ) :
    ∃ w : ℤ, ((fb n i).comp (-(X ^ 2) : ℚ[X])).eval (z : ℚ) = (w : ℚ) := by
  obtain ⟨wD, hwD⟩ := D_pullback_int (N n) z
  obtain ⟨wq, hwq⟩ := qb_pullback_int i z
  refine ⟨wD ^ 3 * wq, ?_⟩
  have hNfac : (((N n).factorial : ℚ)) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  rw [fb]
  simp only [Polynomial.mul_comp, Polynomial.C_comp, Polynomial.pow_comp, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow]
  rw [hwD, hwq]
  push_cast
  field_simp

/-! # §2.  (3.11): the triangular change of basis (p. 9)

>     F_K(X) = det[ (K!)² μ_X( f_i(t) f_j(t)/D_K(t) ) ]_{0≤i,j<h}.                  (3.11)

`muOver n Φ` is `μ_X(Φ(t)/D_tail(t))`, so by `fb_mul_over_DK` the printed entry is

    (K!)² μ_X(f_i f_j/D_K) = ((K!)²/(N!)¹²) · muOver n (D_N⁵ q_i q_j) ,

which is `Gf` below.  Writing `q_i = ∑_k c_{ki} t^k`, the matrix `[muOver n (D_N⁵ q_i q_j)]`
is `Cᵀ G_K C` with `C = (c_{ki})`; `C` is triangular with diagonal `lead q_i`, so its
determinant is `∏_{i<h} lead q_i` and

    det (3.11) = ((K!)²/(N!)¹²)^h (∏_{i<h} lead q_i)² Δ_K = S_K Δ_K = F_K,

the last equality being **exactly (2.5)** — the constant `S_K` is recovered, not assumed. -/

/-- The `(k,l)` entry of `G_K`, indexed by naturals: `μ_X(D_N⁵ t^{k+l}/D_tail)`. -/
def Graw (n k l : ℕ) : ℚ[X] := muOver n ((D (N n)) ^ 5 * X ^ (k + l))

lemma G_eq_Graw (n : ℕ) (i j : Fin (h n)) : G n i j = Graw n i j := rfl

/-- The entry of (3.11): `(K!)² μ_X(f_i f_j/D_K)`. -/
def Gf (n i j : ℕ) : ℚ[X] :=
  C ((((K n).factorial : ℚ)) ^ 2 * ((((N n).factorial : ℚ)) ^ 12)⁻¹) *
    muOver n ((D (N n)) ^ 5 * (qb i * qb j))

/-- `μ_X` is additive over a finite sum (from `muOver_add`). -/
lemma muOver_zero (n : ℕ) : muOver n 0 = 0 := by
  have hz := muOver_add n 0 0
  rw [add_zero] at hz
  linear_combination -hz

lemma muOver_sum {ι : Type*} (n : ℕ) (s : Finset ι) (f : ι → ℚ[X]) :
    muOver n (∑ a ∈ s, f a) = ∑ a ∈ s, muOver n (f a) := by
  classical
  refine Finset.induction_on s (by simp [muOver_zero]) ?_
  intro a s ha ih
  rw [Finset.sum_insert ha, Finset.sum_insert ha, muOver_add, ih]

/-- The expansion of the `(i,j)` entry of (3.11) in the monomial basis. -/
lemma muOver_qb_mul (n i j : ℕ) (hi : i < h n) (hj : j < h n) :
    muOver n ((D (N n)) ^ 5 * (qb i * qb j))
      = ∑ k ∈ range (h n), ∑ l ∈ range (h n),
          C ((qb i).coeff k) * Graw n k l * C ((qb j).coeff l) := by
  have hexp : (D (N n)) ^ 5 * (qb i * qb j)
      = ∑ k ∈ range (h n), ∑ l ∈ range (h n),
          C ((qb i).coeff k * (qb j).coeff l) * ((D (N n)) ^ 5 * X ^ (k + l)) := by
    conv_lhs => rw [qb_expand i (h n) hi, qb_expand j (h n) hj]
    rw [Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul, pow_add]
    ring
  rw [hexp, muOver_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [muOver_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [muOver_C_mul, map_mul, Graw]
  ring

/-- The triangular change-of-basis matrix `C_{ki} = [t^k] q_i`, over `ℚ`. -/
def Cq (n : ℕ) : Matrix (Fin (h n)) (Fin (h n)) ℚ := Matrix.of fun k i => (qb i).coeff k

/-- The same matrix over `ℚ[X]`. -/
def Cmat (n : ℕ) : Matrix (Fin (h n)) (Fin (h n)) ℚ[X] := (Cq n).map C

/-- `[ μ_X(D_N⁵ q_i q_j/D_tail) ] = Cᵀ G_K C`: the change of basis, as a matrix identity. -/
lemma matrix_change_of_basis (n : ℕ) :
    (Matrix.of fun i j : Fin (h n) => muOver n ((D (N n)) ^ 5 * (qb i * qb j)))
      = (Cmat n).transpose * G n * Cmat n := by
  classical
  ext i j
  have hR : ((Cmat n).transpose * G n * Cmat n) i j
      = ∑ l ∈ range (h n), ∑ k ∈ range (h n),
          C ((qb (i : ℕ)).coeff k) * Graw n k l * C ((qb (j : ℕ)).coeff l) := by
    rw [Matrix.mul_apply, ← Fin.sum_univ_eq_sum_range
      (fun l => ∑ k ∈ range (h n),
        C ((qb (i : ℕ)).coeff k) * Graw n k l * C ((qb (j : ℕ)).coeff l)) (h n)]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul, ← Fin.sum_univ_eq_sum_range
      (fun k => C ((qb (i : ℕ)).coeff k) * Graw n k (l : ℕ) * C ((qb (j : ℕ)).coeff (l : ℕ)))
      (h n)]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Cmat, Cq, Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply, G_eq_Graw]
  rw [Matrix.of_apply, hR, muOver_qb_mul n i j i.isLt j.isLt, Finset.sum_comm]

lemma Cq_isUpperTriangular (n : ℕ) : (Cq n).IsUpperTriangular := by
  intro k i hki
  have : (qb (i : ℕ)).natDegree < (k : ℕ) := by
    rw [qb_natDegree]; exact hki
  exact Polynomial.coeff_eq_zero_of_natDegree_lt this

/-- `det C = ∏_{i<h} lead q_i`, the triangularity of the change of basis. -/
lemma det_Cq (n : ℕ) : (Cq n).det = ∏ i ∈ range (h n), qlead i := by
  rw [Matrix.det_of_isUpperTriangular (Cq_isUpperTriangular n)]
  rw [← Fin.prod_univ_eq_prod_range (fun i => qlead i) (h n)]
  exact Finset.prod_congr rfl fun i _ => qb_coeff_self (i : ℕ)

/-- **The constant `S_K` of (2.5) is what the change of basis produces.**

`((K!)²/(N!)¹²)^h · (∏_{i<h} lead q_i)² = S_K`.  This is a known-answer control on (2.5):
the `4^{h-1}/∏((2i)!)²` of the printed `S_K` is exactly the square of the product of the
leading coefficients `(-1)^i 2/(2i)!` of the `q_i`, `i = 1, …, h-1`. -/
lemma S_eq_change_of_basis (n : ℕ) :
    ((((K n).factorial : ℚ)) ^ 2 * ((((N n).factorial : ℚ)) ^ 12)⁻¹) ^ (h n)
        * (∏ i ∈ range (h n), qlead i) ^ 2 = S n := by
  have hKfac : (((K n).factorial : ℚ)) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  have hNfac : (((N n).factorial : ℚ)) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  have hfac : ∀ i : ℕ, (((2 * i).factorial : ℚ)) ≠ 0 :=
    fun i => Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  -- the square of the product of the leading coefficients
  have hsq : (∏ i ∈ range (h n), qlead i) ^ 2
      = 4 ^ (h n - 1) / ∏ i ∈ Icc 1 (h n - 1), (((2 * i).factorial : ℚ)) ^ 2 := by
    rcases Nat.eq_zero_or_pos (h n) with h0 | hpos
    · rw [h0]; simp
    · obtain ⟨m, hm⟩ : ∃ m, h n = m + 1 := ⟨h n - 1, by omega⟩
      rw [hm]
      have hrange : range (m + 1) = insert 0 (Icc 1 m) := by
        ext b
        simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
        omega
      have hq0 : qlead 0 = 1 := by simp [qlead]
      rw [hrange, Finset.prod_insert (by simp), hq0, one_mul, ← Finset.prod_pow]
      have hterm : ∀ i ∈ Icc 1 m, qlead i ^ 2 = 4 / (((2 * i).factorial : ℚ)) ^ 2 := by
        intro i hi
        have hi1 : 1 ≤ i := (Finset.mem_Icc.1 hi).1
        rw [qlead, ite_eq_right (by omega), div_pow, mul_pow, ← pow_mul, mul_comm i 2, pow_mul]
        norm_num
      rw [Finset.prod_congr rfl hterm, Finset.prod_div_distrib, Finset.prod_const,
        Nat.card_Icc]
      simp only [Nat.add_sub_cancel]
  have key : ((((K n).factorial : ℚ)) ^ 2 * ((((N n).factorial : ℚ)) ^ 12)⁻¹) ^ (h n)
      = (((K n).factorial : ℚ)) ^ (2 * h n) / (((N n).factorial : ℚ)) ^ (12 * h n) := by
    rw [mul_pow, ← pow_mul, inv_pow, ← pow_mul, div_eq_mul_inv]
  rw [hsq, key, S, div_mul_div_comm]

/-- **(3.11)** (p. 9): `F_K(X) = det[(K!)² μ_X(f_i f_j/D_K)]_{0≤i,j<h}`. -/
theorem eq_3_11 (n : ℕ) : F n = (Matrix.of fun i j : Fin (h n) => Gf n i j).det := by
  classical
  set κ : ℚ := (((K n).factorial : ℚ)) ^ 2 * ((((N n).factorial : ℚ)) ^ 12)⁻¹ with hκ
  have hsmul : (Matrix.of fun i j : Fin (h n) => Gf n i j)
      = (C κ) • (Matrix.of fun i j : Fin (h n) =>
          muOver n ((D (N n)) ^ 5 * (qb i * qb j))) := by
    ext i j
    simp only [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, Gf, hκ]
  rw [hsmul, Matrix.det_smul, matrix_change_of_basis, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_transpose]
  have hdetC : (Cmat n).det = C ((Cq n).det) := by
    simpa [Cmat] using (RingHom.map_det (C : ℚ →+* ℚ[X]) (Cq n)).symm
  rw [hdetC, det_Cq, Fintype.card_fin, ← map_pow, F, Delta]
  rw [← S_eq_change_of_basis n, hκ]
  simp only [map_mul, map_pow]
  ring

/-! # §3.  The degree of the pullback numerator (p. 9)

> *"The pullback numerator has degree at most `12N + 4h + 1`.  Thus `max(2K, d+1) ≤ 5K`."*

The pullback numerator of the `(i,j)` entry is `A_{ij}(x) = x⁵ f_i(-x²) f_j(-x²)`.  With
`deg f_i = 3N + i` in `t`, its degree in `x` is `5 + 2(3N+i) + 2(3N+j) = 12N + 2(i+j) + 5`,
which for `i, j ≤ h-1` is at most `12N + 4h + 1`.  And `K = 40n`, `N = 3n`, `h = 37n` give
`2K = 80n ≤ 200n = 5K` and `d + 1 = 184n + 2 ≤ 200n = 5K` for `n ≥ 1`. -/

/-- `deg f_i = 3N + i`. -/
lemma fb_natDegree (n i : ℕ) : (fb n i).natDegree = 3 * N n + i := by
  have hc : ((((N n).factorial : ℚ)) ^ 6)⁻¹ ≠ 0 :=
    inv_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)))
  rw [fb, mul_assoc, Polynomial.natDegree_C_mul hc,
    Polynomial.natDegree_mul (pow_ne_zero _ (D_ne_zero _)) (qb_ne_zero i),
    Polynomial.natDegree_pow, D_natDegree, qb_natDegree]

/-- The pullback numerator `A_{ij}(x) = x⁵ f_i(-x²) f_j(-x²)` of the `(i,j)` entry. -/
def pullNum (n i j : ℕ) : ℚ[X] :=
  X ^ 5 * ((fb n i).comp (-(X ^ 2)) * (fb n j).comp (-(X ^ 2)))

/-- **p. 9**: `deg A_{ij} ≤ 12N + 4h + 1` for `i, j < h`. -/
lemma pullNum_natDegree_le (n i j : ℕ) (hi : i < h n) (hj : j < h n) :
    (pullNum n i j).natDegree ≤ 12 * N n + 4 * h n + 1 := by
  have hcomp : ∀ m : ℕ, ((fb n m).comp (-(X ^ 2) : ℚ[X])).natDegree ≤ 2 * (3 * N n + m) := by
    intro m
    refine le_trans (Polynomial.natDegree_comp_le) ?_
    rw [fb_natDegree]
    have hd : ((-(X ^ 2) : ℚ[X])).natDegree = 2 := by
      rw [Polynomial.natDegree_neg, Polynomial.natDegree_X_pow]
    rw [hd]
    omega
  refine le_trans (Polynomial.natDegree_mul_le) ?_
  have h5 : ((X : ℚ[X]) ^ 5).natDegree = 5 := Polynomial.natDegree_X_pow 5
  refine le_trans (Nat.add_le_add_left (Polynomial.natDegree_mul_le) _) ?_
  rw [h5]
  have := hcomp i
  have := hcomp j
  omega

/-- **Lemma 3.3's hypothesis for `A_{ij}`**: the pullback numerator is integer-valued.

`A_{ij}(z) = z⁵ f_i(-z²) f_j(-z²)`, and `f_i(-x²)` is integer-valued by `fb_pullback_int`,
which is the p. 9 sentence *"this proves that `f_i(-x²)` is integer-valued for every
`i ≥ 0`"*. -/
lemma pullNum_int (n i j : ℕ) (z : ℤ) :
    ∃ w : ℤ, (pullNum n i j).eval (z : ℚ) = (w : ℚ) := by
  obtain ⟨wi, hwi⟩ := fb_pullback_int n i z
  obtain ⟨wj, hwj⟩ := fb_pullback_int n j z
  refine ⟨z ^ 5 * (wi * wj), ?_⟩
  rw [pullNum]
  simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
  rw [hwi, hwj]
  push_cast
  ring

/-- **p. 9**: `max(2K, d+1) ≤ 5K` with `d = 12N + 4h + 1`, for `n ≥ 1`.
`2K = 80n`, `d + 1 = 184n + 2`, `5K = 200n`. -/
lemma max_two_K_le_five_K (n : ℕ) (hn : 1 ≤ n) :
    max (2 * K n) (12 * N n + 4 * h n + 1 + 1) ≤ 5 * K n := by
  simp only [K, N, h]
  omega

/-! # §6.  The assembly (p. 9)

Lemma 3.3 bounds every entry of (3.11) by `-6⌊log_p 5K⌋ - v_p(24)`; the determinant of an
`h × h` matrix all of whose entries have Gauss valuation at least `e` has Gauss valuation at
least `h e` (`Zeta5.vGAtLeast_det`, the `L = 0` case of Lemma 4.2). -/

/-- **Lemma 3.3 (p. 8), applied to the `(i,j)` entry of (3.11).  PROVED.**

PAPER STATEMENT, verbatim (p. 8), together with the sentence of p. 9 that applies it:

> **Lemma 3.3.**  Let `A` be integer-valued on `ℤ_p`, with `deg A ≤ d`, and put
> `g(x) = (K!)² A(x) / ∏_{-K≤r≤K, r≠0}(x-r)`.  Then
>
>     v_p^G(τ_X(g)) ≥ -6⌊log_p max(2K, d+1)⌋ - v_p(24).                            (3.10)
>
> *"The pullback numerator has degree at most `12N + 4h + 1`.  Thus `max(2K, d+1) ≤ 5K`, and
> Lemma 3.3 proves (3.12)."*

The statement below is that conclusion at `A = A_{ij} = x⁵f_i(-x²)f_j(-x²)`, transported
through the pullback identity **(3.1)** `μ_X(R) = τ_X(x⁵R(-x²))`, which turns `τ_X(g)` into
`±(K!)² μ_X(f_i f_j/D_K) = ±Gf n i j` because `D_K(-x²) = (-1)^K ∏_{0<|r|≤K}(x-r)`.  (The
sign is immaterial: `vGAtLeast` is invariant under negation.)

HOW IT IS PROVED (`Zeta5/Lemma33.lean`, no `sorry`, no new axiom):

* the pullback (3.1) for every `μ_X(B/D_tail)` (`Lemma33.pullback`), by linearity from the
  monomial and pole cases `eq_3_1_mono`, `eq_3_1_pole` and the partial-fraction basis of
  `Functional.lean`; at these entries it is `Lemma33.entry_pullback`;
* Lemma 3.3 itself (`Lemma33.lemma_3_3`, in the paper's form (3.10); `lemma_3_3_strong` is the
  same bound without the `-v_p(24)`).  The pole terms are the paper's: `v_p(c_r) ≥ -⌊log_p 2K⌋`
  from `c_r = ±(K!)²rA(r)/((K+r)!(K-r)!) = ±rA(r)C(2K,K+r)/C(2K,K)` and
  `v_p(C(2K,K)) ≤ ⌊log_p 2K⌋`, and `v_p(H^{(5)}_{d(r)}) ≥ -5⌊log_p K⌋`.  The polynomial part
  is NOT done by the paper's two-scale estimate `P(ℤ_p) ⊂ p^{-L₀-M₀}ℤ_p` and (3.9): instead
  `A` is expanded in the integer binomial basis `C(x+K, k)`, whose quotients by
  `∏_{0<|r|≤K}(x-r)` are constants (`k ≤ 2K`) or `x·Π_m(x)/k!` (`k = 2K+1+m`), and `τ` of the
  latter is computed exactly from the difference identity (3.3) as `τ(ΔS) = [x⁴]S`.  This
  gives `v_p ≥ -6⌊log_p max(2K,d+1)⌋` directly, i.e. (3.10) with room `v_p(24)`.

The two hypotheses of Lemma 3.3 at these entries are `pullNum_int` and `pullNum_natDegree_le`
above, with `max_two_K_le_five_K`. -/
theorem crude_entry_bound (n p : ℕ) (hp : p.Prime) (i j : ℕ) (hi : i < h n) (hj : j < h n) :
    vGAtLeast p (Gf n i j)
      (-6 * (Nat.log p (5 * K n) : ℤ) - (padicValNat p 24 : ℤ)) := by
  have : Fact p.Prime := ⟨hp⟩
  have hn : 1 ≤ n := by simp only [h] at hi; omega
  exact Lemma33.entry_bound n (qb i) (qb j) _ (pullNum_natDegree_le n i j hi hj)
    (pullNum_int n i j) (max_two_K_le_five_K n hn)

/-- **(3.12)** (p. 9).  `v_p^G(F_K) ≥ -6h⌊log_p(5K)⌋ - h v_p(24)` for every prime `p`.

This is the output of Lemma 3.3 (p. 8) applied to the determinant (3.11) in the
integer-valued basis `f_i(t) = (D_N(t)/(N!)²)³ q_i(t)` of §3.3, using that the pullback
numerator has degree at most `12N + 4h + 1`, whence `max(2K, d+1) ≤ 5K`.

It is the bound that the first branch of (5.1) clears (see `Lp_small_eq`), and it is what
Proposition 5.1 uses at every prime `p ≤ K/M`. -/
theorem eq_3_12' (n p : ℕ) (hp : p.Prime) :
    vGAtLeast p (F n)
      (-6 * (h n : ℤ) * (Nat.log p (5 * K n) : ℤ) - (h n : ℤ) * (padicValNat p 24 : ℤ)) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hdet := vGAtLeast_det (p := p)
    (Matrix.of fun i j : Fin (h n) => Gf n (i : ℕ) (j : ℕ))
    (fun _ _ => -6 * (Nat.log p (5 * K n) : ℤ) - (padicValNat p 24 : ℤ))
    (fun _ => -6 * (Nat.log p (5 * K n) : ℤ) - (padicValNat p 24 : ℤ))
    (fun u v => crude_entry_bound n p hp (u : ℕ) (v : ℕ) u.isLt v.isLt)
    (fun _ _ => by omega)
  rw [eq_3_11 n]
  refine vGAtLeast_mono ?_ hdet
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact le_of_eq (by ring)

/-! # Known-answer controls

Small cases of the p. 9 identities, computed by hand and re-derived by Lean from the
definitions alone. -/

section Controls

/-- `q_1(t) = -t`, so `q_1(-x²) = x²`; and indeed `C(x+1,2) + C(x,2) = x²`. -/
example : qb 1 = -X := by
  rw [qb, ite_eq_right (by norm_num), show (1 : ℕ) - 1 = 0 from rfl, D_zero]
  norm_num

/-- `q_2(t) = t(t+1)/12`, so `q_2(-x²) = x²(x²-1)/12`; at `x = 3` this is `9·8/12 = 6`,
an integer, as `C(5,4) + C(4,4) = 5 + 1 = 6`. -/
example : qb 2 = C (1 / 12 : ℚ) * (X * (X + C (1 : ℚ)))
    ∧ ((qb 2).comp (-(X ^ 2) : ℚ[X])).eval (3 : ℚ) = 6 := by
  have h2 : qb 2 = C (1 / 12 : ℚ) * (X * (X + C (1 : ℚ))) := by
    rw [qb, ite_eq_right (by norm_num), show (2 : ℕ) - 1 = 1 from rfl, D,
      show Finset.Icc 1 1 = ({1} : Finset ℕ) from by decide, Finset.prod_singleton]
    norm_num
  refine ⟨h2, ?_⟩
  rw [h2]
  simp only [Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_comp, Polynomial.add_comp,
    Polynomial.eval_mul, Polynomial.eval_add,
    Polynomial.eval_C, Polynomial.eval_neg, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num

/-- The leading coefficients `lead q_i = (-1)^i 2/(2i)!` at `i = 1, 2, 3`:
`-1`, `1/12`, `-1/360`.  Their squares `1, 1/144, 1/129600` are the factors
`4/((2i)!)²` of `S_K`. -/
example : qlead 0 = 1 ∧ qlead 1 = -1 ∧ qlead 2 = 1 / 12 ∧ qlead 3 = -1 / 360 := by
  refine ⟨by norm_num [qlead], ?_, ?_, ?_⟩ <;>
    · rw [qlead, ite_eq_right (by norm_num)]; norm_num

/-- `D_2(-z²)/(2!)² = C(2-z,2)C(2+z,2)` at `z = 5`: `(1-25)(4-25)/4 = (-24)(-21)/4 = 126`,
and indeed `C(-3,2)C(7,2) = 6 · 21 = 126`. -/
example : ((D 2).comp (-(X ^ 2) : ℚ[X])).eval (5 : ℚ) = 126 * 4 := by
  rw [D, Polynomial.eval_comp, show Finset.Icc 1 2 = ({1, 2} : Finset ℕ) from by decide]
  simp only [Polynomial.eval_prod, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C,
    Polynomial.eval_neg, Polynomial.eval_pow]
  norm_num

/-- `max(2K, d+1) ≤ 5K` at the smallest admissible `n`: `2K = 80`, `d+1 = 186`, `5K = 200`. -/
example : max (2 * K 1) (12 * N 1 + 4 * h 1 + 1 + 1) = 186 ∧ 5 * K 1 = 200 := by
  refine ⟨by norm_num [K, N, h], by norm_num [K]⟩

end Controls

end CrudeBound

/-- **(3.12)** (p. 9), under the name `Normalization.lean` used for it.  -/
theorem eq_3_12 (n p : ℕ) (hp : p.Prime) :
    vGAtLeast p (F n)
      (-6 * (h n : ℤ) * (Nat.log p (5 * K n) : ℤ) - (h n : ℤ) * (padicValNat p 24 : ℤ)) :=
  CrudeBound.eq_3_12' n p hp

/-! # Audit trail: what is actually proved in this file -/

section
#print axioms Zeta5.CrudeBound.eq_3_11
#print axioms Zeta5.CrudeBound.S_eq_change_of_basis
#print axioms Zeta5.CrudeBound.qb_pullback_int
#print axioms Zeta5.CrudeBound.D_pullback_int
#print axioms Zeta5.CrudeBound.fb_pullback_int
#print axioms Zeta5.CrudeBound.pullNum_int
#print axioms Zeta5.CrudeBound.pullNum_natDegree_le
#print axioms Zeta5.CrudeBound.max_two_K_le_five_K
#print axioms Zeta5.CrudeBound.factorial_dvd_descPochhammer_eval
#print axioms Zeta5.CrudeBound.descPochhammer_odd_eval

#print axioms Zeta5.CrudeBound.crude_entry_bound
#print axioms Zeta5.eq_3_12
end

end

end Zeta5
