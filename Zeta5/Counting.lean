/-
Zeta5/Counting.lean

The residue-class counts `ℓ_A(a)` of §4.1 (p. 10), an inequality that the paper asserts
without proof, and the nonnegativity of the dimensions `L_a`
that depends on it.

The paper writes, on p. 10 immediately after (4.4),

    "From (4.4),   2Hx - 21/20 < T < 2Hx,   b_a ≤ 6αx + 3."

`b_a ≤ 6αx + 3` is a statement about `ℓ_N` and does not follow from (4.4); no proof is
given.  It is needed: with the naive bound `ℓ_N(a) ≤ 2⌊N/p⌋ + 2`, i.e. `b_a ≤ 6αx + 6`,
the paper's chain gives only `T - b_a > 2λx - 141/20`, which is `-3/2` at `x = 3`, and does not
yield `L_a ≥ 0`.  (The audit, `docs/zeta5-audit.pdf`, identifies this and supplies a proof.)

Since `x = K/p` and `α = 3/40`, `αx = 3K/(40p) = N/p`, so the inequality reads
`3 ℓ_N(a) ≤ 6N/p + 3`, i.e. `p · ℓ_N(a) ≤ 2N + p`.  `ell_lt` proves the strict form
`p · ℓ_A(a) < 2A + p` for every `A`, every odd prime `p` and every `1 ≤ a ≤ (p-1)/2`; that is
exactly the case split on `v_A = A mod p` that the audit supplies.  `InnerAlloc.L_nonneg` then
proves `L_a ≥ 0`, the conclusion the paper draws from this line.
-/
import Zeta5.Basic

namespace Zeta5

open Finset

/-! ## Counting one residue class in `[1, A]` -/

/-- The number of `j ∈ [1,A]` in a fixed nonzero residue class `r mod p` is `⌊(A+p-r)/p⌋`.

(Equivalently `⌊A/p⌋ + 1_{r ≤ A mod p}`, the form the audit writes; the closed form above is
the one that makes the arithmetic below painless.) -/
lemma card_residue (p r A : ℕ) (hr1 : 1 ≤ r) (hrp : r < p) :
    ((Icc 1 A).filter (fun j => j % p = r)).card = (A + p - r) / p := by
  classical
  have hp : 0 < p := lt_of_le_of_lt (Nat.zero_le r) hrp
  have himg : ((Icc 1 A).filter (fun j => j % p = r))
      = (range ((A + p - r) / p)).image (fun k => r + k * p) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨⟨hj1, hj2⟩, hjr⟩
      have hdm : p * (j / p) + r = j := by
        have h := Nat.div_add_mod j p
        rw [hjr] at h
        exact h
      have hdm' : p * (j / p) = j - r := Nat.eq_sub_of_add_eq hdm
      have hrj : r ≤ j := by omega
      refine ⟨j / p, ?_, ?_⟩
      · have hstep : (j / p + 1) * p ≤ A + p - r := by
          have h1 : (j / p + 1) * p = p * (j / p) + p := by ring
          rw [h1, hdm']
          omega
        exact Nat.lt_of_succ_le ((Nat.le_div_iff_mul_le hp).2 hstep)
      · rw [mul_comm, add_comm]; exact hdm
    · rintro ⟨k, hk, rfl⟩
      have h2 : (k + 1) * p ≤ A + p - r := (Nat.le_div_iff_mul_le hp).1 (Nat.succ_le_of_lt hk)
      have h3 : k * p + p ≤ A + p - r := by rw [add_mul, one_mul] at h2; exact h2
      have hrAp : r ≤ A + p := le_of_lt (lt_of_lt_of_le hrp (Nat.le_add_left p A))
      have h6 : r + k * p + p ≤ A + p := by
        calc r + k * p + p = r + (k * p + p) := by ring
          _ ≤ r + (A + p - r) := Nat.add_le_add_left h3 r
          _ = A + p := by omega
      refine ⟨⟨by omega, Nat.le_of_add_le_add_right h6⟩, ?_⟩
      rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hrp]
  have hinj : Function.Injective (fun k => r + k * p) := by
    intro x y hxy
    simp only at hxy
    exact Nat.eq_of_mul_eq_mul_right hp (Nat.add_left_cancel hxy)
  rw [himg, Finset.card_image_of_injective _ hinj, Finset.card_range]

/-- `(j + a) % p = 0` iff `j` lies in the class `p - a`, for `1 ≤ a < p`. -/
lemma add_mod_eq_zero_iff {p a : ℕ} (ha1 : 1 ≤ a) (hap : a < p) (j : ℕ) :
    (j + a) % p = 0 ↔ j % p = p - a := by
  have hp : 0 < p := lt_of_le_of_lt (Nat.zero_le a) hap
  have hs : j % p < p := Nat.mod_lt _ hp
  have hrw : (j + a) % p = (j % p + a) % p := by
    conv_lhs => rw [Nat.add_mod, Nat.mod_eq_of_lt hap]
  rw [hrw]
  constructor
  · intro hzero
    obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero hzero
    have hlt : p * k < p * 2 := by rw [← hk]; omega
    have hk2 : k < 2 := lt_of_mul_lt_mul_left hlt (Nat.zero_le p)
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [Nat.mul_zero] at hk
      omega
    have hk1 : k = 1 := by omega
    subst hk1
    rw [Nat.mul_one] at hk
    omega
  · intro hclass
    have hsum : j % p + a = p := by omega
    rw [hsum, Nat.mod_self]

/-- `ℓ_A(a) = ⌊(A+p-a)/p⌋ + ⌊(A+a)/p⌋` for `1 ≤ a` and `2a < p`: the two classes `±a` are
distinct and each is counted by `card_residue`. -/
lemma ell_eq (p A a : ℕ) (ha1 : 1 ≤ a) (ha2 : 2 * a < p) :
    ell p A a = (A + p - a) / p + (A + a) / p := by
  have hap : a < p := by omega
  have hne : a ≠ p - a := by omega
  have hfilter : ((Icc 1 A).filter (fun j => j % p = a % p ∨ (j + a) % p = 0))
      = ((Icc 1 A).filter (fun j => j % p = a)) ∪ ((Icc 1 A).filter (fun j => j % p = p - a)) := by
    ext j
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro ⟨hj, hor⟩
      rcases hor with hcase | hcase
      · exact Or.inl ⟨hj, by rwa [Nat.mod_eq_of_lt hap] at hcase⟩
      · exact Or.inr ⟨hj, (add_mod_eq_zero_iff ha1 hap j).1 hcase⟩
    · rintro (⟨hj, hcase⟩ | ⟨hj, hcase⟩)
      · exact ⟨hj, Or.inl (by rw [Nat.mod_eq_of_lt hap]; exact hcase)⟩
      · exact ⟨hj, Or.inr ((add_mod_eq_zero_iff ha1 hap j).2 hcase)⟩
  have hdisj : Disjoint ((Icc 1 A).filter (fun j => j % p = a))
      ((Icc 1 A).filter (fun j => j % p = p - a)) := by
    refine Finset.disjoint_left.2 fun j hj1 hj2 => ?_
    have h1 := (Finset.mem_filter.1 hj1).2
    have h2 := (Finset.mem_filter.1 hj2).2
    exact hne (h1.symm.trans h2)
  have hrewrite : A + p - (p - a) = A + a := by omega
  rw [ell, hfilter, Finset.card_union_of_disjoint hdisj,
    card_residue p a A ha1 hap, card_residue p (p - a) A (by omega) (by omega), hrewrite]

/-! ## The inequality the paper asserts without proof

`b_a ≤ 6αx + 3` with `x = K/p`, i.e. `p ℓ_N(a) ≤ 2N + p`.  We prove the strict form. -/

/-- **The audit's repair of the line after (4.4)** (see the head of this file).  For `1 ≤ a` with
`2a < p` (i.e. `1 ≤ a ≤ (p-1)/2` when `p` is odd), `p · ℓ_A(a) < 2A + p`.

In the paper's variables, with `A = N` and `x = K/p`, this is `b_a = 3ℓ_N(a) < 6αx + 3`.

The proof is the case split the paper omits: writing `ℓ_A(a) = 2⌊A/p⌋ + 1_{a ≤ v} + 1_{a ≥ p-v}`
with `v = A mod p`, both indicators can fire only if `p ≤ 2v`, and then the deficit `2v - p`
absorbs the extra row.  Here it appears as: equality in both of the two `⌊·⌋` bounds would
force `p ∣ (p - 2a)`, which is impossible for `0 < 2a < p`. -/
theorem ell_lt (p A a : ℕ) (ha1 : 1 ≤ a) (ha2 : 2 * a < p) :
    p * ell p A a < 2 * A + p := by
  have hp : 0 < p := by omega
  have hap : a < p := by omega
  set c1 := (A + p - a) / p with hc1
  set c2 := (A + a) / p with hc2
  have hd1 : p * c1 ≤ A + p - a := by
    rw [hc1, mul_comm]; exact Nat.div_mul_le_self _ _
  have hd2 : p * c2 ≤ A + a := by
    rw [hc2, mul_comm]; exact Nat.div_mul_le_self _ _
  have hstrict : p * c1 < A + p - a ∨ p * c2 < A + a := by
    by_contra hcon
    rw [not_or, not_lt, not_lt] at hcon
    obtain ⟨e1, e2⟩ := hcon
    have he1 : p * c1 = A + p - a := le_antisymm hd1 e1
    have he2 : p * c2 = A + a := le_antisymm hd2 e2
    have hm1 : (A + p - a) % p = 0 := by rw [← he1]; exact Nat.mul_mod_right p c1
    have hm2 : (A + a) % p = 0 := by rw [← he2]; exact Nat.mul_mod_right p c2
    have hsum : (A + p - a) + 2 * a = (A + a) + p := by omega
    have hz : ((A + p - a) + 2 * a) % p = 0 := by rw [hsum, Nat.add_mod_right]; exact hm2
    have hz2 : ((A + p - a) + 2 * a) % p = 2 * a := by
      have hadd : ((A + p - a) + 2 * a) % p = ((A + p - a) % p + (2 * a) % p) % p :=
        Nat.add_mod _ _ _
      rw [hadd, hm1, Nat.mod_eq_of_lt ha2, Nat.zero_add, Nat.mod_eq_of_lt ha2]
    have hcontra : (0 : ℕ) = 2 * a := hz.symm.trans hz2
    omega
  rw [ell_eq p A a ha1 ha2, Nat.mul_add, ← hc1, ← hc2]
  rcases hstrict with hs | hs
  · calc p * c1 + p * c2 < (A + p - a) + (A + a) := Nat.add_lt_add_of_lt_of_le hs hd2
      _ = 2 * A + p := by omega
  · calc p * c1 + p * c2 < (A + p - a) + (A + a) := Nat.add_lt_add_of_le_of_lt hd1 hs
      _ = 2 * A + p := by omega

/-- For an odd `p`, the classes of (4.4) are exactly `1 ≤ a ≤ m = (p-1)/2`, and they satisfy
the hypothesis `2a < p` of `ell_lt`. -/
lemma two_mul_lt_of_le_mHalf {p a : ℕ} (hp : Odd p) (ha : a ≤ mHalf p) : 2 * a < p := by
  obtain ⟨k, hk⟩ := hp
  rw [mHalf, hk] at ha
  omega

/-- `b_a = 3ℓ_N(a)` satisfies `p · b_a < 6N + 3p`, the integer form of `b_a < 6αx + 3`. -/
theorem bCoef_lt (n p a : ℕ) (ha1 : 1 ≤ a) (ha2 : 2 * a < p) :
    p * bCoef n p a < 6 * N n + 3 * p := by
  have h := ell_lt p (N n) a ha1 ha2
  have : p * bCoef n p a = 3 * (p * ell p (N n) a) := by rw [bCoef]; ring
  omega

/-- `p` is odd at every inner prime (indeed `p > 200M ≥ 8000`). -/
lemma IsInnerPrime.odd {n M p : ℕ} (hp : IsInnerPrime n M p) : Odd p := by
  have h2 : p ≠ 2 := by
    have := hp.gt_200M
    have := hp.cutoff
    omega
  exact hp.prime.odd_of_ne_two h2

/-- `2 m + 1 = p` at an inner prime. -/
lemma IsInnerPrime.two_mHalf {n M p : ℕ} (hp : IsInnerPrime n M p) : 2 * mHalf p + 1 = p := by
  obtain ⟨k, hk⟩ := hp.odd
  rw [mHalf, hk]
  omega

/-! ## Nonnegativity of the dimensions `L_a` (p. 10)

"The dimensions `L_a` are nonnegative and `L_0 + ∑_a L_a = h`."  This is the conclusion the
paper draws from the disputed line; with `ell_lt` in hand it is an exercise in integer
arithmetic, carried out below in full. -/

namespace InnerAlloc

/-- `h - L_0 ≥ 2p` at an inner prime: the slack in the chain
`T - b_a > 2Hx - 21/20 - (6αx + 3) = 2λx - 81/20 ≥ 3/2`. -/
lemma h_sub_L0_ge {n M p : ℕ} (hp : IsInnerPrime n M p) :
    2 * p + L0 M ≤ h n := by
  have h1 : 200 * M ^ 2 ≤ 40 * n := by simpa [K] using hp.size
  have h2 : 40 ≤ M := hp.cutoff
  have h3 : 3 * p ≤ 40 * n := by simpa [K] using hp.upper
  have hM : 40 * M ≤ M ^ 2 := by nlinarith
  have hn : 200 * (40 * M) ≤ 40 * n := le_trans (by nlinarith) h1
  simp only [h, L0]
  omega

/-- **`L_a ≥ 0`** (p. 10), for every class `1 ≤ a ≤ m`.  This is what the disputed inequality
`b_a ≤ 6αx + 3` is used for, and it fails under the naive bound `b_a ≤ 6αx + 6`. -/
theorem L_nonneg {n M p : ℕ} (hp : IsInnerPrime n M p) (A : InnerAlloc n M p)
    {a : ℕ} (ha1 : 1 ≤ a) (ha2 : a ≤ mHalf p) : 0 ≤ A.L a := by
  have hodd := hp.odd
  have h2m : 2 * mHalf p + 1 = p := hp.two_mHalf
  have hp0 : 0 < p := hp.prime.pos
  -- the disputed inequality, in the form `p · b_a ≤ 6N + 3p - 1`
  have hb : p * bCoef n p a < 6 * N n + 3 * p :=
    bCoef_lt n p a ha1 (two_mul_lt_of_le_mHalf hodd ha2)
  -- `p ⌊N/p⌋ ≤ N`
  have hmN : p * mFloor p (N n) ≤ N n := by
    rw [mFloor, mul_comm]; exact Nat.div_mul_le_self _ _
  -- `h - L_0 ≥ 2p`
  have hhL := h_sub_L0_ge hp
  -- move everything to ℤ
  have hE : (A.E : ℤ) < (mHalf p : ℤ) := by exact_mod_cast A.hE
  have hE0 : (0 : ℤ) ≤ (A.E : ℤ) := Int.natCast_nonneg _
  have hTE := A.hTE
  have hbZ : (p : ℤ) * (bCoef n p a : ℤ) < 6 * (N n : ℤ) + 3 * p := by exact_mod_cast hb
  have hmNZ : (p : ℤ) * (mFloor p (N n) : ℤ) ≤ (N n : ℤ) := by exact_mod_cast hmN
  have hhLZ : 2 * (p : ℤ) + (L0 M : ℤ) ≤ (h n : ℤ) := by exact_mod_cast hhL
  have h2mZ : 2 * (mHalf p : ℤ) + 1 = (p : ℤ) := by exact_mod_cast h2m
  have hp0Z : (0 : ℤ) < (p : ℤ) := by exact_mod_cast hp0
  have hmpos : (0 : ℤ) < (mHalf p : ℤ) := by omega
  -- suffices to prove `b_a ≤ T`
  have hmain : ((bCoef n p a : ℤ)) ≤ A.T := by
    -- compare after multiplying by `2 p m > 0`
    have key : (mHalf p : ℤ) * (bCoef n p a : ℤ) ≤ (mHalf p : ℤ) * A.T := by
      have hstep : 2 * (p : ℤ) * ((mHalf p : ℤ) * (bCoef n p a : ℤ))
          ≤ 2 * (p : ℤ) * ((mHalf p : ℤ) * A.T) := by
        have hlhs : 2 * (p : ℤ) * ((mHalf p : ℤ) * (bCoef n p a : ℤ))
            = ((p : ℤ) - 1) * ((p : ℤ) * (bCoef n p a : ℤ)) := by
          rw [← h2mZ]; ring
        have hrhs : (mHalf p : ℤ) * A.T
            = (h n : ℤ) - (L0 M : ℤ) + 3 * ((N n : ℤ) - (mFloor p (N n) : ℤ)) - A.E := by
          linarith [hTE]
        rw [hlhs, hrhs]
        have hb' : ((p : ℤ) - 1) * ((p : ℤ) * (bCoef n p a : ℤ))
            ≤ ((p : ℤ) - 1) * (6 * (N n : ℤ) + 3 * (p : ℤ) - 1) := by
          have : (0 : ℤ) ≤ (p : ℤ) - 1 := by omega
          nlinarith [hbZ]
        refine le_trans hb' ?_
        nlinarith [hmNZ, hE, hE0, hhLZ, hp0Z]
      have h2p : (0 : ℤ) < 2 * (p : ℤ) := by omega
      exact le_of_mul_le_mul_left hstep h2p
    exact le_of_mul_le_mul_left key hmpos
  have heps : (0 : ℤ) ≤ (A.eps a : ℤ) := Int.natCast_nonneg _
  simp only [L]
  omega

end InnerAlloc

end Zeta5
