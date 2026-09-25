/-
Zeta5/Tail.lean

**§5.3, the tail estimates (5.15)–(5.17) of A. Fauzan, "ζ(5) is irrational" (p. 16).**

This file proves the analytic content of (5.15)–(5.17): the two integrations by parts that
turn `∫ R(x) x^{-3}` into boundary terms plus small remainders.  It is written against an
*abstract* bounded remainder `Q`, so that `Zeta5/AppendixB.lean` can apply it to the concrete
`Qcl` of (5.13) without an import cycle (`AppendixB.lean` imports this file).

The paper's statements, verbatim (p. 16).  With `f = {x}`, `g = {αx}`,

  `R(x) = x F(x) + Q(x)`,  `F(x) = 4λ + 2λf - 12λg`,                                  (5.12)
  `-1/2 ≤ Q(x) ≤ 13/8`,                                                              (5.14)
  `𝒫(x) = 74g(1-g) - λf(1-f)`,  `𝒫̄ = 2923/240`,
  `G₀(v) = v(1-v)(2v-1)/6`,  `𝒞(x) = (74/α)G₀(g) - λG₀(f)`,
  `𝒫' = F + λ`,  `𝒞' = 𝒫 - 𝒫̄`  (away from the finitely many breakpoints in a period),
  `|𝒞(x)| ≤ 118511/(4320√3) < 16`,

and "two integrations by parts now give"

  `∫_T^∞ R(x)x^{-3} dx = -λ/T - 𝒫(T)/T² + 𝒫̄/T² - 2𝒞(T)/T³`
                       ` + 6∫_T^∞ 𝒞(x)x^{-4} dx + ∫_T^∞ Q(x)x^{-3} dx`,               (5.15)

whence `∫_20^∞ R x^{-3} ≤ -2689/48000` (5.16) at `T = 20`, where `𝒫(20) = 37/2` and
`𝒞(20) = 0`, and `∫_M^∞ R x^{-3} ≥ -λ/M + (2923/240 - 1/4)/M² - 32/M³` (5.17) for `40 | M`,
where `𝒫(M) = 𝒞(M) = 0`.

**How this is formalised.**  (5.16) and (5.17) are only ever used through their *difference*
`∫_20^M = ∫_20^∞ - ∫_M^∞`, so the improper integral is avoided altogether: (5.15) is proved
here as a genuine identity on the **finite** interval `[T,X]`,

  `∫_T^X (F(x)/x² - 6𝒞(x)/x⁴) dx = W(X) - W(T)`,  `W(x) = (λx² + (𝒫(x)-𝒫̄)x + 2𝒞(x))/x³`,

by the fundamental theorem of calculus in its right-derivative form
(`intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le`).  `𝒫` and `𝒞` are *continuous*
(the paper says so: "Define the continuous periodic functions"), because `u(1-u)` and `G₀`
vanish at both `0` and `1`; and their right-derivatives exist at **every** point, breakpoints
included, because `x ↦ {cx}` has right-derivative `c` everywhere.  So no splitting at the
breakpoints — whose number grows with `M` — is needed.

Feeding `𝒞 ≤ 16` and `Q ≤ 13/8` into the two remaining integrals and evaluating `W` at `20`
and at `M` then gives, for `40 | M`,

  `∫_20^M R(x)x^{-3} dx ≤ -2689/48000 + λ/M - (2923/240 + 13/16)/M² - 32/M³`,

which is **stronger** than the assembled form of (5.16)–(5.17) that Appendix B consumes
(`-2689/48000 + λ/M - (2923/240 - 1/4)/M² + 32/M³`).

Numerical values: `𝒫(20) = 37/2`,
`𝒞(20) = 0`, `𝒫(M) = 𝒞(M) = 0` for `40 | M`, `max|𝒞| = 118511/(4320√3) = 15.8385… < 16`,
`max|G₀| = 0.0160375… < 161/10000`, and the bound above brackets the true integral at
`M = 40, 80, 120, 200` (referee audit of the preprint; see README, "Provenance").
-/
import Zeta5.Basic

namespace Zeta5

namespace Tail

open MeasureTheory Set Filter

noncomputable section

/-! ## 1.  The right-derivative of `x ↦ {cx}`

`⌊cy⌋` is constant on `[x, (⌊cx⌋+1)/c)`, so `y ↦ ⌊cy⌋` has right-derivative `0` at every
point and `y ↦ {cy} = cy - ⌊cy⌋` has right-derivative `c`.  This is what lets the FTC below
be applied on the whole of `[20,M]` at once, rather than piece by piece. -/

lemma hasDerivWithinAt_floor_mul {c : ℝ} (hc : 0 < c) (x : ℝ) :
    HasDerivWithinAt (fun y : ℝ => ((⌊c * y⌋ : ℤ) : ℝ)) 0 (Set.Ioi x) x := by
  have hfl : (⌊c * x⌋ : ℝ) ≤ c * x := Int.floor_le _
  have hfu : c * x < (⌊c * x⌋ : ℝ) + 1 := Int.lt_floor_add_one _
  have hlt : x < ((⌊c * x⌋ : ℝ) + 1) / c := by
    rw [lt_div_iff₀ hc]; nlinarith
  refine (hasDerivWithinAt_const x (Set.Ioi x) ((⌊c * x⌋ : ℤ) : ℝ)).congr_of_eventuallyEq
    ?_ rfl
  filter_upwards [Ioo_mem_nhdsGT hlt] with y hy
  have h1 : (⌊c * x⌋ : ℝ) ≤ c * y := by nlinarith [hy.1]
  have h2 : c * y < (⌊c * x⌋ : ℝ) + 1 := by
    have h := hy.2
    rw [lt_div_iff₀ hc] at h
    nlinarith
  have hfloor : ⌊c * y⌋ = ⌊c * x⌋ := by
    rw [Int.floor_eq_iff]
    exact ⟨h1, by linarith⟩
  rw [hfloor]

lemma hasDerivWithinAt_fract_mul {c : ℝ} (hc : 0 < c) (x : ℝ) :
    HasDerivWithinAt (fun y : ℝ => Int.fract (c * y)) c (Set.Ioi x) x := by
  have hmul : HasDerivWithinAt (fun y : ℝ => c * y) (c * 1) (Set.Ioi x) x :=
    (hasDerivWithinAt_id x (Set.Ioi x)).const_mul c
  have h1 : HasDerivWithinAt (fun y : ℝ => c * y) c (Set.Ioi x) x := by
    rwa [mul_one] at hmul
  have h2 := hasDerivWithinAt_floor_mul hc x
  have heq : (fun y : ℝ => Int.fract (c * y))
      = fun y : ℝ => c * y - ((⌊c * y⌋ : ℤ) : ℝ) := by
    funext y; exact (Int.self_sub_floor (c * y)).symm
  rw [heq]
  have h3 : HasDerivWithinAt (fun y : ℝ => c * y - ((⌊c * y⌋ : ℤ) : ℝ)) (c - 0)
      (Set.Ioi x) x := h1.fun_sub h2
  rwa [sub_zero] at h3

lemma hasDerivWithinAt_fract (x : ℝ) :
    HasDerivWithinAt (fun y : ℝ => Int.fract y) 1 (Set.Ioi x) x := by
  have h := hasDerivWithinAt_fract_mul (c := (1 : ℝ)) one_pos x
  have heq : (fun y : ℝ => Int.fract ((1 : ℝ) * y)) = fun y : ℝ => Int.fract y := by
    funext y; rw [one_mul]
  rwa [heq] at h

/-! ## 2.  The periodic data `F`, `𝒫`, `G₀`, `𝒞` of p. 16 -/

/-- **(5.12)**: `F(x) = 4λ + 2λ{x} - 12λ{αx}`.  Identical to `Zeta5.AppendixB.Fcl`. -/
def Fc (x : ℝ) : ℝ :=
  4 * (lam : ℝ) + 2 * (lam : ℝ) * Int.fract x - 12 * (lam : ℝ) * Int.fract ((alpha : ℝ) * x)

/-- `φ(u) = u(1-u)`; `φ(0) = φ(1) = 0`, so `φ ∘ fract` is continuous. -/
def phi (u : ℝ) : ℝ := u * (1 - u)

/-- `G₀(v) = v(1-v)(2v-1)/6` (p. 16); `G₀(0) = G₀(1) = 0`. -/
def G0 (v : ℝ) : ℝ := v * (1 - v) * (2 * v - 1) / 6

/-- `𝒫(x) = 74{αx}(1-{αx}) - λ{x}(1-{x})` (p. 16). -/
def Pc (x : ℝ) : ℝ := 74 * phi (Int.fract ((alpha : ℝ) * x)) - (lam : ℝ) * phi (Int.fract x)

/-- `𝒞(x) = (74/α)G₀({αx}) - λG₀({x})` (p. 16). -/
def Cc (x : ℝ) : ℝ :=
  74 / (alpha : ℝ) * G0 (Int.fract ((alpha : ℝ) * x)) - (lam : ℝ) * G0 (Int.fract x)

/-- `𝒫̄ = 2923/240` (p. 16); it is `(74 - λ)/6`, the mean value of `𝒫`. -/
def Pbar : ℝ := 2923 / 240

/-- The numerator of the antiderivative produced by the two integrations by parts of (5.15):
`N(x) = λx² + (𝒫(x) - 𝒫̄)x + 2𝒞(x)`. -/
def NN (x : ℝ) : ℝ := (lam : ℝ) * x ^ 2 + (Pc x - Pbar) * x + 2 * Cc x

/-- The antiderivative of (5.15): `W(x) = N(x)/x³ = λ/x + (𝒫(x)-𝒫̄)/x² + 2𝒞(x)/x³`, whose
derivative is `F(x)/x² - 6𝒞(x)/x⁴`. -/
def WW (x : ℝ) : ℝ := NN x / x ^ 3

/-- The majorant `96/x⁴ + (13/8)/x³` of `6𝒞(x)/x⁴ + Q(x)/x³`, and its antiderivative. -/
def Ub (z : ℝ) : ℝ := -32 / z ^ 3 - (13 / 16) / z ^ 2

/-! ## 3.  Continuity of `𝒫` and `𝒞`

The paper calls `𝒫` and `𝒞` *continuous* periodic functions; that is because `φ` and `G₀`
take the same value at `0` and at `1`, so composing with `{·}` does not create a jump. -/

lemma continuous_phi_fract : Continuous fun x : ℝ => phi (Int.fract x) :=
  ContinuousOn.comp_fract'' (f := phi)
    (Continuous.continuousOn (by unfold phi; fun_prop)) (by norm_num [phi])

lemma continuous_G0_fract : Continuous fun x : ℝ => G0 (Int.fract x) :=
  ContinuousOn.comp_fract'' (f := G0)
    (Continuous.continuousOn (by unfold G0; fun_prop)) (by norm_num [G0])

lemma continuous_Pc : Continuous Pc := by
  unfold Pc
  exact (continuous_const.mul
      (continuous_phi_fract.comp (continuous_const.mul continuous_id))).sub
    (continuous_const.mul continuous_phi_fract)

lemma continuous_Cc : Continuous Cc := by
  unfold Cc
  exact (continuous_const.mul
      (continuous_G0_fract.comp (continuous_const.mul continuous_id))).sub
    (continuous_const.mul continuous_G0_fract)

lemma continuous_NN : Continuous NN := by
  unfold NN
  exact ((continuous_const.mul (continuous_pow 2)).add
      ((continuous_Pc.sub continuous_const).mul continuous_id)).add
    (continuous_const.mul continuous_Cc)

lemma continuousOn_WW {a b : ℝ} (ha : 0 < a) : ContinuousOn WW (Set.Icc a b) := by
  refine ContinuousOn.div continuous_NN.continuousOn (continuous_pow 3).continuousOn ?_
  intro y hy
  exact pow_ne_zero _ (ne_of_gt (lt_of_lt_of_le ha hy.1))

/-! ## 4.  `𝒫' = F + λ` and `𝒞' = 𝒫 - 𝒫̄` (p. 16), as right-derivatives everywhere -/

lemma hasDerivAt_phi (u : ℝ) : HasDerivAt phi (1 - 2 * u) u := by
  have hid : HasDerivAt (fun y : ℝ => y) 1 u := hasDerivAt_id u
  have h1 : HasDerivAt (fun y : ℝ => 1 - y) (-1) u := hid.const_sub (1 : ℝ)
  have h2 : HasDerivAt (fun y : ℝ => y * (1 - y)) (1 * (1 - u) + u * (-1)) u :=
    hid.fun_mul h1
  have hphi : phi = fun y : ℝ => y * (1 - y) := rfl
  rw [hphi]
  convert h2 using 1
  ring

lemma hasDerivAt_G0 (u : ℝ) : HasDerivAt G0 (phi u - 1 / 6) u := by
  have hid : HasDerivAt (fun y : ℝ => y) 1 u := hasDerivAt_id u
  have h1 : HasDerivAt (fun y : ℝ => 1 - y) (-1) u := hid.const_sub (1 : ℝ)
  have hm : HasDerivAt (fun y : ℝ => 2 * y) (2 * 1) u := hid.const_mul (2 : ℝ)
  have h2 : HasDerivAt (fun y : ℝ => 2 * y - 1) (2 * 1) u := hm.sub_const (1 : ℝ)
  have hp : HasDerivAt (fun y : ℝ => y * (1 - y)) (1 * (1 - u) + u * (-1)) u :=
    hid.fun_mul h1
  have h3 : HasDerivAt (fun y : ℝ => y * (1 - y) * (2 * y - 1))
      ((1 * (1 - u) + u * (-1)) * (2 * u - 1) + u * (1 - u) * (2 * 1)) u := hp.fun_mul h2
  have h4 : HasDerivAt (fun y : ℝ => y * (1 - y) * (2 * y - 1) / 6)
      (((1 * (1 - u) + u * (-1)) * (2 * u - 1) + u * (1 - u) * (2 * 1)) / 6) u :=
    h3.div_const 6
  have hG0 : G0 = fun y : ℝ => y * (1 - y) * (2 * y - 1) / 6 := rfl
  rw [hG0]
  convert h4 using 1
  simp only [phi]
  ring

/-- `𝒫' = F + λ` (p. 16), as a right-derivative valid at **every** point. -/
lemma Pc_hasDerivWithinAt (x : ℝ) :
    HasDerivWithinAt Pc (Fc x + (lam : ℝ)) (Set.Ioi x) x := by
  have ha : ((alpha : ℚ) : ℝ) = 3 / 40 := by norm_num [alpha]
  have hl : ((lam : ℚ) : ℝ) = 37 / 40 := by norm_num [lam]
  have hapos : (0 : ℝ) < ((alpha : ℚ) : ℝ) := by rw [ha]; norm_num
  have hf := hasDerivWithinAt_fract x
  have hg := hasDerivWithinAt_fract_mul hapos x
  have h1 : HasDerivWithinAt (fun y : ℝ => phi (Int.fract ((alpha : ℝ) * y)))
      ((1 - 2 * Int.fract ((alpha : ℝ) * x)) * ((alpha : ℚ) : ℝ)) (Set.Ioi x) x :=
    (hasDerivAt_phi _).comp_hasDerivWithinAt x hg
  have h2 : HasDerivWithinAt (fun y : ℝ => phi (Int.fract y))
      ((1 - 2 * Int.fract x) * 1) (Set.Ioi x) x :=
    (hasDerivAt_phi _).comp_hasDerivWithinAt x hf
  have h3 := (h1.const_mul (74 : ℝ)).sub (h2.const_mul ((lam : ℚ) : ℝ))
  have hPc : Pc = fun y : ℝ =>
      74 * phi (Int.fract ((alpha : ℝ) * y)) - ((lam : ℚ) : ℝ) * phi (Int.fract y) := rfl
  rw [hPc]
  convert h3 using 1
  rw [Fc, ha, hl]
  ring

/-- `𝒞' = 𝒫 - 𝒫̄` (p. 16), as a right-derivative valid at **every** point. -/
lemma Cc_hasDerivWithinAt (x : ℝ) :
    HasDerivWithinAt Cc (Pc x - Pbar) (Set.Ioi x) x := by
  have ha : ((alpha : ℚ) : ℝ) = 3 / 40 := by norm_num [alpha]
  have hl : ((lam : ℚ) : ℝ) = 37 / 40 := by norm_num [lam]
  have hapos : (0 : ℝ) < ((alpha : ℚ) : ℝ) := by rw [ha]; norm_num
  have hf := hasDerivWithinAt_fract x
  have hg := hasDerivWithinAt_fract_mul hapos x
  have h1 : HasDerivWithinAt (fun y : ℝ => G0 (Int.fract ((alpha : ℝ) * y)))
      ((phi (Int.fract ((alpha : ℝ) * x)) - 1 / 6) * ((alpha : ℚ) : ℝ)) (Set.Ioi x) x :=
    (hasDerivAt_G0 _).comp_hasDerivWithinAt x hg
  have h2 : HasDerivWithinAt (fun y : ℝ => G0 (Int.fract y))
      ((phi (Int.fract x) - 1 / 6) * 1) (Set.Ioi x) x :=
    (hasDerivAt_G0 _).comp_hasDerivWithinAt x hf
  have h3 := (h1.const_mul (74 / ((alpha : ℚ) : ℝ))).sub (h2.const_mul ((lam : ℚ) : ℝ))
  have hCc : Cc = fun y : ℝ =>
      74 / ((alpha : ℚ) : ℝ) * G0 (Int.fract ((alpha : ℝ) * y))
        - ((lam : ℚ) : ℝ) * G0 (Int.fract y) := rfl
  rw [hCc]
  convert h3 using 1
  rw [Pc, Pbar, ha, hl]
  ring

lemma NN_hasDerivWithinAt (x : ℝ) :
    HasDerivWithinAt NN
      ((lam : ℝ) * (2 * x) + ((Fc x + (lam : ℝ)) * x + (Pc x - Pbar) * 1)
        + 2 * (Pc x - Pbar)) (Set.Ioi x) x := by
  have hid : HasDerivWithinAt (fun y : ℝ => y) 1 (Set.Ioi x) x := hasDerivWithinAt_id x _
  have hx2 : HasDerivWithinAt (fun y : ℝ => y ^ 2) (2 * x) (Set.Ioi x) x := by
    have h : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
      simpa using hasDerivAt_pow 2 x
    exact h.hasDerivWithinAt
  have t1 : HasDerivWithinAt (fun y : ℝ => (lam : ℝ) * y ^ 2) ((lam : ℝ) * (2 * x))
      (Set.Ioi x) x := hx2.const_mul _
  have t2 : HasDerivWithinAt (fun y : ℝ => (Pc y - Pbar) * y)
      ((Fc x + (lam : ℝ)) * x + (Pc x - Pbar) * 1) (Set.Ioi x) x :=
    ((Pc_hasDerivWithinAt x).sub_const Pbar).mul hid
  have t3 : HasDerivWithinAt (fun y : ℝ => 2 * Cc y) (2 * (Pc x - Pbar)) (Set.Ioi x) x :=
    (Cc_hasDerivWithinAt x).const_mul 2
  exact (t1.add t2).add t3

/-- The differentiated form of **(5.15)**: `W' = F(x)/x² - 6𝒞(x)/x⁴`, a right-derivative at
every `x ≠ 0`. -/
lemma WW_hasDerivWithinAt {x : ℝ} (hx : x ≠ 0) :
    HasDerivWithinAt WW (Fc x / x ^ 2 - 6 * Cc x / x ^ 4) (Set.Ioi x) x := by
  have hd : HasDerivWithinAt (fun y : ℝ => y ^ 3) (3 * x ^ 2) (Set.Ioi x) x := by
    have h : HasDerivAt (fun y : ℝ => y ^ 3) (3 * x ^ 2) x := by
      simpa using hasDerivAt_pow 3 x
    exact h.hasDerivWithinAt
  have hx3 : (fun y : ℝ => y ^ 3) x ≠ 0 := pow_ne_zero _ hx
  have h : HasDerivWithinAt (fun y : ℝ => NN y / y ^ 3)
      ((((lam : ℝ) * (2 * x) + ((Fc x + (lam : ℝ)) * x + (Pc x - Pbar) * 1)
            + 2 * (Pc x - Pbar)) * x ^ 3 - NN x * (3 * x ^ 2)) / (x ^ 3) ^ 2)
      (Set.Ioi x) x := (NN_hasDerivWithinAt x).fun_div hd hx3
  have hWW : WW = fun y : ℝ => NN y / y ^ 3 := rfl
  rw [hWW]
  convert h using 1
  simp only [NN]
  field_simp
  ring

/-! ## 5.  The sup bounds `|𝒞| < 16` and `|F| ≤ 12`

`max_{[0,1]}|G₀| = 1/(36√3) = 0.01603750…`, which the paper turns into
`|𝒞| ≤ 118511/(4320√3) = 15.8385… < 16`.  To stay inside ℚ we prove the slightly weaker but
still sufficient rational bound `|G₀| ≤ 161/10000 = 0.0161`, which gives
`|𝒞| ≤ (2960/3 + 37/40)·161/10000 = 19080271/1200000 = 15.9002… < 16`. -/

/-- `G₀(v)² ≤ 1/3888 = (1/(36√3))²` on `[0,1]`, the exact supremum of `G₀²`.  The proof is
the factorisation `1/3888 - G₀(v)² = (u - 1/6)²(u + 1/12)/9` with `u = v(1-v) ≥ 0`. -/
lemma G0_sq_le {v : ℝ} (h0 : 0 ≤ v) (h1 : v ≤ 1) : G0 v ^ 2 ≤ 1 / 3888 := by
  have hu : (0 : ℝ) ≤ v * (1 - v) := mul_nonneg h0 (by linarith)
  have key : (0 : ℝ) ≤ (v * (1 - v) - 1 / 6) ^ 2 * (v * (1 - v) + 1 / 12) :=
    mul_nonneg (sq_nonneg _) (by linarith)
  simp only [G0]
  nlinarith [key]

lemma abs_G0_le {v : ℝ} (h0 : 0 ≤ v) (h1 : v ≤ 1) : |G0 v| ≤ 161 / 10000 := by
  have hsq := G0_sq_le h0 h1
  rw [abs_le]
  refine ⟨?_, ?_⟩
  · nlinarith [sq_nonneg (G0 v + 161 / 10000)]
  · nlinarith [sq_nonneg (G0 v - 161 / 10000)]

lemma abs_Cc_le (x : ℝ) : |Cc x| ≤ 16 := by
  have ha : ((alpha : ℚ) : ℝ) = 3 / 40 := by norm_num [alpha]
  have hl : ((lam : ℚ) : ℝ) = 37 / 40 := by norm_num [lam]
  have hg := abs_le.mp (abs_G0_le (v := Int.fract ((alpha : ℝ) * x))
    (Int.fract_nonneg _) (le_of_lt (Int.fract_lt_one _)))
  have hf := abs_le.mp (abs_G0_le (v := Int.fract x)
    (Int.fract_nonneg _) (le_of_lt (Int.fract_lt_one _)))
  have hCc : Cc x = 74 / (3 / 40 : ℝ) * G0 (Int.fract ((alpha : ℝ) * x))
      - (37 / 40 : ℝ) * G0 (Int.fract x) := by
    rw [Cc, show (74 : ℝ) / ((alpha : ℚ) : ℝ) = 74 / (3 / 40 : ℝ) by rw [ha], hl]
  rw [hCc, abs_le]
  constructor
  · norm_num; linarith [hg.1, hg.2, hf.1, hf.2]
  · norm_num; linarith [hg.1, hg.2, hf.1, hf.2]

lemma abs_Fc_le (x : ℝ) : |Fc x| ≤ 12 := by
  have hl : ((lam : ℚ) : ℝ) = 37 / 40 := by norm_num [lam]
  have h1 := Int.fract_nonneg x
  have h2 := Int.fract_lt_one x
  have h3 := Int.fract_nonneg ((alpha : ℝ) * x)
  have h4 := Int.fract_lt_one ((alpha : ℝ) * x)
  rw [Fc, hl, abs_le]
  exact ⟨by linarith, by linarith⟩

lemma abs_six_Cc_le (x : ℝ) : |6 * Cc x| ≤ 96 := by
  have h := abs_Cc_le x
  rw [abs_mul]
  have : |(6 : ℝ)| = 6 := by norm_num
  rw [this]
  linarith

lemma measurable_Fc : Measurable Fc := by
  unfold Fc
  exact (measurable_const.add (measurable_const.mul measurable_fract)).sub
    (measurable_const.mul (measurable_fract.comp (measurable_const_mul _)))

lemma measurable_Cc : Measurable Cc := continuous_Cc.measurable

lemma measurable_six_Cc : Measurable fun x : ℝ => 6 * Cc x :=
  measurable_const.mul measurable_Cc

/-! ## 5b.  **(5.14)**: `-1/2 ≤ Q(x) ≤ 13/8` (p. 16)

The paper's argument, for the shape (5.13)
`Q = (τ(τ-σ) - (τ-σ)_+ + η(1-η))/2 + 9∫B² - 3∫AB` with `∫B² = d_g(1-2d_g)` and
`∫AB = e_f e_g(min(d_f,d_g) - 2d_f d_g)` (B.1):

* "The first numerator in (5.13) lies between `-1/4` and `1/4`": indeed
  `τ(τ-σ) - (τ-σ)_+ ∈ [-1/4, 0]` and `η(1-η) ∈ [0,1/4]`;
* "Each squared integral is at most `1/8`": `d_g(1-2d_g) ∈ [0,1/8]`;
* "Cauchy–Schwarz bounds the absolute value of the mixed integral by `1/8`":
  `min(d_f,d_g) - 2d_f d_g ∈ [0,1/8]`.

"Consequently `-1/2 ≤ Q(x) ≤ 13/8`": `-1/8 + 0 - 3/8 = -1/2` and
`1/8 + 9/8 + 3/8 = 13/8`.  These are stated here for the raw ingredients so that
`AppendixB.lean` can apply them to its concrete `Qcl` without duplicating the algebra. -/

lemma numerator_bounds {t s : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (hs0 : 0 ≤ s) (hs1 : s < 1) :
    -(1 / 4) ≤ t * (t - s) - max 0 (t - s) ∧ t * (t - s) - max 0 (t - s) ≤ 0 := by
  rcases le_total (t - s) 0 with h | h
  · rw [max_eq_left h]
    refine ⟨?_, ?_⟩
    · nlinarith [sq_nonneg (2 * t - 1)]
    · nlinarith
  · rw [max_eq_right h]
    refine ⟨?_, ?_⟩
    · nlinarith [sq_nonneg (2 * t - 1)]
    · nlinarith

lemma eta_bounds {e : ℝ} (he0 : 0 ≤ e) (he1 : e < 1) :
    0 ≤ e * (1 - e) ∧ e * (1 - e) ≤ 1 / 4 := by
  refine ⟨by nlinarith, by nlinarith [sq_nonneg (2 * e - 1)]⟩

lemma square_bounds {d : ℝ} (hd0 : 0 ≤ d) (hd1 : d ≤ 1 / 2) :
    0 ≤ d * (1 - 2 * d) ∧ d * (1 - 2 * d) ≤ 1 / 8 := by
  refine ⟨by nlinarith, by nlinarith [sq_nonneg (4 * d - 1)]⟩

lemma mixed_bounds {df dg : ℝ} (hdf0 : 0 ≤ df) (hdf1 : df ≤ 1 / 2)
    (hdg0 : 0 ≤ dg) (hdg1 : dg ≤ 1 / 2) :
    0 ≤ min df dg - 2 * df * dg ∧ min df dg - 2 * df * dg ≤ 1 / 8 := by
  rcases le_total df dg with h | h
  · rw [min_eq_left h]
    refine ⟨by nlinarith, by nlinarith [sq_nonneg (4 * dg - 1)]⟩
  · rw [min_eq_right h]
    refine ⟨by nlinarith, by nlinarith [sq_nonneg (4 * df - 1)]⟩

/-- **(5.14)** (p. 16), for the shape (5.13): `-1/2 ≤ Q(x) ≤ 13/8`. -/
theorem eq_5_14 {tau sig eta df dg ef eg : ℝ}
    (htau0 : 0 ≤ tau) (htau1 : tau < 1) (hsig0 : 0 ≤ sig) (hsig1 : sig < 1)
    (heta0 : 0 ≤ eta) (heta1 : eta < 1)
    (hdf0 : 0 ≤ df) (hdf1 : df ≤ 1 / 2) (hdg0 : 0 ≤ dg) (hdg1 : dg ≤ 1 / 2)
    (hef : ef = 1 ∨ ef = -1) (heg : eg = 1 ∨ eg = -1) :
    -(1 / 2) ≤ (tau * (tau - sig) - max 0 (tau - sig) + eta * (1 - eta)) / 2
          + 9 * (dg * (1 - 2 * dg)) - 3 * (ef * eg * (min df dg - 2 * df * dg))
      ∧ (tau * (tau - sig) - max 0 (tau - sig) + eta * (1 - eta)) / 2
          + 9 * (dg * (1 - 2 * dg)) - 3 * (ef * eg * (min df dg - 2 * df * dg)) ≤ 13 / 8 := by
  obtain ⟨n1, n2⟩ := numerator_bounds htau0 htau1 hsig0 hsig1
  obtain ⟨e1, e2⟩ := eta_bounds heta0 heta1
  obtain ⟨s1, s2⟩ := square_bounds hdg0 hdg1
  obtain ⟨m1, m2⟩ := mixed_bounds hdf0 hdf1 hdg0 hdg1
  rcases hef with hf | hf <;> rcases heg with hg | hg <;> rw [hf, hg] <;>
    constructor <;> linarith

/-! ## 6.  Integrability -/

/-- A measurable function bounded by `C`, divided by `xⁿ`, is interval-integrable on any
`[a,b] ⊆ (0,∞)`. -/
lemma intervalIntegrable_bdd_div {f : ℝ → ℝ} {a b C : ℝ} (hab : a ≤ b) (ha : 0 < a) (n : ℕ)
    (hmeas : Measurable f) (hbd : ∀ y, |f y| ≤ C) :
    IntervalIntegrable (fun x => f x / x ^ n) volume a b := by
  have hC : 0 ≤ C := le_trans (abs_nonneg _) (hbd a)
  have han : (0 : ℝ) < a ^ n := by positivity
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  refine MeasureTheory.Integrable.mono' (g := fun _ => C / a ^ n)
    (MeasureTheory.integrableOn_const
      (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top))
    ((hmeas.div (measurable_id.pow_const n)).aestronglyMeasurable) ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with y hy
  obtain ⟨hy1, hy2⟩ := hy
  have hy0 : 0 < y := lt_trans ha hy1
  have hyn : (0 : ℝ) < y ^ n := by positivity
  have hle : a ^ n ≤ y ^ n := pow_le_pow_left₀ ha.le (le_of_lt hy1) n
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hyn, div_le_div_iff₀ hyn han]
  nlinarith [mul_le_mul_of_nonneg_right (hbd y) han.le,
    mul_le_mul_of_nonneg_left hle hC]

/-! ## 7.  (5.15) on a finite interval -/

/-- **(5.15)**, in the finite-interval form that makes the improper integral unnecessary:
`∫_T^X (F(x)/x² - 6𝒞(x)/x⁴) dx = W(X) - W(T)`.  This is the pair of integrations by parts
of p. 16: `F = 𝒫' - λ` gives the first, `𝒫 = 𝒞' + 𝒫̄` the second. -/
theorem integration_by_parts {T X : ℝ} (hT : 0 < T) (hTX : T ≤ X) :
    (∫ x in T..X, (Fc x / x ^ 2 - 6 * Cc x / x ^ 4)) = WW X - WW T := by
  refine intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hTX
    (continuousOn_WW hT) (fun y hy => WW_hasDerivWithinAt (ne_of_gt (lt_trans hT hy.1))) ?_
  exact (intervalIntegrable_bdd_div hTX hT 2 measurable_Fc abs_Fc_le).sub
    (intervalIntegrable_bdd_div hTX hT 4 measurable_six_Cc abs_six_Cc_le)

/-! ### The values of `𝒫` and `𝒞` at the two endpoints (p. 16) -/

lemma fract_eq_zero_of_eq_intCast {c : ℝ} {k : ℤ} (h : c = (k : ℝ)) : Int.fract c = 0 := by
  rw [h, Int.fract_intCast]

/-- `𝒫(20) = 37/2` and `𝒞(20) = 0` (p. 16): `f = {20} = 0`, `g = {3/2} = 1/2`. -/
lemma Pc_Cc_twenty : Pc 20 = 37 / 2 ∧ Cc 20 = 0 := by
  have ha : ((alpha : ℚ) : ℝ) = 3 / 40 := by norm_num [alpha]
  have h20 : Int.fract (20 : ℝ) = 0 := fract_eq_zero_of_eq_intCast (k := 20) (by norm_num)
  have hfl : ⌊(3 : ℝ) / 2⌋ = 1 := by rw [Int.floor_eq_iff]; norm_num
  have hg : Int.fract (((alpha : ℚ) : ℝ) * 20) = 1 / 2 := by
    rw [ha, show (3 : ℝ) / 40 * 20 = 3 / 2 by norm_num, Int.fract, hfl]
    norm_num
  refine ⟨?_, ?_⟩
  · rw [Pc, hg, h20]; norm_num [phi]
  · rw [Cc, hg, h20]; norm_num [G0]

/-- `𝒫(M) = 𝒞(M) = 0` for `40 | M` (p. 16): `f = {M} = 0` and `g = {3M/40} = 0`. -/
lemma Pc_Cc_of_dvd {M : ℕ} (hM : 40 ∣ M) : Pc (M : ℝ) = 0 ∧ Cc (M : ℝ) = 0 := by
  obtain ⟨k, rfl⟩ := hM
  have ha : ((alpha : ℚ) : ℝ) = 3 / 40 := by norm_num [alpha]
  have hM0 : Int.fract (((40 * k : ℕ) : ℝ)) = 0 := Int.fract_natCast _
  have hg : Int.fract (((alpha : ℚ) : ℝ) * ((40 * k : ℕ) : ℝ)) = 0 := by
    refine fract_eq_zero_of_eq_intCast (k := (3 * k : ℤ)) ?_
    rw [ha]; push_cast; ring
  refine ⟨?_, ?_⟩
  · rw [Pc, hg, hM0]; norm_num [phi]
  · rw [Cc, hg, hM0]; norm_num [G0]

/-! ### The elementary majorant integral `∫ (96/x⁴ + (13/8)/x³)` -/

lemma continuousOn_ub {T X : ℝ} (hT : 0 < T) (hTX : T ≤ X) :
    ContinuousOn (fun x : ℝ => 96 / x ^ 4 + (13 / 8) / x ^ 3) (Set.uIcc T X) := by
  have hsub : ∀ y ∈ Set.uIcc T X, y ≠ 0 := by
    intro y hy
    rw [Set.uIcc_of_le hTX] at hy
    exact ne_of_gt (lt_of_lt_of_le hT hy.1)
  exact (ContinuousOn.div continuousOn_const (continuous_pow 4).continuousOn
      fun y hy => pow_ne_zero _ (hsub y hy)).add
    (ContinuousOn.div continuousOn_const (continuous_pow 3).continuousOn
      fun y hy => pow_ne_zero _ (hsub y hy))

lemma integral_ub {T X : ℝ} (hT : 0 < T) (hTX : T ≤ X) :
    (∫ x in T..X, (96 / x ^ 4 + (13 / 8) / x ^ 3)) = Ub X - Ub T := by
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y hy => ?_)
    ((continuousOn_ub hT hTX).intervalIntegrable)
  have hy0 : y ≠ 0 := by
    rw [Set.uIcc_of_le hTX] at hy
    exact ne_of_gt (lt_of_lt_of_le hT hy.1)
  have h1 : HasDerivAt (fun z : ℝ => z ^ 3) (3 * y ^ 2) y := by
    simpa using hasDerivAt_pow 3 y
  have h2 : HasDerivAt (fun z : ℝ => z ^ 2) (2 * y) y := by
    simpa using hasDerivAt_pow 2 y
  have e1 : HasDerivAt (fun z : ℝ => (-32 : ℝ) / z ^ 3)
      ((0 * y ^ 3 - (-32 : ℝ) * (3 * y ^ 2)) / (y ^ 3) ^ 2) y :=
    (hasDerivAt_const y (-32 : ℝ)).fun_div h1 (pow_ne_zero 3 hy0)
  have e2 : HasDerivAt (fun z : ℝ => (-(13 / 16) : ℝ) / z ^ 2)
      ((0 * y ^ 2 - (-(13 / 16) : ℝ) * (2 * y)) / (y ^ 2) ^ 2) y :=
    (hasDerivAt_const y (-(13 / 16) : ℝ)).fun_div h2 (pow_ne_zero 2 hy0)
  have e3 : HasDerivAt (fun z : ℝ => (-32 : ℝ) / z ^ 3 + (-(13 / 16) : ℝ) / z ^ 2)
      ((0 * y ^ 3 - (-32 : ℝ) * (3 * y ^ 2)) / (y ^ 3) ^ 2
        + (0 * y ^ 2 - (-(13 / 16) : ℝ) * (2 * y)) / (y ^ 2) ^ 2) y := e1.fun_add e2
  have hfun : Ub = fun z : ℝ => (-32 : ℝ) / z ^ 3 + (-(13 / 16) : ℝ) / z ^ 2 := by
    funext z; rw [Ub]; ring
  rw [hfun]
  convert e3 using 1
  field_simp
  ring

/-! ## 8.  The main estimate: (5.16) and (5.17) combined -/

/-- **(5.16)–(5.17) combined** (p. 16), in the sharpened form this file actually proves.
With an abstract remainder `Q` satisfying (5.14), for `M ∈ 40ℤ_{>0}`

`∫_20^M (xF(x) + Q(x))x^{-3} dx ≤ -2689/48000 + λ/M - (2923/240 + 13/16)/M² - 32/M³`.

Known-answer controls (from the referee audit; see README, "Provenance"): at
`M = 40, 80, 120, 200` the true integral is `-0.04473, -0.05047, -0.05324, -0.05576` and the
right-hand side here is
`-0.04152, -0.04655, -0.04923, -0.05172`. -/
theorem tail_bound_strong {Qc : ℝ → ℝ} (hQm : Measurable Qc)
    (hQlo : ∀ x, -(1 / 2) ≤ Qc x) (hQhi : ∀ x, Qc x ≤ 13 / 8)
    {M : ℕ} (hM : 40 ∣ M) (hM0 : 0 < M) :
    (∫ x in (20 : ℝ)..(M : ℝ), (x * Fc x + Qc x) / x ^ 3)
      ≤ -2689 / 48000 + (lam : ℝ) / (M : ℝ)
          - (2923 / 240 + 13 / 16) / (M : ℝ) ^ 2 - 32 / (M : ℝ) ^ 3 := by
  have hl : ((lam : ℚ) : ℝ) = 37 / 40 := by norm_num [lam]
  have hM40 : 40 ≤ M := Nat.le_of_dvd hM0 hM
  have hMR : (40 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM40
  have hMpos : (0 : ℝ) < (M : ℝ) := by linarith
  have h20 : (0 : ℝ) < 20 := by norm_num
  have h20M : (20 : ℝ) ≤ (M : ℝ) := by linarith
  have hQabs : ∀ y, |Qc y| ≤ 13 / 8 := fun y => by
    rw [abs_le]; exact ⟨by linarith [hQlo y], hQhi y⟩
  -- the three integrable pieces
  have iA : IntervalIntegrable (fun x : ℝ => Fc x / x ^ 2 - 6 * Cc x / x ^ 4)
      volume 20 (M : ℝ) :=
    (intervalIntegrable_bdd_div h20M h20 2 measurable_Fc abs_Fc_le).sub
      (intervalIntegrable_bdd_div h20M h20 4 measurable_six_Cc abs_six_Cc_le)
  have iB : IntervalIntegrable (fun x : ℝ => 6 * Cc x / x ^ 4 + Qc x / x ^ 3)
      volume 20 (M : ℝ) :=
    (intervalIntegrable_bdd_div h20M h20 4 measurable_six_Cc abs_six_Cc_le).add
      (intervalIntegrable_bdd_div h20M h20 3 hQm hQabs)
  have iC : IntervalIntegrable (fun x : ℝ => 96 / x ^ 4 + (13 / 8) / x ^ 3)
      volume 20 (M : ℝ) := (continuousOn_ub h20 h20M).intervalIntegrable
  -- split the integrand
  have hsplit : (∫ x in (20 : ℝ)..(M : ℝ), (x * Fc x + Qc x) / x ^ 3)
      = (∫ x in (20 : ℝ)..(M : ℝ), (Fc x / x ^ 2 - 6 * Cc x / x ^ 4))
        + (∫ x in (20 : ℝ)..(M : ℝ), (6 * Cc x / x ^ 4 + Qc x / x ^ 3)) := by
    rw [← intervalIntegral.integral_add iA iB]
    refine intervalIntegral.integral_congr ?_
    intro y hy
    rw [Set.uIcc_of_le h20M] at hy
    have hy0 : y ≠ 0 := ne_of_gt (lt_of_lt_of_le h20 hy.1)
    field_simp
    ring
  -- first piece: the two integrations by parts
  have hIBP := integration_by_parts (T := (20 : ℝ)) (X := (M : ℝ)) h20 h20M
  -- second piece: the two sup bounds of (5.14) and p. 16
  have hmono : (∫ x in (20 : ℝ)..(M : ℝ), (6 * Cc x / x ^ 4 + Qc x / x ^ 3))
      ≤ (∫ x in (20 : ℝ)..(M : ℝ), (96 / x ^ 4 + (13 / 8) / x ^ 3)) := by
    refine intervalIntegral.integral_mono_on h20M iB iC ?_
    intro y hy
    have hy0 : (0 : ℝ) < y := lt_of_lt_of_le h20 hy.1
    have hy4 : (0 : ℝ) < y ^ 4 := by positivity
    have hy3 : (0 : ℝ) < y ^ 3 := by positivity
    have hC : 6 * Cc y ≤ 96 := le_trans (le_abs_self _) (abs_six_Cc_le y)
    have b1 : 6 * Cc y / y ^ 4 ≤ 96 / y ^ 4 :=
      (div_le_div_iff_of_pos_right hy4).mpr hC
    have b2 : Qc y / y ^ 3 ≤ (13 / 8) / y ^ 3 :=
      (div_le_div_iff_of_pos_right hy3).mpr (hQhi y)
    linarith
  rw [integral_ub h20 h20M] at hmono
  -- the endpoint values of `W`
  have hW20 : WW 20 = 2689 / 48000 + (1 / 250 + 13 / 6400) := by
    rw [WW, NN, Pc_Cc_twenty.1, Pc_Cc_twenty.2, Pbar, hl]
    norm_num
  have hWM : WW (M : ℝ) = (37 / 40 : ℝ) / (M : ℝ) - (2923 / 240) / (M : ℝ) ^ 2 := by
    rw [WW, NN, (Pc_Cc_of_dvd hM).1, (Pc_Cc_of_dvd hM).2, Pbar, hl]
    field_simp
    ring
  have hUb20 : Ub 20 = -(1 / 250) - 13 / 6400 := by rw [Ub]; norm_num
  have hUbM : Ub (M : ℝ) = -32 / (M : ℝ) ^ 3 - (13 / 16) / (M : ℝ) ^ 2 := rfl
  rw [hUb20, hUbM] at hmono
  have hkey : -2689 / 48000 + (37 / 40 : ℝ) / (M : ℝ)
        - (2923 / 240 + 13 / 16) / (M : ℝ) ^ 2 - 32 / (M : ℝ) ^ 3
      = ((37 / 40 : ℝ) / (M : ℝ) - (2923 / 240) / (M : ℝ) ^ 2
            - (2689 / 48000 + (1 / 250 + 13 / 6400)))
        + (-32 / (M : ℝ) ^ 3 - (13 / 16) / (M : ℝ) ^ 2
            - (-(1 / 250) - 13 / 6400)) := by ring
  rw [hsplit, hIBP, hW20, hWM, hl, hkey]
  linarith [hmono]

/-- **(5.16)–(5.17) combined**, in exactly the form Appendix B consumes:
`∫_20^M R(x)x^{-3} dx ≤ I_{20,∞} + λ/M - (2923/240 - 1/4)/M² + 32/M³` for `M ∈ 40ℤ_{>0}`,
with `I_{20,∞} = -2689/48000` the bound of (5.16). -/
theorem tail_bound {Qc : ℝ → ℝ} (hQm : Measurable Qc)
    (hQlo : ∀ x, -(1 / 2) ≤ Qc x) (hQhi : ∀ x, Qc x ≤ 13 / 8)
    {M : ℕ} (hM : 40 ∣ M) (hM0 : 0 < M) :
    (∫ x in (20 : ℝ)..(M : ℝ), (x * Fc x + Qc x) / x ^ 3)
      ≤ -2689 / 48000 + (lam : ℝ) / (M : ℝ)
          - (2923 / 240 - 1 / 4) / (M : ℝ) ^ 2 + 32 / (M : ℝ) ^ 3 := by
  have h := tail_bound_strong hQm hQlo hQhi hM hM0
  have hM40 : 40 ≤ M := Nat.le_of_dvd hM0 hM
  have hMR : (40 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM40
  have hM2 : (0 : ℝ) < (M : ℝ) ^ 2 := by positivity
  have hM3 : (0 : ℝ) < (M : ℝ) ^ 3 := by positivity
  have e1 : (2923 / 240 - 1 / 4 : ℝ) / (M : ℝ) ^ 2
      ≤ (2923 / 240 + 13 / 16 : ℝ) / (M : ℝ) ^ 2 :=
    (div_le_div_iff_of_pos_right hM2).mpr (by norm_num)
  have e2 : (0 : ℝ) < 32 / (M : ℝ) ^ 3 := by positivity
  linarith

end

end Tail

end Zeta5
