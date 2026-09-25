/-
Zeta5/Sec6/Num/Eval.lean  —  the interval arithmetic for (6.2)/(6.7) (Lemma 6.1, Appendix A.3):
computable rational enclosures (`logUp`/`logLo`, `atanUp`/`atanLo`, `sqrtUp`/`sqrtLo`),
Table 1 as rationals, and the cell checker `cellOK`/`chainOK`, all executed by the kernel.

Imports only Mathlib.  Every finite computation is `decide +kernel`, i.e. checked by the
kernel; there is no `native_decide` or `implemented_by`.
-/
import Mathlib

/-!
# Kernel-checkable rational enclosures for (6.2) on `[0,2]`

All functions below are computable on `ℚ`, are executed by the kernel (`decide +kernel`),
and every one of them carries an *unconditional* soundness theorem (see `Sound.lean`):
the run-time `if`s guard the hypotheses of the analytic lemmas, and fall back to crude
but true bounds, so no correctness of any heuristic (range reduction, Newton iteration)
is needed.
-/

namespace Zeta5
namespace Sec6
namespace Num

def L2lo : ℚ := 69314718055994530941 / 10 ^ 20
def L2hi : ℚ := 69314718055994530942 / 10 ^ 20
def PIlo : ℚ := 314159265358979323846 / 10 ^ 20
def PIhi : ℚ := 314159265358979323847 / 10 ^ 20

/-- argument rounding (bits). -/
def PREC : ℕ := 32
/-- terms of the `atanh` series for `log`, `|z| ≤ 1/5`. -/
def NLOG : ℕ := 7
/-- terms of the `arctan` series, `|x| ≤ 1/2`. -/
def NATAN : ℕ := 14

def rUp (q : ℚ) : ℚ := ((⌈q * 2 ^ PREC⌉ : ℤ) : ℚ) / 2 ^ PREC
def rDn (q : ℚ) : ℚ := ((⌊q * 2 ^ PREC⌋ : ℤ) : ℚ) / 2 ^ PREC
/-- output rounding to `2^-64` (keeps kernel rationals small). -/
def oUp (q : ℚ) : ℚ := ((⌈q * 2 ^ 64⌉ : ℤ) : ℚ) / 2 ^ 64
def oDn (q : ℚ) : ℚ := ((⌊q * 2 ^ 64⌋ : ℤ) : ℚ) / 2 ^ 64

/-- `∑_{k<n} 2 z^{2k+1}/(2k+1)`, the series of `log((1+z)/(1-z))`. -/
def lser (z : ℚ) : ℕ → ℚ
  | 0 => 0
  | n + 1 => lser z n + 2 * z ^ (2 * n + 1) / (2 * n + 1)
def lerr (z : ℚ) (n : ℕ) : ℚ := 2 * |z| ^ (2 * n + 1) / (1 - z ^ 2)

/-- binary exponents `(k, m)`, heuristically with `q * 2^m / 2^k ∈ [2/3, 3/2]`. -/
def redExp (q : ℚ) : ℕ × ℕ :=
  let a := Nat.log2 q.num.natAbs
  let b := Nat.log2 q.den
  let km : ℕ × ℕ := if b ≤ a then (a - b, 0) else (0, b - a)
  let y := q * 2 ^ km.2 / 2 ^ km.1
  if 3 / 2 < y then (km.1 + 1, km.2) else if y < 2 / 3 then (km.1, km.2 + 1) else km

def logUpRaw (q : ℚ) : ℚ :=
  let e := redExp q
  let y := rUp (q * 2 ^ e.2 / 2 ^ e.1)
  let z := (y - 1) / (y + 1)
  if 0 < y ∧ |z| < 1 / 2 then lser z NLOG + lerr z NLOG + e.1 * L2hi - e.2 * L2lo else q - 1

def logLoRaw (q : ℚ) : ℚ :=
  let e := redExp q
  let y := rDn (q * 2 ^ e.2 / 2 ^ e.1)
  let z := (y - 1) / (y + 1)
  if 0 < y ∧ |z| < 1 / 2 then lser z NLOG - lerr z NLOG + e.1 * L2lo - e.2 * L2hi
  else 1 - 1 / q

def logUp (q : ℚ) : ℚ := oUp (logUpRaw q)
def logLo (q : ℚ) : ℚ := oDn (logLoRaw q)

/-- `∑_{k<n} (-1)^k x^{2k+1}/(2k+1)`. -/
def aser (x : ℚ) : ℕ → ℚ
  | 0 => 0
  | n + 1 => aser x n + (-1) ^ n * x ^ (2 * n + 1) / (2 * n + 1)
def aerr (x : ℚ) (n : ℕ) : ℚ := |x| ^ (2 * n + 1) / (1 - x ^ 2)

/-- lower bound for `arctan x0` (sound for `x0 ≥ 0`). -/
def atanLoRaw (x0 : ℚ) : ℚ :=
  let x := rDn x0
  if x ≤ 1 / 3 then aser x NATAN - aerr x NATAN
  else if x ≤ 3 then PIlo / 4 + aser ((x - 1) / (x + 1)) NATAN - aerr ((x - 1) / (x + 1)) NATAN
  else PIlo / 2 - aser (1 / x) NATAN - aerr (1 / x) NATAN

/-- upper bound for `arctan x0` (sound for `x0 ≥ 0`). -/
def atanUpRaw (x0 : ℚ) : ℚ :=
  let x := rUp x0
  if x ≤ 1 / 3 then aser x NATAN + aerr x NATAN
  else if x ≤ 3 then PIhi / 4 + aser ((x - 1) / (x + 1)) NATAN + aerr ((x - 1) / (x + 1)) NATAN
  else PIhi / 2 - aser (1 / x) NATAN + aerr (1 / x) NATAN

def atanLo (x0 : ℚ) : ℚ := oDn (atanLoRaw x0)
def atanUp (x0 : ℚ) : ℚ := oUp (atanUpRaw x0)

/-- Newton iteration with fuel; its output is checked at run time. -/
def isqrtIter : ℕ → ℕ → ℕ → ℕ
  | 0, _, g => g
  | fuel + 1, n, g =>
    let nx := (g + n / g) / 2
    if nx < g then isqrtIter fuel n nx else g

def isqrt (n : ℕ) : ℕ := if n ≤ 1 then n else isqrtIter 200 n (2 ^ (Nat.log2 n / 2 + 1))

def sqrtCand (q : ℚ) : ℕ := isqrt (⌊q * 4 ^ PREC⌋).toNat

def sqrtLo (q : ℚ) : ℚ :=
  let s : ℚ := (sqrtCand q : ℚ) / 2 ^ PREC
  if s ^ 2 ≤ q then s else 0

def sqrtUp (q : ℚ) : ℚ :=
  let s : ℚ := ((sqrtCand q + 1 : ℕ) : ℚ) / 2 ^ PREC
  if q ≤ s ^ 2 then s else q + 1

/-! Table 1 as rationals. -/
def aQ : ℕ → ℚ
  | 0 => 3906748086 / 10 ^ 12 | 1 => 2312248264 / 10 ^ 12 | 2 => 1402286665 / 10 ^ 12
  | 3 => 881725356 / 10 ^ 12 | 4 => 578197906 / 10 ^ 12 | 5 => 396324613 / 10 ^ 12
  | 6 => 283911191 / 10 ^ 12 | 7 => 212206188 / 10 ^ 12 | 8 => 165097686 / 10 ^ 12
  | 9 => 133347132 / 10 ^ 12 | 10 => 111522114 / 10 ^ 12 | 11 => 96349355 / 10 ^ 12
  | 12 => 85815639 / 10 ^ 12 | 13 => 78667711 / 10 ^ 12 | 14 => 74129565 / 10 ^ 12
  | 15 => 71741310 / 10 ^ 12 | _ => 0
def bQ : ℕ → ℚ
  | 0 => 8992695531 / 10 ^ 12 | 1 => 15340997855 / 10 ^ 12 | 2 => 25730180724 / 10 ^ 12
  | 3 => 41909578246 / 10 ^ 12 | 4 => 65851089563 / 10 ^ 12 | 5 => 99481037884 / 10 ^ 12
  | 6 => 144325727458 / 10 ^ 12 | 7 => 201105762729 / 10 ^ 12 | 8 => 269345996903 / 10 ^ 12
  | 9 => 347089554156 / 10 ^ 12 | 10 => 430806704415 / 10 ^ 12 | 11 => 515561896511 / 10 ^ 12
  | 12 => 595448778546 / 10 ^ 12 | 13 => 664241383483 / 10 ^ 12 | 14 => 716160577112 / 10 ^ 12
  | 15 => 746637295669 / 10 ^ 12 | _ => 0
def cQ : ℕ → ℚ
  | 0 => 10515596180 / 10 ^ 12 | 1 => 29471737793 / 10 ^ 12 | 2 => 42934365099 / 10 ^ 12
  | 3 => 58204231966 / 10 ^ 12 | 4 => 69037621310 / 10 ^ 12 | 5 => 78873099189 / 10 ^ 12
  | 6 => 84856120711 / 10 ^ 12 | 7 => 88396082127 / 10 ^ 12 | 8 => 88303382125 / 10 ^ 12
  | 9 => 85472321255 / 10 ^ 12 | 10 => 78899184238 / 10 ^ 12 | 11 => 70353471918 / 10 ^ 12
  | 12 => 58838976615 / 10 ^ 12 | 13 => 44421321106 / 10 ^ 12 | 14 => 30462865791 / 10 ^ 12
  | 15 => 5959622577 / 10 ^ 12 | _ => 0

def alphaQ : ℚ := 3 / 40
def M0Q : ℚ := -1329 / 200

/-- upper bound for the closed form (A.1) of `U^{ω_[a,b]}(t)`. -/
def UomUp (a b t : ℚ) : ℚ :=
  if a ≤ t ∧ t ≤ b then logUp ((b - a) / 4)
  else logUp ((|t - (a + b) / 2| + sqrtUp ((t - a) * (t - b))) / 2)

def UUpR (t : ℚ) : ℕ → ℚ
  | 0 => 0
  | j + 1 => UUpR t j + cQ j * UomUp (aQ j) (bQ j) t

def UUp (t : ℚ) : ℚ := UUpR t 16

/-- lower bound for (A.5) on `[l, r]`, from termwise monotonicity. -/
def VLo (l r : ℚ) : ℚ :=
  let sl := sqrtLo l
  let sr := sqrtUp r
  let t12 : ℚ := if sl = 0 then PIhi / 2 else atanUp (alphaQ / sl)
  logLo (1 + l) - 6 * alphaQ * logUp (r + alphaQ ^ 2) - 2 + 12 * alphaQ
    + 2 * PIlo * sl + 2 * sl * max 0 (atanLo (1 / sr)) - 12 * sr * t12

def BUp (l r : ℚ) : ℚ :=
  2 * UUp (if r ≤ bQ 0 then l else r) - VLo l r

/-- the cell `[l, r]` is certified against the constant `M`. -/
def cellOK (M l r : ℚ) : Bool :=
  decide (0 ≤ l) && decide (l < r) && (decide (r ≤ bQ 0) || decide (aQ 0 ≤ l))
    && decide (BUp l r ≤ M)

/-- consecutive grid points `k / 10¹²`. -/
def chainOK (M : ℚ) : List ℕ → Bool
  | a :: b :: rest => cellOK M ((a : ℚ) / 10 ^ 12) ((b : ℚ) / 10 ^ 12) && chainOK M (b :: rest)
  | _ => true

end Num
end Sec6
end Zeta5
