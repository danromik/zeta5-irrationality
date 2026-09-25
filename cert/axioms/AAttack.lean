/-
cert/axioms/AAttack.lean — attacks on the one remaining axiom, and on the two theorems that
replaced the former axioms (certification of the `axioms` branch, 2026-09-24).

  (a) FIDELITY.  The axiom `Zeta5.Axioms.chebyshev_theta_asymptotic` is checked against the
      textbook statement written out from scratch, with no project name and no `Chebyshev.*`
      abbreviation: `(∑_{p ≤ x prime} log p)/x → 1`.  It is also shown EQUIVALENT (both
      directions, sorry-free, no axiom) to the asymptotic-equivalence form `θ ~[atTop] id`,
      i.e. `θ(x) ~ x`.  So it is neither stronger nor weaker than the cited statement.  Lean
      conventions: `x / 0 = 0` and `⌊x⌋₊ = 0` for `x < 0` occur only for `x ≤ 0`, which the
      filter `atTop` ignores; the statement involves no integral, no `tsum` and no `rpow`.
  (b) NON-VACUITY of the two former axioms, now theorems: the consequences C3Attack.lean
      derived from the axioms are re-derived from the theorems; `#print axioms` must show
      `Hermite.pole_integral` axiom-free and `PNT.prime_riemann_sum` using only the PNT.
  (c) No `unsafe` / `partial` constant in the cone of the main theorem (C3Attack.lean (c),
      copied verbatim).

Run from the repository root, after `lake build`:
  lake env lean cert/axioms/AAttack.lean
-/
import Zeta5

open MeasureTheory Set Filter Topology Asymptotics Lean Elab Command

namespace AAtt

/-! ## (a) Fidelity of the axiom. -/

/-- The textbook prime number theorem in Chebyshev's form, written out with no abbreviation:
`(1/x) ∑_{p prime, p ≤ x} log p → 1`.  The axiom proves it with `exact`, i.e. the two are the
same proposition up to unfolding `Chebyshev.theta`. -/
theorem pnt_textbook :
    Tendsto (fun x : ℝ =>
        (∑ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime, Real.log (p : ℝ)) / x)
      atTop (𝓝 1) := by
  have h := Zeta5.Axioms.chebyshev_theta_asymptotic
  refine h.congr fun x => ?_
  congr 1
  rw [Chebyshev.theta]
  apply Finset.sum_congr ?_ (fun _ _ => rfl)
  ext p
  simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_range]
  constructor
  · rintro ⟨⟨_, h2⟩, hp⟩; exact ⟨by omega, hp⟩
  · rintro ⟨h1, hp⟩; exact ⟨⟨hp.pos, by omega⟩, hp⟩

/-- The converse: the textbook statement implies the axiom (so they are equivalent). -/
theorem axiom_of_textbook
    (h : Tendsto (fun x : ℝ =>
        (∑ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime, Real.log (p : ℝ)) / x)
      atTop (𝓝 1)) :
    Tendsto (fun x : ℝ => Chebyshev.theta x / x) atTop (𝓝 1) := by
  refine h.congr fun x => ?_
  congr 1
  rw [Chebyshev.theta]
  apply Finset.sum_congr ?_ (fun _ _ => rfl)
  ext p
  simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_range]
  constructor
  · rintro ⟨h1, hp⟩; exact ⟨⟨hp.pos, by omega⟩, hp⟩
  · rintro ⟨⟨_, h2⟩, hp⟩; exact ⟨by omega, hp⟩

/-- `θ(x) ~ x` as an asymptotic equivalence is EQUIVALENT to the axiom's statement, with no
axiom used. -/
theorem axiom_iff_isEquivalent :
    Tendsto (fun x : ℝ => Chebyshev.theta x / x) atTop (𝓝 1)
      ↔ Chebyshev.theta ~[atTop] (fun x : ℝ => x) := by
  have hz : ∀ᶠ x : ℝ in atTop, x ≠ 0 := eventually_ne_atTop 0
  rw [isEquivalent_iff_tendsto_one hz]
  rfl

/-- The axiom in the form `θ(x) ~ x`. -/
theorem theta_equiv_id : Chebyshev.theta ~[atTop] (fun x : ℝ => x) :=
  axiom_iff_isEquivalent.mp Zeta5.Axioms.chebyshev_theta_asymptotic

/-! ## (b) Non-vacuity of the two former axioms, now theorems. -/

/-- Hermite at `a = 1`: `∫_0^∞ w(y)/(y²+1) dy = ζ(5) − 3/4`. -/
theorem hermite_at_one :
    ∫ y in Ioi (0 : ℝ), Zeta5.wt y / (y ^ 2 + 1 ^ 2) = Zeta5.zeta5 - 3 / 4 := by
  rw [Zeta5.Hermite.pole_integral 1 one_pos]
  unfold Zeta5.zeta5
  norm_num
  ring

/-- PNT form on `[1, 2]` with `φ ≡ 1`: `(θ(2X) − θ(X))/X → 1` (up to the floors). -/
theorem pnt_dyadic :
    Tendsto (fun X : ℝ =>
        (∑ p ∈ (Finset.Ioc ⌊(1 : ℝ) * X⌋₊ ⌊(2 : ℝ) * X⌋₊).filter Nat.Prime,
          (fun _ : ℝ => (1 : ℝ)) (p / X) * Real.log p) / X)
      atTop (𝓝 1) := by
  have h := Zeta5.PNT.prime_riemann_sum 1 2 (by norm_num) (by norm_num)
    (fun _ => (1 : ℝ)) ⟨1, fun _ _ => by norm_num⟩ ⟨∅, fun _ _ _ => continuousAt_const⟩
  have hI : (∫ _ in (1 : ℝ)..2, (1 : ℝ)) = 1 := by norm_num
  rw [hI] at h
  exact h

end AAtt

#check @Zeta5.Axioms.chebyshev_theta_asymptotic
#print Chebyshev.theta
#print axioms AAtt.pnt_textbook
#print axioms AAtt.axiom_of_textbook
#print axioms AAtt.axiom_iff_isEquivalent
#print axioms AAtt.theta_equiv_id
#print axioms AAtt.hermite_at_one
#print axioms AAtt.pnt_dyadic
#print axioms Zeta5.Hermite.pole_integral
#print axioms Zeta5.PNT.prime_riemann_sum

/-! ## (c) No `unsafe` / `partial` constant in the cone (C3Attack.lean (c), verbatim). -/

elab "#c3unsafe" : command => do
  let env ← getEnv
  let root := ``Zeta5.zeta5_irrational
  let mut seen : Std.HashSet Name := {}
  seen := seen.insert root
  let mut q : Array Name := #[root]
  let mut i := 0
  while h : i < q.size do
    let n := q[i]
    i := i + 1
    match env.find? n with
    | none => pure ()
    | some ci =>
      let es : Array Expr := match ci with
        | .defnInfo v => #[v.type, v.value] | .thmInfo v => #[v.type, v.value]
        | .opaqueInfo v => #[v.type, v.value]
        | .recInfo v => #[v.type] ++ v.rules.toArray.map (·.rhs)
        | _ => #[ci.type]
      let extra : Array Name := match ci with
        | .inductInfo v => v.ctors.toArray ++ v.all.toArray
        | .ctorInfo v => #[v.induct]
        | .recInfo v => v.all.toArray
        | _ => #[]
      for e in es do
        for c in e.getUsedConstants do
          unless seen.contains c do seen := seen.insert c; q := q.push c
      for c in extra do
        unless seen.contains c do seen := seen.insert c; q := q.push c
  let bad := q.filter fun n => match env.find? n with
    | some ci => ci.isUnsafe || ci.isPartial
    | none => false
  let recs := #[`Zeta5.AppendixB.ChainOK._unsafe_rec, `Zeta5.AppendixB.chainEnd._unsafe_rec,
    `Zeta5.AppendixB.chainVal._unsafe_rec, `Zeta5.Audit.visit._unsafe_rec,
    `Zeta5.RealBound.chainB._unsafe_rec]
  logInfo s!"cone size (native walk) {q.size}\nunsafe or partial constants in the cone ({bad.size}): {bad.toList}\n_unsafe_rec auxiliaries in the cone: {(recs.filter seen.contains).toList}\nkinds of the five: {recs.toList.map fun r => match env.find? r with | some ci => (ci.isUnsafe, ci.isPartial) | none => (false, false)}"

#c3unsafe
