import Zeta5
open Zeta5
-- (2) hypothesis hΔpos is discharged
#check @Zeta5.delta_pos
example (n : ℕ) (hn : 0 < n) := Zeta5.RealBound.eq_6_14 n hn (Zeta5.delta_pos n)
#print axioms Zeta5.RealBound.eq_6_14
#print axioms Zeta5.RealBound.prop_6_3
#print axioms Zeta5.prop_6_3
#print axioms Zeta5.zeta5_irrational
#print axioms Zeta5.delta_pos
-- statements
#check @Zeta5.RealBound.eq_6_14
#check @Zeta5.prop_6_3
#print Zeta5.RealBound.Irho
#print Zeta5.RealBound.M0
#print Zeta5.Ubar
#print Zeta5.lam
#print Zeta5.Delta
#print Zeta5.F
#check @Zeta5.Sec6.cauchy_cnd
#check @Zeta5.Sec6.arcsine_pot
#check @Zeta5.Sec6.eq_6_6_cauchy
#check @Zeta5.Sec6.configBound
#check @Zeta5.Sec6.Gram.andreief
#check @Zeta5.Sec6.Gram.eq_6_10
#check @Zeta5.Sec6.Num.cell_sound
#check @Zeta5.Sec6.Num.eq_6_7_closed
#check @Zeta5.Sec6.rho_cross
#check @Zeta5.Sec6.smooth_err_norm
#check @Zeta5.Sec6.rho_energy_ge
#check @Zeta5.Sec6.Num.tail_bound_ge4
#check @Zeta5.RealBound.reg_const_le_sixty
#check @Zeta5.Sec6.Gram.paper_6_9_admissible
-- does Interface.prop_6_3 use RealBound.prop_6_3 ? (value)
#print Zeta5.prop_6_3

-- direct users of the two axioms among Zeta5 constants
open Lean Elab Command in
#eval show CommandElabM Unit from do
  let env ← getEnv
  for ax in [``Zeta5.Axioms.hermite_pole_integral, ``Zeta5.Axioms.pnt_prime_riemann_sum] do
    let mut users : Array Name := #[]
    for (n, ci) in env.constants.toList do
      if (`Zeta5).isPrefixOf n then
        let uses := ci.type.getUsedConstants.contains ax ||
          (match ci.value? (allowOpaque := true) with | some v => v.getUsedConstants.contains ax | none => false)
        if uses && n != ax then users := users.push n
    logInfo m!"direct users of {ax}: {users}"
