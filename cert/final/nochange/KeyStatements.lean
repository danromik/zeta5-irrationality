/-
cert/final/nochange/KeyStatements.lean — prints, in whichever tree it is run from, the
statement of `Zeta5.zeta5_irrational` (and checks it is literally `Irrational Zeta5.zeta5`,
no binders), and the type and value (`pp.all`) of the key definitions and of
`eq_6_14` / `prop_6_3`, with their defining modules. Run in both trees and `diff` the outputs.

  lake env lean cert/final/nochange/KeyStatements.lean
-/
import Zeta5
open Lean Elab Command Meta

elab "#key_check" : command => do
  let env ← getEnv
  let some ci := env.find? ``Zeta5.zeta5_irrational | throwError "missing"
  let expected := mkApp (mkConst ``Irrational) (mkConst ``Zeta5.zeta5)
  logInfo m!"zeta5_irrational: kind thm = {ci matches .thmInfo _}; levelParams = {ci.levelParams}; type == `Irrational Zeta5.zeta5` (Expr.equal): {ci.type.equal expected}; Irrational from {env.getModuleFor? ``Irrational}"
  let some irr := env.find? ``Irrational | throwError "no Irrational"
  logInfo m!"Irrational := {irr.value?.getD (mkConst `none)}"

set_option pp.all true in
elab "#key_dump" : command => do
  let env ← getEnv
  for n in [``Zeta5.zeta5, ``Zeta5.Delta, ``Zeta5.G, ``Zeta5.RealBound.Irho,
            ``Zeta5.RealBound.M0, ``Zeta5.K, ``Zeta5.N, ``Zeta5.h, ``Zeta5.lam,
            ``Zeta5.evalZeta5, ``Zeta5.zeta5_irrational, ``Zeta5.RealBound.eq_6_14,
            ``Zeta5.RealBound.prop_6_3, ``Zeta5.prop_6_3] do
    let some ci := env.find? n | logInfo m!"MISSING {n}"; continue
    let v := match ci with
      | .defnInfo d => m!"{d.value}"
      | _ => m!"(theorem; value not shown)"
    logInfo m!"### {n}  [{env.getModuleFor? n}]\nTYPE: {ci.type}\nVALUE: {v}"

#key_check
set_option pp.all true
#key_dump
