import Zeta5
open Lean Elab Command
/-- transitive closure of constants used (types and values, incl. opaque/theorem bodies) -/
partial def cone (env : Environment) (root : Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut stack := [root]
  while !stack.isEmpty do
    let n := stack.head!; stack := stack.tail!
    if seen.contains n then continue
    seen := seen.insert n
    if let some ci := env.find? n then
      let mut cs := ci.type.getUsedConstants
      if let some v := ci.value? (allowOpaque := true) then cs := cs ++ v.getUsedConstants
      for c in cs do if !seen.contains c then stack := c :: stack
  return seen
#eval show CommandElabM Unit from do
  let env ← getEnv
  let s := cone env ``Zeta5.zeta5_irrational
  for n in [``Zeta5.RealBound.eq_6_14, ``Zeta5.Sec6.configBound, ``Zeta5.Sec6.cauchy_cnd,
            ``Zeta5.Sec6.Num.eq_6_7_closed, ``Zeta5.Sec6.Gram.andreief, ``Zeta5.Sec6.rho_energy_ge,
            ``Zeta5.RealBound.reg_const_le_sixty, ``Zeta5.RealBound.table2_tiles,
            ``Zeta5.Sec6.Gram.paper_6_9_admissible, ``sorryAx] do
    logInfo m!"{n} in cone of zeta5_irrational: {s.contains n}"
