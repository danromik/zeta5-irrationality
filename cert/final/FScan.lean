/-
cert/final/FScan.lean — cert/C3Scan.lean re-run on branch eq614 (code of sections [1]–[5]
copied verbatim; the Zeta5-module filter is by module-name prefix, so the new Zeta5.Sec6.*
modules are included automatically), plus

  [6] a MULTI-ROOT walk from EVERY declaration defined in a Zeta5 module at once: the set of
      axioms reached by the union cone, and the `sorryAx` carriers in it.  If that set is the
      five expected names, then every declaration of the project, not only the main theorem,
      rests on a subset of them.  Run with a planted control: the same walk from the Zeta5
      declarations PLUS the planted constants below must additionally report `sorryAx` and
      the planted axiom.

Original header follows.


Environment-wide scans keyed on the DEFINING MODULE (not the namespace), so internal names,
auxiliary declarations and anything parked in a foreign namespace are included.

  1. every `axiom` in the whole environment;
  2. for every constant defined in a `Zeta5.*` module: axioms, direct `sorryAx` mentions,
     `unsafe` / `partial` definitions, `opaque` constants;
  3. the cone of `Zeta5.zeta5_irrational` (generous successor relation, iterative): its
     `sorry` carriers inside and outside the Zeta5 modules, and the Zeta5 `sorry` carriers it
     does NOT reach (orphans);
  4. the direct users, inside the cone, of each project axiom;
  5. per-module census: declarations reached / declarations defined.

Run from the repository root, after `lake build`:
  lake env lean cert/final/FScan.lean
-/
import Zeta5

open Lean Elab Command

namespace C3S

def constsOf (e : Expr) : Std.HashSet Name := Id.run do
  let mut seen : Std.HashSet Expr := {}
  let mut out : Std.HashSet Name := {}
  let mut stack : Array Expr := #[e]
  let mut fuel := 100000000
  while fuel > 0 do
    fuel := fuel - 1
    match stack.back? with
    | none => break
    | some x =>
      stack := stack.pop
      if seen.contains x then continue
      seen := seen.insert x
      match x with
      | .const n _ => out := out.insert n
      | .app f a => stack := (stack.push f).push a
      | .lam _ t b _ => stack := (stack.push t).push b
      | .forallE _ t b _ => stack := (stack.push t).push b
      | .letE _ t v b _ => stack := ((stack.push t).push v).push b
      | .mdata _ b => stack := stack.push b
      | .proj s _ b => out := out.insert s; stack := stack.push b
      | _ => pure ()
  return out

def succs (ci : ConstantInfo) : Std.HashSet Name :=
  match ci with
  | .axiomInfo v => constsOf v.type
  | .defnInfo v => (constsOf v.type).union (constsOf v.value)
  | .thmInfo v => (constsOf v.type).union (constsOf v.value)
  | .opaqueInfo v => (constsOf v.type).union (constsOf v.value)
  | .quotInfo v => constsOf v.type
  | .inductInfo v => ((constsOf v.type).insertMany v.ctors).insertMany v.all
  | .ctorInfo v => (constsOf v.type).insert v.induct
  | .recInfo v =>
      v.rules.foldl (fun s r => s.union (constsOf r.rhs)) ((constsOf v.type).insertMany v.all)

def moduleOf (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some i => env.header.moduleNames[i.toNat]!
  | none => `_current_file_

def srt (a : Array Name) : List Name := (a.qsort (fun x y => x.toString < y.toString)).toList

end C3S

open C3S in
elab "#c3scan" : command => do
  let env ← getEnv
  -- 1. every axiom in the environment
  let mut allAx : Array Name := #[]
  let mut total := 0
  for (n, ci) in env.constants.map₁.toList do
    total := total + 1
    if ci matches .axiomInfo _ then allAx := allAx.push n
  logInfo s!"[1] constants in environment: {total}\n    axiom declarations ({allAx.size}): {srt allAx}"
  -- 2. module-keyed scan of the Zeta5 modules
  let zmods := env.header.moduleNames.filter (fun m => (`Zeta5).isPrefixOf m || m == `Zeta5)
  let mut zdecls : Array Name := #[]
  let mut zAx : Array Name := #[]
  let mut zSorry : Array Name := #[]
  let mut zUnsafe : Array Name := #[]
  let mut zPartial : Array Name := #[]
  let mut zOpaque : Array Name := #[]
  let mut perMod : Std.HashMap Name Nat := {}
  for (n, ci) in env.constants.map₁.toList do
    let m := moduleOf env n
    if zmods.contains m then
      zdecls := zdecls.push n
      perMod := perMod.insert m (perMod.getD m 0 + 1)
      if ci matches .axiomInfo _ then zAx := zAx.push n
      if (succs ci).contains ``sorryAx then zSorry := zSorry.push n
      if ci.isUnsafe then zUnsafe := zUnsafe.push n
      if ci.isPartial then zPartial := zPartial.push n
      if ci matches .opaqueInfo _ then zOpaque := zOpaque.push n
  logInfo s!"[2] Zeta5 modules: {zmods.size}; declarations defined in them: {zdecls.size}\n    axiom declarations ({zAx.size}): {srt zAx}\n    declarations whose own type/value mentions sorryAx ({zSorry.size}): {srt zSorry}\n    unsafe ({zUnsafe.size}): {srt zUnsafe}\n    partial ({zPartial.size}): {srt zPartial}\n    opaque ({zOpaque.size}): {srt zOpaque}"
  -- 3. the cone
  let root := ``Zeta5.zeta5_irrational
  let mut seen : Std.HashSet Name := {}
  seen := seen.insert root
  let mut queue : Array Name := #[root]
  let mut i := 0
  let mut coneSorry : Array Name := #[]
  let mut axUsers : Std.HashMap Name (Array Name) := {}
  let projAx : Array Name := #[``Zeta5.Axioms.hermite_pole_integral,
    ``Zeta5.Axioms.pnt_prime_riemann_sum]
  while h : i < queue.size do
    let n := queue[i]
    i := i + 1
    match env.find? n with
    | none => pure ()
    | some ci =>
      let ss := succs ci
      if ss.contains ``sorryAx then coneSorry := coneSorry.push n
      for a in projAx do
        if ss.contains a then axUsers := axUsers.insert a ((axUsers.getD a #[]).push n)
      for s in ss do
        unless seen.contains s do
          seen := seen.insert s
          queue := queue.push s
  let outside := coneSorry.filter (fun n => !zmods.contains (moduleOf env n))
  let orphans := zSorry.filter (fun n => !seen.contains n)
  logInfo s!"[3] cone of {root}: {queue.size} constants\n    sorry carriers in the cone ({coneSorry.size}): {srt coneSorry}\n    ... of which OUTSIDE the Zeta5 modules ({outside.size}): {srt outside}\n    Zeta5 sorry carriers NOT in the cone, i.e. orphans ({orphans.size}): {srt orphans}"
  -- 4. direct users of each project axiom
  let mut s4 := "[4] direct users in the cone of each project axiom:"
  for a in projAx do
    s4 := s4 ++ s!"\n    {a}  ({(axUsers.getD a #[]).size}): {srt (axUsers.getD a #[])}"
  logInfo s4
  -- 5. per-module census
  let mut reached : Std.HashMap Name Nat := {}
  for n in queue do
    let m := moduleOf env n
    if zmods.contains m then reached := reached.insert m (reached.getD m 0 + 1)
  let mut s5 := "[5] per-module census, reached/defined:"
  for m in zmods.qsort (fun x y => x.toString < y.toString) do
    s5 := s5 ++ s!"\n    {m} : {reached.getD m 0}/{perMod.getD m 0}"
  logInfo s5

#c3scan


namespace FScanCtl
theorem planted_sorry : (1 : ℕ) = 2 := sorry
axiom planted_axiom : (3 : ℕ) = 4
theorem uses_both : (1 : ℕ) = 2 ∧ (3 : ℕ) = 4 := ⟨planted_sorry, planted_axiom⟩
end FScanCtl

open C3S in
/-- multi-root walk; returns (#constants, axioms reached, sorry carriers). -/
def multiWalk (env : Environment) (roots : Array Name) : Nat × Array Name × Array Name := Id.run do
  let mut seen : Std.HashSet Name := {}
  let mut queue : Array Name := #[]
  for r in roots do
    unless seen.contains r do
      seen := seen.insert r
      queue := queue.push r
  let mut i := 0
  let mut ax : Array Name := #[]
  let mut sc : Array Name := #[]
  while h : i < queue.size do
    let n := queue[i]
    i := i + 1
    match env.find? n with
    | none => pure ()
    | some ci =>
      if ci matches .axiomInfo _ then ax := ax.push n
      let ss := succs ci
      if ss.contains ``sorryAx && n != ``sorryAx then sc := sc.push n
      for s in ss do
        unless seen.contains s do
          seen := seen.insert s
          queue := queue.push s
  return (queue.size, ax, sc)

open C3S in
elab "#fscan6" : command => do
  let env ← getEnv
  let zmods := env.header.moduleNames.filter (fun m => (`Zeta5).isPrefixOf m || m == `Zeta5)
  let mut roots : Array Name := #[]
  for (n, _) in env.constants.map₁.toList do
    if zmods.contains (moduleOf env n) then roots := roots.push n
  let (sz, ax, sc) := multiWalk env roots
  logInfo s!"[6] union cone of ALL {roots.size} Zeta5-module declarations: {sz} constants\n    axioms reached ({ax.size}): {srt ax}\n    sorry carriers ({sc.size}): {srt sc}"
  let ctl := roots ++ #[``FScanCtl.uses_both]
  let (sz', ax', sc') := multiWalk env ctl
  logInfo s!"[6-control] same walk + planted FScanCtl.uses_both: {sz'} constants\n    axioms reached ({ax'.size}): {srt ax'}\n    sorry carriers ({sc'.size}): {srt sc'}"
  -- the main theorem's own module and the modules of all Zeta5 roots, count
  logInfo s!"[6-modules] Zeta5 modules ({zmods.size}): {srt zmods}"

#fscan6
