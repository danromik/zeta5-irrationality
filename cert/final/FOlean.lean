/-
cert/final/FOlean.lean — dependency cone computed from the .olean FILES, without building an
`Environment`.

Methods (a) `#print axioms` and the collectAxioms comparison inside the Audit report both, in
Lean 4.34, read the axiom list that was PRE-COMPUTED and stored in each imported module's
.olean (`exportedAxiomsExt` in `Lean/Util/CollectAxioms.lean`); they never walk the bodies of
imported declarations.  This script does not use `importModules`, `Environment.find?`,
`collectAxioms` or any environment extension.  It

  * reads each module's `ModuleData` straight from its .olean with `readModuleData` (all three
    parts, .olean / .olean.server / .olean.private, for files using the module system),
    starting at the given root module and following `ModuleData.imports`;
  * builds its own table name ↦ (ConstantInfo, module);
  * walks the cone of the target with `Expr.getUsedConstants` (a different traversal from the
    C3 walker's), following types, values, constructors of inductives, recursor rules;
  * reports: the axioms reached, the `sorryAx` carriers reached, names referenced but absent
    from every olean read, and, for every constant stored in a `Zeta5.*` module: axioms,
    `sorryAx` mentions, `unsafe`/`partial` flags, and duplicated names across modules.

Run:  lake env lean --run cert/final/FOlean.lean Zeta5 Zeta5.zeta5_irrational [more targets]
Controls: pass `--control` as the first argument to also run the walk on a synthetic table
into which a planted `sorryAx` user and a planted axiom are inserted (must be found).
-/
import Lean
open Lean

structure Tbl where
  consts : Std.HashMap Name (ConstantInfo × Name) := {}
  dups : Array (Name × Name × Name) := #[]
  dupsDiffer : Array Name := #[]
  /-- the other stored versions of a name stored by two modules (followed too, generously) -/
  alts : Std.HashMap Name (Array ConstantInfo) := {}
  mods : Array Name := #[]

def succ (ci : ConstantInfo) : Array Name :=
  match ci with
  | .axiomInfo v => v.type.getUsedConstants
  | .defnInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .thmInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .opaqueInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .quotInfo v => v.type.getUsedConstants
  | .inductInfo v => v.type.getUsedConstants ++ v.ctors.toArray ++ v.all.toArray
  | .ctorInfo v => v.type.getUsedConstants.push v.induct
  | .recInfo v => v.rules.foldl (fun a r => a ++ r.rhs.getUsedConstants)
      (v.type.getUsedConstants ++ v.all.toArray)

def loadMod (m : Name) : IO (Array ConstantInfo × Array Import) := do
  let f ← findOLean m
  let (main, _) ← readModuleData f
  if !main.isModule then return (main.constants, main.imports)
  let parts ← readModuleDataParts #[f, OLeanLevel.server.adjustFileName f,
    OLeanLevel.private.adjustFileName f]
  let mut cs : Array ConstantInfo := #[]
  for (d, _) in parts do cs := cs ++ d.constants
  return (cs, main.imports)

def load (root : Name) : IO Tbl := do
  let mut t : Tbl := {}
  let mut seen : Std.HashSet Name := {}
  let mut todo : Array Name := #[root]
  seen := seen.insert root
  let mut i := 0
  while h : i < todo.size do
    let m := todo[i]
    i := i + 1
    let (cs, imps) ← loadMod m
    t := { t with mods := t.mods.push m }
    for ci in cs do
      match t.consts.get? ci.name with
      | some (old, m') =>
                        if m' != m then
                          t := { t with dups := t.dups.push (ci.name, m', m) }
                          -- a name stored by two modules must be the same declaration
                          let same := old.type == ci.type && old.value? (allowOpaque := true) == ci.value? (allowOpaque := true)
                          unless same do
                            t := { t with dupsDiffer := t.dupsDiffer.push ci.name,
                                          alts := t.alts.insert ci.name ((t.alts.getD ci.name #[]).push old) }
                        -- same module: later part (server/private) overrides the exported one
                        t := { t with consts := t.consts.insert ci.name (ci, m) }
      | none => t := { t with consts := t.consts.insert ci.name (ci, m) }
    for imp in imps do
      unless seen.contains imp.module do
        seen := seen.insert imp.module
        todo := todo.push imp.module
  return t

def walk (t : Tbl) (root : Name) : Nat × Array Name × Array Name × Array Name × Array Name := Id.run do
  let mut seen : Std.HashSet Name := ({} : Std.HashSet Name).insert root
  let mut q := #[root]
  let mut i := 0
  let mut ax := #[]; let mut sc := #[]; let mut miss := #[]; let mut up := #[]
  while h : i < q.size do
    let n := q[i]
    i := i + 1
    match t.consts.get? n with
    | none => miss := miss.push n
    | some (ci, _) =>
      let vers := (t.alts.getD n #[]).push ci
      if vers.any (· matches .axiomInfo _) then ax := ax.push n
      if vers.any (fun c => c.isUnsafe || c.isPartial) then up := up.push n
      let ss := (t.alts.getD n #[]).foldl (fun a c => a ++ succ c) (succ ci)
      if ss.contains ``sorryAx && n != ``sorryAx then sc := sc.push n
      for s in ss do
        unless seen.contains s do
          seen := seen.insert s
          q := q.push s
  return (q.size, ax, sc, miss, up)

def srt (a : Array Name) : List Name := (a.qsort (fun x y => x.toString < y.toString)).toList

def report (t : Tbl) (target : Name) : IO Unit := do
  let (n, ax, sc, miss, up) := walk t target
  let md := (t.consts.get? target).map (·.2)
  IO.println s!"=== {target}  (defined in {md})\n  constants reached: {n}\n  axioms ({ax.size}): {srt ax}\n  sorryAx carriers ({sc.size}): {srt sc}\n  referenced but in no olean read ({miss.size}): {srt miss}\n  unsafe/partial constants in the cone ({up.size}): {srt up}"

unsafe def main (args : List String) : IO Unit := do
  let (control, args) := match args with
    | "--control" :: r => (true, r) | r => (false, r)
  let rootMod :: targets := args | throw (IO.userError "usage: [--control] <RootModule> <target>...")
  initSearchPath (← findSysroot)
  let t ← load rootMod.toName
  IO.println s!"modules read: {t.mods.size}; constants in table: {t.consts.size}; names stored by two different modules: {t.dups.size}, of which with DIFFERENT type/value: {t.dupsDiffer.size} {t.dupsDiffer.toList.take 20}"
  let zd := t.dups.filter (fun (_, a, b) => (`Zeta5).isPrefixOf a || (`Zeta5).isPrefixOf b)
  IO.println s!"  ... involving a Zeta5 module ({zd.size}): {zd.toList}"
  -- every axiom anywhere in the files read
  let mut allAx := #[]
  let mut zc := 0; let mut zAx := #[]; let mut zS := #[]; let mut zU := #[]; let mut zP := #[]
  let mut entries : Array (Name × ConstantInfo × Name) := #[]
  for (n, ci, m) in t.consts.toList do
    entries := entries.push (n, ci, m)
    for c in t.alts.getD n #[] do entries := entries.push (n, c, `alt)
  IO.println s!"stored versions examined (incl. alternative versions of duplicated names): {entries.size}"
  for (n, ci, m) in entries do
    if ci matches .axiomInfo _ then allAx := allAx.push n
    if (`Zeta5).isPrefixOf m || (m == `alt && (`Zeta5).isPrefixOf n) then
      zc := zc + 1
      if ci matches .axiomInfo _ then zAx := zAx.push n
      if (succ ci).contains ``sorryAx then zS := zS.push n
      if ci.isUnsafe then zU := zU.push n
      if ci.isPartial then zP := zP.push n
  let zmods := t.mods.filter (fun m => (`Zeta5).isPrefixOf m)
  IO.println s!"axiom declarations in all files read ({allAx.size}): {srt allAx}"
  IO.println s!"Zeta5 modules read: {zmods.size}; constants stored in them: {zc}\n  axioms ({zAx.size}): {srt zAx}\n  sorryAx mentions ({zS.size}): {srt zS}\n  unsafe ({zU.size}): {srt zU}\n  partial ({zP.size}): {srt zP}"
  for tg in targets do report t tg.toName
  if control then
    -- planted: ctl.ax : False (axiom), ctl.s uses sorryAx, ctl.top uses both via the real target
    let fls := mkConst ``False
    let axCi := ConstantInfo.axiomInfo { name := `ctl.ax, levelParams := [], type := fls, isUnsafe := false }
    let sVal := mkApp2 (mkConst ``sorryAx [Level.zero]) fls (mkConst ``Bool.false)
    let sCi := ConstantInfo.thmInfo { name := `ctl.s, levelParams := [], type := fls, value := sVal, all := [`ctl.s] }
    let topVal := mkApp2 (mkConst ``And.intro) (mkConst `ctl.s) (mkConst `ctl.ax)
    let topTy := mkApp2 (mkConst ``And) fls fls
    let topV := mkApp (mkApp topVal (mkConst (targets.headD "x").toName)) (mkConst `ctl.missing)
    let topCi := ConstantInfo.thmInfo { name := `ctl.top, levelParams := [], type := topTy, value := topV, all := [`ctl.top] }
    let t' := { t with consts := ((t.consts.insert `ctl.ax (axCi, `ctl)).insert `ctl.s (sCi, `ctl)).insert `ctl.top (topCi, `ctl) }
    IO.println "--- CONTROL (must report sorryAx, ctl.ax, ctl.s, ctl.missing, and the first target's axioms):"
    report t' `ctl.top
