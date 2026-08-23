/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Contender
import Lean.Elab.Command

open Lean Lean.Elab Command Meta

private def contenderName (n : Nat) : Name :=
  Name.mkSimple s!"contender_{n}"

private def comparisonName (n : Nat) : Name :=
  Name.mkSimple s!"contender_{n - 1}_lt_contender_{n}"

private def contenderIndex? (name : Name) : Option Nat := do
  let suffix ← name.toString.dropPrefix? "contender_"
  suffix.toNat?

run_cmd liftTermElabM do
  let env ← getEnv
  let mut largest? : Option Nat := none
  for (name, _) in env.constants do
    if let some n := contenderIndex? name then
      largest? := some (match largest? with | none => n | some largest => max n largest)
  let some largest := largest? | throwError "no declarations named contender_N found"
  for n in List.range (largest + 1) do
    let contender := contenderName n
    let some contenderInfo := env.find? contender |
      throwError "missing {contender}; contender indices must be contiguous"
    let .defnInfo _ := contenderInfo |
      throwError "{contender} must be defined using def"
    unless contenderInfo.type == mkConst ``Nat do
      throwError "{contender} must have type Nat"
    if n > 0 then
      let comparison := comparisonName n
      let some comparisonInfo := env.find? comparison |
        throwError "missing comparison theorem {comparison}"
      let .thmInfo _ := comparisonInfo |
        throwError "{comparison} must be a theorem"
      let expectedType := mkApp2 (mkConst ``Nat.lt)
        (mkConst (contenderName (n - 1))) (mkConst contender)
      unless ← isDefEq comparisonInfo.type expectedType do
        throwError "{comparison} must prove {contenderName (n - 1)} < {contender}"
