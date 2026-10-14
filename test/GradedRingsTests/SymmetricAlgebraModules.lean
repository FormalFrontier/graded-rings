/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Module.PUnit
public import Mathlib.Algebra.Module.ULift
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Data.ZMod.Basic

/-!
# Modules over commutative rings

These examples use canonical Mathlib instances. The scalar and module universes are
independent, with no finiteness, freeness, nontriviality or field assumptions.
-/

@[expose] public section

universe uR uM

section

variable (R : Type uR) (M : Type uM)
variable [CommRing R] [AddCommGroup M] [Module R M]

example : CommRing R := inferInstance
example : AddCommGroup M := inferInstance
example : Module R M := inferInstance
example (r : R) (m : M) : M := r • m
example : R := 0
example : M := 0

end

/-! ## The zero ring and its zero module -/

example : Type 0 := PUnit.{1}
example : Type 0 := PUnit.{1}
example : CommRing PUnit.{1} := inferInstance
example : AddCommGroup PUnit.{1} := inferInstance
example : Module PUnit.{1} PUnit.{1} := inferInstance
example : PUnit.{1} := PUnit.unit
example (r m : PUnit.{1}) : PUnit.{1} := r • m
example : (0 : PUnit.{1}) = 1 := rfl

/-! ## The zero module over the integers -/

example : Type 0 := Int
example : Type 0 := PUnit.{1}
example : CommRing Int := inferInstance
example : AddCommGroup PUnit.{1} := inferInstance
example : Module Int PUnit.{1} := inferInstance
example : Int := 1
example : PUnit.{1} := 0
example (r : Int) (m : PUnit.{1}) : PUnit.{1} := r • m

/-! ## An integer module with torsion -/

example : Type 0 := Int
example : Type 0 := ZMod 2
example : CommRing Int := inferInstance
example : AddCommGroup (ZMod 2) := inferInstance
example : Module Int (ZMod 2) := inferInstance
example : ZMod 2 := 1
example (r : Int) (m : ZMod 2) : ZMod 2 := r • m
example : (1 : ZMod 2) ≠ 0 := by decide
example : (2 : Int) • (1 : ZMod 2) = 0 := by decide

/-! ## Finitely supported integer-valued functions on the naturals -/

noncomputable section

example : Type 0 := Int
example : Type 0 := Nat →₀ Int
example : CommRing Int := inferInstance
example : AddCommGroup (Nat →₀ Int) := inferInstance
example : Module Int (Nat →₀ Int) := inferInstance
example (n : Nat) : Nat →₀ Int := Finsupp.single n 1
example (r : Int) (m : Nat →₀ Int) : Nat →₀ Int := r • m

end

/-! ## A lifted module over unlifted scalars -/

example : Type 0 := Int
example : Type 1 := ULift.{1, 0} (ZMod 2)
example : CommRing Int := inferInstance
example : AddCommGroup (ULift.{1, 0} (ZMod 2)) := inferInstance
example : Module Int (ULift.{1, 0} (ZMod 2)) := inferInstance
example (m : ZMod 2) : ULift.{1, 0} (ZMod 2) := ULift.up m
example (m : ULift.{1, 0} (ZMod 2)) : ZMod 2 := m.down
example : ULift.{1, 0} (ZMod 2) := ULift.up 1
example (r : Int) (m : ULift.{1, 0} (ZMod 2)) : ULift.{1, 0} (ZMod 2) := r • m
example (m : ZMod 2) : (ULift.up m : ULift.{1, 0} (ZMod 2)).down = m := rfl
example (r : Int) (m : ULift.{1, 0} (ZMod 2)) : (r • m).down = r • m.down := rfl

/-! ## Lifted scalars acting on an unlifted module -/

example : Type 1 := ULift.{1, 0} Int
example : Type 0 := ZMod 2
example : CommRing (ULift.{1, 0} Int) := inferInstance
example : AddCommGroup (ZMod 2) := inferInstance
example : Module (ULift.{1, 0} Int) (ZMod 2) := inferInstance
example (r : Int) : ULift.{1, 0} Int := ULift.up r
example (r : ULift.{1, 0} Int) : Int := r.down
example : ULift.{1, 0} Int := ULift.up 1
example (r : ULift.{1, 0} Int) (m : ZMod 2) : ZMod 2 := r • m
example (r : Int) : (ULift.up r : ULift.{1, 0} Int).down = r := rfl
example (r : ULift.{1, 0} Int) (m : ZMod 2) : r • m = r.down • m := rfl

/-! ## The regular module over the integers modulo four -/

example : Type 0 := ZMod 4
example : Type 0 := ZMod 4
example : CommRing (ZMod 4) := inferInstance
example : AddCommGroup (ZMod 4) := inferInstance
example : Module (ZMod 4) (ZMod 4) := inferInstance
example : ZMod 4 := 2
example (r m : ZMod 4) : ZMod 4 := r • m
example (r m : ZMod 4) : r • m = r * m := rfl
example : (2 : ZMod 4) ≠ 0 := by decide
example : (2 : ZMod 4) * 2 = 0 := by decide
