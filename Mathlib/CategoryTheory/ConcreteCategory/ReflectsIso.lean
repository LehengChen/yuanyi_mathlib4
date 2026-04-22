/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.ConcreteCategory.Forget
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Basic

/-!
A `forget₂ C D` forgetful functor between concrete categories `C` and `D`
reflects isomorphisms when the forgetful functor from `C` to types does.
-/

@[expose] public section


universe w u

namespace CategoryTheory

instance : (forget (Type u)).ReflectsIsomorphisms where reflects _ _ _ {i} := i

variable (C : Type*) [Category* C]
    {FC : outParam <| C → C → Type*} {CC : outParam <| C → Type w}
    [outParam <| ∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory.{w} C FC]
variable (D : Type*) [Category* D]
    {FD : outParam <| D → D → Type*} {CD : outParam <| D → Type w}
    [outParam <| ∀ X Y, FunLike (FD X Y) (CD X) (CD Y)] [ConcreteCategory.{w} D FD]

-- This should not be an instance, as it causes a typeclass loop
-- with `CategoryTheory.hasForgetToType`.
/-- A `forget₂ C D` forgetful functor between concrete categories `C` and `D`
where `forget C` reflects isomorphisms, itself reflects isomorphisms.
-/
theorem reflectsIsomorphisms_forget₂ [HasForget₂ C D] [(forget C).ReflectsIsomorphisms] :
    (forget₂ C D).ReflectsIsomorphisms :=
  { reflects := fun X Y f {i} => by
      haveI i' : IsIso ((forget D).map ((forget₂ C D).map f)) := Functor.map_isIso (forget D) _
      haveI : IsIso ((forget C).map f) := by
        rwa [← @HasForget₂.forget_comp C _ _ _ _ _ D _ _ _ _ _]
      apply isIso_of_reflects_iso f (forget C) }

end CategoryTheory
