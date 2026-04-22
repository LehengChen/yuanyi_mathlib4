/-
Copyright (c) 2025 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Mod_

/-!
# Additional results about module objects in Cartesian monoidal categories
-/

@[expose] public section

open CategoryTheory MonoidalCategory SemiCartesianMonoidalCategory

namespace CategoryTheory
universe v u
variable {C : Type u} [Category.{v} C] [SemiCartesianMonoidalCategory C]

/-- Every object is a module over a monoid object via the trivial action. -/
@[reducible] def ModObj.trivialAction (M : C) [MonObj M] (X : C) :
    ModObj M X where
  smul := snd M X
  one_smul' := by
    change MonObj.one (X := M) ▷ X ≫ snd M X = (λ_ X).hom
    rw [snd_def]
    rw [← comp_whiskerRight_assoc]
    change (MonObj.one (X := M) ≫ toUnit M) ▷ X ≫ (λ_ X).hom = (λ_ X).hom
    rw [toUnit_unique (MonObj.one (X := M) ≫ toUnit M) (𝟙 _)]
    simp
  mul_smul' := by
    change MonObj.mul (X := M) ▷ X ≫ snd M X =
      (α_ M M X).hom ≫ M ◁ snd M X ≫ snd M X
    rw [snd_def (X := M) (Y := X)]
    change MonObj.mul (X := M) ▷ X ≫ toUnit M ▷ X ≫ (λ_ X).hom =
      (α_ M M X).hom ≫ M ◁ (toUnit M ▷ X ≫ (λ_ X).hom) ≫
        toUnit M ▷ X ≫ (λ_ X).hom
    rw [← comp_whiskerRight_assoc]
    rw [comp_toUnit]
    rw [show toUnit (M ⊗ M) = M ◁ toUnit M ≫ (ρ_ M).hom ≫ toUnit M from
      toUnit_unique _ _]
    rw [whiskerLeft_comp_assoc]
    rw [← associator_naturality_middle_assoc]
    rw [triangle_assoc]
    rw [comp_whiskerRight_assoc]
    rw [comp_whiskerRight_assoc]

attribute [local instance] ModObj.trivialAction in
/-- Every object is a module over a monoid object via the trivial action. -/
@[simps]
def Mod_.trivialAction (M : Mon C) (X : C) : Mod_ C M.X where
  X := X

end CategoryTheory
