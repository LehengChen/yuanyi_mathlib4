/-
Copyright (c) 2022 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory

/-!
# Functors from a groupoid into a right/left rigid category form a right/left rigid category.

(Using the pointwise monoidal structure on the functor category.)
-/

@[expose] public section


noncomputable section

open CategoryTheory

open CategoryTheory.MonoidalCategory

namespace CategoryTheory.Monoidal

variable {C D : Type*} [Groupoid C] [Category* D] [MonoidalCategory D]

instance functorHasRightDual [RightRigidCategory D] (F : C ⥤ D) : HasRightDual F where
  rightDual :=
    { obj := fun X => (F.obj X)ᘁ
      map := fun f => (F.map (inv f))ᘁ
      map_comp := fun f g => by simp [comp_rightAdjointMate] }
  exact :=
    { evaluation' :=
        { app := fun _ => ε_ _ _
          naturality := fun X Y f => by
            simp [Functor.map_inv, tensorHom_def, ← rightAdjointMate_comp_evaluation,
              ← comp_whiskerRight_assoc, ← comp_rightAdjointMate] }
      coevaluation' :=
        { app := fun _ => η_ _ _
          naturality := fun X Y f => by
            simp [Functor.map_inv, tensorHom_def, ← coevaluation_comp_rightAdjointMate_assoc,
              ← whiskerLeft_comp, ← comp_rightAdjointMate] } }

instance rightRigidFunctorCategory [RightRigidCategory D] : RightRigidCategory (C ⥤ D) where

instance functorHasLeftDual [LeftRigidCategory D] (F : C ⥤ D) : HasLeftDual F where
  leftDual :=
    { obj := fun X => ᘁ(F.obj X)
      map := fun f => ᘁ(F.map (inv f))
      map_comp := fun f g => by simp [comp_leftAdjointMate] }
  exact :=
    { evaluation' :=
        { app := fun _ => ε_ _ _
          naturality := fun X Y f => by
            simp [tensorHom_def, leftAdjointMate_comp_evaluation] }
      coevaluation' :=
        { app := fun _ => η_ _ _
          naturality := fun X Y f => by
            simp [tensorHom_def, coevaluation_comp_leftAdjointMate_assoc] } }

instance leftRigidFunctorCategory [LeftRigidCategory D] : LeftRigidCategory (C ⥤ D) where

instance rigidFunctorCategory [RigidCategory D] : RigidCategory (C ⥤ D) where

end CategoryTheory.Monoidal
