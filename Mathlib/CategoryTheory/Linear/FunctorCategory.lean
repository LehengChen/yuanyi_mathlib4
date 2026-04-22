/-
Copyright (c) 2022 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Preadditive.FunctorCategory
public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.Algebra.Module.Pi

/-!
# Linear structure on functor categories

If `C` and `D` are categories and `D` is `R`-linear,
then `C ⥤ D` is also `R`-linear.

-/

@[expose] public section

namespace CategoryTheory

open CategoryTheory.Limits Linear

variable {R : Type*} [Semiring R]
variable {C D : Type*} [Category* C] [Category* D] [Preadditive D] [Linear R D]

instance functorCategoryLinear : Linear R (C ⥤ D) where
  homModule F G := by
    letI : SMul R (F ⟶ G) := ⟨fun r α =>
      { app := fun X => r • α.app X
        naturality := by
          cat_disch }⟩
    exact Function.Injective.module R
      { toFun := fun α X => α.app X
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
      (fun _ _ h => NatTrans.ext h)
      (fun _ _ => rfl)
  smul_comp := by
    intros
    ext
    apply smul_comp
  comp_smul := by
    intros
    ext
    apply comp_smul

namespace NatTrans

variable {F G : C ⥤ D}

/-- Application of a natural transformation at a fixed object,
as group homomorphism -/
@[simps]
def appLinearMap (X : C) : (F ⟶ G) →ₗ[R] F.obj X ⟶ G.obj X where
  toFun α := α.app X
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem app_smul (X : C) (r : R) (α : F ⟶ G) : (r • α).app X = r • α.app X :=
  rfl

end NatTrans

end CategoryTheory
