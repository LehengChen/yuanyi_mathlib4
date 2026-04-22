/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.EssentiallySmall

/-!
# Comma categories are locally small

We introduce instances showing that the various comma categories
are locally small when the relevant categories that are
involved are locally small.

-/

@[expose] public section

universe w v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

variable {A : Type u₁} {B : Type u₂} {T : Type u₃}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} T]

instance Comma.locallySmall
    (L : A ⥤ T) (R : B ⥤ T)
    [∀ X Y : Comma L R, Small.{w} ((X.left ⟶ Y.left) × (X.right ⟶ Y.right))] :
    LocallySmall.{w} (Comma L R) where
  hom_small X Y := small_of_injective.{w}
      (f := fun g ↦ (⟨g.left, g.right⟩ : (X.left ⟶ Y.left) × (X.right ⟶ Y.right)))
        (fun _ _ _ ↦ by aesop)

instance StructuredArrow.locallySmall (S : T) (T : B ⥤ T)
    [∀ X Y : StructuredArrow S T, Small.{w} (X.right ⟶ Y.right)] :
    LocallySmall.{w} (StructuredArrow S T) where
  hom_small _ _ := small_of_injective.{w}
      (f := fun f ↦ f.right)
      (fun _ _ h ↦ StructuredArrow.hom_ext _ _ h)

instance CostructuredArrow.locallySmall (S : A ⥤ T) (X : T)
    [∀ Y Z : CostructuredArrow S X, Small.{w} (Y.left ⟶ Z.left)] :
    LocallySmall.{w} (CostructuredArrow S X) where
  hom_small _ _ := small_of_injective.{w}
      (f := fun f ↦ f.left)
      (fun _ _ h ↦ CostructuredArrow.hom_ext _ _ h)

instance Over.locallySmall (X : T)
    [∀ Y Z : Over X, Small.{w} (Y.left ⟶ Z.left)] :
    LocallySmall.{w} (Over X) where
  hom_small _ _ := small_of_injective.{w}
      (f := fun f ↦ f.left)
      (fun _ _ h ↦ Over.OverMorphism.ext h)

instance Under.locallySmall (X : T)
    [∀ Y Z : Under X, Small.{w} (Y.right ⟶ Z.right)] :
    LocallySmall.{w} (Under X) where
  hom_small _ _ := small_of_injective.{w}
      (f := fun f ↦ f.right)
      (fun _ _ h ↦ Under.UnderMorphism.ext h)

end CategoryTheory
