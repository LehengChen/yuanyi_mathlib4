/-
Copyright (c) 2022 Julian Kuelshammer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Kuelshammer
-/
module

public import Mathlib.CategoryTheory.Preadditive.Basic
public import Mathlib.CategoryTheory.Endofunctor.Algebra
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Preadditive structure on algebras over a monad

If `C` is a preadditive category and `F` is an additive endofunctor on `C` then `Algebra F` is
also preadditive. Dually, the category `Coalgebra F` is also preadditive.
-/

@[expose] public section


universe v₁ u₁

-- morphism levels before object levels. See note [category_theory universes].
namespace CategoryTheory

variable (C : Type u₁) [Category.{v₁} C] [Preadditive C] (F : C ⥤ C) [Functor.Additive (F : C ⥤ C)]

open CategoryTheory.Limits Preadditive

/-- The category of algebras over an additive endofunctor on a preadditive category is preadditive.
-/
@[simps!]
instance Endofunctor.algebraPreadditive : Preadditive (Endofunctor.Algebra F) where
  homGroup A₁ A₂ := by
    letI : Add (A₁ ⟶ A₂) :=
      { add := fun α β =>
          { f := α.f + β.f
            h := by simp only [Functor.map_add, add_comp, Endofunctor.Algebra.Hom.h, comp_add] } }
    letI : Zero (A₁ ⟶ A₂) :=
      { zero :=
          { f := 0
            h := by simp only [Functor.map_zero, zero_comp, comp_zero] } }
    letI : SMul ℕ (A₁ ⟶ A₂) :=
      { smul := fun n α =>
          { f := n • α.f
            h := by rw [comp_nsmul, Functor.map_nsmul, nsmul_comp, Endofunctor.Algebra.Hom.h] } }
    letI : Neg (A₁ ⟶ A₂) :=
      { neg := fun α =>
          { f := -α.f
            h := by simp only [Functor.map_neg, neg_comp, Endofunctor.Algebra.Hom.h, comp_neg] } }
    letI : Sub (A₁ ⟶ A₂) :=
      { sub := fun α β =>
          { f := α.f - β.f
            h := by simp only [Functor.map_sub, sub_comp, Endofunctor.Algebra.Hom.h, comp_sub] } }
    letI : SMul ℤ (A₁ ⟶ A₂) :=
      { smul := fun r α =>
          { f := r • α.f
            h := by rw [comp_zsmul, Functor.map_zsmul, zsmul_comp, Endofunctor.Algebra.Hom.h] } }
    exact Function.Injective.addCommGroup Endofunctor.Algebra.Hom.f
      (fun _ _ h => Endofunctor.Algebra.Hom.ext h)
      rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ => rfl)
  add_comp := by
    intros
    apply Algebra.Hom.ext
    apply add_comp
  comp_add := by
    intros
    apply Algebra.Hom.ext
    apply comp_add

instance Algebra.forget_additive : (Endofunctor.Algebra.forget F).Additive where

@[simps!]
instance Endofunctor.coalgebraPreadditive : Preadditive (Endofunctor.Coalgebra F) where
  homGroup A₁ A₂ := by
    letI : Add (A₁ ⟶ A₂) :=
      { add := fun α β =>
          { f := α.f + β.f
            h := by simp only [Functor.map_add, comp_add, Endofunctor.Coalgebra.Hom.h, add_comp] } }
    letI : Zero (A₁ ⟶ A₂) :=
      { zero :=
          { f := 0
            h := by simp only [Functor.map_zero, zero_comp, comp_zero] } }
    letI : SMul ℕ (A₁ ⟶ A₂) :=
      { smul := fun n α =>
          { f := n • α.f
            h := by rw [Functor.map_nsmul, comp_nsmul, Endofunctor.Coalgebra.Hom.h, nsmul_comp] } }
    letI : Neg (A₁ ⟶ A₂) :=
      { neg := fun α =>
          { f := -α.f
            h := by simp only [Functor.map_neg, comp_neg, Endofunctor.Coalgebra.Hom.h, neg_comp] } }
    letI : Sub (A₁ ⟶ A₂) :=
      { sub := fun α β =>
          { f := α.f - β.f
            h := by simp only [Functor.map_sub, comp_sub, Endofunctor.Coalgebra.Hom.h, sub_comp] } }
    letI : SMul ℤ (A₁ ⟶ A₂) :=
      { smul := fun r α =>
          { f := r • α.f
            h := by rw [Functor.map_zsmul, comp_zsmul, Endofunctor.Coalgebra.Hom.h, zsmul_comp] } }
    exact Function.Injective.addCommGroup Endofunctor.Coalgebra.Hom.f
      (fun _ _ h => Endofunctor.Coalgebra.Hom.ext h)
      rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ => rfl)
  add_comp := by
    intros
    apply Coalgebra.Hom.ext
    apply add_comp
  comp_add := by
    intros
    apply Coalgebra.Hom.ext
    apply comp_add

instance Coalgebra.forget_additive : (Endofunctor.Coalgebra.forget F).Additive where

end CategoryTheory
