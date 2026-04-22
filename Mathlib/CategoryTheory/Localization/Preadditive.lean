/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Localization.Predicate
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Localization of natural transformations to preadditive categories

-/

public section

namespace CategoryTheory

open Limits

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]

namespace Localization

variable (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W]

lemma liftNatTrans_zero (F₁ F₂ : C ⥤ E) (F₁' F₂' : D ⥤ E)
    [Lifting L W F₁ F₁'] [Lifting L W F₂ F₂']
    [HasZeroMorphisms (C ⥤ E)] [HasZeroMorphisms (D ⥤ E)]
    [Functor.PreservesZeroMorphisms (whiskeringLeftFunctor' L W E)] :
    liftNatTrans L W F₁ F₂ F₁' F₂' 0 = 0 := by
  apply (whiskeringLeftFunctor' L W E).map_injective
  simp [liftNatTrans]
  rfl

lemma liftNatTrans_add (F₁ F₂ : C ⥤ E) (F₁' F₂' : D ⥤ E)
    [Lifting L W F₁ F₁'] [Lifting L W F₂ F₂']
    [Preadditive (C ⥤ E)] [Preadditive (D ⥤ E)]
    [Functor.Additive ((Functor.whiskeringLeft C D E).obj L)]
    (τ τ' : F₁ ⟶ F₂) :
    liftNatTrans L W F₁ F₂ F₁' F₂' (τ + τ') =
      liftNatTrans L W F₁ F₂ F₁' F₂' τ + liftNatTrans L W F₁ F₂ F₁' F₂' τ' := by
  haveI : Functor.Additive (whiskeringLeftFunctor' L W E) := by
    dsimp [whiskeringLeftFunctor']
    infer_instance
  apply (whiskeringLeftFunctor' L W E).map_injective
  rw [Functor.map_add]
  simp only [liftNatTrans, Functor.map_preimage]
  rw [Preadditive.comp_add_assoc, Preadditive.add_comp]
  simp only [Category.assoc]

end Localization

end CategoryTheory
