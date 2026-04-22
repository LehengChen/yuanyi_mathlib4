/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Andrew Yang
-/
module

public import Mathlib.CategoryTheory.ComposableArrows.Basic
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions

/-! # Essential surjectivity of the functor induced on composable arrows

Assuming that `L : C ⥤ D` is a localization functor for a class of morphisms `W`
that has a calculus of left *or* right fractions, we show in this file
that the functor `L.mapComposableArrows n : ComposableArrows C n ⥤ ComposableArrows D n`
is essentially surjective for any `n : ℕ`.

-/

public section

namespace CategoryTheory

namespace Localization

variable {C D : Type*} [Category* C] [Category* D] (L : C ⥤ D) (W : MorphismProperty C)

open ComposableArrows

set_option backward.isDefEq.respectTransparency false in
lemma essSurj_mapComposableArrows_of_hasRightCalculusOfFractions
    (hL : W.IsInvertedBy L) [L.EssSurj]
    (hL_exists_rightFraction : ∀ ⦃X Y : C⦄ (f : L.obj X ⟶ L.obj Y),
      ∃ (φ : W.RightFraction X Y), f = φ.map L hL) (n : ℕ) :
    (L.mapComposableArrows n).EssSurj where
  mem_essImage Y := by
    induction n with
    | zero =>
      obtain ⟨Y, rfl⟩ := mk₀_surjective Y
      exact ⟨mk₀ _, ⟨isoMk₀ (L.objObjPreimageIso Y)⟩⟩
    | succ n hn =>
      obtain ⟨Y, Z, f, rfl⟩ := ComposableArrows.precomp_surjective Y
      obtain ⟨Y', ⟨e⟩⟩ := hn Y
      obtain ⟨f', hf'⟩ := hL_exists_rightFraction
        ((L.objObjPreimageIso Z).hom ≫ f ≫ (e.app 0).inv)
      haveI : IsIso (L.map f'.s) := hL f'.s f'.hs
      refine ⟨Y'.precomp f'.f,
        ⟨isoMkSucc (asIso (L.map f'.s) ≪≫ L.objObjPreimageIso Z) e ?_⟩⟩
      dsimp at hf' ⊢
      simp [← cancel_mono (e.inv.app 0), hf', MorphismProperty.RightFraction.map]

lemma essSurj_mapComposableArrows [L.IsLocalization W] [W.HasLeftCalculusOfFractions]
    (n : ℕ) :
    (L.mapComposableArrows n).EssSurj := by
  have := essSurj L W
  have := essSurj_mapComposableArrows_of_hasRightCalculusOfFractions L.op W.op
    (inverts L.op W.op) (fun ⦃X Y⦄ f => exists_rightFraction L.op W.op f) n
  have := Functor.essSurj_of_iso (L.mapComposableArrowsOpIso n).symm
  exact Functor.essSurj_of_comp_fully_faithful _ (opEquivalence D n).functor.rightOp

end Localization

end CategoryTheory
