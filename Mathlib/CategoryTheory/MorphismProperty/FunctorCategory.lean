/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.CategoryTheory.MorphismProperty.Retract
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition

/-!
# Stability properties of morphism properties on functor categories

Given `W : MorphismProperty C` and a category `J`, we study the
stability properties of `W.functorCategory J : MorphismProperty (J ⥤ C)`.

Under suitable assumptions, we also show that if monomorphisms
in `C` are stable under transfinite compositions (or coproducts),
then the same holds in the category `J ⥤ C`.

-/

@[expose] public section

universe v v' v'' u u' u''

namespace CategoryTheory

open Limits

namespace MorphismProperty

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)

instance [W.IsStableUnderRetracts] (J : Type u'') [Category.{v''} J] :
    (W.functorCategory J).IsStableUnderRetracts where
  of_retract hfg hg j :=
    W.of_retract (hfg.map ((evaluation _ _).obj j)) (hg j)

variable {W}

instance IsStableUnderLimitsOfShape.functorCategory
    {K : Type u'} [Category.{v'} K] [W.IsStableUnderLimitsOfShape K]
    (J : Type u'') [Category.{v''} J]
    [∀ j : J, PreservesLimitsOfShape K ((evaluation J C).obj j)] :
    (W.functorCategory J).IsStableUnderLimitsOfShape K where
  condition X₁ X₂ _ _ hc₁ hc₂ f hf φ hφ j :=
    MorphismProperty.limitsOfShape_le _
      (limitsOfShape.mk' (X₁ ⋙ (evaluation _ _).obj j) (X₂ ⋙ (evaluation _ _).obj j)
      _ _ (isLimitOfPreserves _ hc₁) (isLimitOfPreserves _ hc₂) (Functor.whiskerRight f _)
      (fun k ↦ hf k j) (φ.app j) (fun k ↦ congr_app (hφ k) j))

instance IsStableUnderColimitsOfShape.functorCategory
    {K : Type u'} [Category.{v'} K] [W.IsStableUnderColimitsOfShape K]
    (J : Type u'') [Category.{v''} J]
    [∀ j : J, PreservesColimitsOfShape K ((evaluation J C).obj j)] :
    (W.functorCategory J).IsStableUnderColimitsOfShape K where
  condition X₁ X₂ _ _ hc₁ hc₂ f hf φ hφ j :=
    MorphismProperty.colimitsOfShape_le _
      (colimitsOfShape.mk' (X₁ ⋙ (evaluation _ _).obj j) (X₂ ⋙ (evaluation _ _).obj j)
      _ _ (isColimitOfPreserves _ hc₁) (isColimitOfPreserves _ hc₂) (Functor.whiskerRight f _)
      (fun k ↦ hf k j) (φ.app j) (fun k ↦ congr_app (hφ k) j))

instance [W.IsStableUnderBaseChange] (J : Type u'') [Category.{v''} J]
    [∀ j : J, PreservesLimitsOfShape WalkingCospan ((evaluation J C).obj j)] :
    (W.functorCategory J).IsStableUnderBaseChange where
  of_isPullback sq hr j :=
    W.of_isPullback (sq.map ((evaluation _ _).obj j)) (hr j)

instance [W.IsStableUnderCobaseChange] (J : Type u'') [Category.{v''} J]
    [∀ j : J, PreservesColimitsOfShape WalkingSpan ((evaluation J C).obj j)] :
    (W.functorCategory J).IsStableUnderCobaseChange where
  of_isPushout sq hr j :=
    W.of_isPushout (sq.map ((evaluation _ _).obj j)) (hr j)

instance (K : Type u') [LinearOrder K] [SuccOrder K] [OrderBot K] [WellFoundedLT K]
    [W.IsStableUnderTransfiniteCompositionOfShape K] (J : Type u'') [Category.{v''} J]
    [∀ j : J, PreservesWellOrderContinuousOfShape K ((evaluation J C).obj j)]
    [∀ j : J, PreservesColimitsOfShape K ((evaluation J C).obj j)] :
    (W.functorCategory J).IsStableUnderTransfiniteCompositionOfShape K where
  le := by
    rintro X Y f ⟨hf⟩ j
    have : W.functorCategory J ≤ W.inverseImage ((evaluation _ _).obj j) := fun _ _ _ h ↦ h _
    exact W.transfiniteCompositionsOfShape_le K _ ⟨(hf.ofLE this).map⟩

variable (J : Type u'') [Category.{v''} J]

lemma functorCategory_isomorphisms :
    (isomorphisms C).functorCategory J = isomorphisms (J ⥤ C) := by
  ext _ _ f
  simp only [functorCategory, isomorphisms.iff, NatTrans.isIso_iff_isIso_app]

lemma functorCategory_monomorphisms
    [∀ j : J, ((evaluation J C).obj j).PreservesMonomorphisms] :
    (monomorphisms C).functorCategory J = monomorphisms (J ⥤ C) := by
  ext _ _ f
  simp only [functorCategory, monomorphisms.iff]
  constructor
  · exact fun _ ↦ NatTrans.mono_of_mono_app f
  · intro _ j
    exact inferInstanceAs (Mono (((evaluation J C).obj j).map f))

lemma functorCategory_epimorphisms
    [∀ j : J, ((evaluation J C).obj j).PreservesEpimorphisms] :
    (epimorphisms C).functorCategory J = epimorphisms (J ⥤ C) := by
  ext _ _ f
  simp only [functorCategory, epimorphisms.iff]
  constructor
  · exact fun _ ↦ NatTrans.epi_of_epi_app f
  · intro _ j
    exact inferInstanceAs (Epi (((evaluation J C).obj j).map f))

instance (K : Type u') [LinearOrder K] [SuccOrder K] [OrderBot K] [WellFoundedLT K]
    [(monomorphisms C).IsStableUnderTransfiniteCompositionOfShape K]
    [∀ j : J, ((evaluation J C).obj j).PreservesMonomorphisms]
    [∀ j : J, PreservesWellOrderContinuousOfShape K ((evaluation J C).obj j)]
    [∀ j : J, PreservesColimitsOfShape K ((evaluation J C).obj j)] :
    (monomorphisms (J ⥤ C)).IsStableUnderTransfiniteCompositionOfShape K := by
  rw [← functorCategory_monomorphisms]
  infer_instance

instance (K' : Type u') [(monomorphisms C).IsStableUnderCoproductsOfShape K']
    [∀ j : J, ((evaluation J C).obj j).PreservesMonomorphisms]
    [∀ j : J, PreservesColimitsOfShape (Discrete K') ((evaluation J C).obj j)] :
    (monomorphisms (J ⥤ C)).IsStableUnderCoproductsOfShape K' := by
  rw [← functorCategory_monomorphisms]
  infer_instance

instance [IsStableUnderCoproducts.{u'} (monomorphisms C)]
    [∀ j : J, ((evaluation J C).obj j).PreservesMonomorphisms]
    [∀ (K' : Type u') (j : J), PreservesColimitsOfShape (Discrete K') ((evaluation J C).obj j)] :
    IsStableUnderCoproducts.{u'} (monomorphisms (J ⥤ C)) where

end MorphismProperty

end CategoryTheory
