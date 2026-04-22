/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
/-!

# AB axioms in functor categories

This file proves that, when the relevant limits and colimits exist, exactness of limits and
colimits carries over from `A` to the functor category `C ⥤ A`.
-/

@[expose] public section

namespace CategoryTheory

open CategoryTheory Limits Opposite

variable {A C J : Type*} [Category* A] [Category* C] [Category* J]

instance [HasColimitsOfShape J A] [HasExactColimitsOfShape J A]
    [HasFiniteLimits (C ⥤ A)] [∀ c : C, PreservesFiniteLimits ((evaluation C A).obj c)] :
    HasExactColimitsOfShape J (C ⥤ A) where
  preservesFiniteLimits := by
    apply preservesFiniteLimits_of_evaluation
    intro c
    let W := (Functor.whiskeringRight J (C ⥤ A) A).obj ((evaluation C A).obj c)
    have hW : PreservesFiniteLimits W := by
      constructor
      intro I _ _
      dsimp [W]
      infer_instance
    letI := hW
    letI : PreservesFiniteLimits (W ⋙ (colim : (J ⥤ A) ⥤ A)) :=
      comp_preservesFiniteLimits W (colim : (J ⥤ A) ⥤ A)
    let e : (colim : (J ⥤ C ⥤ A) ⥤ C ⥤ A) ⋙ (evaluation C A).obj c ≅
        W ⋙ (colim : (J ⥤ A) ⥤ A) := by
      dsimp [W]
      refine NatIso.ofComponents (fun F => colimitObjIsoColimitCompEvaluation F c) ?_
      intro F G η
      apply colimit_obj_ext
      intro j
      simp only [Functor.comp_obj, Functor.whiskeringRight_obj_obj, colim_obj,
        evaluation_obj_obj, Functor.comp_map, colim_map, evaluation_obj_map,
        Functor.whiskeringRight_obj_map, colimitObjIsoColimitCompEvaluation_ι_app_hom_assoc]
      have h := congr_app (ι_colimMap η j) c
      dsimp at h
      rw [← Category.assoc, h, Category.assoc, colimitObjIsoColimitCompEvaluation_ι_app_hom]
      simpa using (ι_colimMap (Functor.whiskerRight η ((evaluation C A).obj c)) j).symm
    exact preservesFiniteLimits_of_natIso e.symm

instance [HasLimitsOfShape J A] [HasExactLimitsOfShape J A]
    [HasFiniteColimits (C ⥤ A)]
    [∀ c : C, PreservesFiniteColimits ((evaluation C A).obj c)] :
    HasExactLimitsOfShape J (C ⥤ A) where
  preservesFiniteColimits := by
    apply preservesFiniteColimits_of_evaluation
    intro c
    let W := (Functor.whiskeringRight J (C ⥤ A) A).obj ((evaluation C A).obj c)
    have hW : PreservesFiniteColimits W := by
      constructor
      intro I _ _
      dsimp [W]
      infer_instance
    letI := hW
    letI : PreservesFiniteColimits (W ⋙ (lim : (J ⥤ A) ⥤ A)) :=
      comp_preservesFiniteColimits W (lim : (J ⥤ A) ⥤ A)
    let e : (lim : (J ⥤ C ⥤ A) ⥤ C ⥤ A) ⋙ (evaluation C A).obj c ≅
        W ⋙ (lim : (J ⥤ A) ⥤ A) := by
      dsimp [W]
      refine NatIso.ofComponents (fun F => limitObjIsoLimitCompEvaluation F c) ?_
      intro F G η
      dsimp
      apply limit.hom_ext
      intro j
      rw [Category.assoc, limitObjIsoLimitCompEvaluation_hom_π]
      rw [Category.assoc, limMap_π]
      rw [← Category.assoc, limitObjIsoLimitCompEvaluation_hom_π]
      exact congr_app (limMap_π η j) c
    exact preservesFiniteColimits_of_natIso e.symm

end CategoryTheory
