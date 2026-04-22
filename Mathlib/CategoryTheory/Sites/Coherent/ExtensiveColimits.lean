/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.CategoryTheory.Sites.Coherent.ExtensiveSheaves
public import Mathlib.CategoryTheory.Sites.Limits
/-!

# Colimits in categories of extensive sheaves

This file proves that `J`-shaped colimits of `A`-valued sheaves for the extensive topology are
computed objectwise if `colim : J ⥤ A ⥤ A` preserves finite products.

This holds for all shapes `J` if `A` is a preadditive category.

This can also easily be applied to filtered `J` in the case when `A` is a category of sets, and
eventually to sifted `J` once that API is developed.
-/

@[expose] public section

namespace CategoryTheory

open Limits Sheaf GrothendieckTopology Opposite

section

variable {A C J : Type*} [Category* A] [Category* C] [Category* J]
  [FinitaryExtensive C] [HasColimitsOfShape J A]

lemma isSheaf_pointwiseColimit [PreservesFiniteProducts (colim (J := J) (C := A))]
    (G : J ⥤ Sheaf (extensiveTopology C) A) :
    Presheaf.IsSheaf (extensiveTopology C) (pointwiseCocone (G ⋙ sheafToPresheaf _ A)).pt := by
  rw [Presheaf.isSheaf_iff_preservesFiniteProducts]
  apply +allowSynthFailures comp_preservesFiniteProducts
  exact ⟨fun n ↦ preservesLimitsOfShape_of_evaluation _ _ fun d ↦ by
    simpa using PreservesFiniteProducts.preserves (F := (G.obj d).obj) n⟩

instance [Preadditive A] : PreservesFiniteProducts (colim (J := J) (C := A)) where
  preserves _ := by
    apply +allowSynthFailures preservesProductsOfShape_of_preservesBiproductsOfShape
    apply preservesBiproductsOfShape_of_preservesCoproductsOfShape

instance [PreservesFiniteProducts (colim (J := J) (C := A))] :
    PreservesColimitsOfShape J (sheafToPresheaf (extensiveTopology C) A) where
  preservesColimit {G} := by
    suffices CreatesColimit G (sheafToPresheaf (extensiveTopology C) A) from inferInstance
    refine createsColimitOfIsSheaf _ (fun c hc ↦ ?_)
    let i : c.pt ≅ (G ⋙ sheafToPresheaf _ _).flip ⋙ colim :=
      hc.coconePointUniqueUpToIso (pointwiseIsColimit _)
    rw [Presheaf.isSheaf_of_iso_iff i]
    exact isSheaf_pointwiseColimit _

instance [Preadditive A] [HasFiniteColimits A] :
    PreservesFiniteColimits (sheafToPresheaf (extensiveTopology C) A) where
  preservesFiniteColimits _ := inferInstance

end

end CategoryTheory
