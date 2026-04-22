/-
Copyright (c) 2025 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Images
public import Mathlib.CategoryTheory.Subfunctor.Image
public import Mathlib.Tactic.CategoryTheory.CategoryStar

/-!

# The category of type-valued functors has images
-/

@[expose] public section

universe u

namespace CategoryTheory.FunctorToTypes

open Limits

variable {C : Type*} [Category* C]

attribute [local simp] FunctorToTypes.naturality in
/-- The image of a natural transformation between type-valued functors is a `MonoFactorisation` -/
@[simps]
def monoFactorisation {F G : C ⥤ Type u} (f : F ⟶ G) : MonoFactorisation f where
  I := (Subfunctor.range f).toFunctor
  m := (Subfunctor.range f).ι
  e := Subfunctor.toRange f

/-- The image of a natural transformation between type-valued functors satisfies the universal
property of images -/
noncomputable def monoFactorisationIsImage {F G : C ⥤ Type u} (f : F ⟶ G) :
    IsImage <| monoFactorisation f where
  lift H := Subfunctor.homOfLe (by
    simpa only [H.fac] using Subfunctor.range_comp_le H.e H.m) ≫ inv (Subfunctor.toRange H.m)
  lift_fac H := by
    dsimp [monoFactorisation]
    have hι : inv (Subfunctor.toRange H.m) ≫ H.m = (Subfunctor.range H.m).ι := by
      rw [← cancel_epi (Subfunctor.toRange H.m)]; simp
    rw [Category.assoc, hι, Subfunctor.homOfLe_ι]

instance : HasImages (C ⥤ Type*) where
  has_image f := { exists_image := ⟨ { F := _, isImage := monoFactorisationIsImage f } ⟩ }

instance : HasStrongEpiMonoFactorisations (C ⥤ Type*) where
  has_fac {F G} f := ⟨{ I := image f, m := image.ι f, e := factorThruImage f }⟩

end CategoryTheory.FunctorToTypes
