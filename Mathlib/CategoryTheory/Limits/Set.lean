/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.Lattice
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.CategoryTheory.Types.Set

/-!
# The functor from `Set X` to types preserves filtered colimits

Given `X : Type u`, the functor `Set.functorToTypes : Set X ⥤ Type u`
which sends `A : Set X` to its underlying type preserves filtered colimits.

-/

@[expose] public section

universe w w' u

open CategoryTheory Limits CompleteLattice

namespace Set

open CompleteLattice in
instance {J : Type w} [Category.{w'} J] {X : Type u} [IsFilteredOrEmpty J] :
    PreservesColimitsOfShape J (functorToTypes (X := X)) where
  preservesColimit {F} := by
    refine preservesColimit_of_preserves_colimit_cocone (colimitCocone F).isColimit <|
      Types.FilteredColimit.isColimitOf' (F ⋙ functorToTypes) _
        (fun ⟨x, hx⟩ ↦ ?_) fun i ⟨x, hx⟩ ⟨y, hy⟩ h ↦ ?_
    · aesop (add simp [colimitCocone_cocone_pt, iSup_eq_iUnion])
    · exact ⟨i, 𝟙 _, by simpa using h⟩

end Set
