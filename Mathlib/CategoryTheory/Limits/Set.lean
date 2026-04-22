/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Limits.Lattice
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.CategoryTheory.Types.Set

/-!
# The functor from `Set X` to types preserves sifted-or-empty colimits

Given `X : Type u`, the functor `Set.functorToTypes : Set X ⥤ Type u`
which sends `A : Set X` to its underlying type preserves sifted-or-empty colimits.

-/

@[expose] public section

universe w w' u

open CategoryTheory Limits CompleteLattice

namespace Set

open CompleteLattice in
instance {J : Type w} [Category.{w'} J] {X : Type u} [IsSiftedOrEmpty J] :
    PreservesColimitsOfShape J (functorToTypes (X := X)) where
  preservesColimit {F} := by
    apply preservesColimit_of_preserves_colimit_cocone (colimitCocone F).isColimit
    apply Types.FilteredColimit.isColimitOf
    · rintro ⟨x, hx⟩
      simp only [colimitCocone_cocone_pt, iSup_eq_iUnion, mem_iUnion] at hx
      obtain ⟨i, hi⟩ := hx
      exact ⟨i, ⟨x, hi⟩, rfl⟩
    · intro i j ⟨x, hx⟩ ⟨y, hy⟩ h
      obtain rfl : x = y := by simpa using h
      exact ⟨Functor.Final.lift (Functor.diag J) (i, j),
        (Functor.Final.homToLift (Functor.diag J) (i, j)).1,
        (Functor.Final.homToLift (Functor.diag J) (i, j)).2, rfl⟩

end Set
