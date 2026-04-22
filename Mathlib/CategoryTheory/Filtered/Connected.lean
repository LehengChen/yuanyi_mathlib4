/-
Copyright (c) 2024 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.IsConnected

/-!
# Filtered categories are connected
-/

public section

universe v u

namespace CategoryTheory

variable (C : Type u) [Category.{v} C]

theorem IsFilteredOrEmpty.isPreconnected
    (cocone_objs : ∀ X Y : C, ∃ (Z : C) (_ : X ⟶ Z) (_ : Y ⟶ Z), True) :
    IsPreconnected C :=
  zigzag_isPreconnected fun j j' => by
    obtain ⟨Z, f, g, _⟩ := cocone_objs j j'
    exact .trans (.single <| .inl <| .intro f) (.single <| .inr <| .intro g)

theorem IsCofilteredOrEmpty.isPreconnected
    (cone_objs : ∀ X Y : C, ∃ (W : C) (_ : W ⟶ X) (_ : W ⟶ Y), True) :
    IsPreconnected C :=
  zigzag_isPreconnected fun j j' => by
    obtain ⟨W, f, g, _⟩ := cone_objs j j'
    exact .trans (.single <| .inr <| .intro f) (.single <| .inl <| .intro g)

attribute [local instance] IsFiltered.nonempty in
theorem IsFiltered.isConnected [IsFiltered C] : IsConnected C :=
  { IsFilteredOrEmpty.isPreconnected C IsFilteredOrEmpty.cocone_objs with }

attribute [local instance] IsCofiltered.nonempty in
theorem IsCofiltered.isConnected [IsCofiltered C] : IsConnected C :=
  { IsCofilteredOrEmpty.isPreconnected C IsCofilteredOrEmpty.cone_objs with }

end CategoryTheory
