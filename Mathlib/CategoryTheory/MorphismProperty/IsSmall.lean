/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.Basic
public import Mathlib.Logic.Small.Set

/-!
# Small classes of morphisms

A class of morphisms `W : MorphismProperty C` is `w`-small
if the corresponding set in `Set (Arrow C)` is.

-/

@[expose] public section

universe w t v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace MorphismProperty

variable (W : MorphismProperty C)

/-- A class of morphisms `W : MorphismProperty C` is `w`-small
if the corresponding set in `Set (Arrow C)` is. -/
@[pp_with_univ]
class IsSmall : Prop where
  small_toSet : Small.{w} W.toSet

attribute [instance] IsSmall.small_toSet

instance isSmall_ofHoms {ι : Type t} {A B : ι → C} (f : ∀ i, A i ⟶ B i)
    [Small.{w} (Set.range fun i ↦ Arrow.mk (f i))] :
    IsSmall.{w} (ofHoms f) := by
  let φ (g : Set.range fun i ↦ Arrow.mk (f i)) : (ofHoms f).toSet := ⟨g.1, by
    rw [mem_toSet_iff, ofHoms_iff]
    obtain ⟨i, hi⟩ := g.2
    exact ⟨i, by simp [hi]⟩⟩
  have hφ : Function.Surjective φ := by
    rintro ⟨⟨_, _, f⟩, ⟨i⟩⟩
    exact ⟨⟨Arrow.mk (f i), ⟨i, rfl⟩⟩, rfl⟩
  exact ⟨small_of_surjective hφ⟩

set_option backward.isDefEq.respectTransparency false in
lemma isSmall_iff_eq_ofHoms :
    IsSmall.{w} W ↔ ∃ (ι : Type w) (A B : ι → C) (f : ∀ i, A i ⟶ B i),
      W = ofHoms f := by
  constructor
  · intro
    refine ⟨Shrink.{w} W.toSet, _, _, fun i ↦ ((equivShrink _).symm i).1.hom, ?_⟩
    ext A B f
    rw [ofHoms_iff]
    constructor
    · intro hf
      exact ⟨equivShrink _ ⟨f, hf⟩, by simp⟩
    · rintro ⟨i, hi⟩
      simp only [← W.arrow_mk_mem_toSet_iff, hi, Arrow.mk_eq, Subtype.coe_prop]
  · rintro ⟨_, _, _, _, rfl⟩
    infer_instance

end MorphismProperty

end CategoryTheory
