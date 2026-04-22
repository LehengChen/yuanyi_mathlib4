/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.EpiMono

/-!
# Balanced categories

A category is called balanced if any morphism that is both monic and epic is an isomorphism.

Balanced categories arise frequently. For example, categories in which every monomorphism
(or epimorphism) is strong are balanced. Examples of this are abelian categories and toposes, such
as the category of types.

-/

@[expose] public section


universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

section

variable (C)

/-- A category is called balanced if any morphism that is both monic and epic is an isomorphism. -/
class Balanced : Prop where
  isIso_of_mono_of_epi : ∀ {X Y : C} (f : X ⟶ Y) [Mono f] [Epi f], IsIso f

end

theorem isIso_of_mono_of_epi [Balanced Cᵒᵖ] {X Y : C} (f : X ⟶ Y) [Mono f] [Epi f] :
    IsIso f := by
  rw [← isIso_op_iff]
  exact Balanced.isIso_of_mono_of_epi f.op

theorem isIso_iff_mono_and_epi [Balanced Cᵒᵖ] {X Y : C} (f : X ⟶ Y) :
    IsIso f ↔ Mono f ∧ Epi f :=
  ⟨fun _ => ⟨inferInstance, inferInstance⟩, fun ⟨_, _⟩ => isIso_of_mono_of_epi _⟩

section

instance balanced_opposite [Balanced C] : Balanced Cᵒᵖ :=
  { isIso_of_mono_of_epi := fun f _ _ => by
      haveI : IsIso f.unop := Balanced.isIso_of_mono_of_epi f.unop
      rw [← Quiver.Hom.op_unop f]
      infer_instance }

end

end CategoryTheory
