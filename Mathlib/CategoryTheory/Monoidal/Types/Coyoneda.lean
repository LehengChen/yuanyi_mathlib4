/-
Copyright (c) 2018 Michael Jendrusch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jendrusch, Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Monoidal.Types.Basic
public import Mathlib.CategoryTheory.Monoidal.Comon_

/-!
# `(𝟙_ C ⟶ -)` is a lax monoidal functor to `Type`
-/

@[expose] public section

universe v u

namespace CategoryTheory

open Opposite MonoidalCategory Category

attribute [local instance] ComonObj.instTensorUnit

attribute [local simp] types_tensorObj_def types_tensorUnit_def in
instance (C : Type u) [Category.{v} C] [MonoidalCategory C] :
    (coyoneda.obj (op (𝟙_ C))).LaxMonoidal :=
  Functor.LaxMonoidal.ofTensorHom
    (ε := fun _ => 𝟙 _)
    (μ := fun X Y p ↦ (λ_ (𝟙_ C)).inv ≫ (p.1 ⊗ₘ p.2))
    (μ_natural := by cat_disch)
    (associativity := fun X Y Z => by
      ext ⟨⟨f, g⟩, h⟩; dsimp at f g h ⊢; simp only [Iso.cancel_iso_inv_left, assoc]
      rw [← id_comp h, ← tensorHom_comp_tensorHom, assoc, associator_naturality,
        ← id_comp f, ← tensorHom_comp_tensorHom]
      simpa [ComonObj.instTensorUnit_comul] using
        (ComonObj.comul_assoc_assoc (𝟙_ C) (f ⊗ₘ g ⊗ₘ h)).symm)
    (right_unitality := fun X => by
      ext ⟨f, ⟨⟩⟩; dsimp at f
      simp [unitors_inv_equal])

end CategoryTheory
