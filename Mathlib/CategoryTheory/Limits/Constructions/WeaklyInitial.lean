/-
Copyright (c) 2021 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.WideEqualizers
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-!
# Constructions related to weakly initial objects

This file gives constructions related to weakly initial objects, namely:
* If a category has small products and a small weakly initial set of objects, then it has a weakly
  initial object.
* If a category has wide equalizers and a weakly initial object, then it has an initial object.

These are primarily useful to show the General Adjoint Functor Theorem.
-/

public section


universe v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C]

/--
If `C` has (small) products and a small weakly initial set of objects, then it has a weakly initial
object.
-/
theorem has_weakly_initial_of_weakly_initial_set_and_hasProducts [HasProducts.{v} C] {ι : Type v}
    {B : ι → C} (hB : ∀ A : C, ∃ i, Nonempty (B i ⟶ A)) : ∃ T : C, ∀ X, Nonempty (T ⟶ X) :=
  ⟨∏ᶜ B, fun X => ⟨Pi.π _ _ ≫ (hB X).choose_spec.some⟩⟩

/-- If `C` has (small) wide equalizers and a weakly initial object, then it has an initial object.

The initial object is constructed as the wide equalizer of all endomorphisms on the given weakly
initial object.
-/
theorem hasInitial_of_weakly_initial_and_hasWideEqualizers [HasWideEqualizers.{v} C] {T : C}
    (hT : ∀ X, Nonempty (T ⟶ X)) : HasInitial C := by
  let endos := T ⟶ T
  let i := wideEqualizer.ι (id : endos → endos)
  haveI : Nonempty endos := ⟨𝟙 _⟩
  exact (IsInitial.ofUniqueHom (fun X ↦ i ≫ Classical.choice (hT X)) fun X a ↦ by
    let E := equalizer a (i ≫ Classical.choice (hT X))
    let e : E ⟶ wideEqualizer id := equalizer.ι _ _
    let h : T ⟶ E := Classical.choice (hT E)
    haveI : IsSplitEpi e := IsSplitEpi.mk' ⟨i ≫ h, by
      apply (cancel_mono i).1
      simpa [Category.assoc] using
        wideEqualizer.condition (id : endos → endos) (h ≫ e ≫ i) (𝟙 _)⟩
    exact eq_of_epi_equalizer).hasInitial

end CategoryTheory
