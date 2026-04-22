/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Presentable.CardinalFilteredPresentation
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsClosure

/-!
# Accessible categories are essentially large

If a category `C` satisfies `HasCardinalFilteredGenerator C κ` for `κ : Cardinal.{w}`
(e.g. it is locally `κ`-presentable or `κ`-accessible),
then `C` is equivalent to a `w`-large category, i.e. a category whose type
of objects is in `Type (w + 1)` and whose types of morphisms are in `Type w`.

-/

public section

universe w v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C] {κ : Cardinal.{w}} [Fact κ.IsRegular]

namespace ObjectProperty.IsCardinalFilteredGenerator

variable [LocallySmall.{w} C] {P : ObjectProperty C} [ObjectProperty.EssentiallySmall.{w} P]
    (hP : P.IsCardinalFilteredGenerator κ)

include hP in
lemma essentiallyLarge_top :
    ObjectProperty.EssentiallySmall.{w + 1} (C := C) ⊤ := by
  haveI : LocallySmall.{w + 1} C := ⟨fun X Y ↦ small_lift.{v, w + 1, w} (X ⟶ Y)⟩
  haveI : ObjectProperty.EssentiallySmall.{w + 1} P := by
    obtain ⟨Q, hQ, hPQ⟩ := ObjectProperty.EssentiallySmall.exists_small_le' P
    exact ⟨Q, small_lift.{u, w + 1, w} (Subtype Q), hPQ⟩
  let ι := Σ (J : Type w), SmallCategory J
  let shape : ι → Type w := fun i ↦ i.1
  letI (i : ι) : SmallCategory (shape i) := i.2
  refine ObjectProperty.EssentiallySmall.of_le (Q := P.colimitsClosure shape) ?_
  intro X _
  obtain ⟨J, _, _, ⟨p⟩⟩ := hP.exists_colimitsOfShape X
  exact .of_colimitPresentation (a := ⟨J, inferInstance⟩) p.toColimitPresentation
    (fun j ↦ .of_mem _ (p.prop_diag_obj j))

end ObjectProperty.IsCardinalFilteredGenerator

variable (C κ) in
lemma HasCardinalFilteredGenerator.exists_equivalence
    [HasCardinalFilteredGenerator C κ] :
    ∃ (J : Type (w + 1)) (_ : Category.{w} J), Nonempty (C ≌ J) := by
  rw [exists_equivalence_iff_of_locallySmall]
  obtain ⟨P, _, hP⟩ := HasCardinalFilteredGenerator.exists_generator C κ
  exact hP.essentiallyLarge_top

end CategoryTheory
