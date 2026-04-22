/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.FinallySmall
public import Mathlib.CategoryTheory.Limits.Preserves.Filtered
public import Mathlib.CategoryTheory.Filtered.Small

/-!
# Finally small filtered categories

In this file, we show that if `C` is a filtered finally small category
that is locally small, there exists a final functor `D ⥤ C` from
a small filtered category. The dual result is also obtained.

-/

@[expose] public section

universe w v u

namespace CategoryTheory

variable (C : Type u) [Category.{v} C]

namespace FinallySmall

attribute [local instance] IsFiltered.nonempty

open IsFiltered

variable [IsFiltered C] [LocallySmall.{w} C] [FinallySmall.{w} C]

lemma exists_of_isFiltered :
    ∃ (D : Type w) (_ : SmallCategory D) (_ : IsFiltered D) (F : D ⥤ C), F.Final := by
  /- We get the conclusion under the assumption `Category.{w}`
  (instead of `LocallySmall.{w}`). -/
  have hcat (C₀ : Type u) [Category.{w} C₀] [IsFiltered C₀] [FinallySmall.{w} C₀] :
      ∃ (D : Type w) (_ : SmallCategory D) (_ : IsFiltered D) (F : D ⥤ C₀), F.Final := by
    let F₀ := fromFinalModel.{w} C₀
    let D := IsFiltered.SmallFilteredIntermediate F₀
    let G := IsFiltered.SmallFilteredIntermediate.inclusion F₀
    haveI : Nonempty (FinalModel.{w} C₀) := by
      let f : StructuredArrow (Classical.arbitrary C₀) F₀ := Classical.arbitrary _
      exact ⟨f.right⟩
    haveI : G.Final :=
      Functor.final_of_exists_of_isFiltered_of_fullyFaithful G (fun X => by
        let f : StructuredArrow X F₀ := Classical.arbitrary _
        exact ⟨(IsFiltered.SmallFilteredIntermediate.factoring F₀).obj f.right,
          ⟨f.hom ≫
            (IsFiltered.SmallFilteredIntermediate.factoringCompInclusion F₀).inv.app f.right⟩⟩)
    exact ⟨D, inferInstance, inferInstance, G, inferInstance⟩
  /- To get the conclusion for the given category `C`, it suffices to apply
  the previous result to the category `ShrinkHoms C`. -/
  let e := ShrinkHoms.equivalence.{w} C
  haveI : IsFiltered (ShrinkHoms C) := of_equivalence e
  haveI : FinallySmall.{w} (ShrinkHoms C) := finallySmall_of_final_of_finallySmall e.functor
  obtain ⟨D, _, _, F, _⟩ := hcat (ShrinkHoms C)
  exact ⟨D, inferInstance, inferInstance, F ⋙ e.inverse, inferInstance⟩

/-- If `C` is a locally small filtered finally small category,
this is a small filtered category, equipped with a final functor to `C`
(see `fromFilteredFinalModel`). -/
def FilteredFinalModel : Type w := (exists_of_isFiltered.{w} C).choose

noncomputable instance : Category (FilteredFinalModel.{w} C) :=
  (exists_of_isFiltered.{w} C).choose_spec.choose

instance : IsFiltered (FilteredFinalModel.{w} C) :=
  (exists_of_isFiltered.{w} C).choose_spec.choose_spec.choose

/-- If `C` is a locally small filtered finally small category,
this is a final functor from a small filtered category. -/
noncomputable def fromFilteredFinalModel : FilteredFinalModel.{w} C ⥤ C :=
  (exists_of_isFiltered.{w} C).choose_spec.choose_spec.choose_spec.choose

instance : (fromFilteredFinalModel.{w} C).Final :=
  (exists_of_isFiltered.{w} C).choose_spec.choose_spec.choose_spec.choose_spec

open Limits in
lemma preservesColimitsOfShape_of_isFiltered
    {D E : Type*} [Category* D] [Category* E]
    (F : D ⥤ E) [PreservesFilteredColimitsOfSize.{w, w} F] :
    PreservesColimitsOfShape C F :=
  Functor.Final.preservesColimitsOfShape_of_final
    (FinallySmall.fromFilteredFinalModel.{w} C) _

end FinallySmall

namespace InitiallySmall

variable [IsCofiltered C] [LocallySmall.{w} C] [InitiallySmall.{w} C]

lemma exists_of_isCofiltered :
    ∃ (D : Type w) (_ : SmallCategory D) (_ : IsCofiltered D) (F : D ⥤ C), F.Initial := by
  obtain ⟨D, _, _, F, _⟩ := FinallySmall.exists_of_isFiltered.{w} Cᵒᵖ
  exact ⟨Dᵒᵖ, inferInstance, inferInstance, F.leftOp, inferInstance⟩

/-- If `C` is a locally small cofiltered initially small category,
this is a small cofiltered category, equipped with an initial functor to `C`
(see `fromCofilteredInitialModel`). -/
def CofilteredInitialModel : Type w := (exists_of_isCofiltered.{w} C).choose

noncomputable instance : Category (CofilteredInitialModel.{w} C) :=
  (exists_of_isCofiltered.{w} C).choose_spec.choose

instance : IsCofiltered (CofilteredInitialModel.{w} C) :=
  (exists_of_isCofiltered.{w} C).choose_spec.choose_spec.choose

/-- If `C` is a locally small cofiltered initially small category,
this is an initial functor from a small cofiltered category. -/
noncomputable def fromCofilteredInitialModel : CofilteredInitialModel.{w} C ⥤ C :=
  (exists_of_isCofiltered.{w} C).choose_spec.choose_spec.choose_spec.choose

instance : (fromCofilteredInitialModel.{w} C).Initial :=
  (exists_of_isCofiltered.{w} C).choose_spec.choose_spec.choose_spec.choose_spec

end InitiallySmall

end CategoryTheory
