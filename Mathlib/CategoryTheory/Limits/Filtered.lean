/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Limits.Types.Yoneda

/-!
# Filtered categories and limits

In this file, we show that `C` is filtered if and only if for every functor `F : J ⥤ C` from a
finite category there is some `X : C` such that `lim Hom(F·, X)` is nonempty.

Furthermore, we define the type classes `HasCofilteredLimitsOfSize` and `HasFilteredColimitsOfSize`.
-/

@[expose] public section


universe w' w w₂' w₂ v u

noncomputable section

open CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace CategoryTheory

section NonemptyLimit

open CategoryTheory.Limits Opposite

/-- `C` is filtered if and only if for every functor `F : J ⥤ C` from a finite category there is
    some `X : C` such that `lim Hom(F·, X)` is nonempty.

    Lemma 3.1.2 of [Kashiwara2006] -/
theorem IsFiltered.iff_nonempty_limit : IsFiltered C ↔
    ∀ {J : Type v} [SmallCategory J] [FinCategory J] (F : J ⥤ C),
      ∃ (X : C), Nonempty (limit (F.op ⋙ yoneda.obj X)) := by
  rw [IsFiltered.iff_cocone_nonempty.{v}]
  simp [(Cocone.equiv _).toEquiv.nonempty_congr,
    (limitCompYonedaIsoCocone _ _).toEquiv.nonempty_congr]

/-- `C` is cofiltered if and only if for every functor `F : J ⥤ C` from a finite category there is
    some `X : C` such that `lim Hom(X, F·)` is nonempty. -/
theorem IsCofiltered.iff_nonempty_limit : IsCofiltered C ↔
    ∀ {J : Type v} [SmallCategory J] [FinCategory J] (F : J ⥤ C),
      ∃ (X : C), Nonempty (limit (F ⋙ coyoneda.obj (op X))) := by
  rw [IsCofiltered.iff_cone_nonempty.{v}]
  simp [(Cone.equiv _).toEquiv.nonempty_congr, op_surjective.exists,
    (limitCompCoyonedaIsoCone _ _).toEquiv.nonempty_congr]

end NonemptyLimit

namespace Limits

section

variable (C)

/-- Class for having all cofiltered limits of a given size. -/
-- After https://github.com/leanprover/lean4/pull/12286 and
-- https://github.com/leanprover/lean4/pull/12423, the shape universes in
-- `HasCofilteredLimitsOfSize` and `HasFilteredColimitsOfSize` would default to universe
-- output parameters. See Note [universe output parameters and typeclass caching].
@[univ_out_params, pp_with_univ]
class HasCofilteredLimitsOfSize : Prop where
  /-- For all filtered types of size `w`, we have limits -/
  HasLimitsOfShape : ∀ (I : Type w) [Category.{w'} I] [IsCofiltered I], HasLimitsOfShape I C

/-- Class for having all filtered colimits of a given size. -/
@[univ_out_params, pp_with_univ]
class HasFilteredColimitsOfSize : Prop where
  /-- For all filtered types of a size `w`, we have colimits -/
  HasColimitsOfShape : ∀ (I : Type w) [Category.{w'} I] [IsFiltered I], HasColimitsOfShape I C

/-- Class for having cofiltered limits. -/
abbrev HasCofilteredLimits := HasCofilteredLimitsOfSize.{v, v} C

/-- Class for having filtered colimits. -/
abbrev HasFilteredColimits := HasFilteredColimitsOfSize.{v, v} C

end

instance (priority := 100) hasFilteredColimitsOfSize_of_hasColimitsOfSize
    [HasColimitsOfSize.{w', w} C] : HasFilteredColimitsOfSize.{w', w} C where
  HasColimitsOfShape _ _ _ := inferInstance

instance (priority := 100) hasCofilteredLimitsOfSize_of_hasLimitsOfSize
    [HasLimitsOfSize.{w', w} C] : HasCofilteredLimitsOfSize.{w', w} C where
  HasLimitsOfShape _ _ _ := inferInstance

instance (priority := 100) hasLimitsOfShape_of_has_cofiltered_limits
    [HasCofilteredLimitsOfSize.{w', w} C] (I : Type w) [Category.{w'} I] [IsCofiltered I] :
    HasLimitsOfShape I C :=
  HasCofilteredLimitsOfSize.HasLimitsOfShape _

instance (priority := 100) hasColimitsOfShape_of_has_filtered_colimits
    [HasFilteredColimitsOfSize.{w', w} C] (I : Type w) [Category.{w'} I] [IsFiltered I] :
    HasColimitsOfShape I C :=
  HasFilteredColimitsOfSize.HasColimitsOfShape _

lemma hasCofilteredLimitsOfSize_of_univLE [UnivLE.{w, w₂}] [UnivLE.{w', w₂'}]
    [HasCofilteredLimitsOfSize.{w₂', w₂} C] :
    HasCofilteredLimitsOfSize.{w', w} C where
  HasLimitsOfShape J :=
    haveI := IsCofiltered.of_equivalence ((ShrinkHoms.equivalence.{w₂'} J).trans <|
      Shrink.equivalence.{w₂, w₂'} (ShrinkHoms.{w} J))
    hasLimitsOfShape_of_equivalence ((ShrinkHoms.equivalence.{w₂'} J).trans <|
      Shrink.equivalence.{w₂, w₂'} (ShrinkHoms.{w} J)).symm

lemma hasCofilteredLimitsOfSize_shrink [HasCofilteredLimitsOfSize.{max w' w₂', max w w₂} C] :
    HasCofilteredLimitsOfSize.{w', w} C :=
  hasCofilteredLimitsOfSize_of_univLE.{w', w, max w' w₂', max w w₂}

lemma hasFilteredColimitsOfSize_of_univLE [UnivLE.{w, w₂}] [UnivLE.{w', w₂'}]
    [HasFilteredColimitsOfSize.{w₂', w₂} C] :
    HasFilteredColimitsOfSize.{w', w} C where
  HasColimitsOfShape J :=
    haveI := IsFiltered.of_equivalence ((ShrinkHoms.equivalence.{w₂'} J).trans <|
      Shrink.equivalence.{w₂, w₂'} (ShrinkHoms.{w} J))
    hasColimitsOfShape_of_equivalence ((ShrinkHoms.equivalence.{w₂'} J).trans <|
      Shrink.equivalence.{w₂, w₂'} (ShrinkHoms.{w} J)).symm

lemma hasFilteredColimitsOfSize_shrink [HasFilteredColimitsOfSize.{max w' w₂', max w w₂} C] :
    HasFilteredColimitsOfSize.{w', w} C :=
  hasFilteredColimitsOfSize_of_univLE.{w', w, max w' w₂', max w w₂}

end Limits

end CategoryTheory
