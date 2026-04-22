/-
Copyright (c) 2023 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.FintypeCat
public import Mathlib.CategoryTheory.Limits.Creates
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.CategoryTheory.Limits.Types.Products
public import Mathlib.Data.Finite.Prod
public import Mathlib.Data.Finite.Sigma

/-!
# (Co)limits in the category of finite types

We show that finite (co)limits exist in `FintypeCat` and that they are preserved by the natural
inclusion `FintypeCat.incl`.
-/

@[expose] public section

open CategoryTheory Limits Functor

universe u

namespace CategoryTheory.Limits.FintypeCat

instance {J : Type} [SmallCategory J] (K : J ⥤ FintypeCat.{u}) (j : J) :
    Finite ((K ⋙ FintypeCat.incl.{u}).obj j) := by
  simp only [comp_obj, FintypeCat.incl_obj]
  infer_instance

/-- Any functor from a category with finitely many objects to `Type*` that only involves
finite objects has a finite limit. -/
noncomputable instance finiteLimitOfFiniteDiagram {J : Type} [SmallCategory J] [Finite J]
    (K : J ⥤ Type*) [∀ j, Finite (K.obj j)] : Fintype (limit K) := by
  have : Fintype (sections K) := Fintype.ofFinite (sections K)
  exact Fintype.ofEquiv (sections K) (Types.limitEquivSections K).symm

noncomputable instance inclusionCreatesFiniteLimits {J : Type} [SmallCategory J] [Finite J] :
    CreatesLimitsOfShape J FintypeCat.incl.{u} where
  CreatesLimit {K} := createsLimitOfFullyFaithfulOfIso
    (FintypeCat.of <| limit <| K ⋙ FintypeCat.incl) (Iso.refl _)

/- Help typeclass inference to infer creation of finite limits for the forgetful functor. -/
noncomputable instance {J : Type} [SmallCategory J] [Finite J] :
    CreatesLimitsOfShape J (forget FintypeCat) :=
  FintypeCat.inclusionCreatesFiniteLimits

instance {J : Type} [SmallCategory J] [Finite J] : HasLimitsOfShape J FintypeCat.{u} where
  has_limit F := hasLimit_of_created F FintypeCat.incl

instance hasFiniteLimits : HasFiniteLimits FintypeCat.{u} where
  out _ := inferInstance

noncomputable instance inclusion_preservesFiniteLimits :
    PreservesFiniteLimits FintypeCat.incl.{u} where
  preservesFiniteLimits _ :=
    preservesLimitOfShape_of_createsLimitsOfShape_and_hasLimitsOfShape FintypeCat.incl

/- Help typeclass inference to infer preservation of finite limits for the forgetful functor. -/
noncomputable instance : PreservesFiniteLimits (forget FintypeCat) :=
  FintypeCat.inclusion_preservesFiniteLimits

/-- The categorical product of a finite family in `FintypeCat` is equivalent to the product
as types. -/
noncomputable def productEquiv {ι : Type*} [Finite ι] (X : ι → FintypeCat.{u}) :
    (∏ᶜ X : FintypeCat) ≃ ∀ i, X i :=
  letI : Fintype ι := Fintype.ofFinite _
  haveI : Small.{u} ι :=
    ⟨ULift (Fin (Fintype.card ι)), ⟨(Fintype.equivFin ι).trans Equiv.ulift.symm⟩⟩
  let is₁ : FintypeCat.incl.obj (∏ᶜ fun i ↦ X i) ≅ (∏ᶜ fun i ↦ X i : Type u) :=
    PreservesProduct.iso FintypeCat.incl (fun i ↦ X i)
  let is₂ : (∏ᶜ fun i ↦ X i : Type u) ≅ Shrink.{u} (∀ i, X i) :=
    Types.Small.productIso (fun i ↦ X i)
  let e : (∀ i, X i) ≃ Shrink.{u} (∀ i, X i) := equivShrink _
  (equivEquivIso.symm is₁).trans ((equivEquivIso.symm is₂).trans e.symm)

@[simp]
lemma productEquiv_apply {ι : Type*} [Finite ι] (X : ι → FintypeCat.{u})
    (x : (∏ᶜ X : FintypeCat)) (i : ι) : productEquiv X x i = Pi.π X i x := by
  simpa [productEquiv] using (elementwise_of% piComparison_comp_π FintypeCat.incl X i) x

@[simp]
lemma productEquiv_symm_comp_π_apply {ι : Type*} [Finite ι] (X : ι → FintypeCat.{u})
    (x : ∀ i, X i) (i : ι) : Pi.π X i ((productEquiv X).symm x) = x i := by
  rw [← productEquiv_apply, Equiv.apply_symm_apply]

instance nonempty_pi_of_nonempty {ι : Type*} [Finite ι] (X : ι → FintypeCat.{u})
    [∀ i, Nonempty (X i)] : Nonempty (∏ᶜ X : FintypeCat.{u}) :=
  (Equiv.nonempty_congr <| productEquiv X).mpr inferInstance

/-- The colimit type of a functor from a category with finitely many objects to Types that only
involves finite objects is finite. -/
instance finite_colimitType {J : Type} [SmallCategory J] [Finite J]
    (K : J ⥤ Type*) [∀ j, Finite (K.obj j)] : Finite K.ColimitType :=
  Quot.finite _

/-- Any colimit of a functor from a category with finitely many objects to `Type*` that only
involves finite objects is finite. -/
lemma finite_of_isColimit {J : Type} [SmallCategory J] [Finite J]
    {K : J ⥤ Type*} [∀ j, Finite (K.obj j)] {c : Cocone K} (hc : IsColimit c) :
    Finite c.pt :=
  Finite.of_equiv _ ((Types.isColimit_iff_coconeTypesIsColimit c).1 ⟨hc⟩).equiv

/-- Any functor from a category with finitely many objects to `Type*` that only involves
finite objects has a finite colimit. -/
noncomputable instance finiteColimitOfFiniteDiagram {J : Type} [SmallCategory J] [Finite J]
    (K : J ⥤ Type*) [∀ j, Finite (K.obj j)] : Fintype (colimit K) := by
  have : Finite (colimit K) := finite_of_isColimit (colimit.isColimit K)
  apply Fintype.ofFinite

noncomputable instance inclusionCreatesFiniteColimits {J : Type} [SmallCategory J] [Finite J] :
    CreatesColimitsOfShape J FintypeCat.incl.{u} where
  CreatesColimit {K} := createsColimitOfFullyFaithfulOfIso
    (FintypeCat.of <| colimit <| K ⋙ FintypeCat.incl) (Iso.refl _)

/- Help typeclass inference to infer creation of finite colimits for the forgetful functor. -/
noncomputable instance {J : Type} [SmallCategory J] [Finite J] :
    CreatesColimitsOfShape J (forget FintypeCat) :=
  FintypeCat.inclusionCreatesFiniteColimits

instance {J : Type} [SmallCategory J] [Finite J] : HasColimitsOfShape J FintypeCat.{u} where
  has_colimit F := hasColimit_of_created F FintypeCat.incl

instance hasFiniteColimits : HasFiniteColimits FintypeCat.{u} where
  out _ := inferInstance

noncomputable instance inclusion_preservesFiniteColimits :
    PreservesFiniteColimits FintypeCat.incl.{u} where
  preservesFiniteColimits _ :=
    preservesColimitOfShape_of_createsColimitsOfShape_and_hasColimitsOfShape FintypeCat.incl

/- Help typeclass inference to infer preservation of finite colimits for the forgetful functor. -/
noncomputable instance : PreservesFiniteColimits (forget FintypeCat) :=
  FintypeCat.inclusion_preservesFiniteColimits

lemma jointly_surjective {J : Type*} [SmallCategory J]
    (F : J ⥤ FintypeCat.{u}) (t : Cocone F) (h : IsColimit t) (x : t.pt) :
    ∃ j y, t.ι.app j y = x := by
  classical
  by_contra hx
  simp_rw [not_exists] at hx
  let B : FintypeCat.{u} := FintypeCat.of (ULift.{u} Bool)
  let f₁ : t.pt ⟶ B := FintypeCat.homMk fun _ ↦ ULift.up true
  let f₂ : t.pt ⟶ B := FintypeCat.homMk fun y ↦ ULift.up (if y = x then false else true)
  have hf : f₁ = f₂ := by
    refine h.hom_ext fun j ↦ ?_
    ext y
    have hne : (t.ι.app j) y ≠ x := hx j y
    simpa [f₁, f₂] using hne
  have hfx : f₁ x = f₂ x := ConcreteCategory.congr_hom hf x
  have hdown := congr_arg ULift.down hfx
  simp [f₁, f₂] at hdown

end CategoryTheory.Limits.FintypeCat
