/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-! # Limits in categories of presheaves of modules

In this file, it is shown that under suitable assumptions,
limits exist in the category `PresheafOfModules R`.

-/

@[expose] public section

universe v v₁ v₂ u₁ u₂ u u'

open CategoryTheory Category Limits

namespace PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{u}}
  {J : Type u₂} [Category.{v₂} J]
  (F : J ⥤ PresheafOfModules.{v} R)

section Limits

variable [∀ X, Small.{v} ((F ⋙ evaluation R X) ⋙ forget _).sections]

set_option backward.isDefEq.respectTransparency false in
/-- A cone in the category `PresheafOfModules R` is limit if it is so after the application
of the functors `evaluation R X` for all `X`. -/
def evaluationJointlyReflectsLimits (c : Cone F)
    (hc : ∀ (X : Cᵒᵖ), IsLimit ((evaluation R X).mapCone c)) : IsLimit c where
  lift s :=
    { app := fun X => (hc X).lift ((evaluation R X).mapCone s)
      naturality := fun {X Y} f ↦ by
        apply (isLimitOfPreserves (ModuleCat.restrictScalars (R.map f).hom) (hc Y)).hom_ext
        intro j
        have h₁ := (c.π.app j).naturality f
        have h₂ := (hc X).fac ((evaluation R X).mapCone s) j
        rw [Functor.mapCone_π_app, assoc, assoc, ← Functor.map_comp, IsLimit.fac]
        dsimp at h₁ h₂ ⊢
        rw [h₁, reassoc_of% h₂, Hom.naturality] }
  fac s j := by
    ext1 X
    exact (hc X).fac ((evaluation R X).mapCone s) j
  uniq s m hm := by
    ext1 X
    apply (hc X).uniq ((evaluation R X).mapCone s)
    intro j
    dsimp
    rw [← hm, comp_app]

instance {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    HasLimit (F ⋙ evaluation R Y ⋙ ModuleCat.restrictScalars (R.map f).hom) := by
  change HasLimit ((F ⋙ evaluation R Y) ⋙ ModuleCat.restrictScalars (R.map f).hom)
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- Given `F : J ⥤ PresheafOfModules.{v} R`, this is the presheaf of modules obtained by
taking a limit in the category of modules over `R.obj X` for all `X`. -/
@[simps]
noncomputable def limitPresheafOfModules : PresheafOfModules R where
  obj X := limit (F ⋙ evaluation R X)
  map {_ Y} f := limMap (Functor.whiskerLeft F (restriction R f)) ≫
    (preservesLimitIso (ModuleCat.restrictScalars (R.map f).hom) (F ⋙ evaluation R Y)).inv
  map_id X := by
    dsimp
    rw [← cancel_mono (preservesLimitIso _ _).hom, assoc, Iso.inv_hom_id, comp_id]
    apply limit.hom_ext
    intro j
    simp only [limMap_π, Functor.comp_obj, evaluation_obj, Functor.whiskerLeft_app,
      restriction_app, assoc]
    let e := ModuleCat.restrictScalarsId'App (R.map (𝟙 X)).hom (by simp) (limit (F ⋙ evaluation R X))
    have h :
        e.inv ≫ (preservesLimitIso (ModuleCat.restrictScalars (R.map (𝟙 X)).hom)
            (F ⋙ evaluation R X)).hom ≫
          limit.π ((F ⋙ evaluation R X) ⋙ ModuleCat.restrictScalars (R.map (𝟙 X)).hom) j =
        e.inv ≫ (ModuleCat.restrictScalars (R.map (𝟙 X)).hom).map (limit.π (F ⋙ evaluation R X) j) := by
      simp [e, preservesLimitIso_hom_π]
    calc
      limit.π (F ⋙ evaluation R X) j ≫ (F.obj j).map (𝟙 X) =
          e.inv ≫ (ModuleCat.restrictScalars (R.map (𝟙 X)).hom).map (limit.π (F ⋙ evaluation R X) j) := by
        rw [← ModuleCat.restrictScalarsId'App_inv_naturality, map_id,
          ModuleCat.restrictScalarsId'_inv_app]
        dsimp [e]
      _ = e.inv ≫ (preservesLimitIso (ModuleCat.restrictScalars (R.map (𝟙 X)).hom)
            (F ⋙ evaluation R X)).hom ≫
          limit.π ((F ⋙ evaluation R X) ⋙ ModuleCat.restrictScalars (R.map (𝟙 X)).hom) j := by
        exact h.symm
  map_comp {X Y Z} f g := by
    dsimp
    rw [← cancel_mono (preservesLimitIso _ _).hom, assoc, assoc, assoc, assoc, Iso.inv_hom_id,
      comp_id]
    apply limit.hom_ext
    intro j
    simp only [Functor.comp_obj, evaluation_obj, limMap_π, Functor.whiskerLeft_app, restriction_app,
      map_comp, ModuleCat.restrictScalarsComp'_inv_app, Functor.map_comp, assoc]
    let lf := limMap (Functor.whiskerLeft F (restriction R f))
    let lg := limMap (Functor.whiskerLeft F (restriction R g))
    let pf := (preservesLimitIso (ModuleCat.restrictScalars (R.map f).hom) (F ⋙ evaluation R Y)).inv
    let pg := (preservesLimitIso (ModuleCat.restrictScalars (R.map g).hom) (F ⋙ evaluation R Z)).inv
    let e := ModuleCat.restrictScalarsComp'App (R.map f).hom (R.map g).hom (R.map (f ≫ g)).hom
      (by simp) (limit (F ⋙ evaluation R Z))
    let ej := ModuleCat.restrictScalarsComp'App (R.map f).hom (R.map g).hom (R.map (f ≫ g)).hom
      (by simp) ((F.obj j).obj Z)
    have h1 :
        lf ≫ pf ≫ (ModuleCat.restrictScalars (R.map f).hom).map lg ≫
          (ModuleCat.restrictScalars (R.map f).hom).map pg ≫ e.inv ≫
            (preservesLimitIso (ModuleCat.restrictScalars (R.map (f ≫ g)).hom)
              (F ⋙ evaluation R Z)).hom ≫
              limit.π ((F ⋙ evaluation R Z) ⋙ ModuleCat.restrictScalars (R.map (f ≫ g)).hom) j =
        lf ≫ pf ≫ (ModuleCat.restrictScalars (R.map f).hom).map lg ≫
          (ModuleCat.restrictScalars (R.map f).hom).map pg ≫ e.inv ≫
            (ModuleCat.restrictScalars (R.map (f ≫ g)).hom).map (limit.π (F ⋙ evaluation R Z) j) := by
      simp [lf, lg, pf, pg, e, preservesLimitIso_hom_π]
    have h2 :
        (ModuleCat.restrictScalars (R.map f).hom).map lg ≫
          (ModuleCat.restrictScalars (R.map f).hom).map pg ≫ e.inv ≫
            (ModuleCat.restrictScalars (R.map (f ≫ g)).hom).map (limit.π (F ⋙ evaluation R Z) j) =
          (ModuleCat.restrictScalars (R.map f).hom).map
              (lg ≫ limit.π ((F ⋙ evaluation R Z) ⋙ ModuleCat.restrictScalars (R.map g).hom) j) ≫
            ej.inv := by
      rw [← ModuleCat.restrictScalarsComp'App_inv_naturality]
      dsimp [pg, e, ej]
      rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc, Category.assoc,
        preservesLimitIso_inv_π]
    have step3 :
        lf ≫ pf ≫ (ModuleCat.restrictScalars (R.map f).hom).map
            (lg ≫ limit.π ((F ⋙ evaluation R Z) ⋙ ModuleCat.restrictScalars (R.map g).hom) j) ≫
            ej.inv =
          lf ≫ pf ≫ (ModuleCat.restrictScalars (R.map f).hom).map
            (limit.π (F ⋙ evaluation R Y) j ≫ (Functor.whiskerLeft F (restriction R g)).app j) ≫
            ej.inv := by
      convert congrArg
        (fun t => lf ≫ pf ≫ (ModuleCat.restrictScalars (R.map f).hom).map t ≫ ej.inv)
        (limMap_π (Functor.whiskerLeft F (restriction R g)) j) using 1
    have step5 :
        lf ≫ limit.π ((F ⋙ evaluation R Y) ⋙ ModuleCat.restrictScalars (R.map f).hom) j ≫
            (ModuleCat.restrictScalars (R.map f).hom).map ((F.obj j).map g) ≫
            ej.inv =
          limit.π (F ⋙ evaluation R X) j ≫ (Functor.whiskerLeft F (restriction R f)).app j ≫
            (ModuleCat.restrictScalars (R.map f).hom).map ((F.obj j).map g) ≫
            ej.inv := by
      convert (limMap_π_assoc (Functor.whiskerLeft F (restriction R f)) j
        ((ModuleCat.restrictScalars (R.map f).hom).map ((F.obj j).map g) ≫ ej.inv)) using 1
    symm
    calc
      lf ≫ pf ≫ (ModuleCat.restrictScalars (R.map f).hom).map lg ≫
          (ModuleCat.restrictScalars (R.map f).hom).map pg ≫ e.inv ≫
            (preservesLimitIso (ModuleCat.restrictScalars (R.map (f ≫ g)).hom)
              (F ⋙ evaluation R Z)).hom ≫
              limit.π ((F ⋙ evaluation R Z) ⋙ ModuleCat.restrictScalars (R.map (f ≫ g)).hom) j =
          lf ≫ pf ≫ (ModuleCat.restrictScalars (R.map f).hom).map lg ≫
            (ModuleCat.restrictScalars (R.map f).hom).map pg ≫ e.inv ≫
              (ModuleCat.restrictScalars (R.map (f ≫ g)).hom).map (limit.π (F ⋙ evaluation R Z) j) := h1
      _ = lf ≫ pf ≫
            (ModuleCat.restrictScalars (R.map f).hom).map
              (lg ≫ limit.π ((F ⋙ evaluation R Z) ⋙ ModuleCat.restrictScalars (R.map g).hom) j) ≫
            ej.inv := by
          simpa [Category.assoc] using congrArg (fun t => lf ≫ pf ≫ t) h2
      _ = lf ≫ pf ≫ (ModuleCat.restrictScalars (R.map f).hom).map
            (limit.π (F ⋙ evaluation R Y) j ≫ (Functor.whiskerLeft F (restriction R g)).app j) ≫
            ej.inv := step3
      _ = lf ≫ limit.π ((F ⋙ evaluation R Y) ⋙ ModuleCat.restrictScalars (R.map f).hom) j ≫
            (ModuleCat.restrictScalars (R.map f).hom).map ((F.obj j).map g) ≫
            ej.inv := by
          simp [pf, Category.assoc, preservesLimitIso_inv_π_assoc]
      _ = limit.π (F ⋙ evaluation R X) j ≫ (Functor.whiskerLeft F (restriction R f)).app j ≫
            (ModuleCat.restrictScalars (R.map f).hom).map ((F.obj j).map g) ≫
            ej.inv := step5
      _ = limit.π (F ⋙ evaluation R X) j ≫ (F.obj j).map f ≫
            (ModuleCat.restrictScalars (R.map f).hom).map ((F.obj j).map g) ≫
            ej.inv := by
          simp [Functor.whiskerLeft_app, restriction_app]

set_option backward.isDefEq.respectTransparency false in
/-- The (limit) cone for `F : J ⥤ PresheafOfModules.{v} R` that is constructed from the limit
of `F ⋙ evaluation R X` for all `X`. -/
@[simps]
noncomputable def limitCone : Cone F where
  pt := limitPresheafOfModules F
  π :=
    { app := fun j ↦
        { app := fun X ↦ limit.π (F ⋙ evaluation R X) j
          naturality := fun {X Y} f ↦ by
            dsimp
            simp only [assoc, preservesLimitIso_inv_π]
            apply limMap_π }
      naturality := fun {j j'} f ↦ by
        ext1 X
        simpa using (limit.w (F ⋙ evaluation R X) f).symm }

/-- The cone `limitCone F` is limit for any `F : J ⥤ PresheafOfModules.{v} R`. -/
noncomputable def isLimitLimitCone : IsLimit (limitCone F) :=
  evaluationJointlyReflectsLimits _ _ (fun _ => limit.isLimit _)

instance hasLimit : HasLimit F := ⟨_, isLimitLimitCone F⟩

noncomputable instance evaluation_preservesLimit (X : Cᵒᵖ) :
    PreservesLimit F (evaluation R X) :=
  preservesLimit_of_preserves_limit_cone (isLimitLimitCone F) (limit.isLimit _)

noncomputable instance toPresheaf_preservesLimit :
    PreservesLimit F (toPresheaf R) :=
  preservesLimit_of_preserves_limit_cone (isLimitLimitCone F)
    (Limits.evaluationJointlyReflectsLimits _
      (fun X => isLimitOfPreserves (evaluation R X ⋙ forget₂ _ AddCommGrpCat)
        (isLimitLimitCone F)))

end Limits

variable (R J)

section Small

variable [Small.{v} J]

instance hasLimitsOfShape : HasLimitsOfShape J (PresheafOfModules.{v} R) where
instance hasLimitsOfSize : HasLimitsOfSize.{v, v} (PresheafOfModules.{v} R) where

instance (X : Cᵒᵖ) : PreservesLimitsOfShape J (evaluation.{v} R X) where
instance (X : Cᵒᵖ) : PreservesLimitsOfSize.{v, v} (evaluation.{v} R X) where

instance : PreservesLimitsOfShape J (toPresheaf.{v} R) where
instance : PreservesLimitsOfSize.{v, v} (toPresheaf.{v} R) where

end Small

section Finite

instance hasFiniteLimits : HasFiniteLimits (PresheafOfModules.{v} R) :=
  ⟨fun _ => inferInstance⟩

noncomputable instance evaluation_preservesFiniteLimits (X : Cᵒᵖ) :
    PreservesFiniteLimits (evaluation.{v} R X) where

noncomputable instance toPresheaf_preservesFiniteLimits :
    PreservesFiniteLimits (toPresheaf.{v} R) where

end Finite

end PresheafOfModules
