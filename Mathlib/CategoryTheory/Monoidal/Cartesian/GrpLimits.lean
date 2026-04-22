/-
Copyright (c) 2026 Thomas Browning, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning, Christian Merten
-/
module

public import Mathlib.Algebra.Group.Invertible.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Cartesian.ShrinkYoneda
public import Mathlib.CategoryTheory.Monoidal.Internal.Limits

/-!
# Limits in `Grp C`

We show that `Grp C` has limits.
-/

@[expose] public section

namespace CategoryTheory

open Functor Grp Limits MonObj

universe w v

variable {C : Type*} [Category.{v} C] [CartesianMonoidalCategory C]
  {J : Type w} [Category J]

instance [PreservesLimitsOfShape J (Mon.forget C ⋙ shrinkYoneda.{max w v})] :
    PreservesLimitsOfShape J (shrinkYonedaMon.{max w v} (C := C)) :=
  have : PreservesLimitsOfShape J (shrinkYonedaMon ⋙ (whiskeringRight _ _ _).obj (forget MonCat)) :=
    (inferInstance : PreservesLimitsOfShape J (Mon.forget C ⋙ shrinkYoneda.{max w v}))
  preservesLimitsOfShape_of_reflects_of_preserves _ ((whiskeringRight _ _ _).obj (forget MonCat))

/-- An auxiliary construction in order to prove that `Grp.forget₂Mon` creates limits. -/
noncomputable def Grp.limitAux (F : J ⥤ Grp C) (c : Cone (F ⋙ forget₂Mon C)) (hc : IsLimit c)
    [PreservesLimit (F ⋙ forget₂Mon C) (shrinkYonedaMon.{max w v} (C := C))] : Grp C where
  X := c.pt.X
  grp := GrpObj.ofInvertible c.pt.X fun X f ↦
    letI e := Shrink.mulEquiv.symm.trans <| Iso.monCatIsoToMulEquiv <|
      IsLimit.conePointUniqueUpToIso
        (isLimitOfPreserves (shrinkYonedaMon ⋙ (evaluation _ _).obj (.op X)) hc)
        (limit.isLimit _) ≪≫ (preservesLimitIso (forget₂ GrpCat MonCat)
        (F ⋙ shrinkYonedaGrp.{max w v} ⋙ (evaluation _ _).obj (.op X))).symm
    letI := (limit (F ⋙ shrinkYonedaGrp.{max w v} ⋙ (evaluation _ _).obj (.op X))).str
    ((invertibleOfGroup (e f)).map e.symm).copy f (e.symm_apply_apply f).symm

variable [PreservesLimitsOfShape J (shrinkYonedaMon.{max w v} (C := C))]

noncomputable instance : CreatesLimitsOfShape J (forget₂Mon C) where
  CreatesLimit {F} := createsLimitOfReflectsIso fun c hc =>
    let d : Cone F :=
      { pt := limitAux F c hc
        π.app j := (forget₂Mon C).preimage (c.π.app j)
        π.naturality j j' f := by
          apply (forget₂Mon C).map_injective
          simpa using c.π.naturality f }
    let e : (forget₂Mon C).mapCone d ≅ c :=
      Cone.ext (Iso.refl _) (fun j => by
        dsimp [d]
        rw [Functor.map_preimage]
        exact (Category.id_comp (c.π.app j)).symm)
    { liftedCone := d
      validLift := e
      makesLimit := isLimitOfReflects (forget₂Mon C) (IsLimit.ofIsoLimit hc e.symm) }

noncomputable instance : CreatesLimitsOfShape J (Grp.forget C) :=
  inferInstanceAs <| CreatesLimitsOfShape J (forget₂Mon C ⋙ Mon.forget C)

variable [HasLimitsOfShape J (Mon C)]

instance : HasLimitsOfShape J (Grp C) :=
  hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape (forget₂Mon C)

end CategoryTheory
