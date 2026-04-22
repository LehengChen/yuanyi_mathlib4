/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Limits.Opposites
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import Mathlib.CategoryTheory.Limits.Yoneda

/-!

# Ind- and pro- (co)yoneda lemmas

We define limit versions of the yoneda and coyoneda lemmas.

## Main results

Notation: categories `C`, `I` and functors `D : Iᵒᵖ ⥤ C`, `F : C ⥤ Type`.

- `colimitCoyonedaHomIsoLimit`: pro-coyoneda lemma: morphisms from colimit of coyoneda of
  diagram `D` to `F` is limit of `F` evaluated at `D`.
- `colimitCoyonedaHomIsoLimit'`: a variant of `colimitCoyonedaHomIsoLimit` for a covariant
  diagram.

-/

@[expose] public section

universe u₁ u₂ v₁ v₂

namespace CategoryTheory

namespace Limits

open Opposite

variable {C : Type u₁} [Category.{u₂} C] {I : Type v₁} [Category.{v₂} I]

section HomCocontinuousCovariant

variable (F : I ⥤ C) [HasColimit F]

/-- Hom is functorially cocontinuous: coyoneda of a colimit is the limit
over coyoneda of the diagram. -/
noncomputable def coyonedaOpColimitIsoLimitCoyoneda :
    coyoneda.obj (op <| colimit F) ≅ limit (F.op ⋙ coyoneda) :=
  coyoneda.mapIso (limitOpIsoOpColimit F).symm ≪≫ (preservesLimitIso coyoneda F.op)

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma coyonedaOpColimitIsoLimitCoyoneda_hom_comp_π (i : I) :
    (coyonedaOpColimitIsoLimitCoyoneda F).hom ≫ limit.π (F.op.comp coyoneda) ⟨i⟩
      = coyoneda.map (colimit.ι F i).op := by
  simp only [coyonedaOpColimitIsoLimitCoyoneda, Functor.mapIso_symm,
    Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv, Category.assoc, preservesLimitIso_hom_π,
    ← Functor.map_comp, limitOpIsoOpColimit_inv_comp_π]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma coyonedaOpColimitIsoLimitCoyoneda_inv_comp_π (i : I) :
    (coyonedaOpColimitIsoLimitCoyoneda F).inv ≫ coyoneda.map (colimit.ι F i).op =
      limit.π (F.op.comp coyoneda) ⟨i⟩ := by
  rw [← coyonedaOpColimitIsoLimitCoyoneda_hom_comp_π, ← Category.assoc,
    Iso.inv_hom_id, Category.id_comp]

/-- Hom is cocontinuous: homomorphisms from a colimit is the limit over yoneda of the diagram. -/
noncomputable def colimitHomIsoLimitYoneda (A : C) [HasLimit (F.op ⋙ yoneda.obj A)] :
    (colimit F ⟶ A) ≅ limit (F.op ⋙ yoneda.obj A) := by
  let toLimit : (colimit F ⟶ A) → limit (F.op ⋙ yoneda.obj A) := fun f =>
    Types.Limit.mk _ (fun j => colimit.ι F j.unop ≫ f) (by
      intro j j' g
      dsimp [yoneda]
      exact colimit.w_assoc F g.unop f)
  let coconeOfLimit : limit (F.op ⋙ yoneda.obj A) → Cocone F := fun x =>
    { pt := A
      ι :=
        { app := fun i => limit.π (F.op ⋙ yoneda.obj A) (op i) x
          naturality := fun i j f => by
            simpa [yoneda] using congr_fun (limit.w (F.op ⋙ yoneda.obj A) f.op) x } }
  let fromLimit : limit (F.op ⋙ yoneda.obj A) → (colimit F ⟶ A) := fun x =>
    colimit.desc F (coconeOfLimit x)
  refine Equiv.toIso
    { toFun := toLimit
      invFun := fromLimit
      left_inv := ?_
      right_inv := ?_ }
  · intro f
    apply colimit.hom_ext
    intro i
    dsimp [fromLimit, toLimit, coconeOfLimit]
    simp only [colimit.ι_desc, Types.Limit.π_mk]
  · intro x
    apply Types.limit_ext
    intro j
    dsimp [fromLimit, toLimit, coconeOfLimit]
    simp only [Types.Limit.π_mk]
    rw [colimit.ι_desc]

@[reassoc (attr := simp)]
lemma colimitHomIsoLimitYoneda_hom_comp_π (A : C) [HasLimit (F.op ⋙ yoneda.obj A)]
    (i : I) :
    (colimitHomIsoLimitYoneda F A).hom ≫ limit.π (F.op ⋙ yoneda.obj A) ⟨i⟩ =
      (yoneda.obj A).map (colimit.ι F i).op := by
  ext f
  simp [colimitHomIsoLimitYoneda, yoneda]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma colimitHomIsoLimitYoneda_inv_comp_π (A : C) [HasLimit (F.op ⋙ yoneda.obj A)]
    (i : I) :
    (colimitHomIsoLimitYoneda F A).inv ≫ (yoneda.obj A).map (colimit.ι F i).op =
      limit.π (F.op ⋙ yoneda.obj A) ⟨i⟩ := by
  ext x
  simp [colimitHomIsoLimitYoneda]

end HomCocontinuousCovariant

section HomCocontinuousContravariant

variable (F : Iᵒᵖ ⥤ C) [HasColimit F]

/-- Variant of `coyonedaOoColimitIsoLimitCoyoneda` for contravariant `F`. -/
noncomputable def coyonedaOpColimitIsoLimitCoyoneda' :
    coyoneda.obj (op <| colimit F) ≅ limit (F.rightOp ⋙ coyoneda) :=
  coyoneda.mapIso (limitRightOpIsoOpColimit F).symm ≪≫ preservesLimitIso coyoneda F.rightOp

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma coyonedaOpColimitIsoLimitCoyoneda'_hom_comp_π (i : I) :
    (coyonedaOpColimitIsoLimitCoyoneda' F).hom ≫ limit.π (F.rightOp ⋙ coyoneda) i =
      coyoneda.map (colimit.ι F ⟨i⟩).op := by
  simp only [coyonedaOpColimitIsoLimitCoyoneda', Functor.mapIso_symm, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_inv, Category.assoc, preservesLimitIso_hom_π, ← Functor.map_comp,
    limitRightOpIsoOpColimit_inv_comp_π]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma coyonedaOpColimitIsoLimitCoyoneda'_inv_comp_π (i : I) :
    (coyonedaOpColimitIsoLimitCoyoneda' F).inv ≫ coyoneda.map (colimit.ι F ⟨i⟩).op =
      limit.π (F.rightOp ⋙ coyoneda) i := by
  rw [← coyonedaOpColimitIsoLimitCoyoneda'_hom_comp_π, ← Category.assoc,
    Iso.inv_hom_id, Category.id_comp]

/-- Variant of `colimitHomIsoLimitYoneda` for contravariant `F`. -/
noncomputable def colimitHomIsoLimitYoneda' (A : C) [HasLimit (F.rightOp ⋙ yoneda.obj A)] :
    (colimit F ⟶ A) ≅ limit (F.rightOp ⋙ yoneda.obj A) := by
  let toLimit : (colimit F ⟶ A) → limit (F.rightOp ⋙ yoneda.obj A) := fun f =>
    Types.Limit.mk _ (fun i => colimit.ι F (op i) ≫ f) (by
      intro i j g
      dsimp [yoneda]
      exact colimit.w_assoc F g.op f)
  let coconeOfLimit : limit (F.rightOp ⋙ yoneda.obj A) → Cocone F := fun x =>
    { pt := A
      ι :=
        { app := fun i => limit.π (F.rightOp ⋙ yoneda.obj A) i.unop x
          naturality := fun i j f => by
            simpa [yoneda] using congr_fun (limit.w (F.rightOp ⋙ yoneda.obj A) f.unop) x } }
  let fromLimit : limit (F.rightOp ⋙ yoneda.obj A) → (colimit F ⟶ A) := fun x =>
    colimit.desc F (coconeOfLimit x)
  refine Equiv.toIso
    { toFun := toLimit
      invFun := fromLimit
      left_inv := ?_
      right_inv := ?_ }
  · intro f
    apply colimit.hom_ext
    intro i
    dsimp [fromLimit, toLimit, coconeOfLimit]
    simp only [colimit.ι_desc, Types.Limit.π_mk]
  · intro x
    apply Types.limit_ext
    intro i
    dsimp [fromLimit, toLimit, coconeOfLimit]
    simp only [Types.Limit.π_mk]
    rw [colimit.ι_desc]

@[reassoc (attr := simp)]
lemma colimitHomIsoLimitYoneda'_hom_comp_π (A : C) [HasLimit (F.rightOp ⋙ yoneda.obj A)]
    (i : I) :
    (colimitHomIsoLimitYoneda' F A).hom ≫ limit.π (F.rightOp ⋙ yoneda.obj A) i =
      (yoneda.obj A).map (colimit.ι F ⟨i⟩).op := by
  ext f
  simp [colimitHomIsoLimitYoneda', yoneda]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma colimitHomIsoLimitYoneda'_inv_comp_π (A : C) [HasLimit (F.rightOp ⋙ yoneda.obj A)]
    (i : I) :
    (colimitHomIsoLimitYoneda' F A).inv ≫ (yoneda.obj A).map (colimit.ι F ⟨i⟩).op =
      limit.π (F.rightOp ⋙ yoneda.obj A) i := by
  ext x
  simp [colimitHomIsoLimitYoneda']

end HomCocontinuousContravariant

section ProCoyonedaContravariant

variable (D : Iᵒᵖ ⥤ C) (F : C ⥤ Type u₂)
variable [HasColimit (D.rightOp ⋙ coyoneda)] [HasLimit (D ⋙ F ⋙ uliftFunctor.{u₁})]

/-- Pro-Coyoneda lemma: morphisms from colimit of coyoneda of diagram `D` to `F` is limit
of `F` evaluated at `D`. This variant is for contravariant diagrams, see
`colimitCoyonedaHomIsoLimit'` for a covariant version. -/
noncomputable def colimitCoyonedaHomIsoLimit :
    (colimit (D.rightOp ⋙ coyoneda) ⟶ F) ≅ limit (D ⋙ F ⋙ uliftFunctor.{u₁}) :=
  haveI : HasLimit ((D ⋙ Prod.sectL C F) ⋙ coyonedaEvaluation C) :=
    inferInstanceAs <| HasLimit (D ⋙ F ⋙ uliftFunctor.{u₁})
  haveI : HasLimit ((D.rightOp ⋙ coyoneda).op ⋙ yoneda.obj F) :=
    hasLimit_of_iso (Functor.isoWhiskerLeft (D ⋙ Prod.sectL C F) (coyonedaLemma C)).symm
  colimitHomIsoLimitYoneda _ F ≪≫
    HasLimit.isoOfNatIso (Functor.isoWhiskerLeft (D ⋙ Prod.sectL C F) (coyonedaLemma C))

@[simp]
lemma colimitCoyonedaHomIsoLimit_π_apply (f : colimit (D.rightOp ⋙ coyoneda) ⟶ F) (i : I) :
    limit.π (D ⋙ F ⋙ uliftFunctor.{u₁}) (op i) ((colimitCoyonedaHomIsoLimit D F).hom f) =
      ⟨f.app (D.obj (op i)) ((colimit.ι (D.rightOp ⋙ coyoneda) i).app (D.obj (op i))
          (𝟙 (D.obj (op i))))⟩ := by
  change ((colimitCoyonedaHomIsoLimit D F).hom ≫ (limit.π (D ⋙ F ⋙ uliftFunctor.{u₁}) (op i))) f = _
  simp only [colimitCoyonedaHomIsoLimit, Iso.trans_hom, Category.assoc,
    HasLimit.isoOfNatIso_hom_π]
  rw [← Category.assoc, colimitHomIsoLimitYoneda_hom_comp_π]
  dsimp [coyonedaLemma, types_comp_apply]
  rfl

end ProCoyonedaContravariant

section ProCoyonedaContravariantLeftOp

variable (D : I ⥤ Cᵒᵖ) (F : C ⥤ Type u₂)
variable [HasColimit (D ⋙ coyoneda)] [HasLimit (D.leftOp ⋙ F ⋙ uliftFunctor.{u₁})]

/-- Pro-Coyoneda lemma: morphisms from colimit of coyoneda of diagram `D` to `F` is limit
of `F` evaluated at `D`. This variant is for contravariant diagrams, see
`colimitCoyonedaHomIsoLimit'` for a covariant version. -/
noncomputable def colimitCoyonedaHomIsoLimitLeftOp :
    (colimit (D ⋙ coyoneda) ⟶ F) ≅ limit (D.leftOp ⋙ F ⋙ uliftFunctor.{u₁}) :=
  haveI : HasColimit (D.leftOp.rightOp ⋙ coyoneda) :=
    inferInstanceAs <| HasColimit (D ⋙ coyoneda)
  colimitCoyonedaHomIsoLimit D.leftOp F

@[simp]
lemma colimitCoyonedaHomIsoLimitLeftOp_π_apply (f : colimit (D ⋙ coyoneda) ⟶ F) (i : I) :
    limit.π (D.leftOp ⋙ F ⋙ uliftFunctor.{u₁}) (op i)
        ((colimitCoyonedaHomIsoLimitLeftOp D F).hom f) =
      ⟨f.app (D.obj i).unop ((colimit.ι (D ⋙ coyoneda) i).app (D.obj i).unop
          (𝟙 (D.obj i).unop))⟩ :=
  haveI : HasColimit (D.leftOp.rightOp ⋙ coyoneda) :=
    inferInstanceAs <| HasColimit (D ⋙ coyoneda)
  colimitCoyonedaHomIsoLimit_π_apply _ _ _ _

end ProCoyonedaContravariantLeftOp

section IndYonedaCovariant

variable (D : Iᵒᵖ ⥤ Cᵒᵖ) (F : Cᵒᵖ ⥤ Type u₂)
variable [HasColimit (D.unop ⋙ yoneda)] [HasLimit (D ⋙ F ⋙ uliftFunctor.{u₁})]

/-- Ind-Yoneda lemma: morphisms from colimit of yoneda of diagram `D` to `F` is limit of `F`
evaluated at `D`. This version is for covariant diagrams, see `colimitYonedaHomIsoLimit'` for a
contravariant version. -/
noncomputable def colimitYonedaHomIsoLimit :
      (colimit (D.unop ⋙ yoneda) ⟶ F) ≅ limit (D ⋙ F ⋙ uliftFunctor.{u₁}) :=
  haveI : HasLimit ((D ⋙ Prod.sectL Cᵒᵖ F) ⋙ yonedaEvaluation C) :=
    inferInstanceAs <| HasLimit (D ⋙ F ⋙ uliftFunctor.{u₁})
  haveI : HasLimit ((D.unop ⋙ yoneda).op ⋙ yoneda.obj F) :=
    hasLimit_of_iso (Functor.isoWhiskerLeft (D ⋙ Prod.sectL _ _) (yonedaLemma C)).symm
  colimitHomIsoLimitYoneda _ _ ≪≫
    HasLimit.isoOfNatIso (Functor.isoWhiskerLeft (D ⋙ Prod.sectL _ _) (yonedaLemma C))

@[simp]
lemma colimitYonedaHomIsoLimit_π_apply (f : colimit (D.unop ⋙ yoneda) ⟶ F) (i : Iᵒᵖ) :
    limit.π (D ⋙ F ⋙ uliftFunctor.{u₁}) i ((colimitYonedaHomIsoLimit D F).hom f) =
      ⟨f.app (D.obj i)
        ((colimit.ι (D.unop ⋙ yoneda) i.unop).app (D.obj i) (𝟙 (D.obj i).unop))⟩ := by
  change ((colimitYonedaHomIsoLimit D F).hom ≫ (limit.π (D ⋙ F ⋙ uliftFunctor.{u₁}) i)) f = _
  simp only [colimitYonedaHomIsoLimit, Iso.trans_hom, Category.assoc, HasLimit.isoOfNatIso_hom_π]
  rw [← Category.assoc, colimitHomIsoLimitYoneda_hom_comp_π]
  dsimp [yonedaLemma]
  rfl

end IndYonedaCovariant

section IndYonedaCovariantOp

variable (D : I ⥤ C) (F : Cᵒᵖ ⥤ Type u₂)
variable [HasColimit (D ⋙ yoneda)] [HasLimit (D.op ⋙ F ⋙ uliftFunctor.{u₁})]

/-- Ind-Yoneda lemma: morphisms from colimit of yoneda of diagram `D` to `F` is limit of `F`
evaluated at `D`. This version is for covariant diagrams, see `colimitYonedaHomIsoLimit'` for a
contravariant version. -/
noncomputable def colimitYonedaHomIsoLimitOp :
      (colimit (D ⋙ yoneda) ⟶ F) ≅ limit (D.op ⋙ F ⋙ uliftFunctor.{u₁}) :=
  haveI : HasColimit (D.op.unop ⋙ yoneda) :=
    inferInstanceAs <| HasColimit (D ⋙ yoneda)
  colimitYonedaHomIsoLimit D.op F

@[simp]
lemma colimitYonedaHomIsoLimitOp_π_apply (f : colimit (D ⋙ yoneda) ⟶ F) (i : Iᵒᵖ) :
    limit.π (D.op ⋙ F ⋙ uliftFunctor.{u₁}) i ((colimitYonedaHomIsoLimitOp D F).hom f) =
      ⟨f.app (op (D.obj i.unop))
        ((colimit.ι (D ⋙ yoneda) i.unop).app (op (D.obj i.unop)) (𝟙 (D.obj i.unop)))⟩ :=
  haveI : HasColimit (D.op.unop ⋙ yoneda) :=
    inferInstanceAs <| HasColimit (D ⋙ yoneda)
  colimitYonedaHomIsoLimit_π_apply _ _ _ _

end IndYonedaCovariantOp

section ProCoyonedaCovariant

variable (D : I ⥤ C) (F : C ⥤ Type u₂)
variable [HasColimit (D.op ⋙ coyoneda)] [HasLimit (D ⋙ F ⋙ uliftFunctor.{u₁})]

/-- Pro-Coyoneda lemma: morphisms from colimit of coyoneda of diagram `D` to `F` is limit
of `F` evaluated at `D`. This variant is for covariant diagrams, see
`colimitCoyonedaHomIsoLimit` for a covariant version. -/
noncomputable def colimitCoyonedaHomIsoLimit' :
    (colimit (D.op ⋙ coyoneda) ⟶ F) ≅ limit (D ⋙ F ⋙ uliftFunctor.{u₁}) :=
  haveI : HasLimit ((D ⋙ Prod.sectL C F) ⋙ coyonedaEvaluation C) :=
    inferInstanceAs <| HasLimit (D ⋙ F ⋙ uliftFunctor.{u₁})
  haveI : HasLimit ((D.op ⋙ coyoneda).rightOp ⋙ yoneda.obj F) :=
    hasLimit_of_iso (Functor.isoWhiskerLeft (D ⋙ Prod.sectL C F) (coyonedaLemma C)).symm
  colimitHomIsoLimitYoneda' _ F ≪≫
    HasLimit.isoOfNatIso (Functor.isoWhiskerLeft (D ⋙ Prod.sectL C F) (coyonedaLemma C))

@[simp]
lemma colimitCoyonedaHomIsoLimit'_π_apply (f : colimit (D.op ⋙ coyoneda) ⟶ F) (i : I) :
    limit.π (D ⋙ F ⋙ uliftFunctor.{u₁}) i ((colimitCoyonedaHomIsoLimit' D F).hom f) =
      ⟨f.app (D.obj i) ((colimit.ι (D.op ⋙ coyoneda) ⟨i⟩).app (D.obj i) (𝟙 (D.obj i)))⟩ := by
  change ((colimitCoyonedaHomIsoLimit' D F).hom ≫ (limit.π (D ⋙ F ⋙ uliftFunctor.{u₁}) i)) f = _
  simp only [colimitCoyonedaHomIsoLimit', Iso.trans_hom, Category.assoc, HasLimit.isoOfNatIso_hom_π]
  rw [← Category.assoc, colimitHomIsoLimitYoneda'_hom_comp_π]
  dsimp [coyonedaLemma]
  rfl

end ProCoyonedaCovariant

section ProCoyonedaCovariantUnop

variable (D : Iᵒᵖ ⥤ Cᵒᵖ) (F : C ⥤ Type u₂)
variable [HasColimit (D ⋙ coyoneda)] [HasLimit (D.unop ⋙ F ⋙ uliftFunctor.{u₁})]

/-- Pro-Coyoneda lemma: morphisms from colimit of coyoneda of diagram `D` to `F` is limit
of `F` evaluated at `D`. This variant is for covariant diagrams, see
`colimitCoyonedaHomIsoLimit` for a covariant version. -/
noncomputable def colimitCoyonedaHomIsoLimitUnop :
    (colimit (D ⋙ coyoneda) ⟶ F) ≅ limit (D.unop ⋙ F ⋙ uliftFunctor.{u₁}) :=
  haveI : HasColimit (D.unop.op ⋙ coyoneda) :=
    inferInstanceAs <| HasColimit (D ⋙ coyoneda)
  colimitCoyonedaHomIsoLimit' D.unop F

@[simp]
lemma colimitCoyonedaHomIsoLimitUnop_π_apply (f : colimit (D ⋙ coyoneda) ⟶ F) (i : I) :
    limit.π (D.unop ⋙ F ⋙ uliftFunctor.{u₁}) i ((colimitCoyonedaHomIsoLimitUnop D F).hom f) =
      ⟨f.app (D.obj (op i)).unop
          ((colimit.ι (D ⋙ coyoneda) ⟨i⟩).app (D.obj (op i)).unop (𝟙 (D.obj (op i)).unop))⟩ :=
  haveI : HasColimit (D.unop.op ⋙ coyoneda) :=
    inferInstanceAs <| HasColimit (D ⋙ coyoneda)
  colimitCoyonedaHomIsoLimit'_π_apply _ _ _ _

end ProCoyonedaCovariantUnop

section IndYonedaContravariant

variable (D : I ⥤ Cᵒᵖ) (F : Cᵒᵖ ⥤ Type u₂)
variable [HasColimit (D.leftOp ⋙ yoneda)] [HasLimit (D ⋙ F ⋙ uliftFunctor.{u₁})]

/-- Ind-Yoneda lemma: morphisms from colimit of yoneda of diagram `D` to `F` is limit of `F`
evaluated at `D`. This version is for contravariant diagrams, see `colimitYonedaHomIsoLimit` for a
covariant version. -/
noncomputable def colimitYonedaHomIsoLimit' :
    (colimit (D.leftOp ⋙ yoneda) ⟶ F) ≅ limit (D ⋙ F ⋙ uliftFunctor.{u₁}) :=
  haveI : HasLimit ((D ⋙ Prod.sectL Cᵒᵖ F) ⋙ yonedaEvaluation C) :=
    inferInstanceAs <| HasLimit (D ⋙ F ⋙ uliftFunctor.{u₁})
  haveI : HasLimit ((D.leftOp ⋙ yoneda).rightOp ⋙ yoneda.obj F) :=
    hasLimit_of_iso (Functor.isoWhiskerLeft (D ⋙ Prod.sectL _ _) (yonedaLemma C)).symm
  colimitHomIsoLimitYoneda' _ F ≪≫
    HasLimit.isoOfNatIso (Functor.isoWhiskerLeft (D ⋙ Prod.sectL _ _) (yonedaLemma C))

@[simp]
lemma colimitYonedaHomIsoLimit'_π_apply (f : colimit (D.leftOp ⋙ yoneda) ⟶ F) (i : I) :
    limit.π (D ⋙ F ⋙ uliftFunctor.{u₁}) i ((colimitYonedaHomIsoLimit' D F).hom f) =
      ⟨f.app (D.obj i)
        ((colimit.ι (D.leftOp ⋙ yoneda) (op i)).app (D.obj i) (𝟙 (D.obj i).unop))⟩ := by
  change ((colimitYonedaHomIsoLimit' D F).hom ≫ (limit.π (D ⋙ F ⋙ uliftFunctor.{u₁}) i)) f = _
  simp only [colimitYonedaHomIsoLimit', Iso.trans_hom, Category.assoc, HasLimit.isoOfNatIso_hom_π]
  rw [← Category.assoc, colimitHomIsoLimitYoneda'_hom_comp_π]
  dsimp [yonedaLemma]
  rfl

end IndYonedaContravariant

section IndYonedaContravariantRightOp

variable (D : Iᵒᵖ ⥤ C) (F : Cᵒᵖ ⥤ Type u₂)
variable [HasColimit (D ⋙ yoneda)] [HasLimit (D.rightOp ⋙ F ⋙ uliftFunctor.{u₁})]

/-- Ind-Yoneda lemma: morphisms from colimit of yoneda of diagram `D` to `F` is limit of `F`
evaluated at `D`. This version is for contravariant diagrams, see `colimitYonedaHomIsoLimit` for a
covariant version. -/
noncomputable def colimitYonedaHomIsoLimitRightOp :
    (colimit (D ⋙ yoneda) ⟶ F) ≅ limit (D.rightOp ⋙ F ⋙ uliftFunctor.{u₁}) :=
  haveI : HasColimit (D.rightOp.leftOp ⋙ yoneda) :=
    inferInstanceAs <| HasColimit (D ⋙ yoneda)
  colimitYonedaHomIsoLimit' D.rightOp F

@[simp]
lemma colimitYonedaHomIsoLimitRightOp_π_apply (f : colimit (D ⋙ yoneda) ⟶ F) (i : I) :
    limit.π (D.rightOp ⋙ F ⋙ uliftFunctor.{u₁}) i ((colimitYonedaHomIsoLimitRightOp D F).hom f) =
      ⟨f.app (op (D.obj (op i)))
        ((colimit.ι (D ⋙ yoneda) (op i)).app (op (D.obj (op i))) (𝟙 (D.obj (op i))))⟩ :=
  haveI : HasColimit (D.rightOp.leftOp ⋙ yoneda) :=
    inferInstanceAs <| HasColimit (D ⋙ yoneda)
  colimitYonedaHomIsoLimit'_π_apply _ _ _ _

end IndYonedaContravariantRightOp

end Limits

end CategoryTheory
