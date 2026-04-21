/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Shift.CommShift
public import Mathlib.CategoryTheory.Shift.Induced
public import Mathlib.CategoryTheory.Quotient

/-!
# The shift on a quotient category

Let `C` be a category equipped a shift by a monoid `A`. If we have a relation
on morphisms `r : HomRel C` that is compatible with the shift (i.e. if two
morphisms `f` and `g` are related, then `f⟦a⟧'` and `g⟦a⟧'` are also related
for all `a : A`), then the quotient category `Quotient r` is equipped with
a shift.

The condition `r.IsCompatibleWithShift A` on the relation `r` is a class so that
the shift can be automatically inferred on the quotient category.

-/

@[expose] public section

universe v v' u u' w

open CategoryTheory Category

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (F : C ⥤ D) (r : HomRel C) (A : Type w) [AddMonoid A] [HasShift C A] [HasShift D A]

namespace HomRel

/-- A relation on morphisms is compatible with the shift by a monoid `A` when the
relation if preserved by the shift. -/
class IsCompatibleWithShift : Prop where
  /-- the condition that the relation is preserved by the shift -/
  condition : ∀ (a : A) ⦃X Y : C⦄ (f g : X ⟶ Y), r f g → r (f⟦a⟧') (g⟦a⟧')

end HomRel

namespace CategoryTheory

/-- The shift by a monoid `A` induced on a quotient category `Quotient r` when the
relation `r` is compatible with the shift. -/
noncomputable instance HasShift.quotient [r.IsCompatibleWithShift A] :
    HasShift (Quotient r) A :=
  HasShift.induced (Quotient.functor r) A
    (fun a => Quotient.lift r (shiftFunctor C a ⋙ Quotient.functor r)
      (fun _ _ _ _ hfg => Quotient.sound r (HomRel.IsCompatibleWithShift.condition _ _ _ hfg)))
    (fun _ => Quotient.lift.isLift _ _ _)

/-- The functor `Quotient.functor r : C ⥤ Quotient r` commutes with the shift. -/
noncomputable instance Quotient.functor_commShift [r.IsCompatibleWithShift A] :
    (Quotient.functor r).CommShift A :=
  Functor.CommShift.ofInduced _ _ _ _

-- the construction is made irreducible in order to prevent timeouts and abuse of defeq
#adaptation_note /-- After https://github.com/leanprover/lean4/pull/12247
doing so requires `allowUnsafeReducibility`. -/
set_option allowUnsafeReducibility true in
attribute [irreducible] HasShift.quotient Quotient.functor_commShift

namespace Quotient

variable [r.IsCompatibleWithShift A] [F.CommShift A]
    (hF : ∀ (x y : C) (f₁ f₂ : x ⟶ y), r f₁ f₂ → F.map f₁ = F.map f₂)

namespace LiftCommShift

variable {A}

/-- Auxiliary definition for `Quotient.liftCommShift`. -/
noncomputable def iso (a : A) :
    shiftFunctor (Quotient r) a ⋙ lift r F hF ≅ lift r F hF ⋙ shiftFunctor D a :=
  natIsoLift r ((Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight ((functor r).commShiftIso a).symm _ ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (lift.isLift r F hF) ≪≫ F.commShiftIso a ≪≫
    Functor.isoWhiskerRight (lift.isLift r F hF).symm _ ≪≫ Functor.associator _ _ _)

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma iso_hom_app (a : A) (X : C) :
    (iso F r hF a).hom.app ((functor r).obj X) =
      (lift r F hF).map (((functor r).commShiftIso a).inv.app X) ≫
      (F.commShiftIso a).hom.app X := by
  dsimp only [iso, natIsoLift]
  rw [natTransLift_app]
  dsimp
  rw [Functor.map_id]
  simp [lift_obj_functor_obj]

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma iso_inv_app (a : A) (X : C) :
    (iso F r hF a).inv.app ((functor r).obj X) =
      (F.commShiftIso a).inv.app X ≫
      (lift r F hF).map (((functor r).commShiftIso a).hom.app X) := by
  dsimp only [iso, natIsoLift]
  rw [natTransLift_app]
  dsimp
  rw [(shiftFunctor D a).map_id (F.obj X)]
  simp only [comp_id, id_comp]
  exact
    congrArg (fun k =>
      k ≫ (lift r F hF).map ((Functor.commShiftIso (functor r) a).hom.app X)) <|
      Category.id_comp ((Functor.commShiftIso F a).inv.app X)

attribute [irreducible] iso

end LiftCommShift

set_option backward.isDefEq.respectTransparency false in
/-- When `r : HomRel C` is compatible with the shift by an additive monoid, and
`F : C ⥤ D` is a functor which commutes with the shift and is compatible with `r`, then
the induced functor `Quotient.lift r F _ : Quotient r ⥤ D` also commutes with the shift. -/
@[simps -isSimp commShiftIso]
noncomputable instance liftCommShift :
    (Quotient.lift r F hF).CommShift A where
  commShiftIso := LiftCommShift.iso F r hF
  commShiftIso_zero := by
    ext1
    apply natTrans_ext
    ext X
    dsimp
    rw [LiftCommShift.iso_hom_app, (functor r).commShiftIso_zero,
      Functor.CommShift.isoZero_hom_app, Functor.CommShift.isoZero_inv_app,
      Functor.map_comp, assoc, F.commShiftIso_zero, Functor.CommShift.isoZero_hom_app,
      lift_map_functor_map, ← F.map_comp_assoc, Iso.inv_hom_id_app]
    dsimp [lift_obj_functor_obj]
    rw [F.map_id, id_comp]
  commShiftIso_add a b := by
    ext1
    apply natTrans_ext
    ext X
    dsimp
    rw [LiftCommShift.iso_hom_app, (functor r).commShiftIso_add, F.commShiftIso_add,
      Functor.CommShift.isoAdd_hom_app, Functor.CommShift.isoAdd_hom_app,
      Functor.CommShift.isoAdd_inv_app, Functor.map_comp, Functor.map_comp,
      Functor.map_comp, assoc, assoc, assoc, LiftCommShift.iso_hom_app, lift_map_functor_map]
    congr 1
    rw [← cancel_epi ((shiftFunctor (Quotient r) b ⋙ lift r F hF).map
      (NatTrans.app (Functor.commShiftIso (functor r) a).hom X))]
    have hnat :
        (shiftFunctor (Quotient r) b ⋙ lift r F hF).map
            ((Functor.commShiftIso (functor r) a).hom.app X) ≫
          (LiftCommShift.iso F r hF b).hom.app
            ((shiftFunctor (Quotient r) a).obj ((functor r).obj X)) ≫
            (shiftFunctor D b).map
              ((lift r F hF).map ((Functor.commShiftIso (functor r) a).inv.app X) ≫
                (Functor.commShiftIso F a).hom.app X) ≫
              (shiftFunctorAdd D a b).inv.app ((lift r F hF).obj ((functor r).obj X)) =
        (LiftCommShift.iso F r hF b).hom.app ((shiftFunctor C a ⋙ functor r).obj X) ≫
          (lift r F hF ⋙ shiftFunctor D b).map
            ((Functor.commShiftIso (functor r) a).hom.app X) ≫
            (shiftFunctor D b).map
              ((lift r F hF).map ((Functor.commShiftIso (functor r) a).inv.app X) ≫
                (Functor.commShiftIso F a).hom.app X) ≫
              (shiftFunctorAdd D a b).inv.app ((lift r F hF).obj ((functor r).obj X)) := by
      simpa using
        NatTrans.naturality_assoc ((LiftCommShift.iso F r hF b).hom)
          ((Functor.commShiftIso (functor r) a).hom.app X)
          ((shiftFunctor D b).map
            ((lift r F hF).map ((Functor.commShiftIso (functor r) a).inv.app X) ≫
              (Functor.commShiftIso F a).hom.app X) ≫
            (shiftFunctorAdd D a b).inv.app ((lift r F hF).obj ((functor r).obj X)))
    rw [hnat]
    rw [show (LiftCommShift.iso F r hF b).hom.app ((shiftFunctor C a ⋙ functor r).obj X) =
      (lift r F hF).map ((Functor.commShiftIso (functor r) b).inv.app ((shiftFunctor C a).obj X)) ≫
        (Functor.commShiftIso F b).hom.app ((shiftFunctor C a).obj X) by
      simp [LiftCommShift.iso_hom_app, lift_obj_functor_obj]]
    dsimp
    simp only [Functor.comp_obj, assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app,
      Functor.map_id, id_comp, Iso.hom_inv_id_app, lift_obj_functor_obj]

set_option backward.isDefEq.respectTransparency false in
instance liftCommShift_compatibility :
    NatTrans.CommShift (Quotient.lift.isLift r F hF).hom A where
  shift_comm a := by
    ext X
    dsimp
    rw [Functor.commShiftIso_comp_hom_app, liftCommShift_commShiftIso,
      LiftCommShift.iso_hom_app, ← Functor.map_comp_assoc, Iso.hom_inv_id_app]
    simp [lift, Quotient.functor]

end Quotient

end CategoryTheory
