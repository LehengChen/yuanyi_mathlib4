/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import Mathlib.CategoryTheory.Monoidal.Action.Basic
public import Mathlib.CategoryTheory.Monoidal.Opposite

/-!

# Actions from the monoidal opposite of a category.

In this file, given a monoidal category `C` and a category `D`,
we construct a left `C`-action on `D` out of the data of a right `Cᴹᵒᵖ`-action
on `D`. We also construct a right `C`-action on `D` from the data of a left
`Cᴹᵒᵖ`-action on `D`. Conversely, given left/right `C`-actions on `D`,
we construct a `Cᴹᵒᵖ` action with the conjugate variance.

We construct similar actions for `Cᵒᵖ`, namely, left/right `Cᵒᵖ`-actions
on `Dᵒᵖ` from left/right-actions of `C` on `D`, and vice-versa.

These constructions are not made instances in order to avoid instance loops,
you should bring them as local instances if you intend to use them.

-/

@[expose] public section

namespace CategoryTheory.MonoidalCategory

variable (C D : Type*)

variable [Category* C] [MonoidalCategory C] [Category* D]

namespace MonoidalLeftAction
open scoped MonoidalLeftAction MonoidalRightAction
open MonoidalOpposite


/-- Define a left action of `C` on `D` from a right action of `Cᴹᵒᵖ` on `D` via
the formula `c ⊙ₗ d := d ⊙ᵣ (mop c)`. -/
@[simps -isSimp, implicit_reducible]
def leftActionOfMonoidalOppositeRightAction [MonoidalRightAction Cᴹᵒᵖ D] :
    MonoidalLeftAction C D where
  actionObj c d := d ⊙ᵣ mop c
  actionHomLeft {c c'} f d := d ⊴ᵣ f.mop
  actionHomRight c {d d'} f := f ⊵ᵣ mop c
  actionHom {c c'} {d d} f g := g ⊙ᵣₘ f.mop
  actionAssocIso _ _ _ := αᵣ _ _ _
  actionUnitIso _ := ρᵣ _
  actionHom_def _ _ := MonoidalRightAction.actionHom_def' _ _
  actionAssocIso_hom_naturality _ _ _ :=
    MonoidalRightAction.actionAssocIso_hom_naturality _ _ _
  actionUnitIso_hom_naturality _ :=
    MonoidalRightAction.actionUnitIso_hom_naturality _
  rightUnitor_actionHom c d :=
    MonoidalRightAction.actionHom_leftUnitor _ _
  associator_actionHom c₁ c₂ c₃ d := by
    simpa only [mop_tensorObj, mop_hom_associator,
      MonoidalRightAction.actionHomRight_inv_hom_assoc] using
      (d ⊴ᵣ (α_ (mop c₃) (mop c₂) (mop c₁)).inv) ≫=
        MonoidalRightAction.actionHom_associator
          (mop c₃) (mop c₂) (mop c₁) d |>.symm

/-- Define a left action of `Cᴹᵒᵖ` on `D` from a right action of `C` on `D` via
the formula `mop c ⊙ₗ d = d ⊙ᵣ c`. -/
@[instance_reducible, simps -isSimp]
def monoidalOppositeLeftAction [MonoidalRightAction C D] :
    MonoidalLeftAction Cᴹᵒᵖ D where
  actionObj c d := d ⊙ᵣ unmop c
  actionHomLeft {c c'} f d := d ⊴ᵣ f.unmop
  actionHomRight c {d d'} f := f ⊵ᵣ unmop c
  actionHom {c c'} {d d} f g := g ⊙ᵣₘ f.unmop
  actionAssocIso _ _ _ := αᵣ _ _ _
  actionUnitIso _ := ρᵣ _
  actionHom_def _ _ := MonoidalRightAction.actionHom_def' _ _
  actionAssocIso_hom_naturality _ _ _ :=
    MonoidalRightAction.actionAssocIso_hom_naturality _ _ _
  actionUnitIso_hom_naturality _ :=
    MonoidalRightAction.actionUnitIso_hom_naturality _
  rightUnitor_actionHom c d :=
    MonoidalRightAction.actionHom_leftUnitor _ _
  associator_actionHom c₁ c₂ c₃ d := by
    simpa only [mop_tensorObj, mop_hom_associator,
      MonoidalRightAction.actionHomRight_inv_hom_assoc] using
      (d ⊴ᵣ (α_ (unmop c₃) (unmop c₂) (unmop c₁)).inv) ≫=
        MonoidalRightAction.actionHom_associator
          (unmop c₃) (unmop c₂) (unmop c₁) d |>.symm

section

attribute [local instance] monoidalOppositeLeftAction
variable [MonoidalRightAction C D]

lemma monoidalOppositeLeftAction_actionObj_mop (c : Cᴹᵒᵖ) (d : D) :
    c ⊙ₗ d = d ⊙ᵣ c.unmop := rfl

lemma monoidalOppositeLeftAction_actionHomLeft_mop
    {c c' : Cᴹᵒᵖ} (f : c ⟶ c') (d : D) :
    f ⊵ₗ d = d ⊴ᵣ f.unmop := rfl

lemma monoidalOppositeLeftAction_actionRight_mop
    (c : Cᴹᵒᵖ) {d d' : D} (f : d ⟶ d') :
    c ⊴ₗ f = f ⊵ᵣ c.unmop := rfl

lemma monoidalOppositeLeftAction_actionHom_mop_mop
    {c c' : Cᴹᵒᵖ} {d d' : D} (f : c ⟶ c') (g : d ⟶ d') :
    f ⊙ₗₘ g = g ⊙ᵣₘ f.unmop := rfl

lemma monoidalOppositeLeftAction_actionAssocIso_mop_mop (c c' : Cᴹᵒᵖ) (d : D) :
    αₗ c c' d = αᵣ d c'.unmop c.unmop := rfl

end

open Opposite

/-- Define a left action of `Cᵒᵖ` on `Dᵒᵖ` from a left action of `C` on `D` via
the formula `(op c) ⊙ₗ (op d) = op (c ⊙ₗ d)`. -/
@[instance_reducible, simps -isSimp]
def oppositeLeftAction [MonoidalLeftAction C D] :
    MonoidalLeftAction Cᵒᵖ Dᵒᵖ where
  actionObj c d := op <| c.unop ⊙ₗ d.unop
  actionHomLeft f d := (f.unop ⊵ₗ unop d).op
  actionHomRight c _ _ f := (unop c ⊴ₗ f.unop).op
  actionHom f g := (f.unop ⊙ₗₘ g.unop).op
  actionAssocIso _ _ _ := Iso.op <| (αₗ _ _ _).symm
  actionUnitIso _ := Iso.op <| (λₗ _).symm
  actionHom_def
    | op f, op g => by
        apply Quiver.Hom.unop_inj
        simpa [MonoidalLeftAction.action_exchange] using
          MonoidalLeftAction.actionHom_def f g
  actionAssocIso_hom_naturality
    | op f, op g, op h => by
        apply Quiver.Hom.unop_inj
        haveI := (αₗ (unop _) (unop _) (unop _)).inv ≫=
          MonoidalLeftAction.actionAssocIso_hom_naturality f g h
        simp only [Iso.inv_hom_id_assoc] at this
        simp [← this]
  actionUnitIso_hom_naturality _ := by
    apply Quiver.Hom.unop_inj
    simp
  whiskerRight_actionHomLeft _ _ _ := by
    apply Quiver.Hom.unop_inj
    simp
  associator_actionHom _ _ _ _ := by
    apply Quiver.Hom.unop_inj
    apply IsIso.inv_eq_inv.mp
    simp
  leftUnitor_actionHom _ _ := by
    apply Quiver.Hom.unop_inj
    apply IsIso.inv_eq_inv.mp
    simp
  rightUnitor_actionHom _ _ := by
    apply Quiver.Hom.unop_inj
    apply IsIso.inv_eq_inv.mp
    simp

/-- Define a left action of `C` on `D` from a left action of `Cᵒᵖ` on `Dᵒᵖ` via
the formula `c ⊙ₗ d = unop ((op c) ⊙ₗ (op d))`. -/
@[instance_reducible, simps -isSimp]
def leftActionOfOppositeLeftAction [MonoidalLeftAction Cᵒᵖ Dᵒᵖ] :
    MonoidalLeftAction C D where
  actionObj c d := unop <| op c ⊙ₗ op d
  actionHomLeft {c c'} f d := (f.op ⊵ₗ op d).unop
  actionHomRight c {d d'} f := (op c ⊴ₗ f.op).unop
  actionHom {c c'} {d d} f g := (f.op ⊙ₗₘ g.op).unop
  actionAssocIso _ _ _ := Iso.unop <| (αₗ _ _ _).symm
  actionUnitIso _ := Iso.unop <| (λₗ _).symm
  actionHom_def f g := by
    apply Quiver.Hom.op_inj
    simpa [MonoidalLeftAction.action_exchange] using
      MonoidalLeftAction.actionHom_def f.op g.op
  actionAssocIso_hom_naturality f g h := by
    apply Quiver.Hom.op_inj
    haveI := (αₗ (op _) (op _) (op _)).inv ≫=
      MonoidalLeftAction.actionAssocIso_hom_naturality f.op g.op h.op
    simp only [Iso.inv_hom_id_assoc] at this
    simp [← this]
  actionUnitIso_hom_naturality _ := by
    apply Quiver.Hom.op_inj
    simp
  whiskerRight_actionHomLeft _ _ _ := by
    apply Quiver.Hom.op_inj
    simp
  associator_actionHom _ _ _ _ := by
    apply Quiver.Hom.op_inj
    apply IsIso.inv_eq_inv.mp
    simp
  leftUnitor_actionHom _ _ := by
    apply Quiver.Hom.op_inj
    apply IsIso.inv_eq_inv.mp
    simp
  rightUnitor_actionHom _ _ := by
    apply Quiver.Hom.op_inj
    apply IsIso.inv_eq_inv.mp
    simp

section

attribute [local instance] oppositeLeftAction
variable [MonoidalLeftAction C D]

lemma oppositeLeftAction_actionObj_op (c : Cᵒᵖ) (d : Dᵒᵖ) :
    c ⊙ₗ d = op (c.unop ⊙ₗ d.unop) := rfl

lemma oppositeLeftAction_actionHomLeft_op
    {c c' : Cᵒᵖ} (f : c ⟶ c') (d : Dᵒᵖ) :
    f ⊵ₗ d = op (f.unop ⊵ₗ d.unop) := rfl

lemma oppositeLeftAction_actionRight_op
    (c : Cᵒᵖ) {d d' : Dᵒᵖ} (f : d ⟶ d') :
    c ⊴ₗ f = op (c.unop ⊴ₗ f.unop) := rfl

lemma oppositeLeftAction_actionHom_op
    {c c' : Cᵒᵖ} {d d' : Dᵒᵖ} (f : c ⟶ c') (g : d ⟶ d') :
    f ⊙ₗₘ g = op (f.unop ⊙ₗₘ g.unop) := rfl

lemma oppositeLeftAction_actionAssocIso_op (c c' : Cᵒᵖ) (d : Dᵒᵖ) :
    αₗ c c' d = (αₗ c.unop c'.unop d.unop).symm.op := rfl

end

section

attribute [local instance] leftActionOfOppositeLeftAction
variable [MonoidalLeftAction Cᵒᵖ Dᵒᵖ]

lemma leftActionOfOppositeLeftAction_actionObj_unop (c : Cᵒᵖ) (d : Dᵒᵖ) :
    (unop c) ⊙ₗ (unop d) = unop (c ⊙ₗ d) := rfl

lemma leftActionOfOppositeLeftAction_actionHomLeft_unop
    {c c' : Cᵒᵖ} (f : c ⟶ c') (d : Dᵒᵖ) :
    f.unop ⊵ₗ unop d = unop (f ⊵ₗ d) := rfl

lemma leftActionOfOppositeLeftAction_actionRight_unop
    (c : Cᵒᵖ) {d d' : Dᵒᵖ} (f : d ⟶ d') :
    unop c ⊴ₗ f.unop = unop (c ⊴ₗ f) := rfl

lemma leftActionOfOppositeLeftAction_actionHom_unop
    {c c' : Cᵒᵖ} {d d' : Dᵒᵖ} (f : c ⟶ c') (g : d ⟶ d') :
    f.unop ⊙ₗₘ g.unop = unop (f ⊙ₗₘ g) := rfl

lemma leftActionOfOppositeLeftAction_actionAssocIso_unop
    (c c' : Cᵒᵖ) (d : Dᵒᵖ) :
    αₗ (unop c) (unop c') (unop d) = (αₗ c c' d).symm.unop := rfl

end

end MonoidalLeftAction

namespace MonoidalRightAction
open scoped MonoidalLeftAction MonoidalRightAction
open MonoidalOpposite

/-- Define a right action of `C` on `D` from a left action of `Cᴹᵒᵖ` on `D` via
the formula `d ⊙ᵣ c := (mop c) ⊙ₗ d`. -/
@[simps -isSimp, implicit_reducible]
def rightActionOfMonoidalOppositeLeftAction [MonoidalLeftAction Cᴹᵒᵖ D] :
    MonoidalRightAction C D where
  actionObj d c := mop c ⊙ₗ d
  actionHomLeft {d d'} f c := mop c ⊴ₗ f
  actionHomRight d _ _ f := f.mop ⊵ₗ d
  actionHom {c c'} {d d'} f g := g.mop ⊙ₗₘ f
  actionAssocIso _ _ _ := αₗ _ _ _
  actionUnitIso _ := λₗ _
  actionHom_def _ _ := MonoidalLeftAction.actionHom_def' _ _
  actionAssocIso_hom_naturality _ _ _ :=
    MonoidalLeftAction.actionAssocIso_hom_naturality _ _ _
  actionUnitIso_hom_naturality _ :=
    MonoidalLeftAction.actionUnitIso_hom_naturality _
  actionHom_associator c₁ c₂ c₃ d := by
    simpa only [mop_tensorObj, mop_hom_associator,
      MonoidalLeftAction.inv_hom_actionHomLeft_assoc] using
      (α_ (mop c₃) (mop c₂) (mop c₁)).inv ⊵ₗ d ≫=
        MonoidalLeftAction.associator_actionHom
          (mop c₃) (mop c₂) (mop c₁) d |>.symm

/-- Define a right action of `Cᴹᵒᵖ` on `D` from a left action of `C` on `D` via
the formula `d ⊙ᵣ mop c = c ⊙ₗ d`. -/
@[instance_reducible, simps -isSimp]
def monoidalOppositeRightAction [MonoidalLeftAction C D] :
    MonoidalRightAction Cᴹᵒᵖ D where
  actionObj d c := unmop c ⊙ₗ d
  actionHomLeft {d d'} f c := unmop c ⊴ₗ f
  actionHomRight d _ _ f := f.unmop ⊵ₗ d
  actionHom {c c'} {d d'} f g := g.unmop ⊙ₗₘ f
  actionAssocIso _ _ _ := αₗ _ _ _
  actionUnitIso _ := λₗ _
  actionHom_def _ _ := MonoidalLeftAction.actionHom_def' _ _
  actionAssocIso_hom_naturality _ _ _ :=
    MonoidalLeftAction.actionAssocIso_hom_naturality _ _ _
  actionUnitIso_hom_naturality _ :=
    MonoidalLeftAction.actionUnitIso_hom_naturality _
  actionHom_associator c₁ c₂ c₃ d := by
    simpa only [mop_tensorObj, mop_hom_associator,
      MonoidalLeftAction.inv_hom_actionHomLeft_assoc] using
      (α_ (unmop c₃) (unmop c₂) (unmop c₁)).inv ⊵ₗ d ≫=
        MonoidalLeftAction.associator_actionHom
          (unmop c₃) (unmop c₂) (unmop c₁) d |>.symm

section

attribute [local instance] monoidalOppositeRightAction
variable [MonoidalLeftAction C D]

lemma monoidalOppositeRightAction_actionObj_mop (c : Cᴹᵒᵖ) (d : D) :
    d ⊙ᵣ c = c.unmop ⊙ₗ d := rfl

lemma monoidalOppositeRightAction_actionHomRight_mop
    {c c' : Cᴹᵒᵖ} (f : c ⟶ c') (d : D) :
    d ⊴ᵣ f = f.unmop ⊵ₗ d := rfl

lemma monoidalOppositeRightAction_actionRight_mop
    (c : Cᴹᵒᵖ) {d d' : D} (f : d ⟶ d') :
    f ⊵ᵣ c = c.unmop ⊴ₗ f := rfl

lemma monoidalOppositeRightAction_actionHom_mop_mop
    {c c' : D} {d d' : Cᴹᵒᵖ} (f : c ⟶ c') (g : d ⟶ d') :
    f ⊙ᵣₘ g = g.unmop ⊙ₗₘ f := rfl

lemma monoidalOppositeRightAction_actionAssocIso_mop_mop (c c' : Cᴹᵒᵖ) (d : D) :
    αᵣ d c c' = αₗ c'.unmop c.unmop d := rfl

end

open Opposite

/-- Define a right action of `Cᵒᵖ` on `Dᵒᵖ` from a right action of `C` on `D` via
the formula `(op d) ⊙ᵣ (op c) = op (d ⊙ᵣ c)`. -/
@[instance_reducible, simps -isSimp]
def oppositeRightAction [MonoidalRightAction C D] :
    MonoidalRightAction Cᵒᵖ Dᵒᵖ where
  actionObj c d := op <| c.unop ⊙ᵣ d.unop
  actionHomLeft {c c'} f d := (f.unop ⊵ᵣ unop d).op
  actionHomRight c {d d'} f := (unop c ⊴ᵣ f.unop).op
  actionHom {c c'} {d d'} f g := (f.unop ⊙ᵣₘ g.unop).op
  actionAssocIso _ _ _ := Iso.op <| (αᵣ _ _ _).symm
  actionUnitIso _ := Iso.op <| (ρᵣ _).symm
  actionHom_def
    | op f, op g => by
        apply Quiver.Hom.unop_inj
        simpa [MonoidalRightAction.action_exchange] using
          MonoidalRightAction.actionHom_def f g
  actionAssocIso_hom_naturality
    | op f, op g, op h => by
        apply Quiver.Hom.unop_inj
        haveI := (αᵣ (unop _) (unop _) (unop _)).inv ≫=
          MonoidalRightAction.actionAssocIso_hom_naturality f g h
        simp only [Iso.inv_hom_id_assoc] at this
        simp [← this]
  actionUnitIso_hom_naturality _ := by
    apply Quiver.Hom.unop_inj
    simp
  whiskerRight_actionHomLeft _ _ _ _ _ := by
    apply Quiver.Hom.unop_inj
    simp
  actionHom_associator _ _ _ _ := by
    apply Quiver.Hom.unop_inj
    apply IsIso.inv_eq_inv.mp
    simp
  actionHom_leftUnitor _ _ := by
    apply Quiver.Hom.unop_inj
    apply IsIso.inv_eq_inv.mp
    simp
  actionHom_rightUnitor _ _ := by
    apply Quiver.Hom.unop_inj
    apply IsIso.inv_eq_inv.mp
    simp

/-- Define a right action of `C` on `D` from a right action of `Cᵒᵖ` on `Dᵒᵖ` via
the formula `d ⊙ᵣ c = unop ((op d) ⊙ᵣ (op c))`. -/
@[instance_reducible, simps -isSimp]
def rightActionOfOppositeRightAction [MonoidalRightAction Cᵒᵖ Dᵒᵖ] :
    MonoidalRightAction C D where
  actionObj c d := unop <| op c ⊙ᵣ op d
  actionHomLeft {c c'} f d := (f.op ⊵ᵣ op d).unop
  actionHomRight c {d d'} f := (op c ⊴ᵣ f.op).unop
  actionHom {c c'} {d d} f g := (f.op ⊙ᵣₘ g.op).unop
  actionAssocIso _ _ _ := Iso.unop <| (αᵣ _ _ _).symm
  actionUnitIso _ := Iso.unop <| (ρᵣ _).symm
  actionHom_def f g := by
    apply Quiver.Hom.op_inj
    simpa [MonoidalRightAction.action_exchange] using
      MonoidalRightAction.actionHom_def f.op g.op
  actionAssocIso_hom_naturality f g h := by
    apply Quiver.Hom.op_inj
    haveI := (αᵣ (op _) (op _) (op _)).inv ≫=
      MonoidalRightAction.actionAssocIso_hom_naturality f.op g.op h.op
    simp only [Iso.inv_hom_id_assoc] at this
    simp [← this]
  actionUnitIso_hom_naturality _ := by
    apply Quiver.Hom.op_inj
    simp
  whiskerRight_actionHomLeft _ _ _ _ _ := by
    apply Quiver.Hom.op_inj
    simp
  actionHom_associator _ _ _ _ := by
    apply Quiver.Hom.op_inj
    apply IsIso.inv_eq_inv.mp
    simp
  actionHom_leftUnitor _ _ := by
    apply Quiver.Hom.op_inj
    apply IsIso.inv_eq_inv.mp
    simp
  actionHom_rightUnitor _ _ := by
    apply Quiver.Hom.op_inj
    apply IsIso.inv_eq_inv.mp
    simp

section

attribute [local instance] oppositeRightAction
variable [MonoidalRightAction C D]

lemma oppositeRightAction_actionObj_op (d : Dᵒᵖ) (c : Cᵒᵖ) :
    d ⊙ᵣ c = op (d.unop ⊙ᵣ c.unop) := rfl

lemma oppositeRightAction_actionHomLeft_op
    {d d' : Dᵒᵖ} (f : d ⟶ d') (c : Cᵒᵖ) :
    f ⊵ᵣ c = op (f.unop ⊵ᵣ c.unop) := rfl

lemma oppositeRightAction_actionRight_op
    (d : Dᵒᵖ) {c c' : Cᵒᵖ} (f : c ⟶ c') :
    d ⊴ᵣ f = op (d.unop ⊴ᵣ f.unop) := rfl

lemma oppositeRightAction_actionHom_op
    {d d' : Dᵒᵖ} {c c' : Cᵒᵖ} (f : d ⟶ d') (g : c ⟶ c') :
    f ⊙ᵣₘ g = op (f.unop ⊙ᵣₘ g.unop) := rfl

lemma oppositeRightAction_actionAssocIso_op (d : Dᵒᵖ) (c c' : Cᵒᵖ) :
    αᵣ d c c' = (αᵣ d.unop c.unop c'.unop).symm.op := rfl

end

section

attribute [local instance] rightActionOfOppositeRightAction
variable [MonoidalRightAction Cᵒᵖ Dᵒᵖ]

lemma rightActionOfOppositeRightAction_actionObj_unop (d : Dᵒᵖ) (c : Cᵒᵖ) :
    unop d ⊙ᵣ unop c = unop (d ⊙ᵣ c) := rfl

lemma rightActionOfOppositeRightAction_actionHomLeft_unop
    {d d' : Dᵒᵖ} (f : d ⟶ d') (c : Cᵒᵖ) :
    f.unop ⊵ᵣ unop c = unop (f ⊵ᵣ c) := rfl

lemma rightActionOfOppositeRightAction_actionRight_unop
    (d : Dᵒᵖ) {c c' : Cᵒᵖ} (f : c ⟶ c') :
    unop d ⊴ᵣ f.unop = unop (d ⊴ᵣ f) := rfl

lemma rightActionOfOppositeRightAction_actionHom_unop
    {d d' : Dᵒᵖ} {c c' : Cᵒᵖ} (f : d ⟶ d') (g : c ⟶ c') :
    f.unop ⊙ᵣₘ g.unop = unop (f ⊙ᵣₘ g) := rfl

lemma rightActionOfOppositeRightAction_actionAssocIso_unop (d : Dᵒᵖ) (c c' : Cᵒᵖ) :
    αᵣ (unop d) (unop c) (unop c') = (αᵣ d c c').symm.unop := rfl

end

end MonoidalRightAction

end CategoryTheory.MonoidalCategory
