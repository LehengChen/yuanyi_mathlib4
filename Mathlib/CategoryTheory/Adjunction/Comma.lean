/-
Copyright (c) 2021 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
public import Mathlib.CategoryTheory.PUnit

/-!
# Properties of comma categories relating to adjunctions

This file shows that for a functor `G : D ⥤ C` the data of an initial object in each
`StructuredArrow` category on `G` is equivalent to a left adjoint to `G`, as well as the dual.

Specifically, `adjunctionOfStructuredArrowInitials` gives the left adjoint assuming the
appropriate initial objects exist, and `mkInitialOfLeftAdjoint` constructs the initial objects
provided a left adjoint.

The duals are also shown.
-/

@[expose] public section


universe v₁ v₂ u₁ u₂

noncomputable section

namespace CategoryTheory

open Limits

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D] (G : D ⥤ C)

section OfInitials

variable [∀ A, HasInitial (StructuredArrow A G)]

lemma leftAdjointOfStructuredArrowInitialsAux_right_inv (A : C) (B : D)
    (f : A ⟶ G.obj B) : (⊥_ StructuredArrow A G).hom ≫
      G.map (initial.to (StructuredArrow.mk f)).right = f := by
  rw [StructuredArrow.w (initial.to (StructuredArrow.mk f))]
  rfl

attribute [local simp] leftAdjointOfStructuredArrowInitialsAux_right_inv

attribute [local simp] eq_iff_true_of_subsingleton in
/-- Implementation: If each structured arrow category on `G` has an initial object, an equivalence
which is helpful for constructing a left adjoint to `G`.
-/
@[simps]
def leftAdjointOfStructuredArrowInitialsAux (A : C) (B : D) :
    ((⊥_ StructuredArrow A G).right ⟶ B) ≃ (A ⟶ G.obj B) where
  toFun g := (⊥_ StructuredArrow A G).hom ≫ G.map g
  invFun f := CommaMorphism.right (initial.to (StructuredArrow.mk f))
  left_inv g := by
    simp only
    rw [initial.hom_ext (initial.to _) (StructuredArrow.homMk g rfl)]
    rfl
  right_inv f := leftAdjointOfStructuredArrowInitialsAux_right_inv G A B f

/--
If each structured arrow category on `G` has an initial object, construct a left adjoint to `G`. It
is shown that it is a left adjoint in `adjunctionOfStructuredArrowInitials`.
-/
def leftAdjointOfStructuredArrowInitials : C ⥤ D :=
  Adjunction.leftAdjointOfEquiv (leftAdjointOfStructuredArrowInitialsAux G) fun _ _ => by simp

/--
If each structured arrow category on `G` has an initial object, there is a constructed left adjoint
to `G`.
-/
def adjunctionOfStructuredArrowInitials : leftAdjointOfStructuredArrowInitials G ⊣ G :=
  Adjunction.adjunctionOfEquivLeft _ _

/-- If each structured arrow category on `G` has an initial object, `G` is a right adjoint. -/
lemma isRightAdjointOfStructuredArrowInitials : G.IsRightAdjoint where
  exists_leftAdjoint := ⟨_, ⟨adjunctionOfStructuredArrowInitials G⟩⟩

end OfInitials

section OfTerminals

variable [∀ A, HasTerminal (CostructuredArrow G A)]

lemma rightAdjointOfCostructuredArrowTerminalsAux_left_inv (B : D) (A : C)
    (g : G.obj B ⟶ A) : G.map (terminal.from (CostructuredArrow.mk g)).left ≫
      (⊤_ CostructuredArrow G A).hom = g := by
  rw [CostructuredArrow.w (terminal.from (CostructuredArrow.mk g))]
  rfl

attribute [local simp] rightAdjointOfCostructuredArrowTerminalsAux_left_inv

attribute [local simp] eq_iff_true_of_subsingleton in
/-- Implementation: If each costructured arrow category on `G` has a terminal object, an equivalence
which is helpful for constructing a right adjoint to `G`.
-/
@[simps]
def rightAdjointOfCostructuredArrowTerminalsAux (B : D) (A : C) :
    (G.obj B ⟶ A) ≃ (B ⟶ (⊤_ CostructuredArrow G A).left) where
  toFun g := CommaMorphism.left (terminal.from (CostructuredArrow.mk g))
  invFun g := G.map g ≫ (⊤_ CostructuredArrow G A).hom
  left_inv g := rightAdjointOfCostructuredArrowTerminalsAux_left_inv G B A g
  right_inv g := by
    simp only
    rw [terminal.hom_ext (terminal.from _) (CostructuredArrow.homMk g rfl)]
    rfl

/--
If each costructured arrow category on `G` has a terminal object, construct a right adjoint to `G`.
It is shown that it is a right adjoint in `adjunctionOfCostructuredArrowTerminals`.
-/
def rightAdjointOfCostructuredArrowTerminals : C ⥤ D :=
  Adjunction.rightAdjointOfEquiv (rightAdjointOfCostructuredArrowTerminalsAux G)
      fun B₁ B₂ A f g => by
    rw [← Equiv.eq_symm_apply]
    simp only [rightAdjointOfCostructuredArrowTerminalsAux_apply,
      rightAdjointOfCostructuredArrowTerminalsAux_symm_apply, Functor.map_comp, Category.assoc]
    nth_rewrite 1 [← rightAdjointOfCostructuredArrowTerminalsAux_left_inv G B₂ A g]
    rfl

/-- If each costructured arrow category on `G` has a terminal object, there is a constructed right
adjoint to `G`.
-/
def adjunctionOfCostructuredArrowTerminals : G ⊣ rightAdjointOfCostructuredArrowTerminals G :=
  Adjunction.adjunctionOfEquivRight _ _

/-- If each costructured arrow category on `G` has a terminal object, `G` is a left adjoint. -/
lemma isLeftAdjoint_of_costructuredArrowTerminals : G.IsLeftAdjoint where
  exists_rightAdjoint :=
    ⟨rightAdjointOfCostructuredArrowTerminals G, ⟨Adjunction.adjunctionOfEquivRight _ _⟩⟩

end OfTerminals

section

variable {F : C ⥤ D}

attribute [local simp] Adjunction.homEquiv_unit Adjunction.homEquiv_counit

lemma mkInitialOfLeftAdjoint_uniq_right {G' : D ⥤ C} {F' : C ⥤ D} (h : F' ⊣ G')
    (A : C) (s : Cocone (Functor.empty (StructuredArrow A G')))
    (m : (asEmptyCocone (StructuredArrow.mk (h.unit.app A) : StructuredArrow A G')).pt ⟶
      s.pt) : (h.homEquiv A s.pt.right).symm s.pt.hom = m.right := by
  rw [Equiv.symm_apply_eq, Adjunction.homEquiv_unit]
  rw [← StructuredArrow.w m]
  rfl

lemma mkTerminalOfRightAdjoint_uniq_left {G' : D ⥤ C} {F' : C ⥤ D} (h : F' ⊣ G')
    (A : D) (s : Cone (Functor.empty (CostructuredArrow F' A)))
    (m : s.pt ⟶ (asEmptyCone (CostructuredArrow.mk (h.counit.app A) :
      CostructuredArrow F' A)).pt) : h.homEquiv s.pt.left A s.pt.hom = m.left := by
  rw [← Equiv.eq_symm_apply, Adjunction.homEquiv_counit]
  rw [← CostructuredArrow.w m]
  rfl

lemma asEmptyCone_costructuredArrow_mk_hom {F' : C ⥤ D} {A : D} {Y : C}
    (f : F'.obj Y ⟶ A) :
    (asEmptyCone (CostructuredArrow.mk f : CostructuredArrow F' A)).pt.hom = f := rfl

lemma asEmptyCone_costructuredArrow_mk_right {F' : C ⥤ D} {A : D} {Y : C}
    (f : F'.obj Y ⟶ A) :
    (asEmptyCone (CostructuredArrow.mk f : CostructuredArrow F' A)).pt.right = ⟨⟨⟩⟩ := rfl

lemma fromPUnit_obj (A : D) : (Functor.fromPUnit A).obj ⟨⟨⟩⟩ = A := rfl

lemma mkTerminalOfRightAdjoint_lift_w {G' : D ⥤ C} {F' : C ⥤ D} (h : F' ⊣ G') (A : D)
    (B : Cone (Functor.empty (CostructuredArrow F' A))) : F'.map (h.homEquiv B.pt.left A
      B.pt.hom) ≫ (asEmptyCone (CostructuredArrow.mk (h.counit.app A) :
        CostructuredArrow F' A)).pt.hom = B.pt.hom := by
  rw [asEmptyCone_costructuredArrow_mk_hom, asEmptyCone_costructuredArrow_mk_right]
  simp only [fromPUnit_obj]
  rw [← Adjunction.homEquiv_counit, Equiv.symm_apply_apply]

/-- Given a left adjoint to `G`, we can construct an initial object in each structured arrow
category on `G`. -/
def mkInitialOfLeftAdjoint (h : F ⊣ G) (A : C) :
    IsInitial (StructuredArrow.mk (h.unit.app A) : StructuredArrow A G) where
  desc B := StructuredArrow.homMk ((h.homEquiv _ _).symm B.pt.hom) (by simp)
  uniq s m _ := by
    rw [StructuredArrow.hom_eq_iff]
    simp [mkInitialOfLeftAdjoint_uniq_right h A s m]

/-- Given a right adjoint to `F`, we can construct a terminal object in each costructured arrow
category on `F`. -/
def mkTerminalOfRightAdjoint (h : F ⊣ G) (A : D) :
    IsTerminal (CostructuredArrow.mk (h.counit.app A) : CostructuredArrow F A) where
  lift B := CostructuredArrow.homMk (h.homEquiv _ _ B.pt.hom)
    (mkTerminalOfRightAdjoint_lift_w h A B)
  uniq s m _ := by
    rw [CostructuredArrow.hom_eq_iff]
    simp [mkTerminalOfRightAdjoint_uniq_left h A s m]

end

theorem isRightAdjoint_iff_hasInitial_structuredArrow {G : D ⥤ C} :
    G.IsRightAdjoint ↔ ∀ A, HasInitial (StructuredArrow A G) :=
  ⟨fun _ A => (mkInitialOfLeftAdjoint _ (Adjunction.ofIsRightAdjoint G) A).hasInitial,
    fun _ => isRightAdjointOfStructuredArrowInitials _⟩

theorem isLeftAdjoint_iff_hasTerminal_costructuredArrow {F : C ⥤ D} :
    F.IsLeftAdjoint ↔ ∀ A, HasTerminal (CostructuredArrow F A) :=
  ⟨fun _ A => (mkTerminalOfRightAdjoint _ (Adjunction.ofIsLeftAdjoint F) A).hasTerminal,
    fun _ => isLeftAdjoint_of_costructuredArrowTerminals _⟩

end CategoryTheory
