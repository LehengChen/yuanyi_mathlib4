/-
Copyright (c) 2024 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/
module

public import Mathlib.CategoryTheory.Retract
public import Mathlib.CategoryTheory.MorphismProperty.Basic

/-!
# Stability under retracts

Given `P : MorphismProperty C`, we introduce a typeclass `P.IsStableUnderRetracts` which
is the property that `P` is stable under retracts.

-/

@[expose] public section

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace MorphismProperty

/-- A class of morphisms is stable under retracts if a retract of such a morphism still
lies in the class. -/
@[mk_iff]
class IsStableUnderRetracts (P : MorphismProperty C) : Prop where
  of_retract {X Y Z W : C} {f : X ⟶ Y} {g : Z ⟶ W} (h : RetractArrow f g) (hg : P g) : P f

lemma of_retract {P : MorphismProperty C} [P.IsStableUnderRetracts]
    {X Y Z W : C} {f : X ⟶ Y} {g : Z ⟶ W} (h : RetractArrow f g) (hg : P g) : P f :=
  IsStableUnderRetracts.of_retract h hg

instance {D : Type*} [Category* D] (F : C ⥤ D) (P : MorphismProperty D)
    [P.IsStableUnderRetracts] :
    (P.inverseImage F).IsStableUnderRetracts where
  of_retract h₁ h₂ := of_retract (P := P) (h₁.map F) h₂

instance IsStableUnderRetracts.monomorphisms : (monomorphisms C).IsStableUnderRetracts where
  of_retract {_ _ _ _ _ g} h (_ : Mono g) :=
    mono_of_mono_fac (h := h.left.i ≫ g) (by simpa using h.i_w.symm)

instance IsStableUnderRetracts.epimorphisms : (epimorphisms C).IsStableUnderRetracts where
  of_retract {_ _ _ _ _ g} h (_ : Epi g) :=
    epi_of_epi_fac (h := g ≫ h.right.r) (by simpa using h.r_w)

set_option backward.isDefEq.respectTransparency false in
instance IsStableUnderRetracts.isomorphisms : (isomorphisms C).IsStableUnderRetracts where
  of_retract {X Y Z W f g} h (_ : IsIso _) := by
    exact ⟨h.i.right ≫ inv g ≫ h.r.left, by simp [← h.i_w_assoc], by simp [h.r_w]⟩

instance (P : MorphismProperty C) [P.IsStableUnderRetracts] :
    P.op.IsStableUnderRetracts where
  of_retract h₁ h₂ := P.of_retract h₁.unop h₂

instance (P : MorphismProperty Cᵒᵖ) [P.IsStableUnderRetracts] :
    P.unop.IsStableUnderRetracts where
  of_retract h₁ h₂ := P.of_retract h₁.op h₂

instance (P₁ P₂ : MorphismProperty C)
    [P₁.IsStableUnderRetracts] [P₂.IsStableUnderRetracts] :
    (P₁ ⊓ P₂).IsStableUnderRetracts where
  of_retract := fun h ⟨h₁, h₂⟩ ↦ ⟨of_retract h h₁, of_retract h h₂⟩

/-- The class of morphisms that are retracts of morphisms
belonging to `P : MorphismProperty C`. -/
def retracts (P : MorphismProperty C) : MorphismProperty C :=
  fun _ _ f ↦ ∃ (Z W : C) (g : Z ⟶ W) (_ : RetractArrow f g), P g

lemma le_retracts (P : MorphismProperty C) : P ≤ P.retracts := by
  intro X Y f hf
  exact ⟨_, _, f, { i := 𝟙 _, r := 𝟙 _}, hf⟩

lemma retracts_monotone : Monotone (retracts (C := C)) := by
  intro _ _ h _ _ _ ⟨_, _, _, hg, hg'⟩
  exact ⟨_, _, _, hg, h _ hg'⟩

lemma isStableUnderRetracts_iff_retracts_le (P : MorphismProperty C) :
    P.IsStableUnderRetracts ↔ P.retracts ≤ P := by
  rw [isStableUnderRetracts_iff]
  constructor
  · intro h₁ X Y f ⟨_, _, _, h₂, h₃⟩
    exact h₁ h₂ h₃
  · intro h₁ _ _ _ _ _ _ h₂ h₃
    exact h₁ _ ⟨_, _, _, h₂, h₃⟩

lemma retracts_le (P : MorphismProperty C) [P.IsStableUnderRetracts] :
    P.retracts ≤ P := by
  rwa [← isStableUnderRetracts_iff_retracts_le]

@[simp]
lemma retracts_le_iff {P Q : MorphismProperty C} [Q.IsStableUnderRetracts] :
    P.retracts ≤ Q ↔ P ≤ Q := by
  constructor
  · exact le_trans P.le_retracts
  · intro h
    exact le_trans (retracts_monotone h) Q.retracts_le

instance {P : MorphismProperty C} [P.IsStableUnderRetracts] :
    P.RespectsIso :=
  RespectsIso.of_respects_arrow_iso _
    (fun _ _ e ↦ of_retract (Retract.ofIso e.symm))

end MorphismProperty

end CategoryTheory
