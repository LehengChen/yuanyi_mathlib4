/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.CategoryTheory.Preadditive.Projective.LiftingProperties

/-!
# Characterization of injective objects in terms of lifting properties

An object `I` is injective iff the morphism `I ⟶ 0` has the
right lifting property with respect to monomorphisms,
`injective_iff_rlp_monomorphisms_zero`.

-/

@[expose] public section

universe v u

namespace CategoryTheory

open Limits ZeroObject

variable {C : Type u} [Category.{v} C]

namespace Injective

lemma hasLiftingProperty_of_isZero
    {A B I Z : C} (i : A ⟶ B) [Mono i] [Injective I] (p : I ⟶ Z) (hZ : IsZero Z) :
    HasLiftingProperty i p where
  sq_hasLift {f g} sq := ⟨⟨{
    l := Injective.factorThru f i
    fac_right := hZ.eq_of_tgt _ _ }⟩⟩

instance {A B I : C} (i : A ⟶ B) [Mono i] [Injective I] [HasZeroObject C] (p : I ⟶ 0) :
    HasLiftingProperty i (p : I ⟶ 0) :=
  Injective.hasLiftingProperty_of_isZero i p (isZero_zero C)

end Injective

lemma injective_iff_rlp_monomorphisms_of_isZero
    [HasZeroMorphisms C] {I Z : C} (p : I ⟶ Z) (hZ : IsZero Z) :
    Injective I ↔ (MorphismProperty.monomorphisms C).rlp p := by
  rw [Injective.injective_iff_projective_op]
  refine (projective_iff_llp_epimorphisms_of_isZero p.op hZ.op).trans ⟨?_, ?_⟩
  · intro h A B i hi
    exact (h i.op (by infer_instance)).unop
  · intro h A B i hi
    exact (h i.unop (by infer_instance)).op

lemma injective_iff_rlp_monomorphisms_zero
    [HasZeroMorphisms C] [HasZeroObject C] (I : C) :
    Injective I ↔ (MorphismProperty.monomorphisms C).rlp (0 : I ⟶ 0) :=
  injective_iff_rlp_monomorphisms_of_isZero _ (isZero_zero C)

end CategoryTheory
