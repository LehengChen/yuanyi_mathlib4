/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Abelian.Subobject
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.CategoryTheory.Generator.Preadditive
public import Mathlib.CategoryTheory.Abelian.Opposite

/-!
# A complete abelian category with enough injectives and a separator has an injective coseparator

## Future work
* Once we know that Grothendieck categories have enough injectives, we can use this to conclude
  that Grothendieck categories have an injective coseparator.

## References
* [Peter J Freyd, *Abelian Categories* (Theorem 3.37)][freyd1964abelian]

-/

public section


open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace CategoryTheory.Abelian

variable {C : Type u} [Category.{v} C] [Abelian C]

theorem has_injective_coseparator [HasLimits C] [EnoughInjectives C] (G : C) (hG : IsSeparator G) :
    ∃ G : C, Injective G ∧ IsCoseparator G := by
  haveI : WellPowered.{v} C := wellPowered_of_isDetector G hG.isDetector
  haveI : HasProductsOfShape (Subobject (op G)) C := hasProductsOfShape_of_small.{v} _ _
  refine ⟨piObj fun P : Subobject (op G) => Injective.under (unop P), inferInstance,
    (isCoseparator_pi _).2 <| (Preadditive.isCoseparating_iff _).2 fun X Y f hf => ?_⟩
  refine (Preadditive.isSeparator_iff _).1 hG _ fun h => ?_
  suffices factorThruImage (h ≫ f) = 0 by simp [← Limits.image.fac (h ≫ f), this]
  let R := Subobject.mk (factorThruImage (h ≫ f)).op
  let q : image (h ≫ f) ⟶ Injective.under (unop R) :=
    (Subobject.underlyingIso (factorThruImage (h ≫ f)).op).unop.hom ≫ Injective.ι _
  exact zero_of_comp_mono q
    (by rw [← Injective.comp_factorThru q (Limits.image.ι (h ≫ f)), Limits.image.fac_assoc,
      Category.assoc, hf _ (by simp), comp_zero])

theorem has_projective_separator [HasColimits C] [EnoughProjectives C] (G : C)
    (hG : IsCoseparator G) : ∃ G : C, Projective G ∧ IsSeparator G := by
  obtain ⟨T, hT₁, hT₂⟩ := has_injective_coseparator (op G) ((isSeparator_op_iff _).2 hG)
  exact ⟨unop T, inferInstance, (isSeparator_unop_iff _).2 hT₂⟩

end CategoryTheory.Abelian
