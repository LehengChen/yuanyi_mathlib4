/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Galois.EssSurj
public import Mathlib.CategoryTheory.Action.Continuous
public import Mathlib.Topology.Category.FinTopCat

/-!
# Fiber functors induce an equivalence of categories

Let `C` be a Galois category with fiber functor `F`.

In this file we conclude that the induced functor from `C` to the category of finite,
discrete `Aut F`-sets is an equivalence of categories.
-/

@[expose] public section

universe u₂ u₁ w

open CategoryTheory

namespace CategoryTheory

variable {C : Type u₁} [Category.{u₂} C] {F : C ⥤ FintypeCat.{w}}

namespace PreGaloisCategory

open scoped FintypeCatDiscrete

variable (F) in
/-- The induced functor from `C` to the category of finite, discrete `Aut F`-sets. -/
@[simps! obj_obj map]
def functorToContAction : C ⥤ ContAction FintypeCat (Aut F) :=
  ObjectProperty.lift _ (functorToAction F) (fun X ↦ continuousSMul_aut_fiber F X)

instance [F.Faithful] : (functorToContAction F).Faithful := by
  haveI : (functorToAction F).Faithful := by
    have : Functor.Faithful (functorToAction F ⋙ forget₂ _ FintypeCat) :=
      inferInstanceAs <| Functor.Faithful F
    exact Functor.Faithful.of_comp (functorToAction F) (forget₂ _ FintypeCat)
  exact inferInstanceAs <| (ObjectProperty.lift _ _ _).Faithful

variable [PreGaloisCategory C] [FiberFunctor F]

instance : (functorToContAction F).Full :=
  letI : GaloisCategory C :=
    { hasFiberFunctor := ⟨F ⋙ FintypeCat.uSwitch.{w, u₂}, ⟨FiberFunctor.comp_right _⟩⟩ }
  inferInstanceAs <| (ObjectProperty.lift _ _ _).Full

instance {F : C ⥤ FintypeCat.{u₁}} [FiberFunctor F] : (functorToContAction F).EssSurj where
  mem_essImage X := by
    letI : GaloisCategory C :=
      { hasFiberFunctor := ⟨F ⋙ FintypeCat.uSwitch.{u₁, u₂}, ⟨FiberFunctor.comp_right _⟩⟩ }
    have : ContinuousSMul (Aut F) X.obj.V := X.2
    obtain ⟨A, ⟨i⟩⟩ := exists_lift_of_continuous (F := F) X
    exact ⟨A, ⟨ObjectProperty.isoMk _ i⟩⟩

instance : (functorToContAction F).EssSurj := by
  let F' : C ⥤ FintypeCat.{u₁} := F ⋙ FintypeCat.uSwitch.{w, u₁}
  letI : FiberFunctor F' := FiberFunctor.comp_right _
  have : (functorToContAction F').EssSurj := inferInstance
  let f : Aut F ≃ₜ* Aut F' :=
    (autEquivAutWhiskerRight F (FintypeCat.uSwitchEquivalence.{w, u₁}).fullyFaithfulFunctor)
  let equiv : ContAction FintypeCat.{u₁} (Aut F') ≌ ContAction FintypeCat.{w} (Aut F) :=
    (FintypeCat.uSwitchEquivalence.{u₁, w}.mapContAction (Aut F')
       (fun X ↦ by
          rw [Action.isContinuous_def]
          change Continuous ((fun p ↦ (FintypeCat.uSwitchEquiv X.obj.V).symm p) ∘
              (fun p : Aut F' × _ ↦ (X.obj.ρ p.1).hom p.2) ∘
              (fun p : Aut F' × _ ↦ (p.1, FintypeCat.uSwitchEquiv _ p.2)))
          exact Continuous.comp (by fun_prop) (Continuous.comp X.2.1 (by fun_prop)))
       (fun X ↦ by
          rw [Action.isContinuous_def]
          change Continuous ((fun p ↦ (FintypeCat.uSwitchEquiv X.obj.V).symm p) ∘
              (fun p : Aut F' × _ ↦ (X.obj.ρ p.1).hom p.2) ∘
              (fun p : Aut F' × _ ↦ (p.1, FintypeCat.uSwitchEquiv _ p.2)))
          exact Continuous.comp (by fun_prop) (Continuous.comp X.2.1 (by fun_prop)))).trans <|
      ContAction.resEquiv _ f
  have : functorToContAction F ≅ functorToContAction F' ⋙ equiv.functor :=
    NatIso.ofComponents
      (fun X ↦ ObjectProperty.isoMk _ (Action.mkIso (FintypeCat.uSwitchEquivalence.unitIso.app _)
      (fun g ↦ FintypeCat.uSwitchEquivalence.unitIso.hom.naturality (g.hom.app X))))
      (fun f ↦ by
        ext : 2
        exact FintypeCat.uSwitchEquivalence.unitIso.hom.naturality (F.map f))
  exact Functor.essSurj_of_iso this.symm

/-- Any fiber functor `F` induces an equivalence of categories with the category of finite and
discrete `Aut F`-sets. -/
@[stacks 0BN4]
instance : (functorToContAction F).IsEquivalence where

end PreGaloisCategory

end CategoryTheory
