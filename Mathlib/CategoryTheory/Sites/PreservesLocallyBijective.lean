/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Sites.DenseSubsite.Basic
public import Mathlib.CategoryTheory.Sites.LocallySurjective
/-!

# Preserving and reflecting local injectivity and surjectivity

This file proves that precomposition with a cocontinuous functor preserves local injectivity and
surjectivity of morphisms of presheaves, and that precomposition with a cover-preserving and
cover-dense functor reflects the same properties.
-/

public section

open CategoryTheory Functor Sieve

variable {C D A : Type*} [Category* C] [Category* D] [Category* A]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (H : C ⥤ D) {F G : Dᵒᵖ ⥤ A} (f : F ⟶ G)

namespace CategoryTheory

namespace Presheaf

variable {FA : A → A → Type*} {CA : A → Type*}
variable [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA]


lemma isLocallyInjective_whisker [H.IsCocontinuous J K] [IsLocallyInjective K f] :
    IsLocallyInjective J (whiskerLeft H.op f) where
  equalizerSieve_mem x y h := H.cover_lift J K (equalizerSieve_mem K f x y h)

set_option backward.isDefEq.respectTransparency false in
lemma isLocallyInjective_of_whisker (hH : CoverPreserving J K H)
    [H.IsCoverDense K] [IsLocallyInjective J (whiskerLeft H.op f)] : IsLocallyInjective K f where
  equalizerSieve_mem {X} a b h := by
    apply K.transitive (H.is_cover_of_isCoverDense K X.unop)
    intro Y g ⟨⟨Z, lift, m, fac⟩⟩
    rw [← fac, Sieve.pullback_comp]
    exact K.pullback_stable lift <| K.superset_covering (functorPullback_pushforward_le H _) <| by
      convert hH.cover_preserve <| equalizerSieve_mem J (whiskerLeft H.op f)
        (F.map m.op a) (F.map m.op b) ?_
      · ext W q; simp [Presheaf.equalizerSieve]
      · simpa using congrArg (fun e ↦ (ConcreteCategory.hom (G.map m.op)) e) h

lemma isLocallyInjective_whisker_iff (hH : CoverPreserving J K H) [H.IsCocontinuous J K]
    [H.IsCoverDense K] : IsLocallyInjective J (whiskerLeft H.op f) ↔ IsLocallyInjective K f :=
  ⟨fun _ ↦ isLocallyInjective_of_whisker J K H f hH,
    fun _ ↦ isLocallyInjective_whisker J K H f⟩

lemma isLocallySurjective_whisker [H.IsCocontinuous J K] [IsLocallySurjective K f] :
    IsLocallySurjective J (whiskerLeft H.op f) where
  imageSieve_mem a := H.cover_lift J K (imageSieve_mem K f a)

lemma isLocallySurjective_of_whisker (hH : CoverPreserving J K H)
    [H.IsCoverDense K] [IsLocallySurjective J (whiskerLeft H.op f)] : IsLocallySurjective K f where
  imageSieve_mem {X} a := by
    apply K.transitive (H.is_cover_of_isCoverDense K X)
    intro Y g ⟨⟨Z, lift, m, fac⟩⟩
    rw [← fac, Sieve.pullback_comp]
    exact K.pullback_stable lift <| K.superset_covering (functorPullback_pushforward_le H _) <| by
      convert hH.cover_preserve <| imageSieve_mem J (whiskerLeft H.op f) (G.map m.op a)
      ext W q; simp [Presheaf.imageSieve]; rfl

lemma isLocallySurjective_whisker_iff (hH : CoverPreserving J K H) [H.IsCocontinuous J K]
    [H.IsCoverDense K] : IsLocallySurjective J (whiskerLeft H.op f) ↔ IsLocallySurjective K f :=
  ⟨fun _ ↦ isLocallySurjective_of_whisker J K H f hH,
    fun _ ↦ isLocallySurjective_whisker J K H f⟩

end Presheaf

end CategoryTheory
