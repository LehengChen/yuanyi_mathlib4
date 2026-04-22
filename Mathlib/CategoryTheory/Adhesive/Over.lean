/-
Copyright (c) 2026 Dénes Pápai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dénes Pápai
-/
module

public import Mathlib.CategoryTheory.Adhesive.Basic
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected

/-! # Adhesive structure on slice categories

The slice category `Over B` inherits the property of being adhesive from the
base category.

## TODO
- The dual result for `Under B`.
-/

@[expose] public section

namespace CategoryTheory

open Limits

variable {C : Type*} [Category* C]

/-- Slices of adhesive categories are adhesive. See [adhesive2004], Proposition 8 (ii). -/
instance adhesive_over [Adhesive C] (B : C) : Adhesive (Over B) := by
  let H₁ : ∀ {X Y S : Over B} (f : X ⟶ S) (g : Y ⟶ S) [Mono f], HasPullback f g := by
    intro X Y S f g hf
    haveI : Mono ((Over.forget B).map f) := inferInstance
    haveI : HasPullback ((Over.forget B).map f) ((Over.forget B).map g) := inferInstance
    haveI : HasLimit (cospan f g ⋙ Over.forget B) :=
      hasLimit_of_iso (cospanCompIso (Over.forget B) f g).symm
    exact hasLimit_of_created (cospan f g) (Over.forget B)
  let H₂ : ∀ {X Y S : Over B} (f : S ⟶ X) (g : S ⟶ Y) [Mono f], HasPushout f g := by
    intro X Y S f g hf
    haveI : Mono ((Over.forget B).map f) := inferInstance
    haveI : HasPushout ((Over.forget B).map f) ((Over.forget B).map g) := inferInstance
    haveI : HasColimit (span f g ⋙ Over.forget B) :=
      hasColimit_of_iso (spanCompIso (Over.forget B) f g)
    exact hasColimit_of_created (span f g) (Over.forget B)
  apply Adhesive.mk (hasPullback_of_mono_left := H₁) (hasPushout_of_mono_left := H₂)
  intro W X Y Z f g h i hf H
  haveI : Mono ((Over.forget B).map f) := inferInstance
  haveI : HasPushout ((Over.forget B).map f) ((Over.forget B).map g) := inferInstance
  haveI : HasColimit (span f g ⋙ Over.forget B) :=
    hasColimit_of_iso (spanCompIso (Over.forget B) f g)
  haveI : PreservesColimit (span f g) (Over.forget B) := inferInstance
  have Hmap : IsPushout ((Over.forget B).map f) ((Over.forget B).map g)
      ((Over.forget B).map h) ((Over.forget B).map i) := H.map (Over.forget B)
  intro W' X' Y' Z' f' g' h' i' αW αX αY αZ hf' hg' sq_h sq_i cs
  haveI : Mono f' := hf'.mono_fst_of_mono
  haveI : Mono ((Over.forget B).map f') := inferInstance
  haveI : HasPushout ((Over.forget B).map f') ((Over.forget B).map g') := inferInstance
  haveI : HasColimit (span f' g' ⋙ Over.forget B) :=
    hasColimit_of_iso (spanCompIso (Over.forget B) f' g')
  haveI : PreservesColimit (span f' g') (Over.forget B) := inferInstance
  refine (IsPushout.map_iff (Over.forget B) cs.w).symm.trans ?_
  refine ((Adhesive.van_kampen Hmap) ((Over.forget B).map f') ((Over.forget B).map g')
    ((Over.forget B).map h') ((Over.forget B).map i') ((Over.forget B).map αW)
    ((Over.forget B).map αX) ((Over.forget B).map αY) ((Over.forget B).map αZ)
    (hf'.map (Over.forget B)) (hg'.map (Over.forget B)) (sq_h.map (Over.forget B))
    (sq_i.map (Over.forget B)) (cs.map (Over.forget B))).trans ?_
  constructor
  · rintro ⟨hh, hi⟩
    exact ⟨(IsPullback.map_iff (Over.forget B) sq_h.w).1 hh,
      (IsPullback.map_iff (Over.forget B) sq_i.w).1 hi⟩
  · rintro ⟨hh, hi⟩
    exact ⟨(IsPullback.map_iff (Over.forget B) sq_h.w).2 hh,
      (IsPullback.map_iff (Over.forget B) sq_i.w).2 hi⟩

end CategoryTheory
