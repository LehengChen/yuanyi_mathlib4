/-
Copyright (c) 2024 Nick Ward. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nick Ward
-/
module

public import Mathlib.CategoryTheory.Enriched.Ordinary.Basic

/-!
# Congruence of enriched homs

Recall that when `C` is both a category and a `V`-enriched category, we say it
is an `EnrichedOrdinaryCategory` if it comes equipped with a sufficiently
compatible equivalence between morphisms `X ⟶ Y` in `C` and morphisms
`𝟙_ V ⟶ (X ⟶[V] Y)` in `V`.

In such a `V`-enriched ordinary category `C`, isomorphisms in `C` induce
isomorphisms between hom-objects in `V`. We define this isomorphism in
`CategoryTheory.Iso.eHomCongr` and prove that it respects composition in `C`.

The treatment here parallels that for unenriched categories in
`Mathlib/CategoryTheory/HomCongr.lean` and that for sorts in
`Mathlib/Logic/Equiv/Defs.lean` (cf. `Equiv.arrowCongr`). Note, however, that
they construct equivalences between `Type`s and `Sort`s, respectively, while
in this file we construct isomorphisms between objects in `V`.
-/

@[expose] public section

universe v' v u u'

namespace CategoryTheory
namespace Iso

open Category MonoidalCategory

variable (V : Type u') [Category.{v'} V] [MonoidalCategory V]
  {C : Type u} [Category.{v} C] [EnrichedOrdinaryCategory V C]

/-- Given isomorphisms `α : X ≅ X₁` and `β : Y ≅ Y₁` in `C`, we can construct
an isomorphism between `V` objects `X ⟶[V] Y` and `X₁ ⟶[V] Y₁`. -/
@[simps]
def eHomCongr {X Y X₁ Y₁ : C} (α : X ≅ X₁) (β : Y ≅ Y₁) :
    (X ⟶[V] Y) ≅ (X₁ ⟶[V] Y₁) where
  hom := eHomWhiskerRight V α.inv Y ≫ eHomWhiskerLeft V X₁ β.hom
  inv := eHomWhiskerRight V α.hom Y₁ ≫ eHomWhiskerLeft V X β.inv
  hom_inv_id := by
    rw [← eHom_whisker_exchange]
    slice_lhs 2 3 => rw [← eHomWhiskerRight_comp]
    simp [← eHomWhiskerLeft_comp]
  inv_hom_id := by
    rw [← eHom_whisker_exchange]
    slice_lhs 2 3 => rw [← eHomWhiskerRight_comp]
    simp [← eHomWhiskerLeft_comp]

lemma eHomCongr_refl (X Y : C) :
    eHomCongr V (Iso.refl X) (Iso.refl Y) = Iso.refl (X ⟶[V] Y) := by aesop

lemma eHomCongr_trans {X₁ Y₁ X₂ Y₂ X₃ Y₃ : C} (α₁ : X₁ ≅ X₂) (β₁ : Y₁ ≅ Y₂)
    (α₂ : X₂ ≅ X₃) (β₂ : Y₂ ≅ Y₃) :
    eHomCongr V (α₁ ≪≫ α₂) (β₁ ≪≫ β₂) =
      eHomCongr V α₁ β₁ ≪≫ eHomCongr V α₂ β₂ := by
  ext; simp [eHom_whisker_exchange_assoc]

lemma eHomCongr_symm {X Y X₁ Y₁ : C} (α : X ≅ X₁) (β : Y ≅ Y₁) :
    (eHomCongr V α β).symm = eHomCongr V α.symm β.symm := rfl

/-- `eHomCongr` respects enriched composition. -/
@[reassoc]
lemma eHomCongr_comp {X Y Z X₁ Y₁ Z₁ : C} (α : X ≅ X₁) (β : Y ≅ Y₁)
    (γ : Z ≅ Z₁) :
    eComp V X Y Z ≫ (eHomCongr V α γ).hom =
      (eHomCongr V α β).hom ▷ _ ≫
        _ ◁ (eHomCongr V β γ).hom ≫ eComp V X₁ Y₁ Z₁ := by
  simp only [eHomCongr, assoc, MonoidalCategory.comp_whiskerRight,
    MonoidalCategory.whiskerLeft_comp]
  rw [eComp_eHomWhiskerRight_assoc]
  slice_rhs 4 5 => rw [← eComp_eHomWhiskerLeft]
  slice_rhs 2 4 => rw [eHom_whisker_cancel]

/-- The inverse map defined by `eHomCongr` respects enriched composition. -/
@[reassoc]
lemma eHomCongr_inv_comp {X Y Z X₁ Y₁ Z₁ : C} (α : X ≅ X₁) (β : Y ≅ Y₁)
    (γ : Z ≅ Z₁) :
    eComp V X₁ Y₁ Z₁ ≫ (eHomCongr V α γ).inv =
      (eHomCongr V α β).inv ▷ _ ≫
        _ ◁ (eHomCongr V β γ).inv ≫ eComp V X Y Z :=
  eHomCongr_comp V α.symm β.symm γ.symm

end Iso
end CategoryTheory
