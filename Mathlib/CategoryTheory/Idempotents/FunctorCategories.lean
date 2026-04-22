/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Idempotents.Karoubi

/-!
# Idempotent completeness and functor categories

In this file we define an instance `functor_category_isIdempotentComplete` expressing
that a functor category `J ⥤ C` is idempotent complete when the target category `C` is.

We also provide a fully faithful functor
`karoubiFunctorCategoryEmbedding : Karoubi (J ⥤ C) ⥤ (J ⥤ Karoubi C)` for all categories
`J` and `C`.

-/

@[expose] public section


open CategoryTheory

open CategoryTheory.Category

open CategoryTheory.Idempotents.Karoubi

open CategoryTheory.Limits

namespace CategoryTheory

namespace Idempotents

variable {J C : Type*} [Category* J] [Category* C] (P Q : Karoubi (J ⥤ C)) (f : P ⟶ Q) (X : J)

@[reassoc (attr := simp)]
theorem app_idem : P.p.app X ≫ P.p.app X = P.p.app X :=
  congr_app P.idem X

variable {P Q}

@[reassoc (attr := simp)]
theorem app_p_comp : P.p.app X ≫ f.f.app X = f.f.app X :=
  congr_app (p_comp f) X

@[reassoc (attr := simp)]
theorem app_comp_p : f.f.app X ≫ Q.p.app X = f.f.app X :=
  congr_app (comp_p f) X

@[reassoc]
theorem app_p_comm : P.p.app X ≫ f.f.app X = f.f.app X ≫ Q.p.app X :=
  congr_app (p_comm f) X

variable (J C)

set_option backward.isDefEq.respectTransparency false in
instance functor_category_isIdempotentComplete [IsIdempotentComplete C] :
    IsIdempotentComplete (J ⥤ C) := by
  rw [isIdempotentComplete_iff_hasEqualizer_of_id_and_idempotent]
  intro F p hp
  haveI : ∀ j : J, HasEqualizer (𝟙 (F.obj j)) (p.app j) := fun j =>
    (isIdempotentComplete_iff_hasEqualizer_of_id_and_idempotent C).mp inferInstance _ _
      (congr_app hp j)
  haveI : ∀ j : J, HasLimit ((parallelPair (𝟙 F) p).flip.obj j) := fun j => by
    exact hasLimit_of_iso (F := parallelPair (𝟙 (F.obj j)) (p.app j))
      (parallelPair.ext (Iso.refl _) (Iso.refl _) (by simp) (by simp))
  exact functorCategoryHasLimit (parallelPair (𝟙 F) p)
namespace KaroubiFunctorCategoryEmbedding

variable {J C}

/-- On objects, the functor which sends a formal direct factor `P` of a
functor `F : J ⥤ C` to the functor `J ⥤ Karoubi C` which sends `(j : J)` to
the corresponding direct factor of `F.obj j`. -/
@[simps]
def obj (P : Karoubi (J ⥤ C)) : J ⥤ Karoubi C where
  obj j := ⟨P.X.obj j, P.p.app j, congr_app P.idem j⟩
  map {j j'} φ :=
    { f := P.p.app j ≫ P.X.map φ
      comm := by
        simp only [NatTrans.naturality, assoc]
        have h := congr_app P.idem j
        rw [NatTrans.comp_app] at h
        rw [reassoc_of% h, reassoc_of% h] }

/-- Tautological action on maps of the functor `Karoubi (J ⥤ C) ⥤ (J ⥤ Karoubi C)`. -/
@[simps]
def map {P Q : Karoubi (J ⥤ C)} (f : P ⟶ Q) : obj P ⟶ obj Q where
  app j := ⟨f.f.app j, congr_app f.comm j⟩

end KaroubiFunctorCategoryEmbedding

/-- The tautological fully faithful functor `Karoubi (J ⥤ C) ⥤ (J ⥤ Karoubi C)`. -/
@[simps]
def karoubiFunctorCategoryEmbedding : Karoubi (J ⥤ C) ⥤ J ⥤ Karoubi C where
  obj := KaroubiFunctorCategoryEmbedding.obj
  map := KaroubiFunctorCategoryEmbedding.map

set_option backward.isDefEq.respectTransparency false in
instance : (karoubiFunctorCategoryEmbedding J C).Full where
  map_surjective {P Q} f :=
    ⟨{f :=
        { app := fun j => (f.app j).f
          naturality := fun j j' φ => by
            rw [← Karoubi.comp_p_assoc]
            have h := hom_ext_iff.mp (f.naturality φ)
            dsimp [karoubiFunctorCategoryEmbedding] at h
            simp only [assoc, h.symm, karoubiFunctorCategoryEmbedding_obj,
              KaroubiFunctorCategoryEmbedding.obj_obj_p]
            rw [← P.p.naturality_assoc]
            exact congrArg _ (p_comp (f.app _)).symm }
      comm := by
        ext j
        exact (f.app j).comm }, rfl⟩

instance : (karoubiFunctorCategoryEmbedding J C).Faithful where
  map_injective h := by
    ext j
    exact hom_ext_iff.mp (congr_app h j)

/-- The composition of `(J ⥤ C) ⥤ Karoubi (J ⥤ C)` and `Karoubi (J ⥤ C) ⥤ (J ⥤ Karoubi C)`
equals the functor `(J ⥤ C) ⥤ (J ⥤ Karoubi C)` given by the composition with
`toKaroubi C : C ⥤ Karoubi C`. -/
theorem toKaroubi_comp_karoubiFunctorCategoryEmbedding :
    toKaroubi _ ⋙ karoubiFunctorCategoryEmbedding J C =
      (Functor.whiskeringRight J _ _).obj (toKaroubi C) := by
  apply Functor.ext
  · intro X Y f
    ext j
    simp
  · intro X
    apply Functor.ext
    · intro j j' φ
      ext
      simp
    · intro j
      rfl

end Idempotents

end CategoryTheory
