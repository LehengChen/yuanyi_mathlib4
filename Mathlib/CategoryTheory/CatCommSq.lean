/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Equivalence

/-!
# 2-commutative squares of functors

Similarly to `Mathlib/CategoryTheory/CommSq.lean`, which defines the notion of commutative squares,
this file introduces the notion of 2-commutative squares of functors.

If `T : C₁ ⥤ C₂`, `L : C₁ ⥤ C₃`, `R : C₂ ⥤ C₄`, `B : C₃ ⥤ C₄` are functors,
then `[CatCommSq T L R B]` contains the datum of an isomorphism `T ⋙ R ≅ L ⋙ B`.

Future work: using this notion in the development of the localization of categories
(e.g. localization of adjunctions).

-/

@[expose] public section

namespace CategoryTheory

open Category Functor

variable {C₁ C₂ C₃ C₄ C₅ C₆ : Type*} [Category* C₁] [Category* C₂] [Category* C₃] [Category* C₄]
  [Category* C₅] [Category* C₆]

/-- `CatCommSq T L R B` expresses that there is a 2-commutative square of functors, where
the functors `T`, `L`, `R` and `B` are respectively the left, top, right and bottom functors
of the square. -/
@[ext]
class CatCommSq (T : C₁ ⥤ C₂) (L : C₁ ⥤ C₃) (R : C₂ ⥤ C₄) (B : C₃ ⥤ C₄) where
  /-- Assuming `[CatCommSq T L R B]`, `iso T L R B` is the isomorphism `T ⋙ R ≅ L ⋙ B`
  given by the 2-commutative square. -/
  iso (T) (L) (R) (B) : T ⋙ R ≅ L ⋙ B

variable (T : C₁ ⥤ C₂) (L : C₁ ⥤ C₃) (R : C₂ ⥤ C₄) (B : C₃ ⥤ C₄)

namespace CatCommSq

/-- The vertical identity `CatCommSq` -/
@[instance_reducible, simps!]
def vId : CatCommSq T (𝟭 C₁) (𝟭 C₂) T where
  iso := (Functor.leftUnitor _) ≪≫ (Functor.rightUnitor _).symm

/-- The horizontal identity `CatCommSq` -/
@[simps!, implicit_reducible]
def hId : CatCommSq (𝟭 C₁) L L (𝟭 C₃) where
  iso := (Functor.rightUnitor _) ≪≫ (Functor.leftUnitor _).symm

@[reassoc (attr := simp)]
lemma iso_hom_naturality [h : CatCommSq T L R B] {x y : C₁} (f : x ⟶ y) :
    R.map (T.map f) ≫ (iso T L R B).hom.app y = (iso T L R B).hom.app x ≫ B.map (L.map f) :=
  (iso T L R B).hom.naturality f

@[reassoc (attr := simp)]
lemma iso_inv_naturality [h : CatCommSq T L R B] {x y : C₁} (f : x ⟶ y) :
    B.map (L.map f) ≫ (iso T L R B).inv.app y = (iso T L R B).inv.app x ≫ R.map (T.map f) :=
  (iso T L R B).inv.naturality f

/-- Horizontal composition of 2-commutative squares -/
@[simps!, implicit_reducible]
def hComp (T₁ : C₁ ⥤ C₂) (T₂ : C₂ ⥤ C₃) (V₁ : C₁ ⥤ C₄) (V₂ : C₂ ⥤ C₅) (V₃ : C₃ ⥤ C₆)
    (B₁ : C₄ ⥤ C₅) (B₂ : C₅ ⥤ C₆) [CatCommSq T₁ V₁ V₂ B₁] [CatCommSq T₂ V₂ V₃ B₂] :
    CatCommSq (T₁ ⋙ T₂) V₁ V₃ (B₁ ⋙ B₂) where
  iso := associator _ _ _ ≪≫ isoWhiskerLeft T₁ (iso T₂ V₂ V₃ B₂) ≪≫
    (associator _ _ _).symm ≪≫ isoWhiskerRight (iso T₁ V₁ V₂ B₁) B₂ ≪≫
    associator _ _ _

/-- A variant of `hComp` where both squares can be explicitly provided. -/
abbrev hComp' {T₁ : C₁ ⥤ C₂} {T₂ : C₂ ⥤ C₃} {V₁ : C₁ ⥤ C₄} {V₂ : C₂ ⥤ C₅} {V₃ : C₃ ⥤ C₆}
    {B₁ : C₄ ⥤ C₅} {B₂ : C₅ ⥤ C₆} (S₁ : CatCommSq T₁ V₁ V₂ B₁) (S₂ : CatCommSq T₂ V₂ V₃ B₂) :
    CatCommSq (T₁ ⋙ T₂) V₁ V₃ (B₁ ⋙ B₂) :=
  letI := S₁
  letI := S₂
  hComp _ _ _ V₂ _ _ _

/-- Vertical composition of 2-commutative squares -/
@[simps!, implicit_reducible]
def vComp (L₁ : C₁ ⥤ C₂) (L₂ : C₂ ⥤ C₃) (H₁ : C₁ ⥤ C₄) (H₂ : C₂ ⥤ C₅) (H₃ : C₃ ⥤ C₆)
    (R₁ : C₄ ⥤ C₅) (R₂ : C₅ ⥤ C₆) [CatCommSq H₁ L₁ R₁ H₂] [CatCommSq H₂ L₂ R₂ H₃] :
    CatCommSq H₁ (L₁ ⋙ L₂) (R₁ ⋙ R₂) H₃ where
  iso := (associator _ _ _).symm ≪≫ isoWhiskerRight (iso H₁ L₁ R₁ H₂) R₂ ≪≫
      associator _ _ _ ≪≫ isoWhiskerLeft L₁ (iso H₂ L₂ R₂ H₃) ≪≫
      (associator _ _ _).symm

/-- A variant of `vComp` where both squares can be explicitly provided. -/
abbrev vComp' {L₁ : C₁ ⥤ C₂} {L₂ : C₂ ⥤ C₃} {H₁ : C₁ ⥤ C₄} {H₂ : C₂ ⥤ C₅} {H₃ : C₃ ⥤ C₆}
    {R₁ : C₄ ⥤ C₅} {R₂ : C₅ ⥤ C₆} (S₁ : CatCommSq H₁ L₁ R₁ H₂) (S₂ : CatCommSq H₂ L₂ R₂ H₃) :
    CatCommSq H₁ (L₁ ⋙ L₂) (R₁ ⋙ R₂) H₃ :=
  letI := S₁
  letI := S₂
  vComp _ _ _ H₂ _ _ _

section

variable (T : C₁ ≌ C₂) (L : C₁ ⥤ C₃) (R : C₂ ⥤ C₄) (B : C₃ ≌ C₄)

/-- Horizontal inverse of a 2-commutative square -/
@[simps!, implicit_reducible]
def hInv (_ : CatCommSq T.functor L R B.functor) : CatCommSq T.inverse R L B.inverse where
  iso := (associator _ _ _ ≪≫ (iso T.functor L R B.functor).symm.inverseCompIso).isoCompInverse

set_option backward.isDefEq.respectTransparency false in
lemma hInv_hInv (h : CatCommSq T.functor L R B.functor) :
    hInv T.symm R L B.symm (hInv T L R B h) = h := by
  cases h with
  | mk iso =>
      apply CatCommSq.ext
      dsimp [CatCommSq.iso]
      apply Iso.ext
      ext X
      simp
      erw [← iso.hom.naturality (T.unitIso.inv.app X)]
      rw [Functor.comp_map, ← assoc, ← R.map_comp, T.counitIso_functor_comp]
      simp

/-- In a square of categories, when the top and bottom functors are part
of equivalence of categories, it is equivalent to show 2-commutativity for
the functors of these equivalences or for their inverses. -/
def hInvEquiv : CatCommSq T.functor L R B.functor ≃ CatCommSq T.inverse R L B.inverse where
  toFun := hInv T L R B
  invFun := hInv T.symm R L B.symm
  left_inv := hInv_hInv T L R B
  right_inv := hInv_hInv T.symm R L B.symm

end

section

variable (T : C₁ ⥤ C₂) (L : C₁ ≌ C₃) (R : C₂ ≌ C₄) (B : C₃ ⥤ C₄)

/-- Vertical inverse of a 2-commutative square -/
@[simps!, implicit_reducible]
def vInv (_ : CatCommSq T L.functor R.functor B) : CatCommSq B L.inverse R.inverse T where
  iso := (associator _ _ _ ≪≫ (iso T L.functor R.functor B).symm.compInverseIso).isoInverseComp

set_option backward.isDefEq.respectTransparency false in
lemma vInv_vInv (h : CatCommSq T L.functor R.functor B) :
    vInv B L.symm R.symm T (vInv T L R B h) = h := by
  cases h with
  | mk iso =>
      apply CatCommSq.ext
      dsimp [CatCommSq.iso]
      apply Iso.ext
      ext X
      simp
      rw [L.counit_app_functor]
      erw [← iso.hom.naturality (L.unitIso.inv.app X)]
      rw [Functor.comp_map, ← assoc, ← R.functor.map_comp]
      simp [← T.map_comp, L.unitIso_hom_inv_id_app]

/-- In a square of categories, when the left and right functors are part
of equivalence of categories, it is equivalent to show 2-commutativity for
the functors of these equivalences or for their inverses. -/
def vInvEquiv : CatCommSq T L.functor R.functor B ≃ CatCommSq B L.inverse R.inverse T where
  toFun := vInv T L R B
  invFun := vInv B L.symm R.symm T
  left_inv := vInv_vInv T L R B
  right_inv := vInv_vInv B L.symm R.symm T

end

end CatCommSq

end CategoryTheory
