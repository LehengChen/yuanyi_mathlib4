/-
Copyright (c) 2021 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/
module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Ring.ULift

/-!
# The forgetful functor from (commutative) (semi-) rings preserves filtered colimits.

Forgetful functors from algebraic categories usually don't preserve colimits. However, they tend
to preserve _filtered_ colimits.

In this file, we start with a small filtered category `J` and a functor `F : J ⥤ SemiRingCat`.
We show that the colimit of `F ⋙ forget₂ SemiRingCat MonCat` (in `MonCat`)
carries the structure of a semiring, thereby showing that the forgetful functor
`forget₂ SemiRingCat MonCat` preserves filtered colimits.
In particular, this implies that `forget SemiRingCat` preserves filtered colimits.
Similarly for `CommSemiRingCat`, `RingCat` and `CommRingCat`.

-/

@[expose] public section


universe v u

noncomputable section

open CategoryTheory Limits

open IsFiltered renaming max → max' -- avoid name collision with `_root_.max`.

open AddMonCat.FilteredColimits (colimit_zero_eq colimit_add_mk_eq)

open MonCat.FilteredColimits (colimit_one_eq colimit_mul_mk_eq)

namespace SemiRingCat.FilteredColimits

section

-- We use parameters here, mainly so we can have the abbreviations `R` and `R.mk` below, without
-- passing around `F` all the time.
variable {J : Type v} [SmallCategory J] (F : J ⥤ SemiRingCat.{max v u})

-- This instance is needed below in `colimitSemiring`, during the verification of the
-- semiring axioms.
instance semiringObj (j : J) :
    Semiring (((F ⋙ forget₂ SemiRingCat.{max v u} MonCat) ⋙ forget MonCat).obj j) :=
  inferInstanceAs <| Semiring (F.obj j)

private lemma addMonCat_mk_eq_monCat_mk (j : J) (x : F.obj j) :
    AddMonCat.FilteredColimits.M.mk
      ((F ⋙ forget₂ SemiRingCat.{max v u} AddCommMonCat) ⋙ forget₂ _ _) ⟨j, x⟩ =
      MonCat.FilteredColimits.M.mk (F ⋙ forget₂ SemiRingCat.{max v u} MonCat) ⟨j, x⟩ := rfl

private lemma quot_mk_eq_monCat_mk (j : J) (x : F.obj j) :
    Quot.mk ((F ⋙ forget₂ SemiRingCat.{max v u} MonCat) ⋙ forget MonCat).ColimitTypeRel ⟨j, x⟩ =
      MonCat.FilteredColimits.M.mk (F ⋙ forget₂ SemiRingCat.{max v u} MonCat) ⟨j, x⟩ := rfl

private lemma quot_mk_eq_addMonCat_mk (j : J) (x : F.obj j) :
    Quot.mk ((F ⋙ forget₂ SemiRingCat.{max v u} MonCat) ⋙ forget MonCat).ColimitTypeRel ⟨j, x⟩ =
      AddMonCat.FilteredColimits.M.mk
        ((F ⋙ forget₂ SemiRingCat.{max v u} AddCommMonCat) ⋙ forget₂ _ _) ⟨j, x⟩ := rfl

variable [IsFiltered J]

/-- The colimit of `F ⋙ forget₂ SemiRingCat MonCat` in the category `MonCat`.
In the following, we will show that this has the structure of a semiring.
-/
abbrev R : MonCat.{max v u} :=
  MonCat.FilteredColimits.colimit.{v, u} (F ⋙ forget₂ SemiRingCat.{max v u} MonCat)

private lemma mul_eq_monCat_mul (x y : R.{v, u} F) :
    x * y = (x * y : MonCat.FilteredColimits.M (F ⋙ forget₂ SemiRingCat.{max v u} MonCat)) := rfl

private lemma addCommMonCat_zero_eq_addMonCat_zero :
    (0 : AddCommMonCat.FilteredColimits.M (F ⋙ forget₂ SemiRingCat.{max v u} AddCommMonCat)) =
      (0 : AddMonCat.FilteredColimits.M
        ((F ⋙ forget₂ SemiRingCat.{max v u} AddCommMonCat) ⋙ forget₂ _ _)) := rfl

set_option backward.isDefEq.respectTransparency false in
instance colimitSemiring : Semiring.{max v u} <| R.{v, u} F :=
  { (R.{v, u} F).str,
    AddCommMonCat.FilteredColimits.colimitAddCommMonoid.{v, u}
      (F ⋙ forget₂ SemiRingCat AddCommMonCat.{max v u}) with
    mul_zero := fun x => by
      refine Quot.inductionOn x ?_; clear x; intro x
      obtain ⟨j, x⟩ := x
      rw [addCommMonCat_zero_eq_addMonCat_zero, colimit_zero_eq _ j, addMonCat_mk_eq_monCat_mk,
        mul_eq_monCat_mul, quot_mk_eq_monCat_mk,
        colimit_mul_mk_eq _ ⟨j, _⟩ ⟨j, _⟩ j (𝟙 j) (𝟙 j)]
      rw [CategoryTheory.Functor.map_id]
      dsimp
      rw [mul_zero x]
    zero_mul := fun x => by
      refine Quot.inductionOn x ?_; clear x; intro x
      obtain ⟨j, x⟩ := x
      rw [addCommMonCat_zero_eq_addMonCat_zero, colimit_zero_eq _ j, addMonCat_mk_eq_monCat_mk,
        mul_eq_monCat_mul, quot_mk_eq_monCat_mk,
        colimit_mul_mk_eq _ ⟨j, _⟩ ⟨j, _⟩ j (𝟙 j) (𝟙 j)]
      rw [CategoryTheory.Functor.map_id]
      dsimp
      rw [zero_mul x]
    left_distrib := fun x y z => by
      refine Quot.induction_on₃ x y z ?_; clear x y z; intro x y z
      obtain ⟨j₁, x⟩ := x; obtain ⟨j₂, y⟩ := y; obtain ⟨j₃, z⟩ := z
      let k := IsFiltered.max₃ j₁ j₂ j₃
      let f := IsFiltered.firstToMax₃ j₁ j₂ j₃
      let g := IsFiltered.secondToMax₃ j₁ j₂ j₃
      let h := IsFiltered.thirdToMax₃ j₁ j₂ j₃
      rw [quot_mk_eq_addMonCat_mk, quot_mk_eq_addMonCat_mk, quot_mk_eq_addMonCat_mk]
      rw [colimit_add_mk_eq _ ⟨j₂, _⟩ ⟨j₃, _⟩ k g h]
      simp only [addMonCat_mk_eq_monCat_mk]
      rw [mul_eq_monCat_mul, colimit_mul_mk_eq _ ⟨j₁, _⟩ ⟨k, _⟩ k f (𝟙 k),
        mul_eq_monCat_mul, colimit_mul_mk_eq _ ⟨j₁, _⟩ ⟨j₂, _⟩ k f g,
        mul_eq_monCat_mul, colimit_mul_mk_eq _ ⟨j₁, _⟩ ⟨j₃, _⟩ k f h]
      rw (occs := .pos [2, 3]) [← addMonCat_mk_eq_monCat_mk]
      rw (occs := .pos [2]) [← addMonCat_mk_eq_monCat_mk]
      rw [colimit_add_mk_eq _ ⟨k, _⟩ ⟨k, _⟩ k (𝟙 k) (𝟙 k)]
      rw [addMonCat_mk_eq_monCat_mk]
      simp only [Functor.comp_obj, Functor.comp_map, forget₂_monCat_map,
        AddCommMonCat.coe_forget₂_obj, AddCommMonCat.hom_forget₂_map,
        forget₂_addCommMonCat_map, CategoryTheory.Functor.map_id, MonCat.hom_id,
        MonoidHom.id_apply, AddMonCat.hom_id, AddMonoidHom.id_apply]
      rw [left_distrib (F.map f x) (F.map g y) (F.map h z)]
    right_distrib := fun x y z => by
      refine Quot.induction_on₃ x y z ?_; clear x y z; intro x y z
      obtain ⟨j₁, x⟩ := x; obtain ⟨j₂, y⟩ := y; obtain ⟨j₃, z⟩ := z
      let k := IsFiltered.max₃ j₁ j₂ j₃
      let f := IsFiltered.firstToMax₃ j₁ j₂ j₃
      let g := IsFiltered.secondToMax₃ j₁ j₂ j₃
      let h := IsFiltered.thirdToMax₃ j₁ j₂ j₃
      rw [quot_mk_eq_addMonCat_mk, quot_mk_eq_addMonCat_mk, quot_mk_eq_addMonCat_mk]
      rw [colimit_add_mk_eq _ ⟨j₁, _⟩ ⟨j₂, _⟩ k f g]
      simp only [addMonCat_mk_eq_monCat_mk]
      rw [mul_eq_monCat_mul, colimit_mul_mk_eq _ ⟨k, _⟩ ⟨j₃, _⟩ k (𝟙 k) h,
        mul_eq_monCat_mul, colimit_mul_mk_eq _ ⟨j₁, _⟩ ⟨j₃, _⟩ k f h,
        mul_eq_monCat_mul, colimit_mul_mk_eq _ ⟨j₂, _⟩ ⟨j₃, _⟩ k g h]
      rw (occs := .pos [2, 3]) [← addMonCat_mk_eq_monCat_mk]
      rw (occs := .pos [2]) [← addMonCat_mk_eq_monCat_mk]
      rw [colimit_add_mk_eq _ ⟨k, _⟩ ⟨k, _⟩ k (𝟙 k) (𝟙 k)]
      rw [addMonCat_mk_eq_monCat_mk]
      simp only [Functor.comp_obj, Functor.comp_map, forget₂_monCat_map,
        AddCommMonCat.coe_forget₂_obj, AddCommMonCat.hom_forget₂_map,
        forget₂_addCommMonCat_map, CategoryTheory.Functor.map_id, MonCat.hom_id,
        MonoidHom.id_apply, AddMonCat.hom_id, AddMonoidHom.id_apply]
      rw [right_distrib (F.map f x) (F.map g y) (F.map h z)] }

/-- The bundled semiring giving the filtered colimit of a diagram. -/
def colimit : SemiRingCat.{max v u} :=
  SemiRingCat.of <| R.{v, u} F

/-- The cocone over the proposed colimit semiring. -/
def colimitCocone : Cocone F where
  pt := colimit.{v, u} F
  ι :=
    { app := fun j => ofHom
        { ((MonCat.FilteredColimits.colimitCocone
            (F ⋙ forget₂ SemiRingCat.{max v u} MonCat)).ι.app j).hom,
            ((AddCommMonCat.FilteredColimits.colimitCocone
              (F ⋙ forget₂ SemiRingCat.{max v u} AddCommMonCat)).ι.app j).hom with }
      naturality := fun {_ _} f => hom_ext <|
        RingHom.coe_inj ((Types.TypeMax.colimitCocone (F ⋙ forget SemiRingCat)).ι.naturality f) }

namespace colimitCoconeIsColimit

variable {F} (t : Cocone F)

/-- Auxiliary definition for `colimitCoconeIsColimit`. -/
def descAddMonoidHom : R F →+ t.1 :=
  ((AddCommMonCat.FilteredColimits.colimitCoconeIsColimit.{v, u}
    (F ⋙ forget₂ SemiRingCat AddCommMonCat)).desc
      ((forget₂ SemiRingCat AddCommMonCat).mapCocone t)).hom

lemma descAddMonoidHom_quotMk {j : J} (x : F.obj j) :
    descAddMonoidHom t (Quot.mk _ ⟨j, x⟩) = t.ι.app j x :=
  congr_fun ((forget AddCommMonCat).congr_map
    ((AddCommMonCat.FilteredColimits.colimitCoconeIsColimit.{v, u}
      (F ⋙ forget₂ SemiRingCat AddCommMonCat)).fac
        ((forget₂ SemiRingCat AddCommMonCat).mapCocone t) j)) x

/-- Auxiliary definition for `colimitCoconeIsColimit`. -/
def descMonoidHom : R F →* t.1 :=
  ((MonCat.FilteredColimits.colimitCoconeIsColimit.{v, u}
    (F ⋙ forget₂ _ _)).desc ((forget₂ _ _).mapCocone t)).hom

lemma descMonoidHom_quotMk {j : J} (x : F.obj j) :
    descMonoidHom t (Quot.mk _ ⟨j, x⟩) = t.ι.app j x :=
  congr_fun ((forget MonCat).congr_map
    ((MonCat.FilteredColimits.colimitCoconeIsColimit.{v, u}
      (F ⋙ forget₂ _ _)).fac ((forget₂ _ _).mapCocone t) j)) x

lemma descMonoidHom_apply_eq (x : R F) :
    descMonoidHom t x = descAddMonoidHom t x := by
  obtain ⟨j, x⟩ := x
  rw [descMonoidHom_quotMk t x, descAddMonoidHom_quotMk t x]

end colimitCoconeIsColimit

open colimitCoconeIsColimit in
/-- The proposed colimit cocone is a colimit in `SemiRingCat`. -/
def colimitCoconeIsColimit : IsColimit <| colimitCocone.{v, u} F where
  desc t := ofHom
    { descAddMonoidHom t with
      map_one' := (descMonoidHom_apply_eq t 1).symm.trans (by simp)
      map_mul' x y := by
        change descAddMonoidHom t (x * y) =
          descAddMonoidHom t x * descAddMonoidHom t y
        simp [← descMonoidHom_apply_eq] }
  fac t j := by ext x; exact descAddMonoidHom_quotMk t x
  uniq t m hm := by
    ext ⟨j, x⟩
    exact (congr_fun ((forget SemiRingCat).congr_map (hm j)) x).trans
      (descAddMonoidHom_quotMk t x).symm

instance forget₂Mon_preservesFilteredColimits :
    PreservesFilteredColimits (forget₂ SemiRingCat MonCat.{u}) where
  preserves_filtered_colimits {J hJ1 _} :=
    letI : Category J := hJ1
    { preservesColimit := fun {F} =>
        preservesColimit_of_preserves_colimit_cocone (colimitCoconeIsColimit.{u, u} F)
          (MonCat.FilteredColimits.colimitCoconeIsColimit (F ⋙ forget₂ SemiRingCat MonCat.{u})) }

instance forget_preservesFilteredColimits : PreservesFilteredColimits (forget SemiRingCat.{u}) :=
  Limits.comp_preservesFilteredColimits (forget₂ SemiRingCat MonCat) (forget MonCat.{u})

end

end SemiRingCat.FilteredColimits

namespace CommSemiRingCat.FilteredColimits

section

-- We use parameters here, mainly so we can have the abbreviation `R` below, without
-- passing around `F` all the time.
variable {J : Type v} [SmallCategory J] [IsFiltered J] (F : J ⥤ CommSemiRingCat.{max v u})

/-- The colimit of `F ⋙ forget₂ CommSemiRingCat SemiRingCat` in the category `SemiRingCat`.
In the following, we will show that this has the structure of a _commutative_ semiring.
-/
abbrev R : SemiRingCat.{max v u} :=
  SemiRingCat.FilteredColimits.colimit (F ⋙ forget₂ CommSemiRingCat SemiRingCat.{max v u})

instance colimitCommSemiring : CommSemiring.{max v u} <| R.{v, u} F :=
  { (R F).semiring,
    CommMonCat.FilteredColimits.colimitCommMonoid
      (F ⋙ forget₂ CommSemiRingCat CommMonCat.{max v u}) with }

/-- The bundled commutative semiring giving the filtered colimit of a diagram. -/
def colimit : CommSemiRingCat.{max v u} :=
  CommSemiRingCat.of <| R.{v, u} F

/-- The cocone over the proposed colimit commutative semiring. -/
def colimitCocone : Cocone F where
  pt := colimit.{v, u} F
  ι :=
    { app := fun X ↦ ofHom <| ((SemiRingCat.FilteredColimits.colimitCocone
          (F ⋙ forget₂ CommSemiRingCat SemiRingCat.{max v u})).ι.app X).hom
      naturality := fun _ _ f ↦ hom_ext <|
        RingHom.coe_inj ((Types.TypeMax.colimitCocone
          (F ⋙ forget CommSemiRingCat)).ι.naturality f) }


/-- The proposed colimit cocone is a colimit in `CommSemiRingCat`. -/
def colimitCoconeIsColimit : IsColimit <| colimitCocone.{v, u} F :=
  isColimitOfReflects (forget₂ _ SemiRingCat)
    (SemiRingCat.FilteredColimits.colimitCoconeIsColimit
      (F ⋙ forget₂ CommSemiRingCat SemiRingCat))

instance forget₂SemiRing_preservesFilteredColimits :
    PreservesFilteredColimits (forget₂ CommSemiRingCat SemiRingCat.{u}) where
  preserves_filtered_colimits {J hJ1 _} :=
    letI : Category J := hJ1
    { preservesColimit := fun {F} =>
        preservesColimit_of_preserves_colimit_cocone (colimitCoconeIsColimit.{u, u} F)
          (SemiRingCat.FilteredColimits.colimitCoconeIsColimit
            (F ⋙ forget₂ CommSemiRingCat SemiRingCat.{u})) }

instance forget_preservesFilteredColimits :
    PreservesFilteredColimits (forget CommSemiRingCat.{u}) :=
  Limits.comp_preservesFilteredColimits (forget₂ CommSemiRingCat SemiRingCat)
    (forget SemiRingCat.{u})

end

end CommSemiRingCat.FilteredColimits

namespace RingCat.FilteredColimits

section

-- We use parameters here, mainly so we can have the abbreviation `R` below, without
-- passing around `F` all the time.
variable {J : Type v} [SmallCategory J] [IsFiltered J] (F : J ⥤ RingCat.{max v u})

/-- The colimit of `F ⋙ forget₂ RingCat SemiRingCat` in the category `SemiRingCat`.
In the following, we will show that this has the structure of a ring.
-/
abbrev R : SemiRingCat.{max v u} :=
  SemiRingCat.FilteredColimits.colimit.{v, u} (F ⋙ forget₂ RingCat SemiRingCat.{max v u})

instance colimitRing : Ring.{max v u} <| R.{v, u} F :=
  { (R F).semiring,
    AddCommGrpCat.FilteredColimits.colimitAddCommGroup.{v, u}
      (F ⋙ forget₂ RingCat AddCommGrpCat.{max v u}) with }

/-- The bundled ring giving the filtered colimit of a diagram. -/
def colimit : RingCat.{max v u} :=
  RingCat.of <| R.{v, u} F

/-- The cocone over the proposed colimit ring. -/
def colimitCocone : Cocone F where
  pt := colimit.{v, u} F
  ι :=
    { app := fun X ↦ ofHom <| ((SemiRingCat.FilteredColimits.colimitCocone
          (F ⋙ forget₂ RingCat SemiRingCat.{max v u})).ι.app X).hom
      naturality := fun _ _ f ↦ hom_ext <|
        RingHom.coe_inj ((Types.TypeMax.colimitCocone (F ⋙ forget RingCat)).ι.naturality f) }

/-- The proposed colimit cocone is a colimit in `Ring`. -/
def colimitCoconeIsColimit : IsColimit <| colimitCocone.{v, u} F :=
  isColimitOfReflects (forget₂ _ _)
    (SemiRingCat.FilteredColimits.colimitCoconeIsColimit
      (F ⋙ forget₂ RingCat SemiRingCat))

instance forget₂SemiRing_preservesFilteredColimits :
    PreservesFilteredColimits (forget₂ RingCat SemiRingCat.{u}) where
  preserves_filtered_colimits {J hJ1 _} :=
    letI : Category J := hJ1
    { preservesColimit := fun {F} =>
        preservesColimit_of_preserves_colimit_cocone (colimitCoconeIsColimit.{u, u} F)
          (SemiRingCat.FilteredColimits.colimitCoconeIsColimit
            (F ⋙ forget₂ RingCat SemiRingCat.{u})) }

instance : Limits.PreservesFilteredColimits (forget₂ RingCat AddCommGrpCat.{u}) where
  preserves_filtered_colimits _ :=
    { preservesColimit := fun {F} =>
        Limits.preservesColimit_of_preserves_colimit_cocone
          (RingCat.FilteredColimits.colimitCoconeIsColimit.{u, u} F)
          (AddCommGrpCat.FilteredColimits.colimitCoconeIsColimit
            (F ⋙ forget₂ RingCat AddCommGrpCat.{u})) }

instance forget_preservesFilteredColimits : PreservesFilteredColimits (forget RingCat.{u}) :=
  Limits.comp_preservesFilteredColimits (forget₂ RingCat SemiRingCat) (forget SemiRingCat.{u})

end

end RingCat.FilteredColimits

namespace CommRingCat.FilteredColimits

section

-- We use parameters here, mainly so we can have the abbreviation `R` below, without
-- passing around `F` all the time.
variable {J : Type v} [SmallCategory J] [IsFiltered J] (F : J ⥤ CommRingCat.{max v u})

/-- The colimit of `F ⋙ forget₂ CommRingCat RingCat` in the category `RingCat`.
In the following, we will show that this has the structure of a _commutative_ ring.
-/
abbrev R : RingCat.{max v u} :=
  RingCat.FilteredColimits.colimit.{v, u} (F ⋙ forget₂ CommRingCat RingCat.{max v u})

instance colimitCommRing : CommRing.{max v u} <| R.{v, u} F :=
  { (R.{v, u} F).ring,
    CommSemiRingCat.FilteredColimits.colimitCommSemiring
      (F ⋙ forget₂ CommRingCat CommSemiRingCat.{max v u}) with }

/-- The bundled commutative ring giving the filtered colimit of a diagram. -/
def colimit : CommRingCat.{max v u} :=
  CommRingCat.of <| R.{v, u} F

/-- The cocone over the proposed colimit commutative ring. -/
def colimitCocone : Cocone F where
  pt := colimit.{v, u} F
  ι :=
    { app := fun X ↦ ofHom <| ((RingCat.FilteredColimits.colimitCocone
          (F ⋙ forget₂ CommRingCat RingCat.{max v u})).ι.app X).hom
      naturality := fun _ _ f ↦ hom_ext <|
        RingHom.coe_inj ((Types.TypeMax.colimitCocone (F ⋙ forget CommRingCat)).ι.naturality f) }

/-- The proposed colimit cocone is a colimit in `CommRingCat`. -/
def colimitCoconeIsColimit : IsColimit <| colimitCocone.{v, u} F :=
  isColimitOfReflects (forget₂ _ _)
    (RingCat.FilteredColimits.colimitCoconeIsColimit
      (F ⋙ forget₂ CommRingCat RingCat))

instance forget₂Ring_preservesFilteredColimits :
    PreservesFilteredColimits (forget₂ CommRingCat RingCat.{u}) where
  preserves_filtered_colimits {J hJ1 _} :=
    letI : Category J := hJ1
    { preservesColimit := fun {F} =>
        preservesColimit_of_preserves_colimit_cocone (colimitCoconeIsColimit.{u, u} F)
          (RingCat.FilteredColimits.colimitCoconeIsColimit (F ⋙ forget₂ CommRingCat RingCat.{u})) }

instance forget_preservesFilteredColimits : PreservesFilteredColimits (forget CommRingCat.{u}) :=
  Limits.comp_preservesFilteredColimits (forget₂ CommRingCat RingCat) (forget RingCat.{u})

omit [IsFiltered J] in
protected lemma nontrivial {F : J ⥤ CommRingCat.{v}} [IsFilteredOrEmpty J]
    [∀ i, Nontrivial (F.obj i)] {c : Cocone F} (hc : IsColimit c) : Nontrivial c.pt := by
  classical
  cases isEmpty_or_nonempty J
  · exact ((isColimitEquivIsInitialOfIsEmpty _ _ hc).to (.of (ULift ℤ))).hom.domain_nontrivial
  have i := ‹Nonempty J›.some
  refine ⟨c.ι.app i 0, c.ι.app i 1, fun h ↦ ?_⟩
  have : IsFiltered J := ⟨⟩
  obtain ⟨k, f, e⟩ :=
    (Types.FilteredColimit.isColimit_eq_iff' (isColimitOfPreserves (forget _) hc) _ _).mp h
  exact zero_ne_one (((F.map f).hom.map_zero.symm.trans e).trans (F.map f).hom.map_one)

omit [IsFiltered J] in
instance {F : J ⥤ CommRingCat.{v}} [IsFilteredOrEmpty J]
    [HasColimit F] [∀ i, Nontrivial (F.obj i)] : Nontrivial ↑(Limits.colimit F) :=
  FilteredColimits.nontrivial (getColimitCocone F).2

end

end CommRingCat.FilteredColimits
