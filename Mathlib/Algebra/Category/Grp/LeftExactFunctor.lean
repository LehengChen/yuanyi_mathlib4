/-
Copyright (c) 2025 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.Algebra.Category.Grp.CartesianMonoidal
public import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup
public import Mathlib.CategoryTheory.Monoidal.Internal.Types.CommGrp_
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Preadditive.CommGrp_

/-!
# The forgetful functor `(C ⥤ₗ AddCommGroup) ⥤ (C ⥤ₗ Type v)` is an equivalence

This is true as long as `C` is additive.

Here, `C ⥤ₗ D` is the category of finite-limits-preserving functors from `C` to `D`.

To construct a functor from `C ⥤ₗ Type v` to `C ⥤ₗ AddCommGrpCat.{v}`, notice that a left-exact
functor `F : C ⥤ Type v` induces a functor `CommGrp C ⥤ CommGrp (Type v)`. But `CommGrp C` is
equivalent to `C`, and `CommGrp (Type v)` is equivalent to `AddCommGrpCat.{v}`, so we turn this
into a functor `C ⥤ AddCommGrpCat.{v}`. By construction, composing with the forgetful
functor recovers the functor we started with, so since the forgetful functor reflects finite
limits and `F` preserves finite limits, our constructed functor also preserves finite limits. It
can be shown that this construction gives a quasi-inverse to the whiskering operation
`(C ⥤ₗ AddCommGrpCat.{v}) ⥤ (C ⥤ₗ Type v)`.
-/

@[expose] public section

open CategoryTheory MonoidalCategory Limits


universe v v' u u'

namespace AddCommGrpCat

section

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]

namespace leftExactFunctorForgetEquivalence

attribute [local instance] hasFiniteProducts_of_hasFiniteBiproducts

-- This was deprecated on 2025-10-10 but is still used as a local instance here!
attribute [local instance] AddCommGrpCat.cartesianMonoidalCategoryAddCommGrp

set_option backward.privateInPublic true in
private noncomputable local instance : CartesianMonoidalCategory C := .ofHasFiniteProducts

set_option backward.privateInPublic true in
private noncomputable local instance : BraidedCategory C := .ofCartesianMonoidalCategory

/-- Implementation, see `leftExactFunctorForgetEquivalence`. -/
noncomputable def inverseAux : (C ⥤ₗ Type v) ⥤ C ⥤ AddCommGrpCat.{v} :=
  Functor.mapCommGrpFunctor ⋙
    (Functor.whiskeringLeft _ _ _).obj Preadditive.commGrpEquivalence.functor ⋙
      (Functor.whiskeringRight _ _ _).obj
        (commGrpTypeEquivalenceCommGrp.functor ⋙ commGroupAddCommGroupEquivalence.functor)

instance (F : C ⥤ₗ Type v) : PreservesFiniteLimits (inverseAux.obj F) where
  preservesFiniteLimits J _ _ :=
    have : PreservesLimitsOfShape J (inverseAux.obj F ⋙ forget AddCommGrpCat) :=
      inferInstanceAs (PreservesLimitsOfShape J F.1)
    preservesLimitsOfShape_of_reflects_of_preserves _ (forget AddCommGrpCat)

/-- Implementation, see `leftExactFunctorForgetEquivalence`. -/
noncomputable def inverse : (C ⥤ₗ Type v) ⥤ (C ⥤ₗ AddCommGrpCat.{v}) :=
  ObjectProperty.lift _ inverseAux (by simp only [leftExactFunctor_iff]; infer_instance)

open scoped MonObj

set_option backward.isDefEq.respectTransparency false in
attribute [-instance] Functor.LaxMonoidal.comp Functor.Monoidal.instComp in
/-- Implementation, see `leftExactFunctorForgetEquivalence`.
This is the complicated bit, where we show that forgetting the group structure in the image of
`F` and then reconstructing it recovers the group structure we started with. -/
noncomputable def unitIsoAux (F : C ⥤ AddCommGrpCat.{v}) [PreservesFiniteLimits F] (X : C) :
    letI : (F ⋙ forget AddCommGrpCat).Braided := .ofChosenFiniteProducts _
    commGrpTypeEquivalenceCommGrp.inverse.obj (AddCommGrpCat.toCommGrp.obj (F.obj X)) ≅
      (F ⋙ forget AddCommGrpCat).mapCommGrp.obj (Preadditive.commGrpEquivalence.functor.obj X) := by
  letI : (F ⋙ forget AddCommGrpCat).Braided := .ofChosenFiniteProducts _
  letI : F.Monoidal := .ofChosenFiniteProducts _
  refine CommGrp.mkIso Multiplicative.toAdd.toIso (by
    ext x
    change Multiplicative.toAdd (1 : Multiplicative (F.obj X)) =
      (Functor.LaxMonoidal.ε (F ⋙ forget AddCommGrpCat) ≫ (F ⋙ forget AddCommGrpCat).map η) x
    simp) ?_
  dsimp [-Functor.comp_map, -ConcreteCategory.forget_map_eq_coe, -forget_map]
  have : F.Additive := Functor.additive_of_preserves_binary_products _
  simp only [Category.id_comp]
  ext x
  change Multiplicative.toAdd (x.1 * x.2) =
    ((Functor.LaxMonoidal.μ (F ⋙ forget AddCommGrpCat)
        (Preadditive.commGrpEquivalence.functor.obj X).X
        (Preadditive.commGrpEquivalence.functor.obj X).X ≫
          (F ⋙ forget AddCommGrpCat).map μ) (x.1, x.2))
  rcases x with ⟨x, y⟩
  have hfst :
      (Hom.hom (F.map (SemiCartesianMonoidalCategory.fst X X)))
        ((ConcreteCategory.hom (Functor.LaxMonoidal.μ F X X)) (x, y)) = x := by
    change (Functor.LaxMonoidal.μ F X X ≫ F.map (SemiCartesianMonoidalCategory.fst X X))
      (x, y) = x
    rw [Functor.Monoidal.μ_fst]
    rfl
  have hsnd :
      (Hom.hom (F.map (SemiCartesianMonoidalCategory.snd X X)))
        ((ConcreteCategory.hom (Functor.LaxMonoidal.μ F X X)) (x, y)) = y := by
    change (Functor.LaxMonoidal.μ F X X ≫ F.map (SemiCartesianMonoidalCategory.snd X X))
      (x, y) = y
    rw [Functor.Monoidal.μ_snd]
    rfl
  have hμ :
      ((Functor.LaxMonoidal.μ (F ⋙ forget AddCommGrpCat)
          (Preadditive.commGrpEquivalence.functor.obj X).X
          (Preadditive.commGrpEquivalence.functor.obj X).X ≫
            (F ⋙ forget AddCommGrpCat).map μ) (x, y)) =
        (Hom.hom (F.map (SemiCartesianMonoidalCategory.fst X X)))
          ((ConcreteCategory.hom (Functor.LaxMonoidal.μ F X X)) (x, y)) +
        (Hom.hom (F.map (SemiCartesianMonoidalCategory.snd X X)))
          ((ConcreteCategory.hom (Functor.LaxMonoidal.μ F X X)) (x, y)) := by
    simp [Functor.comp_map, F.map_add, Functor.Monoidal.μ_comp F (forget AddCommGrpCat) X X]
  calc
    Multiplicative.toAdd (x * y)
        =
          (Hom.hom (F.map (SemiCartesianMonoidalCategory.fst X X)))
              ((ConcreteCategory.hom (Functor.LaxMonoidal.μ F X X)) (x, y)) +
            (Hom.hom (F.map (SemiCartesianMonoidalCategory.snd X X)))
              ((ConcreteCategory.hom (Functor.LaxMonoidal.μ F X X)) (x, y)) := by
      rw [hfst, hsnd]
      rfl
    _ = ((Functor.LaxMonoidal.μ (F ⋙ forget AddCommGrpCat)
        (Preadditive.commGrpEquivalence.functor.obj X).X
        (Preadditive.commGrpEquivalence.functor.obj X).X ≫
          (F ⋙ forget AddCommGrpCat).map μ) (x, y)) := by
      simpa using hμ.symm

/-- Implementation, see `leftExactFunctorForgetEquivalence`. -/
noncomputable def unitIso : 𝟭 (C ⥤ₗ AddCommGrpCat) ≅
    (LeftExactFunctor.whiskeringRight _ _ _).obj (LeftExactFunctor.of (forget _)) ⋙ inverse :=
  NatIso.ofComponents (fun F => InducedCategory.isoMk (NatIso.ofComponents (fun X =>
    commGroupAddCommGroupEquivalence.counitIso.app _ ≪≫
      (CommGrpCat.toAddCommGrp.mapIso (commGrpTypeEquivalenceCommGrp.counitIso.app
        (AddCommGrpCat.toCommGrp.obj (F.obj.obj X)))).symm ≪≫
      CommGrpCat.toAddCommGrp.mapIso
        (CommGrpTypeEquivalenceCommGrp.functor.mapIso (unitIsoAux F.obj X)))))

end leftExactFunctorForgetEquivalence

variable (C) in
/-- If `C` is an additive category, the forgetful functor `(C ⥤ₗ AddCommGroup) ⥤ (C ⥤ₗ Type v)` is
an equivalence. -/
noncomputable def leftExactFunctorForgetEquivalence : (C ⥤ₗ AddCommGrpCat.{v}) ≌ (C ⥤ₗ Type v) where
  functor := (LeftExactFunctor.whiskeringRight _ _ _).obj (LeftExactFunctor.of (forget _))
  inverse := leftExactFunctorForgetEquivalence.inverse
  unitIso := leftExactFunctorForgetEquivalence.unitIso
  counitIso := Iso.refl _

end

end AddCommGrpCat
