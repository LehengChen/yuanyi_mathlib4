/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.AlgCat.Basic
public import Mathlib.CategoryTheory.Monoidal.Mon_
public import Mathlib.Tactic.SuppressCompilation

/-!
# `Mon (ModuleCat R) ≌ AlgCat R`

The category of internal monoid objects in `ModuleCat R`
is equivalent to the category of "native" bundled `R`-algebras.

Moreover, this equivalence is compatible with the forgetful functors to `ModuleCat R`.
-/

@[expose] public section

suppress_compilation


universe v u

open CategoryTheory

open LinearMap MonObj

open scoped TensorProduct

attribute [local ext] TensorProduct.ext

namespace ModuleCat

variable {R : Type u} [CommRing R]

namespace MonModuleEquivalenceAlgebra

/-- The ring structure on a monoid object.
This instance is dangerous as it doesn't round trip from a ring to a monoid object and then back
to a ring, since the `npow` field is lost in the middle. Therefore, it is scoped. -/
@[implicit_reducible]
def MonObj.toRing (A : ModuleCat.{u} R) [MonObj A] : Ring A :=
  { (inferInstance : AddCommGroup A) with
    one := η[A] (1 : R)
    mul := fun x y => μ[A] (x ⊗ₜ y)
    one_mul := fun x => by
      convert LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp (one_mul A)) ((1 : R) ⊗ₜ x)
      rw [MonoidalCategory.leftUnitor_hom_apply, one_smul]
    mul_one := fun x => by
      convert LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp (mul_one A)) (x ⊗ₜ (1 : R))
      rw [MonoidalCategory.rightUnitor_hom_apply, one_smul]
    mul_assoc := fun x y z => by
      convert LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp (mul_assoc A)) (x ⊗ₜ y ⊗ₜ z)
    left_distrib := fun x y z => by
      convert μ[A].hom.map_add (x ⊗ₜ y) (x ⊗ₜ z)
      rw [← TensorProduct.tmul_add]
      rfl
    right_distrib := fun x y z => by
      convert μ[A].hom.map_add (x ⊗ₜ z) (y ⊗ₜ z)
      rw [← TensorProduct.add_tmul]
      rfl
    zero_mul := fun x => show μ[A] _ = 0 by
      rw [TensorProduct.zero_tmul, map_zero]
    mul_zero := fun x => show μ[A] _ = 0 by
      rw [TensorProduct.tmul_zero, map_zero] }

scoped[ModuleCat.MonModuleEquivalenceAlgebra] attribute [instance] MonObj.toRing

/-- The algebra structure on a monoid object.
This instance is dangerous as it doesn't round trip from a ring to a monoid object and then back
to a ring, since the `npow` field is lost in the middle. Therefore, it is scoped. -/
scoped instance Algebra_of_Mon_ (A : ModuleCat.{u} R) [MonObj A] : Algebra R A where
  algebraMap :=
  { η[A].hom with
    map_zero' := η[A].hom.map_zero
    map_one' := rfl
    map_mul' := fun x y => by
      have h := LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp (one_mul A).symm) (x ⊗ₜ η[A] y)
      rwa [MonoidalCategory.leftUnitor_hom_apply, ← η[A].hom.map_smul] at h }
  commutes' := fun r a => by
    dsimp
    have h₁ := LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp (one_mul A)) (r ⊗ₜ a)
    have h₂ := LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp (mul_one A)) (a ⊗ₜ r)
    exact h₁.trans h₂.symm
  smul_def' := fun r a =>
    (LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp (one_mul A)) (r ⊗ₜ a)).symm

@[simp]
theorem algebraMap (A : ModuleCat.{u} R) [MonObj A] (r : R) : algebraMap R A r = η[A] r :=
  rfl

private theorem tensorUnit_mk_apply (A : AlgCat.{u} R) (x : ModuleCat.of R A) :
    ((TensorProduct.mk R ↑(MonoidalCategoryStruct.tensorUnit (ModuleCat R)) ↑(ModuleCat.of R A))
        1) x =
      ((1 : R) ⊗ₜ[R] x) :=
  rfl

private theorem mk_tensorUnit_apply (A : AlgCat.{u} R) (x : ModuleCat.of R A) :
    ((TensorProduct.mk R ↑(ModuleCat.of R A) ↑(MonoidalCategoryStruct.tensorUnit (ModuleCat R)))
        x) 1 =
      (x ⊗ₜ[R] (1 : R)) :=
  rfl

private theorem mk_tensorObj_apply (A : AlgCat.{u} R) (x y z : ModuleCat.of R A) :
    ((TensorProduct.mk R ↑(MonoidalCategoryStruct.tensorObj (of R ↑A) (of R ↑A))
        ↑(ModuleCat.of R A)) (x ⊗ₜ[R] y)) z =
      ((x ⊗ₜ[R] y) ⊗ₜ[R] z) :=
  rfl

private theorem inverseObj_one_mul_apply (A : AlgCat.{u} R) (x : ModuleCat.of R A) :
    (Hom.hom (↟(LinearMap.mul' R ↑A)))
        ((Hom.hom (MonoidalCategoryStruct.whiskerRight (↟(Algebra.linearMap R ↑A))
            (of R ↑A))) (((TensorProduct.mk R ↑(MonoidalCategoryStruct.tensorUnit (ModuleCat R))
            ↑(ModuleCat.of R A)) 1) x)) =
      (Hom.hom (MonoidalCategoryStruct.leftUnitor (of R ↑A)).hom)
        (((TensorProduct.mk R ↑(MonoidalCategoryStruct.tensorUnit (ModuleCat R))
          ↑(ModuleCat.of R A)) 1) x) := by
  rw [tensorUnit_mk_apply]
  rw [MonoidalCategory.whiskerRight_apply, MonoidalCategory.leftUnitor_hom_apply]
  simp [LinearMap.mul'_apply, Algebra.smul_def]

private theorem inverseObj_mul_one_apply (A : AlgCat.{u} R) (x : ModuleCat.of R A) :
    (LinearMap.mul' R ↑A)
        ((Hom.hom (MonoidalCategoryStruct.whiskerLeft (of R ↑A) (↟(Algebra.linearMap R ↑A))))
          (((TensorProduct.mk R ↑(ModuleCat.of R A)
            ↑(MonoidalCategoryStruct.tensorUnit (ModuleCat R))) x) 1)) =
      (Hom.hom (MonoidalCategoryStruct.rightUnitor (of R ↑A)).hom)
        (((TensorProduct.mk R ↑(ModuleCat.of R A)
          ↑(MonoidalCategoryStruct.tensorUnit (ModuleCat R))) x) 1) := by
  rw [mk_tensorUnit_apply]
  rw [MonoidalCategory.whiskerLeft_apply, ModuleCat.MonoidalCategory.rightUnitor_hom_apply]
  simp [LinearMap.mul'_apply, Algebra.smul_def]

private theorem inverseObj_mul_assoc_apply (A : AlgCat.{u} R) (x y z : ModuleCat.of R A) :
    (Hom.hom (↟(LinearMap.mul' R ↑A)))
        ((Hom.hom (MonoidalCategoryStruct.whiskerRight (↟(LinearMap.mul' R ↑A))
            (of R ↑A))) (((TensorProduct.mk R
            ↑(MonoidalCategoryStruct.tensorObj (of R ↑A) (of R ↑A)) ↑(ModuleCat.of R A))
            (x ⊗ₜ[R] y)) z)) =
      (Hom.hom (↟(LinearMap.mul' R ↑A)))
        ((Hom.hom (MonoidalCategoryStruct.whiskerLeft (of R ↑A) (↟(LinearMap.mul' R ↑A))))
          ((Hom.hom (MonoidalCategoryStruct.associator (of R ↑A) (of R ↑A) (of R ↑A)).hom)
            (((TensorProduct.mk R ↑(MonoidalCategoryStruct.tensorObj (of R ↑A) (of R ↑A))
              ↑(ModuleCat.of R A)) (x ⊗ₜ[R] y)) z))) := by
  rw [mk_tensorObj_apply]
  rw [MonoidalCategory.whiskerRight_apply, MonoidalCategory.associator_hom_apply,
    MonoidalCategory.whiskerLeft_apply]
  simp [LinearMap.mul'_apply, _root_.mul_assoc]

/-- Converting a monoid object in `ModuleCat R` to a bundled algebra.
-/
@[simps!]
def functor : Mon (ModuleCat.{u} R) ⥤ AlgCat R where
  obj A := AlgCat.of R A.X
  map {_ _} f := AlgCat.ofHom
    { f.hom.hom.toAddMonoidHom with
      toFun := f.hom
      map_one' := LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp (IsMonHom.one_hom f.hom)) (1 : R)
      map_mul' := fun x y =>
        LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp (IsMonHom.mul_hom f.hom)) (x ⊗ₜ y)
      commutes' := fun r =>
        LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp (IsMonHom.one_hom f.hom)) r }

/-- Converting a bundled algebra to a monoid object in `ModuleCat R`.
-/
@[instance_reducible, simps]
def inverseObj (A : AlgCat.{u} R) : MonObj (ModuleCat.of R A) where
  one := ofHom <| Algebra.linearMap R A
  mul := ofHom <| LinearMap.mul' R A
  one_mul := by
    ext : 1
    -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): `ext` did not pick up `TensorProduct.ext`
    refine TensorProduct.ext <| LinearMap.ext_ring <| LinearMap.ext fun x => ?_
    rw [compr₂ₛₗ_apply, compr₂ₛₗ_apply, hom_comp, LinearMap.comp_apply]
    exact inverseObj_one_mul_apply A x
  mul_one := by
    ext : 1
    -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): `ext` did not pick up `TensorProduct.ext`
    refine TensorProduct.ext <| LinearMap.ext fun x => LinearMap.ext_ring ?_
    rw [compr₂ₛₗ_apply]
    simp only [hom_comp, hom_ofHom, LinearMap.comp_apply]
    exact inverseObj_mul_one_apply A x
  mul_assoc := by
    ext : 1
    -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): `ext` did not pick up `TensorProduct.ext`
    refine TensorProduct.ext <| TensorProduct.ext <| LinearMap.ext fun x => LinearMap.ext fun y =>
      LinearMap.ext fun z => ?_
    dsimp only [compr₂ₛₗ_apply, TensorProduct.mk_apply]
    rw [hom_comp, LinearMap.comp_apply, hom_comp, LinearMap.comp_apply, hom_comp,
        LinearMap.comp_apply]
    exact inverseObj_mul_assoc_apply A x y z

attribute [local instance] inverseObj

/-- Converting a bundled algebra to a monoid object in `ModuleCat R`.
-/
@[simps]
def inverse : AlgCat.{u} R ⥤ Mon (ModuleCat.{u} R) where
  obj A := { X := ModuleCat.of R A, mon := inverseObj A }
  map f :=
    { hom := ofHom <| f.hom.toLinearMap
      isMonHom_hom.one_hom := hom_ext <| LinearMap.ext f.hom.commutes
      isMonHom_hom.mul_hom := hom_ext <| TensorProduct.ext <| LinearMap.ext₂ <| map_mul f.hom }

end MonModuleEquivalenceAlgebra

open MonModuleEquivalenceAlgebra

/-- The category of internal monoid objects in `ModuleCat R`
is equivalent to the category of "native" bundled `R`-algebras.
-/
def monModuleEquivalenceAlgebra : Mon (ModuleCat.{u} R) ≌ AlgCat R where
  functor := functor
  inverse := inverse
  unitIso :=
    NatIso.ofComponents
      (fun A =>
        { hom.hom := ofHom
            { toFun := _root_.id
              map_add' _ _ := rfl
              map_smul' _ _ := rfl }
          hom.isMonHom_hom.mul_hom := by
            ext : 1
            -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): `ext` did not pick up `TensorProduct.ext`
            exact TensorProduct.ext rfl
          inv.hom := ofHom
            { toFun := _root_.id
              map_add' := fun _ _ => rfl
              map_smul' := fun _ _ => rfl }
          inv.isMonHom_hom.mul_hom := by
            ext : 1
            -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): `ext` did not pick up `TensorProduct.ext`
            refine TensorProduct.ext ?_
            rfl })
  counitIso :=
    NatIso.ofComponents
      (fun A =>
        { hom := AlgCat.ofHom
            { toFun := _root_.id
              map_zero' := rfl
              map_add' := fun _ _ => rfl
              map_one' := (algebraMap R A).map_one
              map_mul' := fun x y => @LinearMap.mul'_apply R _ _ _ _ _ _ x y
              commutes' := fun _ => rfl }
          inv := AlgCat.ofHom
            { toFun := _root_.id
              map_zero' := rfl
              map_add' := fun _ _ => rfl
              map_one' := (algebraMap R A).map_one.symm
              map_mul' := fun x y => (@LinearMap.mul'_apply R _ _ _ _ _ _ x y).symm
              commutes' := fun _ => rfl } })

/-- The equivalence `Mon (ModuleCat R) ≌ AlgCat R`
is naturally compatible with the forgetful functors to `ModuleCat R`.
-/
def monModuleEquivalenceAlgebraForget :
    MonModuleEquivalenceAlgebra.functor ⋙ forget₂ (AlgCat.{u} R) (ModuleCat.{u} R) ≅
      Mon.forget (ModuleCat.{u} R) :=
  NatIso.ofComponents
    (fun A =>
      { hom := ofHom
          { toFun := _root_.id
            map_add' := fun _ _ => rfl
            map_smul' := fun _ _ => rfl }
        inv := ofHom
          { toFun := _root_.id
            map_add' := fun _ _ => rfl
            map_smul' := fun _ _ => rfl } })

end ModuleCat
