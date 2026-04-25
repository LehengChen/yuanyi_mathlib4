/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Functor.EpiMono

/-!

# Adjunctions involving evaluation

We show that evaluation of functors has adjoints, given the existence of (co)products.

-/

@[expose] public section


namespace CategoryTheory

open CategoryTheory.Limits

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C] (D : Type u₂) [Category.{v₂} D]

noncomputable section

section

variable [∀ a b : C, HasCoproductsOfShape (a ⟶ b) D]

/-- The left adjoint of evaluation. -/
@[simps]
def evaluationLeftAdjoint (c : C) : D ⥤ C ⥤ D where
  obj d :=
    { obj := fun t => ∐ fun _ : c ⟶ t => d
      map := fun f => Sigma.desc fun g => (Sigma.ι fun _ => d) <| g ≫ f
      map_id := by
        intro X
        ext h
        rw [Sigma.ι_desc]
        simp only [Category.comp_id]
      map_comp := by
        intro X Y Z f g
        ext h
        rw [Sigma.ι_desc]
        rw [← Category.assoc]
        rw [← Category.assoc]
        rw [Sigma.ι_desc]
        rw [Sigma.ι_desc] }
  map {_ d₂} f :=
    { app := fun _ => Sigma.desc fun h => f ≫ Sigma.ι (fun _ => d₂) h
      naturality := by
        intro X Y g
        ext h
        simp only
        rw [← Category.assoc]
        rw [Sigma.ι_desc]
        rw [Sigma.ι_desc]
        rw [← Category.assoc]
        rw [Sigma.ι_desc]
        rw [Category.assoc]
        rw [Sigma.ι_desc] }
  map_id := by
    intro d
    ext t h
    rw [Sigma.ι_desc]
    simp only [NatTrans.id_app, Category.id_comp, Category.comp_id]
  map_comp := by
    intro X Y Z f g
    ext t h
    rw [Sigma.ι_desc]
    simp only [NatTrans.comp_app]
    rw [← Category.assoc]
    rw [Sigma.ι_desc]
    rw [Category.assoc]
    rw [Category.assoc]
    rw [Sigma.ι_desc]

private lemma evaluationLeftAdjoint_ι_naturality
    {F : C ⥤ D} {c x : C} {d : D}
    (f : (evaluationLeftAdjoint D c).obj d ⟶ F) (g : c ⟶ x) :
    Sigma.ι _ (𝟙 c) ≫ f.app c ≫ F.map g = Sigma.ι _ g ≫ f.app x := by
  conv_rhs =>
    rw [← Category.id_comp g]
    rw [← Sigma.ι_desc (fun h => Sigma.ι (fun _ => d) (h ≫ g)) (𝟙 c)]
    rw [← evaluationLeftAdjoint_obj_map]
    rw [Category.assoc]
    arg 2
    apply f.naturality
  rfl

private lemma evaluationLeftAdjoint_ι_desc_id
    {F : C ⥤ D} {c : C} {d : D} (f : d ⟶ F.obj c) :
    Sigma.ι _ (𝟙 c) ≫ Sigma.desc (fun h : c ⟶ c => f ≫ F.map h) = f := by
  rw [Sigma.ι_desc, Functor.map_id, Category.comp_id]

/-- The adjunction showing that evaluation is a right adjoint. -/
@[simps! unit_app counit_app_app]
def evaluationAdjunctionRight (c : C) : evaluationLeftAdjoint D c ⊣ (evaluation _ _).obj c :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun d F =>
        { toFun := fun f => Sigma.ι (fun _ => d) (𝟙 _) ≫ f.app c
          invFun := fun f =>
            { app := fun _ => Sigma.desc fun h => f ≫ F.map h
              naturality := by
                intro X Y k
                simp only [evaluationLeftAdjoint_obj_obj, evaluationLeftAdjoint_obj_map]
                ext h
                rw [← Category.assoc]
                rw [Sigma.ι_desc]
                rw [Sigma.ι_desc]
                rw [← Category.assoc]
                rw [Sigma.ι_desc]
                simp only [Functor.map_comp, Category.assoc]
                rfl }
          left_inv := by
            intro f
            ext x
            simp only [evaluationLeftAdjoint_obj_obj]
            ext g
            rw [Sigma.ι_desc]
            rw [Category.assoc]
            apply evaluationLeftAdjoint_ι_naturality (D := D) f g
          right_inv := by
            intro f
            simp only
            apply evaluationLeftAdjoint_ι_desc_id (D := D) (F := F) (c := c) (d := d) f }
      homEquiv_naturality_left_symm := by
        intro X' X Y f g
        ext x
        simp only [Equiv.coe_fn_symm_mk, NatTrans.comp_app, evaluationLeftAdjoint_obj_obj,
          evaluationLeftAdjoint_map_app]
        ext h
        rw [Sigma.ι_desc]
        rw [← Category.assoc]
        rw [Sigma.ι_desc]
        rw [Category.assoc]
        rw [Category.assoc]
        rw [Sigma.ι_desc]
      homEquiv_naturality_right := by
        intro X Y Y' f g
        simp only [Equiv.coe_fn_mk, NatTrans.comp_app, evaluation_obj_map, Category.assoc]
        rfl }

instance evaluationIsRightAdjoint (c : C) : ((evaluation _ D).obj c).IsRightAdjoint :=
  ⟨_, ⟨evaluationAdjunctionRight _ _⟩⟩

/-- See also the file `Mathlib/CategoryTheory/Limits/FunctorCategory/EpiMono.lean`
for a similar result under a `HasPullbacks` assumption. -/
theorem NatTrans.mono_iff_mono_app' {F G : C ⥤ D} (η : F ⟶ G) : Mono η ↔ ∀ c, Mono (η.app c) := by
  constructor
  · intro h c
    apply (inferInstance : Mono (((evaluation _ _).obj c).map η))
  · intro _
    apply NatTrans.mono_of_mono_app

end

section

variable [∀ a b : C, HasProductsOfShape (a ⟶ b) D]

/-- The right adjoint of evaluation. -/
@[simps]
def evaluationRightAdjoint (c : C) : D ⥤ C ⥤ D where
  obj d :=
    { obj := fun t => ∏ᶜ fun _ : t ⟶ c => d
      map := fun f => Pi.lift fun g => Pi.π _ <| f ≫ g
      map_id := by
        intro X
        ext h
        rw [Pi.lift_π]
        simp only [Category.id_comp]
      map_comp := by
        intro X Y Z f g
        ext h
        rw [Pi.lift_π]
        conv_rhs =>
          rw [Category.assoc]
          rw [Pi.lift_π]
          rw [Pi.lift_π]
        rw [Category.assoc] }
  map f :=
    { app := fun _ => Pi.lift fun g => Pi.π _ g ≫ f
      naturality := by
        intro X Y g
        ext h
        simp only
        rw [Category.assoc]
        rw [Pi.lift_π]
        rw [← Category.assoc]
        rw [Pi.lift_π]
        rw [Category.assoc]
        rw [Pi.lift_π]
        conv_rhs =>
          rw [Pi.lift_π] }
  map_id := by
    intro d
    ext t h
    rw [Pi.lift_π]
    simp only [NatTrans.id_app, Category.id_comp, Category.comp_id]
  map_comp := by
    intro X Y Z f g
    ext t h
    rw [Pi.lift_π]
    simp only [NatTrans.comp_app]
    rw [Category.assoc]
    rw [Pi.lift_π]
    rw [← Category.assoc]
    rw [← Category.assoc]
    rw [Pi.lift_π]

private lemma evaluationRightAdjoint_lift_π_id
    {F : C ⥤ D} {c : C} {d : D} (f : F.obj c ⟶ d) :
    Pi.lift (fun h : c ⟶ c => F.map h ≫ f) ≫ Pi.π _ (𝟙 c) = f := by
  rw [Pi.lift_π, Functor.map_id, Category.id_comp]

private lemma evaluationRightAdjoint_naturality_π
    {F : C ⥤ D} {c x : C} {d : D}
    (f : F ⟶ (evaluationRightAdjoint D c).obj d) (g : x ⟶ c) :
    F.map g ≫ f.app c ≫ Pi.π _ (𝟙 c) = f.app x ≫ Pi.π _ g := by
  rw [f.naturality_assoc g, evaluationRightAdjoint_obj_map]
  simp only [evaluationRightAdjoint_obj_obj]
  conv_lhs =>
    arg 2
    rw [Pi.lift_π]
  simp only [Category.comp_id]

/-- The adjunction showing that evaluation is a left adjoint. -/
@[simps! unit_app_app counit_app]
def evaluationAdjunctionLeft (c : C) : (evaluation _ _).obj c ⊣ evaluationRightAdjoint D c :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun F d =>
        { toFun := fun f =>
            { app := fun _ => Pi.lift fun g => F.map g ≫ f
              naturality := by
                intro X Y k
                simp only [evaluationRightAdjoint_obj_obj, evaluationRightAdjoint_obj_map]
                ext h
                rw [Category.assoc]
                rw [Pi.lift_π]
                rw [Category.assoc]
                rw [Pi.lift_π]
                rw [Pi.lift_π]
                rw [← F.map_comp_assoc] }
          invFun := fun f => f.app _ ≫ Pi.π _ (𝟙 _)
          left_inv := by
            intro f
            apply evaluationRightAdjoint_lift_π_id (D := D) (F := F) (c := c) (d := d) f
          right_inv := by
            intro f
            ext x
            simp only [evaluationRightAdjoint_obj_obj]
            ext g
            rw [Pi.lift_π]
            apply evaluationRightAdjoint_naturality_π (D := D) f g }
      homEquiv_naturality_left_symm := by
        intro X' X Y f g
        simp only [Equiv.coe_fn_symm_mk, NatTrans.comp_app, evaluation_obj_map]
        rw [← Category.assoc]
        rfl
      homEquiv_naturality_right := by
        intro X Y Y' f g
        ext x
        simp only [Equiv.coe_fn_mk, evaluationRightAdjoint_obj_obj,
          evaluationRightAdjoint_map_app, NatTrans.comp_app]
        ext h
        rw [Pi.lift_π]
        rw [Category.assoc]
        rw [Pi.lift_π]
        conv_rhs =>
          rw [← Category.assoc]
          rw [Pi.lift_π]
        rw [Category.assoc]
        rfl }

instance evaluationIsLeftAdjoint (c : C) : ((evaluation _ D).obj c).IsLeftAdjoint :=
  ⟨_, ⟨evaluationAdjunctionLeft _ _⟩⟩

/-- See also the file `Mathlib/CategoryTheory/Limits/FunctorCategory/EpiMono.lean`
for a similar result under a `HasPushouts` assumption. -/
theorem NatTrans.epi_iff_epi_app' {F G : C ⥤ D} (η : F ⟶ G) : Epi η ↔ ∀ c, Epi (η.app c) := by
  constructor
  · intro h c
    apply (inferInstance : Epi (((evaluation _ _).obj c).map η))
  · intros
    apply NatTrans.epi_of_epi_app

end

end

end CategoryTheory
