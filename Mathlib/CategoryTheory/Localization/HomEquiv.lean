/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Localization.LocalizerMorphism
public import Mathlib.CategoryTheory.HomCongr

/-!
# Bijections between morphisms in two localized categories

Given two localization functors `L₁ : C ⥤ D₁` and `L₂ : C ⥤ D₂` for the same
class of morphisms `W : MorphismProperty C`, we define a bijection
`Localization.homEquiv W L₁ L₂ : (L₁.obj X ⟶ L₁.obj Y) ≃ (L₂.obj X ⟶ L₂.obj Y)`
between the types of morphisms in the two localized categories.

More generally, given a localizer morphism `Φ : LocalizerMorphism W₁ W₂`, we define a map
`Φ.homMap L₁ L₂ : (L₁.obj X ⟶ L₁.obj Y) ⟶ (L₂.obj (Φ.functor.obj X) ⟶ L₂.obj (Φ.functor.obj Y))`.
The definition `Localization.homEquiv` is obtained by applying the construction
to the identity localizer morphism.

-/

@[expose] public section

namespace CategoryTheory

open Category

variable {C C₁ C₂ C₃ D₁ D₂ D₃ : Type*} [Category* C]
  [Category* C₁] [Category* C₂] [Category* C₃]
  [Category* D₁] [Category* D₂] [Category* D₃]

namespace LocalizerMorphism

variable {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂} {W₃ : MorphismProperty C₃}
  (Φ : LocalizerMorphism W₁ W₂) (Ψ : LocalizerMorphism W₂ W₃)
  (L₁ : C₁ ⥤ D₁) [L₁.IsLocalization W₁]
  (L₂ : C₂ ⥤ D₂)
  (L₃ : C₃ ⥤ D₃)
  {X Y Z : C₁}

/-- If `Φ : LocalizerMorphism W₁ W₂` is a morphism of localizers, `L₁` is a
localization functor for `W₁`, and `L₂` inverts `W₂`, then this is the induced map
`(L₁.obj X ⟶ L₁.obj Y) ⟶ (L₂.obj (Φ.functor.obj X) ⟶ L₂.obj (Φ.functor.obj Y))`
for all objects `X` and `Y`. -/
noncomputable def homMap (f : L₁.obj X ⟶ L₁.obj Y)
    (hL₂ : W₂.IsInvertedBy L₂ := by apply Localization.inverts) :
    L₂.obj (Φ.functor.obj X) ⟶ L₂.obj (Φ.functor.obj Y) :=
  let h : W₁.IsInvertedBy (Φ.functor ⋙ L₂) := fun _ _ _ hf => hL₂ _ (Φ.map _ hf)
  Iso.homCongr ((Localization.fac (Φ.functor ⋙ L₂) h L₁).app _)
    ((Localization.fac (Φ.functor ⋙ L₂) h L₁).app _)
    ((Localization.lift (Φ.functor ⋙ L₂) h L₁).map f)

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma homMap_map (f : X ⟶ Y)
    (hL₂ : W₂.IsInvertedBy L₂ := by apply Localization.inverts) :
    Φ.homMap L₁ L₂ (L₁.map f) (hL₂ := hL₂) = L₂.map (Φ.functor.map f) := by
  let h : W₁.IsInvertedBy (Φ.functor ⋙ L₂) := fun _ _ _ hf => hL₂ _ (Φ.map _ hf)
  change (Localization.fac (Φ.functor ⋙ L₂) h L₁).inv.app X ≫
      (Localization.lift (Φ.functor ⋙ L₂) h L₁).map (L₁.map f) ≫
      (Localization.fac (Φ.functor ⋙ L₂) h L₁).hom.app Y = _
  change (Localization.fac (Φ.functor ⋙ L₂) h L₁).inv.app X ≫
      ((L₁ ⋙ Localization.lift (Φ.functor ⋙ L₂) h L₁).map f ≫
      (Localization.fac (Φ.functor ⋙ L₂) h L₁).hom.app Y) = _
  rw [(Localization.fac (Φ.functor ⋙ L₂) h L₁).hom.naturality f,
    ← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
  rfl

variable (X) in
@[simp]
lemma homMap_id (hL₂ : W₂.IsInvertedBy L₂ := by apply Localization.inverts) :
    Φ.homMap L₁ L₂ (𝟙 (L₁.obj X)) (hL₂ := hL₂) =
      𝟙 (L₂.obj (Φ.functor.obj X)) := by
  simpa using Φ.homMap_map L₁ L₂ (𝟙 X) (hL₂ := hL₂)

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma homMap_comp (f : L₁.obj X ⟶ L₁.obj Y) (g : L₁.obj Y ⟶ L₁.obj Z)
    (hL₂ : W₂.IsInvertedBy L₂ := by apply Localization.inverts) :
    Φ.homMap L₁ L₂ (f ≫ g) (hL₂ := hL₂) =
      Φ.homMap L₁ L₂ f (hL₂ := hL₂) ≫ Φ.homMap L₁ L₂ g (hL₂ := hL₂) := by
  simp [homMap]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma homMap_apply (G : D₁ ⥤ D₂) (e : Φ.functor ⋙ L₂ ≅ L₁ ⋙ G)
    (f : L₁.obj X ⟶ L₁.obj Y)
    (hL₂ : W₂.IsInvertedBy L₂ := by apply Localization.inverts) :
    Φ.homMap L₁ L₂ f (hL₂ := hL₂) = e.hom.app X ≫ G.map f ≫ e.inv.app Y := by
  let h : W₁.IsInvertedBy (Φ.functor ⋙ L₂) := fun _ _ _ hf => hL₂ _ (Φ.map _ hf)
  let G' := Localization.lift (Φ.functor ⋙ L₂) h L₁
  let e' : Φ.functor ⋙ L₂ ≅ L₁ ⋙ G' := (Localization.fac (Φ.functor ⋙ L₂) h L₁).symm
  change e'.hom.app X ≫ G'.map f ≫ e'.inv.app Y = _
  letI : Localization.Lifting L₁ W₁ (Φ.functor ⋙ L₂) G := ⟨e.symm⟩
  let α : G' ≅ G := Localization.liftNatIso L₁ W₁ (L₁ ⋙ G') (Φ.functor ⋙ L₂) _ _ e'.symm
  have : e = e' ≪≫ Functor.isoWhiskerLeft _ α := by
    ext
    simp [α, this]
  simp [this]

@[simp]
lemma id_homMap (f : L₁.obj X ⟶ L₁.obj Y) :
    (id W₁).homMap L₁ L₁ f (hL₂ := Localization.inverts L₁ W₁) = f := by
  simpa using (id W₁).homMap_apply L₁ L₁ (𝟭 D₁) (Iso.refl _) f
    (hL₂ := Localization.inverts L₁ W₁)

@[simp]
lemma homMap_homMap [L₂.IsLocalization W₂] (f : L₁.obj X ⟶ L₁.obj Y)
    (hL₃ : W₃.IsInvertedBy L₃ := by apply Localization.inverts) :
    Ψ.homMap L₂ L₃ (Φ.homMap L₁ L₂ f) (hL₂ := hL₃) =
      (Φ.comp Ψ).homMap L₁ L₃ f (hL₂ := hL₃) := by
  let G := Φ.localizedFunctor L₁ L₂
  let h₃ : W₂.IsInvertedBy (Ψ.functor ⋙ L₃) := fun _ _ _ hf => hL₃ _ (Ψ.map _ hf)
  let G' := Localization.lift (Ψ.functor ⋙ L₃) h₃ L₂
  let e : Φ.functor ⋙ L₂ ≅ L₁ ⋙ G := CatCommSq.iso _ _ _ _
  let e' : Ψ.functor ⋙ L₃ ≅ L₂ ⋙ G' := (Localization.fac (Ψ.functor ⋙ L₃) h₃ L₂).symm
  rw [Φ.homMap_apply L₁ L₂ G e, Ψ.homMap_apply L₂ L₃ G' e' _ (hL₂ := hL₃),
    (Φ.comp Ψ).homMap_apply L₁ L₃ (G ⋙ G')
      (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ e' ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight e _ ≪≫
      Functor.associator _ _ _) _ (hL₂ := hL₃)]
  dsimp
  simp only [Functor.map_comp, assoc, comp_id, id_comp]

end LocalizerMorphism

namespace Localization

variable (W : MorphismProperty C) (L₁ : C ⥤ D₁) [L₁.IsLocalization W]
  (L₂ : C ⥤ D₂) [L₂.IsLocalization W] (L₃ : C ⥤ D₃) [L₃.IsLocalization W]
  {X Y Z : C}

set_option backward.isDefEq.respectTransparency false in
/-- Bijection between types of morphisms in two localized categories
for the same class of morphisms `W`. -/
@[simps -isSimp apply]
noncomputable def homEquiv :
    (L₁.obj X ⟶ L₁.obj Y) ≃ (L₂.obj X ⟶ L₂.obj Y) where
  toFun f := (LocalizerMorphism.id W).homMap L₁ L₂ f (hL₂ := Localization.inverts L₂ W)
  invFun f := (LocalizerMorphism.id W).homMap L₂ L₁ f (hL₂ := Localization.inverts L₁ W)
  left_inv f := by
    change (LocalizerMorphism.id W).homMap L₂ L₁
      ((LocalizerMorphism.id W).homMap L₁ L₂ f (hL₂ := Localization.inverts L₂ W))
      (hL₂ := Localization.inverts L₁ W) = f
    rw [LocalizerMorphism.homMap_homMap (LocalizerMorphism.id W)
      (LocalizerMorphism.id W) L₁ L₂ L₁ f (hL₃ := Localization.inverts L₁ W)]
    apply LocalizerMorphism.id_homMap
  right_inv g := by
    change (LocalizerMorphism.id W).homMap L₁ L₂
      ((LocalizerMorphism.id W).homMap L₂ L₁ g (hL₂ := Localization.inverts L₁ W))
      (hL₂ := Localization.inverts L₂ W) = g
    rw [LocalizerMorphism.homMap_homMap (LocalizerMorphism.id W)
      (LocalizerMorphism.id W) L₂ L₁ L₂ g (hL₃ := Localization.inverts L₂ W)]
    apply LocalizerMorphism.id_homMap

@[simp]
lemma homEquiv_symm_apply (g : L₂.obj X ⟶ L₂.obj Y) :
    (homEquiv W L₁ L₂).symm g = homEquiv W L₂ L₁ g := rfl

set_option backward.isDefEq.respectTransparency false in
lemma homEquiv_eq (G : D₁ ⥤ D₂) (e : L₁ ⋙ G ≅ L₂) (f : L₁.obj X ⟶ L₁.obj Y) :
    homEquiv W L₁ L₂ f = e.inv.app X ≫ G.map f ≫ e.hom.app Y := by
  rw [homEquiv_apply, LocalizerMorphism.homMap_apply (LocalizerMorphism.id W) L₁ L₂ G e.symm,
    Iso.symm_hom, Iso.symm_inv]

@[simp]
lemma homEquiv_refl (f : L₁.obj X ⟶ L₁.obj Y) :
    homEquiv W L₁ L₁ f = f := by
  apply LocalizerMorphism.id_homMap

lemma homEquiv_trans (f : L₁.obj X ⟶ L₁.obj Y) :
    homEquiv W L₂ L₃ (homEquiv W L₁ L₂ f) = homEquiv W L₁ L₃ f := by
  dsimp only [homEquiv_apply]
  exact LocalizerMorphism.homMap_homMap (LocalizerMorphism.id W) (LocalizerMorphism.id W)
    L₁ L₂ L₃ f (hL₃ := Localization.inverts L₃ W)

lemma homEquiv_comp (f : L₁.obj X ⟶ L₁.obj Y) (g : L₁.obj Y ⟶ L₁.obj Z) :
    homEquiv W L₁ L₂ (f ≫ g) = homEquiv W L₁ L₂ f ≫ homEquiv W L₁ L₂ g := by
  exact LocalizerMorphism.homMap_comp (LocalizerMorphism.id W) L₁ L₂ f g
    (hL₂ := Localization.inverts L₂ W)

@[simp]
lemma homEquiv_map (f : X ⟶ Y) : homEquiv W L₁ L₂ (L₁.map f) = L₂.map f := by
  simp [homEquiv_apply]

variable (X) in
@[simp]
lemma homEquiv_id : homEquiv W L₁ L₂ (𝟙 (L₁.obj X)) = 𝟙 (L₂.obj X) := by
  simp [homEquiv_apply]

lemma homEquiv_isoOfHom_inv (f : Y ⟶ X) (hf : W f) :
    homEquiv W L₁ L₂ (isoOfHom L₁ W f hf).inv = (isoOfHom L₂ W f hf).inv := by
  rw [← cancel_mono (isoOfHom L₂ W f hf).hom, Iso.inv_hom_id, isoOfHom_hom,
    ← homEquiv_map W L₁ L₂ f, ← homEquiv_comp, isoOfHom_inv_hom_id, homEquiv_id]

end Localization

end CategoryTheory
