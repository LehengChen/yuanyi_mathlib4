/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Images
public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono

/-!
# Preserving images

In this file, we show that if the source image factor maps are epimorphisms and a functor
preserves the relevant pullbacks and pushouts, then it preserves images.
-/

@[expose] public section


noncomputable section

namespace CategoryTheory

namespace PreservesImage

open CategoryTheory

open CategoryTheory.Limits

universe u₁ u₂ v₁ v₂

variable {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Category.{v₂} B]
variable [HasImages A]
variable [∀ {X Y : A} (f : X ⟶ Y), Epi (factorThruImage f)]
variable [StrongEpiCategory B]
variable (L : A ⥤ B)
variable [∀ {X Y : A} (f : X ⟶ Y), HasImage (L.map f)]
variable [∀ {X Y : A} (f : X ⟶ Y), PreservesLimit (cospan (image.ι f) (image.ι f)) L]
variable [∀ {X Y : A} (f : X ⟶ Y), PreservesColimit (span (factorThruImage f)
  (factorThruImage f)) L]

/-- If the source image factor maps are epimorphisms and a functor preserves the relevant pullbacks
and pushouts, then it preserves images.
-/
@[simps!]
def iso {X Y : A} (f : X ⟶ Y) : image (L.map f) ≅ L.obj (image f) :=
  let aux1 : StrongEpiMonoFactorisation (L.map f) :=
    { I := L.obj (Limits.image f)
      m := L.map <| Limits.image.ι _
      m_mono := preserves_mono_of_preservesLimit _ _
      e := L.map <| factorThruImage _
      e_strong_epi := @strongEpi_of_epi B _ _ _ _ _ (preserves_epi_of_preservesColimit L _)
      fac := by rw [← L.map_comp, Limits.image.fac] }
  IsImage.isoExt (Image.isImage (L.map f)) aux1.toMonoIsImage

@[reassoc]
theorem factorThruImage_comp_hom {X Y : A} (f : X ⟶ Y) :
    factorThruImage (L.map f) ≫ (iso L f).hom = L.map (factorThruImage f) := by simp

@[reassoc]
theorem hom_comp_map_image_ι {X Y : A} (f : X ⟶ Y) :
    (iso L f).hom ≫ L.map (image.ι f) = image.ι (L.map f) := by rw [iso_hom, image.lift_fac]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
theorem inv_comp_image_ι_map {X Y : A} (f : X ⟶ Y) :
    (iso L f).inv ≫ image.ι (L.map f) = L.map (image.ι f) := by simp

end PreservesImage

end CategoryTheory
