/-
Copyright (c) 2022 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Preadditive.FunctorCategory
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Finite
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# If `D` is abelian, then the functor category `C ⥤ D` is also abelian.

-/

@[expose] public section


noncomputable section

namespace CategoryTheory

open CategoryTheory.Limits

namespace Abelian

section

universe z w v u

variable {C : Type u} [Category.{v} C]
variable {D : Type w} [Category.{z} D] [Abelian D]

namespace FunctorCategory

variable {F G : C ⥤ D} (α : F ⟶ G) (X : C)

@[simp] private lemma cokernel_π_app_preservesCokernel_iso_hom :
    (cokernel.π α).app X ≫ (PreservesCokernel.iso ((evaluation C D).obj X) α).hom =
      cokernel.π (α.app X) :=
  PreservesCokernel.π_iso_hom ((evaluation C D).obj X) α

/-- The abelian coimage in a functor category can be calculated componentwise. -/
@[simps!]
def coimageObjIso : (Abelian.coimage α).obj X ≅ Abelian.coimage (α.app X) :=
  PreservesCokernel.iso ((evaluation C D).obj X) _ ≪≫
    cokernel.mapIso _ _ (PreservesKernel.iso ((evaluation C D).obj X) _) (Iso.refl _)
      (by
        rw [← kernelComparison_comp_ι _ ((evaluation C D).obj X)]
        simp [PreservesKernel.iso_hom])

/-- The abelian image in a functor category can be calculated componentwise. -/
@[simps!]
def imageObjIso : (Abelian.image α).obj X ≅ Abelian.image (α.app X) :=
  PreservesKernel.iso ((evaluation C D).obj X) _ ≪≫
    kernel.mapIso _ _ (Iso.refl _) (PreservesCokernel.iso ((evaluation C D).obj X) _)
      (by
        simp only [evaluation_obj_obj, evaluation_obj_map, Iso.refl_hom, Category.id_comp]
        rw [← cokernel_π_app_preservesCokernel_iso_hom]
        simp)

theorem coimageImageComparison_app :
    coimageImageComparison (α.app X) =
      (coimageObjIso α X).inv ≫ (coimageImageComparison α).app X ≫ (imageObjIso α X).hom := by
  ext
  simp only [coequalizer_as_cokernel, equalizer_as_kernel, Category.assoc,
    coimage_image_factorisation, coimageObjIso_inv, imageObjIso_hom, cokernel.π_desc_assoc,
    Category.id_comp, kernel.lift_ι, Category.comp_id]
  erw [kernelComparison_comp_ι _ ((evaluation C D).obj X)]
  erw [π_comp_cokernelComparison_assoc _ ((evaluation C D).obj X)]
  conv_lhs => rw [← coimage_image_factorisation α]
  rfl

theorem coimageImageComparison_app' :
    (coimageImageComparison α).app X =
      (coimageObjIso α X).hom ≫ coimageImageComparison (α.app X) ≫ (imageObjIso α X).inv := by
  simp only [coimageImageComparison_app, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.assoc,
    Category.comp_id]

instance functor_category_isIso_coimageImageComparison :
    IsIso (Abelian.coimageImageComparison α) := by
  letI : ∀ X : C, IsIso ((Abelian.coimageImageComparison α).app X) := by
    intro X
    rw [coimageImageComparison_app']
    infer_instance
  apply NatIso.isIso_of_isIso_app

end FunctorCategory

noncomputable instance functorCategoryAbelian : Abelian (C ⥤ D) :=
  let _ : HasKernels (C ⥤ D) := inferInstance
  let _ : HasCokernels (C ⥤ D) := inferInstance
  Abelian.ofCoimageImageComparisonIsIso

end

end Abelian

end CategoryTheory
