/-
Copyright (c) 2026 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
public import Mathlib.CategoryTheory.ObjectProperty.Kernels

/-!
# Subcategories of abelian categories

Let `C` be an abelian category. Given `P : ObjectProperty C` which is closed
under kernels, cokernels and finite products, we show that the full subcategory
defined by `P` is abelian.

-/

@[expose] public section

namespace CategoryTheory.ObjectProperty

open Limits

variable {C : Type*} [Category* C] (P : ObjectProperty C)

lemma preservesMonomorphisms_ι_of_isNormalEpiCategory [HasZeroMorphisms C] [HasCoequalizers C]
    [HasKernels C] [IsNormalEpiCategory C] [HasZeroObject C]
    [HasZeroObject P.FullSubcategory] [P.IsClosedUnderKernels] :
    P.ι.PreservesMonomorphisms where
  preserves f := by
    intro hf
    letI := hf
    haveI : PreservesLimit (parallelPair f 0) P.ι := P.preservesKernels_ι f
    have mono_of_zero_kernel' {X Y : C} (f : X ⟶ Y) (Z : C)
        (l : IsLimit (KernelFork.ofι (0 : Z ⟶ X) (show 0 ≫ f = 0 by simp))) : Mono f := by
      refine ⟨fun u v huv => ?_⟩
      obtain ⟨W, w, hw, hl⟩ := normalEpiOfEpi (coequalizer.π u v)
      obtain ⟨m, hm⟩ := coequalizer.desc' f huv
      have reassoced {W : C} (h : coequalizer u v ⟶ W) :
          w ≫ coequalizer.π u v ≫ h = 0 ≫ h := by
        rw [← Category.assoc, eq_whisker hw]
      have hwf : w ≫ f = 0 := by rw [← hm, reassoced, zero_comp]
      obtain ⟨n, hn⟩ := KernelFork.IsLimit.lift' l _ hwf
      have hn' : (0 : W ⟶ X) = w := by simpa using hn
      have : IsIso (coequalizer.π u v) := by
        apply isIso_colimit_cocone_parallelPair_of_eq hn'.symm hl
      apply (cancel_mono (coequalizer.π u v)).1
      exact coequalizer.condition _ _
    exact mono_of_zero_kernel' _ _ <| IsLimit.equivIsoLimit (mapZeroKernelFork P.ι f) <|
      (kernel.zeroKernelFork f).mapIsLimit (kernel.isLimitConeZeroCone f) P.ι

instance [Abelian C] [HasZeroObject P.FullSubcategory] [P.IsClosedUnderKernels]
    [P.IsClosedUnderCokernels] :
    IsNormalMonoCategory P.FullSubcategory where
  normalMonoOfMono {X Y} f :=
    have := P.preservesMonomorphisms_ι_of_isNormalEpiCategory
    ⟨{Z := .mk _ (P.prop_cokernel f.hom X.property Y.property)
      g := P.homMk (cokernel.π f.hom)
      w := by cat_disch
      isLimit := isLimitOfReflects P.ι ((KernelFork.isLimitMapConeEquiv _ _).symm
        (Abelian.monoIsKernelOfCokernel _ (cokernelIsCokernel (P.ι.map f)) :))}⟩

lemma preservesEpimorphisms_ι_of_isNormalMonoCategory [HasZeroMorphisms C] [HasEqualizers C]
    [HasCokernels C] [IsNormalMonoCategory C] [HasZeroObject C]
    [HasZeroObject P.FullSubcategory] [P.IsClosedUnderCokernels] :
    P.ι.PreservesEpimorphisms where
  preserves f := by
    intro hf
    letI := hf
    haveI : PreservesColimit (parallelPair f 0) P.ι := P.preservesCokernels_ι f
    have epi_of_zero_cokernel' {X Y : C} (f : X ⟶ Y) (Z : C)
        (l : IsColimit (CokernelCofork.ofπ (0 : Y ⟶ Z) (show f ≫ 0 = 0 by simp))) :
        Epi f := by
      refine ⟨fun u v huv => ?_⟩
      obtain ⟨W, w, hw, hl⟩ := normalMonoOfMono (equalizer.ι u v)
      obtain ⟨m, hm⟩ := equalizer.lift' f huv
      have hwf : f ≫ w = 0 := by rw [← hm, Category.assoc, hw, comp_zero]
      obtain ⟨n, hn⟩ := CokernelCofork.IsColimit.desc' l _ hwf
      have hn' : (0 : Y ⟶ W) = w := by simpa using hn
      have : IsIso (equalizer.ι u v) := by
        apply isIso_limit_cone_parallelPair_of_eq hn'.symm hl
      apply (cancel_epi (equalizer.ι u v)).1
      exact equalizer.condition _ _
    exact epi_of_zero_cokernel' _ _ <|
      IsColimit.equivIsoColimit (mapZeroCokernelCofork P.ι f) <|
      (cokernel.zeroCokernelCofork f).mapIsColimit
        (cokernel.isColimitCoconeZeroCocone f) P.ι

instance [Abelian C] [HasZeroObject P.FullSubcategory] [P.IsClosedUnderKernels]
    [P.IsClosedUnderCokernels] :
    IsNormalEpiCategory P.FullSubcategory where
  normalEpiOfEpi {X Y} f :=
    have := P.preservesEpimorphisms_ι_of_isNormalMonoCategory
    ⟨{W := .mk _ (P.prop_kernel f.hom X.property Y.property)
      g := P.homMk (kernel.ι f.hom)
      w := by cat_disch
      isColimit := isColimitOfReflects P.ι ((CokernelCofork.isColimitMapCoconeEquiv _ _).symm
        (Abelian.epiIsCokernelOfKernel _ (kernelIsKernel (P.ι.map f)) :))}⟩

instance [Abelian C] [P.IsClosedUnderKernels] [P.IsClosedUnderCokernels]
    [P.IsClosedUnderFiniteProducts] : Abelian P.FullSubcategory := by
  haveI : HasZeroObject P.FullSubcategory :=
    hasZeroObject_of_hasTerminal_object (C := P.FullSubcategory)
  exact {}

end CategoryTheory.ObjectProperty
