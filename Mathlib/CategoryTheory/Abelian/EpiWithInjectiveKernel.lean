/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.MorphismProperty.Composition

/-!
# Epimorphisms with an injective kernel

In this file, we define the class of morphisms `epiWithInjectiveKernel` in a
category with kernels. We show that this property of morphisms is multiplicative
under weaker assumptions than abelianness.

This shall be used in the file `Mathlib/Algebra/Homology/Factorizations/Basic.lean` in
order to define morphisms of cochain complexes which satisfy this property
degreewise.

-/

@[expose] public section

namespace CategoryTheory

open Category Limits ZeroObject Preadditive

variable {C : Type*} [Category* C]

namespace Abelian

section Kernels

variable [HasZeroMorphisms C] [HasKernels C]

/-- The class of morphisms in a category with kernels that are epimorphisms
and have an injective kernel. -/
def epiWithInjectiveKernel : MorphismProperty C :=
  fun _ _ f => Epi f ∧ Injective (kernel f)

lemma epiWithInjectiveKernel_of_iso {X Y : C} (f : X ⟶ Y) [IsIso f] :
    epiWithInjectiveKernel f := by
  exact ⟨inferInstance, (isZero_kernel_of_mono f).injective⟩

end Kernels

/-- A morphism `g : X ⟶ Y` is epi with an injective kernel iff there exists a morphism
`f : I ⟶ X` with `I` injective such that `f ≫ g = 0` and
the short complex `I ⟶ X ⟶ Y` has a splitting. -/
lemma epiWithInjectiveKernel_iff [Preadditive C] [HasKernels C] [Balanced C]
    [CategoryWithHomology C] {X Y : C} (g : X ⟶ Y) :
    epiWithInjectiveKernel g ↔ ∃ (I : C) (_ : Injective I) (f : I ⟶ X) (w : f ≫ g = 0),
      Nonempty (ShortComplex.mk f g w).Splitting := by
  constructor
  · rintro ⟨_, _⟩
    let S := ShortComplex.mk (kernel.ι g) g (by simp)
    exact ⟨_, inferInstance, _, S.zero,
      ⟨ShortComplex.Splitting.ofExactOfRetraction S
        (S.exact_of_f_is_kernel (kernelIsKernel g)) (Injective.factorThru (𝟙 _) (kernel.ι g))
        (by simp [S]) inferInstance⟩⟩
  · rintro ⟨I, _, f, w, ⟨σ⟩⟩
    have : IsSplitEpi g := ⟨σ.s, σ.s_g⟩
    have hσ : IsLimit (KernelFork.ofι f w) := by
      refine KernelFork.IsLimit.ofι f w (fun {W'} k hk => k ≫ σ.r) ?_ ?_
      · intro W' k hk
        simpa [Category.assoc, reassoc_of% hk] using congrArg (fun t => k ≫ t) σ.id
      · intro W' k hk m hm
        have hf_r : f ≫ σ.r = 𝟙 I := σ.f_r
        calc
          m = m ≫ (f ≫ σ.r) := by simp [hf_r]
          _ = k ≫ σ.r := by rw [← Category.assoc, hm]
    let e : I ≅ kernel g :=
      IsLimit.conePointUniqueUpToIso hσ (limit.isLimit _)
    exact ⟨inferInstance, Injective.of_iso e inferInstance⟩

instance [Preadditive C] [HasKernels C] [Balanced C] [CategoryWithHomology C]
    [HasBinaryBiproducts C] : (epiWithInjectiveKernel : MorphismProperty C).IsMultiplicative where
  id_mem _ := epiWithInjectiveKernel_of_iso _
  comp_mem {X Y Z} g₁ g₂ hg₁ hg₂ := by
    rw [epiWithInjectiveKernel_iff] at hg₁ hg₂ ⊢
    obtain ⟨I₁, _, f₁, w₁, ⟨σ₁⟩⟩ := hg₁
    obtain ⟨I₂, _, f₂, w₂, ⟨σ₂⟩⟩ := hg₂
    refine ⟨I₁ ⊞ I₂, inferInstance, biprod.fst ≫ f₁ + biprod.snd ≫ f₂ ≫ σ₁.s, ?_, ⟨?_⟩⟩
    · ext
      · simp [reassoc_of% w₁]
      · simp [reassoc_of% σ₁.s_g, w₂]
    · exact
        { r := σ₁.r ≫ biprod.inl + g₁ ≫ σ₂.r ≫ biprod.inr
          s := σ₂.s ≫ σ₁.s
          f_r := by
            ext
            · simp [σ₁.f_r]
            · simp [reassoc_of% w₁]
            · simp
            · simp [reassoc_of% σ₁.s_g, σ₂.f_r]
          s_g := by simp [reassoc_of% σ₁.s_g, σ₂.s_g]
          id := by
            dsimp
            have h := g₁ ≫= σ₂.id =≫ σ₁.s
            simp only [add_comp, assoc, comp_add, id_comp] at h
            rw [← σ₁.id, ← h]
            simp only [comp_add, add_comp, assoc, BinaryBicone.inl_fst_assoc,
              BinaryBicone.inr_fst_assoc, zero_comp, comp_zero, add_zero,
              BinaryBicone.inl_snd_assoc, BinaryBicone.inr_snd_assoc, zero_add]
            abel }

end Abelian

end CategoryTheory
