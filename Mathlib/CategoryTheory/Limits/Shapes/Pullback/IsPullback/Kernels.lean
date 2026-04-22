/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-!
# Horizontal maps in a pullback square have the same kernel

Consider a commutative square:
```
    t
 X₁ --> X₂
l|      |r
 v      v
 X₃ --> X₄
    b
```
* If this is a pullback square, then the induced map `kernel t ⟶ kernel b`
  is an isomorphism.
* If this is a pushout square, then the induced map `cokernel t ⟶ cokernel b`
  is an isomorphism.

(Similar results for the (co)kernels of the vertical maps can be obtained
by applying these results to the flipped square.)

-/

@[expose] public section

universe v v' u u'

namespace CategoryTheory.Limits

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  {X₁ X₂ X₃ X₄ : C} {t : X₁ ⟶ X₂} {l : X₁ ⟶ X₃} {r : X₂ ⟶ X₄} {b : X₃ ⟶ X₄}

lemma isIso_kernel_map_of_isPullback [HasKernel b] (sq : IsPullback t l r b) :
    letI : HasKernel t := by
      refine ⟨⟨{
        cone := KernelFork.ofι (sq.lift 0 (kernel.ι b) (by simp)) (by simp)
        isLimit := ?_ }⟩⟩
      refine KernelFork.IsLimit.ofι _ _
        (fun {W} k hk => kernel.lift b (k ≫ l)
          (by rw [Category.assoc, ← sq.w, ← Category.assoc, hk, zero_comp]))
        (fun {W} k hk => ?_)
        (fun {W} k hk m hm => ?_)
      · exact sq.hom_ext (by simp [hk]) (by simp)
      · ext
        simp [← hm]
    IsIso (kernel.map _ _ _ _ sq.w) :=
  letI : HasKernel t := by
    refine ⟨⟨{
      cone := KernelFork.ofι (sq.lift 0 (kernel.ι b) (by simp)) (by simp)
      isLimit := ?_ }⟩⟩
    refine KernelFork.IsLimit.ofι _ _
      (fun {W} k hk => kernel.lift b (k ≫ l)
        (by rw [Category.assoc, ← sq.w, ← Category.assoc, hk, zero_comp]))
      (fun {W} k hk => ?_)
      (fun {W} k hk m hm => ?_)
    · exact sq.hom_ext (by simp [hk]) (by simp)
    · ext
      simp [← hm]
  ⟨kernel.lift _ (sq.lift 0 (kernel.ι b) (by simp)) (by simp),
    by ext; exact sq.hom_ext (by cat_disch) (by cat_disch), by cat_disch⟩

lemma isIso_cokernel_map_of_isPushout [HasCokernel t] (sq : IsPushout t l r b) :
    letI : HasCokernel b := by
      refine ⟨⟨{
        cocone := CokernelCofork.ofπ (sq.desc (cokernel.π t) 0 (by simp)) (by simp)
        isColimit := ?_ }⟩⟩
      refine CokernelCofork.IsColimit.ofπ _ _
        (fun {W} k hk => cokernel.desc t (r ≫ k)
          (by rw [← Category.assoc, sq.w, Category.assoc, hk, comp_zero]))
        (fun {W} k hk => ?_)
        (fun {W} k hk m hm => ?_)
      · exact sq.hom_ext (by simp) (by simp [hk])
      · ext
        simp [← hm]
    IsIso (cokernel.map _ _ _ _ sq.w) :=
  letI : HasCokernel b := by
    refine ⟨⟨{
      cocone := CokernelCofork.ofπ (sq.desc (cokernel.π t) 0 (by simp)) (by simp)
      isColimit := ?_ }⟩⟩
    refine CokernelCofork.IsColimit.ofπ _ _
      (fun {W} k hk => cokernel.desc t (r ≫ k)
        (by rw [← Category.assoc, sq.w, Category.assoc, hk, comp_zero]))
      (fun {W} k hk => ?_)
      (fun {W} k hk m hm => ?_)
    · exact sq.hom_ext (by simp) (by simp [hk])
    · ext
      simp [← hm]
  ⟨cokernel.desc _ (sq.desc (cokernel.π t) 0 (by simp)) (by simp),
    by cat_disch, by ext; exact sq.hom_ext (by cat_disch) (by cat_disch)⟩

end CategoryTheory.Limits
