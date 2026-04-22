/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.Connected
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.CategoryTheory.Limits.Types.Pushouts
public import Mathlib.CategoryTheory.Limits.Types.Coproducts
public import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
# Stability properties of monomorphisms in `Type`

In this file, we show that in the category `Type u`, monomorphisms
are stable under cobase change, filtered colimits.
After importing `Mathlib/CategoryTheory/MorphismProperty/TransfiniteComposition.lean`,
the fact that monomorphisms are stable under transfinite composition
will also be inferred automatically.

(The stability by retracts holds in any category: it is shown
in the file `Mathlib/CategoryTheory/MorphismProperty/Retract.lean`.)

-/

@[expose] public section

universe v' u' u

namespace CategoryTheory.Types

open MorphismProperty Limits Limits.Types.FilteredColimit

instance : (monomorphisms (Type u)).IsStableUnderCobaseChange where
  of_isPushout {X₁ X₂ X₃ X₄ t l r b} sq ht := by
    simp only [monomorphisms.iff] at ht ⊢
    exact Limits.Types.pushoutCocone_inr_mono_of_isColimit sq.flip.isColimit

instance : MorphismProperty.IsStableUnderFilteredColimits.{v', u'} (monomorphisms (Type u)) where
  isStableUnderColimitsOfShape J _ _ := ⟨fun F₁ F₂ c₁ c₂ hc₁ hc₂ f hf φ hφ ↦ by
    simp only [functorCategory, monomorphisms.iff, mono_iff_injective] at hf ⊢
    replace hφ (j : J) := congr_fun (hφ j)
    dsimp at hφ
    intro x₁ y₁ h
    obtain ⟨j, x₁, y₁, h₁, h₂⟩ := jointly_surjective_of_isColimit₂ hc₁ x₁ y₁
    rw [← h₁, ← h₂] at h ⊢
    rw [hφ, hφ] at h
    obtain ⟨k, α, hk⟩ := (Types.FilteredColimit.isColimit_eq_iff' hc₂ _ _).1 h
    simp only [← FunctorToTypes.naturality] at hk
    rw [← c₁.w α, types_comp_apply, types_comp_apply, hf _ hk]⟩

instance (T : Type u') : MorphismProperty.IsStableUnderCoproductsOfShape
    (monomorphisms (Type u)) T :=
  IsStableUnderCoproductsOfShape.mk _ _ (by
    intro X₁ X₂ _ _ f h
    simp only [monomorphisms.iff, mono_iff_injective] at h ⊢
    refine Function.Injective.of_comp_right (f := Limits.Sigma.map f)
      (g := (Cofan.mk _ (Sigma.ι X₁)).cofanTypes.fromSigma) ?_
      (CofanTypes.bijective_fromSigma_of_isColimit
        ((Cofan.isColimit_cofanTypes_iff _).2 ⟨coproductIsCoproduct X₁⟩)).2
    convert (CofanTypes.bijective_fromSigma_of_isColimit
      ((Cofan.isColimit_cofanTypes_iff _).2 ⟨coproductIsCoproduct X₂⟩)).1.comp
        (Function.injective_id.sigma_map h) using 1
    ext ⟨i, x⟩
    exact congr_fun (Sigma.ι_map f i) x)

instance : MorphismProperty.IsStableUnderCoproducts (monomorphisms (Type u)) where

end CategoryTheory.Types
