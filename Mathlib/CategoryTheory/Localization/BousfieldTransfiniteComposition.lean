/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Localization.Bousfield
public import Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition
public import Mathlib.CategoryTheory.SmallObject.WellOrderInductionData

/-!
# ObjectProperty.isLocal is stable under transfinite compositions

If `P : ObjectProperty C`, then `P.isLocal : MorphismProperty C`
is stable under transfinite compositions.

-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Limits Opposite

variable {C : Type u} [Category.{v} C]

namespace ObjectProperty

variable (P : ObjectProperty C)

set_option backward.isDefEq.respectTransparency false in
instance (J : Type w) [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J] :
    P.isLocal.IsStableUnderTransfiniteCompositionOfShape J where
  le := fun X Y f ⟨hf⟩ Z hZ ↦ by
    refine ⟨fun g₁ g₂ h ↦ hf.isColimit.hom_ext (fun j ↦ ?_), fun g ↦ ?_⟩
    · dsimp at h ⊢
      induction j using SuccOrder.limitRecOn with
      | isMin j hj =>
        obtain rfl := hj.eq_bot
        simpa [← cancel_epi hf.isoBot.inv]
      | succ j hj hj' => exact (hf.map_mem j hj _ hZ).1 (by simpa)
      | isSuccLimit j hj hj' =>
        exact (hf.F.isColimitOfIsWellOrderContinuous j hj).hom_ext
          (fun ⟨k, hk⟩ ↦ by simpa using hj' _ hk)
    · let d : (hf.F.op ⋙ yoneda.obj Z).WellOrderInductionData :=
        .ofExists (fun j hj ↦ (hf.map_mem j hj _ hZ).2) (fun j hj s ↦ by
          let G := (Set.principalSegIio j).monotone.functor ⋙ hf.F
          let h := hf.F.isColimitOfIsWellOrderContinuous j hj
          let e := Limits.opCompYonedaSectionsEquiv G Z
          exact ⟨h.homEquiv.symm (e s), by simpa using h.ι_app_homEquiv_symm (e s)⟩)
      let σ := d.sectionsMk (hf.isoBot.hom ≫ g)
      exact ⟨hf.isColimit.homEquiv.symm ((Limits.opCompYonedaSectionsEquiv hf.F Z) σ), by
        simp only [← hf.fac, Category.assoc, hf.isColimit.ι_app_homEquiv_symm,
          Limits.opCompYonedaSectionsEquiv_apply_app, σ, d.sectionsMk_val_op_bot,
          Iso.inv_hom_id_assoc]⟩

instance : MorphismProperty.IsStableUnderTransfiniteComposition.{w} P.isLocal where

end ObjectProperty

end CategoryTheory
