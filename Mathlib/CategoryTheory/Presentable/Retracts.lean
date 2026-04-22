/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Presentable.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.SplitCoequalizer

/-!
# Presentable objects are stable under retracts

-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C]

lemma Retract.isCardinalPresentable
    {X Y : C} (h : Retract Y X) (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [IsCardinalPresentable X κ] :
    IsCardinalPresentable Y κ := by
  let t : IsSplitCoequalizer (h.r ≫ h.i) (𝟙 X) h.r :=
    { rightSection := h.i, leftSection := 𝟙 X }
  have (j : WalkingParallelPair) :
      IsCardinalPresentable ((parallelPair (h.r ≫ h.i) (𝟙 X)).obj j) κ := by
    cases j <;> change IsCardinalPresentable X κ <;> infer_instance
  exact isCardinalPresentable_of_isColimit' t.asCofork t.isCoequalizer κ
    (hasCardinalLT_of_finite (Arrow WalkingParallelPair) κ (Cardinal.IsRegular.aleph0_le Fact.out))

instance (κ : Cardinal.{w}) [Fact κ.IsRegular] :
    (isCardinalPresentable C κ).IsStableUnderRetracts where
  of_retract {Y X} h hX := by
    rw [isCardinalPresentable_iff] at hX ⊢
    exact h.isCardinalPresentable κ

end CategoryTheory
