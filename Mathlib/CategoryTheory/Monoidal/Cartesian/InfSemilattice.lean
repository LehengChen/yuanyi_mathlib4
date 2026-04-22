/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/
module

public import Mathlib.CategoryTheory.Limits.Preorder
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic

/-!
# The preorder category of a meet-semilattice with a greatest element is Cartesian monoidal

The preorder category of a meet-semilattice `C` with a greatest element is Cartesian monoidal.

A symmetric monoidal structure on the preorder category is automatically provided by the
instance and `CartesianMonoidalCategory.toSymmetricCategory`.
-/

@[expose] public section

namespace CategoryTheory

open Category MonoidalCategory

universe u

variable (C : Type u) [SemilatticeInf C] [OrderTop C]

namespace SemilatticeInf

/-- Cartesian monoidal structure for the preorder category of a meet-semilattice with
a greatest element. -/
noncomputable scoped instance cartesianMonoidalCategory : CartesianMonoidalCategory C :=
  .ofChosenFiniteProducts ⟨_, Preorder.isTerminalTop C⟩ fun X Y ↦ ⟨_, Preorder.isLimitBinaryFan X Y⟩

/-- Braided structure for the preorder category of a meet-semilattice with a greatest element. -/
noncomputable scoped instance braidedCategory : BraidedCategory C := .ofCartesianMonoidalCategory

lemma tensorObj {C : Type u} [SemilatticeInf C] [CartesianMonoidalCategory C] {X Y : C} :
    X ⊗ Y = X ⊓ Y := by
  apply le_antisymm
  · exact le_inf (leOfHom (CartesianMonoidalCategory.fst X Y))
      (leOfHom (CartesianMonoidalCategory.snd X Y))
  · exact leOfHom ((CartesianMonoidalCategory.tensorProductIsBinaryProduct X Y).lift
      (Limits.BinaryFan.mk (homOfLE inf_le_left) (homOfLE inf_le_right)))

lemma tensorUnit {C : Type u} [PartialOrder C] [OrderTop C] [SemiCartesianMonoidalCategory C] :
    𝟙_ C = ⊤ := by
  apply le_antisymm
  · exact le_top
  · exact leOfHom (SemiCartesianMonoidalCategory.toUnit (⊤ : C))

end SemilatticeInf

end CategoryTheory
