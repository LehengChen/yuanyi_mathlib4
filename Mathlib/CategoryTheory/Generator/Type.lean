/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Generator.Basic

/-!
# Generator of Type

In this file, we show that `PUnit`, and more generally any nonempty type, is a separator
of the category `Type u`.

-/

public section

universe u

namespace CategoryTheory

lemma Types.isSeparator_punit (G : Type u := PUnit.{u + 1}) [Nonempty G] : IsSeparator G := by
  intro X Y f g h
  ext x
  obtain ⟨a⟩ := (inferInstance : Nonempty G)
  exact congr_fun (h G (by simp) (fun _ ↦ x)) a

end CategoryTheory
