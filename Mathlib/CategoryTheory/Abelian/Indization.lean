/-
Copyright (c) 2025 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Preadditive.Indization
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.AbelianImages

/-!
# The category of ind-objects is abelian

We show that if `C` is a small abelian category, then `Ind C` is an abelian category.

In the file `Mathlib/CategoryTheory/Abelian/GrothendieckAxioms/Indization.lean`, we show that in
this situation `Ind C` is in fact Grothendieck abelian.
-/

@[expose] public section

universe v

open CategoryTheory.Abelian

namespace CategoryTheory

variable {C : Type v} [SmallCategory C] [Abelian C]

instance {X Y : Ind C} (f : X ⟶ Y) : IsIso (Abelian.coimageImageComparison f) := by
  obtain ⟨I, _, _, _, _, ϕ, ⟨i⟩⟩ := Ind.exists_nonempty_arrow_mk_iso_ind_lim (f := f)
  simpa using (Arrow.isIso_iff_isIso_of_isIso ((coimageImageComparisonFunctor.mapIso i ≪≫
    (PreservesCoimageImageComparison.iso (Ind.lim I) ϕ).symm).hom)).2 inferInstance

noncomputable instance : Abelian (Ind C) :=
  .ofCoimageImageComparisonIsIso

end CategoryTheory
