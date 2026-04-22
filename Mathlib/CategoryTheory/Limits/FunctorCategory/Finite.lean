/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers

/-!

# Functor categories have finite limits when the target category does

These declarations cannot be in `Mathlib/CategoryTheory/Limits/FunctorCategory/Basic.lean` because
that file shouldn't import `Mathlib/CategoryTheory/Limits/Shapes/FiniteProducts.lean`.
-/

@[expose] public section

namespace CategoryTheory.Limits

variable {C : Type*} [Category* C] {K : Type*} [Category* K]

instance [HasFiniteProducts C] : HasFiniteProducts (K ⥤ C) := ⟨inferInstance⟩

instance [HasFiniteProducts C] [HasEqualizers C] : HasFiniteLimits (K ⥤ C) :=
  hasFiniteLimits_of_hasEqualizers_and_finite_products

instance [HasFiniteCoproducts C] : HasFiniteCoproducts (K ⥤ C) := ⟨inferInstance⟩

instance [HasFiniteCoproducts C] [HasCoequalizers C] : HasFiniteColimits (K ⥤ C) :=
  hasFiniteColimits_of_hasCoequalizers_and_finite_coproducts

instance [HasFiniteProducts C] (k : K) :
    PreservesFiniteProducts ((evaluation K C).obj k) where
  preserves _ := inferInstance

instance [HasFiniteProducts C] [HasEqualizers C] (k : K) :
    PreservesFiniteLimits ((evaluation K C).obj k) :=
  preservesFiniteLimits_of_preservesEqualizers_and_finiteProducts _

instance [HasFiniteCoproducts C] (k : K) :
    PreservesFiniteCoproducts ((evaluation K C).obj k) where
  preserves _ := inferInstance

instance [HasFiniteCoproducts C] [HasCoequalizers C] (k : K) :
    PreservesFiniteColimits ((evaluation K C).obj k) :=
  preservesFiniteColimits_of_preservesCoequalizers_and_finiteCoproducts _

end CategoryTheory.Limits
