/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-!
# Miscellany about preservation of (co)limits in monoidal categories

This file records some `PreservesColimits` instances on tensor products in monoidal categories. -/

@[expose] public section

namespace CategoryTheory.MonoidalCategory.Limits
open _root_.CategoryTheory.Limits

variable {C : Type*} [Category* C] [MonoidalCategory C]
  {J : Type*} [Category* J] (F : J ⥤ C)

section Colimits

/-- When `C` is braided and `tensorLeft c` preserves a colimit, then so does `tensorRight k`. -/
instance preservesColimit_of_braided_and_preservesColimit_tensor_left
    [BraidedCategory C] (c : C)
    [PreservesColimit F (tensorLeft c)] :
    PreservesColimit F (tensorRight c) :=
  preservesColimit_of_natIso F (BraidedCategory.tensorLeftIsoTensorRight c)

/-- When `tensorLeft c` and `tensorRight c` are naturally isomorphic and `tensorRight c`
preserves a colimit, then so does `tensorLeft c`. -/
lemma preservesColimit_of_braided_and_preservesColimit_tensor_right
    (c : C) (e : tensorLeft c ≅ tensorRight c)
    [PreservesColimit F (tensorRight c)] :
    PreservesColimit F (tensorLeft c) :=
  preservesColimit_of_natIso F e.symm

lemma preservesCoLimit_curriedTensor [h : ∀ c : C, PreservesColimit F (tensorRight c)] :
    PreservesColimit F (curriedTensor C) :=
  preservesColimit_of_evaluation _ _
    (fun c ↦ inferInstanceAs (PreservesColimit F (tensorRight c)))

end Colimits

section Limits

/-- When `C` is braided and `tensorLeft c` preserves a limit, then so does `tensorRight k`. -/
instance preservesLimit_of_braided_and_preservesLimit_tensor_left
    [BraidedCategory C] (c : C)
    [PreservesLimit F (tensorLeft c)] :
    PreservesLimit F (tensorRight c) :=
  preservesLimit_of_natIso F (BraidedCategory.tensorLeftIsoTensorRight c)

/-- When `tensorLeft c` and `tensorRight c` are naturally isomorphic and `tensorRight c`
preserves a limit, then so does `tensorLeft c`. -/
lemma preservesLimit_of_braided_and_preservesLimit_tensor_right
    (c : C) (e : tensorLeft c ≅ tensorRight c)
    [PreservesLimit F (tensorRight c)] :
    PreservesLimit F (tensorLeft c) :=
  preservesLimit_of_natIso F e.symm

lemma preservesLimit_curriedTensor [h : ∀ c : C, PreservesLimit F (tensorRight c)] :
    PreservesLimit F (curriedTensor C) :=
  preservesLimit_of_evaluation _ _ <| fun c ↦ inferInstanceAs (PreservesLimit F (tensorRight c))

end Limits

end CategoryTheory.MonoidalCategory.Limits
