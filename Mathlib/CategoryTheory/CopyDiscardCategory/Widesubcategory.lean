/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import Mathlib.CategoryTheory.Monoidal.Widesubcategory

/-!
# Copy-discard structures on wide subcategories

Given a monoidal category `C`, a morphism property `P : MorphismProperty C` satisfying
`P.IsMonoidalStable` and a comonoid object `c : C`, we introduce a condition `P.
IsStableUnderComonoid c` saying that `c` inherits a comonoid object structure in the category of
`WideSubcategory P`. If `C` is a copy-discard category, if `P` is also stable under braiding and
that this condition holds for the underlying object of each `c : WideSubcategory P`, we show that
`WideSubcategory P` is also a copy-discard category.
-/

@[expose] public section

namespace CategoryTheory.MorphismProperty

open scoped ComonObj

variable {C : Type*} [Category* C] (P : MorphismProperty C) [MonoidalCategory C]

/-- A braided-stable morphism property stable under comonoid counit and comultiplication. -/
class IsStableUnderComonoid (P : MorphismProperty C) (c : C) [ComonObj c] : Prop where
  counit_mem (P) : P ε[c]
  comul_mem (P) : P Δ[c]

export IsStableUnderComonoid (counit_mem comul_mem)

@[simps]
instance [P.IsMonoidalStable] (c : WideSubcategory P) [ComonObj c.obj]
    [P.IsStableUnderComonoid c.obj] : ComonObj c where
  counit := ⟨ε[c.obj], P.counit_mem⟩
  comul := ⟨Δ[c.obj], P.comul_mem⟩

instance [BraidedCategory C] [P.IsStableUnderBraiding] (c : WideSubcategory P) [ComonObj c.obj]
    [IsCommComonObj c.obj] [P.IsStableUnderComonoid c.obj] : IsCommComonObj c where
  comul_comm := by
    ext
    exact IsCommComonObj.comul_comm _

open CopyDiscardCategory in
attribute [local simp] copy_tensor discard_tensor copy_unit discard_unit in
instance [CopyDiscardCategory C] [P.IsStableUnderBraiding]
    [∀ c : WideSubcategory P, P.IsStableUnderComonoid c.obj] :
    CopyDiscardCategory (WideSubcategory P) where

end CategoryTheory.MorphismProperty
