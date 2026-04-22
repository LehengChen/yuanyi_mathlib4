/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.EpiMono

/-!
An object is injective iff the preadditive yoneda functor on it preserves epimorphisms.
-/

public section


universe v u

open Opposite

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

section Preadditive

variable [Preadditive C]

namespace Injective

theorem injective_iff_preservesEpimorphisms_preadditiveYoneda_obj (J : C) :
    Injective J ↔ (preadditiveYoneda.obj J).PreservesEpimorphisms := by
  exact (injective_iff_preservesEpimorphisms_yoneda_obj J).trans <| Iff.intro
    (fun h => @Functor.preservesEpimorphisms_of_preserves_of_reflects _ _ _ _ _ _
      (preadditiveYoneda.obj J) (forget AddCommGrpCat) h inferInstance)
    (fun h => @Functor.preservesEpimorphisms_comp _ _ _ _ _ _
      (preadditiveYoneda.obj J) (forget AddCommGrpCat) h inferInstance)

theorem injective_iff_preservesEpimorphisms_preadditive_yoneda_obj' (J : C) :
    Injective J ↔ (preadditiveYonedaObj J).PreservesEpimorphisms := by
  exact (injective_iff_preservesEpimorphisms_preadditiveYoneda_obj J).trans <| Iff.intro
    (fun h => @Functor.preservesEpimorphisms_of_preserves_of_reflects _ _ _ _ _ _
      (preadditiveYonedaObj J) (forget₂ _ _) h inferInstance)
    (fun h => @Functor.preservesEpimorphisms_comp _ _ _ _ _ _
      (preadditiveYonedaObj J) (forget₂ _ _) h inferInstance)

end Injective

end Preadditive

end CategoryTheory
