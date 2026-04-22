/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-!
# Transporting existence of specific limits across equivalences

For now, we only treat the case of initial and terminal objects, but other special shapes can be
added in the future.
-/

public section


open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

theorem hasInitial_of_equivalence (e : D ⥤ C) [e.Full] [e.Faithful] [e.EssSurj]
    [HasInitial C] : HasInitial D := by
  let I : D := e.objPreimage (⊥_ C)
  have hI : IsInitial (e.obj I) :=
    IsInitial.ofIso initialIsInitial (e.objObjPreimageIso (⊥_ C)).symm
  exact (@IsInitial.hasInitial D _ I <|
    IsInitial.ofUniqueHom (fun Y => e.preimage (hI.to (e.obj Y))) fun Y f => by
      apply e.map_injective
      rw [e.map_preimage]
      exact hI.hom_ext _ _)

theorem Equivalence.hasInitial_iff (e : C ≌ D) : HasInitial C ↔ HasInitial D :=
  ⟨fun (_ : HasInitial C) => hasInitial_of_equivalence e.inverse,
    fun (_ : HasInitial D) => hasInitial_of_equivalence e.functor⟩

theorem hasTerminal_of_equivalence (e : D ⥤ C) [e.Full] [e.Faithful] [e.EssSurj]
    [HasTerminal C] : HasTerminal D := by
  let T : D := e.objPreimage (⊤_ C)
  have hT : IsTerminal (e.obj T) :=
    IsTerminal.ofIso terminalIsTerminal (e.objObjPreimageIso (⊤_ C)).symm
  exact (@IsTerminal.hasTerminal D _ T <|
    IsTerminal.ofUniqueHom (fun Y => e.preimage (hT.from (e.obj Y))) fun Y f => by
      apply e.map_injective
      rw [e.map_preimage]
      exact hT.hom_ext _ _)

theorem Equivalence.hasTerminal_iff (e : C ≌ D) : HasTerminal C ↔ HasTerminal D :=
  ⟨fun (_ : HasTerminal C) => hasTerminal_of_equivalence e.inverse,
    fun (_ : HasTerminal D) => hasTerminal_of_equivalence e.functor⟩

end CategoryTheory
