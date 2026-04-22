/-
Copyright (c) 2025 Jon Eugster. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, Jon Eugster, Emily Riehl
-/
module

public import Mathlib.CategoryTheory.Enriched.Limits.HasConicalProducts

/-!
# Existence of conical terminal objects
-/

@[expose] public section

universe w v' v u u'

namespace CategoryTheory.Enriched

open Limits HasConicalLimit

/-- A category has a conical terminal object
if it has a conical limit over the empty diagram. -/
abbrev HasConicalTerminal := HasConicalLimitsOfShape (Discrete.{0} PEmpty)

variable (V : Type u') [Category.{v'} V] [MonoidalCategory V]
variable (C : Type u) [Category.{v} C] [EnrichedOrdinaryCategory V C]

example [HasConicalTerminal V C] : HasTerminal C := inferInstance

instance HasConicalProducts.hasConicalTerminal [HasConicalLimit V (Functor.empty.{w} C)] :
    HasConicalTerminal V C :=
  { hasConicalLimit F := by
      let G : Discrete.{w} PEmpty ⥤ Discrete.{0} PEmpty := emptyEquivalence.functor
      haveI : HasConicalLimit V (G ⋙ F) :=
        HasConicalLimit.of_iso V (Functor.uniqueFromEmpty (G ⋙ F)).symm
      exact HasConicalLimit.of_equiv_comp V F G }

end CategoryTheory.Enriched
