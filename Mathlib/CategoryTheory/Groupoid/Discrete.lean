/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Groupoid
public import Mathlib.CategoryTheory.Discrete.Basic
/-!

# Discrete categories are groupoids
-/

@[expose] public section

namespace CategoryTheory

variable {C : Type*}

instance : Groupoid (Discrete C) := { inv := fun h ↦ ⟨⟨h.1.1.symm⟩⟩ }

instance (priority := 100) [Category* C] [∀ {X Y : C} (f : X ⟶ Y), IsIso f] : IsGroupoid C where

end CategoryTheory
