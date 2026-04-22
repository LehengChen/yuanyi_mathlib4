/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.CategoryTheory.Filtered.Connected
public import Mathlib.CategoryTheory.Limits.Preserves.Filtered

/-!

# Forgetful functors from `Over X` and `Under X` preserve connected (co)limits

Note that `Over.forget X : Over X ⥤ C` already preserves all colimits because it is a left adjoint.
See `Mathlib/CategoryTheory/Comma/Over/Pullback.lean`

The filtered and cofiltered preservation instances follow from the stronger connected-shape
instances.

-/

@[expose] public section

namespace CategoryTheory.Limits

variable {C : Type*} [Category* C]

attribute [local instance] IsFiltered.nonempty IsCofiltered.nonempty
attribute [local instance] IsFiltered.isConnected IsCofiltered.isConnected

set_option backward.isDefEq.respectTransparency false in
instance {J : Type*} [Category* J] [IsConnected J] {X : C} :
    PreservesLimitsOfShape J (Over.forget X) := by
  refine ⟨fun {F} ↦ ⟨fun {c} hc ↦ ⟨.ofExistsUnique fun s ↦ ?_⟩⟩⟩
  let i : J := Classical.arbitrary J
  let s' : Cone F := ⟨Over.mk (s.π.app i ≫ (F.obj i).hom), fun j ↦ Over.homMk (s.π.app j) (by
    let z : (Functor.const J).obj s.pt ⟶ (Functor.const J).obj X :=
      { app := fun j ↦ s.π.app j ≫ (F.obj j).hom
        naturality := by
          intro j k e
          simp only [Functor.const_obj_obj, Functor.const_obj_map, Functor.comp_obj,
            Over.forget_obj, Category.id_comp, Category.comp_id]
          rw [← s.w e]
          change (s.π.app j ≫ (F.map e).left) ≫ (F.obj k).hom =
            s.π.app j ≫ (F.obj j).hom
          rw [Category.assoc, Over.w (F.map e)] }
    exact nat_trans_from_is_connected z j i), fun j k e ↦ by ext; simpa using (s.w e).symm⟩
  refine ⟨(hc.lift s').left, fun j ↦ congr($(hc.fac s' j).left), fun f hf ↦ ?_⟩
  dsimp at hf
  exact congr($(hc.uniq s' (Over.homMk f (by simp [s', ← hf]))
    fun j ↦ Over.OverMorphism.ext (hf j)).left)

instance {X : C} : PreservesCofilteredLimitsOfSize (Over.forget X) where
  preserves_cofiltered_limits _ := inferInstance

set_option backward.isDefEq.respectTransparency false in
instance {J : Type*} [Category* J] [IsConnected J] {X : C} :
    PreservesColimitsOfShape J (Under.forget X) := by
  refine ⟨fun {F} ↦ ⟨fun {c} hc ↦ ⟨.ofExistsUnique fun s ↦ ?_⟩⟩⟩
  let i : J := Classical.arbitrary J
  let s' : Cocone F := ⟨Under.mk ((F.obj i).hom ≫ s.ι.app i), fun j ↦ Under.homMk (s.ι.app j) (by
    let z : (Functor.const J).obj X ⟶ (Functor.const J).obj s.pt :=
      { app := fun j ↦ (F.obj j).hom ≫ s.ι.app j
        naturality := by
          intro j k e
          simp only [Functor.const_obj_obj, Functor.const_obj_map, Functor.id_obj,
            Category.id_comp, Category.comp_id]
          rw [← s.w e]
          change (F.obj k).hom ≫ s.ι.app k =
            (F.obj j).hom ≫ (F.map e).right ≫ s.ι.app k
          rw [← Category.assoc, Under.w (F.map e)] }
    exact nat_trans_from_is_connected z j i), fun j k e ↦ by ext; simpa using s.w e⟩
  refine ⟨(hc.desc s').right, fun j ↦ congr($(hc.fac s' j).right), fun f hf ↦ ?_⟩
  dsimp at hf
  exact congr($(hc.uniq s' (Under.homMk f (by simp [s', ← hf]))
    fun j ↦ Under.UnderMorphism.ext (hf j)).right)

instance {X : C} : PreservesFilteredColimitsOfSize (Under.forget X) where
  preserves_filtered_colimits _ := inferInstance

end CategoryTheory.Limits
