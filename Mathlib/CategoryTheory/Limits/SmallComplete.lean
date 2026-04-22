/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.SetTheory.Cardinal.Basic

/-!
# Any small complete category is a preorder

We show that any small category with sufficiently large powers is a preorder: In particular, it
suffices for each object of `C` to have a product indexed by the type of morphisms in `C`; this
follows if a small category `C` in universe `u` has products of size `u`.
Note that in Lean, a preorder category is strictly one where the morphisms are in `Prop`, so
we instead show that the homsets are subsingleton.

## References

* https://ncatlab.org/nlab/show/complete+small+category#in_classical_logic

## Tags

small complete, preorder, Freyd
-/

@[expose] public section


namespace CategoryTheory

open Category Limits

open Cardinal

universe u

variable {C : Type u} [SmallCategory C]
    [∀ Y : C, HasProduct (fun _ : Σ Z W : C, Z ⟶ W => Y)]

set_option backward.isDefEq.respectTransparency false in
/-- A small category with powers indexed by its type of morphisms is a thin category.

in Lean, a preorder category is one where the morphisms are in Prop, which is weaker than the usual
notion of a preorder/thin category which says that each homset is subsingleton; we show the latter
rather than providing a `Preorder C` instance.
-/
instance (priority := 100) : Quiver.IsThin C := fun X Y =>
  ⟨fun r s => by
    classical
      by_contra r_ne_s
      have z : (2 : Cardinal) ≤ #(X ⟶ Y) := by
        rw [Cardinal.two_le_iff]
        exact ⟨_, _, r_ne_s⟩
      let md := Σ Z W : C, Z ⟶ W
      let α := #md
      apply not_le_of_gt (Cardinal.cantor α)
      let yp : C := ∏ᶜ fun _ : md => Y
      apply _root_.trans _ _
      · exact #(X ⟶ yp)
      · apply le_trans (Cardinal.power_le_power_right z)
        rw [Cardinal.power_def]
        apply le_of_eq
        rw [Cardinal.eq]
        refine ⟨⟨Pi.lift, fun f k => f ≫ Pi.π _ k, ?_, ?_⟩⟩
        · intro f
          ext k
          simp [yp]
        · intro f
          ext ⟨j⟩
          simp [yp]
      · apply Cardinal.mk_le_of_injective _
        · intro f
          exact ⟨_, _, f⟩
        · rintro f g k
          cases k
          rfl⟩

end CategoryTheory
