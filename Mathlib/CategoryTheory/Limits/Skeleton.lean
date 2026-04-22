/-
Copyright (c) 2025 Fernando Chu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Chu
-/
module

public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Skeletal

/-!
# (Co)limits of the skeleton of a category

The skeleton of a category inherits all (co)limits the category has.

## Implementation notes

Because the category instance of `ThinSkeleton C` comes from its `Preorder` instance, it is not the
case that `HasLimits C` iff `HasLimits (ThinSkeleton C)`, as the homs live in different universes.
If this is something we really want, we should consider changing the category instance of
`ThinSkeleton C`.
-/

@[expose] public section

noncomputable section

open CategoryTheory ThinSkeleton

namespace CategoryTheory.Limits

universe v₁ u₁ v₂ u₂ v₃ u₃ w w'

variable {J : Type u₁} [Category.{v₁} J] {C : Type u₂} [Category.{v₂} C]
  {D : Type u₃} [Category.{v₃} D]

instance hasLimitsOfShape_skeleton [HasLimitsOfShape J C] : HasLimitsOfShape J (Skeleton C) :=
  hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape (fromSkeleton C)

instance hasLimitsOfSize_skeleton [HasLimitsOfSize.{w, w'} C] :
    HasLimitsOfSize.{w, w'} (Skeleton C) :=
  hasLimits_of_hasLimits_createsLimits (fromSkeleton C)

example [HasLimits C] : HasLimits (Skeleton C) := by infer_instance

instance hasColimitsOfShape_skeleton [HasColimitsOfShape J C] : HasColimitsOfShape J (Skeleton C) :=
  hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape (fromSkeleton C)

instance hasColimitsOfSize_skeleton [HasColimitsOfSize.{w, w'} C] :
    HasColimitsOfSize.{w, w'} (Skeleton C) :=
  hasColimits_of_hasColimits_createsColimits (fromSkeleton C)

example [HasColimits C] : HasColimits (Skeleton C) := by infer_instance

instance hasLimitsOfShape_thinSkeleton [Quiver.IsThin C] [HasLimitsOfShape J C] :
    HasLimitsOfShape J (ThinSkeleton C) :=
  hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape (fromThinSkeleton C)

instance hasLimitsOfSize_thinSkeleton [HasProducts.{w'} C] :
    HasLimitsOfSize.{w, w'} (ThinSkeleton C) where
  has_limits_of_shape K _ :=
    letI : HasProductsOfShape K C := inferInstance
    { has_limit F := by
        let f : K → C := fun k => Quotient.out (F.obj k)
        let t : Cone F :=
          { pt := ThinSkeleton.mk (∏ᶜ f)
            π :=
              { app := fun k => homOfLE (show ThinSkeleton.mk (∏ᶜ f) ≤ F.obj k from by
                  have hk : ThinSkeleton.mk (f k) = F.obj k := by
                    dsimp [f, ThinSkeleton.mk]
                    exact Quotient.out_eq _
                  rw [← hk]
                  exact ⟨Pi.π f k⟩)
                naturality := fun _ _ _ => Subsingleton.elim _ _ } }
        exact
          ⟨t,
            { lift := fun s => homOfLE (show s.pt ≤ t.pt from by
                have hs : ThinSkeleton.mk (Quotient.out s.pt) = s.pt := Quotient.out_eq s.pt
                rw [← hs]
                exact ⟨Pi.lift fun k =>
                  (show Nonempty (Quotient.out s.pt ⟶ f k) from by
                    have hk : ThinSkeleton.mk (f k) = F.obj k := by
                      dsimp [f, ThinSkeleton.mk]
                      exact Quotient.out_eq _
                    have hle : ThinSkeleton.mk (Quotient.out s.pt) ≤ ThinSkeleton.mk (f k) := by
                      rw [hs, hk]
                      exact (s.π.app k).le
                    exact hle).some⟩)
              fac := fun _ _ => Subsingleton.elim _ _
              uniq := fun _ _ _ => Subsingleton.elim _ _ }⟩ }

instance hasColimitsOfShape_thinSkeleton [Quiver.IsThin C] [HasColimitsOfShape J C] :
    HasColimitsOfShape J (ThinSkeleton C) :=
  hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape (fromThinSkeleton C)

instance hasColimitsOfSize_thinSkeleton [HasCoproducts.{w'} C] :
    HasColimitsOfSize.{w, w'} (ThinSkeleton C) where
  has_colimits_of_shape K _ :=
    letI : HasCoproductsOfShape K C := inferInstance
    { has_colimit F := by
        let f : K → C := fun k => Quotient.out (F.obj k)
        let t : Cocone F :=
          { pt := ThinSkeleton.mk (∐ f)
            ι :=
              { app := fun k => homOfLE (show F.obj k ≤ ThinSkeleton.mk (∐ f) from by
                  have hk : ThinSkeleton.mk (f k) = F.obj k := by
                    dsimp [f, ThinSkeleton.mk]
                    exact Quotient.out_eq _
                  rw [← hk]
                  exact ⟨Sigma.ι f k⟩)
                naturality := fun _ _ _ => Subsingleton.elim _ _ } }
        exact
          ⟨t,
            { desc := fun s => homOfLE (show t.pt ≤ s.pt from by
                have hs : ThinSkeleton.mk (Quotient.out s.pt) = s.pt := Quotient.out_eq s.pt
                rw [← hs]
                exact ⟨Sigma.desc fun k =>
                  (show Nonempty (f k ⟶ Quotient.out s.pt) from by
                    have hk : ThinSkeleton.mk (f k) = F.obj k := by
                      dsimp [f, ThinSkeleton.mk]
                      exact Quotient.out_eq _
                    have hle : ThinSkeleton.mk (f k) ≤ ThinSkeleton.mk (Quotient.out s.pt) := by
                      rw [hk, hs]
                      exact (s.ι.app k).le
                    exact hle).some⟩)
              fac := fun _ _ => Subsingleton.elim _ _
              uniq := fun _ _ _ => Subsingleton.elim _ _ }⟩ }

end CategoryTheory.Limits
