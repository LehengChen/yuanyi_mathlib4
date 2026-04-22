/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts

/-!
# Constructors for combining (co)fans

We provide constructors for combining (co)fans and show their (co)limit properties.

## TODO

* Combine (co)fans on sigma types

-/

@[expose] public section

universe u₁ u₂

namespace CategoryTheory

namespace Limits

variable {C : Type u₁} [Category.{u₂} C]

namespace Fan

variable {ι₁ ι₂ : Type*} {X : C} {f₁ : ι₁ → C} {f₂ : ι₂ → C}
    (c₁ : Fan f₁) (c₂ : Fan f₂) (bc : BinaryFan c₁.pt c₂.pt)
    (h₁ : IsLimit c₁) (h₂ : IsLimit c₂) (h : IsLimit bc)

/-- For fans on maps `f₁ : ι₁ → C`, `f₂ : ι₂ → C` and a binary fan on their
cone points, construct one family of morphisms indexed by `ι₁ ⊕ ι₂` -/
@[simp]
abbrev combPairHoms : (i : ι₁ ⊕ ι₂) → bc.pt ⟶ Sum.elim f₁ f₂ i
  | .inl a => bc.fst ≫ c₁.proj a
  | .inr a => bc.snd ≫ c₂.proj a

variable {c₁ c₂ bc}

set_option backward.isDefEq.respectTransparency false in
/-- If `c₁` and `c₂` are limit fans and `bc` is a limit binary fan on their cone
points, then the fan constructed from `combPairHoms` is a limit cone. -/
def combPairIsLimit : IsLimit (Fan.mk bc.pt (combPairHoms c₁ c₂ bc)) :=
  mkFanLimit _
    (fun s ↦ (BinaryFan.IsLimit.lift' (W := s.pt) h
      (Fan.IsLimit.lift h₁ (fun a ↦ s.proj (Sum.inl a)))
      (Fan.IsLimit.lift h₂ (fun a ↦ s.proj (Sum.inr a)))).1)
    (uniq := fun s m hm ↦ BinaryFan.IsLimit.hom_ext h
      (Fan.IsLimit.hom_ext h₁ _ _
        (fun a ↦ by simpa [combPairHoms, Category.assoc] using hm (Sum.inl a)))
      (Fan.IsLimit.hom_ext h₂ _ _
        (fun a ↦ by simpa [combPairHoms, Category.assoc] using hm (Sum.inr a))))

end Fan

namespace Cofan

variable {ι₁ ι₂ : Type*} {X : C} {f₁ : ι₁ → C} {f₂ : ι₂ → C}
    (c₁ : Cofan f₁) (c₂ : Cofan f₂) (bc : BinaryCofan c₁.pt c₂.pt)
    (h₁ : IsColimit c₁) (h₂ : IsColimit c₂) (h : IsColimit bc)

/-- For cofans on maps `f₁ : ι₁ → C`, `f₂ : ι₂ → C` and a binary cofan on their
cocone points, construct one family of morphisms indexed by `ι₁ ⊕ ι₂` -/
@[simp]
abbrev combPairHoms : (i : ι₁ ⊕ ι₂) → Sum.elim f₁ f₂ i ⟶ bc.pt
  | .inl a => c₁.inj a ≫ bc.inl
  | .inr a => c₂.inj a ≫ bc.inr

variable {c₁ c₂ bc}

set_option backward.isDefEq.respectTransparency false in
/-- If `c₁` and `c₂` are colimit cofans and `bc` is a colimit binary cofan on their cocone
points, then the cofan constructed from `combPairHoms` is a colimit cocone. -/
def combPairIsColimit : IsColimit (Cofan.mk bc.pt (combPairHoms c₁ c₂ bc)) :=
  mkCofanColimit _
    (fun s ↦ (BinaryCofan.IsColimit.desc' (W := s.pt) h
      (Cofan.IsColimit.desc h₁ (fun a ↦ s.inj (Sum.inl a)))
      (Cofan.IsColimit.desc h₂ (fun a ↦ s.inj (Sum.inr a)))).1)
    (uniq := fun s m hm ↦ BinaryCofan.IsColimit.hom_ext h
      (Cofan.IsColimit.hom_ext h₁ _ _
        (fun a ↦ by simpa [combPairHoms, Category.assoc] using hm (Sum.inl a)))
      (Cofan.IsColimit.hom_ext h₂ _ _
        (fun a ↦ by simpa [combPairHoms, Category.assoc] using hm (Sum.inr a))))

end Cofan

end Limits

end CategoryTheory
