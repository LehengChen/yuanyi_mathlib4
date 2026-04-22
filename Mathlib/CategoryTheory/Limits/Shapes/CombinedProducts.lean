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
    (fun s ↦ Fan.IsLimit.lift h <| fun i ↦ by
      cases i
      · exact Fan.IsLimit.lift h₁ (fun a ↦ s.proj (.inl a))
      · exact Fan.IsLimit.lift h₂ (fun a ↦ s.proj (.inr a)))
    (fun s w ↦ by
      cases w with
      | inl a =>
          simp only [fan_mk_proj, combPairHoms]
          let fstLift : s.pt ⟶ c₁.pt := Fan.IsLimit.lift h₁ (fun a ↦ s.proj (.inl a))
          let sndLift : s.pt ⟶ c₂.pt := Fan.IsLimit.lift h₂ (fun a ↦ s.proj (.inr a))
          let t : Fan (pairFunction c₁.pt c₂.pt) := Fan.mk s.pt (fun i ↦ by
            cases i
            · exact fstLift
            · exact sndLift)
          have hfst :
              Fan.IsLimit.lift h
                  (fun i ↦ by
                    cases i
                    · exact fstLift
                    · exact sndLift) ≫
                bc.fst =
              fstLift := by
            exact h.fac t ⟨WalkingPair.left⟩
          have hcomp :
              Fan.IsLimit.lift h
                  (fun i ↦ by
                    cases i
                    · exact fstLift
                    · exact sndLift) ≫
                bc.fst ≫ c₁.proj a =
              fstLift ≫ c₁.proj a := by
            have hcomp := congrArg (fun k => k ≫ c₁.proj a) hfst
            simp only [Category.assoc] at hcomp
            exact hcomp
          calc
            Fan.IsLimit.lift h
                (fun i ↦ by
                  cases i
                  · exact fstLift
                  · exact sndLift) ≫
                bc.fst ≫ c₁.proj a
              = fstLift ≫ c₁.proj a := hcomp
            _ = s.proj (.inl a) := by
                exact Fan.IsLimit.fac h₁ (fun a ↦ s.proj (.inl a)) a
      | inr a =>
          simp only [fan_mk_proj, combPairHoms]
          let fstLift : s.pt ⟶ c₁.pt := Fan.IsLimit.lift h₁ (fun a ↦ s.proj (.inl a))
          let sndLift : s.pt ⟶ c₂.pt := Fan.IsLimit.lift h₂ (fun a ↦ s.proj (.inr a))
          let t : Fan (pairFunction c₁.pt c₂.pt) := Fan.mk s.pt (fun i ↦ by
            cases i
            · exact fstLift
            · exact sndLift)
          have hsnd :
              Fan.IsLimit.lift h
                  (fun i ↦ by
                    cases i
                    · exact fstLift
                    · exact sndLift) ≫
                bc.snd =
              sndLift := by
            exact h.fac t ⟨WalkingPair.right⟩
          have hcomp :
              Fan.IsLimit.lift h
                  (fun i ↦ by
                    cases i
                    · exact fstLift
                    · exact sndLift) ≫
                bc.snd ≫ c₂.proj a =
              sndLift ≫ c₂.proj a := by
            have hcomp := congrArg (fun k => k ≫ c₂.proj a) hsnd
            simp only [Category.assoc] at hcomp
            exact hcomp
          calc
            Fan.IsLimit.lift h
                (fun i ↦ by
                  cases i
                  · exact fstLift
                  · exact sndLift) ≫
                bc.snd ≫ c₂.proj a
              = sndLift ≫ c₂.proj a := hcomp
            _ = s.proj (.inr a) := by
                exact Fan.IsLimit.fac h₂ (fun a ↦ s.proj (.inr a)) a)
    (fun s m hm ↦ Fan.IsLimit.hom_ext h _ _ <| fun w ↦ by
      cases w
      · refine Fan.IsLimit.hom_ext h₁ _ _ (fun a ↦ by aesop)
      · refine Fan.IsLimit.hom_ext h₂ _ _ (fun a ↦ by aesop))

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
    (fun s ↦ Cofan.IsColimit.desc h <| fun i ↦ by
      cases i
      · exact Cofan.IsColimit.desc h₁ (fun a ↦ s.inj (.inl a))
      · exact Cofan.IsColimit.desc h₂ (fun a ↦ s.inj (.inr a)))
    (fun s w ↦ by
      cases w with
      | inl a =>
          simp only [cofan_mk_inj, combPairHoms, Category.assoc]
          let inlDesc : c₁.pt ⟶ s.pt := Cofan.IsColimit.desc h₁ (fun a ↦ s.inj (.inl a))
          let inrDesc : c₂.pt ⟶ s.pt := Cofan.IsColimit.desc h₂ (fun a ↦ s.inj (.inr a))
          let t : Cofan (pairFunction c₁.pt c₂.pt) := Cofan.mk s.pt (fun i ↦ by
            cases i
            · exact inlDesc
            · exact inrDesc)
          have hinl :
              bc.inl ≫
                  Cofan.IsColimit.desc h
                    (fun i ↦ by
                      cases i
                      · exact inlDesc
                      · exact inrDesc) =
                inlDesc := by
            exact h.fac t ⟨WalkingPair.left⟩
          have hcomp :
              c₁.inj a ≫ bc.inl ≫
                  Cofan.IsColimit.desc h
                    (fun i ↦ by
                      cases i
                      · exact inlDesc
                      · exact inrDesc) =
                c₁.inj a ≫ inlDesc := by
            have hcomp := congrArg (fun k => c₁.inj a ≫ k) hinl
            exact hcomp
          calc
            c₁.inj a ≫ bc.inl ≫
                Cofan.IsColimit.desc h
                  (fun i ↦ by
                    cases i
                    · exact inlDesc
                    · exact inrDesc)
              = c₁.inj a ≫ inlDesc := hcomp
            _ = s.inj (.inl a) := by
                exact Cofan.IsColimit.fac h₁ (fun a ↦ s.inj (.inl a)) a
      | inr a =>
          simp only [cofan_mk_inj, combPairHoms, Category.assoc]
          let inlDesc : c₁.pt ⟶ s.pt := Cofan.IsColimit.desc h₁ (fun a ↦ s.inj (.inl a))
          let inrDesc : c₂.pt ⟶ s.pt := Cofan.IsColimit.desc h₂ (fun a ↦ s.inj (.inr a))
          let t : Cofan (pairFunction c₁.pt c₂.pt) := Cofan.mk s.pt (fun i ↦ by
            cases i
            · exact inlDesc
            · exact inrDesc)
          have hinr :
              bc.inr ≫
                  Cofan.IsColimit.desc h
                    (fun i ↦ by
                      cases i
                      · exact inlDesc
                      · exact inrDesc) =
                inrDesc := by
            exact h.fac t ⟨WalkingPair.right⟩
          have hcomp :
              c₂.inj a ≫ bc.inr ≫
                  Cofan.IsColimit.desc h
                    (fun i ↦ by
                      cases i
                      · exact inlDesc
                      · exact inrDesc) =
                c₂.inj a ≫ inrDesc := by
            have hcomp := congrArg (fun k => c₂.inj a ≫ k) hinr
            exact hcomp
          calc
            c₂.inj a ≫ bc.inr ≫
                Cofan.IsColimit.desc h
                  (fun i ↦ by
                    cases i
                    · exact inlDesc
                    · exact inrDesc)
              = c₂.inj a ≫ inrDesc := hcomp
            _ = s.inj (.inr a) := by
                exact Cofan.IsColimit.fac h₂ (fun a ↦ s.inj (.inr a)) a)
    (fun s m hm ↦ Cofan.IsColimit.hom_ext h _ _ <| fun w ↦ by
      cases w
      · refine Cofan.IsColimit.hom_ext h₁ _ _ (fun a ↦ by aesop)
      · refine Cofan.IsColimit.hom_ext h₂ _ _ (fun a ↦ by aesop))

end Cofan

end Limits

end CategoryTheory
