/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.BifunctorCokernel
public import Mathlib.CategoryTheory.Monoidal.Preadditive

/-!
# Tensor products of cokernels

Let `c₁` and `c₂` be cokernel coforks for morphisms `f₁ : X₁ ⟶ Y₁` and
`f₂ : X₂ ⟶ Y₂` in a monoidal preadditive category. We define a cokernel
cofork for `(X₁ ⊗ Y₂) ⨿ (Y₁ ⊗ X₂) ⟶ Y₁ ⊗ Y₂` with point `c₁.pt ⊗ c₂.pt`,
and show that it is colimit if `c₁` and `c₂` are colimit, and the
cokernels of `f₁` and `f₂` are preserved by suitable tensor products.

-/

@[expose] public section

namespace CategoryTheory.Limits.CokernelCofork

open MonoidalCategory MonoidalPreadditive

variable {C : Type*} [Category* C]
  [Preadditive C] [MonoidalCategory C] [MonoidalPreadditive C]
  {X₁ Y₁ : C} {f₁ : X₁ ⟶ Y₁} {c₁ : CokernelCofork f₁} (hc₁ : IsColimit c₁)
  {X₂ Y₂ : C} {f₂ : X₂ ⟶ Y₂} {c₂ : CokernelCofork f₂} (hc₂ : IsColimit c₂)
  [HasBinaryCoproduct (X₁ ⊗ Y₂) (Y₁ ⊗ X₂)]

variable (c₁ c₂) in
/-- Given two cokernel coforks `c₁` and `c₂` for `f₁ : X₁ ⟶ Y₁` and `f₂ : X₂ ⟶ Y₂`,
this is the cokernel cofork for `(X₁ ⊗ Y₂) ⨿ (Y₁ ⊗ X₂) ⟶ Y₁ ⊗ Y₂` with
point `c₁.pt ⊗ c₂.pt`. -/
noncomputable abbrev tensor : CokernelCofork (coprod.desc (f₁ ▷ Y₂) (Y₁ ◁ f₂)) :=
  CokernelCofork.ofπ (c₁.π ⊗ₘ c₂.π) (by
    ext
    · simp [tensorHom_def, ← comp_whiskerRight_assoc, coprod.inl_desc]
    · simp [tensorHom_def', ← whiskerLeft_comp_assoc, coprod.inr_desc])

/-- Given two colimit cokernel coforks `c₁` and `c₂` for `f₁ : X₁ ⟶ Y₁` and
`f₂ : X₂ ⟶ Y₂`, if the cokernel of `f₂` is preserved by tensoring on the left
with `c₁.pt`, the cokernel of `f₁` is preserved by tensoring on the right with `Y₂`,
and `c₁.π ▷ X₂` is an epimorphism, then `c₁.pt ⊗ c₂.pt` is the cokernel of the
morphism `(X₁ ⊗ Y₂) ⨿ (Y₁ ⊗ X₂) ⟶ Y₁ ⊗ Y₂`. -/
noncomputable def isColimitTensor
    [PreservesColimit (parallelPair f₂ 0) (tensorLeft c₁.pt)]
    [PreservesColimit (parallelPair f₁ 0) (tensorRight Y₂)]
    [Epi (c₁.π ▷ X₂)] :
    IsColimit (c₁.tensor c₂) := by
  haveI : HasBinaryCoproduct (((curriedTensor C).obj X₁).obj Y₂)
    (((curriedTensor C).obj Y₁).obj X₂) := by assumption
  let F := curriedTensor C
  have exists_desc
      (s : CokernelCofork (coprod.desc ((F.map f₁).app Y₂) ((F.obj Y₁).map f₂))) :
      ∃ (l : (F.obj c₁.pt).obj c₂.pt ⟶ s.pt),
        (F.map c₁.π).app Y₂ ≫ (F.obj c₁.pt).map c₂.π ≫ l = s.π := by
    obtain ⟨l, hl⟩ := Cofork.IsColimit.desc' (mapIsColimit _ hc₁ (F.flip.obj Y₂))
      s.π (by
        have hcondition := coprod.inl ≫= s.condition
        rw [coprod.inl_desc_assoc, comp_zero] at hcondition
        rwa [zero_comp])
    obtain ⟨l', hl'⟩ := Cofork.IsColimit.desc' (mapIsColimit _ hc₂ (F.obj c₁.pt))
      l (by
        have hcondition := coprod.inr ≫= s.condition
        rw [coprod.inr_desc_assoc, ← dsimp% hl] at hcondition
        dsimp [CokernelCofork.map, CokernelCofork.ofπ, Cofork.ofπ] at hcondition
        change (F.obj Y₁).map f₂ ≫ (F.map c₁.π).app Y₂ ≫ l = coprod.inr ≫ 0
          at hcondition
        rw [NatTrans.naturality_assoc, comp_zero] at hcondition
        haveI : Epi ((F.map c₁.π).app X₂) := by
          simpa [F] using (inferInstance : Epi (c₁.π ▷ X₂))
        rw [← cancel_epi ((F.map c₁.π).app X₂)]
        simpa [Category.assoc] using hcondition)
    exact ⟨l', by cat_disch⟩
  have h : IsColimit (c₁.mapBifunctor c₂ F) :=
    Cofork.IsColimit.mk _
      (fun s ↦ (exists_desc s).choose)
      (fun s ↦ by simpa using (exists_desc s).choose_spec)
      (fun s m hm ↦ isColimitMapBifunctor.hom_ext hc₁ hc₂ F (by
        dsimp
        rw [(exists_desc s).choose_spec, ← dsimp% hm, Category.assoc]))
  exact IsColimit.ofIsoColimit h
    (Cofork.ext (Iso.refl _) (by dsimp only [Cofork.π]; simp [F, tensorHom_def]))

end CategoryTheory.Limits.CokernelCofork
