/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Mono

/-!
# Relation between mono/epi and pullback/pushout squares

In this file, monomorphisms and epimorphisms are characterized in terms
of pullback and pushout squares. For example, we obtain `mono_iff_isPullback`
which asserts that a morphism `f : X ⟶ Y` is a monomorphism iff the obvious
square

```
X ⟶ X
|   |
v   v
X ⟶ Y
```

is a pullback square.


-/

public section

namespace CategoryTheory

open Category Limits

variable {C : Type*} [Category* C] {X Y : C} {f : X ⟶ Y}

section Mono

variable {c : PullbackCone f f}

lemma mono_iff_fst_eq_snd
    (hc : ∀ {Z : C} (g g' : Z ⟶ X), g ≫ f = g' ≫ f →
      { φ : Z ⟶ c.pt // φ ≫ c.fst = g ∧ φ ≫ c.snd = g' }) :
    Mono f ↔ c.fst = c.snd := by
  constructor
  · intro hf
    simpa only [← cancel_mono f] using c.condition
  · intro hf
    constructor
    intro Z g g' h
    obtain ⟨φ, rfl, rfl⟩ := hc g g' h
    rw [hf]

lemma mono_iff_isIso_fst (hc : IsLimit c) : Mono f ↔ IsIso c.fst := by
  rw [mono_iff_fst_eq_snd (c := c) (fun {Z} g g' h =>
    PullbackCone.IsLimit.lift' hc (W := Z) g g' h)]
  constructor
  · intro h
    obtain ⟨φ, hφ₁, hφ₂⟩ := PullbackCone.IsLimit.lift' hc (𝟙 X) (𝟙 X) (by simp)
    refine ⟨φ, PullbackCone.IsLimit.hom_ext hc ?_ ?_, hφ₁⟩
    · simp only [assoc, hφ₁, id_comp, comp_id]
    · simp only [assoc, hφ₂, id_comp, comp_id, h]
  · intro
    obtain ⟨φ, hφ₁, hφ₂⟩ := PullbackCone.IsLimit.lift' hc (𝟙 X) (𝟙 X) (by simp)
    have : IsSplitEpi φ := IsSplitEpi.mk ⟨SplitEpi.mk c.fst (by
      rw [← cancel_mono c.fst, assoc, id_comp, hφ₁, comp_id])⟩
    rw [← cancel_epi φ, hφ₁, hφ₂]

lemma mono_iff_isIso_snd (hc : IsLimit c) : Mono f ↔ IsIso c.snd :=
  mono_iff_isIso_fst (PullbackCone.flipIsLimit hc)

variable (f)

lemma mono_iff_isPullback : Mono f ↔ IsPullback (𝟙 X) (𝟙 X) f f := by
  constructor
  · intro
    exact IsPullback.of_isLimit (PullbackCone.isLimitMkIdId f)
  · intro hf
    exact (mono_iff_fst_eq_snd (fun {Z} g g' h =>
      PullbackCone.IsLimit.lift' hf.isLimit (W := Z) g g' h)).2 rfl

end Mono

section Epi

variable {c : PushoutCocone f f}

lemma epi_iff_inl_eq_inr
    (hc : ∀ {Z : C} (g g' : Y ⟶ Z), f ≫ g = f ≫ g' →
      { φ : c.pt ⟶ Z // c.inl ≫ φ = g ∧ c.inr ≫ φ = g' }) :
    Epi f ↔ c.inl = c.inr := by
  constructor
  · intro hf
    simpa only [← cancel_epi f] using c.condition
  · intro hf
    constructor
    intro Z g g' h
    obtain ⟨φ, rfl, rfl⟩ := hc g g' h
    rw [hf]

lemma epi_iff_isIso_inl (hc : IsColimit c) : Epi f ↔ IsIso c.inl := by
  rw [epi_iff_inl_eq_inr (c := c) (fun {Z} g g' h =>
    PushoutCocone.IsColimit.desc' hc (W := Z) g g' h)]
  constructor
  · intro h
    obtain ⟨φ, hφ₁, hφ₂⟩ := PushoutCocone.IsColimit.desc' hc (𝟙 Y) (𝟙 Y) (by simp)
    refine ⟨φ, hφ₁, PushoutCocone.IsColimit.hom_ext hc ?_ ?_⟩
    · simp only [comp_id, reassoc_of% hφ₁]
    · simp only [comp_id, h, reassoc_of% hφ₂]
  · intro
    obtain ⟨φ, hφ₁, hφ₂⟩ := PushoutCocone.IsColimit.desc' hc (𝟙 Y) (𝟙 Y) (by simp)
    have : IsSplitMono φ := IsSplitMono.mk ⟨SplitMono.mk c.inl (by
      rw [← cancel_epi c.inl, reassoc_of% hφ₁, comp_id])⟩
    rw [← cancel_mono φ, hφ₁, hφ₂]

lemma epi_iff_isIso_inr (hc : IsColimit c) : Epi f ↔ IsIso c.inr :=
  epi_iff_isIso_inl (PushoutCocone.flipIsColimit hc)

variable (f)

lemma epi_iff_isPushout : Epi f ↔ IsPushout f f (𝟙 Y) (𝟙 Y) := by
  constructor
  · intro
    exact IsPushout.of_isColimit (PushoutCocone.isColimitMkIdId f)
  · intro hf
    exact (epi_iff_inl_eq_inr (fun {Z} g g' h =>
      PushoutCocone.IsColimit.desc' hf.isColimit (W := Z) g g' h)).2 rfl

end Epi

end CategoryTheory
