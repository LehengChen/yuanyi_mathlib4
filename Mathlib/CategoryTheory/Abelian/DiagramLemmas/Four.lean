/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Joël Riou
-/
module

public import Mathlib.Algebra.Homology.ExactSequence
public import Mathlib.CategoryTheory.Abelian.Refinements

/-!
# The four and five lemmas

Consider the following commutative diagram with exact rows in an abelian category `C`:

```
A ---f--> B ---g--> C ---h--> D ---i--> E
|         |         |         |         |
α         β         γ         δ         ε
|         |         |         |         |
v         v         v         v         v
A' --f'-> B' --g'-> C' --h'-> D' --i'-> E'
```

We show:
- the "mono" version of the four lemma: if `α` is an epimorphism and `β` and `δ` are monomorphisms,
  then `γ` is a monomorphism,
- the "epi" version of the four lemma: if `β` and `δ` are epimorphisms and `ε` is a monomorphism,
  then `γ` is an epimorphism,
- the five lemma: if `α` is an epimorphism, `β` and `δ` are both monomorphisms
  and epimorphisms, and `ε` is a monomorphism, then `γ` is an isomorphism.

## Implementation details

The diagram of the five lemma is given by a morphism in the category `ComposableArrows C 4`
between two objects which satisfy `ComposableArrows.Exact`. Similarly, the two versions of the
four lemma are stated in terms of the category `ComposableArrows C 3`.

The five lemma is deduced from the two versions of the four lemma. Both of these versions
are proved separately. It would be easy to deduce the epi version from the mono version
using duality, but this would require lengthy API developments for `ComposableArrows` (TODO).

## Tags

four lemma, five lemma, diagram lemma, diagram chase
-/

public section


namespace CategoryTheory

open Category Limits Preadditive

namespace Abelian

variable {C : Type*} [Category* C] [Abelian C]

open ComposableArrows

section Four

variable {R₁ R₂ : ComposableArrows C 3} (φ : R₁ ⟶ R₂)

set_option backward.isDefEq.respectTransparency false in
theorem mono_of_epi_of_mono_of_mono' (hR₁ : R₁.map' 0 2 = 0)
    (hR₁' : (mk₂ (R₁.map' 1 2) (R₁.map' 2 3)).Exact)
    (hR₂ : (mk₂ (R₂.map' 0 1) (R₂.map' 1 2)).Exact)
    (h₀ : Epi (app' φ 0)) (h₁ : Mono (app' φ 1)) (h₃ : Mono (app' φ 3)) :
    Mono (app' φ 2) := by
  apply mono_of_cancel_zero
  intro A f₂ h₁
  have h₂ : f₂ ≫ R₁.map' 2 3 = 0 := by
    rw [← cancel_mono (app' φ 3 _), assoc, NatTrans.naturality, reassoc_of% h₁,
      zero_comp, zero_comp]
  obtain ⟨A₁, π₁, _, f₁, hf₁⟩ := (hR₁'.exact 0).exact_up_to_refinements f₂ h₂
  dsimp at hf₁
  have h₃ : (f₁ ≫ app' φ 1) ≫ R₂.map' 1 2 = 0 := by
    rw [assoc, ← NatTrans.naturality, ← reassoc_of% hf₁, h₁, comp_zero]
  obtain ⟨A₂, π₂, _, g₀, hg₀⟩ := (hR₂.exact 0).exact_up_to_refinements _ h₃
  obtain ⟨A₃, π₃, _, f₀, hf₀⟩ := surjective_up_to_refinements_of_epi (app' φ 0 _) g₀
  have h₄ : f₀ ≫ R₁.map' 0 1 = π₃ ≫ π₂ ≫ f₁ := by
    rw [← cancel_mono (app' φ 1 _), assoc, assoc, assoc, NatTrans.naturality,
      ← reassoc_of% hf₀, hg₀]
    rfl
  rw [← cancel_epi π₁, comp_zero, hf₁, ← cancel_epi π₂, ← cancel_epi π₃, comp_zero,
    comp_zero, ← reassoc_of% h₄, ← R₁.map'_comp 0 1 2, hR₁, comp_zero]

theorem mono_of_epi_of_mono_of_mono (hR₁ : R₁.Exact) (hR₂ : R₂.Exact)
    (h₀ : Epi (app' φ 0)) (h₁ : Mono (app' φ 1)) (h₃ : Mono (app' φ 3)) :
    Mono (app' φ 2) :=
  mono_of_epi_of_mono_of_mono' φ
    (by simpa only [R₁.map'_comp 0 1 2] using hR₁.toIsComplex.zero 0)
    (hR₁.exact 1).exact_toComposableArrows (hR₂.exact 0).exact_toComposableArrows h₀ h₁ h₃

set_option backward.isDefEq.respectTransparency false in
theorem epi_of_epi_of_epi_of_mono'
    (hR₁ : (mk₂ (R₁.map' 1 2) (R₁.map' 2 3)).Exact)
    (hR₂ : (mk₂ (R₂.map' 0 1) (R₂.map' 1 2)).Exact) (hR₂' : R₂.map' 1 3 = 0)
    (h₀ : Epi (app' φ 0)) (h₂ : Epi (app' φ 2)) (h₃ : Mono (app' φ 3)) :
    Epi (app' φ 1) := by
  rw [epi_iff_surjective_up_to_refinements]
  intro A g₁
  obtain ⟨A₁, π₁, _, f₂, h₁⟩ :=
    surjective_up_to_refinements_of_epi (app' φ 2 _) (g₁ ≫ R₂.map' 1 2)
  have h₂ : f₂ ≫ R₁.map' 2 3 = 0 := by
    rw [← cancel_mono (app' φ 3 _), assoc, zero_comp, NatTrans.naturality, ← reassoc_of% h₁,
      ← R₂.map'_comp 1 2 3, hR₂', comp_zero, comp_zero]
  obtain ⟨A₂, π₂, _, f₁, h₃⟩ := (hR₁.exact 0).exact_up_to_refinements _ h₂
  dsimp at f₁ h₃
  have h₄ : (π₂ ≫ π₁ ≫ g₁ - f₁ ≫ app' φ 1 _) ≫ R₂.map' 1 2 = 0 := by
    rw [sub_comp, assoc, assoc, assoc, ← NatTrans.naturality, ← reassoc_of% h₃, h₁, sub_self]
  obtain ⟨A₃, π₃, _, g₀, h₅⟩ := (hR₂.exact 0).exact_up_to_refinements _ h₄
  dsimp at g₀ h₅
  rw [comp_sub] at h₅
  obtain ⟨A₄, π₄, _, f₀, h₆⟩ := surjective_up_to_refinements_of_epi (app' φ 0 _) g₀
  refine ⟨A₄, π₄ ≫ π₃ ≫ π₂ ≫ π₁, inferInstance,
    π₄ ≫ π₃ ≫ f₁ + f₀ ≫ (by exact R₁.map' 0 1), ?_⟩
  rw [assoc, assoc, assoc, add_comp, assoc, assoc, assoc, NatTrans.naturality,
    ← reassoc_of% h₆, ← h₅, comp_sub]
  dsimp
  rw [add_sub_cancel]

theorem epi_of_epi_of_epi_of_mono (hR₁ : R₁.Exact) (hR₂ : R₂.Exact)
    (h₀ : Epi (app' φ 0)) (h₂ : Epi (app' φ 2)) (h₃ : Mono (app' φ 3)) :
    Epi (app' φ 1) :=
  epi_of_epi_of_epi_of_mono' φ (hR₁.exact 1).exact_toComposableArrows
    (hR₂.exact 0).exact_toComposableArrows
    (by simpa only [R₂.map'_comp 1 2 3] using hR₂.toIsComplex.zero 1) h₀ h₂ h₃

end Four

section Five

variable {R₁ R₂ : ComposableArrows C 4} (hR₁ : R₁.Exact) (hR₂ : R₂.Exact) (φ : R₁ ⟶ R₂)
include hR₁ hR₂

/-- The five lemma. -/
theorem isIso_of_epi_of_isIso_of_isIso_of_mono (h₀ : Epi (app' φ 0)) (h₁ : Mono (app' φ 1))
    (h₂ : Epi (app' φ 1)) (h₃ : Mono (app' φ 3)) (h₄ : Epi (app' φ 3))
    (h₅ : Mono (app' φ 4)) : IsIso (app' φ 2) := by
  dsimp at h₀ h₁ h₂ h₃ h₄ h₅
  have : Mono (app' φ 2) := by
    apply mono_of_epi_of_mono_of_mono (δlastFunctor.map φ) (R₁.exact_iff_δlast.1 hR₁).1
      (R₂.exact_iff_δlast.1 hR₂).1 <;> assumption
  have : Epi (app' φ 2) := by
    apply epi_of_epi_of_epi_of_mono (δ₀Functor.map φ) (R₁.exact_iff_δ₀.1 hR₁).2
      (R₂.exact_iff_δ₀.1 hR₂).2 <;> assumption
  apply isIso_of_mono_of_epi

end Five

/-! The following "three lemmas" for morphisms in `ComposableArrows C 2` are
special cases of "four lemmas" applied to diagrams where some of the
leftmost or rightmost maps (or objects) are zero. -/

section Three

variable {R₁ R₂ : ComposableArrows C 2} (φ : R₁ ⟶ R₂)

attribute [local simp] Precomp.map

set_option backward.isDefEq.respectTransparency false in
theorem mono_of_epi_of_epi_mono' (hR₁ : R₁.map' 0 2 = 0) (hR₁' : Epi (R₁.map' 1 2))
    (hR₂ : R₂.Exact) (h₀ : Epi (app' φ 0)) (h₁ : Mono (app' φ 1)) :
    Mono (app' φ 2) := by
  let ψ : mk₃ (R₁.map' 0 1) (R₁.map' 1 2) (0 : _ ⟶ R₁.obj' 0) ⟶
    mk₃ (R₂.map' 0 1) (R₂.map' 1 2) (0 : _ ⟶ R₁.obj' 0) := homMk₃ (app' φ 0) (app' φ 1)
      (app' φ 2) (𝟙 _) (naturality' φ 0 1) (naturality' φ 1 2) (by simp)
  refine mono_of_epi_of_mono_of_mono' ψ ?_ (exact₂_mk _ (by simp) ?_)
    (hR₂.exact 0).exact_toComposableArrows h₀ h₁ (by dsimp [ψ]; infer_instance)
  · dsimp
    rw [← Functor.map_comp]
    exact hR₁
  · rw [ShortComplex.exact_iff_epi _ (by simp)]
    exact hR₁'

theorem mono_of_epi_of_epi_of_mono (hR₁ : R₁.Exact) (hR₂ : R₂.Exact)
    (hR₁' : Epi (R₁.map' 1 2)) (h₀ : Epi (app' φ 0)) (h₁ : Mono (app' φ 1)) :
    Mono (app' φ 2) :=
  mono_of_epi_of_epi_mono' φ (by simpa only [map'_comp R₁ 0 1 2] using hR₁.toIsComplex.zero 0)
    hR₁' hR₂ h₀ h₁

set_option backward.isDefEq.respectTransparency false in
theorem epi_of_mono_of_epi_of_mono' (hR₁ : R₁.Exact) (hR₂ : R₂.map' 0 2 = 0)
    (hR₂' : Mono (R₂.map' 0 1)) (h₀ : Epi (app' φ 1)) (h₁ : Mono (app' φ 2)) :
    Epi (app' φ 0) := by
  let ψ : mk₃ (0 : R₁.obj' 0 ⟶ _) (R₁.map' 0 1) (R₁.map' 1 2) ⟶
    mk₃ (0 : R₁.obj' 0 ⟶ _) (R₂.map' 0 1) (R₂.map' 1 2) := homMk₃ (𝟙 _) (app' φ 0) (app' φ 1)
      (app' φ 2) (by simp) (naturality' φ 0 1) (naturality' φ 1 2)
  refine epi_of_epi_of_epi_of_mono' ψ (hR₁.exact 0).exact_toComposableArrows
    (exact₂_mk _ (by simp) ?_) ?_ (by dsimp [ψ]; infer_instance) h₀ h₁
  · rw [ShortComplex.exact_iff_mono _ (by simp)]
    exact hR₂'
  · dsimp
    rw [← Functor.map_comp]
    exact hR₂

theorem epi_of_mono_of_epi_of_mono (hR₁ : R₁.Exact) (hR₂ : R₂.Exact)
    (hR₂' : Mono (R₂.map' 0 1)) (h₀ : Epi (app' φ 1)) (h₁ : Mono (app' φ 2)) :
    Epi (app' φ 0) :=
  epi_of_mono_of_epi_of_mono' φ hR₁
    (by simpa only [map'_comp R₂ 0 1 2] using hR₂.toIsComplex.zero 0) hR₂' h₀ h₁

set_option backward.isDefEq.respectTransparency false in
theorem mono_of_mono_of_mono_of_mono (hR₁ : R₁.Exact)
    (hR₂' : Mono (R₂.map' 0 1))
    (h₀ : Mono (app' φ 0))
    (h₁ : Mono (app' φ 2)) :
    Mono (app' φ 1) := by
  let ψ : mk₃ (0 : R₁.obj' 0 ⟶ _) (R₁.map' 0 1) (R₁.map' 1 2) ⟶
    mk₃ (0 : R₁.obj' 0 ⟶ _) (R₂.map' 0 1) (R₂.map' 1 2) := homMk₃ (𝟙 _) (app' φ 0) (app' φ 1)
      (app' φ 2) (by simp) (naturality' φ 0 1) (naturality' φ 1 2)
  refine mono_of_epi_of_mono_of_mono' ψ (by simp)
    (hR₁.exact 0).exact_toComposableArrows
    (exact₂_mk _ (by simp) ?_) (by dsimp [ψ]; infer_instance) h₀ h₁
  rw [ShortComplex.exact_iff_mono _ (by simp)]
  exact hR₂'

set_option backward.isDefEq.respectTransparency false in
theorem epi_of_epi_of_epi_of_epi (hR₂ : R₂.Exact) (hR₁' : Epi (R₁.map' 1 2))
    (h₀ : Epi (app' φ 0)) (h₁ : Epi (app' φ 2)) :
    Epi (app' φ 1) := by
  let ψ : mk₃ (R₁.map' 0 1) (R₁.map' 1 2) (0 : _ ⟶ R₁.obj' 0) ⟶
    mk₃ (R₂.map' 0 1) (R₂.map' 1 2) (0 : _ ⟶ R₁.obj' 0) := homMk₃ (app' φ 0) (app' φ 1)
      (app' φ 2) (𝟙 _) (naturality' φ 0 1) (naturality' φ 1 2) (by simp)
  refine epi_of_epi_of_epi_of_mono' ψ (exact₂_mk _ (by simp) ?_)
    (hR₂.exact 0).exact_toComposableArrows (by simp)
    h₀ h₁ (by dsimp [ψ]; infer_instance)
  rw [ShortComplex.exact_iff_epi _ (by simp)]
  exact hR₁'

open ZeroObject

set_option backward.isDefEq.respectTransparency false in
lemma isIso_of_epi_of_isIso (hR₁ : R₁.Exact) (hR₂ : R₂.Exact) (hR₁' : Epi (R₁.map' 1 2))
    (hR₂' : Epi (R₂.map' 1 2)) (h₀ : Epi (app' φ 0)) (h₁ : IsIso (app' φ 1)) :
    IsIso (app' φ 2) := by
  let ψ : mk₄ (R₁.map' 0 1) (R₁.map' 1 2) (0 : _ ⟶ (0 : C)) (0 : _ ⟶ (0 : C)) ⟶
      mk₄ (R₂.map' 0 1) (R₂.map' 1 2) (0 : _ ⟶ (0 : C)) (0 : _ ⟶ (0 : C)) :=
    homMk₄ (app' φ 0) (app' φ 1) (app' φ 2) 0 0 (naturality' φ 0 1)
      (naturality' φ 1 2) (by simp) (by simp)
  obtain ⟨h₁m, h₁e⟩ := (isIso_iff_mono_and_epi (app' φ 1)).1 h₁
  refine isIso_of_epi_of_isIso_of_isIso_of_mono ?_ ?_ ψ h₀
    (by simpa [ψ] using h₁m) (by simpa [ψ] using h₁e) inferInstance inferInstance
    inferInstance
  · refine exact_of_δ₀ (hR₁.exact 0).exact_toComposableArrows (exact_of_δ₀ ?_ ?_)
    · refine exact₂_mk _ (by simp) ?_
      rwa [ShortComplex.exact_iff_epi _ (by simp)]
    · refine exact₂_mk _ (by simp) ?_
      rw [ShortComplex.exact_iff_epi _ (by simp)]
      infer_instance
  · refine exact_of_δ₀ (hR₂.exact 0).exact_toComposableArrows (exact_of_δ₀ ?_ ?_)
    · refine exact₂_mk _ (by simp) ?_
      rwa [ShortComplex.exact_iff_epi _ (by simp)]
    · refine exact₂_mk _ (by simp) ?_
      rw [ShortComplex.exact_iff_epi _ (by simp)]
      infer_instance

set_option backward.isDefEq.respectTransparency false in
lemma isIso_of_isIso_of_mono (hR₁ : R₁.Exact) (hR₂ : R₂.Exact) (hR₁' : Mono (R₁.map' 0 1))
    (hR₂' : Mono (R₂.map' 0 1)) (h₁ : IsIso (app' φ 1)) (h₂ : Mono (app' φ 2)) :
    IsIso (app' φ 0) := by
  let ψ : mk₄ (0 : (0 : C) ⟶ (0 : C)) (0 : _ ⟶ _) (R₁.map' 0 1) (R₁.map' 1 2) ⟶
      mk₄ (0 : (0 : C) ⟶ (0 : C)) (0 : _ ⟶ _) (R₂.map' 0 1) (R₂.map' 1 2) :=
    homMk₄ 0 0 (app' φ 0) (app' φ 1) (app' φ 2) (by simp) (by simp) (naturality' φ 0 1)
      (naturality' φ 1 2)
  obtain ⟨h₁m, h₁e⟩ := (isIso_iff_mono_and_epi (app' φ 1)).1 h₁
  refine isIso_of_epi_of_isIso_of_isIso_of_mono ?_ ?_ ψ inferInstance inferInstance inferInstance
    (by simpa [ψ] using h₁m) (by simpa [ψ] using h₁e) h₂
  · refine exact_of_δ₀ (exact₂_mk _ (by simp) ?_) (exact_of_δ₀ ?_ (exact₂_mk _ _ (hR₁.exact 0)))
    · rw [ShortComplex.exact_iff_mono _ (by simp)]
      infer_instance
    · refine exact₂_mk _ (by simp) ?_
      rwa [ShortComplex.exact_iff_mono _ (by simp)]
  · refine exact_of_δ₀ ?_ (exact_of_δ₀ ?_ (exact₂_mk _ _ (hR₂.exact 0)))
    · refine exact₂_mk _ (by simp) ?_
      rw [ShortComplex.exact_iff_mono _ (by simp)]
      infer_instance
    · refine exact₂_mk _ (by simp) ?_
      rwa [ShortComplex.exact_iff_mono _ (by simp)]

end Three

end Abelian

namespace ShortComplex

variable {C : Type*} [Category* C] [Abelian C]
variable {R₁ R₂ : ShortComplex C} (φ : R₁ ⟶ R₂)

attribute [local simp] ComposableArrows.Precomp.map

set_option backward.isDefEq.respectTransparency false in
theorem mono_of_epi_of_epi_of_mono (hR₂ : R₂.Exact) (hR₁' : Epi R₁.g)
    (h₀ : Epi φ.τ₁) (h₁ : Mono φ.τ₂) : Mono (φ.τ₃) :=
  Abelian.mono_of_epi_of_epi_mono' (ShortComplex.mapToComposableArrows φ)
    (by simp) hR₁' hR₂.exact_toComposableArrows h₀ h₁

set_option backward.isDefEq.respectTransparency false in
theorem epi_of_mono_of_epi_of_mono (hR₁ : R₁.Exact)
    (hR₂' : Mono R₂.f) (h₀ : Epi φ.τ₂) (h₁ : Mono φ.τ₃) : Epi φ.τ₁ :=
  Abelian.epi_of_mono_of_epi_of_mono' (ShortComplex.mapToComposableArrows φ)
    hR₁.exact_toComposableArrows (by simp) hR₂' h₀ h₁

theorem mono_of_mono_of_mono_of_mono (hR₁ : R₁.Exact) (hR₂' : Mono R₂.f) (h₀ : Mono φ.τ₁)
    (h₁ : Mono φ.τ₃) : Mono φ.τ₂ :=
  Abelian.mono_of_mono_of_mono_of_mono (ShortComplex.mapToComposableArrows φ)
    hR₁.exact_toComposableArrows hR₂' h₀ h₁

theorem epi_of_epi_of_epi_of_epi (hR₂ : R₂.Exact) (hR₁' : Epi R₁.g) (h₀ : Epi φ.τ₁)
    (h₁ : Epi φ.τ₃) : Epi φ.τ₂ :=
  Abelian.epi_of_epi_of_epi_of_epi (ShortComplex.mapToComposableArrows φ)
    hR₂.exact_toComposableArrows hR₁' h₀ h₁

end ShortComplex

end CategoryTheory
