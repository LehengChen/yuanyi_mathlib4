/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Abelian.Refinements
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.Algebra.Homology.CommSq

/-!
# The exact sequence attached to a pushout square

Consider a pushout square in an abelian category:

```
    t
 X₁ ⟶ X₂
l|    |r
 v    v
 X₃ ⟶ X₄
    b
```

We study the associated exact sequence `X₁ ⟶ X₂ ⊞ X₃ ⟶ X₄ ⟶ 0`.
We also show that the induced morphism `kernel t ⟶ kernel b` is an epimorphism.

-/

public section

universe v u

namespace CategoryTheory

open Category Limits

variable {C : Type u} [Category.{v} C]

namespace Abelian

variable [Abelian C]

instance : (MorphismProperty.monomorphisms C).IsStableUnderCobaseChange :=
  .mk' (fun _ _ _ _ _ _ (_ : Mono _) ↦ inferInstanceAs (Mono _))

instance : (MorphismProperty.epimorphisms C).IsStableUnderBaseChange :=
  .mk' (fun _ _ _ _ _ _ (_ : Epi _) ↦ inferInstanceAs (Epi _))

end Abelian

variable {X₁ X₂ X₃ X₄ : C} {t : X₁ ⟶ X₂} {l : X₁ ⟶ X₃} {r : X₂ ⟶ X₄} {b : X₃ ⟶ X₄}

private lemma epi_iff_surjective_up_to_refinements'
    [HasPullbacks C] [(MorphismProperty.epimorphisms C).IsStableUnderBaseChange]
    {X Y : C} (f : X ⟶ Y) :
    Epi f ↔ ∀ ⦃A : C⦄ (y : A ⟶ Y),
      ∃ (A' : C) (π : A' ⟶ A) (_ : Epi π) (x : A' ⟶ X), π ≫ y = x ≫ f := by
  constructor
  · intro _ A y
    haveI : Epi (pullback.fst y f) :=
      MorphismProperty.pullback_fst (P := MorphismProperty.epimorphisms C) y f inferInstance
    exact ⟨pullback y f, pullback.fst y f, inferInstance, pullback.snd y f,
      pullback.condition⟩
  · intro hf
    obtain ⟨A, π, hπ, a', fac⟩ := hf (𝟙 Y)
    rw [comp_id] at fac
    exact epi_of_epi_fac fac.symm

private lemma ShortComplex.Exact.exact_up_to_refinements'
    [Preadditive C] [HasPullbacks C]
    [(MorphismProperty.epimorphisms C).IsStableUnderBaseChange]
    {S : ShortComplex C} (hS : S.Exact) [S.HasHomology] {A : C}
    (x₂ : A ⟶ S.X₂) (hx₂ : x₂ ≫ S.g = 0) :
    ∃ (A' : C) (π : A' ⟶ A) (_ : Epi π) (x₁ : A' ⟶ S.X₁),
      π ≫ x₂ = x₁ ≫ S.f := by
  have hEpi : Epi S.toCycles := (S.exact_iff_epi_toCycles).1 hS
  obtain ⟨A', π, hπ, x₁, fac⟩ :=
    (epi_iff_surjective_up_to_refinements' S.toCycles).1 hEpi (S.liftCycles x₂ hx₂)
  exact ⟨A', π, hπ, x₁,
    by simpa only [assoc, liftCycles_i, toCycles_i] using fac =≫ S.iCycles⟩

namespace IsPushout

variable [Preadditive C] [HasBinaryBiproduct X₂ X₃]

lemma exact_shortComplex (h : IsPushout t l r b) [h.shortComplex.HasHomology] :
    h.shortComplex.Exact :=
  h.shortComplex.exact_of_g_is_cokernel
    h.isColimitCokernelCofork

set_option backward.isDefEq.respectTransparency false in
/-- Given a pushout square in a preadditive category where the relevant binary biproduct exists
and epimorphisms are stable under base change,
```
X₁ ⟶ X₂
|    |
v    v
X₃ ⟶ X₄
```
the morphism `X₂ ⊞ X₃ ⟶ X₄` is an epimorphism. This lemma translates this
as the existence of liftings up to refinements: a morphism `z : T ⟶ X₄`
can be written as a sum of a morphism to `X₂` and a morphism to `X₃`,
at least if we allow a precomposition with an epimorphism `π : T' ⟶ T`. -/
lemma hom_eq_add_up_to_refinements
    [HasPullbacks C] [(MorphismProperty.epimorphisms C).IsStableUnderBaseChange]
    (h : IsPushout t l r b) {T : C} (x₄ : T ⟶ X₄) :
    ∃ (T' : C) (π : T' ⟶ T) (_ : Epi π) (x₂ : T' ⟶ X₂) (x₃ : T' ⟶ X₃),
      π ≫ x₄ = x₂ ≫ r + x₃ ≫ b := by
  have := h.epi_shortComplex_g
  obtain ⟨T', π, _, u, hu⟩ := (epi_iff_surjective_up_to_refinements' h.shortComplex.g).1
    inferInstance x₄
  refine ⟨T', π, inferInstance, u ≫ biprod.fst, u ≫ biprod.snd, ?_⟩
  simp only [hu, assoc, ← Preadditive.comp_add]
  congr
  cat_disch

/--
Given a commutative diagram in a preadditive category where the relevant binary biproduct exists
and epimorphisms are stable under base change,
```
X₁ ⟶ X₂
|    |  \
v    v   \
X₃ ⟶ X₄   \
 \     \   v
  \     \> X₅
   \_____>
```
where the top/left square is a pushout square,
the outer square involving `X₁`, `X₂`, `X₃` and `X₅`
is a pullback square, and `X₂ ⟶ X₅` is mono,
then `X₄ ⟶ X₅` is a mono.
-/
lemma mono_of_isPullback_of_mono
    [HasPullbacks C] [(MorphismProperty.epimorphisms C).IsStableUnderBaseChange]
    (h₁ : IsPushout t l r b) {X₅ : C} {r' : X₂ ⟶ X₅} {b' : X₃ ⟶ X₅}
    (h₂ : IsPullback t l r' b') (k : X₄ ⟶ X₅)
    (fac₁ : r ≫ k = r') (fac₂ : b ≫ k = b') [Mono r'] : Mono k :=
  Preadditive.mono_of_cancel_zero _ (fun {T₀} x₄ hx₄ ↦ by
    obtain ⟨T₁, π, _, x₂, x₃, eq⟩ := hom_eq_add_up_to_refinements h₁ x₄
    have fac₃ : (-x₂) ≫ r' = x₃ ≫ b' := by
      rw [Preadditive.neg_comp, neg_eq_iff_add_eq_zero, ← fac₂, ← fac₁,
        ← assoc, ← assoc, ← Preadditive.add_comp, ← eq, assoc, hx₄, comp_zero]
    obtain ⟨x₂', hx₂'⟩ : ∃ x₂', π ≫ x₄ = x₂' ≫ r := by
      refine ⟨x₂ + h₂.lift (-x₂) x₃ fac₃ ≫ t, ?_⟩
      rw [eq, Preadditive.add_comp, assoc, h₁.w, IsPullback.lift_snd_assoc, add_comm]
    rw [← cancel_epi π, comp_zero, reassoc_of% hx₂', fac₁] at hx₄
    obtain rfl := zero_of_comp_mono _ hx₄
    rw [zero_comp] at hx₂'
    rw [← cancel_epi π, hx₂', comp_zero])

end IsPushout

namespace IsPullback

variable [Preadditive C] [HasBinaryBiproduct X₂ X₃]

lemma exact_shortComplex' (h : IsPullback t l r b) [h.shortComplex'.HasHomology] :
    h.shortComplex'.Exact :=
  h.shortComplex'.exact_of_f_is_kernel
    h.isLimitKernelFork

/-!
Note: if `h : IsPullback t l r b`, then `X₁ ⟶ X₂ ⊞ X₃` is a monomorphism,
which can be translated in concrete terms thanks to the lemma `IsPullback.hom_ext`:
if a morphism `f : Z ⟶ X₁` becomes zero after composing with `X₁ ⟶ X₂` and
`X₁ ⟶ X₃`, then `f = 0`. This is the reason why we do not state the dual
statement to `IsPushout.hom_eq_add_up_to_refinements`.
-/

end IsPullback

namespace Abelian

variable {X₁ X₂ X₃ X₄ : C} {t : X₁ ⟶ X₂} {l : X₁ ⟶ X₃} {r : X₂ ⟶ X₄} {b : X₃ ⟶ X₄}

lemma mono_cokernel_map_of_isPullback
    [Preadditive C] [HasPullbacks C]
    [(MorphismProperty.epimorphisms C).IsStableUnderBaseChange]
    [HasCokernel t] [HasCokernel b]
    [(ShortComplex.mk b (cokernel.π b) (cokernel.condition b)).HasHomology]
    (sq : IsPullback t l r b) :
    Mono (cokernel.map _ _ _ _ sq.w) := by
  rw [Preadditive.mono_iff_cancel_zero]
  intro A₀ z hz
  haveI : Epi (cokernel.π t) := by infer_instance
  obtain ⟨A₁, π₁, _, x₂, hx₂⟩ :=
    (epi_iff_surjective_up_to_refinements' (cokernel.π t)).1 inferInstance z
  have : (ShortComplex.mk _ _ (cokernel.condition b)).Exact :=
    ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel b)
  obtain ⟨A₂, π₂, _, x₃, hx₃⟩ := this.exact_up_to_refinements' (x₂ ≫ r) (by
    simpa [hz] using hx₂.symm =≫ cokernel.map _ _ _ _ sq.w)
  obtain ⟨x₁, hx₁, rfl⟩ := sq.exists_lift (π₂ ≫ x₂) x₃ (by simpa)
  simp [← cancel_epi π₁, ← cancel_epi π₂, hx₂, ← reassoc_of% hx₁]

set_option backward.isDefEq.respectTransparency false in
lemma epi_kernel_map_of_isPushout
    [Preadditive C] [HasPullbacks C]
    [(MorphismProperty.epimorphisms C).IsStableUnderBaseChange]
    [HasKernel t] [HasKernel b] [HasBinaryBiproduct X₂ X₃] (sq : IsPushout t l r b)
    [(ShortComplex.mk _ _ sq.cokernelCofork.condition).HasHomology] :
    Epi (kernel.map _ _ _ _ sq.w) := by
  rw [epi_iff_surjective_up_to_refinements']
  intro A₀ z
  obtain ⟨A₁, π₁, _, x₁, hx₁⟩ := ((ShortComplex.mk _ _
    sq.cokernelCofork.condition).exact_of_g_is_cokernel
      sq.isColimitCokernelCofork).exact_up_to_refinements'
        (z ≫ kernel.ι _ ≫ biprod.inr) (by simp)
  refine ⟨A₁, π₁, inferInstance, -kernel.lift _ x₁ ?_, ?_⟩
  · simpa using hx₁.symm =≫ biprod.fst
  · ext
    simpa using hx₁ =≫ biprod.snd

end Abelian

end CategoryTheory
