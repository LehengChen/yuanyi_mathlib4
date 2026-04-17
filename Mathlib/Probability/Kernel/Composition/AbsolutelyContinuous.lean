/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
module

public import Mathlib.Probability.Kernel.Composition.MeasureCompProd
public import Mathlib.Probability.Kernel.RadonNikodym

/-!
# Absolute continuity of the composition of measures and kernels

This file contains some results about the absolute continuity of the composition of measures and
kernels which use an assumption `CountableOrCountablyGenerated α β` on the measurable spaces.

Results that hold without that assumption are in files about the definitions of compositions and
products, like `Mathlib/Probability/Kernel/Composition/MeasureCompProd.lean` and
`Mathlib/Probability/Kernel/Composition/MeasureComp.lean`.

The assumption ensures the measurability of the sets where two kernels are absolutely continuous
or mutually singular.

## Main statements

* `absolutelyContinuous_compProd_iff'`: `μ ⊗ₘ κ ≪ ν ⊗ₘ η ↔ μ ≪ ν ∧ ∀ᵐ a ∂μ, κ a ≪ η a`.

-/

public section

open ProbabilityTheory Filter

open scoped ENNReal

namespace MeasureTheory.Measure

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {μ ν : Measure α} {κ η : Kernel α β} [IsFiniteKernel κ] [IsFiniteKernel η]
  [MeasurableSpace.CountableOrCountablyGenerated α β]

lemma MutuallySingular.compProd_of_right (μ ν : Measure α) (hκη : ∀ᵐ a ∂μ, κ a ⟂ₘ η a) :
    μ ⊗ₘ κ ⟂ₘ ν ⊗ₘ η := by
  by_cases hμ : SFinite μ
  swap; · rw [compProd_of_not_sfinite _ _ hμ]; simp
  by_cases hν : SFinite ν
  swap; · rw [compProd_of_not_sfinite _ _ hν]; simp
  let s := κ.mutuallySingularSet η
  have hs : MeasurableSet s := Kernel.measurableSet_mutuallySingularSet κ η
  symm
  refine ⟨s, hs, ?_⟩
  rw [compProd_apply hs, compProd_apply hs.compl]
  have h_eq a : Prod.mk a ⁻¹' s = Kernel.mutuallySingularSetSlice κ η a := rfl
  have h1 a : η a (Prod.mk a ⁻¹' s) = 0 := by rw [h_eq, Kernel.measure_mutuallySingularSetSlice]
  have h2 : ∀ᵐ a ∂μ, κ a (Prod.mk a ⁻¹' s)ᶜ = 0 := by
    filter_upwards [hκη] with a ha
    rwa [h_eq, ← Kernel.withDensity_rnDeriv_eq_zero_iff_measure_eq_zero κ η a,
      Kernel.withDensity_rnDeriv_eq_zero_iff_mutuallySingular]
  simp [h1, lintegral_congr_ae h2]

lemma MutuallySingular.compProd_of_right' (μ ν : Measure α) (hκη : ∀ᵐ a ∂ν, κ a ⟂ₘ η a) :
    μ ⊗ₘ κ ⟂ₘ ν ⊗ₘ η := by
  refine (MutuallySingular.compProd_of_right _ _ ?_).symm
  simp_rw [MutuallySingular.comm, hκη]

lemma mutuallySingular_compProd_right_iff [SFinite μ] :
    μ ⊗ₘ κ ⟂ₘ μ ⊗ₘ η ↔ ∀ᵐ a ∂μ, κ a ⟂ₘ η a :=
  ⟨fun h ↦ mutuallySingular_of_mutuallySingular_compProd h AbsolutelyContinuous.rfl
    AbsolutelyContinuous.rfl, MutuallySingular.compProd_of_right _ _⟩

lemma AbsolutelyContinuous.kernel_of_compProd [SFinite μ] (h : μ ⊗ₘ κ ≪ ν ⊗ₘ η) :
    ∀ᵐ a ∂μ, κ a ≪ η a := by
  suffices ∀ᵐ a ∂μ, κ.singularPart η a = 0 by
    filter_upwards [this] with a ha
    rwa [Kernel.singularPart_eq_zero_iff_absolutelyContinuous] at ha
  rw [← κ.rnDeriv_add_singularPart η, compProd_add_right, AbsolutelyContinuous.add_left_iff] at h
  have : μ ⊗ₘ κ.singularPart η ⟂ₘ ν ⊗ₘ η :=
    MutuallySingular.compProd_of_right μ ν (.of_forall <| Kernel.mutuallySingular_singularPart _ _)
  refine compProd_eq_zero_iff.mp ?_
  exact eq_zero_of_absolutelyContinuous_of_mutuallySingular h.2 this

omit [IsFiniteKernel η] [MeasurableSpace.CountableOrCountablyGenerated α β] in
lemma absolutelyContinuous_of_compProd_ae [SFinite μ] (hκ : ∀ᵐ a ∂μ, NeZero (κ a))
    (h : μ ⊗ₘ κ ≪ ν ⊗ₘ η) :
    μ ≪ ν := by
  refine Measure.AbsolutelyContinuous.mk fun s hs hs0 ↦ ?_
  have h1 : (ν ⊗ₘ η) (s ×ˢ Set.univ) = 0 := by
    by_cases hν : SFinite ν
    swap; · simp [compProd_of_not_sfinite _ _ hν]
    by_cases hη : IsSFiniteKernel η
    swap; · simp [compProd_of_not_isSFiniteKernel _ _ hη]
    rw [Measure.compProd_apply_prod hs MeasurableSet.univ]
    exact setLIntegral_measure_zero _ _ hs0
  have h2 : (μ ⊗ₘ κ) (s ×ˢ Set.univ) = 0 := h h1
  rw [Measure.compProd_apply_prod hs MeasurableSet.univ, lintegral_eq_zero_iff] at h2
  swap; · exact Kernel.measurable_coe _ MeasurableSet.univ
  by_contra hμs
  have : Filter.NeBot (ae (μ.restrict s)) := by simp [hμs]
  have hκs : ∀ᵐ a ∂μ.restrict s, NeZero (κ a) := ae_restrict_of_ae hκ
  obtain ⟨a, ha_zero, ha_nonzero⟩ : ∃ a, κ a Set.univ = 0 ∧ NeZero (κ a) := by
    have h_comb : ∀ᵐ a ∂μ.restrict s, κ a Set.univ = 0 ∧ NeZero (κ a) := by
      filter_upwards [h2, hκs] with a ha_zero ha_nonzero
      exact ⟨ha_zero, ha_nonzero⟩
    exact h_comb.exists
  exact ha_nonzero.out ((Measure.measure_univ_eq_zero.mp ha_zero))

lemma absolutelyContinuous_compProd_iff' [SFinite μ] [SFinite ν]
    (hκ : ∀ᵐ a ∂μ, NeZero (κ a)) :
    μ ⊗ₘ κ ≪ ν ⊗ₘ η ↔ μ ≪ ν ∧ ∀ᵐ a ∂μ, κ a ≪ η a :=
  ⟨fun h ↦ ⟨absolutelyContinuous_of_compProd_ae hκ h, h.kernel_of_compProd⟩,
    fun h ↦ h.1.compProd h.2⟩

lemma absolutelyContinuous_compProd_right_iff [SFinite μ] :
    μ ⊗ₘ κ ≪ μ ⊗ₘ η ↔ ∀ᵐ a ∂μ, κ a ≪ η a :=
  ⟨AbsolutelyContinuous.kernel_of_compProd, AbsolutelyContinuous.compProd_right⟩

end MeasureTheory.Measure
