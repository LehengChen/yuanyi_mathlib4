/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Probability.ProductMeasure
public import Mathlib.Probability.HasLaw

/-!
# Product of bernoulli distributions on a set

This file defines the product of bernoulli distributions on a set as a measure on sets.
For a set `u : Set ι` and `p` between `0` and `1`, this is the measure on `Set ι` such that each
`i ∈ u` belongs to the random set with probability `p`, and each `i ∉ u` doesn't belong to it.

## Notation

`setBer(u, p)` is the product of `p`-Bernoulli distributions on `u`.

## TODO

It is painful to convert from `unitInterval` to `ENNReal`. Should we introduce a coercion or
explicit operation (like `unitInterval.toNNReal`, note the lack of dot notation!)?
-/

public section

open MeasureTheory Measure unitInterval
open scoped ENNReal Finset

namespace ProbabilityTheory
variable {ι Ω : Type*} {m : MeasurableSpace Ω} {X Y : Ω → Set ι} {s u : Set ι} {i j : ι} {p q : I}
  {P : Measure Ω}

variable (u p) in
/-- The product of bernoulli distributions with parameter `p` on the set `u : Set V` is the measure
on `Set V` such that each element of `u` is taken with probability `p`, and the elements outside of
`u` are never taken. -/
@[expose]
noncomputable def setBernoulli : Measure (Set ι) :=
  .comap (fun s i ↦ i ∈ s) <| infinitePi fun i : ι ↦
    toNNReal p • dirac (i ∈ u) + toNNReal (σ p) • dirac False

@[inherit_doc] scoped notation "setBer(" u ", " p ")" => setBernoulli u p

instance : IsProbabilityMeasure setBer(u, p) :=
  MeasurableEquiv.setOf.symm.measurableEmbedding.isProbabilityMeasure_comap <| .of_forall fun P ↦
    ⟨{i | P i}, rfl⟩

variable (u p) in
lemma setBernoulli_eq_map :
    setBer(u, p) = .map (fun p : ι → Prop ↦ {i | p i})
      (infinitePi fun i : ι ↦ toNNReal p • dirac (i ∈ u) + toNNReal (σ p) • dirac False) :=
  MeasurableEquiv.setOf.comap_symm

lemma setBernoulli_apply (S : Set (Set ι)) :
    setBer(u, p) S = (infinitePi fun i ↦ toNNReal p • dirac (i ∈ u) + toNNReal (σ p) • dirac False)
      ((fun t i ↦ i ∈ t) '' S) := MeasurableEquiv.setOf.symm.measurableEmbedding.comap_apply ..

lemma setBernoulli_apply' (S : Set (Set ι)) :
    setBer(u, p) S = (infinitePi fun i ↦ toNNReal p • dirac (i ∈ u) + toNNReal (σ p) • dirac False)
      ((fun p ↦ {i | p i}) ⁻¹' S) := MeasurableEquiv.setOf.symm.comap_apply ..

set_option backward.isDefEq.respectTransparency false in
variable (u) in
@[simp] lemma setBernoulli_zero : setBer(u, 0) = dirac ∅ := by simp [setBernoulli_eq_map]

set_option backward.isDefEq.respectTransparency false in
variable (u) in
@[simp] lemma setBernoulli_one : setBer(u, 1) = dirac u := by simp [setBernoulli_eq_map]

lemma setBernoulli_ae_subset [Countable ↥(uᶜ : Set ι)] : ∀ᵐ s ∂setBer(u, p), s ⊆ u := by
  classical
  rw [ae_iff]
  calc
    setBer(u, p) {s | ¬ s ⊆ u}
    _ = setBer(u, p) (⋃ i : ↥(uᶜ : Set ι), {s | (i : ι) ∈ s}) := by
      congr 1
      ext s
      constructor
      · intro hs
        obtain ⟨i, his, hiu⟩ := Set.not_subset_iff_exists_mem_notMem.mp hs
        exact Set.mem_iUnion.2 ⟨⟨i, hiu⟩, his⟩
      · intro hs
        rcases Set.mem_iUnion.1 hs with ⟨i, his⟩
        exact Set.not_subset_iff_exists_mem_notMem.mpr ⟨i, his, i.2⟩
    _ = 0 := by
      rw [measure_iUnion_null_iff]
      intro i
      have hi : (i : ι) ∉ u := i.2
      calc
        setBer(u, p) {s | (i : ι) ∈ s}
        _ = infinitePi (fun i ↦ toNNReal p • dirac (i ∈ u) + toNNReal (σ p) • dirac False)
              (cylinder {(i : ι)} {fun _ ↦ True}) := by
          rw [setBernoulli_apply']; congr!; ext; simp [funext_iff]
        _ = 0 := by simp [infinitePi_cylinder, hi]

section Countable
variable [Countable ι]

variable (u p) in
@[simp] lemma setBernoulli_singleton (hsu : s ⊆ u) (hu : u.Finite) :
    setBer(u, p) {s} = toNNReal p ^ s.ncard * toNNReal (σ p) ^ (u \ s).ncard := by
  classical
  lift u to Finset ι using hu
  calc
    setBer(u, p) {s}
    _ = ∏' i, ((if i ∈ u ↔ i ∈ s then (toNNReal p : ℝ≥0∞) else 0) +
          if i ∈ s then 0 else (toNNReal (σ p) : ℝ≥0∞)) := by
      simp [setBernoulli_apply, Set.image_singleton, Set.indicator]
      simp [ENNReal.smul_def]
    _ = ∏ i ∈ u, (if i ∈ s then (toNNReal p : ℝ≥0∞) else (toNNReal (σ p) : ℝ≥0∞)) := by
      rw [tprod_eq_prod, Finset.prod_congr rfl] <;>
        simp +contextual [ite_add_ite, mt (@hsu _), ← ENNReal.coe_add]
    _ = toNNReal p ^ s.ncard * toNNReal (σ p) ^ (↑u \ s).ncard := by
      simp [Finset.prod_ite, ← Set.ncard_coe_finset, Set.setOf_and,
        Set.inter_eq_right.2 hsu, ← Set.compl_setOf, Set.diff_eq_compl_inter, Set.inter_comm]

end Countable

/-! ### Bernoulli random variables -/

variable (X u p P) in
/-- A random variable `X : Ω → Set ι` is `p`-bernoulli on a set `u : Set ι` if its distribution is
the product over `u` of `p`-bernoulli distributions. -/
abbrev IsSetBernoulli : Prop := HasLaw X setBer(u, p) P

lemma isSetBernoulli_congr (hXY : X =ᵐ[P] Y) : IsSetBernoulli X u p P ↔ IsSetBernoulli Y u p P :=
  hasLaw_congr hXY

lemma IsSetBernoulli.ae_subset [Countable ↥(uᶜ : Set ι)] (hX : IsSetBernoulli X u p P) :
    ∀ᵐ ω ∂P, X ω ⊆ u := by
  have hp : Measurable fun s : Set ι ↦ s ⊆ u := by
    rw [← measurableSet_setOf]
    have hs_eq : {t : Set ι | t ⊆ u} = ⋂ i : ↥(uᶜ : Set ι), {t | (i : ι) ∉ t} := by
      ext t
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
      constructor
      · intro ht i hit
        exact i.2 (ht hit)
      · intro ht i hit
        by_contra hiu
        exact ht ⟨i, hiu⟩ hit
    rw [hs_eq]
    exact MeasurableSet.iInter fun i ↦ (measurable_set_notMem (i : ι)).setOf
  exact (hX.ae_iff hp).2 setBernoulli_ae_subset

end ProbabilityTheory
