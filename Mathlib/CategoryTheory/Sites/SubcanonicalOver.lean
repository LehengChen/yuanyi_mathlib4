/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Sites.Canonical
public import Mathlib.CategoryTheory.Sites.Over

/-!
# Topology on `Over X` is subcanonical if the base is

We show that if `J` is subcanonical, then also `J.over X` is subcanonical.
-/

@[expose] public section

namespace CategoryTheory.GrothendieckTopology

variable {C : Type*} [Category* C]

set_option backward.isDefEq.respectTransparency false in
instance subcanonical_over (J : GrothendieckTopology C) [J.Subcanonical] (X : C) :
    (J.over X).Subcanonical := by
  refine .of_isSheaf_yoneda_obj _ fun E Z R hR t ht ↦ ?_
  obtain ⟨ι, T, g, rfl⟩ := R.exists_eq_ofArrows
  let hg : Presieve.Arrows.Compatible (CategoryTheory.yoneda.obj E.left)
      (fun i ↦ (g i).left) (fun i ↦ (t (g i) (Sieve.ofArrows_mk T g i)).left) :=
    fun i j Z gi gj hgij ↦ congr($(ht (Over.homMk (U := Over.mk (gi ≫ (T i).hom)) gi rfl)
      (Over.homMk (U := Over.mk (gi ≫ (T i).hom)) gj
      (by dsimp; rw [← Over.w (g i), reassoc_of% hgij, ← Over.w (g j)]))
      (Sieve.ofArrows_mk _ _ i) (Sieve.ofArrows_mk _ _ j) (by ext; exact hgij)).left)
  simp only [J.mem_over_iff, Sieve.ofArrows, Sieve.overEquiv_generate,
    Presieve.functorPushforward_overForget, Sieve.generate_sieve, Presieve.map_ofArrows] at hR
  obtain ⟨a, ha, huniq⟩ := (Presieve.isSheafFor_arrows_iff _ _).1
    ((Subcanonical.isSheaf_of_isRepresentable
      (CategoryTheory.yoneda.obj E.left)).isSheafFor _ hR) _ hg
  refine ⟨?_, ?_, fun y hty ↦ ?_⟩
  · refine Over.homMk a ?_
    refine ((Subcanonical.isSheaf_of_isRepresentable
      (CategoryTheory.yoneda.obj X)).isSheafFor _ hR).isSeparatedFor.ext ?_
    rintro W u ⟨i⟩
    have := ha i
    dsimp at this
    simp [reassoc_of% this]
  · rintro W p ⟨V, v, _, ⟨i⟩, rfl⟩
    refine Over.OverMorphism.ext ?_
    have := ha i
    dsimp at this
    simp [Category.assoc, this,
      Presieve.FamilyOfElements.comp_of_compatible _ ht (Sieve.ofArrows_mk _ _ i)]
  · refine Over.OverMorphism.ext (huniq _ ?_)
    intro i
    exact congr($(hty _ (Sieve.ofArrows_mk _ _ i)).left)

end CategoryTheory.GrothendieckTopology
