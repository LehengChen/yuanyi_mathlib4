/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomologicalFunctor
public import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.Algebra.Homology.Refinements

/-!
# The mapping cone of a monomorphism, up to a quasi-isomorphism

If `S` is a short exact short complex of cochain complexes in an abelian category,
we construct a quasi-isomorphism `descShortComplex S : mappingCone S.f ⟶ S.X₃`.

We obtain this by comparing the homology sequence of `S` and the homology
sequence of the homology functor on the homotopy category, applied to the
distinguished triangle attached to the mapping cone of `S.f`.

-/

@[expose] public section

assert_not_exists TwoSidedIdeal

open CategoryTheory Category ComplexShape HomotopyCategory Limits
  HomologicalComplex.HomologySequence Pretriangulated Preadditive

variable {C : Type*} [Category* C] [Abelian C]

namespace CochainComplex

set_option backward.isDefEq.respectTransparency false in -- Needed in homologySequenceδ_triangleh
@[reassoc]
lemma homologySequenceδ_quotient_mapTriangle_obj
    (T : Triangle (CochainComplex C ℤ)) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    (homologyFunctor C (up ℤ) 0).homologySequenceδ
        ((quotient C (up ℤ)).mapTriangle.obj T) n₀ n₁ h =
      (homologyFunctorFactors C (up ℤ) n₀).hom.app _ ≫
        (HomologicalComplex.homologyFunctor C (up ℤ) 0).shiftMap T.mor₃ n₀ n₁ (by lia) ≫
        (homologyFunctorFactors C (up ℤ) n₁).inv.app _ := by
  apply homologyFunctor_shiftMap

namespace HomotopyCategory

lemma shift_homologyFunctor (n : ℤ) :
    (homologyFunctor C (up ℤ) 0).shift n = homologyFunctor C (up ℤ) n := rfl

end HomotopyCategory

namespace mappingCone

variable (S : ShortComplex (CochainComplex C ℤ)) (hS : S.ShortExact)

/-- The canonical morphism `mappingCone S.f ⟶ S.X₃` when `S` is a short complex
of cochain complexes. -/
noncomputable def descShortComplex : mappingCone S.f ⟶ S.X₃ := desc S.f 0 S.g (by simp)

@[reassoc (attr := simp)]
lemma inr_descShortComplex : inr S.f ≫ descShortComplex S = S.g := by
  simp [descShortComplex]

@[reassoc (attr := simp)]
lemma inr_f_descShortComplex_f (n : ℤ) : (inr S.f).f n ≫ (descShortComplex S).f n = S.g.f n := by
  simp [descShortComplex]

@[reassoc (attr := simp)]
lemma inl_v_descShortComplex_f (i j : ℤ) (h : i + (-1) = j) :
    (inl S.f).v i j h ≫ (descShortComplex S).f j = 0 := by
  simp [descShortComplex]

section

variable (S₁ S₂ : ShortComplex (CochainComplex C ℤ)) (f : S₁ ⟶ S₂)

lemma map_descShortComplex : map S₁.f S₂.f f.τ₁ f.τ₂ f.comm₁₂.symm ≫ descShortComplex S₂ =
    descShortComplex S₁ ≫ f.τ₃ := by
  ext i
  simpa [mappingCone.ext_from_iff _ _ _ rfl, map] using
    congr_fun (congr_arg HomologicalComplex.Hom.f f.comm₂₃) i

end

variable {S}

set_option backward.isDefEq.respectTransparency false in
lemma homologySequenceδ_triangleh (n₀ : ℤ) (n₁ : ℤ) (h : n₀ + 1 = n₁) :
    (homologyFunctor C (up ℤ) 0).homologySequenceδ (triangleh S.f) n₀ n₁ h =
      (homologyFunctorFactors C (up ℤ) n₀).hom.app _ ≫
        HomologicalComplex.homologyMap (descShortComplex S) n₀ ≫ hS.δ n₀ n₁ h ≫
          (homologyFunctorFactors C (up ℤ) n₁).inv.app _ := by
  /- We proceed by diagram chase. We test the identity on
     cocycles `x' : A' ⟶ (mappingCone S.f).X n₀` -/
  dsimp
  rw [← cancel_mono ((homologyFunctorFactors C (up ℤ) n₁).hom.app _),
    assoc, assoc, assoc, Iso.inv_hom_id_app,
    ← cancel_epi ((homologyFunctorFactors C (up ℤ) n₀).inv.app _), Iso.inv_hom_id_app_assoc]
  apply yoneda.map_injective
  ext ⟨A⟩ (x : A ⟶ _)
  obtain ⟨A', π, _, x', w, hx'⟩ :=
    (mappingCone S.f).eq_liftCycles_homologyπ_up_to_refinements x n₁ (by simpa using h)
  have hδ :=
    homologySequenceδ_quotient_mapTriangle_obj_assoc (triangle S.f) n₀ n₁ h
      ((homologyFunctorFactors C (up ℤ) n₁).hom.app S.X₁)
  have hδ' := by
    simpa only [Functor.mapTriangle_obj, triangle_obj₁, triangle_mor₁, triangle_mor₂] using hδ
  rw [hδ']
  dsimp
  rw [comp_id, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app]
  simp
  rw [← cancel_epi π, reassoc_of% hx', reassoc_of% hx',
    HomologicalComplex.homologyπ_naturality_assoc,
    HomologicalComplex.liftCycles_comp_cyclesMap_assoc]
  /- We decompose the cocycle `x'` into two morphisms `a : A' ⟶ S.X₁.X n₁`
     and `b : A' ⟶ S.X₂.X n₀` satisfying certain relations. -/
  obtain ⟨a, b, hab⟩ := decomp_to _ x' n₁ h
  rw [hab, ext_to_iff _ n₁ (n₁ + 1) rfl, add_comp, assoc, assoc, inr_f_d, add_comp, assoc,
    assoc, assoc, assoc, inr_f_fst_v, comp_zero, comp_zero, add_zero, zero_comp,
    d_fst_v _ _ _ _ h, comp_neg, inl_v_fst_v_assoc, comp_neg, neg_eq_zero,
    add_comp, assoc, assoc, assoc, assoc, inr_f_snd_v, comp_id, zero_comp,
    d_snd_v _ _ _ h, comp_add, inl_v_fst_v_assoc, inl_v_snd_v_assoc, zero_comp, add_zero] at w
  /- We simplify the RHS. -/
  conv_rhs => simp only [hab, add_comp, assoc, inr_f_descShortComplex_f,
    inl_v_descShortComplex_f, comp_zero, zero_add]
  rw [hS.δ_eq n₀ n₁ (by simpa using h) (b ≫ S.g.f n₀) _ b rfl (-a)
    (by simp only [neg_comp, neg_eq_iff_add_eq_zero, w.2]) (n₁ + 1) (by simp)]
  /- We simplify the LHS. -/
  dsimp [Functor.shiftMap, homologyFunctor_shift]
  rw [assoc, HomologicalComplex.homologyπ_naturality_assoc,
    HomologicalComplex.liftCycles_comp_cyclesMap_assoc,
    S.X₁.liftCycles_shift_homologyπ_assoc _ _ _ _ n₁ (by lia) (n₁ + 1) (by simp)]
  dsimp [homologyFunctor_shift]
  simp only [hab, add_comp, assoc, inl_v_triangle_mor₃_f_assoc,
    shiftFunctorObjXIso, neg_comp, Iso.inv_hom_id, comp_neg, comp_id,
    inr_f_triangle_mor₃_f_assoc, zero_comp, comp_zero, add_zero]
  simp only [Iso.inv_hom_id_app]
  simpa using Category.comp_id
    (HomologicalComplex.liftCycles S.X₁ (-a) (n₁ + 1) _ _ ≫ HomologicalComplex.homologyπ S.X₁ n₁)

open ComposableArrows

set_option backward.isDefEq.respectTransparency false in
include hS in
lemma quasiIso_descShortComplex : QuasiIso (descShortComplex S) where
  quasiIsoAt n := by
    rw [quasiIsoAt_iff_isIso_homologyMap]
    let φ : ((homologyFunctor C (up ℤ) 0).homologySequenceComposableArrows₅
        (triangleh S.f) n _ rfl).δlast ⟶ (composableArrows₅ hS n _ rfl).δlast :=
      homMk₄ ((homologyFunctorFactors C (up ℤ) _).hom.app _)
        ((homologyFunctorFactors C (up ℤ) _).hom.app _)
        ((homologyFunctorFactors C (up ℤ) _).hom.app _ ≫
          HomologicalComplex.homologyMap (descShortComplex S) n)
        ((homologyFunctorFactors C (up ℤ) _).hom.app _)
        ((homologyFunctorFactors C (up ℤ) _).hom.app _)
        ((homologyFunctorFactors C (up ℤ) _).hom.naturality S.f)
        (by
          have hnat :=
            (homologyFunctorFactors C (up ℤ) n).hom.naturality_assoc (inr S.f)
              (HomologicalComplex.homologyMap (descShortComplex S) n)
          -- Disable `Fin.reduceFinMk`, otherwise `Precomp.obj_succ` does not fire. (https://github.com/leanprover-community/mathlib4/issues/27382)
          dsimp [-Fin.reduceFinMk]
          have hshift :
              ((homologyFunctor C (up ℤ) 0).shift n).map ((quotient C (up ℤ)).map (inr S.f)) =
                (homologyFunctor C (up ℤ) n).map ((quotient C (up ℤ)).map (inr S.f)) := by
            rfl
          rw [hshift]
          have hmap :
              (HomologicalComplex.homologyFunctor C (up ℤ) n).map (inr S.f) =
                HomologicalComplex.homologyMap (inr S.f) n := rfl
          rw [hmap] at hnat
          simpa only [Functor.comp_map, ← HomologicalComplex.homologyMap_comp,
            inr_descShortComplex] using hnat)
        (by
          -- Disable `Fin.reduceFinMk`, otherwise `Precomp.obj_succ` does not fire. (https://github.com/leanprover-community/mathlib4/issues/27382)
          dsimp [-Fin.reduceFinMk]
          have hδ :=
            congrArg
              (fun k => k ≫ (homologyFunctorFactors C (up ℤ) (n + 1)).hom.app S.X₁)
              (homologySequenceδ_triangleh hS n (n + 1) rfl)
          simpa only [triangleh, Functor.mapTriangle_obj, triangle_obj₁, triangle_mor₁,
            triangle_mor₂, Functor.comp_obj, HomologicalComplex.homologyFunctor_obj, assoc,
            Iso.inv_hom_id_app, comp_id] using hδ)
        ((homologyFunctorFactors C (up ℤ) _).hom.naturality S.f)
    have : IsIso ((homologyFunctorFactors C (up ℤ) n).hom.app (mappingCone S.f) ≫
        HomologicalComplex.homologyMap (descShortComplex S) n) := by
      apply Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono
        ((homologyFunctor C (up ℤ) 0).homologySequenceComposableArrows₅_exact _
          (mappingCone_triangleh_distinguished S.f) n _ rfl).δlast
        (composableArrows₅_exact hS n _ rfl).δlast φ
      all_goals dsimp [φ]; infer_instance
    apply IsIso.of_isIso_comp_left ((homologyFunctorFactors C (up ℤ) n).hom.app (mappingCone S.f))

@[reassoc]
lemma descShortComplex_naturality {S₁ S₂ : ShortComplex (CochainComplex C ℤ)} (f : S₁ ⟶ S₂) :
    map S₁.f S₂.f f.τ₁ f.τ₂ f.comm₁₂.symm ≫ descShortComplex S₂ = descShortComplex S₁ ≫ f.τ₃ := by
  ext n
  apply ext_from _ (n + 1) n rfl
  · simp [map]
  · simp [map, ← HomologicalComplex.comp_f, f.comm₂₃]

variable {D : Type*} [Category* D] [Abelian D]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma mapHomologicalComplexIso_hom_descShortComplex (F : C ⥤ D) [F.Additive]
    (S : ShortComplex (CochainComplex C ℤ)) :
    (mapHomologicalComplexIso _ _).hom ≫
      descShortComplex (S.map (F.mapHomologicalComplex (.up ℤ))) =
    (F.mapHomologicalComplex (.up ℤ)).map (descShortComplex S) := by
  symm
  ext n
  simp [mapHomologicalComplexIso, descShortComplex, mapHomologicalComplexXIso,
    mapHomologicalComplexXIso'_hom, Functor.mapHomologicalComplex_map_f,
    desc_f _ _ _ _ n (n + 1) rfl]

end mappingCone

end CochainComplex
