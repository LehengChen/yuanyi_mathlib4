/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Andrew Yang
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-!
# Constructing equalizers from pullbacks and binary products.

If a category has pullbacks and binary products, then it has equalizers.

TODO: generalize universe
-/

@[expose] public section


noncomputable section

universe v v' u u'

open CategoryTheory CategoryTheory.Category

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]
variable {D : Type u'} [Category.{v'} D] (G : C ⥤ D)

-- We hide the "implementation details" inside a namespace
namespace HasEqualizersOfHasPullbacksAndBinaryProducts

variable [HasBinaryProducts C] [HasPullbacks C]

/-- Define the equalizing object -/
abbrev constructEqualizer (F : WalkingParallelPair ⥤ C) : C :=
  pullback (prod.lift (𝟙 _) (F.map WalkingParallelPairHom.left))
    (prod.lift (𝟙 _) (F.map WalkingParallelPairHom.right))

/-- Define the equalizing morphism -/
abbrev pullbackFst (F : WalkingParallelPair ⥤ C) :
    constructEqualizer F ⟶ F.obj WalkingParallelPair.zero :=
  pullback.fst _ _

set_option backward.isDefEq.respectTransparency false in
theorem pullbackFst_eq_pullback_snd (F : WalkingParallelPair ⥤ C) :
    pullbackFst F = pullback.snd _ _ := by
  convert (eq_whisker pullback.condition Limits.prod.fst :
      (_ : constructEqualizer F ⟶ F.obj WalkingParallelPair.zero) = _) <;> simp

set_option backward.isDefEq.respectTransparency false in
/-- Define the equalizing cone -/
abbrev equalizerCone (F : WalkingParallelPair ⥤ C) : Cone F :=
  Cone.ofFork
    (Fork.ofι (pullbackFst F)
      (by
        conv_rhs => rw [pullbackFst_eq_pullback_snd]
        convert (eq_whisker pullback.condition Limits.prod.snd :
          (_ : constructEqualizer F ⟶ F.obj WalkingParallelPair.one) = _) using 1 <;> simp))

set_option backward.isDefEq.respectTransparency false in
/-- Show the equalizing cone is a limit -/
def equalizerConeIsLimit (F : WalkingParallelPair ⥤ C) : IsLimit (equalizerCone F) where
  lift c := pullback.lift (c.π.app _) (c.π.app _)
  fac := by rintro c (_ | _) <;> simp
  uniq := by
    intro c _ J
    have J0 := J WalkingParallelPair.zero
    apply pullback.hom_ext
    · simpa [limit.lift_π] using J0
    · simp [← J0, pullbackFst_eq_pullback_snd]

end HasEqualizersOfHasPullbacksAndBinaryProducts

open HasEqualizersOfHasPullbacksAndBinaryProducts

-- This is not an instance, as it is not always how one wants to construct equalizers!
/-- Any category with pullbacks and binary products, has equalizers. -/
theorem hasEqualizers_of_hasPullbacks_and_binary_products [HasBinaryProducts C] [HasPullbacks C] :
    HasEqualizers C :=
  { has_limit := fun F =>
      HasLimit.mk
        { cone := equalizerCone F
          isLimit := equalizerConeIsLimit F } }

set_option backward.isDefEq.respectTransparency false in
/-- A functor that preserves pullbacks and binary products also preserves equalizers. -/
lemma preservesEqualizers_of_preservesPullbacks_and_binaryProducts
    [HasBinaryProducts C]
    [PreservesLimitsOfShape (Discrete WalkingPair) G] [PreservesLimitsOfShape WalkingCospan G] :
    PreservesLimitsOfShape WalkingParallelPair G :=
  ⟨fun {K} =>
    ⟨fun {s} hs =>
      ⟨by
        let f := prod.lift (𝟙 (K.obj WalkingParallelPair.zero))
          (K.map WalkingParallelPairHom.left)
        let g := prod.lift (𝟙 (K.obj WalkingParallelPair.zero))
          (K.map WalkingParallelPairHom.right)
        have hpb : IsLimit (PullbackCone.mk (s.π.app WalkingParallelPair.zero)
            (s.π.app WalkingParallelPair.zero) (f := f) (g := g) (by
              apply prod.hom_ext
              · simp [f, g]
              · simp only [Category.assoc, prod.lift_snd, f, g]
                exact
                  (s.π.naturality WalkingParallelPairHom.left).symm.trans
                    (s.π.naturality WalkingParallelPairHom.right))) := by
          refine PullbackCone.IsLimit.mk _ (fun c =>
              hs.lift (Cone.ofFork (Fork.ofι c.fst ?_))) ?_ ?_ ?_
          · have hfst_snd : c.fst = c.snd := by
              simpa only [Category.assoc, prod.lift_fst, Category.comp_id, f, g] using
                congrArg (fun e => e ≫ prod.fst) c.condition
            have hleft_right : c.fst ≫ K.map WalkingParallelPairHom.left =
                c.snd ≫ K.map WalkingParallelPairHom.right := by
              simpa only [Category.assoc, prod.lift_snd, f, g] using
                congrArg (fun e => e ≫ prod.snd) c.condition
            rw [← hfst_snd] at hleft_right
            exact hleft_right
          · intro c
            simp
          · intro c
            have hfst_snd : c.fst = c.snd := by
              simpa only [Category.assoc, prod.lift_fst, Category.comp_id, f, g] using
                congrArg (fun e => e ≫ prod.fst) c.condition
            rw [← hfst_snd]
            simp
          · intro c m hfst hsnd
            apply hs.uniq (Cone.ofFork (Fork.ofι c.fst _)) m
            rintro (_ | _)
            · simpa using hfst
            · calc
                m ≫ s.π.app WalkingParallelPair.one =
                    m ≫ s.π.app WalkingParallelPair.zero ≫
                      K.map WalkingParallelPairHom.left := by
                  simp
                _ = c.fst ≫ K.map WalkingParallelPairHom.left := by
                  simpa [Category.assoc] using
                    congrArg (fun e => e ≫ K.map WalkingParallelPairHom.left) hfst
                _ = (Cone.ofFork (Fork.ofι c.fst _)).π.app WalkingParallelPair.one := by
                  simp
        have hpb_map := isLimitPullbackConeMapOfIsLimit G _ hpb
        refine
          { lift := fun c =>
              PullbackCone.IsLimit.lift hpb_map (c.π.app WalkingParallelPair.zero)
                (c.π.app WalkingParallelPair.zero) ?_
            fac := ?_
            uniq := ?_ }
        · apply (mapIsLimitOfPreservesOfIsLimit G _ _ (prodIsProd _ _)).hom_ext
          rintro (_ | _)
          · simp only [Category.assoc, ← G.map_comp, prod.lift_fst, BinaryFan.π_app_left,
              BinaryFan.mk_fst, f, g]
          · simp only [BinaryFan.π_app_right, BinaryFan.mk_snd, Category.assoc, ← G.map_comp,
              prod.lift_snd, f, g]
            exact
              (c.π.naturality WalkingParallelPairHom.left).symm.trans
                (c.π.naturality WalkingParallelPairHom.right)
        · intro c j
          rcases j with (_ | _)
          · exact PullbackCone.IsLimit.lift_fst hpb_map _ _ _
          · let l := PullbackCone.IsLimit.lift hpb_map (c.π.app WalkingParallelPair.zero)
                (c.π.app WalkingParallelPair.zero) (by
                  apply (mapIsLimitOfPreservesOfIsLimit G _ _ (prodIsProd _ _)).hom_ext
                  rintro (_ | _)
                  · simp only [Category.assoc, ← G.map_comp, prod.lift_fst,
                      BinaryFan.π_app_left, BinaryFan.mk_fst, f, g]
                  · simp only [BinaryFan.π_app_right, BinaryFan.mk_snd, Category.assoc,
                      ← G.map_comp, prod.lift_snd, f, g]
                    exact
                      (c.π.naturality WalkingParallelPairHom.left).symm.trans
                        (c.π.naturality WalkingParallelPairHom.right))
            have h₀ : l ≫ G.map (s.π.app WalkingParallelPair.zero) =
                c.π.app WalkingParallelPair.zero := PullbackCone.IsLimit.lift_fst hpb_map _ _ _
            calc
              l ≫ (G.mapCone s).π.app WalkingParallelPair.one =
                  l ≫ G.map (s.π.app WalkingParallelPair.zero) ≫
                    G.map (K.map WalkingParallelPairHom.left) := by
                simp [l, ← G.map_comp]
              _ = c.π.app WalkingParallelPair.zero ≫
                    G.map (K.map WalkingParallelPairHom.left) := by
                simpa [Category.assoc] using
                  congrArg (fun e => e ≫ G.map (K.map WalkingParallelPairHom.left)) h₀
              _ = c.π.app WalkingParallelPair.one := by
                simpa using (c.π.naturality WalkingParallelPairHom.left).symm
        · intro c m h
          apply PullbackCone.IsLimit.hom_ext hpb_map
          · exact (h WalkingParallelPair.zero).trans
              (PullbackCone.IsLimit.lift_fst hpb_map _ _ _).symm
          · exact (h WalkingParallelPair.zero).trans
              (PullbackCone.IsLimit.lift_snd hpb_map _ _ _).symm⟩⟩⟩

-- We hide the "implementation details" inside a namespace
namespace HasCoequalizersOfHasPushoutsAndBinaryCoproducts

variable [HasBinaryCoproducts C] [HasPushouts C]

/-- Define the equalizing object -/
abbrev constructCoequalizer (F : WalkingParallelPair ⥤ C) : C :=
  pushout (coprod.desc (𝟙 _) (F.map WalkingParallelPairHom.left))
    (coprod.desc (𝟙 _) (F.map WalkingParallelPairHom.right))

/-- Define the equalizing morphism -/
abbrev pushoutInl (F : WalkingParallelPair ⥤ C) :
    F.obj WalkingParallelPair.one ⟶ constructCoequalizer F :=
  pushout.inl _ _

set_option backward.isDefEq.respectTransparency false in
theorem pushoutInl_eq_pushout_inr (F : WalkingParallelPair ⥤ C) :
    pushoutInl F = pushout.inr _ _ := by
  convert (whisker_eq Limits.coprod.inl pushout.condition :
    (_ : F.obj _ ⟶ constructCoequalizer _) = _) <;> simp

set_option backward.isDefEq.respectTransparency false in
/-- Define the equalizing cocone -/
abbrev coequalizerCocone (F : WalkingParallelPair ⥤ C) : Cocone F :=
  Cocone.ofCofork
    (Cofork.ofπ (pushoutInl F) (by
        conv_rhs => rw [pushoutInl_eq_pushout_inr]
        convert (whisker_eq Limits.coprod.inr pushout.condition :
          (_ : F.obj _ ⟶ constructCoequalizer _) = _) using 1 <;> simp))

set_option backward.isDefEq.respectTransparency false in
/-- Show the equalizing cocone is a colimit -/
def coequalizerCoconeIsColimit (F : WalkingParallelPair ⥤ C) : IsColimit (coequalizerCocone F) where
  desc c := pushout.desc (c.ι.app _) (c.ι.app _)
  fac := by rintro c (_ | _) <;> simp
  uniq := by
    intro c m J
    have J1 : pushoutInl F ≫ m = c.ι.app WalkingParallelPair.one := by
      simpa using J WalkingParallelPair.one
    apply pushout.hom_ext
    · rw [colimit.ι_desc]
      exact J1
    · rw [colimit.ι_desc, ← pushoutInl_eq_pushout_inr]
      exact J1

end HasCoequalizersOfHasPushoutsAndBinaryCoproducts

open HasCoequalizersOfHasPushoutsAndBinaryCoproducts

-- This is not an instance, as it is not always how one wants to construct equalizers!
/-- Any category with pullbacks and binary products, has equalizers. -/
theorem hasCoequalizers_of_hasPushouts_and_binary_coproducts [HasBinaryCoproducts C]
    [HasPushouts C] : HasCoequalizers C :=
  {
    has_colimit := fun F =>
      HasColimit.mk
        { cocone := coequalizerCocone F
          isColimit := coequalizerCoconeIsColimit F } }

set_option backward.isDefEq.respectTransparency false in
/-- A functor that preserves pushouts and binary coproducts also preserves coequalizers. -/
lemma preservesCoequalizers_of_preservesPushouts_and_binaryCoproducts [HasBinaryCoproducts C]
    [PreservesColimitsOfShape (Discrete WalkingPair) G]
    [PreservesColimitsOfShape WalkingSpan G] : PreservesColimitsOfShape WalkingParallelPair G :=
  ⟨fun {K} =>
    ⟨fun {s} hs =>
      ⟨by
        let f := coprod.desc (𝟙 (K.obj WalkingParallelPair.one))
          (K.map WalkingParallelPairHom.left)
        let g := coprod.desc (𝟙 (K.obj WalkingParallelPair.one))
          (K.map WalkingParallelPairHom.right)
        have hpo : IsColimit (PushoutCocone.mk (s.ι.app WalkingParallelPair.one)
            (s.ι.app WalkingParallelPair.one) (f := f) (g := g) (by
              apply coprod.hom_ext
              · simp [f, g]
              · simp only [← Category.assoc, coprod.inr_desc, f, g]
                exact
                  (s.ι.naturality WalkingParallelPairHom.left).trans
                    (s.ι.naturality WalkingParallelPairHom.right).symm)) := by
          refine PushoutCocone.IsColimit.mk _ (fun c =>
              hs.desc (Cocone.ofCofork (Cofork.ofπ c.inl ?_))) ?_ ?_ ?_
          · have hinl_inr : c.inl = c.inr := by
              simpa only [← Category.assoc, coprod.inl_desc, Category.id_comp, f, g] using
                congrArg (fun e => coprod.inl ≫ e) c.condition
            have hleft_right : K.map WalkingParallelPairHom.left ≫ c.inl =
                K.map WalkingParallelPairHom.right ≫ c.inr := by
              simpa only [← Category.assoc, coprod.inr_desc, f, g] using
                congrArg (fun e => coprod.inr ≫ e) c.condition
            rw [← hinl_inr] at hleft_right
            exact hleft_right
          · intro c
            simp
          · intro c
            have hinl_inr : c.inl = c.inr := by
              simpa only [← Category.assoc, coprod.inl_desc, Category.id_comp, f, g] using
                congrArg (fun e => coprod.inl ≫ e) c.condition
            rw [← hinl_inr]
            simp
          · intro c m hinl hinr
            apply hs.uniq (Cocone.ofCofork (Cofork.ofπ c.inl _)) m
            rintro (_ | _)
            · calc
                s.ι.app WalkingParallelPair.zero ≫ m =
                    K.map WalkingParallelPairHom.left ≫
                      s.ι.app WalkingParallelPair.one ≫ m := by
                  simp
                _ = K.map WalkingParallelPairHom.left ≫ c.inl := by
                  simpa [Category.assoc] using
                    congrArg (fun e => K.map WalkingParallelPairHom.left ≫ e) hinl
                _ = (Cocone.ofCofork (Cofork.ofπ c.inl _)).ι.app
                    WalkingParallelPair.zero := by
                  simp
            · simpa using hinl
        have hpo_map := isColimitPushoutCoconeMapOfIsColimit G _ hpo
        let desc (c : Cocone (K ⋙ G)) :=
          PushoutCocone.IsColimit.desc hpo_map (c.ι.app WalkingParallelPair.one)
            (c.ι.app WalkingParallelPair.one) (by
              apply (mapIsColimitOfPreservesOfIsColimit G _ _ (coprodIsCoprod _ _)).hom_ext
              rintro (_ | _)
              · simp only [BinaryCofan.ι_app_left, BinaryCofan.mk_inl, ←
                  G.map_comp_assoc, coprod.inl_desc, f, g]
              · simp only [BinaryCofan.ι_app_right, BinaryCofan.mk_inr, ←
                  G.map_comp_assoc, coprod.inr_desc, f, g]
                exact
                  (c.ι.naturality WalkingParallelPairHom.left).trans
                    (c.ι.naturality WalkingParallelPairHom.right).symm)
        refine
          { desc := desc
            fac := ?_
            uniq := ?_ }
        · intro c j
          rcases j with (_ | _)
          · let d := desc c
            change (G.mapCocone s).ι.app WalkingParallelPair.zero ≫ d =
              c.ι.app WalkingParallelPair.zero
            have h₁ : G.map (s.ι.app WalkingParallelPair.one) ≫ d =
                c.ι.app WalkingParallelPair.one := by
              exact PushoutCocone.IsColimit.inl_desc hpo_map _ _ _
            calc
              (G.mapCocone s).ι.app WalkingParallelPair.zero ≫ d =
                  G.map (K.map WalkingParallelPairHom.left) ≫
                    G.map (s.ι.app WalkingParallelPair.one) ≫ d := by
                have hnat := G.congr_map (s.ι.naturality WalkingParallelPairHom.left)
                simp only [G.map_comp, Functor.const_obj_map] at hnat
                simpa [Category.assoc] using congrArg (fun e => e ≫ d) hnat.symm
              _ = G.map (K.map WalkingParallelPairHom.left) ≫
                    c.ι.app WalkingParallelPair.one := by
                simpa [Category.assoc] using
                  congrArg (fun e => G.map (K.map WalkingParallelPairHom.left) ≫ e) h₁
              _ = c.ι.app WalkingParallelPair.zero := by
                simpa using c.ι.naturality WalkingParallelPairHom.left
          · change G.map (s.ι.app WalkingParallelPair.one) ≫ desc c =
              c.ι.app WalkingParallelPair.one
            exact PushoutCocone.IsColimit.inl_desc hpo_map _ _ _
        · intro c m h
          apply PushoutCocone.IsColimit.hom_ext hpo_map
          · change G.map (s.ι.app WalkingParallelPair.one) ≫ m =
              G.map (s.ι.app WalkingParallelPair.one) ≫ desc c
            exact (h WalkingParallelPair.one).trans
              (PushoutCocone.IsColimit.inl_desc hpo_map _ _ _).symm
          · change G.map (s.ι.app WalkingParallelPair.one) ≫ m =
              G.map (s.ι.app WalkingParallelPair.one) ≫ desc c
            exact (h WalkingParallelPair.one).trans
              (PushoutCocone.IsColimit.inr_desc hpo_map _ _ _).symm⟩⟩⟩

end CategoryTheory.Limits
