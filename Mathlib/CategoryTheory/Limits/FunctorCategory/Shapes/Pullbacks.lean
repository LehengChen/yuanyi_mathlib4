/-
Copyright (c) 2025 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Pullbacks in functor categories

We prove the isomorphism `(pullback f g).obj d ≅ pullback (f.app d) (g.app d)`.

-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] {F G H : D ⥤ C}

section Pullback

set_option backward.isDefEq.respectTransparency false in
/-- Given functors `F G H` and natural transformations `f : F ⟶ H` and `g : g : G ⟶ H`, together
with a collection of limiting pullback cones for each cospan `F X ⟶ H X, G X ⟶ H X`, we can stitch
them together to give a pullback cone for the cospan formed by `f` and `g`.
`combinePullbackConesIsLimit` shows that this pullback cone is limiting. -/
@[simps!]
def PullbackCone.combine (f : F ⟶ H) (g : G ⟶ H) (c : ∀ X, PullbackCone (f.app X) (g.app X))
    (hc : ∀ X, IsLimit (c X)) : PullbackCone f g :=
  PullbackCone.mk (W := {
    obj X := (c X).pt
    map {X Y} h := (hc Y).lift ⟨_, (c X).π ≫ cospanHomMk (H.map h) (F.map h) (G.map h)⟩
    map_id _ := (hc _).hom_ext <| by rintro (_ | _ | _); all_goals simp
    map_comp _ _ := (hc _).hom_ext <| by rintro (_ | _ | _); all_goals simp })
    { app X := (c X).fst }
    { app X := (c X).snd }
    (by ext; simp [(c _).condition])

/--
The pullback cone `combinePullbackCones` is limiting.
-/
def PullbackCone.combineIsLimit (f : F ⟶ H) (g : G ⟶ H)
    (c : ∀ X, PullbackCone (f.app X) (g.app X)) (hc : ∀ X, IsLimit (c X)) :
    IsLimit (combine f g c hc) :=
  evaluationJointlyReflectsLimits _ fun k ↦ by
    refine IsLimit.equivOfNatIsoOfIso ?_ _ _ ?_ (hc k)
    · exact cospanIsoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    · refine Cone.ext (Iso.refl _) ?_
      rintro (_ | _ | _)
      all_goals cat_disch

/-- Evaluating a pullback amounts to taking the pullback of the evaluations. -/
noncomputable def pullbackObjIso (f : F ⟶ H) (g : G ⟶ H) (d : D)
    [HasPullback f g] [∀ X, HasPullback (f.app X) (g.app X)] :
    (pullback f g).obj d ≅ pullback (f.app d) (g.app d) := by
  let c : ∀ X, PullbackCone (f.app X) (g.app X) := fun X ↦
    pullback.cone (f.app X) (g.app X)
  let hc : ∀ X, IsLimit (c X) := fun X ↦ pullback.isLimit (f.app X) (g.app X)
  exact (IsLimit.conePointUniqueUpToIso (limit.isLimit (cospan f g))
    (PullbackCone.combineIsLimit f g c hc)).app d

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
theorem pullbackObjIso_hom_comp_fst (f : F ⟶ H) (g : G ⟶ H) (d : D)
    [HasPullback f g] [∀ X, HasPullback (f.app X) (g.app X)] :
    (pullbackObjIso f g d).hom ≫ pullback.fst (f.app d) (g.app d) = (pullback.fst f g).app d := by
  let c : ∀ X, PullbackCone (f.app X) (g.app X) :=
    fun X ↦ pullback.cone (f.app X) (g.app X)
  let hc : ∀ X, IsLimit (c X) := fun X ↦ pullback.isLimit (f.app X) (g.app X)
  simpa [pullbackObjIso, c, hc, PullbackCone.combine] using congr_app
    (IsLimit.conePointUniqueUpToIso_hom_comp (limit.isLimit (cospan f g))
      (PullbackCone.combineIsLimit f g c hc) WalkingCospan.left) d

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
theorem pullbackObjIso_hom_comp_snd (f : F ⟶ H) (g : G ⟶ H) (d : D)
    [HasPullback f g] [∀ X, HasPullback (f.app X) (g.app X)] :
    (pullbackObjIso f g d).hom ≫ pullback.snd (f.app d) (g.app d) = (pullback.snd f g).app d := by
  let c : ∀ X, PullbackCone (f.app X) (g.app X) :=
    fun X ↦ pullback.cone (f.app X) (g.app X)
  let hc : ∀ X, IsLimit (c X) := fun X ↦ pullback.isLimit (f.app X) (g.app X)
  simpa [pullbackObjIso, c, hc, PullbackCone.combine] using congr_app
    (IsLimit.conePointUniqueUpToIso_hom_comp (limit.isLimit (cospan f g))
      (PullbackCone.combineIsLimit f g c hc) WalkingCospan.right) d

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
theorem pullbackObjIso_inv_comp_fst (f : F ⟶ H) (g : G ⟶ H) (d : D)
    [HasPullback f g] [∀ X, HasPullback (f.app X) (g.app X)] :
    (pullbackObjIso f g d).inv ≫ (pullback.fst f g).app d = pullback.fst (f.app d) (g.app d) := by
  rw [Iso.inv_comp_eq]
  simp

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
theorem pullbackObjIso_inv_comp_snd (f : F ⟶ H) (g : G ⟶ H) (d : D)
    [HasPullback f g] [∀ X, HasPullback (f.app X) (g.app X)] :
    (pullbackObjIso f g d).inv ≫ (pullback.snd f g).app d = pullback.snd (f.app d) (g.app d) := by
  rw [Iso.inv_comp_eq]
  simp

end Pullback

section Pushout

/-- Evaluating a pushout amounts to taking the pushout of the evaluations. -/
noncomputable def pushoutObjIso (f : F ⟶ G) (g : F ⟶ H) (d : D)
    [HasPushout f g] [∀ X, HasPushout (f.app X) (g.app X)] :
    (pushout f g).obj d ≅ pushout (f.app d) (g.app d) := by
  let c : ∀ X, ColimitCocone ((span f g).flip.obj X) := fun X ↦ by
    let F' := (span f g).flip.obj X
    let t : PushoutCocone (F'.map WalkingSpan.Hom.fst) (F'.map WalkingSpan.Hom.snd) := by
      change PushoutCocone (f.app X) (g.app X)
      exact pushout.cocone (f.app X) (g.app X)
    let ht : IsColimit t := by
      change IsColimit (pushout.cocone (f.app X) (g.app X))
      exact pushout.isColimit (f.app X) (g.app X)
    let e : (Cocone.precompose (diagramIsoSpan F').inv).obj
        (Cocone.ofPushoutCocone t) ≅ t := by
      refine Cocone.ext (Iso.refl _) ?_
      rintro (_ | _ | _) <;> simp [Cocone.ofPushoutCocone]
    exact ⟨Cocone.ofPushoutCocone t,
      (IsColimit.equivOfNatIsoOfIso (diagramIsoSpan F') (Cocone.ofPushoutCocone t) t e).symm ht⟩
  simpa [c] using (IsColimit.coconePointUniqueUpToIso (colimit.isColimit (span f g))
    (combinedIsColimit (span f g) c)).app d

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
theorem inl_comp_pushoutObjIso_hom (f : F ⟶ G) (g : F ⟶ H) (d : D)
    [HasPushout f g] [∀ X, HasPushout (f.app X) (g.app X)] :
    (pushout.inl f g).app d ≫ (pushoutObjIso f g d).hom = pushout.inl (f.app d) (g.app d) := by
  let c : ∀ X, ColimitCocone ((span f g).flip.obj X) := fun X ↦ by
    let F' := (span f g).flip.obj X
    let t : PushoutCocone (F'.map WalkingSpan.Hom.fst) (F'.map WalkingSpan.Hom.snd) := by
      change PushoutCocone (f.app X) (g.app X)
      exact pushout.cocone (f.app X) (g.app X)
    let ht : IsColimit t := by
      change IsColimit (pushout.cocone (f.app X) (g.app X))
      exact pushout.isColimit (f.app X) (g.app X)
    let e : (Cocone.precompose (diagramIsoSpan F').inv).obj
        (Cocone.ofPushoutCocone t) ≅ t := by
      refine Cocone.ext (Iso.refl _) ?_
      rintro (_ | _ | _) <;> simp [Cocone.ofPushoutCocone]
    exact ⟨Cocone.ofPushoutCocone t,
      (IsColimit.equivOfNatIsoOfIso (diagramIsoSpan F') (Cocone.ofPushoutCocone t) t e).symm ht⟩
  refine (congr_app
    (IsColimit.comp_coconePointUniqueUpToIso_hom (colimit.isColimit (span f g))
      (combinedIsColimit (span f g) c) WalkingSpan.left) d).trans ?_
  simp [c, Cocone.ofPushoutCocone]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
theorem inr_comp_pushoutObjIso_hom (f : F ⟶ G) (g : F ⟶ H) (d : D)
    [HasPushout f g] [∀ X, HasPushout (f.app X) (g.app X)] :
    (pushout.inr f g).app d ≫ (pushoutObjIso f g d).hom = pushout.inr (f.app d) (g.app d) := by
  let c : ∀ X, ColimitCocone ((span f g).flip.obj X) := fun X ↦ by
    let F' := (span f g).flip.obj X
    let t : PushoutCocone (F'.map WalkingSpan.Hom.fst) (F'.map WalkingSpan.Hom.snd) := by
      change PushoutCocone (f.app X) (g.app X)
      exact pushout.cocone (f.app X) (g.app X)
    let ht : IsColimit t := by
      change IsColimit (pushout.cocone (f.app X) (g.app X))
      exact pushout.isColimit (f.app X) (g.app X)
    let e : (Cocone.precompose (diagramIsoSpan F').inv).obj
        (Cocone.ofPushoutCocone t) ≅ t := by
      refine Cocone.ext (Iso.refl _) ?_
      rintro (_ | _ | _) <;> simp [Cocone.ofPushoutCocone]
    exact ⟨Cocone.ofPushoutCocone t,
      (IsColimit.equivOfNatIsoOfIso (diagramIsoSpan F') (Cocone.ofPushoutCocone t) t e).symm ht⟩
  refine (congr_app
    (IsColimit.comp_coconePointUniqueUpToIso_hom (colimit.isColimit (span f g))
      (combinedIsColimit (span f g) c) WalkingSpan.right) d).trans ?_
  simp [c, Cocone.ofPushoutCocone]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
theorem inl_comp_pushoutObjIso_inv (f : F ⟶ G) (g : F ⟶ H) (d : D)
    [HasPushout f g] [∀ X, HasPushout (f.app X) (g.app X)] :
    pushout.inl (f.app d) (g.app d) ≫ (pushoutObjIso f g d).inv = (pushout.inl f g).app d := by
  rw [Iso.comp_inv_eq]
  simp

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
theorem inr_comp_pushoutObjIso_inv (f : F ⟶ G) (g : F ⟶ H) (d : D)
    [HasPushout f g] [∀ X, HasPushout (f.app X) (g.app X)] :
    pushout.inr (f.app d) (g.app d) ≫ (pushoutObjIso f g d).inv = (pushout.inr f g).app d := by
  rw [Iso.comp_inv_eq]
  simp

end Pushout

end CategoryTheory.Limits
