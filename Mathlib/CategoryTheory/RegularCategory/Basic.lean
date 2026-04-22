/-
Copyright (c) 2025 Fernando Chu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Chu
-/
module

public import Mathlib.CategoryTheory.ExtremalEpi
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.Sites.Coherent.Basic

/-!
# Regular categories

A regular category is a category with finite limits such that each kernel pair has a coequalizer
and such that regular epimorphisms are stable under pullback.

These categories provide a good ground to develop the calculus of relations, as well as being the
semantics for regular logic.

## Main results

* We show that every regular category has strong epi-mono factorisations, following Theorem 1.11
  in [Gran2021].
* We show that every regular category satisfies Frobenius reciprocity. That is, that in their
  internal language, we have `∃ x, (P(x) ⊓ Q)` iff `(∃ x, P(x)) ⊓ Q`, for a proposition `Q` not
  depending on `x`.

## Future work
* Show that every topos is regular
* Show that regular logic has an interpretation in regular categories

## References
* [Marino Gran, An Introduction to Regular Categories][Gran2021]
* <https://ncatlab.org/nlab/show/regular+category>
-/

@[expose] public section

open CategoryTheory Limits

universe u v

namespace CategoryTheory

variable (C : Type u) [Category.{v} C]

/--
A regular category is a category with finite limits, such that every kernel pair has a coequalizer,
and such that regular epimorphisms are stable under base change.
-/
class Regular extends HasFiniteLimits C where
  hasCoequalizer_of_isKernelPair {X Y Z : C} {f : X ⟶ Y} {g₁ g₂ : Z ⟶ X} :
    IsKernelPair f g₁ g₂ → HasCoequalizer g₁ g₂
  regularEpiIsStableUnderBaseChange : MorphismProperty.IsStableUnderBaseChange (.regularEpi C)

variable {C} [Regular C]

instance {X Y B : C} (f : X ⟶ B) (g : Y ⟶ B) [HasPullback f g] [IsRegularEpi f] :
    IsRegularEpi (pullback.snd f g) := by
  apply Regular.regularEpiIsStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback f g)
  dsimp [MorphismProperty.regularEpi]
  infer_instance

instance {X Y B : C} (f : X ⟶ B) (g : Y ⟶ B) [HasPullback f g] [IsRegularEpi g] :
    IsRegularEpi (pullback.fst f g) := by
  apply Regular.regularEpiIsStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback f g).flip
  dsimp [MorphismProperty.regularEpi]
  infer_instance

instance : Preregular C where
  exists_fac f g := ⟨_, pullback.snd g f, inferInstance, pullback.fst g f, pullback.condition⟩

variable {X Y : C} (f : X ⟶ Y)

namespace Regular

section StrongEpiMonoFactorisation

local instance : HasCoequalizer (pullback.fst f f) (pullback.snd f f) :=
  Regular.hasCoequalizer_of_isKernelPair <| IsKernelPair.of_hasPullback f

set_option backward.isDefEq.respectTransparency false in
instance : Mono (coequalizer.desc f pullback.condition) := by
  let m := (coequalizer.desc f pullback.condition)
  let e := coequalizer.π (pullback.fst f f) (pullback.snd f f)
  constructor
  intro Z a b hab
  let p : pullback e a ⟶ Z := pullback.snd e a
  let q : pullback e (p ≫ b) ⟶ pullback e a := pullback.snd e (p ≫ b)
  have hp : q ≫ p ≫ a = q ≫ pullback.fst e a ≫ e := by
    simp [p, pullback.condition]
  have hq : q ≫ p ≫ b = pullback.fst e (p ≫ b) ≫ e := by
    simp [q, pullback.condition]
  rw [← cancel_epi (q ≫ p)]
  calc
    (q ≫ p) ≫ a = (q ≫ pullback.fst e a) ≫ e := by
      simpa [Category.assoc] using hp
    _ = pullback.fst e (p ≫ b) ≫ e := by
      let r : pullback e (p ≫ b) ⟶ pullback f f :=
        pullback.lift (q ≫ pullback.fst e a) (pullback.fst e (p ≫ b))
          (by
            calc
              (q ≫ pullback.fst e a) ≫ f = (q ≫ p) ≫ a ≫ m := by
                simpa [m, e, Category.assoc] using congrArg (fun u ↦ u ≫ m) hp.symm
              _ = (q ≫ p) ≫ b ≫ m := by
                simpa [m, Category.assoc] using congrArg (fun u ↦ q ≫ p ≫ u) hab
              _ = pullback.fst e (p ≫ b) ≫ f := by
                simpa [m, e, Category.assoc] using congrArg (fun u ↦ u ≫ m) hq)
      simpa [r] using congrArg (fun u ↦ r ≫ u)
        (coequalizer.condition (pullback.fst f f) (pullback.snd f f))
    _ = (q ≫ p) ≫ b := by
      simpa [Category.assoc] using hq.symm

set_option backward.isDefEq.respectTransparency false in
/--
In a regular category, every morphism `f : X ⟶ Y` factors as `e ≫ m`, where `e` is the projection
map to the coequalizer of the kernel pair of `f`, and `m` is the canonical map from that
coequalizer to `Y`. In particular, `f` factors as a strong epimorphism followed by a monomorphism.
-/
noncomputable def strongEpiMonoFactorisation : StrongEpiMonoFactorisation f where
  I := coequalizer (pullback.fst f f) (pullback.snd f f)
  m := coequalizer.desc f pullback.condition
  e := coequalizer.π (pullback.fst f f) (pullback.snd f f)

instance : IsRegularEpi (strongEpiMonoFactorisation f).e := by
  dsimp [strongEpiMonoFactorisation]
  infer_instance

/--
In a regular category, every morphism `f` factors as `e ≫ m`, with `e` a strong epimorphism
and `m` a monomorphism.
-/
instance hasStrongEpiMonoFactorisations : HasStrongEpiMonoFactorisations C where
  has_fac f := ⟨strongEpiMonoFactorisation f⟩

set_option backward.isDefEq.respectTransparency false in
/-- In a regular category, every extremal epimorphism is a regular epimorphism. -/
noncomputable def regularEpiOfExtremalEpi [h : ExtremalEpi f] : RegularEpi f :=
  have := h.isIso (strongEpiMonoFactorisation f).e (strongEpiMonoFactorisation f).m (by simp)
  RegularEpi.ofArrowIso (Arrow.isoMk (f := .mk (strongEpiMonoFactorisation f).e) (Iso.refl _)
    (asIso (strongEpiMonoFactorisation f).m)) (IsRegularEpi.getStruct _)

instance isRegularEpi_of_extremalEpi (f : X ⟶ Y) [ExtremalEpi f] : IsRegularEpi f :=
  ⟨⟨regularEpiOfExtremalEpi f⟩⟩

end StrongEpiMonoFactorisation

section Frobenius

open Subobject

variable {A B : C} (f : A ⟶ B) (A' : Subobject A) (B' : Subobject B)

set_option backward.isDefEq.respectTransparency false in
/--
Given a morphism `f : A ⟶ B` and subobjects `A' ⟶ A` and `B' ⟶ B`, we have a canonical morphism
`(A' ⊓ (Subobject.pullback f).obj B') ⟶ ((«exists» f).obj A' ⊓ B')`.
This morphism is part of a `StrongEpiMonoFactorisation` of
`(A' ⊓ (Subobject.pullback f).obj B').arrow ≫ f`, see `frobeniusStrongEpiMonoFactorisation`.
-/
noncomputable def frobeniusMorphism :
    underlying.obj (A' ⊓ (Subobject.pullback f).obj B') ⟶
      underlying.obj ((«exists» f).obj A' ⊓ B') :=
  (inf_isPullback ((«exists» f).obj A') B').flip.lift
    ((ofLE _ _ (inf_le_right A' ((Subobject.pullback f).obj B'))) ≫ (pullbackπ _ _))
    ((ofLE _ _ (inf_le_left A' ((Subobject.pullback f).obj B'))) ≫ (imageFactorisation f A').F.e)
    (by simp [← imageFactorisation_F_m, (isPullback _ _).w])

set_option backward.isDefEq.respectTransparency false in
lemma frobeniusMorphism_isPullback :
    IsPullback (frobeniusMorphism f A' B')
      ((ofLE _ _ (inf_le_left A' ((Subobject.pullback f).obj B'))))
      ((ofLE _ _ (inf_le_left ((«exists» f).obj A') B')))
      (imageFactorisation _ _).F.e := by
  apply IsPullback.of_right (t := (inf_isPullback ((«exists» f).obj A') B').flip)
    (p := by simp [frobeniusMorphism])
  simpa [frobeniusMorphism, IsPullback.lift_fst, ← imageFactorisation_F_m,
    (isPullback f B').paste_horiz_iff] using
    (inf_isPullback A' ((Subobject.pullback f).obj B')).flip

set_option backward.isDefEq.respectTransparency false in
instance : IsRegularEpi (frobeniusMorphism f A' B') := by
  apply regularEpiIsStableUnderBaseChange.of_isPullback (frobeniusMorphism_isPullback f A' B').flip
  have := strongEpi_of_strongEpiMonoFactorisation (strongEpiMonoFactorisation (A'.arrow ≫ f))
    (imageFactorisation f A').isImage
  simp only [MorphismProperty.regularEpi_iff]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/--
Given a morphism `f : A ⟶ B` and subobjects `A' ⟶ A` and `B' ⟶ B`, the `frobeniusMorphism`
gives a `StrongEpiMonoFactorisation` of `(A' ⊓ (Subobject.pullback f).obj B').arrow ≫ f` through
`((«exists» f).obj A' ⊓ B').arrow`.
This is an auxiliary definition to show `frobenius_reciprocity`.
-/
@[simps!]
noncomputable def frobeniusStrongEpiMonoFactorisation :
    StrongEpiMonoFactorisation ((A' ⊓ (Subobject.pullback f).obj B').arrow ≫ f) where
  I := underlying.obj <| («exists» f).obj A' ⊓ B'
  m := ((«exists» f).obj A' ⊓ B').arrow
  e := frobeniusMorphism f A' B'
  fac := by
    rw [frobeniusMorphism, ← inf_comp_left, ← Category.assoc,
      (inf_isPullback ((«exists» f).obj A') B').flip.lift_snd]
    simp [← imageFactorisation_F_m]

/--
Regular categories satisfy Frobenius reciprocity. That is, in the internal language of regular
categories, we have `∃ x, (P(x) ⊓ Q)` iff `(∃ x, P(x)) ⊓ Q`, for a proposition `Q` not depending on
`x`.
-/
theorem exists_inf_pullback_eq_exists_inf :
    («exists» f).obj (A' ⊓ (Subobject.pullback f).obj B') = («exists» f).obj A' ⊓ B' :=
  eq_of_comm
    (IsImage.isoExt (imageFactorisation _ _).isImage
      (frobeniusStrongEpiMonoFactorisation f A' B').toMonoIsImage)
    (IsImage.isoExt_hom_m (imageFactorisation _ _).isImage
      (frobeniusStrongEpiMonoFactorisation f A' B').toMonoIsImage)

end Frobenius

end Regular

end CategoryTheory
