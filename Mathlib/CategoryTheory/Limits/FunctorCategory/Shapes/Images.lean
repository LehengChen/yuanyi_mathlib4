/-
Copyright (c) 2025 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Images
public import Mathlib.CategoryTheory.Subfunctor.Image
public import Mathlib.Tactic.CategoryTheory.CategoryStar

/-!

# The category of type-valued functors has images
-/

@[expose] public section

universe u

namespace CategoryTheory.FunctorToTypes

open Limits

variable {C : Type*} [Category* C]

attribute [local simp] FunctorToTypes.naturality in
/-- The image of a natural transformation between type-valued functors is a `MonoFactorisation` -/
@[simps]
def monoFactorisation {F G : C ⥤ Type u} (f : F ⟶ G) : MonoFactorisation f where
  I := (Subfunctor.range f).toFunctor
  m := (Subfunctor.range f).ι
  e := Subfunctor.toRange f

/-- The image of a natural transformation between type-valued functors satisfies the universal
property of images -/
noncomputable def monoFactorisationIsImage {F G : C ⥤ Type u} (f : F ⟶ G) :
    IsImage <| monoFactorisation f where
  lift H := {
    app X := fun ⟨x, hx⟩ ↦ H.e.app _ hx.choose
    naturality X Y g := by
      ext
      apply injective_of_mono (H.m.app Y)
      simp [FunctorToTypes.naturality]
      grind }
  lift_fac H := by
    ext
    simp
    grind

instance : HasImages (C ⥤ Type*) where
  has_image f := { exists_image := ⟨ { F := _, isImage := monoFactorisationIsImage f } ⟩ }

instance : HasStrongEpiMonoFactorisations (C ⥤ Type*) where
  has_fac {F G} f := ⟨
    { monoFactorisation f with
      e_strong_epi := by
        change StrongEpi (Subfunctor.toRange f)
        apply StrongEpi.mk'
        intro X Y z hz u v sq
        let liftApp : (T : C) → (Subfunctor.range f).toFunctor.obj T → X.obj T :=
          fun T x ↦ u.app T x.2.choose
        have hright : ∀ (T : C) (x : (Subfunctor.range f).toFunctor.obj T),
            z.app T (liftApp T x) = v.app T x := by
          intro T x
          have hx : (Subfunctor.toRange f).app T x.2.choose = x := by
            apply Subtype.ext
            exact x.2.choose_spec
          have hsq := congrArg (fun (α : F ⟶ Y) ↦ α.app T x.2.choose) sq.w
          simpa [NatTrans.comp_app, liftApp, hx] using hsq
        let l : (Subfunctor.range f).toFunctor ⟶ X :=
          { app T x := liftApp T x
            naturality T T' g := by
              ext x
              apply injective_of_mono (z.app T')
              calc
                z.app T' (liftApp T' ((Subfunctor.range f).toFunctor.map g x)) =
                    v.app T' ((Subfunctor.range f).toFunctor.map g x) := hright T' _
                _ = Y.map g (v.app T x) := FunctorToTypes.naturality _ _ v g x
                _ = Y.map g (z.app T (liftApp T x)) := by rw [← hright T x]
                _ = z.app T' (X.map g (liftApp T x)) :=
                  (FunctorToTypes.naturality _ _ z g (liftApp T x)).symm }
        exact CommSq.HasLift.mk'
          { l := l
            fac_left := by
              ext T x
              apply injective_of_mono (z.app T)
              calc
                z.app T (l.app T ((Subfunctor.toRange f).app T x)) =
                    v.app T ((Subfunctor.toRange f).app T x) := by simpa [l] using hright T _
                _ = z.app T (u.app T x) := by
                  have hsq := congrArg (fun (α : F ⟶ Y) ↦ α.app T x) sq.w
                  simpa [NatTrans.comp_app] using hsq.symm
            fac_right := by
              ext T x
              simpa [l] using hright T x } }⟩

end CategoryTheory.FunctorToTypes
