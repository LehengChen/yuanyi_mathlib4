/-
Copyright (c) 2025 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer
-/
module

public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Limits.Final

/-!
# Finality on Costructured Arrow categories

## References

* [M. Kashiwara, P. Schapira, *Categories and Sheaves*][Kashiwara2006], Proposition 3.1.8(i)
-/

public section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

namespace Functor

open Limits Functor CostructuredArrow

section Small

variable {A : Type u₁} [SmallCategory A] {B : Type u₁} [SmallCategory B]
variable {T : Type u₁} [SmallCategory T]

attribute [local instance] Grothendieck.final_map

set_option backward.isDefEq.respectTransparency false in
/-- The version of `final_of_final_costructuredArrowToOver` on small categories used to prove the
full statement. -/
private lemma final_of_final_costructuredArrowToOver_small (L : A ⥤ T) (R : B ⥤ T) [Final R]
    [∀ b : B, Final (CostructuredArrow.toOver L (R.obj b))] : Final L := by
  rw [final_iff_isIso_colimit_pre]
  intro G
  have : ∀ (b : B), Final ((whiskerLeft R (preFunctor L (𝟭 T))).app b).toFunctor := fun b =>
    inferInstanceAs (Final (CostructuredArrow.toOver L (R.obj b)))
  let i : colimit (L ⋙ G) ≅ colimit G :=
    calc colimit (L ⋙ G) ≅ colimit <| grothendieckProj L ⋙ L ⋙ G :=
            colimitIsoColimitGrothendieck L (L ⋙ G)
      _ ≅ colimit <| Grothendieck.pre (functor L) R ⋙ grothendieckProj L ⋙ L ⋙ G :=
            (Final.colimitIso (Grothendieck.pre (functor L) R) (grothendieckProj L ⋙ L ⋙ G)).symm
      _ ≅ colimit <| Grothendieck.map (whiskerLeft _ (preFunctor L (𝟭 T))) ⋙
            grothendieckPrecompFunctorToComma (𝟭 T) R ⋙ Comma.fst (𝟭 T) R ⋙ G :=
              HasColimit.isoOfNatIso (NatIso.ofComponents (fun _ => Iso.refl _))
      _ ≅ colimit <| grothendieckPrecompFunctorToComma (𝟭 T) R ⋙ Comma.fst (𝟭 T) R ⋙ G :=
            Final.colimitIso _ _
      _ ≅ colimit <| Grothendieck.pre (functor (𝟭 T)) R ⋙ grothendieckProj (𝟭 T) ⋙ G :=
            HasColimit.isoOfNatIso (Iso.refl _)
      _ ≅ colimit <| grothendieckProj (𝟭 T) ⋙ G :=
            Final.colimitIso _ _
      _ ≅ colimit G := (colimitIsoColimitGrothendieck (𝟭 T) G).symm
  convert Iso.isIso_hom i
  simp only [Iso.trans_def, comp_obj, grothendieckProj_obj, Grothendieck.pre_obj_base,
    Grothendieck.pre_obj_fiber, Iso.trans_assoc, Iso.trans_hom, Iso.symm_hom, i]
  rw [← Iso.inv_comp_eq, Iso.eq_inv_comp]
  apply colimit.hom_ext (fun _ => by simp)

end Small

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
variable {T : Type u₃} [Category.{v₃} T]

set_option backward.isDefEq.respectTransparency false in
/-- A functor `L : A ⥤ T` is final if there is a final functor `R : B ⥤ T` such that for all
`b : B`, the canonical functor `CostructuredArrow L (R.obj b) ⥤ Over (R.obj b)` is final. -/
theorem final_of_final_costructuredArrowToOver (L : A ⥤ T) (R : B ⥤ T) [Final R]
    [hB : ∀ b : B, Final (CostructuredArrow.toOver L (R.obj b))] : Final L := by
  let sA : A ≌ AsSmall.{max u₁ u₂ u₃ v₁ v₂ v₃} A := AsSmall.equiv
  let sB : B ≌ AsSmall.{max u₁ u₂ u₃ v₁ v₂ v₃} B := AsSmall.equiv
  let sT : T ≌ AsSmall.{max u₁ u₂ u₃ v₁ v₂ v₃} T := AsSmall.equiv
  let L' := sA.inverse ⋙ L ⋙ sT.functor
  let R' := sB.inverse ⋙ R ⋙ sT.functor
  have (b : _) : (CostructuredArrow.toOver L' (R'.obj b)).Final := by
    let y := R.obj (sB.inverse.obj b); let x := R'.obj b
    change Final (pre sA.inverse _ x ⋙ CostructuredArrow.toOver (L ⋙ sT.functor) x)
    exact (final_iff_equivalence_comp _ _).1 <| (final_iff_equivalence_comp _ _).2 <|
      (final_natIso_iff (NatIso.ofComponents (fun X => Over.isoMk (Iso.refl _)) :
        CostructuredArrow.toOver L y ⋙ Over.post sT.functor ≅
          post L sT.functor y ⋙ CostructuredArrow.toOver _ x)).1 <|
      (final_iff_comp_equivalence _ _).1 (hB _)
  have h : Final L' := final_of_final_costructuredArrowToOver_small L' R'
  simpa [L'] using (final_iff_comp_equivalence _ _).2 <| (final_iff_equivalence_comp _ _).2 h

end Functor

end CategoryTheory
