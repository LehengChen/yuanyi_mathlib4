/-
Copyright (c) 2024 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# (Co)products in functor categories

Given `f : α → D ⥤ C`, we prove the isomorphisms
`(∏ᶜ f).obj d ≅ ∏ᶜ (fun s => (f s).obj d)` and `(∐ f).obj d ≅ ∐ (fun s => (f s).obj d)`.

-/

@[expose] public section

universe w v v₁ v₂ u u₁ u₂

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] {D : Type u₁} [Category.{v₁} D]
  {α : Type w}

section Product

/-- Evaluating a product of functors amounts to taking the product of the evaluations. -/
noncomputable def piObjIso (f : α → D ⥤ C) (d : D)
    [HasProduct f] [HasProduct (fun s => (f s).obj d)]
    [PreservesLimit (Discrete.functor f) ((evaluation D C).obj d)] :
    (∏ᶜ f).obj d ≅ ∏ᶜ (fun s => (f s).obj d) :=
  preservesLimitIso ((evaluation D C).obj d) (Discrete.functor f) ≪≫
    HasLimit.isoOfNatIso (Discrete.natIso fun s => Iso.refl ((f s.as).obj d))

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
theorem piObjIso_hom_comp_π (f : α → D ⥤ C) (d : D)
    [HasProduct f] [HasProduct (fun s => (f s).obj d)]
    [PreservesLimit (Discrete.functor f) ((evaluation D C).obj d)] (s : α) :
    (piObjIso f d).hom ≫ Pi.π (fun s => (f s).obj d) s = (Pi.π f s).app d := by
  simp [piObjIso]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
theorem piObjIso_inv_comp_π (f : α → D ⥤ C) (d : D)
    [HasProduct f] [HasProduct (fun s => (f s).obj d)]
    [PreservesLimit (Discrete.functor f) ((evaluation D C).obj d)] (s : α) :
    (piObjIso f d).inv ≫ (Pi.π f s).app d = Pi.π (fun s => (f s).obj d) s := by
  let e : Discrete.functor f ⋙ (evaluation D C).obj d ≅
      Discrete.functor (fun s => (f s).obj d) :=
    Discrete.natIso fun s => Iso.refl ((f s.as).obj d)
  dsimp [piObjIso]
  change ((HasLimit.isoOfNatIso e).inv ≫
      (preservesLimitIso ((evaluation D C).obj d) (Discrete.functor f)).inv) ≫
        ((evaluation D C).obj d).map (limit.π (Discrete.functor f) (Discrete.mk s)) =
    Pi.π (fun s => (f s).obj d) s
  rw [Category.assoc, preservesLimitIso_inv_π]
  simp [e, Pi.π]

end Product

section Coproduct

/-- Evaluating a coproduct of functors amounts to taking the coproduct of the evaluations. -/
noncomputable def sigmaObjIso (f : α → D ⥤ C) (d : D)
    [HasCoproduct f] [HasCoproduct (fun s => (f s).obj d)]
    [PreservesColimit (Discrete.functor f) ((evaluation D C).obj d)] :
    (∐ f).obj d ≅ ∐ (fun s => (f s).obj d) :=
  preservesColimitIso ((evaluation D C).obj d) (Discrete.functor f) ≪≫
    HasColimit.isoOfNatIso (Discrete.natIso fun s => Iso.refl ((f s.as).obj d))

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
theorem ι_comp_sigmaObjIso_hom (f : α → D ⥤ C) (d : D)
    [HasCoproduct f] [HasCoproduct (fun s => (f s).obj d)]
    [PreservesColimit (Discrete.functor f) ((evaluation D C).obj d)] (s : α) :
    (Sigma.ι f s).app d ≫ (sigmaObjIso f d).hom = Sigma.ι (fun s => (f s).obj d) s := by
  let e : Discrete.functor f ⋙ (evaluation D C).obj d ≅
      Discrete.functor (fun s => (f s).obj d) :=
    Discrete.natIso fun s => Iso.refl ((f s.as).obj d)
  dsimp [sigmaObjIso, Sigma.ι]
  change ((evaluation D C).obj d).map (colimit.ι (Discrete.functor f) (Discrete.mk s)) ≫
      (preservesColimitIso ((evaluation D C).obj d) (Discrete.functor f)).hom ≫
        (HasColimit.isoOfNatIso e).hom =
    colimit.ι (Discrete.functor (fun s => (f s).obj d)) (Discrete.mk s)
  rw [← Category.assoc, ι_preservesColimitIso_hom]
  simp [e]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
theorem ι_comp_sigmaObjIso_inv (f : α → D ⥤ C) (d : D)
    [HasCoproduct f] [HasCoproduct (fun s => (f s).obj d)]
    [PreservesColimit (Discrete.functor f) ((evaluation D C).obj d)] (s : α) :
    Sigma.ι (fun s => (f s).obj d) s ≫ (sigmaObjIso f d).inv = (Sigma.ι f s).app d := by
  simp [sigmaObjIso]

end Coproduct

end CategoryTheory.Limits
