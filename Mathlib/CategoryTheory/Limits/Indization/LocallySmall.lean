/-
Copyright (c) 2024 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Ulift
public import Mathlib.CategoryTheory.Limits.IndYoneda
public import Mathlib.CategoryTheory.Limits.Indization.IndObject

/-!
# There are only `v`-many natural transformations between Ind-objects

We provide the instance `LocallySmall.{v} (FullSubcategory (IsIndObject (C := C)))`, which will
serve as the basis for our definition of the category of Ind-objects.

## Future work

The equivalence established here serves as the basis for a well-known calculation of hom-sets of
ind-objects as a limit of a colimit.
-/

@[expose] public section

open CategoryTheory Limits Opposite

universe v v₁ u u₁

variable {C : Type u} [Category.{v} C]

namespace CategoryTheory

section

variable {I : Type u₁} [Category.{v₁} I]
variable (F : I ⥤ C) (G : Cᵒᵖ ⥤ Type v)

/-- Variant of `colimitYonedaHomIsoLimitOp`: natural transformations with domain
`colimit (F ⋙ yoneda)` are equivalent to a limit in a lower universe. -/
noncomputable def colimitYonedaHomEquiv [HasColimit (F ⋙ yoneda)] [HasLimit (F.op ⋙ G)] :
    (colimit (F ⋙ yoneda) ⟶ G) ≃ limit (F.op ⋙ G) :=
  let e : ((F ⋙ yoneda) ⟶ (Functor.const I).obj G) ≃ (F.op ⋙ G).sections :=
    { toFun := fun α =>
        ⟨fun i => yonedaEquiv (α.app i.unop), fun {i j} f => by
          rw [show (F.op ⋙ G).map f = G.map (F.map f.unop).op by rfl]
          rw [yonedaEquiv_naturality]
          congr 1
          simpa using α.naturality f.unop⟩
      invFun := fun s =>
        { app := fun i => yonedaEquiv.symm (s.val (op i))
          naturality := fun i j f => by
            exact (yonedaEquiv_symm_naturality_left (F.map f) G (s.val (op j))).trans (by
              change yonedaEquiv.symm ((F.op ⋙ G).map f.op (s.val (op j))) =
                yonedaEquiv.symm (s.val (op i)) ≫ ((Functor.const I).obj G).map f
              rw [s.property f.op]
              simp) }
      left_inv := fun α => by
        apply NatTrans.ext
        funext i
        exact Equiv.symm_apply_apply yonedaEquiv (α.app i)
      right_inv := fun s => by
        ext i
        exact Equiv.apply_symm_apply yonedaEquiv (s.val i) }
  (colimit.isColimit (F ⋙ yoneda)).homEquiv.trans <| e.trans (Types.limitEquivSections _).symm

@[simp]
theorem colimitYonedaHomEquiv_π_apply [HasColimit (F ⋙ yoneda)] [HasLimit (F.op ⋙ G)]
    (η : colimit (F ⋙ yoneda) ⟶ G) (i : Iᵒᵖ) :
    limit.π (F.op ⋙ G) i (colimitYonedaHomEquiv F G η) =
      η.app (op (F.obj i.unop)) ((colimit.ι (F ⋙ yoneda) i.unop).app _ (𝟙 _)) := by
  change limit.π (F.op ⋙ G) i ((Types.limitEquivSections (F.op ⋙ G)).symm
    ⟨fun i => yonedaEquiv (((colimit.isColimit (F ⋙ yoneda)).homEquiv η).app i.unop), _⟩) = _
  rw [Types.limitEquivSections_symm_apply]
  change yonedaEquiv (((colimit.isColimit (F ⋙ yoneda)).homEquiv η).app i.unop) =
    η.app (op (F.obj i.unop)) ((colimit.ι (F ⋙ yoneda) i.unop).app _ (𝟙 _))
  rw [IsColimit.homEquiv_apply]
  rfl

instance [HasColimit (F ⋙ yoneda)] [HasLimit (F.op ⋙ G)] :
    Small.{v} (colimit (F ⋙ yoneda) ⟶ G) where
  equiv_small := ⟨_, ⟨colimitYonedaHomEquiv F G⟩⟩

end

instance : LocallySmall.{v} (ObjectProperty.FullSubcategory (IsIndObject (C := C))) where
  hom_small X Y := by
    obtain ⟨⟨P⟩⟩ := X.2
    obtain ⟨⟨Q⟩⟩ := Y.2
    let e₁ := IsColimit.coconePointUniqueUpToIso (P.isColimit) (colimit.isColimit _)
    let e₂ := IsColimit.coconePointUniqueUpToIso (Q.isColimit) (colimit.isColimit _)
    let e₃ := Iso.homCongr e₁ e₂
    dsimp only [colimit.cocone_x] at e₃
    exact small_map (InducedCategory.homEquiv.trans e₃)

end CategoryTheory
