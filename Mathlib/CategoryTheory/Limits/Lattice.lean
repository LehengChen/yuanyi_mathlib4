/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Justus Springer
-/
module

public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.Data.Finset.Lattice.Fold

/-!
# Limits in lattice categories are given by infimums and supremums.
-/

@[expose] public section


universe w w' u

namespace CategoryTheory.Limits.CompleteLattice

section Semilattice

variable {α : Type u} {J : Type w} [SmallCategory J] [FinCategory J]

/-- The limit cone over any functor from a finite diagram into a `SemilatticeInf` with `OrderTop`.
-/
@[simps]
def finiteLimitCone [SemilatticeInf α] [OrderTop α] (F : J ⥤ α) : LimitCone F where
  cone :=
    { pt := Finset.univ.inf F.obj
      π := { app := fun _ => homOfLE (Finset.inf_le (Fintype.complete _)) } }
  isLimit := { lift := fun s => homOfLE (Finset.le_inf fun j _ => (s.π.app j).down.down) }

/--
The colimit cocone over any functor from a finite diagram into a `SemilatticeSup` with `OrderBot`.
-/
@[simps]
def finiteColimitCocone [SemilatticeSup α] [OrderBot α] (F : J ⥤ α) : ColimitCocone F where
  cocone :=
    { pt := Finset.univ.sup F.obj
      ι := { app := fun _ => homOfLE (Finset.le_sup (Fintype.complete _)) } }
  isColimit := { desc := fun s => homOfLE (Finset.sup_le fun j _ => (s.ι.app j).down.down) }

-- see Note [lower instance priority]
instance (priority := 100) hasFiniteLimits_of_semilatticeInf_orderTop [SemilatticeInf α]
    [OrderTop α] : HasFiniteLimits α := ⟨by
  intro J 𝒥₁ 𝒥₂
  exact { has_limit := fun F => HasLimit.mk (finiteLimitCone F) }⟩

-- see Note [lower instance priority]
instance (priority := 100) hasFiniteColimits_of_semilatticeSup_orderBot [SemilatticeSup α]
    [OrderBot α] : HasFiniteColimits α := ⟨by
  intro J 𝒥₁ 𝒥₂
  exact { has_colimit := fun F => HasColimit.mk (finiteColimitCocone F) }⟩

/-- The limit of a functor from a finite diagram into a `SemilatticeInf` with `OrderTop` is the
infimum of the objects in the image.
-/
theorem finite_limit_eq_finset_univ_inf [SemilatticeInf α] [OrderTop α] (F : J ⥤ α) :
    limit F = Finset.univ.inf F.obj :=
  (IsLimit.conePointUniqueUpToIso (limit.isLimit F) (finiteLimitCone F).isLimit).to_eq

/-- The colimit of a functor from a finite diagram into a `SemilatticeSup` with `OrderBot`
is the supremum of the objects in the image.
-/
theorem finite_colimit_eq_finset_univ_sup [SemilatticeSup α] [OrderBot α] (F : J ⥤ α) :
    colimit F = Finset.univ.sup F.obj :=
  (IsColimit.coconePointUniqueUpToIso (colimit.isColimit F) (finiteColimitCocone F).isColimit).to_eq

/--
A finite product in the category of a `SemilatticeInf` with `OrderTop` is the same as the infimum.
-/
theorem finite_product_eq_finset_inf [SemilatticeInf α] [OrderTop α] {ι : Type u} [Fintype ι]
    (f : ι → α) : ∏ᶜ f = Fintype.elems.inf f := by
  trans
  · exact
      (IsLimit.conePointUniqueUpToIso (limit.isLimit _)
          (finiteLimitCone (Discrete.functor f)).isLimit).to_eq
  change Finset.univ.inf (f ∘ discreteEquiv.toEmbedding) = Fintype.elems.inf f
  simp only [← Finset.inf_map, Finset.univ_map_equiv_to_embedding]
  rfl

/-- A finite coproduct in the category of a `SemilatticeSup` with `OrderBot` is the same as the
supremum.
-/
theorem finite_coproduct_eq_finset_sup [SemilatticeSup α] [OrderBot α] {ι : Type u} [Fintype ι]
    (f : ι → α) : ∐ f = Fintype.elems.sup f := by
  trans
  · exact
      (IsColimit.coconePointUniqueUpToIso (colimit.isColimit _)
          (finiteColimitCocone (Discrete.functor f)).isColimit).to_eq
  change Finset.univ.sup (f ∘ discreteEquiv.toEmbedding) = Fintype.elems.sup f
  simp only [← Finset.sup_map, Finset.univ_map_equiv_to_embedding]
  rfl

-- see Note [lower instance priority]
instance (priority := 100) [SemilatticeInf α] : HasBinaryProducts α := by
  haveI : ∀ {x y : α}, HasLimit (pair x y) := by
    intro x y
    refine HasLimit.mk ?_
    let c : BinaryFan x y := BinaryFan.mk (homOfLE inf_le_left) (homOfLE inf_le_right)
    exact
      { cone := c
        isLimit :=
          BinaryFan.isLimitMk
            (fun s => homOfLE (le_inf s.fst.le s.snd.le))
            (fun s => by rfl)
            (fun s => by rfl)
            (fun s m hfst hsnd => by rfl) }
  exact hasBinaryProducts_of_hasLimit_pair α

/-- The binary product in the category of a `SemilatticeInf` is the same as the infimum.
-/
@[simp]
theorem prod_eq_inf [SemilatticeInf α] (x y : α) : Limits.prod x y = x ⊓ y := by
  let c : BinaryFan x y := BinaryFan.mk (homOfLE inf_le_left) (homOfLE inf_le_right)
  have hc : IsLimit c :=
    BinaryFan.isLimitMk
      (fun s => homOfLE (le_inf s.fst.le s.snd.le))
      (fun s => by rfl)
      (fun s => by rfl)
      (fun s m hfst hsnd => by rfl)
  exact (IsLimit.conePointUniqueUpToIso (limit.isLimit (pair x y)) hc).to_eq

-- see Note [lower instance priority]
instance (priority := 100) [SemilatticeSup α] : HasBinaryCoproducts α := by
  haveI : ∀ {x y : α}, HasColimit (pair x y) := by
    intro x y
    refine HasColimit.mk ?_
    let c : BinaryCofan x y := BinaryCofan.mk (homOfLE le_sup_left) (homOfLE le_sup_right)
    exact
      { cocone := c
        isColimit :=
          BinaryCofan.isColimitMk
            (fun s => homOfLE (sup_le s.inl.le s.inr.le))
            (fun s => by rfl)
            (fun s => by rfl)
            (fun s m hfst hsnd => by rfl) }
  exact hasBinaryCoproducts_of_hasColimit_pair α

/-- The binary coproduct in the category of a `SemilatticeSup` is the same as the supremum.
-/
@[simp]
theorem coprod_eq_sup [SemilatticeSup α] (x y : α) : Limits.coprod x y = x ⊔ y := by
  let c : BinaryCofan x y := BinaryCofan.mk (homOfLE le_sup_left) (homOfLE le_sup_right)
  have hc : IsColimit c :=
    BinaryCofan.isColimitMk
      (fun s => homOfLE (sup_le s.inl.le s.inr.le))
      (fun s => by rfl)
      (fun s => by rfl)
      (fun s m hfst hsnd => by rfl)
  exact (IsColimit.coconePointUniqueUpToIso (colimit.isColimit (pair x y)) hc).to_eq

-- see Note [lower instance priority]
instance (priority := 100) [SemilatticeInf α] : HasPullbacks α := by
  haveI : ∀ {x y z : α} {f : x ⟶ z} {g : y ⟶ z}, HasLimit (cospan f g) := by
    intro x y z f g
    refine HasLimit.mk ?_
    let c : PullbackCone f g :=
      PullbackCone.mk (homOfLE inf_le_left) (homOfLE inf_le_right) (by rfl)
    exact
      { cone := c
        isLimit :=
          PullbackCone.IsLimit.mk (by rfl)
            (fun s => homOfLE (le_inf s.fst.le s.snd.le))
            (fun s => by rfl)
            (fun s => by rfl)
            (fun s m hfst hsnd => by rfl) }
  exact hasPullbacks_of_hasLimit_cospan α

/-- The pullback in the category of a `SemilatticeInf` is the same as the infimum over the objects.
-/
@[simp]
theorem pullback_eq_inf [SemilatticeInf α] {x y z : α} (f : x ⟶ z) (g : y ⟶ z) :
    pullback f g = x ⊓ y := by
  let c : PullbackCone f g :=
    PullbackCone.mk (homOfLE inf_le_left) (homOfLE inf_le_right) (by rfl)
  have hc : IsLimit c :=
    PullbackCone.IsLimit.mk (by rfl)
      (fun s => homOfLE (le_inf s.fst.le s.snd.le))
      (fun s => by rfl)
      (fun s => by rfl)
      (fun s m hfst hsnd => by rfl)
  exact (IsLimit.conePointUniqueUpToIso (limit.isLimit (cospan f g)) hc).to_eq

-- see Note [lower instance priority]
instance (priority := 100) [SemilatticeSup α] : HasPushouts α := by
  haveI : ∀ {x y z : α} {f : x ⟶ y} {g : x ⟶ z}, HasColimit (span f g) := by
    intro x y z f g
    refine HasColimit.mk ?_
    let c : PushoutCocone f g :=
      PushoutCocone.mk (homOfLE le_sup_left) (homOfLE le_sup_right) (by rfl)
    exact
      { cocone := c
        isColimit :=
          PushoutCocone.IsColimit.mk (by rfl)
            (fun s => homOfLE (sup_le s.inl.le s.inr.le))
            (fun s => by rfl)
            (fun s => by rfl)
            (fun s m hfst hsnd => by rfl) }
  exact hasPushouts_of_hasColimit_span α

/-- The pushout in the category of a `SemilatticeSup` is the same as the supremum over the objects.
-/
@[simp]
theorem pushout_eq_sup [SemilatticeSup α] (x y z : α) (f : z ⟶ x) (g : z ⟶ y) :
    pushout f g = x ⊔ y := by
  let c : PushoutCocone f g :=
    PushoutCocone.mk (homOfLE le_sup_left) (homOfLE le_sup_right) (by rfl)
  have hc : IsColimit c :=
    PushoutCocone.IsColimit.mk (by rfl)
      (fun s => homOfLE (sup_le s.inl.le s.inr.le))
      (fun s => by rfl)
      (fun s => by rfl)
      (fun s m hfst hsnd => by rfl)
  exact (IsColimit.coconePointUniqueUpToIso (colimit.isColimit (span f g)) hc).to_eq

end Semilattice

variable {α : Type u} [CompleteLattice α] {J : Type w} [Category.{w'} J]

/-- The limit cone over any functor into a complete lattice.
-/
@[simps]
def limitCone (F : J ⥤ α) : LimitCone F where
  cone :=
    { pt := iInf F.obj
      π := { app := fun _ => homOfLE (sInf_le (Set.mem_range_self _)) } }
  isLimit :=
    { lift := fun s =>
        homOfLE (le_sInf (by rintro _ ⟨j, rfl⟩; exact (s.π.app j).le)) }

/-- The colimit cocone over any functor into a complete lattice.
-/
@[simps]
def colimitCocone (F : J ⥤ α) : ColimitCocone F where
  cocone :=
    { pt := iSup F.obj
      ι := { app := fun _ => homOfLE (le_sSup (Set.mem_range_self _)) } }
  isColimit :=
    { desc := fun s =>
        homOfLE (sSup_le (by rintro _ ⟨j, rfl⟩; exact (s.ι.app j).le)) }

-- see Note [lower instance priority]
instance (priority := 100) hasLimits_of_completeLattice : HasLimitsOfSize.{w, w'} α where
  has_limits_of_shape _ := { has_limit := fun F => HasLimit.mk (limitCone F) }

-- see Note [lower instance priority]
instance (priority := 100) hasColimits_of_completeLattice : HasColimitsOfSize.{w, w'} α where
  has_colimits_of_shape _ := { has_colimit := fun F => HasColimit.mk (colimitCocone F) }

section CompleteSemilattice

variable {β : Type u} {K : Type w} [Category.{w'} K]

/-- The limit of a functor into a complete inf-semilattice is the infimum of the objects in the
image.
-/
theorem limit_eq_iInf [CompleteSemilatticeInf β] (F : K ⥤ β) [HasLimit F] :
    limit F = iInf F.obj := by
  let c : Cone F :=
    { pt := iInf F.obj
      π := { app := fun _ => homOfLE (sInf_le (Set.mem_range_self _)) } }
  have hc : IsLimit c :=
    { lift := fun s =>
        homOfLE (le_sInf (by rintro _ ⟨j, rfl⟩; exact (s.π.app j).le)) }
  exact (IsLimit.conePointUniqueUpToIso (limit.isLimit F) hc).to_eq

/-- The colimit of a functor into a complete sup-semilattice is the supremum of the objects in the
image.
-/
theorem colimit_eq_iSup [CompleteSemilatticeSup β] (F : K ⥤ β) [HasColimit F] :
    colimit F = iSup F.obj := by
  let c : Cocone F :=
    { pt := iSup F.obj
      ι := { app := fun _ => homOfLE (le_sSup (Set.mem_range_self _)) } }
  have hc : IsColimit c :=
    { desc := fun s =>
        homOfLE (sSup_le (by rintro _ ⟨j, rfl⟩; exact (s.ι.app j).le)) }
  exact (IsColimit.coconePointUniqueUpToIso (colimit.isColimit F) hc).to_eq

end CompleteSemilattice

end CategoryTheory.Limits.CompleteLattice
