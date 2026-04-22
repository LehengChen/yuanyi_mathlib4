/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.IsLimit
public import Mathlib.CategoryTheory.Limits.Shapes.Preorder.PrincipalSeg
public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.Data.Nat.SuccPred
public import Mathlib.Data.Fin.SuccPredOrder
public import Mathlib.Order.Interval.Set.InitialSeg
public import Mathlib.Order.Interval.Set.Limit
public import Mathlib.Order.SuccPred.InitialSeg
public import Mathlib.Order.SuccPred.Limit
public import Mathlib.Order.SuccPred.LinearLocallyFinite

/-!
# Continuity of functors from well-ordered types

Let `F : J ⥤ C` be a functor from a well-ordered type `J`.
We introduce the typeclass `F.IsWellOrderContinuous`
to say that if `m` is a limit element, then `F.obj m`
is the colimit of the `F.obj j` for `j < m`.

-/

@[expose] public section

universe w w' v u

namespace CategoryTheory.Functor

open Category Limits

variable {C : Type u} [Category.{v} C] {J : Type w} [PartialOrder J]

/-- A functor `F : J ⥤ C` is well-order-continuous if for any limit element `m : J`,
`F.obj m` identifies to the colimit of the `F.obj j` for `j < m`. -/
class IsWellOrderContinuous (F : J ⥤ C) : Prop where
  nonempty_isColimit (m : J) (hm : Order.IsSuccLimit m) :
    Nonempty (IsColimit ((Set.principalSegIio m).cocone F))

/-- If `F : J ⥤ C` is well-order-continuous and `m : J` is a limit element, then
`F.obj m` identifies to the colimit of the `F.obj j` for `j < m`. -/
noncomputable def isColimitOfIsWellOrderContinuous (F : J ⥤ C) [F.IsWellOrderContinuous]
    (m : J) (hm : Order.IsSuccLimit m) :
    IsColimit ((Set.principalSegIio m).cocone F) :=
      (IsWellOrderContinuous.nonempty_isColimit m hm).some

/-- If `F : J ⥤ C` is well-order-continuous and `h : α <i J` is a principal
segment such that `h.top` is a limit element, then
`F.obj h.top` identifies to the colimit of the `F.obj j` for `j : α`. -/
noncomputable def isColimitOfIsWellOrderContinuous' (F : J ⥤ C) [F.IsWellOrderContinuous]
    {α : Type*} [PartialOrder α] (f : α <i J) (hα : Order.IsSuccLimit f.top) :
    IsColimit (f.cocone F) :=
  (F.isColimitOfIsWellOrderContinuous f.top hα).whiskerEquivalence
    f.orderIsoIio.equivalence

instance (F : ℕ ⥤ C) : F.IsWellOrderContinuous where
  nonempty_isColimit m hm := by simp at hm

instance {n : ℕ} (F : Fin n ⥤ C) : F.IsWellOrderContinuous where
  nonempty_isColimit _ hj := (Order.not_isSuccLimit hj).elim

lemma isWellOrderContinuous_of_iso {F G : J ⥤ C} (e : F ≅ G) [F.IsWellOrderContinuous] :
    G.IsWellOrderContinuous where
  nonempty_isColimit (m : J) (hm : Order.IsSuccLimit m) :=
    ⟨(IsColimit.precomposeHomEquiv (isoWhiskerLeft _ e) _).1
      (IsColimit.ofIsoColimit (F.isColimitOfIsWellOrderContinuous m hm)
        (Cocone.ext (e.app _)))⟩

instance (F : J ⥤ C) {J' : Type w'} [PartialOrder J'] (f : J' ≤i J)
    [F.IsWellOrderContinuous] :
    (f.monotone.functor ⋙ F).IsWellOrderContinuous where
  nonempty_isColimit m' hm' := ⟨F.isColimitOfIsWellOrderContinuous'
    ((Set.principalSegIio m').transInitial f) (by simpa)⟩

instance (F : J ⥤ C) {J' : Type w'} [PartialOrder J'] (e : J' ≃o J)
    [F.IsWellOrderContinuous] :
    (e.equivalence.functor ⋙ F).IsWellOrderContinuous :=
  inferInstanceAs (e.toInitialSeg.monotone.functor ⋙ F).IsWellOrderContinuous

instance IsWellOrderContinuous.restriction_setIci
    {J : Type w} [PartialOrder J] [Std.Total (α := J) (· ≤ ·)]
    {F : J ⥤ C} [F.IsWellOrderContinuous] (j : J) :
    ((Subtype.mono_coe (· ∈ Set.Ici j)).functor ⋙ F).IsWellOrderContinuous where
  nonempty_isColimit m hm := ⟨by
    let f : Set.Iio m → Set.Iio m.1 := fun ⟨⟨a, ha⟩, ha'⟩ ↦ ⟨a, ha'⟩
    have hf : Monotone f := fun _ _ h ↦ h
    have : hf.functor.Final := by
      rw [Monotone.final_functor_iff]
      rintro ⟨j', hj'⟩
      push _ ∈ _ at hj'
      dsimp only [f]
      by_cases h : j' ≤ j
      · refine ⟨⟨⟨j, le_refl j⟩, ?_⟩, h⟩
        exact lt_iff_le_not_ge.2 ⟨m.2, fun hmj ↦ hm.1 (by
          rintro ⟨k, hk⟩ _
          exact (show m.1 ≤ j by simpa using hmj).trans hk)⟩
      · have hj_le : j ≤ j' := (total_of (· ≤ ·) j' j).resolve_left h
        exact ⟨⟨⟨j', hj_le⟩, hj'⟩, by rfl⟩
    exact (Functor.Final.isColimitWhiskerEquiv (F := hf.functor) _).2
      (F.isColimitOfIsWellOrderContinuous m.1
        ⟨Set.not_isMin_coe _ hm.1, fun b hb ↦ by
          by_cases hb' : j ≤ b
          · exact hm.2 ⟨b, hb'⟩ ⟨by simpa using hb.1, fun {c} h₁ h₂ ↦
              hb.2 (by simpa using h₁) (by simpa using h₂)⟩
          · apply hb.2
            · exact lt_iff_le_not_ge.2 ⟨(total_of (· ≤ ·) j b).resolve_left hb', hb'⟩
            · exact lt_iff_le_not_ge.2 ⟨m.2, fun hmj ↦ hm.1 (by
                rintro ⟨k, hk⟩ _
                exact hmj.trans hk)⟩⟩)⟩

end CategoryTheory.Functor
