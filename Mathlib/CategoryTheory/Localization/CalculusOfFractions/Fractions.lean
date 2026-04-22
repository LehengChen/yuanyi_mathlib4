/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Localization.CalculusOfFractions

/-!
# Lemmas on fractions

Let `W : MorphismProperty C`, and objects `X` and `Y` in `C`. In this file,
we introduce structures like `W.LeftFraction₂ X Y` which consists of two
left fractions with the "same denominator" which shall be important in
the construction of the preadditive structure on the localized category
when `C` is preadditive and `W` has a left calculus of fractions.

When `W` has a left calculus of fractions, we generalize the lemmas
`RightFraction.exists_leftFraction` as `RightFraction₂.exists_leftFraction₂`,
`Localization.exists_leftFraction` as `Localization.exists_leftFraction₂` and
`Localization.exists_leftFraction₃`, and
`LeftFraction.map_eq_iff` as `LeftFraction₂.map_eq_iff`.

## Implementation note

The lemmas in this file are phrased with data that is bundled into structures like
`LeftFraction₂` or `LeftFraction₃`. It could have been possible to phrase them
with "unbundled data". However, this would require introducing 4 or 5 variables instead
of one. It is also very convenient to use dot notation.
Many definitions have been made reducible so as to ease rewrites when this API is used.

-/

@[expose] public section

namespace CategoryTheory

variable {C D : Type*} [Category* C] [Category* D] (L : C ⥤ D) (W : MorphismProperty C)
  [L.IsLocalization W]

namespace MorphismProperty

/-- This structure contains the data of two left fractions for
`W : MorphismProperty C` that have the same "denominator". -/
structure LeftFraction₂ (X Y : C) where
  /-- the auxiliary object of left fractions -/
  {Y' : C}
  /-- the numerator of the first left fraction -/
  f : X ⟶ Y'
  /-- the numerator of the second left fraction -/
  f' : X ⟶ Y'
  /-- the denominator of the left fractions -/
  s : Y ⟶ Y'
  /-- the condition that the denominator belongs to the given morphism property -/
  hs : W s

/-- This structure contains the data of three left fractions for
`W : MorphismProperty C` that have the same "denominator". -/
structure LeftFraction₃ (X Y : C) where
  /-- the auxiliary object of left fractions -/
  {Y' : C}
  /-- the numerator of the first left fraction -/
  f : X ⟶ Y'
  /-- the numerator of the second left fraction -/
  f' : X ⟶ Y'
  /-- the numerator of the third left fraction -/
  f'' : X ⟶ Y'
  /-- the denominator of the left fractions -/
  s : Y ⟶ Y'
  /-- the condition that the denominator belongs to the given morphism property -/
  hs : W s

/-- This structure contains the data of two right fractions for
`W : MorphismProperty C` that have the same "denominator". -/
structure RightFraction₂ (X Y : C) where
  /-- the auxiliary object of right fractions -/
  {X' : C}
  /-- the denominator of the right fractions -/
  s : X' ⟶ X
  /-- the condition that the denominator belongs to the given morphism property -/
  hs : W s
  /-- the numerator of the first right fraction -/
  f : X' ⟶ Y
  /-- the numerator of the second right fraction -/
  f' : X' ⟶ Y

variable {W}

/-- The equivalence relation on tuples of left fractions with the same denominator
for a morphism property `W`. The fact it is an equivalence relation is not
formalized, but it would follow easily from `LeftFraction₂.map_eq_iff`. -/
def LeftFraction₂Rel {X Y : C} (z₁ z₂ : W.LeftFraction₂ X Y) : Prop :=
  ∃ (Z : C) (t₁ : z₁.Y' ⟶ Z) (t₂ : z₂.Y' ⟶ Z) (_ : z₁.s ≫ t₁ = z₂.s ≫ t₂)
    (_ : z₁.f ≫ t₁ = z₂.f ≫ t₂) (_ : z₁.f' ≫ t₁ = z₂.f' ≫ t₂), W (z₁.s ≫ t₁)

namespace LeftFraction₂

variable {X Y : C} (φ : W.LeftFraction₂ X Y)

/-- The first left fraction. -/
abbrev fst : W.LeftFraction X Y where
  Y' := φ.Y'
  f := φ.f
  s := φ.s
  hs := φ.hs

/-- The second left fraction. -/
abbrev snd : W.LeftFraction X Y where
  Y' := φ.Y'
  f := φ.f'
  s := φ.s
  hs := φ.hs

/-- The exchange of the two fractions. -/
abbrev symm : W.LeftFraction₂ X Y where
  Y' := φ.Y'
  f := φ.f'
  f' := φ.f
  s := φ.s
  hs := φ.hs

end LeftFraction₂

namespace LeftFraction₃

variable {X Y : C} (φ : W.LeftFraction₃ X Y)

/-- The first left fraction. -/
abbrev fst : W.LeftFraction X Y where
  Y' := φ.Y'
  f := φ.f
  s := φ.s
  hs := φ.hs

/-- The second left fraction. -/
abbrev snd : W.LeftFraction X Y where
  Y' := φ.Y'
  f := φ.f'
  s := φ.s
  hs := φ.hs

/-- The third left fraction. -/
abbrev thd : W.LeftFraction X Y where
  Y' := φ.Y'
  f := φ.f''
  s := φ.s
  hs := φ.hs

/-- Forgets the first fraction. -/
abbrev forgetFst : W.LeftFraction₂ X Y where
  Y' := φ.Y'
  f := φ.f'
  f' := φ.f''
  s := φ.s
  hs := φ.hs

/-- Forgets the second fraction. -/
abbrev forgetSnd : W.LeftFraction₂ X Y where
  Y' := φ.Y'
  f := φ.f
  f' := φ.f''
  s := φ.s
  hs := φ.hs

/-- Forgets the third fraction. -/
abbrev forgetThd : W.LeftFraction₂ X Y where
  Y' := φ.Y'
  f := φ.f
  f' := φ.f'
  s := φ.s
  hs := φ.hs

end LeftFraction₃

namespace LeftFraction₂Rel

variable {X Y : C} {z₁ z₂ : W.LeftFraction₂ X Y}

lemma fst (h : LeftFraction₂Rel z₁ z₂) : LeftFractionRel z₁.fst z₂.fst := by
  obtain ⟨Z, t₁, t₂, hst, hft, _, ht⟩ := h
  exact ⟨Z, t₁, t₂, hst, hft, ht⟩

lemma snd (h : LeftFraction₂Rel z₁ z₂) : LeftFractionRel z₁.snd z₂.snd := by
  obtain ⟨Z, t₁, t₂, hst, _, hft', ht⟩ := h
  exact ⟨Z, t₁, t₂, hst, hft', ht⟩

end LeftFraction₂Rel

namespace LeftFraction₂

variable (W)
variable [W.HasLeftCalculusOfFractions]

lemma map_eq_iff {X Y : C} (φ ψ : W.LeftFraction₂ X Y) :
    (φ.fst.map L (Localization.inverts _ _) = ψ.fst.map L (Localization.inverts _ _) ∧
    φ.snd.map L (Localization.inverts _ _) = ψ.snd.map L (Localization.inverts _ _)) ↔
      LeftFraction₂Rel φ ψ := by
  constructor
  · intro ⟨h, h'⟩
    obtain ⟨Z, t₁, t₂, hst, hft, ht⟩ := (LeftFraction.map_eq_iff L W _ _).1 h
    have hmap : L.map (φ.f' ≫ t₁) = L.map (ψ.f' ≫ t₂) := by
      have hmap₀ := congrArg (fun f => f ≫ L.map (φ.s ≫ t₁)) h'
      nth_rewrite 2 [hst] at hmap₀
      dsimp at hmap₀
      rw [L.map_comp, L.map_comp] at hmap₀
      rw [LeftFraction.map_comp_map_s_assoc, LeftFraction.map_comp_map_s_assoc] at hmap₀
      simpa [Functor.map_comp] using hmap₀
    obtain ⟨Z', u, hu, hfu⟩ := (MorphismProperty.map_eq_iff_postcomp L W
      (φ.f' ≫ t₁) (ψ.f' ≫ t₂)).1 hmap
    exact ⟨Z', t₁ ≫ u, t₂ ≫ u, by rw [← Category.assoc, hst, Category.assoc],
      by rw [← Category.assoc, hft, Category.assoc], by simpa only [Category.assoc] using hfu,
      by rw [← Category.assoc]; exact W.comp_mem _ _ ht hu⟩
  · intro h
    exact ⟨(LeftFraction.map_eq_iff L W _ _).2 h.fst, (LeftFraction.map_eq_iff L W _ _).2 h.snd⟩

end LeftFraction₂

namespace RightFraction₂

variable {X Y : C}
variable (φ : W.RightFraction₂ X Y)

/-- The first right fraction. -/
abbrev fst : W.RightFraction X Y where
  X' := φ.X'
  f := φ.f
  s := φ.s
  hs := φ.hs

/-- The second right fraction. -/
abbrev snd : W.RightFraction X Y where
  X' := φ.X'
  f := φ.f'
  s := φ.s
  hs := φ.hs

lemma exists_leftFraction₂ [W.HasLeftCalculusOfFractions] :
    ∃ (ψ : W.LeftFraction₂ X Y), φ.f ≫ ψ.s = φ.s ≫ ψ.f ∧
      φ.f' ≫ ψ.s = φ.s ≫ ψ.f' := by
  obtain ⟨ψ₁, hψ₁⟩ := φ.fst.exists_leftFraction
  obtain ⟨ψ₂, hψ₂⟩ := φ.snd.exists_leftFraction
  obtain ⟨α, hα⟩ := (RightFraction.mk _ ψ₁.hs ψ₂.s).exists_leftFraction
  dsimp at hψ₁ hψ₂ hα
  refine ⟨LeftFraction₂.mk (ψ₁.f ≫ α.f) (ψ₂.f ≫ α.s) (ψ₂.s ≫ α.s)
      (W.comp_mem _ _ ψ₂.hs α.hs), ?_, ?_⟩
  · dsimp
    rw [hα, reassoc_of% hψ₁]
  · rw [reassoc_of% hψ₂]

end RightFraction₂

end MorphismProperty

namespace Localization

variable [W.HasLeftCalculusOfFractions]

open MorphismProperty

lemma exists_leftFraction₂ {X Y : C} (f f' : L.obj X ⟶ L.obj Y) :
    ∃ (φ : W.LeftFraction₂ X Y), f = φ.fst.map L (inverts L W) ∧
      f' = φ.snd.map L (inverts L W) := by
  have ⟨φ, hφ⟩ := exists_leftFraction L W f
  have ⟨φ', hφ'⟩ := exists_leftFraction L W f'
  obtain ⟨α, hα⟩ := (RightFraction.mk _ φ.hs φ'.s).exists_leftFraction
  dsimp at hα
  let ψ : W.LeftFraction₂ X Y :=
    { Y' := α.Y'
      f := φ.f ≫ α.f
      f' := φ'.f ≫ α.s
      s := φ'.s ≫ α.s
      hs := W.comp_mem _ _ φ'.hs α.hs }
  refine ⟨ψ, ?_, ?_⟩
  · rw [hφ, LeftFraction.map_eq_iff L W]
    exact ⟨_, α.f, 𝟙 _, by simpa [ψ] using hα.symm, by simp [ψ],
      by simpa [ψ, hα] using ψ.hs⟩
  · rw [hφ', LeftFraction.map_eq_iff L W]
    exact ⟨_, α.s, 𝟙 _, by simp [ψ], by simp [ψ], by simpa [ψ] using ψ.hs⟩

lemma exists_leftFraction₃ {X Y : C} (f f' f'' : L.obj X ⟶ L.obj Y) :
    ∃ (φ : W.LeftFraction₃ X Y), f = φ.fst.map L (inverts L W) ∧
      f' = φ.snd.map L (inverts L W) ∧
      f'' = φ.thd.map L (inverts L W) := by
  obtain ⟨α, hα, hα'⟩ := exists_leftFraction₂ L W f f'
  have ⟨β, hβ⟩ := exists_leftFraction L W f''
  obtain ⟨γ, hγ⟩ := (RightFraction.mk _ α.hs β.s).exists_leftFraction
  dsimp at hγ
  let ψ : W.LeftFraction₃ X Y :=
    { Y' := γ.Y'
      f := α.f ≫ γ.f
      f' := α.f' ≫ γ.f
      f'' := β.f ≫ γ.s
      s := β.s ≫ γ.s
      hs := W.comp_mem _ _ β.hs γ.hs }
  refine ⟨ψ, ?_, ?_, ?_⟩
  · rw [hα, LeftFraction.map_eq_iff L W]
    exact ⟨_, γ.f, 𝟙 _, by simpa [ψ] using hγ.symm, by simp [ψ],
      by simpa [ψ, hγ] using ψ.hs⟩
  · rw [hα', LeftFraction.map_eq_iff L W]
    exact ⟨_, γ.f, 𝟙 _, by simpa [ψ] using hγ.symm, by simp [ψ],
      by simpa [ψ, hγ] using ψ.hs⟩
  · rw [hβ, LeftFraction.map_eq_iff L W]
    exact ⟨_, γ.s, 𝟙 _, by simp [ψ], by simp [ψ], by simpa [ψ] using ψ.hs⟩

end Localization

end CategoryTheory
