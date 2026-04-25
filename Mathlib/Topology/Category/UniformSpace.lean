/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Patrick Massot, Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Adjunction.Reflective
public import Mathlib.CategoryTheory.Monad.Limits  -- shake: keep (used in `example` only)
public import Mathlib.Topology.Category.TopCat.Basic
public import Mathlib.Topology.UniformSpace.Completion

/-!
# The category of uniform spaces

We construct the category of uniform spaces, show that the complete separated uniform spaces
form a reflective subcategory, and hence possess all limits that uniform spaces do.

TODO: show that uniform spaces actually have all limits!
-/

@[expose] public section


universe u

open CategoryTheory


/-- An object in the category of uniform spaces. -/
structure UniformSpaceCat : Type (u + 1) where
  /-- Construct a bundled `UniformSpace` from the underlying type and the typeclass. -/
  of ::
  /-- The underlying uniform space. -/
  carrier : Type u
  [str : UniformSpace carrier]

attribute [instance] UniformSpaceCat.str

namespace UniformSpaceCat

instance : CoeSort UniformSpaceCat Type* :=
  ⟨carrier⟩

/-- A bundled uniform continuous map. -/
@[ext]
structure Hom (X Y : UniformSpaceCat) where
  /-- The underlying `UniformContinuous` function. -/
  hom' : { f : X → Y // UniformContinuous f }

instance : LargeCategory.{u} UniformSpaceCat.{u} where
  Hom := Hom
  id X := ⟨id, uniformContinuous_id⟩
  comp f g := ⟨⟨g.hom'.val ∘ f.hom'.val, g.hom'.property.comp f.hom'.property⟩⟩
  id_comp := by intros; apply Hom.ext; simp
  comp_id := by intros; apply Hom.ext; simp
  assoc := by intros; apply Hom.ext; ext; simp

instance instFunLike (X Y : UniformSpaceCat) :
    FunLike { f : X → Y // UniformContinuous f } X Y where
  coe := Subtype.val
  coe_injective' _ _ h := Subtype.ext h

instance : ConcreteCategory UniformSpaceCat ({ f : · → · // UniformContinuous f }) where
  hom f := f.hom'
  ofHom f := ⟨f⟩

/-- Turn a morphism in `UniformSpaceCat` back into a function which is `UniformContinuous`. -/
abbrev Hom.hom {X Y : UniformSpaceCat} (f : Hom X Y) :=
  ConcreteCategory.hom (C := UniformSpaceCat) f

/-- Typecheck a function which is `UniformContinuous` as a morphism in `UniformSpaceCat`. -/
abbrev ofHom {X Y : Type u} [UniformSpace X] [UniformSpace Y]
    (f : { f : X → Y // UniformContinuous f }) : of X ⟶ of Y :=
  ConcreteCategory.ofHom f

instance : Inhabited UniformSpaceCat :=
  ⟨UniformSpaceCat.of Empty⟩

theorem coe_of (X : Type u) [UniformSpace X] : (of X : Type u) = X :=
  rfl

@[simp]
theorem hom_comp {X Y Z : UniformSpaceCat} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom = ⟨g ∘ f, g.hom.prop.comp f.hom.prop⟩ :=
  rfl

@[simp]
theorem hom_id (X : UniformSpaceCat) : (𝟙 X : X ⟶ X).hom = ⟨id, uniformContinuous_id⟩ :=
  rfl

@[simp]
theorem hom_ofHom {X Y : Type u} [UniformSpace X] [UniformSpace Y]
    (f : { f : X → Y // UniformContinuous f }) : (ofHom f).hom = f :=
  rfl

theorem coe_comp {X Y Z : UniformSpaceCat} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g : X → Z) = g ∘ f :=
  rfl

@[simp] theorem hom_toFun {X Y : UniformSpaceCat} (f : X ⟶ Y) :
    ⇑(ConcreteCategory.hom f) = (ConcreteCategory.hom f).1 := rfl

theorem coe_id (X : UniformSpaceCat) : (𝟙 X : X → X) = id :=
  rfl

theorem coe_mk {X Y : UniformSpaceCat} (f : X → Y) (hf : UniformContinuous f) :
    (⟨f, hf⟩ : X ⟶ Y).hom = f :=
  rfl

@[ext]
theorem hom_ext {X Y : UniformSpaceCat} {f g : X ⟶ Y} (h : (f : X → Y) = g) : f = g :=
  Hom.ext (Subtype.ext h)

/-- The forgetful functor from uniform spaces to topological spaces. -/
instance hasForgetToTop : HasForget₂ UniformSpaceCat.{u} TopCat.{u} where
  forget₂ :=
    { obj := fun X => TopCat.of X
      map := fun f => TopCat.ofHom
        { toFun := f
          continuous_toFun := f.hom.property.continuous } }

end UniformSpaceCat

/-- A (bundled) complete separated uniform space. -/
structure CpltSepUniformSpace where
  /-- The underlying space -/
  α : Type u
  [isUniformSpace : UniformSpace α]
  [isCompleteSpace : CompleteSpace α]
  [isT0 : T0Space α]

namespace CpltSepUniformSpace

instance : CoeSort CpltSepUniformSpace (Type u) :=
  ⟨CpltSepUniformSpace.α⟩

attribute [instance] isUniformSpace isCompleteSpace isT0

/-- The function forgetting that a complete separated uniform spaces is complete and separated. -/
def toUniformSpace (X : CpltSepUniformSpace) : UniformSpaceCat :=
  UniformSpaceCat.of X

instance completeSpace (X : CpltSepUniformSpace) : CompleteSpace (toUniformSpace X).carrier :=
  CpltSepUniformSpace.isCompleteSpace X

instance t0Space (X : CpltSepUniformSpace) : T0Space (toUniformSpace X).carrier :=
  CpltSepUniformSpace.isT0 X

/-- Construct a bundled `UniformSpace` from the underlying type and the appropriate typeclasses. -/
def of (X : Type u) [UniformSpace X] [CompleteSpace X] [T0Space X] : CpltSepUniformSpace :=
  ⟨X⟩

@[simp]
theorem coe_of (X : Type u) [UniformSpace X] [CompleteSpace X] [T0Space X] :
    (of X : Type u) = X :=
  rfl

instance : Inhabited CpltSepUniformSpace :=
  ⟨CpltSepUniformSpace.of Empty⟩

/-- The category instance on `CpltSepUniformSpace`. -/
instance category : LargeCategory CpltSepUniformSpace :=
  inferInstanceAs <| Category (InducedCategory _ toUniformSpace)

instance instFunLike (X Y : CpltSepUniformSpace) :
    FunLike { f : X → Y // UniformContinuous f } X Y where
  coe := Subtype.val
  coe_injective' _ _ h := Subtype.ext h

/-- The concrete category instance on `CpltSepUniformSpace`. -/
instance concreteCategory : ConcreteCategory CpltSepUniformSpace
    ({ f : · → · // UniformContinuous f }) :=
  inferInstanceAs <| ConcreteCategory (InducedCategory _ toUniformSpace) _

instance hasForgetToUniformSpace : HasForget₂ CpltSepUniformSpace UniformSpaceCat :=
  inferInstanceAs <| HasForget₂ (InducedCategory _ toUniformSpace) _

@[simp]
theorem hom_comp {X Y Z : CpltSepUniformSpace} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ConcreteCategory.hom (f ≫ g) = ⟨g ∘ f, g.hom.hom.prop.comp f.hom.hom.prop⟩ :=
  rfl

@[simp] theorem hom_toFun {X Y : CpltSepUniformSpace} (f : X ⟶ Y) :
    ⇑(ConcreteCategory.hom f) = (ConcreteCategory.hom f).1 := rfl

@[simp]
theorem hom_id (X : CpltSepUniformSpace) :
    ConcreteCategory.hom (𝟙 X : X ⟶ X) = ⟨id, uniformContinuous_id⟩ :=
  rfl

@[simp]
theorem hom_ofHom {X Y : Type u} [UniformSpace X] [UniformSpace Y]
    (f : { f : X → Y // UniformContinuous f }) : (UniformSpaceCat.ofHom f).hom = f :=
  rfl

end CpltSepUniformSpace

namespace UniformSpaceCat

open UniformSpace

open CpltSepUniformSpace

/-- The functor turning uniform spaces into complete separated uniform spaces. -/
@[simps map]
noncomputable def completionFunctor : UniformSpaceCat ⥤ CpltSepUniformSpace where
  obj X := CpltSepUniformSpace.of (Completion X)
  map f := ConcreteCategory.ofHom ⟨Completion.map f.1, Completion.uniformContinuous_map⟩
  map_id _ := InducedCategory.hom_ext (hom_ext (by apply Completion.map_id))
  map_comp f g := InducedCategory.hom_ext (hom_ext (by
    exact (Completion.map_comp g.hom.property f.hom.property).symm))

/-- The inclusion of a uniform space into its completion. -/
noncomputable def completionHom (X : UniformSpaceCat) :
    X ⟶ (forget₂ CpltSepUniformSpace UniformSpaceCat).obj (completionFunctor.obj X) where
  hom'.val := ((↑) : X → Completion X)
  hom'.property := Completion.uniformContinuous_coe X

@[simp]
theorem completionHom_val (X : UniformSpaceCat) (x) : (completionHom X) x = (x : Completion X) :=
  rfl

/-- The mate of a morphism from a `UniformSpace` to a `CpltSepUniformSpace`. -/
noncomputable def extensionHom {X : UniformSpaceCat} {Y : CpltSepUniformSpace}
    (f : X ⟶ (forget₂ CpltSepUniformSpace UniformSpaceCat).obj Y) :
    completionFunctor.obj X ⟶ Y :=
  ConcreteCategory.ofHom ⟨Completion.extension f, Completion.uniformContinuous_extension⟩

@[simp]
theorem extensionHom_val {X : UniformSpaceCat} {Y : CpltSepUniformSpace}
    (f : X ⟶ (forget₂ _ _).obj Y) (x) : (extensionHom f) x = Completion.extension f x :=
  rfl

@[simp] theorem extensionHom_hom_apply {X : UniformSpaceCat} {Y : CpltSepUniformSpace}
    (f : X ⟶ (forget₂ _ _).obj Y) (x : completionFunctor.obj X) :
    (ConcreteCategory.hom (extensionHom f)).1 x = Completion.extension f.hom.1 x := rfl

@[simp]
theorem extension_comp_hom {X : UniformSpaceCat} {Y : CpltSepUniformSpace}
    (f : toUniformSpace (CpltSepUniformSpace.of (Completion X)) ⟶ toUniformSpace Y) :
    (extensionHom (completionHom X ≫ f)).hom = f := by
  ext x
  exact congr_fun (Completion.extension_comp_coe f.hom.property) x

@[deprecated (since := "2025-12-18")] alias extension_comp_coe := extension_comp_hom

set_option backward.isDefEq.respectTransparency false in
/-- The completion functor is left adjoint to the forgetful functor. -/
noncomputable def adj : completionFunctor ⊣ forget₂ CpltSepUniformSpace UniformSpaceCat :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y =>
        { toFun := fun f => completionHom X ≫ f.hom
          invFun := fun f => extensionHom f
          left_inv := fun f => InducedCategory.hom_ext (by simp)
          right_inv := fun f => by
            ext x
            rcases f with ⟨⟨_, _⟩⟩
            exact @Completion.extension_coe _ _ _ _ _ (CpltSepUniformSpace.t0Space _)
              ‹_› _ }
      homEquiv_naturality_left_symm := fun {X' X Y} f g => by
        ext x
        simp [ConcreteCategory.hom_ofHom,
          ← congr_fun (Completion.extension_map (γ := Y) g.hom.2 f.hom.2) x]
        rfl }

noncomputable instance : Reflective (forget₂ CpltSepUniformSpace UniformSpaceCat) where
  L := completionFunctor
  adj := adj
  map_surjective f := ⟨ConcreteCategory.ofHom f.hom, rfl⟩

open CategoryTheory.Limits

-- TODO Once someone defines `HasLimits UniformSpace`, turn this into an instance.
example [HasLimits.{u} UniformSpaceCat.{u}] : HasLimits.{u} CpltSepUniformSpace.{u} :=
  hasLimits_of_reflective <| forget₂ CpltSepUniformSpace UniformSpaceCat.{u}

end UniformSpaceCat
