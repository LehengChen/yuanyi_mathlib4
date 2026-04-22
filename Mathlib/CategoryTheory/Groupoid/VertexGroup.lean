/-
Copyright (c) 2022 Rémi Bottinelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémi Bottinelli
-/
module

public import Mathlib.Algebra.Group.Basic
public import Mathlib.CategoryTheory.Conj
public import Mathlib.CategoryTheory.Groupoid
public import Mathlib.CategoryTheory.PathCategory.Basic
public import Mathlib.Combinatorics.Quiver.Path

/-!
# Vertex group

This file defines the vertex group (*aka* isotropy group) of a groupoid at a vertex.

## Implementation notes

* The instance is defined "manually", instead of relying on `CategoryTheory.Aut.group` or
  using `CategoryTheory.inv`.
* The multiplication order therefore matches the categorical one: `x * y = x ≫ y`.
* The inverse is directly defined in terms of the groupoidal inverse: `x ⁻¹ = Groupoid.inv x`.

## Tags

isotropy, vertex group, groupoid
-/

@[expose] public section


namespace CategoryTheory

namespace Groupoid

universe u v

variable {C : Type u} [Groupoid C]

/-- The vertex group at `c`. -/
@[simps mul one inv]
instance vertexGroup (c : C) : Group (c ⟶ c) where
  mul := fun x y : c ⟶ c => x ≫ y
  mul_assoc := Category.assoc
  one := 𝟙 c
  one_mul := Category.id_comp
  mul_one := Category.comp_id
  inv := Groupoid.inv
  inv_mul_cancel := inv_comp

/-- The inverse in the group is equal to the inverse given by `CategoryTheory.inv`. -/
theorem vertexGroup.inv_eq_inv (c : C) (γ : c ⟶ c) : γ⁻¹ = CategoryTheory.inv γ :=
  Groupoid.inv_eq_inv γ

/-- An arrow in the groupoid defines, by conjugation, an isomorphism of groups between
its endpoints.
-/
@[simps]
def vertexGroupIsomOfMap {c d : C} (f : c ⟶ d) : (c ⟶ c) ≃* (d ⟶ d) where
  toFun γ := inv f ≫ γ ≫ f
  invFun δ := f ≫ δ ≫ inv f
  left_inv := ((Groupoid.isoEquivHom c d).symm f).symm_self_conj
  right_inv := ((Groupoid.isoEquivHom c d).symm f).self_symm_conj
  map_mul' := ((Groupoid.isoEquivHom c d).symm f).conj_comp

/-- A path in the groupoid defines an isomorphism between its endpoints.
-/
def vertexGroupIsomOfPath {c d : C} (p : Quiver.Path c d) : (c ⟶ c) ≃* (d ⟶ d) :=
  vertexGroupIsomOfMap (composePath p)

/-- A functor defines a morphism of vertex groups. -/
@[simps]
def CategoryTheory.Functor.mapVertexGroup {D : Type v} [Groupoid D] (φ : C ⥤ D) (c : C) :
    (c ⟶ c) →* (φ.obj c ⟶ φ.obj c) where
  toFun := φ.map
  map_one' := φ.map_id c
  map_mul' := φ.map_comp

end Groupoid

end CategoryTheory
