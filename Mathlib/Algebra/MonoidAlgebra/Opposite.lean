/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov, Kim Morrison
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.Ring.Opposite
public import Mathlib.Data.Finsupp.Basic

/-!
# Monoid algebras and the opposite ring
-/

assert_not_exists NonUnitalAlgHom AlgEquiv

@[expose] public noncomputable section

open Finsupp MulOpposite

variable {R M : Type*} [Semiring R] [Mul M]

namespace MonoidAlgebra

set_option backward.isDefEq.respectTransparency false in
/-- The opposite of a monoid algebra is equivalent as a ring to the opposite monoid algebra over the
opposite ring. -/
@[to_additive (dont_translate := R) (attr := simps! +simpRhs apply symm_apply)
/-- The opposite of a monoid algebra is equivalent as a ring to the opposite monoid algebra over the
opposite ring. -/]
protected noncomputable def opRingEquiv : R[M]ᵐᵒᵖ ≃+* Rᵐᵒᵖ[Mᵐᵒᵖ] where
  __ := opAddEquiv.symm.trans <|
      (Finsupp.mapRange.addEquiv (opAddEquiv : R ≃+ Rᵐᵒᵖ)).trans <| Finsupp.domCongr opEquiv
  map_mul' := by
    let f : R[M]ᵐᵒᵖ →+ Rᵐᵒᵖ[Mᵐᵒᵖ] :=
      (opAddEquiv.symm.trans <|
        (Finsupp.mapRange.addEquiv (opAddEquiv : R ≃+ Rᵐᵒᵖ)).trans <| Finsupp.domCongr opEquiv
      ).toAddMonoidHom
    have hf' {m : M} {r : R} :
        ((opAddEquiv.symm.trans
        ((Finsupp.mapRange.addEquiv (opAddEquiv : R ≃+ Rᵐᵒᵖ)).trans (Finsupp.domCongr opEquiv))
      ).toAddMonoidHom) (op (single m r)) = single (op m) (op r) := by
      simp
    have hf {m : M} {r : R} : f (op (single m r)) = single (op m) (op r) := by
      simpa only [f] using (hf' (m := m) (r := r))
    rw [Equiv.toFun_as_coe, AddEquiv.toEquiv_eq_coe, AddEquiv.coe_toEquiv]
    exact f.map_mul_iff.2 <| by
      ext m₁ r₁ m₂ r₂ m
      have hmul :
          (f (op (single m₁ r₁) * op (single m₂ r₂))) m =
            (f (op (single m₁ r₁)) * f (op (single m₂ r₂))) m := by
        rw [hf, hf, ← MulOpposite.op_mul, single_mul_single, hf, single_mul_single]
        rfl
      simpa using hmul

set_option backward.isDefEq.respectTransparency false in
@[to_additive (dont_translate := R)]
lemma opRingEquiv_single (r : R) (x : M) :
    MonoidAlgebra.opRingEquiv (op (single x r)) = single (op x) (op r) := by simp

set_option backward.isDefEq.respectTransparency false in
@[to_additive (dont_translate := R)]
lemma opRingEquiv_symm_single (r : Rᵐᵒᵖ) (x : Mᵐᵒᵖ) :
    MonoidAlgebra.opRingEquiv.symm (single x r) = op (single x.unop r.unop) := by simp

end MonoidAlgebra
