/-
Copyright (c) 2021 Yourong Zang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yourong Zang
-/
module

public import Mathlib.Analysis.Calculus.Conformal.NormedSpace
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic

/-!
# Angles and conformal maps

This file proves that conformal maps preserve angles.

-/

public section


namespace InnerProductGeometry

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedAddCommGroup F]
variable [InnerProductSpace ℝ E] [InnerProductSpace ℝ F]

theorem IsConformalMap.preserves_angle {f' : E →L[ℝ] F} (h : IsConformalMap f') (u v : E) :
    angle (f' u) (f' v) = angle u v := by
  obtain ⟨c, hc, li, rfl⟩ := h
  exact (angle_smul_smul hc _ _).trans (li.angle_map _ _)

/-- If a real differentiable map `f` is conformal at a point `x`,
then it preserves the angles at that point. -/
theorem ConformalAt.preserves_angle {f : E → F} {x : E} (h : ConformalAt f x) (u v : E) :
    angle ((fderiv ℝ f x) u) ((fderiv ℝ f x) v) = angle u v :=
  IsConformalMap.preserves_angle (conformalAt_iff_isConformalMap_fderiv.mp h) u v

end InnerProductGeometry
