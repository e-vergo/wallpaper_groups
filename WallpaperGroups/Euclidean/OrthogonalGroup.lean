/-
Copyright (c) 2025 Wallpaper Groups Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import WallpaperGroups.Euclidean.Plane

/-!
# The Orthogonal Group O(2) and Special Orthogonal Group SO(2)

This file defines the orthogonal group O(2) and special orthogonal group SO(2),
along with rotation and reflection matrices.

## Main definitions

* `OrthogonalGroup2` - The orthogonal group O(2) = {A ∈ GL₂(ℝ) | AᵀA = I}
* `SpecialOrthogonalGroup2` - The special orthogonal group SO(2) ⊂ O(2)
* `rotationMatrix` - The rotation matrix R_θ for angle θ
* `reflectionMatrix` - The reflection matrix S_θ for angle θ

## Main results

* `rotationMatrix_mem_SO2` - Rotation matrices are in SO(2)
* `reflectionMatrix_det` - Reflection matrices have determinant -1
* `SO2_eq_rotations` - SO(2) consists exactly of rotations
* `O2_eq_rotations_union_reflections` - O(2) = rotations ∪ reflections
-/

namespace WallpaperGroups.Euclidean

open Matrix

/-- The orthogonal group O(2) consists of 2×2 real matrices A with AᵀA = I.

These are the linear isometries of the Euclidean plane.

blueprint: def:orthogonal_group -/
abbrev OrthogonalGroup2 : Type := Matrix.orthogonalGroup (Fin 2) ℝ

/-- The special orthogonal group SO(2) consists of orthogonal matrices with determinant 1.

These are the rotations of the Euclidean plane.

blueprint: def:special_orthogonal -/
def SpecialOrthogonalGroup2 : Subgroup OrthogonalGroup2 where
  carrier := {A | A.1.det = 1}
  mul_mem' := by intro a b ha hb; sorry
  one_mem' := by sorry
  inv_mem' := by intro a ha; sorry

/-- The rotation matrix R_θ rotates by angle θ counterclockwise.

R_θ = [[cos θ, -sin θ], [sin θ, cos θ]]

blueprint: def:rotation_matrix -/
noncomputable def rotationMatrix (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ]

/-- The reflection matrix S_θ reflects across the line at angle θ/2 from the x-axis.

S_θ = [[cos θ, sin θ], [sin θ, -cos θ]]

blueprint: def:reflection_matrix -/
noncomputable def reflectionMatrix (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos θ, Real.sin θ; Real.sin θ, -Real.cos θ]

/-- Rotation matrices are orthogonal.

blueprint: lem:rotation_in_SO2 -/
lemma rotationMatrix_orthogonal (θ : ℝ) :
    (rotationMatrix θ)ᵀ * rotationMatrix θ = 1 := by
  sorry

/-- Rotation matrices have determinant 1.

blueprint: lem:rotation_in_SO2 -/
lemma rotationMatrix_det (θ : ℝ) : (rotationMatrix θ).det = 1 := by
  sorry

/-- Reflection matrices are orthogonal. -/
lemma reflectionMatrix_orthogonal (θ : ℝ) :
    (reflectionMatrix θ)ᵀ * reflectionMatrix θ = 1 := by
  sorry

/-- Reflection matrices have determinant -1.

blueprint: lem:reflection_det -/
lemma reflectionMatrix_det (θ : ℝ) : (reflectionMatrix θ).det = -1 := by
  sorry

/-- Rotation matrices are in the orthogonal group. -/
lemma rotationMatrix_mem_orthogonalGroup (θ : ℝ) :
    rotationMatrix θ ∈ orthogonalGroup (Fin 2) ℝ := by
  sorry

/-- Reflection matrices are in the orthogonal group. -/
lemma reflectionMatrix_mem_orthogonalGroup (θ : ℝ) :
    reflectionMatrix θ ∈ orthogonalGroup (Fin 2) ℝ := by
  sorry

/-- The rotation matrix as an element of the orthogonal group. -/
noncomputable def rotationMatrix' (θ : ℝ) : OrthogonalGroup2 :=
  ⟨rotationMatrix θ, rotationMatrix_mem_orthogonalGroup θ⟩

/-- The reflection matrix as an element of the orthogonal group. -/
noncomputable def reflectionMatrix' (θ : ℝ) : OrthogonalGroup2 :=
  ⟨reflectionMatrix θ, reflectionMatrix_mem_orthogonalGroup θ⟩

/-- SO(2) consists exactly of rotation matrices.

blueprint: lem:SO2_rotations -/
lemma SO2_eq_rotations (A : OrthogonalGroup2) (hA : A ∈ SpecialOrthogonalGroup2) :
    ∃ θ : ℝ, A.1 = rotationMatrix θ := by
  sorry

/-- O(2) consists of rotations and reflections.

blueprint: lem:O2_structure -/
lemma O2_eq_rotations_or_reflections (A : OrthogonalGroup2) :
    (∃ θ : ℝ, A.1 = rotationMatrix θ) ∨ (∃ θ : ℝ, A.1 = reflectionMatrix θ) := by
  sorry

/-- Rotation by 0 is the identity. -/
lemma rotationMatrix_zero : rotationMatrix 0 = 1 := by
  sorry

/-- Rotation composition corresponds to angle addition. -/
lemma rotationMatrix_add (θ₁ θ₂ : ℝ) :
    rotationMatrix θ₁ * rotationMatrix θ₂ = rotationMatrix (θ₁ + θ₂) := by
  sorry

/-- Rotation by 2π is the identity. -/
lemma rotationMatrix_two_pi : rotationMatrix (2 * Real.pi) = 1 := by
  sorry

/-- Rotation by π is the 180° rotation: R_π = [[-1, 0], [0, -1]]. -/
lemma rotationMatrix_pi : rotationMatrix Real.pi = -1 := by
  sorry

/-- Composition of two reflections is a rotation. -/
lemma reflectionMatrix_mul (θ₁ θ₂ : ℝ) :
    reflectionMatrix θ₁ * reflectionMatrix θ₂ = rotationMatrix (θ₁ - θ₂) := by
  sorry

/-- Reflection squared is the identity. -/
lemma reflectionMatrix_sq (θ : ℝ) :
    reflectionMatrix θ * reflectionMatrix θ = 1 := by
  sorry

end WallpaperGroups.Euclidean
