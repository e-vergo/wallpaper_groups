/-
Copyright (c) 2025 Wallpaper Groups Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import WallpaperGroups.Euclidean.Plane
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

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
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    rw [show (a * b).1 = a.1 * b.1 from rfl, Matrix.det_mul, ha, hb, mul_one]
  one_mem' := by
    simp only [Set.mem_setOf_eq]
    exact Matrix.det_one
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at *
    have h : a⁻¹.1 = star a.1 := rfl
    rw [h, show star a.1 = a.1ᴴ from rfl]
    rw [Matrix.det_conjTranspose]
    simp only [star_trivial, ha]

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
  ext i j
  simp only [rotationMatrix, transpose_apply, mul_apply, one_apply]
  rw [Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, of_apply, cons_val',
      empty_val', cons_val_fin_one, cons_val_zero, cons_val_one]
  · simp only [ite_true]; ring_nf; exact Real.cos_sq_add_sin_sq θ
  · simp only [Fin.reduceEq, ite_false]; ring
  · simp only [Fin.reduceEq, ite_false]; ring
  · simp only [ite_true]; ring_nf; rw [add_comm]; exact Real.cos_sq_add_sin_sq θ

/-- Rotation matrices have determinant 1.

blueprint: lem:rotation_in_SO2 -/
lemma rotationMatrix_det (θ : ℝ) : (rotationMatrix θ).det = 1 := by
  simp [rotationMatrix, det_fin_two_of]
  ring_nf
  exact Real.cos_sq_add_sin_sq θ

/-- Reflection matrices are orthogonal. -/
lemma reflectionMatrix_orthogonal (θ : ℝ) :
    (reflectionMatrix θ)ᵀ * reflectionMatrix θ = 1 := by
  ext i j
  simp only [reflectionMatrix, transpose_apply, mul_apply, one_apply]
  rw [Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, of_apply, cons_val',
      empty_val', cons_val_fin_one, cons_val_zero, cons_val_one]
  · simp only [ite_true]; ring_nf; exact Real.cos_sq_add_sin_sq θ
  · simp only [Fin.reduceEq, ite_false]; ring
  · simp only [Fin.reduceEq, ite_false]; ring
  · simp only [ite_true]; ring_nf; rw [add_comm]; exact Real.cos_sq_add_sin_sq θ

/-- Reflection matrices have determinant -1.

blueprint: lem:reflection_det -/
lemma reflectionMatrix_det (θ : ℝ) : (reflectionMatrix θ).det = -1 := by
  simp only [reflectionMatrix, det_fin_two_of]
  ring_nf
  rw [show -(Real.cos θ ^ 2) - Real.sin θ ^ 2 = -(Real.cos θ ^ 2 + Real.sin θ ^ 2) by ring]
  rw [Real.cos_sq_add_sin_sq]

/-- Rotation matrices are in the orthogonal group. -/
lemma rotationMatrix_mem_orthogonalGroup (θ : ℝ) :
    rotationMatrix θ ∈ orthogonalGroup (Fin 2) ℝ := by
  rw [mem_orthogonalGroup_iff']
  exact rotationMatrix_orthogonal θ

/-- Reflection matrices are in the orthogonal group. -/
lemma reflectionMatrix_mem_orthogonalGroup (θ : ℝ) :
    reflectionMatrix θ ∈ orthogonalGroup (Fin 2) ℝ := by
  rw [mem_orthogonalGroup_iff']
  exact reflectionMatrix_orthogonal θ

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
  set M := A.1 with hM
  let a := M 0 0
  let b := M 1 0
  let c := M 0 1
  let d := M 1 1
  let z : ℂ := ⟨a, b⟩
  have h_ortho : M ᵀ * M = 1 := by
    have := A.2; rw [mem_orthogonalGroup_iff'] at this; exact this
  have h_col0_norm : a ^ 2 + b ^ 2 = 1 := by
    have h00 : (M ᵀ * M) 0 0 = 1 := by rw [h_ortho]; rfl
    simp only [transpose_apply, mul_apply, Fin.sum_univ_two] at h00
    linarith [h00]
  have h_col01 : a * c + b * d = 0 := by
    have h01 : (M ᵀ * M) 0 1 = 0 := by rw [h_ortho]; rfl
    simp only [transpose_apply, mul_apply, Fin.sum_univ_two] at h01
    linarith [h01]
  have h_col1_norm : c ^ 2 + d ^ 2 = 1 := by
    have h11 : (M ᵀ * M) 1 1 = 1 := by rw [h_ortho]; rfl
    simp only [transpose_apply, mul_apply, Fin.sum_univ_two] at h11
    linarith [h11]
  have h_det : a * d - c * b = 1 := by
    simp only [SpecialOrthogonalGroup2, Subgroup.mem_mk, det_fin_two] at hA
    exact hA
  have hz_norm : ‖z‖ = 1 := by
    have h1 : Complex.normSq z = 1 := by
      rw [Complex.normSq_mk]; simp only [sq] at h_col0_norm; linarith
    have h2 : ‖z‖ ^ 2 = 1 := by rw [← Complex.normSq_eq_norm_sq]; exact h1
    nlinarith [norm_nonneg z]
  have hz_ne : z ≠ 0 := by
    intro h; rw [h] at hz_norm; simp at hz_norm
  use Complex.arg z
  have cos_eq : Real.cos (Complex.arg z) = a := by
    have := Complex.cos_arg hz_ne
    simp only [hz_norm, div_one] at this
    exact this
  have sin_eq : Real.sin (Complex.arg z) = b := by
    have := Complex.sin_arg z
    simp only [hz_norm, div_one] at this
    exact this
  have h_d : d = a := by
    nlinarith [sq_nonneg (c + b), sq_nonneg (c - b), sq_nonneg (d + a), sq_nonneg (d - a)]
  have h_c : c = -b := by
    nlinarith [sq_nonneg (c + b), sq_nonneg (c - b), sq_nonneg (d + a), sq_nonneg (d - a)]
  have h_c' : M 0 1 = -(M 1 0) := h_c
  have h_d' : M 1 1 = M 0 0 := h_d
  have cos_eq' : Real.cos z.arg = M 0 0 := cos_eq
  have sin_eq' : Real.sin z.arg = M 1 0 := sin_eq
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.mk_zero, Fin.mk_one, rotationMatrix, of_apply, cons_val', empty_val',
      cons_val_fin_one, cons_val_zero, cons_val_one]
  · exact cos_eq'.symm
  · rw [h_c', ← sin_eq']
  · exact sin_eq'.symm
  · rw [h_d', cos_eq']

/-- Helper: orthogonal matrices with det = -1 are reflections. -/
private lemma O2_det_neg_one_eq_reflections (A : OrthogonalGroup2) (hA : A.1.det = -1) :
    ∃ θ : ℝ, A.1 = reflectionMatrix θ := by
  set M := A.1 with hM
  let a := M 0 0
  let b := M 1 0
  let c := M 0 1
  let d := M 1 1
  let z : ℂ := ⟨a, b⟩
  have h_ortho : M ᵀ * M = 1 := by
    have := A.2; rw [mem_orthogonalGroup_iff'] at this; exact this
  have h_col0_norm : a ^ 2 + b ^ 2 = 1 := by
    have h00 : (M ᵀ * M) 0 0 = 1 := by rw [h_ortho]; rfl
    simp only [transpose_apply, mul_apply, Fin.sum_univ_two] at h00
    linarith [h00]
  have h_col01 : a * c + b * d = 0 := by
    have h01 : (M ᵀ * M) 0 1 = 0 := by rw [h_ortho]; rfl
    simp only [transpose_apply, mul_apply, Fin.sum_univ_two] at h01
    linarith [h01]
  have h_col1_norm : c ^ 2 + d ^ 2 = 1 := by
    have h11 : (M ᵀ * M) 1 1 = 1 := by rw [h_ortho]; rfl
    simp only [transpose_apply, mul_apply, Fin.sum_univ_two] at h11
    linarith [h11]
  have h_det : a * d - c * b = -1 := by
    simp only [det_fin_two] at hA
    linarith [hA]
  have hz_norm : ‖z‖ = 1 := by
    have h1 : Complex.normSq z = 1 := by
      rw [Complex.normSq_mk]; simp only [sq] at h_col0_norm; linarith
    have h2 : ‖z‖ ^ 2 = 1 := by rw [← Complex.normSq_eq_norm_sq]; exact h1
    nlinarith [norm_nonneg z]
  have hz_ne : z ≠ 0 := by
    intro h; rw [h] at hz_norm; simp at hz_norm
  use Complex.arg z
  have cos_eq : Real.cos (Complex.arg z) = a := by
    have := Complex.cos_arg hz_ne
    simp only [hz_norm, div_one] at this
    exact this
  have sin_eq : Real.sin (Complex.arg z) = b := by
    have := Complex.sin_arg z
    simp only [hz_norm, div_one] at this
    exact this
  have h_d : d = -a := by
    nlinarith [sq_nonneg (c + b), sq_nonneg (c - b), sq_nonneg (d + a), sq_nonneg (d - a)]
  have h_c : c = b := by
    nlinarith [sq_nonneg (c + b), sq_nonneg (c - b), sq_nonneg (d + a), sq_nonneg (d - a)]
  have h_c' : M 0 1 = M 1 0 := h_c
  have h_d' : M 1 1 = -(M 0 0) := h_d
  have cos_eq' : Real.cos z.arg = M 0 0 := cos_eq
  have sin_eq' : Real.sin z.arg = M 1 0 := sin_eq
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.mk_zero, Fin.mk_one, reflectionMatrix, of_apply, cons_val', empty_val',
      cons_val_fin_one, cons_val_zero, cons_val_one]
  · exact cos_eq'.symm
  · rw [h_c', sin_eq']
  · exact sin_eq'.symm
  · rw [h_d', cos_eq']

/-- O(2) consists of rotations and reflections.

blueprint: lem:O2_structure -/
lemma O2_eq_rotations_or_reflections (A : OrthogonalGroup2) :
    (∃ θ : ℝ, A.1 = rotationMatrix θ) ∨ (∃ θ : ℝ, A.1 = reflectionMatrix θ) := by
  have h_det_sq : A.1.det ^ 2 = 1 := by
    have h := A.2
    rw [mem_orthogonalGroup_iff'] at h
    have key : (A.1ᵀ * A.1).det = 1 := by rw [h]; exact det_one
    simp only [det_mul, det_transpose] at key
    rw [pow_two]; exact key
  have h_det : A.1.det = 1 ∨ A.1.det = -1 := by
    have : (A.1.det - 1) * (A.1.det + 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp this with h | h
    · left; linarith
    · right; linarith
  rcases h_det with hdet | hdet
  · left; exact SO2_eq_rotations A hdet
  · right; exact O2_det_neg_one_eq_reflections A hdet

/-- Rotation by 0 is the identity. -/
lemma rotationMatrix_zero : rotationMatrix 0 = 1 := by
  simp only [rotationMatrix, Real.cos_zero, Real.sin_zero, neg_zero]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [of_apply, cons_val_zero, cons_val_one]

/-- Rotation composition corresponds to angle addition. -/
lemma rotationMatrix_add (θ₁ θ₂ : ℝ) :
    rotationMatrix θ₁ * rotationMatrix θ₂ = rotationMatrix (θ₁ + θ₂) := by
  simp only [rotationMatrix, Real.cos_add, Real.sin_add]
  ext i j
  simp only [mul_apply, of_apply]
  rw [Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, cons_val_zero, cons_val_one] <;>
    ring

/-- Rotation by 2π is the identity. -/
lemma rotationMatrix_two_pi : rotationMatrix (2 * Real.pi) = 1 := by
  simp only [rotationMatrix, Real.cos_two_pi, Real.sin_two_pi, neg_zero]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [of_apply, cons_val_zero, cons_val_one]

/-- Rotation by π is the 180° rotation: R_π = [[-1, 0], [0, -1]]. -/
lemma rotationMatrix_pi : rotationMatrix Real.pi = -1 := by
  simp only [rotationMatrix, Real.cos_pi, Real.sin_pi, neg_zero]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [of_apply, cons_val_zero, cons_val_one, neg_apply]

/-- Composition of two reflections is a rotation. -/
lemma reflectionMatrix_mul (θ₁ θ₂ : ℝ) :
    reflectionMatrix θ₁ * reflectionMatrix θ₂ = rotationMatrix (θ₁ - θ₂) := by
  simp only [reflectionMatrix, rotationMatrix, Real.cos_sub, Real.sin_sub]
  ext i j
  simp only [mul_apply, of_apply]
  rw [Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, cons_val_zero, cons_val_one] <;>
    ring

/-- Reflection squared is the identity. -/
lemma reflectionMatrix_sq (θ : ℝ) :
    reflectionMatrix θ * reflectionMatrix θ = 1 := by
  rw [reflectionMatrix_mul]
  simp [sub_self, rotationMatrix_zero]

/-- Rotation times reflection is reflection with added angle. -/
lemma rotationMatrix_mul_reflectionMatrix (θ₁ θ₂ : ℝ) :
    rotationMatrix θ₁ * reflectionMatrix θ₂ = reflectionMatrix (θ₁ + θ₂) := by
  ext i j
  simp only [rotationMatrix, reflectionMatrix, mul_apply, of_apply]
  rw [Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, cons_val_zero, cons_val_one,
      Real.cos_add, Real.sin_add] <;> ring

/-- Reflection times rotation is reflection with subtracted angle. -/
lemma reflectionMatrix_mul_rotationMatrix (θ₁ θ₂ : ℝ) :
    reflectionMatrix θ₁ * rotationMatrix θ₂ = reflectionMatrix (θ₁ - θ₂) := by
  ext i j
  simp only [rotationMatrix, reflectionMatrix, mul_apply, of_apply]
  rw [Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, cons_val_zero, cons_val_one,
      Real.cos_sub, Real.sin_sub] <;> ring

end WallpaperGroups.Euclidean
