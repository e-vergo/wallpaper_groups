/-
Copyright (c) 2025 Wallpaper Groups Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import WallpaperGroups.Euclidean.OrthogonalGroup
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.GroupTheory.SpecificGroups.KleinFour
import Mathlib.GroupTheory.IndexNormal

/-!
# Rotation and Reflection Matrix Helpers

This file provides helper lemmas for rotation and reflection matrices used in
cyclic and dihedral point group definitions.

## Main results

* `rotationMatrix'_add` - Addition formula for rotation matrices
* `rotationMatrix'_zero` - Rotation by 0 is identity
* `rotationMatrix'_two_pi` - Rotation by 2π is identity
* `rotationMatrix'_pow` - Power formula for rotation matrices
-/

namespace WallpaperGroups.PointGroup

open WallpaperGroups.Euclidean

-- =============================================================================
-- Helper lemmas for rotation matrices
-- =============================================================================

-- Helper: rotation matrix addition
lemma rotationMatrix'_add (θ₁ θ₂ : ℝ) :
    rotationMatrix' θ₁ * rotationMatrix' θ₂ = rotationMatrix' (θ₁ + θ₂) := by
  apply Subtype.ext
  simp only [rotationMatrix', Submonoid.coe_mul]
  rw [rotationMatrix_add]

lemma rotationMatrix'_zero : rotationMatrix' 0 = 1 := by
  apply Subtype.ext
  simp only [rotationMatrix', Submonoid.coe_one]
  exact rotationMatrix_zero

lemma rotationMatrix'_two_pi : rotationMatrix' (2 * Real.pi) = 1 := by
  apply Subtype.ext
  simp only [rotationMatrix', Submonoid.coe_one, rotationMatrix_two_pi]

-- Helper lemma: rotation matrices have det = 1
lemma rotationMatrix'_det (θ : ℝ) : (rotationMatrix' θ).1.det = 1 :=
  rotationMatrix_det θ

-- Helper lemma: reflection matrices have det = -1
lemma reflectionMatrix'_det (θ : ℝ) : (reflectionMatrix' θ).1.det = -1 :=
  reflectionMatrix_det θ

-- Periodicity lemmas for rotations
lemma rotationMatrix'_add_two_pi (θ : ℝ) :
    rotationMatrix' (θ + 2 * Real.pi) = rotationMatrix' θ := by
  apply Subtype.ext; simp only [rotationMatrix']
  ext i j; simp only [rotationMatrix, Matrix.of_apply]
  fin_cases i <;> fin_cases j <;>
    simp [Real.sin_add_two_pi, Real.cos_add_two_pi]

lemma rotationMatrix'_sub_two_pi (θ : ℝ) :
    rotationMatrix' (θ - 2 * Real.pi) = rotationMatrix' θ := by
  apply Subtype.ext; simp only [rotationMatrix']
  ext i j; simp only [rotationMatrix, Matrix.of_apply]
  fin_cases i <;> fin_cases j <;>
    simp [Real.sin_sub_two_pi, Real.cos_sub_two_pi]

lemma reflectionMatrix'_add_two_pi (θ : ℝ) :
    reflectionMatrix' (θ + 2 * Real.pi) = reflectionMatrix' θ := by
  apply Subtype.ext; simp only [reflectionMatrix']
  ext i j; simp only [reflectionMatrix, Matrix.of_apply]
  fin_cases i <;> fin_cases j <;>
    simp [Real.sin_add_two_pi, Real.cos_add_two_pi]

lemma reflectionMatrix'_sub_two_pi (θ : ℝ) :
    reflectionMatrix' (θ - 2 * Real.pi) = reflectionMatrix' θ := by
  apply Subtype.ext; simp only [reflectionMatrix']
  ext i j; simp only [reflectionMatrix, Matrix.of_apply]
  fin_cases i <;> fin_cases j <;>
    simp [Real.sin_sub_two_pi, Real.cos_sub_two_pi]

lemma rotationMatrix'_add_nat_mul_two_pi (θ : ℝ) (k : ℕ) :
    rotationMatrix' (θ + (k : ℝ) * (2 * Real.pi)) = rotationMatrix' θ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h : θ + ((k + 1 : ℕ) : ℝ) * (2 * Real.pi) =
             (θ + (k : ℝ) * (2 * Real.pi)) + 2 * Real.pi := by push_cast; ring
    rw [h, rotationMatrix'_add_two_pi, ih]

-- Power formula for rotation matrices
lemma rotationMatrix'_pow (θ : ℝ) (k : ℕ) :
    (rotationMatrix' θ) ^ k = rotationMatrix' ((k : ℝ) * θ) := by
  induction k with
  | zero => simp [rotationMatrix'_zero]
  | succ k ih =>
    have h : ((k + 1 : ℕ) : ℝ) * θ = (k : ℝ) * θ + θ := by push_cast; ring
    rw [pow_succ, ih, rotationMatrix'_add, h]

-- n-th power of rotation by 2π/n is identity
lemma rotationMatrix'_pow_n (n : ℕ) [NeZero n] :
    (rotationMatrix' (2 * Real.pi / n)) ^ n = 1 := by
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
  rw [rotationMatrix'_pow]
  have h2 : (n : ℝ) * (2 * Real.pi / n) = 2 * Real.pi := by field_simp
  rw [h2, rotationMatrix'_two_pi]

-- =============================================================================
-- Order of rotation and reflection elements
-- =============================================================================

lemma zpowers_eq_pair_of_orderOf_two {G : Type*} [Group G] (g : G) (hg : orderOf g = 2) :
    (Subgroup.zpowers g : Set G) = {1, g} := by
  ext x
  simp only [SetLike.mem_coe, Subgroup.mem_zpowers_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨n, rfl⟩
    have h2 : g ^ (2 : ℕ) = 1 := by rw [← hg]; exact pow_orderOf_eq_one g
    have hn : n % 2 = 0 ∨ n % 2 = 1 := Int.emod_two_eq_zero_or_one n
    rcases hn with hn | hn
    · left
      have hk : ∃ k, n = 2 * k := ⟨n / 2, (Int.mul_ediv_add_emod n 2).symm.trans (by rw [hn]; ring)⟩
      obtain ⟨k, rfl⟩ := hk
      rw [zpow_mul]; norm_cast; rw [h2, one_zpow]
    · right
      have hk : ∃ k, n = 2 * k + 1 := ⟨n / 2, (Int.mul_ediv_add_emod n 2).symm.trans (by rw [hn])⟩
      obtain ⟨k, rfl⟩ := hk
      rw [zpow_add, zpow_mul, zpow_one]; norm_cast; rw [h2, one_zpow, one_mul]
  · rintro (rfl | rfl)
    · exact ⟨0, zpow_zero _⟩
    · exact ⟨1, zpow_one _⟩

lemma orderOf_rotationMatrix'_pi : orderOf (rotationMatrix' Real.pi) = 2 := by
  apply orderOf_eq_prime
  · apply Subtype.ext
    simp only [sq, rotationMatrix', Submonoid.coe_mul, Submonoid.coe_one]
    rw [rotationMatrix_add, ← two_mul, rotationMatrix_two_pi]
  · intro h
    have := congrArg (·.1) h
    simp only [rotationMatrix', Submonoid.coe_one] at this
    have hcos : rotationMatrix Real.pi 0 0 = 1 := by rw [this]; rfl
    simp only [rotationMatrix, Matrix.of_apply, Matrix.cons_val_zero] at hcos
    have : Real.cos Real.pi = 1 := hcos
    rw [Real.cos_pi] at this
    norm_num at this

lemma orderOf_reflectionMatrix'_zero : orderOf (reflectionMatrix' 0) = 2 := by
  apply orderOf_eq_prime
  · apply Subtype.ext
    simp only [sq, reflectionMatrix', Submonoid.coe_mul, Submonoid.coe_one]
    exact reflectionMatrix_sq 0
  · intro h
    have := congrArg (·.1) h
    simp only [reflectionMatrix', Submonoid.coe_one] at this
    have h11 : reflectionMatrix 0 1 1 = (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 1 := by rw [this]
    simp only [reflectionMatrix, Matrix.of_apply, Matrix.cons_val_one,
      Real.cos_zero, Matrix.one_apply_eq] at h11
    norm_num at h11

/-- The order of the rotation by 2π/n is exactly n. -/
lemma orderOf_rotationMatrix'_two_pi_div (n : ℕ) [NeZero n] :
    orderOf (rotationMatrix' (2 * Real.pi / n)) = n := by
  apply orderOf_eq_of_pow_and_pow_div_prime (NeZero.pos n) (rotationMatrix'_pow_n n)
  intro p hp hdiv
  by_contra h_pow_eq_one
  rw [rotationMatrix'_pow] at h_pow_eq_one
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
  have hp_pos : (p : ℝ) > 0 := by exact_mod_cast hp.pos
  obtain ⟨k, hk⟩ := hdiv
  have hk_pos : 0 < k := by
    by_contra h; push_neg at h
    interval_cases k; simp only [mul_zero] at hk; exact (NeZero.ne n) hk
  have h_angle : (n / p : ℕ) * (2 * Real.pi / n) = 2 * Real.pi / p := by
    have hndivp : (n / p : ℕ) = k := by
      rw [hk, Nat.mul_div_cancel_left k hp.pos]
    rw [hndivp]
    have hp_ne : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
    field_simp
    rw [hk]
    push_cast
    ring
  rw [h_angle] at h_pow_eq_one
  have h := congrArg (·.1) h_pow_eq_one
  simp only [rotationMatrix', Submonoid.coe_one] at h
  have h00 : rotationMatrix (2 * Real.pi / p) 0 0 = 1 := by
    have := congrFun (congrFun h 0) 0
    simp only [Matrix.one_apply_eq] at this
    exact this
  simp only [rotationMatrix, Matrix.of_apply, Matrix.cons_val_zero] at h00
  have h_cos_eq_one : Real.cos (2 * Real.pi / p) = 1 := h00
  have h2pi_div_p_pos : 2 * Real.pi / p > 0 := by positivity
  have h2pi_div_p_lt : 2 * Real.pi / p < 2 * Real.pi := by
    have hp_gt_one : 1 < p := hp.one_lt
    have hp_real_gt_one : (1 : ℝ) < p := by exact_mod_cast hp_gt_one
    have h1 : (p : ℝ)⁻¹ < 1 := by
      have hdiv : 1 / (p : ℝ) < 1 := by rw [div_lt_one hp_pos]; exact hp_real_gt_one
      simp only [one_div] at hdiv; exact hdiv
    calc 2 * Real.pi / p = 2 * Real.pi * (p : ℝ)⁻¹ := by rw [div_eq_mul_inv]
      _ < 2 * Real.pi * 1 := by nlinarith [Real.pi_pos]
      _ = 2 * Real.pi := by ring
  -- cos x = 1 iff x = 2πm for some integer m
  rw [Real.cos_eq_one_iff] at h_cos_eq_one
  obtain ⟨m, hm⟩ := h_cos_eq_one
  -- hm : m * (2 * π) = 2 * π / p
  -- With 0 < 2π/p < 2π, m must be 0
  have hm_zero : m = 0 := by
    by_contra hm_ne
    rcases (ne_iff_lt_or_gt.mp hm_ne) with hm_neg | hm_pos
    · have hm_le : (m : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_iff.mpr hm_neg
      have : (m : ℝ) * (2 * Real.pi) ≤ -1 * (2 * Real.pi) := by nlinarith [Real.pi_pos]
      have : (m : ℝ) * (2 * Real.pi) ≤ -(2 * Real.pi) := by linarith
      rw [hm] at this
      linarith
    · have hm_ge : (m : ℝ) ≥ 1 := by exact_mod_cast Int.add_one_le_iff.mpr hm_pos
      have : (m : ℝ) * (2 * Real.pi) ≥ 1 * (2 * Real.pi) := by nlinarith [Real.pi_pos]
      have : (m : ℝ) * (2 * Real.pi) ≥ 2 * Real.pi := by linarith
      rw [hm] at this
      linarith
  rw [hm_zero] at hm
  simp at hm
  linarith

-- =============================================================================
-- Rotation/reflection multiplication lemmas
-- =============================================================================

lemma rotationMatrix'_mul_reflectionMatrix' (θ₁ θ₂ : ℝ) :
    rotationMatrix' θ₁ * reflectionMatrix' θ₂ = reflectionMatrix' (θ₁ + θ₂) := by
  apply Subtype.ext
  simp only [rotationMatrix', reflectionMatrix', Submonoid.coe_mul]
  exact rotationMatrix_mul_reflectionMatrix θ₁ θ₂

lemma reflectionMatrix'_mul_rotationMatrix' (θ₁ θ₂ : ℝ) :
    reflectionMatrix' θ₁ * rotationMatrix' θ₂ = reflectionMatrix' (θ₁ - θ₂) := by
  apply Subtype.ext
  simp only [rotationMatrix', reflectionMatrix', Submonoid.coe_mul]
  exact reflectionMatrix_mul_rotationMatrix θ₁ θ₂

lemma reflectionMatrix'_mul (θ₁ θ₂ : ℝ) :
    reflectionMatrix' θ₁ * reflectionMatrix' θ₂ = rotationMatrix' (θ₁ - θ₂) := by
  apply Subtype.ext
  simp only [rotationMatrix', reflectionMatrix', Submonoid.coe_mul]
  exact reflectionMatrix_mul θ₁ θ₂

end WallpaperGroups.PointGroup
