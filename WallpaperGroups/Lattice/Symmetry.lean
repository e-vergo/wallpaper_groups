/-
Copyright (c) 2025 Wallpaper Groups Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import WallpaperGroups.Lattice.Basic
import WallpaperGroups.Euclidean.OrthogonalGroup

/-!
# Lattice Symmetry Groups

This file defines the symmetry group of a lattice and characterizes
lattice-preserving linear maps.

## Main definitions

* `latticeSymmetryGroup` - Sym(Λ) = {A ∈ O(2) | A(Λ) = Λ}
* `IsLatticePreserving` - Predicate for A(Λ) ⊆ Λ

## Main results

* `latticeSymmetryGroup_finite` - Sym(Λ) is finite
* `isLatticePreserving_iff_integerMatrix` - A preserves Λ iff its matrix in a lattice basis has integer entries
-/

namespace WallpaperGroups.Lattice

open WallpaperGroups.Euclidean
open Matrix

/-- A linear map preserves a lattice if it maps lattice points to lattice points.

blueprint: def:lattice_preserving -/
def IsLatticePreserving (Λ : Lattice2) (A : OrthogonalGroup2) : Prop :=
  ∀ v : EuclideanPlane, v ∈ Λ →
    (EuclideanSpace.equiv (Fin 2) ℝ).symm (A.1.mulVec (EuclideanSpace.equiv (Fin 2) ℝ v)) ∈ Λ

/-- The symmetry group of a lattice Λ consists of all orthogonal transformations
that preserve Λ.

Sym(Λ) = {A ∈ O(2) | A(Λ) = Λ}

blueprint: def:lattice_symmetry -/
def latticeSymmetryGroup (Λ : Lattice2) : Subgroup OrthogonalGroup2 where
  carrier := {A | IsLatticePreserving Λ A ∧ IsLatticePreserving Λ A⁻¹}
  mul_mem' := by
    intro A B ⟨hA, hA'⟩ ⟨hB, hB'⟩
    constructor
    · intro v hv
      have hBv := hB v hv
      have key : (A * B).1.mulVec = fun w => A.1.mulVec (B.1.mulVec w) := by
        ext w
        simp only [Submonoid.coe_mul, mulVec_mulVec]
      simp only [IsLatticePreserving] at hA hBv ⊢
      rw [key]
      have hBv' : (EuclideanSpace.equiv (Fin 2) ℝ).symm
          (B.1.mulVec (EuclideanSpace.equiv (Fin 2) ℝ v)) ∈ Λ := hBv
      have := hA ((EuclideanSpace.equiv (Fin 2) ℝ).symm
          (B.1.mulVec (EuclideanSpace.equiv (Fin 2) ℝ v))) hBv'
      simp only [ContinuousLinearEquiv.apply_symm_apply] at this
      exact this
    · intro v hv
      have hA'v := hA' v hv
      have key : (A * B)⁻¹.1.mulVec = fun w => B⁻¹.1.mulVec (A⁻¹.1.mulVec w) := by
        ext w
        simp only [_root_.mul_inv_rev, Submonoid.coe_mul, mulVec_mulVec]
      simp only [IsLatticePreserving] at hB' hA'v ⊢
      rw [key]
      have hA'v' : (EuclideanSpace.equiv (Fin 2) ℝ).symm
          (A⁻¹.1.mulVec (EuclideanSpace.equiv (Fin 2) ℝ v)) ∈ Λ := hA'v
      have := hB' ((EuclideanSpace.equiv (Fin 2) ℝ).symm
          (A⁻¹.1.mulVec (EuclideanSpace.equiv (Fin 2) ℝ v))) hA'v'
      simp only [ContinuousLinearEquiv.apply_symm_apply] at this
      exact this
  one_mem' := by
    constructor
    · intro v hv
      simp only [OneMemClass.coe_one, one_mulVec]
      simp only [ContinuousLinearEquiv.symm_apply_apply]
      exact hv
    · intro v hv
      simp only [inv_one, OneMemClass.coe_one, one_mulVec]
      simp only [ContinuousLinearEquiv.symm_apply_apply]
      exact hv
  inv_mem' := by
    intro A ⟨hA, hA'⟩
    constructor
    · exact hA'
    · simp only [inv_inv]; exact hA

/-- The symmetry group of any lattice is finite.

This follows because Sym(Λ) must preserve the finite set of shortest nonzero
lattice vectors.

blueprint: lem:symmetry_finite -/
lemma latticeSymmetryGroup_finite (Λ : Lattice2) :
    Finite (latticeSymmetryGroup Λ) := by
  sorry

/-- A ∈ O(2) preserves Λ iff its matrix representation in a lattice basis has integer entries.

If Λ = ℤa + ℤb, then A preserves Λ iff there exist integers m₁₁, m₁₂, m₂₁, m₂₂ such that
Aa = m₁₁a + m₂₁b and Ab = m₁₂a + m₂₂b.

blueprint: lem:preserving_integer -/
lemma isLatticePreserving_iff_integerMatrix (Λ : Lattice2) (B : LatticeBasis Λ)
    (A : OrthogonalGroup2) :
    IsLatticePreserving Λ A ↔
    ∃ (M : Matrix (Fin 2) (Fin 2) ℤ),
      A.1.mulVec B.a = (M 0 0 : ℝ) • B.a + (M 1 0 : ℝ) • B.b ∧
      A.1.mulVec B.b = (M 0 1 : ℝ) • B.a + (M 1 1 : ℝ) • B.b := by
  sorry

/-- The matrix of a lattice symmetry in a lattice basis has determinant ±1. -/
lemma latticeSymmetry_matrix_det (Λ : Lattice2) (B : LatticeBasis Λ)
    (A : OrthogonalGroup2) (hA : A ∈ latticeSymmetryGroup Λ) :
    ∃ (M : Matrix (Fin 2) (Fin 2) ℤ), M.det = 1 ∨ M.det = -1 := by
  sorry

/-- The identity is always a lattice symmetry. -/
lemma latticeSymmetryGroup.one_mem (Λ : Lattice2) :
    (1 : OrthogonalGroup2) ∈ latticeSymmetryGroup Λ :=
  (latticeSymmetryGroup Λ).one_mem

/-- The 180° rotation R_π is always a lattice symmetry.

This corresponds to the fact that -1 ∈ Sym(Λ) for any lattice. -/
lemma latticeSymmetryGroup.neg_one_mem (Λ : Lattice2) :
    rotationMatrix' Real.pi ∈ latticeSymmetryGroup Λ := by
  sorry

end WallpaperGroups.Lattice
