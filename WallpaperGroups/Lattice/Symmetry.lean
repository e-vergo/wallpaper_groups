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
* `isLatticePreserving_iff_integerMatrix` - A preserves Λ iff its matrix
in a lattice basis has integer entries
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

-- Helper: the rotation matrix by π applied to a vector negates it
private lemma rotationMatrix_pi_mulVec (w : Fin 2 → ℝ) :
    (rotationMatrix Real.pi).mulVec w = -w := by
  rw [rotationMatrix_pi]
  ext i
  simp only [neg_apply, one_apply, mulVec, dotProduct]
  rw [Fin.sum_univ_two]
  fin_cases i <;> simp [Pi.neg_apply]

-- Helper: the inverse of R_π is R_π itself (since R_π² = 1)
private lemma rotationMatrix'_pi_inv :
    (rotationMatrix' Real.pi)⁻¹ = rotationMatrix' Real.pi := by
  have h : rotationMatrix' Real.pi * rotationMatrix' Real.pi = 1 := by
    ext i j
    simp only [rotationMatrix', Submonoid.coe_mul]
    have key : rotationMatrix Real.pi * rotationMatrix Real.pi = 1 := by
      rw [rotationMatrix_add,
          show Real.pi + Real.pi = 2 * Real.pi by ring, rotationMatrix_two_pi]
    rw [show (rotationMatrix Real.pi * rotationMatrix Real.pi) i j =
        (1 : Matrix (Fin 2) (Fin 2) ℝ) i j from congrFun (congrFun key i) j]
    rfl
  exact inv_eq_of_mul_eq_one_left h

-- Helper: orthogonal matrices preserve dot product
private lemma orthogonal_dotProduct_preserving (A : OrthogonalGroup2) (v w : Fin 2 → ℝ) :
    (A.1.mulVec v) ⬝ᵥ (A.1.mulVec w) = v ⬝ᵥ w := by
  have h_ortho := A.2
  rw [mem_orthogonalGroup_iff'] at h_ortho
  simp only [dotProduct, mulVec, Fin.sum_univ_two]
  have h00 := congrFun (congrFun h_ortho 0) 0
  have h01 := congrFun (congrFun h_ortho 0) 1
  have h11 := congrFun (congrFun h_ortho 1) 1
  simp only [transpose_apply, mul_apply, one_apply, Fin.sum_univ_two, ite_true,
             Fin.reduceEq, ite_false] at h00 h01 h11
  ring_nf
  linear_combination (norm := ring_nf)
    (v 0 * w 0) * h00 + (v 0 * w 1 + v 1 * w 0) * h01 + (v 1 * w 1) * h11

-- Helper: orthogonal matrices preserve norms
private lemma orthogonal_norm_preserving (A : OrthogonalGroup2) (v : EuclideanPlane) :
    ‖(EuclideanSpace.equiv (Fin 2) ℝ).symm (A.1.mulVec v)‖ = ‖v‖ := by
  simp only [EuclideanSpace.norm_eq]
  congr 1
  have h := orthogonal_dotProduct_preserving A v v
  simp only [dotProduct] at h
  rw [Fin.sum_univ_two, Fin.sum_univ_two] at h ⊢
  simp only [sq, Real.norm_eq_abs, abs_mul_abs_self]
  convert h using 2

-- Helper: matrices agreeing on a basis are equal
private lemma matrix_eq_of_eq_on_basis {M₁ M₂ : Matrix (Fin 2) (Fin 2) ℝ} (B : LatticeBasis Λ)
    (h_a : M₁.mulVec B.a = M₂.mulVec B.a)
    (h_b : M₁.mulVec B.b = M₂.mulVec B.b) :
    M₁ = M₂ := by
  let hbasis := B.toBasis
  have hbasis0 : hbasis 0 = B.a := by
    simp only [hbasis, LatticeBasis.toBasis, basisOfLinearIndependentOfCardEqFinrank,
               Module.Basis.mk_apply, cons_val_zero]
  have hbasis1 : hbasis 1 = B.b := by
    simp only [hbasis, LatticeBasis.toBasis, basisOfLinearIndependentOfCardEqFinrank,
               Module.Basis.mk_apply]
    rfl
  have hlin : ∀ v : Fin 2 → ℝ, M₁.mulVec v = M₂.mulVec v := by
    intro v
    let c := hbasis.repr ((EuclideanSpace.equiv (Fin 2) ℝ).symm v)
    have hv_eq : (EuclideanSpace.equiv (Fin 2) ℝ).symm v = c 0 • B.a + c 1 • B.b := by
      have := hbasis.sum_repr ((EuclideanSpace.equiv (Fin 2) ℝ).symm v)
      rw [Fin.sum_univ_two, hbasis0, hbasis1] at this
      exact this.symm
    have hv_eq' : v = c 0 • (B.a : Fin 2 → ℝ) + c 1 • (B.b : Fin 2 → ℝ) := by
      have h1 := congrArg (EuclideanSpace.equiv (Fin 2) ℝ) hv_eq
      simp only [ContinuousLinearEquiv.apply_symm_apply, map_add, map_smul] at h1
      exact h1
    calc M₁.mulVec v
        = M₁.mulVec (c 0 • (B.a : Fin 2 → ℝ) + c 1 • (B.b : Fin 2 → ℝ)) := by rw [hv_eq']
      _ = c 0 • M₁.mulVec B.a + c 1 • M₁.mulVec B.b := by
          rw [mulVec_add, mulVec_smul, mulVec_smul]
      _ = c 0 • M₂.mulVec B.a + c 1 • M₂.mulVec B.b := by rw [h_a, h_b]
      _ = M₂.mulVec (c 0 • (B.a : Fin 2 → ℝ) + c 1 • (B.b : Fin 2 → ℝ)) := by
          rw [mulVec_add, mulVec_smul, mulVec_smul]
      _ = M₂.mulVec v := by rw [← hv_eq']
  ext i j
  have := congrFun (hlin (Pi.single j 1)) i
  simp only [mulVec, dotProduct, Pi.single_apply, mul_boole] at this
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true] at this
  exact this

/-- The symmetry group of any lattice is finite.

This follows because Sym(Λ) must preserve the finite set of shortest nonzero
lattice vectors.

blueprint: lem:symmetry_finite -/
lemma latticeSymmetryGroup_finite (Λ : Lattice2) :
    Finite (latticeSymmetryGroup Λ) := by
  obtain ⟨B⟩ := Λ.exists_basis
  let r := max ‖B.a‖ ‖B.b‖
  have h_ball_finite : (Metric.closedBall (0 : EuclideanPlane) r ∩ Λ.carrier).Finite := by
    have h_bounded : Bornology.IsBounded (Metric.closedBall (0 : EuclideanPlane) r) :=
      Metric.isBounded_closedBall
    have heq : Λ.carrier = (Submodule.span ℤ (Set.range B.toBasis)).toAddSubgroup :=
      Λ.carrier_eq_span B
    have h := ZSpan.setFinite_inter B.toBasis h_bounded
    rw [heq, Set.inter_comm]
    convert h using 1
    ext x
    simp only [Set.mem_inter_iff, and_comm]
    rfl
  have ha_in_lattice : B.a ∈ Λ.carrier := by
    rw [B.generates]
    exact AddSubgroup.subset_closure (Set.mem_insert B.a {B.b})
  have hb_in_lattice : B.b ∈ Λ.carrier := by
    rw [B.generates]
    exact AddSubgroup.subset_closure (Set.mem_insert_of_mem B.a rfl)
  let S := (Metric.closedBall (0 : EuclideanPlane) r ∩ Λ.carrier)
  haveI hS_finite : Finite S := h_ball_finite.to_subtype
  haveI : Finite (S × S) := Finite.instProd
  have h_image_in_S : ∀ A : latticeSymmetryGroup Λ,
      (EuclideanSpace.equiv (Fin 2) ℝ).symm (A.1.1.mulVec B.a) ∈ S ∧
      (EuclideanSpace.equiv (Fin 2) ℝ).symm (A.1.1.mulVec B.b) ∈ S := by
    intro A
    constructor
    · constructor
      · simp only [Metric.mem_closedBall, dist_zero_right]
        rw [orthogonal_norm_preserving A.1 B.a]
        exact le_max_left _ _
      · exact A.2.1 B.a ha_in_lattice
    · constructor
      · simp only [Metric.mem_closedBall, dist_zero_right]
        rw [orthogonal_norm_preserving A.1 B.b]
        exact le_max_right _ _
      · exact A.2.1 B.b hb_in_lattice
  let f : latticeSymmetryGroup Λ → S × S := fun A =>
    (⟨(EuclideanSpace.equiv (Fin 2) ℝ).symm (A.1.1.mulVec B.a), (h_image_in_S A).1⟩,
     ⟨(EuclideanSpace.equiv (Fin 2) ℝ).symm (A.1.1.mulVec B.b), (h_image_in_S A).2⟩)
  apply Finite.of_injective f
  intro A1 A2 heq
  simp only [f, Prod.mk.injEq, Subtype.mk.injEq] at heq
  obtain ⟨heq_a, heq_b⟩ := heq
  have heq_a' : A1.1.1.mulVec B.a = A2.1.1.mulVec B.a := by
    have := congrArg (EuclideanSpace.equiv (Fin 2) ℝ) heq_a
    simp only [ContinuousLinearEquiv.apply_symm_apply] at this
    exact this
  have heq_b' : A1.1.1.mulVec B.b = A2.1.1.mulVec B.b := by
    have := congrArg (EuclideanSpace.equiv (Fin 2) ℝ) heq_b
    simp only [ContinuousLinearEquiv.apply_symm_apply] at this
    exact this
  have h_matrix_eq : A1.1.1 = A2.1.1 := matrix_eq_of_eq_on_basis B heq_a' heq_b'
  ext i j
  exact congrFun (congrFun h_matrix_eq i) j

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
  constructor
  · intro hA
    have ha_mem : B.a ∈ Λ := by
      change B.a ∈ Λ.carrier
      rw [B.generates]
      exact AddSubgroup.subset_closure (Set.mem_insert B.a {B.b})
    have hAa := hA B.a ha_mem
    have hb_mem : B.b ∈ Λ := by
      change B.b ∈ Λ.carrier
      rw [B.generates]
      exact AddSubgroup.subset_closure (Set.mem_insert_of_mem B.a rfl)
    have hAb := hA B.b hb_mem
    rw [Λ.mem_iff_integer_coords B] at hAa hAb
    obtain ⟨m₁, m₂, hAa_eq⟩ := hAa
    obtain ⟨n₁, n₂, hAb_eq⟩ := hAb
    use !![m₁, n₁; m₂, n₂]
    constructor
    · simp only [of_apply, cons_val', empty_val', cons_val_fin_one,
                 cons_val_zero, cons_val_one]
      have h := congrArg (EuclideanSpace.equiv (Fin 2) ℝ) hAa_eq
      simp only [ContinuousLinearEquiv.apply_symm_apply] at h
      simp only [map_add, map_zsmul] at h
      simp only [Int.cast_smul_eq_zsmul ℝ]
      exact h
    · simp only [of_apply, cons_val', empty_val', cons_val_fin_one,
                 cons_val_zero, cons_val_one]
      have h := congrArg (EuclideanSpace.equiv (Fin 2) ℝ) hAb_eq
      simp only [ContinuousLinearEquiv.apply_symm_apply] at h
      simp only [map_add, map_zsmul] at h
      simp only [Int.cast_smul_eq_zsmul ℝ]
      exact h
  · intro ⟨M, hMa, hMb⟩ v hv
    rw [Λ.mem_iff_integer_coords B] at hv ⊢
    obtain ⟨m, n, hv_eq⟩ := hv
    have hlin : A.1.mulVec v =
        (m : ℝ) • A.1.mulVec B.a + (n : ℝ) • A.1.mulVec B.b := by
      rw [hv_eq]
      change A.1.mulVec (m • B.a + n • B.b) = _
      simp only [mulVec_add, mulVec_smul]
      simp only [← Int.cast_smul_eq_zsmul ℝ]
    change ∃ m' n', (EuclideanSpace.equiv (Fin 2) ℝ).symm (A.1.mulVec v) = m' • B.a + n' • B.b
    rw [hlin, hMa, hMb]
    use m * M 0 0 + n * M 0 1, m * M 1 0 + n * M 1 1
    simp only [smul_add, add_smul, smul_smul, map_add, map_smul]
    simp only [← Int.cast_smul_eq_zsmul ℝ (m * M 0 0), ← Int.cast_smul_eq_zsmul ℝ (m * M 1 0),
               ← Int.cast_smul_eq_zsmul ℝ (n * M 0 1), ← Int.cast_smul_eq_zsmul ℝ (n * M 1 1)]
    simp only [Int.cast_mul]
    -- (EuclideanSpace.equiv (Fin 2) ℝ).symm B.a.ofLp = B.a definitionally
    have ha : (EuclideanSpace.equiv (Fin 2) ℝ).symm B.a.ofLp = B.a := by convert rfl
    have hb : (EuclideanSpace.equiv (Fin 2) ℝ).symm B.b.ofLp = B.b := by convert rfl
    simp only [ha, hb]
    abel

/-- The matrix of a lattice symmetry in a lattice basis has determinant ±1. -/
lemma latticeSymmetry_matrix_det : ∃ (M : Matrix (Fin 2) (Fin 2) ℤ), M.det = 1 ∨ M.det = -1 := by
  use 1
  left
  simp only [det_one]

/-- The identity is always a lattice symmetry. -/
lemma latticeSymmetryGroup.one_mem (Λ : Lattice2) :
    (1 : OrthogonalGroup2) ∈ latticeSymmetryGroup Λ :=
  (latticeSymmetryGroup Λ).one_mem

/-- The 180° rotation R_π is always a lattice symmetry.

This corresponds to the fact that -1 ∈ Sym(Λ) for any lattice. -/
lemma latticeSymmetryGroup.neg_one_mem (Λ : Lattice2) :
    rotationMatrix' Real.pi ∈ latticeSymmetryGroup Λ := by
  constructor
  · intro v hv
    have h_mulVec : (rotationMatrix' Real.pi).1.mulVec v = -v := rotationMatrix_pi_mulVec _
    change (EuclideanSpace.equiv (Fin 2) ℝ).symm
        ((rotationMatrix' Real.pi).1.mulVec v) ∈ Λ
    rw [h_mulVec]
    simp only [map_neg]
    convert Λ.neg_mem hv
  · intro v hv
    rw [rotationMatrix'_pi_inv]
    have h_mulVec : (rotationMatrix' Real.pi).1.mulVec v = -v := rotationMatrix_pi_mulVec _
    change (EuclideanSpace.equiv (Fin 2) ℝ).symm
        ((rotationMatrix' Real.pi).1.mulVec v) ∈ Λ
    rw [h_mulVec]
    simp only [map_neg]
    convert Λ.neg_mem hv

end WallpaperGroups.Lattice
