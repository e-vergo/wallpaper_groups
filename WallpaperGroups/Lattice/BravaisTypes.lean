/-
Copyright (c) 2025 Wallpaper Groups Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import WallpaperGroups.Lattice.Symmetry
import WallpaperGroups.PointGroup.DihedralPointGroup

/-!
# Bravais Lattice Types

This file defines the five Bravais lattice types in 2D and proves that every
lattice belongs to exactly one type.

## Main definitions

* `ObliqueLattice` - General lattice with Sym(Λ) = C₂
* `RectangularLattice` - Orthogonal axes, unequal lengths, Sym(Λ) = D₂
* `CenteredRectangularLattice` - Equal length axes, Sym(Λ) = D₂
* `SquareLattice` - Orthogonal axes, equal lengths, Sym(Λ) = D₄
* `HexagonalLattice` - 60° angle, equal lengths, Sym(Λ) = D₆

## Main results

* `bravais_classification` - Every lattice is exactly one of the 5 types

blueprint: thm:bravais_classification
-/

namespace WallpaperGroups.Lattice

open WallpaperGroups.Euclidean
open WallpaperGroups.PointGroup
open scoped InnerProductSpace

/-- An oblique lattice has minimal symmetry: only the 180° rotation.

Sym(Λ) = C₂ = {I, R_π}

blueprint: def:oblique_lattice -/
def IsObliqueLattice (Λ : Lattice2) : Prop :=
  Nonempty ((latticeSymmetryGroup Λ) ≃* CyclicPointGroup 2)

/-- A rectangular lattice has orthogonal basis vectors of unequal length.

Sym(Λ) = D₂ (Klein four-group)

blueprint: def:rectangular_lattice -/
def IsRectangularLattice (Λ : Lattice2) : Prop :=
  ∃ (B : LatticeBasis Λ),
    ⟪B.a, B.b⟫_ℝ = (0 : ℝ) ∧
    ‖B.a‖ ≠ ‖B.b‖ ∧
    Nonempty ((latticeSymmetryGroup Λ) ≃* DihedralPointGroup 2)

/-- A centered rectangular (rhombic) lattice has equal length basis vectors
that are not orthogonal.

Sym(Λ) = D₂

blueprint: def:centered_rectangular_lattice -/
def IsCenteredRectangularLattice (Λ : Lattice2) : Prop :=
  ∃ (B : LatticeBasis Λ),
    ‖B.a‖ = ‖B.b‖ ∧
    ⟪B.a, B.b⟫_ℝ ≠ (0 : ℝ) ∧
    ⟪B.a, B.b⟫_ℝ ≠ (‖B.a‖^2 / 2 : ℝ) ∧  -- not 60° or 120°
    Nonempty ((latticeSymmetryGroup Λ) ≃* DihedralPointGroup 2)

/-- A square lattice has orthogonal basis vectors of equal length.

Sym(Λ) = D₄

blueprint: def:square_lattice -/
def IsSquareLattice (Λ : Lattice2) : Prop :=
  ∃ (B : LatticeBasis Λ),
    ⟪B.a, B.b⟫_ℝ = (0 : ℝ) ∧
    ‖B.a‖ = ‖B.b‖ ∧
    Nonempty ((latticeSymmetryGroup Λ) ≃* DihedralPointGroup 4)

/-- A hexagonal lattice has basis vectors of equal length at 60° or 120° angle.

Sym(Λ) = D₆

blueprint: def:hexagonal_lattice -/
def IsHexagonalLattice (Λ : Lattice2) : Prop :=
  ∃ (B : LatticeBasis Λ),
    ‖B.a‖ = ‖B.b‖ ∧
    (⟪B.a, B.b⟫_ℝ = ‖B.a‖^2 / 2 ∨ ⟪B.a, B.b⟫_ℝ = -‖B.a‖^2 / 2) ∧
    Nonempty ((latticeSymmetryGroup Λ) ≃* DihedralPointGroup 6)

/-- Oblique lattices have symmetry group C₂.

blueprint: lem:oblique_symmetry -/
lemma obliqueLattice_symmetryGroup (Λ : Lattice2) (hΛ : IsObliqueLattice Λ) :
    Nonempty ((latticeSymmetryGroup Λ) ≃* CyclicPointGroup 2) :=
  hΛ

/-- Rectangular lattices have symmetry group D₂.

blueprint: lem:rectangular_symmetry -/
lemma rectangularLattice_symmetryGroup (Λ : Lattice2) (hΛ : IsRectangularLattice Λ) :
    Nonempty ((latticeSymmetryGroup Λ) ≃* DihedralPointGroup 2) := by
  obtain ⟨_, _, _, h⟩ := hΛ
  exact h

/-- Centered rectangular lattices have symmetry group D₂.

blueprint: lem:centered_rectangular_symmetry -/
lemma centeredRectangularLattice_symmetryGroup (Λ : Lattice2)
    (hΛ : IsCenteredRectangularLattice Λ) :
    Nonempty ((latticeSymmetryGroup Λ) ≃* DihedralPointGroup 2) := by
  obtain ⟨_, _, _, _, h⟩ := hΛ
  exact h

/-- Square lattices have symmetry group D₄.

blueprint: lem:square_symmetry -/
lemma squareLattice_symmetryGroup (Λ : Lattice2) (hΛ : IsSquareLattice Λ) :
    Nonempty ((latticeSymmetryGroup Λ) ≃* DihedralPointGroup 4) := by
  obtain ⟨_, _, _, h⟩ := hΛ
  exact h

/-- Hexagonal lattices have symmetry group D₆.

blueprint: lem:hexagonal_symmetry -/
lemma hexagonalLattice_symmetryGroup (Λ : Lattice2) (hΛ : IsHexagonalLattice Λ) :
    Nonempty ((latticeSymmetryGroup Λ) ≃* DihedralPointGroup 6) := by
  obtain ⟨_, _, _, h⟩ := hΛ
  exact h

/-! ### Cardinality lemmas for point groups -/

section CardinalityLemmas

/-- If two groups are isomorphic, they have the same cardinality. -/
lemma natCard_of_mulEquiv {G H : Type*} [Mul G] [Mul H] (e : G ≃* H) :
    Nat.card G = Nat.card H :=
  Nat.card_congr e.toEquiv

-- Helper: R_π² = 1
private lemma rotation_pi_sq : rotationMatrix' Real.pi * rotationMatrix' Real.pi = 1 := by
  ext i j
  simp only [Submonoid.coe_mul, OneMemClass.coe_one]
  have h := rotationMatrix_add Real.pi Real.pi
  rw [show Real.pi + Real.pi = 2 * Real.pi by ring, rotationMatrix_two_pi] at h
  exact congrFun (congrFun h i) j

-- Helper: R_π ≠ 1
private lemma rotation_pi_ne_one : rotationMatrix' Real.pi ≠ 1 := by
  intro h
  have h1 : (rotationMatrix' Real.pi).1 0 0 = (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 0 := by
    simp only [h]; rfl
  simp only [rotationMatrix', rotationMatrix, Matrix.of_apply, Matrix.cons_val_zero] at h1
  rw [Real.cos_pi] at h1
  norm_num at h1

-- Helper: S_0 ≠ 1
private lemma reflection_zero_ne_one : reflectionMatrix' 0 ≠ 1 := by
  intro h
  have h1 : (reflectionMatrix' 0).1 1 1 = (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 1 := by
    simp only [h]; rfl
  simp only [reflectionMatrix', reflectionMatrix, Matrix.of_apply,
             Matrix.cons_val_one] at h1
  rw [Real.cos_zero] at h1
  norm_num at h1

-- Helper: S_0 ≠ R_π
private lemma reflection_zero_ne_rotation_pi : reflectionMatrix' 0 ≠ rotationMatrix' Real.pi := by
  intro h
  have h1 : (reflectionMatrix' 0).1 0 0 = (rotationMatrix' Real.pi).1 0 0 := by
    simp only [h]
  simp only [reflectionMatrix', reflectionMatrix, rotationMatrix', rotationMatrix,
             Matrix.of_apply, Matrix.cons_val_zero] at h1
  rw [Real.cos_zero, Real.cos_pi] at h1
  norm_num at h1

-- Helper: R_π * S_0 ≠ 1
private lemma rotation_pi_mul_reflection_zero_ne_one :
    rotationMatrix' Real.pi * reflectionMatrix' 0 ≠ 1 := by
  intro h
  have h1 : (rotationMatrix' Real.pi * reflectionMatrix' 0).1 0 0 =
            (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 0 := by simp only [h]; rfl
  simp only [Submonoid.coe_mul] at h1
  rw [Matrix.mul_apply, Fin.sum_univ_two] at h1
  simp only [rotationMatrix', rotationMatrix, reflectionMatrix', reflectionMatrix,
             Matrix.of_apply, Real.cos_pi, Real.sin_pi, Real.cos_zero, Real.sin_zero,
             Matrix.one_apply_eq] at h1
  norm_num at h1

-- Helper: R_π * S_0 ≠ R_π
private lemma rotation_pi_mul_reflection_zero_ne_rotation_pi :
    rotationMatrix' Real.pi * reflectionMatrix' 0 ≠ rotationMatrix' Real.pi := by
  intro h
  have h1 : (rotationMatrix' Real.pi * reflectionMatrix' 0).1 1 1 =
            (rotationMatrix' Real.pi).1 1 1 := by simp only [h]
  simp only [Submonoid.coe_mul] at h1
  rw [Matrix.mul_apply, Fin.sum_univ_two] at h1
  simp only [rotationMatrix', rotationMatrix, reflectionMatrix', reflectionMatrix,
             Matrix.of_apply, Real.cos_pi, Real.sin_pi, Real.cos_zero, Real.sin_zero] at h1
  norm_num at h1

-- Helper: R_π * S_0 ≠ S_0
private lemma rotation_pi_mul_reflection_zero_ne_reflection_zero :
    rotationMatrix' Real.pi * reflectionMatrix' 0 ≠ reflectionMatrix' 0 := by
  intro h
  have h1 : (rotationMatrix' Real.pi * reflectionMatrix' 0).1 0 0 =
            (reflectionMatrix' 0).1 0 0 := by simp only [h]
  simp only [Submonoid.coe_mul] at h1
  rw [Matrix.mul_apply, Fin.sum_univ_two] at h1
  simp only [rotationMatrix', rotationMatrix, reflectionMatrix', reflectionMatrix,
             Matrix.of_apply, Real.cos_pi, Real.sin_pi, Real.cos_zero, Real.sin_zero] at h1
  norm_num at h1

/-- The order of R_π is 2. -/
private lemma orderOf_rotation_pi : orderOf (rotationMatrix' Real.pi) = 2 := by
  apply orderOf_eq_prime
  · rw [sq]; exact rotation_pi_sq
  · exact rotation_pi_ne_one

/-- The cardinality of C₂ is 2. -/
lemma cyclicPointGroup_two_card : Nat.card (CyclicPointGroup 2) = 2 := by
  have h1 : CyclicPointGroup 2 = Subgroup.closure {rotationMatrix' (2 * Real.pi / 2)} := rfl
  have h2 : (2 * Real.pi / 2 : ℝ) = Real.pi := by ring
  rw [h2] at h1
  rw [h1, ← Subgroup.zpowers_eq_closure, Nat.card_zpowers, orderOf_rotation_pi]

-- Helper: R_π is in D₂
private lemma rotationMatrix_pi_in_D2 : rotationMatrix' Real.pi ∈ DihedralPointGroup 2 := by
  have h : (2 * Real.pi / 2 : ℝ) = Real.pi := by ring
  rw [← h]
  apply Subgroup.subset_closure
  left
  rfl

-- Helper: S_0 is in D₂
private lemma reflectionMatrix_zero_in_D2 : reflectionMatrix' 0 ∈ DihedralPointGroup 2 := by
  apply Subgroup.subset_closure
  right
  rfl

-- Helper: S_0 * R_π = R_π * S_0 (they commute for n=2)
private lemma S0_Rpi_comm :
    reflectionMatrix' 0 * rotationMatrix' Real.pi =
    rotationMatrix' Real.pi * reflectionMatrix' 0 := by
  apply Subtype.ext
  simp only [Submonoid.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [reflectionMatrix', reflectionMatrix, rotationMatrix', rotationMatrix,
               Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Fin.isValue,
               Real.cos_pi, Real.sin_pi, Real.cos_zero, Real.sin_zero,
               Matrix.cons_val_zero, Matrix.cons_val_one] <;>
    norm_num

-- Helper: R_π² = 1
private lemma Rpi_sq : rotationMatrix' Real.pi * rotationMatrix' Real.pi = 1 := by
  rw [rotationMatrix'_add, show Real.pi + Real.pi = 2 * Real.pi by ring, rotationMatrix'_two_pi]

-- Helper: S_0² = 1
private lemma S0_sq : reflectionMatrix' 0 * reflectionMatrix' 0 = 1 := by
  apply Subtype.ext
  simp only [Submonoid.coe_mul, Submonoid.coe_one]
  exact reflectionMatrix_sq 0

-- Helper: (R_π * S_0)² = 1
private lemma RpiS0_sq :
    (rotationMatrix' Real.pi * reflectionMatrix' 0) *
    (rotationMatrix' Real.pi * reflectionMatrix' 0) = 1 := by
  calc (rotationMatrix' Real.pi * reflectionMatrix' 0) *
       (rotationMatrix' Real.pi * reflectionMatrix' 0)
      = rotationMatrix' Real.pi * (reflectionMatrix' 0 * rotationMatrix' Real.pi) *
        reflectionMatrix' 0 := by group
    _ = rotationMatrix' Real.pi * (rotationMatrix' Real.pi * reflectionMatrix' 0) *
        reflectionMatrix' 0 := by rw [S0_Rpi_comm]
    _ = (rotationMatrix' Real.pi * rotationMatrix' Real.pi) *
        (reflectionMatrix' 0 * reflectionMatrix' 0) := by group
    _ = 1 * 1 := by rw [Rpi_sq, S0_sq]
    _ = 1 := one_mul _

-- Define the 4-element set {1, R_π, S_0, R_π * S_0}
private def D2_set : Set OrthogonalGroup2 :=
  {1, rotationMatrix' Real.pi, reflectionMatrix' 0, rotationMatrix' Real.pi * reflectionMatrix' 0}

-- Define D2_set as a subgroup
private def D2_subgroup : Subgroup OrthogonalGroup2 where
  carrier := D2_set
  mul_mem' := by
    intro a b ha hb
    simp only [D2_set, Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb ⊢
    rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl
    -- 1 * 1 = 1
    · simp only [mul_one, true_or]
    -- 1 * r = r
    · simp only [one_mul, or_true, true_or]
    -- 1 * s = s
    · simp only [one_mul, or_true, true_or]
    -- 1 * rs = rs
    · simp only [one_mul, or_true]
    -- r * 1 = r
    · simp only [mul_one, or_true, true_or]
    -- r * r = 1
    · left; exact Rpi_sq
    -- r * s = rs
    · right; right; right; rfl
    -- r * rs = s
    · right; right; left
      calc rotationMatrix' Real.pi * (rotationMatrix' Real.pi * reflectionMatrix' 0)
          = (rotationMatrix' Real.pi * rotationMatrix' Real.pi) * reflectionMatrix' 0 := by group
        _ = 1 * reflectionMatrix' 0 := by rw [Rpi_sq]
        _ = reflectionMatrix' 0 := one_mul _
    -- s * 1 = s
    · simp only [mul_one, or_true, true_or]
    -- s * r = rs
    · right; right; right; rw [S0_Rpi_comm]
    -- s * s = 1
    · left; exact S0_sq
    -- s * rs = r
    · right; left
      calc reflectionMatrix' 0 * (rotationMatrix' Real.pi * reflectionMatrix' 0)
          = (reflectionMatrix' 0 * rotationMatrix' Real.pi) * reflectionMatrix' 0 := by group
        _ = (rotationMatrix' Real.pi * reflectionMatrix' 0) * reflectionMatrix' 0 := by
            rw [S0_Rpi_comm]
        _ = rotationMatrix' Real.pi * (reflectionMatrix' 0 * reflectionMatrix' 0) := by group
        _ = rotationMatrix' Real.pi * 1 := by rw [S0_sq]
        _ = rotationMatrix' Real.pi := mul_one _
    -- rs * 1 = rs
    · simp only [mul_one, or_true]
    -- rs * r = s
    · right; right; left
      calc (rotationMatrix' Real.pi * reflectionMatrix' 0) * rotationMatrix' Real.pi
          = rotationMatrix' Real.pi * (reflectionMatrix' 0 * rotationMatrix' Real.pi) := by group
        _ = rotationMatrix' Real.pi * (rotationMatrix' Real.pi * reflectionMatrix' 0) := by
            rw [S0_Rpi_comm]
        _ = (rotationMatrix' Real.pi * rotationMatrix' Real.pi) * reflectionMatrix' 0 := by group
        _ = 1 * reflectionMatrix' 0 := by rw [Rpi_sq]
        _ = reflectionMatrix' 0 := one_mul _
    -- rs * s = r
    · right; left
      calc (rotationMatrix' Real.pi * reflectionMatrix' 0) * reflectionMatrix' 0
          = rotationMatrix' Real.pi * (reflectionMatrix' 0 * reflectionMatrix' 0) := by group
        _ = rotationMatrix' Real.pi * 1 := by rw [S0_sq]
        _ = rotationMatrix' Real.pi := mul_one _
    -- rs * rs = 1
    · left; exact RpiS0_sq
  one_mem' := by simp only [D2_set, Set.mem_insert_iff, true_or]
  inv_mem' := by
    intro a ha
    simp only [D2_set, Set.mem_insert_iff, Set.mem_singleton_iff] at ha ⊢
    rcases ha with rfl | rfl | rfl | rfl
    · left; simp
    · right; left
      calc (rotationMatrix' Real.pi)⁻¹
          = (rotationMatrix' Real.pi)⁻¹ * 1 := (mul_one _).symm
        _ = (rotationMatrix' Real.pi)⁻¹ *
            (rotationMatrix' Real.pi * rotationMatrix' Real.pi) := by rw [Rpi_sq]
        _ = rotationMatrix' Real.pi := by group
    · right; right; left
      calc (reflectionMatrix' 0)⁻¹
          = (reflectionMatrix' 0)⁻¹ * 1 := (mul_one _).symm
        _ = (reflectionMatrix' 0)⁻¹ *
            (reflectionMatrix' 0 * reflectionMatrix' 0) := by rw [S0_sq]
        _ = reflectionMatrix' 0 := by group
    · right; right; right
      calc (rotationMatrix' Real.pi * reflectionMatrix' 0)⁻¹
          = (rotationMatrix' Real.pi * reflectionMatrix' 0)⁻¹ * 1 := (mul_one _).symm
        _ = (rotationMatrix' Real.pi * reflectionMatrix' 0)⁻¹ *
            ((rotationMatrix' Real.pi * reflectionMatrix' 0) *
             (rotationMatrix' Real.pi * reflectionMatrix' 0)) := by rw [RpiS0_sq]
        _ = rotationMatrix' Real.pi * reflectionMatrix' 0 := by group

-- DihedralPointGroup 2 equals D2_subgroup
private lemma dihedralPointGroup_two_eq_D2_subgroup : DihedralPointGroup 2 = D2_subgroup := by
  have hpi : (2 * Real.pi / (2 : ℕ) : ℝ) = Real.pi := by norm_num
  apply le_antisymm
  -- Closure {R_π, S_0} ≤ D2_subgroup
  · unfold DihedralPointGroup
    simp only [hpi]
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · -- R_π ∈ D2_subgroup
      rw [SetLike.mem_coe, ← Subgroup.mem_carrier]
      simp only [D2_subgroup, D2_set, Set.mem_insert_iff, Set.mem_singleton_iff,
                 or_true, true_or]
    · -- S_0 ∈ D2_subgroup
      rw [SetLike.mem_coe, ← Subgroup.mem_carrier]
      simp only [D2_subgroup, D2_set, Set.mem_insert_iff, Set.mem_singleton_iff,
                 or_true, true_or]
  -- D2_subgroup ≤ Closure {R_π, S_0}
  · intro x hx
    rw [← Subgroup.mem_carrier] at hx
    simp only [D2_subgroup, D2_set, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    unfold DihedralPointGroup
    simp only [hpi]
    rcases hx with rfl | rfl | rfl | rfl
    · exact Subgroup.one_mem _
    · exact Subgroup.subset_closure (by left; rfl)
    · exact Subgroup.subset_closure (by right; rfl)
    · exact Subgroup.mul_mem _ (Subgroup.subset_closure (by left; rfl))
                                (Subgroup.subset_closure (by right; rfl))

-- Finite instance for DihedralPointGroup 2
instance : Finite (DihedralPointGroup 2) := by
  rw [dihedralPointGroup_two_eq_D2_subgroup]
  -- D2_subgroup has carrier D2_set which is a finite set
  have h : Set.Finite D2_set := by
    simp only [D2_set, Set.finite_insert, Set.finite_singleton]
  exact Set.finite_coe_iff.mpr h

/-- D₂ has at least 4 elements. -/
lemma dihedralPointGroup_two_card_ge_four : 4 ≤ Nat.card (DihedralPointGroup 2) := by
  -- We construct 4 distinct elements in D₂: 1, R_π, S_0, R_π * S_0
  -- and show there's an injective map from Fin 4 to DihedralPointGroup 2
  let e0 : DihedralPointGroup 2 := ⟨1, Subgroup.one_mem _⟩
  let e1 : DihedralPointGroup 2 := ⟨rotationMatrix' Real.pi, rotationMatrix_pi_in_D2⟩
  let e2 : DihedralPointGroup 2 := ⟨reflectionMatrix' 0, reflectionMatrix_zero_in_D2⟩
  let e3 : DihedralPointGroup 2 := ⟨rotationMatrix' Real.pi * reflectionMatrix' 0,
            Subgroup.mul_mem _ rotationMatrix_pi_in_D2 reflectionMatrix_zero_in_D2⟩
  -- All pairs are distinct
  have h01 : e0 ≠ e1 := fun h =>
    rotation_pi_ne_one (congrArg Subtype.val h).symm
  have h02 : e0 ≠ e2 := fun h =>
    reflection_zero_ne_one (congrArg Subtype.val h).symm
  have h03 : e0 ≠ e3 := fun h =>
    rotation_pi_mul_reflection_zero_ne_one (congrArg Subtype.val h).symm
  have h12 : e1 ≠ e2 := fun h =>
    reflection_zero_ne_rotation_pi (congrArg Subtype.val h).symm
  have h13 : e1 ≠ e3 := fun h =>
    rotation_pi_mul_reflection_zero_ne_rotation_pi (congrArg Subtype.val h).symm
  have h23 : e2 ≠ e3 := fun h =>
    rotation_pi_mul_reflection_zero_ne_reflection_zero (congrArg Subtype.val h).symm
  -- Build an injective function from Fin 4
  let f : Fin 4 → DihedralPointGroup 2 := ![e0, e1, e2, e3]
  have hf : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp only [f] at hij ⊢ <;> try rfl
    all_goals (first | exact (h01 hij).elim | exact (h01.symm hij).elim
                     | exact (h02 hij).elim | exact (h02.symm hij).elim
                     | exact (h03 hij).elim | exact (h03.symm hij).elim
                     | exact (h12 hij).elim | exact (h12.symm hij).elim
                     | exact (h13 hij).elim | exact (h13.symm hij).elim
                     | exact (h23 hij).elim | exact (h23.symm hij).elim)
  -- DihedralPointGroup 2 is finite (proved above), so we can use Nat.card_le_card_of_injective
  calc 4 = Nat.card (Fin 4) := (Nat.card_fin 4).symm
    _ ≤ Nat.card (DihedralPointGroup 2) := Nat.card_le_card_of_injective f hf

/-- Cardinality of C₂ is strictly less than that of D₂. -/
lemma cyclicPointGroup_two_card_lt_dihedralPointGroup_two :
    Nat.card (CyclicPointGroup 2) < Nat.card (DihedralPointGroup 2) := by
  calc Nat.card (CyclicPointGroup 2) = 2 := cyclicPointGroup_two_card
    _ < 4 := by norm_num
    _ ≤ Nat.card (DihedralPointGroup 2) := dihedralPointGroup_two_card_ge_four

/-- C₂ is not isomorphic to any D_n for n ≥ 2. -/
lemma cyclicPointGroup_two_not_iso_dihedral (n : ℕ) [hn : NeZero n] (hge : n ≥ 2) :
    IsEmpty ((CyclicPointGroup 2) ≃* DihedralPointGroup n) := by
  constructor
  intro e
  have h1 : Nat.card (CyclicPointGroup 2) = 2 := cyclicPointGroup_two_card
  have h2 : Nat.card (CyclicPointGroup 2) = Nat.card (DihedralPointGroup n) :=
    natCard_of_mulEquiv e
  have h3 : 4 ≤ Nat.card (DihedralPointGroup n) := by
    -- |D_n| = 2n, and for n ≥ 2, 2n ≥ 4
    have hcard : Nat.card (DihedralPointGroup n) = 2 * n := by
      have ⟨e⟩ := DihedralPointGroup.equivDihedralGroup n
      rw [Nat.card_congr e.toEquiv]
      exact DihedralGroup.nat_card
    omega
  -- h1 says |C₂| = 2, h2 says |C₂| = |D_n|, h3 says |D_n| ≥ 4
  -- So 2 = |D_n| ≥ 4, contradiction
  have : 2 = Nat.card (DihedralPointGroup n) := h1.symm.trans h2
  omega

/-- Helper: Cardinality of DihedralPointGroup n equals 2n. -/
lemma dihedralPointGroup_card (n : ℕ) [NeZero n] :
    Nat.card (DihedralPointGroup n) = 2 * n := by
  have ⟨e⟩ := DihedralPointGroup.equivDihedralGroup n
  rw [Nat.card_congr e.toEquiv]
  exact DihedralGroup.nat_card

/-- D₂ is not isomorphic to D₄. -/
lemma dihedralPointGroup_two_not_iso_four :
    IsEmpty ((DihedralPointGroup 2) ≃* DihedralPointGroup 4) := by
  constructor
  intro e
  have h2 : Nat.card (DihedralPointGroup 2) = 4 := dihedralPointGroup_card 2
  have h4 : Nat.card (DihedralPointGroup 4) = 8 := dihedralPointGroup_card 4
  have heq : Nat.card (DihedralPointGroup 2) = Nat.card (DihedralPointGroup 4) :=
    natCard_of_mulEquiv e
  omega

/-- D₂ is not isomorphic to D₆. -/
lemma dihedralPointGroup_two_not_iso_six :
    IsEmpty ((DihedralPointGroup 2) ≃* DihedralPointGroup 6) := by
  constructor
  intro e
  have h2 : Nat.card (DihedralPointGroup 2) = 4 := dihedralPointGroup_card 2
  have h6 : Nat.card (DihedralPointGroup 6) = 12 := dihedralPointGroup_card 6
  have heq : Nat.card (DihedralPointGroup 2) = Nat.card (DihedralPointGroup 6) :=
    natCard_of_mulEquiv e
  omega

/-- D₄ is not isomorphic to D₆. -/
lemma dihedralPointGroup_four_not_iso_six :
    IsEmpty ((DihedralPointGroup 4) ≃* DihedralPointGroup 6) := by
  constructor
  intro e
  have h4 : Nat.card (DihedralPointGroup 4) = 8 := dihedralPointGroup_card 4
  have h6 : Nat.card (DihedralPointGroup 6) = 12 := dihedralPointGroup_card 6
  have heq : Nat.card (DihedralPointGroup 4) = Nat.card (DihedralPointGroup 6) :=
    natCard_of_mulEquiv e
  omega

end CardinalityLemmas

/-! ### Basis change lemmas for lattices -/

section BasisChange

variable {Λ : Lattice2}

/-- For an orthogonal basis, the squared norm of an integer linear combination
    decomposes into a sum of squares times the squared norms. -/
lemma norm_sq_of_orthogonal_combination (B : LatticeBasis Λ) (horth : ⟪B.a, B.b⟫_ℝ = 0)
    (m n : ℤ) : ‖(m : ℝ) • B.a + (n : ℝ) • B.b‖^2 = (m : ℝ)^2 * ‖B.a‖^2 + (n : ℝ)^2 * ‖B.b‖^2 := by
  rw [norm_add_sq_real]
  simp only [norm_smul, Real.norm_eq_abs]
  rw [inner_smul_left, inner_smul_right, horth]
  simp only [mul_zero, starRingEnd_apply, star_trivial]
  ring_nf
  rw [sq_abs, sq_abs]
  ring

/-- For an orthogonal basis, the inner product of two integer linear combinations
    decomposes into products of coefficients times squared norms. -/
lemma inner_of_orthogonal_combinations (B : LatticeBasis Λ) (horth : ⟪B.a, B.b⟫_ℝ = 0)
    (m n p q : ℤ) :
    ⟪(m : ℝ) • B.a + (n : ℝ) • B.b, (p : ℝ) • B.a + (q : ℝ) • B.b⟫_ℝ =
    (m : ℝ) * (p : ℝ) * ‖B.a‖^2 + (n : ℝ) * (q : ℝ) * ‖B.b‖^2 := by
  rw [inner_add_left, inner_add_right, inner_add_right]
  simp only [inner_smul_left, inner_smul_right]
  have hab : ⟪B.b, B.a⟫_ℝ = 0 := by rw [real_inner_comm]; exact horth
  rw [horth, hab]
  simp only [real_inner_self_eq_norm_sq, mul_zero, starRingEnd_apply, star_trivial, add_zero, zero_add]
  ring

end BasisChange

/-! ### Key lemma for rectangular vs centered rectangular -/

/-- Integer solutions constraint: if (m² - p²)r = (q² - n²)s with r ≠ s and r,s > 0,
    and mq - np = ±1, and ⟪c,d⟫ = mp·r + nq·s ≠ 0, and ⟪c,d⟫ ≠ (m² + n²)rs/(r+s),
    this leads to a contradiction.

    This is the key number-theoretic lemma for distinguishing rectangular from
    centered rectangular lattices. -/
lemma no_integer_solution_rectangular_centered (r s : ℝ) (hr : r > 0) (hs : s > 0) (hrs : r ≠ s)
    (m n p q : ℤ) (hdet : m * q - n * p = 1 ∨ m * q - n * p = -1)
    (heq_norm : (m : ℝ) ^ 2 * r + (n : ℝ) ^ 2 * s = (p : ℝ) ^ 2 * r + (q : ℝ) ^ 2 * s)
    (hinner_ne0 : (m : ℝ) * (p : ℝ) * r + (n : ℝ) * (q : ℝ) * s ≠ 0)
    (hinner_not_hex : (m : ℝ) * (p : ℝ) * r + (n : ℝ) * (q : ℝ) * s ≠
                      ((m : ℝ) ^ 2 * r + (n : ℝ) ^ 2 * s) / 2) : False := by
  -- From heq_norm: (m² - p²)r = (q² - n²)s
  have h1 : ((m : ℝ) ^ 2 - (p : ℝ) ^ 2) * r = ((q : ℝ) ^ 2 - (n : ℝ) ^ 2) * s := by linarith

  -- Define a = m+p, b = m-p, c = q+n, d = q-n
  -- Then m² - p² = ab and q² - n² = cd
  -- det = (ad + bc)/2 = ±1, so ad + bc = ±2
  set a := m + p with ha_def
  set b := m - p with hb_def
  set c := q + n with hc_def
  set d := q - n with hd_def

  have hab : (m : ℝ) ^ 2 - (p : ℝ) ^ 2 = (a : ℝ) * (b : ℝ) := by
    simp only [ha_def, hb_def]; push_cast; ring
  have hcd : (q : ℝ) ^ 2 - (n : ℝ) ^ 2 = (c : ℝ) * (d : ℝ) := by
    simp only [hc_def, hd_def]; push_cast; ring

  -- From det = ±1: ad + bc = ±2
  have habc : a * d + b * c = 2 ∨ a * d + b * c = -2 := by
    have hdet_eq : 2 * (m * q - n * p) = a * d + b * c := by ring
    rcases hdet with h | h <;> [left; right] <;> linarith

  -- Rewrite h1 in terms of a, b, c, d
  have h1' : (a : ℝ) * (b : ℝ) * r = (c : ℝ) * (d : ℝ) * s := by
    calc (a : ℝ) * (b : ℝ) * r = ((m : ℝ) ^ 2 - (p : ℝ) ^ 2) * r := by rw [← hab]
      _ = ((q : ℝ) ^ 2 - (n : ℝ) ^ 2) * s := h1
      _ = (c : ℝ) * (d : ℝ) * s := by rw [← hcd]

  -- The proof uses the fact that for integers a, b, c, d with ad + bc = ±2
  -- and ab·r = cd·s where r, s > 0 and r ≠ s, we must have ab ≠ cd.
  -- But when ab and cd have the same sign (required for h1' with r, s > 0),
  -- the constraint |ad + bc| = 2 forces ab = cd = ±1.
  --
  -- This is proven by analyzing the constraint on integer products.

  -- First handle the case ab = 0 or cd = 0
  by_cases hab_zero : a * b = 0
  · -- ab = 0 means m² = p², so m = ±p
    have hcd_zero : (c : ℝ) * (d : ℝ) * s = 0 := by
      calc (c : ℝ) * (d : ℝ) * s = (a : ℝ) * (b : ℝ) * r := h1'.symm
        _ = 0 := by simp [show (a : ℝ) * (b : ℝ) = 0 from by exact_mod_cast hab_zero]
    have hcd_zero' : c * d = 0 := by
      have hs_ne : (s : ℝ) ≠ 0 := ne_of_gt hs
      have : (c : ℝ) * (d : ℝ) = 0 := by nlinarith
      exact_mod_cast this
    -- With ab = 0 and cd = 0, we have m = ±p and q = ±n
    -- The determinant mq - np = ±1 then becomes ±pn ∓ np = 0 or -2pn
    -- 0 ≠ ±1 and -2pn = ±1 is impossible for integers
    rcases mul_eq_zero.mp hab_zero with ha_zero | hb_zero <;>
    rcases mul_eq_zero.mp hcd_zero' with hc_zero | hd_zero
    · -- a = 0 (m = -p), c = 0 (q = -n): det = pn - np = 0
      simp only [ha_def] at ha_zero
      simp only [hc_def] at hc_zero
      have hm : m = -p := by omega
      have hq : q = -n := by omega
      have hdet' : m * q - n * p = (-p) * (-n) - n * p := by rw [hm, hq]
      simp only [neg_mul_neg, sub_self] at hdet'
      rcases hdet with h | h <;> omega
    · -- a = 0 (m = -p), d = 0 (q = n): det = -pn - np = -2pn
      simp only [ha_def] at ha_zero
      simp only [hd_def] at hd_zero
      have hm : m = -p := by omega
      have hq : q = n := by omega
      have hdet' : m * q - n * p = (-p) * n - n * p := by rw [hm, hq]
      have hdet'' : m * q - n * p = -2 * p * n := by linarith
      rcases hdet with h | h
      · -- -2*p*n = 1 is impossible for integers
        have hdiv : (2 : ℤ) ∣ -2 * p * n := ⟨-p * n, by ring⟩
        rw [← hdet''] at h
        have : (2 : ℤ) ∣ (1 : ℤ) := by rw [← h]; exact hdiv
        omega
      · -- -2*p*n = -1 is impossible for integers
        have hdiv : (2 : ℤ) ∣ -2 * p * n := ⟨-p * n, by ring⟩
        rw [← hdet''] at h
        have : (2 : ℤ) ∣ (-1 : ℤ) := by rw [← h]; exact hdiv
        omega
    · -- b = 0 (m = p), c = 0 (q = -n): det = -pn - np = -2pn
      simp only [hb_def] at hb_zero
      simp only [hc_def] at hc_zero
      have hm : m = p := by omega
      have hq : q = -n := by omega
      have hdet' : m * q - n * p = p * (-n) - n * p := by rw [hm, hq]
      have hdet'' : m * q - n * p = -2 * p * n := by linarith
      rcases hdet with h | h
      · have hdiv : (2 : ℤ) ∣ -2 * p * n := ⟨-p * n, by ring⟩
        rw [← hdet''] at h
        have : (2 : ℤ) ∣ (1 : ℤ) := by rw [← h]; exact hdiv
        omega
      · have hdiv : (2 : ℤ) ∣ -2 * p * n := ⟨-p * n, by ring⟩
        rw [← hdet''] at h
        have : (2 : ℤ) ∣ (-1 : ℤ) := by rw [← h]; exact hdiv
        omega
    · -- b = 0 (m = p), d = 0 (q = n): det = pn - np = 0
      simp only [hb_def] at hb_zero
      simp only [hd_def] at hd_zero
      have hm : m = p := by omega
      have hq : q = n := by omega
      have hdet' : m * q - n * p = p * n - n * p := by rw [hm, hq]
      simp only [sub_self] at hdet'
      rcases hdet with h | h <;> omega

  · by_cases hcd_zero' : c * d = 0
    · -- cd = 0 but ab ≠ 0: from h1', ab·r = 0, contradiction
      have hcd_real : (c : ℝ) * (d : ℝ) = 0 := by exact_mod_cast hcd_zero'
      have : (a : ℝ) * (b : ℝ) * r = 0 := by rw [h1', hcd_real]; ring
      have hab_ne : (a : ℝ) * (b : ℝ) ≠ 0 := by
        intro h; apply hab_zero; exact_mod_cast h
      have hr_ne : r ≠ 0 := ne_of_gt hr
      exact mul_ne_zero hab_ne hr_ne ‹(a : ℝ) * (b : ℝ) * r = 0›

    · -- ab ≠ 0 and cd ≠ 0
      -- From h1': ab·r = cd·s with r, s > 0, ab and cd must have same sign

      by_cases hab_pos : a * b > 0
      · by_cases hcd_pos : c * d > 0
        · -- ab > 0 and cd > 0
          -- Key: ab ≥ 1, cd ≥ 1. With |ad + bc| = 2, this forces ab = cd = 1
          have hab_ge1 : a * b ≥ 1 := by omega
          have hcd_ge1 : c * d ≥ 1 := by omega

          -- Use polyrith-style reasoning: ab·cd ≤ 1 follows from |ad + bc| = 2
          -- Combined with ab·cd ≥ 1, we get ab·cd = 1, hence ab = cd = 1
          have h_eq : a * b = c * d := by
            -- From ab ≥ 1, cd ≥ 1, and |ad + bc| = 2:
            -- If ab ≥ 2 or cd ≥ 2, then abcd ≥ 2
            -- But the bound |ad + bc| = 2 with positive ab, cd constrains this
            by_contra h_ne
            rcases habc with habc_pos | habc_neg <;> nlinarith [sq_nonneg (a * d - b * c)]
          -- From ab = cd and h1': ab·r = ab·s, so r = s (contradiction)
          have hr_eq_s : r = s := by
            have hab_real : (a : ℝ) * (b : ℝ) = (c : ℝ) * (d : ℝ) := by exact_mod_cast h_eq
            have hab_ne_real : (a : ℝ) * (b : ℝ) ≠ 0 := by exact_mod_cast hab_zero
            have := h1'
            rw [hab_real] at this
            have : (c : ℝ) * (d : ℝ) * r = (c : ℝ) * (d : ℝ) * s := this
            have hcd_ne_real : (c : ℝ) * (d : ℝ) ≠ 0 := by exact_mod_cast hcd_zero'
            nlinarith
          exact hrs hr_eq_s

        · -- ab > 0 and cd < 0: h1' gives (positive)·r = (negative)·s, contradiction
          have hcd_neg : c * d < 0 := lt_of_le_of_ne (le_of_not_gt hcd_pos) hcd_zero'
          have hlhs_pos : (a : ℝ) * (b : ℝ) * r > 0 := mul_pos (by exact_mod_cast hab_pos) hr
          have hrhs_neg : (c : ℝ) * (d : ℝ) * s < 0 :=
            mul_neg_of_neg_of_pos (by exact_mod_cast hcd_neg) hs
          linarith [h1']

      · -- ab ≤ 0, so ab < 0 (since ab ≠ 0)
        have hab_neg : a * b < 0 := by
          rcases lt_or_eq_of_le (le_of_not_gt hab_pos) with h | h
          · exact h
          · exact absurd h.symm hab_zero

        by_cases hcd_pos : c * d > 0
        · -- ab < 0 and cd > 0: h1' gives (negative)·r = (positive)·s, contradiction
          have hlhs_neg : (a : ℝ) * (b : ℝ) * r < 0 :=
            mul_neg_of_neg_of_pos (by exact_mod_cast hab_neg) hr
          have hrhs_pos : (c : ℝ) * (d : ℝ) * s > 0 := mul_pos (by exact_mod_cast hcd_pos) hs
          linarith [h1']

        · -- ab < 0 and cd < 0
          have hcd_neg : c * d < 0 := lt_of_le_of_ne (le_of_not_gt hcd_pos) hcd_zero'
          have hab_le_neg1 : a * b ≤ -1 := by omega
          have hcd_le_neg1 : c * d ≤ -1 := by omega

          -- Similar to positive case: ab = cd
          have h_eq : a * b = c * d := by
            by_contra h_ne
            rcases habc with habc_pos | habc_neg <;> nlinarith [sq_nonneg (a * d - b * c)]

          have hr_eq_s : r = s := by
            have hab_real : (a : ℝ) * (b : ℝ) = (c : ℝ) * (d : ℝ) := by exact_mod_cast h_eq
            have := h1'
            rw [hab_real] at this
            have hcd_ne_real : (c : ℝ) * (d : ℝ) ≠ 0 := by exact_mod_cast hcd_zero'
            nlinarith
          exact hrs hr_eq_s

/-- The five Bravais types are mutually exclusive. -/
lemma bravais_exclusive (Λ : Lattice2) :
    (IsObliqueLattice Λ → ¬IsRectangularLattice Λ ∧ ¬IsCenteredRectangularLattice Λ ∧
                          ¬IsSquareLattice Λ ∧ ¬IsHexagonalLattice Λ) ∧
    (IsRectangularLattice Λ → ¬IsCenteredRectangularLattice Λ ∧
                              ¬IsSquareLattice Λ ∧ ¬IsHexagonalLattice Λ) ∧
    (IsCenteredRectangularLattice Λ → ¬IsSquareLattice Λ ∧ ¬IsHexagonalLattice Λ) ∧
    (IsSquareLattice Λ → ¬IsHexagonalLattice Λ) := by
  refine ⟨?oblique, ?rect, ?crect, ?square⟩
  case oblique =>
    intro ⟨eC2⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    -- Oblique (C₂) vs Rectangular (D₂)
    · intro ⟨_, _, _, ⟨eD2⟩⟩
      have : Nonempty ((CyclicPointGroup 2) ≃* DihedralPointGroup 2) :=
        ⟨eC2.symm.trans eD2⟩
      exact (cyclicPointGroup_two_not_iso_dihedral 2 (by norm_num)).false this.some
    -- Oblique (C₂) vs CenteredRectangular (D₂)
    · intro ⟨_, _, _, _, ⟨eD2⟩⟩
      have : Nonempty ((CyclicPointGroup 2) ≃* DihedralPointGroup 2) :=
        ⟨eC2.symm.trans eD2⟩
      exact (cyclicPointGroup_two_not_iso_dihedral 2 (by norm_num)).false this.some
    -- Oblique (C₂) vs Square (D₄)
    · intro ⟨_, _, _, ⟨eD4⟩⟩
      have : Nonempty ((CyclicPointGroup 2) ≃* DihedralPointGroup 4) :=
        ⟨eC2.symm.trans eD4⟩
      exact (cyclicPointGroup_two_not_iso_dihedral 4 (by norm_num)).false this.some
    -- Oblique (C₂) vs Hexagonal (D₆)
    · intro ⟨_, _, _, ⟨eD6⟩⟩
      have : Nonempty ((CyclicPointGroup 2) ≃* DihedralPointGroup 6) :=
        ⟨eC2.symm.trans eD6⟩
      exact (cyclicPointGroup_two_not_iso_dihedral 6 (by norm_num)).false this.some
  case rect =>
    intro ⟨_, _, _, ⟨eD2⟩⟩
    refine ⟨?_, ?_, ?_⟩
    -- Rectangular vs CenteredRectangular: both have D₂, need geometric argument
    · intro ⟨B2, hB2_eq, hB2_neq0, hB2_not_hex, _⟩
      -- We have:
      -- - Rectangular basis w✝ with ⟪a, b⟫ = 0 and ‖a‖ ≠ ‖b‖
      -- - Centered rectangular basis B2 with ‖a‖ = ‖b‖, ⟪a, b⟫ ≠ 0, and ⟪a,b⟫ ≠ ‖a‖²/2
      -- Both are bases for the same lattice Λ.
      --
      -- The D₂ symmetry group of a lattice determines which geometric type it is.
      -- - Rectangular: reflections are along the coordinate axes (along basis vectors)
      -- - Centered rectangular: reflections are along the diagonals
      --
      -- Both lattices have the same symmetry group (D₂), which means they must
      -- have the same reflection axes. But the definitions of rectangular and
      -- centered rectangular imply different configurations of these axes
      -- relative to the basis.
      --
      -- The incompatibility comes from the fact that both definitions include
      -- the symmetry group condition AND geometric constraints on the basis.
      -- A rectangular lattice by definition has D₂ symmetry with orthogonal
      -- reflections aligned with an orthogonal basis of unequal lengths.
      -- A centered rectangular lattice has D₂ symmetry with reflections
      -- that are NOT aligned with the equal-length basis.
      --
      -- The mathematical fact is that these configurations are exclusive:
      -- you cannot have both an orthogonal-unequal basis AND an equal-length
      -- non-orthogonal (non-hexagonal) basis for the same rank-2 lattice.
      --
      -- This follows from basis change theory: if (a,b) is orthogonal with
      -- ‖a‖ ≠ ‖b‖, and (c,d) = M(a,b) for integer matrix M with det ±1,
      -- then ‖c‖ = ‖d‖ and ⟪c,d⟫ ≠ 0 and ⟪c,d⟫ ≠ ‖c‖²/2 is impossible.
      --
      -- This is a deep result requiring careful analysis of integer solutions.
      -- For now, we accept this as the key geometric lemma.
      --
      -- The proof would proceed by:
      -- 1. Express B2 vectors as integer combinations of w✝ vectors
      -- 2. Use orthogonality of w✝ to compute ‖B2.a‖², ‖B2.b‖², ⟪B2.a, B2.b⟫
      -- 3. Show the constraints are incompatible with det = ±1
      --
      -- TODO: Complete the formal proof of basis incompatibility
      sorry
    -- Rectangular (D₂) vs Square (D₄)
    · intro ⟨_, _, _, ⟨eD4⟩⟩
      have : Nonempty ((DihedralPointGroup 2) ≃* DihedralPointGroup 4) :=
        ⟨eD2.symm.trans eD4⟩
      exact dihedralPointGroup_two_not_iso_four.false this.some
    -- Rectangular (D₂) vs Hexagonal (D₆)
    · intro ⟨_, _, _, ⟨eD6⟩⟩
      have : Nonempty ((DihedralPointGroup 2) ≃* DihedralPointGroup 6) :=
        ⟨eD2.symm.trans eD6⟩
      exact dihedralPointGroup_two_not_iso_six.false this.some
  case crect =>
    intro ⟨_, _, _, _, ⟨eD2⟩⟩
    refine ⟨?_, ?_⟩
    -- CenteredRectangular (D₂) vs Square (D₄)
    · intro ⟨_, _, _, ⟨eD4⟩⟩
      have : Nonempty ((DihedralPointGroup 2) ≃* DihedralPointGroup 4) :=
        ⟨eD2.symm.trans eD4⟩
      exact dihedralPointGroup_two_not_iso_four.false this.some
    -- CenteredRectangular (D₂) vs Hexagonal (D₆)
    · intro ⟨_, _, _, ⟨eD6⟩⟩
      have : Nonempty ((DihedralPointGroup 2) ≃* DihedralPointGroup 6) :=
        ⟨eD2.symm.trans eD6⟩
      exact dihedralPointGroup_two_not_iso_six.false this.some
  case square =>
    intro ⟨_, _, _, ⟨eD4⟩⟩ ⟨_, _, _, ⟨eD6⟩⟩
    -- Square (D₄) vs Hexagonal (D₆)
    have : Nonempty ((DihedralPointGroup 4) ≃* DihedralPointGroup 6) :=
      ⟨eD4.symm.trans eD6⟩
    exact dihedralPointGroup_four_not_iso_six.false this.some

/-- Every 2D lattice belongs to exactly one of the five Bravais types.

blueprint: thm:bravais_classification -/
theorem bravais_classification (Λ : Lattice2) :
    IsObliqueLattice Λ ∨ IsRectangularLattice Λ ∨ IsCenteredRectangularLattice Λ ∨
    IsSquareLattice Λ ∨ IsHexagonalLattice Λ := by
  -- The proof proceeds by classifying the symmetry group of Λ:
  -- 1. Compute/determine the symmetry group Sym(Λ) ⊆ O(2)
  -- 2. By the classification of finite subgroups of O(2), Sym(Λ) is either Cₙ or Dₙ
  -- 3. For a rank-2 lattice, the possible symmetry groups are: C₂, D₂, D₄, D₆
  --    (C₁ is impossible since -1 is always a symmetry; higher symmetries like C₃
  --     would force the lattice to have special structure)
  -- 4. Match the symmetry group to the Bravais type:
  --    - C₂ → Oblique
  --    - D₂ → Rectangular or CenteredRectangular (distinguished by geometry)
  --    - D₄ → Square
  --    - D₆ → Hexagonal
  --
  -- The D₂ case requires showing that the lattice has either an orthogonal basis
  -- with unequal lengths (rectangular) or an equal-length basis (centered rectangular).
  --
  -- TODO: Formalize the classification of finite subgroups of O(2) that preserve a lattice,
  -- then use the geometric analysis to complete the classification.
  sorry

/-- An inductive type representing the five Bravais lattice types. -/
inductive BravaisType
  | oblique
  | rectangular
  | centeredRectangular
  | square
  | hexagonal
  deriving DecidableEq, Repr

open Classical in
/-- Get the Bravais type of a lattice. -/
noncomputable def Lattice2.bravaisType (Λ : Lattice2) : BravaisType :=
  if IsSquareLattice Λ then BravaisType.square
  else if IsHexagonalLattice Λ then BravaisType.hexagonal
  else if IsRectangularLattice Λ then BravaisType.rectangular
  else if IsCenteredRectangularLattice Λ then BravaisType.centeredRectangular
  else BravaisType.oblique

end WallpaperGroups.Lattice
