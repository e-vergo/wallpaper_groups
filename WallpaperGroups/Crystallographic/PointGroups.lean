/-
Copyright (c) 2025 Wallpaper Groups Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import WallpaperGroups.Crystallographic.Restriction
import WallpaperGroups.PointGroup.FiniteO2Classification
import WallpaperGroups.Lattice.BravaisTypes

/-!
# Crystallographic Point Groups

This file defines crystallographic point groups and enumerates all 10 of them.

## Main definitions

* `IsCrystallographicPointGroup` - A point group compatible with some lattice

## Main results

* `crystallographic_point_groups` - The 10 crystallographic point groups are:
  C₁, C₂, C₃, C₄, C₆, D₁, D₂, D₃, D₄, D₆
* `compatible_point_groups` - Which point groups are compatible with each Bravais type

blueprint: cor:crystallographic_enumeration
-/

namespace WallpaperGroups.Crystallographic

open WallpaperGroups.Euclidean
open WallpaperGroups.PointGroup
open WallpaperGroups.Lattice

/-- A point group H ⊂ O(2) is crystallographic if it can be realized as the
symmetry group of some lattice.

Equivalently, H is finite and all rotations in H have order dividing 1, 2, 3, 4, or 6.

blueprint: def:crystallographic_point_group -/
def IsCrystallographicPointGroup (H : Subgroup OrthogonalGroup2) : Prop :=
  Finite H ∧
  ∀ A ∈ H, A ∈ SpecialOrthogonalGroup2 →
    ∃ n ∈ ({1, 2, 3, 4, 6} : Set ℕ), A^n = 1

/-- The cyclic point groups that are crystallographic: C₁, C₂, C₃, C₄, C₆. -/
lemma cyclic_crystallographic (n : ℕ) [NeZero n] :
    IsCrystallographicPointGroup (CyclicPointGroup n) ↔ n ∈ ({1, 2, 3, 4, 6} : Set ℕ) := by
  sorry

/-- The dihedral point groups that are crystallographic: D₁, D₂, D₃, D₄, D₆. -/
lemma dihedral_crystallographic (n : ℕ) [NeZero n] :
    IsCrystallographicPointGroup (DihedralPointGroup n) ↔ n ∈ ({1, 2, 3, 4, 6} : Set ℕ) := by
  sorry

/-- There are exactly 10 crystallographic point groups.

They are: C₁, C₂, C₃, C₄, C₆, D₁, D₂, D₃, D₄, D₆

blueprint: cor:crystallographic_enumeration -/
theorem crystallographic_point_groups (H : Subgroup OrthogonalGroup2)
    (hH : IsCrystallographicPointGroup H) :
    (∃ n : ℕ, ∃ _ : NeZero n,
      n ∈ ({1, 2, 3, 4, 6} : Set ℕ) ∧ Nonempty (H ≃* CyclicPointGroup n)) ∨
    (∃ n : ℕ, ∃ _ : NeZero n,
      n ∈ ({1, 2, 3, 4, 6} : Set ℕ) ∧ Nonempty (H ≃* DihedralPointGroup n)) := by
  sorry

/-- The 10 crystallographic point groups as an inductive type. -/
inductive CrystallographicPointGroupType
  | C1 | C2 | C3 | C4 | C6
  | D1 | D2 | D3 | D4 | D6
  deriving DecidableEq, Repr

/-- Which point groups are compatible with which Bravais lattice types.

| Lattice Type      | Compatible Point Groups          |
|-------------------|----------------------------------|
| Oblique           | C₁, C₂                           |
| Rectangular       | C₁, C₂, D₁, D₂                   |
| Centered Rect     | C₁, C₂, D₁, D₂                   |
| Square            | C₁, C₂, C₄, D₁, D₂, D₄           |
| Hexagonal         | C₁, C₂, C₃, C₆, D₁, D₂, D₃, D₆   |

blueprint: lem:compatible_point_groups -/
lemma compatible_point_groups :
    -- Oblique lattices only support C₁ and C₂
    (∀ Λ : Lattice2, IsObliqueLattice Λ →
      (latticeSymmetryGroup Λ) ≤ CyclicPointGroup 2) ∧
    -- Square lattices support up to D₄
    (∀ Λ : Lattice2, IsSquareLattice Λ →
      ∃ n : ℕ, ∃ _ : NeZero n, n ∈ ({1, 2, 4} : Set ℕ) ∧
        (Nonempty ((latticeSymmetryGroup Λ) ≃* CyclicPointGroup n) ∨
        Nonempty ((latticeSymmetryGroup Λ) ≃* DihedralPointGroup n))) ∧
    -- Hexagonal lattices support up to D₆
    (∀ Λ : Lattice2, IsHexagonalLattice Λ →
      ∃ n : ℕ, ∃ _ : NeZero n, n ∈ ({1, 2, 3, 6} : Set ℕ) ∧
        (Nonempty ((latticeSymmetryGroup Λ) ≃* CyclicPointGroup n) ∨
        Nonempty ((latticeSymmetryGroup Λ) ≃* DihedralPointGroup n))) := by
  sorry

/-- The lattice symmetry group is always crystallographic. -/
lemma latticeSymmetryGroup_isCrystallographic (Λ : Lattice2) :
    IsCrystallographicPointGroup (latticeSymmetryGroup Λ) := by
  sorry

/-- Every crystallographic point group is realized by some lattice. -/
lemma crystallographic_realized (n : ℕ) [NeZero n] (hn : n ∈ ({1, 2, 3, 4, 6} : Set ℕ)) :
    ∃ Λ : Lattice2, Nonempty ((latticeSymmetryGroup Λ) ≃* DihedralPointGroup n) := by
  sorry

end WallpaperGroups.Crystallographic
