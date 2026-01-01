/-
Copyright (c) 2025 Wallpaper Groups Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import WallpaperGroups.Lattice.Symmetry
import WallpaperGroups.PointGroup.CyclicDihedral

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

/-- The five Bravais types are mutually exclusive. -/
lemma bravais_exclusive (Λ : Lattice2) :
    (IsObliqueLattice Λ → ¬IsRectangularLattice Λ ∧ ¬IsCenteredRectangularLattice Λ ∧
                          ¬IsSquareLattice Λ ∧ ¬IsHexagonalLattice Λ) ∧
    (IsRectangularLattice Λ → ¬IsCenteredRectangularLattice Λ ∧
                              ¬IsSquareLattice Λ ∧ ¬IsHexagonalLattice Λ) ∧
    (IsCenteredRectangularLattice Λ → ¬IsSquareLattice Λ ∧ ¬IsHexagonalLattice Λ) ∧
    (IsSquareLattice Λ → ¬IsHexagonalLattice Λ) := by
  sorry

/-- Every 2D lattice belongs to exactly one of the five Bravais types.

blueprint: thm:bravais_classification -/
theorem bravais_classification (Λ : Lattice2) :
    IsObliqueLattice Λ ∨ IsRectangularLattice Λ ∨ IsCenteredRectangularLattice Λ ∨
    IsSquareLattice Λ ∨ IsHexagonalLattice Λ := by
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
