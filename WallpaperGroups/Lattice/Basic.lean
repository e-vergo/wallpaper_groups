/-
Copyright (c) 2025 Wallpaper Groups Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import WallpaperGroups.Euclidean.Plane

/-!
# Rank-2 Lattices in the Euclidean Plane

This file defines rank-2 lattices in ℝ² and their basic properties.

## Main definitions

* `Lattice2` - A rank-2 lattice in the Euclidean plane
* `latticeBasis` - A basis (a, b) for a lattice Λ = ℤa + ℤb
* `latticeFundamentalDomain` - The fundamental domain for a lattice

## Main results

* `Lattice2.discrete` - Every lattice is discrete
* `Lattice2.cocompact` - The quotient ℝ²/Λ is compact (a torus)
-/

namespace WallpaperGroups.Lattice

open WallpaperGroups.Euclidean

/-- A rank-2 lattice in the Euclidean plane.

A lattice Λ ⊂ ℝ² is a discrete subgroup of rank 2, meaning Λ = ℤa + ℤb
for some linearly independent vectors a, b.

blueprint: def:lattice -/
structure Lattice2 where
  /-- The underlying additive subgroup of ℝ². -/
  carrier : AddSubgroup EuclideanPlane
  /-- The lattice has rank 2 (spans ℝ²). -/
  rank_eq_two : ∃ (a b : EuclideanPlane), LinearIndependent ℝ ![a, b] ∧
    carrier = AddSubgroup.closure {a, b}
  /-- The lattice is discrete. -/
  discrete : ∀ x ∈ carrier, x ≠ 0 → ∃ ε > 0, ∀ y ∈ carrier, y ≠ x → ε ≤ ‖y - x‖

instance : SetLike Lattice2 EuclideanPlane where
  coe Λ := Λ.carrier
  coe_injective' := by
    intro Λ₁ Λ₂ h
    have hc : Λ₁.carrier = Λ₂.carrier := SetLike.coe_injective h
    cases Λ₁; cases Λ₂
    simp only at hc
    subst hc
    rfl

-- Note: SetLike already provides a Membership instance, so we don't need to define one

/-- A basis for a lattice consists of two linearly independent vectors
that generate the lattice.

blueprint: def:lattice_basis -/
structure LatticeBasis (Λ : Lattice2) where
  /-- First basis vector. -/
  a : EuclideanPlane
  /-- Second basis vector. -/
  b : EuclideanPlane
  /-- The vectors are linearly independent. -/
  linearIndependent : LinearIndependent ℝ ![a, b]
  /-- The vectors generate the lattice. -/
  generates : Λ.carrier = AddSubgroup.closure {a, b}

/-- Every lattice has a basis. -/
lemma Lattice2.exists_basis (Λ : Lattice2) : Nonempty (LatticeBasis Λ) := by
  sorry

/-- The fundamental domain of a lattice with basis (a, b).

F = {sa + tb | 0 ≤ s < 1, 0 ≤ t < 1}

blueprint: def:fundamental_domain -/
def latticeFundamentalDomain (Λ : Lattice2) (B : LatticeBasis Λ) : Set EuclideanPlane :=
  {v | ∃ (s t : ℝ), 0 ≤ s ∧ s < 1 ∧ 0 ≤ t ∧ t < 1 ∧ v = s • B.a + t • B.b}

/-- Every lattice is discrete (has the discrete topology).

blueprint: lem:lattice_discrete -/
lemma Lattice2.isDiscrete (Λ : Lattice2) :
    ∀ x ∈ Λ.carrier, ∃ ε > 0, ∀ y ∈ Λ.carrier, y ≠ x → ε ≤ ‖y - x‖ := by
  intro x hx
  by_cases h : x = 0
  · -- Use the discrete property with any nonzero lattice point
    sorry
  · exact Λ.discrete x hx h

/-- The quotient ℝ²/Λ is compact (homeomorphic to a torus).

blueprint: lem:lattice_cocompact -/
lemma Lattice2.quotient_compact (Λ : Lattice2) :
    CompactSpace (EuclideanPlane ⧸ Λ.carrier) := by
  sorry

/-- Lattice membership can be characterized using a basis. -/
lemma Lattice2.mem_iff_integer_coords (Λ : Lattice2) (B : LatticeBasis Λ) (v : EuclideanPlane) :
    v ∈ Λ ↔ ∃ (m n : ℤ), v = m • B.a + n • B.b := by
  sorry

/-- The lattice is closed under addition. -/
lemma Lattice2.add_mem (Λ : Lattice2) {v w : EuclideanPlane} (hv : v ∈ Λ) (hw : w ∈ Λ) :
    v + w ∈ Λ :=
  Λ.carrier.add_mem hv hw

/-- The lattice is closed under negation. -/
lemma Lattice2.neg_mem (Λ : Lattice2) {v : EuclideanPlane} (hv : v ∈ Λ) : -v ∈ Λ :=
  Λ.carrier.neg_mem hv

/-- The zero vector is in every lattice. -/
lemma Lattice2.zero_mem (Λ : Lattice2) : (0 : EuclideanPlane) ∈ Λ :=
  Λ.carrier.zero_mem

end WallpaperGroups.Lattice
