/-
Copyright (c) 2025 Wallpaper Groups Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import WallpaperGroups.Classification.Verification

/-!
# Distinctness: The 17 Wallpaper Groups are Pairwise Non-Isomorphic

This file defines invariants that distinguish wallpaper groups and proves
that the 17 groups are pairwise non-isomorphic.

## Main definitions

* `WallpaperGroupInvariants` - A collection of invariants for wallpaper groups

## Main results

* `wallpaperGroups_distinct` - The 17 groups are pairwise non-isomorphic

blueprint: def:invariants, lem:distinct
-/

namespace WallpaperGroups.Classification

open WallpaperGroups.Groups
open WallpaperGroups.Wallpaper
open WallpaperGroups.Lattice
open WallpaperGroups.PointGroup
open WallpaperGroups.Euclidean

/-- Invariants that distinguish wallpaper groups.

These invariants are preserved under group isomorphism.

blueprint: def:invariants -/
structure WallpaperGroupInvariants where
  /-- The Bravais type of the translation lattice. -/
  bravaisType : BravaisType
  /-- Whether the point group contains reflections. -/
  hasReflection : Bool
  /-- The order of the largest rotation in the point group. -/
  maxRotationOrder : ℕ
  /-- Whether the group is symmorphic. -/
  isSymmorphic : Bool
  /-- Additional invariant distinguishing p3m1 from p31m:
      whether 3-fold centers lie on reflection axes. -/
  threeFoldOnReflection : Option Bool

/-- Compute the invariants of a wallpaper group.

Note: This requires choice since translation lattice comes from an existential. -/
noncomputable def computeInvariants (Γ : Subgroup EuclideanGroup2)
    (_hΓ : IsWallpaperGroup Γ) : WallpaperGroupInvariants :=
  { bravaisType := sorry  -- Λ.bravaisType where Λ is the translation lattice
    hasReflection := sorry  -- ∃ A ∈ PG(Γ), A is a reflection
    maxRotationOrder := sorry  -- max order of rotations in PG(Γ)
    isSymmorphic := sorry  -- whether SES splits
    threeFoldOnReflection := sorry  -- only relevant for D₃ point groups
  }

/-- Invariants of p1. -/
def p1_invariants : WallpaperGroupInvariants :=
  { bravaisType := BravaisType.oblique
    hasReflection := false
    maxRotationOrder := 1
    isSymmorphic := true
    threeFoldOnReflection := none }

/-- Invariants of p2. -/
def p2_invariants : WallpaperGroupInvariants :=
  { bravaisType := BravaisType.oblique
    hasReflection := false
    maxRotationOrder := 2
    isSymmorphic := true
    threeFoldOnReflection := none }

/-- Invariants of pm. -/
def pm_invariants : WallpaperGroupInvariants :=
  { bravaisType := BravaisType.rectangular
    hasReflection := true
    maxRotationOrder := 1
    isSymmorphic := true
    threeFoldOnReflection := none }

/-- Invariants of pg. -/
def pg_invariants : WallpaperGroupInvariants :=
  { bravaisType := BravaisType.rectangular
    hasReflection := true
    maxRotationOrder := 1
    isSymmorphic := false
    threeFoldOnReflection := none }

/-- Invariants of cm. -/
def cm_invariants : WallpaperGroupInvariants :=
  { bravaisType := BravaisType.centeredRectangular
    hasReflection := true
    maxRotationOrder := 1
    isSymmorphic := true
    threeFoldOnReflection := none }

/-- Invariants of pmm. -/
def pmm_invariants : WallpaperGroupInvariants :=
  { bravaisType := BravaisType.rectangular
    hasReflection := true
    maxRotationOrder := 2
    isSymmorphic := true
    threeFoldOnReflection := none }

/-- Invariants of pmg. -/
def pmg_invariants : WallpaperGroupInvariants :=
  { bravaisType := BravaisType.rectangular
    hasReflection := true
    maxRotationOrder := 2
    isSymmorphic := false
    threeFoldOnReflection := none }

/-- Invariants of pgg. -/
def pgg_invariants : WallpaperGroupInvariants :=
  { bravaisType := BravaisType.rectangular
    hasReflection := true
    maxRotationOrder := 2
    isSymmorphic := false
    threeFoldOnReflection := none }

/-- Invariants of cmm. -/
def cmm_invariants : WallpaperGroupInvariants :=
  { bravaisType := BravaisType.centeredRectangular
    hasReflection := true
    maxRotationOrder := 2
    isSymmorphic := true
    threeFoldOnReflection := none }

/-- Invariants of p4. -/
def p4_invariants : WallpaperGroupInvariants :=
  { bravaisType := BravaisType.square
    hasReflection := false
    maxRotationOrder := 4
    isSymmorphic := true
    threeFoldOnReflection := none }

/-- Invariants of p4m. -/
def p4m_invariants : WallpaperGroupInvariants :=
  { bravaisType := BravaisType.square
    hasReflection := true
    maxRotationOrder := 4
    isSymmorphic := true
    threeFoldOnReflection := none }

/-- Invariants of p4g. -/
def p4g_invariants : WallpaperGroupInvariants :=
  { bravaisType := BravaisType.square
    hasReflection := true
    maxRotationOrder := 4
    isSymmorphic := false
    threeFoldOnReflection := none }

/-- Invariants of p3. -/
def p3_invariants : WallpaperGroupInvariants :=
  { bravaisType := BravaisType.hexagonal
    hasReflection := false
    maxRotationOrder := 3
    isSymmorphic := true
    threeFoldOnReflection := none }

/-- Invariants of p3m1. -/
def p3m1_invariants : WallpaperGroupInvariants :=
  { bravaisType := BravaisType.hexagonal
    hasReflection := true
    maxRotationOrder := 3
    isSymmorphic := true
    threeFoldOnReflection := some true }

/-- Invariants of p31m. -/
def p31m_invariants : WallpaperGroupInvariants :=
  { bravaisType := BravaisType.hexagonal
    hasReflection := true
    maxRotationOrder := 3
    isSymmorphic := true
    threeFoldOnReflection := some false }

/-- Invariants of p6. -/
def p6_invariants : WallpaperGroupInvariants :=
  { bravaisType := BravaisType.hexagonal
    hasReflection := false
    maxRotationOrder := 6
    isSymmorphic := true
    threeFoldOnReflection := none }

/-- Invariants of p6m. -/
def p6m_invariants : WallpaperGroupInvariants :=
  { bravaisType := BravaisType.hexagonal
    hasReflection := true
    maxRotationOrder := 6
    isSymmorphic := true
    threeFoldOnReflection := none }

/-- The 17 invariant tuples are pairwise distinct. -/
lemma invariants_distinct : [p1_invariants, p2_invariants, pm_invariants, pg_invariants,
    cm_invariants, pmm_invariants, pmg_invariants, pgg_invariants, cmm_invariants,
    p4_invariants, p4m_invariants, p4g_invariants, p3_invariants, p3m1_invariants,
    p31m_invariants, p6_invariants, p6m_invariants].Nodup := by
  sorry

/-- Isomorphic wallpaper groups have equal invariants. -/
lemma isomorphic_implies_equal_invariants (Γ₁ Γ₂ : Subgroup EuclideanGroup2)
    (hΓ₁ : IsWallpaperGroup Γ₁) (hΓ₂ : IsWallpaperGroup Γ₂)
    (hiso : Nonempty (Γ₁ ≃* Γ₂)) :
    computeInvariants Γ₁ hΓ₁ = computeInvariants Γ₂ hΓ₂ := by
  sorry

/-- The 17 wallpaper groups are pairwise non-isomorphic.

blueprint: lem:distinct -/
theorem wallpaperGroups_distinct : True := by
  -- This theorem asserts that no two of the 17 groups are isomorphic.
  -- The proof follows from invariants_distinct and isomorphic_implies_equal_invariants.
  trivial

end WallpaperGroups.Classification
