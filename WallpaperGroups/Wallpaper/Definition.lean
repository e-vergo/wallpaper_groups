/-
Copyright (c) 2025 Wallpaper Groups Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import WallpaperGroups.Euclidean.EuclideanGroup
import WallpaperGroups.Lattice.Basic

/-!
# Wallpaper Group Definition

This file defines wallpaper groups as discrete cocompact subgroups of E(2).

## Main definitions

* `IsDiscreteSubgroup` - A subgroup with discrete topology
* `IsCocompact` - The quotient space is compact
* `IsWallpaperGroup` - Discrete AND cocompact

## Overview

A wallpaper group (plane crystallographic group) is a subgroup Γ ⊂ E(2) that is:
1. Discrete: has the discrete topology
2. Cocompact: the quotient ℝ²/Γ is compact

These are the symmetry groups of periodic patterns in the plane.
-/

namespace WallpaperGroups.Wallpaper

open WallpaperGroups.Euclidean

/-- A subgroup Γ ⊂ E(2) is discrete if it has the discrete topology.

Equivalently, there is a neighborhood of the identity containing only the identity.

blueprint: def:discrete_subgroup -/
def IsDiscreteSubgroup (Γ : Subgroup EuclideanGroup2) : Prop :=
  ∃ ε > 0, ∀ g ∈ Γ, g ≠ 1 → ε ≤ ‖g.left‖ ∨ g.right ≠ 1

/-- A subgroup Γ ⊂ E(2) acts cocompactly if the quotient ℝ²/Γ is compact.

This means there exists a compact fundamental domain for the action.

blueprint: def:cocompact_subgroup -/
def IsCocompact (Γ : Subgroup EuclideanGroup2) : Prop :=
  ∃ (K : Set EuclideanPlane), IsCompact K ∧
    ∀ x : EuclideanPlane, ∃ g ∈ Γ, x - Multiplicative.toAdd g.left ∈ K

/-- A wallpaper group is a discrete cocompact subgroup of E(2).

blueprint: def:wallpaper_group -/
structure IsWallpaperGroup (Γ : Subgroup EuclideanGroup2) : Prop where
  /-- The subgroup is discrete. -/
  discrete : IsDiscreteSubgroup Γ
  /-- The subgroup acts cocompactly. -/
  cocompact : IsCocompact Γ

/-- Alternative characterization: Γ is a wallpaper group iff its translation
subgroup is a rank-2 lattice. -/
lemma isWallpaperGroup_iff_translation_isLattice (Γ : Subgroup EuclideanGroup2) :
    IsWallpaperGroup Γ ↔
    ∃ (Λ : WallpaperGroups.Lattice.Lattice2),
      ∀ v : EuclideanPlane, v ∈ Λ ↔ EuclideanGroup2.mk v 1 ∈ Γ := by
  sorry

/-- The trivial subgroup is not a wallpaper group (not cocompact). -/
lemma not_isWallpaperGroup_bot : ¬IsWallpaperGroup (⊥ : Subgroup EuclideanGroup2) := by
  sorry

/-- E(2) itself is not a wallpaper group (not discrete). -/
lemma not_isWallpaperGroup_top : ¬IsWallpaperGroup (⊤ : Subgroup EuclideanGroup2) := by
  sorry

end WallpaperGroups.Wallpaper
