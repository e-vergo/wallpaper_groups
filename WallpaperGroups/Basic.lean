/-
Copyright (c) 2025 Wallpaper Groups Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.Matrix.Orthogonal
import Mathlib.LinearAlgebra.Trace
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Topology.Algebra.Group.Compact
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Wallpaper Groups - Common Imports and Notation

This file provides common imports used throughout the wallpaper groups formalization.

## Overview

A wallpaper group (plane crystallographic group) is a discrete cocompact subgroup of
the Euclidean group E(2). This project formalizes the theorem that there are exactly
17 such groups up to isomorphism.

## Main Components

* `WallpaperGroups.Euclidean` - The Euclidean plane and group E(2) = ℝ² ⋊ O(2)
* `WallpaperGroups.PointGroup` - Cyclic and dihedral point groups Cₙ, Dₙ
* `WallpaperGroups.Lattice` - Rank-2 lattices and Bravais types
* `WallpaperGroups.Crystallographic` - Crystallographic restriction theorem
* `WallpaperGroups.Wallpaper` - Wallpaper group definition and structure
* `WallpaperGroups.Groups` - The 17 wallpaper groups
* `WallpaperGroups.Classification` - Main classification theorem
-/

namespace WallpaperGroups

-- Common notation will be added here as needed

end WallpaperGroups
