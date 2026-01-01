/-
Copyright (c) 2025 Wallpaper Groups Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import WallpaperGroups.Classification.Completeness

/-!
# Classification of the 17 Wallpaper Groups

This is the root file for the wallpaper groups formalization. It imports
all modules transitively.

## Overview

A **wallpaper group** (plane crystallographic group) is a discrete cocompact
subgroup of the Euclidean group E(2). This project formalizes the theorem that
there are exactly 17 such groups up to isomorphism.

## Main Results

* `WallpaperGroups.Crystallographic.crystallographic_restriction` -
  Lattice-preserving rotations have order ∈ {1, 2, 3, 4, 6}

* `WallpaperGroups.Lattice.bravais_classification` -
  Every 2D lattice is one of 5 Bravais types

* `WallpaperGroups.Classification.wallpaper_classification` -
  Every wallpaper group is isomorphic to exactly one of the 17 types

* `WallpaperGroups.Classification.wallpaper_count` -
  There are exactly 17 wallpaper groups

## File Structure

- `Basic` - Common imports
- `Euclidean/` - Euclidean plane and group E(2)
- `PointGroup/` - Cyclic and dihedral point groups
- `Lattice/` - Rank-2 lattices and Bravais types
- `Crystallographic/` - Crystallographic restriction theorem
- `Wallpaper/` - Wallpaper group definition and structure
- `Groups/` - The 17 wallpaper groups
- `Classification/` - Main classification theorem
-/
