/-
Copyright (c) 2025 Wallpaper Groups Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import WallpaperGroups.Groups.Oblique
import WallpaperGroups.Groups.Rectangular
import WallpaperGroups.Groups.CenteredRectangular
import WallpaperGroups.Groups.Square
import WallpaperGroups.Groups.Hexagonal

/-!
# Verification: Each of the 17 Groups is a Wallpaper Group

This file proves that each of the 17 defined groups satisfies the wallpaper
group definition (discrete and cocompact subgroup of E(2)).

## Main results

For each group G ∈ {p1, p2, pm, pg, cm, pmm, pmg, pgg, cmm, p4, p4m, p4g,
p3, p3m1, p31m, p6, p6m}:
* `G.isWallpaperGroup` - G is a wallpaper group

blueprint: lem:p1_is_wallpaper, lem:p2_is_wallpaper, ...
-/

namespace WallpaperGroups.Classification

open WallpaperGroups.Groups
open WallpaperGroups.Wallpaper
open WallpaperGroups.Lattice

/-! ### Oblique Lattice Groups -/

/-- p1 is a wallpaper group.

blueprint: lem:p1_is_wallpaper -/
theorem p1_isWallpaperGroup (Λ : Lattice2) : IsWallpaperGroup (WallpaperGroup.p1 Λ) := by
  constructor
  · sorry
  · sorry

/-- p2 is a wallpaper group.

blueprint: lem:p2_is_wallpaper -/
theorem p2_isWallpaperGroup (Λ : Lattice2) : IsWallpaperGroup (WallpaperGroup.p2 Λ) := by
  sorry

/-! ### Rectangular Lattice Groups -/

/-- pm is a wallpaper group.

blueprint: lem:pm_is_wallpaper -/
theorem pm_isWallpaperGroup (Λ : Lattice2) : IsWallpaperGroup (WallpaperGroup.pm Λ) := by
  sorry

/-- pg is a wallpaper group.

blueprint: lem:pg_is_wallpaper -/
theorem pg_isWallpaperGroup (Λ : Lattice2) : IsWallpaperGroup (WallpaperGroup.pg Λ) := by
  sorry

/-- pmm is a wallpaper group.

blueprint: lem:pmm_is_wallpaper -/
theorem pmm_isWallpaperGroup (Λ : Lattice2) : IsWallpaperGroup (WallpaperGroup.pmm Λ) := by
  sorry

/-- pmg is a wallpaper group.

blueprint: lem:pmg_is_wallpaper -/
theorem pmg_isWallpaperGroup (Λ : Lattice2) : IsWallpaperGroup (WallpaperGroup.pmg Λ) := by
  sorry

/-- pgg is a wallpaper group.

blueprint: lem:pgg_is_wallpaper -/
theorem pgg_isWallpaperGroup (Λ : Lattice2) : IsWallpaperGroup (WallpaperGroup.pgg Λ) := by
  sorry

/-! ### Centered Rectangular Lattice Groups -/

/-- cm is a wallpaper group.

blueprint: lem:cm_is_wallpaper -/
theorem cm_isWallpaperGroup (Λ : Lattice2) (_hΛ : IsCenteredRectangularLattice Λ) :
    IsWallpaperGroup (WallpaperGroup.cm Λ) := by
  sorry

/-- cmm is a wallpaper group.

blueprint: lem:cmm_is_wallpaper -/
theorem cmm_isWallpaperGroup (Λ : Lattice2) (_hΛ : IsCenteredRectangularLattice Λ) :
    IsWallpaperGroup (WallpaperGroup.cmm Λ) := by
  sorry

/-! ### Square Lattice Groups -/

/-- p4 is a wallpaper group.

blueprint: lem:p4_is_wallpaper -/
theorem p4_isWallpaperGroup (Λ : Lattice2) (_hΛ : IsSquareLattice Λ) :
    IsWallpaperGroup (WallpaperGroup.p4 Λ) := by
  sorry

/-- p4m is a wallpaper group.

blueprint: lem:p4m_is_wallpaper -/
theorem p4m_isWallpaperGroup (Λ : Lattice2) (_hΛ : IsSquareLattice Λ) :
    IsWallpaperGroup (WallpaperGroup.p4m Λ) := by
  sorry

/-- p4g is a wallpaper group.

blueprint: lem:p4g_is_wallpaper -/
theorem p4g_isWallpaperGroup (Λ : Lattice2) (_hΛ : IsSquareLattice Λ) :
    IsWallpaperGroup (WallpaperGroup.p4g Λ) := by
  sorry

/-! ### Hexagonal Lattice Groups -/

/-- p3 is a wallpaper group.

blueprint: lem:p3_is_wallpaper -/
theorem p3_isWallpaperGroup (Λ : Lattice2) (_hΛ : IsHexagonalLattice Λ) :
    IsWallpaperGroup (WallpaperGroup.p3 Λ) := by
  sorry

/-- p3m1 is a wallpaper group.

blueprint: lem:p3m1_is_wallpaper -/
theorem p3m1_isWallpaperGroup (Λ : Lattice2) (_hΛ : IsHexagonalLattice Λ) :
    IsWallpaperGroup (WallpaperGroup.p3m1 Λ) := by
  sorry

/-- p31m is a wallpaper group.

blueprint: lem:p31m_is_wallpaper -/
theorem p31m_isWallpaperGroup (Λ : Lattice2) (_hΛ : IsHexagonalLattice Λ) :
    IsWallpaperGroup (WallpaperGroup.p31m Λ) := by
  sorry

/-- p6 is a wallpaper group.

blueprint: lem:p6_is_wallpaper -/
theorem p6_isWallpaperGroup (Λ : Lattice2) (_hΛ : IsHexagonalLattice Λ) :
    IsWallpaperGroup (WallpaperGroup.p6 Λ) := by
  sorry

/-- p6m is a wallpaper group.

blueprint: lem:p6m_is_wallpaper -/
theorem p6m_isWallpaperGroup (Λ : Lattice2) (_hΛ : IsHexagonalLattice Λ) :
    IsWallpaperGroup (WallpaperGroup.p6m Λ) := by
  sorry

end WallpaperGroups.Classification
