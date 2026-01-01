/-
Copyright (c) 2025 Wallpaper Groups Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import WallpaperGroups.Wallpaper.Structure
import WallpaperGroups.Lattice.BravaisTypes
import WallpaperGroups.Groups.Oblique

/-!
# Rectangular Lattice Wallpaper Groups: pm, pg, pmm, pmg, pgg

This file defines the five wallpaper groups with rectangular lattices.

## Main definitions

* `WallpaperGroup.pm` - Reflections parallel to one axis, PG = D₁, symmorphic
* `WallpaperGroup.pg` - Glide reflections only, PG = D₁, non-symmorphic
* `WallpaperGroup.pmm` - Reflections in both axes, PG = D₂, symmorphic
* `WallpaperGroup.pmg` - Mixed: reflection + glide, PG = D₂, non-symmorphic
* `WallpaperGroup.pgg` - Glide reflections in both directions, PG = D₂, non-symmorphic

blueprint: def:pm, def:pg, def:pmm, def:pmg, def:pgg
-/

namespace WallpaperGroups.Groups

open WallpaperGroups.Euclidean
open WallpaperGroups.Lattice
open WallpaperGroups.Wallpaper
open WallpaperGroups.PointGroup

variable (Λ : Lattice2) (hΛ : IsRectangularLattice Λ)

/-- The wallpaper group pm has translations and reflections parallel to one axis.

- Lattice type: Rectangular
- Point group: D₁ ≅ C₂
- Symmorphic: Yes (contains genuine reflections, not glides)
- The reflection axis is parallel to one lattice vector

blueprint: def:pm -/
def WallpaperGroup.pm (Λ : Lattice2) : Subgroup EuclideanGroup2 where
  carrier := {g | ∃ (A : OrthogonalGroup2),
    A ∈ DihedralPointGroup 1 ∧
    EuclideanGroup2.mk 0 A⁻¹ * g * EuclideanGroup2.mk 0 A ∈ WallpaperGroup.p1 Λ}
  mul_mem' := by intro a b ha hb; sorry
  one_mem' := by sorry
  inv_mem' := by intro a ha; sorry

/-- pm is a wallpaper group. -/
lemma WallpaperGroup.pm.isWallpaperGroup : IsWallpaperGroup (WallpaperGroup.pm Λ) := by
  sorry

/-- pm is symmorphic. -/
lemma WallpaperGroup.pm.isSymmorphic : IsSymmorphic (WallpaperGroup.pm Λ) := by
  sorry

/-- The point group of pm is D₁. -/
lemma WallpaperGroup.pm.pointGroup :
    Nonempty ((WallpaperGroup.pointGroup (WallpaperGroup.pm Λ)) ≃* DihedralPointGroup 1) := by
  sorry

/-- The wallpaper group pg has translations and glide reflections (no pure reflections).

- Lattice type: Rectangular
- Point group: D₁ ≅ C₂
- Symmorphic: No (glide reflections only, no true reflections)
- The glide axis is parallel to one lattice vector

blueprint: def:pg -/
def WallpaperGroup.pg (Λ : Lattice2) : Subgroup EuclideanGroup2 where
  carrier := {g | sorry}
  mul_mem' := by intro a b ha hb; sorry
  one_mem' := by sorry
  inv_mem' := by intro a ha; sorry

/-- pg is a wallpaper group. -/
lemma WallpaperGroup.pg.isWallpaperGroup : IsWallpaperGroup (WallpaperGroup.pg Λ) := by
  sorry

/-- pg is non-symmorphic. -/
lemma WallpaperGroup.pg.not_isSymmorphic : ¬IsSymmorphic (WallpaperGroup.pg Λ) := by
  sorry

/-- The point group of pg is D₁. -/
lemma WallpaperGroup.pg.pointGroup :
    Nonempty ((WallpaperGroup.pointGroup (WallpaperGroup.pg Λ)) ≃* DihedralPointGroup 1) := by
  sorry

/-- The wallpaper group pmm has reflections in both axes.

- Lattice type: Rectangular
- Point group: D₂ (Klein four-group)
- Symmorphic: Yes
- Two perpendicular reflection axes

blueprint: def:pmm -/
def WallpaperGroup.pmm (Λ : Lattice2) : Subgroup EuclideanGroup2 where
  carrier := {g | sorry}
  mul_mem' := by intro a b ha hb; sorry
  one_mem' := by sorry
  inv_mem' := by intro a ha; sorry

/-- pmm is a wallpaper group. -/
lemma WallpaperGroup.pmm.isWallpaperGroup : IsWallpaperGroup (WallpaperGroup.pmm Λ) := by
  sorry

/-- pmm is symmorphic. -/
lemma WallpaperGroup.pmm.isSymmorphic : IsSymmorphic (WallpaperGroup.pmm Λ) := by
  sorry

/-- The point group of pmm is D₂. -/
lemma WallpaperGroup.pmm.pointGroup :
    Nonempty ((WallpaperGroup.pointGroup (WallpaperGroup.pmm Λ)) ≃* DihedralPointGroup 2) := by
  sorry

/-- The wallpaper group pmg has one reflection axis and one glide axis.

- Lattice type: Rectangular
- Point group: D₂
- Symmorphic: No
- One genuine reflection, one glide reflection

blueprint: def:pmg -/
def WallpaperGroup.pmg (Λ : Lattice2) : Subgroup EuclideanGroup2 where
  carrier := {g | sorry}
  mul_mem' := by intro a b ha hb; sorry
  one_mem' := by sorry
  inv_mem' := by intro a ha; sorry

/-- pmg is a wallpaper group. -/
lemma WallpaperGroup.pmg.isWallpaperGroup : IsWallpaperGroup (WallpaperGroup.pmg Λ) := by
  sorry

/-- pmg is non-symmorphic. -/
lemma WallpaperGroup.pmg.not_isSymmorphic : ¬IsSymmorphic (WallpaperGroup.pmg Λ) := by
  sorry

/-- The point group of pmg is D₂. -/
lemma WallpaperGroup.pmg.pointGroup :
    Nonempty ((WallpaperGroup.pointGroup (WallpaperGroup.pmg Λ)) ≃* DihedralPointGroup 2) := by
  sorry

/-- The wallpaper group pgg has glide reflections in both directions.

- Lattice type: Rectangular
- Point group: D₂
- Symmorphic: No
- Two perpendicular glide reflection axes (no true reflections)

blueprint: def:pgg -/
def WallpaperGroup.pgg (Λ : Lattice2) : Subgroup EuclideanGroup2 where
  carrier := {g | sorry}
  mul_mem' := by intro a b ha hb; sorry
  one_mem' := by sorry
  inv_mem' := by intro a ha; sorry

/-- pgg is a wallpaper group. -/
lemma WallpaperGroup.pgg.isWallpaperGroup : IsWallpaperGroup (WallpaperGroup.pgg Λ) := by
  sorry

/-- pgg is non-symmorphic. -/
lemma WallpaperGroup.pgg.not_isSymmorphic : ¬IsSymmorphic (WallpaperGroup.pgg Λ) := by
  sorry

/-- The point group of pgg is D₂. -/
lemma WallpaperGroup.pgg.pointGroup :
    Nonempty ((WallpaperGroup.pointGroup (WallpaperGroup.pgg Λ)) ≃* DihedralPointGroup 2) := by
  sorry

end WallpaperGroups.Groups
