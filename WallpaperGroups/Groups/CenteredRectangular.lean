/-
Copyright (c) 2025 Wallpaper Groups Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import WallpaperGroups.Wallpaper.Structure
import WallpaperGroups.Lattice.BravaisTypes

/-!
# Centered Rectangular Lattice Wallpaper Groups: cm and cmm

This file defines the two wallpaper groups with centered rectangular (rhombic) lattices.

## Main definitions

* `WallpaperGroup.cm` - Reflections + glides, PG = D₁, symmorphic
* `WallpaperGroup.cmm` - Reflections in both axes, PG = D₂, symmorphic

Both groups are symmorphic despite the "centered" lattice structure.

blueprint: def:cm, def:cmm
-/

namespace WallpaperGroups.Groups

open WallpaperGroups.Euclidean
open WallpaperGroups.Lattice
open WallpaperGroups.Wallpaper
open WallpaperGroups.PointGroup

variable (Λ : Lattice2) (hΛ : IsCenteredRectangularLattice Λ)

/-- The wallpaper group cm has reflections across one axis.

- Lattice type: Centered rectangular (rhombic)
- Point group: D₁ ≅ C₂
- Symmorphic: Yes
- Contains both reflections and glide reflections due to lattice centering

The "c" indicates the centered lattice. Despite having glide reflections,
cm is symmorphic because it also contains true reflections.

blueprint: def:cm -/
def WallpaperGroup.cm (Λ : Lattice2) : Subgroup EuclideanGroup2 where
  carrier := {g | g.left ∈ Λ ∧ sorry}
  mul_mem' := by intro a b ha hb; sorry
  one_mem' := by sorry
  inv_mem' := by intro a ha; sorry

/-- cm is a wallpaper group. -/
lemma WallpaperGroup.cm.isWallpaperGroup : IsWallpaperGroup (WallpaperGroup.cm Λ) := by
  sorry

/-- cm is symmorphic. -/
lemma WallpaperGroup.cm.isSymmorphic : IsSymmorphic (WallpaperGroup.cm Λ) := by
  sorry

/-- The point group of cm is D₁. -/
lemma WallpaperGroup.cm.pointGroup :
    Nonempty ((WallpaperGroup.pointGroup (WallpaperGroup.cm Λ)) ≃* DihedralPointGroup 1) := by
  sorry

/-- The wallpaper group cmm has reflections in both axes.

- Lattice type: Centered rectangular (rhombic)
- Point group: D₂ (Klein four-group)
- Symmorphic: Yes
- Two perpendicular reflection axes

blueprint: def:cmm -/
def WallpaperGroup.cmm (Λ : Lattice2) : Subgroup EuclideanGroup2 where
  carrier := {g | g.left ∈ Λ ∧ sorry}
  mul_mem' := by intro a b ha hb; sorry
  one_mem' := by sorry
  inv_mem' := by intro a ha; sorry

/-- cmm is a wallpaper group. -/
lemma WallpaperGroup.cmm.isWallpaperGroup : IsWallpaperGroup (WallpaperGroup.cmm Λ) := by
  sorry

/-- cmm is symmorphic. -/
lemma WallpaperGroup.cmm.isSymmorphic : IsSymmorphic (WallpaperGroup.cmm Λ) := by
  sorry

/-- The point group of cmm is D₂. -/
lemma WallpaperGroup.cmm.pointGroup :
    Nonempty ((WallpaperGroup.pointGroup (WallpaperGroup.cmm Λ)) ≃* DihedralPointGroup 2) := by
  sorry

/-- cm and cmm are the only wallpaper groups with centered rectangular lattice. -/
lemma centeredRectangular_wallpaperGroups (Γ : Subgroup EuclideanGroup2) (hΓ : IsWallpaperGroup Γ)
    (Λ' : Lattice2)
    (hΛ' : ∀ v, v ∈ Λ' ↔ (⟨v, 1⟩ : EuclideanGroup2) ∈ WallpaperGroup.translationSubgroup Γ)
    (hcr : IsCenteredRectangularLattice Λ') :
    Nonempty (Γ ≃* WallpaperGroup.cm Λ') ∨
    Nonempty (Γ ≃* WallpaperGroup.cmm Λ') := by
  sorry

end WallpaperGroups.Groups
