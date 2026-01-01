/-
Copyright (c) 2025 Wallpaper Groups Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import WallpaperGroups.Wallpaper.Structure
import WallpaperGroups.Lattice.BravaisTypes

/-!
# Square Lattice Wallpaper Groups: p4, p4m, p4g

This file defines the three wallpaper groups with square lattices.

## Main definitions

* `WallpaperGroup.p4` - 4-fold rotations, PG = C₄, symmorphic
* `WallpaperGroup.p4m` - 4-fold rotations + reflections, PG = D₄, symmorphic
* `WallpaperGroup.p4g` - 4-fold rotations + glide reflections, PG = D₄, non-symmorphic

blueprint: def:p4, def:p4m, def:p4g
-/

namespace WallpaperGroups.Groups

open WallpaperGroups.Euclidean
open WallpaperGroups.Lattice
open WallpaperGroups.Wallpaper
open WallpaperGroups.PointGroup

variable (Λ : Lattice2) (hΛ : IsSquareLattice Λ)

/-- The wallpaper group p4 has 4-fold rotation symmetry.

- Lattice type: Square
- Point group: C₄ = {I, R_{π/2}, R_π, R_{3π/2}}
- Symmorphic: Yes
- No reflections, only rotations

blueprint: def:p4 -/
def WallpaperGroup.p4 : Subgroup EuclideanGroup2 where
  carrier := {g | ∃ (A : OrthogonalGroup2),
    A ∈ CyclicPointGroup 4 ∧
    g.right = A ∧
    g.left ∈ Λ}
  mul_mem' := by intro a b ha hb; sorry
  one_mem' := by sorry
  inv_mem' := by intro a ha; sorry

/-- p4 is a wallpaper group. -/
lemma WallpaperGroup.p4.isWallpaperGroup : IsWallpaperGroup (WallpaperGroup.p4 Λ) := by
  sorry

/-- p4 is symmorphic. -/
lemma WallpaperGroup.p4.isSymmorphic : IsSymmorphic (WallpaperGroup.p4 Λ) := by
  sorry

/-- The point group of p4 is C₄. -/
lemma WallpaperGroup.p4.pointGroup :
    Nonempty ((WallpaperGroup.pointGroup (WallpaperGroup.p4 Λ)) ≃* CyclicPointGroup 4) := by
  sorry

/-- The wallpaper group p4m has 4-fold rotation and reflection symmetry.

- Lattice type: Square
- Point group: D₄ (symmetries of a square)
- Symmorphic: Yes
- Reflections along axes and diagonals

blueprint: def:p4m -/
def WallpaperGroup.p4m : Subgroup EuclideanGroup2 where
  carrier := {g | ∃ (A : OrthogonalGroup2),
    A ∈ DihedralPointGroup 4 ∧
    g.right = A ∧
    g.left ∈ Λ}
  mul_mem' := by intro a b ha hb; sorry
  one_mem' := by sorry
  inv_mem' := by intro a ha; sorry

/-- p4m is a wallpaper group. -/
lemma WallpaperGroup.p4m.isWallpaperGroup : IsWallpaperGroup (WallpaperGroup.p4m Λ) := by
  sorry

/-- p4m is symmorphic. -/
lemma WallpaperGroup.p4m.isSymmorphic : IsSymmorphic (WallpaperGroup.p4m Λ) := by
  sorry

/-- The point group of p4m is D₄. -/
lemma WallpaperGroup.p4m.pointGroup :
    Nonempty ((WallpaperGroup.pointGroup (WallpaperGroup.p4m Λ)) ≃* DihedralPointGroup 4) := by
  sorry

/-- The wallpaper group p4g has 4-fold rotation and glide reflection symmetry.

- Lattice type: Square
- Point group: D₄
- Symmorphic: No
- Glide reflections along diagonals, no true diagonal reflections

blueprint: def:p4g -/
def WallpaperGroup.p4g (Λ : Lattice2) : Subgroup EuclideanGroup2 where
  carrier := {g | g.left ∈ Λ ∧ sorry}
  mul_mem' := by intro a b ha hb; sorry
  one_mem' := by sorry
  inv_mem' := by intro a ha; sorry

/-- p4g is a wallpaper group. -/
lemma WallpaperGroup.p4g.isWallpaperGroup : IsWallpaperGroup (WallpaperGroup.p4g Λ) := by
  sorry

/-- p4g is non-symmorphic. -/
lemma WallpaperGroup.p4g.not_isSymmorphic : ¬IsSymmorphic (WallpaperGroup.p4g Λ) := by
  sorry

/-- The point group of p4g is D₄. -/
lemma WallpaperGroup.p4g.pointGroup :
    Nonempty ((WallpaperGroup.pointGroup (WallpaperGroup.p4g Λ)) ≃* DihedralPointGroup 4) := by
  sorry

/-- p4, p4m, and p4g are the only wallpaper groups with square lattice. -/
lemma square_wallpaperGroups (Γ : Subgroup EuclideanGroup2) (hΓ : IsWallpaperGroup Γ)
    (Λ' : Lattice2)
    (hΛ' : ∀ v, v ∈ Λ' ↔ (⟨v, 1⟩ : EuclideanGroup2) ∈ WallpaperGroup.translationSubgroup Γ)
    (hsq : IsSquareLattice Λ') :
    Nonempty (Γ ≃* WallpaperGroup.p4 Λ') ∨
    Nonempty (Γ ≃* WallpaperGroup.p4m Λ') ∨
    Nonempty (Γ ≃* WallpaperGroup.p4g Λ') := by
  sorry

end WallpaperGroups.Groups
