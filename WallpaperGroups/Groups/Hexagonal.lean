/-
Copyright (c) 2025 Wallpaper Groups Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import WallpaperGroups.Wallpaper.Structure
import WallpaperGroups.Lattice.BravaisTypes

/-!
# Hexagonal Lattice Wallpaper Groups: p3, p3m1, p31m, p6, p6m

This file defines the five wallpaper groups with hexagonal lattices.

## Main definitions

* `WallpaperGroup.p3` - 3-fold rotations only, PG = C₃
* `WallpaperGroup.p3m1` - 3-fold + reflections through lattice points, PG = D₃
* `WallpaperGroup.p31m` - 3-fold + reflections between lattice points, PG = D₃
* `WallpaperGroup.p6` - 6-fold rotations, PG = C₆
* `WallpaperGroup.p6m` - 6-fold + reflections, PG = D₆

All are symmorphic. The distinction between p3m1 and p31m is the position of
reflection axes relative to lattice points.

blueprint: def:p3, def:p3m1, def:p31m, def:p6, def:p6m
-/

namespace WallpaperGroups.Groups

open WallpaperGroups.Euclidean
open WallpaperGroups.Lattice
open WallpaperGroups.Wallpaper
open WallpaperGroups.PointGroup

variable (Λ : Lattice2) (hΛ : IsHexagonalLattice Λ)

/-- The wallpaper group p3 has 3-fold rotation symmetry.

- Lattice type: Hexagonal
- Point group: C₃ = {I, R_{2π/3}, R_{4π/3}}
- Symmorphic: Yes
- No reflections

blueprint: def:p3 -/
def WallpaperGroup.p3 : Subgroup EuclideanGroup2 where
  carrier := {g | ∃ (A : OrthogonalGroup2),
    A ∈ CyclicPointGroup 3 ∧
    g.right = A ∧
    g.left ∈ Λ}
  mul_mem' := by intro a b ha hb; sorry
  one_mem' := by sorry
  inv_mem' := by intro a ha; sorry

/-- p3 is a wallpaper group. -/
lemma WallpaperGroup.p3.isWallpaperGroup : IsWallpaperGroup (WallpaperGroup.p3 Λ) := by
  sorry

/-- p3 is symmorphic. -/
lemma WallpaperGroup.p3.isSymmorphic : IsSymmorphic (WallpaperGroup.p3 Λ) := by
  sorry

/-- The point group of p3 is C₃. -/
lemma WallpaperGroup.p3.pointGroup :
    Nonempty ((WallpaperGroup.pointGroup (WallpaperGroup.p3 Λ)) ≃* CyclicPointGroup 3) := by
  sorry

/-- The wallpaper group p3m1 has 3-fold rotation and reflections through lattice points.

- Lattice type: Hexagonal
- Point group: D₃
- Symmorphic: Yes
- Reflection axes pass through lattice points

The "1" in p3m1 indicates the reflection axes pass through the 3-fold rotation centers.

blueprint: def:p3m1 -/
def WallpaperGroup.p3m1 : Subgroup EuclideanGroup2 where
  carrier := {g | ∃ (A : OrthogonalGroup2),
    A ∈ DihedralPointGroup 3 ∧
    g.right = A ∧
    g.left ∈ Λ}
  mul_mem' := by intro a b ha hb; sorry
  one_mem' := by sorry
  inv_mem' := by intro a ha; sorry

/-- p3m1 is a wallpaper group. -/
lemma WallpaperGroup.p3m1.isWallpaperGroup : IsWallpaperGroup (WallpaperGroup.p3m1 Λ) := by
  sorry

/-- p3m1 is symmorphic. -/
lemma WallpaperGroup.p3m1.isSymmorphic : IsSymmorphic (WallpaperGroup.p3m1 Λ) := by
  sorry

/-- The point group of p3m1 is D₃. -/
lemma WallpaperGroup.p3m1.pointGroup :
    Nonempty ((WallpaperGroup.pointGroup (WallpaperGroup.p3m1 Λ)) ≃* DihedralPointGroup 3) := by
  sorry

/-- The wallpaper group p31m has 3-fold rotation and reflections between lattice points.

- Lattice type: Hexagonal
- Point group: D₃
- Symmorphic: Yes
- Reflection axes pass between lattice points (at centers of edges)

The "1" in p31m indicates the reflection axes do NOT pass through 3-fold centers.

blueprint: def:p31m -/
def WallpaperGroup.p31m (Λ : Lattice2) : Subgroup EuclideanGroup2 where
  carrier := {g | g.left ∈ Λ ∧ sorry}
  mul_mem' := by intro a b ha hb; sorry
  one_mem' := by sorry
  inv_mem' := by intro a ha; sorry

/-- p31m is a wallpaper group. -/
lemma WallpaperGroup.p31m.isWallpaperGroup : IsWallpaperGroup (WallpaperGroup.p31m Λ) := by
  sorry

/-- p31m is symmorphic. -/
lemma WallpaperGroup.p31m.isSymmorphic : IsSymmorphic (WallpaperGroup.p31m Λ) := by
  sorry

/-- The point group of p31m is D₃. -/
lemma WallpaperGroup.p31m.pointGroup :
    Nonempty ((WallpaperGroup.pointGroup (WallpaperGroup.p31m Λ)) ≃* DihedralPointGroup 3) := by
  sorry

/-- p3m1 and p31m are non-isomorphic despite having the same point group.

They differ in the position of reflection axes relative to lattice points.
In p3m1, all 3-fold centers lie on reflection axes.
In p31m, 3-fold centers at lattice points do NOT lie on reflection axes. -/
lemma p3m1_not_iso_p31m : ¬Nonempty ((WallpaperGroup.p3m1 Λ) ≃* (WallpaperGroup.p31m Λ)) := by
  sorry

/-- The wallpaper group p6 has 6-fold rotation symmetry.

- Lattice type: Hexagonal
- Point group: C₆ = {I, R_{π/3}, R_{2π/3}, R_π, R_{4π/3}, R_{5π/3}}
- Symmorphic: Yes
- No reflections

blueprint: def:p6 -/
def WallpaperGroup.p6 : Subgroup EuclideanGroup2 where
  carrier := {g | ∃ (A : OrthogonalGroup2),
    A ∈ CyclicPointGroup 6 ∧
    g.right = A ∧
    g.left ∈ Λ}
  mul_mem' := by intro a b ha hb; sorry
  one_mem' := by sorry
  inv_mem' := by intro a ha; sorry

/-- p6 is a wallpaper group. -/
lemma WallpaperGroup.p6.isWallpaperGroup : IsWallpaperGroup (WallpaperGroup.p6 Λ) := by
  sorry

/-- p6 is symmorphic. -/
lemma WallpaperGroup.p6.isSymmorphic : IsSymmorphic (WallpaperGroup.p6 Λ) := by
  sorry

/-- The point group of p6 is C₆. -/
lemma WallpaperGroup.p6.pointGroup :
    Nonempty ((WallpaperGroup.pointGroup (WallpaperGroup.p6 Λ)) ≃* CyclicPointGroup 6) := by
  sorry

/-- The wallpaper group p6m has full hexagonal symmetry.

- Lattice type: Hexagonal
- Point group: D₆ (symmetries of a regular hexagon)
- Symmorphic: Yes
- This is the most symmetric wallpaper group

blueprint: def:p6m -/
def WallpaperGroup.p6m : Subgroup EuclideanGroup2 where
  carrier := {g | ∃ (A : OrthogonalGroup2),
    A ∈ DihedralPointGroup 6 ∧
    g.right = A ∧
    g.left ∈ Λ}
  mul_mem' := by intro a b ha hb; sorry
  one_mem' := by sorry
  inv_mem' := by intro a ha; sorry

/-- p6m is a wallpaper group. -/
lemma WallpaperGroup.p6m.isWallpaperGroup : IsWallpaperGroup (WallpaperGroup.p6m Λ) := by
  sorry

/-- p6m is symmorphic. -/
lemma WallpaperGroup.p6m.isSymmorphic : IsSymmorphic (WallpaperGroup.p6m Λ) := by
  sorry

/-- The point group of p6m is D₆. -/
lemma WallpaperGroup.p6m.pointGroup :
    Nonempty ((WallpaperGroup.pointGroup (WallpaperGroup.p6m Λ)) ≃* DihedralPointGroup 6) := by
  sorry

/-- The five hexagonal wallpaper groups are complete. -/
lemma hexagonal_wallpaperGroups (Γ : Subgroup EuclideanGroup2) (hΓ : IsWallpaperGroup Γ)
    (Λ' : Lattice2)
    (hΛ' : ∀ v, v ∈ Λ' ↔ (⟨v, 1⟩ : EuclideanGroup2) ∈ WallpaperGroup.translationSubgroup Γ)
    (hhex : IsHexagonalLattice Λ') :
    Nonempty (Γ ≃* WallpaperGroup.p3 Λ') ∨
    Nonempty (Γ ≃* WallpaperGroup.p3m1 Λ') ∨
    Nonempty (Γ ≃* WallpaperGroup.p31m Λ') ∨
    Nonempty (Γ ≃* WallpaperGroup.p6 Λ') ∨
    Nonempty (Γ ≃* WallpaperGroup.p6m Λ') := by
  sorry

end WallpaperGroups.Groups
