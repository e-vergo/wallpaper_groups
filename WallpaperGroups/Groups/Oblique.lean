/-
Copyright (c) 2025 Wallpaper Groups Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import WallpaperGroups.Wallpaper.Structure
import WallpaperGroups.Lattice.BravaisTypes

/-!
# Oblique Lattice Wallpaper Groups: p1 and p2

This file defines the two wallpaper groups with oblique lattices.

## Main definitions

* `WallpaperGroup.p1` - Translations only, PG = C₁
* `WallpaperGroup.p2` - Translations + 180° rotation, PG = C₂

Both groups are symmorphic.

blueprint: def:p1, def:p2
-/

namespace WallpaperGroups.Groups

open WallpaperGroups.Euclidean
open WallpaperGroups.Lattice
open WallpaperGroups.Wallpaper
open WallpaperGroups.PointGroup

variable (Λ : Lattice2)

/-- The wallpaper group p1 has only translations.

- Lattice type: Any (typically oblique)
- Point group: C₁ = {I}
- Symmorphic: Yes
- Generators: Two independent translations

This is the simplest wallpaper group, isomorphic to ℤ².

blueprint: def:p1 -/
def WallpaperGroup.p1 : Subgroup EuclideanGroup2 where
  carrier := {g | g.right = 1 ∧ g.left ∈ Λ}
  mul_mem' := by
    intro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    constructor
    · simp [SemidirectProduct.mul_right, ha1, hb1]
    · sorry
  one_mem' := by
    constructor
    · simp [SemidirectProduct.one_right]
    · exact Λ.zero_mem
  inv_mem' := by
    intro a ⟨ha1, ha2⟩
    constructor
    · simp [SemidirectProduct.inv_right, ha1]
    · sorry

/-- p1 is a wallpaper group. -/
lemma WallpaperGroup.p1.isWallpaperGroup (hΛ : IsObliqueLattice Λ ∨ IsRectangularLattice Λ ∨
    IsCenteredRectangularLattice Λ ∨ IsSquareLattice Λ ∨ IsHexagonalLattice Λ) :
    IsWallpaperGroup (WallpaperGroup.p1 Λ) := by
  sorry

/-- p1 is symmorphic. -/
lemma WallpaperGroup.p1.isSymmorphic : IsSymmorphic (WallpaperGroup.p1 Λ) := by
  sorry

/-- The point group of p1 is C₁. -/
lemma WallpaperGroup.p1.pointGroup :
    Nonempty ((WallpaperGroup.pointGroup (WallpaperGroup.p1 Λ)) ≃* CyclicPointGroup 1) := by
  sorry

/-- The wallpaper group p2 has translations and 180° rotation.

- Lattice type: Any (typically oblique)
- Point group: C₂ = {I, R_π}
- Symmorphic: Yes
- Generators: Two translations + 180° rotation

blueprint: def:p2 -/
def WallpaperGroup.p2 : Subgroup EuclideanGroup2 where
  carrier := {g | (g.right = 1 ∨ g.right = rotationMatrix' Real.pi) ∧
                   (g.right = 1 → g.left ∈ Λ) ∧
                   (g.right = rotationMatrix' Real.pi → ∃ v ∈ Λ, g.left = v)}
  mul_mem' := by
    intro a b ha hb
    sorry
  one_mem' := by
    constructor
    · left; simp [SemidirectProduct.one_right]
    constructor
    · intro _; exact Λ.zero_mem
    · intro h; sorry
  inv_mem' := by
    intro a ha
    sorry

/-- p2 is a wallpaper group. -/
lemma WallpaperGroup.p2.isWallpaperGroup :
    IsWallpaperGroup (WallpaperGroup.p2 Λ) := by
  sorry

/-- p2 is symmorphic. -/
lemma WallpaperGroup.p2.isSymmorphic : IsSymmorphic (WallpaperGroup.p2 Λ) := by
  sorry

/-- The point group of p2 is C₂. -/
lemma WallpaperGroup.p2.pointGroup :
    Nonempty ((WallpaperGroup.pointGroup (WallpaperGroup.p2 Λ)) ≃* CyclicPointGroup 2) := by
  sorry

/-- p1 and p2 are the only wallpaper groups with oblique lattice. -/
lemma oblique_wallpaperGroups (Γ : Subgroup EuclideanGroup2) (hΓ : IsWallpaperGroup Γ)
    (Λ' : Lattice2)
    (hΛ' : ∀ v, v ∈ Λ' ↔ (⟨v, 1⟩ : EuclideanGroup2) ∈ WallpaperGroup.translationSubgroup Γ)
    (hoblique : IsObliqueLattice Λ') :
    Nonempty (Γ ≃* WallpaperGroup.p1 Λ') ∨ Nonempty (Γ ≃* WallpaperGroup.p2 Λ') := by
  sorry

end WallpaperGroups.Groups
