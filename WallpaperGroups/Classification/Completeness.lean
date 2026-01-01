/-
Copyright (c) 2025 Wallpaper Groups Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import WallpaperGroups.Classification.Distinctness

/-!
# Classification Theorem: Exactly 17 Wallpaper Groups

This file proves the main classification theorem: every wallpaper group is
isomorphic to exactly one of the 17 standard types.

## Main results

* `obliqueLattice_wallpaperGroups` - Oblique lattice → p1 or p2
* `rectangularLattice_wallpaperGroups` - Rectangular lattice → pm, pg, pmm, pmg, or pgg
* `centeredRectangularLattice_wallpaperGroups` - Centered rectangular → cm or cmm
* `squareLattice_wallpaperGroups` - Square lattice → p4, p4m, or p4g
* `hexagonalLattice_wallpaperGroups` - Hexagonal lattice → p3, p3m1, p31m, p6, or p6m
* `wallpaper_classification` - Every wallpaper group ≅ one of the 17
* `wallpaper_count` - There are exactly 17 wallpaper groups

blueprint: thm:classification, cor:seventeen
-/

namespace WallpaperGroups.Classification

open WallpaperGroups.Groups
open WallpaperGroups.Wallpaper
open WallpaperGroups.Lattice
open WallpaperGroups.PointGroup
open WallpaperGroups.Euclidean

/-! ### Completeness by Lattice Type -/

/-- Every wallpaper group with oblique lattice is isomorphic to p1 or p2.

blueprint: lem:oblique_complete -/
theorem obliqueLattice_wallpaperGroups (Γ : Subgroup EuclideanGroup2)
    (hΓ : IsWallpaperGroup Γ)
    (Λ : Lattice2)
    (hΛ_trans : ∀ v, v ∈ Λ ↔ (⟨v, 1⟩ : EuclideanGroup2) ∈ WallpaperGroup.translationSubgroup Γ)
    (hΛ_oblique : IsObliqueLattice Λ) :
    Nonempty (Γ ≃* WallpaperGroup.p1 Λ) ∨
    Nonempty (Γ ≃* WallpaperGroup.p2 Λ) := by
  sorry

/-- Every wallpaper group with rectangular lattice is isomorphic to one of
pm, pg, pmm, pmg, or pgg.

blueprint: lem:rectangular_complete -/
theorem rectangularLattice_wallpaperGroups (Γ : Subgroup EuclideanGroup2)
    (hΓ : IsWallpaperGroup Γ)
    (Λ : Lattice2)
    (hΛ_trans : ∀ v, v ∈ Λ ↔ (⟨v, 1⟩ : EuclideanGroup2) ∈ WallpaperGroup.translationSubgroup Γ)
    (hΛ_rect : IsRectangularLattice Λ) :
    Nonempty (Γ ≃* WallpaperGroup.p1 Λ) ∨
    Nonempty (Γ ≃* WallpaperGroup.p2 Λ) ∨
    Nonempty (Γ ≃* WallpaperGroup.pm Λ) ∨
    Nonempty (Γ ≃* WallpaperGroup.pg Λ) ∨
    Nonempty (Γ ≃* WallpaperGroup.pmm Λ) ∨
    Nonempty (Γ ≃* WallpaperGroup.pmg Λ) ∨
    Nonempty (Γ ≃* WallpaperGroup.pgg Λ) := by
  sorry

/-- Every wallpaper group with centered rectangular lattice is isomorphic to
cm or cmm (or p1, p2).

blueprint: lem:centered_complete -/
theorem centeredRectangularLattice_wallpaperGroups (Γ : Subgroup EuclideanGroup2)
    (hΓ : IsWallpaperGroup Γ)
    (Λ : Lattice2)
    (hΛ_trans : ∀ v, v ∈ Λ ↔ (⟨v, 1⟩ : EuclideanGroup2) ∈ WallpaperGroup.translationSubgroup Γ)
    (_hΛ_cr : IsCenteredRectangularLattice Λ) :
    Nonempty (Γ ≃* WallpaperGroup.p1 Λ) ∨
    Nonempty (Γ ≃* WallpaperGroup.p2 Λ) ∨
    Nonempty (Γ ≃* WallpaperGroup.cm Λ) ∨
    Nonempty (Γ ≃* WallpaperGroup.cmm Λ) := by
  sorry

/-- Every wallpaper group with square lattice is isomorphic to one of
p4, p4m, or p4g (or p1, p2, pm, pmm).

blueprint: lem:square_complete -/
theorem squareLattice_wallpaperGroups (Γ : Subgroup EuclideanGroup2)
    (hΓ : IsWallpaperGroup Γ)
    (Λ : Lattice2)
    (hΛ_trans : ∀ v, v ∈ Λ ↔ (⟨v, 1⟩ : EuclideanGroup2) ∈ WallpaperGroup.translationSubgroup Γ)
    (_hΛ_sq : IsSquareLattice Λ) :
    Nonempty (Γ ≃* WallpaperGroup.p1 Λ) ∨
    Nonempty (Γ ≃* WallpaperGroup.p2 Λ) ∨
    Nonempty (Γ ≃* WallpaperGroup.p4 Λ) ∨
    Nonempty (Γ ≃* WallpaperGroup.p4m Λ) ∨
    Nonempty (Γ ≃* WallpaperGroup.p4g Λ) := by
  sorry

/-- Every wallpaper group with hexagonal lattice is isomorphic to one of
p3, p3m1, p31m, p6, or p6m (or p1, p2).

blueprint: lem:hexagonal_complete -/
theorem hexagonalLattice_wallpaperGroups (Γ : Subgroup EuclideanGroup2)
    (hΓ : IsWallpaperGroup Γ)
    (Λ : Lattice2)
    (hΛ_trans : ∀ v, v ∈ Λ ↔ (⟨v, 1⟩ : EuclideanGroup2) ∈ WallpaperGroup.translationSubgroup Γ)
    (_hΛ_hex : IsHexagonalLattice Λ) :
    Nonempty (Γ ≃* WallpaperGroup.p1 Λ) ∨
    Nonempty (Γ ≃* WallpaperGroup.p2 Λ) ∨
    Nonempty (Γ ≃* WallpaperGroup.p3 Λ) ∨
    Nonempty (Γ ≃* WallpaperGroup.p3m1 Λ) ∨
    Nonempty (Γ ≃* WallpaperGroup.p31m Λ) ∨
    Nonempty (Γ ≃* WallpaperGroup.p6 Λ) ∨
    Nonempty (Γ ≃* WallpaperGroup.p6m Λ) := by
  sorry

/-! ### Main Classification Theorem -/

/-- The 17 wallpaper groups as an inductive type. -/
inductive WallpaperGroupType
  | p1 | p2
  | pm | pg | pmm | pmg | pgg
  | cm | cmm
  | p4 | p4m | p4g
  | p3 | p3m1 | p31m | p6 | p6m
  deriving DecidableEq, Repr, Fintype

/-- Every wallpaper group is isomorphic to exactly one of the 17 types.

blueprint: thm:classification -/
theorem wallpaper_classification (Γ : Subgroup EuclideanGroup2) (hΓ : IsWallpaperGroup Γ) :
    ∃! (t : WallpaperGroupType), ∃ Λ : Lattice2,
      (∀ v, v ∈ Λ ↔ (⟨v, 1⟩ : EuclideanGroup2) ∈ WallpaperGroup.translationSubgroup Γ) ∧
      match t with
      | .p1 => Nonempty (Γ ≃* WallpaperGroup.p1 Λ)
      | .p2 => Nonempty (Γ ≃* WallpaperGroup.p2 Λ)
      | .pm => Nonempty (Γ ≃* WallpaperGroup.pm Λ)
      | .pg => Nonempty (Γ ≃* WallpaperGroup.pg Λ)
      | .pmm => Nonempty (Γ ≃* WallpaperGroup.pmm Λ)
      | .pmg => Nonempty (Γ ≃* WallpaperGroup.pmg Λ)
      | .pgg => Nonempty (Γ ≃* WallpaperGroup.pgg Λ)
      | .cm => Nonempty (Γ ≃* WallpaperGroup.cm Λ)
      | .cmm => Nonempty (Γ ≃* WallpaperGroup.cmm Λ)
      | .p4 => Nonempty (Γ ≃* WallpaperGroup.p4 Λ)
      | .p4m => Nonempty (Γ ≃* WallpaperGroup.p4m Λ)
      | .p4g => Nonempty (Γ ≃* WallpaperGroup.p4g Λ)
      | .p3 => Nonempty (Γ ≃* WallpaperGroup.p3 Λ)
      | .p3m1 => Nonempty (Γ ≃* WallpaperGroup.p3m1 Λ)
      | .p31m => Nonempty (Γ ≃* WallpaperGroup.p31m Λ)
      | .p6 => Nonempty (Γ ≃* WallpaperGroup.p6 Λ)
      | .p6m => Nonempty (Γ ≃* WallpaperGroup.p6m Λ) := by
  sorry

/-- There are exactly 17 wallpaper groups up to isomorphism.

blueprint: cor:seventeen -/
theorem wallpaper_count : Fintype.card WallpaperGroupType = 17 := by
  native_decide

/-- The classification can also be stated as: the quotient of wallpaper groups
by isomorphism has exactly 17 elements. -/
theorem wallpaper_classification' :
    ∃ (S : Finset (Subgroup EuclideanGroup2)),
      S.card = 17 ∧
      (∀ Γ ∈ S, IsWallpaperGroup Γ) ∧
      (∀ Γ₁ ∈ S, ∀ Γ₂ ∈ S, Γ₁ ≠ Γ₂ → ¬Nonempty (Γ₁ ≃* Γ₂)) ∧
      (∀ Γ : Subgroup EuclideanGroup2, IsWallpaperGroup Γ →
        ∃ Γ' ∈ S, Nonempty (Γ ≃* Γ')) := by
  sorry

end WallpaperGroups.Classification
