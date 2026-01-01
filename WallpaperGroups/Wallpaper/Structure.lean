/-
Copyright (c) 2025 Wallpaper Groups Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import WallpaperGroups.Wallpaper.Definition
import WallpaperGroups.Lattice.Basic
import WallpaperGroups.Crystallographic.PointGroups

/-!
# Wallpaper Group Structure

This file develops the structure theory of wallpaper groups: the translation
lattice, point group, short exact sequence, and symmorphic/non-symmorphic
classification.

## Main definitions

* `WallpaperGroup.translationSubgroup` - TG(Γ) = {(v, I) ∈ Γ}
* `WallpaperGroup.pointGroup` - PG(Γ) = projection of Γ to O(2)
* `IsSymmorphic` - Γ ≅ TG(Γ) ⋊ PG(Γ) (short exact sequence splits)

## Main results

* `translationSubgroup_isLattice` - TG(Γ) is a rank-2 lattice
* `pointGroup_isCrystallographic` - PG(Γ) is one of the 10 crystallographic groups
* `wallpaper_ses` - Short exact sequence 1 → TG(Γ) → Γ → PG(Γ) → 1

blueprint: lem:wallpaper_ses
-/

namespace WallpaperGroups.Wallpaper

open WallpaperGroups.Euclidean
open WallpaperGroups.Lattice
open WallpaperGroups.Crystallographic
open WallpaperGroups.PointGroup

/-- The translation subgroup of a wallpaper group.

TG(Γ) = Γ ∩ T = {(v, I) ∈ Γ}

blueprint: def:wallpaper_translations -/
def WallpaperGroup.translationSubgroup (Γ : Subgroup EuclideanGroup2) :
    Subgroup EuclideanGroup2 :=
  Γ ⊓ Euclidean.translationSubgroup

/-- The translation subgroup is a lattice.

blueprint: lem:translation_is_lattice -/
lemma WallpaperGroup.translationSubgroup_isLattice (Γ : Subgroup EuclideanGroup2)
    (hΓ : IsWallpaperGroup Γ) :
    ∃ Λ : Lattice2, ∀ v : EuclideanPlane,
      v ∈ Λ ↔ EuclideanGroup2.mk v 1 ∈ WallpaperGroup.translationSubgroup Γ := by
  sorry

/-- The translation subgroup is normal in Γ.

blueprint: lem:wallpaper_translation_normal -/
lemma WallpaperGroup.translationSubgroup_normal (Γ : Subgroup EuclideanGroup2) :
    (WallpaperGroup.translationSubgroup Γ).Normal := by
  sorry

/-- The point group of a wallpaper group.

PG(Γ) is the image of Γ under the projection π : E(2) → O(2).

blueprint: def:wallpaper_point_group -/
def WallpaperGroup.pointGroup (Γ : Subgroup EuclideanGroup2) : Subgroup OrthogonalGroup2 where
  carrier := {A | ∃ v : EuclideanPlane, EuclideanGroup2.mk v A ∈ Γ}
  mul_mem' := by
    intro A B ⟨v, hv⟩ ⟨w, hw⟩
    use v + Matrix.toEuclideanLin A.1 w
    sorry
  one_mem' := by
    use 0
    sorry
  inv_mem' := by
    intro A ⟨v, hv⟩
    use -(Matrix.toEuclideanLin A⁻¹.1 v)
    sorry

/-- The point group is finite.

blueprint: lem:point_group_finite -/
lemma WallpaperGroup.pointGroup_finite (Γ : Subgroup EuclideanGroup2)
    (hΓ : IsWallpaperGroup Γ) :
    Finite (WallpaperGroup.pointGroup Γ) := by
  sorry

/-- The point group preserves the translation lattice.

blueprint: lem:point_group_preserves -/
lemma WallpaperGroup.pointGroup_preservesLattice (Γ : Subgroup EuclideanGroup2)
    (hΓ : IsWallpaperGroup Γ) (Λ : Lattice2)
    (hΛ : ∀ v, v ∈ Λ ↔ EuclideanGroup2.mk v 1 ∈ WallpaperGroup.translationSubgroup Γ) :
    ∀ A ∈ WallpaperGroup.pointGroup Γ, IsLatticePreserving Λ A := by
  sorry

/-- The point group is crystallographic.

blueprint: lem:point_group_crystallographic -/
lemma WallpaperGroup.pointGroup_isCrystallographic (Γ : Subgroup EuclideanGroup2)
    (hΓ : IsWallpaperGroup Γ) :
    IsCrystallographicPointGroup (WallpaperGroup.pointGroup Γ) := by
  sorry

/-- The short exact sequence for wallpaper groups.

1 → TG(Γ) → Γ → PG(Γ) → 1

blueprint: lem:wallpaper_ses -/
lemma WallpaperGroup.shortExactSequence (Γ : Subgroup EuclideanGroup2)
    (hΓ : IsWallpaperGroup Γ) :
    Function.Surjective (fun g : Γ => ⟨g.1.right, by
      use g.1.left
      exact g.2⟩ : Γ → WallpaperGroup.pointGroup Γ) := by
  sorry

/-- A wallpaper group is symmorphic if the short exact sequence splits.

Equivalently, Γ contains a subgroup isomorphic to PG(Γ) (a "point group copy").

blueprint: def:symmorphic -/
def IsSymmorphic (Γ : Subgroup EuclideanGroup2) : Prop :=
  ∃ (s : WallpaperGroup.pointGroup Γ →* Γ),
    ∀ A, (s A).1.right = A.1

/-- Symmorphic groups contain the origin-centered point group.

blueprint: lem:symmorphic_char -/
lemma isSymmorphic_iff (Γ : Subgroup EuclideanGroup2) (hΓ : IsWallpaperGroup Γ) :
    IsSymmorphic Γ ↔
    ∀ A ∈ WallpaperGroup.pointGroup Γ, EuclideanGroup2.mk 0 A ∈ Γ := by
  sorry

/-- Non-symmorphic groups necessarily contain glide reflections.

blueprint: lem:non_symmorphic_glide -/
lemma nonSymmorphic_hasGlideReflection (Γ : Subgroup EuclideanGroup2)
    (hΓ : IsWallpaperGroup Γ) (hns : ¬IsSymmorphic Γ) :
    ∃ g ∈ Γ, IsGlideReflection g := by
  sorry

/-- The kernel of the projection Γ → PG(Γ) is TG(Γ). -/
lemma WallpaperGroup.projection_ker (Γ : Subgroup EuclideanGroup2) :
    (WallpaperGroup.translationSubgroup Γ : Set EuclideanGroup2) =
    {g ∈ Γ | g.right = 1} := by
  sorry

/-- Two wallpaper groups are isomorphic iff they have isomorphic point groups,
translation lattices of the same Bravais type, and matching extension data. -/
lemma WallpaperGroup.isomorphism_criterion (Γ₁ Γ₂ : Subgroup EuclideanGroup2)
    (hΓ₁ : IsWallpaperGroup Γ₁) (hΓ₂ : IsWallpaperGroup Γ₂) :
    Nonempty (Γ₁ ≃* Γ₂) ↔
    Nonempty ((WallpaperGroup.pointGroup Γ₁) ≃* (WallpaperGroup.pointGroup Γ₂)) ∧
    (∃ Λ₁ Λ₂ : Lattice2,
      (∀ v, v ∈ Λ₁ ↔ EuclideanGroup2.mk v 1 ∈ WallpaperGroup.translationSubgroup Γ₁) ∧
      (∀ v, v ∈ Λ₂ ↔ EuclideanGroup2.mk v 1 ∈ WallpaperGroup.translationSubgroup Γ₂) ∧
      Λ₁.bravaisType = Λ₂.bravaisType) ∧
    (IsSymmorphic Γ₁ ↔ IsSymmorphic Γ₂) := by
  sorry

end WallpaperGroups.Wallpaper
