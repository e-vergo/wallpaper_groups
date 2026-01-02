/-
Copyright (c) 2025 Wallpaper Groups Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import WallpaperGroups.Euclidean.EuclideanGroup
import WallpaperGroups.Lattice.Basic

/-!
# Wallpaper Group Definition

This file defines wallpaper groups as discrete cocompact subgroups of E(2).

## Main definitions

* `IsDiscreteSubgroup` - A subgroup with discrete topology
* `IsCocompact` - The quotient space is compact
* `IsWallpaperGroup` - Discrete AND cocompact

## Overview

A wallpaper group (plane crystallographic group) is a subgroup Γ ⊂ E(2) that is:
1. Discrete: has the discrete topology
2. Cocompact: the quotient ℝ²/Γ is compact

These are the symmetry groups of periodic patterns in the plane.
-/

namespace WallpaperGroups.Wallpaper

open WallpaperGroups.Euclidean

/-- A subgroup Γ ⊂ E(2) is discrete if it has the discrete topology.

Equivalently, there is a neighborhood of the identity containing only the identity.

blueprint: def:discrete_subgroup -/
def IsDiscreteSubgroup (Γ : Subgroup EuclideanGroup2) : Prop :=
  ∃ ε > 0, ∀ g ∈ Γ, g ≠ 1 → ε ≤ ‖g.left‖ ∨ g.right ≠ 1

/-- A subgroup Γ ⊂ E(2) acts cocompactly if the quotient ℝ²/Γ is compact.

This means there exists a compact fundamental domain for the action.

blueprint: def:cocompact_subgroup -/
def IsCocompact (Γ : Subgroup EuclideanGroup2) : Prop :=
  ∃ (K : Set EuclideanPlane), IsCompact K ∧
    ∀ x : EuclideanPlane, ∃ g ∈ Γ, x - Multiplicative.toAdd g.left ∈ K

/-- A wallpaper group is a discrete cocompact subgroup of E(2).

blueprint: def:wallpaper_group -/
structure IsWallpaperGroup (Γ : Subgroup EuclideanGroup2) : Prop where
  /-- The subgroup is discrete. -/
  discrete : IsDiscreteSubgroup Γ
  /-- The subgroup acts cocompactly. -/
  cocompact : IsCocompact Γ

/-- Alternative characterization: Γ is a wallpaper group iff its translation
subgroup is a rank-2 lattice. -/
lemma isWallpaperGroup_iff_translation_isLattice (Γ : Subgroup EuclideanGroup2) :
    IsWallpaperGroup Γ ↔
    ∃ (Λ : WallpaperGroups.Lattice.Lattice2),
      ∀ v : EuclideanPlane, v ∈ Λ ↔ EuclideanGroup2.mk v 1 ∈ Γ := by
  sorry

/-- The trivial subgroup is not a wallpaper group (not cocompact). -/
lemma not_isWallpaperGroup_bot : ¬IsWallpaperGroup (⊥ : Subgroup EuclideanGroup2) := by
  intro ⟨_, hcoc⟩
  -- Get the compact set K and its property
  obtain ⟨K, hK_compact, hK_cover⟩ := hcoc
  -- K is compact, so it's bounded
  obtain ⟨R, hR⟩ := hK_compact.isBounded.subset_ball 0
  -- Take a point x with ‖x‖ > R
  specialize hK_cover (EuclideanSpace.single 0 (R + 1))
  obtain ⟨g, hg_mem, hg_in_K⟩ := hK_cover
  -- g ∈ ⊥ means g = 1
  rw [Subgroup.mem_bot] at hg_mem
  simp only [hg_mem] at hg_in_K
  -- So x - 0 = x ∈ K
  simp only [SemidirectProduct.one_left, toAdd_one, sub_zero] at hg_in_K
  -- But x ∉ ball 0 R since ‖x‖ = R + 1 > R
  have hx_in_ball : EuclideanSpace.single 0 (R + 1) ∈ Metric.ball (0 : EuclideanPlane) R :=
    hR hg_in_K
  rw [Metric.mem_ball] at hx_in_ball
  simp only [dist_zero_right] at hx_in_ball
  -- ‖single 0 (R+1)‖ = ‖R+1‖
  have hnorm : ‖EuclideanSpace.single (0 : Fin 2) (R + 1)‖ = ‖R + 1‖ :=
    EuclideanSpace.norm_single 0 (R + 1)
  rw [hnorm, Real.norm_eq_abs] at hx_in_ball
  -- |R + 1| > R for any R
  have h : |R + 1| > R := by
    obtain hpos | hneg := le_or_gt 0 (R + 1)
    · rw [abs_of_nonneg hpos]; linarith
    · rw [abs_of_neg (by linarith : R + 1 < 0)]; linarith
  linarith

/-- E(2) itself is not a wallpaper group (not discrete). -/
lemma not_isWallpaperGroup_top : ¬IsWallpaperGroup (⊤ : Subgroup EuclideanGroup2) := by
  intro ⟨hdisc, _⟩
  -- Get ε from discreteness
  obtain ⟨ε, hε_pos, hε_sep⟩ := hdisc
  -- Consider the translation by (ε/2, 0)
  let v : EuclideanPlane := EuclideanSpace.single 0 (ε / 2)
  let g : EuclideanGroup2 := EuclideanGroup2.mk v 1
  -- g ∈ ⊤
  have hg_mem : g ∈ (⊤ : Subgroup EuclideanGroup2) := Subgroup.mem_top g
  -- g ≠ 1
  have hg_ne : g ≠ 1 := by
    intro h
    have heq : g.left = (1 : EuclideanGroup2).left := congrArg SemidirectProduct.left h
    simp only [SemidirectProduct.one_left] at heq
    -- g.left = Multiplicative.ofAdd v, and (1 : EuclideanGroup2).left = 1 = ofAdd 0
    have hv_eq : v = 0 := by
      have hteq : Multiplicative.toAdd g.left =
          Multiplicative.toAdd (1 : Multiplicative EuclideanPlane) :=
        congrArg Multiplicative.toAdd heq
      simp only [toAdd_one] at hteq
      change Multiplicative.toAdd (Multiplicative.ofAdd v) = 0 at hteq
      simp only [toAdd_ofAdd] at hteq
      exact hteq
    -- But v = single 0 (ε/2) ≠ 0 since ε > 0
    have hv_ne : v ≠ 0 := by
      intro hv0
      have hnorm : ‖v‖ = 0 := by rw [hv0]; simp
      rw [EuclideanSpace.norm_single, Real.norm_eq_abs,
          abs_of_pos (by linarith : ε / 2 > 0)] at hnorm
      linarith
    exact hv_ne hv_eq
  -- Apply discreteness
  specialize hε_sep g hg_mem hg_ne
  -- g.right = 1 so we need ε ≤ ‖g.left‖
  have hg_right : g.right = 1 := rfl
  cases hε_sep with
  | inl h =>
    -- ε ≤ ‖g.left‖ = ‖v‖ = |ε/2| = ε/2 (since ε > 0)
    -- g.left = Multiplicative.ofAdd v, and ‖Multiplicative.ofAdd v‖ = ‖v‖
    have hnorm_eq : ‖g.left‖ = ‖v‖ := rfl
    have hnorm : ‖v‖ = ‖ε / 2‖ := EuclideanSpace.norm_single 0 (ε / 2)
    rw [hnorm_eq, hnorm, Real.norm_eq_abs, abs_of_pos (by linarith : ε / 2 > 0)] at h
    linarith
  | inr h =>
    exact h hg_right

end WallpaperGroups.Wallpaper
