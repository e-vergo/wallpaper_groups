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

/-- The set of translation vectors in a subgroup Γ forms an AddSubgroup of ℝ². -/
def translationVectors (Γ : Subgroup EuclideanGroup2) : AddSubgroup EuclideanPlane where
  carrier := {v | EuclideanGroup2.mk v 1 ∈ Γ}
  add_mem' := by
    intro v w hv hw
    simp only [Set.mem_setOf_eq] at hv hw ⊢
    have hmul : EuclideanGroup2.mk v 1 * EuclideanGroup2.mk w 1 = EuclideanGroup2.mk (v + w) 1 := by
      apply SemidirectProduct.ext
      · simp only [SemidirectProduct.mul_left, EuclideanGroup2.mk]
        -- Need to show ofAdd v * (orthogonalActionHom 1) (ofAdd w) = ofAdd (v + w)
        simp only [map_one, MulAut.one_apply]
        rfl
      · simp only [SemidirectProduct.mul_right, EuclideanGroup2.mk, mul_one]
    rw [← hmul]
    exact Γ.mul_mem hv hw
  zero_mem' := by
    simp only [Set.mem_setOf_eq]
    have h : EuclideanGroup2.mk 0 1 = 1 := by
      apply SemidirectProduct.ext
      · simp only [SemidirectProduct.one_left, EuclideanGroup2.mk]; rfl
      · simp only [SemidirectProduct.one_right, EuclideanGroup2.mk]
    rw [h]
    exact Γ.one_mem
  neg_mem' := by
    intro v hv
    simp only [Set.mem_setOf_eq] at hv ⊢
    have hinv : (EuclideanGroup2.mk v 1)⁻¹ = EuclideanGroup2.mk (-v) 1 := by
      apply SemidirectProduct.ext
      · simp only [SemidirectProduct.inv_left, EuclideanGroup2.mk]
        -- Need: (orthogonalActionHom 1⁻¹) (ofAdd v)⁻¹ = ofAdd (-v)
        simp only [inv_one, map_one, MulAut.one_apply, ofAdd_neg]
      · simp only [SemidirectProduct.inv_right, EuclideanGroup2.mk, inv_one]
    rw [← hinv]
    exact Γ.inv_mem hv

/-- The translations in a discrete subgroup are discrete. -/
lemma translationVectors_discrete (Γ : Subgroup EuclideanGroup2)
    (hdisc : IsDiscreteSubgroup Γ) :
    ∀ x ∈ translationVectors Γ, x ≠ 0 →
      ∃ ε > 0, ∀ y ∈ translationVectors Γ, y ≠ x → ε ≤ ‖y - x‖ := by
  intro x hx hx_ne
  -- Get ε from discreteness of Γ
  obtain ⟨ε, hε_pos, hε_sep⟩ := hdisc
  -- We use ε as our separation constant
  use ε, hε_pos
  intro y hy hy_ne
  -- For any other y ∈ translationVectors Γ with y ≠ x
  -- We have y - x ∈ translationVectors Γ (since it's a subgroup)
  have hdiff_mem : y - x ∈ translationVectors Γ :=
    (translationVectors Γ).sub_mem hy hx
  -- If y ≠ x, then y - x ≠ 0
  have hdiff_ne : y - x ≠ 0 := sub_ne_zero.mpr hy_ne
  -- Apply discreteness to (y - x, 1)
  have hg_diff_mem : EuclideanGroup2.mk (y - x) 1 ∈ Γ := hdiff_mem
  have hg_diff_ne : EuclideanGroup2.mk (y - x) 1 ≠ 1 := by
    intro h
    have heq : (EuclideanGroup2.mk (y - x) 1).left = (1 : EuclideanGroup2).left :=
      congrArg SemidirectProduct.left h
    simp only [SemidirectProduct.one_left, EuclideanGroup2.mk] at heq
    have hdiff_eq : y - x = 0 := by
      have hteq : Multiplicative.toAdd (Multiplicative.ofAdd (y - x)) =
          Multiplicative.toAdd (1 : Multiplicative EuclideanPlane) :=
        congrArg Multiplicative.toAdd heq
      simp only [toAdd_ofAdd, toAdd_one] at hteq
      exact hteq
    exact hdiff_ne hdiff_eq
  have hε_sep_diff := hε_sep (EuclideanGroup2.mk (y - x) 1) hg_diff_mem hg_diff_ne
  cases hε_sep_diff with
  | inl h => exact h
  | inr h => simp only [EuclideanGroup2.mk, ne_eq, not_true] at h

/-- For a discrete subgroup, elements with orthogonal part = 1 are exactly translations.
This is essentially the definition, but stated as a lemma for clarity. -/
lemma mem_translationVectors_iff (Γ : Subgroup EuclideanGroup2) (v : EuclideanPlane) :
    v ∈ translationVectors Γ ↔ EuclideanGroup2.mk v 1 ∈ Γ := Iff.rfl

/-- Auxiliary lemma: extract a translation from an element with non-trivial rotation.

When g ∈ Γ has g.right ≠ 1, we can still find a pure translation in Γ.
This uses the fact that the point group is finite (from discreteness),
so some power of g.right equals 1. -/
lemma wallpaperGroup_has_nonzero_translation_aux (Γ : Subgroup EuclideanGroup2)
    (hdisc : IsDiscreteSubgroup Γ) (hcoc : IsCocompact Γ)
    (g : EuclideanGroup2) (hg_mem : g ∈ Γ)
    (hg_left_nonzero : Multiplicative.toAdd g.left ≠ 0)
    (hg_right : g.right ≠ 1) :
    ∃ w ∈ translationVectors Γ, w ≠ 0 := by
  -- The point group of a discrete subgroup is finite
  -- For any rotation/reflection A ≠ 1 in O(2), A^n = 1 for some n (finite order)
  -- Then g^n is a pure translation with translation vector ∑_{i=0}^{n-1} A^i v
  -- where v = toAdd g.left

  -- For now, we defer this to the point group structure theory
  -- The key facts needed are:
  -- 1. Discreteness implies point group is finite
  -- 2. Finite subgroups of O(2) are cyclic or dihedral
  -- 3. Every element has finite order

  -- A simpler approach: if g.right is a reflection, g.right² = 1
  -- So g² = (v + g.right v, 1) is a translation
  -- We need v + g.right v ≠ 0, which holds for "generic" v

  -- The full proof requires more infrastructure from PointGroup theory
  sorry

/-- A discrete cocompact subgroup has non-trivial translations.

The proof uses both discreteness (to control the point group) and
cocompactness (to cover distant points). -/
lemma wallpaperGroup_has_nonzero_translation (Γ : Subgroup EuclideanGroup2)
    (hΓ : IsWallpaperGroup Γ) :
    ∃ w ∈ translationVectors Γ, w ≠ 0 := by
  obtain ⟨hdisc, hcoc⟩ := hΓ
  obtain ⟨K, hK_compact, hK_cover⟩ := hcoc
  obtain ⟨R, hR⟩ := hK_compact.isBounded.subset_ball 0
  obtain ⟨ε, hε_pos, hε_sep⟩ := hdisc
  -- Strategy: consider points x at distance > R from origin
  -- The covering element g has x - g.left ∈ K, so g.left is not small
  -- If g.right = 1, we get a non-trivial translation directly
  -- If g.right ≠ 1, we need to combine multiple elements to get a translation

  -- Keep a copy of hK_cover before specializing
  have hK_cover_orig := hK_cover
  -- Key observation: consider the element covering a point far from origin
  -- We use R' = max R 0 + 1 to handle case R < 0
  let R' := max R 0 + 1
  let x : EuclideanPlane := EuclideanSpace.single (0 : Fin 2) (2 * R' + 1)
  obtain ⟨g, hg_mem, hg_cover⟩ := hK_cover x
  -- g.left must be large: ‖g.left‖ > R'
  have hR'_pos : R' > 0 := by
    simp only [R']
    have : max R 0 ≥ 0 := le_max_right R 0
    linarith
  have hR_le_R' : R ≤ R' := by
    simp only [R']
    have : max R 0 ≥ R := le_max_left R 0
    linarith
  have hg_left_large : ‖Multiplicative.toAdd g.left‖ > R' := by
    by_contra h
    push_neg at h
    -- x - g.left ∈ K ⊆ ball 0 R ⊆ ball 0 R' (since R ≤ R')
    have hK_in_ball_R' : K ⊆ Metric.ball (0 : EuclideanPlane) R' := by
      intro y hy
      have hy_R := hR hy
      rw [Metric.mem_ball] at hy_R ⊢
      calc dist y 0 < R := hy_R
           _ ≤ R' := hR_le_R'
    have hk_in_ball : x - Multiplicative.toAdd g.left ∈ Metric.ball (0 : EuclideanPlane) R' :=
      hK_in_ball_R' hg_cover
    rw [Metric.mem_ball, dist_zero_right] at hk_in_ball
    -- ‖x‖ = 2R' + 1, so ‖x - g.left‖ ≥ 2R' + 1 - R' = R' + 1 > R'
    have hx_norm : ‖x‖ = 2 * R' + 1 := by
      simp only [x, EuclideanSpace.norm_single, Real.norm_eq_abs]
      rw [abs_of_pos]; linarith
    have hnorm_bound : ‖x - Multiplicative.toAdd g.left‖ ≥ R' + 1 := by
      have h1 : ‖x - Multiplicative.toAdd g.left‖ ≥ ‖x‖ - ‖Multiplicative.toAdd g.left‖ := by
        have := norm_sub_norm_le x (Multiplicative.toAdd g.left)
        linarith
      calc ‖x - Multiplicative.toAdd g.left‖
          ≥ ‖x‖ - ‖Multiplicative.toAdd g.left‖ := h1
          _ = (2 * R' + 1) - ‖Multiplicative.toAdd g.left‖ := by rw [hx_norm]
          _ ≥ (2 * R' + 1) - R' := by linarith
          _ = R' + 1 := by ring
    linarith
  -- Now we have g ∈ Γ with ‖g.left‖ > R' > 0
  have hg_left_nonzero : Multiplicative.toAdd g.left ≠ 0 := by
    intro h
    rw [h, norm_zero] at hg_left_large
    linarith
  -- Case split on whether g.right = 1
  by_cases hg_right : g.right = 1
  · -- g is a pure translation with non-zero translation vector
    use Multiplicative.toAdd g.left
    constructor
    · -- g.left ∈ translationVectors Γ
      simp only [translationVectors]
      have hg_eq : g = EuclideanGroup2.mk (Multiplicative.toAdd g.left) 1 := by
        apply SemidirectProduct.ext
        · simp only [EuclideanGroup2.mk, ofAdd_toAdd]
        · exact hg_right
      rw [hg_eq] at hg_mem
      exact hg_mem
    · exact hg_left_nonzero
  · -- g.right ≠ 1, so g is not a pure translation
    -- Key insight: if g.right is a reflection (order 2), then g² is a pure translation
    -- If g.right is a rotation by angle θ, then for some n, (g.right)^n = 1
    --   and g^n is a pure translation
    -- In either case, discreteness of Γ ensures the point group is finite
    --   (only finitely many rotations can exist without accumulating at identity)

    -- For a reflection A, we have A² = 1, so g² = (v + Av, 1)
    -- where v = toAdd g.left
    -- We need to show v + Av ≠ 0

    -- Technical approach: use discreteness to show point group is finite,
    -- then take appropriate power of g to get a pure translation.
    -- This requires infrastructure about finite subgroups of O(2).

    -- Alternative: cover a second point in a perpendicular direction,
    -- get another element h, and use combinations of g and h to extract translations.

    -- The detailed proof requires:
    -- 1. Finiteness of point group (from discreteness) - see WallpaperGroup.pointGroup_finite
    -- 2. Structure of finite subgroups of O(2) (cyclic or dihedral)
    -- 3. Existence of non-trivial powers that become identity in point group

    -- Defer to the point group finiteness result
    -- Reconstruct discreteness and cocompactness from components
    have hdisc' : IsDiscreteSubgroup Γ := ⟨ε, hε_pos, hε_sep⟩
    have hcoc' : IsCocompact Γ := ⟨K, hK_compact, hK_cover_orig⟩
    exact wallpaperGroup_has_nonzero_translation_aux Γ hdisc' hcoc' g hg_mem
      hg_left_nonzero hg_right

/-- A discrete cocompact subgroup of E(2) has translations spanning the plane. -/
lemma wallpaperGroup_translations_span (Γ : Subgroup EuclideanGroup2)
    (hΓ : IsWallpaperGroup Γ) :
    Submodule.span ℝ (translationVectors Γ : Set EuclideanPlane) = ⊤ := by
  -- The translations span ℝ² because:
  -- 1. For any direction, cocompactness forces translations in that direction
  -- 2. Discreteness means these translations are non-trivial
  -- 3. Taking two linearly independent directions gives generators
  obtain ⟨hdisc, hcoc⟩ := hΓ
  -- We use the standard basis e₁, e₂ of ℝ²
  -- For each, cocompactness gives us translations approximately in those directions
  sorry

/-- Two linearly independent translations exist in a wallpaper group. -/
lemma wallpaperGroup_has_independent_translations (Γ : Subgroup EuclideanGroup2)
    (hΓ : IsWallpaperGroup Γ) :
    ∃ a b : EuclideanPlane, LinearIndependent ℝ ![a, b] ∧
      a ∈ translationVectors Γ ∧ b ∈ translationVectors Γ := by
  -- Extract two independent translations from the spanning property
  have hspan := wallpaperGroup_translations_span Γ hΓ
  -- The span being ⊤ means there exist generators
  -- We need to extract two independent elements from the additive subgroup
  -- This uses the fact that the span equals the whole space
  sorry

/-- The translation vectors of a wallpaper group equal the closure of two generators. -/
lemma wallpaperGroup_translations_eq_closure (Γ : Subgroup EuclideanGroup2)
    (hΓ : IsWallpaperGroup Γ) :
    ∃ a b : EuclideanPlane, LinearIndependent ℝ ![a, b] ∧
      translationVectors Γ = AddSubgroup.closure {a, b} := by
  -- The translation subgroup is generated by two independent vectors
  -- This follows from:
  -- 1. Discreteness: the subgroup is a Z-lattice
  -- 2. Spanning: it spans ℝ² over ℝ
  -- 3. Standard structure theory: such a subgroup is free abelian of rank 2
  obtain ⟨a, b, hind, ha, hb⟩ := wallpaperGroup_has_independent_translations Γ hΓ
  use a, b, hind
  -- The closure of {a, b} equals translationVectors Γ
  -- This is the key: any discrete subgroup of ℝ² that spans ℝ²
  -- is generated by exactly two elements
  sorry

/-- If Γ is a wallpaper group, then its translation subgroup forms a rank-2 lattice.

Note: The converse is FALSE without additional hypotheses. A subgroup with a rank-2
lattice of translations but with non-discrete point group (e.g., containing all rotations)
would not be a wallpaper group. -/
lemma wallpaperGroup_translation_isLattice (Γ : Subgroup EuclideanGroup2)
    (hΓ : IsWallpaperGroup Γ) :
    ∃ (Λ : WallpaperGroups.Lattice.Lattice2),
      ∀ v : EuclideanPlane, v ∈ Λ ↔ EuclideanGroup2.mk v 1 ∈ Γ := by
  -- Get the two independent generators
  obtain ⟨a, b, hind, hgen⟩ := wallpaperGroup_translations_eq_closure Γ hΓ
  -- Get discreteness
  have hT_discrete := translationVectors_discrete Γ hΓ.discrete
  -- Construct the Lattice2
  refine ⟨⟨translationVectors Γ, ⟨a, b, hind, hgen⟩, hT_discrete⟩, ?_⟩
  -- Show the membership equivalence
  intro v
  rfl

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
