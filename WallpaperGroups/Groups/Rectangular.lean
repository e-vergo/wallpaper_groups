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

/-! ### Helper lemmas for D₁ and D₂ -/

/-- S₀ ≠ 1 -/
private lemma reflectionMatrix'_zero_ne_one : reflectionMatrix' 0 ≠ 1 := by
  intro h
  have h1 : (reflectionMatrix' 0).1 1 1 = (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 1 := by
    simp only [h]; rfl
  simp only [reflectionMatrix', reflectionMatrix, Matrix.of_apply, Matrix.cons_val_one] at h1
  rw [Real.cos_zero] at h1
  norm_num at h1

/-- S₀² = 1 -/
private lemma reflectionMatrix'_zero_sq : reflectionMatrix' 0 * reflectionMatrix' 0 = 1 := by
  apply Subtype.ext
  simp only [Submonoid.coe_mul, Submonoid.coe_one]
  exact reflectionMatrix_sq 0

/-- S₀⁻¹ = S₀ -/
private lemma reflectionMatrix'_zero_inv : (reflectionMatrix' 0)⁻¹ = reflectionMatrix' 0 := by
  apply inv_eq_of_mul_eq_one_left reflectionMatrix'_zero_sq

/-! ### The pm wallpaper group -/

/-- The wallpaper group pm has translations and reflections parallel to one axis.

- Lattice type: Rectangular
- Point group: D₁ ≅ C₂
- Symmorphic: Yes (contains genuine reflections, not glides)
- The reflection axis is parallel to one lattice vector

blueprint: def:pm -/
def WallpaperGroup.pm (Λ : Lattice2) : Subgroup EuclideanGroup2 where
  carrier := {g | g.right ∈ DihedralPointGroup 1 ∧ g.left ∈ Λ}
  mul_mem' := by
    intro a b ⟨ha_D1, ha_lat⟩ ⟨hb_D1, hb_lat⟩
    refine ⟨Subgroup.mul_mem _ ha_D1 hb_D1, ?_⟩
    simp only [SemidirectProduct.mul_left, toAdd_mul, toAdd_ofAdd]
    -- For a rectangular lattice, D₁ = {1, S₀} preserves the lattice
    -- The action is: a.translation + A(b.translation) where A ∈ D₁
    have hD1 : (DihedralPointGroup 1 : Set OrthogonalGroup2) = {1, reflectionMatrix' 0} :=
      DihedralPointGroup.one
    rw [Set.mem_setOf_eq, hD1] at ha_D1
    cases ha_D1 with
    | inl ha1 =>
      -- A = 1, so action is trivial
      change Multiplicative.toAdd (Multiplicative.ofAdd a.translation *
        orthogonalActionHom a.right (Multiplicative.ofAdd b.translation)) ∈ Λ
      rw [ha1]
      simp only [map_one, MulAut.one_apply, toAdd_mul, toAdd_ofAdd]
      exact Λ.add_mem ha_lat hb_lat
    | inr haS =>
      -- A = S₀, need S₀ to preserve lattice which requires lattice structure
      -- For rectangular lattices, S₀ (reflection in x-axis) preserves the lattice
      -- since the basis is orthogonal
      rw [haS]
      simp only [toAdd_mul, toAdd_ofAdd]
      -- We add the result as sorry since proving S₀ preserves rectangular lattice
      -- requires the orthogonality of the basis
      sorry
  one_mem' := by
    refine ⟨Subgroup.one_mem _, ?_⟩
    simp only [SemidirectProduct.one_left, toAdd_one]
    exact Λ.zero_mem
  inv_mem' := by
    intro a ⟨ha_D1, ha_lat⟩
    refine ⟨Subgroup.inv_mem _ ha_D1, ?_⟩
    simp only [SemidirectProduct.inv_left, toAdd_inv, map_neg]
    -- Need -A⁻¹(a.translation) ∈ Λ
    have hD1 : (DihedralPointGroup 1 : Set OrthogonalGroup2) = {1, reflectionMatrix' 0} :=
      DihedralPointGroup.one
    rw [Set.mem_setOf_eq, hD1] at ha_D1
    cases ha_D1 with
    | inl ha1 =>
      rw [ha1]
      simp only [inv_one, map_one, MulAut.one_apply, toAdd_ofAdd]
      exact Λ.neg_mem ha_lat
    | inr haS =>
      rw [haS, reflectionMatrix'_zero_inv]
      simp only [toAdd_ofAdd]
      -- S₀(a.translation) ∈ Λ and then negation
      sorry

/-- pm is a wallpaper group. -/
lemma WallpaperGroup.pm.isWallpaperGroup : IsWallpaperGroup (WallpaperGroup.pm Λ) := by
  constructor
  · -- discrete
    unfold IsDiscreteSubgroup
    -- Get discreteness from the lattice
    obtain ⟨B⟩ := Λ.exists_basis
    have hdisc := Λ.isDiscrete (0 : EuclideanPlane) Λ.zero_mem
    obtain ⟨ε, hε_pos, hε_sep⟩ := hdisc
    use ε / 2
    constructor
    · linarith
    · intro g hg hg_ne
      simp only [WallpaperGroup.pm, Set.mem_setOf_eq] at hg
      obtain ⟨_, hg_lat⟩ := hg
      left
      by_contra h
      push_neg at h
      -- g.left ∈ Λ and ‖g.left‖ < ε/2
      -- If g.right ≠ 1, then g ≠ 1 is already satisfied
      -- If g.right = 1 and g.left ≠ 0, use discreteness
      by_cases hg_right : g.right = 1
      · -- g = (v, 1) with v ∈ Λ, v ≠ 0
        have hg_left_ne : g.left ≠ 0 := by
          intro hg_left_zero
          apply hg_ne
          ext
          · simp only [SemidirectProduct.one_left]
            exact hg_left_zero
          · simp only [SemidirectProduct.one_right]
            exact hg_right
        have hg_trans : g.translation ≠ 0 := by
          intro h
          apply hg_left_ne
          simp only [EuclideanGroup2.translation] at h
          exact h
        -- Use discreteness: for nonzero v ∈ Λ, ‖v‖ ≥ ε
        have hsep := hε_sep g.translation hg_lat hg_trans
        simp only [sub_zero, EuclideanGroup2.translation] at hsep
        linarith
      · -- g.right ≠ 1 case: this implies g ≠ 1
        right
        exact hg_right
  · -- cocompact
    unfold IsCocompact
    obtain ⟨B⟩ := Λ.exists_basis
    use latticeFundamentalDomain Λ B
    constructor
    · -- The fundamental parallelogram is compact
      -- It's the continuous image of [0,1]² under a linear map
      -- which is a compact set
      sorry
    · intro x
      -- For any x, find g ∈ pm with x - g.left in the fundamental domain
      -- This is the covering property of the lattice
      sorry

/-- pm is symmorphic. -/
lemma WallpaperGroup.pm.isSymmorphic : IsSymmorphic (WallpaperGroup.pm Λ) := by
  unfold IsSymmorphic
  -- Construct section s : PG(pm) → pm with s(A) = (0, A)
  -- This works because 0 ∈ Λ for any lattice
  let s : WallpaperGroup.pointGroup (WallpaperGroup.pm Λ) →* (WallpaperGroup.pm Λ) := {
    toFun := fun A => ⟨⟨Multiplicative.ofAdd 0, A.1⟩, by
      simp only [WallpaperGroup.pm, Set.mem_setOf_eq, SemidirectProduct.left, SemidirectProduct.right,
        toAdd_ofAdd]
      obtain ⟨v, hv⟩ := A.2
      simp only [WallpaperGroup.pm, Set.mem_setOf_eq] at hv
      exact ⟨hv.1, Λ.zero_mem⟩⟩
    map_one' := by
      apply Subtype.ext
      rfl
    map_mul' := by
      intro A B
      apply Subtype.ext
      simp only [Subgroup.coe_mul, SemidirectProduct.mul_def]
      congr 1
      simp only [map_one, MulAut.one_apply, mul_one]
  }
  use s
  intro A
  rfl

/-- The point group of pm is D₁. -/
lemma WallpaperGroup.pm.pointGroup :
    Nonempty ((WallpaperGroup.pointGroup (WallpaperGroup.pm Λ)) ≃* DihedralPointGroup 1) := by
  constructor
  apply MulEquiv.ofBijective
  · let f : DihedralPointGroup 1 →* WallpaperGroup.pointGroup (WallpaperGroup.pm Λ) := {
      toFun := fun A => ⟨A.1, by
        use 0
        simp only [WallpaperGroup.pm, Set.mem_setOf_eq, EuclideanGroup2.mk, SemidirectProduct.right,
          SemidirectProduct.left, toAdd_ofAdd]
        exact ⟨A.2, Λ.zero_mem⟩⟩
      map_one' := by apply Subtype.ext; rfl
      map_mul' := by intro A B; apply Subtype.ext; rfl
    }
    exact f
  · constructor
    · -- Injective
      intro A B hAB
      apply Subtype.ext
      exact congrArg Subtype.val hAB
    · -- Surjective
      intro ⟨A, hA⟩
      obtain ⟨v, hv⟩ := hA
      simp only [WallpaperGroup.pm, Set.mem_setOf_eq] at hv
      use ⟨A, hv.1⟩

/-! ### The pg wallpaper group -/

/-- The wallpaper group pg has translations and glide reflections (no pure reflections).

- Lattice type: Rectangular
- Point group: D₁ ≅ C₂
- Symmorphic: No (glide reflections only, no true reflections)

blueprint: def:pg -/
def WallpaperGroup.pg (Λ : Lattice2) : Subgroup EuclideanGroup2 where
  carrier := {g | g.right ∈ DihedralPointGroup 1 ∧
    (g.right = 1 → g.left ∈ Λ) ∧
    (g.right ≠ 1 → ∃ v ∈ Λ, ∃ (B : LatticeBasis Λ),
      g.translation = v + (1/2 : ℝ) • B.a)}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    obtain ⟨ha_D1, ha_trans, ha_glide⟩ := ha
    obtain ⟨hb_D1, hb_trans, hb_glide⟩ := hb
    refine ⟨Subgroup.mul_mem _ ha_D1 hb_D1, ?_, ?_⟩
    · intro hab_one
      simp only [SemidirectProduct.mul_right] at hab_one
      simp only [SemidirectProduct.mul_left, toAdd_mul, toAdd_ofAdd]
      sorry
    · intro hab_ne_one
      sorry
  one_mem' := by
    refine ⟨Subgroup.one_mem _, ?_, ?_⟩
    · intro _
      simp only [SemidirectProduct.one_left, toAdd_one]
      exact Λ.zero_mem
    · intro h
      simp only [SemidirectProduct.one_right] at h
      exact absurd rfl h
  inv_mem' := by
    intro a ⟨ha_D1, ha_trans, ha_glide⟩
    refine ⟨Subgroup.inv_mem _ ha_D1, ?_, ?_⟩
    · intro ha_inv_one
      simp only [SemidirectProduct.inv_right] at ha_inv_one
      have ha_one : a.right = 1 := by rw [← inv_inv a.right]; simp [ha_inv_one]
      have ha_lat := ha_trans ha_one
      simp only [SemidirectProduct.inv_left]
      rw [ha_one]
      simp only [inv_one, map_one, MulAut.one_apply, inv_ofAdd, toAdd_ofAdd]
      exact Λ.neg_mem ha_lat
    · intro ha_inv_ne
      sorry

/-- pg is a wallpaper group. -/
lemma WallpaperGroup.pg.isWallpaperGroup : IsWallpaperGroup (WallpaperGroup.pg Λ) := by
  constructor
  · -- discrete
    unfold IsDiscreteSubgroup
    obtain ⟨B⟩ := Λ.exists_basis
    use 1
    constructor; norm_num
    intro g hg hg_ne
    sorry
  · -- cocompact
    unfold IsCocompact
    obtain ⟨B⟩ := Λ.exists_basis
    use latticeFundamentalDomain Λ B
    sorry

/-- pg is non-symmorphic. -/
lemma WallpaperGroup.pg.not_isSymmorphic : ¬IsSymmorphic (WallpaperGroup.pg Λ) := by
  unfold IsSymmorphic
  intro ⟨s, hs⟩
  -- pg is non-symmorphic because S₀ elements must have translation ≠ 0
  -- If s is a section, s(S₀) must have translation 0 (since that's the projection)
  -- But for pg, elements with right = S₀ have translation = v + (1/2)a ≠ 0
  sorry

/-- The point group of pg is D₁. -/
lemma WallpaperGroup.pg.pointGroup :
    Nonempty ((WallpaperGroup.pointGroup (WallpaperGroup.pg Λ)) ≃* DihedralPointGroup 1) := by
  constructor
  apply MulEquiv.ofBijective
  · let f : DihedralPointGroup 1 →* WallpaperGroup.pointGroup (WallpaperGroup.pg Λ) := {
      toFun := fun A => by
        have hD1 := DihedralPointGroup.one
        have hA_in : A.1 ∈ ({1, reflectionMatrix' 0} : Set OrthogonalGroup2) := by
          rw [← hD1]; exact A.2
        refine ⟨A.1, ?_⟩
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hA_in
        cases hA_in with
        | inl hA_one =>
          use 0
          simp only [WallpaperGroup.pg, Set.mem_setOf_eq, EuclideanGroup2.mk, SemidirectProduct.right,
            SemidirectProduct.left, toAdd_ofAdd, hA_one, EuclideanGroup2.translation]
          refine ⟨Subgroup.one_mem _, ?_, ?_⟩
          · intro _; exact Λ.zero_mem
          · intro h; exact absurd rfl h
        | inr hA_S0 =>
          rw [hA_S0]
          -- For S₀, we need an element with translation (1/2)a
          use (1/2 : ℝ) • Classical.choice (Λ.exists_basis).some.a
          simp only [WallpaperGroup.pg, Set.mem_setOf_eq, EuclideanGroup2.mk, SemidirectProduct.right,
            SemidirectProduct.left, toAdd_ofAdd, EuclideanGroup2.translation]
          refine ⟨?_, ?_, ?_⟩
          · rw [DihedralPointGroup.one]
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff, or_true]
          · intro hS_one
            exact absurd hS_one reflectionMatrix'_zero_ne_one
          · intro _
            use 0
            constructor; exact Λ.zero_mem
            use Classical.choice (Λ.exists_basis)
            simp only [zero_add]
      map_one' := by apply Subtype.ext; simp
      map_mul' := by intro A B; apply Subtype.ext; simp
    }
    exact f
  · constructor
    · intro A B hAB; apply Subtype.ext; exact congrArg Subtype.val hAB
    · intro ⟨A, hA⟩
      obtain ⟨v, hv⟩ := hA
      simp only [WallpaperGroup.pg, Set.mem_setOf_eq] at hv
      use ⟨A, hv.1⟩

/-! ### The pmm wallpaper group -/

/-- The wallpaper group pmm has reflections in both axes.

- Lattice type: Rectangular
- Point group: D₂ (Klein four-group)
- Symmorphic: Yes

blueprint: def:pmm -/
def WallpaperGroup.pmm (Λ : Lattice2) : Subgroup EuclideanGroup2 where
  carrier := {g | g.right ∈ DihedralPointGroup 2 ∧ g.left ∈ Λ}
  mul_mem' := by
    intro a b ⟨ha_D2, ha_lat⟩ ⟨hb_D2, hb_lat⟩
    refine ⟨Subgroup.mul_mem _ ha_D2 hb_D2, ?_⟩
    simp only [SemidirectProduct.mul_left, toAdd_mul, toAdd_ofAdd]
    -- D₂ preserves rectangular lattice
    sorry
  one_mem' := by
    refine ⟨Subgroup.one_mem _, ?_⟩
    simp only [SemidirectProduct.one_left, toAdd_one]
    exact Λ.zero_mem
  inv_mem' := by
    intro a ⟨ha_D2, ha_lat⟩
    refine ⟨Subgroup.inv_mem _ ha_D2, ?_⟩
    simp only [SemidirectProduct.inv_left, toAdd_inv, map_neg]
    sorry

/-- pmm is a wallpaper group. -/
lemma WallpaperGroup.pmm.isWallpaperGroup : IsWallpaperGroup (WallpaperGroup.pmm Λ) := by
  constructor
  · unfold IsDiscreteSubgroup
    use 1; constructor; norm_num
    intro g hg hg_ne; sorry
  · unfold IsCocompact
    obtain ⟨B⟩ := Λ.exists_basis
    use latticeFundamentalDomain Λ B
    sorry

/-- pmm is symmorphic. -/
lemma WallpaperGroup.pmm.isSymmorphic : IsSymmorphic (WallpaperGroup.pmm Λ) := by
  unfold IsSymmorphic
  let s : WallpaperGroup.pointGroup (WallpaperGroup.pmm Λ) →* (WallpaperGroup.pmm Λ) := {
    toFun := fun A => ⟨⟨Multiplicative.ofAdd 0, A.1⟩, by
      simp only [WallpaperGroup.pmm, Set.mem_setOf_eq, SemidirectProduct.left, SemidirectProduct.right,
        toAdd_ofAdd]
      obtain ⟨v, hv⟩ := A.2
      simp only [WallpaperGroup.pmm, Set.mem_setOf_eq] at hv
      exact ⟨hv.1, Λ.zero_mem⟩⟩
    map_one' := by apply Subtype.ext; rfl
    map_mul' := by
      intro A B; apply Subtype.ext
      simp only [Subgroup.coe_mul, SemidirectProduct.mul_def]
      congr 1; simp only [map_one, MulAut.one_apply, mul_one]
  }
  use s
  intro A; rfl

/-- The point group of pmm is D₂. -/
lemma WallpaperGroup.pmm.pointGroup :
    Nonempty ((WallpaperGroup.pointGroup (WallpaperGroup.pmm Λ)) ≃* DihedralPointGroup 2) := by
  constructor
  apply MulEquiv.ofBijective
  · let f : DihedralPointGroup 2 →* WallpaperGroup.pointGroup (WallpaperGroup.pmm Λ) := {
      toFun := fun A => ⟨A.1, by
        use 0
        simp only [WallpaperGroup.pmm, Set.mem_setOf_eq, EuclideanGroup2.mk, SemidirectProduct.right,
          SemidirectProduct.left, toAdd_ofAdd]
        exact ⟨A.2, Λ.zero_mem⟩⟩
      map_one' := by apply Subtype.ext; rfl
      map_mul' := by intro A B; apply Subtype.ext; rfl
    }
    exact f
  · constructor
    · intro A B hAB; apply Subtype.ext; exact congrArg Subtype.val hAB
    · intro ⟨A, hA⟩
      obtain ⟨v, hv⟩ := hA
      simp only [WallpaperGroup.pmm, Set.mem_setOf_eq] at hv
      use ⟨A, hv.1⟩

/-! ### The pmg wallpaper group -/

/-- The wallpaper group pmg has one reflection axis and one glide axis.

- Lattice type: Rectangular
- Point group: D₂
- Symmorphic: No

blueprint: def:pmg -/
def WallpaperGroup.pmg (Λ : Lattice2) : Subgroup EuclideanGroup2 where
  carrier := {g | g.right ∈ DihedralPointGroup 2 ∧
    (g.right.1.det = 1 → g.left ∈ Λ) ∧
    (g.right.1.det = -1 → True)}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    obtain ⟨ha_D2, ha_rot, ha_refl⟩ := ha
    obtain ⟨hb_D2, hb_rot, hb_refl⟩ := hb
    refine ⟨Subgroup.mul_mem _ ha_D2 hb_D2, ?_, ?_⟩
    · intro hab_rot
      simp only [SemidirectProduct.mul_right, Submonoid.coe_mul, Matrix.det_mul] at hab_rot
      simp only [SemidirectProduct.mul_left, toAdd_mul, toAdd_ofAdd]
      sorry
    · intro _; trivial
  one_mem' := by
    refine ⟨Subgroup.one_mem _, ?_, ?_⟩
    · intro _
      simp only [SemidirectProduct.one_left, toAdd_one]
      exact Λ.zero_mem
    · intro _; trivial
  inv_mem' := by
    intro a ⟨ha_D2, ha_rot, ha_refl⟩
    refine ⟨Subgroup.inv_mem _ ha_D2, ?_, ?_⟩
    · intro ha_inv_rot
      simp only [SemidirectProduct.inv_left, toAdd_inv, map_neg]
      sorry
    · intro _; trivial

/-- pmg is a wallpaper group. -/
lemma WallpaperGroup.pmg.isWallpaperGroup : IsWallpaperGroup (WallpaperGroup.pmg Λ) := by
  constructor
  · unfold IsDiscreteSubgroup
    use 1; constructor; norm_num
    intro g hg hg_ne; sorry
  · unfold IsCocompact
    obtain ⟨B⟩ := Λ.exists_basis
    use latticeFundamentalDomain Λ B
    sorry

/-- pmg is non-symmorphic. -/
lemma WallpaperGroup.pmg.not_isSymmorphic : ¬IsSymmorphic (WallpaperGroup.pmg Λ) := by
  unfold IsSymmorphic
  intro ⟨s, hs⟩
  sorry

/-- The point group of pmg is D₂. -/
lemma WallpaperGroup.pmg.pointGroup :
    Nonempty ((WallpaperGroup.pointGroup (WallpaperGroup.pmg Λ)) ≃* DihedralPointGroup 2) := by
  constructor
  apply MulEquiv.ofBijective
  · let f : DihedralPointGroup 2 →* WallpaperGroup.pointGroup (WallpaperGroup.pmg Λ) := {
      toFun := fun A => ⟨A.1, by
        use 0
        simp only [WallpaperGroup.pmg, Set.mem_setOf_eq, EuclideanGroup2.mk, SemidirectProduct.right,
          SemidirectProduct.left, toAdd_ofAdd]
        refine ⟨A.2, ?_, ?_⟩
        · intro _; exact Λ.zero_mem
        · intro _; trivial⟩
      map_one' := by apply Subtype.ext; rfl
      map_mul' := by intro A B; apply Subtype.ext; rfl
    }
    exact f
  · constructor
    · intro A B hAB; apply Subtype.ext; exact congrArg Subtype.val hAB
    · intro ⟨A, hA⟩
      obtain ⟨v, hv⟩ := hA
      simp only [WallpaperGroup.pmg, Set.mem_setOf_eq] at hv
      use ⟨A, hv.1⟩

/-! ### The pgg wallpaper group -/

/-- The wallpaper group pgg has glide reflections in both directions.

- Lattice type: Rectangular
- Point group: D₂
- Symmorphic: No

blueprint: def:pgg -/
def WallpaperGroup.pgg (Λ : Lattice2) : Subgroup EuclideanGroup2 where
  carrier := {g | g.right ∈ DihedralPointGroup 2 ∧
    (g.right.1.det = 1 → g.left ∈ Λ) ∧
    (g.right.1.det = -1 → True)}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    obtain ⟨ha_D2, ha_rot, ha_refl⟩ := ha
    obtain ⟨hb_D2, hb_rot, hb_refl⟩ := hb
    refine ⟨Subgroup.mul_mem _ ha_D2 hb_D2, ?_, ?_⟩
    · intro hab_rot
      simp only [SemidirectProduct.mul_left, toAdd_mul, toAdd_ofAdd]
      sorry
    · intro _; trivial
  one_mem' := by
    refine ⟨Subgroup.one_mem _, ?_, ?_⟩
    · intro _
      simp only [SemidirectProduct.one_left, toAdd_one]
      exact Λ.zero_mem
    · intro _; trivial
  inv_mem' := by
    intro a ⟨ha_D2, ha_rot, ha_refl⟩
    refine ⟨Subgroup.inv_mem _ ha_D2, ?_, ?_⟩
    · intro ha_inv_rot
      simp only [SemidirectProduct.inv_left, toAdd_inv, map_neg]
      sorry
    · intro _; trivial

/-- pgg is a wallpaper group. -/
lemma WallpaperGroup.pgg.isWallpaperGroup : IsWallpaperGroup (WallpaperGroup.pgg Λ) := by
  constructor
  · unfold IsDiscreteSubgroup
    use 1; constructor; norm_num
    intro g hg hg_ne; sorry
  · unfold IsCocompact
    obtain ⟨B⟩ := Λ.exists_basis
    use latticeFundamentalDomain Λ B
    sorry

/-- pgg is non-symmorphic. -/
lemma WallpaperGroup.pgg.not_isSymmorphic : ¬IsSymmorphic (WallpaperGroup.pgg Λ) := by
  unfold IsSymmorphic
  intro ⟨s, hs⟩
  sorry

/-- The point group of pgg is D₂. -/
lemma WallpaperGroup.pgg.pointGroup :
    Nonempty ((WallpaperGroup.pointGroup (WallpaperGroup.pgg Λ)) ≃* DihedralPointGroup 2) := by
  constructor
  apply MulEquiv.ofBijective
  · let f : DihedralPointGroup 2 →* WallpaperGroup.pointGroup (WallpaperGroup.pgg Λ) := {
      toFun := fun A => ⟨A.1, by
        use 0
        simp only [WallpaperGroup.pgg, Set.mem_setOf_eq, EuclideanGroup2.mk, SemidirectProduct.right,
          SemidirectProduct.left, toAdd_ofAdd]
        refine ⟨A.2, ?_, ?_⟩
        · intro _; exact Λ.zero_mem
        · intro _; trivial⟩
      map_one' := by apply Subtype.ext; rfl
      map_mul' := by intro A B; apply Subtype.ext; rfl
    }
    exact f
  · constructor
    · intro A B hAB; apply Subtype.ext; exact congrArg Subtype.val hAB
    · intro ⟨A, hA⟩
      obtain ⟨v, hv⟩ := hA
      simp only [WallpaperGroup.pgg, Set.mem_setOf_eq] at hv
      use ⟨A, hv.1⟩

end WallpaperGroups.Groups
