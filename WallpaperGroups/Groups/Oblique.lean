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
    · simp only [SemidirectProduct.mul_left]
      have h : orthogonalActionHom a.right = 1 := by simp [ha1]
      simp [h, toAdd_mul]
      exact Λ.add_mem ha2 hb2
  one_mem' := by
    constructor
    · simp [SemidirectProduct.one_right]
    · exact Λ.zero_mem
  inv_mem' := by
    intro a ⟨ha1, ha2⟩
    constructor
    · simp [SemidirectProduct.inv_right, ha1]
    · simp only [SemidirectProduct.inv_left]
      have h1 : a.right⁻¹ = 1 := by simp [ha1]
      have h2 : orthogonalActionHom a.right⁻¹ = 1 := by simp [h1]
      simp [h2, toAdd_inv]
      exact Λ.neg_mem ha2

/-- p1 is a wallpaper group. -/
lemma WallpaperGroup.p1.isWallpaperGroup (hΛ : IsObliqueLattice Λ ∨ IsRectangularLattice Λ ∨
    IsCenteredRectangularLattice Λ ∨ IsSquareLattice Λ ∨ IsHexagonalLattice Λ) :
    IsWallpaperGroup (WallpaperGroup.p1 Λ) := by
  constructor
  · -- IsDiscreteSubgroup
    rw [IsDiscreteSubgroup]
    have h := Λ.isDiscrete 0 Λ.zero_mem
    obtain ⟨ε, hε_pos, hε_sep⟩ := h
    use ε, hε_pos
    intro g ⟨hg_right, hg_left⟩ hg_ne_1
    left
    have hgL_ne : Multiplicative.toAdd g.left ≠ 0 := by
      intro h
      apply hg_ne_1
      simp only [SemidirectProduct.ext_iff, SemidirectProduct.one_left,
                 SemidirectProduct.one_right, hg_right, and_true]
      exact Multiplicative.toAdd.injective h
    have := hε_sep (Multiplicative.toAdd g.left) hg_left hgL_ne
    rw [sub_zero] at this
    exact this
  · -- IsCocompact
    rw [IsCocompact]
    obtain ⟨B⟩ := Λ.exists_basis
    use parallelepiped B.toBasis
    constructor
    · exact parallelepiped_isCompact B.toBasis
    · intro x
      let v := ZSpan.floor B.toBasis x
      use EuclideanGroup2.mk (↑v) 1
      constructor
      · constructor
        · rfl
        · have hv := v.2
          have hcarrier : Λ.carrier = (Submodule.span ℤ (Set.range B.toBasis)).toAddSubgroup :=
            Λ.carrier_eq_span B
          change ↑v ∈ Λ.carrier
          rw [hcarrier]
          exact hv
      · simp only [EuclideanGroup2.mk, toAdd_ofAdd]
        have heq : x - ↑v = ZSpan.fract B.toBasis x := by
          rw [ZSpan.fract_apply]
        rw [heq]
        exact ZSpan.fundamentalDomain_subset_parallelepiped B.toBasis
            (ZSpan.fract_mem_fundamentalDomain B.toBasis x)

/-- p1 is symmorphic. -/
lemma WallpaperGroup.p1.isSymmorphic : IsSymmorphic (WallpaperGroup.p1 Λ) := by
  rw [IsSymmorphic]
  let s : WallpaperGroup.pointGroup (WallpaperGroup.p1 Λ) →* ↥(WallpaperGroup.p1 Λ) := {
    toFun := fun A => ⟨EuclideanGroup2.mk 0 A.1, by
      simp only [WallpaperGroup.p1, Subgroup.mem_mk, EuclideanGroup2.mk]
      have ⟨v, hv⟩ := A.2
      simp only [WallpaperGroup.p1, EuclideanGroup2.mk] at hv
      constructor
      · exact hv.1
      · simp; exact Λ.zero_mem⟩
    map_one' := by
      apply Subtype.ext
      simp [EuclideanGroup2.mk]
    map_mul' := by
      intro A B
      apply Subtype.ext
      simp only [EuclideanGroup2.mk, Subgroup.coe_mul]
      have hA : A.1 = 1 := by
        have ⟨v, hv⟩ := A.2
        simp only [WallpaperGroup.p1, EuclideanGroup2.mk] at hv
        exact hv.1
      have hB : B.1 = 1 := by
        have ⟨v, hv⟩ := B.2
        simp only [WallpaperGroup.p1, EuclideanGroup2.mk] at hv
        exact hv.1
      ext
      · simp [hA]
      · simp [hA, hB]
  }
  use s
  intro A
  rfl

/-- The point group of p1 is the trivial subgroup. -/
lemma WallpaperGroup.p1.pointGroup_eq_bot :
    WallpaperGroup.pointGroup (WallpaperGroup.p1 Λ) = ⊥ := by
  ext A
  constructor
  · intro ⟨v, hv⟩
    simp only [WallpaperGroup.p1, EuclideanGroup2.mk] at hv
    have h := hv.1
    simp only [Subgroup.mem_bot]
    exact h
  · intro hA
    simp only [Subgroup.mem_bot] at hA
    rw [hA]
    use 0
    simp only [WallpaperGroup.p1, Subgroup.mem_mk, Set.mem_setOf_eq, EuclideanGroup2.mk]
    constructor
    · rfl
    · simp; exact Λ.zero_mem

/-- The point group of p1 is C₁. -/
lemma WallpaperGroup.p1.pointGroup :
    Nonempty ((WallpaperGroup.pointGroup (WallpaperGroup.p1 Λ)) ≃* CyclicPointGroup 1) := by
  have h1 : WallpaperGroup.pointGroup (WallpaperGroup.p1 Λ) = ⊥ := pointGroup_eq_bot Λ
  have h2 : CyclicPointGroup 1 = ⊥ := CyclicPointGroup.one
  have e1 : ↥(WallpaperGroup.pointGroup (WallpaperGroup.p1 Λ)) ≃* (⊥ : Subgroup OrthogonalGroup2) :=
    MulEquiv.subgroupCongr h1
  have e2 : ↥(CyclicPointGroup 1) ≃* (⊥ : Subgroup OrthogonalGroup2) :=
    MulEquiv.subgroupCongr h2
  exact ⟨e1.trans e2.symm⟩

/-- R_π squared equals 1. -/
private lemma rotationMatrix'_pi_sq :
    rotationMatrix' Real.pi * rotationMatrix' Real.pi = 1 := by
  apply Subtype.ext
  simp only [rotationMatrix', Submonoid.coe_mul, Submonoid.coe_one]
  rw [rotationMatrix_add, show Real.pi + Real.pi = 2 * Real.pi by ring, rotationMatrix_two_pi]

/-- R_π is its own inverse. -/
private lemma rotationMatrix'_pi_inv :
    (rotationMatrix' Real.pi)⁻¹ = rotationMatrix' Real.pi :=
  inv_eq_of_mul_eq_one_left rotationMatrix'_pi_sq

/-- R_π acts on vectors by negation. -/
private lemma rotationPi_action (v : EuclideanPlane) :
    (orthogonalToLinearEquiv (rotationMatrix' Real.pi)) v = -v := by
  unfold orthogonalToLinearEquiv
  simp only [LinearEquiv.ofLinear_apply, rotationMatrix']
  have h : rotationMatrix Real.pi = -1 := rotationMatrix_pi
  rw [Matrix.toEuclideanLin_apply]
  ext i
  simp only [PiLp.neg_apply]
  rw [h]
  simp only [Matrix.neg_mulVec, Matrix.one_mulVec, Pi.neg_apply]

/-- R_π action on Multiplicative EuclideanPlane. -/
private lemma rotationPi_mulAut_action (v : Multiplicative EuclideanPlane) :
    (orthogonalActionHom (rotationMatrix' Real.pi)) v =
    Multiplicative.ofAdd (-Multiplicative.toAdd v) := by
  unfold orthogonalActionHom orthogonalToMulAut
  simp only [MonoidHom.coe_mk, OneHom.coe_mk]
  unfold MulAutMultiplicative
  simp only [MulEquiv.symm_mk, MulEquiv.coe_mk, Equiv.symm_symm]
  simp only [AddEquiv.toMultiplicative, Equiv.coe_fn_mk]
  unfold AddMonoidHom.toMultiplicative orthogonalToAddAut
  simp only [Equiv.coe_fn_mk, MonoidHom.coe_mk, OneHom.coe_mk]
  simp only [AddEquiv.coe_toAddMonoidHom, LinearEquiv.coe_toAddEquiv]
  have h := rotationPi_action (Multiplicative.toAdd v)
  exact congrArg Multiplicative.ofAdd h

/-- The wallpaper group p2 has translations and 180° rotation.

- Lattice type: Any (typically oblique)
- Point group: C₂ = {I, R_π}
- Symmorphic: Yes
- Generators: Two translations + 180° rotation

blueprint: def:p2 -/
def WallpaperGroup.p2 : Subgroup EuclideanGroup2 where
  carrier := {g | (g.right = 1 ∨ g.right = rotationMatrix' Real.pi) ∧ g.left ∈ Λ}
  mul_mem' := by
    intro a b ⟨ha_right, ha_left⟩ ⟨hb_right, hb_left⟩
    constructor
    · simp only [SemidirectProduct.mul_right]
      rcases ha_right with ha1 | haπ <;> rcases hb_right with hb1 | hbπ
      · left; simp [ha1, hb1]
      · right; simp [ha1, hbπ]
      · right; simp [haπ, hb1]
      · left; simp only [haπ, hbπ]; exact rotationMatrix'_pi_sq
    · simp only [SemidirectProduct.mul_left]
      rcases ha_right with ha1 | haπ
      · have h : orthogonalActionHom a.right = 1 := by simp [ha1]
        simp [h]
        exact Λ.add_mem ha_left hb_left
      · rw [haπ, rotationPi_mulAut_action]
        have h_sub := Λ.carrier.sub_mem ha_left hb_left
        convert h_sub using 1
  one_mem' := by
    constructor
    · left; simp [SemidirectProduct.one_right]
    · simp [SemidirectProduct.one_left]; exact Λ.zero_mem
  inv_mem' := by
    intro a ⟨ha_right, ha_left⟩
    constructor
    · simp only [SemidirectProduct.inv_right]
      rcases ha_right with ha1 | haπ
      · left; simp [ha1]
      · right; simp [haπ]; exact rotationMatrix'_pi_inv
    · simp only [SemidirectProduct.inv_left]
      rcases ha_right with ha1 | haπ
      · have h1 : a.right⁻¹ = 1 := by simp [ha1]
        have h2 : orthogonalActionHom a.right⁻¹ = 1 := by simp [h1]
        simp [h2]
        exact Λ.neg_mem ha_left
      · rw [haπ, rotationMatrix'_pi_inv, rotationPi_mulAut_action]
        have h : Multiplicative.toAdd a.left⁻¹ = -Multiplicative.toAdd a.left := toAdd_inv a.left
        rw [h]
        simp only [neg_neg, ofAdd_toAdd]
        exact ha_left

/-- p2 is a wallpaper group. -/
lemma WallpaperGroup.p2.isWallpaperGroup :
    IsWallpaperGroup (WallpaperGroup.p2 Λ) := by
  constructor
  · -- IsDiscreteSubgroup
    rw [IsDiscreteSubgroup]
    have h := Λ.isDiscrete 0 Λ.zero_mem
    obtain ⟨ε, hε_pos, hε_sep⟩ := h
    use ε, hε_pos
    intro g ⟨hg_right, hg_left⟩ hg_ne_1
    -- Either g.left ≠ 0 (and g.right = 1 or R_π), or g.right ≠ 1
    by_cases hg_r : g.right = 1
    · -- g.right = 1, so g.left must be nonzero
      left
      have hgL_ne : Multiplicative.toAdd g.left ≠ 0 := by
        intro h
        apply hg_ne_1
        simp only [SemidirectProduct.ext_iff, SemidirectProduct.one_left,
                   SemidirectProduct.one_right, hg_r, and_true]
        exact Multiplicative.toAdd.injective h
      have := hε_sep (Multiplicative.toAdd g.left) hg_left hgL_ne
      rw [sub_zero] at this
      exact this
    · -- g.right ≠ 1
      right
      exact hg_r
  · -- IsCocompact
    rw [IsCocompact]
    obtain ⟨B⟩ := Λ.exists_basis
    use parallelepiped B.toBasis
    constructor
    · exact parallelepiped_isCompact B.toBasis
    · intro x
      let v := ZSpan.floor B.toBasis x
      use EuclideanGroup2.mk (↑v) 1
      constructor
      · constructor
        · left; rfl
        · have hv := v.2
          have hcarrier : Λ.carrier = (Submodule.span ℤ (Set.range B.toBasis)).toAddSubgroup :=
            Λ.carrier_eq_span B
          show Multiplicative.ofAdd ↑v ∈ Λ
          change (Multiplicative.toAdd (Multiplicative.ofAdd ↑v) : EuclideanPlane) ∈ Λ.carrier
          simp only [toAdd_ofAdd]
          rw [hcarrier]
          exact hv
      · simp only [EuclideanGroup2.mk, toAdd_ofAdd]
        have heq : x - ↑v = ZSpan.fract B.toBasis x := by
          rw [ZSpan.fract_apply]
        rw [heq]
        exact ZSpan.fundamentalDomain_subset_parallelepiped B.toBasis
            (ZSpan.fract_mem_fundamentalDomain B.toBasis x)

/-- p2 is symmorphic. -/
lemma WallpaperGroup.p2.isSymmorphic : IsSymmorphic (WallpaperGroup.p2 Λ) := by
  rw [IsSymmorphic]
  -- First, characterize the point group of p2
  -- The point group consists of elements A such that ∃v, (v, A) ∈ p2
  -- This means A = 1 or A = R_π
  let s : WallpaperGroup.pointGroup (WallpaperGroup.p2 Λ) →* ↥(WallpaperGroup.p2 Λ) := {
    toFun := fun A => ⟨EuclideanGroup2.mk 0 A.1, by
      simp only [WallpaperGroup.p2, Subgroup.mem_mk, EuclideanGroup2.mk]
      have ⟨v, hv⟩ := A.2
      simp only [WallpaperGroup.p2, EuclideanGroup2.mk] at hv
      constructor
      · exact hv.1
      · simp only [ofAdd_zero]; exact Λ.zero_mem⟩
    map_one' := by
      apply Subtype.ext
      simp [EuclideanGroup2.mk]
    map_mul' := by
      intro A B
      apply Subtype.ext
      simp only [EuclideanGroup2.mk, Subgroup.coe_mul]
      -- A and B are in the point group, so A.1 and B.1 are either 1 or R_π
      have hA : A.1 = 1 ∨ A.1 = rotationMatrix' Real.pi := by
        have ⟨v, hv⟩ := A.2
        simp only [WallpaperGroup.p2, EuclideanGroup2.mk] at hv
        exact hv.1
      have hB : B.1 = 1 ∨ B.1 = rotationMatrix' Real.pi := by
        have ⟨v, hv⟩ := B.2
        simp only [WallpaperGroup.p2, EuclideanGroup2.mk] at hv
        exact hv.1
      ext
      · -- left component
        rcases hA with hA1 | hAπ <;> rcases hB with hB1 | hBπ
        · simp [hA1, hB1]
        · simp [hA1, hBπ]
        · simp [hAπ, hB1, rotationPi_mulAut_action]
        · simp [hAπ, hBπ, rotationPi_mulAut_action]
      · -- right component
        simp [SemidirectProduct.mul_right]
  }
  use s
  intro A
  rfl

/-- The point group of p2 is {1, R_π}. -/
lemma WallpaperGroup.p2.pointGroup_carrier :
    (WallpaperGroup.pointGroup (WallpaperGroup.p2 Λ) : Set OrthogonalGroup2) =
    {1, rotationMatrix' Real.pi} := by
  ext A
  simp only [SetLike.mem_coe, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro ⟨v, hv⟩
    simp only [WallpaperGroup.p2, EuclideanGroup2.mk] at hv
    exact hv.1
  · intro hA
    rcases hA with hA1 | hAπ
    · rw [hA1]
      use 0
      simp only [WallpaperGroup.p2, Subgroup.mem_mk, EuclideanGroup2.mk]
      constructor
      · left; rfl
      · simp only [ofAdd_zero]; exact Λ.zero_mem
    · rw [hAπ]
      use 0
      simp only [WallpaperGroup.p2, Subgroup.mem_mk, EuclideanGroup2.mk]
      constructor
      · right; rfl
      · simp only [ofAdd_zero]; exact Λ.zero_mem

/-- The point group of p2 is C₂. -/
lemma WallpaperGroup.p2.pointGroup :
    Nonempty ((WallpaperGroup.pointGroup (WallpaperGroup.p2 Λ)) ≃* CyclicPointGroup 2) := by
  -- Both have the same carrier: {1, R_π}
  have hC2 : (CyclicPointGroup 2 : Set OrthogonalGroup2) = {1, rotationMatrix' Real.pi} :=
    CyclicPointGroup.two
  have hp2 : (WallpaperGroup.pointGroup (WallpaperGroup.p2 Λ) : Set OrthogonalGroup2) =
             {1, rotationMatrix' Real.pi} := pointGroup_carrier Λ
  -- Use that they have the same carriers
  have heq : WallpaperGroup.pointGroup (WallpaperGroup.p2 Λ) = CyclicPointGroup 2 := by
    ext A
    rw [← SetLike.mem_coe, ← SetLike.mem_coe, hp2, hC2]
  exact ⟨MulEquiv.subgroupCongr heq⟩

/-- p1 and p2 are the only wallpaper groups with oblique lattice. -/
lemma oblique_wallpaperGroups (Γ : Subgroup EuclideanGroup2) (hΓ : IsWallpaperGroup Γ)
    (Λ' : Lattice2)
    (hΛ' : ∀ v, v ∈ Λ' ↔ (⟨v, 1⟩ : EuclideanGroup2) ∈ WallpaperGroup.translationSubgroup Γ)
    (hoblique : IsObliqueLattice Λ') :
    Nonempty (Γ ≃* WallpaperGroup.p1 Λ') ∨ Nonempty (Γ ≃* WallpaperGroup.p2 Λ') := by
  sorry

end WallpaperGroups.Groups
