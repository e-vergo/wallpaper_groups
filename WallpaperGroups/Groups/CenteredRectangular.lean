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

* `WallpaperGroup.cm` - Reflections + glides, PG = D_1, symmorphic
* `WallpaperGroup.cmm` - Reflections in both axes, PG = D_2, symmorphic

Both groups are symmorphic despite the "centered" lattice structure.

blueprint: def:cm, def:cmm
-/

namespace WallpaperGroups.Groups

open WallpaperGroups.Euclidean
open WallpaperGroups.Lattice
open WallpaperGroups.Wallpaper
open WallpaperGroups.PointGroup

variable (Λ : Lattice2)

/-- Helper lemma: the orthogonalActionHom preserves lattice membership when
    the orthogonal transformation preserves the lattice. -/
private lemma orthogonalActionHom_preserves_lattice {A : OrthogonalGroup2}
    (hA : IsLatticePreserving Λ A) (v : Multiplicative EuclideanPlane)
    (hv : Multiplicative.toAdd v ∈ Λ) :
    Multiplicative.toAdd ((orthogonalActionHom A) v) ∈ Λ := by
  simp only [orthogonalActionHom, orthogonalToMulAut, orthogonalToAddAut, orthogonalToLinearEquiv,
             MonoidHom.coe_mk, OneHom.coe_mk, MulAutMultiplicative,
             MulEquiv.symm_mk, MulEquiv.coe_mk, Equiv.symm_symm,
             AddEquiv.toMultiplicative, Equiv.coe_fn_mk]
  unfold AddMonoidHom.toMultiplicative
  simp only [Equiv.coe_fn_mk, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd,
             AddEquiv.coe_toAddMonoidHom, LinearEquiv.coe_toAddEquiv]
  simp only [IsLatticePreserving] at hA
  have h := hA (Multiplicative.toAdd v) hv
  simp only [Matrix.UnitaryGroup.inv_val, LinearEquiv.coe_addEquiv_apply,
    LinearEquiv.ofLinear_apply]
  exact h

/-- The wallpaper group cm has reflections across one axis.

- Lattice type: Centered rectangular (rhombic)
- Point group: D_1
- Symmorphic: Yes
- Contains both reflections and glide reflections due to lattice centering

The "c" indicates the centered lattice. Despite having glide reflections,
cm is symmorphic because it also contains true reflections.

blueprint: def:cm -/
def WallpaperGroup.cm (Λ : Lattice2) (hΛ : DihedralPointGroup 1 ≤ latticeSymmetryGroup Λ) :
    Subgroup EuclideanGroup2 where
  carrier := {g | Multiplicative.toAdd g.left ∈ Λ ∧ g.right ∈ DihedralPointGroup 1}
  mul_mem' := by
    intro a b ⟨ha_trans, ha_orth⟩ ⟨hb_trans, hb_orth⟩
    constructor
    · simp only [SemidirectProduct.mul_left]
      rw [toAdd_mul]
      have hpres := (hΛ ha_orth).1
      exact Λ.add_mem ha_trans (orthogonalActionHom_preserves_lattice Λ hpres b.left hb_trans)
    · exact (DihedralPointGroup 1).mul_mem ha_orth hb_orth
  one_mem' := by
    constructor
    · simp only [SemidirectProduct.one_left, toAdd_one]
      exact Λ.zero_mem
    · exact (DihedralPointGroup 1).one_mem
  inv_mem' := by
    intro a ⟨ha_trans, ha_orth⟩
    constructor
    · simp only [SemidirectProduct.inv_left]
      have ha_inv_orth : a.right⁻¹ ∈ DihedralPointGroup 1 := (DihedralPointGroup 1).inv_mem ha_orth
      have hpres := (hΛ ha_inv_orth).1
      have hneg : Multiplicative.toAdd a.left⁻¹ ∈ Λ := by
        rw [toAdd_inv]
        exact Λ.neg_mem ha_trans
      exact orthogonalActionHom_preserves_lattice Λ hpres a.left⁻¹ hneg
    · exact (DihedralPointGroup 1).inv_mem ha_orth

/-- cm is a wallpaper group. -/
lemma WallpaperGroup.cm.isWallpaperGroup (hΛ : DihedralPointGroup 1 ≤ latticeSymmetryGroup Λ) :
    IsWallpaperGroup (WallpaperGroup.cm Λ hΛ) where
  discrete := by
    -- IsDiscreteSubgroup is ∃ ε > 0, ∀ g ∈ Γ, g ≠ 1 → ε ≤ ‖g.left‖ ∨ g.right ≠ 1
    obtain ⟨ε, hε_pos, hε_sep⟩ := Λ.isDiscrete 0 Λ.zero_mem
    use ε, hε_pos
    intro g hg hne
    simp only [WallpaperGroup.cm, Subgroup.mem_mk] at hg
    obtain ⟨htrans, _horth⟩ := hg
    by_cases hzero : Multiplicative.toAdd g.left = 0
    · -- If translation is 0, then g.right ≠ 1 (otherwise g = 1)
      right
      intro heq
      apply hne
      have hleft : g.left = 1 :=
        Multiplicative.toAdd.injective (by simp only [toAdd_one, hzero])
      exact SemidirectProduct.ext hleft heq
    · -- Translation is nonzero
      left
      specialize hε_sep (Multiplicative.toAdd g.left) htrans hzero
      simp only [sub_zero] at hε_sep
      exact hε_sep
  cocompact := by
    -- IsCocompact: ∃ K, IsCompact K ∧ ∀ x, ∃ g ∈ Γ, x - toAdd g.left ∈ K
    obtain ⟨B⟩ := Λ.exists_basis
    use parallelepiped B.toBasis
    constructor
    · exact parallelepiped_isCompact B.toBasis
    · intro x
      -- Use ZSpan.fract to find the lattice element
      let floor_val := (ZSpan.floor B.toBasis x : EuclideanPlane)
      -- Construct the group element (floor_val, 1)
      have hmem : (⟨Multiplicative.ofAdd floor_val, 1⟩ : EuclideanGroup2) ∈
          WallpaperGroup.cm Λ hΛ := by
        simp only [WallpaperGroup.cm, Subgroup.mem_mk]
        constructor
        · -- floor_val ∈ Λ
          have hfloor := (ZSpan.floor B.toBasis x).2
          have hcarrier : Λ.carrier = (Submodule.span ℤ (Set.range B.toBasis)).toAddSubgroup :=
            Λ.carrier_eq_span B
          change floor_val ∈ Λ.carrier
          rw [hcarrier]
          exact hfloor
        · exact (DihedralPointGroup 1).one_mem
      use ⟨Multiplicative.ofAdd floor_val, 1⟩, hmem
      -- x - floor_val ∈ parallelepiped
      simp only [toAdd_ofAdd]
      have hfrac := ZSpan.fract_mem_fundamentalDomain B.toBasis x
      have hsub := ZSpan.fundamentalDomain_subset_parallelepiped B.toBasis hfrac
      convert hsub using 1

/-- cm is symmorphic. -/
lemma WallpaperGroup.cm.isSymmorphic (hΛ : DihedralPointGroup 1 ≤ latticeSymmetryGroup Λ) :
    IsSymmorphic (WallpaperGroup.cm Λ hΛ) := by
  unfold IsSymmorphic
  -- We construct a section s : pointGroup cm → cm by sending A to (0, A)
  -- This works because (0, A) ∈ cm iff A ∈ D_1 (since 0 ∈ Λ always)
  let s : WallpaperGroup.pointGroup (WallpaperGroup.cm Λ hΛ) →* (WallpaperGroup.cm Λ hΛ) := {
    toFun := fun A => ⟨EuclideanGroup2.mk 0 A.1, by
      simp only [WallpaperGroup.cm, Subgroup.mem_mk]
      constructor
      · -- 0 ∈ Λ
        simp only [EuclideanGroup2.mk, toAdd_ofAdd]
        exact Λ.zero_mem
      · -- A ∈ D_1: this follows from A being in the point group of cm
        obtain ⟨v, hv⟩ := A.2
        simp only [WallpaperGroup.cm, Subgroup.mem_mk] at hv
        exact hv.2⟩
    map_one' := by
      apply Subtype.ext
      simp only [OneMemClass.coe_one, EuclideanGroup2.mk]
      rfl
    map_mul' := by
      intro A B
      apply Subtype.ext
      simp only [Subgroup.coe_mul, EuclideanGroup2.mk]
      apply SemidirectProduct.ext
      · -- left component
        simp only [SemidirectProduct.mul_left, ofAdd_zero]
        simp only [orthogonalActionHom, orthogonalToMulAut, orthogonalToAddAut,
                   orthogonalToLinearEquiv, MonoidHom.coe_mk, OneHom.coe_mk, MulAutMultiplicative,
                   MulEquiv.symm_mk, MulEquiv.coe_mk, Equiv.symm_symm,
                   AddEquiv.toMultiplicative, Equiv.coe_fn_mk]
        unfold AddMonoidHom.toMultiplicative
        simp only [Equiv.coe_fn_mk, MonoidHom.coe_mk, OneHom.coe_mk,
                   AddEquiv.coe_toAddMonoidHom, LinearEquiv.coe_toAddEquiv,
                   toAdd_one, map_zero, ofAdd_zero, mul_one]
      · -- right component
        simp only [SemidirectProduct.mul_right]
  }
  use s
  intro A
  rfl

/-- The point group of cm is D_1. -/
lemma WallpaperGroup.cm.pointGroup (hΛ : DihedralPointGroup 1 ≤ latticeSymmetryGroup Λ) :
    Nonempty ((WallpaperGroup.pointGroup (WallpaperGroup.cm Λ hΛ)) ≃* DihedralPointGroup 1) := by
  -- We show that pointGroup cm = D_1 as subgroups of O(2)
  -- Direction 1: if A ∈ pointGroup cm, then ∃ v with (v, A) ∈ cm, so A ∈ D_1
  -- Direction 2: if A ∈ D_1, then (0, A) ∈ cm (since 0 ∈ Λ), so A ∈ pointGroup cm
  have h_eq : WallpaperGroup.pointGroup (WallpaperGroup.cm Λ hΛ) = DihedralPointGroup 1 := by
    ext A
    simp only [WallpaperGroup.pointGroup, Subgroup.mem_mk]
    constructor
    · intro ⟨v, hv⟩
      simp only [WallpaperGroup.cm, Subgroup.mem_mk] at hv
      exact hv.2
    · intro hA
      use 0
      simp only [WallpaperGroup.cm, Subgroup.mem_mk, EuclideanGroup2.mk]
      exact ⟨Λ.zero_mem, hA⟩
  exact ⟨MulEquiv.subgroupCongr h_eq⟩

/-- The wallpaper group cmm has reflections in both axes.

- Lattice type: Centered rectangular (rhombic)
- Point group: D_2 (Klein four-group)
- Symmorphic: Yes
- Two perpendicular reflection axes

blueprint: def:cmm -/
def WallpaperGroup.cmm (Λ : Lattice2) (hΛ : DihedralPointGroup 2 ≤ latticeSymmetryGroup Λ) :
    Subgroup EuclideanGroup2 where
  carrier := {g | Multiplicative.toAdd g.left ∈ Λ ∧ g.right ∈ DihedralPointGroup 2}
  mul_mem' := by
    intro a b ⟨ha_trans, ha_orth⟩ ⟨hb_trans, hb_orth⟩
    constructor
    · simp only [SemidirectProduct.mul_left]
      rw [toAdd_mul]
      have hpres := (hΛ ha_orth).1
      exact Λ.add_mem ha_trans (orthogonalActionHom_preserves_lattice Λ hpres b.left hb_trans)
    · exact (DihedralPointGroup 2).mul_mem ha_orth hb_orth
  one_mem' := by
    constructor
    · simp only [SemidirectProduct.one_left, toAdd_one]
      exact Λ.zero_mem
    · exact (DihedralPointGroup 2).one_mem
  inv_mem' := by
    intro a ⟨ha_trans, ha_orth⟩
    constructor
    · simp only [SemidirectProduct.inv_left]
      have ha_inv_orth : a.right⁻¹ ∈ DihedralPointGroup 2 := (DihedralPointGroup 2).inv_mem ha_orth
      have hpres := (hΛ ha_inv_orth).1
      have hneg : Multiplicative.toAdd a.left⁻¹ ∈ Λ := by
        rw [toAdd_inv]
        exact Λ.neg_mem ha_trans
      exact orthogonalActionHom_preserves_lattice Λ hpres a.left⁻¹ hneg
    · exact (DihedralPointGroup 2).inv_mem ha_orth

/-- cmm is a wallpaper group. -/
lemma WallpaperGroup.cmm.isWallpaperGroup (hΛ : DihedralPointGroup 2 ≤ latticeSymmetryGroup Λ) :
    IsWallpaperGroup (WallpaperGroup.cmm Λ hΛ) where
  discrete := by
    obtain ⟨ε, hε_pos, hε_sep⟩ := Λ.isDiscrete 0 Λ.zero_mem
    use ε, hε_pos
    intro g hg hne
    simp only [WallpaperGroup.cmm, Subgroup.mem_mk] at hg
    obtain ⟨htrans, _horth⟩ := hg
    by_cases hzero : Multiplicative.toAdd g.left = 0
    · right
      intro heq
      apply hne
      have hleft : g.left = 1 :=
        Multiplicative.toAdd.injective (by simp only [toAdd_one, hzero])
      exact SemidirectProduct.ext hleft heq
    · left
      specialize hε_sep (Multiplicative.toAdd g.left) htrans hzero
      simp only [sub_zero] at hε_sep
      exact hε_sep
  cocompact := by
    obtain ⟨B⟩ := Λ.exists_basis
    use parallelepiped B.toBasis
    constructor
    · exact parallelepiped_isCompact B.toBasis
    · intro x
      let floor_val := (ZSpan.floor B.toBasis x : EuclideanPlane)
      have hmem : (⟨Multiplicative.ofAdd floor_val, 1⟩ : EuclideanGroup2) ∈
          WallpaperGroup.cmm Λ hΛ := by
        simp only [WallpaperGroup.cmm, Subgroup.mem_mk]
        constructor
        · have hfloor := (ZSpan.floor B.toBasis x).2
          have hcarrier : Λ.carrier = (Submodule.span ℤ (Set.range B.toBasis)).toAddSubgroup :=
            Λ.carrier_eq_span B
          change floor_val ∈ Λ.carrier
          rw [hcarrier]
          exact hfloor
        · exact (DihedralPointGroup 2).one_mem
      use ⟨Multiplicative.ofAdd floor_val, 1⟩, hmem
      simp only [toAdd_ofAdd]
      have hfrac := ZSpan.fract_mem_fundamentalDomain B.toBasis x
      have hsub := ZSpan.fundamentalDomain_subset_parallelepiped B.toBasis hfrac
      convert hsub using 1

/-- cmm is symmorphic. -/
lemma WallpaperGroup.cmm.isSymmorphic (hΛ : DihedralPointGroup 2 ≤ latticeSymmetryGroup Λ) :
    IsSymmorphic (WallpaperGroup.cmm Λ hΛ) := by
  unfold IsSymmorphic
  let s : WallpaperGroup.pointGroup (WallpaperGroup.cmm Λ hΛ) →* (WallpaperGroup.cmm Λ hΛ) := {
    toFun := fun A => ⟨EuclideanGroup2.mk 0 A.1, by
      simp only [WallpaperGroup.cmm, Subgroup.mem_mk]
      constructor
      · simp only [EuclideanGroup2.mk, toAdd_ofAdd]
        exact Λ.zero_mem
      · obtain ⟨v, hv⟩ := A.2
        simp only [WallpaperGroup.cmm, Subgroup.mem_mk] at hv
        exact hv.2⟩
    map_one' := by
      apply Subtype.ext
      simp only [OneMemClass.coe_one, EuclideanGroup2.mk]
      rfl
    map_mul' := by
      intro A B
      apply Subtype.ext
      simp only [Subgroup.coe_mul, EuclideanGroup2.mk]
      apply SemidirectProduct.ext
      · simp only [SemidirectProduct.mul_left, ofAdd_zero]
        simp only [orthogonalActionHom, orthogonalToMulAut, orthogonalToAddAut,
                   orthogonalToLinearEquiv, MonoidHom.coe_mk, OneHom.coe_mk, MulAutMultiplicative,
                   MulEquiv.symm_mk, MulEquiv.coe_mk, Equiv.symm_symm,
                   AddEquiv.toMultiplicative, Equiv.coe_fn_mk]
        unfold AddMonoidHom.toMultiplicative
        simp only [Equiv.coe_fn_mk, MonoidHom.coe_mk, OneHom.coe_mk,
                   AddEquiv.coe_toAddMonoidHom, LinearEquiv.coe_toAddEquiv,
                   toAdd_one, map_zero, ofAdd_zero, mul_one]
      · simp only [SemidirectProduct.mul_right]
  }
  use s
  intro A
  rfl

/-- The point group of cmm is D_2. -/
lemma WallpaperGroup.cmm.pointGroup (hΛ : DihedralPointGroup 2 ≤ latticeSymmetryGroup Λ) :
    Nonempty ((WallpaperGroup.pointGroup (WallpaperGroup.cmm Λ hΛ)) ≃* DihedralPointGroup 2) := by
  have h_eq : WallpaperGroup.pointGroup (WallpaperGroup.cmm Λ hΛ) = DihedralPointGroup 2 := by
    ext A
    simp only [WallpaperGroup.pointGroup, Subgroup.mem_mk]
    constructor
    · intro ⟨v, hv⟩
      simp only [WallpaperGroup.cmm, Subgroup.mem_mk] at hv
      exact hv.2
    · intro hA
      use 0
      simp only [WallpaperGroup.cmm, Subgroup.mem_mk, EuclideanGroup2.mk]
      exact ⟨Λ.zero_mem, hA⟩
  exact ⟨MulEquiv.subgroupCongr h_eq⟩

/-- cm and cmm are the only wallpaper groups with centered rectangular lattice.

The classification follows from:
1. The point group of any wallpaper group is a crystallographic subgroup of O(2)
2. For a centered rectangular lattice, the symmetry group is D_2
3. The point group must be a subgroup of D_2 that contains -I (rotation by pi)
4. The only such subgroups are C_1, C_2, D_1, D_2
5. For symmorphic groups, the point group determines the wallpaper group

Note: This lemma states that any wallpaper group with centered rectangular lattice
and point group D_1 or D_2 is isomorphic to cm or cmm respectively.
-/
lemma centeredRectangular_wallpaperGroups (Γ : Subgroup EuclideanGroup2) (hΓ : IsWallpaperGroup Γ)
    (Λ' : Lattice2)
    (hΛ' : ∀ v, v ∈ Λ' ↔ (⟨Multiplicative.ofAdd v, 1⟩ : EuclideanGroup2) ∈
        WallpaperGroup.translationSubgroup Γ)
    (hcr : IsCenteredRectangularLattice Λ')
    (hD1 : DihedralPointGroup 1 ≤ latticeSymmetryGroup Λ')
    (hD2 : DihedralPointGroup 2 ≤ latticeSymmetryGroup Λ')
    (hPG : WallpaperGroup.pointGroup Γ = DihedralPointGroup 1 ∨
           WallpaperGroup.pointGroup Γ = DihedralPointGroup 2)
    (hSymm : IsSymmorphic Γ) :
    Nonempty (Γ ≃* WallpaperGroup.cm Λ' hD1) ∨
    Nonempty (Γ ≃* WallpaperGroup.cmm Λ' hD2) := by
  -- For symmorphic wallpaper groups, the group is determined by its translations and point group
  -- Since Γ is symmorphic, it splits as T ⋊ P where T = translation subgroup, P = point group
  -- The translation subgroup corresponds to the lattice Λ'
  -- So Γ ≅ {(v, A) | v ∈ Λ', A ∈ P} which is exactly cm or cmm depending on P
  sorry

end WallpaperGroups.Groups
