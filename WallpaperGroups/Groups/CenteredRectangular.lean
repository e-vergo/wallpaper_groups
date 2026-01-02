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
  simp at h
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
    simp only [WallpaperGroup.cm, Subgroup.mem_mk, Set.mem_setOf_eq] at hg
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
        simp only [WallpaperGroup.cm, Subgroup.mem_mk, Set.mem_setOf_eq,
                   SemidirectProduct.mk, toAdd_ofAdd]
        constructor
        · -- floor_val ∈ Λ
          have hfloor := (ZSpan.floor B.toBasis x).2
          rw [Λ.carrier_eq_span B]
          simp only [Submodule.mem_toAddSubgroup]
          exact hfloor
        · exact (DihedralPointGroup 1).one_mem
      use ⟨Multiplicative.ofAdd floor_val, 1⟩, hmem
      -- x - floor_val ∈ parallelepiped
      simp only [SemidirectProduct.mk, toAdd_ofAdd]
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
        simp only [EuclideanGroup2.mk, SemidirectProduct.mk, toAdd_ofAdd]
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
        simp only [SemidirectProduct.mul_left, SemidirectProduct.mk, ofAdd_zero]
        simp only [orthogonalActionHom, orthogonalToMulAut, orthogonalToAddAut,
                   orthogonalToLinearEquiv, MonoidHom.coe_mk, OneHom.coe_mk, MulAutMultiplicative,
                   MulEquiv.symm_mk, MulEquiv.coe_mk, Equiv.symm_symm,
                   AddEquiv.toMultiplicative, Equiv.coe_fn_mk]
        unfold AddMonoidHom.toMultiplicative
        simp only [Equiv.coe_fn_mk, MonoidHom.coe_mk, OneHom.coe_mk,
                   AddEquiv.coe_toAddMonoidHom, LinearEquiv.coe_toAddEquiv,
                   toAdd_one, map_zero, ofAdd_zero, mul_one]
      · -- right component
        simp only [SemidirectProduct.mul_right, SemidirectProduct.mk]
  }
  use s
  intro A
  simp only [EuclideanGroup2.mk, SemidirectProduct.mk]
  rfl

/-- The point group of cm is D_1. -/
lemma WallpaperGroup.cm.pointGroup (hΛ : DihedralPointGroup 1 ≤ latticeSymmetryGroup Λ) :
    Nonempty ((WallpaperGroup.pointGroup (WallpaperGroup.cm Λ hΛ)) ≃* DihedralPointGroup 1) := by
  -- We show that pointGroup cm = D_1 as subgroups of O(2)
  -- Direction 1: if A ∈ pointGroup cm, then ∃ v with (v, A) ∈ cm, so A ∈ D_1
  -- Direction 2: if A ∈ D_1, then (0, A) ∈ cm (since 0 ∈ Λ), so A ∈ pointGroup cm
  have h_eq : WallpaperGroup.pointGroup (WallpaperGroup.cm Λ hΛ) = DihedralPointGroup 1 := by
    ext A
    simp only [WallpaperGroup.pointGroup, Subgroup.mem_mk, Set.mem_setOf_eq]
    constructor
    · intro ⟨v, hv⟩
      simp only [WallpaperGroup.cm, Subgroup.mem_mk] at hv
      exact hv.2
    · intro hA
      use 0
      simp only [WallpaperGroup.cm, Subgroup.mem_mk,
                 EuclideanGroup2.mk, SemidirectProduct.mk, toAdd_ofAdd]
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
    simp only [WallpaperGroup.cmm, Subgroup.mem_mk, Set.mem_setOf_eq] at hg
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
        simp only [WallpaperGroup.cmm, Subgroup.mem_mk, Set.mem_setOf_eq,
                   SemidirectProduct.mk, toAdd_ofAdd]
        constructor
        · have hfloor := (ZSpan.floor B.toBasis x).2
          rw [Λ.carrier_eq_span B]
          simp only [Submodule.mem_toAddSubgroup]
          exact hfloor
        · exact (DihedralPointGroup 2).one_mem
      use ⟨Multiplicative.ofAdd floor_val, 1⟩, hmem
      simp only [SemidirectProduct.mk, toAdd_ofAdd]
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
      · simp only [EuclideanGroup2.mk, SemidirectProduct.mk, toAdd_ofAdd]
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
      · simp only [SemidirectProduct.mul_left, SemidirectProduct.mk, ofAdd_zero]
        simp only [orthogonalActionHom, orthogonalToMulAut, orthogonalToAddAut,
                   orthogonalToLinearEquiv, MonoidHom.coe_mk, OneHom.coe_mk, MulAutMultiplicative,
                   MulEquiv.symm_mk, MulEquiv.coe_mk, Equiv.symm_symm,
                   AddEquiv.toMultiplicative, Equiv.coe_fn_mk]
        unfold AddMonoidHom.toMultiplicative
        simp only [Equiv.coe_fn_mk, MonoidHom.coe_mk, OneHom.coe_mk,
                   AddEquiv.coe_toAddMonoidHom, LinearEquiv.coe_toAddEquiv,
                   toAdd_one, map_zero, ofAdd_zero, mul_one]
      · simp only [SemidirectProduct.mul_right, SemidirectProduct.mk]
  }
  use s
  intro A
  simp only [EuclideanGroup2.mk, SemidirectProduct.mk]
  rfl

/-- The point group of cmm is D_2. -/
lemma WallpaperGroup.cmm.pointGroup (hΛ : DihedralPointGroup 2 ≤ latticeSymmetryGroup Λ) :
    Nonempty ((WallpaperGroup.pointGroup (WallpaperGroup.cmm Λ hΛ)) ≃* DihedralPointGroup 2) := by
  have h_eq : WallpaperGroup.pointGroup (WallpaperGroup.cmm Λ hΛ) = DihedralPointGroup 2 := by
    ext A
    simp only [WallpaperGroup.pointGroup, Subgroup.mem_mk, Set.mem_setOf_eq]
    constructor
    · intro ⟨v, hv⟩
      simp only [WallpaperGroup.cmm, Subgroup.mem_mk] at hv
      exact hv.2
    · intro hA
      use 0
      simp only [WallpaperGroup.cmm, Subgroup.mem_mk,
                 EuclideanGroup2.mk, SemidirectProduct.mk, toAdd_ofAdd]
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
  cases hPG with
  | inl hP1 =>
    -- Point group is D_1, so Γ ≅ cm
    left
    -- We construct the isomorphism explicitly
    -- f : Γ → cm defined by g ↦ g (identity on underlying elements)
    -- This works because membership conditions are equivalent
    have hiso : ∀ g : EuclideanGroup2, g ∈ Γ ↔ g ∈ WallpaperGroup.cm Λ' hD1 := by
      intro g
      simp only [WallpaperGroup.cm, Subgroup.mem_mk, Set.mem_setOf_eq]
      constructor
      · intro hg
        constructor
        · -- g.left ∈ Λ' iff (g.left, 1) ∈ translationSubgroup Γ
          -- For symmorphic groups, if g = (v, A) ∈ Γ then (v, 1) ∈ Γ (via section)
          -- Actually we need: toAdd g.left ∈ Λ'
          -- By hΛ': v ∈ Λ' ↔ (ofAdd v, 1) ∈ translationSubgroup Γ
          -- The translation subgroup is Γ ⊓ T where T = {(v, 1)}
          -- For wallpaper groups, the lattice is exactly the translation part
          -- Since hSymm: there exists a section s : PG → Γ
          -- For any (v, A) ∈ Γ, we have (v, A) * s(A⁻¹) = (v + A(0), 1) = (v, 1)
          -- So (v, 1) ∈ Γ, hence v ∈ Λ'
          obtain ⟨s, hs⟩ := hSymm
          have hA_in_PG : g.right ∈ WallpaperGroup.pointGroup Γ := by
            simp only [WallpaperGroup.pointGroup, Subgroup.mem_mk, Set.mem_setOf_eq]
            use Multiplicative.toAdd g.left
            simp only [EuclideanGroup2.mk, SemidirectProduct.mk, ofAdd_toAdd]
            exact hg
          let A_sub : WallpaperGroup.pointGroup Γ := ⟨g.right, hA_in_PG⟩
          have hinv : A_sub⁻¹ ∈ WallpaperGroup.pointGroup Γ :=
            (WallpaperGroup.pointGroup Γ).inv_mem A_sub.2
          let Ainv_sub : WallpaperGroup.pointGroup Γ := ⟨g.right⁻¹, hinv⟩
          have hprod : (⟨g, hg⟩ : Γ) * s Ainv_sub ∈ Γ := Γ.mul_mem hg (s Ainv_sub).2
          -- The product g * s(A⁻¹) has right component = A * A⁻¹ = 1
          have hright : (g * (s Ainv_sub).1).right = 1 := by
            simp only [SemidirectProduct.mul_right]
            have heq := hs Ainv_sub
            simp only [Subtype.coe_mk] at heq
            rw [heq]
            exact mul_inv_cancel g.right
          -- So it's a pure translation in Γ, hence in Λ'
          have htrans_mem : (g * (s Ainv_sub).1) ∈ WallpaperGroup.translationSubgroup Γ := by
            simp only [WallpaperGroup.translationSubgroup, Subgroup.mem_inf]
            constructor
            · exact hprod
            · simp only [Euclidean.translationSubgroup, Subgroup.mem_mk, Set.mem_setOf_eq]
              exact hright
          -- Compute the left component
          have hleft_eq : Multiplicative.toAdd (g * (s Ainv_sub).1).left =
              Multiplicative.toAdd g.left + Multiplicative.toAdd ((orthogonalActionHom g.right)
                (s Ainv_sub).1.left) := by
            simp only [SemidirectProduct.mul_left, toAdd_mul]
          -- (orthogonalActionHom g.right) maps (s A⁻¹).left to some value
          -- s(A⁻¹) has left component = ofAdd 0 (from the section construction)
          have hs_left : (s Ainv_sub).1.left = Multiplicative.ofAdd 0 := by
            have heq := hs Ainv_sub
            -- s A has right = A, so s A = (?, A)
            -- From IsSymmorphic: (s A).right = A
            -- But we need to know the left component is 0
            -- This requires knowing s is the canonical section A ↦ (0, A)
            -- Actually IsSymmorphic only guarantees the right component
            -- We need more structure here...
            -- For now, we use that the section exists and any section works for translations
            sorry
          sorry
        · -- g.right ∈ D_1
          have hA := hA_in_PG
          rw [hP1] at hA
          simp only [WallpaperGroup.pointGroup, Subgroup.mem_mk, Set.mem_setOf_eq] at hA
          exact hA
      · intro ⟨htrans, horth⟩
        -- Need to show g ∈ Γ
        -- Since Γ is symmorphic with point group D_1 and translations Λ'
        -- g = (v, A) with v ∈ Λ' and A ∈ D_1
        -- Using the section s : D_1 → Γ, we have s(A) ∈ Γ
        -- Also (v, 1) ∈ Γ (as a translation)
        -- So (v, 1) * s(A) = (v, A) ∈ Γ? No, that's not right...
        -- Actually (v, 1) * (w, A) = (v + w, A) not (v, A)
        -- We need (v, A) = (v - A(w), 1) * (w, A) where s(A) = (w, A)
        -- Hmm, this is getting complicated. Need to think about this more carefully.
        sorry
    sorry
  | inr hP2 =>
    -- Point group is D_2, so Γ ≅ cmm
    right
    sorry

end WallpaperGroups.Groups
