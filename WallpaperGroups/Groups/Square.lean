/-
Copyright (c) 2025 Wallpaper Groups Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import WallpaperGroups.Wallpaper.Structure
import WallpaperGroups.Lattice.BravaisTypes
import Mathlib.Algebra.Group.TypeTags.Basic

/-!
# Square Lattice Wallpaper Groups: p4, p4m, p4g

This file defines the three wallpaper groups with square lattices.

## Main definitions

* `WallpaperGroup.p4` - 4-fold rotations, PG = C₄, symmorphic
* `WallpaperGroup.p4m` - 4-fold rotations + reflections, PG = D₄, symmorphic
* `WallpaperGroup.p4g` - 4-fold rotations + glide reflections, PG = D₄, non-symmorphic

blueprint: def:p4, def:p4m, def:p4g
-/

namespace WallpaperGroups.Groups

open WallpaperGroups.Euclidean
open WallpaperGroups.Lattice
open WallpaperGroups.Wallpaper
open WallpaperGroups.PointGroup

variable (Λ : Lattice2) (hΛ : IsSquareLattice Λ)

/-- Helper lemma: orthogonalActionHom action converted via toAdd gives toEuclideanLin. -/
lemma orthogonalActionHom_toAdd (A : OrthogonalGroup2) (v : Multiplicative EuclideanPlane) :
    Multiplicative.toAdd ((orthogonalActionHom A) v) =
    Matrix.toEuclideanLin A.1 (Multiplicative.toAdd v) := by
  unfold orthogonalActionHom orthogonalToMulAut orthogonalToAddAut orthogonalToLinearEquiv
  simp only [MonoidHom.coe_mk, OneHom.coe_mk]
  unfold MulAutMultiplicative
  simp only [MulEquiv.symm_mk, MulEquiv.coe_mk, Equiv.symm_symm]
  simp only [AddEquiv.toMultiplicative, Equiv.coe_fn_mk]
  unfold AddMonoidHom.toMultiplicative
  simp only [Equiv.coe_fn_mk, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd,
             AddEquiv.coe_toAddMonoidHom, LinearEquiv.coe_toAddEquiv]
  rfl

/-- Helper: elements of C₄ preserve a square lattice.

This follows from the definition of square lattice: Sym(Λ) ≃* D₄,
and C₄ ⊆ D₄. The isomorphism carries C₄ into the lattice symmetry group.

For a proper proof, this would require showing that the isomorphism
Sym(Λ) ≃* D₄ is compatible with the inclusion C₄ ≤ D₄.
We use sorry here as this requires significant infrastructure. -/
lemma squareLattice_C4_preserves (hΛ : IsSquareLattice Λ) (A : OrthogonalGroup2)
    (hA : A ∈ CyclicPointGroup 4) : A ∈ latticeSymmetryGroup Λ := by
  -- Get the D₄ isomorphism from the square lattice hypothesis
  obtain ⟨B, hB_orth, hB_eq, ⟨hD4_iso⟩⟩ := hΛ
  -- C₄ ⊆ D₄
  have hC4_le_D4 : CyclicPointGroup 4 ≤ DihedralPointGroup 4 := CyclicPointGroup.le_dihedral 4
  have hA_in_D4 : A ∈ DihedralPointGroup 4 := hC4_le_D4 hA
  -- Use the inverse isomorphism to get A' ∈ Sym(Λ) with hD4_iso A' = A
  -- Since hD4_iso is an isomorphism Sym(Λ) ≃* D₄, we have hD4_iso.symm : D₄ ≃* Sym(Λ)
  -- So hD4_iso.symm ⟨A, hA_in_D4⟩ gives an element of Sym(Λ)
  -- But this element might not equal A as an element of O(2)!
  --
  -- The key issue is that an abstract isomorphism doesn't preserve the embedding.
  -- For a correct proof, we would need to show that for a square lattice with
  -- orthogonal equal-length basis (a, b), the 90° rotation matrix preserves the lattice.
  -- This is a geometric fact that requires computing the action of rotation on the basis.
  sorry

/-- Helper: The translation lattice is closed under the action of C₄ for square lattices. -/
lemma squareLattice_C4_action_mem (hΛ : IsSquareLattice Λ) (v : EuclideanPlane) (hv : v ∈ Λ)
    (A : OrthogonalGroup2) (hA : A ∈ CyclicPointGroup 4) :
    Matrix.toEuclideanLin A.1 v ∈ Λ := by
  have hA_sym : A ∈ latticeSymmetryGroup Λ := squareLattice_C4_preserves Λ hΛ A hA
  -- A ∈ Sym(Λ) means A preserves Λ
  have hpres : IsLatticePreserving Λ A := hA_sym.1
  -- Apply the preservation property
  have h := hpres v hv
  -- The result is (equiv).symm (A.1.mulVec (equiv v)) ∈ Λ
  -- We need to show Matrix.toEuclideanLin A.1 v ∈ Λ
  -- toEuclideanLin A.1 v = equiv.symm (A.1.mulVec (equiv v))
  convert h

/-- The wallpaper group p4 has 4-fold rotation symmetry.

- Lattice type: Square
- Point group: C₄ = {I, R_{π/2}, R_π, R_{3π/2}}
- Symmorphic: Yes
- No reflections, only rotations

blueprint: def:p4 -/
def WallpaperGroup.p4 : Subgroup EuclideanGroup2 where
  carrier := {g | ∃ (A : OrthogonalGroup2),
    A ∈ CyclicPointGroup 4 ∧
    g.right = A ∧
    g.left ∈ Λ}
  mul_mem' := by
    intro a b ha hb
    obtain ⟨Aa, hAa_mem, hAa_eq, ha_left⟩ := ha
    obtain ⟨Ab, hAb_mem, hAb_eq, hb_left⟩ := hb
    use a.right * b.right
    refine ⟨?_, rfl, ?_⟩
    · -- a.right * b.right ∈ CyclicPointGroup 4
      rw [hAa_eq, hAb_eq]
      exact Subgroup.mul_mem _ hAa_mem hAb_mem
    · -- (a * b).left ∈ Λ
      simp only [SemidirectProduct.mul_left]
      change Multiplicative.toAdd (a.left * (orthogonalActionHom a.right) b.left) ∈ Λ.carrier
      rw [toAdd_mul]
      apply Λ.add_mem ha_left
      -- Use the helper lemma to connect orthogonalActionHom to toEuclideanLin
      rw [orthogonalActionHom_toAdd]
      have hAa_mem' : a.right ∈ CyclicPointGroup 4 := by rw [hAa_eq]; exact hAa_mem
      exact squareLattice_C4_action_mem Λ hΛ (Multiplicative.toAdd b.left) hb_left a.right hAa_mem'
  one_mem' := by
    use 1
    refine ⟨Subgroup.one_mem _, rfl, ?_⟩
    simp only [SemidirectProduct.one_left]
    change Multiplicative.toAdd 1 ∈ Λ.carrier
    rw [toAdd_one]
    exact Λ.zero_mem
  inv_mem' := by
    intro a ha
    obtain ⟨A, hA_mem, hA_eq, ha_left⟩ := ha
    use a.right⁻¹
    refine ⟨?_, rfl, ?_⟩
    · rw [hA_eq]; exact Subgroup.inv_mem _ hA_mem
    · -- a⁻¹.left ∈ Λ
      simp only [SemidirectProduct.inv_left]
      -- a⁻¹.left = (orthogonalActionHom a.right⁻¹) a.left⁻¹
      -- First convert to toAdd form, then use the helper lemma
      change Multiplicative.toAdd ((orthogonalActionHom a.right⁻¹) a.left⁻¹) ∈ Λ.carrier
      rw [orthogonalActionHom_toAdd]
      -- Now need to show: toEuclideanLin (a.right⁻¹).1 (toAdd a.left⁻¹) ∈ Λ
      rw [toAdd_inv]
      simp only [map_neg]
      apply Λ.neg_mem
      have hA_mem' : a.right ∈ CyclicPointGroup 4 := by rw [hA_eq]; exact hA_mem
      have hAinv_mem : a.right⁻¹ ∈ CyclicPointGroup 4 := Subgroup.inv_mem _ hA_mem'
      exact squareLattice_C4_action_mem Λ hΛ (Multiplicative.toAdd a.left) ha_left a.right⁻¹ hAinv_mem

/-- p4 is a wallpaper group. -/
lemma WallpaperGroup.p4.isWallpaperGroup : IsWallpaperGroup (WallpaperGroup.p4 Λ hΛ) := by
  sorry

/-- p4 is symmorphic. -/
lemma WallpaperGroup.p4.isSymmorphic : IsSymmorphic (WallpaperGroup.p4 Λ hΛ) := by
  sorry

/-- The point group of p4 is C₄. -/
lemma WallpaperGroup.p4.pointGroup :
    Nonempty ((WallpaperGroup.pointGroup (WallpaperGroup.p4 Λ hΛ)) ≃* CyclicPointGroup 4) := by
  sorry

/-- The wallpaper group p4m has 4-fold rotation and reflection symmetry.

- Lattice type: Square
- Point group: D₄ (symmetries of a square)
- Symmorphic: Yes
- Reflections along axes and diagonals

blueprint: def:p4m -/
def WallpaperGroup.p4m : Subgroup EuclideanGroup2 where
  carrier := {g | ∃ (A : OrthogonalGroup2),
    A ∈ DihedralPointGroup 4 ∧
    g.right = A ∧
    g.left ∈ Λ}
  mul_mem' := by intro a b ha hb; sorry
  one_mem' := by sorry
  inv_mem' := by intro a ha; sorry

/-- p4m is a wallpaper group. -/
lemma WallpaperGroup.p4m.isWallpaperGroup : IsWallpaperGroup (WallpaperGroup.p4m Λ) := by
  sorry

/-- p4m is symmorphic. -/
lemma WallpaperGroup.p4m.isSymmorphic : IsSymmorphic (WallpaperGroup.p4m Λ) := by
  sorry

/-- The point group of p4m is D₄. -/
lemma WallpaperGroup.p4m.pointGroup :
    Nonempty ((WallpaperGroup.pointGroup (WallpaperGroup.p4m Λ)) ≃* DihedralPointGroup 4) := by
  sorry

/-- The wallpaper group p4g has 4-fold rotation and glide reflection symmetry.

- Lattice type: Square
- Point group: D₄
- Symmorphic: No
- Glide reflections along diagonals, no true diagonal reflections

blueprint: def:p4g -/
def WallpaperGroup.p4g (Λ : Lattice2) : Subgroup EuclideanGroup2 where
  carrier := {g | g.left ∈ Λ ∧ sorry}
  mul_mem' := by intro a b ha hb; sorry
  one_mem' := by sorry
  inv_mem' := by intro a ha; sorry

/-- p4g is a wallpaper group. -/
lemma WallpaperGroup.p4g.isWallpaperGroup : IsWallpaperGroup (WallpaperGroup.p4g Λ) := by
  sorry

/-- p4g is non-symmorphic. -/
lemma WallpaperGroup.p4g.not_isSymmorphic : ¬IsSymmorphic (WallpaperGroup.p4g Λ) := by
  sorry

/-- The point group of p4g is D₄. -/
lemma WallpaperGroup.p4g.pointGroup :
    Nonempty ((WallpaperGroup.pointGroup (WallpaperGroup.p4g Λ)) ≃* DihedralPointGroup 4) := by
  sorry

/-- p4, p4m, and p4g are the only wallpaper groups with square lattice. -/
lemma square_wallpaperGroups (Γ : Subgroup EuclideanGroup2) (hΓ : IsWallpaperGroup Γ)
    (Λ' : Lattice2)
    (hΛ' : ∀ v, v ∈ Λ' ↔ (⟨v, 1⟩ : EuclideanGroup2) ∈ WallpaperGroup.translationSubgroup Γ)
    (hsq : IsSquareLattice Λ') :
    Nonempty (Γ ≃* WallpaperGroup.p4 Λ' hsq) ∨
    Nonempty (Γ ≃* WallpaperGroup.p4m Λ') ∨
    Nonempty (Γ ≃* WallpaperGroup.p4g Λ') := by
  sorry

end WallpaperGroups.Groups
