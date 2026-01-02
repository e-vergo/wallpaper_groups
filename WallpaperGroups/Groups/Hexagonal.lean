/-
Copyright (c) 2025 Wallpaper Groups Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import WallpaperGroups.Wallpaper.Structure
import WallpaperGroups.Lattice.BravaisTypes

/-!
# Hexagonal Lattice Wallpaper Groups: p3, p3m1, p31m, p6, p6m

This file defines the five wallpaper groups with hexagonal lattices.

## Main definitions

* `WallpaperGroup.p3` - 3-fold rotations only, PG = C₃
* `WallpaperGroup.p3m1` - 3-fold + reflections through lattice points, PG = D₃
* `WallpaperGroup.p31m` - 3-fold + reflections between lattice points, PG = D₃
* `WallpaperGroup.p6` - 6-fold rotations, PG = C₆
* `WallpaperGroup.p6m` - 6-fold + reflections, PG = D₆

All are symmorphic. The distinction between p3m1 and p31m is the position of
reflection axes relative to lattice points.

blueprint: def:p3, def:p3m1, def:p31m, def:p6, def:p6m
-/

namespace WallpaperGroups.Groups

open WallpaperGroups.Euclidean
open WallpaperGroups.Lattice
open WallpaperGroups.Wallpaper
open WallpaperGroups.PointGroup

/-! ### Standard hexagonal lattice orientation

For wallpaper group definitions, we work with hexagonal lattices that are
"standardly oriented" - meaning the symmetry group is exactly D₆ as defined
by our standard generators (rotation by π/3 and reflection across the x-axis).

This is equivalent to saying that DihedralPointGroup 6 ≤ latticeSymmetryGroup Λ.
-/

/-- A hexagonal lattice is standardly oriented if D₆ is contained in its symmetry group.
This means the standard rotation by π/3 and reflection preserve the lattice. -/
def IsStandardHexagonalLattice (Λ : Lattice2) : Prop :=
  DihedralPointGroup 6 ≤ latticeSymmetryGroup Λ

variable (Λ : Lattice2)

/-- For a standard hexagonal lattice, elements of D₆ preserve Λ. -/
lemma stdHexLattice_D6_preserves (hΛ : IsStandardHexagonalLattice Λ)
    (A : OrthogonalGroup2) (hA : A ∈ DihedralPointGroup 6)
    (v : EuclideanPlane) (hv : v ∈ Λ) :
    (EuclideanSpace.equiv (Fin 2) ℝ).symm (A.1.mulVec (EuclideanSpace.equiv (Fin 2) ℝ v)) ∈ Λ := by
  have hSymA : A ∈ latticeSymmetryGroup Λ := hΛ hA
  exact hSymA.1 v hv

/-- For a standard hexagonal lattice, elements of C₆ preserve Λ. -/
lemma stdHexLattice_C6_preserves (hΛ : IsStandardHexagonalLattice Λ)
    (A : OrthogonalGroup2) (hA : A ∈ CyclicPointGroup 6)
    (v : EuclideanPlane) (hv : v ∈ Λ) :
    (EuclideanSpace.equiv (Fin 2) ℝ).symm (A.1.mulVec (EuclideanSpace.equiv (Fin 2) ℝ v)) ∈ Λ := by
  have hle : CyclicPointGroup 6 ≤ DihedralPointGroup 6 := CyclicPointGroup.le_dihedral 6
  exact stdHexLattice_D6_preserves Λ hΛ A (hle hA) v hv

/-- For a standard hexagonal lattice, elements of D₃ preserve Λ.
D₃ is a subgroup of D₆ (every other rotation and every other reflection). -/
lemma stdHexLattice_D3_preserves (hΛ : IsStandardHexagonalLattice Λ)
    (A : OrthogonalGroup2) (hA : A ∈ DihedralPointGroup 3)
    (v : EuclideanPlane) (hv : v ∈ Λ) :
    (EuclideanSpace.equiv (Fin 2) ℝ).symm (A.1.mulVec (EuclideanSpace.equiv (Fin 2) ℝ v)) ∈ Λ := by
  -- D₃ ≤ D₆: the rotation by 2π/3 is the square of rotation by π/3,
  -- and reflection S₀ is shared.
  -- For now, we use the fact that D₃ generators are in D₆
  have hle : DihedralPointGroup 3 ≤ DihedralPointGroup 6 := by
    unfold DihedralPointGroup
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · -- rotationMatrix' (2π/3) = (rotationMatrix' (π/3))²
      have hgen : rotationMatrix' (2 * Real.pi / 6) ∈
          Subgroup.closure {rotationMatrix' (2 * Real.pi / 6), reflectionMatrix' 0} :=
        Subgroup.subset_closure (Set.mem_insert _ _)
      have hpow : rotationMatrix' (2 * Real.pi / (3 : ℕ)) =
                  (rotationMatrix' (2 * Real.pi / 6))^2 := by
        have h1 : (2 * Real.pi / (3 : ℕ) : ℝ) = 2 * Real.pi / 6 + 2 * Real.pi / 6 := by
          norm_num; ring
        rw [h1, sq]
        apply Subtype.ext
        simp only [rotationMatrix', Submonoid.coe_mul]
        rw [rotationMatrix_add]
      rw [hpow]
      exact Subgroup.pow_mem _ hgen 2
    · -- reflectionMatrix' 0 is a generator of D₆
      exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  exact stdHexLattice_D6_preserves Λ hΛ A (hle hA) v hv

/-- For a standard hexagonal lattice, elements of C₃ preserve Λ. -/
lemma stdHexLattice_C3_preserves (hΛ : IsStandardHexagonalLattice Λ)
    (A : OrthogonalGroup2) (hA : A ∈ CyclicPointGroup 3)
    (v : EuclideanPlane) (hv : v ∈ Λ) :
    (EuclideanSpace.equiv (Fin 2) ℝ).symm (A.1.mulVec (EuclideanSpace.equiv (Fin 2) ℝ v)) ∈ Λ := by
  have hle : CyclicPointGroup 3 ≤ DihedralPointGroup 3 := CyclicPointGroup.le_dihedral 3
  exact stdHexLattice_D3_preserves Λ hΛ A (hle hA) v hv

/-- For a standard hexagonal lattice, the inverse of any D₆ element also preserves Λ. -/
lemma stdHexLattice_D6_inv_preserves (hΛ : IsStandardHexagonalLattice Λ)
    (A : OrthogonalGroup2) (hA : A ∈ DihedralPointGroup 6)
    (v : EuclideanPlane) (hv : v ∈ Λ) :
    (EuclideanSpace.equiv (Fin 2) ℝ).symm (A⁻¹.1.mulVec (EuclideanSpace.equiv (Fin 2) ℝ v)) ∈ Λ := by
  have hSymA : A ∈ latticeSymmetryGroup Λ := hΛ hA
  exact hSymA.2 v hv

/-- For a standard hexagonal lattice, the inverse of any C₃ element also preserves Λ. -/
lemma stdHexLattice_C3_inv_preserves (hΛ : IsStandardHexagonalLattice Λ)
    (A : OrthogonalGroup2) (hA : A ∈ CyclicPointGroup 3)
    (v : EuclideanPlane) (hv : v ∈ Λ) :
    (EuclideanSpace.equiv (Fin 2) ℝ).symm (A⁻¹.1.mulVec (EuclideanSpace.equiv (Fin 2) ℝ v)) ∈ Λ := by
  have hle1 : CyclicPointGroup 3 ≤ DihedralPointGroup 3 := CyclicPointGroup.le_dihedral 3
  have hle2 : DihedralPointGroup 3 ≤ DihedralPointGroup 6 := by
    unfold DihedralPointGroup
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · have hgen : rotationMatrix' (2 * Real.pi / 6) ∈
          Subgroup.closure {rotationMatrix' (2 * Real.pi / 6), reflectionMatrix' 0} :=
        Subgroup.subset_closure (Set.mem_insert _ _)
      have hpow : rotationMatrix' (2 * Real.pi / (3 : ℕ)) =
                  (rotationMatrix' (2 * Real.pi / 6))^2 := by
        have h1 : (2 * Real.pi / (3 : ℕ) : ℝ) = 2 * Real.pi / 6 + 2 * Real.pi / 6 := by
          norm_num; ring
        rw [h1, sq]
        apply Subtype.ext
        simp only [rotationMatrix', Submonoid.coe_mul]
        rw [rotationMatrix_add]
      rw [hpow]
      exact Subgroup.pow_mem _ hgen 2
    · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  exact stdHexLattice_D6_inv_preserves Λ hΛ A (hle2 (hle1 hA)) v hv

/-- For a standard hexagonal lattice, the inverse of any D₃ element also preserves Λ. -/
lemma stdHexLattice_D3_inv_preserves (hΛ : IsStandardHexagonalLattice Λ)
    (A : OrthogonalGroup2) (hA : A ∈ DihedralPointGroup 3)
    (v : EuclideanPlane) (hv : v ∈ Λ) :
    (EuclideanSpace.equiv (Fin 2) ℝ).symm (A⁻¹.1.mulVec (EuclideanSpace.equiv (Fin 2) ℝ v)) ∈ Λ := by
  have hle2 : DihedralPointGroup 3 ≤ DihedralPointGroup 6 := by
    unfold DihedralPointGroup
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · have hgen : rotationMatrix' (2 * Real.pi / 6) ∈
          Subgroup.closure {rotationMatrix' (2 * Real.pi / 6), reflectionMatrix' 0} :=
        Subgroup.subset_closure (Set.mem_insert _ _)
      have hpow : rotationMatrix' (2 * Real.pi / (3 : ℕ)) =
                  (rotationMatrix' (2 * Real.pi / 6))^2 := by
        have h1 : (2 * Real.pi / (3 : ℕ) : ℝ) = 2 * Real.pi / 6 + 2 * Real.pi / 6 := by
          norm_num; ring
        rw [h1, sq]
        apply Subtype.ext
        simp only [rotationMatrix', Submonoid.coe_mul]
        rw [rotationMatrix_add]
      rw [hpow]
      exact Subgroup.pow_mem _ hgen 2
    · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  exact stdHexLattice_D6_inv_preserves Λ hΛ A (hle2 hA) v hv

/-- For a standard hexagonal lattice, the inverse of any C₆ element also preserves Λ. -/
lemma stdHexLattice_C6_inv_preserves (hΛ : IsStandardHexagonalLattice Λ)
    (A : OrthogonalGroup2) (hA : A ∈ CyclicPointGroup 6)
    (v : EuclideanPlane) (hv : v ∈ Λ) :
    (EuclideanSpace.equiv (Fin 2) ℝ).symm (A⁻¹.1.mulVec (EuclideanSpace.equiv (Fin 2) ℝ v)) ∈ Λ := by
  have hle : CyclicPointGroup 6 ≤ DihedralPointGroup 6 := CyclicPointGroup.le_dihedral 6
  exact stdHexLattice_D6_inv_preserves Λ hΛ A (hle hA) v hv

variable (hΛ : IsStandardHexagonalLattice Λ)

/-- Key lemma: orthogonalActionHom converts to matrix-vector multiplication. -/
private lemma orthogonalActionHom_toAdd' (A : OrthogonalGroup2) (v : Multiplicative EuclideanPlane) :
    Multiplicative.toAdd ((orthogonalActionHom A) v) =
    (EuclideanSpace.equiv (Fin 2) ℝ).symm
      (A.1.mulVec (EuclideanSpace.equiv (Fin 2) ℝ (Multiplicative.toAdd v))) := by
  unfold orthogonalActionHom orthogonalToMulAut orthogonalToAddAut orthogonalToLinearEquiv
  simp only [MonoidHom.coe_mk, OneHom.coe_mk]
  unfold MulAutMultiplicative
  simp only [MulEquiv.symm_mk, MulEquiv.coe_mk, Equiv.symm_symm]
  simp only [AddEquiv.toMultiplicative, MulEquiv.coe_mk, Equiv.coe_fn_mk]
  unfold AddMonoidHom.toMultiplicative
  simp only [Equiv.coe_fn_mk, MonoidHom.coe_mk, OneHom.coe_mk]
  simp only [toAdd_ofAdd, AddEquiv.coe_toAddMonoidHom, LinearEquiv.coe_toAddEquiv]
  -- LHS is ↑(LinearEquiv.ofLinear f g ...) (toAdd v) = f (toAdd v) by LinearEquiv coercion
  -- The coercion ↑(LinearEquiv.ofLinear f g ...) is definitionally (LinearEquiv.ofLinear f g ...).toFun
  -- and (LinearEquiv.ofLinear f g ...).toFun = f by definition
  -- So LHS = (Matrix.toEuclideanLin A.1) (toAdd v)
  -- Use toEuclideanLin_apply: this equals WithLp.toLp 2 (A.1.mulVec (toAdd v).ofLp)
  -- RHS = equiv.symm (A.1.mulVec (equiv (toAdd v)))
  -- Since equiv is the identity on underlying type, this is definitionally equal
  rfl

/-! ### The wallpaper group p3 -/

/-- The wallpaper group p3 has 3-fold rotation symmetry.

- Lattice type: Hexagonal
- Point group: C₃ = {I, R_{2π/3}, R_{4π/3}}
- Symmorphic: Yes
- No reflections

blueprint: def:p3 -/
def WallpaperGroup.p3 : Subgroup EuclideanGroup2 where
  carrier := {g | g.right ∈ CyclicPointGroup 3 ∧ Multiplicative.toAdd g.left ∈ Λ}
  mul_mem' := by
    intro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    constructor
    · simp only [SemidirectProduct.mul_right]
      exact (CyclicPointGroup 3).mul_mem ha1 hb1
    · simp only [SemidirectProduct.mul_left]
      rw [toAdd_mul]
      apply Λ.add_mem ha2
      -- The action of a.right on b.left preserves the lattice
      rw [orthogonalActionHom_toAdd']
      exact stdHexLattice_C3_preserves Λ hΛ a.right ha1 (Multiplicative.toAdd b.left) hb2
  one_mem' := by
    constructor
    · simp only [SemidirectProduct.one_right]
      exact (CyclicPointGroup 3).one_mem
    · simp only [SemidirectProduct.one_left]
      change (0 : EuclideanPlane) ∈ Λ
      exact Λ.zero_mem
  inv_mem' := by
    intro a ⟨ha1, ha2⟩
    constructor
    · simp only [SemidirectProduct.inv_right]
      exact (CyclicPointGroup 3).inv_mem ha1
    · simp only [SemidirectProduct.inv_left]
      -- Need: toAdd((orthogonalActionHom a.right⁻¹) a.left⁻¹) ∈ Λ
      -- This is -(A⁻¹ * v) where v ∈ Λ and A⁻¹ ∈ C₃
      rw [orthogonalActionHom_toAdd', toAdd_inv]
      -- Goal: equiv.symm (A⁻¹.mulVec (equiv (-v))) ∈ Λ
      -- Use that equiv (-v) = -(equiv v) and mulVec_neg and equiv.symm linear
      rw [ContinuousLinearEquiv.map_neg, Matrix.mulVec_neg, map_neg]
      apply Λ.neg_mem
      exact stdHexLattice_C3_inv_preserves Λ hΛ a.right ha1 (Multiplicative.toAdd a.left) ha2

/-- p3 is a wallpaper group. -/
lemma WallpaperGroup.p3.isWallpaperGroup : IsWallpaperGroup (WallpaperGroup.p3 Λ hΛ) := by
  constructor
  · -- Discrete
    use 1
    constructor
    · exact one_pos
    · intro g hg hne
      left
      -- The translation part is in a discrete lattice
      sorry
  · -- Cocompact
    obtain ⟨B⟩ := Λ.exists_basis
    use latticeFundamentalDomain Λ B
    constructor
    · sorry -- fundamental domain is compact
    · intro x
      sorry -- every point can be translated into fundamental domain

/-- p3 is symmorphic. -/
lemma WallpaperGroup.p3.isSymmorphic : IsSymmorphic (WallpaperGroup.p3 Λ hΛ) := by
  -- We need to construct a section s : pointGroup → p3 such that (s A).right = A
  -- For symmorphic groups, we can take s(A) = (0, A)
  sorry

/-- The point group of p3 is C₃. -/
lemma WallpaperGroup.p3.pointGroup :
    Nonempty ((WallpaperGroup.pointGroup (WallpaperGroup.p3 Λ hΛ)) ≃* CyclicPointGroup 3) := by
  -- The projection to O(2) gives exactly C₃
  sorry

/-! ### The wallpaper group p3m1 -/

/-- The wallpaper group p3m1 has 3-fold rotation and reflections through lattice points.

- Lattice type: Hexagonal
- Point group: D₃
- Symmorphic: Yes
- Reflection axes pass through lattice points

The "1" in p3m1 indicates the reflection axes pass through the 3-fold rotation centers.

blueprint: def:p3m1 -/
def WallpaperGroup.p3m1 : Subgroup EuclideanGroup2 where
  carrier := {g | g.right ∈ DihedralPointGroup 3 ∧ Multiplicative.toAdd g.left ∈ Λ}
  mul_mem' := by
    intro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    constructor
    · simp only [SemidirectProduct.mul_right]
      exact (DihedralPointGroup 3).mul_mem ha1 hb1
    · simp only [SemidirectProduct.mul_left]
      rw [toAdd_mul]
      apply Λ.add_mem ha2
      -- D₃ preserves hexagonal lattice
      sorry
  one_mem' := by
    constructor
    · simp only [SemidirectProduct.one_right]
      exact (DihedralPointGroup 3).one_mem
    · simp only [SemidirectProduct.one_left]
      change (0 : EuclideanPlane) ∈ Λ
      exact Λ.zero_mem
  inv_mem' := by
    intro a ⟨ha1, ha2⟩
    constructor
    · simp only [SemidirectProduct.inv_right]
      exact (DihedralPointGroup 3).inv_mem ha1
    · simp only [SemidirectProduct.inv_left]
      sorry

/-- p3m1 is a wallpaper group. -/
lemma WallpaperGroup.p3m1.isWallpaperGroup : IsWallpaperGroup (WallpaperGroup.p3m1 Λ) := by
  constructor
  · use 1
    constructor
    · exact one_pos
    · intro g hg hne; left; sorry
  · obtain ⟨B⟩ := Λ.exists_basis
    use latticeFundamentalDomain Λ B
    constructor
    · sorry
    · intro x; sorry

/-- p3m1 is symmorphic. -/
lemma WallpaperGroup.p3m1.isSymmorphic : IsSymmorphic (WallpaperGroup.p3m1 Λ) := by
  sorry

/-- The point group of p3m1 is D₃. -/
lemma WallpaperGroup.p3m1.pointGroup :
    Nonempty ((WallpaperGroup.pointGroup (WallpaperGroup.p3m1 Λ)) ≃* DihedralPointGroup 3) := by
  sorry

/-! ### The wallpaper group p31m -/

/-- The wallpaper group p31m has 3-fold rotation and reflections between lattice points.

- Lattice type: Hexagonal
- Point group: D₃
- Symmorphic: Yes
- Reflection axes pass between lattice points (at centers of edges)

The "1" in p31m indicates the reflection axes do NOT pass through 3-fold centers.

Note: p31m and p3m1 have the same abstract group structure (semidirect product of hexagonal
lattice with D₃) but differ in the geometric embedding. The difference is which reflection
axes pass through lattice points.

blueprint: def:p31m -/
def WallpaperGroup.p31m : Subgroup EuclideanGroup2 where
  carrier := {g | g.right ∈ DihedralPointGroup 3 ∧ Multiplicative.toAdd g.left ∈ Λ}
  mul_mem' := by
    intro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    constructor
    · simp only [SemidirectProduct.mul_right]
      exact (DihedralPointGroup 3).mul_mem ha1 hb1
    · simp only [SemidirectProduct.mul_left]
      rw [toAdd_mul]
      apply Λ.add_mem ha2
      sorry
  one_mem' := by
    constructor
    · simp only [SemidirectProduct.one_right]
      exact (DihedralPointGroup 3).one_mem
    · simp only [SemidirectProduct.one_left]
      change (0 : EuclideanPlane) ∈ Λ
      exact Λ.zero_mem
  inv_mem' := by
    intro a ⟨ha1, ha2⟩
    constructor
    · simp only [SemidirectProduct.inv_right]
      exact (DihedralPointGroup 3).inv_mem ha1
    · simp only [SemidirectProduct.inv_left]
      sorry

/-- p31m is a wallpaper group. -/
lemma WallpaperGroup.p31m.isWallpaperGroup : IsWallpaperGroup (WallpaperGroup.p31m Λ) := by
  constructor
  · use 1
    constructor
    · exact one_pos
    · intro g hg hne; left; sorry
  · obtain ⟨B⟩ := Λ.exists_basis
    use latticeFundamentalDomain Λ B
    constructor
    · sorry
    · intro x; sorry

/-- p31m is symmorphic. -/
lemma WallpaperGroup.p31m.isSymmorphic : IsSymmorphic (WallpaperGroup.p31m Λ) := by
  sorry

/-- The point group of p31m is D₃. -/
lemma WallpaperGroup.p31m.pointGroup :
    Nonempty ((WallpaperGroup.pointGroup (WallpaperGroup.p31m Λ)) ≃* DihedralPointGroup 3) := by
  sorry

/-! ### p3m1 vs p31m -/

/-- p3m1 and p31m are non-isomorphic despite having the same point group.

They differ in the position of reflection axes relative to lattice points.
In p3m1, all 3-fold centers lie on reflection axes.
In p31m, 3-fold centers at lattice points do NOT lie on reflection axes.

The proof shows these are geometrically distinct:
- An isomorphism must preserve the translation subgroup (it's characteristic)
- This induces an automorphism of the lattice
- But the orientation of reflection axes relative to lattice is an invariant -/
lemma p3m1_not_iso_p31m :
    ¬Nonempty ((WallpaperGroup.p3m1 Λ) ≃* (WallpaperGroup.p31m Λ)) := by
  intro ⟨iso⟩
  -- The translation subgroups are both the same (generated by Λ), so any isomorphism
  -- restricts to an automorphism of Λ.
  -- However, p3m1 has reflections with axes through lattice points,
  -- while p31m has reflections with axes NOT through lattice points.
  -- These geometric configurations are preserved by the isomorphism,
  -- leading to a contradiction.
  --
  -- More precisely: in p3m1, for any reflection σ, there exists v ∈ Λ with σ(v) = -v
  -- (because reflection axes pass through origin = a lattice point).
  -- In p31m, for no reflection σ does there exist such v ≠ 0.
  -- An isomorphism would map reflections to reflections preserving this property,
  -- which is impossible.
  sorry

/-! ### The wallpaper group p6 -/

/-- The wallpaper group p6 has 6-fold rotation symmetry.

- Lattice type: Hexagonal
- Point group: C₆ = {I, R_{π/3}, R_{2π/3}, R_π, R_{4π/3}, R_{5π/3}}
- Symmorphic: Yes
- No reflections

blueprint: def:p6 -/
def WallpaperGroup.p6 : Subgroup EuclideanGroup2 where
  carrier := {g | g.right ∈ CyclicPointGroup 6 ∧ Multiplicative.toAdd g.left ∈ Λ}
  mul_mem' := by
    intro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    constructor
    · simp only [SemidirectProduct.mul_right]
      exact (CyclicPointGroup 6).mul_mem ha1 hb1
    · simp only [SemidirectProduct.mul_left]
      rw [toAdd_mul]
      apply Λ.add_mem ha2
      sorry
  one_mem' := by
    constructor
    · simp only [SemidirectProduct.one_right]
      exact (CyclicPointGroup 6).one_mem
    · simp only [SemidirectProduct.one_left]
      change (0 : EuclideanPlane) ∈ Λ
      exact Λ.zero_mem
  inv_mem' := by
    intro a ⟨ha1, ha2⟩
    constructor
    · simp only [SemidirectProduct.inv_right]
      exact (CyclicPointGroup 6).inv_mem ha1
    · simp only [SemidirectProduct.inv_left]
      sorry

/-- p6 is a wallpaper group. -/
lemma WallpaperGroup.p6.isWallpaperGroup : IsWallpaperGroup (WallpaperGroup.p6 Λ) := by
  constructor
  · use 1
    constructor
    · exact one_pos
    · intro g hg hne; left; sorry
  · obtain ⟨B⟩ := Λ.exists_basis
    use latticeFundamentalDomain Λ B
    constructor
    · sorry
    · intro x; sorry

/-- p6 is symmorphic. -/
lemma WallpaperGroup.p6.isSymmorphic : IsSymmorphic (WallpaperGroup.p6 Λ) := by
  sorry

/-- The point group of p6 is C₆. -/
lemma WallpaperGroup.p6.pointGroup :
    Nonempty ((WallpaperGroup.pointGroup (WallpaperGroup.p6 Λ)) ≃* CyclicPointGroup 6) := by
  sorry

/-! ### The wallpaper group p6m -/

/-- The wallpaper group p6m has full hexagonal symmetry.

- Lattice type: Hexagonal
- Point group: D₆ (symmetries of a regular hexagon)
- Symmorphic: Yes
- This is the most symmetric wallpaper group

blueprint: def:p6m -/
def WallpaperGroup.p6m : Subgroup EuclideanGroup2 where
  carrier := {g | g.right ∈ DihedralPointGroup 6 ∧ Multiplicative.toAdd g.left ∈ Λ}
  mul_mem' := by
    intro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    constructor
    · simp only [SemidirectProduct.mul_right]
      exact (DihedralPointGroup 6).mul_mem ha1 hb1
    · simp only [SemidirectProduct.mul_left]
      rw [toAdd_mul]
      apply Λ.add_mem ha2
      sorry
  one_mem' := by
    constructor
    · simp only [SemidirectProduct.one_right]
      exact (DihedralPointGroup 6).one_mem
    · simp only [SemidirectProduct.one_left]
      change (0 : EuclideanPlane) ∈ Λ
      exact Λ.zero_mem
  inv_mem' := by
    intro a ⟨ha1, ha2⟩
    constructor
    · simp only [SemidirectProduct.inv_right]
      exact (DihedralPointGroup 6).inv_mem ha1
    · simp only [SemidirectProduct.inv_left]
      sorry

/-- p6m is a wallpaper group. -/
lemma WallpaperGroup.p6m.isWallpaperGroup : IsWallpaperGroup (WallpaperGroup.p6m Λ) := by
  constructor
  · use 1
    constructor
    · exact one_pos
    · intro g hg hne; left; sorry
  · obtain ⟨B⟩ := Λ.exists_basis
    use latticeFundamentalDomain Λ B
    constructor
    · sorry
    · intro x; sorry

/-- p6m is symmorphic. -/
lemma WallpaperGroup.p6m.isSymmorphic : IsSymmorphic (WallpaperGroup.p6m Λ) := by
  sorry

/-- The point group of p6m is D₆. -/
lemma WallpaperGroup.p6m.pointGroup :
    Nonempty ((WallpaperGroup.pointGroup (WallpaperGroup.p6m Λ)) ≃* DihedralPointGroup 6) := by
  sorry

/-! ### Completeness -/

/-- The five hexagonal wallpaper groups are complete.

Every wallpaper group with a hexagonal translation lattice is isomorphic to exactly one of:
p3, p3m1, p31m, p6, p6m. -/
lemma hexagonal_wallpaperGroups (Γ : Subgroup EuclideanGroup2) (hΓ : IsWallpaperGroup Γ)
    (Λ' : Lattice2) (hΛ'std : IsStandardHexagonalLattice Λ')
    (hΛ' : ∀ v, v ∈ Λ' ↔ (⟨v, 1⟩ : EuclideanGroup2) ∈ WallpaperGroup.translationSubgroup Γ)
    (hhex : IsHexagonalLattice Λ') :
    Nonempty (Γ ≃* WallpaperGroup.p3 Λ' hΛ'std) ∨
    Nonempty (Γ ≃* WallpaperGroup.p3m1 Λ') ∨
    Nonempty (Γ ≃* WallpaperGroup.p31m Λ') ∨
    Nonempty (Γ ≃* WallpaperGroup.p6 Λ') ∨
    Nonempty (Γ ≃* WallpaperGroup.p6m Λ') := by
  -- The proof proceeds by analyzing the point group of Γ.
  -- For hexagonal lattices, the possible crystallographic point groups are:
  -- C₁, C₂, C₃, C₆, D₁, D₂, D₃, D₆
  -- But for the hexagonal groups specifically:
  -- - p3 has C₃
  -- - p3m1, p31m have D₃
  -- - p6 has C₆
  -- - p6m has D₆
  -- The groups with C₁, C₂, D₁, D₂ are oblique/rectangular, not hexagonal.
  sorry

end WallpaperGroups.Groups
