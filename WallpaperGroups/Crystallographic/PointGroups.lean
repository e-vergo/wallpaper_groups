/-
Copyright (c) 2025 Wallpaper Groups Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import WallpaperGroups.Crystallographic.Restriction
import WallpaperGroups.PointGroup.FiniteO2Classification
import WallpaperGroups.Lattice.BravaisTypes
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Crystallographic Point Groups

This file defines crystallographic point groups and enumerates all 10 of them.

## Main definitions

* `IsCrystallographicPointGroup` - A point group compatible with some lattice

## Main results

* `crystallographic_point_groups` - The 10 crystallographic point groups are:
  C₁, C₂, C₃, C₄, C₆, D₁, D₂, D₃, D₄, D₆
* `compatible_point_groups` - Which point groups are compatible with each Bravais type

blueprint: cor:crystallographic_enumeration
-/

namespace WallpaperGroups.Crystallographic

open WallpaperGroups.Euclidean
open WallpaperGroups.PointGroup
open WallpaperGroups.Lattice

/-- A point group H ⊂ O(2) is crystallographic if it can be realized as the
symmetry group of some lattice.

Equivalently, H is finite and all rotations in H have order dividing 1, 2, 3, 4, or 6.

blueprint: def:crystallographic_point_group -/
def IsCrystallographicPointGroup (H : Subgroup OrthogonalGroup2) : Prop :=
  Finite H ∧
  ∀ A ∈ H, A ∈ SpecialOrthogonalGroup2 →
    ∃ n ∈ ({1, 2, 3, 4, 6} : Set ℕ), A^n = 1

/-! ### Helper lemmas for cyclic and dihedral groups -/

-- Helper: R_{2π/n}^n = 1
private lemma rotationMatrix'_pow_n' (n : ℕ) [NeZero n] :
    (rotationMatrix' (2 * Real.pi / n)) ^ n = 1 := by
  rw [rotationMatrix'_pow]
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
  have h2 : (n : ℝ) * (2 * Real.pi / n) = 2 * Real.pi := by field_simp
  rw [h2, rotationMatrix'_two_pi]

-- Helper: order of the generator of CyclicPointGroup n
private lemma orderOf_rotationMatrix'_generator' (n : ℕ) [NeZero n] :
    orderOf (rotationMatrix' (2 * Real.pi / n)) = n := by
  have h1 : CyclicPointGroup n = Subgroup.zpowers (rotationMatrix' (2 * Real.pi / n)) := by
    unfold CyclicPointGroup
    exact Subgroup.zpowers_eq_closure (rotationMatrix' (2 * Real.pi / n)) |>.symm
  have h2 : Nat.card (CyclicPointGroup n) = n := CyclicPointGroup.card n
  rw [h1, Nat.card_zpowers] at h2
  exact h2

-- CyclicPointGroup n consists of rotations (elements in SO(2))
private lemma CyclicPointGroup_subset_SO2' (n : ℕ) [NeZero n] :
    (CyclicPointGroup n : Set OrthogonalGroup2) ⊆ SpecialOrthogonalGroup2 := by
  intro x hx
  simp only [SetLike.mem_coe, CyclicPointGroup, SpecialOrthogonalGroup2] at *
  have h_gen_in_SO2 : rotationMatrix' (2 * Real.pi / n) ∈ SpecialOrthogonalGroup2 := by
    simp only [SpecialOrthogonalGroup2, Subgroup.mem_mk]
    exact rotationMatrix_det _
  have h_sub : Subgroup.closure {rotationMatrix' (2 * Real.pi / n)} ≤ SpecialOrthogonalGroup2 := by
    rw [Subgroup.closure_le]
    simp only [Set.singleton_subset_iff]
    exact h_gen_in_SO2
  exact h_sub hx

/-- The cyclic point groups that are crystallographic: C₁, C₂, C₃, C₄, C₆. -/
lemma cyclic_crystallographic (n : ℕ) [NeZero n] :
    IsCrystallographicPointGroup (CyclicPointGroup n) ↔ n ∈ ({1, 2, 3, 4, 6} : Set ℕ) := by
  sorry

/-- The dihedral point groups that are crystallographic: D₁, D₂, D₃, D₄, D₆. -/
lemma dihedral_crystallographic (n : ℕ) [NeZero n] :
    IsCrystallographicPointGroup (DihedralPointGroup n) ↔ n ∈ ({1, 2, 3, 4, 6} : Set ℕ) := by
  sorry

/-! ### Cyclic group infrastructure for classification -/

-- Helper lemma: cyclic groups of same cardinality are isomorphic
private lemma cyclic_mulEquiv_of_card_eq {G H : Type*} [Group G] [Group H]
    [hG : IsCyclic G] [hH : IsCyclic H]
    (hcard : Nat.card G = Nat.card H) : Nonempty (G ≃* H) := by
  have e1 : Multiplicative (ZMod (Nat.card G)) ≃* G := zmodCyclicMulEquiv hG
  have e2 : Multiplicative (ZMod (Nat.card H)) ≃* H := zmodCyclicMulEquiv hH
  rw [hcard] at e1
  exact ⟨e1.symm.trans e2⟩

-- CyclicPointGroup n is cyclic
instance isCyclic_cyclicPointGroup (n : ℕ) [NeZero n] : IsCyclic (CyclicPointGroup n) := by
  rw [isCyclic_iff_exists_zpowers_eq_top]
  use ⟨rotationMatrix' (2 * Real.pi / n), Subgroup.subset_closure rfl⟩
  ext ⟨x, hx⟩
  simp only [Subgroup.mem_top, iff_true]
  have hCn : CyclicPointGroup n = Subgroup.zpowers (rotationMatrix' (2 * Real.pi / n)) := by
    unfold CyclicPointGroup; exact (Subgroup.zpowers_eq_closure _).symm
  rw [hCn] at hx
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx
  rw [Subgroup.mem_zpowers_iff]
  use k; apply Subtype.ext; simp only [Subgroup.coe_zpow]; exact hk

-- For a finite cyclic subgroup H ⊆ SO(2)
private lemma finite_cyclic_SO2_mulEquiv (H : Subgroup OrthogonalGroup2)
    (hH_finite : Finite H) (_ : ∀ A ∈ H, A ∈ SpecialOrthogonalGroup2)
    (hH_cyclic : IsCyclic H) :
    ∃ n : ℕ, ∃ _ : NeZero n, Nonempty (H ≃* CyclicPointGroup n) := by
  haveI : Fintype H := Fintype.ofFinite H
  let n := Nat.card H
  have hn_pos : 0 < n := Nat.card_pos
  haveI hn : NeZero n := ⟨ne_of_gt hn_pos⟩
  use n, hn
  have hH_card : Nat.card H = n := rfl
  have hCn_card : Nat.card (CyclicPointGroup n) = n := CyclicPointGroup.card n
  exact cyclic_mulEquiv_of_card_eq (hH_card.trans hCn_card.symm)

/-- There are exactly 10 crystallographic point groups.

They are: C₁, C₂, C₃, C₄, C₆, D₁, D₂, D₃, D₄, D₆

blueprint: cor:crystallographic_enumeration -/
theorem crystallographic_point_groups (H : Subgroup OrthogonalGroup2)
    (hH : IsCrystallographicPointGroup H) :
    (∃ n : ℕ, ∃ _ : NeZero n,
      n ∈ ({1, 2, 3, 4, 6} : Set ℕ) ∧ Nonempty (H ≃* CyclicPointGroup n)) ∨
    (∃ n : ℕ, ∃ _ : NeZero n,
      n ∈ ({1, 2, 3, 4, 6} : Set ℕ) ∧ Nonempty (H ≃* DihedralPointGroup n)) := by
  obtain ⟨hFin, hCryst⟩ := hH
  -- By finite subgroup classification, H ≃* Cm or Dm for some m
  rcases finite_subgroup_O2_classification H hFin with
    ⟨m, hm_nz, ⟨iso_Cm⟩⟩ | ⟨m, hm_nz, ⟨iso_Dm⟩⟩
  · -- Case: H ≃* Cm
    left
    use m, hm_nz
    constructor
    · -- Show m ∈ {1,2,3,4,6}
      -- The generator of Cm corresponds to some g ∈ H with orderOf g = m
      -- Since all elements of Cm are rotations, g ∈ SO(2)
      -- The crystallographic condition gives: ∃ n ∈ {1,2,3,4,6}, g^n = 1
      -- This means m | n, so m ∈ {1,2,3,4,6}

      -- Get generator of H from the isomorphism
      let gen_Cm : CyclicPointGroup m :=
        ⟨rotationMatrix' (2 * Real.pi / m), Subgroup.subset_closure rfl⟩
      let gen_H := iso_Cm.symm gen_Cm
      -- gen_H has order m in H
      have hgen_ord : orderOf gen_H = m := by
        have hord_outer : orderOf (rotationMatrix' (2 * Real.pi / m)) = m :=
          orderOf_rotationMatrix'_generator' m
        have hord_Cm : orderOf gen_Cm = m := by
          -- gen_Cm is the canonical generator in CyclicPointGroup m
          -- Its order equals m
          -- The generator has order m in O(2), and its order in the subgroup is the same
          have hinj : Function.Injective (Subgroup.subtype (CyclicPointGroup m)) :=
            Subtype.val_injective
          have heq := orderOf_injective (Subgroup.subtype (CyclicPointGroup m)) hinj gen_Cm
          simp only [Subgroup.coe_subtype] at heq
          rw [← heq]
          exact hord_outer
        rw [← hord_Cm]
        exact MulEquiv.orderOf_eq iso_Cm.symm gen_Cm
      -- gen_H.val ∈ SO(2) (since gen_Cm is a rotation)
      have hgen_SO2 : (gen_H : OrthogonalGroup2) ∈ SpecialOrthogonalGroup2 := by
        have hCm_SO2 := CyclicPointGroup_subset_SO2' m
        -- gen_H corresponds to a rotation, so it's in SO(2)
        -- The underlying element is iso_Cm.symm gen_Cm, which is a rotation
        -- For now, we use sorry since this requires detailed analysis of the isomorphism
        sorry
      -- Apply crystallographic condition
      obtain ⟨n, hn_set, hn_pow⟩ := hCryst (gen_H : OrthogonalGroup2) gen_H.prop hgen_SO2
      -- orderOf gen_H | n
      have hm_dvd_n : m ∣ n := by
        rw [← hgen_ord]
        have hpow : gen_H ^ n = 1 := by
          apply Subtype.ext
          exact hn_pow
        exact orderOf_dvd_of_pow_eq_one hpow
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn_set ⊢
      -- m divides some n ∈ {1,2,3,4,6}, so m ∈ {1,2,3,4,6}
      -- This follows from divisibility analysis
      have hm_pos : 0 < m := NeZero.pos m
      rcases hn_set with rfl | rfl | rfl | rfl | rfl
      · -- n = 1: m | 1 implies m = 1
        left; exact Nat.eq_one_of_dvd_one hm_dvd_n
      · -- n = 2: m | 2 implies m ∈ {1, 2}
        have hle := Nat.le_of_dvd (by omega) hm_dvd_n
        omega
      · -- n = 3: m | 3 implies m ∈ {1, 3}
        have hle := Nat.le_of_dvd (by omega) hm_dvd_n
        have hdvd3 : m = 1 ∨ m = 3 := by
          have h1 : 1 ≤ m := by omega
          have h2 : m ≤ 3 := hle
          rcases m with _ | _ | _ | _ <;> simp_all
        rcases hdvd3 with rfl | rfl <;> simp
      · -- n = 4: m | 4 implies m ∈ {1, 2, 4}
        have hle := Nat.le_of_dvd (by omega) hm_dvd_n
        have hdvd4 : m = 1 ∨ m = 2 ∨ m = 4 := by
          have h1 : 1 ≤ m := by omega
          have h3 : m ≤ 4 := hle
          have h4 : 4 % m = 0 := Nat.mod_eq_zero_of_dvd hm_dvd_n
          match m with
          | 1 => left; rfl
          | 2 => right; left; rfl
          | 3 => simp_all
          | 4 => right; right; rfl
          | n + 5 => omega
        rcases hdvd4 with rfl | rfl | rfl <;> simp
      · -- n = 6: m | 6 implies m ∈ {1, 2, 3, 6}
        -- Divisors of 6 are {1, 2, 3, 6}, all in our allowed set
        have hle := Nat.le_of_dvd (by omega) hm_dvd_n
        have hdvd6 : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 6 := by
          -- m | 6 and m > 0 implies m ∈ {1, 2, 3, 6}
          sorry
        rcases hdvd6 with rfl | rfl | rfl | rfl <;> simp
    · exact ⟨iso_Cm⟩
  · -- Case: H ≃* Dm
    right
    use m, hm_nz
    constructor
    · -- Show m ∈ {1,2,3,4,6}
      -- The rotation subgroup of Dm is Cm
      -- Get the generator R_{2π/m} in Dm, which corresponds to some rotation in H
      let gen_Dm : DihedralPointGroup m :=
        ⟨rotationMatrix' (2 * Real.pi / m),
         Subgroup.subset_closure (Set.mem_insert _ _)⟩
      let gen_H := iso_Dm.symm gen_Dm
      -- gen_H has order m in H
      have hgen_ord : orderOf gen_H = m := by
        have hord_outer : orderOf (rotationMatrix' (2 * Real.pi / m)) = m :=
          orderOf_rotationMatrix'_generator' m
        have hord_Dm : orderOf gen_Dm = m := by
          have hinj : Function.Injective (Subgroup.subtype (DihedralPointGroup m)) :=
            Subtype.val_injective
          have heq := orderOf_injective (Subgroup.subtype (DihedralPointGroup m)) hinj gen_Dm
          simp only [Subgroup.coe_subtype] at heq
          rw [← heq]
          exact hord_outer
        rw [← hord_Dm]
        exact MulEquiv.orderOf_eq iso_Dm.symm gen_Dm
      -- gen_H.val ∈ SO(2) (since gen_Dm is a rotation)
      have hgen_SO2 : (gen_H : OrthogonalGroup2) ∈ SpecialOrthogonalGroup2 := by
        -- The generator is a rotation, hence in SO(2)
        sorry
      -- Apply crystallographic condition
      obtain ⟨n, hn_set, hn_pow⟩ := hCryst (gen_H : OrthogonalGroup2) gen_H.prop hgen_SO2
      have hm_dvd_n : m ∣ n := by
        rw [← hgen_ord]
        have hpow : gen_H ^ n = 1 := by
          apply Subtype.ext
          exact hn_pow
        exact orderOf_dvd_of_pow_eq_one hpow
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn_set ⊢
      -- m divides some n ∈ {1,2,3,4,6}, so m ∈ {1,2,3,4,6}
      have hm_pos : 0 < m := NeZero.pos m
      rcases hn_set with rfl | rfl | rfl | rfl | rfl
      · -- n = 1: m | 1 implies m = 1
        left; exact Nat.eq_one_of_dvd_one hm_dvd_n
      · -- n = 2: m | 2 implies m ∈ {1, 2}
        have hle := Nat.le_of_dvd (by omega) hm_dvd_n
        omega
      · -- n = 3: m | 3 implies m ∈ {1, 3}
        have hdvd3 : m = 1 ∨ m = 3 := by
          -- m | 3 and m > 0 implies m ∈ {1, 3}
          sorry
        rcases hdvd3 with rfl | rfl <;> simp
      · -- n = 4: m | 4 implies m ∈ {1, 2, 4}
        have hdvd4 : m = 1 ∨ m = 2 ∨ m = 4 := by
          -- m | 4 and m > 0 implies m ∈ {1, 2, 4}
          sorry
        rcases hdvd4 with rfl | rfl | rfl <;> simp
      · -- n = 6: m | 6 implies m ∈ {1, 2, 3, 6}
        have hdvd6 : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 6 := by
          -- m | 6 and m > 0 implies m ∈ {1, 2, 3, 6}
          sorry
        rcases hdvd6 with rfl | rfl | rfl | rfl <;> simp
    · exact ⟨iso_Dm⟩

/-- The 10 crystallographic point groups as an inductive type. -/
inductive CrystallographicPointGroupType
  | C1 | C2 | C3 | C4 | C6
  | D1 | D2 | D3 | D4 | D6
  deriving DecidableEq, Repr

/-- Which point groups are compatible with which Bravais lattice types.

| Lattice Type      | Compatible Point Groups          |
|-------------------|----------------------------------|
| Oblique           | C₁, C₂                           |
| Rectangular       | C₁, C₂, D₁, D₂                   |
| Centered Rect     | C₁, C₂, D₁, D₂                   |
| Square            | C₁, C₂, C₄, D₁, D₂, D₄           |
| Hexagonal         | C₁, C₂, C₃, C₆, D₁, D₂, D₃, D₆   |

blueprint: lem:compatible_point_groups -/
lemma compatible_point_groups :
    -- Oblique lattices only support C₁ and C₂
    (∀ Λ : Lattice2, IsObliqueLattice Λ →
      (latticeSymmetryGroup Λ) ≤ CyclicPointGroup 2) ∧
    -- Square lattices support up to D₄
    (∀ Λ : Lattice2, IsSquareLattice Λ →
      ∃ n : ℕ, ∃ _ : NeZero n, n ∈ ({1, 2, 4} : Set ℕ) ∧
        (Nonempty ((latticeSymmetryGroup Λ) ≃* CyclicPointGroup n) ∨
        Nonempty ((latticeSymmetryGroup Λ) ≃* DihedralPointGroup n))) ∧
    -- Hexagonal lattices support up to D₆
    (∀ Λ : Lattice2, IsHexagonalLattice Λ →
      ∃ n : ℕ, ∃ _ : NeZero n, n ∈ ({1, 2, 3, 6} : Set ℕ) ∧
        (Nonempty ((latticeSymmetryGroup Λ) ≃* CyclicPointGroup n) ∨
        Nonempty ((latticeSymmetryGroup Λ) ≃* DihedralPointGroup n))) := by
  refine ⟨?oblique, ?square, ?hexagonal⟩
  case oblique =>
    intro Λ hΛ
    -- An oblique lattice has symmetry group C₂ by definition
    obtain ⟨eC2⟩ := hΛ
    -- Sym(Λ) ≃* C₂, so Sym(Λ) ≤ C₂
    -- This requires showing that the isomorphism maps into C₂ ⊆ O(2)
    -- The proof involves showing each element A ∈ Sym(Λ) corresponds to an element of C₂
    intro A hA
    -- The isomorphism sends A to some element of C₂
    -- We need to show A is actually in C₂ as a subgroup of O(2)
    -- This is a subtle point: we have an abstract isomorphism, not a concrete embedding
    -- For now, we use sorry as this requires infrastructure about isomorphisms of concrete subgroups
    sorry
  case square =>
    intro Λ hΛ
    -- A square lattice has symmetry group D₄ by definition
    obtain ⟨_, _, _, ⟨eD4⟩⟩ := hΛ
    refine ⟨4, ⟨by norm_num⟩, ?_, ?_⟩
    · simp
    · right; exact ⟨eD4⟩
  case hexagonal =>
    intro Λ hΛ
    -- A hexagonal lattice has symmetry group D₆ by definition
    obtain ⟨_, _, _, ⟨eD6⟩⟩ := hΛ
    refine ⟨6, ⟨by norm_num⟩, ?_, ?_⟩
    · simp
    · right; exact ⟨eD6⟩

/-- The lattice symmetry group is always crystallographic. -/
lemma latticeSymmetryGroup_isCrystallographic (Λ : Lattice2) :
    IsCrystallographicPointGroup (latticeSymmetryGroup Λ) := by
  constructor
  · exact latticeSymmetryGroup_finite Λ
  · intro A hA hASO
    obtain ⟨θ, hθ⟩ := SO2_eq_rotations A hASO
    have hApres : rotationMatrix' θ ∈ latticeSymmetryGroup Λ := by
      convert hA
      apply Subtype.ext
      exact hθ.symm
    obtain ⟨n, hn_set, hn_pow⟩ := crystallographic_restriction Λ θ hApres
    use n, hn_set
    have hAeq : A = rotationMatrix' θ := Subtype.ext hθ
    rw [hAeq]
    exact hn_pow

/-- Every crystallographic point group is realized by some lattice. -/
lemma crystallographic_realized (n : ℕ) [NeZero n] (hn : n ∈ ({1, 2, 3, 4, 6} : Set ℕ)) :
    ∃ Λ : Lattice2, Nonempty ((latticeSymmetryGroup Λ) ≃* DihedralPointGroup n) := by
  -- For each n ∈ {1,2,3,4,6}, we construct an explicit lattice with symmetry Dn
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl
  · -- n = 1: Any generic lattice has D₁ = {1, reflection}
    -- Use the standard rectangular lattice with unequal sides
    -- For simplicity, we use a generic oblique construction
    -- D₁ is realized by a lattice with one reflection symmetry
    -- This requires constructing an explicit lattice
    -- Since this is an existence proof, we defer to the lattice infrastructure
    -- A lattice Λ with basis (1,0) and (0.5, sqrt(3)/2) has D₃ symmetry
    -- A rectangular lattice with (1,0) and (0,2) has D₂ symmetry
    -- For D₁, we need a lattice with exactly one reflection
    -- This corresponds to a centered rectangular lattice in the limit
    -- For the proof, we note that D₁ ≅ D₂ restricted to one reflection
    -- Actually, for any n, we can realize Dn, so we construct explicitly

    -- We use the fact that rectangular lattices exist and have D₂ symmetry
    -- D₁ is a subgroup of D₂, so if we can realize D₂, we can realize D₁
    -- But the statement asks for the symmetry group to BE isomorphic to Dn

    -- For a formal proof, we need to construct explicit lattices
    -- This requires significant lattice construction infrastructure
    -- For now, we provide the proof structure

    -- The standard approach: construct a lattice with basis vectors
    -- that realize the desired symmetry
    sorry
  · -- n = 2: Rectangular lattice has D₂ symmetry
    sorry
  · -- n = 3: Hexagonal lattice can have D₃ symmetry
    sorry
  · -- n = 4: Square lattice has D₄ symmetry
    sorry
  · -- n = 6: Standard hexagonal lattice has D₆ symmetry
    sorry

end WallpaperGroups.Crystallographic
