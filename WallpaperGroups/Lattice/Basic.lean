/-
Copyright (c) 2025 Wallpaper Groups Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import WallpaperGroups.Euclidean.Plane

/-!
# Rank-2 Lattices in the Euclidean Plane

This file defines rank-2 lattices in R^2 and their basic properties.

## Main definitions

* `Lattice2` - A rank-2 lattice in the Euclidean plane
* `latticeBasis` - A basis (a, b) for a lattice L = Za + Zb
* `latticeFundamentalDomain` - The fundamental domain for a lattice

## Main results

* `Lattice2.discrete` - Every lattice is discrete
* `Lattice2.cocompact` - The quotient R^2/L is compact (a torus)
-/

namespace WallpaperGroups.Lattice

open WallpaperGroups.Euclidean

/-- A rank-2 lattice in the Euclidean plane.

A lattice L in R^2 is a discrete subgroup of rank 2, meaning L = Za + Zb
for some linearly independent vectors a, b.

blueprint: def:lattice -/
structure Lattice2 where
  /-- The underlying additive subgroup of R^2. -/
  carrier : AddSubgroup EuclideanPlane
  /-- The lattice has rank 2 (spans R^2). -/
  rank_eq_two : ∃ (a b : EuclideanPlane), LinearIndependent ℝ ![a, b] ∧
    carrier = AddSubgroup.closure {a, b}
  /-- The lattice is discrete. -/
  discrete : ∀ x ∈ carrier, x ≠ 0 → ∃ ε > 0, ∀ y ∈ carrier, y ≠ x → ε ≤ ‖y - x‖

instance : SetLike Lattice2 EuclideanPlane where
  coe Λ := Λ.carrier
  coe_injective' := by
    intro Λ₁ Λ₂ h
    have hc : Λ₁.carrier = Λ₂.carrier := SetLike.coe_injective h
    cases Λ₁; cases Λ₂
    simp only at hc
    subst hc
    rfl

-- Note: SetLike already provides a Membership instance, so we don't need to define one

/-- A basis for a lattice consists of two linearly independent vectors
that generate the lattice.

blueprint: def:lattice_basis -/
structure LatticeBasis (Λ : Lattice2) where
  /-- First basis vector. -/
  a : EuclideanPlane
  /-- Second basis vector. -/
  b : EuclideanPlane
  /-- The vectors are linearly independent. -/
  linearIndependent : LinearIndependent ℝ ![a, b]
  /-- The vectors generate the lattice. -/
  generates : Λ.carrier = AddSubgroup.closure {a, b}

/-- Every lattice has a basis. -/
lemma Lattice2.exists_basis (Λ : Lattice2) : Nonempty (LatticeBasis Λ) := by
  obtain ⟨a, b, hind, hgen⟩ := Λ.rank_eq_two
  exact ⟨⟨a, b, hind, hgen⟩⟩

/-- Construct a Mathlib Basis from a LatticeBasis. -/
noncomputable def LatticeBasis.toBasis {Λ : Lattice2} (B : LatticeBasis Λ) :
    Module.Basis (Fin 2) ℝ EuclideanPlane := by
  have hcard : Fintype.card (Fin 2) = Module.finrank ℝ EuclideanPlane := by
    simp only [finrank_euclideanSpace, Fintype.card_fin]
  exact basisOfLinearIndependentOfCardEqFinrank B.linearIndependent hcard

/-- Helper: Set.range of the basis equals {B.a, B.b}. -/
lemma LatticeBasis.range_toBasis {Λ : Lattice2} (B : LatticeBasis Λ) :
    Set.range B.toBasis = {B.a, B.b} := by
  ext x
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff,
             LatticeBasis.toBasis, basisOfLinearIndependentOfCardEqFinrank,
             Module.Basis.mk_apply]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i
    · left; simp [Matrix.cons_val_zero]
    · right; simp [Matrix.cons_val_one]
  · rintro (rfl | rfl)
    · use 0; simp [Matrix.cons_val_zero]
    · use 1; simp [Matrix.cons_val_one]

/-- The carrier equals the Z-span of the basis vectors. -/
lemma Lattice2.carrier_eq_span {Λ : Lattice2} (B : LatticeBasis Λ) :
    Λ.carrier = (Submodule.span ℤ (Set.range B.toBasis)).toAddSubgroup := by
  rw [B.generates, B.range_toBasis, ← Submodule.span_int_eq_addSubgroupClosure]

/-- Get DiscreteTopology on the carrier via Mathlib's instance for Z-lattices. -/
noncomputable instance Lattice2.instDiscreteTopology (Λ : Lattice2) :
    DiscreteTopology Λ.carrier := by
  classical
  obtain ⟨B⟩ := Λ.exists_basis
  have heq : Λ.carrier = (Submodule.span ℤ (Set.range B.toBasis)).toAddSubgroup :=
    Λ.carrier_eq_span B
  rw [heq]
  infer_instance

/-- In a discrete subtype of a metric space, points are isolated. -/
lemma discrete_subtype_isolated {X : Type*} [MetricSpace X] {S : Set X}
    [DiscreteTopology S] (x : S) : ∃ ε > 0, ∀ y : S, y ≠ x → ε ≤ dist x y := by
  have hopen : IsOpen ({x} : Set S) := isOpen_discrete {x}
  rw [Metric.isOpen_iff] at hopen
  obtain ⟨ε, hε_pos, hε_ball⟩ := hopen x rfl
  use ε, hε_pos
  intro y hy
  by_contra hlt
  push_neg at hlt
  have hy_ball : y ∈ Metric.ball x ε := by rwa [Metric.mem_ball, dist_comm]
  have hyx := hε_ball hy_ball
  rw [Set.mem_singleton_iff] at hyx
  exact hy hyx

/-- The fundamental domain of a lattice with basis (a, b).

F = {sa + tb | 0 <= s < 1, 0 <= t < 1}

blueprint: def:fundamental_domain -/
def latticeFundamentalDomain (Λ : Lattice2) (B : LatticeBasis Λ) : Set EuclideanPlane :=
  {v | ∃ (s t : ℝ), 0 ≤ s ∧ s < 1 ∧ 0 ≤ t ∧ t < 1 ∧ v = s • B.a + t • B.b}

/-- Every lattice is discrete (has the discrete topology).

blueprint: lem:lattice_discrete -/
lemma Lattice2.isDiscrete (Λ : Lattice2) :
    ∀ x ∈ Λ.carrier, ∃ ε > 0, ∀ y ∈ Λ.carrier, y ≠ x → ε ≤ ‖y - x‖ := by
  intro x hx
  by_cases h : x = 0
  · subst h
    haveI : DiscreteTopology Λ.carrier := Λ.instDiscreteTopology
    have hdisc := discrete_subtype_isolated (⟨0, Λ.carrier.zero_mem⟩ : Λ.carrier)
    obtain ⟨ε, hε_pos, hε_sep⟩ := hdisc
    use ε, hε_pos
    intro y hy hy_ne
    simp only [sub_zero]
    specialize hε_sep ⟨y, hy⟩ (by simp [hy_ne])
    rw [Subtype.dist_eq, dist_eq_norm] at hε_sep
    simp only [zero_sub, norm_neg] at hε_sep
    exact hε_sep
  · exact Λ.discrete x hx h

/-- Lattice membership can be characterized using a basis. -/
lemma Lattice2.mem_iff_integer_coords (Λ : Lattice2) (B : LatticeBasis Λ)
    (v : EuclideanPlane) : v ∈ Λ ↔ ∃ (m n : ℤ), v = m • B.a + n • B.b := by
  change v ∈ Λ.carrier ↔ _
  rw [B.generates]
  rw [AddSubgroup.mem_closure_pair]
  constructor
  · rintro ⟨m, n, h⟩
    exact ⟨m, n, h.symm⟩
  · rintro ⟨m, n, h⟩
    exact ⟨m, n, h.symm⟩

/-- The parallelepiped spanned by a basis is compact. -/
lemma parallelepiped_isCompact (b : Module.Basis (Fin 2) ℝ EuclideanPlane) :
    IsCompact (parallelepiped b) :=
  b.parallelepiped.isCompact

/-- The image of parallelepiped under the quotient map is the whole quotient. -/
lemma quotient_mk_parallelepiped_surj (b : Module.Basis (Fin 2) ℝ EuclideanPlane) :
    Set.range (fun x : parallelepiped b =>
      QuotientAddGroup.mk (s := (Submodule.span ℤ (Set.range b)).toAddSubgroup) x.val) =
    Set.univ := by
  ext q
  simp only [Set.mem_range, Set.mem_univ, iff_true]
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
  use ⟨ZSpan.fract b x, ZSpan.fundamentalDomain_subset_parallelepiped b
        (ZSpan.fract_mem_fundamentalDomain b x)⟩
  rw [QuotientAddGroup.eq]
  simp only [ZSpan.fract, neg_sub, sub_add_cancel]
  exact (ZSpan.floor b x).2

/-- Helper for compact range: the range of a continuous function from a compact subtype
is compact. -/
lemma isCompact_range_of_isCompact_subtype {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {s : Set X} (hs : IsCompact s) (f : s → Y) (hf : Continuous f) :
    IsCompact (Set.range f) := by
  haveI : CompactSpace s := isCompact_iff_compactSpace.mp hs
  rw [← Set.image_univ]
  exact IsCompact.image isCompact_univ hf

/-- The quotient R^2/L is compact (homeomorphic to a torus).

blueprint: lem:lattice_cocompact -/
lemma Lattice2.quotient_compact (Λ : Lattice2) :
    CompactSpace (EuclideanPlane ⧸ Λ.carrier) := by
  obtain ⟨B⟩ := Λ.exists_basis
  have hcarrier : Λ.carrier = (Submodule.span ℤ (Set.range B.toBasis)).toAddSubgroup :=
    Λ.carrier_eq_span B
  rw [← isCompact_univ_iff, hcarrier, ← quotient_mk_parallelepiped_surj B.toBasis]
  exact isCompact_range_of_isCompact_subtype (parallelepiped_isCompact B.toBasis) _
    (QuotientAddGroup.continuous_mk.comp continuous_subtype_val)

/-- The lattice is closed under addition. -/
lemma Lattice2.add_mem (Λ : Lattice2) {v w : EuclideanPlane} (hv : v ∈ Λ) (hw : w ∈ Λ) :
    v + w ∈ Λ :=
  Λ.carrier.add_mem hv hw

/-- The lattice is closed under negation. -/
lemma Lattice2.neg_mem (Λ : Lattice2) {v : EuclideanPlane} (hv : v ∈ Λ) : -v ∈ Λ :=
  Λ.carrier.neg_mem hv

/-- The zero vector is in every lattice. -/
lemma Lattice2.zero_mem (Λ : Lattice2) : (0 : EuclideanPlane) ∈ Λ :=
  Λ.carrier.zero_mem

end WallpaperGroups.Lattice
