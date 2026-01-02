/-
Copyright (c) 2025 Wallpaper Groups Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import WallpaperGroups.PointGroup.DihedralPointGroup
import Mathlib.RingTheory.IntegralDomain
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.Complex.Circle

/-!
# Classification of Finite Subgroups of O(2)

This file proves that every finite subgroup of O(2) is either cyclic (Cₙ)
or dihedral (Dₙ).

## Main results

* `finite_subgroup_SO2_isCyclic` - Every finite subgroup of SO(2) is cyclic
* `finite_subgroup_O2_classification` - Every finite H ⊂ O(2) is Cₙ or Dₙ

blueprint: thm:finite_O2_classification
-/

namespace WallpaperGroups.PointGroup

open WallpaperGroups.Euclidean

/-- Embed SO(2) into the complex unit circle via rotation matrices.
    A rotation by θ maps to e^{iθ} = cos θ + i sin θ. -/
noncomputable def SO2ToCircle : SpecialOrthogonalGroup2 →* Circle where
  toFun := fun A => by
    -- A rotation matrix has form [[cos θ, -sin θ], [sin θ, cos θ]]
    -- We extract cos θ = A.1.1 0 0 and sin θ = A.1.1 1 0
    let c := A.1.1 0 0  -- cos θ
    let s := A.1.1 1 0  -- sin θ
    -- Need to show c^2 + s^2 = 1
    have h_ortho : Matrix.transpose (A.1.1) * A.1.1 = 1 := by
      have := A.1.2
      rw [Matrix.mem_orthogonalGroup_iff'] at this
      exact this
    have h00 : (Matrix.transpose (A.1.1) * A.1.1) 0 0 = 1 := by rw [h_ortho]; rfl
    simp only [Matrix.transpose_apply, Matrix.mul_apply, Fin.sum_univ_two] at h00
    have h_norm : c ^ 2 + s ^ 2 = 1 := by
      simp only [sq]
      exact h00
    have h_norm_eq : ‖(⟨c, s⟩ : ℂ)‖ = 1 := by
      have h2 : ‖(⟨c, s⟩ : ℂ)‖^2 = 1 := by
        rw [← Complex.normSq_eq_norm_sq]
        simp only [Complex.normSq_mk]
        linarith
      nlinarith [sq_nonneg ‖(⟨c, s⟩ : ℂ)‖, norm_nonneg (⟨c, s⟩ : ℂ)]
    have hmem : (⟨c, s⟩ : ℂ) ∈ Submonoid.unitSphere ℂ := by
      rw [← mem_sphere_zero_iff_norm] at h_norm_eq
      rw [← Submonoid.coe_unitSphere] at h_norm_eq
      exact h_norm_eq
    exact ⟨⟨c, s⟩, hmem⟩
  map_one' := by
    simp only
    apply Subtype.ext
    simp only [Circle.coe_one]
    simp only [Complex.ext_iff, Complex.one_re, Complex.one_im]
    exact ⟨rfl, rfl⟩
  map_mul' := by
    intro a b
    apply Subtype.ext
    simp only [Circle.coe_mul]
    -- Need to show that the map respects multiplication
    -- (cos θ₁ + i sin θ₁)(cos θ₂ + i sin θ₂) = cos(θ₁+θ₂) + i sin(θ₁+θ₂)
    -- This follows from angle addition formulas
    simp only [Complex.ext_iff]
    constructor
    · simp only [Complex.mul_re]
      -- Need: a00 * b00 - a10 * b10 = (ab)00
      -- From matrix multiplication: (a*b)00 = a00*b00 + a01*b10
      -- For rotation matrices: a01 = -a10, so (a*b)00 = a00*b00 - a10*b10
      have ha : a.1.1 0 1 = -(a.1.1 1 0) := by
        obtain ⟨θ, hθ⟩ := SO2_eq_rotations a.1 a.2
        simp only [hθ, rotationMatrix]
        simp
      have hb : b.1.1 0 1 = -(b.1.1 1 0) := by
        obtain ⟨θ, hθ⟩ := SO2_eq_rotations b.1 b.2
        simp only [hθ, rotationMatrix]
        simp
      have hab : (a * b).1.1 0 0 = a.1.1 0 0 * b.1.1 0 0 + a.1.1 0 1 * b.1.1 1 0 := by
        have : (a * b).1.1 = a.1.1 * b.1.1 := rfl
        rw [this, Matrix.mul_apply, Fin.sum_univ_two]
      rw [ha] at hab
      linarith [hab]
    · simp only [Complex.mul_im]
      -- Need: a10 * b00 + a00 * b10 = (ab)10
      have hab : (a * b).1.1 1 0 = a.1.1 1 0 * b.1.1 0 0 + a.1.1 1 1 * b.1.1 1 0 := by
        have : (a * b).1.1 = a.1.1 * b.1.1 := rfl
        rw [this, Matrix.mul_apply, Fin.sum_univ_two]
      have ha : a.1.1 1 1 = a.1.1 0 0 := by
        obtain ⟨θ, hθ⟩ := SO2_eq_rotations a.1 a.2
        simp only [hθ, rotationMatrix]
        simp
      rw [ha] at hab
      linarith [hab]

/-- The homomorphism from SO(2) to Circle is injective. -/
lemma SO2ToCircle_injective : Function.Injective SO2ToCircle := by
  intro a b hab
  have h : (SO2ToCircle a : ℂ) = (SO2ToCircle b : ℂ) := by
    rw [hab]
  apply Subtype.ext
  apply Subtype.ext
  -- From h: (a00, a10) = (b00, b10) as complex numbers
  have h_re : a.1.1 0 0 = b.1.1 0 0 := by
    have := congr_arg Complex.re h
    simp only [SO2ToCircle, MonoidHom.coe_mk, OneHom.coe_mk] at this
    exact this
  have h_im : a.1.1 1 0 = b.1.1 1 0 := by
    have := congr_arg Complex.im h
    simp only [SO2ToCircle, MonoidHom.coe_mk, OneHom.coe_mk] at this
    exact this
  -- A rotation matrix is determined by its first column
  obtain ⟨θa, hθa⟩ := SO2_eq_rotations a.1 a.2
  obtain ⟨θb, hθb⟩ := SO2_eq_rotations b.1 b.2
  rw [hθa, hθb]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.mk_zero, Fin.mk_one, rotationMatrix, Matrix.of_apply, Matrix.cons_val',
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val_zero, Matrix.cons_val_one]
  · -- (0,0): cos θa = cos θb
    have ha00 : a.1.1 0 0 = Real.cos θa := by simp [hθa, rotationMatrix]
    have hb00 : b.1.1 0 0 = Real.cos θb := by simp [hθb, rotationMatrix]
    linarith [h_re]
  · -- (0,1): -sin θa = -sin θb
    have ha10 : a.1.1 1 0 = Real.sin θa := by simp [hθa, rotationMatrix]
    have hb10 : b.1.1 1 0 = Real.sin θb := by simp [hθb, rotationMatrix]
    linarith [h_im]
  · -- (1,0): sin θa = sin θb
    have ha10 : a.1.1 1 0 = Real.sin θa := by simp [hθa, rotationMatrix]
    have hb10 : b.1.1 1 0 = Real.sin θb := by simp [hθb, rotationMatrix]
    linarith [h_im]
  · -- (1,1): cos θa = cos θb
    have ha00 : a.1.1 0 0 = Real.cos θa := by simp [hθa, rotationMatrix]
    have hb00 : b.1.1 0 0 = Real.cos θb := by simp [hθb, rotationMatrix]
    linarith [h_re]

/-- Composition of SO2ToCircle with Circle → ℂ gives an injective map to ℂ. -/
noncomputable def SO2ToComplex : SpecialOrthogonalGroup2 →* ℂ :=
  Circle.coeHom.comp SO2ToCircle

lemma SO2ToComplex_injective : Function.Injective SO2ToComplex := by
  intro a b h
  apply SO2ToCircle_injective
  apply Subtype.ext
  exact h

/-- Every finite subgroup of SO(2) (as a subgroup of SpecialOrthogonalGroup2) is cyclic. -/
private lemma finite_subgroup_SO2_isCyclic_aux (H : Subgroup SpecialOrthogonalGroup2)
    (hH_finite : Finite H) : IsCyclic H := by
  haveI : Finite H := hH_finite
  exact isCyclic_of_subgroup_isDomain (SO2ToComplex.comp H.subtype)
    (SO2ToComplex_injective.comp Subtype.val_injective)

/-- Every finite subgroup of SO(2) is cyclic.

Since SO(2) ≅ S¹ ≅ ℝ/ℤ, finite subgroups correspond to cyclic subgroups ⟨1/n⟩ ⊂ ℝ/ℤ.

blueprint: lem:finite_SO2_cyclic -/
lemma finite_subgroup_SO2_isCyclic (H : Subgroup OrthogonalGroup2)
    (hH_finite : Finite H)
    (hH_SO2 : ∀ A ∈ H, A ∈ SpecialOrthogonalGroup2) :
    IsCyclic H := by
  -- Build an isomorphism from H to a subgroup of SO(2)
  let H' : Subgroup SpecialOrthogonalGroup2 := {
    carrier := {x | x.1 ∈ H}
    mul_mem' := fun {a} {b} ha hb => H.mul_mem ha hb
    one_mem' := H.one_mem
    inv_mem' := fun {a} ha => H.inv_mem ha
  }
  -- Define an equivalence between H and H'
  let φ : H ≃ H' := {
    toFun := fun x => ⟨⟨x.1, hH_SO2 x.1 x.2⟩, x.2⟩
    invFun := fun x => ⟨x.1.1, x.2⟩
    left_inv := fun x => by simp
    right_inv := fun x => by simp
  }
  haveI : Finite H' := Finite.of_equiv H φ
  have hcyc : IsCyclic H' := finite_subgroup_SO2_isCyclic_aux H' inferInstance
  -- Now transfer the cyclic structure from H' to H via the isomorphism
  let ψ : H ≃* H' := {
    toEquiv := φ
    map_mul' := fun x y => rfl
  }
  exact isCyclic_of_surjective ψ.symm ψ.symm.surjective

/-- If H ⊂ O(2) is finite and H ∩ SO(2) is trivial, then H has at most 2 elements. -/
lemma finite_subgroup_O2_trivial_intersection (H : Subgroup OrthogonalGroup2)
    (hH_finite : Finite H)
    (hH_trivial : ∀ A ∈ H, A ∈ SpecialOrthogonalGroup2 → A = 1) :
    Nat.card H ≤ 2 := by
  haveI : Fintype H := Fintype.ofFinite H
  -- Every non-identity element is a reflection (det = -1)
  have h_refl : ∀ A : H, (A : OrthogonalGroup2) ≠ 1 → (A : OrthogonalGroup2).1.det = -1 := by
    intro A hne
    rcases O2_eq_rotations_or_reflections (A : OrthogonalGroup2) with ⟨θ, hrot⟩ | ⟨θ, hrefl⟩
    · -- A is a rotation, so A ∈ SO(2)
      exfalso
      have hdet : (A : OrthogonalGroup2).1.det = 1 := by rw [hrot]; exact rotationMatrix_det θ
      have hSO2 : (A : OrthogonalGroup2) ∈ SpecialOrthogonalGroup2 := hdet
      have := hH_trivial (A : OrthogonalGroup2) A.2 hSO2
      exact hne this
    · rw [hrefl]; exact reflectionMatrix_det θ
  -- Reflections are their own inverses
  have h_invol : ∀ A : H, (A : OrthogonalGroup2) ≠ 1 →
      (A : OrthogonalGroup2) * (A : OrthogonalGroup2) = 1 := by
    intro A hne
    rcases O2_eq_rotations_or_reflections (A : OrthogonalGroup2) with ⟨θ, hrot⟩ | ⟨θ, hrefl⟩
    · exfalso
      have hdet : (A : OrthogonalGroup2).1.det = 1 := by rw [hrot]; exact rotationMatrix_det θ
      exact hne (hH_trivial (A : OrthogonalGroup2) A.2 hdet)
    · apply Subtype.ext
      change (A : OrthogonalGroup2).1 * (A : OrthogonalGroup2).1 = 1
      rw [hrefl]
      exact reflectionMatrix_sq θ
  -- The product of two distinct reflections is a non-trivial rotation
  have h_prod_rot : ∀ A B : H, (A : OrthogonalGroup2) ≠ 1 → (B : OrthogonalGroup2) ≠ 1 → A ≠ B →
      ((A : OrthogonalGroup2) * (B : OrthogonalGroup2)).1.det = 1 := by
    intro A B hAne hBne hAB
    have hAdet := h_refl A hAne
    have hBdet := h_refl B hBne
    simp only [show ((A : OrthogonalGroup2) * (B : OrthogonalGroup2)).1 =
      (A : OrthogonalGroup2).1 * (B : OrthogonalGroup2).1 from rfl, Matrix.det_mul]
    rw [hAdet, hBdet]
    norm_num
  -- If there are more than 2 elements, we get a contradiction
  by_contra h_gt2
  push_neg at h_gt2
  have h_three : 2 < Nat.card H := h_gt2
  rw [Nat.card_eq_fintype_card] at h_three
  -- Get three distinct elements
  have h_exists3 : ∃ a b : H, a ≠ b ∧ (a : OrthogonalGroup2) ≠ 1 ∧ (b : OrthogonalGroup2) ≠ 1 := by
    -- With card ≥ 3, at least 2 elements are non-identity
    have h_card_ge3 : 3 ≤ Fintype.card H := h_three
    have h_one_unique : ∀ a b : H, (a : OrthogonalGroup2) =
    1 → (b : OrthogonalGroup2) = 1 → a = b := by
      intro a b ha hb
      apply Subtype.ext
      rw [ha, hb]
    -- Count non-identity elements
    let S := Finset.filter (fun x : H => (x : OrthogonalGroup2) ≠ 1) Finset.univ
    have hS_card : S.card ≥ 2 := by
      have hS_compl : (Finset.filter (fun x : H =>
       (x : OrthogonalGroup2) = 1) Finset.univ).card ≤ 1 := by
        by_cases h : ∃ a : H, (a : OrthogonalGroup2) = 1
        · obtain ⟨a, ha⟩ := h
          have : Finset.filter (fun x : H => (x : OrthogonalGroup2) = 1) Finset.univ = {a} := by
            ext x
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
            constructor
            · intro hx; exact Subtype.ext (hx.trans ha.symm)
            · intro hx; rw [hx]; exact ha
          rw [this]; simp
        · push_neg at h
          have : Finset.filter (fun x : H => (x : OrthogonalGroup2) = 1) Finset.univ = ∅ := by
            ext x
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
              iff_false]
            exact h x
          rw [this]; simp
      have key : S.card + (Finset.filter (fun x : H =>
       (x : OrthogonalGroup2) = 1) Finset.univ).card =
          Fintype.card H := by
        have hunion : S ∪ Finset.filter (fun x : H =>
         (x : OrthogonalGroup2) = 1) Finset.univ = Finset.univ := by
          ext x
          simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
          simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
          tauto
        let T := Finset.filter (fun x : H => (x : OrthogonalGroup2) = 1) Finset.univ
        have disj : Disjoint S T := by
          simp only [S, T, Finset.disjoint_filter]
          intro x _ hx
          exact hx
        have hunion' : S ∪ T = Finset.univ := hunion
        rw [← Finset.card_union_of_disjoint disj, hunion', Finset.card_univ]
      omega
    have h_one_lt : 1 < S.card := by omega
    rw [Finset.one_lt_card] at h_one_lt
    obtain ⟨a, ha_mem, b, hb_mem, hab⟩ := h_one_lt
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at ha_mem hb_mem
    exact ⟨a, b, hab, ha_mem, hb_mem⟩
  obtain ⟨a, b, hab, ha_ne1, hb_ne1⟩ := h_exists3
  -- a * b is a rotation, so a * b = 1 by hypothesis
  have hab_rot : ((a : OrthogonalGroup2) * (b : OrthogonalGroup2)).1.det =
   1 := h_prod_rot a b ha_ne1 hb_ne1 hab
  have hab_SO2 : (a : OrthogonalGroup2) * (b : OrthogonalGroup2) ∈
   SpecialOrthogonalGroup2 := hab_rot
  have hab_one : (a : OrthogonalGroup2) * (b : OrthogonalGroup2) = 1 :=
    hH_trivial ((a : OrthogonalGroup2) * (b : OrthogonalGroup2)) (H.mul_mem a.2 b.2) hab_SO2
  -- So b = a⁻¹ = a (since a² = 1)
  have ha_inv : (a : OrthogonalGroup2)⁻¹ = (a : OrthogonalGroup2) := by
    have h := h_invol a ha_ne1
    calc (a : OrthogonalGroup2)⁻¹ = (a : OrthogonalGroup2)⁻¹ * 1 := by group
      _ = (a : OrthogonalGroup2)⁻¹ * ((a : OrthogonalGroup2) * (a : OrthogonalGroup2)) := by rw [h]
      _ = ((a : OrthogonalGroup2)⁻¹ * (a : OrthogonalGroup2)) * (a : OrthogonalGroup2) := by group
      _ = 1 * (a : OrthogonalGroup2) := by simp
      _ = (a : OrthogonalGroup2) := by group
  have hb_eq_a : b = a := by
    have : (b : OrthogonalGroup2) = (a : OrthogonalGroup2)⁻¹ := by
      calc (b : OrthogonalGroup2) = 1 * (b : OrthogonalGroup2) := by group
        _ = ((a : OrthogonalGroup2)⁻¹ * (a : OrthogonalGroup2)) * (b : OrthogonalGroup2) := by simp
        _ = (a : OrthogonalGroup2)⁻¹ * ((a : OrthogonalGroup2) * (b : OrthogonalGroup2)) := by group
        _ = (a : OrthogonalGroup2)⁻¹ * 1 := by rw [hab_one]
        _ = (a : OrthogonalGroup2)⁻¹ := by group
    apply Subtype.ext
    rw [this, ha_inv]
  exact hab hb_eq_a.symm

/-- Every finite subgroup H ⊂ O(2) is isomorphic to either Cₙ or Dₙ for some n.

The proof proceeds by considering H ∩ SO(2):
- This is a finite subgroup of SO(2), hence cyclic of some order n
- If H = H ∩ SO(2), then H ≅ Cₙ
- Otherwise H contains a reflection, and H ≅ Dₙ

blueprint: thm:finite_O2_classification -/
theorem finite_subgroup_O2_classification (H : Subgroup OrthogonalGroup2)
    (hH_finite : Finite H) :
    (∃ n : ℕ, ∃ _ : NeZero n, Nonempty (H ≃* CyclicPointGroup n)) ∨
    (∃ n : ℕ, ∃ _ : NeZero n, Nonempty (H ≃* DihedralPointGroup n)) := by
  haveI : Fintype H := Fintype.ofFinite H
  haveI : Nonempty H := ⟨1⟩
  have hcard_pos : 0 < Nat.card H := Nat.card_pos
  -- Case split: either H ⊆ SO(2) or H contains a reflection
  by_cases hSO2 : ∀ A ∈ H, A ∈ SpecialOrthogonalGroup2
  · -- Case 1: H ⊆ SO(2), so H is cyclic
    left
    have hcyclic : IsCyclic H := finite_subgroup_SO2_isCyclic H hH_finite hSO2
    let n := Nat.card H
    have hn : NeZero n := ⟨Nat.pos_iff_ne_zero.mp hcard_pos⟩
    use n, hn
    -- CyclicPointGroup n is cyclic with card n
    have hcn_card : Nat.card (CyclicPointGroup n) = n := CyclicPointGroup.card n
    -- H is cyclic with card n, so H ≃* CyclicPointGroup n
    have hH_card_eq : Nat.card H = Nat.card (CyclicPointGroup n) := by rw [hcn_card]
    exact ⟨mulEquivOfCyclicCardEq hH_card_eq⟩
  · -- Case 2: H contains a reflection (element with det = -1)
    right
    push_neg at hSO2
    obtain ⟨S, hS_mem, hS_refl⟩ := hSO2
    -- S is a reflection (det = -1)
    have hS_det : S.1.det = -1 := by
      rcases O2_eq_rotations_or_reflections S with ⟨θ, hrot⟩ | ⟨θ, hrefl⟩
      · exfalso
        have : S ∈ SpecialOrthogonalGroup2 := by
          show S.1.det = 1
          rw [hrot]
          exact rotationMatrix_det θ
        exact hS_refl this
      · rw [hrefl]
        exact reflectionMatrix_det θ
    -- Define H' = H ∩ SO(2), the rotation subgroup
    let H' : Subgroup OrthogonalGroup2 := H ⊓ SpecialOrthogonalGroup2
    have hH'_le : H' ≤ H := inf_le_left
    have hH'_SO2 : ∀ A ∈ H', A ∈ SpecialOrthogonalGroup2 := fun A hA => (Subgroup.mem_inf.mp hA).2
    haveI hH'_finite : Finite H' := Finite.of_injective (Subgroup.inclusion hH'_le)
      (Subgroup.inclusion_injective hH'_le)
    have hH'_cyclic : IsCyclic H' := finite_subgroup_SO2_isCyclic H' hH'_finite hH'_SO2
    -- H' has index 2 in H (since S ∉ H' but S * H' ⊆ H)
    -- So |H| = 2 * |H'|
    have hindex : (H'.subgroupOf H).index = 2 := by
      -- Every element of H is either in H' (det = 1) or has det = -1
      have h_cosets : ∀ A ∈ H, A ∈ H' ∨ (A : OrthogonalGroup2).1.det = -1 := by
        intro A hA
        rcases O2_eq_rotations_or_reflections A with ⟨θ, hrot⟩ | ⟨θ, hrefl⟩
        · left
          rw [Subgroup.mem_inf]
          constructor
          · exact hA
          · show A.1.det = 1
            rw [hrot]
            exact rotationMatrix_det θ
        · right
          rw [hrefl]
          exact reflectionMatrix_det θ
      -- Need to show H'.subgroupOf H has index 2
      -- The quotient H / H' has exactly 2 cosets: H' and S * H'
      rw [Subgroup.index_eq_two_iff]
      use ⟨S, hS_mem⟩
      intro ⟨A, hA_mem⟩
      -- S ∉ H' (since S has det -1)
      have hS_not_in_H' : S ∉ H' := by
        intro hS_in'
        have := (Subgroup.mem_inf.mp hS_in').2
        exact hS_refl this
      rcases h_cosets A hA_mem with hA_H' | hA_det
      · -- A ∈ H' : A ∈ H'.subgroupOf H but A * S ∉ H'.subgroupOf H
        right
        constructor
        · -- ⟨A, hA_mem⟩ ∈ H'.subgroupOf H
          exact hA_H'
        · -- A * S ∉ H'.subgroupOf H
          intro hAS_in
          have hAS_in_H' : A * S ∈ H' := hAS_in
          have hAS_det : (A * S).1.det = -1 := by
            simp only [Submonoid.coe_mul, Matrix.det_mul]
            have hA_det1 := (Subgroup.mem_inf.mp hA_H').2
            rw [hA_det1, hS_det]
            norm_num
          have hAS_SO2 := (Subgroup.mem_inf.mp hAS_in_H').2
          have hAS_contra : (A * S).1.det = 1 := hAS_SO2
          rw [hAS_det] at hAS_contra
          norm_num at hAS_contra
      · -- A has det = -1: A ∉ H' but A * S ∈ H'
        left
        constructor
        · -- ⟨A, hA_mem⟩ * ⟨S, hS_mem⟩ ∈ H'.subgroupOf H
          -- A * S has det = 1, so A * S ∈ SO(2), and A * S ∈ H
          show A * S ∈ H'
          rw [Subgroup.mem_inf]
          constructor
          · exact H.mul_mem hA_mem hS_mem
          · show (A * S).1.det = 1
            simp only [Submonoid.coe_mul, Subgroup.coe_toSubmonoid, Matrix.det_mul]
            rw [hA_det, hS_det]
            norm_num
        · -- A ∉ H'
          intro hA_H'
          have hA_SO2 := (Subgroup.mem_inf.mp hA_H').2
          have hA_contra : A.1.det = 1 := hA_SO2
          rw [hA_det] at hA_contra
          norm_num at hA_contra
    -- Now |H| = 2 * |H'|
    have hcard_eq : Nat.card H = 2 * Nat.card H' := by
      have h' := @Subgroup.index_mul_card _ _ (H'.subgroupOf H)
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hH'_le).toEquiv] at h'
      rw [hindex] at h'
      omega
    -- |H'| = n for some n ≥ 1
    have hH'_card_pos : 0 < Nat.card H' := by
      haveI : Nonempty H' := ⟨1⟩
      exact Nat.card_pos
    let n := Nat.card H'
    have hn : NeZero n := ⟨Nat.pos_iff_ne_zero.mp hH'_card_pos⟩
    use n, hn
    -- |DihedralPointGroup n| = 2n = |H|
    have hH_card : Nat.card H = 2 * n := hcard_eq
    -- DihedralGroup n ≃* DihedralPointGroup n (already proved)
    obtain ⟨e_Dn⟩ := DihedralPointGroup.equivDihedralGroup n

    -- The key insight: both H and DihedralPointGroup n are dihedral groups of order 2n
    -- They both have presentation ⟨r, s | r^n = 1, s^2 = 1, srs = r⁻¹⟩
    -- Since DihedralGroup n has a universal property, we can construct the isomorphism

    -- Get a generator of H' (the cyclic rotation part)
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := H')
    have hg_order : orderOf g = n := by
      have h_top : Subgroup.zpowers g = ⊤ := by
        ext x
        simp only [Subgroup.mem_zpowers_iff, Subgroup.mem_top, iff_true]
        exact hg x
      rw [← Nat.card_zpowers g, h_top, Nat.card_eq_fintype_card, Fintype.card_coe,
          ← Nat.card_eq_fintype_card]

    -- The element S has order 2 in H
    let S' : H := ⟨S, hS_mem⟩
    have hS_order : orderOf S' = 2 := by
      apply orderOf_eq_prime
      · -- S'^2 = 1
        rcases O2_eq_rotations_or_reflections S with ⟨θ, hrot⟩ | ⟨θ, hrefl⟩
        · exfalso
          have : S ∈ SpecialOrthogonalGroup2 := by
            show S.1.det = 1; rw [hrot]; exact rotationMatrix_det θ
          exact hS_refl this
        · apply Subtype.ext
          show (S' ^ 2 : H).1 = 1
          simp only [sq, Subgroup.coe_mul]
          apply Subtype.ext
          rw [hrefl]
          exact reflectionMatrix_sq θ
      · intro hS1
        have : (S' : OrthogonalGroup2).1.det = (1 : H).1.1.det := by
          simp only [hS1, Subgroup.coe_one, OneMemClass.coe_one]
        simp only [Subgroup.coe_one, OneMemClass.coe_one, Matrix.det_one] at this
        rw [hS_det] at this
        norm_num at this

    -- The conjugation relation: S * g * S⁻¹ = g⁻¹ (in H)
    -- This is because S is a reflection and g is a rotation
    let g' : H := Subgroup.inclusion hH'_le g

    have hconj : S' * g' * S'⁻¹ = g'⁻¹ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      -- g is in H', so g is a rotation
      have hg_SO2 := hH'_SO2 g.1 g.2
      obtain ⟨θg, hθg⟩ := SO2_eq_rotations g.1 hg_SO2
      -- S is a reflection
      have hS_refl_form : ∃ θ, S.1 = reflectionMatrix θ := by
        rcases O2_eq_rotations_or_reflections S with ⟨θ, hrot⟩ | ⟨θ, hrefl⟩
        · exfalso
          have : S ∈ SpecialOrthogonalGroup2 := by
            show S.1.det = 1; rw [hrot]; exact rotationMatrix_det θ
          exact hS_refl this
        · exact ⟨θ, hrefl⟩
      obtain ⟨θs, hθs⟩ := hS_refl_form
      -- Compute S * R_θg * S⁻¹
      have hS_inv : S⁻¹ = S := by
        rw [inv_eq_iff_mul_eq_one]
        apply Subtype.ext
        rw [hθs]
        exact reflectionMatrix_sq θs
      rw [hS_inv]
      apply Subtype.ext
      simp only [Subgroup.inclusion_mk, Submonoid.coe_mul, Subgroup.coe_toSubmonoid]
      rw [hθg, hθs]
      -- S_θs * R_θg * S_θs = R_{-θg}
      rw [reflectionMatrix_mul_rotationMatrix, reflectionMatrix_mul]
      simp only [sub_sub_cancel]
      rw [show θs - (θs + θg) = -θg by ring]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp only [rotationMatrix, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons, Real.cos_neg, Real.sin_neg] <;> ring

    -- Key helper: g' has order n in H
    have hg'_order : orderOf g' = n := by
      have : orderOf g' = orderOf g := Subgroup.orderOf_coe (Subgroup.inclusion hH'_le g)
      rw [this, hg_order]

    -- Key helper: g'^n = 1
    have hg'_pow_n : g' ^ n = 1 := by
      rw [← hg'_order]
      exact pow_orderOf_eq_one g'

    -- Key helper: S'^2 = 1
    have hS'_sq : S' ^ 2 = 1 := by
      rw [← hS_order]
      exact pow_orderOf_eq_one S'

    -- Key helper: S'⁻¹ = S'
    have hS'_inv : S'⁻¹ = S' := by
      rw [inv_eq_iff_mul_eq_one, ← sq]
      exact hS'_sq

    -- Key helper: S' * g' * S' = g'⁻¹  (conjugation relation)
    have hconj' : S' * g' * S' = g'⁻¹ := by
      rw [mul_assoc, hS'_inv] at hconj
      exact hconj

    -- Key helper: g' * S' = S' * g'⁻¹
    have hgS : g' * S' = S' * g'⁻¹ := by
      calc g' * S' = g' * S' * (S' * S') := by rw [← sq, hS'_sq, mul_one]
        _ = g' * (S' * S') * S' := by group
        _ = g' * 1 * S' := by rw [← sq, hS'_sq]
        _ = S' * (S' * g' * S') := by group
        _ = S' * g'⁻¹ := by rw [hconj']

    -- Extended conjugation for powers
    have hconj_pow : ∀ k : ℕ, g' ^ k * S' = S' * g'⁻¹ ^ k := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ, mul_assoc, ih, ← mul_assoc, hgS, mul_assoc, ← pow_succ]

    -- Define the map φ : DihedralGroup n → H
    let φ : DihedralGroup n → H := fun x =>
      match x with
      | DihedralGroup.r i => g' ^ i.val
      | DihedralGroup.sr i => S' * g' ^ i.val

    -- φ is a group homomorphism
    have hφ_one : φ 1 = 1 := by
      simp only [DihedralGroup.one_def, φ, ZMod.val_zero, pow_zero]

    have hφ_mul : ∀ x y, φ (x * y) = φ x * φ y := by
      intro x y
      cases x with
      | r i =>
        cases y with
        | r j =>
          simp only [DihedralGroup.r_mul_r, φ]
          by_cases h : i.val + j.val < n
          · have hval : (i + j).val = i.val + j.val := ZMod.val_add_of_lt h
            rw [hval, pow_add]
          · have hval : (i + j).val = i.val + j.val - n := by
              have hi : i.val < n := ZMod.val_lt i
              have hj : j.val < n := ZMod.val_lt j
              have hsum : i.val + j.val < 2 * n := by omega
              have := ZMod.val_add i j
              rw [Nat.mod_eq_sub_mod (le_of_not_gt h)] at this
              have h2 : i.val + j.val - n < n := by omega
              rw [Nat.mod_eq_of_lt h2] at this
              exact this
            rw [hval]
            have hle : n ≤ i.val + j.val := le_of_not_gt h
            calc g' ^ (i.val + j.val - n)
                = g' ^ (i.val + j.val - n + n) := by rw [Nat.sub_add_cancel hle, pow_add,
                    pow_add, hg'_pow_n, mul_one]
                _ = g' ^ (i.val + j.val) := by rw [Nat.sub_add_cancel hle]
                _ = g' ^ i.val * g' ^ j.val := by rw [pow_add]
        | sr j =>
          simp only [DihedralGroup.r_mul_sr, φ]
          rw [← mul_assoc]
          have h1 : g' ^ i.val * S' = S' * g'⁻¹ ^ i.val := hconj_pow i.val
          rw [h1, mul_assoc]
          congr 1
          have hi : i.val < n := ZMod.val_lt i
          have hj : j.val < n := ZMod.val_lt j
          by_cases hle : i.val ≤ j.val
          · have hval : (j - i).val = j.val - i.val := ZMod.val_sub hle
            rw [hval]
            calc g'⁻¹ ^ i.val * g' ^ j.val
                = (g' ^ i.val)⁻¹ * g' ^ j.val := by rw [inv_pow]
                _ = g' ^ (j.val - i.val) := by
                    rw [← zpow_natCast, ← zpow_neg, ← zpow_natCast, ← zpow_add]
                    congr 1
                    have h2 : (j.val - i.val : ℤ) = (j.val : ℤ) - (i.val : ℤ) := Int.ofNat_sub hle
                    omega
          · push_neg at hle
            have hval : (j - i).val = j.val + n - i.val := by
              have hsum_lt : j.val + n - i.val < n := by omega
              rw [sub_eq_add_neg]
              have hival : (-i).val = if i = 0 then 0 else n - i.val := ZMod.neg_val i
              rw [ZMod.val_add, hival]
              split_ifs with hi0
              · simp only [hi0, ZMod.val_zero] at hle; omega
              · have hi_le : i.val ≤ n := le_of_lt hi
                rw [← Nat.add_sub_assoc hi_le]
                exact Nat.mod_eq_of_lt hsum_lt
            rw [hval]
            calc g'⁻¹ ^ i.val * g' ^ j.val
                = (g' ^ i.val)⁻¹ * g' ^ j.val := by rw [inv_pow]
                _ = g' ^ (j.val + n - i.val) := by
                    rw [← zpow_natCast g' (j.val + n - i.val)]
                    rw [← zpow_natCast, ← zpow_neg, ← zpow_natCast, ← zpow_add]
                    congr 1
                    have hle2 : i.val ≤ j.val + n := by omega
                    have hcast : ((j.val + n - i.val : ℕ) : ℤ) = (j.val : ℤ) + (n : ℤ) - (i.val : ℤ) := by
                      rw [Nat.cast_sub hle2]; push_cast; ring
                    rw [hcast]
                    have : (-(i.val : ℤ) + (j.val : ℤ)) = (j.val : ℤ) + (n : ℤ) - (i.val : ℤ) - n := by ring
                    rw [this, Int.sub_eq_add_neg, ← zpow_add, zpow_natCast, hg'_pow_n,
                        zpow_neg, zpow_natCast, inv_one, one_mul]
                    rfl
      | sr i =>
        cases y with
        | r j =>
          simp only [DihedralGroup.sr_mul_r, φ]
          rw [mul_assoc]
          congr 1
          by_cases h : i.val + j.val < n
          · have hval : (i + j).val = i.val + j.val := ZMod.val_add_of_lt h
            rw [hval, pow_add]
          · have hval : (i + j).val = i.val + j.val - n := by
              have hi : i.val < n := ZMod.val_lt i
              have hj : j.val < n := ZMod.val_lt j
              have hsum : i.val + j.val < 2 * n := by omega
              have := ZMod.val_add i j
              rw [Nat.mod_eq_sub_mod (le_of_not_gt h)] at this
              have h2 : i.val + j.val - n < n := by omega
              rw [Nat.mod_eq_of_lt h2] at this
              exact this
            rw [hval]
            have hle : n ≤ i.val + j.val := le_of_not_gt h
            calc g' ^ (i.val + j.val - n)
                = g' ^ (i.val + j.val - n + n) := by rw [Nat.sub_add_cancel hle, pow_add,
                    pow_add, hg'_pow_n, mul_one]
                _ = g' ^ (i.val + j.val) := by rw [Nat.sub_add_cancel hle]
                _ = g' ^ i.val * g' ^ j.val := by rw [pow_add]
        | sr j =>
          simp only [DihedralGroup.sr_mul_sr, φ]
          rw [mul_assoc, ← mul_assoc (g' ^ i.val) S' _]
          have h1 : g' ^ i.val * S' = S' * g'⁻¹ ^ i.val := hconj_pow i.val
          rw [h1, mul_assoc, mul_assoc, ← sq, hS'_sq, one_mul]
          have hi : i.val < n := ZMod.val_lt i
          have hj : j.val < n := ZMod.val_lt j
          by_cases hle : i.val ≤ j.val
          · have hval : (j - i).val = j.val - i.val := ZMod.val_sub hle
            rw [hval]
            calc g'⁻¹ ^ i.val * g' ^ j.val
                = (g' ^ i.val)⁻¹ * g' ^ j.val := by rw [inv_pow]
                _ = g' ^ (j.val - i.val) := by
                    rw [← zpow_natCast, ← zpow_neg, ← zpow_natCast, ← zpow_add]
                    congr 1
                    have h2 : (j.val - i.val : ℤ) = (j.val : ℤ) - (i.val : ℤ) := Int.ofNat_sub hle
                    omega
          · push_neg at hle
            have hval : (j - i).val = j.val + n - i.val := by
              have hsum_lt : j.val + n - i.val < n := by omega
              rw [sub_eq_add_neg]
              have hival : (-i).val = if i = 0 then 0 else n - i.val := ZMod.neg_val i
              rw [ZMod.val_add, hival]
              split_ifs with hi0
              · simp only [hi0, ZMod.val_zero] at hle; omega
              · have hi_le : i.val ≤ n := le_of_lt hi
                rw [← Nat.add_sub_assoc hi_le]
                exact Nat.mod_eq_of_lt hsum_lt
            rw [hval]
            calc g'⁻¹ ^ i.val * g' ^ j.val
                = (g' ^ i.val)⁻¹ * g' ^ j.val := by rw [inv_pow]
                _ = g' ^ (j.val + n - i.val) := by
                    rw [← zpow_natCast g' (j.val + n - i.val)]
                    rw [← zpow_natCast, ← zpow_neg, ← zpow_natCast, ← zpow_add]
                    congr 1
                    have hle2 : i.val ≤ j.val + n := by omega
                    have hcast : ((j.val + n - i.val : ℕ) : ℤ) = (j.val : ℤ) + (n : ℤ) - (i.val : ℤ) := by
                      rw [Nat.cast_sub hle2]; push_cast; ring
                    rw [hcast]
                    have : (-(i.val : ℤ) + (j.val : ℤ)) = (j.val : ℤ) + (n : ℤ) - (i.val : ℤ) - n := by ring
                    rw [this, Int.sub_eq_add_neg, ← zpow_add, zpow_natCast, hg'_pow_n,
                        zpow_neg, zpow_natCast, inv_one, one_mul]
                    rfl

    -- Build the homomorphism
    let ψ : DihedralGroup n →* H := ⟨⟨φ, hφ_one⟩, hφ_mul⟩

    -- ψ is injective
    have hψ_inj : Function.Injective ψ := by
      rw [← MonoidHom.ker_eq_bot_iff]
      rw [Subgroup.eq_bot_iff_forall]
      intro x hx
      rw [MonoidHom.mem_ker] at hx
      cases x with
      | r i =>
        simp only [ψ, φ, MonoidHom.coe_mk, OneHom.coe_mk] at hx
        have hi : g' ^ i.val = 1 := hx
        have hdiv : orderOf g' ∣ i.val := orderOf_dvd_of_pow_eq_one hi
        rw [hg'_order] at hdiv
        have hival : i.val < n := ZMod.val_lt i
        have hival_zero : i.val = 0 := by
          rcases Nat.eq_zero_or_pos i.val with h0 | hpos
          · exact h0
          · have := Nat.le_of_dvd hpos hdiv; omega
        have hi_zero : i = 0 := ZMod.val_eq_zero.mp hival_zero
        rw [hi_zero]; rfl
      | sr i =>
        simp only [ψ, φ, MonoidHom.coe_mk, OneHom.coe_mk] at hx
        have hS' : S' * g' ^ i.val = 1 := hx
        -- S' * g'^i = 1 implies contradiction since S' has det -1 and g'^i has det 1
        have hS'_det : (S' : OrthogonalGroup2).1.det = -1 := hS_det
        have hg'_det : ∀ k : ℕ, (g' ^ k : OrthogonalGroup2).1.det = 1 := by
          intro k
          induction k with
          | zero => simp [Matrix.det_one]
          | succ k ih =>
            simp only [pow_succ, Subgroup.coe_mul, Submonoid.coe_mul, Matrix.det_mul, ih]
            have hg_SO2 := hH'_SO2 g.1 g.2
            rw [hg_SO2]
            ring
        have h1_det : (1 : H).1.1.det = 1 := Matrix.det_one
        have hprod_det : (S' * g' ^ i.val : OrthogonalGroup2).1.det = 1 := by rw [hS']; exact h1_det
        simp only [Subgroup.coe_mul, Submonoid.coe_mul, Matrix.det_mul, hS'_det, hg'_det,
          mul_one] at hprod_det
        norm_num at hprod_det

    -- ψ is surjective (by cardinality)
    have hψ_surj : Function.Surjective ψ := by
      have hcard_D : Nat.card (DihedralGroup n) = 2 * n := DihedralGroup.nat_card
      have hcard_H' : Nat.card H = 2 * n := hH_card
      have hcard_eq : Nat.card (DihedralGroup n) = Nat.card H := by rw [hcard_D, hcard_H']
      exact Finite.surjective_of_injective hψ_inj (by rw [hcard_eq])

    -- Build the MulEquiv
    let e : DihedralGroup n ≃* H := MulEquiv.ofBijective ψ ⟨hψ_inj, hψ_surj⟩

    -- H ≃* DihedralGroup n ≃* DihedralPointGroup n
    exact ⟨e.symm.trans e_Dn.symm⟩

/-- The order of a finite subgroup of O(2) determines whether it's cyclic or dihedral. -/
lemma finite_subgroup_O2_cyclic_iff (H : Subgroup OrthogonalGroup2)
    (hH_finite : Finite H) :
    (∀ A ∈ H, A ∈ SpecialOrthogonalGroup2) ↔
    (∃ n : ℕ, ∃ _ : NeZero n, Nonempty (H ≃* CyclicPointGroup n)) := by
  -- This requires the CyclicDihedral infrastructure
  sorry

end WallpaperGroups.PointGroup
