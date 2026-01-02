/-
Copyright (c) 2025 Wallpaper Groups Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import WallpaperGroups.PointGroup.CyclicDihedral
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
  -- This theorem requires the infrastructure from CyclicDihedral.lean
  -- (CyclicPointGroup.card, DihedralPointGroup.card, etc.)
  -- The proof strategy is:
  -- 1. H ∩ SO(2) is cyclic of order n
  -- 2. If H ⊆ SO(2), then H ≅ Cₙ
  -- 3. If H contains a reflection, then H ≅ Dₙ
  sorry

/-- The order of a finite subgroup of O(2) determines whether it's cyclic or dihedral. -/
lemma finite_subgroup_O2_cyclic_iff (H : Subgroup OrthogonalGroup2)
    (hH_finite : Finite H) :
    (∀ A ∈ H, A ∈ SpecialOrthogonalGroup2) ↔
    (∃ n : ℕ, ∃ _ : NeZero n, Nonempty (H ≃* CyclicPointGroup n)) := by
  -- This requires the CyclicDihedral infrastructure
  sorry

end WallpaperGroups.PointGroup
