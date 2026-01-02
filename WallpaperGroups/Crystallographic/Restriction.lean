/-
Copyright (c) 2025 Wallpaper Groups Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import WallpaperGroups.Lattice.Symmetry
import WallpaperGroups.Euclidean.OrthogonalGroup
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex

/-!
# The Crystallographic Restriction Theorem

This file proves the crystallographic restriction theorem: if a rotation
preserves a 2D lattice, its order must be 1, 2, 3, 4, or 6.

## Main results

* `rotationMatrix_trace` - tr(R_θ) = 2cos(θ)
* `crystallographic_restriction` - Lattice-preserving rotations have order ∈ {1,2,3,4,6}

## Proof idea

If R_θ preserves a lattice Λ with basis (a,b), its matrix representation in that
basis has integer entries. The trace 2cos(θ) must be an integer, so
2cos(θ) ∈ {-2, -1, 0, 1, 2}, giving θ ∈ {0, ±π/3, ±π/2, ±2π/3, π}.

blueprint: thm:crystallographic_restriction
-/

namespace WallpaperGroups.Crystallographic

open WallpaperGroups.Euclidean
open WallpaperGroups.Lattice
open Matrix

/-- The trace of a rotation matrix is 2cos(θ).

blueprint: lem:rotation_trace -/
lemma rotationMatrix_trace (θ : ℝ) :
    trace (rotationMatrix θ) = 2 * Real.cos θ := by
  rw [trace_fin_two]
  simp only [rotationMatrix, of_apply, cons_val', empty_val', cons_val_fin_one,
             cons_val_zero, cons_val_one]
  ring

/-- Trace is preserved by similarity (already in Mathlib as Matrix.trace_conj).

blueprint: lem:trace_invariant -/
lemma trace_invariant {n : Type*} [DecidableEq n] [Fintype n]
    (A P : Matrix n n ℝ) (hP : IsUnit P) :
    trace (P * A * P⁻¹) = trace A :=
  Matrix.trace_conj hP A

/-- If M is an integer matrix, its trace is an integer.

blueprint: lem:integer_matrix_trace -/
lemma integer_matrix_trace (M : Matrix (Fin 2) (Fin 2) ℤ) :
    ∃ k : ℤ, (M.map (↑· : ℤ → ℝ)).trace = k := by
  use M 0 0 + M 1 1
  rw [trace_fin_two]
  simp only [map_apply, Int.cast_add]

/-- Integer values of 2cos(θ) and corresponding rotation orders.

| 2cos(θ) |  θ       | order |
|---------|----------|-------|
|  2      | 0        | 1     |
|  1      | π/3      | 6     |
|  0      | π/2      | 4     |
| -1      | 2π/3     | 3     |
| -2      | π        | 2     |
-/
lemma rotation_order_from_trace (θ : ℝ) (h : 2 * Real.cos θ = 2) :
    rotationMatrix θ = 1 := by
  have hcos : Real.cos θ = 1 := by linarith
  have hsin : Real.sin θ = 0 := by
    have h1 := Real.cos_sq_add_sin_sq θ
    rw [hcos] at h1
    nlinarith [sq_nonneg (Real.sin θ)]
  ext i j
  simp only [rotationMatrix, of_apply, cons_val', empty_val', cons_val_fin_one, one_apply]
  fin_cases i <;> fin_cases j <;> simp [hcos, hsin]

/-- The allowed rotation angles in the crystallographic restriction. -/
def crystallographicAngles : Set ℝ :=
  {0, Real.pi / 3, 2 * Real.pi / 3, Real.pi, 4 * Real.pi / 3, 5 * Real.pi / 3,
   Real.pi / 2, 3 * Real.pi / 2}

/-- Helper: Integer in range [-2, 2] -/
lemma int_in_range_two (k : ℤ) (h_le : (k : ℝ) ≤ 2) (h_ge : -2 ≤ (k : ℝ)) :
    k ∈ ({-2, -1, 0, 1, 2} : Set ℤ) := by
  have hk_le : k ≤ 2 := by
    have : (k : ℝ) ≤ (2 : ℤ) := by simpa using h_le
    exact Int.cast_le.mp this
  have hk_ge : -2 ≤ k := by
    have : ((-2 : ℤ) : ℝ) ≤ k := by simpa using h_ge
    exact Int.cast_le.mp this
  interval_cases k <;> simp

/-- Helper: 2cos(θ) is between -2 and 2. -/
lemma two_cos_bounded (θ : ℝ) : -2 ≤ 2 * Real.cos θ ∧ 2 * Real.cos θ ≤ 2 := by
  have h := Real.cos_le_one θ
  have h' := Real.neg_one_le_cos θ
  constructor <;> linarith

/-- The change of basis matrix from standard basis to a lattice basis.
P has columns B.a and B.b, so P maps standard basis to lattice basis. -/
noncomputable def basisChangeMatrix (B : LatticeBasis Λ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![B.a 0, B.b 0; B.a 1, B.b 1]

/-- The change of basis matrix is invertible since the lattice vectors are linearly independent. -/
lemma basisChangeMatrix_isUnit (B : LatticeBasis Λ) : IsUnit (basisChangeMatrix B) := by
  rw [isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  simp only [basisChangeMatrix, det_fin_two_of]
  -- Need: B.a 0 * B.b 1 - B.b 0 * B.a 1 ≠ 0
  -- By contradiction using linearIndependent_fin2
  have h_ind := B.linearIndependent
  rw [linearIndependent_fin2] at h_ind
  obtain ⟨hb_ne, ha_not_smul⟩ := h_ind
  -- hb_ne : ![B.a, B.b] 1 ≠ 0, i.e., B.b ≠ 0
  -- ha_not_smul : ∀ c, c • B.b ≠ B.a
  simp only [cons_val_one, cons_val_zero] at hb_ne ha_not_smul
  intro h_det
  -- det = 0 means B.a 0 * B.b 1 = B.b 0 * B.a 1
  have h_eq : B.a 0 * B.b 1 = B.b 0 * B.a 1 := by linarith
  -- Case on which coordinate of B.b is nonzero
  by_cases hb0 : B.b 0 = 0
  · -- B.b 0 = 0, so B.b 1 ≠ 0 (since B.b ≠ 0)
    have hb1 : B.b 1 ≠ 0 := by
      intro h
      apply hb_ne
      ext i
      fin_cases i <;> assumption
    -- From h_eq: B.a 0 * B.b 1 = 0, so B.a 0 = 0
    have ha0 : B.a 0 = 0 := by
      have h1 : B.a 0 * B.b 1 = 0 := by simp [h_eq, hb0]
      exact (mul_eq_zero.mp h1).resolve_right hb1
    -- Show B.a = (B.a 1 / B.b 1) • B.b contradicts ha_not_smul
    apply ha_not_smul (B.a.ofLp 1 / B.b.ofLp 1)
    apply (WithLp.ofLp_injective 2).eq_iff.mp
    ext i
    simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
    fin_cases i
    · simp only [Fin.mk_zero, hb0, mul_zero, ha0]
    · simp only [Fin.mk_one]
      field_simp
  · -- B.b 0 ≠ 0
    -- Show B.a = (B.a 0 / B.b 0) • B.b contradicts ha_not_smul
    apply ha_not_smul (B.a.ofLp 0 / B.b.ofLp 0)
    apply (WithLp.ofLp_injective 2).eq_iff.mp
    ext i
    simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
    fin_cases i
    · simp only [Fin.mk_zero]
      field_simp
    · simp only [Fin.mk_one]
      field_simp
      linarith

/-- Matrix-vector multiplication relation: P * e_i = column i of P. -/
lemma mulVec_std_basis (P : Matrix (Fin 2) (Fin 2) ℝ) (i : Fin 2) :
    P.mulVec (Pi.single i 1) = fun j => P j i := by
  ext j
  simp only [mulVec, dotProduct, Pi.single_apply, mul_boole, Finset.sum_ite_eq',
             Finset.mem_univ, ite_true]

/-- The action of R_θ on basis vectors determines the matrix representation.
If R_θ(a) = M₀₀ a + M₁₀ b and R_θ(b) = M₀₁ a + M₁₁ b, then R_θ = P M P⁻¹
where P has columns a, b. -/
lemma rotation_eq_conj (B : LatticeBasis Λ) (θ : ℝ) (M : Matrix (Fin 2) (Fin 2) ℤ)
    (hMa : (rotationMatrix' θ).1.mulVec B.a = (M 0 0 : ℝ) • B.a + (M 1 0 : ℝ) • B.b)
    (hMb : (rotationMatrix' θ).1.mulVec B.b = (M 0 1 : ℝ) • B.a + (M 1 1 : ℝ) • B.b) :
    rotationMatrix θ = basisChangeMatrix B * (M.map (↑· : ℤ → ℝ)) * (basisChangeMatrix B)⁻¹ := by
  have hP_unit := basisChangeMatrix_isUnit B
  letI : Invertible (basisChangeMatrix B) := hP_unit.invertible
  -- Key step: show R * P = P * M, then multiply by P⁻¹ on the right
  have h_eq : rotationMatrix θ * basisChangeMatrix B =
  basisChangeMatrix B * (M.map (↑· : ℤ → ℝ)) := by
    ext i j
    simp only [mul_apply, basisChangeMatrix, map_apply]
    rw [Fin.sum_univ_two, Fin.sum_univ_two]
    simp only [of_apply, cons_val_zero, cons_val_one]
    have ha_simp := fun k => congrFun hMa k
    have hb_simp := fun k => congrFun hMb k
    simp only [mulVec, dotProduct, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, Fin.sum_univ_two] at ha_simp hb_simp
    fin_cases i <;> fin_cases j <;>
      simp only [rotationMatrix, of_apply, cons_val_zero, cons_val_one, Fin.mk_zero, Fin.mk_one]
    -- Case i=0, j=0
    · have h0 := ha_simp 0
      simp only [rotationMatrix', rotationMatrix, of_apply, cons_val_zero, cons_val_one] at h0
      linarith
    -- Case i=0, j=1
    · have h0 := hb_simp 0
      simp only [rotationMatrix', rotationMatrix, of_apply, cons_val_zero, cons_val_one] at h0
      linarith
    -- Case i=1, j=0
    · have h1 := ha_simp 1
      simp only [rotationMatrix', rotationMatrix, of_apply, cons_val_zero, cons_val_one] at h1
      linarith
    -- Case i=1, j=1
    · have h1 := hb_simp 1
      simp only [rotationMatrix', rotationMatrix, of_apply, cons_val_zero, cons_val_one] at h1
      linarith
  -- From R * P = P * M, we get R = P * M * P⁻¹
  calc rotationMatrix θ
      = rotationMatrix θ * basisChangeMatrix B * (basisChangeMatrix B)⁻¹ := by
          rw [Matrix.mul_inv_cancel_right_of_invertible]
    _ = basisChangeMatrix B * (M.map (↑· : ℤ → ℝ)) * (basisChangeMatrix B)⁻¹ := by
          rw [h_eq]

/-- Helper: The trace of the rotation matrix equals the trace of its integer representation
in a lattice basis. -/
lemma rotation_trace_eq_integer_trace (Λ : Lattice2) (B : LatticeBasis Λ) (θ : ℝ)
    (hR : rotationMatrix' θ ∈ latticeSymmetryGroup Λ) :
    ∃ k : ℤ, 2 * Real.cos θ = k := by
  -- Since R_θ preserves the lattice, there's an integer matrix representation
  have h_pres : IsLatticePreserving Λ (rotationMatrix' θ) := hR.1
  rw [isLatticePreserving_iff_integerMatrix Λ B] at h_pres
  obtain ⟨M, hMa, hMb⟩ := h_pres
  -- The trace of R_θ is 2cos(θ)
  have h_tr_rot : trace (rotationMatrix θ) = 2 * Real.cos θ := rotationMatrix_trace θ
  use M 0 0 + M 1 1
  rw [← h_tr_rot]
  -- R_θ = P M P⁻¹ where P is the change of basis matrix
  have h_conj := rotation_eq_conj B θ M hMa hMb
  rw [h_conj]
  -- By similarity invariance, trace(P M P⁻¹) = trace(M)
  rw [trace_conj (basisChangeMatrix_isUnit B), trace_fin_two]
  simp only [map_apply, Int.cast_add]

/-- The crystallographic restriction in terms of 2cos(θ) being an integer. -/
lemma crystallographic_cosine (Λ : Lattice2) (θ : ℝ)
    (hR : rotationMatrix' θ ∈ latticeSymmetryGroup Λ) :
    2 * Real.cos θ ∈ ({-2, -1, 0, 1, 2} : Set ℝ) := by
  obtain ⟨B⟩ := Λ.exists_basis
  obtain ⟨k, hk⟩ := rotation_trace_eq_integer_trace Λ B θ hR
  have hbounded := two_cos_bounded θ
  have hk_bounded : k ∈ ({-2, -1, 0, 1, 2} : Set ℤ) := by
    apply int_in_range_two k <;> linarith
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hk_bounded ⊢
  rcases hk_bounded with rfl | rfl | rfl | rfl | rfl <;> simp [hk]

/-- Helper: rotation matrix power in terms of angle multiplication. -/
lemma rotationMatrix'_pow (θ : ℝ) (n : ℕ) :
    (rotationMatrix' θ)^n = rotationMatrix' (n * θ) := by
  induction n with
  | zero =>
    simp only [pow_zero, Nat.cast_zero, zero_mul]
    ext i j
    simp only [rotationMatrix', rotationMatrix, Submonoid.coe_one, one_apply,
               Real.cos_zero, Real.sin_zero, of_apply]
    fin_cases i <;> fin_cases j <;> simp
  | succ n ih =>
    rw [pow_succ, ih]
    ext i j
    simp only [rotationMatrix', rotationMatrix, Submonoid.mk_mul_mk,
               mul_apply, Fin.sum_univ_two, of_apply, cons_val_zero, cons_val_one]
    fin_cases i <;> fin_cases j <;>
      simp only [Fin.mk_zero, Fin.mk_one, cons_val_zero, cons_val_one, Nat.cast_succ]
    -- (0,0): cos(nθ)cos(θ) - sin(nθ)sin(θ) = cos((n+1)θ)
    · have h := Real.cos_add (n * θ) θ
      simp only [add_mul, one_mul] at h ⊢
      linarith
    -- (0,1): -cos(nθ)sin(θ) - sin(nθ)cos(θ) = -sin((n+1)θ)
    · have h := Real.sin_add (n * θ) θ
      simp only [add_mul, one_mul] at h ⊢
      linarith
    -- (1,0): sin(nθ)cos(θ) + cos(nθ)sin(θ) = sin((n+1)θ)
    · have h := Real.sin_add (n * θ) θ
      simp only [add_mul, one_mul] at h ⊢
      linarith
    -- (1,1): -sin(nθ)sin(θ) + cos(nθ)cos(θ) = cos((n+1)θ)
    · have h := Real.cos_add (n * θ) θ
      simp only [add_mul, one_mul] at h ⊢
      linarith

/-- Helper: rotation by 2π is identity. -/
lemma rotationMatrix'_two_pi : rotationMatrix' (2 * Real.pi) = 1 := by
  ext i j
  simp only [rotationMatrix', rotationMatrix, Real.cos_two_pi, Real.sin_two_pi,
             Submonoid.coe_one, one_apply, of_apply]
  fin_cases i <;> fin_cases j <;> simp

/-- Helper: rotation by π/2 has order 4. -/
lemma rotationMatrix'_pi_half_pow_four : (rotationMatrix' (Real.pi / 2))^4 = 1 := by
  rw [rotationMatrix'_pow]
  convert rotationMatrix'_two_pi using 2
  ring

/-- Helper: rotation by π has order 2. -/
lemma rotationMatrix'_pi_pow_two : (rotationMatrix' Real.pi)^2 = 1 := by
  rw [rotationMatrix'_pow]
  convert rotationMatrix'_two_pi using 2

/-- Helper: rotation by 2π/3 has order 3. -/
lemma rotationMatrix'_two_pi_third_pow_three : (rotationMatrix' (2 * Real.pi / 3))^3 = 1 := by
  rw [rotationMatrix'_pow]
  convert rotationMatrix'_two_pi using 2
  ring

/-- Helper: rotation by π/3 has order 6. -/
lemma rotationMatrix'_pi_third_pow_six : (rotationMatrix' (Real.pi / 3))^6 = 1 := by
  rw [rotationMatrix'_pow]
  convert rotationMatrix'_two_pi using 2
  ring

/-- Helper: if 2cos(θ) = 2, then θ = 2kπ for some integer k.
In particular, rotation by θ is the identity. -/
lemma cos_eq_one_of_two_cos_eq_two (θ : ℝ) (h : 2 * Real.cos θ = 2) :
    ∃ k : ℤ, θ = 2 * Real.pi * k := by
  have hcos : Real.cos θ = 1 := by linarith
  obtain ⟨k, hk⟩ := (Real.cos_eq_one_iff θ).mp hcos
  use k
  linarith

/-- Helper: if 2cos(θ) = -2, then θ = (2k+1)π for some integer k. -/
lemma cos_eq_neg_one_of_two_cos_eq_neg_two (θ : ℝ) (h : 2 * Real.cos θ = -2) :
    ∃ k : ℤ, θ = (2 * k + 1) * Real.pi := by
  have hcos : Real.cos θ = -1 := by linarith
  rw [Real.cos_eq_neg_one_iff] at hcos
  obtain ⟨k, hk⟩ := hcos
  use k
  linarith

/-- Helper: cos(4θ) in terms of cos(θ) -/
lemma cos_four_mul (θ : ℝ) : Real.cos (4 * θ) = 8 * Real.cos θ ^ 4 - 8 * Real.cos θ ^ 2 + 1 := by
  have h2 := Real.cos_two_mul θ
  have h4 := Real.cos_two_mul (2 * θ)
  have hsin2 := Real.sin_two_mul θ
  have hcs := Real.cos_sq_add_sin_sq θ
  calc Real.cos (4 * θ)
      = Real.cos (2 * (2 * θ)) := by ring_nf
    _ = 2 * Real.cos (2 * θ) ^ 2 - 1 := h4
    _ = 2 * (2 * Real.cos θ ^ 2 - 1) ^ 2 - 1 := by rw [h2]
    _ = 8 * Real.cos θ ^ 4 - 8 * Real.cos θ ^ 2 + 1 := by ring

/-- Helper: cos(6θ) in terms of cos(θ) -/
lemma cos_six_mul (θ : ℝ) :
    Real.cos (6 * θ) = 32 * Real.cos θ ^ 6 - 48 * Real.cos θ ^ 4 + 18 * Real.cos θ ^ 2 - 1 := by
  have h3 := Real.cos_three_mul θ
  have h6 := Real.cos_two_mul (3 * θ)
  have hsin3 := Real.sin_three_mul θ
  have hcs := Real.cos_sq_add_sin_sq θ
  -- cos(6θ) = 2cos²(3θ) - 1 = 2(4cos³θ - 3cosθ)² - 1
  calc Real.cos (6 * θ)
      = Real.cos (2 * (3 * θ)) := by ring_nf
    _ = 2 * Real.cos (3 * θ) ^ 2 - 1 := h6
    _ = 2 * (4 * Real.cos θ ^ 3 - 3 * Real.cos θ) ^ 2 - 1 := by rw [h3]
    _ = 32 * Real.cos θ ^ 6 - 48 * Real.cos θ ^ 4 + 18 * Real.cos θ ^ 2 - 1 := by ring

/-- Helper: sin(k * 2π) = 0 for integer k -/
lemma sin_int_mul_two_pi (k : ℤ) : Real.sin (k * (2 * Real.pi)) = 0 := by
  have h := Real.sin_add_int_mul_two_pi 0 k
  simp only [zero_add, Real.sin_zero] at h
  exact h

/-- The crystallographic restriction theorem.

If a rotation R_θ preserves a 2D lattice, then θ is a multiple of π/3 or π/2.
Equivalently, the order of R_θ (as an element of SO(2)) divides one of {1, 2, 3, 4, 6}.

blueprint: thm:crystallographic_restriction -/
theorem crystallographic_restriction (Λ : Lattice2) (θ : ℝ)
    (hR : rotationMatrix' θ ∈ latticeSymmetryGroup Λ) :
    ∃ n ∈ ({1, 2, 3, 4, 6} : Set ℕ), (rotationMatrix' θ)^n = 1 := by
  have h_cos := crystallographic_cosine Λ θ hR
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h_cos
  rcases h_cos with h_neg2 | h_neg1 | h_zero | h_one | h_two
  -- Case 2cos(θ) = -2: θ = (2k+1)π, order 2
  · have hcos : Real.cos θ = -1 := by linarith
    have hcos2 : Real.cos (2 * θ) = 1 := by
      have h := Real.cos_two_mul θ
      rw [hcos] at h
      linarith
    have hsin2 : Real.sin (2 * θ) = 0 := by
      have h1 := Real.cos_sq_add_sin_sq (2 * θ)
      rw [hcos2] at h1
      nlinarith [sq_nonneg (Real.sin (2 * θ))]
    use 2
    constructor
    · simp
    · rw [rotationMatrix'_pow]
      ext i j
      simp only [rotationMatrix', rotationMatrix, Submonoid.coe_one, one_apply, of_apply]
      fin_cases i <;> fin_cases j <;> simp [hcos2, hsin2]
  -- Case 2cos(θ) = -1: θ = ±2π/3 + 2kπ, order 3
  · use 3
    constructor
    · simp
    · have hcos : Real.cos θ = -1/2 := by linarith
      have hcos3 : Real.cos (3 * θ) = 1 := by
        have h := Real.cos_three_mul θ
        rw [hcos] at h
        linarith
      have hsin3 : Real.sin (3 * θ) = 0 := by
        have h1 := Real.cos_sq_add_sin_sq (3 * θ)
        rw [hcos3] at h1
        nlinarith [sq_nonneg (Real.sin (3 * θ))]
      rw [rotationMatrix'_pow]
      ext i j
      simp only [rotationMatrix', rotationMatrix, Submonoid.coe_one, one_apply, of_apply]
      fin_cases i <;> fin_cases j <;> simp [hcos3, hsin3]
  -- Case 2cos(θ) = 0: θ = ±π/2 + kπ, order 4
  · use 4
    constructor
    · simp
    · have hcos : Real.cos θ = 0 := by linarith
      have hcos4 : Real.cos (4 * θ) = 1 := by
        have h := cos_four_mul θ
        rw [hcos] at h
        linarith
      have hsin4 : Real.sin (4 * θ) = 0 := by
        have h1 := Real.cos_sq_add_sin_sq (4 * θ)
        rw [hcos4] at h1
        nlinarith [sq_nonneg (Real.sin (4 * θ))]
      rw [rotationMatrix'_pow]
      ext i j
      simp only [rotationMatrix', rotationMatrix, Submonoid.coe_one, one_apply, of_apply]
      fin_cases i <;> fin_cases j <;> simp [hcos4, hsin4]
  -- Case 2cos(θ) = 1: θ = ±π/3 + 2kπ, order 6
  · use 6
    constructor
    · simp
    · have hcos : Real.cos θ = 1/2 := by linarith
      have hcos6 : Real.cos (6 * θ) = 1 := by
        have h := cos_six_mul θ
        rw [hcos] at h
        linarith
      have hsin6 : Real.sin (6 * θ) = 0 := by
        have h1 := Real.cos_sq_add_sin_sq (6 * θ)
        rw [hcos6] at h1
        nlinarith [sq_nonneg (Real.sin (6 * θ))]
      rw [rotationMatrix'_pow]
      ext i j
      simp only [rotationMatrix', rotationMatrix, Submonoid.coe_one, one_apply, of_apply]
      fin_cases i <;> fin_cases j <;> simp [hcos6, hsin6]
  -- Case 2cos(θ) = 2: θ = 2kπ, order 1
  · use 1
    constructor
    · simp
    · rw [pow_one]
      obtain ⟨k, hk⟩ := cos_eq_one_of_two_cos_eq_two θ h_two
      rw [hk]
      ext i j
      simp only [rotationMatrix', rotationMatrix, Submonoid.coe_one, one_apply, of_apply]
      have hangle : 2 * Real.pi * ↑k = ↑k * (2 * Real.pi) := by ring
      have hcos : Real.cos (2 * Real.pi * k) = 1 := by rw [hangle]; exact Real.cos_int_mul_two_pi k
      have hsin : Real.sin (2 * Real.pi * k) = 0 := by rw [hangle]; exact sin_int_mul_two_pi k
      fin_cases i <;> fin_cases j <;> simp [hcos, hsin]

/-- Helper: cos(2π/3) = -1/2 -/
lemma cos_two_pi_div_three : Real.cos (2 * Real.pi / 3) = -1 / 2 := by
  have hangle : 2 * Real.pi / 3 = Real.pi - Real.pi / 3 := by ring
  rw [hangle, Real.cos_pi_sub, Real.cos_pi_div_three]
  ring

/-- A lattice-preserving rotation has angle in the allowed set (mod 2π). -/
lemma crystallographic_angle (Λ : Lattice2) (θ : ℝ)
    (hR : rotationMatrix' θ ∈ latticeSymmetryGroup Λ) :
    ∃ φ : ℝ, φ ∈ crystallographicAngles ∧ ∃ k : ℤ, θ = φ + 2 * Real.pi * k := by
  have h_cos := crystallographic_cosine Λ θ hR
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h_cos
  rcases h_cos with h_neg2 | h_neg1 | h_zero | h_one | h_two
  -- Case 2cos(θ) = -2: θ = π + 2kπ
  · use Real.pi
    refine ⟨?_, ?_⟩
    · simp only [crystallographicAngles, Set.mem_insert_iff, Set.mem_singleton_iff]
      right; right; right; left; trivial
    · have hcos : Real.cos θ = -1 := by linarith
      rw [Real.cos_eq_neg_one_iff] at hcos
      obtain ⟨m, hm⟩ := hcos
      use m
      linarith
  -- Case 2cos(θ) = -1: θ = 2π/3 + 2kπ or θ = 4π/3 + 2kπ
  · have hcos : Real.cos θ = -1/2 := by linarith
    rw [← cos_two_pi_div_three, Real.cos_eq_cos_iff] at hcos
    obtain ⟨k, hk | hk⟩ := hcos
    -- hk: θ = 2kπ + 2π/3, so θ = 2π/3 + 2(-k)π
    · use 2 * Real.pi / 3
      refine ⟨?_, -k, ?_⟩
      · simp only [crystallographicAngles, Set.mem_insert_iff, Set.mem_singleton_iff]
        right; right; left; trivial
      · simp only [Int.cast_neg]; linarith
    -- hk: θ = 2kπ - 2π/3, so θ = 4π/3 + 2(k-1)π
    · use 4 * Real.pi / 3
      refine ⟨?_, k - 1, ?_⟩
      · simp only [crystallographicAngles, Set.mem_insert_iff, Set.mem_singleton_iff]
        right; right; right; right; left; trivial
      · simp only [Int.cast_sub, Int.cast_one]; linarith
  -- Case 2cos(θ) = 0: θ = π/2 + 2kπ or θ = 3π/2 + 2kπ
  · have hcos : Real.cos θ = 0 := by linarith
    rw [← Real.cos_pi_div_two, Real.cos_eq_cos_iff] at hcos
    obtain ⟨k, hk | hk⟩ := hcos
    · use Real.pi / 2
      refine ⟨?_, -k, ?_⟩
      · simp only [crystallographicAngles, Set.mem_insert_iff, Set.mem_singleton_iff]
        right; right; right; right; right; right; left; trivial
      · simp only [Int.cast_neg]; linarith
    · use 3 * Real.pi / 2
      refine ⟨?_, k - 1, ?_⟩
      · simp only [crystallographicAngles, Set.mem_insert_iff, Set.mem_singleton_iff]
        right; right; right; right; right; right; right; trivial
      · simp only [Int.cast_sub, Int.cast_one]; linarith
  -- Case 2cos(θ) = 1: θ = π/3 + 2kπ or θ = 5π/3 + 2kπ
  · have hcos : Real.cos θ = 1/2 := by linarith
    have h_ref : Real.cos (Real.pi / 3) = 1 / 2 := Real.cos_pi_div_three
    rw [← h_ref, Real.cos_eq_cos_iff] at hcos
    obtain ⟨k, hk | hk⟩ := hcos
    · use Real.pi / 3
      refine ⟨?_, -k, ?_⟩
      · simp only [crystallographicAngles, Set.mem_insert_iff, Set.mem_singleton_iff]
        right; left; trivial
      · simp only [Int.cast_neg]; linarith
    · use 5 * Real.pi / 3
      refine ⟨?_, k - 1, ?_⟩
      · simp only [crystallographicAngles, Set.mem_insert_iff, Set.mem_singleton_iff]
        right; right; right; right; right; left; trivial
      · simp only [Int.cast_sub, Int.cast_one]; linarith
  -- Case 2cos(θ) = 2: θ = 2kπ
  · use 0
    refine ⟨?_, ?_⟩
    · simp only [crystallographicAngles, Set.mem_insert_iff, Set.mem_singleton_iff]
      left; trivial
    · obtain ⟨k, hk⟩ := cos_eq_one_of_two_cos_eq_two θ h_two
      use k
      linarith

end WallpaperGroups.Crystallographic
