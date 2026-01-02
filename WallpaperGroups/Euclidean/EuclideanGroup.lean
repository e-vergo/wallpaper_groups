/-
Copyright (c) 2025 Wallpaper Groups Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import WallpaperGroups.Euclidean.OrthogonalGroup

/-!
# The Euclidean Group E(2)

This file defines the Euclidean group E(2) as the semidirect product ℝ² ⋊ O(2),
along with the translation subgroup and glide reflections.

## Main definitions

* `EuclideanGroup2` - The Euclidean group E(2) = ℝ² ⋊ O(2)
* `translationSubgroup` - The normal subgroup of pure translations
* `IsGlideReflection` - Predicate for glide reflection elements

## Main results

* `EuclideanGroup2.mul_def` - Multiplication formula (v₁, A₁)(v₂, A₂) = (v₁ + A₁v₂, A₁A₂)
* `EuclideanGroup2.inv_def` - Inverse formula (v, A)⁻¹ = (-A⁻¹v, A⁻¹)
* `translationSubgroup_normal` - Translations form a normal subgroup
* `EuclideanGroup2.quotient_translations` - E(2)/T ≅ O(2)

## Implementation notes

The semidirect product `N ⋊[φ] G` in Mathlib requires both `N` and `G` to be multiplicative groups.
Since `EuclideanPlane = EuclideanSpace ℝ (Fin 2)` is an additive group, we use
`Multiplicative EuclideanPlane` as the normal subgroup. The action
`φ : O(2) →* MulAut (Multiplicative ℝ²)` is derived from the natural linear action of
orthogonal matrices on vectors.
-/

namespace WallpaperGroups.Euclidean

open Matrix

/-- Construct a linear equivalence from an orthogonal matrix acting on the Euclidean plane.

For A ∈ O(2), this gives the linear isomorphism v ↦ Av. -/
noncomputable def orthogonalToLinearEquiv (A : OrthogonalGroup2) :
    EuclideanPlane ≃ₗ[ℝ] EuclideanPlane :=
  LinearEquiv.ofLinear
    (Matrix.toEuclideanLin A.1)
    (Matrix.toEuclideanLin A⁻¹.1)
    (by
      ext v i
      simp only [LinearMap.coe_comp, LinearMap.id_coe, Function.comp_apply, id_eq]
      rw [Matrix.toEuclideanLin_apply, Matrix.toEuclideanLin_apply]
      rw [mulVec_mulVec]
      have h : A.1 * A⁻¹.1 = 1 := by
        have inv_eq : A⁻¹.1 = star A.1 := rfl
        simp only [inv_eq, star_eq_conjTranspose]
        rw [conjTranspose_eq_transpose_of_trivial]
        have h2 := A.property
        rw [mem_orthogonalGroup_iff] at h2
        exact h2
      rw [h, one_mulVec])
    (by
      ext v i
      simp only [LinearMap.coe_comp, LinearMap.id_coe, Function.comp_apply, id_eq]
      rw [Matrix.toEuclideanLin_apply, Matrix.toEuclideanLin_apply]
      rw [mulVec_mulVec]
      have h : A⁻¹.1 * A.1 = 1 := by
        have inv_eq : A⁻¹.1 = star A.1 := rfl
        simp only [inv_eq, star_eq_conjTranspose]
        rw [conjTranspose_eq_transpose_of_trivial]
        have := A.property
        rw [mem_orthogonalGroup_iff'] at this
        exact this
      rw [h, one_mulVec])

/-- Convert the linear equivalence from an orthogonal matrix to an additive automorphism. -/
noncomputable def orthogonalToAddAut (A : OrthogonalGroup2) : AddAut EuclideanPlane :=
  (orthogonalToLinearEquiv A).toAddEquiv

/-- Convert an orthogonal matrix to a multiplicative automorphism of the multiplicative
version of the Euclidean plane. This uses the equivalence
`MulAut (Multiplicative G) ≃* AddAut G`. -/
noncomputable def orthogonalToMulAut (A : OrthogonalGroup2) :
    MulAut (Multiplicative EuclideanPlane) :=
  (MulAutMultiplicative EuclideanPlane).symm (orthogonalToAddAut A)

/-- The action of O(2) on the multiplicative version of ℝ² as a group homomorphism.

This is the action used in the semidirect product structure of E(2). -/
noncomputable def orthogonalActionHom :
    OrthogonalGroup2 →* MulAut (Multiplicative EuclideanPlane) where
  toFun := orthogonalToMulAut
  map_one' := by
    ext v i
    simp only [orthogonalToMulAut, orthogonalToAddAut, orthogonalToLinearEquiv]
    simp only [MulAutMultiplicative, MulAut.one_apply, MulEquiv.symm_mk, MulEquiv.coe_mk,
               Equiv.symm_symm, AddEquiv.toMultiplicative, Equiv.coe_fn_mk]
    unfold AddMonoidHom.toMultiplicative
    simp only [Equiv.coe_fn_mk, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd,
               AddEquiv.coe_toAddMonoidHom, LinearEquiv.coe_toAddEquiv]
    change ((toEuclideanLin ↑(1 : OrthogonalGroup2)) (Multiplicative.toAdd v)).ofLp i =
           (Multiplicative.toAdd v).ofLp i
    rw [Matrix.toEuclideanLin_apply]
    have h : (1 : OrthogonalGroup2).1 = (1 : Matrix (Fin 2) (Fin 2) ℝ) := rfl
    simp only [h, one_mulVec]
  map_mul' := by
    intros A B
    ext v i
    simp only [orthogonalToMulAut, orthogonalToAddAut, orthogonalToLinearEquiv]
    simp only [MulAutMultiplicative, MulEquiv.symm_mk, MulEquiv.coe_mk, Equiv.symm_symm,
               AddEquiv.toMultiplicative, Equiv.coe_fn_mk, MulAut.mul_apply]
    unfold AddMonoidHom.toMultiplicative
    simp only [Equiv.coe_fn_mk, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd,
               AddEquiv.coe_toAddMonoidHom, LinearEquiv.coe_toAddEquiv]
    -- LHS: toEuclideanLin (A * B) (toAdd v)
    -- RHS: toEuclideanLin A (toEuclideanLin B (toAdd v))
    change ((toEuclideanLin (A * B).1) (Multiplicative.toAdd v)).ofLp i =
           ((toEuclideanLin A.1) ((toEuclideanLin B.1) (Multiplicative.toAdd v))).ofLp i
    rw [Matrix.toEuclideanLin_apply, Matrix.toEuclideanLin_apply, Matrix.toEuclideanLin_apply]
    -- Goal: (toLp 2 ((A*B) *ᵥ v)).ofLp i = (toLp 2 (A *ᵥ (toLp 2 (B *ᵥ v)).ofLp)).ofLp i
    -- Simplify: (A*B) *ᵥ v = A *ᵥ (B *ᵥ v) using mulVec_mulVec
    have hAB : (A * B).1 = A.1 * B.1 := rfl
    simp only [hAB, mulVec_mulVec]

/-- The Euclidean group E(2) is the semidirect product of the translation group ℝ²
and the orthogonal group O(2).

An element (v, A) represents the isometry x ↦ Ax + v.

We use `Multiplicative EuclideanPlane` because Mathlib's `SemidirectProduct` requires
multiplicative groups.

blueprint: def:euclidean_group -/
abbrev EuclideanGroup2 : Type :=
  (Multiplicative EuclideanPlane) ⋊[orthogonalActionHom] OrthogonalGroup2

/-- Helper to create an element of E(2) from a translation vector and orthogonal matrix. -/
def EuclideanGroup2.mk (v : EuclideanPlane) (A : OrthogonalGroup2) : EuclideanGroup2 :=
  SemidirectProduct.mk (Multiplicative.ofAdd v) A

/-- Extract the translation component from an element of E(2). -/
def EuclideanGroup2.translation (g : EuclideanGroup2) : EuclideanPlane :=
  Multiplicative.toAdd g.left

/-- Extract the orthogonal component from an element of E(2). -/
def EuclideanGroup2.orthogonal (g : EuclideanGroup2) : OrthogonalGroup2 :=
  g.right

/-- Multiplication in E(2).

(v₁, A₁) · (v₂, A₂) = (v₁ + A₁v₂, A₁A₂)

blueprint: lem:euclidean_mul -/
lemma EuclideanGroup2.mul_def (g₁ g₂ : EuclideanGroup2) :
    (g₁ * g₂).translation = g₁.translation + Matrix.toEuclideanLin g₁.right.1 g₂.translation ∧
    (g₁ * g₂).orthogonal = g₁.orthogonal * g₂.orthogonal := by
  constructor
  · simp only [translation, SemidirectProduct.mul_left]
    -- Goal: toAdd (g₁.left * (orthogonalActionHom g₁.right) g₂.left) =
    --       toAdd g₁.left + toEuclideanLin g₁.right.1 (toAdd g₂.left)
    -- First simplify the orthogonalActionHom application
    unfold orthogonalActionHom orthogonalToMulAut orthogonalToAddAut orthogonalToLinearEquiv
    simp only [MonoidHom.coe_mk, OneHom.coe_mk]
    unfold MulAutMultiplicative
    simp only [MulEquiv.symm_mk, MulEquiv.coe_mk, Equiv.symm_symm]
    simp only [AddEquiv.toMultiplicative, MulEquiv.coe_mk, Equiv.coe_fn_mk]
    unfold AddMonoidHom.toMultiplicative
    simp only [Equiv.coe_fn_mk, MonoidHom.coe_mk, OneHom.coe_mk]
    simp only [toAdd_mul, toAdd_ofAdd]
    simp only [AddEquiv.coe_toAddMonoidHom, LinearEquiv.coe_toAddEquiv]
    -- The coercion ↑(LinearEquiv.ofLinear f g ...) x = f x, which is definitionally equal
    congr 1
  · simp only [orthogonal, SemidirectProduct.mul_right]

/-- Inverse in E(2).

(v, A)⁻¹ = (-A⁻¹v, A⁻¹)

blueprint: lem:euclidean_inv -/
lemma EuclideanGroup2.inv_def (g : EuclideanGroup2) :
    g⁻¹.translation = -(Matrix.toEuclideanLin g.right⁻¹.1 g.translation) ∧
    g⁻¹.orthogonal = g.orthogonal⁻¹ := by
  constructor
  · simp only [translation, SemidirectProduct.inv_left]
    -- Unfold orthogonalActionHom as in mul_def
    unfold orthogonalActionHom orthogonalToMulAut orthogonalToAddAut orthogonalToLinearEquiv
    simp only [MonoidHom.coe_mk, OneHom.coe_mk]
    unfold MulAutMultiplicative
    simp only [MulEquiv.symm_mk, MulEquiv.coe_mk, Equiv.symm_symm]
    simp only [AddEquiv.toMultiplicative, MulEquiv.coe_mk, Equiv.coe_fn_mk]
    unfold AddMonoidHom.toMultiplicative
    simp only [Equiv.coe_fn_mk, MonoidHom.coe_mk, OneHom.coe_mk]
    simp only [toAdd_ofAdd, AddEquiv.coe_toAddMonoidHom, LinearEquiv.coe_toAddEquiv]
    -- Use toAdd_inv: toAdd x⁻¹ = -toAdd x
    simp only [toAdd_inv]
    -- Use that the linear equiv preserves negation
    simp only [map_neg]
    congr 1
  · simp only [orthogonal, SemidirectProduct.inv_right]

/-- A pure translation is an element of the form (v, I).

blueprint: def:translation_subgroup -/
def translationSubgroup : Subgroup EuclideanGroup2 where
  carrier := {g | g.right = 1}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    simp [SemidirectProduct.mul_right, ha, hb]
  one_mem' := by simp [SemidirectProduct.one_right]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    simp [SemidirectProduct.inv_right, ha]

/-- The translation subgroup is normal in E(2).

blueprint: lem:translation_normal -/
instance translationSubgroup_normal : translationSubgroup.Normal := by
  constructor
  intro n hn g
  simp only [translationSubgroup, Subgroup.mem_mk] at hn ⊢
  change (g * n * g⁻¹).right = 1
  rw [SemidirectProduct.mul_right, SemidirectProduct.mul_right, SemidirectProduct.inv_right]
  rw [hn, mul_one, mul_inv_cancel]

/-- The quotient E(2)/T is isomorphic to O(2).

blueprint: lem:euclidean_quotient -/
lemma EuclideanGroup2.quotient_translations :
    Nonempty (EuclideanGroup2 ⧸ translationSubgroup ≃* OrthogonalGroup2) := by
  -- translationSubgroup = kernel of rightHom : E(2) →* O(2)
  -- By first isomorphism theorem, E(2)/ker(rightHom) ≃* range(rightHom) = O(2)
  -- First get the isomorphism for the kernel
  have iso_ker := QuotientGroup.quotientKerEquivOfSurjective
    (SemidirectProduct.rightHom : EuclideanGroup2 →* OrthogonalGroup2)
    SemidirectProduct.rightHom_surjective
  -- Now we need to transport along the equality translationSubgroup = rightHom.ker
  have h_eq : translationSubgroup = SemidirectProduct.rightHom.ker := by
    ext g
    simp only [translationSubgroup, Subgroup.mem_mk]
    simp only [MonoidHom.mem_ker, SemidirectProduct.rightHom_eq_right]
    rfl
  -- Use Quotient.congrRight to transport the quotient
  have iso_trans : (EuclideanGroup2 ⧸ translationSubgroup) ≃* (EuclideanGroup2 ⧸
      SemidirectProduct.rightHom.ker) :=
    QuotientGroup.quotientMulEquivOfEq h_eq
  exact ⟨iso_trans.trans iso_ker⟩

/-- An element (v, S) is a glide reflection if S is a reflection and v is parallel
to the reflection axis.

blueprint: def:glide_reflection -/
def IsGlideReflection (g : EuclideanGroup2) : Prop :=
  ∃ θ : ℝ, g.right.1 = reflectionMatrix θ ∧
    ∃ t : ℝ, g.translation = t • (EuclideanSpace.single 0 (Real.cos (θ/2)) +
                           EuclideanSpace.single 1 (Real.sin (θ/2)))

/-- The square of a glide reflection is a translation by twice the glide vector.

(v, S)² = (2v, I) when v is parallel to the reflection axis.

blueprint: lem:glide_squared -/
lemma glideReflection_sq (g : EuclideanGroup2) (hg : IsGlideReflection g) :
    (g * g).right = 1 := by
  -- (g * g).right = g.right * g.right by semidirect product multiplication
  simp only [SemidirectProduct.mul_right]
  -- For a glide reflection, g.right.1 = reflectionMatrix θ for some θ
  obtain ⟨θ, hθ, _⟩ := hg
  -- Show g.right * g.right = 1 in OrthogonalGroup2
  -- Use Subtype.ext to reduce to showing the underlying matrices are equal
  apply Subtype.ext
  -- (a * b).1 = a.1 * b.1 for units, so goal becomes g.right.1 * g.right.1 = 1
  change g.right.1 * g.right.1 = 1
  rw [hθ]
  exact reflectionMatrix_sq θ

end WallpaperGroups.Euclidean
