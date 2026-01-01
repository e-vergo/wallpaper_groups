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
      ext v
      simp only [LinearMap.coe_comp, LinearMap.id_coe, Function.comp_apply, id_eq]
      rw [Matrix.toEuclideanLin_apply, Matrix.toEuclideanLin_apply]
      sorry)
    (by
      ext v
      simp only [LinearMap.coe_comp, LinearMap.id_coe, Function.comp_apply, id_eq]
      rw [Matrix.toEuclideanLin_apply, Matrix.toEuclideanLin_apply]
      sorry)

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
    ext v
    simp only [orthogonalToMulAut, orthogonalToAddAut, orthogonalToLinearEquiv]
    simp only [MulAutMultiplicative]
    sorry
  map_mul' := by
    intros A B
    ext v
    simp only [orthogonalToMulAut, orthogonalToAddAut, orthogonalToLinearEquiv]
    sorry

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
    sorry
  · simp only [orthogonal, SemidirectProduct.mul_right]

/-- Inverse in E(2).

(v, A)⁻¹ = (-A⁻¹v, A⁻¹)

blueprint: lem:euclidean_inv -/
lemma EuclideanGroup2.inv_def (g : EuclideanGroup2) :
    g⁻¹.translation = -(Matrix.toEuclideanLin g.right⁻¹.1 g.translation) ∧
    g⁻¹.orthogonal = g.orthogonal⁻¹ := by
  constructor
  · simp only [translation, SemidirectProduct.inv_left]
    sorry
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
  sorry

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
  sorry

end WallpaperGroups.Euclidean
