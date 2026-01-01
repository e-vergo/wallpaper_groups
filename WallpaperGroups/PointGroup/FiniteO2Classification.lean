/-
Copyright (c) 2025 Wallpaper Groups Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import WallpaperGroups.PointGroup.CyclicDihedral

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

/-- Every finite subgroup of SO(2) is cyclic.

Since SO(2) ≅ S¹ ≅ ℝ/ℤ, finite subgroups correspond to cyclic subgroups ⟨1/n⟩ ⊂ ℝ/ℤ.

blueprint: lem:finite_SO2_cyclic -/
lemma finite_subgroup_SO2_isCyclic (H : Subgroup OrthogonalGroup2)
    (hH_finite : Finite H)
    (hH_SO2 : ∀ A ∈ H, A ∈ SpecialOrthogonalGroup2) :
    IsCyclic H := by
  sorry

/-- If H ⊂ O(2) is finite and H ∩ SO(2) is trivial, then H has at most 2 elements. -/
lemma finite_subgroup_O2_trivial_intersection (H : Subgroup OrthogonalGroup2)
    (hH_finite : Finite H)
    (hH_trivial : ∀ A ∈ H, A ∈ SpecialOrthogonalGroup2 → A = 1) :
    Nat.card H ≤ 2 := by
  sorry

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
  sorry

/-- The order of a finite subgroup of O(2) determines whether it's cyclic or dihedral. -/
lemma finite_subgroup_O2_cyclic_iff (H : Subgroup OrthogonalGroup2)
    (hH_finite : Finite H) :
    (∀ A ∈ H, A ∈ SpecialOrthogonalGroup2) ↔
    (∃ n : ℕ, ∃ _ : NeZero n, Nonempty (H ≃* CyclicPointGroup n)) := by
  sorry

end WallpaperGroups.PointGroup
