/-
Copyright (c) 2025 Wallpaper Groups Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import WallpaperGroups.Basic

/-!
# The Euclidean Plane

This file defines the Euclidean plane as ℝ² with the standard inner product structure.

## Main definitions

* `EuclideanPlane` - The Euclidean plane ℝ² as `EuclideanSpace ℝ (Fin 2)`

blueprint: def:euclidean_plane
-/

namespace WallpaperGroups.Euclidean

/-- The Euclidean plane is ℝ² with the standard inner product.

This is the ambient space for wallpaper groups. We use Mathlib's `EuclideanSpace`
which provides the standard Euclidean structure on ℝⁿ.

blueprint: def:euclidean_plane -/
abbrev EuclideanPlane : Type := EuclideanSpace ℝ (Fin 2)

/-- The origin of the Euclidean plane. -/
def origin : EuclideanPlane := 0

/-- Standard basis vector e₁ = (1, 0). -/
noncomputable def e₁ : EuclideanPlane := EuclideanSpace.single 0 1

/-- Standard basis vector e₂ = (0, 1). -/
noncomputable def e₂ : EuclideanPlane := EuclideanSpace.single 1 1

end WallpaperGroups.Euclidean
