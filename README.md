# Classification of the 17 Wallpaper Groups

A Lean 4 formalization of the theorem that there are exactly 17 wallpaper groups up to isomorphism.

## Overview

A **wallpaper group** (plane crystallographic group) is a discrete cocompact subgroup of the Euclidean group E(2). This project formalizes:

1. **Crystallographic restriction theorem**: Lattice-preserving rotations have order ∈ {1, 2, 3, 4, 6}
2. **Point group classification**: 10 crystallographic point groups (C₁, C₂, C₃, C₄, C₆, D₁, D₂, D₃, D₄, D₆)
3. **Bravais lattice classification**: 5 types (oblique, rectangular, centered rectangular, square, hexagonal)
4. **Main theorem**: Exactly 17 wallpaper groups exist

## Blueprint

The formalization blueprint with dependency graph is available at:
- **Blueprint**: https://e-vergo.github.io/wallpaper_groups/blueprint/
- **API docs**: https://e-vergo.github.io/wallpaper_groups/docs/

## Building

```bash
# Get mathlib cache (much faster than building from source)
lake exe cache get

# Build the project
lake build
```

## Project Structure

```
WallpaperGroups/
├── Basic.lean              # Main entry point
├── Euclidean/             # E(2) = ℝ² ⋊ O(2)
├── PointGroup/            # Finite subgroups of O(2)
├── Lattice/               # Z-lattices and Bravais types
└── WallpaperGroup/        # The 17 groups and classification
```

## GitHub Setup

To enable GitHub Pages for the blueprint:

1. Go to **Settings** → **Pages**
2. Under **Source**, select **GitHub Actions**
3. Go to **Settings** → **Actions** → **General**
4. Enable **Allow GitHub Actions to create and approve pull requests**

## References

- Armstrong, M.A. *Groups and Symmetry* (Springer UTM)
- Schwarzenberger, R.L.E. "The 17 Plane Symmetry Groups" (Math. Gazette, 1974)
- Conway, J.H. *The Symmetries of Things*

## License

Apache 2.0
