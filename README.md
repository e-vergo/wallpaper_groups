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

---

## Current Status

**Project builds successfully** with Lean 4.27.0-rc1 + Mathlib.

| Metric | Count |
|--------|-------|
| Lean files | 23 |
| Lines of code | ~7,700 |
| Remaining `sorry` | 94 |

### Completed ✅

- **Euclidean foundations**: E(2) = ℝ² ⋊ O(2) semidirect product structure
- **Orthogonal group**: O(2), SO(2), rotation/reflection matrices with full algebraic properties
- **Point groups**: Cyclic Cₙ and dihedral Dₙ subgroups of O(2) with cardinality proofs
- **Lattices**: Rank-2 lattice structure, basis existence, discreteness
- **Lattice symmetry**: Finite symmetry groups, integer matrix characterization
- **Crystallographic restriction**: Main theorem proving rotation orders ∈ {1,2,3,4,6}
- **Wallpaper group definition**: IsWallpaperGroup predicate with discrete + cocompact conditions
- **All 17 groups defined**: p1, p2, pm, pg, cm, pmm, pmg, pgg, cmm, p4, p4m, p4g, p3, p3m1, p31m, p6, p6m

### In Progress ⏳

- **Group properties**: isWallpaperGroup, isSymmorphic, pointGroup proofs for each of 17 groups
- **Bravais classification**: Proving every lattice is exactly one of 5 types
- **Distinctness**: Proving the 17 groups are pairwise non-isomorphic
- **Completeness**: Main classification theorem

### Proof Strategy

| Aspect | Decision |
|--------|----------|
| Definition | Discrete cocompact subgroups of E(2) |
| Crystallographic restriction | Trace argument (2cos(θ) ∈ ℤ) |
| Extension classification | Explicit enumeration (not H² cohomology) |
| Completeness | Case exhaustion over (lattice, point group) pairs |
| Naming | IUCr notation (p1, p2, pm, pg, cm, pmm, ...) |

---

## Building

### Lean Project

```bash
lake update
lake exe cache get
lake build
```

### Blueprint (requires TeX + Python)

```bash
# Install dependencies
brew install --cask basictex  # or full MacTeX
pip install leanblueprint

# Build and serve
leanblueprint web
leanblueprint serve  # View at http://localhost:8000
```

## Project Structure

```
WallpaperGroups/
├── Basic.lean                      # Common imports
├── Euclidean/
│   ├── Plane.lean                  # EuclideanPlane = EuclideanSpace ℝ (Fin 2)
│   ├── OrthogonalGroup.lean        # O(2), SO(2), rotation/reflection matrices
│   └── EuclideanGroup.lean         # E(2) = ℝ² ⋊ O(2)
├── PointGroup/
│   ├── RotationReflection.lean     # Shared rotation/reflection helpers
│   ├── CyclicPointGroup.lean       # Cₙ definitions and properties
│   ├── DihedralPointGroup.lean     # Dₙ definitions and properties
│   └── FiniteO2Classification.lean # Finite subgroups of O(2) are Cₙ or Dₙ
├── Lattice/
│   ├── Basic.lean                  # Lattice2 structure, basis, discreteness
│   ├── Symmetry.lean               # Lattice symmetry groups
│   └── BravaisTypes.lean           # 5 Bravais lattice types
├── Crystallographic/
│   ├── Restriction.lean            # Crystallographic restriction theorem
│   └── PointGroups.lean            # 10 crystallographic point groups
├── Wallpaper/
│   ├── Definition.lean             # IsWallpaperGroup predicate
│   └── Structure.lean              # Translation subgroup, point group structure
├── Groups/
│   ├── Oblique.lean                # p1, p2
│   ├── Rectangular.lean            # pm, pg, pmm, pmg, pgg
│   ├── CenteredRectangular.lean    # cm, cmm
│   ├── Square.lean                 # p4, p4m, p4g
│   └── Hexagonal.lean              # p3, p3m1, p31m, p6, p6m
└── Classification/
    ├── Verification.lean           # Each group is a wallpaper group
    ├── Distinctness.lean           # Groups are pairwise non-isomorphic
    └── Completeness.lean           # Main theorem: exactly 17 groups
```

## References

- Armstrong, M.A. *Groups and Symmetry* (Springer UTM)
- Schwarzenberger, R.L.E. "The 17 Plane Symmetry Groups" (Math. Gazette, 1974)
- Conway, J.H. *The Symmetries of Things*
- International Tables for Crystallography, Vol. A

## License

Apache 2.0
