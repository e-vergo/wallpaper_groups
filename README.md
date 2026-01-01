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

### Completed ✅

1. **Lean 4 project initialized** with Lake + Mathlib + doc-gen4 (Lean 4.27.0-rc1)
2. **Leanblueprint fully configured and building**:
   - 8 chapters with ~48 definitions and ~64 lemmas/theorems
   - Dependency graph via `\uses{}` macros
   - Local build tested and working
3. **GitHub Actions workflow** configured for auto-deployment

### Next Steps ⏳

1. **Enable GitHub Pages** - In repo settings:
   - Settings → Pages → Source: "GitHub Actions"
   - Settings → Actions → General → Enable "Allow GitHub Actions to create and approve pull requests"

2. **Post to Lean Zulip** - Template ready in `ZULIP_POST.md`

3. **Start Lean implementation** - No Lean code written yet

### Proof Strategy

| Aspect | Decision |
|--------|----------|
| Definition | Discrete cocompact subgroups of E(2) |
| Crystallographic restriction | Trace argument (2cos(θ) ∈ ℤ) |
| Extension classification | Explicit enumeration (not H² cohomology) |
| Completeness | Case exhaustion over (lattice, point group) pairs |
| Naming | IUCr notation (p1, p2, pm, pg, cm, pmm, ...) |

### Mathlib4 Infrastructure

- `EuclideanSpace ℝ (Fin 2)` - Euclidean plane
- `LinearIsometryEquiv` - Orthogonal group elements
- `SemidirectProduct` - For E(2) = ℝ² ⋊ O(2)
- `IsZLattice` - Z-lattice structure
- `DihedralGroup n` - Abstract dihedral groups

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
.
├── WallpaperGroups/
│   └── Basic.lean
├── blueprint/
│   ├── src/
│   │   ├── web.tex
│   │   ├── print.tex
│   │   ├── content.tex
│   │   ├── plastex.cfg
│   │   ├── macros/common.tex
│   │   └── chapter/
│   │       ├── intro.tex
│   │       ├── euclidean.tex
│   │       ├── point_groups.tex
│   │       ├── lattices.tex
│   │       ├── crystallographic.tex
│   │       ├── wallpaper_def.tex
│   │       ├── seventeen.tex
│   │       └── classification.tex
│   └── requirements.txt
├── .github/workflows/blueprint.yml
├── ZULIP_POST.md
├── lakefile.toml
└── lean-toolchain  # v4.27.0-rc1
```

## References

- Armstrong, M.A. *Groups and Symmetry* (Springer UTM)
- Schwarzenberger, R.L.E. "The 17 Plane Symmetry Groups" (Math. Gazette, 1974)
- Conway, J.H. *The Symmetries of Things*
- International Tables for Crystallography, Vol. A

## License

Apache 2.0
