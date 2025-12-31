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

## Current Status (Handoff Notes)

### What's Done ✅

1. **Lean 4 project initialized** with Lake + Mathlib 4.26.0 + doc-gen4
2. **Leanblueprint structure created** with full LaTeX content:
   - `blueprint/src/chapter/` - 8 chapters covering all definitions and theorems
   - `blueprint/src/web.tex` and `print.tex` - entry points
   - `blueprint/src/macros/common.tex` - shared LaTeX macros
   - Dependency graph via `\uses{}` macros throughout
3. **GitHub Actions workflow** at `.github/workflows/blueprint.yml` for auto-deployment
4. **~48 definitions and ~64 lemmas/theorems** fully specified in the blueprint

### What's Pending ⏳

1. **Run `lake update`** - Mathlib clone was interrupted. On fresh clone, run:
   ```bash
   lake update        # Fetches mathlib + doc-gen4 (takes a few minutes)
   lake exe cache get # Downloads prebuilt mathlib (much faster than building)
   ```

2. **Enable GitHub Pages** - In repo settings:
   - Settings → Pages → Source: "GitHub Actions"
   - Settings → Actions → General → Enable "Allow GitHub Actions to create and approve pull requests"

3. **Post to Lean Zulip** - Template ready in `ZULIP_POST.md` for community feedback

4. **Start Lean implementation** - No Lean code written yet, just the blueprint

### Proof Strategy Decisions

| Aspect | Decision |
|--------|----------|
| Definition | Discrete cocompact subgroups of E(2) |
| Crystallographic restriction | Trace argument (2cos(θ) ∈ ℤ) |
| Extension classification | Explicit enumeration (not H² cohomology) |
| Completeness | Case exhaustion over (lattice, point group) pairs |
| Naming | IUCr notation (p1, p2, pm, pg, cm, pmm, ...) |

### Mathlib4 Infrastructure Available

- `EuclideanSpace ℝ (Fin 2)` - Euclidean plane
- `LinearIsometryEquiv` - Orthogonal group elements
- `SemidirectProduct` - For E(2) = ℝ² ⋊ O(2)
- `IsZLattice` - Z-lattice structure
- `DihedralGroup n` - Abstract dihedral groups

### Key Questions for Zulip

1. Best way to define E(2) as semidirect product?
2. How to express "discrete subgroup" idiomatically?
3. Is finite subgroups of O(2) classification formalized?
4. Any related crystallographic work in progress?

---

## Building

```bash
# First time setup (after cloning)
lake update
lake exe cache get

# Build the project
lake build

# Build blueprint locally (requires Python + leanblueprint)
pip install leanblueprint
leanblueprint web
leanblueprint serve  # View at http://localhost:8000
```

## Project Structure

```
.
├── WallpaperGroups/
│   └── Basic.lean           # Placeholder (no code yet)
├── blueprint/
│   ├── src/
│   │   ├── web.tex          # plasTeX entry (dependency graph)
│   │   ├── print.tex        # PDF entry
│   │   ├── content.tex      # Chapter imports
│   │   ├── macros/common.tex
│   │   ├── plastex.cfg      # plasTeX config
│   │   └── chapter/
│   │       ├── intro.tex
│   │       ├── euclidean.tex       # E(2) definitions
│   │       ├── point_groups.tex    # Cₙ, Dₙ classification
│   │       ├── lattices.tex        # 5 Bravais types
│   │       ├── crystallographic.tex # Restriction theorem
│   │       ├── wallpaper_def.tex   # Wallpaper group def
│   │       ├── seventeen.tex       # All 17 groups
│   │       └── classification.tex  # Main theorem
│   └── requirements.txt
├── .github/workflows/blueprint.yml  # CI/CD for Pages
├── ZULIP_POST.md                    # Ready-to-post template
├── lakefile.toml                    # Lake config (mathlib + doc-gen4)
└── lean-toolchain                   # Lean 4.26.0
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
- International Tables for Crystallography, Vol. A

## License

Apache 2.0
