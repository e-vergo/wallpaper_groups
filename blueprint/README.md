# Wallpaper Groups Blueprint

This directory contains the [leanblueprint](https://github.com/PatrickMassot/leanblueprint) for the formalization of the classification of the 17 wallpaper groups in Lean 4.

## Structure

```
blueprint/
├── src/
│   ├── web.tex           # Entry point for web version (plasTeX)
│   ├── print.tex         # Entry point for PDF version
│   ├── content.tex       # Imports all chapter files
│   ├── macros/
│   │   └── common.tex    # Shared LaTeX macros
│   └── chapter/
│       ├── intro.tex           # Introduction and overview
│       ├── euclidean.tex       # Euclidean group E(2)
│       ├── point_groups.tex    # Point groups and O(2) classification
│       ├── lattices.tex        # Lattices and Bravais types
│       ├── crystallographic.tex # Crystallographic restriction
│       ├── wallpaper_def.tex   # Wallpaper group definition
│       ├── seventeen.tex       # The 17 groups (IUCr notation)
│       └── classification.tex  # Main classification theorem
└── README.md
```

## Building

Once the full Lean project is set up with leanblueprint:

```bash
# Install leanblueprint
pip install leanblueprint

# Build web version
leanblueprint web

# Build PDF
leanblueprint pdf

# Check declarations match Lean code
leanblueprint checkdecls

# Serve locally
leanblueprint serve
```

## Key Theorems

1. **Crystallographic Restriction** (`thm:crystallographic_restriction`): Lattice-preserving rotations have order ∈ {1, 2, 3, 4, 6}

2. **Finite Subgroups of O(2)** (`thm:finite_O2_classification`): Every finite subgroup is Cₙ or Dₙ

3. **Bravais Classification** (`thm:bravais_classification`): Five 2D lattice types

4. **Main Classification** (`thm:classification`): Exactly 17 wallpaper groups

## Dependencies

The `\uses{}` macro in each definition/lemma/theorem specifies dependencies, which generate the dependency graph automatically.
