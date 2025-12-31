# Zulip Post: Formalizing the 17 Wallpaper Groups

**Topic suggestion**: `new members` or `Is there code for X?`

---

## Post Title
Formalizing the 17 Wallpaper Groups - Blueprint Feedback Request

## Post Body

Hi everyone,

I'm planning to formalize the classification of the 17 wallpaper groups (plane crystallographic groups) in Lean 4 + Mathlib. I've created a blueprint and would love feedback before diving into the implementation.

### Project Overview

**Main theorem**: There are exactly 17 wallpaper groups up to isomorphism.

**Definition**: A *wallpaper group* is a discrete cocompact subgroup of E(2), the Euclidean group of plane isometries.

**Proof strategy**:
1. Crystallographic restriction theorem (trace argument): rotations must have order ∈ {1, 2, 3, 4, 6}
2. Classify the 10 crystallographic point groups (finite subgroups of O(2) satisfying the restriction)
3. Classify the 5 Bravais lattice types
4. Enumerate extensions for each compatible (lattice, point group) pair
5. Prove there are exactly 17 non-isomorphic groups

### Blueprint

I've prepared a full leanblueprint with:
- ~45 definitions
- ~58 lemmas/theorems
- Dependency graph via `\uses{}` macros

[Link to blueprint once hosted, or attach files]

### Mathlib Infrastructure

**Already available**:
- `EuclideanSpace ℝ (Fin 2)` - Euclidean plane
- `LinearIsometryEquiv` - Orthogonal group
- `SemidirectProduct` - For E(2) = ℝ² ⋊ O(2)
- `IsZLattice` - Z-lattice structure
- `DihedralGroup n` - Abstract dihedral groups

**Needs to be built**:
- E(2) as explicit semidirect product
- Discrete/cocompact subgroup predicates
- Classification of finite subgroups of O(2) as Cₙ or Dₙ
- The 5 Bravais lattice types
- The 17 wallpaper groups themselves

### Questions for the Community

1. **E(2) construction**: Is there existing infrastructure for constructing affine isometry groups as semidirect products? Or should I build ℝ² ⋊ O(2) from scratch using `SemidirectProduct`?

2. **Discrete subgroups**: What's the idiomatic way to express "discrete subgroup of a topological group" in Mathlib4? I see `DiscreteTopology` but I'm not sure how to apply it to subgroups.

3. **Cocompactness**: Is there API for cocompact group actions or characterizing when quotients are compact?

4. **O(2) classification**: Has anyone formalized that finite subgroups of O(2) are exactly cyclic groups Cₙ and dihedral groups Dₙ?

5. **DihedralGroup embedding**: What's the cleanest way to embed `DihedralGroup n` into `LinearIsometryEquiv`? Should I construct explicit rotation/reflection matrices?

6. **Lattice classification**: Is the Bravais classification (5 lattice types in 2D) anywhere in Mathlib?

7. **Related work**: Are there any similar formalizations in progress? (crystallographic groups, space groups, etc.)

### Estimated Scope

Based on similar blueprints, I estimate:
- ~3000-4000 lines of Lean
- Moderate complexity (no heavy analysis, mainly algebra and discrete geometry)

I'd appreciate any feedback on the approach, potential pitfalls, or suggestions for leveraging existing Mathlib infrastructure!

Thanks,
Eric

---

## Alternative: Shorter Version

If you prefer a shorter post:

---

**Title**: Planning: Formalizing 17 Wallpaper Groups

I'm planning to formalize that there are exactly 17 wallpaper groups (discrete cocompact subgroups of E(2)). I have a [blueprint](link) ready.

Quick questions:
1. Best way to define E(2) = ℝ² ⋊ O(2)? Use `SemidirectProduct`?
2. How to express "discrete subgroup" in Mathlib4?
3. Is "finite subgroups of O(2) are Cₙ or Dₙ" formalized?
4. Any related work on crystallographic groups?

Happy to share the full blueprint for feedback!
