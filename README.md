# css-decoupling-lean

A Lean 4 formalization of the results of

> M. He, Y. Wang, H. Song, and Y. Gu, *Toric codes all the way down:
> decoupling translation-invariant topological CSS codes in higher
> dimensions*, arXiv:XXXX.XXXXX (2026).

The formalization works over the actual Laurent polynomial ring
`F_p[Z^D]`, for every prime p and every D ≥ 2, with the superselection
profile defined as a derived object in Mathlib's derived category. It proves
every numbered result of the article and the algebraic statements about its
example, the glued code. The whole project uses only the standard axioms
`propext`, `Classical.choice` and `Quot.sound`; it contains no `sorry`,
`admit`, `native_decide` or project-specific axiom.

The Python implementation of the article's algorithms is a separate
repository, [css-decoupling](https://github.com/hmx21/css-decoupling).
This formalization does not verify that implementation.

## Build

The toolchain is Lean `v4.34.0` with Mathlib `v4.34.0`
(commit `5ed2965256430c3649e86755f9576b54eca72435`), pinned by
`lean-toolchain` and `lake-manifest.json`.

```sh
lake exe cache get     # download prebuilt Mathlib
lake build
```

`lakew` is a thin wrapper that prefers a project-local toolchain in
`.toolchain/` and otherwise calls `lake`. The library is built with
`warningAsError = true`.

## Axiom audit

```sh
lake env lean AuditAll.lean
lake env lean AxiomAudit.lean
```

`AuditAll.lean` collects the transitive axioms of every declaration in the
project, including private and generated ones, and fails if any axiom other
than `propext`, `Classical.choice` and `Quot.sound` occurs.
`AxiomAudit.lean` prints the axioms of the main results individually.

## Correspondence with the article

Declarations are in the namespace `Decoupling.HighDim`; files are under
`Decoupling/HighDim/`.

| Article | Lean | Notes |
| --- | --- | --- |
| Theorem 1, decoupling criterion | `DecouplingCriterion.theorem1_X_canonical` | Decoupling by a local SUM/SWAP circuit with ancillas on a given superlattice, if and only if the restricted profile is that of a toric-code stack. No finiteness of the layers is assumed. |
| Theorem 1, Z sector | `DecouplingCriterion.theorem1_Z`, `theorem1_Z_complementary` | Including the on-site Fourier transform and TC_j ↔ TC_(D−j). |
| Algorithm 1 | `AlgorithmOneSpecification`, `SchreyerAlgorithmOne` | Correctness of the rejection and success branches. The free resolution is a noncomputable Schreyer construction; Algorithm 1 is not an executable Lean program. |
| Algorithm 2 | `SequentialSparseCircuit.materializedProgram`, `materialized_physical_cases` | An executable Lean program on finite arrays, with the physical meaning of its output proved. |
| Proposition 1, polynomial cost | `SequentialSparseCircuit.proposition_one_sparse` | One polynomial, depending only on D, bounds the field operations, the circuit depth and the ancillas of the program above, in the number of coefficients of the input differentials. |
| Proposition 2, vanishing criterion | `KoszulLatticeFiniteExt`, `MinimalLatticeNativeRelative` | |
| Corollary 1, logical qudits on a torus | `Torus.paper_corollary3` | Arbitrary period lattice. |
| Corollary 2, minimal coarse-graining | `Paper.corollary2_form`, `corollary2_atMostOne`, `corollary2_threeDimensional` | At most two nonzero layers, as in the article. |
| Lemma 1, values of a class | `ExtValuesTensor`, `ExtValuesTensorTable`, `ExtValuesLinear` | |
| Lemma 2, restriction to pΛ_triv | `ExtRestrictionVanishing` | |
| Lemma 3, degree bound | `DegreeBound.ext_eq_zero` | |
| Lemma 4, bounded free model | `SchreyerCSS.lemma4` | Schreyer's algorithm over the polynomial ring and localization; degrees \|n\| ≤ D+2. |
| Lemma 5, split triangles | `Triangles` | |
| Lemma 6, gluing | `AdjacentGluing.formal_iff_all_delta` | Any number of layers. |
| Lemma 7, invariance of the profile | `ProfileStabilityCircuit`, `ProfileStabilityAncilla`, `ProfileStabilityMoves` | Including general CSS-preserving Clifford actions. |
| Lemma 8, coarse-grained profile | `LatticePhysical`, `LatticeCompatibility`, `LatticeProfile` | |
| Lemma 9, values on a superlattice | `KoszulLattice.finite_restriction_table` | Arbitrary, also oblique, superlattices. |
| Lemma 10, stable isomorphism of cokernels | `StableFreeDerived`, `StableFreeEffectiveCochainOutput` | Generalized Schanuel route; no free basis of a projective module is computed. |
| Lemma 11, invertible lift | `AlgorithmTwoInvertibleFromPresentation` | |
| Lemma 12, gates | `SparseCircuitSupport`, `OnSiteSwap`, `SparseCircuitPhysical` | |
| Lemma 13, one layer on a torus | `Torus.torus_layer` | |

The glued code of Secs. III B and V:

| Article | Lean |
| --- | --- |
| Check matrices and couplings | `Glued.checks`, `Glued.couplingX`, `Glued.couplingZ`, `Glued.coupling_square` |
| Topological, layers E¹ ≅ E² ≅ F_p, Λ_triv = Z³ | `Glued.topological`, `Glued.actualLayerOneIso`, `Glued.actualLayerTwoIso`, `Glued.lambda0_eq_top` |
| Gluing class with plaquette values (−1, 0, 0), nonzero | `Glued.couplingClass_table`, `Glued.couplingClass_ne_zero` |
| Coarse-graining along x₂ suffices; index p is minimal | `GluedDirectional.lattice_index`, `GluedDirectional.exists_noAncilla_sumCircuit`, `Glued.physicalMinimum` |
| CNOT circuit for p = 2 | `GluedDirectional.binary_noAncilla_transport` |
| 6 or 4 logical qudits on an L₁ × L₂ × L₃ torus | `Glued.rectangular_logicalQudits` |

## Scope

- The formalization proves the statements of the article. Some explanatory
  arguments in the text are not formalized separately: the general signed-area
  and discrete Green formulas, the pictures of strings and relabeled checks,
  and the literal mapping cone drawn in Appendix A5 (the formalization uses an
  isomorphic normalized cone).
- In the cost bound, the formalization uses its own effective Hermann-type
  degree bound with a conservative constant; it does not formalize the
  specific bound quoted from the literature in Appendix C5. Proposition 1
  itself is proved.
- Costs count field operations, not bit operations, for fixed D, measured in
  the dense coefficient count of the given coarse-grained complex. They do not
  bound the coarse-graining index or the preparation of Algorithm 1.

## Layout

- `Decoupling/HighDim/`: the formalization of the article.
- `Decoupling/` (top level): shared infrastructure (Laurent rings, CSS checks,
  Koszul complexes, circuits) and an earlier formalization of the
  three-dimensional case, on which the high-dimensional development builds.
- `Decoupling.lean`: imports every module.

## License

MIT; see [LICENSE](LICENSE). Mathlib is distributed under the Apache 2.0
license.

The formalization was developed by Mingxin He with the AI coding assistant
Codex (OpenAI). Please cite the article above; see
[CITATION.cff](CITATION.cff).
