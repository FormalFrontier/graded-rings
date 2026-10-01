# Finite degree-one generation of a selected-components ring

Import `GradedRings.FiniteVeronese` directly, or import `GradedRings` to use
the aggregate public API. Let `S` be a commutative ring, **including the zero
ring**, with an internal natural grading `𝒮 : ℕ → σ` and
`[SetLike σ S] [AddSubgroupClass σ S] [GradedRing 𝒮]`. For a finite index
type `ι`, strictly positive weights `w : ι → ℕ`, homogeneous elements
`x i : 𝒮 (w i)` and genuine algebra generation over the *actual* old
degree-zero component,

```lean
Algebra.adjoin (𝒮 0) (Set.range (fun i => (x i : S))) = ⊤
```

`GradedRing.Veronese.exists_finite_degree_one_generators 𝒮 w hw x hgen`
returns a finite set `T` in the entire new degree-one component of
`VeroneseRing 𝒮 (Finsupp.weightedBlockSize w)` such that

```lean
T ⊆ (GradedRing.Veronese.component 𝒮 (Finsupp.weightedBlockSize w) 1 : Set _)
Algebra.adjoin (GradedRing.Veronese.component 𝒮 (Finsupp.weightedBlockSize w) 0) T = ⊤
```

`Finsupp.weightedBlockSize w = max 1 (Fintype.card ι) * ∏ i, w i` is positive,
including when `ι` is empty (then it is `1`); it need not be minimal. This
theorem generates the **whole selected direct-sum ring**
`⨁ j, 𝒮 (Finsupp.weightedBlockSize w * j)`, not just an image inside `S`.
The coefficient ring is its *own full new degree-zero component*, canonically
identified with the old `𝒮 0` by `GradedRing.Veronese.zeroRingEquiv` for a
positive index. Elements of `𝒮 0` need not be constant polynomials over a
smaller base ring.

`GradedRing.Veronese.exists_positive_finite_degree_one_generators 𝒮`
instead requires `[Algebra.FiniteType (𝒮 0) S]` and supplies **some**
`n > 0` and a finite set of the new degree-one component generating the
whole `VeroneseRing 𝒮 n` over its actual new degree-zero component. This is
not an assumed chosen generating family: the proof extracts finite positive-
degree homogeneous generators from the native finite-type instance.

The proof combines finite fibers of strictly positive weighted degree and
weighted-block polynomial-adjoin factorization. Weighted homogeneous
evaluation lifts every old selected summand. Adjoin induction constructs a
witness **inside** the new ring for each evaluated polynomial; a coefficient
`r : 𝒮 0` is transported through `(zeroRingEquiv 𝒮 D hD).symm` and the
new ring's existing scalar algebra map. Injectivity of the positive-index
selected-ring inclusion and direct-sum induction cover the entire ring,
including degree zero. Relations, vanishing products, nilpotents and arbitrary
zero-degree coefficients need no extra assumptions. The results do **not**
require a field, domain, `Nontrivial`, `IsNoetherianRing`, equal weights, or
the finite generation of the entire new degree-one module. Strictly positive
input weights are essential to the finite-fiber construction. Neither theorem
claims generation for **every** index, coefficient regrouping, or a Proj or
scheme statement.

The [ordinary direct-import client](../test/FiniteVeronese.lean) proves
generation of `MvPolynomial (Fin 3) ℤ` for ambient weights `0, 2, 3` by the
two positive-weight variables `X 1, X 2` over the full old zero component;
it proves `X 0` has degree zero and is **nonconstant**, then uses the first
theorem on this proved input. It checks the coefficient triangle through
`zeroRingEquiv`, constructs a genuine `Algebra.FiniteType` instance from the
finite generating range and applies the second theorem. Additional clients
prove their input generation for empty `ι` with `D = 1`, test the zero ring
`ZMod 1`, and exercise nilpotence in `ZMod 4` with the same proved generating
family. The [aggregate-root witness](../test/RootClient.lean) calls the first
theorem through an ordinary `import GradedRings`. Private and anonymous
clients are not extra public interfaces.

## Reproduction and dated status

The checked-in `lean-toolchain`, `lakefile.toml` and `lake-manifest.json` pin
Lean `v4.34.0-rc2` and mathlib
`83abb3e776bdefcbc447a1e44d0debe4010039e5` with the destination's
nine exact resolved packages. In a checkout of **this** library, fetch the
matching precompiled mathlib cache first, then check all three native targets
with warnings treated as errors, including both the direct and aggregate clients:

```sh
elan toolchain install leanprover/lean4:v4.34.0-rc2
lake exe cache get
LEAN_NUM_THREADS=1 LAKE_JOBS=1 lake --wfail build GradedRings GradedRingsTests GradedRingsExamples
```

Formal Frontier agents wrote the original producer, direct client and guide;
separate contributors adapted the imports and registration for this library.
The proof uses earlier weighted-evaluation and positive-weight adjoin APIs;
no source-specific exercise correspondence follows. See
[provenance and credits](PROVENANCE.md).
