# Finite generators across selected weighted polynomial degrees

Import `GradedRings.WeightedVeroneseGenerators`, or the aggregate `GradedRings`.
For a finite variable type `ι`, any commutative semiring `R`, arbitrary natural
weights `w : ι → ℕ` (including zero), and a prescribed `0 < n`, the theorem
`MvPolynomial.exists_finset_weightedVeronese_generators (R := R) w n hn`
produces **one finite family** `T : Finset (MvPolynomial ι R)` with:

```lean
(∀ p ∈ T, ∃ j : ℕ, p.IsWeightedHomogeneous w (n * j)) ∧
∀ j : ℕ, ∀ p : MvPolynomial ι R,
  p.IsWeightedHomogeneous w (n * j) →
    p ∈ Algebra.adjoin R (T : Set (MvPolynomial ι R))
```

The base algebra is over the **entire coefficient semiring `R`**. The proof
chooses the pure powers `X i ^ n` and the finite box of coefficient-one
monomials with every exponent less than `n` and weight divisible by `n`.
Coordinatewise quotient and remainder factor each selected-weight monomial;
weighted-homogeneous induction and coefficient inclusion then cover all
polynomials. The variable and coefficient types have independent universes.
This does not require positive weights, inhabited variables, a nontrivial
coefficient ring, a field or Noetherianity.

The [ordinary direct client](../test/WeightedVeroneseGenerators.lean) uses
the **same** family at weighted degrees `4` and `12` over `ℤ` for weights
`2, 3`, including a nonzero polynomial, and exercises arbitrary semiring
coefficients, zero weights, `Empty`, index one and `ZMod 1`. The
[aggregate-root client](../test/RootClient.lean) checks generic public access.
The result gives selected polynomial-component membership; it neither proves
finite generation of the *whole reindexed graded ring* nor treats `n = 0`
or supplies degree-one generators at every selected index.

## Reproduction and status

The project pins Lean `v4.34.0-rc2` and mathlib
`83abb3e776bdefcbc447a1e44d0debe4010039e5`. Install the pinned
toolchain, fetch its matching mathlib cache **before** building, then run
the three strict native targets from the project root:

```sh
lake exe cache get
lake --wfail build GradedRings GradedRingsTests GradedRingsExamples
```

Formal Frontier agents authored the original selected-polynomial producer,
client and guide; different contributors adapted the native import, aggregate
witness and guide. The theorem concerns selected polynomial components, not
finite type or degree-one generation of every whole selected ring. See
[provenance and credits](PROVENANCE.md). No book text, PDF or third-party
proof code is bundled; source correspondence is a separate decision.
