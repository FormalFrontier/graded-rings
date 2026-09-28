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

These are reproduction instructions, not an assertion that this transfer
ran a build. At the September 28, 2026 static transfer checkpoint, the
original isolated implementation had a successful cache-first focused build,
a complete actual-origin private/generated-inclusive transitive standard-three
axiom audit and independent review; Atlas accepted that *isolated* candidate
on September 28, 2026. Those checks and review do **not** establish the
changed destination graph's three-target build, full private-inclusive audit
or fresh destination review. Maintainer acceptance, protected integration,
verified release and source-specific correspondence remain separate. The
owning issue #67 records later revision-specific decisions.

Original mathematical producer, direct client and guide: worker-b Hive Task
`hive-request-b19ed49dc35a86b4f2c7f461f7a2a8997c0265da`, UID
`a441c096-818a-45de-9581-5f096b28e669`. Original fresh independent
review: worker-a Hive Task `hive-request-c63463c2ee5ed9e6cd9ca9927719b6e7cf21d0f2`,
UID `9848d86f-0a38-433e-ab52-5eb525143762`. This distinct static
destination transfer, aggregate witness, guide and metadata: worker-b Hive
Task `hive-request-71135ca8e40ee75e265b4be2ece6f790e993636c`, UID
`f002571f-0a86-4430-a7b1-09bbcd5e1b7f`. See [provenance](PROVENANCE.md).
Original project expression follows the repository's Apache-2.0 terms;
no textbook prose, PDF or third-party proof code is redistributed here.
