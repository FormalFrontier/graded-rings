# Polynomial modules over semirings

Let `R` be a possibly noncommutative semiring, and let `M` be a left `R`-module
whose additive structure is a commutative monoid. The type
`PolynomialModule.Extension R M` represents finitely supported sequences of
coefficients in `M`. The scalar and coefficient universes are independent.

The [basic module](../GradedRings/PolynomialModule/Basic.lean) gives the coefficient
equivalences, single-degree elements, and the canonical `R[X]`-module structure.
Multiplication by `C r` is the original coefficientwise `R`-action; multiplication
by `X` shifts coefficients upward by one degree. More generally,

\[
  (p \mathbin{\bullet} q)_n
    = \sum_{i+j=n} p_i \mathbin{\bullet} q_j.
\]

This is an ordered coefficient formula. Polynomial scalar multiplication is not
asserted to be `R`-linear when `R` is noncommutative. The coefficient support of
`p • q` is contained in the sum of the supports of `p` and `q`.

## Coefficient scalars and polynomial scalars

The named instances `coefficientModule` and `polynomialModule` distinguish the
original `R`-action from the canonical `R[X]`-action. Additional coefficientwise
scalar structures are explicit data supplied by `pointwiseModule`; they are not
global instances. The corresponding `pointwiseCoeffLinearEquiv` identifies their
coefficients with the usual finitely supported functions.

These actions need not coincide. For example, give the natural numbers the
polynomial action obtained by evaluating `X` at zero. Its coefficientwise
polynomial action kills multiplication by `X`, whereas the canonical polynomial
action on `Extension ℕ ℕ` sends `single ℕ 0 1` to `single ℕ 1 1`.

## Universal property

The [universal-property module](../GradedRings/PolynomialModule/UniversalProperty.lean)
provides an additive equivalence

\[
  \operatorname{Hom}_{R[X]}(\operatorname{Extension}_R M,N)
    \simeq
  \operatorname{Hom}_{C}(M,N).
\]

Here `N` has only its given `R[X]`-module structure, and the right-hand side consists
of additive maps satisfying `g (r • m) = C r • g m`. No additional `R`-action or
scalar-tower hypothesis on `N` is required. Restriction evaluates a map on
`single R 0`; the inverse sends a coefficient sequence to the finite sum of
`monomial n 1 • g (q.coeff n)`. The equivalence has application, inverse and
uniqueness lemmas.

## Semilinear maps and coordinates

A ring homomorphism `σ : R →+* S` and a `σ`-semilinear map on coefficients induce
a semilinear map of extensions along `Polynomial.mapRingHom σ`. It acts
coefficientwise, respects single-degree elements, and satisfies identity and
composition laws. Thus

\[
  \operatorname{map}(p \mathbin{\bullet} q)
    = p.\operatorname{map}(\sigma) \mathbin{\bullet} \operatorname{map}(q).
\]

For families of semirings and their modules, coordinate evaluation is an instance
of this construction. The polynomial scalar map evaluates every coefficient at
the chosen coordinate. The target retains its coordinate polynomial action; no
action of the product semiring on the individual coefficient module is needed.
The forward coordinate map assumes neither finiteness nor nonemptiness of the
index type.

## Finite products

The [finite-product module](../GradedRings/PolynomialModule/Pi.lean) provides
`PolynomialModule.Extension.piEquiv R M` for a finite family of possibly
noncommutative semirings `R i` and their original modules `M i`. Only additive
commutative monoids are required on the modules. The product-index, scalar and
module universes are independent, and the public index assumption is `Finite`.
The equivalence is semilinear along `Polynomial.piRingEquiv R`:

\[
  \operatorname{Extension}_{\prod_i R_i}(\prod_i M_i)
    \simeq
  \prod_i \operatorname{Extension}_{R_i}(M_i).
\]

Both polynomial actions are the canonical ones, induced by the given coefficient
modules. `piEquiv_apply` identifies each component with `coordinate`;
`coeff_piEquiv` and `coeff_piEquiv_symm` give the forward and inverse formulas

\[
  (E(q)_i)_n = (q_n)_i, \qquad (E^{-1}(q)_n)_i = (q_i)_n.
\]

Here `E` denotes `PolynomialModule.Extension.piEquiv R M`. The simplification
lemmas `piEquiv_single` and `piEquiv_symm_single` preserve the common degree and
take or assemble the coordinate coefficients. Finiteness is used only to assemble
finitely supported coordinate sequences, not on the degree type. Empty products
are included, with no nonemptiness assumption or additional scalar action on an
individual coefficient module.

## Finite generation

The [finiteness module](../GradedRings/PolynomialModule/Finiteness.lean) proves
`PolynomialModule.Extension.finite_iff`:

```lean
Module.Finite R[X] (PolynomialModule.Extension R M) ↔ Module.Finite R M
```

This holds for every semiring `R` and every `R`-module `M` with an additive
commutative monoid structure, without commutativity of `R` or additive inverses
in `M`. Degree-zero copies of a finite generating set generate the extension,
since multiplication by monomials supplies every degree. Conversely, taking the
constant coefficient gives a surjective semilinear map along
`Polynomial.constantCoeff`. A preservation instance lets typeclass inference
use finite generation of `M` to obtain finite generation of its polynomial
extension; reflection is available through the theorem, not an instance.

## Agreement with Mathlib

The [comparison module](../GradedRings/PolynomialModule/Comparison.lean) applies
under Mathlib's original `CommRing` and `AddCommGroup` hypotheses. It identifies
an extension with `PolynomialModule R M` by sending its coefficient sequence to
`PolynomialModule.ofCoeff R`. Its polynomial linear equivalence fixes Mathlib's
named `PolynomialModule.polynomialModule` structure and preserves every
coefficient, not merely the underlying `R`-linear structure. The inverse and
coefficient-scalar comparison lemmas preserve the original pointwise operations.

The existing Mathlib type and its actions are unchanged. The semiring construction
is a separate generalization with an explicit comparison at the shared floor.

For finite families at these same hypotheses,
`PolynomialModule.Extension.polynomialLinearEquivPolynomialModule_piEquiv`
expresses the pointwise commuting square: converting each component after
`Extension.piEquiv` is the same as applying `PolynomialModule.piEquiv` after
converting the product extension. The proof uses the coefficient formulas for
both equivalences. This compatibility statement retains the comparison's
`CommRing` and `AddCommGroup` hypotheses; the extension finite-product
equivalence itself requires only the semiring and additive-monoid hypotheses.
