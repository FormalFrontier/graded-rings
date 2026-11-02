# Graded rings

Reusable Lean constructions for graded rings, integer filtrations and associated
graded modules, quotients and localizations, finiteness and primes, symmetric
algebras, prime multiplicity, and selected-component Veronese rings. Start with the
mathematics below; the [interface overview](#find-an-interface) links module
references and focused guides.

Authors: Formal Frontier Agents. Original project contributions are licensed
under [Apache-2.0](LICENSE). AI agents developed the Lean formalizations,
proofs, clients and documentation; contributor credits are summarized in
[provenance and credits](docs/PROVENANCE.md).

## Headline results

These are reusable algebraic APIs, not claims of source-specific correspondence
or complete book coverage. Selected-ring and evaluation results below concern
**naturally graded commutative rings** unless another base is stated. Old and new
degree-zero coefficients mean the **entire actual components**, not a smaller
chosen coefficient ring.

- **Polynomial covers and equivalences for principal ideals.** For any
  commutative ring `R` and `a : R`, evaluation at the class of `a t` defines a
  surjective `R/(a)`-algebra map `(R/(a))[T] → C`, where `C` is the Rees algebra
  modulo its coefficient ideal. If `a` is regular, this same map is an
  `R/(a)`-algebra equivalence, including unit generators and the zero ring.
  Composition with augmentation is evaluation at zero
  ([`reesAlgebra.principalPolynomialHom`](GradedRings/ReesAlgebra/PrincipalPolynomial.lean),
  `surjective_principalPolynomialHom`,
  `bijective_principalPolynomialHom`, `principalPolynomialEquiv`, and
  `augmentation_comp_principalPolynomialEquiv`).
- **Coefficient homomorphisms of Rees algebras.** For commutative rings `R`, `S`,
  a ring homomorphism `f : R →+* S` and ideals `I`, `J` with `I.map f ≤ J`,
  [coefficient change](GradedRings/ReesAlgebra/Map.lean) defines
  `reesAlgebra I →+* reesAlgebra J`. Its underlying polynomial map applies `f`
  to every coefficient, and it respects identities and composition. A source
  element belongs to its kernel exactly when every coefficient belongs to
  `RingHom.ker f`. The map is surjective exactly when `f` is surjective and
  `I.map f = J`. The ring universes are independent; no `Algebra R S` structure,
  regularity, nontriviality or finiteness assumption is required.
- **Quotients and localizations.** For commutative rings,
  [homogeneous-ideal quotients](GradedRings/Quotient.lean) inherit the image grading
  for additive-monoid degrees with decidable equality. [Full localization](GradedRings/Localization.lean)
  at homogeneous denominators uses an additive commutative **group** of degrees;
  its degree-zero component is equivalent to equal-degree homogeneous fractions.
  Both allow zero rings without a domain assumption; localization also permits
  zero-divisor denominators.
- **Localization maps and reducedness.** The [degree-multiplying map](docs/degree-multiplying-homogeneous-localization.md)
  uses natural gradings, an ordinary unital ring homomorphism, explicit degree
  compatibility and mapped denominators. Even factor zero requires its degree
  witness; source charts may be arbitrary, but restriction factors are homogeneous.
  Separately, [homogeneous localization preserves reducedness](GradedRings/HomogeneousLocalizationReduced.lean)
  for a **reduced commutative ring**, additive commutative **monoid** degrees with
  decidable equality and any denominator submonoid. Neither interface requires
  a domain, regular denominators or nontriviality; the map needs no positive factor.
- **Finiteness and primes.** In a naturally graded commutative ring,
  [finite type over old degree zero](GradedRings/FiniteType.lean) is equivalent to
  finite generation of the irrelevant ideal; [Noetherianity](GradedRings/Noetherian.lean)
  is equivalent to that finite generation plus Noetherian degree zero.
  For an **integer**-graded commutative ring with a positive-degree homogeneous
  unit, [homogeneous primes](GradedRings/HomogeneousPrime.lean) correspond to
  degree-zero primes by contraction and **radical** extension.
- **Finite Rees modules and stable filtrations.** For any ideal `I` in a commutative
  ring `R` and any `R`-module `M`, with independent universes, an
  [`I`-filtration with finitely generated Rees module](GradedRings/ReesModule.lean)
  is stable: `I • F.N n = F.N (n + 1)` for all sufficiently large `n`.
  Neither `I`, the stages, nor `M` need be finitely generated. Conversely,
  [stability from a given degree and finite generation through that degree](GradedRings/ReesModule/FiniteGeneration.lean)
  suffice for finite generation of the Rees module; no finiteness of later stages
  is needed. Both directions use the natural-number filtration and polynomial
  Rees-module constructions.
- **Lattice operations on Rees submodules.** For any ideal `I` of a commutative
  ring `R` and any `R`-module `M`, [Rees-submodule inclusion](GradedRings/ReesModule/Lattice.lean)
  is equivalent to inclusion at every natural filtration stage. The construction
  preserves binary suprema and arbitrary indexed infima and suprema. For a finite
  family whose Rees submodules are finitely generated over `reesAlgebra I`, the
  supremum filtration again has a finitely generated Rees submodule; no finiteness
  of the ideal, individual stages, or ambient module is required.
- **Monic multiplication and polynomial-module evaluation kernels.** Over any
  commutative ring `R` and any `R`-module `M`, multiplication by a monic
  polynomial `g` is injective on `PolynomialModule R M`. For any antitone family
  `P : ℕ → Submodule R M`, the product has degree-`n` coefficient in `P n` for
  every `n` exactly when the source has degree-`n` coefficient in
  `P (n + g.natDegree)`
  ([`monic_smul_coeff_mem_iff`](GradedRings/PolynomialModule/Monic.lean)
  and `monic_smul_injective`). At every `r : R`, a module-valued polynomial
  evaluates to zero exactly when it is `(X - C r) • q`; for `M = R`,
  `equivPolynomialSelf` identifies this factor-existence statement with ordinary
  polynomial divisibility
  ([`eval_eq_zero_iff_exists_smul_X_sub_C`](GradedRings/PolynomialModule/EvaluationKernel.lean)
  and `exists_smul_X_sub_C_eq_iff_dvd`). Ring and module universes are independent;
  no regularity, nontriviality or finiteness hypothesis is needed.
- **Rees-module evaluation and initial-stage finiteness.** For any ideal `I` of
  a commutative ring `R`, any `R`-module `M` and natural `I`-filtration `H`,
  [evaluation at every `r : R`](GradedRings/ReesModule/Evaluation.lean) maps
  `H.submodule` onto the original `H.N 0`, semilinearly along polynomial
  evaluation composed with the Rees-algebra inclusion. The original-`R`-linear
  constant-single map is a section at every point; the maps are natural under
  stage-preserving linear maps. At zero this is the constant-coefficient
  augmentation, and `H.submodule.FG` implies `(H.N 0).FG`. No ideal, stage or
  ambient finiteness, stability or zero-stage normalization is assumed, and
  ring and module universes are independent.
- **Positive Rees augmentation and stability from degree zero.** For any ideal `I`
  of a commutative ring `R`, any `R`-module `M` and natural `I`-filtration `H`, let
  `B = reesAlgebra I`, `E = H.submodule`, and `K₀` be the kernel of the
  constant-coefficient augmentation `B → R`. The
  [coefficient criterion](GradedRings/ReesModule/AugmentationIdeal.lean) says that
  `f : E` belongs to `K₀ • ⊤` exactly when its constant coefficient vanishes and
  its coefficient of degree `n + 1` belongs to `I • H.N n` for every `n`.
  The equality `ker (H.evalRees (0 : R)) = K₀ • ⊤` holds if and only if
  `∀ n, I • H.N n = H.N (n + 1)`, equivalently
  `∀ n, H.N n = I ^ n • H.N 0`. Evaluation retains its original target `H.N 0`;
  the augmentation is to `R`, not `R/I`. Ring and module universes are independent,
  with no finiteness, regularity, completeness, separation or initial-stage
  normalization assumption.
- **Unique successor-tail factors for Rees evaluation kernels.** For any ideal
  `I` of a commutative ring `R`, any `R`-module `M`, any natural `I`-filtration
  `H`, and every `r : R`,
  [`H.mulXSubC r`](GradedRings/ReesModule/EvaluationKernel.lean) is a
  `reesAlgebra I`-linear map from the canonical tail
  `(H.toIntFiltration.natTail (1 : ℤ)).submodule` into `H.submodule`.
  Its underlying value is multiplication by the **ambient** polynomial
  `X - C r`. It is injective, its range is `LinearMap.ker (H.evalRees r)`,
  and every evaluation-zero element has a unique factor in this tail, whose
  degree-`n` coefficient lies in `H.N (n + 1)`. Coefficient and admissible-single
  formulas, compatibility at zero with the existing cutoff transition, and
  naturality under stage-preserving linear maps describe the map. No regularity
  of `r`, ideal/stage/ambient finiteness, stability, separatedness, exhaustivity,
  Noetherianity, flatness or normalization of `H.N 0` is required; ring and
  module universes are independent. The evaluator still lands semilinearly in
  the **original**, possibly proper `H.N 0`, with only an original-`R`-linear
  constant section. This is not a `reesAlgebra I`-linear short exact sequence
  ending there or an ideal-product kernel formula; `X - C r` need not belong
  to the Rees algebra.
- **Finite weighted normal forms for Rees modules.** For any ideal `I` of a
  commutative ring `R` and any `R`-module `M`, a natural `I`-filtration has
  finitely generated Rees module exactly when one finite family of elements
  `x i` and natural weights `w i` satisfies
  `H.N n = ⨆ i, I ^ (n - w i) • span_R {x i}` for every natural `n`
  ([`submodule_fg_iff_exists_weighted_normal_form`](GradedRings/ReesModule/HomogeneousGenerators.lean)).
  Subtraction is truncated natural subtraction. The family may be empty and
  ring and module universes are independent. The
  `exists_fin_generating_family_single_le_of_submodule_fg` construction also
  selects `x i ∈ H.N (w i)` whose singles in all degrees `q ≤ w i` span the
  same Rees module. No finiteness of the ideal, individual stages or ambient
  module, or normalization at degree zero is required. The bounded-degree
  criterion in `GradedRings.ReesModule` gives eventual stability, without ideal
  finiteness. If `I` is finitely
  generated, finite generation of the Rees module is equivalent to finite
  generation of every original-ring stage together with eventual stability
  (`submodule_fg_iff_fg_stable` in the same module).
- **Weighted generators for Rees modules.** A natural filtration satisfies
  `H.N n = ⨆ i, I ^ (n - w i) • span_R {x_i}` for every `n` if and only if its
  [Rees module](GradedRings/ReesModule/FiniteGeneration.lean) is spanned over
  `reesAlgebra I` by `single R q x_i` for every `q ≤ w i`, including zero and
  all intermediate degrees. The characterization allows an arbitrary index type,
  independent of the ring and module universes, with no separate stage-membership
  assumption on the family. A finite index type gives finite generation without
  assuming the ideal, the individual stages, or the ambient module to be finitely
  generated.
- **Integer-filtered associated gradeds and Rees actions.** Over a commutative ring `R`,
  for an antitone family of submodules of an `R`-module `M`,
  `F.N : ℤ → Submodule R M` with `I • F.N n ≤ F.N (n + 1)`, the
  [integer associated graded](GradedRings/FilteredAssociatedGraded.lean) is the
  direct sum of `F.N n` modulo the next stage inside it. It retains the original
  componentwise `R`-module structure and has a surjective coefficientwise
  representative map, with next-stage kernel and a first-isomorphism comparison.
  No finiteness, exhaustivity, separatedness, lower bound or normalization at
  degree zero is required. The [Rees grading](GradedRings/ReesAlgebra/Grading.lean)
  gives the polynomial Rees algebra its degree grading and its coefficient-ideal
  quotient the image grading. On the same associated-graded carrier, the
  [canonical representation](GradedRings/FilteredAssociatedGraded/ReesAction.lean)
  constructs an action of `C = reesAlgebra I ⧸ I.map (algebraMap R (reesAlgebra I))`.
  Constants act by the original `R`-action, and `I` annihilates the carrier.
  For `q : ℕ`, `a ∈ I ^ q` and `m ∈ F.N n`, the class of `aX^q` sends the
  class of `m` to the class of `a • m` in degree `n + q`.
- **Natural Rees and associated-graded finiteness.** For any natural `I`-filtration
  `H` in an `R`-module, if the coefficients `R` are `I`-adically precomplete and
  `⨅ n, H.N n = ⊥`, its original Rees submodule is finitely generated over
  `reesAlgebra I` if and only if the associated graded of its
  [canonical integer extension](GradedRings/ReesModule/AssociatedGraded.lean) is
  finite over `C = reesAlgebra I ⧸ I.map (algebraMap R (reesAlgebra I))`.
  The extension is constant at `H.N 0` in negative degrees. Ring and module
  universes are independent; no ideal, stage or ambient finite generation,
  exhaustivity, normalization at zero or coefficient Hausdorffness is required.
- **Shifted Rees projections.** For every integer cutoff `k`, the
  [natural tail](GradedRings/FilteredAssociatedGraded/ReesProjection.lean) of an
  integer filtration has stages `F.N (k + q)`. Its polynomial Rees submodule
  maps semilinearly to the full associated graded along `B → C`, by summing the
  homogeneous classes of its coefficients. The kernel is the next tail pulled
  back to this source, not generally the coefficient-ideal multiple. Its range
  consists exactly of elements whose components below `k` vanish. If all lower
  pieces vanish, a finite tail over `B` gives a finite associated graded over `C`,
  without ideal finiteness, Noetherianity, completeness or normalization. In
  particular, an exhaustive integer filtration on a finite original module has
  finite associated graded over `C` if, at one common threshold `c`, it is stable
  at and above `c` and its stages at and below `c` are finitely generated.
- **Ideal-adic associated graded comparison.** For any ideal `I` and module `M`, the
  [canonical integer-adic associated graded](GradedRings/FilteredAssociatedGraded/AdicComparison.lean)
  is linearly equivalent over the quotient Rees algebra to
  `Ideal.AssociatedGradedModule I M`, with both original scalar actions retained.
  The map sends homogeneous representatives to polynomial singleton classes;
  coefficients recover the inverse components, and negative components vanish.
  No finiteness, completeness or separatedness assumption is needed. In the regular
  specialization, composition with `(Ideal.AssociatedGradedModule.regularEquiv I).symm`
  identifies it with the quotient Rees algebra and sends the degree-zero unit to `1`.
- **Maps of quotient Rees modules.** For every ideal `I` of a commutative ring
  `R`, an original-`R`-linear map between arbitrary, independently universed
  modules induces a [quotient-Rees-linear map](GradedRings/ReesModule/Map.lean)
  between their `Ideal.AssociatedGradedModule` modules. It applies the polynomial
  module map to each Rees representative, preserves singleton degrees, and
  commutes with each coefficient map via the ordinary quotient by
  `I ^ (q + 1) • ⊤`. Identities and composition are preserved, without finiteness
  or completeness assumptions.
- **Naturality of the ideal-adic comparison.** Every original-`R`-linear map
  `f : M →ₗ[R] N` induces the [canonical integer-adic map](GradedRings/FilteredAssociatedGraded/AdicMap.lean)
  `Ideal.adicAssociatedGradedHom I f`, linear over the existing quotient Rees
  algebra, with representative, component, identity and composition laws.
  The [comparison and its inverse are natural](GradedRings/FilteredAssociatedGraded/AdicComparisonNaturality.lean)
  for this map and the independently defined quotient Rees map: both forward
  routes send `[m]` in degree `q : ℕ` to the old polynomial singleton class
  of `f m` in degree `q`. The original scalar actions and independent module
  universes are retained, with no finiteness, completeness, separatedness or
  nontriviality assumption.
- **Residue-linear integer graded pieces.** For the same arbitrary ideal-compatible
  integer filtration, the [original pieces](GradedRings/FilteredAssociatedGraded/Pieces.lean)
  carry named `R ⧸ I`-module structures compatible with their original `R` actions.
  Insertion and projection are residue-linear for the whole associated graded's
  existing residue action, with the same functions, representative formulas and
  finite reconstruction. Piece modules and towers are activated locally rather
  than registered globally. No residue action on the stages or ambient stage
  quotients, finiteness or degree-zero normalization is required.
- **Maps of integer-filtered associated gradeds.** An original-`R`-linear map
  preserving every stage of two integer filtrations induces a
  [canonical quotient-Rees-linear map](GradedRings/FilteredAssociatedGraded/Map.lean).
  It sends each homogeneous representative to its image, preserves the original
  `R` action, and respects identities and composition. For stage-preserving maps
  `f, g : M →ₗ[R] N` with filtrations `F` and `H`, their induced maps agree exactly
  when `f m - g m ∈ H.N (n + 1)` for every `n : ℤ` and `m ∈ F.N n`
  (`map_eq_iff`). An induced map vanishes exactly when `f m ∈ H.N (n + 1)` for
  all such representatives (`map_eq_zero_iff`), without requiring the original
  map to vanish. It is injective exactly when, for every `n : ℤ` and
  `x ∈ F.N n`, membership `f x ∈ H.N (n + 1)` implies `x ∈ F.N (n + 1)`.
  It is surjective exactly when `H.N n ≤ (F.N n).map f ⊔ H.N (n + 1)` for every
  integer `n`. Thus stagewise pullback equality `F.N n = (H.N n).comap f` gives
  injectivity, and stagewise image equality `(F.N n).map f = H.N n` gives
  surjectivity, without ambient injectivity or surjectivity of `f` or normalization
  at degree zero. A module equivalence carrying
  each filtration stage onto the corresponding stage induces a quotient-Rees-linear
  equivalence, compatibly with inverses, identities and composition. The modules have
  independent universes; no finiteness, exhaustivity, separatedness or lower bound is
  required.
- **Integer translations.** For every integer `d`,
  [translation of an integer filtration](GradedRings/FilteredAssociatedGraded/Shift.lean)
  has stage `(F.shift d).N n = F.N (n + d)`. Its graded-piece equivalence
  preserves representatives, and `shiftEquiv` identifies the whole associated
  gradeds linearly over the canonical quotient Rees algebra, taking degree `n`
  to degree `n + d`. Representative, inclusion, component and residue-scalar
  formulas accompany zero, composition and inverse identities using the
  canonical filtration comparisons. Translation commutes with maps induced by
  stage-preserving `R`-linear maps, both on the whole associated graded and on each
  graded piece. It also commutes with pullback and image filtrations. The induced
  equivalence between the quotients by inclusion ranges commutes with the
  [subquotient equivalence](GradedRings/FilteredAssociatedGraded/SubquotientShift.lean).
  No additional hypotheses are needed.
- **Pullbacks and images of integer filtrations.** Pullback and image along an
  original-`R`-linear map have the submodule inverse images and direct images as
  their integer stages. They preserve ideal compatibility, respect identities
  and composition, and satisfy the stagewise image–preimage universal property.
  The existing canonical associated-graded map is injective from the pullback
  and surjective onto the image, without ambient injectivity or surjectivity.
  No degree-zero normalization, finiteness, exhaustivity, separation, completeness
  or degree bound is imposed.
- **Binary products of integer filtrations.** For any ideal `I` of a commutative
  ring `R` and ideal-compatible integer filtrations `F`, `H` on independently
  universed `R`-modules `M`, `N`, the product has stages `(F.N n).prod (H.N n)`
  on the original `M × N`. Its [associated graded comparison](GradedRings/FilteredAssociatedGraded/Prod.lean)
  is linear over `C = reesAlgebra I ⧸ I.map (algebraMap R (reesAlgebra I))`
  for the canonical actions, with forward map given by the two projections and
  inverse given by the sum of the two inclusions. No degree-zero normalization,
  finiteness, exhaustivity, separatedness, completeness or degree bound is required.
- **Dependent direct sums of integer filtrations.** For an arbitrary family of
  ideal-compatible integer filtrations over a commutative ring, the componentwise
  filtration on the [dependent direct sum](GradedRings/FilteredAssociatedGraded/DirectSum.lean)
  has associated graded canonically equivalent to the direct sum of the associated
  gradeds, linearly over the quotient Rees algebra. Coordinates are the filtered
  component maps; the inverse is assembled from the filtered summand inclusions.
  Homogeneous representatives retain their summand and absolute integer degree,
  naturally under stage-preserving linear maps. The scalar, index and module
  universes are independent. No finite index set, common lower degree bound,
  finiteness, exhaustivity, separatedness or completeness is required.
- **Exactness of integer associated graded maps.** For compatible original
  linear maps `f : M →ₗ[R] N` and `g : N →ₗ[R] P`, the image of the first
  canonical quotient-Rees-linear associated graded map equals the kernel of the
  second exactly when, for every integer `n` and `y ∈ H.N n`, membership
  `g y ∈ K.N (n + 1)` is equivalent to
  `y ∈ (F.N n).map f ⊔ H.N (n + 1)`. The ambient composite need not vanish.
  An ambient exact pair with strict stage images induces an exact pair, without
  ambient injectivity or surjectivity. The three module universes are independent;
  no finiteness, exhaustivity, separatedness, completeness or degree bound is needed.
- **Induced submodules and filtered quotients.** For any submodule `S`, the
  [subquotient equivalence](GradedRings/FilteredAssociatedGraded/Subquotient.lean)
  identifies the associated graded of `F.image S.mkQ` with the quotient of
  `F.AssociatedGraded` by the range of the canonical map from
  `(F.comap S.subtype).AssociatedGraded`, linearly over the quotient Rees algebra.
  The submodule filtration is induced, not intrinsic ideal-adic. Representative
  formulas and the quotient universal property apply in all integer degrees,
  with no finiteness, normalization, separation or completeness hypotheses.
- **Naturality of associated graded subquotients.** For ideal-compatible integer
  filtrations `F`, `H` on independently universed modules over a commutative ring
  `R`, a stage-preserving `R`-linear map `f` with `f(S) ≤ T` commutes with the
  [induced-submodule and quotient maps](GradedRings/FilteredAssociatedGraded/SubquotientNaturality.lean).
  The subquotient equivalences intertwine the quotient-by-range map induced by
  the ambient associated graded map with the associated graded original quotient
  map, over the canonical quotient Rees actions. No strictness, ambient
  injectivity or surjectivity, finiteness or degree bound is required.
- **Nested induced quotients.** For submodules `S ≤ T` of an integer-filtered
  module, the [nested quotient comparison](GradedRings/FilteredAssociatedGraded/NestedQuotient.lean)
  identifies the filtration induced on `T.map S.mkQ` with the image of the
  filtration induced on `T`. The third isomorphism carries every iterated image
  stage onto the direct image stage. On whole associated gradeds, the subquotient
  equivalence for `S` carries the second graded range onto the induced quotient
  range; quotienting twice then agrees with quotienting directly by the `T`
  range, via the third isomorphisms over the original ring and the canonical
  quotient Rees algebra. No finiteness, normalization, exhaustivity, separatedness,
  completeness or splitting is required.
- **Ideal-power quotients and coefficient multiplication.** For any ideal `I` of a
  commutative ring `R` and every natural degree `q`, the
  [quotient of `I ^ q` by its ideal multiple](GradedRings/ReesAlgebra/QuotientPieces.lean)
  has an `R ⧸ I`-linear comparison `quotientMonomialEquivCoefficients` with the
  degree-`q` component of the coefficient-ideal quotient of the Rees algebra.
  Residue scalars are inherited on the same component with its original `R`-action;
  restricting the comparison to `R` recovers `quotientMonomialEquiv`, with the
  same forward and inverse functions. The denominator is exactly the next ideal
  power, viewed inside `I ^ q`. On these same quotient modules,
  [coefficient multiplication](GradedRings/ReesAlgebra/PowerQuotientMultiplication.lean)
  `powerQuotientMul` is bilinear over `R ⧸ I`; `powerQuotientMul_mk` sends `[a]`
  and `[b]` to `[a * b]` in degree `q + r`. Multiplication is commutative and
  associative under the degree-sum identifications,
  with the class of `1` in degree zero as a two-sided unit. The quotient monomial
  maps preserve this multiplication and send that class of `1` to the quotient
  Rees unit. No finiteness, Noetherianity, nontriviality or positive-degree
  assumption is needed.
- **The algebra of ideal-power quotients.** The
  [direct sum of the ideal-power quotients](GradedRings/ReesAlgebra/PowerQuotientAlgebra.lean)
  is an `R ⧸ I`-algebra canonically equivalent to the coefficient-ideal quotient
  of the Rees algebra. It retains componentwise addition and the original `R` and
  `R ⧸ I` actions. Its unit is the degree-zero class of `1`, and homogeneous
  multiplication is `powerQuotientMul`. The equivalence sends each homogeneous
  insertion to its quotient monomial; its inverse decomposes arbitrary elements
  into coefficient classes. No finiteness or nontriviality assumption is needed.
- **Ideal-power quotients acting on integer associated gradeds.** The
  [ideal-power quotient action](GradedRings/FilteredAssociatedGraded/PowerQuotientAction.lean)
  restricts the existing quotient-Rees action along
  `powerQuotientSumAlgEquiv I : D ≃ₐ[R ⧸ I] C`, in the direction `D → C`,
  where `D = reesAlgebra.powerQuotientSum I`. Use
  `powerQuotientSum_of_mk_smul_single` to send `[a]` in degree `q` and `[m]`
  in degree `n` to `[a • m]` in degree `n + q`. The original `R`, `R ⧸ I`
  and `C` actions are unchanged, and both coefficient actions form scalar towers
  with the `D`-action. Quotient-Rees-linear maps and equivalences between
  associated gradeds restrict to `D` using Mathlib's `restrictScalars`
  constructors, with unchanged forward and inverse functions. No additional
  filtration hypotheses are required.
- **Weighted generation of integer filtrations.** For a separated, antitone
  integer-indexed filtration satisfying `I • F n ≤ F (n + 1)` over an
  `I`-adically **precomplete** commutative coefficient ring,
  [finite degree-weighted lifts generating the successive quotients](GradedRings/FilteredModule/WeightedSpan.lean)
  generate every stage with coefficients in `I ^ ((n - d i).toNat)`.
  Ring, module and finite indexing type have independent universes; the family
  may be empty and the degrees may be negative. The
  [finiteness consequences](GradedRings/FilteredModule/Finiteness.lean) keep
  their extra hypotheses separate: eventual stability needs none, finiteness
  of the original module needs exhaustivity, and finite generation of every
  stage needs `I.FG`. The equality and ambient finiteness require neither
  `I.FG` nor a Hausdorff coefficient ring. This independently generalizes the
  filtered lifting ingredient underlying Fujiwara--Kato, *Foundations of Rigid
  Geometry I*, Proposition 0.7.5.2; it is not the full proposition or a full
  associated-graded construction.
- **Finite integer associated gradeds and weighted generators.** For the
  [canonical quotient-Rees action](GradedRings/FilteredAssociatedGraded/FiniteGeneration.lean),
  finiteness of the whole integer associated graded is equivalent to finite
  homogeneous original-module lifts generating every successive quotient with
  ideal-power weights. This algebraic equivalence needs no completeness,
  separation, exhaustivity or finiteness of the ideal. Over an ideal-adically
  precomplete coefficient ring, separation gives exact weighted descriptions
  in every integer degree and eventual stability. Under these two hypotheses,
  finiteness is also equivalent to the existence of a
  [finitely generated natural Rees tail](GradedRings/FilteredAssociatedGraded/ReesFiniteGeneration.lean)
  whose prescribed projection onto the whole associated graded is surjective;
  neither exhaustivity nor finiteness of the ideal or individual stages is needed.
  Exhaustivity additionally gives finiteness of the original module; `I.FG` instead
  gives finite generation of every stage, without exhaustivity. With both exhaustivity
  and `I.FG`, the intrinsic criterion
  `finite_associatedGraded_iff_finite_fg_stable` says that finiteness over the same
  quotient Rees algebra is equivalent to `Module.Finite R M`, finite generation of
  **every original `R`-stage in every integer degree**, and eventual equality
  `I • F.N n = F.N (n + 1)`. No Noetherianity, coefficient Hausdorffness,
  ambient-module precompleteness, degree-zero normalization or chosen top stage is
  required, and the generator family may be empty.
- **Associated graded modules from the first quotient.** For any ideal `I` in a
  commutative ring `R` and any `R`-module `M`, with independent universes,
  [the Rees-quotient associated graded module](GradedRings/ReesModule.lean) `G`
  is finite over `C = B / IB`, where `B = reesAlgebra I`, whenever
  `Q = M / IM` is finite over `R / I`. The canonical map `C ⊗[R/I] Q → G` is
  surjective, **not generally an isomorphism**. More generally, for a subideal
  `K ≤ I` with `IⁿM = KⁿM + Iⁿ⁺¹M` for **every** natural `n`, the canonical
  `reesAlgebra K ⊗[R] Q → G` is surjective without a finiteness hypothesis,
  and `Q` finite over `R / I` makes `G` finite over `reesAlgebra K`, with **no
  finite-generation assumption on K**. If `Q` is Noetherian over `R` and `K` is finitely
  generated, then `G` is Noetherian over `C`. None of these results requires
  finiteness of the original `M`, Noetherianity of `R`, or finite generation of `I`.
- **Quotient Rees augmentation.** For any ideal `I` of a commutative ring `R`,
  [constant coefficient](GradedRings/ReesAlgebra/Augmentation.lean) induces an
  `R/I`-algebra homomorphism from `C = reesAlgebra I / I·reesAlgebra I` to `R/I`.
  The composite `C → R/I → C` is the degree-zero projection, and the image of
  `R/I → C` is exactly the degree-zero component. No finiteness or nontriviality
  assumption is needed; this does not identify the whole ring `C` with `R/I`.
- **The regular associated graded module.** For any ideal `I` of a commutative ring
  `R`, the [regular associated graded module](GradedRings/AssociatedGradedRegular.lean)
  `Ideal.AssociatedGradedModule I R` is canonically free of rank one over
  `C = reesAlgebra I / I·reesAlgebra I`. The equivalence `regularEquiv` sends
  `c` to `c • regularUnit`, where the generator is the degree-zero unit class.
  Rees-representative and every-coefficient formulas, unique scalar expressions,
  and linear-map extensionality expose this comparison without unfolding its
  quotients. No finiteness, completeness, separatedness or nontriviality is assumed.
- **Symmetric algebras and first order.** [Basis-free grading and graded maps](GradedRings/SymmetricAlgebra.lean)
  are functorial for arbitrary modules over a commutative **semiring**; only
  polynomial coordinates need a basis. Over a commutative **ring**, for any
  module `M`, the [augmentation-square quotient and conormal](GradedRings/SymmetricAlgebraSquareZero.lean)
  give `SymmetricAlgebra R M ⧸ augmentationIdeal² ≃ₐ[R] TrivSqZeroExt R M` and
  `augmentationIdeal.Cotangent ≃ₗ[R] M`, without freeness, projectivity or finiteness.
  Generator formulas, ideal transport and both whole-map naturalities use
  `open scoped TrivSqZeroExt` and the released `coherent-modules` kernel
  equivalence. The quotient's image cotangent ideal corresponds to
  `TrivSqZeroExt.kerIdeal`, not the original augmentation ideal; no scheme or sheaf comparison.
- **Prime multiplicity.** A [multiplicative valuation](GradedRings/PrimeMultiplicity.lean)
  measures a prime element in a commutative domain with well-founded divisibility;
  extension to localization requires non-zero-divisor denominators. Its
  [homogeneous restriction](GradedRings/HomogeneousPrimeMultiplicity.lean) uses
  additive commutative monoid degrees. The [polynomial applications](GradedRings/MvPolynomialAway.lean)
  work over a **field**, with arbitrary variables; irreducibility at denominator
  order one uses a positive-degree homogeneous prime polynomial.
- **Whole selected rings, including index zero.** The [Veronese ring](docs/Veronese.md)
  is the external sum of **whole** old components in multiples of `n`, with a
  native grading for every natural `n`. Its [actual zero ring](docs/VeroneseZero.md)
  is equivalent to old degree zero at every index; whole-ring inclusion is
  injective for `n > 0`, but need not be at zero. At zero, old-zero copies occupy
  separate external summands: each factors as a power of the new degree-one variable
  with its arbitrary coefficient in the entire new zero ring. Polynomial
  evaluation is surjective, hence that external sum is finite type over its new
  zero ring, without old-ring finite type, field, domain or nontriviality.
  No polynomial equivalence or source index-zero convention is asserted.
- **Evaluation and homogeneous lifts.** [Weighted evaluation](docs/WeightedEvaluation.md)
  at chosen homogeneous elements of arbitrary natural weights, **including zero**,
  preserves degrees, is a native graded map and commutes with actual components.
  Only lifting **every** homogeneous target element requires the chosen family
  to generate over old degree zero. The [degree-one specialization](docs/HomogeneousLifts.md)
  uses all of `𝒮 1` and exactly `Algebra.adjoin (𝒮 0) (𝒮 1 : Set S) = ⊤`,
  including degree-zero targets. No finite-variable, domain, field or
  nontriviality assumption is needed.
- **Degree-one generation: all versus finite.** Under that old degree-one
  generation hypothesis, [every positive selected index](docs/VeroneseDegreeOne.md)
  is generated by **all** new degree one over its entire actual new zero ring,
  without finite generation. A finite **positive-weight** homogeneous generating
  family over old zero instead gives a [finite new degree-one family](docs/FiniteVeronese.md)
  at `D = Finsupp.weightedBlockSize w`; native old-zero finite type gives **some**
  positive index. These need no field, domain, nontriviality, equal weights or
  Noetherianity; the finite-family conclusions are not all-index claims.
- **Positive-weight blocks and monomial adjoin.** For finite indices and strictly
  positive natural weights, [exponent decomposition](docs/WeightedBlocks.md)
  recovers a whole finitely supported natural exponent vector of weight `k * D`
  as **exactly `k`** weight-`D` blocks, with positive, not necessarily minimal
  `D = max 1 (Fintype.card ι) * ∏ i, w i`. Over any commutative **semiring**,
  [monomial-adjoin membership](docs/WeightedBlockAdjoin.md) puts weight-`k * D`
  polynomials in the coefficient subalgebra generated by coefficient-one
  weight-`D` monomials, including arbitrary coefficients and `k = 0`.
  Neither result alone gives polynomial factorization or whole-ring generation.
- **Selected weighted-polynomial components.** For finite variables, arbitrary
  natural weights **including zero**, any commutative **semiring**, and each
  prescribed `n > 0`, [one finite homogeneous family](docs/WeightedVeroneseGenerators.md)
  generates **all** polynomial degrees divisible by `n` over the entire
  coefficient semiring—not whole selected-ring finite type or degree-one generation.
- **Finite type at each positive index.** Finite homogeneous generators of
  arbitrary natural weights over entire old zero, or native old-zero finite
  type, make [every prescribed positive whole selected ring](docs/VeroneseFiniteType.md)
  finite type over its **entire actual new zero ring**. No domain, nontriviality,
  field, Noetherianity, positive or equal weights are required. This is distinct
  from index-zero finite type and from degree-one generation at every index.
- **Finite inclusion and whole-ring residue modules.** Under old-zero finite
  type, the [inclusion at each `n > 0`](docs/VeroneseFinite.md) makes the **old ring**
  finite over the whole external selected ring via the actual `inclusion.toAlgebra`.
  For `n > 0`, `r < n`, the [residue projection](docs/VeroneseResidue.md) is linear
  for that same action and has exactly the elements supported in residue `r`
  as its range. Ambient module finiteness makes this image finite; old-zero
  finite type suffices. The [shifted sum](docs/VeroneseResidueModule.md)
  `⨁ k, 𝒮 (n * k + r)` has whole selected-ring convolution; coefficient evaluation
  is linear and injective for `n > 0` and **any** `r`, and identifies the projection
  range when also `r < n`. Ambient finiteness, or full old-zero finite type,
  transports under those positive reduced-index bounds. No individual-fiber
  whole-ring action, arbitrary-submodule finiteness or zero-index bijection follows.
- **Coherent high tails.** [Tail equivalence](docs/CoherentTailVeronese.md) requires
  `N > 0`, an actual zero-ring equivalence, additive equivalences in **all**
  degrees at least `N`, and coefficient/high-product compatibility. For `N ≤ n`
  it identifies the **entire** selected rings with native degree-preserving
  inverse maps; for `n > 0`, `selected_zero` is the exact coefficient square.
  No maps across missing original low degrees or Proj/scheme equivalence follow.

## Find an interface

The [canonical module/interface map](docs/API.md#production-modules) merges
precise assumptions with declaration names and direct imports. Its
[scope distinctions](docs/API.md#scope-distinctions) separate full localizations
from degree-zero pieces, polynomial components from whole selected rings, and
algebraic results from geometric claims. The [subject guides](docs/README.md)
provide focused explanations and clients.

### Integer-filtration interfaces

[`FilteredAssociatedGraded`](GradedRings/FilteredAssociatedGraded.lean) provides
`Ideal.IntFiltration I M`, its direct-sum associated graded and the representative
quotient API. [`FilteredAssociatedGraded.ReesAction`](GradedRings/FilteredAssociatedGraded/ReesAction.lean)
adds the canonical quotient-Rees action, with the original `R`-action fixed.
The representative first-isomorphism comparison concerns this direct-sum
construction, not an identification with the natural ideal-adic Rees-module quotient.

[`FilteredAssociatedGraded.Map`](GradedRings/FilteredAssociatedGraded/Map.lean)
constructs maps for the same ideal `I`. An `R`-linear map `f` between the original
modules need only send `F.N n` into `H.N n` for **every integer** `n`.
`F.map H f hf` is linear over the same quotient-Rees coefficient ring, using
the canonical actions, and has representative, identity and composition formulas.
Stage preservation is an inclusion, not an equality or surjectivity condition.

[`FilteredAssociatedGraded.AdicMap`](GradedRings/FilteredAssociatedGraded/AdicMap.lean)
provides `Ideal.adicAssociatedGradedHom I f` without a separate stage-preservation
argument: the stock ideal-smul inclusion preserves `I ^ n.toNat • ⊤` in every
integer degree. Its singleton and component formulas specialize the generic map;
identities and composition are preserved.
[`FilteredAssociatedGraded.AdicComparisonNaturality`](GradedRings/FilteredAssociatedGraded/AdicComparisonNaturality.lean)
exports `adicAssociatedGradedEquiv_naturality`, its inverse square
`adicAssociatedGradedEquiv_symm_naturality`, and the natural-degree endpoint
`adicAssociatedGradedEquiv_hom_single`. The existing comparison
`Ideal.adicAssociatedGradedMap` is distinct from the map induced by `f`.

[`FilteredAssociatedGraded.ReesProjection`](GradedRings/FilteredAssociatedGraded/ReesProjection.lean)
provides `F.natTail k`, `F.natTailSingle k q m`, and the coefficient-support-sum
map `F.shiftedReesProjection k`. Singleton values characterize that semilinear map;
component, next-tail-kernel, exact range and finite-image theorems use the original
polynomial and associated-graded carriers with their existing actions.

[`ReesModule.Map`](GradedRings/ReesModule/Map.lean) also provides
`E.reesMap L f hf` for arbitrary natural ideal filtrations and stage-preserving
`R`-linear maps. Every coefficient is sent through `f`, with singleton, identity
and composition formulas. Its [range](GradedRings/ReesModule/Range.lean) consists
exactly of target elements whose degree-`q` coefficient lies in `(E.N q).map f`
for every natural `q`; it is surjective exactly when `(E.N q).map f = L.N q` for
every `q`, without requiring ambient surjectivity or stage-zero normalization.
Its [kernel](GradedRings/ReesModule/Kernel.lean) consists exactly of source elements whose every coefficient lies in the kernel of the original linear map. The Rees map is injective exactly when that linear map restricted to the degree-zero source stage is injective; ambient injectivity is not required. For two composable stage-preserving maps `f` and `g`, [exactness](GradedRings/ReesModule/Exactness.lean) of their induced Rees maps is equivalent to `(E.N q).map f = L.N q ⊓ LinearMap.ker g` for every natural `q`, where `E` and `L` are the source and middle filtrations. This describes exactness at the filtered middle and does not require ambient `g ∘ f = 0`.
At any common integer cutoff, these maps commute with
the prescribed shifted projections and the existing map on full integer associated
gradeds, as [semilinear maps along the same quotient of the Rees algebra](GradedRings/FilteredAssociatedGraded/ReesProjectionNaturality.lean).

[`ReesTransition`](GradedRings/FilteredAssociatedGraded/ReesTransition.lean)
provides injective cutoff transitions `F.natTailTransition k l hkl` for `k ≤ l`.
They multiply the underlying polynomial by `X ^ (l - k).toNat`, preserving each
coefficient's integer filtration degree. The multiplying polynomial need not
belong to the Rees algebra.
The transitions preserve identities and composition, commute with the prescribed
shifted projections, and are natural for stage-preserving linear maps.

[`ReesModule.EvaluationKernel`](GradedRings/ReesModule/EvaluationKernel.lean)
uses the existing transition from tail one to tail zero and coefficientwise
identity Rees maps to define `H.mulXSubC r`, rather than a new tail or shift.
The [polynomial-module monic](GradedRings/PolynomialModule/Monic.lean) and
[ambient evaluation-kernel](GradedRings/PolynomialModule/EvaluationKernel.lean)
interfaces are independent of filtrations and Rees modules. All three leaves
are publicly exported by `GradedRings`; their detailed formulas and scalar
conventions are in the [API map](docs/API.md#polynomial-modules-and-rees-evaluation-kernels).

[Residue coefficients](GradedRings/FilteredAssociatedGraded/Coefficients.lean)
act on the same whole associated graded by restricting the canonical quotient-Rees
action along `R/I → C`; residue representatives act by the original `R`-action.

The [weighted lifting](GradedRings/FilteredModule/WeightedSpan.lean) and
[finiteness](GradedRings/FilteredModule/Finiteness.lean) interfaces take finite
weighted lifts and generation in **every** successive quotient as hypotheses.
The [finite-generation bridge](GradedRings/FilteredAssociatedGraded/FiniteGeneration.lean)
derives those finite weighted generators from finiteness of the constructed
associated graded over its canonical quotient-Rees ring, without completeness or
separation. Applying the lifting consequences then requires precomplete coefficients
and a separated filtration, with exhaustivity or `I.FG` added for the distinct
ambient-module or stage-finiteness conclusions in the headlines. These interfaces,
including the [Rees grading](GradedRings/ReesAlgebra/Grading.lean), are exported by
`GradedRings`.

[`FilteredAssociatedGraded.ReesFiniteGeneration`](GradedRings/FilteredAssociatedGraded/ReesFiniteGeneration.lean)
converts a supplied all-integer weighted stage formula into a natural-tail formula
at any cutoff `k` below every weight. The relative weights are `(d i - k).toNat`,
and the ideal powers use natural subtraction. It also gives `F.N n = F.N k` for
every `n ≤ k`. These algebraic lemmas allow arbitrary, possibly empty indexing
families and require no finiteness, completeness, separation or exhaustivity.
For precomplete coefficients and a separated filtration, the same module supplies
`finite_associatedGraded_iff_exists_fg_natTail`, retaining the projection-surjectivity
condition. With exhaustivity and `I.FG`, use
`F.finite_associatedGraded_iff_finite_fg_stable hI hsep hexhaustive` to pass in either
direction between finite associated graded over the fixed quotient Rees algebra and
finite original module, all-integer original-stage FG, and eventual ideal stability.
The theorem takes no finite-associated-graded instance as a hypothesis.

## Build and use

Install the exact toolchain in `lean-toolchain`: Lean `v4.34.0-rc2`.
The direct dependencies are mathlib at
`83abb3e776bdefcbc447a1e44d0debe4010039e5` and the released
`coherent-modules` at `1dfe73a0d8d506a7871d5393e274582d36161265`;
`lake-manifest.json` freezes all ten resolved Git dependencies. From a checkout, obtain matching compiled
mathlib artifacts **before** building:

```sh
lake exe cache get
lake --wfail build
```

Do not replace the manifest or substitute a moving mathlib branch. The default
build includes the aggregate library, all regression-test modules and
the five stored examples. Named targets are also available:

```sh
lake --wfail build GradedRings GradedRingsTests GradedRingsExamples
lake --wfail build QuotientLocalization FinitenessAndPrimes Symmetric Multiplicity
```

All shipped Lean modules use Lean's module system. Ordinary-import
`GradedRings` for the full API, or a `GradedRings.<Leaf>` module from the
[API map](docs/API.md#production-modules). Public imports re-export the intended
interfaces; clients need neither `import all` nor private names. The selected-ring
leaf also exports its named technical grading and reindexing helpers, but the main
API does not require clients to use them.

The quotient, localization and prime-multiplicity tests compare full public
constructions with their original constructions by Lean-private ordinary-import
`rfl` equalities. This checks computation as well as availability of theorem
names. Ordinary builds check proofs; named axiom prints in tests/examples
complement, but do not replace, the complete transitive standard-axiom audit
including private and generated declarations.

### Build resources

Build time and memory depend on the targets, cache state, network and hardware.
These instructions specify neither a cold-build time nor a minimum-memory
guarantee. Leave headroom for Lake, dependencies and documentation generation;
`LAKE_JOBS` and `LEAN_NUM_THREADS` settings alone should not be treated as enforced
aggregate process, thread or memory bounds.

## Complete examples

Each link is a complete native module with its imports and hypotheses, compiled
by `GradedRingsExamples`. These modules demonstrate use of the library.

- [Quotient and localization](examples/QuotientLocalization.lean): quotient-map
  multiplication, recombination of the quotient grading, homogeneous-fraction
  degree membership and the degree-zero equivalence round trip.
- [Finiteness and primes](examples/FinitenessAndPrimes.lean): derive finite type
  and Noetherianity from an irrelevant-ideal generating set, extract positive
  homogeneous generators, and contract after radical extension of a prime.
- [Symmetric algebras](examples/Symmetric.lean): map a product of generators by a
  linear map, preserve homogeneous degree in basis coordinates, and return through
  the inverse coordinate map. The coefficient semiring need not be a field.
- [Multiplicity](examples/Multiplicity.lean): evaluate products of prime powers,
  recognize a unit at maximal numerator multiplicity, and use denominator order
  one to force a unit factor. This file uses the aggregate import.
- [Integer filtrations](examples/GradedRingsExamples/FilteredAssociatedGradedAdic.lean):
  extend the zero-ideal filtration of `2ℤ` while preserving its proper initial
  stage and nonzero degree-zero class; exhibit a general integer filtration
  with a nonzero degree-`-2` piece, which no such natural extension can have.

## Proof ideas

The [API guide](docs/API.md#proof-ideas) outlines the quotient/localization,
finite-generation, Noetherian, prime-correspondence and symmetric-algebra arguments.

## References and credit

Ravi Vakil, *The Rising Sea: Foundations of Algebraic Geometry*, October 21, 2025
draft, exercises around 4.5.F–H and 5.4.N motivate several constructions.
Section 7.4.4, Exercise 7.4.D motivates the selected-component Veronese ring;
this library supplies its algebraic ring layer, not the Proj isomorphism.
Section 7.4.4, Exercise 7.4.E (printed page 215; degree-zero coefficient
convention in §4.5.6, pp. 151–152) motivates homogeneous polynomial lifts
and positive-Veronese degree-one generation under old-ring generation. The
library does not supply coefficient regrouping or chart/Proj invariance.
The basis-free symmetric algebra also supports projective-space applications.

For background on the Rees and associated-graded algebra/module constructions
in [`ReesAlgebra`](GradedRings/ReesAlgebra.lean) and
[`ReesModule`](GradedRings/ReesModule.lean), see K. Fujiwara and F. Kato,
*Foundations of Rigid Geometry I*,
[arXiv:1308.4734v5](https://arxiv.org/abs/1308.4734v5). This scoped background
reference does not assert exact theorem correspondence or book coverage.

These are mathematical references; no source PDF, figures or substantial source
prose is distributed.

Lean and mathlib supply the foundational APIs. The finite homogeneous Rees
family uses Andrew Yang's filtration and polynomial-module formalizations and
Johan Commelin's finite-span extraction API, with the same all-lower-degree
family as the library's weighted-normal-form formalization. Rees-module
evaluation uses Yang's polynomial evaluation and single maps, the library's
coefficientwise Rees maps, and Commelin's semilinear finite-image API. The monic
coefficient and linear-factor interfaces also use Mathlib's polynomial
monic/division, coefficient and finitely supported function APIs. The natural
kernel presentation reuses the existing canonical tail transitions,
natural-to-integer extension and coefficientwise Rees maps.
Authentic notices
and distinct contributor/adaptation roles are summarized in
[provenance and credits](docs/PROVENANCE.md).

## Natural filtrations and their integer extensions

`GradedRings.FilteredAssociatedGraded.Adic` extends an ideal-compatible natural
filtration `F` of an `R`-module to an integer filtration with stage
`F.N (Int.toNat n)`. Every nonpositive stage remains `F.N 0`; the construction
does not require the filtration to start at the whole module. Its least-extension
property compares stagewise inclusions with arbitrary integer filtrations.

At every natural degree, including zero, the associated graded piece is canonically
`R`-linearly equivalent to the quotient of `F.N q` by the pullback of `F.N (q+1)`.
This equivalence preserves quotient representatives. Negative pieces of these
extensions vanish, while general integer filtrations may have nonzero negative
pieces. The ideal-adic extension specializes the stable filtration of the whole
module and has stages `I ^ (Int.toNat n) • ⊤`.
