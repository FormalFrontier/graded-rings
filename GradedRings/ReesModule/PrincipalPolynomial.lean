/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Module.Submodule.Pointwise
public import Mathlib.Algebra.Module.Submodule.RestrictScalars
public import Mathlib.Algebra.Polynomial.Module.Basic
public import Mathlib.Algebra.Regular.SMul
public import Mathlib.LinearAlgebra.Finsupp.LSum
public import GradedRings.ReesAlgebra.QuotientPieces
public import GradedRings.ReesModule

/-!
# Polynomial coordinates for a principal-ideal associated graded module

For a principal ideal `I = Ideal.span {a}`, the coefficient quotient
`Q = M ⧸ (I • ⊤)` maps in degree `q` to the class of the Rees-module singleton
with coefficient `a ^ q • m`. Extending these maps by the universal property of
finitely supported functions gives an `R ⧸ I`-linear map from
`PolynomialModule (R ⧸ I) Q` to `Ideal.AssociatedGradedModule I M`.

The target is the quotient Rees module with its quotient Rees ring action. Its
coefficient action is restriction along the canonical algebra map. The comparison
map is surjective without a regularity hypothesis. If scalar multiplication by
`a` is injective on `M`, it gives a linear equivalence. No regularity hypothesis
on `R` is needed.

## References

* Mathlib's `Finsupp.lsum` extends the family of homogeneous coefficient maps.
* Mathlib's `PolynomialModule.coeffLinearEquiv` identifies polynomial modules
  with finitely supported coefficient functions.
-/

public section

universe u v

namespace Ideal.AssociatedGradedModule

/-- Membership in a power of a principal ideal times the whole module is divisibility by
that power of the generator. -/
private theorem mem_span_singleton_pow_smul_top_iff
    {R : Type u} [CommSemiring R] {M : Type v} [AddCommMonoid M] [Module R M]
    (a : R) (q : ℕ) (m : M) :
    m ∈ (Ideal.span ({a} : Set R)) ^ q • (⊤ : Submodule R M) ↔
      ∃ x : M, a ^ q • x = m := by
  rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists]
  simp only [Submodule.mem_top, true_and]

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

section Principal

variable (a : R)

local notation "I" => Ideal.span (Singleton.singleton a : Set R)
local notation "A" => R ⧸ I
local notation "Q" => M ⧸ (I • (⊤ : Submodule R M))
local notation "B" => reesAlgebra I
local notation "J" => Ideal.map (algebraMap R B) I
local notation "S" => Ideal.Filtration.submodule (Ideal.stableFiltration I (⊤ : Submodule R M))
local notation "D" => J • (⊤ : Submodule B S)
local notation "N" => Ideal.AssociatedGradedModule I M

private theorem principalPower_smul_mem (q : ℕ) (m : M) :
    a ^ q • m ∈ I ^ q • (⊤ : Submodule R M) := by
  apply Submodule.smul_mem_smul
  · rw [Ideal.span_singleton_pow]
    exact Ideal.subset_span (by simp)
  · exact Submodule.mem_top

/-- Membership in the denominator is the image of multiplication by the generator,
using the scalar action inherited from the Rees module. -/
private theorem mem_principalDenominator_iff (p : S) :
    p ∈ D ↔ ∃ s : S, a • s = p := by
  rw [Ideal.map_span, Set.image_singleton, Submodule.ideal_span_singleton_smul]
  simpa only [Submodule.mem_top, true_and, IsScalarTower.algebraMap_smul] using
    (Submodule.mem_smul_pointwise_iff_exists p (algebraMap R B a)
      (⊤ : Submodule B S))

/-- A degree-`q` denominator coefficient has one more principal-ideal factor
than a coefficient of the Rees module. -/
private theorem principalDenominator_coeff_exists (p : S) (hp : p ∈ D) (q : ℕ) :
    ∃ m : M, a ^ (q + 1) • m = (p : PolynomialModule R M).coeff q := by
  obtain ⟨s, rfl⟩ := (mem_principalDenominator_iff (M := M) a p).mp hp
  obtain ⟨m, hm⟩ :=
    (mem_span_singleton_pow_smul_top_iff (M := M) a q
      ((s : PolynomialModule R M).coeff q)).mp (s.property q)
  refine ⟨m, ?_⟩
  rw [Submodule.coe_smul_of_tower]
  change a ^ (q + 1) • m =
    ((PolynomialModule.coeffLinearEquiv R R) (a • (s : PolynomialModule R M))) q
  rw [map_smul]
  change a ^ (q + 1) • m = a • (s : PolynomialModule R M).coeff q
  rw [pow_succ', mul_smul, hm]

private theorem principalDenominator_coeff_mem (p : S) (hp : p ∈ D) (q : ℕ) :
    (p : PolynomialModule R M).coeff q ∈ I ^ (q + 1) • (⊤ : Submodule R M) := by
  obtain ⟨m, hm⟩ := principalDenominator_coeff_exists (M := M) a p hp q
  rw [← hm]
  exact principalPower_smul_mem a (q + 1) m

private noncomputable def principalReesSingle (q : ℕ) : M →ₗ[R] S :=
  let weightedSingle : M →ₗ[R] PolynomialModule R M :=
    (PolynomialModule.lsingle R q).comp
      (a ^ q • (LinearMap.id : M →ₗ[R] M))
  LinearMap.codRestrict (Submodule.restrictScalars R S) weightedSingle
    (fun m => single_mem I M q (a ^ q • m) (principalPower_smul_mem a q m))

private noncomputable def principalSingle (q : ℕ) : M →ₗ[R] N :=
  ((mk I M).restrictScalars R).comp (principalReesSingle (M := M) a q)

private theorem principalSingle_apply (q : ℕ) (m : M) :
    principalSingle a q m =
      mk I M
        ⟨PolynomialModule.single R q (a ^ q • m),
          single_mem I M q (a ^ q • m) (principalPower_smul_mem a q m)⟩ := by
  rfl

private theorem principalSingle_le_ker (q : ℕ) :
    I • (⊤ : Submodule R M) ≤ LinearMap.ker (principalSingle (M := M) a q) := by
  apply Submodule.smul_le.mpr
  intro r hr m _
  change principalSingle a q (r • m) = 0
  rw [map_smul]
  have hrA : Ideal.Quotient.mk I r = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hr
  have hrC : algebraMap R (B ⧸ J) r = 0 := by
    rw [IsScalarTower.algebraMap_apply R A (B ⧸ J)]
    change algebraMap A (B ⧸ J) (Ideal.Quotient.mk I r) = 0
    rw [hrA, map_zero]
  calc
    r • principalSingle a q m =
        (algebraMap R (B ⧸ J) r) • principalSingle a q m :=
      (IsScalarTower.algebraMap_smul (B ⧸ J) r (principalSingle a q m)).symm
    _ = 0 := by
      rw [hrC]
      exact zero_smul (B ⧸ J) (principalSingle a q m)

private noncomputable def principalCoefficientR (q : ℕ) : Q →ₗ[R] N :=
  (I • (⊤ : Submodule R M)).liftQ (principalSingle a q) (principalSingle_le_ker a q)

private noncomputable def principalCoefficient (q : ℕ) : Q →ₗ[A] N :=
  (principalCoefficientR a q).extendScalarsOfSurjective Ideal.Quotient.mk_surjective

/-- The coefficient-linear polynomial map to the associated graded module of a
principal ideal. In degree `q`, a coefficient class represented by `m` is sent to
the quotient Rees class of the singleton with coefficient `a ^ q • m`. -/
noncomputable def principalPolynomialHom : PolynomialModule A Q →ₗ[A] N :=
  (Finsupp.lsum A (fun q => principalCoefficient (M := M) a q)).comp
    (PolynomialModule.coeffLinearEquiv A A).toLinearMap

/-- On a singleton with a represented coefficient, the polynomial map is the
class of the Rees-module singleton, with its principal-ideal weight. -/
@[simp]
theorem principalPolynomialHom_single (q : ℕ) (m : M) :
    principalPolynomialHom a
        (PolynomialModule.single A q (Submodule.Quotient.mk m : Q)) =
      mk I M
        ⟨PolynomialModule.single R q (a ^ q • m),
          single_mem I M q (a ^ q • m) (by
            apply Submodule.smul_mem_smul
            · rw [Ideal.span_singleton_pow]
              exact Ideal.subset_span (by simp)
            · exact Submodule.mem_top)⟩ := by
  change (Finsupp.lsum A (fun n => principalCoefficient (M := M) a n))
      ((PolynomialModule.single A q (Submodule.Quotient.mk m : Q)).coeff) = _
  rw [PolynomialModule.coeff_single, Finsupp.lsum_single]
  exact principalSingle_apply a q m

private theorem polynomialModule_sum_single (p : PolynomialModule R M) :
    ∑ q ∈ p.coeff.support, PolynomialModule.single R q (p.coeff q) = p := by
  apply (PolynomialModule.coeffLinearEquiv R R).injective
  change (∑ q ∈ p.coeff.support, PolynomialModule.single R q (p.coeff q)).coeff = p.coeff
  rw [PolynomialModule.coeff_sum]
  simpa only [PolynomialModule.coeff_single, Finsupp.sum] using Finsupp.sum_single p.coeff

private theorem exists_principalPolynomialHom_preimage_mk (p : S) :
    ∃ f : PolynomialModule A Q, principalPolynomialHom a f = mk I M p := by
  classical
  have hcoeff (q : ℕ) : ∃ m : M, a ^ q • m = (p : PolynomialModule R M).coeff q := by
    apply (mem_span_singleton_pow_smul_top_iff a q _).mp
    exact ((Ideal.stableFiltration I (⊤ : Submodule R M)).mem_submodule _).1 p.property q
  choose c hc using hcoeff
  let s : ℕ → S := fun q =>
    ⟨PolynomialModule.single R q (a ^ q • c q),
      single_mem I M q (a ^ q • c q) (principalPower_smul_mem a q (c q))⟩
  let f : PolynomialModule A Q :=
    ∑ q ∈ (p : PolynomialModule R M).coeff.support,
      PolynomialModule.single A q (Submodule.Quotient.mk (c q) : Q)
  have hs : (∑ q ∈ (p : PolynomialModule R M).coeff.support, s q) = p := by
    apply Subtype.ext
    change (Submodule.subtype S) (∑ q ∈ (p : PolynomialModule R M).coeff.support, s q) = _
    rw [map_sum]
    change (∑ q ∈ (p : PolynomialModule R M).coeff.support,
      PolynomialModule.single R q (a ^ q • c q)) = (p : PolynomialModule R M)
    simp_rw [hc]
    exact polynomialModule_sum_single (p : PolynomialModule R M)
  refine ⟨f, ?_⟩
  calc
    principalPolynomialHom a f =
        ∑ q ∈ (p : PolynomialModule R M).coeff.support, mk I M (s q) := by
      simp only [f, map_sum]
      apply Finset.sum_congr rfl
      intro q _
      exact principalPolynomialHom_single a q (c q)
    _ = mk I M (∑ q ∈ (p : PolynomialModule R M).coeff.support, s q) :=
      (map_sum (mk I M) _ _).symm
    _ = mk I M p := congrArg (mk I M) hs

/-- Every class in the associated graded module of a principal ideal has a
polynomial representative with coefficients in the degree-zero quotient. -/
theorem principalPolynomialHom_surjective :
    Function.Surjective (principalPolynomialHom (M := M) a) := by
  have hpre (p : S) : ∃ f : PolynomialModule A Q,
      principalPolynomialHom (M := M) a f = mk I M p :=
    exists_principalPolynomialHom_preimage_mk (R := R) (M := M) a p
  intro z
  refine Quot.inductionOn z ?_
  intro p
  obtain ⟨f, hf⟩ := hpre p
  exact ⟨f, hf.trans (mk_apply I M p)⟩

private theorem principalPolynomialHom_lift (p : PolynomialModule A Q) :
    ∃ s : S, mk I M s = principalPolynomialHom a p ∧
      ∀ q : ℕ, ∃ m : M, (Submodule.Quotient.mk m : Q) = p.coeff q ∧
        (s : PolynomialModule R M).coeff q = a ^ q • m := by
  induction p using PolynomialModule.induction_linear with
  | zero =>
      refine ⟨0, ?_, ?_⟩
      · exact (map_zero (mk I M)).trans
          (map_zero (principalPolynomialHom (M := M) a)).symm
      · intro q
        exact ⟨0, by simp, by simp⟩
  | add p p' hp hp' =>
      obtain ⟨s, hs, hcoeff⟩ := hp
      obtain ⟨s', hs', hcoeff'⟩ := hp'
      refine ⟨s + s', by simp only [map_add, hs, hs'], ?_⟩
      intro q
      obtain ⟨m, hm, hsm⟩ := hcoeff q
      obtain ⟨m', hm', hsm'⟩ := hcoeff' q
      refine ⟨m + m', ?_, ?_⟩
      · change (Submodule.Quotient.mk m : Q) + Submodule.Quotient.mk m' =
          p.coeff q + p'.coeff q
        rw [hm, hm']
      · change (s : PolynomialModule R M).coeff q +
          (s' : PolynomialModule R M).coeff q = a ^ q • (m + m')
        rw [hsm, hsm', smul_add]
  | single n z =>
      refine Submodule.Quotient.induction_on (I • (⊤ : Submodule R M)) z ?_
      intro m
      refine ⟨⟨PolynomialModule.single R n (a ^ n • m),
        single_mem I M n (a ^ n • m) (principalPower_smul_mem a n m)⟩,
        (principalPolynomialHom_single a n m).symm, ?_⟩
      intro q
      by_cases h : n = q
      · subst q
        exact ⟨m, by simp, by simp⟩
      · exact ⟨0, by simp [Ne.symm h], by simp [Ne.symm h]⟩

private theorem principalCoefficient_quotient_eq_zero
    (ha : IsSMulRegular M a) (q : ℕ) (m : M)
    (hm : a ^ q • m ∈ I ^ (q + 1) • (⊤ : Submodule R M)) :
    (Submodule.Quotient.mk m : Q) = 0 := by
  obtain ⟨x, hx⟩ := (mem_span_singleton_pow_smul_top_iff a (q + 1) (a ^ q • m)).mp hm
  have hxm : a • x = m := (IsSMulRegular.pow q ha) (by
    simpa only [pow_succ, mul_smul] using hx)
  change m ∈ LinearMap.ker ((I • (⊤ : Submodule R M)).mkQ)
  rw [(I • (⊤ : Submodule R M)).ker_mkQ, ← hxm]
  simpa only [pow_one] using principalPower_smul_mem a 1 x

/-- The principal-ideal polynomial map is injective when the generator acts
regularly on the module. No regularity assumption on the coefficient ring is needed. -/
theorem principalPolynomialHom_injective (ha : IsSMulRegular M a) :
    Function.Injective (principalPolynomialHom (M := M) a) := by
  intro p p' h
  have hz : principalPolynomialHom a (p - p') = 0 := by
    rw [map_sub, h, sub_self]
  obtain ⟨s, hs, hcoeff⟩ := principalPolynomialHom_lift a (p - p')
  have hmem : s ∈ D := by
    let _ : AddCommGroup S := Module.addCommMonoidToAddCommGroup R
    change s ∈ (D).restrictScalars R
    rw [← ((D).restrictScalars R).ker_mkQ]
    exact (mk_apply I M s).symm.trans (hs.trans hz)
  have hzero : p - p' = 0 := by
    apply PolynomialModule.coeff_injective
    ext q
    change (p - p').coeff q = 0
    obtain ⟨m, hm, hsm⟩ := hcoeff q
    rw [← hm]
    apply principalCoefficient_quotient_eq_zero a ha q m
    rw [← hsm]
    exact principalDenominator_coeff_mem (M := M) a s hmem q
  exact sub_eq_zero.mp hzero

/-- Polynomial coordinates for the associated graded module when the principal
ideal generator acts regularly on the module. -/
@[expose] noncomputable def principalPolynomialEquiv (ha : IsSMulRegular M a) :
    PolynomialModule A Q ≃ₗ[A] N :=
  LinearEquiv.ofBijective (principalPolynomialHom a)
    ⟨principalPolynomialHom_injective a ha, principalPolynomialHom_surjective a⟩

/-- The underlying linear map of the principal coordinate equivalence is the
principal polynomial comparison. -/
@[simp] theorem principalPolynomialEquiv_toLinearMap (ha : IsSMulRegular M a) :
    (principalPolynomialEquiv a ha).toLinearMap = principalPolynomialHom a := rfl

/-- The coordinate equivalence has the principal polynomial comparison as its
forward map. -/
@[simp] theorem principalPolynomialEquiv_apply (ha : IsSMulRegular M a)
    (p : PolynomialModule A Q) :
    principalPolynomialEquiv a ha p = principalPolynomialHom a p := rfl

/-- A homogeneous represented coefficient maps to its weighted Rees class. -/
theorem principalPolynomialEquiv_single (ha : IsSMulRegular M a)
    (q : ℕ) (m : M) :
    principalPolynomialEquiv a ha
        (PolynomialModule.single A q (Submodule.Quotient.mk m : Q)) =
      mk I M
        ⟨PolynomialModule.single R q (a ^ q • m),
          single_mem I M q (a ^ q • m) (by
            apply Submodule.smul_mem_smul
            · rw [Ideal.span_singleton_pow]
              exact Ideal.subset_span (by simp)
            · exact Submodule.mem_top)⟩ := by
  simpa only [principalPolynomialEquiv_apply] using principalPolynomialHom_single a q m

/-- The inverse coordinate equivalence reads a weighted homogeneous Rees class
as the corresponding residue coefficient. -/
theorem principalPolynomialEquiv_symm_apply_mk_single
    (ha : IsSMulRegular M a) (q : ℕ) (m : M) :
    (principalPolynomialEquiv a ha).symm
        (mk I M
          ⟨PolynomialModule.single R q (a ^ q • m),
            single_mem I M q (a ^ q • m) (by
              apply Submodule.smul_mem_smul
              · rw [Ideal.span_singleton_pow]
                exact Ideal.subset_span (by simp)
              · exact Submodule.mem_top)⟩) =
      PolynomialModule.single A q (Submodule.Quotient.mk m : Q) := by
  apply (principalPolynomialEquiv a ha).injective
  rw [LinearEquiv.apply_symm_apply, principalPolynomialEquiv_single]

/-- The inverse polynomial coordinates of a singleton quotient class are its residue
coefficient. -/
@[simp] theorem principalPolynomialEquiv_symm_apply_quotient_mk_single
    (ha : IsSMulRegular M a) (q : ℕ) (m : M) :
    (principalPolynomialEquiv a ha).symm
        (Submodule.Quotient.mk
          ⟨PolynomialModule.single R q (a ^ q • m),
            single_mem I M q (a ^ q • m) (by
              apply Submodule.smul_mem_smul
              · rw [Ideal.span_singleton_pow]
                exact Ideal.subset_span (by simp)
              · exact Submodule.mem_top)⟩) =
      PolynomialModule.single A q (Submodule.Quotient.mk m : Q) := by
  simpa only [mk_apply] using principalPolynomialEquiv_symm_apply_mk_single a ha q m

end Principal

end Ideal.AssociatedGradedModule
