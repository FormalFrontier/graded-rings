/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GradedRings.PolynomialModule.Basic
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.RingTheory.Finiteness.Basic
import GradedRings.PolynomialModule.Pi
public import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Algebra.Polynomial.Coeff

/-!
# Finiteness of polynomial modules

Extension to polynomial scalars preserves and reflects finite generation over a
possibly noncommutative semiring. A finite generating set for the coefficient
module gives generators in degree zero, and multiplication by monomials generates
all other degrees. Conversely, taking the constant coefficient is a surjective
semilinear map along `Polynomial.constantCoeff`.

Polynomial extension also preserves finite presentation in the finite-subset,
zero-kernel sense of `Module.FinitePresentation`. The proof extends the chosen
coefficient generators in degree zero and transports their finitely generated
zero kernel through the finite free comparison. No additive cancellation or
change-of-generators principle is used. When the coefficient module is an additive
commutative group, polynomial extension also reflects this finite-subset,
zero-kernel notion of finite presentation. A chosen finite polynomial generating subset
whose linear-combination kernel is bottom also descends by coefficient sum to a finite
coefficient generating subset with bottom linear-combination kernel, without an additive
group hypothesis.

The polynomial action is the one on `PolynomialModule.Extension`: constants act
by the given coefficient action, and the variable acts by successor shift.

For a surjective unit-reflecting homomorphism `f : R →+* S`, finite presentation
of the extension of the regular `S`-module, restricted along `f`, forces the
kernel of `f` to be finitely generated as a left `R`-module. This implication
requires neither commutativity nor additive inverses.
-/

@[expose] public section

universe u v w

open Polynomial

namespace PolynomialModule.Extension

variable {R : Type u} {M : Type v} [rR : Semiring R] [AddCommMonoid M] [Module R M]

private theorem span_image_single_eq_top [DecidableEq (Extension R M)] (s : Finset M)
    (hs : Submodule.span R (s : Set M) = ⊤) :
    Submodule.span R[X]
      ((s.image (single R 0) : Finset (Extension R M)) : Set (Extension R M)) = ⊤ := by
  classical
  let T : Finset (Extension R M) := s.image (single R 0)
  let P : Submodule R[X] (Extension R M) := Submodule.span R[X] (T : Set (Extension R M))
  have hsingle0 (m : M) : single R 0 m ∈ P := by
    have hm : m ∈ Submodule.span R (s : Set M) := by
      rw [hs]
      trivial
    refine Submodule.span_induction
      (p := fun x _ => single R 0 x ∈ P) ?_ ?_ ?_ ?_ hm
    · intro x hx
      apply Submodule.subset_span
      exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
    · simpa only [single_zero] using P.zero_mem
    · intro x y _ _ hx hy
      simpa only [single_add] using P.add_mem hx hy
    · intro r x _ hx
      simpa only [single_smul, C_smul] using P.smul_mem (C r) hx
  apply top_unique
  intro q _
  refine induction_linear q P.zero_mem (fun x y hx hy => P.add_mem hx hy) ?_
  intro n m
  simpa only [monomial_smul_single, add_zero, one_smul] using
    P.smul_mem (monomial n (1 : R)) (hsingle0 m)

/-- Extension to polynomial scalars is finitely generated exactly when the original
coefficient module is finitely generated. Neither commutativity of the semiring nor
additive inverses in the module are required. -/
theorem finite_iff : Module.Finite R[X] (PolynomialModule.Extension R M) ↔
    Module.Finite R M := by
  constructor
  · intro h
    let := h
    let f : PolynomialModule.Extension R M →ₛₗ[Polynomial.constantCoeff] M :=
      { toFun := fun q => q.coeff 0
        map_add' := fun q q' => by simp
        map_smul' := fun p q => by simpa using coeff_smul p q 0 }
    apply Module.Finite.of_surjective f
    intro m
    refine ⟨single R 0 m, ?_⟩
    change (single R 0 m).coeff 0 = m
    simp
  · intro h
    classical
    obtain ⟨s, hs⟩ := h.fg_top
    exact Module.Finite.of_fg_top ⟨s.image (single R 0), span_image_single_eq_top s hs⟩

/-- Polynomial extension preserves finite generation of the coefficient module. -/
instance [Module.Finite R M] : Module.Finite R[X] (PolynomialModule.Extension R M) :=
  finite_iff.mpr inferInstance

/-- Let `f : R →+* S` be a surjective homomorphism which reflects units. If the
polynomial extension of the regular `S`-module restricted along `f` is finitely
presented, then the kernel of `f` is finitely generated as a left `R`-module.
The coefficient action in the hypothesis is `r • s = f r * s`. -/
theorem fg_ker_compHom_of_finitePresentation {S : Type v} [sS : Semiring S]
    (f : R →+* S) [IsLocalHom f] (hf : Function.Surjective f)
    (h : @Module.FinitePresentation (Polynomial R)
      (@PolynomialModule.Extension R S rR sS.toAddCommMonoid (Module.compHom S f))
      (@Polynomial.semiring R rR)
      ((@PolynomialModule.Extension.coeffEquiv R S rR sS.toAddCommMonoid
        (Module.compHom S f)).addCommMonoid)
      (@PolynomialModule.Extension.polynomialModule R S rR sS.toAddCommMonoid
        (Module.compHom S f))) :
    (@LinearMap.ker R R R S rR rR rR.toAddCommMonoid sS.toAddCommMonoid
      (@Semiring.toModule R rR) (Module.compHom S f) (RingHom.id R)
      (@Module.compHom.toLinearMap R S rR sS f)).FG := by
  classical
  let originalModule : @Module R S rR sS.toAddCommMonoid := Module.compHom S f
  let _ : Module R S := originalModule
  let ES : Type v := @PolynomialModule.Extension R S rR sS.toAddCommMonoid originalModule
  let addES : AddCommMonoid ES :=
    (@PolynomialModule.Extension.coeffEquiv R S rR sS.toAddCommMonoid
      originalModule).addCommMonoid
  let Q := Polynomial R
  let qR : Semiring Q := @Polynomial.semiring R rR
  let polynomialAction : @Module Q ES qR addES :=
    @PolynomialModule.Extension.polynomialModule R S rR sS.toAddCommMonoid originalModule
  let fL := @Module.compHom.toLinearMap R S rR sS f
  let I0 : Submodule R R := LinearMap.ker fL
  let E := h.out
  let s := Classical.choose E
  let hs := Classical.choose_spec E
  let I := ↥s
  let _ : Fintype I := { elems := s.attach, complete := Finset.mem_attach s }
  let FQ := I →₀ Q
  let Ls : FQ →ₗ[Q] ES :=
    @Finsupp.linearCombination I ES Q qR addES polynomialAction (fun i => i.val)
  let K := LinearMap.ker Ls
  let k := Classical.choose hs.2
  have hk : Submodule.span Q (k : Set FQ) = K := Classical.choose_spec hs.2
  have hsrange : Set.range (fun i : I => i.val) = (s : Set ES) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact i.property
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  have hLs_surj : Function.Surjective Ls := by
    apply LinearMap.range_eq_top.mp
    change LinearMap.range (Finsupp.linearCombination Q (fun i : I => i.val)) = ⊤
    rw [Finsupp.range_linearCombination, hsrange]
    exact hs.1
  let u := Classical.choose (hLs_surj (single R 0 (1 : S)))
  have hu : Ls u = single R 0 (1 : S) :=
    Classical.choose_spec (hLs_surj (single R 0 (1 : S)))
  have hLs_sum (z : FQ) : Ls z = ∑ i, z i • i.val := by
    calc
      Ls z = z.sum (fun i a => a • i.val) :=
        @Finsupp.linearCombination_apply I ES Q qR addES polynomialAction
          (fun i => i.val) z
      _ = ∑ i, z i • i.val :=
        Finsupp.sum_fintype z (fun i a => a • i.val) (fun i => zero_smul Q i.val)
  have hLs_coeff (z : FQ) :
      (Ls z).coeff 0 = ∑ i, f ((z i).coeff 0) * i.val.coeff 0 := by
    have hsum : (∑ i, ((z i) • i.val).coeff 0) =
        ∑ i, f ((z i).coeff 0) * i.val.coeff 0 := by
      apply Finset.sum_congr rfl
      intro i _
      calc
        ((z i) • i.val).coeff 0 = (z i).coeff 0 • i.val.coeff 0 := by
          simpa using coeff_smul (z i) i.val 0
        _ = f ((z i).coeff 0) * i.val.coeff 0 :=
          RingHom.toModule_smul f ((z i).coeff 0) (i.val.coeff 0)
    rw [hLs_sum]
    simpa only [coeff_sum, Finsupp.finsetSum_apply] using hsum
  let b : I → R := fun i => Classical.choose (hf (i.val.coeff 0))
  have fb (i : I) : f (b i) = i.val.coeff 0 :=
    Classical.choose_spec (hf (i.val.coeff 0))
  let r : I → R := fun i => (u i).coeff 0
  let T : R := ∑ i, r i * b i
  have fT : f T = 1 := by
    calc
      f T = ∑ i, f ((u i).coeff 0) * i.val.coeff 0 := by
        simp only [T, map_sum, map_mul, fb, r]
      _ = (Ls u).coeff 0 := (hLs_coeff u).symm
      _ = 1 := by rw [hu]; simp
  have hT : IsUnit T := IsUnit.of_map f T (by rw [fT]; exact isUnit_one)
  let TU : Rˣ := Classical.choose hT
  have hTU : (TU : R) = T := Classical.choose_spec hT
  let Tinv : R := ↑(TU⁻¹)
  have hTinv : Tinv * T = 1 := by simp [Tinv, ← hTU]
  let d : I → R := fun i => Tinv * r i
  let lambda : FQ →ₛₗ[(Polynomial.constantCoeff : Q →+* R)] R :=
    { toFun := fun z => ∑ i, (z i).coeff 0 * b i
      map_add' := fun z z' => by
        change (∑ i, ((z + z') i).coeff 0 * b i) =
          (∑ i, (z i).coeff 0 * b i) + ∑ i, (z' i).coeff 0 * b i
        calc
          (∑ i, ((z + z') i).coeff 0 * b i) =
              ∑ i, ((z i).coeff 0 * b i + (z' i).coeff 0 * b i) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finsupp.add_apply, Polynomial.coeff_add, add_mul]
          _ = _ := Finset.sum_add_distrib
      map_smul' := fun p z => by
        change (∑ i, ((p • z) i).coeff 0 * b i) =
          p.coeff 0 * ∑ i, (z i).coeff 0 * b i
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        change (p * z i).coeff 0 * b i = p.coeff 0 * ((z i).coeff 0 * b i)
        rw [Polynomial.mul_coeff_zero, mul_assoc] }
  let lambdaK : K →ₛₗ[(Polynomial.constantCoeff : Q →+* R)] R :=
    { toFun := fun x => lambda x.val
      map_add' := fun x y => lambda.map_add x.val y.val
      map_smul' := fun p x => lambda.map_smul' p x.val }
  -- Constant polynomials supply the scalar section for semilinear span transport.
  let _ : RingHomSurjective (Polynomial.constantCoeff : Q →+* R) :=
    ⟨fun a => ⟨C a, by simp⟩⟩
  have hlambdaK (x : K) : lambdaK x ∈ I0 := by
    have hx : Ls x.val = 0 := x.property
    change f (∑ i, (x.val i).coeff 0 * b i) = 0
    rw [map_sum]
    simp_rw [map_mul, fb]
    rw [← hLs_coeff, hx]
    simp
  have himage : K.map lambda = I0 := by
    ext a
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hlambdaK ⟨z, hz⟩
    · intro ha
      have hfa : f a = 0 := ha
      -- The inverse normalizes on the left; the kernel element remains leftmost.
      let za : FQ := Finsupp.equivFunOnFinite.symm (fun i => C (a * d i))
      have hza_apply (i : I) : za i = C (a * d i) := rfl
      have hkill (i : I) : (C (a * d i)) • i.val = 0 := by
        apply PolynomialModule.Extension.ext
        ext n
        rw [coeff_C_smul]
        change f (a * d i) * i.val.coeff n = 0
        rw [map_mul, hfa, zero_mul, zero_mul]
      have hza : za ∈ K := by
        change Ls za = 0
        rw [hLs_sum]
        apply Finset.sum_eq_zero
        intro i _
        rw [hza_apply, hkill]
      have hlambda_za : lambda za = a := by
        change (∑ i, (za i).coeff 0 * b i) = a
        simp only [hza_apply, Polynomial.coeff_C_zero]
        calc
          (∑ i, (a * d i) * b i) = a * Tinv * T := by
            simp only [T, d, Finset.mul_sum, mul_assoc]
          _ = a := by rw [mul_assoc, hTinv, mul_one]
      exact ⟨za, hza, hlambda_za⟩
  let w0 : Finset R := k.image lambda
  have hw0 : Submodule.span R (w0 : Set R) = I0 := by
    calc
      Submodule.span R (w0 : Set R) =
          Submodule.span R (lambda '' (k : Set FQ)) := by
        simp only [w0, Finset.coe_image]
      _ = (Submodule.span Q (k : Set FQ)).map lambda :=
        (Submodule.map_span lambda (k : Set FQ)).symm
      _ = I0 := by rw [hk, himage]
  exact ⟨w0, hw0⟩

private noncomputable def mapLinearEquiv {A : Type v} {B : Type w}
    [AddCommMonoid A] [AddCommMonoid B] [Module R A] [Module R B]
    (e : A ≃ₗ[R] B) : Extension R A ≃ₗ[R[X]] Extension R B :=
  LinearEquiv.ofLinearMap (mapLinear e.toLinearMap) (mapLinear e.symm.toLinearMap)
    (by
      apply LinearMap.ext
      intro q
      apply Extension.ext
      apply Finsupp.ext
      intro n
      change coeff (mapLinear e.toLinearMap (mapLinear e.symm.toLinearMap q)) n = coeff q n
      simp)
    (by
      apply LinearMap.ext
      intro q
      apply Extension.ext
      apply Finsupp.ext
      intro n
      change coeff (mapLinear e.symm.toLinearMap (mapLinear e.toLinearMap q)) n = coeff q n
      simp)

private theorem coeff_mapLinearEquiv {A : Type v} {B : Type w}
    [AddCommMonoid A] [AddCommMonoid B] [Module R A] [Module R B]
    (e : A ≃ₗ[R] B) (q : Extension R A) (n : ℕ) :
    coeff (mapLinearEquiv e q) n = e (coeff q n) :=
  coeff_mapLinear e.toLinearMap q n

/-- Polynomial extension preserves finite presentation in the finite-subset,
zero-kernel sense, over a possibly noncommutative semiring. -/
instance finitePresentation [h : Module.FinitePresentation R M] :
    Module.FinitePresentation R[X] (Extension R M) := by
  classical
  let s : Finset M := Classical.choose h.out
  have hs : Submodule.span R (s : Set M) = ⊤ ∧
      (LinearMap.ker (Finsupp.linearCombination R ((↑) : s → M))).FG :=
    Classical.choose_spec h.out
  let I := ↥s
  let F := I →₀ R
  let L : F →ₗ[R] M := Finsupp.linearCombination R ((↑) : I → M)
  let K : Submodule R F := LinearMap.ker L
  let t : Finset F := Classical.choose hs.2
  have ht : Submodule.span R (t : Set F) = K := Classical.choose_spec hs.2
  let s' : Finset (Extension R M) := s.image (single R 0)
  let I' := ↥s'
  let L' : (I' →₀ R[X]) →ₗ[R[X]] Extension R M :=
    Finsupp.linearCombination R[X] ((↑) : I' → Extension R M)
  let fintypeI : Fintype I := { elems := s.attach, complete := Finset.mem_attach s }
  let fintypeI' : Fintype I' := { elems := s'.attach, complete := Finset.mem_attach s' }
  let eI : I ≃ I' :=
    { toFun := fun i =>
        ⟨single R 0 i.val, Finset.mem_image_of_mem (single R 0) i.property⟩
      invFun := fun j => ⟨j.val.coeff 0, by
        rcases Finset.mem_image.mp j.property with ⟨m, hm, hj⟩
        rw [← hj]
        simpa using hm⟩
      left_inv := by
        intro i
        apply Subtype.ext
        simp
      right_inv := by
        intro j
        apply Subtype.ext
        rcases Finset.mem_image.mp j.property with ⟨m, hm, hj⟩
        change single R 0 (j.val.coeff 0) = j.val
        rw [← hj]
        simp }
  let a : F ≃ₗ[R] (I → R) := Finsupp.linearEquivFunOnFinite R R I
  let b : (I' →₀ R[X]) ≃ₗ[R[X]] (I' → R[X]) :=
    Finsupp.linearEquivFunOnFinite R[X] R[X] I'
  let Ea := mapLinearEquiv a
  let fPi : Extension R (I → R) →ₗ[R[X]] (I → Extension R R) :=
    LinearMap.pi fun i => mapLinear (LinearMap.proj i : (I → R) →ₗ[R] R)
  let bPi : (I → Extension R R) →ₗ[R[X]] Extension R (I → R) :=
    s.attach.sum fun i =>
      (mapLinear (LinearMap.single R (fun _ : I => R) i)).comp (LinearMap.proj i)
  have hattach : s.attach = (Finset.univ : Finset I) := by
    ext i
    simp
  have hfPi : fPi = (piLinearEquiv R R I).toLinearMap := by
    apply LinearMap.ext
    intro q
    funext i
    apply Extension.ext
    apply Finsupp.ext
    intro n
    change coeff (mapLinear (LinearMap.proj i : (I → R) →ₗ[R] R) q) n =
      coeff (piLinearEquiv R R I q i) n
    rw [coeff_mapLinear, piLinearEquiv_coeff]
    rfl
  have hbPi : bPi = (piLinearEquiv R R I).symm.toLinearMap := by
    apply LinearMap.ext
    intro p
    apply Extension.ext
    apply Finsupp.ext
    intro n
    funext i
    refine Eq.trans ?_ (piLinearEquiv_symm_coeff R R I p n i).symm
    let ev : ((I → Extension R R) →ₗ[R[X]] Extension R (I → R)) →+ R :=
      { toFun := fun f => coeff (f p) n i
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    change ev bPi = coeff (p i) n
    simp only [bPi, map_sum]
    change (∑ j ∈ s.attach,
      coeff (mapLinear (LinearMap.single R (fun _ : I => R) j) (p j)) n i) =
        coeff (p i) n
    simp only [coeff_mapLinear]
    rw [hattach]
    simp [LinearMap.single_apply, Pi.single_apply]
  have hPiRight : fPi.comp bPi = LinearMap.id := by
    rw [hfPi, hbPi]
    apply LinearMap.ext
    intro p
    exact (piLinearEquiv R R I).apply_symm_apply p
  have hPiLeft : bPi.comp fPi = LinearMap.id := by
    rw [hfPi, hbPi]
    apply LinearMap.ext
    intro q
    exact (piLinearEquiv R R I).symm_apply_apply q
  let ePi : Extension R (I → R) ≃ₗ[R[X]] (I → Extension R R) :=
    LinearEquiv.ofLinearMap fPi bPi hPiRight hPiLeft
  have hePi : ePi = piLinearEquiv R R I := by
    apply LinearEquiv.ext
    intro q
    exact DFunLike.congr_fun hfPi q
  let c := ePi.trans (LinearEquiv.piCongrRight fun _ : I => regularEquiv R)
  have hc : c = piRegularEquiv R I := by
    change ePi.trans (LinearEquiv.piCongrRight fun _ : I => regularEquiv R) = _
    rw [hePi]
    rfl
  let rI := LinearEquiv.piCongrLeft' R[X] (fun _ : I => R[X]) eI
  let ψ : Extension R F ≃ₗ[R[X]] (I' →₀ R[X]) :=
    ((Ea.trans c).trans rI).trans b.symm
  have hψcoeff (q : Extension R F) (j : I') (n : ℕ) :
      (ψ q j).coeff n = (q.coeff n) (eI.symm j) := by
    change (c (Ea q) (eI.symm j)).coeff n = _
    rw [hc, piRegularEquiv_coeff, coeff_mapLinearEquiv]
    rfl
  have hψapply (q : Extension R F) (j : I') :
      ψ q j = ∑ n ∈ q.coeff.support,
        Polynomial.monomial n ((q.coeff n) (eI.symm j)) := by
    apply Polynomial.ext
    intro n
    rw [hψcoeff, Polynomial.finsetSum_coeff]
    by_cases hn : n ∈ q.coeff.support
    · simp [Polynomial.coeff_monomial, hn]
    · have hz : q.coeff n = 0 := Finsupp.notMem_support_iff.mp hn
      simpa [Polynomial.coeff_monomial, hn, hz] using
        (show (0 : F) (eI.symm j) = (0 : R) from rfl)
  have hψsymm (u : I' →₀ R[X]) (n : ℕ) (i : I) :
      ((ψ.symm u).coeff n) i = (u (eI i)).coeff n := by
    have hx := hψcoeff (ψ.symm u) (eI i) n
    simpa only [LinearEquiv.apply_symm_apply, Equiv.symm_apply_apply] using hx.symm
  have hψsingle (n : ℕ) (f : F) (j : I') :
      ψ (single R n f) j = Polynomial.monomial n (f (eI.symm j)) := by
    apply Polynomial.ext
    intro k
    rw [hψcoeff, coeff_single_apply, Polynomial.coeff_monomial]
    split_ifs <;> rfl
  have hψsingle_single (i : I) (r : R) :
      ψ (single R 0 (Finsupp.single i r)) = Finsupp.single (eI i) (C r) := by
    apply Finsupp.ext
    intro j
    rw [hψsingle]
    by_cases hij : i = eI.symm j
    · have heij : eI i = j :=
        (congrArg eI hij).trans (eI.apply_symm_apply j)
      have hinner : (Finsupp.single i r : F) (eI.symm j) = r := by
        rw [← hij, Finsupp.single_eq_same]
      have houter : (Finsupp.single (eI i) (C r) : I' →₀ R[X]) j = C r := by
        rw [← heij, Finsupp.single_eq_same]
      rw [hinner, houter, Polynomial.monomial_zero_left]
    · have heij : eI i ≠ j := by
        intro h
        apply hij
        simpa only [Equiv.symm_apply_apply] using congrArg eI.symm h
      have hinner : (Finsupp.single i r : F) (eI.symm j) = 0 :=
        Finsupp.single_eq_of_ne' hij
      have houter : (Finsupp.single (eI i) (C r) : I' →₀ R[X]) j = 0 :=
        Finsupp.single_eq_of_ne' heij
      rw [hinner, houter, Polynomial.monomial_zero_right]
  have hintertwine : L'.comp ψ.toLinearMap = mapLinear L := by
    apply linearMap_ext
    intro f
    change L' (ψ (single R 0 f)) = mapLinear L (single R 0 f)
    rw [mapLinear_single]
    refine Finsupp.induction_linear f ?_ ?_ ?_
    · simp
    · intro f g hf hg
      simpa only [single_add, map_add] using congrArg₂ (· + ·) hf hg
    · intro i r
      rw [hψsingle_single]
      have hL'single : L' (Finsupp.single (eI i) (C r)) =
          C r • ((eI i : I') : Extension R M) :=
        Finsupp.linearCombination_single R[X] (C r) (eI i)
      have hLsingle : L (Finsupp.single i r) = r • (i : M) :=
        Finsupp.linearCombination_single R r i
      rw [hL'single, hLsingle]
      rw [show ((eI i : I') : Extension R M) = single R 0 (i : M) from rfl]
      simp only [single_smul, C_smul]
  have hsurjL : Function.Surjective L := by
    have hrange : Set.range ((↑) : I → M) = (s : Set M) := by
      ext m
      constructor
      · rintro ⟨i, rfl⟩
        exact i.property
      · intro hm
        exact ⟨⟨m, hm⟩, rfl⟩
    have htop : LinearMap.range L = ⊤ := by
      change LinearMap.range (Finsupp.linearCombination R ((↑) : I → M)) = ⊤
      rw [Finsupp.range_linearCombination, hrange]
      exact hs.1
    intro m
    have hm : m ∈ LinearMap.range L := by rw [htop]; trivial
    exact hm
  have hsurjNL : Function.Surjective (mapLinear L) := by
    have hmap := (map_surjective_iff L).mpr hsurjL
    intro q
    obtain ⟨v, hv⟩ := hmap q
    exact ⟨v, (mapLinear_apply L v).trans hv⟩
  have hsurjL' : Function.Surjective L' := by
    intro q
    obtain ⟨v, hv⟩ := hsurjNL q
    refine ⟨ψ v, ?_⟩
    change (L'.comp ψ.toLinearMap) v = q
    rw [hintertwine]
    exact hv
  have hspan' : Submodule.span R[X] (s' : Set (Extension R M)) = ⊤ := by
    have hrange : Set.range ((↑) : I' → Extension R M) =
        (s' : Set (Extension R M)) := by
      ext q
      constructor
      · rintro ⟨j, rfl⟩
        exact j.property
      · intro hq
        exact ⟨⟨q, hq⟩, rfl⟩
    have htop : LinearMap.range L' = ⊤ := by
      apply top_unique
      intro q _
      exact hsurjL' q
    change LinearMap.range (Finsupp.linearCombination R[X]
      ((↑) : I' → Extension R M)) = ⊤ at htop
    rw [Finsupp.range_linearCombination, hrange] at htop
    exact htop
  have hexact : Function.Exact K.subtype L := by
    intro f
    constructor
    · intro hf
      exact ⟨⟨f, hf⟩, rfl⟩
    · rintro ⟨k, rfl⟩
      exact k.property
  have hexactN : Function.Exact (mapLinear K.subtype) (mapLinear L) := by
    intro q
    change mapLinear L q = 0 ↔ ∃ v : Extension R K, mapLinear K.subtype v = q
    have hx := (exact_iff_map K.subtype L).mp hexact q
    change map L q = 0 ↔ ∃ v : Extension R K, map K.subtype v = q at hx
    simpa only [mapLinear_apply] using hx
  have hrangeN : LinearMap.range (mapLinear K.subtype) =
      LinearMap.ker (mapLinear L) := by
    ext q
    exact (hexactN q).symm
  let promote : ↥t → K := fun k =>
    ⟨k.val, ht ▸ (Submodule.subset_span k.property)⟩
  let tK : Finset K := t.attach.image promote
  let TK : Finset (Extension R K) := tK.image (single R 0)
  let J : Extension R K →ₗ[R[X]] (I' →₀ R[X]) :=
    ψ.toLinearMap.comp (mapLinear K.subtype)
  let w : Finset (I' →₀ R[X]) := TK.image J
  have hspanK : Submodule.span R (tK : Set K) = ⊤ := by
    apply top_unique
    intro k _
    have hk : (k : F) ∈ Submodule.span R (t : Set F) := by
      rw [ht]
      exact k.property
    have hkspan : ∀ hK : (k : F) ∈ K,
        (⟨(k : F), hK⟩ : K) ∈ Submodule.span R (tK : Set K) := by
      refine Submodule.span_induction
        (p := fun f _ => ∀ hK : f ∈ K,
          (⟨f, hK⟩ : K) ∈ Submodule.span R (tK : Set K))
        ?_ ?_ ?_ ?_ hk
      · intro f hf _
        apply Submodule.subset_span
        exact Finset.mem_image.mpr ⟨⟨f, hf⟩, Finset.mem_attach t ⟨f, hf⟩, rfl⟩
      · intro _
        exact (Submodule.span R (tK : Set K)).zero_mem
      · intro f g hf hg ihf ihg _
        exact (Submodule.span R (tK : Set K)).add_mem (ihf (ht ▸ hf)) (ihg (ht ▸ hg))
      · intro r f hf ihf _
        exact (Submodule.span R (tK : Set K)).smul_mem r (ihf (ht ▸ hf))
    exact hkspan k.property
  let : Module.Finite R K := Module.Finite.of_fg_top ⟨tK, hspanK⟩
  have hspanTK : Submodule.span R[X] (TK : Set (Extension R K)) = ⊤ :=
    span_image_single_eq_top tK hspanK
  have hrelation (k : ↥t) :
      J (single R 0 (promote k)) = ψ (single R 0 k.val) := by
    change ψ (mapLinear K.subtype (single R 0 (promote k))) = _
    rw [mapLinear_single]
    rfl
  have hrelation_coeff (k : ↥t) (i : I) :
      J (single R 0 (promote k)) (eI i) = C (k.val i) := by
    rw [hrelation, hψsingle]
    simp
  have hrangeJ : LinearMap.range J = LinearMap.ker L' := by
    ext u
    constructor
    · rintro ⟨v, rfl⟩
      have hv : mapLinear K.subtype v ∈ LinearMap.ker (mapLinear L) := by
        rw [← hrangeN]
        exact ⟨v, rfl⟩
      change L' (ψ (mapLinear K.subtype v)) = 0
      change (L'.comp ψ.toLinearMap) (mapLinear K.subtype v) = 0
      rw [hintertwine]
      exact hv
    · intro hu
      change L' u = 0 at hu
      have hv : ψ.symm u ∈ LinearMap.ker (mapLinear L) := by
        change mapLinear L (ψ.symm u) = 0
        rw [← hintertwine]
        change L' (ψ (ψ.symm u)) = 0
        simpa only [LinearEquiv.apply_symm_apply] using hu
      rw [← hrangeN] at hv
      obtain ⟨v, hv⟩ := hv
      refine ⟨v, ?_⟩
      change ψ (mapLinear K.subtype v) = u
      rw [hv, LinearEquiv.apply_symm_apply]
  have hker' : Submodule.span R[X] (w : Set (I' →₀ R[X])) = LinearMap.ker L' := by
    calc
      Submodule.span R[X] (w : Set (I' →₀ R[X])) =
          (Submodule.span R[X] (TK : Set (Extension R K))).map J := by
        simpa only [w, Finset.coe_image] using
          (Submodule.map_span J (TK : Set (Extension R K))).symm
      _ = (⊤ : Submodule R[X] (Extension R K)).map J := by rw [hspanTK]
      _ = LinearMap.range J := Submodule.map_top J
      _ = LinearMap.ker L' := hrangeJ
  exact { out := ⟨s', hspan', ⟨w, hker'⟩⟩ }

end PolynomialModule.Extension

namespace PolynomialModule.Extension

variable {R : Type u} {M : Type v} [Semiring R] [AddCommGroup M] [Module R M]

private noncomputable def freeConstantCoeff (I : Type w) :
    (I →₀ R[X]) →ₛₗ[(Polynomial.constantCoeff : R[X] →+* R)] (I →₀ R) :=
  Finsupp.mapRange.linearMap
    { toFun := (Polynomial.constantCoeff : R[X] →+* R)
      map_add' := (Polynomial.constantCoeff : R[X] →+* R).map_add
      map_smul' := (Polynomial.constantCoeff : R[X] →+* R).map_mul }

private theorem freeConstantCoeff_apply {I : Type w} (z : I →₀ R[X]) (i : I) :
    freeConstantCoeff I z i = (z i).coeff 0 := rfl

private theorem freeConstantCoeff_single {I : Type w} (i : I) (b : R[X]) :
    freeConstantCoeff I (Finsupp.single i b) = Finsupp.single i (b.coeff 0) := by
  classical
  ext j
  simp only [freeConstantCoeff_apply, Finsupp.single_apply]
  split_ifs <;> simp

private noncomputable def freeConstant (I : Type w) :
    (I →₀ R) →ₛₗ[(Polynomial.C : R →+* R[X])] (I →₀ R[X]) :=
  Finsupp.mapRange.linearMap
    { toFun := (Polynomial.C : R →+* R[X])
      map_add' := (Polynomial.C : R →+* R[X]).map_add
      map_smul' := (Polynomial.C : R →+* R[X]).map_mul }

private theorem freeConstant_apply {I : Type w} (x : I →₀ R) (i : I) :
    freeConstant I x i = Polynomial.C (x i) := rfl

private theorem freeConstantCoeff_freeConstant {I : Type w} (x : I →₀ R) :
    freeConstantCoeff I (freeConstant I x) = x := by
  ext i
  simp only [freeConstantCoeff_apply, freeConstant_apply, Polynomial.coeff_C_zero]

private noncomputable def negCoefficients (u : Extension R M) : Extension R M :=
  ofCoeff R (-u.coeff)

private theorem negCoefficients_apply (u : Extension R M) (n : ℕ) :
    (negCoefficients u).coeff n = -(u.coeff n) := rfl

private noncomputable def tailCoefficients (u : Extension R M) : Extension R M :=
  ofCoeff R (Finsupp.onFinset (u.coeff.support.image Nat.pred)
    (fun n => u.coeff (n + 1)) (by
      intro n hn
      exact Finset.mem_image.mpr ⟨n + 1, Finsupp.mem_support_iff.mpr hn, by simp⟩))

private theorem tailCoefficients_apply (u : Extension R M) (n : ℕ) :
    (tailCoefficients u).coeff n = u.coeff (n + 1) := rfl

private theorem add_X_smul_neg_tail {u : Extension R M} (hu : u.coeff 0 = 0) :
    u + (X : R[X]) • negCoefficients (tailCoefficients u) = 0 := by
  apply ext
  ext n
  cases n with
  | zero => simp [hu]
  | succ n => simp [negCoefficients_apply, tailCoefficients_apply]

/-- Polynomial extension reflects finite presentation when the coefficient module
is an additive commutative group. Here finite presentation uses a finite subset and
its own finitely generated zero kernel; the scalar semiring need not be a ring or
commutative. -/
theorem finitePresentation_of_extension
    (h : Module.FinitePresentation R[X] (Extension R M)) :
    Module.FinitePresentation R M := by
  classical
  let s : Finset (Extension R M) := Classical.choose h.out
  have hs : Submodule.span R[X] (s : Set (Extension R M)) = ⊤ ∧
      (LinearMap.ker (Finsupp.linearCombination R[X]
        ((↑) : s → Extension R M))).FG := Classical.choose_spec h.out
  let I := ↥s
  let L : (I →₀ R[X]) →ₗ[R[X]] Extension R M :=
    Finsupp.linearCombination R[X] ((↑) : I → Extension R M)
  let K : Submodule R[X] (I →₀ R[X]) := LinearMap.ker L
  let k : Finset (I →₀ R[X]) := Classical.choose hs.2
  have hk : Submodule.span R[X] (k : Set (I →₀ R[X])) = K :=
    Classical.choose_spec hs.2
  let t : Finset M := s.image (fun u => u.coeff 0)
  let T := ↥t
  let a : I → T := fun i =>
    ⟨i.val.coeff 0, Finset.mem_image.mpr ⟨i.val, i.property, rfl⟩⟩
  let p : (I →₀ R) →ₗ[R] M :=
    Finsupp.linearCombination R (fun i : I => i.val.coeff 0)
  let q : (T →₀ R) →ₗ[R] M := Finsupp.linearCombination R ((↑) : T → M)
  let A : (I →₀ R) →ₗ[R] (T →₀ R) := Finsupp.lmapDomain R R a
  let Λ : (I →₀ R[X]) →ₛₗ[(Polynomial.constantCoeff : R[X] →+* R)] (I →₀ R) :=
    freeConstantCoeff I
  let J : (I →₀ R) →ₛₗ[(Polynomial.C : R →+* R[X])] (I →₀ R[X]) := freeConstant I
  let D : (I →₀ R[X]) →ₛₗ[(Polynomial.constantCoeff : R[X] →+* R)] (T →₀ R) :=
    { toFun := fun z => A (Λ z)
      map_add' := fun z z' => by simp only [map_add]
      map_smul' := fun b z => by rw [Λ.map_smulₛₗ, A.map_smul] }
  have hD (z : I →₀ R[X]) : D z = A (Λ z) := rfl
  let ell : Finset (T →₀ R) := k.image (fun z => D z)
  have hpq (x : I →₀ R) : q (A x) = p x :=
    Finsupp.linearCombination_mapDomain R a x
  have hΛJ (x : I →₀ R) : Λ (J x) = x := freeConstantCoeff_freeConstant x
  have hcoeff (z : I →₀ R[X]) : p (Λ z) = (L z).coeff 0 := by
    induction z using Finsupp.induction_linear with
    | zero => simp
    | add z z' hz hz' =>
      simp only [map_add, coeff_add, Finsupp.add_apply, hz, hz']
    | single i b =>
      simpa [p, L, Λ, freeConstantCoeff_single, Finsupp.linearCombination_single]
        using (coeff_smul b i.val 0).symm
  have hqD (z : I →₀ R[X]) : q (D z) = (L z).coeff 0 := by
    rw [hD, hpq, hcoeff]
  have hL : Function.Surjective L := by
    have hrange : LinearMap.range L = ⊤ :=
      (Finsupp.span_eq_range_linearCombination (R := R[X])
        (s : Set (Extension R M))).symm.trans hs.1
    intro u
    have hu : u ∈ LinearMap.range L := by rw [hrange]; trivial
    exact hu
  have Ha (j : T) : ∃ i : I, a i = j := by
    obtain ⟨u, hu, hj⟩ := Finset.mem_image.mp j.property
    refine ⟨⟨u, hu⟩, ?_⟩
    exact Subtype.ext hj
  let σ : T → I := fun j => Classical.choose (Ha j)
  have hσ (j : T) : a (σ j) = j := Classical.choose_spec (Ha j)
  let B : (T →₀ R) →ₗ[R] (I →₀ R) := Finsupp.lmapDomain R R σ
  have hAB (y : T →₀ R) : A (B y) = y := by
    induction y using Finsupp.induction_linear with
    | zero => simp
    | add y y' hy hy' => simp only [map_add, hy, hy']
    | single j r =>
      change Finsupp.mapDomain a (Finsupp.mapDomain σ (Finsupp.single j r)) = _
      rw [Finsupp.mapDomain_single, Finsupp.mapDomain_single, hσ]
  have hlift (x : I →₀ R) (hx : p x = 0) :
      ∃ z : I →₀ R[X], L z = 0 ∧ Λ z = x := by
    let u : Extension R M := L (J x)
    have hu : u.coeff 0 = 0 := by rw [← hcoeff, hΛJ, hx]
    let n : Extension R M := negCoefficients (tailCoefficients u)
    let v : I →₀ R[X] := Classical.choose (hL n)
    have hv : L v = n := Classical.choose_spec (hL n)
    refine ⟨J x + (X : R[X]) • v, ?_, ?_⟩
    · rw [map_add, L.map_smul, hv]
      exact add_X_smul_neg_tail hu
    · rw [map_add, Λ.map_smulₛₗ, hΛJ]
      simp
  have hliftq (y : T →₀ R) (hy : q y = 0) :
      ∃ z : I →₀ R[X], L z = 0 ∧ D z = y := by
    have hx : p (B y) = 0 := by rw [← hpq, hAB, hy]
    obtain ⟨z, hz, hzx⟩ := hlift (B y) hx
    exact ⟨z, hz, by rw [hD, hzx, hAB]⟩
  have hspan : Submodule.span R (t : Set M) = ⊤ := by
    apply top_unique
    intro m _
    obtain ⟨z, hz⟩ := hL (single R 0 m)
    have hm : q (D z) = m := by rw [hqD, hz]; simp
    rw [← hm, Finsupp.span_eq_range_linearCombination]
    exact ⟨D z, rfl⟩
  have hkzero {z : I →₀ R[X]} (hz : z ∈ k) : L z = 0 := by
    have hzspan : z ∈ Submodule.span R[X] (k : Set (I →₀ R[X])) :=
      Submodule.subset_span hz
    have hzK : z ∈ K := hk ▸ hzspan
    exact hzK
  have hDspan {z : I →₀ R[X]}
      (hz : z ∈ Submodule.span R[X] (k : Set (I →₀ R[X]))) :
      D z ∈ Submodule.span R (ell : Set (T →₀ R)) := by
    refine Submodule.span_induction
      (p := fun z _ => D z ∈ Submodule.span R (ell : Set (T →₀ R)))
      ?_ ?_ ?_ ?_ hz
    · intro z hz
      exact Submodule.subset_span (Finset.mem_image.mpr ⟨z, hz, rfl⟩)
    · simpa only [map_zero] using (Submodule.span R (ell : Set (T →₀ R))).zero_mem
    · intro z z' hz hz' ih ih'
      simpa only [map_add] using
        (Submodule.span R (ell : Set (T →₀ R))).add_mem ih ih'
    · intro b z hz ih
      simpa only [D.map_smulₛₗ] using
        (Submodule.span R (ell : Set (T →₀ R))).smul_mem (Polynomial.constantCoeff b) ih
  have hker : Submodule.span R (ell : Set (T →₀ R)) = LinearMap.ker q := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      intro y hy
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
      change q (D z) = 0
      rw [hqD, hkzero hz, coeff_zero, Finsupp.zero_apply]
    · intro y hy
      obtain ⟨z, hz, hzy⟩ := hliftq y hy
      have hzK : z ∈ K := hz
      have hzspan : z ∈ Submodule.span R[X] (k : Set (I →₀ R[X])) := hk.symm ▸ hzK
      rw [← hzy]
      exact hDspan hzspan
  exact { out := ⟨t, hspan, ⟨ell, hker⟩⟩ }

/-- For an additive commutative group of coefficients, polynomial extension
preserves and reflects finite presentation in the finite-subset, zero-kernel sense. -/
theorem finitePresentation_iff_of_addCommGroup :
    Module.FinitePresentation R[X] (Extension R M) ↔ Module.FinitePresentation R M := by
  constructor
  · exact finitePresentation_of_extension
  · intro h
    exact finitePresentation (R := R) (M := M) (h := h)

end PolynomialModule.Extension

namespace PolynomialModule.Extension

variable {R : Type u} {M : Type v} [Semiring R] [AddCommMonoid M] [Module R M]

private noncomputable def scalarCoefficientSum (R : Type u) [Semiring R] : R[X] →+ R :=
  Polynomial.eval₂AddMonoidHom (RingHom.id R) 1

private noncomputable def freeCoefficientSum (I : Type w) : (I →₀ R[X]) →+ (I →₀ R) :=
  Finsupp.mapRange.addMonoidHom (ι := I) (scalarCoefficientSum R)

private theorem freeCoefficientSum_apply {I : Type w} (f : I →₀ R[X]) (i : I) :
    freeCoefficientSum I f i = scalarCoefficientSum R (f i) := rfl

private theorem freeCoefficientSum_single {I : Type w} (i : I) (p : R[X]) :
    freeCoefficientSum I (Finsupp.single i p) =
      Finsupp.single i (scalarCoefficientSum R p) := by
  classical
  ext j
  simp only [freeCoefficientSum_apply, Finsupp.single_apply]
  split_ifs <;> simp

open Classical in
private noncomputable def coefficientSumIndex (S : Finset (Extension R M)) :
    S → S.image (coefficientSum (R := R)) :=
  fun s => ⟨coefficientSum s.val, Finset.mem_image.mpr ⟨s.val, s.property, rfl⟩⟩

open Classical in
private noncomputable def descendCoefficients (S : Finset (Extension R M)) :
    (S →₀ R[X]) →+ (S.image (coefficientSum (R := R)) →₀ R) :=
  (Finsupp.lmapDomain R R (coefficientSumIndex S)).toAddMonoidHom.comp
    (freeCoefficientSum S)

private theorem descendCoefficients_single (S : Finset (Extension R M))
    (s : S) (p : R[X]) :
    descendCoefficients S (Finsupp.single s p) =
      Finsupp.single (coefficientSumIndex S s) (scalarCoefficientSum R p) := by
  classical
  change Finsupp.mapDomain (coefficientSumIndex S)
    (freeCoefficientSum S (Finsupp.single s p)) = _
  rw [freeCoefficientSum_single, Finsupp.mapDomain_single]

open Classical in
private theorem linearCombination_descendCoefficients (S : Finset (Extension R M))
    (f : S →₀ R[X]) :
    Finsupp.linearCombination R ((↑) : S.image (coefficientSum (R := R)) → M)
        (descendCoefficients S f) =
      coefficientSum (Finsupp.linearCombination R[X] ((↑) : S → Extension R M) f) := by
  classical
  refine Finsupp.induction_linear f ?_ ?_ ?_
  · simp
  · intro f g hf hg
    simp only [map_add, hf, hg]
  · intro s p
    rw [descendCoefficients_single, Finsupp.linearCombination_single,
      Finsupp.linearCombination_single, coefficientSum_smul]
    rfl

open Classical in
/-- Summing coefficients of a finite polynomial generating subset gives a generating
subset of the coefficient module. -/
theorem span_image_coefficientSum_eq_top (S : Finset (Extension R M))
    (hS : Submodule.span R[X] (S : Set (Extension R M)) = ⊤) :
    Submodule.span R (S.image (coefficientSum (R := R)) : Set M) = ⊤ := by
  classical
  let L := Finsupp.linearCombination R[X] ((↑) : S → Extension R M)
  have hL : Function.Surjective L := by
    apply (span_range_eq_top_iff_surjective_finsuppLinearCombination
      (R := R[X]) (v := ((↑) : S → Extension R M))).mp
    simpa only [Subtype.range_coe_subtype, Finset.setOfPred_mem] using hS
  apply le_antisymm le_top
  intro m _
  obtain ⟨f, hf⟩ := hL (single R 0 m)
  have hm : Finsupp.linearCombination R
      ((↑) : S.image (coefficientSum (R := R)) → M) (descendCoefficients S f) = m := by
    rw [linearCombination_descendCoefficients]
    change coefficientSum (L f) = m
    rw [hf, coefficientSum_single]
  rw [← hm, Finsupp.linearCombination_apply]
  exact Submodule.sum_mem _ fun t _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span t.property)

private theorem freeConstant_single {I : Type w} (i : I) (r : R) :
    freeConstant (R := R) I (Finsupp.single i r) = Finsupp.single i (Polynomial.C r) := by
  classical
  ext j
  simp only [freeConstant_apply, Finsupp.single_apply]
  split_ifs <;> simp

open Classical in
private theorem descendCoefficients_constant_section (S : Finset (Extension R M))
    (rep : S.image (coefficientSum (R := R)) → S)
    (hrep : ∀ t, coefficientSumIndex S (rep t) = t)
    (a : S.image (coefficientSum (R := R)) →₀ R) :
    descendCoefficients S
        (freeConstant (R := R) S (Finsupp.lmapDomain R R rep a)) = a := by
  classical
  refine Finsupp.induction_linear a ?_ ?_ ?_
  · simp
  · intro a b ha hb
    simp only [map_add, ha, hb]
  · intro t r
    simp only [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
      freeConstant_single, descendCoefficients_single, hrep]
    congr 1
    simp [scalarCoefficientSum, Polynomial.eval₂AddMonoidHom]

private theorem descendCoefficients_X_smul (S : Finset (Extension R M)) (f : S →₀ R[X]) :
    descendCoefficients S ((X : R[X]) • f) = descendCoefficients S f := by
  classical
  change Finsupp.mapDomain (coefficientSumIndex S)
      (freeCoefficientSum S ((X : R[X]) • f)) =
    Finsupp.mapDomain (coefficientSumIndex S) (freeCoefficientSum S f)
  congr 1
  ext i
  change scalarCoefficientSum R (X * f i) = scalarCoefficientSum R (f i)
  simp [scalarCoefficientSum, Polynomial.eval₂AddMonoidHom]

private theorem exists_prefix_tail (q : Extension R M) (hq : coefficientSum q = 0) :
    ∃ w z : Extension R M, w + z = 0 ∧ q + (X : R[X]) • w = w := by
  classical
  let U := q.coeff.support
  let N : ℕ := U.sup id
  let H := Finset.range (N + 1)
  let prefixSum (n : ℕ) := (U.filter (fun i => i ≤ n)).sum (fun i => q.coeff i)
  let tail (n : ℕ) := (U.filter (fun i => n < i)).sum (fun i => q.coeff i)
  have htotalq : U.sum (fun i => q.coeff i) = 0 := hq
  have hbound {i : ℕ} (hi : i ∈ U) : i ≤ N :=
    Finset.le_sup (f := fun n : ℕ => n) hi
  have hp (n : ℕ) (hn : prefixSum n ≠ 0) : n ∈ H := by
    by_contra hnH
    have hNn : N < n := Nat.lt_of_lt_of_le (Nat.lt_succ_self N)
      (Nat.le_of_not_gt (fun h => hnH (Finset.mem_range.mpr h)))
    have hfilter : U.filter (fun i => i ≤ n) = U := by
      apply Finset.filter_eq_self.mpr
      intro i hi
      exact (hbound hi).trans (Nat.le_of_lt hNn)
    apply hn
    change (U.filter (fun i => i ≤ n)).sum (fun i => q.coeff i) = 0
    rw [hfilter]
    exact htotalq
  have ht (n : ℕ) (hn : tail n ≠ 0) : n ∈ H := by
    by_contra hnH
    have hNn : N < n := Nat.lt_of_lt_of_le (Nat.lt_succ_self N)
      (Nat.le_of_not_gt (fun h => hnH (Finset.mem_range.mpr h)))
    apply hn
    apply Finset.sum_eq_zero
    intro i hi
    obtain ⟨hiU, hni⟩ := Finset.mem_filter.mp hi
    exact False.elim (not_lt_of_ge ((hbound hiU).trans (Nat.le_of_lt hNn)) hni)
  have htotal (n : ℕ) : prefixSum n + tail n = 0 := by
    calc
      prefixSum n + tail n = U.sum (fun i => q.coeff i) := by
        simpa only [prefixSum, tail, not_le] using
          (Finset.sum_filter_add_sum_filter_not U (fun i => i ≤ n) (fun i => q.coeff i))
      _ = 0 := htotalq
  have hprefix_range (n : ℕ) :
      prefixSum n = (Finset.range (n + 1)).sum (fun i => q.coeff i) := by
    change (U.filter (fun i => i ≤ n)).sum (fun i => q.coeff i) = _
    refine Finset.sum_subset ?_ ?_
    · intro i hi
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_filter.mp hi).2)
    · intro i hi hin
      by_contra hzero
      exact hin (Finset.mem_filter.mpr
        ⟨Finsupp.mem_support_iff.mpr hzero, Nat.le_of_lt_succ (Finset.mem_range.mp hi)⟩)
  let w : Extension R M := ofCoeff R (Finsupp.onFinset H prefixSum hp)
  let z : Extension R M := ofCoeff R (Finsupp.onFinset H tail ht)
  have hw (n : ℕ) : w.coeff n = prefixSum n := rfl
  have hz (n : ℕ) : z.coeff n = tail n := rfl
  refine ⟨w, z, ?_, ?_⟩
  · apply ext
    apply Finsupp.ext
    intro n
    simpa only [coeff_add, Finsupp.add_apply, coeff_zero, Finsupp.zero_apply, hw, hz] using
      htotal n
  · apply ext
    apply Finsupp.ext
    intro n
    cases n with
    | zero =>
      simp only [coeff_add, Finsupp.add_apply, coeff_X_smul_zero, add_zero, hw]
      rw [hprefix_range]
      simp
    | succ n =>
      simp only [coeff_add, Finsupp.add_apply, coeff_X_smul_succ, hw]
      rw [hprefix_range (n + 1), Finset.sum_range_succ, ← hprefix_range n]
      exact add_comm _ _

open Classical in
/-- A spanning polynomial subset with zero own relation kernel descends, by coefficient
sum, to a coefficient subset with zero own relation kernel. -/
theorem ker_linearCombination_image_coefficientSum_eq_bot (S : Finset (Extension R M))
    (hS : Submodule.span R[X] (S : Set (Extension R M)) = ⊤)
    (hK : LinearMap.ker
      (Finsupp.linearCombination R[X] ((↑) : S → Extension R M)) = ⊥) :
    LinearMap.ker (Finsupp.linearCombination R
      ((↑) : S.image (coefficientSum (R := R)) → M)) = ⊥ := by
  classical
  let T := S.image (coefficientSum (R := R))
  let Ls := Finsupp.linearCombination R[X] ((↑) : S → Extension R M)
  let LT := Finsupp.linearCombination R ((↑) : T → M)
  have hL : Function.Surjective Ls := by
    apply (span_range_eq_top_iff_surjective_finsuppLinearCombination
      (R := R[X]) (v := ((↑) : S → Extension R M))).mp
    simpa only [Subtype.range_coe_subtype, Finset.setOfPred_mem] using hS
  have hEta : Function.Surjective (coefficientSumIndex S) := by
    intro t
    obtain ⟨s, hs, he⟩ := Finset.mem_image.mp t.property
    exact ⟨⟨s, hs⟩, Subtype.ext he⟩
  let rep : T → S := fun t => Classical.choose (hEta t)
  have hrep (t : T) : coefficientSumIndex S (rep t) = t := Classical.choose_spec (hEta t)
  let sigma := Finsupp.lmapDomain R R rep
  let P : Extension R M → (S →₀ R[X]) := fun q => Classical.choose (hL q)
  have hP (q : Extension R M) : Ls (P q) = q := Classical.choose_spec (hL q)
  apply le_antisymm ?_ bot_le
  intro a ha
  have ha0 : LT a = 0 := ha
  let lifted := freeConstant (R := R) S (sigma a)
  have hlifted : descendCoefficients S lifted = a :=
    descendCoefficients_constant_section S rep hrep a
  let q := Ls lifted
  have hq : coefficientSum q = 0 := by
    change coefficientSum (Ls lifted) = 0
    rw [← linearCombination_descendCoefficients S lifted, hlifted]
    exact ha0
  obtain ⟨w, z, hwz, hshift⟩ := exists_prefix_tail q hq
  let b := P w
  let cLift := P z
  have hb : Ls b = w := hP w
  have hc : Ls cLift = z := hP z
  let u := b + cLift
  let v := lifted + (X : R[X]) • b + cLift
  have huK : u ∈ LinearMap.ker Ls := by
    change Ls (b + cLift) = 0
    rw [map_add, hb, hc, hwz]
  have hvK : v ∈ LinearMap.ker Ls := by
    change Ls (lifted + (X : R[X]) • b + cLift) = 0
    rw [map_add, map_add, Ls.map_smul, hb, hc]
    change q + (X : R[X]) • w + z = 0
    rw [hshift, hwz]
  have hu : u = 0 := by
    have hu0 : u ∈ (⊥ : Submodule R[X] (S →₀ R[X])) := hK ▸ huK
    simpa only [Submodule.mem_bot] using hu0
  have hv : v = 0 := by
    have hv0 : v ∈ (⊥ : Submodule R[X] (S →₀ R[X])) := hK ▸ hvK
    simpa only [Submodule.mem_bot] using hv0
  have huv : descendCoefficients S v = a + descendCoefficients S u := by
    change descendCoefficients S (lifted + (X : R[X]) • b + cLift) =
      a + descendCoefficients S (b + cLift)
    rw [map_add, map_add, hlifted, descendCoefficients_X_smul, map_add, add_assoc]
  have ha' : a = 0 := by
    simpa only [hv, hu, map_zero, add_zero] using huv.symm
  simpa only [Submodule.mem_bot] using ha'

/-- A polynomial generating subset whose own relation kernel is zero gives a finite
presentation of the coefficient module. -/
theorem finitePresentation_of_extension_ker_eq_bot (S : Finset (Extension R M))
    (hS : Submodule.span R[X] (S : Set (Extension R M)) = ⊤)
    (hK : LinearMap.ker
      (Finsupp.linearCombination R[X] ((↑) : S → Extension R M)) = ⊥) :
    Module.FinitePresentation R M := by
  classical
  refine { out := ⟨S.image (coefficientSum (R := R)),
    span_image_coefficientSum_eq_top S hS, ∅, ?_⟩ }
  rw [Finset.coe_empty, Submodule.span_empty,
    ker_linearCombination_image_coefficientSum_eq_bot S hS hK]

end PolynomialModule.Extension

namespace PolynomialModule.Extension

open scoped BigOperators

variable {R : Type u} {M : Type v} [Semiring R] [AddCommMonoid M] [Module R M]

private theorem exists_addUnit_preimage_of_surjective
    {I : Type w} (L : (I →₀ R[X]) →ₗ[R[X]] Extension R M)
    (hL : Function.Surjective L)
    (hUnitGen : ∀ m : M, IsAddUnit m →
      m ∈ Submodule.span R
        (Set.range (fun d : AddUnits R × M => (d.1 : R) • d.2)))
    {e eInv : Extension R M} (he : e + eInv = 0) :
    ∃ b bInv : I →₀ R[X], L b = e ∧ b + bInv = 0 := by
  classical
  let Y : M → I →₀ R[X] := fun m => Classical.choose (hL (single R 0 m))
  have hY (m : M) : L (Y m) = single R 0 m :=
    Classical.choose_spec (hL (single R 0 m))
  have hCoeff (n : ℕ) : IsAddUnit (e.coeff n) := by
    have hn : e.coeff n + eInv.coeff n = 0 := by
      have h := congrArg (fun q : Extension R M => q.coeff n) he
      simpa only [coeff_add, coeff_zero, Finsupp.add_apply, Finsupp.zero_apply] using h
    refine ⟨⟨e.coeff n, eInv.coeff n, hn, ?_⟩, rfl⟩
    rw [add_comm]
    exact hn
  have hrepr (n : ℕ) :
      ∃ c : (AddUnits R × M) →₀ R,
        c.sum (fun x a => a • ((x.1 : R) • x.2)) = e.coeff n :=
    Finsupp.mem_span_range_iff_exists_finsupp.mp (hUnitGen (e.coeff n) (hCoeff n))
  let d (n : ℕ) : (AddUnits R × M) →₀ R := Classical.choose (hrepr n)
  have hd (n : ℕ) :
      (d n).sum (fun x a => a • ((x.1 : R) • x.2)) = e.coeff n :=
    Classical.choose_spec (hrepr n)
  let b : I →₀ R[X] := ∑ n ∈ e.coeff.support,
    (Polynomial.X ^ n : R[X]) •
      ∑ x ∈ (d n).support, Polynomial.C (d n x * (x.1 : R)) • Y x.2
  let bInv : I →₀ R[X] := ∑ n ∈ e.coeff.support,
    (Polynomial.X ^ n : R[X]) •
      ∑ x ∈ (d n).support, Polynomial.C (d n x * x.1.neg) • Y x.2
  have hX (n : ℕ) (m : M) :
      (Polynomial.X ^ n : R[X]) • single R 0 m = single R n m := by
    induction n with
    | zero => simp only [pow_zero, one_smul]
    | succ n ih => rw [pow_succ', mul_smul, ih, X_smul_single]
  refine ⟨b, bInv, ?_, ?_⟩
  · calc
      L b = ∑ n ∈ e.coeff.support,
          (Polynomial.X ^ n : R[X]) • single R 0 (e.coeff n) := by
        simp only [b, map_sum, L.map_smul, hY]
        apply Finset.sum_congr rfl
        intro n hn
        apply congrArg (fun q : Extension R M => (Polynomial.X ^ n : R[X]) • q)
        calc
          (∑ x ∈ (d n).support,
              Polynomial.C (d n x * (x.1 : R)) • single R 0 x.2) =
              ∑ x ∈ (d n).support,
                single R 0 (d n x • ((x.1 : R) • x.2)) := by
            apply Finset.sum_congr rfl
            intro x hx
            rw [C_smul, ← single_smul, mul_smul]
          _ = single R 0 (e.coeff n) := by
            have h := congrArg (lsingle R (M := M) 0) (hd n)
            simpa only [Finsupp.sum, map_sum, lsingle_apply] using h
      _ = e.coeff.sum (single R) := by
        change (∑ n ∈ e.coeff.support,
          (Polynomial.X ^ n : R[X]) • single R 0 (e.coeff n)) =
            ∑ n ∈ e.coeff.support, single R n (e.coeff n)
        apply Finset.sum_congr rfl
        intro n hn
        exact hX n (e.coeff n)
      _ = e := sum_single e
  · dsimp only [b, bInv]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro n hn
    rw [← smul_add, ← Finset.sum_add_distrib]
    have hzero :
        (∑ x ∈ (d n).support,
          (Polynomial.C (d n x * (x.1 : R)) • Y x.2 +
            Polynomial.C (d n x * x.1.neg) • Y x.2)) = 0 := by
      apply Finset.sum_eq_zero
      intro x hx
      have hu : d n x * (x.1 : R) + d n x * x.1.neg = 0 := by
        rw [← mul_add, AddUnits.val_neg, mul_zero]
      rw [← add_smul, ← Polynomial.C_add, hu, map_zero, zero_smul]
    rw [hzero, smul_zero]

end PolynomialModule.Extension

namespace PolynomialModule.Extension

variable {R : Type u} {M : Type v} [Semiring R] [AddCommMonoid M] [Module R M]

private theorem scalarCoefficientSum_mul (p q : R[X]) :
    scalarCoefficientSum R (p * q) =
      scalarCoefficientSum R p * scalarCoefficientSum R q := by
  change Polynomial.eval₂ (RingHom.id R) 1 (p * q) =
    Polynomial.eval₂ (RingHom.id R) 1 p * Polynomial.eval₂ (RingHom.id R) 1 q
  exact Polynomial.eval₂_mul_noncomm _ _ (fun _ => Commute.one_right _)

private theorem descendCoefficients_smul (S : Finset (Extension R M))
    (p : R[X]) (f : S →₀ R[X]) :
    descendCoefficients S (p • f) =
      scalarCoefficientSum R p • descendCoefficients S f := by
  classical
  refine Finsupp.induction_linear f ?_ ?_ ?_
  · simp only [smul_zero, map_zero]
  · intro f g hf hg
    simp only [smul_add, map_add, hf, hg]
  · intro s q
    rw [Finsupp.smul_single', descendCoefficients_single,
      descendCoefficients_single, Finsupp.smul_single', scalarCoefficientSum_mul]

open Classical in
private theorem exists_mem_ker_descendCoefficients (S : Finset (Extension R M))
    (hS : Submodule.span R[X] (S : Set (Extension R M)) = ⊤)
    (hUnitGen : ∀ m : M, IsAddUnit m →
      m ∈ Submodule.span R
        (Set.range (fun d : AddUnits R × M => (d.1 : R) • d.2)))
    (a : S.image (coefficientSum (R := R)) →₀ R)
    (ha : a ∈ LinearMap.ker (Finsupp.linearCombination R
      ((↑) : S.image (coefficientSum (R := R)) → M))) :
    ∃ z : S →₀ R[X],
      z ∈ LinearMap.ker (Finsupp.linearCombination R[X] ((↑) : S → Extension R M)) ∧
        descendCoefficients S z = a := by
  let T := S.image (coefficientSum (R := R))
  let L := Finsupp.linearCombination R[X] ((↑) : S → Extension R M)
  have hL : Function.Surjective L := by
    apply (span_range_eq_top_iff_surjective_finsuppLinearCombination
      (R := R[X]) (v := ((↑) : S → Extension R M))).mp
    simpa only [Subtype.range_coe_subtype, Finset.setOfPred_mem] using hS
  have hEta : Function.Surjective (coefficientSumIndex S) := by
    intro t
    obtain ⟨s, hs, he⟩ := Finset.mem_image.mp t.property
    exact ⟨⟨s, hs⟩, Subtype.ext he⟩
  let rep : T → S := fun t => Classical.choose (hEta t)
  have hrep (t : T) : coefficientSumIndex S (rep t) = t :=
    Classical.choose_spec (hEta t)
  let c := freeConstant (R := R) S (Finsupp.lmapDomain R R rep a)
  have hc : descendCoefficients S c = a :=
    descendCoefficients_constant_section S rep hrep a
  have ha0 : Finsupp.linearCombination R ((↑) : T → M) a = 0 := ha
  have hq : coefficientSum (L c) = 0 := by
    calc
      coefficientSum (L c) = Finsupp.linearCombination R ((↑) : T → M)
          (descendCoefficients S c) := (linearCombination_descendCoefficients S c).symm
      _ = 0 := by rw [hc, ha0]
  obtain ⟨w, wInv, hw, hfix⟩ := exists_prefix_tail (L c) hq
  obtain ⟨b, bInv, hb, hbb⟩ :=
    exists_addUnit_preimage_of_surjective L hL hUnitGen hw
  have hbL : w + L bInv = 0 := by
    rw [← hb, ← map_add, hbb, map_zero]
  refine ⟨c + (X : R[X]) • b + bInv, ?_, ?_⟩
  · change L (c + (X : R[X]) • b + bInv) = 0
    rw [map_add, map_add, L.map_smul, hb, hfix, hbL]
  · rw [map_add, map_add, descendCoefficients_X_smul, hc, add_assoc,
      ← map_add, hbb, map_zero, add_zero]

open Classical in
private theorem span_image_descendCoefficients_eq_ker (S : Finset (Extension R M))
    (hS : Submodule.span R[X] (S : Set (Extension R M)) = ⊤)
    (hUnitGen : ∀ m : M, IsAddUnit m →
      m ∈ Submodule.span R
        (Set.range (fun d : AddUnits R × M => (d.1 : R) • d.2)))
    (k : Finset (S →₀ R[X]))
    (hk : Submodule.span R[X] (k : Set (S →₀ R[X])) =
      LinearMap.ker (Finsupp.linearCombination R[X] ((↑) : S → Extension R M))) :
    Submodule.span R
        (k.image (descendCoefficients S) :
          Set (S.image (coefficientSum (R := R)) →₀ R)) =
      LinearMap.ker (Finsupp.linearCombination R
        ((↑) : S.image (coefficientSum (R := R)) → M)) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro a ha
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp ha
    have hzK : Finsupp.linearCombination R[X] ((↑) : S → Extension R M) z = 0 := by
      have hz' : z ∈ Submodule.span R[X] (k : Set (S →₀ R[X])) :=
        Submodule.subset_span hz
      rw [hk] at hz'
      exact hz'
    change Finsupp.linearCombination R
      ((↑) : S.image (coefficientSum (R := R)) → M) (descendCoefficients S z) = 0
    rw [linearCombination_descendCoefficients, hzK, map_zero]
  · intro a ha
    obtain ⟨z, hz, hza⟩ := exists_mem_ker_descendCoefficients S hS hUnitGen a ha
    rw [← hza]
    have hzspan : z ∈ Submodule.span R[X] (k : Set (S →₀ R[X])) := by
      rw [hk]
      exact hz
    refine Submodule.span_induction (p := fun z _ =>
      descendCoefficients S z ∈ Submodule.span R
        (k.image (descendCoefficients S) :
          Set (S.image (coefficientSum (R := R)) →₀ R))) ?_ ?_ ?_ ?_ hzspan
    · intro z hz
      exact Submodule.subset_span (Finset.mem_image.mpr ⟨z, hz, rfl⟩)
    · simp only [map_zero, Submodule.zero_mem]
    · intro x y hx hy hx' hy'
      rw [map_add]
      exact Submodule.add_mem _ hx' hy'
    · intro p x hx hx'
      rw [descendCoefficients_smul]
      exact Submodule.smul_mem _ _ hx'

open Classical in
/-- If additive units of the coefficient module are spanned by additive-unit scalar
multiples, finite generation of the relations of a polynomial generating subset
implies finite generation of the relations of its coefficient-sum image. -/
theorem fg_ker_linearCombination_image_coefficientSum_of_addUnits_span
    (S : Finset (Extension R M))
    (hS : Submodule.span R[X] (S : Set (Extension R M)) = ⊤)
    (hUnitGen : ∀ m : M, IsAddUnit m →
      m ∈ Submodule.span R
        (Set.range (fun d : AddUnits R × M => (d.1 : R) • d.2)))
    (hK : (LinearMap.ker
      (Finsupp.linearCombination R[X] ((↑) : S → Extension R M))).FG) :
    (LinearMap.ker (Finsupp.linearCombination R
      ((↑) : S.image (coefficientSum (R := R)) → M))).FG := by
  classical
  obtain ⟨k, hk⟩ := hK
  exact ⟨k.image (descendCoefficients S),
    span_image_descendCoefficients_eq_ker S hS hUnitGen k hk⟩

/-- Finite presentation of the polynomial extension reflects to the coefficient module
when its additive units are spanned by additive-unit scalar multiples. -/
theorem finitePresentation_of_extension_of_isAddUnit_mem_span
    (hUnitGen : ∀ m : M, IsAddUnit m →
      m ∈ Submodule.span R
        (Set.range (fun d : AddUnits R × M => (d.1 : R) • d.2)))
    (hFP : Module.FinitePresentation R[X] (Extension R M)) :
    Module.FinitePresentation R M := by
  classical
  obtain ⟨S, hS, k, hk⟩ := hFP.out
  refine { out := ⟨S.image (coefficientSum (R := R)),
    span_image_coefficientSum_eq_top S hS, k.image (descendCoefficients S), ?_⟩ }
  exact span_image_descendCoefficients_eq_ker S hS hUnitGen k hk

/-- Under the additive-unit spanning hypothesis, the polynomial extension is finitely
presented exactly when the coefficient module is finitely presented. -/
theorem finitePresentation_extension_iff_of_isAddUnit_mem_span
    (hUnitGen : ∀ m : M, IsAddUnit m →
      m ∈ Submodule.span R
        (Set.range (fun d : AddUnits R × M => (d.1 : R) • d.2))) :
    Module.FinitePresentation R[X] (Extension R M) ↔ Module.FinitePresentation R M := by
  constructor
  · exact finitePresentation_of_extension_of_isAddUnit_mem_span hUnitGen
  · intro h
    let _ : Module.FinitePresentation R M := h
    infer_instance

end PolynomialModule.Extension
