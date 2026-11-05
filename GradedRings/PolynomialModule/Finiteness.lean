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
change-of-generators principle is used.

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
