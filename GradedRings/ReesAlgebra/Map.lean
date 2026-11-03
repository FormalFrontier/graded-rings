/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import Mathlib.Algebra.Polynomial.Eval.Coeff
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.ReesAlgebra

/-!
# Coefficient homomorphisms of Rees algebras

A ring homomorphism carrying one ideal into another induces a coefficient
homomorphism between their Rees algebras. Its underlying polynomial is the
coefficient map, and its kernel is characterized coefficientwise. Surjectivity
is equivalent to surjectivity on coefficients together with equality of the
image ideal and the target ideal. Injectivity is equivalent to injectivity on
coefficients. A coefficient-ring equivalence induces a ring equivalence to the
Rees algebra of the image ideal, compatible with inverses and composition.

The construction uses Mathlib's polynomial coefficient homomorphism,
subalgebra restriction, and ideal-image and ideal-power APIs.
-/

@[expose] public section

universe u v w

open scoped Polynomial

namespace reesAlgebra

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
variable {I : Ideal R} {J : Ideal S}

private theorem map_mem (f : R →+* S) (h : I.map f ≤ J) (p : reesAlgebra I) :
    Polynomial.map f (p : R[X]) ∈ reesAlgebra J := by
  refine (mem_reesAlgebra_iff J _).2 ?_
  intro n
  have hn : f ((p : R[X]).coeff n) ∈ (I ^ n).map f :=
    Ideal.mem_map_of_mem f ((mem_reesAlgebra_iff I _).1 p.property n)
  rw [Ideal.map_pow f I n] at hn
  simpa only [Polynomial.coeff_map] using (Ideal.pow_right_mono h n) hn

/-- The coefficient homomorphism of Rees algebras induced by a ring homomorphism
whose ideal image is contained in the target ideal. -/
noncomputable def map (f : R →+* S) (h : I.map f ≤ J) : reesAlgebra I →+* reesAlgebra J :=
  (Polynomial.mapRingHom f).restrict (reesAlgebra I) (reesAlgebra J)
    (fun p hp => by exact map_mem f h ⟨p, hp⟩)

/-- Coercing coefficient change to polynomials gives the polynomial coefficient map. -/
@[simp]
theorem coe_map (f : R →+* S) (h : I.map f ≤ J) (p : reesAlgebra I) :
    (map f h p : S[X]) = Polynomial.map f (p : R[X]) := by
  simp only [map, RingHom.coe_restrict_apply, Polynomial.coe_mapRingHom]

/-- Coefficient change applies the coefficient ring homomorphism in every degree. -/
theorem coeff_map (f : R →+* S) (h : I.map f ≤ J) (p : reesAlgebra I) (n : ℕ) :
    (map f h p : S[X]).coeff n = f ((p : R[X]).coeff n) := by
  rw [coe_map, Polynomial.coeff_map]

/-- Coefficient change along the identity fixes a Rees algebra. -/
@[simp]
theorem map_id (I : Ideal R) :
    map (RingHom.id R) (by simpa only [Ideal.map_id] using (le_refl I)) =
      RingHom.id (reesAlgebra I) := by
  apply RingHom.ext
  intro p
  apply Subtype.val_injective
  simpa only [RingHom.id_apply, coe_map] using
    (Polynomial.map_id (p := (p : R[X])))

section Composition

variable {T : Type w} [CommRing T] {K : Ideal T}

/-- Coefficient change commutes with composition of ring homomorphisms. -/
@[simp]
theorem map_comp (f : R →+* S) (g : S →+* T)
    (hIJ : I.map f ≤ J) (hJK : J.map g ≤ K) :
    (map g hJK).comp (map f hIJ) =
      map (g.comp f) (by
        simpa only [Ideal.map_map] using
          (Ideal.map_mono (f := g) hIJ).trans hJK) := by
  apply RingHom.ext
  intro p
  apply Subtype.val_injective
  simpa only [RingHom.comp_apply, coe_map] using
    (Polynomial.map_map f g (p : R[X]))

end Composition

/-- The kernel of coefficient change consists of elements whose coefficients
lie in the coefficient homomorphism's kernel. -/
theorem mem_ker_map_iff (f : R →+* S) (h : I.map f ≤ J) (p : reesAlgebra I) :
    p ∈ RingHom.ker (map f h) ↔
      ∀ n, (p : R[X]).coeff n ∈ RingHom.ker f := by
  constructor
  · intro hp n
    apply RingHom.mem_ker.mpr
    have hp0 : map f h p = 0 := RingHom.mem_ker.mp hp
    have hcoeff := congrArg (fun q : reesAlgebra J => (q : S[X]).coeff n) hp0
    simpa only [coeff_map, Subalgebra.coe_zero, Polynomial.coeff_zero] using hcoeff
  · intro hp
    apply RingHom.mem_ker.mpr
    apply Subtype.ext
    apply Polynomial.ext
    intro n
    rw [coeff_map, Subalgebra.coe_zero, Polynomial.coeff_zero]
    exact RingHom.mem_ker.mp (hp n)

private theorem surjective_map_conditions (f : R →+* S) (h : I.map f ≤ J)
    (hs : Function.Surjective (map f h)) :
    Function.Surjective f ∧ I.map f = J := by
  constructor
  · intro s
    let q : reesAlgebra J :=
      ⟨Polynomial.monomial 0 s, reesAlgebra.monomial_mem.mpr (by simp)⟩
    obtain ⟨p, hp⟩ := hs q
    refine ⟨(p : R[X]).coeff 0, ?_⟩
    calc
      f ((p : R[X]).coeff 0) = (map f h p : S[X]).coeff 0 :=
        (coeff_map f h p 0).symm
      _ = (Polynomial.monomial 0 s).coeff 0 :=
        congrArg (fun a : reesAlgebra J => (a : S[X]).coeff 0) hp
      _ = s := Polynomial.coeff_monomial_same 0 s
  · apply le_antisymm h
    intro s hsJ
    let q : reesAlgebra J :=
      ⟨Polynomial.monomial 1 s,
        reesAlgebra.monomial_mem.mpr (by simpa only [pow_one] using hsJ)⟩
    obtain ⟨p, hp⟩ := hs q
    have hpI : (p : R[X]).coeff 1 ∈ I := by
      simpa only [pow_one] using
        (mem_reesAlgebra_iff I (p : R[X])).mp p.property 1
    have hfs : f ((p : R[X]).coeff 1) = s := by
      calc
        f ((p : R[X]).coeff 1) = (map f h p : S[X]).coeff 1 :=
          (coeff_map f h p 1).symm
        _ = (Polynomial.monomial 1 s).coeff 1 :=
          congrArg (fun a : reesAlgebra J => (a : S[X]).coeff 1) hp
        _ = s := Polynomial.coeff_monomial_same 1 s
    rw [← hfs]
    exact Ideal.mem_map_of_mem f hpI

private theorem map_surjective_of_surjective (f : R →+* S) (h : I.map f ≤ J)
    (hf : Function.Surjective f) (hIJ : I.map f = J) :
    Function.Surjective (map f h) := by
  classical
  intro q
  have hlift : ∀ n : ℕ, ∃ a : R, a ∈ I ^ n ∧ f a = (q : S[X]).coeff n := by
    intro n
    apply (Ideal.mem_map_iff_of_surjective f hf).mp
    rw [Ideal.map_pow, hIJ]
    exact (mem_reesAlgebra_iff J _).mp q.property n
  choose a ha hfa using hlift
  let p : R[X] := Finset.sum (q : S[X]).support (fun n => Polynomial.monomial n (a n))
  have hpcoeff (n : ℕ) :
      p.coeff n = if n ∈ (q : S[X]).support then a n else 0 := by
    dsimp only [p]
    rw [Polynomial.finsetSum_coeff]
    by_cases hn : n ∈ (q : S[X]).support
    · rw [ite_eq_left hn]
      calc
        _ = (Polynomial.monomial n (a n)).coeff n := by
          apply Finset.sum_eq_single n
          · intro b _ hbn
            exact Polynomial.coeff_monomial_of_ne (a b) (Ne.symm hbn)
          · intro hnot
            exact (hnot hn).elim
        _ = a n := Polynomial.coeff_monomial_same n (a n)
    · rw [ite_eq_right hn]
      apply Finset.sum_eq_zero
      intro b hb
      apply Polynomial.coeff_monomial_of_ne
      intro hnb
      subst b
      exact hn hb
  have hp : p ∈ reesAlgebra I := by
    apply (mem_reesAlgebra_iff I p).mpr
    intro n
    rw [hpcoeff n]
    split_ifs
    · exact ha n
    · exact (I ^ n).zero_mem
  refine ⟨⟨p, hp⟩, ?_⟩
  apply Subtype.ext
  apply Polynomial.ext
  intro n
  rw [coeff_map]
  change f (p.coeff n) = (q : S[X]).coeff n
  rw [hpcoeff n]
  split_ifs with hn
  · exact hfa n
  · rw [map_zero, (Polynomial.notMem_support_iff).mp hn]

/-- Coefficient change is surjective exactly when the coefficient map is
surjective and its ideal image is the target ideal. -/
theorem map_surjective_iff (f : R →+* S) (h : I.map f ≤ J) :
    Function.Surjective (map f h) ↔ Function.Surjective f ∧ I.map f = J :=
  ⟨surjective_map_conditions f h, fun hs => map_surjective_of_surjective f h hs.1 hs.2⟩


/-- A coefficient homomorphism of Rees algebras is injective exactly when the
coefficient ring homomorphism is injective. -/
theorem map_injective_iff (f : R →+* S) (h : I.map f ≤ J) :
    Function.Injective (map f h) ↔ Function.Injective f := by
  constructor
  · intro hmap a b hab
    have hconst :
        map f h (algebraMap R (reesAlgebra I) a) =
          map f h (algebraMap R (reesAlgebra I) b) := by
      apply Subtype.ext
      simp only [coe_map, Subalgebra.coe_algebraMap, Polynomial.algebraMap_eq,
        Polynomial.map_C, hab]
    have hcoeff := congrArg (fun p : reesAlgebra I => (p : R[X]).coeff 0) (hmap hconst)
    simpa only [Subalgebra.coe_algebraMap, Polynomial.algebraMap_eq,
      Polynomial.coeff_C_zero] using hcoeff
  · intro hf p q hpq
    apply Subtype.ext
    apply Polynomial.map_injective f hf
    simpa only [coe_map] using congrArg (fun p : reesAlgebra J => (p : S[X])) hpq

/-- A coefficient-ring equivalence induces a ring equivalence from a Rees algebra
to the Rees algebra of the image ideal. -/
noncomputable def equivMap (e : R ≃+* S) (I : Ideal R) :
    reesAlgebra I ≃+* reesAlgebra (I.map (e : R →+* S)) :=
  RingEquiv.ofRingHom
    (map (I := I) (J := I.map (e : R →+* S)) (e : R →+* S) le_rfl)
    (map (I := I.map (e : R →+* S)) (J := I) (e.symm : S →+* R)
      (Ideal.map_of_equiv (I := I) e).le)
    (by
      apply RingHom.ext
      intro p
      apply Subtype.ext
      rw [RingHom.comp_apply, RingHom.id_apply]
      have h : (e : R →+* S).comp (e.symm : S →+* R) = RingHom.id S := by
        simpa only [RingEquiv.toRingHom_eq_coe] using
          RingEquiv.toRingHom_comp_symm_toRingHom e
      calc
        _ = Polynomial.map (e : R →+* S)
            (map (I := I.map (e : R →+* S)) (J := I) (e.symm : S →+* R)
              (Ideal.map_of_equiv (I := I) e).le p : R[X]) :=
          coe_map (I := I) (J := I.map (e : R →+* S)) (e : R →+* S) le_rfl _
        _ = Polynomial.map (e : R →+* S)
            (Polynomial.map (e.symm : S →+* R) (p : S[X])) :=
          congrArg (Polynomial.map (e : R →+* S))
            (coe_map (I := I.map (e : R →+* S)) (J := I) (e.symm : S →+* R)
              (Ideal.map_of_equiv (I := I) e).le p)
        _ = Polynomial.map ((e : R →+* S).comp (e.symm : S →+* R)) (p : S[X]) :=
          Polynomial.map_map (e.symm : S →+* R) (e : R →+* S) (p : S[X])
        _ = Polynomial.map (RingHom.id S) (p : S[X]) :=
          congrArg (fun f : S →+* S => Polynomial.map f (p : S[X])) h
        _ = (p : S[X]) := Polynomial.map_id (p := (p : S[X])))
    (by
      apply RingHom.ext
      intro p
      apply Subtype.ext
      rw [RingHom.comp_apply, RingHom.id_apply]
      have h : (e.symm : S →+* R).comp (e : R →+* S) = RingHom.id R := by
        simpa only [RingEquiv.toRingHom_eq_coe] using
          RingEquiv.symm_toRingHom_comp_toRingHom e
      calc
        _ = Polynomial.map (e.symm : S →+* R)
            (map (I := I) (J := I.map (e : R →+* S)) (e : R →+* S) le_rfl p : S[X]) :=
          coe_map (I := I.map (e : R →+* S)) (J := I) (e.symm : S →+* R)
            (Ideal.map_of_equiv (I := I) e).le _
        _ = Polynomial.map (e.symm : S →+* R)
            (Polynomial.map (e : R →+* S) (p : R[X])) :=
          congrArg (Polynomial.map (e.symm : S →+* R))
            (coe_map (I := I) (J := I.map (e : R →+* S)) (e : R →+* S) le_rfl p)
        _ = Polynomial.map ((e.symm : S →+* R).comp (e : R →+* S)) (p : R[X]) :=
          Polynomial.map_map (e : R →+* S) (e.symm : S →+* R) (p : R[X])
        _ = Polynomial.map (RingHom.id R) (p : R[X]) :=
          congrArg (fun f : R →+* R => Polynomial.map f (p : R[X])) h
        _ = (p : R[X]) := Polynomial.map_id (p := (p : R[X])))

/-- The polynomial underlying a coefficient equivalence is the coefficient map. -/
@[simp]
theorem coe_equivMap (e : R ≃+* S) (I : Ideal R) (p : reesAlgebra I) :
    ((equivMap e I : reesAlgebra I ≃+* reesAlgebra (I.map (e : R →+* S))) p : S[X]) =
      Polynomial.map (e : R →+* S) (p : R[X]) := by
  have h : (equivMap e I : reesAlgebra I →+* reesAlgebra (I.map (e : R →+* S))) =
      map (I := I) (J := I.map (e : R →+* S)) (e : R →+* S) le_rfl := by
    unfold equivMap
    exact RingEquiv.coe_ringHom_ofRingHom _ _ _ _
  exact (congrArg
    (fun f : reesAlgebra I →+* reesAlgebra (I.map (e : R →+* S)) => (f p : S[X])) h).trans
      (coe_map (e : R →+* S) le_rfl p)

/-- A coefficient equivalence applies the ring equivalence to each coefficient. -/
theorem coeff_equivMap (e : R ≃+* S) (I : Ideal R) (p : reesAlgebra I) (n : ℕ) :
    (equivMap e I p : S[X]).coeff n = e ((p : R[X]).coeff n) := by
  rw [coe_equivMap, Polynomial.coeff_map, RingEquiv.coe_toRingHom]

/-- The inverse coefficient equivalence maps polynomial coefficients by the inverse ring
equivalence. -/
@[simp]
theorem coe_equivMap_symm (e : R ≃+* S) (I : Ideal R)
    (p : reesAlgebra (I.map (e : R →+* S))) :
    ((equivMap e I : reesAlgebra I ≃+* reesAlgebra (I.map (e : R →+* S))).symm p : R[X]) =
      Polynomial.map (e.symm : S →+* R) (p : S[X]) := by
  have h : ((equivMap e I).symm : reesAlgebra (I.map (e : R →+* S)) →+* reesAlgebra I) =
      map (I := I.map (e : R →+* S)) (J := I) (e.symm : S →+* R)
        (Ideal.map_of_equiv (I := I) e).le := by
    unfold equivMap
    rw [RingEquiv.ofRingHom_symm]
    exact RingEquiv.coe_ringHom_ofRingHom _ _ _ _
  exact (congrArg
    (fun f : reesAlgebra (I.map (e : R →+* S)) →+* reesAlgebra I => (f p : R[X])) h).trans
      (coe_map (e.symm : S →+* R) (Ideal.map_of_equiv (I := I) e).le p)

/-- The coefficients of the inverse equivalence are obtained by the inverse coefficient
ring equivalence. -/
theorem coeff_equivMap_symm (e : R ≃+* S) (I : Ideal R)
    (p : reesAlgebra (I.map (e : R →+* S))) (n : ℕ) :
    ((equivMap e I).symm p : R[X]).coeff n = e.symm ((p : S[X]).coeff n) := by
  rw [coe_equivMap_symm, Polynomial.coeff_map, RingEquiv.coe_toRingHom]

private theorem coe_ringEquiv_cast {K L : Ideal R} (h : K = L) (p : reesAlgebra K) :
    (RingEquiv.cast (R := fun H : Ideal R => reesAlgebra H) h p : R[X]) = (p : R[X]) := by
  cases h
  rfl

/-- Coefficient transport by the identity equivalence is the identity after identifying
its image ideal with the original ideal. -/
theorem equivMap_refl (I : Ideal R) :
    (equivMap (RingEquiv.refl R) I).trans
      (RingEquiv.cast (R := fun H : Ideal R => reesAlgebra H)
        (show I.map (RingEquiv.refl R : R →+* R) = I from by
          have h : (RingEquiv.refl R : R →+* R) = RingHom.id R := by
            simpa only [RingEquiv.toRingHom_eq_coe] using
              (RingEquiv.toRingHom_refl (R := R))
          exact (congrArg (fun f : R →+* R => I.map f) h).trans (Ideal.map_id I))) =
      RingEquiv.refl (reesAlgebra I) := by
  apply RingEquiv.ext
  intro p
  apply Subtype.ext
  rw [RingEquiv.trans_apply]
  rw [coe_ringEquiv_cast]
  calc
    (equivMap (RingEquiv.refl R) I p : R[X]) =
        Polynomial.map (RingEquiv.refl R : R →+* R) (p : R[X]) :=
      coe_equivMap (RingEquiv.refl R) I p
    _ = Polynomial.map (RingHom.id R) (p : R[X]) :=
      congrArg (fun f : R →+* R => Polynomial.map f (p : R[X])) (by
        simpa only [RingEquiv.toRingHom_eq_coe] using (RingEquiv.toRingHom_refl (R := R)))
    _ = (p : R[X]) := Polynomial.map_id (p := (p : R[X]))

/-- The inverse coefficient equivalence agrees with transport by the inverse ring
equivalence after identifying the double image ideal. -/
theorem equivMap_symm (e : R ≃+* S) (I : Ideal R) :
    (equivMap e I).symm =
      (equivMap e.symm (I.map (e : R →+* S))).trans
        (RingEquiv.cast (R := fun H : Ideal R => reesAlgebra H)
          (Ideal.map_of_equiv (I := I) e)) := by
  apply RingEquiv.ext
  intro p
  apply Subtype.ext
  calc
    ((equivMap e I).symm p : R[X]) =
        Polynomial.map (e.symm : S →+* R) (p : S[X]) :=
      coe_equivMap_symm e I p
    _ = (equivMap e.symm (I.map (e : R →+* S)) p : R[X]) :=
      (coe_equivMap e.symm (I.map (e : R →+* S)) p).symm
    _ = (RingEquiv.cast (R := fun H : Ideal R => reesAlgebra H)
        (Ideal.map_of_equiv (I := I) e)
        (equivMap e.symm (I.map (e : R →+* S)) p) : R[X]) :=
      (coe_ringEquiv_cast (Ideal.map_of_equiv (I := I) e)
        (equivMap e.symm (I.map (e : R →+* S)) p)).symm
    _ = (((equivMap e.symm (I.map (e : R →+* S))).trans
        (RingEquiv.cast (R := fun H : Ideal R => reesAlgebra H)
          (Ideal.map_of_equiv (I := I) e))) p : R[X]) :=
      congrArg (fun q : reesAlgebra I => (q : R[X]))
        (RingEquiv.trans_apply (equivMap e.symm (I.map (e : R →+* S)))
          (RingEquiv.cast (R := fun H : Ideal R => reesAlgebra H)
            (Ideal.map_of_equiv (I := I) e)) p).symm

/-- Coefficient equivalences respect composition after the standard identification
of sequential and composite image ideals. -/
theorem equivMap_trans {T : Type w} [CommRing T]
    (e : R ≃+* S) (d : S ≃+* T) (I : Ideal R) :
    ((equivMap e I).trans (equivMap d (I.map (e : R →+* S)))).trans
      (RingEquiv.cast (R := fun H : Ideal T => reesAlgebra H)
        (show (I.map (e : R →+* S)).map (d : S →+* T) = I.map (e.trans d : R →+* T) from by
          have h : (d : S →+* T).comp (e : R →+* S) = (e.trans d : R →+* T) := by
            simpa only [RingEquiv.toRingHom_eq_coe] using
              (RingEquiv.toRingHom_trans e d).symm
          exact (Ideal.map_map (I := I) (e : R →+* S) (d : S →+* T)).trans
            (congrArg (fun f : R →+* T => I.map f) h))) =
      equivMap (e.trans d) I := by
  apply RingEquiv.ext
  intro p
  apply Subtype.ext
  rw [RingEquiv.trans_apply]
  rw [coe_ringEquiv_cast]
  rw [RingEquiv.trans_apply]
  calc
    (equivMap d (I.map (e : R →+* S)) (equivMap e I p) : T[X]) =
        Polynomial.map (d : S →+* T) (equivMap e I p : S[X]) :=
      coe_equivMap d (I.map (e : R →+* S)) (equivMap e I p)
    _ = Polynomial.map (d : S →+* T) (Polynomial.map (e : R →+* S) (p : R[X])) :=
      congrArg (Polynomial.map (d : S →+* T)) (coe_equivMap e I p)
    _ = Polynomial.map ((d : S →+* T).comp (e : R →+* S)) (p : R[X]) :=
      Polynomial.map_map (e : R →+* S) (d : S →+* T) (p : R[X])
    _ = Polynomial.map (e.trans d : R →+* T) (p : R[X]) :=
      congrArg (fun f : R →+* T => Polynomial.map f (p : R[X])) (by
        simpa only [RingEquiv.toRingHom_eq_coe] using (RingEquiv.toRingHom_trans e d).symm)
    _ = (equivMap (e.trans d) I p : T[X]) :=
      (coe_equivMap (e.trans d) I p).symm

end reesAlgebra
