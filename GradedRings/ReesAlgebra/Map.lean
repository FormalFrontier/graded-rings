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
image ideal and the target ideal.

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

end reesAlgebra
