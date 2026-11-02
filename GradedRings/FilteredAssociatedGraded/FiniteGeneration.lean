/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GradedRings.FilteredAssociatedGraded.ReesAction
public import GradedRings.ReesAlgebra.QuotientPieces
public import GradedRings.FilteredModule.Finiteness

/-!
# Finite generation of integer-filtered associated graded modules

For the canonical quotient Rees action, homogeneous representatives span the
associated graded exactly when they generate every filtration stage modulo its
successor with ideal-power weights. Finiteness is equivalent to such generation
by a finite family. Over precomplete coefficients, separation gives exact
weighted descriptions and eventual stability; exhaustivity gives finiteness of
the original module. Finite generation of the ideal additionally gives finite
generation of every stage.

The coefficient-lifting step uses the original module action and requires neither
separation of the coefficient ring nor completeness of the target module. The
finite family may be empty, its weights may be negative, and the fixed-family
spanning criterion also permits infinite indexing types.

## References

* K. Fujiwara and F. Kato, *Foundations of Rigid Geometry I*,
  arXiv:1308.4734v5, Proposition 0.7.5.2, for the filtered-generation context.
  The precomplete-base assertions generalize the complete-base ingredient,
  and finite generation of the ideal is needed only for stage finiteness.
* Mathlib's additive direct-sum decomposition and finite-span extraction API.
-/

@[expose] public section

universe uR uM uι

namespace Ideal.IntFiltration

variable {R : Type uR} [CommRing R] {I : Ideal R}
variable {M : Type uM} [AddCommGroup M] [Module R M]
variable (F : I.IntFiltration M)

local notation "B" => reesAlgebra I
local notation "J" => I.map (algebraMap R B)
local notation "C" => B ⧸ J
local notation "G" => F.AssociatedGraded

/-- Finiteness over the quotient Rees algebra gives a finite family of original-stage
representatives whose homogeneous classes span the associated graded module. -/
theorem exists_fin_span_single_eq_top
    (hfinite : Module.Finite C F.AssociatedGraded) :
    ∃ (m : ℕ) (d : Fin m → ℤ) (x : Fin m → M)
      (hx : ∀ i : Fin m, x i ∈ F.N (d i)),
      Submodule.span C
        (Set.range (fun i : Fin m => F.single (d i) ⟨x i, hx i⟩)) = ⊤ := by
  classical
  let P := Σ n : ℤ, F.N n
  let k : P → G := fun p => F.single p.1 p.2
  have hspan : Submodule.span C (Set.range k) = ⊤ := by
    apply top_unique
    intro z _
    rw [← F.sum_support_inclusion z]
    apply Submodule.sum_mem
    intro n _
    obtain ⟨y, hy⟩ := F.cl_surjective n (F.component n z)
    rw [← hy, ← F.single_apply n y]
    exact Submodule.subset_span ⟨⟨n, y⟩, rfl⟩
  have hfg : (Submodule.span C (Set.range k)).FG := by
    rw [hspan]
    exact hfinite.fg_top
  obtain ⟨s, hs, hss⟩ :=
    (Submodule.fg_span_iff_fg_span_finset_subset (R := C) (Set.range k)).mp hfg
  have hs' : (s : Set G) ⊆ k '' (Set.univ : Set P) := by
    simpa only [Set.image_univ] using hs
  obtain ⟨t, _, hts⟩ := Finset.subset_set_image_iff.mp hs'
  obtain ⟨m, e, he⟩ := t.finite_toSet.fin_embedding
  refine ⟨m, fun i => (e i).1, fun i => ((e i).2 : M),
    fun i => (e i).2.property, ?_⟩
  change Submodule.span C (Set.range (fun i : Fin m => k (e i))) = ⊤
  rw [Set.range_comp', he, ← Finset.coe_image, hts, ← hss, hspan]

/-- A family of homogeneous representatives spans over the quotient Rees algebra
exactly when its weighted original-scalar spans generate every successive
quotient. The family need not be finite. -/
theorem span_single_eq_top_iff_weighted_generation
    {ι : Type uι} (d : ι → ℤ) (x : ι → M)
    (hx : ∀ i : ι, x i ∈ F.N (d i)) :
    Submodule.span C
        (Set.range (fun i : ι => F.single (d i) ⟨x i, hx i⟩)) = ⊤ ↔
      ∀ n : ℤ, F.N n ≤
        (⨆ i : ι, I ^ ((n - d i).toNat) •
          Submodule.span R ({x i} : Set M)) ⊔ F.N (n + 1) := by
  classical
  let W : ℤ → Submodule R M := fun n =>
    ⨆ i : ι, I ^ ((n - d i).toNat) • Submodule.span R ({x i} : Set M)
  let S : Submodule C G := Submodule.span C
    (Set.range (fun i : ι => F.single (d i) ⟨x i, hx i⟩))
  have hW (n : ℤ) : W n ≤ F.N n := by
    refine iSup_le fun i y hy => ?_
    obtain ⟨a, ha, rfl⟩ := Submodule.mem_smul_span_singleton.mp hy
    have hmem := F.pow_smul_le (n - d i).toNat (d i)
      (Submodule.smul_mem_smul ha (hx i))
    exact F.antitone (by omega : n ≤ d i + ((n - d i).toNat : ℤ)) hmem
  have hsingle_congr {n k : ℤ} (h : n = k) (m : F.N n) (m' : F.N k)
      (hm : (m : M) = (m' : M)) : F.single n m = F.single k m' := by
    subst k
    exact congrArg (F.single n) (Subtype.ext hm)
  change S = ⊤ ↔ ∀ n : ℤ, F.N n ≤ W n ⊔ F.N (n + 1)
  constructor
  · intro htop
    -- These are original-scalar images, not submodules over the quotient Rees ring.
    let L : (n : ℤ) → Submodule R (F.GradedPiece n) := fun n =>
      ((W n).comap (F.N n).subtype).map (F.cl n)
    have hscalar (n : ℤ) (i : ι) (c : C) :
        F.component n (c • F.single (d i) ⟨x i, hx i⟩) ∈ L n := by
      refine DirectSum.Decomposition.inductionOn
        (reesAlgebra.quotientHomogeneousComponent I) ?_ ?_ ?_ c
      · have hzero : (0 : C) • F.single (d i) ⟨x i, hx i⟩ = (0 : G) :=
          Module.zero_smul (R := C) _
        rw [hzero, (F.component n).map_zero]
        exact (L n).zero_mem
      · intro q c
        obtain ⟨z, rfl⟩ := (reesAlgebra.quotientMonomialEquiv I q).surjective c
        induction z using Submodule.Quotient.induction_on with
        | H a =>
          rw [reesAlgebra.quotientMonomialEquiv_mk, F.monomial_smul_single]
          let y : F.N (d i + (q : ℤ)) :=
            ⟨(a : R) • x i,
              F.pow_smul_le q (d i) (Submodule.smul_mem_smul a.property (hx i))⟩
          change F.component n (F.single (d i + (q : ℤ)) y) ∈ L n
          by_cases heq : d i + (q : ℤ) = n
          · have hexp : (n - d i).toNat = q := by omega
            have hw : (a : R) • x i ∈ W n := by
              apply Submodule.mem_iSup_of_mem i
              rw [hexp]
              exact Submodule.mem_smul_span_singleton.mpr ⟨(a : R), a.property, rfl⟩
            rw [hsingle_congr heq y ⟨(a : R) • x i, hW n hw⟩ rfl,
              F.component_single]
            exact Submodule.mem_map.mpr ⟨⟨(a : R) • x i, hW n hw⟩, hw, rfl⟩
          · rw [F.component_single_of_ne _ _ (Ne.symm heq)]
            exact (L n).zero_mem
      · intro c c' hc hc'
        rw [add_smul, map_add]
        exact (L n).add_mem hc hc'
    have hcomponent (n : ℤ) {z : G} (hz : z ∈ S) : F.component n z ∈ L n := by
      refine Submodule.closure_induction
        (p := fun z _ => F.component n z ∈ L n) ?_ ?_ ?_ hz
      · rw [map_zero]
        exact (L n).zero_mem
      · intro z z' _ _ hz hz'
        rw [map_add]
        exact (L n).add_mem hz hz'
      · rintro c _ ⟨i, rfl⟩
        exact hscalar n i c
    intro n m hm
    have hz : F.single n ⟨m, hm⟩ ∈ S := by
      rw [htop]
      exact Submodule.mem_top
    have hclass := hcomponent n hz
    rw [F.component_single] at hclass
    obtain ⟨y, hy, heq⟩ := Submodule.mem_map.mp hclass
    have htail : m - (y : M) ∈ F.N (n + 1) :=
      (F.cl_eq_cl_iff n ⟨m, hm⟩ y).mp heq.symm
    exact Submodule.mem_sup.mpr
      ⟨(y : M), hy, m - (y : M), htail, by rw [add_comm, sub_add_cancel]⟩
  · intro hgen
    have hsingle (n : ℤ) (m : F.N n) : F.single n m ∈ S := by
      have hweighted {y : M} (hy : y ∈ W n) :
          ∃ hyN : y ∈ F.N n, F.single n ⟨y, hyN⟩ ∈ S := by
        refine Submodule.iSup_induction
          (fun i : ι => I ^ ((n - d i).toNat) • Submodule.span R ({x i} : Set M))
          (motive := fun y => ∃ hyN : y ∈ F.N n, F.single n ⟨y, hyN⟩ ∈ S)
          hy ?_ ?_ ?_
        · intro i y hy
          have hyN : y ∈ F.N n := hW n (Submodule.mem_iSup_of_mem i hy)
          refine ⟨hyN, ?_⟩
          obtain ⟨a, ha, rfl⟩ := Submodule.mem_smul_span_singleton.mp hy
          by_cases hdi : d i ≤ n
          · let q : ℕ := (n - d i).toNat
            have heq : d i + (q : ℤ) = n := by dsimp [q]; omega
            have hmon : (Ideal.Quotient.mk J
                (reesAlgebra.monomial I q ⟨a, ha⟩) : C) •
                F.single (d i) ⟨x i, hx i⟩ ∈ S :=
              S.smul_mem _ (Submodule.subset_span ⟨i, rfl⟩)
            rw [F.monomial_smul_single] at hmon
            have he : F.single (d i + (q : ℤ))
                ⟨a • x i, F.pow_smul_le q (d i) (Submodule.smul_mem_smul ha (hx i))⟩ =
                F.single n ⟨a • x i, hyN⟩ :=
              hsingle_congr heq _ _ rfl
            rwa [he] at hmon
          · have hnext : a • x i ∈ F.N (n + 1) :=
              (F.N (n + 1)).smul_mem a (F.antitone (by omega) (hx i))
            rw [(F.single_eq_zero_iff n _).mpr hnext]
            exact S.zero_mem
        · refine ⟨(F.N n).zero_mem, ?_⟩
          change F.single n (0 : F.N n) ∈ S
          rw [map_zero]
          exact S.zero_mem
        · rintro y z ⟨hy, hyS⟩ ⟨hz, hzS⟩
          refine ⟨(F.N n).add_mem hy hz, ?_⟩
          change F.single n ((⟨y, hy⟩ : F.N n) + ⟨z, hz⟩) ∈ S
          rw [map_add]
          exact S.add_mem hyS hzS
      obtain ⟨y, hy, z, hz, hm⟩ := Submodule.mem_sup.mp (hgen n m.property)
      obtain ⟨hyN, hyS⟩ := hweighted hy
      have hzN : z ∈ F.N n := F.antitone (by omega) hz
      have hz0 : F.single n ⟨z, hzN⟩ = 0 := (F.single_eq_zero_iff n _).mpr hz
      have hm' : m = (⟨y, hyN⟩ : F.N n) + ⟨z, hzN⟩ := Subtype.ext hm.symm
      rw [hm', map_add, hz0, add_zero]
      exact hyS
    apply top_unique
    intro z _
    rw [← F.sum_support_inclusion z]
    exact S.sum_mem fun n _ => by
      obtain ⟨m, hm⟩ := F.cl_surjective n (F.component n z)
      rw [← hm, ← F.single_apply]
      exact hsingle n m

/-- The whole integer associated graded is finite over the canonical quotient
Rees algebra exactly when finitely many original-module representatives generate
all successive quotients with ideal-power weights. -/
theorem finite_associatedGraded_iff_exists_weighted_generation :
    Module.Finite C G ↔
      ∃ (k : ℕ) (d : Fin k → ℤ) (x : Fin k → M),
        (∀ i : Fin k, x i ∈ F.N (d i)) ∧
        ∀ n : ℤ, F.N n ≤
          (⨆ i : Fin k, I ^ ((n - d i).toNat) •
            Submodule.span R ({x i} : Set M)) ⊔ F.N (n + 1) := by
  constructor
  · intro hfinite
    obtain ⟨k, d, x, hx, hspan⟩ := F.exists_fin_span_single_eq_top hfinite
    exact ⟨k, d, x, hx,
      (F.span_single_eq_top_iff_weighted_generation d x hx).mp hspan⟩
  · rintro ⟨k, d, x, hx, hgen⟩
    have hspan := (F.span_single_eq_top_iff_weighted_generation d x hx).mpr hgen
    apply Module.Finite.of_fg_top
    rw [← hspan]
    exact Submodule.fg_span (Set.finite_range _)

/-- Over precomplete coefficients, finite generation of the associated graded of
a separated integer filtration gives an exact finite weighted expression for
every stage, including degrees below the generator weights. -/
theorem exists_eq_iSup_pow_smul_span_singleton_of_finite_associatedGraded
    [IsPrecomplete I R] [Module.Finite C G]
    (hsep : (⨅ n : ℤ, F.N n) = ⊥) :
    ∃ (k : ℕ) (d : Fin k → ℤ) (x : Fin k → M),
      (∀ i : Fin k, x i ∈ F.N (d i)) ∧
      ∀ n : ℤ, F.N n =
        ⨆ i : Fin k, I ^ ((n - d i).toNat) •
          Submodule.span R ({x i} : Set M) := by
  obtain ⟨k, d, x, hx, hgen⟩ :=
    (F.finite_associatedGraded_iff_exists_weighted_generation).mp inferInstance
  refine ⟨k, d, x, hx, ?_⟩
  intro n
  exact Submodule.eq_iSup_pow_smul_span_singleton_of_isPrecomplete
    I F.N F.antitone F.smul_le hsep d x hx hgen n

/-- Over precomplete coefficients, a separated integer filtration with finite
associated graded is eventually stable under multiplication by the ideal. -/
theorem exists_eq_smul_of_finite_associatedGraded
    [IsPrecomplete I R] [Module.Finite C G]
    (hsep : (⨅ n : ℤ, F.N n) = ⊥) :
    ∃ c : ℤ, ∀ n : ℤ, c ≤ n → F.N (n + 1) = I • F.N n := by
  obtain ⟨k, d, x, hx, hgen⟩ :=
    (F.finite_associatedGraded_iff_exists_weighted_generation).mp inferInstance
  exact Submodule.exists_eq_smul_of_weighted_generation
    I F.N F.antitone F.smul_le hsep d x hx hgen

/-- Over precomplete coefficients, finite generation of the associated graded of
a separated exhaustive integer filtration makes the original module finite. -/
theorem moduleFinite_of_finite_associatedGraded
    [IsPrecomplete I R] [Module.Finite C G]
    (hsep : (⨅ n : ℤ, F.N n) = ⊥)
    (hexhaustive : (⨆ n : ℤ, F.N n) = ⊤) :
    Module.Finite R M := by
  obtain ⟨k, d, x, hx, hgen⟩ :=
    (F.finite_associatedGraded_iff_exists_weighted_generation).mp inferInstance
  exact Submodule.moduleFinite_of_weighted_generation
    I F.N F.antitone F.smul_le hsep d x hx hgen hexhaustive

/-- For a finitely generated ideal, the stages of a separated integer filtration
over precomplete coefficients are finitely generated whenever its associated
graded is finite. Exhaustivity is not required. -/
theorem fg_of_finite_associatedGraded
    [IsPrecomplete I R] [Module.Finite C G]
    (hsep : (⨅ n : ℤ, F.N n) = ⊥) (hI : I.FG) (n : ℤ) :
    (F.N n).FG := by
  obtain ⟨k, d, x, hx, hgen⟩ :=
    (F.finite_associatedGraded_iff_exists_weighted_generation).mp inferInstance
  exact Submodule.fg_of_weighted_generation
    I F.N F.antitone F.smul_le hsep d x hx hgen hI n

end Ideal.IntFiltration
