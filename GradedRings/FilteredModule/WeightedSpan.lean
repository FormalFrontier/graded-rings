/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Filtration
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic.Abel

/-!
# Weighted generation of a separated filtration

Finite weighted lifts generating each successive quotient generate every stage of a
separated integer-indexed filtration, provided the coefficient ring is precomplete.
The coefficients and all finite linear combinations use the original module action.

The proof lifts coefficient sequences using `IsPrecomplete.prec`. A common natural
shift makes these sequences adic Cauchy. Finite telescoping then recovers their tails
at the original, unshifted weighted precisions; no separation of the coefficient
ring, closedness of ideals, or completeness of the target module is needed.

## Implementation notes

This is the independent filtered coefficient-lifting argument underlying the context
of Fujiwara--Kato, Proposition 0.7.5.2, not its full graded formulation. The equality
here is a semantic generalization: it assumes only precompleteness of the coefficient
ring, does not require the ideal to be finitely generated, and holds in every integer
degree, including negative degrees. The indexing family may be empty.

## References

* K. Fujiwara and F. Kato, *Foundations of Rigid Geometry I*,
  arXiv:1308.4734v5, Proposition 0.7.5.2, for the filtered-generation context.
-/

@[expose] public section

namespace Submodule

universe uR uM uι

variable {R : Type uR} [CommRing R]
variable {M : Type uM} [AddCommGroup M] [Module R M]
variable {ι : Type uι}

/-- Finite sums of weighted cyclic submodules have ordinary scalar coefficients. -/
private theorem mem_iSup_ideal_smul_span_singleton_iff [Fintype ι]
    (J : ι → Ideal R) (x : ι → M) (y : M) :
    y ∈ (⨆ i : ι, J i • span R ({x i} : Set M)) ↔
      ∃ c : ι → R, (∀ i, c i ∈ J i) ∧ ∑ i, c i • x i = y := by
  classical
  constructor
  · intro hy
    have hy' : y ∈ ⨆ i ∈ (Finset.univ : Finset ι),
        J i • span R ({x i} : Set M) := by
      simpa using hy
    obtain ⟨v, hv⟩ :=
      (mem_iSup_finset_iff_exists_sum
        (fun i => J i • span R ({x i} : Set M)) y).mp hy'
    have hv' : ∀ i, ∃ c ∈ J i, c • x i = (v i : M) := fun i =>
      mem_smul_span_singleton.mp (v i).property
    choose c hc hcv using hv'
    refine ⟨c, hc, ?_⟩
    calc
      ∑ i, c i • x i = ∑ i, (v i : M) :=
        Finset.sum_congr rfl fun i _ => hcv i
      _ = y := by simpa using hv
  · rintro ⟨c, hc, rfl⟩
    exact sum_mem_iSup fun i => mem_smul_span_singleton.mpr ⟨c i, hc i, rfl⟩

/-- Compatibility on an integer filtration, using its natural tail. -/
private theorem pow_smul_le_integer (I : Ideal R) (F : ℤ → Submodule R M)
    (hanti : Antitone F) (hcompat : ∀ z : ℤ, I • F z ≤ F (z + 1))
    (z : ℤ) (k : ℕ) : I ^ k • F z ≤ F (z + k) := by
  let T : I.Filtration M :=
    { N := fun t => F (z + t)
      mono := fun t => hanti (by omega)
      smul_le := fun t => by
        simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using hcompat (z + t) }
  simpa only [T, Nat.add_zero, Nat.cast_zero, add_zero] using T.pow_smul_le k 0

/-- An individual weighted coefficient acts into its required filtration stage. -/
private theorem weighted_smul_mem (I : Ideal R) (F : ℤ → Submodule R M)
    (hanti : Antitone F) (hcompat : ∀ z : ℤ, I • F z ≤ F (z + 1))
    (d : ℤ) (x : M) (hx : x ∈ F d) (z : ℤ) (c : R)
    (hc : c ∈ I ^ ((z - d).toNat)) : c • x ∈ F z := by
  have hmem : c • x ∈ I ^ ((z - d).toNat) • F d := smul_mem_smul hc hx
  have hstage := pow_smul_le_integer I F hanti hcompat d ((z - d).toNat) hmem
  exact hanti (by omega : z ≤ d + ((z - d).toNat : ℤ)) hstage

/-- Extract one finite family of updates, leaving a next-stage residual. -/
private theorem exists_weighted_update [Fintype ι]
    (I : Ideal R) (F : ℤ → Submodule R M) (d : ι → ℤ) (x : ι → M)
    (hgen : ∀ z : ℤ, F z ≤
      (⨆ i : ι, I ^ ((z - d i).toNat) • span R ({x i} : Set M)) ⊔ F (z + 1))
    (z : ℤ) (y : M) (hy : y ∈ F z) :
    ∃ a : ι → R, (∀ i, a i ∈ I ^ ((z - d i).toNat)) ∧
      y - ∑ i, a i • x i ∈ F (z + 1) := by
  obtain ⟨w, hw, r, hr, hwr⟩ := mem_sup.mp (hgen z hy)
  obtain ⟨a, ha, haw⟩ :=
    (mem_iSup_ideal_smul_span_singleton_iff
      (fun i => I ^ ((z - d i).toNat)) x w).mp hw
  refine ⟨a, ha, ?_⟩
  have heq : y - ∑ i, a i • x i = r := by
    rw [haw, ← hwr]
    abel
  rw [heq]
  exact hr

/-- Recursive updates give finite approximations and residuals at every natural stage. -/
private theorem exists_weighted_approximations [Fintype ι]
    (I : Ideal R) (F : ℤ → Submodule R M) (d : ι → ℤ) (x : ι → M)
    (hgen : ∀ z : ℤ, F z ≤
      (⨆ i : ι, I ^ ((z - d i).toNat) • span R ({x i} : Set M)) ⊔ F (z + 1))
    (n : ℤ) (y : M) (hy : y ∈ F n) :
    ∃ p : ℕ → ι → R,
      (∀ i, p 0 i = 0) ∧
      (∀ (t : ℕ) i, p (t + 1) i - p t i ∈ I ^ ((n + t - d i).toNat)) ∧
      ∀ (t : ℕ), y - ∑ i, p t i • x i ∈ F (n + t) := by
  classical
  let a : (t : ℕ) → F (n + t) → (ι → R) := fun t r =>
    Classical.choose (exists_weighted_update I F d x hgen (n + t) r r.property)
  have ha (t : ℕ) (r : F (n + t)) :
      (∀ i, a t r i ∈ I ^ ((n + t - d i).toNat)) ∧
      (r : M) - ∑ i, a t r i • x i ∈ F (n + t + 1) :=
    Classical.choose_spec
      (exists_weighted_update I F d x hgen (n + t) r r.property)
  let next : (t : ℕ) → F (n + t) → F (n + (t + 1 : ℕ)) := fun t r =>
    ⟨(r : M) - ∑ i, a t r i • x i, by
      simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using (ha t r).2⟩
  let r : (t : ℕ) → F (n + t) :=
    Nat.rec (motive := fun t => F (n + t)) ⟨y, by simpa using hy⟩ next
  let u : ℕ → ι → R := fun t => a t (r t)
  let p : ℕ → ι → R := fun t i => ∑ s ∈ Finset.range t, u s i
  have hrstep (t : ℕ) :
      (r (t + 1)).val = (r t).val - ∑ i, u t i • x i := by
    rfl
  have hpstep (t : ℕ) (i : ι) : p (t + 1) i = p t i + u t i := by
    simp only [p, Finset.sum_range_succ]
  have hres (t : ℕ) : y - ∑ i, p t i • x i = (r t).val := by
    induction t with
    | zero => simp [p, r]
    | succ t ih =>
      simp only [hpstep, add_smul, Finset.sum_add_distrib]
      rw [sub_add_eq_sub_sub, ih, hrstep]
  refine ⟨p, ?_, ?_, ?_⟩
  · intro i
    simp [p]
  · intro t i
    rw [hpstep]
    simpa only [add_sub_cancel_left] using (ha t (r t)).1 i
  · intro t
    rw [hres]
    exact (r t).property

/-- Finite telescoping controls every pair of approximations, not just neighbors. -/
private theorem coefficient_difference_mem (I : Ideal R)
    (e : ℕ → ℕ) (he : Monotone e) (p : ℕ → R)
    (hp : ∀ t, p (t + 1) - p t ∈ I ^ (e t))
    {s u : ℕ} (hsu : s ≤ u) : p u - p s ∈ I ^ (e s) := by
  induction u, hsu using Nat.le_induction with
  | base => simp
  | succ u hsu ih =>
    have hu : p (u + 1) - p u ∈ I ^ (e s) :=
      Ideal.pow_le_pow_right (he hsu) (hp u)
    have hsum := (I ^ (e s)).add_mem ih hu
    convert hsum using 1
    abel

/-- Precompleteness gives tails at the original weighted precisions without closed ideals. -/
private theorem exists_weighted_coefficient_limits [Finite ι]
    (I : Ideal R) [IsPrecomplete I R] (d : ι → ℤ) (n : ℤ)
    (p : ℕ → ι → R)
    (hp : ∀ (t : ℕ) i, p (t + 1) i - p t i ∈ I ^ ((n + t - d i).toNat)) :
    ∃ c : ι → R, ∀ i (t : ℕ), c i - p t i ∈ I ^ ((n + t - d i).toNat) := by
  classical
  let := Fintype.ofFinite ι
  have he (i : ι) : Monotone (fun t : ℕ => (n + t - d i).toNat) := by
    intro s t hst
    change (n + (s : ℤ) - d i).toNat ≤ (n + (t : ℤ) - d i).toNat
    omega
  have hdiff (i : ι) {s u : ℕ} (hsu : s ≤ u) :
      p u i - p s i ∈ I ^ ((n + s - d i).toNat) :=
    coefficient_difference_mem I _ (he i) (fun t => p t i) (fun t => hp t i) hsu
  -- The finite supremum is zero for an empty family.
  let a : ℕ := Finset.univ.sup fun i => (d i - n).toNat
  have hshift (i : ι) (k : ℕ) : k ≤ (n + (a + k : ℕ) - d i).toNat := by
    have hai : (d i - n).toNat ≤ a :=
      Finset.le_sup (f := fun i : ι => (d i - n).toNat) (Finset.mem_univ i)
    omega
  have hprec : ∀ i, ∃ c : R, ∀ k : ℕ, c - p (a + k) i ∈ I ^ k := by
    intro i
    have hcauchy : ∀ {k l : ℕ}, k ≤ l →
        p (a + k) i ≡ p (a + l) i [SMOD (I ^ k • ⊤ : Submodule R R)] := by
      intro k l hkl
      have htel := hdiff i (Nat.add_le_add_left hkl a)
      have hmem : p (a + l) i - p (a + k) i ∈ I ^ k :=
        Ideal.pow_le_pow_right (hshift i k) htel
      apply SModEq.sub_mem.mpr
      simpa only [Ideal.smul_eq_mul, Ideal.mul_top, neg_sub] using (I ^ k).neg_mem hmem
    obtain ⟨c, hc⟩ := IsPrecomplete.prec (I := I) (M := R) inferInstance hcauchy
    refine ⟨c, fun k => ?_⟩
    simpa only [Ideal.smul_eq_mul, Ideal.mul_top] using SModEq.sub_mem.mp ((hc k).symm)
  choose c hc using hprec
  refine ⟨c, ?_⟩
  intro i t
  -- Use a later finite approximation, at least as precise as the required weight.
  let k : ℕ := max ((n + t - d i).toNat) t
  have htk : t ≤ a + k := by omega
  have hek : (n + t - d i).toNat ≤ k := le_max_left _ _
  have hnear : c i - p (a + k) i ∈ I ^ ((n + t - d i).toNat) :=
    Ideal.pow_le_pow_right hek (hc i k)
  have htel := hdiff i htk
  have hsum := (I ^ ((n + t - d i).toNat)).add_mem hnear htel
  convert hsum using 1
  abel

/--
Finite weighted lifts generating every successive quotient of a separated integer
filtration generate every stage over a precomplete coefficient ring.

This is the independent filtered coefficient-lifting argument underlying the context
of Fujiwara--Kato, *Foundations of Rigid Geometry I*, Proposition 0.7.5.2. Unlike the
complete-base, finite-ideal setting there, this equality needs only `IsPrecomplete I R`,
not separation of `R` or finite generation of `I`. It uses the original `R`-module
action and holds in all integer degrees; it is not a full associated-graded statement.
-/
theorem eq_iSup_pow_smul_span_singleton_of_isPrecomplete [Finite ι]
    (I : Ideal R) [IsPrecomplete I R] (F : ℤ → Submodule R M)
    (hanti : Antitone F) (hcompat : ∀ n : ℤ, I • F n ≤ F (n + 1))
    (hsep : (⨅ n : ℤ, F n) = ⊥) (d : ι → ℤ) (x : ι → M)
    (hx : ∀ i : ι, x i ∈ F (d i))
    (hgen : ∀ n : ℤ, F n ≤
      (⨆ i : ι, (I ^ ((n - d i).toNat)) • Submodule.span R ({x i} : Set M)) ⊔ F (n + 1))
    (n : ℤ) :
    F n = ⨆ i : ι, (I ^ ((n - d i).toNat)) • Submodule.span R ({x i} : Set M) := by
  classical
  let := Fintype.ofFinite ι
  apply le_antisymm
  · intro y hy
    obtain ⟨p, hp0, hp, hres⟩ := exists_weighted_approximations I F d x hgen n y hy
    obtain ⟨c, hc⟩ := exists_weighted_coefficient_limits I d n p hp
    have hcmem (i : ι) : c i ∈ I ^ ((n - d i).toNat) := by
      simpa only [Nat.cast_zero, add_zero, hp0, sub_zero] using hc i 0
    have hv : (∑ i, c i • x i) ∈
        ⨆ i : ι, I ^ ((n - d i).toNat) • span R ({x i} : Set M) :=
      (mem_iSup_ideal_smul_span_singleton_iff
        (fun i => I ^ ((n - d i).toNat)) x _).mpr ⟨c, hcmem, rfl⟩
    have htail (t : ℕ) : y - ∑ i, c i • x i ∈ F (n + t) := by
      have hsum : (∑ i, (c i - p t i) • x i) ∈ F (n + t) :=
        (F (n + t)).sum_mem fun i _ =>
          weighted_smul_mem I F hanti hcompat (d i) (x i) (hx i) (n + t)
            (c i - p t i) (hc i t)
      have hmem := (F (n + t)).sub_mem (hres t) hsum
      convert hmem using 1
      simp only [sub_smul, Finset.sum_sub_distrib]
      abel
    have hall : y - ∑ i, c i • x i ∈ ⨅ z : ℤ, F z := by
      apply (mem_iInf F).mpr
      intro z
      have hz : z ≤ n + ((z - n).toNat : ℤ) := by omega
      exact hanti hz (htail (z - n).toNat)
    have heq : y = ∑ i, c i • x i := by
      apply sub_eq_zero.mp
      simpa only [hsep, mem_bot] using hall
    exact heq.symm ▸ hv
  · refine iSup_le fun i y hy => ?_
    obtain ⟨c, hc, rfl⟩ := mem_smul_span_singleton.mp hy
    exact weighted_smul_mem I F hanti hcompat (d i) (x i) (hx i) n c hc

end Submodule
