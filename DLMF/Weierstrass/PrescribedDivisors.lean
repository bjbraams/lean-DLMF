/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Weierstrass.Basic.ZetaProperties
public import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Tactic

/-!
# Balanced sigma products

Finite products of shifted sigma functions construct elliptic functions with prescribed
zeros and poles. Equal numbers of factors cancel the sign and constant multipliers;
equality of the sums of their locations cancels the exponential multiplier. Repeated
locations encode multiplicities. Empty products give the constant one.

Sources: Chandrasekharan, *Elliptic Functions*, Chapter IV, §3, Theorem 4, pp. 54–55;
Lawden, *Elliptic Functions and Applications*, §8.9;
Koecher–Krieg, *Elliptic Functions and Modular Forms*, Chapter I, §6.
The balance hypothesis concerns chosen complex representatives, rather than just their
classes modulo the lattice. Shifting representatives gives the usual divisor condition.
All sigma identities are taken from the project's foundational lattice-product API.
-/

@[expose] public noncomputable section

open Complex PeriodPair

namespace DLMF.Weierstrass

attribute [local instance] Classical.propDecidable

variable {ι : Type*}

/-- A finite product of sigma functions with shifted zeros, repeated according to
multiplicity; it is entire in `z`. -/
def sigmaProduct (L : PeriodPair) (s : Finset ι) (a : ι → ℂ) (z : ℂ) : ℂ :=
  ∏ i ∈ s, weierstrassSigma L (z - a i)

/-- The product formula for shifted sigma factors. -/
theorem sigmaProduct_def (L : PeriodPair) (s : Finset ι) (a : ι → ℂ) (z : ℂ) :
    sigmaProduct L s a z = ∏ i ∈ s, weierstrassSigma L (z - a i) := rfl

/-- A quotient of sigma products with equally many zero and pole factors. At zeros of
the denominator this uses Lean's totalized division; divisor statements use meromorphic orders. -/
def sigmaQuotient (L : PeriodPair) (s : Finset ι) (a b : ι → ℂ) (z : ℂ) : ℂ :=
  sigmaProduct L s a z / sigmaProduct L s b z

/-- The quotient formula for the prescribed-divisor construction. -/
theorem sigmaQuotient_def (L : PeriodPair) (s : Finset ι) (a b : ι → ℂ) (z : ℂ) :
    sigmaQuotient L s a b z = sigmaProduct L s a z / sigmaProduct L s b z := rfl

/-- The empty sigma quotient is the constant one. -/
@[simp]
theorem sigmaQuotient_empty (L : PeriodPair) (a b : ι → ℂ) (z : ℂ) :
    sigmaQuotient L ∅ a b z = 1 := by simp [sigmaQuotient, sigmaProduct]

/-- A sigma product vanishes precisely in one of the specified lattice classes. -/
theorem sigmaProduct_eq_zero_iff (L : PeriodPair) (s : Finset ι) (a : ι → ℂ) (z : ℂ) :
    sigmaProduct L s a z = 0 ↔ ∃ i ∈ s, z - a i ∈ L.lattice := by
  classical
  simp [sigmaProduct, Finset.prod_eq_zero_iff, weierstrassSigma_eq_zero_iff]

/-- Finite sigma products are analytic everywhere. -/
theorem analyticAt_sigmaProduct (L : PeriodPair) (s : Finset ι) (a : ι → ℂ) (z : ℂ) :
    AnalyticAt ℂ (sigmaProduct L s a) z := by
  apply Finset.analyticAt_fun_prod
  intro i _hi
  exact ((differentiable_weierstrassSigma L).analyticAt (z - a i)).comp
    (f := fun u : ℂ => u - a i) (analyticAt_id.sub analyticAt_const)

/-- The period multiplier of a sigma product depends only on the number and sum
of its zero locations. The same nonzero constant works for every finite product. -/
theorem exists_sigmaProduct_add_coe (L : PeriodPair) (w : L.lattice) :
    ∃ κ : ℂ, κ ≠ 0 ∧ ∀ (s : Finset ι) (a : ι → ℂ) (z : ℂ),
      sigmaProduct L s a (z + w) = κ ^ s.card *
        exp (L.quasiPeriod w * (s.card * z - ∑ i ∈ s, a i)) * sigmaProduct L s a z := by
  obtain ⟨κ, hκ, hσ⟩ := exists_weierstrassSigma_add_mem L w.2 L.ω₁_div_two_notMem_lattice
  have hσ' (u : ℂ) : weierstrassSigma L (u + w) =
      κ * exp (L.quasiPeriod w * u) * weierstrassSigma L u := by
    simpa only [weierstrassZeta_eq_periodPair_weierstrassZeta,
      L.weierstrassZeta_add_coe, add_sub_cancel_left] using hσ u
  refine ⟨κ, hκ, fun s a z => ?_⟩
  calc
    sigmaProduct L s a (z + w) =
        ∏ i ∈ s, κ * exp (L.quasiPeriod w * (z - a i)) * weierstrassSigma L (z - a i) := by
      apply Finset.prod_congr rfl
      intro i _hi
      rw [add_sub_right_comm, hσ']
    _ = κ ^ s.card * (∏ i ∈ s, exp (L.quasiPeriod w * (z - a i))) *
        sigmaProduct L s a z := by
      simp only [Finset.prod_mul_distrib, Finset.prod_const, sigmaProduct]
    _ = _ := by
      rw [← exp_sum]
      congr 3
      rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]

/-- Equal sums of zero and pole representatives make a sigma quotient elliptic,
including at totalized zeros of its denominator. -/
theorem periodic_sigmaQuotient (L : PeriodPair) (s : Finset ι) (a b : ι → ℂ)
    (hbalance : ∑ i ∈ s, a i = ∑ i ∈ s, b i) (w : L.lattice) :
    Function.Periodic (sigmaQuotient L s a b) (w : ℂ) := by
  obtain ⟨κ, hκ, hp⟩ := exists_sigmaProduct_add_coe (ι := ι) L w
  intro z
  simp only [sigmaQuotient, hp, hbalance]
  exact mul_div_mul_left _ _
    (mul_ne_zero (pow_ne_zero _ hκ) (Complex.exp_ne_zero _))

/-- A sigma quotient is meromorphic on the entire plane. -/
theorem meromorphic_sigmaQuotient (L : PeriodPair) (s : Finset ι) (a b : ι → ℂ) :
    Meromorphic (sigmaQuotient L s a b) := by
  intro z
  exact (analyticAt_sigmaProduct L s a z).meromorphicAt.div
    (analyticAt_sigmaProduct L s b z).meromorphicAt

/-- Away from the denominator's zero classes, the zeros are exactly the prescribed ones. -/
theorem sigmaQuotient_eq_zero_iff (L : PeriodPair) (s : Finset ι) (a b : ι → ℂ) (z : ℂ)
    (hb : ∀ i ∈ s, z - b i ∉ L.lattice) :
    sigmaQuotient L s a b z = 0 ↔ ∃ i ∈ s, z - a i ∈ L.lattice := by
  have hden : sigmaProduct L s b z ≠ 0 := by
    intro h
    obtain ⟨i, hi, hz⟩ := (sigmaProduct_eq_zero_iff L s b z).mp h
    exact hb i hi hz
  rw [sigmaQuotient, div_eq_zero_iff, or_iff_left hden, sigmaProduct_eq_zero_iff]

/-- The meromorphic order of sigma is one on its lattice and zero elsewhere. -/
theorem meromorphicOrderAt_weierstrassSigma (L : PeriodPair) (z : ℂ) :
    meromorphicOrderAt (weierstrassSigma L) z = if z ∈ L.lattice then 1 else 0 := by
  have han := (differentiable_weierstrassSigma L).analyticAt z
  rw [han.meromorphicOrderAt_eq]
  by_cases hz : z ∈ L.lattice
  · rw [ite_eq_left hz, han.analyticOrderAt_eq_one_of_zero_deriv_ne_zero
      (weierstrassSigma_eq_zero_of_mem L hz) (deriv_weierstrassSigma_ne_zero L hz)]
    rfl
  · rw [ite_eq_right hz, han.analyticOrderAt_eq_zero.mpr
      ((weierstrassSigma_eq_zero_iff L).not.mpr hz)]
    rfl

/-- Sigma quotients realize the prescribed divisor with all multiplicities and
cancellations. In particular this describes their poles despite totalized division. -/
theorem meromorphicOrderAt_sigmaQuotient (L : PeriodPair) (s : Finset ι)
    (a b : ι → ℂ) (z : ℂ) :
    meromorphicOrderAt (sigmaQuotient L s a b) z =
      (∑ i ∈ s, if z - a i ∈ L.lattice then (1 : WithTop ℤ) else 0) -
        ∑ i ∈ s, if z - b i ∈ L.lattice then (1 : WithTop ℤ) else 0 := by
  have hprod (a : ι → ℂ) : meromorphicOrderAt (sigmaProduct L s a) z =
      ∑ i ∈ s, if z - a i ∈ L.lattice then (1 : WithTop ℤ) else 0 := by
    have hdef : sigmaProduct L s a = fun u => ∏ i ∈ s, weierstrassSigma L (u - a i) := rfl
    rw [hdef, meromorphicOrderAt_fun_prod (s := s)
      (f := fun i u => weierstrassSigma L (u - a i)) (fun i _ =>
        (((differentiable_weierstrassSigma L).analyticAt (z - a i)).comp
          (f := fun u : ℂ => u - a i) (analyticAt_id.sub analyticAt_const)).meromorphicAt)]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [meromorphicOrderAt_fun_comp_sub_const_eq_meromorphicOrderAt,
      meromorphicOrderAt_weierstrassSigma]
  calc
    meromorphicOrderAt (sigmaQuotient L s a b) z =
        meromorphicOrderAt (sigmaProduct L s a / sigmaProduct L s b) z := rfl
    _ = _ := by
      rw [meromorphicOrderAt_div (analyticAt_sigmaProduct L s a z).meromorphicAt
        (analyticAt_sigmaProduct L s b z).meromorphicAt, hprod a, hprod b]

/-- The sufficient half of Abel's theorem for a complex torus: equal-degree finite
zero and pole lists whose sums agree modulo the lattice are the divisor of an elliptic
function. No separation is required; common classes cancel in the asserted orders. -/
theorem exists_elliptic_with_prescribed_orders (L : PeriodPair) (s : Finset ι)
    (a b : ι → ℂ) (hbalance : (∑ i ∈ s, a i) - ∑ i ∈ s, b i ∈ L.lattice) :
    ∃ f : ℂ → ℂ, Meromorphic f ∧ (∀ w : L.lattice, Function.Periodic f (w : ℂ)) ∧
      ∀ z, meromorphicOrderAt f z =
        (∑ i ∈ s, if z - a i ∈ L.lattice then (1 : WithTop ℤ) else 0) -
          ∑ i ∈ s, if z - b i ∈ L.lattice then (1 : WithTop ℤ) else 0 := by
  classical
  by_cases hs : s = ∅
  · subst s
    refine ⟨sigmaQuotient L ∅ a b, meromorphic_sigmaQuotient L ∅ a b,
      fun w => periodic_sigmaQuotient L ∅ a b (by simp) w,
      meromorphicOrderAt_sigmaQuotient L ∅ a b⟩
  obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.mpr hs
  let δ := (∑ i ∈ s, a i) - ∑ i ∈ s, b i
  let b' := Function.update b j (b j + δ)
  have hsum : ∑ i ∈ s, b' i = ∑ i ∈ s, a i := by
    rw [Finset.sum_update_of_mem hj]
    dsimp only [δ]
    have hsumb : (∑ i ∈ s \ {j}, b i) + b j = ∑ i ∈ s, b i := by
      simpa only [Finset.sdiff_singleton_eq_erase] using Finset.sum_erase_add s b hj
    linear_combination hsumb
  have hclass (z : ℂ) (i : ι) : z - b' i ∈ L.lattice ↔ z - b i ∈ L.lattice := by
    by_cases hij : i = j
    · subst i
      simp only [b', Function.update_self]
      constructor
      · intro h
        convert add_mem h hbalance using 1
        dsimp only [δ]
        ring
      · intro h
        convert sub_mem h hbalance using 1
        dsimp only [δ]
        ring
    · simp [b', Function.update_of_ne hij]
  refine ⟨sigmaQuotient L s a b', meromorphic_sigmaQuotient L s a b',
    fun w => periodic_sigmaQuotient L s a b' hsum.symm w, fun z => ?_⟩
  rw [meromorphicOrderAt_sigmaQuotient]
  simp only [hclass]

end DLMF.Weierstrass
