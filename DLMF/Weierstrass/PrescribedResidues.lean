/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Weierstrass.Basic.ZetaProperties
import Mathlib.Tactic

/-!
# Elliptic functions with prescribed simple principal parts

For poles `aᵢ` and residues `rᵢ` whose sum is zero, the finite sum
`∑ rᵢ ζ(z - aᵢ)` is a meromorphic elliptic function. At pairwise incongruent poles
its principal part is exactly `rᵢ/(z-aᵢ)`. Its derivative is a finite sum of shifted
Weierstrass functions. No branch choices are involved. Repeated locations are allowed
in the construction; the local principal-part theorem states the separation it needs.

Sources: Lawden, *Elliptic Functions and Applications*, §8.11;
Koecher–Krieg, *Elliptic Functions and Modular Forms*, Chapter I, §6;
Armitage–Eberlein, *Elliptic Functions*, Chapter 7.
Quasi-periodicity is reused from TauCeti through the foundational zeta bridge.
-/

@[expose] public noncomputable section

open Complex PeriodPair

namespace DLMF.Weierstrass

variable {ι : Type*}

/-- The finite zeta sum with poles `aᵢ` and residues `rᵢ`, using the regular-part
totalization of `ζ` at its lattice poles. It is elliptic when the residues sum to zero. -/
def zetaSum (L : PeriodPair) (s : Finset ι) (a r : ι → ℂ) (z : ℂ) : ℂ :=
  ∑ i ∈ s, r i * weierstrassZeta L (z - a i)

/-- The defining finite-sum formula for the prescribed-residue construction. -/
theorem zetaSum_def (L : PeriodPair) (s : Finset ι) (a r : ι → ℂ) (z : ℂ) :
    zetaSum L s a r z = ∑ i ∈ s, r i * weierstrassZeta L (z - a i) := rfl

/-- The quasi-period of a zeta sum is the sum of the residues times the zeta quasi-period. -/
theorem zetaSum_add_coe (L : PeriodPair) (s : Finset ι) (a r : ι → ℂ)
    (z : ℂ) (w : L.lattice) :
    zetaSum L s a r (z + w) = zetaSum L s a r z + (∑ i ∈ s, r i) * L.quasiPeriod w := by
  simp only [zetaSum, weierstrassZeta_eq_periodPair_weierstrassZeta,
    add_sub_right_comm z (w : ℂ), L.weierstrassZeta_add_coe, mul_add,
    Finset.sum_add_distrib, Finset.sum_mul]

/-- Residues summing to zero give an elliptic zeta sum, including at totalized poles. -/
theorem periodic_zetaSum (L : PeriodPair) (s : Finset ι) (a r : ι → ℂ)
    (hr : ∑ i ∈ s, r i = 0) (w : L.lattice) :
    Function.Periodic (zetaSum L s a r) (w : ℂ) := by
  intro z
  rw [zetaSum_add_coe, hr, zero_mul, add_zero]

/-- A finite zeta sum is meromorphic everywhere, with or without residue balance. -/
theorem meromorphic_zetaSum (L : PeriodPair) (s : Finset ι) (a r : ι → ℂ) :
    Meromorphic (zetaSum L s a r) := by
  intro z
  apply MeromorphicAt.fun_sum
  intro i _hi
  exact (MeromorphicAt.const (r i) z).mul
    ((meromorphic_weierstrassZeta L (z - a i)).comp_analyticAt (g := fun w : ℂ => w - a i)
      (analyticAt_id.sub analyticAt_const))

/-- The derivative of a zeta sum on the complement of the specified lattice cosets. -/
theorem hasDerivAt_zetaSum (L : PeriodPair) (s : Finset ι) (a r : ι → ℂ) {z : ℂ}
    (hz : ∀ i ∈ s, z - a i ∉ L.lattice) :
    HasDerivAt (zetaSum L s a r) (∑ i ∈ s, -(r i * ℘[L] (z - a i))) z := by
  apply HasDerivAt.fun_sum
  intro i hi
  simpa using ((hasDerivAt_weierstrassZeta L (hz i hi)).comp z
    ((hasDerivAt_id z).sub_const (a i))).const_mul (r i)

/-- At a pole incongruent to all the other specified poles the singular part is
exactly the prescribed simple fraction; a zero prescribed residue is permitted. -/
theorem analyticAt_zetaSum_sub_principalPart (L : PeriodPair) (s : Finset ι)
    (a r : ι → ℂ) {j : ι} (hj : j ∈ s)
    (hsep : ∀ i ∈ s, i ≠ j → a j - a i ∉ L.lattice) :
    AnalyticAt ℂ (fun z => zetaSum L s a r z - r j / (z - a j)) (a j) := by
  classical
  have heq : (fun z => zetaSum L s a r z - r j / (z - a j)) =
      fun z => r j * (weierstrassZeta L (z - a j) - 1 / (z - a j)) +
        ∑ i ∈ s.erase j, r i * weierstrassZeta L (z - a i) := by
    funext z
    rw [zetaSum, ← Finset.sum_erase_add _ _ hj]
    ring
  rw [heq]
  apply AnalyticAt.add
  · have h₀ : AnalyticAt ℂ (fun u => weierstrassZeta L u - 1 / (u - 0)) (a j - a j) := by
      simpa only [sub_self] using analyticAt_weierstrassZeta_sub L (zero_mem L.lattice)
    have h := h₀.comp (f := fun z : ℂ => z - a j) (analyticAt_id.sub analyticAt_const)
    simpa using! analyticAt_const.mul h
  · apply Finset.analyticAt_fun_sum
    intro i hi
    exact analyticAt_const.mul
      ((analyticOnNhd_weierstrassZeta L _
        (hsep i (Finset.mem_of_mem_erase hi) (Finset.ne_of_mem_erase hi))).comp
          (f := fun z : ℂ => z - a i)
          (analyticAt_id.sub analyticAt_const))

end DLMF.Weierstrass
