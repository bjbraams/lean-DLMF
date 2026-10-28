/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Hypergeometric.FiniteConvolution
public import DLMF.Hypergeometric.ArgumentContinuation
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Matroid.Init
public import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Gauss summation for regularized coefficients on the boundary

At a singular denominator parameter, the zero initial coefficients are removed
before applying the proved ordinary Gauss summation theorem. The reciprocal Gamma
recurrence avoids division by a possibly vanishing numerator Pochhammer symbol.
-/

@[expose] public section
open Complex Filter
open scoped Nat Topology
noncomputable section
namespace DLMF.Hypergeometric

/-- Gauss summation of regularized coefficients at a regular denominator parameter. -/
theorem hasSum_regularizedGauss_one_of_nonpole {a b c : ℂ}
    (hc : ∀ k : ℕ, c ≠ -k) (h : 0 < (c - a - b).re) :
    HasSum (fun n : ℕ => poch a n * poch b n / (n.factorial * Gamma (c + n)))
      (Gamma (c - a - b) / (Gamma (c - a) * Gamma (c - b))) := by
  have hs : Summable (gaussHGCoeff a b c) := by
    simpa using (ordinaryHypergeometric_summable_of_mem_sphere (a := a) (b := b)
      (c := c) (z := 1) (by simp) h)
  have hs' := hs.hasSum
  rw [← ordinaryHypergeometric_one_eq_tsum, gauss_summation hc h] at hs'
  convert hs'.div_const (Gamma c) using 1
  · funext n
    have hg := (div_eq_iff (Gamma_ne_zero hc)).mp (Gamma_add_nat_div_Gamma_eq (n := n) c hc)
    rw [hg, gaussHGCoeff]
    ring
  · field_simp [Gamma_ne_zero hc]

/-- Regularized Gauss summation retains all denominator parameters, including Gamma poles. -/
theorem hasSum_regularizedGauss_one {a b c : ℂ} (h : 0 < (c - a - b).re) :
    HasSum (fun n : ℕ => poch a n * poch b n / (n.factorial * Gamma (c + n)))
      (Gamma (c - a - b) / (Gamma (c - a) * Gamma (c - b))) := by
  by_cases hc : ∀ k : ℕ, c ≠ -k
  · exact hasSum_regularizedGauss_one_of_nonpole hc h
  push Not at hc
  obtain ⟨m, rfl⟩ := hc
  let N := m + 1
  have hN : (N : ℂ) ≠ 0 := by dsimp [N]; exact_mod_cast Nat.succ_ne_zero m
  have hcN : ∀ k : ℕ, (N : ℂ) + 1 ≠ -k := not_neg_nat_of_re_pos (by simp; positivity)
  have hgap : (N : ℂ) + 1 - (a + N) - (b + N) = -(m : ℂ) - a - b := by
    dsimp [N]; push_cast; ring
  have hs : Summable (gaussHGCoeff (a + N) (b + N) (N + 1)) := by
    simpa using (ordinaryHypergeometric_summable_of_mem_sphere
      (a := a + N) (b := b + N) (c := N + 1) (z := 1) (by simp) (by rwa [hgap]))
  have hs' := hs.hasSum
  rw [← ordinaryHypergeometric_one_eq_tsum, gauss_summation hcN (by rwa [hgap]), hgap] at hs'
  have hzero : ∑ k ∈ Finset.range N,
      poch a k * poch b k / (k.factorial * Gamma (-(m : ℂ) + k)) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hkm : k ≤ m := by have := Finset.mem_range.mp hk; dsimp [N] at this; omega
    rw [show -(m : ℂ) + k = -((m - k : ℕ) : ℂ) by push_cast [Nat.cast_sub hkm]; ring,
      Gamma_neg_nat_eq_zero]
    simp
  apply (hasSum_nat_add_iff' N).mp
  rw [hzero, sub_zero]
  have hsum := hs'.mul_left (poch a N * poch b N / (N.factorial : ℂ))
  convert hsum using 1
  · funext k
    have hfac : ((k + N).factorial : ℂ) = (N.factorial : ℂ) * poch (N + 1 : ℂ) k := by
      rw [← poch_nat_one, ← poch_nat_one, show (N : ℂ) + 1 = 1 + N by ring, ← poch_add]
      congr 1; omega
    rw [show -(m : ℂ) + ((k + N : ℕ) : ℂ) = (k : ℂ) + 1 by dsimp [N]; push_cast; ring,
      Gamma_nat_eq_factorial, gaussHGCoeff, hfac,
      show k + N = N + k by omega, poch_add a N k, poch_add b N k]
    ring
  · symm
    rw [Gamma_nat_eq_factorial]
    have href (u : ℂ) : poch u N / Gamma (1 - u) = (-1 : ℂ) ^ N / Gamma (-(m : ℂ) - u) := by
      have hi := recip_Gamma_eq_poch_mul m (-(m : ℂ) - u)
      rw [show -(m : ℂ) - u + ((m + 1 : ℕ) : ℂ) = 1 - u by push_cast; ring,
        show -(m : ℂ) - u = 1 - u - (N : ℂ) by dsimp [N]; push_cast; ring,
        poch_reflect] at hi
      have hn : (-1 : ℂ) ^ N * (-1) ^ N = 1 := by rw [← mul_pow]; simp
      simp only [div_eq_mul_inv]
      rw [show -(m : ℂ) - u = 1 - u - (N : ℂ) by dsimp [N]; push_cast; ring, hi]
      linear_combination -(poch u N * (Gamma (1 - u))⁻¹) * hn
    rw [show (N : ℂ) + 1 - (a + N) = 1 - a by ring,
      show (N : ℂ) + 1 - (b + N) = 1 - b by ring]
    have hnf : (N.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr N.factorial_ne_zero
    have hn : (-1 : ℂ) ^ N * (-1) ^ N = 1 := by rw [← mul_pow]; simp
    calc
      _ = Gamma (-(m : ℂ) - a - b) *
          ((poch a N / Gamma (1 - a)) * (poch b N / Gamma (1 - b))) := by field_simp
      _ = _ := by rw [href, href]; simp only [div_mul_div_comm, hn, one_div]; ring

/-- The left boundary limit of the continued regularized Gauss function, for every denominator
parameter. Mathlib's Abel limit theorem applies to `hasSum_regularizedGauss_one`, so exceptional
parameters require no separate continuation argument. -/
theorem tendsto_regularizedGaussHG_left_one {a b c : ℂ} (h : 0 < (c - a - b).re) :
    Tendsto (fun x : ℝ => regularizedGaussHG a b c x) (𝓝[<] 1)
      (𝓝 (Gamma (c - a - b) / (Gamma (c - a) * Gamma (c - b)))) := by
  have hA := Complex.tendsto_tsum_powerSeries_nhdsWithin_lt
    (hasSum_regularizedGauss_one h).tendsto_sum_nat
  rw [Filter.tendsto_map'_iff] at hA
  refine hA.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT (show (-1 : ℝ) < 1 by norm_num)] with x hx
  have hx' : ‖(x : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_lt]
    exact hx
  rw [regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hx', regularizedGaussHGFun_eq_tsum]
  apply tsum_congr
  intro n
  simp only [poch]
  ring

end DLMF.Hypergeometric
