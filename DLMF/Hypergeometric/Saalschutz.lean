/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.Complex.ScalarSeries
public import DLMF.Hypergeometric.Continuation
public import DLMF.Gamma.Pochhammer

/-!
# The Pfaff–Saalschütz summation (Duverney Ex. 4.9; DLMF 16.4.3)

Comparing coefficients in Euler's transformation `𝐅(c-a,c-b;c;z) = (1-z)^{a+b-c} 𝐅(a,b;c;z)`
gives a convolution identity for the regularized coefficients, valid for all parameters
(`regularized_saalschutz_convolution`). Rewriting `(c-a-b)ₙ₋ₖ` and `1/(n-k)!` through Pochhammer
symbols in `k` turns it into the balanced terminating `₃F₂` summation
`₃F₂(-n, a, b; c, 1+a+b-c-n; 1) = (c-a)ₙ (c-b)ₙ / ((c)ₙ (c-a-b)ₙ)`.
-/

@[expose] public section

open Complex Filter
open scoped Topology Nat

noncomputable section

namespace DLMF.Hypergeometric

/-- The coefficients of `𝐅(a,b;c;z)`: `(a)ₙ (b)ₙ / (n! Γ(c+n))`. -/
theorem hasSum_regularizedGaussHGFun_coeff (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => poch a n * poch b n / (n ! * Gamma (c + n)) * z ^ n)
      (regularizedGaussHGFun a b c z) := by
  rw [regularizedGaussHGFun_eq_tsum]
  refine ((summable_regularizedGaussHGFun_term a b c hz).hasSum).congr_fun fun n => ?_
  simp only [poch]
  field_simp

/-- The binomial series `(1-z)^{-d} = ∑ (d)ₘ zᵐ/m!` on the unit disk. -/
theorem hasSum_one_sub_cpow_neg (d : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => poch d n / n ! * z ^ n) ((1 - z) ^ (-d)) := by
  exact hasSum_poch_div_factorial hz

/-- **Regularized Pfaff–Saalschütz convolution**, valid for all parameters: comparing coefficients
in Euler's transformation `𝐅(c-a,c-b;c;z) = (1-z)^{a+b-c} 𝐅(a,b;c;z)` gives
`∑ₖ (a)ₖ(b)ₖ/(k! Γ(c+k)) · (c-a-b)ₙ₋ₖ/(n-k)! = (c-a)ₙ(c-b)ₙ/(n! Γ(c+n))`. -/
theorem regularized_saalschutz_convolution (a b c : ℂ) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), poch a k * poch b k / (k ! * Gamma (c + k)) *
        (poch (c - a - b) (n - k) / (n - k)!) =
      poch (c - a) n * poch (c - b) n / (n ! * Gamma (c + n)) := by
  have h := Complex.powerSeries_coefficients_unique (f := regularizedGaussHGFun (c - a) (c - b) c)
    (c := fun n => ∑ k ∈ Finset.range (n + 1), poch a k * poch b k / (k ! * Gamma (c + k)) *
        (poch (c - a - b) (n - k) / (n - k)!))
    (d := fun n => poch (c - a) n * poch (c - b) n / (n ! * Gamma (c + n)))
    (fun z hz => by
      have hconv := Complex.hasSum_powerSeries_convolution (hasSum_regularizedGaussHGFun_coeff a b c hz)
        (hasSum_one_sub_cpow_neg (c - a - b) hz)
      rw [regularizedGaussHGFun_euler (c - a) (c - b) c hz,
        show c - (c - a) - (c - b) = -(c - a - b) by ring,
        show c - (c - a) = a by ring, show c - (c - b) = b by ring, mul_comm]
      exact hconv)
    (fun z hz => hasSum_regularizedGaussHGFun_coeff (c - a) (c - b) c hz)
  exact congrFun h n

/-- `(d)ₙ = (d)ₙ₋ₖ (-1)ᵏ (1-d-n)ₖ` for `k ≤ n`. -/
theorem poch_eq_poch_sub_mul (d : ℂ) {n k : ℕ} (hk : k ≤ n) :
    poch d n = poch d (n - k) * ((-1) ^ k * poch (1 - d - n) k) := by
  have h := poch_add d (n - k) k
  rw [Nat.sub_add_cancel hk] at h
  rw [h]
  congr 1
  have := DLMF.Gamma.poch_neg_eq (-(d + ((n - k : ℕ) : ℂ))) k
  rw [neg_neg] at this
  rw [this]
  congr 2
  push_cast [Nat.cast_sub hk]
  ring

/-- **Pfaff–Saalschütz summation** (DLMF 16.4.3; Duverney Ex. 4.9): the balanced terminating
`₃F₂(-n, a, b; c, 1+a+b-c-n; 1) = (c-a)ₙ (c-b)ₙ / ((c)ₙ (c-a-b)ₙ)`. -/
@[dlmf 16.4.E3]
theorem pfaff_saalschutz (n : ℕ) {a b c : ℂ} (hc : ∀ k : ℕ, c ≠ -k)
    (hd : poch (1 + a + b - c - n) n ≠ 0) :
    ∑ k ∈ Finset.range (n + 1), poch (-(n : ℂ)) k * poch a k * poch b k /
        (poch c k * poch (1 + a + b - c - n) k * k !) =
      poch (c - a) n * poch (c - b) n / (poch c n * poch (c - a - b) n) := by
  set d := c - a - b with hddef
  have hd' : poch (1 - d - n) n ≠ 0 := by
    rw [show 1 - d - n = 1 + a + b - c - n by rw [hddef]; ring]; exact hd
  have hdn : poch d n ≠ 0 := by
    have := poch_eq_poch_sub_mul d (le_refl n)
    rw [Nat.sub_self, poch_zero, one_mul] at this
    rw [this]; exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hd'
  have hΓ : Gamma c ≠ 0 := Gamma_ne_zero hc
  have hG (m : ℕ) : Gamma (c + m) = poch c m * Gamma c := by
    rw [poch, ← Gamma_add_nat_div_Gamma_eq c hc]; field_simp
  have hcm (m : ℕ) : poch c m ≠ 0 := poch_ne_zero_of_not_neg_nat hc m
  have hpk (k : ℕ) (hk : k ≤ n) : poch (1 - d - n) k ≠ 0 := by
    intro h0
    have := poch_add (1 - d - n) k (n - k)
    rw [Nat.add_sub_cancel' hk, h0, zero_mul] at this
    exact hd' this
  have hconv := regularized_saalschutz_convolution a b c n
  rw [← hddef] at hconv
  have hn : (n ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  rw [eq_div_iff (mul_ne_zero (hcm n) hdn)]
  rw [hG n, eq_div_iff (mul_ne_zero hn (mul_ne_zero (hcm n) hΓ)), Finset.sum_mul] at hconv
  rw [← hconv, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [hG k, poch_eq_poch_sub_mul d hk', poch_neg_coe_nat, Nat.descFactorial_eq_div hk']
  have hkf : (k ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  have hnkf : ((n - k)! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (n - k).factorial_ne_zero
  have hdiv : ((n ! / (n - k)! : ℕ) : ℂ) = n ! / (n - k)! := by
    rw [Nat.cast_div (Nat.factorial_dvd_factorial (Nat.sub_le n k)) hnkf]
  rw [hdiv, show 1 + a + b - c - (n : ℂ) = 1 - d - n by rw [hddef]; ring]
  have := hpk k hk'
  have := hcm k
  have hm1 : (((-1 : ℂ)) ^ k) ^ 2 = 1 := by rw [← pow_mul, pow_mul']; norm_num
  field_simp
  rw [hm1]
  ring

end DLMF.Hypergeometric

end
