/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.QHypergeometric.BasicSummations.Heine
public import DLMF.Hypergeometric.Derivatives

/-!
# The classical limit of Heine's q-derivatives

As the positive real base approaches one, Heine's iterated q-derivatives tend to the
corresponding derivatives of the Gauss hypergeometric function inside the unit disk. The
proof combines the exact q-derivative formula, the analytic classical limit, and the finite
shifted-factorial limits.
-/

@[expose] public noncomputable section

open Complex Filter Finset Set DLMF.QSeries
open scoped Real Topology

namespace DLMF.QHypergeometric

/-- As `q → 1⁻`, the iterated q-derivatives of `2φ1(q^a,q^b;q^c;q,z)` tend to the derivatives of
the Gauss function `F(a,b;c;z)`. -/
theorem heine_classical_derivative_limit {a b c z : ℂ} (hc : ∀ n : ℕ, c≠ -(n:ℂ))
    (hz : ‖z‖<1) (n : ℕ) :
    Tendsto (fun q : ℝ => qDerivIterate n q
      (fun w => qPhi [(q:ℂ)^a,(q:ℂ)^b] [(q:ℂ)^c] q w) z)
      (𝓝[<] 1) (𝓝 (iteratedDeriv n (ordinaryHypergeometric a b c) z)) := by
  have hcn : ∀ j : ℕ, c + (n : ℂ) ≠ -(j : ℂ) :=
    DLMF.Hypergeometric.not_neg_nat_add_nat hc n
  have hb : DLMF.Hypergeometric.LowerParametersRegular
      (([c + n] : List ℂ) : Multiset ℂ) := by
    intro x hx
    simp only [Multiset.mem_coe, List.mem_singleton] at hx
    subst x
    exact hcn
  have hgauss : DLMF.Hypergeometric.generalizedHypergeometric
      (([a + n, b + n] : List ℂ) : Multiset ℂ)
      (([c + n] : List ℂ) : Multiset ℂ) z = ordinaryHypergeometric (a + n) (b + n) (c + n) z := by
    have hs := DLMF.Hypergeometric.generalizedHypergeometric_hasSum_disk
      (a := (([a + n, b + n] : List ℂ) : Multiset ℂ))
      (b := (([c + n] : List ℂ) : Multiset ℂ)) (by simp) hb hz
    have ht := (DLMF.Hypergeometric.hasFPowerSeriesOnBall_ordinaryHypergeometric
      (a + n) (b + n) (c + n)).hasSum_mul_pow
      (DLMF.Hypergeometric.mem_eball_one_of_norm_lt_one hz)
    refine hs.unique (ht.congr_fun fun j => ?_)
    simp [DLMF.Hypergeometric.generalizedHypergeometricCoeff,
      DLMF.Hypergeometric.pochhammerProduct, DLMF.Hypergeometric.gaussHypergeometricCoeff]
  have hseries := qPhi_classical_limit [a + n, b + n] [c + n] z hb (by simp)
    (fun _ => hz)
  simp only [List.map_cons, List.map_nil, qPhiExponent, List.length_cons,
    List.length_nil] at hseries
  norm_num only at hseries
  simp only [zpow_zero, one_mul, hgauss] at hseries
  have hcoeff := ((tendsto_qPochhammer_normalized a n).mul
    (tendsto_qPochhammer_normalized b n)).div (tendsto_qPochhammer_normalized c n)
      (DLMF.Hypergeometric.pochhammer_ne_zero_of_not_neg_nat hc n)
  rw [DLMF.Hypergeometric.iteratedDeriv_hypergeometric n hc hz]
  refine (hcoeff.mul hseries).congr' ?_
  filter_upwards [ClassicalLimit.eventually_qDenominatorRegular_cpow [c]
    (by simpa using hc), Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with q hregular hq
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.1.ne'
  have hqnorm : ‖(q : ℂ)‖ < 1 := by simpa [Complex.norm_real, abs_of_pos hq.1] using hq.2
  have hD : 1 - (q : ℂ) ≠ 0 := by exact_mod_cast (sub_ne_zero.mpr hq.2.ne')
  have hC : qPochhammer ((q : ℂ) ^ c) q n ≠ 0 :=
    qPochhammer_ne_zero_of_qDenominatorRegular hqnorm hregular n
  have hderiv := heine_qDerivative (a := (q : ℂ) ^ a) (b := (q : ℂ) ^ b)
    (c := (q : ℂ) ^ c) (d := 1) (z := z) hq0 hqnorm (by simpa using hz) hregular n
  simp only [mul_one, one_mul, one_pow] at hderiv
  rw [hderiv]
  have hp (x : ℂ) : (q : ℂ) ^ (x + (n : ℂ)) = (q : ℂ) ^ x * (q : ℂ) ^ n := by
    rw [Complex.cpow_add _ _ hq0, Complex.cpow_natCast]
  simp only [hp, qPochhammerList, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_one]
  simp only [Pi.div_apply]
  field_simp [hD, hC]



end DLMF.QHypergeometric
