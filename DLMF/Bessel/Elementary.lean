/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Bessel.KIntegrals
public import DLMF.Bessel.Asymptotics

/-!
# Elementary properties of the cylinder functions (DLMF Chapter 10, Beals–Wong Ch. 9)

* `besselY_half`, `besselY_neg_half`, `hankelH1_half`, … : half-integer orders (DLMF 10.16.1).
* `besselJ_neg_eq`, `hankelH1_neg`, `hankelH2_neg`: `J_{-ν} = cos(νπ) J_ν - sin(νπ) Y_ν` and
  `H^{(1)}_{-ν} = e^{iπν} H^{(1)}_ν`, `H^{(2)}_{-ν} = e^{-iπν} H^{(2)}_ν` (DLMF 10.4.6).
* `hankelH1_add_sub`, `hankelH2_add_sub`: the Hankel recurrence (DLMF 10.6.1).
* `norm_besselJ_int_le_one`: `|J_n(x)| ≤ 1` for real `x` and integer `n` (DLMF 10.14.1).
* `hasSum_besselJ_add`: Neumann's addition theorem (DLMF 10.23.3), from Bessel's integral.
* `besselI_int_eq`, `hasSum_besselI_generating_function`, `hasSum_besselI_cos`: `I_n(z) =
  (-i)ⁿ J_n(iz)`, the generating function (DLMF 10.35.1) and `e^{z cos θ}` (DLMF 10.35.3).
* `besselI_ofReal_pos`, `besselK_neg`, `besselK_ofReal_pos`: `I_ν(x) > 0` for `ν > -1`,
  `K_{-ν} = K_ν` (DLMF 10.27.3), and `K_ν(x) > 0` for every real `ν`, for `x > 0`.
* `hankelH1_sub_exp_isBigO`, `besselY_sub_sin_isBigO`: leading large-`x` behaviour of `H^{(1)}_ν`
  and `Y_ν` (DLMF 10.7.8).
* `iterate_zRecipDeriv_cpow_mul_besselJ`, `iterate_zRecipDeriv_cpow_neg_mul_besselJ`: the iterated
  derivative formulas DLMF 10.6.6.
* `besselI_eq_poisson_integral`: Poisson's integral for `I_ν` (DLMF 10.32.2).
-/

@[expose] public section

open Complex Filter Set Asymptotics
open scoped Real Topology Nat

noncomputable section

namespace DLMF.Bessel

/-! ### Half-integer orders -/

/-- `Y_{1/2} = -J_{-1/2}`. -/
theorem besselY_half_eq (z : ℂ) : besselY (1 / 2) z = -besselJ (-(1 / 2)) z := by
  have hn : ∀ k : ℤ, (1 / 2 : ℂ) ≠ k := fun k hk => by
    have h := congrArg Complex.re hk
    simp at h
    have : (1 : ℝ) = 2 * k := by linarith
    have h2 : (1 : ℤ) = 2 * k := by exact_mod_cast this
    omega
  rw [besselY_eq_of_not_int hn, besselD]
  have hc : cos ((1 / 2 : ℂ) * π) = 0 := by
    rw [show (1 / 2 : ℂ) * π = ((π / 2 : ℝ) : ℂ) by push_cast; ring, ← ofReal_cos,
      Real.cos_pi_div_two, ofReal_zero]
  have hs : sin ((1 / 2 : ℂ) * π) = 1 := by
    rw [show (1 / 2 : ℂ) * π = ((π / 2 : ℝ) : ℂ) by push_cast; ring, ← ofReal_sin,
      Real.sin_pi_div_two, ofReal_one]
  rw [hc, hs]
  ring

/-- `Y_{-1/2} = J_{1/2}`. -/
theorem besselY_neg_half_eq (z : ℂ) : besselY (-(1 / 2)) z = besselJ (1 / 2) z := by
  have hn : ∀ k : ℤ, (-(1 / 2) : ℂ) ≠ k := fun k hk => by
    have h := congrArg Complex.re hk
    simp at h
    have : (-1 : ℝ) = 2 * k := by linarith
    have h2 : (-1 : ℤ) = 2 * k := by exact_mod_cast this
    omega
  rw [besselY_eq_of_not_int hn, besselD, neg_neg]
  have hc : cos (-(1 / 2 : ℂ) * π) = 0 := by
    rw [show -(1 / 2 : ℂ) * π = ((-(π / 2) : ℝ) : ℂ) by push_cast; ring, ← ofReal_cos,
      Real.cos_neg, Real.cos_pi_div_two, ofReal_zero]
  have hs : sin (-(1 / 2 : ℂ) * π) = -1 := by
    rw [show -(1 / 2 : ℂ) * π = ((-(π / 2) : ℝ) : ℂ) by push_cast; ring, ← ofReal_sin,
      Real.sin_neg, Real.sin_pi_div_two]
    push_cast
    ring
  rw [hc, hs]
  ring

/-- `Y_{1/2}(z) = -√(2/(πz)) cos z` (DLMF 10.16.1). -/
@[dlmf 10.16.E1]
theorem besselY_half {z : ℂ} (hz : z ∈ slitPlane) :
    besselY (1 / 2) z = -((2 / (π * z)) ^ (1 / 2 : ℂ) * cos z) := by
  rw [besselY_half_eq, besselJ_neg_half z hz]

/-- `Y_{-1/2}(z) = √(2/(πz)) sin z` (DLMF 10.16.1). -/
@[dlmf 10.16.E1]
theorem besselY_neg_half {z : ℂ} (hz : z ∈ slitPlane) :
    besselY (-(1 / 2)) z = (2 / (π * z)) ^ (1 / 2 : ℂ) * sin z := by
  rw [besselY_neg_half_eq, besselJ_half z hz]

/-- `H^{(1)}_{1/2}(z) = -i √(2/(πz)) e^{iz}` (DLMF 10.16.1). -/
@[dlmf 10.16.E1]
theorem hankelH1_half {z : ℂ} (hz : z ∈ slitPlane) :
    hankelH1 (1 / 2) z = -I * (2 / (π * z)) ^ (1 / 2 : ℂ) * exp (I * z) := by
  rw [hankelH1, besselY_half hz, besselJ_half z hz, show I * z = z * I by ring,
    ← cos_add_sin_I]
  ring_nf
  rw [I_sq]
  ring

/-- `H^{(2)}_{1/2}(z) = i √(2/(πz)) e^{-iz}` (DLMF 10.16.1). -/
@[dlmf 10.16.E1]
theorem hankelH2_half {z : ℂ} (hz : z ∈ slitPlane) :
    hankelH2 (1 / 2) z = I * (2 / (π * z)) ^ (1 / 2 : ℂ) * exp (-(I * z)) := by
  rw [hankelH2, besselY_half hz, besselJ_half z hz,
    show -(I * z) = -z * I by ring, ← cos_add_sin_I, cos_neg, sin_neg]
  ring_nf
  rw [I_sq]
  ring

/-- `H^{(1)}_{-1/2}(z) = √(2/(πz)) e^{iz}` (DLMF 10.16.1). -/
@[dlmf 10.16.E1]
theorem hankelH1_neg_half {z : ℂ} (hz : z ∈ slitPlane) :
    hankelH1 (-(1 / 2)) z = (2 / (π * z)) ^ (1 / 2 : ℂ) * exp (I * z) := by
  rw [hankelH1, besselY_neg_half hz, besselJ_neg_half z hz,
    show I * z = z * I by ring, ← cos_add_sin_I]
  ring

/-- `H^{(2)}_{-1/2}(z) = √(2/(πz)) e^{-iz}` (DLMF 10.16.1). -/
@[dlmf 10.16.E1]
theorem hankelH2_neg_half {z : ℂ} (hz : z ∈ slitPlane) :
    hankelH2 (-(1 / 2)) z = (2 / (π * z)) ^ (1 / 2 : ℂ) * exp (-(I * z)) := by
  rw [hankelH2, besselY_neg_half hz, besselJ_neg_half z hz,
    show -(I * z) = -z * I by ring, ← cos_add_sin_I, cos_neg, sin_neg]
  ring

/-! ### Hankel functions of negative order and their recurrence -/

/-- `J_{-ν} = cos(νπ) J_ν - sin(νπ) Y_ν` for every order. -/
theorem besselJ_neg_eq (ν : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    besselJ (-ν) z = cos (ν * π) * besselJ ν z - sin (ν * π) * besselY ν z := by
  refine DLMF.Confluent.eq_of_continuousAt_of_integerComplement
    (f := fun μ => besselJ (-μ) z)
    (g := fun μ => cos (μ * π) * besselJ μ z - sin (μ * π) * besselY μ z)
    (continuousAt_besselJ_order (fun μ => -μ) continuous_neg ν hz)
    (((by fun_prop : Continuous fun μ : ℂ => cos (μ * π)).continuousAt.mul
      (continuousAt_besselJ_order (fun μ => μ) continuous_id ν hz)).sub
      ((by fun_prop : Continuous fun μ : ℂ => sin (μ * π)).continuousAt.mul
      (continuousAt_besselY_order (fun μ => μ) continuous_id ν hz)))
    (fun c hc => ?_)
  have hc' := DLMF.Confluent.forall_of_mem_integerComplement hc
  have hs := sin_mul_pi_ne_zero hc'
  rw [besselY_eq_of_not_int hc', besselD]
  field_simp
  ring

/-- `H^{(1)}_{-ν}(z) = e^{iπν} H^{(1)}_ν(z)` (DLMF 10.4.6). -/
@[dlmf 10.4.E6]
theorem hankelH1_neg (ν : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    hankelH1 (-ν) z = exp (π * ν * I) * hankelH1 ν z := by
  rw [hankelH1, hankelH1, besselJ_neg_eq ν hz, besselY_neg ν hz,
    show (π : ℂ) * ν * I = (ν * π) * I by ring, ← cos_add_sin_I]
  ring_nf
  rw [I_sq]
  ring

/-- `H^{(2)}_{-ν}(z) = e^{-iπν} H^{(2)}_ν(z)` (DLMF 10.4.6). -/
@[dlmf 10.4.E6]
theorem hankelH2_neg (ν : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    hankelH2 (-ν) z = exp (-(π * ν * I)) * hankelH2 ν z := by
  rw [hankelH2, hankelH2, besselJ_neg_eq ν hz, besselY_neg ν hz,
    show -((π : ℂ) * ν * I) = -(ν * π) * I by ring, ← cos_add_sin_I, cos_neg, sin_neg]
  ring_nf
  rw [I_sq]
  ring

/-- The recurrence `H_{ν-1} + H_{ν+1} = (2ν/z) H_ν` for `H^{(1)}` (DLMF 10.6.1). -/
@[dlmf 10.6.E1]
theorem hankelH1_add_sub (ν : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    (2 * ν / z) * hankelH1 ν z = hankelH1 (ν - 1) z + hankelH1 (ν + 1) z := by
  have hJ := besselJ_add_sub (ν := ν) (slitPlane_ne_zero hz)
  have hY := besselY_add_sub ν hz
  simp only [hankelH1]
  linear_combination hJ + I * hY

/-- The recurrence `H_{ν-1} + H_{ν+1} = (2ν/z) H_ν` for `H^{(2)}` (DLMF 10.6.1). -/
@[dlmf 10.6.E1]
theorem hankelH2_add_sub (ν : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    (2 * ν / z) * hankelH2 ν z = hankelH2 (ν - 1) z + hankelH2 (ν + 1) z := by
  have hJ := besselJ_add_sub (ν := ν) (slitPlane_ne_zero hz)
  have hY := besselY_add_sub ν hz
  simp only [hankelH2]
  linear_combination hJ - I * hY

/-! ### Bound for integer order on the real line -/

/-- `|J_n(x)| ≤ 1` for real `x` and integer `n` (DLMF 10.14.1). -/
@[dlmf 10.14.E1]
theorem norm_besselJ_int_le_one (n : ℤ) (x : ℝ) : ‖besselJ n x‖ ≤ 1 := by
  rw [besselJ_int_eq_integral_cos, norm_mul]
  have hle : ‖∫ θ in (0 : ℝ)..π, cos ((x : ℂ) * sin θ - n * θ)‖ ≤ 1 * |π - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun θ _ => ?_
    rw [show (x : ℂ) * sin (θ : ℂ) - n * θ = ((x * Real.sin θ - n * θ : ℝ) : ℂ) by
      push_cast; ring, ← ofReal_cos, norm_real, Real.norm_eq_abs]
    exact Real.abs_cos_le_one _
  have hπ : 0 < π := Real.pi_pos
  rw [sub_zero, abs_of_pos hπ, one_mul] at hle
  rw [show ‖(1 / π : ℂ)‖ = 1 / π by
    rw [norm_div, norm_one, norm_real, Real.norm_eq_abs, abs_of_pos hπ]]
  calc 1 / π * ‖∫ θ in (0 : ℝ)..π, cos ((x : ℂ) * sin θ - n * θ)‖ ≤ 1 / π * π := by gcongr
    _ = 1 := by field_simp

/-! ### Neumann's addition theorem -/

/-- **Neumann's addition theorem** `J_n(x + y) = ∑_{m∈ℤ} J_m(x) J_{n-m}(y)` (DLMF 10.23.3). -/
@[dlmf 10.23.E3]
theorem hasSum_besselJ_add (n : ℤ) (x y : ℂ) :
    HasSum (fun m : ℤ => besselJ m x * besselJ (n - m : ℤ) y) (besselJ n (x + y)) := by
  set F : ℤ → ℝ → ℂ := fun m θ =>
    besselJ m x * exp (I * (m - n : ℤ) * θ) * exp (I * y * sin θ) with hF
  have hlim (θ : ℝ) : HasSum (fun m : ℤ => F m θ) (exp (I * ((x + y) * sin θ - n * θ))) := by
    have h := (hasSum_besselJ_jacobiAnger x θ).mul_right (exp (I * y * sin θ - I * n * θ))
    convert h using 1
    · funext m
      simp only [hF, mul_assoc, ← exp_add]
      congr 2
      push_cast
      ring
    · rw [← exp_add]
      ring_nf
  have hcont (m : ℤ) : Continuous fun θ : ℝ => F m θ := by
    simp only [hF]
    fun_prop
  have hbound (m : ℤ) (θ : ℝ) : ‖F m θ‖ ≤ ‖besselJ m x‖ * Real.exp ‖y‖ := by
    simp only [hF]
    rw [norm_mul, norm_mul, show I * ((m - n : ℤ) : ℂ) * (θ : ℂ) =
      ((((m - n : ℤ) : ℝ) * θ : ℝ) : ℂ) * I by push_cast; ring, norm_exp_ofReal_mul_I, mul_one]
    gcongr
    refine (norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr ?_)
    rw [norm_mul, norm_mul, norm_I, one_mul]
    have hs : ‖sin (θ : ℂ)‖ ≤ 1 := by
      rw [← ofReal_sin, norm_real, Real.norm_eq_abs]
      exact Real.abs_sin_le_one θ
    calc ‖y‖ * ‖sin (θ : ℂ)‖ ≤ ‖y‖ * 1 := by gcongr
      _ = ‖y‖ := mul_one _
  have hsum : Summable fun m : ℤ => ‖besselJ m x‖ * Real.exp ‖y‖ :=
    (summable_norm_besselJ_int x).mul_right _
  have hint := intervalIntegral.hasSum_integral_of_dominated_convergence
    (μ := MeasureTheory.volume) (a := 0) (b := 2 * π) (F := F)
    (f := fun θ : ℝ => exp (I * ((x + y) * sin θ - n * θ)))
    (fun m _ => ‖besselJ m x‖ * Real.exp ‖y‖)
    (fun m => (hcont m).aestronglyMeasurable)
    (fun m => Filter.Eventually.of_forall fun θ _ => hbound m θ)
    (Filter.Eventually.of_forall fun _ _ => hsum)
    intervalIntegrable_const
    (Filter.Eventually.of_forall fun θ _ => hlim θ)
  have hterm (m : ℤ) : ∫ θ in (0 : ℝ)..2 * π, F m θ =
      2 * π * (besselJ m x * besselJ (n - m : ℤ) y) := by
    have he : (fun θ : ℝ => F m θ) =
        fun θ : ℝ => besselJ m x * exp (I * (y * sin θ - ((n - m : ℤ) : ℂ) * θ)) := by
      funext θ
      simp only [hF]
      rw [mul_assoc, ← exp_add]
      push_cast
      congr 2
      ring
    rw [he, intervalIntegral.integral_const_mul]
    have hJ := besselJ_int_eq_integral_exp (n - m) y
    have hπ : (2 * π : ℂ) ≠ 0 := by
      exact mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero)
    rw [hJ]
    field_simp
  simp only [hterm] at hint
  have hJ := besselJ_int_eq_integral_exp n (x + y)
  have hπ : (2 * π : ℂ) ≠ 0 := mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero)
  have h2 := hint.div_const (2 * π)
  convert h2 using 1
  · funext m
    field_simp
  · rw [hJ]
    field_simp

/-! ### Integer-order modified functions: generating function and cosine series -/

/-- `I_n(z) = (-i)ⁿ J_n(iz)` for natural `n` and every `z`. -/
theorem besselI_nat_eq (n : ℕ) (z : ℂ) : besselI n z = (-I) ^ n * besselJ n (I * z) := by
  rw [besselI, besselJ_eq_regularized, cpow_natCast, cpow_natCast,
    show -((I * z) ^ 2 / 4) = z ^ 2 / 4 by ring_nf; rw [I_sq]; ring, ← mul_assoc, ← mul_pow,
    show -I * (I * z / 2) = z / 2 by ring_nf; rw [I_sq]; ring]

/-- `I_n(z) = (-i)ⁿ J_n(iz)` for integer `n` and every `z` (DLMF 10.27.6 at integer order). -/
theorem besselI_int_eq (n : ℤ) (z : ℂ) : besselI n z = (-I) ^ n * besselJ n (I * z) := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · rw [Int.cast_natCast, zpow_natCast, besselI_nat_eq]
  · have hI := besselI_neg_int (n : ℤ) z
    have hJ := besselJ_neg_int (n : ℤ) (I * z)
    push_cast at hI hJ ⊢
    rw [hI, hJ, besselI_nat_eq]
    simp only [zpow_neg, zpow_natCast]
    have h4 : ((-I : ℂ) ^ n)⁻¹ = I ^ n := by
      rw [← inv_pow, inv_neg, inv_I, neg_neg]
    rw [h4, neg_pow (I : ℂ)]
    ring

/-- The generating function `∑_{n∈ℤ} I_n(z) tⁿ = exp((z/2)(t + t⁻¹))` (DLMF 10.35.1). -/
@[dlmf 10.35.E1]
theorem hasSum_besselI_generating_function (z t : ℂ) (ht : t ≠ 0) :
    HasSum (fun n : ℤ => besselI n z * t ^ n) (exp (z / 2 * (t + t⁻¹))) := by
  have h := hasSum_besselJ_generating_function (I * z) (-I * t)
    (mul_ne_zero (neg_ne_zero.mpr I_ne_zero) ht)
  convert h using 1
  · funext n
    rw [besselI_int_eq, mul_zpow]
    ring
  · congr 1
    rw [mul_inv, show (-I : ℂ)⁻¹ = I by rw [inv_neg, inv_I, neg_neg]]
    ring_nf
    rw [I_sq]
    ring

/-- The bilateral series `e^{z cos θ} = ∑_{n∈ℤ} I_n(z) e^{inθ}`. -/
theorem hasSum_besselI_exp_cos (z : ℂ) (θ : ℝ) :
    HasSum (fun n : ℤ => besselI n z * exp (I * n * θ)) (exp (z * cos θ)) := by
  have h := hasSum_besselI_generating_function z (exp (I * θ)) (exp_ne_zero _)
  have hcos : z / 2 * (exp (I * θ) + (exp (I * θ))⁻¹) = z * cos θ := by
    rw [← exp_neg, cos, show -(I * (θ : ℂ)) = -(θ : ℂ) * I by ring,
      show I * (θ : ℂ) = (θ : ℂ) * I by ring]
    ring
  rw [hcos] at h
  convert h using 2 with n
  rw [← exp_int_mul]
  ring_nf

/-- `e^{z cos θ} = I₀(z) + 2 ∑_{k≥1} I_k(z) cos(kθ)` (DLMF 10.35.3). -/
@[dlmf 10.35.E3]
theorem hasSum_besselI_cos (z : ℂ) (θ : ℝ) :
    HasSum (fun k : ℕ => 2 * besselI (k + 1 : ℕ) z * cos ((k + 1 : ℕ) * θ))
      (exp (z * cos θ) - besselI 0 z) := by
  have h := (hasSum_besselI_exp_cos z θ).nat_add_neg
  have hterm (n : ℕ) : besselI ((n : ℤ) : ℂ) z * exp (I * ((n : ℤ) : ℂ) * θ) +
      besselI ((-(n : ℤ) : ℤ) : ℂ) z * exp (I * ((-(n : ℤ) : ℤ) : ℂ) * θ) =
      2 * besselI n z * cos (n * θ) := by
    have hI := besselI_neg_int (n : ℤ) z
    push_cast at hI ⊢
    rw [hI, cos]
    ring_nf
  simp_rw [hterm] at h
  simp only [Int.cast_zero, mul_zero, zero_mul, Complex.exp_zero, mul_one] at h
  have hs := (hasSum_nat_add_iff' 1).mpr h
  convert hs using 1
  rw [Finset.sum_range_one]
  simp
  ring

/-! ### Positivity of `I_ν` and `K_ν` on the positive axis -/

/-- Identity under the stated parameter and domain assumptions: `Complex.Gamma ((ν : ℂ) + 1 + n) =
((Real.Gamma (ν + 1 + n) : ℝ) : ℂ)`. -/
theorem Gamma_ofReal_add_one_add (ν : ℝ) (n : ℕ) :
    Complex.Gamma ((ν : ℂ) + 1 + n) = ((Real.Gamma (ν + 1 + n) : ℝ) : ℂ) := by
  rw [← Complex.Gamma_ofReal]
  push_cast
  rfl

/-- `I_ν(x)` for real `ν` and `x > 0` as a real series. -/
theorem besselI_ofReal_eq {ν x : ℝ} (hx : 0 < x) :
    besselI ν x = (((x / 2) ^ ν * ∑' n : ℕ,
      (x ^ 2 / 4) ^ n / n ! * (Real.Gamma (ν + 1 + n))⁻¹ : ℝ) : ℂ) := by
  rw [besselI, regularized0F1_eq_tsum, ofReal_mul, ofReal_cpow (by positivity), ofReal_tsum]
  push_cast
  congr 1
  refine tsum_congr fun n => ?_
  rw [Gamma_ofReal_add_one_add]

/-- `I_ν(x) > 0` for real `ν > -1` and `x > 0`. -/
theorem besselI_ofReal_pos {ν x : ℝ} (hν : -1 < ν) (hx : 0 < x) :
    ∃ r : ℝ, 0 < r ∧ besselI ν x = r := by
  refine ⟨_, ?_, besselI_ofReal_eq hx⟩
  set f : ℕ → ℝ := fun n => (x ^ 2 / 4) ^ n / n ! * (Real.Gamma (ν + 1 + n))⁻¹ with hf
  have hpos (n : ℕ) : 0 < f n := by
    have : 0 < ν + 1 + n := by have := n.cast_nonneg (α := ℝ); linarith
    simp only [hf]
    have := Real.Gamma_pos_of_pos this
    positivity
  have hsum : Summable f := by
    have h := summable_regularized0F1_term ((ν : ℂ) + 1) ((x : ℂ) ^ 2 / 4)
    refine (Complex.summable_ofReal.mp ?_)
    refine h.congr fun n => ?_
    simp only [hf]
    rw [Gamma_ofReal_add_one_add]
    push_cast
    rfl
  exact mul_pos (Real.rpow_pos_of_pos (by positivity) _) (hsum.tsum_pos (fun n => (hpos n).le) 0
    (hpos 0))

/-- Estimate under the stated parameter and domain assumptions: `∃ r : ℝ, 0 < r ∧ besselK ν x =
r`. -/
theorem besselK_ofReal_pos_of_gt {ν x : ℝ} (hν : -1 / 2 < ν) (hx : 0 < x) :
    ∃ r : ℝ, 0 < r ∧ besselK ν x = r := by
  have hνc : -1 / 2 < (ν : ℂ).re := by simpa using hν
  have hxc : 0 < (x : ℂ).re := by simpa using hx
  rw [besselK_eq_integral_tricomi hνc hxc]
  set f : ℝ → ℝ := fun t => Real.exp (-(2 * x) * t) * t ^ (ν - 1 / 2) * (1 + t) ^ (ν - 1 / 2)
    with hf
  have heq : EqOn (fun t : ℝ => exp (-(2 * (x : ℂ)) * t) * (t : ℂ) ^ ((ν : ℂ) - 1 / 2) *
      (1 + (t : ℂ)) ^ ((ν : ℂ) - 1 / 2)) (fun t => (f t : ℂ)) (Ioi 0) := by
    intro t ht
    have ht0 : (0 : ℝ) ≤ t := le_of_lt ht
    simp only [hf]
    push_cast
    rw [ofReal_cpow ht0, show (1 + (t : ℂ)) = ((1 + t : ℝ) : ℂ) by push_cast; ring,
      ofReal_cpow (by linarith)]
    push_cast
    rfl
  have hint := DLMF.Confluent.kummerU_laplace_integrable (a := (ν : ℂ) + 1 / 2)
    (b := 2 * ν + 1) (z := 2 * x) (by simp; linarith) (by simp; linarith)
  have hexp1 : (ν : ℂ) + 1 / 2 - 1 = ν - 1 / 2 := by ring
  have hexp2 : 2 * (ν : ℂ) + 1 - (ν + 1 / 2) - 1 = ν - 1 / 2 := by ring
  rw [hexp1, hexp2] at hint
  have hintc := hint.congr_fun heq measurableSet_Ioi
  have hfi : MeasureTheory.IntegrableOn f (Ioi 0) := by
    have := hintc.re
    simpa using this
  have hI : ∫ t : ℝ in Ioi 0, exp (-(2 * (x : ℂ)) * t) * (t : ℂ) ^ ((ν : ℂ) - 1 / 2) *
      (1 + (t : ℂ)) ^ ((ν : ℂ) - 1 / 2) = ((∫ t : ℝ in Ioi 0, f t : ℝ) : ℂ) := by
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi heq, integral_complex_ofReal]
  have hfpos : 0 < ∫ t : ℝ in Ioi 0, f t := by
    rw [MeasureTheory.setIntegral_pos_iff_support_of_nonneg_ae _ hfi]
    · have hsub : Ioi (0 : ℝ) ⊆ Function.support f ∩ Ioi 0 := fun t ht => by
        refine ⟨?_, ht⟩
        simp only [Function.mem_support, hf]
        have ht0 : (0 : ℝ) < t := ht
        positivity
      exact lt_of_lt_of_le (by simp) (MeasureTheory.measure_mono hsub)
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : (0 : ℝ) < t := ht
      simp only [Pi.zero_apply, hf]
      positivity
  have hG : Complex.Gamma ((ν : ℂ) + 1 / 2) = ((Real.Gamma (ν + 1 / 2) : ℝ) : ℂ) := by
    rw [← Complex.Gamma_ofReal]; push_cast; ring_nf
  have hGpos : 0 < Real.Gamma (ν + 1 / 2) := Real.Gamma_pos_of_pos (by linarith)
  have hpow : (2 * (x : ℂ)) ^ (ν : ℂ) = (((2 * x) ^ ν : ℝ) : ℂ) := by
    rw [ofReal_cpow (by positivity)]; push_cast; ring_nf
  refine ⟨Real.sqrt π * (2 * x) ^ ν * Real.exp (-x) / Real.Gamma (ν + 1 / 2) *
    ∫ t : ℝ in Ioi 0, f t, ?_, ?_⟩
  · have := Real.sqrt_pos.mpr Real.pi_pos
    have := Real.rpow_pos_of_pos (by positivity : (0 : ℝ) < 2 * x) ν
    positivity
  · rw [hI, hG, hpow, ← ofReal_neg, ← ofReal_exp]
    push_cast
    ring

/-- `K_ν(x) > 0` for every real order `ν` and `x > 0`. -/
theorem besselK_ofReal_pos (ν : ℝ) {x : ℝ} (hx : 0 < x) :
    ∃ r : ℝ, 0 < r ∧ besselK ν x = r := by
  by_cases hν : -1 / 2 < ν
  · exact besselK_ofReal_pos_of_gt hν hx
  · obtain ⟨r, hr, h⟩ := besselK_ofReal_pos_of_gt (ν := -ν) (by linarith) hx
    refine ⟨r, hr, ?_⟩
    rw [← besselK_neg _ (Or.inl (by simpa using hx)), ← h]
    push_cast
    rfl

/-! ### Leading large-argument behaviour of `H^{(1)}_ν` and `Y_ν` -/

/-- `H^{(1)}_ν(x) = √(2/(πx)) e^{i(x - νπ/2 - π/4)} + O(x^{-3/2})` as `x → +∞`
(leading term of DLMF 10.17.5; compare DLMF 10.2.5). -/
@[dlmf 10.2.E5]
theorem hankelH1_sub_exp_isBigO (ν : ℂ) :
    (fun x : ℝ => hankelH1 ν x -
      (Real.sqrt (2 / (π * x)) : ℂ) * exp ((x - ν * π / 2 - π / 4) * I)) =O[atTop]
      (fun x : ℝ => x ^ (-(3 / 2) : ℝ)) := by
  have hpi := Real.pi_pos
  have hm := besselK_ray_isBigO ν (c := -I) (by simp) (α := π / 4)
    (by rw [abs_of_pos (by positivity)]; linarith) half_le_re_neg_I_mul_exp
  set c : ℂ := 2 / (π * I) with hcdef
  have hb : (fun x : ℝ => c * exp (-(I * ν * π / 2)) * exp (((1 * x : ℝ) : ℂ) * I)) =O[atTop]
      (fun _ => (1 : ℝ)) :=
    IsBigO.of_bound ‖c * exp (-(I * ν * π / 2))‖ (Eventually.of_forall fun x => by
      rw [norm_mul, norm_exp_ofReal_mul_I]; simp)
  refine (hb.mul hm).congr' ?_ (Eventually.of_forall fun x => one_mul _)
  filter_upwards [eventually_gt_atTop 0] with x hx
  have hs : (x : ℂ) ∈ slitPlane := Or.inl (by simpa using hx)
  have harg : -(π / 2) < arg (x : ℂ) := by
    rw [arg_ofReal_of_nonneg hx.le]; linarith
  rw [hankelH1_eq_besselK ν hs harg]
  have hPm := two_mul_ray_cpow hx (α := -(π / 2)) (by rw [abs_neg, abs_of_pos (by positivity)])
  rw [exp_neg_pi_div_two_mul_I'] at hPm
  rw [hPm, sqrt_two_div_pi_mul hx]
  have hEE : exp (((1 * x : ℝ) : ℂ) * I) * exp (-I * x) = 1 := by
    rw [← exp_add]; push_cast; ring_nf; exact exp_zero
  have hA : exp (-(I * ν * π / 2)) * exp (((1 * x : ℝ) : ℂ) * I) *
      exp (-((-(π / 2) : ℝ) * I / 2)) =
      exp ((π / 2 : ℝ) * I) * exp ((x - ν * π / 2 - π / 4) * I) := by
    rw [← exp_add, ← exp_add, ← exp_add]; congr 1; push_cast; ring
  rw [exp_pi_div_two_mul_I'] at hA
  have hc : c * I = 2 / π := by
    have : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr hpi.ne'
    rw [hcdef]
    field_simp
  rw [← hcdef]
  generalize ((2 * x : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) = s at *
  generalize exp (-(I * ν * π / 2)) = a at *
  generalize exp (((1 * x : ℝ) : ℂ) * I) = E at *
  generalize exp (-I * x) = E2 at *
  generalize exp (-((-(π / 2) : ℝ) * I / 2)) = p at *
  generalize besselK ν (-I * x) = K at *
  generalize exp ((x - ν * π / 2 - π / 4) * I) = T at *
  linear_combination (c * a * K) * hEE - (c * (Real.sqrt π : ℂ) * s) * hA -
    ((Real.sqrt π : ℂ) * s * T) * hc

/-- **Large-argument behaviour of `Y_ν`** (DLMF 10.7.8): for every complex `ν`,
`Y_ν(x) = √(2/(πx)) sin(x - νπ/2 - π/4) + O(x^{-3/2})` as `x → +∞`. -/
@[dlmf 10.7.E8]
theorem besselY_sub_sin_isBigO (ν : ℂ) :
    (fun x : ℝ => besselY ν x -
      (Real.sqrt (2 / (π * x)) : ℂ) * sin (x - ν * π / 2 - π / 4)) =O[atTop]
      (fun x : ℝ => x ^ (-(3 / 2) : ℝ)) := by
  have h := ((hankelH1_sub_exp_isBigO ν).const_mul_left (-I)).add
    ((besselJ_sub_cos_isBigO ν).const_mul_left I)
  refine h.congr' (Eventually.of_forall fun x => ?_) EventuallyEq.rfl
  simp only [hankelH1, exp_mul_I]
  ring_nf
  rw [I_sq]
  ring

/-! ### Iterated derivative formulas -/

/-- `(z^ν J_ν(z))' = z^ν J_{ν-1}(z)` on the slit plane (DLMF 10.6.6). -/
theorem hasDerivAt_cpow_mul_besselJ' (ν : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    HasDerivAt (fun w : ℂ => w ^ ν * besselJ ν w) (z ^ ν * besselJ (ν - 1) z) z := by
  have hz0 := slitPlane_ne_zero hz
  have h := ((hasDerivAt_id z).cpow_const (c := ν) hz).mul (hasDerivAt_besselJ' (ν := ν) hz)
  convert h using 1
  · rfl
  simp only [id]
  rw [cpow_sub _ _ hz0, cpow_one]
  field_simp
  ring

/-- `(z^{-ν} J_ν(z))' = -z^{-ν} J_{ν+1}(z)` on the slit plane (DLMF 10.6.6). -/
theorem hasDerivAt_cpow_neg_mul_besselJ' (ν : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    HasDerivAt (fun w : ℂ => w ^ (-ν) * besselJ ν w) (-(z ^ (-ν) * besselJ (ν + 1) z)) z := by
  have hz0 := slitPlane_ne_zero hz
  have h := ((hasDerivAt_id z).cpow_const (c := -ν) hz).mul (hasDerivAt_besselJ (ν := ν) hz)
  convert h using 1
  · rfl
  simp only [id]
  rw [cpow_sub _ _ hz0, cpow_one]
  field_simp
  ring

/-- The operator `f ↦ z⁻¹ f'`. -/
def zRecipDeriv (f : ℂ → ℂ) : ℂ → ℂ := fun z => deriv f z / z

/-- `(z⁻¹ d/dz)^k (z^ν J_ν(z)) = z^{ν-k} J_{ν-k}(z)` (DLMF 10.6.6). -/
@[dlmf 10.6.E6]
theorem iterate_zRecipDeriv_cpow_mul_besselJ (ν : ℂ) (k : ℕ) {z : ℂ} (hz : z ∈ slitPlane) :
    (zRecipDeriv^[k] fun w => w ^ ν * besselJ ν w) z = z ^ (ν - k) * besselJ (ν - k) z := by
  induction k generalizing z with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', zRecipDeriv]
    have he : (zRecipDeriv^[k] fun w => w ^ ν * besselJ ν w) =ᶠ[𝓝 z]
        fun w => w ^ (ν - k) * besselJ (ν - k) w :=
      Filter.eventually_of_mem (isOpen_slitPlane.mem_nhds hz) fun w hw => ih hw
    rw [he.deriv_eq, (hasDerivAt_cpow_mul_besselJ' (ν - k) hz).deriv]
    push_cast
    rw [show ν - ((k : ℂ) + 1) = ν - k - 1 by ring, cpow_sub _ (1 : ℂ) (slitPlane_ne_zero hz),
      cpow_one]
    field_simp

/-- `(z⁻¹ d/dz)^k (z^{-ν} J_ν(z)) = (-1)^k z^{-ν-k} J_{ν+k}(z)` (DLMF 10.6.6). -/
@[dlmf 10.6.E6]
theorem iterate_zRecipDeriv_cpow_neg_mul_besselJ (ν : ℂ) (k : ℕ) {z : ℂ} (hz : z ∈ slitPlane) :
    (zRecipDeriv^[k] fun w => w ^ (-ν) * besselJ ν w) z =
      (-1) ^ k * z ^ (-ν - k) * besselJ (ν + k) z := by
  induction k generalizing z with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', zRecipDeriv]
    have he : (zRecipDeriv^[k] fun w => w ^ (-ν) * besselJ ν w) =ᶠ[𝓝 z]
        fun w => (-1) ^ k * (w ^ (-(ν + k)) * besselJ (ν + k) w) :=
      Filter.eventually_of_mem (isOpen_slitPlane.mem_nhds hz) fun w hw => by
        rw [ih hw, show -ν - k = -(ν + k) by ring]; ring
    rw [he.deriv_eq, ((hasDerivAt_cpow_neg_mul_besselJ' (ν + k) hz).const_mul _).deriv]
    push_cast
    rw [show -ν - (k + 1) = -(ν + k) - 1 by ring, cpow_sub _ (1 : ℂ) (slitPlane_ne_zero hz),
      cpow_one, show ν + k + 1 = ν + (k + 1) by ring]
    field_simp
    ring

/-! ### Poisson's integral for `I_ν` -/

/-- **Poisson's integral for `I_ν`** (DLMF 10.32.2): for `Re ν > -1/2` and `z` in the slit
plane, `I_ν(z) = (z/2)^ν / (√π Γ(ν+½)) ∫_{-1}^{1} (1-t²)^{ν-½} e^{zt} dt`. -/
@[dlmf 10.32.E2]
theorem besselI_eq_poisson_integral {ν z : ℂ} (hν : -1 / 2 < ν.re) (hz : z ∈ slitPlane) :
    besselI ν z = (z / 2) ^ ν / (Real.sqrt π * Gamma (ν + 1 / 2)) *
      ∫ t : ℝ in (-1 : ℝ)..1, (1 - (t : ℂ) ^ 2) ^ (ν - 1 / 2) * exp (z * t) := by
  have hz0 := slitPlane_ne_zero hz
  have ha : 0 < (ν + 1 / 2).re := by norm_num; linarith
  have hb : 0 < (ν + 1).re := by simp only [add_re, one_re]; linarith
  have hca : 2 * ν + 1 - (ν + 1 / 2) = ν + 1 / 2 := by ring
  let w : ℝ → ℂ := fun u => (u : ℂ) ^ (ν - 1 / 2) *
    (1 - (u : ℂ)) ^ (ν - 1 / 2) * exp (2 * z * u)
  let f : ℝ → ℂ := fun t => (1 - (t : ℂ) ^ 2) ^ (ν - 1 / 2) * exp (z * t)
  have hi : (∫ t : ℝ in (-1 : ℝ)..1, f t) =
      2 * (4 : ℂ) ^ (ν - 1 / 2) * exp (-z) * ∫ u : ℝ in (0 : ℝ)..1, w u := by
    have hsub := intervalIntegral.smul_integral_comp_mul_sub f
      (a := (0 : ℝ)) (b := 1) 2 1
    simp only [mul_zero, zero_sub, mul_one, show (2 : ℝ) - 1 = 1 by norm_num,
      Complex.real_smul, ofReal_ofNat] at hsub
    rw [← hsub, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
    intro u hu
    have hbase : 1 - ((2 * u - 1 : ℝ) : ℂ) ^ 2 =
        (4 : ℂ) * ((u : ℂ) * ((1 - u : ℝ) : ℂ)) := by push_cast; ring
    have hpow : (1 - ((2 * u - 1 : ℝ) : ℂ) ^ 2) ^ (ν - 1 / 2) =
        (4 : ℂ) ^ (ν - 1 / 2) *
          ((u : ℂ) ^ (ν - 1 / 2) * (1 - (u : ℂ)) ^ (ν - 1 / 2)) := by
      rw [hbase, ← ofReal_mul, ← ofReal_ofNat (n := 4),
        mul_cpow_ofReal_nonneg (by norm_num : (0 : ℝ) ≤ 4)
          (mul_nonneg hu.1.le (sub_nonneg.mpr hu.2.le)), ofReal_mul,
        mul_cpow_ofReal_nonneg hu.1.le (sub_nonneg.mpr hu.2.le), ofReal_sub, ofReal_one]
    have he : z * ((2 * u - 1 : ℝ) : ℂ) = -z + 2 * z * u := by
      push_cast; ring
    dsimp [f, w]
    rw [hpow, he, exp_add]
    ring
  have hM := DLMF.Confluent.kummerM_eq_euler_integral (z := 2 * z) ha
    (show 0 < (2 * ν + 1 - (ν + 1 / 2)).re by rwa [hca])
  rw [hca, show ν + 1 / 2 - 1 = ν - 1 / 2 by ring] at hM
  change DLMF.Confluent.kummerM (ν + 1 / 2) (2 * ν + 1) (2 * z) =
    Gamma (2 * ν + 1) / (Gamma (ν + 1 / 2) * Gamma (ν + 1 / 2)) *
      ∫ u : ℝ in (0 : ℝ)..1, w u at hM
  have hν2 : ∀ k : ℕ, 1 + 2 * ν ≠ -k := fun k h => by
    have := congrArg Complex.re h
    simp at this
    have := k.cast_nonneg (α := ℝ)
    linarith
  have hKB := DLMF.Confluent.kummerM_besselI ν z hz hν2
  have hA : Gamma (ν + 1 / 2) ≠ 0 := Gamma_ne_zero_of_re_pos ha
  have hB : Gamma (ν + 1) ≠ 0 := Gamma_ne_zero_of_re_pos hb
  have hP : (Real.sqrt π : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hpow : (4 : ℂ) ^ (ν - 1 / 2) * (2 : ℂ) ^ (-2 * ν) = 1 / 2 := by
    rw [show (4 : ℂ) = (2 : ℝ) * (2 : ℝ) by norm_num,
      mul_cpow_ofReal_nonneg (by norm_num) (by norm_num), ofReal_ofNat,
      ← cpow_add _ _ (by norm_num), ← cpow_add _ _ (by norm_num)]
    rw [show ν - 1 / 2 + (ν - 1 / 2) + -2 * ν = -1 by ring, cpow_neg_one]
    norm_num
  have hd := Gamma_mul_Gamma_add_half (ν + 1 / 2)
  rw [show ν + 1 / 2 + 1 / 2 = ν + 1 by ring,
    show 2 * (ν + 1 / 2) = 2 * ν + 1 by ring,
    show 1 - (2 * ν + 1) = -2 * ν by ring] at hd
  have hG : Gamma (2 * ν + 1) =
      2 * (4 : ℂ) ^ (ν - 1 / 2) * Gamma (ν + 1 / 2) * Gamma (ν + 1) / Real.sqrt π := by
    apply (eq_div_iff hP).mpr
    linear_combination -2 * Gamma (2 * ν + 1) * (Real.sqrt π : ℂ) * hpow -
      2 * (4 : ℂ) ^ (ν - 1 / 2) * hd
  have hzν : (z / 2) ^ (-ν) * (z / 2) ^ ν = 1 := by
    rw [cpow_neg, inv_mul_cancel₀ (cpow_ne_zero_iff.mpr (Or.inl (div_ne_zero hz0 two_ne_zero)))]
  have h4 : (4 : ℂ) ^ (ν - 1 / 2) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl (by norm_num))
  change _ = (z / 2) ^ ν / (Real.sqrt π * Gamma (ν + 1 / 2)) *
    ∫ t : ℝ in (-1 : ℝ)..1, f t
  rw [hi]
  rw [hM, hG, show 1 + ν = ν + 1 by ring] at hKB
  set W := ∫ u : ℝ in (0 : ℝ)..1, w u
  have hEm : exp (-z) * exp z = 1 := by rw [← exp_add, neg_add_cancel, exp_zero]
  have hstep : besselI ν z = (exp (-z) * (z / 2) ^ ν / Gamma (ν + 1)) *
      (Gamma (ν + 1) * exp z * (z / 2) ^ (-ν) * besselI ν z) := by
    have : (exp (-z) * (z / 2) ^ ν / Gamma (ν + 1)) *
        (Gamma (ν + 1) * exp z * (z / 2) ^ (-ν) * besselI ν z) =
        besselI ν z * ((exp (-z) * exp z) * ((z / 2) ^ (-ν) * (z / 2) ^ ν)) := by
      field_simp
    rw [this, hEm, hzν]
    ring
  rw [hstep, ← hKB]
  field_simp

end DLMF.Bessel
