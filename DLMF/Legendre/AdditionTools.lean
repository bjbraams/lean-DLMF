/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Legendre.FourierCoefficients

/-!
# Tools for the Legendre addition theorems of general degree

Infrastructure for the addition theorems DLMF 14.18.1–14.18.5 and 14.28.1 for complex degree `ν`,
proved coefficientwise in the Fourier expansion in the angle `φ`, with Carlson's theorem in `ν`
carrying the integer case (the polynomial addition theorem) to all degrees. The Fourier coefficient
`AdditionTheorem.coeff`, the cosine expansion and Carlson's theorem are in
`DLMF.Legendre.FourierCoefficients`.

## Main definitions

* `AdditionTheorem.hyperbolicArg`: the argument `cosh ξ₁ cosh ξ₂ - sinh ξ₁ sinh ξ₂ cos t` of the
  hyperbolic addition theorem.
* `AdditionTheorem.ferrersArg`: the argument `cos θ₁ cos θ₂ + sin θ₁ sin θ₂ cos t` of the Ferrers
  addition theorem.

## Main results

* `AdditionTheorem.norm_legendreP_le`, `AdditionTheorem.norm_associatedP_nat_le`,
  `AdditionTheorem.norm_associatedP_neg_le`: Laplace-type bounds on `(1, ∞)`:
  `|P_ν(x)| ≤ (2x)^{|Re ν|}` from Laplace's first integral `legendreP_laplace`, and bounds from
  14.12.7 and from the fractional integral 14.12.5.
* `AdditionTheorem.coeff_kernel`, `AdditionTheorem.hyperbolic_nat`: Fourier coefficients of the
  finite Legendre angular kernel, giving the integer-degree identity.
* `AdditionTheorem.hyperbolic_coeff_eq`, `associatedP_addition`: the Fourier
  coefficients of `φ ↦ P_ν(cosh ξ₁ cosh ξ₂ - sinh ξ₁ sinh ξ₂ cos φ)` for all complex `ν`, and DLMF
  14.18.4.
* `AdditionTheorem.regularizedGaussHG_one_eq_integral`: the representation
  `𝖯_ν(cos θ) = π^{-1/2} ∫₀^π 𝐅(ν+1, -ν; 1/2; sin²(θ/2) sin² t) dt` (termwise, with Wallis'
  integral `AdditionTheorem.integral_sin_pow_even`), which with 15.4.14 is the Mehler–Dirichlet
  integral in disguise.
* `AdditionTheorem.norm_ferrersP_zero_le`: the sharp bound `|𝖯_ν(cos θ)| ≤ e^{θ |Im ν|} / cos (θ/2)`
  for `0 ≤ θ < π` and all complex `ν`.
* `AdditionTheorem.norm_ferrersP_neg_le`, `AdditionTheorem.ferrersP_nat_eq`: bounds for `𝖯^{-m}_ν`
  (from 14.12.2) and `𝖯^m_ν = (-1)^m (ν-m+1)_{2m} 𝖯^{-m}_ν` for every complex `ν`.
* `AdditionTheorem.ferrers_coeff_eq`, `AdditionTheorem.ferrersP_addition_of_nat`,
  `AdditionTheorem.ferrers_nat`: Carlson's theorem with type `θ₁ + θ₂ < π`, and DLMF 14.18.1 from
  its integer case (the polynomial addition theorem).
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory DLMF.Hypergeometric DLMF
open scoped Real Topology Nat

namespace DLMF.Legendre

/-- A power of a number in `[B⁻¹, B]`, `B ≥ 1`, is at most `B^{|r|}`. -/
theorem AdditionTheorem.rpow_le {b B r : ℝ} (hb : 0 < b) (h1 : B⁻¹ ≤ b) (h2 : b ≤ B) :
    b ^ r ≤ B ^ |r| := by
  have hB : 0 < B := hb.trans_le h2
  rcases le_or_gt 0 r with hr | hr
  · rw [abs_of_nonneg hr]; exact Real.rpow_le_rpow hb.le h2 hr
  · rw [abs_of_neg hr, show b ^ r = (b⁻¹) ^ (-r) by
      rw [Real.inv_rpow hb.le, ← Real.rpow_neg hb.le, neg_neg]]
    exact Real.rpow_le_rpow (inv_pos.2 hb).le (by
      rw [inv_le_comm₀ hb hB]; exact h1) (by linarith)

/-- The Laplace base `x + √(x²-1) cos u` lies in `[(2x)⁻¹, 2x]` for `x ≥ 1`. -/
theorem AdditionTheorem.laplace_base_mem {x : ℝ} (hx : 1 ≤ x) (u : ℝ) :
    0 < x + Real.sqrt (x ^ 2 - 1) * Real.cos u ∧
    (2 * x)⁻¹ ≤ x + Real.sqrt (x ^ 2 - 1) * Real.cos u ∧
    x + Real.sqrt (x ^ 2 - 1) * Real.cos u ≤ 2 * x := by
  set s := Real.sqrt (x ^ 2 - 1) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = x ^ 2 - 1 := Real.sq_sqrt (by nlinarith)
  have hsx : s < x := by nlinarith
  have hc1 := Real.cos_le_one u
  have hc2 := Real.neg_one_le_cos u
  have hlow : x - s ≤ x + s * Real.cos u := by nlinarith
  have hxs : 0 < x - s := by linarith
  have hprod : (x - s) * (x + s) = 1 := by nlinarith
  refine ⟨by linarith, ?_, by nlinarith⟩
  refine le_trans ?_ hlow
  rw [inv_le_iff_one_le_mul₀ (by linarith)]
  nlinarith

/-- `associatedP ν 0 = legendreP ν` on `[1, ∞)`. -/
theorem AdditionTheorem.associatedP_zero {ν : ℂ} {x : ℝ} (hx : 1 ≤ x) :
    associatedP ν 0 x = legendreP ν x := by
  rcases eq_or_lt_of_le hx with h | h
  · subst h
    rw [ofReal_one, legendreP_one]
    simp only [associatedP, zero_div, zero_mul, exp_zero, one_mul, sub_zero, sub_self]
    rw [regularizedGaussHG_zero_of_regular]
    · simp
    · intro k hk
      have := congrArg Complex.re hk; simp at this; linarith [(k.cast_nonneg : (0:ℝ) ≤ k)]
  · exact associatedP_zero_order ν (LaplaceIntegrals.one_lt_mem h)

/-- Laplace bound `|P_ν(x)| ≤ (2x)^{|Re ν|}` for real `x ≥ 1`. -/
theorem AdditionTheorem.norm_legendreP_le (ν : ℂ) {x : ℝ} (hx : 1 ≤ x) :
    ‖legendreP ν x‖ ≤ (2 * x) ^ |ν.re| := by
  rw [legendreP_laplace ν hx, norm_mul]
  have hI : ‖∫ u in (0:ℝ)..π, (((x + Real.sqrt (x ^ 2 - 1) * Real.cos u : ℝ)) : ℂ) ^ ν‖ ≤
      (2 * x) ^ |ν.re| * |π - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun u _ => ?_
    obtain ⟨h0, h1, h2⟩ := AdditionTheorem.laplace_base_mem hx u
    rw [norm_cpow_eq_rpow_re_of_pos h0]
    exact AdditionTheorem.rpow_le h0 h1 h2
  have hπ := Real.pi_pos
  rw [sub_zero, abs_of_pos hπ] at hI
  rw [show ‖(1:ℂ) / π‖ = 1 / π by
    rw [norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hπ]]
  calc 1 / π * ‖∫ u in (0:ℝ)..π, (((x + Real.sqrt (x ^ 2 - 1) * Real.cos u : ℝ)) : ℂ) ^ ν‖
      ≤ 1 / π * ((2 * x) ^ |ν.re| * π) := by gcongr
    _ = (2 * x) ^ |ν.re| := by field_simp

/-- Bound for nonnegative integer order on `(1, ∞)` from 14.12.7. -/
theorem AdditionTheorem.norm_associatedP_nat_le (ν : ℂ) (m : ℕ) {x : ℝ} (hx : 1 < x) :
    ‖associatedP ν m x‖ ≤ ‖poch (ν + 1) m‖ * (2 * x) ^ |ν.re| := by
  rw [associatedP_fourier_integral ν m hx, norm_mul, norm_div]
  have hI : ‖∫ θ : ℝ in (0:ℝ)..π, (x + Real.sqrt (x ^ 2 - 1) * Real.cos θ : ℂ) ^ ν *
      Real.cos (m * θ)‖ ≤ (2 * x) ^ |ν.re| * |π - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun u _ => ?_
    obtain ⟨h0, h1, h2⟩ := AdditionTheorem.laplace_base_mem hx.le u
    rw [norm_mul, show (x + Real.sqrt (x ^ 2 - 1) * Real.cos u : ℂ) =
      ((x + Real.sqrt (x ^ 2 - 1) * Real.cos u : ℝ) : ℂ) by push_cast; ring,
      norm_cpow_eq_rpow_re_of_pos h0, Complex.norm_real, Real.norm_eq_abs]
    calc (x + Real.sqrt (x ^ 2 - 1) * Real.cos u) ^ ν.re * |Real.cos (m * u)|
        ≤ (2 * x) ^ |ν.re| * 1 := by
          gcongr
          · exact AdditionTheorem.rpow_le h0 h1 h2
          · exact Real.abs_cos_le_one _
      _ = _ := mul_one _
  have hπ := Real.pi_pos
  rw [sub_zero, abs_of_pos hπ] at hI
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hπ]
  calc ‖poch (ν + 1) m‖ / π * ‖∫ θ : ℝ in (0:ℝ)..π,
        (x + Real.sqrt (x ^ 2 - 1) * Real.cos θ : ℂ) ^ ν * Real.cos (m * θ)‖
      ≤ ‖poch (ν + 1) m‖ / π * ((2 * x) ^ |ν.re| * π) := by gcongr
    _ = _ := by field_simp

/-- Bound for negative integer order on `(1, ∞)` from the fractional integral 14.12.5. -/
theorem AdditionTheorem.norm_associatedP_neg_le (ν : ℂ) {m : ℕ} (hm : 1 ≤ m) {x : ℝ} (hx : 1 < x) :
    ‖associatedP ν (-(m:ℂ)) x‖ ≤ ‖((x:ℂ) ^ 2 - 1) ^ (-(m:ℂ) / 2) / Gamma m‖ *
      ((2 * x) ^ |ν.re| * (x - 1) ^ (m - 1) * (x - 1)) := by
  have hm' : (0:ℝ) < (m:ℂ).re := by simp; exact_mod_cast hm
  rw [associatedP_fractional_integral hm' ν hx, norm_mul]
  gcongr
  have hI := intervalIntegral.norm_integral_le_of_norm_le_const (a := 1) (b := x)
    (C := (2 * x) ^ |ν.re| * (x - 1) ^ (m - 1))
    (f := fun t : ℝ => associatedP ν 0 t * ((x:ℂ) - t) ^ ((m:ℂ) - 1)) (fun t ht => by
      rw [uIoc_of_le hx.le] at ht
      rw [norm_mul, AdditionTheorem.associatedP_zero ht.1.le, show (m:ℂ) - 1 = ((m - 1 : ℕ) : ℂ) by
        rw [Nat.cast_sub hm]; simp, cpow_natCast, norm_pow]
      gcongr
      · exact (AdditionTheorem.norm_legendreP_le ν ht.1.le).trans
          (Real.rpow_le_rpow (by linarith [ht.1]) (by linarith [ht.2]) (abs_nonneg _))
      · rw [show (x:ℂ) - t = ((x - t : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonneg (by linarith [ht.2])]
        linarith [ht.1])
  rwa [abs_of_pos (by linarith : (0:ℝ) < x - 1)] at hI

/-- `|(ν+1)_m| ≤ m! e^m e^{|ν|}`. -/
theorem AdditionTheorem.norm_poch_le (ν : ℂ) (m : ℕ) :
    ‖poch (ν + 1) m‖ ≤ m ! * Real.exp m * Real.exp ‖ν‖ := by
  have h1 : ‖poch (ν + 1) m‖ ≤ (‖ν‖ + m) ^ m := by
    have key : ∀ k : ℕ, k ≤ m → ‖poch (ν + 1) k‖ ≤ (‖ν‖ + m) ^ k := by
      intro k
      induction k with
      | zero => intro _; simp [poch_zero]
      | succ k ih =>
        intro hk
        rw [poch_succ, norm_mul, pow_succ]
        gcongr
        · exact ih (by omega)
        · calc ‖ν + 1 + k‖ ≤ ‖ν‖ + ‖(1:ℂ) + k‖ := by
                rw [add_assoc]; exact norm_add_le _ _
            _ ≤ ‖ν‖ + m := by
                gcongr
                rw [show (1:ℂ) + k = ((1 + k : ℕ) : ℂ) by push_cast; ring, Complex.norm_natCast]
                exact_mod_cast (by omega : 1 + k ≤ m)
    exact key m le_rfl
  have h2 := Real.pow_div_factorial_le_exp (x := ‖ν‖ + m) (by positivity) m
  have hf : (0:ℝ) < m ! := by exact_mod_cast Nat.factorial_pos m
  rw [div_le_iff₀ hf, Real.exp_add] at h2
  calc ‖poch (ν + 1) m‖ ≤ (‖ν‖ + m) ^ m := h1
    _ ≤ Real.exp ‖ν‖ * Real.exp m * m ! := h2
    _ = _ := by ring

/-- A real number below `1` lies in the cut plane. -/
theorem AdditionTheorem.ofReal_mem_cutPlane {r : ℝ} (hr : r < 1) : (r : ℂ) ∈ cutPlane := by
  rw [mem_cutPlane]; left; simp; linarith

/-- The argument `cosh ξ₁ cosh ξ₂ - sinh ξ₁ sinh ξ₂ cos t` of the hyperbolic addition theorem. -/
def AdditionTheorem.hyperbolicArg (ξ₁ ξ₂ t : ℝ) : ℝ :=
  Real.cosh ξ₁ * Real.cosh ξ₂ - Real.sinh ξ₁ * Real.sinh ξ₂ * Real.cos t

/-- For `ξ₁, ξ₂ ≥ 0` and real `t`, `1 ≤ AdditionTheorem.hyperbolicArg ξ₁ ξ₂ t ≤ cosh (ξ₁ + ξ₂)`. -/
theorem AdditionTheorem.hyperbolicArg_mem {ξ₁ ξ₂ : ℝ} (h1 : 0 ≤ ξ₁) (h2 : 0 ≤ ξ₂) (t : ℝ) :
    1 ≤ AdditionTheorem.hyperbolicArg ξ₁ ξ₂ t ∧ AdditionTheorem.hyperbolicArg ξ₁ ξ₂ t ≤
        Real.cosh (ξ₁ + ξ₂) := by
  have hs : 0 ≤ Real.sinh ξ₁ * Real.sinh ξ₂ :=
    mul_nonneg (Real.sinh_nonneg_iff.2 h1) (Real.sinh_nonneg_iff.2 h2)
  have hc1 := Real.cos_le_one t
  have hc2 := Real.neg_one_le_cos t
  have hsub := Real.one_le_cosh (ξ₁ - ξ₂)
  rw [Real.cosh_sub] at hsub
  rw [Real.cosh_add]
  unfold AdditionTheorem.hyperbolicArg
  constructor <;> nlinarith

/-- The order-zero Legendre function along `AdditionTheorem.hyperbolicArg` is `C²` in the angle. -/
theorem AdditionTheorem.hyperbolicArg_contDiff (ν : ℂ) {ξ₁ ξ₂ : ℝ} (h1 : 0 ≤ ξ₁) (h2 : 0 ≤ ξ₂) :
    ContDiff ℝ 2 (fun t : ℝ => associatedP ν 0 (AdditionTheorem.hyperbolicArg ξ₁ ξ₂ t)) := by
  have hG : DifferentiableOn ℂ (fun z => regularizedGaussHG (ν + 1) (-ν) 1 z) cutPlane :=
    DifferentiableOn.regularizedGaussHG (differentiableOn_const _) (differentiableOn_const _)
      (differentiableOn_const _) differentiableOn_id fun w hw => hw
  have hG2 : ContDiffOn ℝ 2 (fun z => regularizedGaussHG (ν + 1) (-ν) 1 z) cutPlane :=
    (hG.contDiffOn isOpen_cutPlane).restrict_scalars ℝ
  have hh : ContDiff ℝ 2
      (fun t : ℝ => (((1 - AdditionTheorem.hyperbolicArg ξ₁ ξ₂ t) / 2 : ℝ) : ℂ)) := by
    refine ofRealCLM.contDiff.comp ?_
    unfold AdditionTheorem.hyperbolicArg
    exact (contDiff_const.sub
        (contDiff_const.sub (contDiff_const.mul Real.contDiff_cos))).div_const 2
  have := hG2.comp_contDiff hh fun t =>
    AdditionTheorem.ofReal_mem_cutPlane
        (by linarith [(AdditionTheorem.hyperbolicArg_mem h1 h2 t).1])
  convert this using 1
  funext t
  simp only [Function.comp, ExteriorGreen.associatedP_eq]
  congr 1; push_cast; ring

/-- Order-zero values along `AdditionTheorem.hyperbolicArg` are bounded by
`(2 cosh (ξ₁+ξ₂))^{|Re ν|}`. -/
theorem AdditionTheorem.hyperbolicArg_norm_le (ν : ℂ) {ξ₁ ξ₂ : ℝ} (h1 : 0 ≤ ξ₁)
    (h2 : 0 ≤ ξ₂) (t : ℝ) :
    ‖associatedP ν 0 (AdditionTheorem.hyperbolicArg ξ₁ ξ₂ t)‖ ≤
        (2 * Real.cosh (ξ₁ + ξ₂)) ^ |ν.re| := by
  obtain ⟨hX1, hX2⟩ := AdditionTheorem.hyperbolicArg_mem h1 h2 t
  rw [AdditionTheorem.associatedP_zero hX1]
  exact (AdditionTheorem.norm_legendreP_le ν hX1).trans
    (Real.rpow_le_rpow (by linarith) (by linarith) (abs_nonneg _))

/-- Bound on the Fourier coefficients in the hyperbolic case. -/
theorem AdditionTheorem.hyperbolic_coeff_bound (ν : ℂ) {ξ₁ ξ₂ : ℝ} (h1 : 0 ≤ ξ₁)
    (h2 : 0 ≤ ξ₂) (m : ℤ) :
    ‖AdditionTheorem.coeff (fun t => associatedP ν 0 (AdditionTheorem.hyperbolicArg ξ₁ ξ₂ t)) m‖ ≤
      (2 * Real.cosh (ξ₁ + ξ₂)) ^ |ν.re| := by
  rw [AdditionTheorem.coeff, norm_mul]
  have hI := intervalIntegral.norm_integral_le_of_norm_le_const (a := -π) (b := π)
    (C := (2 * Real.cosh (ξ₁ + ξ₂)) ^ |ν.re|)
    (f := fun t : ℝ => exp (-((m:ℂ) * t * I)) *
        associatedP ν 0 (AdditionTheorem.hyperbolicArg ξ₁ ξ₂ t))
    (fun t _ => by
      rw [norm_mul, show -((m:ℂ) * t * I) = ((-(m * t) : ℝ) : ℂ) * I by push_cast; ring,
        norm_exp_ofReal_mul_I, one_mul]
      exact AdditionTheorem.hyperbolicArg_norm_le ν h1 h2 t)
  have hπ := Real.pi_pos
  rw [abs_of_pos (by linarith : (0:ℝ) < π - -π)] at hI
  rw [show ‖(1:ℂ) / (2 * π)‖ = 1 / (2 * π) by
    rw [norm_div, norm_one, norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hπ]]
  calc 1 / (2 * π) * ‖∫ t : ℝ in (-π)..π, exp (-((m:ℂ) * t * I)) *
        associatedP ν 0 (AdditionTheorem.hyperbolicArg ξ₁ ξ₂ t)‖
      ≤ 1 / (2 * π) * ((2 * Real.cosh (ξ₁ + ξ₂)) ^ |ν.re| * (π - -π)) := by gcongr
    _ = _ := by field_simp; ring

/-- The order-zero function at a fixed argument in the cut plane is entire in the degree. -/
theorem AdditionTheorem.differentiable_associatedP_zero {z : ℂ} (hz : (1 - z) / 2 ∈ cutPlane) :
    Differentiable ℂ (fun ν : ℂ => associatedP ν 0 z) := by
  simp only [ExteriorGreen.associatedP_eq]
  exact differentiable_regularizedGaussHG_comp (A := fun ν : ℂ => ν + 1) (B := fun ν : ℂ => -ν)
    (C := fun _ => 1) (by fun_prop) (by fun_prop) (by fun_prop) hz

/-- The Fourier coefficients in the hyperbolic case are entire in the degree. -/
theorem AdditionTheorem.hyperbolic_coeff_differentiable {ξ₁ ξ₂ : ℝ} (h1 : 0 ≤ ξ₁)
    (h2 : 0 ≤ ξ₂) (m : ℤ) :
    Differentiable ℂ (fun ν =>
        AdditionTheorem.coeff
        (fun t => associatedP ν 0 (AdditionTheorem.hyperbolicArg ξ₁ ξ₂ t)) m) := by
  have hz : ∀ t, (1 - ((AdditionTheorem.hyperbolicArg ξ₁ ξ₂ t : ℝ) : ℂ)) / 2 ∈
      cutPlane := fun t => by
    rw [show (1 - ((AdditionTheorem.hyperbolicArg ξ₁ ξ₂ t : ℝ) : ℂ)) / 2 =
        (((1 - AdditionTheorem.hyperbolicArg ξ₁ ξ₂ t) / 2 : ℝ) : ℂ) by
      push_cast; ring]
    exact AdditionTheorem.ofReal_mem_cutPlane
        (by linarith [(AdditionTheorem.hyperbolicArg_mem h1 h2 t).1])
  have key : DifferentiableOn ℂ (fun ν => ∫ t in (-π)..π, exp (-((m:ℂ) * t * I)) *
      associatedP ν 0 (AdditionTheorem.hyperbolicArg ξ₁ ξ₂ t)) univ := by
    apply Complex.differentiableOn_intervalIntegral_of_locally_dominated isOpen_univ
    · intro ν _
      exact ((by fun_prop : Continuous fun t : ℝ => exp (-((m:ℂ) * t * I))).mul
        (AdditionTheorem.hyperbolicArg_contDiff ν h1 h2).continuous).aestronglyMeasurable
    · refine ae_of_all _ fun t => ?_
      exact ((differentiable_const _).mul
        (AdditionTheorem.differentiable_associatedP_zero (hz t))).differentiableOn
    · intro ν₀ _
      refine ⟨Metric.ball ν₀ 1, Metric.ball_mem_nhds _ one_pos,
        fun _ => (2 * Real.cosh (ξ₁ + ξ₂)) ^ (|ν₀.re| + 1),
        integrableOn_const (by rw [uIoc_of_le (by linarith [Real.pi_pos])]; simp), ae_of_all _ ?_⟩
      intro t y hy
      rw [norm_mul, show -((m:ℂ) * t * I) = ((-(m * t) : ℝ) : ℂ) * I by push_cast; ring,
        norm_exp_ofReal_mul_I, one_mul]
      refine (AdditionTheorem.hyperbolicArg_norm_le y h1 h2 t).trans
          (Real.rpow_le_rpow_of_exponent_le ?_ ?_)
      · have := Real.one_le_cosh (ξ₁ + ξ₂); linarith
      · have hd : ‖y - ν₀‖ < 1 := by simpa [dist_eq_norm] using hy
        have h3 := abs_re_le_norm (y - ν₀)
        rw [sub_re] at h3
        have h4 := abs_sub_abs_le_abs_sub y.re ν₀.re
        linarith
  rw [← differentiableOn_univ]
  exact (key.const_mul _).congr fun ν _ => rfl

/-- `associatedP ν μ z` is entire in the degree for `(1 - z)/2` in the cut plane. -/
theorem AdditionTheorem.differentiable_associatedP (μ : ℂ) {z : ℂ} (hz : (1 - z) / 2 ∈ cutPlane) :
    Differentiable ℂ (fun ν : ℂ => associatedP ν μ z) := by
  unfold associatedP
  exact (differentiable_const _).mul (differentiable_regularizedGaussHG_comp
    (A := fun ν : ℂ => ν + 1) (B := fun ν : ℂ => -ν) (C := fun _ => 1 - μ)
    (by fun_prop) (by fun_prop) (by fun_prop) hz)

/-- `(2x)^{|r|} = exp (log (2x) |r|)`. -/
theorem AdditionTheorem.rpow_eq_exp {x : ℝ} (hx : 0 < x) (r : ℝ) :
    (2 * x) ^ |r| = Real.exp (Real.log (2 * x) * |r|) := by
  rw [Real.rpow_def_of_pos (by linarith)]

/-- The right-hand side coefficients of the hyperbolic addition theorem satisfy a Carlson bound. -/
theorem AdditionTheorem.hyperbolic_rhs_bound {x₁ x₂ : ℝ} (hx₁ : 1 < x₁) (hx₂ : 1 < x₂) (m : ℕ) :
    ∃ C : ℝ, ∀ ν : ℂ, ‖(-1:ℂ) ^ m * associatedP ν (-(m:ℂ)) x₁ * associatedP ν m x₂‖ ≤
      C * Real.exp ((Real.log (2 * x₁) + Real.log (2 * x₂) + 1) * |ν.re| + 1 * |ν.im|) := by
  have hl1 : 0 ≤ Real.log (2 * x₁) := Real.log_nonneg (by linarith)
  have hl2 : 0 ≤ Real.log (2 * x₂) := Real.log_nonneg (by linarith)
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · refine ⟨1, fun ν => ?_⟩
    rw [pow_zero, one_mul, Nat.cast_zero, neg_zero, norm_mul]
    have e1 := (AdditionTheorem.norm_associatedP_nat_le ν 0 hx₁).trans_eq (by
      rw [poch_zero, norm_one, one_mul, AdditionTheorem.rpow_eq_exp (by linarith)])
    have e2 := (AdditionTheorem.norm_associatedP_nat_le ν 0 hx₂).trans_eq (by
      rw [poch_zero, norm_one, one_mul, AdditionTheorem.rpow_eq_exp (by linarith)])
    simp only [Nat.cast_zero] at e1 e2
    calc ‖associatedP ν 0 x₁‖ * ‖associatedP ν 0 x₂‖
        ≤ Real.exp (Real.log (2 * x₁) * |ν.re|) * Real.exp (Real.log (2 * x₂) * |ν.re|) :=
          mul_le_mul e1 e2 (norm_nonneg _) (Real.exp_pos _).le
      _ ≤ 1 * Real.exp ((Real.log (2 * x₁) + Real.log (2 * x₂) + 1) * |ν.re| + 1 * |ν.im|) := by
          rw [← Real.exp_add]
          refine (Real.exp_le_exp.mpr ?_).trans (le_of_eq (one_mul _).symm)
          nlinarith [abs_nonneg ν.re, abs_nonneg ν.im]
  · set C₁ := ‖((x₁:ℂ) ^ 2 - 1) ^ (-(m:ℂ) / 2) / Gamma m‖ * ((x₁ - 1) ^ (m - 1) * (x₁ - 1))
    have hC₁ : 0 ≤ C₁ := by
      have : 0 ≤ x₁ - 1 := by linarith
      positivity
    refine ⟨C₁ * (m ! * Real.exp m), fun ν => ?_⟩
    have e1 : ‖associatedP ν (-(m:ℂ)) x₁‖ ≤ C₁ * Real.exp (Real.log (2 * x₁) * |ν.re|) := by
      refine (AdditionTheorem.norm_associatedP_neg_le ν hm hx₁).trans_eq ?_
      rw [AdditionTheorem.rpow_eq_exp (by linarith)]; ring
    have e2 : ‖associatedP ν m x₂‖ ≤ m ! * Real.exp m * Real.exp ‖ν‖ *
        Real.exp (Real.log (2 * x₂) * |ν.re|) := by
      refine (AdditionTheorem.norm_associatedP_nat_le ν m hx₂).trans ?_
      rw [AdditionTheorem.rpow_eq_exp (by linarith)]
      gcongr
      exact AdditionTheorem.norm_poch_le ν m
    have hn : ‖ν‖ ≤ |ν.re| + |ν.im| := norm_le_abs_re_add_abs_im ν
    rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    calc ‖associatedP ν (-(m:ℂ)) x₁‖ * ‖associatedP ν m x₂‖
        ≤ (C₁ * Real.exp (Real.log (2 * x₁) * |ν.re|)) * (m ! * Real.exp m * Real.exp ‖ν‖ *
            Real.exp (Real.log (2 * x₂) * |ν.re|)) :=
          mul_le_mul e1 e2 (norm_nonneg _) (by positivity)
      _ = C₁ * (m ! * Real.exp m) * Real.exp (Real.log (2 * x₁) * |ν.re| + ‖ν‖ +
            Real.log (2 * x₂) * |ν.re|) := by
          rw [Real.exp_add, Real.exp_add]; ring
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
          nlinarith [abs_nonneg ν.re, abs_nonneg ν.im]

/-- `∫_{-π}^{π} e^{ikt} dt = 2π δ_{k0}` for integer `k`. -/
theorem AdditionTheorem.integral_exp_intCast (k : ℤ) :
    (∫ t : ℝ in (-π)..π, exp (k * t * I)) = if k = 0 then 2 * (π:ℂ) else 0 := by
  split_ifs with hk
  · subst hk; simp; ring
  · have hc : (k:ℂ) * I ≠ 0 := mul_ne_zero (by exact_mod_cast hk) I_ne_zero
    have h := integral_exp_mul_complex (a := -π) (b := π) hc
    have he : exp ((k:ℂ) * I * ((π:ℝ):ℂ)) = exp ((k:ℂ) * I * ((-π:ℝ):ℂ)) := by
      have := AdditionTheorem.exp_pi (-k)
      push_cast at this ⊢
      rw [show (k:ℂ) * I * π = -(-(k:ℂ) * π * I) by ring,
        show (k:ℂ) * I * -π = -(-(k:ℂ) * -π * I) by ring, this]
    rw [show (fun t : ℝ => exp ((k:ℂ) * t * I)) = fun t : ℝ => exp ((k:ℂ) * I * t) by
      funext t; ring_nf, h, he, sub_self, zero_div]

/-- Linearity of the Fourier coefficient: sums. -/
theorem AdditionTheorem.coeff_add {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g) (m : ℤ) :
    AdditionTheorem.coeff (fun t => f t + g t) m = AdditionTheorem.coeff f m +
        AdditionTheorem.coeff g m := by
  simp only [AdditionTheorem.coeff, mul_add]
  rw [intervalIntegral.integral_add, mul_add]
  · exact ((by fun_prop : Continuous fun t : ℝ => exp (-((m:ℂ) * t * I))).mul
      hf).intervalIntegrable _ _
  · exact ((by fun_prop : Continuous fun t : ℝ => exp (-((m:ℂ) * t * I))).mul
      hg).intervalIntegrable _ _

/-- Linearity of the Fourier coefficient: scalars. -/
theorem AdditionTheorem.coeff_const_mul (c : ℂ) (f : ℝ → ℂ) (m : ℤ) :
    AdditionTheorem.coeff (fun t => c * f t) m = c * AdditionTheorem.coeff f m := by
  simp only [AdditionTheorem.coeff]
  rw [show (fun t : ℝ => exp (-((m:ℂ) * t * I)) * (c * f t)) =
    fun t : ℝ => c * (exp (-((m:ℂ) * t * I)) * f t) by funext t; ring,
    intervalIntegral.integral_const_mul]
  ring

/-- Linearity of the Fourier coefficient: finite sums. -/
theorem AdditionTheorem.coeff_sum {ι : Type*} (s : Finset ι) (F : ι → ℝ → ℂ)
    (hF : ∀ i, Continuous (F i))
    (m : ℤ) : AdditionTheorem.coeff (fun t => ∑ i ∈ s, F i t) m = ∑ i ∈ s,
        AdditionTheorem.coeff (F i) m := by
  simp only [AdditionTheorem.coeff, Finset.mul_sum]
  rw [intervalIntegral.integral_finsetSum, Finset.mul_sum]
  intro i _
  exact ((by fun_prop : Continuous fun t : ℝ => exp (-((m:ℂ) * t * I))).mul
    (hF i)).intervalIntegrable _ _

/-- The Fourier coefficients of a constant. -/
theorem AdditionTheorem.coeff_const (a : ℂ) (m : ℕ) :
    AdditionTheorem.coeff (fun _ => a) m = if m = 0 then a else 0 := by
  have h := AdditionTheorem.integral_exp_intCast (-(m:ℤ))
  rw [AdditionTheorem.coeff, show (fun t : ℝ => exp (-(((m:ℤ):ℂ) * t * I)) * a) =
    fun t : ℝ => a * exp (((-(m:ℤ) : ℤ):ℂ) * t * I) by funext t; push_cast; ring_nf,
    intervalIntegral.integral_const_mul, h]
  have hπ : (π:ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  by_cases hm : m = 0
  · subst hm; simp; field_simp
  · simp [hm]

/-- The Fourier coefficients of `cos (j t)`, `j ≥ 1`. -/
theorem AdditionTheorem.coeff_cos {j : ℕ} (hj : 1 ≤ j) (m : ℕ) :
    AdditionTheorem.coeff (fun t : ℝ => cos ((j:ℂ) * t)) m = if j = m then 1 / 2 else 0 := by
  have h1 := AdditionTheorem.integral_exp_intCast ((j:ℤ) - m)
  have h2 := AdditionTheorem.integral_exp_intCast (-((j:ℤ) + m))
  have hsplit : (fun t : ℝ => exp (-(((m:ℤ):ℂ) * t * I)) * cos ((j:ℂ) * t)) =
      fun t : ℝ => (1/2:ℂ) * exp ((((j:ℤ) - m : ℤ):ℂ) * t * I) +
        (1/2:ℂ) * exp (((-((j:ℤ) + m) : ℤ):ℂ) * t * I) := by
    funext t
    have e1 : exp ((((j:ℤ) - m : ℤ):ℂ) * t * I) =
        exp (-(((m:ℤ):ℂ) * t * I)) * exp ((j:ℂ) * t * I) := by
      rw [← exp_add]; congr 1; push_cast; ring
    have e2 : exp (((-((j:ℤ) + m) : ℤ):ℂ) * t * I) =
        exp (-(((m:ℤ):ℂ) * t * I)) * exp (-((j:ℂ) * t) * I) := by
      rw [← exp_add]; congr 1; push_cast; ring
    rw [e1, e2, Complex.cos]
    ring
  rw [AdditionTheorem.coeff, hsplit, intervalIntegral.integral_add,
      intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, h1, h2]
  · have hπ : (π:ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
    have hjm : -((j:ℤ) + m) ≠ 0 := by omega
    simp only [hjm, ite_false, mul_zero, add_zero]
    by_cases h : j = m
    · subst h; simp; field_simp
    · have : (j:ℤ) - m ≠ 0 := by omega
      simp [this, h]
  · exact ((by fun_prop : Continuous fun t : ℝ =>
      exp ((((j:ℤ) - m : ℤ):ℂ) * t * I)).const_mul _).intervalIntegrable _ _
  · exact ((by fun_prop : Continuous fun t : ℝ =>
      exp (((-((j:ℤ) + m) : ℤ):ℂ) * t * I)).const_mul _).intervalIntegrable _ _

open DLMF.OrthogonalPolynomials.LegendreAddition in
/-- The Fourier coefficients of the finite Legendre angular kernel are its coefficients. -/
theorem AdditionTheorem.coeff_kernel (n : ℕ) (x y s t : ℂ) (m : ℕ) :
    AdditionTheorem.coeff (fun u : ℝ => kernel n x y s t u) m =
        OrthogonalPolynomials.LegendreAddition.coeff n m x y s t := by
  have hc : ∀ k : ℕ, Continuous fun u : ℝ =>
      OrthogonalPolynomials.LegendreAddition.coeff n (k+1) x y s t * cos (((k:ℂ)+1) * u) :=
    fun k => by fun_prop
  have hg : Continuous fun u : ℝ => ∑ k ∈ Finset.range n,
      OrthogonalPolynomials.LegendreAddition.coeff n (k+1) x y s t * cos (((k:ℂ)+1) * u) :=
          continuous_finsetSum _ fun k _ => hc k
  unfold kernel
  rw [AdditionTheorem.coeff_add
      (f := fun _ : ℝ => OrthogonalPolynomials.LegendreAddition.coeff n 0 x y s t)
      (g := fun u : ℝ => 2 *
      ∑ k ∈ Finset.range n, OrthogonalPolynomials.LegendreAddition.coeff n (k+1) x y s t *
          cos (((k:ℂ)+1) * u)) continuous_const
      (continuous_const.mul hg), AdditionTheorem.coeff_const,
    AdditionTheorem.coeff_const_mul (f := fun u : ℝ => ∑ k ∈ Finset.range n,
      OrthogonalPolynomials.LegendreAddition.coeff n (k+1) x y s t * cos (((k:ℂ)+1) * u)),
    AdditionTheorem.coeff_sum
        (F := fun k (u : ℝ) => OrthogonalPolynomials.LegendreAddition.coeff n (k+1) x y s t *
        cos (((k:ℂ)+1) * u)) _
      fun k => hc k]
  have hterm : ∀ k : ℕ,
      AdditionTheorem.coeff
      (fun u : ℝ => OrthogonalPolynomials.LegendreAddition.coeff n (k+1) x y s t *
      cos (((k:ℂ)+1) * u)) m = if k + 1 = m then
          OrthogonalPolynomials.LegendreAddition.coeff n (k+1) x y s t / 2 else 0 := by
    intro k
    rw [AdditionTheorem.coeff_const_mul]
    have := AdditionTheorem.coeff_cos (j := k + 1) (by omega) m
    push_cast at this
    rw [this]
    split_ifs <;> ring
  simp only [hterm]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · rw [show (if m = 0 then OrthogonalPolynomials.LegendreAddition.coeff n 0 x y s t else 0) = 0 by
        simp; omega, zero_add]
    obtain ⟨p, rfl⟩ : ∃ p, m = p + 1 := ⟨m - 1, by omega⟩
    simp only [add_left_inj, Finset.sum_ite_eq', Finset.mem_range]
    split_ifs with hp
    · ring
    · rw [coeff_eq_zero (by omega)]; ring

open DLMF.OrthogonalPolynomials.LegendreAddition in
/-- Integer degree and order on `(1, ∞)`: `P^m_n(x) = (x²-1)^{m/2} P_n^{(m)}(x)`. -/
theorem AdditionTheorem.associatedP_nat_nat (n m : ℕ) {x : ℝ} (hx : 1 < x) :
    associatedP n m x = (Real.sqrt (x ^ 2 - 1) : ℂ) ^ m * jet n m x := by
  have hz := LaplaceIntegrals.one_lt_mem hx
  have hev : associatedP (n:ℂ) 0 =ᶠ[𝓝 (x:ℂ)] DLMF.OrthogonalPolynomials.legendrePolyP n := by
    filter_upwards [(isOpen_slitPlane.preimage (by fun_prop : Continuous fun w : ℂ => w-1)).mem_nhds
      hz] with w hw
    rw [associatedP_zero_order _ hw, legendreP_nat n (one_add_mem_slitPlane_of_sub_one hw)]
  rw [associatedP_nat_order_derivative n m hz, hev.iteratedDeriv_eq,
    OrthogonalityIntegrals.legendreBranchPower_real _ hx]
  have hpow : ((x:ℂ)^2-1)^((m:ℂ)/2) = (Real.sqrt (x^2-1):ℂ)^m := by
    rw [show (x:ℂ)^2-1 = ((x^2-1:ℝ):ℂ) by push_cast; ring,
      show (m:ℂ)/2 = (((m:ℝ)/2 : ℝ):ℂ) by push_cast; ring, ← ofReal_cpow (by nlinarith),
      ← ofReal_pow]
    congr 1
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast (by nlinarith)]
    ring_nf
  rw [hpow]; rfl

/-- `√(cosh² ξ - 1) = sinh ξ` for `ξ ≥ 0`. -/
theorem AdditionTheorem.sqrt_cosh_sq {ξ : ℝ} (h : 0 ≤ ξ) : Real.sqrt (Real.cosh ξ ^ 2 - 1) =
    Real.sinh ξ := by
  rw [Real.cosh_sq, add_sub_cancel_right, Real.sqrt_sq (Real.sinh_nonneg_iff.2 h)]

open DLMF.OrthogonalPolynomials.LegendreAddition in
/-- The hyperbolic addition theorem at integer degree, coefficientwise. -/
theorem AdditionTheorem.hyperbolic_nat (n : ℕ) {ξ₁ ξ₂ : ℝ} (h1 : 0 < ξ₁) (h2 : 0 < ξ₂) (m : ℕ) :
    AdditionTheorem.coeff (fun t => associatedP (n:ℂ) 0 (AdditionTheorem.hyperbolicArg ξ₁ ξ₂ t)) m =
      (-1:ℂ) ^ m * associatedP n (-(m:ℂ)) (Real.cosh ξ₁) * associatedP n m (Real.cosh ξ₂) := by
  have hsq : ∀ ξ : ℝ, (I * (Real.sinh ξ : ℂ)) ^ 2 = 1 - (Real.cosh ξ : ℂ) ^ 2 := by
    intro ξ
    have h' : ((Real.cosh ξ : ℝ) : ℂ) ^ 2 = (Real.sinh ξ : ℂ) ^ 2 + 1 := by
      rw [← ofReal_pow, Real.cosh_sq]; push_cast; ring
    rw [mul_pow, I_sq, h']; ring
  have hfun : (fun u : ℝ => associatedP (n:ℂ) 0 (AdditionTheorem.hyperbolicArg ξ₁ ξ₂ u)) =
      fun u : ℝ => kernel n (Real.cosh ξ₁) (Real.cosh ξ₂) (I * Real.sinh ξ₁)
          (I * Real.sinh ξ₂) u := by
    funext u
    obtain ⟨hX1, -⟩ := AdditionTheorem.hyperbolicArg_mem h1.le h2.le u
    rw [AdditionTheorem.associatedP_zero hX1, legendreP_nat n (Or.inl (by simp; linarith)),
      ← legendre_eq_kernel n _ _ _ _ u (hsq ξ₁) (hsq ξ₂)]
    congr 1
    have hI : (I * (Real.sinh ξ₁ : ℂ)) * (I * Real.sinh ξ₂) =
        -((Real.sinh ξ₁ : ℂ) * Real.sinh ξ₂) := by
      rw [show (I * (Real.sinh ξ₁ : ℂ)) * (I * Real.sinh ξ₂) = I ^ 2 *
          ((Real.sinh ξ₁ : ℂ) * Real.sinh ξ₂) by ring,
        I_sq]; ring
    rw [hI, AdditionTheorem.hyperbolicArg]
    push_cast
    ring
  have hc1 : (1:ℝ) < Real.cosh ξ₁ := Real.one_lt_cosh.2 h1.ne'
  have hc2 : (1:ℝ) < Real.cosh ξ₂ := Real.one_lt_cosh.2 h2.ne'
  rw [hfun, AdditionTheorem.coeff_kernel]
  rcases le_or_gt m n with hmn | hmn
  · have hG : ∀ j : ℕ, (n:ℂ) - m + 1 ≠ -j := by
      intro j h
      have : ((n - m + 1 + j : ℕ) : ℂ) = 0 := by push_cast [Nat.cast_sub hmn]; linear_combination h
      exact absurd (Nat.cast_eq_zero.1 this) (by omega)
    rw [associatedP_negative_integer_order (n:ℂ) m hG (LaplaceIntegrals.one_lt_mem hc1),
      show (n:ℂ) - m + 1 = ((n - m : ℕ) : ℂ) + 1 by push_cast [Nat.cast_sub hmn]; ring,
      show (n:ℂ) + m + 1 = ((n + m : ℕ) : ℂ) + 1 by push_cast; ring,
      Gamma_nat_eq_factorial, Gamma_nat_eq_factorial,
      AdditionTheorem.associatedP_nat_nat n m hc1, AdditionTheorem.associatedP_nat_nat n m hc2,
      AdditionTheorem.sqrt_cosh_sq h1.le, AdditionTheorem.sqrt_cosh_sq h2.le]
    simp only [OrthogonalPolynomials.LegendreAddition.coeff, weight]
    rw [show (I * (Real.sinh ξ₁ : ℂ) * (I * Real.sinh ξ₂)) = -((Real.sinh ξ₁ : ℂ) * Real.sinh ξ₂) by
      rw [show (I * (Real.sinh ξ₁ : ℂ)) * (I * Real.sinh ξ₂) = I ^ 2 *
          ((Real.sinh ξ₁ : ℂ) * Real.sinh ξ₂) by ring,
        I_sq]; ring, neg_pow, mul_pow]
    ring
  · rw [coeff_eq_zero hmn, AdditionTheorem.associatedP_nat_nat n m hc2, jet_eq_zero hmn]
    simp

/-- The Fourier coefficients of `φ ↦ P_ν(cosh ξ₁ cosh ξ₂ - sinh ξ₁ sinh ξ₂ cos φ)`, for every
complex degree (Carlson's theorem from the integer case). -/
theorem AdditionTheorem.hyperbolic_coeff_eq (ν : ℂ) {ξ₁ ξ₂ : ℝ} (h1 : 0 < ξ₁)
    (h2 : 0 < ξ₂) (m : ℕ) :
    AdditionTheorem.coeff (fun t => associatedP ν 0 (AdditionTheorem.hyperbolicArg ξ₁ ξ₂ t)) m =
      (-1:ℂ) ^ m * associatedP ν (-(m:ℂ)) (Real.cosh ξ₁) * associatedP ν m (Real.cosh ξ₂) := by
  have hc1 : (1:ℝ) < Real.cosh ξ₁ := Real.one_lt_cosh.2 h1.ne'
  have hc2 : (1:ℝ) < Real.cosh ξ₂ := Real.one_lt_cosh.2 h2.ne'
  have hz : ∀ x : ℝ, 1 < x → (1 - (x:ℂ)) / 2 ∈ cutPlane := fun x hx => by
    rw [show (1 - (x:ℂ)) / 2 = (((1 - x) / 2 : ℝ) : ℂ) by push_cast; ring]
    exact AdditionTheorem.ofReal_mem_cutPlane (by linarith)
  obtain ⟨C, hC⟩ := AdditionTheorem.hyperbolic_rhs_bound hc1 hc2 m
  set A := Real.log (2 * Real.cosh ξ₁) + Real.log (2 * Real.cosh ξ₂) + 1
  set K := 2 * Real.cosh (ξ₁ + ξ₂)
  have hK : 1 ≤ K := by have := Real.one_le_cosh (ξ₁ + ξ₂); simp only [K]; linarith
  have hlK : 0 ≤ Real.log K := Real.log_nonneg hK
  have hA : 0 ≤ A := by
    have := Real.log_nonneg (by linarith : (1:ℝ) ≤ 2 * Real.cosh ξ₁)
    have := Real.log_nonneg (by linarith : (1:ℝ) ≤ 2 * Real.cosh ξ₂)
    simp only [A]; linarith
  have key := AdditionTheorem.eq_zero_of_carlson
      (f := fun ν => AdditionTheorem.coeff (fun t => associatedP ν 0
      (AdditionTheorem.hyperbolicArg ξ₁ ξ₂ t)) m - (-1:ℂ) ^ m *
          associatedP ν (-(m:ℂ)) (Real.cosh ξ₁) *
      associatedP ν m (Real.cosh ξ₂))
    ((AdditionTheorem.hyperbolic_coeff_differentiable h1.le h2.le m).sub
      (((differentiable_const _).mul (AdditionTheorem.differentiable_associatedP _ (hz _ hc1))).mul
        (AdditionTheorem.differentiable_associatedP _ (hz _ hc2))))
    (C := 1 + |C|) (A := Real.log K + A) (B := 1) (by linarith) zero_le_one
    (by linarith [Real.pi_gt_three])
    (fun w _ => by
      refine (norm_sub_le _ _).trans ?_
      have e1 := AdditionTheorem.hyperbolic_coeff_bound w h1.le h2.le m
      rw [show (2 * Real.cosh (ξ₁ + ξ₂)) = 2 * (Real.cosh (ξ₁ + ξ₂)) from rfl,
        AdditionTheorem.rpow_eq_exp (Real.cosh_pos _)] at e1
      have e2 := hC w
      have hE1 : Real.exp (Real.log K * |w.re|) ≤
          Real.exp ((Real.log K + A) * |w.re| + 1 * |w.im|) :=
        Real.exp_le_exp.mpr (by nlinarith [abs_nonneg w.re, abs_nonneg w.im])
      have hE2 : Real.exp (A * |w.re| + 1 * |w.im|) ≤
          Real.exp ((Real.log K + A) * |w.re| + 1 * |w.im|) :=
        Real.exp_le_exp.mpr (by nlinarith [abs_nonneg w.re, abs_nonneg w.im])
      have hCa : C * Real.exp (A * |w.re| + 1 * |w.im|) ≤
          |C| * Real.exp ((Real.log K + A) * |w.re| + 1 * |w.im|) :=
        (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le).trans
          (mul_le_mul_of_nonneg_left hE2 (abs_nonneg C))
      have e1' : ‖AdditionTheorem.coeff
          (fun t => associatedP w 0 (AdditionTheorem.hyperbolicArg ξ₁ ξ₂ t)) m‖ ≤
          Real.exp (Real.log K * |w.re|) := e1
      nlinarith)
    (fun n => by rw [AdditionTheorem.hyperbolic_nat n h1 h2 m, sub_self]) ν
  exact sub_eq_zero.mp key

/-- At coincident arguments and phi zero, the order-zero P value is understood by its regular
extension at one. -/
@[dlmf 14.18.E4]
theorem associatedP_addition (ν : ℂ) {ξ₁ ξ₂ : ℝ} (h1 : 0 < ξ₁) (h2 : 0 < ξ₂) (phi : ℝ) :
    HasSum (fun j : ℕ => let m:=j+1;
        2*(-1)^m*associatedP ν (-m) (Real.cosh ξ₁)*associatedP ν m (Real.cosh ξ₂)*Real.cos (m*phi))
        (associatedP ν 0 (Real.cosh ξ₁*Real.cosh ξ₂-Real.sinh ξ₁*Real.sinh ξ₂*Real.cos
        phi)-associatedP ν 0 (Real.cosh ξ₁)*associatedP ν 0 (Real.cosh ξ₂)) := by
  have hper : Function.Periodic
      (fun t : ℝ => associatedP ν 0 (AdditionTheorem.hyperbolicArg ξ₁ ξ₂ t)) (2 * π) :=
    fun t => by simp only [AdditionTheorem.hyperbolicArg, Real.cos_add_two_pi]
  have hev : ∀ t, (fun t : ℝ => associatedP ν 0 (AdditionTheorem.hyperbolicArg ξ₁ ξ₂ t)) (-t) =
      (fun t : ℝ => associatedP ν 0 (AdditionTheorem.hyperbolicArg ξ₁ ξ₂ t)) t :=
    fun t => by simp only [AdditionTheorem.hyperbolicArg, Real.cos_neg]
  have hF := AdditionTheorem.hasSum_cos
      (AdditionTheorem.hyperbolicArg_contDiff ν h1.le h2.le) hper hev phi
  have h0 := AdditionTheorem.hyperbolic_coeff_eq ν h1 h2 0
  simp only [pow_zero, one_mul, Nat.cast_zero, neg_zero] at h0
  convert hF using 1
  · funext j
    rw [AdditionTheorem.hyperbolic_coeff_eq ν h1 h2 (j + 1)]
    push_cast
    ring
  · rw [h0, AdditionTheorem.hyperbolicArg]; push_cast; rfl

/-! ### The Ferrers case (14.18.1) -/

/-- Wallis' integral in Gamma form: `∫₀^π sin^{2n} t dt = √π Γ(n + 1/2)/n!`. -/
theorem AdditionTheorem.integral_sin_pow_even (n : ℕ) :
    (∫ t : ℝ in (0:ℝ)..π, (((Real.sin t) ^ 2 : ℝ) : ℂ) ^ n) =
      (Real.sqrt π : ℂ) * Gamma (1 / 2 + n) / n ! := by
  have hR : ∀ n : ℕ, (∫ t : ℝ in (0:ℝ)..π, (((Real.sin t) ^ 2 : ℝ) : ℂ) ^ n) =
      ((∫ t : ℝ in (0:ℝ)..π, Real.sin t ^ (2 * n) : ℝ) : ℂ) := by
    intro n
    rw [← intervalIntegral.integral_ofReal]
    refine intervalIntegral.integral_congr fun t _ => ?_
    push_cast; ring
  rw [hR]
  induction n with
  | zero =>
    simp only [mul_zero, pow_zero, intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one,
      CharP.cast_eq_zero, add_zero, Nat.factorial_zero, Nat.cast_one, div_one]
    rw [legendre_Gamma_one_half, ← ofReal_mul, Real.mul_self_sqrt Real.pi_pos.le]
  | succ n ih =>
    have h := integral_sin_pow (a := 0) (b := π) (n := 2 * n)
    simp only [Real.sin_zero, Real.sin_pi, zero_pow (Nat.succ_ne_zero _), zero_mul, sub_self,
      zero_div, zero_add] at h
    rw [show 2 * (n + 1) = 2 * n + 2 by ring, h, ofReal_mul, ih]
    have hG : Gamma (1 / 2 + ((n + 1 : ℕ) : ℂ)) = (1 / 2 + n) * Gamma (1 / 2 + n) := by
      rw [show (1:ℂ) / 2 + ((n + 1 : ℕ) : ℂ) = (1 / 2 + n) + 1 by push_cast; ring,
        Gamma_add_one _ (by
          intro h0; have := congrArg Complex.re h0; simp at this;
              linarith [(n.cast_nonneg : (0:ℝ) ≤ n)])]
    rw [hG, Nat.factorial_succ]
    push_cast
    field_simp
    ring

/-- `𝐅(ν+1, -ν; 1; s) = π^{-1/2} ∫₀^π 𝐅(ν+1, -ν; 1/2; s sin² t) dt` for `0 ≤ s < 1`
(the Mehler–Dirichlet integral in disguise). -/
theorem AdditionTheorem.regularizedGaussHG_one_eq_integral (ν : ℂ) {s : ℝ} (hs0 : 0 ≤ s)
    (hs1 : s < 1) :
    regularizedGaussHGFun (ν + 1) (-ν) 1 s = 1 / (Real.sqrt π : ℂ) *
      ∫ t : ℝ in (0:ℝ)..π,
          regularizedGaussHGFun (ν + 1) (-ν) (1 / 2) ((s * Real.sin t ^ 2 : ℝ)) := by
  have hsn : ‖(s:ℂ)‖ < 1 := by rw [norm_real, Real.norm_eq_abs, abs_of_nonneg hs0]; exact hs1
  set e : ℕ → ℂ := fun n => (ascPochhammer ℂ n).eval (ν + 1) * (ascPochhammer ℂ n).eval (-ν) *
    (s:ℂ) ^ n / n.factorial * (Gamma (1 / 2 + n))⁻¹ with he_def
  have he : Summable (fun n => ‖e n‖) := summable_norm_regularizedGaussHGFun_term _ _ _ hsn
  set F : ℕ → ℝ → ℂ := fun n t => e n * (((Real.sin t) ^ 2 : ℝ) : ℂ) ^ n with hF_def
  have hFc : ∀ n, Continuous (F n) := fun n => by simp only [hF_def]; fun_prop
  have hs := intervalIntegral.hasSum_integral_of_dominated_convergence
    (a := (0 : ℝ)) (b := π) (μ := MeasureTheory.volume) (F := F)
    (f := fun t => regularizedGaussHGFun (ν + 1) (-ν) (1 / 2) ((s * Real.sin t ^ 2 : ℝ)))
    (fun n _ => ‖e n‖) (fun n => (hFc n).aestronglyMeasurable)
    (fun n => Filter.Eventually.of_forall fun t _ => by
      simp only [hF_def, norm_mul, norm_pow]
      have : ‖(((Real.sin t) ^ 2 : ℝ) : ℂ)‖ ≤ 1 := by
        rw [norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        nlinarith [Real.sin_sq_add_cos_sq t, sq_nonneg (Real.cos t)]
      calc ‖e n‖ * ‖(((Real.sin t) ^ 2 : ℝ) : ℂ)‖ ^ n ≤ ‖e n‖ * 1 ^ n := by gcongr
        _ = ‖e n‖ := by simp)
    (Filter.Eventually.of_forall fun t _ => he)
    intervalIntegrable_const
    (Filter.Eventually.of_forall fun t _ => by
      have hz : ‖(((s * Real.sin t ^ 2 : ℝ)) : ℂ)‖ < 1 := by
        rw [norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        have h1 : Real.sin t ^ 2 ≤ 1 := by
                                          nlinarith [Real.sin_sq_add_cos_sq t,
                                            sq_nonneg (Real.cos t)]
        nlinarith
      refine (hasSum_regularizedGaussHGFun (ν + 1) (-ν) (1 / 2) hz).congr_fun fun n => ?_
      simp only [hF_def, he_def]
      push_cast
      ring)
  have hint : ∀ n, (∫ t : ℝ in (0:ℝ)..π, F n t) = (Real.sqrt π : ℂ) *
      ((ascPochhammer ℂ n).eval (ν + 1) * (ascPochhammer ℂ n).eval (-ν) * (s:ℂ) ^ n /
        n.factorial * (Gamma (1 + n))⁻¹) := by
    intro n
    simp only [hF_def]
    rw [intervalIntegral.integral_const_mul, AdditionTheorem.integral_sin_pow_even,
      show (1:ℂ) + n = (n:ℂ) + 1 by ring, Gamma_nat_eq_factorial]
    have hG : Gamma (1 / 2 + n) ≠ 0 := Gamma_ne_zero_of_re_pos (by
      simp; linarith [(n.cast_nonneg : (0:ℝ) ≤ n)])
    have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    simp only [he_def]
    generalize Gamma (1 / 2 + n) = G at hG ⊢
    field_simp
  simp only [hint] at hs
  have h1 := (hasSum_regularizedGaussHGFun (ν + 1) (-ν) 1 hsn).mul_left (Real.sqrt π : ℂ)
  have hπ : (Real.sqrt π : ℂ) ≠ 0 := ofReal_ne_zero.2 (Real.sqrt_pos.2 Real.pi_pos).ne'
  rw [hs.unique h1]
  field_simp

/-- `(1 - cos θ)/2 = sin²(θ/2)`. -/
theorem AdditionTheorem.one_sub_cos_half (θ : ℝ) : (1 - Real.cos θ) / 2 = Real.sin (θ / 2) ^ 2 := by
  have h := Real.cos_two_mul (θ / 2)
  rw [show 2 * (θ / 2) = θ by ring] at h
  have := Real.sin_sq_add_cos_sq (θ / 2)
  linarith

/-- **Sharp exponential bound for Ferrers functions of order zero**:
`|𝖯_ν(cos θ)| ≤ e^{θ |Im ν|} / cos(θ/2)` for `0 ≤ θ < π` and all complex `ν`. -/
theorem AdditionTheorem.norm_ferrersP_zero_le (ν : ℂ) {θ : ℝ} (h0 : 0 ≤ θ) (hπ : θ < π) :
    ‖ferrersP ν 0 (Real.cos θ)‖ ≤ Real.exp (θ * |ν.im|) / Real.cos (θ / 2) := by
  set c := Real.sin (θ / 2) with hc
  have hc0 : 0 ≤ c := Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  have hc1 : c < 1 := by
    rw [hc, ← Real.sin_pi_div_two]
    exact Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith) le_rfl (by linarith)
  have hcos : 0 < Real.cos (θ / 2) := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hs1 : c ^ 2 < 1 := by nlinarith
  have hF : ferrersP ν 0 (Real.cos θ) = regularizedGaussHGFun (ν + 1) (-ν) 1 ((c ^ 2 : ℝ)) := by
    simp only [ferrersP, zero_div, cpow_zero, one_mul, sub_zero]
    rw [show (1 - ((Real.cos θ : ℝ) : ℂ)) / 2 = ((c ^ 2 : ℝ) : ℂ) by
      rw [hc, ← AdditionTheorem.one_sub_cos_half]; push_cast; ring]
    exact regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ (by
      rw [norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hs1)
  rw [hF, AdditionTheorem.regularizedGaussHG_one_eq_integral ν (sq_nonneg c) hs1]
  have hsq : (Real.sqrt π : ℝ) ^ 2 = π := Real.sq_sqrt Real.pi_pos.le
  have hsqp : 0 < Real.sqrt π := Real.sqrt_pos.2 Real.pi_pos
  set B := Real.exp (θ * |ν.im|) / Real.cos (θ / 2) with hB
  have hpt : ∀ t : ℝ, ‖regularizedGaussHGFun (ν + 1) (-ν) (1 / 2) ((c ^ 2 * Real.sin t ^ 2 : ℝ))‖ ≤
      B / Real.sqrt π := by
    intro t
    set y := c * Real.sin t
    have hy1 : |y| ≤ c := by
      rw [abs_mul, abs_of_nonneg hc0]
      exact mul_le_of_le_one_right hc0 (Real.abs_sin_le_one t)
    set w := Real.arcsin y
    have hw : |w| ≤ θ / 2 := by
      have hθ2 : Real.arcsin c = θ / 2 := by
        rw [hc]; exact Real.arcsin_sin (by linarith) (by linarith)
      rw [abs_le]
      constructor
      · have := Real.arcsin_le_arcsin (neg_le_of_abs_le hy1)
        rw [Real.arcsin_neg, hθ2] at this; exact this
      · have := Real.arcsin_le_arcsin (le_of_abs_le hy1)
        rw [hθ2] at this; exact this
    have hwπ : |w| < π / 2 := by linarith
    have hsw : Real.sin w = y := Real.sin_arcsin (by linarith [neg_abs_le y]) (by
      linarith [le_abs_self y])
    have hcw : Real.cos (θ / 2) ≤ Real.cos w := by
      rw [← Real.cos_abs w]
      exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith) hw
    have hcw0 : 0 < Real.cos w := hcos.trans_le hcw
    have hc12 : ∀ k : ℕ, (1 / 2 : ℂ) ≠ -(k : ℂ) := fun k h => by
      have := congrArg Complex.re h; simp at this; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    rw [show ((c ^ 2 * Real.sin t ^ 2 : ℝ) : ℂ) = (Real.sin w : ℂ) ^ 2 by
        rw [hsw]; simp only [y]; push_cast; ring,
      regularizedGaussHGFun_eq_div_Gamma hc12, legendre_Gamma_one_half,
      show -ν = 1 - (ν + 1) by ring, sin_sq_cos_quotient (ν + 1) hwπ, norm_div, norm_div,
      Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos hcw0, abs_of_pos hsqp]
    gcongr
    rw [hB]
    refine div_le_div₀ (Real.exp_pos _).le ?_ hcos hcw
    refine (FerrersFourier.norm_cos_le _).trans (Real.exp_le_exp.mpr ?_)
    have him : ((2 * (ν + 1) - 1) * (w : ℂ)).im = 2 * ν.im * w := by simp
    rw [him, abs_mul, abs_mul, abs_two]
    nlinarith [abs_nonneg ν.im]
  have hI := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := π)
    (C := B / Real.sqrt π)
    (f := fun t : ℝ => regularizedGaussHGFun (ν + 1) (-ν) (1 / 2) ((c ^ 2 * Real.sin t ^ 2 : ℝ)))
    (fun t _ => hpt t)
  rw [sub_zero, abs_of_pos Real.pi_pos] at hI
  rw [norm_mul, show ‖(1:ℂ) / (Real.sqrt π : ℂ)‖ = 1 / Real.sqrt π by
    rw [norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hsqp]]
  calc 1 / Real.sqrt π * ‖∫ t : ℝ in (0:ℝ)..π,
        regularizedGaussHGFun (ν + 1) (-ν) (1 / 2) ((c ^ 2 * Real.sin t ^ 2 : ℝ))‖
      ≤ 1 / Real.sqrt π * (B / Real.sqrt π * π) := by gcongr
    _ = B * (π / Real.sqrt π ^ 2) := by ring
    _ = B := by rw [hsq, div_self Real.pi_ne_zero, mul_one]

/-- The bound `AdditionTheorem.norm_ferrersP_zero_le` on `[cos Θ, 1]`. -/
theorem AdditionTheorem.norm_ferrersP_zero_le_of_mem (ν : ℂ) {Θ x : ℝ} (h0 : 0 ≤ Θ) (hπ : Θ < π)
    (hx1 : Real.cos Θ ≤ x) (hx2 : x ≤ 1) :
    ‖ferrersP ν 0 x‖ ≤ Real.exp (Θ * |ν.im|) / Real.cos (Θ / 2) := by
  have hxm : -1 ≤ x := le_trans (Real.neg_one_le_cos Θ) hx1
  set γ := Real.arccos x
  have hγ0 : 0 ≤ γ := Real.arccos_nonneg x
  have hγ : γ ≤ Θ := by
    have := Real.arccos_le_arccos hx1
    rwa [Real.arccos_cos h0 (by linarith)] at this
  have hxγ : Real.cos γ = x := Real.cos_arccos hxm hx2
  have h := AdditionTheorem.norm_ferrersP_zero_le ν hγ0 (by linarith)
  rw [hxγ] at h
  refine h.trans (div_le_div₀ (Real.exp_pos _).le (Real.exp_le_exp.mpr (by
    nlinarith [abs_nonneg ν.im])) (Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩)
    (Real.cos_le_cos_of_nonneg_of_le_pi (by linarith) (by linarith) (by linarith)))

/-- The argument `cos θ₁ cos θ₂ + sin θ₁ sin θ₂ cos t` of the Ferrers addition theorem. -/
def AdditionTheorem.ferrersArg (θ₁ θ₂ t : ℝ) : ℝ :=
  Real.cos θ₁ * Real.cos θ₂ + Real.sin θ₁ * Real.sin θ₂ * Real.cos t

/-- For `θ₁, θ₂ ≥ 0` with `θ₁ + θ₂ < π` and real `t`,
`cos (θ₁ + θ₂) ≤ AdditionTheorem.ferrersArg θ₁ θ₂ t ≤ 1`. -/
theorem AdditionTheorem.ferrersArg_mem {θ₁ θ₂ : ℝ} (h1 : 0 ≤ θ₁) (h2 : 0 ≤ θ₂)
    (hs : θ₁ + θ₂ < π) (t : ℝ) :
    Real.cos (θ₁ + θ₂) ≤ AdditionTheorem.ferrersArg θ₁ θ₂ t ∧
        AdditionTheorem.ferrersArg θ₁ θ₂ t ≤ 1 := by
  have hs1 : 0 ≤ Real.sin θ₁ := Real.sin_nonneg_of_nonneg_of_le_pi h1 (by linarith)
  have hs2 : 0 ≤ Real.sin θ₂ := Real.sin_nonneg_of_nonneg_of_le_pi h2 (by linarith)
  have hss := mul_nonneg hs1 hs2
  have hc1 := Real.cos_le_one t
  have hc2 := Real.neg_one_le_cos t
  have hsub := Real.cos_le_one (θ₁ - θ₂)
  rw [Real.cos_sub] at hsub
  rw [Real.cos_add]
  unfold AdditionTheorem.ferrersArg
  constructor <;> nlinarith

/-- The order-zero Ferrers function along `AdditionTheorem.ferrersArg` is `C²` in the angle. -/
theorem AdditionTheorem.ferrersArg_contDiff (ν : ℂ) {θ₁ θ₂ : ℝ} (h1 : 0 ≤ θ₁) (h2 : 0 ≤ θ₂)
    (hs : θ₁ + θ₂ < π) :
    ContDiff ℝ 2 (fun t : ℝ => ferrersP ν 0 (AdditionTheorem.ferrersArg θ₁ θ₂ t)) := by
  have hG : DifferentiableOn ℂ (fun z => regularizedGaussHG (ν + 1) (-ν) 1 z) cutPlane :=
    DifferentiableOn.regularizedGaussHG (differentiableOn_const _) (differentiableOn_const _)
      (differentiableOn_const _) differentiableOn_id fun w hw => hw
  have hG2 : ContDiffOn ℝ 2 (fun z => regularizedGaussHG (ν + 1) (-ν) 1 z) cutPlane :=
    (hG.contDiffOn isOpen_cutPlane).restrict_scalars ℝ
  have hh : ContDiff ℝ 2
      (fun t : ℝ => (((1 - AdditionTheorem.ferrersArg θ₁ θ₂ t) / 2 : ℝ) : ℂ)) := by
    refine ofRealCLM.contDiff.comp ?_
    unfold AdditionTheorem.ferrersArg
    exact (contDiff_const.sub
        (contDiff_const.add (contDiff_const.mul Real.contDiff_cos))).div_const 2
  have hc : -1 < Real.cos (θ₁ + θ₂) := by
    rw [← Real.cos_pi]; exact Real.cos_lt_cos_of_nonneg_of_le_pi (by linarith) le_rfl hs
  have := hG2.comp_contDiff hh fun t =>
    AdditionTheorem.ofReal_mem_cutPlane
        (by linarith [(AdditionTheorem.ferrersArg_mem h1 h2 hs t).1])
  convert this using 1
  funext t
  simp only [Function.comp, FerrersGreen.ferrersP_zero_eq_regularizedGaussHG]
  congr 1; push_cast; ring

/-- `-1 < cos (θ₁ + θ₂)`. -/
theorem AdditionTheorem.neg_one_lt_cos {θ : ℝ} (h0 : 0 ≤ θ) (hs : θ < π) : -1 < Real.cos θ := by
  rw [← Real.cos_pi]; exact Real.cos_lt_cos_of_nonneg_of_le_pi h0 le_rfl hs

/-- Order-zero Ferrers values along `AdditionTheorem.ferrersArg` obey the sharp exponential bound.
-/
theorem AdditionTheorem.ferrersArg_norm_le (ν : ℂ) {θ₁ θ₂ : ℝ} (h1 : 0 ≤ θ₁) (h2 : 0 ≤ θ₂)
    (hs : θ₁ + θ₂ < π)
    (t : ℝ) : ‖ferrersP ν 0 (AdditionTheorem.ferrersArg θ₁ θ₂ t)‖ ≤
      Real.exp ((θ₁ + θ₂) * |ν.im|) / Real.cos ((θ₁ + θ₂) / 2) :=
  AdditionTheorem.norm_ferrersP_zero_le_of_mem ν (by linarith) hs
      (AdditionTheorem.ferrersArg_mem h1 h2 hs t).1
    (AdditionTheorem.ferrersArg_mem h1 h2 hs t).2

/-- Bound on the Fourier coefficients in the Ferrers case. -/
theorem AdditionTheorem.ferrers_coeff_bound (ν : ℂ) {θ₁ θ₂ : ℝ} (h1 : 0 ≤ θ₁) (h2 : 0 ≤ θ₂)
    (hs : θ₁ + θ₂ < π)
    (m : ℤ) : ‖AdditionTheorem.coeff
        (fun t => ferrersP ν 0 (AdditionTheorem.ferrersArg θ₁ θ₂ t)) m‖ ≤
      Real.exp ((θ₁ + θ₂) * |ν.im|) / Real.cos ((θ₁ + θ₂) / 2) := by
  rw [AdditionTheorem.coeff, norm_mul]
  have hI := intervalIntegral.norm_integral_le_of_norm_le_const (a := -π) (b := π)
    (C := Real.exp ((θ₁ + θ₂) * |ν.im|) / Real.cos ((θ₁ + θ₂) / 2))
    (f := fun t : ℝ => exp (-((m:ℂ) * t * I)) * ferrersP ν 0 (AdditionTheorem.ferrersArg θ₁ θ₂ t))
    (fun t _ => by
      rw [norm_mul, show -((m:ℂ) * t * I) = ((-(m * t) : ℝ) : ℂ) * I by push_cast; ring,
        norm_exp_ofReal_mul_I, one_mul]
      exact AdditionTheorem.ferrersArg_norm_le ν h1 h2 hs t)
  have hπ := Real.pi_pos
  rw [abs_of_pos (by linarith : (0:ℝ) < π - -π)] at hI
  rw [show ‖(1:ℂ) / (2 * π)‖ = 1 / (2 * π) by
    rw [norm_div, norm_one, norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hπ]]
  calc 1 / (2 * π) * ‖∫ t : ℝ in (-π)..π, exp (-((m:ℂ) * t * I)) *
        ferrersP ν 0 (AdditionTheorem.ferrersArg θ₁ θ₂ t)‖
      ≤ 1 / (2 * π) * (Real.exp ((θ₁ + θ₂) * |ν.im|) / Real.cos ((θ₁ + θ₂) / 2) * (π - -π)) := by
        gcongr
    _ = _ := by field_simp; ring

/-- `ferrersP ν μ x` is entire in the degree for `x ∈ (-1, 1]`. -/
theorem AdditionTheorem.differentiable_ferrersP (μ : ℂ) {x : ℝ} (hx : -1 < x) :
    Differentiable ℂ (fun ν : ℂ => ferrersP ν μ x) := by
  unfold ferrersP
  refine (differentiable_const _).mul (differentiable_regularizedGaussHG_comp
    (A := fun ν : ℂ => ν + 1) (B := fun ν : ℂ => -ν) (C := fun _ => 1 - μ)
    (by fun_prop) (by fun_prop) (by fun_prop) ?_)
  rw [show (1 - (x:ℂ)) / 2 = (((1 - x) / 2 : ℝ) : ℂ) by push_cast; ring]
  exact AdditionTheorem.ofReal_mem_cutPlane (by linarith)

/-- The Fourier coefficients in the Ferrers case are entire in the degree. -/
theorem AdditionTheorem.ferrers_coeff_differentiable {θ₁ θ₂ : ℝ} (h1 : 0 ≤ θ₁) (h2 : 0 ≤ θ₂)
    (hs : θ₁ + θ₂ < π)
    (m : ℤ) :
    Differentiable ℂ (fun ν =>
        AdditionTheorem.coeff (fun t => ferrersP ν 0 (AdditionTheorem.ferrersArg θ₁ θ₂ t)) m) := by
  have hc := AdditionTheorem.neg_one_lt_cos (by linarith) hs
  have key : DifferentiableOn ℂ (fun ν => ∫ t in (-π)..π, exp (-((m:ℂ) * t * I)) *
      ferrersP ν 0 (AdditionTheorem.ferrersArg θ₁ θ₂ t)) univ := by
    apply Complex.differentiableOn_intervalIntegral_of_locally_dominated isOpen_univ
    · intro ν _
      exact ((by fun_prop : Continuous fun t : ℝ => exp (-((m:ℂ) * t * I))).mul
        (AdditionTheorem.ferrersArg_contDiff ν h1 h2 hs).continuous).aestronglyMeasurable
    · refine ae_of_all _ fun t => ?_
      exact ((differentiable_const _).mul (AdditionTheorem.differentiable_ferrersP 0
        (by linarith [(AdditionTheorem.ferrersArg_mem h1 h2 hs t).1]))).differentiableOn
    · intro ν₀ _
      refine ⟨Metric.ball ν₀ 1, Metric.ball_mem_nhds _ one_pos,
        fun _ => Real.exp ((θ₁ + θ₂) * (|ν₀.im| + 1)) / Real.cos ((θ₁ + θ₂) / 2),
        integrableOn_const (by rw [uIoc_of_le (by linarith [Real.pi_pos])]; simp), ae_of_all _ ?_⟩
      intro t y hy
      rw [norm_mul, show -((m:ℂ) * t * I) = ((-(m * t) : ℝ) : ℂ) * I by push_cast; ring,
        norm_exp_ofReal_mul_I, one_mul]
      refine (AdditionTheorem.ferrersArg_norm_le y h1 h2 hs t).trans (div_le_div_of_nonneg_right
        (Real.exp_le_exp.mpr ?_) (Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩).le)
      have hd : ‖y - ν₀‖ < 1 := by simpa [dist_eq_norm] using hy
      have h3 := abs_im_le_norm (y - ν₀)
      rw [sub_im] at h3
      have h4 := abs_sub_abs_le_abs_sub y.im ν₀.im
      have : |y.im| ≤ |ν₀.im| + 1 := by linarith
      nlinarith
  rw [← differentiableOn_univ]
  exact (key.const_mul _).congr fun ν _ => rfl

/-- Ferrers functions of nonzero real order vanish at `x = 1` (where `(1+x)/(1-x)` is totalized
to `0`). -/
theorem AdditionTheorem.ferrersP_one {μ : ℂ} (hμ : μ ≠ 0) (ν : ℂ) : ferrersP ν μ 1 = 0 := by
  simp only [ferrersP]
  rw [show ((1:ℝ) + 1) / (1 - 1) = 0 by norm_num, ofReal_zero,
    zero_cpow (div_ne_zero hμ two_ne_zero), zero_mul]

/-- Bound for negative integer order on `[0, π)` from the fractional integral 14.12.2. -/
theorem AdditionTheorem.norm_ferrersP_neg_le {m : ℕ} (hm : 1 ≤ m) {θ : ℝ}
    (h0 : 0 ≤ θ) (hπ : θ < π) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ ν : ℂ, ‖ferrersP ν (-(m:ℂ)) (Real.cos θ)‖ ≤ K * Real.exp (θ * |ν.im|) := by
  have hm0 : (m:ℂ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  rcases eq_or_lt_of_le h0 with h | h
  · subst h
    refine ⟨0, le_rfl, fun ν => ?_⟩
    rw [Real.cos_zero, AdditionTheorem.ferrersP_one (neg_ne_zero.2 hm0)]; simp
  set x := Real.cos θ
  have hx : x ∈ Ioo (-1:ℝ) 1 := ⟨AdditionTheorem.neg_one_lt_cos h0 hπ, by
    rw [← Real.cos_zero]; exact Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl hπ.le h⟩
  have hcos : 0 < Real.cos (θ / 2) := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  refine ⟨‖(1 - (x:ℂ) ^ 2) ^ (-(m:ℂ) / 2) / Gamma m‖ * ((1 - x) ^ (m - 1) * (1 - x)) /
    Real.cos (θ / 2), by have : 0 ≤ 1 - x := by linarith [hx.2]
                         positivity, fun ν => ?_⟩
  have hm' : (0:ℝ) < (m:ℂ).re := by simp; exact_mod_cast hm
  rw [ferrersP_fractional_integral hm' ν hx, norm_mul]
  have hI := intervalIntegral.norm_integral_le_of_norm_le_const (a := x) (b := 1)
    (C := Real.exp (θ * |ν.im|) / Real.cos (θ / 2) * (1 - x) ^ (m - 1))
    (f := fun t : ℝ => ferrersP ν 0 t * ((t:ℂ) - x) ^ ((m:ℂ) - 1)) (fun t ht => by
      rw [uIoc_of_le hx.2.le] at ht
      rw [norm_mul, show (m:ℂ) - 1 = ((m - 1 : ℕ) : ℂ) by
        rw [Nat.cast_sub hm]; simp, cpow_natCast, norm_pow]
      gcongr
      · exact AdditionTheorem.norm_ferrersP_zero_le_of_mem ν h0 hπ ht.1.le ht.2
      · rw [show (t:ℂ) - x = ((t - x : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonneg (by linarith [ht.1])]
        linarith [ht.2])
  rw [abs_of_pos (by linarith [hx.2] : (0:ℝ) < 1 - x)] at hI
  calc ‖(1 - (x:ℂ) ^ 2) ^ (-(m:ℂ) / 2) / Gamma m‖ *
        ‖∫ t : ℝ in x..1, ferrersP ν 0 t * ((t:ℂ) - x) ^ ((m:ℂ) - 1)‖
      ≤ ‖(1 - (x:ℂ) ^ 2) ^ (-(m:ℂ) / 2) / Gamma m‖ *
        (Real.exp (θ * |ν.im|) / Real.cos (θ / 2) * (1 - x) ^ (m - 1) * (1 - x)) := by gcongr
    _ = _ := by field_simp

/-- `|(a)_k| ≤ k! ε^{-k} e^{ε (|a| + k)}`. -/
theorem AdditionTheorem.norm_poch_le_exp (a : ℂ) (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ‖poch a k‖ ≤ k ! / ε ^ k * Real.exp (ε * (‖a‖ + k)) := by
  have h1 : ‖poch a k‖ ≤ (‖a‖ + k) ^ k := by
    have key : ∀ j : ℕ, j ≤ k → ‖poch a j‖ ≤ (‖a‖ + k) ^ j := by
      intro j
      induction j with
      | zero => intro _; simp [poch_zero]
      | succ j ih =>
        intro hj
        rw [poch_succ, norm_mul, pow_succ]
        gcongr
        · exact ih (by omega)
        · calc ‖a + j‖ ≤ ‖a‖ + ‖(j:ℂ)‖ := norm_add_le _ _
            _ ≤ ‖a‖ + k := by
                gcongr
                rw [Complex.norm_natCast]; exact_mod_cast (by omega : j ≤ k)
    exact key k le_rfl
  have h2 := Real.pow_div_factorial_le_exp (x := ε * (‖a‖ + k)) (by positivity) k
  have hf : (0:ℝ) < k ! := by exact_mod_cast Nat.factorial_pos k
  rw [div_le_iff₀ hf, mul_pow] at h2
  calc ‖poch a k‖ ≤ (‖a‖ + k) ^ k := h1
    _ = (ε ^ k * (‖a‖ + k) ^ k) / ε ^ k := by field_simp
    _ ≤ (Real.exp (ε * (‖a‖ + k)) * k !) / ε ^ k := by gcongr
    _ = _ := by ring

/-- `𝖯^m_ν(x) = (-1)^m (ν-m+1)_{2m} 𝖯^{-m}_ν(x)` for every complex `ν` (14.9.3 without the
exceptional degrees, by continuation in `ν`). -/
theorem AdditionTheorem.ferrersP_nat_eq (ν : ℂ) (m : ℕ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ferrersP ν m x = (-1) ^ m * poch (ν - m + 1) (2 * m) * ferrersP ν (-(m:ℂ)) x := by
  set D : ℂ → ℂ := fun ν => ferrersP ν m x - (-1) ^ m * poch (ν - m + 1) (2 * m) *
    ferrersP ν (-(m:ℂ)) x
  have hD : Differentiable ℂ D := by
    refine (AdditionTheorem.differentiable_ferrersP _ hx.1).sub
        (((differentiable_const _).mul ?_).mul
      (AdditionTheorem.differentiable_ferrersP _ hx.1))
    show Differentiable ℂ (fun ν : ℂ => (ascPochhammer ℂ (2 * m)).eval (ν - m + 1))
    exact ((ascPochhammer ℂ (2 * m)).differentiable).comp (by fun_prop)
  have hgen : ∀ ν : ℂ, (m:ℝ) < ν.re → D ν = 0 := by
    intro ν hν
    have hre : 1 < (ν - m + 1).re := by simp; linarith
    have hh : ∀ n : ℕ, ν - m + 1 ≠ -n := fun n h => by
      have := congrArg Complex.re h; simp at this; linarith [(n.cast_nonneg : (0:ℝ) ≤ n)]
    have hGa : Gamma (ν - m + 1) ≠ 0 := Gamma_ne_zero_of_re_pos (by linarith)
    have hP := DLMF.Gamma.poch_mul_recip_Gamma_add_nat (ν - m + 1) (2 * m)
    rw [show ν - m + 1 + ((2 * m : ℕ) : ℂ) = ν + m + 1 by push_cast; ring] at hP
    have hGb : Gamma (ν + m + 1) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp; linarith)
    simp only [D]
    rw [ferrersP_negative_integer_order ν m hh hx]
    have hs : ((-1:ℂ)) ^ m * (-1) ^ m = 1 := by rw [← mul_pow]; norm_num
    have : poch (ν - m + 1) (2 * m) * Gamma (ν - m + 1) / Gamma (ν + m + 1) = 1 := by
      rw [mul_div_assoc, div_eq_mul_inv, mul_comm (Gamma _), ← mul_assoc, hP, inv_mul_cancel₀ hGa]
    rw [show (-1:ℂ) ^ m * poch (ν - m + 1) (2 * m) * ((-1) ^ m * Gamma (ν - m + 1) /
        Gamma (ν + m + 1) * ferrersP ν m x) = ((-1:ℂ) ^ m * (-1) ^ m) *
        (poch (ν - m + 1) (2 * m) * Gamma (ν - m + 1) / Gamma (ν + m + 1)) * ferrersP ν m x by
      ring, hs, this]
    ring
  have han : AnalyticOnNhd ℂ D univ := hD.differentiableOn.analyticOnNhd isOpen_univ
  have hev : D =ᶠ[𝓝 ((m:ℂ) + 1)] 0 := by
    have hopen : IsOpen {z : ℂ | (m:ℝ) < z.re} := isOpen_lt continuous_const continuous_re
    filter_upwards [hopen.mem_nhds (by simp : (m:ℝ) < ((m:ℂ) + 1).re)] with z hz
    exact hgen z hz
  have := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (mem_univ _) hev
    (mem_univ ν)
  exact sub_eq_zero.mp this

/-- The right-hand side coefficients of the Ferrers addition theorem satisfy a Carlson bound of
type `θ₁ + θ₂ + ε` on the imaginary axis. -/
theorem AdditionTheorem.ferrers_rhs_bound {θ₁ θ₂ : ℝ} (h1 : 0 ≤ θ₁) (h2 : 0 ≤ θ₂)
    (hs : θ₁ + θ₂ < π) (m : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, ∀ ν : ℂ, ‖(-1:ℂ) ^ m * ferrersP ν (-(m:ℂ)) (Real.cos θ₁) *
      ferrersP ν m (Real.cos θ₂)‖ ≤ C * Real.exp (ε * |ν.re| + (θ₁ + θ₂ + ε) * |ν.im|) := by
  have hπ1 : θ₁ < π := by linarith
  have hπ2 : θ₂ < π := by linarith
  have hc1 : 0 < Real.cos (θ₁ / 2) := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hc2 : 0 < Real.cos (θ₂ / 2) := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hn : ∀ ν : ℂ, ‖ν‖ ≤ |ν.re| + |ν.im| := norm_le_abs_re_add_abs_im
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · refine ⟨1 / (Real.cos (θ₁ / 2) * Real.cos (θ₂ / 2)), fun ν => ?_⟩
    rw [pow_zero, one_mul, Nat.cast_zero, neg_zero, norm_mul]
    have e1 := AdditionTheorem.norm_ferrersP_zero_le ν h1 hπ1
    have e2 := AdditionTheorem.norm_ferrersP_zero_le ν h2 hπ2
    calc ‖ferrersP ν 0 (Real.cos θ₁)‖ * ‖ferrersP ν 0 (Real.cos θ₂)‖
        ≤ (Real.exp (θ₁ * |ν.im|) / Real.cos (θ₁ / 2)) *
          (Real.exp (θ₂ * |ν.im|) / Real.cos (θ₂ / 2)) :=
          mul_le_mul e1 e2 (norm_nonneg _) (by positivity)
      _ = 1 / (Real.cos (θ₁ / 2) * Real.cos (θ₂ / 2)) * Real.exp (θ₁ * |ν.im| + θ₂ * |ν.im|) := by
          rw [Real.exp_add]; field_simp
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
          nlinarith [abs_nonneg ν.re, abs_nonneg ν.im]
  · obtain ⟨K₁, hK₁, hb₁⟩ := AdditionTheorem.norm_ferrersP_neg_le hm h1 hπ1
    obtain ⟨K₂, hK₂, hb₂⟩ := AdditionTheorem.norm_ferrersP_neg_le hm h2 hπ2
    rcases eq_or_lt_of_le h2 with h | h
    · subst h
      refine ⟨0, fun ν => ?_⟩
      rw [Real.cos_zero, AdditionTheorem.ferrersP_one (by exact_mod_cast hm.ne') ν]; simp
    have hx2 : Real.cos θ₂ ∈ Ioo (-1:ℝ) 1 := ⟨AdditionTheorem.neg_one_lt_cos h2 hπ2, by
      rw [← Real.cos_zero]; exact Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl hπ2.le h⟩
    set P : ℝ := (2 * m) ! / ε ^ (2 * m) * Real.exp (ε * (m + 1 + (2 * m : ℕ)))
    refine ⟨K₁ * K₂ * P, fun ν => ?_⟩
    rw [AdditionTheorem.ferrersP_nat_eq ν m hx2]
    have hp : ‖poch (ν - m + 1) (2 * m)‖ ≤ P * Real.exp (ε * ‖ν‖) := by
      refine (AdditionTheorem.norm_poch_le_exp _ _ hε).trans ?_
      have : ‖ν - m + 1‖ ≤ ‖ν‖ + (m + 1) := by
        calc ‖ν - m + 1‖ ≤ ‖ν‖ + ‖(m:ℂ)‖ + ‖(1:ℂ)‖ := by
              refine (norm_add_le _ _).trans ?_
              gcongr; exact norm_sub_le _ _
          _ = ‖ν‖ + (m + 1) := by rw [Complex.norm_natCast, norm_one]; ring
      simp only [P]
      rw [mul_assoc, ← Real.exp_add]
      gcongr
      nlinarith
    simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    calc ‖ferrersP ν (-(m:ℂ)) (Real.cos θ₁)‖ * (‖poch (ν - m + 1) (2 * m)‖ *
          ‖ferrersP ν (-(m:ℂ)) (Real.cos θ₂)‖)
        ≤ (K₁ * Real.exp (θ₁ * |ν.im|)) * ((P * Real.exp (ε * ‖ν‖)) *
          (K₂ * Real.exp (θ₂ * |ν.im|))) := by
          gcongr
          · exact hb₁ ν
          · exact hb₂ ν
      _ = K₁ * K₂ * P * Real.exp (θ₁ * |ν.im| + ε * ‖ν‖ + θ₂ * |ν.im|) := by
          rw [Real.exp_add, Real.exp_add]; ring
      _ ≤ _ := by
          have : 0 ≤ P := by positivity
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
          nlinarith [mul_le_mul_of_nonneg_left (hn ν) hε.le, abs_nonneg ν.re, abs_nonneg ν.im]

/-- The Fourier coefficients of `φ ↦ 𝖯_ν(cos θ₁ cos θ₂ + sin θ₁ sin θ₂ cos φ)` for every complex
degree, given the integer case (Carlson's theorem with type `θ₁ + θ₂ < π`). -/
theorem AdditionTheorem.ferrers_coeff_eq {θ₁ θ₂ : ℝ} (h1 : 0 ≤ θ₁) (h2 : 0 ≤ θ₂)
    (hs : θ₁ + θ₂ < π) (m : ℕ)
    (hnat : ∀ n : ℕ, AdditionTheorem.coeff
        (fun t => ferrersP n 0 (AdditionTheorem.ferrersArg θ₁ θ₂ t)) m =
      (-1:ℂ) ^ m * ferrersP n (-(m:ℂ)) (Real.cos θ₁) * ferrersP n m (Real.cos θ₂)) (ν : ℂ) :
    AdditionTheorem.coeff (fun t => ferrersP ν 0 (AdditionTheorem.ferrersArg θ₁ θ₂ t)) m =
      (-1:ℂ) ^ m * ferrersP ν (-(m:ℂ)) (Real.cos θ₁) * ferrersP ν m (Real.cos θ₂) := by
  set ε := (π - (θ₁ + θ₂)) / 2 with hεdef
  have hε : 0 < ε := by simp only [hεdef]; linarith
  obtain ⟨C, hC⟩ := AdditionTheorem.ferrers_rhs_bound h1 h2 hs m hε
  have hcos : 0 < Real.cos ((θ₁ + θ₂) / 2) := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hπ1 : -1 < Real.cos θ₁ := AdditionTheorem.neg_one_lt_cos h1 (by linarith)
  have hπ2 : -1 < Real.cos θ₂ := AdditionTheorem.neg_one_lt_cos h2 (by linarith)
  have key := AdditionTheorem.eq_zero_of_carlson
      (f := fun ν => AdditionTheorem.coeff (fun t => ferrersP ν 0
      (AdditionTheorem.ferrersArg θ₁ θ₂ t)) m - (-1:ℂ) ^ m * ferrersP ν (-(m:ℂ)) (Real.cos θ₁) *
      ferrersP ν m (Real.cos θ₂))
    ((AdditionTheorem.ferrers_coeff_differentiable h1 h2 hs m).sub
      (((differentiable_const _).mul (AdditionTheorem.differentiable_ferrersP _ hπ1)).mul
        (AdditionTheorem.differentiable_ferrersP _ hπ2)))
    (C := 1 / Real.cos ((θ₁ + θ₂) / 2) + |C|) (A := ε) (B := θ₁ + θ₂ + ε) hε.le
    (by linarith) (by simp only [hεdef]; linarith)
    (fun w _ => by
      refine (norm_sub_le _ _).trans ?_
      have e1 := AdditionTheorem.ferrers_coeff_bound w h1 h2 hs m
      have hE1 : Real.exp ((θ₁ + θ₂) * |w.im|) ≤ Real.exp (ε * |w.re| + (θ₁ + θ₂ + ε) * |w.im|) :=
        Real.exp_le_exp.mpr (by nlinarith [abs_nonneg w.re, abs_nonneg w.im])
      have e1' : ‖AdditionTheorem.coeff
          (fun t => ferrersP w 0 (AdditionTheorem.ferrersArg θ₁ θ₂ t)) m‖ ≤
          1 / Real.cos ((θ₁ + θ₂) / 2) * Real.exp (ε * |w.re| + (θ₁ + θ₂ + ε) * |w.im|) := by
        refine e1.trans ?_
        rw [div_eq_mul_inv, one_div, mul_comm]
        exact mul_le_mul_of_nonneg_left hE1 (inv_pos.2 hcos).le
      have hCa : C * Real.exp (ε * |w.re| + (θ₁ + θ₂ + ε) * |w.im|) ≤
          |C| * Real.exp (ε * |w.re| + (θ₁ + θ₂ + ε) * |w.im|) :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le
      have e2 := hC w
      nlinarith)
    (fun n => by rw [hnat n, sub_self]) ν
  exact sub_eq_zero.mp key

/-- **Addition theorem for Ferrers functions** (DLMF 14.18.1), given its integer case. -/
theorem AdditionTheorem.ferrersP_addition_of_nat {θ₁ θ₂ : ℝ} (h1 : 0 ≤ θ₁) (h2 : 0 ≤ θ₂)
    (hs : θ₁ + θ₂ < π)
    (hnat : ∀ m n : ℕ, AdditionTheorem.coeff
        (fun t => ferrersP n 0 (AdditionTheorem.ferrersArg θ₁ θ₂ t)) m =
      (-1:ℂ) ^ m * ferrersP n (-(m:ℂ)) (Real.cos θ₁) * ferrersP n m (Real.cos θ₂))
    (ν : ℂ) (phi : ℝ) :
    HasSum (fun j : ℕ => let m := j + 1; 2 * (-1) ^ m * ferrersP ν (-m) (Real.cos θ₁) *
      ferrersP ν m (Real.cos θ₂) * Real.cos (m * phi))
      (ferrersP ν 0 (Real.cos θ₁ * Real.cos θ₂ + Real.sin θ₁ * Real.sin θ₂ * Real.cos phi) -
        ferrersP ν 0 (Real.cos θ₁) * ferrersP ν 0 (Real.cos θ₂)) := by
  have hper : Function.Periodic
      (fun t : ℝ => ferrersP ν 0 (AdditionTheorem.ferrersArg θ₁ θ₂ t)) (2 * π) :=
    fun t => by simp only [AdditionTheorem.ferrersArg, Real.cos_add_two_pi]
  have hev : ∀ t, (fun t : ℝ => ferrersP ν 0 (AdditionTheorem.ferrersArg θ₁ θ₂ t)) (-t) =
      (fun t : ℝ => ferrersP ν 0 (AdditionTheorem.ferrersArg θ₁ θ₂ t)) t :=
    fun t => by simp only [AdditionTheorem.ferrersArg, Real.cos_neg]
  have hF := AdditionTheorem.hasSum_cos
      (AdditionTheorem.ferrersArg_contDiff ν h1 h2 hs) hper hev phi
  have h0 := AdditionTheorem.ferrers_coeff_eq h1 h2 hs 0 (hnat 0) ν
  simp only [pow_zero, one_mul, Nat.cast_zero, neg_zero] at h0
  convert hF using 1
  · funext j
    rw [AdditionTheorem.ferrers_coeff_eq h1 h2 hs (j + 1) (hnat (j + 1)) ν]
    push_cast
    ring
  · rw [h0]; rfl

/-! ### The integer case of 14.18.1 -/

/-- Nonnegative integer order Ferrers P agrees with the polynomial form on `(-1, 1]`. -/
theorem AdditionTheorem.ferrersP_nat_eq_ferrersPNat (n k : ℕ) {x : ℝ} (hx : x ∈ Ioc (-1:ℝ) 1) :
    ferrersP n k x = ferrersPNat n k x := by
  rcases eq_or_lt_of_le hx.2 with rfl | hlt
  · rw [ferrersPNat_one]
    rcases k with _ | k
    · simp only [ferrersP, Nat.cast_zero, zero_div, cpow_zero, one_mul, sub_zero, sub_self,
        ite_true]
      have hc : ∀ j : ℕ, (1:ℂ) ≠ -(j:ℂ) := by
        intro j h; have := congrArg Complex.re h; simp at this;
            linarith [(j.cast_nonneg : (0:ℝ) ≤ j)]
      rw [show ((1:ℂ) - ((1:ℝ):ℂ))/2 = 0 by simp, regularizedGaussHG_zero_of_regular hc]
      simp
    · simp [ferrersP]
      left; exact_mod_cast Nat.succ_ne_zero k
  · exact (ferrersPNat_eq n k ⟨hx.1, hlt⟩).symm

/-- Negative integer order Ferrers P in polynomial form on `(-1, 1]`. -/
theorem AdditionTheorem.ferrersP_neg_nat_eq_ferrersPNat (n k : ℕ) (hk : k ≤ n) {x : ℝ}
    (hx : x ∈ Ioc (-1:ℝ) 1) :
    ferrersP n (-(k:ℂ)) x = (-1)^k * ((n-k).factorial / (n+k).factorial : ℂ) *
        ferrersPNat n k x := by
  rcases eq_or_lt_of_le hx.2 with rfl | hlt
  · rw [ferrersPNat_one]
    rcases k with _ | k
    · rw [Nat.cast_zero, neg_zero, ← Nat.cast_zero,
          AdditionTheorem.ferrersP_nat_eq_ferrersPNat n 0 hx,
        ferrersPNat_one]
      simp [Nat.factorial_ne_zero]
    · simp [ferrersP]
      left; intro h; have := congrArg Complex.re h; simp at this;
          linarith [(k.cast_nonneg : (0:ℝ) ≤ k)]
  · have hG : ∀ j : ℕ, (n:ℂ) - k + 1 ≠ -j := by
      intro j h
      have : ((n - k + 1 + j : ℕ) : ℂ) = 0 := by push_cast [Nat.cast_sub hk]; linear_combination h
      exact absurd (Nat.cast_eq_zero.1 this) (by omega)
    rw [ferrersP_negative_integer_order (n:ℂ) k hG ⟨hx.1, hlt⟩, ferrersPNat_eq n k ⟨hx.1, hlt⟩,
      show (n:ℂ) - k + 1 = ((n - k : ℕ) : ℂ) + 1 by push_cast [Nat.cast_sub hk]; ring,
      show (n:ℂ) + k + 1 = ((n + k : ℕ) : ℂ) + 1 by push_cast; ring,
      Gamma_nat_eq_factorial, Gamma_nat_eq_factorial]
    ring

open DLMF.OrthogonalPolynomials.LegendreAddition in
/-- The Ferrers addition theorem at integer degree, coefficientwise: the Fourier coefficients of
`φ ↦ P_n(cos θ₁ cos θ₂ + sin θ₁ sin θ₂ cos φ)` are `(-1)^m 𝖯^{-m}_n(cos θ₁) 𝖯^m_n(cos θ₂)`. -/
theorem AdditionTheorem.ferrers_nat {θ₁ θ₂ : ℝ} (h1 : 0 ≤ θ₁) (h2 : 0 ≤ θ₂)
    (hs : θ₁ + θ₂ < π) (m n : ℕ) :
    AdditionTheorem.coeff (fun t => ferrersP n 0 (AdditionTheorem.ferrersArg θ₁ θ₂ t)) m =
      (-1:ℂ) ^ m * ferrersP n (-(m:ℂ)) (Real.cos θ₁) * ferrersP n m (Real.cos θ₂) := by
  have hθ1 : θ₁ < π := by linarith
  have hθ2 : θ₂ < π := by linarith
  have hcos : ∀ θ, 0 ≤ θ → θ < π → Real.cos θ ∈ Ioc (-1:ℝ) 1 := fun θ h0 hπ =>
    ⟨by rw [← Real.cos_pi]; exact Real.cos_lt_cos_of_nonneg_of_le_pi h0 le_rfl hπ,
          Real.cos_le_one θ⟩
  have hx1 := hcos θ₁ h1 hθ1
  have hx2 := hcos θ₂ h2 hθ2
  have hsq : ∀ θ : ℝ, (Real.sin θ : ℂ) ^ 2 = 1 - (Real.cos θ : ℂ) ^ 2 := fun θ => by
    rw [← ofReal_pow, ← ofReal_pow, Real.sin_sq]; push_cast; ring
  have hfun : (fun t : ℝ => ferrersP (n:ℂ) 0 (AdditionTheorem.ferrersArg θ₁ θ₂ t)) =
      fun t : ℝ => kernel n (Real.cos θ₁) (Real.cos θ₂) (Real.sin θ₁) (Real.sin θ₂) t := by
    funext t
    have hY := AdditionTheorem.ferrersArg_mem h1 h2 hs t
    have hY1 : -1 < AdditionTheorem.ferrersArg θ₁ θ₂ t :=
        lt_of_lt_of_le (AdditionTheorem.neg_one_lt_cos (by linarith) hs) hY.1
    rw [ferrersP_zero _ hY1, legendreP_nat n (Or.inl (by simp; linarith)),
      ← legendre_eq_kernel n _ _ _ _ t (hsq θ₁) (hsq θ₂), AdditionTheorem.ferrersArg]
    push_cast; ring_nf
  have hsin : ∀ θ, 0 ≤ θ → θ < π → Real.sqrt (1 - Real.cos θ^2) = Real.sin θ := fun θ h0 hπ =>
    (Real.sin_eq_sqrt_one_sub_cos_sq h0 hπ.le).symm
  have hF : ∀ k : ℕ, ∀ θ, 0 ≤ θ → θ < π → ferrersPNat n k (Real.cos θ) =
      (-1)^k * (Real.sin θ:ℂ)^k * jet n k (Real.cos θ) := by
    intro k θ h0 hπ
    rw [ferrersPNat, hsin θ h0 hπ]; rfl
  rw [hfun, AdditionTheorem.coeff_kernel]
  rcases le_or_gt m n with hmn | hmn
  · rw [AdditionTheorem.ferrersP_neg_nat_eq_ferrersPNat n m hmn hx1,
        AdditionTheorem.ferrersP_nat_eq_ferrersPNat n m hx2,
      hF m θ₁ h1 hθ1, hF m θ₂ h2 hθ2]
    have h4 : ((-1:ℂ)) ^ m * (-1) ^ m * ((-1) ^ m * (-1) ^ m) = 1 := by
      rw [← mul_pow, ← mul_pow]; norm_num
    simp only [OrthogonalPolynomials.LegendreAddition.coeff, weight]
    linear_combination (-(((n - m).factorial / (n + m).factorial : ℂ) *
        (Real.sin θ₁ * Real.sin θ₂ : ℂ) ^ m *
      jet n m (Real.cos θ₁) * jet n m (Real.cos θ₂))) * h4 + 0 *
          (mul_pow (Real.sin θ₁ : ℂ) (Real.sin θ₂) m)
  · rw [coeff_eq_zero hmn, AdditionTheorem.ferrersP_nat_eq_ferrersPNat n m hx2, hF m θ₂ h2 hθ2,
        jet_eq_zero hmn]
    simp

end DLMF.Legendre
