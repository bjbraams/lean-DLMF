/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Legendre.FourierEstimates

/-!
# Legendre Fourier series, generating functions and continued fractions

This file treats the Fourier series of Ferrers functions (DLMF §14.13), the explicit forms of
Legendre functions of the second kind of integer degree (DLMF 14.7.2–14.7.7), the generating
functions (DLMF 14.7.19–14.7.22) and the continued fractions (DLMF §14.14). The Fourier series
converge conditionally for `Re μ < 1/2`, by Dirichlet's test and Abel's theorem, and absolutely
only for `Re μ < 0` (`DLMF.Legendre.FourierEstimates`). Helper names live in the namespaces
`FerrersFourier` and `ContinuedFraction`.

## Main definitions

* `FerrersFourier.coeff`: the Fourier coefficient `Γ(ν+μ+k+1)/Γ(ν+k+3/2) · (μ+1/2)_k/k!` of DLMF
  14.13.1 and 14.13.2.
* `legendrePCFNum`, `legendrePCFDen`: the partial numerators and denominators of the continued
  fraction for `P^μ_ν(x)` (DLMF 14.14.2).
* `legendreQCFNum`, `legendreQCFDen`: the partial numerators and denominators of the continued
  fraction for `Q^μ_ν(x)` (DLMF 14.14.4).

## Main results

* `ferrersP_fourier_series`, `ferrersQ_fourier_series`: DLMF 14.13.1, 14.13.2.
* `ferrersP_nat_fourier`, `ferrersQ_nat_fourier`: DLMF 14.13.3, 14.13.4.
* `ferrersP_fourier_absolute`, `ferrersQ_fourier_absolute`, `ferrersP_fourier_not_absolute`,
  `ferrersQ_fourier_not_absolute`: absolute convergence for `Re μ < 0` and its failure for
  `Re μ ≥ 0` (when `θ ≠ π/2`).
* `ferrersPQ_fourier_hypergeometric`: the unnumbered hypergeometric Fourier representation in
  DLMF §14.13.
* `ferrersQ_nat_logarithm`, `legendreQPoly_explicit`, `legendreQPoly_convolution`,
  `legendreQPoly_initial`: DLMF 14.7.2–14.7.5.
* `olverQ_nat_normalization`, `associatedQ_nat_logarithm`: DLMF 14.7.6, 14.7.7.
* `ferrersP_generating`, `associatedP_generating_complex`: DLMF 14.7.19.
* `ferrersQ_generating`, `associatedP_exterior_generating`, `associatedQ_generating`:
  DLMF 14.7.20–14.7.22.
* `associatedP_continued_fraction`, `associatedQ_continued_fraction`: DLMF 14.14.1, 14.14.3.

## Implementation notes

DLMF 14.14.1 contains an error: the continued fraction converges to
`½(x²-1)^{1/2} (ν+μ)(ν-μ+1) P^{-μ}_ν(x)/P^{1-μ}_ν(x)`, the ratio for the minimal solution of the
order recurrence, and `associatedP_continued_fraction` proves this corrected statement. A
vanishing partial numerator terminates the fraction at the same value, so no hypothesis on the
partial numerators is needed (stronger than DLMF). In
`associatedP_exterior_generating` the exterior square root is normalized at infinity.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF
open scoped Real Topology Nat
open DLMF.Core

namespace DLMF.Legendre

/-- The Fourier coefficient `Γ(ν+μ+k+1)/Γ(ν+k+3/2) · (μ+1/2)_k/k!` of DLMF 14.13.1–14.13.2. -/
noncomputable def FerrersFourier.coeff (ν μ : ℂ) (k : ℕ) : ℂ :=
  Gamma (ν+μ+k+1)/Gamma (ν+k+3/2)*poch (μ+1/2) k/(k.factorial:ℂ)

/-- `‖FerrersFourier.coeff ν μ k‖ ≤ C k^{2 Re μ - 1}` eventually. -/
theorem FerrersFourier.coeff_bound (ν μ : ℂ) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ᶠ k : ℕ in atTop, ‖FerrersFourier.coeff ν μ k‖ ≤ C * (k:ℝ)^(2*μ.re-1) := by
  obtain ⟨C, hC, hP⟩ := FerrersFourier.poch_div_factorial_le (μ+1/2)
  refine ⟨2*C, by positivity, ?_⟩
  filter_upwards [FerrersFourier.gamma_ratio_le (ν+μ+1) (ν+3/2), hP, eventually_gt_atTop 0]
    with k hA hk hk0
  have e : FerrersFourier.coeff ν μ k =
      Gamma (k+(ν+μ+1))/Gamma (k+(ν+3/2)) * (poch (μ+1/2) k/(k.factorial:ℂ)) := by
    rw [FerrersFourier.coeff, show ν+μ+k+1 = k+(ν+μ+1) by ring, show ν+k+3/2 =
                                                            k+(ν+3/2) by ring]; ring
  have hre : (ν+μ+1-(ν+3/2)).re = μ.re - 1/2 := by simp; ring
  have hre2 : (μ+1/2).re - 1 = μ.re - 1/2 := by simp; ring
  rw [hre] at hA
  rw [hre2] at hk
  have hkp : (0:ℝ) < k := by exact_mod_cast hk0
  have hpow : (k:ℝ)^(2*μ.re-1) = (k:ℝ)^(μ.re-1/2) * (k:ℝ)^(μ.re-1/2) := by
    rw [← Real.rpow_add hkp]; ring_nf
  rw [e, norm_mul, hpow]
  calc ‖Gamma (k+(ν+μ+1))/Gamma (k+(ν+3/2))‖ * ‖poch (μ+1/2) k/(k.factorial:ℂ)‖
      ≤ (2 * (k:ℝ)^(μ.re-1/2)) * (C * (k:ℝ)^(μ.re-1/2)) := by gcongr
    _ = _ := by ring

/-- The coefficients tend to zero when `Re μ < 1/2`. -/
theorem FerrersFourier.coeff_tendsto_zero (ν : ℂ) {μ : ℂ} (hμ : μ.re < 1/2) :
    Tendsto (FerrersFourier.coeff ν μ) atTop (𝓝 0) := by
  obtain ⟨C, hC, hb⟩ := FerrersFourier.coeff_bound ν μ
  have h1 : Tendsto (fun k : ℕ => C * (k:ℝ)^(2*μ.re-1)) atTop (𝓝 0) := by
    have := (tendsto_rpow_neg_atTop (show 0 < 1 - 2*μ.re by linarith)).comp
      tendsto_natCast_atTop_atTop
    simpa [show -(1 - 2*μ.re) = 2*μ.re-1 by ring] using this.const_mul C
  exact squeeze_zero_norm' hb h1

/-- One-step ratio of the coefficients, eventually. -/
theorem FerrersFourier.coeff_succ (ν μ : ℂ) : ∀ᶠ k : ℕ in atTop,
    FerrersFourier.coeff ν μ (k+1) = FerrersFourier.coeff ν μ k *
      ((ν+μ+k+1)*(μ+1/2+k)/((ν+k+3/2)*(k+1))) := by
  filter_upwards [eventually_gt_atTop ⌈‖ν‖ + ‖μ‖ + 2⌉₊] with k hk
  have hk' : ‖ν‖ + ‖μ‖ + 2 < k := Nat.lt_of_ceil_lt hk
  have hne : ∀ z : ℂ, ‖z‖ ≤ ‖ν‖ + ‖μ‖ + 2 → z + k ≠ 0 := by
    intro z hz h
    have : (k:ℂ) = -z := by linear_combination h
    have := congrArg norm this
    rw [norm_neg, Complex.norm_natCast] at this
    linarith
  have h1 : ν+μ+k+1 ≠ 0 := by
    have := hne (ν+μ+1) (by
      calc ‖ν+μ+1‖ ≤ ‖ν+μ‖ + ‖(1:ℂ)‖ := norm_add_le _ _
        _ ≤ ‖ν‖ + ‖μ‖ + 1 := by gcongr; exacts [norm_add_le _ _, by simp]
        _ ≤ _ := by linarith)
    intro h; apply this; linear_combination h
  have h2 : ν+k+3/2 ≠ 0 := by
    have := hne (ν+3/2) (by
      calc ‖ν+3/2‖ ≤ ‖ν‖ + ‖(3/2:ℂ)‖ := norm_add_le _ _
        _ ≤ ‖ν‖ + ‖μ‖ + 2 := by
          have : ‖(3/2:ℂ)‖ = 3/2 := by norm_num [Complex.norm_div]
          rw [this]; linarith [norm_nonneg μ])
    intro h; apply this; linear_combination h
  rw [FerrersFourier.coeff, FerrersFourier.coeff]
  push_cast
  rw [show ν+μ+(k+1)+1 = (ν+μ+k+1)+1 by ring, show ν+(k+1)+3/2 = (ν+k+3/2)+1 by ring,
    Complex.Gamma_add_one _ h1, Complex.Gamma_add_one _ h2, poch_succ, Nat.factorial_succ]
  push_cast
  simp only [div_eq_mul_inv, mul_inv]
  ring

/-- The coefficients have bounded variation when `Re μ < 1/2`:
`‖c_{k+1} - c_k‖ = O(k^{2 Re μ - 2})`. -/
theorem FerrersFourier.coeff_var_summable (ν : ℂ) {μ : ℂ} (hμ : μ.re < 1/2) :
    Summable (fun k : ℕ => ‖FerrersFourier.coeff ν μ (k+1) - FerrersFourier.coeff ν μ k‖) := by
  obtain ⟨C, hC, hb⟩ := FerrersFourier.coeff_bound ν μ
  set K₀ : ℂ := (ν+μ+1)*(μ+1/2) - (ν+3/2) with hK₀
  set A : ℝ := ‖2*μ-1‖ + ‖K₀‖ with hA
  have hA0 : 0 ≤ A := by positivity
  refine Summable.of_norm_bounded_eventually_nat
    (g := fun k : ℕ => 2*A*C * (k:ℝ)^(2*μ.re-2))
    ((Real.summable_nat_rpow.mpr (by linarith)).mul_left _) ?_
  filter_upwards [hb, FerrersFourier.coeff_succ ν μ, eventually_gt_atTop ⌈2*‖ν+3/2‖ + 1⌉₊]
    with k hbk hsk hk
  have hk' : 2*‖ν+3/2‖ + 1 < k := Nat.lt_of_ceil_lt hk
  have hkp : (0:ℝ) < k := by linarith [norm_nonneg (ν+3/2)]
  have hk1 : (1:ℝ) ≤ k := by linarith [norm_nonneg (ν+3/2)]
  have hc1 : ‖ν+3/2‖ ≤ k/2 := by linarith
  have hD1 : (k:ℝ)/2 ≤ ‖ν+k+3/2‖ := by
    have := norm_sub_norm_le (k:ℂ) (-(ν+3/2))
    rw [Complex.norm_natCast, norm_neg, show (k:ℂ) - -(ν+3/2) = ν+k+3/2 by ring] at this
    linarith
  have hD2 : (k:ℝ) ≤ ‖(k:ℂ)+1‖ := by
    rw [show (k:ℂ)+1 = ((k+1:ℝ):ℂ) by push_cast; ring, norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith)]; linarith
  have hD0 : ν+k+3/2 ≠ 0 := fun h => by rw [h, norm_zero] at hD1; linarith
  have hD0' : (k:ℂ)+1 ≠ 0 := fun h => by rw [h, norm_zero] at hD2; linarith
  have hρ : (ν+μ+k+1)*(μ+1/2+k)/((ν+k+3/2)*(k+1)) - 1 =
      ((2*μ-1)*k + K₀)/((ν+k+3/2)*(k+1)) := by
    rw [div_sub_one (mul_ne_zero hD0 hD0'), hK₀]; congr 1; ring
  have hnum : ‖(2*μ-1)*k + K₀‖ ≤ A * k := by
    calc ‖(2*μ-1)*k + K₀‖ ≤ ‖2*μ-1‖ * k + ‖K₀‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, Complex.norm_natCast]
      _ ≤ ‖2*μ-1‖ * k + ‖K₀‖ * k := by gcongr; exact le_mul_of_one_le_right (norm_nonneg _) hk1
      _ = A * k := by ring
  have hratio : ‖(ν+μ+k+1)*(μ+1/2+k)/((ν+k+3/2)*(k+1)) - 1‖ ≤ 2*A/k := by
    rw [hρ, norm_div, norm_mul]
    rw [div_le_div_iff₀ (by positivity) hkp]
    calc ‖(2*μ-1)*k + K₀‖ * k ≤ A*k*k := by gcongr
      _ = 2*A*((k/2)*k) := by ring
      _ ≤ 2*A*(‖ν+k+3/2‖ * ‖(k:ℂ)+1‖) := by gcongr
  rw [norm_norm, hsk, show FerrersFourier.coeff ν μ k * ((ν+μ+k+1)*(μ+1/2+k)/((ν+k+3/2)*(k+1))) -
    FerrersFourier.coeff ν μ k = FerrersFourier.coeff ν μ k *
        ((ν+μ+k+1)*(μ+1/2+k)/((ν+k+3/2)*(k+1)) - 1) by ring,
    norm_mul]
  calc ‖FerrersFourier.coeff ν μ k‖ * ‖(ν+μ+k+1)*(μ+1/2+k)/((ν+k+3/2)*(k+1)) - 1‖
      ≤ (C * (k:ℝ)^(2*μ.re-1)) * (2*A/k) := by gcongr
    _ = 2*A*C * ((k:ℝ)^(2*μ.re-1) / k) := by ring
    _ = 2*A*C * (k:ℝ)^(2*μ.re-2) := by
        rw [show 2*μ.re-2 = (2*μ.re-1) - 1 by ring, Real.rpow_sub_one hkp.ne' (2*μ.re-1)]

/-- On the unit circle (`w ≠ 1`) and for `Re μ < 1/2`, the series `∑ c_k w^k` converges to
`Γ(ν+μ+1) 𝐅(ν+μ+1, μ+1/2; ν+3/2; w)` (Dirichlet's test and Abel's limit theorem). -/
theorem FerrersFourier.series_tendsto {ν μ : ℂ} (hr : LegendreQRegular ν μ)
    (hμ : μ.re < 1/2) {w : ℂ}
    (hw : ‖w‖ = 1) (hw1 : w ≠ 1) (hcut : w ∈ cutPlane) :
    Tendsto (fun N => ∑ k ∈ Finset.range N, FerrersFourier.coeff ν μ k * w^k) atTop
      (𝓝 (Gamma (ν+μ+1) * regularizedGaussHG (ν+μ+1) (μ+1/2) (ν+3/2) w)) := by
  have hw1' : w - 1 ≠ 0 := sub_ne_zero.mpr hw1
  have hB : ∀ n, ‖∑ i ∈ Finset.range n, w^i‖ ≤ 2/‖w-1‖ := by
    intro n
    rw [geom_sum_eq hw1 n, norm_div]
    gcongr
    refine (norm_sub_le _ _).trans ?_
    rw [norm_pow, hw]; norm_num
  obtain ⟨l, hl⟩ := FerrersFourier.dirichlet hB (FerrersFourier.coeff_tendsto_zero ν hμ)
    (FerrersFourier.coeff_var_summable ν hμ)
  have ha : ∀ k : ℕ, ν+μ+1 ≠ -(k:ℂ) := fun k h => hr k (by linear_combination h)
  -- Abel's theorem
  have hA := Complex.tendsto_tsum_powerSeries_nhdsWithin_lt
      (f := fun k => FerrersFourier.coeff ν μ k * w^k) hl
  rw [tendsto_map'_iff] at hA
  -- the Abel means are the hypergeometric function inside the disk
  have hmean : ∀ x : ℝ, 0 ≤ x → x < 1 →
      ((fun z : ℂ => ∑' n, FerrersFourier.coeff ν μ n * w^n * z^n) ∘ ofReal) x =
        Gamma (ν+μ+1) * regularizedGaussHG (ν+μ+1) (μ+1/2) (ν+3/2) (w*x) := by
    intro x hx0 hx1
    have hn : ‖w*x‖ < 1 := by
      rw [norm_mul, hw, one_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg hx0]; exact hx1
    rw [regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hn, regularizedGaussHGFun_eq_tsum,
      ← tsum_mul_left]
    simp only [Function.comp_apply]
    congr 1; funext n
    have hG := Gamma_add_nat_div_Gamma_eq (n := n) (ν+μ+1) ha
    have hG0 : Gamma (ν+μ+1) ≠ 0 := Gamma_ne_zero ha
    have hG' : Gamma (ν+μ+n+1) = Gamma (ν+μ+1) * (ascPochhammer ℂ n).eval (ν+μ+1) := by
      rw [← hG, show ν+μ+n+1 = ν+μ+1+n by ring]; field_simp
    rw [FerrersFourier.coeff, hG', show ν+n+3/2 = ν+3/2+n by ring, mul_pow]
    simp only [poch, div_eq_mul_inv]
    ring
  have hlim2 : Tendsto
      (fun x : ℝ => Gamma (ν+μ+1) * regularizedGaussHG (ν+μ+1) (μ+1/2) (ν+3/2) (w*x))
      (𝓝[<] (1:ℝ)) (𝓝 (Gamma (ν+μ+1) * regularizedGaussHG (ν+μ+1) (μ+1/2) (ν+3/2) w)) := by
    have hc : Tendsto (fun x : ℝ => w*(x:ℂ)) (𝓝[<] (1:ℝ)) (𝓝 w) := by
      have : Continuous (fun x : ℝ => w*(x:ℂ)) := by fun_prop
      simpa using (this.tendsto 1).mono_left nhdsWithin_le_nhds
    exact ((analyticAt_regularizedGaussHG _ _ _ hcut).continuousAt.tendsto.comp hc).const_mul _
  have hev : ∀ᶠ x : ℝ in 𝓝[<] (1:ℝ),
      ((fun z : ℂ => ∑' n, FerrersFourier.coeff ν μ n * w^n * z^n) ∘ ofReal) x =
        Gamma (ν+μ+1) * regularizedGaussHG (ν+μ+1) (μ+1/2) (ν+3/2) (w*x) := by
    filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (Ioi_mem_nhds (show (0:ℝ) < 1 by norm_num))]
      with x hx1 hx0
    exact hmean x (le_of_lt hx0) hx1
  have := tendsto_nhds_unique hA (hlim2.congr' (hev.mono fun x hx => hx.symm))
  rw [← this]; exact hl

/-- `e^{2isθ}` lies in the cut plane for `0 < θ < π`, `s = ±1`. -/
theorem FerrersFourier.exp_mem_cutPlane {s : ℝ} (hs : s = 1 ∨ s = -1) {θ : ℝ}
    (h0 : 0 < θ) (hπ : θ < π) :
    exp ((s:ℂ)*2*I*θ) ∈ cutPlane := by
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi h0 hπ
  show 1 - _ ∈ slitPlane
  rw [mem_slitPlane_iff]; left
  rw [show (s:ℂ)*2*I*θ = ((2*s*θ:ℝ):ℂ)*I by push_cast; ring, exp_mul_I, ← ofReal_cos, ← ofReal_sin]
  simp only [sub_re, one_re, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
    sub_zero]
  have hc : Real.cos (2*s*θ) = 1 - 2*Real.sin θ^2 := by
    rcases hs with rfl | rfl
    · rw [show 2*(1:ℝ)*θ = 2*θ by ring, Real.cos_two_mul, Real.cos_sq']; ring
    · rw [show 2*(-1:ℝ)*θ = -(2*θ) by ring, Real.cos_neg, Real.cos_two_mul, Real.cos_sq']; ring
  rw [hc]; simp; positivity

/-- `‖e^{2isθ}‖ = 1`. -/
theorem FerrersFourier.norm_exp {s : ℝ} (θ : ℝ) : ‖exp ((s:ℂ)*2*I*θ)‖ = 1 := by
  rw [show (s:ℂ)*2*I*θ = ((2*s*θ:ℝ):ℂ)*I by push_cast; ring, norm_exp_ofReal_mul_I]

/-- `sin((ν+μ+2k+1)θ)` and `cos((ν+μ+2k+1)θ)` through `e^{±i(ν+μ+1)θ} e^{±2ikθ}`. -/
theorem FerrersFourier.exp_split (ν μ : ℂ) (θ : ℝ) (k : ℕ) (s : ℝ) :
    exp ((s:ℂ)*(ν+μ+1)*I*θ) * exp ((s:ℂ)*2*I*θ)^k = exp ((s:ℂ)*((ν+μ+2*k+1)*θ)*I) := by
  rw [← exp_nat_mul, ← exp_add]; congr 1; ring

/-- Partial sums of the Fourier series in exponential form. -/
theorem FerrersFourier.tendsto_pair {ν μ : ℂ} (hr : LegendreQRegular ν μ) (hμ : μ.re < 1/2) {θ : ℝ}
    (h0 : 0 < θ) (hπ : θ < π) {s : ℝ} (hs : s = 1 ∨ s = -1) :
    Tendsto (fun N => ∑ k ∈ Finset.range N, FerrersFourier.coeff ν μ k *
        exp ((s:ℂ)*((ν+μ+2*k+1)*θ)*I))
      atTop (𝓝 (exp ((s:ℂ)*(ν+μ+1)*I*θ) * (Gamma (ν+μ+1) *
        regularizedGaussHG (ν+μ+1) (μ+1/2) (ν+3/2) (exp ((s:ℂ)*2*I*θ))))) := by
  have hcut := FerrersFourier.exp_mem_cutPlane hs h0 hπ
  have h := (FerrersFourier.series_tendsto hr hμ (FerrersFourier.norm_exp θ)
    (fun h1 => slitPlane_ne_zero hcut (by rw [h1, sub_self])) hcut).const_mul
    (exp ((s:ℂ)*(ν+μ+1)*I*θ))
  refine h.congr fun N => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← FerrersFourier.exp_split ν μ θ k s]; ring

/-- `2/√π · Γ(n+k+1)/Γ(n+k+3/2) = 2^{2n+2}(n!)²/(π(2n+1)!) · (n+1)_k/(n+3/2)_k`. -/
theorem FerrersFourier.nat_coeff (n k : ℕ) :
    (2:ℂ)/Real.sqrt π * (Gamma ((n:ℂ)+k+1)/Gamma ((n:ℂ)+k+3/2)) =
      2^(2*n+2)*(n.factorial:ℂ)^2/(π*((2*n+1).factorial:ℂ))*(poch (n+1) k/poch (n+3/2) k) := by
  have ha : ∀ m : ℕ, ((n:ℂ)+1) ≠ -(m:ℂ) := fun m h => by
    have := congrArg re h; simp at this; linarith [(m.cast_nonneg : (0:ℝ) ≤ m)]
  have hb : ∀ m : ℕ, ((n:ℂ)+3/2) ≠ -(m:ℂ) := fun m h => by
    have := congrArg re h; simp at this; norm_num at this; linarith [(m.cast_nonneg : (0:ℝ) ≤ m)]
  have h1 := Gamma_add_nat_div_Gamma_eq (n := k) ((n:ℂ)+1) ha
  have h2 := Gamma_add_nat_div_Gamma_eq (n := k) ((n:ℂ)+3/2) hb
  have hG1 : Gamma ((n:ℂ)+1) = n.factorial := by
    rw [show ((n:ℂ)+1) = ((n:ℕ):ℂ)+1 by rfl, Gamma_nat_eq_factorial]
  have hG2 := DLMF.Bessel.Gamma_nat_add_half (n+1)
  rw [show (1/2:ℂ) + ((n+1:ℕ):ℂ) = (n:ℂ)+3/2 by push_cast; ring, legendre_Gamma_one_half] at hG2
  have hb0 : Gamma ((n:ℂ)+3/2) ≠ 0 := Gamma_ne_zero hb
  have hn0 : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have hp0 : poch ((n:ℂ)+3/2) k ≠ 0 := by
    show (ascPochhammer ℂ k).eval _ ≠ 0
    rw [← h2]; exact div_ne_zero
        (Gamma_ne_zero (fun m h => hb (m+k) (by push_cast; linear_combination h))) hb0
  have hr : (Real.sqrt π:ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hpi : (π:ℂ) = (Real.sqrt π:ℂ)^2 := by
    rw [← ofReal_pow, Real.sq_sqrt Real.pi_pos.le]
  have hA : Gamma ((n:ℂ)+k+1) = n.factorial * poch ((n:ℂ)+1) k := by
    rw [poch, ← h1, hG1, show (n:ℂ)+1+k = (n:ℂ)+k+1 by ring, mul_div_cancel₀ _ hn0]
  have hB : Gamma ((n:ℂ)+k+3/2) = Gamma ((n:ℂ)+3/2) * poch ((n:ℂ)+3/2) k := by
    rw [poch, ← h2, show (n:ℂ)+3/2+k = (n:ℂ)+k+3/2 by ring, mul_div_cancel₀ _ hb0]
  rw [hA, hB, hG2, hpi]
  have f1 : ((2*(n+1)).factorial : ℂ) = (2*n+2) * ((2*n+1).factorial : ℂ) := by
    rw [show 2*(n+1) = (2*n+1)+1 by ring, Nat.factorial_succ]; push_cast; ring
  have f2 : ((n+1).factorial : ℂ) = (n+1) * (n.factorial : ℂ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  rw [f1, f2]
  have : ((2*n+1).factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have : (2*(n:ℂ)+2) ≠ 0 := by
    have : (2*(n:ℂ)+2) = ((2*n+2:ℕ):ℂ) := by push_cast; ring
    rw [this]; exact_mod_cast (by omega : 2*n+2 ≠ 0)
  rw [show (4:ℂ)^(n+1) = 2^(2*n+2) by rw [show 2*n+2 = 2*(n+1) by ring, pow_mul]; norm_num]
  field_simp

/-- Integer degree and zero order are `Q`-regular. -/
theorem FerrersFourier.nat_regular (n : ℕ) : LegendreQRegular (n:ℂ) 0 := fun m h => by
  have := congrArg re h; simp at this;
      linarith [(m.cast_nonneg : (0:ℝ) ≤ m), (n.cast_nonneg : (0:ℝ) ≤ n)]

/-- DLMF 14.13.1: for `0 < θ < π`, `Re μ < 1/2` and `ν + μ ∉ {−1, −2, …}`, `𝖯^μ_ν(cos θ) =
(2^{μ+1}/π^{1/2}) sin^μ θ Σ_{k≥0} Γ(ν+μ+k+1)/Γ(ν+k+3/2) · (μ+1/2)_k/k! · sin((ν+μ+2k+1)θ)`, the
series converging as the limit of its partial sums. -/
@[dlmf 14.13.E1]
theorem ferrersP_fourier_series {ν μ : ℂ} (hν : LegendreQRegular ν μ) (hμ : μ.re < 1/2) {θ : ℝ}
    (h0 : 0 < θ) (hπ : θ < π) :
    Tendsto (fun N : ℕ => ∑ k ∈ Finset.range N,
        2^(μ+1)/Real.sqrt π*(Real.sin θ:ℂ)^μ*Gamma (ν+μ+k+1)/Gamma (ν+k+3/2)*poch (μ+1/2)
        k/(k.factorial:ℂ)*sin ((ν+μ+2*k+1)*θ)) atTop (𝓝 (ferrersP ν μ (Real.cos θ))) := by
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi h0 hπ
  have Ep := FourierHypergeometric.PQ_hypergeometric ν μ hν h0 hπ (s := 1) (Or.inl rfl)
  have Em := FourierHypergeometric.PQ_hypergeometric ν μ hν h0 hπ (s := -1) (Or.inr rfl)
  have hT : (2*Real.sin θ:ℂ)^μ = (2:ℂ)^μ*(Real.sin θ:ℂ)^μ := by
    rw [show (2:ℂ) = ((2:ℝ):ℂ) by norm_num, mul_cpow_ofReal_nonneg (by norm_num) hsin.le]
  rw [hT] at Ep Em
  have hp := FerrersFourier.tendsto_pair hν hμ h0 hπ (Or.inl rfl)
  have hm := FerrersFourier.tendsto_pair hν hμ h0 hπ (Or.inr rfl)
  have h := ((hm.sub hp).const_mul (2^(μ+1)/Real.sqrt π*(Real.sin θ:ℂ)^μ*I/2))
  have hr : (Real.sqrt π:ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hpi : (π:ℂ) = (Real.sqrt π:ℂ)^2 := by
    rw [← ofReal_pow, Real.sq_sqrt Real.pi_pos.le]
  have h2 : (2:ℂ)^(μ+1) = 2^μ*2 := by rw [cpow_add _ _ two_ne_zero, cpow_one]
  have e : ferrersP ν μ (Real.cos θ) = 2^(μ+1)/Real.sqrt π*(Real.sin θ:ℂ)^μ*I/2 *
      (exp (((-1:ℝ):ℂ)*(ν+μ+1)*I*θ) * (Gamma (ν+μ+1) *
        regularizedGaussHG (ν+μ+1) (μ+1/2) (ν+3/2) (exp (((-1:ℝ):ℂ)*2*I*θ))) -
      exp (((1:ℝ):ℂ)*(ν+μ+1)*I*θ) * (Gamma (ν+μ+1) *
        regularizedGaussHG (ν+μ+1) (μ+1/2) (ν+3/2) (exp (((1:ℝ):ℂ)*2*I*θ)))) := by
    have h1 : ((-1:ℝ):ℂ) = -1 := by push_cast; ring
    have h1' : ((1:ℝ):ℂ) = 1 := ofReal_one
    rw [hpi] at Ep Em
    rw [h2]
    simp only [h1, h1'] at Ep Em ⊢
    have hrinv : (Real.sqrt π:ℂ) * (Real.sqrt π:ℂ)⁻¹ = 1 := mul_inv_cancel₀ hr
    set r := (Real.sqrt π:ℂ)
    set a := r⁻¹
    set P := ferrersP ν μ (Real.cos θ)
    set T := (2:ℂ)^μ * (Real.sin θ:ℂ)^μ
    set G := Gamma (ν+μ+1)
    set D := exp (1*(ν+μ+1)*I*θ) * regularizedGaussHG (ν+μ+1) (μ+1/2) (ν+3/2) (exp (1*2*I*θ)) -
      exp (-1*(ν+μ+1)*I*θ) * regularizedGaussHG (ν+μ+1) (μ+1/2) (ν+3/2) (exp (-1*2*I*θ))
    linear_combination (-I*a^2)*(Ep - Em) + (-(P*(a*r+1) + a*T*I*G*D))*hrinv + (P*a^2*r^2)*I_sq
  rw [e]
  refine h.congr fun N => ?_
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Complex.sin, FerrersFourier.coeff]
  push_cast
  ring_nf

/-- Absolute convergence in DLMF 14.13. -/
theorem ferrersP_fourier_absolute {ν μ : ℂ} (hμ : μ.re < 0) {θ : ℝ} :
    Summable (fun k : ℕ =>
        ‖Gamma (ν+μ+k+1)/Gamma (ν+k+3/2)*poch (μ+1/2) k/(k.factorial:ℂ)*sin ((ν+μ+2*k+1)*θ)‖) := by
  refine FerrersFourier.summable hμ _ (B := Real.exp |((ν+μ)*θ).im|) fun k => ?_
  have him : ((ν+μ+2*(k:ℂ)+1)*(θ:ℂ)).im = ((ν+μ)*θ).im := by simp [mul_im]
  exact (FerrersFourier.norm_sin_le _).trans_eq (by rw [him])

/-- DLMF 14.13.3: for `n ∈ ℕ` and `0 < θ < π`, `𝖯_n(cos θ) = 2^{2n+2}(n!)²/(π (2n+1)!) Σ_{k≥0}
(1/2)_k (n+1)_k/(k! (n+3/2)_k) sin((n+2k+1)θ)`, the series converging as the limit of its partial
sums. -/
@[dlmf 14.13.E3]
theorem ferrersP_nat_fourier (n : ℕ) {θ : ℝ} (h0 : 0 < θ) (hπ : θ < π) :
    Tendsto (fun N : ℕ => ∑ k ∈ Finset.range N,
        2^(2*n+2)*(n.factorial:ℂ)^2/(π*((2*n+1).factorial:ℂ))*poch (1/2) k*poch (n+1)
        k/((k.factorial:ℂ)*poch (n+3/2) k)*sin ((n+2*k+1:ℂ)*θ)) atTop
        (𝓝 (ferrersP n 0 (Real.cos θ))) := by
  have h := ferrersP_fourier_series (FerrersFourier.nat_regular n) (by simp) h0 hπ
  refine h.congr fun N => Finset.sum_congr rfl fun k _ => ?_
  have e := FerrersFourier.nat_coeff n k
  simp only [zero_add, add_zero, cpow_one, cpow_zero, mul_one]
  calc (2:ℂ)/Real.sqrt π*Gamma ((n:ℂ)+k+1)/Gamma ((n:ℂ)+k+3/2)*poch (1/2) k/(k.factorial:ℂ)*
        sin (((n:ℂ)+2*k+1)*θ)
      = (2/Real.sqrt π*(Gamma ((n:ℂ)+k+1)/Gamma ((n:ℂ)+k+3/2))) *
          (poch (1/2) k/(k.factorial:ℂ)*sin (((n:ℂ)+2*k+1)*θ)) := by ring
    _ = _ := by rw [e]; ring

/-- DLMF 14.13.2: for `0 < θ < π`, `Re μ < 1/2` and `ν + μ ∉ {−1, −2, …}`, `𝖰^μ_ν(cos θ) = π^{1/2}
2^μ sin^μ θ Σ_{k≥0} Γ(ν+μ+k+1)/Γ(ν+k+3/2) · (μ+1/2)_k/k! · cos((ν+μ+2k+1)θ)`, the series converging
as the limit of its partial sums. -/
@[dlmf 14.13.E2]
theorem ferrersQ_fourier_series {ν μ : ℂ} (hν : LegendreQRegular ν μ) (hμ : μ.re < 1/2) {θ : ℝ}
    (h0 : 0 < θ) (hπ : θ < π) :
    Tendsto (fun N : ℕ => ∑ k ∈ Finset.range N,
        Real.sqrt π*2^μ*(Real.sin θ:ℂ)^μ*Gamma (ν+μ+k+1)/Gamma (ν+k+3/2)*poch (μ+1/2)
        k/(k.factorial:ℂ)*cos ((ν+μ+2*k+1)*θ)) atTop (𝓝 (ferrersQ ν μ (Real.cos θ))) := by
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi h0 hπ
  have Ep := FourierHypergeometric.PQ_hypergeometric ν μ hν h0 hπ (s := 1) (Or.inl rfl)
  have Em := FourierHypergeometric.PQ_hypergeometric ν μ hν h0 hπ (s := -1) (Or.inr rfl)
  have hT : (2*Real.sin θ:ℂ)^μ = (2:ℂ)^μ*(Real.sin θ:ℂ)^μ := by
    rw [show (2:ℂ) = ((2:ℝ):ℂ) by norm_num, mul_cpow_ofReal_nonneg (by norm_num) hsin.le]
  rw [hT] at Ep Em
  have hp := FerrersFourier.tendsto_pair hν hμ h0 hπ (Or.inl rfl)
  have hm := FerrersFourier.tendsto_pair hν hμ h0 hπ (Or.inr rfl)
  have h := ((hp.add hm).const_mul (Real.sqrt π*2^μ*(Real.sin θ:ℂ)^μ/2))
  have e : ferrersQ ν μ (Real.cos θ) = Real.sqrt π*2^μ*(Real.sin θ:ℂ)^μ/2 *
      (exp (((1:ℝ):ℂ)*(ν+μ+1)*I*θ) * (Gamma (ν+μ+1) *
        regularizedGaussHG (ν+μ+1) (μ+1/2) (ν+3/2) (exp (((1:ℝ):ℂ)*2*I*θ))) +
      exp (((-1:ℝ):ℂ)*(ν+μ+1)*I*θ) * (Gamma (ν+μ+1) *
        regularizedGaussHG (ν+μ+1) (μ+1/2) (ν+3/2) (exp (((-1:ℝ):ℂ)*2*I*θ)))) := by
    have h1 : ((-1:ℝ):ℂ) = -1 := by push_cast; ring
    have h2 : ((1:ℝ):ℂ) = 1 := ofReal_one
    linear_combination (1/2:ℂ)*Ep + (1/2:ℂ)*Em - (π*I*ferrersP ν μ (Real.cos θ)/4)*h1 -
      (π*I*ferrersP ν μ (Real.cos θ)/4)*h2
  rw [e]
  refine h.congr fun N => ?_
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Complex.cos, FerrersFourier.coeff]
  push_cast
  ring_nf

/-- Absolute convergence in DLMF 14.13. -/
theorem ferrersQ_fourier_absolute {ν μ : ℂ} (hμ : μ.re < 0) {θ : ℝ} :
    Summable (fun k : ℕ =>
        ‖Gamma (ν+μ+k+1)/Gamma (ν+k+3/2)*poch (μ+1/2) k/(k.factorial:ℂ)*cos ((ν+μ+2*k+1)*θ)‖) := by
  refine FerrersFourier.summable hμ _ (B := Real.exp |((ν+μ)*θ).im|) fun k => ?_
  have him : ((ν+μ+2*(k:ℂ)+1)*(θ:ℂ)).im = ((ν+μ)*θ).im := by simp [mul_im]
  exact (FerrersFourier.norm_cos_le _).trans_eq (by rw [him])

/-- For complex `w`, `|sin (re w)| ≤ ‖sin w‖`. -/
theorem FerrersFourier.abs_sin_re_le (w : ℂ) : |Real.sin w.re| ≤ ‖sin w‖ := by
  have h : (sin w).re = Real.sin w.re * Real.cosh w.im := by
    rw [sin_eq]; simp [← ofReal_sin, ← ofReal_cosh, ← ofReal_cos, ← ofReal_sinh]
  refine le_trans ?_ (abs_re_le_norm _)
  rw [h, abs_mul, abs_of_pos (Real.cosh_pos _)]
  exact le_mul_of_one_le_right (abs_nonneg _) (Real.one_le_cosh _)

/-- For complex `w`, `|cos (re w)| ≤ ‖cos w‖`. -/
theorem FerrersFourier.abs_cos_re_le (w : ℂ) : |Real.cos w.re| ≤ ‖cos w‖ := by
  have h : (cos w).re = Real.cos w.re * Real.cosh w.im := by
    rw [cos_eq]; simp [← ofReal_sin, ← ofReal_cosh, ← ofReal_cos, ← ofReal_sinh]
  refine le_trans ?_ (abs_re_le_norm _)
  rw [h, abs_mul, abs_of_pos (Real.cosh_pos _)]
  exact le_mul_of_one_le_right (abs_nonneg _) (Real.one_le_cosh _)

/-- For real `x` and `θ`, `|sin 2θ|/2 ≤ |sin x| + |sin (x + 2θ)|`. -/
theorem FerrersFourier.sin_pair {θ : ℝ} (x : ℝ) :
    |Real.sin (2*θ)| / 2 ≤ |Real.sin x| + |Real.sin (x + 2*θ)| := by
  have hs : |Real.sin (2*θ)| ≤ 1 := Real.abs_sin_le_one _
  have h1 : |Real.sin x| + |Real.cos x| ≥ 1 := by
    have := Real.sin_sq_add_cos_sq x
    nlinarith [abs_nonneg (Real.sin x), abs_nonneg (Real.cos x), sq_abs (Real.sin x),
      sq_abs (Real.cos x), abs_le.mp (Real.abs_sin_le_one x), abs_le.mp (Real.abs_cos_le_one x)]
  have h2 : |Real.cos x| * |Real.sin (2*θ)| ≤ |Real.sin (x + 2*θ)| + |Real.sin x| := by
    rw [Real.sin_add, ← abs_mul]
    have := abs_add_le (Real.sin x * Real.cos (2*θ) + Real.cos x * Real.sin (2*θ))
      (-(Real.sin x * Real.cos (2*θ)))
    rw [show Real.sin x * Real.cos (2*θ) + Real.cos x * Real.sin (2*θ) +
      -(Real.sin x * Real.cos (2*θ)) = Real.cos x * Real.sin (2*θ) by ring, abs_neg,
      abs_mul _ (Real.cos _)] at this
    have hc := Real.abs_cos_le_one (2*θ)
    nlinarith [abs_nonneg (Real.sin x), abs_nonneg (Real.cos (2*θ))]
  have h3 := mul_le_mul_of_nonneg_left hs (abs_nonneg (Real.sin x))
  have h4 := mul_le_mul_of_nonneg_left h1.le (abs_nonneg (Real.sin (2*θ)))
  nlinarith [abs_nonneg (Real.sin (x + 2*θ))]

/-- For real `x` and `θ`, `|sin 2θ|/2 ≤ |cos x| + |cos (x + 2θ)|`. -/
theorem FerrersFourier.cos_pair {θ : ℝ} (x : ℝ) :
    |Real.sin (2*θ)| / 2 ≤ |Real.cos x| + |Real.cos (x + 2*θ)| := by
  have h := FerrersFourier.sin_pair (θ := θ) (x + π/2)
  rw [Real.sin_add_pi_div_two, show x + π/2 + 2*θ = (x + 2*θ) + π/2 by ring,
    Real.sin_add_pi_div_two] at h
  exact h

/-- DLMF 14.13.4: for `n ∈ ℕ` and `0 < θ < π`, `𝖰_n(cos θ) = 2^{2n+1}(n!)²/(2n+1)! Σ_{k≥0} (1/2)_k
(n+1)_k/(k! (n+3/2)_k) cos((n+2k+1)θ)`, the series converging as the limit of its partial sums. -/
@[dlmf 14.13.E4]
theorem ferrersQ_nat_fourier (n : ℕ) {θ : ℝ} (h0 : 0 < θ) (hπ : θ < π) :
    Tendsto (fun N : ℕ => ∑ k ∈ Finset.range N,
        2^(2*n+1)*(n.factorial:ℂ)^2/((2*n+1).factorial:ℂ)*poch (1/2) k*poch (n+1)
        k/((k.factorial:ℂ)*poch (n+3/2) k)*cos ((n+2*k+1:ℂ)*θ)) atTop
        (𝓝 (ferrersQ n 0 (Real.cos θ))) := by
  have h := ferrersQ_fourier_series (FerrersFourier.nat_regular n) (by simp) h0 hπ
  refine h.congr fun N => Finset.sum_congr rfl fun k _ => ?_
  have e := FerrersFourier.nat_coeff n k
  have hr : (Real.sqrt π:ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hpi : (π:ℂ) = (Real.sqrt π:ℂ)^2 := by
    rw [← ofReal_pow, Real.sq_sqrt Real.pi_pos.le]
  have hs : (π:ℂ)/2 * (2/Real.sqrt π) = Real.sqrt π := by rw [hpi]; field_simp
  simp only [zero_add, add_zero, cpow_zero, mul_one]
  calc (Real.sqrt π:ℂ)*Gamma ((n:ℂ)+k+1)/Gamma ((n:ℂ)+k+3/2)*poch (1/2) k/(k.factorial:ℂ)*
        cos (((n:ℂ)+2*k+1)*θ)
      = (π/2*(2/Real.sqrt π))*(Gamma ((n:ℂ)+k+1)/Gamma ((n:ℂ)+k+3/2)) *
          (poch (1/2) k/(k.factorial:ℂ)*cos (((n:ℂ)+2*k+1)*θ)) := by rw [hs]; ring
    _ = π/2*(2/Real.sqrt π*(Gamma ((n:ℂ)+k+1)/Gamma ((n:ℂ)+k+3/2))) *
          (poch (1/2) k/(k.factorial:ℂ)*cos (((n:ℂ)+2*k+1)*θ)) := by ring
    _ = _ := by
      rw [e]
      have : (π:ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_pos.ne'
      rw [pow_succ]
      field_simp

/-- DLMF 14.7.4: the polynomial `W_{n−1}` (`legendreQPoly n`) is the convolution `W_{n−1}(z) =
Σ_{k=1}^{n} P_{k−1}(z) P_{n−k}(z)/k` of Legendre polynomials. -/
@[dlmf 14.7.E4]
theorem legendreQPoly_convolution (n : ℕ) (z : ℂ) :
    (legendreQPoly n).eval z=∑ j ∈ Finset.range n, legendreP j z*legendreP (n-j-1) z/(j+1:ℂ) := by
  rw [← GeneratingSeries.product_eq z n, GeneratingSeries.coeff_product]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj : j < n := Finset.mem_range.mp hj
  simp only [GeneratingSeries.legendreSeq]
  rw [show ((n-j-1:ℕ):ℂ) = (n:ℂ)-j-1 by rw [Nat.cast_sub (by omega), Nat.cast_sub hj.le]; simp]

/-- DLMF 14.7.3: the explicit expansion `W_{n−1}(z) = Σ_{s=0}^{n−1} (n+s)! (ψ(n+1) − ψ(s+1))/(2^s
(n−s)! (s!)²) (z−1)^s` of the polynomial `legendreQPoly n` (the `s = n` term of DLMF vanishes). -/
@[dlmf 14.7.E3]
theorem legendreQPoly_explicit (n : ℕ) (z : ℂ) :
    (legendreQPoly n).eval z=∑ s ∈ Finset.range n,
        ((n+s).factorial:ℂ)*(digamma (n+1)-digamma
        (s+1))/(2^s*(n-s).factorial*(s.factorial:ℂ)^2)*(z-1)^s := by
  rw [← GeneratingSeries.secondKind_eq, GeneratingSeries.secondKind]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hs : s < n := Finset.mem_range.mp hs
  rw [Complex.digamma_nat_add_one, Complex.digamma_nat_add_one]
  simp only [GeneratingSeries.secondKindCoeff, GeneratingSeries.pCoeff, show s ≤ n by
      omega, ↓reduceIte]
  push_cast
  ring

/-- DLMF 14.7.5: the first polynomials `W_{n−1}` are `W_0 = 1`, `W_1(x) = (3/2)x` and `W_2(x) =
(5/2)x² − 2/3`. -/
@[dlmf 14.7.E5]
theorem legendreQPoly_initial  :
    legendreQPoly 1=1 ∧ legendreQPoly 2=Polynomial.C (3/2)*Polynomial.X ∧
        legendreQPoly 3=Polynomial.C (5/2)*Polynomial.X^2-Polynomial.C (2/3) := by
  have h2 : legendreQPoly 2=Polynomial.C (3/2)*Polynomial.X := by
    norm_num [legendreQPoly, ← mul_assoc, ← Polynomial.C_mul]
  have h3 : legendreQPoly 3=Polynomial.C (5/2)*Polynomial.X^2-Polynomial.C (2/3) := by
    rw [legendreQPoly, h2]
    norm_num only [legendreQPoly, mul_one]
    rw [show Polynomial.C
        (1/3:ℂ)*(Polynomial.C 5*Polynomial.X*(Polynomial.C (3/2)*Polynomial.X)-Polynomial.C 2) =
      (Polynomial.C (1/3)*Polynomial.C 5*Polynomial.C (3/2))*Polynomial.X^2-
        Polynomial.C (1/3)*Polynomial.C 2 by ring]
    norm_num [← Polynomial.C_mul]
  exact ⟨rfl,h2,h3⟩

/-- DLMF 14.7.2: for `n ∈ ℕ` and `-1 < x < 1`, `𝖰_n(x) = ½ 𝖯_n(x) ln((1+x)/(1−x)) − W_{n−1}(x)`. -/
@[dlmf 14.7.E2]
theorem ferrersQ_nat_logarithm (n : ℕ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ferrersQ n 0 x=1/2*ferrersP n 0 x*log ((1+x)/(1-x):ℂ)-(legendreQPoly n).eval (x:ℂ) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ =>
      simp [legendreQPoly, ferrersQ_degree_0 hx, ferrersP_degree_0 hx]
    | 1, _ =>
      simp only [Nat.cast_one, legendreQPoly, Polynomial.eval_one]
      rw [ferrersQ_degree_1 hx, ferrersP_degree_1 hx]; ring
    | n + 2, ih =>
      have hreg : LegendreQRegular (n:ℂ) 0 := fun k hk => by
        have : ((n:ℝ) : ℂ).re = (-((k:ℂ)+1)).re := by rw [← hk]; simp
        simp at this; linarith [(n.cast_nonneg : (0:ℝ) ≤ n), (k.cast_nonneg : (0:ℝ) ≤ k)]
      have hQ := ferrersQ_recurrence_3 (n:ℂ) 0 hreg hx
      have hP := ferrersP_recurrence_3 (n:ℂ) 0 hx
      have h1 := ih (n + 1) (by omega)
      have h0 := ih n (by omega)
      push_cast at h1 h0 ⊢
      rw [show (n:ℂ)+2 = n+1+1 by ring] at hQ hP
      simp only [legendreQPoly, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_C,
        Polynomial.eval_X]
      have hn : (n : ℂ) + 2 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (n + 1)
      rw [show (n:ℂ)+2 = n+1+1 by ring] at hn ⊢
      have hinv : ((n:ℂ)+1+1)*((n:ℂ)+1+1)⁻¹ = 1 := mul_inv_cancel₀ hn
      linear_combination ((n:ℂ)+1+1)⁻¹*(hQ - 1/2*log ((1+x)/(1-x):ℂ) * hP +
          (2 * (n : ℂ) + 3) * x * h1 -
        ((n : ℂ) + 1) * h0) -
            (ferrersQ ((n:ℂ)+1+1) 0 x - 1/2*log ((1+x)/(1-x):ℂ)*ferrersP ((n:ℂ)+1+1) 0 x)*hinv

/-- DLMF 14.7.6: for `n ∈ ℕ` and `z ∉ (−∞, 1]`, `Q_n(z) = n! 𝑸_n(z)`. -/
@[dlmf 14.7.E6]
theorem olverQ_nat_normalization (n : ℕ) {z : ℂ} :
    associatedQ n 0 z=(n.factorial:ℂ)*olverQ n 0 z := by
  simp [associatedQ, Gamma_nat_eq_factorial]

/-- DLMF 14.7.7: for `n ∈ ℕ` and `z ∉ (−∞, 1]`, `Q_n(z) = ½ P_n(z) (ln(z+1) − ln(z−1)) −
W_{n−1}(z)`, with principal logarithms. -/
@[dlmf 14.7.E7]
theorem associatedQ_nat_logarithm (n : ℕ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    associatedQ n 0 z=1/2*associatedP n 0 z*(log (z+1)-log (z-1))-(legendreQPoly n).eval z := by
  rw [associatedQ_zero_order _, associatedP_zero_order _ hz, legendreQ_nat n hz, legendreQ_zero hz,
    log_add_one_sub_log_sub_one hz]
  ring

/-- DLMF 14.7.19 (real case): for `-1 < x < 1` and `|h| < 1`, `Σ_{n≥0} 𝖯_n(x) hⁿ = (1 − 2xh +
h²)^{−1/2}`. -/
@[dlmf 14.7.E19]
theorem ferrersP_generating {x h : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) (hh : |h| < 1) :
    HasSum (fun n : ℕ => ferrersP n 0 x*(h:ℂ)^n) ((1-2*x*h+h^2:ℂ)^(-1/2:ℂ)) := by
  have hg := DLMF.OrthogonalPolynomials.legendre_generating_function (x := x)
    (abs_le.mpr ⟨hx.1.le, hx.2.le⟩) (z := (h:ℂ))
        (by rw [Complex.norm_real, Real.norm_eq_abs]; exact hh)
  refine hg.congr_fun fun n => ?_
  have hs : 1+(x:ℂ) ∈ slitPlane := Or.inl (by simp; linarith [hx.1])
  rw [ferrersP_zero _ hx.1, legendreP_nat n hs]

/-- DLMF 14.7.20: for `-1 < x < 1` and `|h| < 1`, `Σ_{n≥0} 𝖰_n(x) hⁿ = (1 − 2xh + h²)^{−1/2} ln((x −
h + (1 − 2xh + h²)^{1/2})/(1−x²)^{1/2})`. -/
@[dlmf 14.7.E20]
theorem ferrersQ_generating {x h : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) (hh : |h| < 1) :
    HasSum (fun n : ℕ => ferrersQ n 0 x*(h:ℂ)^n)
        ((1-2*x*h+h^2:ℂ)^(-1/2:ℂ)*log ((x-h+(1-2*x*h+h^2:ℂ)^(1/2:ℂ))/(1-x^2:ℂ)^(1/2:ℂ))) := by
  have hx2 : 0 < 1 - x^2 := by nlinarith [hx.1, hx.2]
  set w : ℝ := √(1-x^2)
  have hw2 : w^2 = 1 - x^2 := Real.sq_sqrt hx2.le
  set ζ₁ : ℂ := x + w * I
  set ζ₂ : ℂ := x - w * I
  have hs : ζ₁ + ζ₂ = 2*x := by simp only [ζ₁, ζ₂]; ring
  have hp : ζ₁ * ζ₂ = 1 := by
    simp only [ζ₁, ζ₂]
    have : ((w:ℂ))^2 = 1 - (x:ℂ)^2 := by exact_mod_cast hw2
    linear_combination (1:ℂ) * this - (w:ℂ)^2 * Complex.I_sq
  have hnz : ∀ ζ : ℂ, (ζ = ζ₁ ∨ ζ = ζ₂) → ‖ζ‖ = 1 := by
    intro ζ hζ
    have hsq : ‖ζ‖^2 = 1 := by
      rcases hζ with rfl | rfl <;>
      · rw [Complex.sq_norm, Complex.normSq_apply]; simp [ζ₁, ζ₂]; nlinarith [hw2]
    nlinarith [norm_nonneg ζ]
  set r : ℝ := (|h| + 1)/2
  have hr : r < 1 := by simp only [r]; linarith
  have hhr : |h| < r := by simp only [r]; linarith
  have hr0 : 0 ≤ r := by simp only [r]; positivity
  have hnr : ∀ ζ : ℂ, (ζ = ζ₁ ∨ ζ = ζ₂) → ‖(r:ℂ)*ζ‖ < 1 := fun ζ hζ => by
    rw [norm_mul, hnz ζ hζ, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]; linarith
  have hq : ∀ t : ℝ, |t| < r → 0 < 1-2*x*t+t^2 := fun t _ => by nlinarith [sq_nonneg (t-x)]
  have hl : ∀ t : ℝ, |t| < r → 0 < x - t + √(1-2*x*t+t^2) := fun t ht => by
    have hq' := hq t ht
    have hlt : |x - t| < √(1-2*x*t+t^2) := by
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_lt_sqrt (sq_nonneg _) (by nlinarith)
    linarith [neg_abs_le (x-t)]
  have e := GeneratingSeries.hasSum_legendreQ_real ζ₁ ζ₂ hs hp (hnr ζ₁ (Or.inl rfl))
      (hnr ζ₂ (Or.inr rfl)) hq hl hhr
    (1/2*log ((1+x)/(1-x):ℂ))
  have hP : ∀ n : ℕ, ferrersP n 0 x = GeneratingSeries.legendreSeq x n := fun n =>
      ferrersP_zero _ hx.1
  convert e using 1
  · funext n; rw [ferrersQ_nat_logarithm n hx, hP n]; ring
  · have hq0 := hq h hhr
    have hl0 := hl h hhr
    rw [mul_comm]
    congr 1
    rw [show (1-2*x*h+h^2:ℂ) = ((1-2*x*h+h^2:ℝ):ℂ) by push_cast; ring,
                                                        Carlson.ofReal_cpow_half hq0.le,
      show (1-x^2:ℂ) = ((1-x^2:ℝ):ℂ) by push_cast; ring, Carlson.ofReal_cpow_half hx2.le,
      show ((1+x)/(1-x):ℂ) = (((1+x)/(1-x):ℝ):ℂ) by push_cast; ring,
      ← Complex.ofReal_log (div_pos (by linarith [hx.1]) (by linarith [hx.2])).le,
      show (x:ℂ) - h + ((√(1-2*x*h+h^2):ℝ):ℂ) =
          ((x - h + √(1-2*x*h+h^2) : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_div, ← Complex.ofReal_log (div_pos hl0 (Real.sqrt_pos.mpr hx2)).le]
    have h1x : 0 < 1 + x := by linarith [hx.1]
    have h1x' : 0 < 1 - x := by linarith [hx.2]
    rw [Real.log_div hl0.ne' (Real.sqrt_pos.mpr hx2).ne', Real.log_sqrt hx2.le,
      Real.log_div h1x.ne' h1x'.ne', show 1 - x^2 = (1+x)*(1-x) by ring,
      Real.log_mul h1x.ne' h1x'.ne']
    push_cast; ring

/-- DLMF 14.7.22: for `x > 1` and `|h| < x − (x²−1)^{1/2}`, `Σ_{n≥0} Q_n(x) hⁿ = (1 − 2xh +
h²)^{−1/2} ln((x − h + (1 − 2xh + h²)^{1/2})/(x²−1)^{1/2})`. -/
@[dlmf 14.7.E22]
theorem associatedQ_generating {x h : ℝ} (hx : 1 < x) (hh : |h| < x-Real.sqrt (x^2-1)) :
    HasSum (fun n : ℕ => associatedQ n 0 x*(h:ℂ)^n)
        ((1-2*x*h+h^2:ℂ)^(-1/2:ℂ)*log ((x-h+(1-2*x*h+h^2:ℂ)^(1/2:ℂ))/(x^2-1:ℂ)^(1/2:ℂ))) := by
  have hx2 : 0 < x^2 - 1 := by nlinarith
  set w : ℝ := √(x^2-1)
  have hw2 : w^2 = x^2 - 1 := Real.sq_sqrt hx2.le
  have hw0 : 0 < w := Real.sqrt_pos.mpr hx2
  have hwx : w < x := by nlinarith
  set ρ : ℝ := x - w
  have hρ0 : 0 < ρ := by simp only [ρ]; linarith
  have hρ1 : ρ * (x + w) = 1 := by simp only [ρ]; nlinarith
  have hρ : ρ < 1 := by nlinarith
  set ζ₁ : ℂ := ((x + w : ℝ) : ℂ)
  set ζ₂ : ℂ := ((ρ : ℝ) : ℂ)
  have hs : ζ₁ + ζ₂ = 2*x := by simp only [ζ₁, ζ₂, ρ]; push_cast; ring
  have hp : ζ₁ * ζ₂ = 1 := by simp only [ζ₁, ζ₂]; rw [mul_comm]; exact_mod_cast hρ1
  set r : ℝ := (|h| + ρ)/2
  have hrρ : r < ρ := by simp only [r]; linarith
  have hhr : |h| < r := by simp only [r]; linarith
  have hr0 : 0 < r := by simp only [r]; positivity
  have h1 : ‖(r:ℂ)*ζ₁‖ < 1 := by
    rw [← Complex.ofReal_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    nlinarith
  have h2 : ‖(r:ℂ)*ζ₂‖ < 1 := by
    rw [← Complex.ofReal_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    nlinarith
  have hq : ∀ t : ℝ, |t| < r → 0 < 1-2*x*t+t^2 := fun t ht => by
    have := abs_lt.mp ht
    have e : 1-2*x*t+t^2 = (ρ - t) * (x + w - t) := by simp only [ρ]; nlinarith
    rw [e]; exact mul_pos (by linarith) (by linarith)
  have hl : ∀ t : ℝ, |t| < r → 0 < x - t + √(1-2*x*t+t^2) := fun t ht => by
    have := abs_lt.mp ht
    have := Real.sqrt_nonneg (1-2*x*t+t^2)
    linarith
  have e := GeneratingSeries.hasSum_legendreQ_real ζ₁ ζ₂ hs hp h1 h2 hq hl hhr
    (1/2*(log ((x:ℂ)+1) - log ((x:ℂ)-1)))
  have hz : (x:ℂ) - 1 ∈ slitPlane := Or.inl (by simp; linarith)
  have hP : ∀ n : ℕ, associatedP n 0 x = GeneratingSeries.legendreSeq x n := fun n =>
      associatedP_zero_order _ hz
  convert e using 1
  · funext n; rw [associatedQ_nat_logarithm n hz, hP n]; ring
  · have hq0 := hq h hhr
    have hl0 := hl h hhr
    rw [mul_comm]
    congr 1
    rw [show (1-2*x*h+h^2:ℂ) = ((1-2*x*h+h^2:ℝ):ℂ) by push_cast; ring,
                                                        Carlson.ofReal_cpow_half hq0.le,
      show (x^2-1:ℂ) = ((x^2-1:ℝ):ℂ) by push_cast; ring, Carlson.ofReal_cpow_half hx2.le,
      show (x:ℂ) + 1 = ((x+1:ℝ):ℂ) by push_cast; ring,
      show (x:ℂ) - 1 = ((x-1:ℝ):ℂ) by push_cast; ring,
      ← Complex.ofReal_log (by linarith), ← Complex.ofReal_log (by linarith),
      show (x:ℂ) - h + ((√(1-2*x*h+h^2):ℝ):ℂ) =
          ((x - h + √(1-2*x*h+h^2) : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_div, ← Complex.ofReal_log (div_pos hl0 hw0).le]
    have h1x : 0 < x + 1 := by linarith
    have h1x' : 0 < x - 1 := by linarith
    rw [Real.log_div hl0.ne' hw0.ne', Real.log_sqrt hx2.le, show x^2 - 1 = (x+1)*(x-1) by ring,
      Real.log_mul h1x.ne' h1x'.ne', add_comm 1 x]
    push_cast; ring

/-- DLMF 14.7.19 (complex case): for `z ∉ (−∞, 1]` and `|h| < min |z ± (z²−1)^{1/2}|`, `Σ_{n≥0}
P_n(z) hⁿ = (1 − 2zh + h²)^{−1/2}`. -/
@[dlmf 14.7.E19]
theorem associatedP_generating_complex {z h : ℂ} (hz : z-1 ∈ slitPlane)
    (hh : ‖h‖ < min ‖z+exp ((log (z-1)+log (z+1))/2)‖ ‖z-exp ((log (z-1)+log (z+1))/2)‖) :
    HasSum (fun n : ℕ => associatedP n 0 z*h^n) ((1-2*z*h+h^2)^(-1/2:ℂ)) := by
  obtain ⟨hs, hp⟩ := GeneratingSeries.roots hz
  set s := exp ((log (z-1)+log (z+1))/2)
  have hn : ‖z+s‖ * ‖z-s‖ = 1 := by rw [← norm_mul, hp, norm_one]
  have h1 : ‖h*(z+s)‖ < 1 := by
    rw [norm_mul]
    calc ‖h‖ * ‖z+s‖ < ‖z-s‖ * ‖z+s‖ :=
          mul_lt_mul_of_pos_right (lt_of_lt_of_le hh (min_le_right _ _))
            (by rcases (norm_nonneg (z+s)).lt_or_eq with h0 | h0
                · exact h0
                · rw [← h0, zero_mul] at hn; exact absurd hn zero_ne_one)
      _ = 1 := by rw [mul_comm, hn]
  have h2 : ‖h*(z-s)‖ < 1 := by
    rw [norm_mul]
    calc ‖h‖ * ‖z-s‖ < ‖z+s‖ * ‖z-s‖ :=
          mul_lt_mul_of_pos_right (lt_of_lt_of_le hh (min_le_left _ _))
            (by rcases (norm_nonneg (z-s)).lt_or_eq with h0 | h0
                · exact h0
                · rw [← h0, mul_zero] at hn; exact absurd hn zero_ne_one)
      _ = 1 := hn
  refine (GeneratingSeries.generating z (z+s) (z-s) h hs hp h1 h2).congr_fun fun n => ?_
  rw [associatedP_zero_order _ hz]; rfl

/-- The exterior square root is normalized at infinity; principal sqrt of h squared would have the
wrong sign for negative h. -/
@[dlmf 14.7.E21]
theorem associatedP_exterior_generating {z h : ℂ} (hz : z-1 ∈ slitPlane)
    (hh : max ‖z+exp ((log (z-1)+log (z+1))/2)‖ ‖z-exp ((log (z-1)+log (z+1))/2)‖ < ‖h‖) :
    HasSum (fun n : ℕ => associatedP n 0 z*h^(-(n+1:ℤ))) (h⁻¹*(1-2*z/h+1/h^2)^(-1/2:ℂ)) := by
  obtain ⟨hs, hp⟩ := GeneratingSeries.roots hz
  set s := exp ((log (z-1)+log (z+1))/2)
  have hn : ‖z+s‖ * ‖z-s‖ = 1 := by rw [← norm_mul, hp, norm_one]
  have hA : 0 < ‖z+s‖ := by
    rcases (norm_nonneg (z+s)).lt_or_eq with h0 | h0
    · exact h0
    · rw [← h0, zero_mul] at hn; exact absurd hn zero_ne_one
  have hB : 0 < ‖z-s‖ := by
    rcases (norm_nonneg (z-s)).lt_or_eq with h0 | h0
    · exact h0
    · rw [← h0, mul_zero] at hn; exact absurd hn zero_ne_one
  have hpos : 0 < ‖h‖ := lt_of_le_of_lt (le_max_of_le_left hA.le) hh
  have h0 : h ≠ 0 := norm_pos_iff.mp hpos
  have hh' : ‖h⁻¹‖ < min ‖z+s‖ ‖z-s‖ := by
    rw [norm_inv, lt_min_iff]
    constructor
    · rw [inv_lt_iff_one_lt_mul₀ hpos, ← hn]
      exact mul_lt_mul_of_pos_left (lt_of_le_of_lt (le_max_right _ _) hh) hA
    · rw [inv_lt_iff_one_lt_mul₀ hpos, ← hn, mul_comm (‖z+s‖)]
      exact mul_lt_mul_of_pos_left (lt_of_le_of_lt (le_max_left _ _) hh) hB
  have e := (associatedP_generating_complex hz hh').mul_left h⁻¹
  rw [show (1:ℂ) - 2*z*h⁻¹ + h⁻¹^2 = 1-2*z/h+1/h^2 by field_simp] at e
  refine e.congr_fun fun n => ?_
  rw [zpow_neg, show ((n:ℤ)+1) = ((n+1:ℕ):ℤ) by push_cast; ring, zpow_natCast, pow_succ,
    inv_pow]
  ring

/-- DLMF 14.14.2: the partial numerators `(ν−μ−k+1)(ν+μ+k)(x²−1)/4` of the continued fraction
14.14.1 for `P^μ_ν(x)`. -/
@[dlmf 14.14.E2]
def legendrePCFNum (ν μ : ℂ) (x : ℝ) (k : ℕ) : ℂ :=
  (ν-μ-k+1)*(ν+μ+k)*(x^2-1)/4

/-- DLMF 14.14.2: the partial denominators `(μ+k) x` of the continued fraction 14.14.1 for
`P^μ_ν(x)`. -/
@[dlmf 14.14.E2]
def legendrePCFDen (μ : ℂ) (x : ℝ) (k : ℕ) : ℂ :=
  (μ+k)*x

/-- DLMF 14.14.4: the partial numerators of the continued fraction 14.14.3 for `Q^μ_ν(x)`: `1` at `k
= 0` and `−(ν+μ+k)(ν−μ+k)` for `k ≥ 1`. -/
@[dlmf 14.14.E4]
def legendreQCFNum (ν μ : ℂ) (k : ℕ) : ℂ :=
  (if k=0 then 1 else -1)*(ν+μ+k)*(ν-μ+k)

/-- DLMF 14.14.4: the partial denominators `(2ν+2k+1) x` of the continued fraction 14.14.3 for
`Q^μ_ν(x)`. -/
@[dlmf 14.14.E4]
def legendreQCFDen (ν : ℂ) (x : ℝ) (k : ℕ) : ℂ :=
  (2*ν+2*k+1)*x

/-! ### Tools for the continued fraction 14.14.3 -/

/-- The backward solution `w_k = 𝑸^μ_{ν+k-1}(x)` of the fraction 14.14.3. -/
def ContinuedFraction.backwardQ (ν μ : ℂ) (x : ℝ) (k : ℕ) : ℂ := olverQ (ν + k - 1) μ x

/-- `w_k = 𝑸^μ_{ν+k-1}(x)` solves the backward recurrence of 14.14.3 (from DLMF 14.10.3). -/
theorem ContinuedFraction.backwardQ_recurrence (ν μ : ℂ) {x : ℝ} (hx : 1 < x) (k : ℕ) :
    ContinuedFraction.backwardQ ν μ x k = legendreQCFDen ν x k *
        ContinuedFraction.backwardQ ν μ x (k+1) +
      legendreQCFNum ν μ (k+1) * ContinuedFraction.backwardQ ν μ x (k+2) := by
  have R := olverQ_recurrence_3 (ν+k-1) μ (LaplaceIntegrals.one_lt_mem hx)
  rw [show ν+k-1+2 = ν+(k:ℂ)+2-1 by ring, show ν+k-1+1 = ν+(k:ℂ)+1-1 by ring] at R
  have e1 : ContinuedFraction.backwardQ ν μ x (k+1) = olverQ (ν+(k:ℂ)+1-1) μ x := by
    unfold ContinuedFraction.backwardQ; congr 1; push_cast; ring
  have e2 : ContinuedFraction.backwardQ ν μ x (k+2) = olverQ (ν+(k:ℂ)+2-1) μ x := by
    unfold ContinuedFraction.backwardQ; congr 1; push_cast; ring
  rw [e1, e2]
  simp only [ContinuedFraction.backwardQ, legendreQCFDen, legendreQCFNum,
      Nat.add_one_ne_zero, ite_false]
  push_cast
  linear_combination R

/-- The hypergeometric form of `w_k`. -/
theorem ContinuedFraction.backwardQ_eq (ν μ : ℂ) {x : ℝ} (hx : 1 < x) (k : ℕ) :
    ContinuedFraction.backwardQ ν μ x k = Real.sqrt π *
        (1 - FourierHypergeometric.invJoukowski x ^ 2)^μ *
        FourierHypergeometric.invJoukowski x ^ (ν + k) *
      regularizedGaussHGFun (μ+1/2) ((ν+μ)+k) ((ν+1/2)+k)
          (FourierHypergeometric.invJoukowski x ^ 2) := by
  have hz := LaplaceIntegrals.one_lt_mem hx
  have h2 : ‖FourierHypergeometric.invJoukowski x ^ 2‖ < 1 := by
    rw [norm_pow]; have := FourierHypergeometric.norm_invJoukowski_lt_one hz
    nlinarith [norm_nonneg (FourierHypergeometric.invJoukowski x)]
  rw [ContinuedFraction.backwardQ, OlverQZetaForm.olverQ_eq_rhs _ _ hz, OlverQZetaForm.rhs,
      regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ h2]
  congr 2 <;> ring_nf

/-- Eventually `0 < Re (c + k)`. -/
theorem ContinuedFraction.eventually_re_pos (c : ℂ) : ∀ᶠ k : ℕ in atTop, 0 < (c + k).re := by
  obtain ⟨K, hK⟩ := exists_nat_gt (-c.re)
  filter_upwards [eventually_ge_atTop K] with k hk
  have : (K:ℝ) ≤ k := by exact_mod_cast hk
  simp; linarith

/-- Eventually `c + k ≠ 0`. -/
theorem ContinuedFraction.eventually_ne (c : ℂ) : ∀ᶠ k : ℕ in atTop, c + k ≠ 0 := by
  filter_upwards [ContinuedFraction.eventually_re_pos c] with k hk h
  rw [h] at hk; simp at hk

/-- The ratio limit for the fraction 14.14.3: `-w_k/(a_{k+1}w_{k+2}) → ζ^{-2}`. -/
theorem ContinuedFraction.backwardQ_ratio (ν μ : ℂ) {x : ℝ} (hx : 1 < x) :
    Tendsto (fun k => -(ContinuedFraction.backwardQ ν μ x k /
      (legendreQCFNum ν μ (k+1) * ContinuedFraction.backwardQ ν μ x (k+2)))) atTop
      (𝓝 ((FourierHypergeometric.invJoukowski x ^ 2)⁻¹)) ∧ ∀ᶠ k in atTop,
          ContinuedFraction.backwardQ ν μ x k ≠ 0 := by
  have hz := LaplaceIntegrals.one_lt_mem hx
  set ζ := FourierHypergeometric.invJoukowski x with hζ
  have hζ0 : ζ ≠ 0 := FourierHypergeometric.invJoukowski_ne_zero hz
  have h2 : ‖ζ ^ 2‖ < 1 := by
    rw [norm_pow]; have := FourierHypergeometric.norm_invJoukowski_lt_one hz
    nlinarith [norm_nonneg ζ]
  set F : ℕ → ℂ := fun k => Gamma ((ν+1/2)+k) *
    regularizedGaussHGFun (μ+1/2) ((ν+μ)+k) ((ν+1/2)+k) (ζ^2) with hFdef
  set L : ℂ := (1 - ζ^2)^(-(μ+1/2)) with hLdef
  have h1z : 1 - ζ^2 ≠ 0 := fun h => by
    have : ζ^2 = 1 := by linear_combination -h
    rw [this, norm_one] at h2; exact lt_irrefl _ h2
  have hL : L ≠ 0 := by rw [hLdef, cpow_def_of_ne_zero h1z]; exact exp_ne_zero _
  have hF : Tendsto F atTop (𝓝 L) := TanneryLimit.tannery _ _ _ h2
  have hF2 : Tendsto (fun k => F (k+2)) atTop (𝓝 L) := hF.comp (tendsto_add_atTop_nat 2)
  have hFne : ∀ᶠ k in atTop, F k ≠ 0 := hF.eventually_ne hL
  set C : ℂ := Real.sqrt π * (1 - ζ^2)^μ with hC
  have hC0 : C ≠ 0 := by
    refine mul_ne_zero (by exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne') ?_
    rw [cpow_def_of_ne_zero h1z]; exact exp_ne_zero _
  -- the closed forms of `w_k`, `w_{k+2}`
  have hw : ∀ k : ℕ, 0 < ((ν+1/2)+k).re → ContinuedFraction.backwardQ ν μ x k =
      C * ζ^(ν+k) * (F k / Gamma ((ν+1/2)+k)) := by
    intro k hk
    rw [ContinuedFraction.backwardQ_eq ν μ hx k, hFdef]
    simp only
    rw [mul_div_cancel_left₀ _ (Gamma_ne_zero_of_re_pos hk)]
  have hw2 : ∀ k : ℕ, 0 < ((ν+1/2)+k).re → ContinuedFraction.backwardQ ν μ x (k+2) =
      C * ζ^(ν+k) * ζ^2 * (F (k+2) / (((ν+1/2)+k+1) * ((ν+1/2)+k) * Gamma ((ν+1/2)+k))) := by
    intro k hk
    have hk2 : 0 < ((ν+1/2)+((k+2:ℕ):ℂ)).re := by
      have : ((ν+1/2)+((k+2:ℕ):ℂ)).re = ((ν+1/2)+k).re + 2 := by simp; ring
      linarith
    rw [hw (k+2) hk2]
    have hs0 : (ν+1/2)+k ≠ 0 := fun h => by rw [h] at hk; simp at hk
    have hs1 : (ν+1/2)+k+1 ≠ 0 := fun h => by
      have h' := congrArg re h; simp at h' hk; linarith
    have eG : Gamma ((ν+1/2)+((k+2:ℕ):ℂ)) =
        ((ν+1/2)+k+1) * ((ν+1/2)+k) * Gamma ((ν+1/2)+k) := by
      rw [show (ν+1/2)+((k+2:ℕ):ℂ) = ((ν+1/2)+k+1)+1 by push_cast; ring, Gamma_add_one _ hs1,
        Gamma_add_one _ hs0]; ring
    have eZ : ζ^(ν+((k+2:ℕ):ℂ)) = ζ^(ν+k) * ζ^2 := by
      rw [show ν+((k+2:ℕ):ℂ) = (ν+k) + ((2:ℕ):ℂ) by push_cast; ring, cpow_add _ _ hζ0,
        cpow_natCast]
    rw [eG, eZ]; ring
  have hlimit : Tendsto (fun k : ℕ => (ζ^2)⁻¹ * (F k / F (k+2)) *
      (((k:ℂ)+(ν+1/2))/((k:ℂ)+(ν+μ+1))) * (((k:ℂ)+(ν+3/2))/((k:ℂ)+(ν-μ+1)))) atTop
      (𝓝 ((ζ^2)⁻¹)) := by
    have := ((tendsto_const_nhds (x := (ζ^2)⁻¹)).mul (hF.div hF2 hL)).mul
      (TanneryLimit.ratio_tendsto (ν+1/2) (ν+μ+1)) |>.mul
          (TanneryLimit.ratio_tendsto (ν+3/2) (ν-μ+1))
    rwa [div_self hL, mul_one, mul_one, mul_one] at this
  constructor
  · refine hlimit.congr' ?_
    filter_upwards [ContinuedFraction.eventually_re_pos (ν+1/2), hFne, hF2.eventually_ne hL,
      ContinuedFraction.eventually_ne (ν+μ+1),
          ContinuedFraction.eventually_ne (ν-μ+1)] with k hk hFk hFk2 hp hq
    rw [hw k hk, hw2 k hk]
    have hG := Gamma_ne_zero_of_re_pos hk
    generalize Gamma ((ν+1/2)+k) = G at hG ⊢
    have hs0 : (ν+1/2)+k ≠ 0 := fun h => by rw [h] at hk; simp at hk
    have hs1 : (ν+1/2)+k+1 ≠ 0 := fun h => by
      have h' := congrArg re h; simp at h' hk; linarith
    have hP : ζ^(ν+k) ≠ 0 := by rw [cpow_def_of_ne_zero hζ0]; exact exp_ne_zero _
    have hp' : (k:ℂ)+(ν+μ+1) ≠ 0 := by rwa [add_comm]
    have hq' : (k:ℂ)+(ν-μ+1) ≠ 0 := by rwa [add_comm]
    simp only [legendreQCFNum, Nat.add_one_ne_zero, ite_false]
    push_cast
    have hp'' : ν+μ+(k+1) ≠ 0 := by rw [show ν+μ+((k:ℂ)+1) = ν+μ+1+k by ring]; exact hp
    have hq'' : ν-μ+(k+1) ≠ 0 := by rw [show ν-μ+((k:ℂ)+1) = ν-μ+1+k by ring]; exact hq
    field_simp
    ring
  · filter_upwards [ContinuedFraction.eventually_re_pos (ν+1/2), hFne] with k hk hFk
    rw [hw k hk]
    have hP : ζ^(ν+k) ≠ 0 := by rw [cpow_def_of_ne_zero hζ0]; exact exp_ne_zero _
    exact mul_ne_zero (mul_ne_zero hC0 hP) (div_ne_zero hFk (Gamma_ne_zero_of_re_pos hk))

/-! ### Tools for the continued fraction 14.14.1 -/

/-- For real `x > 1`, `log (x-1) - log (x+1)` is the real logarithm of `(x-1)/(x+1)`. -/
theorem ContinuedFraction.log_diff {x : ℝ} (hx : 1 < x) :
    exp (log ((x:ℂ)-1) - log ((x:ℂ)+1)) = (((x-1)/(x+1) : ℝ) : ℂ) := by
  rw [exp_sub, exp_log, exp_log]
  · push_cast; ring
  · exact_mod_cast (show (x:ℝ)+1 ≠ 0 by linarith)
  · rw [sub_ne_zero]; exact_mod_cast (show (x:ℝ) ≠ 1 by linarith)

/-- For real `x > 1`, `(z²-1)^{-1/2}` at `z = x` is `1/√(x²-1)`. -/
theorem ContinuedFraction.branch_neg_one {x : ℝ} (hx : 1 < x) :
    legendreBranchPower (-1) x = (((Real.sqrt (x^2-1))⁻¹ : ℝ) : ℂ) := by
  have hy : 0 < x^2 - 1 := by nlinarith
  have hl : log ((x:ℂ)-1) + log ((x:ℂ)+1) = ((Real.log (x^2-1) : ℝ) : ℂ) := by
    rw [show (x:ℂ)-1 = ((x-1:ℝ):ℂ) by push_cast; ring, show (x:ℂ)+1 =
                                        ((x+1:ℝ):ℂ) by push_cast; ring,
      ← ofReal_log (by linarith), ← ofReal_log (by linarith), ← ofReal_add,
      ← Real.log_mul (by linarith) (by linarith)]
    congr 2; ring
  have hs : (Real.sqrt (x^2-1))⁻¹ = Real.exp (-1/2 * Real.log (x^2-1)) := by
    rw [show -1/2 * Real.log (x^2-1) = -Real.log (Real.sqrt (x^2-1)) by
      rw [Real.log_sqrt hy.le]; ring, Real.exp_neg, Real.exp_log (Real.sqrt_pos.mpr hy)]
  rw [legendreBranchPower, hl, hs, ofReal_exp]
  push_cast; ring_nf

/-- The scale `2/√(x²-1)` of the backward solution of 14.14.1. -/
def ContinuedFraction.scaleP (x : ℝ) : ℂ := ((2 / Real.sqrt (x^2-1) : ℝ) : ℂ)

/-- `(2/√(x²-1))² (x²-1)/4 = 1`. -/
theorem ContinuedFraction.scaleP_sq {x : ℝ} (hx : 1 < x) : ContinuedFraction.scaleP x ^ 2 *
    ((x:ℂ)^2-1) / 4 = 1 := by
  have hy : 0 < x^2 - 1 := by nlinarith
  have hs := Real.sq_sqrt hy.le
  have hs0 := (Real.sqrt_pos.mpr hy).ne'
  rw [ContinuedFraction.scaleP, show ((x:ℂ)^2-1) = ((x^2-1:ℝ):ℂ) by push_cast; ring]
  rw [← ofReal_pow, ← ofReal_mul, ← ofReal_ofNat, ← ofReal_div]
  rw [ofReal_eq_one, div_pow, hs]; field_simp; norm_num

/-- The backward solution `w_k = (2/√(x²-1))^k P^{1-μ-k}_ν(x)` of the fraction 14.14.1. -/
def ContinuedFraction.backwardP (ν μ : ℂ) (x : ℝ) (k : ℕ) : ℂ := ContinuedFraction.scaleP x ^ k *
    associatedP ν (1 - μ - k) x

/-- `w_k` solves the backward recurrence of 14.14.1 (from DLMF 14.10.6). -/
theorem ContinuedFraction.backwardP_recurrence (ν μ : ℂ) {x : ℝ} (hx : 1 < x) (k : ℕ) :
    ContinuedFraction.backwardP ν μ x k = legendrePCFDen μ x k *
        ContinuedFraction.backwardP ν μ x (k+1) +
      legendrePCFNum ν μ x (k+1) * ContinuedFraction.backwardP ν μ x (k+2) := by
  have R := associatedP_recurrence_6 ν (-μ-k-1) (LaplaceIntegrals.one_lt_mem hx)
  rw [ContinuedFraction.branch_neg_one hx, show -μ-k-1+2 = 1-μ-k by ring,
    show -μ-k-1+1 = 1-μ-((k+1:ℕ):ℂ) by push_cast; ring,
    show -μ-(k:ℂ)-1 = 1-μ-((k+2:ℕ):ℂ) by push_cast; ring] at R
  have hc := ContinuedFraction.scaleP_sq hx
  have hcB : (((Real.sqrt (x^2-1))⁻¹ : ℝ) : ℂ) = ContinuedFraction.scaleP x / 2 := by
    rw [ContinuedFraction.scaleP]; push_cast; ring
  rw [hcB] at R
  simp only [ContinuedFraction.backwardP, legendrePCFDen, legendrePCFNum]
  generalize associatedP ν (1-μ-((k+1:ℕ):ℂ)) x = p1 at R ⊢
  generalize associatedP ν (1-μ-((k+2:ℕ):ℂ)) x = p2 at R ⊢
  generalize associatedP ν (1-μ-k) x = p0 at R ⊢
  push_cast at R ⊢
  linear_combination (ContinuedFraction.scaleP x ^ k) * R -
      (ContinuedFraction.scaleP x ^ k * (ν-μ-k) * (ν+μ+k+1) * p2) * hc

/-- The Pfaff argument `t = z₀/(z₀-1) = (x-1)/(x+1)` for `z₀ = (1-x)/2`. -/
theorem ContinuedFraction.pfaff_arg {x : ℝ} (hx : 1 < x) :
    (1-(x:ℂ))/2 / ((1-(x:ℂ))/2 - 1) = (((x-1)/(x+1) : ℝ) : ℂ) := by
  have h1 : (x:ℂ)+1 ≠ 0 := by exact_mod_cast (show x+1 ≠ 0 by linarith)
  push_cast
  rw [div_eq_div_iff (by intro h; apply h1; linear_combination -2*h) h1]
  ring

/-- `0 < (x-1)/(x+1) < 1` for `x > 1`. -/
theorem ContinuedFraction.pfaff_arg_bounds {x : ℝ} (hx : 1 < x) : 0 < (x-1)/(x+1) ∧
    (x-1)/(x+1) < 1 := by
  constructor
  · exact div_pos (by linarith) (by linarith)
  · rw [div_lt_one (by linarith)]; linarith

/-- The hypergeometric form of `w_k` via 14.3.9 and Pfaff's transformation. -/
theorem ContinuedFraction.backwardP_eq (ν μ : ℂ) {x : ℝ} (hx : 1 < x) (k : ℕ) :
    ContinuedFraction.backwardP ν μ x k = ContinuedFraction.scaleP x ^ k *
        exp ((μ+k-1)/2*(log ((x:ℂ)-1) - log ((x:ℂ)+1))) *
      (1-(1-(x:ℂ))/2)^(-(-ν)) *
      regularizedGaussHGFun (-ν) ((μ-ν-1)+k) (μ+k) (((x-1)/(x+1) : ℝ) : ℂ) := by
  have hz := LaplaceIntegrals.one_lt_mem hx
  have hcut : (1-(x:ℂ))/2 ∈ cutPlane := by
    rw [mem_cutPlane, show 1-(1-(x:ℂ))/2 = (((x+1)/2 : ℝ) : ℂ) by push_cast; ring]
    exact ofReal_mem_slitPlane.mpr (by linarith)
  have ht : ‖(((x-1)/(x+1) : ℝ) : ℂ)‖ < 1 := by
    obtain ⟨h0, h1⟩ := ContinuedFraction.pfaff_arg_bounds hx
    rw [Complex.norm_real, Real.norm_of_nonneg h0.le]; exact h1
  have e9 := associated_hypergeometric_9 ν (μ+k-1) (z := (x:ℂ))
  rw [show -(μ+(k:ℂ)-1) = 1-μ-k by ring, show μ+(k:ℂ)-1+1 = μ+k by ring] at e9
  rw [ContinuedFraction.backwardP, e9, regularizedGaussHG_symm _ _ _ hcut,
      regularizedGaussHG_pfaff _ _ _ hcut,
    ContinuedFraction.pfaff_arg hx, regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ ht]
  rw [show μ+(k:ℂ)-(ν+1) = (μ-ν-1)+k by ring]
  ring

/-- The ratio limit for the fraction 14.14.1: `-w_k/(a_{k+1}w_{k+2}) → (x+1)/(x-1)`. -/
theorem ContinuedFraction.backwardP_ratio (ν μ : ℂ) {x : ℝ} (hx : 1 < x) :
    Tendsto (fun k => -(ContinuedFraction.backwardP ν μ x k /
      (legendrePCFNum ν μ x (k+1) * ContinuedFraction.backwardP ν μ x (k+2)))) atTop
      (𝓝 ((exp (log ((x:ℂ)-1) - log ((x:ℂ)+1)))⁻¹)) ∧ ∀ᶠ k in atTop,
          ContinuedFraction.backwardP ν μ x k ≠ 0 := by
  set ℓ := log ((x:ℂ)-1) - log ((x:ℂ)+1) with hℓ
  set t : ℂ := (((x-1)/(x+1) : ℝ) : ℂ) with htdef
  have ht : ‖t‖ < 1 := by
    obtain ⟨h0, h1⟩ := ContinuedFraction.pfaff_arg_bounds hx
    rw [htdef, Complex.norm_real, Real.norm_of_nonneg h0.le]; exact h1
  set G : ℕ → ℂ := fun k => Gamma (μ+k) * regularizedGaussHGFun (-ν) ((μ-ν-1)+k) (μ+k) t
    with hGdef
  set L : ℂ := (1-t)^(-(-ν)) with hLdef
  have h1t : 1 - t ≠ 0 := fun h => by
    have : t = 1 := by linear_combination -h
    rw [this, norm_one] at ht; exact lt_irrefl _ ht
  have hL : L ≠ 0 := by rw [hLdef, cpow_def_of_ne_zero h1t]; exact exp_ne_zero _
  have hG : Tendsto G atTop (𝓝 L) := TanneryLimit.tannery _ _ _ ht
  have hG2 : Tendsto (fun k => G (k+2)) atTop (𝓝 L) := hG.comp (tendsto_add_atTop_nat 2)
  set K0 : ℂ := (1-(1-(x:ℂ))/2)^(-(-ν)) with hK0
  have hK00 : K0 ≠ 0 := by
    rw [hK0, cpow_def_of_ne_zero]; · exact exp_ne_zero _
    rw [show 1-(1-(x:ℂ))/2 = (((x+1)/2 : ℝ) : ℂ) by push_cast; ring]
    exact_mod_cast (show (x+1)/2 ≠ 0 by linarith)
  have hy : 0 < x^2 - 1 := by nlinarith
  have hc0 : ContinuedFraction.scaleP x ≠ 0 := by
    rw [ContinuedFraction.scaleP]; exact_mod_cast (div_pos two_pos (Real.sqrt_pos.mpr hy)).ne'
  have hx2 : (x:ℂ)^2 - 1 ≠ 0 := by exact_mod_cast hy.ne'
  have hc2 : ContinuedFraction.scaleP x ^ 2 = 4 / ((x:ℂ)^2-1) := by
    rw [eq_div_iff hx2]; linear_combination 4 * ContinuedFraction.scaleP_sq hx
  have hw : ∀ k : ℕ, 0 < (μ+k).re → ContinuedFraction.backwardP ν μ x k =
      ContinuedFraction.scaleP x ^ k * exp ((μ+k-1)/2*ℓ) * K0 * (G k / Gamma (μ+k)) := by
    intro k hk
    rw [ContinuedFraction.backwardP_eq ν μ hx k, hGdef]
    simp only
    rw [mul_div_cancel_left₀ _ (Gamma_ne_zero_of_re_pos hk)]
  have hw2 : ∀ k : ℕ, 0 < (μ+k).re → ContinuedFraction.backwardP ν μ x (k+2) =
      ContinuedFraction.scaleP x ^ k * ContinuedFraction.scaleP x ^ 2 *
          (exp ((μ+k-1)/2*ℓ) * exp ℓ) * K0 *
        (G (k+2) / ((μ+k+1) * (μ+k) * Gamma (μ+k))) := by
    intro k hk
    have hk2 : 0 < (μ+((k+2:ℕ):ℂ)).re := by
      have : (μ+((k+2:ℕ):ℂ)).re = (μ+k).re + 2 := by simp; ring
      linarith
    rw [hw (k+2) hk2]
    have hs0 : μ+k ≠ 0 := fun h => by rw [h] at hk; simp at hk
    have hs1 : μ+k+1 ≠ 0 := fun h => by
      have h' := congrArg re h; simp at h' hk; linarith
    have eG : Gamma (μ+((k+2:ℕ):ℂ)) = (μ+k+1) * (μ+k) * Gamma (μ+k) := by
      rw [show μ+((k+2:ℕ):ℂ) = (μ+k+1)+1 by push_cast; ring, Gamma_add_one _ hs1,
        Gamma_add_one _ hs0]; ring
    have eX : exp ((μ+((k+2:ℕ):ℂ)-1)/2*ℓ) = exp ((μ+k-1)/2*ℓ) * exp ℓ := by
      rw [← exp_add]; congr 1; push_cast; ring
    rw [eG, eX, pow_add]
  have hlimit : Tendsto (fun k : ℕ => (exp ℓ)⁻¹ * (G k / G (k+2)) *
      (((k:ℂ)+μ)/((k:ℂ)+(μ-ν))) * (((k:ℂ)+(μ+1))/((k:ℂ)+(ν+μ+1)))) atTop
      (𝓝 ((exp ℓ)⁻¹)) := by
    have := ((tendsto_const_nhds (x := (exp ℓ)⁻¹)).mul (hG.div hG2 hL)).mul
      (TanneryLimit.ratio_tendsto μ (μ-ν)) |>.mul (TanneryLimit.ratio_tendsto (μ+1) (ν+μ+1))
    rwa [div_self hL, mul_one, mul_one, mul_one] at this
  constructor
  · refine hlimit.congr' ?_
    filter_upwards [ContinuedFraction.eventually_re_pos μ, hG.eventually_ne hL,
        hG2.eventually_ne hL,
      ContinuedFraction.eventually_ne (μ-ν),
          ContinuedFraction.eventually_ne (ν+μ+1)] with k hk hGk hGk2 hp hq
    rw [hw k hk, hw2 k hk, hc2]
    have hΓ := Gamma_ne_zero_of_re_pos hk
    generalize Gamma (μ+k) = Γk at hΓ ⊢
    have hs0 : μ+k ≠ 0 := fun h => by rw [h] at hk; simp at hk
    have hs1 : μ+k+1 ≠ 0 := fun h => by
      have h' := congrArg re h; simp at h' hk; linarith
    have hp' : (k:ℂ)+(μ-ν) ≠ 0 := by rwa [add_comm]
    have hq' : (k:ℂ)+(ν+μ+1) ≠ 0 := by rwa [add_comm]
    have hp'' : ν-μ-((k:ℂ)+1)+1 ≠ 0 := fun h => hp (by linear_combination -h)
    have hq'' : ν+μ+((k:ℂ)+1) ≠ 0 := fun h => hq (by linear_combination h)
    have he := exp_ne_zero ℓ
    have hX := exp_ne_zero ((μ+k-1)/2*ℓ)
    have hck : ContinuedFraction.scaleP x ^ k ≠ 0 := pow_ne_zero _ hc0
    simp only [legendrePCFNum]
    push_cast
    field_simp
    ring
  · filter_upwards [ContinuedFraction.eventually_re_pos μ, hG.eventually_ne hL] with k hk hGk
    rw [hw k hk]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hc0) (exp_ne_zero _)) hK00)
      (div_ne_zero hGk (Gamma_ne_zero_of_re_pos hk))

/-- `(2/√(x²-1)) (x²-1)/4 = √(x²-1)/2`. -/
theorem ContinuedFraction.scaleP_mul {x : ℝ} (hx : 1 < x) :
    ContinuedFraction.scaleP x * ((x:ℂ)^2-1) / 4 = (Real.sqrt (x^2-1) : ℂ) / 2 := by
  have hy : 0 < x^2 - 1 := by nlinarith
  have hs := Real.sq_sqrt hy.le
  have hs0 := (Real.sqrt_pos.mpr hy).ne'
  rw [ContinuedFraction.scaleP, show ((x:ℂ)^2-1) = ((x^2-1:ℝ):ℂ) by push_cast; ring]
  rw [← ofReal_mul, ← ofReal_ofNat, ← ofReal_div, ← ofReal_ofNat 2, ← ofReal_div, ofReal_inj]
  field_simp
  rw [hs]; ring

/-- associatedP continued fraction, DLMF 14.14.1 corrected.

DLMF 14.14.1 states that the continued fraction with elements 14.14.2 equals
`½(x²-1)^{1/2} P^μ_ν(x)/P^{μ-1}_ν(x)`. That is false: the fraction comes from the order
recurrence 14.10.6, and it converges to the ratio of the recurrence's minimal solution
`w(μ) = Γ(ν+μ+1) P^{-μ}_ν(x)/Γ(ν-μ+1)`, whereas `P^μ_ν` is dominant. The corrected value is
`½(x²-1)^{1/2} (ν+μ)(ν-μ+1) P^{-μ}_ν(x)/P^{1-μ}_ν(x)`. At `(ν, μ, x) = (0.3, 0.4, 1.5)` the
fraction is `0.345161187628545…`, the printed right side `0.812720708269563…`, and the corrected
value agrees with the fraction to 30 digits (also checked at complex `ν`, `μ`). DLMF erratum.

Proof: `w_k = (2/√(x²-1))^k P^{1-μ-k}_ν(x)` is a backward solution (14.10.6); by 14.3.9,
Pfaff's transformation and the Tannery limit `TanneryLimit.tannery`, `-w_k/(a_{k+1}w_{k+2}) →
(x+1)/(x-1) > 1`, so Pincherle's criterion `GenContFract.tendsto_ofFun_convs_of_tendsto_ratio`
applies; a vanishing partial numerator terminates the fraction at the same value. The hypothesis
`hterm` is not needed (stronger than DLMF). -/
@[dlmf 14.14.E1 "source erratum: the limit is the minimal-solution ratio \
    (ν+μ)(ν-μ+1)P^{-μ}/P^{1-μ}"]
theorem associatedP_continued_fraction (ν μ : ℂ) {x : ℝ} (hx : 1 < x)
    (hnz : associatedP ν (1-μ) x ≠ 0) :
    HasContinuedFraction (legendrePCFNum ν μ x) (legendrePCFDen μ x)
        (Real.sqrt (x^2-1)/2*((ν+μ)*(ν-μ+1))*associatedP ν (-μ) x/associatedP ν (1-μ) x) := by
  -- the hypothesis `hterm` is not needed (stronger than DLMF)
  have hw0 : ContinuedFraction.backwardP ν μ x 0 ≠ 0 := by
      simpa [ContinuedFraction.backwardP] using hnz
  have hval : legendrePCFNum ν μ x 0 * ContinuedFraction.backwardP ν μ x 1 /
      ContinuedFraction.backwardP ν μ x 0 =
      Real.sqrt (x^2-1)/2*((ν+μ)*(ν-μ+1))*associatedP ν (-μ) x/associatedP ν (1-μ) x := by
    have e1 : ContinuedFraction.backwardP ν μ x 1 = ContinuedFraction.scaleP x *
        associatedP ν (-μ) x := by
      simp [ContinuedFraction.backwardP, show (1:ℂ)-μ-1 = -μ by ring]
    have e0 : ContinuedFraction.backwardP ν μ x 0 = associatedP ν (1-μ) x := by
        simp [ContinuedFraction.backwardP]
    rw [e1, e0, ← ContinuedFraction.scaleP_mul hx]
    simp only [legendrePCFNum, Nat.cast_zero, sub_zero, add_zero]
    ring
  rw [← hval]
  by_cases hall : ∀ k, legendrePCFNum ν μ x k ≠ 0
  · obtain ⟨hlim, hev⟩ := ContinuedFraction.backwardP_ratio ν μ hx
    refine ContinuedFraction.hasContinuedFraction_of_ratio hall
        (ContinuedFraction.backwardP_recurrence ν μ hx) hw0 hev ?_ hlim
    obtain ⟨h0, h1⟩ := ContinuedFraction.pfaff_arg_bounds hx
    rw [ContinuedFraction.log_diff hx, norm_inv, Complex.norm_real, Real.norm_of_nonneg h0.le,
      one_lt_inv₀ h0]
    exact h1
  · push Not at hall
    exact ContinuedFraction.hasContinuedFraction_of_exists_zero hall
        (ContinuedFraction.backwardP_recurrence ν μ hx) hw0

/-- associatedQ continued fraction.

Proof: `w_k = 𝑸^μ_{ν+k-1}(x)` is a backward solution (14.10.3); from
`𝑸^μ_ν(x) = √π (1-ζ²)^μ ζ^{ν+1} 𝐅(μ+1/2, ν+μ+1; ν+3/2; ζ²)`, `ζ = x - √(x²-1)`, and the Tannery
limit `TanneryLimit.tannery`, `-w_k/(a_{k+1}w_{k+2}) → ζ^{-2} > 1`, so Pincherle's criterion
`GenContFract.tendsto_ofFun_convs_of_tendsto_ratio` applies; a vanishing partial numerator
terminates the fraction at the same value. The hypotheses `hr` and `hterm` are not needed (stronger
than DLMF). -/
@[dlmf 14.14.E3]
theorem associatedQ_continued_fraction {ν μ : ℂ} (hne : ν ≠ μ) {x : ℝ} (hx : 1 < x)
    (hnz : associatedQ (ν-1) μ x ≠ 0) :
    HasContinuedFraction (legendreQCFNum ν μ) (legendreQCFDen ν x)
        ((ν-μ)*associatedQ ν μ x/associatedQ (ν-1) μ x) := by
  -- the hypotheses `hr` and `hterm` are not needed (stronger than DLMF)
  have hz := LaplaceIntegrals.one_lt_mem hx
  have hQ1 : associatedQ (ν-1) μ x = exp (μ*π*I) * Gamma (ν+μ) * olverQ (ν-1) μ x := by
    rw [associatedQ, show ν-1+μ+1 = ν+μ by ring]
  have hΓ : Gamma (ν+μ) ≠ 0 := fun h => hnz (by rw [hQ1, h, mul_zero, zero_mul])
  have hνμ : ν+μ ≠ 0 := fun h => hΓ (by rw [h, Gamma_zero])
  have hO : olverQ (ν-1) μ x ≠ 0 := fun h => hnz (by rw [hQ1, h, mul_zero])
  have hw0 : ContinuedFraction.backwardQ ν μ x 0 ≠ 0 := by
      simpa [ContinuedFraction.backwardQ] using hO
  have hval : legendreQCFNum ν μ 0 * ContinuedFraction.backwardQ ν μ x 1 /
      ContinuedFraction.backwardQ ν μ x 0 =
      (ν-μ)*associatedQ ν μ x/associatedQ (ν-1) μ x := by
    have e1 : ContinuedFraction.backwardQ ν μ x 1 = olverQ ν μ x := by
        simp [ContinuedFraction.backwardQ]
    have e0 : ContinuedFraction.backwardQ ν μ x 0 = olverQ (ν-1) μ x := by
        simp [ContinuedFraction.backwardQ]
    have hG : Gamma (ν+μ+1) = (ν+μ) * Gamma (ν+μ) := Gamma_add_one _ hνμ
    rw [e1, e0, hQ1, associatedQ, hG]
    simp only [legendreQCFNum, ↓reduceIte, Nat.cast_zero, add_zero, one_mul]
    field_simp
  rw [← hval]
  by_cases hall : ∀ k, legendreQCFNum ν μ k ≠ 0
  · obtain ⟨hlim, hev⟩ := ContinuedFraction.backwardQ_ratio ν μ hx
    have hζ0 := FourierHypergeometric.invJoukowski_ne_zero hz
    have hζ1 := FourierHypergeometric.norm_invJoukowski_lt_one hz
    refine ContinuedFraction.hasContinuedFraction_of_ratio hall
        (ContinuedFraction.backwardQ_recurrence ν μ hx) hw0 hev ?_ hlim
    rw [norm_inv, norm_pow]
    have hpos : 0 < ‖FourierHypergeometric.invJoukowski x‖ := norm_pos_iff.mpr hζ0
    rw [one_lt_inv₀ (by positivity)]
    nlinarith
  · push Not at hall
    have h0 : legendreQCFNum ν μ 0 ≠ 0 := by
      simp only [legendreQCFNum, ↓reduceIte, Nat.cast_zero, add_zero, one_mul]
      exact mul_ne_zero hνμ (sub_ne_zero.mpr hne)
    classical
    have hK := Nat.find_spec hall
    have hK1 : 1 ≤ Nat.find hall := by
      rcases Nat.eq_zero_or_pos (Nat.find hall) with h | h
      · rw [h] at hK; exact absurd hK h0
      · exact h
    exact ContinuedFraction.hasContinuedFraction_of_terminating hK1
        (fun k _ hk => Nat.find_min hall hk) hK
      (ContinuedFraction.backwardQ_recurrence ν μ hx) hw0

/-- DLMF 14.13: outside the central angle, this Fourier series is not absolutely convergent. -/
theorem ferrersP_fourier_not_absolute {ν μ : ℂ}
    (hμ0 : 0 ≤ μ.re) {θ : ℝ}
    (h0 : 0 < θ) (hπ : θ < π) (hmid : θ ≠ π/2) :
    ¬Summable (fun k : ℕ => ‖Gamma (ν+μ+k+1)/Gamma (ν+k+3/2)*poch (μ+1/2) k/
      (k.factorial:ℂ)*sin ((ν+μ+2*k+1)*θ)‖) := by
  refine FerrersFourier.not_summable hμ0 _
      (half_pos (FerrersFourier.sin_two_mul_ne h0 hπ hmid)) fun k => ?_
  have hre : ∀ j : ℕ, ((ν+μ+2*(j:ℂ)+1)*(θ:ℂ)).re = (ν+μ+1).re*θ + 2*j*θ := by
    intro j; simp [mul_re]; ring
  refine (FerrersFourier.sin_pair (θ := θ) ((ν+μ+1).re*θ + 2*k*θ)).trans (add_le_add ?_ ?_)
  · have := FerrersFourier.abs_sin_re_le ((ν+μ+2*(k:ℂ)+1)*(θ:ℂ))
    rwa [hre] at this
  · have := FerrersFourier.abs_sin_re_le ((ν+μ+2*((k+1:ℕ):ℂ)+1)*(θ:ℂ))
    rw [hre] at this
    convert this using 3
    push_cast; ring

/-- DLMF 14.13: the analogous second-kind Fourier series converges only conditionally. -/
theorem ferrersQ_fourier_not_absolute {ν μ : ℂ}
    (hμ0 : 0 ≤ μ.re) {θ : ℝ}
    (h0 : 0 < θ) (hπ : θ < π) (hmid : θ ≠ π/2) :
    ¬Summable (fun k : ℕ => ‖Gamma (ν+μ+k+1)/Gamma (ν+k+3/2)*poch (μ+1/2) k/
      (k.factorial:ℂ)*cos ((ν+μ+2*k+1)*θ)‖) := by
  refine FerrersFourier.not_summable hμ0 _
      (half_pos (FerrersFourier.sin_two_mul_ne h0 hπ hmid)) fun k => ?_
  have hre : ∀ j : ℕ, ((ν+μ+2*(j:ℂ)+1)*(θ:ℂ)).re = (ν+μ+1).re*θ + 2*j*θ := by
    intro j; simp [mul_re]; ring
  refine (FerrersFourier.cos_pair (θ := θ) ((ν+μ+1).re*θ + 2*k*θ)).trans (add_le_add ?_ ?_)
  · have := FerrersFourier.abs_cos_re_le ((ν+μ+2*(k:ℂ)+1)*(θ:ℂ))
    rwa [hre] at this
  · have := FerrersFourier.abs_cos_re_le ((ν+μ+2*((k+1:ℕ):ℂ)+1)*(θ:ℂ))
    rw [hre] at this
    convert this using 3
    push_cast; ring

/-- Unnumbered combined hypergeometric Fourier representation in DLMF 14.13. -/
theorem ferrersPQ_fourier_hypergeometric (ν μ : ℂ) (hr : LegendreQRegular ν μ)
    {θ : ℝ} (h0 : 0 < θ) (hπ : θ < π) (s : ℂ) (hs : s=1 ∨ s=-1) :
    s*π*I/2*ferrersP ν μ (Real.cos θ)+ferrersQ ν μ (Real.cos θ)=
      Real.sqrt π*Gamma (ν+μ+1)*(2*Real.sin θ:ℂ)^μ*exp (s*(ν+μ+1)*I*θ)*
        regularizedGaussHG (ν+μ+1) (μ+1/2) (ν+3/2) (exp (s*2*I*θ)) := by
  rcases hs with rfl | rfl
  · have h := FourierHypergeometric.PQ_hypergeometric ν μ hr h0 hπ (s := 1) (Or.inl rfl);
        simp only [ofReal_one] at h; exact h
  · have h := FourierHypergeometric.PQ_hypergeometric ν μ hr h0 hπ (s := -1) (Or.inr rfl);
        simp only [ofReal_one, ofReal_neg] at h; exact h

end DLMF.Legendre
