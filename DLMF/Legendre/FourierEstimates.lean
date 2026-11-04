/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Legendre.FourierTools
public import DLMF.Legendre.SeriesTools
public import DLMF.Legendre.SpecialValues

/-!
# Estimates for the Ferrers Fourier series

Growth estimates behind the Fourier series of Ferrers functions (DLMF §14.13): bounds for Gamma
ratios and Pochhammer quotients, for `sin` and `cos` of complex argument, the absolute convergence
of the series for `Re μ < 0` and its failure for `Re μ ≥ 0`, and Dirichlet's test. The results
are used in `DLMF.Legendre.Series`.

## Main results

* `FerrersFourier.summable`, `FerrersFourier.not_summable`: absolute convergence of the Fourier
  series exactly for `Re μ < 0`.
* `FerrersFourier.dirichlet`: Dirichlet's test for series `∑ cₙ bₙ` with bounded partial sums
  of `bₙ` and `cₙ → 0` of bounded variation.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF
open scoped Real Topology Nat
open DLMF.Core

namespace DLMF.Legendre

/-- Eventual bound `‖Γ(k+a)/Γ(k+b)‖ ≤ 2 k^{Re(a-b)}` (from DLMF 5.11.12). -/
theorem FerrersFourier.gamma_ratio_le (a b : ℂ) :
    ∀ᶠ k : ℕ in atTop, ‖Gamma (k+a)/Gamma (k+b)‖ ≤ 2 * (k:ℝ)^((a-b).re) := by
  have h := (DLMF.Gamma.Gamma_ratio_power (a := a) (b := b)).comp tendsto_natCast_atTop_atTop
  have h2 := (h.norm).eventually (gt_mem_nhds (show ‖(1:ℂ)‖ < 2 by norm_num))
  filter_upwards [h2, eventually_gt_atTop 0] with k hk hk0
  simp only [Function.comp_apply, Complex.ofReal_natCast] at hk
  rw [norm_div, norm_natCast_cpow_of_pos hk0] at hk
  have hp : 0 < (k:ℝ)^((a-b).re) := Real.rpow_pos_of_pos (by exact_mod_cast hk0) _
  rw [div_lt_iff₀ hp] at hk
  exact hk.le

/-- Eventual bound `‖(a)_k/k!‖ ≤ C k^{Re a - 1}`. -/
theorem FerrersFourier.pochhammer_div_factorial_le (a : ℂ) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ᶠ k : ℕ in atTop, ‖pochhammer a k/(k.factorial:ℂ)‖ ≤ C * (k:ℝ)^(a.re-1) := by
  by_cases ha : ∃ m : ℕ, a = -m
  · obtain ⟨m, rfl⟩ := ha
    refine ⟨0, le_rfl, ?_⟩
    filter_upwards [eventually_gt_atTop m] with k hk
    simp [pochhammer, ascPochhammer_eval_neg_coe_nat_of_lt hk]
  · push Not at ha
    refine ⟨2/‖Gamma a‖, by positivity, ?_⟩
    filter_upwards [FerrersFourier.gamma_ratio_le a 1] with k hk
    have hG : Gamma a ≠ 0 := Gamma_ne_zero ha
    have e : pochhammer a k/(k.factorial:ℂ) = Gamma (k+a)/Gamma (k+1) / Gamma a := by
      rw [pochhammer, ← Gamma_add_nat_div_Gamma_eq a ha, ← Complex.Gamma_nat_eq_factorial,
        add_comm (k:ℂ) a]
      ring
    rw [e, norm_div]
    simp only [sub_re, one_re] at hk
    calc ‖Gamma (k+a)/Gamma (k+1)‖/‖Gamma a‖ ≤ 2 * (k:ℝ)^(a.re-1)/‖Gamma a‖ := by gcongr
      _ = _ := by ring

/-- `‖sin w‖ ≤ exp |Im w|`. -/
theorem FerrersFourier.norm_sin_le (w : ℂ) : ‖sin w‖ ≤ Real.exp |w.im| := by
  rw [Complex.sin]
  have h1 : ‖exp (-w * I)‖ ≤ Real.exp |w.im| := by
    rw [Complex.norm_exp]; simp only [mul_re, neg_re, I_re, mul_zero, neg_im, I_im, mul_one,
      zero_sub, neg_neg]
    exact Real.exp_le_exp.mpr (le_abs_self _)
  have h2 : ‖exp (w * I)‖ ≤ Real.exp |w.im| := by
    rw [Complex.norm_exp]; simp only [mul_re, I_re, mul_zero, I_im, mul_one, zero_sub]
    exact Real.exp_le_exp.mpr (neg_le_abs _)
  rw [norm_div, norm_mul, norm_I, mul_one, Complex.norm_two]
  have := norm_sub_le (exp (-w * I)) (exp (w * I))
  linarith

/-- `‖cos w‖ ≤ exp |Im w|`. -/
theorem FerrersFourier.norm_cos_le (w : ℂ) : ‖cos w‖ ≤ Real.exp |w.im| := by
  rw [Complex.cos]
  have h1 : ‖exp (w * I)‖ ≤ Real.exp |w.im| := by
    rw [Complex.norm_exp]; simp only [mul_re, I_re, mul_zero, I_im, mul_one, zero_sub]
    exact Real.exp_le_exp.mpr (neg_le_abs _)
  have h2 : ‖exp (-w * I)‖ ≤ Real.exp |w.im| := by
    rw [Complex.norm_exp]; simp only [mul_re, neg_re, I_re, mul_zero, neg_im, I_im, mul_one,
      zero_sub, neg_neg]
    exact Real.exp_le_exp.mpr (le_abs_self _)
  rw [norm_div, Complex.norm_two]
  have := norm_add_le (exp (w * I)) (exp (-w * I))
  linarith

/-- Absolute convergence of the Ferrers Fourier coefficients against bounded factors when
`Re μ < 0`: the coefficients are `O(k^{2 Re μ - 1})`. -/
theorem FerrersFourier.summable {ν μ : ℂ} (hμ : μ.re < 0) (s : ℕ → ℂ) {B : ℝ}
    (hs : ∀ k, ‖s k‖ ≤ B) :
    Summable (fun k : ℕ => ‖Gamma (ν+μ+k+1)/Gamma (ν+k+3/2)*pochhammer (μ+1/2) k/
      (k.factorial:ℂ)*s k‖) := by
  obtain ⟨C, hC, hP⟩ := FerrersFourier.pochhammer_div_factorial_le (μ+1/2)
  have hB : 0 ≤ B := (norm_nonneg _).trans (hs 0)
  refine Summable.of_norm_bounded_eventually_nat
    (g := fun k : ℕ => 2*C*B * (k:ℝ)^(2*μ.re-1))
    ((Real.summable_nat_rpow.mpr (by linarith)).mul_left _) ?_
  filter_upwards [FerrersFourier.gamma_ratio_le (ν+μ+1) (ν+3/2), hP, eventually_gt_atTop 0]
    with k hA hk hk0
  have e : Gamma (ν+μ+k+1)/Gamma (ν+k+3/2)*pochhammer (μ+1/2) k/(k.factorial:ℂ)*s k =
      Gamma (k+(ν+μ+1))/Gamma (k+(ν+3/2)) * (pochhammer (μ+1/2) k/(k.factorial:ℂ)) * s k := by
    rw [show ν+μ+k+1 = k+(ν+μ+1) by ring, show ν+k+3/2 = k+(ν+3/2) by ring]; ring
  have hre : (ν+μ+1-(ν+3/2)).re = μ.re - 1/2 := by simp; ring
  have hre2 : (μ+1/2).re - 1 = μ.re - 1/2 := by simp; ring
  rw [hre] at hA
  rw [hre2] at hk
  have hkp : (0:ℝ) < k := by exact_mod_cast hk0
  have hpow : (k:ℝ)^(2*μ.re-1) = (k:ℝ)^(μ.re-1/2) * (k:ℝ)^(μ.re-1/2) := by
    rw [← Real.rpow_add hkp]; ring_nf
  rw [norm_norm, e, norm_mul, norm_mul, hpow]
  have h0 : 0 ≤ (k:ℝ)^(μ.re-1/2) := (Real.rpow_pos_of_pos hkp _).le
  calc ‖Gamma (k+(ν+μ+1))/Gamma (k+(ν+3/2))‖ * ‖pochhammer (μ+1/2) k/(k.factorial:ℂ)‖ * ‖s k‖
      ≤ (2 * (k:ℝ)^(μ.re-1/2)) * (C * (k:ℝ)^(μ.re-1/2)) * B := by
        gcongr
        exact hs k
    _ = _ := by ring

/-- Eventual lower bound `‖Γ(k+a)/Γ(k+b)‖ ≥ k^{Re(a-b)}/2` (from DLMF 5.11.12). -/
theorem FerrersFourier.gamma_ratio_ge (a b : ℂ) :
    ∀ᶠ k : ℕ in atTop, (k:ℝ)^((a-b).re) / 2 ≤ ‖Gamma (k+a)/Gamma (k+b)‖ := by
  have h := (DLMF.Gamma.Gamma_ratio_power (a := a) (b := b)).comp tendsto_natCast_atTop_atTop
  have h2 := (h.norm).eventually (lt_mem_nhds (show (1/2:ℝ) < ‖(1:ℂ)‖ by norm_num))
  filter_upwards [h2, eventually_gt_atTop 0] with k hk hk0
  simp only [Function.comp_apply, Complex.ofReal_natCast] at hk
  rw [norm_div, norm_natCast_cpow_of_pos hk0] at hk
  have hp : 0 < (k:ℝ)^((a-b).re) := Real.rpow_pos_of_pos (by exact_mod_cast hk0) _
  rw [lt_div_iff₀ hp] at hk
  linarith

/-- Non-absolute convergence of the Ferrers Fourier coefficients against factors that are not
small at two consecutive indices, when `Re μ ≥ 0`. -/
theorem FerrersFourier.not_summable {ν μ : ℂ} (hμ : 0 ≤ μ.re) (s : ℕ → ℂ) {δ : ℝ} (hδ : 0 < δ)
    (hs : ∀ k, δ ≤ ‖s k‖ + ‖s (k+1)‖) :
    ¬Summable (fun k : ℕ => ‖Gamma (ν+μ+k+1)/Gamma (ν+k+3/2)*pochhammer (μ+1/2) k/
      (k.factorial:ℂ)*s k‖) := by
  intro hsum
  set a : ℕ → ℝ := fun k => ‖Gamma (ν+μ+k+1)/Gamma (ν+k+3/2)*pochhammer (μ+1/2) k/
      (k.factorial:ℂ)*s k‖ with ha
  have hpole : ∀ m : ℕ, μ+1/2 ≠ -m := fun m h => by
    have := congrArg Complex.re h; simp at this; linarith [(m.cast_nonneg : (0:ℝ) ≤ m)]
  have hG : Gamma (μ+1/2) ≠ 0 := Gamma_ne_zero hpole
  set c : ℝ := 1/(4*‖Gamma (μ+1/2)‖) with hc
  have hc0 : 0 < c := by rw [hc]; have := norm_pos_iff.mpr hG; positivity
  -- eventual lower bound `a k ≥ c ‖s k‖ / k`
  have hlow : ∀ᶠ k : ℕ in atTop, c * ‖s k‖ / k ≤ a k := by
    filter_upwards [FerrersFourier.gamma_ratio_ge (ν+μ+1) (ν+3/2),
        FerrersFourier.gamma_ratio_ge (μ+1/2) 1,
      eventually_gt_atTop 0] with k hA hP hk0
    have e : Gamma (ν+μ+k+1)/Gamma (ν+k+3/2)*pochhammer (μ+1/2) k/(k.factorial:ℂ)*s k =
        Gamma (k+(ν+μ+1))/Gamma (k+(ν+3/2)) * (Gamma (k+(μ+1/2))/Gamma (k+1) /
          Gamma (μ+1/2)) * s k := by
      rw [pochhammer, ← Gamma_add_nat_div_Gamma_eq (μ+1/2) hpole, ← Complex.Gamma_nat_eq_factorial,
        show ν+μ+k+1 = k+(ν+μ+1) by ring, show ν+k+3/2 = k+(ν+3/2) by ring,
        add_comm (μ+1/2) (k:ℂ)]
      ring
    have hre : (ν+μ+1-(ν+3/2)).re = μ.re - 1/2 := by simp; ring
    have hre2 : (μ+1/2-1).re = μ.re - 1/2 := by simp; ring
    rw [hre] at hA
    rw [hre2] at hP
    have hkp : (0:ℝ) < k := by exact_mod_cast hk0
    have hk1 : (1:ℝ) ≤ k := by exact_mod_cast hk0
    have hpow : (k:ℝ)^(-1:ℝ) ≤ (k:ℝ)^(μ.re-1/2) * (k:ℝ)^(μ.re-1/2) := by
      rw [← Real.rpow_add hkp]
      exact Real.rpow_le_rpow_of_exponent_le hk1 (by linarith)
    rw [Real.rpow_neg_one] at hpow
    simp only [ha]
    rw [e, norm_mul, norm_mul, norm_div (Gamma (k+(μ+1/2))/Gamma (k+1))]
    have hGn : 0 < ‖Gamma (μ+1/2)‖ := norm_pos_iff.mpr hG
    have h0 : 0 ≤ (k:ℝ)^(μ.re-1/2) := (Real.rpow_pos_of_pos hkp _).le
    calc c * ‖s k‖ / k = ((k:ℝ)⁻¹ / 4 / ‖Gamma (μ+1/2)‖) * ‖s k‖ := by rw [hc]; field_simp
      _ ≤ (((k:ℝ)^(μ.re-1/2) / 2) * ((k:ℝ)^(μ.re-1/2) / 2 / ‖Gamma (μ+1/2)‖)) * ‖s k‖ := by
          gcongr
          calc (k:ℝ)⁻¹ / 4 / ‖Gamma (μ+1/2)‖
              ≤ ((k:ℝ)^(μ.re-1/2) * (k:ℝ)^(μ.re-1/2)) / 4 / ‖Gamma (μ+1/2)‖ := by gcongr
            _ = _ := by ring
      _ ≤ _ := by gcongr
  have hsum2 : Summable (fun k => a k + a (k+1)) := hsum.add ((summable_nat_add_iff 1).mpr hsum)
  have hh : Summable (fun k : ℕ => 1 / ((k+1 : ℕ) : ℝ)) := by
    refine Summable.of_norm_bounded_eventually_nat (hsum2.mul_left (1/(c*δ))) ?_
    filter_upwards [hlow, (tendsto_add_atTop_nat 1).eventually hlow, eventually_gt_atTop 0]
      with k hk hk' hk0
    have hkp : (0:ℝ) < k := by exact_mod_cast hk0
    have hk1 : (0:ℝ) < ((k+1 : ℕ) : ℝ) := by positivity
    have hle : c * ‖s k‖ / ((k+1 : ℕ) : ℝ) ≤ a k := by
      refine le_trans ?_ hk
      gcongr
      linarith
    have hsk := hs k
    have hnn : 0 ≤ ‖1 / ((k+1 : ℕ) : ℝ)‖ := norm_nonneg _
    rw [Real.norm_of_nonneg (by positivity)]
    rw [div_le_iff₀ hk1] at hle hk'
    have hcd : 0 < c * δ := mul_pos hc0 hδ
    rw [div_le_iff₀ hk1]
    have key : c*δ ≤ (a k + a (k+1)) * ((k+1:ℕ):ℝ) := by
      nlinarith [mul_le_mul_of_nonneg_left hsk hc0.le]
    rw [show 1/(c*δ) * (a k + a (k+1)) * ((k+1:ℕ):ℝ) =
      ((a k + a (k+1)) * ((k+1:ℕ):ℝ)) / (c*δ) by ring, le_div_iff₀ hcd]
    linarith
  exact Real.not_summable_one_div_natCast ((summable_nat_add_iff 1).mp hh)

/-- `sin 2θ ≠ 0` for `0 < θ < π`, `θ ≠ π/2`. -/
theorem FerrersFourier.sin_two_mul_ne {θ : ℝ} (h0 : 0 < θ) (hπ : θ < π) (hmid : θ ≠ π/2) :
    0 < |Real.sin (2*θ)| := by
  rw [abs_pos, Real.sin_two_mul]
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi h0 hπ
  have hc : Real.cos θ ≠ 0 := by
    intro hc
    apply hmid
    refine Real.injOn_cos ⟨h0.le, hπ.le⟩ ⟨by positivity, by linarith [Real.pi_pos]⟩ ?_
    rw [hc, Real.cos_pi_div_two]
  positivity

/-- Summation by parts (Dirichlet's test with bounded variation): if the partial sums of `b`
are bounded, `c → 0` and `∑ ‖c (n+1) - c n‖ < ∞`, then `∑ c n b n` converges. -/
theorem FerrersFourier.dirichlet {c b : ℕ → ℂ} {M : ℝ} (hB : ∀ n, ‖∑ i ∈ Finset.range n, b i‖ ≤ M)
    (hc : Tendsto c atTop (𝓝 0)) (hv : Summable (fun n => ‖c (n+1) - c n‖)) :
    ∃ l, Tendsto (fun n => ∑ i ∈ Finset.range n, c i * b i) atTop (𝓝 l) := by
  set B : ℕ → ℂ := fun n => ∑ i ∈ Finset.range n, b i with hBdef
  have hparts : ∀ n, ∑ i ∈ Finset.range n, c i * b i =
      c n * B n - ∑ i ∈ Finset.range n, (c (i+1) - c i) * B (i+1) := by
    intro n
    induction n with
    | zero => simp [hBdef]
    | succ n ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
      simp only [hBdef, Finset.sum_range_succ]
      ring
  have hM : 0 ≤ M := (norm_nonneg _).trans (hB 0)
  have hs : Summable (fun i => (c (i+1) - c i) * B (i+1)) := by
    refine Summable.of_norm_bounded (hv.mul_right M) fun i => ?_
    rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hB _) (norm_nonneg _)
  refine ⟨0 - ∑' i, (c (i+1) - c i) * B (i+1), ?_⟩
  simp_rw [hparts]
  refine Tendsto.sub ?_ hs.hasSum.tendsto_sum_nat
  have h0 : Tendsto (fun n => M * ‖c n‖) atTop (𝓝 0) := by
    simpa using (hc.norm.const_mul M)
  refine squeeze_zero_norm (fun n => ?_) h0
  rw [norm_mul, mul_comm]; exact mul_le_mul_of_nonneg_right (hB n) (norm_nonneg _)

end DLMF.Legendre
