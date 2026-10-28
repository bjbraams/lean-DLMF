/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.ErrorFunctions.BoundsAsymptotics.ContinuedFractions

/-!
# Gaussian error-function remainder estimates

Faddeeva continued fractions and signed remainder bounds for the complementary error function.

Source references and common attribution are retained in
`DLMF.ErrorFunctions.BoundsAsymptotics`.
-/

@[expose] public noncomputable section

open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF

open scoped Real Topology Nat Interval

namespace DLMF.Confluent

/-- Continued-fraction representation: `HasContinuedFraction (fun k => if k=0 then I/Real.sqrt π
else -(k : ℂ)/2) (fun _ => z) (faddeevaW z)`. -/
@[dlmf 7.9.E3]
theorem faddeevaW_continuedFraction {z : ℂ} (hz : 0 < z.im) :
    HasContinuedFraction (fun k => if k=0 then I/Real.sqrt π else -(k : ℂ)/2) (fun _ => z) (faddeevaW z) := by
  set ζ : ℂ := -I * z with hζ
  have hζre : 0 < ζ.re := by simp [ζ, hz]
  have hζ0 : ζ ≠ 0 := fun h => by simp [h] at hζre
  have hp : (Real.sqrt π : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  set a1 : ℕ → ℂ := fun k => if k=0 then ζ else (k : ℂ)/2 with ha1
  set b1 : ℕ → ℂ := fun k => if Even k then ζ^2 else 1 with hb1
  set aE : ℕ → ℂ := fun k => if k=0 then I else -(k : ℂ)/2 with haE
  have h1 := erfc_continuedFraction_one hζre
  rw [incGF_hasContinuedFraction_iff (fun k hk => by
    simp only [show k ≠ 0 by omega, ↓reduceIte]
    exact div_ne_zero (Nat.cast_ne_zero.mpr (by omega)) two_ne_zero)] at h1
  rw [incGF_hasContinuedFraction_iff (fun k hk => by
    simp only [show k ≠ 0 by omega, ↓reduceIte]
    exact div_ne_zero (neg_ne_zero.mpr (Nat.cast_ne_zero.mpr (by omega))) two_ne_zero)]
  set r : ℕ → ℂ := fun k => if Even k then I / ζ else I * ζ with hr
  have hr0 : ∀ k, r k ≠ 0 := fun k => by
    simp only [r]; split_ifs
    · exact div_ne_zero I_ne_zero hζ0
    · exact mul_ne_zero I_ne_zero hζ0
  have hIζ : I * ζ = z := by simp only [ζ]; ring_nf; rw [I_sq]; ring
  have hEa : aE = fun k => (if k = 0 then r 0 else r (k - 1) * r k) * a1 k := by
    funext k
    rcases k with _ | j
    · simp only [aE, a1, r, ↓reduceIte, show Even 0 from ⟨0, rfl⟩]; field_simp
    · simp only [aE, a1, r, Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
      rcases Nat.even_or_odd j with hj | hj
      · have hj' : ¬ Even (j + 1) := Nat.not_even_iff_odd.mpr hj.add_one
        simp only [hj, hj', ↓reduceIte]
        field_simp
        rw [I_sq]
      · have hj' : Even (j + 1) := hj.add_one
        have hj2 : ¬ Even j := Nat.not_even_iff_odd.mpr hj
        simp only [hj2, hj', ↓reduceIte]
        field_simp
        rw [I_sq]
  have hEb : (fun _ : ℕ => z) = fun k => r k * b1 k := by
    funext k
    simp only [r, b1]
    split_ifs
    · rw [← hIζ]; field_simp
    · rw [mul_one, hIζ]
  have hconv : ∀ n, (GenContFract.cfConv_ofFun 0
      (fun k => if k=0 then I/Real.sqrt π else -(k : ℂ)/2) (fun _ => z)).convs n =
      (Real.sqrt π : ℂ)⁻¹ * (GenContFract.cfConv_ofFun 0 a1 b1).convs n := by
    intro n
    have e : (fun k : ℕ => if k=0 then I/Real.sqrt π else -(k : ℂ)/2) =
        fun k : ℕ => if k = 0 then (Real.sqrt π : ℂ)⁻¹ * aE 0 else aE k := by
      funext k
      split_ifs with hk
      · simp [aE, div_eq_inv_mul]
      · simp [aE, hk]
    rw [e, GenContFract.cfConv_convs_smul_a0, hEa, hEb, GenContFract.cfConv_equiv_convs r hr0]
  rw [show (GenContFract.cfConv_ofFun 0
      (fun k => if k=0 then I/Real.sqrt π else -(k : ℂ)/2) (fun _ => z)).convs =
      fun n => (Real.sqrt π : ℂ)⁻¹ * (GenContFract.cfConv_ofFun 0 a1 b1).convs n from
      funext hconv]
  convert h1.const_mul ((Real.sqrt π : ℂ)⁻¹) using 2
  simp only [faddeevaW, ζ]
  field_simp
  ring_nf
  rw [I_sq]
  ring_nf

/-- The Gaussian kernel along a ray. -/
theorem norm_cexp_neg_ofReal_mul_exp_ofReal_mul_I_sq (r y : ℝ) :
    ‖cexp (-(((r : ℂ) * exp (y * I)) ^ 2 / 4))‖ = Real.exp (-(r ^ 2 * Real.cos (2 * y)) / 4) := by
  rw [Complex.norm_exp, ofReal_mul_exp_ofReal_mul_I_sq]
  congr 1
  rw [neg_re, div_ofNat_re, re_ofReal_mul, exp_ofReal_mul_I_re]
  ring

/-- The Gaussian kernel is bounded by `1` in the sector `|arg t| ≤ π/4`. -/
theorem norm_cexp_neg_ofReal_mul_exp_ofReal_mul_I_sq_le_one (r : ℝ) {y : ℝ} (hy : |y| ≤ π / 4) :
    ‖cexp (-(((r : ℂ) * exp (y * I)) ^ 2 / 4))‖ ≤ 1 := by
  rw [norm_cexp_neg_ofReal_mul_exp_ofReal_mul_I_sq, Real.exp_le_one_iff]
  have : 0 ≤ Real.cos (2 * y) := by
    rw [← Real.cos_abs, abs_mul, abs_two]
    exact Real.cos_nonneg_of_mem_Icc ⟨by linarith [abs_nonneg y, Real.pi_pos], by linarith⟩
  have := mul_nonneg (sq_nonneg r) this
  linarith

/-- Integrability of the Gaussian kernel along a ray `|arg t| < π/4`. -/
theorem integrableOn_gauss_rotate (c : ℝ) {θ : ℝ} (hθ : |θ| < π / 4) :
    IntegrableOn (fun r : ℝ => Real.exp (-c * r) • cexp (-(((r : ℂ) * exp (θ * I)) ^ 2 / 4)))
      (Ioi 0) := by
  have hb : 0 < (exp (((2 * θ : ℝ) : ℂ) * I) / 4).re := by
    rw [div_ofNat_re, exp_ofReal_mul_I_re]
    have : 0 < Real.cos (2 * θ) := by
      rw [← Real.cos_abs, abs_mul, abs_two]
      exact Real.cos_pos_of_mem_Ioo ⟨by linarith [abs_nonneg θ, Real.pi_pos], by linarith⟩
    positivity
  refine (integrable_cexp_quadratic hb (-c : ℂ) 0).integrableOn.congr_fun (fun r _ => ?_)
    measurableSet_Ioi
  rw [Complex.real_smul, ofReal_exp, ← Complex.exp_add, ofReal_mul_exp_ofReal_mul_I_sq]
  push_cast
  ring_nf

/-- The Laplace transform of the Gaussian kernel along a ray `|arg t| < π/4` is entire. -/
theorem differentiable_laplace_gauss_rotate {θ : ℝ} (hθ : |θ| < π / 4) :
    Differentiable ℂ (fun w : ℂ => ∫ r in Ioi (0 : ℝ), cexp (-(w * r)) •
      cexp (-(((r : ℂ) * exp (θ * I)) ^ 2 / 4))) := fun w =>
  (differentiableOn_integral_cexp_neg_mul_smul (integrableOn_gauss_rotate (w.re - 1) hθ)).differentiableAt
    ((isOpen_lt continuous_const continuous_re).mem_nhds (by simp))

/-- The real Laplace representation `erfc x = π^{-1/2} e^{-x²} ∫₀^∞ e^{-xt} e^{-t²/4} dt`. -/
theorem erfc_ofReal_eq_laplace_gauss (x : ℝ) :
    erfc x = 1 / Real.sqrt π * cexp (-(x : ℂ) ^ 2) *
      ∫ t in Ioi (0 : ℝ), cexp (-((x : ℂ) * t)) * cexp (-((t : ℂ) ^ 2 / 4)) := by
  have hre : (erfc x).re = TauCeti.Real.erfc x := by
    rw [erfc, erf_ofReal, TauCeti.Real.erfc_def]; simp
  have herfc : erfc (x : ℂ) = (TauCeti.Real.erfc x : ℂ) := by
    rw [erfc, erf_ofReal, TauCeti.Real.erfc_def]; push_cast; ring
  have hm := Real.millsRatio_integral x
  rw [Real.millsRatio, hre] at hm
  have hI : ∫ t in Ioi (x : ℝ), Real.exp (-t ^ 2) = Real.sqrt π / 2 * TauCeti.Real.erfc x := by
    have := Real.exp_pos (x ^ 2)
    field_simp at hm ⊢
    nlinarith [hm]
  -- substitution `t = 2s` and the shift `u = x + s`
  have h2 := integral_comp_mul_left_Ioi
    (fun t : ℝ => cexp (-((x : ℂ) * t)) * cexp (-((t : ℂ) ^ 2 / 4))) 0 (two_pos : (0 : ℝ) < 2)
  rw [mul_zero] at h2
  have hsh := setIntegral_Ioi_comp_add_right (fun u : ℝ => cexp (-((u : ℂ) ^ 2))) 0 x
  rw [zero_add] at hsh
  have hcomp : ∫ s in Ioi (0 : ℝ), cexp (-(x : ℂ) ^ 2) *
      (cexp (-((x : ℂ) * ((2 * s : ℝ) : ℂ))) * cexp (-((((2 * s : ℝ) : ℂ)) ^ 2 / 4))) =
      ∫ s in Ioi (0 : ℝ), cexp (-(((s + x : ℝ) : ℂ) ^ 2)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
    rw [← Complex.exp_add, ← Complex.exp_add]
    push_cast
    ring_nf
  rw [integral_const_mul, h2, hsh] at hcomp
  have hreal : ∫ u in Ioi x, cexp (-((u : ℂ) ^ 2)) = ((∫ u in Ioi x, Real.exp (-u ^ 2) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    push_cast; rfl
  rw [hreal, hI] at hcomp
  rw [herfc]
  have hcomp' : cexp (-(x : ℂ) ^ 2) * ∫ t in Ioi (0 : ℝ), cexp (-((x : ℂ) * t)) *
      cexp (-((t : ℂ) ^ 2 / 4)) = 2 * ((Real.sqrt π / 2 * TauCeti.Real.erfc x : ℝ) : ℂ) := by
    rw [← hcomp, Complex.real_smul]
    push_cast
    field_simp
  rw [mul_assoc, hcomp']
  have hπ : (Real.sqrt π : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  push_cast
  field_simp

/-- **Rotated Laplace representation of `erfc`**: for `|θ| < π/4` and every complex `z`,
`erfc z = π^{-1/2} e^{-z²} e^{iθ} ∫₀^∞ e^{-z e^{iθ} r} e^{-(r e^{iθ})²/4} dr`. -/
theorem erfc_eq_integral_rotate {θ : ℝ} (hθ : |θ| < π / 4) (z : ℂ) :
    erfc z = 1 / Real.sqrt π * cexp (-z ^ 2) * (exp (θ * I) * ∫ r in Ioi (0 : ℝ),
      cexp (-(z * exp (θ * I) * r)) * cexp (-(((r : ℂ) * exp (θ * I)) ^ 2 / 4))) := by
  have hL := differentiable_laplace_gauss_rotate hθ
  simp only [smul_eq_mul] at hL
  have hd1 : Differentiable ℂ erfc := by
    unfold erfc; exact differentiable_const _ |>.sub differentiable_erf_complex
  have hd2 : Differentiable ℂ (fun z : ℂ => 1 / Real.sqrt π * cexp (-z ^ 2) * (exp (θ * I) *
      ∫ r in Ioi (0 : ℝ), cexp (-(z * exp (θ * I) * r)) *
        cexp (-(((r : ℂ) * exp (θ * I)) ^ 2 / 4)))) := by
    have := hL.comp (differentiable_id.mul_const (exp (θ * I)))
    exact ((differentiable_const _).mul (by fun_prop)).mul ((differentiable_const _).mul this)
  have hreal : ∀ x : ℝ, 0 < x → erfc x = 1 / Real.sqrt π * cexp (-(x : ℂ) ^ 2) *
      (exp (θ * I) * ∫ r in Ioi (0 : ℝ), cexp (-((x : ℂ) * exp (θ * I) * r)) *
        cexp (-(((r : ℂ) * exp (θ * I)) ^ 2 / 4))) := by
    intro x hx
    rw [erfc_ofReal_eq_laplace_gauss x]
    congr 1
    have hy : ∀ y ∈ [[0, θ]], |y| ≤ π / 4 := fun y hy =>
      (abs_le_abs_of_mem_uIcc_zero hy).trans hθ.le
    refine integral_cexp_neg_mul_mul_eq_rotate (F := fun t => cexp (-(t ^ 2 / 4))) (σ := 1)
      (C := 1) (k := 0) one_pos (fun r _ y _ => by fun_prop) (fun r _ _ y hy' => ?_)
      (fun r _ y hy' => ?_) (fun y hy' => ?_)
    · rw [sub_self, Real.rpow_zero, mul_one]
      exact norm_cexp_neg_ofReal_mul_exp_ofReal_mul_I_sq_le_one r (hy y hy')
    · rw [Real.rpow_zero, mul_one]
      exact norm_cexp_neg_ofReal_mul_exp_ofReal_mul_I_sq_le_one r (hy y hy')
    · rw [re_ofReal_mul, exp_ofReal_mul_I_re]
      have := hy y hy'
      exact mul_pos hx (Real.cos_pos_of_mem_Ioo ⟨by linarith [neg_abs_le y, Real.pi_pos],
        by linarith [le_abs_self y, Real.pi_pos]⟩)
  have hfreq : ∃ᶠ w in 𝓝[≠] (1 : ℂ), erfc w = 1 / Real.sqrt π * cexp (-w ^ 2) *
      (exp (θ * I) * ∫ r in Ioi (0 : ℝ), cexp (-(w * exp (θ * I) * r)) *
        cexp (-(((r : ℂ) * exp (θ * I)) ^ 2 / 4))) := by
    have ht : Tendsto (fun r : ℝ => (r : ℂ)) (𝓝[≠] (1 : ℝ)) (𝓝[≠] (1 : ℂ)) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · have := (continuous_ofReal.tendsto (1 : ℝ)).mono_left
          (nhdsWithin_le_nhds (s := ({1}ᶜ : Set ℝ)))
        rwa [ofReal_one] at this
      · filter_upwards [self_mem_nhdsWithin] with r hr
        simpa using hr
    apply ht.frequently
    apply Eventually.frequently
    filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds (zero_lt_one' ℝ))] with r hr
    exact hreal r hr
  exact (hd1.differentiableOn.analyticOnNhd isOpen_univ).eqOn_of_preconnected_of_frequently_eq
    (hd2.differentiableOn.analyticOnNhd isOpen_univ) isPreconnected_univ (mem_univ _) hfreq
    (mem_univ z)

/-- Coefficients of `e^{-t²/4} = ∑ aₙ tⁿ`. -/
noncomputable def gaussQuarterCoeff (n : ℕ) : ℂ :=
  if Even n then (-1 / 4 : ℂ) ^ (n / 2) / ((n / 2).factorial : ℂ) else 0

/-- Partial sums of `∑ aₙ tⁿ` are partial sums of the exponential series of `-t²/4`. -/
theorem sum_gaussQuarterCoeff (t : ℂ) (M : ℕ) :
    (∑ n ∈ Finset.range (2 * M), t ^ n * gaussQuarterCoeff n =
      ∑ k ∈ Finset.range M, (-(t ^ 2 / 4)) ^ k / (k.factorial : ℂ)) ∧
    (∑ n ∈ Finset.range (2 * M + 1), t ^ n * gaussQuarterCoeff n =
      ∑ k ∈ Finset.range (M + 1), (-(t ^ 2 / 4)) ^ k / (k.factorial : ℂ)) := by
  induction M with
  | zero => simp [gaussQuarterCoeff]
  | succ M ih =>
    have h1 : ∑ n ∈ Finset.range (2 * (M + 1)), t ^ n * gaussQuarterCoeff n =
        ∑ k ∈ Finset.range (M + 1), (-(t ^ 2 / 4)) ^ k / (k.factorial : ℂ) := by
      rw [show 2 * (M + 1) = 2 * M + 1 + 1 by ring, Finset.sum_range_succ, ih.2]
      have : ¬ Even (2 * M + 1) := by simp
      simp [gaussQuarterCoeff]
    refine ⟨h1, ?_⟩
    rw [Finset.sum_range_succ, h1, Finset.sum_range_succ (n := M + 1)]
    congr 1
    have he : Even (2 * (M + 1)) := even_two_mul _
    have hd : 2 * (M + 1) / 2 = M + 1 := by omega
    simp only [gaussQuarterCoeff, he, ite_true, hd]
    rw [neg_pow, div_pow, div_pow, ← pow_mul]
    ring

/-- Taylor remainders of `e^{-t²/4}` along a ray, in the form required by Watson's lemma. -/
theorem gauss_sub_sum_isBigO (θ : ℝ) (N : ℕ) :
    (fun r : ℝ => cexp (-(((r : ℂ) * exp (θ * I)) ^ 2 / 4)) - ∑ n ∈ Finset.range N,
      (((r : ℂ) * exp (θ * I)) ^ ((n : ℂ) + 1 - 1)) • gaussQuarterCoeff n)
      =O[𝓝[>] 0] fun r => r ^ ((N : ℝ) + (1 : ℂ).re - 1) := by
  obtain ⟨M, hM⟩ : ∃ M : ℕ, N ≤ 2 * M ∧
      ∀ t : ℂ, ∑ n ∈ Finset.range N, t ^ n * gaussQuarterCoeff n =
        ∑ k ∈ Finset.range M, (-(t ^ 2 / 4)) ^ k / (k.factorial : ℂ) := by
    obtain ⟨M, rfl | rfl⟩ := Nat.even_or_odd' N
    · exact ⟨M, le_rfl, fun t => (sum_gaussQuarterCoeff t M).1⟩
    · exact ⟨M + 1, by omega, fun t => (sum_gaussQuarterCoeff t M).2⟩
  refine IsBigO.of_bound 3 ?_
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds (zero_lt_one' ℝ))]
    with r hr hr1
  have hr : (0 : ℝ) < r := hr
  have hr1 : r < 1 := hr1
  simp only [one_re, add_sub_cancel_right, cpow_natCast, smul_eq_mul]
  rw [hM.2]
  have hb := Complex.norm_exp_sub_sum_le_norm_mul_exp (-(((r : ℂ) * exp (θ * I)) ^ 2 / 4)) M
  have hn : ‖-(((r : ℂ) * exp (θ * I)) ^ 2 / 4)‖ = r ^ 2 / 4 := by
    rw [norm_neg, norm_div, norm_pow, norm_mul, Complex.norm_real, Real.norm_of_nonneg hr.le,
      norm_exp_ofReal_mul_I, mul_one]
    simp
  rw [hn] at hb
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hr.le _), Real.rpow_natCast]
  refine hb.trans ?_
  have h1 : (r ^ 2 / 4) ^ M ≤ r ^ N := by
    calc (r ^ 2 / 4) ^ M ≤ (r ^ 2) ^ M := by
          gcongr; linarith [sq_nonneg r]
      _ = r ^ (2 * M) := by rw [← pow_mul]
      _ ≤ r ^ N := pow_le_pow_of_le_one hr.le hr1.le hM.1
  have h2 : Real.exp (r ^ 2 / 4) ≤ 3 := by
    have : r ^ 2 / 4 ≤ 1 / 4 := by nlinarith
    calc Real.exp (r ^ 2 / 4) ≤ Real.exp (1 / 4) := Real.exp_le_exp.mpr this
      _ ≤ 3 := by
        have := Real.exp_one_lt_d9
        have h := Real.exp_le_exp.mpr (show (1 : ℝ) / 4 ≤ 1 by norm_num)
        linarith
  calc (r ^ 2 / 4) ^ M * Real.exp (r ^ 2 / 4) ≤ r ^ N * 3 := by
        gcongr
    _ = 3 * r ^ N := by ring

/-- `(1/2)ₙ 4ⁿ n! = (2n)!`. -/
theorem poch_half_mul_four_pow_mul_factorial (n : ℕ) :
    poch (1 / 2) n * (4 ^ n * (n.factorial : ℂ)) = ((2 * n).factorial : ℂ) := by
  induction n with
  | zero => simp [poch]
  | succ n ih =>
    rw [poch_succ, show 2 * (n + 1) = 2 * n + 1 + 1 by ring, Nat.factorial_succ (2 * n + 1),
      Nat.factorial_succ (2 * n), Nat.factorial_succ n]
    push_cast
    rw [← ih]
    ring

/-- `erfc z ~ π^{-1/2} e^{-z²} ∑ (-1)ⁿ (1/2)ₙ z^{-2n-1}` in a rotated sector. -/
theorem erfc_rotSector_asymptotic {θ δ : ℝ} (hθ : |θ| < π / 4) (hδ : 0 < δ) :
    HasAsymptoticExpansion (comap (fun z : ℂ => z * exp (θ * I)) (sectorAtTop δ))
      (fun n z => exp (-z ^ 2) * z ^ (-(2 * (n : ℂ) + 1)))
      (fun n => (-1 : ℂ) ^ n * poch (1 / 2) n / Real.sqrt π) erfc := by
  have hθ' : |θ| < π / 2 := by linarith [Real.pi_pos]
  have hW := hasAsymptoticExpansion_integral_cexp_smul_rotate_comap
    (F := fun t => cexp (-(t ^ 2 / 4))) (a := gaussQuarterCoeff) (μ := 1) (c := 0) hθ'
    (by norm_num) hδ (integrableOn_gauss_rotate 0 hθ) (gauss_sub_sum_isBigO θ)
  have hE := hW.even (fun n => by
    have : ¬ Even (2 * n + 1) := by simp
    simp [gaussQuarterCoeff, this])
  have h3 := (hE.const_smul (1 / Real.sqrt π : ℂ)).mul_left (fun z : ℂ => cexp (-z ^ 2))
  refine ((h3.congr' (Eventually.of_forall fun z => ?_)).congr_scale fun n =>
    Eventually.of_forall fun z => ?_).congr_coeff ?_
  · simp only [Pi.smul_apply, smul_eq_mul]
    rw [erfc_eq_integral_rotate hθ z]
    ring
  · simp only
    push_cast
    ring_nf
  · funext n
    have hπ : (Real.sqrt π : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
    have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
    have hp := poch_half_mul_four_pow_mul_factorial n
    simp only [Pi.smul_apply, smul_eq_mul, gaussQuarterCoeff, even_two_mul, ite_true,
      show 2 * n / 2 = n by omega]
    rw [show ((2 * n : ℕ) : ℂ) + 1 = ((2 * n : ℕ) : ℂ) + 1 from rfl,
      Complex.Gamma_nat_eq_factorial, ← hp]
    field_simp
    rw [mul_assoc, ← mul_pow]
    norm_num

/-- Identity under the stated parameter and domain assumptions: `HasAsymptoticExpansion (sector
(3*π/4-δ)) (fun n z => exp (-z^2)*z^(-(2*(n : ℂ)+1))) (fun n => (-1 : ℂ)^n*poch (1/2)
n/Real.sqrt π) erfc ∧ HasAsymptoticExpansion (sector (3*π/4-δ)) (fun n z => exp
(-z^2)*z^(-(2*(n : ℂ)+1))) (fun n => -(-1 : ℂ)^n*poch (1/2) n/Real.sqrt π) (fun z => erfc
(-z)-2)`. -/
@[dlmf 7.12.E1]
theorem erfc_sector_asymptotic {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 3*π/4) :
    HasAsymptoticExpansion (sector (3*π/4-δ)) (fun n z => exp (-z^2)*z^(-(2*(n : ℂ)+1))) (fun n => (-1 : ℂ)^n*poch (1/2) n/Real.sqrt π) erfc ∧ HasAsymptoticExpansion (sector (3*π/4-δ)) (fun n z => exp (-z^2)*z^(-(2*(n : ℂ)+1))) (fun n => -(-1 : ℂ)^n*poch (1/2) n/Real.sqrt π) (fun z => erfc (-z)-2) := by
  set d := min δ (π / 4) with hd
  have hd0 : 0 < d := lt_min hδ (by positivity)
  have hdδ : d ≤ δ := min_le_left _ _
  have hdπ : d ≤ π / 4 := min_le_right _ _
  have hcov := le_sup_comap_rotate (α := 3 * π / 4 - δ) (β := π / 4 - d / 2) (γ := π / 2 - d / 2)
    (by linarith) (by linarith) (by linarith) (by linarith)
  have hcos : 0 < Real.cos (π / 2 - d / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩
  have hβ : |π / 4 - d / 2| < π / 4 := by
    rw [abs_lt]; constructor <;> linarith
  have h1 := erfc_rotSector_asymptotic (θ := -(π / 4 - d / 2)) (by rwa [abs_neg]) hcos
  have h2 := erfc_rotSector_asymptotic (θ := π / 4 - d / 2) hβ hcos
  have hA : HasAsymptoticExpansion (sector (3 * π / 4 - δ))
      (fun n z => exp (-z ^ 2) * z ^ (-(2 * (n : ℂ) + 1)))
      (fun n => (-1 : ℂ) ^ n * poch (1 / 2) n / Real.sqrt π) erfc :=
    (h1.sup h2).mono hcov
  refine ⟨hA, ?_⟩
  refine (hA.neg.congr' (Eventually.of_forall fun z => ?_)).congr_coeff ?_
  · simp only [Pi.neg_apply]
    rw [erfc_negative]
    ring
  · funext n
    simp only [Pi.neg_apply]
    ring

/-- Unnormalized erfc remainder. -/
def erfcAsymptoticRemainder (N : ℕ) (z : ℂ) : ℂ :=
  erfc z-exp (-z^2)/Real.sqrt π*∑ n ∈ Finset.range N, (-1 : ℂ)^n*poch (1/2) n/z^(2*n+1)

/-- `(1/2)_n = Γ(n+1/2)/√π`, as a real number. -/
theorem poch_half_eq_Gamma (n : ℕ) :
    poch (1/2) n = ((Real.Gamma (n+1/2)/Real.sqrt π : ℝ) : ℂ) := by
  induction n with
  | zero =>
    rw [poch_zero]; simp only [Nat.cast_zero, zero_add, Real.Gamma_one_half_eq]
    rw [div_self (Real.sqrt_pos.mpr Real.pi_pos).ne']; simp
  | succ n ih =>
    rw [poch_succ, ih]
    have : ((n+1:ℕ):ℝ)+1/2 = ((n:ℝ)+1/2)+1 := by push_cast; ring
    rw [this, Real.Gamma_add_one (by positivity)]
    push_cast; ring

/-- `r e^{iy}` lies in the slit plane for `r > 0` and `|y| < π`. -/
theorem ofReal_mul_exp_mem_slitPlane {r y : ℝ} (hr : 0 < r) (hy : |y| < π) :
    (r : ℂ) * exp (y * I) ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  by_cases hs : Real.sin y = 0
  · left
    have hy0 : y = 0 := (Real.sin_eq_zero_iff_of_lt_of_lt (by linarith [neg_abs_le y])
      (by linarith [le_abs_self y])).mp hs
    subst hy0; simp [hr]
  · right
    rw [im_ofReal_mul, exp_ofReal_mul_I_im]
    exact mul_ne_zero hr.ne' hs

/-- Bound for the kernel `t^{-1/2}/(1+t)` of the Laplace form of `erfc` along rays. -/
theorem norm_erfcKernel_le {θ c : ℝ} (hc0 : 0 < c)
    (hc : ∀ s : ℝ, 0 ≤ s → ∀ u : ℝ, |u| ≤ |θ| → c ≤ ‖1 + (s : ℂ) * exp (u * I)‖)
    (hθ : |θ| < π) {r y : ℝ} (hr : 0 < r) (hy : |y| ≤ |θ|) :
    ‖((r : ℂ) * exp (y * I)) ^ (-1/2 : ℂ) * (1 + (r : ℂ) * exp (y * I))⁻¹‖ ≤
      1 / c * r ^ (-1/2 : ℝ) := by
  have hy' : |y| < π := lt_of_le_of_lt hy hθ
  rw [abs_lt] at hy'
  rw [norm_mul, norm_inv, ofReal_mul_exp_cpow hr hy'.1 hy'.2.le, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hr,
    show (y : ℂ) * I * (-1/2 : ℂ) = ((-y/2 : ℝ) : ℂ) * I by push_cast; ring,
    norm_exp_ofReal_mul_I, mul_one]
  have h1 := hc r hr.le y hy
  have hre : ((-1/2 : ℂ)).re = -1/2 := by norm_num
  rw [hre]
  have hp : 0 < r ^ (-1/2 : ℝ) := Real.rpow_pos_of_pos hr _
  calc r ^ (-1/2 : ℝ) * ‖1 + (r : ℂ) * exp (y * I)‖⁻¹ ≤ r ^ (-1/2 : ℝ) * (1 / c) := by
        gcongr; rw [one_div]; exact inv_anti₀ hc0 h1
    _ = _ := by ring

/-- If `re z > 0` and `re (z e^{iθ}) > 0` with `|θ| < π`, then `re (z e^{iy}) > 0` for every
`y` between `0` and `θ`. -/
theorem re_mul_exp_pos_of_mem_uIcc_of_lt_pi {z : ℂ} {θ y : ℝ} (hθ : |θ| < π) (hz : 0 < z.re)
    (hzθ : 0 < (z * exp (θ * I)).re) (hy : y ∈ [[0, θ]]) : 0 < (z * exp (y * I)).re := by
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  have h0 : |arg z| < π / 2 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hz)
  have h1 : |arg z + θ| < π / 2 := by
    rw [re_mul_exp_ofReal_mul_I] at hzθ
    have hc : 0 < Real.cos (arg z + θ) := by
      by_contra hc; push Not at hc; nlinarith [norm_nonneg z]
    rw [abs_lt] at h0 hθ
    exact abs_lt_pi_div_two_of_cos_pos' (by linarith) (by linarith) hc
  have h2 : |arg z + y| < π / 2 := by
    rcases le_total 0 θ with h | h
    · rw [uIcc_of_le h] at hy
      rw [abs_lt] at h0 h1 ⊢; constructor <;> linarith [hy.1, hy.2]
    · rw [uIcc_of_ge h] at hy
      rw [abs_lt] at h0 h1 ⊢; constructor <;> linarith [hy.1, hy.2]
  rw [re_mul_exp_ofReal_mul_I]
  refine mul_pos (norm_pos_iff.mpr hz0) ?_
  rw [← Real.cos_abs]
  exact Real.cos_pos_of_mem_Ioo ⟨by linarith [abs_nonneg (arg z + y), Real.pi_pos], h2⟩

/-- **Rotated Laplace form of `erfc`** (DLMF 7.7.2 continued): for `|θ| < π` and `z` in the
quarter-plane sector `|im (z e^{iθ/2})| < re (z e^{iθ/2})`,
`erfc z = e^{-z²}/π · e^{iθ} ∫₀^∞ e^{-z² e^{iθ} r} (r e^{iθ})^{-1/2}/(1 + r e^{iθ}) dr`. -/
theorem erfc_eq_integral_rotate_laplace {θ : ℝ} (hθ : |θ| < π) {z : ℂ}
    (hz : |(z * exp (((θ / 2 : ℝ) : ℂ) * I)).im| < (z * exp (((θ / 2 : ℝ) : ℂ) * I)).re) :
    erfc z = exp (-z ^ 2) / π * (exp (θ * I) * ∫ r in Ioi (0 : ℝ),
      cexp (-(z ^ 2 * exp (θ * I) * r)) *
        (((r : ℂ) * exp (θ * I)) ^ (-1/2 : ℂ) * (1 + (r : ℂ) * exp (θ * I))⁻¹)) := by
  obtain ⟨c, hc0, hc⟩ := exists_pos_le_norm_one_add_ofReal_mul_exp hθ
  set ω := exp (((θ / 2 : ℝ) : ℂ) * I) with hω
  set U : Set ℂ := {z : ℂ | |(z * ω).im| < (z * ω).re} with hU
  have hUo : IsOpen U := isOpen_lt (by fun_prop) (by fun_prop)
  have hUc : Convex ℝ U := by
    intro x hx y hy a b ha hb hab
    have hx : |(x * ω).im| < (x * ω).re := hx
    have hy : |(y * ω).im| < (y * ω).re := hy
    show |((a • x + b • y) * ω).im| < ((a • x + b • y) * ω).re
    have hre : ((a • x + b • y) * ω).re = a * (x * ω).re + b * (y * ω).re := by
      simp only [add_mul, add_re, Complex.real_smul, mul_assoc, re_ofReal_mul]
    have him : ((a • x + b • y) * ω).im = a * (x * ω).im + b * (y * ω).im := by
      simp only [add_mul, add_im, Complex.real_smul, mul_assoc, im_ofReal_mul]
    rw [hre, him]
    rw [abs_lt] at hx hy ⊢
    rcases ha.lt_or_eq with ha | ha
    · constructor
      · nlinarith [mul_nonneg hb (by linarith [hy.1] : 0 ≤ (y * ω).re + (y * ω).im)]
      · nlinarith [mul_nonneg hb (by linarith [hy.2] : 0 ≤ (y * ω).re - (y * ω).im)]
    · subst ha; rw [zero_add] at hab; subst hab
      constructor <;> linarith [hy.1, hy.2]
  have hsq : ∀ z : ℂ, z ^ 2 * exp (θ * I) = (z * ω) ^ 2 := by
    intro z; rw [mul_pow, hω, ← Complex.exp_nat_mul]; push_cast; ring_nf
  have hUre : ∀ z ∈ U, 0 < (z ^ 2 * exp (θ * I)).re := by
    intro z hz
    have hz : |(z * ω).im| < (z * ω).re := hz
    rw [hsq, sq, mul_re]
    have h := abs_lt.mp hz
    nlinarith [abs_nonneg (z * ω).im]
  set K : ℂ → ℂ := fun t => t ^ (-1/2 : ℂ) * (1 + t)⁻¹ with hK
  have hKd : ∀ r : ℝ, 0 < r → ∀ y : ℝ, |y| ≤ |θ| →
      DifferentiableAt ℂ K ((r : ℂ) * exp (y * I)) := by
    intro r hr y hy
    have hm := ofReal_mul_exp_mem_slitPlane hr (lt_of_le_of_lt hy hθ)
    have hne : 1 + (r : ℂ) * exp (y * I) ≠ 0 := fun h0 => by
      have := hc r hr.le y hy; rw [h0, norm_zero] at this; linarith
    exact (differentiableAt_id.cpow (differentiableAt_const _) hm).mul
      (((differentiableAt_const _).add differentiableAt_id).inv hne)
  set G : ℝ → ℂ := fun r => K ((r : ℂ) * exp (θ * I)) with hG
  have hGc : ContinuousOn G (Ioi 0) := fun r hr =>
    ((hKd r hr θ le_rfl).continuousAt.comp (x := r)
      (f := fun r : ℝ => (r : ℂ) * exp (θ * I)) (by fun_prop)).continuousWithinAt
  have hLd := differentiableOn_integral_cexp_neg_mul_smul_of_le_rpow (G := G) (C := 1 / c)
    (D := 0) (k := -1/2) (by norm_num) hGc (fun r hr => by
      rw [add_zero]; exact norm_erfcKernel_le hc0 hc hθ hr le_rfl)
  simp only [smul_eq_mul] at hLd
  have hR : DifferentiableOn ℂ (fun z : ℂ => exp (-z ^ 2) / π * (exp (θ * I) *
      ∫ r in Ioi (0 : ℝ), cexp (-(z ^ 2 * exp (θ * I) * r)) * G r)) U := by
    refine (DifferentiableOn.div_const (by fun_prop) _).mul ((differentiableOn_const _).mul ?_)
    exact hLd.comp (by fun_prop : DifferentiableOn ℂ (fun z : ℂ => z ^ 2 * exp (θ * I)) U)
      (fun z hz => hUre z hz)
  have hd1 : Differentiable ℂ erfc := by
    unfold erfc; exact differentiable_const _ |>.sub differentiable_erf_complex
  -- agreement near `z₀ = e^{-iθ/4}`
  have hagree : ∀ w : ℂ, |w.im| < w.re → w ∈ U → erfc w = exp (-w ^ 2) / π *
      (exp (θ * I) * ∫ r in Ioi (0 : ℝ), cexp (-(w ^ 2 * exp (θ * I) * r)) * G r) := by
    intro w hw hwU
    have hw1 : 0 < w.re := lt_of_le_of_lt (abs_nonneg _) hw
    have hw2 : 0 < (w ^ 2).re := by
      rw [sq, mul_re]; have h := abs_lt.mp hw; nlinarith [abs_nonneg w.im]
    rw [erfc_eq_laplace hw1 hw2]
    congr 1
    have hlap : (∫ t : ℝ in Ioi 0, exp (-w ^ 2 * t) * (t : ℂ) ^ (-1/2 : ℂ) * (1 + (t : ℂ)) ^ (-1 : ℂ)) =
        ∫ t : ℝ in Ioi 0, cexp (-(w ^ 2 * t)) * K t :=
      setIntegral_congr_fun measurableSet_Ioi fun t _ => by
        rw [hK]; simp only [cpow_neg_one]; ring_nf
    rw [hlap]
    refine integral_cexp_neg_mul_mul_eq_rotate (F := K) (σ := 1/2) (C := 1 / c) (k := -1/2)
      (by norm_num) (fun r hr y hy => hKd r hr y (abs_le_abs_of_mem_uIcc_zero hy))
      (fun r hr _ y hy => ?_) (fun r hr y hy => ?_)
      (fun y hy => re_mul_exp_pos_of_mem_uIcc_of_lt_pi hθ hw2 (hUre w hwU) hy)
    · rw [show (1/2 : ℝ) - 1 = -1/2 by norm_num]
      exact norm_erfcKernel_le hc0 hc hθ hr (abs_le_abs_of_mem_uIcc_zero hy)
    · exact norm_erfcKernel_le hc0 hc hθ (by linarith) (abs_le_abs_of_mem_uIcc_zero hy)
  set z₀ : ℂ := exp (((-(θ / 4)) : ℝ) * I) with hz₀
  have hθ4 : |θ / 4| < π / 4 := by rw [abs_div, abs_of_pos (by norm_num : (0:ℝ) < 4)]; linarith
  have hsec : ∀ u : ℝ, |u| < π / 4 → |(exp (u * I)).im| < (exp (u * I)).re := by
    intro u hu
    rw [exp_ofReal_mul_I_re, exp_ofReal_mul_I_im]
    have hu' := abs_lt.mp hu
    rcases le_total 0 u with h | h
    · rw [abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi h (by linarith))]
      rw [← Real.cos_pi_div_two_sub]
      have := Real.cos_lt_cos_of_nonneg_of_le_pi_div_two h (by linarith) (by linarith : u < π/2 - u)
      linarith
    · rw [abs_of_nonpos (Real.sin_nonpos_of_nonpos_of_neg_pi_le h (by linarith)),
        ← Real.sin_neg, ← Real.cos_neg u, ← Real.cos_pi_div_two_sub]
      have := Real.cos_lt_cos_of_nonneg_of_le_pi_div_two (by linarith) (by linarith)
        (by linarith : -u < π/2 - -u)
      linarith
  have hz₀a : |z₀.im| < z₀.re := hsec _ (by rwa [abs_neg])
  have hz₀U : z₀ ∈ U := by
    show |(z₀ * ω).im| < (z₀ * ω).re
    rw [hz₀, hω, ← Complex.exp_add, show ((-(θ / 4) : ℝ) : ℂ) * I + ((θ / 2 : ℝ) : ℂ) * I =
      ((θ / 4 : ℝ) : ℂ) * I by push_cast; ring]
    exact hsec _ hθ4
  have hev : erfc =ᶠ[𝓝 z₀] (fun z : ℂ => exp (-z ^ 2) / π * (exp (θ * I) *
      ∫ r in Ioi (0 : ℝ), cexp (-(z ^ 2 * exp (θ * I) * r)) * G r)) := by
    have hV : IsOpen {w : ℂ | |w.im| < w.re} := isOpen_lt (by fun_prop) continuous_re
    filter_upwards [hV.mem_nhds hz₀a, hUo.mem_nhds hz₀U] with w hw hwU
    exact hagree w hw hwU
  exact (hd1.differentiableOn.analyticOnNhd hUo).eqOn_of_preconnected_of_eventuallyEq
    (hR.analyticOnNhd hUo) hUc.isPreconnected hz₀U hev hz

/-- Sector-dependent next-term bounds from DLMF §7.12(i). -/
theorem erfc_remainder_bound {z : ℂ} (hz0 : z ≠ 0) (hz : |arg z| < π/2) (N : ℕ) :
    ‖erfcAsymptoticRemainder N z‖ ≤ (if |arg z| ≤ π/4 then 1 else 1/Real.sin (2*|arg z|))*‖exp (-z^2)/Real.sqrt π*poch (1/2) N/z^(2*N+1)‖ := by
  set α := arg z with hα
  set θ : ℝ := -2 * α with hθdef
  have hθ : |θ| < π := by
    rw [hθdef, abs_mul, abs_neg, abs_two]; linarith
  have hθ2 : θ / 2 = -α := by rw [hθdef]; ring
  set ω := exp (((θ / 2 : ℝ) : ℂ) * I) with hω
  set e := exp (θ * I) with he
  set s : ℝ := ‖z‖ with hs
  have hs0 : 0 < s := by rw [hs]; exact norm_pos_iff.mpr hz0
  have hzω : z * ω = (s : ℂ) := by
    conv_lhs => rw [← norm_mul_exp_arg_mul_I z]
    rw [hω, hθ2, mul_assoc, ← Complex.exp_add]
    push_cast
    simp [hs, hα]
  have hωne : ω ≠ 0 := Complex.exp_ne_zero _
  have hωn : ‖ω‖ = 1 := by rw [hω]; exact norm_exp_ofReal_mul_I _
  have heω : e = ω ^ 2 := by
    rw [he, hω, ← Complex.exp_nat_mul]; push_cast; ring_nf
  have hen : ‖e‖ = 1 := by rw [he]; exact norm_exp_ofReal_mul_I _
  have hz' : |(z * ω).im| < (z * ω).re := by
    rw [hzω, ofReal_im, ofReal_re, abs_zero]; exact hs0
  have hrep := erfc_eq_integral_rotate_laplace hθ hz'
  have hz2e : z ^ 2 * e = ((s ^ 2 : ℝ) : ℂ) := by
    rw [heω, ← mul_pow, hzω]; push_cast; ring
  -- the sector constant
  set L : ℝ := if |arg z| ≤ π/4 then 1 else Real.sin (2*|arg z|) with hL
  have hL0 : 0 < L := by
    rw [hL]; split_ifs with h
    · exact one_pos
    · push Not at h
      exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hLden : ∀ r : ℝ, 0 ≤ r → L ≤ ‖1 + (r : ℂ) * e‖ := by
    intro r hr
    rw [hL]; split_ifs with h
    · refine one_le_norm_one_add_ofReal_mul_exp hr ?_
      rw [← Real.cos_abs, hθdef, abs_mul, abs_neg, abs_two]
      exact Real.cos_nonneg_of_mem_Icc ⟨by linarith [abs_nonneg α, Real.pi_pos],
        by linarith⟩
    · have hsin2 : |Real.sin θ| = Real.sin (2 * |arg z|) := by
        have hpos : 0 ≤ Real.sin (2 * |arg z|) :=
          Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by linarith)
        have key : |Real.sin (-2 * α)| = |Real.sin (2 * |α|)| := by
          rcases le_total 0 α with h0 | h0
          · rw [abs_of_nonneg h0, neg_mul, Real.sin_neg, abs_neg]
          · rw [abs_of_nonpos h0]; ring_nf
        rw [hθdef, key, abs_of_nonneg hpos]
      rw [← hsin2]; exact abs_sin_le_norm_one_add_ofReal_mul_exp _ _
  have hden0 : ∀ r : ℝ, 0 ≤ r → 1 + (r : ℂ) * e ≠ 0 := fun r hr h0 => by
    have := hLden r hr; rw [h0, norm_zero] at this; linarith
  -- real moments
  set g : ℕ → ℝ → ℝ := fun n r => r ^ ((n : ℝ) - 1/2) * Real.exp (-(s ^ 2 * r)) with hg
  have hmom (n : ℕ) : (∫ r in Ioi (0:ℝ), g n r) = Real.Gamma (n+1/2) / s^(2*n+1) := by
    have hr0 : 0 < s ^ 2 := by positivity
    have := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (n:ℝ)+1/2) (by positivity) hr0
    rw [show (n:ℝ)+1/2-1 = (n:ℝ)-1/2 by ring] at this
    simp only [hg]
    rw [this, Real.div_rpow zero_le_one hr0.le, Real.one_rpow, ← Real.rpow_two,
      ← Real.rpow_mul hs0.le, show 2*((n:ℝ)+1/2) = ((2*n+1:ℕ):ℝ) by push_cast; ring,
      Real.rpow_natCast]
    ring
  have hint (n : ℕ) : IntegrableOn (g n) (Ioi 0) := by
    have := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := (n:ℝ)-1/2) (b := s ^ 2)
      (by have : (0:ℝ) ≤ n := Nat.cast_nonneg n; linarith) one_pos (by positivity)
    refine this.congr_fun (fun u _ => ?_) measurableSet_Ioi
    simp [hg, Real.rpow_one, neg_mul]
  -- pointwise decomposition
  set R : ℝ → ℂ := fun r => ω⁻¹ * (((r ^ (-1/2 : ℝ) * Real.exp (-(s ^ 2 * r)) : ℝ) : ℂ) *
    ((-((r : ℂ) * e)) ^ N * (1 + (r : ℂ) * e)⁻¹)) with hR
  have hpt : ∀ r ∈ Ioi (0 : ℝ), cexp (-(z ^ 2 * e * r)) *
      (((r : ℂ) * e) ^ (-1/2 : ℂ) * (1 + (r : ℂ) * e)⁻¹) =
      ∑ n ∈ Finset.range N, ω⁻¹ * (-e) ^ n * ((g n r : ℝ) : ℂ) + R r := by
    intro r hr
    have hr : (0 : ℝ) < r := hr
    have hd := hden0 r hr.le
    have hgeom : (1 + (r : ℂ) * e)⁻¹ =
        ∑ n ∈ Finset.range N, (-((r : ℂ) * e))^n + (-((r : ℂ) * e))^N * (1 + (r : ℂ) * e)⁻¹ := by
      have hgs := geom_sum_mul (-((r : ℂ) * e)) N
      have hS : (∑ n ∈ Finset.range N, (-((r : ℂ) * e))^n) * (1 + (r : ℂ) * e) =
          1 - (-((r : ℂ) * e))^N := by linear_combination (-1 : ℂ) * hgs
      have hS' : ∑ n ∈ Finset.range N, (-((r : ℂ) * e))^n =
          (1 - (-((r : ℂ) * e))^N) * (1 + (r : ℂ) * e)⁻¹ := by
        rw [← hS, mul_assoc, mul_inv_cancel₀ hd, mul_one]
      rw [hS']; ring
    have hcp : ((r : ℂ) * e) ^ (-1/2 : ℂ) = ((r ^ (-1/2 : ℝ) : ℝ) : ℂ) * ω⁻¹ := by
      rw [he, ofReal_mul_exp_cpow hr (by linarith [(abs_lt.mp hθ).1]) (abs_lt.mp hθ).2.le,
        Complex.ofReal_cpow hr.le, hω, ← Complex.exp_neg]
      push_cast
      ring_nf
    have hpow (n : ℕ) : r ^ ((n:ℝ) - 1/2) = r ^ (-1/2 : ℝ) * r ^ n := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hr]; ring_nf
    have hex : cexp (-(z ^ 2 * e * r)) = ((Real.exp (-(s ^ 2 * r)) : ℝ) : ℂ) := by
      rw [hz2e, Complex.ofReal_exp]; push_cast; ring_nf
    rw [hcp, hex, hgeom, hR]
    simp only [hg, hpow]
    push_cast
    rw [mul_add, mul_add, Finset.mul_sum, Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun n _ => ?_
      rw [neg_pow ((r : ℂ) * e), mul_pow, neg_pow e]; ring
    · ring
  have hTi : ∀ n, IntegrableOn (fun r : ℝ => ω⁻¹ * (-e) ^ n * ((g n r : ℝ) : ℂ)) (Ioi 0) :=
    fun n => ((hint n).ofReal).const_mul _
  have hTint : ∀ n, ∫ r in Ioi (0:ℝ), ω⁻¹ * (-e) ^ n * ((g n r : ℝ) : ℂ) =
      ω⁻¹ * (-e) ^ n * ((Real.Gamma (n+1/2) / s^(2*n+1) : ℝ) : ℂ) := by
    intro n; rw [integral_const_mul, integral_complex_ofReal, hmom]
  have hRb : ∀ r ∈ Ioi (0:ℝ), ‖R r‖ ≤ 1 / L * g N r := by
    intro r hr
    have hr : (0:ℝ) < r := hr
    rw [hR]; simp only
    rw [norm_mul, norm_inv, hωn, inv_one, one_mul, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (by positivity), norm_mul, norm_pow, norm_neg, norm_mul,
      Complex.norm_real, Real.norm_of_nonneg hr.le, hen, mul_one, norm_inv]
    have h1 := hLden r hr.le
    have h2 : ‖1 + (r : ℂ) * e‖⁻¹ ≤ 1 / L := by rw [one_div]; exact inv_anti₀ hL0 h1
    have hpow : r ^ ((N:ℝ) - 1/2) = r ^ (-1/2 : ℝ) * r ^ N := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hr]; ring_nf
    simp only [hg, hpow]
    have h0 : 0 ≤ r ^ (-1/2:ℝ) * Real.exp (-(s^2*r)) * r ^ N := by positivity
    calc r ^ (-1/2:ℝ) * Real.exp (-(s^2*r)) * (r ^ N * ‖1 + (r:ℂ) * e‖⁻¹)
        = (r ^ (-1/2:ℝ) * Real.exp (-(s^2*r)) * r ^ N) * ‖1 + (r:ℂ) * e‖⁻¹ := by ring
      _ ≤ (r ^ (-1/2:ℝ) * Real.exp (-(s^2*r)) * r ^ N) * (1 / L) := by gcongr
      _ = _ := by ring
  have hbi : IntegrableOn (fun r => 1 / L * g N r) (Ioi 0) := (hint N).const_mul _
  have hRc : ContinuousOn R (Ioi 0) := by
    intro r hr
    have hr : (0:ℝ) < r := hr
    have hd := hden0 r hr.le
    refine ContinuousAt.continuousWithinAt ?_
    rw [hR]
    refine continuousAt_const.mul (ContinuousAt.mul ?_ ?_)
    · exact Complex.continuous_ofReal.continuousAt.comp
        ((Real.continuousAt_rpow_const _ _ (Or.inl hr.ne')).mul (by fun_prop))
    · exact (by fun_prop : Continuous fun r : ℝ => (-((r:ℂ) * e)) ^ N).continuousAt.mul
        (ContinuousAt.inv₀ (by fun_prop) hd)
  have hRi : IntegrableOn R (Ioi 0) :=
    Integrable.mono' hbi (hRc.aestronglyMeasurable measurableSet_Ioi)
      ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall hRb))
  have hint2 : ∫ r in Ioi (0:ℝ), cexp (-(z ^ 2 * e * r)) *
      (((r : ℂ) * e) ^ (-1/2 : ℂ) * (1 + (r : ℂ) * e)⁻¹) =
      ∑ n ∈ Finset.range N, ω⁻¹ * (-e) ^ n * ((Real.Gamma (n+1/2) / s^(2*n+1) : ℝ) : ℂ) +
        ∫ r in Ioi (0:ℝ), R r := by
    rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_add
      (integrable_finsetSum _ fun n _ => hTi n) hRi, integral_finsetSum _ fun n _ => hTi n]
    simp only [hTint]
  have hRn := norm_integral_le_of_norm_le hbi
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall hRb))
  have hgN : ∫ r in Ioi (0:ℝ), 1 / L * g N r = 1 / L * (Real.Gamma (N+1/2) / s^(2*N+1)) := by
    rw [integral_const_mul, hmom]
  rw [hgN] at hRn
  -- assemble
  have hsqrt : ((Real.sqrt π : ℝ) : ℂ) * (Real.sqrt π : ℂ) = π := by
    exact_mod_cast Real.mul_self_sqrt Real.pi_pos.le
  have hsq0 : ((Real.sqrt π : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hzpow : ∀ n : ℕ, z ^ (2*n+1) = (s : ℂ) ^ (2*n+1) / ω ^ (2*n+1) := by
    intro n; rw [← hzω, mul_pow]; field_simp
  have hterm : ∀ n ∈ Finset.range N, exp (-z^2) / π * (e * (ω⁻¹ * (-e) ^ n *
      ((Real.Gamma (n+1/2) / s^(2*n+1) : ℝ) : ℂ))) =
      exp (-z^2) / Real.sqrt π * ((-1 : ℂ)^n * poch (1/2) n / z^(2*n+1)) := by
    intro n _
    rw [poch_half_eq_Gamma, hzpow, heω, neg_pow (ω^2)]
    have hs' : (s:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs0.ne'
    push_cast
    rw [← hsqrt]
    field_simp
    ring
  have hsum : exp (-z^2) / π * (e * ∑ n ∈ Finset.range N, ω⁻¹ * (-e) ^ n *
      ((Real.Gamma (n+1/2) / s^(2*n+1) : ℝ) : ℂ)) =
      exp (-z^2) / Real.sqrt π * ∑ n ∈ Finset.range N, (-1 : ℂ)^n * poch (1/2) n / z^(2*n+1) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl hterm
  have hmain : erfcAsymptoticRemainder N z = exp (-z^2) / π * (e * ∫ r in Ioi (0:ℝ), R r) := by
    rw [erfcAsymptoticRemainder, hrep, ← he, hint2, mul_add, mul_add, hsum]
    ring
  rw [hmain, norm_mul, norm_mul, hen, one_mul, norm_div, Complex.norm_real,
    Real.norm_of_nonneg Real.pi_pos.le]
  have hG0 : 0 < Real.Gamma (N+1/2) := Real.Gamma_pos_of_pos (by positivity)
  have hrhs : ‖exp (-z^2)/Real.sqrt π*poch (1/2) N/z^(2*N+1)‖ =
      ‖exp (-z^2)‖ / π * (Real.Gamma (N+1/2) / s^(2*N+1)) := by
    rw [poch_half_eq_Gamma, norm_div, norm_mul, norm_div, Complex.norm_real, Complex.norm_real,
      norm_pow, ← hs, Real.norm_of_nonneg (Real.sqrt_nonneg _),
      Real.norm_of_nonneg (by positivity : 0 ≤ Real.Gamma (N+1/2) / Real.sqrt π)]
    have h := Real.mul_self_sqrt Real.pi_pos.le
    have h0 : 0 < Real.sqrt π := Real.sqrt_pos.mpr Real.pi_pos
    field_simp
    rw [Real.sq_sqrt Real.pi_pos.le]
  rw [hrhs]
  have hc : (if |arg z| ≤ π/4 then (1:ℝ) else 1/Real.sin (2*|arg z|)) = 1 / L := by
    rw [hL]; split_ifs <;> simp
  rw [hc]
  calc ‖exp (-z^2)‖ / π * ‖∫ r in Ioi (0:ℝ), R r‖
      ≤ ‖exp (-z^2)‖ / π * (1 / L * (Real.Gamma (N+1/2) / s^(2*N+1))) := by gcongr
    _ = _ := by ring

/-- Real Laplace form of `erfc x` for `x > 0`. -/
theorem erfc_ofReal_eq_laplace {x : ℝ} (hx : 0 < x) :
    TauCeti.Real.erfc x = Real.exp (-x^2)/π *
      ∫ u in Ioi (0:ℝ), Real.exp (-(x^2*u)) * u^(-1/2:ℝ) * (1+u)^(-1:ℝ) := by
  have h := erfc_eq_laplace (z := (x:ℂ)) (by simpa using hx) (by rw [← ofReal_pow, ofReal_re]; positivity)
  have hk : (∫ t : ℝ in Ioi 0, exp (-(x:ℂ)^2*t) * (t:ℂ)^(-1/2:ℂ) * (1+(t:ℂ))^(-1:ℂ)) =
      ((∫ u in Ioi (0:ℝ), Real.exp (-(x^2*u)) * u^(-1/2:ℝ) * (1+u)^(-1:ℝ) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht : (0:ℝ) < t := ht
    push_cast
    rw [ofReal_cpow ht.le, ofReal_cpow (by linarith)]
    push_cast; ring_nf
  have herfc : erfc (x:ℂ) = (TauCeti.Real.erfc x : ℂ) := by
    rw [erfc, erf_ofReal, TauCeti.Real.erfc_def]; push_cast; ring
  rw [hk, herfc] at h
  have := congrArg re h
  rw [ofReal_re] at this
  rw [this, show -(x:ℂ)^2 = ((-x^2:ℝ):ℂ) by push_cast; ring, ← ofReal_exp,
    show ((Real.exp (-x^2):ℂ)/(π:ℂ)) = ((Real.exp (-x^2)/π:ℝ):ℂ) by push_cast; ring,
    ← ofReal_mul, ofReal_re]

/-- Signed real remainder from DLMF §7.12(i). -/
theorem erfc_remainder_sign {x : ℝ} (hx : 0 < x) (N : ℕ) :
    0 ≤ (-1 : ℝ)^N*(erfcAsymptoticRemainder N x).re := by
  set r := x^2 with hr
  have hr0 : 0 < r := by positivity
  -- moments
  have hmom (n : ℕ) : (∫ u in Ioi (0:ℝ), u^((n:ℝ)-1/2) * Real.exp (-(r*u))) =
      Real.Gamma (n+1/2) / x^(2*n+1) := by
    have := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (n:ℝ)+1/2) (by positivity) hr0
    rw [show (n:ℝ)+1/2-1 = (n:ℝ)-1/2 by ring] at this
    rw [this, Real.div_rpow zero_le_one hr0.le, Real.one_rpow, hr, ← Real.rpow_two,
      ← Real.rpow_mul hx.le, show 2*((n:ℝ)+1/2) = ((2*n+1:ℕ):ℝ) by push_cast; ring,
      Real.rpow_natCast]
    ring
  have hint (n : ℕ) : IntegrableOn (fun u : ℝ => u^((n:ℝ)-1/2) * Real.exp (-(r*u))) (Ioi 0) := by
    have := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := (n:ℝ)-1/2) (b := r)
      (by have : (0:ℝ) ≤ n := Nat.cast_nonneg n; linarith) one_pos hr0
    refine this.congr_fun (fun u _ => ?_) measurableSet_Ioi
    simp [Real.rpow_one, neg_mul]
  set g : ℝ → ℝ := fun u => u^((N:ℝ)-1/2) * Real.exp (-(r*u)) * (1+u)⁻¹ with hg
  have hgint : IntegrableOn g (Ioi 0) := by
    refine (hint N).mono' ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable (fun u hu => ?_) measurableSet_Ioi
      have hu : (0:ℝ) < u := hu
      refine ContinuousAt.continuousWithinAt ?_
      have : 1 + u ≠ 0 := by linarith
      exact ((Real.continuousAt_rpow_const _ _ (Or.inl hu.ne')).mul (by fun_prop)).mul
        ((continuousAt_const.add continuousAt_id).inv₀ this)
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun u hu => ?_)
      have hu : (0:ℝ) < u := hu
      rw [Real.norm_of_nonneg (by positivity)]
      have h1 : (1+u)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
      have : 0 ≤ u^((N:ℝ)-1/2) * Real.exp (-(r*u)) := by positivity
      simp only [hg]
      nlinarith
  have hgnn : 0 ≤ ∫ u in Ioi (0:ℝ), g u :=
    setIntegral_nonneg measurableSet_Ioi fun u hu => by
      have hu : (0:ℝ) < u := hu; positivity
  -- the kernel decomposition
  have hdec : (∫ u in Ioi (0:ℝ), Real.exp (-(x^2*u)) * u^(-1/2:ℝ) * (1+u)^(-1:ℝ)) =
      ∑ n ∈ Finset.range N, (-1:ℝ)^n * (Real.Gamma (n+1/2) / x^(2*n+1)) +
        (-1:ℝ)^N * ∫ u in Ioi (0:ℝ), g u := by
    have hpt : ∀ u ∈ Ioi (0:ℝ), Real.exp (-(x^2*u)) * u^(-1/2:ℝ) * (1+u)^(-1:ℝ) =
        ∑ n ∈ Finset.range N, (-1:ℝ)^n * (u^((n:ℝ)-1/2) * Real.exp (-(r*u))) + (-1:ℝ)^N * g u := by
      intro u hu
      have hu : (0:ℝ) < u := hu
      have hgeom : (1+u)⁻¹ = ∑ n ∈ Finset.range N, (-u)^n + (-u)^N * (1+u)⁻¹ := by
        have h := geom_sum_mul (-u) N
        have h1 : 1 + u ≠ 0 := by linarith
        have hS : (∑ n ∈ Finset.range N, (-u)^n) = (1 - (-u)^N) * (1+u)⁻¹ := by
          rw [eq_mul_inv_iff_mul_eq₀ h1]; linear_combination (-1)*h
        rw [hS]; ring
      have hpow (n : ℕ) : u^((n:ℝ)-1/2) = u^(-1/2:ℝ) * u^n := by
        rw [← Real.rpow_natCast, ← Real.rpow_add hu]; ring_nf
      rw [Real.rpow_neg_one, hgeom, mul_add, Finset.mul_sum]
      simp only [hg, hpow, hr]
      congr 1
      · refine Finset.sum_congr rfl fun n _ => ?_; rw [neg_pow]; ring
      · rw [neg_pow]; ring
    rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_add, integral_finsetSum]
    · congr 1
      · refine Finset.sum_congr rfl fun n _ => ?_
        rw [integral_const_mul, hmom]
      · rw [integral_const_mul]
    · exact fun n _ => (hint n).const_mul _
    · exact integrable_finsetSum _ fun n _ => (hint n).const_mul _
    · exact hgint.const_mul _
  -- the remainder
  have hR : (erfcAsymptoticRemainder N x).re = Real.exp (-x^2)/π * ((-1:ℝ)^N * ∫ u in Ioi (0:ℝ), g u) := by
    have hsum : (exp (-(x:ℂ)^2)/Real.sqrt π*∑ n ∈ Finset.range N, (-1 : ℂ)^n*poch (1/2) n/(x:ℂ)^(2*n+1)) =
        ((Real.exp (-x^2)/π * ∑ n ∈ Finset.range N, (-1:ℝ)^n * (Real.Gamma (n+1/2) / x^(2*n+1)) : ℝ) : ℂ) := by
      simp only [poch_half_eq_Gamma]
      push_cast
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      have hp : (Real.sqrt π:ℂ)*Real.sqrt π = π := by exact_mod_cast Real.mul_self_sqrt Real.pi_pos.le
      have hp0 : (Real.sqrt π:ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
      rw [← hp]; field_simp
    have herfc : erfc (x:ℂ) = (TauCeti.Real.erfc x : ℂ) := by
      rw [erfc, erf_ofReal, TauCeti.Real.erfc_def]; push_cast; ring
    rw [erfcAsymptoticRemainder, hsum, herfc, ← ofReal_sub, ofReal_re, erfc_ofReal_eq_laplace hx, hdec]
    ring
  rw [hR, ← mul_assoc, mul_comm ((-1:ℝ)^N), mul_assoc, ← mul_assoc ((-1:ℝ)^N), ← pow_add,
    ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]
  have : 0 ≤ Real.exp (-x^2)/π := by positivity
  exact mul_nonneg this hgnn

end DLMF.Confluent
end
