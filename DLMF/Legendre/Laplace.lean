/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Legendre.SecondKind
public import DLMF.OrthogonalPolynomials.Legendre

/-!
# Laplace's integral for `P_ν` (Temme §8.6)

Gauss's quadratic transformation and Pfaff's transformation give
`P_ν(z) = z^ν F(-ν/2, (1-ν)/2; 1; 1 - 1/z²)` near `(1, √2)`, and the identity principle extends
it to `Re z > 0`. For real `x ≥ 1`, write `x + √(x²-1) cos φ = x (1 + r cos φ)` with
`r² = 1 - 1/x² < 1`; integrating the binomial series termwise and using
`∫₀^π cos^{2m} = π (2m)!/(4^m m!²)` and `(a)₂ₘ = 4^m (a/2)ₘ ((a+1)/2)ₘ` gives Laplace's first
integral `P_ν(x) = π⁻¹ ∫₀^π (x + √(x²-1) cos φ)^ν dφ` for every complex `ν`.
-/

@[expose] public section

open Complex Filter Set DLMF.Hypergeometric
open scoped Topology Real

noncomputable section

namespace DLMF.Legendre

/-- For `Re z > 0`, `1 - 1/z²` lies in the cut plane. -/
theorem one_sub_recip_sq_mem_cutPlane {z : ℂ} (hz : 0 < z.re) : 1 - 1 / z ^ 2 ∈ cutPlane := by
  rw [mem_cutPlane, sub_sub_cancel, one_div]
  exact recip_mem_slitPlane' (Complex.sq_mem_slitPlane_of_re_pos hz)

/-- Near `x ∈ (1, √2)`, Gauss's quadratic transformation and Pfaff's transformation give
`P_ν(x) = x^ν F(-ν/2, (1-ν)/2; 1; 1 - 1/x²)`. -/
theorem legendreP_eq_pfaff_real (ν : ℂ) {x : ℝ} (hx1 : 1 < x) (hx2 : x ^ 2 < 2) :
    legendreP ν x = (x : ℂ) ^ ν *
      regularizedGaussHG (-ν / 2) ((1 - ν) / 2) 1 (1 - 1 / (x : ℂ) ^ 2) := by
  have h1 : ∀ k : ℕ, (1 : ℂ) ≠ -(k : ℂ) := fun k h => by
    have := congrArg re h; simp at this; linarith [(k.cast_nonneg : (0:ℝ) ≤ k)]
  set w : ℂ := (1 - x) / 2 with hw
  have hwn : ‖w‖ < 1 := by
    rw [hw, show (1 - (x : ℂ)) / 2 = ((1 - x) / 2 : ℝ) by push_cast; ring, norm_real,
      Real.norm_eq_abs, abs_lt]
    constructor <;> nlinarith
  have hq : 4 * w * (1 - w) = ((1 - x ^ 2 : ℝ) : ℂ) := by rw [hw]; push_cast; ring
  have hqn : ‖4 * w * (1 - w)‖ < 1 := by
    rw [hq, norm_real, Real.norm_eq_abs, abs_lt]; constructor <;> nlinarith
  have hre : w.re < 1 / 2 := by rw [hw]; simp; linarith
  have hG := gauss_quadratic (a := -ν / 2) (b := (ν + 1) / 2)
    (by rw [show -ν / 2 + (ν + 1) / 2 + 1 / 2 = 1 by ring]; exact h1) hwn hqn hre
  rw [show 2 * (-ν / 2) = -ν by ring, show 2 * ((ν + 1) / 2) = ν + 1 by ring,
    show -ν / 2 + (ν + 1) / 2 + 1 / 2 = 1 by ring] at hG
  have hx0 : (0 : ℝ) < x := by linarith
  have hu : ((1 - x ^ 2 : ℝ) : ℂ) ∈ cutPlane := by
    rw [mem_cutPlane, show (1 : ℂ) - ((1 - x ^ 2 : ℝ) : ℂ) = ((x ^ 2 : ℝ) : ℂ) by push_cast; ring]
    exact Or.inl (by simp only [ofReal_re]; positivity)
  have hpf := regularizedGaussHG_pfaff (-ν / 2) ((ν + 1) / 2) 1 hu
  have hu1 : ‖((1 - x ^ 2 : ℝ) : ℂ)‖ < 1 := by rw [← hq]; exact hqn
  have e1 : legendreP ν x = ₂F₁ (-ν) (ν + 1) 1 w := by
    rw [ordinaryHypergeometric_eq_Gamma_mul_regularizedGaussHG h1 hwn, Gamma_one, one_mul]; rfl
  have e2 : ₂F₁ (-ν / 2) ((ν + 1) / 2) 1 (((1 - x ^ 2 : ℝ) : ℂ)) =
      regularizedGaussHG (-ν / 2) ((ν + 1) / 2) 1 (((1 - x ^ 2 : ℝ) : ℂ)) := by
    rw [ordinaryHypergeometric_eq_Gamma_mul_regularizedGaussHG h1 hu1, Gamma_one, one_mul]
  have hxc : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx0.ne'
  have hpow : (1 - ((1 - x ^ 2 : ℝ) : ℂ)) ^ (-(-ν / 2)) = (x : ℂ) ^ ν := by
    rw [show (1 - ((1 - x ^ 2 : ℝ) : ℂ)) = (x : ℂ) ^ (2 : ℕ) by push_cast; ring,
      ← cpow_natCast, ← cpow_mul _ (by simp [log_im, arg_ofReal_of_nonneg hx0.le]; positivity)
        (by simp [log_im, arg_ofReal_of_nonneg hx0.le]; positivity)]
    congr 1; push_cast; ring
  have harg : ((1 - x ^ 2 : ℝ) : ℂ) / (((1 - x ^ 2 : ℝ) : ℂ) - 1) = 1 - 1 / (x : ℂ) ^ 2 := by
    push_cast; field_simp; ring
  rw [e1, hG, hq, e2, hpf, hpow, harg, show 1 - (ν + 1) / 2 = (1 - ν) / 2 by ring]


/-- `P_ν(z) = z^ν 𝐅(-ν/2, (1-ν)/2; 1; 1 - 1/z²)` for `Re z > 0`, from Gauss's quadratic
transformation (DLMF 15.8.18) and Pfaff's transformation, extended by the identity principle. -/
theorem legendreP_eq_cpow_mul (ν : ℂ) {z : ℂ} (hz : 0 < z.re) :
    legendreP ν z = z ^ ν * regularizedGaussHG (-ν / 2) ((1 - ν) / 2) 1 (1 - 1 / z ^ 2) := by
  set U : Set ℂ := {z | 0 < z.re}
  have hU : IsPreconnected U := (convex_halfSpace_re_gt 0).isPreconnected
  have hf : AnalyticOnNhd ℂ (legendreP ν) U := by
    intro w hw
    have hs : 1 + w ∈ slitPlane := Or.inl (by simp; linarith [show 0 < w.re from hw])
    exact (analyticAt_regularizedGaussHG _ _ _ (mem_cutPlane_of_one_add hs)).comp_of_eq
      (by fun_prop) rfl
  have hg : AnalyticOnNhd ℂ
      (fun z : ℂ => z ^ ν * regularizedGaussHG (-ν / 2) ((1 - ν) / 2) 1 (1 - 1 / z ^ 2)) U := by
    intro w hw
    have hw0 : w ≠ 0 := by rintro rfl; simp [U] at hw
    exact (analyticAt_id.cpow analyticAt_const (Or.inl hw)).mul
      ((analyticAt_regularizedGaussHG _ _ _ (one_sub_recip_sq_mem_cutPlane hw)).comp_of_eq
        (by fun_prop (disch := exact pow_ne_zero 2 hw0)) rfl)
  have hx0 : ((6 / 5 : ℝ) : ℂ) ∈ U := by simp [U]
  refine hf.eqOn_of_preconnected_of_frequently_eq hg hU hx0 ?_ hz
  have ht : Tendsto (fun r : ℝ => (r : ℂ)) (𝓝[≠] (6 / 5 : ℝ)) (𝓝[≠] ((6 / 5 : ℝ) : ℂ)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · exact (continuous_ofReal.tendsto _).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r hr
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff, ofReal_inj] using hr
  apply ht.frequently
  apply Eventually.frequently
  filter_upwards [nhdsWithin_le_nhds (Ioo_mem_nhds (show (1 : ℝ) < 6 / 5 by norm_num)
    (show (6 / 5 : ℝ) < 7 / 5 by norm_num))] with r hr
  exact legendreP_eq_pfaff_real ν hr.1 (by nlinarith [hr.1, hr.2])


/-- Duplication for Pochhammer symbols: `(a)₂ₘ = 4ᵐ (a/2)ₘ ((a+1)/2)ₘ`. -/
theorem poch_two_mul (a : ℂ) (m : ℕ) :
    poch a (2 * m) = 4 ^ m * poch (a / 2) m * poch ((a + 1) / 2) m := by
  induction m with
  | zero => simp [poch_zero]
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, poch_succ, poch_succ, ih, poch_succ, poch_succ]
    push_cast
    ring

/-- The regularized Gauss series as a `HasSum` on the unit disk. -/
theorem hasSum_regularizedGaussHGFun (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => (ascPochhammer ℂ n).eval a * (ascPochhammer ℂ n).eval b * z ^ n /
      n.factorial * (Gamma (c + n))⁻¹) (regularizedGaussHGFun a b c z) := by
  rw [regularizedGaussHGFun_eq_tsum]
  exact (summable_regularizedGaussHGFun_term a b c hz).hasSum

/-- The binomial series `(1+t)^ν = ∑ (-ν)ₙ (-t)ⁿ / n!` for `|t| < 1`. -/
theorem hasSum_one_add_cpow (ν : ℂ) {t : ℂ} (ht : ‖t‖ < 1) :
    HasSum (fun n : ℕ => poch (-ν) n * (-t) ^ n / n.factorial) ((1 + t) ^ ν) := by
  have h1 : ∀ k : ℕ, (1 : ℂ) ≠ -(k : ℂ) := fun k h => by
    have := congrArg re h; simp at this; linarith [(k.cast_nonneg : (0:ℝ) ≤ k)]
  have ht' : ‖-t‖ < 1 := by rwa [norm_neg]
  have h := hasSum_regularizedGaussHGFun (-ν) 1 1 ht'
  rw [regularizedGaussHGFun_eq_div_Gamma h1, Gamma_one, div_one,
    ordinaryHypergeometric_eq_one_sub_neg_cpow (fun k h => h1 k (by rw [h]; ring)) ht',
    sub_neg_eq_add,
    neg_neg] at h
  refine h.congr_fun fun n => ?_
  rw [show (1 : ℂ) + n = ((n : ℕ) : ℂ) + 1 by ring, Gamma_nat_eq_factorial]
  have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  simp only [poch, ascPochhammer_eval_one]
  field_simp


/-- `∫₀^π (1 + r cos φ)^ν dφ = π 𝐅(-ν/2, (1-ν)/2; 1; r²)` for `0 ≤ r < 1`, by termwise
integration of the binomial series. -/
theorem integral_one_add_mul_cos_cpow (ν : ℂ) {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) :
    ∫ φ in (0 : ℝ)..π, (((1 + r * Real.cos φ : ℝ)) : ℂ) ^ ν =
      π * regularizedGaussHGFun (-ν / 2) ((1 - ν) / 2) 1 ((r : ℂ) ^ 2) := by
  set F : ℕ → ℝ → ℂ := fun n φ => poch (-ν) n * (-((r * Real.cos φ : ℝ) : ℂ)) ^ n /
    n.factorial with hF
  have hlim (φ : ℝ) : HasSum (fun n => F n φ) ((((1 + r * Real.cos φ : ℝ)) : ℂ) ^ ν) := by
    have hn : ‖((r * Real.cos φ : ℝ) : ℂ)‖ < 1 := by
      rw [norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg hr0]
      calc r * |Real.cos φ| ≤ r * 1 := by gcongr; exact Real.abs_cos_le_one φ
        _ < 1 := by linarith
    have h := hasSum_one_add_cpow ν hn
    simp only [hF]
    push_cast at h ⊢
    exact h
  have hsb : Summable fun n : ℕ => ‖poch (-ν) n‖ * r ^ n / n.factorial := by
    have h := (hasSum_one_add_cpow ν (t := -(r : ℂ)) (by
      rw [norm_neg, norm_real, Real.norm_of_nonneg hr0]; exact hr)).summable.norm
    refine h.congr fun n => ?_
    rw [neg_neg, norm_div, norm_mul, norm_pow, norm_real, Real.norm_of_nonneg hr0,
      Complex.norm_natCast]
  have hint := intervalIntegral.hasSum_integral_of_dominated_convergence
    (μ := MeasureTheory.volume) (a := 0) (b := π) (F := F)
    (f := fun φ : ℝ => (((1 + r * Real.cos φ : ℝ)) : ℂ) ^ ν)
    (fun n _ => ‖poch (-ν) n‖ * r ^ n / n.factorial)
    (fun n => (by simp only [hF]; fun_prop : Continuous (F n)).aestronglyMeasurable)
    (fun n => Eventually.of_forall fun φ _ => by
      simp only [hF, norm_div, norm_mul, norm_pow, norm_neg, norm_real, Real.norm_eq_abs,
        Complex.norm_natCast, abs_of_nonneg hr0]
      gcongr
      calc r * |Real.cos φ| ≤ r * 1 := by gcongr; exact Real.abs_cos_le_one φ
        _ = r := mul_one r)
    (Eventually.of_forall fun _ _ => hsb) intervalIntegrable_const
    (Eventually.of_forall fun φ _ => hlim φ)
  have hterm (n : ℕ) : ∫ φ in (0 : ℝ)..π, F n φ =
      poch (-ν) n * (-(r : ℂ)) ^ n / n.factorial *
        ((∫ φ in (0 : ℝ)..π, Real.cos φ ^ n : ℝ) : ℂ) := by
    have hfun : F n = fun φ : ℝ => (poch (-ν) n * (-(r : ℂ)) ^ n / n.factorial) *
        ((Real.cos φ ^ n : ℝ) : ℂ) := by
      funext φ; simp only [hF]; push_cast; ring
    rw [hfun, intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal]
  simp only [hterm] at hint
  -- only even indices contribute
  have hodd : ∀ n ∉ Set.range (fun m : ℕ => 2 * m), poch (-ν) n * (-(r : ℂ)) ^ n /
      n.factorial * ((∫ φ in (0 : ℝ)..π, Real.cos φ ^ n : ℝ) : ℂ) = 0 := by
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m + 1 := by
      rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
      · exact absurd ⟨m, by simp only; omega⟩ hn
      · exact ⟨m, hm⟩
    rw [DLMF.OrthogonalPolynomials.integral_cos_pow_odd_zero_pi]; simp
  have heven := ((mul_right_injective₀ (two_ne_zero : (2 : ℕ) ≠ 0)).hasSum_iff hodd).mpr hint
  have htarget := (hasSum_regularizedGaussHGFun (-ν / 2) ((1 - ν) / 2) 1
    (z := (r : ℂ) ^ 2) (by rw [norm_pow, norm_real, Real.norm_of_nonneg hr0]; nlinarith)).mul_left
    (π : ℂ)
  refine heven.unique (htarget.congr_fun fun m => ?_)
  simp only [Function.comp]
  rw [DLMF.OrthogonalPolynomials.integral_cos_pow_even_zero_pi, poch_two_mul,
    show (-ν + 1) / 2 = (1 - ν) / 2 by ring, show (1 : ℂ) + m = ((m : ℕ) : ℂ) + 1 by ring,
    Gamma_nat_eq_factorial]
  have hf : ((2 * m).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hf' : (m.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hm1 : ((-1 : ℂ)) ^ (2 * m) = 1 := by rw [pow_mul]; norm_num
  rw [neg_pow, hm1, one_mul]
  simp only [poch]
  push_cast
  field_simp
  ring


/-- **Laplace's first integral** `P_ν(x) = π⁻¹ ∫₀^π (x + √(x²-1) cos φ)^ν dφ` for real `x ≥ 1`
and every complex `ν` (Temme §8.6). -/
theorem legendreP_laplace (ν : ℂ) {x : ℝ} (hx : 1 ≤ x) :
    legendreP ν x =
      1 / π * ∫ φ in (0 : ℝ)..π, (((x + Real.sqrt (x ^ 2 - 1) * Real.cos φ : ℝ)) : ℂ) ^ ν := by
  have hx0 : (0 : ℝ) < x := by linarith
  set r := Real.sqrt (1 - 1 / x ^ 2) with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r ^ 2 = 1 - 1 / x ^ 2 := Real.sq_sqrt (by
    rw [sub_nonneg, div_le_one (by positivity)]; nlinarith)
  have hr1 : r < 1 := by
    have h1 : 0 < 1 / x ^ 2 := by positivity
    have h2 : r ^ 2 < 1 := by rw [hr2]; linarith
    nlinarith
  have hsx : Real.sqrt (x ^ 2 - 1) = x * r := by
    rw [hr, show x ^ 2 - 1 = x ^ 2 * (1 - 1 / x ^ 2) by field_simp,
      Real.sqrt_mul (sq_nonneg x), Real.sqrt_sq hx0.le]
  have hint : ∫ φ in (0 : ℝ)..π, (((x + Real.sqrt (x ^ 2 - 1) * Real.cos φ : ℝ)) : ℂ) ^ ν =
      (x : ℂ) ^ ν * ∫ φ in (0 : ℝ)..π, (((1 + r * Real.cos φ : ℝ)) : ℂ) ^ ν := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun φ _ => ?_
    have hpos : 0 ≤ 1 + r * Real.cos φ := by
      nlinarith [Real.neg_one_le_cos φ, Real.cos_le_one φ]
    rw [hsx, show x + x * r * Real.cos φ = x * (1 + r * Real.cos φ) by ring, ofReal_mul,
      mul_cpow_ofReal_nonneg hx0.le hpos]
  have hrc : ‖((r : ℂ)) ^ 2‖ < 1 := by
    rw [norm_pow, norm_real, Real.norm_of_nonneg hr0]; nlinarith
  rw [hint, integral_one_add_mul_cos_cpow ν hr0 hr1,
    legendreP_eq_cpow_mul ν (by simpa using hx0)]
  have harg : 1 - 1 / (x : ℂ) ^ 2 = (r : ℂ) ^ 2 := by
    rw [show (r : ℂ) ^ 2 = ((r ^ 2 : ℝ) : ℂ) by push_cast; ring, hr2]; push_cast; ring
  rw [harg, regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hrc]
  have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp

end DLMF.Legendre

end
