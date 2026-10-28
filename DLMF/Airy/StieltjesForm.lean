/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Hypergeometric.EulerIntegral
public import DLMF.Hypergeometric.Derivatives
public import DLMFMathlib.Analysis.Complex.ParametricHolomorphy
public import DLMFMathlib.Analysis.Asymptotics.StieltjesRemainder
public import TauCeti.Analysis.SpecialFunctions.Beta
public import Mathlib.MeasureTheory.Integral.Gamma
public import DLMFMathlib.Analysis.SpecialFunctions.Complex.ArgLog

/-!
# The binomial in Stieltjes–Euler form, for the Airy error bounds

For `0 < a < 1` and `1 + t` in the slit plane,

  `(1+t)^{-a} = (Γ(a)Γ(1-a))⁻¹ ∫₀¹ τ^{a-1}(1-τ)^{-a} (1 + tτ)⁻¹ dτ`

(Euler's integral for `₂F₁(1, a; 1; -t)`, continued from the unit disc by the identity theorem),
and the remainder of the binomial expansion after `N` terms is
`(-t)^N (Γ(a)Γ(1-a))⁻¹ ∫₀¹ τ^{N+a-1}(1-τ)^{-a} (1 + tτ)⁻¹ dτ`. On a ray `t = r e^{iθ}`,
`|θ| < π`, the factor `(1 + tτ)⁻¹` is bounded by `1` for `cos θ ≥ 0` and by `|csc θ|` otherwise.
These give Olver's multipliers `1` and `|csc(ph ζ)|` in DLMF 9.7.17 (Olver, *Asymptotics and
Special Functions*, Ch. 7 §§3–4; Nemes 2017b).

## Main results

* `airySt_binom`: the Stieltjes–Euler form of `(1+t)^{-a}`.
* `airySt_binom_rem`: the exact remainder of the binomial expansion.
* `airySt_factor_bound`: the ray bound of the remainder factor.
* `airySt_rem_le_M`, `airySt_rem_le_chi`: the remainder of the ray Laplace integral
  `∫₀^∞ e^{-Wr} t^{b-1}(1+t)^{-a} dr`, `t = r e^{iθ}`, after `N` terms is at most `M_θ` and at
  most `χ(N+b) + 1` times the first neglected term (Olver Ch. 7 §§3–4; Boyd's method for χ).

Helper names carry the prefix `airySt_`.
-/

@[expose] public noncomputable section

open MeasureTheory Set Finset Complex Filter DLMF.Hypergeometric
open scoped Real Topology

namespace DLMF.Airy

/-- The Euler weight `τ^{a-1} (1-τ)^{-a}`. -/
def airySt_w (a τ : ℝ) : ℝ := τ ^ (a - 1) * (1 - τ) ^ (-a)

/-- The Euler weight `τ^{a-1}(1-τ)^{-a}` is nonnegative on `(0,1)`. -/
theorem airySt_w_nonneg (a : ℝ) {τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1) : 0 ≤ airySt_w a τ := by
  have := hτ.1; have : 0 < 1 - τ := by linarith [hτ.2]
  unfold airySt_w; positivity

/-- `τ^k` times the Euler weight is the Beta integrand `τ^{(a+k)-1}(1-τ)^{(1-a)-1}`. -/
theorem airySt_w_pow {a : ℝ} (k : ℕ) {τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1) :
    τ ^ k * airySt_w a τ = τ ^ ((a + k) - 1) * (1 - τ) ^ ((1 - a) - 1) := by
  unfold airySt_w
  rw [show (a + k) - 1 = (a - 1) + k by ring, Real.rpow_add hτ.1, Real.rpow_natCast,
    show (1 - a) - 1 = -a by ring]
  ring

/-- For `0 < a < 1`, `τ^k τ^{a-1}(1-τ)^{-a}` is integrable on `(0,1)`. -/
theorem airySt_integrableOn_w {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (k : ℕ) :
    IntegrableOn (fun τ : ℝ => τ ^ k * airySt_w a τ) (Ioo 0 1) := by
  have h := (TauCeti.intervalIntegrable_rpow_mul_one_sub_rpow (a := a + k) (b := 1 - a)
    (by positivity) (by linarith) (u := 0) (v := 1) (by simp) (by simp))
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one] at h
  exact h.congr_fun (fun τ hτ => (airySt_w_pow k hτ).symm) measurableSet_Ioo

/-- The moments of the Euler weight: `∫₀¹ τ^k w = Γ(a+k)Γ(1-a)/Γ(k+1)`. -/
theorem airySt_moment {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (k : ℕ) :
    ∫ τ in Ioo (0 : ℝ) 1, τ ^ k * airySt_w a τ =
      Real.Gamma (a + k) * Real.Gamma (1 - a) / Real.Gamma (k + 1) := by
  have h := TauCeti.integral_rpow_mul_one_sub_rpow (a := a + k) (b := 1 - a) (by positivity)
    (by linarith)
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo] at h
  rw [setIntegral_congr_fun measurableSet_Ioo (fun τ hτ => airySt_w_pow k hτ), h,
    ProbabilityTheory.beta]
  congr 2; ring

/-- `1 + tτ ≠ 0` for `τ ∈ [0,1]` when `1 + t ∈ slitPlane`. -/
theorem airySt_one_add_mul_mem {t : ℂ} (ht : 1 + t ∈ slitPlane) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) 1) :
    1 + t * τ ∈ slitPlane := by
  have h := (starConvex_ofReal_slitPlane (x := 1) one_pos) ht (a := 1 - τ) (b := τ)
    (by linarith [hτ.2]) hτ.1 (by ring)
  convert h using 1
  simp only [real_smul]; push_cast; ring

/-- The Euler form of the binomial on the unit disc. -/
theorem airySt_binom_disc {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {t : ℂ} (ht : ‖t‖ < 1) :
    (1 + t) ^ (-(a : ℂ)) = (1 / (Real.Gamma a * Real.Gamma (1 - a)) : ℝ) *
      ∫ τ in Ioo (0 : ℝ) 1, (airySt_w a τ : ℂ) * (1 + t * τ)⁻¹ := by
  have h1 := ordinaryHypergeometric_eq_one_sub_neg_cpow (a := (a : ℂ)) (c := 1) (z := -t)
    (fun k hk => by have := congrArg Complex.re hk; simp at this; linarith [(k.cast_nonneg : (0:ℝ) ≤ k)])
    (by simpa using ht)
  rw [sub_neg_eq_add] at h1
  rw [← h1, ordinaryHypergeometric_symm,
    ordinaryHypergeometric_eq_integral (by simpa using ha0) (by simp; linarith) (by simpa using ht)]
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo,
    Complex.Gamma_one, show (1 : ℂ) - a = ((1 - a : ℝ) : ℂ) by push_cast; ring,
    Complex.Gamma_ofReal, Complex.Gamma_ofReal]
  congr 1
  · push_cast; ring
  · refine setIntegral_congr_fun measurableSet_Ioo fun τ hτ => ?_
    have h0 : (0 : ℝ) ≤ τ := hτ.1.le
    have h1 : (0 : ℝ) ≤ 1 - τ := by linarith [hτ.2]
    simp only [airySt_w]
    push_cast
    rw [ofReal_cpow h0, ofReal_cpow h1, cpow_neg_one]
    push_cast
    ring_nf

/-- The Stieltjes integral `∫₀¹ τ^{a-1}(1-τ)^{-a} (1 + uτ)⁻¹ dτ` is holomorphic in `u` on the
set where `1 + u` lies in the slit plane. -/
private lemma airySt_stieltjes_analyticOnNhd {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    AnalyticOnNhd ℂ (fun u : ℂ => ∫ τ in Ioo (0 : ℝ) 1, (airySt_w a τ : ℂ) * (1 + u * τ)⁻¹)
      {t : ℂ | 1 + t ∈ slitPlane} := by
  have hUo : IsOpen {t : ℂ | 1 + t ∈ slitPlane} := isOpen_slitPlane.preimage (by fun_prop)
  have hne : ∀ u ∈ {t : ℂ | 1 + t ∈ slitPlane}, ∀ τ ∈ Icc (0 : ℝ) 1, 1 + u * τ ≠ 0 :=
    fun u hu τ hτ => slitPlane_ne_zero (airySt_one_add_mul_mem hu hτ)
  have hwi : IntegrableOn (fun τ : ℝ => airySt_w a τ) (Ioo 0 1) := by
    simpa using airySt_integrableOn_w ha0 ha1 0
  refine DifferentiableOn.analyticOnNhd ?_ hUo
  refine Complex.differentiableOn_integral_of_locally_dominated hUo (fun u _ => ?_) ?_ ?_
  · exact ((Complex.continuous_ofReal.comp_aestronglyMeasurable hwi.aestronglyMeasurable).mul
      (by fun_prop : Measurable fun τ : ℝ => (1 + u * τ)⁻¹).aestronglyMeasurable)
  · refine (ae_restrict_iff' measurableSet_Ioo).mpr (Filter.Eventually.of_forall fun τ hτ => ?_)
    intro u hu
    have hd : DifferentiableAt ℂ (fun v : ℂ => 1 + v * (τ : ℂ)) u := by fun_prop
    exact ((differentiableAt_const _).mul (hd.inv
        (hne u hu τ (Ioo_subset_Icc_self hτ)))).differentiableWithinAt
  · intro u₀ hu₀
    obtain ⟨τ₀, hτ₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr zero_le_one)
      (f := fun τ : ℝ => ‖1 + u₀ * τ‖) (by fun_prop)
    set δ := ‖1 + u₀ * τ₀‖ with hδ
    have hδ0 : 0 < δ := norm_pos_iff.mpr (hne u₀ hu₀ τ₀ hτ₀)
    refine ⟨Metric.ball u₀ (δ / 2), Metric.ball_mem_nhds _ (by positivity),
      fun τ => airySt_w a τ * (2 / δ), hwi.mul_const _, ?_⟩
    refine (ae_restrict_iff' measurableSet_Ioo).mpr (Filter.Eventually.of_forall fun τ hτ => ?_)
    intro u hu
    have hτI : τ ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self hτ
    have hm : δ ≤ ‖1 + u₀ * τ‖ := hmin hτI
    have hd : ‖u - u₀‖ < δ / 2 := by simpa [dist_eq_norm] using hu
    have hlow : δ / 2 ≤ ‖1 + u * τ‖ := by
      have h1 : ‖1 + u₀ * τ‖ ≤ ‖1 + u * τ‖ + ‖(u - u₀) * τ‖ := by
        calc ‖1 + u₀ * τ‖ = ‖(1 + u * τ) - (u - u₀) * τ‖ := by ring_nf
          _ ≤ _ := norm_sub_le _ _
      have h2 : ‖(u - u₀) * (τ : ℂ)‖ ≤ ‖u - u₀‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hτI.1]
        exact mul_le_of_le_one_right (norm_nonneg _) hτI.2
      linarith
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (airySt_w_nonneg a hτ), norm_inv]
    refine mul_le_mul_of_nonneg_left ?_ (airySt_w_nonneg a hτ)
    rw [inv_le_comm₀ (by linarith) (by positivity)]
    calc (2 / δ)⁻¹ = δ / 2 := by field_simp
      _ ≤ _ := hlow

/-- **The binomial as a Stieltjes (Euler) integral**: for `0 < a < 1` and `1 + t` in the slit
plane, `(1+t)^{-a} = (Γ(a)Γ(1-a))⁻¹ ∫₀¹ τ^{a-1}(1-τ)^{-a} (1 + tτ)⁻¹ dτ`. -/
theorem airySt_binom {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {t : ℂ} (ht : 1 + t ∈ slitPlane) :
    (1 + t) ^ (-(a : ℂ)) = (1 / (Real.Gamma a * Real.Gamma (1 - a)) : ℝ) *
      ∫ τ in Ioo (0 : ℝ) 1, (airySt_w a τ : ℂ) * (1 + t * τ)⁻¹ := by
  set U : Set ℂ := {t : ℂ | 1 + t ∈ slitPlane} with hU
  have hUo : IsOpen U := isOpen_slitPlane.preimage (by fun_prop)
  have hUc : IsPreconnected U := by
    have : U = (fun w : ℂ => w - 1) '' slitPlane := by
      ext u; simp only [hU, mem_ofPred_eq, mem_image]
      constructor
      · intro h; exact ⟨1 + u, h, by ring⟩
      · rintro ⟨w, hw, rfl⟩; simpa using hw
    rw [this]
    exact (Complex.starConvex_one_slitPlane.isPathConnected one_mem_slitPlane).isConnected.isPreconnected.image _
      (by fun_prop : Continuous fun w : ℂ => w - 1).continuousOn
  have hf : AnalyticOnNhd ℂ (fun u : ℂ => (1 + u) ^ (-(a : ℂ))) U := by
    refine DifferentiableOn.analyticOnNhd (fun u hu => ?_) hUo
    exact ((differentiableAt_const _).add differentiableAt_id).cpow (differentiableAt_const _)
      hu |>.differentiableWithinAt
  have hg : AnalyticOnNhd ℂ (fun u : ℂ => ((1 / (Real.Gamma a * Real.Gamma (1 - a)) : ℝ) : ℂ) *
      ∫ τ in Ioo (0 : ℝ) 1, (airySt_w a τ : ℂ) * (1 + u * τ)⁻¹) U := fun u hu =>
    analyticAt_const.mul (airySt_stieltjes_analyticOnNhd ha0 ha1 u hu)
  have h0U : (0 : ℂ) ∈ U := by simp [hU]
  have hev : (fun u : ℂ => (1 + u) ^ (-(a : ℂ))) =ᶠ[𝓝 0] fun u : ℂ =>
      ((1 / (Real.Gamma a * Real.Gamma (1 - a)) : ℝ) : ℂ) *
        ∫ τ in Ioo (0 : ℝ) 1, (airySt_w a τ : ℂ) * (1 + u * τ)⁻¹ := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) one_pos] with u hu
    exact airySt_binom_disc ha0 ha1 (by simpa using hu)
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg hUc h0U hev ht

/-- The binomial coefficient of `(1+t)^{-a}`: `(-1)^k Γ(a+k)/(Γ(a) k!)`. -/
def airySt_coef (a : ℝ) (k : ℕ) : ℝ :=
  (-1) ^ k * Real.Gamma (a + k) / (Real.Gamma a * Real.Gamma (k + 1))

/-- **Exact remainder of the binomial expansion** in Stieltjes–Euler form. -/
theorem airySt_binom_rem {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {t : ℂ} (ht : 1 + t ∈ slitPlane)
    (N : ℕ) :
    (1 + t) ^ (-(a : ℂ)) - ∑ k ∈ range N, (airySt_coef a k : ℂ) * t ^ k =
      (-t) ^ N * (((1 / (Real.Gamma a * Real.Gamma (1 - a)) : ℝ) : ℂ) *
        ∫ τ in Ioo (0 : ℝ) 1, ((τ ^ N * airySt_w a τ : ℝ) : ℂ) * (1 + t * τ)⁻¹) := by
  have hne : ∀ τ ∈ Ioo (0 : ℝ) 1, 1 + t * τ ≠ 0 := fun τ hτ =>
    slitPlane_ne_zero (airySt_one_add_mul_mem ht (Ioo_subset_Icc_self hτ))
  have hint : ∀ k : ℕ, IntegrableOn (fun τ : ℝ => ((τ ^ k * airySt_w a τ : ℝ) : ℂ)) (Ioo 0 1) :=
    fun k => (airySt_integrableOn_w ha0 ha1 k).ofReal
  have hpt : ∀ τ ∈ Ioo (0 : ℝ) 1, (airySt_w a τ : ℂ) * (1 + t * τ)⁻¹ =
      ∑ k ∈ range N, ((τ ^ k * airySt_w a τ : ℝ) : ℂ) * (-t) ^ k +
        (-t) ^ N * (((τ ^ N * airySt_w a τ : ℝ) : ℂ) * (1 + t * τ)⁻¹) := by
    intro τ hτ
    have hg := stRem_geom (t * τ) (hne τ hτ) N
    conv_lhs => rw [← one_div, hg]
    rw [mul_add, Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun k _ => ?_
      push_cast; ring
    · push_cast; ring
  have hcont : ContinuousOn (fun τ : ℝ => (1 + t * τ)⁻¹) (Icc 0 1) :=
    ContinuousOn.inv₀ (by fun_prop) fun τ hτ => slitPlane_ne_zero (airySt_one_add_mul_mem ht hτ)
  have hrem : IntegrableOn (fun τ : ℝ => ((τ ^ N * airySt_w a τ : ℝ) : ℂ) * (1 + t * τ)⁻¹)
      (Ioo 0 1) :=
    (hint N).mul_continuousOn_of_subset hcont measurableSet_Ioo isCompact_Icc Ioo_subset_Icc_self
  rw [airySt_binom ha0 ha1 ht, setIntegral_congr_fun measurableSet_Ioo hpt,
    integral_add (integrable_finsetSum _ fun k _ => (hint k).mul_const _)
      (hrem.const_mul _),
    integral_finsetSum _ fun k _ => (hint k).mul_const _, integral_const_mul]
  have hk : ∀ k ∈ range N, (((1 / (Real.Gamma a * Real.Gamma (1 - a)) : ℝ) : ℂ) *
      ∫ τ in Ioo (0 : ℝ) 1, ((τ ^ k * airySt_w a τ : ℝ) : ℂ) * (-t) ^ k) =
        (airySt_coef a k : ℂ) * t ^ k := by
    intro k _
    rw [integral_mul_const, integral_complex_ofReal, airySt_moment ha0 ha1 k, airySt_coef]
    have h1 : Real.Gamma (1 - a) ≠ 0 := (Real.Gamma_pos_of_pos (by linarith)).ne'
    have h2 : Real.Gamma a ≠ 0 := (Real.Gamma_pos_of_pos ha0).ne'
    have h3 : Real.Gamma (k + 1) ≠ 0 := (Real.Gamma_pos_of_pos (by positivity)).ne'
    have h1' : (Real.Gamma (1 - a) : ℂ) ≠ 0 := ofReal_ne_zero.mpr h1
    have h2' : (Real.Gamma a : ℂ) ≠ 0 := ofReal_ne_zero.mpr h2
    have h3' : (Real.Gamma (k + 1) : ℂ) ≠ 0 := ofReal_ne_zero.mpr h3
    rw [neg_pow]
    push_cast
    field_simp
  rw [mul_add, Finset.mul_sum, Finset.sum_congr rfl hk]
  ring

/-- The ray multiplier: `1` if `cos θ ≥ 0`, else `|csc θ|`. -/
def airySt_M (θ : ℝ) : ℝ := if 0 ≤ Real.cos θ then 1 else |Real.sin θ|⁻¹

/-- The ray multiplier `M_θ` (`1` if `cos θ ≥ 0`, else `|csc θ|`) is positive for `|θ| < π`. -/
theorem airySt_M_pos {θ : ℝ} (hθ : |θ| < π) : 0 < airySt_M θ := by
  unfold airySt_M
  split_ifs with h
  · exact one_pos
  · refine inv_pos.mpr (abs_pos.mpr fun hs => h ?_)
    rcases Real.sin_eq_zero_iff_of_lt_of_lt (by linarith [neg_abs_le θ])
      (by linarith [le_abs_self θ]) |>.mp hs with rfl
    simp

/-- For `s ≥ 0` and `|θ| < π`, `|(1 + s e^{iθ})⁻¹| ≤ M_θ`. -/
theorem airySt_norm_recip_le {θ : ℝ} (hθ : |θ| < π) {s : ℝ} (hs : 0 ≤ s) :
    ‖(1 + (s : ℂ) * exp (θ * I))⁻¹‖ ≤ airySt_M θ := by
  rw [norm_inv]
  unfold airySt_M
  split_ifs with h
  · exact inv_le_one_of_one_le₀ (Complex.one_le_norm_one_add_ofReal_mul_exp hs h)
  · have hM := airySt_M_pos hθ
    unfold airySt_M at hM; simp only [h, ↓reduceIte] at hM
    exact inv_anti₀ (inv_pos.mp hM) (Complex.abs_sin_le_norm_one_add_ofReal_mul_exp s θ)

/-- The Stieltjes factor of the binomial remainder is bounded by `M_θ` times its value at `0`. -/
theorem airySt_factor_bound {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {θ : ℝ} (hθ : |θ| < π) {r : ℝ}
    (hr : 0 ≤ r) (N : ℕ) :
    ‖((1 / (Real.Gamma a * Real.Gamma (1 - a)) : ℝ) : ℂ) *
        ∫ τ in Ioo (0 : ℝ) 1, ((τ ^ N * airySt_w a τ : ℝ) : ℂ) * (1 + (r * exp (θ * I)) * τ)⁻¹‖ ≤
      airySt_M θ * (Real.Gamma (a + N) / (Real.Gamma a * Real.Gamma (N + 1))) := by
  have hG : 0 < Real.Gamma a * Real.Gamma (1 - a) :=
    mul_pos (Real.Gamma_pos_of_pos ha0) (Real.Gamma_pos_of_pos (by linarith))
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hI : ‖∫ τ in Ioo (0 : ℝ) 1, ((τ ^ N * airySt_w a τ : ℝ) : ℂ) *
      (1 + (r * exp (θ * I)) * τ)⁻¹‖ ≤ ∫ τ in Ioo (0 : ℝ) 1, τ ^ N * airySt_w a τ * airySt_M θ := by
    refine norm_integral_le_of_norm_le ((airySt_integrableOn_w ha0 ha1 N).mul_const _) ?_
    refine (ae_restrict_iff' measurableSet_Ioo).mpr (Filter.Eventually.of_forall fun τ hτ => ?_)
    have h0 : 0 ≤ τ ^ N * airySt_w a τ := mul_nonneg (pow_nonneg hτ.1.le _) (airySt_w_nonneg a hτ)
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg h0]
    refine mul_le_mul_of_nonneg_left ?_ h0
    have := airySt_norm_recip_le hθ (s := r * τ) (mul_nonneg hr hτ.1.le)
    convert this using 3; push_cast; ring
  rw [integral_mul_const, airySt_moment ha0 ha1] at hI
  have h1 : Real.Gamma (1 - a) ≠ 0 := (Real.Gamma_pos_of_pos (by linarith)).ne'
  calc 1 / (Real.Gamma a * Real.Gamma (1 - a)) * ‖∫ τ in Ioo (0 : ℝ) 1,
        ((τ ^ N * airySt_w a τ : ℝ) : ℂ) * (1 + (r * exp (θ * I)) * τ)⁻¹‖
      ≤ 1 / (Real.Gamma a * Real.Gamma (1 - a)) *
          (Real.Gamma (a + N) * Real.Gamma (1 - a) / Real.Gamma (N + 1) * airySt_M θ) :=
        mul_le_mul_of_nonneg_left hI (by positivity)
    _ = _ := by field_simp

/-- `(r e^{iθ})^s = r^s e^{iθ s}` for `r > 0`, `|θ| < π`. -/
theorem airySt_ray_cpow {r : ℝ} (hr : 0 < r) {θ : ℝ} (hθ : |θ| < π) (s : ℂ) :
    ((r : ℂ) * exp (θ * I)) ^ s = (r : ℂ) ^ s * exp (θ * I * s) := by
  have hr0 : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr.ne'
  have him : (θ * I : ℂ).im = θ := by simp
  rw [cpow_def_of_ne_zero (mul_ne_zero hr0 (exp_ne_zero _)), log_ofReal_mul hr (exp_ne_zero _),
    log_exp (by rw [him]; linarith [neg_abs_le θ]) (by rw [him]; linarith [le_abs_self θ]),
    cpow_def_of_ne_zero hr0, ← ofReal_log hr.le, ← exp_add]
  congr 1; ring

/-- `1 + r e^{iθ}` lies in the slit plane for `r ≥ 0`, `|θ| < π`. -/
theorem airySt_one_add_mem {r : ℝ} (hr : 0 ≤ r) {θ : ℝ} (hθ : |θ| < π) :
    1 + (r : ℂ) * exp (θ * I) ∈ slitPlane := by
  rcases eq_or_lt_of_le hr with h | h
  · subst h; simp
  by_cases hs : Real.sin θ = 0
  · have hu0 : θ = 0 := by
      rcases Real.sin_eq_zero_iff_of_lt_of_lt (by linarith [neg_abs_le θ])
        (by linarith [le_abs_self θ]) |>.mp hs with h'
      exact h'
    subst hu0
    left
    simp; linarith
  · right
    simp [exp_ofReal_mul_I_im] at *
    exact ⟨h.ne', hs⟩

/-- The `k`-th term of the ray expansion: `c_k e^{iθ(b-1+k)} Γ(b+k) W^{-(b+k)}`. -/
def airySt_T (b a θ W : ℝ) (k : ℕ) : ℂ :=
  (airySt_coef a k : ℂ) * exp (θ * I * ((b : ℂ) - 1 + k)) *
    (Gamma ((b : ℂ) + k) * (W : ℂ) ^ (-((b : ℂ) + k)))

/-- The absolute value of the binomial coefficient `binom(-a, k)` is `Γ(a+k)/(Γ(a) k!)` for `a > 0`.
-/
theorem airySt_abs_coef {a : ℝ} (ha : 0 < a) (k : ℕ) :
    |airySt_coef a k| = Real.Gamma (a + k) / (Real.Gamma a * Real.Gamma (k + 1)) := by
  unfold airySt_coef
  have h1 := Real.Gamma_pos_of_pos (show 0 < a + k by positivity)
  have h2 := Real.Gamma_pos_of_pos ha
  have h3 := Real.Gamma_pos_of_pos (show (0 : ℝ) < k + 1 by positivity)
  rw [mul_div_assoc, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_pos (by positivity)]

/-- The modulus of the `k`-th term of the ray Laplace expansion is `Γ(a+k)/(Γ(a) k!) · Γ(b+k)
W^{-(b+k)}`. -/
theorem airySt_norm_T {b a θ W : ℝ} (hb : 0 < b) (ha : 0 < a) (hW : 0 < W) (k : ℕ) :
    ‖airySt_T b a θ W k‖ =
      Real.Gamma (a + k) / (Real.Gamma a * Real.Gamma (k + 1)) * Real.Gamma (b + k) *
        W ^ (-(b + k)) := by
  unfold airySt_T
  have he : θ * I * ((b : ℂ) - 1 + k) = ((θ * (b - 1 + k) : ℝ) : ℂ) * I := by push_cast; ring
  have hg : Gamma ((b : ℂ) + k) = ((Real.Gamma (b + k) : ℝ) : ℂ) := by
    rw [← Complex.Gamma_ofReal]; push_cast; rfl
  have hw : (W : ℂ) ^ (-((b : ℂ) + k)) = ((W ^ (-(b + k)) : ℝ) : ℂ) := by
    rw [ofReal_cpow hW.le]; push_cast; rfl
  rw [he, hg, hw, norm_mul, norm_mul, norm_mul, norm_exp_ofReal_mul_I, Complex.norm_real,
    Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, airySt_abs_coef ha,
    Real.norm_of_nonneg (Real.Gamma_pos_of_pos (by positivity)).le,
    Real.norm_of_nonneg (Real.rpow_nonneg hW.le _)]
  ring

/-- The ray monomial integrand on `(0,∞)`. -/
theorem airySt_term_eq {b W θ : ℝ} (hθ : |θ| < π) (k : ℕ) {r : ℝ} (hr : 0 < r) :
    Complex.exp (-(W * r)) * (((r : ℂ) * exp (θ * I)) ^ ((b : ℂ) - 1) *
      ((r : ℂ) * exp (θ * I)) ^ k) =
      exp (θ * I * ((b : ℂ) - 1 + k)) * (((r ^ ((b + k) - 1) * Real.exp (-(W * r)) : ℝ) : ℂ)) := by
  have ht : (r : ℂ) * exp (θ * I) ≠ 0 := mul_ne_zero (ofReal_ne_zero.mpr hr.ne') (exp_ne_zero _)
  rw [← cpow_natCast, ← cpow_add _ _ ht, airySt_ray_cpow hr hθ]
  push_cast
  rw [ofReal_cpow hr.le]
  push_cast
  ring_nf

/-- The ray Laplace integrand `e^{-Wr} t^{b-1} t^k`, `t = r e^{iθ}`, is integrable on `(0,∞)`. -/
theorem airySt_term_integrableOn {b W θ : ℝ} (hb : 0 < b) (hW : 0 < W) (hθ : |θ| < π) (k : ℕ) :
    IntegrableOn (fun r : ℝ => Complex.exp (-(W * r)) * (((r : ℂ) * exp (θ * I)) ^ ((b : ℂ) - 1) *
      ((r : ℂ) * exp (θ * I)) ^ k)) (Ioi 0) := by
  have h := ((stRem_integrableOn_rpow_exp (m := (b + k) - 1) (by have := k.cast_nonneg (α := ℝ); linarith) hW).ofReal
    (𝕜 := ℂ)).const_mul (exp (θ * I * ((b : ℂ) - 1 + k)))
  exact IntegrableOn.congr_fun h (fun r hr => (airySt_term_eq hθ k hr).symm) measurableSet_Ioi

/-- The ray Laplace integral of `t^{b-1} t^k`, `t = r e^{iθ}`, equals `e^{iθ(b-1+k)} Γ(b+k)
W^{-(b+k)}`. -/
theorem airySt_term_integral {b W θ : ℝ} (hb : 0 < b) (hW : 0 < W) (hθ : |θ| < π) (k : ℕ) :
    ∫ r in Ioi (0 : ℝ), Complex.exp (-(W * r)) * (((r : ℂ) * exp (θ * I)) ^ ((b : ℂ) - 1) *
      ((r : ℂ) * exp (θ * I)) ^ k) =
      exp (θ * I * ((b : ℂ) - 1 + k)) * (Gamma ((b : ℂ) + k) * (W : ℂ) ^ (-((b : ℂ) + k))) := by
  rw [setIntegral_congr_fun measurableSet_Ioi (fun r hr => airySt_term_eq hθ k hr),
    integral_const_mul]
  congr 1
  have h := integral_cpow_mul_cexp_neg_mul_Ioi_of_real (s := (b : ℂ) + k) (by simp; positivity) hW
  rw [← h]
  refine setIntegral_congr_fun measurableSet_Ioi (fun r hr => ?_)
  have hr : (0 : ℝ) < r := hr
  push_cast
  rw [ofReal_cpow hr.le]
  push_cast
  ring_nf

/-- The Stieltjes factor of the binomial remainder. -/
def airySt_Q (a : ℝ) (N : ℕ) (t : ℂ) : ℂ :=
  ((1 / (Real.Gamma a * Real.Gamma (1 - a)) : ℝ) : ℂ) *
    ∫ τ in Ioo (0 : ℝ) 1, ((τ ^ N * airySt_w a τ : ℝ) : ℂ) * (1 + t * τ)⁻¹

/-- The ray Laplace integral of `t^{b-1}(1+t)^{-a}`, with real damping `W`. -/
def airySt_L (b a θ W : ℝ) : ℂ :=
  ∫ r in Ioi (0 : ℝ), Complex.exp (-(W * r)) * (((r : ℂ) * exp (θ * I)) ^ ((b : ℂ) - 1) *
    (1 + (r : ℂ) * exp (θ * I)) ^ (-(a : ℂ)))

/-- **Exact remainder of the ray expansion.** -/
theorem airySt_rem_repr {a b W θ : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hb : 0 < b) (hW : 0 < W)
    (hθ : |θ| < π) (N : ℕ)
    (hint : IntegrableOn (fun r : ℝ => Complex.exp (-(W * r)) *
      (((r : ℂ) * exp (θ * I)) ^ ((b : ℂ) - 1) * (1 + (r : ℂ) * exp (θ * I)) ^ (-(a : ℂ))))
      (Ioi 0)) :
    airySt_L b a θ W - ∑ k ∈ range N, airySt_T b a θ W k =
      ∫ r in Ioi (0 : ℝ), Complex.exp (-(W * r)) * (((r : ℂ) * exp (θ * I)) ^ ((b : ℂ) - 1) *
        ((-((r : ℂ) * exp (θ * I))) ^ N * airySt_Q a N ((r : ℂ) * exp (θ * I)))) := by
  have hT : ∀ k, airySt_T b a θ W k = ∫ r in Ioi (0 : ℝ), (airySt_coef a k : ℂ) *
      (Complex.exp (-(W * r)) * (((r : ℂ) * exp (θ * I)) ^ ((b : ℂ) - 1) *
        ((r : ℂ) * exp (θ * I)) ^ k)) := by
    intro k
    rw [integral_const_mul, airySt_term_integral hb hW hθ k, airySt_T]
    ring
  simp_rw [hT]
  rw [← integral_finsetSum _ (fun k _ => (airySt_term_integrableOn hb hW hθ k).const_mul _),
    airySt_L, ← integral_sub hint (integrable_finsetSum _ fun k _ =>
      (airySt_term_integrableOn hb hW hθ k).const_mul _)]
  refine setIntegral_congr_fun measurableSet_Ioi (fun r hr => ?_)
  have hr : (0 : ℝ) ≤ r := le_of_lt hr
  have h := airySt_binom_rem ha0 ha1 (airySt_one_add_mem hr hθ) N
  simp only [airySt_Q]
  rw [← h, mul_sub, mul_sub, Finset.mul_sum, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-- Euler's integral `∫₀^∞ r^{m-1} e^{-Wr} dr = Γ(m) W^{-m}` for `m, W > 0`. -/
theorem airySt_gamma_int {m W : ℝ} (hm : 0 < m) (hW : 0 < W) :
    ∫ r in Ioi (0 : ℝ), r ^ (m - 1) * Real.exp (-(W * r)) = Real.Gamma m * W ^ (-m) := by
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := 1) (q := m - 1) one_pos (by linarith) hW
  simp only [Real.rpow_one, div_one, sub_add_cancel, mul_one, neg_mul] at h
  rw [h, mul_comm]

/-- The norm of the ray remainder integrand. -/
theorem airySt_norm_integrand {a b W θ : ℝ} (hθ : |θ| < π) (N : ℕ) {r : ℝ} (hr : 0 < r) :
    ‖Complex.exp (-(W * r)) * (((r : ℂ) * exp (θ * I)) ^ ((b : ℂ) - 1) *
        ((-((r : ℂ) * exp (θ * I))) ^ N * airySt_Q a N ((r : ℂ) * exp (θ * I))))‖ =
      r ^ ((b + N) - 1) * Real.exp (-(W * r)) * ‖airySt_Q a N ((r : ℂ) * exp (θ * I))‖ := by
  have he : θ * I * ((b : ℂ) - 1) = ((θ * (b - 1) : ℝ) : ℂ) * I := by push_cast; ring
  rw [airySt_ray_cpow hr hθ, he, norm_mul, norm_mul, norm_mul, norm_mul, norm_pow, norm_neg,
    Complex.norm_ofReal_mul_exp_ofReal_mul_I hr.le, norm_exp_ofReal_mul_I,
        norm_cpow_eq_rpow_re_of_pos hr,
    show (-(W * r : ℂ)) = ((-(W * r) : ℝ) : ℂ) by push_cast; ring, norm_exp,
    ofReal_re, Real.rpow_sub hr, Real.rpow_add hr, Real.rpow_natCast, Real.rpow_one]
  simp only [sub_re, ofReal_re, one_re]
  rw [Real.rpow_sub hr, Real.rpow_one]
  field_simp

/-- **The ray remainder bound with Olver's multiplier `M_θ`.** -/
theorem airySt_rem_le_M {a b W θ : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hb : 0 < b) (hW : 0 < W)
    (hθ : |θ| < π) (N : ℕ)
    (hint : IntegrableOn (fun r : ℝ => Complex.exp (-(W * r)) *
      (((r : ℂ) * exp (θ * I)) ^ ((b : ℂ) - 1) * (1 + (r : ℂ) * exp (θ * I)) ^ (-(a : ℂ))))
      (Ioi 0)) :
    ‖airySt_L b a θ W - ∑ k ∈ range N, airySt_T b a θ W k‖ ≤
      airySt_M θ * ‖airySt_T b a θ W N‖ := by
  rw [airySt_rem_repr ha0 ha1 hb hW hθ N hint, airySt_norm_T hb ha0 hW]
  set C := Real.Gamma (a + N) / (Real.Gamma a * Real.Gamma (N + 1))
  have hb' : 0 < b + N := by positivity
  calc _ ≤ ∫ r in Ioi (0 : ℝ), r ^ ((b + N) - 1) * Real.exp (-(W * r)) * (airySt_M θ * C) := by
        refine norm_integral_le_of_norm_le
          ((stRem_integrableOn_rpow_exp (by linarith) hW).mul_const _) ?_
        refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun r hr => ?_)
        have hr : (0 : ℝ) < r := hr
        rw [airySt_norm_integrand hθ N hr]
        exact mul_le_mul_of_nonneg_left (airySt_factor_bound ha0 ha1 hθ hr.le N) (by positivity)
    _ = _ := by rw [integral_mul_const, airySt_gamma_int hb' hW]; ring

/-- Olver's Gamma ratio `χ(m) = √π Γ(m/2+1)/Γ(m/2+1/2)` (DLMF 9.7.3). -/
def airySt_chi (m : ℝ) : ℝ := Real.sqrt π * Real.Gamma (m / 2 + 1) / Real.Gamma (m / 2 + 1 / 2)

/-- `Γ(m+1) ∫₀^∞ (W²+ρ²)^{-(m+1)/2} dρ = Γ(m) χ(m) W^{-m}`. -/
theorem airySt_chi_integral {m W : ℝ} (hm : 0 < m) (hW : 0 < W) :
    Real.Gamma (m + 1) * ∫ ρ in Ioi (0 : ℝ), (W ^ 2 + ρ ^ 2) ^ (-(m + 1) / 2) =
      Real.Gamma m * airySt_chi m * W ^ (-m) := by
  set s := (m + 1) / 2 with hs
  have hneg : -(m + 1) / 2 = -s := by rw [hs]; ring
  rw [hneg]
  have h1 := TauCeti.integral_one_add_sq_rpow (s := s) (by rw [hs]; linarith)
  have h2 := integral_comp_abs (f := fun x : ℝ => (1 + x ^ 2) ^ (-s))
  simp only [sq_abs] at h2
  have h3 := integral_comp_mul_left_Ioi (fun ρ : ℝ => (W ^ 2 + ρ ^ 2) ^ (-s)) 0 hW
  simp only [mul_zero, smul_eq_mul] at h3
  have h4 : ∀ x : ℝ, (W ^ 2 + (W * x) ^ 2) ^ (-s) = W ^ (-(m + 1)) * (1 + x ^ 2) ^ (-s) := by
    intro x
    rw [show W ^ 2 + (W * x) ^ 2 = W ^ 2 * (1 + x ^ 2) by ring,
      Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hW.le]
    congr 2; push_cast; rw [hs]; ring
  simp_rw [h4, integral_const_mul] at h3
  have hJ : ∫ ρ in Ioi (0 : ℝ), (W ^ 2 + ρ ^ 2) ^ (-s) =
      W * W ^ (-(m + 1)) * (ProbabilityTheory.beta (1 / 2) (s - 1 / 2) / 2) := by
    rw [← h1, h2]
    field_simp
    calc _ = W * (W⁻¹ * ∫ x in Ioi (0 : ℝ), (W ^ 2 + x ^ 2) ^ (-s)) := by field_simp
      _ = _ := by rw [← h3]; ring
  rw [hJ, ProbabilityTheory.beta, airySt_chi, Real.Gamma_one_half_eq,
    show s - 1 / 2 = m / 2 by rw [hs]; ring, show (1 / 2 : ℝ) + m / 2 = m / 2 + 1 / 2 by ring,
    Real.Gamma_add_one hm.ne', Real.Gamma_add_one (by positivity : m / 2 ≠ 0)]
  have hWm : W * W ^ (-(m + 1)) = W ^ (-m) := by
    rw [Real.rpow_neg hW.le, Real.rpow_neg hW.le, Real.rpow_add hW, Real.rpow_one]
    field_simp
  rw [hWm]
  have := Real.Gamma_pos_of_pos (show 0 < m / 2 + 1 / 2 by positivity)
  field_simp

/-- For `sin θ ≠ 0` there is a rotation `β` with `cos β > 0` and `cos (θ + β) = 0`. -/
private lemma airySt_exists_rotation {θ : ℝ} (hsin : Real.sin θ ≠ 0) :
    ∃ β : ℝ, 0 < Real.cos β ∧ Real.cos (θ + β) = 0 := by
  rcases lt_or_gt_of_ne hsin with h | h
  · refine ⟨-(π / 2) - θ, ?_, ?_⟩
    · rw [Real.cos_sub, Real.cos_neg, Real.sin_neg, Real.cos_pi_div_two, Real.sin_pi_div_two]
      linarith
    · rw [show θ + (-(π / 2) - θ) = -(π / 2) by ring, Real.cos_neg, Real.cos_pi_div_two]
  · refine ⟨π / 2 - θ, ?_, ?_⟩
    · rw [Real.cos_pi_div_two_sub]; exact h
    · rw [show θ + (π / 2 - θ) = π / 2 by ring, Real.cos_pi_div_two]

/-- The `(N+1)`-st remainder as a Stieltjes mixture, for the χ bound. -/
theorem airySt_rem_succ_le {a b W θ : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hb : 0 < b) (hW : 0 < W)
    (hθ : |θ| < π) (hsin : Real.sin θ ≠ 0) (N : ℕ) :
    ‖∫ r in Ioi (0 : ℝ), Complex.exp (-(W * r)) * (((r : ℂ) * exp (θ * I)) ^ ((b : ℂ) - 1) *
        ((-((r : ℂ) * exp (θ * I))) ^ (N + 1) * airySt_Q a (N + 1) ((r : ℂ) * exp (θ * I))))‖ ≤
      airySt_chi (b + N) * ‖airySt_T b a θ W N‖ := by
  set m := b + N with hmdef
  have hm : 0 < m := by positivity
  set C : ℝ := 1 / (Real.Gamma a * Real.Gamma (1 - a)) with hC
  have hCpos : 0 < C := by
    have := Real.Gamma_pos_of_pos ha0; have := Real.Gamma_pos_of_pos (by linarith : 0 < 1 - a)
    positivity
  set g : ℝ → ℝ := fun τ => τ ^ (N + 1) * airySt_w a τ with hg
  have hpt : ∀ r ∈ Ioi (0 : ℝ), Complex.exp (-(W * r)) *
      (((r : ℂ) * exp (θ * I)) ^ ((b : ℂ) - 1) *
        ((-((r : ℂ) * exp (θ * I))) ^ (N + 1) * airySt_Q a (N + 1) ((r : ℂ) * exp (θ * I)))) =
      ((-1) ^ (N + 1) * exp (θ * I * m) * C) * ((r : ℂ) ^ (m : ℂ) * Complex.exp (-(W * r)) *
        ∫ τ in Ioo (0 : ℝ) 1, (g τ : ℂ) / (1 + τ * (r * exp (θ * I)))) := by
    intro r hr
    have hr : (0 : ℝ) < r := hr
    have ht : (r : ℂ) * exp (θ * I) ≠ 0 :=
      mul_ne_zero (ofReal_ne_zero.mpr hr.ne') (exp_ne_zero _)
    have hQ : airySt_Q a (N + 1) ((r : ℂ) * exp (θ * I)) = (C : ℂ) *
        ∫ τ in Ioo (0 : ℝ) 1, (g τ : ℂ) / (1 + τ * (r * exp (θ * I))) := by
      simp only [airySt_Q, hC, hg]
      congr 1
      refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
      simp only [div_eq_mul_inv]; ring_nf
    have hpow : ((r : ℂ) * exp (θ * I)) ^ ((b : ℂ) - 1) * (-((r : ℂ) * exp (θ * I))) ^ (N + 1) =
        (-1) ^ (N + 1) * (exp (θ * I * m) * (r : ℂ) ^ (m : ℂ)) := by
      rw [neg_eq_neg_one_mul, mul_pow, ← cpow_natCast ((r : ℂ) * exp (θ * I)),
        mul_left_comm, ← cpow_add _ _ ht, airySt_ray_cpow hr hθ, hmdef]
      push_cast
      ring_nf
    rw [hQ, ← mul_assoc (((r : ℂ) * exp (θ * I)) ^ ((b : ℂ) - 1)), hpow]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul, norm_mul]
  have hnc : ‖((-1 : ℂ) ^ (N + 1) * exp (θ * I * m) * C)‖ = C := by
    rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
      show θ * I * (m : ℂ) = ((θ * m : ℝ) : ℂ) * I by push_cast; ring, norm_exp_ofReal_mul_I,
      one_mul, Complex.norm_real, Real.norm_of_nonneg hCpos.le]
  rw [hnc]
  obtain ⟨β, hβ, hσ⟩ := airySt_exists_rotation hsin
  have hg0 : ∀ τ ∈ Ioo (0 : ℝ) 1, 0 ≤ g τ := fun τ hτ =>
    mul_nonneg (pow_nonneg hτ.1.le _) (airySt_w_nonneg a hτ)
  have hgτ : ∀ τ ∈ Ioo (0 : ℝ) 1, g τ / τ = τ ^ N * airySt_w a τ := by
    intro τ hτ
    simp only [hg, pow_succ]
    field_simp [hτ.1.ne']
  have hgi : IntegrableOn (fun τ => g τ / τ) (Ioo 0 1) :=
    (airySt_integrableOn_w ha0 ha1 N).congr_fun (fun τ hτ => (hgτ τ hτ).symm) measurableSet_Ioo
  have hmix := stRem_mix_chi hm hW hβ hσ hsin hg0 (airySt_integrableOn_w ha0 ha1 (N + 1)) hgi
  rw [setIntegral_congr_fun measurableSet_Ioo hgτ, airySt_moment ha0 ha1,
    airySt_chi_integral hm hW] at hmix
  rw [airySt_norm_T hb ha0 hW]
  have h1 := Real.Gamma_pos_of_pos (by linarith : 0 < 1 - a)
  calc C * ‖_‖ ≤ C * (Real.Gamma m * airySt_chi m * W ^ (-m) *
        (Real.Gamma (a + N) * Real.Gamma (1 - a) / Real.Gamma (N + 1))) :=
      mul_le_mul_of_nonneg_left (by linarith [hmix]) hCpos.le
    _ = _ := by
      rw [hC, ← hmdef]
      field_simp

/-- **The ray remainder bound with multiplier `χ(N+b) + 1`**, for `sin θ ≠ 0`. -/
theorem airySt_rem_le_chi {a b W θ : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hb : 0 < b) (hW : 0 < W)
    (hθ : |θ| < π) (hsin : Real.sin θ ≠ 0) (N : ℕ)
    (hint : IntegrableOn (fun r : ℝ => Complex.exp (-(W * r)) *
      (((r : ℂ) * exp (θ * I)) ^ ((b : ℂ) - 1) * (1 + (r : ℂ) * exp (θ * I)) ^ (-(a : ℂ))))
      (Ioi 0)) :
    ‖airySt_L b a θ W - ∑ k ∈ range N, airySt_T b a θ W k‖ ≤
      (airySt_chi (b + N) + 1) * ‖airySt_T b a θ W N‖ := by
  have hsplit : airySt_L b a θ W - ∑ k ∈ range N, airySt_T b a θ W k =
      airySt_T b a θ W N + (airySt_L b a θ W - ∑ k ∈ range (N + 1), airySt_T b a θ W k) := by
    rw [sum_range_succ]; ring
  rw [hsplit, airySt_rem_repr ha0 ha1 hb hW hθ (N + 1) hint]
  calc _ ≤ ‖airySt_T b a θ W N‖ + airySt_chi (b + N) * ‖airySt_T b a θ W N‖ :=
        (norm_add_le _ _).trans (by gcongr; exact airySt_rem_succ_le ha0 ha1 hb hW hθ hsin N)
    _ = _ := by ring

/-- The chi estimate for a single positive exponential density. -/
theorem laplaceChi_kernel {m W X θ : ℝ} (hm : 0 < m) (hW : 0 < W)
    (hX : 0 < X) (hsin : Real.sin θ ≠ 0) :
    ‖∫ r in Ioi (0 : ℝ), (r : ℂ) ^ (m : ℂ) * Complex.exp (-(W * r)) /
      (X + r * exp (θ * I))‖ ≤
      airySt_chi m * ∫ r in Ioi (0 : ℝ), r ^ (m - 1) * Real.exp (-(W * r)) := by
  obtain ⟨β, hβ, hσ⟩ := airySt_exists_rotation hsin
  have h := stRem_chi_ray hm hW hX hβ hσ
  rw [airySt_chi_integral hm hW] at h
  rw [Real.integral_rpow_mul_exp_neg_mul_Ioi hm hW]
  convert h using 1
  rw [Real.rpow_neg hW.le, one_div, Real.inv_rpow hW.le]
  ring

/-- `X + r e^{iθ} ≠ 0` for `X > 0`, real `r` and `sin θ ≠ 0`. -/
private lemma laplaceChi_den_ne_zero {X θ : ℝ} (hX : 0 < X) (hsin : Real.sin θ ≠ 0) (r : ℝ) :
    (X : ℂ) + r * exp (θ * I) ≠ 0 := by
  intro he
  have hi := congrArg Complex.im he
  simp only [add_im, ofReal_im, mul_im, ofReal_re, exp_ofReal_mul_I_im,
    zero_mul, add_zero, zero_add, zero_im] at hi
  have hr : r = 0 := (mul_eq_zero.mp hi).resolve_right hsin
  simp only [hr, ofReal_zero, zero_mul, add_zero, ofReal_eq_zero] at he
  exact hX.ne' he

/-- `|r / (X + r e^{iθ})| ≤ 1/|sin θ|` for `X, r > 0` and `sin θ ≠ 0`. -/
private lemma laplaceChi_kernel_norm_le {X θ r : ℝ} (hX : 0 < X) (hsin : Real.sin θ ≠ 0)
    (hr : 0 < r) : ‖(r : ℂ) / (X + r * exp (θ * I))‖ ≤ 1 / |Real.sin θ| := by
  have hi := abs_im_le_norm ((X : ℂ) + r * exp (θ * I))
  simp only [add_im, ofReal_im, mul_im, ofReal_re, exp_ofReal_mul_I_im,
    zero_mul, add_zero, zero_add, abs_mul, abs_of_pos hr] at hi
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hr.le]
  apply (div_le_div_iff₀ (norm_pos_iff.mpr (laplaceChi_den_ne_zero hX hsin r))
    (abs_pos.mpr hsin)).mpr
  simpa using hi

/-- Positive Laplace mixtures retain the unshifted chi multiplier. -/
theorem laplaceChi_mixture {m X θ : ℝ} (hm : 0 < m) (hX : 0 < X)
    (hsin : Real.sin θ ≠ 0) (g : ℝ → ℝ)
    (hg0 : ∀ v ∈ Ioi (0 : ℝ), 0 ≤ g v)
    (hprod : Integrable (fun p : ℝ × ℝ =>
      p.1 ^ (m - 1) * Real.exp (-((1 + p.2) * p.1)) * g p.2)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ))))) :
    ‖∫ r in Ioi (0 : ℝ), (r : ℂ) ^ (m : ℂ) *
      (∫ v in Ioi (0 : ℝ), (Real.exp (-((1 + v) * r)) * g v : ℝ)) /
        (X + r * exp (θ * I))‖ ≤
      airySt_chi m * ∫ r in Ioi (0 : ℝ), r ^ (m - 1) *
        ∫ v in Ioi (0 : ℝ), Real.exp (-((1 + v) * r)) * g v := by
  let f : ℝ → ℝ → ℝ := fun r v => r ^ (m - 1) * Real.exp (-((1 + v) * r)) * g v
  let H : ℝ → ℝ → ℂ := fun r v => (r : ℂ) ^ (m : ℂ) *
      Complex.exp (-((1 + v) * r)) / (X + r * exp (θ * I)) * g v
  have hden (r : ℝ) : (X : ℂ) + r * exp (θ * I) ≠ 0 := laplaceChi_den_ne_zero hX hsin r
  have hkcont : Continuous (fun r : ℝ => (r : ℂ) / (X + r * exp (θ * I))) := by
    exact (by fun_prop : Continuous (fun r : ℝ => (r : ℂ))).div (by fun_prop) hden
  have hH_eq (r v : ℝ) (hr : 0 < r) : H r v = (f r v : ℂ) *
      ((r : ℂ) / (X + r * exp (θ * I))) := by
    have hp : r ^ m = r ^ (m - 1) * r := by
      calc r ^ m = r ^ ((m - 1) + 1) := by congr 1; ring
        _ = r ^ (m - 1) * r := by rw [Real.rpow_add hr, Real.rpow_one]
    have hc : (r : ℂ) ^ (m : ℂ) = (r ^ m : ℝ) := by
      rw [Complex.ofReal_cpow hr.le]
    dsimp [H, f]
    rw [hc, hp]
    push_cast
    ring
  have hkbound (r : ℝ) (hr : 0 < r) :
      ‖(r : ℂ) / (X + r * exp (θ * I))‖ ≤ 1 / |Real.sin θ| :=
    laplaceChi_kernel_norm_le hX hsin hr
  have hHi : Integrable (Function.uncurry H)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    refine (hprod.div_const |Real.sin θ|).mono' ?_ ?_
    · have hc := (Complex.continuous_ofReal.comp_aestronglyMeasurable hprod.aestronglyMeasurable).mul hkcont.aestronglyMeasurable.comp_fst
      refine hc.congr ?_
      change ∀ᵐ p ∂((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))),
        (f p.1 p.2 : ℂ) * ((p.1 : ℂ) / (X + p.1 * exp (θ * I))) = H p.1 p.2
      rw [Measure.prod_restrict, ae_restrict_iff' (measurableSet_Ioi.prod measurableSet_Ioi)]
      exact Eventually.of_forall fun p hp => (hH_eq p.1 p.2 hp.1).symm
    · rw [Measure.prod_restrict, ae_restrict_iff' (measurableSet_Ioi.prod measurableSet_Ioi)]
      refine Eventually.of_forall fun p hp => ?_
      have hf0 : 0 ≤ f p.1 p.2 := by
        dsimp [f]; exact mul_nonneg (mul_nonneg (Real.rpow_nonneg hp.1.le _) (Real.exp_pos _).le) (hg0 p.2 hp.2)
      change ‖H p.1 p.2‖ ≤ f p.1 p.2 / |Real.sin θ|
      rw [hH_eq p.1 p.2 hp.1, norm_mul,
        Complex.norm_real, Real.norm_of_nonneg hf0]
      exact (mul_le_mul_of_nonneg_left (hkbound p.1 hp.1) hf0).trans_eq (by dsimp [f]; ring)
  have hpt (r : ℝ) : (r : ℂ) ^ (m : ℂ) *
      (∫ v in Ioi (0 : ℝ), (Real.exp (-((1 + v) * r)) * g v : ℝ)) /
        (X + r * exp (θ * I)) = ∫ v in Ioi (0 : ℝ), H r v := by
    rw [← integral_complex_ofReal, ← integral_const_mul, ← integral_div]
    congr 1
    funext v
    dsimp [H]
    rw [ofReal_mul, ofReal_exp]
    push_cast
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi (fun r _ => hpt r), integral_integral_swap hHi]
  have hbound (v : ℝ) (hv : v ∈ Ioi (0 : ℝ)) :
      ‖∫ r in Ioi (0 : ℝ), H r v‖ ≤ airySt_chi m * ∫ r in Ioi (0 : ℝ), f r v := by
    have hv0 : 0 < 1 + v := by have : 0 < v := hv; linarith
    have he : (∫ r in Ioi (0 : ℝ), H r v) =
      (∫ r in Ioi (0 : ℝ), (r : ℂ) ^ (m : ℂ) * Complex.exp (-((1 + v) * r)) /
        (X + r * exp (θ * I))) * (g v : ℂ) := by
      exact integral_mul_const _ _
    rw [he, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hg0 v hv)]
    have hb := mul_le_mul_of_nonneg_right
      (laplaceChi_kernel hm hv0 hX hsin) (hg0 v hv)
    dsimp only [f]
    rw [integral_mul_const]
    simpa only [ofReal_add, ofReal_one, mul_assoc] using hb
  calc ‖∫ v in Ioi (0 : ℝ), ∫ r in Ioi (0 : ℝ), H r v‖
      ≤ ∫ v in Ioi (0 : ℝ), airySt_chi m * ∫ r in Ioi (0 : ℝ), f r v :=
        norm_integral_le_of_norm_le (hprod.integral_prod_right.const_mul _)
          ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall hbound))
    _ = airySt_chi m * ∫ r in Ioi (0 : ℝ), r ^ (m - 1) *
        ∫ v in Ioi (0 : ℝ), Real.exp (-((1 + v) * r)) * g v := by
      have hswap : Integrable (Function.uncurry fun v r => f r v)
          ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := hprod.swap
      rw [integral_const_mul, integral_integral_swap hswap]
      congr 1
      apply integral_congr_ae
      exact Eventually.of_forall fun r => by dsimp [f]; rw [← integral_const_mul]; congr 1; funext v; ring

/-- A finite moment of a nonnegative Laplace density supplies product integrability. -/
theorem laplaceChi_prod_integrable {m : ℝ} (hm : 0 < m) (g : ℝ → ℝ)
    (hgm : Measurable g) (hg0 : ∀ v ∈ Ioi (0 : ℝ), 0 ≤ g v)
    (hLap : ∀ r ∈ Ioi (0 : ℝ), IntegrableOn
      (fun v : ℝ => Real.exp (-(v * r)) * g v) (Ioi 0))
    (hMom : IntegrableOn (fun r : ℝ => r ^ (m - 1) * Real.exp (-r) *
      (1 + ∫ v in Ioi (0 : ℝ), Real.exp (-(v * r)) * g v)) (Ioi 0)) :
    Integrable (fun p : ℝ × ℝ =>
      p.1 ^ (m - 1) * Real.exp (-((1 + p.2) * p.1)) * g p.2)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  let f : ℝ × ℝ → ℝ := fun p =>
    p.1 ^ (m - 1) * Real.exp (-((1 + p.2) * p.1)) * g p.2
  have hfmeas : Measurable f := by dsimp [f]; fun_prop
  apply (integrable_prod_iff hfmeas.aestronglyMeasurable).mpr
  have heq (r v : ℝ) : f (r, v) =
      (r ^ (m - 1) * Real.exp (-r)) * (Real.exp (-(v * r)) * g v) := by
    dsimp [f]
    rw [show -((1 + v) * r) = -r + -(v * r) by ring, Real.exp_add]
    ring
  constructor
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun r hr => ?_)
    exact ((hLap r hr).const_mul (r ^ (m - 1) * Real.exp (-r))).congr
      ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun v _ => (heq r v).symm))
  · have hAtom : IntegrableOn (fun r : ℝ => r ^ (m - 1) * Real.exp (-r)) (Ioi 0) := by
      simpa using stRem_integrableOn_rpow_exp (m := m - 1) (by linarith) (show (0 : ℝ) < 1 by norm_num)
    refine (hMom.sub hAtom).congr_fun (fun r hr => ?_) measurableSet_Ioi
    have hnonneg (v : ℝ) (hv : v ∈ Ioi (0 : ℝ)) : 0 ≤ f (r, v) := by
      dsimp [f]
      exact mul_nonneg (mul_nonneg (Real.rpow_nonneg hr.le _) (Real.exp_pos _).le) (hg0 v hv)
    rw [setIntegral_congr_fun measurableSet_Ioi
      (fun v hv => Real.norm_of_nonneg (hnonneg v hv))]
    simp_rw [heq]
    rw [integral_const_mul]
    dsimp only [Pi.sub_apply]
    ring


end DLMF.Airy
