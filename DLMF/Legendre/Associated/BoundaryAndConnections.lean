/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Legendre.Associated.Wronskians

/-!
# Boundary behavior and connections of associated Legendre functions

Boundary estimates, hypergeometric values and degree-reflection connections for associated
Legendre functions.

Source references and common attribution are retained in
`DLMF.Legendre.Associated`.
-/

@[expose] public noncomputable section

open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF

open scoped Real Topology Nat ComplexConjugate

namespace DLMF.Legendre

/-- Norm bounds on `(1,√2)` for the Legendre hypergeometric arguments. -/
theorem legendre_near_one_bounds {x : ℝ} (h1 : 1 < x) (h2 : x^2 < 2) :
    ‖((1:ℂ)-x)/2‖ < 1 ∧ (((1:ℂ)-x)/2).re < 1/2 ∧ ‖1-1/(x:ℂ)^2‖ < 1 ∧ ‖1/(x:ℂ)^2‖ < 1 := by
  have hx0 : (0:ℝ) < x := by linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [show ((1:ℂ)-x)/2 = (((1-x)/2:ℝ):ℂ) by push_cast; ring, norm_real, Real.norm_eq_abs, abs_lt]
    constructor <;> nlinarith
  · simp; linarith
  · rw [show 1-1/(x:ℂ)^2 = ((1-1/x^2:ℝ):ℂ) by push_cast; ring, norm_real, Real.norm_eq_abs, abs_lt]
    have : 0 < 1/x^2 := by positivity
    have : 1/x^2 < 1 := by rw [div_lt_one (by positivity)]; nlinarith
    constructor <;> linarith
  · rw [show 1/(x:ℂ)^2 = ((1/x^2:ℝ):ℂ) by push_cast; ring, norm_real, Real.norm_eq_abs, abs_lt]
    have : 0 < 1/x^2 := by positivity
    have : 1/x^2 < 1 := by rw [div_lt_one (by positivity)]; nlinarith
    constructor <;> linarith

/-- DLMF 14.3.18-type quadratic representation near `x = 1⁺`. -/
theorem regularizedGaussHG_legendre_quadratic (ν c : ℂ) (hc : ∀ k : ℕ, c ≠ -(k:ℂ)) {x : ℝ} (h1 : 1 < x)
    (h2 : x^2 < 2) :
    regularizedGaussHG (ν+1) (-ν) c ((1-x)/2) =
      (x:ℂ)^(1+ν-c)*((1+x)/2:ℂ)^(c-1)*regularizedGaussHG ((c-ν)/2) ((c-ν-1)/2) c (1-1/(x:ℂ)^2) := by
  obtain ⟨hw, hr, hy, -⟩ := legendre_near_one_bounds h1 h2
  have hx0 : (x:ℂ) ≠ 0 := by exact_mod_cast (by linarith : (0:ℝ) < x).ne'
  have harg : 4*(((1:ℂ)-x)/2)*(((1:ℂ)-x)/2-1)/(1-2*(((1:ℂ)-x)/2))^2 = 1-1/(x:ℂ)^2 := by
    rw [show (1:ℂ)-2*((1-x)/2) = x by ring]; field_simp; ring
  have hq := quadratic_complementary (a := -ν) (c := c) hc hw hr (by rwa [harg])
  rw [harg, show (1:ℂ)-2*((1-x)/2) = x by ring, show (1:ℂ)-((1-x)/2) = (1+x)/2 by ring,
    show (1:ℂ)-(-ν) = ν+1 by ring, show ν+1-c = 1+ν-c by ring,
    show (-ν+c)/2 = (c-ν)/2 by ring, show (-ν+c-1)/2 = (c-ν-1)/2 by ring] at hq
  rw [congrFun (ordinaryHypergeometric_symm (-ν) (ν+1) c), ordinaryHypergeometric_eq_Gamma_mul_regularizedGaussHG hc hw,
    ordinaryHypergeometric_eq_Gamma_mul_regularizedGaussHG hc hy] at hq
  have hG := Complex.Gamma_ne_zero hc
  apply mul_left_cancel₀ hG
  rw [hq]; ring

/-- The `u ↔ 1-u` connection for the Olver Gauss function at `u = 1/x²`. -/
theorem regularizedGaussHG_olver_connection (ν μ : ℂ) {x : ℝ} (h1 : 1 < x) (h2 : x^2 < 2) :
    sin (π*(-μ))/π*regularizedGaussHG ((ν+μ+2)/2) ((ν+μ+1)/2) (ν+3/2) (1/(x:ℂ)^2) =
      (1/(x:ℂ)^2)^(-ν-1/2)*regularizedGaussHG ((1+μ-ν)/2) ((1+μ-ν-1)/2) (1+μ) (1-1/(x:ℂ)^2)/
        (Gamma ((ν-μ+1)/2)*Gamma ((ν-μ+2)/2)) -
      (1-1/(x:ℂ)^2)^(-μ)*(1/(x:ℂ)^2)^(-ν-1/2)/(Gamma ((ν+μ+2)/2)*Gamma ((ν+μ+1)/2))*
        regularizedGaussHG ((1-μ-ν)/2) ((1-μ-ν-1)/2) (1-μ) (1-1/(x:ℂ)^2) := by
  obtain ⟨-, -, hy, hu⟩ := legendre_near_one_bounds h1 h2
  have h1u : ‖1-1/(x:ℂ)^2‖ < 1 := hy
  have h := regularized_connection_one_sub ((ν+μ+2)/2) ((ν+μ+1)/2) (ν+3/2) hu h1u
  rw [← regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hu,
    ← regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ h1u,
    ← regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ h1u] at h
  have hyc := mem_cutPlane_of_norm_lt_one h1u
  rw [regularizedGaussHG_euler _ _ _ hyc, regularizedGaussHG_euler (ν+3/2-(ν+μ+2)/2) _ _ hyc] at h
  rw [show ν+3/2-(ν+μ+2)/2-(ν+μ+1)/2 = -μ by ring,
    show (ν+μ+2)/2+(ν+μ+1)/2-(ν+3/2)+1 = 1+μ by ring,
    show ν+3/2-(ν+μ+2)/2 = (ν-μ+1)/2 by ring, show ν+3/2-(ν+μ+1)/2 = (ν-μ+2)/2 by ring,
    show -μ+1 = 1-μ by ring, show (1:ℂ)-(1-1/(x:ℂ)^2) = 1/(x:ℂ)^2 by ring,
    show 1+μ-(ν+μ+2)/2-(ν+μ+1)/2 = -ν-1/2 by ring,
    show 1-μ-(ν-μ+1)/2-(ν-μ+2)/2 = -ν-1/2 by ring,
    show 1+μ-(ν+μ+2)/2 = (1+μ-ν-1)/2 by ring, show 1+μ-(ν+μ+1)/2 = (1+μ-ν)/2 by ring,
    show 1-μ-(ν-μ+1)/2 = (1-μ-ν)/2 by ring, show 1-μ-(ν-μ+2)/2 = (1-μ-ν-1)/2 by ring,
    regularizedGaussHG_symm ((1+μ-ν-1)/2) ((1+μ-ν)/2) (1+μ) hyc] at h
  rw [h]; ring

/-- Complex powers of positive reals as exponentials of real logarithms. -/
theorem legendre_ofReal_cpow_exp {r : ℝ} (hr : 0 < r) (s : ℂ) : ((r:ℂ))^s = exp ((Real.log r:ℂ)*s) := by
  rw [cpow_def_of_ne_zero (by exact_mod_cast hr.ne'), ofReal_log hr.le]

/-- Powers of two as exponentials. -/
theorem legendre_two_cpow_exp (s : ℂ) : (2:ℂ)^s = exp ((Real.log 2:ℂ)*s) := by
  rw [cpow_def_of_ne_zero two_ne_zero, show (2:ℂ) = ((2:ℝ):ℂ) by norm_num, ← ofReal_log (by norm_num)]

/-- `2 = exp (log 2)`. -/
theorem legendre_two_eq_exp : (2:ℂ) = exp (Real.log 2:ℂ) := by
  rw [← ofReal_exp, Real.exp_log (by norm_num)]; norm_num

/-- Scalar identity behind the `P^{-μ}` coefficient in DLMF 14.9.15. -/
theorem legendre_connection_scalar_minus (ν μ : ℂ) {x : ℝ} (h1 : 1 < x) :
    2*(1/(x:ℂ)^2)^(-ν-1/2)*(legendreBranchPower μ x/(2^(ν+1)*(x:ℂ)^(ν+μ+1))) =
      exp (-μ/2*(log ((x:ℂ)+1)-log ((x:ℂ)-1)))*((x:ℂ)^(1+ν-(1+μ))*((1+x)/2:ℂ)^(1+μ-1))*2^(-(ν-μ)) := by
  have hx : (0:ℝ) < x := by linarith
  have hp : (0:ℝ) < x+1 := by linarith
  have hm : (0:ℝ) < x-1 := by linarith
  have e1 : (1/(x:ℂ)^2) = ((1/x^2:ℝ):ℂ) := by push_cast; ring
  have e2 : ((1+x)/2:ℂ) = (((x+1)/2:ℝ):ℂ) := by push_cast; ring
  have e4 : (x:ℂ)+1 = ((x+1:ℝ):ℂ) := by push_cast; ring
  have e5 : (x:ℂ)-1 = ((x-1:ℝ):ℂ) := by push_cast; ring
  unfold legendreBranchPower
  rw [e1, e2, e4, e5, legendre_ofReal_cpow_exp (by positivity : (0:ℝ) < 1/x^2),
    legendre_ofReal_cpow_exp (by positivity : (0:ℝ) < (x+1)/2), legendre_ofReal_cpow_exp hx, legendre_ofReal_cpow_exp hx,
    legendre_two_cpow_exp, legendre_two_cpow_exp, ← ofReal_log hp.le, ← ofReal_log hm.le,
    Real.log_div (by positivity : x+1 ≠ 0) (by norm_num : (2:ℝ) ≠ 0),
    Real.log_div (by norm_num : (1:ℝ) ≠ 0) (by positivity : x^2 ≠ 0), Real.log_one, Real.log_pow]
  nth_rw 1 [legendre_two_eq_exp]
  simp only [← exp_add, ← exp_sub]
  congr 1
  push_cast
  ring

/-- Scalar identity behind the `P^{μ}` coefficient in DLMF 14.9.15. -/
theorem legendre_connection_scalar_plus (ν μ : ℂ) {x : ℝ} (h1 : 1 < x) :
    2*(1-1/(x:ℂ)^2)^(-μ)*(1/(x:ℂ)^2)^(-ν-1/2)*(legendreBranchPower μ x/(2^(ν+1)*(x:ℂ)^(ν+μ+1))) =
      exp (μ/2*(log ((x:ℂ)+1)-log ((x:ℂ)-1)))*((x:ℂ)^(1+ν-(1-μ))*((1+x)/2:ℂ)^(1-μ-1))*2^(-(ν+μ)) := by
  have hx : (0:ℝ) < x := by linarith
  have hp : (0:ℝ) < x+1 := by linarith
  have hm : (0:ℝ) < x-1 := by linarith
  have e1 : (1/(x:ℂ)^2) = ((1/x^2:ℝ):ℂ) := by push_cast; ring
  have e0 : (1-1/(x:ℂ)^2) = (((x-1)*(x+1)/x^2:ℝ):ℂ) := by
    have : (x:ℂ) ≠ 0 := by exact_mod_cast hx.ne'
    push_cast; field_simp; ring
  have e2 : ((1+x)/2:ℂ) = (((x+1)/2:ℝ):ℂ) := by push_cast; ring
  have e4 : (x:ℂ)+1 = ((x+1:ℝ):ℂ) := by push_cast; ring
  have e5 : (x:ℂ)-1 = ((x-1:ℝ):ℂ) := by push_cast; ring
  unfold legendreBranchPower
  rw [e0, e1, e2, e4, e5, legendre_ofReal_cpow_exp (by positivity : (0:ℝ) < (x-1)*(x+1)/x^2),
    legendre_ofReal_cpow_exp (by positivity : (0:ℝ) < 1/x^2),
    legendre_ofReal_cpow_exp (by positivity : (0:ℝ) < (x+1)/2), legendre_ofReal_cpow_exp hx, legendre_ofReal_cpow_exp hx,
    legendre_two_cpow_exp, legendre_two_cpow_exp, ← ofReal_log hp.le, ← ofReal_log hm.le,
    Real.log_div (by positivity : x+1 ≠ 0) (by norm_num : (2:ℝ) ≠ 0),
    Real.log_div (by norm_num : (1:ℝ) ≠ 0) (by positivity : x^2 ≠ 0), Real.log_one, Real.log_pow,
    Real.log_div (by positivity : (x-1)*(x+1) ≠ 0) (by positivity : x^2 ≠ 0),
    Real.log_mul hm.ne' hp.ne', Real.log_pow]
  nth_rw 1 [legendre_two_eq_exp]
  simp only [← exp_add, ← exp_sub]
  congr 1
  push_cast
  ring

/-- DLMF 14.9.15 on `(1,√2)` for non-integer order. -/
theorem associated_connection_15_real (ν μ : ℂ) (hμ : ∀ n : ℤ, μ ≠ n) {x : ℝ} (h1 : 1 < x) (h2 : x^2 < 2) :
    2*sin (μ*π)/π*olverQ ν μ x=associatedP ν μ x/Gamma (ν+μ+1)-associatedP ν (-μ) x/Gamma (ν-μ+1) := by
  have hc1 : ∀ k : ℕ, 1-μ ≠ -(k:ℂ) := fun k hk => hμ (k+1) (by push_cast; linear_combination -hk)
  have hc2 : ∀ k : ℕ, 1+μ ≠ -(k:ℂ) := fun k hk => hμ (-(k+1)) (by push_cast; linear_combination hk)
  have hT := regularizedGaussHG_olver_connection ν μ h1 h2
  have I1 := legendre_connection_scalar_minus ν μ h1
  have I2 := legendre_connection_scalar_plus ν μ h1
  have hd1 := legendre_recip_duplication (ν+μ)
  have hd2 := legendre_recip_duplication (ν-μ)
  have hs : sin (μ*π) = -sin (π*(-μ)) := by rw [mul_neg, sin_neg, neg_neg, mul_comm]
  unfold olverQ associatedP
  rw [show 1-(-μ) = 1+μ by ring, regularizedGaussHG_legendre_quadratic ν (1-μ) hc1 h1 h2,
    regularizedGaussHG_legendre_quadratic ν (1+μ) hc2 h1 h2,
    show (1-μ-ν)/2 = ((1-μ)-ν)/2 by ring] at *
  rw [div_eq_mul_inv _ (Gamma (ν+μ+1)), div_eq_mul_inv _ (Gamma (ν-μ+1)), hd1, hd2, hs]
  linear_combination (-2*(Real.sqrt π:ℂ)*(legendreBranchPower μ x/(2^(ν+1)*(x:ℂ)^(ν+μ+1))))*hT
    + (-(Real.sqrt π:ℂ)*regularizedGaussHG ((1+μ-ν)/2) ((1+μ-ν-1)/2) (1+μ) (1-1/(x:ℂ)^2)*
        (Gamma ((ν-μ+1)/2))⁻¹*(Gamma ((ν-μ+2)/2))⁻¹)*I1
    + ((Real.sqrt π:ℂ)*regularizedGaussHG ((1-μ-ν)/2) ((1-μ-ν-1)/2) (1-μ) (1-1/(x:ℂ)^2)*
        (Gamma ((ν+μ+1)/2))⁻¹*(Gamma ((ν+μ+2)/2))⁻¹)*I2

/-- DLMF 14.9.15 on the cut plane for non-integer order. -/
theorem associated_connection_15_nonint (ν μ : ℂ) (hμ : ∀ n : ℤ, μ ≠ n) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    2*sin (μ*π)/π*olverQ ν μ z=associatedP ν μ z/Gamma (ν+μ+1)-associatedP ν (-μ) z/Gamma (ν-μ+1) := by
  have hf : AnalyticOnNhd ℂ (fun w => 2*sin (μ*π)/π*olverQ ν μ w) {z : ℂ | z-1 ∈ slitPlane} :=
    fun w hw => analyticAt_const.mul (olverQ_analytic ν μ w hw)
  have hg : AnalyticOnNhd ℂ (fun w => associatedP ν μ w/Gamma (ν+μ+1)-associatedP ν (-μ) w/Gamma (ν-μ+1))
      {z : ℂ | z-1 ∈ slitPlane} :=
    fun w hw => ((associatedP_analytic ν μ w hw).div_const).sub ((associatedP_analytic ν (-μ) w hw).div_const)
  set x₀ : ℝ := 6/5
  have h2 : ((x₀:ℝ):ℂ) ∈ {z : ℂ | z-1 ∈ slitPlane} := by
    show ((x₀:ℝ):ℂ) - 1 ∈ slitPlane
    rw [show ((x₀:ℝ):ℂ) - 1 = ((x₀-1:ℝ):ℂ) by push_cast; ring]
    exact Or.inl (by simp [x₀]; norm_num)
  refine hf.eqOn_of_preconnected_of_frequently_eq hg isPreconnected_sub_one_mem_slitPlane h2 ?_ hz
  have ht : Tendsto (fun r : ℝ => (r : ℂ)) (𝓝[≠] x₀) (𝓝[≠] ((x₀ : ℝ) : ℂ)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · exact (continuous_ofReal.tendsto _).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r hr
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff, ofReal_inj] using hr
  apply ht.frequently
  have hI : Ioo (1:ℝ) (7/5) ∈ 𝓝 x₀ := Ioo_mem_nhds (by norm_num [x₀]) (by norm_num [x₀])
  refine (Filter.Eventually.frequently (nhdsWithin_le_nhds (Filter.mem_of_superset hI ?_)))
  intro r hr
  exact associated_connection_15_real ν μ hμ hr.1 (by nlinarith [hr.1, hr.2])

/-- DLMF 14.9.15: `2 sin(μπ)/π · 𝑸^μ_ν = P^μ_ν/Γ(ν+μ+1) - P^{-μ}_ν/Γ(ν-μ+1)` on the cut plane. -/
theorem olverQ_connection (ν μ : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    2*sin (μ*π)/π*olverQ ν μ z=associatedP ν μ z/Gamma (ν+μ+1)-associatedP ν (-μ) z/Gamma (ν-μ+1) := by
  by_cases hμ : ∀ n : ℤ, μ ≠ n
  · exact associated_connection_15_nonint ν μ hμ hz
  push Not at hμ
  obtain ⟨m, rfl⟩ := hμ
  set G : ℂ → ℂ := fun μ => 2*sin (μ*π)/π*olverQ ν μ z -
    (associatedP ν μ z*(Gamma (ν+μ+1))⁻¹-associatedP ν (-μ) z*(Gamma (ν-μ+1))⁻¹)
  have hGc : Continuous G := by
    have hQ := (olverQ_entire_order ν z hz).continuous
    have hP := (associatedP_entire_order ν z hz).continuous
    have hPm : Continuous fun μ : ℂ => associatedP ν (-μ) z := hP.comp continuous_neg
    have g1 := continuous_recip_Gamma.comp (by fun_prop : Continuous fun μ : ℂ => ν+μ+1)
    have g2 := continuous_recip_Gamma.comp (by fun_prop : Continuous fun μ : ℂ => ν-μ+1)
    exact ((by fun_prop : Continuous fun μ : ℂ => 2*sin (μ*π)/π).mul hQ).sub
      ((hP.mul g1).sub (hPm.mul g2))
  have hev : G =ᶠ[𝓝[≠] (m:ℂ)] fun _ => 0 := by
    have hb : ∀ᶠ μ in 𝓝 (m:ℂ), μ ∈ Metric.ball (m:ℂ) 1 := Metric.ball_mem_nhds _ one_pos
    filter_upwards [nhdsWithin_le_nhds hb, self_mem_nhdsWithin] with μ hμ2 hμ3
    have hnot : ∀ n : ℤ, μ ≠ n := by
      intro n hn
      subst hn
      have hlt : ‖((n:ℂ)-m)‖ < 1 := by simpa [dist_eq_norm] using hμ2
      rw [← Int.cast_sub, Complex.norm_intCast] at hlt
      have : |((n-m:ℤ):ℝ)| < 1 := by simpa using hlt
      rw [← Int.cast_abs] at this
      have : |n-m| < 1 := by exact_mod_cast this
      have := Int.abs_lt_one_iff.mp this
      exact hμ3 (by simp [show n = m by omega])
    simp only [G]
    rw [associated_connection_15_nonint ν μ hnot hz, div_eq_mul_inv, div_eq_mul_inv, sub_self]
  have h0 : G m = 0 := tendsto_nhds_unique (hGc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    (tendsto_const_nhds.congr' hev.symm)
  simp only [G] at h0
  rw [div_eq_mul_inv, div_eq_mul_inv]
  linear_combination h0

/-- The regularized Gauss function at the origin is `1/Γ(c)`, also at poles of `Γ`. -/
theorem regularizedGaussHG_at_zero (a b c : ℂ) : regularizedGaussHG a b c 0 = (Gamma c)⁻¹ := by
  rw [regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ (by simp), regularizedGaussHGFun_eq_tsum,
    tsum_eq_single 0 (fun n hn => by simp [zero_pow hn])]
  simp

/-- Abel's identity for two solutions of the associated Legendre equation of orders `±μ`. -/
theorem associatedP_wronskian_const (ν μ : ℂ) {z w : ℂ} (hz : z-1 ∈ slitPlane) (hw : w-1 ∈ slitPlane) :
    (1-z^2)*ODE.wronskian (associatedP ν (-μ)) (associatedP ν μ) z =
      (1-w^2)*ODE.wronskian (associatedP ν (-μ)) (associatedP ν μ) w := by
  set G : ℂ → ℂ := fun y => (1-y^2)*ODE.wronskian (associatedP ν (-μ)) (associatedP ν μ) y
  have hd : ∀ y ∈ {z : ℂ | z-1 ∈ slitPlane}, HasDerivAt G 0 y := by
    intro y hy
    have hfa := associatedP_analytic ν (-μ) y hy
    have hga := associatedP_analytic ν μ y hy
    have hf2 : HasDerivAt (deriv (associatedP ν (-μ))) (iteratedDeriv 2 (associatedP ν (-μ)) y) y := by
      rw [iteratedDeriv_succ, iteratedDeriv_one]
      exact ((associatedP_analytic ν (-μ)).deriv y hy).differentiableAt.hasDerivAt
    have hg2 : HasDerivAt (deriv (associatedP ν μ)) (iteratedDeriv 2 (associatedP ν μ) y) y := by
      rw [iteratedDeriv_succ, iteratedDeriv_one]
      exact ((associatedP_analytic ν μ).deriv y hy).differentiableAt.hasDerivAt
    have ef := associatedP_ode ν (-μ) hy
    have eg := associatedP_ode ν μ hy
    rw [neg_sq] at ef
    have hsq : HasDerivAt (fun y : ℂ => 1-y^2) (-(2*y)) y := by
      simpa using ((hasDerivAt_id y).pow 2).const_sub 1
    refine (hsq.mul ((hfa.differentiableAt.hasDerivAt.mul hg2).sub
      (hga.differentiableAt.hasDerivAt.mul hf2))).congr_deriv ?_
    simp only [Pi.mul_apply, Pi.sub_apply]
    linear_combination (associatedP ν (-μ) y)*eg-(associatedP ν μ y)*ef
  have := isOpen_sub_one_mem_slitPlane.is_const_of_deriv_eq_zero isPreconnected_sub_one_mem_slitPlane
    (fun y hy => (hd y hy).differentiableAt.differentiableWithinAt) (fun y hy => (hd y hy).deriv) hz hw
  simpa [G] using this

/-- DLMF 14.2.7: for `z-1` in the slit plane (`z ∉ (-∞, 1]`), `𝒲{P^{-μ}_ν(z), P^μ_ν(z)} = 2
sin(μπ)/(π (1-z²))`, with `𝒲{f,g} = f g' - g f'`. -/
@[dlmf 14.2.E7]
theorem associated_wronskian_7 (ν μ : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    ODE.wronskian (associatedP ν (-μ)) (associatedP ν μ) z=2*sin (μ*π)/(π*(1-z^2)) := by
  set H : ℂ → ℂ := fun y => 2*μ*regularizedGaussHG (ν+1) (-ν) (1-(-μ)) ((1-y)/2)*
      regularizedGaussHG (ν+1) (-ν) (1-μ) ((1-y)/2) + (1-y^2)*(ν*(ν+1)/2)*
      (regularizedGaussHG (ν+1) (-ν) (1-(-μ)) ((1-y)/2)*regularizedGaussHG (ν+1+1) (-ν+1) (1-μ+1) ((1-y)/2)
       - regularizedGaussHG (ν+1) (-ν) (1-μ) ((1-y)/2)*regularizedGaussHG (ν+1+1) (-ν+1) (1-(-μ)+1) ((1-y)/2))
  have hne : ∀ y : ℂ, y-1 ∈ slitPlane → 1-y^2 ≠ 0 := by
    intro y hy h
    have hp := slitPlane_ne_zero (one_add_mem_slitPlane_of_sub_one hy)
    have hfac : (y-1)*(1+y)=0 := by linear_combination -h
    exact (mul_ne_zero (slitPlane_ne_zero hy) hp) hfac
  have hGH : ∀ y : ℂ, y-1 ∈ slitPlane →
      (1-y^2)*ODE.wronskian (associatedP ν (-μ)) (associatedP ν μ) y = H y := by
    intro y hy
    have hf : HasDerivAt (associatedP ν (-μ)) _ y := hasDerivAt_associatedP_aux (ν+1) (-ν) (1-(-μ)) (-μ) hy
    have hg : HasDerivAt (associatedP ν μ) _ y := hasDerivAt_associatedP_aux (ν+1) (-ν) (1-μ) μ hy
    have hE : exp (-μ/2*(log (y+1)-log (y-1)))*exp (μ/2*(log (y+1)-log (y-1))) = 1 := by
      rw [← exp_add]; ring_nf; exact exp_zero
    have hB : exp (μ/2*(log (y+1)-log (y-1))) ≠ 0 := exp_ne_zero _
    have h1 := hne y hy
    unfold ODE.wronskian
    rw [hf.deriv, hg.deriv]
    simp only [associatedP, H]
    rw [eq_inv_of_mul_eq_one_left hE]
    generalize exp (μ/2*(log (y+1)-log (y-1))) = B at hB ⊢
    field_simp
    ring
  have hF : ∀ a b c : ℂ, ContinuousAt (fun y : ℂ => regularizedGaussHG a b c ((1-y)/2)) 1 := by
    intro a b c
    have h0 : ((1:ℂ)-1)/2 ∈ cutPlane := by simpa using zero_mem_cutPlane
    have hg : ContinuousAt (fun y : ℂ => (1-y)/2) 1 := by fun_prop
    exact ContinuousAt.comp (g := regularizedGaussHG a b c) (f := fun y : ℂ => (1-y)/2) (x := 1)
      (analyticAt_regularizedGaussHG a b c h0).continuousAt hg
  have hcont : ContinuousAt H 1 := by
    simp only [H]
    exact ((continuousAt_const.mul (hF _ _ _)).mul (hF _ _ _)).add
      ((by fun_prop : ContinuousAt (fun y : ℂ => (1-y^2)*(ν*(ν+1)/2)) 1).mul
        (((hF _ _ _).mul (hF _ _ _)).sub ((hF _ _ _).mul (hF _ _ _))))
  have hH1 : H 1 = 2*μ*(Gamma (1-(-μ)))⁻¹*(Gamma (1-μ))⁻¹ := by
    simp only [H, sub_self, zero_div, regularizedGaussHG_at_zero]; ring
  have hlim : Tendsto (fun ε : ℝ => H (1+ε)) (𝓝[>] (0:ℝ)) (𝓝 (H 1)) := by
    have : Tendsto (fun ε : ℝ => (1:ℂ)+ε) (𝓝[>] (0:ℝ)) (𝓝 1) := by
      have hc : Continuous (fun ε : ℝ => (1:ℂ)+ε) := by fun_prop
      simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    exact hcont.tendsto.comp this
  have hev : ∀ᶠ ε : ℝ in 𝓝[>] (0:ℝ), H (1+ε) =
      (1-z^2)*ODE.wronskian (associatedP ν (-μ)) (associatedP ν μ) z := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hm : (1+(ε:ℂ))-1 ∈ slitPlane := by
      rw [add_sub_cancel_left]; exact Or.inl (by simpa using hε)
    rw [← hGH _ hm, associatedP_wronskian_const ν μ hm hz]
  have hval := tendsto_nhds_unique (hlim.congr' hev) tendsto_const_nhds
  rw [hH1] at hval
  have hm : μ*(Gamma (1-(-μ)))⁻¹ = (Gamma μ)⁻¹ := by
    rw [show 1-(-μ) = μ+1 by ring]
    by_cases h0 : μ = 0
    · simp [h0]
    · rw [Gamma_add_one _ h0, mul_inv, ← mul_assoc, mul_inv_cancel₀ h0, one_mul]
  have hrefl := legendre_recip_Gamma_reflection μ
  have hz1 := hne z hz
  have hpi : (π:ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [eq_div_iff (mul_ne_zero hpi hz1)]
  rw [show 2*μ*(Gamma (1-(-μ)))⁻¹*(Gamma (1-μ))⁻¹ = 2*((Gamma μ)⁻¹*(Gamma (1-μ))⁻¹) by
    rw [← hm]; ring] at hval
  rw [mul_comm μ π]
  linear_combination -π*hval + 2*hrefl

/-- Explicit derivative of `𝑸^μ_ν`. -/
theorem hasDerivAt_olverQ (ν μ : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    HasDerivAt (olverQ ν μ) ((Real.sqrt π:ℂ)*legendreBranchPower μ z/(2^(ν+1)*z^(ν+μ+1))*
      ((μ*z/(z^2-1)-(ν+μ+1)/z)*regularizedGaussHG ((ν+μ+2)/2) ((ν+μ+1)/2) (ν+3/2) (1/z^2) +
        (ν+μ+2)/2*((ν+μ+1)/2)*regularizedGaussHG ((ν+μ+2)/2+1) ((ν+μ+1)/2+1) (ν+3/2+1) (1/z^2)*(-2/z^3))) z := by
  have hz0 := slitPlane_ne_zero (mem_slitPlane_of_sub_one hz)
  have hm := slitPlane_ne_zero hz
  have hp' : z+1 ∈ slitPlane := by simpa [add_comm] using one_add_mem_slitPlane_of_sub_one hz
  have hp := slitPlane_ne_zero hp'
  have hB : HasDerivAt (legendreBranchPower μ) _ z :=
    ((((hasDerivAt_id z).sub_const 1).clog hz).add (((hasDerivAt_id z).add_const 1).clog hp')).const_mul (μ/2)
      |>.cexp
  have hP := (hasDerivAt_id z).cpow_const (c := ν+μ+1) (mem_slitPlane_of_sub_one hz)
  have hcut := recip_sq_mem_cutPlane hz
  have hFd := (analyticAt_regularizedGaussHG ((ν+μ+2)/2) ((ν+μ+1)/2) (ν+3/2) hcut).differentiableAt.hasDerivAt
  rw [deriv_regularizedGaussHG _ _ _ hcut] at hFd
  have hu : HasDerivAt (fun w : ℂ => 1/w^2) (-2/z^3) z := by
    have := (hasDerivAt_pow 2 z).inv (pow_ne_zero 2 hz0)
    convert this using 1
    · ext t; simp
    · field_simp; ring
  have hF := hFd.comp z hu
  have hD : HasDerivAt (fun w : ℂ => 2^(ν+1)*w^(ν+μ+1)) (2^(ν+1)*((ν+μ+1)*z^(ν+μ+1-1))) z := by
    simpa using hP.const_mul ((2:ℂ)^(ν+1))
  have hne : (2:ℂ)^(ν+1)*z^(ν+μ+1) ≠ 0 :=
    mul_ne_zero (cpow_ne_zero_iff.mpr (Or.inl two_ne_zero)) (cpow_ne_zero_iff.mpr (Or.inl hz0))
  have h := ((hB.const_mul (Real.sqrt π:ℂ)).div hD hne).mul hF
  refine h.congr_of_eventuallyEq (Eventually.of_forall fun w => ?_) |>.congr_deriv ?_
  · simp [olverQ, legendreBranchPower, Function.comp_def, mul_div_assoc]
  · simp only [id_eq, Function.comp_def]
    rw [cpow_sub _ _ hz0, cpow_one]
    unfold legendreBranchPower
    simp only [Pi.add_apply, Pi.div_apply]
    generalize exp (μ/2*(log (z-1)+log (z+1))) = E
    have hz2 : z^2-1 ≠ 0 := by intro h; apply mul_ne_zero hm hp; linear_combination h
    have hr : z^(ν+μ+1) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hz0)
    have h2 : (2:ℂ)^(ν+1) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl two_ne_zero)
    field_simp
    ring

/-- Two continuous functions that agree off a countable set agree everywhere. -/
theorem legendre_eq_of_continuous_off_countable {f g : ℂ → ℂ} (hf : Continuous f) (hg : Continuous g)
    {S : Set ℂ} (hS : S.Countable) (h : ∀ μ ∉ S, f μ = g μ) (μ : ℂ) : f μ = g μ :=
  congrFun (Continuous.ext_on (hS.dense_compl ℂ) hf hg h) μ

/-- Two continuous functions that agree at non-integers agree everywhere. -/
theorem legendre_eq_of_continuous_nonint {f g : ℂ → ℂ} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ μ : ℂ, (∀ n : ℤ, μ ≠ n) → f μ = g μ) (μ : ℂ) : f μ = g μ :=
  legendre_eq_of_continuous_off_countable hf hg (countable_range (Int.cast : ℤ → ℂ))
    (fun μ hμ => h μ (fun n hn => hμ ⟨n, hn.symm⟩)) μ

/-- If `μ` is not an integer, then `sin (μπ) ≠ 0`. -/
theorem legendre_sin_ne_zero {μ : ℂ} (hμ : ∀ n : ℤ, μ ≠ n) : sin (μ*π) ≠ 0 := by
  rw [Ne, Complex.sin_eq_zero_iff]
  rintro ⟨k, hk⟩
  exact hμ k (mul_right_cancel₀ (ofReal_ne_zero.mpr Real.pi_ne_zero) hk)

/-- DLMF 14.9.11 on the principal sheet. -/
theorem associatedP_reflect_degree (ν μ : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    associatedP (-ν-1) μ z=associatedP ν μ z := by
  unfold associatedP
  rw [show -(-ν-1)=ν+1 by ring, show -ν-1+1 = -ν by ring,
    regularizedGaussHG_symm _ _ _ (mem_cutPlane_of_one_add (one_add_mem_slitPlane_of_sub_one hz))]

/-- For non-integer order, `𝑸^μ_ν` is locally the combination of `P^{±μ}_ν` from DLMF 14.9.15. -/
theorem olverQ_eventuallyEq_nonint (ν μ : ℂ) (hμ : ∀ n : ℤ, μ ≠ n) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    olverQ ν μ =ᶠ[𝓝 z] fun w => π/(2*sin (μ*π))*(associatedP ν μ w*(Gamma (ν+μ+1))⁻¹-
      associatedP ν (-μ) w*(Gamma (ν-μ+1))⁻¹) := by
  filter_upwards [isOpen_sub_one_mem_slitPlane.mem_nhds hz] with w hw
  have hc := olverQ_connection ν μ hw
  rw [div_eq_mul_inv (associatedP ν μ w), div_eq_mul_inv (associatedP ν (-μ) w)] at hc
  generalize (Gamma (ν+μ+1))⁻¹ = g1 at hc ⊢
  generalize (Gamma (ν-μ+1))⁻¹ = g2 at hc ⊢
  have hs := legendre_sin_ne_zero hμ
  have hs' : sin (π*μ) ≠ 0 := by rwa [mul_comm]
  have hpi : (π:ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [← hc]; field_simp

/-- For non-integer `μ` and `z - 1` in the slit plane, the `z`-derivative of `𝑸^μ_ν` is `π/(2
sin(μπ))` times `(P^μ_ν)'(z)/Γ(ν+μ+1) - (P^{-μ}_ν)'(z)/Γ(ν-μ+1)`. -/
theorem deriv_olverQ_nonint (ν μ : ℂ) (hμ : ∀ n : ℤ, μ ≠ n) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    deriv (olverQ ν μ) z = π/(2*sin (μ*π))*(deriv (associatedP ν μ) z*(Gamma (ν+μ+1))⁻¹-
      deriv (associatedP ν (-μ)) z*(Gamma (ν-μ+1))⁻¹) := by
  rw [(olverQ_eventuallyEq_nonint ν μ hμ hz).deriv_eq]
  have h1 := (associatedP_analytic ν μ z hz).differentiableAt.hasDerivAt
  have h2 := (associatedP_analytic ν (-μ) z hz).differentiableAt.hasDerivAt
  exact (((h1.mul_const _).sub (h2.mul_const _)).const_mul _).deriv

/-- For `z - 1` in the slit plane, the derivative of `P^μ_ν` is `μ/(1-z²) P^μ_ν(z) - ((ν+1)(-ν)/2)
((z+1)/(z-1))^{μ/2} 𝐅(ν+2, 1-ν; 2-μ; (1-z)/2)`. -/
theorem deriv_associatedP (ν μ : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    deriv (associatedP ν μ) z = μ/(1-z^2)*associatedP ν μ z-
      (ν+1)*(-ν)/2*(exp (μ/2*(log (z+1)-log (z-1)))*regularizedGaussHG (ν+1+1) (-ν+1) (1-μ+1) ((1-z)/2)) :=
  (hasDerivAt_associatedP_aux (ν+1) (-ν) (1-μ) μ hz).deriv

/-- For `z - 1` in the slit plane, the derivative `(P^μ_ν)'(z)` is continuous in the order `μ`. -/
theorem continuous_deriv_associatedP_order (ν : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    Continuous fun μ => deriv (associatedP ν μ) z := by
  have hw := mem_cutPlane_of_one_add (one_add_mem_slitPlane_of_sub_one hz)
  have e := funext fun μ => deriv_associatedP ν μ hz
  rw [e]
  have hP := (associatedP_entire_order ν z hz).continuous
  have hG := (differentiable_regularizedGaussHG_comp (A := fun _ : ℂ => ν+1+1) (B := fun _ : ℂ => -ν+1)
    (C := fun μ : ℂ => 1-μ+1) (by fun_prop) (by fun_prop) (by fun_prop) hw).continuous
  exact ((continuous_id.div_const _).mul hP).sub (continuous_const.mul
    ((by fun_prop : Continuous fun μ : ℂ => exp (μ/2*(log (z+1)-log (z-1)))).mul hG))

/-- For `z - 1` in the slit plane, the derivative `(𝑸^μ_ν)'(z)` is continuous in the order `μ`. -/
theorem continuous_deriv_olverQ_order (ν : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    Continuous fun μ => deriv (olverQ ν μ) z := by
  have hz0 := slitPlane_ne_zero (mem_slitPlane_of_sub_one hz)
  have : NeZero z := ⟨hz0⟩
  have hc := recip_sq_mem_cutPlane hz
  have e := funext fun μ => (hasDerivAt_olverQ ν μ hz).deriv
  rw [e]
  have hB : Continuous fun μ : ℂ => legendreBranchPower μ z := by
    unfold legendreBranchPower; fun_prop
  have hP : Continuous fun μ : ℂ => z^(ν+μ+1) := (differentiable_const_cpow_of_neZero z |>.comp
    (by fun_prop : Differentiable ℂ fun μ : ℂ => ν+μ+1)).continuous
  have hG1 := (differentiable_regularizedGaussHG_comp (A := fun μ : ℂ => (ν+μ+2)/2)
    (B := fun μ : ℂ => (ν+μ+1)/2) (C := fun _ : ℂ => ν+3/2) (by fun_prop) (by fun_prop) (by fun_prop) hc).continuous
  have hG2 := (differentiable_regularizedGaussHG_comp (A := fun μ : ℂ => (ν+μ+2)/2+1)
    (B := fun μ : ℂ => (ν+μ+1)/2+1) (C := fun _ : ℂ => ν+3/2+1) (by fun_prop) (by fun_prop) (by fun_prop) hc).continuous
  have hD : ∀ μ : ℂ, (2:ℂ)^(ν+1)*z^(ν+μ+1) ≠ 0 := fun μ =>
    mul_ne_zero (cpow_ne_zero_iff.mpr (Or.inl two_ne_zero)) (cpow_ne_zero_iff.mpr (Or.inl hz0))
  exact ((continuous_const.mul hB).div (continuous_const.mul hP) hD).mul
    (((by fun_prop : Continuous fun μ : ℂ => μ*z/(z^2-1)-(ν+μ+1)/z).mul hG1).add
      (((by fun_prop : Continuous fun μ : ℂ => (ν+μ+2)/2*((ν+μ+1)/2)).mul hG2).mul continuous_const))

/-- If `z - 1` lies in the slit plane, then `z² - 1 ≠ 0`. -/
theorem legendre_sq_sub_one_ne_zero {z : ℂ} (hz : z-1 ∈ slitPlane) : z^2-1 ≠ 0 := by
  have hm := slitPlane_ne_zero hz
  have hp := slitPlane_ne_zero (one_add_mem_slitPlane_of_sub_one hz)
  intro h; apply mul_ne_zero hm hp; linear_combination h

/-- Continuity in the order of a Wronskian at a fixed point. -/
theorem continuous_legendreWronskian_order {f g : ℂ → ℂ → ℂ} {z : ℂ}
    (hf : Continuous fun μ => f μ z) (hf' : Continuous fun μ => deriv (f μ) z)
    (hg : Continuous fun μ => g μ z) (hg' : Continuous fun μ => deriv (g μ) z) :
    Continuous fun μ => ODE.wronskian (f μ) (g μ) z :=
  (hf.mul hg').sub (hg.mul hf')

/-- For non-integer `μ` and `z - 1` in the slit plane, the Wronskian `W{P^{-μ}_ν, 𝑸^μ_ν}(z) =
-1/(Γ(ν+μ+1) (z²-1))`; the non-integer case of DLMF 14.2.8. -/
theorem associated_wronskian_8_nonint (ν μ : ℂ) (hμ : ∀ n : ℤ, μ ≠ n) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    ODE.wronskian (associatedP ν (-μ)) (olverQ ν μ) z = -(Gamma (ν+μ+1))⁻¹*(z^2-1)⁻¹ := by
  have h7 := associated_wronskian_7 ν μ hz
  unfold ODE.wronskian at h7 ⊢
  rw [deriv_olverQ_nonint ν μ hμ hz, (olverQ_eventuallyEq_nonint ν μ hμ hz).eq_of_nhds]
  generalize (Gamma (ν+μ+1))⁻¹ = g1
  generalize (Gamma (ν-μ+1))⁻¹ = g2
  have hs := legendre_sin_ne_zero hμ
  have hs' : sin (π*μ) ≠ 0 := by rwa [mul_comm]
  have hpi : (π:ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hz2 := legendre_sq_sub_one_ne_zero hz
  have hz2' : 1-z^2 ≠ 0 := fun h => hz2 (by linear_combination -h)
  linear_combination (norm := skip) (π/(2*sin (μ*π))*g1)*h7
  field_simp
  ring

/-- For non-integer `μ` and `z - 1` in the slit plane, the Wronskian `W{P^μ_ν, 𝑸^μ_ν}(z) =
-1/(Γ(ν-μ+1) (z²-1))`. -/
theorem olverQ_wronskian_pos_nonint (ν μ : ℂ) (hμ : ∀ n : ℤ, μ ≠ n) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    ODE.wronskian (associatedP ν μ) (olverQ ν μ) z = -(Gamma (ν-μ+1))⁻¹*(z^2-1)⁻¹ := by
  have h7 := associated_wronskian_7 ν μ hz
  unfold ODE.wronskian at h7 ⊢
  rw [deriv_olverQ_nonint ν μ hμ hz, (olverQ_eventuallyEq_nonint ν μ hμ hz).eq_of_nhds]
  generalize (Gamma (ν+μ+1))⁻¹ = g1
  generalize (Gamma (ν-μ+1))⁻¹ = g2
  have hs := legendre_sin_ne_zero hμ
  have hs' : sin (π*μ) ≠ 0 := by rwa [mul_comm]
  have hpi : (π:ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hz2 := legendre_sq_sub_one_ne_zero hz
  have hz2' : 1-z^2 ≠ 0 := fun h => hz2 (by linear_combination -h)
  linear_combination (norm := skip) (π/(2*sin (μ*π))*g2)*h7
  field_simp
  ring

/-- For `z - 1` in the slit plane, `μ ↦ P^{-μ}_ν(z)` is continuous. -/
theorem continuous_associatedP_neg_order (ν : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    Continuous fun μ => associatedP ν (-μ) z :=
  (associatedP_entire_order ν z hz).continuous.comp continuous_neg

/-- For `z - 1` in the slit plane, `μ ↦ (P^{-μ}_ν)'(z)` is continuous. -/
theorem continuous_deriv_associatedP_neg_order (ν : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    Continuous fun μ => deriv (associatedP ν (-μ)) z :=
  (continuous_deriv_associatedP_order ν hz).comp continuous_neg

/-- DLMF 14.2.8: for `z-1` in the slit plane (`z ∉ (-∞, 1]`), `𝒲{P^{-μ}_ν(z), 𝑸^μ_ν(z)} =
-1/(Γ(ν+μ+1) (z²-1))`. -/
@[dlmf 14.2.E8]
theorem associated_wronskian_8 (ν μ : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    ODE.wronskian (associatedP ν (-μ)) (olverQ ν μ) z=-1/(Gamma (ν+μ+1)*(z^2-1)) := by
  have key := legendre_eq_of_continuous_nonint
    (f := fun μ => ODE.wronskian (associatedP ν (-μ)) (olverQ ν μ) z)
    (g := fun μ => -(Gamma (ν+μ+1))⁻¹*(z^2-1)⁻¹)
    (continuous_legendreWronskian_order (continuous_associatedP_neg_order ν hz)
      (continuous_deriv_associatedP_neg_order ν hz) (olverQ_entire_order ν z hz).continuous
      (continuous_deriv_olverQ_order ν hz))
    ((continuous_recip_Gamma.comp (by fun_prop)).neg.mul continuous_const)
    (fun μ hμ => associated_wronskian_8_nonint ν μ hμ hz) μ
  rw [key, div_eq_mul_inv, mul_inv]; ring

/-- For all complex `ν, μ` and `z - 1` in the slit plane, the Wronskian `W{P^μ_ν, 𝑸^μ_ν}(z) =
-1/(Γ(ν-μ+1) (z²-1))`, extended from non-integer `μ` by continuity in the order. -/
theorem olverQ_wronskian_pos (ν μ : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    ODE.wronskian (associatedP ν μ) (olverQ ν μ) z = -(Gamma (ν-μ+1))⁻¹*(z^2-1)⁻¹ :=
  legendre_eq_of_continuous_nonint
    (f := fun μ => ODE.wronskian (associatedP ν μ) (olverQ ν μ) z)
    (g := fun μ => -(Gamma (ν-μ+1))⁻¹*(z^2-1)⁻¹)
    (continuous_legendreWronskian_order (associatedP_entire_order ν z hz).continuous
      (continuous_deriv_associatedP_order ν hz) (olverQ_entire_order ν z hz).continuous
      (continuous_deriv_olverQ_order ν hz))
    ((continuous_recip_Gamma.comp (by fun_prop)).neg.mul continuous_const)
    (fun μ hμ => olverQ_wronskian_pos_nonint ν μ hμ hz) μ

/-- DLMF 14.2.10: when `ν+μ ∉ {-1,-2,…}` and for `z-1` in the slit plane (`z ∉ (-∞, 1]`),
`𝒲{P^μ_ν(z), Q^μ_ν(z)} = -e^{μπi} Γ(ν+μ+1)/(Γ(ν-μ+1) (z²-1))`. -/
@[dlmf 14.2.E10]
theorem associated_wronskian_10 (ν μ : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    ODE.wronskian (associatedP ν μ) (associatedQ ν μ) z=-exp (μ*π*I)*Gamma (ν+μ+1)/(Gamma (ν-μ+1)*(z^2-1)) := by
  have hW := olverQ_wronskian_pos ν μ hz
  have hd : deriv (associatedQ ν μ) z = exp (μ*π*I)*Gamma (ν+μ+1)*deriv (olverQ ν μ) z :=
    deriv_const_mul _ (olverQ_analytic ν μ z hz).differentiableAt
  unfold ODE.wronskian at hW ⊢
  rw [hd]
  simp only [associatedQ]
  rw [div_eq_mul_inv, mul_inv]
  linear_combination (exp (μ*π*I)*Gamma (ν+μ+1))*hW

/-- For non-integer `μ` and `z - 1` in the slit plane, near `z` the function `𝑸^μ_{-ν-1}` equals
`π/(2 sin(μπ)) (P^μ_ν/Γ(μ-ν) - P^{-μ}_ν/Γ(-ν-μ))`, using `P^{±μ}_{-ν-1} = P^{±μ}_ν`. -/
theorem olverQ_reflect_eventuallyEq_nonint (ν μ : ℂ) (hμ : ∀ n : ℤ, μ ≠ n) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    olverQ (-ν-1) μ =ᶠ[𝓝 z] fun w => π/(2*sin (μ*π))*(associatedP ν μ w*(Gamma (-ν-1+μ+1))⁻¹-
      associatedP ν (-μ) w*(Gamma (-ν-1-μ+1))⁻¹) := by
  filter_upwards [olverQ_eventuallyEq_nonint (-ν-1) μ hμ hz,
    isOpen_sub_one_mem_slitPlane.mem_nhds hz] with w hw hw'
  rw [hw, associatedP_reflect_degree ν μ hw', associatedP_reflect_degree ν (-μ) hw']

/-- For non-integer `μ` and `z - 1` in the slit plane, the Wronskian `W{𝑸^μ_ν, 𝑸^μ_{-ν-1}}(z) =
cos(νπ)/(z²-1)`; the non-integer case of DLMF 14.2.9. -/
theorem associated_wronskian_9_nonint (ν μ : ℂ) (hμ : ∀ n : ℤ, μ ≠ n) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    ODE.wronskian (olverQ ν μ) (olverQ (-ν-1) μ) z=cos (ν*π)*(z^2-1)⁻¹ := by
  have h7 := associated_wronskian_7 ν μ hz
  have he := olverQ_reflect_eventuallyEq_nonint ν μ hμ hz
  have hd2 : deriv (olverQ (-ν-1) μ) z = π/(2*sin (μ*π))*(deriv (associatedP ν μ) z*(Gamma (-ν-1+μ+1))⁻¹-
      deriv (associatedP ν (-μ)) z*(Gamma (-ν-1-μ+1))⁻¹) := by
    rw [he.deriv_eq]
    have h1 := (associatedP_analytic ν μ z hz).differentiableAt.hasDerivAt
    have h2 := (associatedP_analytic ν (-μ) z hz).differentiableAt.hasDerivAt
    exact (((h1.mul_const _).sub (h2.mul_const _)).const_mul _).deriv
  have r1 := legendre_recip_Gamma_reflection (ν+μ+1)
  have r2 := legendre_recip_Gamma_reflection (ν-μ+1)
  rw [show 1-(ν+μ+1) = -ν-1-μ+1 by ring] at r1
  rw [show 1-(ν-μ+1) = -ν-1+μ+1 by ring] at r2
  have t1 : sin (π*(ν+μ+1)) = -(sin (ν*π)*cos (μ*π)+cos (ν*π)*sin (μ*π)) := by
    rw [show (π:ℂ)*(ν+μ+1) = ν*π+μ*π+π by ring, sin_add_pi, sin_add]
  have t2 : sin (π*(ν-μ+1)) = -(sin (ν*π)*cos (μ*π)-cos (ν*π)*sin (μ*π)) := by
    rw [show (π:ℂ)*(ν-μ+1) = ν*π-μ*π+π by ring, sin_add_pi, sin_sub]
  unfold ODE.wronskian at h7 ⊢
  rw [hd2, he.eq_of_nhds, deriv_olverQ_nonint ν μ hμ hz, (olverQ_eventuallyEq_nonint ν μ hμ hz).eq_of_nhds]
  generalize (Gamma (ν+μ+1))⁻¹ = g1 at r1 ⊢
  generalize (Gamma (ν-μ+1))⁻¹ = g2 at r2 ⊢
  generalize (Gamma (-ν-1+μ+1))⁻¹ = h1 at r2 ⊢
  generalize (Gamma (-ν-1-μ+1))⁻¹ = h2 at r1 ⊢
  have hs := legendre_sin_ne_zero hμ
  have hs' : sin (π*μ) ≠ 0 := by rwa [mul_comm]
  have hpi : (π:ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hE : g1*h2-g2*h1 = -2*cos (ν*π)*sin (μ*π)/π := by
    rw [eq_div_iff hpi]; linear_combination r1 - r2 + t1 - t2
  have hz2 := legendre_sq_sub_one_ne_zero hz
  have hz2' : 1-z^2 ≠ 0 := fun h => hz2 (by linear_combination -h)
  linear_combination (norm := skip) ((π/(2*sin (μ*π)))^2*(g1*h2-g2*h1))*h7 +
    ((π/(2*sin (μ*π)))^2*(2*sin (μ*π)/(π*(1-z^2))))*hE
  field_simp
  ring

/-- DLMF 14.2.9: for `z-1` in the slit plane (`z ∉ (-∞, 1]`), `𝒲{𝑸^μ_ν(z), 𝑸^μ_{-ν-1}(z)} =
cos(νπ)/(z²-1)`. -/
@[dlmf 14.2.E9]
theorem associated_wronskian_9 (ν μ : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    ODE.wronskian (olverQ ν μ) (olverQ (-ν-1) μ) z=cos (ν*π)/(z^2-1) := by
  have key := legendre_eq_of_continuous_nonint
    (f := fun μ => ODE.wronskian (olverQ ν μ) (olverQ (-ν-1) μ) z)
    (g := fun _ => cos (ν*π)*(z^2-1)⁻¹)
    (continuous_legendreWronskian_order (olverQ_entire_order ν z hz).continuous
      (continuous_deriv_olverQ_order ν hz) (olverQ_entire_order (-ν-1) z hz).continuous
      (continuous_deriv_olverQ_order (-ν-1) hz))
    continuous_const
    (fun μ hμ => associated_wronskian_9_nonint ν μ hμ hz) μ
  rw [key, div_eq_mul_inv]

/-- DLMF 14.29.1: `f` satisfies the generalized Legendre equation at `z`, `(1-z²) f'' - 2z f' +
(ν(ν+1) - μ₁²/(2(1-z)) - μ₂²/(2(1+z))) f = 0`. -/
@[dlmf 14.29.E1]
def IsGeneralizedLegendreSolution (ν μ₁ μ₂ : ℂ) (f : ℂ → ℂ) (z : ℂ) : Prop :=
  (1-z^2)*iteratedDeriv 2 f z-2*z*deriv f z+(ν*(ν+1)-μ₁^2/(2*(1-z))-μ₂^2/(2*(1+z)))*f z=0

/-- DLMF 14.29.1 with `μ₁ = μ₂ = μ`: for `z ≠ ±1` the generalized Legendre equation reduces to the
associated Legendre equation `(1-z²) f'' - 2z f' + (ν(ν+1) - μ²/(1-z²)) f = 0`. -/
@[dlmf 14.29.E1]
theorem generalizedLegendre_equal_orders (ν μ : ℂ) (f : ℂ → ℂ) {z : ℂ} (hz : z ≠ 1) (hzm : z ≠ -1) :
    IsGeneralizedLegendreSolution ν μ μ f z ↔ (1-z^2)*iteratedDeriv 2 f z-2*z*deriv f z+(ν*(ν+1)-μ^2/(1-z^2))*f z=0 := by
  unfold IsGeneralizedLegendreSolution
  have h1 : 1-z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
  have h2 : 1+z ≠ 0 := by intro h; apply hzm; linear_combination h
  have he : μ^2/(2*(1-z))+μ^2/(2*(1+z))=μ^2/(1-z^2) := by
    have h3 : 1-z^2=(1-z)*(1+z) := by ring
    rw [h3]
    field_simp
    ring
  have heq : ν*(ν+1)-μ^2/(2*(1-z))-μ^2/(2*(1+z))=ν*(ν+1)-μ^2/(1-z^2) := by
    linear_combination -he
  rw [heq]

/-- The gauge factor behind the negative-integer-order formula on the cut plane. -/
theorem associated_gauge_neg_nat (m : ℕ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    exp ((m:ℂ)/2*(log (z+1)-log (z-1))) * ((1-z)/2)^m * ((1-(1-z)/2)^m)⁻¹ =
      (-1)^m * exp (-(m:ℂ)/2*(log (z+1)-log (z-1))) := by
  have h0 : z-1 ≠ 0 := slitPlane_ne_zero hz
  have h1 : z+1 ≠ 0 := by
    simpa [add_comm] using slitPlane_ne_zero (one_add_mem_slitPlane_of_sub_one hz)
  have key : exp ((m:ℂ)/2*(log (z+1)-log (z-1))) * (z-1)^m =
      exp (-(m:ℂ)/2*(log (z+1)-log (z-1))) * (z+1)^m := by
    have ha : (z-1)^m = exp (m*log (z-1)) := by rw [exp_nat_mul, exp_log h0]
    have hb : (z+1)^m = exp (m*log (z+1)) := by rw [exp_nat_mul, exp_log h1]
    rw [ha, hb, ← exp_add, ← exp_add]
    congr 1; ring
  rw [show 1-(1-z)/2 = (z+1)/2 by ring, show (1-z)/2 = (-1)*(z-1)/2 by ring, div_pow, div_pow,
    mul_pow]
  have h1m : (z+1)^m ≠ 0 := pow_ne_zero _ h1
  generalize exp ((m:ℂ)/2*(log (z+1)-log (z-1))) = E1 at key ⊢
  generalize exp (-(m:ℂ)/2*(log (z+1)-log (z-1))) = E2 at key ⊢
  field_simp
  linear_combination key

/-- The Pochhammer product behind the negative-integer-order formulas. -/
theorem poch_mul_poch_neg_mul_Gamma (ν : ℂ) (m : ℕ) (h : ∀ n : ℕ, ν-m+1 ≠ -n) :
    poch (ν+1) m * poch (-ν) m * Gamma (ν-m+1) = (-1)^m * Gamma (ν+m+1) := by
  have h1 := poch_one_sub_sub (ν-m+1) m
  rw [show 1-(ν-m+1)-(m:ℂ) = -ν by ring] at h1
  have h2 := poch_add (ν-m+1) m m
  rw [show ν-m+1+(m:ℂ) = ν+1 by ring] at h2
  have h3 := Gamma_add_nat_div_Gamma_eq (n := m+m) (ν-m+1) h
  rw [show ν-m+1+((m+m:ℕ):ℂ) = ν+m+1 by push_cast; ring] at h3
  rw [div_eq_iff (Gamma_ne_zero h)] at h3
  rw [h1, h3, ← poch, h2]
  ring

/-- Under the hypothesis of DLMF 14.9.3, `Γ(ν+m+1)` is regular and nonzero. -/
theorem Gamma_add_nat_ne_zero (ν : ℂ) (m : ℕ) (h : ∀ n : ℕ, ν-m+1 ≠ -n) : Gamma (ν+m+1) ≠ 0 :=
  Gamma_ne_zero fun n hn => h (n+2*m) (by push_cast; linear_combination hn)

/-- DLMF 15.2.3_5 followed by Euler's transformation for the Legendre parameters `ν+1, -ν`. -/
theorem regularizedGaussHG_legendre_neg_nat (ν : ℂ) (m : ℕ) {w : ℂ} (hw : w ∈ cutPlane) :
    regularizedGaussHG (ν+1) (-ν) (1-((m+1:ℕ):ℂ)) w = poch (ν+1) (m+1) * poch (-ν) (m+1) *
      w^(m+1) * ((1-w)^(m+1))⁻¹ * regularizedGaussHG (ν+1) (-ν) ((m+1:ℕ)+1) w := by
  rw [show 1-((m+1:ℕ):ℂ) = -(m:ℂ) by push_cast; ring, regularizedGaussHG_neg_nat _ _ _ hw,
    regularizedGaussHG_euler _ _ _ hw,
    show (m:ℂ)+2-(ν+1+m+1)-(-ν+m+1) = -((m+1:ℕ):ℂ) by push_cast; ring,
    show (m:ℂ)+2-(ν+1+m+1) = -ν by ring, show (m:ℂ)+2-(-ν+m+1) = ν+1 by ring,
    regularizedGaussHG_symm _ _ _ hw, cpow_neg, cpow_natCast,
    show (m:ℂ)+2 = ((m+1:ℕ):ℂ)+1 by push_cast; ring]
  ring

/-- The Ferrers gauge factor behind DLMF 14.9.3. -/
theorem ferrers_gauge_neg_nat (m : ℕ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    (((1+x)/(1-x):ℝ):ℂ)^((m:ℂ)/2) * ((1-(x:ℂ))/2)^m * ((1-(1-(x:ℂ))/2)^m)⁻¹ =
      (((1+x)/(1-x):ℝ):ℂ)^(-(m:ℂ)/2) := by
  have h1 : (0:ℝ) < 1+x := by linarith [hx.1]
  have h2 : (0:ℝ) < 1-x := by linarith [hx.2]
  have hr : (((1+x)/(1-x):ℝ):ℂ) ≠ 0 := ofReal_ne_zero.mpr (div_pos h1 h2).ne'
  have h1' : (1+(x:ℂ)) ≠ 0 := by exact_mod_cast h1.ne'
  have h2' : (1-(x:ℂ)) ≠ 0 := by exact_mod_cast h2.ne'
  have hsq : (((1+x)/(1-x):ℝ):ℂ)^((m:ℂ)/2) * (((1+x)/(1-x):ℝ):ℂ)^((m:ℂ)/2) =
      ((1+(x:ℂ))/(1-x))^m := by
    rw [← cpow_add _ _ hr, add_halves, cpow_natCast]; push_cast; rfl
  have hc : (((1+x)/(1-x):ℝ):ℂ)^((m:ℂ)/2) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hr)
  rw [show -(m:ℂ)/2 = -((m:ℂ)/2) by ring, cpow_neg, show 1-(1-(x:ℂ))/2 = (1+x)/2 by ring]
  generalize (((1+x)/(1-x):ℝ):ℂ)^((m:ℂ)/2) = R at hsq hc ⊢
  rw [div_pow] at hsq
  have h1m : (1+(x:ℂ))^m ≠ 0 := pow_ne_zero _ h1'
  have h2m : (1-(x:ℂ))^m ≠ 0 := pow_ne_zero _ h2'
  rw [div_pow, div_pow]
  field_simp
  field_simp at hsq
  linear_combination hsq
/-- The Legendre Pochhammer product `(ν+1)ₘ(-ν)ₘ = (-1)ᵐ (ν-m+1)₂ₘ`. -/
theorem poch_mul_poch_neg (ν : ℂ) (m : ℕ) :
    poch (ν+1) m * poch (-ν) m = (-1)^m * poch (ν-m+1) (2*m) := by
  have h1 := poch_one_sub_sub (ν-m+1) m
  rw [show 1-(ν-m+1)-(m:ℂ) = -ν by ring] at h1
  have h2 := poch_add (ν-m+1) m m
  rw [show ν-m+1+(m:ℂ) = ν+1 by ring] at h2
  rw [h1, two_mul, h2]
  ring

/-- The Ferrers gauge factor at nonnegative integer order. -/
theorem ferrers_gauge_nat (m : ℕ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    (((1+x)/(1-x):ℝ):ℂ)^((m:ℂ)/2) * ((1-(x:ℂ))/2)^m = (1-(x:ℂ)^2)^((m:ℂ)/2)/2^m := by
  have ha : (0:ℝ) ≤ 1+x := by linarith [hx.1]
  have hb : (0:ℝ) < 1-x := by linarith [hx.2]
  have hb0 : ((1-x:ℝ):ℂ) ≠ 0 := ofReal_ne_zero.mpr hb.ne'
  have e1 : (((1+x)/(1-x):ℝ):ℂ) = ((1+x:ℝ):ℂ)/((1-x:ℝ):ℂ) := by push_cast; ring
  have e2 : 1-(x:ℂ)^2 = ((1+x:ℝ):ℂ)*((1-x:ℝ):ℂ) := by push_cast; ring
  have e3 : (1-(x:ℂ))^m = ((1-x:ℝ):ℂ)^((m:ℂ)/2) * ((1-x:ℝ):ℂ)^((m:ℂ)/2) := by
    rw [← cpow_add _ _ hb0, add_halves, cpow_natCast]; push_cast; rfl
  have hc : ((1-x:ℝ):ℂ)^((m:ℂ)/2) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hb0)
  rw [e1, e2, div_cpow_ofReal_nonneg ha hb.le, mul_cpow_ofReal_nonneg ha hb.le, div_pow, e3]
  field_simp

/-- The gauge factor of the associated Legendre function at nonnegative integer order. -/
theorem associated_gauge_nat (m : ℕ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    exp ((m:ℂ)/2*(log (z+1)-log (z-1))) * ((-1)^m * ((1-z)/2)^m) =
      legendreBranchPower m z / 2^m := by
  have h0 : z-1 ≠ 0 := slitPlane_ne_zero hz
  have ha : (z-1)^m = exp ((m:ℂ)*log (z-1)) := by rw [exp_nat_mul, exp_log h0]
  rw [← mul_pow, show (-1)*((1-z)/2) = (z-1)/2 by ring, div_pow, ha, legendreBranchPower,
    mul_div_assoc', ← exp_add]
  congr 2; ring

end DLMF.Legendre

end
