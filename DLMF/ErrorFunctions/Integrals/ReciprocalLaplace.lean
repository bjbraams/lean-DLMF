/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.ErrorFunctions.Integrals.FresnelTransforms

/-!
# Reciprocal-argument Laplace integrals of error functions

Local domination and analytic continuation for Laplace transforms involving reciprocal arguments
and square-root error functions.

Source references and common attribution are retained in
`DLMF.ErrorFunctions.Integrals`.
-/

@[expose] public noncomputable section

open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF

open scoped Real Topology Nat

namespace DLMF.Confluent

/-! ### Tools for DLMF 7.14.4 and its companion -/

/-- The antiderivative (in `x = √t`) for the Laplace transforms of DLMF 7.14.4. -/
noncomputable def erfInt_G (p α β γ : ℂ) (x : ℝ) : ℂ :=
  1/p*exp (p*(x:ℂ)^2)*erfc (α*x+γ/x) - exp (-2*α*γ)/p*((1+α/β)/2*exp (2*β*γ)*erfc (β*x+γ/x) +
    (α/β-1)/2*exp (-2*β*γ)*erfc (β*x+(-γ)/x))

/-- At `x`, the function `(erfInt_G p α β γ)` has derivative `(2*x*exp (p*(x:ℂ)^2)*erfc
(α*x+γ/x))`. -/
theorem erfInt_hasDerivAt_G {p α β γ : ℂ} (hp : p = α^2-β^2) (hp0 : p ≠ 0) (hβ : β ≠ 0)
    {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (erfInt_G p α β γ) (2*x*exp (p*(x:ℂ)^2)*erfc (α*x+γ/x)) x := by
  have hx' : (x:ℂ) ≠ 0 := by exact_mod_cast hx
  have hsq : HasDerivAt (fun x : ℝ => exp (p*(x:ℂ)^2)) (exp (p*(x:ℂ)^2)*(p*(2*x))) x := by
    have h : HasDerivAt (fun w : ℂ => p*w^2) (p*(2*(x:ℂ))) (x:ℂ) := by
      simpa using ((hasDerivAt_pow 2 (x:ℂ)).const_mul p)
    exact h.cexp.comp_ofReal
  have h1 := hasDerivAt_erfc_mul_add_div α γ hx
  have h2 := hasDerivAt_erfc_mul_add_div β γ hx
  have h3 := hasDerivAt_erfc_mul_add_div β (-γ) hx
  have h := (((hsq.const_mul (1/p)).mul h1).sub ((((h2.const_mul
    ((1+α/β)/2*exp (2*β*γ))).add (h3.const_mul ((α/β-1)/2*exp (-2*β*γ)))).const_mul
    (exp (-2*α*γ)/p))))
  convert h using 1
  · funext y; simp only [erfInt_G, Pi.mul_apply, Pi.sub_apply, Pi.add_apply]
  · have e1 : exp (-(α*x+γ/x)^2) = exp (-2*α*γ)*exp (-(β^2*x^2+γ^2/x^2))*exp (-(p*(x:ℂ)^2)) := by
      rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; rw [hp]; field_simp; ring
    have e2 : exp (-(β*x+γ/x)^2) = exp (-(β^2*x^2+γ^2/x^2))*exp (-2*β*γ) := by
      rw [← Complex.exp_add]; congr 1; field_simp; ring
    have e3 : exp (-(β*x+(-γ)/x)^2) = exp (-(β^2*x^2+γ^2/x^2))*exp (2*β*γ) := by
      rw [← Complex.exp_add]; congr 1; field_simp; ring
    have hA : exp (p*(x:ℂ)^2) * exp (-(p*(x:ℂ)^2)) = 1 := by rw [← Complex.exp_add]; simp
    have hB : exp (2*β*γ) * exp (-2*β*γ) = 1 := by rw [← Complex.exp_add]; ring_nf; simp
    rw [e1, e2, e3]
    generalize exp (-(β^2*x^2+γ^2/x^2)) = Q at *
    generalize exp (p*(x:ℂ)^2) = A at *
    generalize exp (-(p*(x:ℂ)^2)) = A' at *
    generalize exp (2*β*γ) = B at *
    generalize exp (-2*β*γ) = B' at *
    generalize (Real.sqrt π : ℂ) = P at *
    generalize erfc (α*x+γ/x) = F at *
    field_simp
    linear_combination (2*β*cexp (-(2*α*γ))*Q*((x:ℂ)^2*α-γ)/P) * hA -
      (2*β*cexp (-(2*α*γ))*Q*((x:ℂ)^2*α-γ)/P) * hB

/-- The derivative of `G(√t)`. -/
theorem erfInt_hasDerivAt_G_sqrt {p α β γ : ℂ} (hp : p = α^2-β^2) (hp0 : p ≠ 0) (hβ : β ≠ 0)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun t : ℝ => erfInt_G p α β γ (Real.sqrt t))
      (exp (p*t)*erfc (α*Real.sqrt t+γ/Real.sqrt t)) t := by
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have h := (erfInt_hasDerivAt_G (γ := γ) hp hp0 hβ hs.ne').scomp t
    (Real.hasDerivAt_sqrt ht.ne')
  have hs' : (Real.sqrt t : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hsq : (Real.sqrt t : ℂ)^2 = t := by exact_mod_cast Real.sq_sqrt ht.le
  refine (h.congr_deriv ?_ :)
  rw [hsq, real_smul]; push_cast; field_simp

/-- `erfc (βx + δ/x) → 0` as `x → ∞` when `Re β > 0` and `Re β² > 0`. -/
theorem erfInt_tendsto_erfc_atTop {β : ℂ} (hβ : 0 < β.re) (hβ2 : 0 < (β^2).re) (δ : ℂ) :
    Tendsto (fun x : ℝ => erfc (β*x+δ/x)) atTop (𝓝 0) := by
  have hinv : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  refine tendsto_erfc_zero_of_re ?_ ?_
  · have h1 : Tendsto (fun x : ℝ => δ.re*x⁻¹) atTop (𝓝 0) := by simpa using hinv.const_mul δ.re
    have : Tendsto (fun x : ℝ => β.re*x + δ.re*x⁻¹) atTop atTop :=
      (tendsto_id.const_mul_atTop hβ).atTop_add h1
    refine this.congr' ?_
    filter_upwards with x
    rw [add_re, div_ofReal_re, re_mul_ofReal]; simp [div_eq_mul_inv]
  · have h1 : Tendsto (fun x : ℝ => (δ^2).re*(x⁻¹)^2 + 2*(β*δ).re) atTop (𝓝 (2*(β*δ).re)) := by
      simpa using ((hinv.pow 2).const_mul (δ^2).re).add_const (2*(β*δ).re)
    have : Tendsto (fun x : ℝ => (β^2).re*x^2 + ((δ^2).re*(x⁻¹)^2 + 2*(β*δ).re)) atTop atTop :=
      ((tendsto_pow_atTop two_ne_zero).const_mul_atTop hβ2).atTop_add h1
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    have hx' : (x:ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hx)
    have : (β*(x:ℂ)+δ/x)^2 = β^2*((x^2:ℝ):ℂ) + 2*(β*δ) + δ^2/((x^2:ℝ):ℂ) := by
      push_cast; field_simp; ring
    rw [this]
    simp only [add_re, div_ofReal_re]
    rw [mul_comm (β^2), re_ofReal_mul]
    simp [div_eq_mul_inv]; ring

/-- **Core of DLMF 7.14.4**: with `p = α² - β²`, the Laplace-type integral
`∫₀^∞ e^{pt} erfc(α√t + γ/√t) dt` equals `e^{-2αγ-2βγ}/(β(α+β))`, given integrability and the
decay of `e^{px²} erfc(αx+γ/x)` at infinity. -/
theorem erfInt_laplace_core {p α β γ : ℂ} (hp : p = α^2-β^2) (hp0 : p ≠ 0) (hβ : 0 < β.re)
    (hβ2 : 0 < (β^2).re) (hγ : 0 < γ.re) (hγ2 : 0 < (γ^2).re) (hαβ : α + β ≠ 0)
    (hint : IntegrableOn (fun t : ℝ => exp (p*t)*erfc (α*Real.sqrt t+γ/Real.sqrt t)) (Ioi 0))
    (hlim : Tendsto (fun x : ℝ => exp (p*(x:ℂ)^2)*erfc (α*x+γ/x)) atTop (𝓝 0)) :
    (∫ t in Ioi (0:ℝ), exp (p*t)*erfc (α*Real.sqrt t+γ/Real.sqrt t)) =
      exp (-2*α*γ-2*β*γ)/(β*(α+β)) := by
  have hβ0 : β ≠ 0 := fun h => by simp [h] at hβ
  set L0 : ℂ := -(exp (-2*α*γ)/p*((α/β-1)*exp (-2*β*γ))) with hL0
  -- limit of `G` at `0⁺`
  have hG0 : Tendsto (erfInt_G p α β γ) (𝓝[>] 0) (𝓝 L0) := by
    have hx0 : Tendsto (fun x : ℝ => (x:ℂ)) (𝓝[>] 0) (𝓝 0) := by
      have := (Complex.continuous_ofReal.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
      simpa using this
    have he : Tendsto (fun x : ℝ => exp (p*(x:ℂ)^2)) (𝓝[>] 0) (𝓝 1) := by
      have := ((hx0.pow 2).const_mul p).cexp
      simpa using this
    have h1 := tendsto_erfc_mul_add_div_nhdsGT α hγ hγ2
    have h2 := tendsto_erfc_mul_add_div_nhdsGT β hγ hγ2
    have h3 : Tendsto (fun x : ℝ => erfc (β*x+(-γ)/x)) (𝓝[>] 0) (𝓝 (2 - 0)) := by
      have := (tendsto_erfc_mul_add_div_nhdsGT (-β) hγ hγ2).const_sub 2
      refine this.congr fun x => ?_
      rw [← erfc_negative]; congr 1; ring
    have := ((he.const_mul (1/p)).mul h1).sub ((((h2.const_mul ((1+α/β)/2*exp (2*β*γ))).add
      (h3.const_mul ((α/β-1)/2*exp (-2*β*γ))))).const_mul (exp (-2*α*γ)/p))
    have hv : L0 = 1/p*1*0 - exp (-2*α*γ)/p*((1+α/β)/2*exp (2*β*γ)*0 +
        (α/β-1)/2*exp (-2*β*γ)*(2-0)) := by rw [hL0]; ring
    rw [hv]
    refine this.congr fun x => ?_
    rw [erfInt_G]
  -- limit of `G` at `∞`
  have hGi : Tendsto (erfInt_G p α β γ) atTop (𝓝 0) := by
    have h2 := erfInt_tendsto_erfc_atTop hβ hβ2 γ
    have h3 := erfInt_tendsto_erfc_atTop hβ hβ2 (-γ)
    have := (hlim.const_mul (1/p)).sub ((((h2.const_mul ((1+α/β)/2*exp (2*β*γ))).add
      (h3.const_mul ((α/β-1)/2*exp (-2*β*γ))))).const_mul (exp (-2*α*γ)/p))
    simp only [mul_zero, add_zero, sub_zero] at this
    refine this.congr fun x => ?_
    rw [erfInt_G]; ring
  set f : ℝ → ℂ := Function.update (fun t : ℝ => erfInt_G p α β γ (Real.sqrt t)) 0 L0 with hf
  have hsq0 : Tendsto Real.sqrt (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have := (Real.continuous_sqrt.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
      simpa using this
    · filter_upwards [self_mem_nhdsWithin] with t ht using Real.sqrt_pos.2 ht
  have hcont : ContinuousWithinAt f (Ici 0) 0 := by
    rw [← continuousWithinAt_Ioi_iff_Ici, ContinuousWithinAt]
    have hf0 : f 0 = L0 := by simp [hf]
    rw [hf0]
    refine (hG0.comp hsq0).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    simp [hf, Function.update_of_ne (ne_of_gt (mem_Ioi.1 ht))]
  have hderiv : ∀ t ∈ Ioi (0:ℝ), HasDerivAt f
      (exp (p*t)*erfc (α*Real.sqrt t+γ/Real.sqrt t)) t := by
    intro t ht
    have ht : (0:ℝ) < t := ht
    refine (erfInt_hasDerivAt_G_sqrt hp hp0 hβ0 ht).congr_of_eventuallyEq ?_
    filter_upwards [lt_mem_nhds ht] with s hs
    simp [hf, Function.update_of_ne (ne_of_gt hs)]
  have hfi : Tendsto f atTop (𝓝 0) := by
    refine (hGi.comp Real.tendsto_sqrt_atTop).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with t ht
    simp [hf, Function.update_of_ne (ne_of_gt ht)]
  rw [integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint hfi]
  have hf0 : f 0 = L0 := by simp [hf]
  rw [hf0, hL0, hp]
  have hp' : α^2-β^2 ≠ 0 := hp ▸ hp0
  have hab : α - β ≠ 0 := fun h => hp' (by linear_combination (α+β)*h)
  rw [show -2*α*γ-2*β*γ = -2*α*γ + (-2*β*γ) by ring, Complex.exp_add]
  field_simp
  ring

/-- If `Re a > 0` and `Re c ≥ 0`, then `ac` is not a negative real number. -/
theorem erfInt_re_mul_nonneg_or {a c : ℂ} (ha : 0 < a.re) (hc : 0 ≤ c.re) :
    0 ≤ (a*c).re ∨ (a*c).im ≠ 0 := by
  by_cases h : (a*c).im = 0
  · left
    simp only [mul_re, mul_im] at h ⊢
    have : (a.re*c.re - a.im*c.im) * a.re = c.re*(a.re^2+a.im^2) := by
      linear_combination (-a.im) * h
    have h2 : 0 ≤ c.re*(a.re^2+a.im^2) := by positivity
    by_contra hneg
    push Not at hneg
    nlinarith
  · exact Or.inr h

/-- `(a t)^{1/2} = a^{1/2} √t` for `Re a > 0`, `t > 0`. -/
theorem erfInt_cpow_half_mul_ofReal {a : ℂ} (ha : 0 < a.re) {t : ℝ} (ht : 0 < t) :
    (a*t)^(1/2 : ℂ) = a^(1/2 : ℂ)*Real.sqrt t := by
  have ha0 : a ≠ 0 := fun h => by simp [h] at ha
  have hr : 0 < (a^(1/2 : ℂ)*(Real.sqrt t:ℂ)).re := by
    rw [re_mul_ofReal]; exact mul_pos (re_cpow_half_pos ha) (Real.sqrt_pos.2 ht)
  have hsq : (a^(1/2 : ℂ)*(Real.sqrt t:ℂ))^2 = a*t := by
    rw [mul_pow, cpow_half_sq ha0]; congr 1; exact_mod_cast Real.sq_sqrt ht.le
  rw [← hsq, sq_cpow_half hr]

/-- `(c/t)^{1/2} = c^{1/2}/√t` for `Re c > 0`, `t > 0`. -/
theorem erfInt_cpow_half_div_ofReal {c : ℂ} (hc : 0 < c.re) {t : ℝ} (ht : 0 < t) :
    (c/t)^(1/2 : ℂ) = c^(1/2 : ℂ)/Real.sqrt t := by
  have hc0 : c ≠ 0 := fun h => by simp [h] at hc
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have hr : 0 < (c^(1/2 : ℂ)/(Real.sqrt t:ℂ)).re := by
    rw [div_ofReal_re]; exact div_pos (re_cpow_half_pos hc) hs
  have hsq : (c^(1/2 : ℂ)/(Real.sqrt t:ℂ))^2 = c/t := by
    rw [div_pow, cpow_half_sq hc0]; congr 1; exact_mod_cast Real.sq_sqrt ht.le
  rw [← hsq, sq_cpow_half hr]

/-- `(ac)^{1/2} = a^{1/2} c^{1/2}` for `Re a > 0`, `Re c > 0`. -/
theorem erfInt_cpow_half_mul {a c : ℂ} (ha : 0 < a.re) (hc : 0 < c.re) :
    (a*c)^(1/2 : ℂ) = a^(1/2 : ℂ)*c^(1/2 : ℂ) := by
  have ha0 : a ≠ 0 := fun h => by simp [h] at ha
  have hc0 : c ≠ 0 := fun h => by simp [h] at hc
  have hr : 0 < (a^(1/2 : ℂ)*c^(1/2 : ℂ)).re := by
    refine re_mul_pos_of_re_sq_pos (re_cpow_half_pos ha) ?_ (re_cpow_half_pos hc) ?_
    · rw [cpow_half_sq ha0]; exact ha
    · rw [cpow_half_sq hc0]; exact hc.le
  have hsq : (a^(1/2 : ℂ)*c^(1/2 : ℂ))^2 = a*c := by
    rw [mul_pow, cpow_half_sq ha0, cpow_half_sq hc0]
  rw [← hsq, sq_cpow_half hr]

/-- The sharp bound for the integrand of DLMF 7.14.4: for `Re a > 0`, `Re c > 0`, `t > 0`,
`z = (at)^{1/2} + (c/t)^{1/2}` has `Re z > 0` and `Re z² ≥ Re a · t`. -/
theorem erfInt_re_sq_ge {a c : ℂ} (ha : 0 < a.re) (hc : 0 < c.re) {t : ℝ} (ht : 0 < t) :
    0 < ((a*t)^(1/2 : ℂ) + (c/t)^(1/2 : ℂ)).re ∧
      a.re*t ≤ (((a*t)^(1/2 : ℂ) + (c/t)^(1/2 : ℂ))^2).re := by
  have hat : 0 < (a*(t:ℂ)).re := by rw [re_mul_ofReal]; positivity
  have hct : 0 < (c/(t:ℂ)).re := by rw [div_ofReal_re]; positivity
  have hat0 : a*(t:ℂ) ≠ 0 := fun h => by rw [h] at hat; simp at hat
  have hct0 : c/(t:ℂ) ≠ 0 := fun h => by rw [h] at hct; simp at hct
  set u := (a*t)^(1/2 : ℂ)
  set v := (c/t)^(1/2 : ℂ)
  have hu := re_cpow_half_pos hat
  have hv := re_cpow_half_pos hct
  have hu2 : u^2 = a*t := cpow_half_sq hat0
  have hv2 : v^2 = c/t := cpow_half_sq hct0
  have huv : 0 < (u*v).re :=
    re_mul_pos_of_re_sq_pos hu (by rw [hu2]; exact hat) hv (by rw [hv2]; exact hct.le)
  refine ⟨by rw [add_re]; linarith, ?_⟩
  have : (u+v)^2 = u^2 + 2*(u*v) + v^2 := by ring
  rw [this, hu2, hv2]
  simp only [add_re, re_mul_ofReal, div_ofReal_re]
  have : (2*(u*v)).re = 2*(u*v).re := by simp
  rw [this]
  have : 0 < c.re / t := by positivity
  linarith

/-- Bound for the integrand of DLMF 7.14.4: `‖erfc((at)^{1/2} + (c/t)^{1/2})‖ ≤ 1` and
`≤ e^{-Re a t}/√(π Re a t)`. -/
theorem erfInt_norm_erfc_plus_le {a c : ℂ} (ha : 0 < a.re) (hc : 0 < c.re) {t : ℝ} (ht : 0 < t) :
    ‖erfc ((a*t)^(1/2 : ℂ) + (c/t)^(1/2 : ℂ))‖ ≤ 1 ∧
      ‖erfc ((a*t)^(1/2 : ℂ) + (c/t)^(1/2 : ℂ))‖ ≤
        Real.exp (-(a.re*t))/Real.sqrt (π*(a.re*t)) := by
  obtain ⟨h1, h2⟩ := erfInt_re_sq_ge ha hc ht
  have hat : 0 < a.re*t := by positivity
  have h2' : 0 < (((a*t)^(1/2 : ℂ) + (c/t)^(1/2 : ℂ))^2).re := lt_of_lt_of_le hat h2
  refine ⟨norm_erfc_le_one h1 h2', (norm_erfc_le h1 h2').trans ?_⟩
  rw [Complex.norm_exp, neg_re]
  gcongr

/-- A uniform exponential majorant for the integrand of DLMF 7.14.4. -/
theorem erfInt_norm_plus_le {a b c : ℂ} (ha : 0 < a.re) (hc : 0 < c.re) {t : ℝ} (ht : 0 < t) :
    ‖exp ((a-b)*t)*erfc ((a*t)^(1/2 : ℂ) + (c/t)^(1/2 : ℂ))‖ ≤
      (Real.exp (|(a-b).re| + |b.re|) + 1/Real.sqrt (π*a.re)) * Real.exp (-(b.re*t)) := by
  obtain ⟨h1, h2⟩ := erfInt_norm_erfc_plus_le ha hc ht
  have hre : ((a-b)*(t:ℂ)).re = (a.re - b.re)*t := by simp [sub_re]
  rw [norm_mul, Complex.norm_exp, hre]
  have hK : 0 ≤ 1/Real.sqrt (π*a.re) := by positivity
  rcases le_or_gt t 1 with h | h
  · have e1 : Real.exp ((a.re - b.re)*t) ≤ Real.exp (|(a-b).re|) := by
      gcongr
      have : (a-b).re = a.re - b.re := sub_re a b
      rw [← this]
      calc (a-b).re * t ≤ |(a-b).re| * t := by gcongr; exact le_abs_self _
        _ ≤ |(a-b).re| * 1 := by gcongr
        _ = _ := mul_one _
    have e2 : 1 ≤ Real.exp (|b.re|) * Real.exp (-(b.re*t)) := by
      rw [← Real.exp_add, Real.one_le_exp_iff]
      have : b.re * t ≤ |b.re| := by
        calc b.re * t ≤ |b.re| * t := by gcongr; exact le_abs_self _
          _ ≤ |b.re| * 1 := by gcongr
          _ = _ := mul_one _
      linarith
    calc Real.exp ((a.re - b.re)*t) * ‖erfc ((a*t)^(1/2 : ℂ) + (c/t)^(1/2 : ℂ))‖
        ≤ Real.exp (|(a-b).re|) * 1 := by gcongr
      _ ≤ Real.exp (|(a-b).re|) * (Real.exp (|b.re|) * Real.exp (-(b.re*t))) := by gcongr
      _ = Real.exp (|(a-b).re| + |b.re|) * Real.exp (-(b.re*t)) := by
          rw [Real.exp_add]; ring
      _ ≤ _ := by gcongr; linarith
  · have hs : Real.sqrt (π*a.re) ≤ Real.sqrt (π*(a.re*t)) :=
      Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (le_mul_of_one_le_right ha.le h.le)
        Real.pi_pos.le)
    have hs0 : 0 < Real.sqrt (π*a.re) := Real.sqrt_pos.2 (by positivity)
    calc Real.exp ((a.re - b.re)*t) * ‖erfc ((a*t)^(1/2 : ℂ) + (c/t)^(1/2 : ℂ))‖
        ≤ Real.exp ((a.re - b.re)*t) * (Real.exp (-(a.re*t))/Real.sqrt (π*(a.re*t))) := by
          gcongr
      _ ≤ Real.exp ((a.re - b.re)*t) * (Real.exp (-(a.re*t))/Real.sqrt (π*a.re)) := by gcongr
      _ = 1/Real.sqrt (π*a.re) * Real.exp (-(b.re*t)) := by
          rw [mul_div_assoc', ← Real.exp_add]; ring_nf
      _ ≤ _ := by
          gcongr
          linarith [Real.exp_pos (|(a-b).re| + |b.re|)]

/-- Continuity of the integrand of DLMF 7.14.4 on `(0, ∞)`. -/
theorem erfInt_continuousOn_plus (s : ℂ) {a c : ℂ} (ha : 0 ≤ a.re) (hc : 0 ≤ c.re) (σ : ℂ) :
    ContinuousOn (fun t : ℝ => exp (s*t)*erfc (σ*(a*t)^(1/2 : ℂ) + (c/t)^(1/2 : ℂ))) (Ioi 0) := by
  intro t ht
  have ht : (0:ℝ) < t := ht
  have ht' : (t:ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  refine ContinuousAt.continuousWithinAt ?_
  have hE : Continuous erfc := by
    unfold erfc; have := differentiable_erf_complex.continuous; fun_prop
  have h1 : ContinuousAt (fun t : ℝ => (a*t)^(1/2 : ℂ)) t := by
    refine (continuousAt_cpow_const_of_re_pos (Or.inl ?_) (by norm_num)).comp
      (by fun_prop : Continuous fun t : ℝ => a*(t:ℂ)).continuousAt
    rw [re_mul_ofReal]; positivity
  have h2 : ContinuousAt (fun t : ℝ => (c/t)^(1/2 : ℂ)) t := by
    refine (continuousAt_cpow_const_of_re_pos (Or.inl ?_) (by norm_num)).comp ?_
    · rw [div_ofReal_re]; positivity
    · exact (continuous_const.continuousAt).div (Complex.continuous_ofReal.continuousAt) ht'
  exact ((by fun_prop : Continuous fun t : ℝ => exp (s*t)).continuousAt).mul
    (hE.continuousAt.comp ((continuousAt_const.mul h1).add h2))

/-- **DLMF 7.14.4 for `Re c > 0`, `a ≠ b`.** -/
theorem erfInt_laplace_plus_of_re_pos {a b c : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) (hc : 0 < c.re)
    (hab : a ≠ b) :
    (∫ t : ℝ in Ioi 0, exp ((a-b)*t)*erfc ((a*t)^(1/2 : ℂ)+(c/t)^(1/2 : ℂ))) =
      exp (-2*((a*c)^(1/2 : ℂ)+(b*c)^(1/2 : ℂ)))/(b^(1/2 : ℂ)*(a^(1/2 : ℂ)+b^(1/2 : ℂ))) := by
  have ha0 : a ≠ 0 := fun h => by simp [h] at ha
  have hb0 : b ≠ 0 := fun h => by simp [h] at hb
  have hc0 : c ≠ 0 := fun h => by simp [h] at hc
  set α := a^(1/2 : ℂ) with hα
  set β := b^(1/2 : ℂ) with hβ
  set γ := c^(1/2 : ℂ) with hγ
  have hαr : 0 < α.re := re_cpow_half_pos ha
  have hβr : 0 < β.re := re_cpow_half_pos hb
  have hγr : 0 < γ.re := re_cpow_half_pos hc
  have hα2 : α^2 = a := cpow_half_sq ha0
  have hβ2 : β^2 = b := cpow_half_sq hb0
  have hγ2 : γ^2 = c := cpow_half_sq hc0
  have hp : a - b = α^2 - β^2 := by rw [hα2, hβ2]
  have hp0 : a - b ≠ 0 := sub_ne_zero.2 hab
  have hαβ : α + β ≠ 0 := fun h => by
    have := congrArg re h; simp at this; linarith
  -- the integrand in `√t` form
  have hform : ∀ t : ℝ, 0 < t → exp ((a-b)*t)*erfc ((a*t)^(1/2 : ℂ)+(c/t)^(1/2 : ℂ)) =
      exp ((a-b)*t)*erfc (α*Real.sqrt t+γ/Real.sqrt t) := by
    intro t ht
    rw [erfInt_cpow_half_mul_ofReal ha ht, erfInt_cpow_half_div_ofReal hc ht]
  have hint0 : IntegrableOn (fun t : ℝ => exp ((a-b)*t)*erfc ((a*t)^(1/2 : ℂ)+(c/t)^(1/2 : ℂ)))
      (Ioi 0) := by
    have hg : IntegrableOn (fun t : ℝ => (Real.exp (|(a-b).re| + |b.re|) +
        1/Real.sqrt (π*a.re)) * Real.exp (-(b.re*t))) (Ioi 0) := by
      have : IntegrableOn (fun t : ℝ => (Real.exp (|(a-b).re| + |b.re|) +
          1/Real.sqrt (π*a.re)) * Real.exp (-b.re*t)) (Ioi 0) :=
        (exp_neg_integrableOn_Ioi 0 hb).const_mul _
      refine this.congr_fun (fun t _ => by ring_nf) measurableSet_Ioi
    refine hg.mono' ?_ ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall
      fun t ht => erfInt_norm_plus_le ha hc ht))
    have := erfInt_continuousOn_plus (a-b) ha.le hc.le 1
    simp only [one_mul] at this
    exact this.aestronglyMeasurable measurableSet_Ioi
  have hint : IntegrableOn (fun t : ℝ => exp ((a-b)*t)*erfc (α*Real.sqrt t+γ/Real.sqrt t))
      (Ioi 0) := hint0.congr_fun (fun t ht => hform t ht) measurableSet_Ioi
  have hlim : Tendsto (fun x : ℝ => exp ((a-b)*(x:ℂ)^2)*erfc (α*x+γ/x)) atTop (𝓝 0) := by
    have hd : Tendsto (fun x : ℝ => (Real.exp (|(a-b).re| + |b.re|) + 1/Real.sqrt (π*a.re)) *
        Real.exp (-(b.re*x^2))) atTop (𝓝 0) := by
      have : Tendsto (fun x : ℝ => -(b.re*x^2)) atTop atBot :=
        tendsto_neg_atTop_atBot.comp ((tendsto_pow_atTop two_ne_zero).const_mul_atTop hb)
      simpa using (Real.tendsto_exp_atBot.comp this).const_mul
        (Real.exp (|(a-b).re| + |b.re|) + 1/Real.sqrt (π*a.re))
    refine squeeze_zero_norm' ?_ hd
    filter_upwards [eventually_gt_atTop 0] with x hx
    have hx2 : (0:ℝ) < x^2 := by positivity
    have := erfInt_norm_plus_le (b := b) ha hc hx2
    rw [hform _ hx2, Real.sqrt_sq hx.le] at this
    push_cast at this
    exact this
  have hcore := erfInt_laplace_core hp hp0 hβr (by rw [hβ2]; exact hb) hγr (by rw [hγ2]; exact hc)
    hαβ hint hlim
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t ht => hform t ht), hcore,
    erfInt_cpow_half_mul ha hc, erfInt_cpow_half_mul hb hc]
  simp only [hα, hβ, hγ]
  congr 1
  ring_nf

/-- Continuity of `w ↦ w^{1/2}` at points with `Re w ≥ 0`. -/
theorem erfInt_continuousAt_cpow_half {w : ℂ} (hw : 0 ≤ w.re ∨ w.im ≠ 0) :
    ContinuousAt (fun z : ℂ => z^(1/2 : ℂ)) w :=
  continuousAt_cpow_const_of_re_pos hw (by norm_num)

/-- `ε ↦ (c+ε)/t` and the half power: continuity at `ε = 0` for `Re c ≥ 0`, `t > 0`. -/
theorem erfInt_tendsto_cpow_half_shift {c : ℂ} (hc : 0 ≤ c.re) {t : ℝ} (ht : 0 < t) :
    Tendsto (fun ε : ℝ => ((c+ε)/t)^(1/2 : ℂ)) (𝓝[>] 0) (𝓝 ((c/t)^(1/2 : ℂ))) := by
  have hg : ContinuousAt (fun z : ℂ => z^(1/2:ℂ)) ((c + ((0:ℝ):ℂ))/(t:ℂ)) :=
    erfInt_continuousAt_cpow_half (Or.inl (by
      simp only [ofReal_zero, add_zero, div_ofReal_re]; positivity))
  have hf : ContinuousAt (fun ε : ℝ => (c+(ε:ℂ))/(t:ℂ)) 0 := by fun_prop
  have h : ContinuousAt (fun ε : ℝ => ((c+ε)/t)^(1/2 : ℂ)) 0 :=
    ContinuousAt.comp (g := fun z : ℂ => z^(1/2:ℂ)) hg hf
  have := h.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
  simpa using this

/-- **DLMF 7.14.4** in full: `Re a > 0`, `Re b > 0`, `Re c ≥ 0`. From
`erfInt_laplace_plus_of_re_pos` by continuity in `(b, c) ↦ (b+ε, c+ε)`, `ε → 0⁺`. -/
theorem erfInt_laplace_plus {a b c : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) (hc : 0 ≤ c.re) :
    (∫ t : ℝ in Ioi 0, exp ((a-b)*t)*erfc ((a*t)^(1/2 : ℂ)+(c/t)^(1/2 : ℂ))) =
      exp (-2*((a*c)^(1/2 : ℂ)+(b*c)^(1/2 : ℂ)))/(b^(1/2 : ℂ)*(a^(1/2 : ℂ)+b^(1/2 : ℂ))) := by
  set F : ℝ → ℝ → ℂ := fun ε t => exp ((a-(b+ε))*t)*erfc ((a*t)^(1/2 : ℂ)+((c+ε)/t)^(1/2 : ℂ))
    with hF
  set R : ℝ → ℂ := fun ε => exp (-2*((a*(c+ε))^(1/2 : ℂ)+((b+ε)*(c+ε))^(1/2 : ℂ)))/
    ((b+ε)^(1/2 : ℂ)*(a^(1/2 : ℂ)+(b+ε)^(1/2 : ℂ))) with hR
  have hre1 : ∀ ε : ℝ, 0 < ε → 0 < (b+ε).re ∧ 0 < (c+ε).re := fun ε hε => by
    simp only [add_re, ofReal_re]; constructor <;> linarith
  -- the integrals converge
  set K : ℝ := Real.exp (|(a-b).re| + 1 + (|b.re| + 1)) + 1/Real.sqrt (π*a.re) with hK
  have hI : Tendsto (fun ε => ∫ t in Ioi (0:ℝ), F ε t) (𝓝[>] 0) (𝓝 (∫ t in Ioi (0:ℝ), F 0 t)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun t => K * Real.exp (-b.re*t))
      ?_ ?_ ((exp_neg_integrableOn_Ioi 0 hb).const_mul K) ?_
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      have := erfInt_continuousOn_plus (a-(b+ε)) (a := a) (c := c+ε) ha.le (hre1 ε hε).2.le 1
      simp only [one_mul] at this
      exact this.aestronglyMeasurable measurableSet_Ioi
    · filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with ε hε
      refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
      have ht : (0:ℝ) < t := ht
      have h := erfInt_norm_plus_le (b := b+ε) ha (hre1 ε hε.1).2 ht
      refine h.trans ?_
      have e1 : |(a-(b+ε)).re| ≤ |(a-b).re| + 1 := by
        have : (a-(b+ε)).re = (a-b).re - ε := by simp [sub_re]; ring
        rw [this]
        calc |(a-b).re - ε| ≤ |(a-b).re| + |ε| := abs_sub _ _
          _ ≤ _ := by rw [abs_of_pos hε.1]; linarith [hε.2]
      have e2 : |(b+ε).re| ≤ |b.re| + 1 := by
        simp only [add_re, ofReal_re]
        calc |b.re + ε| ≤ |b.re| + |ε| := abs_add_le _ _
          _ ≤ _ := by rw [abs_of_pos hε.1]; linarith [hε.2]
      have e3 : Real.exp (-((b+ε).re*t)) ≤ Real.exp (-b.re*t) := by
        gcongr; simp only [add_re, ofReal_re]; nlinarith [hε.1]
      have hK' : Real.exp (|(a-(b+ε)).re| + |(b+ε).re|) + 1/Real.sqrt (π*a.re) ≤ K := by
        simp only [hK]; gcongr
      exact mul_le_mul hK' e3 (by positivity) (by simp only [hK]; positivity)
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
      have ht : (0:ℝ) < t := ht
      have hE : Continuous erfc := by
        unfold erfc; have := differentiable_erf_complex.continuous; fun_prop
      have h1 : Tendsto (fun ε : ℝ => exp ((a-(b+ε))*t)) (𝓝[>] 0) (𝓝 (exp ((a-(b+((0:ℝ):ℂ)))*t))) :=
        ((by fun_prop : Continuous fun ε : ℝ => exp ((a-(b+ε))*t)).tendsto 0).mono_left
          nhdsWithin_le_nhds
      have h2 := ((hE.tendsto _).comp ((erfInt_tendsto_cpow_half_shift hc ht).const_add
        ((a*t)^(1/2 : ℂ))))
      have := h1.mul h2
      simp only [ofReal_zero, add_zero] at this
      simpa [hF] using this
  -- the right-hand sides converge
  have hRc : Tendsto R (𝓝[>] 0) (𝓝 (R 0)) := by
    have hbc : ContinuousAt (fun ε : ℝ => (b+ε)^(1/2 : ℂ)) 0 :=
      ContinuousAt.comp (g := fun z : ℂ => z^(1/2:ℂ)) (f := fun ε : ℝ => b+(ε:ℂ))
        (erfInt_continuousAt_cpow_half (Or.inl (by simp; exact hb.le))) (by fun_prop)
    have hac : ContinuousAt (fun ε : ℝ => (a*(c+ε))^(1/2 : ℂ)) 0 :=
      ContinuousAt.comp (g := fun z : ℂ => z^(1/2:ℂ)) (f := fun ε : ℝ => a*(c+(ε:ℂ)))
        (erfInt_continuousAt_cpow_half (by simpa using erfInt_re_mul_nonneg_or ha hc))
        (by fun_prop)
    have hbc' : ContinuousAt (fun ε : ℝ => ((b+ε)*(c+ε))^(1/2 : ℂ)) 0 :=
      ContinuousAt.comp (g := fun z : ℂ => z^(1/2:ℂ)) (f := fun ε : ℝ => (b+(ε:ℂ))*(c+(ε:ℂ)))
        (erfInt_continuousAt_cpow_half (by simpa using erfInt_re_mul_nonneg_or hb hc))
        (by fun_prop)
    have hden : ((b+((0:ℝ):ℂ))^(1/2 : ℂ)*(a^(1/2 : ℂ)+(b+((0:ℝ):ℂ))^(1/2 : ℂ))) ≠ 0 := by
      simp only [ofReal_zero, add_zero]
      have h1 := re_cpow_half_pos hb
      have h2 := re_cpow_half_pos ha
      refine mul_ne_zero (fun h => by rw [h] at h1; simp at h1) (fun h => ?_)
      have := congrArg re h; simp at this; linarith
    have hcont : ContinuousAt R 0 := by
      simp only [hR]
      refine ContinuousAt.div ?_ (hbc.mul (continuousAt_const.add hbc)) hden
      exact ((continuousAt_const.mul (hac.add hbc')).cexp)
    exact hcont.tendsto.mono_left nhdsWithin_le_nhds
  -- they agree for small `ε > 0`
  have hne : ∀ᶠ ε : ℝ in 𝓝[>] 0, a ≠ b + ε := by
    by_cases hab : a = b
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      intro h
      have : ((ε:ℝ):ℂ) = 0 := by linear_combination hab - h
      have : ε = 0 := by exact_mod_cast this
      exact (ne_of_gt (mem_Ioi.1 hε)) this
    · have hc' : Tendsto (fun ε : ℝ => b + (ε:ℂ)) (𝓝[>] 0) (𝓝 b) := by
        have := ((by fun_prop : Continuous fun ε : ℝ => b+(ε:ℂ)).tendsto 0).mono_left
          (nhdsWithin_le_nhds (s := Ioi 0))
        simpa using this
      filter_upwards [hc'.eventually_ne (Ne.symm hab)] with ε hε using Ne.symm hε
  have heq : (fun ε => ∫ t in Ioi (0:ℝ), F ε t) =ᶠ[𝓝[>] 0] R := by
    filter_upwards [self_mem_nhdsWithin, hne] with ε hε hab
    obtain ⟨h1, h2⟩ := hre1 ε hε
    exact erfInt_laplace_plus_of_re_pos ha h1 h2 hab
  have := tendsto_nhds_unique (hI.congr' heq) hRc
  simpa [hF, hR] using this

/-- A crude global bound: `‖erf w‖ ≤ (2/√π) ‖w‖ e^{max(0, -Re w²)}`. -/
theorem erfInt_norm_erf_le (w : ℂ) :
    ‖erf w‖ ≤ 2/Real.sqrt π * Real.exp (max 0 (-(w^2).re)) * ‖w‖ := by
  have hs : Convex ℝ (segment ℝ (0:ℂ) w) := convex_segment _ _
  have h := hs.norm_image_sub_le_of_norm_hasDerivWithin_le (f := erf)
    (f' := fun z => 2/Real.sqrt π*exp (-z^2))
    (C := 2/Real.sqrt π * Real.exp (max 0 (-(w^2).re)))
    (fun z _ => (hasDerivAt_erf_complex z).hasDerivWithinAt) (fun z hz => ?_)
    (left_mem_segment ℝ 0 w) (right_mem_segment ℝ 0 w)
  · have he : erf 0 = 0 := by simp [erf]
    simpa [he] using h
  · rw [segment_eq_image'] at hz
    obtain ⟨τ, ⟨hτ0, hτ1⟩, rfl⟩ := hz
    simp only [zero_add, sub_zero]
    have hπ : 0 < Real.sqrt π := Real.sqrt_pos.2 Real.pi_pos
    rw [norm_mul, Complex.norm_exp, norm_div, Complex.norm_real, Real.norm_of_nonneg hπ.le]
    simp only [Complex.norm_ofNat]
    gcongr
    have : (-(τ • w)^2).re = -(τ^2 * (w^2).re) := by
      rw [real_smul, mul_pow, ← ofReal_pow, neg_re, re_ofReal_mul]
    rw [this]
    have h1 : τ^2 ≤ 1 := by nlinarith
    have h2 : 0 ≤ τ^2 := sq_nonneg τ
    rcases le_total 0 (w^2).re with h | h
    · have : 0 ≤ τ^2 * (w^2).re := mul_nonneg h2 h
      linarith [le_max_left 0 (-(w^2).re)]
    · have : (w^2).re ≤ τ^2 * (w^2).re := by nlinarith
      linarith [le_max_right 0 (-(w^2).re)]

/-- Bound for the integrand of the companion of DLMF 7.14.4: for `Re a > 0`, `Re c > 0`,
`‖c‖ ≤ M`, `t > 0`. -/
theorem erfInt_norm_erfc_minus_le {a c : ℂ} (ha : 0 < a.re) (hc : 0 < c.re) {M : ℝ}
    (hM : ‖c‖ ≤ M) {t : ℝ} (ht : 0 < t) :
    ‖erfc (-(a*t)^(1/2 : ℂ) + (c/t)^(1/2 : ℂ))‖ ≤ 1 + 2/Real.sqrt π *
      Real.exp (2*Real.sqrt (‖a‖*M)) * (Real.sqrt ‖a‖ * Real.sqrt t + Real.sqrt M / Real.sqrt t) := by
  have hat : 0 < (a*(t:ℂ)).re := by rw [re_mul_ofReal]; positivity
  have hct : 0 < (c/(t:ℂ)).re := by rw [div_ofReal_re]; positivity
  have hat0 : a*(t:ℂ) ≠ 0 := fun h => by rw [h] at hat; simp at hat
  have hct0 : c/(t:ℂ) ≠ 0 := fun h => by rw [h] at hct; simp at hct
  set u := (a*t)^(1/2 : ℂ)
  set v := (c/t)^(1/2 : ℂ)
  have hu2 : u^2 = a*t := cpow_half_sq hat0
  have hv2 : v^2 = c/t := cpow_half_sq hct0
  have hM0 : 0 ≤ M := (norm_nonneg _).trans hM
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have hnu : ‖u‖ = Real.sqrt ‖a‖ * Real.sqrt t := by
    have : ‖u‖^2 = ‖a‖ * t := by
      rw [← norm_pow, hu2, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.le]
    rw [← Real.sqrt_mul (norm_nonneg _), ← this, Real.sqrt_sq (norm_nonneg _)]
  have hnv : ‖v‖ ≤ Real.sqrt M / Real.sqrt t := by
    have : ‖v‖^2 = ‖c‖ / t := by
      rw [← norm_pow, hv2, norm_div, Complex.norm_real, Real.norm_of_nonneg ht.le]
    rw [← Real.sqrt_div' _ ht.le, ← Real.sqrt_sq (norm_nonneg v), this]
    exact Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hM ht.le)
  have hw : ‖-u + v‖ ≤ Real.sqrt ‖a‖ * Real.sqrt t + Real.sqrt M / Real.sqrt t := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_neg, hnu]; linarith
  have hre : max 0 (-((-u+v)^2).re) ≤ 2*Real.sqrt (‖a‖*M) := by
    have hsq : (-u+v)^2 = u^2 - 2*(u*v) + v^2 := by ring
    have h1 : -((-u+v)^2).re ≤ 2*‖u*v‖ := by
      rw [hsq, hu2, hv2]
      simp only [sub_re, add_re, re_mul_ofReal, div_ofReal_re]
      have : (2*(u*v)).re = 2*(u*v).re := by simp
      rw [this]
      have : 0 < a.re * t := by positivity
      have : 0 < c.re / t := by positivity
      have := re_le_norm (u*v)
      linarith
    have h2 : ‖u*v‖ ≤ Real.sqrt (‖a‖*M) := by
      rw [norm_mul, hnu]
      calc Real.sqrt ‖a‖ * Real.sqrt t * ‖v‖ ≤ Real.sqrt ‖a‖ * Real.sqrt t *
            (Real.sqrt M / Real.sqrt t) := by gcongr
        _ = Real.sqrt (‖a‖*M) := by
            rw [Real.sqrt_mul (norm_nonneg _)]; field_simp
    refine max_le (by positivity) (by linarith)
  have herf := erfInt_norm_erf_le (-u+v)
  have : erfc (-u+v) = 1 - erf (-u+v) := rfl
  rw [this]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_one]
  gcongr
  calc ‖erf (-u+v)‖ ≤ 2/Real.sqrt π * Real.exp (max 0 (-((-u+v)^2).re)) * ‖-u+v‖ := herf
    _ ≤ 2/Real.sqrt π * Real.exp (2*Real.sqrt (‖a‖*M)) *
        (Real.sqrt ‖a‖ * Real.sqrt t + Real.sqrt M / Real.sqrt t) := by gcongr

/-- Integrability of `(A + B√t + C/√t) e^{-λt}` on `(0, ∞)`. -/
theorem erfInt_integrableOn_majorant {l : ℝ} (hl : 0 < l) (A B C : ℝ) :
    IntegrableOn (fun t : ℝ => (A + B*Real.sqrt t + C/Real.sqrt t) * Real.exp (-(l*t))) (Ioi 0) := by
  have h0 : IntegrableOn (fun t : ℝ => t^(0:ℝ) * Real.exp (-l * t^(1:ℝ))) (Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_rpow (by norm_num) one_pos hl
  have h1 : IntegrableOn (fun t : ℝ => t^(1/2:ℝ) * Real.exp (-l * t^(1:ℝ))) (Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_rpow (by norm_num) one_pos hl
  have h2 : IntegrableOn (fun t : ℝ => t^(-1/2:ℝ) * Real.exp (-l * t^(1:ℝ))) (Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_rpow (by norm_num) one_pos hl
  have := ((h0.const_mul A).add (h1.const_mul B)).add (h2.const_mul C)
  refine IntegrableOn.congr_fun this (fun t ht => ?_) measurableSet_Ioi
  have ht : (0:ℝ) < t := ht
  simp only [Real.rpow_zero, Real.rpow_one, one_mul, Pi.add_apply]
  rw [Real.sqrt_eq_rpow, show (-1/2:ℝ) = -(1/2) by norm_num, Real.rpow_neg ht.le]
  ring_nf

/-- **Companion of DLMF 7.14.4 for `Re c > 0`.** -/
theorem erfInt_laplace_minus_of_re_pos {a b c : ℂ} (ha : 0 < a.re) (hba : 0 < (b-a).re)
    (hc : 0 < c.re) :
    (∫ t : ℝ in Ioi 0, exp ((a-b)*t)*erfc (-(a*t)^(1/2 : ℂ)+(c/t)^(1/2 : ℂ))) =
      exp (2*((a*c)^(1/2 : ℂ)-(b*c)^(1/2 : ℂ)))/(b^(1/2 : ℂ)*(b^(1/2 : ℂ)-a^(1/2 : ℂ))) := by
  have hb : 0 < b.re := by have : (b-a).re = b.re - a.re := sub_re b a; linarith
  have ha0 : a ≠ 0 := fun h => by simp [h] at ha
  have hb0 : b ≠ 0 := fun h => by simp [h] at hb
  have hc0 : c ≠ 0 := fun h => by simp [h] at hc
  set α := -a^(1/2 : ℂ) with hα
  set β := b^(1/2 : ℂ) with hβ
  set γ := c^(1/2 : ℂ) with hγ
  have hβr : 0 < β.re := re_cpow_half_pos hb
  have hγr : 0 < γ.re := re_cpow_half_pos hc
  have hα2 : α^2 = a := by rw [hα, neg_sq]; exact cpow_half_sq ha0
  have hβ2 : β^2 = b := cpow_half_sq hb0
  have hγ2 : γ^2 = c := cpow_half_sq hc0
  have hp : a - b = α^2 - β^2 := by rw [hα2, hβ2]
  have hab : a ≠ b := fun h => by rw [h, sub_self] at hba; simp at hba
  have hp0 : a - b ≠ 0 := sub_ne_zero.2 hab
  have hαβ : α + β ≠ 0 := fun h => by
    have : β = a^(1/2 : ℂ) := by rw [hα] at h; linear_combination h
    apply hab; rw [← hβ2, this, cpow_half_sq ha0]
  have hform : ∀ t : ℝ, 0 < t → exp ((a-b)*t)*erfc (-(a*t)^(1/2 : ℂ)+(c/t)^(1/2 : ℂ)) =
      exp ((a-b)*t)*erfc (α*Real.sqrt t+γ/Real.sqrt t) := by
    intro t ht
    rw [erfInt_cpow_half_mul_ofReal ha ht, erfInt_cpow_half_div_ofReal hc ht, hα, neg_mul]
  set l := (b-a).re with hl
  set Cst := 2/Real.sqrt π * Real.exp (2*Real.sqrt (‖a‖*‖c‖)) with hCst
  have hbnd : ∀ t : ℝ, 0 < t → ‖exp ((a-b)*t)*erfc (-(a*t)^(1/2 : ℂ)+(c/t)^(1/2 : ℂ))‖ ≤
      (1 + Cst*Real.sqrt ‖a‖*Real.sqrt t + Cst*Real.sqrt ‖c‖/Real.sqrt t) * Real.exp (-(l*t)) := by
    intro t ht
    have h := erfInt_norm_erfc_minus_le ha hc le_rfl ht
    have hre : ((a-b)*(t:ℂ)).re = -(l*t) := by simp [hl, sub_re]; ring
    rw [norm_mul, Complex.norm_exp, hre, mul_comm]
    gcongr
    refine h.trans (le_of_eq ?_)
    simp only [hCst]; ring
  have hint0 : IntegrableOn (fun t : ℝ => exp ((a-b)*t)*erfc (-(a*t)^(1/2 : ℂ)+(c/t)^(1/2 : ℂ)))
      (Ioi 0) := by
    refine (erfInt_integrableOn_majorant hba _ _ _).mono' ?_ ((ae_restrict_iff' measurableSet_Ioi).2
      (Eventually.of_forall fun t ht => hbnd t ht))
    have := erfInt_continuousOn_plus (a-b) ha.le hc.le (-1)
    simp only [neg_one_mul] at this
    exact this.aestronglyMeasurable measurableSet_Ioi
  have hint : IntegrableOn (fun t : ℝ => exp ((a-b)*t)*erfc (α*Real.sqrt t+γ/Real.sqrt t))
      (Ioi 0) := hint0.congr_fun (fun t ht => hform t ht) measurableSet_Ioi
  have hlim : Tendsto (fun x : ℝ => exp ((a-b)*(x:ℂ)^2)*erfc (α*x+γ/x)) atTop (𝓝 0) := by
    have h2 : Tendsto (fun x : ℝ => erfc (α*x+γ/x)) atTop (𝓝 (2 - 0)) := by
      have ha2 : 0 < ((a^(1/2 : ℂ))^2).re := by rw [cpow_half_sq ha0]; exact ha
      have := (erfInt_tendsto_erfc_atTop (re_cpow_half_pos ha) ha2 (-γ)).const_sub 2
      refine this.congr fun x => ?_
      rw [← erfc_negative]; congr 1; rw [hα]; ring
    have h1 : Tendsto (fun x : ℝ => exp ((a-b)*(x:ℂ)^2)) atTop (𝓝 0) := by
      refine tendsto_zero_iff_norm_tendsto_zero.2 ?_
      have : Tendsto (fun x : ℝ => -(l*x^2)) atTop atBot :=
        tendsto_neg_atTop_atBot.comp ((tendsto_pow_atTop two_ne_zero).const_mul_atTop hba)
      refine (Real.tendsto_exp_atBot.comp this).congr fun x => ?_
      have hre : ((a-b)*(x:ℂ)^2).re = -(l*x^2) := by
        rw [← ofReal_pow, re_mul_ofReal, hl]; simp [sub_re]; ring
      simp only [Function.comp_apply]; rw [Complex.norm_exp, hre]
    simpa using h1.mul h2
  have hcore := erfInt_laplace_core hp hp0 hβr (by rw [hβ2]; exact hb) hγr (by rw [hγ2]; exact hc)
    hαβ hint hlim
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t ht => hform t ht), hcore,
    erfInt_cpow_half_mul ha hc, erfInt_cpow_half_mul hb hc]
  simp only [hα, hβ, hγ]
  congr 1
  · congr 1; ring
  · ring

/-- **Companion of DLMF 7.14.4** in full (`Re c ≥ 0`), by continuity in `c ↦ c + ε`. -/
theorem erfInt_laplace_minus {a b c : ℂ} (ha : 0 < a.re) (hba : 0 < (b-a).re) (hc : 0 ≤ c.re) :
    (∫ t : ℝ in Ioi 0, exp ((a-b)*t)*erfc (-(a*t)^(1/2 : ℂ)+(c/t)^(1/2 : ℂ))) =
      exp (2*((a*c)^(1/2 : ℂ)-(b*c)^(1/2 : ℂ)))/(b^(1/2 : ℂ)*(b^(1/2 : ℂ)-a^(1/2 : ℂ))) := by
  have hb : 0 < b.re := by have : (b-a).re = b.re - a.re := sub_re b a; linarith
  set F : ℝ → ℝ → ℂ := fun ε t => exp ((a-b)*t)*erfc (-(a*t)^(1/2 : ℂ)+((c+ε)/t)^(1/2 : ℂ))
    with hF
  set R : ℝ → ℂ := fun ε => exp (2*((a*(c+ε))^(1/2 : ℂ)-(b*(c+ε))^(1/2 : ℂ)))/
    (b^(1/2 : ℂ)*(b^(1/2 : ℂ)-a^(1/2 : ℂ))) with hR
  have hre1 : ∀ ε : ℝ, 0 < ε → 0 < (c+ε).re := fun ε hε => by
    simp only [add_re, ofReal_re]; linarith
  set l := (b-a).re with hl
  set M := ‖c‖ + 1 with hM
  set Cst := 2/Real.sqrt π * Real.exp (2*Real.sqrt (‖a‖*M)) with hCst
  have hI : Tendsto (fun ε => ∫ t in Ioi (0:ℝ), F ε t) (𝓝[>] 0) (𝓝 (∫ t in Ioi (0:ℝ), F 0 t)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun t => (1 + Cst*Real.sqrt ‖a‖*Real.sqrt t + Cst*Real.sqrt M/Real.sqrt t) *
        Real.exp (-(l*t))) ?_ ?_ (erfInt_integrableOn_majorant hba _ _ _) ?_
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      have := erfInt_continuousOn_plus (a-b) (a := a) (c := c+ε) ha.le (hre1 ε hε).le (-1)
      simp only [neg_one_mul] at this
      exact this.aestronglyMeasurable measurableSet_Ioi
    · filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with ε hε
      refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
      have ht : (0:ℝ) < t := ht
      have hcM : ‖c+ε‖ ≤ M := by
        refine (norm_add_le _ _).trans ?_
        rw [Complex.norm_real, Real.norm_of_nonneg hε.1.le]; linarith [hε.2]
      have h := erfInt_norm_erfc_minus_le ha (hre1 ε hε.1) hcM ht
      have hre : ((a-b)*(t:ℂ)).re = -(l*t) := by simp [hl, sub_re]; ring
      simp only [hF]
      rw [norm_mul, Complex.norm_exp, hre, mul_comm]
      gcongr
      refine h.trans (le_of_eq ?_)
      simp only [hCst]; ring
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
      have ht : (0:ℝ) < t := ht
      have hE : Continuous erfc := by
        unfold erfc; have := differentiable_erf_complex.continuous; fun_prop
      have h2 := ((hE.tendsto _).comp ((erfInt_tendsto_cpow_half_shift hc ht).const_add
        (-(a*t)^(1/2 : ℂ))))
      have := h2.const_mul (exp ((a-b)*t))
      simpa [hF] using this
  have hRc : Tendsto R (𝓝[>] 0) (𝓝 (R 0)) := by
    have hac : ContinuousAt (fun ε : ℝ => (a*(c+ε))^(1/2 : ℂ)) 0 :=
      ContinuousAt.comp (g := fun z : ℂ => z^(1/2:ℂ)) (f := fun ε : ℝ => a*(c+(ε:ℂ)))
        (erfInt_continuousAt_cpow_half (by simpa using erfInt_re_mul_nonneg_or ha hc))
        (by fun_prop)
    have hbc : ContinuousAt (fun ε : ℝ => (b*(c+ε))^(1/2 : ℂ)) 0 :=
      ContinuousAt.comp (g := fun z : ℂ => z^(1/2:ℂ)) (f := fun ε : ℝ => b*(c+(ε:ℂ)))
        (erfInt_continuousAt_cpow_half (by simpa using erfInt_re_mul_nonneg_or hb hc))
        (by fun_prop)
    have hcont : ContinuousAt R 0 := by
      simp only [hR]
      exact ((continuousAt_const.mul (hac.sub hbc)).cexp).div_const _
    exact hcont.tendsto.mono_left nhdsWithin_le_nhds
  have heq : (fun ε => ∫ t in Ioi (0:ℝ), F ε t) =ᶠ[𝓝[>] 0] R := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact erfInt_laplace_minus_of_re_pos ha hba (hre1 ε hε)
  have := tendsto_nhds_unique (hI.congr' heq) hRc
  simpa [hF, hR] using this

/-- Identity under the stated parameter and domain assumptions: `(∫ t : ℝ in Ioi 0, exp
((a-b)*t)*erfc ((a*t)^(1/2 : ℂ)+(c/t)^(1/2 : ℂ)))=exp (-2*((a*c)^(1/2 : ℂ)+(b*c)^(1/2 :
ℂ)))/(b^(1/2 : ℂ)*(a^(1/2 : ℂ)+b^(1/2 : ℂ)))`. -/
@[dlmf 7.14.E4]
theorem erfc_sqrt_reciprocal_laplace {a b c : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) (hc : 0 ≤ c.re) :
    (∫ t : ℝ in Ioi 0, exp ((a-b)*t)*erfc ((a*t)^(1/2 : ℂ)+(c/t)^(1/2 : ℂ)))=exp (-2*((a*c)^(1/2 : ℂ)+(b*c)^(1/2 : ℂ)))/(b^(1/2 : ℂ)*(a^(1/2 : ℂ)+b^(1/2 : ℂ))) :=
  erfInt_laplace_plus ha hb hc

/-- Unnumbered transform following DLMF 7.14.4. -/
theorem erfc_sqrt_reciprocal_laplace_negative {a b c : ℂ} (ha : 0 < a.re) (hb : 0 < (b-a).re) (hc : 0 ≤ c.re) :
    (∫ t : ℝ in Ioi 0, exp ((a-b)*t)*erfc (-(a*t)^(1/2 : ℂ)+(c/t)^(1/2 : ℂ)))=exp (2*((a*c)^(1/2 : ℂ)-(b*c)^(1/2 : ℂ)))/(b^(1/2 : ℂ)*(b^(1/2 : ℂ)-a^(1/2 : ℂ))) :=
  erfInt_laplace_minus ha hb hc

/-- A continuous function with a limit at `+∞` is bounded on `[0, ∞)`. -/
theorem exists_bound_Ici_of_tendsto {g : ℝ → ℂ} {L : ℂ} (hg : Continuous g)
    (hL : Tendsto g atTop (𝓝 L)) : ∃ B : ℝ, ∀ t : ℝ, 0 ≤ t → ‖g t‖ ≤ B := by
  obtain ⟨T, hT⟩ := (Metric.tendsto_atTop.mp hL) 1 one_pos
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0:ℝ)) (b := max T 0)).exists_bound_of_continuousOn
    hg.continuousOn
  refine ⟨max C (‖L‖+1), fun t ht => ?_⟩
  by_cases h : t ≤ max T 0
  · exact (hC t ⟨ht, h⟩).trans (le_max_left _ _)
  · have h1 := hT t ((le_max_left T 0).trans (not_le.mp h).le)
    rw [dist_eq_norm] at h1
    have : ‖g t‖ ≤ ‖g t - L‖ + ‖L‖ := by
      simpa using norm_add_le (g t - L) L
    exact (by linarith : ‖g t‖ ≤ ‖L‖+1).trans (le_max_right _ _)

/-- Laplace transform of a bounded function `u` with `u 0 = 0`, computed from an antiderivative
`G` of `e^{-at} u'(t)/a`, by integration by parts. -/
theorem integral_exp_mul_eq_of_antideriv {a : ℂ} (ha : 0 < a.re) {u u' G : ℝ → ℂ} {B : ℝ}
    {L : ℂ} (hu : Continuous u) (hu0 : u 0 = 0) (hB : ∀ t : ℝ, 0 ≤ t → ‖u t‖ ≤ B)
    (hud : ∀ t : ℝ, 0 < t → HasDerivAt u (u' t) t) (hG : ContinuousWithinAt G (Ici 0) 0)
    (hG0 : G 0 = 0) (hGd : ∀ t : ℝ, 0 < t → HasDerivAt G (exp (-a*t)*u' t/a) t)
    (hGl : Tendsto G atTop (𝓝 L)) :
    (∫ t : ℝ in Ioi 0, exp (-a*t)*u t) = L := by
  have ha0 : a ≠ 0 := fun h => by simp [h] at ha
  have hn : 0 < ‖a‖ := norm_pos_iff.mpr ha0
  set F : ℝ → ℂ := fun t => -(exp (-a*t)/a)*u t + G t with hF
  have hexp (t : ℝ) : HasDerivAt (fun t : ℝ => exp (-a*(t:ℂ))) (exp (-a*t)*(-a)) t := by
    have := ((hasDerivAt_id (t:ℂ)).const_mul (-a)).cexp
    simpa using this.comp_ofReal
  have hd : ∀ t : ℝ, 0 < t → HasDerivAt F (exp (-a*t)*u t) t := by
    intro t ht
    have h := (((hexp t).div_const a).mul (hud t ht)).neg.add (hGd t ht)
    convert h using 1
    · funext s; simp [hF, div_eq_mul_inv]
    · field_simp
      ring
  have hre (t : ℝ) : (-a*(t:ℂ)).re = -a.re*t := by simp
  have hcont : ContinuousWithinAt F (Ici 0) 0 := by
    refine ContinuousWithinAt.add ?_ hG
    exact ((by fun_prop : Continuous fun t : ℝ => exp (-a*t)/a).neg.mul hu).continuousWithinAt
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 le_rfl)
  have hdecay : Tendsto (fun t : ℝ => Real.exp (-a.re*t)) atTop (𝓝 0) := by
    have : Tendsto (fun t : ℝ => -a.re*t) atTop atBot :=
      tendsto_id.const_mul_atTop_of_neg (by linarith)
    exact Real.tendsto_exp_atBot.comp this
  have hlim : Tendsto F atTop (𝓝 (0 + L)) := by
    refine Tendsto.add ?_ hGl
    have hev : ∀ᶠ t : ℝ in atTop, ‖-(exp (-a*t)/a)*u t‖ ≤ B/‖a‖*Real.exp (-a.re*t) := by
      filter_upwards [eventually_ge_atTop 0] with t ht
      rw [norm_mul, norm_neg, norm_div, Complex.norm_exp, hre]
      calc Real.exp (-a.re*t)/‖a‖*‖u t‖ ≤ Real.exp (-a.re*t)/‖a‖*B := by
            gcongr; exact hB t ht
        _ = _ := by ring
    refine squeeze_zero_norm' hev ?_
    simpa using hdecay.const_mul (B/‖a‖)
  have hint : IntegrableOn (fun t : ℝ => exp (-a*t)*u t) (Ioi 0) := by
    have hg : IntegrableOn (fun t : ℝ => B*Real.exp (-a.re*t)) (Ioi 0) :=
      ((exp_neg_integrableOn_Ioi 0 ha).const_mul B :)
    refine hg.mono' ((by fun_prop : Continuous fun t : ℝ => exp (-a*t)).mul hu).aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    rw [norm_mul, Complex.norm_exp, hre, mul_comm]
    exact mul_le_mul_of_nonneg_right (hB t (le_of_lt ht)) (Real.exp_pos _).le
  rw [integral_Ioi_of_hasDerivAt_of_tendsto hcont (fun t ht => hd t ht) hint hlim]
  simp [hF, hu0, hG0]

/-- Derivative of `w⁻¹ erf(w √t)`: it equals `e^{-w² t}/√(π t)`. -/
theorem hasDerivAt_recip_mul_erf_sqrt {w : ℂ} (hw : w ≠ 0) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun t : ℝ => w⁻¹*erf (w*(Real.sqrt t : ℂ)))
      (exp (-(w^2*t))/((Real.sqrt π:ℂ)*(Real.sqrt t:ℂ))) t := by
  have hs : HasDerivAt (fun t : ℝ => ((Real.sqrt t:ℝ):ℂ)) ((1/(2*Real.sqrt t):ℝ):ℂ) t :=
    (Real.hasDerivAt_sqrt ht.ne').ofReal_comp
  have h := ((hasDerivAt_erf_complex _).comp t (hs.const_mul w)).const_mul w⁻¹
  refine h.congr_deriv ?_
  have hst : (Real.sqrt t:ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr ht).ne'
  have hsp : (Real.sqrt π:ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hsq : ((Real.sqrt t:ℂ))^2 = t := by exact_mod_cast Real.sq_sqrt ht.le
  rw [mul_pow, hsq]
  push_cast
  field_simp

/-- `w⁻¹ erf(w √t) → w⁻¹` as `t → ∞` when `Re w > 0` and `Re w² > 0`. -/
theorem tendsto_recip_mul_erf_sqrt {w : ℂ} (hw : 0 < w.re) (hw2 : 0 < (w^2).re) :
    Tendsto (fun t : ℝ => w⁻¹*erf (w*(Real.sqrt t : ℂ))) atTop (𝓝 (w⁻¹*1)) := by
  refine Tendsto.const_mul _ ?_
  have h0 : Tendsto (fun t : ℝ => erfc (w*(Real.sqrt t : ℂ))) atTop (𝓝 0) := by
    refine tendsto_erfc_zero_of_re_sq ?_ ?_
    · filter_upwards [eventually_gt_atTop 0] with t ht
      rw [re_mul_ofReal]; exact mul_pos hw (Real.sqrt_pos.mpr ht)
    · have h0 : Tendsto (fun t : ℝ => (w^2).re*t) atTop atTop := tendsto_id.const_mul_atTop' hw2
      refine h0.congr' ?_
      filter_upwards [eventually_ge_atTop 0] with t ht
      rw [mul_pow, ← ofReal_pow, Real.sq_sqrt ht, re_mul_ofReal]
  have := h0.const_sub 1
  simp only [sub_zero] at this
  refine this.congr fun t => ?_
  simp [erfc]

/-- `π √(2t/π) = √2 √π √t`. -/
theorem pi_mul_sqrt_two_mul_div_pi {t : ℝ} (ht : 0 ≤ t) :
    π*Real.sqrt (2*t/π) = Real.sqrt 2*Real.sqrt π*Real.sqrt t := by
  have hp := Real.pi_pos
  refine (pow_left_inj₀ (by positivity) (by positivity) two_ne_zero).mp ?_
  rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity),
    Real.sq_sqrt hp.le, Real.sq_sqrt ht]
  field_simp

/-- Derivative of `t ↦ √(2t/π)` (as a complex-valued function). -/
theorem hasDerivAt_sqrt_two_mul_div_pi {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun t : ℝ => ((Real.sqrt (2*t/π):ℝ):ℂ)) (((1/(π*Real.sqrt (2*t/π))):ℝ):ℂ) t := by
  have hp := Real.pi_pos
  have hne : 2*t/π ≠ 0 := by positivity
  have h := ((Real.hasDerivAt_sqrt hne).comp t (((hasDerivAt_id t).const_mul 2).div_const π)).ofReal_comp
  refine h.congr_deriv ?_
  congr 1
  have : 0 < Real.sqrt (2*t/π) := Real.sqrt_pos.mpr (by positivity)
  field_simp

/-- `(√(2t/π))² π/2 = t`. -/
theorem pi_mul_sqrt_two_mul_div_pi_sq {t : ℝ} (ht : 0 ≤ t) :
    (π:ℂ)*((Real.sqrt (2*t/π):ℝ):ℂ)^2/2 = t := by
  rw [← ofReal_pow, Real.sq_sqrt (by have := Real.pi_pos; positivity)]
  have : (π:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  push_cast
  field_simp

/-- If `Re u, Re u², Re v, Re v² > 0` then `Re (u v) > 0`. -/
theorem re_mul_pos_of_re_sq {u v : ℂ} (hu : 0 < u.re) (hu2 : 0 < (u^2).re) (hv : 0 < v.re)
    (hv2 : 0 < (v^2).re) : 0 < (u*v).re := by
  have e1 : (u^2).re = u.re^2 - u.im^2 := by simp [sq]
  have e2 : (v^2).re = v.re^2 - v.im^2 := by simp [sq]
  have hlt : (u.im*v.im)^2 < (u.re*v.re)^2 := by
    rw [mul_pow, mul_pow]
    have h3 : u.im^2*v.im^2 ≤ u.re^2*v.im^2 := mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
    have h4 : u.re^2*v.im^2 < u.re^2*v.re^2 := mul_lt_mul_of_pos_left (by linarith) (by positivity)
    linarith
  have := abs_lt_of_sq_lt_sq hlt (by positivity)
  rw [mul_re]
  linarith [le_abs_self (u.im*v.im)]

/-- The Fresnel functions along `√(2t/π)` are bounded on `[0, ∞)`. -/
theorem exists_bound_fresnel_sqrt {f : ℂ → ℂ} {g : ℝ → ℝ} (hf : Differentiable ℂ f)
    (hfg : ∀ x : ℝ, f x = g x) (hg : Tendsto g atTop (𝓝 (1/2))) :
    ∃ B : ℝ, ∀ t : ℝ, 0 ≤ t → ‖f ((Real.sqrt (2*t/π):ℝ):ℂ)‖ ≤ B := by
  refine exists_bound_Ici_of_tendsto (L := ((1/2:ℝ):ℂ)) (hf.continuous.comp (by fun_prop)) ?_
  have hs : Tendsto (fun t : ℝ => Real.sqrt (2*t/π)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp ((tendsto_id.const_mul_atTop' two_pos).atTop_div_const Real.pi_pos)
  have := ((continuous_ofReal.tendsto _).comp hg).comp hs
  refine this.congr fun t => ?_
  simp [hfg]

/-- Integration by parts for a Laplace transform: if `u` is bounded on `[0, ∞)` with `u 0 = 0`
and continuous derivative `u'`, then `∫₀^∞ e^{-at} u = a⁻¹ ∫₀^∞ e^{-at} u'`. -/
theorem integral_exp_mul_eq_of_deriv {a : ℂ} (ha : 0 < a.re) {u u' : ℝ → ℂ} {B : ℝ}
    (hu : Continuous u) (hu0 : u 0 = 0) (hB : ∀ t : ℝ, 0 ≤ t → ‖u t‖ ≤ B)
    (hud : ∀ t : ℝ, 0 < t → HasDerivAt u (u' t) t) (hu' : Continuous u')
    (hi : IntegrableOn (fun t : ℝ => exp (-a*t)*u' t) (Ioi 0)) :
    (∫ t : ℝ in Ioi 0, exp (-a*t)*u t) = (∫ t : ℝ in Ioi 0, exp (-a*t)*u' t)/a := by
  have hc : Continuous fun t : ℝ => exp (-a*t)*u' t := by fun_prop
  refine integral_exp_mul_eq_of_antideriv ha hu hu0 hB hud
    (G := fun t => (∫ s in (0:ℝ)..t, exp (-a*s)*u' s)/a) ?_ (by simp) ?_ ?_
  · exact (continuous_iff_continuousAt.mpr fun t =>
      ((hc.integral_hasStrictDerivAt 0 t).hasDerivAt.div_const a).continuousAt).continuousWithinAt
  · exact fun t _ => (hc.integral_hasStrictDerivAt 0 t).hasDerivAt.div_const a
  · exact (intervalIntegral_tendsto_integral_Ioi 0 hi tendsto_id).div_const a

/-- Laplace transform of `cos(πt²/2)`. -/
theorem laplace_cos_pi_sq {a : ℂ} (ha : 0 < a.re) :
    (∫ t : ℝ in Ioi 0, exp (-a*t)*cos (π*(t:ℂ)^2/2)) = fresnelAuxFComplex (a/π) := by
  set c : ℝ := Real.sqrt (π/2)
  have hc : 0 < c := Real.sqrt_pos.mpr (by positivity)
  have hc0 : (c:ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hc2 : (c:ℂ)^2 = π/2 := by
    have := Real.sq_sqrt (by positivity : (0:ℝ) ≤ π/2); exact_mod_cast this
  have hre : 0 < (a/c).re := by rw [div_ofReal_re]; exact div_pos ha hc
  have h := integral_comp_mul_left_Ioi (fun x : ℝ => exp (-(a/c)*x)*cos ((x:ℂ)^2)) 0 hc
  rw [mul_zero, fresnelAuxFComplex_laplace_square hre] at h
  have e : (fun x : ℝ => exp (-(a/c)*((c*x:ℝ):ℂ))*cos (((c*x:ℝ):ℂ)^2)) =
      fun t : ℝ => exp (-a*t)*cos (π*(t:ℂ)^2/2) := by
    funext t; push_cast
    rw [mul_pow, hc2]; congr 2
    · field_simp
    · ring
  simp only [e] at h
  rw [h, real_smul]
  have h2 : (a/(c:ℂ))/((Real.sqrt (2*π):ℝ):ℂ) = a/π := by
    have : (c:ℂ)*((Real.sqrt (2*π):ℝ):ℂ) = π := by
      simp only [c]; rw [← ofReal_mul, ← Real.sqrt_mul (by positivity)]
      rw [show π/2*(2*π) = π^2 by ring, Real.sqrt_sq Real.pi_pos.le]
    rw [div_div, this]
  rw [h2]; push_cast; field_simp; rfl

/-- Laplace transform of `sin(πt²/2)`. -/
theorem laplace_sin_pi_sq {a : ℂ} (ha : 0 < a.re) :
    (∫ t : ℝ in Ioi 0, exp (-a*t)*sin (π*(t:ℂ)^2/2)) = fresnelAuxGComplex (a/π) := by
  set c : ℝ := Real.sqrt (π/2)
  have hc : 0 < c := Real.sqrt_pos.mpr (by positivity)
  have hc0 : (c:ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hc2 : (c:ℂ)^2 = π/2 := by
    have := Real.sq_sqrt (by positivity : (0:ℝ) ≤ π/2); exact_mod_cast this
  have hre : 0 < (a/c).re := by rw [div_ofReal_re]; exact div_pos ha hc
  have h := integral_comp_mul_left_Ioi (fun x : ℝ => exp (-(a/c)*x)*sin ((x:ℂ)^2)) 0 hc
  rw [mul_zero, fresnelAuxGComplex_laplace_square hre] at h
  have e : (fun x : ℝ => exp (-(a/c)*((c*x:ℝ):ℂ))*sin (((c*x:ℝ):ℂ)^2)) =
      fun t : ℝ => exp (-a*t)*sin (π*(t:ℂ)^2/2) := by
    funext t; push_cast
    rw [mul_pow, hc2]; congr 2
    · field_simp
    · ring
  simp only [e] at h
  rw [h, real_smul]
  have h2 : (a/(c:ℂ))/((Real.sqrt (2*π):ℝ):ℂ) = a/π := by
    have : (c:ℂ)*((Real.sqrt (2*π):ℝ):ℂ) = π := by
      simp only [c]; rw [← ofReal_mul, ← Real.sqrt_mul (by positivity)]
      rw [show π/2*(2*π) = π^2 by ring, Real.sqrt_sq Real.pi_pos.le]
    rw [div_div, this]
  rw [h2]; push_cast; field_simp; rfl

/-- Identity under the stated parameter and domain assumptions: `(∫ t : ℝ in Ioi 0, exp
(-a*t)*fresnelCosInt t)=fresnelAuxFComplex (a/π)/a`. -/
@[dlmf 7.14.E5]
theorem fresnelCosInt_laplace {a : ℂ} (ha : 0 < a.re) :
    (∫ t : ℝ in Ioi 0, exp (-a*t)*fresnelCosInt t)=fresnelAuxFComplex (a/π)/a := by
  obtain ⟨B, hB⟩ := exists_bound_Ici_of_tendsto (L := ((1/2:ℝ):ℂ))
    (g := fun t : ℝ => fresnelCosInt (t:ℂ)) (fresnelCosInt_entire.continuous.comp continuous_ofReal)
    (((continuous_ofReal.tendsto _).comp Real.tendsto_fresnelCosInt_atTop).congr
      fun t => (fresnelCosInt_ofReal t).symm)
  have hi : IntegrableOn (fun t : ℝ => exp (-a*t)*cos (π*(t:ℂ)^2/2)) (Ioi 0) := by
    refine (exp_neg_integrableOn_Ioi 0 ha).mono' (by fun_prop : Continuous fun t : ℝ =>
      exp (-a*t)*cos (π*(t:ℂ)^2/2)).aestronglyMeasurable (Eventually.of_forall fun t => ?_)
    rw [norm_mul, Complex.norm_exp]
    have : (-a*(t:ℂ)).re = -a.re*t := by simp
    rw [this]
    have h1 : ‖cos (π*(t:ℂ)^2/2)‖ ≤ 1 := by
      rw [show (π:ℂ)*(t:ℂ)^2/2 = ((π*t^2/2:ℝ):ℂ) by push_cast; ring, ← ofReal_cos, norm_real,
        Real.norm_eq_abs]
      exact Real.abs_cos_le_one _
    simpa using mul_le_mul_of_nonneg_left h1 (Real.exp_pos (-a.re*t)).le
  rw [integral_exp_mul_eq_of_deriv ha (u := fun t : ℝ => fresnelCosInt (t:ℂ)) (fresnelCosInt_entire.continuous.comp continuous_ofReal)
    (by simpa using (fresnelCosInt_ofReal 0).trans (by simp [Real.fresnelCosInt])) hB
    (fun t _ => (hasDerivAt_fresnelCosInt_complex t).comp_ofReal) (by fun_prop) hi,
    laplace_cos_pi_sq ha]

/-- Identity under the stated parameter and domain assumptions: `(∫ t : ℝ in Ioi 0, exp
(-a*t)*fresnelCosInt (Real.sqrt (2*t/π)))=(((a^2+1)^(1/2 : ℂ))+a)^(1/2 : ℂ)/(2*a*(a^2+1)^(1/2
: ℂ))`. -/
@[dlmf 7.14.E7]
theorem fresnelCosInt_sqrt_laplace {a : ℂ} (ha : 0 < a.re) :
    (∫ t : ℝ in Ioi 0, exp (-a*t)*fresnelCosInt (Real.sqrt (2*t/π)))=(((a^2+1)^(1/2 : ℂ))+a)^(1/2 : ℂ)/(2*a*(a^2+1)^(1/2 : ℂ)) := by
  have ha0 : a ≠ 0 := fun h => by simp [h] at ha
  have hm : (0:ℝ) < (a-I).re := by simpa using ha
  have hp : (0:ℝ) < (a+I).re := by simpa using ha
  set u1 := (a-I)^(1/2 : ℂ); set v1 := (a+I)^(1/2 : ℂ)
  have hu1 : u1^2 = a-I := cpow_half_sq (fun h => by simp [h] at hm)
  have hv1 : v1^2 = a+I := cpow_half_sq (fun h => by simp [h] at hp)
  have hu1r : 0 < u1.re := re_cpow_half_pos hm
  have hv1r : 0 < v1.re := re_cpow_half_pos hp
  have hu10 : u1 ≠ 0 := fun h => by simp [h] at hu1r
  have hv10 : v1 ≠ 0 := fun h => by simp [h] at hv1r
  have hu1r2 : 0 < (u1^2).re := by rw [hu1]; exact hm
  have hv1r2 : 0 < (v1^2).re := by rw [hv1]; exact hp
  have hs2 : (Real.sqrt 2:ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr two_pos).ne'
  have hsp : (Real.sqrt π:ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hec : Continuous erf := differentiable_erf_complex.continuous
  obtain ⟨B, hB⟩ := exists_bound_fresnel_sqrt fresnelCosInt_entire fresnelCosInt_ofReal
    Real.tendsto_fresnelCosInt_atTop
  set k : ℂ := 1/(2*a*Real.sqrt 2)
  have key := integral_exp_mul_eq_of_antideriv (a := a) (B := B) ha
    (u := fun t : ℝ => fresnelCosInt ((Real.sqrt (2*t/π):ℝ):ℂ))
    (u' := fun t : ℝ => cos (t:ℂ)*(((1/(π*Real.sqrt (2*t/π))):ℝ):ℂ))
    (G := fun t : ℝ => k*(u1⁻¹*erf (u1*(Real.sqrt t:ℂ)) + v1⁻¹*erf (v1*(Real.sqrt t:ℂ))))
    (L := k*(u1⁻¹*1 + v1⁻¹*1))
    (fresnelCosInt_entire.continuous.comp (by fun_prop))
    (by have h0 := fresnelCosInt_ofReal 0; simp [Real.fresnelCosInt] at h0; simpa using h0) hB
    (fun t ht => by
      have h := (hasDerivAt_fresnelCosInt_complex _).comp t (hasDerivAt_sqrt_two_mul_div_pi ht)
      rw [pi_mul_sqrt_two_mul_div_pi_sq ht.le] at h
      exact h)
    ((by fun_prop : Continuous fun t : ℝ =>
      k*(u1⁻¹*erf (u1*(Real.sqrt t:ℂ)) + v1⁻¹*erf (v1*(Real.sqrt t:ℂ)))).continuousWithinAt)
    (by simp [erf_zero])
    (fun t ht => by
      have h := (((hasDerivAt_recip_mul_erf_sqrt hu10 ht).add
        (hasDerivAt_recip_mul_erf_sqrt hv10 ht)).const_mul k)
      refine h.congr_deriv ?_
      rw [hu1, hv1, pi_mul_sqrt_two_mul_div_pi ht.le]
      have hst : (Real.sqrt t:ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr ht).ne'
      have e1 : exp (-((a-I)*t)) = exp (-a*t)*exp (t*I) := by
        rw [← Complex.exp_add]; congr 1; ring
      have e2 : exp (-((a+I)*t)) = exp (-a*t)*exp (-t*I) := by
        rw [← Complex.exp_add]; congr 1; ring
      rw [e1, e2, Complex.cos]
      simp only [k]
      push_cast
      field_simp)
    (((tendsto_recip_mul_erf_sqrt hu1r hu1r2).add (tendsto_recip_mul_erf_sqrt hv1r hv1r2)).const_mul k)
  rw [key]
  have huv : (a^2+1)^(1/2 : ℂ) = u1*v1 := by
    rw [show a^2+1 = (u1*v1)^2 by rw [mul_pow, hu1, hv1]; ring_nf; rw [I_sq]; ring]
    exact sq_cpow_half (re_mul_pos_of_re_sq hu1r hu1r2 hv1r hv1r2)
  have hw : (u1*v1+a)^(1/2 : ℂ) = (u1+v1)/Real.sqrt 2 := by
    have h2 : ((Real.sqrt 2:ℂ))^2 = 2 := by exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
    rw [show u1*v1+a = ((u1+v1)/Real.sqrt 2)^2 by
      rw [div_pow, h2, add_sq, hu1, hv1]; ring]
    refine sq_cpow_half ?_
    rw [div_ofReal_re]
    exact div_pos (by simp; linarith) (Real.sqrt_pos.mpr two_pos)
  rw [huv, hw]
  simp only [k]
  field_simp
  ring

/-- Identity under the stated parameter and domain assumptions: `(∫ t : ℝ in Ioi 0, exp
(-a*t)*fresnelSinInt t)=fresnelAuxGComplex (a/π)/a`. -/
@[dlmf 7.14.E6]
theorem fresnelSinInt_laplace {a : ℂ} (ha : 0 < a.re) :
    (∫ t : ℝ in Ioi 0, exp (-a*t)*fresnelSinInt t)=fresnelAuxGComplex (a/π)/a := by
  obtain ⟨B, hB⟩ := exists_bound_Ici_of_tendsto (L := ((1/2:ℝ):ℂ))
    (g := fun t : ℝ => fresnelSinInt (t:ℂ)) (fresnelSinInt_entire.continuous.comp continuous_ofReal)
    (((continuous_ofReal.tendsto _).comp Real.tendsto_fresnelSinInt_atTop).congr
      fun t => (fresnelSinInt_ofReal t).symm)
  have hi : IntegrableOn (fun t : ℝ => exp (-a*t)*sin (π*(t:ℂ)^2/2)) (Ioi 0) := by
    refine (exp_neg_integrableOn_Ioi 0 ha).mono' (by fun_prop : Continuous fun t : ℝ =>
      exp (-a*t)*sin (π*(t:ℂ)^2/2)).aestronglyMeasurable (Eventually.of_forall fun t => ?_)
    rw [norm_mul, Complex.norm_exp]
    have : (-a*(t:ℂ)).re = -a.re*t := by simp
    rw [this]
    have h1 : ‖sin (π*(t:ℂ)^2/2)‖ ≤ 1 := by
      rw [show (π:ℂ)*(t:ℂ)^2/2 = ((π*t^2/2:ℝ):ℂ) by push_cast; ring, ← ofReal_sin, norm_real,
        Real.norm_eq_abs]
      exact Real.abs_sin_le_one _
    simpa using mul_le_mul_of_nonneg_left h1 (Real.exp_pos (-a.re*t)).le
  rw [integral_exp_mul_eq_of_deriv ha (u := fun t : ℝ => fresnelSinInt (t:ℂ)) (fresnelSinInt_entire.continuous.comp continuous_ofReal)
    (by simpa using (fresnelSinInt_ofReal 0).trans (by simp [Real.fresnelSinInt])) hB
    (fun t _ => (hasDerivAt_fresnelSinInt_complex t).comp_ofReal) (by fun_prop) hi,
    laplace_sin_pi_sq ha]

/-- Identity under the stated parameter and domain assumptions: `(∫ t : ℝ in Ioi 0, exp
(-a*t)*fresnelSinInt (Real.sqrt (2*t/π)))=(((a^2+1)^(1/2 : ℂ))-a)^(1/2 : ℂ)/(2*a*(a^2+1)^(1/2
: ℂ))`. -/
@[dlmf 7.14.E8]
theorem fresnelSinInt_sqrt_laplace {a : ℂ} (ha : 0 < a.re) :
    (∫ t : ℝ in Ioi 0, exp (-a*t)*fresnelSinInt (Real.sqrt (2*t/π)))=(((a^2+1)^(1/2 : ℂ))-a)^(1/2 : ℂ)/(2*a*(a^2+1)^(1/2 : ℂ)) := by
  have ha0 : a ≠ 0 := fun h => by simp [h] at ha
  have hm : (0:ℝ) < (a-I).re := by simpa using ha
  have hp : (0:ℝ) < (a+I).re := by simpa using ha
  set u1 := (a-I)^(1/2 : ℂ); set v1 := (a+I)^(1/2 : ℂ)
  have hu1 : u1^2 = a-I := cpow_half_sq (fun h => by simp [h] at hm)
  have hv1 : v1^2 = a+I := cpow_half_sq (fun h => by simp [h] at hp)
  have hu1r : 0 < u1.re := re_cpow_half_pos hm
  have hv1r : 0 < v1.re := re_cpow_half_pos hp
  have hu10 : u1 ≠ 0 := fun h => by simp [h] at hu1r
  have hv10 : v1 ≠ 0 := fun h => by simp [h] at hv1r
  have hu1r2 : 0 < (u1^2).re := by rw [hu1]; exact hm
  have hv1r2 : 0 < (v1^2).re := by rw [hv1]; exact hp
  have hs2 : (Real.sqrt 2:ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr two_pos).ne'
  have hsp : (Real.sqrt π:ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hec : Continuous erf := differentiable_erf_complex.continuous
  obtain ⟨B, hB⟩ := exists_bound_fresnel_sqrt fresnelSinInt_entire fresnelSinInt_ofReal
    Real.tendsto_fresnelSinInt_atTop
  set k : ℂ := 1/(2*a*Real.sqrt 2*I)
  have key := integral_exp_mul_eq_of_antideriv (a := a) (B := B) ha
    (u := fun t : ℝ => fresnelSinInt ((Real.sqrt (2*t/π):ℝ):ℂ))
    (u' := fun t : ℝ => sin (t:ℂ)*(((1/(π*Real.sqrt (2*t/π))):ℝ):ℂ))
    (G := fun t : ℝ => k*(u1⁻¹*erf (u1*(Real.sqrt t:ℂ)) - v1⁻¹*erf (v1*(Real.sqrt t:ℂ))))
    (L := k*(u1⁻¹*1 - v1⁻¹*1))
    (fresnelSinInt_entire.continuous.comp (by fun_prop))
    (by have h0 := fresnelSinInt_ofReal 0; simp [Real.fresnelSinInt] at h0; simpa using h0) hB
    (fun t ht => by
      have h := (hasDerivAt_fresnelSinInt_complex _).comp t (hasDerivAt_sqrt_two_mul_div_pi ht)
      rw [pi_mul_sqrt_two_mul_div_pi_sq ht.le] at h
      exact h)
    ((by fun_prop : Continuous fun t : ℝ =>
      k*(u1⁻¹*erf (u1*(Real.sqrt t:ℂ)) - v1⁻¹*erf (v1*(Real.sqrt t:ℂ)))).continuousWithinAt)
    (by simp [erf_zero])
    (fun t ht => by
      have h := (((hasDerivAt_recip_mul_erf_sqrt hu10 ht).sub
        (hasDerivAt_recip_mul_erf_sqrt hv10 ht)).const_mul k)
      refine h.congr_deriv ?_
      rw [hu1, hv1, pi_mul_sqrt_two_mul_div_pi ht.le]
      have hst : (Real.sqrt t:ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr ht).ne'
      have e1 : exp (-((a-I)*t)) = exp (-a*t)*exp (t*I) := by
        rw [← Complex.exp_add]; congr 1; ring
      have e2 : exp (-((a+I)*t)) = exp (-a*t)*exp (-t*I) := by
        rw [← Complex.exp_add]; congr 1; ring
      rw [e1, e2, Complex.sin]
      simp only [k]
      push_cast
      field_simp
      ring_nf
      rw [I_sq]
      ring)
    (((tendsto_recip_mul_erf_sqrt hu1r hu1r2).sub (tendsto_recip_mul_erf_sqrt hv1r hv1r2)).const_mul k)
  rw [key]
  have huv : (a^2+1)^(1/2 : ℂ) = u1*v1 := by
    rw [show a^2+1 = (u1*v1)^2 by rw [mul_pow, hu1, hv1]; ring_nf; rw [I_sq]; ring]
    exact sq_cpow_half (re_mul_pos_of_re_sq hu1r hu1r2 hv1r hv1r2)
  have hw : (u1*v1-a)^(1/2 : ℂ) = (v1-u1)/(Real.sqrt 2*I) := by
    have h2 : ((Real.sqrt 2:ℂ))^2 = 2 := by exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
    rw [show u1*v1-a = ((v1-u1)/(Real.sqrt 2*I))^2 by
      rw [div_pow, mul_pow, h2, I_sq, sub_sq, hu1, hv1]; field_simp; ring]
    refine sq_cpow_half ?_
    -- `Im (v1 - u1) > 0` since `(v1 - u1)(v1 + u1) = 2i` and `Re (v1 + u1) > 0`
    have hdw : (v1-u1)*(v1+u1) = 2*I := by
      rw [show (v1-u1)*(v1+u1) = v1^2-u1^2 by ring, hu1, hv1]; ring
    have hre := congrArg Complex.re hdw
    have him := congrArg Complex.im hdw
    simp only [mul_re, mul_im, sub_re, sub_im, add_re, add_im] at hre him
    norm_num at hre him
    have hwr : 0 < v1.re + u1.re := by linarith
    have hdim : 0 < v1.im - u1.im := by
      have hS : (v1.im-u1.im)*((v1.im+u1.im)^2+(v1.re+u1.re)^2) = 2*(v1.re+u1.re) := by
        linear_combination (-(v1.im+u1.im))*hre + (v1.re+u1.re)*him
      by_contra hc
      push Not at hc
      nlinarith [mul_nonpos_of_nonpos_of_nonneg hc
        (by positivity : 0 ≤ (v1.im+u1.im)^2+(v1.re+u1.re)^2)]
    have : ((v1-u1)/(Real.sqrt 2*I)) = (-I*(v1-u1))/Real.sqrt 2 := by
      field_simp; rw [I_sq]; ring
    rw [this, div_ofReal_re]
    refine div_pos ?_ (Real.sqrt_pos.mpr two_pos)
    simpa using hdim
  rw [huv, hw]
  simp only [k]
  field_simp

end DLMF.Confluent

end
