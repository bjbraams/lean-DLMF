/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.IncompleteGamma.SpecialValues
public import DLMF.IncompleteGamma.ExpIntegralAsymptotics
public import DLMF.IncompleteGamma.RealIntegrals
public import ToMathlib.Analysis.Integral.Laplace
public import DLMFMathlib.Analysis.Asymptotics.LaplaceSaddle
public import DLMFMathlib.Analysis.Calculus.DoubleZeroSqrt
public import DLMFMathlib.Analysis.Calculus.InverseSeries

/-!
# Large-argument incomplete Gamma expansions

Large-argument expansions, coefficient bounds and normalized incomplete-Gamma ratios.

Source references and common attribution are retained in
`DLMF.IncompleteGamma.Asymptotics`.
-/

@[expose] public noncomputable section

open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF

open scoped Real Topology Nat

namespace DLMF.Confluent

open DLMF.Statistical

/-- Falling-factorial incomplete-Gamma coefficients. -/
@[dlmf 8.11.E1]
def incGammaAsymptoticCoeff (a : ℂ) (k : ℕ) : ℂ :=
  (-1 : ℂ)^k*poch (1-a) k

/-- Normalized finite upper-Gamma remainder on the logarithmic plane. -/
@[dlmf 8.11.E2]
def incGammaAsymptoticRemainder (a : ℂ) (N : ℕ) (w : ℂ) : ℂ :=
  exp ((1-a)*w+exp w)*upperIncGammaOnLog a w-∑ k ∈ Finset.range N, incGammaAsymptoticCoeff a k*exp (-(k : ℂ)*w)

/-- Identity under the stated parameter and domain assumptions: `HasAsymptoticExpansion (logSector
(3*π/2-δ)) (fun k w => exp ((a-1-k)*w-exp w)) (incGammaAsymptoticCoeff a) (fun w =>
upperIncGammaOnLog a w)`. -/
@[dlmf 8.11.E3]
theorem upperIncGamma_log_asymptotic (a : ℂ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 3*π/2) :
    HasAsymptoticExpansion (logSector (3*π/2-δ)) (fun k w => exp ((a-1-k)*w-exp w)) (incGammaAsymptoticCoeff a) (fun w => upperIncGammaOnLog a w) := by
  have h := (genExpIntE_log_sector_asymptotic (1-a) hδ hδ1).mul_left (fun w => exp (a*w))
  have hφ : (fun (k : ℕ) (w : ℂ) => exp (a*w) * exp (-exp w-(k+1 : ℂ)*w)) =
      fun (k : ℕ) w => exp ((a-1-k)*w-exp w) := by
    funext k w; rw [← Complex.exp_add]; congr 1; ring
  have hf : (fun w => exp (a*w) • genExpIntEOnLog (1-a) w) = fun w => upperIncGammaOnLog a w := by
    funext w
    rw [smul_eq_mul, genExpIntEOnLog, show (1:ℂ) - (1 - a) = a by ring, ← mul_assoc,
      ← Complex.exp_add, show a*w + (1-a-1)*w = 0 by ring, Complex.exp_zero, one_mul]
  rw [hφ, hf] at h
  exact h

/-- The signed next-term real bound in DLMF §8.11(i). -/
theorem incGammaAsymptoticRemainder_real_bound {a x : ℝ} (hx : 0 < x) {N : ℕ} (hN : a-1 ≤ N) :
    ‖incGammaAsymptoticRemainder a N (Real.log x)‖ ≤ ‖incGammaAsymptoticCoeff a N/(x : ℂ)^N‖ ∧ 0 ≤ (incGammaAsymptoticRemainder a N (Real.log x)).re*(incGammaAsymptoticCoeff a N/(x : ℂ)^N).re := by
  have hx0 : (x:ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  set θ : ℝ := x^((N:ℝ)+1-a)*Real.exp x*(upperIncGamma ((a-N:ℝ):ℂ) x).re
  have hθ0 : 0 < θ := by
    have := incG_upperIncGamma_re_pos (a := a-N) hx (incG_integrableOn_rpow_exp_of_le_one (by linarith) hx)
    positivity
  have hθ1 : θ ≤ 1 := by
    have hle := incG_upperIncGamma_re_le (a := a-N) (by linarith) hx
    calc θ ≤ x^((N:ℝ)+1-a)*Real.exp x*(x^(a-N-1)*Real.exp (-x)) := by
          simp only [θ]; gcongr
      _ = 1 := by
        rw [show x^((N:ℝ)+1-a)*Real.exp x*(x^(a-N-1)*Real.exp (-x)) =
          (x^((N:ℝ)+1-a)*x^(a-N-1))*(Real.exp x*Real.exp (-x)) by ring,
          ← Real.rpow_add hx, ← Real.exp_add]; ring_nf; simp
  have hlog : upperIncGammaOnLog a (Real.log x) = upperIncGamma a x := by
    rw [DLMF.Confluent.upperIncGammaOnLog_eq_upperIncGamma a (by simpa using Real.pi_pos) (by simpa using Real.pi_pos.le),
      ← ofReal_exp, Real.exp_log hx]
  have hR : incGammaAsymptoticRemainder a N (Real.log x) = incGammaAsymptoticCoeff a N/(x : ℂ)^N*θ := by
    set X : ℂ := (x:ℂ)
    have hE : exp ((1-(a:ℂ))*(Real.log x : ℂ)+exp (Real.log x : ℂ)) = X^(1-(a:ℂ))*exp X := by
      rw [← ofReal_exp, Real.exp_log hx, ofReal_log hx.le, Complex.exp_add, cpow_def_of_ne_zero hx0,
        mul_comm (log X)]
    have hk : ∀ k : ℕ, exp (-(k:ℂ)*(Real.log x : ℂ)) = X^(-(k:ℂ)) := by
      intro k; rw [ofReal_log hx.le, cpow_def_of_ne_zero hx0, mul_comm]
    have hU := incG_upperIncGamma_expansion (a:ℂ) hx0 N
    have hθc : ((θ:ℝ):ℂ) = X^((N:ℂ)+1-a)*exp X*upperIncGamma ((a-N:ℝ):ℂ) x := by
      simp only [θ]
      conv_rhs => rw [incG_upperIncGamma_ofReal_re (a-N) hx]
      push_cast
      rw [ofReal_cpow hx.le]; push_cast; simp only [X]
    have hsum : ∀ k ∈ Finset.range N, X^(1-(a:ℂ))*exp X*((-1:ℂ)^k*poch (1-a) k*(X^((a:ℂ)-1-k)*exp (-X))) =
        incGammaAsymptoticCoeff a k*X^(-(k:ℂ)) := by
      intro k _
      have he : exp X*exp (-X) = 1 := by rw [← Complex.exp_add]; simp
      have hc : X^(1-(a:ℂ))*X^((a:ℂ)-1-k) = X^(-(k:ℂ)) := by
        rw [← cpow_add _ _ hx0]; ring_nf
      rw [incGammaAsymptoticCoeff]
      linear_combination ((-1:ℂ)^k*poch (1-a) k)*(X^(1-(a:ℂ))*X^((a:ℂ)-1-k))*he +
        ((-1:ℂ)^k*poch (1-a) k)*hc
    have hpow : X^(1-(a:ℂ)) = X^((N:ℂ)+1-a)*(X^N)⁻¹ := by
      rw [← cpow_natCast, ← cpow_neg, ← cpow_add _ _ hx0]; ring_nf
    unfold incGammaAsymptoticRemainder
    rw [hE, hlog, hU, mul_add, Finset.mul_sum, Finset.sum_congr rfl hsum]
    simp_rw [hk]
    rw [hθc, hpow, incGammaAsymptoticCoeff]
    push_cast
    simp only [X]
    ring
  rw [hR]
  constructor
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hθ0]
    exact mul_le_of_le_one_right (norm_nonneg _) hθ1
  · rw [re_mul_ofReal]; nlinarith [sq_nonneg (incGammaAsymptoticCoeff a N/(x : ℂ)^N).re]

/-- The series with terms `(fun k : ℕ => z^a*exp (-z)*z^k/poch a (k+1))` converges to
`(lowerIncGamma a z)`. -/
@[dlmf 8.11.E4]
theorem lowerIncGamma_large_parameter_hasSum {a : ℂ} (ha : ∀ n : ℕ, a ≠ -n) (z : ℂ) :
    HasSum (fun k : ℕ => z^a*exp (-z)*z^k/poch a (k+1)) (lowerIncGamma a z) := by
  have hs := (scIncGamma_hasSum_exponential a z).mul_left (Gamma a*z^a)
  have he : Gamma a*z^a*scIncGamma a z=lowerIncGamma a z := by
    rw [(scIncGamma_regularized_pair a z).2,lowerIncGamma_eq_regularized ha]
    ring
  rw [he] at hs
  refine hs.congr_fun fun k => ?_
  have hg := Gamma_add_nat_div_Gamma_eq (n:=k+1) a ha
  rw [← poch,div_eq_iff (Gamma_ne_zero ha)] at hg
  rw [show a+(k:ℂ)+1=a+((k+1:ℕ):ℂ) by push_cast; ring,hg]
  field_simp [Gamma_ne_zero ha]

/-- In the sector `|arg a| ≤ π - δ`, every shift `a + m` with `m ≥ 0` keeps a fixed fraction
of the modulus: `sin δ · ‖a‖ ≤ ‖a + m‖`. -/
theorem sin_mul_norm_le_norm_add_of_abs_arg_le {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < π) {a : ℂ}
    (harg : |arg a| ≤ π - δ) {m : ℝ} (hm : 0 ≤ m) :
    Real.sin δ * ‖a‖ ≤ ‖a + m‖ := by
  have hs : 0 ≤ Real.sin δ := Real.sin_nonneg_of_nonneg_of_le_pi hδ.le hδ1.le
  have hcos : -Real.cos δ ≤ Real.cos (arg a) := by
    rw [← Real.cos_abs (arg a), ← Real.cos_pi_sub]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith) harg
  have hre : a.re = ‖a‖ * Real.cos (arg a) := (Complex.norm_mul_cos_arg a).symm
  have hn : ‖a‖^2 = a.re^2 + a.im^2 := by rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hn' : ‖a + m‖^2 = (a.re + m)^2 + a.im^2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
  have hsc := Real.sin_sq_add_cos_sq δ
  have h0 : 0 ≤ ‖a‖ := norm_nonneg _
  have hre' : -(‖a‖ * Real.cos δ) ≤ a.re := by rw [hre]; nlinarith
  refine (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).mp ?_
  rw [mul_pow, hn', hn]
  nlinarith [sq_nonneg (‖a‖ * Real.cos δ - m), mul_nonneg hm (by linarith : 0 ≤ a.re + ‖a‖ * Real.cos δ)]

/-- Pochhammer lower bound in the sector: `(sin δ · ‖a‖)^k ≤ ‖(a + m)_k‖` for `m ≥ 0`. -/
theorem pow_le_norm_poch_of_abs_arg_le {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < π) {a : ℂ}
    (harg : |arg a| ≤ π - δ) {m : ℝ} (hm : 0 ≤ m) (k : ℕ) :
    (Real.sin δ * ‖a‖)^k ≤ ‖poch (a + m) k‖ := by
  have hs : 0 ≤ Real.sin δ := Real.sin_nonneg_of_nonneg_of_le_pi hδ.le hδ1.le
  induction k with
  | zero => simp [poch_zero]
  | succ k ih =>
    rw [poch_succ, norm_mul, pow_succ]
    have h := sin_mul_norm_le_norm_add_of_abs_arg_le hδ hδ1 harg (m := m + k) (by positivity)
    rw [show a + ((m + k : ℝ) : ℂ) = a + m + k by push_cast; ring] at h
    exact mul_le_mul ih h (by positivity) (norm_nonneg _)

/-- Formula under the stated hypotheses: `IsBigO (sector (π-δ)) (fun a => lowerIncGamma a
z-z^a*exp (-z)*∑ k ∈ Finset.range N, z^k/poch a (k+1)) (fun a => z^a*exp (-z)*z^N/poch a
(N+1))`. -/
@[dlmf 8.11.E4]
theorem lowerIncGamma_large_parameter_asymptotic {z : ℂ} (hz : z ≠ 0) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < π) (N : ℕ) :
    IsBigO (sector (π-δ)) (fun a => lowerIncGamma a z-z^a*exp (-z)*∑ k ∈ Finset.range N, z^k/poch a (k+1)) (fun a => z^a*exp (-z)*z^N/poch a (N+1)) := by
  set c := Real.sin δ with hc
  have hc0 : 0 < c := Real.sin_pos_of_pos_of_lt_pi hδ hδ1
  have hev : ∀ᶠ a in sector (π-δ), 2*‖z‖/c ≤ ‖a‖ ∧ a ≠ 0 ∧ |arg a| ≤ π-δ := by
    have h1 : ∀ᶠ a in sector (π-δ), 2*‖z‖/c ≤ ‖a‖ :=
      ((eventually_ge_atTop (2*‖z‖/c)).comap norm).filter_mono inf_le_left
    have h2 : ∀ᶠ a in sector (π-δ), a ≠ 0 ∧ |arg a| ≤ π-δ :=
      mem_inf_of_right (mem_principal_self _)
    filter_upwards [h1, h2] with a ha1 ha2 using ⟨ha1, ha2⟩
  refine IsBigO.of_bound 2 ?_
  filter_upwards [hev] with a ⟨hR, ha0, harg⟩
  have hnp : ∀ n : ℕ, a ≠ -n := by
    intro n hn
    rcases Nat.eq_zero_or_pos n with h | h
    · exact ha0 (by simp [hn, h])
    · have : arg a = π := by
        rw [hn, show -(n:ℂ) = ((-(n:ℝ) : ℝ) : ℂ) by push_cast; ring]
        have hn0 : (0:ℝ) < n := by exact_mod_cast h
        exact Complex.arg_ofReal_of_neg (by linarith)
      rw [this, abs_of_pos Real.pi_pos] at harg
      linarith
  set B : ℂ := z^a*exp (-z)*z^N/poch a (N+1) with hB
  have hs := lowerIncGamma_large_parameter_hasSum hnp z
  have htail := (hasSum_nat_add_iff' N).mpr hs
  have hterm : ∀ k : ℕ, z^a*exp (-z)*z^(k+N)/poch a (k+N+1) = B * (z^k/poch (a+((N+1:ℕ):ℝ)) k) := by
    intro k
    rw [show k+N+1 = (N+1)+k by ring, poch_add, hB]
    push_cast
    rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, mul_inv, pow_add]
    ring
  simp only [hterm] at htail
  clear_value B
  have hbound : ∀ k : ℕ, ‖B * (z^k/poch (a+((N+1:ℕ):ℝ)) k)‖ ≤ ‖B‖ * (1/2)^k := by
    intro k
    rw [norm_mul, norm_div, norm_pow]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have hp := pow_le_norm_poch_of_abs_arg_le hδ hδ1 harg (m := ((N+1:ℕ):ℝ)) (by positivity) k
    have hca : 2*‖z‖ ≤ c*‖a‖ := by
      rw [div_le_iff₀ hc0] at hR; linarith
    have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
    have hpos : 0 < (c*‖a‖)^k := pow_pos (by nlinarith) k
    rw [div_le_iff₀ (lt_of_lt_of_le hpos hp)]
    calc ‖z‖^k = (1/2)^k * (2*‖z‖)^k := by rw [← mul_pow]; ring_nf
      _ ≤ (1/2)^k * (c*‖a‖)^k := by gcongr
      _ ≤ (1/2)^k * ‖poch (a+((N+1:ℕ):ℝ)) k‖ := by gcongr
  have hgeom : HasSum (fun k : ℕ => ‖B‖ * (1/2:ℝ)^k) (‖B‖ * 2) := by
    have := (hasSum_geometric_two).mul_left ‖B‖
    simpa [one_div] using this
  have hle := htail.norm_le_of_bounded hgeom hbound
  rw [Finset.mul_sum]
  have hsum : ∑ k ∈ Finset.range N, z^a*exp (-z)*(z^k/poch a (k+1)) =
      ∑ k ∈ Finset.range N, z^a*exp (-z)*z^k/poch a (k+1) :=
    Finset.sum_congr rfl fun k _ => by ring
  rw [hsum]
  linarith

/-- On the logarithmic sector, `exp` maps into the principal sector. -/
theorem igAsy_tendsto_exp_logSector {α : ℝ} (hα : α < π) :
    Tendsto exp (logSector α) (sector α) := by
  refine tendsto_inf.mpr ⟨?_, ?_⟩
  · rw [tendsto_comap_iff]
    have : (norm ∘ exp : ℂ → ℝ) = fun w : ℂ => Real.exp w.re := by
      funext w; simp [Complex.norm_exp]
    rw [this]
    exact tendsto_comap.mono_left inf_le_left
  · rw [tendsto_principal]
    filter_upwards [mem_inf_of_right (mem_principal_self _)] with w hw
    have hw' : |w.im| ≤ α := hw
    refine ⟨Complex.exp_ne_zero w, ?_⟩
    have h1 : -π < w.im := by linarith [neg_abs_le w.im]
    have h2 : w.im ≤ π := by linarith [le_abs_self w.im]
    rw [← Complex.log_im, Complex.log_exp h1 h2]
    exact hw'

/-- Points of a sector of half-angle `π - δ` are not nonpositive integers. -/
theorem igAsy_ne_neg_nat {δ : ℝ} (hδ : 0 < δ) {a : ℂ} (ha0 : a ≠ 0) (harg : |arg a| ≤ π-δ) (n : ℕ) :
    a ≠ -n := by
  intro hn
  rcases Nat.eq_zero_or_pos n with h | h
  · exact ha0 (by simp [hn, h])
  · have : arg a = π := by
      rw [hn, show -(n:ℂ) = ((-(n:ℝ) : ℝ) : ℂ) by push_cast; ring]
      have hn0 : (0:ℝ) < n := by exact_mod_cast h
      exact Complex.arg_ofReal_of_neg (by linarith)
    rw [this, abs_of_pos Real.pi_pos] at harg
    linarith

/-- First half of 8.11.5 on the principal sector. -/
theorem igAsy_normIncGammaP_equiv_sector {z : ℂ} (hz : z ≠ 0) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < π) :
    IsEquivalent (sector (π-δ)) (fun a => normIncGammaPContinued a z)
      (fun a => z^a*exp (-z)/Gamma (1+a)) := by
  have H := lowerIncGamma_large_parameter_asymptotic hz hδ hδ1 1
  have hev : ∀ᶠ a in sector (π-δ), a ≠ 0 ∧ |arg a| ≤ π-δ :=
    mem_inf_of_right (mem_principal_self _)
  have hnorm : Tendsto (fun a : ℂ => ‖a‖) (sector (π-δ)) atTop :=
    tendsto_comap.mono_left inf_le_left
  have hsmall : Tendsto (fun a : ℂ => z/(a+1)) (sector (π-δ)) (𝓝 0) := by
    have h2 : ∀ᶠ a in sector (π-δ), 2 ≤ ‖a‖ := hnorm.eventually_ge_atTop 2
    have hlim : Tendsto (fun a : ℂ => ‖z‖/(‖a‖-1)) (sector (π-δ)) (𝓝 0) := by
      have := (tendsto_atTop_add_const_right _ (-1) hnorm).inv_tendsto_atTop.const_mul ‖z‖
      simpa [div_eq_mul_inv, sub_eq_add_neg] using this
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [h2] with a ha
    rw [norm_div]
    have h1 : ‖a‖-1 ≤ ‖a+1‖ := by
      have := norm_sub_norm_le a (-1); simp at this; linarith [norm_add_le a 1, norm_sub_le a (-1)]
    gcongr
    linarith
  have hlo : (fun a => z^a*exp (-z)/Gamma (1+a) * (z/(a+1))) =o[sector (π-δ)]
      (fun a => z^a*exp (-z)/Gamma (1+a)) := by
    have := (isBigO_refl (fun a => z^a*exp (-z)/Gamma (1+a)) (sector (π-δ))).mul_isLittleO
      ((isLittleO_one_iff ℂ).mpr hsmall)
    simpa using this
  refine IsBigO.trans_isLittleO ?_ hlo
  have H2 := H.mul (isBigO_refl (fun a => (Gamma a)⁻¹) (sector (π-δ)))
  refine (H2.congr' ?_ ?_)
  · filter_upwards [hev] with a ⟨ha0, harg⟩
    have hnp := igAsy_ne_neg_nat hδ ha0 harg
    simp only [Pi.sub_apply]
    rw [normIncGammaPContinued_eq hnp, normIncGammaP, add_comm 1 a,
      Complex.Gamma_add_one a ha0]
    simp [poch_one]
    field_simp
  · filter_upwards [hev] with a ⟨ha0, harg⟩
    have hnp := igAsy_ne_neg_nat hδ ha0 harg
    have ha1 : a + 1 ≠ 0 := by simpa [add_eq_zero_iff_eq_neg] using hnp 1
    rw [add_comm 1 a, Complex.Gamma_add_one a ha0, show (1:ℕ)+1 = 2 by rfl]
    simp [poch_succ, poch_zero]
    field_simp

/-- Stirling's formula in the form used for 8.11.5. -/
theorem igAsy_stirling_logSector {z : ℂ} (hz : z ≠ 0) {w : ℂ} (hw1 : -π < w.im) (hw2 : w.im < π) :
    z^(exp w)*exp (-z)/Gamma (1+exp w) =
      exp (exp w-z+exp w*(log z-w)-w/2)/Real.sqrt (2*π) * exp (-DLMF.Gamma.binetMu (exp w)) := by
  set a := exp w with ha
  have ha0 : a ≠ 0 := Complex.exp_ne_zero w
  have hlog : log a = w := Complex.log_exp hw1 hw2.le
  have hslit : a ∈ slitPlane := by
    rw [mem_slitPlane_iff_arg]; refine ⟨?_, ha0⟩
    rw [← Complex.log_im, hlog]; exact hw2.ne
  have hG : Gamma (1+a) = exp (w + DLMF.Gamma.binetExponent a) := by
    rw [add_comm, Complex.Gamma_add_one a ha0, DLMF.Gamma.Gamma_eq_exp_binetExponent hslit,
      Complex.exp_add, ha]
  have hsq : (Real.sqrt (2*π) : ℂ) = exp ((1/2)*log (2*π)) := by
    have h2 : (0:ℝ) < 2*π := by positivity
    rw [show (2*π : ℂ) = ((2*π : ℝ) : ℂ) by push_cast; ring, ← ofReal_log h2.le,
      show (1/2 : ℂ) * ((Real.log (2*π) : ℝ) : ℂ) = (((1/2) * Real.log (2*π) : ℝ) : ℂ) by push_cast; ring,
      ← ofReal_exp, Real.sqrt_eq_rpow, Real.rpow_def_of_pos h2, mul_comm]
  rw [hG, hsq, cpow_def_of_ne_zero hz, DLMF.Gamma.binetExponent, hlog]
  simp only [div_eq_mul_inv, ← Complex.exp_neg, ← Complex.exp_add]
  congr 1
  ring

/-- The Binet remainder tends to zero on the logarithmic sector. -/
theorem igAsy_tendsto_binetMu_logSector {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < π) :
    Tendsto (fun w => DLMF.Gamma.binetMu (exp w)) (logSector (π-δ)) (𝓝 0) := by
  have hc : 0 < 1 - Real.cos δ := by
    have := Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl 0) hδ1.le hδ
    rw [Real.cos_zero] at this
    linarith
  have hE : Tendsto (fun w : ℂ => Real.exp w.re) (logSector (π-δ)) atTop :=
    tendsto_comap.mono_left inf_le_left
  have hlim : Tendsto (fun w : ℂ => 1/(6*(Real.exp w.re*(1-Real.cos δ)))) (logSector (π-δ)) (𝓝 0) := by
    have := ((hE.atTop_mul_const hc).const_mul_atTop (by norm_num : (0:ℝ) < 6)).inv_tendsto_atTop
    refine this.congr fun w => ?_
    simp only [Pi.inv_apply, one_div]
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [mem_inf_of_right (mem_principal_self _)] with w hw
  have hw' : |w.im| ≤ π-δ := hw
  have h1 : -π < w.im := by linarith [neg_abs_le w.im]
  have h2 : w.im < π := by linarith [le_abs_self w.im]
  set a := exp w
  have ha0 : a ≠ 0 := Complex.exp_ne_zero w
  have harg : arg a = w.im := by rw [← Complex.log_im, Complex.log_exp h1 h2.le]
  have hslit : a ∈ slitPlane := by
    rw [mem_slitPlane_iff_arg]; exact ⟨by rw [harg]; exact h2.ne, ha0⟩
  have hn : ‖a‖ = Real.exp w.re := Complex.norm_exp w
  have hre : -(‖a‖*Real.cos δ) ≤ a.re := by
    have hcos : -Real.cos δ ≤ Real.cos (arg a) := by
      rw [← Real.cos_abs (arg a), ← Real.cos_pi_sub]
      exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith) (by rw [harg]; exact hw')
    rw [← Complex.norm_mul_cos_arg a]; nlinarith [norm_nonneg a]
  refine (DLMF.Gamma.norm_binetMu_le hslit).trans ?_
  rw [← hn]
  have hp : 0 < ‖a‖*(1-Real.cos δ) := mul_pos (norm_pos_iff.mpr ha0) hc
  gcongr
  linarith

/-- Identity under the stated parameter and domain assumptions: `IsEquivalent (logSector (π-δ))
(fun w => normIncGammaPContinued (exp w) z) (fun w => z^(exp w)*exp (-z)/Gamma (1+exp w)) ∧
IsEquivalent (logSector (π-δ)) (fun w => normIncGammaPContinued (exp w) z) (fun w => exp (exp
w-z+exp w*(log z-w)-w/2)/Real.sqrt (2*π))`. -/
@[dlmf 8.11.E5]
theorem normIncGammaP_large_parameter_equivalent {z : ℂ} (hz : z ≠ 0) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < π) :
    IsEquivalent (logSector (π-δ)) (fun w => normIncGammaPContinued (exp w) z) (fun w => z^(exp w)*exp (-z)/Gamma (1+exp w)) ∧ IsEquivalent (logSector (π-δ)) (fun w => normIncGammaPContinued (exp w) z) (fun w => exp (exp w-z+exp w*(log z-w)-w/2)/Real.sqrt (2*π)) := by
  have h1 := (igAsy_normIncGammaP_equiv_sector hz hδ hδ1).comp_tendsto
    (igAsy_tendsto_exp_logSector (by linarith : π-δ < π))
  refine ⟨h1, h1.trans ?_⟩
  have hmu := igAsy_tendsto_binetMu_logSector hδ hδ1
  have hexp : Tendsto (fun w => exp (-DLMF.Gamma.binetMu (exp w))) (logSector (π-δ)) (𝓝 1) := by
    have := (Complex.continuous_exp.tendsto (-0)).comp hmu.neg
    simpa [Function.comp_def] using this
  refine (isEquivalent_iff_exists_eq_mul.mpr ⟨_, hexp, ?_⟩)
  filter_upwards [mem_inf_of_right (mem_principal_self _)] with w hw
  have hw' : |w.im| ≤ π-δ := hw
  simp only [Function.comp, Pi.mul_apply]
  rw [igAsy_stirling_logSector hz (by linarith [neg_abs_le w.im]) (by linarith [le_abs_self w.im])]
  ring

/-- Polynomials b_k(lam), defined by the differential recurrence 8.11.9. -/
@[dlmf 8.11.E9]
def incGammaLambdaPolynomial : ℕ → Polynomial ℂ
  | 0 => 1
  | k+1 => Polynomial.X*(1-Polynomial.X)*(incGammaLambdaPolynomial k).derivative+
      Polynomial.C (2*(k : ℂ)+1)*Polynomial.X*incGammaLambdaPolynomial k

/-- Identity under the stated parameter and domain assumptions: `incGammaLambdaPolynomial 0=1 ∧
incGammaLambdaPolynomial 1=Polynomial.X ∧ incGammaLambdaPolynomial
2=Polynomial.X*(2*Polynomial.X+1)`. -/
@[dlmf 8.11.E8]
theorem incGammaLambdaPolynomial_initial  :
    incGammaLambdaPolynomial 0=1 ∧ incGammaLambdaPolynomial 1=Polynomial.X ∧ incGammaLambdaPolynomial 2=Polynomial.X*(2*Polynomial.X+1) := by
  norm_num [incGammaLambdaPolynomial, Polynomial.derivative_mul, Polynomial.derivative_X, Polynomial.C_ofNat]
  ring

/-- `1 - x s > 0` for `x < 1` and `s ∈ [0,1]`. -/
theorem igAsy_one_sub_mul_pos {x s : ℝ} (hx : x < 1) (hs : s ∈ Icc (0:ℝ) 1) : 0 < 1 - x*s := by
  rcases le_or_gt x 0 with h | h
  · nlinarith [mul_nonpos_of_nonpos_of_nonneg h hs.1]
  · nlinarith [mul_le_mul_of_nonneg_left hs.2 h.le]

/-- Real version of the polynomials `b_k` of 8.11.9. -/
noncomputable def igAsy_b : ℕ → Polynomial ℝ
  | 0 => 1
  | k+1 => Polynomial.X*(1-Polynomial.X)*(igAsy_b k).derivative +
      Polynomial.C (2*(k:ℝ)+1)*Polynomial.X*igAsy_b k

/-- `igAsy_b` complexifies to `incGammaLambdaPolynomial`. -/
theorem igAsy_b_map (k : ℕ) : (igAsy_b k).map (algebraMap ℝ ℂ) = incGammaLambdaPolynomial k := by
  induction k with
  | zero => simp [igAsy_b, incGammaLambdaPolynomial]
  | succ k ih =>
    rw [igAsy_b, incGammaLambdaPolynomial, ← ih]
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_one,
      Polynomial.map_X, Polynomial.map_C, Polynomial.derivative_map]
    simp

/-- `b_k(x)` at a real point. -/
theorem igAsy_b_eval (k : ℕ) (x : ℝ) :
    (incGammaLambdaPolynomial k).eval (x : ℂ) = (((igAsy_b k).eval x : ℝ) : ℂ) := by
  rw [← igAsy_b_map, Polynomial.eval_map, show (x:ℂ) = algebraMap ℝ ℂ x from rfl,
    Polynomial.eval₂_at_apply]
  rfl

/-- `v_k(y) = b_k(y)/(1-y)^{2k}`. -/
noncomputable def igAsy_v (k : ℕ) (y : ℝ) : ℝ := (igAsy_b k).eval y / (1-y)^(2*k)

/-- `v_0 = 1`. -/
theorem igAsy_v_zero (y : ℝ) : igAsy_v 0 y = 1 := by simp [igAsy_v, igAsy_b]

/-- The primitive `W_k(t) = b_k(λt)/(1-λt)^{2k+1}`. -/
noncomputable def igAsy_W (k : ℕ) (l t : ℝ) : ℝ := (igAsy_b k).eval (l*t) / (1-l*t)^(2*k+1)

/-- The derivative of `W_k`. -/
noncomputable def igAsy_W' (k : ℕ) (l t : ℝ) : ℝ :=
  l*((igAsy_b k).derivative.eval (l*t)*(1-l*t) + (2*k+1)*(igAsy_b k).eval (l*t))/(1-l*t)^(2*k+2)

/-- `W_k` has derivative `W_k'` where `1 - λt ≠ 0`. -/
theorem igAsy_hasDerivAt_W (k : ℕ) {l t : ℝ} (h : 1 - l*t ≠ 0) :
    HasDerivAt (igAsy_W k l) (igAsy_W' k l t) t := by
  have hP := ((igAsy_b k).hasDerivAt (l*t)).comp t ((hasDerivAt_id t).const_mul l)
  have hD := (((hasDerivAt_id t).const_mul l).const_sub 1).pow (2*k+1)
  have hq := hP.div hD (pow_ne_zero _ h)
  unfold igAsy_W
  convert hq using 1
  · funext s; simp [Function.comp_def]
  unfold igAsy_W'
  simp only [id, mul_one, Function.comp_apply, Pi.pow_apply]
  rw [show 2*k+1-1 = 2*k by omega]
  field_simp
  push_cast
  ring

/-- `t W_k'(t) = v_{k+1}(λt)`. -/
theorem igAsy_mul_W' (k : ℕ) (l t : ℝ) :
    t * igAsy_W' k l t = igAsy_v (k+1) (l*t) := by
  unfold igAsy_W' igAsy_v
  simp only [igAsy_b, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
    Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_C]
  rw [show 2*(k+1) = 2*k+2 by ring]
  field_simp

/-- The integrand `g(t) = t^{a-1} e^{λa(1-t)}` of `e^{λa} γ*`-type integrals. -/
noncomputable def igAsy_g (l : ℝ) (a : ℂ) (t : ℝ) : ℂ := (t:ℂ)^(a-1) * exp (l*a*(1-t))

/-- `H(t) = t^a e^{λa(1-t)}`. -/
noncomputable def igAsy_H (l : ℝ) (a : ℂ) (t : ℝ) : ℂ := (t:ℂ)^a * exp (l*a*(1-t))

/-- `H' = a(1-λt) g` for `t > 0`. -/
theorem igAsy_hasDerivAt_H (l : ℝ) (a : ℂ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (igAsy_H l a) (a*(1-l*t)*igAsy_g l a t) t := by
  have hslit : (t:ℂ) ∈ slitPlane := by simpa using ofReal_mem_slitPlane.mpr ht
  have h1 := (Complex.hasStrictDerivAt_cpow_const (c := a) hslit).hasDerivAt.comp_ofReal
  have h2 : HasDerivAt (fun s : ℝ => exp (l*a*(1-(s:ℂ)))) (exp (l*a*(1-t)) * (-(l*a))) t := by
    have := ((((hasDerivAt_id' (t:ℂ)).const_sub 1).const_mul ((l:ℂ)*a)).cexp).comp_ofReal
    convert this using 1; ring
  have h := h1.mul h2
  unfold igAsy_H
  convert h using 1
  unfold igAsy_g
  have ht0 : (t:ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  rw [show (t:ℂ)^a = (t:ℂ)^(a-1) * t by
        have := cpow_add (a-1) 1 ht0; rwa [sub_add_cancel, cpow_one] at this]
  ring

/-- `W_k` is continuous on `[0,1]` for `λ < 1`. -/
theorem igAsy_continuousOn_W (k : ℕ) {l : ℝ} (hl : l < 1) :
    ContinuousOn (igAsy_W k l) (uIcc 0 1) := by
  unfold igAsy_W
  refine ContinuousOn.div (by fun_prop) (by fun_prop) fun s hs => ?_
  rw [uIcc_of_le zero_le_one] at hs
  exact pow_ne_zero _ (igAsy_one_sub_mul_pos hl hs).ne'

/-- `t ↦ v_k(λt)` is continuous on `[0,1]` for `λ < 1`. -/
theorem igAsy_continuousOn_v (k : ℕ) {l : ℝ} (hl : l < 1) :
    ContinuousOn (fun s => igAsy_v k (l*s)) (uIcc 0 1) := by
  unfold igAsy_v
  refine ContinuousOn.div (by fun_prop) (by fun_prop) fun s hs => ?_
  rw [uIcc_of_le zero_le_one] at hs
  exact pow_ne_zero _ (igAsy_one_sub_mul_pos hl hs).ne'

/-- `W_k'` is continuous on `[0,1]` for `λ < 1`. -/
theorem igAsy_continuousOn_W' (k : ℕ) {l : ℝ} (hl : l < 1) :
    ContinuousOn (igAsy_W' k l) (uIcc 0 1) := by
  unfold igAsy_W'
  refine ContinuousOn.div (by fun_prop) (by fun_prop) fun s hs => ?_
  rw [uIcc_of_le zero_le_one] at hs
  exact pow_ne_zero _ (igAsy_one_sub_mul_pos hl hs).ne'

/-- `g` is continuous for `Re a > 1`. -/
theorem igAsy_continuous_g (l : ℝ) {a : ℂ} (ha : 1 < a.re) : Continuous (igAsy_g l a) := by
  unfold igAsy_g
  refine Continuous.mul ?_ (by fun_prop)
  exact continuous_iff_continuousAt.mpr fun t =>
    (Complex.continuousAt_ofReal_cpow_const t (a-1) (Or.inl (by simp; linarith)))

/-- One complex integration by parts. -/
theorem igAsy_ibpC (k : ℕ) {l : ℝ} (hl : l < 1) {a : ℂ} (ha : 1 < a.re) :
    ∫ t in (0:ℝ)..1, igAsy_g l a t * igAsy_v k (l*t) =
      igAsy_W k l 1/a - 1/a * ∫ t in (0:ℝ)..1, igAsy_g l a t * igAsy_v (k+1) (l*t) := by
  have ha0 : a ≠ 0 := fun h => by simp [h] at ha; linarith
  have hgc := igAsy_continuous_g l ha
  have hHc : ContinuousOn (igAsy_H l a) (uIcc 0 1) := by
    unfold igAsy_H
    refine ContinuousOn.mul ?_ (by fun_prop)
    exact (continuous_iff_continuousAt.mpr fun t =>
      (Complex.continuousAt_ofReal_cpow_const t a (Or.inl (by linarith)))).continuousOn
  have hv : ContinuousOn (fun s : ℝ => ((igAsy_W k l s : ℝ) : ℂ)/a) (uIcc 0 1) :=
    ((continuous_ofReal.comp_continuousOn (igAsy_continuousOn_W k hl))).div_const _
  have hu' : ∀ t ∈ Ioo (min (0:ℝ) 1) (max 0 1), HasDerivAt (igAsy_H l a)
      (a*(1-l*t)*igAsy_g l a t) t := fun t ht => igAsy_hasDerivAt_H l a (by simpa using ht.1)
  have hv' : ∀ t ∈ Ioo (min (0:ℝ) 1) (max 0 1), HasDerivAt (fun s : ℝ => ((igAsy_W k l s : ℝ) : ℂ)/a)
      (((igAsy_W' k l t : ℝ) : ℂ)/a) t := by
    intro t ht
    simp only [min_eq_left zero_le_one, max_eq_right zero_le_one] at ht
    exact ((igAsy_hasDerivAt_W k (igAsy_one_sub_mul_pos hl ⟨ht.1.le, ht.2.le⟩).ne').ofReal_comp).div_const _
  have hi1 : IntervalIntegrable (fun t : ℝ => a*(1-l*t)*igAsy_g l a t) volume 0 1 :=
    (by fun_prop : Continuous fun t : ℝ => a*(1-l*t)*igAsy_g l a t).intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun t : ℝ => ((igAsy_W' k l t : ℝ) : ℂ)/a) volume 0 1 :=
    ((continuous_ofReal.comp_continuousOn (igAsy_continuousOn_W' k hl)).div_const _).intervalIntegrable
  have H := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt hHc hv hu' hv' hi1 hi2
  have hc1 : ∫ t in (0:ℝ)..1, igAsy_H l a t * (((igAsy_W' k l t : ℝ) : ℂ)/a) =
      (∫ t in (0:ℝ)..1, igAsy_g l a t * igAsy_v (k+1) (l*t))/a := by
    rw [← intervalIntegral.integral_div]
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [← igAsy_mul_W']
    unfold igAsy_H igAsy_g
    rcases eq_or_ne t 0 with h0 | h0
    · subst h0; simp [zero_cpow ha0]
    · have ht0 : (t:ℂ) ≠ 0 := by exact_mod_cast h0
      rw [show (t:ℂ)^a = (t:ℂ)^(a-1) * t by
        have := cpow_add (a-1) 1 ht0; rwa [sub_add_cancel, cpow_one] at this]
      push_cast; ring
  have hc2 : ∫ t in (0:ℝ)..1, a*(1-l*t)*igAsy_g l a t * (((igAsy_W k l t : ℝ) : ℂ)/a) =
      ∫ t in (0:ℝ)..1, igAsy_g l a t * igAsy_v k (l*t) := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le zero_le_one] at ht
    have h1 := (igAsy_one_sub_mul_pos hl ht).ne'
    have h1' : (1:ℂ) - l*t ≠ 0 := by exact_mod_cast h1
    simp only [igAsy_W, igAsy_v]
    push_cast
    field_simp
    ring
  rw [hc1, hc2] at H
  have hH1 : igAsy_H l a 1 = 1 := by simp [igAsy_H]
  have hH0 : igAsy_H l a 0 = 0 := by simp [igAsy_H, zero_cpow ha0]
  rw [hH1, hH0] at H
  field_simp at H ⊢
  linear_combination H

/-- Iterated complex integration by parts. -/
theorem igAsy_iterC {l : ℝ} (hl : l < 1) {a : ℂ} (ha : 1 < a.re) (N : ℕ) :
    ∫ t in (0:ℝ)..1, igAsy_g l a t =
      ∑ k ∈ Finset.range N, (-1)^k/a^(k+1) * (igAsy_W k l 1 : ℂ) +
        (-1)^N/a^N * ∫ t in (0:ℝ)..1, igAsy_g l a t * igAsy_v N (l*t) := by
  have ha0 : a ≠ 0 := fun h => by simp [h] at ha; linarith
  induction N with
  | zero => simp [igAsy_v_zero]
  | succ N ih =>
    rw [ih, igAsy_ibpC N hl ha, Finset.sum_range_succ]
    ring

/-- `∫₀¹ e^{-c(1-t)} dt ≤ 1/c`. -/
theorem igAsy_integral_exp_le {c : ℝ} (hc0 : 0 < c) :
    ∫ t in (0:ℝ)..1, Real.exp (-c*(1-t)) ≤ 1/c := by
  have hd : ∀ s ∈ uIcc (0:ℝ) 1, HasDerivAt (fun s : ℝ => Real.exp (-c*(1-s))/c)
      (Real.exp (-c*(1-s))) s := by
    intro s _
    have := ((Real.hasDerivAt_exp (-c*(1-s))).comp s
      (((hasDerivAt_id s).const_sub 1).const_mul (-c))).div_const c
    convert this using 1
    simp only [id, Function.comp_apply]
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((by fun_prop : Continuous fun s : ℝ => Real.exp (-c*(1-s))).intervalIntegrable _ _)]
  simp only [sub_self, mul_zero, Real.exp_zero]
  rw [div_sub_div_same, div_le_div_iff_of_pos_right hc0]
  linarith [Real.exp_pos (-c*(1-0))]

/-- Pointwise bound `‖t^{a-1} e^{λa(1-t)}‖ ≤ e^{-(Re a(1-λ)-1)(1-t)}`. -/
theorem igAsy_norm_g_le {l : ℝ} {a : ℂ} (ha : 1 < a.re) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖igAsy_g l a t‖ ≤ Real.exp (-(a.re*(1-l)-1)*(1-t)) := by
  unfold igAsy_g
  rcases ht0.eq_or_lt with h | h
  · subst h
    have : a - 1 ≠ 0 := fun h' => by
      have := congrArg Complex.re h'; simp at this; linarith
    simp [zero_cpow this]; positivity
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos h, Complex.norm_exp]
  have hre : (l * a * (1 - (t:ℂ))).re = l*a.re*(1-t) := by simp
  rw [hre, sub_re, one_re]
  have h1 : t ≤ Real.exp (t-1) := by linarith [Real.add_one_le_exp (t-1)]
  have h2 : t^(a.re-1) ≤ Real.exp ((t-1)*(a.re-1)) := by
    rw [Real.exp_mul]; exact Real.rpow_le_rpow h.le h1 (by linarith)
  calc t^(a.re-1) * Real.exp (l*a.re*(1-t)) ≤ Real.exp ((t-1)*(a.re-1)) * Real.exp (l*a.re*(1-t)) :=
        mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
    _ = Real.exp (-(a.re*(1-l)-1)*(1-t)) := by rw [← Real.exp_add]; ring_nf

/-- Remainder bound for the complex integral. -/
theorem igAsy_norm_integral_le {l : ℝ} (hl : l < 1) {a : ℂ} (ha : 1 < a.re) (ha2 : 2 ≤ a.re*(1-l))
    {N : ℕ} {K : ℝ} (hK : ∀ t ∈ Icc (0:ℝ) 1, |igAsy_v N (l*t)| ≤ K) :
    ‖∫ t in (0:ℝ)..1, igAsy_g l a t * igAsy_v N (l*t)‖ ≤ K * (2/(a.re*(1-l))) := by
  have hK0 : 0 ≤ K := le_trans (abs_nonneg _) (hK 0 ⟨le_rfl, zero_le_one⟩)
  set c := (a.re*(1-l))/2 with hc_def
  have hc : 0 < c := by linarith
  have hcont : ContinuousOn (fun t : ℝ => igAsy_g l a t * igAsy_v N (l*t)) (uIcc 0 1) :=
    (igAsy_continuous_g l ha).continuousOn.mul
      (continuous_ofReal.comp_continuousOn (igAsy_continuousOn_v N hl))
  refine (intervalIntegral.norm_integral_le_integral_norm zero_le_one).trans ?_
  calc ∫ t in (0:ℝ)..1, ‖igAsy_g l a t * igAsy_v N (l*t)‖
      ≤ ∫ t in (0:ℝ)..1, K * Real.exp (-c*(1-t)) := by
        refine intervalIntegral.integral_mono_on zero_le_one hcont.norm.intervalIntegrable
          ((by fun_prop : Continuous fun t : ℝ => K * Real.exp (-c*(1-t))).intervalIntegrable _ _) ?_
        intro t ht
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_comm]
        refine mul_le_mul (hK t ht) ((igAsy_norm_g_le ha ht.1 ht.2).trans ?_) (norm_nonneg _) hK0
        rw [Real.exp_le_exp]
        have : 0 ≤ 1 - t := by linarith [ht.2]
        nlinarith
    _ = K * ∫ t in (0:ℝ)..1, Real.exp (-c*(1-t)) := intervalIntegral.integral_const_mul _ _
    _ ≤ K * (1/c) := mul_le_mul_of_nonneg_left (igAsy_integral_exp_le hc) hK0
    _ = K * (2/(a.re*(1-l))) := by rw [hc_def]; field_simp

/-- Identity under the stated parameter and domain assumptions: `HasAsymptoticExpansion (logSector
(π/2-δ)) (fun k w => exp (exp w*(w+Real.log lam)-lam*exp w-(k+1 : ℂ)*w)/(lam-1 : ℂ)^(2*k+1))
(fun k => -(-1 : ℂ)^k*(incGammaLambdaPolynomial k).eval (lam : ℂ)) (fun w =>
lowerIncGammaOnLog (exp w) (w+Real.log lam))`. -/
@[dlmf 8.11.E6]
theorem lowerIncGamma_fixed_ratio_asymptotic {lam : ℝ} (hlam : 0 < lam) (hlam1 : lam < 1) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < π/2) :
    HasAsymptoticExpansion (logSector (π/2-δ)) (fun k w => exp (exp w*(w+Real.log lam)-lam*exp w-(k+1 : ℂ)*w)/(lam-1 : ℂ)^(2*k+1)) (fun k => -(-1 : ℂ)^k*(incGammaLambdaPolynomial k).eval (lam : ℂ)) (fun w => lowerIncGammaOnLog (exp w) (w+Real.log lam)) := by
  intro N
  obtain ⟨K, hK⟩ : ∃ K, ∀ t ∈ Icc (0:ℝ) 1, |igAsy_v N (lam*t)| ≤ K := by
    obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn
      (by simpa [uIcc_of_le zero_le_one] using igAsy_continuousOn_v N hlam1)
    exact ⟨K, fun t ht => by simpa [Real.norm_eq_abs] using hK t ht⟩
  have hK0 : 0 ≤ K := le_trans (abs_nonneg _) (hK 0 ⟨le_rfl, zero_le_one⟩)
  set c := Real.sin δ with hc_def
  have hc : 0 < c := Real.sin_pos_of_pos_of_lt_pi hδ (by linarith)
  set R : ℝ := max 2 (2/(1-lam)) with hR_def
  have hl1 : (0:ℝ) < 1 - lam := by linarith
  have hlc : ((lam:ℂ)-1)^(2*N+1) ≠ 0 := pow_ne_zero _ (by
    rw [sub_ne_zero]; exact_mod_cast hlam1.ne)
  refine IsBigO.of_bound (K*(2/(c*(1-lam)))*‖((lam:ℂ)-1)^(2*N+1)‖) ?_
  have hev1 : ∀ᶠ w in logSector (π/2-δ), R/c ≤ Real.exp w.re :=
    ((tendsto_comap.mono_left inf_le_left : Tendsto (fun w : ℂ => Real.exp w.re)
      (logSector (π/2-δ)) atTop)).eventually_ge_atTop _
  have hev2 : ∀ᶠ w in logSector (π/2-δ), |w.im| ≤ π/2-δ := mem_inf_of_right (mem_principal_self _)
  filter_upwards [hev1, hev2] with w hw1 hw2
  set a := exp w with ha_def
  have hna : ‖a‖ = Real.exp w.re := Complex.norm_exp w
  have hre : a.re = Real.exp w.re * Real.cos w.im := Complex.exp_re w
  have hcos : c ≤ Real.cos w.im := by
    rw [← Real.cos_abs, hc_def, ← Real.cos_pi_div_two_sub]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith) hw2
  have hreA : c*‖a‖ ≤ a.re := by rw [hna, hre]; nlinarith [Real.exp_pos w.re]
  have hRa : R ≤ a.re := by
    rw [div_le_iff₀ hc] at hw1; rw [hna] at hreA; linarith
  have ha1 : 1 < a.re := lt_of_lt_of_le (by norm_num) ((le_max_left _ _).trans hRa)
  have ha2 : 2 ≤ a.re*(1-lam) := by
    have : 2/(1-lam) ≤ a.re := (le_max_right _ _).trans hRa
    rwa [div_le_iff₀ hl1] at this
  have ha0 : a ≠ 0 := Complex.exp_ne_zero w
  set E := exp (a*(w+Real.log lam) - lam*a) with hE
  have hw' : exp (w + (Real.log lam : ℂ)) = a * lam := by
    rw [Complex.exp_add, ← ofReal_exp, Real.exp_log hlam]
  have hf : lowerIncGammaOnLog a (w+Real.log lam) = E * ∫ t in (0:ℝ)..1, igAsy_g lam a t := by
    unfold lowerIncGammaOnLog
    rw [hw', scIncGamma_integral (by linarith)]
    have hG := Complex.Gamma_ne_zero_of_re_pos (by linarith : 0 < a.re)
    rw [show Gamma a * exp (a*(w+Real.log lam)) * (1/Gamma a * ∫ t in (0:ℝ)..1,
        (t:ℂ)^(a-1) * exp (-(a*lam)*t)) = exp (a*(w+Real.log lam)) * ∫ t in (0:ℝ)..1,
        (t:ℂ)^(a-1) * exp (-(a*lam)*t) by field_simp]
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [igAsy_g, hE]
    rw [mul_left_comm, ← Complex.exp_add, mul_left_comm (exp _), ← Complex.exp_add]
    congr 2
    ring
  have hφ : ∀ k : ℕ, (exp (a*(w+Real.log lam)-lam*a-(k+1 : ℂ)*w)/(lam-1 : ℂ)^(2*k+1)) •
      (-(-1 : ℂ)^k*(incGammaLambdaPolynomial k).eval (lam : ℂ)) =
      E * ((-1)^k/a^(k+1) * (igAsy_W k lam 1 : ℂ)) := by
    intro k
    have hak : exp (-(k+1 : ℂ)*w) = (a^(k+1))⁻¹ := by
      rw [ha_def, ← Complex.exp_nat_mul, ← Complex.exp_neg]; push_cast; ring_nf
    have hl' : (1:ℂ) - lam ≠ 0 := by rw [sub_ne_zero]; exact_mod_cast hlam1.ne'
    rw [smul_eq_mul, show a*(w+Real.log lam)-lam*a-(k+1 : ℂ)*w = (a*(w+Real.log lam)-lam*a) +
      (-(k+1 : ℂ)*w) by ring, Complex.exp_add, ← hE, hak, igAsy_b_eval]
    simp only [igAsy_W, mul_one]
    push_cast
    rw [show ((lam:ℂ)-1)^(2*k+1) = -((1-lam)^(2*k+1)) by
      rw [show (lam:ℂ)-1 = -(1-lam) by ring, Odd.neg_pow ⟨k, rfl⟩]]
    field_simp
  have hφN : exp (a*(w+Real.log lam)-lam*a-(N+1 : ℂ)*w)/(lam-1 : ℂ)^(2*N+1) =
      E/(a^(N+1)*((lam:ℂ)-1)^(2*N+1)) := by
    have hak : exp (-(N+1 : ℂ)*w) = (a^(N+1))⁻¹ := by
      rw [ha_def, ← Complex.exp_nat_mul, ← Complex.exp_neg]; push_cast; ring_nf
    rw [show a*(w+Real.log lam)-lam*a-(N+1 : ℂ)*w = (a*(w+Real.log lam)-lam*a) +
      (-(N+1 : ℂ)*w) by ring, Complex.exp_add, ← hE, hak]
    field_simp
  simp only [hf, hφ, hφN]
  rw [← Finset.mul_sum, ← mul_sub, igAsy_iterC hlam1 ha1 N, add_sub_cancel_left]
  have hI := igAsy_norm_integral_le hlam1 ha1 ha2 hK
  have hapos : 0 < ‖a‖ := norm_pos_iff.mpr ha0
  simp only [norm_pow, norm_mul, norm_div, norm_neg, norm_one, one_pow]
  have hb : K * (2/(a.re*(1-lam))) ≤ K * (2/(c*(1-lam)))/‖a‖ := by
    have : 2/(a.re*(1-lam)) ≤ 2/(c*(1-lam))/‖a‖ := by
      rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
    rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_left this hK0
  calc ‖E‖ * (1/‖a‖^N * ‖∫ t in (0:ℝ)..1, igAsy_g lam a t * igAsy_v N (lam*t)‖)
      ≤ ‖E‖ * (1/‖a‖^N * (K * (2/(c*(1-lam)))/‖a‖)) := by gcongr; exact hI.trans hb
    _ = K*(2/(c*(1-lam)))*‖(lam:ℂ)-1‖^(2*N+1) * (‖E‖/(‖a‖^(N+1)*‖(lam:ℂ)-1‖^(2*N+1))) := by
        have : ‖(lam:ℂ)-1‖^(2*N+1) ≠ 0 := by rw [← norm_pow]; exact norm_ne_zero_iff.mpr hlc
        field_simp
        ring

/-- Identity under the stated parameter and domain assumptions: `HasAsymptoticExpansion (logSector
(3*π/2-δ)) (fun k w => exp (exp w*(w+Real.log lam)-lam*exp w-(k+1 : ℂ)*w)/(lam-1 : ℂ)^(2*k+1))
(fun k => (-1 : ℂ)^k*(incGammaLambdaPolynomial k).eval (lam : ℂ)) (fun w => upperIncGammaOnLog
(exp w) (w+Real.log lam))`. -/
@[dlmf 8.11.E7]
theorem upperIncGamma_fixed_ratio_asymptotic {lam : ℝ} (hlam : 1 < lam) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 3*π/2) :
    HasAsymptoticExpansion (logSector (3*π/2-δ)) (fun k w => exp (exp w*(w+Real.log lam)-lam*exp w-(k+1 : ℂ)*w)/(lam-1 : ℂ)^(2*k+1)) (fun k => (-1 : ℂ)^k*(incGammaLambdaPolynomial k).eval (lam : ℂ)) (fun w => upperIncGammaOnLog (exp w) (w+Real.log lam)) := by
  sorry

/-- The negative-parameter continuation stated after DLMF 8.11.9. -/
@[dlmf 8.11.E7]
theorem upperIncGamma_negative_parameter_ratio_asymptotic {lam : ℝ} (hlam : lam < 0) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 3*π/2-arg ((-lam+Real.log (-lam) : ℝ)+π*I)) :
    HasAsymptoticExpansion (logSector (3*π/2-arg ((-lam+Real.log (-lam) : ℝ)+π*I)-δ)) (fun k w => exp (-exp w*(w+Real.log (-lam))+lam*exp w-(k+1 : ℂ)*w)/(1-lam : ℂ)^(2*k+1)) (fun k => (incGammaLambdaPolynomial k).eval (lam : ℂ)) (fun w => upperIncGammaOnLog (-exp w) (w+Real.log (-lam))) := by
  sorry

/-- Estimate under the stated parameter and domain assumptions: `∃ c : ℕ → ℂ, (∀ n < 6, c
n=([Real.sqrt (π/2),-1/3,Real.sqrt (2*π)/24,-4/135,Real.sqrt (2*π)/576,8/2835] : List ℂ)[n]!)
∧ ∀ δ : ℝ, 0 < δ → δ < 2*π → HasAsymptoticExpansion (logSector (2*π-δ)) (fun n w => exp ((exp
w-1)*w-exp w+(1-(n : ℂ))*w/2)) c (fun w => upperIncGammaOnLog (exp w) w)`. -/
@[dlmf 8.11.E12]
theorem upperIncGamma_diagonal_asymptotic  :
    ∃ c : ℕ → ℂ, (∀ n < 6, c n=([Real.sqrt (π/2),-1/3,Real.sqrt (2*π)/24,-4/135,Real.sqrt (2*π)/576,8/2835] : List ℂ)[n]!) ∧ ∀ δ : ℝ, 0 < δ → δ < 2*π → HasAsymptoticExpansion (logSector (2*π-δ)) (fun n w => exp ((exp w-1)*w-exp w+(1-(n : ℂ))*w/2)) c (fun w => upperIncGammaOnLog (exp w) w) := by
  sorry

/-- Real polynomials `p_k` with `b_k = X p_k` for `k ≥ 1` (helper for 8.11.18). -/
noncomputable def igAsy_poly : ℕ → Polynomial ℝ
  | 0 => 1
  | k+1 => (1 - Polynomial.X) * (igAsy_poly k + Polynomial.X * (igAsy_poly k).derivative) +
      Polynomial.C (2*(k:ℝ)+1) * Polynomial.X * igAsy_poly k

/-- The rational functions `h_k(y) = p_k(y)/(1-y)^{2k}` of the integration by parts. -/
noncomputable def igAsy_h (k : ℕ) (y : ℝ) : ℝ := (igAsy_poly k).eval y / (1-y)^(2*k)

/-- The recursion of `igAsy_poly`, evaluated. -/
theorem igAsy_poly_eval_succ (k : ℕ) (y : ℝ) :
    (igAsy_poly (k+1)).eval y = (1-y)*((igAsy_poly k).eval y + y*(igAsy_poly k).derivative.eval y) +
      (2*k+1)*y*(igAsy_poly k).eval y := by
  simp [igAsy_poly]

/-- The derivative step of the integration by parts. -/
theorem igAsy_hasDerivAt_V (k : ℕ) {x s : ℝ} (hs : 1 - x*s ≠ 0) :
    HasDerivAt (fun t : ℝ => t*(igAsy_poly k).eval (x*t)/(1-x*t)^(2*k+1)) (igAsy_h (k+1) (x*s)) s := by
  have hP := ((igAsy_poly k).hasDerivAt (x*s)).comp s ((hasDerivAt_id s).const_mul x)
  have hD := (((hasDerivAt_id s).const_mul x).const_sub 1).pow (2*k+1)
  have h := ((hasDerivAt_id s).mul hP).div hD (pow_ne_zero _ hs)
  convert h using 1
  · funext t; simp [Function.comp_def]
  rw [igAsy_h, igAsy_poly_eval_succ]
  simp only [id, mul_one, Function.comp_apply, Pi.pow_apply, Pi.mul_apply]
  rw [show 2*k+1-1 = 2*k by omega, show 2*(k+1) = 2*k+2 by ring]
  field_simp
  push_cast
  ring

/-- `h_0 = 1`. -/
theorem igAsy_h_zero (y : ℝ) : igAsy_h 0 y = 1 := by simp [igAsy_h, igAsy_poly]

/-- The Laplace-type integrand `s^n e^{n x (1-s)}` with `n = m+1`. -/
noncomputable def igAsy_F (m : ℕ) (x s : ℝ) : ℝ := s^(m+1) * Real.exp ((m+1)*x*(1-s))

/-- Derivative of the integrand `igAsy_F`. -/
theorem igAsy_hasDerivAt_F (m : ℕ) (x s : ℝ) :
    HasDerivAt (igAsy_F m x) ((m+1)*(1-x*s)*s^m*Real.exp ((m+1)*x*(1-s))) s := by
  have h1 := hasDerivAt_pow (m+1) s
  have h2 := (Real.hasDerivAt_exp ((m+1)*x*(1-s))).comp s
    (((hasDerivAt_id s).const_sub 1).const_mul ((m+1)*x))
  have h := h1.mul h2
  unfold igAsy_F
  convert h using 1
  · funext t; simp [Function.comp_def]
  push_cast
  simp only [id, Function.comp_apply]
  ring

/-- `s ↦ h_k(x s)` is continuous on `[0,1]` for `x < 1`. -/
theorem igAsy_continuousOn_h (k : ℕ) {x : ℝ} (hx : x < 1) :
    ContinuousOn (fun s : ℝ => igAsy_h k (x*s)) (uIcc 0 1) := by
  unfold igAsy_h
  refine ContinuousOn.div (by fun_prop) (by fun_prop) fun s hs => ?_
  rw [uIcc_of_le zero_le_one] at hs
  exact pow_ne_zero _ (igAsy_one_sub_mul_pos hx hs).ne'

/-- One integration by parts. -/
theorem igAsy_ibp (m k : ℕ) {x : ℝ} (hx : x < 1) :
    ∫ s in (0:ℝ)..1, igAsy_F m x s * igAsy_h k (x*s) =
      igAsy_h k x/((m+1)*(1-x)) - 1/(m+1) * ∫ s in (0:ℝ)..1, igAsy_F m x s * igAsy_h (k+1) (x*s) := by
  have hm : (m:ℝ)+1 ≠ 0 := by positivity
  have hx1 : 1 - x ≠ 0 := by linarith
  have hu : ∀ s ∈ uIcc (0:ℝ) 1, HasDerivAt (igAsy_F m x)
      ((m+1)*(1-x*s)*s^m*Real.exp ((m+1)*x*(1-s))) s := fun s _ => igAsy_hasDerivAt_F m x s
  have hv : ∀ s ∈ uIcc (0:ℝ) 1, HasDerivAt
      (fun t : ℝ => t*(igAsy_poly k).eval (x*t)/(1-x*t)^(2*k+1)/(m+1))
      (igAsy_h (k+1) (x*s)/(m+1)) s := by
    intro s hs
    rw [uIcc_of_le zero_le_one] at hs
    exact (igAsy_hasDerivAt_V k (igAsy_one_sub_mul_pos hx hs).ne').div_const _
  have hu' : IntervalIntegrable (fun s : ℝ => (m+1)*(1-x*s)*s^m*Real.exp ((m+1)*x*(1-s)))
      volume 0 1 := (by fun_prop : Continuous _).intervalIntegrable _ _
  have hv' : IntervalIntegrable (fun s : ℝ => igAsy_h (k+1) (x*s)/(m+1)) volume 0 1 :=
    ((igAsy_continuousOn_h (k+1) hx).div_const _).intervalIntegrable
  have H := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu' hv'
  have hcongr : ∫ s in (0:ℝ)..1, (m+1)*(1-x*s)*s^m*Real.exp ((m+1)*x*(1-s)) *
      ((s*(igAsy_poly k).eval (x*s)/(1-x*s)^(2*k+1))/(m+1)) =
      ∫ s in (0:ℝ)..1, igAsy_F m x s * igAsy_h k (x*s) := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le zero_le_one] at hs
    have h1 := (igAsy_one_sub_mul_pos hx hs).ne'
    simp only [igAsy_F, igAsy_h]
    field_simp
    ring
  rw [hcongr] at H
  have hdiv : ∫ s in (0:ℝ)..1, igAsy_F m x s * (igAsy_h (k+1) (x*s)/(m+1)) =
      (∫ s in (0:ℝ)..1, igAsy_F m x s * igAsy_h (k+1) (x*s))/(m+1) := by
    rw [← intervalIntegral.integral_div]; congr 1; funext s; ring
  rw [hdiv] at H
  simp only [igAsy_F, igAsy_h, one_pow, one_mul, sub_self, mul_zero, Real.exp_zero, zero_mul,
    mul_one, ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false, not_false_eq_true, zero_pow,
    zero_div, sub_zero] at H ⊢
  rw [pow_succ] at H
  field_simp at H ⊢
  linear_combination H

/-- Iterated integration by parts. -/
theorem igAsy_iter (m : ℕ) {x : ℝ} (hx : x < 1) (N : ℕ) :
    ∫ s in (0:ℝ)..1, igAsy_F m x s =
      ∑ k ∈ Finset.range N, (-1)^k/((m:ℝ)+1)^(k+1) * (igAsy_h k x/(1-x)) +
        (-1)^N/((m:ℝ)+1)^N * ∫ s in (0:ℝ)..1, igAsy_F m x s * igAsy_h N (x*s) := by
  induction N with
  | zero => simp [igAsy_h_zero]
  | succ N ih =>
    rw [ih, igAsy_ibp m N hx, Finset.sum_range_succ]
    have hm : (m:ℝ)+1 ≠ 0 := by positivity
    have hx1 : 1 - x ≠ 0 := by linarith
    field_simp
    ring_nf

/-- The integrand is nonnegative on `[0, ∞)`. -/
theorem igAsy_F_nonneg (m : ℕ) (x : ℝ) {s : ℝ} (hs : 0 ≤ s) : 0 ≤ igAsy_F m x s := by
  unfold igAsy_F; positivity

/-- Exponential majorant `s^n e^{n x(1-s)} ≤ e^{-n(1-x)(1-s)}`. -/
theorem igAsy_F_le (m : ℕ) (x : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    igAsy_F m x s ≤ Real.exp (-((m+1)*(1-x))*(1-s)) := by
  unfold igAsy_F
  have h1 : s ≤ Real.exp (s-1) := by linarith [Real.add_one_le_exp (s-1)]
  have h2 : s^(m+1) ≤ Real.exp ((m+1)*(s-1)) := by
    calc s^(m+1) ≤ (Real.exp (s-1))^(m+1) := pow_le_pow_left₀ hs h1 _
      _ = Real.exp ((m+1)*(s-1)) := by rw [← Real.exp_nat_mul]; push_cast; ring_nf
  calc s^(m+1) * Real.exp ((m+1)*x*(1-s)) ≤ Real.exp ((m+1)*(s-1)) * Real.exp ((m+1)*x*(1-s)) :=
        mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
    _ = Real.exp (-((m+1)*(1-x))*(1-s)) := by rw [← Real.exp_add]; ring_nf

/-- `∫₀¹ s^n e^{n x (1-s)} ds ≤ 1/(n(1-x))` for `x < 1`. -/
theorem igAsy_integral_F_le (m : ℕ) {x : ℝ} (hx : x < 1) :
    ∫ s in (0:ℝ)..1, igAsy_F m x s ≤ 1/((m+1)*(1-x)) := by
  set c : ℝ := (m+1)*(1-x) with hc
  have hc0 : 0 < c := by rw [hc]; have : 0 < 1-x := by linarith
                         positivity
  have hle : ∫ s in (0:ℝ)..1, igAsy_F m x s ≤ ∫ s in (0:ℝ)..1, Real.exp (-c*(1-s)) := by
    refine intervalIntegral.integral_mono_on zero_le_one
      ((by unfold igAsy_F; fun_prop : Continuous (igAsy_F m x)).intervalIntegrable _ _)
      ((by fun_prop : Continuous fun s : ℝ => Real.exp (-c*(1-s))).intervalIntegrable _ _) ?_
    intro s hs
    exact igAsy_F_le m x hs.1
  have hval : ∫ s in (0:ℝ)..1, Real.exp (-c*(1-s)) = (1 - Real.exp (-c))/c := by
    have hd : ∀ s ∈ uIcc (0:ℝ) 1, HasDerivAt (fun s : ℝ => Real.exp (-c*(1-s))/c)
        (Real.exp (-c*(1-s))) s := by
      intro s _
      have := ((Real.hasDerivAt_exp (-c*(1-s))).comp s
        (((hasDerivAt_id s).const_sub 1).const_mul (-c))).div_const c
      convert this using 1
      simp only [id, Function.comp_apply]
      field_simp
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
      ((by fun_prop : Continuous fun s : ℝ => Real.exp (-c*(1-s))).intervalIntegrable _ _)]
    simp only [sub_self, mul_zero, Real.exp_zero, sub_zero, mul_one]
    ring
  rw [hval] at hle
  refine hle.trans ?_
  rw [div_le_div_iff_of_pos_right hc0]
  linarith [Real.exp_pos (-c)]

/-- The absolute value of a real polynomial is bounded by `A (1+|y|)^{deg}`. -/
theorem igAsy_abs_eval_le (p : Polynomial ℝ) (y : ℝ) :
    |p.eval y| ≤ (∑ i ∈ Finset.range (p.natDegree+1), |p.coeff i|) * (1+|y|)^p.natDegree := by
  rw [Polynomial.eval_eq_sum_range, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => ?_)
  rw [abs_mul, abs_pow]
  have hi' : i ≤ p.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  gcongr
  calc |y|^i ≤ (1+|y|)^i := by gcongr; linarith
    _ ≤ (1+|y|)^p.natDegree := pow_le_pow_right₀ (by linarith [abs_nonneg y]) hi'

/-- `deg p_k ≤ 2k`. -/
theorem igAsy_poly_natDegree_le (k : ℕ) : (igAsy_poly k).natDegree ≤ 2*k := by
  induction k with
  | zero => simp [igAsy_poly]
  | succ k ih =>
    rw [igAsy_poly]
    have hd := (igAsy_poly k).natDegree_derivative_le
    have h1 : (1 - Polynomial.X : Polynomial ℝ).natDegree ≤ 1 := by
      refine (Polynomial.natDegree_sub_le _ _).trans ?_; simp
    have h2 : (igAsy_poly k + Polynomial.X * (igAsy_poly k).derivative).natDegree ≤ 2*k+1 := by
      refine (Polynomial.natDegree_add_le _ _).trans (max_le (by omega) ?_)
      refine Polynomial.natDegree_mul_le.trans ?_
      have := Polynomial.natDegree_X_le (R := ℝ)
      omega
    refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
    · refine Polynomial.natDegree_mul_le.trans ?_; omega
    · refine Polynomial.natDegree_mul_le.trans ?_
      have h3 : (Polynomial.C (2*(k:ℝ)+1) * Polynomial.X).natDegree ≤ 1 := by
        refine Polynomial.natDegree_mul_le.trans ?_
        have := Polynomial.natDegree_X_le (R := ℝ)
        simp only [Polynomial.natDegree_C]; omega
      omega

/-- A uniform bound on `h_N` on `(-∞, max 0 (1-δ)]`. -/
theorem igAsy_h_bound (N : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ K, 0 ≤ K ∧ ∀ y : ℝ, y ≤ max 0 (1-δ) → |igAsy_h N y| ≤ K := by
  set c : ℝ := min 1 δ / 2 with hc
  have hc0 : 0 < c := by rw [hc]; positivity
  set A := ∑ i ∈ Finset.range ((igAsy_poly N).natDegree+1), |(igAsy_poly N).coeff i|
  have hA : 0 ≤ A := Finset.sum_nonneg fun i _ => abs_nonneg _
  refine ⟨A/c^(2*N), by positivity, fun y hy => ?_⟩
  have hsep : c*(1+|y|) ≤ 1-y := by
    rcases le_or_gt y 0 with h | h
    · rw [abs_of_nonpos h]
      have : c ≤ 1 := by rw [hc]; linarith [min_le_left 1 δ]
      nlinarith
    · rw [abs_of_pos h]
      have hy' : y ≤ 1-δ := by
        rcases le_max_iff.mp hy with h' | h'
        · linarith
        · exact h'
      have : c ≤ δ/2 := by rw [hc]; linarith [min_le_right 1 δ]
      nlinarith
  have hy1 : 0 < 1+|y| := by positivity
  have hpos : 0 < 1-y := lt_of_lt_of_le (by positivity) hsep
  unfold igAsy_h
  rw [abs_div, abs_pow, abs_of_pos hpos, div_le_div_iff₀ (by positivity) (by positivity)]
  have hp := igAsy_abs_eval_le (igAsy_poly N) y
  have hd := igAsy_poly_natDegree_le N
  calc |(igAsy_poly N).eval y| * c^(2*N) ≤ A*(1+|y|)^(igAsy_poly N).natDegree * c^(2*N) := by
        gcongr
    _ ≤ A*(1+|y|)^(2*N) * c^(2*N) := by
        gcongr
        · linarith [abs_nonneg y]
    _ = A * (c*(1+|y|))^(2*N) := by rw [mul_pow]; ring
    _ ≤ A * (1-y)^(2*N) := by gcongr

/-- `γ(n+1, nx)/((nx)^n e^{-nx}) = n x ∫₀¹ s^n e^{n x (1-s)} ds` with `n = m+1`. -/
theorem igAsy_lowerIncGamma_ratio_eq (m : ℕ) (x : ℝ) :
    lowerIncGamma (((m+1:ℕ):ℂ)+1) (((m+1:ℕ):ℂ)*x)/((((m+1:ℕ):ℂ)*x)^(m+1)*exp (-((m+1:ℕ):ℂ)*x)) =
      (((m+1)*x * ∫ s in (0:ℝ)..1, igAsy_F m x s : ℝ) : ℂ) := by
  push_cast
  by_cases hx : x = 0
  · subst hx; simp
  set z : ℂ := ((m:ℂ)+1)*x with hz
  have hz0 : z ≠ 0 := mul_ne_zero (by exact_mod_cast Nat.succ_ne_zero m) (by exact_mod_cast hx)
  have hnp := natCast_add_one_ne_neg_nat (m+1)
  push_cast at hnp
  have hre : 0 < ((m:ℂ)+1+1).re := by simp; positivity
  have hL : lowerIncGamma ((m:ℂ)+1+1) z =
      z^(m+2) * ∫ t in (0:ℝ)..1, (t:ℂ)^(m+1) * exp (-z*t) := by
    rw [lowerIncGamma_eq_regularized hnp, show (m:ℂ)+1+1+1 = 1 + ((m:ℂ)+1+1) by ring,
      ← (scIncGamma_regularized_pair _ z).2,
      scIncGamma_integral hre z, show ((m:ℂ)+1+1) = ((m+2 : ℕ) : ℂ) by push_cast; ring, cpow_natCast,
      show ((m+2 : ℕ) : ℂ) - 1 = ((m+1 : ℕ) : ℂ) by push_cast; ring]
    simp only [cpow_natCast]
    have hG : Gamma ((m+2 : ℕ) : ℂ) ≠ 0 := Gamma_ne_zero (by
      intro k hk; exact hnp k (by rw [← hk]; push_cast; ring))
    field_simp
  rw [show (-((m:ℂ)+1)*x) = -z by rw [hz]; ring, hL]
  have hI : (∫ t in (0:ℝ)..1, (t:ℂ)^(m+1) * exp (-z*t)) * exp z =
      ((∫ s in (0:ℝ)..1, igAsy_F m x s : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_mul_const, ← intervalIntegral.integral_ofReal]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [igAsy_F, hz]
    push_cast
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    ring
  rw [← hI, Complex.exp_neg]
  field_simp
  ring

end DLMF.Confluent
end
