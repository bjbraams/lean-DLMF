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
# Large argument and large parameter expansions, DLMF §8.11

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
New theorem statements are initially admitted and are not completed proofs.

Proof methods (helper prefix `igAsy_`): 8.11.5 combines 8.11.4 with Binet's form of Stirling's
formula (`DLMF.Gamma.Gamma_eq_exp_binetExponent`, `DLMF.Gamma.norm_binetMu_le`); 8.11.6 and
8.11.18 (hence 8.11.17) use repeated integration by parts in `∫₀¹ t^{a-1} e^{λa(1-t)} dt`, whose
boundary terms produce the polynomials `b_k` of 8.11.9; 8.11.13 at `x = 1` uses the
finite-interval Laplace method of `ToMathlib/Analysis/Integral/Laplace.lean` and Stirling's
formula from Mathlib.
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

/-- upperIncGamma log asymptotic. -/
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

/-- lowerIncGamma large parameter hasSum. -/
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

/-- lowerIncGamma large parameter asymptotic. -/
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

/-- normIncGammaP large parameter equivalent. -/
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

/-- incGammaLambdaPolynomial initial. -/
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


/-- lowerIncGamma fixed ratio asymptotic. -/
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

/-- upperIncGamma fixed ratio asymptotic. -/
@[dlmf 8.11.E7]
theorem upperIncGamma_fixed_ratio_asymptotic {lam : ℝ} (hlam : 1 < lam) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 3*π/2) :
    HasAsymptoticExpansion (logSector (3*π/2-δ)) (fun k w => exp (exp w*(w+Real.log lam)-lam*exp w-(k+1 : ℂ)*w)/(lam-1 : ℂ)^(2*k+1)) (fun k => (-1 : ℂ)^k*(incGammaLambdaPolynomial k).eval (lam : ℂ)) (fun w => upperIncGammaOnLog (exp w) (w+Real.log lam)) := by
  sorry

/-- The negative-parameter continuation stated after DLMF 8.11.9. -/
@[dlmf 8.11.E7]
theorem upperIncGamma_negative_parameter_ratio_asymptotic {lam : ℝ} (hlam : lam < 0) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 3*π/2-arg ((-lam+Real.log (-lam) : ℝ)+π*I)) :
    HasAsymptoticExpansion (logSector (3*π/2-arg ((-lam+Real.log (-lam) : ℝ)+π*I)-δ)) (fun k w => exp (-exp w*(w+Real.log (-lam))+lam*exp w-(k+1 : ℂ)*w)/(1-lam : ℂ)^(2*k+1)) (fun k => (incGammaLambdaPolynomial k).eval (lam : ℂ)) (fun w => upperIncGammaOnLog (-exp w) (w+Real.log (-lam))) := by
  sorry

/-- upperIncGamma diagonal asymptotic. -/
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


/-- The identity 8.11.14 with `S_n` unfolded. -/
theorem igAsy_exp_identity (n : ℕ) (x : ℝ) :
    exp (n*x : ℂ)=expPartialSum n (n*x)+(n*x : ℂ)^n/n.factorial*
      (lowerIncGamma (n+1) (n*x)/((n*x : ℂ)^n*exp (-n*x : ℂ))) := by
  rw [show (-n*x : ℂ) = -(n*x : ℂ) by ring]
  set z : ℂ := (n*x : ℂ)
  have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  by_cases hz : z = 0
  · have h0 : lowerIncGamma (n+1) z = 0 := by
      rw [lowerIncGamma_eq_regularized (natCast_add_one_ne_neg_nat n), hz,
        zero_cpow (by exact_mod_cast n.succ_ne_zero), mul_zero, zero_mul]
    rw [h0, zero_div, mul_zero, add_zero, hz, Complex.exp_zero, expPartialSum,
      Finset.sum_eq_single 0]
    · simp
    · intro k _ hk; simp [hk]
    · simp
  · rw [lowerIncGamma_nat_succ_expPartialSum n hz, Complex.exp_neg]
    have he : exp z ≠ 0 := Complex.exp_ne_zero z
    have hzn : z^n ≠ 0 := pow_ne_zero _ hz
    field_simp
    ring

/-- `q(u) = -(log(1-u)+u)/u²`, extended by `1/2` at `0`. -/
noncomputable def igAsy_q (u : ℝ) : ℝ := if u = 0 then 1/2 else -(Real.log (1-u) + u)/u^2

/-- `|q(u) - 1/2| ≤ 2u` on `[0, 1/8]`. -/
theorem igAsy_q_sub_half {u : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ 1/8) : |igAsy_q u - 1/2| ≤ 2*u := by
  unfold igAsy_q
  split_ifs with h
  · simp [h]
  have hu' : 0 < u := lt_of_le_of_ne hu0 (Ne.symm h)
  have habs : |u| < 1 := by rw [abs_of_pos hu']; linarith
  have hl := Real.abs_log_sub_add_sum_range_le habs 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, abs_of_pos hu'] at hl
  norm_num at hl
  have h1 : u^3/(1-u) ≤ 2*u^3 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith [pow_pos hu' 3]
  have heq : -(Real.log (1-u) + u)/u^2 - 1/2 = -((u + u^2/2 + Real.log (1-u))/u^2) := by
    field_simp; ring
  rw [heq, abs_neg, abs_div, abs_of_pos (by positivity : (0:ℝ) < u^2), div_le_iff₀ (by positivity)]
  nlinarith

/-- The even integrand `(1-|t|)^k e^{k|t|}`. -/
noncomputable def igAsy_E (k : ℕ) (t : ℝ) : ℝ := (1-|t|)^k * Real.exp (k*|t|)

/-- The Gaussian form `e^{-k t² q(|t|)} = (1-|t|)^k e^{k|t|}`. -/
theorem igAsy_exp_q_eq (k : ℕ) {t : ℝ} (ht : |t| < 1) :
    exp (-((k:ℝ):ℂ) * (t:ℂ)^2 * ((igAsy_q |t| : ℝ) : ℂ)) = (igAsy_E k t : ℂ) := by
  unfold igAsy_E igAsy_q
  split_ifs with h
  · have : t = 0 := abs_eq_zero.mp h
    subst this; simp
  · have hpos : 0 < 1 - |t| := by linarith
    have hr : t^2 * (-(Real.log (1-|t|) + |t|)/|t|^2) = -(Real.log (1-|t|) + |t|) := by
      have : |t|^2 ≠ 0 := by positivity
      rw [← sq_abs t]; field_simp
    have ht2 : -((k:ℝ):ℂ) * (t:ℂ)^2 * ((-(Real.log (1-|t|) + |t|)/|t|^2 : ℝ) : ℂ) =
        ((k * Real.log (1-|t|) + k*|t| : ℝ) : ℂ) := by
      rw [mul_assoc, show (t:ℂ)^2 = ((t^2:ℝ):ℂ) by push_cast; ring, ← ofReal_mul, hr]
      push_cast; ring
    rw [ht2, ← ofReal_exp]
    congr 1
    rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log hpos]

/-- Laplace's method at the endpoint maximum: `√k ∫_{-1/8}^{1/8} E_k → √(2π)`. -/
theorem igAsy_tendsto_sqrt_mul_integral_E :
    Tendsto (fun k : ℕ => Real.sqrt k * ∫ t in Icc (-(1/8:ℝ)) (1/8), igAsy_E k t) atTop
      (𝓝 (Real.sqrt (2*π))) := by
  have hqm : Measurable igAsy_q := by
    unfold igAsy_q
    exact Measurable.ite (measurableSet_singleton 0) measurable_const (by fun_prop)
  have H := (Complex.tendstoUniformlyOn_sqrt_mul_integral_laplace_Icc (S := (univ : Set Unit))
    (A := fun _ _ => (1:ℂ)) (q := fun _ t => ((igAsy_q |t| : ℝ) : ℂ)) (c := 1/4) (L := 0) (M := 1)
    (B := 2) (δ := 1/8) (by norm_num) (by norm_num) (fun _ _ => measurable_const)
    (fun _ _ => (Complex.measurable_ofReal.comp (hqm.comp continuous_abs.measurable)))
    (fun _ _ t ht => ?_) (fun _ _ => by simp) (fun _ _ t _ => by simp)
    (fun _ _ t ht => ?_)).tendsto_at (mem_univ ())
  rotate_left
  · have h := igAsy_q_sub_half (abs_nonneg t) (abs_le.mpr ⟨by linarith [ht.1], ht.2⟩)
    simp only [ofReal_re]
    have := (abs_le.mp h).1
    have : |t| ≤ 1/8 := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
    linarith
  · have h := igAsy_q_sub_half (abs_nonneg t) (abs_le.mpr ⟨by linarith [ht.1], ht.2⟩)
    rw [abs_zero, show igAsy_q 0 = 1/2 by simp [igAsy_q], ← ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs]
    exact h
  have hq0 : igAsy_q |0| = 1/2 := by simp [igAsy_q]
  simp only [hq0, one_mul] at H
  have hC : ((Real.pi : ℂ) / ((1/2 : ℝ) : ℂ)) ^ (1/2 : ℂ) = (Real.sqrt (2*π) : ℂ) := by
    rw [show ((Real.pi : ℂ) / ((1/2 : ℝ) : ℂ)) = ((2*π : ℝ) : ℂ) by push_cast; ring,
      show (1/2 : ℂ) = ((1/2 : ℝ) : ℂ) by push_cast; ring, ← ofReal_cpow (by positivity),
      Real.sqrt_eq_rpow]
  rw [hC] at H
  have H2 := H.comp tendsto_natCast_atTop_atTop
  have hE : ∀ k : ℕ, ((Real.sqrt k * ∫ t in Icc (-(1/8:ℝ)) (1/8), igAsy_E k t : ℝ) : ℂ) =
      (Real.sqrt k : ℂ) * ∫ t in Icc (-(1/8:ℝ)) (1/8),
        exp (-((k:ℝ):ℂ) * (t:ℂ)^2 * ((igAsy_q |t| : ℝ) : ℂ)) := by
    intro k
    rw [ofReal_mul, ← integral_complex_ofReal]
    congr 1
    refine setIntegral_congr_fun measurableSet_Icc fun t ht => ?_
    rw [igAsy_exp_q_eq k (by rw [abs_lt]; constructor <;> linarith [ht.1, ht.2])]
  have H3 : Tendsto (fun k : ℕ => ((Real.sqrt k * ∫ t in Icc (-(1/8:ℝ)) (1/8), igAsy_E k t : ℝ) : ℂ))
      atTop (𝓝 (Real.sqrt (2*π) : ℂ)) := by
    simp only [hE]; exact H2
  have H4 := (Complex.continuous_re.tendsto _).comp H3
  simp only [Function.comp_def, ofReal_re] at H4
  exact H4


/-- Folding the even integrand: `∫_{-1/8}^{1/8} E_{m+1} = 2 ∫_{7/8}^1 s^{m+1} e^{(m+1)(1-s)} ds`. -/
theorem igAsy_integral_E_eq (m : ℕ) :
    ∫ t in Icc (-(1/8:ℝ)) (1/8), igAsy_E (m+1) t = 2 * ∫ s in (7/8:ℝ)..1, igAsy_F m 1 s := by
  have hc : Continuous (igAsy_E (m+1)) := by unfold igAsy_E; fun_prop
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num),
    ← intervalIntegral.integral_add_adjacent_intervals (b := 0) (hc.intervalIntegrable _ _)
      (hc.intervalIntegrable _ _)]
  have h1 : ∫ t in (-(1/8:ℝ))..0, igAsy_E (m+1) t = ∫ t in (0:ℝ)..(1/8), igAsy_E (m+1) t := by
    have := intervalIntegral.integral_comp_neg (a := 0) (b := 1/8) (igAsy_E (m+1))
    rw [neg_zero] at this
    rw [← this]
    congr 1; funext t; simp [igAsy_E]
  have h2 : ∫ t in (0:ℝ)..(1/8), igAsy_E (m+1) t = ∫ s in (7/8:ℝ)..1, igAsy_F m 1 s := by
    have := intervalIntegral.integral_comp_sub_left (a := 0) (b := 1/8) (igAsy_F m 1) 1
    rw [show (1:ℝ) - 1/8 = 7/8 by norm_num, sub_zero] at this
    rw [← this]
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le (by norm_num)] at ht
    simp only [igAsy_E, igAsy_F, abs_of_nonneg ht.1]
    push_cast
    ring_nf
  rw [h1, h2]; ring

/-- `s^n e^{n(1-s)} ≤ e^{-n(1-s)²/2}` on `[0,1]`. -/
theorem igAsy_F_one_le (m : ℕ) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    igAsy_F m 1 s ≤ Real.exp (-((m+1)*(1-s)^2/2)) := by
  rcases hs0.eq_or_lt with h | h
  · subst h; simp [igAsy_F]; positivity
  have hu : |1-s| < 1 := by rw [abs_lt]; constructor <;> linarith
  have hS := Real.hasSum_pow_div_log_of_abs_lt_one hu
  have hle := sum_le_hasSum (Finset.range 2) (fun i _ => by
    have : 0 ≤ 1-s := by linarith
    positivity) hS
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, sub_sub_cancel] at hle
  norm_num at hle
  unfold igAsy_F
  rw [← Real.exp_log (pow_pos h (m+1)), ← Real.exp_add, Real.exp_le_exp, Real.log_pow]
  push_cast
  nlinarith [show (0:ℝ) ≤ (m:ℝ)+1 by positivity]

/-- The tail `√n ∫₀^{7/8} s^n e^{n(1-s)} ds → 0`. -/
theorem igAsy_tendsto_tail :
    Tendsto (fun m : ℕ => Real.sqrt ((m:ℝ)+1) * ∫ s in (0:ℝ)..(7/8), igAsy_F m 1 s) atTop (𝓝 0) := by
  have hb : ∀ m : ℕ, ∫ s in (0:ℝ)..(7/8), igAsy_F m 1 s ≤ 7/8 * Real.exp (-(((m:ℝ)+1)/128)) := by
    intro m
    have := intervalIntegral.integral_mono_on (g := fun _ => Real.exp (-(((m:ℝ)+1)/128)))
      (by norm_num : (0:ℝ) ≤ 7/8)
      ((by unfold igAsy_F; fun_prop : Continuous (igAsy_F m 1)).intervalIntegrable _ _)
      (continuous_const.intervalIntegrable (μ := volume) _ _) (fun s hs => by
        refine (igAsy_F_one_le m hs.1 (by linarith [hs.2])).trans ?_
        rw [Real.exp_le_exp]
        have : 1/64 ≤ (1-s)^2 := by nlinarith [hs.2]
        nlinarith [show (0:ℝ) ≤ (m:ℝ)+1 by positivity])
    simpa using this
  have hnn : ∀ m : ℕ, 0 ≤ ∫ s in (0:ℝ)..(7/8), igAsy_F m 1 s := fun m =>
    intervalIntegral.integral_nonneg (by norm_num) fun s hs => igAsy_F_nonneg m 1 hs.1
  have hlim : Tendsto (fun m : ℕ => 7/8 * 128 * ((((m:ℝ)+1)/128)^1 * Real.exp (-(((m:ℝ)+1)/128))))
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun m : ℕ => ((m:ℝ)+1)/128) atTop atTop :=
      (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds).atTop_div_const (by norm_num)
    have := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp h1).const_mul (7/8*128)
    simpa using this
  refine squeeze_zero (fun m => mul_nonneg (Real.sqrt_nonneg _) (hnn m)) (fun m => ?_) hlim
  have hm : (1:ℝ) ≤ (m:ℝ)+1 := by simp
  have hs : Real.sqrt ((m:ℝ)+1) ≤ (m:ℝ)+1 := by
    rw [Real.sqrt_le_left (by positivity)]; nlinarith
  calc Real.sqrt ((m:ℝ)+1) * ∫ s in (0:ℝ)..(7/8), igAsy_F m 1 s
      ≤ ((m:ℝ)+1) * (7/8 * Real.exp (-(((m:ℝ)+1)/128))) :=
        mul_le_mul hs (hb m) (hnn m) (by positivity)
    _ = 7/8 * 128 * ((((m:ℝ)+1)/128)^1 * Real.exp (-(((m:ℝ)+1)/128))) := by ring

/-- `√n ∫₀¹ s^n e^{n(1-s)} ds → √(π/2)`, written as `√(2π)/2`. -/
theorem igAsy_tendsto_sqrt_J :
    Tendsto (fun m : ℕ => Real.sqrt ((m:ℝ)+1) * ∫ s in (0:ℝ)..1, igAsy_F m 1 s) atTop
      (𝓝 (Real.sqrt (2*π)/2)) := by
  have hE := (igAsy_tendsto_sqrt_mul_integral_E.comp (tendsto_add_atTop_nat 1)).div_const 2
  have hc : Continuous (igAsy_F 0 1) := by unfold igAsy_F; fun_prop
  have H := igAsy_tendsto_tail.add hE
  rw [zero_add] at H
  refine H.congr fun m => ?_
  have hcF : Continuous (igAsy_F m 1) := by unfold igAsy_F; fun_prop
  have hsplit : ∫ s in (0:ℝ)..1, igAsy_F m 1 s =
      (∫ s in (0:ℝ)..(7/8), igAsy_F m 1 s) + ∫ s in (7/8:ℝ)..1, igAsy_F m 1 s :=
    (intervalIntegral.integral_add_adjacent_intervals (hcF.intervalIntegrable _ _)
      (hcF.intervalIntegrable _ _)).symm
  simp only [Function.comp_apply, igAsy_integral_E_eq]
  rw [hsplit]
  push_cast
  ring


/-- `e_n(nx)/e^{nx} = 1 - (nx)^n/n! · S_n(x)/e^{nx}` with the integral form of `S_n`. -/
theorem igAsy_ratio_eq (m : ℕ) (x : ℝ) :
    expPartialSum (m+1) (((m+1:ℕ):ℂ)*x)/exp (((m+1:ℕ):ℂ)*x) =
      ((1 - ((m+1)*x)^(m+1)/((m+1).factorial) * ((m+1)*x*∫ s in (0:ℝ)..1, igAsy_F m x s) /
        Real.exp ((m+1)*x) : ℝ) : ℂ) := by
  have hI := igAsy_exp_identity (m+1) x
  rw [igAsy_lowerIncGamma_ratio_eq] at hI
  have he : exp (((m+1:ℕ):ℂ)*x) ≠ 0 := Complex.exp_ne_zero _
  rw [div_eq_iff he]
  push_cast at hI ⊢
  have he' : exp (((m:ℂ)+1)*x) ≠ 0 := Complex.exp_ne_zero _
  rw [sub_mul, one_mul, div_mul_cancel₀ _ he']
  linear_combination -hI

/-- `x e^{1-x} < 1` for `x ≠ 1`. -/
theorem igAsy_mul_exp_lt_one {x : ℝ} (hx1 : x ≠ 1) : x * Real.exp (1-x) < 1 := by
  have h := Real.add_one_lt_exp (sub_ne_zero.mpr hx1)
  have he : Real.exp (x-1) * Real.exp (1-x) = 1 := by rw [← Real.exp_add]; simp
  have hp := Real.exp_pos (1-x)
  nlinarith

/-- `(nx)^n/(n! e^{nx}) ≤ (x e^{1-x})^n` for `x ≥ 0`. -/
theorem igAsy_pow_div_factorial_le (n : ℕ) {x : ℝ} (hx0 : 0 ≤ x) :
    ((n:ℝ)*x)^n/n.factorial/Real.exp (n*x) ≤ (x*Real.exp (1-x))^n := by
  have h := Real.pow_div_factorial_le_exp (n:ℝ) (n.cast_nonneg) n
  rw [div_le_iff₀ (Real.exp_pos _), mul_pow, mul_pow, ← Real.exp_nat_mul]
  have he : Real.exp (n*(1-x)) * Real.exp (n*x) = Real.exp n := by rw [← Real.exp_add]; ring_nf
  calc (n:ℝ)^n * x^n / n.factorial = x^n * ((n:ℝ)^n/n.factorial) := by ring
    _ ≤ x^n * Real.exp n := by gcongr
    _ = x^n * Real.exp (n*(1-x)) * Real.exp (n*x) := by rw [mul_assoc, he]

/-- 8.11.13 for `0 ≤ x < 1`. -/
theorem igAsy_poisson_lt {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    Tendsto (fun m : ℕ => ((m+1)*x)^(m+1)/((m+1).factorial) * ((m+1)*x*∫ s in (0:ℝ)..1, igAsy_F m x s) /
        Real.exp ((m+1)*x)) atTop (𝓝 0) := by
  set r := x*Real.exp (1-x)
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := igAsy_mul_exp_lt_one hx1.ne
  have hlim : Tendsto (fun m : ℕ => r^(m+1) * (x/(1-x))) atTop (𝓝 0) := by
    have := ((tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).comp (tendsto_add_atTop_nat 1)).mul_const
      (x/(1-x))
    simpa [Function.comp_def] using this
  refine squeeze_zero (fun m => ?_) (fun m => ?_) hlim
  · have := intervalIntegral.integral_nonneg (μ := volume) (zero_le_one' ℝ) fun s hs => igAsy_F_nonneg m x hs.1
    positivity
  · have hJ := igAsy_integral_F_le m hx1
    have hJ0 := intervalIntegral.integral_nonneg (μ := volume) (zero_le_one' ℝ) fun s hs => igAsy_F_nonneg m x hs.1
    have hP := igAsy_pow_div_factorial_le (m+1) hx0
    push_cast at hP
    have h1 : (m+1)*x*∫ s in (0:ℝ)..1, igAsy_F m x s ≤ x/(1-x) := by
      have hm : (0:ℝ) < m+1 := by positivity
      have hx' : 0 < 1-x := by linarith
      calc (m+1)*x*∫ s in (0:ℝ)..1, igAsy_F m x s ≤ (m+1)*x*(1/((m+1)*(1-x))) := by gcongr
        _ = x/(1-x) := by field_simp
    rw [mul_div_right_comm]
    exact mul_le_mul hP h1 (by positivity) (by positivity)

/-- 8.11.13 at `x = 1`. -/
theorem igAsy_poisson_one :
    Tendsto (fun m : ℕ => ((m+1)*1)^(m+1)/((m+1).factorial) * ((m+1)*1*∫ s in (0:ℝ)..1, igAsy_F m 1 s) /
        Real.exp ((m+1)*1)) atTop (𝓝 (1/2)) := by
  have hst := (Stirling.tendsto_stirlingSeq_sqrt_pi.comp (tendsto_add_atTop_nat 1)).inv₀
    (by positivity : Real.sqrt π ≠ 0)
  have H := (hst.mul igAsy_tendsto_sqrt_J).div_const (Real.sqrt 2)
  have hval : (Real.sqrt π)⁻¹ * (Real.sqrt (2*π)/2) / Real.sqrt 2 = 1/2 := by
    rw [Real.sqrt_mul (by norm_num)]
    have : Real.sqrt π ≠ 0 := by positivity
    have : Real.sqrt 2 ≠ 0 := by positivity
    field_simp
  rw [hval] at H
  refine H.congr fun m => ?_
  simp only [Function.comp_apply, Stirling.stirlingSeq]
  push_cast
  have hm : (0:ℝ) < m+1 := by positivity
  have hs : Real.sqrt ((m:ℝ)+1) * Real.sqrt ((m:ℝ)+1) = (m:ℝ)+1 := Real.mul_self_sqrt hm.le
  rw [Real.sqrt_mul (by norm_num), div_pow, ← Real.exp_nat_mul]
  have hf : ((m+1).factorial : ℝ) ≠ 0 := by positivity
  have : Real.sqrt 2 ≠ 0 := by positivity
  have : Real.sqrt ((m:ℝ)+1) ≠ 0 := by positivity
  push_cast
  field_simp
  rw [Real.sq_sqrt hm.le]


/-- Exponential-series terms increase up to index `n` when `n ≤ y`. -/
theorem igAsy_term_le {k : ℕ} {y : ℝ} : ∀ n, k ≤ n → (n:ℝ) ≤ y →
    y^k/k.factorial ≤ y^n/n.factorial := by
  intro n hkn
  induction n, hkn using Nat.le_induction with
  | base => intro _; exact le_rfl
  | succ n hkn ih =>
    intro hy
    have hy' : (n:ℝ) ≤ y := by push_cast at hy; linarith
    refine (ih hy').trans ?_
    have hn : (0:ℝ) < n+1 := by positivity
    have hy0 : 0 ≤ y := le_trans (Nat.cast_nonneg n) hy'
    rw [Nat.factorial_succ, pow_succ]
    push_cast
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    push_cast at hy
    have : 0 ≤ y^n * (n.factorial : ℝ) := by positivity
    nlinarith

/-- 8.11.13 for `x > 1`. -/
theorem igAsy_poisson_gt {x : ℝ} (hx : 1 < x) :
    Tendsto (fun m : ℕ => expPartialSum (m+1) (((m+1:ℕ):ℂ)*x)/exp (((m+1:ℕ):ℂ)*x)) atTop (𝓝 0) := by
  set r := x*Real.exp (1-x)
  have hr0 : 0 ≤ r := by have : 0 ≤ x := by linarith
                         positivity
  have hr1 : r < 1 := igAsy_mul_exp_lt_one hx.ne'
  have heq : ∀ m : ℕ, expPartialSum (m+1) (((m+1:ℕ):ℂ)*x)/exp (((m+1:ℕ):ℂ)*x) =
      (((∑ k ∈ Finset.range (m+1+1), ((m+1:ℕ)*x)^k/k.factorial)/Real.exp ((m+1:ℕ)*x) : ℝ) : ℂ) := by
    intro m; simp only [expPartialSum]; push_cast; rfl
  simp only [heq]
  rw [show (0:ℂ) = ((0:ℝ):ℂ) by simp]
  refine (continuous_ofReal.tendsto _).comp ?_
  have hlim : Tendsto (fun m : ℕ => ((m+1:ℕ):ℝ)*r^(m+1) + r^(m+1)) atTop (𝓝 0) := by
    have h1 := (tendsto_self_mul_const_pow_of_lt_one hr0 hr1).comp (tendsto_add_atTop_nat 1)
    have h2 := (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).comp (tendsto_add_atTop_nat 1)
    simpa [Function.comp_def] using h1.add h2
  refine squeeze_zero (fun m => by positivity) (fun m => ?_) hlim
  set n := m+1
  have hy : (n:ℝ) ≤ n*x := by nlinarith [show (0:ℝ) ≤ n by positivity]
  have hsum : ∑ k ∈ Finset.range (n+1), ((n:ℝ)*x)^k/k.factorial ≤ (n+1) * (((n:ℝ)*x)^n/n.factorial) := by
    have := Finset.sum_le_card_nsmul (Finset.range (n+1)) (fun k => ((n:ℝ)*x)^k/k.factorial)
      (((n:ℝ)*x)^n/n.factorial) (fun k hk => igAsy_term_le n
        (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)) hy)
    simpa using this
  have hP := igAsy_pow_div_factorial_le n (by linarith : 0 ≤ x)
  calc (∑ k ∈ Finset.range (n+1), ((n:ℝ)*x)^k/k.factorial)/Real.exp (n*x)
      ≤ (n+1) * (((n:ℝ)*x)^n/n.factorial) / Real.exp (n*x) := by gcongr
    _ = (n+1) * (((n:ℝ)*x)^n/n.factorial/Real.exp (n*x)) := by ring
    _ ≤ (n+1) * r^n := by gcongr
    _ = (n:ℝ)*r^n + r^n := by ring

/-- expPartialSum poisson limit. -/
@[dlmf 8.11.E13]
theorem expPartialSum_poisson_limit {x : ℝ} (hx : 0 ≤ x) :
    Tendsto (fun n : ℕ => expPartialSum n (n*x)/exp (n*x : ℂ)) atTop (𝓝 (if 1 < x then 0 else if x=1 then 1/2 else 1)) := by
  rw [← tendsto_add_atTop_iff_nat 1]
  split_ifs with h1 h2
  · exact igAsy_poisson_gt h1
  · subst h2
    simp only [igAsy_ratio_eq]
    have := (continuous_ofReal.tendsto _).comp (tendsto_const_nhds (x := (1:ℝ)) |>.sub igAsy_poisson_one)
    rw [show (1/2:ℂ) = ((1 - 1/2 : ℝ) : ℂ) by push_cast; norm_num]
    exact this
  · have hx1 : x < 1 := by
      rcases lt_trichotomy x 1 with h | h | h
      · exact h
      · exact absurd h h2
      · exact absurd h h1
    simp only [igAsy_ratio_eq]
    have := (continuous_ofReal.tendsto _).comp (tendsto_const_nhds (x := (1:ℝ)) |>.sub (igAsy_poisson_lt hx hx1))
    rw [show (1:ℂ) = ((1 - 0 : ℝ) : ℂ) by push_cast; norm_num]
    exact this

/-- The exponential partial-sum remainder S_n. -/
@[dlmf 8.11.E15]
def expPartialSumRemainderS (n : ℕ) (x : ℝ) : ℂ :=
  lowerIncGamma (n+1) (n*x)/((n*x : ℂ)^n*exp (-n*x : ℂ))

/-- expPartialSumRemainderS identity. -/
@[dlmf 8.11.E14]
theorem expPartialSumRemainderS_identity (n : ℕ) (x : ℝ) :
    exp (n*x : ℂ)=expPartialSum n (n*x)+(n*x : ℂ)^n/n.factorial*expPartialSumRemainderS n x := by
  rw [expPartialSumRemainderS]
  exact igAsy_exp_identity n x

/-- `S_n(x) = n x ∫₀¹ s^n e^{n x (1-s)} ds`. -/
theorem igAsy_S_eq (m : ℕ) (x : ℝ) :
    expPartialSumRemainderS (m+1) x = (((m+1)*x * ∫ s in (0:ℝ)..1, igAsy_F m x s : ℝ) : ℂ) := by
  unfold expPartialSumRemainderS
  exact igAsy_lowerIncGamma_ratio_eq m x

/-- The real coefficients `d_k(x) = (-1)^k x h_k(x)/(1-x)` of 8.11.18. -/
noncomputable def igAsy_d (k : ℕ) (x : ℝ) : ℝ := (-1)^k * (x * igAsy_h k x/(1-x))

/-- The exact remainder of 8.11.18. -/
theorem igAsy_S_remainder (m N : ℕ) {x : ℝ} (hx : x < 1) :
    expPartialSumRemainderS (m+1) x - ∑ k ∈ Finset.range N, (igAsy_d k x : ℂ)/((m:ℂ)+1)^k =
      (((m+1)*x*((-1)^N/((m:ℝ)+1)^N * ∫ s in (0:ℝ)..1, igAsy_F m x s * igAsy_h N (x*s)) : ℝ) : ℂ) := by
  rw [igAsy_S_eq, igAsy_iter m hx N]
  have hm : (m:ℝ)+1 ≠ 0 := by positivity
  have hcast : ∀ k : ℕ, ((m:ℂ)+1)^k = (((m:ℝ)+1)^k : ℝ) := fun k => by push_cast; ring
  simp only [igAsy_d, hcast, ← ofReal_div, ← ofReal_sum, ← ofReal_sub]
  congr 1
  rw [mul_add, Finset.mul_sum, add_sub_right_comm]
  rw [show ∑ i ∈ Finset.range N, ((m:ℝ)+1)*x*((-1)^i/((m:ℝ)+1)^(i+1)*(igAsy_h i x/(1-x))) -
      ∑ k ∈ Finset.range N, (-1)^k*(x*igAsy_h k x/(1-x))/((m:ℝ)+1)^k = 0 by
    rw [sub_eq_zero]; refine Finset.sum_congr rfl fun k _ => ?_
    rw [pow_succ]; field_simp]
  ring

/-- The remainder bound behind 8.11.18. -/
theorem igAsy_S_remainder_bound (N : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C, ∀ m : ℕ, ∀ x : ℝ, x ≤ 1-δ →
      ‖expPartialSumRemainderS (m+1) x - ∑ k ∈ Finset.range N, (igAsy_d k x : ℂ)/((m:ℂ)+1)^k‖
        ≤ C * (1/((m:ℝ)+1)^N) := by
  obtain ⟨K, hK0, hK⟩ := igAsy_h_bound N hδ
  refine ⟨K * max 1 (1/δ), fun m x hxδ => ?_⟩
  have hx : x < 1 := by linarith
  have hx1 : 0 < 1 - x := by linarith
  have hm : (0:ℝ) < (m:ℝ)+1 := by positivity
  rw [igAsy_S_remainder m N hx, Complex.norm_real, Real.norm_eq_abs]
  set I := ∫ s in (0:ℝ)..1, igAsy_F m x s * igAsy_h N (x*s)
  have hFc : Continuous (igAsy_F m x) := by unfold igAsy_F; fun_prop
  have hI : |I| ≤ K * (1/((m+1)*(1-x))) := by
    refine (intervalIntegral.abs_integral_le_integral_abs zero_le_one).trans ?_
    refine le_trans ?_ (mul_le_mul_of_nonneg_left (igAsy_integral_F_le m hx) hK0)
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on zero_le_one ?_
      ((hFc.const_smul K).intervalIntegrable _ _) ?_
    · exact ((hFc.continuousOn.mul (igAsy_continuousOn_h N hx)).abs).intervalIntegrable
    · intro s hs
      have hy : x*s ≤ max 0 (1-δ) := by
        rcases le_or_gt x 0 with h | h
        · exact (mul_nonpos_of_nonpos_of_nonneg h hs.1).trans (le_max_left _ _)
        · exact (le_trans (by nlinarith [hs.2]) hxδ).trans (le_max_right _ _)
      rw [abs_mul, abs_of_nonneg (igAsy_F_nonneg m x hs.1), mul_comm K]
      exact mul_le_mul_of_nonneg_left (hK _ hy) (igAsy_F_nonneg m x hs.1)
  have hxr : |x|/(1-x) ≤ max 1 (1/δ) := by
    rw [div_le_iff₀ hx1]
    rcases le_or_gt x 0 with h | h
    · rw [abs_of_nonpos h]; nlinarith [le_max_left 1 (1/δ)]
    · rw [abs_of_pos h]
      have h1 : 1/δ ≤ max 1 (1/δ) := le_max_right _ _
      have h2 : δ ≤ 1-x := by linarith
      have h3 : 1 ≤ (1/δ)*(1-x) := by rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hδ]; linarith
      nlinarith
  have hpos : 0 < ((m:ℝ)+1)^N := by positivity
  rw [abs_mul, abs_mul, abs_mul, abs_div, abs_pow, abs_neg, abs_one, one_pow, abs_of_pos hm, abs_of_pos hpos]
  calc ((m:ℝ)+1)*|x| * (1/((m:ℝ)+1)^N*|I|) ≤ ((m:ℝ)+1)*|x| * (1/((m:ℝ)+1)^N*(K*(1/((m+1)*(1-x))))) := by
        gcongr
    _ = K*(|x|/(1-x))*(1/((m:ℝ)+1)^N) := by field_simp
    _ ≤ K*max 1 (1/δ)*(1/((m:ℝ)+1)^N) := by gcongr

/-- The phase `φ(u) = u - log(1+u)`, with `(1+u)^n e^{-nu} = e^{-n φ(u)}`. -/
noncomputable def igAsy_phi (u : ℝ) : ℝ := u - Real.log (1+u)

/-- The quotient `φ(u)/u²`, extended analytically to `u = 0`. -/
noncomputable def igAsy_Q : ℝ → ℝ := dslope (dslope igAsy_phi 0) 0

/-- `φ` is analytic at `0`. -/
theorem igAsy_analyticAt_phi : AnalyticAt ℝ igAsy_phi 0 := by
  unfold igAsy_phi
  exact analyticAt_id.sub ((analyticAt_const.add analyticAt_id).log (by norm_num))

/-- `Q` is analytic at `0`. -/
theorem igAsy_analyticAt_Q : AnalyticAt ℝ igAsy_Q 0 :=
  (igAsy_analyticAt_phi.dslope 0).dslope 0

/-- `φ(u) = u² Q(u)`. -/
theorem igAsy_phi_eq (u : ℝ) : igAsy_phi u = u^2 * igAsy_Q u := by
  have h := dblZero_eq_sq_mul_dslope (g := igAsy_phi) (x₀ := 0) (by simp [igAsy_phi]) ?_ u
  · simpa [igAsy_Q] using h
  · have : HasDerivAt igAsy_phi (1 - 1/(1+0)) 0 :=
      (hasDerivAt_id 0).sub (((hasDerivAt_id (0:ℝ)).const_add 1).log (by norm_num))
    rw [this.deriv]; norm_num

/-- `|φ(u) - u²/2| ≤ 2|u|³` for `|u| ≤ 1/2`. -/
theorem igAsy_phi_sub_le {u : ℝ} (hu : |u| ≤ 1/2) : |igAsy_phi u - u^2/2| ≤ 2*|u|^3 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := -u) (by rw [abs_neg]; linarith) 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, abs_neg, sub_neg_eq_add] at h
  have h1 : |igAsy_phi u - u^2/2| = |(0 + (-u)^(0+1)/((0:ℕ)+1) + (-u)^(1+1)/((1:ℕ)+1))
      + Real.log (1+u)| := by
    rw [← abs_neg]; unfold igAsy_phi; congr 1; push_cast; ring
  rw [h1]
  refine h.trans ?_
  show |u|^3/(1-|u|) ≤ 2*|u|^3
  rw [div_le_iff₀ (by linarith)]
  have : 0 ≤ |u|^3 := by positivity
  nlinarith [abs_nonneg u]

/-- `Q(0) = 1/2`. -/
theorem igAsy_Q_zero : igAsy_Q 0 = 1/2 := by
  have hc : Tendsto (fun u => |igAsy_Q u - 1/2|) (𝓝[≠] 0) (𝓝 |igAsy_Q 0 - 1/2|) :=
    ((igAsy_analyticAt_Q.continuousAt.sub continuousAt_const).abs).tendsto.mono_left
      nhdsWithin_le_nhds
  have h2 : Tendsto (fun u : ℝ => 2*|u|) (𝓝[≠] 0) (𝓝 0) := by
    have : Tendsto (fun u : ℝ => 2*|u|) (𝓝 0) (𝓝 (2*|0|)) :=
      (continuous_const.mul continuous_abs).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  have hle : ∀ᶠ u in 𝓝[≠] (0:ℝ), |igAsy_Q u - 1/2| ≤ 2*|u| := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Metric.ball_mem_nhds (0:ℝ)
      (by norm_num : (0:ℝ) < 1/2))] with u hu hb
    have hu0 : u ≠ 0 := hu
    have hb' : |u| ≤ 1/2 := by simpa [Real.dist_eq] using (Metric.mem_ball.1 hb).le
    have h := igAsy_phi_sub_le hb'
    rw [igAsy_phi_eq, show u^2 * igAsy_Q u - u^2/2 = u^2 * (igAsy_Q u - 1/2) by ring, abs_mul,
      abs_of_nonneg (sq_nonneg u), ← sq_abs, show 2*|u|^3 = |u|^2 * (2*|u|) by ring] at h
    exact le_of_mul_le_mul_left h (by positivity)
  have := le_of_tendsto_of_tendsto hc h2 hle
  have h0 : |igAsy_Q 0 - 1/2| = 0 := le_antisymm this (abs_nonneg _)
  linarith [abs_eq_zero.1 h0]

/-- The signed square root `u √(2 Q(u))` of `2φ(u)`. -/
noncomputable def igAsy_sqrtPhi (u : ℝ) : ℝ := (u - 0) * Real.sqrt (2 * igAsy_Q u)

/-- The signed square root vanishes at `0`. -/
theorem igAsy_sqrtPhi_zero : igAsy_sqrtPhi 0 = 0 := by simp [igAsy_sqrtPhi]

/-- The signed square root is analytic at `0` with derivative `1`, and `φ = V²/2` near `0`. -/
theorem igAsy_sqrtPhi_props : AnalyticAt ℝ igAsy_sqrtPhi 0 ∧ HasDerivAt igAsy_sqrtPhi 1 0 ∧
    ∀ᶠ x in 𝓝 0, igAsy_phi x = igAsy_sqrtPhi x ^ 2 / 2 := by
  obtain ⟨h1, h2, h3⟩ := dblZero_signedSqrt (g := igAsy_phi) igAsy_analyticAt_Q
    (by rw [igAsy_Q_zero]; norm_num) (Eventually.of_forall fun x => by rw [igAsy_phi_eq]; ring)
  refine ⟨h1, ?_, h3.mono fun x hx => hx.1⟩
  have : Real.sqrt (2 * igAsy_Q 0) = 1 := by rw [igAsy_Q_zero]; norm_num
  rw [this] at h2
  exact h2

/-- Taylor coefficients of the inverse of `u ↦ u √(2Q(u))` up to degree `8`. -/
noncomputable def igAsy_Pc : ℕ → ℝ
  | 1 => 1 | 2 => 1/3 | 3 => 1/36 | 4 => -1/270 | 5 => 1/4320 | 6 => 1/17010
  | 7 => -139/5443200 | 8 => 1/204120 | _ => 0

/-- The degree-`8` polynomial `P(v) = ∑_{k<9} P_k v^k` divided by `v`. -/
noncomputable def igAsy_P1 (v : ℝ) : ℝ :=
  1 + v/3 + v^2/36 - v^3/270 + v^4/4320 + v^5/17010 - 139*v^6/5443200 + v^7/204120

theorem igAsy_sum_Pc (v : ℝ) : ∑ k ∈ Finset.range 9, igAsy_Pc k * v^k = v * igAsy_P1 v := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, igAsy_Pc, igAsy_P1]
  ring

/-- The residual polynomial of the inverse-series verification. -/
noncomputable def igAsy_R (v : ℝ) : ℝ := -v^62/2768104942150133660519356040269823606784000000000 + 139*v^61/8201792421185581216353647526725403279360000000000 - 64363*v^60/164035848423711624327072950534508065587200000000000 + 8414711*v^59/1458096430432992216240648449195627249664000000000000 - 39398720783*v^58/699886286607836263795511255613901079838720000000000000 + 800844031091*v^57/2666233472791757195411471449957718399385600000000000000 + 203207581524653*v^56/319948016735010863449376573994926207926272000000000000000 - 589903790773392367*v^55/19907876596845120392405653493017630715412480000000000000000 + 1812135294676417436239*v^54/6370520510990438525569809117765641828931993600000000000000000 - 61536180983488037268223*v^53/56626848986581675782842747713472371812728832000000000000000000 - 3200028968192764058201*v^52/530876709249203210464150759813803485744332800000000000000000 + 311443135429997527330939*v^51/2831342449329083789142137385673618590636441600000000000000000 - 44454799605418997643991*v^50/75839529892743315780592965687686212249190400000000000000000 - 559676526517695375461*v^49/674129154602162806938604139446099664437248000000000000000 + 198376372993988324996513*v^48/5898630102768924560712786220153372063825920000000000000000 - 128833516499331115639963*v^47/655403344752102728968087357794819118202880000000000000000 - 3667317918596362552760177*v^46/15729680274050465495234096587075658836869120000000000000000 + 324230753132416786833013*v^45/32770167237605136448404367889740955910144000000000000000 - 14952974654565356951124521*v^44/294931505138446228035639311007668603191296000000000000000 - 13252544188014095919239*v^43/130040346180972763684144317022781571072000000000000000 + 27771663040102917607741*v^42/10403227694477821094731545361822525685760000000000000 - 11954991339734226940007*v^41/1083669551508106364034535975189846425600000000000000 - 36449936144571194043961*v^40/722446367672070909356357316793230950400000000000000 + 75166882097473144608997*v^39/120407727945345151559392886132205158400000000000000 - 22315566379032504120787*v^38/16054363726046020207919051484294021120000000000000 - 120052626821536535467*v^37/7963474070459335420594767601336320000000000000 + 6103713633575949013303*v^36/47780844422756012523568605608017920000000000000 - 29626459559588237*v^35/530898271363955694706317840089088000000000 - 517463897990836994347*v^34/106179654272791138941263568017817600000000000 + 121286984931364029473*v^33/8848304522732594911771964001484800000000000 + 17223711251174594586739*v^32/309690658295640821912018740051968000000000000 - 25997842511592509407*v^31/35112319534653154411793507942400000000000 + 252464389076981274511*v^30/140449278138612617647174031769600000000000 + 58750710510092643809*v^29/2926026627887762867649458995200000000000 - 11171106973961039807*v^28/65022813953061397058876866560000000000 - 522621430896224857*v^27/602063092157975898693304320000000000 + 6291240544991059709*v^26/6095888808099505974269706240000000000 - 181301900023966397*v^25/20158362460646514465177600000000000 - 17454651767210771*v^24/368610056423250550220390400000000 + 696576869128085983*v^23/1075112664567814104809472000000000 - 200522812574221273*v^22/179185444094635684134912000000000 - 35470128327336733*v^21/597284813648785613783040000000 - 132577309851169703*v^20/398189875765857075855360000000 - 510374274227141*v^19/493787048320755302400000000 - 2858145000327557*v^18/967419523240663449600000000 + 517628494375877*v^17/131676546218868080640000000 + 2490219288582629*v^16/65838273109434040320000000 - 14261288811003299*v^15/10973045518239006720000000 - 7688700092268269*v^14/438921820729560268800000 - 469646448720269*v^13/4354383142158336000000 - 1797913715932633*v^12/4354383142158336000000 - 713769681139453*v^11/725730523693056000000 - 7696763934359*v^10/7679688081408000000 - 16218691291337*v^9/1343945414246400000 - 408540701317127*v^8/1511938591027200000 - 8497883956229*v^7/3199870033920000 - 1823729366989*v^6/114281072640000 - 17479190864627*v^5/266655836160000 - 16977567694037*v^4/88885278720000 - 58412710933*v^3/148142131200 - 15240966109*v^2/27433728000 - 158347621*v/326592000 - 235145669/1175731200

/-- The polynomial identity behind the inverse-series verification. -/
theorem igAsy_residual_identity (v : ℝ) :
    2*(v * igAsy_P1 v - (-∑ i ∈ Finset.range 9, (-(v * igAsy_P1 v))^(i+1)/((i:ℝ)+1))) - v^2 =
      v^10 * igAsy_R v := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, igAsy_P1, igAsy_R]
  norm_num
  ring

/-- `P₁` is continuous. -/
theorem igAsy_continuous_P1 : Continuous igAsy_P1 := by unfold igAsy_P1; fun_prop

/-- The residual polynomial is continuous. -/
theorem igAsy_continuous_R : Continuous igAsy_R := by unfold igAsy_R; fun_prop

/-- `2φ(P(v)) - v² = O(v^{10})`. -/
theorem igAsy_isBigO_residual :
    (fun v => 2 * igAsy_phi (v * igAsy_P1 v) - v^2) =O[𝓝 0] fun v => v^10 := by
  set Pn : ℝ → ℝ := fun v => v * igAsy_P1 v with hPn
  have hPc : Continuous Pn := continuous_id.mul igAsy_continuous_P1
  have hP0 : Tendsto Pn (𝓝 0) (𝓝 0) := by simpa [hPn] using hPc.tendsto 0
  have hP1 : Tendsto igAsy_P1 (𝓝 0) (𝓝 1) := by
    simpa [igAsy_P1] using igAsy_continuous_P1.tendsto 0
  set E : ℝ → ℝ := fun v => ∑ i ∈ Finset.range 9, (-(Pn v))^(i+1)/((i:ℝ)+1) +
    Real.log (1 + Pn v) with hE
  have hEO : E =O[𝓝 0] fun v => v^10 := by
    refine IsBigO.of_bound (2*2^10) ?_
    filter_upwards [hP0.eventually (Metric.closedBall_mem_nhds (0:ℝ) (by norm_num : (0:ℝ) < 1/2)),
      hP1.eventually (Metric.closedBall_mem_nhds (1:ℝ) one_pos)] with v hv h1
    have hv' : |Pn v| ≤ 1/2 := by simpa [Real.dist_eq] using Metric.mem_closedBall.1 hv
    have h1' : |igAsy_P1 v| ≤ 2 := by
      have := Metric.mem_closedBall.1 h1
      rw [Real.dist_eq] at this
      have := abs_sub_abs_le_abs_sub (igAsy_P1 v) 1
      norm_num at this ⊢; linarith
    have hb := Real.abs_log_sub_add_sum_range_le (x := -(Pn v)) (by rw [abs_neg]; linarith) 9
    rw [abs_neg, sub_neg_eq_add] at hb
    have h2 : |Pn v| ^ (9+1) / (1 - |Pn v|) ≤ 2 * |Pn v|^10 := by
      rw [div_le_iff₀ (by linarith), show 9+1 = 10 by rfl]
      have : 0 ≤ |Pn v|^10 := by positivity
      nlinarith
    have h3 : |Pn v| ≤ 2 * |v| := by
      simp only [hPn, abs_mul]; nlinarith [abs_nonneg v]
    have h4 : |Pn v|^10 ≤ (2*|v|)^10 := pow_le_pow_left₀ (abs_nonneg _) h3 10
    rw [Real.norm_eq_abs, norm_pow, Real.norm_eq_abs]
    calc |E v| ≤ 2 * |Pn v|^10 := hb.trans h2
      _ ≤ 2 * (2*|v|)^10 := by gcongr
      _ = 2*2^10 * |v|^10 := by ring
  have hRO : (fun v => v^10 * igAsy_R v) =O[𝓝 0] fun v => v^10 := by
    have := (isBigO_refl (fun v : ℝ => v^10) (𝓝 0)).mul
      ((igAsy_continuous_R.tendsto 0).isBigO_one ℝ)
    simpa using this
  refine (hRO.sub (hEO.const_mul_left 2)).congr' (Eventually.of_forall fun v => ?_)
    EventuallyEq.rfl
  have := igAsy_residual_identity v
  simp only [hE, hPn, igAsy_phi] at this ⊢
  rw [← this]
  ring

/-- `V(P(v)) - v = O(v⁹)` as `v → 0`, `v ≠ 0`. -/
theorem igAsy_isBigO_sqrtPhi_P :
    (fun v => igAsy_sqrtPhi (v * igAsy_P1 v) - v) =O[𝓝[≠] 0] fun v => v^9 := by
  set Pn : ℝ → ℝ := fun v => v * igAsy_P1 v with hPn
  set A : ℝ → ℝ := fun v => igAsy_P1 v * Real.sqrt (2 * igAsy_Q (Pn v)) with hA
  have hPc : Continuous Pn := continuous_id.mul igAsy_continuous_P1
  have hP0 : Tendsto Pn (𝓝 0) (𝓝 0) := by simpa [hPn] using hPc.tendsto 0
  have hQP : Tendsto (fun v => igAsy_Q (Pn v)) (𝓝 0) (𝓝 (1/2)) := by
    rw [← igAsy_Q_zero]; exact igAsy_analyticAt_Q.continuousAt.tendsto.comp hP0
  have hAt : Tendsto A (𝓝 0) (𝓝 1) := by
    have h1 : Tendsto igAsy_P1 (𝓝 0) (𝓝 1) := by
      simpa [igAsy_P1] using igAsy_continuous_P1.tendsto 0
    have := h1.mul ((hQP.const_mul 2).sqrt)
    rw [show (1:ℝ) * Real.sqrt (2*(1/2)) = 1 by norm_num] at this
    exact this
  have hsq : (fun v => A v ^ 2 - 1 ^ 2) =O[𝓝[≠] 0] fun v => v^8 := by
    have h := (igAsy_isBigO_residual.mono nhdsWithin_le_nhds).mul
      (isBigO_refl (fun v : ℝ => (v^2)⁻¹) (𝓝[≠] 0))
    refine h.congr' ?_ ?_
    · filter_upwards [self_mem_nhdsWithin, Eventually.filter_mono nhdsWithin_le_nhds
        (hQP.eventually (lt_mem_nhds (by norm_num : (0:ℝ) < 1/2)))] with v hv hq
      have hv : v ≠ 0 := hv
      simp only [hA]
      rw [mul_pow, Real.sq_sqrt (by linarith : (0:ℝ) ≤ 2 * igAsy_Q (Pn v))]
      simp only [igAsy_phi_eq, hPn]
      field_simp
    · filter_upwards [self_mem_nhdsWithin] with v hv
      have hv : v ≠ 0 := hv
      field_simp
  have h1 := invSer_isBigO_sub_of_pow_sub two_ne_zero one_ne_zero
    (hAt.mono_left nhdsWithin_le_nhds) tendsto_const_nhds hsq
  refine ((isBigO_refl (fun v : ℝ => v) _).mul h1).congr' (Eventually.of_forall fun v => ?_)
    (Eventually.of_forall fun v => by ring)
  simp only [hA, hPn, igAsy_sqrtPhi]
  ring

/-- The Taylor coefficients of a local inverse of `u ↦ u √(2Q(u))` up to degree `8`. -/
theorem igAsy_coeff_of_inverse {U : ℝ → ℝ} {p : FormalMultilinearSeries ℝ ℝ ℝ}
    (hp : HasFPowerSeriesAt U p 0) (hl : ∀ᶠ x in 𝓝 0, U (igAsy_sqrtPhi x) = x) :
    ∀ k < 9, p.coeff k = igAsy_Pc k := by
  have hs : HasStrictDerivAt U (deriv U 0) (igAsy_sqrtPhi 0) := by
    rw [igAsy_sqrtPhi_zero]; exact hp.analyticAt.hasStrictDerivAt
  have hPt : Tendsto (fun v => v * igAsy_P1 v) (𝓝[≠] 0) (𝓝 0) := by
    have h : Continuous fun v : ℝ => v * igAsy_P1 v := continuous_id.mul igAsy_continuous_P1
    have := h.tendsto 0
    simp only [zero_mul] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hid : Tendsto (fun v : ℝ => v) (𝓝[≠] 0) (𝓝 (igAsy_sqrtPhi 0)) := by
    rw [igAsy_sqrtPhi_zero]; exact tendsto_id.mono_left nhdsWithin_le_nhds
  have ha : (fun v => v * igAsy_P1 v - U v) =O[𝓝[≠] 0] fun v => v^9 :=
    (invSer_isBigO_sub_of_leftInverse hs hl igAsy_sqrtPhi_props.1.continuousAt hPt hid).trans
      igAsy_isBigO_sqrtPhi_P
  have hc := (hp.isBigO_sub_partialSum_pow 9).mono (nhdsWithin_le_nhds (s := {0}ᶜ))
  simp only [zero_add, FormalMultilinearSeries.partialSum,
    FormalMultilinearSeries.apply_eq_pow_smul_coeff, smul_eq_mul] at hc
  have hc' : (fun y => U y - ∑ k ∈ Finset.range 9, y^k * p.coeff k) =O[𝓝[≠] 0]
      fun y => y^9 :=
    hc.trans (IsBigO.of_bound 1 (Eventually.of_forall fun y => by simp))
  have H := hc'.neg_left.sub ha
  have H' : (fun v : ℝ => ∑ k ∈ Finset.range 9, (fun k => p.coeff k - igAsy_Pc k) k * v^k)
      =O[𝓝[≠] 0] fun v => v^9 := by
    refine H.congr' (Eventually.of_forall fun v => ?_) EventuallyEq.rfl
    simp only [sub_mul, Finset.sum_sub_distrib, igAsy_sum_Pc, mul_comm (p.coeff _)]
    ring
  intro k hk
  exact sub_eq_zero.1 (lapSad_coeff_eq_zero_of_isBigO 9 H' k hk)

/-- **The saddle substitution for `φ(u) = u - log(1+u)`.** There is an analytic `U` with
`φ(U(v)) = v²/2` near `0`, `sign U(v) = sign v`, and Taylor coefficients `igAsy_Pc`. -/
theorem igAsy_saddle : ∃ (U : ℝ → ℝ) (p : FormalMultilinearSeries ℝ ℝ ℝ) (v₀ : ℝ), 0 < v₀ ∧
    HasFPowerSeriesAt U p 0 ∧ (∀ k < 9, p.coeff k = igAsy_Pc k) ∧
    (∀ v ∈ Icc (-v₀) v₀, HasDerivAt U (deriv U v) v ∧ ContinuousAt (deriv U) v ∧
      -1/2 < U v ∧ igAsy_phi (U v) = v^2/2) ∧ U (-v₀) < 0 ∧ 0 < U v₀ := by
  obtain ⟨hVa, hVd, hVphi⟩ := igAsy_sqrtPhi_props
  obtain ⟨U, hUa, -, hU0, hl, hr⟩ := dblZero_exists_analytic_inverse hVa hVd one_ne_zero
  rw [igAsy_sqrtPhi_zero] at hUa hU0 hr
  obtain ⟨p, hp⟩ := hUa
  have hUt : Tendsto U (𝓝 0) (𝓝 0) := by
    simpa [hU0] using hp.analyticAt.continuousAt.tendsto
  have hev : ∀ᶠ v in 𝓝 (0:ℝ), AnalyticAt ℝ U v ∧ -1/2 < U v ∧ igAsy_phi (U v) = v^2/2 ∧
      igAsy_sqrtPhi (U v) = v := by
    filter_upwards [hp.analyticAt.eventually_analyticAt,
      hUt.eventually (lt_mem_nhds (by norm_num : (-1/2:ℝ) < 0)), hUt.eventually hVphi, hr]
      with v h1 h2 h3 h4
    exact ⟨h1, h2, by rw [h3, h4], h4⟩
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
  have hmem : ∀ v ∈ Icc (-(ε/2)) (ε/2), dist v 0 < ε := fun v hv => by
    rw [Real.dist_eq, sub_zero, abs_lt]; constructor <;> linarith [hv.1, hv.2]
  refine ⟨U, p, ε/2, by positivity, hp, igAsy_coeff_of_inverse hp hl, fun v hv => ?_, ?_, ?_⟩
  · obtain ⟨h1, h2, h3, -⟩ := hball (hmem v hv)
    exact ⟨h1.differentiableAt.hasDerivAt, h1.deriv.continuousAt, h2, h3⟩
  · obtain ⟨-, -, -, h4⟩ := hball (hmem (-(ε/2)) ⟨le_rfl, by linarith⟩)
    by_contra hc
    replace hc := not_lt.1 hc
    have : 0 ≤ igAsy_sqrtPhi (U (-(ε/2))) := by
      unfold igAsy_sqrtPhi; rw [sub_zero]; exact mul_nonneg hc (Real.sqrt_nonneg _)
    linarith
  · obtain ⟨-, -, -, h4⟩ := hball (hmem (ε/2) ⟨by linarith, le_rfl⟩)
    by_contra hc
    replace hc := not_lt.1 hc
    have : igAsy_sqrtPhi (U (ε/2)) ≤ 0 := by
      unfold igAsy_sqrtPhi; rw [sub_zero]
      exact mul_nonpos_of_nonpos_of_nonneg hc (Real.sqrt_nonneg _)
    linarith

/-- `s^n e^{n(1-s)} = e^{-n φ(s-1)}` at `s = 1 + u > 0`. -/
theorem igAsy_F_one_add (m : ℕ) {u : ℝ} (hu : -1 < u) :
    igAsy_F m 1 (1+u) = Real.exp (-((m:ℝ)+1) * igAsy_phi u) := by
  have h : 0 < 1+u := by linarith
  unfold igAsy_F igAsy_phi
  rw [← Real.exp_log (pow_pos h (m+1)), ← Real.exp_add, Real.log_pow]
  congr 1; push_cast; ring

/-- `∫₀^∞ s^n e^{n(1-s)} ds = eⁿ n!/n^{n+1}`. -/
theorem igAsy_integral_F_Ioi (m : ℕ) :
    IntegrableOn (igAsy_F m 1) (Ioi 0) ∧ ∫ s in Ioi (0:ℝ), igAsy_F m 1 s =
      Real.exp ((m:ℝ)+1) * ((m+1).factorial * (((m:ℝ)+1)^(m+2))⁻¹) := by
  have hs : (0:ℝ) < (m:ℝ)+2 := by positivity
  have hz : (0:ℝ) < (m:ℝ)+1 := by positivity
  have heq : EqOn (igAsy_F m 1) (fun s => Real.exp ((m:ℝ)+1) *
      (Real.exp (-((m:ℝ)+1) * s) * s ^ ((m:ℝ)+2-1))) (Ioi 0) := by
    intro s _
    dsimp only
    rw [show (m:ℝ)+2-1 = ((m+1:ℕ):ℝ) by push_cast; ring, Real.rpow_natCast]
    unfold igAsy_F
    rw [show ((m:ℝ)+1)*1*(1-s) = ((m:ℝ)+1) + (-((m:ℝ)+1) * s) by ring, Real.exp_add]
    ring
  have hI : IntegrableOn (fun s => Real.exp ((m:ℝ)+1) *
      (Real.exp (-((m:ℝ)+1) * s) * s ^ ((m:ℝ)+2-1))) (Ioi 0) :=
    (integrableOn_exp_neg_mul_mul_rpow_sub_one hs hz).const_mul _
  refine ⟨hI.congr_fun heq.symm measurableSet_Ioi, ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioi heq, integral_const_mul,
    integral_exp_neg_mul_mul_rpow_sub_one hs hz,
    show (m:ℝ)+2 = ((m+1:ℕ):ℝ)+1 by push_cast; ring, Real.Gamma_nat_eq_factorial,
    Real.rpow_neg hz.le, show ((m+1:ℕ):ℝ)+1 = ((m+2:ℕ):ℝ) by push_cast; ring, Real.rpow_natCast]

/-- `φ` decreases on `(-1, 0]`: `φ(t-1) ≤ φ(s-1)` for `0 < s ≤ t ≤ 1`. -/
theorem igAsy_phi_anti {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) (ht : t ≤ 1) :
    igAsy_phi (t-1) ≤ igAsy_phi (s-1) := by
  have ht0 : 0 < t := hs.trans_le hst
  have h := Real.one_sub_inv_le_log_of_pos (div_pos ht0 hs)
  rw [Real.log_div ht0.ne' hs.ne', inv_div] at h
  unfold igAsy_phi
  simp only [add_sub_cancel]
  have h2 : 0 ≤ (t - s) * (1/t - 1) := mul_nonneg (by linarith) (by
    rw [sub_nonneg, le_div_iff₀ ht0]; linarith)
  have h3 : s/t = 1 - (t-s)/t := by field_simp; ring
  have h4 : (t-s)/t = (t-s)*(1/t) := by ring
  nlinarith

/-- Left tail: `∫₀ᵗ F ≤ t e^{-n φ(t-1)}` for `0 < t ≤ 1`. -/
theorem igAsy_left_tail (m : ℕ) {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    0 ≤ ∫ s in (0:ℝ)..t, igAsy_F m 1 s ∧
      ∫ s in (0:ℝ)..t, igAsy_F m 1 s ≤ t * Real.exp (-((m:ℝ)+1) * igAsy_phi (t-1)) := by
  have hc : Continuous (igAsy_F m 1) := by unfold igAsy_F; fun_prop
  refine ⟨intervalIntegral.integral_nonneg ht0.le fun s hs => igAsy_F_nonneg m 1 hs.1, ?_⟩
  have := intervalIntegral.integral_mono_on ht0.le (hc.intervalIntegrable _ _)
    (continuous_const.intervalIntegrable (μ := volume) _ _)
    (g := fun _ => Real.exp (-((m:ℝ)+1) * igAsy_phi (t-1))) fun s hs => by
      rcases hs.1.eq_or_lt with h | h
      · subst h; simp [igAsy_F]; positivity
      · have := igAsy_F_one_add m (u := s-1) (by linarith)
        rw [add_sub_cancel] at this
        rw [this, Real.exp_le_exp]
        have := igAsy_phi_anti h hs.2 ht1
        nlinarith [show (0:ℝ) ≤ (m:ℝ)+1 by positivity]
  simpa using this

/-- Right tail: `∫_{1+a}^∞ F ≤ e^{-n φ(a)} (1+a)/(n a)` for `a > 0`. -/
theorem igAsy_right_tail (m : ℕ) {a : ℝ} (ha : 0 < a) :
    0 ≤ ∫ s in Ioi (1+a), igAsy_F m 1 s ∧ ∫ s in Ioi (1+a), igAsy_F m 1 s ≤
      Real.exp (-((m:ℝ)+1) * igAsy_phi a) * ((1+a)/(((m:ℝ)+1)*a)) := by
  set n : ℝ := (m:ℝ)+1 with hn
  have hn0 : 0 < n := by positivity
  set t := 1+a with ht
  have ht0 : 0 < t := by linarith
  set θ := a/t with hθ
  have hθ0 : 0 < θ := div_pos ha ht0
  have hFi : IntegrableOn (igAsy_F m 1) (Ioi t) :=
    (igAsy_integral_F_Ioi m).1.mono_set (Ioi_subset_Ioi ht0.le)
  refine ⟨setIntegral_nonneg measurableSet_Ioi fun s hs =>
    igAsy_F_nonneg m 1 (ht0.trans hs).le, ?_⟩
  set C := Real.exp (-n * igAsy_phi a + n*θ*t) with hC
  have hgi : IntegrableOn (fun s => C * Real.exp ((-(n*θ)) * s)) (Ioi t) :=
    (integrableOn_exp_mul_Ioi (by nlinarith) t).const_mul C
  have hle := setIntegral_mono_on hFi hgi measurableSet_Ioi fun s (hs : t < s) => by
    have hs0 : 0 < s := ht0.trans hs
    have h1 := igAsy_F_one_add m (u := s-1) (by linarith)
    rw [add_sub_cancel] at h1
    rw [h1, hC, ← Real.exp_add, Real.exp_le_exp]
    have h2 := Real.log_le_sub_one_of_pos (div_pos hs0 ht0)
    rw [Real.log_div hs0.ne' ht0.ne'] at h2
    have h3 : igAsy_phi (s-1) - igAsy_phi a ≥ θ * (s - t) := by
      unfold igAsy_phi
      rw [show 1 + (s-1) = s by ring, ← ht]
      have : s/t - 1 = (s - t) - θ*(s-t) := by rw [hθ, ht]; field_simp; ring
      linarith
    nlinarith
  rw [integral_const_mul, integral_exp_mul_Ioi (by nlinarith) t, hC] at hle
  refine hle.trans (le_of_eq ?_)
  rw [neg_div_neg_eq, mul_div_assoc', ← Real.exp_add, show -n * igAsy_phi a + n*θ*t + -(n*θ)*t =
    -n * igAsy_phi a by ring, hθ]
  field_simp

/-- The exact decomposition behind 8.11.16: the Gaussian integral after the saddle substitution
plus exponentially small boundary terms. -/
theorem igAsy_one_decomp {U : ℝ → ℝ} {v₀ : ℝ} (hv₀ : 0 < v₀) (hU0 : U 0 = 0)
    (hd : ∀ v ∈ Icc (-v₀) v₀, HasDerivAt U (deriv U v) v ∧ ContinuousAt (deriv U) v ∧
      -1/2 < U v ∧ igAsy_phi (U v) = v^2/2) (ha : 0 < U v₀) (m : ℕ) :
    ((m:ℝ)+1)*1 * (∫ s in (0:ℝ)..1, igAsy_F m 1 s) -
        (m+1).factorial * Real.exp ((m:ℝ)+1) / (2*((m:ℝ)+1)^(m+1)) =
      ((m:ℝ)+1)^2/2 * (∫ v in (0:ℝ)..v₀, Real.exp (-((m:ℝ)+1) * v^2/2) * (v * (-U (-v) - U v))) +
      ((m:ℝ)+1)/2 * ((∫ s in (0:ℝ)..(1 + U (-v₀)), igAsy_F m 1 s) -
        (∫ s in Ioi (1 + U v₀), igAsy_F m 1 s) +
        Real.exp (-((m:ℝ)+1) * v₀^2/2) * (-U (-v₀) - U v₀)) := by
  set n : ℝ := (m:ℝ)+1 with hn
  set F := igAsy_F m 1 with hF
  have hFc : Continuous F := by rw [hF]; unfold igAsy_F; fun_prop
  set g : ℝ → ℝ := fun v => Real.exp (-n * v^2/2) with hg
  have hgd : ∀ v, HasDerivAt g (-n * v * g v) v := fun v => by
    have := (((hasDerivAt_pow 2 v).const_mul (-n)).div_const 2).exp
    convert this using 1
    simp only [hg]; push_cast; ring
  have hgc : Continuous g := by rw [hg]; fun_prop
  have hUc : ContinuousOn U (Icc (-v₀) v₀) := fun v hv =>
    (hd v hv).1.continuousAt.continuousWithinAt
  have hU'c : ContinuousOn (deriv U) (Icc (-v₀) v₀) := fun v hv =>
    (hd v hv).2.1.continuousWithinAt
  have hIcc1 : uIcc (-v₀) 0 ⊆ Icc (-v₀) v₀ := by
    rw [uIcc_of_le (by linarith)]; exact Icc_subset_Icc le_rfl hv₀.le
  have hIcc2 : uIcc 0 v₀ ⊆ Icc (-v₀) v₀ := by
    rw [uIcc_of_le hv₀.le]; exact Icc_subset_Icc (by linarith) le_rfl
  have hFU : ∀ v ∈ Icc (-v₀) v₀, F (1 + U v) = g v := fun v hv => by
    rw [hF, igAsy_F_one_add m (by linarith [(hd v hv).2.2.1]), (hd v hv).2.2.2, hg]
    congr 1; ring
  -- substitution
  have hsub : ∀ {a b : ℝ}, uIcc a b ⊆ Icc (-v₀) v₀ →
      ∫ v in a..b, g v * deriv U v = ∫ s in (1 + U a)..(1 + U b), F s := by
    intro a b hab
    rw [← intervalIntegral.integral_comp_mul_deriv (f := fun v => 1 + U v) (f' := deriv U)
      (fun x hx => ((hd x (hab hx)).1.const_add 1)) (hU'c.mono hab) hFc]
    refine intervalIntegral.integral_congr fun v hv => ?_
    simp only [Function.comp_apply, hFU v (hab hv)]
  -- integration by parts
  have hibp : ∀ {a b : ℝ}, uIcc a b ⊆ Icc (-v₀) v₀ →
      ∫ v in a..b, g v * deriv U v = g b * U b - g a * U a - ∫ v in a..b, (-n * v * g v) * U v := by
    intro a b hab
    exact intervalIntegral.integral_mul_deriv_eq_deriv_mul (fun x _ => hgd x)
      (fun x hx => (hd x (hab hx)).1)
      ((by fun_prop : Continuous fun v => -n * v * g v).intervalIntegrable _ _)
      ((hU'c.mono hab).intervalIntegrable)
  have h1 := hsub hIcc1
  have h2 := hsub hIcc2
  rw [hibp hIcc1] at h1
  rw [hibp hIcc2] at h2
  rw [hU0, add_zero] at h1 h2
  -- reflection
  have hrefl : ∫ v in (-v₀)..0, (-n * v * g v) * U v = ∫ v in (0:ℝ)..v₀, (n * v * g v) * U (-v) := by
    have := intervalIntegral.integral_comp_neg (a := 0) (b := v₀)
      (fun v => (-n * v * g v) * U v)
    rw [neg_zero] at this
    rw [← this]
    refine intervalIntegral.integral_congr fun v _ => ?_
    simp only [hg]; ring_nf
  rw [hrefl] at h1
  -- the Gaussian integral
  have hUc2 : ContinuousOn U (uIcc 0 v₀) := hUc.mono hIcc2
  have hUn : ContinuousOn (fun v => U (-v)) (uIcc 0 v₀) := hUc.comp continuousOn_neg
    (fun v hv => by
      rw [uIcc_of_le hv₀.le] at hv
      exact ⟨by linarith [hv.2], by linarith [hv.1]⟩)
  have hi1 : IntervalIntegrable (fun v => (n * v * g v) * U (-v)) volume 0 v₀ :=
    ((by fun_prop : Continuous fun v => n * v * g v).continuousOn.mul hUn).intervalIntegrable
  have hi2 : IntervalIntegrable (fun v => (-n * v * g v) * U v) volume 0 v₀ :=
    ((by fun_prop : Continuous fun v => -n * v * g v).continuousOn.mul hUc2).intervalIntegrable
  have hI : n * ∫ v in (0:ℝ)..v₀, Real.exp (-n * v^2/2) * (v * (-U (-v) - U v)) =
      -(∫ v in (0:ℝ)..v₀, (n * v * g v) * U (-v)) + ∫ v in (0:ℝ)..v₀, (-n * v * g v) * U v := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_neg,
      ← intervalIntegral.integral_add (f := fun v => -((n * v * g v) * U (-v))) hi1.neg hi2]
    refine intervalIntegral.integral_congr fun v _ => ?_
    simp only [hg]; ring
  -- splitting the integrals
  obtain ⟨hFi, hFI⟩ := igAsy_integral_F_Ioi m
  have hb1 : 0 < 1 + U (-v₀) := by linarith [(hd (-v₀) ⟨le_rfl, by linarith⟩).2.2.1]
  have ha1 : (1:ℝ) ≤ 1 + U v₀ := by linarith
  have hs1 : ∫ s in (0:ℝ)..1, F s = (∫ s in (0:ℝ)..(1 + U (-v₀)), F s) +
      ∫ s in (1 + U (-v₀))..1, F s :=
    (intervalIntegral.integral_add_adjacent_intervals (hFc.intervalIntegrable _ _)
      (hFc.intervalIntegrable _ _)).symm
  have hs2 : ∫ s in Ioi (0:ℝ), F s = (∫ s in (0:ℝ)..1, F s) + ((∫ s in (1:ℝ)..(1 + U v₀), F s) +
      ∫ s in Ioi (1 + U v₀), F s) := by
    rw [← Ioc_union_Ioi_eq_Ioi zero_le_one, setIntegral_union Ioc_disjoint_Ioi_same
      measurableSet_Ioi (hFi.mono_set Ioc_subset_Ioi_self) (hFi.mono_set (Ioi_subset_Ioi
      zero_le_one)), ← Ioc_union_Ioi_eq_Ioi ha1, setIntegral_union Ioc_disjoint_Ioi_same
      measurableSet_Ioi (hFi.mono_set (Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi zero_le_one)))
      (hFi.mono_set (Ioi_subset_Ioi (by linarith))), intervalIntegral.integral_of_le zero_le_one,
      intervalIntegral.integral_of_le ha1]
  have hfac : ((m+1).factorial : ℝ) * Real.exp n / (2 * n^(m+1)) =
      n/2 * ∫ s in Ioi (0:ℝ), F s := by
    rw [hF, hFI]
    have : (0:ℝ) < n := by positivity
    field_simp
    ring
  rw [hfac, hs2, hs1]
  have hg0 : g 0 = 1 := by simp [hg]
  have hgv : g v₀ = Real.exp (-n * v₀^2/2) := rfl
  have hgv' : g (-v₀) = Real.exp (-n * v₀^2/2) := by simp [hg]
  rw [hgv', hg0] at h1
  rw [hgv, hg0] at h2
  linear_combination (n/2) * (h2 - h1 - hI)

/-- `x^{-(j+1)} = (x^{j+1})⁻¹` for `x > 0`. -/
theorem igAsy_rpow_neg_succ {x : ℝ} (hx : 0 < x) (j : ℕ) : x ^ (-((j:ℝ)+1)) = (x^(j+1))⁻¹ := by
  rw [Real.rpow_neg hx.le, show (j:ℝ)+1 = ((j+1:ℕ):ℝ) by push_cast; ring, Real.rpow_natCast]

/-- `n e^{-n κ} = O(n^{-N})`. -/
theorem igAsy_exp_small {κ : ℝ} (hκ : 0 < κ) (N : ℕ) :
    ∀ᶠ m : ℕ in atTop, ((m:ℝ)+1) * Real.exp (-((m:ℝ)+1) * κ) ≤
      κ⁻¹^(N+1) * (((m:ℝ)+1)^N)⁻¹ := by
  have h1 : Tendsto (fun m : ℕ => ((m:ℝ)+1) * κ) atTop atTop :=
    (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds).atTop_mul_const hκ
  have h2 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero (N+1)).comp h1
  filter_upwards [h2.eventually (ge_mem_nhds (zero_lt_one))] with m hm
  simp only [Function.comp_apply] at hm
  have hn : (0:ℝ) < (m:ℝ)+1 := by positivity
  rw [← mul_le_mul_iff_of_pos_left (pow_pos hκ (N+1)),
    ← mul_le_mul_iff_of_pos_left (pow_pos hn N)]
  calc ((m:ℝ)+1)^N * (κ^(N+1) * (((m:ℝ)+1) * Real.exp (-((m:ℝ)+1) * κ)))
      = (((m:ℝ)+1) * κ)^(N+1) * Real.exp (-(((m:ℝ)+1) * κ)) := by
        rw [mul_pow, show -(((m:ℝ)+1) * κ) = -((m:ℝ)+1) * κ by ring]; ring
    _ ≤ 1 := hm
    _ = ((m:ℝ)+1)^N * (κ^(N+1) * (κ⁻¹^(N+1) * (((m:ℝ)+1)^N)⁻¹)) := by
      rw [inv_pow]; field_simp

/-- expPartialSumRemainderS one asymptotic. -/
@[dlmf 8.11.E16]
theorem expPartialSumRemainderS_one_asymptotic  :
    ∃ c : ℕ → ℂ, (∀ n < 4, c n=([-2/3,4/135,-8/2835,-16/8505] : List ℂ)[n]!) ∧ HasAsymptoticExpansion atTop (fun j (n : ℕ) => (n+1 : ℂ)^(-(j : ℤ))) c (fun n => expPartialSumRemainderS (n+1) 1-(n+1).factorial*exp (n+1 : ℂ)/(2*(n+1 : ℂ)^(n+1))) := by
  obtain ⟨U, p, v₀, hv₀, hp, hc, hd, hb, ha⟩ := igAsy_saddle
  have hc0 : p.coeff 0 = 0 := (hc 0 (by norm_num)).trans (by simp [igAsy_Pc])
  have hU0 : U 0 = 0 := by rw [← hp.coeff_zero 1]; exact hc0
  have hUc : ContinuousOn U (Icc (-v₀) v₀) := fun v hv =>
    (hd v hv).1.continuousAt.continuousWithinAt
  set γ : ℕ → ℝ := fun j => Real.Gamma ((j:ℝ)+1) * (2^j * (-2 * p.coeff (2*j))) with hγ
  have hγ0 : γ 0 = 0 := by simp [hγ, hc0]
  have hγs : ∀ k, γ (k+1) / 2 = -((k+1).factorial : ℝ) * 2^(k+1) * p.coeff (2*k+2) := by
    intro k
    simp only [hγ]
    rw [show ((k+1:ℕ):ℝ)+1 = ((k+1:ℕ):ℝ)+1 from rfl, Real.Gamma_nat_eq_factorial,
      show 2*(k+1) = 2*k+2 by ring]
    ring
  have H := lapSad_hasAsymptoticExpansion_gauss_analytic hp hv₀ hUc
  refine ⟨fun k => ((γ (k+1) / 2 : ℝ) : ℂ), ?_, ?_⟩
  · intro k hk
    interval_cases k <;>
      norm_num [hγs, hc 2 (by norm_num), hc 4 (by norm_num), hc 6 (by norm_num),
        hc 8 (by norm_num), igAsy_Pc, Nat.factorial]
  intro N
  have hnat : Tendsto (fun m : ℕ => (m:ℝ)+1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  obtain ⟨C, hC⟩ := ((H (N+1)).comp_tendsto hnat).bound
  set κ : ℝ := v₀^2/2 with hκ
  have hκ0 : 0 < κ := by positivity
  set a := U v₀
  set b := U (-v₀)
  set K : ℝ := (1 + b) + (1 + a)/a + |-b - a| with hK
  have hφb : igAsy_phi b = κ := by
    rw [(hd (-v₀) ⟨le_rfl, by linarith⟩).2.2.2]; ring
  have hφa : igAsy_phi a = κ := (hd v₀ ⟨by linarith, le_rfl⟩).2.2.2
  have hb1 : 0 < 1 + b := by linarith [(hd (-v₀) ⟨le_rfl, by linarith⟩).2.2.1]
  refine IsBigO.of_bound (C/2 + K/2 * κ⁻¹^(N+1)) ?_
  filter_upwards [hC, igAsy_exp_small hκ0 N] with m hCm hEm
  simp only [Function.comp_apply] at hCm
  set n : ℝ := (m:ℝ)+1 with hn
  have hn0 : 0 < n := by positivity
  have hn1 : 1 ≤ n := by simp [hn]
  have hdec := igAsy_one_decomp hv₀ hU0 hd ha m
  obtain ⟨hL0, hL1⟩ := igAsy_left_tail m hb1 (by linarith)
  obtain ⟨hR0, hR1⟩ := igAsy_right_tail m ha
  rw [add_sub_cancel_left, hφb] at hL1
  rw [hφa] at hR1
  set I := ∫ v in (0:ℝ)..v₀, Real.exp (-n * v^2/2) * (v * (-U (-v) - U v))
  set TL := ∫ s in (0:ℝ)..(1 + b), igAsy_F m 1 s
  set TR := ∫ s in Ioi (1 + a), igAsy_F m 1 s
  set E := Real.exp (-n * κ) with hE
  have hE' : Real.exp (-n * v₀^2/2) = E := by rw [hE, hκ]; congr 1; ring
  rw [hE'] at hdec
  -- the real form of the function
  have hfun : expPartialSumRemainderS (m+1) 1 - ((m+1).factorial : ℂ) * Complex.exp ((m:ℂ)+1) /
      (2*((m:ℂ)+1)^(m+1)) = ((n^2/2 * I + n/2 * (TL - TR + E * (-b - a)) : ℝ) : ℂ) := by
    rw [← hdec, igAsy_S_eq]
    push_cast
    rfl
  have hsumC : ∑ j ∈ Finset.range N, ((m:ℂ)+1)^(-(j:ℤ)) • (((γ (j+1) / 2 : ℝ)) : ℂ) =
      ((∑ j ∈ Finset.range N, (n^j)⁻¹ * (γ (j+1) / 2) : ℝ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [zpow_neg, zpow_natCast, smul_eq_mul, hn]
    push_cast
    ring
  have hsumR : ∑ j ∈ Finset.range N, (n^j)⁻¹ * (γ (j+1) / 2) =
      n^2/2 * ∑ j ∈ Finset.range (N+1), n ^ (-((j:ℝ)+1)) • γ j := by
    rw [Finset.sum_range_succ', hγ0, smul_zero, add_zero, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_eq_mul, igAsy_rpow_neg_succ hn0 (j+1)]
    field_simp
    ring
  have hnorm : ‖((m:ℂ)+1)^(-(N:ℤ))‖ = (n^N)⁻¹ := by
    rw [zpow_neg, zpow_natCast, norm_inv, norm_pow,
      show ‖(m:ℂ)+1‖ = (m:ℝ)+1 by exact_mod_cast Complex.norm_natCast (m+1)]
  rw [igAsy_rpow_neg_succ hn0 (N+1), Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (inv_pos.2 (pow_pos hn0 _))] at hCm
  rw [hfun, hsumC, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, hsumR, hnorm]
  set T := TL - TR + E * (-b - a) with hT
  set Ss := ∑ j ∈ Finset.range (N+1), n ^ (-((j:ℝ)+1)) • γ j
  have hEp : 0 < E := Real.exp_pos _
  have hK0 : 0 ≤ K := by
    rw [hK]; have := div_pos (by linarith : 0 < 1 + a) ha; positivity
  have hTb : |T| ≤ K * E := by
    have h1 : (1+a)/(n*a) ≤ (1+a)/a :=
      div_le_div_of_nonneg_left (by linarith) ha (by nlinarith)
    have h2 := hR1.trans (mul_le_mul_of_nonneg_left h1 hEp.le)
    have h3 := mul_le_mul_of_nonneg_left (le_abs_self (-b - a)) hEp.le
    have h4 := mul_le_mul_of_nonneg_left (neg_abs_le (-b - a)) hEp.le
    have h5 : K*E = (1+b)*E + E*((1+a)/a) + E*|-b-a| := by rw [hK]; ring
    have h6 : 0 ≤ (1+b)*E := by positivity
    have h7 : 0 ≤ E*((1+a)/a) := mul_nonneg hEp.le (div_pos (by linarith) ha).le
    rw [abs_le]; constructor <;> linarith
  calc |n^2/2 * I + n/2 * T - n^2/2 * Ss| = |n^2/2 * (I - Ss) + n/2 * T| := by ring_nf
    _ ≤ n^2/2 * |I - Ss| + n/2 * |T| := by
      refine (abs_add_le _ _).trans (le_of_eq ?_)
      rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0:ℝ) < n^2/2),
        abs_of_pos (by positivity : (0:ℝ) < n/2)]
    _ ≤ n^2/2 * (C * (n^(N+1+1))⁻¹) + K/2 * (n * E) := by
      have := mul_le_mul_of_nonneg_left hTb (by positivity : (0:ℝ) ≤ n/2)
      exact add_le_add (mul_le_mul_of_nonneg_left hCm (by positivity))
        (this.trans (le_of_eq (by ring)))
    _ ≤ n^2/2 * (C * (n^(N+1+1))⁻¹) + K/2 * (κ⁻¹^(N+1) * (n^N)⁻¹) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hEm (by positivity))
    _ = (C/2 + K/2 * κ⁻¹^(N+1)) * (n^N)⁻¹ := by
      field_simp
      ring

/-- expPartialSumRemainderS neg one asymptotic. -/
@[dlmf 8.11.E17]
theorem expPartialSumRemainderS_neg_one_asymptotic  :
    ∃ c : ℕ → ℂ, (∀ n < 5, c n=([-1/2,1/8,1/32,-1/128,-13/512] : List ℂ)[n]!) ∧ HasAsymptoticExpansion atTop (fun j (n : ℕ) => (n+1 : ℂ)^(-(j : ℤ))) c (fun n => expPartialSumRemainderS (n+1) (-1)) := by
  refine ⟨fun k => (igAsy_d k (-1) : ℂ), ?_, ?_⟩
  · intro n hn
    interval_cases n <;>
      norm_num [igAsy_d, igAsy_h, igAsy_poly, Polynomial.derivative_mul]
  · intro N
    obtain ⟨C, hC⟩ := igAsy_S_remainder_bound N (δ := 1) one_pos
    refine IsBigO.of_bound C (Eventually.of_forall fun n => ?_)
    have hm : (0:ℝ) < (n:ℝ)+1 := by positivity
    have hsum : ∑ j ∈ Finset.range N, ((n:ℂ)+1)^(-(j:ℤ)) • (igAsy_d j (-1) : ℂ) =
        ∑ k ∈ Finset.range N, (igAsy_d k (-1) : ℂ)/((n:ℂ)+1)^k := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_eq_mul, zpow_neg, zpow_natCast, div_eq_mul_inv, mul_comm]
    rw [hsum]
    dsimp only
    rw [zpow_neg, zpow_natCast, norm_inv, norm_pow,
      show ‖(n:ℂ)+1‖ = (n:ℝ)+1 by exact_mod_cast Complex.norm_natCast (n+1), ← one_div]
    exact hC n (-1) (by norm_num)

/-- The coefficients d_k(x). -/
@[dlmf 8.11.E19]
def expPartialSumRemainderCoeff (k : ℕ) (x : ℝ) : ℂ :=
  if k=0 then x/(1-x) else (-1 : ℂ)^k*(incGammaLambdaPolynomial k).eval (x : ℂ)/(1-x : ℂ)^(2*k+1)

/-- `b_k = X p_k` for `k ≥ 1`. -/
theorem igAsy_lambdaPoly_eq {k : ℕ} (hk : 1 ≤ k) :
    incGammaLambdaPolynomial k = Polynomial.X * (igAsy_poly k).map (algebraMap ℝ ℂ) := by
  induction k, hk using Nat.le_induction with
  | base =>
    simp [incGammaLambdaPolynomial, igAsy_poly]
  | succ k hk ih =>
    rw [incGammaLambdaPolynomial, ih, igAsy_poly]
    simp only [Polynomial.derivative_mul, Polynomial.derivative_X, Polynomial.map_add,
      Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_one, Polynomial.map_X,
      Polynomial.map_C, Polynomial.derivative_map]
    simp
    ring

/-- `b_k(x) = x p_k(x)` for `k ≥ 1`, evaluated at a real point. -/
theorem igAsy_lambdaPoly_eval {k : ℕ} (hk : 1 ≤ k) (x : ℝ) :
    (incGammaLambdaPolynomial k).eval (x : ℂ) = x * (((igAsy_poly k).eval x : ℝ) : ℂ) := by
  rw [igAsy_lambdaPoly_eq hk, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_map,
    show (x:ℂ) = algebraMap ℝ ℂ x from rfl, Polynomial.eval₂_at_apply]
  rfl

/-- The coefficients `d_k(x)` of 8.11.19 in terms of `h_k`. -/
theorem igAsy_coeff_eq (k : ℕ) {x : ℝ} (hx : x ≠ 1) :
    expPartialSumRemainderCoeff k x = (igAsy_d k x : ℂ) := by
  unfold igAsy_d
  have hx1 : (1:ℂ) - x ≠ 0 := by
    rw [sub_ne_zero]; exact_mod_cast hx.symm
  unfold expPartialSumRemainderCoeff
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [igAsy_h_zero]
  · simp only [hk.ne', ↓reduceIte]
    rw [igAsy_lambdaPoly_eval hk, igAsy_h]
    push_cast
    rw [pow_succ]
    field_simp

/-- expPartialSumRemainderS uniform asymptotic. -/
@[dlmf 8.11.E18]
theorem expPartialSumRemainderS_uniform_asymptotic {δ : ℝ} (hδ : 0 < δ) (N : ℕ) :
    IsBigO (comap (fun p : ℕ × ℝ => p.1) atTop ⊓ 𝓟 {p : ℕ × ℝ | p.2 ≤ 1-δ}) (fun p => expPartialSumRemainderS (p.1+1) p.2-∑ k ∈ Finset.range N, expPartialSumRemainderCoeff k p.2/(p.1+1 : ℂ)^k) (fun p => (p.1+1 : ℝ)^(-(N : ℤ))) := by
  obtain ⟨C, hC⟩ := igAsy_S_remainder_bound N hδ
  refine IsBigO.of_bound C ?_
  filter_upwards [mem_inf_of_right (mem_principal_self _)] with p hp
  have hp' : p.2 ≠ 1 := fun h => by have : p.2 ≤ 1-δ := hp; linarith
  rw [Finset.sum_congr rfl fun k _ => by rw [igAsy_coeff_eq k hp']]
  have hm : (0:ℝ) < (p.1:ℝ)+1 := by positivity
  rw [Real.norm_eq_abs, zpow_neg, zpow_natCast, abs_inv, abs_of_pos (by positivity), ← one_div]
  exact hC p.1 p.2 hp


/-! ### The central expansion 8.11.10 (helper prefix `igCen_`)

The statements 8.11.10–8.11.11 were moved verbatim to the end of the file, after the saddle
substitution `igAsy_saddle` that their proofs use. -/


/-- `d/dt (-t²) = -2t`. -/
theorem igCen_hasDerivAt_neg_sq (x : ℝ) : HasDerivAt (fun t : ℝ => -t^2) (-(2*x)) x := by
  convert (hasDerivAt_pow 2 x).const_mul (-1:ℝ) using 1
  · funext t; ring
  · push_cast; ring

/-- `|e^{-s²} - e^{-y²}| ≤ |s - y|`. -/
theorem igCen_exp_neg_sq_lip (s y : ℝ) : |Real.exp (-s^2) - Real.exp (-y^2)| ≤ |s - y| := by
  have hd : ∀ x : ℝ, HasDerivAt (fun t : ℝ => Real.exp (-t^2)) (-(2*x) * Real.exp (-x^2)) x :=
    fun x => by
      have h := igCen_hasDerivAt_neg_sq x
      convert h.exp using 1; ring
  have hb : ∀ x : ℝ, ‖-(2*x) * Real.exp (-x^2)‖ ≤ 1 := fun x => by
    rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_pos (Real.exp_pos _), abs_mul,
      abs_two]
    have h1 : 1 + x^2 ≤ Real.exp (x^2) := by linarith [Real.add_one_le_exp (x^2)]
    have h2 : 2*|x| ≤ 1 + x^2 := by nlinarith [sq_abs x, sq_nonneg (|x| - 1)]
    have h3 : Real.exp (-x^2) * Real.exp (x^2) = 1 := by rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos (-x^2)]
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := fun t : ℝ => Real.exp (-t^2))
    (fun x _ => (hd x).hasDerivWithinAt) (fun x _ => hb x) convex_univ (mem_univ y) (mem_univ s)
  simpa [Real.norm_eq_abs] using this

/-- Linearisation of `erf`: `|erf T - erf y - (2/√π)(T-y)e^{-y²}| ≤ (2/√π)(T-y)²`. -/
theorem igCen_erf_sub (T y : ℝ) :
    |TauCeti.Real.erf T - TauCeti.Real.erf y - 2/Real.sqrt π * (T - y) * Real.exp (-y^2)| ≤
      2/Real.sqrt π * (T - y)^2 := by
  have hc : Continuous fun t : ℝ => Real.exp (-t^2) := by fun_prop
  have h1 : TauCeti.Real.erf T - TauCeti.Real.erf y =
      2/Real.sqrt π * ∫ t in y..T, Real.exp (-t^2) := by
    rw [TauCeti.Real.erf_def, TauCeti.Real.erf_def, ← mul_sub,
      intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable _ _)
        (hc.intervalIntegrable _ _)]
  have h2 : (∫ t in y..T, Real.exp (-t^2)) - (T - y) * Real.exp (-y^2) =
      ∫ t in y..T, (Real.exp (-t^2) - Real.exp (-y^2)) := by
    rw [intervalIntegral.integral_sub (hc.intervalIntegrable _ _) intervalIntegrable_const,
      intervalIntegral.integral_const, smul_eq_mul]
  have h3 : ‖∫ t in y..T, (Real.exp (-t^2) - Real.exp (-y^2))‖ ≤ |T - y| * |T - y| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun t ht => ?_
    rw [Real.norm_eq_abs]
    refine (igCen_exp_neg_sq_lip t y).trans ?_
    rcases le_total y T with h | h
    · rw [uIoc_of_le h] at ht
      rw [abs_of_nonneg (by linarith [ht.1]), abs_of_nonneg (by linarith)]; linarith [ht.2]
    · rw [uIoc_of_ge h] at ht
      rw [abs_of_nonpos (by linarith [ht.2]), abs_of_nonpos (by linarith)]; linarith [ht.1]
  have hp : 0 < 2/Real.sqrt π := by positivity
  rw [show TauCeti.Real.erf T - TauCeti.Real.erf y - 2/Real.sqrt π * (T - y) * Real.exp (-y^2) =
    2/Real.sqrt π * ((∫ t in y..T, Real.exp (-t^2)) - (T - y) * Real.exp (-y^2)) by rw [h1]; ring,
    h2, abs_mul, abs_of_pos hp]
  rw [Real.norm_eq_abs, abs_mul_abs_self] at h3
  gcongr
  nlinarith [h3]

/-- Gaussian tail: `1 - erf M ≤ e^{-M²}/M` for `M > 0`. -/
theorem igCen_one_sub_erf_le {M : ℝ} (hM : 0 < M) :
    1 - TauCeti.Real.erf M ≤ Real.exp (-M^2) / M := by
  have hc : Continuous fun t : ℝ => Real.exp (-t^2) := by fun_prop
  have hsp : 1 ≤ Real.sqrt π := by
    rw [Real.one_le_sqrt]; linarith [Real.pi_gt_three]
  have hX : ∀ X, M ≤ X → TauCeti.Real.erf X ≤ TauCeti.Real.erf M + Real.exp (-M^2) / M := by
    intro X hX
    have h1 : TauCeti.Real.erf X - TauCeti.Real.erf M =
        2/Real.sqrt π * ∫ t in M..X, Real.exp (-t^2) := by
      rw [TauCeti.Real.erf_def, TauCeti.Real.erf_def, ← mul_sub,
        intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable _ _)
          (hc.intervalIntegrable _ _)]
    have h2 : ∫ t in M..X, Real.exp (-t^2) ≤ ∫ t in M..X, t / M * Real.exp (-t^2) :=
      intervalIntegral.integral_mono_on hX (hc.intervalIntegrable _ _)
        ((by fun_prop : Continuous fun t : ℝ => t / M * Real.exp (-t^2)).intervalIntegrable _ _)
        fun t ht => by
          have : 1 ≤ t / M := by rw [le_div_iff₀ hM]; linarith [ht.1]
          nlinarith [Real.exp_pos (-t^2)]
    have h3 : ∫ t in M..X, t / M * Real.exp (-t^2) =
        (Real.exp (-M^2) - Real.exp (-X^2)) / (2*M) := by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t => -Real.exp (-t^2) / (2*M))
        (fun t _ => by
          have h := igCen_hasDerivAt_neg_sq t
          convert (h.exp.neg).div_const (2*M) using 1; field_simp)
        ((by fun_prop : Continuous fun t : ℝ => t / M * Real.exp (-t^2)).intervalIntegrable _ _)]
      ring
    have h4 : (Real.exp (-M^2) - Real.exp (-X^2)) / (2*M) ≤ Real.exp (-M^2) / (2*M) := by
      gcongr; linarith [Real.exp_pos (-X^2)]
    have h5 : 2/Real.sqrt π * (Real.exp (-M^2) / (2*M)) ≤ Real.exp (-M^2) / M := by
      rw [show 2/Real.sqrt π * (Real.exp (-M^2) / (2*M)) = Real.exp (-M^2) / M / Real.sqrt π by
        field_simp]
      exact div_le_self (by positivity) hsp
    have hp : 0 ≤ 2/Real.sqrt π := by positivity
    nlinarith [mul_le_mul_of_nonneg_left (h2.trans (h3 ▸ h4)) hp]
  have := le_of_tendsto TauCeti.Real.tendsto_erf_atTop (eventually_atTop.2 ⟨M, hX⟩)
  linarith

/-- `e^{-x} ≤ 2/x²` for `x > 0`. -/
theorem igCen_exp_neg_le {x : ℝ} (hx : 0 < x) : Real.exp (-x) ≤ 2 / x^2 := by
  have h := Real.pow_div_factorial_le_exp x hx.le 2
  rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos x) (by positivity)]
  norm_num [Nat.factorial] at h
  linarith

/-- Cubic Taylor bound for `φ(u) = u - log(1+u)`. -/
theorem igCen_phi_cubic {u : ℝ} (hu : |u| ≤ 1/2) :
    |igAsy_phi u - u^2/2 + u^3/3| ≤ 2*|u|^4 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := -u) (by rw [abs_neg]; linarith) 3
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, abs_neg, sub_neg_eq_add] at h
  have hu1 : 0 < 1 - |u| := by linarith
  have h2 : |u|^(3+1) / (1 - |u|) ≤ 2*|u|^4 := by
    rw [div_le_iff₀ hu1, show 3+1 = 4 from rfl]; nlinarith [pow_nonneg (abs_nonneg u) 4]
  have h3 : igAsy_phi u - u^2/2 + u^3/3 = -(0 + (-u)^(0+1)/((0:ℕ)+1) + (-u)^(1+1)/((1:ℕ)+1) +
      (-u)^(2+1)/((2:ℕ)+1) + Real.log (1 + u)) := by
    unfold igAsy_phi; push_cast; ring
  rw [h3, abs_neg]
  exact h.trans h2

/-- If `v² = 2φ(u)` and `uv ≥ 0`, then `v = u - u²/3 + O(u³)`. -/
theorem igCen_v_approx {u v : ℝ} (hu : |u| ≤ 1/2) (hv : v^2 = 2*igAsy_phi u) (huv : 0 ≤ u*v) :
    |v - (u - u^2/3)| ≤ 6*|u|^3 := by
  set w := u - u^2/3 with hw
  have hφ := igCen_phi_cubic hu
  have hu4 : |u|^4 ≤ |u|^3 / 2 := by
    rw [pow_succ]; nlinarith [pow_nonneg (abs_nonneg u) 3]
  have hd : |v^2 - w^2| ≤ 5*|u|^4 := by
    rw [hv, hw]
    have : 2*igAsy_phi u - (u - u^2/3)^2 = 2*(igAsy_phi u - u^2/2 + u^3/3) - u^4/9 := by ring
    rw [this]
    have : |u^4/9| = |u|^4/9 := by rw [abs_div, abs_pow]; norm_num
    calc _ ≤ |2*(igAsy_phi u - u^2/2 + u^3/3)| + |u^4/9| := abs_sub _ _
      _ ≤ 2*(2*|u|^4) + |u|^4/9 := by rw [abs_mul, abs_two, this]; gcongr
      _ ≤ 5*|u|^4 := by nlinarith [pow_nonneg (abs_nonneg u) 4]
  rcases eq_or_ne u 0 with h0 | h0
  · subst h0
    have : v = 0 := by
      have : v^2 = 0 := by rw [hv]; simp [igAsy_phi]
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
    simp [this, hw]
  have hpos : 0 < |u| := abs_pos.2 h0
  have hwu : (5/6)*|u| ≤ |w| := by
    rw [hw, show u - u^2/3 = u*(1 - u/3) by ring, abs_mul]
    have : 5/6 ≤ |1 - u/3| := by
      rw [abs_of_pos (by linarith [neg_abs_le u, le_abs_self u])]
      linarith [le_abs_self u]
    nlinarith
  have hvw : 0 ≤ v*w := by
    rw [hw, show v*(u - u^2/3) = (u*v)*(1 - u/3) by ring]
    exact mul_nonneg huv (by linarith [le_abs_self u])
  have hsum : |w| ≤ |v + w| := by
    rcases le_total 0 w with h | h
    · have : 0 ≤ v ∨ w = 0 := by
        rcases h.lt_or_eq with h' | h'
        · left; by_contra hc; push Not at hc; nlinarith
        · right; exact h'.symm
      rcases this with hv0 | hw0
      · rw [abs_of_nonneg h, abs_of_nonneg (by linarith)]; linarith
      · rw [hw0]; simp
    · have : v ≤ 0 ∨ w = 0 := by
        rcases h.lt_or_eq with h' | h'
        · left; by_contra hc; push Not at hc; nlinarith
        · right; exact h'
      rcases this with hv0 | hw0
      · rw [abs_of_nonpos h, abs_of_nonpos (by linarith)]; linarith
      · rw [hw0]; simp
  have hm : |v - w| * |v + w| ≤ 5*|u|^4 := by
    rw [← abs_mul, show (v - w)*(v + w) = v^2 - w^2 by ring]; exact hd
  have hvw' : (5/6)*|u| ≤ |v + w| := hwu.trans hsum
  have : |v - w| * ((5/6)*|u|) ≤ 5*|u|^4 :=
    (mul_le_mul_of_nonneg_left hvw' (abs_nonneg _)).trans hm
  have h6 : 5*|u|^4 = (6*|u|^3) * ((5/6)*|u|) := by ring
  rw [h6] at this
  exact le_of_mul_le_mul_right this (by positivity)



/-- `φ'(u) = 1 - 1/(1+u)` for `u > -1`. -/
theorem igCen_hasDerivAt_phi {u : ℝ} (hu : -1 < u) :
    HasDerivAt igAsy_phi (1 - 1/(1+u)) u := by
  have h1 : HasDerivAt (fun w : ℝ => 1 + w) 1 u := (hasDerivAt_id u).const_add 1
  have h2 := (Real.hasDerivAt_log (by linarith : (1+u) ≠ 0)).comp u h1
  have := (hasDerivAt_id u).sub h2
  convert this using 1
  · funext w; simp [igAsy_phi]
  · simp [one_div]

/-- The saddle substitution `U` of `igAsy_saddle` restricted to a small interval `[-w₀, w₀]`,
with `U'(v) = 1 + 2v/3 + O(v²)` and `vU(v) ≥ 0`. -/
theorem igCen_U : ∃ (U : ℝ → ℝ) (w₀ C₂ : ℝ), 0 < w₀ ∧ w₀ ≤ 1/2 ∧ 0 ≤ C₂ ∧
    (∀ v ∈ Icc (-w₀) w₀, HasDerivAt U (deriv U v) v ∧ ContinuousAt (deriv U) v ∧
      -1/2 < U v ∧ igAsy_phi (U v) = v^2/2 ∧ 0 ≤ v * U v ∧
      |deriv U v - 1 - 2/3*v| ≤ C₂ * v^2) ∧ U (-w₀) < 0 ∧ 0 < U w₀ := by
  obtain ⟨U, p, v₀, hv₀, hp, hc, hd, -, -⟩ := igAsy_saddle
  have hc0 : p.coeff 0 = 0 := (hc 0 (by norm_num)).trans (by simp [igAsy_Pc])
  have hU0 : U 0 = 0 := by rw [← hp.coeff_zero 1]; exact hc0
  have hc1 : p.coeff 1 = 1 := (hc 1 (by norm_num)).trans (by simp [igAsy_Pc])
  have hc2 : p.coeff 2 = 1/3 := (hc 2 (by norm_num)).trans (by simp [igAsy_Pc])
  have hO := hp.isBigO_sub_partialSum_pow 3
  simp only [zero_add, FormalMultilinearSeries.partialSum,
    FormalMultilinearSeries.apply_eq_pow_smul_coeff, smul_eq_mul] at hO
  obtain ⟨c, hcpos, hcb⟩ := hO.exists_pos
  rw [isBigOWith_iff] at hcb
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hcb
  have hr : ∀ v : ℝ, |v| < ε → |U v - v - v^2/3| ≤ c * |v|^3 := by
    intro v hv
    have := hball (by simpa [Real.dist_eq] using hv)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, hc0, hc1, hc2, Real.norm_eq_abs] at this
    rw [abs_of_nonneg (pow_nonneg (abs_nonneg v) 3)] at this
    convert this using 2
    ring
  set w₀ := min (v₀/2) (min (ε/2) (1/(3*(1+c)))) with hw₀
  have hw0 : 0 < w₀ := by positivity
  have hw1 : w₀ ≤ v₀/2 := min_le_left _ _
  have hw2 : w₀ ≤ ε/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hw3 : w₀ ≤ 1/(3*(1+c)) := (min_le_right _ _).trans (min_le_right _ _)
  have hw3' : w₀ * (3*(1+c)) ≤ 1 := by rwa [le_div_iff₀ (by positivity)] at hw3
  have hw4 : w₀ ≤ 1/3 := by nlinarith
  have hsmall : ∀ v ∈ Icc (-w₀) w₀, |v| ≤ w₀ := fun v hv => abs_le.2 ⟨hv.1, hv.2⟩
  have hrv : ∀ v ∈ Icc (-w₀) w₀, |U v - v - v^2/3| ≤ c * |v|^3 := fun v hv =>
    hr v (by linarith [hsmall v hv])
  have hUv : ∀ v ∈ Icc (-w₀) w₀, |U v - v| ≤ |v|/2 := by
    intro v hv
    have h1 := hrv v hv
    have h2 := hsmall v hv
    have h3 : c * |v| ≤ 1/3 := by nlinarith [abs_nonneg v]
    have h4 : |U v - v| ≤ |v^2/3| + |U v - v - v^2/3| := by
      have := abs_add_le (v^2/3) (U v - v - v^2/3)
      rwa [show v^2/3 + (U v - v - v^2/3) = U v - v by ring] at this
    have h5 : |v^2/3| = |v| *|v|/3 := by rw [abs_div, abs_pow, sq]; norm_num
    have h6 : c * |v|^3 = (c*|v|)*|v| *|v| := by ring
    rw [h5] at h4
    rw [h6] at h1
    have h7 : (c*|v|)*|v| *|v| ≤ (1/3)*|v| *|v| := by
      have := abs_nonneg v
      gcongr
    nlinarith [abs_nonneg v]
  have hIcc : ∀ v ∈ Icc (-w₀) w₀, v ∈ Icc (-v₀) v₀ := fun v hv =>
    ⟨by linarith [hv.1], by linarith [hv.2]⟩
  refine ⟨U, w₀, 2*(2*c+1), hw0, by linarith, by positivity, fun v hv => ?_, ?_, ?_⟩
  · obtain ⟨hUd, hUc, hU1, hUφ⟩ := hd v (hIcc v hv)
    refine ⟨hUd, hUc, hU1, hUφ, ?_, ?_⟩
    · have := hUv v hv
      have h2 : v * U v = v^2 + v * (U v - v) := by ring
      have h3 : |v * (U v - v)| ≤ |v| * (|v|/2) := by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left this (abs_nonneg v)
      have h4 := neg_abs_le (v * (U v - v))
      nlinarith [sq_abs v]
    · -- the derivative identity `U v · U' v = v (1 + U v)`
      have hnhds : Icc (-v₀) v₀ ∈ 𝓝 v := by
        apply Icc_mem_nhds <;> linarith [hv.1, hv.2]
      have hφU := (igCen_hasDerivAt_phi (by linarith : -1 < U v)).comp v hUd
      have hsq : HasDerivAt (fun w => igAsy_phi (U w)) v v := by
        have := (hasDerivAt_pow 2 v).div_const 2
        refine (this.congr_of_eventuallyEq ?_).congr_deriv (by push_cast; ring)
        filter_upwards [hnhds] with w hw
        exact (hd w hw).2.2.2
      have hid := hφU.unique hsq
      have hU1' : 0 < 1 + U v := by linarith
      have hkey : U v * deriv U v = v * (1 + U v) := by
        field_simp at hid
        linarith
      rcases eq_or_ne v 0 with h0 | h0
      · subst h0
        have : deriv U 0 = 1 := by rw [hp.deriv]; exact hc1
        simp [this]
      · have hvpos : 0 < |v| := abs_pos.2 h0
        have hUlow : |v|/2 ≤ |U v| := by
          have := hUv v hv
          have := abs_sub_abs_le_abs_sub v (U v)
          rw [abs_sub_comm] at this
          linarith
        set r := U v - v - v^2/3 with hrdef
        have hrb := hrv v hv
        have hid2 : (deriv U v - 1 - 2/3*v) * U v = -r + v^3/9 + v*r/3 := by
          rw [hrdef]; linear_combination hkey
        have hv1 : |v| ≤ 1 := by linarith [hsmall v hv]
        have hb : |-r + v^3/9 + v*r/3| ≤ (2*c+1) * |v|^3 := by
          have e1 : |-r + v^3/9 + v*r/3| ≤ |r| + |v|^3/9 + |v| *|r|/3 := by
            have := abs_add_le (-r + v^3/9) (v*r/3)
            have := abs_add_le (-r) (v^3/9)
            rw [abs_neg] at this
            have : |v^3/9| = |v|^3/9 := by rw [abs_div, abs_pow]; norm_num
            have : |v*r/3| = |v| *|r|/3 := by rw [abs_div, abs_mul]; norm_num
            linarith
          have e2 : |v| *|r| ≤ |r| := mul_le_of_le_one_left (abs_nonneg r) hv1
          have e3 : 0 ≤ |v|^3 := by positivity
          nlinarith
        have hm : |deriv U v - 1 - 2/3*v| * (|v|/2) ≤ (2*c+1) * |v|^3 := by
          calc |deriv U v - 1 - 2/3*v| * (|v|/2) ≤ |deriv U v - 1 - 2/3*v| * |U v| :=
                mul_le_mul_of_nonneg_left hUlow (abs_nonneg _)
            _ = |-r + v^3/9 + v*r/3| := by rw [← abs_mul, hid2]
            _ ≤ _ := hb
        have : (2*c+1) * |v|^3 = (2*(2*c+1) * v^2) * (|v|/2) := by
          rw [← sq_abs v]; ring
        rw [this] at hm
        exact le_of_mul_le_mul_right hm (by positivity)
  · have := hUv (-w₀) ⟨le_rfl, by linarith⟩
    rw [abs_neg, abs_of_pos hw0] at this
    linarith [le_abs_self (U (-w₀) - -w₀)]
  · have := hUv w₀ ⟨by linarith, le_rfl⟩
    rw [abs_of_pos hw0] at this
    linarith [neg_abs_le (U w₀ - w₀)]


/-- `(1+u)^a e^{-au} = e^{-aφ(u)}` for `u > -1`. -/
theorem igCen_kernel (a : ℝ) {u : ℝ} (hu : -1 < u) :
    (1+u)^a * Real.exp (-a*u) = Real.exp (-a * igAsy_phi u) := by
  rw [Real.rpow_def_of_pos (by linarith), ← Real.exp_add]
  unfold igAsy_phi
  congr 1; ring


/-- The substitution `t = a(1+u)` in `∫₀ˣ t^a e^{-t} dt`. -/
theorem igCen_integral_subst {a u₁ : ℝ} (ha : 0 < a) (hu : -1 ≤ u₁) :
    ∫ t in (0:ℝ)..a*(1+u₁), t^a * Real.exp (-t) =
      a^(a+1) * Real.exp (-a) * ∫ u in (-1:ℝ)..u₁, (1+u)^a * Real.exp (-a*u) := by
  have h := intervalIntegral.integral_comp_mul_add (a := -1) (b := u₁)
    (fun t : ℝ => t^a * Real.exp (-t)) ha.ne' a
  rw [show a * -1 + a = 0 by ring, show a*u₁ + a = a*(1+u₁) by ring] at h
  rw [← smul_eq_mul (a := a^(a+1) * Real.exp (-a)), ← intervalIntegral.integral_smul]
  have h2 : ∫ u in (-1:ℝ)..u₁, (fun t : ℝ => t^a * Real.exp (-t)) (a*u + a) =
      ∫ u in (-1:ℝ)..u₁, a^a * Real.exp (-a) * ((1+u)^a * Real.exp (-a*u)) := by
    refine intervalIntegral.integral_congr fun u hu' => ?_
    rw [uIcc_of_le hu] at hu'
    have h1u : 0 ≤ 1 + u := by linarith [hu'.1]
    simp only
    rw [show a*u + a = a*(1+u) by ring, Real.mul_rpow ha.le h1u,
      show -(a*(1+u)) = -a + -a*u by ring, Real.exp_add]
    ring
  rw [h2, intervalIntegral.integral_const_mul, smul_eq_mul] at h
  have h3 : ∫ t in (0:ℝ)..a*(1+u₁), t^a * Real.exp (-t) =
      a * (a^a * Real.exp (-a) * ∫ u in (-1:ℝ)..u₁, (1+u)^a * Real.exp (-a*u)) := by
    rw [h]; field_simp
  rw [h3, intervalIntegral.integral_smul]
  simp only [smul_eq_mul]
  rw [Real.rpow_add_one ha.ne']
  ring


/-- Stirling's formula with Binet's remainder: `a^{a+1} e^{-a}/Γ(a+1) = √a/√(2π) e^{-Φ(a)}`. -/
theorem igCen_stirling {a : ℝ} (ha : 0 < a) :
    a^(a+1) * Real.exp (-a) / Real.Gamma (a+1) =
      Real.sqrt a / Real.sqrt (2*π) * Real.exp (-DLMF.Gamma.binetIntegral a) := by
  have hG : Real.Gamma (a+1) = Real.exp (Real.log a + ((a - 1/2) * Real.log a - a +
      1/2 * Real.log (2*π) + DLMF.Gamma.binetIntegral a)) := by
    rw [Real.Gamma_add_one ha.ne', Real.exp_add, Real.exp_log ha,
      ← DLMF.Gamma.log_Gamma_eq_add_binetIntegral ha, Real.exp_log (Real.Gamma_pos_of_pos ha)]
  have h1 : a^(a+1) = Real.exp ((a+1) * Real.log a) := by
    rw [Real.rpow_def_of_pos ha]; ring_nf
  have h2 : Real.sqrt a = Real.exp (1/2 * Real.log a) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos ha]; ring_nf
  have h3 : Real.sqrt (2*π) = Real.exp (1/2 * Real.log (2*π)) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by positivity)]; ring_nf
  rw [hG, h1, h2, h3]
  simp only [div_eq_mul_inv, ← Real.exp_neg, ← Real.exp_add]
  congr 1; ring

/-- For real `a, x > 0`, the continued `P(a+1, x)` is the real integral
`(1/Γ(a+1)) ∫₀ˣ t^a e^{-t} dt`. -/
theorem igCen_normIncGammaP_eq {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    normIncGammaPContinued ((a:ℂ)+1) (x:ℂ) =
      (((∫ t in (0:ℝ)..x, t^a * Real.exp (-t)) / Real.Gamma (a+1) : ℝ) : ℂ) := by
  have hre : 0 < ((a:ℂ)+1).re := by simp; linarith
  have hnp : ∀ n : ℕ, (a:ℂ)+1 ≠ -n := by
    intro n h
    have := congrArg Complex.re h
    simp at this
    have : (0:ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  rw [normIncGammaPContinued_eq hnp, DLMF.Statistical.normIncGammaP,
    lowerIncGamma_eq_integral hre hx, show (a:ℂ)+1 = ((a+1:ℝ):ℂ) by push_cast; ring,
    Complex.Gamma_ofReal, show ((a+1:ℝ):ℂ) - 1 = (a:ℂ) by push_cast; ring]
  push_cast
  congr 1
  rw [← intervalIntegral.integral_ofReal]
  refine intervalIntegral.integral_congr fun t ht => ?_
  have ht0 : (0:ℝ) ≤ t := by rw [uIcc_of_le hx.le] at ht; exact ht.1
  push_cast
  rw [ofReal_cpow ht0]

/-- Continuity of `u ↦ (1+u)^a e^{-au}` for `a ≥ 0`. -/
theorem igCen_continuous_g {a : ℝ} (ha : 0 ≤ a) :
    Continuous fun u : ℝ => (1+u)^a * Real.exp (-a*u) :=
  ((Real.continuous_rpow_const ha).comp (continuous_const.add continuous_id)).mul (by fun_prop)

/-- `∫_α^β e^{-t²} dt = (√π/2)(erf β - erf α)`. -/
theorem igCen_integral_exp_neg_sq (α β : ℝ) :
    ∫ t in α..β, Real.exp (-t^2) =
      Real.sqrt π / 2 * (TauCeti.Real.erf β - TauCeti.Real.erf α) := by
  have hc : Continuous fun t : ℝ => Real.exp (-t^2) := by fun_prop
  rw [TauCeti.Real.erf_def, TauCeti.Real.erf_def, ← mul_sub,
    intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable _ _)
      (hc.intervalIntegrable _ _)]
  have : Real.sqrt π ≠ 0 := by positivity
  field_simp

/-- Gaussian integral over an interval through `erf`. -/
theorem igCen_integral_gauss {s : ℝ} (hs : 0 < s) (α β : ℝ) :
    ∫ v in α..β, Real.exp (-v^2/s^2) =
      s * (Real.sqrt π / 2) * (TauCeti.Real.erf (β/s) - TauCeti.Real.erf (α/s)) := by
  have h := intervalIntegral.integral_comp_mul_left (a := α) (b := β)
    (fun t : ℝ => Real.exp (-t^2)) (inv_ne_zero hs.ne')
  calc ∫ v in α..β, Real.exp (-v^2/s^2) = ∫ v in α..β, Real.exp (-(s⁻¹ * v)^2) := by
        congr 1; funext v; congr 1; field_simp
    _ = _ := by
        rw [h, igCen_integral_exp_neg_sq, inv_inv, smul_eq_mul, mul_comm s⁻¹ α, mul_comm s⁻¹ β,
          ← div_eq_mul_inv, ← div_eq_mul_inv]
        ring

/-- `∫_α^β v e^{-v²/s²} dv = (s²/2)(e^{-α²/s²} - e^{-β²/s²})`. -/
theorem igCen_integral_mul_gauss {s : ℝ} (hs : 0 < s) (α β : ℝ) :
    ∫ v in α..β, v * Real.exp (-v^2/s^2) =
      s^2/2 * (Real.exp (-α^2/s^2) - Real.exp (-β^2/s^2)) := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun v => -(s^2/2) * Real.exp (-v^2/s^2))
    (fun v _ => by
      have h : HasDerivAt (fun t : ℝ => -t^2/s^2) (-(2*v)/s^2) v :=
        (igCen_hasDerivAt_neg_sq v).div_const _
      convert h.exp.const_mul (-(s^2/2)) using 1
      field_simp)
    ((by fun_prop : Continuous fun v : ℝ => v * Real.exp (-v^2/s^2)).intervalIntegrable _ _)]
  ring

/-- `v² e^{-v²/s²} ≤ 2s² e^{-v²/(2s²)}`. -/
theorem igCen_sq_mul_gauss_le {s : ℝ} (hs : 0 < s) (v : ℝ) :
    v^2 * Real.exp (-v^2/s^2) ≤ 2*s^2 * Real.exp (-(1/(2*s^2)) * v^2) := by
  set z := v^2/(2*s^2) with hz
  have h1 : v^2 = 2*s^2*z := by rw [hz]; field_simp
  have h2 : -v^2/s^2 = -z + -z := by rw [hz]; field_simp; ring
  have h3 : -(1/(2*s^2)) * v^2 = -z := by rw [hz]; field_simp
  rw [h2, h3, Real.exp_add, h1]
  have h4 : z * Real.exp (-z) ≤ 1 := by
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_one (Real.exp_pos z)]
    linarith [Real.add_one_le_exp z]
  have h5 : 0 ≤ 2*s^2*Real.exp (-z) := by positivity
  calc 2*s^2*z * (Real.exp (-z) * Real.exp (-z)) = (2*s^2*Real.exp (-z)) * (z * Real.exp (-z)) := by
        ring
    _ ≤ (2*s^2*Real.exp (-z)) * 1 := mul_le_mul_of_nonneg_left h4 h5
    _ = _ := by ring

/-- The remainder integral: if `|h(v)| ≤ C v²` on `[α, β]`, then
`|∫_α^β e^{-v²/s²} h(v) dv| ≤ 6 C s³`. -/
theorem igCen_err_bound {s C α β : ℝ} (hs : 0 < s) (hC : 0 ≤ C) (hαβ : α ≤ β) {h : ℝ → ℝ}
    (hb : ∀ v ∈ Icc α β, |h v| ≤ C * v^2) :
    |∫ v in α..β, Real.exp (-v^2/s^2) * h v| ≤ 6 * C * s^3 := by
  have hb2 : 0 < 1/(2*s^2) := by positivity
  have hint : Integrable fun v : ℝ => Real.exp (-(1/(2*s^2)) * v^2) :=
    integrable_exp_neg_mul_sq hb2
  have hG := integral_gaussian (1/(2*s^2))
  have hsq : Real.sqrt (π / (1/(2*s^2))) ≤ 3 * s := by
    have h1 : π / (1/(2*s^2)) ≤ (3*s)^2 := by
      rw [div_le_iff₀ hb2]; field_simp; nlinarith [Real.pi_lt_four, sq_nonneg s]
    calc Real.sqrt (π / (1/(2*s^2))) ≤ Real.sqrt ((3*s)^2) := Real.sqrt_le_sqrt h1
      _ = 3*s := Real.sqrt_sq (by positivity)
  have hcI : Continuous fun v : ℝ => C * (2*s^2 * Real.exp (-(1/(2*s^2)) * v^2)) := by fun_prop
  calc |∫ v in α..β, Real.exp (-v^2/s^2) * h v|
      ≤ ∫ v in α..β, C * (2*s^2 * Real.exp (-(1/(2*s^2)) * v^2)) := by
        rw [← Real.norm_eq_abs]
        refine intervalIntegral.norm_integral_le_of_norm_le hαβ
          (Eventually.of_forall fun v hv => ?_) (hcI.intervalIntegrable _ _)
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
        have := hb v ⟨hv.1.le, hv.2⟩
        calc Real.exp (-v^2/s^2) * |h v| ≤ Real.exp (-v^2/s^2) * (C * v^2) :=
              mul_le_mul_of_nonneg_left this (Real.exp_pos _).le
          _ = C * (v^2 * Real.exp (-v^2/s^2)) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left (igCen_sq_mul_gauss_le hs v) hC
    _ = C * (2*s^2) * ∫ v in α..β, Real.exp (-(1/(2*s^2)) * v^2) := by
        rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]; ring
    _ ≤ C * (2*s^2) * ∫ v, Real.exp (-(1/(2*s^2)) * v^2) := by
        gcongr
        rw [intervalIntegral.integral_of_le hαβ]
        exact setIntegral_le_integral hint (Eventually.of_forall fun _ => (Real.exp_pos _).le)
    _ ≤ C * (2*s^2) * (3*s) := by rw [hG]; gcongr
    _ = 6 * C * s^3 := by ring

/-- The left piece `∫_{-1}^b (1+u)^a e^{-au} du ∈ [0, e^{-aφ(b)}]` for `-1 < b ≤ 0`. -/
theorem igCen_J1 {a b : ℝ} (ha : 0 < a) (hb1 : -1 < b) (hb0 : b ≤ 0) :
    0 ≤ ∫ u in (-1:ℝ)..b, (1+u)^a * Real.exp (-a*u) ∧
      ∫ u in (-1:ℝ)..b, (1+u)^a * Real.exp (-a*u) ≤ Real.exp (-a * igAsy_phi b) := by
  have hc := igCen_continuous_g ha.le
  have hle : (-1:ℝ) ≤ b := hb1.le
  constructor
  · exact intervalIntegral.integral_nonneg hle fun u hu =>
      mul_nonneg (Real.rpow_nonneg (by linarith [hu.1]) _) (Real.exp_pos _).le
  · have := intervalIntegral.integral_mono_on hle (hc.intervalIntegrable _ _)
      (continuous_const.intervalIntegrable (μ := volume) _ _)
      (g := fun _ => Real.exp (-a * igAsy_phi b)) fun u hu => by
        rcases hu.1.eq_or_lt with h | h
        · subst h; simp [Real.zero_rpow ha.ne']; positivity
        · rw [igCen_kernel a h, Real.exp_le_exp]
          have := igAsy_phi_anti (s := 1+u) (t := 1+b) (by linarith) (by linarith [hu.2])
            (by linarith)
          simp only [add_sub_cancel_left] at this
          nlinarith
    rw [intervalIntegral.integral_const, smul_eq_mul] at this
    have := Real.exp_pos (-a * igAsy_phi b)
    nlinarith


/-- The comparison of the Gaussian main term with the DLMF form (algebraic part of 8.11.10). -/
theorem igCen_stepB {s y B π' rT ry eT ey v₁ : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (hB : 0 < B)
    (hy : |y| ≤ B) (hπ'1 : 1 ≤ π') (hey0 : 0 ≤ ey) (hey1 : ey ≤ 1)
    (herf : |rT - ry - 2/π' * (v₁/s - y) * ey| ≤ 2/π' * (v₁/s - y)^2)
    (hlip : |ey - eT| ≤ |v₁/s - y|)
    (hρ : |v₁ - (s*y - (s*y)^2/3)| ≤ 6*|s*y|^3) :
    |((1 + rT)/2 - s/(3*π') * eT) - ((1 + ry)/2 - s/(3*π')*(1+y^2)*ey)| ≤
      ((B^2/3 + 6*B^3)^2 + (B^2/3 + 6*B^3) + 6*B^3) * s^2 := by
  set c₁ := B^2/3 + 6*B^3 with hc₁
  have hπ'0 : 0 < π' := by linarith
  have hs3π : s/(3*π') ≤ s := div_le_self hs.le (by linarith)
  have hyB3 : |y|^3 ≤ B^3 := pow_le_pow_left₀ (abs_nonneg y) hy 3
  have hyB2 : |y|^2 ≤ B^2 := pow_le_pow_left₀ (abs_nonneg y) hy 2
  set ρ := v₁ - (s*y - (s*y)^2/3) with hρdef
  have hρb : |ρ| ≤ 6 * s^3 * B^3 := by
    calc |ρ| ≤ 6*|s*y|^3 := hρ
      _ = 6 * s^3 * |y|^3 := by rw [abs_mul, abs_of_pos hs]; ring
      _ ≤ 6 * s^3 * B^3 := by gcongr
  set d := v₁/s - y with hd
  have hdρ : d = ρ/s - s*y^2/3 := by
    rw [hd, hρdef]; field_simp; ring
  have hρs : |ρ/s| ≤ 6 * B^3 * s^2 := by
    rw [abs_div, abs_of_pos hs, div_le_iff₀ hs]
    calc |ρ| ≤ 6 * s^3 * B^3 := hρb
      _ = 6 * B^3 * s^2 * s := by ring
  have hsy : |s*y^2/3| ≤ s * B^2/3 := by
    rw [abs_div, abs_mul, abs_of_pos hs, abs_pow, abs_of_pos (by norm_num : (0:ℝ) < 3)]
    gcongr
  have hdb : |d| ≤ s * c₁ := by
    rw [hdρ]
    have h1 : 6 * B^3 * s^2 ≤ 6 * B^3 * s := by
      have : s^2 ≤ s := by nlinarith
      have : 0 ≤ 6 * B^3 := by positivity
      exact mul_le_mul_of_nonneg_left (by assumption) this
    calc |ρ/s - s*y^2/3| ≤ |ρ/s| + |s*y^2/3| := abs_sub _ _
      _ ≤ 6 * B^3 * s + s * B^2/3 := by linarith
      _ = s * c₁ := by rw [hc₁]; ring
  have hid : ((1 + rT)/2 - s/(3*π') * eT) - ((1 + ry)/2 - s/(3*π')*(1+y^2)*ey) =
      ((rT - ry)/2 - 1/π' * d * ey) + 1/π' * (ρ/s) * ey + s/(3*π') * (ey - eT) := by
    rw [hdρ]; field_simp; ring
  have q1 : |(rT - ry)/2 - 1/π' * d * ey| ≤ d^2 := by
    have e : (rT - ry)/2 - 1/π' * d * ey = (rT - ry - 2/π' * d * ey)/2 := by ring
    rw [e, abs_div, abs_two, div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
    have h2 : 2/π' ≤ 2 := div_le_self (by norm_num) hπ'1
    calc |rT - ry - 2/π' * d * ey| ≤ 2/π' * d^2 := herf
      _ ≤ 2 * d^2 := by gcongr
      _ = d^2 * 2 := by ring
  have q2 : |1/π' * (ρ/s) * ey| ≤ 6 * B^3 * s^2 := by
    rw [abs_mul, abs_mul, abs_of_nonneg hey0, abs_of_pos (by positivity)]
    have h1 : 1/π' ≤ 1 := div_le_self zero_le_one hπ'1
    calc 1/π' * |ρ/s| * ey ≤ 1 * (6 * B^3 * s^2) * 1 := by gcongr
      _ = _ := by ring
  have q3 : |s/(3*π') * (ey - eT)| ≤ c₁ * s^2 := by
    rw [abs_mul, abs_of_pos (by positivity)]
    calc s/(3*π') * |ey - eT| ≤ s * (s * c₁) := by gcongr; exact hlip.trans hdb
      _ = c₁ * s^2 := by ring
  have hd2 : d^2 ≤ c₁^2 * s^2 := by
    rw [← sq_abs d, show c₁^2 * s^2 = (s*c₁)^2 by ring]
    exact pow_le_pow_left₀ (abs_nonneg d) hdb 2
  rw [hid]
  calc _ ≤ |(rT - ry)/2 - 1/π' * d * ey + 1/π' * (ρ/s) * ey| +
        |s/(3*π') * (ey - eT)| := abs_add_le _ _
    _ ≤ |(rT - ry)/2 - 1/π' * d * ey| + |1/π' * (ρ/s) * ey| +
        |s/(3*π') * (ey - eT)| := by gcongr; exact abs_add_le _ _
    _ ≤ d^2 + 6 * B^3 * s^2 + c₁ * s^2 := by linarith
    _ ≤ c₁^2 * s^2 + 6 * B^3 * s^2 + c₁ * s^2 := by linarith
    _ = _ := by ring

set_option maxHeartbeats 1600000 in
/-- The central estimate behind 8.11.10, in the variable `s = √(2/a)`:
`P(a+1, a(1+sy)) = (1 + erf y)/2 - s/(3√π) (1+y²) e^{-y²} + O(s²)` uniformly for `|y| ≤ B`. -/
theorem igCen_core {B : ℝ} (hB : 0 < B) : ∃ C s₀ : ℝ, 0 < s₀ ∧ s₀ ≤ 1 ∧
    ∀ s y : ℝ, 0 < s → s ≤ s₀ → |y| ≤ B →
    |(∫ t in (0:ℝ)..(2/s^2)*(1+s*y), t^(2/s^2) * Real.exp (-t)) / Real.Gamma (2/s^2+1) -
      ((1 + TauCeti.Real.erf y)/2 - s/(3*Real.sqrt π)*(1+y^2)*Real.exp (-y^2))| ≤ C * s^2 := by
  obtain ⟨U, w₀, C₂, hw0, hw1, hC₂, hU, hUm, hUp⟩ := igCen_U
  set δ₁ := min (1/2) (min (-U (-w₀)) (U w₀)) with hδ₁
  have hδ₁0 : 0 < δ₁ := by
    simp only [hδ₁, lt_min_iff]; exact ⟨by norm_num, by linarith, hUp⟩
  set c₁ := B^2/3 + 6*B^3 with hc₁
  have hc₁0 : 0 ≤ c₁ := by positivity
  set D := (5/w₀^5 + 6*C₂) + (c₁^2 + c₁ + 6*B^3) with hD
  have hD0 : 0 ≤ D := by positivity
  refine ⟨D + (2 + B^2 + D)/24, min 1 (δ₁/B), by positivity, min_le_left _ _,
    fun s y hs hs0 hy => ?_⟩
  have hs1 : s ≤ 1 := hs0.trans (min_le_left _ _)
  have hsB : s * B ≤ δ₁ := by
    have := hs0.trans (min_le_right _ _); rwa [le_div_iff₀ hB] at this
  obtain ⟨a, ha_def⟩ : ∃ a : ℝ, a = 2/s^2 := ⟨_, rfl⟩
  rw [← ha_def]
  have ha : 0 < a := by rw [ha_def]; positivity
  have has : a * s^2 = 2 := by rw [ha_def]; field_simp
  set u₁ := s*y with hu₁
  have hu₁B : |u₁| ≤ δ₁ := by
    rw [hu₁, abs_mul, abs_of_pos hs]; nlinarith [abs_nonneg y]
  have hδa : δ₁ ≤ 1/2 := min_le_left _ _
  have hδb : δ₁ ≤ -U (-w₀) := (min_le_right _ _).trans (min_le_left _ _)
  have hδc : δ₁ ≤ U w₀ := (min_le_right _ _).trans (min_le_right _ _)
  have hu₁h : |u₁| ≤ 1/2 := hu₁B.trans hδa
  -- the upper limit in the `v` variable
  have hUc : ContinuousOn U (Icc (-w₀) w₀) := fun v hv =>
    (hU v hv).1.continuousAt.continuousWithinAt
  obtain ⟨v₁, hv₁, hUv₁⟩ : ∃ v₁ ∈ Icc (-w₀) w₀, U v₁ = u₁ :=
    intermediate_value_Icc (by linarith) hUc
      ⟨by linarith [neg_abs_le u₁], by linarith [le_abs_self u₁]⟩
  obtain ⟨-, -, -, hφv1, hsign, -⟩ := hU v₁ hv₁
  have hv1sq : v₁^2 = 2 * igAsy_phi u₁ := by rw [← hUv₁, hφv1]; ring
  have hρ := igCen_v_approx hu₁h hv1sq (by rw [← hUv₁, mul_comm]; exact hsign)
  -- the integral as `J₁ + G₀ + (2/3) G₁ + E`
  set g : ℝ → ℝ := fun u => (1+u)^a * Real.exp (-a*u) with hg
  have hgc : Continuous g := igCen_continuous_g ha.le
  have hsub : ∫ t in (0:ℝ)..a*(1+u₁), t^a * Real.exp (-t) =
      a^(a+1) * Real.exp (-a) * ∫ u in (-1:ℝ)..u₁, g u :=
    igCen_integral_subst ha (by linarith [neg_abs_le u₁])
  have hsplit : ∫ u in (-1:ℝ)..u₁, g u =
      (∫ u in (-1:ℝ)..U (-w₀), g u) + ∫ u in U (-w₀)..u₁, g u :=
    (intervalIntegral.integral_add_adjacent_intervals (hgc.intervalIntegrable _ _)
      (hgc.intervalIntegrable _ _)).symm
  have hIcc1 : uIcc (-w₀) v₁ ⊆ Icc (-w₀) w₀ := by
    rw [uIcc_of_le hv₁.1]; exact Icc_subset_Icc le_rfl hv₁.2
  have hchange : ∫ u in U (-w₀)..u₁, g u =
      ∫ v in (-w₀)..v₁, Real.exp (-v^2/s^2) * deriv U v := by
    rw [← hUv₁, ← intervalIntegral.integral_comp_mul_deriv (fun x hx => (hU x (hIcc1 hx)).1)
      (fun x hx => (hU x (hIcc1 hx)).2.1.continuousWithinAt) hgc]
    refine intervalIntegral.integral_congr fun v hv => ?_
    obtain ⟨-, -, h1, h2, -, -⟩ := hU v (hIcc1 hv)
    simp only [Function.comp_apply, hg]
    rw [igCen_kernel a (by linarith), h2]
    congr 2
    rw [ha_def]; field_simp
  set h : ℝ → ℝ := fun v => deriv U v - 1 - 2/3*v with hh
  have hcU' : ContinuousOn (deriv U) (uIcc (-w₀) v₁) := fun x hx =>
    (hU x (hIcc1 hx)).2.1.continuousWithinAt
  have hdec : ∫ v in (-w₀)..v₁, Real.exp (-v^2/s^2) * deriv U v =
      (∫ v in (-w₀)..v₁, Real.exp (-v^2/s^2)) +
      2/3 * (∫ v in (-w₀)..v₁, v * Real.exp (-v^2/s^2)) +
      ∫ v in (-w₀)..v₁, Real.exp (-v^2/s^2) * h v := by
    have i1 : IntervalIntegrable (fun v => Real.exp (-v^2/s^2)) volume (-w₀) v₁ :=
      (by fun_prop : Continuous fun v : ℝ => Real.exp (-v^2/s^2)).intervalIntegrable _ _
    have i2 : IntervalIntegrable (fun v => v * Real.exp (-v^2/s^2)) volume (-w₀) v₁ :=
      (by fun_prop : Continuous fun v : ℝ => v * Real.exp (-v^2/s^2)).intervalIntegrable _ _
    have i3 : IntervalIntegrable (fun v => Real.exp (-v^2/s^2) * h v) volume (-w₀) v₁ :=
      ContinuousOn.intervalIntegrable ((by fun_prop : Continuous fun v : ℝ =>
        Real.exp (-v^2/s^2)).continuousOn.mul ((hcU'.sub continuousOn_const).sub
          (by fun_prop)))
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add i1 (i2.const_mul _),
      ← intervalIntegral.integral_add (i1.add (i2.const_mul _)) i3]
    refine intervalIntegral.integral_congr fun v _ => ?_
    simp only [hh]; ring
  -- the pieces
  set J₁ := ∫ u in (-1:ℝ)..U (-w₀), g u with hJ₁
  set E := ∫ v in (-w₀)..v₁, Real.exp (-v^2/s^2) * h v with hE
  set π' := Real.sqrt π with hπ'
  have hπ'1 : 1 ≤ π' := by rw [hπ', Real.one_le_sqrt]; linarith [Real.pi_gt_three]
  have hπ'0 : 0 < π' := by linarith
  have hsπ1 : s ≤ s*π' := le_mul_of_one_le_right hs.le hπ'1
  have hsπ : s^2 ≤ s*π' := by rw [sq]; exact mul_le_mul_of_nonneg_left (hs1.trans hπ'1) hs.le
  have hs3π : s/(3*π') ≤ s := div_le_self hs.le (by linarith)
  set eM := Real.exp (-w₀^2/s^2) with heM
  set eT := Real.exp (-v₁^2/s^2) with heT
  set ey := Real.exp (-y^2) with hey
  set rT := TauCeti.Real.erf (v₁/s) with hrT
  set rM := TauCeti.Real.erf (w₀/s) with hrM
  set ry := TauCeti.Real.erf y with hry
  have hG₀ : ∫ v in (-w₀)..v₁, Real.exp (-v^2/s^2) = s * (π'/2) * (rT + rM) := by
    rw [igCen_integral_gauss hs, neg_div, TauCeti.Real.erf_neg]; ring
  have hG₁ : ∫ v in (-w₀)..v₁, v * Real.exp (-v^2/s^2) = s^2/2 * (eM - eT) := by
    rw [igCen_integral_mul_gauss hs, neg_sq]
  have hJ : ∫ u in (-1:ℝ)..u₁, g u = J₁ + s * (π'/2) * (rT + rM) + 2/3 * (s^2/2 * (eM - eT)) + E := by
    rw [hsplit, hchange, hdec, hG₀, hG₁]; ring
  -- bounds on the pieces
  have hUw : -1 < U (-w₀) := by linarith [(hU (-w₀) ⟨le_rfl, by linarith⟩).2.2.1]
  obtain ⟨hJ₁0, hJ₁1⟩ := igCen_J1 ha hUw hUm.le
  have hφw : igAsy_phi (U (-w₀)) = w₀^2/2 := by
    rw [(hU (-w₀) ⟨le_rfl, by linarith⟩).2.2.2.1, neg_sq]
  have haw : -a * (w₀^2/2) = -w₀^2/s^2 := by
    rw [ha_def]; field_simp
  rw [hφw, haw] at hJ₁1
  have hEb : |E| ≤ 6 * C₂ * s^3 :=
    igCen_err_bound hs hC₂ hv₁.1 fun v hv => (hU v (hIcc1 (by rw [uIcc_of_le hv₁.1]; exact hv))).2.2.2.2.2
  have hM : 0 < w₀/s := by positivity
  have hrM1 : 1 - rM ≤ eM / (w₀/s) := by
    have := igCen_one_sub_erf_le hM
    rwa [div_pow, ← neg_div] at this
  have hrM0 : 0 ≤ 1 - rM := by linarith [TauCeti.Real.erf_le_one (w₀/s)]
  have heM : eM ≤ 2 * s^4 / w₀^4 := by
    have := igCen_exp_neg_le (x := w₀^2/s^2) (by positivity)
    rw [heM, neg_div]; refine this.trans (le_of_eq ?_); field_simp
  have heM0 : 0 ≤ eM := (Real.exp_pos _).le
  -- Stirling
  have hst := igCen_stirling ha
  have hsa : Real.sqrt a / Real.sqrt (2*π) = 1/(s*π') := by
    rw [ha_def, Real.sqrt_div' _ (by positivity : (0:ℝ) ≤ s^2), Real.sqrt_sq hs.le,
      Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2), hπ']
    have : Real.sqrt 2 ≠ 0 := by positivity
    field_simp
  rw [hsa] at hst
  set Φ := DLMF.Gamma.binetIntegral a with hΦ
  obtain ⟨hΦ0, hΦ1⟩ := DLMF.Gamma.binetIntegral_pos_lt ha
  have hΦs : 1/(12*a) = s^2/24 := by
    rw [ha_def]; field_simp; ring
  rw [hΦs] at hΦ1
  have hP : (∫ t in (0:ℝ)..a*(1+s*y), t^a * Real.exp (-t)) / Real.Gamma (a+1) =
      Real.exp (-Φ) * ((∫ u in (-1:ℝ)..u₁, g u) / (s*π')) := by
    rw [← hu₁, hsub, mul_div_right_comm, hst]; ring
  rw [hP]
  -- step A: the Gaussian main part `X`
  set K := (∫ u in (-1:ℝ)..u₁, g u) / (s*π') with hK
  set X := (1 + rT)/2 - s/(3*π') * eT with hX
  have hA : |K - X| ≤ (5/w₀^5 + 6*C₂) * s^2 := by
    have hid : K - X = J₁/(s*π') - (1 - rM)/2 + s/(3*π') * eM + E/(s*π') := by
      rw [hK, hJ, hX]; field_simp; ring
    rw [hid]
    have hw1' : w₀ ≤ 1 := by linarith
    have hs4 : s^4 ≤ s^2 := pow_le_pow_of_le_one hs.le hs1 (by norm_num)
    have hs3 : s^3 ≤ s^2 := pow_le_pow_of_le_one hs.le hs1 (by norm_num)
    have hs5 : s^5 ≤ s^2 := pow_le_pow_of_le_one hs.le hs1 (by norm_num)
    have hw45 : 1/w₀^4 ≤ 1/w₀^5 := by
      apply one_div_le_one_div_of_le (by positivity)
      exact pow_le_pow_of_le_one hw0.le hw1' (by norm_num)
    have t1 : |J₁/(s*π')| ≤ 2 * s^2 / w₀^4 := by
      rw [abs_div, abs_of_nonneg hJ₁0, abs_of_pos (by positivity)]
      rw [div_le_iff₀ (by positivity)]
      have : J₁ ≤ 2*s^4/w₀^4 := hJ₁1.trans heM
      calc J₁ ≤ 2*s^4/w₀^4 := this
        _ = 2*s^2/w₀^4 * (s^2) := by ring
        _ ≤ 2*s^2/w₀^4 * (s*π') := by gcongr
    have t2 : |(1 - rM)/2| ≤ s^2 / w₀^5 := by
      rw [abs_of_nonneg (by linarith)]
      have : eM / (w₀/s) ≤ 2*s^5/w₀^5 := by
        rw [div_div_eq_mul_div]
        calc eM * s / w₀ ≤ 2*s^4/w₀^4 * s / w₀ := by gcongr
          _ = 2*s^5/w₀^5 := by field_simp
      have h5 : 2*s^5/w₀^5 ≤ 2*s^2/w₀^5 := by gcongr
      have h6 := hrM1.trans (this.trans h5)
      calc (1 - rM)/2 ≤ (2*s^2/w₀^5)/2 := by gcongr
        _ = s^2/w₀^5 := by ring
    have t3 : |s/(3*π') * eM| ≤ 2 * s^2 / w₀^4 := by
      rw [abs_of_nonneg (by positivity)]
      calc s/(3*π') * eM ≤ s * (2 * s^4 / w₀^4) := by gcongr
        _ = 2 * s^5 / w₀^4 := by ring
        _ ≤ 2 * s^2 / w₀^4 := by gcongr
    have t4 : |E/(s*π')| ≤ 6 * C₂ * s^2 := by
      rw [abs_div, abs_of_pos (show 0 < s*π' by positivity), div_le_iff₀ (by positivity)]
      calc |E| ≤ 6 * C₂ * s^3 := hEb
        _ = 6 * C₂ * s^2 * s := by ring
        _ ≤ 6 * C₂ * s^2 * (s * π') := by gcongr
    have e1 : 2 * s^2 / w₀^4 = 2 * s^2 * (1/w₀^4) := by ring
    have e2 : s^2 / w₀^5 = s^2 * (1/w₀^5) := by ring
    have : 2 * s^2 * (1/w₀^4) ≤ 2 * s^2 * (1/w₀^5) := by gcongr
    calc _ ≤ |J₁/(s*π') - (1 - rM)/2 + s/(3*π') * eM| + |E/(s*π')| := abs_add_le _ _
      _ ≤ |J₁/(s*π') - (1 - rM)/2| + |s/(3*π') * eM| + |E/(s*π')| := by
          gcongr; exact abs_add_le _ _
      _ ≤ |J₁/(s*π')| + |(1 - rM)/2| + |s/(3*π') * eM| + |E/(s*π')| := by
          gcongr; exact abs_sub _ _
      _ ≤ 2*s^2*(1/w₀^5) + s^2*(1/w₀^5) + 2*s^2*(1/w₀^5) + 6*C₂*s^2 := by
          rw [e1] at t1 t3; rw [e2] at t2; linarith
      _ = _ := by ring
  -- step B: comparison of `X` with the target
  set tgt := (1 + ry)/2 - s/(3*π')*(1+y^2)*ey with htgt
  have hyB2 : |y|^2 ≤ B^2 := pow_le_pow_left₀ (abs_nonneg y) hy 2
  have hey1 : ey ≤ 1 := by rw [hey]; exact Real.exp_le_one_iff.2 (neg_nonpos.2 (sq_nonneg y))
  have hey0 : 0 ≤ ey := (Real.exp_pos _).le
  have hB' : |X - tgt| ≤ (c₁^2 + c₁ + 6*B^3) * s^2 := by
    have herf := igCen_erf_sub (v₁/s) y
    rw [← hrT, ← hry, ← hey] at herf
    have hT : eT = Real.exp (-(v₁/s)^2) := by rw [heT, div_pow, neg_div]
    have hl := igCen_exp_neg_sq_lip y (v₁/s)
    rw [← hey, ← hT, abs_sub_comm y] at hl
    exact igCen_stepB hs hs1 hB hy hπ'1 hey0 hey1 herf hl (by rw [← hu₁]; exact hρ)
  -- step C: the Binet factor
  have hKt : |K - tgt| ≤ D * s^2 := by
    have := abs_sub_le K X tgt
    rw [hD]; linarith
  have htgtb : |tgt| ≤ 1 + (1 + B^2) := by
    rw [htgt]
    have h1 : |(1 + ry)/2| ≤ 1 := by
      rw [abs_le]; constructor <;>
        linarith [TauCeti.Real.erf_le_one y, TauCeti.Real.neg_one_lt_erf y]
    have h2 : |s/(3*π')*(1+y^2)*ey| ≤ 1 + B^2 := by
      rw [abs_of_nonneg (by positivity)]
      have h3 : s/(3*π') ≤ 1 := hs3π.trans hs1
      have h4 : y^2 ≤ B^2 := by rw [← sq_abs]; exact hyB2
      calc s/(3*π')*(1+y^2)*ey ≤ 1 * (1 + B^2) * 1 := by gcongr
        _ = 1 + B^2 := by ring
    exact (abs_sub _ _).trans (by linarith)
  have hKb : |K| ≤ 2 + B^2 + D := by
    have := abs_sub_abs_le_abs_sub K tgt
    have : D * s^2 ≤ D := by
      have : s^2 ≤ 1 := by nlinarith
      exact mul_le_of_le_one_right hD0 this
    linarith
  have hexp : |Real.exp (-Φ) - 1| ≤ s^2/24 := by
    rw [abs_sub_comm, abs_of_nonneg (by linarith [Real.exp_le_one_iff.2 (by linarith : -Φ ≤ 0)])]
    linarith [Real.add_one_le_exp (-Φ)]
  have hid : Real.exp (-Φ) * K - tgt = (Real.exp (-Φ) - 1) * K + (K - tgt) := by ring
  rw [hid]
  calc _ ≤ |(Real.exp (-Φ) - 1) * K| + |K - tgt| := abs_add_le _ _
    _ ≤ s^2/24 * (2 + B^2 + D) + D * s^2 := by
        rw [abs_mul]; gcongr
    _ = _ := by ring
/-- Uniform large positive parameter with bounded real central variable. -/
def gammaCentralFilter (B : ℝ) : Filter (ℝ × ℝ) :=
  comap Prod.fst atTop ⊓ 𝓟 {p : ℝ × ℝ | 0 < p.1 ∧ |p.2| ≤ B}

/-- normIncGammaP central expansion. Proof: Stirling with Binet's remainder, the saddle substitution
`φ(U(v)) = v²/2` with `U'(v) = 1 + 2v/3 + O(v²)`, and the Gaussian integral through `erf`
(`igCen_core`). -/
@[dlmf 8.11.E10]
theorem normIncGammaP_central_expansion {B : ℝ} (hB : 0 < B) :
    IsBigO (gammaCentralFilter B) (fun p : ℝ × ℝ => normIncGammaPContinued (p.1+1) (p.1+Real.sqrt (2*p.1)*p.2)-erfc (-p.2)/2+((Real.sqrt (2/(π*p.1))/3*(1+p.2^2)*Real.exp (-p.2^2) : ℝ) : ℂ)) (fun p => p.1⁻¹) := by
  obtain ⟨C, s₀, hs₀, -, hcore⟩ := igCen_core hB
  set s₁ := min s₀ (1/(2*B)) with hs₁
  have hs₁0 : 0 < s₁ := by positivity
  refine IsBigO.of_bound (2*C) ?_
  have hev : ∀ᶠ p : ℝ × ℝ in gammaCentralFilter B, 2/s₁^2 ≤ p.1 ∧ 0 < p.1 ∧ |p.2| ≤ B := by
    have h1 : ∀ᶠ p : ℝ × ℝ in gammaCentralFilter B, 2/s₁^2 ≤ p.1 :=
      (tendsto_comap.eventually (eventually_ge_atTop _)).filter_mono inf_le_left
    have h2 : ∀ᶠ p : ℝ × ℝ in gammaCentralFilter B, 0 < p.1 ∧ |p.2| ≤ B :=
      mem_inf_of_right (mem_principal_self _)
    exact h1.and h2
  filter_upwards [hev] with p ⟨hA, ha, hy⟩
  obtain ⟨a, y⟩ := p
  simp only at hA ha hy ⊢
  set s := Real.sqrt (2/a) with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 (by positivity)
  have hss : s^2 = 2/a := Real.sq_sqrt (by positivity)
  have hsle : s ≤ s₁ := by
    rw [← Real.sqrt_sq hs₁0.le, hs]
    apply Real.sqrt_le_sqrt
    rw [div_le_iff₀ ha]; rw [div_le_iff₀ (by positivity)] at hA; linarith
  have hsy : s * |y| ≤ 1/2 := by
    have h1 : s ≤ 1/(2*B) := hsle.trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at h1
    nlinarith [abs_nonneg y]
  have h2s : 2/s^2 = a := by rw [hss]; field_simp
  have hc := hcore s y hs0 (hsle.trans (min_le_left _ _)) hy
  rw [h2s] at hc
  have hx : (a:ℂ) + (Real.sqrt (2*a) : ℂ) * (y:ℂ) = ((a*(1+s*y) : ℝ) : ℂ) := by
    have : Real.sqrt (2*a) = a * s := by
      rw [hs, ← Real.sqrt_sq ha.le, ← Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq ha.le]
      congr 1; field_simp
    rw [this]; push_cast; ring
  have hxpos : 0 < a*(1+s*y) := by
    have : -(s*|y|) ≤ s*y := by rw [← mul_neg]; exact mul_le_mul_of_nonneg_left (neg_abs_le y) hs0.le
    have : 0 < 1 + s*y := by linarith
    positivity
  rw [hx, igCen_normIncGammaP_eq ha hxpos, show -(y:ℂ) = ((-y:ℝ):ℂ) by push_cast; ring,
    erfc_ofReal]
  have hsq : Real.sqrt (2/(π*a)) = s/Real.sqrt π := by
    rw [hs, ← Real.sqrt_div' _ Real.pi_pos.le]; congr 1; field_simp
  rw [hsq, TauCeti.Real.erfc_def, TauCeti.Real.erf_neg]
  have e : ((((∫ t in (0:ℝ)..a*(1+s*y), t^a * Real.exp (-t)) / Real.Gamma (a+1) : ℝ) : ℂ) -
      ((1 - -TauCeti.Real.erf y : ℝ) : ℂ)/2 +
      ((s/Real.sqrt π/3*(1+y^2)*Real.exp (-y^2) : ℝ) : ℂ)) =
      (((∫ t in (0:ℝ)..a*(1+s*y), t^a * Real.exp (-t)) / Real.Gamma (a+1) -
        ((1 + TauCeti.Real.erf y)/2 - s/(3*Real.sqrt π)*(1+y^2)*Real.exp (-y^2)) : ℝ) : ℂ) := by
    push_cast; ring
  rw [e, Complex.norm_real, Real.norm_eq_abs, norm_inv, Real.norm_eq_abs, abs_of_pos ha]
  calc _ ≤ C * s^2 := hc
    _ = 2*C*a⁻¹ := by rw [hss]; ring

/-- scIncGamma central expansion. -/
@[dlmf 8.11.E11]
theorem scIncGamma_central_expansion {B : ℝ} (hB : 0 < B) :
    IsBigO (gammaCentralFilter B) (fun p : ℝ × ℝ => let x := p.1+Real.sqrt (2*p.1)*p.2; (x : ℂ)^(1-(p.1 : ℂ))*scIncGamma (1-p.1) (-x)+Real.cos (π*p.1)-Real.sin (π*p.1)/π*(2*Real.sqrt π*dawsonF p.2+(2/3*Real.sqrt (2*π/p.1)*(1-p.2^2) : ℝ))*Real.exp (p.2^2)) (fun p => p.1⁻¹) := by
  sorry

end DLMF.Confluent
