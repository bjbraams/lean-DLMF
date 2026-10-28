/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Struve.Asymptotics.IntegratedKernels

/-!
# Asymptotic expansions of integrated Struve functions

Evaluation of the integrated kernels gives the Struve primitive expansions and their constants.

Source references and common attribution are retained in
`DLMF.Struve.Asymptotics`.
-/

@[expose] public noncomputable section

open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF

open scoped Real Topology Nat

namespace DLMF.Struve

open DLMF.Bessel DLMF.Airy

section StruvePrimitive

open scoped Interval

/-- `Γ(1/2 - s) (2s)! = (-4)^s s! √π`. -/
theorem struvePrim_Gamma_half_sub_nat (s : ℕ) :
    Gamma (1 / 2 - s) * ((2 * s).factorial : ℂ) = (-4 : ℂ) ^ s * s.factorial * Real.sqrt π := by
  induction s with
  | zero =>
    simp only [Nat.cast_zero, sub_zero, mul_zero, Nat.factorial_zero, Nat.cast_one, mul_one,
      pow_zero, one_mul]
    rw [Complex.Gamma_one_half_eq, Real.sqrt_eq_rpow, ofReal_cpow Real.pi_pos.le]
    push_cast; ring_nf
  | succ s ih =>
    have h1 : Gamma (1 / 2 - s) = (1 / 2 - ((s + 1 : ℕ) : ℂ)) * Gamma (1 / 2 - ((s + 1 : ℕ) : ℂ)) := by
      rw [← Gamma_add_one]
      · push_cast; ring_nf
      · intro h
        have := congrArg Complex.re h
        simp at this
        linarith
    rw [h1] at ih
    rw [show 2 * (s + 1) = 2 * s + 1 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ,
      Nat.factorial_succ]
    push_cast at ih ⊢
    linear_combination (-2 * (2 * (s : ℂ) + 2)) * ih

/-- The `k = j+1` term of the expansion of `∫₀^z 𝐊₀` differentiates to the `k`-th term of the
expansion of `𝐊₀` (DLMF 11.6.1 with `ν = 0`). -/
theorem struvePrim_term_hasDerivAt (j : ℕ) {z : ℂ} (hz : z ≠ 0) :
    HasDerivAt (fun w : ℂ => 2 / π * ((-1) ^ (j + 1 + 1) * ((2 * (j + 1)).factorial : ℂ) *
      (2 * (j + 1) - 1).factorial / (((j + 1).factorial : ℂ) ^ 2 * (2 * w) ^ (2 * (j + 1)))))
      (struveAsymptoticTerm 0 z (j + 1)) z := by
  have hz2 : (2 : ℂ) * z ≠ 0 := mul_ne_zero two_ne_zero hz
  set n : ℕ := 2 * (j + 1) with hn
  set A : ℂ := 2 / π * ((-1) ^ (j + 1 + 1) * ((2 * (j + 1)).factorial : ℂ) *
      (2 * (j + 1) - 1).factorial / (((j + 1).factorial : ℂ) ^ 2)) with hA
  have hfun : (fun w : ℂ => 2 / π * ((-1) ^ (j + 1 + 1) * ((2 * (j + 1)).factorial : ℂ) *
      (2 * (j + 1) - 1).factorial / (((j + 1).factorial : ℂ) ^ 2 * (2 * w) ^ (2 * (j + 1))))) =
      fun w => A * (2 * w) ^ (-(n : ℤ)) := by
    funext w
    rw [hA, zpow_neg, zpow_natCast]
    field_simp
    rfl
  rw [hfun]
  have hd : HasDerivAt (fun w : ℂ => A * (2 * w) ^ (-(n : ℤ)))
      (A * ((-(n : ℤ) : ℂ) * (2 * z) ^ (-(n : ℤ) - 1) * 2)) z := by
    have h1 := (hasDerivAt_zpow (-(n : ℤ)) (2 * z) (Or.inl hz2)).comp z
      ((hasDerivAt_id z).const_mul 2)
    simpa using h1.const_mul A
  convert hd using 1
  -- identify the term
  have hG1 := Gamma_nat_add_half_mul (j + 1)
  have hG2 := struvePrim_Gamma_half_sub_nat (j + 1)
  have hsq : (Real.sqrt π : ℂ) ≠ 0 := ofReal_ne_zero.2 (Real.sqrt_pos.2 Real.pi_pos).ne'
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_pos.ne'
  have hGa : Gamma (1 / 2 - ((j + 1 : ℕ) : ℂ)) ≠ 0 := by
    intro h; rw [h, zero_mul] at hG2
    exact (mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num))
      (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _))) hsq) hG2.symm
  have hpow : (z / 2) ^ ((0 : ℂ) - 2 * ((j + 1 : ℕ) : ℂ) - 1) = ((z / 2) ^ (n + 1))⁻¹ := by
    rw [show (0 : ℂ) - 2 * ((j + 1 : ℕ) : ℂ) - 1 = -((n + 1 : ℕ) : ℂ) by rw [hn]; push_cast; ring,
      cpow_neg, cpow_natCast]
  have hfac : ((2 * (j + 1)).factorial : ℂ) = (2 * (j + 1) : ℕ) * ((2 * (j + 1) - 1).factorial) := by
    rw [show 2 * (j + 1) = (2 * j + 1) + 1 by ring, Nat.factorial_succ]; push_cast; simp
  rw [struveAsymptoticTerm, zero_add, hpow, hA,
    show (-(n : ℤ) - 1) = -((n + 1 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast]
  have hk : ((j + 1).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  have h2k : ((2 * (j + 1)).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  have e1 : Gamma (((j + 1 : ℕ) : ℂ) + 1 / 2) =
      ((2 * (j + 1)).factorial : ℂ) * Real.sqrt π / (((j + 1).factorial : ℂ) * 4 ^ (j + 1)) := by
    rw [eq_div_iff (mul_ne_zero hk (pow_ne_zero _ (by norm_num))), ← hG1]; ring
  have e2 : Gamma (1 / 2 - ((j + 1 : ℕ) : ℂ)) =
      (-4 : ℂ) ^ (j + 1) * ((j + 1).factorial : ℂ) * Real.sqrt π / ((2 * (j + 1)).factorial : ℂ) := by
    rw [eq_div_iff h2k, ← hG2]
  rw [e1, e2, hfac, hn]
  have hz' : z / 2 ≠ 0 := div_ne_zero hz two_ne_zero
  have h2m1 : (((2 * (j + 1) - 1).factorial : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  field_simp
  push_cast
  ring_nf
  have key : (-4 : ℂ) ^ j * (-1) ^ j * (1 / 2) ^ (j * 2) * 4 ^ j = 2 ^ (j * 2) := by
    rw [mul_comm j 2, pow_mul, pow_mul, ← mul_pow, ← mul_pow, ← mul_pow]; norm_num
  linear_combination (-(↑j * z ^ 3 * z ^ (j * 2) * 16 + z ^ 3 * z ^ (j * 2) * 16)) * key

/-- The constant term `2/(πz)` of the expansion of `𝐊₀`. -/
theorem struvePrim_term_zero {z : ℂ} (hz : z ≠ 0) : struveAsymptoticTerm 0 z 0 = 2 / (π * z) := by
  have hG : Gamma (1 / 2) ≠ 0 := by
    rw [Complex.Gamma_one_half_eq]; exact (cpow_ne_zero_iff_of_exponent_ne_zero (by norm_num)).2
      (ofReal_ne_zero.2 Real.pi_pos.ne')
  rw [struveAsymptoticTerm]
  simp only [Nat.cast_zero, mul_zero, sub_zero, zero_add, zero_sub, div_self hG, one_mul]
  rw [cpow_neg_one]
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_pos.ne'
  field_simp

/-- Asymptotic bound with the indicated comparison function: `(fun z : ℂ => DLMF.primitive
(struveK 0) z - 2/π*(log (2*z)+Real.eulerMascheroniConstant)-2/π*∑ j ∈ Finset.range N, let
k:=j+1; (-1)^(k+1)*((2*k).factorial:ℂ)*(2*k-1).factorial/((k.factorial:ℂ)^2*(2*z)^(2*k)))
=O[sector (π-δ)] (fun z : ℂ => z^(-(2*(N+1):ℤ)))`. -/
@[dlmf 11.6.E3]
theorem struveK_primitive_asymptotic {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π) (N : ℕ) :
    (fun z : ℂ => DLMF.primitive (struveK 0) z - 2/π*(log (2*z)+Real.eulerMascheroniConstant)-2/π*∑ j ∈ Finset.range N, let k:=j+1; (-1)^(k+1)*((2*k).factorial:ℂ)*(2*k-1).factorial/((k.factorial:ℂ)^2*(2*z)^(2*k))) =O[sector (π-δ)] (fun z : ℂ => z^(-(2*(N+1):ℤ))) := by
  set c : ℕ → ℂ → ℂ := fun j w => 2 / π * ((-1) ^ (j + 1 + 1) * ((2 * (j + 1)).factorial : ℂ) *
      (2 * (j + 1) - 1).factorial / (((j + 1).factorial : ℂ) ^ 2 * (2 * w) ^ (2 * (j + 1)))) with hc
  have hGeq : (fun z : ℂ => DLMF.primitive (struveK 0) z - 2/π*(log (2*z)+Real.eulerMascheroniConstant)-2/π*∑ j ∈ Finset.range N, let k:=j+1; (-1)^(k+1)*((2*k).factorial:ℂ)*(2*k-1).factorial/((k.factorial:ℂ)^2*(2*z)^(2*k))) =
      fun z => (DLMF.primitive (struveK 0) z - 2 / π * (log (2 * z) + Real.eulerMascheroniConstant)) -
        ∑ j ∈ Finset.range N, c j z := by
    funext z
    simp only [hc, Finset.mul_sum]
  rw [hGeq]
  have hα0 : 0 ≤ π - δ := by linarith
  have hα : π - δ < π := by linarith
  -- the derivative bound
  obtain ⟨C, hCb⟩ := (struveK_asymptotic 0 hδ hδπ (N + 1)).bound
  obtain ⟨R, hR⟩ := struvePrim_exists_of_eventually_sector hCb
  have hexp : ∀ z : ℂ, z ≠ 0 → ‖z ^ ((0 : ℂ) - 2 * ((N + 1 : ℕ) : ℂ) - 1)‖ =
      ‖z‖ ^ (-(((2 * (N + 1) : ℕ) : ℤ) + 1)) := by
    intro z hz
    rw [norm_cpow_of_ne_zero hz]
    have him : ((0 : ℂ) - 2 * ((N + 1 : ℕ) : ℂ) - 1).im = 0 := by simp
    rw [him, mul_zero, Real.exp_zero, div_one]
    have : ((0 : ℂ) - 2 * ((N + 1 : ℕ) : ℂ) - 1).re = ((-(((2 * (N + 1) : ℕ) : ℤ) + 1) : ℤ) : ℝ) := by
      simp; ring
    rw [this, Real.rpow_intCast]
  have hmain := struvePrim_isBigO_of_deriv (G := fun z => (DLMF.primitive (struveK 0) z -
      2 / π * (log (2 * z) + Real.eulerMascheroniConstant)) - ∑ j ∈ Finset.range N, c j z)
    (G' := fun z => struveK 0 z - ∑ k ∈ Finset.range (N + 1), struveAsymptoticTerm 0 z k) hα0 hα
    (m := 2 * (N + 1)) (by omega) ?_ ?_ (R := max R 1) (C := C) (by positivity) ?_
  · convert hmain using 3; push_cast; ring
  · -- derivative
    intro z hz
    have hz0 : z ≠ 0 := slitPlane_ne_zero hz
    have h2z : 2 * z ∈ slitPlane := by
      rw [mem_slitPlane_iff] at hz ⊢
      simp only [mul_re, mul_im, re_ofNat, im_ofNat, zero_mul, sub_zero, add_zero]
      rcases hz with h | h
      · left; linarith
      · right; simpa using h
    have hlog : HasDerivAt (fun w : ℂ => 2 / π * (log (2 * w) + Real.eulerMascheroniConstant))
        (2 / (π * z)) z := by
      have h1 := ((((hasDerivAt_id' z).const_mul 2).clog h2z).add_const
        (Real.eulerMascheroniConstant : ℂ)).const_mul (2 / (π : ℂ))
      have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_pos.ne'
      convert h1 using 1
      field_simp
    have hsum : HasDerivAt (fun w => ∑ j ∈ Finset.range N, c j w)
        (∑ j ∈ Finset.range N, struveAsymptoticTerm 0 z (j + 1)) z :=
      HasDerivAt.fun_sum fun j _ => struvePrim_term_hasDerivAt j hz0
    convert ((struvePrim_hasDerivAt hz).sub hlog).sub hsum using 1
    rw [Finset.sum_range_succ', struvePrim_term_zero hz0]
    ring
  · -- limit on the positive axis
    have hterm : ∀ j : ℕ, Tendsto (fun t : ℝ => c j t) atTop (𝓝 0) := by
      intro j
      have hpow : Tendsto (fun t : ℝ => ((2 * (t : ℂ)) ^ (2 * (j + 1)))⁻¹) atTop (𝓝 0) := by
        refine tendsto_inv₀_cobounded.comp (tendsto_norm_atTop_iff_cobounded.1 ?_)
        have h2 : Tendsto (fun t : ℝ => (2 * t) ^ (2 * (j + 1))) atTop atTop :=
          (tendsto_pow_atTop (by omega)).comp (tendsto_id.const_mul_atTop two_pos)
        refine h2.congr' ((eventually_ge_atTop 0).mono fun t ht => ?_)
        simp only [norm_pow, norm_mul, norm_real, Real.norm_of_nonneg ht,
          RCLike.norm_ofNat]
      have := hpow.const_mul (2 / π * ((-1) ^ (j + 1 + 1) * ((2 * (j + 1)).factorial : ℂ) *
        (2 * (j + 1) - 1).factorial / (((j + 1).factorial : ℂ) ^ 2)))
      rw [mul_zero] at this
      refine this.congr fun t => ?_
      simp only [hc]
      rw [mul_assoc, div_mul_eq_div_div, div_eq_mul_inv _ ((2 * (t : ℂ)) ^ (2 * (j + 1)))]
    have := struvePrim_tendsto_ofReal.sub (tendsto_finsetSum (Finset.range N) fun j _ => hterm j)
    simpa using this
  · intro z hz harg
    have hz1 : 1 ≤ ‖z‖ := (le_max_right _ _).trans hz
    have hz0 : z ≠ 0 := norm_pos_iff.1 (by linarith)
    have h := hR z ((le_max_left _ _).trans hz) hz0 harg
    rwa [hexp z hz0] at h

/-- `(1 - t²)^{-1/2}` is integrable on `(0, 1]`. -/
theorem struvePrim_integrableOn_w :
    IntegrableOn (fun t : ℝ => 1 / Real.sqrt (1 - t ^ 2)) (Ioc 0 1) := by
  refine intervalIntegral.integrableOn_deriv_of_nonneg (g := Real.arcsin) Real.continuous_arcsin.continuousOn
    (fun t ht => Real.hasDerivAt_arcsin (by linarith [ht.1]) (by linarith [ht.2]))
    (fun t _ => by positivity)

/-- `∫₀¹ ((1-t²)^{-1/2} - (1+t²)^{-1/2})/t dt = log(1+√2)`, with integrability. -/
theorem struvePrim_integral_w_sub_g :
    IntegrableOn (fun t : ℝ => (1 / Real.sqrt (1 - t ^ 2) - 1 / Real.sqrt (1 + t ^ 2)) / t)
      (Ioc 0 1) ∧
    ∫ t in Ioc (0 : ℝ) 1, (1 / Real.sqrt (1 - t ^ 2) - 1 / Real.sqrt (1 + t ^ 2)) / t =
      Real.log (1 + Real.sqrt 2) := by
  set F : ℝ → ℝ := fun t => Real.log (1 + Real.sqrt (1 + t ^ 2)) -
    Real.log (1 + Real.sqrt (1 - t ^ 2)) with hF
  have hFc : ContinuousOn F (Icc 0 1) := by
    refine ContinuousOn.sub ?_ ?_
    · exact (Real.continuousOn_log.comp (by fun_prop : Continuous fun t : ℝ =>
        1 + Real.sqrt (1 + t ^ 2)).continuousOn fun t _ => by
          have := Real.sqrt_nonneg (1 + t ^ 2); simp only [mem_compl_iff, mem_singleton_iff]
          linarith)
    · exact (Real.continuousOn_log.comp (by fun_prop : Continuous fun t : ℝ =>
        1 + Real.sqrt (1 - t ^ 2)).continuousOn fun t _ => by
          have := Real.sqrt_nonneg (1 - t ^ 2); simp only [mem_compl_iff, mem_singleton_iff]
          linarith)
  have hFd : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt F
      ((1 / Real.sqrt (1 - t ^ 2) - 1 / Real.sqrt (1 + t ^ 2)) / t) t := by
    intro t ht
    have hS : 0 < 1 + t ^ 2 := by positivity
    have hQ : 0 < 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
    have hSs := Real.sqrt_pos.2 hS
    have hQs := Real.sqrt_pos.2 hQ
    have d1 : HasDerivAt (fun t : ℝ => 1 + t ^ 2) (2 * t) t := by
      simpa using ((hasDerivAt_pow 2 t).const_add 1)
    have d2 : HasDerivAt (fun t : ℝ => 1 - t ^ 2) (-(2 * t)) t := by
      simpa using ((hasDerivAt_pow 2 t).const_sub 1)
    have e1 := ((d1.sqrt hS.ne').const_add 1).log (by positivity)
    have e2 := ((d2.sqrt hQ.ne').const_add 1).log (by positivity)
    convert e1.sub e2 using 1
    have hS2 := Real.sq_sqrt hS.le
    have hQ2 := Real.sq_sqrt hQ.le
    have ht0 : t ≠ 0 := ht.1.ne'
    field_simp
    nlinarith [hS2, hQ2]
  have hnn : ∀ t ∈ Ioo (0 : ℝ) 1,
      0 ≤ (1 / Real.sqrt (1 - t ^ 2) - 1 / Real.sqrt (1 + t ^ 2)) / t := by
    intro t ht
    have hQ : 0 < 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
    refine div_nonneg (sub_nonneg.2 ?_) ht.1.le
    exact one_div_le_one_div_of_le (Real.sqrt_pos.2 hQ)
      (Real.sqrt_le_sqrt (by nlinarith))
  have hint := intervalIntegral.integrableOn_deriv_of_nonneg hFc hFd hnn
  refine ⟨hint, ?_⟩
  rw [← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hFc hFd
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).2 hint)]
  simp only [hF]
  norm_num

/-- `∫₁^∞ (1+τ²)^{-1/2}/τ dτ = log(1+√2)`, with integrability. -/
theorem struvePrim_integral_g_Ioi_one :
    IntegrableOn (fun t : ℝ => 1 / Real.sqrt (1 + t ^ 2) / t) (Ioi 1) ∧
    ∫ t in Ioi (1 : ℝ), 1 / Real.sqrt (1 + t ^ 2) / t = Real.log (1 + Real.sqrt 2) := by
  set H : ℝ → ℝ := fun t => Real.log t - Real.log (1 + Real.sqrt (1 + t ^ 2)) with hH
  have hHd : ∀ t ∈ Ici (1 : ℝ), HasDerivAt H (1 / Real.sqrt (1 + t ^ 2) / t) t := by
    intro t ht
    have ht0 : 0 < t := by linarith [mem_Ici.1 ht]
    have hS : 0 < 1 + t ^ 2 := by positivity
    have hSs := Real.sqrt_pos.2 hS
    have d1 : HasDerivAt (fun t : ℝ => 1 + t ^ 2) (2 * t) t := by
      simpa using ((hasDerivAt_pow 2 t).const_add 1)
    have e1 := ((d1.sqrt hS.ne').const_add 1).log (by positivity)
    convert (Real.hasDerivAt_log ht0.ne').sub e1 using 1
    have hS2 := Real.sq_sqrt hS.le
    field_simp
    nlinarith [hS2]
  have hnn : ∀ t ∈ Ioi (1 : ℝ), 0 ≤ 1 / Real.sqrt (1 + t ^ 2) / t := fun t ht => by
    have : (0 : ℝ) < t := by linarith [mem_Ioi.1 ht]
    positivity
  have hlim : Tendsto H atTop (𝓝 0) := by
    have heq : ∀ t : ℝ, 0 < t → H t = -Real.log ((1 + Real.sqrt (1 + t ^ 2)) / t) := by
      intro t ht
      simp only [hH]
      rw [Real.log_div (by positivity) ht.ne']; ring
    have h1 : Tendsto (fun t : ℝ => (1 + Real.sqrt (1 + t ^ 2)) / t) atTop (𝓝 1) := by
      have h2 : Tendsto (fun t : ℝ => 1 / t + Real.sqrt (1 / t ^ 2 + 1)) atTop (𝓝 (0 + Real.sqrt (0 + 1))) := by
        refine (tendsto_const_nhds.div_atTop tendsto_id).add ?_
        refine (Real.continuous_sqrt.tendsto _).comp ?_
        exact (tendsto_const_nhds.div_atTop (tendsto_pow_atTop two_ne_zero)).add tendsto_const_nhds
      rw [zero_add, zero_add, Real.sqrt_one] at h2
      refine h2.congr' ((eventually_gt_atTop 0).mono fun t ht => ?_)
      show _ = (1 + Real.sqrt (1 + t ^ 2)) / t
      have e : 1 / t ^ 2 + 1 = (1 + t ^ 2) / t ^ 2 := by field_simp
      rw [add_div, e, Real.sqrt_div (by positivity), Real.sqrt_sq ht.le]
    have h3 := (Real.continuousAt_log one_ne_zero).tendsto.comp h1
    rw [Real.log_one] at h3
    have h4 := h3.neg
    rw [neg_zero] at h4
    exact h4.congr' ((eventually_gt_atTop 0).mono fun t ht => (heq t ht).symm)
  have hint := integrableOn_Ioi_deriv_of_nonneg' hHd hnn hlim
  refine ⟨hint, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_nonneg' hHd hnn hlim]
  simp only [hH]
  norm_num

/-- The real Laplace form of `𝐌₀` on the positive axis (DLMF 11.5.4 with `ν = 0`). -/
theorem struvePrim_struveM_zero_ofReal {u : ℝ} (hu : 0 < u) :
    struveM 0 u = ((-(2 / π) * ∫ t in Ioc (0 : ℝ) 1,
      Real.exp (-(u * t)) * (1 / Real.sqrt (1 - t ^ 2)) : ℝ) : ℂ) := by
  rw [struveM_integral (ν := 0) (by norm_num) (ofReal_mem_slitPlane.2 hu)]
  have hG : Gamma (0 + 1 / 2) = ((Real.sqrt π : ℝ) : ℂ) := by
    rw [zero_add, Complex.Gamma_one_half_eq, Real.sqrt_eq_rpow, ofReal_cpow Real.pi_pos.le]
    push_cast; rfl
  have hint : ∫ t in (0 : ℝ)..1, exp (-(u : ℂ) * t) * (1 - (t : ℂ) ^ 2) ^ ((0 : ℂ) - 1 / 2) =
      ((∫ t in Ioc (0 : ℝ) 1, Real.exp (-(u * t)) * (1 / Real.sqrt (1 - t ^ 2)) : ℝ) : ℂ) := by
    rw [intervalIntegral.integral_of_le zero_le_one, ← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    have h0 : 0 ≤ 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
    have h1 : (1 - (t : ℂ) ^ 2) ^ ((0 : ℂ) - 1 / 2) = (((1 - t ^ 2) ^ (-(1 / 2) : ℝ) : ℝ) : ℂ) := by
      rw [ofReal_cpow h0]; push_cast; ring_nf
    rw [h1, Real.rpow_neg h0, ← Real.sqrt_eq_rpow, ofReal_mul, ofReal_exp]
    push_cast; ring_nf
  rw [hint, hG, cpow_zero]
  have hss : ((Real.sqrt π : ℝ) : ℂ) * (Real.sqrt π : ℝ) = (π : ℂ) := by
    rw [← ofReal_mul, Real.mul_self_sqrt Real.pi_pos.le]
  push_cast
  rw [mul_one, hss, neg_div]

/-- Fubini for the DLMF.primitive of `𝐌₀`:
`∫₀^x 𝐌₀ = -(2/π) ∫₀¹ (1-t²)^{-1/2} (1 - e^{-xt})/t dt`. -/
theorem struvePrim_primitive_M_ofReal {x : ℝ} (hx : 0 < x) :
    DLMF.primitive (struveM 0) x = ((-(2 / π) * ∫ t in Ioc (0 : ℝ) 1,
      (1 / Real.sqrt (1 - t ^ 2)) * ((1 - Real.exp (-(x * t))) / t) : ℝ) : ℂ) := by
  set g : ℝ → ℝ := fun t => 1 / Real.sqrt (1 - t ^ 2) with hg
  set k : ℝ → ℝ := fun u => -(2 / π) * ∫ t in Ioc (0 : ℝ) 1, Real.exp (-(u * t)) * g t with hk
  have hP : DLMF.primitive (struveM 0) x = ((∫ u in (0 : ℝ)..x, k u : ℝ) : ℂ) := by
    simp only [DLMF.primitive, segmentIntegral, sub_zero, zero_add]
    have h1 : ∫ t in (0 : ℝ)..1, struveM 0 (↑t * ↑x) = ∫ t in (0 : ℝ)..1, ((k (x * t) : ℝ) : ℂ) := by
      refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun t ht => ?_)
      rw [uIoc_of_le zero_le_one] at ht
      rw [← ofReal_mul, mul_comm t x, struvePrim_struveM_zero_ofReal (by nlinarith [ht.1])]
    rw [h1, intervalIntegral.integral_ofReal]
    have h2 := intervalIntegral.integral_comp_mul_left (a := 0) (b := 1) k hx.ne'
    rw [mul_zero, mul_one, smul_eq_mul] at h2
    rw [h2, ← ofReal_mul, mul_inv_cancel_left₀ hx.ne']
  rw [hP]
  congr 1
  set f : ℝ → ℝ → ℝ := fun u t => Real.exp (-(u * t)) * g t with hf
  have hg0 : ∀ t, 0 ≤ g t := fun t => by simp only [hg]; positivity
  have hinner : ∀ t ∈ Ioc (0 : ℝ) 1, ∫ u in Ioc 0 x, f u t = g t * ((1 - Real.exp (-(x * t))) / t) := by
    intro t ht
    rw [← intervalIntegral.integral_of_le hx.le]
    simp only [hf]
    rw [intervalIntegral.integral_mul_const, struvePrim_integral_exp (ne_of_gt ht.1), mul_comm]
  have hq : ∀ t ∈ Ioc (0 : ℝ) 1, 0 ≤ (1 - Real.exp (-(x * t))) / t ∧
      (1 - Real.exp (-(x * t))) / t ≤ x := by
    intro t ht
    have he1 : 1 - Real.exp (-(x * t)) ≤ x * t := by
      have := Real.add_one_le_exp (-(x * t)); linarith
    have : Real.exp (-(x * t)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [ht.1])
    exact ⟨div_nonneg (by linarith) ht.1.le, by rw [div_le_iff₀ ht.1]; linarith⟩
  have hgm : Measurable g := by simp only [hg]; fun_prop
  have hfm : Measurable (Function.uncurry f) := by
    simp only [hf]
    exact ((by fun_prop : Measurable fun p : ℝ × ℝ => Real.exp (-(p.1 * p.2)))).mul
      (hgm.comp measurable_snd)
  have hval : IntegrableOn (fun t => g t * ((1 - Real.exp (-(x * t))) / t)) (Ioc 0 1) := by
    refine Integrable.mono' (struvePrim_integrableOn_w.const_mul x)
      (((hgm.mul ((by fun_prop : Measurable fun t : ℝ => 1 - Real.exp (-(x * t))).div
        measurable_id))).aestronglyMeasurable) ?_
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun t ht => ?_)
    obtain ⟨h0, h1⟩ := hq t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hg0 t) h0)]
    exact (mul_le_mul_of_nonneg_left h1 (hg0 t)).trans_eq (mul_comm _ _)
  have hint : Integrable (Function.uncurry f)
      ((volume.restrict (Ioc 0 x)).prod (volume.restrict (Ioc (0 : ℝ) 1))) := by
    rw [integrable_prod_iff' hfm.aestronglyMeasurable]
    refine ⟨Eventually.of_forall fun t => ?_, ?_⟩
    · exact ((by fun_prop : Continuous fun u : ℝ => Real.exp (-(u * t)) * g t)).integrableOn_Ioc
    · refine hval.congr ((ae_restrict_iff' measurableSet_Ioc).mpr
        (Eventually.of_forall fun t ht => ?_))
      show g t * ((1 - Real.exp (-(x * t))) / t) = ∫ u in Ioc 0 x, ‖Function.uncurry f (u, t)‖
      rw [← hinner t ht]
      refine setIntegral_congr_fun measurableSet_Ioc fun u _ => ?_
      simp only [Function.uncurry_apply_pair, hf]
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (hg0 t))]
  rw [intervalIntegral.integral_of_le hx.le]
  simp only [hk]
  rw [integral_const_mul]
  congr 1
  have hsw := integral_integral_swap hint
  simp only [hf] at hsw
  rw [hsw]
  refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
  have := hinner t ht
  simp only [hf] at this
  rw [this]

/-- Dominated convergence for `∫_s h(t) (1 - e^{-xt}) dt → ∫_s h` as `x → ∞`, `s ⊆ (0, ∞)`. -/
theorem struvePrim_tendsto_integral_one_sub_exp {s : Set ℝ} (hs : MeasurableSet s)
    (hpos : s ⊆ Ioi 0) {h : ℝ → ℝ} (hi : IntegrableOn h s) :
    Tendsto (fun x : ℝ => ∫ t in s, h t * (1 - Real.exp (-(x * t)))) atTop
      (𝓝 (∫ t in s, h t)) := by
  have hlim : ∀ t ∈ s, Tendsto (fun x : ℝ => h t * (1 - Real.exp (-(x * t)))) atTop (𝓝 (h t)) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := hpos ht
    have h1 : Tendsto (fun x : ℝ => Real.exp (-(x * t))) atTop (𝓝 0) := by
      refine Real.tendsto_exp_atBot.comp ?_
      exact tendsto_neg_atTop_atBot.comp (tendsto_id.atTop_mul_const ht0)
    simpa using ((tendsto_const_nhds (x := (1 : ℝ))).sub h1).const_mul (h t)
  refine tendsto_integral_filter_of_dominated_convergence (fun t => ‖h t‖) ?_ ?_ hi.norm ?_
  · exact Eventually.of_forall fun x => hi.aestronglyMeasurable.mul
      ((by fun_prop : Continuous fun t : ℝ => 1 - Real.exp (-(x * t))).aestronglyMeasurable)
  · filter_upwards [eventually_ge_atTop 0] with x hx
    refine (ae_restrict_iff' hs).mpr (Eventually.of_forall fun t ht => ?_)
    have ht0 : (0 : ℝ) < t := hpos ht
    have he : Real.exp (-(x * t)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
    have he0 := Real.exp_pos (-(x * t))
    rw [norm_mul, Real.norm_eq_abs (1 - _), abs_of_nonneg (by linarith)]
    nlinarith [norm_nonneg (h t)]
  · exact (ae_restrict_iff' hs).mpr (Eventually.of_forall hlim)

/-- `∫₀¹ (1-t²)^{-1/2}(1 - e^{-xt})/t dt - (log 2x + γ) → 0` as `x → ∞`. -/
theorem struvePrim_tendsto_Phi :
    Tendsto (fun x : ℝ => (∫ t in Ioc (0 : ℝ) 1,
      (1 / Real.sqrt (1 - t ^ 2)) * ((1 - Real.exp (-(x * t))) / t)) -
        (Real.log (2 * x) + Real.eulerMascheroniConstant)) atTop (𝓝 0) := by
  set w : ℝ → ℝ := fun t => 1 / Real.sqrt (1 - t ^ 2) with hw
  set g : ℝ → ℝ := fun t => 1 / Real.sqrt (1 + t ^ 2) with hg
  set E : ℝ → ℝ → ℝ := fun x t => 1 - Real.exp (-(x * t)) with hE
  set Ψ : ℝ → ℝ := fun x => ∫ τ in Ioi (0 : ℝ), g τ * (E x τ / τ) with hΨ
  -- the `𝐊₀` side
  have hK : Tendsto (fun x : ℝ => Ψ x - (Real.log (2 * x) + Real.eulerMascheroniConstant))
      atTop (𝓝 0) := by
    have h := (Complex.continuous_re.tendsto 0).comp struvePrim_tendsto_ofReal
    rw [zero_re] at h
    have h2 := h.const_mul (π / 2)
    rw [mul_zero] at h2
    refine h2.congr' ((eventually_gt_atTop 0).mono fun x hx => ?_)
    simp only [Function.comp]
    rw [struvePrim_primitive_ofReal hx, show (2 : ℂ) * x = ((2 * x : ℝ) : ℂ) by push_cast; ring,
      ← ofReal_log (by positivity)]
    have hre : (((2 / π * ∫ τ in Ioi (0 : ℝ), 1 / Real.sqrt (1 + τ ^ 2) *
        ((1 - Real.exp (-(x * τ))) / τ) : ℝ) : ℂ) -
        2 / π * (((Real.log (2 * x)) : ℂ) + (Real.eulerMascheroniConstant : ℂ))).re =
        2 / π * (Ψ x - (Real.log (2 * x) + Real.eulerMascheroniConstant)) := by
      rw [show (2 : ℂ) / π = ((2 / π : ℝ) : ℂ) by push_cast; rfl, ← ofReal_add, ← ofReal_mul,
        ← ofReal_sub, ofReal_re]
      simp only [hΨ, hg, hE]; ring
    rw [hre]
    field_simp
  -- integrability facts
  have hI1 := struvePrim_integral_w_sub_g
  have hI2 := struvePrim_integral_g_Ioi_one
  have hmul : ∀ {s : Set ℝ}, MeasurableSet s → s ⊆ Ioi 0 → ∀ {h : ℝ → ℝ}, IntegrableOn h s →
      ∀ x : ℝ, 0 ≤ x → IntegrableOn (fun t => h t * E x t) s := by
    intro s hs hpos h hi x hx
    refine Integrable.mono' hi.norm (hi.aestronglyMeasurable.mul
      ((by fun_prop : Continuous fun t : ℝ => E x t).aestronglyMeasurable)) ?_
    refine (ae_restrict_iff' hs).mpr (Eventually.of_forall fun t ht => ?_)
    have ht0 : (0 : ℝ) < t := hpos ht
    have he : Real.exp (-(x * t)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
    have he0 := Real.exp_pos (-(x * t))
    simp only [hE]
    rw [norm_mul, Real.norm_eq_abs (1 - _), abs_of_nonneg (by linarith)]
    nlinarith [norm_nonneg (h t)]
  have hgm : Measurable g := by simp only [hg]; fun_prop
  have hsmall : ∀ x : ℝ, 0 < x → IntegrableOn (fun t => g t * (E x t / t)) (Ioc 0 1) := by
    intro x hx
    refine Measure.integrableOn_of_bounded (M := x) (by simp)
      ((hgm.mul ((by fun_prop : Measurable fun t : ℝ => E x t).div measurable_id)).aestronglyMeasurable) ?_
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun t ht => ?_)
    have he1 : 1 - Real.exp (-(x * t)) ≤ x * t := by
      have := Real.add_one_le_exp (-(x * t)); linarith
    have he : Real.exp (-(x * t)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [ht.1])
    have hq0 : 0 ≤ E x t / t := div_nonneg (by simp only [hE]; linarith) ht.1.le
    have hq : E x t / t ≤ x := by rw [div_le_iff₀ ht.1]; simp only [hE]; linarith
    have hg0 : 0 ≤ g t := by simp only [hg]; positivity
    have hg1 : g t ≤ 1 := by
      simp only [hg]; rw [div_le_one (Real.sqrt_pos.2 (by positivity))]
      exact Real.one_le_sqrt.2 (by nlinarith)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hg0 hq0)]
    calc g t * (E x t / t) ≤ 1 * x := mul_le_mul hg1 hq hq0 zero_le_one
      _ = x := one_mul x
  -- the decomposition
  have hdec : ∀ x : ℝ, 0 < x →
      (∫ t in Ioc (0 : ℝ) 1, w t * (E x t / t)) - Ψ x =
        (∫ t in Ioc (0 : ℝ) 1, ((w t - g t) / t) * E x t) -
          ∫ t in Ioi (1 : ℝ), (g t / t) * E x t := by
    intro x hx
    have hA := hmul measurableSet_Ioc Ioc_subset_Ioi_self hI1.1 x hx.le
    have hB := hmul measurableSet_Ioi (Ioi_subset_Ioi zero_le_one) hI2.1 x hx.le
    have h1 : ∫ t in Ioc (0 : ℝ) 1, w t * (E x t / t) =
        (∫ t in Ioc (0 : ℝ) 1, ((w t - g t) / t) * E x t) +
          ∫ t in Ioc (0 : ℝ) 1, g t * (E x t / t) := by
      rw [← integral_add hA (hsmall x hx)]
      refine setIntegral_congr_fun measurableSet_Ioc fun t _ => ?_
      ring
    have h2 : Ψ x = (∫ t in Ioc (0 : ℝ) 1, g t * (E x t / t)) +
        ∫ t in Ioi (1 : ℝ), (g t / t) * E x t := by
      have hB' : IntegrableOn (fun t => g t * (E x t / t)) (Ioi 1) :=
        hB.congr_fun (fun t _ => by ring) measurableSet_Ioi
      simp only [hΨ]
      rw [← Ioc_union_Ioi_eq_Ioi zero_le_one, setIntegral_union (Ioc_disjoint_Ioi le_rfl)
        measurableSet_Ioi (hsmall x hx) hB']
      congr 1
      refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
      ring
    rw [h1, h2]; ring
  have hL1 := struvePrim_tendsto_integral_one_sub_exp measurableSet_Ioc Ioc_subset_Ioi_self hI1.1
  have hL2 := struvePrim_tendsto_integral_one_sub_exp measurableSet_Ioi
    (Ioi_subset_Ioi zero_le_one) hI2.1
  rw [hI1.2] at hL1
  rw [hI2.2] at hL2
  have hfin := (hL1.sub hL2).add hK
  rw [sub_self, zero_add] at hfin
  refine hfin.congr' ((eventually_gt_atTop 0).mono fun x hx => ?_)
  have := hdec x hx
  simp only [hE, hw, hg] at this ⊢
  linarith

/-- `𝐌₀` is entire. -/
theorem struvePrim_differentiable_struveM_zero : Differentiable ℂ (struveM 0) := by
  have hL : Differentiable ℂ (struveL 0) := by simpa using struveL_nat_entire 0
  have hI : Differentiable ℂ (besselI 0) := by
    have he : besselI 0 = fun z => regularizedHGFun (∅ : Multiset ℂ) {0 + 1} (z ^ 2 / 4) := by
      funext z; simp [besselI]
    rw [he]
    exact fun z => ((analyticAt_regularized0F1 _ _).differentiableAt).comp z
      ((differentiableAt_pow 2).div_const 4)
  exact hL.sub hI

/-- The DLMF.primitive `∫₀^z 𝐌₀` differentiates to `𝐌₀`. -/
theorem struvePrim_hasDerivAt_M (z : ℂ) :
    HasDerivAt (DLMF.primitive (struveM 0)) (struveM 0 z) z := by
  have hP : DLMF.primitive (struveM 0) =
      fun w : ℂ => w * ∫ t in (0 : ℝ)..1, struveM 0 ((t : ℂ) * w) := by
    funext w; simp [DLMF.primitive, segmentIntegral]
  rw [hP]
  exact Complex.hasDerivAt_mul_integral_comp_mul struvePrim_differentiable_struveM_zero z

/-- `∫₀^x 𝐌₀ + (2/π)(log 2x + γ) → 0` as `x → +∞` (the constant in DLMF 11.6.4). -/
theorem struvePrim_tendsto_M_ofReal :
    Tendsto (fun x : ℝ => DLMF.primitive (struveM 0) x +
      2 / π * (log (2 * x) + Real.eulerMascheroniConstant)) atTop (𝓝 0) := by
  have h0 := struvePrim_tendsto_Phi.const_mul (-(2 / π))
  rw [mul_zero] at h0
  have h := (Complex.continuous_ofReal.tendsto 0).comp h0
  rw [ofReal_zero] at h
  refine h.congr' ((eventually_gt_atTop 0).mono fun x hx => ?_)
  simp only [Function.comp]
  rw [struvePrim_primitive_M_ofReal hx, show (2 : ℂ) * x = ((2 * x : ℝ) : ℂ) by push_cast; ring,
    ← ofReal_log (by positivity)]
  push_cast
  ring

/-- Asymptotic bound with the indicated comparison function: `(fun z : ℂ => DLMF.primitive
(struveM 0) z + 2/π*(log (2*z)+Real.eulerMascheroniConstant)-2/π*∑ j ∈ Finset.range N, let
k:=j+1; 1*((2*k).factorial:ℂ)*(2*k-1).factorial/((k.factorial:ℂ)^2*(2*z)^(2*k))) =O[sector
(π/2-δ)] (fun z : ℂ => z^(-(2*(N+1):ℤ)))`. -/
@[dlmf 11.6.E4]
theorem struveM_primitive_asymptotic {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π/2) (N : ℕ) :
    (fun z : ℂ => DLMF.primitive (struveM 0) z + 2/π*(log (2*z)+Real.eulerMascheroniConstant)-2/π*∑ j ∈ Finset.range N, let k:=j+1; 1*((2*k).factorial:ℂ)*(2*k-1).factorial/((k.factorial:ℂ)^2*(2*z)^(2*k))) =O[sector (π/2-δ)] (fun z : ℂ => z^(-(2*(N+1):ℤ))) := by
  set c : ℕ → ℂ → ℂ := fun j w => 2 / π * ((-1) ^ (j + 1 + 1) * ((2 * (j + 1)).factorial : ℂ) *
      (2 * (j + 1) - 1).factorial / (((j + 1).factorial : ℂ) ^ 2 * (2 * w) ^ (2 * (j + 1)))) with hc
  have hsq : ∀ j : ℕ, ((-1 : ℂ) ^ (j + 1 + 1)) * (-1) ^ (j + 1 + 1) = 1 := fun j => by
    rw [← mul_pow]; norm_num
  have hGeq : (fun z : ℂ => DLMF.primitive (struveM 0) z + 2/π*(log (2*z)+Real.eulerMascheroniConstant)-2/π*∑ j ∈ Finset.range N, let k:=j+1; 1*((2*k).factorial:ℂ)*(2*k-1).factorial/((k.factorial:ℂ)^2*(2*z)^(2*k))) =
      fun z => (DLMF.primitive (struveM 0) z +
        2 / π * (log (2 * z) + Real.eulerMascheroniConstant)) -
        ∑ j ∈ Finset.range N, (-1) ^ (j + 1 + 1) * c j z := by
    funext z
    simp only [hc, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    have := hsq j
    linear_combination (-(2 / (π : ℂ)) * (((2 * (j + 1)).factorial : ℂ) *
      (2 * (j + 1) - 1).factorial / (((j + 1).factorial : ℂ) ^ 2 * (2 * z) ^ (2 * (j + 1))))) * this
  rw [hGeq]
  have hα0 : 0 ≤ π / 2 - δ := by linarith
  have hα : π / 2 - δ < π := by linarith [Real.pi_pos]
  obtain ⟨C, hCb⟩ := (struveM_asymptotic 0 hδ hδπ (N + 1)).bound
  obtain ⟨R, hR⟩ := struvePrim_exists_of_eventually_sector hCb
  have hexp : ∀ z : ℂ, z ≠ 0 → ‖z ^ ((0 : ℂ) - 2 * ((N + 1 : ℕ) : ℂ) - 1)‖ =
      ‖z‖ ^ (-(((2 * (N + 1) : ℕ) : ℤ) + 1)) := by
    intro z hz
    rw [norm_cpow_of_ne_zero hz]
    have him : ((0 : ℂ) - 2 * ((N + 1 : ℕ) : ℂ) - 1).im = 0 := by simp
    rw [him, mul_zero, Real.exp_zero, div_one]
    have : ((0 : ℂ) - 2 * ((N + 1 : ℕ) : ℂ) - 1).re = ((-(((2 * (N + 1) : ℕ) : ℤ) + 1) : ℤ) : ℝ) := by
      simp; ring
    rw [this, Real.rpow_intCast]
  have hmain := struvePrim_isBigO_of_deriv (G := fun z => (DLMF.primitive (struveM 0) z +
      2 / π * (log (2 * z) + Real.eulerMascheroniConstant)) -
        ∑ j ∈ Finset.range N, (-1) ^ (j + 1 + 1) * c j z)
    (G' := fun z => struveM 0 z -
      ∑ k ∈ Finset.range (N + 1), (-1) ^ (k + 1) * struveAsymptoticTerm 0 z k) hα0 hα
    (m := 2 * (N + 1)) (by omega) ?_ ?_ (R := max R 1) (C := C) (by positivity) ?_
  · convert hmain using 3; push_cast; ring
  · intro z hz
    have hz0 : z ≠ 0 := slitPlane_ne_zero hz
    have h2z : 2 * z ∈ slitPlane := by
      rw [mem_slitPlane_iff] at hz ⊢
      simp only [mul_re, mul_im, re_ofNat, im_ofNat, zero_mul, sub_zero, add_zero]
      rcases hz with h | h
      · left; linarith
      · right; simpa using h
    have hlog : HasDerivAt (fun w : ℂ => 2 / π * (log (2 * w) + Real.eulerMascheroniConstant))
        (2 / (π * z)) z := by
      have h1 := ((((hasDerivAt_id' z).const_mul 2).clog h2z).add_const
        (Real.eulerMascheroniConstant : ℂ)).const_mul (2 / (π : ℂ))
      have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_pos.ne'
      convert h1 using 1
      field_simp
    have hsum : HasDerivAt (fun w => ∑ j ∈ Finset.range N, (-1) ^ (j + 1 + 1) * c j w)
        (∑ j ∈ Finset.range N, (-1) ^ (j + 1 + 1) * struveAsymptoticTerm 0 z (j + 1)) z :=
      HasDerivAt.fun_sum fun j _ => (struvePrim_term_hasDerivAt j hz0).const_mul _
    convert ((struvePrim_hasDerivAt_M z).add hlog).sub hsum using 1
    rw [Finset.sum_range_succ', struvePrim_term_zero hz0]
    ring
  · have hterm : ∀ j : ℕ, Tendsto (fun t : ℝ => (-1) ^ (j + 1 + 1) * c j t) atTop (𝓝 0) := by
      intro j
      have hpow : Tendsto (fun t : ℝ => ((2 * (t : ℂ)) ^ (2 * (j + 1)))⁻¹) atTop (𝓝 0) := by
        refine tendsto_inv₀_cobounded.comp (tendsto_norm_atTop_iff_cobounded.1 ?_)
        have h2 : Tendsto (fun t : ℝ => (2 * t) ^ (2 * (j + 1))) atTop atTop :=
          (tendsto_pow_atTop (by omega)).comp (tendsto_id.const_mul_atTop two_pos)
        refine h2.congr' ((eventually_ge_atTop 0).mono fun t ht => ?_)
        simp only [norm_pow, norm_mul, norm_real, Real.norm_of_nonneg ht, RCLike.norm_ofNat]
      have := hpow.const_mul ((-1) ^ (j + 1 + 1) * (2 / π * ((-1) ^ (j + 1 + 1) *
        ((2 * (j + 1)).factorial : ℂ) *
        (2 * (j + 1) - 1).factorial / (((j + 1).factorial : ℂ) ^ 2))))
      rw [mul_zero] at this
      refine this.congr fun t => ?_
      simp only [hc]
      rw [mul_assoc, mul_assoc, div_mul_eq_div_div, div_eq_mul_inv _ ((2 * (t : ℂ)) ^ (2 * (j + 1)))]
    have := struvePrim_tendsto_M_ofReal.sub
      (tendsto_finsetSum (Finset.range N) fun j _ => hterm j)
    simpa using this
  · intro z hz harg
    have hz1 : 1 ≤ ‖z‖ := (le_max_right _ _).trans hz
    have hz0 : z ≠ 0 := norm_pos_iff.1 (by linarith)
    have h := hR z ((le_max_left _ _).trans hz) hz0 harg
    rwa [hexp z hz0] at h

end StruvePrimitive

end DLMF.Struve
end
