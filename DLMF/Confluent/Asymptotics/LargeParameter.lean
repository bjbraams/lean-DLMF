/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Confluent.Asymptotics.LargeArgument

/-!
# Large-parameter confluent hypergeometric expansions

Large-second-parameter expansions of regularized Kummer functions and their limiting forms.

Source references and common attribution are retained in
`DLMF.Confluent.Asymptotics`.
-/

@[expose] public section

open Complex Filter MeasureTheory Asymptotics

open scoped Real Topology Nat

open DLMF.Hypergeometric

noncomputable section

namespace DLMF.Confluent

/-! ### The large-`b` expansion 13.8.2

For `re a > 0`, Euler's integral in the variable `s = 1 - e^{-t}` is the Laplace transform
`∫₀^∞ e^{-bt} t^{a-1} q(t) dt` of the generating function 13.8.3, and Watson's lemma gives
`b^a Γ(b-a)/Γ(b) M(a,b,z) ~ ∑ (a)_s q_s(z) b^{-s}` (`hcub_largeB_base`). For every `a`,
13.8.1 multiplied by the Gamma-ratio expansion 5.11.13 gives an expansion of the same function
with explicit coefficients `hcub_largeBMix` (`hcub_largeB_mix`). Uniqueness of asymptotic
expansions identifies the two coefficient sequences for `re a > 0`; both are entire in `a`
(the `q_s` through Cauchy's integral formula), so the identity theorem gives the coefficient
identity for all `a` (`hcub_largeBMix_eq`), and with it 13.8.2 without restriction on `a`.
-/

section LargeBPoincare

open Set

/-- The large-`b` generating function is analytic at `t = 0`. -/
theorem hcub_analyticAt_largeBGenerating (a z : ℂ) : AnalyticAt ℂ (largeBGenerating a z) 0 := by
  have h1 : expSubOneDiv 0 ∈ slitPlane := by simp [expSubOneDiv]
  have h2 : AnalyticAt ℂ (fun t : ℂ => exp (t + z * (1 - exp (-t)))) 0 :=
    (analyticAt_id.add (analyticAt_const.mul (analyticAt_const.sub analyticAt_id.neg.cexp))).cexp
  exact ((analyticAt_expSubOneDiv 0).cpow analyticAt_const h1).mul h2

/-- The Taylor remainder of the large-`b` generating function after `N` terms is `O(|t|^N)` as `t →
0`. -/
theorem hcub_largeB_taylor (a z : ℂ) (N : ℕ) :
    (fun t => largeBGenerating a z t - ∑ n ∈ Finset.range N, largeBCoeff a z n * t ^ n)
      =O[𝓝 0] fun t => ‖t‖ ^ N := by
  have h := (hcub_analyticAt_largeBGenerating a z).hasFPowerSeriesAt.isBigO_sub_partialSum_pow N
  refine h.congr' (Eventually.of_forall fun s => ?_) EventuallyEq.rfl
  simp only [zero_add, FormalMultilinearSeries.partialSum,
    FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, largeBCoeff]

/-- The substitution `s = 1 - e^{-t}` transforms the Euler integrand of `M(a,b,z)` into `e^{-bt}
t^{a-1} G(a,z,t)`, with `G` the large-`b` generating function. -/
theorem hcub_subst (a z : ℂ) (b : ℝ) {t : ℝ} (ht : 0 < t) :
    |Real.exp (-t)| • (((1 - Real.exp (-t) : ℝ) : ℂ) ^ (a - 1) *
      (1 - ((1 - Real.exp (-t) : ℝ) : ℂ)) ^ ((b : ℂ) - a - 1) *
        exp (z * ((1 - Real.exp (-t) : ℝ) : ℂ))) =
    Real.exp (-b * t) • ((t : ℂ) ^ (a - 1) * largeBGenerating a z t) := by
  set E : ℝ := (Real.exp t - 1) / t with hE
  have hE0 : 0 < E := div_pos (by linarith [Real.add_one_lt_exp ht.ne']) ht
  have hEc : expSubOneDiv (t : ℂ) = (E : ℂ) := by
    rw [expSubOneDiv, ite_eq_right_iff.mpr (fun h => absurd h (by exact_mod_cast ht.ne')), hE]
    push_cast; rfl
  have hs : (1 - Real.exp (-t) : ℝ) = Real.exp (-t) * (t * E) := by
    rw [hE, Real.exp_neg]; field_simp
  have hc : ((1 - Real.exp (-t) : ℝ) : ℂ) ^ (a - 1) =
      exp (-(t : ℂ) * (a - 1)) * ((t : ℂ) ^ (a - 1) * (E : ℂ) ^ (a - 1)) := by
    rw [hs, Complex.ofReal_mul, mul_cpow_ofReal_nonneg (Real.exp_pos _).le
      (by positivity), Complex.ofReal_mul, mul_cpow_ofReal_nonneg ht.le hE0.le, hcub_ofReal_cpow_exp]
    push_cast; ring_nf
  rw [hc, show (1 : ℂ) - ((1 - Real.exp (-t) : ℝ) : ℂ) = ((Real.exp (-t) : ℝ) : ℂ) by push_cast; ring,
    hcub_ofReal_cpow_exp, abs_of_pos (Real.exp_pos _), Complex.real_smul,
    Complex.real_smul, largeBGenerating, hEc]
  push_cast
  have e1 : exp (-(t : ℂ)) * (exp (-(t : ℂ) * (a - 1)) * ((t : ℂ) ^ (a - 1) * (E : ℂ) ^ (a - 1)) *
      exp (-(t : ℂ) * ((b : ℂ) - a - 1)) * exp (z * (1 - exp (-(t : ℂ))))) =
      (t : ℂ) ^ (a - 1) * (E : ℂ) ^ (a - 1) *
        exp (-(t : ℂ) + -(t : ℂ) * (a - 1) + -(t : ℂ) * ((b : ℂ) - a - 1) +
          z * (1 - exp (-(t : ℂ)))) := by
    simp only [Complex.exp_add]; ring
  have e2 : exp (-(b : ℂ) * t) * ((t : ℂ) ^ (a - 1) * ((E : ℂ) ^ (a - 1) *
      exp (t + z * (1 - exp (-(t : ℂ)))))) =
      (t : ℂ) ^ (a - 1) * (E : ℂ) ^ (a - 1) *
        exp (-(b : ℂ) * t + (t + z * (1 - exp (-(t : ℂ))))) := by
    simp only [Complex.exp_add]; ring
  rw [e1, e2]
  congr 2
  ring

/-- The Euler integral `∫₀¹ s^{a-1}(1-s)^{b-a-1} e^{zs} ds` equals the Laplace integral `∫₀^∞
e^{-bt} t^{a-1} G(a,z,t) dt`. -/
theorem hcub_euler_eq_laplace (a z : ℂ) (b : ℝ) :
    ∫ s : ℝ in (0 : ℝ)..1, (s : ℂ) ^ (a - 1) * (1 - (s : ℂ)) ^ ((b : ℂ) - a - 1) * exp (z * s) =
      ∫ t in Ioi (0 : ℝ), Real.exp (-b * t) • ((t : ℂ) ^ (a - 1) * largeBGenerating a z t) := by
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo, ← hcub_image,
    integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi (fun t _ => hcub_hasDerivWithinAt t)
      hcub_injOn]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  exact hcub_subst a z b ht

/-- For `0 < Re a < b`, the Laplace integrand `e^{-bt} t^{a-1} G(a,z,t)` is integrable on `(0, ∞)`.
-/
theorem hcub_integrableOn (a z : ℂ) (ha : 0 < a.re) {b : ℝ} (hb : a.re < b) :
    IntegrableOn (fun t : ℝ => Real.exp (-b * t) • ((t : ℂ) ^ (a - 1) * largeBGenerating a z t))
      (Ioi 0) := by
  have hβ := betaIntegral_convergent (u := a) (v := (b : ℂ) - a) ha (by simp; linarith)
  have h1 : IntervalIntegrable (fun s : ℝ => (s : ℂ) ^ (a - 1) * (1 - (s : ℂ)) ^ ((b : ℂ) - a - 1) *
      exp (z * s)) volume 0 1 := hβ.mul_continuousOn (by fun_prop)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at h1
  have h2 := h1.mono_set Ioo_subset_Ioc_self
  rw [← hcub_image, integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi
    (fun t _ => hcub_hasDerivWithinAt t) hcub_injOn] at h2
  refine h2.congr_fun (fun t ht => hcub_subst a z b ht) measurableSet_Ioi

/-- Watson's lemma for the Laplace form of Euler's integral: the large-`b` expansion of
`b^a Γ(b-a)/Γ(b) M(a,b,z)` when `re a > 0`. -/
theorem hcub_largeB_base (a z : ℂ) (ha : 0 < a.re) (n : ℕ) :
    (fun b : ℝ => (b : ℂ) ^ a * Gamma (b - a) / Gamma b * kummerM a b z -
       ∑ s ∈ Finset.range n, poch a s * largeBCoeff a z s * ((b : ℂ)⁻¹) ^ s)
      =O[atTop] fun b => ((b : ℂ)⁻¹) ^ n := by
  set F : ℝ → ℂ := fun t => (t : ℂ) ^ (a - 1) * largeBGenerating a z t with hF
  have hF : ∀ N : ℕ, (fun t : ℝ => F t - ∑ k ∈ Finset.range N,
      ((t : ℂ) ^ ((k : ℂ) + a - 1)) • largeBCoeff a z k) =O[𝓝[>] 0]
        fun t : ℝ => t ^ ((N : ℝ) + a.re - 1) := by
    intro N
    have hT : (fun t : ℝ => largeBGenerating a z t - ∑ k ∈ Finset.range N,
        largeBCoeff a z k * (t : ℂ) ^ k) =O[𝓝[>] 0] fun t : ℝ => ‖(t : ℂ)‖ ^ N := by
      have hc : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[>] 0) (𝓝 0) := by
        have := (continuous_ofReal.tendsto (0 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
        simpa using this
      exact (hcub_largeB_taylor a z N).comp_tendsto hc
    have hT' : (fun t : ℝ => largeBGenerating a z t - ∑ k ∈ Finset.range N,
        largeBCoeff a z k * (t : ℂ) ^ k) =O[𝓝[>] 0] fun t : ℝ => (t : ℂ) ^ N :=
      hT.trans (IsBigO.of_bound 1 (Eventually.of_forall fun t => by simp))
    have hm := (isBigO_refl (fun t : ℝ => (t : ℂ) ^ (a - 1)) (𝓝[>] 0)).mul hT'
    refine (hm.congr' ?_ EventuallyEq.rfl).trans (IsBigO.of_bound 1 ?_)
    · filter_upwards [self_mem_nhdsWithin] with t ht
      have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt ht)
      simp only [hF, mul_sub, Finset.mul_sum, smul_eq_mul]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [show (k : ℂ) + a - 1 = (k : ℂ) + (a - 1) by ring, cpow_add _ _ ht0, cpow_natCast]
      ring
    · filter_upwards [self_mem_nhdsWithin] with t ht
      have ht' : (0 : ℝ) < t := ht
      rw [norm_mul, norm_pow, norm_cpow_eq_rpow_re_of_pos ht', Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos ht', Real.norm_eq_abs,
        abs_of_pos (Real.rpow_pos_of_pos ht' _), one_mul,
        show (N : ℝ) + a.re - 1 = (a - 1).re + N by simp; ring, Real.rpow_add ht',
        Real.rpow_natCast]
  have hW := hasAsymptoticExpansion_integral_exp_smul_cpow (μ := a) (c := a.re + 1) ha
    (hcub_integrableOn a z ha (by linarith)) hF n
  have hm := (isBigO_refl (fun b : ℝ => (b : ℂ) ^ a / Gamma a) atTop).mul hW
  have hGa : Gamma a ≠ 0 := Gamma_ne_zero (not_neg_nat_of_re_pos ha)
  refine (hm.congr' ?_ ?_).trans (isBigO_const_mul_self (Gamma a)⁻¹ _ atTop)
  · filter_upwards [eventually_gt_atTop (a.re + 1)] with b hb
    have hb0 : 0 < b := by linarith
    have hba : 0 < ((b : ℂ) - a).re := by simp; linarith
    have hGb : Gamma (b : ℂ) ≠ 0 := Gamma_ne_zero (not_neg_nat_of_re_pos (by simpa using hb0))
    have hGba : Gamma ((b : ℂ) - a) ≠ 0 := Gamma_ne_zero (not_neg_nat_of_re_pos hba)
    rw [kummerM_eq_euler_integral ha hba, hcub_euler_eq_laplace]
    simp only [smul_eq_mul, mul_sub, Finset.mul_sum]
    congr 1
    · field_simp
    · refine Finset.sum_congr rfl fun s _ => ?_
      have hp : Gamma ((s : ℂ) + a) = Gamma a * poch a s := by
        have h1 := DLMF.Gamma.poch_mul_recip_Gamma_add_nat a s
        have h2 : Gamma (a + s) ≠ 0 := Gamma_ne_zero (not_neg_nat_of_re_pos (by simp; positivity))
        rw [add_comm]
        field_simp at h1
        linear_combination -h1
      rw [hp, ← hcub_cpow_mul_cpow_neg hb0 a s]
      field_simp
  · filter_upwards [eventually_gt_atTop 0] with b hb
    rw [← hcub_cpow_mul_cpow_neg hb a n]
    field_simp

/-- `b^a Γ(b-a)/Γ(b+s) = ∑_{k<n-s} G_k b^{-s-k} + O(b^{-n})`, from the Gamma-ratio expansion
5.11.13. -/
theorem hcub_ratio_shift_kummer (a : ℂ) {s n : ℕ} (hs : s ≤ n) :
    (fun b : ℝ => (b : ℂ) ^ a * Gamma ((b : ℂ) - a) / Gamma ((b : ℂ) + s) -
      ∑ k ∈ Finset.range (n - s), DLMF.Gamma.stirlingRatioG (-a) s k * ((b : ℂ)⁻¹) ^ (s + k))
      =O[atTop] fun b => ((b : ℂ)⁻¹) ^ n := by
  have h := DLMF.Gamma.Gamma_ratio_expansion (-a) (s : ℂ) (n - s)
  have hm := (isBigO_refl (fun b : ℝ => (b : ℂ) ^ a) atTop).mul h
  refine hm.congr' ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with b hb
    have hb0 : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
    rw [mul_sub, Finset.mul_sum, Finset.mul_sum, ← sub_eq_add_neg]
    congr 1
    · ring
    · refine Finset.sum_congr rfl fun k _ => ?_
      have := hcub_cpow_mul_cpow_neg hb a s
      rw [show -a - (s : ℂ) = -((s : ℂ) + a) by ring, pow_add, ← this, inv_pow]
      ring
  · filter_upwards [eventually_gt_atTop 0] with b hb
    rw [show -a - (s : ℂ) - ((n - s : ℕ) : ℂ) = -((n : ℂ) + a) by push_cast [hs]; ring,
      hcub_cpow_mul_cpow_neg hb]

/-- `b^a Γ(b-a)/Γ(b)` is bounded as `b → +∞`. -/
theorem hcub_ratio_isBigO_one (a : ℂ) :
    (fun b : ℝ => (b : ℂ) ^ a * Gamma ((b : ℂ) - a) / Gamma (b : ℂ)) =O[atTop]
      fun _ => (1 : ℂ) := by
  have h := hcub_ratio_shift_kummer a (s := 0) (n := 0) le_rfl
  simpa using h

/-- Coefficients of 13.8.1 re-expanded in powers of `1/b` after multiplication by
`b^a Γ(b-a)/Γ(b)`. -/
noncomputable def hcub_largeBMix (a z : ℂ) (N : ℕ) : ℂ :=
  ∑ s ∈ Finset.range (N + 1), poch a s * z ^ s / s ! * DLMF.Gamma.stirlingRatioG (-a) s (N - s)

/-- 13.8.1 re-expanded: `b^a Γ(b-a)/Γ(b) M(a,b,z) ~ ∑ hcub_largeBMix a z N b^{-N}` for all `a`. -/
theorem hcub_largeB_mix (a z : ℂ) (n : ℕ) :
    (fun b : ℝ => (b : ℂ) ^ a * Gamma (b - a) / Gamma b * kummerM a b z -
       ∑ N ∈ Finset.range n, hcub_largeBMix a z N * ((b : ℂ)⁻¹) ^ N)
      =O[atTop] fun b => ((b : ℂ)⁻¹) ^ n := by
  have h1 := kummerM_large_b a z n
  have h2 := ((hcub_ratio_isBigO_one a).mul h1).congr_right fun b => one_mul _
  have h3 : (fun b : ℝ => ∑ s ∈ Finset.range n, poch a s * z ^ s / s ! *
      ((b : ℂ) ^ a * Gamma ((b : ℂ) - a) / Gamma ((b : ℂ) + s) -
        ∑ k ∈ Finset.range (n - s), DLMF.Gamma.stirlingRatioG (-a) s k * ((b : ℂ)⁻¹) ^ (s + k)))
      =O[atTop] fun b => ((b : ℂ)⁻¹) ^ n :=
    IsBigO.fun_sum fun s hs => (hcub_ratio_shift_kummer a
      (Finset.mem_range.mp hs).le).const_mul_left _
  refine (h2.add h3).congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_gt_atTop 0] with b hb
  have hb' : ∀ k : ℕ, (b : ℂ) ≠ -k := not_neg_nat_of_re_pos (by simpa using hb)
  have hGb : Gamma (b : ℂ) ≠ 0 := Gamma_ne_zero hb'
  have hflip := Finset.sum_range_diag_flip n fun s k =>
    poch a s * z ^ s / s ! * (DLMF.Gamma.stirlingRatioG (-a) s k * ((b : ℂ)⁻¹) ^ (s + k))
  simp only [hcub_largeBMix, Finset.sum_mul]
  have hN : ∀ m ∈ Finset.range n, ∑ k ∈ Finset.range (m + 1),
      poch a k * z ^ k / k ! * DLMF.Gamma.stirlingRatioG (-a) k (m - k) * ((b : ℂ)⁻¹) ^ m =
      ∑ k ∈ Finset.range (m + 1), poch a k * z ^ k / k ! *
        (DLMF.Gamma.stirlingRatioG (-a) k (m - k) * ((b : ℂ)⁻¹) ^ (k + (m - k))) := by
    intro m _
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Nat.add_sub_cancel' (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))]
    ring
  rw [Finset.sum_congr rfl hN, hflip]
  have hS : ∀ s ∈ Finset.range n, poch a s / (poch (b : ℂ) s * s !) * z ^ s *
      ((b : ℂ) ^ a * Gamma ((b : ℂ) - a) / Gamma (b : ℂ)) =
      poch a s * z ^ s / s ! * ((b : ℂ) ^ a * Gamma ((b : ℂ) - a) / Gamma ((b : ℂ) + s)) := by
    intro s _
    have h := DLMF.Gamma.poch_mul_recip_Gamma_add_nat (b : ℂ) s
    have hp : poch (b : ℂ) s ≠ 0 := poch_ne_zero_of_not_neg_nat hb' s
    have hGs : Gamma ((b : ℂ) + s) ≠ 0 := Gamma_ne_zero (not_neg_nat_of_re_pos (by simp; positivity))
    have hf : (s ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    field_simp at h
    rw [← h]
    field_simp
  simp only [mul_sub, Finset.mul_sum] at *
  rw [Finset.sum_congr rfl (fun s hs => (mul_comm _ _).trans (hS s hs))]
  simp only [Finset.sum_sub_distrib]
  ring

/-- For `re a > 0` the re-expanded coefficients of 13.8.1 are those of 13.8.2. -/
theorem hcub_largeBMix_eq_of_re_pos (a z : ℂ) (ha : 0 < a.re) (N : ℕ) :
    hcub_largeBMix a z N = poch a N * largeBCoeff a z N := by
  have h := HasAsymptoticExpansion.unique hcub_isAsymptoticScale hcub_frequently_ne
    (a := hcub_largeBMix a z) (b := fun N => poch a N * largeBCoeff a z N)
    (f := fun b : ℝ => (b : ℂ) ^ a * Gamma (b - a) / Gamma b * kummerM a b z)
    (fun n => (hcub_largeB_mix a z n).congr_left fun b => by
      simp only [smul_eq_mul]; congr 1; exact Finset.sum_congr rfl fun _ _ => mul_comm _ _)
    (fun n => (hcub_largeB_base a z ha n).congr_left fun b => by
      simp only [smul_eq_mul]; congr 1; exact Finset.sum_congr rfl fun _ _ => mul_comm _ _)
  exact congrFun h N

/-- The explicit large-`b` coefficient sum is entire in `a`. -/
theorem hcub_differentiable_largeBMix (z : ℂ) (N : ℕ) :
    Differentiable ℂ (fun a => hcub_largeBMix a z N) := by
  unfold hcub_largeBMix
  refine Differentiable.fun_sum fun s _ => ?_
  exact (((Polynomial.differentiable _).mul (differentiable_const _)).div_const _).mul
    ((hcub_differentiable_stirlingRatioG _ _).comp differentiable_neg)

/-- The large-`b` generating function is complex differentiable in `t` for `|t| ≤ 1/2`. -/
theorem hcub_differentiableAt_largeBGenerating (a z : ℂ) {t : ℂ} (ht : ‖t‖ ≤ 1 / 2) :
    DifferentiableAt ℂ (largeBGenerating a z) t := by
  have hE : DifferentiableAt ℂ expSubOneDiv t := (analyticAt_expSubOneDiv t).differentiableAt
  show DifferentiableAt ℂ (fun t => expSubOneDiv t ^ (a - 1) * exp (t + z * (1 - exp (-t)))) t
  exact (hE.cpow (differentiableAt_const _) (hcub_expSubOneDiv_mem_slitPlane ht)).mul
    (by fun_prop)

/-- Each large-`b` coefficient is an entire function of `a`. -/
theorem hcub_differentiable_largeBCoeff (z : ℂ) (N : ℕ) :
    Differentiable ℂ (fun a => largeBCoeff a z N) := by
  have hE : ∀ t : ℂ, DifferentiableAt ℂ expSubOneDiv t := fun t =>
    (analyticAt_expSubOneDiv t).differentiableAt
  have hrest : ∀ t : ℂ, DifferentiableAt ℂ (fun t : ℂ => exp (t + z * (1 - exp (-t)))) t :=
    fun t => by fun_prop
  have h := hcub_differentiable_iteratedDeriv (G := fun a t => largeBGenerating a z t)
    (r := 1 / 2) (by norm_num)
    (fun a t ht => by
      have hEc : ContinuousAt (fun p : ℂ × ℂ => expSubOneDiv p.2) (a, t) :=
        ContinuousAt.comp (f := fun p : ℂ × ℂ => p.2) (g := expSubOneDiv) (hE t).continuousAt
          continuous_snd.continuousAt
      have hpow : ContinuousAt (fun p : ℂ × ℂ => expSubOneDiv p.2 ^ (p.1 - 1)) (a, t) :=
        hEc.cpow (continuous_fst.sub continuous_const).continuousAt
          (hcub_expSubOneDiv_mem_slitPlane ht.le)
      have hr : ContinuousAt (fun p : ℂ × ℂ => exp (p.2 + z * (1 - exp (-p.2)))) (a, t) :=
        ContinuousAt.comp (f := fun p : ℂ × ℂ => p.2)
          (g := fun t : ℂ => exp (t + z * (1 - exp (-t)))) (hrest t).continuousAt
          continuous_snd.continuousAt
      exact hpow.mul hr)
    (fun a t ht => (hcub_differentiableAt_largeBGenerating a z
      (by simpa using ht)).differentiableWithinAt)
    (fun t ht => by
      have h0 : expSubOneDiv t ≠ 0 := slitPlane_ne_zero (hcub_expSubOneDiv_mem_slitPlane ht.le)
      intro a
      exact ((differentiableAt_id.sub (differentiableAt_const _)).const_cpow
        (Or.inl h0)).mul (differentiableAt_const _)) N
  exact h.div_const _

/-- The coefficient identity behind 13.8.2, for all `a`: the re-expansion of 13.8.1 has the
coefficients `(a)_N q_N(a,z)`. Proved for `re a > 0` by uniqueness of asymptotic expansions
(Watson's lemma on one side, 13.8.1 on the other) and continued by the identity theorem. -/
theorem hcub_largeBMix_eq (a z : ℂ) (N : ℕ) :
    hcub_largeBMix a z N = poch a N * largeBCoeff a z N := by
  set f : ℂ → ℂ := fun a => hcub_largeBMix a z N - poch a N * largeBCoeff a z N with hfdef
  have hf : Differentiable ℂ f := (hcub_differentiable_largeBMix z N).sub
    ((Polynomial.differentiable _).mul (hcub_differentiable_largeBCoeff z N))
  have hA : AnalyticOnNhd ℂ f univ := fun x _ => hf.analyticAt x
  have h0 : f =ᶠ[𝓝 1] 0 := by
    have hopen : IsOpen {a : ℂ | 0 < a.re} := isOpen_lt continuous_const continuous_re
    filter_upwards [hopen.mem_nhds (by simp : (1 : ℂ) ∈ {a : ℂ | 0 < a.re})] with x hx
    simp [hfdef, hcub_largeBMix_eq_of_re_pos x z hx N]
  have := hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (mem_univ 1) h0
    (mem_univ a)
  simpa [hfdef, sub_eq_zero] using this

/-- `Γ(b)/Γ(b-a) b^{-a}` is bounded as `b → +∞`. -/
theorem hcub_ratio_isBigO_one' (a : ℂ) :
    (fun b : ℝ => Gamma (b : ℂ) / Gamma ((b : ℂ) - a) * (b : ℂ) ^ (-a)) =O[atTop]
      fun _ => (1 : ℂ) := by
  have h := DLMF.Gamma.Gamma_ratio_expansion 0 (-a) 0
  have hm := (isBigO_refl (fun b : ℝ => (b : ℂ) ^ (-a)) atTop).mul h
  refine hm.congr' (Eventually.of_forall fun b => ?_) ?_
  · simp [sub_eq_add_neg]; ring
  · filter_upwards [eventually_gt_atTop 0] with b hb
    have hb0 : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
    rw [← cpow_add _ _ hb0]; simp

end LargeBPoincare

/- The Gamma ratio grows like b^a, so the absolute remainder is O(b^(-n)). -/
/-- Formula under the stated hypotheses: `Asymptotics.IsBigO atTop (fun b : ℝ => kummerM a b z -
Gamma (b : ℂ) / Gamma ((b : ℂ) - a) * ∑ s ∈ Finset.range n, poch a s * largeBCoeff a z s * (b
: ℂ) ^ (-(s : ℂ) - a)) (fun b : ℝ => (b : ℂ) ^ (-(n : ℂ)))`. -/
@[dlmf 13.8.E2]
theorem kummerM_large_b_poincare (a z : ℂ) (n : ℕ) :
    Asymptotics.IsBigO atTop
      (fun b : ℝ => kummerM a b z -
        Gamma (b : ℂ) / Gamma ((b : ℂ) - a) *
          ∑ s ∈ Finset.range n, poch a s * largeBCoeff a z s * (b : ℂ) ^ (-(s : ℂ) - a))
      (fun b : ℝ => (b : ℂ) ^ (-(n : ℂ))) := by
  have hK := hcub_largeB_mix a z n
  simp only [hcub_largeBMix_eq] at hK
  refine ((hcub_ratio_isBigO_one' a).mul hK).congr' ?_ ?_
  · filter_upwards [eventually_gt_atTop (max 0 a.re)] with b hb
    have hb0' : 0 < b := lt_of_le_of_lt (le_max_left _ _) hb
    have hb0 : (b : ℂ) ≠ 0 := by exact_mod_cast hb0'.ne'
    have hba : 0 < ((b : ℂ) - a).re := by simp; linarith [le_max_right 0 a.re]
    have hGb : Gamma (b : ℂ) ≠ 0 := Gamma_ne_zero (not_neg_nat_of_re_pos (by simpa using hb0'))
    have hGba : Gamma ((b : ℂ) - a) ≠ 0 := Gamma_ne_zero (not_neg_nat_of_re_pos hba)
    have hpa : (b : ℂ) ^ (-a) * (b : ℂ) ^ a = 1 := by
      rw [← cpow_add _ _ hb0]; simp
    have hs : ∀ s : ℕ, (b : ℂ) ^ (-(s : ℂ) - a) = (b : ℂ) ^ (-a) * ((b : ℂ)⁻¹) ^ s := by
      intro s
      rw [sub_eq_add_neg, add_comm, cpow_add _ _ hb0, cpow_neg (b : ℂ) (s : ℂ), cpow_natCast,
        inv_pow]
    simp only [hs, mul_sub, Finset.mul_sum]
    congr 1
    · field_simp
      linear_combination (kummerM a b z) * hpa
    · refine Finset.sum_congr rfl fun s _ => by ring
  · filter_upwards [eventually_gt_atTop 0] with b hb
    rw [one_mul, cpow_neg, cpow_natCast, inv_pow]

/-- Identity under the stated parameter and domain assumptions: `Asymptotics.IsBigO atTop (fun b :
ℝ => kummerM a b b - (Real.sqrt π : ℂ) * (b / 2 : ℂ) ^ (a / 2) * (1 / Gamma ((a + 1) / 2) + (a
+ 1) * (8 / b : ℂ) ^ (1 / 2 : ℂ) / (3 * Gamma (a / 2)))) (fun b : ℝ => (b : ℂ) ^ (a / 2 -
1))`. -/
@[dlmf 13.8.E6]
theorem kummerM_transition (a : ℂ) :
    Asymptotics.IsBigO atTop
      (fun b : ℝ => kummerM a b b -
        (Real.sqrt π : ℂ) * (b / 2 : ℂ) ^ (a / 2) *
          (1 / Gamma ((a + 1) / 2) + (a + 1) * (8 / b : ℂ) ^ (1 / 2 : ℂ) / (3 * Gamma (a / 2))))
      (fun b : ℝ => (b : ℂ) ^ (a / 2 - 1)) := by
  sorry

/-- Identity under the stated parameter and domain assumptions: `Asymptotics.IsBigO atTop (fun b :
ℝ => kummerU a b b - (Real.sqrt π : ℂ) * (2 * b : ℂ) ^ (-(a / 2)) * (1 / Gamma ((a + 1) / 2) -
(a + 1) * (8 / b : ℂ) ^ (1 / 2 : ℂ) / (3 * Gamma (a / 2)))) (fun b : ℝ => (b : ℂ) ^ (-(a / 2)
- 1))`. -/
@[dlmf 13.8.E7]
theorem kummerU_transition (a : ℂ) :
    Asymptotics.IsBigO atTop
      (fun b : ℝ => kummerU a b b -
        (Real.sqrt π : ℂ) * (2 * b : ℂ) ^ (-(a / 2)) *
          (1 / Gamma ((a + 1) / 2) - (a + 1) * (8 / b : ℂ) ^ (1 / 2 : ℂ) / (3 * Gamma (a / 2))))
      (fun b : ℝ => (b : ℂ) ^ (-(a / 2) - 1)) := by
  sorry

/- DLMF uses scaled Gamma in M, ordinary Gamma in U, and a relative error in U.
The parameter ray is real and positive, as in the source statement. -/
/-- Identity under the stated parameter and domain assumptions: `Asymptotics.IsBigO atTop (fun a :
ℝ => kummerM a (a / ν) z - exp (ν * z) * DLMF.Gamma.scaledGamma (a / ν : ℂ) /
DLMF.Gamma.scaledGamma (a : ℂ) * (1 + (1 - ν) * (1 + 6 * ν ^ 2 * z ^ 2) / (12 * a))) (fun a :
ℝ => (a : ℂ)⁻¹ ^ 2)`. -/
@[dlmf 13.8.E17]
theorem kummerM_large_a_b (ν : ℝ) (z : ℂ) (hν : 0 < ν) (hν1 : ν < 1) :
    Asymptotics.IsBigO atTop
      (fun a : ℝ => kummerM a (a / ν) z -
        exp (ν * z) * DLMF.Gamma.scaledGamma (a / ν : ℂ) / DLMF.Gamma.scaledGamma (a : ℂ) *
          (1 + (1 - ν) * (1 + 6 * ν ^ 2 * z ^ 2) / (12 * a)))
      (fun a : ℝ => (a : ℂ)⁻¹ ^ 2) := by
  sorry

/-- Identity under the stated parameter and domain assumptions: `Asymptotics.IsBigO atTop (fun a :
ℝ => kummerU a (a / ν + 1) z - z ^ (-(a / ν : ℂ)) * exp ((1 - ν) * z) * Gamma (a / ν : ℂ) /
Gamma (a : ℂ) * (1 + ν * z * (1 - ν) * (2 - ν * z) / (2 * a))) (fun a : ℝ => z ^ (-(a / ν :
ℂ)) * exp ((1 - ν) * z) * Gamma (a / ν : ℂ) / Gamma (a : ℂ) * (a : ℂ)⁻¹ ^ 2)`. -/
@[dlmf 13.8.E18]
theorem kummerU_large_a_b (ν : ℝ) (z : ℂ) (hν : 0 < ν) (hν1 : ν < 1)
    (hz : 0 < z.re) :
    Asymptotics.IsBigO atTop
      (fun a : ℝ => kummerU a (a / ν + 1) z -
        z ^ (-(a / ν : ℂ)) * exp ((1 - ν) * z) * Gamma (a / ν : ℂ) / Gamma (a : ℂ) *
          (1 + ν * z * (1 - ν) * (2 - ν * z) / (2 * a)))
      (fun a : ℝ => z ^ (-(a / ν : ℂ)) * exp ((1 - ν) * z) *
        Gamma (a / ν : ℂ) / Gamma (a : ℂ) * (a : ℂ)⁻¹ ^ 2) := by
  sorry

/-- Formula under the stated hypotheses: `Asymptotics.IsBigO atTop (fun x : ℝ => whittakerM κ μ x
- Gamma (1 + 2 * μ) / Gamma (1 / 2 + μ - κ) * exp (x / 2) * (x : ℂ) ^ (-κ) * ∑ s ∈
Finset.range n, poch (1 / 2 - μ + κ) s * poch (1 / 2 + μ + κ) s / s.factorial * (x : ℂ) ^ (-(s
: ℂ))) (fun x : ℝ => exp (x / 2) * (x : ℂ) ^ (-κ - n))`. -/
@[dlmf 13.19.E1]
theorem whittakerM_poincare_real (κ μ : ℂ) (n : ℕ)
    (hκ : ∀ k : ℕ, μ - κ ≠ -1 / 2 - k) (hμ : ∀ k : ℕ, 1 + 2 * μ ≠ -k) :
    Asymptotics.IsBigO atTop
      (fun x : ℝ => whittakerM κ μ x -
        Gamma (1 + 2 * μ) / Gamma (1 / 2 + μ - κ) * exp (x / 2) * (x : ℂ) ^ (-κ) *
          ∑ s ∈ Finset.range n,
            poch (1 / 2 - μ + κ) s * poch (1 / 2 + μ + κ) s / s.factorial *
              (x : ℂ) ^ (-(s : ℂ)))
      (fun x : ℝ => exp (x / 2) * (x : ℂ) ^ (-κ - n)) := by
  have h := regularizedHGFun_poincare_real (μ - κ + 1 / 2) (1 + 2 * μ) n (fun k hk =>
    hκ k (by linear_combination hk))
  rw [show 1 - (μ - κ + 1 / 2) = 1 / 2 - μ + κ by ring,
    show 1 + 2 * μ - (μ - κ + 1 / 2) = 1 / 2 + μ + κ by ring,
    show μ - κ + 1 / 2 = 1 / 2 + μ - κ by ring] at h
  refine (((isBigO_refl (fun x : ℝ => Gamma (1 + 2 * μ) * exp (-x / 2) * (x : ℂ) ^ (μ + 1 / 2))
    atTop).mul h).congr' ?_ ?_).trans (isBigO_const_mul_self (Gamma (1 + 2 * μ))
      (fun x : ℝ => exp (x / 2) * (x : ℂ) ^ (-κ - n)) atTop)
  · filter_upwards [eventually_gt_atTop 0] with x hx
    have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
    rw [whittakerM, kummerM_eq_mul_regularizedHGFun hμ]
    have hp : exp (-(x : ℂ) / 2) * (x : ℂ) ^ (μ + 1 / 2) * (exp (x : ℂ) *
        (x : ℂ) ^ (1 / 2 + μ - κ - (1 + 2 * μ))) = exp ((x : ℂ) / 2) * (x : ℂ) ^ (-κ) := by
      rw [show exp (-(x : ℂ) / 2) * (x : ℂ) ^ (μ + 1 / 2) * (exp (x : ℂ) *
        (x : ℂ) ^ (1 / 2 + μ - κ - (1 + 2 * μ))) = (exp (-(x : ℂ) / 2) * exp (x : ℂ)) *
          ((x : ℂ) ^ (μ + 1 / 2) * (x : ℂ) ^ (1 / 2 + μ - κ - (1 + 2 * μ))) by ring,
        ← Complex.exp_add, ← Complex.cpow_add _ _ hx0]
      ring_nf
    rw [show 1 / 2 + μ - κ = μ - κ + 1 / 2 by ring] at hp ⊢
    linear_combination (-Gamma (1 + 2 * μ) / Gamma (μ - κ + 1 / 2) * ∑ s ∈ Finset.range n,
      poch (1 / 2 - μ + κ) s * poch (1 / 2 + μ + κ) s / s.factorial *
        (x : ℂ) ^ (-(s : ℂ))) * hp
  · filter_upwards [eventually_gt_atTop 0] with x hx
    have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
    rw [show Gamma (1 + 2 * μ) * exp (-(x : ℂ) / 2) * (x : ℂ) ^ (μ + 1 / 2) *
      (exp (x : ℂ) * (x : ℂ) ^ (1 / 2 + μ - κ - (1 + 2 * μ) - n)) =
      Gamma (1 + 2 * μ) * ((exp (-(x : ℂ) / 2) * exp (x : ℂ)) *
        ((x : ℂ) ^ (μ + 1 / 2) * (x : ℂ) ^ (1 / 2 + μ - κ - (1 + 2 * μ) - n))) by ring,
      ← Complex.exp_add, ← Complex.cpow_add _ _ hx0]
    ring_nf

/-- Formula under the stated hypotheses: `Asymptotics.IsBigO atTop (fun x : ℝ => whittakerW κ μ x
- exp (-x / 2) * (x : ℂ) ^ κ * ∑ s ∈ Finset.range n, poch (1 / 2 + μ - κ) s * poch (1 / 2 - μ
- κ) s / s.factorial * (-(x : ℂ)) ^ (-(s : ℂ))) (fun x : ℝ => exp (-x / 2) * (x : ℂ) ^ (κ -
n))`. -/
@[dlmf 13.19.E3]
theorem whittakerW_poincare (κ μ : ℂ) (n : ℕ) :
    Asymptotics.IsBigO atTop
      (fun x : ℝ => whittakerW κ μ x -
        exp (-x / 2) * (x : ℂ) ^ κ *
          ∑ s ∈ Finset.range n,
            poch (1 / 2 + μ - κ) s * poch (1 / 2 - μ - κ) s / s.factorial *
              (-(x : ℂ)) ^ (-(s : ℂ)))
      (fun x : ℝ => exp (-x / 2) * (x : ℂ) ^ (κ - n)) := by
  have h := kummerU_poincare (1 / 2 + μ - κ) (1 + 2 * μ) n
  rw [show 1 / 2 + μ - κ - (1 + 2 * μ) + 1 = 1 / 2 - μ - κ by ring] at h
  refine ((isBigO_refl (fun x : ℝ => exp (-x / 2) * (x : ℂ) ^ (1 / 2 + μ)) atTop).mul h
    ).congr' ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with x hx
    have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
    rw [whittakerW_eq_kummerU (by simpa using hx)]
    have hp : (x : ℂ) ^ (1 / 2 + μ) * (x : ℂ) ^ (-(1 / 2 + μ - κ)) = (x : ℂ) ^ κ := by
      rw [← Complex.cpow_add _ _ hx0]; ring_nf
    linear_combination (-exp (-x / 2) * ∑ s ∈ Finset.range n,
      poch (1 / 2 + μ - κ) s * poch (1 / 2 - μ - κ) s / s.factorial *
        (-(x : ℂ)) ^ (-(s : ℂ))) * hp
  · filter_upwards [eventually_gt_atTop 0] with x hx
    have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
    rw [mul_assoc, ← Complex.cpow_add _ _ hx0]
    ring_nf

end DLMF.Confluent

end
end
