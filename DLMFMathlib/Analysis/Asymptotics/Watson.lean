/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.Asymptotics.AsymptoticExpansion
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Watson's lemma

Let `F : ℝ → E` have the expansion `F(t) ~ ∑ aₙ t^{n+μ-1}` as `t → 0⁺`, with `μ > 0`, and let
`e^{-ct} F(t)` be integrable on `(0, ∞)` for some `c`. Then the Laplace transform has the
asymptotic expansion

`∫₀^∞ e^{-zt} F(t) dt ~ ∑ Γ(n+μ) aₙ z^{-(n+μ)}`   as `z → +∞`

(Temme, *Special Functions*, Theorem 2.4, for real `z`). The proof splits the remainder
integral at a small `δ`: near `0` the hypothesis gives `O(z^{-(N+μ)})` through the Gamma
integral, and beyond `δ` the factor `e^{-zt}` contributes `O(e^{-δz})`, which is smaller than
any power of `z`.

## Main results

* `integral_exp_neg_mul_mul_rpow_sub_one`: `∫₀^∞ e^{-zt} t^{s-1} dt = Γ(s) z^{-s}`, and its
  complex-exponent version `integral_exp_neg_mul_smul_cpow_sub_one`.
* `isBigO_integral_exp_smul`: if `G(t) = O(t^{s-1})` at `0⁺`, then the Laplace transform of `G`
  is `O(z^{-s})`.
* `hasAsymptoticExpansion_integral_exp_smul`: Watson's lemma.
* `hasAsymptoticExpansion_integral_exp_smul_cpow`: Watson's lemma with a complex exponent `μ`,
  `re μ > 0`, and coefficients in a complex normed space.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Finset Asymptotics

open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- `t ↦ e^{-zt} t^{s-1}` is integrable on `(0, ∞)` for `s, z > 0`. -/
theorem integrableOn_exp_neg_mul_mul_rpow_sub_one {s z : ℝ} (hs : 0 < s) (hz : 0 < z) :
    IntegrableOn (fun t : ℝ => Real.exp (-z * t) * t ^ (s - 1)) (Ioi 0) := by
  have := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := s - 1) (b := z) (by linarith)
    one_pos hz
  refine this.congr_fun (fun t _ => ?_) measurableSet_Ioi
  simp only [Real.rpow_one]
  ring

/-- `∫₀^∞ e^{-zt} t^{s-1} dt = Γ(s) z^{-s}` for `s, z > 0`. -/
theorem integral_exp_neg_mul_mul_rpow_sub_one {s z : ℝ} (hs : 0 < s) (hz : 0 < z) :
    ∫ t in Ioi (0 : ℝ), Real.exp (-z * t) * t ^ (s - 1) = Real.Gamma s * z ^ (-s) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi hs hz
  rw [Real.div_rpow zero_le_one hz.le, Real.one_rpow, one_div, ← Real.rpow_neg hz.le] at h
  rw [mul_comm (Real.Gamma s), ← h]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  ring_nf

omit [CompleteSpace E] in
/-- Integrability of `e^{-wt} F` for `w ≥ c`, given that of `e^{-ct} F`. -/
theorem MeasureTheory.IntegrableOn.exp_neg_mul_smul_of_le {F : ℝ → E} {c w : ℝ}
    (hint : IntegrableOn (fun t => Real.exp (-c * t) • F t) (Ioi 0)) (hw : c ≤ w) :
    IntegrableOn (fun t => Real.exp (-w * t) • F t) (Ioi 0) := by
  have hFm : AEStronglyMeasurable F (volume.restrict (Ioi 0)) := by
    have hc : AEStronglyMeasurable (fun t : ℝ => Real.exp (c * t)) (volume.restrict (Ioi 0)) :=
      (by fun_prop : Continuous fun t : ℝ => Real.exp (c * t)).aestronglyMeasurable
    refine (hc.smul hint.aestronglyMeasurable).congr (Eventually.of_forall fun t => ?_)
    show Real.exp (c * t) • (Real.exp (-c * t) • F t) = F t
    rw [smul_smul, ← Real.exp_add]
    simp
  refine hint.norm.mono' (((by fun_prop : Continuous fun t : ℝ => Real.exp (-w * t)
    ).aestronglyMeasurable).smul hFm) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
  simp only [norm_smul, Real.norm_eq_abs, Real.abs_exp]
  exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by nlinarith [mem_Ioi.mp ht]))
    (norm_nonneg _)

omit [CompleteSpace E] in
/-- **Watson remainder bound.** If `G(t) = O(t^{s-1})` as `t → 0⁺` with `s > 0`, and `e^{-ct} G`
is integrable on `(0, ∞)`, then `∫₀^∞ e^{-zt} G(t) dt = O(z^{-s})` as `z → +∞`. -/
theorem isBigO_integral_exp_smul {G : ℝ → E} {s c : ℝ} (hs : 0 < s)
    (hint : IntegrableOn (fun t => Real.exp (-c * t) • G t) (Ioi 0))
    (hG : G =O[𝓝[>] 0] fun t => t ^ (s - 1)) :
    (fun z => ∫ t in Ioi (0 : ℝ), Real.exp (-z * t) • G t) =O[atTop] fun z => z ^ (-s) := by
  -- replace `c` by `c' = max c 0 ≥ 0`
  set c' := max c 0 with hc'
  have hc'0 : 0 ≤ c' := le_max_right _ _
  have hintG : ∀ w : ℝ, c ≤ w → IntegrableOn (fun t => Real.exp (-w * t) • G t) (Ioi 0) :=
    fun w hw => hint.exp_neg_mul_smul_of_le hw
  -- the bound near `0`
  obtain ⟨K, hK, hKw⟩ := hG.exists_pos
  obtain ⟨ε, hε, hεb⟩ := Metric.eventually_nhds_iff.mp
    (eventually_nhdsWithin_iff.mp hKw.bound)
  set δ := ε / 2 with hδ
  have hδ0 : 0 < δ := by positivity
  have hGb : ∀ t ∈ Ioc (0 : ℝ) δ, ‖G t‖ ≤ K * t ^ (s - 1) := by
    intro t ht
    have h := hεb (y := t) (by rw [Real.dist_eq, sub_zero, abs_of_pos ht.1]; linarith [ht.2])
      ht.1
    rwa [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos ht.1 _)] at h
  -- the tail constant
  set A := ∫ t in Ioi (0 : ℝ), Real.exp (-(c' + 1) * t) * ‖G t‖ with hA
  have hAint : IntegrableOn (fun t => Real.exp (-(c' + 1) * t) * ‖G t‖) (Ioi 0) := by
    have h := (hintG (c' + 1) (by linarith [le_max_left c 0])).norm
    exact IntegrableOn.congr_fun h (fun t _ => by simp [norm_smul, Real.abs_exp])
      measurableSet_Ioi
  -- the exponential is smaller than any power
  have hexp : ∀ᶠ z in atTop, Real.exp (-δ * z) ≤ z ^ (-s) := by
    have h := (isLittleO_rpow_exp_pos_mul_atTop s hδ0).bound one_pos
    filter_upwards [h, eventually_gt_atTop 0] with z hz hz0
    rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hz0 _),
      Real.abs_exp] at hz
    rw [Real.rpow_neg hz0.le, neg_mul, Real.exp_neg]
    exact inv_anti₀ (Real.rpow_pos_of_pos hz0 _) hz
  refine IsBigO.of_bound (K * Real.Gamma s + A * Real.exp ((c' + 1) * δ)) ?_
  filter_upwards [hexp, eventually_ge_atTop (c' + 1)] with z hze hz
  have hz0 : 0 < z := by linarith
  have hzc : c ≤ z := by linarith [le_max_left c 0]
  rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hz0 _)]
  -- split the integral at `δ`
  have hI := hintG z hzc
  rw [← Ioc_union_Ioi_eq_Ioi hδ0.le, setIntegral_union (Ioc_disjoint_Ioi le_rfl)
    measurableSet_Ioi (hI.mono_set Ioc_subset_Ioi_self) (hI.mono_set (Ioi_subset_Ioi hδ0.le))]
  refine (norm_add_le _ _).trans ?_
  have h1 : ‖∫ t in Ioc (0 : ℝ) δ, Real.exp (-z * t) • G t‖ ≤ K * Real.Gamma s * z ^ (-s) := by
    refine (norm_integral_le_integral_norm _).trans ?_
    have hmono : ∫ t in Ioc (0 : ℝ) δ, ‖Real.exp (-z * t) • G t‖ ≤
        ∫ t in Ioc (0 : ℝ) δ, K * (Real.exp (-z * t) * t ^ (s - 1)) := by
      refine setIntegral_mono_on (hI.mono_set Ioc_subset_Ioi_self).norm
        (((integrableOn_exp_neg_mul_mul_rpow_sub_one hs hz0).mono_set
          Ioc_subset_Ioi_self).const_mul K) measurableSet_Ioc fun t ht => ?_
      rw [norm_smul, Real.norm_eq_abs, Real.abs_exp]
      have := hGb t ht
      have he := Real.exp_pos (-z * t)
      nlinarith
    refine hmono.trans ?_
    rw [MeasureTheory.integral_const_mul, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hK.le
    rw [← integral_exp_neg_mul_mul_rpow_sub_one hs hz0]
    refine setIntegral_mono_set (integrableOn_exp_neg_mul_mul_rpow_sub_one hs hz0)
      ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_))
      (Eventually.of_forall Ioc_subset_Ioi_self)
    exact mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (le_of_lt ht) _)
  have h2 : ‖∫ t in Ioi δ, Real.exp (-z * t) • G t‖ ≤
      A * Real.exp ((c' + 1) * δ) * z ^ (-s) := by
    refine (norm_integral_le_integral_norm _).trans ?_
    have hmono : ∫ t in Ioi δ, ‖Real.exp (-z * t) • G t‖ ≤
        ∫ t in Ioi δ, Real.exp (-(z - c' - 1) * δ) * (Real.exp (-(c' + 1) * t) * ‖G t‖) := by
      refine setIntegral_mono_on (hI.mono_set (Ioi_subset_Ioi hδ0.le)).norm
        ((hAint.mono_set (Ioi_subset_Ioi hδ0.le)).const_mul _) measurableSet_Ioi
        fun t ht => ?_
      have ht' : δ < t := ht
      rw [norm_smul, Real.norm_eq_abs, Real.abs_exp, ← mul_assoc, ← Real.exp_add]
      refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
      nlinarith
    refine hmono.trans ?_
    rw [MeasureTheory.integral_const_mul]
    have hAle : ∫ t in Ioi δ, Real.exp (-(c' + 1) * t) * ‖G t‖ ≤ A :=
      setIntegral_mono_set hAint
        ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t _ => by positivity))
        (Eventually.of_forall (Ioi_subset_Ioi hδ0.le))
    have hsplit : Real.exp (-(z - c' - 1) * δ) = Real.exp ((c' + 1) * δ) * Real.exp (-δ * z) := by
      rw [← Real.exp_add]; ring_nf
    rw [hsplit]
    calc Real.exp ((c' + 1) * δ) * Real.exp (-δ * z) *
          ∫ t in Ioi δ, Real.exp (-(c' + 1) * t) * ‖G t‖
        ≤ Real.exp ((c' + 1) * δ) * z ^ (-s) * A := by
          gcongr
      _ = A * Real.exp ((c' + 1) * δ) * z ^ (-s) := by ring
  calc ‖∫ t in Ioc (0 : ℝ) δ, Real.exp (-z * t) • G t‖ + ‖∫ t in Ioi δ, Real.exp (-z * t) • G t‖
      ≤ K * Real.Gamma s * z ^ (-s) + A * Real.exp ((c' + 1) * δ) * z ^ (-s) := add_le_add h1 h2
    _ = _ := by ring

/-- **Watson's lemma.** If `F(t) - ∑_{n<N} t^{n+μ-1} aₙ = O(t^{N+μ-1})` as `t → 0⁺` for every
`N`, with `μ > 0`, and `e^{-ct} F` is integrable on `(0, ∞)`, then
`∫₀^∞ e^{-zt} F(t) dt ~ ∑ Γ(n+μ) aₙ z^{-(n+μ)}` as `z → +∞`. -/
theorem hasAsymptoticExpansion_integral_exp_smul {F : ℝ → E} {a : ℕ → E} {μ c : ℝ}
    (hμ : 0 < μ) (hint : IntegrableOn (fun t => Real.exp (-c * t) • F t) (Ioi 0))
    (hF : ∀ N : ℕ, (fun t => F t - ∑ n ∈ range N, t ^ ((n : ℝ) + μ - 1) • a n) =O[𝓝[>] 0]
      fun t => t ^ ((N : ℝ) + μ - 1)) :
    HasAsymptoticExpansion atTop (fun (n : ℕ) (z : ℝ) => z ^ (-((n : ℝ) + μ)))
      (fun n => Real.Gamma ((n : ℝ) + μ) • a n)
      (fun z => ∫ t in Ioi (0 : ℝ), Real.exp (-z * t) • F t) := by
  intro N
  set c' := max c 0 + 1 with hc'
  have hcc' : c ≤ c' := by linarith [le_max_left c 0]
  have hc'0 : 0 < c' := by linarith [le_max_right c 0]
  set G : ℝ → E := fun t => F t - ∑ n ∈ range N, t ^ ((n : ℝ) + μ - 1) • a n with hG
  have hpow : ∀ (w s : ℝ), 0 < w → 0 < s → ∀ b : E,
      IntegrableOn (fun t : ℝ => Real.exp (-w * t) • (t ^ (s - 1) • b)) (Ioi 0) := by
    intro w s hw hs b
    exact IntegrableOn.congr_fun ((integrableOn_exp_neg_mul_mul_rpow_sub_one hs hw).smul_const b)
      (fun t _ => by simp only [smul_smul]) measurableSet_Ioi
  have hsN : ∀ n : ℕ, 0 < (n : ℝ) + μ := fun n => by positivity
  have hintG : IntegrableOn (fun t => Real.exp (-c' * t) • G t) (Ioi 0) := by
    have h := (hint.exp_neg_mul_smul_of_le hcc').sub (integrable_finsetSum (range N)
      fun (n : ℕ) _ => (hpow c' ((n : ℝ) + μ) hc'0 (hsN n) (a n)))
    refine IntegrableOn.congr_fun h (fun t _ => ?_) measurableSet_Ioi
    simp only [hG, smul_sub, Finset.smul_sum, Pi.sub_apply]
  refine (isBigO_integral_exp_smul (hsN N) hintG (by simpa [hG] using hF N)).congr' ?_
    EventuallyEq.rfl
  filter_upwards [eventually_ge_atTop c'] with z hz
  have hzc : c ≤ z := hcc'.trans hz
  have hz0 : 0 < z := hc'0.trans_le hz
  simp only [hG, smul_sub, Finset.smul_sum]
  rw [integral_sub (hint.exp_neg_mul_smul_of_le hzc) (integrable_finsetSum (range N)
    fun (n : ℕ) _ => hpow z ((n : ℝ) + μ) hz0 (hsN n) (a n)), integral_finsetSum _
    fun (n : ℕ) _ => hpow z ((n : ℝ) + μ) hz0 (hsN n) (a n)]
  congr 1
  refine sum_congr rfl fun n _ => ?_
  simp_rw [smul_smul]
  rw [integral_smul_const, integral_exp_neg_mul_mul_rpow_sub_one (hsN n) hz0, mul_comm]

section Complex

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

/-- `t ↦ e^{-zt} t^{s-1}` is integrable on `(0, ∞)` for complex `s` with `re s > 0`. -/
theorem integrableOn_exp_neg_mul_smul_cpow_sub_one {s : ℂ} {z : ℝ} (hs : 0 < s.re)
    (hz : 0 < z) :
    IntegrableOn (fun t : ℝ => Real.exp (-z * t) • (t : ℂ) ^ (s - 1)) (Ioi 0) := by
  refine (integrableOn_exp_neg_mul_mul_rpow_sub_one hs hz).mono' ?_ ?_
  · exact (ContinuousOn.aestronglyMeasurable (fun t ht => by
      have : (t : ℂ) ∈ Complex.slitPlane := Complex.ofReal_mem_slitPlane.mpr ht
      exact ((by fun_prop : Continuous fun t : ℝ => Real.exp (-z * t)).continuousAt.smul
        ((Complex.continuous_ofReal.continuousAt).cpow continuousAt_const this)
        ).continuousWithinAt) measurableSet_Ioi)
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    rw [norm_smul, Real.norm_eq_abs, Real.abs_exp, Complex.norm_cpow_eq_rpow_re_of_pos ht]
    simp

/-- `∫₀^∞ e^{-zt} t^{s-1} dt = Γ(s) z^{-s}` for complex `s` with `re s > 0` and real `z > 0`. -/
theorem integral_exp_neg_mul_smul_cpow_sub_one {s : ℂ} {z : ℝ} (hs : 0 < s.re) (hz : 0 < z) :
    ∫ t in Ioi (0 : ℝ), Real.exp (-z * t) • (t : ℂ) ^ (s - 1) =
      Complex.Gamma s * (z : ℂ) ^ (-s) := by
  have h := Complex.integral_cpow_mul_exp_neg_mul_Ioi hs hz
  have hz' : (z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hz.ne'
  rw [one_div, Complex.inv_cpow _ _ (by simp [Complex.arg_ofReal_of_nonneg hz.le, Real.pi_pos.ne]),
    ← Complex.cpow_neg, mul_comm] at h
  rw [← h]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  rw [Complex.real_smul, Complex.ofReal_exp, mul_comm]
  push_cast
  ring_nf

/-- **Watson's lemma, complex exponent.** If
`F(t) - ∑_{n<N} t^{n+μ-1} aₙ = O(t^{N + re μ - 1})` as `t → 0⁺` for every `N`, with `re μ > 0`,
and `e^{-ct} F` is integrable on `(0, ∞)`, then
`∫₀^∞ e^{-zt} F(t) dt ~ ∑ Γ(n+μ) aₙ z^{-(n+μ)}` as `z → +∞`. -/
theorem hasAsymptoticExpansion_integral_exp_smul_cpow {F : ℝ → V} {a : ℕ → V} {μ : ℂ} {c : ℝ}
    (hμ : 0 < μ.re) (hint : IntegrableOn (fun t => Real.exp (-c * t) • F t) (Ioi 0))
    (hF : ∀ N : ℕ, (fun t => F t - ∑ n ∈ range N, ((t : ℂ) ^ ((n : ℂ) + μ - 1)) • a n)
      =O[𝓝[>] 0] fun t => t ^ ((N : ℝ) + μ.re - 1)) :
    HasAsymptoticExpansion atTop (fun (n : ℕ) (z : ℝ) => (z : ℂ) ^ (-((n : ℂ) + μ)))
      (fun n => Complex.Gamma ((n : ℂ) + μ) • a n)
      (fun z => ∫ t in Ioi (0 : ℝ), Real.exp (-z * t) • F t) := by
  intro N
  set c' := max c 0 + 1 with hc'
  have hcc' : c ≤ c' := by linarith [le_max_left c 0]
  have hc'0 : 0 < c' := by linarith [le_max_right c 0]
  set G : ℝ → V := fun t => F t - ∑ n ∈ range N, ((t : ℂ) ^ ((n : ℂ) + μ - 1)) • a n with hG
  have hsN : ∀ n : ℕ, 0 < ((n : ℂ) + μ).re := fun n => by simp; positivity
  have hpow : ∀ (w : ℝ) (n : ℕ), 0 < w → ∀ b : V,
      IntegrableOn (fun t : ℝ => Real.exp (-w * t) • (((t : ℂ) ^ ((n : ℂ) + μ - 1)) • b))
        (Ioi 0) := by
    intro w n hw b
    exact IntegrableOn.congr_fun
      ((integrableOn_exp_neg_mul_smul_cpow_sub_one (hsN n) hw).smul_const b)
      (fun t _ => by rw [smul_assoc]) measurableSet_Ioi
  have hintG : IntegrableOn (fun t => Real.exp (-c' * t) • G t) (Ioi 0) := by
    have h := (hint.exp_neg_mul_smul_of_le hcc').sub (integrable_finsetSum (range N)
      fun (n : ℕ) _ => (hpow c' n hc'0 (a n)))
    refine IntegrableOn.congr_fun h (fun t _ => ?_) measurableSet_Ioi
    simp only [hG, smul_sub, Finset.smul_sum, Pi.sub_apply]
  have hb := isBigO_integral_exp_smul (s := (N : ℝ) + μ.re) (by positivity) hintG
    (by simpa [hG] using hF N)
  have hnorm : (fun z : ℝ => z ^ (-((N : ℝ) + μ.re))) =O[atTop]
      fun z : ℝ => (z : ℂ) ^ (-((N : ℂ) + μ)) := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [eventually_gt_atTop 0] with z hz
    rw [one_mul, Complex.norm_cpow_eq_rpow_re_of_pos hz, Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos hz _)]
    simp
  refine (hb.trans hnorm).congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_ge_atTop c'] with z hz
  have hzc : c ≤ z := hcc'.trans hz
  have hz0 : 0 < z := hc'0.trans_le hz
  simp only [hG, smul_sub, Finset.smul_sum]
  rw [integral_sub (hint.exp_neg_mul_smul_of_le hzc) (integrable_finsetSum (range N)
    fun (n : ℕ) _ => hpow z n hz0 (a n)), integral_finsetSum _
    fun (n : ℕ) _ => hpow z n hz0 (a n)]
  congr 1
  refine sum_congr rfl fun n _ => ?_
  simp_rw [← smul_assoc]
  rw [integral_smul_const, integral_exp_neg_mul_smul_cpow_sub_one (hsN n) hz0, smul_eq_mul,
    mul_comm]

end Complex
