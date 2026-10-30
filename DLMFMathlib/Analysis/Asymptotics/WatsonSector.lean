/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.Asymptotics.Watson
public import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Watson's lemma in a sector

The Laplace transform `∫₀^∞ e^{-zt} F(t) dt` has the asymptotic expansion of Watson's lemma as
`z → ∞` in every closed sector `|arg z| ≤ π/2 - δ`, described here by `δ |z| ≤ re z`
(Temme, *Special Functions*, Theorem 2.4).

## Main results

* `integral_cpow_mul_cexp_neg_mul_Ioi`: `∫₀^∞ t^{s-1} e^{-zt} dt = Γ(s) z^{-s}` for `re s > 0`,
  `re z > 0`.
* `Asymptotics.sectorAtTop`: the filter `z → ∞` with `δ |z| ≤ re z`.
* `hasAsymptoticExpansion_integral_cexp_smul_sector`: Watson's lemma in a sector.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Finset Asymptotics Complex

open scoped Topology

/-- Helper lemma for `integral_cpow_mul_cexp_neg_mul_Ioi`: the case of a positive real scale. -/
theorem integral_cpow_mul_cexp_neg_mul_Ioi_of_real {s : ℂ} (hs : 0 < s.re) {r : ℝ} (hr : 0 < r) :
    ∫ u : ℝ in Set.Ioi 0, (u : ℂ) ^ (s - 1) * Complex.exp (-((r : ℂ) * u)) =
      Complex.Gamma s * (r : ℂ) ^ (-s) := by
  have hr0 : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr.ne'
  have hG : ∫ x : ℝ in Set.Ioi 0, (x : ℂ) ^ (s - 1) * Complex.exp (-(x : ℂ)) =
      Complex.Gamma s := by
    rw [Gamma_eq_integral hs, GammaIntegral]
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    push_cast
    ring
  have h := integral_comp_mul_left_Ioi
    (fun x : ℝ => (x : ℂ) ^ (s - 1) * Complex.exp (-(x : ℂ))) 0 hr
  rw [mul_zero, hG] at h
  have h2 : ∫ u : ℝ in Set.Ioi 0, (u : ℂ) ^ (s - 1) * Complex.exp (-((r : ℂ) * u)) =
      (r : ℂ) ^ (-(s - 1)) * ∫ x : ℝ in Set.Ioi 0,
        ((r * x : ℝ) : ℂ) ^ (s - 1) * Complex.exp (-((r * x : ℝ) : ℂ)) := by
    rw [← MeasureTheory.integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
    have hP : (r : ℂ) ^ (-(s - 1)) * (r : ℂ) ^ (s - 1) = 1 := by
      rw [cpow_neg, inv_mul_cancel₀ (cpow_ne_zero_iff.mpr (Or.inl hr0))]
    rw [ofReal_mul, mul_cpow_ofReal_nonneg hr.le (le_of_lt hu)]
    linear_combination (-((u : ℂ) ^ (s - 1) * Complex.exp (-((r : ℂ) * u)))) * hP
  rw [h2, h, Complex.real_smul, ofReal_inv, show -s = -(s - 1) + -1 by ring,
    cpow_add _ _ hr0, cpow_neg_one]
  ring

/-- The Laplace transform of a power: `∫₀^∞ u^(s-1) e^(-z u) du = Γ(s) z^(-s)` for
`Re s > 0` and `Re z > 0`. Proved for real `z` by scaling and extended to the right
half-plane by analytic continuation. -/
theorem integral_cpow_mul_cexp_neg_mul_Ioi {s z : ℂ} (hs : 0 < s.re) (hz : 0 < z.re) :
    ∫ u : ℝ in Set.Ioi 0, (u : ℂ) ^ (s - 1) * Complex.exp (-(z * u)) =
      Complex.Gamma s * z ^ (-s) := by
  set U : Set ℂ := {w | 0 < w.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const continuous_re
  let I : ℂ → ℂ := fun w => ∫ u : ℝ in Set.Ioi 0, (u : ℂ) ^ (s - 1) * Complex.exp (-(w * u))
  have hmeas (w : ℂ) : AEStronglyMeasurable
      (fun u : ℝ => (u : ℂ) ^ (s - 1) * Complex.exp (-(w * u))) (volume.restrict (Set.Ioi 0)) :=
    Measurable.aestronglyMeasurable (by fun_prop)
  have hnorm (w : ℂ) (u : ℝ) (hu : 0 < u) :
      ‖(u : ℂ) ^ (s - 1) * Complex.exp (-(w * u))‖ = u ^ (s.re - 1) * Real.exp (-w.re * u) := by
    rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hu, Complex.norm_exp]
    simp
  have hint (w : ℂ) (hw : 0 < w.re) : Integrable
      (fun u : ℝ => (u : ℂ) ^ (s - 1) * Complex.exp (-(w * u))) (volume.restrict (Set.Ioi 0)) := by
    have hb := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := s.re - 1) (b := w.re)
      (by linarith) one_pos hw
    refine Integrable.mono' hb (hmeas w) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    rw [hnorm w u hu, Real.rpow_one]
  have hdiff : DifferentiableOn ℂ I U := by
    intro w₀ hw₀
    have hw₀' : 0 < w₀.re := hw₀
    set δ := w₀.re / 2 with hδ
    have hδ0 : 0 < δ := by positivity
    have hball : Metric.ball w₀ δ ∈ 𝓝 w₀ := Metric.ball_mem_nhds _ hδ0
    have hre : ∀ w ∈ Metric.ball w₀ δ, δ < w.re := by
      intro w hw
      rw [Metric.mem_ball, dist_eq_norm] at hw
      have h1 := abs_re_le_norm (w - w₀)
      rw [sub_re] at h1
      have h2 := (abs_lt.mp (lt_of_le_of_lt h1 hw)).1
      linarith
    have hbint : Integrable (fun u : ℝ => u ^ s.re * Real.exp (-δ * u))
        (volume.restrict (Set.Ioi 0)) := by
      have := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := s.re) (b := δ)
        (by linarith) one_pos hδ0
      simp only [Real.rpow_one] at this
      exact this
    have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume.restrict (Set.Ioi 0))
      (F := fun w (u : ℝ) => (u : ℂ) ^ (s - 1) * Complex.exp (-(w * u)))
      (F' := fun w (u : ℝ) => (u : ℂ) ^ (s - 1) * (Complex.exp (-(w * u)) * -(u : ℂ)))
      (bound := fun u : ℝ => u ^ s.re * Real.exp (-δ * u))
      hball (Eventually.of_forall hmeas) (hint w₀ hw₀')
      (Measurable.aestronglyMeasurable (by fun_prop)) ?_ hbint ?_
    · exact h.2.differentiableAt.differentiableWithinAt
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu w hw
      have hu' : 0 < u := hu
      have hwre := hre w hw
      rw [norm_mul, norm_mul, norm_neg, norm_cpow_eq_rpow_re_of_pos hu', Complex.norm_exp,
        Complex.norm_real, Real.norm_of_nonneg hu'.le]
      have e : u ^ (s - 1).re * u = u ^ s.re := by
        rw [sub_re, one_re, Real.rpow_sub_one hu'.ne']
        field_simp
      have hexp : Real.exp (-(w * u)).re ≤ Real.exp (-δ * u) := by
        apply Real.exp_le_exp.mpr
        simp only [neg_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
        nlinarith
      calc u ^ (s - 1).re * (Real.exp (-(w * u)).re * u)
          = u ^ s.re * Real.exp (-(w * u)).re := by rw [← e]; ring
        _ ≤ u ^ s.re * Real.exp (-δ * u) := by gcongr
    · filter_upwards with u w _
      have := ((hasDerivAt_id w).mul_const (u : ℂ)).neg.cexp.const_mul ((u : ℂ) ^ (s - 1))
      simpa using this
  have hanI : AnalyticOnNhd ℂ I U := hdiff.analyticOnNhd hUo
  have hanR : AnalyticOnNhd ℂ (fun w => Complex.Gamma s * w ^ (-s)) U := by
    refine DifferentiableOn.analyticOnNhd (fun w hw => ?_) hUo
    have hslit : w ∈ slitPlane := mem_slitPlane_iff.mpr (Or.inl hw)
    exact ((differentiableAt_id.cpow (differentiableAt_const _) hslit).const_mul
      _).differentiableWithinAt
  have hfreq : ∃ᶠ w in 𝓝[≠] (1 : ℂ), I w = Complex.Gamma s * w ^ (-s) := by
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
    exact integral_cpow_mul_cexp_neg_mul_Ioi_of_real hs hr
  exact hanI.eqOn_of_preconnected_of_frequently_eq hanR (convex_halfSpace_re_gt 0).isPreconnected
    (by simp [hU]) hfreq hz

namespace Asymptotics

/-- The filter `z → ∞` within the closed sector `δ |z| ≤ re z`, that is `|arg z| ≤ arccos δ`. -/
def sectorAtTop (δ : ℝ) : Filter ℂ :=
  comap (fun z : ℂ => ‖z‖) atTop ⊓ 𝓟 {z : ℂ | δ * ‖z‖ ≤ z.re}

/-- The stated relation follows from the given hypotheses: `∀ᶠ z in sectorAtTop δ, p z`. -/
theorem eventually_sectorAtTop {δ : ℝ} {p : ℂ → Prop} {R : ℝ}
    (h : ∀ z : ℂ, R ≤ ‖z‖ → δ * ‖z‖ ≤ z.re → p z) : ∀ᶠ z in sectorAtTop δ, p z := by
  rw [sectorAtTop, eventually_inf_principal]
  exact (tendsto_comap.eventually (eventually_ge_atTop R)).mono fun z hz hzs => h z hz hzs

/-- The map `(fun z : ℂ => ‖z‖)` tends to `atTop` along `(sectorAtTop δ)`. -/
theorem tendsto_norm_sectorAtTop (δ : ℝ) : Tendsto (fun z : ℂ => ‖z‖) (sectorAtTop δ) atTop :=
  tendsto_comap.mono_left inf_le_left

end Asymptotics

section Sector

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

omit [CompleteSpace V] in
/-- Integrability of `e^{-zt} G` for `re z ≥ c`, given that of `e^{-ct} G`. -/
theorem integrableOn_cexp_neg_mul_smul_of_le {G : ℝ → V} {c : ℝ} {z : ℂ}
    (hint : IntegrableOn (fun t => Real.exp (-c * t) • G t) (Ioi 0)) (hz : c ≤ z.re) :
    IntegrableOn (fun t : ℝ => Complex.exp (-(z * t)) • G t) (Ioi 0) := by
  have hGm : AEStronglyMeasurable G (volume.restrict (Ioi 0)) := by
    have hc : AEStronglyMeasurable (fun t : ℝ => Real.exp (c * t)) (volume.restrict (Ioi 0)) :=
      (by fun_prop : Continuous fun t : ℝ => Real.exp (c * t)).aestronglyMeasurable
    refine (hc.smul hint.aestronglyMeasurable).congr (Eventually.of_forall fun t => ?_)
    show Real.exp (c * t) • (Real.exp (-c * t) • G t) = G t
    rw [smul_smul, ← Real.exp_add]
    simp
  refine hint.norm.mono' (((by fun_prop : Continuous fun t : ℝ => Complex.exp (-(z * t))
    ).aestronglyMeasurable).smul hGm) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
  have ht : (0 : ℝ) < t := ht
  rw [norm_smul, norm_smul, Complex.norm_exp, Real.norm_eq_abs, Real.abs_exp]
  refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
  simp only [neg_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
  nlinarith

/-- **Watson remainder bound in a sector.** If `G(t) = O(t^{s-1})` as `t → 0⁺` with `s > 0` and
`e^{-ct} G` is integrable on `(0, ∞)`, then `∫₀^∞ e^{-zt} G(t) dt = O(|z|^{-s})` as `z → ∞` in the
sector `δ |z| ≤ re z`. -/
theorem isBigO_integral_cexp_smul_sector {G : ℝ → V} {s c δ : ℝ} (hs : 0 < s) (hδ : 0 < δ)
    (hint : IntegrableOn (fun t => Real.exp (-c * t) • G t) (Ioi 0))
    (hG : G =O[𝓝[>] 0] fun t => t ^ (s - 1)) :
    (fun z : ℂ => ∫ t in Ioi (0 : ℝ), Complex.exp (-(z * t)) • G t) =O[sectorAtTop δ]
      fun z => ‖z‖ ^ (-s) := by
  set c' := max c 0 with hc'
  have hc'0 : 0 ≤ c' := le_max_right _ _
  -- the bound near `0`
  obtain ⟨K, hK, hKw⟩ := hG.exists_pos
  obtain ⟨ε, hε, hεb⟩ := Metric.eventually_nhds_iff.mp
    (eventually_nhdsWithin_iff.mp hKw.bound)
  set d := ε / 2 with hd
  have hd0 : 0 < d := by positivity
  have hGb : ∀ t ∈ Ioc (0 : ℝ) d, ‖G t‖ ≤ K * t ^ (s - 1) := by
    intro t ht
    have h := hεb (y := t) (by rw [Real.dist_eq, sub_zero, abs_of_pos ht.1]; linarith [ht.2])
      ht.1
    rwa [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos ht.1 _)] at h
  -- the tail constant
  have hcint := hint.exp_neg_mul_smul_of_le (w := c' + 1) (by linarith [le_max_left c 0])
  set A := ∫ t in Ioi (0 : ℝ), Real.exp (-(c' + 1) * t) * ‖G t‖ with hA
  have hAint : IntegrableOn (fun t => Real.exp (-(c' + 1) * t) * ‖G t‖) (Ioi 0) :=
    IntegrableOn.congr_fun hcint.norm (fun t _ => by simp [norm_smul, Real.abs_exp])
      measurableSet_Ioi
  have hA0 : 0 ≤ A := setIntegral_nonneg measurableSet_Ioi fun t _ => by positivity
  -- the exponential is smaller than any power
  have hexp : ∀ᶠ r in atTop, Real.exp (-(d * δ) * r) ≤ r ^ (-s) := by
    have h := (isLittleO_rpow_exp_pos_mul_atTop s (by positivity : 0 < d * δ)).bound one_pos
    filter_upwards [h, eventually_gt_atTop 0] with r hr hr0
    rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hr0 _),
      Real.abs_exp] at hr
    rw [Real.rpow_neg hr0.le, neg_mul, Real.exp_neg]
    exact inv_anti₀ (Real.rpow_pos_of_pos hr0 _) hr
  obtain ⟨R₀, hR₀⟩ := eventually_atTop.mp hexp
  refine IsBigO.of_bound (K * Real.Gamma s * δ ^ (-s) + A * Real.exp ((c' + 1) * d)) ?_
  refine eventually_sectorAtTop (R := max (max R₀ 1) ((c' + 1) / δ)) fun z hzR hzs => ?_
  have hR1 : 1 ≤ ‖z‖ := (le_max_right _ _).trans ((le_max_left _ _).trans hzR)
  have hzpos : 0 < ‖z‖ := by linarith
  have hre : c' + 1 ≤ z.re := by
    have h1 : (c' + 1) / δ ≤ ‖z‖ := (le_max_right _ _).trans hzR
    rw [div_le_iff₀ hδ] at h1
    linarith
  have hrepos : 0 < z.re := by linarith
  have hzc : c ≤ z.re := by linarith [le_max_left c 0]
  have hI := integrableOn_cexp_neg_mul_smul_of_le hint hzc
  rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hzpos _)]
  rw [← Ioc_union_Ioi_eq_Ioi hd0.le, setIntegral_union (Ioc_disjoint_Ioi le_rfl)
    measurableSet_Ioi (hI.mono_set Ioc_subset_Ioi_self) (hI.mono_set (Ioi_subset_Ioi hd0.le))]
  refine (norm_add_le _ _).trans ?_
  have hnormexp : ∀ t : ℝ, ‖Complex.exp (-(z * t))‖ = Real.exp (-z.re * t) := fun t => by
    rw [Complex.norm_exp]; simp
  have h1 : ‖∫ t in Ioc (0 : ℝ) d, Complex.exp (-(z * t)) • G t‖ ≤
      K * Real.Gamma s * δ ^ (-s) * ‖z‖ ^ (-s) := by
    refine (norm_integral_le_integral_norm _).trans ?_
    have hmono : ∫ t in Ioc (0 : ℝ) d, ‖Complex.exp (-(z * t)) • G t‖ ≤
        ∫ t in Ioc (0 : ℝ) d, K * (Real.exp (-z.re * t) * t ^ (s - 1)) := by
      refine setIntegral_mono_on (hI.mono_set Ioc_subset_Ioi_self).norm
        (((integrableOn_exp_neg_mul_mul_rpow_sub_one hs hrepos).mono_set
          Ioc_subset_Ioi_self).const_mul K) measurableSet_Ioc fun t ht => ?_
      rw [norm_smul, hnormexp]
      have := hGb t ht
      have he := Real.exp_pos (-z.re * t)
      nlinarith
    refine hmono.trans ?_
    rw [MeasureTheory.integral_const_mul]
    have hle : ∫ t in Ioc (0 : ℝ) d, Real.exp (-z.re * t) * t ^ (s - 1) ≤
        Real.Gamma s * z.re ^ (-s) := by
      rw [← integral_exp_neg_mul_mul_rpow_sub_one hs hrepos]
      refine setIntegral_mono_set (integrableOn_exp_neg_mul_mul_rpow_sub_one hs hrepos)
        ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_))
        (Eventually.of_forall Ioc_subset_Ioi_self)
      exact mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (le_of_lt ht) _)
    have hpow : z.re ^ (-s) ≤ δ ^ (-s) * ‖z‖ ^ (-s) := by
      rw [← Real.mul_rpow hδ.le hzpos.le]
      exact Real.rpow_le_rpow_of_nonpos (by positivity) hzs (by linarith)
    have hΓ := Real.Gamma_pos_of_pos hs
    calc K * ∫ t in Ioc (0 : ℝ) d, Real.exp (-z.re * t) * t ^ (s - 1)
        ≤ K * (Real.Gamma s * (δ ^ (-s) * ‖z‖ ^ (-s))) := by
          gcongr; exact hle.trans (by gcongr)
      _ = _ := by ring
  have h2 : ‖∫ t in Ioi d, Complex.exp (-(z * t)) • G t‖ ≤
      A * Real.exp ((c' + 1) * d) * ‖z‖ ^ (-s) := by
    refine (norm_integral_le_integral_norm _).trans ?_
    have hmono : ∫ t in Ioi d, ‖Complex.exp (-(z * t)) • G t‖ ≤
        ∫ t in Ioi d, Real.exp (-(z.re - c' - 1) * d) * (Real.exp (-(c' + 1) * t) * ‖G t‖) := by
      refine setIntegral_mono_on (hI.mono_set (Ioi_subset_Ioi hd0.le)).norm
        ((hAint.mono_set (Ioi_subset_Ioi hd0.le)).const_mul _) measurableSet_Ioi
        fun t ht => ?_
      have ht' : d < t := ht
      rw [norm_smul, hnormexp, ← mul_assoc, ← Real.exp_add]
      refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
      nlinarith
    refine hmono.trans ?_
    rw [MeasureTheory.integral_const_mul]
    have hAle : ∫ t in Ioi d, Real.exp (-(c' + 1) * t) * ‖G t‖ ≤ A :=
      setIntegral_mono_set hAint
        ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t _ => by positivity))
        (Eventually.of_forall (Ioi_subset_Ioi hd0.le))
    have hsplit : Real.exp (-(z.re - c' - 1) * d) =
        Real.exp ((c' + 1) * d) * Real.exp (-d * z.re) := by
      rw [← Real.exp_add]; ring_nf
    have hdec : Real.exp (-d * z.re) ≤ ‖z‖ ^ (-s) := by
      have h3 : Real.exp (-d * z.re) ≤ Real.exp (-(d * δ) * ‖z‖) :=
        Real.exp_le_exp.mpr (by nlinarith)
      exact h3.trans (hR₀ ‖z‖ ((le_max_left _ _).trans ((le_max_left _ _).trans hzR)))
    rw [hsplit]
    calc Real.exp ((c' + 1) * d) * Real.exp (-d * z.re) *
          ∫ t in Ioi d, Real.exp (-(c' + 1) * t) * ‖G t‖
        ≤ Real.exp ((c' + 1) * d) * ‖z‖ ^ (-s) * A := by gcongr
      _ = A * Real.exp ((c' + 1) * d) * ‖z‖ ^ (-s) := by ring
  calc ‖∫ t in Ioc (0 : ℝ) d, Complex.exp (-(z * t)) • G t‖ +
        ‖∫ t in Ioi d, Complex.exp (-(z * t)) • G t‖
      ≤ K * Real.Gamma s * δ ^ (-s) * ‖z‖ ^ (-s) + A * Real.exp ((c' + 1) * d) * ‖z‖ ^ (-s) :=
        add_le_add h1 h2
    _ = _ := by ring

/-- `|z|^{-re s} = O(z^{-s})` as `z → ∞` in a sector, since `|arg z| ≤ π`. -/
theorem isBigO_norm_rpow_cpow_neg_sector (δ : ℝ) (s : ℂ) :
    (fun z : ℂ => ‖z‖ ^ (-s.re)) =O[sectorAtTop δ] fun z => z ^ (-s) := by
  refine IsBigO.of_bound (Real.exp (Real.pi * |s.im|)) ?_
  refine eventually_sectorAtTop (R := 1) fun z hz _ => ?_
  have hz0 : z ≠ 0 := by intro h; rw [h, norm_zero] at hz; linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _),
    Complex.norm_cpow_of_ne_zero hz0, neg_re, neg_im, mul_div_assoc', le_div_iff₀ (Real.exp_pos _),
    mul_comm (Real.exp _)]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (Real.rpow_nonneg (norm_nonneg _) _)
  have h1 := Complex.abs_arg_le_pi z
  have h2 : |arg z * -s.im| ≤ Real.pi * |s.im| := by
    rw [abs_mul, abs_neg]; exact mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
  linarith [le_abs_self (arg z * -s.im)]

/-- **Watson's lemma in a sector** (Temme, Theorem 2.4): if
`F(t) - ∑_{n<N} t^{n+μ-1} aₙ = O(t^{N + re μ - 1})` as `t → 0⁺` for every `N`, with `re μ > 0`,
and `e^{-ct} F` is integrable on `(0, ∞)`, then
`∫₀^∞ e^{-zt} F(t) dt ~ ∑ Γ(n+μ) aₙ z^{-(n+μ)}` as `z → ∞` with `δ |z| ≤ re z`, `δ > 0`. -/
theorem hasAsymptoticExpansion_integral_cexp_smul_sector {F : ℝ → V} {a : ℕ → V} {μ : ℂ}
    {c δ : ℝ} (hμ : 0 < μ.re) (hδ : 0 < δ)
    (hint : IntegrableOn (fun t => Real.exp (-c * t) • F t) (Ioi 0))
    (hF : ∀ N : ℕ, (fun t => F t - ∑ n ∈ range N, ((t : ℂ) ^ ((n : ℂ) + μ - 1)) • a n)
      =O[𝓝[>] 0] fun t => t ^ ((N : ℝ) + μ.re - 1)) :
    HasAsymptoticExpansion (sectorAtTop δ) (fun (n : ℕ) (z : ℂ) => z ^ (-((n : ℂ) + μ)))
      (fun n => Complex.Gamma ((n : ℂ) + μ) • a n)
      (fun z => ∫ t in Ioi (0 : ℝ), Complex.exp (-(z * t)) • F t) := by
  intro N
  set c' := max c 0 + 1 with hc'
  have hcc' : c ≤ c' := by linarith [le_max_left c 0]
  have hc'0 : 0 < c' := by linarith [le_max_right c 0]
  set G : ℝ → V := fun t => F t - ∑ n ∈ range N, ((t : ℂ) ^ ((n : ℂ) + μ - 1)) • a n with hG
  have hsN : ∀ n : ℕ, 0 < ((n : ℂ) + μ).re := fun n => by simp; positivity
  have hpowr : ∀ (n : ℕ) (b : V), IntegrableOn (fun t : ℝ => Real.exp (-c' * t) •
      (((t : ℂ) ^ ((n : ℂ) + μ - 1)) • b)) (Ioi 0) := fun n b =>
    IntegrableOn.congr_fun ((integrableOn_exp_neg_mul_smul_cpow_sub_one (hsN n) hc'0).smul_const b)
      (fun t _ => by rw [smul_assoc]) measurableSet_Ioi
  have hpowz : ∀ (n : ℕ) (b : V) (z : ℂ), c' ≤ z.re → IntegrableOn (fun t : ℝ =>
      Complex.exp (-(z * t)) • (((t : ℂ) ^ ((n : ℂ) + μ - 1)) • b)) (Ioi 0) :=
    fun n b z hz => integrableOn_cexp_neg_mul_smul_of_le (hpowr n b) hz
  have hintG : IntegrableOn (fun t => Real.exp (-c' * t) • G t) (Ioi 0) := by
    have h := (hint.exp_neg_mul_smul_of_le hcc').sub (integrable_finsetSum (range N)
      fun (n : ℕ) _ => hpowr n (a n))
    refine IntegrableOn.congr_fun h (fun t _ => ?_) measurableSet_Ioi
    simp only [hG, smul_sub, Finset.smul_sum, Pi.sub_apply]
  have hb := isBigO_integral_cexp_smul_sector (s := (N : ℝ) + μ.re) (by positivity) hδ hintG
    (by simpa [hG] using hF N)
  have hnorm := isBigO_norm_rpow_cpow_neg_sector δ ((N : ℂ) + μ)
  simp only [add_re, natCast_re] at hnorm
  refine (hb.trans hnorm).congr' ?_ EventuallyEq.rfl
  refine eventually_sectorAtTop (R := c' / δ) fun z hzR hzs => ?_
  have hzc' : c' ≤ z.re := by rw [div_le_iff₀ hδ] at hzR; linarith
  have hzc : c ≤ z.re := hcc'.trans hzc'
  have hz0 : 0 < z.re := hc'0.trans_le hzc'
  simp only [hG, smul_sub, Finset.smul_sum]
  rw [integral_sub (integrableOn_cexp_neg_mul_smul_of_le hint hzc)
    (integrable_finsetSum (range N) fun (n : ℕ) _ => hpowz n (a n) z hzc'),
    integral_finsetSum _ fun (n : ℕ) _ => hpowz n (a n) z hzc']
  congr 1
  refine sum_congr rfl fun n _ => ?_
  simp_rw [← smul_assoc]
  rw [integral_smul_const]
  congr 1
  rw [smul_eq_mul, mul_comm, ← integral_cpow_mul_cexp_neg_mul_Ioi (hsN n) hz0]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  rw [smul_eq_mul, mul_comm]

end Sector
