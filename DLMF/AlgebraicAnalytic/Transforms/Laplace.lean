/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AlgebraicAnalytic.Transforms.Basic
public import DLMFMathlib.Analysis.Complex.ParametricHolomorphy
public import DLMFMathlib.Analysis.Integral.LaplaceRay
public import DLMFMathlib.Analysis.SpecialFunctions.ImproperIntegralsExtra
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Convolution
public import Mathlib.Analysis.MellinTransform
public import Mathlib.MeasureTheory.Integral.ExpDecay
public import Mathlib.Topology.EMetricSpace.BoundedVariation

/-!
# The Laplace transform (DLMF §1.14(iii))

Statements of DLMF §1.14(iii) for `laplaceTransform f s = ∫₀^∞ e^{-st} f(t) dt` (1.14.17).

DLMF assumes throughout that `f` is piecewise continuous on `[0, ∞)` and of exponential growth
(1.14.18) with exponent `α`, and `ℜs > α`. Here "piecewise continuous" is replaced by the weaker
`LocallyIntegrableOn f (Ici 0)` wherever that suffices (stronger than DLMF), and the exponential
growth is the predicate `IsOfExponentialGrowth f α`.

Proved: absolute convergence, analyticity and decay for `ℜs > α` (§1.14(iii), 1.14.19),
the translation rules 1.14.21–1.14.22, and differentiation of every order (1.14.23).
Analyticity uses the project’s dominated-holomorphy theorem, and differentiation uses Mathlib’s
`hasDerivAt_integral_of_dominated_loc_of_deriv_le`. Admitted: inversion 1.14.20, integration
1.14.24, derivatives with jumps 1.14.28, and uniqueness. The convolution theorem 1.14.31
is proved from Mathlib’s `MeasureTheory.integral_convolution` by extension by zero.
The periodic and antiperiodic rules 1.14.25–1.14.26 and the derivative rules 1.14.27 and
1.14.29 are proved by splitting the half-line integral and by Mathlib’s improper-integral
fundamental theorem `integral_Ioi_of_hasDerivAt_of_tendsto`.
-/

@[expose] public noncomputable section

open MeasureTheory Complex Set Filter Topology Asymptotics

namespace DLMF.AlgebraicAnalytic

/-- DLMF §1.14(iii) (convergence): if `f` is locally integrable on `[0, ∞)` and of exponential
growth `α` (1.14.18), then `e^{-st} f(t)` is integrable on `(0, ∞)` for `ℜs > α`. -/
@[dlmf 1.14.iii]
theorem integrableOn_laplace_integrand {f : ℝ → ℂ} {α : ℝ} (hf : LocallyIntegrableOn f (Ici 0))
    (hg : IsOfExponentialGrowth f α) {s : ℂ} (hs : α < s.re) :
    IntegrableOn (fun t : ℝ => cexp (-s * t) * f t) (Ioi 0) := by
  obtain ⟨M, hM⟩ := hg
  have hmeas : AEStronglyMeasurable f (volume.restrict (Ioi 0)) :=
    (hf.aestronglyMeasurable).mono_set Ioi_subset_Ici_self
  have hb : IntegrableOn (fun t : ℝ => M * Real.exp (-(s.re - α) * t)) (Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 (by linarith)).const_mul M
  refine hb.mono' ((by fun_prop : Continuous fun t : ℝ => cexp (-s * t)).aestronglyMeasurable.mul
    hmeas) ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_))
  have ht0 : (0 : ℝ) ≤ t := le_of_lt ht
  rw [norm_mul, Complex.norm_exp]
  have hre : (-s * (t : ℂ)).re = -s.re * t := by simp
  rw [hre]
  calc Real.exp (-s.re * t) * ‖f t‖ ≤ Real.exp (-s.re * t) * (M * Real.exp (α * t)) :=
        mul_le_mul_of_nonneg_left (hM t ht0) (Real.exp_pos _).le
    _ = M * Real.exp (-(s.re - α) * t) := by
        rw [mul_left_comm, ← Real.exp_add]; congr 2; ring

/-- DLMF §1.14(iii) (analyticity): under 1.14.18, `𝓛(f)(s)` is analytic in `ℜs > α`. -/
@[dlmf 1.14.iii]
theorem differentiableOn_laplaceTransform {f : ℝ → ℂ} {α : ℝ}
    (hf : LocallyIntegrableOn f (Ici 0)) (hg : IsOfExponentialGrowth f α) :
    DifferentiableOn ℂ (laplaceTransform f) {s : ℂ | α < s.re} := by
  obtain ⟨M, hM⟩ := hg
  have hU : IsOpen {s : ℂ | α < s.re} := isOpen_lt continuous_const Complex.continuous_re
  refine Complex.differentiableOn_integral_Ioi_of_locally_dominated hU 0
    (fun s hs => (integrableOn_laplace_integrand hf ⟨M, hM⟩ hs).aestronglyMeasurable)
    (Eventually.of_forall fun t => by fun_prop) ?_
  intro s hs
  change α < s.re at hs
  let β := (s.re + α) / 2
  have hβ : α < β := by dsimp [β]; linarith
  have hsβ : β < s.re := by dsimp [β]; linarith
  refine ⟨{z : ℂ | β < z.re}, (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hsβ,
    fun t => M * Real.exp (-(β - α) * t),
    (exp_neg_integrableOn_Ioi 0 (by linarith)).const_mul M, ?_⟩
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht z hz
  rw [norm_mul, Complex.norm_exp]
  have hre : (-z * (t : ℂ)).re = -z.re * t := by simp
  rw [hre]
  calc Real.exp (-z.re * t) * ‖f t‖ ≤ Real.exp (-β * t) * ‖f t‖ := by
        gcongr
        exact ht.le
    _ ≤ Real.exp (-β * t) * (M * Real.exp (α * t)) :=
        mul_le_mul_of_nonneg_left (hM t ht.le) (Real.exp_pos _).le
    _ = M * Real.exp (-(β - α) * t) := by
        rw [mul_left_comm, ← Real.exp_add]; congr 2; ring

/-- A global exponential majorant gives a quantitative bound for the Laplace transform. -/
theorem norm_laplaceTransform_le {f : ℝ → ℂ} {α M : ℝ}
    (hM : ∀ t, 0 ≤ t → ‖f t‖ ≤ M * Real.exp (α * t)) {s : ℂ} (hs : α < s.re) :
    ‖laplaceTransform f s‖ ≤ M / (s.re - α) := by
  have hi : IntegrableOn (fun t : ℝ => M * Real.exp (-(s.re - α) * t)) (Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 (by linarith)).const_mul M
  have hb : ∀ᵐ (t : ℝ) ∂(volume.restrict (Ioi (0 : ℝ))),
      ‖cexp (-s * t) * f t‖ ≤ M * Real.exp (-(s.re - α) * t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [norm_mul, Complex.norm_exp]
    have hre : (-s * (t : ℂ)).re = -s.re * t := by simp
    rw [hre]
    calc Real.exp (-s.re * t) * ‖f t‖ ≤
          Real.exp (-s.re * t) * (M * Real.exp (α * t)) :=
            mul_le_mul_of_nonneg_left (hM t ht.le) (Real.exp_pos _).le
      _ = M * Real.exp (-(s.re - α) * t) := by
          rw [mul_left_comm, ← Real.exp_add]; congr 2; ring
  have he : (∫ t : ℝ in Ioi 0, M * Real.exp (-(s.re - α) * t)) = M / (s.re - α) := by
    rw [integral_const_mul, integral_exp_mul_Ioi (by linarith : -(s.re - α) < 0) 0]
    simp only [mul_zero, Real.exp_zero, div_neg]
    ring
  exact he ▸ norm_integral_le_of_norm_le hi hb

/-- DLMF 1.14.19: under 1.14.18, `𝓛(f)(s) → 0` as `ℜs → ∞`, uniformly in `ℑs`. -/
@[dlmf 1.14.E19]
theorem tendsto_laplaceTransform_re_atTop {f : ℝ → ℂ} {α : ℝ}
    (hg : IsOfExponentialGrowth f α) :
    Tendsto (laplaceTransform f) (comap Complex.re atTop) (𝓝 0) := by
  obtain ⟨M, hM⟩ := hg
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hre : Tendsto Complex.re (comap Complex.re atTop) atTop := tendsto_comap
  have hlim : Tendsto (fun s : ℂ => M / (s.re - α)) (comap Complex.re atTop) (𝓝 0) :=
    tendsto_const_nhds.div_atTop (by
      simpa only [sub_eq_add_neg] using tendsto_atTop_add_const_right _ (-α) hre)
  refine squeeze_zero' (Eventually.of_forall fun s => norm_nonneg _) ?_ hlim
  filter_upwards [hre.eventually_gt_atTop α] with s hs
  exact norm_laplaceTransform_le hM hs

/-- DLMF 1.14.20 (Bromwich inversion): if `f` is continuous on `[0, ∞)`, of exponential growth
`α`, and of locally bounded variation (as when `f'` is piecewise continuous), then for `t > 0`
and `σ > α`,
`f(t) = (1/2πi) lim_{T→∞} ∫_{σ-iT}^{σ+iT} e^{ts} 𝓛(f)(s) ds`, the path parametrized by
`s = σ + iy` (`ds = i dy`). -/
@[dlmf 1.14.E20]
theorem tendsto_laplaceTransform_inversion {f : ℝ → ℂ} {α : ℝ} (hf : ContinuousOn f (Ici 0))
    (hbv : LocallyBoundedVariationOn f (Ici 0)) (hg : IsOfExponentialGrowth f α) {σ : ℝ}
    (hσ : α < σ) {t : ℝ} (ht : 0 < t) :
    Tendsto (fun T : ℝ => (1 / (2 * Real.pi) : ℂ) *
        ∫ y in -T..T, cexp (t * (σ + y * I)) * laplaceTransform f (σ + y * I)) atTop
      (𝓝 (f t)) := by
  sorry

/-- DLMF §1.14(iii), after 1.14.20: if moreover `𝓛(f)(s) = O(s^{-K})` with `K > 1` in a
half-plane `ℜs ≥ γ` (here `γ > α`), then for every `σ > γ` and `t > 0` the inversion integral
converges absolutely and `f(t) = (1/2π) ∫ e^{t(σ+iy)} 𝓛(f)(σ + iy) dy`; continuity of `f`
suffices. -/
@[dlmf 1.14.E20]
theorem laplaceTransform_inversion_of_isBigO {f : ℝ → ℂ} {α γ K C : ℝ}
    (hf : ContinuousOn f (Ici 0)) (hg : IsOfExponentialGrowth f α) (hγ : α < γ) (hK : 1 < K)
    (hbound : ∀ s : ℂ, γ ≤ s.re → ‖laplaceTransform f s‖ ≤ C * ‖s‖ ^ (-K)) {σ : ℝ}
    (hσ : γ < σ) {t : ℝ} (ht : 0 < t) :
    f t = (1 / (2 * Real.pi) : ℂ) *
      ∫ y : ℝ, cexp (t * (σ + y * I)) * laplaceTransform f (σ + y * I) := by
  sorry

/-- DLMF 1.14.21 (translation): `𝓛(f)(s - a) = 𝓛(f_a)(s)` with `f_a(t) = e^{at} f(t)`. This holds
identically (also when the integrals diverge, both sides being `0`). -/
@[dlmf 1.14.E21]
theorem laplaceTransform_sub (f : ℝ → ℂ) (s a : ℂ) :
    laplaceTransform f (s - a) = laplaceTransform (fun t => cexp (a * t) * f t) s := by
  unfold laplaceTransform
  congr 1
  funext t
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  ring

/-- DLMF 1.14.22 (translation): for `a ≥ 0`, `𝓛(f_a⁺)(s) = e^{-as} 𝓛(f)(s)` with
`f_a⁺(t) = H(t - a) f(t - a)` (`H` the Heaviside function; its value at `0` is irrelevant). -/
@[dlmf 1.14.E22]
theorem laplaceTransform_heaviside_shift (f : ℝ → ℂ) {a : ℝ} (ha : 0 ≤ a) (s : ℂ) :
    laplaceTransform (fun t => (Ioi a).indicator (fun t => f (t - a)) t) s =
      cexp (-a * s) * laplaceTransform f s := by
  unfold laplaceTransform
  have h1 : (∫ t in Ioi (0 : ℝ), cexp (-s * t) * (Ioi a).indicator (fun t => f (t - a)) t) =
      ∫ t : ℝ, (Ioi a).indicator (fun t => cexp (-s * t) * f (t - a)) t := by
    rw [← integral_indicator measurableSet_Ioi]
    congr 1
    funext t
    by_cases hta : a < t
    · have ht0 : 0 < t := lt_of_le_of_lt ha hta
      simp [indicator_of_mem, hta, ht0]
    · simp [indicator_of_notMem, hta]
  have h2 : (∫ t : ℝ, (Ioi a).indicator (fun t => cexp (-s * t) * f (t - a)) t) =
      ∫ u : ℝ, (Ioi (0 : ℝ)).indicator (fun u : ℝ => cexp (-s * ((u : ℂ) + a)) * f u) u := by
    rw [← integral_add_right_eq_self (fun t => (Ioi a).indicator
      (fun t => cexp (-s * t) * f (t - a)) t) a]
    congr 1
    funext u
    by_cases hu : 0 < u
    · have : a < u + a := by linarith
      simp [indicator_of_mem, hu, this]
    · have : ¬ a < u + a := by linarith
      simp [indicator_of_notMem, hu, this]
  rw [h1, h2, integral_indicator measurableSet_Ioi, ← integral_const_mul]
  congr 1
  funext u
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  ring

/-- Bound a polynomially weighted Laplace integrand by a real exponential moment. -/
private lemma norm_laplace_moment_le {f : ℝ → ℂ} {α M β : ℝ}
    (hM : ∀ t, 0 ≤ t → ‖f t‖ ≤ M * Real.exp (α * t)) (n : ℕ)
    {t : ℝ} (ht : 0 ≤ t) {s : ℂ} (hs : β ≤ s.re) :
    ‖cexp (-s * t) * ((t : ℂ) ^ n * f t)‖ ≤
      M * (t ^ n * Real.exp (-((β - α) * t))) := by
  rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg ht, Complex.norm_exp]
  have hre : (-s * (t : ℂ)).re = -s.re * t := by simp
  rw [hre]
  calc Real.exp (-s.re * t) * (t ^ n * ‖f t‖) ≤
        Real.exp (-β * t) * (t ^ n * (M * Real.exp (α * t))) := by
          gcongr
          exact hM t ht
    _ = M * (t ^ n * Real.exp (-((β - α) * t))) := by
        rw [show -((β - α) * t) = -β * t + α * t by ring, Real.exp_add]
        ring

/-- Every polynomial moment of the Laplace integrand is integrable inside the half-plane. -/
private lemma integrableOn_laplace_moment {f : ℝ → ℂ} {α M : ℝ}
    (hf : AEStronglyMeasurable f (volume.restrict (Ioi 0)))
    (hM : ∀ t, 0 ≤ t → ‖f t‖ ≤ M * Real.exp (α * t)) (n : ℕ) {s : ℂ} (hs : α < s.re) :
    IntegrableOn (fun t : ℝ => cexp (-s * t) * ((t : ℂ) ^ n * f t)) (Ioi 0) := by
  have hi : IntegrableOn (fun t : ℝ => M * (t ^ n * Real.exp (-((s.re - α) * t)))) (Ioi 0) := by
    simpa only [Real.rpow_natCast] using!
      (integrableOn_rpow_mul_exp_neg_mul (r := n)
        (by have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n; linarith) (sub_pos.mpr hs)).const_mul M
  refine hi.mono' ((by fun_prop : Continuous fun t : ℝ => cexp (-s * t)).aestronglyMeasurable.mul
    ((by fun_prop : Continuous fun t : ℝ => (t : ℂ) ^ n).aestronglyMeasurable.mul hf)) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact norm_laplace_moment_le hM n ht.le le_rfl

/-- Differentiating a Laplace moment inserts one additional factor `-t` in the integrand. -/
theorem hasDerivAt_laplaceTransform_moment {f : ℝ → ℂ} {α : ℝ}
    (hf : LocallyIntegrableOn f (Ici 0)) (hg : IsOfExponentialGrowth f α)
    (n : ℕ) {s : ℂ} (hs : α < s.re) :
    HasDerivAt (laplaceTransform (fun t => (t : ℂ) ^ n * f t))
      (-laplaceTransform (fun t => (t : ℂ) ^ (n + 1) * f t) s) s := by
  obtain ⟨M, hM⟩ := hg
  have hfm := hf.aestronglyMeasurable.mono_set Ioi_subset_Ici_self
  let β := (s.re + α) / 2
  have hβ : α < β := by dsimp [β]; linarith
  have hsβ : β < s.re := by dsimp [β]; linarith
  have hV : {z : ℂ | β < z.re} ∈ 𝓝 s :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hsβ
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun z t => cexp (-z * t) * ((t : ℂ) ^ n * f t))
    (F' := fun z t => -(cexp (-z * t) * ((t : ℂ) ^ (n + 1) * f t))) hV
    (Eventually.of_forall fun z =>
      (by fun_prop : Continuous fun t : ℝ => cexp (-z * t)).aestronglyMeasurable.mul
        ((by fun_prop : Continuous fun t : ℝ => (t : ℂ) ^ n).aestronglyMeasurable.mul hfm))
    (integrableOn_laplace_moment hfm hM n hs)
    ((integrableOn_laplace_moment hfm hM (n + 1) hs).neg.aestronglyMeasurable)
    (bound := fun t : ℝ => M * (t ^ (n + 1) * Real.exp (-((β - α) * t))))
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht z hz
      rw [norm_neg]
      exact norm_laplace_moment_le hM (n + 1) ht.le hz.le)
    (by
      simpa only [Real.rpow_natCast] using!
        (integrableOn_rpow_mul_exp_neg_mul (r := (n + 1 : ℕ))
          (by have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n; linarith)
          (sub_pos.mpr hβ)).const_mul M)
    (Eventually.of_forall fun t z _ => by
      convert (((hasDerivAt_id z).neg.mul_const (t : ℂ)).cexp.mul_const
        ((t : ℂ) ^ n * f t)) using 1 <;> simp [pow_succ]
      ring)
  simpa only [integral_neg, laplaceTransform] using! hd.2

/-- DLMF 1.14.23: `(-1)ⁿ (dⁿ/dsⁿ) 𝓛(f)(s) = 𝓛(f_n)(s)` with `f_n(t) = tⁿ f(t)`, for `ℜs > α`. -/
@[dlmf 1.14.E23]
theorem iteratedDeriv_laplaceTransform {f : ℝ → ℂ} {α : ℝ} (hf : LocallyIntegrableOn f (Ici 0))
    (hg : IsOfExponentialGrowth f α) (n : ℕ) {s : ℂ} (hs : α < s.re) :
    (-1) ^ n * iteratedDeriv n (laplaceTransform f) s =
      laplaceTransform (fun t => (t : ℂ) ^ n * f t) s := by
  have hi : ∀ k : ℕ, ∀ z : ℂ, α < z.re →
      iteratedDeriv k (laplaceTransform f) z =
        (-1) ^ k * laplaceTransform (fun t => (t : ℂ) ^ k * f t) z := by
    intro k
    induction k with
    | zero => intro z hz; simp
    | succ k ih =>
      intro z hz
      have he : iteratedDeriv k (laplaceTransform f) =ᶠ[𝓝 z]
          fun w => (-1) ^ k * laplaceTransform (fun t => (t : ℂ) ^ k * f t) w := by
        filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz]
          with w hw using ih w hw
      rw [iteratedDeriv_succ, he.deriv_eq,
        ((hasDerivAt_laplaceTransform_moment hf hg k hz).const_mul ((-1 : ℂ) ^ k)).deriv]
      ring
  rw [hi n s hs, ← mul_assoc, ← mul_pow]
  simp

/-- A finite limit of `f(t)/t` at zero supplies the extra convergence needed
when integrating the Laplace transform along a horizontal ray. -/
private lemma integrableOn_laplace_quotient {f : ℝ → ℂ} {α : ℝ}
    (hf : LocallyIntegrableOn f (Ici 0)) (hg : IsOfExponentialGrowth f α) {l : ℂ}
    (hl : Tendsto (fun t : ℝ => f t / t) (𝓝[>] 0) (𝓝 l)) {s : ℂ} (hs : α < s.re) :
    IntegrableOn (fun t : ℝ => cexp (-s * t) * (f t / t)) (Ioi 0) := by
  let F : ℝ → ℂ := fun t => cexp (-s * t) * (f t / t)
  have hw : ContinuousOn (fun t : ℝ => cexp (-s * t) / t) (Ioi 0) := by
    intro t ht
    exact ((by fun_prop : ContinuousAt (fun u : ℝ => cexp (-s * u)) t).div
      Complex.continuous_ofReal.continuousAt (ofReal_ne_zero.mpr ht.ne')).continuousWithinAt
  have hloc : LocallyIntegrableOn F (Ioi 0) := by
    have h := (hf.mono_set Ioi_subset_Ici_self).continuousOn_mul hw isOpen_Ioi.isLocallyClosed
    convert h using 1
    ext t
    dsimp [F]
    ring
  have he0 : Tendsto (fun t : ℝ => cexp (-s * t)) (𝓝[>] 0) (𝓝 1) := by
    have hc : Continuous (fun t : ℝ => cexp (-s * t)) := by fun_prop
    simpa only [ofReal_zero, mul_zero, Complex.exp_zero] using
      (hc.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
  have hzero : F =O[𝓝[>] 0] (fun _ : ℝ => (1 : ℝ)) :=
    isBigO_const_of_tendsto (by simpa only [one_mul] using he0.mul hl) one_ne_zero
  obtain ⟨M, hM⟩ := hg
  have hM0 : 0 ≤ M := (norm_nonneg (f 0)).trans (by simpa using hM 0 le_rfl)
  have htop : F =O[atTop] (fun t : ℝ => Real.exp (-(s.re - α) * t)) := by
    refine IsBigO.of_bound M ?_
    filter_upwards [eventually_ge_atTop 1] with t ht
    have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
    dsimp [F]
    rw [norm_mul, norm_div, norm_exp, norm_real, Real.norm_eq_abs, abs_of_pos ht0,
      Real.abs_exp]
    simp only [mul_re, neg_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
    calc Real.exp (-s.re * t) * (‖f t‖ / t) ≤
        Real.exp (-s.re * t) * (M * Real.exp (α * t)) := by
          apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
          exact (div_le_div_of_nonneg_right (hM t ht0.le) ht0.le).trans
            (div_le_self (by positivity) ht)
      _ = M * Real.exp (-(s.re - α) * t) := by
        rw [mul_left_comm, ← Real.exp_add]
        congr 2
        ring
  have htop' := htop.trans
    (isLittleO_exp_neg_mul_rpow_atTop (by linarith : 0 < s.re - α) (-2)).isBigO
  have hi := mellinConvergent_of_isBigO_rpow (s := (1 : ℂ)) (a := 2) (b := 0)
    hloc htop' (by norm_num) (by simpa using hzero) (by norm_num)
  simpa only [MellinConvergent, sub_self, cpow_zero, one_smul] using hi

/-- DLMF 1.14.24: if moreover `lim_{t→0+} f(t)/t` exists, then
`∫_s^∞ 𝓛(f)(u) du = 𝓛(f_{-1})(s)` with `f_{-1}(t) = f(t)/t`, the integral along the horizontal ray
`u = s + v`, `v ≥ 0`. -/
@[dlmf 1.14.E24]
theorem integral_laplaceTransform_ray {f : ℝ → ℂ} {α : ℝ} (hf : LocallyIntegrableOn f (Ici 0))
    (hg : IsOfExponentialGrowth f α) {l : ℂ}
    (hl : Tendsto (fun t : ℝ => f t / t) (𝓝[>] 0) (𝓝 l)) {s : ℂ} (hs : α < s.re) :
    ∫ v in Ioi (0 : ℝ), laplaceTransform f (s + v) = laplaceTransform (fun t => f t / t) s := by
  exact Complex.integral_Ioi_integral_cexp_add_mul
    (hf.mono_set Ioi_subset_Ici_self).aestronglyMeasurable
    (integrableOn_laplace_quotient hf hg hl hs)

/-- Translate a positive half-line integral to start at zero, including totalized integrals. -/
private lemma integral_Ioi_eq_integral_shift (F : ℝ → ℂ) (a : ℝ) :
    (∫ t in Ioi a, F t) = ∫ t in Ioi (0 : ℝ), F (t + a) := by
  rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi]
  rw [← integral_add_right_eq_self ((Ioi a).indicator F) a]
  congr 1
  funext t
  by_cases ht : 0 < t
  · simp [indicator_of_mem, ht, show a < t + a by linarith]
  · simp [indicator_of_notMem, ht, show ¬a < t + a by linarith]

/-- A constant multiplier under a shift determines the tail of the Laplace integral. -/
private lemma laplace_tail_of_multiplier {f : ℝ → ℂ} {a : ℝ} {c : ℂ}
    (hper : ∀ t, 0 < t → f (t + a) = c * f t) (s : ℂ) :
    (∫ t in Ioi a, cexp (-s * t) * f t) =
      c * cexp (-a * s) * laplaceTransform f s := by
  rw [integral_Ioi_eq_integral_shift]
  have he : (∫ t in Ioi (0 : ℝ), cexp (-s * ((t + a : ℝ) : ℂ)) * f (t + a)) =
      ∫ t in Ioi (0 : ℝ), (c * cexp (-a * s)) * (cexp (-s * t) * f t) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    rw [hper t ht]
    push_cast
    rw [show -s * ((t : ℂ) + a) = -a * s + -s * t by ring, Complex.exp_add]
    ring
  rw [he, integral_const_mul, laplaceTransform]

/-- Sum the Laplace integral over repeated shifts with a multiplier of norm at most one. -/
private lemma laplaceTransform_of_shift_mul {f : ℝ → ℂ} {α a : ℝ} {c : ℂ}
    (ha : 0 < a) (hc : ‖c‖ ≤ 1)
    (hf : LocallyIntegrableOn f (Ici 0)) (hg : IsOfExponentialGrowth f α)
    (hper : ∀ t, 0 < t → f (t + a) = c * f t) {s : ℂ} (hs : α < s.re) (hs0 : 0 < s.re) :
    laplaceTransform f s =
      (1 - c * cexp (-a * s))⁻¹ * ∫ t in (0 : ℝ)..a, cexp (-s * t) * f t := by
  have hi := integrableOn_laplace_integrand hf hg hs
  have ht := laplace_tail_of_multiplier hper s
  have he := intervalIntegral.integral_interval_add_Ioi hi (hi.mono_set (Ioi_subset_Ioi ha.le))
  rw [ht] at he
  have hn : ‖c * cexp (-a * s)‖ < 1 := by
    rw [norm_mul]
    calc ‖c‖ * ‖cexp (-a * s)‖ ≤ 1 * ‖cexp (-a * s)‖ := by gcongr
      _ < 1 := by
        rw [one_mul, Complex.norm_exp, Real.exp_lt_one_iff]
        simp only [mul_re, neg_re, ofReal_re, neg_im, ofReal_im, neg_zero, zero_mul, sub_zero]
        nlinarith
  have hne : 1 - c * cexp (-a * s) ≠ 0 := by
    intro h
    have heq := sub_eq_zero.mp h
    rw [← heq, norm_one] at hn
    exact lt_irrefl _ hn
  apply (mul_left_cancel₀ hne)
  rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul]
  change (∫ t in (0 : ℝ)..a, cexp (-s * t) * f t) +
    c * cexp (-a * s) * laplaceTransform f s = laplaceTransform f s at he
  linear_combination -he

/-- DLMF 1.14.25: if `a > 0` and `f(t + a) = f(t)` for `t > 0`, then
`𝓛(f)(s) = (1 - e^{-as})⁻¹ ∫₀^a e^{-st} f(t) dt`. -/
@[dlmf 1.14.E25]
theorem laplaceTransform_of_periodic {f : ℝ → ℂ} {α a : ℝ} (ha : 0 < a)
    (hf : LocallyIntegrableOn f (Ici 0)) (hg : IsOfExponentialGrowth f α)
    (hper : ∀ t, 0 < t → f (t + a) = f t) {s : ℂ} (hs : α < s.re) (hs0 : 0 < s.re) :
    laplaceTransform f s =
      (1 - cexp (-a * s))⁻¹ * ∫ t in (0 : ℝ)..a, cexp (-s * t) * f t := by
  simpa only [one_mul] using laplaceTransform_of_shift_mul (c := 1) ha (by norm_num)
    hf hg (by simpa only [one_mul] using hper) hs hs0

/-- DLMF 1.14.26: if `a > 0` and `f(t + a) = -f(t)` for `t > 0`, then
`𝓛(f)(s) = (1 + e^{-as})⁻¹ ∫₀^a e^{-st} f(t) dt`. -/
@[dlmf 1.14.E26]
theorem laplaceTransform_of_antiperiodic {f : ℝ → ℂ} {α a : ℝ} (ha : 0 < a)
    (hf : LocallyIntegrableOn f (Ici 0)) (hg : IsOfExponentialGrowth f α)
    (hper : ∀ t, 0 < t → f (t + a) = -f t) {s : ℂ} (hs : α < s.re) (hs0 : 0 < s.re) :
    laplaceTransform f s =
      (1 + cexp (-a * s))⁻¹ * ∫ t in (0 : ℝ)..a, cexp (-s * t) * f t := by
  simpa only [neg_one_mul, sub_neg_eq_add] using
    laplaceTransform_of_shift_mul (c := -1) ha (by norm_num)
      hf hg (by simpa only [neg_one_mul] using hper) hs hs0

/-- The exponentially damped original function tends to zero inside its Laplace half-plane. -/
private lemma laplace_integrand_tendsto_zero {f : ℝ → ℂ} {α : ℝ}
    (hg : IsOfExponentialGrowth f α) {s : ℂ} (hs : α < s.re) :
    Tendsto (fun t : ℝ => cexp (-s * t) * f t) atTop (𝓝 0) := by
  obtain ⟨M, hM⟩ := hg
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have he : Tendsto (fun t : ℝ => M * Real.exp (-(s.re - α) * t)) atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_def, id_eq] using!
      (Real.tendsto_exp_atBot.comp (tendsto_const_nhds.neg_mul_atTop
        (by linarith : -(s.re - α) < 0) tendsto_id)).const_mul M
  refine squeeze_zero' (Eventually.of_forall fun t => norm_nonneg _) ?_ he
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  rw [norm_mul, Complex.norm_exp]
  have hre : (-s * (t : ℂ)).re = -s.re * t := by simp
  rw [hre]
  calc Real.exp (-s.re * t) * ‖f t‖ ≤
        Real.exp (-s.re * t) * (M * Real.exp (α * t)) :=
          mul_le_mul_of_nonneg_left (hM t ht) (Real.exp_pos _).le
    _ = M * Real.exp (-(s.re - α) * t) := by
        rw [mul_left_comm, ← Real.exp_add]; congr 2; ring

/-- DLMF 1.14.27: if `f` is continuous on `[0, ∞)`, differentiable on `(0, ∞)` with locally
integrable derivative `f'`, and `f`, `f'` are of exponential growth `α`, then
`𝓛(f')(s) = s 𝓛(f)(s) - f(0+)` for `ℜs > α`. -/
@[dlmf 1.14.E27]
theorem laplaceTransform_deriv {f f' : ℝ → ℂ} {α : ℝ} (hf : ContinuousOn f (Ici 0))
    (hderiv : ∀ t, 0 < t → HasDerivAt f (f' t) t) (hf' : LocallyIntegrableOn f' (Ici 0))
    (hg : IsOfExponentialGrowth f α) (hg' : IsOfExponentialGrowth f' α) {s : ℂ}
    (hs : α < s.re) :
    laplaceTransform f' s = s * laplaceTransform f s - f 0 := by
  have hfi := integrableOn_laplace_integrand (hf.locallyIntegrableOn measurableSet_Ici) hg hs
  have hf'i := integrableOn_laplace_integrand hf' hg' hs
  have hc : ContinuousOn (fun t : ℝ => cexp (-s * t) * f t) (Ici 0) :=
    (by fun_prop : Continuous fun t : ℝ => cexp (-s * t)).continuousOn.mul hf
  have hd : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt (fun t : ℝ => cexp (-s * t) * f t)
      (cexp (-s * t) * f' t - s * (cexp (-s * t) * f t)) t := by
    intro t ht
    convert! (((Complex.ofRealCLM.hasDerivAt (x := t)).const_mul (-s)).cexp.mul
      (hderiv t ht)) using 1
    simp [Complex.ofRealCLM_apply]
    ring
  have he := integral_Ioi_of_hasDerivAt_of_tendsto (hc 0 (by simp)) hd
    (hf'i.sub (hfi.const_mul s)) (laplace_integrand_tendsto_zero hg hs)
  rw [integral_sub hf'i (hfi.const_mul s), integral_const_mul] at he
  simp only [ofReal_zero, mul_zero, Complex.exp_zero, one_mul, zero_sub] at he
  change laplaceTransform f' s - s * laplaceTransform f s = -f 0 at he
  linear_combination he

/-- DLMF 1.14.28: if `f` has jump discontinuities at `0 = t₀ < t₁ < ⋯ < tₙ` and is differentiable
elsewhere on `(0, ∞)` with locally integrable derivative `f'`, then
`𝓛(f')(s) = s 𝓛(f)(s) - f(0+) - ∑_{k=1}^{n} e^{-s t_k}(f(t_k+) - f(t_k-))`. -/
@[dlmf 1.14.E28]
theorem laplaceTransform_deriv_of_jumps {f f' : ℝ → ℂ} {α : ℝ} {n : ℕ} {τ : ℕ → ℝ}
    (hτ0 : τ 0 = 0) (hτ : ∀ k < n, τ k < τ (k + 1))
    (hderiv : ∀ t, 0 < t → t ∉ τ '' (Finset.range (n + 1) : Set ℕ) → HasDerivAt f (f' t) t)
    (hf : LocallyIntegrableOn f (Ici 0)) (hf' : LocallyIntegrableOn f' (Ici 0))
    (hg : IsOfExponentialGrowth f α) (hg' : IsOfExponentialGrowth f' α) {fp fm : ℕ → ℂ}
    (hp : ∀ k ≤ n, Tendsto f (𝓝[>] (τ k)) (𝓝 (fp k)))
    (hm : ∀ k ≤ n, 0 < k → Tendsto f (𝓝[<] (τ k)) (𝓝 (fm k))) {s : ℂ} (hs : α < s.re) :
    laplaceTransform f' s = s * laplaceTransform f s - fp 0 -
      ∑ k ∈ Finset.Icc 1 n, cexp (-s * τ k) * (fp k - fm k) := by
  sorry

/-- DLMF 1.14.29: if `f, f', …, f^{(n-1)}` are continuous on `[0, ∞)` and of exponential growth,
and `f^{(n)}` is locally integrable (and of exponential growth), then
`𝓛(f^{(n)})(s) = sⁿ 𝓛(f)(s) - s^{n-1} f(0+) - ⋯ - f^{(n-1)}(0+)`. The derivatives are given as a
family `g k` with `g 0 = f` and `(g k)' = g (k + 1)` on `(0, ∞)`. -/
@[dlmf 1.14.E29]
theorem laplaceTransform_iteratedDeriv {g : ℕ → ℝ → ℂ} {α : ℝ} {n : ℕ}
    (hcont : ∀ k < n, ContinuousOn (g k) (Ici 0))
    (hderiv : ∀ k < n, ∀ t, 0 < t → HasDerivAt (g k) (g (k + 1) t) t)
    (hloc : LocallyIntegrableOn (g n) (Ici 0)) (hg : ∀ k ≤ n, IsOfExponentialGrowth (g k) α)
    {s : ℂ} (hs : α < s.re) :
    laplaceTransform (g n) s =
      s ^ n * laplaceTransform (g 0) s - ∑ k ∈ Finset.range n, s ^ (n - 1 - k) * g k 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn : n < n + 1 := Nat.lt_succ_self n
    have hp := ih (fun k hk => hcont k (Nat.lt_trans hk hn))
      (fun k hk => hderiv k (Nat.lt_trans hk hn))
      ((hcont n hn).locallyIntegrableOn measurableSet_Ici)
      (fun k hk => hg k (Nat.le_trans hk hn.le))
    have he := laplaceTransform_deriv (hcont n hn) (hderiv n hn) hloc
      (hg n hn.le) (hg (n + 1) le_rfl) hs
    rw [he, hp, Finset.sum_range_succ]
    have hsum : s * (∑ k ∈ Finset.range n, s ^ (n - 1 - k) * g k 0) =
        ∑ k ∈ Finset.range n, s ^ (n - k) * g k 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      have hk : k < n := Finset.mem_range.mp hk
      rw [show n - k = (n - 1 - k) + 1 by omega, pow_succ]
      ring
    simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, one_mul]
    rw [mul_sub, hsum, pow_succ]
    ring

/-- Extending weighted functions by zero identifies Laplace convolution with ordinary convolution.
-/
private lemma convolution_laplace_integrands (f g : ℝ → ℂ) (s : ℂ) :
    convolution ((Ioi (0 : ℝ)).indicator (fun t => cexp (-s * t) * f t))
      ((Ioi (0 : ℝ)).indicator (fun t => cexp (-s * t) * g t))
      (ContinuousLinearMap.mul ℂ ℂ) volume =
      (Ioi (0 : ℝ)).indicator (fun t => cexp (-s * t) * laplaceConvolution f g t) := by
  funext t
  simp only [convolution, ContinuousLinearMap.mul_apply']
  by_cases ht : 0 < t
  · rw [indicator_of_mem ht, laplaceConvolution, ← intervalIntegral.integral_const_mul,
      intervalIntegral.integral_of_le ht.le, ← integral_Icc_eq_integral_Ioc,
      integral_Icc_eq_integral_Ioo, ← integral_indicator measurableSet_Ioo]
    apply integral_congr_ae (Eventually.of_forall fun u => ?_)
    by_cases hu : 0 < u ∧ u < t
    · have htu : 0 < t - u := sub_pos.mpr hu.2
      rw [indicator_of_mem hu.1, indicator_of_mem htu, indicator_of_mem hu]
      have he : cexp (-s * u) * cexp (-s * ((t - u : ℝ) : ℂ)) = cexp (-s * t) := by
        rw [← Complex.exp_add]
        congr 1
        push_cast
        ring
      calc cexp (-s * u) * f u * (cexp (-s * ((t - u : ℝ) : ℂ)) * g (t - u)) =
          (cexp (-s * u) * cexp (-s * ((t - u : ℝ) : ℂ))) * (f u * g (t - u)) := by ring
        _ = _ := by rw [he]
    · have hn : u ∉ Ioo (0 : ℝ) t := hu
      rw [indicator_of_notMem hn]
      by_cases hu0 : 0 < u
      · have htu : ¬ 0 < t - u := by simp only [sub_pos]; tauto
        simp [indicator, hu0, htu]
      · rw [indicator_of_notMem hu0, zero_mul]
  · rw [indicator_of_notMem ht]
    apply integral_eq_zero_of_ae
    exact Eventually.of_forall fun u => by
      dsimp only
      by_cases hu : 0 < u
      · have htu : ¬ 0 < t - u := by linarith
        simp [indicator, hu, htu]
      · simp [indicator, hu]

/-- DLMF 1.14.31 (convolution theorem): `𝓛(f * g) = 𝓛(f) 𝓛(g)` for the Laplace convolution
1.14.30, for `ℜs > α`. -/
@[dlmf 1.14.E31]
theorem laplaceTransform_laplaceConvolution {f g : ℝ → ℂ} {α : ℝ}
    (hf : LocallyIntegrableOn f (Ici 0)) (hg : LocallyIntegrableOn g (Ici 0))
    (hfe : IsOfExponentialGrowth f α) (hge : IsOfExponentialGrowth g α) {s : ℂ}
    (hs : α < s.re) :
    laplaceTransform (laplaceConvolution f g) s = laplaceTransform f s * laplaceTransform g s := by
  have hfi := (integrable_indicator_iff measurableSet_Ioi).mpr
    (integrableOn_laplace_integrand hf hfe hs)
  have hgi := (integrable_indicator_iff measurableSet_Ioi).mpr
    (integrableOn_laplace_integrand hg hge hs)
  have he := integral_convolution (L := ContinuousLinearMap.mul ℂ ℂ) hfi hgi
  rw [convolution_laplace_integrands] at he
  simpa only [integral_indicator measurableSet_Ioi, ContinuousLinearMap.mul_apply',
    laplaceTransform] using he

/-- DLMF §1.14(iii) (uniqueness, Lerch): if `f`, `g` are continuous on `[0, ∞)`, of exponential
growth `α`, and `𝓛(f)(s) = 𝓛(g)(s)` for all real `s > α`, then `f = g` on `[0, ∞)`. -/
@[dlmf 1.14.iii]
theorem eqOn_of_laplaceTransform_eq {f g : ℝ → ℂ} {α : ℝ} (hf : ContinuousOn f (Ici 0))
    (hg : ContinuousOn g (Ici 0)) (hfe : IsOfExponentialGrowth f α)
    (hge : IsOfExponentialGrowth g α)
    (h : ∀ s : ℝ, α < s → laplaceTransform f s = laplaceTransform g s) :
    EqOn f g (Ici 0) := by
  sorry

end DLMF.AlgebraicAnalytic
