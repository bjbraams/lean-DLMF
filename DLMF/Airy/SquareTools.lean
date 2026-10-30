/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Airy.Integrals
public import DLMFMathlib.Analysis.ODE.SymmetricSquare
public import DLMFMathlib.Analysis.SpecialFunctions.Pow.ComplexReal

/-!
# Ai² as a Gaussian average of Ai

The representation `Ai(x)² = (2^{2/3}/π) ∫₀^∞ Ai(2^{2/3}(x + t²)) dt` for real `x`
(`airyAi_sq_eq_integral`), the basic tool for the product integrals of DLMF §9.11.

Proof: with `c = 2^{2/3}` and `F(x) = ∫₀^∞ Ai(c(x+t²)) dt`,
* differentiation under the integral sign (Gaussian domination from the bounds 9.7.15) gives
  `F' = c ∫ Ai'`, `F'' = c² ∫ u Ai(u)`, `F''' = c³ ∫ (Ai + u Ai')`, and an integration by parts
  in `t` turns this into the product equation `F''' - 4xF' - 2F = 0` (DLMF 9.11.1);
* the Wronskian of three solutions of 9.11.1 is constant, and that of `Ai², Ai Bi, Bi²` is
  `2/π³` (9.11.2), so Cramer's rule writes `F = a Ai² + b Ai Bi + d Bi²`;
* `x^{1/2} F(x) → 0`, `x^{1/2} Ai² → 0` and `x^{1/2} Ai Bi → 1/(2π)` (9.7.5, 9.7.7) force
  `b = d = 0`;
* `F(0)` is the Mellin transform 9.10.17 at `α = 1/2`, and Legendre's duplication formula with
  `Γ(1/3)Γ(2/3) = 2π/√3` gives `a = π/c`.

For the Mellin transform 9.11.15 the representation is rewritten with `s = t²` as
`x^{α-1} Ai(x)² = (c/2π) ∫ Φ(x, v) dv` with `Φ(x, v) = 1_{x<v} x^{α-1} (v-x)^{-1/2} Ai(cv)`;
Fubini (`airySq_double`) reduces the `x`-integral to a Beta integral, and the remaining
`v`-integral is the Mellin transform 9.10.17 at `α + 1/2` after scaling (`airySq_scaled_mellin`).

The helpers carry the prefix `airySq_`.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics
open scoped Real Topology
namespace DLMF.Airy

/-- `u^2 e^{-u/6} ≤ 72`, in the form `u^2 e^{-2u/3} ≤ 72 e^{-u/2}`. -/
theorem airySq_sq_mul_exp_le {u : ℝ} (hu : 0 ≤ u) :
    u ^ 2 * Real.exp (-(2 / 3) * u) ≤ 72 * Real.exp (-u / 2) := by
  have h := Real.quadratic_le_exp_of_nonneg (show 0 ≤ u / 6 by positivity)
  have h2 : u ^ 2 ≤ 72 * Real.exp (u / 6) := by nlinarith [sq_nonneg u]
  have e : Real.exp (-u / 2) = Real.exp (u / 6) * Real.exp (-(2 / 3) * u) := by
    rw [← Real.exp_add]; ring_nf
  rw [e, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le

/-- `ζ(u) ≥ 2u/3` for `u ≥ 1`. -/
theorem airySq_zeta_ge {u : ℝ} (hu : 1 ≤ u) : 2 / 3 * u ≤ airyZeta u := by
  unfold airyZeta
  have : u ^ (1 : ℝ) ≤ u ^ (3 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hu (by norm_num)
  rw [Real.rpow_one] at this
  linarith

/-- `0 < Ai(u) ≤ e^{-2u/3}` for `u ≥ 1`. -/
theorem airySq_ai_le {u : ℝ} (hu : 1 ≤ u) : |airyAiReal u| ≤ Real.exp (-(2 / 3) * u) := by
  have hu0 : 0 < u := by linarith
  rw [abs_of_pos (airyAiReal_pos hu0.le)]
  refine (airy_ai_bound hu0).trans ?_
  have hs : 1 ≤ Real.sqrt π := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by linarith [Real.pi_gt_three])
  have hq : 1 ≤ u ^ (1 / 4 : ℝ) := Real.one_le_rpow hu (by norm_num)
  have hd : 1 ≤ 2 * Real.sqrt π * u ^ (1 / 4 : ℝ) := by nlinarith
  calc Real.exp (-airyZeta u) / (2 * Real.sqrt π * u ^ (1 / 4 : ℝ)) ≤ Real.exp (-airyZeta u) :=
        div_le_self (Real.exp_pos _).le hd
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith [airySq_zeta_ge hu])

/-- `|Ai'(u)| ≤ u e^{-2u/3}` for `u ≥ 1`. -/
theorem airySq_aiDeriv_le {u : ℝ} (hu : 1 ≤ u) :
    |airyAiDerivReal u| ≤ u * Real.exp (-(2 / 3) * u) := by
  have hu0 : 0 < u := by linarith
  refine (airy_aiDeriv_bound hu0).trans ?_
  have hz := airyInt_two_thirds_le_airyZeta hu
  have hs : 1 ≤ Real.sqrt π := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by linarith [Real.pi_gt_three])
  have h3 : 7 / (72 * airyZeta u) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
  have hq : u ^ (1 / 4 : ℝ) ≤ u := by
    simpa using Real.rpow_le_rpow_of_exponent_le hu (show (1 / 4 : ℝ) ≤ 1 by norm_num)
  have he : Real.exp (-airyZeta u) ≤ Real.exp (-(2 / 3) * u) :=
    Real.exp_le_exp.mpr (by linarith [airySq_zeta_ge hu])
  have hq0 : 0 ≤ u ^ (1 / 4 : ℝ) := by positivity
  have hE := (Real.exp_pos (-airyZeta u)).le
  calc u ^ (1 / 4 : ℝ) * Real.exp (-airyZeta u) / (2 * Real.sqrt π) * (1 + 7 / (72 * airyZeta u))
      ≤ u * Real.exp (-(2 / 3) * u) / (2 * 1) * (1 + 1) := by gcongr
    _ = _ := by ring

/-- The exponential decay class used for the Ai² representation. -/
def AirySqDecay (h : ℝ → ℝ) : Prop := ∃ K, ∀ u, 1 ≤ u → |h u| ≤ K * Real.exp (-u / 2)

/-- Extension of the decay bound to every half-line `[a, ∞)`, by compactness. -/
theorem AirySqDecay.ext {h : ℝ → ℝ} (hd : AirySqDecay h) (hc : Continuous h) (a : ℝ) :
    ∃ K, 0 ≤ K ∧ ∀ u, a ≤ u → |h u| ≤ K * Real.exp (-u / 2) := by
  obtain ⟨K, hK⟩ := hd
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := a) (b := 1)).exists_bound_of_continuousOn
    hc.continuousOn
  have hK0 : 0 ≤ max K 0 := le_max_right _ _
  have hM0 : 0 ≤ max M 0 * Real.exp (1 / 2) := by positivity
  refine ⟨max K 0 + max M 0 * Real.exp (1 / 2), by positivity, fun u hu => ?_⟩
  have hE := (Real.exp_pos (-u / 2)).le
  by_cases h1 : 1 ≤ u
  · refine (hK u h1).trans ?_
    nlinarith [le_max_left K 0]
  · replace h1 := not_le.mp h1
    have hb := hM u ⟨hu, h1.le⟩
    rw [Real.norm_eq_abs] at hb
    have he : 1 ≤ Real.exp (1 / 2) * Real.exp (-u / 2) := by
      rw [← Real.exp_add]; exact Real.one_le_exp (by linarith)
    have : max M 0 ≤ max M 0 * Real.exp (1 / 2) * Real.exp (-u / 2) := by
      rw [mul_assoc]; exact le_mul_of_one_le_right (le_max_right _ _) he
    nlinarith [le_max_left M 0]

/-- A bound `|h u| ≤ 2 u² e^{-2u/3}` for `u ≥ 1` implies the decay class `|h u| ≤ K e^{-u/2}`. -/
theorem airySq_decay_of_le {h : ℝ → ℝ} (hb : ∀ u, 1 ≤ u → |h u| ≤ 2 * (u ^ 2 * Real.exp (-(2 / 3) * u))) :
    AirySqDecay h :=
  ⟨144, fun u hu => (hb u hu).trans (by nlinarith [airySq_sq_mul_exp_le (u := u) (by linarith)])⟩

/-- `Ai` restricted to the reals lies in the exponential decay class. -/
theorem airySq_decay_ai : AirySqDecay airyAiReal := by
  refine airySq_decay_of_le fun u hu => (airySq_ai_le hu).trans ?_
  have := Real.exp_pos (-(2 / 3) * u)
  nlinarith [one_le_pow₀ (n := 2) hu]

/-- `Ai'` restricted to the reals lies in the exponential decay class. -/
theorem airySq_decay_aiDeriv : AirySqDecay airyAiDerivReal := by
  refine airySq_decay_of_le fun u hu => (airySq_aiDeriv_le hu).trans ?_
  have := Real.exp_pos (-(2 / 3) * u)
  have : u ≤ u ^ 2 := by nlinarith
  nlinarith

/-- `u ↦ u Ai(u)` lies in the exponential decay class. -/
theorem airySq_decay_mul_ai : AirySqDecay fun u => u * airyAiReal u := by
  refine airySq_decay_of_le fun u hu => ?_
  have h := airySq_ai_le hu
  have := Real.exp_pos (-(2 / 3) * u)
  rw [abs_mul, abs_of_pos (by linarith : 0 < u)]
  have : u ≤ u ^ 2 := by nlinarith
  have h1 : u * |airyAiReal u| ≤ u * Real.exp (-(2 / 3) * u) :=
    mul_le_mul_of_nonneg_left h (by linarith)
  nlinarith

/-- `u ↦ Ai(u) + u Ai'(u)` lies in the exponential decay class. -/
theorem airySq_decay_ai_add : AirySqDecay fun u => airyAiReal u + u * airyAiDerivReal u := by
  refine airySq_decay_of_le fun u hu => ?_
  have h := airySq_ai_le hu
  have h' := airySq_aiDeriv_le hu
  have := Real.exp_pos (-(2 / 3) * u)
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_of_pos (by linarith : 0 < u)]
  have h1 : u * |airyAiDerivReal u| ≤ u * (u * Real.exp (-(2 / 3) * u)) :=
    mul_le_mul_of_nonneg_left h' (by linarith)
  have : 1 ≤ u ^ 2 := by nlinarith
  nlinarith

/-- The Gaussian bound on the integrand `h(c(x+t²))`, uniformly for `x ≥ b`. -/
theorem airySq_bound {h : ℝ → ℝ} (hd : AirySqDecay h) (hc : Continuous h) {c : ℝ} (hc0 : 0 < c)
    (b : ℝ) : ∃ K, 0 ≤ K ∧ ∀ x, b ≤ x → ∀ t : ℝ,
      |h (c * (x + t ^ 2))| ≤ K * Real.exp (-(c / 2) * t ^ 2) := by
  obtain ⟨K, hK0, hK⟩ := hd.ext hc (c * b)
  refine ⟨K * Real.exp (-(c * b) / 2), by positivity, fun x hx t => ?_⟩
  have hu : c * b ≤ c * (x + t ^ 2) := mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg t]) hc0.le
  refine (hK _ hu).trans ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hK0
  rw [← Real.exp_add]
  exact Real.exp_le_exp.mpr (by nlinarith [sq_nonneg t])

/-- For `h` continuous in the decay class and `c > 0`, `t ↦ h(c(x+t²))` is integrable on `ℝ`. -/
theorem airySq_integrable {h : ℝ → ℝ} (hd : AirySqDecay h) (hc : Continuous h) {c : ℝ}
    (hc0 : 0 < c) (x : ℝ) : Integrable (fun t : ℝ => h (c * (x + t ^ 2))) := by
  obtain ⟨K, -, hK⟩ := airySq_bound hd hc hc0 x
  refine ((integrable_exp_neg_mul_sq (by positivity : 0 < c / 2)).const_mul K).mono'
    (by fun_prop) (Eventually.of_forall fun t => ?_)
  rw [Real.norm_eq_abs]; exact hK x le_rfl t

/-- Differentiation under the integral sign for `x ↦ ∫₀^∞ h(c(x+t²)) dt`. -/
theorem airySq_hasDerivAt {h h' : ℝ → ℝ} (hd : AirySqDecay h) (hc : Continuous h)
    (hd' : AirySqDecay h') (hc' : Continuous h') (hder : ∀ u, HasDerivAt h (h' u) u)
    {c : ℝ} (hc0 : 0 < c) (x₀ : ℝ) :
    HasDerivAt (fun x => ∫ t in Ioi 0, h (c * (x + t ^ 2)))
      (c * ∫ t in Ioi 0, h' (c * (x₀ + t ^ 2))) x₀ := by
  obtain ⟨K, hK0, hK⟩ := airySq_bound hd' hc' hc0 (x₀ - 1)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi 0))
    (F := fun x t => h (c * (x + t ^ 2))) (F' := fun x t => c * h' (c * (x + t ^ 2)))
    (bound := fun t => c * (K * Real.exp (-(c / 2) * t ^ 2))) (x₀ := x₀)
    (Metric.ball_mem_nhds x₀ one_pos)
    (Eventually.of_forall fun x => (by fun_prop : Continuous fun t : ℝ => h (c * (x + t ^ 2))).aestronglyMeasurable)
    (airySq_integrable hd hc hc0 x₀).integrableOn
    (by fun_prop : Continuous fun t : ℝ => c * h' (c * (x₀ + t ^ 2))).aestronglyMeasurable
    (Eventually.of_forall fun t x hx => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos hc0]
      refine mul_le_mul_of_nonneg_left (hK x ?_ t) hc0.le
      have := (Metric.mem_ball.mp hx); rw [Real.dist_eq] at this
      linarith [neg_abs_le (x - x₀)])
    (((integrable_exp_neg_mul_sq (by positivity : 0 < c / 2)).const_mul K).const_mul c).integrableOn
    (Eventually.of_forall fun t x _ => by
      have := (hder (c * (x + t ^ 2))).comp x
        (((hasDerivAt_id x).add_const (t ^ 2)).const_mul c)
      exact this.congr_deriv (by ring))
  rw [integral_const_mul] at key
  exact key.2

/-- The scale `c = 2^{2/3}` of the Ai² representation. -/
def airySq_c : ℝ := (2 : ℝ) ^ (2 / 3 : ℝ)

/-- The scale `c = 2^{2/3}` is positive. -/
theorem airySq_c_pos : 0 < airySq_c := by unfold airySq_c; positivity

/-- The scale satisfies `c³ = 4`. -/
theorem airySq_c_cube : airySq_c ^ 3 = 4 := by
  unfold airySq_c
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num

/-- `F(x) = ∫₀^∞ Ai(c(x+t²)) dt`. -/
def airySq_F (x : ℝ) : ℝ := ∫ t in Ioi 0, airyAiReal (airySq_c * (x + t ^ 2))
/-- `∫₀^∞ Ai'(c(x+t²)) dt`. -/
def airySq_F1 (x : ℝ) : ℝ := ∫ t in Ioi 0, airyAiDerivReal (airySq_c * (x + t ^ 2))
/-- `∫₀^∞ u Ai(u) dt` with `u = c(x+t²)`. -/
def airySq_F2 (x : ℝ) : ℝ := ∫ t in Ioi 0, (fun u => u * airyAiReal u) (airySq_c * (x + t ^ 2))
/-- `∫₀^∞ (Ai(u) + u Ai'(u)) dt` with `u = c(x+t²)`. -/
def airySq_F3 (x : ℝ) : ℝ :=
  ∫ t in Ioi 0, (fun u => airyAiReal u + u * airyAiDerivReal u) (airySq_c * (x + t ^ 2))

/-- `Ai` is continuous on the reals. -/
theorem airySq_cont_ai : Continuous airyAiReal :=
  continuous_iff_continuousAt.mpr fun x => (hasDerivAt_airyAiReal x).continuousAt
/-- `Ai'` is continuous on the reals. -/
theorem airySq_cont_aiDeriv : Continuous airyAiDerivReal :=
  continuous_iff_continuousAt.mpr fun x => (hasDerivAt_airyAiDerivReal x).continuousAt

/-- `F' = c F₁`, where `F(x) = ∫₀^∞ Ai(c(x+t²)) dt` and `F₁` is the same integral of `Ai'`. -/
theorem airySq_hasDerivAt_F (x : ℝ) : HasDerivAt airySq_F (airySq_c * airySq_F1 x) x :=
  airySq_hasDerivAt airySq_decay_ai airySq_cont_ai airySq_decay_aiDeriv airySq_cont_aiDeriv
    hasDerivAt_airyAiReal airySq_c_pos x

/-- `F₁' = c F₂`, where `F₂(x) = ∫₀^∞ u Ai(u) dt` with `u = c(x+t²)`. -/
theorem airySq_hasDerivAt_F1 (x : ℝ) : HasDerivAt airySq_F1 (airySq_c * airySq_F2 x) x :=
  airySq_hasDerivAt airySq_decay_aiDeriv airySq_cont_aiDeriv airySq_decay_mul_ai
    (by have := airySq_cont_ai; fun_prop) hasDerivAt_airyAiDerivReal airySq_c_pos x

/-- `F₂' = c F₃`, where `F₃(x) = ∫₀^∞ (Ai(u) + u Ai'(u)) dt` with `u = c(x+t²)`. -/
theorem airySq_hasDerivAt_F2 (x : ℝ) : HasDerivAt airySq_F2 (airySq_c * airySq_F3 x) x :=
  airySq_hasDerivAt airySq_decay_mul_ai (by have := airySq_cont_ai; fun_prop) airySq_decay_ai_add
    (by have := airySq_cont_ai; have := airySq_cont_aiDeriv; fun_prop)
    (fun u => ((hasDerivAt_id u).mul (hasDerivAt_airyAiReal u)).congr_deriv (by simp))
    airySq_c_pos x

/-- Integrability of `t · 2ct Ai'(c(x+t²))` on `(0, ∞)`. -/
theorem airySq_integrable_ibp (x : ℝ) : IntegrableOn (fun t : ℝ => t * (2 * airySq_c * t *
      airyAiDerivReal (airySq_c * (x + t ^ 2)))) (Ioi 0) := by
  have hc0 := airySq_c_pos
  obtain ⟨K, hK0, hK⟩ := airySq_bound airySq_decay_aiDeriv airySq_cont_aiDeriv hc0 x
  have hi := (integrableOn_rpow_mul_exp_neg_mul_sq (by positivity : 0 < airySq_c / 2)
    (s := 2) (by norm_num)).const_mul (2 * airySq_c * K)
  simp only [Real.rpow_two] at hi
  refine hi.mono' (by have := airySq_cont_aiDeriv; fun_prop) ?_
  refine (ae_restrict_mem measurableSet_Ioi).mono fun t ht => ?_
  rw [Real.norm_eq_abs]
  have := hK x le_rfl t
  rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_pos ht, abs_of_pos hc0, abs_two]
  have ht2 : t * (2 * airySq_c * t * |airyAiDerivReal (airySq_c * (x + t ^ 2))|) =
    2 * airySq_c * t ^ 2 * |airyAiDerivReal (airySq_c * (x + t ^ 2))| := by ring
  rw [ht2, show 2 * airySq_c * K * (t ^ 2 * Real.exp (-(airySq_c / 2) * t ^ 2)) =
    2 * airySq_c * t ^ 2 * (K * Real.exp (-(airySq_c / 2) * t ^ 2)) by ring]
  exact mul_le_mul_of_nonneg_left this (by positivity)

/-- Integration by parts in `t`: `2c ∫₀^∞ t² Ai'(c(x+t²)) dt = -F(x)`. -/
theorem airySq_ibp (x : ℝ) :
    ∫ t in Ioi 0, t * (2 * airySq_c * t * airyAiDerivReal (airySq_c * (x + t ^ 2))) =
      -airySq_F x := by
  have hc0 := airySq_c_pos
  obtain ⟨K, hK0, hK⟩ := airySq_bound airySq_decay_aiDeriv airySq_cont_aiDeriv hc0 x
  obtain ⟨K', hK0', hK'⟩ := airySq_bound airySq_decay_ai airySq_cont_ai hc0 x
  have hv : ∀ t : ℝ, HasDerivAt (fun t : ℝ => airyAiReal (airySq_c * (x + t ^ 2)))
      (2 * airySq_c * t * airyAiDerivReal (airySq_c * (x + t ^ 2))) t := fun t => by
    have := (hasDerivAt_airyAiReal (airySq_c * (x + t ^ 2))).comp t
      (((hasDerivAt_pow 2 t).const_add x).const_mul airySq_c)
    exact this.congr_deriv (by push_cast; ring)
  have h1 := airySq_integrable_ibp x
  have h2 : IntegrableOn (fun t : ℝ => (1 : ℝ) * airyAiReal (airySq_c * (x + t ^ 2))) (Ioi 0) := by
    simpa using (airySq_integrable airySq_decay_ai airySq_cont_ai hc0 x).integrableOn
  have hz : Tendsto (fun t : ℝ => t * airyAiReal (airySq_c * (x + t ^ 2))) (𝓝[>] 0) (𝓝 0) := by
    have : Continuous fun t : ℝ => t * airyAiReal (airySq_c * (x + t ^ 2)) := by
      have := airySq_cont_ai; fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  have hinf : Tendsto (fun t : ℝ => t * airyAiReal (airySq_c * (x + t ^ 2))) atTop (𝓝 0) := by
    have hl := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (airySq_c / 2) (by positivity)).const_mul K'
    rw [mul_zero] at hl
    refine squeeze_zero_norm' ?_ hl
    filter_upwards [eventually_ge_atTop 1] with t ht
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < t), Real.rpow_one]
    have h3 := hK' x le_rfl t
    have h4 : Real.exp (-(airySq_c / 2) * t ^ 2) ≤ Real.exp (-(airySq_c / 2) * t) :=
      Real.exp_le_exp.mpr (by
        have : t ≤ t ^ 2 := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ airySq_c / 2)])
    calc t * |airyAiReal (airySq_c * (x + t ^ 2))| ≤ t * (K' * Real.exp (-(airySq_c / 2) * t)) :=
          mul_le_mul_of_nonneg_left (h3.trans (mul_le_mul_of_nonneg_left h4 hK0')) (by linarith)
      _ = _ := by ring
  have := integral_Ioi_mul_deriv_eq_deriv_mul (u := fun t : ℝ => t) (u' := fun _ => (1 : ℝ))
    (fun t _ => hasDerivAt_id t) (fun t _ => hv t) h1 h2 hz hinf
  simp only [sub_zero, zero_sub, one_mul] at this
  exact this

/-- The product equation for `F`: the derivative of `F'' = c² F₂` is `4x F' + 2F`. -/
theorem airySq_hasDerivAt_F2' (x : ℝ) :
    HasDerivAt (fun x => airySq_c ^ 2 * airySq_F2 x)
      (4 * x * (airySq_c * airySq_F1 x) + 2 * airySq_F x) x := by
  have hc0 := airySq_c_pos
  have h := (airySq_hasDerivAt_F2 x).const_mul (airySq_c ^ 2)
  refine h.congr_deriv ?_
  have e : airySq_F3 x = airySq_F x + airySq_c * x * airySq_F1 x +
      (1 / 2) * ∫ t in Ioi 0, t * (2 * airySq_c * t * airyAiDerivReal (airySq_c * (x + t ^ 2))) := by
    have i0 := airySq_integrable airySq_decay_ai airySq_cont_ai hc0 x
    have i1 := ((airySq_integrable airySq_decay_aiDeriv airySq_cont_aiDeriv hc0 x).integrableOn
      (s := Ioi 0)).const_mul (airySq_c * x)
    have i2 := (airySq_integrable_ibp x).const_mul (1 / 2)
    have i01 : IntegrableOn (fun t : ℝ => airyAiReal (airySq_c * (x + t ^ 2)) +
        airySq_c * x * airyAiDerivReal (airySq_c * (x + t ^ 2))) (Ioi 0) := i0.integrableOn.add i1
    rw [airySq_F, airySq_F1, ← integral_const_mul, ← integral_const_mul, ← integral_add i0.integrableOn i1,
      ← integral_add i01 i2, airySq_F3]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    ring
  rw [e, airySq_ibp, ← mul_assoc, ← pow_succ, airySq_c_cube]
  ring

/-- A solution triple `(y, y', y'')` of the product equation `y''' = 4x y' + 2y` (DLMF 9.11.1). -/
def AirySqIsProdSol (y y1 y2 : ℝ → ℝ) : Prop :=
  ∀ x, HasDerivAt y (y1 x) x ∧ HasDerivAt y1 (y2 x) x ∧ HasDerivAt y2 (4 * x * y1 x + 2 * y x) x

/-- The Wronskian determinant of three triples. -/
def airySq_det (y y1 y2 u u1 u2 v v1 v2 : ℝ → ℝ) (x : ℝ) : ℝ :=
  y x * (u1 x * v2 x - v1 x * u2 x) - u x * (y1 x * v2 x - v1 x * y2 x) +
    v x * (y1 x * u2 x - u1 x * y2 x)

/-- Decomposition along a fundamental system with constant nonzero Wronskian. -/
theorem airySq_decomp_gen {y y1 y2 u u1 u2 v v1 v2 w w1 w2 : ℝ → ℝ} (hy : AirySqIsProdSol y y1 y2)
    (hu : AirySqIsProdSol u u1 u2) (hv : AirySqIsProdSol v v1 v2) (hw : AirySqIsProdSol w w1 w2)
    {D : ℝ} (hW : ∀ x, airySq_det u u1 u2 v v1 v2 w w1 w2 x = D) (hD : D ≠ 0) (x : ℝ) :
    y x = airySq_det y y1 y2 v v1 v2 w w1 w2 0 / D * u x +
      airySq_det u u1 u2 y y1 y2 w w1 w2 0 / D * v x +
      airySq_det u u1 u2 v v1 v2 y y1 y2 0 / D * w x :=
  ODE.thirdOrder_decomp (p := fun x => 4*x) (q := fun _ => 2) hy hu hv hw hW hD x 0

/-- Products of real Airy solutions solve the product equation. -/
theorem airySq_isProdSol_mul {f f' g g' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : ∀ x, HasDerivAt f' (x * f x) x) (hg : ∀ x, HasDerivAt g (g' x) x)
    (hg' : ∀ x, HasDerivAt g' (x * g x) x) :
    AirySqIsProdSol (fun x => f x * g x) (fun x => f' x * g x + f x * g' x)
      (fun x => 2 * x * f x * g x + 2 * f' x * g' x) := by
  change ODE.IsThirdOrderSolution (fun x => 4*x) (fun _ => 2) _ _ _
  simpa only [mul_one] using ODE.product_isThirdOrderSolution
    (fun x => ⟨hf x, hf' x⟩) (fun x => ⟨hg x, hg' x⟩) (fun x => hasDerivAt_id x)

/-- The triple of `F`. -/
theorem airySq_isProdSol_F :
    AirySqIsProdSol airySq_F (fun x => airySq_c * airySq_F1 x) (fun x => airySq_c ^ 2 * airySq_F2 x) :=
  fun x => ⟨airySq_hasDerivAt_F x,
    ((airySq_hasDerivAt_F1 x).const_mul airySq_c).congr_deriv (by ring), airySq_hasDerivAt_F2' x⟩

/-- Every solution of the product equation is a combination of `Ai², Ai Bi, Bi²`. -/
theorem airySq_decomp {y y1 y2 : ℝ → ℝ} (hy : AirySqIsProdSol y y1 y2) :
    ∃ a b d : ℝ, ∀ x, y x = a * airyAiReal x ^ 2 + b * (airyAiReal x * airyBiReal x) +
      d * airyBiReal x ^ 2 := by
  have hA := hasDerivAt_airyAiReal
  have hA' := hasDerivAt_airyAiDerivReal
  have hB := hasDerivAt_airyBiReal
  have hB' := hasDerivAt_airyBiDerivReal
  have h1 := airySq_isProdSol_mul hA hA' hA hA'
  have h2 := airySq_isProdSol_mul hA hA' hB hB'
  have h3 := airySq_isProdSol_mul hB hB' hB hB'
  have hW : ∀ x, airySq_det (fun x => airyAiReal x * airyAiReal x)
      (fun x => airyAiDerivReal x * airyAiReal x + airyAiReal x * airyAiDerivReal x)
      (fun x => 2 * x * airyAiReal x * airyAiReal x + 2 * airyAiDerivReal x * airyAiDerivReal x)
      (fun x => airyAiReal x * airyBiReal x)
      (fun x => airyAiDerivReal x * airyBiReal x + airyAiReal x * airyBiDerivReal x)
      (fun x => 2 * x * airyAiReal x * airyBiReal x + 2 * airyAiDerivReal x * airyBiDerivReal x)
      (fun x => airyBiReal x * airyBiReal x)
      (fun x => airyBiDerivReal x * airyBiReal x + airyBiReal x * airyBiDerivReal x)
      (fun x => 2 * x * airyBiReal x * airyBiReal x + 2 * airyBiDerivReal x * airyBiDerivReal x) x =
      2 / π ^ 3 := fun x => by
    unfold airySq_det
    have w := wronskian_airyReal x
    calc _ = 2 * (airyAiReal x * airyBiDerivReal x - airyAiDerivReal x * airyBiReal x) ^ 3 := by ring
      _ = _ := by rw [w]; ring
  have hπ : (2 / π ^ 3 : ℝ) ≠ 0 := by have := Real.pi_pos; positivity
  have key := airySq_decomp_gen hy h1 h2 h3 hW hπ
  obtain ⟨a, b, d, hk⟩ : ∃ a b d : ℝ, ∀ x, y x = a * (airyAiReal x * airyAiReal x) +
      b * (airyAiReal x * airyBiReal x) + d * (airyBiReal x * airyBiReal x) := ⟨_, _, _, key⟩
  exact ⟨a, b, d, fun x => (hk x).trans (by ring)⟩

/-- The Mellin value `∫₀^∞ s^{-1/2} Ai(s) ds = √π / (3^{5/6} Γ(5/6))` (DLMF 9.10.17 at `α = 1/2`). -/
theorem airySq_mellin_half :
    ∫ s in Ioi 0, s ^ (-(1 / 2) : ℝ) * airyAiReal s =
      Real.sqrt π / ((3 : ℝ) ^ (5 / 6 : ℝ) * Real.Gamma (5 / 6)) := by
  have h := (airyAi_mellin (α := 1 / 2) (by norm_num)).2
  have e1 : ∀ t ∈ Ioi (0 : ℝ), (t : ℂ) ^ ((1 / 2 : ℂ) - 1) * airyAi t =
      ((t ^ (-(1 / 2) : ℝ) * airyAiReal t : ℝ) : ℂ) := fun t ht => by
    rw [airyAi_ofReal_eq, ofReal_mul, ofReal_cpow (le_of_lt ht)]
    norm_num
  rw [setIntegral_congr_fun measurableSet_Ioi e1, integral_complex_ofReal] at h
  have e2 : Gamma (1 / 2 : ℂ) / ((3 : ℂ) ^ ((1 / 2 + 2) / 3 : ℂ) * Gamma (1 / 2 / 3 + 2 / 3)) =
      ((Real.sqrt π / ((3 : ℝ) ^ (5 / 6 : ℝ) * Real.Gamma (5 / 6)) : ℝ) : ℂ) := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, Complex.Gamma_ofReal,
      Real.Gamma_one_half_eq, show ((1 / 2 : ℝ) : ℂ) / 3 + 2 / 3 = ((5 / 6 : ℝ) : ℂ) by push_cast; ring,
      Complex.Gamma_ofReal, show ((((1 / 2 : ℝ) : ℂ) + 2) / 3 : ℂ) = ((5 / 6 : ℝ) : ℂ) by push_cast; ring,
      show (3 : ℂ) = ((3 : ℝ) : ℂ) by norm_num, ← ofReal_cpow (by norm_num)]
    push_cast; ring
  rw [e2] at h
  exact_mod_cast h

/-- `F(0) = ∫₀^∞ Ai(ct²) dt` through the substitutions `y = t²`, `s = cy`. -/
theorem airySq_F_zero_eq :
    airySq_F 0 = airySq_c ^ (-(1 / 2) : ℝ) / 2 * ∫ s in Ioi 0, s ^ (-(1 / 2) : ℝ) * airyAiReal s := by
  have hc0 := airySq_c_pos
  have h1 := integral_comp_rpow_Ioi_of_pos (g := fun y : ℝ => y ^ (-(1 / 2) : ℝ) / 2 *
    airyAiReal (airySq_c * y)) (p := 2) (by norm_num)
  have e1 : ∀ t ∈ Ioi (0 : ℝ), (2 * t ^ ((2 : ℝ) - 1)) • ((fun y : ℝ => y ^ (-(1 / 2) : ℝ) / 2 *
      airyAiReal (airySq_c * y)) (t ^ (2 : ℝ))) = airyAiReal (airySq_c * (0 + t ^ 2)) := fun t ht => by
    have ht' : 0 < t := ht
    simp only [smul_eq_mul, Real.rpow_two, zero_add]
    rw [← Real.rpow_natCast t 2, ← Real.rpow_mul ht'.le]
    norm_num
    rw [Real.rpow_neg ht'.le, Real.rpow_one]
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioi e1] at h1
  rw [airySq_F, h1]
  have h2 := integral_comp_mul_left_Ioi (fun s : ℝ => (s / airySq_c) ^ (-(1 / 2) : ℝ) / 2 *
    airyAiReal s) 0 hc0
  have e2 : ∀ y ∈ Ioi (0 : ℝ), (fun s : ℝ => (s / airySq_c) ^ (-(1 / 2) : ℝ) / 2 * airyAiReal s)
      (airySq_c * y) = y ^ (-(1 / 2) : ℝ) / 2 * airyAiReal (airySq_c * y) := fun y _ => by
    simp only
    rw [mul_div_cancel_left₀ _ hc0.ne']
  rw [setIntegral_congr_fun measurableSet_Ioi e2, mul_zero] at h2
  rw [h2, smul_eq_mul]
  have e3 : ∀ s ∈ Ioi (0 : ℝ), (s / airySq_c) ^ (-(1 / 2) : ℝ) / 2 * airyAiReal s =
      airySq_c ^ (1 / 2 : ℝ) / 2 * (s ^ (-(1 / 2) : ℝ) * airyAiReal s) := fun s hs => by
    rw [Real.div_rpow (le_of_lt hs) hc0.le, Real.rpow_neg hc0.le]
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioi e3, integral_const_mul]
  have e4 : airySq_c⁻¹ * airySq_c ^ (1 / 2 : ℝ) = airySq_c ^ (-(1 / 2) : ℝ) := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hc0]; norm_num
  rw [← e4]; ring

/-- The normalization `c F(0) = π Ai(0)²`. -/
theorem airySq_F_zero : airySq_c * airySq_F 0 = π * airyAiReal 0 ^ 2 := by
  have hA : airyAiReal 0 = 1 / ((3 : ℝ) ^ (2 / 3 : ℝ) * Real.Gamma (2 / 3)) := by
    have h := airyAi_zero
    rw [Gamma_two_thirds_eq, ← ofReal_mul, ← ofReal_one, ← ofReal_div] at h
    simp [airyAiReal, h]
  rw [airySq_F_zero_eq, airySq_mellin_half, hA]
  have hdup := Real.Gamma_mul_Gamma_add_half (1 / 3)
  have hrefl := airyMod_gamma_third_reflection
  norm_num at hdup
  have hc : airySq_c * airySq_c ^ (-(1 / 2) : ℝ) = (2 : ℝ) ^ (1 / 3 : ℝ) := by
    have hc0 := airySq_c_pos
    rw [show airySq_c * airySq_c ^ (-(1 / 2) : ℝ) = airySq_c ^ (1 : ℝ) * airySq_c ^ (-(1 / 2) : ℝ) by
      rw [Real.rpow_one], ← Real.rpow_add hc0]
    unfold airySq_c
    rw [← Real.rpow_mul (by norm_num)]; norm_num
  have h3 : ((3 : ℝ) ^ (2 / 3 : ℝ)) ^ 2 = (3 : ℝ) ^ (5 / 6 : ℝ) * Real.sqrt 3 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add (by norm_num), ← Real.rpow_natCast,
      ← Real.rpow_mul (by norm_num)]; norm_num
  have hG13 := (Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 1 / 3)).ne'
  have hG23 := (Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 2 / 3)).ne'
  have hG56 := (Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 5 / 6)).ne'
  have hP : (3 : ℝ) ^ (5 / 6 : ℝ) ≠ 0 := by positivity
  have hs3 : Real.sqrt 3 ≠ 0 := by positivity
  rw [show airySq_c * (airySq_c ^ (-(1 / 2) : ℝ) / 2 * (Real.sqrt π / ((3 : ℝ) ^ (5 / 6 : ℝ) *
      Real.Gamma (5 / 6)))) = (airySq_c * airySq_c ^ (-(1 / 2) : ℝ)) * Real.sqrt π /
      (2 * (3 : ℝ) ^ (5 / 6 : ℝ) * Real.Gamma (5 / 6)) by ring, hc, div_pow, mul_pow, h3,
    one_pow, mul_one_div, div_eq_div_iff (mul_ne_zero (mul_ne_zero two_ne_zero hP) hG56)
      (mul_ne_zero (mul_ne_zero hP hs3) (pow_ne_zero 2 hG23))]
  apply mul_left_cancel₀ hG13
  linear_combination ((2 : ℝ) ^ (1 / 3 : ℝ) * Real.sqrt π * Real.Gamma (2 / 3) *
    (3 : ℝ) ^ (5 / 6 : ℝ)) * hrefl - (2 * (3 : ℝ) ^ (5 / 6 : ℝ) * π) * hdup

/-- `|F(x)| ≤ e^{-2x/3} ∫₀^∞ e^{-2t²/3} dt` for `x ≥ 1`. -/
theorem airySq_F_le {x : ℝ} (hx : 1 ≤ x) :
    |airySq_F x| ≤ Real.exp (-(2 / 3) * x) * ∫ t in Ioi 0, Real.exp (-(2 / 3) * t ^ 2) := by
  have hc1 : 1 ≤ airySq_c := Real.one_le_rpow (by norm_num) (by norm_num)
  rw [← integral_const_mul, airySq_F, ← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le
    ((integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 2 / 3)).const_mul _).integrableOn
    (Eventually.of_forall fun t => ?_)
  have hu : x + t ^ 2 ≤ airySq_c * (x + t ^ 2) := by
    nlinarith [sq_nonneg t]
  rw [Real.norm_eq_abs]
  refine (airySq_ai_le (by nlinarith [sq_nonneg t])).trans ?_
  rw [← Real.exp_add]
  exact Real.exp_le_exp.mpr (by nlinarith)

/-- `x^{1/2} F(x) → 0` as `x → +∞`. -/
theorem airySq_tendsto_F : Tendsto (fun x => x ^ (1 / 2 : ℝ) * airySq_F x) atTop (𝓝 0) := by
  have hl := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 / 2) (2 / 3) (by norm_num)).mul_const
    (∫ t in Ioi 0, Real.exp (-(2 / 3) * t ^ 2))
  rw [zero_mul] at hl
  refine squeeze_zero_norm' ?_ hl
  filter_upwards [eventually_ge_atTop 1] with x hx
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity), mul_assoc, neg_mul]
  exact mul_le_mul_of_nonneg_left (by simpa [neg_mul] using airySq_F_le hx) (by positivity)

/-- `x^{1/2} Ai(x)² → 0` as `x → +∞`. -/
theorem airySq_tendsto_ai_sq :
    Tendsto (fun x => x ^ (1 / 2 : ℝ) * airyAiReal x ^ 2) atTop (𝓝 0) := by
  have hl := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 / 2) (4 / 3) (by norm_num)
  refine squeeze_zero_norm' ?_ hl
  filter_upwards [eventually_ge_atTop 1] with x hx
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity), abs_pow]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have h := airySq_ai_le hx
  calc |airyAiReal x| ^ 2 ≤ Real.exp (-(2 / 3) * x) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
    _ = _ := by rw [← Real.exp_nat_mul]; ring_nf

/-- `x^{1/2} Ai(x) Bi(x) → 1/(2π)` as `x → +∞`, from DLMF 9.7.5 and 9.7.7. -/
theorem airySq_tendsto_ai_bi :
    Tendsto (fun x => x ^ (1 / 2 : ℝ) * (airyAiReal x * airyBiReal x)) atTop (𝓝 (1 / (2 * π))) := by
  have hw := IsEquivalent.refl (u := fun x : ℝ => ((x ^ (1 / 2 : ℝ) : ℝ) : ℂ)) (l := atTop)
  have h := hw.mul (airyAi_isEquivalent.mul airyBi_isEquivalent)
  have hv : (fun x : ℝ => ((x ^ (1 / 2 : ℝ) : ℝ) : ℂ)) *
      ((fun x : ℝ => ((Real.exp (-airyZeta x) / (2 * Real.sqrt π * x ^ (1 / 4 : ℝ)) : ℝ) : ℂ)) *
        fun x : ℝ => ((Real.exp (airyZeta x) / (Real.sqrt π * x ^ (1 / 4 : ℝ)) : ℝ) : ℂ)) =ᶠ[atTop]
      fun _ => ((1 / (2 * π) : ℝ) : ℂ) := by
    filter_upwards [eventually_gt_atTop 0] with x hx
    simp only [Pi.mul_apply]
    rw [← ofReal_mul, ← ofReal_mul]
    congr 1
    have hq : x ^ (1 / 4 : ℝ) * x ^ (1 / 4 : ℝ) = x ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_add hx]; norm_num
    have hs := Real.mul_self_sqrt Real.pi_pos.le
    have he : Real.exp (-airyZeta x) * Real.exp (airyZeta x) = 1 := by
      rw [← Real.exp_add]; simp
    have h4 : 0 < x ^ (1 / 4 : ℝ) := by positivity
    have hsp : 0 < Real.sqrt π := Real.sqrt_pos.mpr Real.pi_pos
    calc x ^ (1 / 2 : ℝ) * (Real.exp (-airyZeta x) / (2 * Real.sqrt π * x ^ (1 / 4 : ℝ)) *
          (Real.exp (airyZeta x) / (Real.sqrt π * x ^ (1 / 4 : ℝ)))) =
          x ^ (1 / 2 : ℝ) * (Real.exp (-airyZeta x) * Real.exp (airyZeta x)) /
            (2 * (Real.sqrt π * Real.sqrt π) * (x ^ (1 / 4 : ℝ) * x ^ (1 / 4 : ℝ))) := by ring
      _ = _ := by
        rw [he, hs, hq]
        have : x ^ (1 / 2 : ℝ) ≠ 0 := by positivity
        field_simp
  have ht := (h.congr_right hv).symm.tendsto_nhds tendsto_const_nhds
  have ht' := (continuous_re.tendsto _).comp ht
  simp only [ofReal_re] at ht'
  refine ht'.congr fun x => ?_
  simp [airyAi_ofReal_eq, airyBi_ofReal_eq, ← ofReal_mul]

/-- **Ai² as a Gaussian average of Ai**: `Ai(x)² = (c/π) ∫₀^∞ Ai(c(x+t²)) dt`, `c = 2^{2/3}`. -/
theorem airySq_rep (x : ℝ) : airySq_c * airySq_F x = π * airyAiReal x ^ 2 := by
  obtain ⟨a, b, d, hF⟩ := airySq_decomp airySq_isProdSol_F
  have hq := airySq_tendsto_ai_bi
  have hr := airySq_tendsto_ai_sq
  have hf := airySq_tendsto_F
  have hπ : (1 / (2 * π) : ℝ) ≠ 0 := by have := Real.pi_pos; positivity
  -- `A/B → 0` and `F/B² → 0`
  have hAB : Tendsto (fun x => airyAiReal x / airyBiReal x) atTop (𝓝 0) := by
    have := hr.div hq hπ
    rw [zero_div] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    have h1 := (airyAiReal_pos hx.le).ne'
    have h2 := (airyBiReal_pos hx.le).ne'
    have h3 : x ^ (1 / 2 : ℝ) ≠ 0 := by positivity
    simp only [Pi.div_apply]
    field_simp
  have hFB : Tendsto (fun x => airySq_F x / airyBiReal x ^ 2) atTop (𝓝 0) := by
    have := (hf.mul hr).div (hq.pow 2) (pow_ne_zero 2 hπ)
    rw [zero_mul, zero_div] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    have h1 := (airyAiReal_pos hx.le).ne'
    have h2 := (airyBiReal_pos hx.le).ne'
    have h3 : x ^ (1 / 2 : ℝ) ≠ 0 := by positivity
    simp only [Pi.div_apply]
    field_simp
  have hd : d = 0 := by
    have h2 : Tendsto (fun x => a * (airyAiReal x / airyBiReal x) ^ 2 + b * (airyAiReal x / airyBiReal x) + d) atTop (𝓝 d) := by
      simpa using ((hAB.pow 2).const_mul a).add (hAB.const_mul b) |>.add_const d
    refine tendsto_nhds_unique (h2.congr' ?_) hFB
    filter_upwards [eventually_gt_atTop 0] with x hx
    have h2 := (airyBiReal_pos hx.le).ne'
    rw [hF x]; field_simp
  have hb : b = 0 := by
    have h1 : Tendsto (fun x => a * (airyAiReal x / airyBiReal x) + b) atTop (𝓝 b) := by
      simpa using (hAB.const_mul a).add_const b
    have h2 : Tendsto (fun x => airySq_F x / (airyAiReal x * airyBiReal x)) atTop (𝓝 0) := by
      have := hf.div hq hπ
      rw [zero_div] at this
      refine this.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with x hx
      have h3 : x ^ (1 / 2 : ℝ) ≠ 0 := by positivity
      simp only [Pi.div_apply]
      field_simp
    refine tendsto_nhds_unique (h1.congr' ?_) h2
    filter_upwards [eventually_gt_atTop 0] with x hx
    have h1 := (airyAiReal_pos hx.le).ne'
    have h2 := (airyBiReal_pos hx.le).ne'
    rw [hF x, hd]; field_simp; ring
  have h0 := airySq_F_zero
  rw [hF 0, hb, hd] at h0
  rw [hF x, hb, hd]
  have hA0 := (airyAiReal_pos (le_refl (0 : ℝ))).ne'
  have ha : airySq_c * a = π := by
    have : (airySq_c * a - π) * airyAiReal 0 ^ 2 = 0 := by linear_combination h0
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · exact absurd (pow_eq_zero_iff two_ne_zero |>.mp h) hA0
  linear_combination airyAiReal x ^ 2 * ha

/-- **Ai² as a Gaussian average of Ai**, complex form:
`Ai(x)² = (2^{2/3}/π) ∫₀^∞ Ai(2^{2/3}(x + t²)) dt` for real `x`, with the integral convergent. -/
theorem airyAi_sq_eq_integral (x : ℝ) :
    IntegrableOn (fun t : ℝ => airyAi (((2 : ℝ) ^ (2 / 3 : ℝ) * (x + t ^ 2) : ℝ))) (Ioi 0) ∧
      airyAi x ^ 2 = (((2 : ℝ) ^ (2 / 3 : ℝ) / π : ℝ) : ℂ) *
        ∫ t in Ioi 0, airyAi (((2 : ℝ) ^ (2 / 3 : ℝ) * (x + t ^ 2) : ℝ)) := by
  have e : (fun t : ℝ => airyAi (((2 : ℝ) ^ (2 / 3 : ℝ) * (x + t ^ 2) : ℝ))) =
      fun t : ℝ => ((airyAiReal (airySq_c * (x + t ^ 2)) : ℝ) : ℂ) := by
    funext t; rw [airyAi_ofReal_eq]; rfl
  rw [e, integral_complex_ofReal]
  refine ⟨(airySq_integrable airySq_decay_ai airySq_cont_ai airySq_c_pos x).integrableOn.ofReal, ?_⟩
  have h := airySq_rep x
  rw [airyAi_ofReal_eq, ← airySq_F, ← ofReal_pow, ← ofReal_mul]
  congr 1
  have := Real.pi_pos.ne'
  rw [show (2 : ℝ) ^ (2 / 3 : ℝ) = airySq_c from rfl]
  field_simp
  linarith

/-- The substitution `s = t²`: `F(x) = ½ ∫₀^∞ s^{-1/2} Ai(c(x+s)) ds`. -/
theorem airySq_F_eq_half (x : ℝ) :
    airySq_F x = ∫ s in Ioi 0, s ^ (-(1 / 2) : ℝ) / 2 * airyAiReal (airySq_c * (x + s)) := by
  have h1 := integral_comp_rpow_Ioi_of_pos (g := fun s : ℝ => s ^ (-(1 / 2) : ℝ) / 2 *
    airyAiReal (airySq_c * (x + s))) (p := 2) (by norm_num)
  have e1 : ∀ t ∈ Ioi (0 : ℝ), (2 * t ^ ((2 : ℝ) - 1)) • ((fun s : ℝ => s ^ (-(1 / 2) : ℝ) / 2 *
      airyAiReal (airySq_c * (x + s))) (t ^ (2 : ℝ))) = airyAiReal (airySq_c * (x + t ^ 2)) :=
    fun t ht => by
    have ht' : 0 < t := ht
    simp only [smul_eq_mul, Real.rpow_two]
    rw [← Real.rpow_natCast t 2, ← Real.rpow_mul ht'.le]
    norm_num
    rw [Real.rpow_neg ht'.le, Real.rpow_one]
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioi e1] at h1
  rw [airySq_F, h1]

/-! ### The Mellin transform of `Ai²` (DLMF 9.11.15) -/

/-- Shift of a half-line integral to a whole-line integral with an indicator. -/
theorem airySq_shift {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (g : ℝ → E) (x : ℝ) :
    ∫ s in Ioi 0, g s = ∫ v, (Ioi x).indicator (fun v => g (v - x)) v := by
  rw [← integral_indicator measurableSet_Ioi, ← integral_sub_right_eq_self _ x]
  congr 1; ext v
  simp only [indicator, mem_Ioi, sub_pos]

/-- `|Ai| ≤ K` on `[0, ∞)`. -/
theorem airySq_ai_bdd : ∃ K, ∀ u, 0 ≤ u → |airyAiReal u| ≤ K := by
  obtain ⟨K, hK0, hK⟩ := airySq_decay_ai.ext airySq_cont_ai 0
  refine ⟨K, fun u hu => (hK u hu).trans ?_⟩
  exact mul_le_of_le_one_right hK0 (Real.exp_le_one_iff.mpr (by linarith))

/-- Integrability of `t^{α-1} Ai(t)²` on `(0, ∞)`. -/
theorem airySq_integrableOn_mellin {α : ℂ} (hα : 0 < α.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (α - 1) * airyAi t ^ 2) (Ioi 0) := by
  obtain ⟨K, hK⟩ := airySq_ai_bdd
  have h := (airyAi_mellin hα).1.mul_bdd (c := K) (g := fun t : ℝ => airyAi t)
    (by have := airySq_cont_ai
        exact (continuous_ofReal.comp this).aestronglyMeasurable.congr
          (Eventually.of_forall fun t => (airyAi_ofReal_eq t).symm))
    ((ae_restrict_mem measurableSet_Ioi).mono fun t ht => by
      rw [airyAi_ofReal_eq, norm_real, Real.norm_eq_abs]; exact hK t (le_of_lt ht))
  refine h.congr (Eventually.of_forall fun t => ?_)
  simp only; ring

/-- The kernel of the double integral for the Mellin transform of `Ai²`. -/
def airySq_Φ (α : ℂ) (x v : ℝ) : ℂ :=
  if x < v then (x : ℂ) ^ (α - 1) * ((v : ℂ) - x) ^ ((1 / 2 : ℂ) - 1) *
    ((airyAiReal (airySq_c * v) : ℝ) : ℂ) else 0

/-- The real kernel `s^{-1/2} Ai(c(x+s))` is integrable on `(0, ∞)`. -/
theorem airySq_integrableOn_half (x : ℝ) :
    IntegrableOn (fun s : ℝ => s ^ (-(1 / 2) : ℝ) / 2 * airyAiReal (airySq_c * (x + s))) (Ioi 0) := by
  rw [← integrableOn_Ioi_comp_rpow_iff _ (p := 2) (by norm_num)]
  refine (airySq_integrable airySq_decay_ai airySq_cont_ai airySq_c_pos x).integrableOn.congr_fun
    (fun t ht => ?_) measurableSet_Ioi
  have ht' : 0 < t := ht
  simp only [smul_eq_mul, Real.rpow_two]
  rw [← Real.rpow_natCast t 2, ← Real.rpow_mul ht'.le]
  norm_num
  rw [Real.rpow_neg ht'.le, Real.rpow_one]
  field_simp

/-- Pointwise form: `x^{α-1} Ai(x)² = (c/2π) ∫ Φ(x, v) dv` for `x > 0`. -/
theorem airySq_mellin_pt (α : ℂ) (x : ℝ) :
    (x : ℂ) ^ (α - 1) * airyAi x ^ 2 = ((airySq_c / (2 * π) : ℝ) : ℂ) * ∫ v, airySq_Φ α x v := by
  have e1 : (fun v => airySq_Φ α x v) = fun v => (x : ℂ) ^ (α - 1) * (Ioi x).indicator
      (fun v => ((((v - x) ^ (-(1 / 2) : ℝ) / 2 * airyAiReal (airySq_c * (x + (v - x))) : ℝ) : ℂ))
        * 2) v := by
    funext v
    by_cases hv : x < v
    · simp only [airySq_Φ, hv, ↓reduceIte]
      rw [indicator_of_mem (mem_Ioi.mpr hv), add_sub_cancel,
        ofReal_mul, ofReal_div, ofReal_cpow (sub_nonneg.mpr hv.le)]
      push_cast; ring_nf
    · simp only [airySq_Φ, hv, ↓reduceIte]
      rw [indicator_of_notMem (by simpa using hv), mul_zero]
  rw [e1, integral_const_mul]
  have e2 := airySq_shift (fun s : ℝ => (((s ^ (-(1 / 2) : ℝ) / 2 *
    airyAiReal (airySq_c * (x + s))) : ℝ) : ℂ) * 2) x
  rw [← e2, integral_mul_const, integral_complex_ofReal, ← airySq_F_eq_half,
    airyAi_ofReal_eq]
  have h := airySq_rep x
  have hπ := Real.pi_pos.ne'
  rw [show (airyAiReal x : ℂ) ^ 2 = ((airySq_c / π * airySq_F x : ℝ) : ℂ) by
    rw [← ofReal_pow]; congr 1; field_simp; linarith]
  push_cast
  field_simp

/-- The real kernel `1_{v > x} (v-x)^{-1/2} Ai(cv)`. -/
def airySq_kr (x v : ℝ) : ℝ :=
  (Ioi x).indicator (fun v => (v - x) ^ (-(1 / 2) : ℝ) * airyAiReal (airySq_c * v)) v

/-- The kernel `Φ(α; x, v)` factors as `x^{α-1}` times the real kernel
`1_{v > x}(v-x)^{-1/2} Ai(cv)`. -/
theorem airySq_Φ_eq (α : ℂ) (x v : ℝ) :
    airySq_Φ α x v = (x : ℂ) ^ (α - 1) * ((airySq_kr x v : ℝ) : ℂ) := by
  by_cases hv : x < v
  · simp only [airySq_Φ, airySq_kr, hv, ↓reduceIte]
    rw [indicator_of_mem (mem_Ioi.mpr hv), ofReal_mul, ofReal_cpow (sub_nonneg.mpr hv.le)]
    push_cast; ring_nf
  · simp only [airySq_Φ, airySq_kr, hv, ↓reduceIte]
    rw [indicator_of_notMem (by simpa using hv), ofReal_zero, mul_zero]

/-- The real kernel at `x` is the shift by `x` of `s ↦ 1_{s > 0} s^{-1/2} Ai(c(x+s))`. -/
theorem airySq_kr_shift (x : ℝ) : (fun v => airySq_kr x v) = fun v =>
    (Ioi 0).indicator (fun s => s ^ (-(1 / 2) : ℝ) / 2 * airyAiReal (airySq_c * (x + s)) * 2) (v - x) := by
  funext v
  by_cases hv : x < v
  · rw [airySq_kr, indicator_of_mem (mem_Ioi.mpr hv), indicator_of_mem (mem_Ioi.mpr (sub_pos.mpr hv)),
      add_sub_cancel]
    ring
  · rw [airySq_kr, indicator_of_notMem (by simpa using hv),
      indicator_of_notMem (by simpa using hv)]

/-- The real kernel `v ↦ 1_{v > x}(v-x)^{-1/2} Ai(cv)` is integrable. -/
theorem airySq_kr_integrable (x : ℝ) : Integrable (fun v => airySq_kr x v) := by
  rw [airySq_kr_shift]
  have h := IntegrableOn.integrable_indicator ((airySq_integrableOn_half x).mul_const 2) measurableSet_Ioi
  exact h.comp_sub_right x

/-- `∫ 1_{v > x}(v-x)^{-1/2} Ai(cv) dv = 2 F(x)`. -/
theorem airySq_kr_integral (x : ℝ) : ∫ v, airySq_kr x v = 2 * airySq_F x := by
  have e : (fun v => airySq_kr x v) = fun v => (Ioi x).indicator (fun v =>
      (fun s => s ^ (-(1 / 2) : ℝ) / 2 * airyAiReal (airySq_c * (x + s)) * 2) (v - x)) v := by
    funext v
    simp only [airySq_kr, add_sub_cancel]
    congr 1; funext v; ring
  rw [e, ← airySq_shift (fun s => s ^ (-(1 / 2) : ℝ) / 2 * airyAiReal (airySq_c * (x + s)) * 2) x,
    integral_mul_const, airySq_F_eq_half]
  ring

/-- For `x ≥ 0` the real kernel is nonnegative, since `Ai > 0` on `[0, ∞)`. -/
theorem airySq_kr_nonneg {x : ℝ} (hx : 0 ≤ x) (v : ℝ) : 0 ≤ airySq_kr x v := by
  rw [airySq_kr]
  refine indicator_nonneg (fun v hv => ?_) v
  have hv' : x < v := hv
  exact mul_nonneg (Real.rpow_nonneg (by linarith) _)
    (airyAiReal_pos (mul_nonneg airySq_c_pos.le (by linarith))).le

/-- The kernel `(x, v) ↦ Φ(α; x, v)` is measurable. -/
theorem airySq_Φ_measurable (α : ℂ) : Measurable fun p : ℝ × ℝ => airySq_Φ α p.1 p.2 := by
  unfold airySq_Φ
  refine Measurable.ite (measurableSet_lt measurable_fst measurable_snd) ?_ measurable_const
  have := airySq_cont_ai
  fun_prop

/-- For `Re α > 0`, the kernel `Φ(α; x, v)` is integrable on `(0, ∞) × ℝ`. -/
theorem airySq_Φ_integrable {α : ℂ} (hα : 0 < α.re) :
    Integrable (fun p : ℝ × ℝ => airySq_Φ α p.1 p.2) ((volume.restrict (Ioi 0)).prod volume) := by
  rw [integrable_prod_iff (airySq_Φ_measurable α).aestronglyMeasurable]
  constructor
  · refine Eventually.of_forall fun x => ?_
    simp_rw [airySq_Φ_eq]
    exact (airySq_kr_integrable x).ofReal.const_mul _
  · have hm := (airySq_integrableOn_mellin (α := (α.re : ℂ)) (by simpa using hα)).norm
    have hπ := Real.pi_pos.ne'
    have hc := airySq_c_pos.ne'
    refine IntegrableOn.congr_fun (hm.const_mul (2 * π / airySq_c)) (fun x hx => ?_) measurableSet_Ioi
    have hx' : (0 : ℝ) < x := hx
    simp only [airySq_Φ_eq, norm_mul, norm_real, Real.norm_eq_abs,
      abs_of_nonneg (airySq_kr_nonneg hx'.le _)]
    rw [integral_const_mul, airySq_kr_integral, Complex.norm_cpow_eq_rpow_re_of_pos hx',
      Complex.norm_cpow_eq_rpow_re_of_pos hx', airyAi_ofReal_eq, ← ofReal_pow, norm_real,
      Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    simp only [sub_re, ofReal_re, one_re]
    have h := airySq_rep x
    field_simp
    linear_combination -h

/-- The inner `x`-integral is a Beta integral (DLMF 5.12.1). -/
theorem airySq_inner (α : ℂ) (v : ℝ) :
    ∫ x in Ioi 0, airySq_Φ α x v = (Ioi 0).indicator (fun v : ℝ => betaIntegral α (1 / 2) *
      ((v : ℂ) ^ (α + 1 / 2 - 1) * ((airyAiReal (airySq_c * v) : ℝ) : ℂ))) v := by
  by_cases hv : 0 < v
  · rw [indicator_of_mem (mem_Ioi.mpr hv)]
    have e : ∀ x ∈ Ioi (0 : ℝ), airySq_Φ α x v = (Iio v).indicator (fun x : ℝ => (x : ℂ) ^ (α - 1) *
        ((v : ℂ) - x) ^ ((1 / 2 : ℂ) - 1) * ((airyAiReal (airySq_c * v) : ℝ) : ℂ)) x := fun x _ => by
      by_cases hxv : x < v
      · simp only [airySq_Φ, hxv, ↓reduceIte, indicator_of_mem (mem_Iio.mpr hxv)]
      · simp only [airySq_Φ, hxv, ↓reduceIte]
        rw [indicator_of_notMem (by simpa using hxv)]
    rw [setIntegral_congr_fun measurableSet_Ioi e, setIntegral_indicator measurableSet_Iio,
      Ioi_inter_Iio, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hv.le,
      intervalIntegral.integral_mul_const, betaIntegral_scaled α (1 / 2) hv]
    ring
  · rw [indicator_of_notMem (by simpa using hv)]
    refine (setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_).trans (integral_zero ℝ ℂ)
    have : ¬ x < v := by have : (0 : ℝ) < x := hx; linarith
    simp only [airySq_Φ, this, ↓reduceIte]

/-- Fubini: `∫₀^∞ ∫ Φ(x,v) dv dx = B(α, 1/2) ∫₀^∞ v^{α-1/2} Ai(cv) dv`. -/
theorem airySq_double {α : ℂ} (hα : 0 < α.re) :
    ∫ x in Ioi 0, ∫ v, airySq_Φ α x v = betaIntegral α (1 / 2) *
      ∫ v : ℝ in Ioi 0, (v : ℂ) ^ (α + 1 / 2 - 1) * ((airyAiReal (airySq_c * v) : ℝ) : ℂ) := by
  rw [integral_integral_swap (f := fun x v => airySq_Φ α x v) (airySq_Φ_integrable hα)]
  simp_rw [airySq_inner]
  rw [integral_indicator measurableSet_Ioi, integral_const_mul]

/-- The scaled Mellin transform `∫₀^∞ v^{w-1} Ai(cv) dv = c^{-w} M_Ai(w)` (DLMF 9.10.17). -/
theorem airySq_scaled_mellin {w : ℂ} (hw : 0 < w.re) :
    ∫ v : ℝ in Ioi 0, (v : ℂ) ^ (w - 1) * ((airyAiReal (airySq_c * v) : ℝ) : ℂ) =
      exp (-(Real.log airySq_c : ℂ) * w) *
        (Gamma w / ((3 : ℂ) ^ ((w + 2) / 3) * Gamma (w / 3 + 2 / 3))) := by
  have hc0 := airySq_c_pos
  have h := integral_comp_mul_left_Ioi (fun s : ℝ => ((s / airySq_c : ℝ) : ℂ) ^ (w - 1) *
    ((airyAiReal s : ℝ) : ℂ)) 0 hc0
  have e1 : ∀ v ∈ Ioi (0 : ℝ), (fun s : ℝ => ((s / airySq_c : ℝ) : ℂ) ^ (w - 1) *
      ((airyAiReal s : ℝ) : ℂ)) (airySq_c * v) =
      (v : ℂ) ^ (w - 1) * ((airyAiReal (airySq_c * v) : ℝ) : ℂ) := fun v _ => by
    simp only; rw [mul_div_cancel_left₀ _ hc0.ne']
  rw [setIntegral_congr_fun measurableSet_Ioi e1, mul_zero] at h
  rw [h]
  have e2 : ∀ s ∈ Ioi (0 : ℝ), ((s / airySq_c : ℝ) : ℂ) ^ (w - 1) * ((airyAiReal s : ℝ) : ℂ) =
      exp (-(Real.log airySq_c : ℂ) * (w - 1)) * ((s : ℂ) ^ (w - 1) * airyAi s) := fun s hs => by
    have hs' : (0 : ℝ) < s := hs
    rw [Complex.ofReal_cpow_eq_exp (div_pos hs' hc0), Complex.ofReal_cpow_eq_exp
        hs', Real.log_div hs'.ne' hc0.ne',
      airyAi_ofReal_eq, ← mul_assoc, ← Complex.exp_add]
    push_cast; ring_nf
  rw [setIntegral_congr_fun measurableSet_Ioi e2, integral_const_mul, (airyAi_mellin hw).2,
    real_smul, ← mul_assoc]
  congr 1
  rw [show ((airySq_c⁻¹ : ℝ) : ℂ) = exp (-(Real.log airySq_c : ℂ)) by
    rw [← ofReal_neg, ← ofReal_exp, ← Real.log_inv, Real.exp_log (inv_pos.mpr hc0)],
    ← Complex.exp_add]
  ring_nf

end DLMF.Airy
