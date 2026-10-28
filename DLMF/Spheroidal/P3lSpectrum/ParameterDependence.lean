/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Spheroidal.P3lSpectrum.EntireEigenfunctions

/-!
# Parameter dependence of spheroidal eigenfunctions

Analytic parameter dependence and real-solution properties of spheroidal spectral
eigenfunctions.

Source references and common attribution are retained in
`DLMF.Spheroidal.P3lSpectrum`.
-/

@[expose] public noncomputable section

open Complex Set Filter FormalMultilinearSeries

open scoped Topology ENNReal ContDiff

namespace DLMF.Spheroidal

/-! ### Dependence on the parameter -/

/-- The coefficients are polynomials in `c`. -/
lemma p3lH_differentiable (m : ℕ) (γ2 : ℂ) (k : ℕ) :
    Differentiable ℂ fun c => p3lH m γ2 c k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k, ih with
    | 0, _ => simp only [p3lH]; fun_prop
    | 1, _ => simp only [p3lH]; fun_prop
    | 2, _ => simp only [p3lH]; fun_prop
    | k + 3, ih =>
      have h2 := ih (k + 2) (by omega); have h1 := ih (k + 1) (by omega)
      have h0 := ih k (by omega)
      simp only [p3lH]
      exact ((((differentiable_id.sub_const _).mul h2).sub (h1.const_mul _)).sub
        (h0.const_mul _)).div_const _

/-- The derivative series `∑ (n+1) f_{n+1} uⁿ`. -/
def p3lD (m : ℕ) (γ2 c : ℂ) (u : ℂ) : ℂ := ∑' n : ℕ, ((n : ℂ) + 1) * p3lB m γ2 c (n + 1) * u ^ n

/-- The derivative of the Frobenius series is the derivative series. -/
lemma p3lF_deriv (m : ℕ) (γ2 c : ℂ) {u : ℂ} (hu : ‖u‖ < 5 / 3) :
    deriv (p3lF m γ2 c) u = p3lD m γ2 c u := by
  have hz : u ∈ Metric.eball (0 : ℂ) (ENNReal.ofReal (5 / 3)) := by
    rw [Metric.eball_ofReal, mem_ball_zero_iff]; exact hu
  exact ((p3lF_hasFPowerSeriesOnBall m γ2 c).deriv_ofScalars.hasSum_mul_pow hz).tsum_eq.symm

/-- The derivative of the Frobenius solution. -/
theorem p3lY_deriv (m : ℕ) (γ2 c : ℂ) {z : ℂ} (hz : ‖z - 1‖ < 5 / 3) :
    deriv (p3lY m γ2 c) z = p3lD m γ2 c (z - 1) := by
  rw [show p3lY m γ2 c = fun w => p3lF m γ2 c (w - 1) from rfl, p3lY_hasDerivAt_aux]
  exact p3lF_deriv m γ2 c hz

/-- Summability of `(n+1) rⁿ` for `0 ≤ r < 1`. -/
lemma p3l_summable_succ_geom {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) :
    Summable fun n : ℕ => ((n : ℝ) + 1) * r ^ n := by
  have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 (r := r) (by rwa [Real.norm_of_nonneg hr0])
  have h2 := summable_geometric_of_lt_one hr0 hr
  exact (h1.add h2).congr fun n => by ring

/-- Joint continuity of the Frobenius series and its derivative series in `(c, u)`. -/
lemma p3l_continuousOn_FD (m : ℕ) (γ2 : ℂ) :
    ContinuousOn (fun p : ℂ × ℂ => p3lF m γ2 p.1 p.2) (univ ×ˢ Metric.ball 0 (3 / 2)) ∧
    ContinuousOn (fun p : ℂ × ℂ => p3lD m γ2 p.1 p.2) (univ ×ˢ Metric.ball 0 (3 / 2)) := by
  have key : ∀ p₀ : ℂ × ℂ, p₀ ∈ univ ×ˢ Metric.ball (0 : ℂ) (3 / 2) →
      ContinuousAt (fun p : ℂ × ℂ => p3lF m γ2 p.1 p.2) p₀ ∧
      ContinuousAt (fun p : ℂ × ℂ => p3lD m γ2 p.1 p.2) p₀ := by
    rintro ⟨c₀, u₀⟩ ⟨-, hu₀⟩
    set K := ‖c₀‖ + 1
    obtain ⟨C, hC0, hC⟩ := p3lB_bound m γ2 (by positivity : (0 : ℝ) ≤ K)
    set s : Set (ℂ × ℂ) := Metric.ball 0 K ×ˢ Metric.ball 0 (3 / 2)
    have hs : s ∈ 𝓝 (c₀, u₀) :=
      prod_mem_nhds (Metric.isOpen_ball.mem_nhds (by simp [K])) (Metric.isOpen_ball.mem_nhds hu₀)
    have hb : ∀ p ∈ s, ‖p.1‖ ≤ K ∧ ‖p.2‖ ≤ 3 / 2 := fun p hp =>
      ⟨(mem_ball_zero_iff.1 hp.1).le, (mem_ball_zero_iff.1 hp.2).le⟩
    have hcB : ∀ n, Continuous fun p : ℂ × ℂ => p3lB m γ2 p.1 n :=
      fun n => (p3lH_differentiable m γ2 (n + 2)).continuous.comp continuous_fst
    constructor
    · refine (continuousOn_tsum (u := fun n => C * (9 / 10) ^ n)
        (f := fun n (p : ℂ × ℂ) => p3lB m γ2 p.1 n * p.2 ^ n)
        (fun n => ((hcB n).mul (continuous_snd.pow n)).continuousOn)
        ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left C)
        (fun n p hp => ?_)).continuousAt hs
      obtain ⟨h1, h2⟩ := hb p hp
      rw [norm_mul, norm_pow]
      calc ‖p3lB m γ2 p.1 n‖ * ‖p.2‖ ^ n ≤ C * (3 / 5) ^ n * (3 / 2) ^ n := by
            gcongr; exact hC _ h1 n
        _ = C * (9 / 10) ^ n := by rw [mul_assoc, ← mul_pow]; norm_num
    · refine (continuousOn_tsum (u := fun n : ℕ => C * (((n : ℝ) + 1) * (9 / 10) ^ n))
        (f := fun (n : ℕ) (p : ℂ × ℂ) => ((n : ℂ) + 1) * p3lB m γ2 p.1 (n + 1) * p.2 ^ n)
        (fun n => ((continuous_const.mul (hcB (n + 1))).mul
          (continuous_snd.pow n)).continuousOn)
        ((p3l_summable_succ_geom (by norm_num) (by norm_num)).mul_left C)
        (fun n p hp => ?_)).continuousAt hs
      obtain ⟨h1, h2⟩ := hb p hp
      rw [norm_mul, norm_mul, norm_pow]
      have hn : ‖((n : ℂ) + 1)‖ = (n : ℝ) + 1 := by
        rw [show ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
          Real.norm_of_nonneg (by positivity)]
      rw [hn]
      calc ((n : ℝ) + 1) * ‖p3lB m γ2 p.1 (n + 1)‖ * ‖p.2‖ ^ n
          ≤ ((n : ℝ) + 1) * (C * (3 / 5) ^ (n + 1)) * (3 / 2) ^ n := by
            gcongr; exact hC _ h1 _
        _ ≤ ((n : ℝ) + 1) * (C * (3 / 5) ^ n) * (3 / 2) ^ n := by
            have hp : ((3 : ℝ) / 5) ^ (n + 1) ≤ (3 / 5) ^ n :=
              pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_succ n)
            have := mul_le_mul_of_nonneg_left hp hC0
            have h3 : (0 : ℝ) ≤ (3 / 2) ^ n := by positivity
            have h4 : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this h4) h3
        _ = C * (((n : ℝ) + 1) * (9 / 10) ^ n) := by
            rw [show (9 / 10 : ℝ) = 3 / 5 * (3 / 2) by norm_num, mul_pow]; ring
  exact ⟨fun p hp => (key p hp).1.continuousWithinAt, fun p hp => (key p hp).2.continuousWithinAt⟩

/-- `c ↦ F(c, u)` and `c ↦ D(c, u)` are entire for `‖u‖ ≤ 1`. -/
theorem p3l_differentiable_FD (m : ℕ) (γ2 : ℂ) {u : ℂ} (hu : ‖u‖ ≤ 1) :
    Differentiable ℂ (fun c => p3lF m γ2 c u) ∧ Differentiable ℂ (fun c => p3lD m γ2 c u) := by
  have key : ∀ c₀ : ℂ, DifferentiableAt ℂ (fun c => p3lF m γ2 c u) c₀ ∧
      DifferentiableAt ℂ (fun c => p3lD m γ2 c u) c₀ := by
    intro c₀
    set K := ‖c₀‖ + 1
    obtain ⟨C, hC0, hC⟩ := p3lB_bound m γ2 (by positivity : (0 : ℝ) ≤ K)
    have hs : Metric.ball (0 : ℂ) K ∈ 𝓝 c₀ := Metric.isOpen_ball.mem_nhds (by simp [K])
    have hdB : ∀ n, Differentiable ℂ fun c => p3lB m γ2 c n :=
      fun n => p3lH_differentiable m γ2 (n + 2)
    constructor
    · refine (differentiableOn_tsum_of_summable_norm (u := fun n => C * (3 / 5) ^ n)
        ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left C)
        (fun n => ((hdB n).mul_const _).differentiableOn) Metric.isOpen_ball
        (fun n c hc => ?_)).differentiableAt hs
      rw [norm_mul, norm_pow]
      have h1 := hC c (mem_ball_zero_iff.1 hc).le n
      have : ‖u‖ ^ n ≤ 1 := pow_le_one₀ (norm_nonneg _) hu
      calc ‖p3lB m γ2 c n‖ * ‖u‖ ^ n ≤ C * (3 / 5) ^ n * 1 := by gcongr
        _ = _ := mul_one _
    · refine (differentiableOn_tsum_of_summable_norm
        (u := fun n : ℕ => C * (((n : ℝ) + 1) * (3 / 5) ^ n))
        ((p3l_summable_succ_geom (by norm_num) (by norm_num)).mul_left C)
        (fun n => (((hdB (n + 1)).const_mul _).mul_const _).differentiableOn) Metric.isOpen_ball
        (fun n c hc => ?_)).differentiableAt hs
      rw [norm_mul, norm_mul, norm_pow]
      have hn : ‖((n : ℂ) + 1)‖ = (n : ℝ) + 1 := by
        rw [show ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
          Real.norm_of_nonneg (by positivity)]
      rw [hn]
      have h1 := hC c (mem_ball_zero_iff.1 hc).le (n + 1)
      have : ‖u‖ ^ n ≤ 1 := pow_le_one₀ (norm_nonneg _) hu
      calc ((n : ℝ) + 1) * ‖p3lB m γ2 c (n + 1)‖ * ‖u‖ ^ n
          ≤ ((n : ℝ) + 1) * (C * (3 / 5) ^ (n + 1)) * 1 := by gcongr
        _ ≤ ((n : ℝ) + 1) * (C * (3 / 5) ^ n) * 1 := by
            have hp : ((3 : ℝ) / 5) ^ (n + 1) ≤ (3 / 5) ^ n :=
              pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_succ n)
            have := mul_le_mul_of_nonneg_left hp hC0
            have h4 : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this h4) zero_le_one
        _ = _ := by ring
  exact ⟨fun c => (key c).1, fun c => (key c).2⟩

/-! ### Real parameters: the real solution on `(-2/3, 8/3)` -/

/-- The parameter `c = λ - m(m+1)` as a complex number. -/
def p3lC (m : ℕ) (lam : ℝ) : ℂ := ((lam - (m : ℝ) * (m + 1) : ℝ) : ℂ)

/-- The real Frobenius solution `x ↦ Y(x)` for real `λ`, `γ²`. -/
def p3lyR (m : ℕ) (γr lam x : ℝ) : ℝ := (p3lY m (γr : ℂ) (p3lC m lam) (x : ℂ)).re

/-- Its derivative. -/
def p3lyR' (m : ℕ) (γr lam x : ℝ) : ℝ := (deriv (p3lY m (γr : ℂ) (p3lC m lam)) (x : ℂ)).re

/-- The coefficients are real for real parameters. -/
lemma p3lB_ofReal (m : ℕ) (γr cr : ℝ) (n : ℕ) :
    p3lB m (γr : ℂ) (cr : ℂ) n = ((p3lH m γr cr (n + 2) : ℝ) : ℂ) :=
  (p3lH_map Complex.ofRealHom m γr cr (n + 2)).symm

/-- `‖x - 1‖ = |x - 1|` for real `x`. -/
lemma p3l_norm_ofReal_sub_one {x : ℝ} (hx : |x - 1| < 5 / 3) : ‖(x : ℂ) - 1‖ < 5 / 3 := by
  rw [show (x : ℂ) - 1 = ((x - 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
    Real.norm_eq_abs]; exact hx

/-- The Frobenius solution is real on the real axis for real parameters. -/
theorem p3lY_ofReal (m : ℕ) (γr lam x : ℝ) :
    p3lY m (γr : ℂ) (p3lC m lam) (x : ℂ) = (p3lyR m γr lam x : ℂ) := by
  have e : p3lY m (γr : ℂ) (p3lC m lam) (x : ℂ) =
      ((∑' n, p3lH m γr (lam - (m : ℝ) * (m + 1)) (n + 2) * (x - 1) ^ n : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]
    simp only [p3lY, p3lF, p3lC, p3lB_ofReal]
    push_cast; rfl
  simp only [p3lyR, e, Complex.ofReal_re]

/-- Its derivative is real on the real axis for real parameters. -/
theorem p3lY_deriv_ofReal (m : ℕ) (γr lam : ℝ) {x : ℝ} (hx : |x - 1| < 5 / 3) :
    deriv (p3lY m (γr : ℂ) (p3lC m lam)) (x : ℂ) = (p3lyR' m γr lam x : ℂ) := by
  have e : deriv (p3lY m (γr : ℂ) (p3lC m lam)) (x : ℂ) =
      ((∑' n : ℕ, ((n : ℝ) + 1) * p3lH m γr (lam - (m : ℝ) * (m + 1)) (n + 1 + 2) *
        (x - 1) ^ n : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum, p3lY_deriv _ _ _ (p3l_norm_ofReal_sub_one hx)]
    simp only [p3lD, p3lC, p3lB_ofReal]
    push_cast; rfl
  simp only [p3lyR', e, Complex.ofReal_re]

/-- `y(1) = 1`. -/
theorem p3lyR_one (m : ℕ) (γr lam : ℝ) : p3lyR m γr lam 1 = 1 := by
  simp [p3lyR, p3lY_one]

/-- `y' ` is the derivative of `y`. -/
theorem p3lyR_hasDerivAt (m : ℕ) (γr lam : ℝ) {x : ℝ} (hx : |x - 1| < 5 / 3) :
    HasDerivAt (p3lyR m γr lam) (p3lyR' m γr lam x) x := by
  have hY := p3lY_analyticOnNhd m (γr : ℂ) (p3lC m lam) (x : ℂ)
    (by simpa [dist_eq_norm] using p3l_norm_ofReal_sub_one hx)
  exact hY.differentiableAt.hasDerivAt.real_of_complex

/-- The real equation `((1-x²)^{m+1} y')' = -(λ - m(m+1) + γ²(1-x²)) (1-x²)^m y`. -/
theorem p3lyR_hasDerivAt_flux (m : ℕ) (γr lam : ℝ) {x : ℝ} (hx : |x - 1| < 5 / 3) :
    HasDerivAt (fun t => (1 - t ^ 2) ^ (m + 1) * p3lyR' m γr lam t)
      (-((lam - (m : ℝ) * (m + 1) + γr * (1 - x ^ 2)) * (1 - x ^ 2) ^ m * p3lyR m γr lam x)) x := by
  set Y := p3lY m (γr : ℂ) (p3lC m lam)
  have hxb : (x : ℂ) ∈ Metric.ball (1 : ℂ) (5 / 3) := by
    simpa [dist_eq_norm] using p3l_norm_ofReal_sub_one hx
  have hY := p3lY_analyticOnNhd m (γr : ℂ) (p3lC m lam) (x : ℂ) hxb
  have d2 := hY.deriv.differentiableAt.hasDerivAt
  have hp : HasDerivAt (fun w : ℂ => (1 - w ^ 2) ^ (m + 1))
      (((m + 1 : ℕ) : ℂ) * (1 - (x : ℂ) ^ 2) ^ m * (-(2 * (x : ℂ)))) (x : ℂ) := by
    have := ((hasDerivAt_pow 2 (x : ℂ)).const_sub 1).pow (m + 1)
    convert this using 1; push_cast; ring
  have h := (hp.mul d2).real_of_complex
  have eY := p3lY_sol m (γr : ℂ) (p3lC m lam) (x : ℂ) hxb
  have hfun : (fun t : ℝ => ((1 - (t : ℂ) ^ 2) ^ (m + 1) * deriv Y (t : ℂ)).re) =
      fun t => (1 - t ^ 2) ^ (m + 1) * p3lyR' m γr lam t := by
    funext t
    rw [show (1 - (t : ℂ) ^ 2) ^ (m + 1) = (((1 - t ^ 2) ^ (m + 1) : ℝ) : ℂ) by push_cast; ring,
      Complex.re_ofReal_mul]
    rfl
  simp only [Pi.mul_apply] at h
  rw [hfun] at h
  refine h.congr_deriv ?_
  have e2 : ((m + 1 : ℕ) : ℂ) * (1 - (x : ℂ) ^ 2) ^ m * (-(2 * (x : ℂ))) * deriv Y x +
      (1 - (x : ℂ) ^ 2) ^ (m + 1) * deriv (deriv Y) x =
      (((-((lam - (m : ℝ) * (m + 1) + γr * (1 - x ^ 2)) * (1 - x ^ 2) ^ m)) : ℝ) : ℂ) * Y x := by
    have hc : p3lC m lam = (lam : ℂ) - (m : ℂ) * ((m : ℂ) + 1) := by simp [p3lC]
    push_cast
    linear_combination (1 - (x : ℂ) ^ 2) ^ m * eY - (1 - (x : ℂ) ^ 2) ^ m * Y x * hc
  rw [e2, Complex.re_ofReal_mul]
  simp only [p3lyR, Y]
  ring

/-- Zeros of the real Frobenius solution in `(-1/2, 3/2)` are simple. -/
theorem p3lyR_simple (m : ℕ) (γr lam : ℝ) {x : ℝ} (hx : x ∈ Ioo (-1 / 2 : ℝ) (3 / 2))
    (h0 : p3lyR m γr lam x = 0) : p3lyR' m γr lam x ≠ 0 := by
  intro h1
  have hx' : |x - 1| < 5 / 3 := by rw [abs_lt]; constructor <;> linarith [hx.1, hx.2]
  have hxb : (x : ℂ) ∈ Metric.ball (1 : ℂ) (5 / 3) := by
    simpa [dist_eq_norm] using p3l_norm_ofReal_sub_one hx'
  have hYa := p3lY_analyticOnNhd m (γr : ℂ) (p3lC m lam)
  have hx1 : 1 - (x : ℂ) ^ 2 ≠ 0 := by
    rw [show 1 - (x : ℂ) ^ 2 = ((1 - x ^ 2 : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_ne_zero]
    intro h
    have : (x - 1) * (x + 1) = 0 := by linear_combination -h
    rcases mul_eq_zero.1 this with h | h
    · -- `x = 1`: but `Y(1) = 1`
      have : x = 1 := by linarith
      subst this
      rw [p3lyR_one] at h0; exact one_ne_zero h0
    · linarith [hx.1]
  have hev : p3lY m (γr : ℂ) (p3lC m lam) =ᶠ[𝓝 (x : ℂ)] fun _ => 0 :=
    p3l_eventuallyEq (Metric.isOpen_ball.mem_nhds hxb) hx1 (hYa _ hxb) analyticAt_const
      (p3lY_sol m _ _) (fun z _ => by simp)
      (by rw [p3lY_ofReal, h0]; simp) (by rw [p3lY_deriv_ofReal m γr lam hx', h1]; simp)
  have := hYa.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball _ _).isPreconnected
    hxb hev (Metric.mem_ball_self (by norm_num) : (1 : ℂ) ∈ Metric.ball 1 (5 / 3))
  simp [p3lY_one] at this

/-- Points of `(-1/2, 3/2)` lie within `3/2` of `1`. -/
lemma p3l_abs_sub_one_of_mem {x : ℝ} (hx : x ∈ Ioo (-1 / 2 : ℝ) (3 / 2)) : |x - 1| < 3 / 2 := by
  rw [abs_lt]; constructor <;> linarith [hx.1, hx.2]

/-- Joint continuity of the real solution and its derivative in `(λ, x)`. -/
theorem p3lyR_continuousOn (m : ℕ) (γr : ℝ) :
    ContinuousOn (Function.uncurry (p3lyR m γr)) (univ ×ˢ Ioo (-1 / 2 : ℝ) (3 / 2)) ∧
    ContinuousOn (Function.uncurry (p3lyR' m γr)) (univ ×ˢ Ioo (-1 / 2 : ℝ) (3 / 2)) := by
  obtain ⟨hF, hD⟩ := p3l_continuousOn_FD m (γr : ℂ)
  set φ : ℝ × ℝ → ℂ × ℂ := fun p => (p3lC m p.1, (p.2 : ℂ) - 1)
  have hφ : Continuous φ := by
    simp only [φ, p3lC]; fun_prop
  have hmaps : MapsTo φ (univ ×ˢ Ioo (-1 / 2 : ℝ) (3 / 2)) (univ ×ˢ Metric.ball 0 (3 / 2)) := by
    rintro ⟨l, x⟩ ⟨-, hx⟩
    refine ⟨mem_univ _, ?_⟩
    simp only [φ, mem_ball_zero_iff]
    rw [show (x : ℂ) - 1 = ((x - 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs]
    exact p3l_abs_sub_one_of_mem hx
  constructor
  · exact Complex.continuous_re.comp_continuousOn (hF.comp hφ.continuousOn hmaps)
  · refine (Complex.continuous_re.comp_continuousOn (hD.comp hφ.continuousOn hmaps)).congr ?_
    rintro ⟨l, x⟩ ⟨-, hx⟩
    have hx' : ‖(x : ℂ) - 1‖ < 5 / 3 := p3l_norm_ofReal_sub_one (by
      linarith [p3l_abs_sub_one_of_mem hx])
    simp only [Function.uncurry_apply_pair, p3lyR', Function.comp_apply, φ]
    rw [p3lY_deriv _ _ _ hx']

/-- **Lower bound.** For `λ - m(m+1) < -|γ²|`, `Y(0) Y'(0) ≠ 0`. -/
theorem p3lyR_lower (m : ℕ) (γr lam : ℝ) (hc : lam - (m : ℝ) * (m + 1) < -|γr|) :
    p3lyR m γr lam 0 * p3lyR' m γr lam 0 ≠ 0 := by
  set y := p3lyR m γr lam
  set y' := p3lyR' m γr lam
  set q : ℝ → ℝ := fun t => (lam - (m : ℝ) * (m + 1) + γr * (1 - t ^ 2)) * (1 - t ^ 2) ^ m
  set ψ : ℝ → ℝ := fun t => y t * ((1 - t ^ 2) ^ (m + 1) * y' t)
  have hI : ∀ t ∈ Icc (0 : ℝ) 1, |t - 1| < 5 / 3 := fun t ht => by
    rw [abs_lt]; constructor <;> linarith [ht.1, ht.2]
  have hψ : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt ψ ((1 - t ^ 2) ^ (m + 1) * y' t ^ 2 - q t * y t ^ 2) t := by
    intro t ht
    have := (p3lyR_hasDerivAt m γr lam (hI t ht)).mul (p3lyR_hasDerivAt_flux m γr lam (hI t ht))
    exact this.congr_deriv (by simp only [q, y, y']; ring)
  have hq : ∀ t ∈ Icc (0 : ℝ) 1, q t ≤ 0 := by
    intro t ht
    have h1 : 0 ≤ 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
    have h2 : 1 - t ^ 2 ≤ 1 := by nlinarith
    have h3 : lam - (m : ℝ) * (m + 1) + γr * (1 - t ^ 2) < 0 := by
      have : γr * (1 - t ^ 2) ≤ |γr| := by
        calc γr * (1 - t ^ 2) ≤ |γr| * (1 - t ^ 2) := by gcongr; exact le_abs_self γr
          _ ≤ |γr| * 1 := by gcongr
          _ = |γr| := mul_one _
      linarith
    exact mul_nonpos_of_nonpos_of_nonneg h3.le (pow_nonneg h1 m)
  have hmono : MonotoneOn ψ (Icc 0 1) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 1)
      (fun t ht => (hψ t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hψ t (interior_subset ht)).differentiableAt.differentiableWithinAt)
      (fun t ht => ?_)
    rw [(hψ t (interior_subset ht)).deriv]
    have ht' := interior_subset ht
    have h1 : 0 ≤ 1 - t ^ 2 := by nlinarith [ht'.1, ht'.2]
    have := hq t ht'
    have : 0 ≤ (1 - t ^ 2) ^ (m + 1) * y' t ^ 2 := by positivity
    nlinarith [sq_nonneg (y t)]
  intro h0
  have hψ0 : ψ 0 = 0 := by simp only [ψ]; norm_num; exact mul_eq_zero.1 h0
  have hψ1 : ψ 1 = 0 := by simp [ψ]
  have hzero : ∀ t ∈ Icc (0 : ℝ) 1, ψ t = 0 := fun t ht =>
    le_antisymm (hψ1 ▸ hmono ht ⟨zero_le_one, le_rfl⟩ ht.2)
      (hψ0 ▸ hmono ⟨le_rfl, zero_le_one⟩ ht ht.1)
  have hm : (1 / 2 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hev : ψ =ᶠ[𝓝 (1 / 2 : ℝ)] fun _ => 0 := by
    filter_upwards [Icc_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)]
      with t ht using hzero t ht
  have hd0 := (hψ _ hm).unique ((hasDerivAt_const (1 / 2 : ℝ) (0 : ℝ)).congr_of_eventuallyEq hev)
  have hq' : q (1 / 2) < 0 := by
    simp only [q]
    have : γr * (1 - (1 / 2) ^ 2) ≤ |γr| := by
      calc γr * (1 - (1 / 2 : ℝ) ^ 2) ≤ |γr| * (1 - (1 / 2) ^ 2) := by
            gcongr; exact le_abs_self γr
        _ ≤ |γr| := by nlinarith [abs_nonneg γr]
    exact mul_neg_of_neg_of_pos (by linarith) (by positivity)
  have hA : 0 ≤ (1 - (1 / 2 : ℝ) ^ 2) ^ (m + 1) * y' (1 / 2) ^ 2 := by positivity
  have hB : 0 ≤ -q (1 / 2) * y (1 / 2) ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  have hy : y (1 / 2) = 0 := by
    have : -q (1 / 2) * y (1 / 2) ^ 2 = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · exact pow_eq_zero_iff (by norm_num) |>.1 h
  have hy' : y' (1 / 2) = 0 := by
    have : (1 - (1 / 2 : ℝ) ^ 2) ^ (m + 1) * y' (1 / 2) ^ 2 = 0 := by
      rw [hy] at hd0; linarith
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h (by positivity)
    · exact pow_eq_zero_iff (by norm_num) |>.1 h
  exact p3lyR_simple m γr lam (by norm_num) hy hy'

/-- The clamped reciprocal weight `1/(1-x²)^{m+1}`, continuous on `ℝ`. -/
def p3lRho (m : ℕ) (t : ℝ) : ℝ := 1 / (1 - (max (-3 / 4) (min t (3 / 4))) ^ 2) ^ (m + 1)

/-- The denominator of the clamped weight lies in `(0, 1]`. -/
lemma p3lRho_den (m : ℕ) (t : ℝ) :
    0 < (1 - (max (-3 / 4 : ℝ) (min t (3 / 4))) ^ 2) ^ (m + 1) ∧
      (1 - (max (-3 / 4 : ℝ) (min t (3 / 4))) ^ 2) ^ (m + 1) ≤ 1 := by
  set u := max (-3 / 4 : ℝ) (min t (3 / 4))
  have h1 : -3 / 4 ≤ u := le_max_left _ _
  have h2 : u ≤ 3 / 4 := max_le (by norm_num) (min_le_right _ _)
  have h3 : 0 < 1 - u ^ 2 := by nlinarith
  exact ⟨by positivity, pow_le_one₀ h3.le (by nlinarith)⟩

/-- The clamped weight is continuous. -/
lemma p3lRho_continuous (m : ℕ) : Continuous (p3lRho m) := by
  unfold p3lRho
  exact continuous_const.div (by fun_prop) fun t => (p3lRho_den m t).1.ne'

/-- The clamped weight is at least `1`. -/
lemma p3lRho_ge_one (m : ℕ) (t : ℝ) : 1 ≤ p3lRho m t := by
  obtain ⟨h1, h2⟩ := p3lRho_den m t
  unfold p3lRho
  rw [le_div_iff₀ h1]; linarith

/-- On `(-3/4, 3/4)` the clamped weight is `1/(1-t²)^{m+1}`. -/
lemma p3lRho_eq {m : ℕ} {t : ℝ} (ht : t ∈ Ioo (-3 / 4 : ℝ) (3 / 4)) :
    p3lRho m t * (1 - t ^ 2) ^ (m + 1) = 1 := by
  have e : max (-3 / 4 : ℝ) (min t (3 / 4)) = t := by
    rw [min_eq_left ht.2.le, max_eq_right ht.1.le]
  have : 0 < 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
  unfold p3lRho
  rw [e]; field_simp

/-- **Many zeros for large `λ`** (Sturm comparison with `sin(ω s(x))`, `s' = 1/(1-x²)^{m+1}`):
`J` zeros of the real Frobenius solution in `(0, 1/2)`. -/
lemma p3lyR_many_zeros (m : ℕ) (γr lam : ℝ) {J : ℕ} (hJ : 1 ≤ J)
    (hlam : |γr| + (2 * J * Real.pi) ^ 2 * (4 / 3) ^ (2 * m + 1) < lam - (m : ℝ) * (m + 1)) :
    ∃ z : Fin J → ℝ, StrictMono z ∧ (∀ j, z j ∈ Ioo (0 : ℝ) (1 / 2)) ∧
      ∀ j, p3lyR m γr lam (z j) = 0 := by
  set ρ := p3lRho m
  have hρc := p3lRho_continuous m
  set sR : ℝ → ℝ := fun x => ∫ t in (0 : ℝ)..x, ρ t
  have hs : ∀ x, HasDerivAt sR (ρ x) x := fun x => (hρc.integral_hasStrictDerivAt 0 x).hasDerivAt
  have hsc : Continuous sR := continuous_iff_continuousAt.2 fun x => (hs x).continuousAt
  have hsm : StrictMono sR := strictMono_of_hasDerivAt_pos hs
    (fun x => lt_of_lt_of_le one_pos (p3lRho_ge_one m x))
  have hs0 : sR 0 = 0 := by simp [sR]
  have hshalf : 1 / 2 ≤ sR (1 / 2) := by
    have := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (intervalIntegrable_const :
        IntervalIntegrable (fun _ => (1 : ℝ)) MeasureTheory.volume 0 (1 / 2))
      (hρc.intervalIntegrable 0 (1 / 2))
      (fun t _ => p3lRho_ge_one m t)
    simpa [sR] using this
  set w0 : ℝ := 2 * J * Real.pi
  have hJ' : (1 : ℝ) ≤ J := by exact_mod_cast hJ
  have hω : 0 < w0 := by positivity
  -- the points where `w0 s(x) = jπ`
  have hpt : ∀ j : ℕ, j ≤ J → ∃ x ∈ Icc (0 : ℝ) (1 / 2), sR x = j / (2 * J) := by
    intro j hj
    have hjJ : (j : ℝ) ≤ J := by exact_mod_cast hj
    refine intermediate_value_Icc (by norm_num) hsc.continuousOn ⟨?_, ?_⟩
    · rw [hs0]; positivity
    · refine le_trans ?_ hshalf
      rw [div_le_iff₀ (by positivity)]; linarith
  choose! xs hxs hsx using hpt
  have hxmono : ∀ i j : ℕ, i ≤ J → j ≤ J → i < j → xs i < xs j := by
    intro i j hi hj hij
    rw [← hsm.lt_iff_lt, hsx i hi, hsx j hj]
    have : (i : ℝ) < j := by exact_mod_cast hij
    gcongr
  have hωs : ∀ j : ℕ, j ≤ J → w0 * sR (xs j) = j * Real.pi := by
    intro j hj
    rw [hsx j hj]; simp only [w0]; field_simp
  set P : ℝ → ℝ := fun t => (1 - t ^ 2) ^ (m + 1)
  set u : ℝ → ℝ := fun t => Real.sin (w0 * sR t)
  set u' : ℝ → ℝ := fun t => w0 * Real.cos (w0 * sR t) * ρ t
  have hu : ∀ x, HasDerivAt u (u' x) x := fun x =>
    (((hs x).const_mul w0).sin).congr_deriv (by simp only [u']; ring)
  have hpu : ∀ x ∈ Icc (0 : ℝ) (1 / 2),
      HasDerivAt (fun t => P t * u' t) (-((w0 ^ 2 * ρ x) * u x)) x := by
    intro x hx
    have hev : (fun t => w0 * Real.cos (w0 * sR t)) =ᶠ[𝓝 x] fun t => P t * u' t := by
      filter_upwards [Ioo_mem_nhds (show (-3 / 4 : ℝ) < x by linarith [hx.1])
        (show x < 3 / 4 by linarith [hx.2])] with t ht
      simp only [P, u']
      have := p3lRho_eq (m := m) ht
      simp only [ρ] at this ⊢
      linear_combination (-(w0 * Real.cos (w0 * sR t))) * this
    have := (((hs x).const_mul w0).cos).const_mul w0
    refine (this.congr_of_eventuallyEq hev.symm).congr_deriv ?_
    simp only [u]; ring
  have hv := fun x (hx : x ∈ Icc (0 : ℝ) (1 / 2)) => p3lyR_hasDerivAt m γr lam (x := x) (by
    rw [abs_lt]; constructor <;> linarith [hx.1, hx.2])
  have hpv := fun x (hx : x ∈ Icc (0 : ℝ) (1 / 2)) => p3lyR_hasDerivAt_flux m γr lam (x := x) (by
    rw [abs_lt]; constructor <;> linarith [hx.1, hx.2])
  have hzero : ∀ j : ℕ, j < J → ∃ x ∈ Ioo (xs j) (xs (j + 1)), p3lyR m γr lam x = 0 := by
    intro j hj
    have hab := hxmono j (j + 1) hj.le hj (Nat.lt_succ_self j)
    have hsub : Icc (xs j) (xs (j + 1)) ⊆ Icc (0 : ℝ) (1 / 2) := fun x hx =>
      ⟨(hxs j hj.le).1.trans hx.1, hx.2.trans (hxs (j + 1) hj).2⟩
    refine ODE.sturm_comparison_strict (p := P) (q₁ := fun x => w0 ^ 2 * ρ x)
      (q₂ := fun x => (lam - (m : ℝ) * (m + 1) + γr * (1 - x ^ 2)) * (1 - x ^ 2) ^ m)
      (u := u) (u' := u') (v := p3lyR m γr lam) (v' := p3lyR' m γr lam) hab
      (fun x _ => hu x) (fun x hx => hpu x (hsub hx)) (fun x hx => hv x (hsub hx))
      (fun x hx => hpv x (hsub hx)) ?_ ?_ (fun x hx => ?_) ?_ ?_ (fun x hx => ?_)
    · have := hxs j hj.le
      simp only [P]; apply pow_nonneg; nlinarith [this.1, this.2]
    · have := hxs (j + 1) hj
      simp only [P]; apply pow_nonneg; nlinarith [this.1, this.2]
    · have hx' := hsub (Ioo_subset_Icc_self hx)
      have hx0 : (0 : ℝ) < 1 - x ^ 2 := by nlinarith [hx'.1, hx'.2]
      have h34 : (3 / 4 : ℝ) ≤ 1 - x ^ 2 := by nlinarith [hx'.1, hx'.2]
      have hρx := p3lRho_eq (m := m) (t := x) ⟨by linarith [hx'.1], by linarith [hx'.2]⟩
      have hPpos : 0 < (1 - x ^ 2) ^ (m + 1) := by positivity
      show w0 ^ 2 * ρ x < _
      have hρ' : ρ x = 1 / (1 - x ^ 2) ^ (m + 1) := by
        rw [eq_div_iff hPpos.ne']; exact hρx
      rw [hρ', ← sub_pos]
      have hcoef : lam - (m : ℝ) * (m + 1) + γr * (1 - x ^ 2) ≥ lam - (m : ℝ) * (m + 1) - |γr| := by
        have : -(|γr|) ≤ γr * (1 - x ^ 2) := by
          have h1 : 1 - x ^ 2 ≤ 1 := by nlinarith
          have := neg_abs_le γr
          nlinarith [abs_nonneg γr, abs_mul_abs_self γr, le_abs_self γr]
        linarith
      have hpow : (3 / 4 : ℝ) ^ (2 * m + 1) ≤ (1 - x ^ 2) ^ (2 * m + 1) := by gcongr
      have hkey : w0 ^ 2 < (1 - x ^ 2) ^ (2 * m + 1) *
          (lam - (m : ℝ) * (m + 1) + γr * (1 - x ^ 2)) := by
        have h43 : (4 / 3 : ℝ) ^ (2 * m + 1) * (3 / 4) ^ (2 * m + 1) = 1 := by
          rw [← mul_pow]; norm_num
        have hpos : 0 < (3 / 4 : ℝ) ^ (2 * m + 1) := by positivity
        have hc1 : (2 * J * Real.pi) ^ 2 * (4 / 3) ^ (2 * m + 1) <
            lam - (m : ℝ) * (m + 1) - |γr| := by linarith
        calc w0 ^ 2 = (2 * J * Real.pi) ^ 2 * (4 / 3) ^ (2 * m + 1) * (3 / 4) ^ (2 * m + 1) := by
              rw [mul_assoc, h43, mul_one]
          _ < (lam - (m : ℝ) * (m + 1) - |γr|) * (3 / 4) ^ (2 * m + 1) := by gcongr
          _ ≤ (lam - (m : ℝ) * (m + 1) + γr * (1 - x ^ 2)) * (1 - x ^ 2) ^ (2 * m + 1) := by
              have : (0 : ℝ) ≤ (2 * J * Real.pi) ^ 2 * (4 / 3) ^ (2 * m + 1) := by positivity
              gcongr
              · linarith
          _ = _ := by ring
      have e : (lam - (m : ℝ) * (m + 1) + γr * (1 - x ^ 2)) * (1 - x ^ 2) ^ m -
          w0 ^ 2 * (1 / (1 - x ^ 2) ^ (m + 1)) =
          ((1 - x ^ 2) ^ (2 * m + 1) * (lam - (m : ℝ) * (m + 1) + γr * (1 - x ^ 2)) - w0 ^ 2) /
            (1 - x ^ 2) ^ (m + 1) := by
        field_simp; ring
      rw [e]
      exact div_pos (by linarith) hPpos
    · show Real.sin (w0 * sR (xs j)) = 0
      rw [hωs j hj.le]; exact Real.sin_nat_mul_pi j
    · show Real.sin (w0 * sR (xs (j + 1))) = 0
      rw [hωs (j + 1) hj]; exact_mod_cast Real.sin_nat_mul_pi (j + 1)
    · show Real.sin (w0 * sR x) ≠ 0
      intro hsin
      obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.1 hsin
      have h1 : w0 * sR (xs j) < w0 * sR x := by gcongr; exact hsm hx.1
      have h2 : w0 * sR x < w0 * sR (xs (j + 1)) := by gcongr; exact hsm hx.2
      rw [hωs j hj.le, ← hn] at h1; rw [hωs (j + 1) hj, ← hn] at h2
      have h1' : (j : ℝ) < n := lt_of_mul_lt_mul_right h1 Real.pi_pos.le
      have h2' : (n : ℝ) < ((j + 1 : ℕ) : ℝ) := lt_of_mul_lt_mul_right h2 Real.pi_pos.le
      have e1 : (j : ℤ) < n := by exact_mod_cast h1'
      have e2 : n < ((j + 1 : ℕ) : ℤ) := by exact_mod_cast h2'
      push_cast at e2
      omega
  choose! zs hzs hz0 using hzero
  refine ⟨fun j => zs j, fun i j hij => ?_, fun j => ⟨?_, ?_⟩, fun j => hz0 j j.2⟩
  · have hij' : (i : ℕ) < j := hij
    have h1 := (hzs i i.2).2
    have h2 := (hzs j j.2).1
    rcases Nat.lt_or_ge ((i : ℕ) + 1) j with h | h
    · exact h1.trans ((hxmono _ _ (by omega) (by omega) h).trans h2)
    · have : (i : ℕ) + 1 = j := by omega
      rw [this] at h1; exact h1.trans h2
  · have := (hxs j (by omega)).1
    linarith [(hzs j j.2).1]
  · have h1 := (hzs j j.2).2
    have h2 : xs (j + 1) ≤ 1 / 2 := (hxs (j + 1) (by omega)).2
    have h3 : xs (j + 1) ≠ 1 / 2 ∨ xs (j + 1) = 1 / 2 := by tauto
    linarith

/-- Points of `(-1/2, 3/2)` lie within `5/3` of `1`. -/
lemma p3l_abs_lt_of_mem {x : ℝ} (hx : x ∈ Ioo (-1 / 2 : ℝ) (3 / 2)) : |x - 1| < 5 / 3 := by
  have := p3l_abs_sub_one_of_mem hx; linarith

/-- **Odd eigenvalues are unbounded** (Sturm oscillation and deformation): `Y(0) = 0` for
arbitrarily large `λ`. -/
lemma p3l_exists_odd_zero (m : ℕ) (γr Λ₀ : ℝ) : ∃ lam > Λ₀, p3lyR m γr lam 0 = 0 := by
  by_contra hcon
  push Not at hcon
  set U := Ioo (-1 / 2 : ℝ) (3 / 2)
  have hab : Icc (0 : ℝ) 1 ⊆ U := fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  obtain ⟨hcY, hcY'⟩ := p3lyR_continuousOn m γr
  have hd : ∀ t ∈ (univ : Set ℝ), ∀ x ∈ U, HasDerivAt (p3lyR m γr t) (p3lyR' m γr t x) x :=
    fun t _ x hx => p3lyR_hasDerivAt m γr t (p3l_abs_lt_of_mem hx)
  have hs : ∀ t ∈ (univ : Set ℝ), ∀ x ∈ U, p3lyR m γr t x = 0 → p3lyR' m γr t x ≠ 0 :=
    fun t _ x hx h0 => p3lyR_simple m γr t hx h0
  have hconst : ∀ l ∈ Ioi Λ₀,
      {x | x ∈ Icc (0 : ℝ) 1 ∧ p3lyR m γr l x = 0}.ncard =
        {x | x ∈ Icc (0 : ℝ) 1 ∧ p3lyR m γr (Λ₀ + 1) x = 0}.ncard := fun l hl =>
    ODE.sturmDef_ncard_eq_of_isPreconnected (Λ := univ) isOpen_univ isOpen_Ioo hab hcY hcY' hd hs
      isPreconnected_Ioi (subset_univ _)
      (fun t ht => ⟨hcon t ht, by rw [p3lyR_one]; exact one_ne_zero⟩) hl
      (show Λ₀ + 1 ∈ Ioi Λ₀ by simp)
  set n₀ := {x | x ∈ Icc (0 : ℝ) 1 ∧ p3lyR m γr (Λ₀ + 1) x = 0}.ncard
  set J := n₀ + 1
  set l₂ := max (Λ₀ + 1)
    ((m : ℝ) * (m + 1) + |γr| + (2 * J * Real.pi) ^ 2 * (4 / 3) ^ (2 * m + 1) + 1)
  have hl₂ : l₂ ∈ Ioi Λ₀ := by
    simp only [mem_Ioi, l₂]; exact lt_max_of_lt_left (by linarith)
  obtain ⟨z, hz, hzI, hz0⟩ := p3lyR_many_zeros m γr l₂ (J := J) (by omega) (by
    have := le_max_right (Λ₀ + 1)
      ((m : ℝ) * (m + 1) + |γr| + (2 * J * Real.pi) ^ 2 * (4 / 3) ^ (2 * m + 1) + 1)
    linarith)
  have hfin : {x | x ∈ Icc (0 : ℝ) 1 ∧ p3lyR m γr l₂ x = 0}.Finite :=
    ODE.sturmDef_finite (fun x hx => hd l₂ trivial x (hab hx))
      (fun x hx => hs l₂ trivial x (hab hx))
  have hle := ODE.p2l_le_ncard_of_strictMono (P := fun x => x ∈ Icc (0 : ℝ) 1 ∧
    p3lyR m γr l₂ x = 0) hz (fun j => ⟨⟨(hzI j).1.le, by linarith [(hzI j).2]⟩, hz0 j⟩) hfin
  rw [hconst l₂ hl₂] at hle
  omega

/-- The spectrum of the factor equation with real parameters. -/
def p3lSpec (m : ℕ) (γr : ℝ) : Set ℝ :=
  {lam | ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ p3lSol m (γr : ℂ) (p3lC m lam) univ g ∧ g ≠ 0}

/-- `Y(0) Y'(0)` is the real number `y(0) y'(0)`. -/
theorem p3lY_zero_eq (m : ℕ) (γr lam : ℝ) :
    p3lY m (γr : ℂ) (p3lC m lam) 0 * deriv (p3lY m (γr : ℂ) (p3lC m lam)) 0 =
      ((p3lyR m γr lam 0 * p3lyR' m γr lam 0 : ℝ) : ℂ) := by
  have h1 := p3lY_ofReal m γr lam 0
  have h2 := p3lY_deriv_ofReal m γr lam (x := 0) (by norm_num)
  push_cast at h1 h2 ⊢
  rw [h1, h2]

/-- The spectrum is infinite. -/
theorem p3lSpec_infinite (m : ℕ) (γr : ℝ) : (p3lSpec m γr).Infinite := by
  intro hfin
  obtain ⟨M, hM⟩ := hfin.bddAbove
  obtain ⟨lam, hlam, h0⟩ := p3l_exists_odd_zero m γr M
  have hmem : lam ∈ p3lSpec m γr := by
    refine p3l_exists_entire ?_
    rw [p3lY_zero_eq, h0, zero_mul, Complex.ofReal_zero]
  exact absurd (hM hmem) (not_le.2 hlam)

/-- The spectrum meets every `(-∞, x)` in a finite set (lower bound and analyticity in `λ`). -/
theorem p3lSpec_Iio_finite (m : ℕ) (γr x : ℝ) : (p3lSpec m γr ∩ Iio x).Finite := by
  set L₀ := (m : ℝ) * (m + 1) - |γr|
  set g : ℝ → ℝ := fun lam => p3lyR m γr lam 0 * p3lyR' m γr lam 0
  set Gc : ℂ → ℂ := fun w => p3lF m (γr : ℂ) (w - (m : ℂ) * ((m : ℂ) + 1)) (-1) *
    p3lD m (γr : ℂ) (w - (m : ℂ) * ((m : ℂ) + 1)) (-1)
  have hGc : Differentiable ℂ Gc := by
    obtain ⟨h1, h2⟩ := p3l_differentiable_FD m (γr : ℂ) (u := -1) (by simp)
    exact (h1.comp (differentiable_id.sub_const _)).mul (h2.comp (differentiable_id.sub_const _))
  have hGg : ∀ lam : ℝ, Gc lam = (g lam : ℂ) := by
    intro lam
    rw [← p3lY_zero_eq, p3lY_deriv _ _ _ (by norm_num)]
    simp only [Gc, p3lY, p3lC]
    push_cast
    ring_nf
  have hgre : g = fun t : ℝ => (Gc t).re := funext fun t => by rw [hGg]; simp
  have hg : ∀ t, AnalyticAt ℝ g t := fun t => hgre ▸ ODE.p2s_analyticAt_re hGc t
  have hlow : ∀ lam, lam < L₀ → g lam ≠ 0 := fun lam hl =>
    p3lyR_lower m γr lam (by simp only [L₀] at hl; linarith)
  refine (ODE.p2s_finite_zeros_Icc hg (hlow (L₀ - 1) (by linarith)) L₀ x).subset ?_
  rintro lam ⟨⟨G, hGd, hGs, hGne⟩, hlx⟩
  have h := p3l_Y_mul_deriv_eq_zero hGd hGs hGne
  rw [p3lY_zero_eq, Complex.ofReal_eq_zero] at h
  refine ⟨⟨?_, le_of_lt hlx⟩, h⟩
  by_contra hl
  exact hlow lam (not_le.1 hl) h

end DLMF.Spheroidal

end
