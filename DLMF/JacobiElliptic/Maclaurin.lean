/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.JacobiElliptic.JacobiODE

/-!
# Maclaurin series of the Jacobian elliptic functions (DLMF §22.10)

The initial Maclaurin coefficients of `sn, cn, dn` in `z`, the convergence of the full
expansions, and the expansions in `k` and in `k'` (DLMF §22.10).

## Main results

* `jacobiSn_isBigO_maclaurin`, `jacobiCn_isBigO_maclaurin`, `jacobiDn_isBigO_maclaurin`:
  DLMF 22.10.1–22.10.3, as big-O statements at `z = 0`, for complex
  `k ∈ jacobiModulusDomain`.
* `jacobi_hasFPowerSeriesOnBall`: the full expansions converge in the disc `|z| < min(K, K')`
  (prose of DLMF §22.10(i)), stated for `0 < k < 1` as the existence of a power series on that
  ball.
* `jacobiSn_isBigO_small_modulus`, `jacobiCn_isBigO_small_modulus`,
  `jacobiDn_isBigO_small_modulus`: the expansions DLMF 22.10.4–22.10.6 as `k → 0`.
* `jacobiSn_isBigO_small_comodulus`, `jacobiCn_isBigO_small_comodulus`,
  `jacobiDn_isBigO_small_comodulus`: the expansions DLMF 22.10.7–22.10.9 as `k → 1`.

## Implementation notes

The expansions in `k` and `k'` are for fixed complex `z`, with `k` tending to its limit inside
`jacobiModulusDomain`; in 22.10.7–22.10.9 `cosh z ≠ 0` is assumed (`sech z` appears).
DLMF 22.10.1–22.10.3 are proved by bootstrapping the system `sn' = cn dn`, `cn' = -sn dn`,
`dn' = -k² sn cn` against the Maclaurin polynomials, and the radius statement from the absence
of poles in `|z| < K'`. The coefficients have been checked numerically (mpmath), also for
complex `k`.
-/

@[expose] public section

open Complex Asymptotics Filter DLMF.Elliptic
open scoped Topology NNReal ENNReal

noncomputable section

namespace DLMF.JacobiElliptic

variable {k : ℂ}

/-! ### §22.10(i): Maclaurin series in `z` -/

/-- Bootstrapping the Maclaurin coefficients of a solution of the Jacobi system
`s' = cd, c' = -sd, d' = -κsc` from polynomial approximations. -/
private lemma jacobiSystem_isBigO_of_approx {s c d S C D S' C' D' : ℂ → ℂ} {κ : ℂ}
    (hs : ∀ᶠ z in 𝓝 0, HasDerivAt s (c z * d z) z)
    (hc : ∀ᶠ z in 𝓝 0, HasDerivAt c (-(s z * d z)) z)
    (hd : ∀ᶠ z in 𝓝 0, HasDerivAt d (-(κ * s z * c z)) z)
    (hS : ∀ z, HasDerivAt S (S' z) z) (hC : ∀ z, HasDerivAt C (C' z) z)
    (hD : ∀ z, HasDerivAt D (D' z) z)
    (h0s : s 0 = S 0) (h0c : c 0 = C 0) (h0d : d 0 = D 0)
    (hrs : (fun z => C z * D z - S' z) =O[𝓝 0] fun z => z ^ 8)
    (hrc : (fun z => -(S z * D z) - C' z) =O[𝓝 0] fun z => z ^ 7)
    (hrd : (fun z => -(κ * S z * C z) - D' z) =O[𝓝 0] fun z => z ^ 7) :
    (fun z => s z - S z) =O[𝓝 0] (fun z => z ^ 9) ∧
      (fun z => c z - C z) =O[𝓝 0] (fun z => z ^ 8) ∧
      (fun z => d z - D z) =O[𝓝 0] (fun z => z ^ 8) := by
  set es := fun z => s z - S z with hes_def
  set ec := fun z => c z - C z with hec_def
  set ed := fun z => d z - D z with hed_def
  have hes : ∀ᶠ z in 𝓝 0, HasDerivAt es ((C z * D z - S' z) + C z * ed z + D z * ec z +
      ec z * ed z) z := by
    filter_upwards [hs] with z hz
    exact (hz.sub (hS z)).congr_deriv (by simp only [hec_def, hed_def]; ring)
  have hec : ∀ᶠ z in 𝓝 0, HasDerivAt ec ((-(S z * D z) - C' z) + (-1) * (S z * ed z) +
      (-1) * (D z * es z) + (-1) * (es z * ed z)) z := by
    filter_upwards [hc] with z hz
    exact (hz.sub (hC z)).congr_deriv (by simp only [hes_def, hed_def]; ring)
  have hed : ∀ᶠ z in 𝓝 0, HasDerivAt ed ((-(κ * S z * C z) - D' z) + (-κ) * (S z * ec z) +
      (-κ) * (C z * es z) + (-κ) * (es z * ec z)) z := by
    filter_upwards [hd] with z hz
    exact (hz.sub (hD z)).congr_deriv (by simp only [hes_def, hec_def]; ring)
  have z0s : es 0 = 0 := by simp [hes_def, h0s]
  have z0c : ec 0 = 0 := by simp [hec_def, h0c]
  have z0d : ed 0 = 0 := by simp [hed_def, h0d]
  have bS := isBigO_one_of_continuousAt (hS 0).continuousAt
  have bC := isBigO_one_of_continuousAt (hC 0).continuousAt
  have bD := isBigO_one_of_continuousAt (hD 0).continuousAt
  have bes := isBigO_one_of_continuousAt hes.self_of_nhds.continuousAt
  have bec := isBigO_one_of_continuousAt hec.self_of_nhds.continuousAt
  have bed := isBigO_one_of_continuousAt hed.self_of_nhds.continuousAt
  have bk : (fun _ : ℂ => (-1 : ℂ)) =O[𝓝 0] fun _ => (1 : ℂ) := isBigO_const_const _ one_ne_zero _
  have bκ : (fun _ : ℂ => (-κ : ℂ)) =O[𝓝 0] fun _ => (1 : ℂ) := isBigO_const_const _ one_ne_zero _
  have P : ∀ j, j ≤ 8 → es =O[𝓝 0] (fun z => z ^ j) ∧ ec =O[𝓝 0] (fun z => z ^ j) ∧
      ed =O[𝓝 0] (fun z => z ^ j) := by
    intro j
    induction j with
    | zero => intro _; simp only [pow_zero]; exact ⟨bes, bec, bed⟩
    | succ j ih =>
      intro hj
      obtain ⟨h1, h2, h3⟩ := ih (by omega)
      have r8 := hrs.trans (pow_isBigO_pow_of_le (a := 8) (b := j) (by omega))
      have r7c := hrc.trans (pow_isBigO_pow_of_le (a := 7) (b := j) (by omega))
      have r7d := hrd.trans (pow_isBigO_pow_of_le (a := 7) (b := j) (by omega))
      refine ⟨isBigO_pow_succ_of_deriv_isBigO_pow hes z0s ?_,
          isBigO_pow_succ_of_deriv_isBigO_pow hec z0c ?_,
        isBigO_pow_succ_of_deriv_isBigO_pow hed z0d ?_⟩
      · exact ((r8.add (mul_isBigO_pow_of_isBigO_one h3 bC)).add
            (mul_isBigO_pow_of_isBigO_one h2 bD)).add (mul_isBigO_pow_of_isBigO_one h3 bec)
      · exact ((r7c.add (mul_isBigO_pow_of_isBigO_one (mul_isBigO_pow_of_isBigO_one h3 bS) bk)).add
          (mul_isBigO_pow_of_isBigO_one (mul_isBigO_pow_of_isBigO_one h1 bD) bk)).add
              (mul_isBigO_pow_of_isBigO_one (mul_isBigO_pow_of_isBigO_one h3 bes) bk)
      · exact ((r7d.add (mul_isBigO_pow_of_isBigO_one (mul_isBigO_pow_of_isBigO_one h2 bS) bκ)).add
          (mul_isBigO_pow_of_isBigO_one (mul_isBigO_pow_of_isBigO_one h1 bC) bκ)).add
              (mul_isBigO_pow_of_isBigO_one (mul_isBigO_pow_of_isBigO_one h2 bes) bκ)
  obtain ⟨h1, h2, h3⟩ := P 8 le_rfl
  exact ⟨isBigO_pow_succ_of_deriv_isBigO_pow hes z0s
    (((hrs.add (mul_isBigO_pow_of_isBigO_one h3 bC)).add (mul_isBigO_pow_of_isBigO_one h2 bD)).add
        (mul_isBigO_pow_of_isBigO_one h3 bec)), h2, h3⟩

/-- Asymptotic bound with the indicated comparison function: `R =O[𝓝 0] fun z => z ^ n`. -/
private lemma isBigO_pow_of_eq_pow_mul {R Q : ℂ → ℂ} {n : ℕ} (hQ : Continuous Q)
    (h : ∀ z, R z = z ^ n * Q z) : R =O[𝓝 0] fun z => z ^ n := by
  rw [show R = fun z => Q z * z ^ n from funext fun z => by rw [h, mul_comm]]
  exact mul_isBigO_pow_of_isBigO_one (isBigO_refl _ _) (isBigO_one_of_continuousAt hQ.continuousAt)

/-- The Maclaurin polynomials of `sn, cn, dn` (DLMF 22.10.1–22.10.3) approximate them to
orders `z⁹, z⁸, z⁸`. -/
private lemma jacobiSnCnDnk_sub_maclaurin_isBigO {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    (fun z => jacobiSn z k - (z - (1 + k ^ 2) * z ^ 3 / 6 + (1 + 14 * k ^ 2 + k ^ 4) * z ^ 5 /
        120 - (1 + 135 * k ^ 2 + 135 * k ^ 4 + k ^ 6) * z ^ 7 / 5040)) =O[𝓝 0]
        (fun z => z ^ 9) ∧
      (fun z => jacobiCn z k - (1 - z ^ 2 / 2 + (1 + 4 * k ^ 2) * z ^ 4 / 24 -
        (1 + 44 * k ^ 2 + 16 * k ^ 4) * z ^ 6 / 720)) =O[𝓝 0] (fun z => z ^ 8) ∧
      (fun z => jacobiDn z k - (1 - k ^ 2 * z ^ 2 / 2 + k ^ 2 * (4 + k ^ 2) * z ^ 4 / 24 -
        k ^ 2 * (16 + 44 * k ^ 2 + k ^ 4) * z ^ 6 / 720)) =O[𝓝 0] (fun z => z ^ 8) := by
  have hreg := eventually_jacobiLetterTheta_ne_zero hk
      (jacobiLetterTheta_jacobiThetaArgument_zero_ne_zero hk (q := .n) (by decide))
  have hpow : ∀ (a : ℂ) (n : ℕ) (b : ℂ) (z : ℂ),
      HasDerivAt (fun z : ℂ => a * z ^ n / b) (a * (n * z ^ (n - 1)) / b) z :=
    fun a n b z => ((hasDerivAt_pow n z).const_mul a).div_const b
  refine jacobiSystem_isBigO_of_approx (κ := k ^ 2)
    (S' := fun z => 1 - (1 + k ^ 2) * (3 * z ^ 2) / 6 + (1 + 14 * k ^ 2 + k ^ 4) * (5 * z ^ 4) /
        120 - (1 + 135 * k ^ 2 + 135 * k ^ 4 + k ^ 6) * (7 * z ^ 6) / 5040)
    (C' := fun z => -(1 * (2 * z) / 2) + (1 + 4 * k ^ 2) * (4 * z ^ 3) / 24 -
        (1 + 44 * k ^ 2 + 16 * k ^ 4) * (6 * z ^ 5) / 720)
    (D' := fun z => -(k ^ 2 * (2 * z) / 2) + k ^ 2 * (4 + k ^ 2) * (4 * z ^ 3) / 24 -
        k ^ 2 * (16 + 44 * k ^ 2 + k ^ 4) * (6 * z ^ 5) / 720)
    (hreg.mono fun z hz => hasDerivAt_jacobiSn hk hz)
    (hreg.mono fun z hz => hasDerivAt_jacobiCn hk hz)
    (hreg.mono fun z hz => hasDerivAt_jacobiDn hk hz) ?_ ?_ ?_
    (by simp [jacobiSn_zero hk]) (by simp [jacobiCn_zero hk]) (by simp [jacobiDn_zero hk])
    ?_ ?_ ?_
  · intro z
    have := ((((hasDerivAt_id z).sub (hpow (1 + k ^ 2) 3 6 z)).add
      (hpow (1 + 14 * k ^ 2 + k ^ 4) 5 120 z)).sub (hpow (1 + 135 * k ^ 2 + 135 * k ^ 4 + k ^ 6)
        7 5040 z))
    convert this using 1
    funext w; rfl
  · intro z
    have := ((((hasDerivAt_const z (1 : ℂ)).sub (hpow 1 2 2 z)).add
      (hpow (1 + 4 * k ^ 2) 4 24 z)).sub (hpow (1 + 44 * k ^ 2 + 16 * k ^ 4) 6 720 z))
    convert this using 1
    · funext w; simp
    · simp
  · intro z
    have := ((((hasDerivAt_const z (1 : ℂ)).sub (hpow (k ^ 2) 2 2 z)).add
      (hpow (k ^ 2 * (4 + k ^ 2)) 4 24 z)).sub (hpow (k ^ 2 * (16 + 44 * k ^ 2 + k ^ 4)) 6 720 z))
    convert this using 1
    simp
  · refine isBigO_pow_of_eq_pow_mul
        (Q := fun z => k^10*z^4/32400 + 187*k^8*z^4/129600 - k^8*z^2/864 +
      731*k^6*z^4/172800 - 19*k^6*z^2/1152 + 3*k^6/160 + 187*k^4*z^4/129600 - 19*k^4*z^2/1152 +
      29*k^4/320 + k^2*z^4/32400 - k^2*z^2/864 + 3*k^2/160) (by fun_prop) fun z => by ring
  · refine isBigO_pow_of_eq_pow_mul (Q := fun z => -k^12*z^6/3628800 - 179*k^10*z^6/3628800 +
      k^10*z^4/50400 - 6091*k^8*z^6/3628800 + 367*k^8*z^4/201600 - 41*k^8*z^2/60480 -
      8101*k^6*z^6/3628800 + 1301*k^6*z^4/100800 - 101*k^6*z^2/3360 + 4*k^6/315 -
      551*k^4*z^6/907200 + 509*k^4*z^4/67200 - 949*k^4*z^2/20160 + 19*k^4/105 -
      k^2*z^6/226800 + 11*k^2*z^4/50400 - 157*k^2*z^2/30240 + 17*k^2/210 + 1/5040)
      (by fun_prop) fun z => by ring
  · refine isBigO_pow_of_eq_pow_mul (Q := fun z => -k^12*z^6/226800 - 551*k^10*z^6/907200 +
      11*k^10*z^4/50400 - 8101*k^8*z^6/3628800 + 509*k^8*z^4/67200 - 157*k^8*z^2/30240 +
      k^8/5040 - 6091*k^6*z^6/3628800 + 1301*k^6*z^4/100800 - 949*k^6*z^2/20160 + 17*k^6/210 -
      179*k^4*z^6/3628800 + 367*k^4*z^4/201600 - 101*k^4*z^2/3360 + 19*k^4/105 -
      k^2*z^6/3628800 + k^2*z^4/50400 - 41*k^2*z^2/60480 + 4*k^2/315)
      (by fun_prop) fun z => by ring

/-- A function complex differentiable on an open disc has a power series on that disc. -/
private lemma exists_hasFPowerSeriesOnBall_of_differentiableOn {f : ℂ → ℂ} {r : ℝ≥0∞} (hr : 0 < r)
    (hf : DifferentiableOn ℂ f (Metric.eball 0 r)) :
    ∃ p : FormalMultilinearSeries ℂ ℂ ℂ, HasFPowerSeriesOnBall f p 0 r := by
  have hsub : ∀ r' : ℝ≥0, (r' : ℝ≥0∞) < r → 0 < r' →
      HasFPowerSeriesOnBall f (cauchyPowerSeries f 0 r') 0 r' := by
    intro r' hr' h0
    refine DifferentiableOn.hasFPowerSeriesOnBall (hf.mono fun w hw => ?_) h0
    rw [Metric.mem_closedBall, dist_zero_right] at hw
    rw [Metric.mem_eball, edist_zero_right]
    refine lt_of_le_of_lt ?_ hr'
    rw [enorm_eq_nnnorm, ENNReal.coe_le_coe, ← NNReal.coe_le_coe, coe_nnnorm]; exact hw
  obtain ⟨r0, h0, h0r⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hr
  have h := hsub r0 h0r (by exact_mod_cast h0)
  refine ⟨cauchyPowerSeries f 0 r0, ?_⟩
  exact
  { r_le := ENNReal.le_of_forall_pos_nnreal_lt fun r' hr' hr'r =>
      (h.exchange_radius (hsub r' hr'r hr')).r_le
    r_pos := hr
    hasSum := fun {y} hy => by
      rw [Metric.mem_eball, edist_zero_right] at hy
      obtain ⟨r', hr1, hr2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hy
      have hpos : 0 < r' := by
        exact ENNReal.coe_pos.mp (lt_of_le_of_lt bot_le hr1)
      exact (h.exchange_radius (hsub r' hr2 hpos)).hasSum (by
        rw [Metric.mem_eball, edist_zero_right]; exact hr1) }

/-- For real `0 < k < 1`, `sn, cn, dn` have no pole in the disc `|z| < K'`. -/
private lemma jacobiLetterTheta_n_ne_zero_of_norm_lt {κ : ℝ} (hk0 : 0 < κ) (hk1 : κ < 1) {z : ℂ}
    (hz : ‖z‖ < Real.completeEllipticKOfParameter (1 - κ ^ 2)) :
    jacobiLetterTheta .n (jacobiThetaArgument z κ) (jacobiTau κ) ≠ 0 := by
  have hk := ofReal_mem_jacobiModulusDomain hk0 hk1
  have hτ := jacobiTau_im_pos hk
  have hK := completeEllipticK_ofReal (k := κ) (by nlinarith)
  have hKp := completeEllipticKPrime_ofReal (k := κ) (by positivity)
  have hKpos : 0 < Real.completeEllipticKOfParameter (κ ^ 2) :=
      Real.completeEllipticKOfParameter_pos (by nlinarith)
  rw [jacobiLetterTheta]
  refine div_ne_zero (fun h => ?_) (jacobiThetaFourTau_zero_ne_zero hτ)
  obtain ⟨m, n, hmn⟩ := ((DLMF.Theta.jacobiThetaTau_eq_zero_iff hτ _).2.2.2).mp h
  set Kr := Real.completeEllipticKOfParameter (κ ^ 2)
  set Kp := Real.completeEllipticKOfParameter (1 - κ ^ 2)
  rw [jacobiThetaArgument, jacobiTau, hK, hKp] at hmn
  have hKc : (Kr : ℂ) ≠ 0 := by exact_mod_cast hKpos.ne'
  have hz' : z = 2 * Kr * m + (2 * n + 1) * Kp * I := by
    field_simp at hmn
    linear_combination hmn
  have him : z.im = (2 * n + 1) * Kp := by
    rw [hz']; simp
  have h1 : Kp ≤ |z.im| := by
    rw [him, abs_mul]
    have hKp0 : 0 ≤ Kp := (Real.completeEllipticKOfParameter_pos (by nlinarith)).le
    rw [abs_of_nonneg hKp0]
    have : (1 : ℝ) ≤ |2 * (n : ℝ) + 1| := by
      have : (1 : ℤ) ≤ |2 * n + 1| := by
        rcases le_or_gt 0 n with h | h
        · rw [abs_of_nonneg (by omega)]; omega
        · rw [abs_of_neg (by omega)]; omega
      exact_mod_cast this
    nlinarith
  linarith [abs_im_le_norm z]

/-- DLMF 22.10.1: `sn(z,k) = z - (1 + k²) z³/3! + (1 + 14k² + k⁴) z⁵/5!
- (1 + 135k² + 135k⁴ + k⁶) z⁷/7! + O(z⁹)`. -/
@[dlmf 22.10.E1 "domain: k ∈ jacobiModulusDomain"]
theorem jacobiSn_isBigO_maclaurin (hk : k ∈ jacobiModulusDomain) :
    (fun z => jacobiSn z k - (z - (1 + k ^ 2) * z ^ 3 / 6 + (1 + 14 * k ^ 2 + k ^ 4) * z ^ 5 /
        120 -
      (1 + 135 * k ^ 2 + 135 * k ^ 4 + k ^ 6) * z ^ 7 / 5040)) =O[𝓝 0] fun z => z ^ 9 := by
  exact (jacobiSnCnDnk_sub_maclaurin_isBigO hk).1

/-- DLMF 22.10.2: `cn(z,k) = 1 - z²/2! + (1 + 4k²) z⁴/4! - (1 + 44k² + 16k⁴) z⁶/6! + O(z⁸)`.
-/
@[dlmf 22.10.E2 "domain: k ∈ jacobiModulusDomain"]
theorem jacobiCn_isBigO_maclaurin (hk : k ∈ jacobiModulusDomain) :
    (fun z => jacobiCn z k - (1 - z ^ 2 / 2 + (1 + 4 * k ^ 2) * z ^ 4 / 24 -
      (1 + 44 * k ^ 2 + 16 * k ^ 4) * z ^ 6 / 720)) =O[𝓝 0] fun z => z ^ 8 := by
  exact (jacobiSnCnDnk_sub_maclaurin_isBigO hk).2.1

/-- DLMF 22.10.3: `dn(z,k) = 1 - k² z²/2! + k²(4 + k²) z⁴/4! - k²(16 + 44k² + k⁴) z⁶/6! + O(z⁸)`.
-/
@[dlmf 22.10.E3 "domain: k ∈ jacobiModulusDomain"]
theorem jacobiDn_isBigO_maclaurin (hk : k ∈ jacobiModulusDomain) :
    (fun z => jacobiDn z k - (1 - k ^ 2 * z ^ 2 / 2 + k ^ 2 * (4 + k ^ 2) * z ^ 4 / 24 -
      k ^ 2 * (16 + 44 * k ^ 2 + k ^ 4) * z ^ 6 / 720)) =O[𝓝 0] fun z => z ^ 8 := by
  exact (jacobiSnCnDnk_sub_maclaurin_isBigO hk).2.2

/-- DLMF §22.10(i), prose: the full Maclaurin expansions of `sn, cn, dn` converge for
`|z| < min(K, K')`; stated for `0 < k < 1` as power series on the ball of that radius
(`K = K(k²)`, `K' = K(1 - k²)`). -/
@[dlmf 22.10.i "special case: 0 < k < 1"]
theorem jacobi_hasFPowerSeriesOnBall {κ : ℝ} (hk0 : 0 < κ) (hk1 : κ < 1) :
    let r := ENNReal.ofReal (min (DLMF.Elliptic.Real.completeEllipticKOfParameter (κ ^ 2))
      (DLMF.Elliptic.Real.completeEllipticKOfParameter (1 - κ ^ 2)))
    (∃ p : FormalMultilinearSeries ℂ ℂ ℂ, HasFPowerSeriesOnBall (fun z => jacobiSn z κ) p 0 r) ∧
      (∃ p : FormalMultilinearSeries ℂ ℂ ℂ,
        HasFPowerSeriesOnBall (fun z => jacobiCn z κ) p 0 r) ∧
      ∃ p : FormalMultilinearSeries ℂ ℂ ℂ, HasFPowerSeriesOnBall (fun z => jacobiDn z κ) p 0 r :=
          by
  intro r
  have hk := ofReal_mem_jacobiModulusDomain hk0 hk1
  have hr : 0 < r := ENNReal.ofReal_pos.mpr
      (lt_min (Real.completeEllipticKOfParameter_pos (by nlinarith))
    (Real.completeEllipticKOfParameter_pos (by nlinarith)))
  have hreg : ∀ z ∈ Metric.eball (0 : ℂ) r,
      jacobiLetterTheta .n (jacobiThetaArgument z κ) (jacobiTau κ) ≠ 0 := by
    intro z hz
    refine jacobiLetterTheta_n_ne_zero_of_norm_lt hk0 hk1 ?_
    rw [Metric.mem_eball, edist_zero_right, enorm_eq_nnnorm] at hz
    have h1 : (‖z‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖z‖ := by
      rw [ofReal_norm, enorm_eq_nnnorm]
    rw [h1, ENNReal.ofReal_lt_ofReal_iff_of_nonneg (norm_nonneg _)] at hz
    exact lt_of_lt_of_le hz (min_le_right _ _)
  exact ⟨exists_hasFPowerSeriesOnBall_of_differentiableOn hr fun z hz =>
      (hasDerivAt_jacobiSn hk (hreg z hz)).differentiableAt.differentiableWithinAt,
    exists_hasFPowerSeriesOnBall_of_differentiableOn hr fun z hz =>
      (hasDerivAt_jacobiCn hk (hreg z hz)).differentiableAt.differentiableWithinAt,
    exists_hasFPowerSeriesOnBall_of_differentiableOn hr fun z hz =>
      (hasDerivAt_jacobiDn hk (hreg z hz)).differentiableAt.differentiableWithinAt⟩

/-! ### §22.10(ii): Maclaurin series in `k` and `k'` -/

/-- DLMF 22.10.4: `sn(z,k) = sin z - k²(z - sin z cos z) cos z/4 + O(k⁴)` as `k → 0` in
`jacobiModulusDomain`, for fixed complex `z`. Admitted. -/
@[dlmf 22.10.E4 "domain: k → 0 within jacobiModulusDomain, fixed z"]
theorem jacobiSn_isBigO_small_modulus (z : ℂ) :
    (fun k => jacobiSn z k - (sin z - k ^ 2 / 4 * (z - sin z * cos z) * cos z))
      =O[𝓝[jacobiModulusDomain] 0] fun k => k ^ 4 := by
  sorry

/-- DLMF 22.10.5: `cn(z,k) = cos z + k²(z - sin z cos z) sin z/4 + O(k⁴)` as `k → 0`.
Admitted. -/
@[dlmf 22.10.E5 "domain: k → 0 within jacobiModulusDomain, fixed z"]
theorem jacobiCn_isBigO_small_modulus (z : ℂ) :
    (fun k => jacobiCn z k - (cos z + k ^ 2 / 4 * (z - sin z * cos z) * sin z))
      =O[𝓝[jacobiModulusDomain] 0] fun k => k ^ 4 := by
  sorry

/-- DLMF 22.10.6: `dn(z,k) = 1 - k² sin² z/2 + O(k⁴)` as `k → 0`. Admitted. -/
@[dlmf 22.10.E6 "domain: k → 0 within jacobiModulusDomain, fixed z"]
theorem jacobiDn_isBigO_small_modulus (z : ℂ) :
    (fun k => jacobiDn z k - (1 - k ^ 2 / 2 * sin z ^ 2))
      =O[𝓝[jacobiModulusDomain] 0] fun k => k ^ 4 := by
  sorry

/-- DLMF 22.10.7: `sn(z,k) = tanh z - k'²(z - sinh z cosh z) sech² z/4 + O(k'⁴)` as `k → 1`
in `jacobiModulusDomain`, for fixed `z` with `cosh z ≠ 0`. Admitted. -/
@[dlmf 22.10.E7 "domain: k → 1 within jacobiModulusDomain, fixed z with cosh z ≠ 0"]
theorem jacobiSn_isBigO_small_comodulus {z : ℂ} (hz : cosh z ≠ 0) :
    (fun k => jacobiSn z k - (tanh z - jacobiComodulus k ^ 2 / 4 * (z - sinh z * cosh z) /
      cosh z ^ 2)) =O[𝓝[jacobiModulusDomain] 1] fun k => jacobiComodulus k ^ 4 := by
  sorry

/-- DLMF 22.10.8: `cn(z,k) = sech z + k'²(z - sinh z cosh z) tanh z sech z/4 + O(k'⁴)` as
`k → 1`, `cosh z ≠ 0`. Admitted. -/
@[dlmf 22.10.E8 "domain: k → 1 within jacobiModulusDomain, fixed z with cosh z ≠ 0"]
theorem jacobiCn_isBigO_small_comodulus {z : ℂ} (hz : cosh z ≠ 0) :
    (fun k => jacobiCn z k - (1 / cosh z + jacobiComodulus k ^ 2 / 4 *
      (z - sinh z * cosh z) * tanh z / cosh z))
      =O[𝓝[jacobiModulusDomain] 1] fun k => jacobiComodulus k ^ 4 := by
  sorry

/-- DLMF 22.10.9: `dn(z,k) = sech z + k'²(z + sinh z cosh z) tanh z sech z/4 + O(k'⁴)` as
`k → 1`, `cosh z ≠ 0`. Admitted. -/
@[dlmf 22.10.E9 "domain: k → 1 within jacobiModulusDomain, fixed z with cosh z ≠ 0"]
theorem jacobiDn_isBigO_small_comodulus {z : ℂ} (hz : cosh z ≠ 0) :
    (fun k => jacobiDn z k - (1 / cosh z + jacobiComodulus k ^ 2 / 4 *
      (z + sinh z * cosh z) * tanh z / cosh z))
      =O[𝓝[jacobiModulusDomain] 1] fun k => jacobiComodulus k ^ 4 := by
  sorry

end DLMF.JacobiElliptic
