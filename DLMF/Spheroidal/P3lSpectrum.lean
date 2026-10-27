/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Hypergeometric.Series
public import DLMFMathlib.Analysis.ODE.P2lSturmLiouville
public import DLMFMathlib.Analysis.ODE.P2sSturmSpectrum

/-!
# The spectrum of the spheroidal factor equation (DLMF §30.3(i))

For `m ∈ ℕ` and real `γ²`, `λ`, consider the equation of the entire factor `g` of
`(1 - z²)^{m/2} g(z)` (DLMF §30.3(i)):

`(1 - z²) g'' - 2(m+1) z g' + (λ - m(m+1) + γ²(1 - z²)) g = 0`.

We prove that the set `p3lSpec m γ²` of real `λ` for which it has a nonzero entire solution is
infinite and meets every half-line `(-∞, x)` in a finite set (`p3lSpec_infinite`,
`p3lSpec_Iio_finite`). This gives the existence of the eigenvalues `λ^m_n(γ²)`
(`DLMF.Spheroidal.exists_spheroidalEigenvalue`).

## Method

* **Frobenius solution at `z = 1`** (exponent `0`): `Y(z) = ∑ f_k (z - 1)^k` with the
  recurrence `2(k+1)(k+m+1) f_{k+1} = (c - k(k+2m+1)) f_k - 2γ² f_{k-1} - γ² f_{k-2}`,
  `c = λ - m(m+1)`, convergent for `|z - 1| < 5/3` (majorants, uniformly for `|c| ≤ K`).
* **Entire solutions force `Y(0) Y'(0) = 0`**: the Wronskian `(1-z²)^{m+1}(g Y' - g' Y)` is
  constant on the disc and vanishes at `z = 1`; applied to `g(z)` and `g(-z)`.
* **Conversely**, if `Y(0) = 0` (`Y'(0) = 0`), `Y` and `∓Y(-z)` agree on the lens between the
  discs about `±1` and glue to a solution on `|z| ≤ 6/5`; its Taylor coefficients at `0` satisfy
  a three-term recurrence and decay geometrically, hence superexponentially
  (`p3l_superexp`), so the solution is entire.
* **Discreteness and lower bound**: `λ ↦ Y(0) Y'(0)` is entire in `λ`; for
  `λ < m(m+1) - |γ²|` it does not vanish (monotonicity of `(1-x²)^{m+1} y y'` on `[0, 1]`).
* **Infinitely many eigenvalues**: by Sturm comparison with `sin(ω s(x))`,
  `s' = (1-x²)^{-m-1}`, the real solution has at least `J` zeros in `(0, 1/2)` for large `λ`;
  the zero count in `[0, 1]` is locally constant in `λ` while `Y(0) ≠ 0`
  (`ODE.sturmDef_ncard_eq_of_isPreconnected`), so `Y(0) = 0` for arbitrarily large `λ`.

Uses the power-series helpers of `DLMF.Hypergeometric.Series` and the Sturm tools of
`DLMFMathlib/Analysis/ODE`. Proof round 3, agent `ls` (prefix `p3l_`).
-/

@[expose] public noncomputable section

open Complex Set Filter FormalMultilinearSeries
open scoped Topology ENNReal ContDiff

namespace DLMF.Spheroidal

/-- Shifted Frobenius coefficients at `z = 1`. -/
def p3lH {K : Type*} [Field K] (m : ℕ) (γ2 c : K) : ℕ → K
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | k + 3 => ((c - (k : K) * (k + 2 * m + 1)) * p3lH m γ2 c (k + 2) -
      2 * γ2 * p3lH m γ2 c (k + 1) - γ2 * p3lH m γ2 c k) / (2 * ((k : K) + 1) * (k + m + 1))

/-- The coefficients commute with ring homomorphisms. -/
lemma p3lH_map {K L : Type*} [Field K] [Field L] [CharZero L] (f : K →+* L) (m : ℕ) (γ2 c : K)
    (k : ℕ) : f (p3lH m γ2 c k) = p3lH m (f γ2) (f c) k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k, ih with
    | 0, _ => simp [p3lH]
    | 1, _ => simp [p3lH]
    | 2, _ => simp [p3lH]
    | k + 3, ih =>
      simp only [p3lH, map_div₀, map_sub, map_mul, map_add, map_natCast, map_ofNat, map_one]
      rw [ih (k + 2) (by omega), ih (k + 1) (by omega), ih k (by omega)]

/-- Majorant of the Frobenius coefficients for `‖c‖ ≤ K`, `‖γ2‖ = G`. -/
def p3lMaj (m : ℕ) (G K : ℝ) : ℕ → ℝ
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | k + 3 => ((K + (k : ℝ) * (k + 2 * m + 1)) * p3lMaj m G K (k + 2) +
      2 * G * p3lMaj m G K (k + 1) + G * p3lMaj m G K k) / (2 * ((k : ℝ) + 1) * (k + m + 1))

/-- The majorant is nonnegative. -/
lemma p3lMaj_nonneg (m : ℕ) {G K : ℝ} (hG : 0 ≤ G) (hK : 0 ≤ K) (k : ℕ) :
    0 ≤ p3lMaj m G K k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k, ih with
    | 0, _ => simp [p3lMaj]
    | 1, _ => simp [p3lMaj]
    | 2, _ => simp [p3lMaj]
    | k + 3, ih =>
      simp only [p3lMaj]
      have := ih (k + 2) (by omega); have := ih (k + 1) (by omega); have := ih k (by omega)
      positivity

/-- The majorant bounds the coefficients for `‖c‖ ≤ K`. -/
lemma p3lH_le_maj (m : ℕ) {γ2 c : ℂ} {K : ℝ} (hc : ‖c‖ ≤ K) (k : ℕ) :
    ‖p3lH m γ2 c k‖ ≤ p3lMaj m ‖γ2‖ K k := by
  have hK : 0 ≤ K := (norm_nonneg _).trans hc
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k, ih with
    | 0, _ => simp [p3lH, p3lMaj]
    | 1, _ => simp [p3lH, p3lMaj]
    | 2, _ => simp [p3lH, p3lMaj]
    | k + 3, ih =>
      simp only [p3lH, p3lMaj]
      have h2 := ih (k + 2) (by omega); have h1 := ih (k + 1) (by omega)
      have h0 := ih k (by omega)
      have hd : ‖(2 * ((k : ℂ) + 1) * (k + m + 1))‖ = 2 * ((k : ℝ) + 1) * (k + m + 1) := by
        rw [show (2 * ((k : ℂ) + 1) * (k + m + 1)) = ((2 * ((k : ℝ) + 1) * (k + m + 1) : ℝ) : ℂ)
          by push_cast; ring, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      rw [norm_div, hd]
      gcongr
      have hck : ‖c - (k : ℂ) * (k + 2 * m + 1)‖ ≤ K + (k : ℝ) * (k + 2 * m + 1) := by
        refine (norm_sub_le _ _).trans (add_le_add hc (le_of_eq ?_))
        rw [show (k : ℂ) * (k + 2 * m + 1) = (((k : ℝ) * (k + 2 * m + 1) : ℝ) : ℂ) by
            push_cast; ring,
          Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      calc ‖(c - (k : ℂ) * (k + 2 * m + 1)) * p3lH m γ2 c (k + 2) - 2 * γ2 * p3lH m γ2 c (k + 1) -
            γ2 * p3lH m γ2 c k‖
          ≤ ‖c - (k : ℂ) * (k + 2 * m + 1)‖ * ‖p3lH m γ2 c (k + 2)‖ +
            2 * ‖γ2‖ * ‖p3lH m γ2 c (k + 1)‖ + ‖γ2‖ * ‖p3lH m γ2 c k‖ := by
            refine (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans ?_) ?_)
            · rw [norm_mul, norm_mul, norm_mul]; norm_num
            · rw [norm_mul]
        _ ≤ _ := by
            have := norm_nonneg (p3lH m γ2 c (k + 2))
            gcongr


/-- Geometric bound `C (3/5)^k` for the majorant. -/
lemma p3lMaj_le (m : ℕ) {G K : ℝ} (hG : 0 ≤ G) (hK : 0 ≤ K) :
    ∃ C : ℝ, ∀ k, p3lMaj m G K k ≤ C * (3 / 5) ^ k := by
  set N : ℕ := ⌈5 * (2 * (m : ℝ) + 1) + 5 * K + 31 * G⌉₊ + 1
  set M : ℝ := ∑ j ∈ Finset.range (N + 3), p3lMaj m G K j / (3 / 5) ^ j
  have hterm : ∀ j < N + 3, p3lMaj m G K j ≤ M * (3 / 5) ^ j := by
    intro j hj
    have h0 : ∀ i ∈ Finset.range (N + 3), 0 ≤ p3lMaj m G K i / (3 / 5) ^ i :=
      fun i _ => div_nonneg (p3lMaj_nonneg m hG hK i) (by positivity)
    have := Finset.single_le_sum h0 (Finset.mem_range.2 hj)
    rw [div_le_iff₀ (by positivity)] at this
    exact this
  refine ⟨M, fun k => ?_⟩
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    by_cases hk : k < N + 3
    · exact hterm k hk
    obtain ⟨k, rfl⟩ : ∃ i, k = i + 3 := ⟨k - 3, by omega⟩
    have hkN : (N : ℝ) ≤ k := by exact_mod_cast (show N ≤ k by omega)
    have hN : 5 * (2 * (m : ℝ) + 1) + 5 * K + 31 * G + 1 ≤ N := by
      have := Nat.le_ceil (5 * (2 * (m : ℝ) + 1) + 5 * K + 31 * G)
      simp only [N]; push_cast; linarith
    have h2 := ih (k + 2) (by omega); have h1 := ih (k + 1) (by omega)
    have h0 := ih k (by omega)
    simp only [p3lMaj]
    have hD : 0 < 2 * ((k : ℝ) + 1) * (k + m + 1) := by positivity
    rw [div_le_iff₀ hD]
    have hM : 0 ≤ M := Finset.sum_nonneg fun i _ =>
      div_nonneg (p3lMaj_nonneg m hG hK i) (by positivity)
    have hρ : (0 : ℝ) < (3 / 5) ^ k := by positivity
    have hA : 0 ≤ K + (k : ℝ) * (k + 2 * m + 1) := by positivity
    calc (K + (k : ℝ) * (k + 2 * m + 1)) * p3lMaj m G K (k + 2) +
          2 * G * p3lMaj m G K (k + 1) + G * p3lMaj m G K k
        ≤ (K + (k : ℝ) * (k + 2 * m + 1)) * (M * (3 / 5) ^ (k + 2)) +
          2 * G * (M * (3 / 5) ^ (k + 1)) + G * (M * (3 / 5) ^ k) := by gcongr
      _ = M * (3 / 5) ^ k * ((K + (k : ℝ) * (k + 2 * m + 1)) * (9 / 25) + 2 * G * (3 / 5) + G) := by
          ring
      _ ≤ M * (3 / 5) ^ k * (2 * ((k : ℝ) + 1) * (k + m + 1) * (27 / 125)) := by
          gcongr
          have hk1 : (1 : ℝ) ≤ k := by linarith
          have : 5 * (2 * (m : ℝ) + 1) + 5 * K + 31 * G ≤ k := by linarith
          nlinarith [mul_le_mul_of_nonneg_left this (show (0 : ℝ) ≤ k by linarith)]
      _ = M * (3 / 5) ^ (k + 3) * (2 * ((k : ℝ) + 1) * (k + m + 1)) := by ring


/-- Shift of a coefficient sequence (multiplication of the series by the variable). -/
def p3lSh (u : ℕ → ℂ) : ℕ → ℂ
  | 0 => 0
  | n + 1 => u n

/-- Multiplication of a power series by its variable. -/
lemma p3l_hasSum_sh {u : ℕ → ℂ} {S z : ℂ} (h : HasSum (fun n => u n * z ^ n) S) :
    HasSum (fun n => p3lSh u n * z ^ n) (z * S) :=
  HasSum.mul_pow_shift (c := p3lSh u) h rfl

/-- Coefficients of `A f'' + B f' + C f` for quadratic `A, B, C` and `f = ∑ bₙ zⁿ`. -/
def p3lE (a0 a1 a2 b0 b1 b2 c0 c1 c2 : ℂ) (b : ℕ → ℂ) (n : ℕ) : ℂ :=
  a0 * (((n : ℂ) + 1) * ((n : ℂ) + 2) * b (n + 2)) + a1 * ((n : ℂ) * ((n : ℂ) + 1) * b (n + 1)) +
    a2 * ((n : ℂ) * ((n : ℂ) - 1) * b n) + b0 * (((n : ℂ) + 1) * b (n + 1)) +
    b1 * ((n : ℂ) * b n) + b2 * p3lSh (fun n => (n : ℂ) * b n) n + c0 * b n +
    c1 * p3lSh b n + c2 * p3lSh (p3lSh b) n

/-- The power series of `A f'' + B f' + C f` on the disc of convergence of `f`. -/
lemma p3l_hasSum_op {a0 a1 a2 b0 b1 b2 c0 c1 c2 : ℂ} {b : ℕ → ℂ} {f : ℂ → ℂ} {r : ℝ≥0∞}
    (h : HasFPowerSeriesOnBall f (ofScalars ℂ b) 0 r) {z : ℂ} (hz : z ∈ Metric.eball 0 r) :
    HasSum (fun n => p3lE a0 a1 a2 b0 b1 b2 c0 c1 c2 b n * z ^ n)
      ((a0 + a1 * z + a2 * z ^ 2) * deriv (deriv f) z +
        (b0 + b1 * z + b2 * z ^ 2) * deriv f z + (c0 + c1 * z + c2 * z ^ 2) * f z) := by
  have hF := h.hasSum_mul_pow hz
  have hY := h.hasSum_z_mul_deriv hz
  have hD1 := h.deriv_ofScalars.hasSum_mul_pow hz
  have hD2 := h.deriv_ofScalars.deriv_ofScalars.hasSum_mul_pow hz
  have hZ2 := h.deriv_ofScalars.hasSum_z_mul_deriv hz
  have hX : HasSum (fun n : ℕ => (n : ℂ) * (n - 1) * b n * z ^ n)
      (z ^ 2 * deriv (deriv f) z) := by
    have ht := HasSum.mul_pow_shift (c := fun n => (n : ℂ) * (n - 1) * b n)
      (s := z * deriv (deriv f) z) (by
        convert hZ2 using 1
        funext n; push_cast; ring) (by simp)
    convert ht using 1
    ring
  have hY1 := p3l_hasSum_sh hY
  have hF1 := p3l_hasSum_sh hF
  have hF2 := p3l_hasSum_sh hF1
  have hT := (((((((((hD2.mul_left a0).add (hZ2.mul_left a1)).add (hX.mul_left a2)).add
    (hD1.mul_left b0)).add (hY.mul_left b1)).add (hY1.mul_left b2)).add (hF.mul_left c0)).add
    (hF1.mul_left c1)).add (hF2.mul_left c2))
  convert hT using 1
  · funext n
    simp only [p3lE]
    push_cast
    ring
  · ring

/-- Coefficients of a power series vanishing on a ball vanish. -/
lemma p3l_coeff_eq_zero_of_hasSum {e : ℕ → ℂ} {r : ℝ} (hr : 0 < r)
    (h : ∀ z : ℂ, ‖z‖ < r → HasSum (fun n => e n * z ^ n) 0) : e = 0 := by
  have hrad : ENNReal.ofReal r ≤ (ofScalars ℂ e).radius := by
    refine ENNReal.le_of_forall_nnreal_lt fun t ht => ?_
    have ht' : (t : ℝ) < r := by
      rwa [← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_lt_ofReal_iff hr] at ht
    have hs := (h (t : ℂ) (by simpa using ht')).summable.tendsto_atTop_zero.norm
    refine (ofScalars ℂ e).le_radius_of_tendsto (l := 0) ?_
    simpa [ofScalars_norm, norm_mul, norm_pow] using hs
  have hp : HasFPowerSeriesOnBall (fun _ => (0 : ℂ)) (ofScalars ℂ e) 0 (ENNReal.ofReal r) :=
    { r_le := hrad
      r_pos := ENNReal.ofReal_pos.2 hr
      hasSum := fun {y} hy => by
        rw [Metric.eball_ofReal, mem_ball_zero_iff] at hy
        simpa [ofScalars_apply_eq, mul_comm] using h y hy }
  exact (ofScalars_series_eq_zero ℂ).1 hp.hasFPowerSeriesAt.eq_zero


/-- The Frobenius coefficients `f_n` of the solution at `z = 1` (in powers of `z - 1`). -/
def p3lB (m : ℕ) (γ2 c : ℂ) (n : ℕ) : ℂ := p3lH m γ2 c (n + 2)

/-- Uniform geometric bound `C (3/5)^n` of the Frobenius coefficients for `‖c‖ ≤ K`. -/
lemma p3lB_bound (m : ℕ) (γ2 : ℂ) {K : ℝ} (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c : ℂ, ‖c‖ ≤ K → ∀ n, ‖p3lB m γ2 c n‖ ≤ C * (3 / 5) ^ n := by
  obtain ⟨C, hC⟩ := p3lMaj_le m (norm_nonneg γ2) hK
  refine ⟨max C 0, le_max_right _ _, fun c hc n => ?_⟩
  refine (p3lH_le_maj m hc (n + 2)).trans ((hC (n + 2)).trans ?_)
  rw [pow_add]
  have h1 : ((3 : ℝ) / 5) ^ 2 ≤ 1 := by norm_num
  have h2 : (0 : ℝ) ≤ (3 / 5) ^ n := by positivity
  calc C * ((3 / 5) ^ n * (3 / 5) ^ 2) ≤ max C 0 * ((3 / 5) ^ n * (3 / 5) ^ 2) := by
        gcongr; exact le_max_left _ _
    _ ≤ max C 0 * ((3 / 5) ^ n * 1) := by gcongr
    _ = _ := by ring

/-- The Frobenius series `∑ f_n uⁿ`. -/
def p3lF (m : ℕ) (γ2 c : ℂ) (u : ℂ) : ℂ := ∑' n, p3lB m γ2 c n * u ^ n

/-- The solution of the factor equation analytic at `z = 1` with value `1` there. -/
def p3lY (m : ℕ) (γ2 c : ℂ) (z : ℂ) : ℂ := p3lF m γ2 c (z - 1)

/-- A geometric bound `C ρⁿ` gives radius at least `ρ⁻¹`. -/
lemma p3l_le_radius {b : ℕ → ℂ} {C ρ : ℝ} (hρ : 0 < ρ) (hb : ∀ n, ‖b n‖ ≤ C * ρ ^ n) :
    ENNReal.ofReal ρ⁻¹ ≤ (ofScalars ℂ b).radius := by
  rw [ENNReal.ofReal_eq_coe_nnreal (inv_nonneg.2 hρ.le)]
  refine (ofScalars ℂ b).le_radius_of_bound C fun n => ?_
  simp only [ofScalars_norm, NNReal.coe_mk]
  calc ‖b n‖ * ρ⁻¹ ^ n ≤ C * ρ ^ n * ρ⁻¹ ^ n := by gcongr; exact hb n
    _ = C := by rw [mul_assoc, ← mul_pow, mul_inv_cancel₀ hρ.ne', one_pow, mul_one]

/-- The Frobenius series converges on the disc of radius `5/3`. -/
lemma p3lF_hasFPowerSeriesOnBall (m : ℕ) (γ2 c : ℂ) :
    HasFPowerSeriesOnBall (p3lF m γ2 c) (ofScalars ℂ (p3lB m γ2 c)) 0 (ENNReal.ofReal (5 / 3)) := by
  obtain ⟨C, -, hC⟩ := p3lB_bound m γ2 (norm_nonneg c)
  set p := ofScalars ℂ (p3lB m γ2 c)
  have hrad : ENNReal.ofReal (5 / 3) ≤ p.radius := by
    have := p3l_le_radius (b := p3lB m γ2 c) (ρ := 3 / 5) (by norm_num) (hC c le_rfl)
    norm_num at this ⊢
    exact this
  have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal (5 / 3) := by norm_num
  have h := (p.hasFPowerSeriesOnBall (hpos.trans_le hrad)).mono hpos hrad
  have hsum : p.sum = p3lF m γ2 c := by
    funext z
    simp [p, FormalMultilinearSeries.sum, p3lF, mul_comm]
  rwa [hsum] at h

/-- The Frobenius coefficients satisfy the recurrence of the factor equation at `z = 1`. -/
lemma p3lB_rec (m : ℕ) (γ2 c : ℂ) (n : ℕ) :
    p3lE 0 (-2) (-1) (-2 * ((m : ℂ) + 1)) (-2 * ((m : ℂ) + 1)) 0 c (-2 * γ2) (-γ2)
      (p3lB m γ2 c) n = 0 := by
  have hs1 : p3lSh (p3lB m γ2 c) n = p3lH m γ2 c (n + 1) := by
    rcases n with _ | n
    · simp [p3lSh, p3lH]
    · simp [p3lSh, p3lB]
  have hs2 : p3lSh (p3lSh (p3lB m γ2 c)) n = p3lH m γ2 c n := by
    rcases n with _ | _ | n
    · simp [p3lSh, p3lH]
    · simp [p3lSh, p3lH]
    · simp [p3lSh, p3lB]
  simp only [p3lE, hs1, hs2]
  simp only [p3lB]
  have hrec : p3lH m γ2 c (n + 1 + 2) = ((c - (n : ℂ) * (n + 2 * m + 1)) * p3lH m γ2 c (n + 2) -
      2 * γ2 * p3lH m γ2 c (n + 1) - γ2 * p3lH m γ2 c n) / (2 * ((n : ℂ) + 1) * (n + m + 1)) := rfl
  have hD : (2 * ((n : ℂ) + 1) * (n + m + 1)) ≠ 0 := by
    have : (2 * ((n : ℝ) + 1) * (n + m + 1)) ≠ 0 := by positivity
    exact_mod_cast this
  have hm : (2 * ((n : ℂ) + 1) * (n + m + 1)) * p3lH m γ2 c (n + 1 + 2) =
      (c - (n : ℂ) * (n + 2 * m + 1)) * p3lH m γ2 c (n + 2) -
      2 * γ2 * p3lH m γ2 c (n + 1) - γ2 * p3lH m γ2 c n := by
    rw [hrec, mul_div_cancel₀ _ hD]
  linear_combination (-1 : ℂ) * hm

/-- The Frobenius series solves the factor equation in the variable `u = z - 1`. -/
lemma p3lF_ode (m : ℕ) (γ2 c : ℂ) {u : ℂ} (hu : ‖u‖ < 5 / 3) :
    (-2 * u - u ^ 2) * deriv (deriv (p3lF m γ2 c)) u -
      2 * ((m : ℂ) + 1) * (1 + u) * deriv (p3lF m γ2 c) u +
      (c - 2 * γ2 * u - γ2 * u ^ 2) * p3lF m γ2 c u = 0 := by
  have hz : u ∈ Metric.eball (0 : ℂ) (ENNReal.ofReal (5 / 3)) := by
    rw [Metric.eball_ofReal, mem_ball_zero_iff]; exact hu
  have h := p3l_hasSum_op (a0 := 0) (a1 := -2) (a2 := -1) (b0 := -2 * ((m : ℂ) + 1))
    (b1 := -2 * ((m : ℂ) + 1)) (b2 := 0) (c0 := c) (c1 := -2 * γ2) (c2 := -γ2)
    (p3lF_hasFPowerSeriesOnBall m γ2 c) hz
  simp only [p3lB_rec, zero_mul] at h
  have := h.unique hasSum_zero
  linear_combination this

/-- Derivative of a translate. -/
lemma p3lY_hasDerivAt_aux {f : ℂ → ℂ} (z : ℂ) : deriv (fun w => f (w - 1)) z = deriv f (z - 1) :=
  deriv_comp_sub_const (f := f) (a := 1) (x := z)

/-- The Frobenius solution solves the factor equation on the disc `|z - 1| < 5/3`. -/
lemma p3lY_ode (m : ℕ) (γ2 c : ℂ) {z : ℂ} (hz : ‖z - 1‖ < 5 / 3) :
    (1 - z ^ 2) * deriv (deriv (p3lY m γ2 c)) z - 2 * ((m : ℂ) + 1) * z * deriv (p3lY m γ2 c) z +
      (c + γ2 * (1 - z ^ 2)) * p3lY m γ2 c z = 0 := by
  have e1 : deriv (p3lY m γ2 c) = fun w => deriv (p3lF m γ2 c) (w - 1) := by
    funext w; exact p3lY_hasDerivAt_aux (f := p3lF m γ2 c) w
  have e2 : deriv (deriv (p3lY m γ2 c)) z = deriv (deriv (p3lF m γ2 c)) (z - 1) := by
    rw [e1]; exact p3lY_hasDerivAt_aux (f := deriv (p3lF m γ2 c)) z
  rw [e2, e1]
  have h := p3lF_ode m γ2 c hz
  simp only [p3lY]
  linear_combination h


/-- The factor equation `(1-z²) f'' - 2(m+1) z f' + (c + γ²(1-z²)) f = 0` on `U`. -/
def p3lSol (m : ℕ) (γ2 c : ℂ) (U : Set ℂ) (f : ℂ → ℂ) : Prop :=
  ∀ z ∈ U, (1 - z ^ 2) * deriv (deriv f) z - 2 * ((m : ℂ) + 1) * z * deriv f z +
    (c + γ2 * (1 - z ^ 2)) * f z = 0

/-- The Frobenius solution solves the factor equation on `|z - 1| < 5/3`. -/
lemma p3lY_sol (m : ℕ) (γ2 c : ℂ) : p3lSol m γ2 c (Metric.ball 1 (5 / 3)) (p3lY m γ2 c) :=
  fun z hz => p3lY_ode m γ2 c (by simpa [dist_eq_norm] using hz)

/-- `F(0) = 1`. -/
lemma p3lF_zero (m : ℕ) (γ2 c : ℂ) : p3lF m γ2 c 0 = 1 := by
  simp only [p3lF]
  rw [tsum_eq_single 0 (fun n hn => by simp [zero_pow hn])]
  simp [p3lB, p3lH]

/-- `Y(1) = 1`. -/
lemma p3lY_one (m : ℕ) (γ2 c : ℂ) : p3lY m γ2 c 1 = 1 := by
  simp [p3lY, p3lF_zero]

/-- The Frobenius series is analytic on its disc. -/
lemma p3lF_analyticOnNhd (m : ℕ) (γ2 c : ℂ) :
    AnalyticOnNhd ℂ (p3lF m γ2 c) (Metric.ball 0 (5 / 3)) := fun u hu =>
  (p3lF_hasFPowerSeriesOnBall m γ2 c).analyticAt_of_mem (by rwa [Metric.eball_ofReal])

/-- The Frobenius solution is analytic on `|z - 1| < 5/3`. -/
lemma p3lY_analyticOnNhd (m : ℕ) (γ2 c : ℂ) :
    AnalyticOnNhd ℂ (p3lY m γ2 c) (Metric.ball 1 (5 / 3)) := by
  intro z hz
  have h := p3lF_analyticOnNhd m γ2 c (z - 1) (by simpa [dist_eq_norm] using hz)
  exact h.comp (f := fun w : ℂ => w - 1) (by fun_prop)

/-- The normalized coefficient `p` of `f'' = p f' + q f`. -/
def p3lP (m : ℕ) (z : ℂ) : ℂ := 2 * ((m : ℂ) + 1) * z / (1 - z ^ 2)

/-- The normalized coefficient `q` of `f'' = p f' + q f`. -/
def p3lQ (γ2 c : ℂ) (z : ℂ) : ℂ := -(c + γ2 * (1 - z ^ 2)) / (1 - z ^ 2)

/-- The factor equation in the normalized form `f'' = p f' + q f`. -/
lemma p3l_ode_normal {m : ℕ} {γ2 c : ℂ} {U : Set ℂ} {f : ℂ → ℂ} (hf : p3lSol m γ2 c U f)
    {z : ℂ} (hz : z ∈ U) (h1 : 1 - z ^ 2 ≠ 0) :
    deriv (deriv f) z = p3lP m z * deriv f z + p3lQ γ2 c z * f z := by
  have := hf z hz
  simp only [p3lP, p3lQ]
  field_simp
  linear_combination this

/-- Smoothness of `p` away from `±1`. -/
lemma p3lP_contDiffAt (m : ℕ) {z : ℂ} (h1 : 1 - z ^ 2 ≠ 0) : ContDiffAt ℂ ∞ (p3lP m) z := by
  unfold p3lP
  exact ContDiffAt.div (by fun_prop) (by fun_prop) h1

/-- Smoothness of `q` away from `±1`. -/
lemma p3lQ_contDiffAt (γ2 c : ℂ) {z : ℂ} (h1 : 1 - z ^ 2 ≠ 0) :
    ContDiffAt ℂ ∞ (p3lQ γ2 c) z := by
  unfold p3lQ
  exact ContDiffAt.div (by fun_prop) (by fun_prop) h1

/-- Uniqueness for the factor equation on a preconnected open set avoiding `±1`. -/
lemma p3l_eqOn {m : ℕ} {γ2 c : ℂ} {U : Set ℂ} (hU : IsOpen U) (hU' : IsPreconnected U)
    (h1 : ∀ z ∈ U, 1 - z ^ 2 ≠ 0) {f g : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f U)
    (hg : AnalyticOnNhd ℂ g U) (hfs : p3lSol m γ2 c U f) (hgs : p3lSol m γ2 c U g) {x₀ : ℂ}
    (hx₀ : x₀ ∈ U) (h₀ : f x₀ = g x₀) (h₁ : deriv f x₀ = deriv g x₀) : EqOn f g U :=
  ODE.eqOn_of_ode hU hU' hf hg hx₀ (p3lP_contDiffAt m (h1 x₀ hx₀))
    (p3lQ_contDiffAt γ2 c (h1 x₀ hx₀)) (fun z hz => p3l_ode_normal hfs hz (h1 z hz))
    (fun z hz => p3l_ode_normal hgs hz (h1 z hz)) h₀ h₁

/-- Local uniqueness at a regular point. -/
lemma p3l_eventuallyEq {m : ℕ} {γ2 c x₀ : ℂ} {U : Set ℂ} (hU : U ∈ 𝓝 x₀)
    (h1 : 1 - x₀ ^ 2 ≠ 0) {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f x₀)
    (hg : AnalyticAt ℂ g x₀) (hfs : p3lSol m γ2 c U f) (hgs : p3lSol m γ2 c U g)
    (h₀ : f x₀ = g x₀) (h₁ : deriv f x₀ = deriv g x₀) : f =ᶠ[𝓝 x₀] g := by
  have hne : ∀ᶠ z in 𝓝 x₀, 1 - z ^ 2 ≠ 0 :=
    ((continuous_const.sub (continuous_pow 2)).continuousAt.eventually_ne h1)
  exact ODE.eventuallyEq_of_eventuallyEq_ode hf hg (p3lP_contDiffAt m h1)
    (p3lQ_contDiffAt γ2 c h1)
    (by filter_upwards [hU, hne] with z hz hz1 using p3l_ode_normal hfs hz hz1)
    (by filter_upwards [hU, hne] with z hz hz1 using p3l_ode_normal hgs hz hz1) h₀ h₁

/-- Derivative of `f(-z)`. -/
lemma p3l_deriv_comp_neg (f : ℂ → ℂ) (z : ℂ) :
    deriv (fun w => f (-w)) z = -deriv f (-z) := deriv_comp_neg (f := f) (x := z)

/-- The reflection `z ↦ s f(-z)` preserves the factor equation. -/
lemma p3lSol_reflect {m : ℕ} {γ2 c : ℂ} {U : Set ℂ} {f : ℂ → ℂ} (hf : p3lSol m γ2 c U f)
    (s : ℂ) : p3lSol m γ2 c ((fun z => -z) ⁻¹' U) (fun z => s * f (-z)) := by
  intro z hz
  have e1 : deriv (fun w => s * f (-w)) = fun w => -(s * deriv f (-w)) := by
    funext w
    rw [deriv_const_mul_field']
    simp only
    rw [p3l_deriv_comp_neg]; ring
  have e2 : deriv (deriv (fun w => s * f (-w))) z = s * deriv (deriv f) (-z) := by
    rw [e1, deriv.fun_neg, deriv_const_mul_field']
    simp only
    rw [p3l_deriv_comp_neg]; ring
  rw [e2, e1]
  have := hf (-z) hz
  linear_combination s * this


/-- `1 - z² ≠ 0` in the open unit disc. -/
lemma p3l_one_sub_sq_ne_zero {z : ℂ} (hz : ‖z‖ < 1) : 1 - z ^ 2 ≠ 0 := by
  intro h
  have h2 : ‖z‖ ^ 2 = 1 := by
    rw [← norm_pow, show z ^ 2 = 1 by linear_combination -h, norm_one]
  nlinarith [norm_nonneg z]

/-- An entire solution vanishing to first order at `0` vanishes. -/
theorem p3l_eq_zero_of_data {m : ℕ} {γ2 c : ℂ} {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    (hgs : p3lSol m γ2 c univ g) (h0 : g 0 = 0) (h1 : deriv g 0 = 0) : g = 0 := by
  have hA : AnalyticOnNhd ℂ g univ := fun z _ => hg.analyticAt z
  have hB : EqOn g (fun _ => 0) (Metric.ball 0 1) := by
    refine p3l_eqOn (m := m) (γ2 := γ2) (c := c) Metric.isOpen_ball
      (convex_ball _ _).isPreconnected
      (fun z hz => p3l_one_sub_sq_ne_zero (by simpa using hz)) (fun z _ => hA z trivial)
      (fun z _ => analyticAt_const) (fun z _ => hgs z trivial) (fun z _ => by simp)
      (Metric.mem_ball_self one_pos) h0 (by simpa using h1)
  have hev : g =ᶠ[𝓝 0] 0 := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) one_pos] with z hz using hB hz
  funext z
  exact hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (mem_univ 0) hev
    (mem_univ z)

/-- The Wronskian of an entire solution with the Frobenius solution vanishes at `0`. -/
theorem p3l_wronskian {m : ℕ} {γ2 c : ℂ} {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    (hgs : p3lSol m γ2 c univ g) :
    g 0 * deriv (p3lY m γ2 c) 0 = deriv g 0 * p3lY m γ2 c 0 := by
  set Y := p3lY m γ2 c
  set B : Set ℂ := Metric.ball 1 (5 / 3)
  have hg' : Differentiable ℂ (deriv g) := fun z => (hg.analyticAt z).deriv.differentiableAt
  set W : ℂ → ℂ := fun z => (1 - z ^ 2) ^ (m + 1) * (g z * deriv Y z - deriv g z * Y z)
  have hW : ∀ z ∈ B, HasDerivAt W 0 z := by
    intro z hz
    have hY := p3lY_analyticOnNhd m γ2 c z hz
    have d1 := hY.differentiableAt.hasDerivAt
    have d2 := hY.deriv.differentiableAt.hasDerivAt
    have g1 := (hg z).hasDerivAt
    have g2 := (hg' z).hasDerivAt
    have hp : HasDerivAt (fun w : ℂ => (1 - w ^ 2) ^ (m + 1))
        (((m + 1 : ℕ) : ℂ) * (1 - z ^ 2) ^ m * (-(2 * z))) z := by
      have := ((hasDerivAt_pow 2 z).const_sub 1).pow (m + 1)
      convert this using 1; push_cast; ring
    have h := hp.mul ((g1.mul d2).sub (g2.mul d1))
    have eY := p3lY_sol m γ2 c z hz
    have eg := hgs z trivial
    refine h.congr_deriv ?_
    simp only [Pi.sub_apply, Pi.mul_apply]
    push_cast
    linear_combination (1 - z ^ 2) ^ m * (g z * eY - Y z * eg)
  have hc := Metric.isOpen_ball.is_const_of_deriv_eq_zero (f := W)
    (convex_ball (1 : ℂ) (5 / 3)).isPreconnected
    (fun z hz => (hW z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (hW z hz).deriv) (x := 0) (y := 1)
    (by simp; norm_num) (by simp)
  simp only [W] at hc
  norm_num at hc
  linear_combination hc

/-- **Entire solutions force `Y(0) Y'(0) = 0`.** -/
theorem p3l_Y_mul_deriv_eq_zero {m : ℕ} {γ2 c : ℂ} {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    (hgs : p3lSol m γ2 c univ g) (hne : g ≠ 0) :
    p3lY m γ2 c 0 * deriv (p3lY m γ2 c) 0 = 0 := by
  have h1 := p3l_wronskian hg hgs
  have hh : Differentiable ℂ (fun z => 1 * g (-z)) := by
    have := hg.comp differentiable_neg; simpa [Function.comp_def] using this
  have hhs : p3lSol m γ2 c univ (fun z => 1 * g (-z)) := by
    simpa using p3lSol_reflect hgs 1
  have h2 := p3l_wronskian hh hhs
  have e : deriv (fun z => 1 * g (-z)) 0 = -deriv g 0 := by
    simp only [one_mul]; rw [p3l_deriv_comp_neg]; simp
  rw [e] at h2
  simp only [neg_zero, one_mul] at h2
  have ha : g 0 * deriv (p3lY m γ2 c) 0 = 0 := by linear_combination (h1 + h2) / 2
  have hb : deriv g 0 * p3lY m γ2 c 0 = 0 := by linear_combination (h2 - h1) / 2
  by_contra hY
  rcases mul_ne_zero_iff.1 hY with ⟨hY0, hY1⟩
  exact hne (p3l_eq_zero_of_data hg hgs ((mul_eq_zero.1 ha).resolve_right hY1)
    ((mul_eq_zero.1 hb).resolve_right hY0))


/-! ### Superexponential decay from a backward recurrence -/

/-- Iterating a backward recurrence improves a geometric bound by `θ = Aσ² + B/σ²`. -/
lemma p3l_iter {a : ℕ → ℝ} {A B D σ : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hσ : 0 < σ) {J : ℕ}
    (hJ : 2 ≤ J) (hrec : ∀ k ≥ J, a k ≤ A * a (k + 2) + B * a (k - 2))
    (hD : ∀ j, a j ≤ D * σ ^ j) :
    ∀ n k, J + 2 * n ≤ k → a k ≤ D * (A * σ ^ 2 + B / σ ^ 2) ^ n * σ ^ k := by
  intro n
  induction n with
  | zero => intro k _; simpa using hD k
  | succ n ih =>
    intro k hk
    have h1 := ih (k + 2) (by omega)
    have h2 := ih (k - 2) (by omega)
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
    have h3 := hrec (j + 2) (by omega)
    simp only [Nat.add_sub_cancel] at h2 h3
    have hσ2 : σ ^ 2 ≠ 0 := by positivity
    calc a (j + 2) ≤ A * a (j + 2 + 2) + B * a j := h3
      _ ≤ A * (D * (A * σ ^ 2 + B / σ ^ 2) ^ n * σ ^ (j + 2 + 2)) +
          B * (D * (A * σ ^ 2 + B / σ ^ 2) ^ n * σ ^ j) := by gcongr
      _ = D * (A * σ ^ 2 + B / σ ^ 2) ^ (n + 1) * σ ^ (j + 2) := by
          have e : B / σ ^ 2 * σ ^ (j + 2) = B * σ ^ j := by
            rw [pow_add]; field_simp
          rw [pow_succ]
          linear_combination (-(D * (A * σ ^ 2 + B / σ ^ 2) ^ n)) * e

/-- One improvement step of a geometric bound, from `σ` to `σ √((1+σ²)/2)`. -/
lemma p3l_superexp_step {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) {σ D : ℝ} (hσ0 : 0 < σ)
    (hσ1 : σ < 1) (hD : ∀ n, a n ≤ D * σ ^ n)
    (hrec : ∀ ε > 0, ∀ η > 0, ∃ J, 2 ≤ J ∧ ∀ k ≥ J, a k ≤ (1 + ε) * a (k + 2) + η * a (k - 2)) :
    ∃ D', ∀ n, a n ≤ D' * (σ * Real.sqrt ((1 + σ ^ 2) / 2)) ^ n := by
  have hs2 : 0 < 1 - σ ^ 2 := by nlinarith
  obtain ⟨J, hJ, hJr⟩ := hrec ((1 - σ ^ 2) / (4 * σ ^ 2)) (by positivity)
    (σ ^ 2 * (1 - σ ^ 2) / 4) (by positivity)
  set q := (1 + σ ^ 2) / 2
  have hθ : (1 + (1 - σ ^ 2) / (4 * σ ^ 2)) * σ ^ 2 + σ ^ 2 * (1 - σ ^ 2) / 4 / σ ^ 2 = q := by
    simp only [q]; field_simp; ring
  have hL := p3l_iter (by positivity) (by positivity) hσ0 hJ hJr hD
  rw [hθ] at hL
  set t := Real.sqrt q
  have hq0 : 0 < q := by positivity
  have ht0 : 0 < t := Real.sqrt_pos.2 hq0
  have ht1 : t ≤ 1 := Real.sqrt_le_one.2 (by simp only [q]; nlinarith)
  have htq : t ^ 2 = q := Real.sq_sqrt hq0.le
  have hD0 : 0 ≤ D := by simpa using (ha 0).trans (hD 0)
  refine ⟨D / t ^ (J + 1), fun k => ?_⟩
  rw [mul_pow, show D / t ^ (J + 1) * (σ ^ k * t ^ k) = D * σ ^ k * (t ^ k / t ^ (J + 1)) by ring]
  by_cases hk : k < J
  · have : t ^ (J + 1) ≤ t ^ k := pow_le_pow_of_le_one ht0.le ht1 (by omega)
    have h1 : 1 ≤ t ^ k / t ^ (J + 1) := by rw [le_div_iff₀ (by positivity)]; linarith
    calc a k ≤ D * σ ^ k := hD k
      _ = D * σ ^ k * 1 := by ring
      _ ≤ _ := by gcongr
  · set n := (k - J) / 2
    have h := hL n k (by omega)
    have h2 : t ^ (2 * n) * t ^ (J + 1) ≤ t ^ k := by
      rw [← pow_add]; exact pow_le_pow_of_le_one ht0.le ht1 (by omega)
    have h3 : q ^ n ≤ t ^ k / t ^ (J + 1) := by
      rw [le_div_iff₀ (by positivity), ← htq, ← pow_mul]; exact h2
    calc a k ≤ D * q ^ n * σ ^ k := h
      _ = D * σ ^ k * q ^ n := by ring
      _ ≤ _ := by gcongr

/-- **Superexponential decay.** A nonnegative sequence with a geometric bound of ratio `σ < 1`
satisfying `a_k ≤ (1+ε) a_{k+2} + η a_{k-2}` eventually, for all `ε, η > 0`, is bounded by
`C τⁿ` for every `τ > 0`. -/
lemma p3l_superexp {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) {σ₀ D₀ : ℝ} (hσ0 : 0 < σ₀)
    (hσ1 : σ₀ < 1) (hD : ∀ n, a n ≤ D₀ * σ₀ ^ n)
    (hrec : ∀ ε > 0, ∀ η > 0, ∃ J, 2 ≤ J ∧ ∀ k ≥ J, a k ≤ (1 + ε) * a (k + 2) + η * a (k - 2)) :
    ∀ τ > 0, ∃ C, ∀ n, a n ≤ C * τ ^ n := by
  set q₀ := (1 + σ₀ ^ 2) / 2
  have hq₀ : q₀ < 1 := by simp only [q₀]; nlinarith
  have hq₀' : 0 ≤ q₀ := by positivity
  have key : ∀ N : ℕ, ∃ σ D : ℝ, 0 < σ ∧ σ ≤ σ₀ ∧ σ ^ 2 ≤ σ₀ ^ 2 * q₀ ^ N ∧
      ∀ n, a n ≤ D * σ ^ n := by
    intro N
    induction N with
    | zero => exact ⟨σ₀, D₀, hσ0, le_rfl, by simp, hD⟩
    | succ N ih =>
      obtain ⟨σ, D, h0, h1, h2, h3⟩ := ih
      obtain ⟨D', hD'⟩ := p3l_superexp_step ha h0 (h1.trans_lt hσ1) h3 hrec
      have hq : 0 ≤ (1 + σ ^ 2) / 2 := by positivity
      have hqle : (1 + σ ^ 2) / 2 ≤ q₀ := by
        simp only [q₀]; nlinarith
      have hs1 : Real.sqrt ((1 + σ ^ 2) / 2) ≤ 1 :=
        Real.sqrt_le_one.2 (hqle.trans hq₀.le)
      refine ⟨σ * Real.sqrt ((1 + σ ^ 2) / 2), D', ?_, ?_, ?_, hD'⟩
      · exact mul_pos h0 (Real.sqrt_pos.2 (by positivity))
      · nlinarith [Real.sqrt_nonneg ((1 + σ ^ 2) / 2)]
      · rw [mul_pow, Real.sq_sqrt hq, pow_succ]
        calc σ ^ 2 * ((1 + σ ^ 2) / 2) ≤ σ₀ ^ 2 * q₀ ^ N * q₀ := by gcongr
          _ = _ := by ring
  intro τ hτ
  have hlim : Tendsto (fun N => σ₀ ^ 2 * q₀ ^ N) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq₀' hq₀).const_mul (σ₀ ^ 2)
  obtain ⟨N, hN⟩ := (hlim.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < τ ^ 2))).exists
  obtain ⟨σ, D, h0, -, h2, h3⟩ := key N
  have hστ : σ < τ := lt_of_pow_lt_pow_left₀ 2 hτ.le (h2.trans_lt hN)
  have hD0 : 0 ≤ D := by simpa using (ha 0).trans (h3 0)
  exact ⟨D, fun n => (h3 n).trans (by gcongr)⟩


/-! ### Entire solutions from solutions on a disc of radius `> 1` -/

/-- The factor equation is preserved by equality on an open set. -/
lemma p3lSol_congr {m : ℕ} {γ2 c : ℂ} {U : Set ℂ} (hU : IsOpen U) {f g : ℂ → ℂ}
    (h : EqOn f g U) (hf : p3lSol m γ2 c U f) : p3lSol m γ2 c U g := by
  intro z hz
  have he : f =ᶠ[𝓝 z] g := by
    filter_upwards [hU.mem_nhds hz] with w hw using h hw
  rw [← he.deriv_eq, ← he.deriv.deriv_eq, ← h hz]
  exact hf z hz

/-- A one-variable power series is `ofScalars` of its coefficients. -/
lemma p3l_eq_ofScalars_coeff (p : FormalMultilinearSeries ℂ ℂ ℂ) :
    p = ofScalars ℂ (fun n => p.coeff n) := by
  ext n
  rw [apply_eq_prod_smul_coeff]
  simp [ofScalars, mul_comm]

/-- A solution analytic on a disc of radius `6/5` about `0` extends to an entire solution. -/
lemma p3l_entire_of_ball {m : ℕ} {γ2 c : ℂ} {G : ℂ → ℂ}
    (hG : DifferentiableOn ℂ G (Metric.closedBall 0 (6 / 5)))
    (hode : p3lSol m γ2 c (Metric.ball 0 (2 / 3)) G) :
    ∃ E : ℂ → ℂ, Differentiable ℂ E ∧ p3lSol m γ2 c univ E ∧
      EqOn E G (Metric.ball 0 (6 / 5)) := by
  have hp0 := hG.hasFPowerSeriesOnBall (R := 6 / 5) (by norm_num)
  set a : ℕ → ℂ := fun n => (cauchyPowerSeries G 0 (6 / 5)).coeff n
  have hp : HasFPowerSeriesOnBall G (ofScalars ℂ a) 0 ((6 / 5 : NNReal) : ℝ≥0∞) := by
    simp only [a]; rw [← p3l_eq_ofScalars_coeff]; exact hp0
  -- the coefficient recurrence
  have hE : p3lE 1 0 (-1) 0 (-2 * ((m : ℂ) + 1)) 0 (c + γ2) 0 (-γ2) a = 0 := by
    refine p3l_coeff_eq_zero_of_hasSum (r := 2 / 3) (by norm_num) fun z hz => ?_
    have hz' : z ∈ Metric.eball (0 : ℂ) ((6 / 5 : NNReal) : ℝ≥0∞) := by
      rw [Metric.mem_eball, edist_zero_right]
      have : ‖z‖₊ < (6 / 5 : NNReal) := by
        rw [← NNReal.coe_lt_coe]; simp only [coe_nnnorm]; push_cast; linarith
      exact_mod_cast this
    have h := p3l_hasSum_op (a0 := 1) (a1 := 0) (a2 := -1) (b0 := 0)
      (b1 := -2 * ((m : ℂ) + 1)) (b2 := 0) (c0 := c + γ2) (c1 := 0) (c2 := -γ2) hp hz'
    convert h using 1
    have := hode z (by simpa using hz)
    linear_combination -this
  -- geometric decay
  have hrad : ((6 / 5 : NNReal) : ℝ≥0∞) ≤ (ofScalars ℂ a).radius := hp.r_le
  obtain ⟨C₀, -, hC₀⟩ := (ofScalars ℂ a).norm_mul_pow_le_of_lt_radius (r := 11 / 10)
    (lt_of_lt_of_le (ENNReal.coe_lt_coe.2 (by rw [← NNReal.coe_lt_coe]; norm_num)) hrad)
  have hD : ∀ n, ‖a n‖ ≤ C₀ * (10 / 11) ^ n := by
    intro n
    have h := hC₀ n
    rw [ofScalars_norm] at h
    have e : ((11 / 10 : NNReal) : ℝ) = 11 / 10 := by norm_num
    rw [e] at h
    calc ‖a n‖ = ‖a n‖ * (11 / 10) ^ n * (10 / 11) ^ n := by
          rw [mul_assoc, ← mul_pow]; norm_num
      _ ≤ C₀ * (10 / 11) ^ n := by gcongr
  have hrec : ∀ ε > 0, ∀ η > 0, ∃ J, 2 ≤ J ∧ ∀ k ≥ J,
      ‖a k‖ ≤ (1 + ε) * ‖a (k + 2)‖ + η * ‖a (k - 2)‖ := by
    intro ε hε η hη
    set L := ‖c + γ2‖
    set X : ℝ := (5 + (1 + ε) * L) / ε + ‖γ2‖ / η + L
    refine ⟨⌈X⌉₊ + 2, by omega, fun k hk => ?_⟩
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
    have hXk : X + 2 ≤ ((j + 2 : ℕ) : ℝ) := by
      have := Nat.le_ceil X
      have : ((⌈X⌉₊ + 2 : ℕ) : ℝ) ≤ ((j + 2 : ℕ) : ℝ) := by exact_mod_cast hk
      push_cast at this ⊢; linarith
    set K : ℝ := ((j + 2 : ℕ) : ℝ) with hK
    have hL0 : 0 ≤ L := norm_nonneg _
    have hX0 : (5 + (1 + ε) * L) / ε ≤ X := by
      have : 0 ≤ ‖γ2‖ / η := by positivity
      simp only [X]; linarith
    have hX1 : ‖γ2‖ / η + L ≤ X := by
      have : 0 ≤ (5 + (1 + ε) * L) / ε := by positivity
      simp only [X]; linarith
    have hK1 : 1 ≤ K := by
      have : 0 ≤ X := le_trans (by positivity) hX0
      linarith
    have hKK : K ≤ K ^ 2 := by nlinarith
    have hpos : 0 < K ^ 2 - L := by
      have : L ≤ X := by
        have : 0 ≤ ‖γ2‖ / η := by positivity
        linarith
      nlinarith
    have hA : (K + 1) * (K + 2) ≤ (1 + ε) * (K ^ 2 - L) := by
      have h1 : 5 + (1 + ε) * L ≤ ε * K := by
        rw [div_le_iff₀ hε] at hX0; nlinarith
      have hK0 : 0 ≤ K := by linarith
      nlinarith [mul_le_mul_of_nonneg_left h1 hK0,
        mul_le_mul_of_nonneg_left hK1 (by positivity : (0 : ℝ) ≤ (1 + ε) * L)]
    have hB : ‖γ2‖ ≤ η * (K ^ 2 - L) := by
      have h1 : ‖γ2‖ / η ≤ K ^ 2 - L := by linarith
      rwa [div_le_iff₀ hη, mul_comm] at h1
    -- the recurrence at index `j + 2`
    have hk := congrFun hE (j + 2)
    simp only [p3lE, p3lSh, Pi.zero_apply] at hk
    have hDk : ((K : ℂ) * (K - 1) + 2 * ((m : ℂ) + 1) * K - (c + γ2)) * a (j + 2) =
        ((K : ℂ) + 1) * (K + 2) * a (j + 2 + 2) - γ2 * a j := by
      simp only [hK]; push_cast at hk ⊢; linear_combination -hk
    have hnD : K ^ 2 - L ≤ ‖(K : ℂ) * (K - 1) + 2 * ((m : ℂ) + 1) * K - (c + γ2)‖ := by
      have e : (K : ℂ) * (K - 1) + 2 * ((m : ℂ) + 1) * K =
          ((K * (K - 1) + 2 * ((m : ℝ) + 1) * K : ℝ) : ℂ) := by push_cast; ring
      rw [e]
      refine le_trans ?_ (norm_sub_norm_le _ _)
      rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      have : 0 ≤ (m : ℝ) := by positivity
      nlinarith
    have hn := congrArg norm hDk
    rw [norm_mul] at hn
    have hup : ‖((K : ℂ) + 1) * (K + 2) * a (j + 2 + 2) - γ2 * a j‖ ≤
        (K + 1) * (K + 2) * ‖a (j + 2 + 2)‖ + ‖γ2‖ * ‖a j‖ := by
      refine (norm_sub_le _ _).trans (le_of_eq ?_)
      have e1 : ‖(K : ℂ) + 1‖ = K + 1 := by
        rw [show (K : ℂ) + 1 = ((K + 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
          Real.norm_of_nonneg (by positivity)]
      have e2 : ‖(K : ℂ) + 2‖ = K + 2 := by
        rw [show (K : ℂ) + 2 = ((K + 2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
          Real.norm_of_nonneg (by positivity)]
      rw [norm_mul, norm_mul, norm_mul, e1, e2]
    have : (K ^ 2 - L) * ‖a (j + 2)‖ ≤
        (K ^ 2 - L) * ((1 + ε) * ‖a (j + 2 + 2)‖ + η * ‖a (j + 2 - 2)‖) := by
      simp only [Nat.add_sub_cancel]
      calc (K ^ 2 - L) * ‖a (j + 2)‖ ≤ _ * ‖a (j + 2)‖ := by gcongr
        _ ≤ _ := hn.le.trans hup
        _ ≤ (1 + ε) * (K ^ 2 - L) * ‖a (j + 2 + 2)‖ + η * (K ^ 2 - L) * ‖a j‖ := by gcongr
        _ = _ := by ring
    exact le_of_mul_le_mul_left this hpos
  have hsup := p3l_superexp (fun n => norm_nonneg (a n)) (by norm_num) (by norm_num) hD hrec
  -- infinite radius
  have hinf : (ofScalars ℂ a).radius = ⊤ := by
    refine ENNReal.eq_top_of_forall_nnreal_le fun r => ?_
    obtain ⟨C, hC⟩ := hsup (1 / ((r : ℝ) + 1)) (by positivity)
    refine (ofScalars ℂ a).le_radius_of_bound C fun n => ?_
    rw [ofScalars_norm]
    have hr : (0 : ℝ) ≤ r := r.2
    calc ‖a n‖ * (r : ℝ) ^ n ≤ C * (1 / ((r : ℝ) + 1)) ^ n * (r : ℝ) ^ n := by
          gcongr; exact hC n
      _ = C * ((r : ℝ) / ((r : ℝ) + 1)) ^ n := by rw [div_pow, div_pow]; ring
      _ ≤ C * 1 := by
          have hC0 : 0 ≤ C := by simpa using (norm_nonneg (a 0)).trans (hC 0)
          gcongr
          exact pow_le_one₀ (by positivity) ((div_le_one (by positivity)).2 (by linarith))
      _ = C := mul_one C
  set E := (ofScalars ℂ a).sum
  have hEs : HasFPowerSeriesOnBall E (ofScalars ℂ a) 0 ⊤ := by
    have := (ofScalars ℂ a).hasFPowerSeriesOnBall (by rw [hinf]; exact ENNReal.zero_lt_top)
    rwa [hinf] at this
  have hEd : Differentiable ℂ E := fun z =>
    (hEs.analyticAt_of_mem (by simp)).differentiableAt
  refine ⟨E, hEd, fun z _ => ?_, fun z hz => ?_⟩
  · have h := p3l_hasSum_op (a0 := 1) (a1 := 0) (a2 := -1) (b0 := 0)
      (b1 := -2 * ((m : ℂ) + 1)) (b2 := 0) (c0 := c + γ2) (c1 := 0) (c2 := -γ2) hEs
      (show z ∈ Metric.eball (0 : ℂ) ⊤ by simp)
    rw [hE] at h
    simp only [Pi.zero_apply, zero_mul] at h
    have := h.unique hasSum_zero
    linear_combination this
  · have hz' : z ∈ Metric.eball (0 : ℂ) ((6 / 5 : NNReal) : ℝ≥0∞) := by
      rw [Metric.mem_eball, edist_zero_right]
      have hz2 : ‖z‖ < 6 / 5 := by simpa using hz
      have : ‖z‖₊ < (6 / 5 : NNReal) := by
        rw [← NNReal.coe_lt_coe]; simp only [coe_nnnorm]; push_cast; linarith
      exact_mod_cast this
    exact (hEs.hasSum_mul_pow (by simp)).unique (hp.hasSum_mul_pow hz')


/-- Restriction of the factor equation to a subset. -/
lemma p3lSol_mono {m : ℕ} {γ2 c : ℂ} {U V : Set ℂ} {f : ℂ → ℂ} (hUV : U ⊆ V)
    (hf : p3lSol m γ2 c V f) : p3lSol m γ2 c U f := fun z hz => hf z (hUV hz)

/-- `‖z - 1‖² = ‖z‖² - 2 Re z + 1`. -/
lemma p3l_norm_sub_one_sq (z : ℂ) : ‖z - 1‖ ^ 2 = ‖z‖ ^ 2 - 2 * z.re + 1 := by
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero]
  ring

/-- Points of the closed disc of radius `6/5` with `Re z ≥ 0` lie in `|z - 1| < 5/3`. -/
lemma p3l_norm_sub_one_lt {z : ℂ} (hz : ‖z‖ ≤ 6 / 5) (hre : 0 ≤ z.re) : ‖z - 1‖ < 5 / 3 := by
  have h := p3l_norm_sub_one_sq z
  by_contra hc
  push Not at hc
  have : (5 / 3 : ℝ) ^ 2 ≤ ‖z - 1‖ ^ 2 := by gcongr
  nlinarith [norm_nonneg z]

/-- Membership in the reflected disc. -/
lemma p3l_mem_neg_ball {z : ℂ} : z ∈ (fun w : ℂ => -w) ⁻¹' Metric.ball 1 (5 / 3) ↔
    ‖z + 1‖ < 5 / 3 := by
  simp [dist_eq_norm]

/-- **Construction of an entire solution** when `Y(0) Y'(0) = 0`: the Frobenius solution at `1`
and its reflection at `-1` glue to a solution on a disc of radius `> 1`. -/
theorem p3l_exists_entire {m : ℕ} {γ2 c : ℂ}
    (h : p3lY m γ2 c 0 * deriv (p3lY m γ2 c) 0 = 0) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ p3lSol m γ2 c univ g ∧ g ≠ 0 := by
  set Y := p3lY m γ2 c with hYdef
  obtain ⟨s, hs0, hs1⟩ : ∃ s : ℂ, s * Y 0 = Y 0 ∧ -s * deriv Y 0 = deriv Y 0 := by
    rcases mul_eq_zero.1 h with h0 | h1
    · exact ⟨-1, by rw [h0]; ring, by ring⟩
    · exact ⟨1, by ring, by rw [h1]; ring⟩
  set Yt : ℂ → ℂ := fun z => s * Y (-z)
  set Bp : Set ℂ := Metric.ball 1 (5 / 3)
  set Bm : Set ℂ := (fun w : ℂ => -w) ⁻¹' Bp
  have hBm : Bm = Metric.ball (-1) (5 / 3) := by
    ext z; rw [p3l_mem_neg_ball]
    simp [dist_eq_norm]
  set W := Bp ∩ Bm
  have hWo : IsOpen W := Metric.isOpen_ball.inter (by rw [hBm]; exact Metric.isOpen_ball)
  have hWc : IsPreconnected W :=
    ((convex_ball _ _).inter (by rw [hBm]; exact convex_ball _ _)).isPreconnected
  have hW1 : ∀ z ∈ W, 1 - z ^ 2 ≠ 0 := by
    rintro z ⟨hz1, hz2⟩ h0
    have : z = 1 ∨ z = -1 := by
      have : (z - 1) * (z + 1) = 0 := by linear_combination -h0
      rcases mul_eq_zero.1 this with h | h
      · left; linear_combination h
      · right; linear_combination h
    rw [hBm] at hz2
    rcases this with rfl | rfl
    · norm_num [dist_eq_norm] at hz2
    · simp only [Bp, Metric.mem_ball, dist_eq_norm] at hz1
      norm_num at hz1
  have hYa := p3lY_analyticOnNhd m γ2 c
  have hYta : AnalyticOnNhd ℂ Yt Bm := fun z hz =>
    analyticAt_const.mul ((hYa (-z) hz).comp (f := fun w : ℂ => -w) (by fun_prop))
  have hYs := p3lY_sol m γ2 c
  have hYts : p3lSol m γ2 c Bm Yt := p3lSol_reflect hYs s
  have h0W : (0 : ℂ) ∈ W := ⟨by simp [Bp]; norm_num, by rw [hBm]; simp; norm_num⟩
  have hdYt : deriv Yt 0 = -s * deriv Y 0 := by
    simp only [Yt]
    rw [deriv_const_mul_field']
    beta_reduce
    rw [p3l_deriv_comp_neg]; simp
  have heq : EqOn Y Yt W :=
    p3l_eqOn hWo hWc hW1 (fun z hz => hYa z hz.1) (fun z hz => hYta z hz.2)
      (p3lSol_mono inter_subset_left hYs) (p3lSol_mono inter_subset_right hYts) h0W
      (by simp [Yt, hs0]) (by rw [hdYt, hs1])
  set G : ℂ → ℂ := fun z => if 0 ≤ z.re then Y z else Yt z
  have hGW : EqOn G Y W := by
    intro z hz
    simp only [G]
    split_ifs
    · rfl
    · exact (heq hz).symm
  have hGd : DifferentiableOn ℂ G (Metric.closedBall 0 (6 / 5)) := by
    intro z hz
    have hz' : ‖z‖ ≤ 6 / 5 := by simpa using hz
    refine DifferentiableAt.differentiableWithinAt ?_
    rcases lt_trichotomy z.re 0 with hr | hr | hr
    · have hm : -z ∈ Bp := by
        have := p3l_norm_sub_one_lt (z := -z) (by simpa using hz') (by simp; linarith)
        simpa [Bp, dist_eq_norm] using this
      have hev : G =ᶠ[𝓝 z] Yt := by
        filter_upwards [Complex.continuous_re.continuousAt.eventually (gt_mem_nhds hr)]
          with w hw
        simp only [G, ite_eq_right_iff]; exact fun h => absurd h (not_le.2 hw)
      exact (hYta z hm).differentiableAt.congr_of_eventuallyEq hev
    · have hzW : z ∈ W := by
        refine ⟨?_, ?_⟩
        · have := p3l_norm_sub_one_lt hz' hr.ge
          simpa [Bp, dist_eq_norm] using this
        · show -z ∈ Bp
          have := p3l_norm_sub_one_lt (z := -z) (by simpa using hz') (by simp; linarith)
          simpa [Bp, dist_eq_norm] using this
      have hev : G =ᶠ[𝓝 z] Y := by
        filter_upwards [hWo.mem_nhds hzW] with w hw using hGW hw
      exact (hYa z hzW.1).differentiableAt.congr_of_eventuallyEq hev
    · have hm : z ∈ Bp := by
        have := p3l_norm_sub_one_lt hz' hr.le
        simpa [Bp, dist_eq_norm] using this
      have hev : G =ᶠ[𝓝 z] Y := by
        filter_upwards [Complex.continuous_re.continuousAt.eventually (lt_mem_nhds hr)]
          with w hw
        simp only [G, ite_eq_left_iff]; exact fun h => absurd hw.le h
      exact (hYa z hm).differentiableAt.congr_of_eventuallyEq hev
  have hsub : Metric.ball (0 : ℂ) (2 / 3) ⊆ W := by
    intro z hz
    have hz' : ‖z‖ < 2 / 3 := by simpa using hz
    refine ⟨?_, ?_⟩
    · simp only [Bp, Metric.mem_ball, dist_eq_norm]
      calc ‖z - 1‖ ≤ ‖z‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ < 5 / 3 := by simp; linarith
    · show -z ∈ Bp
      simp only [Bp, Metric.mem_ball, dist_eq_norm]
      calc ‖-z - 1‖ ≤ ‖-z‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ < 5 / 3 := by simp; linarith
  have hGs : p3lSol m γ2 c (Metric.ball 0 (2 / 3)) G :=
    p3lSol_congr Metric.isOpen_ball (fun z hz => (hGW (hsub hz)).symm)
      (p3lSol_mono (hsub.trans inter_subset_left) hYs)
  obtain ⟨E, hEd, hEs, hEG⟩ := p3l_entire_of_ball hGd hGs
  refine ⟨E, hEd, hEs, fun hE0 => ?_⟩
  have hY0 : Y =ᶠ[𝓝 0] 0 := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 2 / 3)] with z hz
    have h1 := hEG (Metric.ball_subset_ball (by norm_num) hz)
    rw [hE0, hGW (hsub hz)] at h1
    simpa using h1.symm
  have := hYa.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball _ _).isPreconnected
    (by simp; norm_num) hY0 (Metric.mem_ball_self (by norm_num) : (1 : ℂ) ∈ Bp)
  simp [p3lY_one] at this


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

