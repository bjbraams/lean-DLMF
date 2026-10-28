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
# Entire spheroidal eigenfunctions from series

Spectral coefficient recurrences, superexponential decay and extension of local spheroidal
solutions to entire functions.

Source references and common attribution are retained in
`DLMF.Spheroidal.P3lSpectrum`.
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

end DLMF.Spheroidal
end
