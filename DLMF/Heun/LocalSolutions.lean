/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Heun.Basic
public import DLMF.Heun.Equation
public import DLMF.Hypergeometric.Series

/-!
# Basic solutions of Heun's equation (DLMF §31.3)

`heunLocal a q α β γ δ z = ∑ c_j z^j` is DLMF's `Hl(a, q; α, β, γ, δ; z)` (31.3.1), with the
coefficients `c_j` of the three-term recurrence 31.3.2–31.3.4 (`heunLocalCoeff`). This file
states

* the recurrence (31.3.2, 31.3.3, proved from the definition), `Hl(0) = 1` (proved), the
  convergence of the series in `|z| < min(1, |a|)` and the characterization of `Hl` as the
  solution with exponent `0` and value `1` at the origin (§31.3(i), admitted);
* the second solution at `0` (31.3.5) and the Fuchs–Frobenius solutions at `1`, `a`, `∞`
  (31.3.6–31.3.11), each as a solution of Heun's equation on the disk of convergence of the `Hl`
  involved (admitted);
* the equivalent expressions 31.3.12 (proved, for all `z`: the two series agree term by term)
  and 31.3.13 (admitted).

Domains: the principal powers `z^{1-γ}`, `(1-z)^{1-δ}`, `((a-z)/(a-1))^{1-ε}`, `z^{-α}` are used
where their bases lie in `slitPlane`. Exceptional parameters: DLMF requires
`γ ∉ {0, -1, -2, …}` for 31.3.1 and `γ ∉ {1, 2, 3, …}` for 31.3.5; at the other singularities
the corresponding restrictions on `δ`, `ε` and `α - β` are imposed. For `γ ∈ ℤ` DLMF only remarks
(§31.3(i), last paragraph) that a second solution can be constructed as in §2.7(i), in general
with a logarithmic singularity; that remark is not acquired. The remarks of §31.3(iii) on the
192 = 8 · 24 equivalent local solutions are informal (not acquired beyond 31.3.12–31.3.13).

Every formula was checked numerically (mpmath, coefficients from the recurrence, ODE residuals
below `10⁻²⁹` at sample points for complex parameters).
-/

@[expose] public section

open Complex Filter Set FormalMultilinearSeries
open scoped Topology Real

noncomputable section

namespace DLMF.Heun

variable {a q α β γ δ ε : ℂ}

/-! ### The recurrence -/

@[simp] theorem heunLocalCoeff_zero : heunLocalCoeff a q α β γ δ 0 = 1 := rfl

@[simp] theorem heunLocalCoeff_one : heunLocalCoeff a q α β γ δ 1 = q / (a * γ) := rfl

/-- DLMF 31.3.2: `aγc₁ - qc₀ = 0` (for `aγ ≠ 0`). -/
@[dlmf 31.3.E2]
theorem heunLocalCoeff_rec_zero (ha : a ≠ 0) (hγ : γ ≠ 0) :
    a * γ * heunLocalCoeff a q α β γ δ 1 - q * heunLocalCoeff a q α β γ δ 0 = 0 := by
  simp only [heunLocalCoeff_one, heunLocalCoeff_zero]
  field_simp
  ring

/-- DLMF 31.3.3: `R_j c_{j+1} - (Q_j + q) c_j + P_j c_{j-1} = 0` for `j ≥ 1` (for `R_j ≠ 0`, that
is `a ≠ 0` and `γ ≠ -j`). -/
@[dlmf 31.3.E3]
theorem heunLocalCoeff_rec {j : ℕ} (hj : 1 ≤ j) (hR : heunRecR a γ j ≠ 0) :
    heunRecR a γ j * heunLocalCoeff a q α β γ δ (j + 1) -
      (heunRecQ a α β γ δ j + q) * heunLocalCoeff a q α β γ δ j +
      heunRecP α β j * heunLocalCoeff a q α β γ δ (j - 1) = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  rw [show k + 1 + 1 = k + 2 from rfl, heunLocalCoeff, mul_div_cancel₀ _ hR]
  ring

/-- `Hl(a, q; α, β, γ, δ; 0) = 1` (DLMF §31.3(i): the solution "assumes the value 1" at `0`). -/
@[dlmf 31.3.i]
theorem heunLocal_zero : heunLocal a q α β γ δ 0 = 1 := by
  rw [heunLocal, tsum_eq_single 0]
  · simp
  · intro j hj
    simp [zero_pow hj]

/-! ### Convergence of the Maclaurin series of `Hl` -/

/-- `(u m + v)/(a (m + 1)(m + γ)) → 0`. -/
lemma p1h_tendsto_lin_div (u v a γ : ℂ) (ha : a ≠ 0) :
    Tendsto (fun n : ℕ => (u * n + v) / (a * ((n : ℂ) + 1) * ((n : ℂ) + γ))) atTop (𝓝 0) := by
  have hw : Tendsto (fun n : ℕ => ((n : ℂ))⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_nhds_zero_nat
  have h := ((tendsto_const_nhds (x := u)).add ((tendsto_const_nhds (x := v)).mul hw)).mul hw
    |>.div (((tendsto_const_nhds (x := a)).mul ((tendsto_const_nhds (x := (1 : ℂ))).add hw)).mul
      ((tendsto_const_nhds (x := (1 : ℂ))).add ((tendsto_const_nhds (x := γ)).mul hw)))
      (by simp [ha])
  simp only [mul_zero, add_zero, zero_div] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  simp only [Pi.div_apply]
  field_simp

/-- One step of the majorant argument for a three-term recurrence. -/
lemma p1h_step {a A B c₀ c c' : ℂ} {η δ r : ℝ} (hη : 0 < η) (hδ : 0 ≤ δ)
    (h : c' = A * c + B * c₀) (h1 : ‖A + B - 1‖ ≤ η * δ / 2) (h2 : ‖B + 1 / a‖ ≤ δ / 2)
    (hr1 : 1 / ‖a‖ + δ ≤ r) (hr2 : 1 + η * (1 / ‖a‖ + δ) ≤ r) :
    max (η * ‖c'‖) ‖c' - c‖ ≤ r * max (η * ‖c‖) ‖c - c₀‖ := by
  set N := max (η * ‖c‖) ‖c - c₀‖
  have hc : η * ‖c‖ ≤ N := le_max_left _ _
  have hx : ‖c - c₀‖ ≤ N := le_max_right _ _
  have hN : 0 ≤ N := (norm_nonneg _).trans hx
  have he : c' - c = (c - c₀) / a + ((A + B - 1) * c - (B + 1 / a) * (c - c₀)) := by
    rw [h]; ring
  have hea : ‖(A + B - 1) * c - (B + 1 / a) * (c - c₀)‖ ≤ δ * N := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    have e1 : ‖A + B - 1‖ * ‖c‖ ≤ δ / 2 * N := by
      have : ‖A + B - 1‖ * (η * ‖c‖) ≤ η * δ / 2 * N :=
        mul_le_mul h1 hc (by positivity) (by positivity)
      nlinarith
    have e2 : ‖B + 1 / a‖ * ‖c - c₀‖ ≤ δ / 2 * N :=
      mul_le_mul h2 hx (norm_nonneg _) (by positivity)
    linarith
  have hx' : ‖c' - c‖ ≤ (1 / ‖a‖ + δ) * N := by
    rw [he]
    refine (norm_add_le _ _).trans ?_
    rw [norm_div]
    have : ‖c - c₀‖ / ‖a‖ ≤ 1 / ‖a‖ * N := by
      rw [div_eq_mul_one_div, mul_comm]
      exact mul_le_mul_of_nonneg_left hx (by positivity)
    linarith
  have hc' : η * ‖c'‖ ≤ r * N := by
    have : c' = c + (c' - c) := by ring
    rw [this]
    calc η * ‖c + (c' - c)‖ ≤ η * ‖c‖ + η * ‖c' - c‖ := by
          rw [← mul_add]; exact mul_le_mul_of_nonneg_left (norm_add_le _ _) hη.le
      _ ≤ N + η * ((1 / ‖a‖ + δ) * N) := by gcongr
      _ = (1 + η * (1 / ‖a‖ + δ)) * N := by ring
      _ ≤ r * N := by gcongr
  refine max_le hc' (hx'.trans ?_)
  gcongr

/-- The recurrence of `heunLocalCoeff` in the form `c_{n+2} = A_n c_{n+1} + B_n c_n`. -/
lemma p1h_coeff_add_two (a q α β γ δ : ℂ) (n : ℕ) :
    heunLocalCoeff a q α β γ δ (n + 2) =
      (heunRecQ a α β γ δ (n + 1) + q) / heunRecR a γ (n + 1) *
          heunLocalCoeff a q α β γ δ (n + 1) +
        -heunRecP α β (n + 1) / heunRecR a γ (n + 1) * heunLocalCoeff a q α β γ δ n := by
  rw [heunLocalCoeff]; ring

lemma p1h_eventually_R_ne (a γ : ℂ) (ha : a ≠ 0) :
    ∀ᶠ n : ℕ in atTop, heunRecR a γ (n + 1) ≠ 0 := by
  obtain ⟨N, hN⟩ := exists_nat_gt ‖γ‖
  filter_upwards [eventually_ge_atTop N] with n hn
  unfold heunRecR
  refine mul_ne_zero (mul_ne_zero ha (by norm_cast)) fun h => ?_
  have h' : γ = -(((n + 1 : ℕ) : ℂ)) := by linear_combination h
  have : ‖γ‖ = (n + 1 : ℝ) := by rw [h', norm_neg, Complex.norm_natCast]; push_cast; ring
  have : (N : ℝ) ≤ n := by exact_mod_cast hn
  linarith

lemma p1h_tendsto_A_add_B (a q α β γ δ : ℂ) (ha : a ≠ 0) :
    Tendsto (fun n : ℕ => (heunRecQ a α β γ δ (n + 1) + q) / heunRecR a γ (n + 1) +
      -heunRecP α β (n + 1) / heunRecR a γ (n + 1) - 1) atTop (𝓝 0) := by
  have h := (p1h_tendsto_lin_div (a * δ - 2 * a - δ + 2)
    (-a * γ - α * β + α + β + q - 1) a γ ha).comp (tendsto_add_atTop_nat 1)
  refine h.congr' ?_
  filter_upwards [p1h_eventually_R_ne a γ ha] with n hn
  simp only [Function.comp_apply]
  rw [eq_comm, ← add_div, div_sub_one hn]
  unfold heunRecR heunRecQ heunRecP heunEps
  push_cast
  ring_nf

lemma p1h_tendsto_B (a α β γ : ℂ) (ha : a ≠ 0) :
    Tendsto (fun n : ℕ => -heunRecP α β (n + 1) / heunRecR a γ (n + 1) + 1 / a) atTop
      (𝓝 0) := by
  have h := (p1h_tendsto_lin_div ((-a * α - a * β + a * γ + 3 * a) / a)
    ((-a * α * β + a * α + a * β + a * γ - a) / a) a γ ha).comp (tendsto_add_atTop_nat 1)
  refine h.congr' ?_
  filter_upwards [p1h_eventually_R_ne a γ ha] with n hn
  simp only [Function.comp_apply]
  rw [eq_comm, div_add_div _ _ hn ha]
  unfold heunRecR heunRecP at *
  field_simp
  push_cast
  ring


theorem p1h_radius_pos {a : ℂ} (ha : a ≠ 0) : 0 < heunLocalRadius a :=
  lt_min one_pos (norm_pos_iff.2 ha)

/-- Majorant bound: `∑ ‖c_n‖ tⁿ` converges for `0 ≤ t < min(1, |a|)`. -/
lemma p1h_summable_norm {a q α β γ δ : ℂ} (ha : a ≠ 0) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : t < heunLocalRadius a) :
    Summable (fun n => ‖heunLocalCoeff a q α β γ δ n‖ * t ^ n) := by
  set c := heunLocalCoeff a q α β γ δ
  set ρ := heunLocalRadius a with hρdef
  have hρ : 0 < ρ := p1h_radius_pos ha
  have hρ1 : ρ ≤ 1 := min_le_left _ _
  have hρa : ρ ≤ ‖a‖ := min_le_right _ _
  have hapos : 0 < ‖a‖ := norm_pos_iff.2 ha
  set r := 2 / (t + ρ) with hr
  have htρ : 0 < t + ρ := by linarith
  have hr0 : 1 / ρ < r := by
    rw [hr, div_lt_div_iff₀ hρ htρ]; linarith
  have hrt : r * t < 1 := by
    rw [hr, div_mul_eq_mul_div, div_lt_one htρ]; linarith
  have hiρ : 1 ≤ 1 / ρ := by rw [le_div_iff₀ hρ]; linarith
  have hia : 1 / ‖a‖ ≤ 1 / ρ := one_div_le_one_div_of_le hρ hρa
  set δ' := (r - 1 / ρ) / 2 with hδ'
  have hδ0 : 0 < δ' := by rw [hδ']; linarith
  have hr1 : 1 / ‖a‖ + δ' ≤ r := by rw [hδ']; linarith
  have hD : 0 < 1 / ‖a‖ + δ' := by positivity
  set η := (r - 1) / (1 / ‖a‖ + δ') with hη
  have hη0 : 0 < η := div_pos (by linarith) hD
  have hr2 : 1 + η * (1 / ‖a‖ + δ') ≤ r := by
    rw [hη, div_mul_cancel₀ _ hD.ne']; linarith
  have e1 := (Metric.tendsto_nhds.1 (p1h_tendsto_A_add_B a q α β γ δ ha)) (η * δ' / 2)
    (by positivity)
  have e2 := (Metric.tendsto_nhds.1 (p1h_tendsto_B a α β γ ha)) (δ' / 2) (by positivity)
  set g : ℕ → ℝ := fun n => max (η * ‖c (n + 1)‖) ‖c (n + 1) - c n‖ * t ^ n with hg
  have hg0 : ∀ n, 0 ≤ g n := fun n =>
    mul_nonneg ((norm_nonneg _).trans (le_max_right _ _)) (pow_nonneg ht0 _)
  have hgs : Summable g := by
    refine summable_of_ratio_norm_eventually_le hrt ?_
    filter_upwards [e1, e2] with n h1 h2
    rw [dist_zero_right] at h1 h2
    rw [Real.norm_of_nonneg (hg0 _), Real.norm_of_nonneg (hg0 _), hg]
    simp only
    have hs := p1h_step (a := a) hη0 hδ0.le (p1h_coeff_add_two a q α β γ δ n) h1.le h2.le hr1 hr2
    rw [pow_succ]
    calc max (η * ‖c (n + 1 + 1)‖) ‖c (n + 1 + 1) - c (n + 1)‖ * (t ^ n * t)
        ≤ r * max (η * ‖c (n + 1)‖) ‖c (n + 1) - c n‖ * (t ^ n * t) := by
          gcongr
      _ = r * t * (max (η * ‖c (n + 1)‖) ‖c (n + 1) - c n‖ * t ^ n) := by ring
  have h1 : Summable (fun n => ‖c (n + 1)‖ * t ^ (n + 1)) := by
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
      (hgs.mul_left (t / η))
    have : η * ‖c (n + 1)‖ ≤ max (η * ‖c (n + 1)‖) ‖c (n + 1) - c n‖ := le_max_left _ _
    rw [hg]
    simp only
    rw [pow_succ]
    calc ‖c (n + 1)‖ * (t ^ n * t) = t / η * ((η * ‖c (n + 1)‖) * t ^ n) := by
          field_simp
      _ ≤ t / η * (max (η * ‖c (n + 1)‖) ‖c (n + 1) - c n‖ * t ^ n) := by gcongr
  exact (summable_nat_add_iff 1).1 h1


/-- The power series of `Hl` converges on the disk `|z| < min(1, |a|)`. -/
theorem p1h_hasFPowerSeriesOnBall {a q α β γ δ : ℂ} (ha : a ≠ 0) :
    HasFPowerSeriesOnBall (heunLocal a q α β γ δ) (ofScalars ℂ (heunLocalCoeff a q α β γ δ)) 0
      (ENNReal.ofReal (heunLocalRadius a)) := by
  set p := ofScalars ℂ (heunLocalCoeff a q α β γ δ)
  have hrad : ENNReal.ofReal (heunLocalRadius a) ≤ p.radius := by
    refine ENNReal.le_of_forall_nnreal_lt fun t ht => ?_
    refine p.le_radius_of_summable ?_
    have ht' : (t : ℝ) < heunLocalRadius a := by
      rwa [← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_lt_ofReal_iff (p1h_radius_pos ha)] at ht
    refine (p1h_summable_norm (q := q) (α := α) (β := β) (γ := γ) (δ := δ) ha t.2 ht').congr
      fun n => ?_
    simp [p]
  have hpos : 0 < ENNReal.ofReal (heunLocalRadius a) :=
    ENNReal.ofReal_pos.2 (p1h_radius_pos ha)
  have h := (p.hasFPowerSeriesOnBall (hpos.trans_le hrad)).mono hpos hrad
  have hsum : p.sum = heunLocal a q α β γ δ := by
    funext z
    simp [p, FormalMultilinearSeries.sum, heunLocal, mul_comm]
  rwa [hsum] at h

/-- Shift of a coefficient sequence (multiplication of the series by `z`). -/
def p1hSh (u : ℕ → ℂ) : ℕ → ℂ
  | 0 => 0
  | n + 1 => u n

lemma p1h_hasSum_sh {u : ℕ → ℂ} {S z : ℂ} (h : HasSum (fun n => u n * z ^ n) S) :
    HasSum (fun n => p1hSh u n * z ^ n) (z * S) :=
  HasSum.mul_pow_shift (c := p1hSh u) h rfl

/-- The coefficient of `zⁿ` in `z (𝒟 f - q f)` for `f = ∑ bₙ zⁿ` (with `ε = heunEps α β γ δ`). -/
def p1hE (a q α β γ δ : ℂ) (b : ℕ → ℂ) (n : ℕ) : ℂ :=
  p1hSh (p1hSh fun n => (n : ℂ) * (n - 1) * b n) n -
    (1 + a) * p1hSh (fun n => (n : ℂ) * (n - 1) * b n) n + a * ((n : ℂ) * (n - 1) * b n) +
    (γ + δ + heunEps α β γ δ) * p1hSh (p1hSh fun n => (n : ℂ) * b n) n -
    (γ * (1 + a) + δ * a + heunEps α β γ δ) * p1hSh (fun n => (n : ℂ) * b n) n +
    γ * a * ((n : ℂ) * b n) + α * β * p1hSh (p1hSh b) n - q * p1hSh b n

theorem p1hE_zero (a q α β γ δ : ℂ) (b : ℕ → ℂ) : p1hE a q α β γ δ b 0 = 0 := by
  simp [p1hE, p1hSh]

theorem p1hE_one (a q α β γ δ : ℂ) (b : ℕ → ℂ) :
    p1hE a q α β γ δ b 1 = a * γ * b 1 - q * b 0 := by
  simp only [p1hE, p1hSh]
  push_cast
  ring

theorem p1hE_add_two (a q α β γ δ : ℂ) (b : ℕ → ℂ) (k : ℕ) :
    p1hE a q α β γ δ b (k + 2) = heunRecR a γ (k + 1) * b (k + 2) -
      (heunRecQ a α β γ δ (k + 1) + q) * b (k + 1) + heunRecP α β (k + 1) * b k := by
  simp only [p1hE, p1hSh, heunRecR, heunRecQ, heunRecP, heunEps]
  push_cast
  ring

/-- For a power series `f = ∑ bₙ zⁿ`, the function `z (𝒟 f - q f)` has the power series with
coefficients `p1hE … b`. -/
theorem p1h_hasSum_heunOperator {a q α β γ δ : ℂ} {b : ℕ → ℂ} {f : ℂ → ℂ} {r : ENNReal}
    (h : HasFPowerSeriesOnBall f (ofScalars ℂ b) 0 r) {z : ℂ} (hz' : z ∈ Metric.eball 0 r) :
    HasSum (fun n => p1hE a q α β γ δ b n * z ^ n)
      (z * (heunOperator a α β γ δ (heunEps α β γ δ) f z - q * f z)) := by
  set ε := heunEps α β γ δ with hε
  have hF := h.hasSum_mul_pow hz'
  have hY := h.hasSum_z_mul_deriv hz'
  have hX : HasSum (fun n : ℕ => (n : ℂ) * (n - 1) * b n * z ^ n)
      (z ^ 2 * deriv (deriv f) z) := by
    have hs : HasSum (fun n : ℕ =>
        (n + 1 : ℂ) * ((n + 1 : ℂ) - 1) * b (n + 1) * z ^ n)
        (z * deriv (deriv f) z) := by
      convert h.deriv_ofScalars.hasSum_z_mul_deriv hz' using 1
      funext n
      ring
    have ht := HasSum.mul_pow_shift (c := fun n => (n : ℂ) * (n - 1) * b n)
      (by simpa only [Nat.cast_add, Nat.cast_one] using hs) (by simp)
    convert ht using 1
    ring
  have hX1 := p1h_hasSum_sh hX
  have hX2 := p1h_hasSum_sh hX1
  have hY1 := p1h_hasSum_sh hY
  have hY2 := p1h_hasSum_sh hY1
  have hF1 := p1h_hasSum_sh hF
  have hF2 := p1h_hasSum_sh hF1
  have hT := ((((((((hX2.sub (hX1.mul_left (1 + a))).add (hX.mul_left a)).add
    (hY2.mul_left (γ + δ + ε))).sub (hY1.mul_left (γ * (1 + a) + δ * a + ε))).add
    (hY.mul_left (γ * a))).add (hF2.mul_left (α * β))).sub (hF1.mul_left q)))
  convert hT using 1
  · funext n
    simp only [p1hE, ← hε]
    ring
  · rw [heunOperator]
    ring

/-- `z (𝒟 Hl - q Hl) = 0` on the disk of convergence. -/
lemma p1h_heunOperator_heunLocal {a q α β γ δ : ℂ} (ha : a ≠ 0) (hγ : ∀ n : ℕ, γ ≠ -(n : ℂ))
    {z : ℂ} (hz : ‖z‖ < heunLocalRadius a) :
    z * (heunOperator a α β γ δ (heunEps α β γ δ) (heunLocal a q α β γ δ) z -
      q * heunLocal a q α β γ δ z) = 0 := by
  set c := heunLocalCoeff a q α β γ δ with hc
  have h := p1h_hasFPowerSeriesOnBall (q := q) (α := α) (β := β) (δ := δ) (γ := γ) ha
  have hz' : z ∈ Metric.eball (0 : ℂ) (ENNReal.ofReal (heunLocalRadius a)) := by
    rw [Metric.eball_ofReal, mem_ball_zero_iff]; exact hz
  have hT := p1h_hasSum_heunOperator (a := a) (q := q) (α := α) (β := β) (γ := γ) (δ := δ) h hz'
  have hcoef : ∀ n, p1hE a q α β γ δ c n = 0 := by
    intro n
    have hγ0 : γ ≠ 0 := by simpa using hγ 0
    rcases n with _ | _ | k
    · exact p1hE_zero _ _ _ _ _ _ _
    · rw [p1hE_one, hc, heunLocalCoeff, heunLocalCoeff]
      field_simp
      ring
    · have hR : heunRecR a γ (k + 1) ≠ 0 := by
        unfold heunRecR
        refine mul_ne_zero (mul_ne_zero ha (by norm_cast)) fun h0 => hγ (k + 1) ?_
        push_cast at h0 ⊢; linear_combination h0
      rw [p1hE_add_two, hc, heunLocalCoeff, mul_div_cancel₀ _ hR]
      ring
  refine hT.unique ?_
  convert (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℂ)) 0) using 1
  funext n
  rw [hcoef n, zero_mul]

/-- DLMF 31.3.1: for `a ≠ 0` and `γ ∉ {0, -1, -2, …}` the Maclaurin series `∑ c_j z^j`
converges to `Hl(a, q; α, β, γ, δ; z)` for `|z| < min(1, |a|)` (the radius given by the nearest
singularity; the ratio `c_{j+1}/c_j` tends to `1` or `1/a`). -/
@[dlmf 31.3.E1]
theorem hasSum_heunLocal (ha : a ≠ 0) (hγ : ∀ n : ℕ, γ ≠ -(n : ℂ)) {z : ℂ}
    (hz : ‖z‖ < heunLocalRadius a) :
    HasSum (fun j => heunLocalCoeff a q α β γ δ j * z ^ j) (heunLocal a q α β γ δ z) :=
  (p1h_hasFPowerSeriesOnBall ha).hasSum_mul_pow (by rwa [Metric.eball_ofReal, mem_ball_zero_iff])

/-- DLMF §31.3(i): `Hl` is analytic in the disk `|z| < min(1, |a|)` and solves Heun's equation
(with `ε = α + β + 1 - γ - δ`) there, away from the regular singular point `z = 0`. -/
@[dlmf 31.3.i, dlmf 31.3.E1]
theorem heunLocal_isHeunSolOn (ha : a ≠ 0) (hγ : ∀ n : ℕ, γ ≠ -(n : ℂ)) :
    AnalyticOnNhd ℂ (heunLocal a q α β γ δ) (Metric.ball 0 (heunLocalRadius a)) ∧
    IsHeunSolOn a q α β γ δ (heunEps α β γ δ) (heunLocal a q α β γ δ)
      (Metric.ball 0 (heunLocalRadius a) \ {0}) := by
  have h := p1h_hasFPowerSeriesOnBall (q := q) (α := α) (β := β) (γ := γ) (δ := δ) ha
  have hA : AnalyticOnNhd ℂ (heunLocal a q α β γ δ) (Metric.ball 0 (heunLocalRadius a)) :=
    fun z hz => h.analyticAt_of_mem (by rwa [Metric.eball_ofReal])
  refine ⟨hA, ?_⟩
  have hs : ∀ z ∈ Metric.ball 0 (heunLocalRadius a) \ {0}, z ≠ 0 ∧ z ≠ 1 ∧ z ≠ a := by
    rintro z ⟨hz, hz0⟩
    rw [mem_ball_zero_iff] at hz
    refine ⟨hz0, fun h1 => ?_, fun h1 => ?_⟩
    · subst h1; simp only [norm_one] at hz
      exact absurd (hz.trans_le (min_le_left _ _)) (lt_irrefl _)
    · subst h1; exact absurd (hz.trans_le (min_le_right _ _)) (lt_irrefl _)
  rw [isHeunSolOn_iff_heunOperator hs]
  rintro z ⟨hz, hz0⟩
  have hzA := hA z hz
  refine ⟨hzA.differentiableAt, hzA.deriv.differentiableAt, ?_⟩
  rw [mem_ball_zero_iff] at hz
  have := p1h_heunOperator_heunLocal (q := q) (α := α) (β := β) (δ := δ) ha hγ hz
  rcases mul_eq_zero.1 this with h0 | h0
  · exact absurd h0 hz0
  · exact sub_eq_zero.1 h0

/-! ### Transformations used for the local solutions -/

/-- Restriction of a solution to a subset. -/
lemma p1h_isLinearODE2On_mono {p r w : ℂ → ℂ} {s t : Set ℂ} (h : IsLinearODE2On p r w t)
    (hst : s ⊆ t) : IsLinearODE2On p r w s :=
  ⟨fun z hz => h.1 z (hst hz), fun z hz => h.2 z (hst hz)⟩

/-- Heun's equation is symmetric in `α` and `β`. -/
lemma p1h_isHeunSolOn_swap {w : ℂ → ℂ} {s : Set ℂ} (h : IsHeunSolOn a q α β γ δ ε w s) :
    IsHeunSolOn a q β α γ δ ε w s := by
  have : heunCoeffR a q β α = heunCoeffR a q α β := by
    funext z; unfold heunCoeffR; ring
  unfold IsHeunSolOn at *
  rwa [this]

/-- The homography `z ↦ 1 - z` (§31.2(v)): a solution of Heun's equation with parameters
`(1 - a, αβ - q; α, β, δ, γ; ε)` composed with `1 - z` solves the original equation. -/
lemma p1h_isHeunSolOn_one_sub {U V : Set ℂ} (hU : IsOpen U)
    (hUs : ∀ z ∈ U, z ≠ 0 ∧ z ≠ 1 ∧ z ≠ a ∧ 1 - z ∈ V) {w : ℂ → ℂ}
    (hw : IsHeunSolOn (1 - a) (α * β - q) α β δ γ ε w V) :
    IsHeunSolOn a q α β γ δ ε (fun z => w (1 - z)) U := by
  refine p1h_isLinearODE2On_comp (φ₁ := fun _ => -1) (φ₂ := fun _ => 0) hU
    (fun z _ => by simpa using (hasDerivAt_id' z).const_sub (1 : ℂ))
    (fun z _ => hasDerivAt_const _ _) (fun z hz => (hUs z hz).2.2.2) (fun z hz => ?_)
    (fun z hz => ?_) hw
  · obtain ⟨h0, h1, ha, -⟩ := hUs z hz
    have h1' : z - 1 ≠ 0 := sub_ne_zero.2 h1
    have ha' : z - a ≠ 0 := sub_ne_zero.2 ha
    have e1 : 1 - z - 1 = -z := by ring
    have e2 : 1 - z - (1 - a) = -(z - a) := by ring
    have e3 : 1 - z = -(z - 1) := by ring
    simp only [heunCoeffP, e1, e2]
    rw [e3]
    field_simp
    ring
  · obtain ⟨h0, h1, ha, -⟩ := hUs z hz
    have h1' : z - 1 ≠ 0 := sub_ne_zero.2 h1
    have ha' : z - a ≠ 0 := sub_ne_zero.2 ha
    have e1 : 1 - z - 1 = -z := by ring
    have e2 : 1 - z - (1 - a) = -(z - a) := by ring
    have e3 : 1 - z = -(z - 1) := by ring
    simp only [heunCoeffR, e1, e2]
    rw [e3]
    field_simp
    ring

/-- The homography `z ↦ (a - z)/(a - 1)` (§31.2(v)). -/
lemma p1h_isHeunSolOn_comp_a (ha1 : a ≠ 1) {U V : Set ℂ} (hU : IsOpen U)
    (hUs : ∀ z ∈ U, z ≠ 0 ∧ z ≠ 1 ∧ z ≠ a ∧ (a - z) / (a - 1) ∈ V) {w : ℂ → ℂ}
    (hw : IsHeunSolOn (a / (a - 1)) ((α * β * a - q) / (a - 1)) α β ε δ γ w V) :
    IsHeunSolOn a q α β γ δ ε (fun z => w ((a - z) / (a - 1))) U := by
  have ha1' : a - 1 ≠ 0 := sub_ne_zero.2 ha1
  refine p1h_isLinearODE2On_comp (φ₁ := fun _ => -1 / (a - 1)) (φ₂ := fun _ => 0) hU
    (fun z _ => ?_) (fun z _ => hasDerivAt_const _ _) (fun z hz => (hUs z hz).2.2.2)
    (fun z hz => ?_) (fun z hz => ?_) hw
  · convert ((hasDerivAt_id' z).const_sub a).div_const (a - 1) using 1
  · obtain ⟨h0, h1, ha, -⟩ := hUs z hz
    have h1' : z - 1 ≠ 0 := sub_ne_zero.2 h1
    have ha' : z - a ≠ 0 := sub_ne_zero.2 ha
    have e1 : (a - z) / (a - 1) - 1 = -(z - 1) / (a - 1) := by field_simp; ring
    have e2 : (a - z) / (a - 1) - a / (a - 1) = -z / (a - 1) := by field_simp; ring
    have e3 : (a - z) / (a - 1) = -(z - a) / (a - 1) := by ring
    simp only [heunCoeffP, e1, e2]
    rw [e3]
    field_simp
    ring
  · obtain ⟨h0, h1, ha, -⟩ := hUs z hz
    have h1' : z - 1 ≠ 0 := sub_ne_zero.2 h1
    have ha' : z - a ≠ 0 := sub_ne_zero.2 ha
    have e1 : (a - z) / (a - 1) - 1 = -(z - 1) / (a - 1) := by field_simp; ring
    have e2 : (a - z) / (a - 1) - a / (a - 1) = -z / (a - 1) := by field_simp; ring
    have e3 : (a - z) / (a - 1) = -(z - a) / (a - 1) := by ring
    simp only [heunCoeffR, e1, e2]
    rw [e3]
    field_simp
    ring

/-- The map `w ↦ z^{-α} w(1/z)` (§31.2(v), §31.3(ii)): a solution of Heun's equation with
parameters `(1/a, q/a - α(β - ε) - (α/a)(β - δ); α, α - γ + 1, α - β + 1, δ; ε)` gives a
solution of the original equation. -/
lemma p1h_isHeunSolOn_infinity (ha0 : a ≠ 0) (hε : ε = heunEps α β γ δ) {U V : Set ℂ}
    (hU : IsOpen U) (hUs : ∀ z ∈ U, z ∈ slitPlane ∧ z ≠ 1 ∧ z ≠ a ∧ 1 / z ∈ V) {w : ℂ → ℂ}
    (hw : IsHeunSolOn (1 / a) (q / a - α * (β - ε) - α / a * (β - δ)) α (α - γ + 1)
      (α - β + 1) δ ε w V) :
    IsHeunSolOn a q α β γ δ ε (fun z => z ^ (-α) * w (1 / z)) U := by
  subst hε
  unfold heunEps at *
  set L : ℂ → ℂ := fun z => -α / z
  set L' : ℂ → ℂ := fun z => α / z ^ 2
  have hne : ∀ z ∈ U, z ≠ 0 ∧ z - 1 ≠ 0 ∧ z - a ≠ 0 := fun z hz =>
    ⟨slitPlane_ne_zero (hUs z hz).1, sub_ne_zero.2 (hUs z hz).2.1, sub_ne_zero.2 (hUs z hz).2.2.1⟩
  refine p1h_isLinearODE2On_mul (L := L) (L' := L')
    (p₁ := fun z => heunCoeffP a γ δ (α + β + 1 - γ - δ) z + 2 * L z)
    (r₁ := fun z => heunCoeffR a q α β z + heunCoeffP a γ δ (α + β + 1 - γ - δ) z * L z +
      L z ^ 2 + L' z)
    hU (fun z hz => ?_) (fun z hz => ?_) (fun z hz => rfl) (fun z hz => rfl) ?_
  · have h := p1h_hasDerivAt_cpow (s := -α) (hasDerivAt_id' z) (hUs z hz).1
    convert h using 1
    simp only [L]
    ring
  · have h0 := (hne z hz).1
    convert ((hasDerivAt_id' z).inv h0).const_mul (-α) using 1
    · ext y; simp [L, div_eq_mul_inv]
    · simp [L']; field_simp
  refine p1h_isLinearODE2On_comp (φ₁ := fun z => -1 / z ^ 2)
    (φ₂ := fun z => 2 / z ^ 3) hU (fun z hz => ?_) (fun z hz => ?_)
    (fun z hz => (hUs z hz).2.2.2) (fun z hz => ?_) (fun z hz => ?_) hw
  · have h0 := (hne z hz).1
    convert ((hasDerivAt_id' z).inv h0) using 1
    · ext y; simp
  · have h0 := (hne z hz).1
    have := (((hasDerivAt_id' z).pow 2).inv (pow_ne_zero 2 h0)).const_mul (-1 : ℂ)
    convert this using 1
    · ext y; simp [div_eq_mul_inv]
    · simp; field_simp
  · obtain ⟨h0, h1, ha⟩ := hne z hz
    have e1 : 1 / z - 1 = -(z - 1) / z := by field_simp; ring
    have e2 : 1 / z - 1 / a = -(z - a) / (z * a) := by field_simp; ring
    simp only [heunCoeffP, L, e1, e2]
    field_simp
    ring
  · obtain ⟨h0, h1, ha⟩ := hne z hz
    have e1 : 1 / z - 1 = -(z - 1) / z := by field_simp; ring
    have e2 : 1 / z - 1 / a = -(z - a) / (z * a) := by field_simp; ring
    simp only [heunCoeffP, heunCoeffR, L, L', e1, e2]
    field_simp
    ring

/-- The domain `{|z| < min(1, |a|)} ∩ slitPlane` is open. -/
lemma p1h_isOpen_ball_slit (a : ℂ) :
    IsOpen {z : ℂ | ‖z‖ < heunLocalRadius a ∧ z ∈ slitPlane} :=
  (isOpen_lt continuous_norm continuous_const).inter isOpen_slitPlane

/-- A point of the disk of convergence of `Hl(a, ⋯)` is neither `1` nor `a`. -/
lemma p1h_ne_of_radius {a z : ℂ} (hz : ‖z‖ < heunLocalRadius a) : z ≠ 1 ∧ z ≠ a := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · subst h; simp only [norm_one] at hz; exact absurd (hz.trans_le (min_le_left _ _)) (lt_irrefl _)
  · subst h; exact absurd (hz.trans_le (min_le_right _ _)) (lt_irrefl _)

/-- The domain `{|1/z| < min(1, |1/a|)} ∩ slitPlane` is open. -/
lemma p1h_isOpen_inv_slit (a : ℂ) :
    IsOpen {z : ℂ | ‖1 / z‖ < heunLocalRadius (1 / a) ∧ z ∈ slitPlane} := by
  have hc : ContinuousOn (fun z : ℂ => ‖1 / z‖) slitPlane := by
    refine ContinuousOn.norm (continuousOn_const.div continuousOn_id fun z hz => ?_)
    exact slitPlane_ne_zero hz
  have := hc.isOpen_inter_preimage isOpen_slitPlane (isOpen_Iio (a := heunLocalRadius (1 / a)))
  convert this using 1
  ext z
  simp [and_comm]

/-- A one-variable power series is `ofScalars` of its coefficients. -/
lemma p1h_eq_ofScalars_coeff (p : FormalMultilinearSeries ℂ ℂ ℂ) :
    p = ofScalars ℂ (fun n => p.coeff n) := by
  ext n
  rw [apply_eq_prod_smul_coeff]
  simp [ofScalars, mul_comm]

/-- Coefficients of a power series vanishing on a ball vanish. -/
lemma p1h_coeff_eq_zero_of_hasSum {e : ℕ → ℂ} {r : ℝ} (hr : 0 < r)
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
  have := hp.hasFPowerSeriesAt.eq_zero
  exact (ofScalars_series_eq_zero ℂ).1 this

/-- DLMF §31.3(i), characterization of `Hl`: for `γ ∉ {0, -1, -2, …}`, every solution of Heun's
equation near `0` (punctured) that is analytic at `0` is `w(0) · Hl(z)` near `0`. -/
@[dlmf 31.3.i]
theorem eventuallyEq_heunLocal_of_analyticAt (ha : a ≠ 0) (hγ : ∀ n : ℕ, γ ≠ -(n : ℂ))
    {w : ℂ → ℂ} {U : Set ℂ} (hU : U ∈ 𝓝 (0 : ℂ)) (hw : AnalyticAt ℂ w 0)
    (hsol : IsHeunSolOn a q α β γ δ (heunEps α β γ δ) w (U \ {0})) :
    w =ᶠ[𝓝 0] fun z => w 0 * heunLocal a q α β γ δ z := by
  obtain ⟨p, r, hp⟩ := hw
  set b : ℕ → ℂ := fun n => p.coeff n with hb
  have hp' : HasFPowerSeriesOnBall w (ofScalars ℂ b) 0 r := by
    rw [hb, ← p1h_eq_ofScalars_coeff]; exact hp
  obtain ⟨ρ, hρ, hρU⟩ := Metric.mem_nhds_iff.1 hU
  obtain ⟨t, ht0, ht, htr⟩ := ENNReal.lt_iff_exists_real_btwn.1 hp.r_pos
  have ht0' : 0 < t := ENNReal.ofReal_pos.1 ht
  set r' := min t (min ρ (heunLocalRadius a)) with hr'
  have hr'0 : 0 < r' := lt_min ht0' (lt_min hρ (p1h_radius_pos ha))
  have hr'r : ENNReal.ofReal r' ≤ r :=
    (ENNReal.ofReal_le_ofReal (min_le_left _ _)).trans htr.le
  have hr'ρ : r' ≤ ρ := (min_le_right _ _).trans (min_le_left _ _)
  have hr'a : r' ≤ heunLocalRadius a := (min_le_right _ _).trans (min_le_right _ _)
  have hsub : Metric.ball (0 : ℂ) r' \ {0} ⊆ U \ {0} := fun z hz =>
    ⟨hρU (Metric.ball_subset_ball hr'ρ hz.1), hz.2⟩
  have hs : ∀ z ∈ Metric.ball (0 : ℂ) r' \ {0}, z ≠ 0 ∧ z ≠ 1 ∧ z ≠ a := fun z hz =>
    ⟨hz.2, p1h_ne_of_radius ((mem_ball_zero_iff.1 hz.1).trans_le hr'a)⟩
  have hsol' := (isHeunSolOn_iff_heunOperator hs).1 (p1h_isLinearODE2On_mono hsol hsub)
  have hzr : ∀ z : ℂ, ‖z‖ < r' → z ∈ Metric.eball (0 : ℂ) r := fun z hz => by
    refine Metric.eball_subset_eball hr'r ?_
    rw [Metric.eball_ofReal, mem_ball_zero_iff]; exact hz
  have hE : p1hE a q α β γ δ b = 0 := by
    refine p1h_coeff_eq_zero_of_hasSum hr'0 fun z hz => ?_
    convert p1h_hasSum_heunOperator (a := a) (q := q) (α := α) (β := β) (γ := γ) (δ := δ) hp'
      (hzr z hz) using 1
    rcases eq_or_ne z 0 with rfl | hz0
    · simp
    · rw [(hsol' z ⟨mem_ball_zero_iff.2 hz, hz0⟩).2.2, sub_self, mul_zero]
  have hbc : ∀ n, b n = b 0 * heunLocalCoeff a q α β γ δ n := by
    have hγ0 : γ ≠ 0 := by simpa using hγ 0
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      match n, ih with
      | 0, _ => simp
      | 1, _ =>
        have h1 := congrFun hE 1
        rw [p1hE_one] at h1
        rw [heunLocalCoeff]
        simp only [Pi.zero_apply] at h1
        field_simp
        linear_combination h1
      | k + 2, ih =>
        have hR : heunRecR a γ (k + 1) ≠ 0 := by
          unfold heunRecR
          refine mul_ne_zero (mul_ne_zero ha (by norm_cast)) fun h0 => hγ (k + 1) ?_
          push_cast at h0 ⊢; linear_combination h0
        have h2 := congrFun hE (k + 2)
        rw [p1hE_add_two, ih (k + 1) (by omega), ih k (by omega)] at h2
        simp only [Pi.zero_apply] at h2
        rw [heunLocalCoeff]
        field_simp
        linear_combination h2
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hr'0] with z hz
  rw [mem_ball_zero_iff] at hz
  have h1 := hp'.hasSum_mul_pow (hzr z hz)
  have h2 := (hasSum_heunLocal (q := q) (α := α) (β := β) (δ := δ) ha hγ
    (hz.trans_le hr'a)).mul_left (b 0)
  have hb0 : b 0 = w 0 := by
    simp only [hb]
    simpa using hp.coeff_zero
  rw [← hb0]
  refine h1.unique ?_
  convert h2 using 1
  funext n
  rw [hbc n]; ring

/-! ### The other local solutions (31.3.5–31.3.11) -/

/-- DLMF 31.3.5: for `γ ∉ {1, 2, 3, …}` the solution with exponent `1 - γ` at `z = 0` is
`z^{1-γ} Hl(a, (aδ + ε)(1 - γ) + q; α + 1 - γ, β + 1 - γ, 2 - γ, δ; z)`. -/
@[dlmf 31.3.E5]
theorem heunLocal_second_isHeunSolOn (ha : a ≠ 0) (hγ : ∀ n : ℕ, γ ≠ (n : ℂ) + 1)
    (hε : ε = heunEps α β γ δ) :
    IsHeunSolOn a q α β γ δ ε
      (fun z => z ^ (1 - γ) * heunLocal a ((a * δ + ε) * (1 - γ) + q) (α + 1 - γ) (β + 1 - γ)
        (2 - γ) δ z)
      {z | ‖z‖ < heunLocalRadius a ∧ z ∈ slitPlane} := by
  have hF : α + β + 1 = γ + δ + ε := by rw [hε]; unfold heunEps; ring
  have hγ' : ∀ n : ℕ, 2 - γ ≠ -(n : ℂ) := fun n h =>
    hγ (n + 1) (by push_cast; linear_combination -h)
  have h := (heunLocal_isHeunSolOn (q := (a * δ + ε) * (1 - γ) + q) (α := α + 1 - γ)
    (β := β + 1 - γ) (δ := δ) ha hγ').2
  have hε' : heunEps (α + 1 - γ) (β + 1 - γ) (2 - γ) δ = ε := by rw [hε]; unfold heunEps; ring
  rw [hε'] at h
  refine heun_fHomotopic_zero hF (p1h_isOpen_ball_slit a) (fun z hz => ?_) ?_
  · exact ⟨hz.2, p1h_ne_of_radius hz.1⟩
  · rw [show q + (a * δ + ε) * (1 - γ) = (a * δ + ε) * (1 - γ) + q from add_comm _ _]
    refine p1h_isLinearODE2On_mono h fun z hz => ⟨mem_ball_zero_iff.2 hz.1, ?_⟩
    exact slitPlane_ne_zero hz.2

/-- DLMF 31.3.6: for `δ ∉ {0, -1, -2, …}` the solution with exponent `0` at `z = 1` is
`Hl(1 - a, αβ - q; α, β, δ, γ; 1 - z)`. -/
@[dlmf 31.3.E6]
theorem heunLocal_at_one_isHeunSolOn (ha : a ≠ 1) (hδ : ∀ n : ℕ, δ ≠ -(n : ℂ))
    (hε : ε = heunEps α β γ δ) :
    IsHeunSolOn a q α β γ δ ε (fun z => heunLocal (1 - a) (α * β - q) α β δ γ (1 - z))
      ({z | ‖1 - z‖ < heunLocalRadius (1 - a)} \ {1}) := by
  have ha' : 1 - a ≠ 0 := sub_ne_zero.2 (Ne.symm ha)
  have h := (heunLocal_isHeunSolOn (a := 1 - a) (q := α * β - q) (α := α) (β := β) (γ := δ)
    (δ := γ) ha' hδ).2
  have hε' : heunEps α β δ γ = ε := by rw [hε]; unfold heunEps; ring
  rw [hε'] at h
  refine p1h_isHeunSolOn_one_sub (V := Metric.ball 0 (heunLocalRadius (1 - a)) \ {0})
    ((isOpen_lt (by fun_prop) continuous_const).sdiff isClosed_singleton) (fun z hz => ?_) h
  obtain ⟨hz, hz1⟩ := hz
  have hz1' : z ≠ 1 := hz1
  obtain ⟨h1, h2⟩ := p1h_ne_of_radius hz
  refine ⟨fun h0 => h1 (by rw [h0, sub_zero]), hz1', fun h0 => h2 (by rw [h0]), ?_, ?_⟩
  · exact mem_ball_zero_iff.2 hz
  · exact sub_ne_zero.2 (Ne.symm hz1')

/-- DLMF 31.3.7: for `δ ∉ {1, 2, 3, …}` the solution with exponent `1 - δ` at `z = 1` is
`(1-z)^{1-δ} Hl(1 - a, ((1-a)γ + ε)(1 - δ) + αβ - q; α + 1 - δ, β + 1 - δ, 2 - δ, γ; 1 - z)`. -/
@[dlmf 31.3.E7]
theorem heunLocal_second_at_one_isHeunSolOn (ha : a ≠ 1) (hδ : ∀ n : ℕ, δ ≠ (n : ℂ) + 1)
    (hε : ε = heunEps α β γ δ) :
    IsHeunSolOn a q α β γ δ ε
      (fun z => (1 - z) ^ (1 - δ) * heunLocal (1 - a) (((1 - a) * γ + ε) * (1 - δ) + α * β - q)
        (α + 1 - δ) (β + 1 - δ) (2 - δ) γ (1 - z))
      {z | ‖1 - z‖ < heunLocalRadius (1 - a) ∧ 1 - z ∈ slitPlane} := by
  have ha' : 1 - a ≠ 0 := sub_ne_zero.2 (Ne.symm ha)
  have hε' : ε = heunEps α β δ γ := by rw [hε]; unfold heunEps; ring
  have h := heunLocal_second_isHeunSolOn (a := 1 - a) (q := α * β - q) (α := α) (β := β)
    (γ := δ) (δ := γ) ha' hδ hε'
  rw [show ((1 - a) * γ + ε) * (1 - δ) + α * β - q = ((1 - a) * γ + ε) * (1 - δ) + (α * β - q)
    by ring]
  refine p1h_isHeunSolOn_one_sub (V := {u | ‖u‖ < heunLocalRadius (1 - a) ∧ u ∈ slitPlane})
    ((isOpen_lt (by fun_prop : Continuous fun z : ℂ => ‖1 - z‖) continuous_const).inter
      (isOpen_slitPlane.preimage (by fun_prop : Continuous fun z : ℂ => 1 - z)))
    (fun z hz => ?_) h
  obtain ⟨hz, hzs⟩ := hz
  obtain ⟨h1, h2⟩ := p1h_ne_of_radius hz
  refine ⟨fun h0 => h1 (by rw [h0, sub_zero]), fun h0 => slitPlane_ne_zero hzs
    (show 1 - z = 0 by rw [h0, sub_self]),
    fun h0 => h2 (by rw [h0]), hz, hzs⟩

/-- DLMF 31.3.8: for `ε ∉ {0, -1, -2, …}` the solution with exponent `0` at `z = a` is
`Hl(a/(a-1), (αβa - q)/(a-1); α, β, ε, δ; (a-z)/(a-1))`. -/
@[dlmf 31.3.E8]
theorem heunLocal_at_a_isHeunSolOn (ha0 : a ≠ 0) (ha1 : a ≠ 1) (hε' : ∀ n : ℕ, ε ≠ -(n : ℂ))
    (hε : ε = heunEps α β γ δ) :
    IsHeunSolOn a q α β γ δ ε
      (fun z => heunLocal (a / (a - 1)) ((α * β * a - q) / (a - 1)) α β ε δ ((a - z) / (a - 1)))
      ({z | ‖(a - z) / (a - 1)‖ < heunLocalRadius (a / (a - 1))} \ {a}) := by
  have ha1' : a - 1 ≠ 0 := sub_ne_zero.2 ha1
  have ha' : a / (a - 1) ≠ 0 := div_ne_zero ha0 ha1'
  have h := (heunLocal_isHeunSolOn (a := a / (a - 1)) (q := (α * β * a - q) / (a - 1)) (α := α)
    (β := β) (γ := ε) (δ := δ) ha' hε').2
  have hγ : heunEps α β ε δ = γ := by rw [hε]; unfold heunEps; ring
  rw [hγ] at h
  refine p1h_isHeunSolOn_comp_a ha1 (V := Metric.ball 0 (heunLocalRadius (a / (a - 1))) \ {0})
    ((isOpen_lt (by fun_prop) continuous_const).sdiff isClosed_singleton) (fun z hz => ?_) h
  obtain ⟨hz, hza⟩ := hz
  have hza' : z ≠ a := hza
  obtain ⟨h1, h2⟩ := p1h_ne_of_radius hz
  refine ⟨fun h0 => h2 (by rw [h0, sub_zero]), fun h0 => h1 (by rw [h0]; exact div_self ha1'),
    hza', mem_ball_zero_iff.2 hz, ?_⟩
  exact div_ne_zero (sub_ne_zero.2 (Ne.symm hza')) ha1'

/-- DLMF 31.3.9: for `ε ∉ {1, 2, 3, …}` the solution with exponent `1 - ε` at `z = a` is
`((a-z)/(a-1))^{1-ε} Hl(a/(a-1), (a(δ+γ) - γ)(1-ε)/(a-1) + (αβa - q)/(a-1);
α + 1 - ε, β + 1 - ε, 2 - ε, δ; (a-z)/(a-1))`. -/
@[dlmf 31.3.E9]
theorem heunLocal_second_at_a_isHeunSolOn (ha0 : a ≠ 0) (ha1 : a ≠ 1)
    (hε' : ∀ n : ℕ, ε ≠ (n : ℂ) + 1) (hε : ε = heunEps α β γ δ) :
    IsHeunSolOn a q α β γ δ ε
      (fun z => ((a - z) / (a - 1)) ^ (1 - ε) *
        heunLocal (a / (a - 1)) ((a * (δ + γ) - γ) * (1 - ε) / (a - 1) + (α * β * a - q) / (a - 1))
          (α + 1 - ε) (β + 1 - ε) (2 - ε) δ ((a - z) / (a - 1)))
      {z | ‖(a - z) / (a - 1)‖ < heunLocalRadius (a / (a - 1)) ∧
        (a - z) / (a - 1) ∈ slitPlane} := by
  have ha1' : a - 1 ≠ 0 := sub_ne_zero.2 ha1
  have ha' : a / (a - 1) ≠ 0 := div_ne_zero ha0 ha1'
  have hγ : γ = heunEps α β ε δ := by rw [hε]; unfold heunEps; ring
  have h := heunLocal_second_isHeunSolOn (a := a / (a - 1)) (q := (α * β * a - q) / (a - 1))
    (α := α) (β := β) (γ := ε) (δ := δ) (ε := γ) ha' hε' hγ
  rw [show (a * (δ + γ) - γ) * (1 - ε) / (a - 1) + (α * β * a - q) / (a - 1) =
    (a / (a - 1) * δ + γ) * (1 - ε) + (α * β * a - q) / (a - 1) by field_simp; ring]
  refine p1h_isHeunSolOn_comp_a ha1
    (V := {u | ‖u‖ < heunLocalRadius (a / (a - 1)) ∧ u ∈ slitPlane})
    ((isOpen_lt (by fun_prop : Continuous fun z : ℂ => ‖(a - z) / (a - 1)‖)
      continuous_const).inter
      (isOpen_slitPlane.preimage (by fun_prop : Continuous fun z : ℂ => (a - z) / (a - 1))))
    (fun z hz => ?_) h
  obtain ⟨hz, hzs⟩ := hz
  obtain ⟨h1, h2⟩ := p1h_ne_of_radius hz
  refine ⟨fun h0 => h2 (by rw [h0, sub_zero]), fun h0 => h1 (by rw [h0]; exact div_self ha1'),
    fun h0 => slitPlane_ne_zero hzs (show (a - z) / (a - 1) = 0 by rw [h0, sub_self, zero_div]),
    hz, hzs⟩

/-- DLMF 31.3.10 (as corrected in DLMF 1.1.7): for `α - β ∉ {-1, -2, …}` the solution with
exponent `α` at `∞` is
`z^{-α} Hl(1/a, q/a - α(β - ε) - (α/a)(β - δ); α, α - γ + 1, α - β + 1, δ; 1/z)`,
valid for `|z| > max(1, |a|)` off the branch cut of `z^{-α}`. -/
@[dlmf 31.3.E10]
theorem heunLocal_at_infinity_isHeunSolOn (ha0 : a ≠ 0)
    (hαβ : ∀ n : ℕ, α - β + 1 ≠ -(n : ℂ)) (hε : ε = heunEps α β γ δ) :
    IsHeunSolOn a q α β γ δ ε
      (fun z => z ^ (-α) * heunLocal (1 / a) (q / a - α * (β - ε) - α / a * (β - δ)) α
        (α - γ + 1) (α - β + 1) δ (1 / z))
      {z | ‖1 / z‖ < heunLocalRadius (1 / a) ∧ z ∈ slitPlane} := by
  have ha' : 1 / a ≠ 0 := one_div_ne_zero ha0
  have h := (heunLocal_isHeunSolOn (a := 1 / a) (q := q / a - α * (β - ε) - α / a * (β - δ))
    (α := α) (β := α - γ + 1) (γ := α - β + 1) (δ := δ) ha' hαβ).2
  have hε' : heunEps α (α - γ + 1) (α - β + 1) δ = ε := by rw [hε]; unfold heunEps; ring
  rw [hε'] at h
  refine p1h_isHeunSolOn_infinity ha0 hε (V := Metric.ball 0 (heunLocalRadius (1 / a)) \ {0})
    (p1h_isOpen_inv_slit a) (fun z hz => ?_) h
  obtain ⟨hz, hzs⟩ := hz
  obtain ⟨h1, h2⟩ := p1h_ne_of_radius hz
  refine ⟨hzs, fun h0 => h1 (by rw [h0, div_one]), fun h0 => h2 (by rw [h0]),
    mem_ball_zero_iff.2 hz, one_div_ne_zero (slitPlane_ne_zero hzs)⟩

/-- DLMF 31.3.11 (as corrected in DLMF 1.1.7): for `β - α ∉ {-1, -2, …}` the solution with
exponent `β` at `∞` is
`z^{-β} Hl(1/a, q/a - β(α - ε) - (β/a)(α - δ); β, β - γ + 1, β - α + 1, δ; 1/z)`. -/
@[dlmf 31.3.E11]
theorem heunLocal_second_at_infinity_isHeunSolOn (ha0 : a ≠ 0)
    (hαβ : ∀ n : ℕ, β - α + 1 ≠ -(n : ℂ)) (hε : ε = heunEps α β γ δ) :
    IsHeunSolOn a q α β γ δ ε
      (fun z => z ^ (-β) * heunLocal (1 / a) (q / a - β * (α - ε) - β / a * (α - δ)) β
        (β - γ + 1) (β - α + 1) δ (1 / z))
      {z | ‖1 / z‖ < heunLocalRadius (1 / a) ∧ z ∈ slitPlane} := by
  have ha' : 1 / a ≠ 0 := one_div_ne_zero ha0
  have h := (heunLocal_isHeunSolOn (a := 1 / a) (q := q / a - β * (α - ε) - β / a * (α - δ))
    (α := β) (β := β - γ + 1) (γ := β - α + 1) (δ := δ) ha' hαβ).2
  have hε' : heunEps β (β - γ + 1) (β - α + 1) δ = ε := by rw [hε]; unfold heunEps; ring
  rw [hε'] at h
  have hεs : ε = heunEps β α γ δ := by rw [hε]; unfold heunEps; ring
  refine p1h_isHeunSolOn_swap (p1h_isHeunSolOn_infinity ha0 hεs
    (V := Metric.ball 0 (heunLocalRadius (1 / a)) \ {0}) (p1h_isOpen_inv_slit a)
    (fun z hz => ?_) h)
  obtain ⟨hz, hzs⟩ := hz
  obtain ⟨h1, h2⟩ := p1h_ne_of_radius hz
  refine ⟨hzs, fun h0 => h1 (by rw [h0, div_one]), fun h0 => h2 (by rw [h0]),
    mem_ball_zero_iff.2 hz, one_div_ne_zero (slitPlane_ne_zero hzs)⟩

/-! ### Equivalent expressions (§31.3(iii)) -/

/-- The coefficients of `Hl(1/a, q/a; α, β, γ, ε; ·)` are `a^j` times those of
`Hl(a, q; α, β, γ, δ; ·)`, where `ε = α + β + 1 - γ - δ`. -/
lemma h31_heunLocalCoeff_inv (ha : a ≠ 0) (j : ℕ) :
    heunLocalCoeff (1 / a) (q / a) α β γ (heunEps α β γ δ) j =
      a ^ j * heunLocalCoeff a q α β γ δ j := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    match j, ih with
    | 0, _ => simp
    | 1, _ =>
      simp only [heunLocalCoeff_one, pow_one]
      rcases eq_or_ne γ 0 with rfl | hγ
      · simp
      · field_simp
    | k + 2, ih =>
      have h1 := ih (k + 1) (by omega)
      have h0 := ih k (by omega)
      have hQ : heunRecQ (1 / a) α β γ (heunEps α β γ δ) (k + 1) =
          heunRecQ a α β γ δ (k + 1) / a := by
        unfold heunRecQ heunEps
        field_simp
        ring
      have hR : heunRecR (1 / a) γ (k + 1) = heunRecR a γ (k + 1) / a ^ 2 := by
        unfold heunRecR
        field_simp
      rw [heunLocalCoeff, heunLocalCoeff, h1, h0, hQ, hR, div_div_eq_mul_div, mul_div_assoc']
      congr 1
      field_simp
      ring

/-- DLMF 31.3.12: `Hl(a, q; α, β, γ, δ; z) = Hl(1/a, q/a; α, β, γ, α + β + 1 - γ - δ; z/a)`,
from the homography `z̃ = z/a`. Stronger than DLMF: proved for every `z` and all parameters with
`a ≠ 0`, since the two series agree term by term (including the junk values outside the disk of
convergence). -/
@[dlmf 31.3.E12]
theorem heunLocal_eq_heunLocal_inv (ha : a ≠ 0) (z : ℂ) :
    heunLocal a q α β γ δ z =
      heunLocal (1 / a) (q / a) α β γ (α + β + 1 - γ - δ) (z / a) := by
  rw [heunLocal, heunLocal]
  refine tsum_congr fun j => ?_
  rw [show α + β + 1 - γ - δ = heunEps α β γ δ from rfl, h31_heunLocalCoeff_inv ha, div_pow]
  field_simp

/-- The domain of 31.3.13 is star-shaped with respect to `0`. -/
lemma p1h_pfaff_domain_star {a : ℂ} {z : ℂ} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hz : ‖z‖ < heunLocalRadius a) (hz' : ‖z / (z - 1)‖ < heunLocalRadius (a / (a - 1))) :
    ‖(t : ℂ) * z‖ < heunLocalRadius a ∧
      ‖(t : ℂ) * z / ((t : ℂ) * z - 1)‖ < heunLocalRadius (a / (a - 1)) := by
  set ρ := heunLocalRadius (a / (a - 1))
  have hρ1 : ρ ≤ 1 := min_le_left _ _
  have hz1 : ‖z‖ < 1 := hz.trans_le (min_le_left _ _)
  have htz : ‖(t : ℂ) * z‖ ≤ ‖z‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht0]
    exact mul_le_of_le_one_left (norm_nonneg _) ht1
  refine ⟨htz.trans_lt hz, ?_⟩
  have hne : ∀ u : ℂ, ‖u‖ < 1 → u - 1 ≠ 0 := fun u hu h => by
    rw [sub_eq_zero] at h; rw [h, norm_one] at hu; exact lt_irrefl _ hu
  have hz1' := hne z hz1
  have htz1 := hne _ (htz.trans_lt hz1)
  rw [norm_div] at hz' ⊢
  rw [div_lt_iff₀ (norm_pos_iff.2 hz1')] at hz'
  rw [div_lt_iff₀ (norm_pos_iff.2 htz1)]
  have hsq : ∀ u : ℂ, ‖u‖ ^ 2 = u.re ^ 2 + u.im ^ 2 := fun u => by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hρ0 : 0 ≤ ρ := le_min zero_le_one (norm_nonneg _)
  have key : ‖z‖ ^ 2 < (ρ * ‖z - 1‖) ^ 2 := by
    have h0 : 0 ≤ ‖z‖ := norm_nonneg _
    exact pow_lt_pow_left₀ hz' h0 two_ne_zero
  refine lt_of_pow_lt_pow_left₀ 2 (mul_nonneg hρ0 (norm_nonneg _)) ?_
  rw [mul_pow] at key ⊢
  rw [hsq, hsq] at key
  rw [hsq, hsq]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero, add_zero, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im] at key ⊢
  have hn : 0 ≤ z.re ^ 2 + z.im ^ 2 := by positivity
  have hρ2 : ρ ^ 2 ≤ 1 := by nlinarith
  have hρpos : 0 < ρ := by
    by_contra h
    have : ρ = 0 := le_antisymm (not_lt.1 h) hρ0
    rw [this, zero_mul] at hz'
    exact absurd hz' (not_lt.2 (norm_nonneg _))
  have hprod := mul_nonneg (mul_nonneg hn (sub_nonneg.2 hρ2)) (mul_nonneg ht0 (sub_nonneg.2 ht1))
  rcases ht0.eq_or_lt with rfl | htpos
  · nlinarith
  · nlinarith [mul_pos htpos (sub_pos.2 key), mul_nonneg (sub_nonneg.2 ht1) (sq_nonneg ρ)]

/-- DLMF 31.3.13: `Hl(a, q; α, β, γ, δ; z)
= (1-z)^{-α} Hl(a/(a-1), -(q - aαγ)/(a-1); α, α + 1 - δ, γ, α + 1 - β; z/(z-1))`, from the
homography `z̃ = z/(z-1)`, where both series converge. -/
@[dlmf 31.3.E13]
theorem heunLocal_eq_pfaff (ha0 : a ≠ 0) (ha1 : a ≠ 1) (hγ : ∀ n : ℕ, γ ≠ -(n : ℂ)) {z : ℂ}
    (hz : ‖z‖ < heunLocalRadius a) (hz' : ‖z / (z - 1)‖ < heunLocalRadius (a / (a - 1))) :
    heunLocal a q α β γ δ z =
      (1 - z) ^ (-α) * heunLocal (a / (a - 1)) (-(q - a * α * γ) / (a - 1)) α (α + 1 - δ) γ
        (α + 1 - β) (z / (z - 1)) := by
  have ha1' : a - 1 ≠ 0 := sub_ne_zero.2 ha1
  have ha' : a / (a - 1) ≠ 0 := div_ne_zero ha0 ha1'
  set ρ := heunLocalRadius a
  set ρ' := heunLocalRadius (a / (a - 1))
  set H := heunLocal (a / (a - 1)) (-(q - a * α * γ) / (a - 1)) α (α + 1 - δ) γ (α + 1 - β)
  set G : ℂ → ℂ := fun z => (1 - z) ^ (-α) * H (z / (z - 1)) with hG
  set D : Set ℂ := {z | ‖z‖ < ρ ∧ ‖z / (z - 1)‖ < ρ'} with hD
  have hρ1 : ρ ≤ 1 := min_le_left _ _
  have hD1 : ∀ u ∈ D, ‖u‖ < 1 := fun u hu => hu.1.trans_le hρ1
  have hDne : ∀ u ∈ D, u - 1 ≠ 0 := fun u hu h => by
    have := hD1 u hu; rw [sub_eq_zero] at h; rw [h, norm_one] at this; exact lt_irrefl _ this
  have hDslit : ∀ u ∈ D, 1 - u ∈ slitPlane := fun u hu => by
    refine mem_slitPlane_iff.2 (Or.inl ?_)
    have := (Complex.re_le_norm u).trans_lt (hD1 u hu)
    simp only [Complex.sub_re, Complex.one_re]; linarith
  have hDopen : IsOpen D := by
    have hc : ContinuousOn (fun u : ℂ => ‖u / (u - 1)‖) (Metric.ball 0 1) := by
      refine ContinuousOn.norm (continuousOn_id.div (continuousOn_id.sub continuousOn_const)
        fun u hu => ?_)
      intro h; rw [sub_eq_zero] at h; rw [h, mem_ball_zero_iff, norm_one] at hu
      exact lt_irrefl _ hu
    have := (isOpen_lt continuous_norm (continuous_const (y := ρ))).inter
      (hc.isOpen_inter_preimage Metric.isOpen_ball (isOpen_Iio (a := ρ')))
    convert this using 1
    ext u
    simp only [hD, Set.mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_Iio, mem_ball_zero_iff]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, h1.trans_le hρ1, h2⟩
    · rintro ⟨h1, -, h2⟩; exact ⟨h1, h2⟩
  have h0D : (0 : ℂ) ∈ D := by
    simp only [hD, Set.mem_ofPred_eq, norm_zero, zero_div]
    exact ⟨p1h_radius_pos ha0, p1h_radius_pos ha'⟩
  have hDconn : IsPreconnected D := by
    have hstar : StarConvex ℝ (0 : ℂ) D := fun y hy s t hs ht hst => by
      have e : s • (0 : ℂ) + t • y = (t : ℂ) * y := by simp [Complex.real_smul]
      rw [e]
      exact p1h_pfaff_domain_star ht (by linarith) hy.1 hy.2
    exact (hstar.isPathConnected h0D).isConnected.isPreconnected
  have hHl : AnalyticOnNhd ℂ (heunLocal a q α β γ δ) D := fun u hu =>
    (heunLocal_isHeunSolOn (q := q) (α := α) (β := β) (δ := δ) ha0 hγ).1 u
      (mem_ball_zero_iff.2 hu.1)
  have hHH := heunLocal_isHeunSolOn (q := -(q - a * α * γ) / (a - 1)) (α := α)
    (β := α + 1 - δ) (δ := α + 1 - β) ha' hγ
  have hGa : AnalyticOnNhd ℂ G D := fun u hu => by
    have h1 : AnalyticAt ℂ (fun u : ℂ => (1 - u) ^ (-α)) u :=
      (analyticAt_const.sub analyticAt_id).cpow analyticAt_const (hDslit u hu)
    have h2 : AnalyticAt ℂ (fun u : ℂ => u / (u - 1)) u :=
      analyticAt_id.div (analyticAt_id.sub analyticAt_const) (hDne u hu)
    have h3 : AnalyticAt ℂ H (u / (u - 1)) := hHH.1 _ (mem_ball_zero_iff.2 hu.2)
    exact h1.mul (AnalyticAt.comp (g := H) (f := fun u : ℂ => u / (u - 1)) h3 h2)
  have hε : heunEps α (α + 1 - δ) γ (α + 1 - β) = heunEps α β γ δ := by unfold heunEps; ring
  have hw := hHH.2
  rw [hε] at hw
  have hsol : IsHeunSolOn a q α β γ δ (heunEps α β γ δ) G (D \ {0}) := by
    refine heun_homography_mobius ha1 (by unfold heunEps; ring) (hDopen.sdiff isClosed_singleton)
      (Metric.isOpen_ball.sdiff isClosed_singleton) (fun u hu => ?_) hw
    obtain ⟨hu, hu0⟩ := hu
    have hu0' : u ≠ 0 := hu0
    refine ⟨hDslit u hu, hu0', (p1h_ne_of_radius hu.1).2, mem_ball_zero_iff.2 hu.2, ?_⟩
    exact div_ne_zero hu0' (hDne u hu)
  have hev := eventuallyEq_heunLocal_of_analyticAt ha0 hγ (hDopen.mem_nhds h0D) (hGa 0 h0D) hsol
  have hG0 : G 0 = 1 := by simp [hG, H, heunLocal_zero]
  rw [hG0] at hev
  have hev' : heunLocal a q α β γ δ =ᶠ[𝓝 0] G := by
    filter_upwards [hev] with u hu
    rw [hu, one_mul]
  exact hHl.eqOn_of_preconnected_of_eventuallyEq hGa hDconn h0D hev' ⟨hz, hz'⟩

end DLMF.Heun
