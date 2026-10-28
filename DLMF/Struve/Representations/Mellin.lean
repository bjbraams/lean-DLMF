/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Struve.Representations.BarnesAndSonine

/-!
# Mellin transforms of Struve functions

Mellin integral representations of Struve functions, with convergence and endpoint estimates.

Source references and common attribution are retained in
`DLMF.Struve.Representations`.
-/

@[expose] public noncomputable section

open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF

open scoped Real Topology Nat

namespace DLMF.Struve

open DLMF.Bessel

/-! ### Mellin transforms of `H_ν` (DLMF 11.7.9–11.7.11)

The improper integrals `∫₀^∞ t^{μ-ν-1} H_ν(t) dt` converge only conditionally. For `re ν > -1/2`
the Poisson representation, the conditionally convergent Mellin transform of the sine
(`Complex.tendsto_integral_cpow_mul_sin`, obtained by Abel regularization) and dominated
convergence for improper parametric integrals give the value. Integration by parts with
`d/dt (t^{ν+1} H_{ν+1}) = t^{ν+1} H_ν` extends it to `re ν > re μ - 3/2`; the boundary terms
vanish by `H_ν = Y_ν + K_ν`, Hankel's expansion of `Y_ν` and the Laplace representation of `K_ν`.
-/

/-- `u^{μ-1} sin u = u^μ sinc u` for `u ≠ 0`. -/
theorem struveMel_cpow_mul_sin_eq (μ : ℂ) {u : ℝ} (hu : u ≠ 0) :
    (u : ℂ) ^ (μ - 1) * (Real.sin u : ℂ) = (u : ℂ) ^ μ * (Real.sinc u : ℂ) := by
  rw [Real.sinc_of_ne_zero hu, cpow_sub _ _ (ofReal_ne_zero.mpr hu), cpow_one]
  push_cast
  field_simp

/-- The Mellin sine integrand is interval integrable for `re μ > -1`. -/
theorem struveMel_intervalIntegrable {μ : ℂ} (h0 : -1 < μ.re) (a b : ℝ) :
    IntervalIntegrable (fun u : ℝ => (u : ℂ) ^ (μ - 1) * (Real.sin u : ℂ)) volume a b := by
  have h := (intervalIntegral.intervalIntegrable_cpow' h0 (a := a) (b := b)).mul_continuousOn
    (continuous_ofReal.comp Real.continuous_sinc).continuousOn
  refine h.congr_ae ?_
  have hn : ∀ᵐ u : ℝ ∂volume, u ≠ 0 := by
    rw [ae_iff]; simp [measure_singleton]
  refine ae_restrict_of_ae ?_
  filter_upwards [hn] with u hu
  exact (struveMel_cpow_mul_sin_eq μ hu).symm

/-- **Mellin transform of the sine** including Dirichlet's integral at `μ = 0`:
`∫₀^X u^{μ-1} sin u du → Γ(μ) sin(πμ/2)` (`π/2` at `μ = 0`) for `-1 < re μ < 1`. -/
theorem struveMel_tendsto_sin {μ : ℂ} (h0 : -1 < μ.re) (h1 : μ.re < 1) :
    Tendsto (fun X : ℝ => ∫ u in (0 : ℝ)..X, (u : ℂ) ^ (μ - 1) * (Real.sin u : ℂ)) atTop
      (𝓝 (if μ = 0 then (π / 2 : ℂ) else Gamma μ * sin (π * μ / 2))) := by
  split_ifs with hμ
  · subst hμ
    have h := (continuous_ofReal.tendsto _).comp TauCeti.Contour.tendsto_integral_sinc_atTop
    refine (h.congr fun X => ?_).trans (by push_cast; exact le_rfl)
    simp only [Function.comp, ← intervalIntegral.integral_ofReal]
    refine intervalIntegral.integral_congr_ae ?_
    have hn : ∀ᵐ u : ℝ ∂volume, u ≠ 0 := by
      rw [ae_iff]; simp [measure_singleton]
    filter_upwards [hn] with u hu _
    rw [struveMel_cpow_mul_sin_eq 0 hu, cpow_zero, one_mul]
  · exact Complex.tendsto_integral_cpow_mul_sin h0 h1 hμ

/-- The partial Mellin sine integrals are bounded on `[0, ∞)`. -/
theorem struveMel_exists_bound {μ : ℂ} (h0 : -1 < μ.re) (h1 : μ.re < 1) :
    ∃ C, ∀ X : ℝ, 0 ≤ X →
      ‖∫ u in (0 : ℝ)..X, (u : ℂ) ^ (μ - 1) * (Real.sin u : ℂ)‖ ≤ C := by
  have hc : Continuous (fun X : ℝ => ∫ u in (0 : ℝ)..X, (u : ℂ) ^ (μ - 1) * (Real.sin u : ℂ)) :=
    intervalIntegral.continuous_primitive (struveMel_intervalIntegrable h0) 0
  obtain ⟨C, hC⟩ := MeasureTheory.exists_norm_le_of_continuousOn_of_tendsto hc.continuousOn
    (struveMel_tendsto_sin h0 h1)
  exact ⟨C, fun X hX => hC X hX⟩

/-- Scaling: `∫₀^R t^{μ-1} sin(ct) dt = c^{-μ} ∫₀^{Rc} u^{μ-1} sin u du` for `c > 0`. -/
theorem struveMel_integral_scale (μ : ℂ) {c : ℝ} (hc : 0 < c) {R : ℝ} (hR : 0 ≤ R) :
    ∫ t in (0 : ℝ)..R, (t : ℂ) ^ (μ - 1) * (Real.sin (t * c) : ℂ) =
      (c : ℂ) ^ (-μ) * ∫ u in (0 : ℝ)..R * c, (u : ℂ) ^ (μ - 1) * (Real.sin u : ℂ) := by
  have h := intervalIntegral.integral_comp_mul_right
    (fun u : ℝ => (u : ℂ) ^ (μ - 1) * (Real.sin u : ℂ)) hc.ne' (a := 0) (b := R)
  simp only [zero_mul] at h
  have hc0 : (c : ℂ) ≠ 0 := ofReal_ne_zero.mpr hc.ne'
  have hpt : ∀ t : ℝ, 0 ≤ t → (t : ℂ) ^ (μ - 1) * (Real.sin (t * c) : ℂ) =
      (c : ℂ) ^ (1 - μ) * (((t * c : ℝ) : ℂ) ^ (μ - 1) * (Real.sin (t * c) : ℂ)) := by
    intro t ht
    rw [ofReal_mul, mul_cpow_ofReal_nonneg ht hc.le, ← mul_assoc, ← mul_assoc,
      mul_comm ((c : ℂ) ^ (1 - μ)), mul_assoc ((t : ℂ) ^ (μ - 1)), ← cpow_add _ _ hc0]
    simp
  rw [intervalIntegral.integral_congr (g := fun t : ℝ => (c : ℂ) ^ (1 - μ) *
      (((t * c : ℝ) : ℂ) ^ (μ - 1) * (Real.sin (t * c) : ℂ))) (fun t ht => by
        rw [uIcc_of_le hR] at ht; exact hpt t ht.1),
    intervalIntegral.integral_const_mul, h, Complex.real_smul, ← mul_assoc]
  congr 1
  rw [show (1 - μ) = -μ + 1 by ring, cpow_add _ _ hc0, cpow_one, ofReal_inv]
  field_simp

/-- `sin^{2a-1} θ cos^{2b-1} θ` is integrable on `(0, π/2]` with the Beta value. -/
theorem struveMel_trigBeta {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) :
    IntegrableOn (fun θ : ℝ => (Real.sin θ : ℂ) ^ (2 * a - 1) * (Real.cos θ : ℂ) ^ (2 * b - 1))
      (Ioc 0 (π / 2)) ∧
    ∫ θ in Ioc 0 (π / 2), (Real.sin θ : ℂ) ^ (2 * a - 1) * (Real.cos θ : ℂ) ^ (2 * b - 1) =
      Gamma a * Gamma b / (2 * Gamma (a + b)) := by
  obtain ⟨h1, h2⟩ := trigBeta ha hb
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity)).mp h1, ?_⟩
  rw [← intervalIntegral.integral_of_le (by positivity), h2]

/-- The direct region of the Struve Mellin transform: for `re ν > -1/2` and `|re μ| < 1`,
`∫₀^R t^{μ-ν-1} H_ν(t) dt` converges to the Poisson–Beta value. -/
theorem struveMel_tendsto_direct {μ ν : ℂ} (hμ0 : -1 < μ.re) (hμ1 : μ.re < 1)
    (hν : -1 / 2 < ν.re) :
    Tendsto (fun R : ℝ => ∫ t in (0 : ℝ)..R, (t : ℂ) ^ (μ - ν - 1) * struveH ν t) atTop
      (𝓝 (2 * (1 / 2 : ℂ) ^ ν / (Real.sqrt π * Gamma (ν + 1 / 2)) *
        ((if μ = 0 then (π / 2 : ℂ) else Gamma μ * sin (π * μ / 2)) *
          (Gamma (ν + 1 / 2) * Gamma ((1 - μ) / 2) / (2 * Gamma (ν + 1 / 2 + (1 - μ) / 2)))))) := by
  set S : ℂ := if μ = 0 then (π / 2 : ℂ) else Gamma μ * sin (π * μ / 2)
  set A : ℂ := 2 * (1 / 2 : ℂ) ^ ν / (Real.sqrt π * Gamma (ν + 1 / 2))
  set K : ℝ → ℝ → ℂ := fun t θ =>
    (t : ℂ) ^ (μ - 1) * (Real.sin (t * Real.cos θ) : ℂ) * (Real.sin θ : ℂ) ^ (2 * ν)
  set m : Measure ℝ := volume.restrict (Ioc 0 (π / 2))
  have ha : 0 < (ν + 1 / 2).re := by simp; linarith
  have hb : 0 < ((1 - μ) / 2).re := by simp; linarith
  have hb' : 0 < (1 / 2 : ℂ).re := by norm_num
  -- the weight `sin^{2ν}` and the Beta weight
  have hW := struveMel_trigBeta ha hb'
  have hB := struveMel_trigBeta ha hb
  have e1 : 2 * (ν + 1 / 2) - 1 = 2 * ν := by ring
  have e2 : 2 * (1 / 2 : ℂ) - 1 = 0 := by norm_num
  have e3 : 2 * ((1 - μ) / 2) - 1 = -μ := by ring
  simp only [e1, e2, e3, cpow_zero, mul_one] at hW hB
  obtain ⟨C, hC⟩ := struveMel_exists_bound hμ0 hμ1
  have hθ : ∀ᵐ θ ∂m, θ ∈ Ioo 0 (π / 2) := by
    have hn : ∀ᵐ θ : ℝ ∂volume, θ ≠ π / 2 := by
      rw [ae_iff]; simp [measure_singleton]
    filter_upwards [ae_restrict_mem measurableSet_Ioc, ae_restrict_of_ae hn] with θ h1 h2
    exact ⟨h1.1, lt_of_le_of_ne h1.2 h2⟩
  have hcos : ∀ θ ∈ Ioo 0 (π / 2), 0 < Real.cos θ := fun θ h =>
    Real.cos_pos_of_mem_Ioo ⟨by linarith [h.1, Real.pi_pos], h.2⟩
  have hinner : ∀ θ ∈ Ioo 0 (π / 2), ∀ R : ℝ, 0 ≤ R → ∫ t in (0 : ℝ)..R, K t θ =
      (Real.sin θ : ℂ) ^ (2 * ν) * (Real.cos θ : ℂ) ^ (-μ) *
        ∫ u in (0 : ℝ)..R * Real.cos θ, (u : ℂ) ^ (μ - 1) * (Real.sin u : ℂ) := by
    intro θ hθ R hR
    simp only [K]
    rw [intervalIntegral.integral_mul_const, struveMel_integral_scale μ (hcos θ hθ) hR]
    ring
  have hsinpos : ∀ θ ∈ Ioc 0 (π / 2), 0 < Real.sin θ := fun θ h =>
    Real.sin_pos_of_pos_of_lt_pi h.1 (by linarith [h.2, Real.pi_pos])
  have hmain : Tendsto (fun R => ∫ t in (0 : ℝ)..R, ∫ θ, K t θ ∂m) atTop
      (𝓝 (∫ θ, (Real.sin θ : ℂ) ^ (2 * ν) * (Real.cos θ : ℂ) ^ (-μ) * S ∂m)) := by
    refine MeasureTheory.tendsto_intervalIntegral_integral_of_dominated
      (bound := fun θ => C * ‖(Real.sin θ : ℂ) ^ (2 * ν) * (Real.cos θ : ℂ) ^ (-μ)‖)
      (fun R hR => ?_) (fun R hR => ?_) (hB.1.norm.const_mul C) ?_
    · have hT : Integrable (fun t : ℝ => t ^ μ.re) (volume.restrict (Ioc 0 R)) :=
        (intervalIntegrable_iff_integrableOn_Ioc_of_le hR).mp
          (intervalIntegral.intervalIntegrable_rpow' hμ0)
      have hF : Integrable (fun p : ℝ × ℝ => p.1 ^ μ.re * ‖(Real.sin p.2 : ℂ) ^ (2 * ν)‖)
          ((volume.restrict (Ioc 0 R)).prod m) := Integrable.mul_prod hT hW.1.norm
      refine hF.mono' ?_ ?_
      · rw [Measure.prod_restrict]
        refine ContinuousOn.aestronglyMeasurable (fun p hp => ?_)
          (measurableSet_Ioc.prod measurableSet_Ioc)
        have ht : 0 < p.1 := hp.1.1
        have hs : 0 < Real.sin p.2 := hsinpos p.2 hp.2
        refine ContinuousAt.continuousWithinAt ?_
        simp only [K]
        refine ContinuousAt.mul (ContinuousAt.mul ?_ (by fun_prop)) ?_
        · exact ((continuous_ofReal.continuousAt).cpow continuousAt_const
            (ofReal_mem_slitPlane.mpr ht)).comp continuousAt_fst
        · exact ContinuousAt.comp (x := p) (f := fun q : ℝ × ℝ => Real.sin q.2)
            (g := fun x : ℝ => (x : ℂ) ^ (2 * ν))
            ((continuous_ofReal.continuousAt).cpow continuousAt_const
              (ofReal_mem_slitPlane.mpr hs)) (by fun_prop)
      · rw [Measure.prod_restrict]
        filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)] with p hp
        have ht : 0 < p.1 := hp.1.1
        simp only [K, Function.uncurry, norm_mul, norm_real, Real.norm_eq_abs,
          norm_cpow_eq_rpow_re_of_pos ht]
        have hsin : |Real.sin (p.1 * Real.cos p.2)| ≤ p.1 := by
          refine (Real.abs_sin_le_abs).trans ?_
          rw [abs_mul, abs_of_pos ht]
          exact mul_le_of_le_one_right ht.le (Real.abs_cos_le_one _)
        have hre : (μ - 1).re = μ.re - 1 := by simp
        rw [hre]
        have hp1 : p.1 ^ (μ.re - 1) * p.1 = p.1 ^ μ.re := by
          rw [Real.rpow_sub_one ht.ne']; field_simp
        calc p.1 ^ (μ.re - 1) * |Real.sin (p.1 * Real.cos p.2)| * ‖(Real.sin p.2 : ℂ) ^ (2 * ν)‖
            ≤ p.1 ^ (μ.re - 1) * p.1 * ‖(Real.sin p.2 : ℂ) ^ (2 * ν)‖ := by gcongr
          _ = _ := by rw [hp1]
    · filter_upwards [hθ] with θ hθ'
      rw [hinner θ hθ' R hR, norm_mul, mul_comm C]
      exact mul_le_mul_of_nonneg_left (hC _ (mul_nonneg hR (hcos θ hθ').le)) (norm_nonneg _)
    · filter_upwards [hθ] with θ hθ'
      have h := ((struveMel_tendsto_sin hμ0 hμ1).comp
        (tendsto_id.atTop_mul_const (hcos θ hθ'))).const_mul
        ((Real.sin θ : ℂ) ^ (2 * ν) * (Real.cos θ : ℂ) ^ (-μ))
      refine h.congr' ?_
      filter_upwards [eventually_ge_atTop 0] with R hR
      rw [hinner θ hθ' R hR]
      rfl
  rw [integral_mul_const, hB.2] at hmain
  have hpt : ∀ t : ℝ, 0 < t → (t : ℂ) ^ (μ - ν - 1) * struveH ν t = A * ∫ θ, K t θ ∂m := by
    intro t ht
    have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
    rw [struveH_trig_integral hν (ofReal_mem_slitPlane.mpr ht),
      intervalIntegral.integral_of_le (by positivity)]
    have hK : ∀ θ, K t θ = (t : ℂ) ^ (μ - 1) *
        (sin ((t : ℂ) * (Real.cos θ : ℂ)) * (Real.sin θ : ℂ) ^ (2 * ν)) := by
      intro θ; simp only [K]; push_cast; ring
    simp_rw [hK]
    rw [integral_const_mul]
    have hh : (t : ℂ) / 2 = ((t : ℝ) : ℂ) * ((1 / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [hh, mul_cpow_ofReal_nonneg ht.le (by norm_num)]
    have hc : (t : ℂ) ^ (μ - ν - 1) * (t : ℂ) ^ ν = (t : ℂ) ^ (μ - 1) := by
      rw [← cpow_add _ _ ht0]; ring_nf
    simp only [A, m]
    rw [show ((1 / 2 : ℝ) : ℂ) = (1 / 2 : ℂ) by push_cast; ring, ← hc]
    ring
  refine (hmain.const_mul A).congr' ?_ |>.trans (by rw [mul_comm S])
  filter_upwards [eventually_ge_atTop 0] with R hR
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun t ht => ?_)
  rw [uIoc_of_le hR] at ht
  exact (hpt t ht.1).symm

/-- `(1/2)^ν = 2^{-ν}`. -/
theorem struveMel_half_cpow (ν : ℂ) : (1 / 2 : ℂ) ^ ν = (2 : ℂ) ^ (-ν) := by
  have h : (2 : ℂ).arg = 0 := by simp
  rw [one_div, inv_cpow _ _ (by rw [h]; exact Real.pi_ne_zero.symm), cpow_neg]

/-- `z / Γ(z+1) = 1/Γ(z)` for every complex `z` (with Mathlib's conventions at the poles). -/
theorem struveMel_div_Gamma_add_one (z : ℂ) : z / Gamma (z + 1) = (Gamma z)⁻¹ := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  · rw [Complex.Gamma_add_one z hz]
    rcases eq_or_ne (Gamma z) 0 with h | h
    · simp [h]
    · field_simp

/-- The Struve Mellin value `V(μ, ν)` of DLMF 11.7.10–11.7.11. -/
theorem struveMel_value_eq {μ ν : ℂ} (hμ0 : -1 < μ.re) (hμ1 : μ.re < 1) (hν : -1 / 2 < ν.re) :
    2 * (1 / 2 : ℂ) ^ ν / (Real.sqrt π * Gamma (ν + 1 / 2)) *
        ((if μ = 0 then (π / 2 : ℂ) else Gamma μ * sin (π * μ / 2)) *
          (Gamma (ν + 1 / 2) * Gamma ((1 - μ) / 2) / (2 * Gamma (ν + 1 / 2 + (1 - μ) / 2)))) =
      if μ = 0 then π / (2 ^ (ν + 1) * Gamma (ν + 1))
      else Gamma (μ / 2) * 2 ^ (μ - ν - 1) * sin (π * μ / 2) /
        (cos (π * μ / 2) * Gamma (ν - μ / 2 + 1)) := by
  have hG1 : Gamma (ν + 1 / 2) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp; linarith)
  have hsq : (Real.sqrt π : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hsq2 : (Real.sqrt π : ℂ) * (Real.sqrt π : ℂ) = π := by
    rw [← ofReal_mul, Real.mul_self_sqrt Real.pi_pos.le]
  have h2 : (2 : ℂ) ^ (-ν) * (2 : ℂ) ^ ν = 1 := by
    rw [← cpow_add _ _ two_ne_zero]; simp
  rw [struveMel_half_cpow]
  split_ifs with hμ
  · subst hμ
    have hG : Gamma (ν + 1 / 2 + (1 - 0) / 2) = Gamma (ν + 1) := by ring_nf
    rw [hG, show (1 - (0 : ℂ)) / 2 = 1 / 2 by ring, DLMF.Confluent.Gamma_one_half_eq_sqrt,
      cpow_add _ _ two_ne_zero, cpow_one]
    generalize Gamma (ν + 1 / 2) = G at hG1 ⊢
    rcases eq_or_ne (Gamma (ν + 1)) 0 with h | h
    · simp [h]
    · field_simp
      linear_combination h2
  · have hG2 : Gamma (ν + 1 / 2 + (1 - μ) / 2) = Gamma (ν - μ / 2 + 1) := by ring_nf
    rw [hG2]
    have hh : Gamma (μ / 2 + 1 / 2) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp; linarith)
    have hD : Gamma (ν - μ / 2 + 1) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp; linarith)
    have hc : cos (π * μ / 2) ≠ 0 := by
      rw [Ne, Complex.cos_eq_zero_iff]
      rintro ⟨k, hk⟩
      have hμk : μ = 2 * k + 1 := by
        have hp : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
        field_simp at hk
        linear_combination hk
      have hre := congrArg Complex.re hμk
      simp at hre
      have h1 : (2 * k + 1 : ℝ) < 1 := by linarith
      have h2 : -1 < (2 * k + 1 : ℝ) := by linarith
      have h3 : k < 0 := by exact_mod_cast (show (k : ℝ) < 0 by linarith)
      have h4 : -1 < k := by exact_mod_cast (show (-1 : ℝ) < k by linarith)
      omega
    have hQ : (2 : ℂ) ^ (1 - μ) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl two_ne_zero)
    have hdup := Complex.Gamma_mul_Gamma_add_half (μ / 2)
    rw [show 2 * (μ / 2) = μ by ring] at hdup
    have hrefl := Complex.Gamma_mul_Gamma_one_sub (μ / 2 + 1 / 2)
    rw [show 1 - (μ / 2 + 1 / 2) = (1 - μ) / 2 by ring,
      show (π : ℂ) * (μ / 2 + 1 / 2) = π * μ / 2 + π / 2 by ring, Complex.sin_add_pi_div_two]
      at hrefl
    have hQT : (2 : ℂ) ^ (-ν) = (2 : ℂ) ^ (1 - μ) * (2 : ℂ) ^ (μ - ν - 1) := by
      rw [← cpow_add _ _ two_ne_zero]; ring_nf
    have ha : Gamma μ = Gamma (μ / 2) * Gamma (μ / 2 + 1 / 2) / ((2 : ℂ) ^ (1 - μ) * Real.sqrt π) := by
      rw [hdup]; field_simp
    have hb : Gamma ((1 - μ) / 2) = Real.sqrt π * Real.sqrt π /
        (cos (π * μ / 2) * Gamma (μ / 2 + 1 / 2)) := by
      rw [hsq2, eq_div_iff (mul_ne_zero hc hh), ← mul_assoc, mul_comm _ (cos _),
        mul_assoc, mul_comm (Gamma _) (Gamma _), hrefl]
      field_simp
    rw [ha, hb, hQT]
    generalize Gamma (ν + 1 / 2) = G at hG1 ⊢
    generalize Gamma (μ / 2 + 1 / 2) = H at hh ⊢
    generalize Gamma (ν - μ / 2 + 1) = D at hD ⊢
    generalize cos (π * μ / 2) = c at hc ⊢
    field_simp

/-- `x^a = O(x^b)` at infinity when `a ≤ b`. -/
theorem struveMel_rpow_isBigO_rpow {a b : ℝ} (h : a ≤ b) :
    (fun x : ℝ => x ^ a) =O[atTop] (fun x : ℝ => x ^ b) := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [eventually_ge_atTop 1] with x hx
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos (by linarith) _),
    abs_of_pos (Real.rpow_pos_of_pos (by linarith) _), one_mul]
  exact Real.rpow_le_rpow_of_exponent_le hx h

/-- `Y_ν(x) = O(x^{-1/2})` as `x → +∞`, for every complex order. -/
theorem struveMel_besselY_isBigO (ν : ℂ) :
    (fun x : ℝ => besselY ν x) =O[atTop] (fun x : ℝ => x ^ (-(1 / 2) : ℝ)) := by
  -- the Hankel function
  have hH : (fun x : ℝ => hankelH1 ν x) =O[atTop] (fun x : ℝ => x ^ (-(1 / 2) : ℝ)) := by
    have h0 := hasAsymptoticExpansion_hankelH1 ν 0
    simp only [Finset.range_zero, Finset.sum_empty, sub_zero, Nat.cast_zero, zero_add] at h0
    have hs : (fun x : ℝ => (2 * (-I * x)) ^ (-(1 / 2 : ℂ))) =O[atTop]
        (fun x : ℝ => x ^ (-(1 / 2) : ℝ)) := by
      refine IsBigO.of_bound 1 ?_
      filter_upwards [eventually_gt_atTop 0] with x hx
      have hz : (2 * (-I * (x : ℂ))) ≠ 0 := by
        simp [hx.ne', I_ne_zero]
      rw [norm_cpow_of_ne_zero hz]
      have him : (-(1 / 2 : ℂ)).im = 0 := by simp
      have hre : (-(1 / 2 : ℂ)).re = -(1 / 2) := by norm_num
      rw [him, hre, mul_zero, Real.exp_zero, div_one, Real.norm_eq_abs,
        abs_of_pos (Real.rpow_pos_of_pos hx _), one_mul]
      have hn : ‖2 * (-I * (x : ℂ))‖ = 2 * x := by
        simp [abs_of_pos hx]
      rw [hn, Real.mul_rpow (by norm_num) hx.le]
      have h2 : (2 : ℝ) ^ (-(1 / 2) : ℝ) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
      exact mul_le_of_le_one_left (Real.rpow_nonneg hx.le _) h2
    have h1 := h0.trans hs
    have he : (fun x : ℝ => exp (I * x)) =O[atTop] (fun _ : ℝ => (1 : ℝ)) :=
      IsBigO.of_bound 1 (Eventually.of_forall fun x => by
        rw [norm_exp_I_mul_ofReal]; simp)
    have h2 := he.mul h1
    simp only [one_mul] at h2
    refine h2.congr' (Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => rfl)
    dsimp only
    rw [← mul_assoc, ← Complex.exp_add]
    simp
  -- the Bessel function `J`
  have hJ : (fun x : ℝ => besselJ ν x) =O[atTop] (fun x : ℝ => x ^ (-(1 / 2) : ℝ)) := by
    have h1 := (besselJ_sub_cos_isBigO ν).trans (struveMel_rpow_isBigO_rpow
      (show (-(3 / 2) : ℝ) ≤ -(1 / 2) by norm_num))
    set c : ℂ := ν * π / 2 + π / 4
    have hc : (fun x : ℝ => (Real.sqrt (2 / (π * x)) : ℂ) * cos (x - ν * π / 2 - π / 4)) =O[atTop]
        (fun x : ℝ => x ^ (-(1 / 2) : ℝ)) := by
      refine IsBigO.of_bound (Real.sqrt (2 / π) * Real.exp |c.im|) ?_
      filter_upwards [eventually_gt_atTop 0] with x hx
      rw [norm_mul, norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _), abs_of_pos (Real.rpow_pos_of_pos hx _)]
      have hs : Real.sqrt (2 / (π * x)) = Real.sqrt (2 / π) * x ^ (-(1 / 2) : ℝ) := by
        rw [show 2 / (π * x) = 2 / π * x⁻¹ by field_simp, Real.sqrt_mul (by positivity),
          Real.sqrt_inv, Real.rpow_neg hx.le, ← Real.sqrt_eq_rpow]
      have hcos : ‖cos ((x : ℂ) - ν * π / 2 - π / 4)‖ ≤ Real.exp |c.im| := by
        rw [show (x : ℂ) - ν * π / 2 - π / 4 = x - c by simp only [c]; ring, Complex.cos]
        have e1 : ‖exp ((x - c) * I)‖ = Real.exp c.im := by
          rw [Complex.norm_exp]; simp
        have e2 : ‖exp (-(x - c) * I)‖ = Real.exp (-c.im) := by
          rw [Complex.norm_exp]; simp
        calc ‖(exp ((x - c) * I) + exp (-(x - c) * I)) / 2‖
            ≤ (‖exp ((x - c) * I)‖ + ‖exp (-(x - c) * I)‖) / 2 := by
              rw [norm_div]; simp only [Complex.norm_ofNat]
              gcongr; exact norm_add_le _ _
          _ ≤ (Real.exp |c.im| + Real.exp |c.im|) / 2 := by
              rw [e1, e2]; gcongr
              · exact le_abs_self _
              · exact neg_le_abs _
          _ = Real.exp |c.im| := by ring
      rw [hs]
      calc Real.sqrt (2 / π) * x ^ (-(1 / 2) : ℝ) * ‖cos ((x : ℂ) - ν * π / 2 - π / 4)‖
          ≤ Real.sqrt (2 / π) * x ^ (-(1 / 2) : ℝ) * Real.exp |c.im| := by gcongr
        _ = _ := by ring
    exact (h1.add hc).congr' (Eventually.of_forall fun x => by ring)
      (Eventually.of_forall fun x => rfl)
  have h := (hH.sub hJ).const_mul_left (-I)
  refine h.congr' (Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => rfl)
  simp only [hankelH1]
  ring_nf
  rw [I_sq]; ring

/-- `K_ν(x) = O(x^{re ν - 1})` as `x → +∞` when `re ν ≤ 1/2`, from the Laplace representation
DLMF 11.5.2. -/
theorem struveMel_struveK_isBigO {ν : ℂ} (hν : ν.re ≤ 1 / 2) :
    (fun x : ℝ => struveK ν x) =O[atTop] (fun x : ℝ => x ^ (ν.re - 1)) := by
  set A : ℝ := ‖2 / ((Real.sqrt π : ℂ) * Gamma (ν + 1 / 2))‖
  refine IsBigO.of_bound (A * 2 ^ (-ν.re)) ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  have hre : 0 < (x : ℂ).re := by simpa using hx
  rw [struveK_eq_besselYLaplace ν hre, besselYLaplace]
  have hint : ‖∫ t in Ioi (0 : ℝ), yLaplaceKernel ν x t‖ ≤ 1 / x := by
    have hg : IntegrableOn (fun t : ℝ => Real.exp (-x * t)) (Ioi 0) :=
      exp_neg_integrableOn_Ioi 0 hx
    have hval : ∫ t in Ioi (0 : ℝ), Real.exp (-x * t) = 1 / x := by
      have := integral_exp_mul_Ioi (a := -x) (by linarith) 0
      simp only [mul_zero, Real.exp_zero] at this
      rw [this]; field_simp
    rw [← hval]
    refine norm_integral_le_of_norm_le hg ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [yLaplaceKernel, norm_mul, Complex.norm_exp]
    have h1 : (1 + (t : ℂ) ^ 2) = ((1 + t ^ 2 : ℝ) : ℂ) := by push_cast; ring
    rw [h1, norm_cpow_eq_rpow_re_of_pos (by positivity)]
    have h2 : (1 + t ^ 2) ^ (ν - 1 / 2).re ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith) (by simp; linarith)
    have h3 : (-(x : ℂ) * t).re = -x * t := by simp
    rw [h3]
    exact mul_le_of_le_one_right (Real.exp_pos _).le h2
  have hpow : ‖((x : ℂ) / 2) ^ ν‖ = 2 ^ (-ν.re) * x ^ ν.re := by
    rw [show (x : ℂ) / 2 = ((x / 2 : ℝ) : ℂ) by push_cast; ring,
      norm_cpow_eq_rpow_re_of_pos (by positivity), Real.div_rpow hx.le (by norm_num),
      Real.rpow_neg (by norm_num)]
    ring
  rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hx _)]
  calc ‖2 * ((x : ℂ) / 2) ^ ν / (Real.sqrt π * Gamma (ν + 1 / 2)) *
        ∫ t in Ioi (0 : ℝ), yLaplaceKernel ν x t‖
      = A * ‖((x : ℂ) / 2) ^ ν‖ * ‖∫ t in Ioi (0 : ℝ), yLaplaceKernel ν x t‖ := by
        simp only [A, norm_mul, norm_div]; ring
    _ ≤ A * (2 ^ (-ν.re) * x ^ ν.re) * (1 / x) := by
        rw [hpow]; gcongr
    _ = A * 2 ^ (-ν.re) * x ^ (ν.re - 1) := by
        rw [Real.rpow_sub_one hx.ne']; ring

/-- `H_ν(x) = O(x^{-1/2} + x^{re ν - 1})` as `x → +∞` when `re ν ≤ 1/2`. -/
theorem struveMel_struveH_isBigO {ν : ℂ} (hν : ν.re ≤ 1 / 2) :
    (fun x : ℝ => struveH ν x) =O[atTop] (fun x : ℝ => x ^ (-(1 / 2) : ℝ) + x ^ (ν.re - 1)) := by
  have hY := struveMel_besselY_isBigO ν
  have hK := struveMel_struveK_isBigO hν
  have hpos : ∀ᶠ x : ℝ in atTop, 0 < x := eventually_gt_atTop 0
  have h1 : (fun x : ℝ => x ^ (-(1 / 2) : ℝ)) =O[atTop]
      (fun x : ℝ => x ^ (-(1 / 2) : ℝ) + x ^ (ν.re - 1)) := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [hpos] with x hx
    have a := Real.rpow_pos_of_pos hx (-(1 / 2))
    have b := Real.rpow_pos_of_pos hx (ν.re - 1)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos a, abs_of_pos (by linarith)]
    linarith
  have h2 : (fun x : ℝ => x ^ (ν.re - 1)) =O[atTop]
      (fun x : ℝ => x ^ (-(1 / 2) : ℝ) + x ^ (ν.re - 1)) := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [hpos] with x hx
    have a := Real.rpow_pos_of_pos hx (-(1 / 2))
    have b := Real.rpow_pos_of_pos hx (ν.re - 1)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos b, abs_of_pos (by linarith)]
    linarith
  refine ((hY.trans h1).add (hK.trans h2)).congr' (Eventually.of_forall fun x => ?_)
    (Eventually.of_forall fun x => rfl)
  simp only [struveK]; ring

/-- The integration-by-parts boundary term `R^{μ-ν} H_ν(R)` tends to zero when `re ν ≤ 1/2`,
`re μ < 1` and `re μ < re ν + 1/2`. -/
theorem struveMel_tendsto_boundary {μ ν : ℂ} (hν : ν.re ≤ 1 / 2) (h1 : μ.re < 1)
    (h2 : μ.re < ν.re + 1 / 2) :
    Tendsto (fun R : ℝ => (R : ℂ) ^ (μ - ν) * struveH ν R) atTop (𝓝 0) := by
  have hp : (fun R : ℝ => (R : ℂ) ^ (μ - ν)) =O[atTop] (fun R : ℝ => R ^ (μ.re - ν.re)) := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [eventually_gt_atTop 0] with R hR
    rw [norm_cpow_eq_rpow_re_of_pos hR, Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos hR _), one_mul]
    simp
  have hb := hp.mul (struveMel_struveH_isBigO hν)
  refine hb.trans_tendsto ?_
  have t1 := tendsto_rpow_neg_atTop (y := -(μ.re - ν.re - 1 / 2)) (by linarith)
  have t2 := tendsto_rpow_neg_atTop (y := -(μ.re - 1)) (by linarith)
  simp only [neg_neg] at t1 t2
  refine (t1.add t2).congr' ?_ |>.trans (by rw [add_zero])
  filter_upwards [eventually_gt_atTop 0] with R hR
  rw [mul_add, ← Real.rpow_add hR, ← Real.rpow_add hR]
  congr 1; ring_nf

/-- For `t > 0`, `t^a H_ν(t) = t^{a+ν+1} (1/2)^{ν+1} H̃_ν(t)` with the entire core `H̃_ν`. -/
theorem struveMel_cpow_mul_struveH (a ν : ℂ) {t : ℝ} (ht : 0 < t) :
    (t : ℂ) ^ a * struveH ν t = (t : ℂ) ^ (a + ν + 1) * ((1 / 2 : ℂ) ^ (ν + 1) * struveHCore ν t) := by
  have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
  rw [struveH, show (t : ℂ) / 2 = ((t : ℝ) : ℂ) * ((1 / 2 : ℝ) : ℂ) by push_cast; ring,
    mul_cpow_ofReal_nonneg ht.le (by norm_num), show ((1 / 2 : ℝ) : ℂ) = (1 / 2 : ℂ) by push_cast; ring,
    show a + ν + 1 = a + (ν + 1) by ring, cpow_add a (ν + 1) ht0]
  ring

/-- The Struve Mellin integrand `t^{μ-ν-1} H_ν(t)` is interval integrable on `[0, R]`
when `re μ > -1`. -/
theorem struveMel_intervalIntegrable_struveH {μ : ℂ} (hμ0 : -1 < μ.re) (ν : ℂ) {R : ℝ} (hR : 0 ≤ R) :
    IntervalIntegrable (fun t : ℝ => (t : ℂ) ^ (μ - ν - 1) * struveH ν t) volume 0 R := by
  have h := (intervalIntegral.intervalIntegrable_cpow' hμ0 (a := 0) (b := R)).mul_continuousOn
    (g := fun t : ℝ => (1 / 2 : ℂ) ^ (ν + 1) * struveHCore ν t)
    (continuous_const.mul ((entire_struveHCore ν).continuous.comp continuous_ofReal)).continuousOn
  refine h.congr (fun t ht => ?_)
  rw [uIoc_of_le hR] at ht
  rw [struveMel_cpow_mul_struveH _ _ ht.1]
  ring_nf

/-- **Integration by parts** in the Struve Mellin integral, from `d/dt (t^{ν+1} H_{ν+1}) =
t^{ν+1} H_ν` (DLMF 11.4.27). -/
theorem struveMel_integral_by_parts {μ : ℂ} (hμ0 : -1 < μ.re) (ν : ℂ) {R : ℝ} (hR : 0 < R) :
    ∫ t in (0 : ℝ)..R, (t : ℂ) ^ (μ - ν - 1) * struveH ν t =
      (R : ℂ) ^ (μ - (ν + 1)) * struveH (ν + 1) R -
        (μ - 2 * ν - 2) * ∫ t in (0 : ℝ)..R, (t : ℂ) ^ (μ - (ν + 1) - 1) * struveH (ν + 1) t := by
  set F : ℝ → ℂ := fun t => (t : ℂ) ^ (μ + 1) * ((1 / 2 : ℂ) ^ (ν + 1 + 1) * struveHCore (ν + 1) t)
  have hF : ∀ t : ℝ, 0 < t → F t = (t : ℂ) ^ (μ - (ν + 1)) * struveH (ν + 1) t := by
    intro t ht
    rw [struveMel_cpow_mul_struveH _ _ ht]
    simp only [F]; ring_nf
  have hFc : ContinuousOn F (Icc 0 R) := by
    refine Continuous.continuousOn ?_
    refine Continuous.mul ?_ (continuous_const.mul
      ((entire_struveHCore (ν + 1)).continuous.comp continuous_ofReal))
    exact continuous_iff_continuousAt.mpr fun t =>
      continuousAt_ofReal_cpow_const t (μ + 1) (Or.inl (by simp; linarith))
  have hF0 : F 0 = 0 := by
    simp only [F, ofReal_zero]
    rw [zero_cpow (by intro h; have := congrArg Complex.re h; simp at this; linarith), zero_mul]
  set f' : ℝ → ℂ := fun t => (t : ℂ) ^ (μ - ν - 1) * struveH ν t +
    (μ - 2 * ν - 2) * ((t : ℂ) ^ (μ - (ν + 1) - 1) * struveH (ν + 1) t)
  have hderiv : ∀ t ∈ Ioo 0 R, HasDerivAt F (f' t) t := by
    intro t ht
    have ht0 : 0 < t := ht.1
    have htc : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht0.ne'
    have hs : (t : ℂ) ∈ slitPlane := ofReal_mem_slitPlane.mpr ht0
    have hφ := (struveH_weighted_deriv_27 (ν + 1) hs).comp_ofReal
    simp only [one_mul, add_sub_cancel_right] at hφ
    have hψ : HasDerivAt (fun x : ℝ => (x : ℂ) ^ (μ - 2 * ν - 2))
        ((μ - 2 * ν - 2) * (t : ℂ) ^ (μ - 2 * ν - 2 - 1)) t := by
      have h := ((hasDerivAt_id (t : ℂ)).cpow_const (c := μ - 2 * ν - 2) hs).comp_ofReal
      simpa using h
    have hprod := hψ.mul hφ
    have hev : (fun x : ℝ => (x : ℂ) ^ (μ - 2 * ν - 2) * ((x : ℂ) ^ (ν + 1) * struveH (ν + 1) x))
        =ᶠ[𝓝 t] F := by
      filter_upwards [Ioi_mem_nhds ht0] with x hx
      have hxc : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt hx)
      rw [hF x hx, ← mul_assoc, ← cpow_add _ _ hxc]
      ring_nf
    refine (hprod.congr_of_eventuallyEq hev.symm).congr_deriv ?_
    simp only [f']
    have e1 : (t : ℂ) ^ (μ - 2 * ν - 2 - 1) * ((t : ℂ) ^ (ν + 1) * struveH (ν + 1) t) =
        (t : ℂ) ^ (μ - (ν + 1) - 1) * struveH (ν + 1) t := by
      rw [← mul_assoc, ← cpow_add _ _ htc]; ring_nf
    have e2 : (t : ℂ) ^ (μ - 2 * ν - 2) * ((t : ℂ) ^ (ν + 1) * struveH ν t) =
        (t : ℂ) ^ (μ - ν - 1) * struveH ν t := by
      rw [← mul_assoc, ← cpow_add _ _ htc]; ring_nf
    linear_combination (μ - 2 * ν - 2) * e1 + e2
  have hint1 := struveMel_intervalIntegrable_struveH hμ0 ν hR.le
  have hint2 := struveMel_intervalIntegrable_struveH hμ0 (ν + 1) hR.le
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hR.le hFc hderiv
    (hint1.add (hint2.const_mul _))
  rw [hF0, sub_zero, hF R hR] at hftc
  simp only [f'] at hftc
  rw [intervalIntegral.integral_add hint1 (hint2.const_mul _),
    intervalIntegral.integral_const_mul] at hftc
  linear_combination hftc

/-- The value of the Struve Mellin transform, DLMF 11.7.10–11.7.11 (removable case `μ = 0`). -/
noncomputable def struveMel_value (μ ν : ℂ) : ℂ :=
  if μ = 0 then π / (2 ^ (ν + 1) * Gamma (ν + 1))
  else Gamma (μ / 2) * 2 ^ (μ - ν - 1) * sin (π * μ / 2) / (cos (π * μ / 2) * Gamma (ν - μ / 2 + 1))

/-- The recurrence `V(μ, ν) = 2 (ν + 1 - μ/2) V(μ, ν + 1)`, valid for all parameters. -/
theorem struveMel_value_succ (μ ν : ℂ) :
    struveMel_value μ ν = -(μ - 2 * ν - 2) * struveMel_value μ (ν + 1) := by
  have h2 : ∀ w : ℂ, (2 : ℂ) ^ (w + 1) = 2 * 2 ^ w := fun w => by
    rw [cpow_add _ _ two_ne_zero, cpow_one]; ring
  unfold struveMel_value
  split_ifs with hμ
  · have h := struveMel_div_Gamma_add_one (ν + 1)
    rw [show ν + 1 + 1 = (ν + 1) + 1 by ring, h2 (ν + 1)]
    rw [show -(μ - 2 * ν - 2) = 2 * (ν + 1) by rw [hμ]; ring]
    calc π / (2 ^ (ν + 1) * Gamma (ν + 1)) = π / 2 ^ (ν + 1) * (Gamma (ν + 1))⁻¹ := by
          rw [div_mul_eq_div_div, div_eq_mul_inv]
      _ = π / 2 ^ (ν + 1) * ((ν + 1) / Gamma (ν + 1 + 1)) := by rw [h]
      _ = _ := by
          have h0 : (2 : ℂ) ^ (ν + 1) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl two_ne_zero)
          field_simp
  · have h := struveMel_div_Gamma_add_one (ν - μ / 2 + 1)
    rw [show ν + 1 - μ / 2 + 1 = (ν - μ / 2 + 1) + 1 by ring,
      show μ - ν - 1 = (μ - (ν + 1) - 1) + 1 by ring, h2 (μ - (ν + 1) - 1),
      show -(μ - 2 * ν - 2) = 2 * (ν - μ / 2 + 1) by ring]
    calc Gamma (μ / 2) * (2 * 2 ^ (μ - (ν + 1) - 1)) * sin (π * μ / 2) /
          (cos (π * μ / 2) * Gamma (ν - μ / 2 + 1)) =
        Gamma (μ / 2) * (2 * 2 ^ (μ - (ν + 1) - 1)) * sin (π * μ / 2) / cos (π * μ / 2) *
          (Gamma (ν - μ / 2 + 1))⁻¹ := by
          rw [div_mul_eq_div_div, div_eq_mul_inv]
      _ = Gamma (μ / 2) * (2 * 2 ^ (μ - (ν + 1) - 1)) * sin (π * μ / 2) / cos (π * μ / 2) *
          ((ν - μ / 2 + 1) / Gamma (ν - μ / 2 + 1 + 1)) := by rw [h]
      _ = _ := by
          rw [mul_div_assoc', div_mul_eq_div_div]
          ring

/-- **The Struve Mellin transform** as an improper integral: for `|re μ| < 1` and
`re μ - 3/2 < re ν`, `∫₀^R t^{μ-ν-1} H_ν(t) dt → V(μ, ν)`. -/
theorem struveMel_tendsto {μ ν : ℂ} (hμ0 : -1 < μ.re) (hμ1 : μ.re < 1)
    (hν : μ.re - 3 / 2 < ν.re) :
    Tendsto (fun R : ℝ => ∫ t in (0 : ℝ)..R, (t : ℂ) ^ (μ - ν - 1) * struveH ν t) atTop
      (𝓝 (struveMel_value μ ν)) := by
  suffices h : ∀ n : ℕ, ∀ ν : ℂ, -1 / 2 < ν.re + n → μ.re - 3 / 2 < ν.re →
      Tendsto (fun R : ℝ => ∫ t in (0 : ℝ)..R, (t : ℂ) ^ (μ - ν - 1) * struveH ν t) atTop
        (𝓝 (struveMel_value μ ν)) from h 2 ν (by push_cast; linarith) hν
  intro n
  induction n with
  | zero =>
    intro ν hν1 _
    simp only [Nat.cast_zero, add_zero] at hν1
    have h := struveMel_tendsto_direct hμ0 hμ1 hν1
    rwa [struveMel_value_eq hμ0 hμ1 hν1] at h
  | succ n ih =>
    intro ν hν1 hν2
    by_cases hd : -1 / 2 < ν.re
    · have h := struveMel_tendsto_direct hμ0 hμ1 hd
      rwa [struveMel_value_eq hμ0 hμ1 hd] at h
    push Not at hd
    have hnext := ih (ν + 1) (by simp; push_cast at hν1; linarith) (by simp; linarith)
    have hb := struveMel_tendsto_boundary (μ := μ) (ν := ν + 1) (by simp; linarith) hμ1
      (by simp; linarith)
    rw [struveMel_value_succ μ ν]
    have hlim := hb.sub (hnext.const_mul (μ - 2 * ν - 2))
    rw [zero_sub, ← neg_mul] at hlim
    refine hlim.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with R hR
    rw [struveMel_integral_by_parts hμ0 ν hR]

/-- Horizontal-ray integral representation: `HasIntegralAtTop (fun t : ℝ => struveH ν t) 0 (-cos
(π*ν/2)/sin (π*ν/2))`. -/
@[dlmf 11.7.E9]
theorem struveH_integral_plain {ν : ℂ} (h0 : -2 < ν.re) (h1 : ν.re < 0) :
    HasIntegralAtTop (fun t : ℝ => struveH ν t) 0 (-cos (π*ν/2)/sin (π*ν/2)) := by
  have h := struveMel_tendsto (μ := ν + 1) (ν := ν) (by simp; linarith) (by simp; linarith)
    (by simp; linarith)
  have he : ∀ t : ℝ, (t : ℂ) ^ (ν + 1 - ν - 1) * struveH ν t = struveH ν t := fun t => by
    rw [show ν + 1 - ν - 1 = 0 by ring, cpow_zero, one_mul]
  simp only [he] at h
  unfold HasIntegralAtTop
  convert h using 2
  unfold struveMel_value
  have hs : sin (π * (ν + 1) / 2) = cos (π * ν / 2) := by
    rw [show (π : ℂ) * (ν + 1) / 2 = π * ν / 2 + π / 2 by ring, Complex.sin_add_pi_div_two]
  have hc : cos (π * (ν + 1) / 2) = -sin (π * ν / 2) := by
    rw [show (π : ℂ) * (ν + 1) / 2 = π * ν / 2 + π / 2 by ring, Complex.cos_add_pi_div_two]
  split_ifs with hν1
  · have hν' : ν = -1 := by linear_combination hν1
    subst hν'
    rw [show (-1 : ℂ) + 1 = 0 by ring, Complex.Gamma_zero]
    have h1 : sin (π * (-1 : ℂ) / 2) = -1 := by
      rw [show (π : ℂ) * (-1) / 2 = -(π / 2) by ring, Complex.sin_neg, Complex.sin_pi_div_two]
    have h2 : cos (π * (-1 : ℂ) / 2) = 0 := by
      rw [show (π : ℂ) * (-1) / 2 = -(π / 2) by ring, Complex.cos_neg, Complex.cos_pi_div_two]
    rw [h1, h2]; simp
  · rw [hs, hc, show ν + 1 - ν - 1 = 0 by ring, cpow_zero, mul_one,
      show ν - (ν + 1) / 2 + 1 = (ν + 1) / 2 by ring]
    have hG : Gamma ((ν + 1) / 2) ≠ 0 := by
      refine Complex.Gamma_ne_zero fun m hm => ?_
      have hre := congrArg Complex.re hm
      simp at hre
      rcases m with _ | m
      · exact hν1 (by simpa using hm)
      · push_cast at hre; linarith
    field_simp

/-- Horizontal-ray integral representation: `HasIntegralAtTop (fun t : ℝ => (t:ℂ)^(-ν-1)*struveH ν
t) 0 (π/(2^(ν+1)*Gamma (ν+1)))`. -/
@[dlmf 11.7.E10]
theorem struveH_integral_mellin_zero {ν : ℂ} (hν : -3/2 < ν.re) :
    HasIntegralAtTop (fun t : ℝ => (t:ℂ)^(-ν-1)*struveH ν t) 0 (π/(2^(ν+1)*Gamma (ν+1))) := by
  have h := struveMel_tendsto (μ := 0) (ν := ν) (by norm_num) (by norm_num) (by simp; linarith)
  simp only [struveMel_value, zero_sub] at h
  exact h

/-- Horizontal-ray integral representation: `HasIntegralAtTop (fun t : ℝ => (t:ℂ)^(μ-ν-1)*struveH
ν t) 0 (if μ=0 then π/(2^(ν+1)*Gamma (ν+1)) else Gamma (μ/2)*2^(μ-ν-1)*sin (π*μ/2)/(cos
(π*μ/2)*Gamma (ν-μ/2+1)))`. -/
@[dlmf 11.7.E11]
theorem struveH_integral_mellin {μ ν : ℂ} (hμ : |μ.re| < 1) (hν : μ.re-3/2 < ν.re) :
    HasIntegralAtTop (fun t : ℝ => (t:ℂ)^(μ-ν-1)*struveH ν t) 0 (if μ=0 then π/(2^(ν+1)*Gamma (ν+1)) else Gamma (μ/2)*2^(μ-ν-1)*sin (π*μ/2)/(cos (π*μ/2)*Gamma (ν-μ/2+1))) := by
  obtain ⟨h0, h1⟩ := abs_lt.mp hμ
  exact struveMel_tendsto h0 h1 hν

/-- struveH integral product. DLMF 11.7.12 states only `Re(μ+ν) > 0`; the integral then
diverges, e.g. at `μ = 3`, `ν = -2` the integrand grows like `t^(1/2) cos(...)`. The cross terms
`t^(-ν-3/2)` and `t^(-μ-3/2)` of the large-`t` expansion require `Re μ, Re ν > -3/2`
(hypotheses added 2026-10-20). -/
@[dlmf 11.7.E12]
theorem struveH_integral_product {μ ν : ℂ} (h : 0 < (μ+ν).re) (hμ : -3/2 < μ.re)
    (hν : -3/2 < ν.re) :
    HasIntegralAtTop (fun t : ℝ => (t:ℂ)^(-μ-ν)*struveH μ t*struveH ν t) 0 (Real.sqrt π*Gamma (μ+ν)/(2^(μ+ν)*Gamma (μ+ν+1/2)*Gamma (μ+1/2)*Gamma (ν+1/2))) := by
  sorry

/-- Fubini for the Laplace transform of a Poisson-weighted integral. -/
theorem laplace_poissonWeight {a : ℂ} {β : ℝ} (hβ : β < a.re) {k : ℝ → ℝ → ℂ}
    (hk : Continuous (Function.uncurry k))
    (hkb : ∀ t s : ℝ, 0 < t → s ∈ Ioc (0:ℝ) 1 → ‖k t s‖ ≤ Real.exp (β*t)) :
    IntegrableOn (fun t : ℝ => exp (-a*t) * ∫ s : ℝ in 0..1, (1-(s:ℂ)^2)^(-1/2:ℂ) * k t s)
      (Ioi 0) ∧
    (∫ t : ℝ in Ioi 0, exp (-a*t) * ∫ s : ℝ in 0..1, (1-(s:ℂ)^2)^(-1/2:ℂ) * k t s) =
      ∫ s : ℝ in 0..1, (1-(s:ℂ)^2)^(-1/2:ℂ) * ∫ t : ℝ in Ioi 0, exp (-a*t) * k t s := by
  set w : ℝ → ℂ := fun s => (1-(s:ℂ)^2)^(-1/2:ℂ)
  have hw : IntegrableOn w (Ioc 0 1) := by
    have := intervalIntegrable_poissonWeight (ν := 0) (by norm_num)
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at this
    convert this using 3; norm_num
  set F : ℝ × ℝ → ℂ := fun p => exp (-a*p.1) * (w p.2 * k p.1 p.2)
  have hwm : Measurable w := by
    simp only [w]; fun_prop
  have hFm : AEStronglyMeasurable F ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioc (0:ℝ) 1))) := by
    apply Measurable.aestronglyMeasurable
    simp only [F]
    have hk' : Measurable (fun p : ℝ × ℝ => k p.1 p.2) := hk.measurable
    have : Measurable (fun p : ℝ × ℝ => w p.2) := hwm.comp measurable_snd
    fun_prop
  have hG : Integrable (fun p : ℝ × ℝ => Real.exp ((β - a.re)*p.1) * ‖w p.2‖)
      ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioc (0:ℝ) 1))) :=
    (integrableOn_exp_mul_Ioi (by linarith) 0).mul_prod hw.norm
  have hF : Integrable F ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioc (0:ℝ) 1))) := by
    refine hG.mono' hFm ?_
    rw [Measure.prod_restrict]
    filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioc)] with p hp
    obtain ⟨ht, hs⟩ := hp
    simp only [F, norm_mul, Complex.norm_exp]
    have h1 := hkb p.1 p.2 ht hs
    have : (-a*(p.1:ℂ)).re = -a.re*p.1 := by simp
    rw [this]
    calc Real.exp (-a.re*p.1) * (‖w p.2‖ * ‖k p.1 p.2‖)
        ≤ Real.exp (-a.re*p.1) * (‖w p.2‖ * Real.exp (β*p.1)) := by gcongr
      _ = Real.exp ((β - a.re)*p.1) * ‖w p.2‖ := by
        rw [show (β - a.re)*p.1 = -a.re*p.1 + β*p.1 by ring, Real.exp_add]; ring
  have hswap := integral_integral_swap (f := fun t s => F (t, s)) hF
  have hint := hF.integral_prod_left
  constructor
  · refine (hint.congr (Eventually.of_forall fun t => ?_))
    simp only [F]
    rw [integral_const_mul, intervalIntegral.integral_of_le zero_le_one]
  · rw [intervalIntegral.integral_of_le zero_le_one]
    convert hswap using 1
    · refine integral_congr_ae (Eventually.of_forall fun t => ?_)
      simp only [F]
      rw [integral_const_mul, intervalIntegral.integral_of_le zero_le_one]
    · refine integral_congr_ae (Eventually.of_forall fun s => ?_)
      simp only [F]
      rw [← integral_const_mul]
      congr 1; funext t; ring

/-- `∫₀^∞ e^{-at} e^{ct} dt = 1/(a-c)` for `Re c < Re a`. -/
theorem integral_exp_neg_mul_exp_Ioi {a c : ℂ} (h : c.re < a.re) :
    IntegrableOn (fun t : ℝ => exp (-a*t) * exp (c*t)) (Ioi 0) ∧
    (∫ t : ℝ in Ioi 0, exp (-a*t) * exp (c*t)) = 1/(a-c) := by
  have he : (fun t : ℝ => exp (-a*t) * exp (c*t)) = fun t : ℝ => exp ((c-a)*t) := by
    funext t; rw [← Complex.exp_add]; ring_nf
  have hre : (c-a).re < 0 := by simp; linarith
  have hne : a - c ≠ 0 := fun h0 => by
    have := congrArg Complex.re h0; simp at this; linarith
  rw [he]
  refine ⟨integrableOn_exp_mul_complex_Ioi hre 0, ?_⟩
  rw [integral_exp_mul_complex_Ioi hre 0]
  simp only [ofReal_zero, mul_zero, Complex.exp_zero]
  have hne' : c - a ≠ 0 := fun h0 => hne (by linear_combination -h0)
  field_simp
  ring

/-- Laplace transform of `sin(st)`. -/
theorem laplace_sin_mul {a : ℂ} (ha : 0 < a.re) (s : ℝ) :
    (∫ t : ℝ in Ioi 0, exp (-a*t) * sin ((t:ℂ)*s)) = s/(a^2+s^2) := by
  have h1 := integral_exp_neg_mul_exp_Ioi (a := a) (c := I*s) (by simpa using ha)
  have h2 := integral_exp_neg_mul_exp_Ioi (a := a) (c := -I*s) (by simpa using ha)
  have hsin : ∀ t : ℝ, exp (-a*t) * sin ((t:ℂ)*s) =
      (exp (-a*t) * exp (I*s*t) - exp (-a*t) * exp (-I*s*t)) / (2*I) := by
    intro t
    have h2I : (2:ℂ)*I ≠ 0 := by simp
    rw [eq_div_iff h2I, Complex.sin]
    ring_nf; rw [I_sq]; ring_nf
  simp_rw [hsin]
  rw [integral_div, integral_sub h1.1 h2.1, h1.2, h2.2]
  have hp : a - I*s ≠ 0 := fun h0 => by
    have := congrArg Complex.re h0; simp at this; linarith
  have hm : a - -I*s ≠ 0 := fun h0 => by
    have := congrArg Complex.re h0; simp at this; linarith
  have hprod : (a - I*s)*(a - -I*s) = a^2+s^2 := by ring_nf; rw [I_sq]; ring
  have key : 1/(a - I*s) - 1/(a - -I*s) = (2*I) * (s/(a^2+s^2)) := by
    rw [div_sub_div _ _ hp hm, hprod]; ring
  rw [key, mul_div_cancel_left₀ _ (by simp : (2:ℂ)*I ≠ 0)]

/-- Laplace transform of `sinh(st)`. -/
theorem laplace_sinh_mul {a : ℂ} (ha : 1 < a.re) {s : ℝ} (hs : s ∈ Ioc (0:ℝ) 1) :
    (∫ t : ℝ in Ioi 0, exp (-a*t) * sinh ((t:ℂ)*s)) = s/(a^2-s^2) := by
  have h1 := integral_exp_neg_mul_exp_Ioi (a := a) (c := (s:ℂ)) (by simp; linarith [hs.2])
  have h2 := integral_exp_neg_mul_exp_Ioi (a := a) (c := -(s:ℂ)) (by simp; linarith [hs.1])
  have hsinh : ∀ t : ℝ, exp (-a*t) * sinh ((t:ℂ)*s) =
      (exp (-a*t) * exp (s*t) - exp (-a*t) * exp (-s*t)) / 2 := by
    intro t
    rw [Complex.sinh]
    ring_nf
  simp_rw [hsinh]
  rw [integral_div, integral_sub h1.1 h2.1, h1.2, h2.2]
  have hp : a - s ≠ 0 := fun h0 => by
    have := congrArg Complex.re h0; simp at this; linarith [hs.2]
  have hm : a - -(s:ℂ) ≠ 0 := fun h0 => by
    have := congrArg Complex.re h0; simp at this; linarith [hs.1]
  have key : 1/(a - s) - 1/(a - -(s:ℂ)) = 2 * (s/(a^2-s^2)) := by
    rw [div_sub_div _ _ hp hm, show (a - s)*(a - -(s:ℂ)) = a^2-s^2 by ring]; ring
  rw [key, mul_div_cancel_left₀ _ (by norm_num : (2:ℂ) ≠ 0)]

end DLMF.Struve
end
