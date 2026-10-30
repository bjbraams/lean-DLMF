/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Confluent.Zeros.RealZeros

/-!
# Large complex zeros of Kummer functions

Localization and enumeration of the large complex Kummer zeros, with their asymptotic
corrections.

Source references and common attribution are retained in
`DLMF.Confluent.Zeros`.
-/

@[expose] public section

open Complex Filter Set

open scoped Real Topology

open DLMF.Hypergeometric

noncomputable section

namespace DLMF.Confluent

/-! ### Large complex zeros (DLMF 13.9.9)

The zeros are located by comparing `𝐌(a,b,·)` on small circles with the exponential model
`A (exp (z - w) - 1)` (`DLMF.erfZ_exists_zero_of_expModel`, a Rouché argument), using the
one-term sector expansion `regularizedHGFun_poincare_sector` (DLMF 13.7.2). -/

section LargeZeros

open Asymptotics Metric

/-- `log (t i) = log t + (π/2) i` for `t > 0`. -/
theorem kumZ_log_ofReal_mul_I {t : ℝ} (ht : 0 < t) :
    log ((t : ℂ) * I) = Real.log t + (π / 2 : ℝ) * I := by
  apply Complex.ext
  · simp [log_re, abs_of_pos ht]
  · rw [log_im, arg_real_mul I ht, arg_I]; simp

/-- `log` is `2/t`-Lipschitz on the disc of radius `t/2` about `t i`. -/
theorem kumZ_norm_log_sub_le {t : ℝ} (ht : 0 < t) {z : ℂ} (hz : ‖z - t * I‖ ≤ t / 2) :
    ‖log z - log ((t : ℂ) * I)‖ ≤ 2 / t * ‖z - t * I‖ := by
  have hmem : ∀ u ∈ closedBall ((t : ℂ) * I) (t / 2), t / 2 ≤ u.im := by
    intro u hu
    rw [mem_closedBall, dist_eq_norm] at hu
    have h1 := abs_im_le_norm (u - t * I)
    simp only [sub_im, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero,
      add_zero] at h1
    rw [abs_le] at h1
    linarith
  refine (convex_closedBall ((t : ℂ) * I) (t / 2)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := log) (f' := fun u => u⁻¹) (fun u hu => ?_) (fun u hu => ?_)
    (mem_closedBall_self (by linarith)) (by rwa [mem_closedBall, dist_eq_norm])
  · have him := hmem u hu
    exact (hasDerivAt_log (mem_slitPlane_iff.mpr (Or.inr (by linarith)))).hasDerivWithinAt
  · have him := hmem u hu
    have hn : t / 2 ≤ ‖u‖ := him.trans ((le_abs_self _).trans (abs_im_le_norm u))
    rw [norm_inv]
    calc ‖u‖⁻¹ ≤ (t / 2)⁻¹ := inv_anti₀ (by positivity) hn
      _ = 2 / t := by field_simp

/-- Factorization `z^s = u^s exp(s (log z - log u))`. -/
theorem kumZ_cpow_eq {u z : ℂ} (hu : u ≠ 0) (hz : z ≠ 0) (s : ℂ) :
    z ^ s = u ^ s * exp (s * (log z - log u)) := by
  rw [cpow_def_of_ne_zero hz, cpow_def_of_ne_zero hu, ← Complex.exp_add]
  ring_nf

/-- Explicit form of the sector Poincaré bound for `𝐌` (DLMF 13.7.2, one term). -/
theorem kumZ_sector_bound (a b : ℂ) (ha : ∀ k : ℕ, a ≠ -k) (hba : ∀ k : ℕ, b - a ≠ -k) :
    ∃ K₁ > 0, ∃ R : ℝ, ∀ z : ℂ, R ≤ ‖z‖ → π / 4 ≤ z.arg → z.arg ≤ π - π / 4 →
      ‖regularizedHGFun {a} {b} z -
        (exp z * z ^ (a - b) / Gamma a + exp (π * I * a) * z ^ (-a) / Gamma (b - a))‖ ≤
        K₁ * (‖exp z * z ^ (a - b - 1)‖ + ‖z ^ (-a - 1)‖) := by
  have h := regularizedHGFun_poincare_sector a b 1 (δ := π / 4) (by positivity)
    (by linarith [Real.pi_pos]) ha hba
  obtain ⟨K₁, hK₁, hb⟩ := h.exists_pos
  rw [IsBigOWith, eventually_inf_principal, eventually_comap, eventually_atTop] at hb
  obtain ⟨R, hR⟩ := hb
  refine ⟨K₁, hK₁, R, fun z hzR h1 h2 => ?_⟩
  have := hR ‖z‖ hzR z rfl ⟨h1, h2⟩
  simpa [DLMF.Hypergeometric.poch_zero, abs_of_nonneg (add_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (norm_nonneg _))] using this

/-- `‖exp ζ‖ ≤ 3` for `‖ζ‖ ≤ 1`. -/
theorem kumZ_norm_exp_le_three {ζ : ℂ} (h : ‖ζ‖ ≤ 1) : ‖exp ζ‖ ≤ 3 := by
  rw [Complex.norm_exp]
  have := Real.exp_one_lt_d9
  have h1 : ζ.re ≤ 1 := (re_le_norm ζ).trans h
  calc Real.exp ζ.re ≤ Real.exp 1 := Real.exp_le_exp.mpr h1
    _ ≤ 3 := by linarith

/-- Core localization for the large zeros of `M(a,b,·)` in the upper half-plane: every exact
solution `w` of the model equation `exp w = -(e^{πia} Γ(a)/Γ(b-a)) (t i)^{b-2a}` with
`‖w - t i‖ ≤ K log t` has a zero of `M(a,b,·)` within `C log t / t`, for all large `t`. -/
theorem kumZ_core (a b : ℂ) (hb : ∀ k : ℕ, b ≠ -k) (ha : ∀ k : ℕ, a ≠ -k)
    (hba : ∀ k : ℕ, b - a ≠ -k) (K : ℝ) :
    ∃ C : ℝ, ∀ᶠ t : ℝ in atTop, ∀ w : ℂ,
      exp w = -(exp (π * I * a) * Gamma a / Gamma (b - a)) * ((t : ℂ) * I) ^ (b - 2 * a) →
      ‖w - t * I‖ ≤ K * Real.log t →
      ∃ z, ‖z - w‖ ≤ C * Real.log t / t ∧ kummerM a b z = 0 := by
  obtain ⟨K₁, hK₁, R, hR⟩ := kumZ_sector_bound a b ha hba
  have hGa : Gamma a ≠ 0 := Gamma_ne_zero ha
  have hGba : Gamma (b - a) ≠ 0 := Gamma_ne_zero hba
  have hGb : Gamma b ≠ 0 := Gamma_ne_zero hb
  have he : exp (π * I * a) ≠ 0 := Complex.exp_ne_zero _
  set E : ℝ := 2 * ‖a‖ + 6 * ‖a - b‖ with hE
  set D : ℝ := K₁ * (9 * ‖Gamma a‖ + 3 * ‖Gamma (b - a)‖ / ‖exp (π * I * a)‖) * 2 with hD
  have hE0 : 0 ≤ E := by positivity
  have hD0 : 0 ≤ D := by positivity
  set C : ℝ := 4 * (E * 2 * (1 + |K|) + D + 1) with hC
  have hC0 : 4 ≤ C := by
    have : 0 ≤ E * 2 * (1 + |K|) := by positivity
    linarith
  set M₀ : ℝ := ‖a‖ + ‖a - b‖ + 1 with hM₀
  have hM₀1 : 1 ≤ M₀ := by have := norm_nonneg a; have := norm_nonneg (a - b); linarith
  set θ : ℝ := 1 / (2 * C + 4 * (1 + |K|) * M₀ + 4) with hθ
  have hden : 0 < 2 * C + 4 * (1 + |K|) * M₀ + 4 := by positivity
  have hθ0 : 0 < θ := by positivity
  have hCθ : C * θ ≤ 1 / 2 := by
    rw [hθ, mul_one_div, div_le_iff₀ hden]
    have hX : 0 ≤ (1 + |K|) * M₀ := by positivity
    linarith only [hX]
  have hKθ : 2 * (1 + |K|) * θ * M₀ ≤ 1 / 2 := by
    rw [hθ]
    rw [show 2 * (1 + |K|) * (1 / (2 * C + 4 * (1 + |K|) * M₀ + 4)) * M₀ =
      (2 * (1 + |K|) * M₀) / (2 * C + 4 * (1 + |K|) * M₀ + 4) by ring, div_le_iff₀ hden]
    linarith only [hC0]
  refine ⟨C, ?_⟩
  have hlog : ∀ᶠ t : ℝ in atTop, ‖Real.log t‖ ≤ θ * ‖t‖ := Real.isLittleO_log_id_atTop.bound hθ0
  filter_upwards [hlog, eventually_ge_atTop (max (2 * |R|) (Real.exp 1))] with t hθt htT
  intro w hw hwK
  have htexp : Real.exp 1 ≤ t := le_of_max_le_right htT
  have ht0 : 0 < t := lt_of_lt_of_le (Real.exp_pos 1) htexp
  have htR : 2 * |R| ≤ t := le_of_max_le_left htT
  have hlt1 : 1 ≤ Real.log t := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) htexp
  rw [Real.norm_of_nonneg (by linarith), Real.norm_of_nonneg ht0.le] at hθt
  set lam : ℝ := Real.log t / t with hlam
  have hlamθ : lam ≤ θ := by rw [hlam, div_le_iff₀ ht0]; exact hθt
  have hlampos : 0 < lam := by positivity
  have hinvlam : 1 / t ≤ lam := by rw [hlam]; gcongr
  set ρ : ℝ := C * Real.log t / t with hρ
  have hρlam : ρ = C * lam := by rw [hρ, hlam]; ring
  have hρpos : 0 < ρ := by rw [hρlam]; positivity
  have hρ2 : ρ ≤ 1 / 2 := by
    rw [hρlam]; nlinarith only [hlamθ, hCθ, hC0]
  set u : ℂ := (t : ℂ) * I with hu
  have hu0 : u ≠ 0 := mul_ne_zero (ofReal_ne_zero.mpr ht0.ne') I_ne_zero
  set B : ℂ := exp (π * I * a) * u ^ (-a) / Gamma (b - a) with hB
  have hB0 : B ≠ 0 := by
    rw [hB]
    refine div_ne_zero (mul_ne_zero he ?_) hGba
    rw [cpow_def_of_ne_zero hu0]; exact Complex.exp_ne_zero _
  have hBn : 0 < ‖B‖ := norm_pos_iff.mpr hB0
  have hanM : AnalyticOnNhd ℂ (fun z => kummerM a b z / Gamma b) (closedBall w ρ) :=
    fun z _ => ((hasFPowerSeriesOnBall_kummerM (a := a) hb).analyticAt_of_mem
      (by simp)).div_const
  suffices hmain : ∀ z ∈ sphere w ρ,
      ‖kummerM a b z / Gamma b - -B * (exp (z - w) - 1)‖ < ‖-B‖ * ρ / 2 by
    obtain ⟨z, hz, hz0⟩ :=
      DLMF.erfZ_exists_zero_of_expModel hρpos hρ2 (neg_ne_zero.mpr hB0) hanM hmain
    refine ⟨z, (mem_ball_iff_norm.mp hz).le, ?_⟩
    simpa [hGb] using hz0
  intro z hz
  -- the main estimate on the circle
  have hzw : ‖z - w‖ = ρ := mem_sphere_iff_norm.mp hz
  have hzu : ‖z - u‖ ≤ (1 + |K|) * Real.log t := by
    have h1 : ‖z - u‖ ≤ ‖z - w‖ + ‖w - u‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    have h2 : K * Real.log t ≤ |K| * Real.log t :=
      mul_le_mul_of_nonneg_right (le_abs_self K) (by linarith)
    rw [hzw] at h1
    have h3 : (1 + |K|) * Real.log t = Real.log t + |K| * Real.log t := by ring
    linarith only [h1, h2, hwK, hρ2, hlt1, h3]
  have hzu2 : ‖z - u‖ ≤ t / 2 := by
    have : (1 + |K|) * Real.log t ≤ (1 + |K|) * (θ * t) :=
      mul_le_mul_of_nonneg_left hθt (by positivity)
    have h3 : (1 + |K|) * θ ≤ 1 / 4 := by nlinarith only [hKθ, hM₀1, abs_nonneg K, hθ0]
    nlinarith only [this, h3, hzu, ht0]
  set ε : ℂ := log z - log u with hε
  have hεb : ‖ε‖ ≤ 2 * (1 + |K|) * lam := by
    have := kumZ_norm_log_sub_le ht0 hzu2
    calc ‖ε‖ ≤ 2 / t * ‖z - u‖ := this
      _ ≤ 2 / t * ((1 + |K|) * Real.log t) := by gcongr
      _ = 2 * (1 + |K|) * lam := by rw [hlam]; ring
  set η : ℝ := 2 * (1 + |K|) * lam with hη
  have hη0 : 0 ≤ η := by positivity
  have hηM : η * M₀ ≤ 1 / 2 := by
    have : η ≤ 2 * (1 + |K|) * θ := by rw [hη]; gcongr
    nlinarith only [this, hKθ, hM₀1, hη0]
  have hεa : ‖-a * ε‖ ≤ ‖a‖ * η := by
    rw [norm_mul, norm_neg]; gcongr
  have hεab : ‖(a - b) * ε‖ ≤ ‖a - b‖ * η := by
    rw [norm_mul]; gcongr
  have haη : ‖a‖ * η ≤ 1 / 2 := by nlinarith only [hηM, hη0, norm_nonneg a, norm_nonneg (a - b), hM₀]
  have habη : ‖a - b‖ * η ≤ 1 / 2 := by nlinarith only [hηM, hη0, norm_nonneg a, norm_nonneg (a - b), hM₀]
  -- `z` lies in the sector and is large
  have hzim : t / 2 ≤ z.im := by
    have h1 := abs_im_le_norm (z - u)
    simp only [hu, sub_im, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero,
      add_zero] at h1
    rw [abs_le] at h1
    linarith only [h1.1, hzu2]
  have hzn : t / 2 ≤ ‖z‖ := hzim.trans ((le_abs_self _).trans (abs_im_le_norm z))
  have hz0' : z ≠ 0 := by
    intro h; rw [h, norm_zero] at hzn; linarith only [hzn, ht0]
  have harg : |z.arg - π / 2| ≤ 1 / 2 := by
    have h1 : ε.im = z.arg - π / 2 := by
      rw [hε, sub_im, log_im, hu, kumZ_log_ofReal_mul_I ht0]; simp
    rw [← h1]
    refine (abs_im_le_norm ε).trans (hεb.trans ?_)
    nlinarith only [hηM, hM₀1, hη0]
  have hpi := Real.two_le_pi
  have hbound := hR z (by linarith only [le_abs_self R, hzn, htR]) (by rw [abs_le] at harg; linarith only [harg.1, hpi])
    (by rw [abs_le] at harg; linarith only [harg.2, hpi])
  -- algebraic identities
  have hz1 : z ^ (a - b) = u ^ (a - b) * exp ((a - b) * ε) := kumZ_cpow_eq hu0 hz0' _
  have hz2 : z ^ (-a) = u ^ (-a) * exp (-a * ε) := kumZ_cpow_eq hu0 hz0' _
  have hz3 : z ^ (a - b - 1) = z ^ (a - b) / z := by rw [cpow_sub _ _ hz0', cpow_one]
  have hz4 : z ^ (-a - 1) = z ^ (-a) / z := by rw [cpow_sub _ _ hz0', cpow_one]
  have hu' : u ^ (a - b) * u ^ (b - 2 * a) = u ^ (-a) := by
    rw [← cpow_add _ _ hu0]; ring_nf
  have hexpz : exp z = exp (z - w) * exp w := by rw [← Complex.exp_add]; ring_nf
  have hP1 : exp z * z ^ (a - b) / Gamma a = -(B * exp (z - w) * exp ((a - b) * ε)) := by
    rw [hexpz, hw, hz1, hB, ← hu']
    field_simp
  have hP2 : exp (π * I * a) * z ^ (-a) / Gamma (b - a) = B * exp (-a * ε) := by
    rw [hz2, hB]; ring
  have hMeq : kummerM a b z / Gamma b = regularizedHGFun {a} {b} z := by
    rw [kummerM_eq_mul_regularizedHGFun hb]; field_simp
  have hsplit : kummerM a b z / Gamma b - -B * (exp (z - w) - 1) =
      (regularizedHGFun {a} {b} z -
        (exp z * z ^ (a - b) / Gamma a + exp (π * I * a) * z ^ (-a) / Gamma (b - a))) +
      B * ((exp (-a * ε) - 1) - exp (z - w) * (exp ((a - b) * ε) - 1)) := by
    rw [hMeq, hP1, hP2]; ring
  -- bound the model discrepancy
  have hzw1 : ‖z - w‖ ≤ 1 := by rw [hzw]; linarith only [hρ2]
  have hexp3 := kumZ_norm_exp_le_three hzw1
  have hea := norm_exp_sub_one_le (x := -a * ε) (by linarith only [hεa, haη])
  have heab := norm_exp_sub_one_le (x := (a - b) * ε) (by linarith only [hεab, habη])
  have hexpab3 := kumZ_norm_exp_le_three (ζ := (a - b) * ε) (by linarith only [hεab, habη])
  have hexpa3 := kumZ_norm_exp_le_three (ζ := -a * ε) (by linarith only [hεa, haη])
  have hmodel : ‖B * ((exp (-a * ε) - 1) - exp (z - w) * (exp ((a - b) * ε) - 1))‖ ≤
      ‖B‖ * (E * η) := by
    rw [norm_mul]
    gcongr
    calc ‖(exp (-a * ε) - 1) - exp (z - w) * (exp ((a - b) * ε) - 1)‖
        ≤ ‖exp (-a * ε) - 1‖ + ‖exp (z - w)‖ * ‖exp ((a - b) * ε) - 1‖ := by
          rw [← norm_mul]; exact norm_sub_le _ _
      _ ≤ 2 * (‖a‖ * η) + 3 * (2 * (‖a - b‖ * η)) := by
          gcongr
          · exact hea.trans (by gcongr)
          · exact heab.trans (by gcongr)
      _ = E * η := by rw [hE]; ring
  have hasym : K₁ * (‖exp z * z ^ (a - b - 1)‖ + ‖z ^ (-a - 1)‖) ≤ ‖B‖ * (D / t) := by
    have h1 : exp z * z ^ (a - b - 1) = Gamma a * (exp z * z ^ (a - b) / Gamma a) / z := by
      rw [hz3]; field_simp
    have h2 : z ^ (-a - 1) = (B * Gamma (b - a) / exp (π * I * a)) * exp (-a * ε) / z := by
      rw [hz4, hz2, hB]; field_simp
    have hzinv : 1 / ‖z‖ ≤ 2 / t := by
      rw [div_le_div_iff₀ (by positivity) ht0]; linarith only [hzn]
    have hb1 : ‖exp z * z ^ (a - b - 1)‖ ≤ ‖Gamma a‖ * ‖B‖ * 9 * (2 / t) := by
      rw [h1, hP1, norm_div, norm_mul, norm_neg, norm_mul, norm_mul]
      calc ‖Gamma a‖ * (‖B‖ * ‖exp (z - w)‖ * ‖exp ((a - b) * ε)‖) / ‖z‖
          = ‖Gamma a‖ * (‖B‖ * ‖exp (z - w)‖ * ‖exp ((a - b) * ε)‖) * (1 / ‖z‖) := by ring
        _ ≤ ‖Gamma a‖ * (‖B‖ * 3 * 3) * (2 / t) := by gcongr
        _ = ‖Gamma a‖ * ‖B‖ * 9 * (2 / t) := by ring
    have hb2 : ‖z ^ (-a - 1)‖ ≤ ‖B‖ * ‖Gamma (b - a)‖ / ‖exp (π * I * a)‖ * 3 * (2 / t) := by
      rw [h2, norm_div, norm_mul, norm_div, norm_mul]
      calc ‖B‖ * ‖Gamma (b - a)‖ / ‖exp (π * I * a)‖ * ‖exp (-a * ε)‖ / ‖z‖
          = ‖B‖ * ‖Gamma (b - a)‖ / ‖exp (π * I * a)‖ * ‖exp (-a * ε)‖ * (1 / ‖z‖) := by ring
        _ ≤ ‖B‖ * ‖Gamma (b - a)‖ / ‖exp (π * I * a)‖ * 3 * (2 / t) := by gcongr
    calc K₁ * (‖exp z * z ^ (a - b - 1)‖ + ‖z ^ (-a - 1)‖)
        ≤ K₁ * (‖Gamma a‖ * ‖B‖ * 9 * (2 / t) +
            ‖B‖ * ‖Gamma (b - a)‖ / ‖exp (π * I * a)‖ * 3 * (2 / t)) := by gcongr
      _ = ‖B‖ * (D / t) := by rw [hD]; ring
  rw [norm_neg, hsplit]
  calc ‖(regularizedHGFun {a} {b} z -
        (exp z * z ^ (a - b) / Gamma a + exp (π * I * a) * z ^ (-a) / Gamma (b - a))) +
      B * ((exp (-a * ε) - 1) - exp (z - w) * (exp ((a - b) * ε) - 1))‖
      ≤ ‖B‖ * (D / t) + ‖B‖ * (E * η) :=
        (norm_add_le _ _).trans (add_le_add (hbound.trans hasym) hmodel)
    _ ≤ ‖B‖ * ((D + E * 2 * (1 + |K|)) * lam) := by
        rw [← mul_add]
        gcongr
        have : D / t ≤ D * lam := by
          rw [div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_left hinvlam hD0
        rw [hη]; linarith only [this]
    _ < ‖B‖ * ρ / 2 := by
        rw [hρlam, mul_div_assoc]
        gcongr
        rw [hC]; have hXl : 0 ≤ (D + E * 2 * (1 + |K|)) * lam := by positivity
        linarith only [hXl, hlampos]

/-- `‖log Y‖ ≤ |log ‖Y‖| + π`. -/
theorem kumZ_norm_log_le (Y : ℂ) : ‖log Y‖ ≤ |Real.log ‖Y‖| + π := by
  refine (norm_le_abs_re_add_abs_im _).trans ?_
  rw [log_re, log_im]
  gcongr
  exact abs_arg_le_pi Y

/-- The distance of the model zero from the ray point grows at most logarithmically. -/
theorem kumZ_dist_bound (G v c α : ℂ) (hG : G ≠ 0) (hv : v ≠ 0) :
    ∃ K : ℝ, ∀ t : ℝ, Real.exp 1 ≤ t → ‖α + log (G * ((t : ℂ) * v) ^ c)‖ ≤ K * Real.log t := by
  refine ⟨‖α‖ + |Real.log ‖G‖| + |c.re| + |c.re| * |Real.log ‖v‖| + |arg v * c.im| + π,
    fun t ht => ?_⟩
  have ht0 : 0 < t := lt_of_lt_of_le (Real.exp_pos 1) ht
  have hlt1 : 1 ≤ Real.log t := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) ht
  have htv : (t : ℂ) * v ≠ 0 := mul_ne_zero (ofReal_ne_zero.mpr ht0.ne') hv
  have hnorm : ‖G * ((t : ℂ) * v) ^ c‖ =
      ‖G‖ * ((t * ‖v‖) ^ c.re / Real.exp (arg v * c.im)) := by
    rw [norm_mul, norm_cpow_of_ne_zero htv, arg_real_mul v ht0, norm_mul, norm_real,
      Real.norm_of_nonneg ht0.le]
  have hGn : 0 < ‖G‖ := norm_pos_iff.mpr hG
  have hvn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hlog : Real.log ‖G * ((t : ℂ) * v) ^ c‖ =
      Real.log ‖G‖ + c.re * (Real.log t + Real.log ‖v‖) - arg v * c.im := by
    rw [hnorm, Real.log_mul hGn.ne' (by positivity), Real.log_div (by positivity)
      (Real.exp_pos _).ne', Real.log_rpow (by positivity), Real.log_exp,
      Real.log_mul ht0.ne' hvn.ne']
    ring
  have h1 := kumZ_norm_log_le (G * ((t : ℂ) * v) ^ c)
  rw [hlog] at h1
  have h2 : |Real.log ‖G‖ + c.re * (Real.log t + Real.log ‖v‖) - arg v * c.im| ≤
      |Real.log ‖G‖| + |c.re| * Real.log t + |c.re| * |Real.log ‖v‖| + |arg v * c.im| := by
    have e1 := abs_sub (Real.log ‖G‖ + c.re * (Real.log t + Real.log ‖v‖)) (arg v * c.im)
    have e2 := abs_add_le (Real.log ‖G‖) (c.re * (Real.log t + Real.log ‖v‖))
    have e3 : |c.re * (Real.log t + Real.log ‖v‖)| ≤ |c.re| * Real.log t +
        |c.re| * |Real.log ‖v‖| := by
      rw [abs_mul, ← mul_add]
      gcongr
      refine (abs_add_le _ _).trans ?_
      rw [abs_of_pos (by linarith)]
    linarith
  have h3 := norm_add_le α (log (G * ((t : ℂ) * v) ^ c))
  have hα : ‖α‖ ≤ ‖α‖ * Real.log t := le_mul_of_one_le_right (norm_nonneg _) hlt1
  have hG' : |Real.log ‖G‖| ≤ |Real.log ‖G‖| * Real.log t :=
    le_mul_of_one_le_right (abs_nonneg _) hlt1
  have hv' : |c.re| * |Real.log ‖v‖| ≤ |c.re| * |Real.log ‖v‖| * Real.log t :=
    le_mul_of_one_le_right (by positivity) hlt1
  have ha' : |arg v * c.im| ≤ |arg v * c.im| * Real.log t :=
    le_mul_of_one_le_right (abs_nonneg _) hlt1
  have hp' : π ≤ π * Real.log t := le_mul_of_one_le_right Real.pi_pos.le hlt1
  calc ‖α + log (G * ((t : ℂ) * v) ^ c)‖
      ≤ ‖α‖ + (|Real.log ‖G‖| + |c.re| * Real.log t + |c.re| * |Real.log ‖v‖| +
          |arg v * c.im| + π) := by linarith
    _ ≤ _ := by nlinarith

/-- `log (-(t i)) = log t - (π/2) i` for `t > 0`. -/
theorem kumZ_log_neg_ofReal_mul_I {t : ℝ} (ht : 0 < t) :
    log (-((t : ℂ) * I)) = Real.log t - (π / 2 : ℝ) * I := by
  have h : -((t : ℂ) * I) = (t : ℂ) * (-I) := by ring
  apply Complex.ext
  · rw [h]; simp [log_re, abs_of_pos ht]
  · rw [h, log_im, arg_real_mul _ ht, arg_neg_I]; simp

/-- The Landau scale: `log (2πn) / (2πn) = O(n⁻¹ log n)`. -/
theorem kumZ_scale_isBigO (C : ℝ) :
    (fun n : ℕ => C * Real.log (2 * n * π) / (2 * n * π)) =O[atTop]
      (fun n : ℕ => ‖(n : ℂ)⁻¹ * log n‖) := by
  refine IsBigO.of_bound (|C| * 4) ?_
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hpi := Real.two_le_pi
  have hpi4 := Real.pi_le_four
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
  have hcl : log (n : ℂ) = (Real.log n : ℂ) := by
    rw [← ofReal_natCast, ofReal_log hn0.le]
  have hg : ‖(n : ℂ)⁻¹ * log n‖ = (n : ℝ)⁻¹ * Real.log n := by
    rw [norm_mul, norm_inv, hcl, norm_real, Real.norm_of_nonneg hlogn, Complex.norm_natCast]
  rw [hg, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ (n : ℝ)⁻¹ * Real.log n)]
  have h8 : Real.log (2 * n * π) ≤ 4 * Real.log n := by
    rw [← Real.log_rpow hn0]
    apply Real.log_le_log (by positivity)
    have : (n : ℝ) ^ (4 : ℝ) = n ^ 4 := by norm_cast
    rw [this]
    have h3 : (8 : ℝ) ≤ n ^ 3 := by
      have := pow_le_pow_left₀ (by norm_num) hn' 3
      norm_num at this; linarith
    calc 2 * (n : ℝ) * π ≤ 2 * n * 4 := by gcongr
      _ = 8 * n := by ring
      _ ≤ n ^ 3 * n := by gcongr
      _ = n ^ 4 := by ring
  have hpos : 0 ≤ Real.log (2 * n * π) := Real.log_nonneg (by nlinarith [hn', hpi])
  rw [abs_div, abs_mul, abs_of_nonneg hpos, abs_of_pos (by positivity : (0 : ℝ) < 2 * n * π)]
  rw [div_le_iff₀ (by positivity)]
  calc |C| * Real.log (2 * n * π) ≤ |C| * (4 * Real.log n) := by gcongr
    _ ≤ |C| * 4 * ((n : ℝ)⁻¹ * Real.log n) * (2 * n * π) := by
        field_simp
        nlinarith [abs_nonneg C, mul_nonneg (abs_nonneg C) hlogn]

end LargeZeros

/-- DLMF 13.9.9: for `a, b - a ∉ -ℕ` the large zeros of `M(a,b,·)` near the imaginary axis are
`±(2n + a)πi + log(-Γ(a)/Γ(b-a) (±2nπi)^{b-2a}) + O(n⁻¹ log n)`. -/
@[dlmf 13.9.E9]
theorem kummerM_large_zeros (a b : ℂ) (sign : Bool) (ha : ∀ k : ℕ, a ≠ -k)
    (hba : ∀ k : ℕ, b - a ≠ -k) (hb : ∀ k : ℕ, b ≠ -k) :
    ∃ r : ℕ → ℂ,
      Asymptotics.IsBigO atTop
        (fun n : ℕ => r n -
          ((if sign then 1 else -1) * (2 * n + a) * π * I +
            log (-Gamma a / Gamma (b - a) *
              ((if sign then 1 else -1) * 2 * n * π * I) ^ (b - 2 * a))))
        (fun n : ℕ => (n : ℂ)⁻¹ * log n) ∧
      ∀ᶠ n : ℕ in atTop, kummerM a b (r n) = 0 := by
  set F : ℕ → ℂ := fun n => (if sign then 1 else -1) * (2 * n + a) * π * I +
    log (-Gamma a / Gamma (b - a) * ((if sign then 1 else -1) * 2 * n * π * I) ^ (b - 2 * a))
    with hF
  suffices h : ∃ C : ℝ, ∀ᶠ n : ℕ in atTop, ∃ z, ‖z - F n‖ ≤
      C * Real.log (2 * n * π) / (2 * n * π) ∧ kummerM a b z = 0 by
    obtain ⟨C, hC⟩ := h
    obtain ⟨r, hr, hr0⟩ := Complex.zloc_eventually_exists_zero_isBigO
      (f := fun _ => kummerM a b) (w := F) hC (kumZ_scale_isBigO C)
    exact ⟨r, Asymptotics.isBigO_norm_right.mp hr, hr0⟩
  have hGa : Gamma a ≠ 0 := Gamma_ne_zero ha
  have hGba : Gamma (b - a) ≠ 0 := Gamma_ne_zero hba
  have hG : -Gamma a / Gamma (b - a) ≠ 0 := div_ne_zero (neg_ne_zero.mpr hGa) hGba
  have ht : Tendsto (fun n : ℕ => 2 * (n : ℝ) * π) atTop atTop := by
    have h1 := (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop (by norm_num : (0:ℝ) < 2)
    exact h1.atTop_mul_const Real.pi_pos
  have hexpn (n : ℕ) (x : ℂ) : exp ((2 * n + x) * π * I) = exp (π * I * x) := by
    rw [show (2 * n + x) * π * I = n * (2 * π * I) + π * I * x by ring, Complex.exp_add,
      exp_nat_mul_two_pi_mul_I, one_mul]
  cases sign with
  | true =>
    obtain ⟨K, hK⟩ := kumZ_dist_bound (-Gamma a / Gamma (b - a)) I (b - 2 * a) (a * π * I) hG
      I_ne_zero
    obtain ⟨C, hC⟩ := kumZ_core a b hb ha hba K
    refine ⟨C, ?_⟩
    filter_upwards [ht.eventually hC, ht.eventually (eventually_ge_atTop (Real.exp 1))]
      with n hn hn1
    set t : ℝ := 2 * (n : ℝ) * π with htdef
    have ht0 : 0 < t := lt_of_lt_of_le (Real.exp_pos 1) hn1
    have hcast : (1 : ℂ) * 2 * n * π * I = (t : ℂ) * I := by rw [htdef]; push_cast; ring
    have hY : -Gamma a / Gamma (b - a) * ((t : ℂ) * I) ^ (b - 2 * a) ≠ 0 := by
      refine mul_ne_zero hG ?_
      rw [cpow_def_of_ne_zero (mul_ne_zero (ofReal_ne_zero.mpr ht0.ne') I_ne_zero)]
      exact Complex.exp_ne_zero _
    have hFn : F n = (2 * n + a) * π * I +
        log (-Gamma a / Gamma (b - a) * ((t : ℂ) * I) ^ (b - 2 * a)) := by
      rw [hF]; simp only [ite_true]; rw [hcast]; ring
    refine hn (F n) ?_ ?_
    · rw [hFn, Complex.exp_add, exp_log hY, hexpn]
      field_simp
    · have : F n - (t : ℂ) * I = a * π * I +
          log (-Gamma a / Gamma (b - a) * ((t : ℂ) * I) ^ (b - 2 * a)) := by
        rw [hFn, htdef]; push_cast; ring
      rw [this]
      exact hK t hn1
  | false =>
    obtain ⟨K, hK⟩ := kumZ_dist_bound (-Gamma a / Gamma (b - a)) (-I) (b - 2 * a)
      (-(a * π * I)) hG (neg_ne_zero.mpr I_ne_zero)
    have ha' : ∀ k : ℕ, b - (b - a) ≠ -k := by simpa [sub_sub_cancel] using ha
    obtain ⟨C, hC⟩ := kumZ_core (b - a) b hb hba ha' K
    refine ⟨C, ?_⟩
    filter_upwards [ht.eventually hC, ht.eventually (eventually_ge_atTop (Real.exp 1))]
      with n hn hn1
    set t : ℝ := 2 * (n : ℝ) * π with htdef
    have ht0 : 0 < t := lt_of_lt_of_le (Real.exp_pos 1) hn1
    have htI : (t : ℂ) * I ≠ 0 := mul_ne_zero (ofReal_ne_zero.mpr ht0.ne') I_ne_zero
    have hcast : (-1 : ℂ) * 2 * n * π * I = (t : ℂ) * (-I) := by rw [htdef]; push_cast; ring
    have hY : -Gamma a / Gamma (b - a) * ((t : ℂ) * (-I)) ^ (b - 2 * a) ≠ 0 := by
      refine mul_ne_zero hG ?_
      rw [cpow_def_of_ne_zero (mul_ne_zero (ofReal_ne_zero.mpr ht0.ne')
        (neg_ne_zero.mpr I_ne_zero))]
      exact Complex.exp_ne_zero _
    have hFn : F n = -((2 * n + a) * π * I) +
        log (-Gamma a / Gamma (b - a) * ((t : ℂ) * (-I)) ^ (b - 2 * a)) := by
      rw [hF]; simp only [Bool.false_eq_true, ite_false]; rw [hcast]; ring
    have hex : exp (-F n) = -(exp (π * I * (b - a)) * Gamma (b - a) / Gamma (b - (b - a))) *
        ((t : ℂ) * I) ^ (b - 2 * (b - a)) := by
      rw [hFn, neg_add, neg_neg, Complex.exp_add, Complex.exp_neg, exp_log hY, hexpn,
        sub_sub_cancel]
      have hm : (t : ℂ) * (-I) = -((t : ℂ) * I) := by ring
      rw [hm, cpow_def_of_ne_zero (neg_ne_zero.mpr htI), cpow_def_of_ne_zero htI,
        kumZ_log_neg_ofReal_mul_I ht0, kumZ_log_ofReal_mul_I ht0]
      have hE : exp (π * I * a) * exp (-((↑(Real.log t) - ↑(π / 2 : ℝ) * I) * (b - 2 * a))) =
          exp (π * I * (b - a)) *
            exp ((↑(Real.log t) + ↑(π / 2 : ℝ) * I) * (b - 2 * (b - a))) := by
        rw [← Complex.exp_add, ← Complex.exp_add]
        congr 1
        push_cast
        ring
      rw [Complex.exp_neg] at hE
      rw [mul_inv, show (-Gamma a / Gamma (b - a))⁻¹ = -(Gamma (b - a) / Gamma a) by
        rw [neg_div, inv_neg, inv_div]]
      calc _ = -(Gamma (b - a) / Gamma a) * (exp (π * I * a) *
            (exp ((↑(Real.log t) - ↑(π / 2 : ℝ) * I) * (b - 2 * a)))⁻¹) := by ring
        _ = _ := by rw [hE]; ring
    have hdist : ‖-F n - (t : ℂ) * I‖ ≤ K * Real.log t := by
      have : -F n - (t : ℂ) * I = -(-(a * π * I) +
          log (-Gamma a / Gamma (b - a) * ((t : ℂ) * (-I)) ^ (b - 2 * a))) := by
        rw [hFn, htdef]; push_cast; ring
      rw [this, norm_neg]
      exact hK t hn1
    obtain ⟨z', hz', hz'0⟩ := hn (-F n) hex hdist
    refine ⟨-z', ?_, ?_⟩
    · rw [show -z' - F n = -(z' - -F n) by ring, norm_neg]; exact hz'
    · rw [kummerM_kummer_transform hb, neg_neg, hz'0, mul_zero]

/-- Identity under the stated parameter and domain assumptions: `∃ α : ℕ → ℂ, Asymptotics.IsBigO
atTop (fun n : ℕ => α n + π ^ 2 / (4 * z) * ((n : ℂ) ^ 2 + (b - 3 / 2) * n) + 1 / (16 * z) *
((b - 3 / 2) ^ 2 * π ^ 2 + 4 / 3 * z ^ 2 - 8 * b * (z - 1) - 4 * b ^ 2 - 3)) (fun n : ℕ => (n
: ℂ)⁻¹) ∧ ∀ᶠ n : ℕ in atTop, kummerM (α n) b z = 0`. -/
@[dlmf 13.9.E10]
theorem kummerM_zeros_in_a (b z : ℂ) (hz : z ≠ 0) (hb : ∀ k : ℕ, b ≠ -k) :
    ∃ α : ℕ → ℂ,
      Asymptotics.IsBigO atTop
        (fun n : ℕ => α n + π ^ 2 / (4 * z) * ((n : ℂ) ^ 2 + (b - 3 / 2) * n) +
          1 / (16 * z) * ((b - 3 / 2) ^ 2 * π ^ 2 + 4 / 3 * z ^ 2 -
            8 * b * (z - 1) - 4 * b ^ 2 - 3))
        (fun n : ℕ => (n : ℂ)⁻¹) ∧
      ∀ᶠ n : ℕ in atTop, kummerM (α n) b z = 0 := by
  sorry

/-- Zeros of `U(a,b,·)` in the open sector `|ph z| < π`; DLMF calls their number `T(a,b)`. -/
def kummerUSectorZeros (a b : ℝ) : Set ℂ :=
  {z | z ≠ 0 ∧ |arg z| < π ∧ kummerU a b z = 0}

/-- DLMF 13.9.11: the number of zeros in the sector `|ph z| < π` when `b ≤ 1`, `a < 0` and
`Γ(a)Γ(a-b+1) > 0`, with `a`, `b` and `a-b+1` nonintegral. Corrected 2026-10-20: the
earlier statement counted positive zeros with this formula and omitted DLMF's hypotheses;
it was false, e.g. at `(a,b) = (-1.3,-2.2)` there are no positive zeros. -/
@[dlmf 13.9.E11]
theorem kummerU_sectorZeros_gamma_pos {a b : ℝ} (hb : b ≤ 1) (ha : a < 0)
    (hai : ∀ n : ℤ, a ≠ n) (hbi : ∀ n : ℤ, b ≠ n) (habi : ∀ n : ℤ, a - b + 1 ≠ n)
    (h : 0 < Real.Gamma a * Real.Gamma (a - b + 1)) :
    (kummerUSectorZeros a b).encard = Int.toNat (⌊-a⌋ + 1) := by
  sorry

/-- DLMF 13.9.12, the companion of `kummerU_sectorZeros_gamma_pos` for
`Γ(a)Γ(a-b+1) < 0` (corrected 2026-10-20 in the same way). -/
@[dlmf 13.9.E12]
theorem kummerU_sectorZeros_gamma_neg {a b : ℝ} (hb : b ≤ 1) (ha : a < 0)
    (hai : ∀ n : ℤ, a ≠ n) (hbi : ∀ n : ℤ, b ≠ n) (habi : ∀ n : ℤ, a - b + 1 ≠ n)
    (h : Real.Gamma a * Real.Gamma (a - b + 1) < 0) :
    (kummerUSectorZeros a b).encard = Int.toNat ⌊-a⌋ := by
  sorry

/-- Identity under the stated parameter and domain assumptions: `(kummerUPosZeros a b).encard =
0`. -/
@[dlmf 13.9.E13]
theorem kummerU_posZeros_none {a b : ℝ} (ha : 0 ≤ a) :
    (kummerUPosZeros a b).encard = 0 := by
  rw [Set.encard_eq_zero, Set.eq_empty_iff_forall_notMem]
  rintro x ⟨hx, hzero⟩
  rcases ha.eq_or_lt with rfl | ha
  · simp [kummerU_zero] at hzero
  · have hl := kummerU_laplace (a := (a : ℂ)) (b := b) (z := x) (by simpa using ha)
      (by simpa using hx)
    let g : ℝ → ℝ := fun t => Real.exp (-x * t) * t ^ (a - 1) * (1 + t) ^ (b - a - 1)
    have hfg : ∀ t ∈ Set.Ioi (0 : ℝ),
        exp (-(x : ℂ) * t) * (t : ℂ) ^ ((a : ℂ) - 1) * (1 + (t : ℂ)) ^ ((b : ℂ) - a - 1) =
          (g t : ℂ) := by
      intro t ht
      have ht0 : (0 : ℝ) ≤ t := le_of_lt ht
      have ht1 : (0 : ℝ) ≤ 1 + t := by linarith
      simp only [g, ofReal_mul, ofReal_exp, ofReal_cpow ht0, ofReal_cpow ht1]
      push_cast
      ring_nf
    have hgpos : ∀ t ∈ Set.Ioi (0 : ℝ), 0 < g t := by
      intro t ht
      have ht' : (0 : ℝ) < t := ht
      have : 0 < 1 + t := by linarith
      positivity
    have hgi : MeasureTheory.IntegrableOn g (Set.Ioi 0) := by
      refine MeasureTheory.IntegrableOn.congr_fun
        (kummerU_laplace_integrable (a := (a : ℂ)) (b := b) (z := x)
          (by simpa using ha) (by simpa using hx)).norm (fun t ht => ?_) measurableSet_Ioi
      rw [hfg t ht, norm_real, Real.norm_of_nonneg (hgpos t ht).le]
    have hpos : 0 < ∫ t in Set.Ioi 0, g t := by
      rw [MeasureTheory.setIntegral_pos_iff_support_of_nonneg_ae
        (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => (hgpos t ht).le) hgi]
      have hsup : Function.support g ∩ Set.Ioi 0 = Set.Ioi 0 := by
        ext t
        simp only [Set.mem_inter_iff, Function.mem_support, and_iff_right_iff_imp]
        exact fun ht => (hgpos t ht).ne'
      rw [hsup, Real.volume_Ioi]
      exact ENNReal.zero_lt_top
    have hI : (∫ t : ℝ in Set.Ioi 0,
        exp (-(x : ℂ) * t) * (t : ℂ) ^ ((a : ℂ) - 1) * (1 + (t : ℂ)) ^ ((b : ℂ) - a - 1)) =
        ((∫ t in Set.Ioi 0, g t : ℝ) : ℂ) := by
      rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hfg,
        integral_complex_ofReal]
    have hG : Gamma (a : ℂ) ≠ 0 := Gamma_ne_zero_of_re_pos (by simpa using ha)
    rw [hl, hI] at hzero
    simp [hG, hpos.ne'] at hzero

/-- DLMF 13.9.14: the number `P(a,b)` of positive zeros when `a + 1 < b ≤ 1`, with `a`, `b`
and `a-b+1` nonintegral (acquired 2026-10-20; DLMF's `P` counts positive zeros). Proved by
Kummer's transformation and the Sturm-comparison count `kzt_U_posZeros_count`; only the
nonintegrality of `a-b+1` is used (`hai` and `hbi` are not needed). -/
@[dlmf 13.9.E14]
theorem kummerU_posZeros_ceil {a b : ℝ} (hb : b ≤ 1) (hab : a + 1 < b)
    (habi : ∀ n : ℤ, a - b + 1 ≠ n) :
    (kummerUPosZeros a b).encard = Int.toNat ⌈b - a - 1⌉ := by
  have h := kzt_U_posZeros_count (a := a - b + 1) (b := 2 - b) (by linarith) (by linarith) habi
  have hset : kummerUPosZeros a b =
      {x : ℝ | 0 < x ∧ kummerU ((a - b + 1 : ℝ) : ℂ) ((2 - b : ℝ) : ℂ) (x : ℂ) = 0} := by
    ext x
    simp only [kummerUPosZeros, Set.mem_ofPred_eq]
    refine and_congr_right fun hx => ?_
    have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
    have hpow : (x : ℂ) ^ (1 - (b : ℂ)) ≠ 0 := by
      rw [Ne, cpow_eq_zero_iff]
      exact fun h => hx0 h.1
    rw [kummerU_kummer_transform_all _ _ hx0, mul_eq_zero, or_iff_right hpow]
    push_cast
    rfl
  rw [hset, h, show -(a - b + 1) = b - a - 1 by ring]

/-- DLMF 13.9.15: no positive zeros when `a + 1 ≥ b`. Stronger than DLMF: no restriction on
`b` and no nonintegrality hypotheses. Kummer's transformation reduces it to 13.9.13 at the
nonnegative first parameter `a - b + 1`. -/
@[dlmf 13.9.E15]
theorem kummerU_posZeros_none_of_le {a b : ℝ} (h : b ≤ a + 1) :
    (kummerUPosZeros a b).encard = 0 := by
  have h0 := kummerU_posZeros_none (a := a - b + 1) (b := 2 - b) (by linarith)
  rw [Set.encard_eq_zero, Set.eq_empty_iff_forall_notMem] at h0 ⊢
  rintro x ⟨hx, hzero⟩
  refine h0 x ⟨hx, ?_⟩
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  rw [kummerU_kummer_transform_all _ _ hx0] at hzero
  have hpow : (x : ℂ) ^ (1 - (b : ℂ)) ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff]
    exact fun h => hx0 h.1
  push_cast
  exact (mul_eq_zero.mp hzero).resolve_left hpow

/- DLMF 13.9.14 (count of zeros of `U(a,b,·)` on the negative axis) was removed from the
formalization: with the principal-branch `kummerU` the stated count is false, since `U` is
complex-valued and bounded away from zero on the negative axis in tested cases where the
count is positive. See `STATEMENT_AUDIT_2026-09-27.md`. -/

/-- No zeros of the principal-branch `U(a,b,·)` on the negative axis when `a + 1 ≥ b`.
This is not DLMF 13.9.15, whose `P(a,b)` counts positive zeros (see
`kummerU_posZeros_none_of_le`); the `dlmf` tag was removed on 2026-10-20.
The polynomial case `a ∈ -ℕ` is excluded: there `U(-n,b,x) = (-1)ⁿ n! L_n^{(b-1)}(x)` with
`b - 1 ≤ -n`, which can vanish at negative `x` (e.g. `U(-1,-1,x) = x + 1`). For other `a`
the statement was checked numerically (mpmath, 16 October 2026); `|U|` approaches zero on the
negative axis only as `a` approaches a nonpositive integer. -/
theorem kummerU_negZeros_none {a b : ℝ} (h : a + 1 ≥ b) (ha : ∀ n : ℕ, a ≠ -(n : ℝ)) :
    {x : ℝ | x < 0 ∧ kummerU a b (x : ℂ) = 0}.encard = 0 := by
  rw [Set.encard_eq_zero, Set.eq_empty_iff_forall_notMem]
  rintro x ⟨hx, hU⟩
  exact DLMF.Confluent.kzt_U_neg_ne_zero h ha hx hU

/-- Identity under the stated parameter and domain assumptions: `∃ α : ℕ → ℂ, Asymptotics.IsBigO
atTop (fun n : ℕ => α n + n + 2 / π * (z * n) ^ (1 / 2 : ℂ) + 2 * z / π ^ 2 - b / 2 - 1 / 4)
(fun n : ℕ => (n : ℂ)⁻¹ ^ (1 / 2 : ℂ)) ∧ ∀ᶠ n : ℕ in atTop, kummerU (α n) b z = 0`. -/
@[dlmf 13.9.E16]
theorem kummerU_zeros_in_a (b z : ℂ) (hz : z ∈ slitPlane) :
    ∃ α : ℕ → ℂ,
      Asymptotics.IsBigO atTop
        (fun n : ℕ => α n + n + 2 / π * (z * n) ^ (1 / 2 : ℂ) + 2 * z / π ^ 2 -
          b / 2 - 1 / 4)
        (fun n : ℕ => (n : ℂ)⁻¹ ^ (1 / 2 : ℂ)) ∧
      ∀ᶠ n : ℕ in atTop, kummerU (α n) b z = 0 := by
  sorry

end DLMF.Confluent

end
end
