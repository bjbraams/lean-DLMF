/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Struve.Asymptotics.IntegratedExpansions

/-!
# Large-order and scaled Struve expansions

Large-order expansions and their scaled forms, with coefficient and normalization identities.

Source references and common attribution are retained in
`DLMF.Struve.Asymptotics`.
-/

@[expose] public noncomputable section

open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF

open scoped Real Topology Nat

namespace DLMF.Struve

open DLMF.Bessel DLMF.Airy

section LargeOrder

open scoped Interval

/-- In the sector `|arg ν| ≤ π - δ`, `‖ν + s‖ ≥ s sin δ` for `s > 0`. -/
theorem mul_sin_le_norm_add_ofReal {ν : ℂ} {δ : ℝ} (hδ : 0 < δ) (harg : |arg ν| ≤ π - δ) {s : ℝ}
    (hs : 0 < s) : s * Real.sin δ ≤ ‖ν + s‖ := by
  set θ := arg ν
  set r := ‖ν‖
  have hre : ν.re = r * Real.cos θ := (norm_mul_cos_arg ν).symm
  have him : ν.im = r * Real.sin θ := (norm_mul_sin_arg ν).symm
  have hr0 : 0 ≤ r := norm_nonneg _
  have hsq : ‖ν + s‖ ^ 2 = (r * Real.cos θ + s) ^ 2 + (r * Real.sin θ) ^ 2 := by
    rw [Complex.sq_norm, normSq_apply, add_re, add_im, ofReal_re, ofReal_im, add_zero, hre, him]
    ring
  have hcs := Real.sin_sq_add_cos_sq θ
  have hkey : (s * Real.sin δ) ^ 2 ≤ ‖ν + s‖ ^ 2 := by
    rw [hsq]
    have hsd := Real.sin_sq_le_one δ
    rcases le_or_gt 0 (Real.cos θ) with hc | hc
    · nlinarith [mul_nonneg (mul_nonneg hr0 hs.le) hc, sq_nonneg (r * Real.cos θ),
        sq_nonneg (r * Real.sin θ), mul_le_mul_of_nonneg_left hsd (sq_nonneg s)]
    · have hθ : π / 2 < |θ| := by
        by_contra h; push Not at h
        have := Real.cos_nonneg_of_neg_pi_div_two_le_of_le (x := θ)
          (by linarith [neg_abs_le θ]) (by linarith [le_abs_self θ])
        linarith
      have h1 : Real.sin δ ≤ Real.sin (π - |θ|) :=
        Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) (by linarith)
          (by linarith)
      have hδ0 : 0 ≤ Real.sin δ :=
        Real.sin_nonneg_of_nonneg_of_le_pi hδ.le (by linarith [abs_nonneg θ])
      have h2 : Real.sin (π - |θ|) ^ 2 = Real.sin θ ^ 2 := by
        rw [Real.sin_pi_sub]
        rcases le_total 0 θ with h | h
        · rw [abs_of_nonneg h]
        · rw [abs_of_nonpos h, Real.sin_neg, neg_sq]
      have h3 : Real.sin δ ^ 2 ≤ Real.sin θ ^ 2 := by
        rw [← h2]
        have : 0 ≤ Real.sin (π - |θ|) := Real.sin_nonneg_of_nonneg_of_le_pi
          (by linarith [Complex.abs_arg_le_pi ν]) (by linarith [abs_nonneg θ])
        exact pow_le_pow_left₀ hδ0 h1 2
      have e : (r * Real.cos θ + s) ^ 2 + (r * Real.sin θ) ^ 2 =
          (r + s * Real.cos θ) ^ 2 + s ^ 2 * Real.sin θ ^ 2 := by
        linear_combination (r ^ 2 - s ^ 2) * hcs
      rw [e]
      nlinarith [sq_nonneg (r + s * Real.cos θ), mul_le_mul_of_nonneg_left h3 (sq_nonneg s)]
  calc s * Real.sin δ ≤ |s * Real.sin δ| := le_abs_self _
    _ = Real.sqrt ((s * Real.sin δ) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (‖ν + s‖ ^ 2) := Real.sqrt_le_sqrt hkey
    _ = ‖ν + s‖ := Real.sqrt_sq (norm_nonneg _)

/-- `‖1/Γ(s₀ + k)‖ ≤ ‖1/Γ(s₀)‖ / ((3/2) sin δ)^k` for `s₀ = ν + N + 3/2` in the sector. -/
theorem norm_recip_Gamma_add_nat_le_of_arg {ν : ℂ} {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π)
    (harg : |arg ν| ≤ π - δ) (N k : ℕ) :
    ‖(Gamma (ν + N + 3 / 2 + k))⁻¹‖ ≤
      ‖(Gamma (ν + N + 3 / 2))⁻¹‖ / (3 / 2 * Real.sin δ) ^ k := by
  have hsin : 0 < Real.sin δ := Real.sin_pos_of_pos_of_lt_pi hδ hδπ
  have hρ : 0 < 3 / 2 * Real.sin δ := by positivity
  induction k with
  | zero => simp
  | succ k ih =>
    set s := ν + N + 3 / 2 + k with hs
    have hsn : (N + 3 / 2 + k : ℝ) * Real.sin δ ≤ ‖s‖ := by
      have := mul_sin_le_norm_add_ofReal hδ harg (s := N + 3 / 2 + k) (by positivity)
      rw [hs]; convert this using 2; push_cast; ring
    have hs1 : 3 / 2 * Real.sin δ ≤ ‖s‖ := le_trans (by
      have : (3 / 2 : ℝ) ≤ N + 3 / 2 + k := by
        have := (N.cast_nonneg : (0 : ℝ) ≤ N); have := (k.cast_nonneg : (0 : ℝ) ≤ k); linarith
      nlinarith) hsn
    have hs0 : s ≠ 0 := by
      intro h; rw [h, norm_zero] at hs1; linarith
    have hrec := DLMF.Hypergeometric.recip_Gamma_eq_mul_recip_Gamma_add_one s
    have h1 : (Gamma (s + 1))⁻¹ = (Gamma s)⁻¹ / s := by
      rw [hrec]; field_simp
    rw [show ν + N + 3 / 2 + ((k + 1 : ℕ) : ℂ) = s + 1 by rw [hs]; push_cast; ring, h1,
      norm_div, pow_succ, ← div_div]
    exact div_le_div₀ (by positivity) ih hρ hs1

/-- Tail bound for the Struve series in the order variable. -/
theorem struve_series_tail_isBigO {z : ℂ} (hz : z ≠ 0) {ε : ℂ} (hε : ‖ε‖ = 1) {δ : ℝ}
    (hδ : 0 < δ) (hδπ : δ < π) (N : ℕ) (S : ℂ → ℂ)
    (hS : ∀ ν, HasSum (fun n : ℕ => ε ^ n * (z / 2) ^ (2 * n) * struveCoeff ν n) (S ν)) :
    (fun ν : ℂ => (z / 2) ^ (ν + 1) * S ν - (z / 2) ^ (ν + 1) *
      ∑ n ∈ Finset.range N, ε ^ n * (z / 2) ^ (2 * n) * struveCoeff ν n) =O[sector (π - δ)]
      (fun ν : ℂ => (z / 2) ^ (ν + 1) / Gamma (ν + N + 3 / 2)) := by
  have hsin : 0 < Real.sin δ := Real.sin_pos_of_pos_of_lt_pi hδ hδπ
  set ρ := 3 / 2 * Real.sin δ with hρdef
  have hρ : 0 < ρ := by positivity
  set q := ‖z / 2‖ with hq
  have hq0 : 0 < q := norm_pos_iff.mpr (div_ne_zero hz two_ne_zero)
  set a : ℕ → ℝ := fun k => q ^ (2 * (k + N)) / (Real.Gamma ((k + N : ℕ) + 3 / 2) * ρ ^ k)
    with hadef
  have hΓpos : ∀ n : ℕ, 0 < Real.Gamma ((n : ℝ) + 3 / 2) := fun n =>
    Real.Gamma_pos_of_pos (by positivity)
  have hapos : ∀ k, 0 < a k := fun k => by rw [hadef]; have := hΓpos (k + N); positivity
  have hsum : Summable a := by
    refine summable_of_ratio_test_tendsto_lt_one (l := 0) zero_lt_one
      (Eventually.of_forall fun k => (hapos k).ne') ?_
    have hratio : ∀ k : ℕ, ‖a (k + 1)‖ / ‖a k‖ = q ^ 2 / ρ * ((k + N : ℝ) + 3 / 2)⁻¹ := by
      intro k
      rw [Real.norm_of_nonneg (hapos _).le, Real.norm_of_nonneg (hapos _).le, hadef]
      simp only
      have hG : Real.Gamma (((k + 1 + N : ℕ) : ℝ) + 3 / 2) =
          ((k + N : ℝ) + 3 / 2) * Real.Gamma (((k + N : ℕ) : ℝ) + 3 / 2) := by
        rw [show (((k + 1 + N : ℕ) : ℝ) + 3 / 2) = ((k + N : ℕ) : ℝ) + 3 / 2 + 1 by
          push_cast; ring, Real.Gamma_add_one (by positivity)]
        push_cast; ring
      rw [hG, show 2 * (k + 1 + N) = 2 * (k + N) + 2 by ring, pow_add, pow_succ]
      have := hΓpos (k + N)
      have : (0 : ℝ) < (k + N : ℝ) + 3 / 2 := by positivity
      field_simp
      ring
    simp_rw [hratio]
    rw [show (0 : ℝ) = q ^ 2 / ρ * 0 by ring]
    refine tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp ?_)
    exact tendsto_atTop_add_const_right _ _ (tendsto_natCast_atTop_atTop.atTop_add
      tendsto_const_nhds)
  set A := ∑' k, a k
  refine IsBigO.of_bound A ?_
  rw [DLMF.sector, eventually_inf_principal]
  refine Eventually.of_forall fun ν hν => ?_
  obtain ⟨-, harg⟩ := hν
  have htail : S ν - ∑ n ∈ Finset.range N, ε ^ n * (z / 2) ^ (2 * n) * struveCoeff ν n =
      ∑' k, ε ^ (k + N) * (z / 2) ^ (2 * (k + N)) * struveCoeff ν (k + N) := by
    rw [← (hS ν).tsum_eq, ← (hS ν).summable.sum_add_tsum_nat_add N]; ring
  have hbd : ∀ k, ‖ε ^ (k + N) * (z / 2) ^ (2 * (k + N)) * struveCoeff ν (k + N)‖ ≤
      ‖(Gamma (ν + N + 3 / 2))⁻¹‖ * a k := by
    intro k
    have hG := norm_recip_Gamma_add_nat_le_of_arg hδ hδπ harg N k
    rw [norm_mul, norm_mul, norm_pow, norm_pow, hε, one_pow, one_mul, struveCoeff, one_div,
      mul_inv, norm_mul, show ((k + N : ℕ) : ℂ) + 3 / 2 = (((k + N : ℕ) + 3 / 2 : ℝ) : ℂ) by
        push_cast; ring, Complex.Gamma_ofReal, ← ofReal_inv, Complex.norm_real,
      Real.norm_of_nonneg (inv_nonneg.mpr (hΓpos _).le),
      show ((k + N : ℕ) : ℂ) + ν + 3 / 2 = ν + N + 3 / 2 + k by push_cast; ring, hadef]
    simp only
    rw [← hq]
    calc q ^ (2 * (k + N)) * ((Real.Gamma ((k + N : ℕ) + 3 / 2))⁻¹ *
          ‖(Gamma (ν + N + 3 / 2 + k))⁻¹‖)
        ≤ q ^ (2 * (k + N)) * ((Real.Gamma ((k + N : ℕ) + 3 / 2))⁻¹ *
          (‖(Gamma (ν + N + 3 / 2))⁻¹‖ / ρ ^ k)) := by gcongr
      _ = _ := by field_simp
  have hT := tsum_of_norm_bounded ((hsum.hasSum).mul_left ‖(Gamma (ν + N + 3 / 2))⁻¹‖) hbd
  rw [← mul_sub, htail, norm_mul, norm_div]
  calc ‖(z / 2) ^ (ν + 1)‖ * ‖∑' k, ε ^ (k + N) * (z / 2) ^ (2 * (k + N)) *
        struveCoeff ν (k + N)‖
      ≤ ‖(z / 2) ^ (ν + 1)‖ * (‖(Gamma (ν + N + 3 / 2))⁻¹‖ * A) := by gcongr
    _ = _ := by rw [norm_inv]; ring

/-- In the sector `|arg ν| ≤ π - δ`, `‖ν + s‖ ≥ ‖ν‖ sin δ` for `s ≥ 0`. -/
theorem norm_mul_sin_le_norm_add_ofReal {ν : ℂ} {δ : ℝ} (hδ : 0 < δ) (harg : |arg ν| ≤ π - δ)
    {s : ℝ} (hs : 0 ≤ s) : ‖ν‖ * Real.sin δ ≤ ‖ν + s‖ := by
  set θ := arg ν
  set r := ‖ν‖
  have hre : ν.re = r * Real.cos θ := (norm_mul_cos_arg ν).symm
  have him : ν.im = r * Real.sin θ := (norm_mul_sin_arg ν).symm
  have hr0 : 0 ≤ r := norm_nonneg _
  have hsq : ‖ν + s‖ ^ 2 = (r * Real.cos θ + s) ^ 2 + (r * Real.sin θ) ^ 2 := by
    rw [Complex.sq_norm, normSq_apply, add_re, add_im, ofReal_re, ofReal_im, add_zero, hre, him]
    ring
  have hcs := Real.sin_sq_add_cos_sq θ
  have hkey : (r * Real.sin δ) ^ 2 ≤ ‖ν + s‖ ^ 2 := by
    rw [hsq]
    have hsd := Real.sin_sq_le_one δ
    rcases le_or_gt 0 (Real.cos θ) with hc | hc
    · nlinarith [mul_nonneg (mul_nonneg hr0 hs) hc, sq_nonneg s,
        mul_le_mul_of_nonneg_left hsd (sq_nonneg r)]
    · have hθ : π / 2 < |θ| := by
        by_contra h; push Not at h
        have := Real.cos_nonneg_of_neg_pi_div_two_le_of_le (x := θ)
          (by linarith [neg_abs_le θ]) (by linarith [le_abs_self θ])
        linarith
      have h1 : Real.sin δ ≤ Real.sin (π - |θ|) :=
        Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) (by linarith)
          (by linarith)
      have hδ0 : 0 ≤ Real.sin δ :=
        Real.sin_nonneg_of_nonneg_of_le_pi hδ.le (by linarith [abs_nonneg θ])
      have h2 : Real.sin (π - |θ|) ^ 2 = Real.sin θ ^ 2 := by
        rw [Real.sin_pi_sub]
        rcases le_total 0 θ with h | h
        · rw [abs_of_nonneg h]
        · rw [abs_of_nonpos h, Real.sin_neg, neg_sq]
      have h3 : Real.sin δ ^ 2 ≤ Real.sin θ ^ 2 := by
        rw [← h2]; exact pow_le_pow_left₀ hδ0 h1 2
      have e : (r * Real.cos θ + s) ^ 2 + (r * Real.sin θ) ^ 2 =
          (s + r * Real.cos θ) ^ 2 + r ^ 2 * Real.sin θ ^ 2 := by ring
      rw [e]
      nlinarith [sq_nonneg (s + r * Real.cos θ), mul_le_mul_of_nonneg_left h3 (sq_nonneg r)]
  calc r * Real.sin δ ≤ |r * Real.sin δ| := le_abs_self _
    _ = Real.sqrt ((r * Real.sin δ) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (‖ν + s‖ ^ 2) := Real.sqrt_le_sqrt hkey
    _ = ‖ν + s‖ := Real.sqrt_sq (norm_nonneg _)

/-- Shifting a point of the sector to the right keeps it in the slit plane. -/
theorem add_ofReal_mem_slitPlane_of_arg {ν : ℂ} (hν : ν ≠ 0) {δ : ℝ} (hδ : 0 < δ)
    (harg : |arg ν| ≤ π - δ) {s : ℝ} (hs : 0 ≤ s) : ν + s ∈ slitPlane := by
  have hslit : ν ∈ slitPlane := mem_slitPlane_iff_arg.mpr
    ⟨fun h => by rw [h, abs_of_pos Real.pi_pos] at harg; linarith, hν⟩
  rcases mem_slitPlane_iff.mp hslit with h | h
  · exact Or.inl (by simp; linarith)
  · exact Or.inr (by simpa using h)

/-- `log (ν + c) - log ν = ∫₀^c ds / (ν + s)` along a horizontal segment in the slit plane. -/
theorem log_add_ofReal_sub_log {ν : ℂ} (hν : ∀ s : ℝ, 0 ≤ s → ν + s ∈ slitPlane) {c : ℝ}
    (hc : 0 ≤ c) : log (ν + c) - log ν = ∫ s in (0 : ℝ)..c, (ν + s)⁻¹ := by
  have hd : ∀ s ∈ [[0, c]], HasDerivAt (fun s : ℝ => log (ν + s)) (ν + s)⁻¹ s := by
    intro s hs
    rw [uIcc_of_le hc] at hs
    have h1 : HasDerivAt (fun s : ℝ => ν + (s : ℂ)) 1 s := by
      simpa using ((hasDerivAt_id (s : ℂ)).const_add ν).comp_ofReal
    have h := h1.clog_real (hν s hs.1)
    simpa using h
  have hcont : ContinuousOn (fun s : ℝ => (ν + s)⁻¹) [[0, c]] := by
    intro s hs
    rw [uIcc_of_le hc] at hs
    exact ((continuous_const.add continuous_ofReal).continuousAt.inv₀
      (slitPlane_ne_zero (hν s hs.1))).continuousWithinAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hcont.intervalIntegrable]
  simp

/-- `log (z/2) = log z - log 2`. -/
theorem log_div_two_eq {z : ℂ} (hz : z ≠ 0) : log (z / 2) = log z - log 2 := by
  have h2 : (2 : ℂ) = ((2 : ℝ) : ℂ) := by norm_num
  apply Complex.ext
  · rw [log_re, sub_re, log_re, h2, ← ofReal_log (by norm_num), ofReal_re, ← h2, norm_div,
      Complex.norm_ofNat, Real.log_div (norm_ne_zero_iff.mpr hz) (by norm_num)]
  · rw [log_im, sub_im, log_im, h2, ← ofReal_log (by norm_num), ofReal_im, sub_zero, ← h2,
      div_eq_mul_inv, show (2 : ℂ)⁻¹ = ((2⁻¹ : ℝ) : ℂ) by push_cast; rfl,
      arg_mul_real (by norm_num)]

/-- The map `(fun ν : ℂ => ‖ν‖)` tends to `atTop` along `(sector α)`. -/
theorem tendsto_norm_sector (α : ℝ) : Tendsto (fun ν : ℂ => ‖ν‖) (sector α) atTop :=
  tendsto_comap.mono_left inf_le_left

/-- The Stirling correction in the leading large-order term tends to `0`. -/
theorem tendsto_struve_stirling_exponent {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π) :
    Tendsto (fun ν : ℂ => (ν + 1) * (log ν - log (ν + 3 / 2)) + 3 / 2 -
      DLMF.Gamma.binetMu (ν + 3 / 2)) (sector (π - δ)) (𝓝 0) := by
  have hsin : 0 < Real.sin δ := Real.sin_pos_of_pos_of_lt_pi hδ hδπ
  have hcos : 0 < 1 - Real.cos δ := by
    have := Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl hδπ.le hδ
    rw [Real.cos_zero] at this; linarith
  set C := 3 / 2 / Real.sin δ + 1 / (6 * (1 - Real.cos δ)) with hC
  have hb : Tendsto (fun ν : ℂ => C * ‖ν‖⁻¹) (sector (π - δ)) (𝓝 0) := by
    simpa using (tendsto_inv_atTop_zero.comp (tendsto_norm_sector (π - δ))).const_mul C
  refine squeeze_zero_norm' ?_ hb
  rw [DLMF.sector, eventually_inf_principal]
  filter_upwards [tendsto_comap.eventually (eventually_gt_atTop (0 : ℝ))]
    with ν hν0 hν
  obtain ⟨hν, harg⟩ := hν
  set r := ‖ν‖ with hr
  have hshift : ∀ s : ℝ, 0 ≤ s → ν + s ∈ slitPlane := fun s hs =>
    add_ofReal_mem_slitPlane_of_arg hν hδ harg hs
  -- the logarithmic part
  have hlog := log_add_ofReal_sub_log hshift (c := 3 / 2) (by norm_num)
  push_cast at hlog
  have hA : (ν + 1) * (log ν - log (ν + 3 / 2)) + 3 / 2 =
      ∫ s in (0 : ℝ)..(3 / 2), ((s : ℂ) - 1) / (ν + s) := by
    have hint : IntervalIntegrable (fun s : ℝ => (ν + s)⁻¹) volume 0 (3 / 2) := by
      refine ContinuousOn.intervalIntegrable fun s hs => ?_
      rw [uIcc_of_le (by norm_num)] at hs
      exact ((continuous_const.add continuous_ofReal).continuousAt.inv₀
        (slitPlane_ne_zero (hshift s hs.1))).continuousWithinAt
    have h1 : ∫ s in (0 : ℝ)..(3 / 2), ((s : ℂ) - 1) / (ν + s) =
        ∫ s in (0 : ℝ)..(3 / 2), (1 - (ν + 1) * (ν + s)⁻¹) := by
      refine intervalIntegral.integral_congr fun s hs => ?_
      rw [uIcc_of_le (by norm_num)] at hs
      have := slitPlane_ne_zero (hshift s hs.1)
      field_simp
      ring
    rw [h1, intervalIntegral.integral_sub intervalIntegrable_const (hint.const_mul _),
      intervalIntegral.integral_const_mul, ← hlog]
    simp
    ring
  have hAb : ‖∫ s in (0 : ℝ)..(3 / 2), ((s : ℂ) - 1) / (ν + s)‖ ≤
      1 / (r * Real.sin δ) * |3 / 2 - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun s hs => ?_
    rw [uIoc_of_le (by norm_num)] at hs
    have h1 := norm_mul_sin_le_norm_add_ofReal hδ harg (s := s) hs.1.le
    have h2 : ‖(s : ℂ) - 1‖ ≤ 1 := by
      rw [show (s : ℂ) - 1 = ((s - 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_eq_abs, abs_le]
      constructor <;> linarith [hs.1, hs.2]
    rw [norm_div]
    have hp : 0 < r * Real.sin δ := by positivity
    calc ‖(s : ℂ) - 1‖ / ‖ν + s‖ ≤ 1 / ‖ν + s‖ := by gcongr
      _ ≤ 1 / (r * Real.sin δ) := by gcongr
  -- the Binet part
  have hw : ν + 3 / 2 ∈ slitPlane := by simpa using hshift (3 / 2) (by norm_num)
  have hμ := DLMF.Gamma.norm_binetMu_le hw
  have hcosθ : -Real.cos δ ≤ Real.cos (arg ν) := by
    rw [← Real.cos_pi_sub, ← Real.cos_abs (arg ν)]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith) harg
  have hre : ν.re = r * Real.cos (arg ν) := (norm_mul_cos_arg ν).symm
  have hwre : r * (1 - Real.cos δ) ≤ ‖ν + 3 / 2‖ + (ν + 3 / 2).re := by
    have h1 : r ≤ ‖ν + 3 / 2‖ + 3 / 2 := by
      have := norm_add_le (ν + 3 / 2) (-(3 / 2 : ℂ))
      simp only [add_neg_cancel_right, norm_neg] at this
      norm_num at this ⊢; linarith
    have h2 : (ν + 3 / 2).re = ν.re + 3 / 2 := by simp
    rw [h2, hre]
    nlinarith
  have hμb : ‖DLMF.Gamma.binetMu (ν + 3 / 2)‖ ≤ 1 / (6 * (r * (1 - Real.cos δ))) :=
    hμ.trans (one_div_le_one_div_of_le (by positivity) (by linarith))
  rw [hA]
  refine (norm_sub_le _ _).trans ?_
  have e : C * r⁻¹ = 1 / (r * Real.sin δ) * |3 / 2 - 0| + 1 / (6 * (r * (1 - Real.cos δ))) := by
    rw [hC, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2 - 0)]
    field_simp
    ring
  rw [e]
  exact add_le_add hAb hμb

/-- The leading term of the Struve series written through Binet's formula. -/
theorem struve_lead_eq {z : ℂ} (hz : z ≠ 0) {ν : ℂ} (hν : ν ≠ 0) (hw : ν + 3 / 2 ∈ slitPlane) :
    (z / 2) ^ (ν + 1) * struveCoeff ν 0 =
      z / (π * ν * Real.sqrt 2) * exp (ν * (1 + log z - log 2 - log ν)) *
        exp ((ν + 1) * (log ν - log (ν + 3 / 2)) + 3 / 2 - DLMF.Gamma.binetMu (ν + 3 / 2)) := by
  have hz2 : z / 2 ≠ 0 := div_ne_zero hz two_ne_zero
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hG32 : Gamma (3 / 2) = exp (log π * (1 / 2)) / exp (log 2) := by
    rw [show (3 / 2 : ℂ) = 1 / 2 + 1 by norm_num, Complex.Gamma_add_one _ (by norm_num),
      Complex.Gamma_one_half_eq, cpow_def_of_ne_zero hπ, exp_log two_ne_zero]
    ring
  have hGw := DLMF.Gamma.Gamma_eq_exp_binetExponent hw
  have hl2π : log (2 * π : ℂ) = log 2 + log π := by
    rw [show (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) by push_cast; ring, ← ofReal_log (by positivity),
      Real.log_mul (by norm_num) Real.pi_ne_zero, ofReal_add, ofReal_log (by norm_num),
      ofReal_log Real.pi_pos.le]
    norm_num
  have hs2 : ((Real.sqrt 2 : ℝ) : ℂ) = exp (log 2 * (1 / 2)) := by
    rw [Real.sqrt_eq_rpow, ofReal_cpow (by norm_num), cpow_def_of_ne_zero (by norm_num)]
    push_cast; ring_nf
  have hpre : z / (π * ν * Real.sqrt 2) = exp (log z - log π - log ν - log 2 * (1 / 2)) := by
    rw [Complex.exp_sub, Complex.exp_sub, Complex.exp_sub, exp_log hz, exp_log hπ, exp_log hν,
      ← hs2]
    field_simp
  rw [hpre, struveCoeff, Nat.cast_zero, zero_add, zero_add, hG32, hGw, DLMF.Gamma.binetExponent,
    hl2π, cpow_def_of_ne_zero hz2, log_div_two_eq hz]
  simp only [div_eq_mul_inv, one_mul, ← Complex.exp_neg, ← Complex.exp_add]
  congr 1
  ring

/-- `(z/2)^{ν+1} / (Γ(3/2) Γ(ν+3/2))` has the leading behaviour of DLMF 11.6.5. -/
theorem struve_lead_isEquivalent {z : ℂ} (hz : z ≠ 0) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π) :
    (fun ν : ℂ => (z / 2) ^ (ν + 1) * struveCoeff ν 0) ~[sector (π - δ)]
      fun ν => z / (π * ν * Real.sqrt 2) * exp (ν * (1 + log z - log 2 - log ν)) := by
  refine isEquivalent_of_tendsto_one ?_
  have h := (Complex.continuous_exp.tendsto 0).comp (tendsto_struve_stirling_exponent hδ hδπ)
  rw [Complex.exp_zero] at h
  refine h.congr' ?_
  rw [EventuallyEq, DLMF.sector, eventually_inf_principal]
  refine Eventually.of_forall fun ν hν => ?_
  obtain ⟨hν0, harg⟩ := hν
  have hw : ν + 3 / 2 ∈ slitPlane := by
    simpa using add_ofReal_mem_slitPlane_of_arg hν0 hδ harg (s := 3 / 2) (by norm_num)
  have hg : z / (π * ν * Real.sqrt 2) * exp (ν * (1 + log z - log 2 - log ν)) ≠ 0 := by
    refine mul_ne_zero (div_ne_zero hz (mul_ne_zero (mul_ne_zero ?_ hν0) ?_)) (exp_ne_zero _)
    · exact ofReal_ne_zero.mpr Real.pi_ne_zero
    · exact ofReal_ne_zero.mpr (by positivity)
  simp only [Function.comp_apply, Pi.div_apply]
  rw [struve_lead_eq hz hν0 hw, mul_div_cancel_left₀ _ hg]

/-- From the first term of the order expansion to the leading behaviour of DLMF 11.6.5. -/
theorem isEquivalent_of_struve_order_expansion {f : ℂ → ℂ} {z : ℂ} (hz : z ≠ 0) {δ : ℝ}
    (hδ : 0 < δ) (hδπ : δ < π)
    (h : (fun ν : ℂ => f ν - (z / 2) ^ (ν + 1) * struveCoeff ν 0) =O[sector (π - δ)]
      fun ν : ℂ => (z / 2) ^ (ν + 1) / Gamma (ν + ((1 : ℕ) : ℂ) + 3 / 2)) :
    f ~[sector (π - δ)]
      fun ν => z / (π * ν * Real.sqrt 2) * exp (ν * (1 + log z - log 2 - log ν)) := by
  have hsin : 0 < Real.sin δ := Real.sin_pos_of_pos_of_lt_pi hδ hδπ
  set lead : ℂ → ℂ := fun ν => (z / 2) ^ (ν + 1) * struveCoeff ν 0 with hlead
  set k : ℂ → ℂ := fun ν => Gamma (3 / 2) / (ν + 3 / 2) with hk
  have hk0 : Tendsto k (sector (π - δ)) (𝓝 0) := by
    have hb : Tendsto (fun ν : ℂ => ‖Gamma (3 / 2)‖ / Real.sin δ * ‖ν‖⁻¹) (sector (π - δ))
        (𝓝 0) := by
      simpa using (tendsto_inv_atTop_zero.comp (tendsto_norm_sector (π - δ))).const_mul
        (‖Gamma (3 / 2)‖ / Real.sin δ)
    refine squeeze_zero_norm' ?_ hb
    rw [DLMF.sector, eventually_inf_principal]
    filter_upwards [tendsto_comap.eventually (eventually_gt_atTop (0 : ℝ))] with ν hν0 hν
    obtain ⟨-, harg⟩ := hν
    have h1 := norm_mul_sin_le_norm_add_ofReal hδ harg (s := 3 / 2) (by norm_num)
    push_cast at h1
    rw [hk, norm_div]
    have hp : 0 < ‖ν‖ * Real.sin δ := by positivity
    calc ‖Gamma (3 / 2)‖ / ‖ν + 3 / 2‖ ≤ ‖Gamma (3 / 2)‖ / (‖ν‖ * Real.sin δ) := by gcongr
      _ = _ := by field_simp
  have hko : k =o[sector (π - δ)] fun _ => (1 : ℂ) := (isLittleO_one_iff ℂ).mpr hk0
  have hrem : (fun ν : ℂ => (z / 2) ^ (ν + 1) / Gamma (ν + ((1 : ℕ) : ℂ) + 3 / 2)) =ᶠ[sector (π - δ)]
      fun ν => lead ν * k ν := by
    rw [EventuallyEq, DLMF.sector, eventually_inf_principal]
    refine Eventually.of_forall fun ν hν => ?_
    obtain ⟨hν0, harg⟩ := hν
    have hw0 : ν + 3 / 2 ≠ 0 := slitPlane_ne_zero (by
      simpa using add_ofReal_mem_slitPlane_of_arg hν0 hδ harg (s := 3 / 2) (by norm_num))
    have hG32 : Gamma (3 / 2) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by norm_num)
    have hrec := DLMF.Hypergeometric.recip_Gamma_eq_mul_recip_Gamma_add_one (ν + 3 / 2)
    have h5 : (Gamma (ν + ((1 : ℕ) : ℂ) + 3 / 2))⁻¹ = (Gamma (ν + 3 / 2))⁻¹ / (ν + 3 / 2) := by
      rw [show ν + ((1 : ℕ) : ℂ) + 3 / 2 = ν + 3 / 2 + 1 by push_cast; ring, eq_div_iff hw0,
        mul_comm, ← hrec]
    simp only [hlead, hk, struveCoeff, Nat.cast_zero, zero_add]
    rw [div_eq_mul_inv, h5]
    field_simp
  have hE : (fun ν => f ν - lead ν) =o[sector (π - δ)] lead := by
    have h1 := h.trans_eventuallyEq hrem
    have h2 : (fun ν => lead ν * k ν) =o[sector (π - δ)] fun ν => lead ν * 1 :=
      (isBigO_refl lead _).mul_isLittleO hko
    simpa using h1.trans_isLittleO h2
  have hE' : f ~[sector (π - δ)] lead := hE
  exact hE'.trans (struve_lead_isEquivalent hz hδ hδπ)

end LargeOrder

/-- Identity under the stated parameter and domain assumptions: `(fun ν : ℂ => struveH ν z)
~[sector (π-δ)] (fun ν => z/(π*ν*Real.sqrt 2)*exp (ν*(1+log z-log 2-log ν)))`. -/
@[dlmf 11.6.E5]
theorem struveH_large_order {z : ℂ} (hz : z ∈ slitPlane) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π) :
    (fun ν : ℂ => struveH ν z) ~[sector (π-δ)] (fun ν => z/(π*ν*Real.sqrt 2)*exp (ν*(1+log z-log 2-log ν))) := by
  refine isEquivalent_of_struve_order_expansion (slitPlane_ne_zero hz) hδ hδπ ?_
  simpa [struveH] using struve_series_tail_isBigO (slitPlane_ne_zero hz) (by simp) hδ hδπ 1
    (fun ν => struveHCore ν z) (fun ν => hasSum_struveHCore ν z)

/-- Identity under the stated parameter and domain assumptions: `(fun ν : ℂ => struveL ν z)
~[sector (π-δ)] (fun ν => z/(π*ν*Real.sqrt 2)*exp (ν*(1+log z-log 2-log ν)))`. -/
@[dlmf 11.6.E5]
theorem struveL_large_order {z : ℂ} (hz : z ∈ slitPlane) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π) :
    (fun ν : ℂ => struveL ν z) ~[sector (π-δ)] (fun ν => z/(π*ν*Real.sqrt 2)*exp (ν*(1+log z-log 2-log ν))) := by
  refine isEquivalent_of_struve_order_expansion (slitPlane_ne_zero hz) hδ hδπ ?_
  have h := struve_series_tail_isBigO (slitPlane_ne_zero hz) (ε := 1) (by simp) hδ hδπ 1
    (fun ν => struveLCore ν z) (fun ν => by simpa using hasSum_struveLCore ν z)
  simpa [struveL] using h

/-- Finite polynomial formula for the saddle-endpoint coefficients. -/
def struveScaledCoeff (lam : ℂ) (k : ℕ) : ℂ :=
  (∑ j ∈ Finset.range (k+1), if k ≤ 2*j then
    ((2*j).factorial:ℂ)/(j.factorial:ℂ) *
      (∏ r ∈ Finset.range j, (Polynomial.X-Polynomial.C (1/2+r:ℂ))).coeff (2*j-k) /
      lam^(2*j) else 0) / (k.factorial:ℂ)

section StruveLOScaled

open Polynomial Metric

/-- The polynomial `∏_{r<j} (X - (1/2 + r))` of `struveScaledCoeff`. -/
noncomputable def struveLO_P (j : ℕ) : ℂ[X] :=
  ∏ r ∈ Finset.range j, (Polynomial.X - Polynomial.C (1/2 + r : ℂ))

/-- `deg P_j ≤ j`. -/
theorem struveLO_natDegree_P (j : ℕ) : (struveLO_P j).natDegree ≤ j := by
  rw [struveLO_P, natDegree_prod_of_monic _ _ (fun r _ => monic_X_sub_C _)]
  simp only [natDegree_X_sub_C, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one, le_refl]

/-- `(ν - 1/2 choose j) = P_j(ν)/j!`. -/
theorem struveLO_b_eq_eval (ν : ℂ) (j : ℕ) :
    struveLO_b (ν - 1/2) j = (struveLO_P j).eval ν / (j.factorial : ℂ) := by
  unfold struveLO_b struveLO_P
  rw [eval_prod]
  congr 1
  refine Finset.prod_congr rfl fun r _ => ?_
  simp only [eval_sub, eval_X, eval_C]
  ring

/-- The polynomial in `w = 1/ν` collecting the binomial terms. -/
noncomputable def struveLO_Q (μ : ℂ) (N : ℕ) : ℂ[X] :=
  ∑ j ∈ Finset.range N, C (((2 * j).factorial : ℂ) / ((j.factorial : ℂ) * μ ^ (2 * j))) *
    reflect (2 * j) (struveLO_P j)

/-- At `w = 1/ν`, `Q` is the sum of the binomial terms `(ν-1/2 choose j) (2j)!/(μν)^{2j}`. -/
theorem struveLO_eval_Q (μ : ℂ) (N : ℕ) {ν : ℂ} (hν : ν ≠ 0) :
    (struveLO_Q μ N).eval ν⁻¹ = ∑ j ∈ Finset.range N,
      struveLO_b (ν - 1/2) j * ((2 * j).factorial : ℂ) / (μ * ν) ^ (2 * j) := by
  unfold struveLO_Q
  rw [eval_finsetSum]
  refine Finset.sum_congr rfl fun j _ => ?_
  let _ : Invertible ν := invertibleOfNonzero hν
  have h := eval₂_reflect_mul_pow (RingHom.id ℂ) ν (2 * j) (struveLO_P j)
    ((struveLO_natDegree_P j).trans (by omega))
  rw [invOf_eq_inv] at h
  have h' : (reflect (2 * j) (struveLO_P j)).eval ν⁻¹ = (struveLO_P j).eval ν / ν ^ (2 * j) := by
    rw [eq_div_iff (pow_ne_zero _ hν)]; exact h
  rw [eval_mul, eval_C, h', struveLO_b_eq_eval]
  have : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast j.factorial_ne_zero
  rw [mul_pow]
  field_simp

/-- The coefficients of `Q` below degree `N` are `k! c_k(μ)` of DLMF 11.6.8. -/
theorem struveLO_coeff_Q (μ : ℂ) {N k : ℕ} (hk : k < N) :
    (struveLO_Q μ N).coeff k = (k.factorial : ℂ) * struveScaledCoeff μ k := by
  have hkf : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  unfold struveLO_Q struveScaledCoeff
  rw [finsetSum_coeff, mul_div_cancel₀ _ hkf]
  set f : ℕ → ℂ := fun j => (C (((2 * j).factorial : ℂ) / ((j.factorial : ℂ) * μ ^ (2 * j))) *
    reflect (2 * j) (struveLO_P j)).coeff k with hf
  have hf0 : ∀ j, k < j → f j = 0 := by
    intro j hj
    simp only [hf, coeff_C_mul, coeff_reflect]
    rw [revAt_le (by omega)]
    rw [coeff_eq_zero_of_natDegree_lt ((struveLO_natDegree_P j).trans_lt (by omega)), mul_zero]
  have hfe : ∀ j, f j = if k ≤ 2 * j then ((2 * j).factorial : ℂ) / (j.factorial : ℂ) *
      (∏ r ∈ Finset.range j, (Polynomial.X - Polynomial.C (1/2 + r : ℂ))).coeff (2 * j - k) /
      μ ^ (2 * j) else 0 := by
    intro j
    simp only [hf, coeff_C_mul, coeff_reflect]
    split_ifs with h
    · rw [revAt_le h, struveLO_P]
      ring
    · have hr : (revAt (2 * j)) k = k := by
        rw [← revAtFun_eq]; simp [revAtFun, h]
      rw [hr, coeff_eq_zero_of_natDegree_lt ((struveLO_natDegree_P j).trans_lt (by omega)),
        mul_zero]
  calc ∑ j ∈ Finset.range N, f j = ∑ j ∈ Finset.range (k + 1), f j := by
        refine (Finset.sum_subset (Finset.range_subset_range.2 (by omega)) fun j _ hj => ?_).symm
        simp only [Finset.mem_range, not_lt] at hj
        exact hf0 j (by omega)
    _ = _ := Finset.sum_congr rfl fun j _ => hfe j

/-- The binomial terms reproduce the coefficients of DLMF 11.6.6–11.6.7 up to `O(ν^{-N})`. -/
theorem struveLO_poly_bound (μ : ℂ) (N : ℕ) : ∃ B : ℝ, ∀ ν : ℂ, 1 ≤ ‖ν‖ →
    ‖∑ j ∈ Finset.range N, struveLO_b (ν - 1/2) j * ((2 * j).factorial : ℂ) / (μ * ν) ^ (2 * j) -
      ∑ k ∈ Finset.range N, (k.factorial : ℂ) * struveScaledCoeff μ k / ν ^ k‖ ≤
      B * ‖ν‖⁻¹ ^ N := by
  set Q := struveLO_Q μ N
  set T : ℂ[X] := ∑ k ∈ Finset.range N, C (Q.coeff k) * X ^ k with hT
  have hdvd : X ^ N ∣ Q - T := by
    rw [X_pow_dvd_iff]
    intro d hd
    rw [coeff_sub, hT, finsetSum_coeff]
    simp only [coeff_C_mul_X_pow]
    simp [Finset.mem_range.2 hd]
  obtain ⟨S, hS⟩ := hdvd
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn
    S.continuous.continuousOn
  refine ⟨B, fun ν hν => ?_⟩
  have hν0 : ν ≠ 0 := by rintro rfl; norm_num at hν
  have hw : ν⁻¹ ∈ closedBall (0 : ℂ) 1 := by
    rw [mem_closedBall, dist_zero_right, norm_inv]; exact inv_le_one_of_one_le₀ hν
  have h1 : ∑ k ∈ Finset.range N, (k.factorial : ℂ) * struveScaledCoeff μ k / ν ^ k = T.eval ν⁻¹ := by
    rw [hT, eval_finsetSum]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [eval_mul, eval_C, eval_pow, eval_X, struveLO_coeff_Q μ (Finset.mem_range.1 hk), inv_pow,
      div_eq_mul_inv]
  rw [← struveLO_eval_Q μ N hν0, h1, ← eval_sub, hS, eval_mul, eval_pow, eval_X, norm_mul,
    norm_pow, norm_inv, mul_comm]
  exact mul_le_mul_of_nonneg_right (hB _ hw) (by positivity)

/-- In the closed sector `|arg ν| ≤ π/2 - δ`, `re ν ≥ sin δ · |ν|`. -/
theorem struveLO_re_ge {ν : ℂ} {δ : ℝ} (hν : ν ≠ 0) (h : |arg ν| ≤ π / 2 - δ) (hδ : 0 < δ) :
    Real.sin δ * ‖ν‖ ≤ ν.re := by
  have hc : Real.cos (π / 2 - δ) ≤ Real.cos (arg ν) := by
    rw [← Real.cos_abs (arg ν)]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_pos]) h
  rw [Real.cos_pi_div_two_sub, cos_arg hν, le_div_iff₀ (norm_pos_iff.2 hν)] at hc
  exact hc

/-- `log (z/2) = log z - log 2` for `z ≠ 0`. -/
theorem struveLO_log_div_two {z : ℂ} (hz : z ≠ 0) : log (z / 2) = log z - log 2 := by
  have h := log_mul_ofReal (1 / 2) (by norm_num) z hz
  rw [show z * ((1 / 2 : ℝ) : ℂ) = z / 2 by push_cast; ring] at h
  rw [h, show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, ← ofReal_log (by norm_num), one_div,
    Real.log_inv]
  push_cast; ring

/-- The normalization in DLMF 11.6.6–11.6.7: `e^{(1-ν)(log z - log 2)} · 2 (z/2)^ν = z`. -/
theorem struveLO_normalize {z : ℂ} (hz : z ≠ 0) (ν : ℂ) :
    exp ((1 - ν) * (log z - log 2)) * (2 * (z / 2) ^ ν) = z := by
  have hz2 : z / 2 ≠ 0 := div_ne_zero hz two_ne_zero
  rw [cpow_def_of_ne_zero hz2, struveLO_log_div_two hz]
  have : exp ((1 - ν) * (log z - log 2)) * exp ((log z - log 2) * ν) = exp (log z - log 2) := by
    rw [← exp_add]; ring_nf
  rw [show exp ((1 - ν) * (log z - log 2)) * (2 * exp ((log z - log 2) * ν)) =
    2 * (exp ((1 - ν) * (log z - log 2)) * exp ((log z - log 2) * ν)) by ring, this,
    ← struveLO_log_div_two hz, exp_log hz2]
  ring

/-- `‖(a choose j)‖ ≤ (2|ν|)^j` for `a = ν - 1/2`, `j ≤ N ≤ |ν|`. -/
theorem struveLO_norm_b_le {ν : ℂ} {N j : ℕ} (hj : j ≤ N) (hN : (N : ℝ) ≤ ‖ν‖) :
    ‖struveLO_b (ν - 1 / 2) j‖ ≤ (2 * ‖ν‖) ^ j := by
  unfold struveLO_b
  rw [norm_div, norm_prod, Complex.norm_natCast]
  have h1 : (1 : ℝ) ≤ j.factorial := by exact_mod_cast j.factorial_pos
  calc (∏ i ∈ Finset.range j, ‖ν - 1 / 2 - i‖) / j.factorial ≤ ∏ i ∈ Finset.range j, ‖ν - 1 / 2 - i‖ :=
        div_le_self (Finset.prod_nonneg fun _ _ => norm_nonneg _) h1
    _ ≤ ∏ _i ∈ Finset.range j, 2 * ‖ν‖ :=
        Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i hi => by
          have hi : (i : ℝ) + 1 ≤ N := by
            have := Finset.mem_range.1 hi; exact_mod_cast (by omega : i + 1 ≤ N)
          calc ‖ν - 1 / 2 - i‖ ≤ ‖ν‖ + ‖(1 / 2 : ℂ) + i‖ := by
                rw [sub_sub]; exact norm_sub_le _ _
            _ ≤ ‖ν‖ + (1 / 2 + i) := by
                gcongr
                calc ‖(1 / 2 : ℂ) + i‖ ≤ ‖(1 / 2 : ℂ)‖ + ‖(i : ℂ)‖ := norm_add_le _ _
                  _ = 1 / 2 + i := by simp
            _ ≤ 2 * ‖ν‖ := by linarith)
    _ = (2 * ‖ν‖) ^ j := by rw [Finset.prod_const, Finset.card_range]

/-- The exponentially small tail terms are `O(|ν|^{-N})`. -/
theorem struveLO_tail_term_le {x κ L : ℝ} (hx : 1 ≤ x) (hκ : 0 < κ) (hL : 0 < L) {c : ℝ}
    (hc : 2 * κ * x ≤ c) (N j : ℕ) :
    L * x * ((2 * x) ^ j * (Real.exp (-(c / 2)) * ((2 * j).factorial * (2 / c) ^ (2 * j + 1)))) ≤
      (L * 2 ^ j * (2 * j).factorial * (1 / κ) ^ (2 * j + 1) * (N + j + 1).factorial /
        κ ^ (N + j + 1)) * x⁻¹ ^ N := by
  have hx0 : 0 < x := by linarith
  have hc0 : 0 < c := by nlinarith
  have he : Real.exp (-(c / 2)) ≤ (N + j + 1).factorial / (κ * x) ^ (N + j + 1) :=
    (Real.exp_le_exp.2 (by nlinarith)).trans (struveLO_exp_neg_le (by positivity) _)
  have h2c : 2 / c ≤ 1 / κ := by
    rw [div_le_div_iff₀ hc0 hκ]; nlinarith
  calc L * x * ((2 * x) ^ j * (Real.exp (-(c / 2)) * ((2 * j).factorial * (2 / c) ^ (2 * j + 1))))
      ≤ L * x * ((2 * x) ^ j * ((N + j + 1).factorial / (κ * x) ^ (N + j + 1) *
          ((2 * j).factorial * (1 / κ) ^ (2 * j + 1)))) := by gcongr
    _ = _ := by
        rw [mul_pow, mul_pow, inv_pow]
        have : x ^ (N + j + 1) = x * x ^ j * x ^ N := by ring
        rw [this]
        field_simp

end StruveLOScaled

/-- Asymptotic bound with the indicated comparison function: `(fun ν : ℂ => Real.sqrt π*Gamma
(ν+1/2)*exp ((1-ν)*(log (lam*ν)-log 2))*struveK ν (lam*ν)-∑ k ∈ Finset.range N,
(k.factorial:ℂ)*struveScaledCoeff (lam) k/ν^k) =O[sector (π/2-δ)] (fun ν : ℂ => ν^(-(N:ℤ)))`. -/
@[dlmf 11.6.E6]
theorem struveK_scaled_asymptotic {lam : ℝ} (hlam : 1 < lam) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π/2) (N : ℕ) :
    (fun ν : ℂ => Real.sqrt π*Gamma (ν+1/2)*exp ((1-ν)*(log (lam*ν)-log 2))*struveK ν (lam*ν)-∑ k ∈ Finset.range N, (k.factorial:ℂ)*struveScaledCoeff (lam) k/ν^k) =O[sector (π/2-δ)] (fun ν : ℂ => ν^(-(N:ℤ))) := by
  obtain ⟨B, hB⟩ := struveLO_poly_bound (lam : ℂ) N
  set s := Real.sin δ with hs_def
  have hs : 0 < s := Real.sin_pos_of_pos_of_lt_pi hδ (by linarith [Real.pi_pos])
  have hl1 : 0 < lam - 1 := by linarith
  have hl0 : 0 < lam := by linarith
  set C' : ℝ := lam * 2 ^ N * (2 * N).factorial / ((lam - 1) * s) ^ (2 * N + 1) with hC'
  set R : ℝ := max (max 1 N) ((N + 1) / s) with hR
  refine IsBigO.of_bound (B + C') ?_
  rw [DLMF.sector, eventually_inf_principal]
  filter_upwards [tendsto_comap.eventually (eventually_ge_atTop R)] with ν hνR hν
  obtain ⟨hν0, harg⟩ := hν
  have hre := struveLO_re_ge hν0 harg hδ
  have hR1 : 1 ≤ ‖ν‖ := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hνR
  have hRN : (N : ℝ) ≤ ‖ν‖ := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hνR
  have hRs : (N : ℝ) + 1 ≤ s * ‖ν‖ := by
    have h := le_trans (le_max_right _ _) hνR
    rw [div_le_iff₀ hs] at h; linarith
  have hnorm0 : 0 < ‖ν‖ := by linarith
  set z : ℂ := (lam : ℂ) * ν with hz
  set a : ℂ := ν - 1 / 2 with ha_def
  have hzre : z.re = lam * ν.re := by simp [hz]
  have hare : a.re = ν.re - 1 / 2 := by simp [ha_def]
  have ha : (N : ℝ) ≤ a.re := by rw [hare]; linarith
  have hνre : 0 < ν.re := by linarith
  have hza : a.re < z.re := by rw [hare, hzre]; nlinarith
  have hz0 : z ≠ 0 := mul_ne_zero (ofReal_ne_zero.2 hl0.ne') hν0
  have hK := struveLO_K_integral_bound N ha hza
  have hrep := DLMF.Bessel.struveK_eq_integral ν (z := z) (by rw [hzre]; positivity)
  set J := ∫ t in Ioi (0 : ℝ), exp (-z * t) * (1 + (t : ℂ) ^ 2) ^ (ν - 1 / 2) with hJ
  have hG : Gamma (ν + 1 / 2) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp; linarith)
  have hsq : (Real.sqrt π : ℂ) ≠ 0 := ofReal_ne_zero.2 (Real.sqrt_pos.2 Real.pi_pos).ne'
  have hid : Real.sqrt π * Gamma (ν + 1 / 2) * exp ((1 - ν) * (log z - log 2)) * struveK ν z =
      z * J := by
    rw [hrep]
    have hc : (Real.sqrt π : ℂ) * Gamma (ν + 1 / 2) ≠ 0 := mul_ne_zero hsq hG
    calc _ = ((Real.sqrt π : ℂ) * Gamma (ν + 1 / 2) / ((Real.sqrt π : ℂ) * Gamma (ν + 1 / 2))) *
          ((exp ((1 - ν) * (log z - log 2)) * (2 * (z / 2) ^ ν)) * J) := by ring
      _ = z * J := by rw [div_self hc, one_mul, struveLO_normalize hz0 ν]
  have hsum : z * ∑ j ∈ Finset.range N, struveLO_b a j * ((2 * j).factorial : ℂ) / z ^ (2 * j + 1) =
      ∑ j ∈ Finset.range N, struveLO_b (ν - 1/2) j * ((2 * j).factorial : ℂ) / ((lam : ℂ) * ν) ^ (2 * j) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← ha_def, ← hz, pow_succ]
    field_simp
  have hP : (∏ i ∈ Finset.range N, ‖a - i‖) ≤ (2 * ‖ν‖) ^ N := by
    calc (∏ i ∈ Finset.range N, ‖a - i‖) ≤ ∏ _i ∈ Finset.range N, 2 * ‖ν‖ :=
          Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i hi => by
            have hi : (i : ℝ) + 1 ≤ N := by exact_mod_cast Finset.mem_range.1 hi
            calc ‖a - i‖ ≤ ‖ν‖ + ‖(1 / 2 : ℂ) + i‖ := by
                  rw [ha_def, sub_sub]; exact norm_sub_le _ _
              _ ≤ ‖ν‖ + (1 / 2 + i) := by
                  gcongr
                  calc ‖(1 / 2 : ℂ) + i‖ ≤ ‖(1 / 2 : ℂ)‖ + ‖(i : ℂ)‖ := norm_add_le _ _
                    _ = 1 / 2 + i := by simp
              _ ≤ 2 * ‖ν‖ := by linarith)
      _ = (2 * ‖ν‖) ^ N := by rw [Finset.prod_const, Finset.card_range]
  have hden : (lam - 1) * s * ‖ν‖ ≤ z.re - a.re := by rw [hzre, hare]; nlinarith
  have hpos : 0 < (lam - 1) * s * ‖ν‖ := by positivity
  have hE : ‖z‖ * ‖J - ∑ j ∈ Finset.range N, struveLO_b a j * ((2 * j).factorial : ℂ) / z ^ (2 * j + 1)‖ ≤
      C' * ‖ν‖⁻¹ ^ N := by
    have hzn : ‖z‖ = lam * ‖ν‖ := by rw [hz, norm_mul, norm_real, Real.norm_of_nonneg hl0.le]
    rw [hzn]
    calc lam * ‖ν‖ * ‖J - _‖
        ≤ lam * ‖ν‖ * ((∏ i ∈ Finset.range N, ‖a - i‖) * (2 * N).factorial /
            (z.re - a.re) ^ (2 * N + 1)) := by gcongr
      _ ≤ lam * ‖ν‖ * ((2 * ‖ν‖) ^ N * (2 * N).factorial / ((lam - 1) * s * ‖ν‖) ^ (2 * N + 1)) := by
          gcongr
      _ = C' * ‖ν‖⁻¹ ^ N := by
          have hx : ‖ν‖ ^ (2 * N + 1) = ‖ν‖ * ‖ν‖ ^ N * ‖ν‖ ^ N := by ring
          have hn0 : ‖ν‖ ≠ 0 := hnorm0.ne'
          rw [hC', mul_pow ((lam - 1) * s) ‖ν‖, hx, mul_pow 2 ‖ν‖, inv_pow]
          field_simp
  rw [hid]
  have hsplit : z * J - ∑ k ∈ Finset.range N, (k.factorial : ℂ) * struveScaledCoeff lam k / ν ^ k =
      (∑ j ∈ Finset.range N, struveLO_b (ν - 1/2) j * ((2 * j).factorial : ℂ) / ((lam : ℂ) * ν) ^ (2 * j) -
        ∑ k ∈ Finset.range N, (k.factorial : ℂ) * struveScaledCoeff lam k / ν ^ k) +
      z * (J - ∑ j ∈ Finset.range N, struveLO_b a j * ((2 * j).factorial : ℂ) / z ^ (2 * j + 1)) := by
    rw [mul_sub, hsum]; ring
  rw [hsplit, norm_zpow, zpow_neg, zpow_natCast, ← inv_pow]
  calc _ ≤ ‖∑ j ∈ Finset.range N, struveLO_b (ν - 1/2) j * ((2 * j).factorial : ℂ) / ((lam : ℂ) * ν) ^ (2 * j) -
        ∑ k ∈ Finset.range N, (k.factorial : ℂ) * struveScaledCoeff lam k / ν ^ k‖ +
      ‖z‖ * ‖J - ∑ j ∈ Finset.range N, struveLO_b a j * ((2 * j).factorial : ℂ) / z ^ (2 * j + 1)‖ := by
        rw [← norm_mul]; exact norm_add_le _ _
    _ ≤ B * ‖ν‖⁻¹ ^ N + C' * ‖ν‖⁻¹ ^ N := add_le_add (hB ν hR1) hE
    _ = (B + C') * ‖ν‖⁻¹ ^ N := by ring

/-- Asymptotic bound with the indicated comparison function: `(fun ν : ℂ => -Real.sqrt π*Gamma
(ν+1/2)*exp ((1-ν)*(log (lam*ν)-log 2))*struveM ν (lam*ν)-∑ k ∈ Finset.range N,
(k.factorial:ℂ)*struveScaledCoeff (I*lam) k/ν^k) =O[sector (π/2-δ)] (fun ν : ℂ =>
ν^(-(N:ℤ)))`. -/
@[dlmf 11.6.E7]
theorem struveM_scaled_asymptotic {lam : ℝ} (hlam : 0 < lam) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π/2) (N : ℕ) :
    (fun ν : ℂ => -Real.sqrt π*Gamma (ν+1/2)*exp ((1-ν)*(log (lam*ν)-log 2))*struveM ν (lam*ν)-∑ k ∈ Finset.range N, (k.factorial:ℂ)*struveScaledCoeff (I*lam) k/ν^k) =O[sector (π/2-δ)] (fun ν : ℂ => ν^(-(N:ℤ))) := by
  obtain ⟨B, hB⟩ := struveLO_poly_bound (I * lam : ℂ) N
  set s := Real.sin δ with hs_def
  have hs : 0 < s := Real.sin_pos_of_pos_of_lt_pi hδ (by linarith [Real.pi_pos])
  set κ : ℝ := lam * s / 2 with hκ
  have hκ0 : 0 < κ := by positivity
  set C1 : ℝ := lam * 2 ^ N * (2 * N).factorial / (lam * s) ^ (2 * N + 1) with hC1
  set C2 : ℝ := ∑ j ∈ Finset.range N, (lam * 2 ^ j * (2 * j).factorial * (1 / κ) ^ (2 * j + 1) *
    (N + j + 1).factorial / κ ^ (N + j + 1)) with hC2
  set R : ℝ := max (max 1 N) ((N + 1) / s) with hR
  refine IsBigO.of_bound (B + C1 + C2) ?_
  rw [DLMF.sector, eventually_inf_principal]
  filter_upwards [tendsto_comap.eventually (eventually_ge_atTop R)] with ν hνR hν
  obtain ⟨hν0, harg⟩ := hν
  have hre := struveLO_re_ge hν0 harg hδ
  have hR1 : 1 ≤ ‖ν‖ := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hνR
  have hRN : (N : ℝ) ≤ ‖ν‖ := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hνR
  have hRs : (N : ℝ) + 1 ≤ s * ‖ν‖ := by
    have h := le_trans (le_max_right _ _) hνR
    rw [div_le_iff₀ hs] at h; linarith
  have hnorm0 : 0 < ‖ν‖ := by linarith
  set z : ℂ := (lam : ℂ) * ν with hz
  set a : ℂ := ν - 1 / 2 with ha_def
  have hzre : z.re = lam * ν.re := by simp [hz]
  have hare : a.re = ν.re - 1 / 2 := by simp [ha_def]
  have ha : (N : ℝ) ≤ a.re := by rw [hare]; linarith
  have hνre : 0 < ν.re := by linarith
  have hzpos : 0 < z.re := by rw [hzre]; positivity
  have hz0 : z ≠ 0 := mul_ne_zero (ofReal_ne_zero.2 hlam.ne') hν0
  have hK := struveLO_M_integral_bound N ha hzpos
  have hrep := struveM_integral (ν := ν) (by linarith) (z := z) (by
    rw [mem_slitPlane_iff]; left; exact hzpos)
  set J := ∫ t : ℝ in (0 : ℝ)..1, exp (-z * t) * (1 - (t : ℂ) ^ 2) ^ (ν - 1 / 2) with hJ
  have hG : Gamma (ν + 1 / 2) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp; linarith)
  have hsq : (Real.sqrt π : ℂ) ≠ 0 := ofReal_ne_zero.2 (Real.sqrt_pos.2 Real.pi_pos).ne'
  have hid : -Real.sqrt π * Gamma (ν + 1 / 2) * exp ((1 - ν) * (log z - log 2)) * struveM ν z =
      z * J := by
    rw [hrep]
    have hc : (Real.sqrt π : ℂ) * Gamma (ν + 1 / 2) ≠ 0 := mul_ne_zero hsq hG
    calc _ = ((Real.sqrt π : ℂ) * Gamma (ν + 1 / 2) / ((Real.sqrt π : ℂ) * Gamma (ν + 1 / 2))) *
          ((exp ((1 - ν) * (log z - log 2)) * (2 * (z / 2) ^ ν)) * J) := by ring
      _ = z * J := by rw [div_self hc, one_mul, struveLO_normalize hz0 ν]
  have hsum : z * ∑ j ∈ Finset.range N,
        struveLO_b a j * (-1) ^ j * ((2 * j).factorial : ℂ) / z ^ (2 * j + 1) =
      ∑ j ∈ Finset.range N, struveLO_b (ν - 1/2) j * ((2 * j).factorial : ℂ) /
        ((I * lam : ℂ) * ν) ^ (2 * j) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hI : ((I * lam : ℂ) * ν) ^ (2 * j) = (-1) ^ j * z ^ (2 * j) := by
      rw [hz, mul_pow, mul_pow, mul_pow, pow_mul I, I_sq]; ring
    have hinv : ((-1 : ℂ) ^ j)⁻¹ = (-1) ^ j := by rw [← inv_pow, inv_neg, inv_one]
    rw [← ha_def, hI, div_eq_mul_inv, div_eq_mul_inv, mul_inv, hinv, pow_succ, mul_inv]
    linear_combination (struveLO_b a j * (-1) ^ j * ((2 * j).factorial : ℂ) * (z ^ (2 * j))⁻¹) *
      (mul_inv_cancel₀ hz0)
  have hcre : lam * s * ‖ν‖ ≤ z.re := by rw [hzre]; nlinarith
  have hE : ‖z‖ * ‖J - ∑ j ∈ Finset.range N,
        struveLO_b a j * (-1) ^ j * ((2 * j).factorial : ℂ) / z ^ (2 * j + 1)‖ ≤
      (C1 + C2) * ‖ν‖⁻¹ ^ N := by
    have hzn : ‖z‖ = lam * ‖ν‖ := by rw [hz, norm_mul, norm_real, Real.norm_of_nonneg hlam.le]
    rw [hzn]
    have hP : (∏ i ∈ Finset.range N, ‖a - i‖) ≤ (2 * ‖ν‖) ^ N := by
      calc (∏ i ∈ Finset.range N, ‖a - i‖) ≤ ∏ _i ∈ Finset.range N, 2 * ‖ν‖ :=
            Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i hi => by
              have hi : (i : ℝ) + 1 ≤ N := by exact_mod_cast Finset.mem_range.1 hi
              calc ‖a - i‖ ≤ ‖ν‖ + ‖(1 / 2 : ℂ) + i‖ := by
                    rw [ha_def, sub_sub]; exact norm_sub_le _ _
                _ ≤ ‖ν‖ + (1 / 2 + i) := by
                    gcongr
                    calc ‖(1 / 2 : ℂ) + i‖ ≤ ‖(1 / 2 : ℂ)‖ + ‖(i : ℂ)‖ := norm_add_le _ _
                      _ = 1 / 2 + i := by simp
                _ ≤ 2 * ‖ν‖ := by linarith)
        _ = (2 * ‖ν‖) ^ N := by rw [Finset.prod_const, Finset.card_range]
    have hpos : 0 < lam * s * ‖ν‖ := by positivity
    have h1 : lam * ‖ν‖ * ((∏ i ∈ Finset.range N, ‖a - i‖) * (2 * N).factorial /
        z.re ^ (2 * N + 1)) ≤ C1 * ‖ν‖⁻¹ ^ N := by
      calc lam * ‖ν‖ * ((∏ i ∈ Finset.range N, ‖a - i‖) * (2 * N).factorial / z.re ^ (2 * N + 1))
          ≤ lam * ‖ν‖ * ((2 * ‖ν‖) ^ N * (2 * N).factorial / (lam * s * ‖ν‖) ^ (2 * N + 1)) := by
            gcongr
        _ = C1 * ‖ν‖⁻¹ ^ N := by
            have hx : ‖ν‖ ^ (2 * N + 1) = ‖ν‖ * ‖ν‖ ^ N * ‖ν‖ ^ N := by ring
            have hn0 : ‖ν‖ ≠ 0 := hnorm0.ne'
            rw [hC1, mul_pow (lam * s) ‖ν‖, hx, mul_pow 2 ‖ν‖, inv_pow]
            field_simp
    have h2 : lam * ‖ν‖ * ∑ j ∈ Finset.range N, ‖struveLO_b a j‖ *
        (Real.exp (-(z.re / 2)) * ((2 * j).factorial * (2 / z.re) ^ (2 * j + 1))) ≤
        C2 * ‖ν‖⁻¹ ^ N := by
      rw [Finset.mul_sum, hC2, Finset.sum_mul]
      refine Finset.sum_le_sum fun j hj => ?_
      have hb := struveLO_norm_b_le (ν := ν) (j := j) (le_of_lt (Finset.mem_range.1 hj)) hRN
      calc lam * ‖ν‖ * (‖struveLO_b a j‖ *
            (Real.exp (-(z.re / 2)) * ((2 * j).factorial * (2 / z.re) ^ (2 * j + 1))))
          ≤ lam * ‖ν‖ * ((2 * ‖ν‖) ^ j *
            (Real.exp (-(z.re / 2)) * ((2 * j).factorial * (2 / z.re) ^ (2 * j + 1)))) := by
            gcongr
        _ ≤ _ := struveLO_tail_term_le hR1 hκ0 hlam (by rw [hκ]; linarith) N j
    calc lam * ‖ν‖ * ‖J - _‖ ≤ lam * ‖ν‖ * ((∏ i ∈ Finset.range N, ‖a - i‖) * (2 * N).factorial /
          z.re ^ (2 * N + 1) + ∑ j ∈ Finset.range N, ‖struveLO_b a j‖ *
          (Real.exp (-(z.re / 2)) * ((2 * j).factorial * (2 / z.re) ^ (2 * j + 1)))) := by gcongr
      _ ≤ C1 * ‖ν‖⁻¹ ^ N + C2 * ‖ν‖⁻¹ ^ N := by rw [mul_add]; exact add_le_add h1 h2
      _ = (C1 + C2) * ‖ν‖⁻¹ ^ N := by ring
  rw [hid]
  have hsplit : z * J - ∑ k ∈ Finset.range N, (k.factorial : ℂ) * struveScaledCoeff (I * lam) k / ν ^ k =
      (∑ j ∈ Finset.range N, struveLO_b (ν - 1/2) j * ((2 * j).factorial : ℂ) / ((I * lam : ℂ) * ν) ^ (2 * j) -
        ∑ k ∈ Finset.range N, (k.factorial : ℂ) * struveScaledCoeff (I * lam) k / ν ^ k) +
      z * (J - ∑ j ∈ Finset.range N,
        struveLO_b a j * (-1) ^ j * ((2 * j).factorial : ℂ) / z ^ (2 * j + 1)) := by
    rw [mul_sub, hsum]; ring
  rw [hsplit, norm_zpow, zpow_neg, zpow_natCast, ← inv_pow]
  calc _ ≤ _ + _ := norm_add_le _ _
    _ ≤ B * ‖ν‖⁻¹ ^ N + (C1 + C2) * ‖ν‖⁻¹ ^ N := add_le_add (hB ν hR1) (by rw [norm_mul]; exact hE)
    _ = (B + C1 + C2) * ‖ν‖⁻¹ ^ N := by ring

/-- Identity under the stated parameter and domain assumptions: `struveScaledCoeff lam 0=1 ∧
struveScaledCoeff lam 1=2/(lam:ℂ)^2 ∧ struveScaledCoeff lam 2=6/(lam:ℂ)^4-1/(2*(lam:ℂ)^2) ∧
struveScaledCoeff lam 3=20/(lam:ℂ)^6-4/(lam:ℂ)^4 ∧ struveScaledCoeff lam
4=70/(lam:ℂ)^8-45/(2*(lam:ℂ)^6)+3/(8*(lam:ℂ)^4)`. -/
@[dlmf 11.6.E8]
theorem struveScaledCoeff_initial (lam : ℂ) (hlam : lam ≠ 0) :
    struveScaledCoeff lam 0=1 ∧ struveScaledCoeff lam 1=2/(lam:ℂ)^2 ∧ struveScaledCoeff lam 2=6/(lam:ℂ)^4-1/(2*(lam:ℂ)^2) ∧ struveScaledCoeff lam 3=20/(lam:ℂ)^6-4/(lam:ℂ)^4 ∧ struveScaledCoeff lam 4=70/(lam:ℂ)^8-45/(2*(lam:ℂ)^6)+3/(8*(lam:ℂ)^4) := by
  simp only [struveScaledCoeff, Finset.sum_range_succ, Finset.prod_range_succ,
    Finset.sum_range_zero, Finset.prod_range_zero, one_mul]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [Nat.factorial, Polynomial.coeff_mul_X_sub_C, Polynomial.coeff_one,
      Polynomial.mul_coeff_zero, Polynomial.coeff_X] <;>
    field_simp <;> ring

/-- Identity under the stated parameter and domain assumptions: `(fun ν : ℂ => struveL ν (lam*ν))
~[sector (π/2-δ)] (fun ν => besselI ν (lam*ν))`. -/
@[dlmf 11.6.E9]
theorem struveL_scaled_equiv {lam : ℝ} (hlam : 0 < lam) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π/2) :
    (fun ν : ℂ => struveL ν (lam*ν)) ~[sector (π/2-δ)] (fun ν => besselI ν (lam*ν)) := by
  sorry

end DLMF.Struve
end
