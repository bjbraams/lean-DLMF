/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Airy.ModulusPhase.Representations

/-!
# Nicholson representations for Airy moduli

Nicholson integral formulas and remainder estimates for the Airy modulus and derivative modulus.

Source references and common attribution are retained in
`DLMF.Airy.ModulusPhase`.
-/

@[expose] public noncomputable section

open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF.Confluent

open scoped Real Topology

namespace DLMF.Airy

/-! ### Nicholson's formula on the real line and its consequences -/

section Nicholson

open scoped Nat

/-- The real Nicholson kernel `e^{xt} e^{-t³/12} t^{-1/2}`. -/
noncomputable def airyMod_kernel (x t : ℝ) : ℝ :=
  Real.exp (x * t) * (Real.exp (-(t ^ 3 / 12)) * t ^ (-(1 / 2) : ℝ))

/-- The real Nicholson kernel is positive on `(0, ∞)`. -/
theorem airyMod_kernel_pos (x : ℝ) {t : ℝ} (ht : 0 < t) : 0 < airyMod_kernel x t := by
  unfold airyMod_kernel; positivity

/-- **Nicholson's formula on the real line** (DLMF 9.11.4):
`M(x)² = π^{-3/2} ∫₀^∞ e^{xt - t³/12} t^{-1/2} dt`. -/
theorem airyMod_sq_eq_integral (x : ℝ) :
    airyModulus x ^ 2 = (∫ t in Ioi (0 : ℝ), airyMod_kernel x t) / (π * Real.sqrt π) := by
  have h := (airyMod_modulus_sq_exp_integral x).2
  rw [airyAi_ofReal_eq, airyBi_ofReal_eq, airyMod_pi_cpow] at h
  have hI : (∫ t : ℝ in Ioi 0, exp ((x : ℂ) * t - (t : ℂ) ^ 3 / 12) * (t : ℂ) ^ (-1 / 2 : ℂ)) =
      ((∫ t in Ioi (0 : ℝ), airyMod_kernel x t : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) => ?_
    simp only [airyMod_kernel]
    rw [ofReal_mul, ofReal_mul, ofReal_exp, ofReal_exp, ofReal_cpow ht.le]
    push_cast
    rw [sub_eq_add_neg, Complex.exp_add, show (-(1 / 2) : ℂ) = -1 / 2 by ring]; ring
  rw [hI] at h
  rw [airyModulus_sq]
  exact_mod_cast h

/-- The real Nicholson kernel is integrable on `(0, ∞)`. -/
theorem airyMod_kernel_integrable (x : ℝ) : IntegrableOn (airyMod_kernel x) (Ioi 0) :=
  airyMod_integrableOn_exp x

/-- A function positive on `(0, ∞)` and integrable there has positive integral. -/
theorem airyMod_integral_pos {f : ℝ → ℝ} (hf : IntegrableOn f (Ioi 0))
    (hpos : ∀ t, 0 < t → 0 < f t) : 0 < ∫ t in Ioi (0 : ℝ), f t := by
  refine (setIntegral_pos_iff_support_of_nonneg_ae ?_ hf).2 ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t)
    exact (hpos t ht).le
  · have : Ioi (0 : ℝ) ⊆ Function.support f ∩ Ioi 0 := fun t (ht : 0 < t) =>
      ⟨(hpos t ht).ne', ht⟩
    refine lt_of_lt_of_le ?_ (measure_mono this)
    rw [Real.volume_Ioi]; exact ENNReal.zero_lt_top

/-- `M²` is strictly increasing on the whole real line. -/
theorem airyMod_sq_strictMono : StrictMono fun x => airyModulus x ^ 2 := by
  intro x y hxy
  simp only [airyMod_sq_eq_integral]
  have hπ : 0 < π * Real.sqrt π := by positivity
  refine div_lt_div_of_pos_right ?_ hπ
  rw [← sub_pos, ← integral_sub (airyMod_kernel_integrable y) (airyMod_kernel_integrable x)]
  refine airyMod_integral_pos ((airyMod_kernel_integrable y).sub (airyMod_kernel_integrable x))
    fun t ht => ?_
  simp only [airyMod_kernel]
  have h1 : Real.exp (x * t) < Real.exp (y * t) := Real.exp_lt_exp.2 (by nlinarith)
  have h2 : 0 < Real.exp (-(t ^ 3 / 12)) * t ^ (-(1 / 2) : ℝ) := by positivity
  nlinarith

/-- Scaling form of Nicholson's formula: for `s > 0`,
`s^{1/2} M(-s)² = π^{-3/2} ∫₀^∞ e^{-u} e^{-u³/(12 s³)} u^{-1/2} du`. -/
theorem airyMod_sqrt_mul_sq {s : ℝ} (hs : 0 < s) :
    s ^ (1 / 2 : ℝ) * airyModulus (-s) ^ 2 = (∫ u in Ioi (0 : ℝ),
      Real.exp (-u) * (Real.exp (-(u ^ 3 / (12 * s ^ 3))) * u ^ (-(1 / 2) : ℝ))) /
        (π * Real.sqrt π) := by
  rw [airyMod_sq_eq_integral, mul_div_assoc']
  congr 1
  have h := integral_comp_mul_left_Ioi (airyMod_kernel (-s)) 0 (inv_pos.mpr hs)
  rw [mul_zero, smul_eq_mul, inv_inv] at h
  have hs12 : 0 < s ^ (1 / 2 : ℝ) := by positivity
  have key : ∀ u ∈ Ioi (0 : ℝ), airyMod_kernel (-s) (s⁻¹ * u) = s ^ (1 / 2 : ℝ) *
      (Real.exp (-u) * (Real.exp (-(u ^ 3 / (12 * s ^ 3))) * u ^ (-(1 / 2) : ℝ))) := by
    intro u (hu : 0 < u)
    simp only [airyMod_kernel]
    rw [Real.mul_rpow (inv_pos.mpr hs).le hu.le, Real.inv_rpow hs.le, Real.rpow_neg hs.le,
      inv_inv]
    have : -s * (s⁻¹ * u) = -u := by field_simp
    rw [this, mul_pow, inv_pow]
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioi key, integral_const_mul] at h
  have hs0 : s ^ (1 / 2 : ℝ) * s ^ (1 / 2 : ℝ) = s := by
    rw [← Real.rpow_add hs]; norm_num
  apply mul_left_cancel₀ hs12.ne'
  rw [← mul_assoc, hs0, h]

/-- The scaled Nicholson integrand is integrable. -/
theorem airyMod_scaled_integrable {s : ℝ} (hs : 0 ≤ s) : IntegrableOn (fun u : ℝ =>
    Real.exp (-u) * (Real.exp (-(u ^ 3 / (12 * s ^ 3))) * u ^ (-(1 / 2) : ℝ))) (Ioi 0) := by
  have hint := Real.GammaIntegral_convergent (s := 1 / 2) (by norm_num)
  refine hint.mono' ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable (fun t ht => ?_) measurableSet_Ioi
    exact ((Real.continuous_exp.comp continuous_neg).continuousAt.mul
      ((Real.continuous_exp.comp (by fun_prop)).continuousAt.mul
        (Real.continuousAt_rpow_const _ _ (Or.inl (ne_of_gt ht))))).continuousWithinAt
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t)
    rw [Real.norm_of_nonneg (by positivity), show (1 / 2 : ℝ) - 1 = -(1 / 2) by norm_num]
    have : Real.exp (-(t ^ 3 / (12 * s ^ 3))) ≤ 1 := Real.exp_le_one_iff.mpr
      (neg_nonpos.mpr (by positivity))
    have h0 : 0 ≤ t ^ (-(1 / 2) : ℝ) := by positivity
    have h1 : 0 < Real.exp (-t) := Real.exp_pos _
    calc Real.exp (-t) * (Real.exp (-(t ^ 3 / (12 * s ^ 3))) * t ^ (-(1 / 2) : ℝ))
        ≤ Real.exp (-t) * (1 * t ^ (-(1 / 2) : ℝ)) := by gcongr
      _ = _ := by ring

/-- The remainder of the exponential series for `e^{-w}` after `K` terms. -/
noncomputable def airyMod_rem (K : ℕ) (w : ℝ) : ℝ :=
  Real.exp (-w) - ∑ k ∈ Finset.range K, (-w) ^ k / k !

/-- Derivative of the partial sums of `e^{-w}`. -/
theorem airyMod_hasDerivAt_partial (K : ℕ) (w : ℝ) :
    HasDerivAt (fun w : ℝ => ∑ k ∈ Finset.range (K + 1), (-w) ^ k / k !)
      (-∑ k ∈ Finset.range K, (-w) ^ k / k !) w := by
  induction K with
  | zero => simpa using hasDerivAt_const w (1 : ℝ)
  | succ K ih =>
    have h := ih.add (((hasDerivAt_neg w).pow (K + 1)).div_const ((K + 1) ! : ℝ))
    simp only [Finset.sum_range_succ] at h ⊢
    convert h using 1
    simp only [Nat.add_sub_cancel, Nat.factorial_succ]
    push_cast
    field_simp
    ring

/-- Derivative of the exponential remainder: `R_{K+1}' = -R_K`. -/
theorem airyMod_hasDerivAt_rem (K : ℕ) (w : ℝ) :
    HasDerivAt (airyMod_rem (K + 1)) (-airyMod_rem K w) w := by
  have h := ((Real.hasDerivAt_exp (-w)).comp w (hasDerivAt_neg w)).sub
    (airyMod_hasDerivAt_partial K w)
  unfold airyMod_rem
  exact h.congr_deriv (by ring)

/-- `R_{K+1}(0) = 0`. -/
theorem airyMod_rem_zero (K : ℕ) : airyMod_rem (K + 1) 0 = 0 := by
  simp [airyMod_rem, Finset.sum_range_succ']

/-- The alternating bound for the exponential remainder: for `w ≥ 0`,
`0 ≤ (-1)^K R_K(w) ≤ w^K / K!`. -/
theorem airyMod_rem_bounds (K : ℕ) {w : ℝ} (hw : 0 ≤ w) :
    0 ≤ (-1) ^ K * airyMod_rem K w ∧ (-1) ^ K * airyMod_rem K w ≤ w ^ K / K ! := by
  induction K generalizing w with
  | zero =>
    simp only [pow_zero, one_mul, airyMod_rem, Finset.range_zero, Finset.sum_empty, sub_zero,
      Nat.factorial_zero, Nat.cast_one, div_one]
    exact ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr (by linarith)⟩
  | succ K ih =>
    have hg : ∀ v : ℝ, HasDerivAt (fun v => (-1) ^ (K + 1) * airyMod_rem (K + 1) v)
        ((-1) ^ K * airyMod_rem K v) v := fun v => by
      convert (airyMod_hasDerivAt_rem K v).const_mul ((-1 : ℝ) ^ (K + 1)) using 1; ring
    have hh : ∀ v : ℝ, HasDerivAt (fun v => v ^ (K + 1) / (Nat.factorial (K + 1) : ℝ) -
        (-1) ^ (K + 1) * airyMod_rem (K + 1) v) (v ^ K / (Nat.factorial K : ℝ) - (-1) ^ K * airyMod_rem K v) v :=
      fun v => by
        convert ((hasDerivAt_pow (K + 1) v).div_const (Nat.factorial (K + 1) : ℝ)).sub (hg v)
          using 1
        rw [Nat.factorial_succ]; push_cast; field_simp
    have mono : ∀ {f f' : ℝ → ℝ}, (∀ v, HasDerivAt f (f' v) v) → (∀ v, 0 ≤ v → 0 ≤ f' v) →
        f 0 ≤ f w := by
      intro f f' hf hf'
      have hm : MonotoneOn f (Ici 0) := by
        refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
          (fun v _ => (hf v).continuousAt.continuousWithinAt)
          (fun v _ => (hf v).hasDerivWithinAt) ?_
        intro v hv
        rw [interior_Ici] at hv
        exact hf' v (le_of_lt hv)
      exact hm (Set.self_mem_Ici) hw hw
    constructor
    · have := mono hg (fun v hv => (ih hv).1)
      simpa [airyMod_rem_zero] using this
    · have := mono hh (fun v hv => sub_nonneg.mpr (ih hv).2)
      simp only [airyMod_rem_zero, mul_zero, sub_zero, ne_eq, Nat.add_eq_zero_iff, one_ne_zero,
        and_false, not_false_eq_true, zero_pow, zero_div] at this
      linarith

/-- `Γ(m + 1/2) = √π ∏_{j<m} (2j+1) / 2^m`. -/
theorem airyMod_gamma_half (m : ℕ) :
    Real.Gamma (m + 1 / 2) = Real.sqrt π * (∏ j ∈ Finset.range m, (2 * (j : ℝ) + 1)) / 2 ^ m := by
  induction m with
  | zero => simpa using Real.Gamma_one_half_eq
  | succ m ih =>
    rw [show ((m + 1 : ℕ) : ℝ) + 1 / 2 = (m + 1 / 2) + 1 by push_cast; ring,
      Real.Gamma_add_one (by positivity), ih, Finset.prod_range_succ, pow_succ]
    field_simp

/-- The moment terms of the expansion of `M²` at `-∞`. -/
theorem airyMod_term_identity (k : ℕ) {s : ℝ} (hs : 0 < s) :
    (π * Real.sqrt π)⁻¹ * (Real.Gamma ((3 * k : ℕ) + 1 / 2) * s ^ (-(((3 * k : ℕ) : ℝ) + 1 / 2)) *
      ((-1) ^ k / (12 ^ k * k !))) =
      s ^ (-1 / 2 : ℝ) / π * airyModulusCoeff k * (-s) ^ (-(3 * k : ℤ)) := by
  have hπ := Real.pi_pos
  have hsp : 0 < Real.sqrt π := Real.sqrt_pos.mpr hπ
  rw [airyMod_gamma_half, airyModulusCoeff, Real.rpow_neg hs.le, Real.rpow_add hs,
    Real.rpow_natCast, zpow_neg, show (3 * (k : ℤ)) = ((3 * k : ℕ) : ℤ) by push_cast; ring,
    zpow_natCast, neg_pow s, show (-1 : ℝ) ^ (3 * k) = (-1) ^ k by
      rw [pow_mul]; norm_num,
    show (-1 / 2 : ℝ) = -(1 / 2) by ring, Real.rpow_neg hs.le]
  have h1 : (0 : ℝ) < s ^ (1 / 2 : ℝ) := by positivity
  have h3 : (96 : ℝ) ^ k = 2 ^ (3 * k) * 12 ^ k := by rw [pow_mul, ← mul_pow]; norm_num
  rw [h3]
  field_simp
  rw [← pow_mul, pow_mul]
  norm_num
  exact neg_one_pow_eq_or ℝ k

/-- The terms `e^{-st} t^{3k-1/2}` integrate to `Γ(3k+1/2) s^{-(3k+1/2)}`. -/
theorem airyMod_term_integral (k : ℕ) {s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun t : ℝ => Real.exp (-s * t) * t ^ ((((3 * k : ℕ) : ℝ) + 1 / 2) - 1)) (Ioi 0) ∧
    ∫ t in Ioi (0 : ℝ), Real.exp (-s * t) * t ^ ((((3 * k : ℕ) : ℝ) + 1 / 2) - 1) =
      Real.Gamma ((3 * k : ℕ) + 1 / 2) * s ^ (-(((3 * k : ℕ) : ℝ) + 1 / 2)) :=
  ⟨integrableOn_exp_neg_mul_mul_rpow_sub_one (by positivity) hs,
    integral_exp_neg_mul_mul_rpow_sub_one (by positivity) hs⟩

/-- The error of the truncated expansion of `M²` at `-∞` as an integral of the exponential
remainder: for `s > 0`, `M(-s)² - (s^{-1/2}/π) ∑_{k<N} c_k (-s)^{-3k} =
π^{-3/2} ∫₀^∞ e^{-st} t^{-1/2} R_N(t³/12) dt`. -/
theorem airyMod_sq_error_integral {s : ℝ} (hs : 0 < s) (N : ℕ) :
    IntegrableOn (fun t : ℝ => Real.exp (-s * t) * t ^ (-(1 / 2) : ℝ) * airyMod_rem N (t ^ 3 / 12))
      (Ioi 0) ∧
    airyModulus (-s) ^ 2 - s ^ (-1 / 2 : ℝ) / π * airyModulusSum false N (-s) =
      (π * Real.sqrt π)⁻¹ * ∫ t in Ioi (0 : ℝ),
        Real.exp (-s * t) * t ^ (-(1 / 2) : ℝ) * airyMod_rem N (t ^ 3 / 12) := by
  set B : ℕ → ℝ → ℝ := fun k t => Real.exp (-s * t) * t ^ ((((3 * k : ℕ) : ℝ) + 1 / 2) - 1) *
    ((-1) ^ k / (12 ^ k * k !))
  have hB : ∀ k, IntegrableOn (B k) (Ioi 0) := fun k => (airyMod_term_integral k hs).1.mul_const _
  have hBi : ∀ k, ∫ t in Ioi (0 : ℝ), B k t =
      Real.Gamma ((3 * k : ℕ) + 1 / 2) * s ^ (-(((3 * k : ℕ) : ℝ) + 1 / 2)) *
        ((-1) ^ k / (12 ^ k * k !)) := fun k => by
    rw [integral_mul_const, (airyMod_term_integral k hs).2]
  have hpt : ∀ t : ℝ, 0 < t → airyMod_kernel (-s) t =
      Real.exp (-s * t) * t ^ (-(1 / 2) : ℝ) * airyMod_rem N (t ^ 3 / 12) +
        ∑ k ∈ Finset.range N, B k t := by
    intro t ht
    simp only [airyMod_kernel, airyMod_rem, B]
    have : ∀ k ∈ Finset.range N, Real.exp (-s * t) * t ^ (-(1 / 2) : ℝ) *
        ((-(t ^ 3 / 12)) ^ k / k !) = Real.exp (-s * t) * t ^ ((((3 * k : ℕ) : ℝ) + 1 / 2) - 1) *
          ((-1) ^ k / (12 ^ k * k !)) := by
      intro k _
      rw [show (((3 * k : ℕ) : ℝ) + 1 / 2) - 1 = ((3 * k : ℕ) : ℝ) + (-(1 / 2)) by ring,
        Real.rpow_add ht, Real.rpow_natCast, neg_pow, div_pow, pow_mul]
      field_simp
    rw [← Finset.sum_congr rfl this, ← Finset.mul_sum]
    ring
  have hA : IntegrableOn (fun t : ℝ => Real.exp (-s * t) * t ^ (-(1 / 2) : ℝ) *
      airyMod_rem N (t ^ 3 / 12)) (Ioi 0) := by
    refine ((airyMod_kernel_integrable (-s)).sub (integrable_finsetSum (Finset.range N) fun k _ => hB k)).congr_fun
      (fun t (ht : 0 < t) => ?_) measurableSet_Ioi
    simp only [Pi.sub_apply, hpt t ht]
    ring
  refine ⟨hA, ?_⟩
  rw [airyMod_sq_eq_integral, setIntegral_congr_fun measurableSet_Ioi hpt,
    integral_add hA (integrable_finsetSum (Finset.range N) fun k _ => hB k), integral_finsetSum (Finset.range N) fun k _ => hB k]
  simp only [hBi, airyModulusSum, Bool.false_eq_true, ite_false]
  rw [Finset.mul_sum, div_eq_inv_mul, mul_add, Finset.mul_sum]
  have : ∀ k ∈ Finset.range N, (π * Real.sqrt π)⁻¹ * (Real.Gamma ((3 * k : ℕ) + 1 / 2) *
      s ^ (-(((3 * k : ℕ) : ℝ) + 1 / 2)) * ((-1) ^ k / (12 ^ k * k !))) =
      s ^ (-1 / 2 : ℝ) / π * (airyModulusCoeff k * (-s) ^ (-(3 * k : ℤ))) := by
    intro k _; rw [airyMod_term_identity k hs]; ring
  rw [Finset.sum_congr rfl this]
  ring

/-- Signed first-neglected-term bound for the expansion of `M²` at `-∞` (DLMF §9.8(iv)). -/
theorem airyMod_sq_error_bound {x : ℝ} (hx : x < 0) (N : ℕ) :
    |(airyModulus x ^ 2) - ((-x) ^ (-1 / 2 : ℝ) / π) * airyModulusSum false N x| ≤ |((-x) ^ (-1 / 2 : ℝ) / π) * airyModulusCoeff N * x ^ (-(3 * N : ℤ))| ∧
      0 ≤ ((airyModulus x ^ 2) - ((-x) ^ (-1 / 2 : ℝ) / π) * airyModulusSum false N x) * (((-x) ^ (-1 / 2 : ℝ) / π) * airyModulusCoeff N * x ^ (-(3 * N : ℤ))) := by
  obtain ⟨s, hs, rfl⟩ : ∃ s : ℝ, 0 < s ∧ x = -s := ⟨-x, by linarith, by ring⟩
  rw [neg_neg]
  have hπ := Real.pi_pos
  have hc : 0 < (π * Real.sqrt π)⁻¹ := by positivity
  obtain ⟨hA, hE⟩ := airyMod_sq_error_integral hs N
  rw [hE, ← airyMod_term_identity N hs]
  set J := ∫ t in Ioi (0 : ℝ), Real.exp (-s * t) * t ^ (-(1 / 2) : ℝ) * airyMod_rem N (t ^ 3 / 12)
  set G := Real.Gamma ((3 * N : ℕ) + 1 / 2) * s ^ (-(((3 * N : ℕ) : ℝ) + 1 / 2))
  have hJ1 : 0 ≤ (-1) ^ N * J := by
    rw [← integral_const_mul]
    refine setIntegral_nonneg measurableSet_Ioi fun t (ht : 0 < t) => ?_
    have := (airyMod_rem_bounds N (w := t ^ 3 / 12) (by positivity)).1
    have : 0 ≤ Real.exp (-s * t) * t ^ (-(1 / 2) : ℝ) := by positivity
    nlinarith
  have hJ2 : (-1) ^ N * J ≤ G / (12 ^ N * N !) := by
    have hI := (airyMod_term_integral N hs)
    rw [show G / (12 ^ N * N !) = ∫ t in Ioi (0 : ℝ), Real.exp (-s * t) *
        t ^ ((((3 * N : ℕ) : ℝ) + 1 / 2) - 1) / (12 ^ N * N !) by
      rw [integral_div, hI.2], ← integral_const_mul]
    refine setIntegral_mono_on (hA.const_mul _) (hI.1.div_const _) measurableSet_Ioi
      fun t (ht : 0 < t) => ?_
    have hb := (airyMod_rem_bounds N (w := t ^ 3 / 12) (by positivity)).2
    have h0 : 0 ≤ Real.exp (-s * t) * t ^ (-(1 / 2) : ℝ) := by positivity
    have e : Real.exp (-s * t) * t ^ ((((3 * N : ℕ) : ℝ) + 1 / 2) - 1) / (12 ^ N * N !) =
        Real.exp (-s * t) * t ^ (-(1 / 2) : ℝ) * ((t ^ 3 / 12) ^ N / N !) := by
      rw [show (((3 * N : ℕ) : ℝ) + 1 / 2) - 1 = ((3 * N : ℕ) : ℝ) + (-(1 / 2)) by ring,
        Real.rpow_add ht, Real.rpow_natCast, div_pow, pow_mul]
      field_simp
    rw [e]
    calc (-1) ^ N * (Real.exp (-s * t) * t ^ (-(1 / 2) : ℝ) * airyMod_rem N (t ^ 3 / 12))
        = Real.exp (-s * t) * t ^ (-(1 / 2) : ℝ) * ((-1) ^ N * airyMod_rem N (t ^ 3 / 12)) := by
          ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hb h0
  have hsq : ((-1 : ℝ) ^ N) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hab : |(-1 : ℝ) ^ N| = 1 := by simp
  have hG : 0 ≤ G / (12 ^ N * N !) := hJ1.trans hJ2
  constructor
  · rw [show (π * Real.sqrt π)⁻¹ * J = (-1) ^ N * ((π * Real.sqrt π)⁻¹ * ((-1) ^ N * J)) by
      rw [← mul_assoc ((-1 : ℝ) ^ N), mul_comm ((-1 : ℝ) ^ N), mul_assoc, ← mul_assoc ((-1 : ℝ) ^ N),
        ← pow_two, hsq, one_mul],
      show (π * Real.sqrt π)⁻¹ * (G * ((-1) ^ N / (12 ^ N * N !))) =
        (-1) ^ N * ((π * Real.sqrt π)⁻¹ * (G / (12 ^ N * N !))) by ring,
      abs_mul ((-1 : ℝ) ^ N), abs_mul ((-1 : ℝ) ^ N), hab, one_mul, one_mul,
      abs_of_nonneg (mul_nonneg hc.le hJ1), abs_of_nonneg (mul_nonneg hc.le hG)]
    exact mul_le_mul_of_nonneg_left hJ2 hc.le
  · have : (π * Real.sqrt π)⁻¹ * J * ((π * Real.sqrt π)⁻¹ * (G * ((-1) ^ N / (12 ^ N * N !)))) =
        ((π * Real.sqrt π)⁻¹ * ((-1) ^ N * J)) * ((π * Real.sqrt π)⁻¹ * (G / (12 ^ N * N !))) := by
      ring
    rw [this]
    exact mul_nonneg (mul_nonneg hc.le hJ1) (mul_nonneg hc.le hG)

/-- The second Nicholson kernel `e^{xt} e^{-t³/12} t^{3/2}`. -/
noncomputable def airyMod_kernel2 (x t : ℝ) : ℝ :=
  Real.exp (x * t) * (Real.exp (-(t ^ 3 / 12)) * (t ^ 2 * t ^ (-(1 / 2) : ℝ)))

/-- The second Nicholson kernel is integrable on `(0, ∞)`. -/
theorem airyMod_kernel2_integrable (x : ℝ) : IntegrableOn (airyMod_kernel2 x) (Ioi 0) :=
  airyMod_integrableOn_exp_pow x 2

/-- **Nicholson-type formula for `N²`** on the real line:
`N(x)² = π^{-3/2} (½ ∫₀^∞ e^{xt - t³/12} t^{3/2} dt - x ∫₀^∞ e^{xt - t³/12} t^{-1/2} dt)`. -/
theorem airyMod_derivSq_eq_integral (x : ℝ) :
    airyDerivModulus x ^ 2 = ((∫ t in Ioi (0 : ℝ), airyMod_kernel2 x t) / 2 -
      x * ∫ t in Ioi (0 : ℝ), airyMod_kernel x t) / (π * Real.sqrt π) := by
  have h := airyMod_derivModulus_sq_integral x
  rw [airyAiDeriv_ofReal_eq, airyBiDeriv_ofReal_eq, airyMod_pi_cpow] at h
  have hc : ∀ t : ℝ, 0 < t → ((t : ℂ) ^ (-1 / 2 : ℂ)) = ((t ^ (-(1 / 2) : ℝ) : ℝ) : ℂ) := by
    intro t ht; rw [ofReal_cpow ht.le]; push_cast; ring_nf
  have hI : (∫ t : ℝ in Ioi 0, exp ((x : ℂ) * t - (t : ℂ) ^ 3 / 12) * (t : ℂ) ^ (-1 / 2 : ℂ)) =
      ((∫ t in Ioi (0 : ℝ), airyMod_kernel x t : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) => ?_
    simp only [airyMod_kernel]
    rw [hc t ht]; push_cast
    rw [sub_eq_add_neg, Complex.exp_add]; ring
  have hI2 : (∫ t : ℝ in Ioi 0, exp ((x : ℂ) * t - (t : ℂ) ^ 3 / 12) *
      ((t : ℂ) ^ 2 * (t : ℂ) ^ (-1 / 2 : ℂ))) = ((∫ t in Ioi (0 : ℝ), airyMod_kernel2 x t : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) => ?_
    simp only [airyMod_kernel2]
    rw [hc t ht]; push_cast
    rw [sub_eq_add_neg, Complex.exp_add]; ring
  rw [hI, hI2] at h
  rw [airyDerivModulus_sq]
  have h' : ((airyAiDerivReal x ^ 2 + airyBiDerivReal x ^ 2 : ℝ) : ℂ) =
      ((((∫ t in Ioi (0 : ℝ), airyMod_kernel2 x t) / 2 - x * ∫ t in Ioi (0 : ℝ), airyMod_kernel x t) /
        (π * Real.sqrt π) : ℝ) : ℂ) := by
    push_cast; rw [h]; push_cast; ring
  exact_mod_cast h'

/-- Strict monotonicity of Laplace-type integrals `∫₀^∞ e^{xt} w(t) dt` in `x` for a positive
weight `w`. -/
theorem airyMod_integral_exp_strictMono {w : ℝ → ℝ} (hw : ∀ t, 0 < t → 0 < w t)
    (hint : ∀ a : ℝ, IntegrableOn (fun t => Real.exp (a * t) * w t) (Ioi 0)) {x y : ℝ}
    (hxy : x < y) :
    ∫ t in Ioi (0 : ℝ), Real.exp (x * t) * w t < ∫ t in Ioi (0 : ℝ), Real.exp (y * t) * w t := by
  rw [← sub_pos, ← integral_sub (hint y) (hint x)]
  refine airyMod_integral_pos ((hint y).sub (hint x)) fun t ht => ?_
  have h1 : Real.exp (x * t) < Real.exp (y * t) := Real.exp_lt_exp.2 (by nlinarith)
  have := hw t ht
  nlinarith

/-- The moment terms `e^{-st} t^{m-1/2}` integrate to `Γ(m+1/2) s^{-(m+1/2)}`. -/
theorem airyMod_mom_integral (m : ℕ) {s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun t : ℝ => Real.exp (-s * t) * t ^ (((m : ℝ) + 1 / 2) - 1)) (Ioi 0) ∧
    ∫ t in Ioi (0 : ℝ), Real.exp (-s * t) * t ^ (((m : ℝ) + 1 / 2) - 1) =
      Real.Gamma (m + 1 / 2) * s ^ (-((m : ℝ) + 1 / 2)) :=
  ⟨integrableOn_exp_neg_mul_mul_rpow_sub_one (by positivity) hs,
    integral_exp_neg_mul_mul_rpow_sub_one (by positivity) hs⟩

/-- The moment terms of the expansion of `N²` at `-∞` coming from `∫ e^{-st} t^{3/2} e^{-t³/12}`. -/
theorem airyMod_deriv_term_identity (j : ℕ) {s : ℝ} (hs : 0 < s) :
    (π * Real.sqrt π)⁻¹ / 2 * (Real.Gamma ((3 * j + 2 : ℕ) + 1 / 2) *
      s ^ (-(((3 * j + 2 : ℕ) : ℝ) + 1 / 2)) * ((-1) ^ j / (12 ^ j * j !))) =
      s ^ (1 / 2 : ℝ) / π * (-s) ^ (-(3 * (j + 1 : ℕ) : ℤ)) *
        (airyDerivModulusCoeff (j + 1) - airyModulusCoeff (j + 1)) := by
  have hπ := Real.pi_pos
  have hsp : 0 < Real.sqrt π := Real.sqrt_pos.mpr hπ
  have hP : ∏ i ∈ Finset.range (3 * (j + 1)), (2 * (i : ℝ) + 1) =
      (∏ i ∈ Finset.range (3 * j + 2), (2 * (i : ℝ) + 1)) * (6 * j + 5) := by
    rw [show 3 * (j + 1) = (3 * j + 2) + 1 by ring, Finset.prod_range_succ]; push_cast; ring
  rw [airyDerivModulusCoeff, airyModulusCoeff, hP, airyMod_gamma_half (3 * j + 2)]
  generalize ∏ i ∈ Finset.range (3 * j + 2), (2 * (i : ℝ) + 1) = P
  rw [Real.rpow_neg hs.le, Real.rpow_add hs, Real.rpow_natCast, zpow_neg,
    show (3 * ((j + 1 : ℕ) : ℤ)) = ((3 * j + 3 : ℕ) : ℤ) by push_cast; ring, zpow_natCast,
    neg_pow s, show (-1 : ℝ) ^ (3 * j + 3) = -(-1) ^ j by
      rw [show 3 * j + 3 = 3 * (j + 1) by ring, pow_mul]; norm_num; ring,
    show s ^ (3 * j + 3) = s ^ (3 * j + 2) * s by ring, Nat.factorial_succ]
  have h3 : (96 : ℝ) ^ (j + 1) = 2 ^ (3 * j + 2) * 12 ^ j * 24 := by
    rw [pow_succ, pow_add, pow_mul, show (96 : ℝ) = 2 ^ 3 * 12 by norm_num, mul_pow]; ring
  rw [h3]
  push_cast
  have h65 : (1 - 6 * ((j : ℝ) + 1)) ≠ 0 := by
    have : (0 : ℝ) ≤ j := Nat.cast_nonneg j; linarith
  have h1 : (0 : ℝ) < s ^ (1 / 2 : ℝ) := by positivity
  have hsq : s ^ (1 / 2 : ℝ) * s ^ (1 / 2 : ℝ) = s := by rw [← Real.rpow_add hs]; norm_num
  have hpj : ((-1 : ℝ) ^ j) ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp
  have e1 : (s ^ (1 / 2 : ℝ)) ^ 2 = s := by rw [sq, hsq]
  have e2 : ((-1 : ℝ) ^ j) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [e1, e2]
  ring

/-- The truncation error of `π^{-3/2}/2 ∫₀^∞ e^{-st} t^{3/2} e^{-t³/12} dt` at `s → +∞`. -/
theorem airyMod_kernel2_error {s : ℝ} (hs : 0 < s) (N : ℕ) :
    |(π * Real.sqrt π)⁻¹ / 2 * (∫ t in Ioi (0 : ℝ), airyMod_kernel2 (-s) t) -
      ∑ j ∈ Finset.range N, s ^ (1 / 2 : ℝ) / π * (-s) ^ (-(3 * (j + 1 : ℕ) : ℤ)) *
        (airyDerivModulusCoeff (j + 1) - airyModulusCoeff (j + 1))| ≤
      (π * Real.sqrt π)⁻¹ / 2 * (Real.Gamma ((3 * N + 2 : ℕ) + 1 / 2) *
        s ^ (-(((3 * N + 2 : ℕ) : ℝ) + 1 / 2)) / (12 ^ N * N !)) := by
  have hπ := Real.pi_pos
  have hc : 0 < (π * Real.sqrt π)⁻¹ / 2 := by positivity
  set B : ℕ → ℝ → ℝ := fun j t => Real.exp (-s * t) * t ^ ((((3 * j + 2 : ℕ) : ℝ) + 1 / 2) - 1) *
    ((-1) ^ j / (12 ^ j * j !))
  have hB : ∀ j, IntegrableOn (B j) (Ioi 0) := fun j =>
    (airyMod_mom_integral (3 * j + 2) hs).1.mul_const _
  have hBi : ∀ j, ∫ t in Ioi (0 : ℝ), B j t =
      Real.Gamma ((3 * j + 2 : ℕ) + 1 / 2) * s ^ (-(((3 * j + 2 : ℕ) : ℝ) + 1 / 2)) *
        ((-1) ^ j / (12 ^ j * j !)) := fun j => by
    rw [integral_mul_const, (airyMod_mom_integral (3 * j + 2) hs).2]
  have hpw : ∀ t : ℝ, 0 < t → ∀ j : ℕ, t ^ ((((3 * j + 2 : ℕ) : ℝ) + 1 / 2) - 1) =
      t ^ (3 * j) * (t ^ 2 * t ^ (-(1 / 2) : ℝ)) := fun t ht j => by
    rw [show (((3 * j + 2 : ℕ) : ℝ) + 1 / 2) - 1 = ((3 * j + 2 : ℕ) : ℝ) + (-(1 / 2)) by ring,
      Real.rpow_add ht, Real.rpow_natCast, pow_add]; ring
  have hpt : ∀ t : ℝ, 0 < t → airyMod_kernel2 (-s) t =
      Real.exp (-s * t) * (t ^ 2 * t ^ (-(1 / 2) : ℝ)) * airyMod_rem N (t ^ 3 / 12) +
        ∑ j ∈ Finset.range N, B j t := by
    intro t ht
    simp only [airyMod_kernel2, airyMod_rem, B]
    have : ∀ j ∈ Finset.range N, Real.exp (-s * t) * (t ^ 2 * t ^ (-(1 / 2) : ℝ)) *
        ((-(t ^ 3 / 12)) ^ j / j !) = Real.exp (-s * t) *
          t ^ ((((3 * j + 2 : ℕ) : ℝ) + 1 / 2) - 1) * ((-1) ^ j / (12 ^ j * j !)) := by
      intro j _
      rw [hpw t ht j, neg_pow, div_pow, pow_mul]
      field_simp
    rw [← Finset.sum_congr rfl this, ← Finset.mul_sum]
    ring
  have hg : IntegrableOn (fun t : ℝ => Real.exp (-s * t) * t ^ ((((3 * N + 2 : ℕ) : ℝ) + 1 / 2) - 1) /
      (12 ^ N * N !)) (Ioi 0) := (airyMod_mom_integral (3 * N + 2) hs).1.div_const _
  have hA : IntegrableOn (fun t : ℝ => Real.exp (-s * t) * (t ^ 2 * t ^ (-(1 / 2) : ℝ)) *
      airyMod_rem N (t ^ 3 / 12)) (Ioi 0) := by
    refine ((airyMod_kernel2_integrable (-s)).sub
      (integrable_finsetSum (Finset.range N) fun k _ => hB k)).congr_fun
      (fun t (ht : 0 < t) => ?_) measurableSet_Ioi
    simp only [Pi.sub_apply, hpt t ht]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hpt,
    integral_add hA (integrable_finsetSum (Finset.range N) fun k _ => hB k),
    integral_finsetSum (Finset.range N) fun k _ => hB k, mul_add, Finset.mul_sum]
  simp only [hBi, airyMod_deriv_term_identity _ hs, add_sub_cancel_right]
  rw [abs_mul, abs_of_pos hc]
  refine mul_le_mul_of_nonneg_left ?_ hc.le
  rw [show Real.Gamma ((3 * N + 2 : ℕ) + 1 / 2) * s ^ (-(((3 * N + 2 : ℕ) : ℝ) + 1 / 2)) /
      (12 ^ N * N !) = ∫ t in Ioi (0 : ℝ), Real.exp (-s * t) *
        t ^ ((((3 * N + 2 : ℕ) : ℝ) + 1 / 2) - 1) / (12 ^ N * N !) by
    rw [integral_div, (airyMod_mom_integral (3 * N + 2) hs).2]]
  rw [← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le hg ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t)
  have hb := airyMod_rem_bounds N (w := t ^ 3 / 12) (by positivity)
  have h0 : 0 ≤ Real.exp (-s * t) * (t ^ 2 * t ^ (-(1 / 2) : ℝ)) := by positivity
  have habs : |airyMod_rem N (t ^ 3 / 12)| ≤ (t ^ 3 / 12) ^ N / N ! := by
    have : |airyMod_rem N (t ^ 3 / 12)| = (-1) ^ N * airyMod_rem N (t ^ 3 / 12) := by
      rw [← abs_of_nonneg hb.1, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    rw [this]; exact hb.2
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h0, hpw t ht N]
  calc Real.exp (-s * t) * (t ^ 2 * t ^ (-(1 / 2) : ℝ)) * |airyMod_rem N (t ^ 3 / 12)|
      ≤ Real.exp (-s * t) * (t ^ 2 * t ^ (-(1 / 2) : ℝ)) * ((t ^ 3 / 12) ^ N / N !) :=
        mul_le_mul_of_nonneg_left habs h0
    _ = _ := by rw [div_pow, pow_mul]; field_simp

/-- Error bound for the truncated expansion of `N²` at `-∞` with `N + 1` terms. -/
theorem airyMod_derivSq_error {x : ℝ} (hx : x < 0) (N : ℕ) :
    |airyDerivModulus x ^ 2 - ∑ k ∈ Finset.range (N + 1),
        (-x) ^ (1 / 2 : ℝ) / π * x ^ (-(3 * k : ℤ)) * airyDerivModulusCoeff k| ≤
      (|airyModulusCoeff (N + 1)| + π * ((π * Real.sqrt π)⁻¹ / 2 *
        (Real.Gamma ((3 * N + 2 : ℕ) + 1 / 2) / (12 ^ N * N !)))) *
        |(-x) ^ (1 / 2 : ℝ) / π * x ^ (-(3 * (N + 1 : ℕ) : ℤ))| := by
  obtain ⟨s, hs, rfl⟩ : ∃ s : ℝ, 0 < s ∧ x = -s := ⟨-x, by linarith, by ring⟩
  rw [neg_neg]
  have hπ := Real.pi_pos
  have hsp : 0 < Real.sqrt π := Real.sqrt_pos.mpr hπ
  have hsq : s * s ^ (-1 / 2 : ℝ) = s ^ (1 / 2 : ℝ) := by
    rw [show s * s ^ (-1 / 2 : ℝ) = s ^ (1 : ℝ) * s ^ (-1 / 2 : ℝ) by rw [Real.rpow_one],
      ← Real.rpow_add hs]; norm_num
  -- decomposition of `N²`
  have hN : airyDerivModulus (-s) ^ 2 = (π * Real.sqrt π)⁻¹ / 2 *
      (∫ t in Ioi (0 : ℝ), airyMod_kernel2 (-s) t) + s * airyModulus (-s) ^ 2 := by
    rw [airyMod_derivSq_eq_integral, airyMod_sq_eq_integral]; ring
  have hsum : ∑ k ∈ Finset.range (N + 1),
      s ^ (1 / 2 : ℝ) / π * (-s) ^ (-(3 * k : ℤ)) * airyDerivModulusCoeff k =
      s * (s ^ (-1 / 2 : ℝ) / π * airyModulusSum false (N + 1) (-s)) +
        ∑ j ∈ Finset.range N, s ^ (1 / 2 : ℝ) / π * (-s) ^ (-(3 * (j + 1 : ℕ) : ℤ)) *
          (airyDerivModulusCoeff (j + 1) - airyModulusCoeff (j + 1)) := by
    simp only [airyModulusSum, Bool.false_eq_true, ite_false, Finset.mul_sum]
    rw [← sub_eq_iff_eq_add', ← Finset.sum_sub_distrib, Finset.sum_range_succ']
    have h0 : airyDerivModulusCoeff 0 = airyModulusCoeff 0 := by
      simp [airyDerivModulusCoeff]
    rw [h0]
    simp only [CharP.cast_eq_zero, mul_zero, neg_zero, zpow_zero, mul_one]
    rw [show s ^ (1 / 2 : ℝ) / π * airyModulusCoeff 0 - s * (s ^ (-1 / 2 : ℝ) / π *
      airyModulusCoeff 0) = 0 by rw [← hsq]; ring, add_zero]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hsq]; push_cast; ring
  rw [hN, hsum]
  have e1 := (airyMod_sq_error_bound (x := -s) (by linarith) (N + 1)).1
  rw [neg_neg] at e1
  have e2 := airyMod_kernel2_error hs N
  have key : (π * Real.sqrt π)⁻¹ / 2 * (∫ t in Ioi (0 : ℝ), airyMod_kernel2 (-s) t) +
      s * airyModulus (-s) ^ 2 - (s * (s ^ (-1 / 2 : ℝ) / π * airyModulusSum false (N + 1) (-s)) +
        ∑ j ∈ Finset.range N, s ^ (1 / 2 : ℝ) / π * (-s) ^ (-(3 * (j + 1 : ℕ) : ℤ)) *
          (airyDerivModulusCoeff (j + 1) - airyModulusCoeff (j + 1))) =
      s * (airyModulus (-s) ^ 2 - s ^ (-1 / 2 : ℝ) / π * airyModulusSum false (N + 1) (-s)) +
      ((π * Real.sqrt π)⁻¹ / 2 * (∫ t in Ioi (0 : ℝ), airyMod_kernel2 (-s) t) -
        ∑ j ∈ Finset.range N, s ^ (1 / 2 : ℝ) / π * (-s) ^ (-(3 * (j + 1 : ℕ) : ℤ)) *
          (airyDerivModulusCoeff (j + 1) - airyModulusCoeff (j + 1))) := by ring
  rw [key]
  refine (abs_add_le _ _).trans ?_
  have hphi : |s ^ (1 / 2 : ℝ) / π * (-s) ^ (-(3 * (N + 1 : ℕ) : ℤ))| =
      s ^ (-(((3 * N + 2 : ℕ) : ℝ) + 1 / 2)) / π := by
    rw [abs_mul, abs_of_pos (by positivity), zpow_neg, abs_inv, abs_zpow, abs_neg, abs_of_pos hs,
      show (3 * ((N + 1 : ℕ) : ℤ)) = ((3 * N + 3 : ℕ) : ℤ) by push_cast; ring, zpow_natCast,
      Real.rpow_neg hs.le, Real.rpow_add hs, Real.rpow_natCast,
      show s ^ (3 * N + 3) = s ^ (3 * N + 2) * (s ^ (1 / 2 : ℝ) * s ^ (1 / 2 : ℝ)) by
        rw [← Real.rpow_add hs]; norm_num; ring]
    field_simp
  have hpsi : s * |s ^ (-1 / 2 : ℝ) / π * airyModulusCoeff (N + 1) * (-s) ^ (-(3 * (N + 1 : ℕ) : ℤ))| =
      |airyModulusCoeff (N + 1)| * |s ^ (1 / 2 : ℝ) / π * (-s) ^ (-(3 * (N + 1 : ℕ) : ℤ))| := by
    rw [← hsq, ← abs_of_pos hs]
    simp only [abs_mul, abs_div, abs_of_pos hπ, abs_abs]
    ring
  rw [hphi] at hpsi ⊢
  rw [abs_mul, abs_of_pos hs]
  have := mul_le_mul_of_nonneg_left e1 hs.le
  push_cast at this hpsi e2 ⊢
  rw [hpsi] at this
  have e2' : (π * Real.sqrt π)⁻¹ / 2 * (Real.Gamma ((3 * N + 2 : ℕ) + 1 / 2) *
      s ^ (-(((3 * N + 2 : ℕ) : ℝ) + 1 / 2)) / (12 ^ N * N !)) =
      π * ((π * Real.sqrt π)⁻¹ / 2 * (Real.Gamma ((3 * N + 2 : ℕ) + 1 / 2) / (12 ^ N * N !))) *
        (s ^ (-(((3 * N + 2 : ℕ) : ℝ) + 1 / 2)) / π) := by
    field_simp
  push_cast at e2'
  rw [e2'] at e2
  nlinarith [this, e2]

/-- The exponential remainder is continuous. -/
theorem airyMod_rem_continuous (K : ℕ) : Continuous (airyMod_rem K) := by
  unfold airyMod_rem; fun_prop

/-- `|R_K(w)| ≤ w^K / K!` for `w ≥ 0`. -/
theorem airyMod_rem_abs_le (K : ℕ) {w : ℝ} (hw : 0 ≤ w) : |airyMod_rem K w| ≤ w ^ K / K ! := by
  have hb := airyMod_rem_bounds K hw
  have : |airyMod_rem K w| = (-1) ^ K * airyMod_rem K w := by
    rw [← abs_of_nonneg hb.1, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  rw [this]; exact hb.2

/-- The moment `t^{3K+3/2}` written in the kernel's factored form. -/
theorem airyMod_pow_factor {t : ℝ} (ht : 0 < t) (K : ℕ) :
    t ^ ((((3 * K + 2 : ℕ) : ℝ) + 1 / 2) - 1) = t ^ (3 * K) * (t ^ 2 * t ^ (-(1 / 2) : ℝ)) := by
  rw [show (((3 * K + 2 : ℕ) : ℝ) + 1 / 2) - 1 = ((3 * K + 2 : ℕ) : ℝ) + (-(1 / 2)) by ring,
    Real.rpow_add ht, Real.rpow_natCast, pow_add]; ring

/-- The pointwise first-neglected-term bound for the `N²` error integrand. -/
theorem airyMod_derivErr_pointwise (s : ℝ) (K : ℕ) {t : ℝ} (ht : 0 < t) :
    0 ≤ (-1) ^ K * (Real.exp (-s * t) * t ^ (-(1 / 2) : ℝ) *
        (t ^ 2 * airyMod_rem K (t ^ 3 / 12) / 4 - airyMod_rem (K + 1) (t ^ 3 / 12) / (2 * t))) ∧
    (-1) ^ K * (Real.exp (-s * t) * t ^ (-(1 / 2) : ℝ) *
        (t ^ 2 * airyMod_rem K (t ^ 3 / 12) / 4 - airyMod_rem (K + 1) (t ^ 3 / 12) / (2 * t))) ≤
      Real.exp (-s * t) * t ^ ((((3 * K + 2 : ℕ) : ℝ) + 1 / 2) - 1) *
        ((6 * K + 7) / (24 * 12 ^ K * (K + 1 : ℕ)!)) := by
  have hu : 0 ≤ t ^ 3 / 12 := by positivity
  obtain ⟨p0, p1⟩ := airyMod_rem_bounds K hu
  obtain ⟨q0, q1⟩ := airyMod_rem_bounds (K + 1) hu
  set p := (-1) ^ K * airyMod_rem K (t ^ 3 / 12)
  set q := (-1) ^ (K + 1) * airyMod_rem (K + 1) (t ^ 3 / 12)
  have ex : 0 < Real.exp (-s * t) * t ^ (-(1 / 2) : ℝ) := by positivity
  have e : (-1) ^ K * (Real.exp (-s * t) * t ^ (-(1 / 2) : ℝ) *
      (t ^ 2 * airyMod_rem K (t ^ 3 / 12) / 4 - airyMod_rem (K + 1) (t ^ 3 / 12) / (2 * t))) =
      Real.exp (-s * t) * t ^ (-(1 / 2) : ℝ) * (t ^ 2 * p / 4 + q / (2 * t)) := by
    simp only [p, q, pow_succ]; ring
  rw [e, airyMod_pow_factor ht K]
  constructor
  · positivity
  · have hb : t ^ 2 * p / 4 + q / (2 * t) ≤ t ^ (3 * K) * t ^ 2 *
        ((6 * K + 7) / (24 * 12 ^ K * (K + 1 : ℕ)!)) := by
      have h1 : t ^ 2 * p / 4 ≤ t ^ 2 * ((t ^ 3 / 12) ^ K / K !) / 4 := by gcongr
      have h2 : q / (2 * t) ≤ (t ^ 3 / 12) ^ (K + 1) / (K + 1)! / (2 * t) := by gcongr
      refine (add_le_add h1 h2).trans (le_of_eq ?_)
      rw [Nat.factorial_succ, div_pow, div_pow, pow_mul, pow_succ, pow_succ]
      push_cast
      field_simp
      ring
    calc _ ≤ Real.exp (-s * t) * t ^ (-(1 / 2) : ℝ) * (t ^ (3 * K) * t ^ 2 *
          ((6 * K + 7) / (24 * 12 ^ K * (K + 1 : ℕ)!))) := mul_le_mul_of_nonneg_left hb ex.le
      _ = _ := by ring

/-- The truncation error of `π^{-3/2}/2 ∫₀^∞ e^{-st} t^{3/2} e^{-t³/12} dt` as an integral of the
exponential remainder. -/
theorem airyMod_kernel2_error_integral {s : ℝ} (hs : 0 < s) (K : ℕ) :
    IntegrableOn (fun t : ℝ => Real.exp (-s * t) * (t ^ 2 * t ^ (-(1 / 2) : ℝ)) *
      airyMod_rem K (t ^ 3 / 12)) (Ioi 0) ∧
    (π * Real.sqrt π)⁻¹ / 2 * (∫ t in Ioi (0 : ℝ), airyMod_kernel2 (-s) t) -
      ∑ j ∈ Finset.range K, s ^ (1 / 2 : ℝ) / π * (-s) ^ (-(3 * (j + 1 : ℕ) : ℤ)) *
        (airyDerivModulusCoeff (j + 1) - airyModulusCoeff (j + 1)) =
      (π * Real.sqrt π)⁻¹ / 2 * ∫ t in Ioi (0 : ℝ), Real.exp (-s * t) *
        (t ^ 2 * t ^ (-(1 / 2) : ℝ)) * airyMod_rem K (t ^ 3 / 12) := by
  set B : ℕ → ℝ → ℝ := fun j t => Real.exp (-s * t) * t ^ ((((3 * j + 2 : ℕ) : ℝ) + 1 / 2) - 1) *
    ((-1) ^ j / (12 ^ j * j !))
  have hB : ∀ j, IntegrableOn (B j) (Ioi 0) := fun j =>
    (airyMod_mom_integral (3 * j + 2) hs).1.mul_const _
  have hBi : ∀ j, ∫ t in Ioi (0 : ℝ), B j t =
      Real.Gamma ((3 * j + 2 : ℕ) + 1 / 2) * s ^ (-(((3 * j + 2 : ℕ) : ℝ) + 1 / 2)) *
        ((-1) ^ j / (12 ^ j * j !)) := fun j => by
    rw [integral_mul_const, (airyMod_mom_integral (3 * j + 2) hs).2]
  have hpt : ∀ t : ℝ, 0 < t → airyMod_kernel2 (-s) t =
      Real.exp (-s * t) * (t ^ 2 * t ^ (-(1 / 2) : ℝ)) * airyMod_rem K (t ^ 3 / 12) +
        ∑ j ∈ Finset.range K, B j t := by
    intro t ht
    simp only [airyMod_kernel2, airyMod_rem, B]
    have : ∀ j ∈ Finset.range K, Real.exp (-s * t) * (t ^ 2 * t ^ (-(1 / 2) : ℝ)) *
        ((-(t ^ 3 / 12)) ^ j / j !) = Real.exp (-s * t) *
          t ^ ((((3 * j + 2 : ℕ) : ℝ) + 1 / 2) - 1) * ((-1) ^ j / (12 ^ j * j !)) := by
      intro j _
      rw [airyMod_pow_factor ht j, neg_pow, div_pow, pow_mul]
      field_simp
    rw [← Finset.sum_congr rfl this, ← Finset.mul_sum]
    ring
  have hA : IntegrableOn (fun t : ℝ => Real.exp (-s * t) * (t ^ 2 * t ^ (-(1 / 2) : ℝ)) *
      airyMod_rem K (t ^ 3 / 12)) (Ioi 0) := by
    refine ((airyMod_kernel2_integrable (-s)).sub
      (integrable_finsetSum (Finset.range K) fun k _ => hB k)).congr_fun
      (fun t (ht : 0 < t) => ?_) measurableSet_Ioi
    simp only [Pi.sub_apply, hpt t ht]
    ring
  refine ⟨hA, ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioi hpt,
    integral_add hA (integrable_finsetSum (Finset.range K) fun k _ => hB k),
    integral_finsetSum (Finset.range K) fun k _ => hB k, mul_add, Finset.mul_sum]
  simp only [hBi, airyMod_deriv_term_identity _ hs, add_sub_cancel_right]

/-- The `N²` error integrand `e^{-st} t^{-1/2} (t² R_K/4 - R_{K+1}/(2t))` is integrable. -/
theorem airyMod_derivErr_integrable (s : ℝ) (hs : 0 < s) (K : ℕ) :
    IntegrableOn (fun t : ℝ => Real.exp (-s * t) * t ^ (-(1 / 2) : ℝ) *
      (t ^ 2 * airyMod_rem K (t ^ 3 / 12) / 4 - airyMod_rem (K + 1) (t ^ 3 / 12) / (2 * t)))
      (Ioi 0) := by
  have hc := airyMod_rem_continuous
  refine ((airyMod_mom_integral (3 * K + 2) hs).1.mul_const
    ((6 * K + 7) / (24 * 12 ^ K * (K + 1 : ℕ)!))).mono' ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    intro t (ht : 0 < t)
    have : t ≠ 0 := ht.ne'
    refine ContinuousAt.continuousWithinAt ?_
    have h1 : ContinuousAt (fun t : ℝ => t ^ (-(1 / 2) : ℝ)) t :=
      Real.continuousAt_rpow_const _ _ (Or.inl this)
    have h2 : ContinuousAt (fun t : ℝ => airyMod_rem K (t ^ 3 / 12)) t :=
      ((hc K).comp (by fun_prop)).continuousAt
    have h3 : ContinuousAt (fun t : ℝ => airyMod_rem (K + 1) (t ^ 3 / 12)) t :=
      ((hc (K + 1)).comp (by fun_prop)).continuousAt
    have h5 : ContinuousAt (fun t : ℝ => 2 * t) t := by fun_prop
    exact (((Real.continuous_exp.continuousAt).comp (by fun_prop)).mul h1).mul
      ((((continuousAt_id.pow 2).mul h2).div_const 4).sub
        (h3.div h5 (by simpa using this)))
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t)
    obtain ⟨h0, h1⟩ := airyMod_derivErr_pointwise s K ht
    have e : ‖Real.exp (-s * t) * t ^ (-(1 / 2) : ℝ) *
        (t ^ 2 * airyMod_rem K (t ^ 3 / 12) / 4 - airyMod_rem (K + 1) (t ^ 3 / 12) / (2 * t))‖ =
        (-1) ^ K * (Real.exp (-s * t) * t ^ (-(1 / 2) : ℝ) *
        (t ^ 2 * airyMod_rem K (t ^ 3 / 12) / 4 - airyMod_rem (K + 1) (t ^ 3 / 12) / (2 * t))) := by
      rw [← abs_of_nonneg h0, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
        Real.norm_eq_abs]
    rw [e]
    exact h1

/-- Integration by parts for the `M²` error integrand:
`s ∫ e^{-st} t^{-1/2} R_{K+1}(t³/12) = ∫ e^{-st} t^{-1/2}(t² R_K/4 - R_{K+1}/(2t)) - ½ ∫ e^{-st} t^{3/2} R_K`. -/
theorem airyMod_derivErr_ibp {s : ℝ} (hs : 0 < s) (K : ℕ) :
    s * ∫ t in Ioi (0 : ℝ), Real.exp (-s * t) * t ^ (-(1 / 2) : ℝ) * airyMod_rem (K + 1) (t ^ 3 / 12) =
      (∫ t in Ioi (0 : ℝ), Real.exp (-s * t) * t ^ (-(1 / 2) : ℝ) *
        (t ^ 2 * airyMod_rem K (t ^ 3 / 12) / 4 - airyMod_rem (K + 1) (t ^ 3 / 12) / (2 * t))) -
      (∫ t in Ioi (0 : ℝ), Real.exp (-s * t) * (t ^ 2 * t ^ (-(1 / 2) : ℝ)) *
        airyMod_rem K (t ^ 3 / 12)) / 2 := by
  set F : ℝ → ℝ := fun t => Real.exp (-s * t) * t ^ (-(1 / 2) : ℝ) * airyMod_rem (K + 1) (t ^ 3 / 12)
  set E : ℝ → ℝ := fun t => Real.exp (-s * t) * t ^ (-(1 / 2) : ℝ) *
    (t ^ 2 * airyMod_rem K (t ^ 3 / 12) / 4 - airyMod_rem (K + 1) (t ^ 3 / 12) / (2 * t))
  set B : ℝ → ℝ := fun t => Real.exp (-s * t) * (t ^ 2 * t ^ (-(1 / 2) : ℝ)) *
    airyMod_rem K (t ^ 3 / 12)
  have hA : IntegrableOn F (Ioi 0) := (airyMod_sq_error_integral hs (K + 1)).1
  have hE : IntegrableOn E (Ioi 0) := airyMod_derivErr_integrable s hs K
  have hB : IntegrableOn B (Ioi 0) := (airyMod_kernel2_error_integral hs K).1
  have hderiv : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt F (-s * F t + (E t - B t / 2)) t := by
    intro t (ht : 0 < t)
    have h1 : HasDerivAt (fun t : ℝ => Real.exp (-s * t)) (Real.exp (-s * t) * (-s)) t := by
      simpa using ((hasDerivAt_id t).const_mul (-s)).exp
    have h2 := Real.hasDerivAt_rpow_const (p := (-(1 / 2) : ℝ)) (Or.inl ht.ne')
    have h3 : HasDerivAt (fun t : ℝ => airyMod_rem (K + 1) (t ^ 3 / 12))
        (-airyMod_rem K (t ^ 3 / 12) * (3 * t ^ 2 / 12)) t := by
      have h4 : HasDerivAt (fun t : ℝ => t ^ 3 / 12) (3 * t ^ 2 / 12) t := by
        simpa using (hasDerivAt_pow 3 t).div_const 12
      exact (airyMod_hasDerivAt_rem K (t ^ 3 / 12)).comp t h4
    convert (h1.mul h2).mul h3 using 1
    simp only [F, E, B, Pi.mul_apply]
    rw [Real.rpow_sub_one ht.ne']
    field_simp
    ring
  have f'int : IntegrableOn (fun t => -s * F t + (E t - B t / 2)) (Ioi 0) :=
    (hA.const_mul (-s)).add (hE.sub (hB.div_const 2))
  have hlim : Tendsto F atTop (𝓝 0) :=
    tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi hderiv f'int hA
  have hF0 : F 0 = 0 := by simp [F]
  have hcont : ContinuousWithinAt F (Ici 0) 0 := by
    rw [ContinuousWithinAt, hF0]
    set p : ℝ := ((3 * (K + 1) : ℕ) : ℝ) + (-(1 / 2))
    have hp : 0 < p := by simp only [p]; push_cast; linarith [(Nat.cast_nonneg K : (0 : ℝ) ≤ K)]
    have hg : Tendsto (fun t : ℝ => t ^ p / (12 ^ (K + 1) * (K + 1)!)) (𝓝[Ici 0] 0) (𝓝 0) := by
      have := ((Real.continuousAt_rpow_const 0 p (Or.inr hp.le)).div_const
        (12 ^ (K + 1) * ((K + 1)! : ℝ))).tendsto
      rw [Real.zero_rpow hp.ne', zero_div] at this
      exact this.mono_left nhdsWithin_le_nhds
    refine squeeze_zero_norm' ?_ hg
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 ≤ t)
    rcases ht.eq_or_lt with rfl | ht
    · rw [hF0, norm_zero, Real.zero_rpow hp.ne', zero_div]
    · have hb := airyMod_rem_abs_le (K + 1) (w := t ^ 3 / 12) (by positivity)
      have he : Real.exp (-s * t) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
      have hw : 0 < t ^ (-(1 / 2) : ℝ) := by positivity
      simp only [F, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_pos hw]
      have e : t ^ p / (12 ^ (K + 1) * (K + 1)!) =
          t ^ (-(1 / 2) : ℝ) * ((t ^ 3 / 12) ^ (K + 1) / (K + 1)!) := by
        simp only [p]
        rw [Real.rpow_add ht, Real.rpow_natCast, div_pow, pow_mul]
        field_simp
      rw [e]
      calc Real.exp (-s * t) * t ^ (-(1 / 2) : ℝ) * |airyMod_rem (K + 1) (t ^ 3 / 12)|
          ≤ 1 * t ^ (-(1 / 2) : ℝ) * ((t ^ 3 / 12) ^ (K + 1) / (K + 1)!) := by gcongr
        _ = _ := by ring
  have key := integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv f'int hlim
  rw [hF0, sub_zero] at key
  have i1 : ∫ t in Ioi (0 : ℝ), -s * F t + (E t - B t / 2) =
      (∫ t in Ioi (0 : ℝ), -s * F t) + ∫ t in Ioi (0 : ℝ), (E t - B t / 2) :=
    integral_add (hA.const_mul (-s)) (hE.sub (hB.div_const 2))
  have i2 : ∫ t in Ioi (0 : ℝ), (E t - B t / 2) =
      (∫ t in Ioi (0 : ℝ), E t) - ∫ t in Ioi (0 : ℝ), B t / 2 :=
    integral_sub hE (hB.div_const 2)
  rw [i1, i2, integral_const_mul, integral_div] at key
  linarith

/-- `d_{K+1} = (d_{K+1} - a_{K+1}) (6K+7)/(12(K+1))` for the `N²` and `M²` coefficients. -/
theorem airyMod_derivCoeff_eq (K : ℕ) :
    airyDerivModulusCoeff (K + 1) = (airyDerivModulusCoeff (K + 1) - airyModulusCoeff (K + 1)) *
      ((6 * K + 7) / (12 * (K + 1))) := by
  have hK : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have h1 : (1 - 6 * ((K + 1 : ℕ) : ℝ)) ≠ 0 := by push_cast; linarith
  have h2 : (12 * ((K : ℝ) + 1)) ≠ 0 := by positivity
  simp only [airyDerivModulusCoeff]
  field_simp
  push_cast
  ring

/-- The first neglected term of the `N²` expansion as a moment integral. -/
theorem airyMod_derivMod_term_identity (K : ℕ) {s : ℝ} (hs : 0 < s) :
    (π * Real.sqrt π)⁻¹ * (Real.Gamma ((3 * K + 2 : ℕ) + 1 / 2) *
      s ^ (-(((3 * K + 2 : ℕ) : ℝ) + 1 / 2)) * ((6 * K + 7) / (24 * 12 ^ K * (K + 1 : ℕ)!))) *
        (-1) ^ K =
      s ^ (1 / 2 : ℝ) / π * airyDerivModulusCoeff (K + 1) * (-s) ^ (-(3 * (K + 1 : ℕ) : ℤ)) := by
  have h := airyMod_deriv_term_identity K hs
  rw [airyMod_derivCoeff_eq K]
  have e : s ^ (1 / 2 : ℝ) / π * ((airyDerivModulusCoeff (K + 1) - airyModulusCoeff (K + 1)) *
      ((6 * K + 7) / (12 * (K + 1)))) * (-s) ^ (-(3 * (K + 1 : ℕ) : ℤ)) =
      (s ^ (1 / 2 : ℝ) / π * (-s) ^ (-(3 * (K + 1 : ℕ) : ℤ)) *
        (airyDerivModulusCoeff (K + 1) - airyModulusCoeff (K + 1))) *
          ((6 * K + 7) / (12 * (K + 1))) := by ring
  rw [e, ← h, Nat.factorial_succ]
  push_cast
  field_simp
  norm_num

/-- Splitting the truncated `N²` series into the `M²` series and the kernel-2 series. -/
theorem airyMod_derivSum_split {s : ℝ} (hs : 0 < s) (K : ℕ) :
    s ^ (1 / 2 : ℝ) / π * airyModulusSum true (K + 1) (-s) =
      s * (s ^ (-1 / 2 : ℝ) / π * airyModulusSum false (K + 1) (-s)) +
        ∑ j ∈ Finset.range K, s ^ (1 / 2 : ℝ) / π * (-s) ^ (-(3 * (j + 1 : ℕ) : ℤ)) *
          (airyDerivModulusCoeff (j + 1) - airyModulusCoeff (j + 1)) := by
  have hsq : s * s ^ (-1 / 2 : ℝ) = s ^ (1 / 2 : ℝ) := by
    rw [show s * s ^ (-1 / 2 : ℝ) = s ^ (1 : ℝ) * s ^ (-1 / 2 : ℝ) by rw [Real.rpow_one],
      ← Real.rpow_add hs]; norm_num
  simp only [airyModulusSum, ite_true, Bool.false_eq_true, ite_false, Finset.mul_sum]
  rw [← sub_eq_iff_eq_add', ← Finset.sum_sub_distrib, Finset.sum_range_succ']
  have h0 : airyDerivModulusCoeff 0 = airyModulusCoeff 0 := by
    simp [airyDerivModulusCoeff]
  rw [h0]
  simp only [CharP.cast_eq_zero, mul_zero, neg_zero, zpow_zero, mul_one]
  rw [show s ^ (1 / 2 : ℝ) / π * airyModulusCoeff 0 - s * (s ^ (-1 / 2 : ℝ) / π *
    airyModulusCoeff 0) = 0 by rw [← hsq]; ring, add_zero]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← hsq]; push_cast; ring

/-- The error of the truncated expansion of `N²` at `-∞` as a single integral:
`N(-s)² - (s^{1/2}/π) ∑_{k<K+1} d_k (-s)^{-3k} =
π^{-3/2} ∫₀^∞ e^{-st} t^{-1/2} (t² R_K(t³/12)/4 - R_{K+1}(t³/12)/(2t)) dt`. -/
theorem airyMod_derivSq_error_integral {s : ℝ} (hs : 0 < s) (K : ℕ) :
    airyDerivModulus (-s) ^ 2 - s ^ (1 / 2 : ℝ) / π * airyModulusSum true (K + 1) (-s) =
      (π * Real.sqrt π)⁻¹ * ∫ t in Ioi (0 : ℝ), Real.exp (-s * t) * t ^ (-(1 / 2) : ℝ) *
        (t ^ 2 * airyMod_rem K (t ^ 3 / 12) / 4 - airyMod_rem (K + 1) (t ^ 3 / 12) / (2 * t)) := by
  have hN : airyDerivModulus (-s) ^ 2 = (π * Real.sqrt π)⁻¹ / 2 *
      (∫ t in Ioi (0 : ℝ), airyMod_kernel2 (-s) t) + s * airyModulus (-s) ^ 2 := by
    rw [airyMod_derivSq_eq_integral, airyMod_sq_eq_integral]; ring
  have h1 := (airyMod_sq_error_integral hs (K + 1)).2
  have h2 := (airyMod_kernel2_error_integral hs K).2
  have h3 := airyMod_derivErr_ibp hs K
  rw [hN, airyMod_derivSum_split hs K]
  have : (π * Real.sqrt π)⁻¹ / 2 * (∫ t in Ioi (0 : ℝ), airyMod_kernel2 (-s) t) +
      s * airyModulus (-s) ^ 2 - (s * (s ^ (-1 / 2 : ℝ) / π * airyModulusSum false (K + 1) (-s)) +
        ∑ j ∈ Finset.range K, s ^ (1 / 2 : ℝ) / π * (-s) ^ (-(3 * (j + 1 : ℕ) : ℤ)) *
          (airyDerivModulusCoeff (j + 1) - airyModulusCoeff (j + 1))) =
      s * (airyModulus (-s) ^ 2 - s ^ (-1 / 2 : ℝ) / π * airyModulusSum false (K + 1) (-s)) +
      ((π * Real.sqrt π)⁻¹ / 2 * (∫ t in Ioi (0 : ℝ), airyMod_kernel2 (-s) t) -
        ∑ j ∈ Finset.range K, s ^ (1 / 2 : ℝ) / π * (-s) ^ (-(3 * (j + 1 : ℕ) : ℤ)) *
          (airyDerivModulusCoeff (j + 1) - airyModulusCoeff (j + 1))) := by ring
  rw [this, h1, h2]
  have e : s * ((π * Real.sqrt π)⁻¹ * ∫ t in Ioi (0 : ℝ), Real.exp (-s * t) *
      t ^ (-(1 / 2) : ℝ) * airyMod_rem (K + 1) (t ^ 3 / 12)) = (π * Real.sqrt π)⁻¹ *
      (s * ∫ t in Ioi (0 : ℝ), Real.exp (-s * t) * t ^ (-(1 / 2) : ℝ) *
        airyMod_rem (K + 1) (t ^ 3 / 12)) := by ring
  rw [e, h3]
  ring

/-- The cross-term Nicholson kernel `e^{xt} e^{-t³/12} t^{1/2}`. -/
noncomputable def airyMod_kernel1 (x t : ℝ) : ℝ :=
  Real.exp (x * t) * (Real.exp (-(t ^ 3 / 12)) * (t ^ 1 * t ^ (-(1 / 2) : ℝ)))

/-- Nicholson-type formula for `Ai Ai' + Bi Bi'` on the real line. -/
theorem airyMod_cross_eq_integral (x : ℝ) :
    airyAiReal x * airyAiDerivReal x + airyBiReal x * airyBiDerivReal x =
      (∫ t in Ioi (0 : ℝ), airyMod_kernel1 x t) / (2 * (π * Real.sqrt π)) := by
  have h := airyMod_cross_integral x
  rw [airyAi_ofReal_eq, airyBi_ofReal_eq, airyAiDeriv_ofReal_eq, airyBiDeriv_ofReal_eq,
    airyMod_pi_cpow] at h
  have hI : (∫ t : ℝ in Ioi 0, exp ((x : ℂ) * t - (t : ℂ) ^ 3 / 12) *
      ((t : ℂ) ^ 1 * (t : ℂ) ^ (-1 / 2 : ℂ))) = ((∫ t in Ioi (0 : ℝ), airyMod_kernel1 x t : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) => ?_
    have hc : ((t : ℂ) ^ (-1 / 2 : ℂ)) = ((t ^ (-(1 / 2) : ℝ) : ℝ) : ℂ) := by
      rw [ofReal_cpow ht.le]; push_cast; ring_nf
    simp only [airyMod_kernel1]
    rw [hc]; push_cast
    rw [sub_eq_add_neg, Complex.exp_add]; ring
  rw [hI] at h
  exact_mod_cast h

/-- `|x|^{1/2} M(x)² < 1/π` for `x < 0`. -/
theorem airyMod_sqrt_mul_sq_lt {s : ℝ} (hs : 0 < s) : s ^ (1 / 2 : ℝ) * airyModulus (-s) ^ 2 < 1 / π := by
  have hπ := Real.pi_pos
  rw [airyMod_sqrt_mul_sq hs]
  have hG : ∫ u in Ioi (0 : ℝ), Real.exp (-u) * u ^ (-(1 / 2) : ℝ) = Real.sqrt π := by
    rw [← Real.Gamma_one_half_eq, Real.Gamma_eq_integral (by norm_num)]
    norm_num
  have hint := Real.GammaIntegral_convergent (s := 1 / 2) (by norm_num)
  rw [show (1 / 2 : ℝ) - 1 = -(1 / 2) by norm_num] at hint
  have hlt : (∫ u in Ioi (0 : ℝ), Real.exp (-u) * (Real.exp (-(u ^ 3 / (12 * s ^ 3))) *
      u ^ (-(1 / 2) : ℝ))) < ∫ u in Ioi (0 : ℝ), Real.exp (-u) * u ^ (-(1 / 2) : ℝ) := by
    rw [← sub_pos, ← integral_sub hint (airyMod_scaled_integrable hs.le)]
    refine airyMod_integral_pos (hint.sub (airyMod_scaled_integrable hs.le)) fun u hu => ?_
    have : Real.exp (-(u ^ 3 / (12 * s ^ 3))) < 1 := Real.exp_lt_one_iff.mpr
      (neg_lt_zero.mpr (by positivity))
    have h2 : 0 < Real.exp (-u) * u ^ (-(1 / 2) : ℝ) := by positivity
    nlinarith
  rw [hG] at hlt
  have hsp : 0 < Real.sqrt π := Real.sqrt_pos.mpr hπ
  rw [div_lt_div_iff₀ (by positivity) hπ]
  nlinarith

end Nicholson

/-- `M(x)` is strictly increasing on `(-∞, 0]`, DLMF §9.8(iii). -/
theorem airy_modulus_monotone :
    StrictMonoOn (airyModulus) (Iic 0) := by
  intro x _ y _ hxy
  exact lt_of_pow_lt_pow_left₀ 2 (airyModulus_pos y).le (airyMod_sq_strictMono hxy)

/-- `M'(x)` is strictly increasing on `(-∞, 0]`, DLMF §9.8(iii). -/
theorem airy_modulus_deriv_monotone :
    StrictMonoOn (deriv airyModulus) (Iic 0) := by
  have hπ := Real.pi_pos
  set C : ℝ → ℝ := fun x => airyAiReal x * airyAiDerivReal x + airyBiReal x * airyBiDerivReal x
  have hC : ∀ x, HasDerivAt C (airyDerivModulus x ^ 2 + x * airyModulus x ^ 2) x := fun x => by
    have h := ((hasDerivAt_airyAiReal x).mul (hasDerivAt_airyAiDerivReal x)).add
      ((hasDerivAt_airyBiReal x).mul (hasDerivAt_airyBiDerivReal x))
    refine h.congr_deriv ?_
    rw [airyDerivModulus_sq, airyModulus_sq]; ring
  have hD : ∀ x, HasDerivAt (deriv airyModulus)
      (((airyDerivModulus x ^ 2 + x * airyModulus x ^ 2) * airyModulus x -
        C x * (C x / airyModulus x)) / airyModulus x ^ 2) x := fun x => by
    rw [deriv_airyModulus]
    exact (hC x).div (hasDerivAt_airyModulus x) (airyModulus_pos x).ne'
  refine strictMonoOn_of_deriv_pos (convex_Iic 0)
    (fun x _ => (hD x).continuousAt.continuousWithinAt) fun x hx => ?_
  rw [interior_Iic, mem_Iio] at hx
  rw [(hD x).deriv]
  have hM := airyModulus_pos x
  have hL := airy_lagrange x
  rw [← airyModulus_sq, ← airyDerivModulus_sq] at hL
  have hb := airyMod_sqrt_mul_sq_lt (s := -x) (by linarith)
  rw [neg_neg] at hb
  have hsq : ((-x) ^ (1 / 2 : ℝ)) ^ 2 = -x := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num
  have key : 0 < 1 / π ^ 2 + x * airyModulus x ^ 4 := by
    have h0 : 0 ≤ (-x) ^ (1 / 2 : ℝ) * airyModulus x ^ 2 :=
      mul_nonneg (Real.rpow_nonneg (by linarith) _) (by positivity)
    have h1 : ((-x) ^ (1 / 2 : ℝ) * airyModulus x ^ 2) ^ 2 < (1 / π) ^ 2 :=
      pow_lt_pow_left₀ hb h0 (by norm_num)
    rw [mul_pow, hsq] at h1
    have : (1 / π) ^ 2 = 1 / π ^ 2 := by ring
    nlinarith
  have e : ((airyDerivModulus x ^ 2 + x * airyModulus x ^ 2) * airyModulus x -
      C x * (C x / airyModulus x)) / airyModulus x ^ 2 =
      (1 / π ^ 2 + x * airyModulus x ^ 4) / airyModulus x ^ 3 := by
    have hNC : (airyDerivModulus x ^ 2 + x * airyModulus x ^ 2) * airyModulus x ^ 2 - C x ^ 2 =
        1 / π ^ 2 + x * airyModulus x ^ 4 := by
      simp only [C]
      field_simp
      linear_combination hL
    rw [← hNC]
    field_simp
  rw [e]; positivity

end DLMF.Airy
end
