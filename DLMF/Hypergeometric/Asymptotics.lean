/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.Complex.TaylorParameter

public import DLMF.Bessel.Modified
public import Mathlib.Analysis.SpecialFunctions.Arcosh
public import Mathlib.Analysis.Complex.TaylorSeries
public import DLMF.Gamma.Asymptotics
public import DLMF.Gamma.RecipGammaDeriv
public import DLMF.Hypergeometric.Continuation

/-!
# Large-parameter asymptotics (DLMF §15.12)

The large-denominator expansions are stated along the positive real axis, with
the variable in the series disk. Remainders use Mathlib's `Asymptotics.IsBigO`.
The Bessel approximation E5–E6 uses existing `besselI` and `Real.arcosh`, with
`1 < x < 3` ensuring the hypergeometric series argument is in the disk.
E1 defines the larger complex-sector boundary; those sector domains are deferred.
E6 uses Mathlib's `Real.arcosh` (https://dlmf.nist.gov/15.12.E6); no
duplicate inverse-hyperbolic-function definition is introduced.
E7–E13 require parabolic-cylinder/Airy functions and continuous choices of
turning-point branches not yet available in this project's hypergeometric API.
-/

@[expose] public section

open Complex Filter
open scoped Real Topology
open DLMF.Bessel

noncomputable section

namespace DLMF.Hypergeometric

/-- `c^m k! ≤ m! (c)_k` for real `c ≥ 1` and `k ≥ m`. -/
theorem pow_mul_factorial_le_poch {c : ℝ} (hc : 1 ≤ c) {m k : ℕ} (hk : m ≤ k) :
    c ^ m * k.factorial ≤ m.factorial * (ascPochhammer ℝ k).eval c := by
  induction k, hk using Nat.le_induction with
  | base =>
    have : c ^ m ≤ (ascPochhammer ℝ m).eval c := by
      induction m with
      | zero => simp
      | succ j ih =>
        rw [ascPochhammer_succ_eval, pow_succ]
        exact mul_le_mul ih (by linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]) (by positivity)
          (ascPochhammer_eval_nonneg (by linarith) j)
    have hf : (0 : ℝ) < m.factorial := by positivity
    nlinarith
  | succ k hk ih =>
    rw [Nat.factorial_succ, Nat.cast_mul, ascPochhammer_succ_eval]
    have hk1 : ((k + 1 : ℕ) : ℝ) ≤ c + k := by push_cast; linarith
    have h0 : (0 : ℝ) ≤ c ^ m * k.factorial := by positivity
    calc c ^ m * (((k + 1 : ℕ) : ℝ) * k.factorial) = (c ^ m * k.factorial) * ((k + 1 : ℕ) : ℝ) := by
          ring
      _ ≤ (m.factorial * (ascPochhammer ℝ k).eval c) * (c + k) :=
          mul_le_mul ih hk1 (by positivity) (by
            have := ascPochhammer_eval_nonneg (show (0 : ℝ) ≤ c by linarith) k
            positivity)
      _ = _ := by ring

@[dlmf 15.12.E2]
theorem large_denominator_expansion (a b : ℂ) {z : ℂ} (hz : ‖z‖ < 1) (m : ℕ) :
    Asymptotics.IsBigO atTop
      (fun c : ℝ => ₂F₁ a b (c : ℂ) z -
        ∑ k ∈ Finset.range m, gaussHGCoeff a b c k * z ^ k)
      (fun c : ℝ => (c : ℂ)⁻¹ ^ m) := by
  set g : ℕ → ℝ := fun k => ‖gaussHGCoeff (‖a‖ : ℂ) (‖b‖ : ℂ) 1 k * z ^ k‖ with hg
  have hgs : Summable g := summable_norm_gaussHGCoeff_mul_pow _ _ _ hz
  refine Asymptotics.IsBigO.of_bound (m.factorial * ∑' k, g k) ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with c hc
  have hc0 : (0 : ℝ) < c := by linarith
  set f : ℕ → ℂ := fun k => gaussHGCoeff a b c k * z ^ k with hf
  have hfs : Summable f := (summable_norm_gaussHGCoeff_mul_pow a b c hz).of_norm
  have hF : ₂F₁ a b (c : ℂ) z = ∑' k, f k := by
    rw [ordinaryHypergeometric_eq_tsum]
    simp only [smul_eq_mul, hf]
    congr 1
    funext n
    simp [gaussHGCoeff, poch, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
  rw [hF, ← hfs.sum_add_tsum_nat_add m, add_sub_cancel_left]
  -- termwise bound on the tail
  have hbd : ∀ k, ‖f (k + m)‖ ≤ m.factorial * (c ^ m)⁻¹ * g (k + m) := by
    intro k
    have hpos := pow_mul_factorial_le_poch hc (Nat.le_add_left m k)
    have hpc : ‖poch (c : ℂ) (k + m)‖ = (ascPochhammer ℝ (k + m)).eval c := by
      rw [poch, ascPochhammer_eval_ofReal, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (ascPochhammer_eval_nonneg hc0.le _)]
    have h1 : ‖poch (1 : ℂ) (k + m)‖ = (k + m).factorial := by
      rw [poch_nat_one, Complex.norm_natCast]
    have ha := norm_ascPochhammer_eval_le (le_refl ‖a‖) (k + m)
    have hb := norm_ascPochhammer_eval_le (le_refl ‖b‖) (k + m)
    have hfac : (0 : ℝ) < (k + m).factorial := by positivity
    have hP : 0 < (ascPochhammer ℝ (k + m)).eval c := by
      have : (0 : ℝ) < c ^ m * (k + m).factorial := by positivity
      have hmf : (0 : ℝ) < m.factorial := by positivity
      by_contra hneg
      have := not_lt.mp hneg
      nlinarith
    simp only [hf, hg, gaussHGCoeff, norm_mul, norm_div, norm_pow, Complex.norm_natCast, hpc, h1]
    rw [show ‖poch a (k + m)‖ = ‖(ascPochhammer ℂ (k + m)).eval a‖ from rfl,
      show ‖poch b (k + m)‖ = ‖(ascPochhammer ℂ (k + m)).eval b‖ from rfl]
    have hz0 : 0 ≤ ‖z‖ ^ (k + m) := by positivity
    have hcm : 0 < c ^ m := by positivity
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    calc ‖(ascPochhammer ℂ (k + m)).eval a‖ * ‖(ascPochhammer ℂ (k + m)).eval b‖ * ‖z‖ ^ (k + m)
        ≤ ‖poch (‖a‖ : ℂ) (k + m)‖ * ‖poch (‖b‖ : ℂ) (k + m)‖ * ‖z‖ ^ (k + m) := by gcongr
      _ = m.factorial * (c ^ m)⁻¹ * (‖poch (‖a‖ : ℂ) (k + m)‖ * ‖poch (‖b‖ : ℂ) (k + m)‖ /
            ((k + m).factorial * (k + m).factorial) * ‖z‖ ^ (k + m)) *
            ((c ^ m * (k + m).factorial) / m.factorial * (k + m).factorial) := by
          field_simp
      _ ≤ _ := by
          have hle : c ^ m * (k + m).factorial / m.factorial ≤ (ascPochhammer ℝ (k + m)).eval c := by
            rw [div_le_iff₀ (by positivity)]; linarith
          gcongr
  have hgs' : Summable fun k => g (k + m) := (summable_nat_add_iff m).mpr hgs
  have hnorm : ‖∑' k, f (k + m)‖ ≤ m.factorial * (c ^ m)⁻¹ * ∑' k, g k := by
    calc ‖∑' k, f (k + m)‖ ≤ ∑' k, m.factorial * (c ^ m)⁻¹ * g (k + m) :=
          tsum_of_norm_bounded (hgs'.mul_left _).hasSum hbd
      _ = m.factorial * (c ^ m)⁻¹ * ∑' k, g (k + m) := tsum_mul_left
      _ ≤ m.factorial * (c ^ m)⁻¹ * ∑' k, g k := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [← hgs.sum_add_tsum_nat_add m]
          have : 0 ≤ ∑ i ∈ Finset.range m, g i := Finset.sum_nonneg fun i _ => norm_nonneg _
          linarith
  rw [norm_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc0, inv_pow]
  calc ‖∑' k, f (k + m)‖ ≤ m.factorial * (c ^ m)⁻¹ * ∑' k, g k := hnorm
    _ = _ := by ring

/-- The removable quotient in the generating function has value `1` at zero. -/
def expSubOneDiv (t : ℂ) : ℂ := if t = 0 then 1 else (exp t - 1) / t

/-- Generating function for the large-denominator coefficients. -/
@[dlmf 15.12.E4]
def largeDenominatorGenerating (a b c z t : ℂ) : ℂ :=
  expSubOneDiv t ^ (b - 1) * exp (t * (1 - c)) * (1 - z + z * exp (-t)) ^ (-a)

/-- Taylor coefficients of DLMF's generating function. -/
@[dlmf 15.12.E4]
def largeDenominatorCoeff (a b c z : ℂ) (n : ℕ) : ℂ :=
  iteratedDeriv n (largeDenominatorGenerating a b c z) 0 / (n.factorial : ℂ)

/-- `expSubOneDiv` is the difference quotient of `exp` at `0`. -/
theorem expSubOneDiv_eq_dslope : expSubOneDiv = dslope exp 0 := by
  funext t
  by_cases ht : t = 0
  · subst ht; simp [expSubOneDiv, dslope_same, Complex.deriv_exp]
  · rw [expSubOneDiv, ite_eq_right_iff.mpr (fun h => absurd h ht), dslope_of_ne _ ht, slope_def_field, exp_zero, sub_zero]

/-- `expSubOneDiv` is entire. -/
theorem analyticAt_expSubOneDiv (t : ℂ) : AnalyticAt ℂ expSubOneDiv t := by
  rw [expSubOneDiv_eq_dslope]
  have h : DifferentiableOn ℂ (dslope exp 0) Set.univ :=
    (differentiableOn_dslope Filter.univ_mem).mpr differentiable_exp.differentiableOn
  exact h.analyticAt Filter.univ_mem

/-- The generating function is analytic at `0`. -/
theorem analyticAt_largeDenominatorGenerating (a b c z : ℂ) :
    AnalyticAt ℂ (largeDenominatorGenerating a b c z) 0 := by
  have h1 : expSubOneDiv 0 ∈ slitPlane := by simp [expSubOneDiv]
  have h2 : (1 - z + z * exp (-(0 : ℂ))) ∈ slitPlane := by simp
  unfold largeDenominatorGenerating
  exact (((analyticAt_expSubOneDiv 0).cpow analyticAt_const h1).mul
    ((analyticAt_id.mul analyticAt_const).cexp)).mul
    (((analyticAt_const.sub analyticAt_const).add
      (analyticAt_const.mul (analyticAt_id.neg.cexp))).cpow analyticAt_const h2)

@[dlmf 15.12.E4]
theorem large_denominator_generating_hasSum (a b c z : ℂ) :
    ∃ r : ℝ, 0 < r ∧ ∀ t : ℂ, ‖t‖ < r →
      HasSum (fun n : ℕ => largeDenominatorCoeff a b c z n * t ^ n)
        (largeDenominatorGenerating a b c z t) := by
  obtain ⟨r, hr, h⟩ := (analyticAt_largeDenominatorGenerating a b c z).exists_ball_analyticOnNhd
  refine ⟨r, hr, fun t ht => ?_⟩
  have hs := Complex.hasSum_taylorSeries_on_ball h.differentiableOn (z := t) (by simpa using ht)
  refine hs.congr_fun fun n => ?_
  simp only [largeDenominatorCoeff, sub_zero, smul_eq_mul]
  ring


/-! ### The shifted large-denominator expansion 15.12.3

For `re b > 0`, Euler's integral 15.6.1 in the variable `s = 1 - e^{-t}` is the Laplace transform
`∫₀^∞ e^{-λt} t^{b-1} q(t) dt` of the generating function 15.12.4, and Watson's lemma gives 15.12.3
(`hcub_largeDen_base`). For every `b`, the expansion 15.12.2 along the ray `c + λ`
(`hcub_large_denominator_shift`) multiplied by the Gamma-ratio expansion 5.11.13 gives an
expansion of the same function with explicit coefficients `hcub_largeDenMix`
(`hcub_largeDen_mix`). Uniqueness of asymptotic expansions identifies the coefficients for
`re b > 0`; both sides are entire in `b` (the Taylor coefficients `q_k` through Cauchy's integral
formula, `hcub_differentiable_iteratedDeriv`), so the identity theorem gives the coefficient
identity for all `b` (`hcub_largeDenMix_eq`). The same scheme proves 13.8.2 in
`DLMF.Confluent.Asymptotics`.
-/

section ShiftExpansion

open MeasureTheory Set Asymptotics
open scoped Nat

theorem hcub_ofReal_cpow_exp (t : ℝ) (w : ℂ) :
    ((Real.exp t : ℝ) : ℂ) ^ w = exp (t * w) := by
  rw [cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos t).ne'), ← ofReal_log (Real.exp_pos t).le,
    Real.log_exp]

theorem hcub_image : (fun t : ℝ => 1 - Real.exp (-t)) '' Ioi 0 = Ioo 0 1 := by
  ext s
  simp only [mem_image, mem_Ioi, mem_Ioo]
  constructor
  · rintro ⟨t, ht, rfl⟩
    have h1 : Real.exp (-t) < 1 := by
      rw [show (1:ℝ) = Real.exp 0 from Real.exp_zero.symm]; exact Real.exp_lt_exp.mpr (by linarith)
    exact ⟨by linarith, by linarith [Real.exp_pos (-t)]⟩
  · rintro ⟨h0, h1⟩
    refine ⟨-Real.log (1 - s), ?_, ?_⟩
    · have : Real.log (1 - s) < 0 := Real.log_neg (by linarith) (by linarith)
      linarith
    · rw [neg_neg, Real.exp_log (by linarith)]; ring

theorem hcub_hasDerivWithinAt (t : ℝ) :
    HasDerivWithinAt (fun t : ℝ => 1 - Real.exp (-t)) (Real.exp (-t)) (Ioi 0) t := by
  have h := ((Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_neg t)).const_sub 1
  refine (h.congr_deriv ?_).hasDerivWithinAt
  simp

theorem hcub_injOn : InjOn (fun t : ℝ => 1 - Real.exp (-t)) (Ioi 0) := by
  intro x _ y _ h
  have : Real.exp (-x) = Real.exp (-y) := by simp only at h; linarith
  have := Real.exp_injective this
  linarith

theorem hcub_cpow_mul_cpow_neg {b : ℝ} (hb : 0 < b) (a : ℂ) (s : ℕ) :
    (b : ℂ) ^ a * (b : ℂ) ^ (-((s : ℂ) + a)) = ((b : ℂ)⁻¹) ^ s := by
  have hb0 : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  rw [← cpow_add _ _ hb0, show a + -((s : ℂ) + a) = -(s : ℂ) by ring, cpow_neg, cpow_natCast,
    inv_pow]

/-- `b^p Γ(b+c-p)/Γ(b+c+s) = ∑_{k<n-s} G_k b^{-s-k} + O(b^{-n})`, from the Gamma-ratio
expansion 5.11.13. -/
theorem hcub_ratio_shift (p c : ℂ) {s n : ℕ} (hs : s ≤ n) :
    (fun b : ℝ => (b : ℂ) ^ p * Gamma ((b : ℂ) + (c - p)) / Gamma ((b : ℂ) + (c + s)) -
      ∑ k ∈ Finset.range (n - s),
        DLMF.Gamma.stirlingRatioG (c - p) (c + s) k * ((b : ℂ)⁻¹) ^ (s + k))
      =O[atTop] fun b => ((b : ℂ)⁻¹) ^ n := by
  have h := DLMF.Gamma.Gamma_ratio_expansion (c - p) (c + s) (n - s)
  have hm := (isBigO_refl (fun b : ℝ => (b : ℂ) ^ p) atTop).mul h
  refine hm.congr' ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with b hb
    have hb0 : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
    rw [mul_sub, Finset.mul_sum, Finset.mul_sum]
    congr 1
    · ring
    · refine Finset.sum_congr rfl fun k _ => ?_
      have := hcub_cpow_mul_cpow_neg hb p s
      rw [show c - p - (c + s) = -((s : ℂ) + p) by ring, pow_add, ← this, inv_pow]
      ring
  · filter_upwards [eventually_gt_atTop 0] with b hb
    rw [show c - p - (c + s) - ((n - s : ℕ) : ℂ) = -((n : ℂ) + p) by push_cast [hs]; ring,
      hcub_cpow_mul_cpow_neg hb]

/-- The scale `b ↦ b^{-n}` (complex-valued) at `+∞`. -/
theorem hcub_isAsymptoticScale :
    IsAsymptoticScale atTop (fun (n : ℕ) (b : ℝ) => ((b : ℂ)⁻¹) ^ n) := by
  intro n
  have h0 : (fun b : ℝ => (b : ℂ)⁻¹) =o[atTop] (fun _ => (1 : ℂ)) := by
    rw [isLittleO_one_iff]
    have := (continuous_ofReal.tendsto (0 : ℝ)).comp tendsto_inv_atTop_zero
    simpa [Function.comp_def] using this
  have := h0.mul_isBigO (isBigO_refl (fun b : ℝ => ((b : ℂ)⁻¹) ^ n) atTop)
  simpa [pow_succ, mul_comm] using this

theorem hcub_frequently_ne (n : ℕ) : ∃ᶠ b : ℝ in atTop, ((b : ℂ)⁻¹) ^ n ≠ 0 := by
  refine (eventually_gt_atTop (0 : ℝ)).mono (fun b hb => ?_) |>.frequently
  exact pow_ne_zero _ (inv_ne_zero (by exact_mod_cast hb.ne'))

theorem hcub_differentiable_stirlingRatioG (c : ℂ) (k : ℕ) :
    Differentiable ℂ (fun x => DLMF.Gamma.stirlingRatioG x c k) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases k with _ | n
    · have : (fun x => DLMF.Gamma.stirlingRatioG x c 0) = fun _ => 1 := by
        funext x; rw [DLMF.Gamma.stirlingRatioG]
      rw [this]; exact differentiable_const _
    · have : (fun x => DLMF.Gamma.stirlingRatioG x c (n + 1)) = fun x =>
          (∑ k : Fin (n + 1), (-1 : ℂ) ^ k.val *
            (Polynomial.aeval x (Polynomial.bernoulli (k.val + 2)) -
              Polynomial.aeval c (Polynomial.bernoulli (k.val + 2))) / (k.val + 2) *
            DLMF.Gamma.stirlingRatioG x c (n - k.val)) / (n + 1) := by
        funext x; rw [DLMF.Gamma.stirlingRatioG]
      rw [this]
      refine Differentiable.div_const (Differentiable.fun_sum fun k _ => ?_) _
      exact (((differentiable_const _).mul ((Polynomial.differentiable_aeval _).sub
        (differentiable_const _))).div_const _).mul (ih _ (by omega))

theorem hcub_expSubOneDiv_re_pos {t : ℂ} (ht : ‖t‖ ≤ 1 / 2) : 0 < (expSubOneDiv t).re := by
  rcases eq_or_ne t 0 with rfl | ht0
  · simp [expSubOneDiv]
  have h := Complex.norm_exp_sub_one_sub_id_le (x := t) (by linarith)
  have hE : expSubOneDiv t - 1 = (exp t - 1 - t) / t := by
    rw [expSubOneDiv, ite_eq_right_iff.mpr (fun h => absurd h ht0)]; field_simp
  have hn : ‖expSubOneDiv t - 1‖ ≤ 1 / 2 := by
    rw [hE, norm_div]
    have : 0 < ‖t‖ := norm_pos_iff.mpr ht0
    rw [div_le_iff₀ this]; nlinarith
  have h1 := Complex.abs_re_le_norm (expSubOneDiv t - 1)
  rw [Complex.sub_re, Complex.one_re] at h1
  have h2 := abs_le.mp (h1.trans hn)
  linarith [h2.1]

theorem hcub_expSubOneDiv_mem_slitPlane {t : ℂ} (ht : ‖t‖ ≤ 1 / 2) : expSubOneDiv t ∈ slitPlane :=
  mem_slitPlane_iff.mpr (Or.inl (hcub_expSubOneDiv_re_pos ht))

/-- Holomorphy in a parameter of Taylor coefficients, through Cauchy's integral formula on the
circle of radius `r`. -/
theorem hcub_differentiable_iteratedDeriv {G : ℂ → ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hcont : ∀ a : ℂ, ∀ t : ℂ, ‖t‖ = r → ContinuousAt (fun p : ℂ × ℂ => G p.1 p.2) (a, t))
    (hdt : ∀ a : ℂ, DifferentiableOn ℂ (G a) (Metric.closedBall 0 r))
    (hda : ∀ t : ℂ, ‖t‖ = r → Differentiable ℂ (fun a => G a t)) (N : ℕ) :
    Differentiable ℂ (fun a => iteratedDeriv N (G a) 0) := by
  exact Complex.differentiable_iteratedDeriv_param hr hcont hdt hda N


/-- `(re C)_n ≤ ‖(C)_n‖` when `re C ≥ 0`. -/
theorem hcub_poch_re_le_norm {C : ℂ} (hC : 0 ≤ C.re) (n : ℕ) :
    (ascPochhammer ℝ n).eval C.re ≤ ‖poch C n‖ := by
  induction n with
  | zero => simp [poch]
  | succ n ih =>
    rw [ascPochhammer_succ_eval, poch, ascPochhammer_succ_eval, norm_mul]
    have h1 : C.re + n ≤ ‖C + n‖ := by
      have := Complex.re_le_norm (C + n); simpa using this
    exact mul_le_mul ih h1 (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]) (norm_nonneg _)

lemma hcub_div_le_aux {A A' P F M R : ℝ} (hA : 0 ≤ A) (hAA' : A ≤ A') (hP : 0 < P) (hF : 0 < F)
    (hR : 0 < R) (hRF : R * F ≤ M * P) : A / (P * F) ≤ M * R⁻¹ * (A' / (F * F)) := by
  have hA' : 0 ≤ A' := hA.trans hAA'
  calc A / (P * F) ≤ A' / (P * F) := div_le_div_of_nonneg_right hAA' (by positivity)
    _ ≤ M * R⁻¹ * (A' / (F * F)) := by
      rw [div_le_iff₀ (by positivity)]
      field_simp
      nlinarith [mul_le_mul_of_nonneg_left hRF (by positivity : 0 ≤ A' * F)]

/-- The large-denominator expansion 15.12.2 along a shifted ray `c + λ`, `λ → +∞`, with complex
`c`. -/
theorem hcub_large_denominator_shift (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) (m : ℕ) :
    (fun l : ℝ => ₂F₁ a b (c + l) z - ∑ k ∈ Finset.range m, gaussHGCoeff a b (c + l) k * z ^ k)
      =O[atTop] fun l : ℝ => ((l : ℂ)⁻¹) ^ m := by
  set g : ℕ → ℝ := fun k => ‖gaussHGCoeff (‖a‖ : ℂ) (‖b‖ : ℂ) 1 k * z ^ k‖ with hg
  have hgs : Summable g := summable_norm_gaussHGCoeff_mul_pow _ _ _ hz
  refine Asymptotics.IsBigO.of_bound (m.factorial * 2 ^ m * ∑' k, g k) ?_
  filter_upwards [eventually_ge_atTop (2 + 2 * |c.re|)] with l hl
  have hca := neg_abs_le c.re
  have hca' := abs_nonneg c.re
  set ρ := c.re + l with hρ
  have hρ1 : 1 ≤ ρ := by linarith
  have hρl : l / 2 ≤ ρ := by linarith
  have hl0 : 0 < l := by linarith
  set C : ℂ := c + l with hC
  have hCre : C.re = ρ := by simp [hC, hρ]
  set f : ℕ → ℂ := fun k => gaussHGCoeff a b C k * z ^ k with hf
  have hfs : Summable f := (summable_norm_gaussHGCoeff_mul_pow a b C hz).of_norm
  have hF : ₂F₁ a b C z = ∑' k, f k := by
    rw [ordinaryHypergeometric_eq_tsum]
    simp only [smul_eq_mul, hf]
    congr 1
    funext n
    simp [gaussHGCoeff, poch, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
  rw [hF, ← hfs.sum_add_tsum_nat_add m, add_sub_cancel_left]
  have hbd : ∀ k, ‖f (k + m)‖ ≤ m.factorial * (ρ ^ m)⁻¹ * g (k + m) := by
    intro k
    have hpos := pow_mul_factorial_le_poch hρ1 (Nat.le_add_left m k)
    have hpc := hcub_poch_re_le_norm (C := C) (by rw [hCre]; linarith) (k + m)
    rw [hCre] at hpc
    have ha := norm_ascPochhammer_eval_le (le_refl ‖a‖) (k + m)
    have hb := norm_ascPochhammer_eval_le (le_refl ‖b‖) (k + m)
    have hfac : (0 : ℝ) < (k + m).factorial := by positivity
    have hP : 0 < (ascPochhammer ℝ (k + m)).eval ρ := ascPochhammer_pos _ _ (by linarith)
    have hPC : 0 < ‖poch C (k + m)‖ := hP.trans_le hpc
    have e1 : ‖f (k + m)‖ = (‖poch a (k + m)‖ * ‖poch b (k + m)‖ * ‖z‖ ^ (k + m)) /
        (‖poch C (k + m)‖ * (k + m).factorial) := by
      simp only [hf, gaussHGCoeff, norm_mul, norm_div, norm_pow, Complex.norm_natCast]; ring
    have e2 : g (k + m) = (‖poch (‖a‖ : ℂ) (k + m)‖ * ‖poch (‖b‖ : ℂ) (k + m)‖ * ‖z‖ ^ (k + m)) /
        ((k + m).factorial * (k + m).factorial) := by
      simp only [hg, gaussHGCoeff, norm_mul, norm_div, norm_pow, Complex.norm_natCast,
        poch_nat_one]; ring
    rw [e1, e2]
    refine hcub_div_le_aux (by positivity) ?_ hPC hfac (by positivity) ?_
    · gcongr
    · nlinarith [hpos, hpc, (by positivity : (0 : ℝ) ≤ m.factorial)]
  have hgs' : Summable fun k => g (k + m) := (summable_nat_add_iff m).mpr hgs
  have hnorm : ‖∑' k, f (k + m)‖ ≤ m.factorial * (ρ ^ m)⁻¹ * ∑' k, g k := by
    calc ‖∑' k, f (k + m)‖ ≤ ∑' k, m.factorial * (ρ ^ m)⁻¹ * g (k + m) :=
          tsum_of_norm_bounded (hgs'.mul_left _).hasSum hbd
      _ = m.factorial * (ρ ^ m)⁻¹ * ∑' k, g (k + m) := tsum_mul_left
      _ ≤ m.factorial * (ρ ^ m)⁻¹ * ∑' k, g k := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [← hgs.sum_add_tsum_nat_add m]
          have : 0 ≤ ∑ i ∈ Finset.range m, g i := Finset.sum_nonneg fun i _ => norm_nonneg _
          linarith
  have hρm : (ρ ^ m)⁻¹ ≤ 2 ^ m * (l ^ m)⁻¹ := by
    rw [← inv_pow, ← inv_pow, ← mul_pow]
    gcongr
    rw [inv_le_comm₀ (by linarith) (by positivity), mul_inv, inv_inv]
    linarith
  have hS : 0 ≤ ∑' k, g k := tsum_nonneg fun k => norm_nonneg _
  rw [norm_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hl0, inv_pow]
  calc ‖∑' k, f (k + m)‖ ≤ m.factorial * (ρ ^ m)⁻¹ * ∑' k, g k := hnorm
    _ ≤ m.factorial * (2 ^ m * (l ^ m)⁻¹) * ∑' k, g k := by gcongr
    _ = _ := by ring


theorem hcub_largeDen_taylor (a b c z : ℂ) (N : ℕ) :
    (fun t => largeDenominatorGenerating a b c z t -
      ∑ n ∈ Finset.range N, largeDenominatorCoeff a b c z n * t ^ n) =O[𝓝 0] fun t => ‖t‖ ^ N := by
  have h := (analyticAt_largeDenominatorGenerating a b c z).hasFPowerSeriesAt.isBigO_sub_partialSum_pow
    N
  refine h.congr' (Eventually.of_forall fun s => ?_) EventuallyEq.rfl
  simp only [zero_add, FormalMultilinearSeries.partialSum,
    FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, largeDenominatorCoeff]

/-- Euler's integrand for `F(a,b;c+λ;z)` in the variable `s = 1 - e^{-t}`. -/
theorem hcub_subst₂ (a b c z : ℂ) (l : ℝ) {t : ℝ} (ht : 0 < t) :
    |Real.exp (-t)| • (((1 - Real.exp (-t) : ℝ) : ℂ) ^ (b - 1) *
      (1 - ((1 - Real.exp (-t) : ℝ) : ℂ)) ^ (c + l - b - 1) *
        (1 - z * ((1 - Real.exp (-t) : ℝ) : ℂ)) ^ (-a)) =
    Real.exp (-l * t) • ((t : ℂ) ^ (b - 1) * largeDenominatorGenerating a b c z t) := by
  set E : ℝ := (Real.exp t - 1) / t with hE
  have hE0 : 0 < E := div_pos (by linarith [Real.add_one_lt_exp ht.ne']) ht
  have hEc : expSubOneDiv (t : ℂ) = (E : ℂ) := by
    rw [expSubOneDiv, ite_eq_right_iff.mpr (fun h => absurd h (by exact_mod_cast ht.ne')), hE]
    push_cast; rfl
  have hs : (1 - Real.exp (-t) : ℝ) = Real.exp (-t) * (t * E) := by
    rw [hE, Real.exp_neg]; field_simp
  have hc : ((1 - Real.exp (-t) : ℝ) : ℂ) ^ (b - 1) =
      exp (-(t : ℂ) * (b - 1)) * ((t : ℂ) ^ (b - 1) * (E : ℂ) ^ (b - 1)) := by
    rw [hs, Complex.ofReal_mul, mul_cpow_ofReal_nonneg (Real.exp_pos _).le
      (by positivity), Complex.ofReal_mul, mul_cpow_ofReal_nonneg ht.le hE0.le, hcub_ofReal_cpow_exp]
    push_cast; ring_nf
  have hw : (1 - z * ((1 - Real.exp (-t) : ℝ) : ℂ)) = 1 - z + z * exp (-(t : ℂ)) := by
    push_cast; ring
  rw [hc, show (1 : ℂ) - ((1 - Real.exp (-t) : ℝ) : ℂ) = ((Real.exp (-t) : ℝ) : ℂ) by push_cast; ring,
    hcub_ofReal_cpow_exp, abs_of_pos (Real.exp_pos _), Complex.real_smul,
    Complex.real_smul, largeDenominatorGenerating, hEc, hw]
  set W := (1 - z + z * exp (-(t : ℂ))) ^ (-a)
  push_cast
  have e1 : exp (-(t : ℂ)) * (exp (-(t : ℂ) * (b - 1)) * ((t : ℂ) ^ (b - 1) * (E : ℂ) ^ (b - 1)) *
      exp (-(t : ℂ) * (c + l - b - 1)) * W) =
      (t : ℂ) ^ (b - 1) * (E : ℂ) ^ (b - 1) * W *
        exp (-(t : ℂ) + -(t : ℂ) * (b - 1) + -(t : ℂ) * (c + l - b - 1)) := by
    simp only [Complex.exp_add]; ring
  have e2 : exp (-(l : ℂ) * t) * ((t : ℂ) ^ (b - 1) * ((E : ℂ) ^ (b - 1) *
      exp (t * (1 - c)) * W)) =
      (t : ℂ) ^ (b - 1) * (E : ℂ) ^ (b - 1) * W * exp (-(l : ℂ) * t + t * (1 - c)) := by
    simp only [Complex.exp_add]; ring
  rw [e1, e2]
  congr 2
  ring

theorem hcub_euler_eq_laplace₂ (a b c z : ℂ) (l : ℝ) :
    ∫ s : ℝ in (0 : ℝ)..1, (s : ℂ) ^ (b - 1) * (1 - (s : ℂ)) ^ (c + l - b - 1) *
      (1 - z * s) ^ (-a) =
      ∫ t in Ioi (0 : ℝ), Real.exp (-l * t) •
        ((t : ℂ) ^ (b - 1) * largeDenominatorGenerating a b c z t) := by
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo, ← hcub_image,
    integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi (fun t _ => hcub_hasDerivWithinAt t)
      hcub_injOn]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  exact hcub_subst₂ a b c z l ht

theorem hcub_one_sub_mul_mem_slitPlane {z : ℂ} (hz : ‖z‖ < 1) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    1 - z * s ∈ slitPlane := by
  refine mem_slitPlane_iff.mpr (Or.inl ?_)
  have h1 : ‖z * s‖ < 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1]
    nlinarith [hs.2, norm_nonneg z]
  have h2 := Complex.re_le_norm (z * s)
  simp only [sub_re, one_re]
  linarith

theorem hcub_integrableOn₂ (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) (hb : 0 < b.re) {l : ℝ}
    (hl : (b - c).re < l) :
    IntegrableOn (fun t : ℝ => Real.exp (-l * t) •
      ((t : ℂ) ^ (b - 1) * largeDenominatorGenerating a b c z t)) (Ioi 0) := by
  have hβ := betaIntegral_convergent (u := b) (v := c + l - b) hb (by simp at hl ⊢; linarith)
  have hcont : ContinuousOn (fun s : ℝ => (1 - z * s) ^ (-a)) (Icc 0 1) := fun s hs =>
    ((continuous_const.sub (continuous_const.mul continuous_ofReal)).continuousAt.cpow
      continuousAt_const (hcub_one_sub_mul_mem_slitPlane hz hs)).continuousWithinAt
  have h1 : IntervalIntegrable (fun s : ℝ => (s : ℂ) ^ (b - 1) * (1 - (s : ℂ)) ^ (c + l - b - 1) *
      (1 - z * s) ^ (-a)) volume 0 1 := by
    refine hβ.mul_continuousOn ?_
    rwa [uIcc_of_le zero_le_one]
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at h1
  have h2 := h1.mono_set Ioo_subset_Ioc_self
  rw [← hcub_image, integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi
    (fun t _ => hcub_hasDerivWithinAt t) hcub_injOn] at h2
  refine h2.congr_fun (fun t ht => hcub_subst₂ a b c z l ht) measurableSet_Ioi


/-- Watson's lemma for the Laplace form of Euler's integral: 15.12.3 when `re b > 0`. -/
theorem hcub_largeDen_base (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) (hb : 0 < b.re) (m : ℕ) :
    (fun l : ℝ => Gamma (c - b + l) / Gamma (c + l) * (l : ℂ) ^ b * ₂F₁ a b (c + l) z -
       ∑ k ∈ Finset.range m, poch b k * largeDenominatorCoeff a b c z k * ((l : ℂ)⁻¹) ^ k)
      =O[atTop] fun l => ((l : ℂ)⁻¹) ^ m := by
  set F : ℝ → ℂ := fun t => (t : ℂ) ^ (b - 1) * largeDenominatorGenerating a b c z t with hFdef
  have hF : ∀ N : ℕ, (fun t : ℝ => F t - ∑ k ∈ Finset.range N,
      ((t : ℂ) ^ ((k : ℂ) + b - 1)) • largeDenominatorCoeff a b c z k) =O[𝓝[>] 0]
        fun t : ℝ => t ^ ((N : ℝ) + b.re - 1) := by
    intro N
    have hT : (fun t : ℝ => largeDenominatorGenerating a b c z t - ∑ k ∈ Finset.range N,
        largeDenominatorCoeff a b c z k * (t : ℂ) ^ k) =O[𝓝[>] 0]
          fun t : ℝ => ‖(t : ℂ)‖ ^ N := by
      have hc : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[>] 0) (𝓝 0) := by
        have := (continuous_ofReal.tendsto (0 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
        simpa using this
      exact (hcub_largeDen_taylor a b c z N).comp_tendsto hc
    have hT' : (fun t : ℝ => largeDenominatorGenerating a b c z t - ∑ k ∈ Finset.range N,
        largeDenominatorCoeff a b c z k * (t : ℂ) ^ k) =O[𝓝[>] 0] fun t : ℝ => (t : ℂ) ^ N :=
      hT.trans (IsBigO.of_bound 1 (Eventually.of_forall fun t => by simp))
    have hm := (isBigO_refl (fun t : ℝ => (t : ℂ) ^ (b - 1)) (𝓝[>] 0)).mul hT'
    refine (hm.congr' ?_ EventuallyEq.rfl).trans (IsBigO.of_bound 1 ?_)
    · filter_upwards [self_mem_nhdsWithin] with t ht
      have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt ht)
      simp only [hFdef, mul_sub, Finset.mul_sum, smul_eq_mul]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [show (k : ℂ) + b - 1 = (k : ℂ) + (b - 1) by ring, cpow_add _ _ ht0, cpow_natCast]
      ring
    · filter_upwards [self_mem_nhdsWithin] with t ht
      have ht' : (0 : ℝ) < t := ht
      rw [norm_mul, norm_pow, Complex.norm_cpow_eq_rpow_re_of_pos ht', Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos ht', Real.norm_eq_abs,
        abs_of_pos (Real.rpow_pos_of_pos ht' _), one_mul,
        show (N : ℝ) + b.re - 1 = (b - 1).re + N by simp; ring, Real.rpow_add ht',
        Real.rpow_natCast]
  have hW := hasAsymptoticExpansion_integral_exp_smul_cpow (μ := b) (c := (b - c).re + 1) hb
    (hcub_integrableOn₂ a b c hz hb (by linarith)) hF m
  have hm := (isBigO_refl (fun l : ℝ => (l : ℂ) ^ b / Gamma b) atTop).mul hW
  have hGb : Gamma b ≠ 0 := Gamma_ne_zero (not_neg_nat_of_re_pos hb)
  refine (hm.congr' ?_ ?_).trans (isBigO_const_mul_self (Gamma b)⁻¹ _ atTop)
  · filter_upwards [eventually_gt_atTop ((b - c).re + 1), eventually_gt_atTop 0] with l hl hl0
    have hcb : 0 < (c + l - b).re := by simp at hl ⊢; linarith
    have hcl : 0 < (c + l).re := by
      have : (c + l).re = (c + l - b).re + b.re := by simp
      linarith
    have hG1 : Gamma (c + l) ≠ 0 := Gamma_ne_zero (not_neg_nat_of_re_pos hcl)
    have hG2 : Gamma (c + l - b) ≠ 0 := Gamma_ne_zero (not_neg_nat_of_re_pos hcb)
    rw [ordinaryHypergeometric_eq_integral hb hcb hz, hcub_euler_eq_laplace₂,
      show c - b + (l : ℂ) = c + l - b by ring]
    simp only [smul_eq_mul, mul_sub, Finset.mul_sum]
    congr 1
    · field_simp
    · refine Finset.sum_congr rfl fun s _ => ?_
      have hp : Gamma ((s : ℂ) + b) = Gamma b * poch b s := by
        have h1 := DLMF.Gamma.poch_mul_recip_Gamma_add_nat b s
        have h2 : Gamma (b + s) ≠ 0 := Gamma_ne_zero (not_neg_nat_of_re_pos (by simp; positivity))
        rw [add_comm]
        field_simp at h1
        linear_combination -h1
      rw [hp, ← hcub_cpow_mul_cpow_neg hl0 b s]
      field_simp
  · filter_upwards [eventually_gt_atTop 0] with l hl
    rw [← hcub_cpow_mul_cpow_neg hl b m]
    field_simp

/-- Coefficients of 15.12.2 (on the ray `c + λ`) re-expanded in powers of `1/λ` after
multiplication by `λ^b Γ(c-b+λ)/Γ(c+λ)`. -/
noncomputable def hcub_largeDenMix (a b c z : ℂ) (N : ℕ) : ℂ :=
  ∑ k ∈ Finset.range (N + 1), poch a k * poch b k * z ^ k / k ! *
    DLMF.Gamma.stirlingRatioG (c - b) (c + k) (N - k)

/-- 15.12.2 on the ray `c + λ` re-expanded, for all `b`. -/
theorem hcub_largeDen_mix (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) (m : ℕ) :
    (fun l : ℝ => Gamma (c - b + l) / Gamma (c + l) * (l : ℂ) ^ b * ₂F₁ a b (c + l) z -
       ∑ N ∈ Finset.range m, hcub_largeDenMix a b c z N * ((l : ℂ)⁻¹) ^ N)
      =O[atTop] fun l => ((l : ℂ)⁻¹) ^ m := by
  have h1 := hcub_large_denominator_shift a b c hz m
  have hR : (fun l : ℝ => (l : ℂ) ^ b * Gamma ((l : ℂ) + (c - b)) / Gamma ((l : ℂ) + (c + 0)))
      =O[atTop] fun _ => (1 : ℂ) := by
    have h := hcub_ratio_shift b c (s := 0) (n := 0) le_rfl
    simpa using h
  have h2 := (hR.mul h1).congr_right fun l => one_mul _
  have h3 : (fun l : ℝ => ∑ k ∈ Finset.range m, poch a k * poch b k * z ^ k / k ! *
      ((l : ℂ) ^ b * Gamma ((l : ℂ) + (c - b)) / Gamma ((l : ℂ) + (c + k)) -
        ∑ j ∈ Finset.range (m - k),
          DLMF.Gamma.stirlingRatioG (c - b) (c + k) j * ((l : ℂ)⁻¹) ^ (k + j)))
      =O[atTop] fun l => ((l : ℂ)⁻¹) ^ m :=
    IsBigO.fun_sum fun k hk => (hcub_ratio_shift b c
      (Finset.mem_range.mp hk).le).const_mul_left _
  refine (h2.add h3).congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_gt_atTop (|c.re| + 1)] with l hl
  have hca := neg_abs_le c.re
  have hcl : 0 < (c + l).re := by simp; linarith
  have hcl' : ∀ k : ℕ, c + l ≠ -k := not_neg_nat_of_re_pos hcl
  have hflip := Finset.sum_range_diag_flip m fun k j =>
    poch a k * poch b k * z ^ k / k ! *
      (DLMF.Gamma.stirlingRatioG (c - b) (c + k) j * ((l : ℂ)⁻¹) ^ (k + j))
  simp only [hcub_largeDenMix, Finset.sum_mul]
  have hN : ∀ n ∈ Finset.range m, ∑ k ∈ Finset.range (n + 1),
      poch a k * poch b k * z ^ k / k ! * DLMF.Gamma.stirlingRatioG (c - b) (c + k) (n - k) *
        ((l : ℂ)⁻¹) ^ n =
      ∑ k ∈ Finset.range (n + 1), poch a k * poch b k * z ^ k / k ! *
        (DLMF.Gamma.stirlingRatioG (c - b) (c + k) (n - k) * ((l : ℂ)⁻¹) ^ (k + (n - k))) := by
    intro n _
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Nat.add_sub_cancel' (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))]
    ring
  rw [Finset.sum_congr rfl hN, hflip]
  have hS : ∀ k ∈ Finset.range m, gaussHGCoeff a b (c + l) k * z ^ k *
      ((l : ℂ) ^ b * Gamma ((l : ℂ) + (c - b)) / Gamma ((l : ℂ) + (c + 0))) =
      poch a k * poch b k * z ^ k / k ! *
        ((l : ℂ) ^ b * Gamma ((l : ℂ) + (c - b)) / Gamma ((l : ℂ) + (c + k))) := by
    intro k _
    have h := DLMF.Gamma.poch_mul_recip_Gamma_add_nat (c + l) k
    have hp : poch (c + l) k ≠ 0 := poch_ne_zero_of_not_neg_nat hcl' k
    have hGs : Gamma (c + l + k) ≠ 0 := Gamma_ne_zero (not_neg_nat_of_re_pos (by
      simp at hcl ⊢; positivity))
    have hG0 : Gamma (c + l) ≠ 0 := Gamma_ne_zero hcl'
    have hf : (k ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    field_simp at h
    rw [show (l : ℂ) + (c + k) = c + l + k by ring, show (l : ℂ) + (c + 0) = c + l by ring,
      ← h, gaussHGCoeff]
    field_simp
  have hX : Gamma (c - b + l) / Gamma (c + l) * (l : ℂ) ^ b =
      (l : ℂ) ^ b * Gamma ((l : ℂ) + (c - b)) / Gamma ((l : ℂ) + (c + 0)) := by
    rw [show (l : ℂ) + (c - b) = c - b + l by ring, show (l : ℂ) + (c + 0) = c + l by ring]; ring
  rw [hX]
  simp only [mul_sub, Finset.mul_sum] at *
  rw [Finset.sum_congr rfl (fun s hs => (mul_comm _ _).trans (hS s hs))]
  simp only [Finset.sum_sub_distrib]
  ring


/-- For `re b > 0` the re-expanded coefficients of 15.12.2 are those of 15.12.3. -/
theorem hcub_largeDenMix_eq_of_re_pos (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) (hb : 0 < b.re)
    (N : ℕ) : hcub_largeDenMix a b c z N = poch b N * largeDenominatorCoeff a b c z N := by
  have h := HasAsymptoticExpansion.unique hcub_isAsymptoticScale hcub_frequently_ne
    (a := hcub_largeDenMix a b c z) (b := fun N => poch b N * largeDenominatorCoeff a b c z N)
    (f := fun l : ℝ => Gamma (c - b + l) / Gamma (c + l) * (l : ℂ) ^ b * ₂F₁ a b (c + l) z)
    (fun n => (hcub_largeDen_mix a b c hz n).congr_left fun l => by
      simp only [smul_eq_mul]; congr 1; exact Finset.sum_congr rfl fun _ _ => mul_comm _ _)
    (fun n => (hcub_largeDen_base a b c hz hb n).congr_left fun l => by
      simp only [smul_eq_mul]; congr 1; exact Finset.sum_congr rfl fun _ _ => mul_comm _ _)
  exact congrFun h N

theorem hcub_differentiable_largeDenMix (a c z : ℂ) (N : ℕ) :
    Differentiable ℂ (fun b => hcub_largeDenMix a b c z N) := by
  unfold hcub_largeDenMix
  refine Differentiable.fun_sum fun k _ => ?_
  exact ((((differentiable_const _).mul (Polynomial.differentiable _)).mul
    (differentiable_const _)).div_const _).mul
    ((hcub_differentiable_stirlingRatioG _ _).comp ((differentiable_const _).sub differentiable_id))

theorem hcub_one_sub_exp_mem_slitPlane {z : ℂ} (hz : ‖z‖ < 1) {t : ℂ} (ht : ‖t‖ ≤ 1 / 2) :
    1 - z + z * exp (-t) ∈ slitPlane := by
  refine mem_slitPlane_iff.mpr (Or.inl ?_)
  have h1 : ‖exp (-t) - 1‖ ≤ 1 := by
    have := Complex.norm_exp_sub_one_le (x := -t) (by rw [norm_neg]; linarith)
    rw [norm_neg] at this; linarith
  have h2 : ‖z * (exp (-t) - 1)‖ < 1 := by
    rw [norm_mul]; nlinarith [norm_nonneg z, norm_nonneg (exp (-t) - 1)]
  have h3 := abs_le.mp (Complex.abs_re_le_norm (z * (exp (-t) - 1)))
  have : 1 - z + z * exp (-t) = 1 + z * (exp (-t) - 1) := by ring
  rw [this, add_re, one_re]
  linarith [h3.1]

theorem hcub_differentiable_largeDenominatorCoeff (a c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) (N : ℕ) :
    Differentiable ℂ (fun b => largeDenominatorCoeff a b c z N) := by
  have hE : ∀ t : ℂ, DifferentiableAt ℂ expSubOneDiv t := fun t =>
    (analyticAt_expSubOneDiv t).differentiableAt
  have hrest : ∀ t : ℂ, ‖t‖ ≤ 1 / 2 → DifferentiableAt ℂ
      (fun t : ℂ => exp (t * (1 - c)) * (1 - z + z * exp (-t)) ^ (-a)) t := fun t ht =>
    (by fun_prop : DifferentiableAt ℂ (fun t : ℂ => exp (t * (1 - c))) t).mul
      ((by fun_prop : DifferentiableAt ℂ (fun t : ℂ => 1 - z + z * exp (-t)) t).cpow
        (differentiableAt_const _) (hcub_one_sub_exp_mem_slitPlane hz ht))
  have h := hcub_differentiable_iteratedDeriv (G := fun b t => largeDenominatorGenerating a b c z t)
    (r := 1 / 2) (by norm_num)
    (fun b t ht => by
      have hEc : ContinuousAt (fun p : ℂ × ℂ => expSubOneDiv p.2) (b, t) :=
        ContinuousAt.comp (f := fun p : ℂ × ℂ => p.2) (g := expSubOneDiv) (hE t).continuousAt
          continuous_snd.continuousAt
      have hpow : ContinuousAt (fun p : ℂ × ℂ => expSubOneDiv p.2 ^ (p.1 - 1)) (b, t) :=
        hEc.cpow (continuous_fst.sub continuous_const).continuousAt
          (hcub_expSubOneDiv_mem_slitPlane ht.le)
      have hr : ContinuousAt (fun p : ℂ × ℂ =>
          exp (p.2 * (1 - c)) * (1 - z + z * exp (-p.2)) ^ (-a)) (b, t) :=
        ContinuousAt.comp (f := fun p : ℂ × ℂ => p.2)
          (g := fun t : ℂ => exp (t * (1 - c)) * (1 - z + z * exp (-t)) ^ (-a))
          (hrest t ht.le).continuousAt continuous_snd.continuousAt
      have := hpow.mul hr
      simp only [largeDenominatorGenerating, mul_assoc]
      exact this)
    (fun b t ht => by
      have h1 : DifferentiableAt ℂ (fun t => expSubOneDiv t ^ (b - 1) *
          (exp (t * (1 - c)) * (1 - z + z * exp (-t)) ^ (-a))) t :=
        ((hE t).cpow (differentiableAt_const (b - 1))
          (hcub_expSubOneDiv_mem_slitPlane (by simpa using ht))).mul (hrest t (by simpa using ht))
      simpa only [largeDenominatorGenerating, mul_assoc] using h1.differentiableWithinAt)
    (fun t ht => by
      have h0 : expSubOneDiv t ≠ 0 := slitPlane_ne_zero (hcub_expSubOneDiv_mem_slitPlane ht.le)
      intro b
      simp only [largeDenominatorGenerating]
      exact (((differentiableAt_id.sub (differentiableAt_const _)).const_cpow
        (Or.inl h0)).mul (differentiableAt_const _)).mul (differentiableAt_const _)) N
  exact h.div_const _

/-- The coefficient identity behind 15.12.3, for all `b`. -/
theorem hcub_largeDenMix_eq (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) (N : ℕ) :
    hcub_largeDenMix a b c z N = poch b N * largeDenominatorCoeff a b c z N := by
  set f : ℂ → ℂ := fun b => hcub_largeDenMix a b c z N - poch b N * largeDenominatorCoeff a b c z N
    with hfdef
  have hf : Differentiable ℂ f := (hcub_differentiable_largeDenMix a c z N).sub
    ((Polynomial.differentiable _).mul (hcub_differentiable_largeDenominatorCoeff a c hz N))
  have hA : AnalyticOnNhd ℂ f univ := fun x _ => hf.analyticAt x
  have h0 : f =ᶠ[𝓝 1] 0 := by
    have hopen : IsOpen {b : ℂ | 0 < b.re} := isOpen_lt continuous_const continuous_re
    filter_upwards [hopen.mem_nhds (by simp : (1 : ℂ) ∈ {b : ℂ | 0 < b.re})] with x hx
    simp [hfdef, hcub_largeDenMix_eq_of_re_pos a x c hz hx N]
  have := hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (mem_univ 1) h0
    (mem_univ b)
  simpa [hfdef, sub_eq_zero] using this

end ShiftExpansion

@[dlmf 15.12.E3]
theorem large_denominator_shift_expansion (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) (m : ℕ) :
    Asymptotics.IsBigO atTop
      (fun l : ℝ => Gamma (c - b + l) / Gamma (c + l) * (l : ℂ) ^ b * ₂F₁ a b (c + l) z -
        ∑ k ∈ Finset.range m, largeDenominatorCoeff a b c z k * poch b k / (l : ℂ) ^ k)
      (fun l : ℝ => (l : ℂ)⁻¹ ^ m) := by
  have hK := hcub_largeDen_mix a b c hz m
  simp only [hcub_largeDenMix_eq a _ c hz] at hK
  refine hK.congr_left fun l => ?_
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [inv_pow]; ring

@[dlmf 15.12.E5]
theorem large_opposite_parameters_bessel (a b c : ℝ) {x : ℝ} (hx : 1 < x) (hx3 : x < 3) :
    let ζ : ℂ := Real.arcosh x
    ∃ r₁ r₂ : ℝ → ℂ,
      Asymptotics.IsBigO atTop r₁ (fun l : ℝ => (l : ℂ)⁻¹ ^ 2) ∧
      Asymptotics.IsBigO atTop r₂ (fun l : ℝ => (l : ℂ)⁻¹ ^ 2) ∧
      ∀ᶠ l : ℝ in atTop,
        regularizedGaussHGFun (a + l) (b - l) c ((1 - (x : ℂ)) / 2) =
          (2 : ℂ) ^ (((a : ℂ) + b - 1) / 2) * (x + 1 : ℂ) ^ (((c : ℂ) - a - b - 1) / 2) /
            (x - 1 : ℂ) ^ ((c : ℂ) / 2) * (ζ * sinh ζ) ^ (1 / 2 : ℂ) *
            ((l : ℂ) + a / 2 - b / 2) ^ (1 - (c : ℂ)) *
            (besselI (c - 1) (((l : ℂ) + a / 2 - b / 2) * ζ) * (1 + r₁ l) +
              besselI (c - 2) (((l : ℂ) + a / 2 - b / 2) * ζ) / (2 * (l : ℂ) + a - b) *
                (((c : ℂ) - 1 / 2) * (c - 3 / 2) * (1 / ζ - cosh ζ / sinh ζ) +
                  (2 * (c : ℂ) - a - b - 1) * (a + b - 1) / 2 * tanh (ζ / 2) + r₂ l)) := by
  sorry

end DLMF.Hypergeometric
