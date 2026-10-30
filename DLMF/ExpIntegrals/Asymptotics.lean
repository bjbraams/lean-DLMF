/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.ExpIntegrals.Continuation
public import DLMF.IncompleteGamma.ExpIntegralAsymptotics

/-!
# Sectorial asymptotic expansions and explicit remainders, DLMF §6.12

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
New theorem statements are initially admitted and are not completed proofs.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF
open scoped Real Topology Nat Interval
namespace DLMF.Confluent

/-- The n-th auxiliary-function asymptotic term; aux=true means g. -/
def expIntAsymptoticTerm (aux : Bool) (n : ℕ) (z : ℂ) : ℂ :=
  (-1 : ℂ)^n * ((2*n + if aux then 1 else 0).factorial : ℂ) / z^(2*n + if aux then 2 else 1)

/-- Finite auxiliary-function remainder. -/
@[dlmf 6.12.E5, dlmf 6.12.E6]
def expIntAsymptoticRemainder (aux : Bool) (N : ℕ) (z : ℂ) : ℂ :=
  (if aux then expIntAuxG z else expIntAuxF z) - ∑ n ∈ Finset.range N, expIntAsymptoticTerm aux n z

/-- A convergent improper integral of an integrable function is its Lebesgue integral. -/
theorem _root_.DLMF.HasIntegralAtTop.eq_integral_Ioi {f : ℝ → ℂ} {a : ℝ} {v : ℂ}
    (h : HasIntegralAtTop f a v) (hi : IntegrableOn f (Ioi a)) : ∫ t in Ioi a, f t = v :=
  tendsto_nhds_unique (intervalIntegral_tendsto_integral_Ioi a hi tendsto_id) h

/-- Laplace transforms of natural powers, `∫₀^∞ e^{-zt} t^m dt = m!/z^{m+1}`. -/
theorem laplace_nat_pow {z : ℂ} (hz : 0 < z.re) (m : ℕ) :
    IntegrableOn (fun t : ℝ => exp (-z*t)*(t:ℂ)^m) (Ioi 0) ∧
    ∫ t : ℝ in Ioi 0, exp (-z*t)*(t:ℂ)^m = m.factorial/z^(m+1) := by
  have ha : 0 < ((m:ℂ)+1).re := by simp; positivity
  have he : ∀ t : ℝ, exp (-z*t)*(t:ℂ)^((m:ℂ)+1-1)*(1+(t:ℂ))^(((m:ℂ)+1+1)-((m:ℂ)+1)-1) =
      exp (-z*t)*(t:ℂ)^m := fun t => by
    rw [show (m:ℂ)+1-1 = (m:ℕ) by ring, cpow_natCast, show (m:ℂ)+1+1-((m:ℂ)+1)-1 = 0 by ring, cpow_zero, mul_one]
  constructor
  · have := kummerU_laplace_integrable (b := (m:ℂ)+1+1) ha hz
    simpa only [he] using this
  · have h1 := kummerU_laplace_shift_one ha hz
    rw [kummerU_shift_one _ (Or.inl hz)] at h1
    simp only [he] at h1
    have hG : Gamma ((m:ℂ)+1) = m.factorial := by exact_mod_cast Complex.Gamma_nat_eq_factorial m
    rw [hG] at h1
    have hf : (m.factorial : ℂ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
    have hz0 : z ≠ 0 := fun h => by simp [h] at hz
    rw [show -((m:ℂ)+1) = -((m+1:ℕ):ℂ) by push_cast; ring, cpow_neg, cpow_natCast] at h1
    field_simp at h1 ⊢
    linear_combination -h1

/-- `|t²+1| ≥ 1` on the real line. -/
theorem norm_ofReal_sq_add_one_ge (t : ℝ) : 1 ≤ ‖(t:ℂ)^2+1‖ := by
  rw [show ((t:ℂ)^2+1) = ((t^2+1:ℝ):ℂ) by push_cast; ring, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity)]
  nlinarith [sq_nonneg t]

/-- `t²+1 ≠ 0` on the real line. -/
theorem ofReal_sq_add_one_ne (t : ℝ) : (t:ℂ)^2+1 ≠ 0 := fun h => by
  have := norm_ofReal_sq_add_one_ge t; rw [h, norm_zero] at this; linarith

/-- Integrability of the Laplace rational kernels `e^{-zt} t^m/(t²+1)`. -/
theorem integrableOn_laplace_rational {z : ℂ} (hz : 0 < z.re) (m : ℕ) :
    IntegrableOn (fun t : ℝ => exp (-z*t)*(t:ℂ)^m/((t:ℂ)^2+1)) (Ioi 0) := by
  refine ((laplace_nat_pow hz m).1.norm).mono' ?_ (Eventually.of_forall fun t => ?_)
  · exact (Continuous.div (by fun_prop) (by fun_prop) ofReal_sq_add_one_ne).aestronglyMeasurable
  · rw [norm_div]
    exact div_le_self (norm_nonneg _) (norm_ofReal_sq_add_one_ge t)

/-- The reduction `t^{m+2}/(t²+1) = t^m - t^m/(t²+1)` under the Laplace integral. -/
theorem laplace_rational_succ {z : ℂ} (hz : 0 < z.re) (m : ℕ) :
    ∫ t : ℝ in Ioi 0, exp (-z*t)*(t:ℂ)^(m+2)/((t:ℂ)^2+1) =
      m.factorial/z^(m+1) - ∫ t : ℝ in Ioi 0, exp (-z*t)*(t:ℂ)^m/((t:ℂ)^2+1) := by
  rw [← (laplace_nat_pow hz m).2, ← integral_sub (laplace_nat_pow hz m).1 (integrableOn_laplace_rational hz m)]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  have := ofReal_sq_add_one_ne t
  field_simp
  ring

/-- Real Laplace representations of `f` and `g` for `re z > 0`. -/
theorem expIntAux_laplace_Ioi {z : ℂ} (hz : 0 < z.re) :
    expIntAuxF z = ∫ t : ℝ in Ioi 0, exp (-z*t)*(t:ℂ)^0/((t:ℂ)^2+1) ∧
    expIntAuxG z = ∫ t : ℝ in Ioi 0, exp (-z*t)*(t:ℂ)^1/((t:ℂ)^2+1) := by
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  obtain ⟨h1, h2⟩ := expIntAux_laplace_hasIntegralAtTop hz0 hz.le
  constructor
  · rw [← (h1.congr fun t _ => by simp).eq_integral_Ioi (integrableOn_laplace_rational hz 0)]
  · rw [← (h2.congr fun t _ => by ring).eq_integral_Ioi (integrableOn_laplace_rational hz 1)]

/-- The auxiliary-function remainders as Laplace integrals, for both `f` and `g`. -/
lemma expIntAux_remainder_integral_general (aux : Bool) {z : ℂ} (hz : 0 < z.re) (N : ℕ) :
    expIntAsymptoticRemainder aux N z = (-1 : ℂ)^N * ∫ t : ℝ in Ioi 0,
      exp (-z*t)*(t : ℂ)^(2*N+if aux then 1 else 0)/((t : ℂ)^2+1) := by
  induction N with
  | zero =>
    simp only [expIntAsymptoticRemainder, Finset.range_zero, Finset.sum_empty, sub_zero, pow_zero,
      one_mul, mul_zero, zero_add]
    cases aux
    · simpa using (expIntAux_laplace_Ioi hz).1
    · simpa using (expIntAux_laplace_Ioi hz).2
  | succ N ih =>
    have hs := laplace_rational_succ hz (2*N+if aux then 1 else 0)
    rw [show 2*N+(if aux = true then 1 else 0)+2 = 2*(N+1)+(if aux = true then 1 else 0) by ring] at hs
    rw [hs]
    simp only [expIntAsymptoticRemainder, Finset.sum_range_succ] at ih ⊢
    rw [← sub_sub, ih, expIntAsymptoticTerm]
    have : (2*N + if aux = true then 2 else 1) = 2*N+(if aux = true then 1 else 0)+1 := by
      cases aux <;> simp
    rw [this, pow_succ]
    ring

/-- A uniform lower bound for `|t² + 1|` on the sector `|arg t| ≤ |θ| < π/2`. -/
theorem exists_pos_le_norm_ofReal_mul_exp_sq_add_one {θ : ℝ} (hθ : |θ| < π / 2) :
    ∃ c > 0, ∀ r y : ℝ, |y| ≤ |θ| → c ≤ ‖((r : ℂ) * exp (y * I)) ^ 2 + 1‖ := by
  obtain ⟨c, hc0, hc⟩ := exists_pos_le_norm_one_add_ofReal_mul_exp (Φ := 2 * |θ|) (by linarith)
  refine ⟨c, hc0, fun r y hy => ?_⟩
  rw [ofReal_mul_exp_ofReal_mul_I_sq, add_comm]
  exact hc _ (sq_nonneg r) _ (by rw [abs_mul, abs_two]; linarith)

/-- `Ci` is differentiable on the slit plane. -/
theorem differentiableAt_cosInt {z : ℂ} (hz : z ∈ slitPlane) : DifferentiableAt ℂ cosInt z := by
  unfold cosInt
  exact ((cosIntCin_entire z).neg.add (differentiableAt_log hz)).add_const _

/-- The auxiliary functions `f` and `g` of DLMF §6.2(ii) are differentiable on the slit plane. -/
lemma differentiableOn_expIntAux (aux : Bool) :
    DifferentiableOn ℂ (fun z => if aux then expIntAuxG z else expIntAuxF z) slitPlane := by
  intro z hz
  have hc := differentiableAt_cosInt hz
  have hs : DifferentiableAt ℂ sinIntTail z := by
    unfold sinIntTail; exact (sinInt_entire z).sub_const _
  cases aux
  · simp only [Bool.false_eq_true, ite_false]
    unfold expIntAuxF
    exact ((hc.mul (differentiableAt_sin)).sub (hs.mul differentiableAt_cos)).differentiableWithinAt
  · simp only [ite_true]
    unfold expIntAuxG
    exact ((hc.neg.mul differentiableAt_cos).sub (hs.mul differentiableAt_sin)).differentiableWithinAt

/-- Coefficients of `tᵐ/(1+t²) = ∑ aₙ tⁿ`. -/
noncomputable def expIntAuxCoeff (m n : ℕ) : ℂ :=
  if m ≤ n ∧ Even (n - m) then (-1) ^ ((n - m) / 2) else 0

/-- Partial sums of `∑ cₙ tⁿ` are the partial sums of the geometric series of `tᵐ/(t²+1)`. -/
lemma sum_expIntAuxCoeff (m : ℕ) (t : ℂ) (M : ℕ) :
    (∑ n ∈ Finset.range (m + 2 * M), t ^ n * expIntAuxCoeff m n =
      t ^ m * ∑ k ∈ Finset.range M, (-t ^ 2) ^ k) ∧
    (∑ n ∈ Finset.range (m + 2 * M + 1), t ^ n * expIntAuxCoeff m n =
      t ^ m * ∑ k ∈ Finset.range (M + 1), (-t ^ 2) ^ k) := by
  induction M with
  | zero =>
    have h0 : ∑ n ∈ Finset.range m, t ^ n * expIntAuxCoeff m n = 0 :=
      Finset.sum_eq_zero fun n hn => by
        simp [expIntAuxCoeff, show ¬ m ≤ n from by simpa using hn]
    refine ⟨by simpa using h0, ?_⟩
    rw [mul_zero, add_zero, Finset.sum_range_succ, h0]
    simp [expIntAuxCoeff]
  | succ M ih =>
    have h1 : ∑ n ∈ Finset.range (m + 2 * (M + 1)), t ^ n * expIntAuxCoeff m n =
        t ^ m * ∑ k ∈ Finset.range (M + 1), (-t ^ 2) ^ k := by
      rw [show m + 2 * (M + 1) = m + 2 * M + 1 + 1 by ring, Finset.sum_range_succ, ih.2]
      have : ¬ Even (m + 2 * M + 1 - m) := by
        rw [show m + 2 * M + 1 - m = 2 * M + 1 by omega]; simp
      simp [expIntAuxCoeff, this]
    refine ⟨h1, ?_⟩
    have he : m + 2 * (M + 1) - m = 2 * (M + 1) := by omega
    have hterm : t ^ (m + 2 * (M + 1)) * expIntAuxCoeff m (m + 2 * (M + 1)) =
        t ^ m * (-t ^ 2) ^ (M + 1) := by
      simp only [expIntAuxCoeff]
      rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by omega, by rw [he]; exact even_two_mul _⟩), he,
        show 2 * (M + 1) / 2 = M + 1 by omega, pow_add, neg_pow (t ^ 2), ← pow_mul]
      ring
    rw [Finset.sum_range_succ, h1, hterm, Finset.sum_range_succ (n := M + 1)]
    ring

/-- Every partial sum of `∑ cₙ tⁿ` agrees with a partial geometric sum of `tᵐ/(t²+1)`. -/
lemma exists_sum_expIntAuxCoeff (m N : ℕ) : ∃ M : ℕ, N ≤ m + 2 * M ∧ ∀ t : ℂ,
    ∑ n ∈ Finset.range N, t ^ n * expIntAuxCoeff m n = t ^ m * ∑ k ∈ Finset.range M, (-t ^ 2) ^ k := by
  rcases le_or_gt N m with h | h
  · refine ⟨0, by omega, fun t => ?_⟩
    simp only [Finset.range_zero, Finset.sum_empty, mul_zero]
    exact Finset.sum_eq_zero fun n hn => by
      simp [expIntAuxCoeff, show ¬ m ≤ n by simp at hn; omega]
  · obtain ⟨M, hM | hM⟩ := Nat.even_or_odd' (N - m)
    · exact ⟨M, by omega, fun t => by
        rw [show N = m + 2 * M by omega]; exact (sum_expIntAuxCoeff m t M).1⟩
    · exact ⟨M + 1, by omega, fun t => by
        rw [show N = m + 2 * M + 1 by omega]; exact (sum_expIntAuxCoeff m t M).2⟩

/-- Taylor remainders of `tᵐ/(t²+1)` along a ray, in the form required by Watson's lemma. -/
lemma expIntAux_kernel_sub_sum_isBigO (m : ℕ) {θ : ℝ} (hθ : |θ| < π / 2) (N : ℕ) :
    (fun r : ℝ => ((r : ℂ) * exp (θ * I)) ^ m / (((r : ℂ) * exp (θ * I)) ^ 2 + 1) -
      ∑ n ∈ Finset.range N, (((r : ℂ) * exp (θ * I)) ^ ((n : ℂ) + 1 - 1)) • expIntAuxCoeff m n)
      =O[𝓝[>] 0] fun r => r ^ ((N : ℝ) + (1 : ℂ).re - 1) := by
  obtain ⟨c, hc0, hc⟩ := exists_pos_le_norm_ofReal_mul_exp_sq_add_one hθ
  obtain ⟨M, hNM, hM⟩ := exists_sum_expIntAuxCoeff m N
  refine IsBigO.of_bound (1 / c) ?_
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds (zero_lt_one' ℝ))]
    with r hr hr1
  have hr : (0 : ℝ) < r := hr
  have hr1 : r < 1 := hr1
  simp only [one_re, add_sub_cancel_right, cpow_natCast, smul_eq_mul]
  rw [hM]
  set t : ℂ := (r : ℂ) * exp (θ * I)
  have hden := hc r θ le_rfl
  have hne : t ^ 2 + 1 ≠ 0 := fun h0 => by
    rw [h0, norm_zero] at hden; linarith
  have hgeom : t ^ m / (t ^ 2 + 1) - t ^ m * ∑ k ∈ Finset.range M, (-t ^ 2) ^ k =
      t ^ m * (-t ^ 2) ^ M / (t ^ 2 + 1) := by
    have h := mul_neg_geom_sum (-t ^ 2) M
    rw [sub_neg_eq_add, add_comm] at h
    field_simp
    linear_combination (-(t ^ m)) * h
  rw [hgeom, norm_div, norm_mul, norm_pow, norm_pow, norm_neg, norm_pow]
  have ht : ‖t‖ = r := by
    simp only [t, norm_mul, Complex.norm_real, Real.norm_of_nonneg hr.le, norm_exp_ofReal_mul_I,
      mul_one]
  rw [ht, Real.norm_of_nonneg (Real.rpow_nonneg hr.le _), Real.rpow_natCast,
    div_le_iff₀ (hc0.trans_le hden)]
  have hpow : r ^ m * (r ^ 2) ^ M ≤ r ^ N := by
    rw [← pow_mul, ← pow_add]; exact pow_le_pow_of_le_one hr.le hr1.le hNM
  calc r ^ m * (r ^ 2) ^ M ≤ r ^ N := hpow
    _ ≤ 1 / c * r ^ N * ‖t ^ 2 + 1‖ := by
      rw [show 1 / c * r ^ N * ‖t ^ 2 + 1‖ = r ^ N * (‖t ^ 2 + 1‖ / c) by ring]
      exact le_mul_of_one_le_right (by positivity) ((one_le_div hc0).mpr hden)

/-- Bounds for the kernel `tᵐ/(t²+1)` on the sector `|arg t| ≤ |θ| < π/2`. -/
lemma norm_expIntAux_kernel_le {θ c : ℝ} (hc0 : 0 < c)
    (hc : ∀ r y : ℝ, |y| ≤ |θ| → c ≤ ‖((r : ℂ) * exp (y * I)) ^ 2 + 1‖) (m : ℕ) {r : ℝ}
    (hr : 0 ≤ r) {y : ℝ} (hy : |y| ≤ |θ|) :
    ‖((r : ℂ) * exp (y * I)) ^ m / (((r : ℂ) * exp (y * I)) ^ 2 + 1)‖ ≤ 1 / c * r ^ m := by
  have hden := hc r y hy
  rw [norm_div, norm_pow, norm_mul, Complex.norm_real, Real.norm_of_nonneg hr,
    norm_exp_ofReal_mul_I, mul_one, div_le_iff₀ (hc0.trans_le hden)]
  rw [show 1 / c * r ^ m * ‖((r : ℂ) * exp (y * I)) ^ 2 + 1‖ =
    r ^ m * (‖((r : ℂ) * exp (y * I)) ^ 2 + 1‖ / c) by ring]
  exact le_mul_of_one_le_right (by positivity) ((one_le_div hc0).mpr hden)

/-- `(r e^{iy})² + 1 ≠ 0` under a uniform lower bound `c ≤ ‖(r e^{iy})² + 1‖`. -/
theorem ofReal_mul_exp_sq_add_one_ne {θ c : ℝ} (hc0 : 0 < c)
    (hc : ∀ r y : ℝ, |y| ≤ |θ| → c ≤ ‖((r : ℂ) * exp (y * I)) ^ 2 + 1‖) (r : ℝ) {y : ℝ}
    (hy : |y| ≤ |θ|) : ((r : ℂ) * exp (y * I)) ^ 2 + 1 ≠ 0 := fun h0 => by
  have := hc r y hy; rw [h0, norm_zero] at this; linarith

/-- **Rotated Laplace representations of `f` and `g`** (DLMF 6.7.13–6.7.14 continued): for
`|θ| < π/2` and `re (z e^{iθ}) > 0`, with `m = 0` for `f` and `m = 1` for `g`,
`f(z), g(z) = e^{iθ} ∫₀^∞ e^{-z e^{iθ} r} (r e^{iθ})ᵐ/((r e^{iθ})² + 1) dr`. -/
lemma expIntAux_eq_integral_rotate (aux : Bool) {θ : ℝ} (hθ : |θ| < π / 2) {z : ℂ}
    (hz : 0 < (z * exp (θ * I)).re) :
    (if aux then expIntAuxG z else expIntAuxF z) = exp (θ * I) * ∫ r in Ioi (0 : ℝ),
      cexp (-(z * exp (θ * I) * r)) * (((r : ℂ) * exp (θ * I)) ^ (if aux then 1 else 0) /
        (((r : ℂ) * exp (θ * I)) ^ 2 + 1)) := by
  set m : ℕ := if aux then 1 else 0 with hm
  obtain ⟨c, hc0, hc⟩ := exists_pos_le_norm_ofReal_mul_exp_sq_add_one hθ
  set U : Set ℂ := {z : ℂ | 0 < (z * exp (θ * I)).re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const (by fun_prop)
  have hUc : Convex ℝ U := by
    intro x hx y hy a b ha hb hab
    have hx : 0 < (x * exp (θ * I)).re := hx
    have hy : 0 < (y * exp (θ * I)).re := hy
    show 0 < ((a • x + b • y) * exp (θ * I)).re
    have he : ((a • x + b • y) * exp (θ * I)).re =
        a * (x * exp (θ * I)).re + b * (y * exp (θ * I)).re := by
      simp only [add_mul, add_re, Complex.real_smul, mul_assoc, re_ofReal_mul]
    rw [he]
    rcases ha.lt_or_eq with ha | ha
    · nlinarith [mul_nonneg hb hy.le]
    · subst ha; rw [zero_add] at hab; subst hab; simpa using hy
  have hUs : U ⊆ slitPlane := by
    intro x hx
    rw [mem_slitPlane_iff]
    by_contra h
    push Not at h
    have hx' : (x * exp (θ * I)).re = x.re * Real.cos θ := by
      rw [mul_re, exp_ofReal_mul_I_re, exp_ofReal_mul_I_im, h.2]; ring
    have : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [neg_abs_le θ], by
      linarith [le_abs_self θ]⟩
    have hx2 : 0 < (x * exp (θ * I)).re := hx
    rw [hx'] at hx2
    nlinarith [h.1]
  set G : ℝ → ℂ := fun r => ((r : ℂ) * exp (θ * I)) ^ m / (((r : ℂ) * exp (θ * I)) ^ 2 + 1)
    with hG
  have hGc : ContinuousOn G (Ioi 0) := fun r _ =>
    ((by fun_prop : Continuous fun r : ℝ => ((r : ℂ) * exp (θ * I)) ^ m).continuousAt.div
      (by fun_prop : Continuous fun r : ℝ => ((r : ℂ) * exp (θ * I)) ^ 2 + 1).continuousAt
      (ofReal_mul_exp_sq_add_one_ne hc0 hc r le_rfl)).continuousWithinAt
  have hLd := differentiableOn_integral_cexp_neg_mul_smul_of_le_rpow (G := G) (C := 1 / c)
    (D := 0) (k := m) (by have := (Nat.cast_nonneg m : (0 : ℝ) ≤ m); linarith) hGc (fun r hr => by
      rw [Real.rpow_natCast, add_zero]; exact norm_expIntAux_kernel_le hc0 hc m hr.le le_rfl)
  simp only [smul_eq_mul] at hLd
  have hR : DifferentiableOn ℂ (fun z : ℂ => exp (θ * I) * ∫ r in Ioi (0 : ℝ),
      cexp (-(z * exp (θ * I) * r)) * G r) U :=
    (differentiableOn_const _).mul (hLd.comp (differentiableOn_id.mul_const _)
      (fun z hz => hz))
  have hL : DifferentiableOn ℂ (fun z => if aux then expIntAuxG z else expIntAuxF z) U :=
    (differentiableOn_expIntAux aux).mono hUs
  -- agreement on `U ∩ {re z > 0}`
  have hagree : ∀ w : ℂ, 0 < w.re → w ∈ U → (if aux then expIntAuxG w else expIntAuxF w) =
      exp (θ * I) * ∫ r in Ioi (0 : ℝ), cexp (-(w * exp (θ * I) * r)) * G r := by
    intro w hw hwU
    have hlap : (if aux then expIntAuxG w else expIntAuxF w) =
        ∫ t : ℝ in Ioi 0, cexp (-(w * t)) * ((t : ℂ) ^ m / ((t : ℂ) ^ 2 + 1)) := by
      have h := expIntAux_laplace_Ioi hw
      rw [hm]
      cases aux
      · simp only [Bool.false_eq_true, ite_false, h.1]
        exact setIntegral_congr_fun measurableSet_Ioi fun t _ => by ring_nf
      · simp only [ite_true, h.2]
        exact setIntegral_congr_fun measurableSet_Ioi fun t _ => by ring_nf
    rw [hlap]
    refine integral_cexp_neg_mul_mul_eq_rotate (F := fun t : ℂ => t ^ m / (t ^ 2 + 1))
      (σ := 1) (C := 1 / c) (k := m) one_pos (fun r _ y hy => ?_) (fun r hr hr1 y hy => ?_)
      (fun r hr y hy => ?_) (fun y hy => re_mul_exp_pos_of_mem_uIcc hθ hw hwU hy)
    · exact (differentiableAt_pow m).div ((differentiableAt_pow 2).add_const 1)
        (ofReal_mul_exp_sq_add_one_ne hc0 hc r (abs_le_abs_of_mem_uIcc_zero hy))
    · refine (norm_expIntAux_kernel_le hc0 hc m hr.le (abs_le_abs_of_mem_uIcc_zero hy)).trans ?_
      rw [sub_self, Real.rpow_zero, mul_one]
      have : r ^ m ≤ 1 := pow_le_one₀ hr.le hr1
      have : 0 < 1 / c := by positivity
      nlinarith
    · rw [Real.rpow_natCast]
      exact norm_expIntAux_kernel_le hc0 hc m (by linarith) (abs_le_abs_of_mem_uIcc_zero hy)
  -- the identity theorem
  set z₀ : ℂ := exp ((-(θ / 2) : ℝ) * I) with hz₀
  have hcos : 0 < Real.cos (θ / 2) := Real.cos_pos_of_mem_Ioo ⟨by
    linarith [neg_abs_le θ, Real.pi_pos], by linarith [le_abs_self θ, Real.pi_pos]⟩
  have hz₀re : 0 < z₀.re := by rw [hz₀, exp_ofReal_mul_I_re, Real.cos_neg]; exact hcos
  have hz₀U : z₀ ∈ U := by
    show 0 < (z₀ * exp (θ * I)).re
    rw [hz₀, ← Complex.exp_add, show ((-(θ / 2) : ℝ) : ℂ) * I + θ * I = ((θ / 2 : ℝ) : ℂ) * I by
      push_cast; ring, exp_ofReal_mul_I_re]
    exact hcos
  have hev : (fun z => if aux then expIntAuxG z else expIntAuxF z) =ᶠ[𝓝 z₀]
      (fun z : ℂ => exp (θ * I) * ∫ r in Ioi (0 : ℝ), cexp (-(z * exp (θ * I) * r)) * G r) := by
    have hV : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const continuous_re
    filter_upwards [hV.mem_nhds hz₀re, hUo.mem_nhds hz₀U] with w hw hwU
    exact hagree w hw hwU
  exact (hL.analyticOnNhd hUo).eqOn_of_preconnected_of_eventuallyEq (hR.analyticOnNhd hUo)
    hUc.isPreconnected hz₀U hev hz

/-- Watson's expansion of `f` and `g` in a rotated sector. -/
lemma expIntAux_rotSector_asymptotic (aux : Bool) {θ δ : ℝ} (hθ : |θ| < π / 2) (hδ : 0 < δ) :
    HasAsymptoticExpansion (comap (fun z : ℂ => z * exp (θ * I)) (sectorAtTop δ))
      (fun (n : ℕ) (z : ℂ) => z ^ (-((n : ℂ) + 1)))
      (fun n => Gamma ((n : ℂ) + 1) • expIntAuxCoeff (if aux then 1 else 0) n)
      (fun z => if aux then expIntAuxG z else expIntAuxF z) := by
  set m : ℕ := if aux then 1 else 0 with hm
  obtain ⟨c, hc0, hc⟩ := exists_pos_le_norm_ofReal_mul_exp_sq_add_one hθ
  have hGc : ContinuousOn (fun r : ℝ => ((r : ℂ) * exp (θ * I)) ^ m /
      (((r : ℂ) * exp (θ * I)) ^ 2 + 1)) (Ioi 0) := fun r _ =>
    ((by fun_prop : Continuous fun r : ℝ => ((r : ℂ) * exp (θ * I)) ^ m).continuousAt.div
      (by fun_prop : Continuous fun r : ℝ => ((r : ℂ) * exp (θ * I)) ^ 2 + 1).continuousAt
      (ofReal_mul_exp_sq_add_one_ne hc0 hc r le_rfl)).continuousWithinAt
  have hint : IntegrableOn (fun r : ℝ => Real.exp (-1 * r) • (((r : ℂ) * exp (θ * I)) ^ m /
      (((r : ℂ) * exp (θ * I)) ^ 2 + 1))) (Ioi 0) := by
    have hmaj := (integrableOn_exp_neg_mul_mul_rpow_sub_one (s := (m : ℝ) + 1) (by positivity)
      one_pos).const_mul (1 / c)
    refine hmaj.mono' (((by fun_prop : Continuous fun t : ℝ => Real.exp (-1 * t)
      ).continuousOn.smul hGc).aestronglyMeasurable measurableSet_Ioi) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    have ht : (0 : ℝ) < t := ht
    rw [norm_smul, Real.norm_eq_abs, Real.abs_exp, add_sub_cancel_right, Real.rpow_natCast]
    calc Real.exp (-1 * t) * ‖((t : ℂ) * exp (θ * I)) ^ m / (((t : ℂ) * exp (θ * I)) ^ 2 + 1)‖
        ≤ Real.exp (-1 * t) * (1 / c * t ^ m) :=
          mul_le_mul_of_nonneg_left (norm_expIntAux_kernel_le hc0 hc m ht.le le_rfl)
            (Real.exp_pos _).le
      _ = _ := by ring
  have hW := hasAsymptoticExpansion_integral_cexp_smul_rotate_comap
    (F := fun t : ℂ => t ^ m / (t ^ 2 + 1)) (a := expIntAuxCoeff m) (μ := 1) (c := 1) hθ
    (by norm_num) hδ hint (expIntAux_kernel_sub_sum_isBigO m hθ)
  refine hW.congr' ?_
  have h := (tendsto_comap : Tendsto (fun z : ℂ => z * exp (θ * I))
    (comap (fun z : ℂ => z * exp (θ * I)) (sectorAtTop δ)) (sectorAtTop δ)).eventually
    (eventually_sectorAtTop (R := 1) (p := fun w : ℂ => 0 < w.re) fun w hw hws => by nlinarith)
  filter_upwards [h] with z hz
  rw [expIntAux_eq_integral_rotate aux hθ hz]
  simp only [smul_eq_mul, hm]

/-- The two rotated sectors `|arg (z e^{∓iβ})| ≤ β`, `β = π/2 - d/2`, cover `|arg z| ≤ π - δ`. -/
theorem sector_pi_sub_le_sup {δ : ℝ} (hδ : 0 < δ) :
    ∃ β : ℝ, |β| < π / 2 ∧ 0 < Real.cos β ∧ sector (π - δ) ≤
      comap (fun z : ℂ => z * exp (((-β : ℝ) : ℂ) * I)) (sectorAtTop (Real.cos β)) ⊔
        comap (fun z : ℂ => z * exp ((β : ℂ) * I)) (sectorAtTop (Real.cos β)) := by
  set d := min δ (π / 2) with hd
  have hd0 : 0 < d := lt_min hδ (by positivity)
  have hdδ : d ≤ δ := min_le_left _ _
  have hdπ : d ≤ π / 2 := min_le_right _ _
  refine ⟨π / 2 - d / 2, by rw [abs_lt]; constructor <;> linarith,
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩,
    le_sup_comap_rotate (by linarith) le_rfl (by linarith) (by linarith)⟩

/-- On the logarithmic plane, `E₁` is the generalized exponential integral with `p = 1`. -/
lemma expIntE1OnLog_eq_genExpIntEOnLog_one (w : ℂ) :
    expIntE1OnLog w = genExpIntEOnLog 1 w := by
  simp only [genExpIntEOnLog, sub_self, zero_mul, Complex.exp_zero, one_mul,
    upperIncGammaOnLog_zero, expIntE1OnLog]

/-- Identity under the stated parameter and domain assumptions: `HasAsymptoticExpansion (logSector
(3*π/2-δ)) (fun n w => exp (-exp w-(n+1 : ℂ)*w)) (fun n => (-1 : ℂ)^n*n.factorial)
expIntE1OnLog`. -/
@[dlmf 6.12.E1]
theorem expIntE1_logSector_asymptotic {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 3*π/2) :
    HasAsymptoticExpansion (logSector (3*π/2-δ)) (fun n w => exp (-exp w-(n+1 : ℂ)*w)) (fun n => (-1 : ℂ)^n*n.factorial) expIntE1OnLog := by
  have h := genExpIntE_log_sector_asymptotic 1 hδ hδ1
  have he : genExpIntEOnLog 1 = expIntE1OnLog := by
    funext w; exact (expIntE1OnLog_eq_genExpIntEOnLog_one w).symm
  simp only [poch_nat_one, he] at h
  exact h

/-- At `w = log x + π i`, the E₁ asymptotic scale is `e^x/(-x)^{n+1}`. -/
theorem exp_neg_exp_sub_mul_log_add_pi_I {x : ℝ} (hx : 0 < x) (n : ℕ) :
    exp (-exp ((Real.log x : ℂ) + π*I) - (n+1 : ℂ)*((Real.log x : ℂ) + π*I)) =
      (Real.exp x : ℂ) / (-(x:ℂ))^(n+1) := by
  have hw : exp ((Real.log x : ℂ) + π*I) = -(x:ℂ) := by
    rw [Complex.exp_add, Complex.exp_pi_mul_I, ← Complex.ofReal_exp, Real.exp_log hx]; ring
  rw [sub_eq_add_neg, Complex.exp_add, hw, neg_neg, Complex.ofReal_exp,
    show -((n+1 : ℂ)*((Real.log x : ℂ) + π*I)) = -(((n+1 : ℕ) : ℂ)*((Real.log x : ℂ) + π*I)) by
      push_cast; ring, Complex.exp_neg, Complex.exp_nat_mul, hw, div_eq_mul_inv]

/-- Identity under the stated parameter and domain assumptions: `HasAsymptoticExpansion atTop (fun
n (x : ℝ) => Real.exp x / x^(n+1)) (fun n => (n.factorial : ℝ)) Real.expIntEi`. -/
@[dlmf 6.12.E2]
theorem expIntEi_asymptotic  :
    HasAsymptoticExpansion atTop (fun n (x : ℝ) => Real.exp x / x^(n+1)) (fun n => (n.factorial : ℝ)) Real.expIntEi := by
  have hδ : (0:ℝ) < π/2 := by positivity
  have hδ1 : π/2 < 3*π/2 := by linarith [Real.pi_pos]
  set g : ℝ → ℂ := fun x => (Real.log x : ℂ) + π*I with hg
  have hgt : Tendsto g atTop (logSector (3*π/2-π/2)) := by
    unfold logSector
    refine tendsto_inf.mpr ⟨tendsto_comap_iff.mpr ?_, tendsto_principal.mpr ?_⟩
    · refine tendsto_id.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with x hx
      simp [hg, Real.exp_log hx]
    · refine Eventually.of_forall fun x => ?_
      show |(g x).im| ≤ 3*π/2-π/2
      simp only [hg, add_im, ofReal_im, mul_im, ofReal_re, I_re, mul_zero, I_im, mul_one,
        zero_add, ofReal_im]
      rw [add_zero, abs_of_pos Real.pi_pos]; linarith
  have h := (expIntE1_logSector_asymptotic hδ hδ1).comp_tendsto hgt
  intro N
  have hN := h N
  have hL : (fun x : ℝ => Real.expIntEi x - ∑ n ∈ Finset.range N,
      (Real.exp x / x^(n+1)) • (n.factorial : ℝ)) =O[atTop]
      (fun x => (expIntE1OnLog ∘ g) x - ∑ n ∈ Finset.range N,
        exp (-exp (g x)-(n+1 : ℂ)*(g x)) • ((-1 : ℂ)^n*n.factorial)) := by
    refine IsBigO.of_bound' ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    have hsum : ∑ n ∈ Finset.range N, exp (-exp (g x)-(n+1 : ℂ)*(g x)) • ((-1 : ℂ)^n*n.factorial)
        = -(((∑ n ∈ Finset.range N, (Real.exp x / x^(n+1)) • (n.factorial : ℝ) : ℝ)) : ℂ) := by
      simp only [smul_eq_mul]
      push_cast
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [hg, exp_neg_exp_sub_mul_log_add_pi_I hx, neg_pow, pow_succ]
      simp only [Complex.ofReal_exp]
      have hx0 : (x:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
      field_simp
    have hre : (expIntE1OnLog (g x)).re = -Real.expIntEi x := by
      have := expIntE1OnLog_halfTurn (Real.log x : ℂ) (ε := 1) (Or.inl rfl)
      simp only [Complex.ofReal_one, one_mul] at this
      rw [hg]; simp only
      rw [this, ← Complex.ofReal_exp, Real.exp_log hx, Real.expIntEi, abs_of_pos hx]
      simp; ring
    rw [Function.comp_apply, hsum, sub_neg_eq_add]
    refine le_trans ?_ (Complex.abs_re_le_norm _)
    rw [Real.norm_eq_abs, add_re, hre, ofReal_re, ← abs_neg]
    apply le_of_eq; congr 1; ring
  refine hL.trans (hN.trans (IsBigO.of_bound' ?_))
  filter_upwards [eventually_gt_atTop 0] with x hx
  rw [exp_neg_exp_sub_mul_log_add_pi_I hx, norm_div, norm_pow, norm_neg, Complex.norm_real,
    Complex.norm_real, norm_div, norm_pow]

/-- Identity under the stated parameter and domain assumptions: `HasAsymptoticExpansion (sector
(π-δ)) (fun n z => z^(-(2*(n : ℂ)+1))) (fun n => (-1 : ℂ)^n*((2*n+0).factorial : ℂ))
expIntAuxF`. -/
@[dlmf 6.12.E3]
theorem expIntAuxF_sector_asymptotic {δ : ℝ} (hδ : 0 < δ) :
    HasAsymptoticExpansion (sector (π-δ)) (fun n z => z^(-(2*(n : ℂ)+1))) (fun n => (-1 : ℂ)^n*((2*n+0).factorial : ℂ)) expIntAuxF := by
  obtain ⟨β, hβ, hcos, hcov⟩ := sector_pi_sub_le_sup hδ
  have hodd : ∀ n : ℕ, Gamma (((2 * n + 1 : ℕ) : ℂ) + 1) • expIntAuxCoeff 0 (2 * n + 1) = 0 := by
    intro n
    simp [expIntAuxCoeff]
  have h1 := (expIntAux_rotSector_asymptotic false (θ := -β) (by rwa [abs_neg]) hcos).even hodd
  have h2 := (expIntAux_rotSector_asymptotic false (θ := β) hβ hcos).even hodd
  refine (((h1.sup h2).mono hcov).congr_scale fun n => Eventually.of_forall fun z => ?_).congr_coeff ?_
  · simp only; push_cast; ring_nf
  · funext n
    simp only [Bool.false_eq_true, ↓reduceIte, expIntAuxCoeff, zero_le, true_and, Nat.sub_zero,
      even_two_mul, show 2 * n / 2 = n by omega, smul_eq_mul, add_zero]
    rw [Complex.Gamma_nat_eq_factorial]
    ring

/-- Identity under the stated parameter and domain assumptions: `expIntAsymptoticRemainder false N
z = (-1 : ℂ)^N * ∫ t : ℝ in Ioi 0, exp (-z*t)*(t : ℂ)^(2*N+0)/((t : ℂ)^2+1)`. -/
@[dlmf 6.12.E7]
theorem expIntAuxF_remainder_integral {z : ℂ} (hz : 0 < z.re) (N : ℕ) :
    expIntAsymptoticRemainder false N z = (-1 : ℂ)^N * ∫ t : ℝ in Ioi 0, exp (-z*t)*(t : ℂ)^(2*N+0)/((t : ℂ)^2+1) := by
  simpa using expIntAux_remainder_integral_general false hz N

/-- Identity under the stated parameter and domain assumptions: `HasAsymptoticExpansion (sector
(π-δ)) (fun n z => z^(-(2*(n : ℂ)+2))) (fun n => (-1 : ℂ)^n*((2*n+1).factorial : ℂ))
expIntAuxG`. -/
@[dlmf 6.12.E4]
theorem expIntAuxG_sector_asymptotic {δ : ℝ} (hδ : 0 < δ) :
    HasAsymptoticExpansion (sector (π-δ)) (fun n z => z^(-(2*(n : ℂ)+2))) (fun n => (-1 : ℂ)^n*((2*n+1).factorial : ℂ)) expIntAuxG := by
  obtain ⟨β, hβ, hcos, hcov⟩ := sector_pi_sub_le_sup hδ
  have hev : ∀ n : ℕ, Gamma (((2 * n : ℕ) : ℂ) + 1) • expIntAuxCoeff 1 (2 * n) = 0 := by
    intro n
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp [expIntAuxCoeff]
    · have : ¬ Even (2 * n - 1) := by
        rw [show 2 * n - 1 = 2 * (n - 1) + 1 by omega]; simp
      simp [expIntAuxCoeff, this]
  have h1 := (expIntAux_rotSector_asymptotic true (θ := -β) (by rwa [abs_neg]) hcos).odd hev
  have h2 := (expIntAux_rotSector_asymptotic true (θ := β) hβ hcos).odd hev
  refine (((h1.sup h2).mono hcov).congr_scale fun n => Eventually.of_forall fun z => ?_).congr_coeff ?_
  · simp only; push_cast; ring_nf
  · funext n
    simp only [↓reduceIte, expIntAuxCoeff, show 1 ≤ 2 * n + 1 by omega, true_and,
      show 2 * n + 1 - 1 = 2 * n by omega, even_two_mul, show 2 * n / 2 = n by omega, smul_eq_mul]
    rw [Complex.Gamma_nat_eq_factorial]
    ring

/-- Identity under the stated parameter and domain assumptions: `expIntAsymptoticRemainder true N
z = (-1 : ℂ)^N * ∫ t : ℝ in Ioi 0, exp (-z*t)*(t : ℂ)^(2*N+1)/((t : ℂ)^2+1)`. -/
@[dlmf 6.12.E8]
theorem expIntAuxG_remainder_integral {z : ℂ} (hz : 0 < z.re) (N : ℕ) :
    expIntAsymptoticRemainder true N z = (-1 : ℂ)^N * ∫ t : ℝ in Ioi 0, exp (-z*t)*(t : ℂ)^(2*N+1)/((t : ℂ)^2+1) := by
  simpa using expIntAux_remainder_integral_general true hz N

/-- Rotated Laplace representation of `E₁`: for `z ≠ 0` with `|arg z| < π`,
`E₁(z) = e^{-z} e^{iθ} ∫₀^∞ e^{-|z| r}/(1 + r e^{iθ}) dr` with `θ = -arg z`. -/
theorem genExpIntE_one_eq_integral_rotate {z : ℂ} (hz0 : z ≠ 0) (hz : |arg z| < π) :
    genExpIntE 1 z = cexp (-z) * (exp (((-arg z : ℝ) : ℂ) * I) * ∫ r in Ioi (0 : ℝ),
      cexp (-((‖z‖ : ℂ) * r)) * (1 + (r : ℂ) * exp (((-arg z : ℝ) : ℂ) * I))⁻¹) := by
  have hθ : |-arg z| < π := by rwa [abs_neg]
  have hw : |(log z).im + -arg z| < π / 2 := by
    rw [log_im, add_neg_cancel, abs_zero]; positivity
  have h := genExpIntEOnLog_eq_integral_rotate 1 hθ hw
  rw [Complex.exp_log hz0] at h
  have hze : z * exp (((-arg z : ℝ) : ℂ) * I) = (‖z‖ : ℂ) := by
    conv_lhs => rw [← norm_mul_exp_arg_mul_I z]
    rw [mul_assoc, ← Complex.exp_add]
    push_cast
    simp
  have h2 := genExpIntEOnLog_eq_genExpIntE 1 (w := log z) (by rw [log_im]; exact neg_pi_lt_arg z)
    (by rw [log_im]; exact arg_le_pi z)
  rw [Complex.exp_log hz0] at h2
  rw [← h2, h, hze]
  simp only [cpow_neg_one]

/-- First omitted term and csc multiplier from DLMF §6.12(i). -/
lemma expIntE1_remainder_bound {z : ℂ} (hz0 : z ≠ 0) (hz : |arg z| < π) (N : ℕ) :
    ‖genExpIntE 1 z - exp (-z)*∑ n ∈ Finset.range N, (-1 : ℂ)^n*(n.factorial : ℂ)/z^(n+1)‖ ≤ (if |arg z| ≤ π/2 then 1 else 1/Real.sin |arg z|) * ‖exp (-z)*(N.factorial : ℂ)/z^(N+1)‖ := by
  set θ : ℝ := -arg z with hθ
  set e : ℂ := exp (θ * I) with he
  set a : ℝ := ‖z‖ with ha
  have ha0 : 0 < a := by rw [ha]; exact norm_pos_iff.mpr hz0
  have hare : 0 < (a : ℂ).re := by rw [Complex.ofReal_re]; exact ha0
  have hze : z * e = (a : ℂ) := by
    conv_lhs => rw [← norm_mul_exp_arg_mul_I z]
    rw [he, hθ, mul_assoc, ← Complex.exp_add]
    push_cast
    simp [ha]
  have hne : e ≠ 0 := Complex.exp_ne_zero _
  have hen : ‖e‖ = 1 := by rw [he]; exact norm_exp_ofReal_mul_I θ
  set L : ℝ := if |arg z| ≤ π/2 then 1 else Real.sin |arg z| with hL
  have hL0 : 0 < L := by
    rw [hL]; split_ifs with h
    · exact one_pos
    · push Not at h
      exact Real.sin_pos_of_pos_of_lt_pi (by linarith) hz
  have hLden : ∀ r : ℝ, 0 ≤ r → L ≤ ‖1 + (r : ℂ) * e‖ := by
    intro r hr
    rw [hL]; split_ifs with h
    · refine one_le_norm_one_add_ofReal_mul_exp hr ?_
      rw [← Real.cos_abs, hθ, abs_neg]
      exact Real.cos_nonneg_of_mem_Icc ⟨by linarith [abs_nonneg (arg z), Real.pi_pos], h⟩
    · have : |Real.sin θ| = Real.sin |arg z| := by
        rw [hθ, Real.sin_neg, abs_neg]
        rcases le_total 0 (arg z) with h0 | h0
        · rw [abs_of_nonneg h0, abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi h0
            (arg_le_pi z))]
        · rw [abs_of_nonpos h0, Real.sin_neg, abs_of_nonpos]
          exact Real.sin_nonpos_of_nonpos_of_neg_pi_le h0 (neg_pi_lt_arg z).le
      rw [← this]; exact abs_sin_le_norm_one_add_ofReal_mul_exp _ _
  have hden0 : ∀ r : ℝ, 0 ≤ r → 1 + (r : ℂ) * e ≠ 0 := fun r hr h0 => by
    have := hLden r hr; rw [h0, norm_zero] at this; linarith
  -- pointwise geometric decomposition
  set T : ℕ → ℝ → ℂ := fun n r => (-e)^n * (cexp (-(a : ℂ)*r) * (r : ℂ)^n) with hT
  set R : ℝ → ℂ := fun r => cexp (-((a : ℂ) * r)) * ((-((r : ℂ) * e))^N * (1 + (r : ℂ) * e)⁻¹)
    with hR
  have hpt : ∀ r ∈ Ioi (0 : ℝ), cexp (-((a : ℂ) * r)) * (1 + (r : ℂ) * e)⁻¹ =
      ∑ n ∈ Finset.range N, T n r + R r := by
    intro r hr
    have hd := hden0 r (le_of_lt hr)
    have hgeom : ∀ M : ℕ, (1 + (r : ℂ) * e)⁻¹ =
        ∑ n ∈ Finset.range M, (-((r : ℂ) * e))^n + (-((r : ℂ) * e))^M * (1 + (r : ℂ) * e)⁻¹ := by
      intro M
      have hg := geom_sum_mul (-((r : ℂ) * e)) M
      have hS : (∑ n ∈ Finset.range M, (-((r : ℂ) * e))^n) * (1 + (r : ℂ) * e) =
          1 - (-((r : ℂ) * e))^M := by linear_combination (-1 : ℂ) * hg
      have hS' : ∑ n ∈ Finset.range M, (-((r : ℂ) * e))^n =
          (1 - (-((r : ℂ) * e))^M) * (1 + (r : ℂ) * e)⁻¹ := by
        rw [← hS, mul_assoc, mul_inv_cancel₀ hd, mul_one]
      rw [hS']; ring
    rw [hgeom N, mul_add, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [hT]; simp only
    rw [neg_pow ((r : ℂ) * e), mul_pow, neg_pow e, neg_mul]; ring
  have hTi : ∀ n, IntegrableOn (T n) (Ioi 0) := fun n =>
    ((laplace_nat_pow hare n).1).const_mul _
  have hTint : ∀ n, ∫ r in Ioi (0 : ℝ), T n r = (-e)^n * (n.factorial / (a : ℂ)^(n+1)) := by
    intro n
    rw [hT]; simp only
    rw [integral_const_mul, (laplace_nat_pow hare n).2]
  have hRb : ∀ r ∈ Ioi (0 : ℝ), ‖R r‖ ≤ 1 / L * (Real.exp (-a * r) * r ^ N) := by
    intro r hr
    have hr : (0 : ℝ) < r := hr
    rw [hR]; simp only
    rw [norm_mul, norm_mul, norm_inv, norm_pow, norm_neg, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg hr.le, hen, mul_one,
      show -((a : ℂ) * r) = ((-a * r : ℝ) : ℂ) by push_cast; ring, Complex.norm_exp_ofReal]
    have h1 := hLden r hr.le
    have h2 : (‖1 + (r : ℂ) * e‖)⁻¹ ≤ 1 / L := by
      rw [one_div]; exact inv_anti₀ hL0 h1
    have : 0 ≤ Real.exp (-a * r) * r ^ N := by positivity
    calc Real.exp (-a * r) * (r ^ N * ‖1 + (r : ℂ) * e‖⁻¹)
        = (Real.exp (-a * r) * r ^ N) * ‖1 + (r : ℂ) * e‖⁻¹ := by ring
      _ ≤ (Real.exp (-a * r) * r ^ N) * (1 / L) := by gcongr
      _ = _ := by ring
  have hbi : IntegrableOn (fun r : ℝ => 1 / L * (Real.exp (-a * r) * r ^ N)) (Ioi 0) := by
    have : IntegrableOn (fun r : ℝ => 1 / L * ‖cexp (-(a : ℂ) * r) * (r : ℂ) ^ N‖) (Ioi 0) :=
      (laplace_nat_pow hare N).1.norm.const_mul (1 / L)
    refine this.congr_fun (fun r hr => ?_) measurableSet_Ioi
    have hr : (0 : ℝ) < r := hr
    simp only
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hr.le,
      show -(a : ℂ) * r = ((-a * r : ℝ) : ℂ) by push_cast; ring, Complex.norm_exp_ofReal]
  have hRc : ContinuousOn R (Ioi 0) := by
    intro r hr
    have hd := hden0 r (le_of_lt hr)
    rw [hR]
    refine ContinuousAt.continuousWithinAt ?_
    refine ContinuousAt.mul (by fun_prop) (ContinuousAt.mul (by fun_prop) ?_)
    exact ContinuousAt.inv₀ (by fun_prop) hd
  have hRi : IntegrableOn R (Ioi 0) :=
    Integrable.mono' hbi (hRc.aestronglyMeasurable measurableSet_Ioi)
      ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall hRb))
  have hint : ∫ r in Ioi (0 : ℝ), cexp (-((a : ℂ) * r)) * (1 + (r : ℂ) * e)⁻¹ =
      ∑ n ∈ Finset.range N, (-e)^n * (n.factorial / (a : ℂ)^(n+1)) +
        ∫ r in Ioi (0 : ℝ), R r := by
    rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_add
      (integrable_finsetSum _ fun n _ => hTi n) hRi, integral_finsetSum _ fun n _ => hTi n]
    simp only [hTint]
  have hRn := norm_integral_le_of_norm_le hbi
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall hRb))
  rw [integral_const_mul] at hRn
  have hlap := (laplace_nat_pow hare N).2
  have hlapr : ∫ r in Ioi (0 : ℝ), Real.exp (-a * r) * r ^ N = N.factorial / a^(N+1) := by
    have h' : ((∫ r in Ioi (0 : ℝ), Real.exp (-a * r) * r ^ N : ℝ) : ℂ) =
        ((N.factorial / a^(N+1) : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      push_cast
      rw [← hlap]
    exact_mod_cast h'
  rw [hlapr] at hRn
  -- assemble
  have hzpow : ∀ n : ℕ, z^(n+1) = (a : ℂ)^(n+1) / e^(n+1) := by
    intro n
    rw [← hze, mul_pow]; field_simp
  have hmain : genExpIntE 1 z - exp (-z)*∑ n ∈ Finset.range N,
      (-1 : ℂ)^n*(n.factorial : ℂ)/z^(n+1) = cexp (-z) * (e * ∫ r in Ioi (0 : ℝ), R r) := by
    rw [genExpIntE_one_eq_integral_rotate hz0 hz, ← hθ, ← he, ← ha, hint, mul_add,
      mul_add, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    have : ∀ n ∈ Finset.range N, cexp (-z) * (e * ((-e)^n * (n.factorial / (a : ℂ)^(n+1)))) =
        cexp (-z) * ((-1 : ℂ)^n*(n.factorial : ℂ)/z^(n+1)) := by
      intro n _
      rw [hzpow, neg_pow e]
      have ha' : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha0.ne'
      field_simp
      ring
    rw [Finset.sum_congr rfl this]
    ring
  rw [hmain, norm_mul, norm_mul, hen, one_mul]
  have hrhs : ‖exp (-z)*(N.factorial : ℂ)/z^(N+1)‖ = ‖exp (-z)‖ * (N.factorial / a^(N+1)) := by
    rw [norm_div, norm_mul, norm_pow, Complex.norm_natCast, ← ha]; ring
  rw [hrhs]
  have hc : (if |arg z| ≤ π/2 then (1:ℝ) else 1/Real.sin |arg z|) = 1 / L := by
    rw [hL]; split_ifs <;> simp
  rw [hc]
  calc ‖exp (-z)‖ * ‖∫ r in Ioi (0 : ℝ), R r‖
      ≤ ‖exp (-z)‖ * (1 / L * (N.factorial / a^(N+1))) := by gcongr
    _ = _ := by ring

/-- The tails `e^{-t}/t^m` are integrable on every right half-line with positive endpoint. -/
theorem integrableOn_exp_neg_div_pow {x : ℝ} (hx : 0 < x) (m : ℕ) :
    IntegrableOn (fun t : ℝ => Real.exp (-t)/t^m) (Ioi x) := by
  refine Integrable.mono' ((exp_neg_integrableOn_Ioi x one_pos).div_const (x^m)) ?_ ?_
  · exact (ContinuousOn.div (by fun_prop) (by fun_prop)
      fun t ht => pow_ne_zero _ (lt_trans hx ht).ne').aestronglyMeasurable measurableSet_Ioi
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun t ht => ?_)
    have ht0 : 0 < t := lt_trans hx ht
    rw [Real.norm_eq_abs, abs_of_pos (div_pos (Real.exp_pos _) (pow_pos ht0 m)), neg_one_mul]
    exact div_le_div_of_nonneg_left (Real.exp_pos _).le (pow_pos hx m)
      (pow_le_pow_left₀ hx.le (le_of_lt ht) m)

/-- One integration by parts in the `E₁` tail. -/
theorem integral_exp_neg_div_pow_succ {x : ℝ} (hx : 0 < x) (k : ℕ) :
    (∫ t in Ioi x, Real.exp (-t)/t^(k+1)) =
      Real.exp (-x)/x^(k+1) - (k+1)*∫ t in Ioi x, Real.exp (-t)/t^(k+2) := by
  have hd : ∀ t : ℝ, 0 < t → HasDerivAt (fun t => -(Real.exp (-t)/t^(k+1)))
      (Real.exp (-t)/t^(k+1) + (k+1)*(Real.exp (-t)/t^(k+2))) t := by
    intro t ht
    have ht0 : t ≠ 0 := ht.ne'
    have h := (((hasDerivAt_neg t).exp).div (hasDerivAt_pow (k+1) t) (pow_ne_zero _ ht0)).neg
    convert h using 1
    field_simp
    push_cast
    ring
  have hlim : Tendsto (fun t => -(Real.exp (-t)/t^(k+1))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => Real.exp (-t)/t^(k+1)) atTop (𝓝 0) := by
      have := (Real.tendsto_exp_neg_atTop_nhds_zero).div_atTop
        (tendsto_pow_atTop (Nat.succ_ne_zero k))
      exact this
    simpa using h1.neg
  have hi1 := integrableOn_exp_neg_div_pow hx (k+1)
  have hi2 := (integrableOn_exp_neg_div_pow hx (k+2)).const_mul ((k:ℝ)+1)
  have h := integral_Ioi_of_hasDerivAt_of_tendsto (hd x hx).continuousAt.continuousWithinAt
    (fun t ht => hd t (lt_trans hx ht)) (hi1.add hi2) hlim
  rw [integral_add hi1 hi2, integral_const_mul] at h
  linear_combination h

/-- Signed real remainder in DLMF §6.12(i). -/
lemma expIntE1_remainder_sign {x : ℝ} (hx : 0 < x) (N : ℕ) :
    0 ≤ (-1 : ℝ)^N * ((genExpIntE 1 x).re - Real.exp (-x)*∑ n ∈ Finset.range N, (-1 : ℝ)^n*(n.factorial : ℝ)/x^(n+1)) := by
  have hE : (genExpIntE 1 x).re = ∫ t in Ioi x, Real.exp (-t)/t^(0+1) := by
    rw [genExpIntE_one_eq_integral hx, Complex.ofReal_re]
    simp
  have key : ∀ N : ℕ, (genExpIntE 1 x).re - Real.exp (-x)*∑ n ∈ Finset.range N,
      (-1 : ℝ)^n*(n.factorial : ℝ)/x^(n+1) =
      (-1:ℝ)^N*N.factorial*∫ t in Ioi x, Real.exp (-t)/t^(N+1) := by
    intro N
    induction N with
    | zero => simp [hE]
    | succ N ih =>
      rw [Finset.sum_range_succ, mul_add, ← sub_sub, ih, integral_exp_neg_div_pow_succ hx N,
        Nat.factorial_succ]
      push_cast
      ring
  have h1 : (-1:ℝ)^N*(-1)^N = 1 := by rw [← pow_add, ← two_mul, pow_mul]; simp
  rw [key, ← mul_assoc, ← mul_assoc, h1, one_mul]
  refine mul_nonneg (by positivity) (setIntegral_nonneg measurableSet_Ioi fun t ht => ?_)
  exact div_nonneg (Real.exp_pos _).le (pow_nonneg (lt_trans hx ht).le _)

/-- The χ-dependent Ei remainder estimate in DLMF §6.12(i). -/
theorem expIntEi_remainder_bound {x : ℝ} (hx : 0 < x) (N : ℕ) :
    |Real.expIntEi x - Real.exp x*∑ n ∈ Finset.range N, (n.factorial : ℝ)/x^(n+1)| ≤ (1+Real.sqrt π*Real.Gamma (1+(N+1 : ℝ)/2)/Real.Gamma (1/2+(N+1 : ℝ)/2))*Real.exp x*(N.factorial : ℝ)/x^(N+1) := by
  sorry

/-- First omitted term and csc multiplier in DLMF §6.12(ii). -/
lemma expIntAux_remainder_bound (aux : Bool) {z : ℂ} (hz0 : z ≠ 0) (hz : |arg z| < π/2) (N : ℕ) :
    ‖expIntAsymptoticRemainder aux N z‖ ≤ (if |arg z| ≤ π/4 then 1 else 1/Real.sin (2*|arg z|)) * ‖expIntAsymptoticTerm aux N z‖ := by
  set m := 2 * N + if aux then 1 else 0 with hm
  set θ := -arg z with hθ
  have hre : 0 < z.re := by
    have := (Complex.abs_arg_lt_pi_div_two_iff.mp hz)
    rcases this with h | h
    · exact h
    · exact absurd h hz0
  have hr := expIntAux_remainder_integral_general aux hre N
  obtain ⟨c, hc0, hc⟩ := exists_pos_le_norm_one_add_ofReal_mul_exp (Φ := 2 * |θ|)
    (by rw [hθ, abs_neg]; linarith)
  have hden : ∀ r : ℝ, ∀ y : ℝ, |y| ≤ |θ| →
      ((r : ℂ) * exp (y * I)) ^ 2 + 1 = 1 + ((r ^ 2 : ℝ) : ℂ) * exp (((2 * y : ℝ) : ℂ) * I) := by
    intro r y _; rw [ofReal_mul_exp_ofReal_mul_I_sq]; ring
  have hdenc : ∀ r : ℝ, ∀ y : ℝ, |y| ≤ |θ| → c ≤ ‖((r : ℂ) * exp (y * I)) ^ 2 + 1‖ := by
    intro r y hy
    rw [hden r y hy]
    exact hc _ (sq_nonneg r) _ (by rw [abs_mul, abs_two]; linarith)
  have hFn : ∀ r : ℝ, 0 < r → ∀ y : ℝ, |y| ≤ |θ| →
      ‖((r : ℂ) * exp (y * I)) ^ m / (((r : ℂ) * exp (y * I)) ^ 2 + 1)‖ ≤ 1 / c * r ^ m := by
    intro r hr y hy
    rw [norm_div, norm_pow, norm_mul, Complex.norm_real, Real.norm_of_nonneg hr.le,
      norm_exp_ofReal_mul_I, mul_one, div_le_iff₀ (hc0.trans_le (hdenc r y hy))]
    have := hdenc r y hy
    rw [show 1 / c * r ^ m * ‖((r : ℂ) * exp (y * I)) ^ 2 + 1‖ =
      r ^ m * (‖((r : ℂ) * exp (y * I)) ^ 2 + 1‖ / c) by ring]
    exact le_mul_of_one_le_right (by positivity) ((one_le_div hc0).mpr this)
  have hrot := integral_cexp_neg_mul_mul_eq_rotate
    (F := fun t : ℂ => t ^ m / (t ^ 2 + 1)) (θ := θ) (σ := 1) (C := 1 / c) (k := m) (z := z)
    one_pos
    (fun r hr y hy => by
      have hne : ((r : ℂ) * exp (y * I)) ^ 2 + 1 ≠ 0 := fun h0 => by
        have := hdenc r y (abs_le_abs_of_mem_uIcc_zero hy); rw [h0, norm_zero] at this
        linarith
      exact (differentiableAt_pow m).div ((differentiableAt_pow 2).add_const 1) hne)
    (fun r hr hr1 y hy => by
      refine (hFn r hr y (abs_le_abs_of_mem_uIcc_zero hy)).trans ?_
      rw [sub_self, Real.rpow_zero, mul_one]
      have : r ^ m ≤ 1 := pow_le_one₀ hr.le hr1
      have : 0 < 1 / c := by positivity
      nlinarith)
    (fun r hr y hy => by
      rw [Real.rpow_natCast]
      exact hFn r (by linarith) y (abs_le_abs_of_mem_uIcc_zero hy))
    (fun y hy => by
      rw [re_mul_exp_ofReal_mul_I]
      have h1 : |arg z + y| ≤ |arg z| := by
        rcases le_total 0 (arg z) with h | h
        · rw [hθ, uIcc_of_ge (by linarith)] at hy
          rw [abs_of_nonneg h, abs_le]; constructor <;> linarith [hy.1, hy.2]
        · rw [hθ, uIcc_of_le (by linarith)] at hy
          rw [abs_of_nonpos h, abs_le]; constructor <;> linarith [hy.1, hy.2]
      have h2 : 0 < Real.cos (arg z + y) := by
        rw [← Real.cos_abs]
        exact Real.cos_pos_of_mem_Ioo ⟨by linarith [abs_nonneg (arg z + y), Real.pi_pos],
          by linarith⟩
      exact mul_pos (norm_pos_iff.mpr hz0) h2)
  have hI : ∫ t : ℝ in Ioi 0, exp (-z*t)*(t : ℂ)^m/((t : ℂ)^2+1) =
      ∫ t : ℝ in Ioi 0, cexp (-(z * t)) * ((t : ℂ) ^ m / ((t : ℂ) ^ 2 + 1)) :=
    setIntegral_congr_fun measurableSet_Ioi fun t _ => by ring_nf
  have hze : z * exp (θ * I) = (‖z‖ : ℂ) := by
    conv_lhs => rw [← norm_mul_exp_arg_mul_I z]
    rw [hθ, mul_assoc, ← Complex.exp_add]
    push_cast
    simp
  rw [hr, hI, hrot, hze]
  set L : ℝ := if |arg z| ≤ π/4 then 1 else Real.sin (2*|arg z|) with hL
  have hsin2 : |Real.sin (2 * θ)| = Real.sin (2 * |arg z|) := by
    have hpos : 0 ≤ Real.sin (2 * |arg z|) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by linarith)
    have key : |Real.sin (2 * (-arg z))| = |Real.sin (2 * |arg z|)| := by
      rcases le_total 0 (arg z) with h | h
      · rw [abs_of_nonneg h, mul_neg, Real.sin_neg, abs_neg]
      · rw [abs_of_nonpos h]
    rw [hθ, key, abs_of_nonneg hpos]
  have hL0 : 0 < L := by
    rw [hL]; split_ifs with h
    · exact one_pos
    · push Not at h
      exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hLden : ∀ r : ℝ, L ≤ ‖((r : ℂ) * exp (θ * I)) ^ 2 + 1‖ := by
    intro r
    rw [hden r θ le_rfl]
    rw [hL]; split_ifs with h
    · refine one_le_norm_one_add_ofReal_mul_exp (sq_nonneg r) ?_
      rw [← Real.cos_abs, abs_mul, abs_two, hθ, abs_neg]
      exact Real.cos_nonneg_of_mem_Icc ⟨by linarith [abs_nonneg (arg z), Real.pi_pos],
        by linarith⟩
    · rw [← hsin2]; exact abs_sin_le_norm_one_add_ofReal_mul_exp _ _
  have hs : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hbound : ∀ r ∈ Ioi (0 : ℝ), ‖cexp (-((‖z‖ : ℂ) * r)) *
      (((r : ℂ) * exp (θ * I)) ^ m / (((r : ℂ) * exp (θ * I)) ^ 2 + 1))‖ ≤
      1 / L * (Real.exp (-‖z‖ * r) * r ^ ((m : ℝ) + 1 - 1)) := by
    intro r hr
    have hr : (0 : ℝ) < r := hr
    rw [norm_mul, show -((‖z‖ : ℂ) * r) = ((-‖z‖ * r : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_exp_ofReal, norm_div, norm_pow, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg hr.le, norm_exp_ofReal_mul_I, mul_one, add_sub_cancel_right,
      Real.rpow_natCast]
    have h1 := hLden r
    have h2 : r ^ m / ‖((r : ℂ) * exp (θ * I)) ^ 2 + 1‖ ≤ r ^ m / L :=
      div_le_div_of_nonneg_left (by positivity) hL0 h1
    calc Real.exp (-‖z‖ * r) * (r ^ m / ‖((r : ℂ) * exp (θ * I)) ^ 2 + 1‖)
        ≤ Real.exp (-‖z‖ * r) * (r ^ m / L) := by gcongr
      _ = _ := by ring
  have hint := (integrableOn_exp_neg_mul_mul_rpow_sub_one hs hzn).const_mul (1 / L)
  have hnorm := norm_integral_le_of_norm_le hint
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall hbound))
  rw [integral_const_mul, integral_exp_neg_mul_mul_rpow_sub_one hs hzn,
    Real.Gamma_nat_eq_factorial, Real.rpow_neg hzn.le,
    show (m : ℝ) + 1 = ((m + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast] at hnorm
  have hexp : (2 * N + if aux then 2 else 1) = m + 1 := by
    rw [hm]; cases aux <;> simp
  rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_exp_ofReal_mul_I,
    one_mul, expIntAsymptoticTerm, hexp, ← hm, norm_div, norm_mul, norm_pow, norm_neg, norm_one,
    one_pow, one_mul, norm_pow, Complex.norm_natCast]
  refine hnorm.trans (le_of_eq ?_)
  rw [hL]
  split_ifs <;> field_simp

/-- Signed real auxiliary-function remainder. -/
lemma expIntAux_remainder_sign (aux : Bool) {x : ℝ} (hx : 0 < x) (N : ℕ) :
    0 ≤ (expIntAsymptoticRemainder aux N x).re * (expIntAsymptoticTerm aux N x).re := by
  set m := 2*N+if aux then 1 else 0
  have hr := expIntAux_remainder_integral_general aux (z := x) (by simpa using hx) N
  have hI : (∫ t : ℝ in Ioi 0, exp (-(x:ℂ)*t)*(t : ℂ)^m/((t : ℂ)^2+1)) =
      ((∫ t : ℝ in Ioi 0, Real.exp (-x*t)*t^m/(t^2+1) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    push_cast; rfl
  have hpos : 0 ≤ ∫ t : ℝ in Ioi 0, Real.exp (-x*t)*t^m/(t^2+1) :=
    setIntegral_nonneg measurableSet_Ioi fun t ht => by
      have : 0 < t := ht
      positivity
  rw [hr, hI, expIntAsymptoticTerm]
  have h1 : ((-1:ℂ)^N*((∫ t : ℝ in Ioi 0, Real.exp (-x*t)*t^m/(t^2+1) : ℝ) : ℂ)).re =
      (-1:ℝ)^N*∫ t : ℝ in Ioi 0, Real.exp (-x*t)*t^m/(t^2+1) := by
    rw [show (-1:ℂ)^N = (((-1:ℝ)^N : ℝ) : ℂ) by push_cast; rfl, ← ofReal_mul, ofReal_re]
  have h2 : ((-1 : ℂ)^N * ((2*N + if aux then 1 else 0).factorial : ℂ) / (x:ℂ)^(2*N + if aux then 2 else 1)).re =
      (-1:ℝ)^N * ((2*N + if aux then 1 else 0).factorial : ℝ) / x^(2*N + if aux then 2 else 1) := by
    rw [show (-1 : ℂ)^N * ((2*N + if aux then 1 else 0).factorial : ℂ) / (x:ℂ)^(2*N + if aux then 2 else 1) =
      (((-1:ℝ)^N * ((2*N + if aux then 1 else 0).factorial : ℝ) / x^(2*N + if aux then 2 else 1) : ℝ) : ℂ) by
      push_cast; rfl, ofReal_re]
  rw [h1, h2]
  have : 0 ≤ ((2*N + if aux then 1 else 0).factorial : ℝ) / x^(2*N + if aux then 2 else 1) := by positivity
  have e : (-1:ℝ)^N*(-1:ℝ)^N = 1 := by rw [← mul_pow]; simp
  calc 0 ≤ (∫ t : ℝ in Ioi 0, Real.exp (-x*t)*t^m/(t^2+1)) *
        (((2*N + if aux then 1 else 0).factorial : ℝ) / x^(2*N + if aux then 2 else 1)) := mul_nonneg hpos this
    _ = _ := by rw [mul_div_assoc]; linear_combination (-(∫ t : ℝ in Ioi 0, Real.exp (-x*t)*t^m/(t^2+1)) *
        (((2*N + if aux then 1 else 0).factorial : ℝ) / x^(2*N + if aux then 2 else 1)))*e

end DLMF.Confluent
