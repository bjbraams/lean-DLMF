/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.ParabolicCylinder.Uniform
public import DLMFMathlib.Analysis.ODE.LiouvilleGreenExpansion

/-!
# Olver's uniform expansion of `U(-½μ², μt√2)` for `t > 1` (DLMF 12.10.3)

With `a = -½μ²` and `z = μ t √2`, Weber's equation becomes `d²w/dt² = μ⁴ (t²-1) w`. We apply the
Liouville–Green expansion with error bounds (`LiouvilleGreen.exists_solution_expansion_exp`,
Olver, *Asymptotics and Special Functions*, Ch. 10, Thm. 3.1) with `u = μ²`,
`A = (t²-1)^{-1/4}`, `g = 0` and the coefficients `(-1)^s A_s(t)`, `A_s = u_s(t)/(t²-1)^{3s/2}`
(DLMF 12.10.8). The polynomial recursions DLMF 12.10.11–12.10.12 are exactly the Liouville–Green
recursion `A² A_s'' + 2AA'A_s' + AA''A_s = 2A_{s+1}'` (`pcfLG_recursion`). The constructed
solution is identified with `U` as the recessive solution at `+∞`: a Wronskian argument
(`pcfLG_eq_mul_of_tendsto`) together with the large-`t` limit
`U/(A e^{-μ²ξ}) → h(μ)` (`pcfLG_tendsto_U_div`, from DLMF 12.9.1). The normalizer is
`g = h/Φ(μ²)`, where `Φ` realizes the formal series `∑ c_s u^{-s}`, `c_s = lim_{t→∞} A_s(t)`
(`pcfLG_exists_asymptotic`, a Borel-type lemma).

## Main results

* `pcfLG_core`: the uniform estimate for each truncation order.
* `pcf_negative_parameter_uniform_U`: DLMF 12.10.3 with the normalizer
  `g(μ) ∼ h(μ)/∑ c_s μ^{-2s}`.

DLMF 12.10.14 (`IsCylinderGNormalizer`) additionally requires the identity
`(∑ c_s u^{-s})·(1 + ½∑ γ_s (u/2)^{-s}) ∼ 1`, which is not proved here.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF
open scoped Real Topology Nat
namespace DLMF.Confluent
open Polynomial

/-- A function with vanishing derivative on `(b, ∞)` is constant there. -/
lemma pcfLG_const_of_hasDerivAt_zero {b : ℝ} {f : ℝ → ℂ} (h : ∀ t, b < t → HasDerivAt f 0 t) :
    ∃ a, ∀ t, b < t → f t = a := by
  obtain ⟨a, ha⟩ := (isOpen_Ioi (a := b)).exists_is_const_of_deriv_eq_zero isPreconnected_Ioi
    (fun t ht => (h t ht).differentiableAt.differentiableWithinAt)
    (fun t ht => (h t ht).deriv)
  exact ⟨a, fun t ht => ha t ht⟩

/-- **Uniqueness of the recessive solution.** Let `U` (complex) and `W` (real, nonvanishing,
tending to `0`) solve `w'' = q w` on `(b, ∞)`. If `U / W` has a limit at `+∞`, then `U` is a
constant multiple of `W` on `(b, ∞)`. -/
lemma pcfLG_eq_mul_of_tendsto {b : ℝ} {q : ℝ → ℝ} {U U' : ℝ → ℂ} {W W' : ℝ → ℝ}
    (hU : ∀ t, b < t → HasDerivAt U (U' t) t) (hU' : ∀ t, b < t → HasDerivAt U' (q t * U t) t)
    (hW : ∀ t, b < t → HasDerivAt W (W' t) t) (hW' : ∀ t, b < t → HasDerivAt W' (q t * W t) t)
    (hW0 : ∀ t, b < t → W t ≠ 0) (hWl : Tendsto W atTop (𝓝 0)) {L : ℂ}
    (hl : Tendsto (fun t => U t / W t) atTop (𝓝 L)) :
    ∃ κ : ℂ, ∀ t, b < t → U t = κ * W t := by
  have hWc : ∀ t, b < t → HasDerivAt (fun s => (W s : ℂ)) (W' t) t := fun t ht =>
    (hW t ht).ofReal_comp
  have hWc' : ∀ t, b < t → HasDerivAt (fun s => (W' s : ℂ)) ((q t : ℂ) * W t) t := fun t ht => by
    simpa using (hW' t ht).ofReal_comp
  -- the Wronskian is constant
  obtain ⟨C, hC⟩ := pcfLG_const_of_hasDerivAt_zero (b := b)
    (f := fun t => U t * W' t - U' t * W t) (fun t ht => by
      have := ((hU t ht).mul (hWc' t ht)).sub ((hU' t ht).mul (hWc t ht))
      convert this using 1; ring)
  -- derivative of the quotient
  have hg : ∀ t, b < t → HasDerivAt (fun s => U s / W s) (-C * (((W t)^2)⁻¹ : ℝ)) t := by
    intro t ht
    have hw : (W t : ℂ) ≠ 0 := by exact_mod_cast hW0 t ht
    have := (hU t ht).div (hWc t ht) hw
    convert this using 1
    rw [← hC t ht]; push_cast; field_simp; ring
  by_cases hC0 : C = 0
  · obtain ⟨κ, hκ⟩ := pcfLG_const_of_hasDerivAt_zero (b := b) (f := fun s => U s / W s)
      (fun t ht => by simpa [hC0] using hg t ht)
    refine ⟨κ, fun t ht => ?_⟩
    have := hκ t ht
    have hw : (W t : ℂ) ≠ 0 := by exact_mod_cast hW0 t ht
    rw [← this]; field_simp
  · exfalso
    set η : ℝ := Real.sqrt ‖C‖ / 2 with hη
    have hCpos : 0 < ‖C‖ := norm_pos_iff.2 hC0
    have hηpos : 0 < η := by positivity
    have hd : Tendsto (fun t => U (t+1) / W (t+1) - U t / W t) atTop (𝓝 0) := by
      have h1 := hl.comp (tendsto_atTop_add_const_right _ 1 tendsto_id)
      simpa using h1.sub hl
    have hev1 : ∀ᶠ t in atTop, ‖U (t+1) / W (t+1) - U t / W t‖ < 1 :=
      (tendsto_order.1 (tendsto_norm.comp hd)).2 1 (by simp)
    have hev2 : ∀ᶠ s in atTop, |W s| < η :=
      (tendsto_order.1 (by simpa using hWl.abs)).2 η hηpos
    obtain ⟨T, hT⟩ := (hev1.and ((eventually_ge_atTop (b+1)).and
      (eventually_forall_ge_atTop.2 hev2))).exists_forall_of_atTop
    obtain ⟨h1, hTb, h3⟩ := hT T le_rfl
    -- FTC on `[T, T+1]`
    have hcont : ContinuousOn (fun s => ((W s)^2)⁻¹) (Icc T (T+1)) := by
      intro s hs
      have hs' : b < s := by linarith [hs.1]
      exact ((hW s hs').continuousAt.pow 2).inv₀ (pow_ne_zero 2 (hW0 s hs'))
        |>.continuousWithinAt
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := T) (b := T+1)
      (f := fun s => U s / W s) (f' := fun s => -C * ((((W s)^2)⁻¹ : ℝ) : ℂ))
      (fun s hs => hg s (by rw [uIcc_of_le (by linarith)] at hs; linarith [hs.1]))
      ((continuousOn_const.mul (continuous_ofReal.comp_continuousOn hcont)).intervalIntegrable_of_Icc
        (by linarith))
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal] at hFTC
    have hlow : (η^2)⁻¹ ≤ ∫ s in T..T+1, ((W s)^2)⁻¹ := by
      have := intervalIntegral.integral_mono_on (a := T) (b := T+1) (f := fun _ => (η^2)⁻¹)
        (g := fun s => ((W s)^2)⁻¹) (μ := volume) (by linarith) intervalIntegrable_const
        (hcont.intervalIntegrable_of_Icc (by linarith)) (fun s hs => by
          have hs' : b < s := by linarith [hs.1]
          have hw := hW0 s hs'
          have hlt := h3 s hs.1
          have : (W s)^2 < η^2 := by
            have := sq_abs (W s); nlinarith [abs_nonneg (W s)]
          exact inv_anti₀ (by positivity) this.le)
      simpa using this
    have hnorm : ‖U (T+1) / W (T+1) - U T / W T‖ = ‖C‖ * ∫ s in T..T+1, ((W s)^2)⁻¹ := by
      rw [← hFTC, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
      exact intervalIntegral.integral_nonneg (by linarith) fun s _ => by positivity
    have hη2 : η^2 = ‖C‖ / 4 := by
      rw [hη, div_pow, Real.sq_sqrt hCpos.le]; norm_num
    have : 4 ≤ ‖C‖ * ∫ s in T..T+1, ((W s)^2)⁻¹ := by
      calc (4:ℝ) = ‖C‖ * (η^2)⁻¹ := by rw [hη2]; field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left hlow hCpos.le
    linarith [hnorm ▸ h1]

/-- **Borel's lemma at infinity** (real coefficients): every formal series `∑ c_s u^{-s}` is
the asymptotic expansion of some function, here a truncation `∑_{s<n(u)} c_s u^{-s}` with
`n(u)` the largest `n ≤ ⌊u⌋` for which `∑_{s<n} |c_s| ≤ u`. -/
lemma pcfLG_exists_asymptotic (c : ℕ → ℝ) : ∃ F : ℝ → ℝ, ∀ N : ℕ,
    (fun u : ℝ => F u - ∑ s ∈ Finset.range N, c s / u^s) =O[atTop] (fun u : ℝ => (u^N)⁻¹) := by
  classical
  let n : ℝ → ℕ := fun u => Nat.findGreatest (fun m => ∑ s ∈ Finset.range m, |c s| ≤ u) ⌊u⌋₊
  refine ⟨fun u => ∑ s ∈ Finset.range (n u), c s / u^s, fun N => ?_⟩
  refine IsBigO.of_bound (|c N| + 1) ?_
  filter_upwards [eventually_ge_atTop (1:ℝ), eventually_ge_atTop (N:ℝ),
    eventually_ge_atTop (∑ s ∈ Finset.range N, |c s|)] with u hu1 huN huS
  have hu0 : 0 < u := by linarith
  have hP0 : ∑ s ∈ Finset.range 0, |c s| ≤ u := by simp; linarith
  have hspec : ∑ s ∈ Finset.range (n u), |c s| ≤ u :=
    Nat.findGreatest_spec (P := fun m => ∑ s ∈ Finset.range m, |c s| ≤ u) (Nat.zero_le _) hP0
  have hNn : N ≤ n u := Nat.le_findGreatest (Nat.le_floor huN) huS
  have hsplit : (∑ s ∈ Finset.range (n u), c s / u^s) - ∑ s ∈ Finset.range N, c s / u^s =
      ∑ s ∈ Finset.Ico N (n u), c s / u^s := by
    rw [← Finset.sum_range_add_sum_Ico _ hNn]; ring
  rw [hsplit, Real.norm_eq_abs, Real.norm_eq_abs, abs_inv, abs_pow, abs_of_pos hu0]
  rcases Nat.lt_or_ge N (n u) with hlt | hge
  · rw [Finset.sum_eq_sum_Ico_succ_bot hlt]
    have h1 : |c N / u^N| = |c N| * (u^N)⁻¹ := by
      rw [abs_div, abs_pow, abs_of_pos hu0, div_eq_mul_inv]
    have h2 : |∑ s ∈ Finset.Ico (N+1) (n u), c s / u^s| ≤ (u^N)⁻¹ := by
      calc |∑ s ∈ Finset.Ico (N+1) (n u), c s / u^s|
          ≤ ∑ s ∈ Finset.Ico (N+1) (n u), |c s| * (u^(N+1))⁻¹ := by
            refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun s hs => ?_)
            rw [abs_div, abs_pow, abs_of_pos hu0, div_eq_mul_inv]
            refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
            exact inv_anti₀ (by positivity) (pow_le_pow_right₀ hu1 (Finset.mem_Ico.1 hs).1)
        _ = (∑ s ∈ Finset.Ico (N+1) (n u), |c s|) * (u^(N+1))⁻¹ := by rw [Finset.sum_mul]
        _ ≤ u * (u^(N+1))⁻¹ := by
            refine mul_le_mul_of_nonneg_right ((Finset.sum_le_sum_of_subset_of_nonneg
              (fun s hs => Finset.mem_range.2 (Finset.mem_Ico.1 hs).2)
              (fun s _ _ => abs_nonneg _)).trans hspec) (by positivity)
        _ = (u^N)⁻¹ := by rw [pow_succ]; field_simp
    calc |c N / u^N + ∑ s ∈ Finset.Ico (N+1) (n u), c s / u^s|
        ≤ |c N| * (u^N)⁻¹ + (u^N)⁻¹ := (abs_add_le _ _).trans (by rw [h1]; linarith)
      _ = (|c N| + 1) * (u^N)⁻¹ := by ring
  · rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty, abs_zero]; positivity

/-- Combining real powers of a positive base. -/
lemma pcfLG_rpow_mul {y : ℝ} (hy : 0 < y) {a b c : ℝ} (h : a + b = c) :
    y ^ a * y ^ b = y ^ c := by
  rw [← Real.rpow_add hy, h]

/-- Derivative of `P(t) (t²-1)^c` on `t > 1`. -/
lemma pcfLG_hasDerivAt_poly_rpow (P : Polynomial ℝ) (c : ℝ) {t : ℝ} (ht : 1 < t) :
    HasDerivAt (fun t => P.eval t * (t^2-1) ^ c)
      (((derivative P).eval t * (t^2-1) + 2*c*t*P.eval t) * (t^2-1) ^ (c-1)) t := by
  have hy : 0 < t^2-1 := by nlinarith
  have h1 : HasDerivAt (fun t : ℝ => t^2-1) (2*t) t := by
    simpa using (hasDerivAt_pow 2 t).sub_const 1
  have h2 := h1.rpow_const (p := c) (Or.inl hy.ne')
  have := (P.hasDerivAt t).mul h2
  convert this using 1
  have e : (t^2-1) ^ c = (t^2-1) * (t^2-1) ^ (c-1) := by
    conv_lhs => rw [show c = 1 + (c-1) by ring]
    rw [Real.rpow_add hy, Real.rpow_one]
  rw [e]; ring

/-- The Liouville–Green amplitude `A = (t²-1)^{-1/4}`. -/
def pcfLG_A (t : ℝ) : ℝ := (t^2-1) ^ (-1/4:ℝ)
/-- `A'`. -/
def pcfLG_A1 (t : ℝ) : ℝ := -(t/2) * (t^2-1) ^ (-5/4:ℝ)
/-- `A''`. -/
def pcfLG_A2 (t : ℝ) : ℝ := (3*t^2+2)/4 * (t^2-1) ^ (-9/4:ℝ)

/-- Olver's coefficient `A_s(t) = u_s(t)/(t²-1)^{3s/2}` (DLMF 12.10.8), real form. -/
def pcfLG_hatA (s : ℕ) (t : ℝ) : ℝ := (pcfOlverU s).eval t * (t^2-1) ^ (-(3*s/2:ℝ))
/-- `A_s'(t) = r_{s-1}(t)/(t²-1)^{(3s+2)/2}`. -/
def pcfLG_hatAd (s : ℕ) (t : ℝ) : ℝ :=
  (pcfOlverPair s).2.eval t * (t^2-1) ^ (-((3*s+2)/2:ℝ))
/-- `A_s''`. -/
def pcfLG_hatAd2 (s : ℕ) (t : ℝ) : ℝ :=
  ((derivative (pcfOlverPair s).2).eval t * (t^2-1) - (3*s+2)*t*(pcfOlverPair s).2.eval t) *
    (t^2-1) ^ (-((3*s+4)/2):ℝ)

/-- `A' = -(t/2)(t²-1)^{-5/4}`. -/
lemma pcfLG_hasDerivAt_A {t : ℝ} (ht : 1 < t) : HasDerivAt pcfLG_A (pcfLG_A1 t) t := by
  have := pcfLG_hasDerivAt_poly_rpow 1 (-1/4) ht
  simp only [eval_one, one_mul, derivative_one, eval_zero, zero_mul, zero_add, mul_one] at this
  unfold pcfLG_A pcfLG_A1
  convert this using 1
  rw [show (-1/4:ℝ) - 1 = -5/4 by norm_num]; ring

/-- `A'' = (3t²+2)/4 · (t²-1)^{-9/4}`. -/
lemma pcfLG_hasDerivAt_A1 {t : ℝ} (ht : 1 < t) : HasDerivAt pcfLG_A1 (pcfLG_A2 t) t := by
  have hy : 0 < t^2-1 := by nlinarith
  have := pcfLG_hasDerivAt_poly_rpow (C (-1/2:ℝ) * X) (-5/4) ht
  unfold pcfLG_A1 pcfLG_A2
  convert this using 1
  · funext t; simp; ring
  · rw [show (-5/4:ℝ) - 1 = -9/4 by norm_num]
    simp only [eval_mul, eval_C, eval_X, derivative_mul, derivative_C, derivative_X, zero_mul,
      zero_add, mul_one]
    ring

/-- `A_s' ` from the Olver recursion (DLMF 12.10.11). -/
lemma pcfLG_olverU_eq (s : ℕ) :
    (X^2-1)*derivative (pcfOlverU s)-C (3*(s:ℝ))*X*pcfOlverU s = (pcfOlverPair s).2 := by
  rcases s with _ | s
  · simp [pcfOlverU, pcfOlverPair]
  · have := (pcfOlverU_spec s).1
    rw [pcfOlverR] at this
    push_cast; exact this

/-- `A_s' = r_{s-1}(t)/(t²-1)^{(3s+2)/2}`, from DLMF 12.10.11. -/
lemma pcfLG_hasDerivAt_hatA (s : ℕ) {t : ℝ} (ht : 1 < t) :
    HasDerivAt (pcfLG_hatA s) (pcfLG_hatAd s t) t := by
  have := pcfLG_hasDerivAt_poly_rpow (pcfOlverU s) (-(3*s/2)) ht
  have he := congrArg (Polynomial.eval t) (pcfLG_olverU_eq s)
  simp only [eval_sub, eval_mul, eval_pow, eval_X, eval_one, eval_C] at he
  unfold pcfLG_hatA pcfLG_hatAd
  convert this using 1
  rw [← he, show -(3*(s:ℝ)/2) - 1 = -((3*s+2)/2) by ring]; ring

/-- The derivative of `A_s'`. -/
lemma pcfLG_hasDerivAt_hatAd (s : ℕ) {t : ℝ} (ht : 1 < t) :
    HasDerivAt (pcfLG_hatAd s) (pcfLG_hatAd2 s t) t := by
  have := pcfLG_hasDerivAt_poly_rpow (pcfOlverPair s).2 (-((3*s+2)/2)) ht
  unfold pcfLG_hatAd pcfLG_hatAd2
  convert this using 1
  rw [show -((3*(s:ℝ)+2)/2) - 1 = -((3*s+4)/2) by ring]; ring

/-- The second Olver polynomial of the pair is `r_s` (DLMF 12.10.12). -/
lemma pcfLG_olverPair_snd_succ (s : ℕ) : (pcfOlverPair (s+1)).2 =
    C (1/8:ℝ)*(C 3*X^2+C 2)*(pcfOlverPair s).1 - C (3/2*(s+1:ℝ))*X*(pcfOlverPair s).2 +
      C (1/2:ℝ)*(X^2-1)*derivative (pcfOlverPair s).2 := by
  rw [pcfOlverPair]

/-- **The Liouville–Green recursion for Olver's coefficients**: with `A = (t²-1)^{-1/4}`,
`A² A_s'' + 2 A A' A_s' + A A'' A_s = 2 A_{s+1}'`. -/
lemma pcfLG_recursion (s : ℕ) {t : ℝ} (ht : 1 < t) :
    pcfLG_A t ^ 2 * pcfLG_hatAd2 s t + 2 * pcfLG_A t * pcfLG_A1 t * pcfLG_hatAd s t +
      pcfLG_A t * pcfLG_A2 t * pcfLG_hatA s t = 2 * pcfLG_hatAd (s+1) t := by
  have hy : 0 < t^2-1 := by nlinarith
  set y := t^2-1
  set Z := y ^ (-((3*(s:ℝ)+5)/2))
  have e1 : pcfLG_A t ^ 2 * y ^ (-((3*(s:ℝ)+4)/2)) = Z := by
    rw [pcfLG_A, ← Real.rpow_natCast, ← Real.rpow_mul hy.le]
    exact pcfLG_rpow_mul hy (by push_cast; ring)
  have e2 : pcfLG_A t * y ^ (-5/4:ℝ) * y ^ (-((3*(s:ℝ)+2)/2)) = Z := by
    rw [pcfLG_A, pcfLG_rpow_mul hy (c := -3/2) (by norm_num)]
    exact pcfLG_rpow_mul hy (by ring)
  have e3 : pcfLG_A t * y ^ (-9/4:ℝ) * y ^ (-(3*(s:ℝ)/2)) = Z := by
    rw [pcfLG_A, pcfLG_rpow_mul hy (c := -5/2) (by norm_num)]
    exact pcfLG_rpow_mul hy (by ring)
  have e4 : y ^ (-((3*((s+1:ℕ):ℝ)+2)/2)) = Z := by simp only [Z]; congr 1; push_cast; ring
  have hp := congrArg (Polynomial.eval t) (pcfLG_olverPair_snd_succ s)
  simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_one, eval_C] at hp
  simp only [pcfLG_hatAd2, pcfLG_hatAd, pcfLG_hatA, pcfLG_A1, pcfLG_A2]
  rw [e4, hp]
  have : pcfOlverU s = (pcfOlverPair s).1 := rfl
  rw [this]
  linear_combination
    ((derivative (pcfOlverPair s).2).eval t * y - (3*s+2)*t*(pcfOlverPair s).2.eval t) * e1 +
    (-t * (pcfOlverPair s).2.eval t) * e2 + ((3*t^2+2)/4 * (pcfOlverPair s).1.eval t) * e3

/-- `ξ' = √(t²-1)` (DLMF 12.10.7). -/
lemma pcfLG_hasDerivAt_xi {t : ℝ} (ht : 1 < t) :
    HasDerivAt pcfXi (Real.sqrt (t^2-1)) t := by
  have hy : 0 < t^2-1 := by nlinarith
  set r := Real.sqrt (t^2-1) with hr
  have hr0 : 0 < r := Real.sqrt_pos.2 hy
  have hr2 : r^2 = t^2-1 := Real.sq_sqrt hy.le
  have h1 : HasDerivAt (fun t : ℝ => t^2-1) (2*t) t := by
    simpa using (hasDerivAt_pow 2 t).sub_const 1
  have hs : HasDerivAt (fun t : ℝ => Real.sqrt (t^2-1)) (2*t / (2 * r)) t := h1.sqrt hy.ne'
  have htr : 0 < t + r := by linarith
  have hl : HasDerivAt (fun t : ℝ => Real.log (t + Real.sqrt (t^2-1))) ((1 + 2*t/(2*r)) / (t + r)) t :=
    ((hasDerivAt_id t).add hs).log htr.ne'
  have := (((hasDerivAt_id t).mul hs).sub hl).div_const 2
  have e : pcfXi = fun x => ((((id : ℝ → ℝ) * fun t : ℝ => Real.sqrt (t^2-1)) -
      fun t : ℝ => Real.log (t + Real.sqrt (t^2-1))) : ℝ → ℝ) x / 2 := by
    funext x; simp [pcfXi]
  rw [e]
  convert this using 1
  simp only [id]
  field_simp
  rw [← hr]
  nlinarith [hr2]

/-- `A⁻² = √(t²-1)`. -/
lemma pcfLG_A_sq_recip {t : ℝ} (ht : 1 < t) : (pcfLG_A t ^ 2)⁻¹ = Real.sqrt (t^2-1) := by
  have hy : 0 < t^2-1 := by nlinarith
  rw [pcfLG_A, ← Real.rpow_natCast, ← Real.rpow_mul hy.le, ← Real.rpow_neg hy.le,
    Real.sqrt_eq_rpow]
  norm_num

/-- `A⁻⁴ = t²-1`. -/
lemma pcfLG_A_pow_four_recip {t : ℝ} (ht : 1 < t) : (pcfLG_A t ^ 4)⁻¹ = t^2-1 := by
  have hy : 0 < t^2-1 := by nlinarith
  rw [pcfLG_A, ← Real.rpow_natCast, ← Real.rpow_mul hy.le, ← Real.rpow_neg hy.le]
  norm_num

/-- `A(t) > 0` for `t > 1`. -/
lemma pcfLG_A_pos {t : ℝ} (ht : 1 < t) : 0 < pcfLG_A t := by
  have hy : 0 < t^2-1 := by nlinarith
  exact Real.rpow_pos_of_pos hy _

/-- A polynomial bound for `t ≥ 1`. -/
lemma pcfLG_abs_eval_le (P : Polynomial ℝ) {d : ℕ} (hd : P.natDegree ≤ d) {t : ℝ} (ht : 1 ≤ t) :
    |P.eval t| ≤ (∑ i ∈ Finset.range (d+1), |P.coeff i|) * t^d := by
  rw [eval_eq_sum_range' (Nat.lt_succ_of_le hd), Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => ?_)
  rw [abs_mul, abs_pow, abs_of_pos (by linarith : (0:ℝ) < t)]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht (Nat.lt_succ_iff.1
    (Finset.mem_range.1 hi))) (abs_nonneg _)

/-- `|P(t)| (t²-1)^{-e} ≤ K t^{d-2e}` for `t ≥ c > 1`. -/
lemma pcfLG_poly_rpow_bound (P : Polynomial ℝ) {d : ℕ} (hd : P.natDegree ≤ d) {e c : ℝ}
    (he : 0 ≤ e) (hc : 1 < c) : ∃ K, 0 ≤ K ∧ ∀ t, c ≤ t →
      |P.eval t * (t^2-1) ^ (-e)| ≤ K * t ^ ((d:ℝ) - 2*e) := by
  set S := ∑ i ∈ Finset.range (d+1), |P.coeff i|
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hc2 : 0 < 1 - 1/c^2 := by
    have : 1/c^2 < 1 := by rw [div_lt_one (by positivity)]; nlinarith
    linarith
  refine ⟨S * (1 - 1/c^2) ^ (-e), by positivity, fun t ht => ?_⟩
  have ht0 : 0 < t := by linarith
  have hy : (1 - 1/c^2) * t^2 ≤ t^2-1 := by
    have : 1 ≤ t^2/c^2 := by rw [le_div_iff₀ (by positivity)]; nlinarith
    have : t^2/c^2 = t^2 * (1/c^2) := by ring
    nlinarith
  have hy0 : 0 < (1 - 1/c^2) * t^2 := by positivity
  rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos (lt_of_lt_of_le hy0 hy) _)]
  have h1 := pcfLG_abs_eval_le P hd (by linarith : 1 ≤ t)
  have h2 : (t^2-1) ^ (-e) ≤ ((1 - 1/c^2) * t^2) ^ (-e) :=
    Real.rpow_le_rpow_of_nonpos hy0 hy (by linarith)
  have h3 : ((1 - 1/c^2) * t^2) ^ (-e) = (1 - 1/c^2) ^ (-e) * t ^ (-2*e) := by
    rw [Real.mul_rpow hc2.le (by positivity)]
    congr 1
    rw [← Real.rpow_natCast t 2, ← Real.rpow_mul ht0.le]
    push_cast; ring_nf
  have h4 : (t:ℝ) ^ d * t ^ (-2*e) = t ^ ((d:ℝ) - 2*e) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add ht0]; ring_nf
  calc |P.eval t| * (t^2-1) ^ (-e) ≤ (S * t^d) * (((1 - 1/c^2) * t^2) ^ (-e)) :=
        mul_le_mul h1 h2 (Real.rpow_pos_of_pos (lt_of_lt_of_le hy0 hy) _).le (by positivity)
    _ = S * (1 - 1/c^2) ^ (-e) * t ^ ((d:ℝ) - 2*e) := by rw [h3, ← h4]; ring

/-- Integrability of `|P(t)|(t²-1)^{-e}` on `(c,∞)`, `c > 1`, when `d - 2e < -1`. -/
lemma pcfLG_integrableOn_poly_rpow (P : Polynomial ℝ) {d : ℕ} (hd : P.natDegree ≤ d) {e c : ℝ}
    (he : 0 ≤ e) (hde : (d:ℝ) - 2*e < -1) (hc : 1 < c) :
    IntegrableOn (fun t => |P.eval t * (t^2-1) ^ (-e)|) (Ioi c) := by
  obtain ⟨K, hK, hb⟩ := pcfLG_poly_rpow_bound P hd he hc
  refine Integrable.mono' ((integrableOn_Ioi_rpow_of_lt hde (by linarith)).const_mul K) ?_
    (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_)
  · refine ContinuousOn.aestronglyMeasurable (fun t ht => ?_) measurableSet_Ioi
    have hy : 0 < t^2-1 := by have : c < t := ht; nlinarith
    exact ((P.continuous.continuousAt.mul ((continuousAt_id.pow 2).sub continuousAt_const |>.rpow_const
      (Or.inl hy.ne'))).abs).continuousWithinAt
  · rw [Real.norm_eq_abs, abs_abs]; exact hb t (le_of_lt ht)

/-- Tail bound for `|P(t)|(t²-1)^{-e}`: `∫_x^∞ ≤ K x^{d-2e+1}/(-(d-2e+1))` for `x ≥ c > 1`. -/
lemma pcfLG_tail_poly_rpow (P : Polynomial ℝ) {d : ℕ} (hd : P.natDegree ≤ d) {e c : ℝ}
    (he : 0 ≤ e) (hde : (d:ℝ) - 2*e < -1) (hc : 1 < c) : ∃ K, 0 ≤ K ∧ ∀ x, c ≤ x →
      ∫ t in Ioi x, |P.eval t * (t^2-1) ^ (-e)| ≤ K * x ^ ((d:ℝ) - 2*e + 1) := by
  obtain ⟨K, hK, hb⟩ := pcfLG_poly_rpow_bound P hd he hc
  refine ⟨K / (-((d:ℝ) - 2*e + 1)), div_nonneg hK (by linarith), fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  calc ∫ t in Ioi x, |P.eval t * (t^2-1) ^ (-e)| ≤ ∫ t in Ioi x, K * t ^ ((d:ℝ) - 2*e) := by
        refine setIntegral_mono_on ((pcfLG_integrableOn_poly_rpow P hd he hde hc).mono_set
          (Ioi_subset_Ioi hx)) ((integrableOn_Ioi_rpow_of_lt hde hx0).const_mul K)
          measurableSet_Ioi fun t ht => hb t (hx.trans (le_of_lt ht))
    _ = K / (-((d:ℝ) - 2*e + 1)) * x ^ ((d:ℝ) - 2*e + 1) := by
        rw [integral_const_mul, integral_Ioi_rpow_of_lt hde hx0]; field_simp

/-- The parity–degree class bounds the degree. -/
lemma pcfLG_good_natDegree {e D : ℕ} {f : Polynomial ℝ} (hf : pcfLG_good e D f) :
    f.natDegree ≤ D :=
  natDegree_le_iff_coeff_eq_zero.2 fun n hn => by
    by_contra h; have := (hf n h).2; exact absurd hn (not_lt.2 (by exact_mod_cast this))

/-- `deg u_s ≤ 3s`. -/
lemma pcfLG_natDegree_olverU (s : ℕ) : (pcfOlverU s).natDegree ≤ 3*s :=
  pcfLG_good_natDegree (pcfLG_olverPair_inv s).1

/-- `deg r_{s} ≤ 3s+2`, i.e. `deg (pcfOlverPair (s+1)).2 ≤ 3s+2`. -/
lemma pcfLG_natDegree_olverPair_snd (s : ℕ) : (pcfOlverPair (s+1)).2.natDegree ≤ 3*s+2 := by
  rw [pcfLG_olverPair_snd_succ]
  exact pcfLG_good_natDegree (pcfLG_r_good (pcfLG_olverPair_inv s).1 (pcfLG_olverPair_inv s).2)

/-- `P(t)/t^d → coeff_d P` when `deg P ≤ d`. -/
lemma pcfLG_tendsto_eval_div_pow (P : Polynomial ℝ) {d : ℕ} (hd : P.natDegree ≤ d) :
    Tendsto (fun t => P.eval t / t^d) atTop (𝓝 (P.coeff d)) := by
  have e : ∀ᶠ t in atTop, P.eval t / t^d =
      ∑ i ∈ Finset.range (d+1), P.coeff i * (if i = d then 1 else (t^(d-i))⁻¹) := by
    filter_upwards [eventually_gt_atTop 0] with t ht
    rw [eval_eq_sum_range' (Nat.lt_succ_of_le hd), Finset.sum_div]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    split_ifs with h
    · subst h; field_simp
    · have : t^d = t^i * t^(d-i) := by rw [← pow_add, Nat.add_sub_cancel' hi']
      rw [this]; field_simp
  refine Tendsto.congr' (EventuallyEq.symm e) ?_
  have : P.coeff d = ∑ i ∈ Finset.range (d+1), P.coeff i * (if i = d then 1 else 0) := by
    rw [Finset.sum_eq_single d]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; simp at h
  rw [this]
  refine tendsto_finsetSum _ fun i hi => (tendsto_const_nhds.mul ?_)
  split_ifs with h
  · exact tendsto_const_nhds
  · have hi' := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    exact (tendsto_pow_atTop (by omega : d - i ≠ 0)).inv_tendsto_atTop

/-- The limit `c_s = lim_{t→∞} A_s(t)`, the coefficient of `t^{3s}` in `u_s`. -/
def pcfLG_c (s : ℕ) : ℝ := (pcfOlverU s).coeff (3*s)

/-- `t²/(t²-1) → 1`. -/
lemma pcfLG_tendsto_sq_div : Tendsto (fun t : ℝ => t^2/(t^2-1)) atTop (𝓝 1) := by
  have h : Tendsto (fun t : ℝ => 1/(1 - (t^2)⁻¹)) atTop (𝓝 (1/(1-0))) :=
    tendsto_const_nhds.div (tendsto_const_nhds.sub
      ((tendsto_pow_atTop two_ne_zero).inv_tendsto_atTop)) (by norm_num)
  rw [show (1:ℝ)/(1-0) = 1 by norm_num] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 1] with t ht
  have : t^2 ≠ 0 := by positivity
  have : t^2 - 1 ≠ 0 := by nlinarith
  field_simp

/-- `A_s(t) → c_s` as `t → ∞`. -/
lemma pcfLG_tendsto_hatA (s : ℕ) : Tendsto (pcfLG_hatA s) atTop (𝓝 (pcfLG_c s)) := by
  have h1 := pcfLG_tendsto_eval_div_pow (pcfOlverU s) (pcfLG_natDegree_olverU s)
  have h2 : Tendsto (fun t : ℝ => (t^2/(t^2-1)) ^ (3*s/2:ℝ)) atTop (𝓝 1) := by
    have := pcfLG_tendsto_sq_div.rpow_const (p := 3*s/2) (Or.inl one_ne_zero)
    simpa using this
  have := h1.mul h2
  rw [mul_one] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 1] with t ht
  have hy : 0 < t^2-1 := by nlinarith
  have ht0 : 0 < t := by linarith
  rw [pcfLG_hatA, Real.div_rpow (by positivity) hy.le, Real.rpow_neg hy.le,
    show (t^2) ^ (3*(s:ℝ)/2) = t ^ (3*s) by
      rw [← Real.rpow_natCast t 2, ← Real.rpow_mul ht0.le, ← Real.rpow_natCast]; push_cast; ring_nf]
  have : t ^ (3*s) ≠ 0 := by positivity
  field_simp

/-- `A(t) → 0` as `t → ∞`. -/
lemma pcfLG_tendsto_A : Tendsto pcfLG_A atTop (𝓝 0) := by
  have h : Tendsto (fun t : ℝ => t^2-1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ (tendsto_pow_atTop two_ne_zero)
  have := (tendsto_rpow_neg_atTop (y := 1/4) (by norm_num)).comp h
  refine this.congr fun t => ?_
  simp [pcfLG_A, Function.comp]; ring_nf

/-- `√(t²-1)/t → 1`. -/
lemma pcfLG_tendsto_sqrt_div : Tendsto (fun t : ℝ => Real.sqrt (t^2-1) / t) atTop (𝓝 1) := by
  have h : Tendsto (fun t : ℝ => Real.sqrt (1 - (t^2)⁻¹)) atTop (𝓝 (Real.sqrt (1 - 0))) :=
    (tendsto_const_nhds.sub ((tendsto_pow_atTop two_ne_zero).inv_tendsto_atTop)).sqrt
  rw [sub_zero, Real.sqrt_one] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 1] with t ht
  have ht0 : 0 < t := by linarith
  rw [show 1 - (t^2)⁻¹ = (t^2-1)/t^2 by field_simp, Real.sqrt_div' _ (by positivity),
    Real.sqrt_sq ht0.le]

/-- The real normalizing constant `h(μ)` of DLMF 12.10.15. -/
def pcfLG_h (μ : ℝ) : ℝ := 2 ^ (-μ^2/4-1/4) * Real.exp (-μ^2/4) * μ ^ (μ^2/2-1/2)

/-- `h(μ) > 0`. -/
lemma pcfLG_h_pos {μ : ℝ} (hμ : 0 < μ) : 0 < pcfLG_h μ := by unfold pcfLG_h; positivity

/-- `pcfH μ` is the real number `h(μ)` for `μ > 0`. -/
lemma pcfLG_pcfH_eq {μ : ℝ} (hμ : 0 < μ) : pcfH μ = (pcfLG_h μ : ℂ) := by
  unfold pcfH pcfLG_h
  push_cast
  rw [Complex.ofReal_cpow (by norm_num), Complex.ofReal_cpow hμ.le]
  push_cast; ring_nf

/-- **The normalization at infinity**: `e^{z²/4} z^{a+1/2} A(t) e^{-μ²ξ(t)} → 1/h(μ)` as
`t → ∞`, where `z = μ t √2`, `a = -μ²/2`. -/
lemma pcfLG_tendsto_R {μ : ℝ} (hμ : 0 < μ) :
    Tendsto (fun t : ℝ => Real.exp ((μ*t*Real.sqrt 2)^2/4) * (μ*t*Real.sqrt 2) ^ (1/2-μ^2/2) *
      pcfLG_A t * Real.exp (-(μ^2 * pcfXi t))) atTop (𝓝 (pcfLG_h μ)⁻¹) := by
  set p : ℝ := 1/2-μ^2/2
  set C₀ : ℝ := p * Real.log μ + p/2 * Real.log 2 + μ^2/2 * Real.log 2
  set r : ℝ → ℝ := fun t => Real.sqrt (t^2-1)
  set E : ℝ → ℝ := fun t => μ^2/2 * (1 / (1 + r t / t)) + C₀ + 1/4 * Real.log (t^2/(t^2-1)) +
    μ^2/2 * Real.log ((1 + r t / t)/2)
  have hlim : Tendsto E atTop (𝓝 (μ^2/2 * (1/(1+1)) + C₀ + 1/4 * Real.log 1 +
      μ^2/2 * Real.log ((1+1)/2))) := by
    have hq := pcfLG_tendsto_sqrt_div
    refine ((((tendsto_const_nhds.mul (tendsto_const_nhds.div (tendsto_const_nhds.add hq)
      (by norm_num))).add tendsto_const_nhds).add (tendsto_const_nhds.mul
      (pcfLG_tendsto_sq_div.log one_ne_zero))).add (tendsto_const_nhds.mul
      (((tendsto_const_nhds.add hq).div_const 2).log (by norm_num))))
  have hval : μ^2/2 * (1/(1+1)) + C₀ + 1/4 * Real.log 1 + μ^2/2 * Real.log ((1+1)/2) =
      Real.log (pcfLG_h μ)⁻¹ := by
    rw [Real.log_inv, pcfLG_h, Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_rpow (by norm_num),
      Real.log_rpow hμ, Real.log_exp]
    simp only [C₀, p]; norm_num; ring
  rw [hval] at hlim
  have := (Real.continuous_exp.tendsto _).comp hlim
  rw [Real.exp_log (inv_pos.2 (pcfLG_h_pos hμ))] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 1] with t ht
  have ht0 : 0 < t := by linarith
  have hy : 0 < t^2-1 := by nlinarith
  have hr0 : 0 < r t := Real.sqrt_pos.2 hy
  have hr2 : r t ^ 2 = t^2-1 := Real.sq_sqrt hy.le
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hz : 0 < μ*t*Real.sqrt 2 := by positivity
  simp only [Function.comp, pcfLG_A]
  rw [Real.rpow_def_of_pos hz, Real.rpow_def_of_pos hy, ← Real.exp_add, ← Real.exp_add,
    ← Real.exp_add]
  congr 1
  simp only [E, C₀, pcfXi]
  have e1 : 1 / (1 + r t / t) = t^2 - t * r t := by
    field_simp
    nlinarith [hr2]
  have e2 : Real.log ((1 + r t / t)/2) = Real.log (t + r t) - Real.log 2 - Real.log t := by
    rw [show (1 + r t / t)/2 = (t + r t)/(2*t) by field_simp, Real.log_div (by positivity)
      (by positivity), Real.log_mul (by norm_num) ht0.ne']; ring
  have e3 : Real.log (t^2/(t^2-1)) = 2 * Real.log t - Real.log (t^2-1) := by
    rw [Real.log_div (by positivity) hy.ne', Real.log_pow]; push_cast; ring
  have e4 : Real.log (μ*t*Real.sqrt 2) = Real.log μ + Real.log t + 1/2 * Real.log 2 := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul hμ.ne' ht0.ne',
      Real.log_sqrt (by norm_num)]; ring
  rw [e1, e2, e3, e4]
  have : (μ*t*Real.sqrt 2)^2 = 2*μ^2*t^2 := by rw [mul_pow, mul_pow, hs2]; ring
  rw [this]
  simp only [r]
  ring

/-- The positive real axis tends to infinity inside every sector. -/
lemma pcfLG_tendsto_sector {α : ℝ} (hα : 0 ≤ α) {μ : ℝ} (hμ : 0 < μ) :
    Tendsto (fun t : ℝ => ((μ*t*Real.sqrt 2 : ℝ) : ℂ)) atTop (sector α) := by
  have hm : 0 < μ * Real.sqrt 2 := by positivity
  refine tendsto_inf.2 ⟨tendsto_comap_iff.2 ?_, tendsto_principal.2 ?_⟩
  · have : Tendsto (fun t : ℝ => μ * Real.sqrt 2 * t) atTop atTop :=
      tendsto_id.const_mul_atTop hm
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with t ht
    simp only [Function.comp, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_pos (by positivity)]; ring
  · filter_upwards [eventually_gt_atTop 0] with t ht
    have hx : 0 < μ*t*Real.sqrt 2 := by positivity
    refine ⟨by exact_mod_cast hx.ne', ?_⟩
    rw [Complex.arg_ofReal_of_nonneg hx.le, abs_zero]; exact hα

/-- **The normalization of `U` at infinity** (from DLMF 12.9.1): for fixed `μ > 0`,
`U(-μ²/2, μ t √2) / (A(t) e^{-μ² ξ(t)}) → h(μ)` as `t → ∞`. -/
lemma pcfLG_tendsto_U_div {μ : ℝ} (hμ : 0 < μ) :
    Tendsto (fun t : ℝ => pcfU (-μ^2/2) (μ*t*Real.sqrt 2) /
      ((pcfLG_A t * Real.exp (-(μ^2 * pcfXi t)) : ℝ) : ℂ)) atTop (𝓝 (pcfH μ)) := by
  set a : ℂ := -(μ:ℂ)^2/2
  have hO := pcfU_sector_asymptotic a (δ := π/4) (by positivity) (by linarith [Real.pi_pos]) 1
  have hz2 : Tendsto (fun z : ℂ => z ^ (-(2*(1:ℕ):ℤ))) (sector (3*π/4-π/4)) (𝓝 0) := by
    have : Tendsto (fun z : ℂ => ‖z‖) (sector (3*π/4-π/4)) atTop :=
      tendsto_comap.mono_left inf_le_left
    refine tendsto_zero_iff_norm_tendsto_zero.2 ?_
    have h2 := (tendsto_pow_atTop (two_ne_zero)).comp this |>.inv_tendsto_atTop
    refine h2.congr fun z => ?_
    simp
  have hE := (hO.trans_tendsto hz2).add_const 1
  simp only [zero_add, Finset.sum_range_one] at hE
  have hE' : Tendsto (fun z : ℂ => cexp (z^2/4) * z^(a+1/2) * pcfU a z) (sector (3*π/4-π/4))
      (𝓝 1) := by
    refine hE.congr fun z => ?_
    simp [pcfUTerm, poch_zero]
  have hT := hE'.comp (pcfLG_tendsto_sector (α := 3*π/4-π/4) (by linarith [Real.pi_pos]) hμ)
  have hR := (Complex.continuous_ofReal.tendsto _).comp (pcfLG_tendsto_R hμ)
  have hRne : ((pcfLG_h μ)⁻¹ : ℝ) ≠ 0 := inv_ne_zero (pcfLG_h_pos hμ).ne'
  have := hT.div hR (by exact_mod_cast hRne)
  rw [pcfLG_pcfH_eq hμ, show (pcfLG_h μ : ℂ) = 1 / (((pcfLG_h μ)⁻¹ : ℝ) : ℂ) by
    push_cast; field_simp]
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 1] with t ht
  have hx : 0 < μ*t*Real.sqrt 2 := by have : 0 < t := by linarith
                                      positivity
  have hcp : ((μ*t*Real.sqrt 2 : ℝ):ℂ)^(a+1/2) = (((μ*t*Real.sqrt 2)^(1/2-μ^2/2) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow hx.le]; congr 1; simp only [a]; push_cast; ring
  have hp : 0 < (μ*t*Real.sqrt 2)^(1/2-μ^2/2) := Real.rpow_pos_of_pos hx _
  have hA : 0 < pcfLG_A t * Real.exp (-(μ^2 * pcfXi t)) :=
    mul_pos (pcfLG_A_pos ht) (Real.exp_pos _)
  have hden : ((Real.exp ((μ*t*Real.sqrt 2)^2/4) * (μ*t*Real.sqrt 2)^(1/2-μ^2/2) * pcfLG_A t *
      Real.exp (-(μ^2 * pcfXi t)) : ℝ) : ℂ) = cexp (((μ*t*Real.sqrt 2 : ℝ) : ℂ)^2/4) *
      ((μ*t*Real.sqrt 2 : ℝ):ℂ)^(a+1/2) * ((pcfLG_A t * Real.exp (-(μ^2 * pcfXi t)) : ℝ) : ℂ) := by
    rw [hcp]; push_cast; ring
  have hp' : ((μ*t*Real.sqrt 2 : ℝ):ℂ)^(a+1/2) ≠ 0 := by rw [hcp]; exact_mod_cast hp.ne'
  have hA' : ((pcfLG_A t * Real.exp (-(μ^2 * pcfXi t)) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hA.ne'
  have he : cexp (((μ*t*Real.sqrt 2 : ℝ) : ℂ)^2/4) ≠ 0 := Complex.exp_ne_zero _
  simp only [Function.comp, Pi.div_apply]
  rw [hden, mul_div_mul_left _ _ (mul_ne_zero he hp')]
  push_cast; ring

/-- Continuity of `P(t) (t²-1)^c` on `(1, ∞)`. -/
lemma pcfLG_continuousOn_poly_rpow (P : Polynomial ℝ) (c : ℝ) :
    ContinuousOn (fun t => P.eval t * (t^2-1) ^ c) (Ioi 1) := fun _t ht =>
  ((pcfLG_hasDerivAt_poly_rpow P c ht).continuousAt).continuousWithinAt

/-- Continuity of `A''` on `(1, ∞)`. -/
lemma pcfLG_continuousOn_A2 : ContinuousOn pcfLG_A2 (Ioi 1) := by
  have := pcfLG_continuousOn_poly_rpow (C (3/4:ℝ) * X^2 + C (1/2:ℝ)) (-9/4)
  refine this.congr fun t _ => ?_
  simp only [pcfLG_A2, eval_add, eval_mul, eval_C, eval_pow, eval_X]; ring

/-- Continuity of `A_s''` on `(1, ∞)`. -/
lemma pcfLG_continuousOn_hatAd2 (s : ℕ) : ContinuousOn (pcfLG_hatAd2 s) (Ioi 1) := by
  have := pcfLG_continuousOn_poly_rpow
    (derivative (pcfOlverPair s).2 * (X^2 - 1) - C (3*(s:ℝ)+2) * X * (pcfOlverPair s).2)
    (-((3*s+4)/2))
  refine this.congr fun t _ => ?_
  simp [pcfLG_hatAd2]

/-- `A A'' = (3t²+2)/4 · (t²-1)^{-5/2}`. -/
lemma pcfLG_A_mul_A2 {t : ℝ} (ht : 1 < t) :
    pcfLG_A t * pcfLG_A2 t = (C (3/4:ℝ) * X^2 + C (1/2:ℝ)).eval t * (t^2-1) ^ (-(5/2):ℝ) := by
  have hy : 0 < t^2-1 := by nlinarith
  unfold pcfLG_A pcfLG_A2
  rw [show (t^2-1) ^ (-1/4:ℝ) * ((3*t^2+2)/4 * (t^2-1) ^ (-9/4:ℝ)) =
    (3*t^2+2)/4 * ((t^2-1) ^ (-1/4:ℝ) * (t^2-1) ^ (-9/4:ℝ)) by ring,
    pcfLG_rpow_mul hy (c := -(5/2)) (by norm_num)]
  simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X]; ring

/-- The error-control integrand `|A A''|` is integrable at infinity. -/
lemma pcfLG_integrableOn_V {c : ℝ} (hc : 1 < c) :
    IntegrableOn (fun t => |pcfLG_A t * pcfLG_A2 t - (fun _ => (0:ℝ)) t * pcfLG_A t ^ 2|) (Ioi c) := by
  have := pcfLG_integrableOn_poly_rpow (C (3/4:ℝ) * X^2 + C (1/2:ℝ)) (d := 2) (by compute_degree)
    (e := 5/2) (by norm_num) (by norm_num) hc
  refine this.congr_fun (fun t ht => ?_) measurableSet_Ioi
  have : 1 < t := hc.trans ht
  simp only [zero_mul, sub_zero, pcfLG_A_mul_A2 this]

/-- Tail bound for the error-control integral. -/
lemma pcfLG_tail_V {c : ℝ} (hc : 1 < c) : ∃ K, 0 ≤ K ∧ ∀ x, c ≤ x →
    ∫ t in Ioi x, |pcfLG_A t * pcfLG_A2 t - (fun _ => (0:ℝ)) t * pcfLG_A t ^ 2| ≤ K := by
  obtain ⟨K, hK, hb⟩ := pcfLG_tail_poly_rpow (C (3/4:ℝ) * X^2 + C (1/2:ℝ)) (d := 2)
    (by compute_degree) (e := 5/2) (by norm_num) (by norm_num) hc
  refine ⟨K, hK, fun x hx => ?_⟩
  have hx1 : 1 ≤ x := by linarith
  rw [setIntegral_congr_fun measurableSet_Ioi (g := fun t =>
    |(C (3/4:ℝ) * X^2 + C (1/2:ℝ)).eval t * (t^2-1) ^ (-(5/2):ℝ)|) (fun t ht => by
      have : 1 < t := lt_of_lt_of_le hc (hx.trans (le_of_lt ht))
      simp only [zero_mul, sub_zero, pcfLG_A_mul_A2 this])]
  refine (hb x hx).trans ?_
  have : x ^ ((2:ℕ) - 2*(5/2:ℝ) + 1) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hx1 (by norm_num)
  nlinarith

/-- Integrability of `|A_n'|` at infinity. -/
lemma pcfLG_integrableOn_hatAd (n : ℕ) {c : ℝ} (hc : 1 < c) :
    IntegrableOn (fun t => |pcfLG_hatAd n t|) (Ioi c) := by
  rcases n with _ | m
  · simp [pcfLG_hatAd, pcfOlverPair]
  · have := pcfLG_integrableOn_poly_rpow (pcfOlverPair (m+1)).2 (d := 3*m+2)
      (pcfLG_natDegree_olverPair_snd m) (e := (3*((m+1:ℕ):ℝ)+2)/2) (by positivity)
      (by push_cast; linarith) hc
    simpa [pcfLG_hatAd] using this

/-- Tail bound for `∫_x^∞ |A_n'|`: `≤ K x^{-2}` for `x ≥ c > 1`. -/
lemma pcfLG_tail_hatAd (n : ℕ) {c : ℝ} (hc : 1 < c) : ∃ K, 0 ≤ K ∧ ∀ x, c ≤ x →
    ∫ t in Ioi x, |pcfLG_hatAd n t| ≤ K * x ^ (-2:ℝ) := by
  rcases n with _ | m
  · exact ⟨0, le_rfl, fun x _ => by simp [pcfLG_hatAd, pcfOlverPair]⟩
  · obtain ⟨K, hK, hb⟩ := pcfLG_tail_poly_rpow (pcfOlverPair (m+1)).2 (d := 3*m+2)
      (pcfLG_natDegree_olverPair_snd m) (e := (3*((m+1:ℕ):ℝ)+2)/2) (by positivity)
      (by push_cast; linarith) hc
    refine ⟨K, hK, fun x hx => ?_⟩
    have := hb x hx
    rw [show ((3*m+2:ℕ):ℝ) - 2*((3*((m+1:ℕ):ℝ)+2)/2) + 1 = -2 by push_cast; ring] at this
    simpa [pcfLG_hatAd] using this

/-- `A_s` is bounded on `[c, ∞)`, `c > 1`. -/
lemma pcfLG_bound_hatA (s : ℕ) {c : ℝ} (hc : 1 < c) : ∃ K, 0 ≤ K ∧ ∀ t, c ≤ t →
    |pcfLG_hatA s t| ≤ K := by
  obtain ⟨K, hK, hb⟩ := pcfLG_poly_rpow_bound (pcfOlverU s) (pcfLG_natDegree_olverU s)
    (e := 3*s/2) (by positivity) hc
  refine ⟨K, hK, fun t ht => ?_⟩
  have := hb t ht
  rw [show ((3*s:ℕ):ℝ) - 2*(3*(s:ℝ)/2) = 0 by push_cast; ring, Real.rpow_zero, mul_one] at this
  exact this

/-- `A_0 = 1`. -/
lemma pcfLG_hatA_zero (t : ℝ) : pcfLG_hatA 0 t = 1 := by
  simp [pcfLG_hatA, pcfOlverU, pcfOlverPair]

/-- `c_0 = 1`. -/
lemma pcfLG_c_zero : pcfLG_c 0 = 1 := by
  simp [pcfLG_c, pcfOlverU, pcfOlverPair]

/-- `|c_s| ≤ K` whenever `|A_s| ≤ K` near infinity. -/
lemma pcfLG_abs_c_le {s : ℕ} {c K : ℝ} (hb : ∀ t, c ≤ t → |pcfLG_hatA s t| ≤ K) :
    |pcfLG_c s| ≤ K :=
  le_of_tendsto (pcfLG_tendsto_hatA s).abs (eventually_atTop.2 ⟨c, hb⟩)

/-- `ξ` is monotone on `(1, ∞)`. -/
lemma pcfLG_xi_mono {x t : ℝ} (hx : 1 < x) (hxt : x ≤ t) : pcfXi x ≤ pcfXi t := by
  have hm : MonotoneOn pcfXi (Ioi 1) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun t => Real.sqrt (t^2-1))
      (convex_Ioi 1) (fun t ht => (pcfLG_hasDerivAt_xi ht).continuousAt.continuousWithinAt)
      (fun t ht => ?_) (fun t _ => Real.sqrt_nonneg _)
    rw [interior_Ioi] at ht
    exact (pcfLG_hasDerivAt_xi ht).hasDerivWithinAt
  exact hm hx (lt_of_lt_of_le hx hxt) hxt

/-- `U(-μ²/2, μt√2)` as a function of `t`: first derivative. -/
lemma pcfLG_hasDerivAt_U (μ t : ℝ) :
    HasDerivAt (fun t : ℝ => pcfU (-μ^2/2) (μ*t*Real.sqrt 2))
      ((μ:ℂ) * Real.sqrt 2 * pcfUDeriv (-μ^2/2) (μ*t*Real.sqrt 2)) t := by
  have h1 : HasDerivAt (fun w : ℂ => (μ:ℂ) * w * Real.sqrt 2) ((μ:ℂ) * Real.sqrt 2) (t:ℂ) := by
    simpa using ((hasDerivAt_id (t:ℂ)).const_mul (μ:ℂ)).mul_const ((Real.sqrt 2 : ℝ) : ℂ)
  have := ((hasDerivAt_pcfU (-(μ:ℂ)^2/2) ((μ:ℂ) * t * Real.sqrt 2)).comp (t:ℂ) h1).comp_ofReal
  exact this.congr_deriv (by ring)

/-- `U(-μ²/2, μt√2)` as a function of `t`: Weber's equation `w'' = μ⁴(t²-1) w`. -/
lemma pcfLG_hasDerivAt_U' (μ t : ℝ) :
    HasDerivAt (fun t : ℝ => (μ:ℂ) * Real.sqrt 2 * pcfUDeriv (-μ^2/2) (μ*t*Real.sqrt 2))
      (((μ^4*(t^2-1) : ℝ) : ℂ) * pcfU (-μ^2/2) (μ*t*Real.sqrt 2)) t := by
  have h1 : HasDerivAt (fun w : ℂ => (μ:ℂ) * w * Real.sqrt 2) ((μ:ℂ) * Real.sqrt 2) (t:ℂ) := by
    simpa using ((hasDerivAt_id (t:ℂ)).const_mul (μ:ℂ)).mul_const ((Real.sqrt 2 : ℝ) : ℂ)
  have := (((hasDerivAt_pcfUDeriv (-(μ:ℂ)^2/2) ((μ:ℂ) * t * Real.sqrt 2)).comp (t:ℂ)
    h1).comp_ofReal).const_mul ((μ:ℂ) * Real.sqrt 2)
  have hs2 : ((Real.sqrt 2 : ℝ) : ℂ)^2 = 2 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  refine this.congr_deriv ?_
  push_cast
  linear_combination (((μ:ℂ)^4*(t:ℂ)^2/4) * (((Real.sqrt 2 : ℝ) : ℂ)^2 + 2) - (μ:ℂ)^4/2) *
    pcfU (-(μ:ℂ)^2/2) ((μ:ℂ) * t * Real.sqrt 2) * hs2

/-- The truncated Olver series `∑_{s<N} A_s(t)/u^s`. -/
def pcfLG_ser (N : ℕ) (u t : ℝ) : ℝ := ∑ s ∈ Finset.range N, pcfLG_hatA s t / u^s
/-- Its value at `t = ∞`: `∑_{s<N} c_s/u^s`. -/
def pcfLG_S (N : ℕ) (u : ℝ) : ℝ := ∑ s ∈ Finset.range N, pcfLG_c s / u^s

/-- The Liouville–Green series with coefficients `(-1)^s A_s` is the Olver series. -/
lemma pcfLG_lgSeries_eq (N : ℕ) (u t : ℝ) :
    LiouvilleGreen.lgSeries u (fun s t => (-1)^s * pcfLG_hatA s t) N t = pcfLG_ser N u t := by
  unfold LiouvilleGreen.lgSeries pcfLG_ser
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← mul_assoc, ← mul_pow]; norm_num

/-- A truncated series with leading term `1` and bounded higher coefficients is within
`K/u` of `1`. -/
lemma pcfLG_abs_sum_sub_one_le {N : ℕ} (hN : 1 ≤ N) {f : ℕ → ℝ} (hf0 : f 0 = 1) {K : ℕ → ℝ}
    (hK : ∀ s, |f s| ≤ K s) {u : ℝ} (hu : 1 ≤ u) :
    |∑ s ∈ Finset.range N, f s / u^s - 1| ≤ (∑ s ∈ Finset.range N, K s) / u := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  have hu0 : 0 < u := by linarith
  rw [Finset.sum_range_succ', hf0, pow_zero, div_one, add_sub_cancel_right,
    Finset.sum_range_succ', add_div]
  have hK0 : 0 ≤ K 0 := (abs_nonneg _).trans (hK 0)
  have : |∑ s ∈ Finset.range M, f (s+1) / u^(s+1)| ≤ (∑ s ∈ Finset.range M, K (s+1)) / u := by
    rw [Finset.sum_div]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun s _ => ?_)
    rw [abs_div, abs_pow, abs_of_pos hu0]
    have h1 : u ≤ u^(s+1) := by
      calc u = u^1 := (pow_one u).symm
        _ ≤ u^(s+1) := pow_le_pow_right₀ hu (by omega)
    calc |f (s+1)| / u^(s+1) ≤ K (s+1) / u^(s+1) := by gcongr; exact hK _
      _ ≤ K (s+1) / u := by
        have := (abs_nonneg _).trans (hK (s+1))
        exact div_le_div_of_nonneg_left this hu0 h1
  have : 0 ≤ K 0 / u := by positivity
  linarith

/-- **Core estimate for DLMF 12.10.3.** For `t ≥ 1+δ` and `μ` large,
`U(-μ²/2, μt√2) S_N(μ²)/(h(μ) A(t) e^{-μ²ξ(t)}) = ∑_{s<N} A_s(t) μ^{-2s} + O(μ^{-2N})`. -/
lemma pcfLG_core {δ : ℝ} (hδ : 0 < δ) {N : ℕ} (hN : 1 ≤ N) : ∃ C μ₀ : ℝ, 1 ≤ μ₀ ∧ 0 ≤ C ∧
    ∀ μ, μ₀ ≤ μ → |pcfLG_S N (μ^2) - 1| ≤ 1/2 ∧ ∀ t, 1 + δ ≤ t →
      ‖pcfU (-μ^2/2) (μ*t*Real.sqrt 2) * (pcfLG_S N (μ^2) : ℂ) /
        (pcfH μ * ((pcfLG_A t * Real.exp (-(μ^2 * pcfXi t)) : ℝ) : ℂ)) -
          (pcfLG_ser N (μ^2) t : ℂ)‖ ≤ C / (μ^2)^N ∧ |pcfLG_ser N (μ^2) t| ≤ 3/2 := by
  set c : ℝ := 1 + δ/2 with hcdef
  have hc : 1 < c := by linarith
  choose KA hKA0 hKA using fun s => pcfLG_bound_hatA s hc
  set KS := ∑ s ∈ Finset.range N, KA s
  have hKS : 0 ≤ KS := Finset.sum_nonneg fun s _ => hKA0 s
  obtain ⟨I, hI0, hI⟩ := pcfLG_tail_hatAd N hc
  obtain ⟨V0, hV00, hV⟩ := pcfLG_tail_V hc
  set Cε := I * Real.exp (V0/2)
  have hCε : 0 ≤ Cε := by positivity
  refine ⟨Cε, max 1 (2*(KS+Cε)+1), le_max_left _ _, hCε, fun μ hμ => ?_⟩
  have hμ1 : 1 ≤ μ := (le_max_left _ _).trans hμ
  have hμ0 : 0 < μ := by linarith
  set u := μ^2 with hu
  have hu1 : 1 ≤ u := by nlinarith
  have hu0 : 0 < u := by linarith
  have huK : 2*(KS+Cε) ≤ u := by nlinarith [le_max_right 1 (2*(KS+Cε)+1)]
  have hsmall : (KS + Cε)/u ≤ 1/2 := by rw [div_le_iff₀ hu0]; linarith
  -- bounds on the series and on `S`
  have hser : ∀ t, c ≤ t → |pcfLG_ser N u t - 1| ≤ KS/u := fun t ht =>
    pcfLG_abs_sum_sub_one_le hN (pcfLG_hatA_zero t) (fun s => hKA s t ht) hu1
  have hS : |pcfLG_S N u - 1| ≤ KS/u :=
    pcfLG_abs_sum_sub_one_le hN pcfLG_c_zero (fun s => pcfLG_abs_c_le (hKA s)) hu1
  have hKSu : KS/u ≤ 1/2 := le_trans (div_le_div_of_nonneg_right (by linarith) hu0.le) hsmall
  refine ⟨hS.trans hKSu, ?_⟩
  -- the Liouville–Green solution
  obtain ⟨ε, ε', w', H⟩ := LiouvilleGreen.exists_solution_expansion_exp (a := 1) hu0
    (A := pcfLG_A) (A' := pcfLG_A1) (A'' := pcfLG_A2) (ξ := pcfXi) (g := fun _ => 0)
    (fun x hx => (pcfLG_A_pos hx).ne') (fun x hx => pcfLG_hasDerivAt_A hx)
    (fun x hx => pcfLG_hasDerivAt_A1 hx) pcfLG_continuousOn_A2 continuousOn_const
    (fun x hx => by rw [pcfLG_A_sq_recip hx]; exact pcfLG_hasDerivAt_xi hx)
    (fun c' hc' => pcfLG_integrableOn_V hc') (n := N)
    (As := fun s t => (-1)^s * pcfLG_hatA s t) (Ad := fun s t => (-1)^s * pcfLG_hatAd s t)
    (Ad2 := fun s t => (-1)^s * pcfLG_hatAd2 s t)
    (fun s _ x hx => (pcfLG_hasDerivAt_hatA s hx).const_mul _)
    (fun s _ x hx => (pcfLG_hasDerivAt_hatAd s hx).const_mul _)
    (fun s _ => continuousOn_const.mul (pcfLG_continuousOn_hatAd2 s))
    (fun x _ => by simp [pcfLG_hatAd, pcfOlverPair])
    (fun s _ x hx => by
      have := pcfLG_recursion s hx
      simp only [zero_mul, sub_zero]
      rw [pow_succ]
      linear_combination (-1:ℝ)^s * this)
    (fun c' hc' => by simpa [abs_mul] using pcfLG_integrableOn_hatAd N hc')
  simp only [pcfLG_lgSeries_eq] at H
  -- the error bound on `[c, ∞)`
  have hεb : ∀ t, c ≤ t → |ε t| ≤ Cε * t ^ (-2:ℝ) / u^N := by
    intro t ht
    have ht1 : 1 < t := lt_of_lt_of_le hc ht
    have h4 := (H t ht1).2.2.2.1
    simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, zero_mul, sub_zero] at h4
    have hV' := hV t ht
    simp only [zero_mul, sub_zero, abs_mul] at hV'
    refine h4.trans ?_
    have e1 : Real.exp ((∫ x in Ioi t, |pcfLG_A x| * |pcfLG_A2 x|) / (2*u)) ≤ Real.exp (V0/2) := by
      refine Real.exp_le_exp.2 ?_
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      have : 0 ≤ ∫ x in Ioi t, |pcfLG_A x| * |pcfLG_A2 x| :=
        setIntegral_nonneg measurableSet_Ioi fun _ _ => by positivity
      nlinarith
    have e2 := hI t ht
    have hnn : 0 ≤ ∫ x in Ioi t, |pcfLG_hatAd N x| :=
      setIntegral_nonneg measurableSet_Ioi fun _ _ => abs_nonneg _
    calc (∫ x in Ioi t, |pcfLG_hatAd N x|) / u^N *
          Real.exp ((∫ x in Ioi t, |pcfLG_A x| * |pcfLG_A2 x|) / (2*u))
        ≤ (I * t ^ (-2:ℝ)) / u^N * Real.exp (V0/2) := by
          gcongr
      _ = Cε * t ^ (-2:ℝ) / u^N := by simp only [Cε]; ring
  have hεb' : ∀ t, c ≤ t → |ε t| ≤ Cε / u := by
    intro t ht
    have ht1 : 1 ≤ t := by linarith
    have h1 : t ^ (-2:ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos ht1 (by norm_num)
    have h2 : u ≤ u^N := by
      calc u = u^1 := (pow_one u).symm
        _ ≤ u^N := pow_le_pow_right₀ hu1 hN
    refine (hεb t ht).trans ?_
    calc Cε * t ^ (-2:ℝ) / u^N ≤ Cε * 1 / u^N := by gcongr
      _ ≤ Cε / u := by rw [mul_one]; exact div_le_div_of_nonneg_left hCε hu0 h2
  have hsum : ∀ t, c ≤ t → |pcfLG_ser N u t + ε t - 1| ≤ 1/2 := by
    intro t ht
    have := hser t ht; have := hεb' t ht
    have : |pcfLG_ser N u t + ε t - 1| ≤ |pcfLG_ser N u t - 1| + |ε t| := by
      rw [show pcfLG_ser N u t + ε t - 1 = (pcfLG_ser N u t - 1) + ε t by ring]
      exact abs_add_le _ _
    have : KS/u + Cε/u ≤ 1/2 := by rw [← add_div]; exact hsmall
    linarith
  have hpos : ∀ t, c ≤ t → 1/2 ≤ pcfLG_ser N u t + ε t := fun t ht => by
    have := abs_le.1 (hsum t ht); linarith [this.1]
  set W : ℝ → ℝ := fun t => pcfLG_A t * Real.exp (-(u * pcfXi t)) * (pcfLG_ser N u t + ε t)
    with hWdef
  set q : ℝ → ℝ := fun t => u^2 * (pcfLG_A t ^ 4)⁻¹ + (fun _ => (0:ℝ)) t with hq
  have hAe : ∀ t, 1 < t → 0 < pcfLG_A t * Real.exp (-(u * pcfXi t)) := fun t ht =>
    mul_pos (pcfLG_A_pos ht) (Real.exp_pos _)
  have hS0 : pcfLG_S N u ≠ 0 := by
    have := abs_le.1 (hS.trans hKSu); intro h; rw [h] at this; linarith [this.1]
  -- `W → 0`
  have hWl : Tendsto W atTop (𝓝 0) := by
    have hb : Tendsto (fun t => (3/2 * Real.exp (-(u * pcfXi c))) * pcfLG_A t) atTop (𝓝 0) := by
      simpa using pcfLG_tendsto_A.const_mul (3/2 * Real.exp (-(u * pcfXi c)))
    refine squeeze_zero' ?_ ?_ hb
    · filter_upwards [eventually_ge_atTop c] with t ht
      have ht1 : 1 < t := lt_of_lt_of_le hc ht
      exact (mul_pos (hAe t ht1) (by linarith [hpos t ht])).le
    · filter_upwards [eventually_ge_atTop c] with t ht
      have ht1 : 1 < t := lt_of_lt_of_le hc ht
      have h1 : Real.exp (-(u * pcfXi t)) ≤ Real.exp (-(u * pcfXi c)) :=
        Real.exp_le_exp.2 (by nlinarith [pcfLG_xi_mono hc ht])
      have h2 : pcfLG_ser N u t + ε t ≤ 3/2 := by
        have := abs_le.1 (hsum t ht); linarith [this.2]
      have hA := (pcfLG_A_pos ht1).le
      simp only [hWdef]
      calc pcfLG_A t * Real.exp (-(u * pcfXi t)) * (pcfLG_ser N u t + ε t)
          ≤ pcfLG_A t * Real.exp (-(u * pcfXi c)) * (3/2) := by
            gcongr
            linarith [hpos t ht]
        _ = 3/2 * Real.exp (-(u * pcfXi c)) * pcfLG_A t := by ring
  -- `ε → 0` and the limit of the series
  have hεl : Tendsto ε atTop (𝓝 0) := by
    have hb : Tendsto (fun t : ℝ => Cε * t ^ (-2:ℝ) / u^N) atTop (𝓝 0) := by
      simpa using ((tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 2)).const_mul Cε).div_const
        (u^N)
    refine squeeze_zero_norm' ?_ hb
    filter_upwards [eventually_ge_atTop c] with t ht
    rw [Real.norm_eq_abs]; exact hεb t ht
  have hserl : Tendsto (fun t => pcfLG_ser N u t) atTop (𝓝 (pcfLG_S N u)) :=
    tendsto_finsetSum _ fun s _ => (pcfLG_tendsto_hatA s).div_const _
  have hsl : Tendsto (fun t => ((pcfLG_ser N u t + ε t : ℝ) : ℂ)) atTop (𝓝 (pcfLG_S N u : ℂ)) := by
    have := (hserl.add hεl); rw [add_zero] at this
    exact (Complex.continuous_ofReal.tendsto _).comp this
  have hUl := pcfLG_tendsto_U_div hμ0
  have hS0' : (pcfLG_S N u : ℂ) ≠ 0 := by exact_mod_cast hS0
  have hl : Tendsto (fun t : ℝ => pcfU (-μ^2/2) (μ*t*Real.sqrt 2) / (W t : ℂ)) atTop
      (𝓝 (pcfH μ / pcfLG_S N u)) := by
    refine (hUl.div hsl hS0').congr' ?_
    filter_upwards [eventually_gt_atTop 1] with t ht
    simp only [Pi.div_apply, hWdef, hu]
    push_cast
    rw [div_div]
  -- identification with `U`
  obtain ⟨κ, hκ⟩ := pcfLG_eq_mul_of_tendsto (b := c) (q := q)
    (U := fun t => pcfU (-μ^2/2) (μ*t*Real.sqrt 2))
    (U' := fun t => (μ:ℂ) * Real.sqrt 2 * pcfUDeriv (-μ^2/2) (μ*t*Real.sqrt 2)) (W := W) (W' := w')
    (fun t _ => pcfLG_hasDerivAt_U μ t)
    (fun t ht => by
      have h1 : 1 < t := lt_trans hc ht
      have := pcfLG_hasDerivAt_U' μ t
      refine this.congr_deriv ?_
      congr 2
      simp only [hq, pcfLG_A_pow_four_recip h1, hu]; ring)
    (fun t ht => (H t (lt_trans hc ht)).2.1)
    (fun t ht => (H t (lt_trans hc ht)).2.2.1)
    (fun t ht => (mul_pos (hAe t (lt_trans hc ht)) (by linarith [hpos t ht.le])).ne') hWl hl
  -- the constant
  have hκS : κ * pcfLG_S N u = pcfH μ := by
    refine tendsto_nhds_unique ((hsl.const_mul κ).congr' ?_) hUl
    filter_upwards [eventually_gt_atTop c] with t ht
    have ht1 : 1 < t := lt_trans hc ht
    have hne : ((pcfLG_A t * Real.exp (-(u * pcfXi t)) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (hAe t ht1).ne'
    rw [hκ t ht]
    have hA0 : (pcfLG_A t : ℂ) ≠ 0 := by exact_mod_cast (pcfLG_A_pos ht1).ne'
    simp only [hWdef, hu]
    push_cast
    field_simp
  have hh0 : pcfH μ ≠ 0 := by rw [pcfLG_pcfH_eq hμ0]; exact_mod_cast (pcfLG_h_pos hμ0).ne'
  intro t ht
  have htc : c < t := by linarith
  have ht1 : 1 < t := lt_trans hc htc
  have hne : ((pcfLG_A t * Real.exp (-(u * pcfXi t)) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (hAe t ht1).ne'
  refine ⟨?_, ?_⟩
  · have heq : pcfU (-μ^2/2) (μ*t*Real.sqrt 2) * (pcfLG_S N u : ℂ) /
        (pcfH μ * ((pcfLG_A t * Real.exp (-(u * pcfXi t)) : ℝ) : ℂ)) - (pcfLG_ser N u t : ℂ) =
        (ε t : ℂ) := by
      rw [hκ t htc, ← hκS]
      have hA0 : (pcfLG_A t : ℂ) ≠ 0 := by exact_mod_cast (pcfLG_A_pos ht1).ne'
      simp only [hWdef, hu]
      push_cast
      have hκ0 : κ ≠ 0 := by rintro rfl; rw [zero_mul] at hκS; exact hh0 hκS.symm
      have hS1 : ((pcfLG_S N (μ^2) : ℝ) : ℂ) ≠ 0 := hS0'
      field_simp
      ring
    rw [heq, Complex.norm_real, Real.norm_eq_abs]
    refine (hεb t (by linarith)).trans ?_
    have h1 : t ^ (-2:ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
    have : Cε * t ^ (-2:ℝ) ≤ Cε := by nlinarith [Real.rpow_nonneg (by linarith : (0:ℝ) ≤ t) (-2:ℝ)]
    exact div_le_div_of_nonneg_right this (by positivity)
  · have := abs_le.1 ((hser t (by linarith)).trans hKSu)
    rw [abs_le]; constructor <;> linarith [this.1, this.2]

/-- Eventual statements for the uniform filter. -/
lemma pcfLG_eventually_uniform {S : Set ℝ} {P : ℝ × ℝ → Prop} (μ₀ : ℝ)
    (h : ∀ μ, μ₀ ≤ μ → ∀ t ∈ S, P (μ, t)) : ∀ᶠ p in pcfUniformFilter S, P p := by
  unfold pcfUniformFilter
  rw [eventually_inf_principal]
  filter_upwards [(eventually_ge_atTop μ₀).comap Prod.fst] with p hp hpS
  exact h p.1 hp p.2 hpS

/-- The complex denominator of DLMF 12.10.3 is real. -/
lemma pcfLG_denom_eq {μ t : ℝ} (ht : 1 < t) (G : ℂ) :
    G * cexp (-(μ:ℂ)^2 * (pcfXi t : ℂ)) / ((t:ℂ)^2-1)^(1/4:ℂ) =
      G * ((pcfLG_A t * Real.exp (-(μ^2 * pcfXi t)) : ℝ) : ℂ) := by
  have hy : 0 < t^2-1 := by nlinarith
  have e1 : ((t:ℂ)^2-1)^(1/4:ℂ) = (((t^2-1) ^ (1/4:ℝ) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow hy.le]; push_cast; rfl
  have hp : 0 < (t^2-1) ^ (1/4:ℝ) := Real.rpow_pos_of_pos hy _
  rw [e1, pcfLG_A, show (-1/4:ℝ) = -(1/4) by norm_num, Real.rpow_neg hy.le]
  have hp' : (((t^2-1) ^ (1/4:ℝ) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  push_cast
  field_simp

/-- `pcfOlverA` is the real coefficient `A_s` for `t > 1`. -/
lemma pcfLG_olverA_eq (s : ℕ) {t : ℝ} (ht : 1 < t) : pcfOlverA s t = (pcfLG_hatA s t : ℂ) := by
  have hy : 0 < t^2-1 := by nlinarith
  have e1 : ((t:ℂ)^2-1)^(3*(s:ℂ)/2) = (((t^2-1) ^ (3*(s:ℝ)/2) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow hy.le]; push_cast; rfl
  rw [pcfOlverA, e1, pcfLG_hatA, Real.rpow_neg hy.le]
  push_cast
  rw [div_eq_mul_inv]

/-- The series of `pcfOlverA` is the real series `pcfLG_ser`. -/
lemma pcfLG_sum_olverA_eq (N : ℕ) (μ : ℝ) {t : ℝ} (ht : 1 < t) :
    ∑ s ∈ Finset.range N, pcfOlverA s t / (μ:ℂ)^(2*s) = (pcfLG_ser N (μ^2) t : ℂ) := by
  rw [pcfLG_ser]; push_cast
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [pcfLG_olverA_eq s ht, pow_mul]

/-- The complex series `∑ c_s μ^{-2s}` is real. -/
lemma pcfLG_sum_c_eq (N : ℕ) (μ : ℝ) :
    ∑ s ∈ Finset.range N, (pcfLG_c s : ℂ) / (μ:ℂ)^(2*s) = (pcfLG_S N (μ^2) : ℂ) := by
  rw [pcfLG_S]; push_cast
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [pow_mul]

/-- `‖μ^{-2N}‖ = (μ²)^{-N}` for `μ > 0`. -/
lemma pcfLG_norm_zpow {μ : ℝ} (hμ : 0 < μ) (N : ℕ) :
    ‖(μ:ℂ)^(-(2*N:ℤ))‖ = ((μ^2)^N)⁻¹ := by
  rw [norm_zpow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hμ, zpow_neg,
    show (2*N:ℤ) = ((2*N:ℕ):ℤ) by push_cast; ring, zpow_natCast, pow_mul]

/-- The Borel sum of the coefficients `c_s`, composed with `u = μ²`. -/
lemma pcfLG_borel_bound {Φ : ℝ → ℝ} (hΦ : ∀ N : ℕ,
    (fun u : ℝ => Φ u - ∑ s ∈ Finset.range N, pcfLG_c s / u^s) =O[atTop] (fun u : ℝ => (u^N)⁻¹))
    (N : ℕ) : ∃ B μ₁ : ℝ, 0 ≤ B ∧ 1 ≤ μ₁ ∧ ∀ μ, μ₁ ≤ μ →
      |Φ (μ^2) - pcfLG_S N (μ^2)| ≤ B / (μ^2)^N := by
  obtain ⟨B, hB⟩ := (hΦ N).bound
  obtain ⟨u₁, hu₁⟩ := eventually_atTop.1 (hB.and (eventually_ge_atTop (1:ℝ)))
  refine ⟨max B 0, max 1 u₁, le_max_right _ _, le_max_left _ _, fun μ hμ => ?_⟩
  have hμ1 : 1 ≤ μ := (le_max_left _ _).trans hμ
  have hμu : u₁ ≤ μ^2 := by nlinarith [le_max_right 1 u₁]
  obtain ⟨h1, h2⟩ := hu₁ (μ^2) hμu
  have hpos : 0 < (μ^2)^N := by positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_inv, abs_of_pos hpos] at h1
  rw [pcfLG_S]
  calc _ ≤ B * ((μ^2)^N)⁻¹ := h1
    _ ≤ max B 0 * ((μ^2)^N)⁻¹ := by gcongr; exact le_max_left _ _
    _ = max B 0 / (μ^2)^N := by rw [div_eq_mul_inv]

/-- **DLMF 12.10.3 with an explicit normalizer** (Olver's uniform expansion of `U` for
`t > 1`). There is a function `g` with
`U(-½μ², μt√2) ∼ g(μ) e^{-μ²ξ(t)} (t²-1)^{-1/4} ∑ A_s(t)/μ^{2s}` as `μ → ∞`, uniformly for
`t ≥ 1+δ`; moreover `g(μ)/h(μ) · ∑_{s<N} c_s μ^{-2s} = 1 + O(μ^{-2N})`, where `h` is DLMF 12.10.15
and `c_s = lim_{t→∞} A_s(t)` is the coefficient of `t^{3s}` in `u_s`. Identifying
`(∑ c_s u^{-s})^{-1}` with `1 + ½∑ γ_s (u/2)^{-s}` would give DLMF 12.10.14. Proof: the
Liouville–Green expansion with error bounds (Olver, Ch. 10, Thm. 3.1) for
`w'' = μ⁴(t²-1)w`, identified with `U` as the recessive solution at `+∞` via DLMF 12.9.1. -/
@[dlmf 12.10.E3]
theorem pcf_negative_parameter_uniform_U :
    ∃ g : ℝ → ℂ, (∀ N : ℕ, (fun μ : ℝ => g μ / pcfH μ *
        (∑ s ∈ Finset.range N, (pcfLG_c s : ℂ) / (μ:ℂ)^(2*s)) - 1) =O[atTop]
        (fun μ : ℝ => (μ:ℂ)^(-(2*N:ℤ)))) ∧
      ∀ δ : ℝ, 0 < δ → HasCylinderUniformExpansion
        (fun μ t => pcfU (-μ^2/2) (μ*t*Real.sqrt 2)/(g μ*exp (-μ^2*pcfXi t)/(t^2-1:ℂ)^(1/4:ℂ)))
        (fun s t => pcfOlverA s t) (Ici (1+δ)) := by
  obtain ⟨Φ, hΦ⟩ := pcfLG_exists_asymptotic pcfLG_c
  -- `Φ(μ²)` stays near `1`
  have hΦ1 : ∃ μ₁ : ℝ, 1 ≤ μ₁ ∧ ∀ μ, μ₁ ≤ μ → 1/2 ≤ Φ (μ^2) ∧ Φ (μ^2) ≤ 2 := by
    obtain ⟨B, μ₁, hB, hμ₁, hb⟩ := pcfLG_borel_bound hΦ 1
    refine ⟨max μ₁ (2*B+1), le_trans hμ₁ (le_max_left _ _), fun μ hμ => ?_⟩
    have hμ1 : μ₁ ≤ μ := (le_max_left _ _).trans hμ
    have h := hb μ hμ1
    have hS : pcfLG_S 1 (μ^2) = 1 := by simp [pcfLG_S, pcfLG_c_zero]
    rw [hS, pow_one] at h
    have hμB : 2*B+1 ≤ μ := (le_max_right _ _).trans hμ
    have hμ2 : 2*B ≤ μ^2 := by nlinarith
    have : B / μ^2 ≤ 1/2 := by rw [div_le_iff₀ (by nlinarith)]; linarith
    have := abs_le.1 (h.trans this)
    constructor <;> linarith [this.1, this.2]
  obtain ⟨μ₁, hμ₁, hΦb⟩ := hΦ1
  refine ⟨fun μ => pcfH μ / (Φ (μ^2) : ℂ), fun N => ?_, fun δ hδ => ?_⟩
  · -- the normalizer
    obtain ⟨B, μ₂, hB, hμ₂, hb⟩ := pcfLG_borel_bound hΦ N
    refine IsBigO.of_bound (2*B) ?_
    filter_upwards [eventually_ge_atTop (max μ₁ μ₂)] with μ hμ
    have hμ0 : 0 < μ := by linarith [le_max_left μ₁ μ₂]
    obtain ⟨hΦl, -⟩ := hΦb μ ((le_max_left _ _).trans hμ)
    have hh0 : pcfH μ ≠ 0 := by rw [pcfLG_pcfH_eq hμ0]; exact_mod_cast (pcfLG_h_pos hμ0).ne'
    have hΦ0 : (Φ (μ^2) : ℂ) ≠ 0 := by exact_mod_cast (by linarith : (0:ℝ) < Φ (μ^2)).ne'
    rw [pcfLG_sum_c_eq, pcfLG_norm_zpow hμ0]
    have heq : pcfH μ / (Φ (μ^2) : ℂ) / pcfH μ * (pcfLG_S N (μ^2) : ℂ) - 1 =
        (((pcfLG_S N (μ^2) - Φ (μ^2)) / Φ (μ^2) : ℝ) : ℂ) := by
      push_cast; field_simp
    rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos (show (0:ℝ) < Φ (μ^2) by linarith),
      abs_sub_comm]
    have := hb μ ((le_max_right _ _).trans hμ)
    rw [div_le_iff₀ (by linarith)]
    calc |Φ (μ^2) - pcfLG_S N (μ^2)| ≤ B / (μ^2)^N := this
      _ = 2*B * ((μ^2)^N)⁻¹ * (1/2) := by ring
      _ ≤ 2*B * ((μ^2)^N)⁻¹ * Φ (μ^2) := by gcongr
  · -- the expansion
    have key : ∀ N : ℕ, 1 ≤ N → (fun p : ℝ × ℝ => pcfU (-p.1^2/2) (p.1*p.2*Real.sqrt 2) /
        (pcfH p.1 / (Φ (p.1^2) : ℂ) * exp (-p.1^2*pcfXi p.2) / (p.2^2-1:ℂ)^(1/4:ℂ)) -
        ∑ s ∈ Finset.range N, pcfOlverA s p.2 / (p.1:ℂ)^(2*s)) =O[pcfUniformFilter (Ici (1+δ))]
        (fun p : ℝ × ℝ => (p.1:ℂ)^(-(2*N:ℤ))) := by
      intro N hN
      obtain ⟨C, μ₀, hμ₀, hC, hcore⟩ := pcfLG_core hδ hN
      obtain ⟨B, μ₂, hB, hμ₂, hb⟩ := pcfLG_borel_bound hΦ N
      refine IsBigO.of_bound (4*C + 3*B) (pcfLG_eventually_uniform (max μ₀ (max μ₁ μ₂))
        fun μ hμ t ht => ?_)
      have hμ0 : 0 < μ := by linarith [le_max_left μ₀ (max μ₁ μ₂)]
      have ht1 : 1 < t := by have : 1 + δ ≤ t := ht; linarith
      obtain ⟨hS, hct⟩ := hcore μ ((le_max_left _ _).trans hμ)
      obtain ⟨hX, hser⟩ := hct t ht
      obtain ⟨hΦl, hΦu⟩ := hΦb μ ((le_max_left _ _).trans ((le_max_right _ _).trans hμ))
      have hbo := hb μ ((le_max_right _ _).trans ((le_max_right _ _).trans hμ))
      have hh0 : pcfH μ ≠ 0 := by rw [pcfLG_pcfH_eq hμ0]; exact_mod_cast (pcfLG_h_pos hμ0).ne'
      have hSpos : 1/2 ≤ pcfLG_S N (μ^2) := by linarith [(abs_le.1 hS).1]
      have hS0 : (pcfLG_S N (μ^2) : ℂ) ≠ 0 := by exact_mod_cast (by linarith : (0:ℝ) < _).ne'
      have hΦ0 : (Φ (μ^2) : ℂ) ≠ 0 := by exact_mod_cast (by linarith : (0:ℝ) < Φ (μ^2)).ne'
      have hAe : ((pcfLG_A t * Real.exp (-(μ^2 * pcfXi t)) : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast (mul_pos (pcfLG_A_pos ht1) (Real.exp_pos _)).ne'
      simp only
      rw [pcfLG_denom_eq ht1, pcfLG_sum_olverA_eq N μ ht1, pcfLG_norm_zpow hμ0]
      set X := pcfU (-μ^2/2) (μ*t*Real.sqrt 2) * (pcfLG_S N (μ^2) : ℂ) /
        (pcfH μ * ((pcfLG_A t * Real.exp (-(μ^2 * pcfXi t)) : ℝ) : ℂ)) with hXdef
      have hF : pcfU (-μ^2/2) (μ*t*Real.sqrt 2) / (pcfH μ / (Φ (μ^2) : ℂ) *
          ((pcfLG_A t * Real.exp (-(μ^2 * pcfXi t)) : ℝ) : ℂ)) - (pcfLG_ser N (μ^2) t : ℂ) =
          (Φ (μ^2) / pcfLG_S N (μ^2) : ℂ) * (X - pcfLG_ser N (μ^2) t) +
          (((Φ (μ^2) - pcfLG_S N (μ^2)) / pcfLG_S N (μ^2) : ℝ) : ℂ) * (pcfLG_ser N (μ^2) t : ℂ) := by
        rw [hXdef]; push_cast; field_simp; ring
      rw [hF]
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_div, abs_of_pos (by linarith : (0:ℝ) < pcfLG_S N (μ^2))]
      have hn1 : ‖(Φ (μ^2) / pcfLG_S N (μ^2) : ℂ)‖ ≤ 4 := by
        rw [show (Φ (μ^2) / pcfLG_S N (μ^2) : ℂ) = ((Φ (μ^2) / pcfLG_S N (μ^2) : ℝ) : ℂ) by
          push_cast; rfl, Complex.norm_real, Real.norm_eq_abs, abs_div,
          abs_of_pos (by linarith : (0:ℝ) < Φ (μ^2)), abs_of_pos (by linarith : (0:ℝ) < _),
          div_le_iff₀ (by linarith)]
        linarith
      have hp : 0 < (μ^2)^N := by positivity
      have h2 : |Φ (μ^2) - pcfLG_S N (μ^2)| / pcfLG_S N (μ^2) * |pcfLG_ser N (μ^2) t| ≤
          3*B / (μ^2)^N := by
        calc |Φ (μ^2) - pcfLG_S N (μ^2)| / pcfLG_S N (μ^2) * |pcfLG_ser N (μ^2) t|
            ≤ (B / (μ^2)^N) / (1/2) * (3/2) := by
              gcongr
          _ = 3*B / (μ^2)^N := by ring
      calc ‖(Φ (μ^2) / pcfLG_S N (μ^2) : ℂ)‖ * ‖X - (pcfLG_ser N (μ^2) t : ℂ)‖ +
            |Φ (μ^2) - pcfLG_S N (μ^2)| / pcfLG_S N (μ^2) * |pcfLG_ser N (μ^2) t|
          ≤ 4 * (C / (μ^2)^N) + 3*B / (μ^2)^N := by
            gcongr
      _ = (4*C + 3*B) * ((μ^2)^N)⁻¹ := by ring
    intro N
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · -- `N = 0` follows from `N = 1`
      have h1 := key 1 le_rfl
      have hb : (fun p : ℝ × ℝ => (p.1:ℂ)^(-(2*(1:ℕ):ℤ))) =O[pcfUniformFilter (Ici (1+δ))]
          (fun p : ℝ × ℝ => (p.1:ℂ)^(-(2*(0:ℕ):ℤ))) := by
        refine IsBigO.of_bound 1 (pcfLG_eventually_uniform 1 fun μ hμ t _ => ?_)
        rw [pcfLG_norm_zpow (by linarith), pcfLG_norm_zpow (by linarith)]
        simp only [pow_zero, inv_one, one_mul, pow_one]
        exact inv_le_one_of_one_le₀ (by nlinarith)
      have hc : (fun _ : ℝ × ℝ => (1:ℂ)) =O[pcfUniformFilter (Ici (1+δ))]
          (fun p : ℝ × ℝ => (p.1:ℂ)^(-(2*(0:ℕ):ℤ))) :=
        IsBigO.of_bound 1 (Eventually.of_forall fun p => by simp)
      refine ((h1.trans hb).add hc).congr_left fun p => ?_
      simp [pcfOlverA, pcfOlverU, pcfOlverPair]
    · exact key N hN

end DLMF.Confluent
