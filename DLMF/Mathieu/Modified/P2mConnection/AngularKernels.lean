/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Mathieu.Modified.Properties
public import DLMF.Mathieu.IntegralEquations
public import DLMF.Mathieu.SecondSolutions

/-!
# Angular Bessel kernels for modified Mathieu connections

Bessel product integrals and angular Fourier kernels prepare the radial Mathieu connection
formulas.

Source references and common attribution are retained in
`DLMF.Mathieu.Modified.P2mConnection`.
-/

@[expose] public noncomputable section

open Complex Set Filter MeasureTheory

open scoped Topology Real

namespace DLMF.Mathieu

/-- `A^{2n}_0(q) ≠ 0` for real `q ≠ 0` (recurrences and normalizations of §28.4). -/
theorem p2m_fourierA_even_zero_ne (n : ℕ) {q : ℝ} (hq : q ≠ 0) :
    mathieuFourierA (2 * n) 0 q ≠ 0 := by
  intro h0
  have hq' : (q : ℂ) ≠ 0 := by exact_mod_cast hq
  have key : ∀ m : ℕ, mathieuFourierA (2 * n) (2 * m) q = 0 ∧
      mathieuFourierA (2 * n) (2 * m + 2) q = 0 := by
    intro m
    induction m with
    | zero =>
      refine ⟨by simpa using h0, ?_⟩
      have h := mathieuFourierA_even_rec_zero n q
      rw [h0, mul_zero, zero_sub, neg_eq_zero] at h
      simpa using (mul_eq_zero.mp h).resolve_left hq'
    | succ m ih =>
      refine ⟨by rw [show 2 * (m + 1) = 2 * m + 2 by ring]; exact ih.2, ?_⟩
      rcases m with _ | m
      · have h := mathieuFourierA_even_rec_one n q
        simp only [mul_zero, zero_add] at ih
        rw [ih.2, h0, mul_zero, zero_sub, mul_zero, zero_add, neg_eq_zero] at h
        simpa using (mul_eq_zero.mp h).resolve_left hq'
      · have h := mathieuFourierA_even_rec n q (m := m + 2) (by omega)
        rw [show 2 * (m + 2) - 2 = 2 * (m + 1) by omega, show 2 * (m + 2) = 2 * (m + 1) + 2 by ring,
          ih.1, ih.2] at h
        rw [show 2 * (m + 1 + 1) + 2 = 2 * (m + 1) + 2 + 2 by ring]
        simp only [mul_zero, zero_sub, zero_add, neg_eq_zero] at h
        exact (mul_eq_zero.mp h).resolve_left hq'
  have hs := hasSum_mathieuFourierA_even_sq n q
  have : (fun m : ℕ => (if m = 0 then (2 : ℂ) else 1) * mathieuFourierA (2 * n) (2 * m) q ^ 2) =
      fun _ => 0 := by funext m; rw [(key m).1]; simp
  rw [this] at hs
  exact one_ne_zero (hs.unique hasSum_zero)

/-- `A^{2n+1}_1(q) ≠ 0` for real `q ≠ 0` (recurrences and normalizations of §28.4). -/
theorem p2m_fourierA_odd_one_ne (n : ℕ) {q : ℝ} (hq : q ≠ 0) :
    mathieuFourierA (2 * n + 1) 1 q ≠ 0 := by
  intro h0
  have hq' : (q : ℂ) ≠ 0 := by exact_mod_cast hq
  have key : ∀ m : ℕ, mathieuFourierA (2 * n + 1) (2 * m + 1) q = 0 ∧
      mathieuFourierA (2 * n + 1) (2 * m + 3) q = 0 := by
    intro m
    induction m with
    | zero =>
      refine ⟨by simpa using h0, ?_⟩
      have h := mathieuFourierA_odd_rec_zero n q
      rw [h0, mul_zero, zero_sub, neg_eq_zero] at h
      simpa using (mul_eq_zero.mp h).resolve_left hq'
    | succ m ih =>
      refine ⟨by rw [show 2 * (m + 1) + 1 = 2 * m + 3 by ring]; exact ih.2, ?_⟩
      have h := mathieuFourierA_odd_rec n q (m := m + 1) (by omega)
      rw [show 2 * (m + 1) - 1 = 2 * m + 1 by omega, show 2 * (m + 1) + 1 = 2 * m + 3 by ring,
        ih.1, ih.2] at h
      rw [show 2 * (m + 1) + 3 = 2 * (m + 1) + 3 by ring]
      simp only [mul_zero, zero_sub, zero_add, neg_eq_zero] at h
      exact (mul_eq_zero.mp h).resolve_left hq'
  have hs := hasSum_mathieuFourierA_odd_sq n q
  have : (fun m : ℕ => mathieuFourierA (2 * n + 1) (2 * m + 1) q ^ 2) = fun _ => 0 := by
    funext m; rw [(key m).1]; simp
  rw [this] at hs
  exact one_ne_zero (hs.unique hasSum_zero)

/-- `B^{2n+1}_1(q) ≠ 0` for real `q ≠ 0` (recurrences and normalizations of §28.4). -/
theorem p2m_fourierB_odd_one_ne (n : ℕ) {q : ℝ} (hq : q ≠ 0) :
    mathieuFourierB (2 * n + 1) 1 q ≠ 0 := by
  intro h0
  have hq' : (q : ℂ) ≠ 0 := by exact_mod_cast hq
  have key : ∀ m : ℕ, mathieuFourierB (2 * n + 1) (2 * m + 1) q = 0 ∧
      mathieuFourierB (2 * n + 1) (2 * m + 3) q = 0 := by
    intro m
    induction m with
    | zero =>
      refine ⟨by simpa using h0, ?_⟩
      have h := mathieuFourierB_odd_rec_zero n q
      rw [h0, mul_zero, zero_sub, neg_eq_zero] at h
      simpa using (mul_eq_zero.mp h).resolve_left hq'
    | succ m ih =>
      refine ⟨by rw [show 2 * (m + 1) + 1 = 2 * m + 3 by ring]; exact ih.2, ?_⟩
      have h := mathieuFourierB_odd_rec n q (m := m + 1) (by omega)
      rw [show 2 * (m + 1) - 1 = 2 * m + 1 by omega, show 2 * (m + 1) + 1 = 2 * m + 3 by ring,
        ih.1, ih.2] at h
      simp only [mul_zero, zero_sub, zero_add, neg_eq_zero] at h
      exact (mul_eq_zero.mp h).resolve_left hq'
  have hs := hasSum_mathieuFourierB_odd_sq n q
  have : (fun m : ℕ => mathieuFourierB (2 * n + 1) (2 * m + 1) q ^ 2) = fun _ => 0 := by
    funext m; rw [(key m).1]; simp
  rw [this] at hs
  exact one_ne_zero (hs.unique hasSum_zero)

/-- `B^{2n+2}_2(q) ≠ 0` for real `q ≠ 0` (recurrences and normalizations of §28.4). -/
theorem p2m_fourierB_even_two_ne (n : ℕ) {q : ℝ} (hq : q ≠ 0) :
    mathieuFourierB (2 * n + 2) 2 q ≠ 0 := by
  intro h0
  have hq' : (q : ℂ) ≠ 0 := by exact_mod_cast hq
  have key : ∀ m : ℕ, mathieuFourierB (2 * n + 2) (2 * m + 2) q = 0 ∧
      mathieuFourierB (2 * n + 2) (2 * m + 4) q = 0 := by
    intro m
    induction m with
    | zero =>
      refine ⟨by simpa using h0, ?_⟩
      have h := mathieuFourierB_even_rec_zero n q
      rw [h0, mul_zero, zero_sub, neg_eq_zero] at h
      simpa using (mul_eq_zero.mp h).resolve_left hq'
    | succ m ih =>
      refine ⟨by rw [show 2 * (m + 1) + 2 = 2 * m + 4 by ring]; exact ih.2, ?_⟩
      have h := mathieuFourierB_even_rec n q (m := m + 2) (by omega)
      rw [show 2 * (m + 2) - 2 = 2 * m + 2 by omega, show 2 * (m + 2) = 2 * m + 4 by ring,
        ih.1, ih.2] at h
      rw [show 2 * (m + 1) + 4 = 2 * m + 4 + 2 by ring]
      simp only [mul_zero, zero_sub, zero_add, neg_eq_zero] at h
      exact (mul_eq_zero.mp h).resolve_left hq'
  have hs := hasSum_mathieuFourierB_even_sq n q
  have : (fun m : ℕ => mathieuFourierB (2 * n + 2) (2 * m + 2) q ^ 2) = fun _ => 0 := by
    funext m; rw [(key m).1]; simp
  rw [this] at hs
  exact one_ne_zero (hs.unique hasSum_zero)

/-- Termwise integration of `g ∑ c_n φ_n` over `[a, b]`, for `∑ ‖c_n‖ < ∞`, `‖φ_n‖ ≤ 1`
(dominated interchange of sum and integral). -/
lemma p2m_hasSum_integral_mul {c : ℕ → ℂ} (hc : Summable fun n => ‖c n‖)
    {φ : ℕ → ℝ → ℂ} (hφc : ∀ n, Continuous (φ n)) (hφ : ∀ n x, ‖φ n x‖ ≤ 1)
    {g f : ℝ → ℂ} (hg : Continuous g) (hf : ∀ x, HasSum (fun n => c n * φ n x) (f x))
    (a b : ℝ) :
    HasSum (fun n => c n * ∫ x in a..b, g x * φ n x) (∫ x in a..b, g x * f x) := by
  have e : (fun n => c n * ∫ x in a..b, g x * φ n x) =
      fun n => ∫ x in a..b, g x * (c n * φ n x) := by
    funext n; rw [← intervalIntegral.integral_const_mul]; congr 1; funext x; ring
  rw [e]
  refine intervalIntegral.hasSum_integral_of_dominated_convergence
    (fun n x => ‖c n‖ * ‖g x‖) (fun n => ?_) (fun n => ?_) ?_ ?_ ?_
  · exact (hg.mul (continuous_const.mul (hφc n))).aestronglyMeasurable
  · refine ae_of_all _ fun x _ => ?_
    rw [norm_mul, norm_mul]
    calc ‖g x‖ * (‖c n‖ * ‖φ n x‖) ≤ ‖g x‖ * (‖c n‖ * 1) := by gcongr; exact hφ n x
      _ = _ := by ring
  · exact ae_of_all _ fun x _ => hc.mul_right _
  · simp_rw [tsum_mul_right]
    exact (continuous_const.mul hg.norm).intervalIntegrable _ _
  · exact ae_of_all _ fun x _ => (hf x).mul_left (g x)

/-- `∫₀^π ce_{2n}(π/2 - t) dt = π A_0`. -/
lemma p2m_integral_ce_even_shift (n : ℕ) (q : ℝ) :
    ∫ t in (0 : ℝ)..π, mathieuCe (2 * n) ((π / 2 - t : ℝ) : ℂ) q =
      π * mathieuFourierA (2 * n) 0 q := by
  have hc : Continuous fun u : ℝ => mathieuCe (2 * n) (u : ℂ) q :=
    (isMathieuSolution_mathieuCe _ _).differentiable.continuous.comp continuous_ofReal
  rw [intervalIntegral.integral_comp_sub_left (fun u : ℝ => mathieuCe (2 * n) (u : ℂ) q)]
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0)
    (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
  have h1 : ∫ x in (π / 2 - π)..0, mathieuCe (2 * n) (x : ℂ) q =
      ∫ x in (0 : ℝ)..π / 2, mathieuCe (2 * n) (x : ℂ) q := by
    have := intervalIntegral.integral_comp_neg (a := 0) (b := π / 2)
      (fun x : ℝ => mathieuCe (2 * n) (x : ℂ) q)
    rw [neg_zero] at this
    rw [show π / 2 - π = -(π / 2) by ring, ← this]
    simp only [Complex.ofReal_neg, mathieuCe_neg]
  rw [h1, show π / 2 - 0 = π / 2 by ring, p1a2_quarter_A0]
  ring

/-- `∑ (-1)^ℓ A^{2n}_{2ℓ} J_ℓ(h)² = (A^{2n}_0)² / ce_{2n}(π/2)` (from 10.9.26, 10.9.2, 28.10.1). -/
lemma p2m_key_even (n : ℕ) {h : ℝ} (hh : 0 < h) :
    HasSum (fun ℓ : ℕ => (-1 : ℂ) ^ ℓ * mathieuFourierA (2 * n) (2 * ℓ) (h ^ 2) *
      besselJ (ℓ : ℂ) (h : ℂ) ^ 2)
      (mathieuFourierA (2 * n) 0 (h ^ 2) ^ 2 / mathieuCe (2 * n) (π / 2) (h ^ 2)) := by
  set A := fun ℓ : ℕ => mathieuFourierA (2 * n) (2 * ℓ) (h ^ 2)
  set g : ℝ → ℂ := fun θ => besselJ 0 (2 * (h : ℂ) * (Real.cos θ : ℂ))
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hslit : (h : ℂ) ∈ slitPlane := by
    rw [mem_slitPlane_iff]; left; simpa using hh
  -- product formula
  have hprod : ∀ ℓ : ℕ, (-1 : ℂ) ^ ℓ * besselJ (ℓ : ℂ) (h : ℂ) ^ 2 =
      2 / π * ∫ θ in (0 : ℝ)..π / 2, g θ * Complex.cos (2 * ℓ * θ) := by
    intro ℓ
    have h1 := DLMF.Bessel.besselJ_mul_besselJ_eq_integral (ℓ : ℂ) (-(ℓ : ℂ))
      (by simp) hslit
    have h2 := DLMF.Bessel.besselJ_neg_int (ℓ : ℤ) (h : ℂ)
    push_cast at h2
    rw [zpow_natCast] at h2
    rw [h2, add_neg_cancel] at h1
    rw [show (-1 : ℂ) ^ ℓ * besselJ (ℓ : ℂ) (h : ℂ) ^ 2 =
      besselJ (ℓ : ℂ) h * ((-1) ^ ℓ * besselJ (ℓ : ℂ) h) by ring, h1]
    congr 2; funext θ; congr 2; ring
  -- summability of the coefficients
  have hsA : Summable fun ℓ => ‖A ℓ‖ := by
    have := (mathieu_fourier_locallyUniform (2 * n) (h ^ 2)).1 0
    simp only [mul_zero, Complex.cos_zero, mul_one] at this
    exact this.comp_injective (fun a b hab => by simpa using hab)
  have hgc : Continuous g := by
    have hJ0 : Continuous (besselJ 0) := continuous_iff_continuousAt.2 fun x => by
      simpa using (Complex.analyticAt_besselJ_int 0 x).continuousAt
    exact hJ0.comp (by fun_prop)
  have hsum := p2m_hasSum_integral_mul hsA (φ := fun ℓ θ => Complex.cos (2 * ℓ * θ))
    (fun ℓ => by fun_prop) (fun ℓ x => by
      rw [show (2 * (ℓ : ℂ) * (x : ℂ)) = ((2 * ℓ * x : ℝ) : ℂ) by push_cast; ring,
        ← Complex.ofReal_cos, Complex.norm_real, Real.norm_eq_abs]
      exact Real.abs_cos_le_one _)
    hgc (f := fun θ => mathieuCe (2 * n) θ (h ^ 2))
    (fun x => hasSum_mathieuCe_even n (h ^ 2) x) 0 (π / 2)
  set ce : ℝ → ℂ := fun θ => mathieuCe (2 * n) (θ : ℂ) (h ^ 2)
  have hce : Continuous ce :=
    (isMathieuSolution_mathieuCe _ _).differentiable.continuous.comp continuous_ofReal
  set F : ℝ → ℝ → ℂ := fun θ t =>
    Complex.cos (2 * (h : ℂ) * (Real.cos θ : ℂ) * Complex.sin (t : ℂ)) * ce θ
  have hF : Continuous (Function.uncurry F) := by
    simp only [F, ce]
    exact (by fun_prop : Continuous fun p : ℝ × ℝ =>
      Complex.cos (2 * (h : ℂ) * (Real.cos p.1 : ℂ) * Complex.sin (p.2 : ℂ))).mul
      (hce.comp continuous_fst)
  have hI1 : ∫ θ in (0 : ℝ)..π / 2, g θ * ce θ =
      1 / π * ∫ θ in (0 : ℝ)..π / 2, ∫ t in (0 : ℝ)..π, F θ t := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    simp only [g, F, DLMF.Bessel.besselJ_zero_eq_integral_cos, intervalIntegral.integral_mul_const]
    ring
  have hswap : ∫ θ in (0 : ℝ)..π / 2, ∫ t in (0 : ℝ)..π, F θ t =
      ∫ t in (0 : ℝ)..π, ∫ θ in (0 : ℝ)..π / 2, F θ t := by
    refine intervalIntegral_intervalIntegral_swap ?_
    exact (hF.continuousOn.integrableOn_compact ((isCompact_uIcc (a := (0 : ℝ)) (b := π / 2)).prod
      (isCompact_uIcc (a := (0 : ℝ)) (b := π)))).mono_set
      (Set.prod_mono Set.uIoc_subset_uIcc Set.uIoc_subset_uIcc)
  have hinner : ∀ t : ℝ, ∫ θ in (0 : ℝ)..π / 2, F θ t = π / 2 *
      (mathieuFourierA (2 * n) 0 (h ^ 2) / mathieuCe (2 * n) (π / 2) (h ^ 2) *
        mathieuCe (2 * n) ((π / 2 - t : ℝ) : ℂ) (h ^ 2)) := by
    intro t
    have h1 := integral_cos_mathieuCe_even n h ((π / 2 - t : ℝ) : ℂ)
    rw [← Complex.ofReal_cos, Real.cos_pi_div_two_sub, Complex.ofReal_sin] at h1
    rw [← h1]
    field_simp
    refine intervalIntegral.integral_congr fun θ _ => ?_
    simp only [F, ce]
    congr 2; ring
  have hval : 2 / π * ∫ θ in (0 : ℝ)..π / 2, g θ * ce θ =
      mathieuFourierA (2 * n) 0 (h ^ 2) ^ 2 / mathieuCe (2 * n) (π / 2) (h ^ 2) := by
    rw [hI1, hswap]
    simp_rw [hinner]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      p2m_integral_ce_even_shift]
    field_simp
  rw [← hval]
  convert hsum.mul_left (2 / (π : ℂ)) using 1
  funext ℓ
  rw [show (-1 : ℂ) ^ ℓ * A ℓ * besselJ (ℓ : ℂ) (h : ℂ) ^ 2 =
    A ℓ * ((-1 : ℂ) ^ ℓ * besselJ (ℓ : ℂ) (h : ℂ) ^ 2) by ring, hprod]
  ring

/-- `∫₀^π cos t P(t) dt = 0` when `P(π - t) = P(t)`. -/
lemma p2m_integral_cos_mul_symm {P : ℝ → ℂ} (hP : ∀ t, P (π - t) = P t) :
    ∫ t in (0 : ℝ)..π, (Real.cos t : ℂ) * P t = 0 := by
  have h := intervalIntegral.integral_comp_sub_left (a := 0) (b := π)
    (fun t : ℝ => (Real.cos t : ℂ) * P t) π
  simp only [sub_self, sub_zero, Real.cos_pi_sub, hP, Complex.ofReal_neg, neg_mul,
    intervalIntegral.integral_neg] at h
  linear_combination -h / 2

/-- `∫₀^π sin t ce_{2n+1}(π/2 - t) dt = (π/2) A_1`. -/
lemma p2m_integral_ce_odd_shift (n : ℕ) (q : ℝ) :
    ∫ t in (0 : ℝ)..π, (Real.sin t : ℂ) * mathieuCe (2 * n + 1) ((π / 2 - t : ℝ) : ℂ) q =
      π / 2 * mathieuFourierA (2 * n + 1) 1 q := by
  set f : ℝ → ℂ := fun u => (Real.cos u : ℂ) * mathieuCe (2 * n + 1) (u : ℂ) q
  have hc : Continuous f := by
    have := (isMathieuSolution_mathieuCe (2 * n + 1) q).differentiable.continuous
    fun_prop
  have e : ∀ t : ℝ, (Real.sin t : ℂ) * mathieuCe (2 * n + 1) ((π / 2 - t : ℝ) : ℂ) q =
      f (π / 2 - t) := by
    intro t; simp only [f, Real.cos_pi_div_two_sub]
  simp_rw [e]
  rw [intervalIntegral.integral_comp_sub_left f]
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0)
    (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
  have h1 : ∫ x in (π / 2 - π)..0, f x = ∫ x in (0 : ℝ)..π / 2, f x := by
    have := intervalIntegral.integral_comp_neg (a := 0) (b := π / 2) f
    rw [neg_zero] at this
    rw [show π / 2 - π = -(π / 2) by ring, ← this]
    simp only [f, Complex.ofReal_neg, mathieuCe_neg, Real.cos_neg]
  rw [h1, show π / 2 - 0 = π / 2 by ring]
  simp only [f]
  rw [p1a2_quarter_A1]
  ring

/-- `∑ (-1)^ℓ A^{2n+1}_{2ℓ+1} J_ℓ(h) J_{ℓ+1}(h) = -h (A^{2n+1}_1)² / (2 ce'_{2n+1}(π/2))`
(from 10.9.26, 10.9.2, 28.10.3). -/
lemma p2m_key_odd (n : ℕ) {h : ℝ} (hh : 0 < h) :
    HasSum (fun ℓ : ℕ => (-1 : ℂ) ^ ℓ * mathieuFourierA (2 * n + 1) (2 * ℓ + 1) (h ^ 2) *
      (besselJ (ℓ : ℂ) (h : ℂ) * besselJ ((ℓ + 1 : ℕ) : ℂ) (h : ℂ)))
      (-(h * mathieuFourierA (2 * n + 1) 1 (h ^ 2) ^ 2) /
        (2 * deriv (fun w => mathieuCe (2 * n + 1) w (h ^ 2)) (π / 2))) := by
  set A := fun ℓ : ℕ => mathieuFourierA (2 * n + 1) (2 * ℓ + 1) (h ^ 2)
  set g : ℝ → ℂ := fun θ => besselJ 1 (2 * (h : ℂ) * (Real.cos θ : ℂ))
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hslit : (h : ℂ) ∈ slitPlane := by
    rw [mem_slitPlane_iff]; left; simpa using hh
  have hprod : ∀ ℓ : ℕ, (-1 : ℂ) ^ ℓ * (besselJ (ℓ : ℂ) (h : ℂ) *
      besselJ ((ℓ + 1 : ℕ) : ℂ) (h : ℂ)) =
      2 / π * ∫ θ in (0 : ℝ)..π / 2, g θ * Complex.cos ((2 * ℓ + 1) * θ) := by
    intro ℓ
    have h1 := DLMF.Bessel.besselJ_mul_besselJ_eq_integral ((ℓ + 1 : ℕ) : ℂ) (-(ℓ : ℂ))
      (by simp) hslit
    have h2 := DLMF.Bessel.besselJ_neg_int (ℓ : ℤ) (h : ℂ)
    push_cast at h2
    simp only [Nat.cast_add, Nat.cast_one] at h1
    rw [zpow_natCast] at h2
    rw [h2, show (ℓ : ℂ) + 1 + -ℓ = 1 by ring] at h1
    rw [show (-1 : ℂ) ^ ℓ * (besselJ (ℓ : ℂ) (h : ℂ) * besselJ ((ℓ + 1 : ℕ) : ℂ) (h : ℂ)) =
      besselJ ((ℓ : ℂ) + 1) h * ((-1) ^ ℓ * besselJ (ℓ : ℂ) h) by push_cast; ring, h1]
    congr 2; funext θ; congr 2; ring
  have hsA : Summable fun ℓ => ‖A ℓ‖ := by
    have := (mathieu_fourier_locallyUniform (2 * n + 1) (h ^ 2)).1 0
    simp only [mul_zero, Complex.cos_zero, mul_one] at this
    exact this.comp_injective (fun a b hab => by simpa using hab)
  have hJ1 : Continuous (besselJ 1) := continuous_iff_continuousAt.2 fun x => by
    simpa using (Complex.analyticAt_besselJ_int 1 x).continuousAt
  have hgc : Continuous g := hJ1.comp (by fun_prop)
  have hsum := p2m_hasSum_integral_mul hsA (φ := fun ℓ θ => Complex.cos ((2 * ℓ + 1) * θ))
    (fun ℓ => by fun_prop) (fun ℓ x => by
      rw [show ((2 * (ℓ : ℂ) + 1) * (x : ℂ)) = (((2 * ℓ + 1) * x : ℝ) : ℂ) by push_cast; ring,
        ← Complex.ofReal_cos, Complex.norm_real, Real.norm_eq_abs]
      exact Real.abs_cos_le_one _)
    hgc (f := fun θ => mathieuCe (2 * n + 1) θ (h ^ 2))
    (fun x => hasSum_mathieuCe_odd n (h ^ 2) x) 0 (π / 2)
  set ce : ℝ → ℂ := fun θ => mathieuCe (2 * n + 1) (θ : ℂ) (h ^ 2)
  have hce : Continuous ce :=
    (isMathieuSolution_mathieuCe _ _).differentiable.continuous.comp continuous_ofReal
  set Fc : ℝ → ℝ → ℂ := fun θ t =>
    Complex.cos (2 * (h : ℂ) * (Real.cos θ : ℂ) * (Real.sin t : ℂ)) * ce θ
  set Fs : ℝ → ℝ → ℂ := fun θ t =>
    Complex.sin (2 * (h : ℂ) * (Real.cos θ : ℂ) * (Real.sin t : ℂ)) * ce θ
  set F : ℝ → ℝ → ℂ := fun θ t => (Real.cos t : ℂ) * Fc θ t + (Real.sin t : ℂ) * Fs θ t
  have hFc : Continuous (Function.uncurry Fc) := by
    simp only [Fc]
    exact (by fun_prop : Continuous fun p : ℝ × ℝ =>
      Complex.cos (2 * (h : ℂ) * (Real.cos p.1 : ℂ) * (Real.sin p.2 : ℂ))).mul
      (hce.comp continuous_fst)
  have hFs : Continuous (Function.uncurry Fs) := by
    simp only [Fs]
    exact (by fun_prop : Continuous fun p : ℝ × ℝ =>
      Complex.sin (2 * (h : ℂ) * (Real.cos p.1 : ℂ) * (Real.sin p.2 : ℂ))).mul
      (hce.comp continuous_fst)
  have hF : Continuous (Function.uncurry F) := by
    simp only [F]
    exact ((by fun_prop : Continuous fun p : ℝ × ℝ => (Real.cos p.2 : ℂ)).mul hFc).add
      ((by fun_prop : Continuous fun p : ℝ × ℝ => (Real.sin p.2 : ℂ)).mul hFs)
  have hI1 : ∫ θ in (0 : ℝ)..π / 2, g θ * ce θ =
      1 / π * ∫ θ in (0 : ℝ)..π / 2, ∫ t in (0 : ℝ)..π, F θ t := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    have hJ : ∀ z : ℂ, besselJ 1 z = 1 / π * ∫ t in (0 : ℝ)..π,
        Complex.cos (z * Complex.sin t - t) := by
      intro z; simpa using DLMF.Bessel.besselJ_int_eq_integral_cos 1 z
    simp only [g]
    rw [hJ, mul_assoc, ← intervalIntegral.integral_mul_const]
    congr 2; funext t
    simp only [F, Fc, Fs, Complex.cos_sub, Complex.ofReal_sin,
      Complex.ofReal_cos]
    ring
  have hswap : ∫ θ in (0 : ℝ)..π / 2, ∫ t in (0 : ℝ)..π, F θ t =
      ∫ t in (0 : ℝ)..π, ∫ θ in (0 : ℝ)..π / 2, F θ t := by
    refine intervalIntegral_intervalIntegral_swap ?_
    exact (hF.continuousOn.integrableOn_compact ((isCompact_uIcc (a := (0 : ℝ)) (b := π / 2)).prod
      (isCompact_uIcc (a := (0 : ℝ)) (b := π)))).mono_set
      (Set.prod_mono Set.uIoc_subset_uIcc Set.uIoc_subset_uIcc)
  set K := -(h * mathieuFourierA (2 * n + 1) 1 (h ^ 2) /
        deriv (fun w => mathieuCe (2 * n + 1) w (h ^ 2)) (π / 2))
  have hQ : ∀ t : ℝ, ∫ θ in (0 : ℝ)..π / 2, Fs θ t = π / 2 *
      (K * mathieuCe (2 * n + 1) ((π / 2 - t : ℝ) : ℂ) (h ^ 2)) := by
    intro t
    have h1 := integral_sin_mathieuCe_odd n h ((π / 2 - t : ℝ) : ℂ)
    rw [← Complex.ofReal_cos, Real.cos_pi_div_two_sub] at h1
    rw [← h1]
    field_simp
    refine intervalIntegral.integral_congr fun θ _ => ?_
    simp only [Fs, ce]
    congr 2; ring
  have hP : ∀ t, ∫ θ in (0 : ℝ)..π / 2, Fc θ (π - t) = ∫ θ in (0 : ℝ)..π / 2, Fc θ t := by
    intro t; simp only [Fc, Real.sin_pi_sub]
  have hcP : Continuous fun t => ∫ θ in (0 : ℝ)..π / 2, Fc θ t := by
    have : Continuous (Function.uncurry fun t θ => Fc θ t) := by
      show Continuous fun p : ℝ × ℝ => Fc p.2 p.1
      simp only [Fc]
      exact (by fun_prop : Continuous fun p : ℝ × ℝ =>
        Complex.cos (2 * (h : ℂ) * (Real.cos p.2 : ℂ) * (Real.sin p.1 : ℂ))).mul
        (hce.comp continuous_snd)
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' this _ _
  have hinner : ∀ t : ℝ, ∫ θ in (0 : ℝ)..π / 2, F θ t =
      (Real.cos t : ℂ) * (∫ θ in (0 : ℝ)..π / 2, Fc θ t) +
        (Real.sin t : ℂ) * (π / 2 * (K * mathieuCe (2 * n + 1) ((π / 2 - t : ℝ) : ℂ) (h ^ 2))) := by
    intro t
    rw [← hQ, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add]
    · exact (continuous_const.mul (by simp only [Fc]; fun_prop)).intervalIntegrable _ _
    · exact (continuous_const.mul (by simp only [Fs]; fun_prop)).intervalIntegrable _ _
  have hce1 : Continuous fun t : ℝ => (Real.sin t : ℂ) *
      (π / 2 * (K * mathieuCe (2 * n + 1) ((π / 2 - t : ℝ) : ℂ) (h ^ 2))) := by
    have := (isMathieuSolution_mathieuCe (2 * n + 1) (h ^ 2)).differentiable.continuous
    fun_prop
  have hval : 2 / π * ∫ θ in (0 : ℝ)..π / 2, g θ * ce θ =
      -(h * mathieuFourierA (2 * n + 1) 1 (h ^ 2) ^ 2) /
        (2 * deriv (fun w => mathieuCe (2 * n + 1) w (h ^ 2)) (π / 2)) := by
    rw [hI1, hswap]
    simp_rw [hinner]
    have hi1 : IntervalIntegrable (fun t : ℝ => (Real.cos t : ℂ) *
        ∫ θ in (0 : ℝ)..π / 2, Fc θ t) volume 0 π :=
      ((continuous_ofReal.comp Real.continuous_cos).mul hcP).intervalIntegrable _ _
    rw [intervalIntegral.integral_add hi1 (hce1.intervalIntegrable _ _),
      p2m_integral_cos_mul_symm hP]
    simp_rw [mul_left_comm _ (π / 2 : ℂ), mul_left_comm _ K]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      p2m_integral_ce_odd_shift]
    simp only [K]
    field_simp
    ring
  rw [← hval]
  convert hsum.mul_left (2 / (π : ℂ)) using 1
  funext ℓ
  rw [show (-1 : ℂ) ^ ℓ * A ℓ * (besselJ (ℓ : ℂ) (h : ℂ) * besselJ ((ℓ + 1 : ℕ) : ℂ) (h : ℂ)) =
    A ℓ * ((-1 : ℂ) ^ ℓ * (besselJ (ℓ : ℂ) (h : ℂ) * besselJ ((ℓ + 1 : ℕ) : ℂ) (h : ℂ))) by ring,
    hprod]
  ring

/-- `∫₀^π sin t se_{2n+1}(t) dt = (π/2) B_1`. -/
lemma p2m_integral_se_odd (n : ℕ) (q : ℝ) :
    ∫ t in (0 : ℝ)..π, (Real.sin t : ℂ) * mathieuSe (2 * n + 1) (t : ℂ) q =
      π / 2 * mathieuFourierB (2 * n + 1) 1 q := by
  set f : ℝ → ℂ := fun u => (Real.sin u : ℂ) * mathieuSe (2 * n + 1) (u : ℂ) q
  have hc : Continuous f := by
    have := (isMathieuSolution_mathieuSe (2 * n + 1) q).differentiable.continuous
    fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := π / 2)
    (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
  have h1 : ∫ x in (π / 2)..π, f x = ∫ x in (0 : ℝ)..π / 2, f x := by
    have := intervalIntegral.integral_comp_sub_left (a := 0) (b := π / 2) f π
    rw [show π - π / 2 = π / 2 by ring, sub_zero] at this
    rw [← this]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [f, Real.sin_pi_sub]
    congr 1
    have e1 := mathieuSe_odd_add_pi n (-(t : ℂ)) q
    rw [mathieuSe_neg] at e1
    push_cast
    rw [show (π : ℂ) - t = -t + π by ring, e1]; ring
  rw [h1]
  simp only [f]
  rw [p1a2_quarter_B1]
  ring

/-- For `n ≥ 1` the Fourier coefficients `B^n_{2ℓ+a}(q)` are absolutely summable in `ℓ`
(they decay faster than any geometric sequence). -/
private lemma p2m_summable_norm_fourierB {n : ℕ} (hn : n ≠ 0) (q : ℝ) (a : ℕ) :
    Summable fun ℓ : ℕ => ‖mathieuFourierB n (2 * ℓ + a) q‖ := by
  obtain ⟨C, hC0, hC⟩ := p2f_fourierB_decay hn q 1
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun ℓ => ?_)
    ((summable_geometric_of_lt_one (Real.exp_pos (-1)).le
      (Real.exp_lt_one_iff.mpr (by norm_num))).mul_left C)
  refine (hC (2 * ℓ + a)).trans ?_
  rw [← Real.exp_nat_mul]
  gcongr
  push_cast; nlinarith

/-- `∑ B^{2n+1}_{2ℓ+1} J_ℓ(ih) J_{ℓ+1}(ih) = ih (B^{2n+1}_1)² / (2 se'_{2n+1}(0))`
(from 10.9.26, 10.9.2, 28.10.5). -/
lemma p2m_key_se_odd (n : ℕ) {h : ℝ} (hh : 0 < h) :
    HasSum (fun ℓ : ℕ => mathieuFourierB (2 * n + 1) (2 * ℓ + 1) (h ^ 2) *
      (besselJ (ℓ : ℂ) (I * h) * besselJ ((ℓ + 1 : ℕ) : ℂ) (I * h)))
      (I * h * mathieuFourierB (2 * n + 1) 1 (h ^ 2) ^ 2 /
        (2 * deriv (fun w => mathieuSe (2 * n + 1) w (h ^ 2)) 0)) := by
  set c := fun ℓ : ℕ => (-1 : ℂ) ^ ℓ * mathieuFourierB (2 * n + 1) (2 * ℓ + 1) (h ^ 2)
  set G : ℝ → ℂ := fun θ => besselJ 1 (2 * (I * h) * (Real.cos θ : ℂ))
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hslit : I * (h : ℂ) ∈ slitPlane := by
    rw [mem_slitPlane_iff]; right; simpa using hh.ne'
  have hprod : ∀ ℓ : ℕ, (-1 : ℂ) ^ ℓ * (besselJ (ℓ : ℂ) (I * h) *
      besselJ ((ℓ + 1 : ℕ) : ℂ) (I * h)) =
      2 / π * ∫ θ in (0 : ℝ)..π / 2, G θ * Complex.cos ((2 * ℓ + 1) * θ) := by
    intro ℓ
    have h1 := DLMF.Bessel.besselJ_mul_besselJ_eq_integral ((ℓ + 1 : ℕ) : ℂ) (-(ℓ : ℂ))
      (by simp) hslit
    have h2 := DLMF.Bessel.besselJ_neg_int (ℓ : ℤ) (I * h)
    push_cast at h2
    simp only [Nat.cast_add, Nat.cast_one] at h1
    rw [zpow_natCast] at h2
    rw [h2, show (ℓ : ℂ) + 1 + -ℓ = 1 by ring] at h1
    rw [show (-1 : ℂ) ^ ℓ * (besselJ (ℓ : ℂ) (I * h) * besselJ ((ℓ + 1 : ℕ) : ℂ) (I * h)) =
      besselJ ((ℓ : ℂ) + 1) (I * h) * ((-1) ^ ℓ * besselJ (ℓ : ℂ) (I * h)) by push_cast; ring, h1]
    congr 2; funext θ; congr 2; ring
  have hsB : Summable fun ℓ => ‖c ℓ‖ := by
    simpa only [c, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul] using
      p2m_summable_norm_fourierB (n := 2 * n + 1) (by omega) (h ^ 2) 1
  have hJ1 : Continuous (besselJ 1) := continuous_iff_continuousAt.2 fun x => by
    simpa using (Complex.analyticAt_besselJ_int 1 x).continuousAt
  have hGc : Continuous G := hJ1.comp (by fun_prop)
  have hsum := p2m_hasSum_integral_mul hsB (φ := fun ℓ θ => Complex.cos ((2 * ℓ + 1) * θ))
    (fun ℓ => by fun_prop) (fun ℓ x => by
      rw [show ((2 * (ℓ : ℂ) + 1) * (x : ℂ)) = (((2 * ℓ + 1) * x : ℝ) : ℂ) by push_cast; ring,
        ← Complex.ofReal_cos, Complex.norm_real, Real.norm_eq_abs]
      exact Real.abs_cos_le_one _)
    hGc (f := fun θ => mathieuSe (2 * n + 1) ((π / 2 - θ : ℝ) : ℂ) (h ^ 2))
    (fun x => by
      have := hasSum_mathieuSe_odd n (h ^ 2) ((π / 2 - x : ℝ) : ℂ)
      convert this using 2 with ℓ
      have e := p1a2_sin_odd_half_pi_sub ℓ (x : ℂ)
      push_cast at e ⊢
      rw [e]; simp only [c]; ring) 0 (π / 2)
  set se : ℝ → ℂ := fun u => mathieuSe (2 * n + 1) (u : ℂ) (h ^ 2)
  have hse : Continuous se :=
    (isMathieuSolution_mathieuSe _ _).differentiable.continuous.comp continuous_ofReal
  -- reflect θ ↦ π/2 - θ
  have hrefl : ∫ θ in (0 : ℝ)..π / 2, G θ * mathieuSe (2 * n + 1) ((π / 2 - θ : ℝ) : ℂ) (h ^ 2) =
      ∫ u in (0 : ℝ)..π / 2, besselJ 1 (2 * (I * h) * (Real.sin u : ℂ)) * se u := by
    have := intervalIntegral.integral_comp_sub_left (a := 0) (b := π / 2)
      (fun u : ℝ => besselJ 1 (2 * (I * h) * (Real.sin u : ℂ)) * se u) (π / 2)
    rw [show π / 2 - π / 2 = 0 by ring, sub_zero] at this
    rw [← this]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    simp only [G, se, Real.sin_pi_div_two_sub]
  set Fc : ℝ → ℝ → ℂ := fun u t =>
    Complex.cos (2 * (I * h) * (Real.sin u : ℂ) * (Real.sin t : ℂ)) * se u
  set Fs : ℝ → ℝ → ℂ := fun u t =>
    Complex.sin (2 * (I * h) * (Real.sin u : ℂ) * (Real.sin t : ℂ)) * se u
  set F : ℝ → ℝ → ℂ := fun u t => (Real.cos t : ℂ) * Fc u t + (Real.sin t : ℂ) * Fs u t
  have hFc : Continuous (Function.uncurry Fc) := by
    simp only [Fc]
    exact (by fun_prop : Continuous fun p : ℝ × ℝ =>
      Complex.cos (2 * (I * h) * (Real.sin p.1 : ℂ) * (Real.sin p.2 : ℂ))).mul
      (hse.comp continuous_fst)
  have hFs : Continuous (Function.uncurry Fs) := by
    simp only [Fs]
    exact (by fun_prop : Continuous fun p : ℝ × ℝ =>
      Complex.sin (2 * (I * h) * (Real.sin p.1 : ℂ) * (Real.sin p.2 : ℂ))).mul
      (hse.comp continuous_fst)
  have hF : Continuous (Function.uncurry F) := by
    simp only [F]
    exact ((by fun_prop : Continuous fun p : ℝ × ℝ => (Real.cos p.2 : ℂ)).mul hFc).add
      ((by fun_prop : Continuous fun p : ℝ × ℝ => (Real.sin p.2 : ℂ)).mul hFs)
  have hI1 : ∫ u in (0 : ℝ)..π / 2, besselJ 1 (2 * (I * h) * (Real.sin u : ℂ)) * se u =
      1 / π * ∫ u in (0 : ℝ)..π / 2, ∫ t in (0 : ℝ)..π, F u t := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun u _ => ?_
    have hJ : ∀ z : ℂ, besselJ 1 z = 1 / π * ∫ t in (0 : ℝ)..π,
        Complex.cos (z * Complex.sin t - t) := by
      intro z; simpa using DLMF.Bessel.besselJ_int_eq_integral_cos 1 z
    rw [hJ, mul_assoc, ← intervalIntegral.integral_mul_const]
    congr 2; funext t
    simp only [F, Fc, Fs, Complex.cos_sub, Complex.ofReal_sin, Complex.ofReal_cos]
    ring
  have hswap : ∫ u in (0 : ℝ)..π / 2, ∫ t in (0 : ℝ)..π, F u t =
      ∫ t in (0 : ℝ)..π, ∫ u in (0 : ℝ)..π / 2, F u t := by
    refine intervalIntegral_intervalIntegral_swap ?_
    exact (hF.continuousOn.integrableOn_compact ((isCompact_uIcc (a := (0 : ℝ)) (b := π / 2)).prod
      (isCompact_uIcc (a := (0 : ℝ)) (b := π)))).mono_set
      (Set.prod_mono Set.uIoc_subset_uIcc Set.uIoc_subset_uIcc)
  set K := h * mathieuFourierB (2 * n + 1) 1 (h ^ 2) /
        deriv (fun w => mathieuSe (2 * n + 1) w (h ^ 2)) 0
  have hQ : ∀ t : ℝ, ∫ u in (0 : ℝ)..π / 2, Fs u t = I * (π / 2 *
      (K * mathieuSe (2 * n + 1) (t : ℂ) (h ^ 2))) := by
    intro t
    have h1 := integral_sinh_mathieuSe_odd n h (t : ℂ)
    rw [← h1]
    field_simp
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun u _ => ?_
    simp only [Fs, se]
    rw [show 2 * (I * (h : ℂ)) * (Real.sin u : ℂ) * (Real.sin t : ℂ) =
      (2 * h * Complex.sin t * Real.sin u) * I by push_cast; ring, Complex.sin_mul_I]
    ring
  have hP : ∀ t, ∫ u in (0 : ℝ)..π / 2, Fc u (π - t) = ∫ u in (0 : ℝ)..π / 2, Fc u t := by
    intro t; simp only [Fc, Real.sin_pi_sub]
  have hcP : Continuous fun t => ∫ u in (0 : ℝ)..π / 2, Fc u t := by
    have : Continuous (Function.uncurry fun t u => Fc u t) := by
      show Continuous fun p : ℝ × ℝ => Fc p.2 p.1
      simp only [Fc]
      exact (by fun_prop : Continuous fun p : ℝ × ℝ =>
        Complex.cos (2 * (I * h) * (Real.sin p.2 : ℂ) * (Real.sin p.1 : ℂ))).mul
        (hse.comp continuous_snd)
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' this _ _
  have hinner : ∀ t : ℝ, ∫ u in (0 : ℝ)..π / 2, F u t =
      (Real.cos t : ℂ) * (∫ u in (0 : ℝ)..π / 2, Fc u t) +
        (Real.sin t : ℂ) * (I * (π / 2 * (K * mathieuSe (2 * n + 1) (t : ℂ) (h ^ 2)))) := by
    intro t
    rw [← hQ, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add]
    · exact (continuous_const.mul (by simp only [Fc]; fun_prop)).intervalIntegrable _ _
    · exact (continuous_const.mul (by simp only [Fs]; fun_prop)).intervalIntegrable _ _
  have hse1 : Continuous fun t : ℝ => (Real.sin t : ℂ) *
      (I * (π / 2 * (K * mathieuSe (2 * n + 1) (t : ℂ) (h ^ 2)))) := by
    have := (isMathieuSolution_mathieuSe (2 * n + 1) (h ^ 2)).differentiable.continuous
    fun_prop
  have hval : 2 / π * ∫ θ in (0 : ℝ)..π / 2,
      G θ * mathieuSe (2 * n + 1) ((π / 2 - θ : ℝ) : ℂ) (h ^ 2) =
      I * h * mathieuFourierB (2 * n + 1) 1 (h ^ 2) ^ 2 /
        (2 * deriv (fun w => mathieuSe (2 * n + 1) w (h ^ 2)) 0) := by
    rw [hrefl, hI1, hswap]
    simp_rw [hinner]
    have hi1 : IntervalIntegrable (fun t : ℝ => (Real.cos t : ℂ) *
        ∫ u in (0 : ℝ)..π / 2, Fc u t) volume 0 π :=
      ((continuous_ofReal.comp Real.continuous_cos).mul hcP).intervalIntegrable _ _
    rw [intervalIntegral.integral_add hi1 (hse1.intervalIntegrable _ _),
      p2m_integral_cos_mul_symm hP]
    simp_rw [mul_left_comm _ I, mul_left_comm _ (π / 2 : ℂ), mul_left_comm _ K]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, p2m_integral_se_odd]
    simp only [K]
    field_simp
    ring
  rw [← hval]
  convert hsum.mul_left (2 / (π : ℂ)) using 1
  funext ℓ
  have hP2 : (-1 : ℂ) ^ ℓ * (-1) ^ ℓ = 1 := by rw [← pow_add, ← two_mul, pow_mul]; simp
  rw [show mathieuFourierB (2 * n + 1) (2 * ℓ + 1) (h ^ 2) *
      (besselJ (ℓ : ℂ) (I * h) * besselJ ((ℓ + 1 : ℕ) : ℂ) (I * h)) =
    c ℓ * ((-1 : ℂ) ^ ℓ * (besselJ (ℓ : ℂ) (I * h) * besselJ ((ℓ + 1 : ℕ) : ℂ) (I * h))) by
      simp only [c]; linear_combination (-(mathieuFourierB (2 * n + 1) (2 * ℓ + 1) (h ^ 2) *
        (besselJ (ℓ : ℂ) (I * h) * besselJ ((ℓ + 1 : ℕ) : ℂ) (I * h)))) * hP2, hprod]
  ring

/-- `∫₀^π w(t) P(t) dt = 0` when `w(π - t) = -w(t)` and `P(π - t) = P(t)`. -/
lemma p2m_integral_antisymm_mul_symm {w P : ℝ → ℂ} (hw : ∀ t, w (π - t) = -w t)
    (hP : ∀ t, P (π - t) = P t) : ∫ t in (0 : ℝ)..π, w t * P t = 0 := by
  have h := intervalIntegral.integral_comp_sub_left (a := 0) (b := π) (fun t : ℝ => w t * P t) π
  simp only [sub_self, sub_zero, hw, hP, neg_mul, intervalIntegral.integral_neg] at h
  linear_combination -h / 2

/-- `y (J_1(y) + J_3(y)) = 4 J_2(y)`. -/
lemma p2m_besselJ_one_add_three (y : ℂ) :
    y * (besselJ 1 y + besselJ 3 y) = 4 * besselJ 2 y := by
  by_cases hy : y = 0
  · subst hy; simp [DLMF.Bessel.besselJ_apply_zero]
  · have h := p2m_besselJExp_rec 2 hy 0
    rw [Complex.exp_zero, mul_one] at h
    have e : ∀ k : ℤ, besselJExp (k : ℂ) y 0 = besselJ (k : ℂ) y := fun k => by
      rw [p1c_besselJExp_intCast, Complex.exp_zero, mul_one]
    have e1 := e 1; have e2 := e 2; have e3 := e 3
    push_cast at e1 e2 e3
    rw [show (2 : ℂ) - 1 = 1 by norm_num, show (2 : ℂ) + 1 = 3 by norm_num, e1, e2, e3] at h
    rw [h]; field_simp; ring

/-- `∫₀^π sin t cos t se_{2n+2}(π/2 - t) dt = (π/4) B_2`. -/
lemma p2m_integral_se_even_shift (n : ℕ) (q : ℝ) :
    ∫ t in (0 : ℝ)..π, (Real.sin t : ℂ) * (Real.cos t : ℂ) *
      mathieuSe (2 * n + 2) ((π / 2 - t : ℝ) : ℂ) q = π / 4 * mathieuFourierB (2 * n + 2) 2 q := by
  set f : ℝ → ℂ := fun u => (Real.sin u : ℂ) * (Real.cos u : ℂ) *
    mathieuSe (2 * n + 2) (u : ℂ) q
  have hc : Continuous f := by
    have := (isMathieuSolution_mathieuSe (2 * n + 2) q).differentiable.continuous
    fun_prop
  have e : ∀ t : ℝ, (Real.sin t : ℂ) * (Real.cos t : ℂ) *
      mathieuSe (2 * n + 2) ((π / 2 - t : ℝ) : ℂ) q = f (π / 2 - t) := by
    intro t; simp only [f, Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub]; ring
  simp_rw [e]
  rw [intervalIntegral.integral_comp_sub_left f]
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0)
    (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
  have h1 : ∫ x in (π / 2 - π)..0, f x = ∫ x in (0 : ℝ)..π / 2, f x := by
    have := intervalIntegral.integral_comp_neg (a := 0) (b := π / 2) f
    rw [neg_zero] at this
    rw [show π / 2 - π = -(π / 2) by ring, ← this]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [f, Complex.ofReal_neg, mathieuSe_neg, Real.cos_neg, Real.sin_neg]; ring
  rw [h1, show π / 2 - 0 = π / 2 by ring]
  simp only [f]
  rw [p1a2_quarter_B2]
  ring

/-- `J_a(h) J_b(h)` for integers `a, b` with `a + b = s ≥ 0`, as a product integral. -/
lemma p2m_prod_int {a b : ℤ} {s : ℕ} (hab : a + b = s) {h : ℂ} (hh : h ∈ slitPlane) :
    besselJ (a : ℂ) h * besselJ (b : ℂ) h = 2 / π * ∫ θ in (0 : ℝ)..π / 2,
      besselJ (s : ℂ) (2 * h * (Real.cos θ : ℂ)) * Complex.cos (((a - b : ℤ) : ℂ) * θ) := by
  have h1 := DLMF.Bessel.besselJ_mul_besselJ_eq_integral (a : ℂ) (b : ℂ) (by
    rw [show (a : ℂ) + b = ((a + b : ℤ) : ℂ) by push_cast; ring, hab]; simp; linarith) hh
  rw [h1, show (a : ℂ) + b = (s : ℂ) by exact_mod_cast hab]
  congr 2; funext θ; push_cast; ring_nf

/-- The Bessel-product terms of the sum in `p2m_key_se_even` as Fourier integrals:
`(-1)^ℓ (4 J_ℓ J_{ℓ+2} + 2h (J_{ℓ+1} J_{ℓ+2} - J_ℓ J_{ℓ+3}))(h)`
`= (2/π) ∫₀^{π/2} g(θ) sin((2ℓ+2)θ) dθ` with `g(θ) = 2h (J₁ + J₃)(2h cos θ) sin θ`. -/
private lemma p2m_key_se_even_prod {h : ℝ} (hh : 0 < h) (ℓ : ℕ) :
    (-1 : ℂ) ^ ℓ * (4 * (besselJ (ℓ : ℂ) h * besselJ ((ℓ + 2 : ℕ) : ℂ) h) +
        2 * h * (besselJ ((ℓ + 1 : ℕ) : ℂ) h * besselJ ((ℓ + 2 : ℕ) : ℂ) h -
          besselJ (ℓ : ℂ) h * besselJ ((ℓ + 3 : ℕ) : ℂ) h)) =
      2 / π * ∫ θ in (0 : ℝ)..π / 2, 2 * h * (besselJ 1 (2 * (h : ℂ) * (Real.cos θ : ℂ)) +
        besselJ 3 (2 * (h : ℂ) * (Real.cos θ : ℂ))) * (Real.sin θ : ℂ) *
          Complex.sin ((2 * ℓ + 2) * θ) := by
  set Y : ℝ → ℂ := fun θ => 2 * (h : ℂ) * (Real.cos θ : ℂ)
  set g : ℝ → ℂ := fun θ => 2 * h * (besselJ 1 (Y θ) + besselJ 3 (Y θ)) * (Real.sin θ : ℂ)
  show _ = 2 / π * ∫ θ in (0 : ℝ)..π / 2, g θ * Complex.sin ((2 * ℓ + 2) * θ)
  have hslit : (h : ℂ) ∈ slitPlane := by
    rw [mem_slitPlane_iff]; left; simpa using hh
  have hneg : ∀ k : ℕ, besselJ (((-(k : ℤ)) : ℤ) : ℂ) (h : ℂ) = (-1 : ℂ) ^ k * besselJ (k : ℂ) h :=
    fun k => by
      have := DLMF.Bessel.besselJ_neg_int (k : ℤ) (h : ℂ)
      rw [zpow_natCast] at this; push_cast at this ⊢; exact this

  have hP : (-1 : ℂ) ^ ℓ * (-1) ^ ℓ = 1 := by rw [← pow_add, ← two_mul, pow_mul]; simp
  have P1 : besselJ ((ℓ + 2 : ℕ) : ℂ) h * ((-1) ^ ℓ * besselJ (ℓ : ℂ) h) =
      2 / π * ∫ θ in (0 : ℝ)..π / 2, besselJ 2 (Y θ) * Complex.cos ((2 * ℓ + 2) * θ) := by
    have := p2m_prod_int (a := ((ℓ + 2 : ℕ) : ℤ)) (b := -(ℓ : ℤ)) (s := 2) (by push_cast; ring)
      hslit
    rw [hneg] at this
    simp only [Int.cast_natCast] at this
    rw [this]; congr 2; funext θ; simp only [Y]; push_cast; ring_nf
  have P2 : besselJ ((ℓ + 2 : ℕ) : ℂ) h * ((-1) ^ (ℓ + 1) * besselJ ((ℓ + 1 : ℕ) : ℂ) h) =
      2 / π * ∫ θ in (0 : ℝ)..π / 2, besselJ 1 (Y θ) * Complex.cos ((2 * ℓ + 3) * θ) := by
    have := p2m_prod_int (a := ((ℓ + 2 : ℕ) : ℤ)) (b := -((ℓ + 1 : ℕ) : ℤ)) (s := 1)
      (by push_cast; ring) hslit
    rw [hneg] at this
    simp only [Int.cast_natCast] at this
    rw [this]; congr 2; funext θ; simp only [Y]; push_cast; ring_nf
  have P3 : besselJ ((ℓ + 3 : ℕ) : ℂ) h * ((-1) ^ ℓ * besselJ (ℓ : ℂ) h) =
      2 / π * ∫ θ in (0 : ℝ)..π / 2, besselJ 3 (Y θ) * Complex.cos ((2 * ℓ + 3) * θ) := by
    have := p2m_prod_int (a := ((ℓ + 3 : ℕ) : ℤ)) (b := -(ℓ : ℤ)) (s := 3) (by push_cast; ring)
      hslit
    rw [hneg] at this
    simp only [Int.cast_natCast] at this
    rw [this]; congr 2; funext θ; simp only [Y]; push_cast; ring_nf
  have lhs : (-1 : ℂ) ^ ℓ * (4 * (besselJ (ℓ : ℂ) h * besselJ ((ℓ + 2 : ℕ) : ℂ) h) +
      2 * h * (besselJ ((ℓ + 1 : ℕ) : ℂ) h * besselJ ((ℓ + 2 : ℕ) : ℂ) h -
        besselJ (ℓ : ℂ) h * besselJ ((ℓ + 3 : ℕ) : ℂ) h)) =
      4 * (besselJ ((ℓ + 2 : ℕ) : ℂ) h * ((-1) ^ ℓ * besselJ (ℓ : ℂ) h)) -
      2 * h * (besselJ ((ℓ + 2 : ℕ) : ℂ) h * ((-1) ^ (ℓ + 1) * besselJ ((ℓ + 1 : ℕ) : ℂ) h)) -
      2 * h * (besselJ ((ℓ + 3 : ℕ) : ℂ) h * ((-1) ^ ℓ * besselJ (ℓ : ℂ) h)) := by
    rw [pow_succ]; ring
  rw [lhs, P1, P2, P3]
  have hJc : ∀ k : ℤ, Continuous (besselJ (k : ℂ)) := fun k =>
    continuous_iff_continuousAt.2 fun x => (Complex.analyticAt_besselJ_int k x).continuousAt
  have hJ1 : Continuous (besselJ 1) := by simpa using hJc 1
  have hJ2 : Continuous (besselJ 2) := by simpa using hJc 2
  have hJ3 : Continuous (besselJ 3) := by simpa using hJc 3
  have hY : Continuous Y := by fun_prop
  have e : ∀ θ : ℝ, g θ * Complex.sin ((2 * ℓ + 2) * θ) =
      4 * (besselJ 2 (Y θ) * Complex.cos ((2 * ℓ + 2) * θ)) -
      2 * h * (besselJ 1 (Y θ) * Complex.cos ((2 * ℓ + 3) * θ)) -
      2 * h * (besselJ 3 (Y θ) * Complex.cos ((2 * ℓ + 3) * θ)) := by
    intro θ
    have hr := p2m_besselJ_one_add_three (Y θ)
    have c2 : Complex.cos ((2 * ℓ + 3) * θ) =
        Complex.cos ((2 * ℓ + 2) * θ) * Complex.cos θ -
          Complex.sin ((2 * ℓ + 2) * θ) * Complex.sin θ := by
      rw [← Complex.cos_add]; ring_nf
    simp only [g]
    rw [c2]
    simp only [Y, Complex.ofReal_cos, Complex.ofReal_sin] at hr ⊢
    linear_combination Complex.cos ((2 * ℓ + 2) * θ) * hr
  simp_rw [e]
  have i1 : IntervalIntegrable (fun θ : ℝ => besselJ 2 (Y θ) * Complex.cos ((2 * ℓ + 2) * θ))
      volume 0 (π / 2) := ((hJ2.comp hY).mul (by fun_prop)).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun θ : ℝ => besselJ 1 (Y θ) * Complex.cos ((2 * ℓ + 3) * θ))
      volume 0 (π / 2) := ((hJ1.comp hY).mul (by fun_prop)).intervalIntegrable _ _
  have i3 : IntervalIntegrable (fun θ : ℝ => besselJ 3 (Y θ) * Complex.cos ((2 * ℓ + 3) * θ))
      volume 0 (π / 2) := ((hJ3.comp hY).mul (by fun_prop)).intervalIntegrable _ _
  rw [intervalIntegral.integral_sub ((i1.const_mul 4).sub (i2.const_mul _)) (i3.const_mul _),
    intervalIntegral.integral_sub (i1.const_mul 4) (i2.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  ring

/-- `J₁(y) + J₃(y) = (1/π) ∫₀^π (2 cos t cos 2t cos(y sin t) + 4 sin t cos² t sin(y sin t)) dt`,
from Bessel's integral 10.9.2. -/
private lemma p2m_besselJ_one_add_three_integral (y : ℂ) :
    besselJ 1 y + besselJ 3 y = 1 / π * ∫ t in (0 : ℝ)..π,
      (2 * (Real.cos t : ℂ) * (Real.cos (2 * t) : ℂ) * Complex.cos (y * (Real.sin t : ℂ)) +
        4 * (Real.sin t : ℂ) * (Real.cos t : ℂ) * ((Real.cos t : ℂ) *
          Complex.sin (y * (Real.sin t : ℂ)))) := by
  have e1 : besselJ 1 y = 1 / π * ∫ t in (0 : ℝ)..π, Complex.cos (y * Complex.sin t - t) := by
    simpa using DLMF.Bessel.besselJ_int_eq_integral_cos 1 y
  have e3 : besselJ 3 y = 1 / π * ∫ t in (0 : ℝ)..π,
      Complex.cos (y * Complex.sin t - 3 * t) := by
    simpa using DLMF.Bessel.besselJ_int_eq_integral_cos 3 y
  rw [e1, e3, ← mul_add, ← intervalIntegral.integral_add (by
    exact (by fun_prop : Continuous fun t : ℝ =>
      Complex.cos (y * Complex.sin t - t)).intervalIntegrable _ _)
    (by exact (by fun_prop : Continuous fun t : ℝ =>
      Complex.cos (y * Complex.sin t - 3 * t)).intervalIntegrable _ _)]
  congr 2; funext t
  simp only [Complex.ofReal_cos, Complex.ofReal_sin, Complex.ofReal_mul, Complex.ofReal_ofNat]
  rw [show y * Complex.sin t - 3 * t = (y * Complex.sin t - t) - 2 * t by ring,
    Complex.cos_sub (y * Complex.sin t - t), Complex.cos_sub, Complex.sin_sub,
    Complex.cos_two_mul, Complex.sin_two_mul]
  linear_combination (-2 * Complex.cos (y * Complex.sin t) * Complex.cos t) *
    Complex.sin_sq_add_cos_sq (t : ℂ)

/-- The Bessel-product sum for `se_{2n+2}`, equal to `-h² (B^{2n+2}_2)² / se'_{2n+2}(π/2)`
(from 10.9.26, 10.9.2, 28.10.7). -/
lemma p2m_key_se_even (n : ℕ) {h : ℝ} (hh : 0 < h) :
    HasSum (fun ℓ : ℕ => (-1 : ℂ) ^ ℓ * mathieuFourierB (2 * n + 2) (2 * ℓ + 2) (h ^ 2) *
      (4 * (besselJ (ℓ : ℂ) h * besselJ ((ℓ + 2 : ℕ) : ℂ) h) +
        2 * h * (besselJ ((ℓ + 1 : ℕ) : ℂ) h * besselJ ((ℓ + 2 : ℕ) : ℂ) h -
          besselJ (ℓ : ℂ) h * besselJ ((ℓ + 3 : ℕ) : ℂ) h)))
      (-(h ^ 2 * mathieuFourierB (2 * n + 2) 2 (h ^ 2) ^ 2) /
        deriv (fun w => mathieuSe (2 * n + 2) w (h ^ 2)) (π / 2)) := by
  set B := fun ℓ : ℕ => mathieuFourierB (2 * n + 2) (2 * ℓ + 2) (h ^ 2)
  set Y : ℝ → ℂ := fun θ => 2 * (h : ℂ) * (Real.cos θ : ℂ)
  set g : ℝ → ℂ := fun θ => 2 * h * (besselJ 1 (Y θ) + besselJ 3 (Y θ)) * (Real.sin θ : ℂ)
  have hprod : ∀ ℓ : ℕ, (-1 : ℂ) ^ ℓ * (4 * (besselJ (ℓ : ℂ) h * besselJ ((ℓ + 2 : ℕ) : ℂ) h) +
        2 * h * (besselJ ((ℓ + 1 : ℕ) : ℂ) h * besselJ ((ℓ + 2 : ℕ) : ℂ) h -
          besselJ (ℓ : ℂ) h * besselJ ((ℓ + 3 : ℕ) : ℂ) h)) =
      2 / π * ∫ θ in (0 : ℝ)..π / 2, g θ * Complex.sin ((2 * ℓ + 2) * θ) :=
    p2m_key_se_even_prod hh
  have hsB : Summable fun ℓ => ‖B ℓ‖ :=
    p2m_summable_norm_fourierB (n := 2 * n + 2) (by omega) (h ^ 2) 2
  have hJc : ∀ k : ℤ, Continuous (besselJ (k : ℂ)) := fun k =>
    continuous_iff_continuousAt.2 fun x => (Complex.analyticAt_besselJ_int k x).continuousAt
  have hJ1 : Continuous (besselJ 1) := by simpa using hJc 1
  have hJ3 : Continuous (besselJ 3) := by simpa using hJc 3
  have hY : Continuous Y := by fun_prop
  have hgc : Continuous g := by
    simp only [g]
    exact (continuous_const.mul ((hJ1.comp hY).add (hJ3.comp hY))).mul (by fun_prop)
  have hsum := p2m_hasSum_integral_mul hsB (φ := fun ℓ θ => Complex.sin ((2 * ℓ + 2) * θ))
    (fun ℓ => by fun_prop) (fun ℓ x => by
      rw [show ((2 * (ℓ : ℂ) + 2) * (x : ℂ)) = (((2 * ℓ + 2) * x : ℝ) : ℂ) by push_cast; ring,
        ← Complex.ofReal_sin, Complex.norm_real, Real.norm_eq_abs]
      exact Real.abs_sin_le_one _)
    hgc (f := fun θ => mathieuSe (2 * n + 2) θ (h ^ 2))
    (fun x => hasSum_mathieuSe_even n (h ^ 2) x) 0 (π / 2)
  set se : ℝ → ℂ := fun θ => mathieuSe (2 * n + 2) (θ : ℂ) (h ^ 2)
  have hse : Continuous se :=
    (isMathieuSolution_mathieuSe _ _).differentiable.continuous.comp continuous_ofReal
  set Fc : ℝ → ℝ → ℂ := fun θ t =>
    Complex.cos (2 * (h : ℂ) * (Real.cos θ : ℂ) * (Real.sin t : ℂ)) * (Real.sin θ : ℂ) * se θ
  set Fs : ℝ → ℝ → ℂ := fun θ t =>
    Complex.sin (2 * (h : ℂ) * (Real.cos θ : ℂ) * (Real.sin t : ℂ)) * (Real.sin θ : ℂ) * se θ
  set F : ℝ → ℝ → ℂ := fun θ t => (2 * (Real.cos t : ℂ) * (Real.cos (2 * t) : ℂ)) * Fc θ t +
    (4 * (Real.sin t : ℂ) * (Real.cos t : ℂ)) * ((Real.cos t : ℂ) * Fs θ t)
  have hFc : Continuous (Function.uncurry Fc) := by
    simp only [Fc]
    exact ((by fun_prop : Continuous fun p : ℝ × ℝ =>
      Complex.cos (2 * (h : ℂ) * (Real.cos p.1 : ℂ) * (Real.sin p.2 : ℂ))).mul
      (by fun_prop : Continuous fun p : ℝ × ℝ => (Real.sin p.1 : ℂ))).mul
      (hse.comp continuous_fst)
  have hFs : Continuous (Function.uncurry Fs) := by
    simp only [Fs]
    exact ((by fun_prop : Continuous fun p : ℝ × ℝ =>
      Complex.sin (2 * (h : ℂ) * (Real.cos p.1 : ℂ) * (Real.sin p.2 : ℂ))).mul
      (by fun_prop : Continuous fun p : ℝ × ℝ => (Real.sin p.1 : ℂ))).mul
      (hse.comp continuous_fst)
  have hF : Continuous (Function.uncurry F) := by
    simp only [F]
    exact ((by fun_prop : Continuous fun p : ℝ × ℝ =>
      (2 * (Real.cos p.2 : ℂ) * (Real.cos (2 * p.2) : ℂ))).mul hFc).add
      ((by fun_prop : Continuous fun p : ℝ × ℝ => (4 * (Real.sin p.2 : ℂ) * (Real.cos p.2 : ℂ))).mul
        ((by fun_prop : Continuous fun p : ℝ × ℝ => (Real.cos p.2 : ℂ)).mul hFs))
  have hJ13 := p2m_besselJ_one_add_three_integral
  have hI1 : ∫ θ in (0 : ℝ)..π / 2, g θ * se θ =
      2 * h * (1 / π * ∫ θ in (0 : ℝ)..π / 2, ∫ t in (0 : ℝ)..π, F θ t) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    simp only [g]
    rw [hJ13]
    have e : ∫ t in (0 : ℝ)..π, F θ t = (∫ t in (0 : ℝ)..π,
        (2 * (Real.cos t : ℂ) * (Real.cos (2 * t) : ℂ) * Complex.cos (Y θ * (Real.sin t : ℂ)) +
          4 * (Real.sin t : ℂ) * (Real.cos t : ℂ) * ((Real.cos t : ℂ) *
            Complex.sin (Y θ * (Real.sin t : ℂ))))) * ((Real.sin θ : ℂ) * se θ) := by
      rw [← intervalIntegral.integral_mul_const]
      congr 1; funext t
      simp only [F, Fc, Fs, Y]
      ring
    rw [e]
    ring
  have hswap : ∫ θ in (0 : ℝ)..π / 2, ∫ t in (0 : ℝ)..π, F θ t =
      ∫ t in (0 : ℝ)..π, ∫ θ in (0 : ℝ)..π / 2, F θ t := by
    refine intervalIntegral_intervalIntegral_swap ?_
    exact (hF.continuousOn.integrableOn_compact ((isCompact_uIcc (a := (0 : ℝ)) (b := π / 2)).prod
      (isCompact_uIcc (a := (0 : ℝ)) (b := π)))).mono_set
      (Set.prod_mono Set.uIoc_subset_uIcc Set.uIoc_subset_uIcc)
  set K := -(h * mathieuFourierB (2 * n + 2) 2 (h ^ 2) /
        (2 * deriv (fun w => mathieuSe (2 * n + 2) w (h ^ 2)) (π / 2)))
  have hQ : ∀ t : ℝ, ∫ θ in (0 : ℝ)..π / 2, (Real.cos t : ℂ) * Fs θ t = π / 2 *
      (K * mathieuSe (2 * n + 2) ((π / 2 - t : ℝ) : ℂ) (h ^ 2)) := by
    intro t
    have h1 := integral_sin_sin_mathieuSe_even n h ((π / 2 - t : ℝ) : ℂ)
    rw [← Complex.ofReal_cos, Real.cos_pi_div_two_sub, ← Complex.ofReal_sin,
      Real.sin_pi_div_two_sub] at h1
    rw [← h1]
    field_simp
    refine intervalIntegral.integral_congr fun θ _ => ?_
    simp only [Fs, se]
    ring_nf
  have hP : ∀ t, ∫ θ in (0 : ℝ)..π / 2, Fc θ (π - t) = ∫ θ in (0 : ℝ)..π / 2, Fc θ t := by
    intro t; simp only [Fc, Real.sin_pi_sub]
  have hcP : Continuous fun t => ∫ θ in (0 : ℝ)..π / 2, Fc θ t := by
    have : Continuous (Function.uncurry fun t θ => Fc θ t) := by
      show Continuous fun p : ℝ × ℝ => Fc p.2 p.1
      simp only [Fc]
      exact ((by fun_prop : Continuous fun p : ℝ × ℝ =>
        Complex.cos (2 * (h : ℂ) * (Real.cos p.2 : ℂ) * (Real.sin p.1 : ℂ))).mul
        (by fun_prop : Continuous fun p : ℝ × ℝ => (Real.sin p.2 : ℂ))).mul
        (hse.comp continuous_snd)
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' this _ _
  have hinner : ∀ t : ℝ, ∫ θ in (0 : ℝ)..π / 2, F θ t =
      (2 * (Real.cos t : ℂ) * (Real.cos (2 * t) : ℂ)) * (∫ θ in (0 : ℝ)..π / 2, Fc θ t) +
        (4 * (Real.sin t : ℂ) * (Real.cos t : ℂ)) *
          (π / 2 * (K * mathieuSe (2 * n + 2) ((π / 2 - t : ℝ) : ℂ) (h ^ 2))) := by
    intro t
    rw [← hQ, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add]
    · exact (continuous_const.mul (by simp only [Fc]; fun_prop)).intervalIntegrable _ _
    · exact (continuous_const.mul (continuous_const.mul
        (by simp only [Fs]; fun_prop))).intervalIntegrable _ _
  have hse1 : Continuous fun t : ℝ => (4 * (Real.sin t : ℂ) * (Real.cos t : ℂ)) *
      (π / 2 * (K * mathieuSe (2 * n + 2) ((π / 2 - t : ℝ) : ℂ) (h ^ 2))) := by
    have := (isMathieuSolution_mathieuSe (2 * n + 2) (h ^ 2)).differentiable.continuous
    fun_prop
  have hval : 2 / π * ∫ θ in (0 : ℝ)..π / 2, g θ * se θ =
      -(h ^ 2 * mathieuFourierB (2 * n + 2) 2 (h ^ 2) ^ 2) /
        deriv (fun w => mathieuSe (2 * n + 2) w (h ^ 2)) (π / 2) := by
    rw [hI1, hswap]
    simp_rw [hinner]
    have hi1 : IntervalIntegrable (fun t : ℝ => (2 * (Real.cos t : ℂ) * (Real.cos (2 * t) : ℂ)) *
        ∫ θ in (0 : ℝ)..π / 2, Fc θ t) volume 0 π :=
      ((by fun_prop : Continuous fun t : ℝ => (2 * (Real.cos t : ℂ) *
        (Real.cos (2 * t) : ℂ))).mul hcP).intervalIntegrable _ _
    rw [intervalIntegral.integral_add hi1 (hse1.intervalIntegrable _ _),
      p2m_integral_antisymm_mul_symm (fun t => by
        simp only [Real.cos_pi_sub, show 2 * (π - t) = -(2 * t) + 2 * π by ring,
          Real.cos_add_two_pi, Real.cos_neg]; push_cast; ring) hP]
    have e : ∀ t : ℝ, (4 * (Real.sin t : ℂ) * (Real.cos t : ℂ)) *
        (π / 2 * (K * mathieuSe (2 * n + 2) ((π / 2 - t : ℝ) : ℂ) (h ^ 2))) =
        (2 * π * K) * ((Real.sin t : ℂ) * (Real.cos t : ℂ) *
          mathieuSe (2 * n + 2) ((π / 2 - t : ℝ) : ℂ) (h ^ 2)) := fun t => by ring
    simp_rw [e]
    rw [intervalIntegral.integral_const_mul, p2m_integral_se_even_shift]
    simp only [K]
    field_simp
    ring
  rw [← hval]
  convert hsum.mul_left (2 / (π : ℂ)) using 1
  funext ℓ
  rw [show (-1 : ℂ) ^ ℓ * mathieuFourierB (2 * n + 2) (2 * ℓ + 2) (h ^ 2) *
      (4 * (besselJ (ℓ : ℂ) h * besselJ ((ℓ + 2 : ℕ) : ℂ) h) +
        2 * h * (besselJ ((ℓ + 1 : ℕ) : ℂ) h * besselJ ((ℓ + 2 : ℕ) : ℂ) h -
          besselJ (ℓ : ℂ) h * besselJ ((ℓ + 3 : ℕ) : ℂ) h)) =
      B ℓ * ((-1 : ℂ) ^ ℓ * (4 * (besselJ (ℓ : ℂ) h * besselJ ((ℓ + 2 : ℕ) : ℂ) h) +
        2 * h * (besselJ ((ℓ + 1 : ℕ) : ℂ) h * besselJ ((ℓ + 2 : ℕ) : ℂ) h -
          besselJ (ℓ : ℂ) h * besselJ ((ℓ + 3 : ℕ) : ℂ) h))) by simp only [B]; ring, hprod]
  ring

end DLMF.Mathieu
end
