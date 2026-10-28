/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Mathieu.Modified.P2mConnection.AngularKernels

/-!
# Radial Mathieu connections and monodromy

Radial connection coefficients and the imaginary-period monodromy identities for modified
Mathieu functions.

Source references and common attribution are retained in
`DLMF.Mathieu.Modified.P2mConnection`.
-/

@[expose] public noncomputable section

open Complex Set Filter MeasureTheory

open scoped Topology Real

namespace DLMF.Mathieu

/-- `‖J_n(w)‖ ≤ e^{‖w‖}` for integer `n`. -/
lemma p2m_norm_besselJ_int_le (n : ℤ) (w : ℂ) : ‖besselJ (n : ℂ) w‖ ≤ Real.exp ‖w‖ := by
  rw [DLMF.Bessel.besselJ_int_eq_integral_cos n w, norm_mul]
  have hπ : 0 < π := Real.pi_pos
  have h1 : ‖∫ θ in (0 : ℝ)..π, Complex.cos (w * Complex.sin θ - n * θ)‖ ≤
      Real.exp ‖w‖ * |π - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun θ _ => ?_
    refine (p2f_norm_cos_le _).trans (Real.exp_le_exp.2 ?_)
    have : (w * Complex.sin θ - n * θ).im = w.im * Real.sin θ := by
      have e : Complex.sin (θ : ℂ) = (Real.sin θ : ℂ) := (Complex.ofReal_sin θ).symm
      rw [e]; simp [Complex.sin_ofReal_re]
    rw [this, abs_mul]
    calc |w.im| * |Real.sin θ| ≤ |w.im| * 1 := by gcongr; exact Real.abs_sin_le_one θ
      _ ≤ ‖w‖ := by rw [mul_one]; exact Complex.abs_im_le_norm w
  rw [sub_zero, abs_of_pos hπ] at h1
  have h2 : ‖(1 / π : ℂ)‖ = 1 / π := by
    rw [norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hπ]
  rw [h2]
  calc 1 / π * ‖∫ θ in (0 : ℝ)..π, Complex.cos (w * Complex.sin θ - n * θ)‖
      ≤ 1 / π * (Real.exp ‖w‖ * π) := by gcongr
    _ = Real.exp ‖w‖ := by field_simp

/-- `‖J_n(h e^w)‖ ≤ e^{h e}` for `‖w‖ < 1`, `h > 0`. -/
lemma p2m_norm_besselJExp_int_le (n : ℤ) {h : ℝ} (hh : 0 < h) {w : ℂ} (hw : ‖w‖ < 1) :
    ‖besselJExp (n : ℂ) h w‖ ≤ Real.exp (h * Real.exp 1) := by
  rw [p1c_besselJExp_intCast]
  refine (p2m_norm_besselJ_int_le n _).trans (Real.exp_le_exp.2 ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh, Complex.norm_exp]
  gcongr
  exact (Complex.re_le_norm w).trans hw.le

/-- The derivative of `z ↦ J_a(h e^{-z}) J_b(h e^z) - J_b(h e^{-z}) J_a(h e^z)` at `0`. -/
lemma p2m_hasDerivAt_cross (a b : ℂ) {h : ℂ} (hh : h ≠ 0) :
    HasDerivAt (fun z => besselJExp a h (-z) * besselJExp b h z -
        besselJExp b h (-z) * besselJExp a h z)
      (2 * (b - a) * besselJExp a h 0 * besselJExp b h 0 +
        2 * h * (besselJExp (a + 1) h 0 * besselJExp b h 0 -
          besselJExp a h 0 * besselJExp (b + 1) h 0)) 0 := by
  have hn : ∀ μ : ℂ, HasDerivAt (fun z => besselJExp μ h (-z))
      (-(μ * besselJExp μ h 0 - h * besselJExp (μ + 1) h 0)) 0 := fun μ => by
    have := (p2m_hasDerivAt_besselJExp μ hh (-0)).comp (0 : ℂ) (hasDerivAt_neg (0 : ℂ))
    simp only [neg_zero, Complex.exp_zero, mul_one] at this
    convert this using 1 <;> first | rfl | ring
  have hp : ∀ μ : ℂ, HasDerivAt (fun z => besselJExp μ h z)
      (μ * besselJExp μ h 0 - h * besselJExp (μ + 1) h 0) 0 := fun μ => by
    have := p2m_hasDerivAt_besselJExp μ hh 0
    simpa using this
  have := ((hn a).mul (hp b)).sub ((hn b).mul (hp a))
  simp only [neg_zero] at this
  convert this using 1; ring

/-- `Ms^{(1)'}_{2k+2}(0, h) = -(-1)^k h² B^{2k+2}_2 / se'_{2k+2}(π/2)` (termwise
differentiation of 28.24.5). -/
lemma p2m_radialMs_one_even_deriv (k : ℕ) {h : ℝ} (hh : 0 < h) :
    deriv (fun z => radialMathieuMs 1 (2 * k + 2) z h) 0 =
      -((-1 : ℂ) ^ k * h ^ 2 * mathieuFourierB (2 * k + 2) 2 (h ^ 2) /
        deriv (fun w => mathieuSe (2 * k + 2) w (h ^ 2)) (π / 2)) := by
  have hq : h ^ 2 ≠ 0 := by positivity
  have hh' : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  have hB2 := p2m_fourierB_even_two_ne k hq
  have hB : mathieuFourierB (2 * k + 2) (2 * 0 + 2) (h ^ 2) ≠ 0 := by simpa using hB2
  set c := fun ℓ : ℕ => (-1 : ℂ) ^ k * ((-1 : ℂ) ^ ℓ *
    (mathieuFourierB (2 * k + 2) (2 * ℓ + 2) (h ^ 2) / mathieuFourierB (2 * k + 2) 2 (h ^ 2)))
  set f : ℕ → ℂ → ℂ := fun ℓ z => c ℓ *
    (besselJExp (ℓ : ℂ) h (-z) * besselJExp ((ℓ + 2 : ℕ) : ℂ) h z -
      besselJExp ((ℓ + 2 : ℕ) : ℂ) h (-z) * besselJExp (ℓ : ℂ) h z)
  have hS : ∀ z, HasSum (fun ℓ => f ℓ z) (radialMathieuMs 1 (2 * k + 2) z h) := by
    intro z
    have := hasSum_radialMathieuMs_even_cross 1 le_rfl (by norm_num) k 0 hh hB z
    convert this using 2 with ℓ
    simp only [f, c, mathieuCylExp, Nat.cast_zero, sub_zero, Int.cast_natCast, add_zero, mul_zero,
      zero_add]
    ring
  have hfun : (fun z => radialMathieuMs 1 (2 * k + 2) z h) = fun z => ∑' ℓ, f ℓ z :=
    funext fun z => (hS z).tsum_eq.symm
  have hsc : Summable fun ℓ => ‖c ℓ‖ := by
    obtain ⟨C, hC0, hC⟩ := p2f_fourierB_decay (n := 2 * k + 2) (by omega) (h ^ 2) 1
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun ℓ => ?_)
      ((summable_geometric_of_lt_one (Real.exp_pos (-1)).le
        (Real.exp_lt_one_iff.mpr (by norm_num))).mul_left
          (C / ‖mathieuFourierB (2 * k + 2) 2 (h ^ 2)‖))
    simp only [c, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_div]
    rw [div_eq_mul_inv C, mul_comm C, mul_assoc, div_eq_mul_inv, mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 (norm_nonneg _))
    refine (hC (2 * ℓ + 2)).trans ?_
    rw [← Real.exp_nat_mul]
    gcongr
    push_cast; nlinarith
  set M := Real.exp (h * Real.exp 1)
  have hD := hasSum_deriv_of_summable_norm (U := Metric.ball (0 : ℂ) 1)
    (F := f) (u := fun ℓ => ‖c ℓ‖ * (2 * M ^ 2)) (hsc.mul_right _)
    (fun ℓ => by
      have hd : Differentiable ℂ (f ℓ) := by
        intro z
        have h1 := fun μ => (p2m_hasDerivAt_besselJExp μ hh' z).differentiableAt
        have h2 := fun μ => ((p2m_hasDerivAt_besselJExp μ hh' (-z)).comp z
          (hasDerivAt_neg z)).differentiableAt
        exact ((((h2 _).mul (h1 _)).sub ((h2 _).mul (h1 _))).const_mul _)
      exact hd.differentiableOn)
    Metric.isOpen_ball
    (fun ℓ w hw => by
      rw [Metric.mem_ball, dist_zero_right] at hw
      have hw' : ‖-w‖ < 1 := by rwa [norm_neg]
      have e1 := p2m_norm_besselJExp_int_le (ℓ : ℤ) hh hw
      have e2 := p2m_norm_besselJExp_int_le ((ℓ + 2 : ℕ) : ℤ) hh hw
      have e3 := p2m_norm_besselJExp_int_le (ℓ : ℤ) hh hw'
      have e4 := p2m_norm_besselJExp_int_le ((ℓ + 2 : ℕ) : ℤ) hh hw'
      simp only [Int.cast_natCast] at e1 e2 e3 e4
      simp only [f, norm_mul]
      gcongr
      refine (norm_sub_le _ _).trans ?_
      rw [norm_mul, norm_mul]
      have hM : 0 ≤ M := (Real.exp_pos _).le
      nlinarith [norm_nonneg (besselJExp (ℓ : ℂ) h (-w)),
        norm_nonneg (besselJExp ((ℓ + 2 : ℕ) : ℂ) h w),
        norm_nonneg (besselJExp ((ℓ + 2 : ℕ) : ℂ) h (-w)),
        norm_nonneg (besselJExp (ℓ : ℂ) h w),
        mul_le_mul e3 e2 (norm_nonneg _) hM, mul_le_mul e4 e1 (norm_nonneg _) hM])
    (Metric.mem_ball_self one_pos)
  rw [hfun, ← hD.tsum_eq]
  have hder : ∀ ℓ, deriv (f ℓ) 0 = c ℓ * (4 * (besselJ (ℓ : ℂ) h * besselJ ((ℓ + 2 : ℕ) : ℂ) h) +
      2 * h * (besselJ ((ℓ + 1 : ℕ) : ℂ) h * besselJ ((ℓ + 2 : ℕ) : ℂ) h -
        besselJ (ℓ : ℂ) h * besselJ ((ℓ + 3 : ℕ) : ℂ) h)) := by
    intro ℓ
    have := (p2m_hasDerivAt_cross (ℓ : ℂ) ((ℓ + 2 : ℕ) : ℂ) hh').const_mul (c ℓ)
    rw [this.deriv]
    have ez : ∀ j : ℕ, besselJExp (j : ℂ) h 0 = besselJ (j : ℂ) h := fun j => by
      have := p1c_besselJExp_intCast (j : ℤ) h 0
      simpa using this
    rw [show (ℓ : ℂ) + 1 = ((ℓ + 1 : ℕ) : ℂ) by push_cast; ring,
      show ((ℓ + 2 : ℕ) : ℂ) + 1 = ((ℓ + 3 : ℕ) : ℂ) by push_cast; ring, ez, ez, ez, ez]
    push_cast; ring
  simp_rw [hder]
  have hk := (p2m_key_se_even k hh).mul_left ((-1 : ℂ) ^ k / mathieuFourierB (2 * k + 2) 2 (h ^ 2))
  have e : (fun ℓ : ℕ => c ℓ * (4 * (besselJ (ℓ : ℂ) h * besselJ ((ℓ + 2 : ℕ) : ℂ) h) +
      2 * h * (besselJ ((ℓ + 1 : ℕ) : ℂ) h * besselJ ((ℓ + 2 : ℕ) : ℂ) h -
        besselJ (ℓ : ℂ) h * besselJ ((ℓ + 3 : ℕ) : ℂ) h))) = fun ℓ : ℕ =>
      (-1 : ℂ) ^ k / mathieuFourierB (2 * k + 2) 2 (h ^ 2) *
        ((-1 : ℂ) ^ ℓ * mathieuFourierB (2 * k + 2) (2 * ℓ + 2) (h ^ 2) *
          (4 * (besselJ (ℓ : ℂ) h * besselJ ((ℓ + 2 : ℕ) : ℂ) h) +
            2 * h * (besselJ ((ℓ + 1 : ℕ) : ℂ) h * besselJ ((ℓ + 2 : ℕ) : ℂ) h -
              besselJ (ℓ : ℂ) h * besselJ ((ℓ + 3 : ℕ) : ℂ) h))) := funext fun ℓ => by
    simp only [c]; ring
  rw [e, hk.tsum_eq]
  field_simp

/-- If `w` solves the modified Mathieu equation 28.20.1 then `t ↦ w(ct)`, `c² = -1`, solves
Mathieu's equation 28.2.1. -/
theorem p1c_isMathieuSolution_comp {a q : ℂ} {w : ℂ → ℂ} (hw : IsModMathieuSolution a q w)
    {c : ℂ} (hc : c ^ 2 = -1) : IsMathieuSolution a q (fun t => w (c * t)) := by
  have hd : ∀ t, HasDerivAt (fun t => w (c * t)) (deriv w (c * t) * c) t := fun t => by
    have := ((hw.differentiable (c * t)).hasDerivAt).comp t ((hasDerivAt_id t).const_mul c)
    convert this using 1 <;> first | rfl | simp
  refine ⟨fun t => (hd t).differentiableAt, fun t => ?_⟩
  have he : deriv (fun t => w (c * t)) = fun t => deriv w (c * t) * c :=
    funext fun t => (hd t).deriv
  rw [he]
  have h2 := ((hw.hasDerivAt_deriv (c * t)).comp t ((hasDerivAt_id t).const_mul c)).mul_const c
  have hc' : c = I ∨ c = -I := by
    have : (c - I) * (c + I) = 0 := by ring_nf; rw [hc, I_sq]; ring
    rcases mul_eq_zero.mp this with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h)
  have hcos : Complex.cosh (2 * (c * t)) = Complex.cos (2 * t) := by
    rcases hc' with rfl | rfl
    · rw [show 2 * (I * t) = (2 * t) * I by ring, Complex.cosh_mul_I]
    · rw [show 2 * (-I * t) = -((2 * t) * I) by ring, Complex.cosh_neg, Complex.cosh_mul_I]
  convert h2 using 1
  · rfl
  rw [hcos]
  linear_combination ((2 * q * Complex.cos (2 * t) - a) * w (c * t)) * hc

/-- `J_k(h e^0) = J_k(h)` for the continued Bessel function of integer order. -/
lemma p2m_besselJExp_zero (k : ℤ) (h : ℂ) : besselJExp k h 0 = besselJ k h := by
  rw [p1c_besselJExp_intCast, Complex.exp_zero, mul_one]

/-- Integer orders with real `h` are admissible (without the normality of the noninteger
case). -/
lemma p2m_admissible_intCast (k : ℤ) (h : ℝ) : ModMathieuAdmissible (k : ℂ) (h : ℂ) :=
  Or.inr ⟨⟨k, rfl⟩, by rw [p1c_hsq]; exact ofReal_im _⟩

/-- `Mc^{(j)}_m(·, h)` solves Mathieu's equation along the imaginary axis (`j = 1, …, 4`). -/
lemma p2m_isMathieuSolution_McJ (j : ℕ) (hj₁ : 1 ≤ j) (hj₄ : j ≤ 4) (m : ℕ) {h : ℝ}
    (hh : 0 < h) :
    IsMathieuSolution (mathieuA m (h ^ 2)) ((h ^ 2 : ℝ) : ℂ)
      (fun t => radialMathieuMc j m (-I * t) h) := by
  have hadm : ModMathieuAdmissible (m : ℂ) (h : ℂ) := by
    simpa using p2m_admissible_intCast (m : ℤ) h
  have hh' : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  have hw := isModMathieuSolution_modMathieuM j hj₁ hj₄ hadm hh'
  have hl : mathieuLambda (m : ℂ) ((h : ℂ) ^ 2) = (mathieuA m (h ^ 2) : ℂ) := by
    rw [p1c_hsq, show (m : ℂ) = ((m : ℤ) : ℂ) by simp, mathieuLambda_intCast,
      mathieuLambdaInt]
    simp
  rw [hl, p1c_hsq] at hw
  exact p1c_isMathieuSolution_comp hw (c := -I) (by rw [neg_sq, I_sq])

/-- `Ms^{(j)}_m(·, h)` solves Mathieu's equation along the imaginary axis (`m ≥ 1`,
`j = 1, …, 4`). -/
lemma p2m_isMathieuSolution_MsJ (j : ℕ) (hj₁ : 1 ≤ j) (hj₄ : j ≤ 4) {m : ℕ} (hm : m ≠ 0)
    {h : ℝ} (hh : 0 < h) :
    IsMathieuSolution (mathieuB m (h ^ 2)) ((h ^ 2 : ℝ) : ℂ)
      (fun t => radialMathieuMs j m (-I * t) h) := by
  have hadm : ModMathieuAdmissible (-(m : ℂ)) (h : ℂ) := by
    simpa using p2m_admissible_intCast (-(m : ℤ)) h
  have hh' : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  have hw := isModMathieuSolution_modMathieuM j hj₁ hj₄ hadm hh'
  have hl : mathieuLambda (-(m : ℂ)) ((h : ℂ) ^ 2) = (mathieuB m (h ^ 2) : ℂ) := by
    rw [p1c_hsq, show -(m : ℂ) = (Int.cast (-(m : ℤ)) : ℂ) by simp, mathieuLambda_intCast,
      mathieuLambdaInt]
    simp [hm]
  rw [hl, p1c_hsq] at hw
  have := p1c_isMathieuSolution_comp hw (c := -I) (by rw [neg_sq, I_sq])
  exact this.const_mul ((-1 : ℂ) ^ m)

/-- `Mc^{(1)}_m(z, h)` is even in `z`. -/
lemma p2m_radialMc_one_neg (m : ℕ) {h : ℝ} (hh : 0 < h) (z : ℂ) :
    radialMathieuMc 1 m (-z) h = radialMathieuMc 1 m z h := by
  have hq : h ^ 2 ≠ 0 := by positivity
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' m
  · have hA : mathieuFourierA (2 * k) (2 * 0) (h ^ 2) ≠ 0 := by
      simpa using p2m_fourierA_even_zero_ne k hq
    have h1 := hasSum_radialMathieuMc_even_cross 1 le_rfl (by norm_num) k 0 hh hA z
    have h2 := hasSum_radialMathieuMc_even_cross 1 le_rfl (by norm_num) k 0 hh hA (-z)
    simp only [neg_neg, mathieuCylExp] at h1 h2
    have e := h2.unique (by convert h1 using 2 with ℓ; ring)
    have h0 : mathieuEpsilon 0 ≠ 0 := by simp [mathieuEpsilon]
    exact mul_left_cancel₀ h0 e
  · have hA : mathieuFourierA (2 * k + 1) (2 * 0 + 1) (h ^ 2) ≠ 0 := by
      simpa using p2m_fourierA_odd_one_ne k hq
    have h1 := hasSum_radialMathieuMc_odd_cross 1 le_rfl (by norm_num) k 0 hh hA z
    have h2 := hasSum_radialMathieuMc_odd_cross 1 le_rfl (by norm_num) k 0 hh hA (-z)
    simp only [neg_neg, mathieuCylExp] at h1 h2
    exact h2.unique (by convert h1 using 2 with ℓ; push_cast; ring)

/-- `J_k(h e^0) = J_k(h)`, natural order. -/
lemma p2m_besselJExp_zero_nat (k : ℕ) (h : ℂ) : besselJExp (k : ℂ) h 0 = besselJ (k : ℂ) h := by
  simpa using p2m_besselJExp_zero k h

/-- `Mc^{(1)}_{2k}(0, h) = (-1)^k A^{2k}_0 / ce_{2k}(π/2)`. -/
lemma p2m_radialMc_one_zero_even (k : ℕ) {h : ℝ} (hh : 0 < h) :
    radialMathieuMc 1 (2 * k) 0 h = (-1 : ℂ) ^ k * mathieuFourierA (2 * k) 0 (h ^ 2) /
      mathieuCe (2 * k) (π / 2) (h ^ 2) := by
  have hq : h ^ 2 ≠ 0 := by positivity
  have hA0 := p2m_fourierA_even_zero_ne k hq
  have hA : mathieuFourierA (2 * k) (2 * 0) (h ^ 2) ≠ 0 := by simpa using hA0
  have h1 := hasSum_radialMathieuMc_even_cross 1 le_rfl (by norm_num) k 0 hh hA 0
  have hk := (p2m_key_even k hh).mul_left ((-1 : ℂ) ^ k * 2 / mathieuFourierA (2 * k) 0 (h ^ 2))
  have e := h1.unique (by
    convert hk using 2 with ℓ
    simp only [neg_zero, mathieuCylExp, Nat.cast_zero, sub_zero, Int.cast_natCast, add_zero,
      mul_zero, p2m_besselJExp_zero_nat]
    field_simp
    ring)
  simp only [mathieuEpsilon, ↓reduceIte] at e
  have hc : mathieuCe (2 * k) (π / 2) (h ^ 2) ≠ 0 := by
    intro h0
    exact p1a2_ce_or_deriv_ne_zero (2 * k) (h ^ 2) ((π / 2 : ℝ) : ℂ) (by push_cast; exact h0)
      (p1a2_deriv_ce_even_half_pi k (h ^ 2))
  field_simp at e ⊢
  linear_combination e

/-- `Mc^{(1)}_{2k+1}(0, h) = -(-1)^k h A^{2k+1}_1 / ce'_{2k+1}(π/2)`. -/
lemma p2m_radialMc_one_zero_odd (k : ℕ) {h : ℝ} (hh : 0 < h) :
    radialMathieuMc 1 (2 * k + 1) 0 h = -((-1 : ℂ) ^ k * h * mathieuFourierA (2 * k + 1) 1 (h ^ 2) /
      deriv (fun w => mathieuCe (2 * k + 1) w (h ^ 2)) (π / 2)) := by
  have hq : h ^ 2 ≠ 0 := by positivity
  have hA1 := p2m_fourierA_odd_one_ne k hq
  have hA : mathieuFourierA (2 * k + 1) (2 * 0 + 1) (h ^ 2) ≠ 0 := by simpa using hA1
  have h1 := hasSum_radialMathieuMc_odd_cross 1 le_rfl (by norm_num) k 0 hh hA 0
  have hk := (p2m_key_odd k hh).mul_left
    ((-1 : ℂ) ^ k * 2 / mathieuFourierA (2 * k + 1) 1 (h ^ 2))
  have e := h1.unique (by
    convert hk using 2 with ℓ
    simp only [neg_zero, mathieuCylExp, Nat.cast_zero, sub_zero, Int.cast_natCast, add_zero,
      mul_zero, zero_add, p2m_besselJExp_zero_nat]
    field_simp
    ring)
  have hc : deriv (fun w => mathieuCe (2 * k + 1) w (h ^ 2)) (π / 2) ≠ 0 := by
    intro h0
    exact p1a2_ce_or_deriv_ne_zero (2 * k + 1) (h ^ 2) ((π / 2 : ℝ) : ℂ)
      (p1a2_ce_odd_half_pi k (h ^ 2)) (by push_cast; exact h0)
  field_simp at e ⊢
  linear_combination e

/-- `√(2/π) ≠ 0` in `ℂ`. -/
theorem p2m_sqrt_two_div_pi_ne : ((Real.sqrt (2 / π) : ℝ) : ℂ) ≠ 0 := by
  have : 0 < Real.sqrt (2 / π) := Real.sqrt_pos.2 (by positivity)
  exact_mod_cast this.ne'

/-- `Mc^{(1)}_m(0, h) g_{e,m}(h) = √(2/π)`. -/
lemma p2m_radialMc_one_zero_mul (m : ℕ) {h : ℝ} (hh : 0 < h) :
    radialMathieuMc 1 m 0 h * mathieuJoinGe m h = Real.sqrt (2 / π) := by
  have hq : h ^ 2 ≠ 0 := by positivity
  have hh' : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  have hP : ∀ k : ℕ, (-1 : ℂ) ^ k * (-1) ^ k = 1 := fun k => by
    rw [← pow_add, ← two_mul, pow_mul]; simp
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' m
  · have hA0 := p2m_fourierA_even_zero_ne k hq
    have hc : mathieuCe (2 * k) (π / 2) (h ^ 2) ≠ 0 := by
      intro h0
      exact p1a2_ce_or_deriv_ne_zero (2 * k) (h ^ 2) ((π / 2 : ℝ) : ℂ) (by push_cast; exact h0)
        (p1a2_deriv_ce_even_half_pi k (h ^ 2))
    rw [p2m_radialMc_one_zero_even k hh, mathieuJoinGe,
      ite_eq_left_of_eq_true _ _ (eq_true (even_two_mul k)),
      show 2 * k / 2 = k by omega]
    field_simp
    linear_combination hP k
  · have hA1 := p2m_fourierA_odd_one_ne k hq
    have hc : deriv (fun w => mathieuCe (2 * k + 1) w (h ^ 2)) (π / 2) ≠ 0 := by
      intro h0
      exact p1a2_ce_or_deriv_ne_zero (2 * k + 1) (h ^ 2) ((π / 2 : ℝ) : ℂ)
        (p1a2_ce_odd_half_pi k (h ^ 2)) (by push_cast; exact h0)
    rw [p2m_radialMc_one_zero_odd k hh, mathieuJoinGe,
      ite_eq_right_of_eq_false _ _ (eq_false (Nat.not_even_two_mul_add_one k)),
      show (2 * k + 1) / 2 = k by omega, pow_succ]
    field_simp
    linear_combination hP k

/-- **DLMF 28.22.1** (proof). -/
theorem p2m_radialMathieuMc_one_eq (m : ℕ) {h : ℝ} (hh : 0 < h) (z : ℂ) :
    radialMathieuMc 1 m z h = Real.sqrt (2 / π) / (mathieuJoinGe m h * mathieuCe m 0 (h ^ 2)) *
      modMathieuCe m z ((h ^ 2 : ℝ) : ℂ) := by
  rw [modMathieuCe_natCast]
  have hG := p2m_isMathieuSolution_McJ 1 le_rfl (by norm_num) m hh
  have hev : ∀ t, radialMathieuMc 1 m (-I * -t) h = radialMathieuMc 1 m (-I * t) h := by
    intro t; rw [show -I * -t = -(-I * t) by ring, p2m_radialMc_one_neg m hh]
  have hrep := p1a2_eq_mul_ce hG hev (I * z)
  simp only [mul_zero] at hrep
  rw [show -I * (I * z) = z by ring_nf; rw [I_sq]; ring] at hrep
  rw [hrep]
  have hv := p2m_radialMc_one_zero_mul m hh
  have hg : mathieuJoinGe m h ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hv; exact p2m_sqrt_two_div_pi_ne hv.symm
  rw [← hv]
  field_simp

/-- `Ms^{(1)}_m(z, h)` is odd in `z`. -/
lemma p2m_radialMs_one_neg {m : ℕ} (hm : m ≠ 0) {h : ℝ} (hh : 0 < h) (z : ℂ) :
    radialMathieuMs 1 m (-z) h = -radialMathieuMs 1 m z h := by
  have hq : h ^ 2 ≠ 0 := by positivity
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' m
  · obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have hB : mathieuFourierB (2 * k + 2) (2 * 0 + 2) (h ^ 2) ≠ 0 := by
      simpa using p2m_fourierB_even_two_ne k hq
    have h1 := hasSum_radialMathieuMs_even_cross 1 le_rfl (by norm_num) k 0 hh hB z
    have h2 := hasSum_radialMathieuMs_even_cross 1 le_rfl (by norm_num) k 0 hh hB (-z)
    simp only [neg_neg, mathieuCylExp] at h1 h2
    rw [show 2 * (k + 1) = 2 * k + 2 by ring]
    exact h2.unique (by convert h1.neg using 2 with ℓ; ring)
  · have hB : mathieuFourierB (2 * k + 1) (2 * 0 + 1) (h ^ 2) ≠ 0 := by
      simpa using p2m_fourierB_odd_one_ne k hq
    have h1 := hasSum_radialMathieuMs_odd_cross 1 le_rfl (by norm_num) k 0 hh hB z
    have h2 := hasSum_radialMathieuMs_odd_cross 1 le_rfl (by norm_num) k 0 hh hB (-z)
    simp only [neg_neg, mathieuCylExp] at h1 h2
    exact h2.unique (by convert h1.neg using 2 with ℓ; ring)

/-- `J_k(h e^{πi/2}) = J_k(ih)`. -/
lemma p2m_besselJExp_half_pi_I (k : ℕ) (h : ℂ) :
    besselJExp (k : ℂ) h (π / 2 * I) = besselJ (k : ℂ) (I * h) := by
  have := p1c_besselJExp_intCast k h (π / 2 * I)
  push_cast at this
  rw [this, Complex.exp_pi_div_two_mul_I, mul_comm]

/-- `J_k(h e^{-πi/2}) = (-1)^k J_k(ih)`. -/
lemma p2m_besselJExp_neg_half_pi_I (k : ℕ) (h : ℂ) :
    besselJExp (k : ℂ) h (-(π / 2 * I)) = (-1 : ℂ) ^ k * besselJ (k : ℂ) (I * h) := by
  have := p1c_besselJExp_intCast k h (-(π / 2 * I))
  push_cast at this
  rw [this, Complex.exp_neg, Complex.exp_pi_div_two_mul_I, Complex.inv_I,
    show (h * -I) = -(I * h) by ring]
  have := Complex.besselJ_int_neg (k : ℤ) (I * h)
  push_cast at this
  rw [this, zpow_natCast]

/-- `Ms^{(1)}_{2k+1}(-πi/2, h) = -(-1)^k i h B^{2k+1}_1 / se'_{2k+1}(0)`. -/
lemma p2m_radialMs_one_odd_val (k : ℕ) {h : ℝ} (hh : 0 < h) :
    radialMathieuMs 1 (2 * k + 1) (-(π / 2 * I)) h = -((-1 : ℂ) ^ k * I * h *
      mathieuFourierB (2 * k + 1) 1 (h ^ 2) /
        deriv (fun w => mathieuSe (2 * k + 1) w (h ^ 2)) 0) := by
  have hq : h ^ 2 ≠ 0 := by positivity
  have hB1 := p2m_fourierB_odd_one_ne k hq
  have hB : mathieuFourierB (2 * k + 1) (2 * 0 + 1) (h ^ 2) ≠ 0 := by simpa using hB1
  have h1 := hasSum_radialMathieuMs_odd_cross 1 le_rfl (by norm_num) k 0 hh hB (-(π / 2 * I))
  have hk := (p2m_key_se_odd k hh).mul_left
    ((-1 : ℂ) ^ k * (-2) / mathieuFourierB (2 * k + 1) 1 (h ^ 2))
  have hP : ∀ ℓ : ℕ, (-1 : ℂ) ^ ℓ * (-1) ^ ℓ = 1 := fun ℓ => by
    rw [← pow_add, ← two_mul, pow_mul]; simp
  have e := h1.unique (by
    convert hk using 2 with ℓ
    simp only [neg_neg, mathieuCylExp, Nat.cast_zero, sub_zero, Int.cast_natCast, add_zero,
      mul_zero, zero_add]
    rw [p2m_besselJExp_half_pi_I, p2m_besselJExp_neg_half_pi_I, p2m_besselJExp_half_pi_I,
      p2m_besselJExp_neg_half_pi_I, pow_succ]
    field_simp
    linear_combination (-2 * mathieuFourierB (2 * k + 1) (2 * ℓ + 1) (h ^ 2) *
      besselJ (ℓ : ℂ) (I * h) * besselJ ((ℓ + 1 : ℕ) : ℂ) (I * h)) * hP ℓ)
  have hs : deriv (fun w => mathieuSe (2 * k + 1) w (h ^ 2)) 0 ≠ 0 := by
    rw [deriv_mathieuSe_zero]; exact_mod_cast (mathieuSeDerivZero_pos _ _).ne'
  rw [e]
  field_simp

/-- `Ms^{(1)}_m = c Se_m` with `c = Ms^{(1)'}_m(0)/se_m'(0)`. -/
lemma p2m_radialMs_one_eq_mul {m : ℕ} (hm : m ≠ 0) {h : ℝ} (hh : 0 < h) (z : ℂ) :
    radialMathieuMs 1 m z h = deriv (fun z => radialMathieuMs 1 m z h) 0 /
      deriv (fun w => mathieuSe m w (h ^ 2)) 0 * modMathieuSe m z ((h ^ 2 : ℝ) : ℂ) := by
  rw [modMathieuSe_natCast hm]
  have hG := p2m_isMathieuSolution_MsJ 1 le_rfl (by norm_num) hm hh
  have hodd : ∀ t, radialMathieuMs 1 m (-I * -t) h = -radialMathieuMs 1 m (-I * t) h := by
    intro t; rw [show -I * -t = -(-I * t) by ring, p2m_radialMs_one_neg hm hh]
  have hrep := p1a2_eq_mul_se hG hodd (I * z)
  rw [show -I * (I * z) = z by ring_nf; rw [I_sq]; ring] at hrep
  rw [hrep]
  have hd : HasDerivAt (fun t => radialMathieuMs 1 m (-I * t) h)
      (deriv (fun z => radialMathieuMs 1 m z h) 0 * -I) 0 := by
    have hdiff := hG.differentiable
    have h1 : DifferentiableAt ℂ (fun z => radialMathieuMs 1 m z h) 0 := by
      have := (hdiff (I * 0)).comp (0 : ℂ) ((differentiableAt_id).const_mul I)
      have e : ((fun t => radialMathieuMs 1 m (-I * t) h) ∘ fun t => I * t) =
          fun z => radialMathieuMs 1 m z h := by
        funext t; simp only [Function.comp]; rw [show -I * (I * t) = t by ring_nf; rw [I_sq]; ring]
      rw [e] at this; simpa using this
    have h1' : HasDerivAt (fun z => radialMathieuMs 1 m z h)
        (deriv (fun z => radialMathieuMs 1 m z h) 0) (-I * 0) := by
      rw [mul_zero]; exact h1.hasDerivAt
    have := h1'.comp (0 : ℂ) ((hasDerivAt_id (0 : ℂ)).const_mul (-I))
    simp only [mul_one] at this
    exact this
  rw [hd.deriv]
  ring

/-- **DLMF 28.22.2** (proof). -/
theorem p2m_radialMathieuMs_one_eq {m : ℕ} (hm : m ≠ 0) {h : ℝ} (hh : 0 < h) (z : ℂ) :
    radialMathieuMs 1 m z h = Real.sqrt (2 / π) /
      (mathieuJoinGo m h * deriv (fun x => mathieuSe m x (h ^ 2)) 0) *
      modMathieuSe m z ((h ^ 2 : ℝ) : ℂ) := by
  have hq : h ^ 2 ≠ 0 := by positivity
  have hh' : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  have hs0 : deriv (fun w => mathieuSe m w (h ^ 2)) 0 ≠ 0 := by
    rw [deriv_mathieuSe_zero]; exact_mod_cast (mathieuSeDerivZero_pos _ _).ne'
  have hP : ∀ k : ℕ, (-1 : ℂ) ^ k * (-1) ^ k = 1 := fun k => by
    rw [← pow_add, ← two_mul, pow_mul]; simp
  have hrep := p2m_radialMs_one_eq_mul hm hh
  rw [hrep z]
  congr 1
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' m
  · obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [show 2 * (k + 1) = 2 * k + 2 by ring] at hs0 ⊢
    have hB2 := p2m_fourierB_even_two_ne k hq
    have hc : deriv (fun w => mathieuSe (2 * k + 2) w (h ^ 2)) (π / 2) ≠ 0 := by
      intro h0
      exact p1a2_se_or_deriv_ne_zero (2 * k + 2) (h ^ 2) ((π / 2 : ℝ) : ℂ)
        (p1a2_se_even_half_pi k (h ^ 2)) (by push_cast; exact h0)
    rw [p2m_radialMs_one_even_deriv k hh, mathieuJoinGo,
      ite_eq_right_of_eq_false _ _ (eq_false (by
        rw [Nat.not_odd_iff_even]; exact ⟨k + 1, by ring⟩)),
      show (2 * k + 2 - 2) / 2 = k by omega, pow_succ]
    field_simp
    linear_combination hP k
  · have hB1 := p2m_fourierB_odd_one_ne k hq
    have hc : mathieuSe (2 * k + 1) (π / 2) (h ^ 2) ≠ 0 := by
      intro h0
      exact p1a2_se_or_deriv_ne_zero (2 * k + 1) (h ^ 2) ((π / 2 : ℝ) : ℂ)
        (by push_cast; exact h0) (p1a2_deriv_se_odd_half_pi k (h ^ 2))
    have hv := hrep (-(π / 2 * I))
    rw [p2m_radialMs_one_odd_val k hh, modMathieuSe_natCast (by omega),
      show I * -(↑π / 2 * I) = ((π / 2 : ℝ) : ℂ) by push_cast; ring_nf; rw [I_sq]; ring] at hv
    push_cast at hv
    rw [mathieuJoinGo, ite_eq_left_of_eq_true _ _ (eq_true (odd_two_mul_add_one k)),
      show (2 * k + 1) / 2 = k by omega]
    field_simp at hv ⊢
    linear_combination (-1 : ℂ) ^ k * hv + (h * mathieuFourierB (2 * k + 1) 1 (h ^ 2)) * hP k

/-! ### The monodromy `z ↦ z + πi` and 28.22.3–28.22.4 -/

/-- Monodromy of the continued `Y_μ` under `z ↦ z + πi`, every order:
`Y_μ(h e^{z+πi}) = e^{-iμπ} Y_μ(h e^z) + 2i cos(μπ) J_μ(h e^z)`. -/
lemma p2m_besselYExp_add_pi_I (μ : ℂ) {h : ℂ} (hh : h ≠ 0) (z : ℂ) :
    besselYExp μ h (z + π * I) = Complex.exp (-(μ * π * I)) * besselYExp μ h z +
      2 * I * Complex.cos (μ * π) * besselJExp μ h z := by
  have hc := p2m_continuousAt_besselYExp_order hh
  have hJ := p2m_differentiable_besselJExp_order hh
  refine DLMF.Confluent.eq_of_continuousAt_of_integerComplement
    (f := fun μ => besselYExp μ h (z + π * I))
    (g := fun μ => Complex.exp (-(μ * π * I)) * besselYExp μ h z +
      2 * I * Complex.cos (μ * π) * besselJExp μ h z)
    (hc _ _) (((by fun_prop : ContinuousAt (fun μ : ℂ => Complex.exp (-(μ * π * I))) μ).mul
      (hc z μ)).add ((by fun_prop : ContinuousAt (fun μ : ℂ => 2 * I * Complex.cos (μ * π)) μ).mul
        (hJ z μ).continuousAt)) (fun c hc' => ?_)
  have hk := DLMF.Confluent.forall_of_mem_integerComplement hc'
  have hs := DLMF.Bessel.sin_mul_pi_ne_zero hk
  have e : Complex.exp (2 * (π * I)) = 1 := by
    rw [Complex.exp_eq_one_iff]; exact ⟨1, by ring⟩
  rw [p2m_besselYExp_of_not_int hk, p2m_besselYExp_of_not_int hk]
  simp only [p2m_besselDExp]
  rw [m28c_besselJExp_add c h z _ e, m28c_besselJExp_add (-c) h z _ e]
  have hsin : 2 * I * Complex.sin (c * π) =
      Complex.exp (c * (π * I)) - Complex.exp (-(c * π * I)) := by
    rw [Complex.sin]; ring_nf; rw [I_sq]; ring_nf
  field_simp
  rw [show c * (π * I) = c * π * I by ring] at hsin
  linear_combination (-(besselJExp c h z * Complex.cos (c * π))) * hsin

/-- Integer-order case: `Y_k(h e^{z+πi}) = (-1)^k (Y_k(h e^z) + 2i J_k(h e^z))`. -/
lemma p2m_besselYExp_add_pi_I_int (k : ℤ) {h : ℂ} (hh : h ≠ 0) (z : ℂ) :
    besselYExp k h (z + π * I) = (-1 : ℂ) ^ k * (besselYExp k h z + 2 * I * besselJExp k h z) := by
  rw [p2m_besselYExp_add_pi_I _ hh, DLMF.Bessel.cos_int_mul_pi_complex,
    show -((k : ℂ) * π * I) = -(I * k * π) by ring, p1c_exp_neg_I_int_mul_pi]
  ring

/-- Term-wise monodromy `z ↦ z + πi` of the integer-order series 28.24.1 with `j = 2`. -/
lemma p2m_modMathieuTerm_two_add_pi_I (m : ℤ) {h : ℂ} (hh : h ≠ 0) (z : ℂ) (n ℓ : ℤ) :
    modMathieuTerm 2 m (z + π * I) h n ℓ =
      (-1 : ℂ) ^ m * (modMathieuTerm 2 m z h n ℓ + 2 * I * modMathieuTerm 1 m z h n ℓ) := by
  have e : Complex.exp (2 * -(π * I)) = 1 := by
    rw [Complex.exp_eq_one_iff]; exact ⟨-1, by push_cast; ring⟩
  have hJ := m28c_besselJExp_add ((ℓ - n : ℤ) : ℂ) h (-z) _ e
  have hY := p2m_besselYExp_add_pi_I_int (m + n + ℓ) hh z
  simp only [modMathieuTerm, mathieuCylExp]
  rw [show -(z + π * I) = -z + -(π * I) by ring, hJ,
    show (m : ℂ) + n + ℓ = ((m + n + ℓ : ℤ) : ℂ) by push_cast; ring, hY,
    show ((ℓ - n : ℤ) : ℂ) * -(π * I) = -(I * ((ℓ - n : ℤ) : ℂ) * π) by ring,
    p1c_exp_neg_I_int_mul_pi]
  have hP : (-1 : ℂ) ^ (ℓ - n) * (-1) ^ (m + n + ℓ) = (-1) ^ m := by
    rw [← zpow_add₀ (by norm_num), show ℓ - n + (m + n + ℓ) = m + 2 * ℓ by ring,
      zpow_add₀ (by norm_num), zpow_mul]
    simp
  linear_combination (-1 : ℂ) ^ ℓ * mathieuMeCoeff (m : ℂ) (h ^ 2) ℓ *
    besselJExp ((ℓ - n : ℤ) : ℂ) h (-z) * (besselYExp ((m + n + ℓ : ℤ) : ℂ) h z +
      2 * I * besselJExp ((m + n + ℓ : ℤ) : ℂ) h z) * hP

/-- Monodromy of `M^{(2)}_k` for integer `k`, `h > 0`:
`M^{(2)}_k(z + πi) = (-1)^k (M^{(2)}_k(z) + 2i M^{(1)}_k(z))` (DLMF 28.20.25 at integer order). -/
lemma p2m_modMathieuM_two_add_pi_I (k : ℤ) {h : ℝ} (hh : 0 < h) (z : ℂ) :
    modMathieuM 2 k (z + π * I) h =
      (-1 : ℂ) ^ k * (modMathieuM 2 k z h + 2 * I * modMathieuM 1 k z h) := by
  have hadm : ModMathieuAdmissible (k : ℂ) (h : ℂ) := by
    exact p2m_admissible_intCast k h
  have hh' : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  set n := modMathieuIndex (k : ℂ) h
  have h1 := summable_modMathieuTerm 1 le_rfl (by norm_num) hadm hh' n z
  have h2 := summable_modMathieuTerm 2 (by norm_num) (by norm_num) hadm hh' n z
  simp only [modMathieuM]
  rw [tsum_congr (p2m_modMathieuTerm_two_add_pi_I k hh' z n), tsum_mul_left,
    h2.tsum_add (h1.mul_left _), tsum_mul_left]
  ring

/-- `Mc^{(2)}_m(z + πi) = (-1)^m (Mc^{(2)}_m(z) + 2i Mc^{(1)}_m(z))`. -/
lemma p2m_radialMc_two_add_pi_I (m : ℕ) {h : ℝ} (hh : 0 < h) (z : ℂ) :
    radialMathieuMc 2 m (z + π * I) h =
      (-1 : ℂ) ^ m * (radialMathieuMc 2 m z h + 2 * I * radialMathieuMc 1 m z h) := by
  have := p2m_modMathieuM_two_add_pi_I (m : ℤ) hh z
  simp only [Int.cast_natCast, zpow_natCast] at this
  exact this

/-- `Ms^{(2)}_m(z + πi) = (-1)^m (Ms^{(2)}_m(z) + 2i Ms^{(1)}_m(z))`. -/
lemma p2m_radialMs_two_add_pi_I (m : ℕ) {h : ℝ} (hh : 0 < h) (z : ℂ) :
    radialMathieuMs 2 m (z + π * I) h =
      (-1 : ℂ) ^ m * (radialMathieuMs 2 m z h + 2 * I * radialMathieuMs 1 m z h) := by
  have := p2m_modMathieuM_two_add_pi_I (-(m : ℤ)) hh z
  simp only [Int.cast_neg, Int.cast_natCast, zpow_neg, zpow_natCast] at this
  simp only [radialMathieuMs, this]
  have hP : ((-1 : ℂ) ^ m)⁻¹ = (-1) ^ m := by
    rw [← inv_pow, inv_neg, inv_one]
  rw [hP]; ring

/-- `fe_n(0, q) = 0` for real `q ≠ 0`. -/
lemma p2m_mathieuFe_zero (n : ℕ) {q : ℝ} (hq : q ≠ 0) : mathieuFe n 0 q = 0 := by
  simp [mathieuFe, hq, (mathieuWII_spec _ _).2.1]

/-- `fe_n'(0, q) ≠ 0` for real `q ≠ 0`. -/
lemma p2m_deriv_mathieuFe_zero_ne (n : ℕ) {q : ℝ} (hq : q ≠ 0) :
    deriv (fun z => mathieuFe n z q) 0 ≠ 0 := by
  rw [show (fun z => mathieuFe n z q) =
      fun z => (mathieuFeDerivZero n q : ℂ) * mathieuWII (mathieuA n q) q z from
    funext fun z => by simp [mathieuFe, hq],
    deriv_const_mul _ ((isMathieuSolution_mathieuWII _ _).differentiable 0),
    (mathieuWII_spec _ _).2.2, mul_one]
  intro h0
  apply mathieuFeC_ne_zero n hq
  simp [mathieuFeC, hq, h0]

/-- **DLMF 28.22.3** (proof). -/
theorem p2m_radialMathieuMc_two_eq (m : ℕ) {h : ℝ} (hh : 0 < h) (z : ℂ) :
    radialMathieuMc 2 m z h = Real.sqrt (2 / π) / (mathieuJoinGe m h * mathieuCe m 0 (h ^ 2)) *
      (-mathieuJoinFe m h * modMathieuCe m z ((h ^ 2 : ℝ) : ℂ) +
        2 / (π * mathieuFeC m (h ^ 2)) * modMathieuFe m z (h ^ 2)) := by
  have hq : h ^ 2 ≠ 0 := by positivity
  have hnq : ¬ (m = 0 ∧ h ^ 2 = 0) := fun h' => hq h'.2
  have hG := p2m_isMathieuSolution_McJ 2 (by norm_num) (by norm_num) m hh
  have hce := isMathieuSolution_mathieuCe m (h ^ 2)
  have hfe := isMathieuSolution_mathieuFe hnq
  have hC := mathieuFeC_ne_zero m hq
  have hce0 : mathieuCe m 0 (h ^ 2) ≠ 0 := by
    rw [mathieuCe_zero]; exact_mod_cast (mathieuCeZero_pos m _).ne'
  have hfe0 := p2m_mathieuFe_zero m hq
  have hW : mathieuCe m 0 (h ^ 2) * deriv (fun z => mathieuFe m z (h ^ 2)) 0 -
      deriv (fun z => mathieuCe m z (h ^ 2)) 0 * mathieuFe m 0 (h ^ 2) ≠ 0 := by
    rw [hfe0, mul_zero, sub_zero]; exact mul_ne_zero hce0 (p2m_deriv_mathieuFe_zero_ne m hq)
  have hrep := congrFun (p2x_eq_comb_of_wronskian hce hfe hW hG)
  obtain ⟨α, β, hαβ⟩ : ∃ α β : ℂ, ∀ t, radialMathieuMc 2 m (-I * t) h =
      α * mathieuCe m t (h ^ 2) + β * mathieuFe m t (h ^ 2) := ⟨_, _, fun t => hrep t⟩
  have h0 := hαβ 0
  rw [hfe0, mul_zero, mul_zero, add_zero] at h0
  have hπ := hαβ (-π)
  rw [show -I * -(π : ℂ) = 0 + π * I by ring, p2m_radialMc_two_add_pi_I m hh 0] at hπ
  have hP : (-1 : ℂ) ^ m * (-1) ^ m = 1 := by rw [← mul_pow]; simp
  have hceπ : mathieuCe m (-π) (h ^ 2) = (-1) ^ m * mathieuCe m 0 (h ^ 2) := by
    have := p2m_mathieuCe_add_pi m (-π) (h ^ 2)
    rw [neg_add_cancel] at this
    rw [this, ← mul_assoc, hP, one_mul]
  have hf0 : mathieuFeF m 0 (h ^ 2) = 0 := by
    have := p1a1_mathieuFeF_neg hq hC 0
    rw [neg_zero] at this
    linear_combination this / 2
  have hfπ : mathieuFeF m (-π) (h ^ 2) = 0 := by
    have := p1a1_mathieuFeF_add_pi hq hC (-π)
    rw [neg_add_cancel, hf0] at this
    have := congrArg (fun x => (-1 : ℂ) ^ m * x) this
    simp only [mul_zero, ← mul_assoc, hP, one_mul] at this
    exact this.symm
  rw [mathieuFe_eq hC, hfπ, hceπ, h0] at hπ
  have hv := p2m_radialMc_one_zero_mul m hh
  have hg : mathieuJoinGe m h ≠ 0 := by
    intro h0'; rw [h0', mul_zero] at hv; exact p2m_sqrt_two_div_pi_ne hv.symm
  have hβ : β = -2 * I * radialMathieuMc 1 m 0 h / (π * mathieuFeC m (h ^ 2) *
      mathieuCe m 0 (h ^ 2)) := by
    have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have hπ' : α * mathieuCe m 0 (h ^ 2) + 2 * I * radialMathieuMc 1 m 0 h =
        α * mathieuCe m 0 (h ^ 2) - β * mathieuFeC m (h ^ 2) * π * mathieuCe m 0 (h ^ 2) := by
      linear_combination (-1 : ℂ) ^ m * hπ - (2 * I * radialMathieuMc 1 m 0 h +
        β * mathieuFeC m (h ^ 2) * π * mathieuCe m 0 (h ^ 2)) * hP
    field_simp
    linear_combination hπ'
  have hα : α = radialMathieuMc 2 m 0 h / mathieuCe m 0 (h ^ 2) := by
    field_simp; exact h0.symm
  have hM1 : radialMathieuMc 1 m 0 h = Real.sqrt (2 / π) / mathieuJoinGe m h := by
    field_simp; exact hv
  have hs : (Real.sqrt (2 / π) : ℂ) * Real.sqrt (π / 2) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.sqrt_mul (by positivity)]
    rw [show 2 / π * (π / 2) = 1 by field_simp]; simp
  have hz := hαβ (I * z)
  rw [show -I * (I * z) = z by ring_nf; rw [I_sq]; ring] at hz
  rw [hz, modMathieuCe_natCast, modMathieuFe, mathieuJoinFe, hβ, hα, hM1]
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp
  linear_combination (-(radialMathieuMc 2 m 0 h * mathieuCe m (I * z) (h ^ 2) *
    mathieuJoinGe m h * π * mathieuFeC m (h ^ 2))) * hs

/-- `ge_n(0, q) ≠ 0` and `ge_n'(0, q) = 0` for real `q ≠ 0`, `n ≥ 1`. -/
lemma p2m_mathieuGe_zero {n : ℕ} (hn : n ≠ 0) {q : ℝ} (hq : q ≠ 0) :
    mathieuGe n 0 q ≠ 0 ∧ deriv (fun z => mathieuGe n z q) 0 = 0 := by
  have hS := mathieuGeS_ne_zero hn hq
  have e : (fun z => mathieuGe n z q) =
      fun z => (mathieuGeZero n q : ℂ) * mathieuWI (mathieuB n q) q z :=
    funext fun z => by simp [mathieuGe]
  refine ⟨?_, ?_⟩
  · rw [congrFun e 0, (mathieuWI_spec _ _).2.1, mul_one]
    intro h0; apply hS; simp [mathieuGeS, h0]
  · rw [e, deriv_const_mul _ ((isMathieuSolution_mathieuWI _ _).differentiable 0),
      (mathieuWI_spec _ _).2.2, mul_zero]

/-- `g_{o,m}(h) ≠ 0` for `h > 0`, `m ≥ 1`. -/
lemma p2m_mathieuJoinGo_ne {m : ℕ} (hm : m ≠ 0) {h : ℝ} (hh : 0 < h) :
    mathieuJoinGo m h ≠ 0 := by
  have hq : h ^ 2 ≠ 0 := by positivity
  have hh' : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' m
  · obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [show 2 * (k + 1) = 2 * k + 2 by ring]
    have hB2 := p2m_fourierB_even_two_ne k hq
    have hc : deriv (fun w => mathieuSe (2 * k + 2) w (h ^ 2)) (π / 2) ≠ 0 := by
      intro h0
      exact p1a2_se_or_deriv_ne_zero (2 * k + 2) (h ^ 2) ((π / 2 : ℝ) : ℂ)
        (p1a2_se_even_half_pi k (h ^ 2)) (by push_cast; exact h0)
    rw [mathieuJoinGo, ite_eq_right_of_eq_false _ _ (eq_false (by
        rw [Nat.not_odd_iff_even]; exact ⟨k + 1, by ring⟩))]
    have := p2m_sqrt_two_div_pi_ne
    exact div_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) this) hc)
      (mul_ne_zero (pow_ne_zero _ hh') hB2)
  · have hB1 := p2m_fourierB_odd_one_ne k hq
    have hc : mathieuSe (2 * k + 1) (π / 2) (h ^ 2) ≠ 0 := by
      intro h0
      exact p1a2_se_or_deriv_ne_zero (2 * k + 1) (h ^ 2) ((π / 2 : ℝ) : ℂ)
        (by push_cast; exact h0) (p1a2_deriv_se_odd_half_pi k (h ^ 2))
    rw [mathieuJoinGo, ite_eq_left_of_eq_true _ _ (eq_true (odd_two_mul_add_one k))]
    have := p2m_sqrt_two_div_pi_ne
    exact div_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) this) hc)
      (mul_ne_zero hh' hB1)

/-- **DLMF 28.22.4** (proof). -/
theorem p2m_radialMathieuMs_two_eq {m : ℕ} (hm : m ≠ 0) {h : ℝ} (hh : 0 < h) (z : ℂ) :
    radialMathieuMs 2 m z h = Real.sqrt (2 / π) /
      (mathieuJoinGo m h * deriv (fun x => mathieuSe m x (h ^ 2)) 0) *
      (-mathieuJoinFo m h * modMathieuSe m z ((h ^ 2 : ℝ) : ℂ) -
        2 / (π * mathieuGeS m (h ^ 2)) * modMathieuGe m z (h ^ 2)) := by
  have hq : h ^ 2 ≠ 0 := by positivity
  have hG := p2m_isMathieuSolution_MsJ 2 (by norm_num) (by norm_num) hm hh
  have hse := isMathieuSolution_mathieuSe m (h ^ 2)
  have hge := isMathieuSolution_mathieuGe m (h ^ 2)
  have hS := mathieuGeS_ne_zero hm hq
  obtain ⟨hge0, hge0'⟩ := p2m_mathieuGe_zero hm hq
  have hse0 : mathieuSe m 0 (h ^ 2) = 0 := by simp [mathieuSe, (mathieuWII_spec _ _).2.1]
  have hs0 : deriv (fun w => mathieuSe m w (h ^ 2)) 0 ≠ 0 := by
    rw [deriv_mathieuSe_zero]; exact_mod_cast (mathieuSeDerivZero_pos _ _).ne'
  have hW : mathieuSe m 0 (h ^ 2) * deriv (fun z => mathieuGe m z (h ^ 2)) 0 -
      deriv (fun z => mathieuSe m z (h ^ 2)) 0 * mathieuGe m 0 (h ^ 2) ≠ 0 := by
    rw [hse0, zero_mul, zero_sub, neg_ne_zero]; exact mul_ne_zero hs0 hge0
  have hrep := p2x_eq_comb_of_wronskian hse hge hW hG
  obtain ⟨α, β, hαβ⟩ : ∃ α β : ℂ, (fun t => radialMathieuMs 2 m (-I * t) h) =
      fun t => α * mathieuSe m t (h ^ 2) + β * mathieuGe m t (h ^ 2) := ⟨_, _, hrep⟩
  -- the derivative at `0`
  have hD : Differentiable ℂ fun z => radialMathieuMs 2 m z h := by
    have := hG.differentiable.comp (differentiable_id.const_mul I)
    convert this using 1
    funext t; simp only [Function.comp, id]
    rw [show -I * (I * t) = t by ring_nf; rw [I_sq]; ring]
  have hd : HasDerivAt (fun t => radialMathieuMs 2 m (-I * t) h)
      (deriv (fun z => radialMathieuMs 2 m z h) 0 * -I) 0 := by
    have h1' : HasDerivAt (fun z => radialMathieuMs 2 m z h)
        (deriv (fun z => radialMathieuMs 2 m z h) 0) (-I * 0) := by
      rw [mul_zero]; exact (hD 0).hasDerivAt
    have := h1'.comp (0 : ℂ) ((hasDerivAt_id (0 : ℂ)).const_mul (-I))
    simp only [mul_one] at this
    exact this
  have hd2 : HasDerivAt (fun t => α * mathieuSe m t (h ^ 2) + β * mathieuGe m t (h ^ 2))
      (α * deriv (fun w => mathieuSe m w (h ^ 2)) 0 +
        β * deriv (fun w => mathieuGe m w (h ^ 2)) 0) 0 :=
    ((hse.differentiable 0).hasDerivAt.const_mul α).add
      ((hge.differentiable 0).hasDerivAt.const_mul β)
  rw [hαβ] at hd
  have hα0 := hd.unique hd2
  rw [hge0', mul_zero, add_zero] at hα0
  -- the monodromy
  have hMs1 := p2m_radialMathieuMs_one_eq hm hh
  set K := Real.sqrt (2 / π) / (mathieuJoinGo m h * deriv (fun x => mathieuSe m x (h ^ 2)) 0)
    with hK
  have hP : (-1 : ℂ) ^ m * (-1) ^ m = 1 := by rw [← mul_pow]; simp
  have hshift : ∀ t, (-1 : ℂ) ^ m * (α * mathieuSe m t (h ^ 2) + β * mathieuGe m t (h ^ 2) +
      2 * I * (K * (-I * mathieuSe m t (h ^ 2)))) =
      (-1) ^ m * (α * mathieuSe m t (h ^ 2) + β * (mathieuGe m t (h ^ 2) -
        π * mathieuGeS m (h ^ 2) * mathieuSe m t (h ^ 2))) := by
    intro t
    have e1 := congrFun hαβ (t - π)
    have e2 := congrFun hαβ t
    have e3 := hMs1 (-I * t)
    rw [show -I * ((t : ℂ) - π) = -I * t + π * I by ring, p2m_radialMs_two_add_pi_I m hh,
      e2, e3, modMathieuSe_natCast hm,
      show I * (-I * t) = t by ring_nf; rw [I_sq]; ring] at e1
    have hseπ : mathieuSe m (t - π) (h ^ 2) = (-1) ^ m * mathieuSe m t (h ^ 2) := by
      have := p2m_mathieuSe_add_pi hm (t - π) (h ^ 2)
      rw [sub_add_cancel] at this
      rw [this, ← mul_assoc, hP, one_mul]
    have hgπ : mathieuGeG m (t - π) (h ^ 2) = (-1) ^ m * mathieuGeG m t (h ^ 2) := by
      have := p1a1_mathieuGeG_add_pi hm hS (t - π)
      rw [sub_add_cancel] at this
      rw [this, ← mul_assoc, hP, one_mul]
    have hgeπ : mathieuGe m (t - π) (h ^ 2) = (-1) ^ m * (mathieuGe m t (h ^ 2) -
        π * mathieuGeS m (h ^ 2) * mathieuSe m t (h ^ 2)) := by
      rw [mathieuGe_eq hS, mathieuGe_eq hS, hseπ, hgπ]; ring
    rw [hseπ, hgeπ] at e1
    rw [e1]
    ring
  have hβ : β * (π * mathieuGeS m (h ^ 2)) = -2 * K := by
    by_contra hne
    have hz : ∀ t, mathieuSe m t (h ^ 2) = 0 := by
      intro t
      have h2 : (β * (π * mathieuGeS m (h ^ 2)) + 2 * K) * mathieuSe m t (h ^ 2) = 0 := by
        linear_combination (norm := ring_nf) (-1 : ℂ) ^ m * hshift t -
          ((β * (π * mathieuGeS m (h ^ 2)) + 2 * K) * mathieuSe m t (h ^ 2)) * hP +
          (2 * K * mathieuSe m t (h ^ 2) * (-1 : ℂ) ^ m * (-1 : ℂ) ^ m) * I_sq
      refine (mul_eq_zero.mp h2).resolve_left ?_
      intro h3; apply hne; linear_combination h3
    apply hs0
    rw [show (fun w => mathieuSe m w (h ^ 2)) = fun _ => 0 from funext hz, deriv_const]
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hg := p2m_mathieuJoinGo_ne hm hh
  have hα : α = deriv (fun z => radialMathieuMs 2 m z h) 0 * -I /
      deriv (fun w => mathieuSe m w (h ^ 2)) 0 := by
    field_simp; linear_combination -hα0
  have hβ' : β = -2 * K / (π * mathieuGeS m (h ^ 2)) := by
    field_simp; linear_combination hβ
  have hs : (Real.sqrt (2 / π) : ℂ) * Real.sqrt (π / 2) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.sqrt_mul (by positivity)]
    rw [show 2 / π * (π / 2) = 1 by field_simp]; simp
  have hz := congrFun hαβ (I * z)
  rw [show -I * (I * z) = z by ring_nf; rw [I_sq]; ring] at hz
  rw [hz, modMathieuSe_natCast hm, modMathieuGe, mathieuJoinFo, hα, hβ', hK]
  field_simp
  linear_combination (deriv (fun z => radialMathieuMs 2 m z h) 0 * I *
    mathieuSe m (I * z) (h ^ 2) * mathieuJoinGo m h * π * mathieuGeS m (h ^ 2)) * hs

end DLMF.Mathieu

end
