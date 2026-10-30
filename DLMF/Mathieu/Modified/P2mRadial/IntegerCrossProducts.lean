/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Mathieu.Modified.P2mRadial.SeriesEquation

/-!
# Integer-order Mathieu Bessel cross-product expansions

Integer-order Bessel cross-product expansions identify the radial Mathieu solution families.

Source references and common attribution are retained in
`DLMF.Mathieu.Modified.P2mRadial`.
-/

@[expose] public noncomputable section

open Complex Set Filter

open scoped Topology Real Nat

namespace DLMF.Mathieu

/-! ### Integer-order cross-product expansions (28.24.2–28.24.5) -/

/-- `Y_{-μ} = cos(μπ) Y_μ + sin(μπ) J_μ` for the continued functions, every order. -/
lemma p2m_besselYExp_neg (μ : ℂ) {h : ℂ} (hh : h ≠ 0) (z : ℂ) :
    besselYExp (-μ) h z = Complex.cos (μ * π) * besselYExp μ h z +
      Complex.sin (μ * π) * besselJExp μ h z := by
  have hc := p2m_continuousAt_besselYExp_order hh z
  have hJ := p2m_differentiable_besselJExp_order hh z
  refine DLMF.Confluent.eq_of_continuousAt_of_integerComplement
    (f := fun μ => besselYExp (-μ) h z)
    (g := fun μ => Complex.cos (μ * π) * besselYExp μ h z +
      Complex.sin (μ * π) * besselJExp μ h z)
    ((hc _).comp (by fun_prop : ContinuousAt (fun μ : ℂ => -μ) μ))
    (((by fun_prop : ContinuousAt (fun μ : ℂ => Complex.cos (μ * π)) μ).mul (hc μ)).add
      ((by fun_prop : ContinuousAt (fun μ : ℂ => Complex.sin (μ * π)) μ).mul
        (hJ μ).continuousAt)) (fun c hc' => ?_)
  have hk := DLMF.Confluent.forall_of_mem_integerComplement hc'
  have hk' : ∀ k : ℤ, -c ≠ k := fun k h' => hk (-k) (by push_cast; linear_combination -h')
  have hs := DLMF.Bessel.sin_mul_pi_ne_zero hk
  rw [p2m_besselYExp_of_not_int hk', p2m_besselYExp_of_not_int hk]
  simp only [p2m_besselDExp, neg_neg, neg_mul, Complex.cos_neg, Complex.sin_neg]
  field_simp
  have := Complex.sin_sq_add_cos_sq (c * π)
  linear_combination (-besselJExp c h z) * this

/-- `Y_{-k} = (-1)^k Y_k` for integer `k`. -/
lemma p2m_besselYExp_neg_intCast (k : ℤ) {h : ℂ} (hh : h ≠ 0) (z : ℂ) :
    besselYExp ((-k : ℤ) : ℂ) h z = (-1 : ℂ) ^ k * besselYExp k h z := by
  rw [Int.cast_neg, p2m_besselYExp_neg _ hh, DLMF.Bessel.cos_int_mul_pi_complex,
    Complex.sin_int_mul_pi, zero_mul, add_zero]

/-- For an integer `k`, `𝒞^{(j)}_{-k}(h e^z) = (-1)^k 𝒞^{(j)}_k(h e^z)`. -/
lemma p2m_mathieuCylExp_neg_intCast (j : ℕ) (hj₁ : 1 ≤ j) (hj₄ : j ≤ 4) (k : ℤ) {h : ℂ}
    (hh : h ≠ 0) (z : ℂ) :
    mathieuCylExp j ((-k : ℤ) : ℂ) h z = (-1 : ℂ) ^ k * mathieuCylExp j k h z := by
  have hJ := p1c_besselJExp_neg_intCast k h z
  have hY := p2m_besselYExp_neg_intCast k hh z
  interval_cases j <;> simp only [mathieuCylExp, hJ, hY] <;> ring

/-- `ce_N(z + π) = (-1)^N ce_N(z)`. -/
theorem p2m_mathieuCe_add_pi (N : ℕ) (z : ℂ) (q : ℝ) :
    mathieuCe N (z + π) q = (-1 : ℂ) ^ N * mathieuCe N z q := by
  rcases Nat.even_or_odd' N with ⟨t, rfl | rfl⟩
  · rw [mathieuCe_even_add_pi, pow_mul]; simp
  · rw [mathieuCe_odd_add_pi, pow_succ, pow_mul]; simp

/-- `se_N(z + π) = (-1)^N se_N(z)`, `N ≥ 1`. -/
theorem p2m_mathieuSe_add_pi {N : ℕ} (hN : N ≠ 0) (z : ℂ) (q : ℝ) :
    mathieuSe N (z + π) q = (-1 : ℂ) ^ N * mathieuSe N z q := by
  rcases Nat.even_or_odd' N with ⟨t, rfl | rfl⟩
  · obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
    rw [show 2 * (s + 1) = 2 * s + 2 by ring, mathieuSe_even_add_pi, pow_add, pow_mul]; simp
  · rw [mathieuSe_odd_add_pi, pow_succ, pow_mul]; simp

/-- For `K ∈ ℤ`, `cos(K(x + π)) = (-1)^K cos(Kx)`. -/
theorem p2m_cos_add_int_mul_pi (K : ℤ) (x : ℂ) :
    Complex.cos (K * (x + π)) = (-1 : ℂ) ^ K * Complex.cos (K * x) := by
  rw [mul_add, Complex.cos_add, DLMF.Bessel.cos_int_mul_pi_complex,
    Complex.sin_int_mul_pi]; ring

/-- For `K ∈ ℤ`, `sin(K(x + π)) = (-1)^K sin(Kx)`. -/
theorem p2m_sin_add_int_mul_pi (K : ℤ) (x : ℂ) :
    Complex.sin (K * (x + π)) = (-1 : ℂ) ^ K * Complex.sin (K * x) := by
  rw [mul_add, Complex.sin_add, DLMF.Bessel.cos_int_mul_pi_complex,
    Complex.sin_int_mul_pi]; ring

/-- If `K ≡ N (mod 2)` then `(-1)^N (-1)^K = 1`. -/
lemma p2m_negOnePow_mul_eq_one {N : ℕ} {K : ℤ} (hK : ∃ k : ℤ, K = N + 2 * k) :
    (-1 : ℂ) ^ N * (-1 : ℂ) ^ K = 1 := by
  obtain ⟨k, rfl⟩ := hK
  rw [← zpow_natCast, ← zpow_add₀ (by norm_num), show (N : ℤ) + (N + 2 * k) = 2 * (N + k) by
    ring, zpow_mul]
  simp

/-- An integrand `f` with `f(x + π) = f(x)` and `f(π - x) = -f(x)` integrates to `0` over
`[0, π]`. -/
lemma p2m_integral_eq_zero_of_reflect {f : ℝ → ℂ} (hf : ∀ x, f (π - x) = -f x) :
    ∫ x in (0 : ℝ)..π, f x = 0 := by
  have h1 : ∫ x in (0 : ℝ)..π, f x = ∫ x in (0 : ℝ)..π, f (π - x) := by
    rw [intervalIntegral.integral_comp_sub_left]; simp
  simp only [hf, intervalIntegral.integral_neg] at h1
  linear_combination h1 / 2

/-- Doubling the interval for a `π`-periodic integrand. -/
lemma p2m_integral_two_pi {f : ℝ → ℂ} (hc : Continuous f) (hf : ∀ x, f (x + π) = f x) :
    ∫ x in (0 : ℝ)..2 * π, f x = 2 * ∫ x in (0 : ℝ)..π, f x := by
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := π) (hc.intervalIntegrable _ _)
    (hc.intervalIntegrable _ _)]
  have : ∫ x in π..2 * π, f x = ∫ x in (0 : ℝ)..π, f x := by
    have e := intervalIntegral.integral_comp_add_right f (a := 0) (b := π) π
    simp only [hf, zero_add] at e
    rw [show (2 : ℝ) * π = π + π by ring]; exact e.symm
  rw [this]; ring

/-- The integer-order coefficients `c^N_{2k}` of `me_N = √2 ce_N` (`N ≥ 0`) as cosine integrals:
`c^N_{2k}(q) = √2/(2π) ∫₀^{2π} ce_N(x) cos((N+2k)x) dx`. -/
theorem p2m_mathieuMeCoeff_ce (N : ℕ) (q : ℝ) (k : ℤ) :
    mathieuMeCoeff ((N : ℤ) : ℂ) (q : ℂ) k = (Real.sqrt 2 : ℂ) / (2 * π) *
      ∫ x in (0 : ℝ)..2 * π, mathieuCe N x q * Complex.cos (((N + 2 * k : ℤ) : ℂ) * x) := by
  set K : ℤ := N + 2 * k
  have hex : ∃ k' : ℤ, (k' : ℂ) = ((N : ℤ) : ℂ) := ⟨N, rfl⟩
  have hNK : (-1 : ℂ) ^ N * (-1 : ℂ) ^ K = 1 := p2m_negOnePow_mul_eq_one ⟨k, rfl⟩
  have hce := (isMathieuSolution_mathieuCe N q).differentiable
  have hcc : Continuous fun x : ℝ => mathieuCe N x q :=
    hce.continuous.comp Complex.continuous_ofReal
  have hshift : ∀ x : ℝ, mathieuCe N ((x - π : ℝ) : ℂ) q = (-1 : ℂ) ^ N * mathieuCe N x q := by
    intro x
    have := p2m_mathieuCe_add_pi N ((x - π : ℝ) : ℂ) q
    push_cast at this ⊢
    rw [sub_add_cancel] at this
    rw [this, ← mul_assoc, ← mul_pow]; simp
  simp only [mathieuMeCoeff, hex, ite_true, mathieuMe_intCast, mathieuMeInt]
  simp only [Int.natCast_nonneg, ite_true, Int.toNat_natCast]
  rw [show ((N : ℤ) : ℂ) + 2 * (k : ℂ) = (K : ℂ) by push_cast [K]; ring]
  -- the sine part vanishes
  have hsin : ∫ x in (0 : ℝ)..π, mathieuCe N x q * Complex.sin ((K : ℂ) * x) = 0 := by
    refine p2m_integral_eq_zero_of_reflect fun x => ?_
    have hs : Complex.sin ((K : ℂ) * ((x - π : ℝ) : ℂ)) = (-1 : ℂ) ^ K * Complex.sin (K * x) := by
      have := p2m_sin_add_int_mul_pi K ((x - π : ℝ) : ℂ)
      push_cast at this ⊢
      rw [sub_add_cancel] at this
      rw [this, ← mul_assoc, ← mul_zpow]; simp
    rw [show ((π - x : ℝ) : ℂ) = -((x - π : ℝ) : ℂ) by push_cast; ring, mathieuCe_neg, hshift,
      mul_neg, Complex.sin_neg, hs]
    linear_combination (-(mathieuCe N x q * Complex.sin (K * x))) * hNK
  have hcos : ∫ x in (0 : ℝ)..2 * π, mathieuCe N x q * Complex.cos ((K : ℂ) * x) =
      2 * ∫ x in (0 : ℝ)..π, mathieuCe N x q * Complex.cos ((K : ℂ) * x) := by
    refine p2m_integral_two_pi (by fun_prop) fun x => ?_
    push_cast
    rw [p2m_mathieuCe_add_pi, p2m_cos_add_int_mul_pi]
    linear_combination (mathieuCe N x q * Complex.cos (K * x)) * hNK
  have e : ∀ x : ℝ, (Real.sqrt 2 : ℂ) * mathieuCe N x q * Complex.exp (-(I * K * x)) =
      (Real.sqrt 2 : ℂ) * (mathieuCe N x q * Complex.cos ((K : ℂ) * x)) -
        ((Real.sqrt 2 : ℂ) * I) * (mathieuCe N x q * Complex.sin ((K : ℂ) * x)) := by
    intro x
    rw [show -(I * (K : ℂ) * x) = (-((K : ℂ) * x)) * I by ring, Complex.exp_mul_I,
      Complex.cos_neg, Complex.sin_neg]
    ring
  simp_rw [e]
  have i1 : IntervalIntegrable (fun x : ℝ => mathieuCe N x q * Complex.cos ((K : ℂ) * x))
      MeasureTheory.volume 0 π := (by fun_prop : Continuous fun x : ℝ =>
        mathieuCe N x q * Complex.cos ((K : ℂ) * x)).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun x : ℝ => mathieuCe N x q * Complex.sin ((K : ℂ) * x))
      MeasureTheory.volume 0 π := (by fun_prop : Continuous fun x : ℝ =>
        mathieuCe N x q * Complex.sin ((K : ℂ) * x)).intervalIntegrable _ _
  rw [intervalIntegral.integral_sub (i1.const_mul _) (i2.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hsin, hcos]
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp
  ring

/-- `(-1)^{a-b} = (-1)^a (-1)^b` for integers `a, b`. -/
theorem p2m_negOnePow_sub (a b : ℤ) : (-1 : ℂ) ^ (a - b) = (-1 : ℂ) ^ a * (-1 : ℂ) ^ b := by
  rw [zpow_sub₀ (by norm_num), div_eq_mul_inv,
    inv_eq_of_mul_eq_one_right (m28b_negOnePow_mul_self b)]

/-- `(-1)^{-a} = (-1)^a` for an integer `a`. -/
lemma p2m_negOnePow_neg (a : ℤ) : (-1 : ℂ) ^ (-a) = (-1 : ℂ) ^ a := by
  rw [zpow_neg, inv_eq_of_mul_eq_one_right (m28b_negOnePow_mul_self a)]

/-- `(√2)² = 2` in `ℂ`. -/
lemma p2m_sqrt_two_sq : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; push_cast; rfl

/-- `hasSum_radialMathieuMc_even_cross` (DLMF 28.24.2) for complex `h` with real `h² = q`. -/
theorem p3m_hasSum_radialMathieuMc_even_cross_gen (j : ℕ) (hj₁ : 1 ≤ j) (hj₄ : j ≤ 4) (m s : ℕ)
    {h : ℂ} {q : ℝ} (hq : h ^ 2 = (q : ℂ)) (hh : h ≠ 0)
    (hA : mathieuFourierA (2 * m) (2 * s) q ≠ 0) (z : ℂ) :
    HasSum (fun ℓ : ℕ => (-1 : ℂ) ^ m * ((-1 : ℂ) ^ ℓ *
        (mathieuFourierA (2 * m) (2 * ℓ) q / mathieuFourierA (2 * m) (2 * s) q) *
        (besselJExp ((ℓ : ℤ) - s : ℤ) h (-z) * mathieuCylExp j ((ℓ + s : ℕ) : ℂ) h z +
          besselJExp ((ℓ + s : ℕ) : ℂ) h (-z) * mathieuCylExp j ((ℓ : ℤ) - s : ℤ) h z)))
      (mathieuEpsilon s * radialMathieuMc j (2 * m) z h) := by
  have hh' : (h : ℂ) ≠ 0 := hh
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  set N : ℕ := 2 * m with hN
  have hadm : ModMathieuAdmissible ((N : ℕ) : ℂ) (h : ℂ) :=
    Or.inr ⟨⟨N, by push_cast; rfl⟩, by rw [hq]; exact Complex.ofReal_im _⟩
  have H := p2m_hasSum_modMathieuTerm j hj₁ hj₄ hadm hh' ((s : ℤ) - m) z
  set c := mathieuMeCoeff ((N : ℕ) : ℂ) ((h : ℂ) ^ 2) with hcdef
  set I0 : ℤ → ℂ := fun K => ∫ x in (0 : ℝ)..2 * π,
    mathieuCe N x q * Complex.cos ((K : ℂ) * x) with hI0
  have hc : ∀ k : ℤ, c k = (Real.sqrt 2 : ℂ) / (2 * π) * I0 (N + 2 * k) := by
    intro k
    have := p2m_mathieuMeCoeff_ce N q k
    push_cast at this
    rw [hcdef, hq, this]
    simp only [hI0, Int.cast_add, Int.cast_natCast, Int.cast_mul, Int.cast_ofNat]
  have hIneg : ∀ K : ℤ, I0 (-K) = I0 K := by
    intro K; simp only [hI0]; push_cast; simp only [neg_mul, Complex.cos_neg]
  have hAeq : ∀ ℓ : ℕ, mathieuFourierA (2 * m) (2 * ℓ) q =
      (if ℓ = 0 then 1 / (2 * π) else 1 / π : ℂ) * I0 (2 * ℓ) := by
    intro ℓ
    simp only [mathieuFourierA, hI0, hN]
    push_cast
    simp
  set M := radialMathieuMc j (2 * m) z h
  set f : ℤ → ℂ := fun p => modMathieuTerm j ((N : ℕ) : ℂ) z h ((s : ℤ) - m) (p - m) with hfdef
  have H1 : HasSum f (c ((s : ℤ) - m) * M) :=
    ((Equiv.subRight (m : ℤ)).hasSum_iff
      (f := fun p => modMathieuTerm j ((N : ℕ) : ℂ) z h ((s : ℤ) - m) p)).mpr H
  have hf : ∀ p : ℤ, f p = (-1 : ℂ) ^ p * (-1 : ℂ) ^ (m : ℤ) *
      ((Real.sqrt 2 : ℂ) / (2 * π) * I0 (2 * p)) * besselJExp ((p - s : ℤ) : ℂ) h (-z) *
        mathieuCylExp j ((p + s : ℤ) : ℂ) h z := by
    intro p
    simp only [hfdef, modMathieuTerm]
    rw [← hcdef, hc, p2m_negOnePow_sub, show (N : ℤ) + 2 * (p - m) = 2 * p by simp [hN]; ring,
      show p - m - (s - m) = p - s by ring,
      show ((N : ℕ) : ℂ) + (((s : ℤ) - m : ℤ) : ℂ) + ((p - m : ℤ) : ℂ) = ((p + s : ℤ) : ℂ) by
        simp [hN]; ring]
  have H2 := H1.nat_add_neg
  set A2s := mathieuFourierA (2 * m) (2 * s) q with hA2s
  set Kc : ℂ := (Real.sqrt 2 : ℂ) / A2s
  have H3 := (H2.mul_left Kc).sub (hasSum_ite_eq (0 : ℕ) (Kc * f 0))
  have hs2 := p2m_sqrt_two_sq
  have hKc : A2s * Kc = (Real.sqrt 2 : ℂ) := by simp only [Kc]; field_simp
  have hfpos : ∀ ℓ : ℕ, f ℓ = (-1 : ℂ) ^ ℓ * (-1 : ℂ) ^ m *
      ((Real.sqrt 2 : ℂ) / (2 * π) * I0 (2 * ℓ)) * besselJExp (((ℓ : ℤ) - s : ℤ) : ℂ) h (-z) *
        mathieuCylExp j (((ℓ : ℤ) + s : ℤ) : ℂ) h z := by
    intro ℓ; rw [hf]; simp only [zpow_natCast]
  have hfneg : ∀ ℓ : ℕ, f (-(ℓ : ℤ)) = (-1 : ℂ) ^ ℓ * (-1 : ℂ) ^ m *
      ((Real.sqrt 2 : ℂ) / (2 * π) * I0 (2 * ℓ)) * besselJExp (((ℓ : ℤ) + s : ℤ) : ℂ) h (-z) *
        mathieuCylExp j (((ℓ : ℤ) - s : ℤ) : ℂ) h z := by
    intro ℓ
    rw [hf, show -(ℓ : ℤ) - s = -((ℓ : ℤ) + s) by ring, show -(ℓ : ℤ) + s = -((ℓ : ℤ) - s) by ring,
      p1c_besselJExp_neg_intCast, p2m_mathieuCylExp_neg_intCast j hj₁ hj₄ _ hh',
      show 2 * -(ℓ : ℤ) = -(2 * ℓ) by ring, hIneg, p2m_negOnePow_neg, zpow_natCast,
      zpow_natCast]
    have hsgn : (-1 : ℂ) ^ ((ℓ : ℤ) + s) * (-1 : ℂ) ^ ((ℓ : ℤ) - s) = 1 := by
      rw [← zpow_add₀ (by norm_num), show (ℓ : ℤ) + s + (ℓ - s) = 2 * ℓ by ring, zpow_mul]
      simp
    linear_combination ((-1 : ℂ) ^ ℓ * (-1 : ℂ) ^ m * ((Real.sqrt 2 : ℂ) / (2 * π) *
      I0 (2 * ℓ)) * besselJExp (((ℓ : ℤ) + s : ℤ) : ℂ) h (-z) *
        mathieuCylExp j (((ℓ : ℤ) - s : ℤ) : ℂ) h z) * hsgn
  convert H3 using 1
  · funext ℓ
    rw [hfpos, hfneg, hAeq, show ((ℓ + s : ℕ) : ℂ) = (((ℓ : ℤ) + s : ℤ) : ℂ) by push_cast; ring]
    by_cases hℓ : ℓ = 0
    · subst hℓ
      have e0 : f 0 = f ((0 : ℕ) : ℤ) := by simp
      rw [e0, hfpos]
      have hJC : besselJExp ((((0 : ℕ) : ℤ) - s : ℤ) : ℂ) h (-z) *
          mathieuCylExp j ((((0 : ℕ) : ℤ) + s : ℤ) : ℂ) h z =
          besselJExp ((((0 : ℕ) : ℤ) + s : ℤ) : ℂ) h (-z) *
          mathieuCylExp j ((((0 : ℕ) : ℤ) - s : ℤ) : ℂ) h z := by
        simp only [Nat.cast_zero, zero_sub, zero_add]
        rw [p1c_besselJExp_neg_intCast, p2m_mathieuCylExp_neg_intCast j hj₁ hj₄ _ hh']
        ring
      simp only [ite_true]
      field_simp
      linear_combination I0 (2 * ((0 : ℕ) : ℤ)) * hJC - I0 (2 * ((0 : ℕ) : ℤ)) *
        (Real.sqrt 2 : ℂ) * (besselJExp ((((0 : ℕ) : ℤ) + s : ℤ) : ℂ) h (-z) *
          mathieuCylExp j ((((0 : ℕ) : ℤ) - s : ℤ) : ℂ) h z) * hKc -
        I0 (2 * ((0 : ℕ) : ℤ)) * (besselJExp ((((0 : ℕ) : ℤ) + s : ℤ) : ℂ) h (-z) *
          mathieuCylExp j ((((0 : ℕ) : ℤ) - s : ℤ) : ℂ) h z) * hs2
    · simp only [hℓ, ite_false, sub_zero]
      field_simp
      set X := besselJExp (((ℓ : ℤ) - s : ℤ) : ℂ) h (-z) *
          mathieuCylExp j (((ℓ : ℤ) + s : ℤ) : ℂ) h z +
        besselJExp (((ℓ : ℤ) + s : ℤ) : ℂ) h (-z) * mathieuCylExp j (((ℓ : ℤ) - s : ℤ) : ℂ) h z
      linear_combination (-I0 (2 * ℓ) * X * (Real.sqrt 2 : ℂ)) * hKc - I0 (2 * ℓ) * X * hs2
  · rw [hc, show (N : ℤ) + 2 * ((s : ℤ) - m) = 2 * s by simp [hN]; ring]
    have hA' := hA
    rw [hA2s, hAeq s] at hA' hKc
    simp only [mathieuEpsilon]
    split_ifs at hA' hKc ⊢ with hs0
    · field_simp at hKc ⊢
      linear_combination (-((Real.sqrt 2 : ℂ) * M)) * hKc - 2 * π * M * hs2
    · field_simp at hKc ⊢
      linear_combination (-((Real.sqrt 2 : ℂ) * M)) * hKc - π * M * hs2

/-- Proof of `hasSum_radialMathieuMc_even_cross` (DLMF 28.24.2). -/
theorem p2m_hasSum_radialMathieuMc_even_cross (j : ℕ) (hj₁ : 1 ≤ j) (hj₄ : j ≤ 4) (m s : ℕ)
    {h : ℝ} (hh : 0 < h) (hA : mathieuFourierA (2 * m) (2 * s) (h ^ 2) ≠ 0) (z : ℂ) :
    HasSum (fun ℓ : ℕ => (-1 : ℂ) ^ m * ((-1 : ℂ) ^ ℓ *
        (mathieuFourierA (2 * m) (2 * ℓ) (h ^ 2) / mathieuFourierA (2 * m) (2 * s) (h ^ 2)) *
        (besselJExp ((ℓ : ℤ) - s : ℤ) h (-z) * mathieuCylExp j ((ℓ + s : ℕ) : ℂ) h z +
          besselJExp ((ℓ + s : ℕ) : ℂ) h (-z) * mathieuCylExp j ((ℓ : ℤ) - s : ℤ) h z)))
      (mathieuEpsilon s * radialMathieuMc j (2 * m) z h) :=
  p3m_hasSum_radialMathieuMc_even_cross_gen j hj₁ hj₄ m s (q := h ^ 2) (by push_cast; ring)
    (by exact_mod_cast hh.ne') hA z

/-- `hasSum_radialMathieuMc_odd_cross` (DLMF 28.24.3) for complex `h` with real `h² = q`. -/
theorem p3m_hasSum_radialMathieuMc_odd_cross_gen (j : ℕ) (hj₁ : 1 ≤ j) (hj₄ : j ≤ 4) (m s : ℕ)
    {h : ℂ} {q : ℝ} (hq : h ^ 2 = (q : ℂ)) (hh : h ≠ 0)
    (hA : mathieuFourierA (2 * m + 1) (2 * s + 1) q ≠ 0) (z : ℂ) :
    HasSum (fun ℓ : ℕ => (-1 : ℂ) ^ m * ((-1 : ℂ) ^ ℓ *
        (mathieuFourierA (2 * m + 1) (2 * ℓ + 1) q /
          mathieuFourierA (2 * m + 1) (2 * s + 1) q) *
        (besselJExp ((ℓ : ℤ) - s : ℤ) h (-z) * mathieuCylExp j ((ℓ + s + 1 : ℕ) : ℂ) h z +
          besselJExp ((ℓ + s + 1 : ℕ) : ℂ) h (-z) * mathieuCylExp j ((ℓ : ℤ) - s : ℤ) h z)))
      (radialMathieuMc j (2 * m + 1) z h) := by
  have hh' : (h : ℂ) ≠ 0 := hh
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  set N : ℕ := 2 * m + 1 with hN
  have hadm : ModMathieuAdmissible ((N : ℕ) : ℂ) (h : ℂ) :=
    Or.inr ⟨⟨N, by push_cast; rfl⟩, by rw [hq]; exact Complex.ofReal_im _⟩
  have H := p2m_hasSum_modMathieuTerm j hj₁ hj₄ hadm hh' ((s : ℤ) - m) z
  set c := mathieuMeCoeff ((N : ℕ) : ℂ) ((h : ℂ) ^ 2) with hcdef
  set I0 : ℤ → ℂ := fun K => ∫ x in (0 : ℝ)..2 * π,
    mathieuCe N x q * Complex.cos ((K : ℂ) * x) with hI0
  have hc : ∀ k : ℤ, c k = (Real.sqrt 2 : ℂ) / (2 * π) * I0 (N + 2 * k) := by
    intro k
    have := p2m_mathieuMeCoeff_ce N q k
    push_cast at this
    rw [hcdef, hq, this]
    simp only [hI0, Int.cast_add, Int.cast_natCast, Int.cast_mul, Int.cast_ofNat]
  have hIneg : ∀ K : ℤ, I0 (-K) = I0 K := by
    intro K; simp only [hI0]; push_cast; simp only [neg_mul, Complex.cos_neg]
  have hAeq : ∀ ℓ : ℕ, mathieuFourierA (2 * m + 1) (2 * ℓ + 1) q =
      (1 / π : ℂ) * I0 (2 * ℓ + 1) := by
    intro ℓ
    simp only [mathieuFourierA, hI0, hN]
    push_cast
    simp
  set M := radialMathieuMc j (2 * m + 1) z h
  set f : ℤ → ℂ := fun p => modMathieuTerm j ((N : ℕ) : ℂ) z h ((s : ℤ) - m) (p - m) with hfdef
  have H1 : HasSum f (c ((s : ℤ) - m) * M) :=
    ((Equiv.subRight (m : ℤ)).hasSum_iff
      (f := fun p => modMathieuTerm j ((N : ℕ) : ℂ) z h ((s : ℤ) - m) p)).mpr H
  have hf : ∀ p : ℤ, f p = (-1 : ℂ) ^ p * (-1 : ℂ) ^ (m : ℤ) *
      ((Real.sqrt 2 : ℂ) / (2 * π) * I0 (2 * p + 1)) * besselJExp ((p - s : ℤ) : ℂ) h (-z) *
        mathieuCylExp j ((p + s + 1 : ℤ) : ℂ) h z := by
    intro p
    simp only [hfdef, modMathieuTerm]
    rw [← hcdef, hc, p2m_negOnePow_sub,
      show (N : ℤ) + 2 * (p - m) = 2 * p + 1 by simp [hN]; ring,
      show p - m - (s - m) = p - s by ring,
      show ((N : ℕ) : ℂ) + (((s : ℤ) - m : ℤ) : ℂ) + ((p - m : ℤ) : ℂ) = ((p + s + 1 : ℤ) : ℂ) by
        simp [hN]; ring]
  have H2 := H1.nat_add_neg_add_one
  set A2s := mathieuFourierA (2 * m + 1) (2 * s + 1) q with hA2s
  set Kc : ℂ := (Real.sqrt 2 : ℂ) / A2s
  have H3 := H2.mul_left Kc
  have hs2 := p2m_sqrt_two_sq
  have hKc : A2s * Kc = (Real.sqrt 2 : ℂ) := by simp only [Kc]; field_simp
  have hfpos : ∀ ℓ : ℕ, f ℓ = (-1 : ℂ) ^ ℓ * (-1 : ℂ) ^ m *
      ((Real.sqrt 2 : ℂ) / (2 * π) * I0 (2 * ℓ + 1)) *
        besselJExp (((ℓ : ℤ) - s : ℤ) : ℂ) h (-z) *
        mathieuCylExp j (((ℓ : ℤ) + s + 1 : ℤ) : ℂ) h z := by
    intro ℓ; rw [hf]; simp only [zpow_natCast]
  have hfneg : ∀ ℓ : ℕ, f (-((ℓ : ℤ) + 1)) = (-1 : ℂ) ^ ℓ * (-1 : ℂ) ^ m *
      ((Real.sqrt 2 : ℂ) / (2 * π) * I0 (2 * ℓ + 1)) *
        besselJExp (((ℓ : ℤ) + s + 1 : ℤ) : ℂ) h (-z) *
        mathieuCylExp j (((ℓ : ℤ) - s : ℤ) : ℂ) h z := by
    intro ℓ
    rw [hf, show -((ℓ : ℤ) + 1) - s = -((ℓ : ℤ) + s + 1) by ring,
      show -((ℓ : ℤ) + 1) + s + 1 = -((ℓ : ℤ) - s) by ring,
      p1c_besselJExp_neg_intCast, p2m_mathieuCylExp_neg_intCast j hj₁ hj₄ _ hh',
      show 2 * -((ℓ : ℤ) + 1) + 1 = -(2 * ℓ + 1) by ring, hIneg, p2m_negOnePow_neg,
      zpow_natCast]
    have hsgn : (-1 : ℂ) ^ ((ℓ : ℤ) + 1) * ((-1 : ℂ) ^ ((ℓ : ℤ) + s + 1) *
        (-1 : ℂ) ^ ((ℓ : ℤ) - s)) = (-1 : ℂ) ^ ℓ := by
      rw [← zpow_add₀ (by norm_num), ← zpow_add₀ (by norm_num),
        show (ℓ : ℤ) + 1 + ((ℓ : ℤ) + s + 1 + (ℓ - s)) = ℓ + 2 * (ℓ + 1) by ring,
        zpow_add₀ (by norm_num), zpow_mul]
      simp
    linear_combination ((-1 : ℂ) ^ m * ((Real.sqrt 2 : ℂ) / (2 * π) *
      I0 (2 * ℓ + 1)) * besselJExp (((ℓ : ℤ) + s + 1 : ℤ) : ℂ) h (-z) *
        mathieuCylExp j (((ℓ : ℤ) - s : ℤ) : ℂ) h z) * hsgn
  convert H3 using 1
  · funext ℓ
    rw [hfpos, hfneg, hAeq, show ((ℓ + s + 1 : ℕ) : ℂ) = (((ℓ : ℤ) + s + 1 : ℤ) : ℂ) by
      push_cast; ring]
    field_simp
    set X := besselJExp (((ℓ : ℤ) - s : ℤ) : ℂ) h (-z) *
        mathieuCylExp j (((ℓ : ℤ) + s + 1 : ℤ) : ℂ) h z +
      besselJExp (((ℓ : ℤ) + s + 1 : ℤ) : ℂ) h (-z) * mathieuCylExp j (((ℓ : ℤ) - s : ℤ) : ℂ) h z
    linear_combination (-I0 (2 * ℓ + 1) * X * (Real.sqrt 2 : ℂ)) * hKc - I0 (2 * ℓ + 1) * X * hs2
  · rw [hc, show (N : ℤ) + 2 * ((s : ℤ) - m) = 2 * s + 1 by simp [hN]; ring]
    rw [hA2s, hAeq s] at hKc
    field_simp at hKc ⊢
    linear_combination (-((Real.sqrt 2 : ℂ) * M)) * hKc - π * M * hs2

/-- Proof of `hasSum_radialMathieuMc_odd_cross` (DLMF 28.24.3). -/
theorem p2m_hasSum_radialMathieuMc_odd_cross (j : ℕ) (hj₁ : 1 ≤ j) (hj₄ : j ≤ 4) (m s : ℕ)
    {h : ℝ} (hh : 0 < h) (hA : mathieuFourierA (2 * m + 1) (2 * s + 1) (h ^ 2) ≠ 0) (z : ℂ) :
    HasSum (fun ℓ : ℕ => (-1 : ℂ) ^ m * ((-1 : ℂ) ^ ℓ *
        (mathieuFourierA (2 * m + 1) (2 * ℓ + 1) (h ^ 2) /
          mathieuFourierA (2 * m + 1) (2 * s + 1) (h ^ 2)) *
        (besselJExp ((ℓ : ℤ) - s : ℤ) h (-z) * mathieuCylExp j ((ℓ + s + 1 : ℕ) : ℂ) h z +
          besselJExp ((ℓ + s + 1 : ℕ) : ℂ) h (-z) * mathieuCylExp j ((ℓ : ℤ) - s : ℤ) h z)))
      (radialMathieuMc j (2 * m + 1) z h) :=
  p3m_hasSum_radialMathieuMc_odd_cross_gen j hj₁ hj₄ m s (q := h ^ 2) (by push_cast; ring)
    (by exact_mod_cast hh.ne') hA z

/-- The integer-order coefficients `c^{-N}_{2k}` of `me_{-N} = -√2 i se_N` (`N ≥ 1`) as sine
integrals: `c^{-N}_{2k}(q) = -√2/(2π) ∫₀^{2π} se_N(x) sin((2k-N)x) dx`. -/
theorem p2m_mathieuMeCoeff_se {N : ℕ} (hN0 : N ≠ 0) (q : ℝ) (k : ℤ) :
    mathieuMeCoeff ((-(N : ℤ) : ℤ) : ℂ) (q : ℂ) k = -((Real.sqrt 2 : ℂ) / (2 * π)) *
      ∫ x in (0 : ℝ)..2 * π, mathieuSe N x q * Complex.sin (((-(N : ℤ) + 2 * k : ℤ) : ℂ) * x) := by
  set K : ℤ := -(N : ℤ) + 2 * k
  have hex : ∃ k' : ℤ, (k' : ℂ) = ((-(N : ℤ) : ℤ) : ℂ) := ⟨-(N : ℤ), rfl⟩
  have hNK : (-1 : ℂ) ^ N * (-1 : ℂ) ^ K = 1 := p2m_negOnePow_mul_eq_one ⟨k - N, by simp [K]; ring⟩
  have hse := (isMathieuSolution_mathieuSe N q).differentiable
  have hsc : Continuous fun x : ℝ => mathieuSe N x q :=
    hse.continuous.comp Complex.continuous_ofReal
  have hshift : ∀ x : ℝ, mathieuSe N ((x - π : ℝ) : ℂ) q = (-1 : ℂ) ^ N * mathieuSe N x q := by
    intro x
    have := p2m_mathieuSe_add_pi hN0 ((x - π : ℝ) : ℂ) q
    push_cast at this ⊢
    rw [sub_add_cancel] at this
    rw [this, ← mul_assoc, ← mul_pow]; simp
  have hneg : ¬ (0 : ℤ) ≤ -(N : ℤ) := by omega
  simp only [mathieuMeCoeff, hex, ite_true, mathieuMe_intCast, mathieuMeInt, hneg, ite_false,
    Int.natAbs_neg, Int.natAbs_natCast]
  rw [show ((-(N : ℤ) : ℤ) : ℂ) + 2 * (k : ℂ) = (K : ℂ) by push_cast [K]; ring]
  have hcos0 : ∫ x in (0 : ℝ)..π, mathieuSe N x q * Complex.cos ((K : ℂ) * x) = 0 := by
    refine p2m_integral_eq_zero_of_reflect fun x => ?_
    have hc : Complex.cos ((K : ℂ) * ((x - π : ℝ) : ℂ)) = (-1 : ℂ) ^ K * Complex.cos (K * x) := by
      have := p2m_cos_add_int_mul_pi K ((x - π : ℝ) : ℂ)
      push_cast at this ⊢
      rw [sub_add_cancel] at this
      rw [this, ← mul_assoc, ← mul_zpow]; simp
    rw [show ((π - x : ℝ) : ℂ) = -((x - π : ℝ) : ℂ) by push_cast; ring, mathieuSe_neg, hshift,
      mul_neg, Complex.cos_neg, hc]
    linear_combination (-(mathieuSe N x q * Complex.cos (K * x))) * hNK
  have hsin : ∫ x in (0 : ℝ)..2 * π, mathieuSe N x q * Complex.sin ((K : ℂ) * x) =
      2 * ∫ x in (0 : ℝ)..π, mathieuSe N x q * Complex.sin ((K : ℂ) * x) := by
    refine p2m_integral_two_pi (by fun_prop) fun x => ?_
    push_cast
    rw [p2m_mathieuSe_add_pi hN0, p2m_sin_add_int_mul_pi]
    linear_combination (mathieuSe N x q * Complex.sin (K * x)) * hNK
  have e : ∀ x : ℝ, -((Real.sqrt 2 : ℂ) * I) * mathieuSe N x q * Complex.exp (-(I * K * x)) =
      -((Real.sqrt 2 : ℂ) * I) * (mathieuSe N x q * Complex.cos ((K : ℂ) * x)) -
        (Real.sqrt 2 : ℂ) * (mathieuSe N x q * Complex.sin ((K : ℂ) * x)) := by
    intro x
    rw [show -(I * (K : ℂ) * x) = (-((K : ℂ) * x)) * I by ring, Complex.exp_mul_I,
      Complex.cos_neg, Complex.sin_neg]
    ring_nf
    rw [I_sq]
    ring
  simp_rw [e]
  have i1 : IntervalIntegrable (fun x : ℝ => mathieuSe N x q * Complex.cos ((K : ℂ) * x))
      MeasureTheory.volume 0 π := (by fun_prop : Continuous fun x : ℝ =>
        mathieuSe N x q * Complex.cos ((K : ℂ) * x)).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun x : ℝ => mathieuSe N x q * Complex.sin ((K : ℂ) * x))
      MeasureTheory.volume 0 π := (by fun_prop : Continuous fun x : ℝ =>
        mathieuSe N x q * Complex.sin ((K : ℂ) * x)).intervalIntegrable _ _
  rw [intervalIntegral.integral_sub (i1.const_mul _) (i2.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hcos0, hsin]
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp
  ring

/-- `hasSum_radialMathieuMs_odd_cross` (DLMF 28.24.4) for complex `h` with real `h² = q`. -/
theorem p3m_hasSum_radialMathieuMs_odd_cross_gen (j : ℕ) (hj₁ : 1 ≤ j) (hj₄ : j ≤ 4) (m s : ℕ)
    {h : ℂ} {q : ℝ} (hq : h ^ 2 = (q : ℂ)) (hh : h ≠ 0)
    (hB : mathieuFourierB (2 * m + 1) (2 * s + 1) q ≠ 0) (z : ℂ) :
    HasSum (fun ℓ : ℕ => (-1 : ℂ) ^ m * ((-1 : ℂ) ^ ℓ *
        (mathieuFourierB (2 * m + 1) (2 * ℓ + 1) q /
          mathieuFourierB (2 * m + 1) (2 * s + 1) q) *
        (besselJExp ((ℓ : ℤ) - s : ℤ) h (-z) * mathieuCylExp j ((ℓ + s + 1 : ℕ) : ℂ) h z -
          besselJExp ((ℓ + s + 1 : ℕ) : ℂ) h (-z) * mathieuCylExp j ((ℓ : ℤ) - s : ℤ) h z)))
      (radialMathieuMs j (2 * m + 1) z h) := by
  have hh' : (h : ℂ) ≠ 0 := hh
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  set N : ℕ := 2 * m + 1 with hN
  have hN0 : N ≠ 0 := by omega
  set ν : ℂ := -((N : ℕ) : ℂ) with hν
  have hadm : ModMathieuAdmissible ν (h : ℂ) :=
    Or.inr ⟨⟨-(N : ℤ), by push_cast; rfl⟩, by rw [hq]; exact Complex.ofReal_im _⟩
  set n : ℤ := (s : ℤ) + m + 1 with hn
  have H := p2m_hasSum_modMathieuTerm j hj₁ hj₄ hadm hh' n z
  set c := mathieuMeCoeff ν ((h : ℂ) ^ 2) with hcdef
  set S0 : ℤ → ℂ := fun K => ∫ x in (0 : ℝ)..2 * π,
    mathieuSe N x q * Complex.sin ((K : ℂ) * x) with hS0
  have hc : ∀ k : ℤ, c k = -((Real.sqrt 2 : ℂ) / (2 * π)) * S0 (-(N : ℤ) + 2 * k) := by
    intro k
    have := p2m_mathieuMeCoeff_se hN0 q k
    push_cast at this
    rw [hcdef, hν, hq, this]
    simp only [hS0, Int.cast_add, Int.cast_natCast, Int.cast_mul, Int.cast_ofNat, Int.cast_neg]
  have hSneg : ∀ K : ℤ, S0 (-K) = -S0 K := by
    intro K; simp only [hS0]; push_cast
    simp only [neg_mul, Complex.sin_neg, mul_neg, intervalIntegral.integral_neg]
  have hBeq : ∀ ℓ : ℕ, mathieuFourierB (2 * m + 1) (2 * ℓ + 1) q =
      (1 / π : ℂ) * S0 (2 * ℓ + 1) := by
    intro ℓ
    simp only [mathieuFourierB, hS0, hN]
    push_cast
    simp
  set M := modMathieuM j ν z h
  have hMs : radialMathieuMs j (2 * m + 1) z h = -M := by
    simp only [radialMathieuMs, M, hν, hN]; rw [pow_succ, pow_mul]; simp
  rw [hMs]
  set f : ℤ → ℂ := fun p => modMathieuTerm j ν z h n (p + (m + 1)) with hfdef
  have H1 : HasSum f (c n * M) :=
    ((Equiv.addRight ((m : ℤ) + 1)).hasSum_iff
      (f := fun p => modMathieuTerm j ν z h n p)).mpr H
  have hf : ∀ p : ℤ, f p = (-1 : ℂ) ^ p * (-1 : ℂ) ^ (m : ℤ) *
      ((Real.sqrt 2 : ℂ) / (2 * π) * S0 (2 * p + 1)) * besselJExp ((p - s : ℤ) : ℂ) h (-z) *
        mathieuCylExp j ((p + s + 1 : ℤ) : ℂ) h z := by
    intro p
    simp only [hfdef, modMathieuTerm]
    rw [← hcdef, hc, zpow_add₀ (by norm_num), zpow_add₀ (by norm_num),
      show -(N : ℤ) + 2 * (p + (m + 1)) = 2 * p + 1 by simp [hN]; ring,
      show p + (m + 1) - n = p - s by simp [hn]; ring,
      show ν + (n : ℂ) + ((p + (m + 1) : ℤ) : ℂ) = ((p + s + 1 : ℤ) : ℂ) by
        simp [hν, hN, hn]; ring]
    simp only [zpow_one]
    ring
  have H2 := H1.nat_add_neg_add_one
  set B2s := mathieuFourierB (2 * m + 1) (2 * s + 1) q with hB2s
  set Kc : ℂ := (Real.sqrt 2 : ℂ) / B2s
  have H3 := H2.mul_left Kc
  have hs2 := p2m_sqrt_two_sq
  have hKc : B2s * Kc = (Real.sqrt 2 : ℂ) := by simp only [Kc]; field_simp
  have hfpos : ∀ ℓ : ℕ, f ℓ = (-1 : ℂ) ^ ℓ * (-1 : ℂ) ^ m *
      ((Real.sqrt 2 : ℂ) / (2 * π) * S0 (2 * ℓ + 1)) *
        besselJExp (((ℓ : ℤ) - s : ℤ) : ℂ) h (-z) *
        mathieuCylExp j (((ℓ : ℤ) + s + 1 : ℤ) : ℂ) h z := by
    intro ℓ; rw [hf]; simp only [zpow_natCast]
  have hfneg : ∀ ℓ : ℕ, f (-((ℓ : ℤ) + 1)) = -((-1 : ℂ) ^ ℓ * (-1 : ℂ) ^ m *
      ((Real.sqrt 2 : ℂ) / (2 * π) * S0 (2 * ℓ + 1)) *
        besselJExp (((ℓ : ℤ) + s + 1 : ℤ) : ℂ) h (-z) *
        mathieuCylExp j (((ℓ : ℤ) - s : ℤ) : ℂ) h z) := by
    intro ℓ
    rw [hf, show -((ℓ : ℤ) + 1) - s = -((ℓ : ℤ) + s + 1) by ring,
      show -((ℓ : ℤ) + 1) + s + 1 = -((ℓ : ℤ) - s) by ring,
      p1c_besselJExp_neg_intCast, p2m_mathieuCylExp_neg_intCast j hj₁ hj₄ _ hh',
      show 2 * -((ℓ : ℤ) + 1) + 1 = -(2 * ℓ + 1) by ring, hSneg, p2m_negOnePow_neg,
      zpow_natCast]
    have hsgn : (-1 : ℂ) ^ ((ℓ : ℤ) + 1) * ((-1 : ℂ) ^ ((ℓ : ℤ) + s + 1) *
        (-1 : ℂ) ^ ((ℓ : ℤ) - s)) = (-1 : ℂ) ^ ℓ := by
      rw [← zpow_add₀ (by norm_num), ← zpow_add₀ (by norm_num),
        show (ℓ : ℤ) + 1 + ((ℓ : ℤ) + s + 1 + (ℓ - s)) = ℓ + 2 * (ℓ + 1) by ring,
        zpow_add₀ (by norm_num), zpow_mul]
      simp
    linear_combination (-((-1 : ℂ) ^ m * ((Real.sqrt 2 : ℂ) / (2 * π) *
      S0 (2 * ℓ + 1)) * besselJExp (((ℓ : ℤ) + s + 1 : ℤ) : ℂ) h (-z) *
        mathieuCylExp j (((ℓ : ℤ) - s : ℤ) : ℂ) h z)) * hsgn
  convert H3 using 1
  · funext ℓ
    rw [hfpos, hfneg, hBeq, show ((ℓ + s + 1 : ℕ) : ℂ) = (((ℓ : ℤ) + s + 1 : ℤ) : ℂ) by
      push_cast; ring]
    field_simp
    linear_combination (-S0 (2 * ℓ + 1) * (besselJExp (((ℓ : ℤ) - s : ℤ) : ℂ) h (-z) *
        mathieuCylExp j (((ℓ : ℤ) + s + 1 : ℤ) : ℂ) h z -
      besselJExp (((ℓ : ℤ) + s + 1 : ℤ) : ℂ) h (-z) * mathieuCylExp j (((ℓ : ℤ) - s : ℤ) : ℂ) h z) *
        (Real.sqrt 2 : ℂ)) * hKc - S0 (2 * ℓ + 1) * (besselJExp (((ℓ : ℤ) - s : ℤ) : ℂ) h (-z) *
        mathieuCylExp j (((ℓ : ℤ) + s + 1 : ℤ) : ℂ) h z -
      besselJExp (((ℓ : ℤ) + s + 1 : ℤ) : ℂ) h (-z) *
        mathieuCylExp j (((ℓ : ℤ) - s : ℤ) : ℂ) h z) * hs2
  · rw [hc, show -(N : ℤ) + 2 * n = 2 * s + 1 by simp [hN, hn]; ring]
    rw [hB2s, hBeq s] at hKc
    field_simp at hKc ⊢
    linear_combination ((Real.sqrt 2 : ℂ) * M) * hKc + π * M * hs2

/-- Proof of `hasSum_radialMathieuMs_odd_cross` (DLMF 28.24.4). -/
theorem p2m_hasSum_radialMathieuMs_odd_cross (j : ℕ) (hj₁ : 1 ≤ j) (hj₄ : j ≤ 4) (m s : ℕ)
    {h : ℝ} (hh : 0 < h) (hB : mathieuFourierB (2 * m + 1) (2 * s + 1) (h ^ 2) ≠ 0) (z : ℂ) :
    HasSum (fun ℓ : ℕ => (-1 : ℂ) ^ m * ((-1 : ℂ) ^ ℓ *
        (mathieuFourierB (2 * m + 1) (2 * ℓ + 1) (h ^ 2) /
          mathieuFourierB (2 * m + 1) (2 * s + 1) (h ^ 2)) *
        (besselJExp ((ℓ : ℤ) - s : ℤ) h (-z) * mathieuCylExp j ((ℓ + s + 1 : ℕ) : ℂ) h z -
          besselJExp ((ℓ + s + 1 : ℕ) : ℂ) h (-z) * mathieuCylExp j ((ℓ : ℤ) - s : ℤ) h z)))
      (radialMathieuMs j (2 * m + 1) z h) :=
  p3m_hasSum_radialMathieuMs_odd_cross_gen j hj₁ hj₄ m s (q := h ^ 2) (by push_cast; ring)
    (by exact_mod_cast hh.ne') hB z

/-- `hasSum_radialMathieuMs_even_cross` (DLMF 28.24.5) for complex `h` with real `h² = q`. -/
theorem p3m_hasSum_radialMathieuMs_even_cross_gen (j : ℕ) (hj₁ : 1 ≤ j) (hj₄ : j ≤ 4) (m s : ℕ)
    {h : ℂ} {q : ℝ} (hq : h ^ 2 = (q : ℂ)) (hh : h ≠ 0)
    (hB : mathieuFourierB (2 * m + 2) (2 * s + 2) q ≠ 0) (z : ℂ) :
    HasSum (fun ℓ : ℕ => (-1 : ℂ) ^ m * ((-1 : ℂ) ^ ℓ *
        (mathieuFourierB (2 * m + 2) (2 * ℓ + 2) q /
          mathieuFourierB (2 * m + 2) (2 * s + 2) q) *
        (besselJExp ((ℓ : ℤ) - s : ℤ) h (-z) * mathieuCylExp j ((ℓ + s + 2 : ℕ) : ℂ) h z -
          besselJExp ((ℓ + s + 2 : ℕ) : ℂ) h (-z) * mathieuCylExp j ((ℓ : ℤ) - s : ℤ) h z)))
      (radialMathieuMs j (2 * m + 2) z h) := by
  have hh' : (h : ℂ) ≠ 0 := hh
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  set N : ℕ := 2 * m + 2 with hN
  have hN0 : N ≠ 0 := by omega
  set ν : ℂ := -((N : ℕ) : ℂ) with hν
  have hadm : ModMathieuAdmissible ν (h : ℂ) :=
    Or.inr ⟨⟨-(N : ℤ), by push_cast; rfl⟩, by rw [hq]; exact Complex.ofReal_im _⟩
  set n : ℤ := (s : ℤ) + m + 2 with hn
  have H := p2m_hasSum_modMathieuTerm j hj₁ hj₄ hadm hh' n z
  set c := mathieuMeCoeff ν ((h : ℂ) ^ 2) with hcdef
  set S0 : ℤ → ℂ := fun K => ∫ x in (0 : ℝ)..2 * π,
    mathieuSe N x q * Complex.sin ((K : ℂ) * x) with hS0
  have hc : ∀ k : ℤ, c k = -((Real.sqrt 2 : ℂ) / (2 * π)) * S0 (-(N : ℤ) + 2 * k) := by
    intro k
    have := p2m_mathieuMeCoeff_se hN0 q k
    push_cast at this
    rw [hcdef, hν, hq, this]
    simp only [hS0, Int.cast_add, Int.cast_natCast, Int.cast_mul, Int.cast_ofNat, Int.cast_neg]
  have hSneg : ∀ K : ℤ, S0 (-K) = -S0 K := by
    intro K; simp only [hS0]; push_cast
    simp only [neg_mul, Complex.sin_neg, mul_neg, intervalIntegral.integral_neg]
  have hS00 : S0 0 = 0 := by simp [hS0]
  have hBeq : ∀ ℓ : ℕ, mathieuFourierB (2 * m + 2) (2 * ℓ + 2) q =
      (1 / π : ℂ) * S0 (2 * ℓ + 2) := by
    intro ℓ
    simp only [mathieuFourierB, hS0, hN]
    push_cast
    simp
  set M := modMathieuM j ν z h
  have hMs : radialMathieuMs j (2 * m + 2) z h = M := by
    simp only [radialMathieuMs, M, hν, hN]
    rw [show 2 * m + 2 = 2 * (m + 1) by ring, pow_mul]; push_cast; simp
  rw [hMs]
  set f : ℤ → ℂ := fun p => modMathieuTerm j ν z h n (p + (m + 2)) with hfdef
  have H1 : HasSum f (c n * M) :=
    ((Equiv.addRight ((m : ℤ) + 2)).hasSum_iff
      (f := fun p => modMathieuTerm j ν z h n p)).mpr H
  have hf : ∀ p : ℤ, f p = -((-1 : ℂ) ^ p * (-1 : ℂ) ^ (m : ℤ) *
      ((Real.sqrt 2 : ℂ) / (2 * π) * S0 (2 * p + 2))) * besselJExp ((p - s : ℤ) : ℂ) h (-z) *
        mathieuCylExp j ((p + s + 2 : ℤ) : ℂ) h z := by
    intro p
    simp only [hfdef, modMathieuTerm]
    rw [← hcdef, hc, zpow_add₀ (by norm_num), zpow_add₀ (by norm_num),
      show -(N : ℤ) + 2 * (p + (m + 2)) = 2 * p + 2 by simp [hN]; ring,
      show p + (m + 2) - n = p - s by simp [hn]; ring,
      show ν + (n : ℂ) + ((p + (m + 2) : ℤ) : ℂ) = ((p + s + 2 : ℤ) : ℂ) by
        simp [hν, hN, hn]; ring]
    have : (-1 : ℂ) ^ (2 : ℤ) = 1 := by norm_num
    rw [this]
    ring
  have hfm1 : f (-1) = 0 := by
    rw [hf, show 2 * (-1 : ℤ) + 2 = 0 by ring, hS00]; ring
  have H1' : HasSum (fun p => f (p - 1)) (c n * M) :=
    ((Equiv.subRight (1 : ℤ)).hasSum_iff (f := f)).mpr H1
  have H2 := (hasSum_nat_add_iff' 1).mpr H1'.nat_add_neg
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, neg_zero, zero_sub,
    hfm1, add_zero, sub_zero] at H2
  set B2s := mathieuFourierB (2 * m + 2) (2 * s + 2) q with hB2s
  set Kc : ℂ := (Real.sqrt 2 : ℂ) / B2s
  have H3 := H2.mul_left (-Kc)
  have hs2 := p2m_sqrt_two_sq
  have hKc : B2s * Kc = (Real.sqrt 2 : ℂ) := by simp only [Kc]; field_simp
  have hfpos : ∀ ℓ : ℕ, f (((ℓ + 1 : ℕ) : ℤ) - 1) = -((-1 : ℂ) ^ ℓ * (-1 : ℂ) ^ m *
      ((Real.sqrt 2 : ℂ) / (2 * π) * S0 (2 * ℓ + 2))) *
        besselJExp (((ℓ : ℤ) - s : ℤ) : ℂ) h (-z) *
        mathieuCylExp j (((ℓ : ℤ) + s + 2 : ℤ) : ℂ) h z := by
    intro ℓ; rw [show (((ℓ + 1 : ℕ) : ℤ) - 1) = (ℓ : ℤ) by push_cast; ring, hf]
    simp only [zpow_natCast]
  have hfneg : ∀ ℓ : ℕ, f (-((ℓ + 1 : ℕ) : ℤ) - 1) = (-1 : ℂ) ^ ℓ * (-1 : ℂ) ^ m *
      ((Real.sqrt 2 : ℂ) / (2 * π) * S0 (2 * ℓ + 2)) *
        besselJExp (((ℓ : ℤ) + s + 2 : ℤ) : ℂ) h (-z) *
        mathieuCylExp j (((ℓ : ℤ) - s : ℤ) : ℂ) h z := by
    intro ℓ
    rw [show -((ℓ + 1 : ℕ) : ℤ) - 1 = -((ℓ : ℤ) + 2) by push_cast; ring, hf,
      show -((ℓ : ℤ) + 2) - s = -((ℓ : ℤ) + s + 2) by ring,
      show -((ℓ : ℤ) + 2) + s + 2 = -((ℓ : ℤ) - s) by ring,
      p1c_besselJExp_neg_intCast, p2m_mathieuCylExp_neg_intCast j hj₁ hj₄ _ hh',
      show 2 * -((ℓ : ℤ) + 2) + 2 = -(2 * ℓ + 2) by ring, hSneg, p2m_negOnePow_neg,
      zpow_natCast]
    have hsgn : (-1 : ℂ) ^ ((ℓ : ℤ) + 2) * ((-1 : ℂ) ^ ((ℓ : ℤ) + s + 2) *
        (-1 : ℂ) ^ ((ℓ : ℤ) - s)) = (-1 : ℂ) ^ ℓ := by
      rw [← zpow_add₀ (by norm_num), ← zpow_add₀ (by norm_num),
        show (ℓ : ℤ) + 2 + ((ℓ : ℤ) + s + 2 + (ℓ - s)) = ℓ + 2 * (ℓ + 2) by ring,
        zpow_add₀ (by norm_num), zpow_mul]
      simp
    linear_combination ((-1 : ℂ) ^ m * ((Real.sqrt 2 : ℂ) / (2 * π) *
      S0 (2 * ℓ + 2)) * besselJExp (((ℓ : ℤ) + s + 2 : ℤ) : ℂ) h (-z) *
        mathieuCylExp j (((ℓ : ℤ) - s : ℤ) : ℂ) h z) * hsgn
  convert H3 using 1
  · funext ℓ
    rw [hfpos, hfneg, hBeq, show ((ℓ + s + 2 : ℕ) : ℂ) = (((ℓ : ℤ) + s + 2 : ℤ) : ℂ) by
      push_cast; ring]
    field_simp
    linear_combination (-S0 (2 * ℓ + 2) * (besselJExp (((ℓ : ℤ) - s : ℤ) : ℂ) h (-z) *
        mathieuCylExp j (((ℓ : ℤ) + s + 2 : ℤ) : ℂ) h z -
      besselJExp (((ℓ : ℤ) + s + 2 : ℤ) : ℂ) h (-z) * mathieuCylExp j (((ℓ : ℤ) - s : ℤ) : ℂ) h z) *
        (Real.sqrt 2 : ℂ)) * hKc - S0 (2 * ℓ + 2) * (besselJExp (((ℓ : ℤ) - s : ℤ) : ℂ) h (-z) *
        mathieuCylExp j (((ℓ : ℤ) + s + 2 : ℤ) : ℂ) h z -
      besselJExp (((ℓ : ℤ) + s + 2 : ℤ) : ℂ) h (-z) *
        mathieuCylExp j (((ℓ : ℤ) - s : ℤ) : ℂ) h z) * hs2
  · rw [hc, show -(N : ℤ) + 2 * n = 2 * s + 2 by simp [hN, hn]; ring]
    rw [hB2s, hBeq s] at hKc
    field_simp at hKc ⊢
    linear_combination (-((Real.sqrt 2 : ℂ) * M)) * hKc - π * M * hs2

/-- Proof of `hasSum_radialMathieuMs_even_cross` (DLMF 28.24.5). -/
theorem p2m_hasSum_radialMathieuMs_even_cross (j : ℕ) (hj₁ : 1 ≤ j) (hj₄ : j ≤ 4) (m s : ℕ)
    {h : ℝ} (hh : 0 < h) (hB : mathieuFourierB (2 * m + 2) (2 * s + 2) (h ^ 2) ≠ 0) (z : ℂ) :
    HasSum (fun ℓ : ℕ => (-1 : ℂ) ^ m * ((-1 : ℂ) ^ ℓ *
        (mathieuFourierB (2 * m + 2) (2 * ℓ + 2) (h ^ 2) /
          mathieuFourierB (2 * m + 2) (2 * s + 2) (h ^ 2)) *
        (besselJExp ((ℓ : ℤ) - s : ℤ) h (-z) * mathieuCylExp j ((ℓ + s + 2 : ℕ) : ℂ) h z -
          besselJExp ((ℓ + s + 2 : ℕ) : ℂ) h (-z) * mathieuCylExp j ((ℓ : ℤ) - s : ℤ) h z)))
      (radialMathieuMs j (2 * m + 2) z h) :=
  p3m_hasSum_radialMathieuMs_even_cross_gen j hj₁ hj₄ m s (q := h ^ 2) (by push_cast; ring)
    (by exact_mod_cast hh.ne') hB z

end DLMF.Mathieu

end
