/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.CoalescingSaddles.DifferentialEquations.HyperbolicUmbilic

/-!
# Differential identities for the elliptic umbilic

Polynomial-weight estimates and parameter derivatives give the differential equations of the
elliptic umbilic.

Source references and common attribution are retained in
`DLMF.CoalescingSaddles.DifferentialEquations`.
-/

@[expose] public noncomputable section

open Complex MeasureTheory Set Filter Function

open scoped Real Topology

namespace DLMF.CoalescingSaddles

/-! ### Helpers: the elliptic umbilic integral with polynomial weights

The elliptic umbilic integral is an integral over the 2-cycle `∑ ε_{jk} ρ_j × ρ_k` in the
coordinates `a = s + it`, `b = s - it` (`ellipticUmbilicIntegral`). For a continuous,
polynomially bounded weight `W(a, b)`, `q2t_EM W` is the corresponding moment. On `ρ_j × ρ_k`
the integrand is bounded by `A e^{-r} e^{-q}` uniformly for bounded parameters, so the moments
may be differentiated under the integral sign (`q2t_hasDerivAt_EM`), and integration by parts
along a ray in `a` (or `b`) leaves a boundary term at `a = 0` (or `b = 0`) independent of `j`
(or `k`); these cancel because the columns (rows) of `ε` sum to zero (`q2t_EM_Wa`,
`q2t_EM_Wb`). -/

/-- A weight `W(a, b)` that is continuous and polynomially bounded. -/
def Q2tPolyBdd (W : ℂ → ℂ → ℂ) : Prop :=
  Continuous (fun p : ℂ × ℂ => W p.1 p.2) ∧
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ a b, ‖W a b‖ ≤ C * (1 + ‖a‖ + ‖b‖) ^ N

/-- Constant weights are polynomially bounded. -/
lemma q2t_polyBdd_const (c : ℂ) : Q2tPolyBdd fun _ _ => c :=
  ⟨continuous_const, ‖c‖, norm_nonneg _, 0, fun a b => by simp⟩

/-- The weight `(a, b) ↦ a` is polynomially bounded. -/
lemma q2t_polyBdd_fst : Q2tPolyBdd fun a _ => a :=
  ⟨continuous_fst, 1, zero_le_one, 1, fun a b => by
    simp only [pow_one, one_mul]; linarith [norm_nonneg b]⟩

/-- The weight `(a, b) ↦ b` is polynomially bounded. -/
lemma q2t_polyBdd_snd : Q2tPolyBdd fun _ b => b :=
  ⟨continuous_snd, 1, zero_le_one, 1, fun a b => by
    simp only [pow_one, one_mul]; linarith [norm_nonneg a]⟩

/-- `1 ≤ 1 + ‖a‖ + ‖b‖`. -/
lemma q2t_one_le_base (a b : ℂ) : 1 ≤ 1 + ‖a‖ + ‖b‖ := by
  linarith [norm_nonneg a, norm_nonneg b]

/-- Sums of polynomially bounded weights are polynomially bounded. -/
lemma q2t_polyBdd_add {W₁ W₂ : ℂ → ℂ → ℂ} (h₁ : Q2tPolyBdd W₁) (h₂ : Q2tPolyBdd W₂) :
    Q2tPolyBdd fun a b => W₁ a b + W₂ a b := by
  obtain ⟨c₁, C₁, hC₁, N₁, hb₁⟩ := h₁
  obtain ⟨c₂, C₂, hC₂, N₂, hb₂⟩ := h₂
  refine ⟨c₁.add c₂, C₁ + C₂, by positivity, N₁ + N₂, fun a b => ?_⟩
  have h1 := q2t_one_le_base a b
  have e1 : (1 + ‖a‖ + ‖b‖) ^ N₁ ≤ (1 + ‖a‖ + ‖b‖) ^ (N₁ + N₂) :=
    pow_le_pow_right₀ h1 (by omega)
  have e2 : (1 + ‖a‖ + ‖b‖) ^ N₂ ≤ (1 + ‖a‖ + ‖b‖) ^ (N₁ + N₂) :=
    pow_le_pow_right₀ h1 (by omega)
  calc ‖W₁ a b + W₂ a b‖ ≤ ‖W₁ a b‖ + ‖W₂ a b‖ := norm_add_le _ _
    _ ≤ C₁ * (1 + ‖a‖ + ‖b‖) ^ N₁ + C₂ * (1 + ‖a‖ + ‖b‖) ^ N₂ := add_le_add (hb₁ a b) (hb₂ a b)
    _ ≤ C₁ * (1 + ‖a‖ + ‖b‖) ^ (N₁ + N₂) + C₂ * (1 + ‖a‖ + ‖b‖) ^ (N₁ + N₂) :=
        add_le_add (mul_le_mul_of_nonneg_left e1 hC₁) (mul_le_mul_of_nonneg_left e2 hC₂)
    _ = (C₁ + C₂) * (1 + ‖a‖ + ‖b‖) ^ (N₁ + N₂) := by ring

/-- Products of polynomially bounded weights are polynomially bounded. -/
lemma q2t_polyBdd_mul {W₁ W₂ : ℂ → ℂ → ℂ} (h₁ : Q2tPolyBdd W₁) (h₂ : Q2tPolyBdd W₂) :
    Q2tPolyBdd fun a b => W₁ a b * W₂ a b := by
  obtain ⟨c₁, C₁, hC₁, N₁, hb₁⟩ := h₁
  obtain ⟨c₂, C₂, hC₂, N₂, hb₂⟩ := h₂
  refine ⟨c₁.mul c₂, C₁ * C₂, by positivity, N₁ + N₂, fun a b => ?_⟩
  rw [norm_mul, pow_add]
  calc ‖W₁ a b‖ * ‖W₂ a b‖ ≤ (C₁ * (1 + ‖a‖ + ‖b‖) ^ N₁) * (C₂ * (1 + ‖a‖ + ‖b‖) ^ N₂) :=
        mul_le_mul (hb₁ a b) (hb₂ a b) (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- The elliptic umbilic ray directions have modulus `1`. -/
lemma q2t_norm_rayDir (j : Fin 3) : ‖ellipticUmbilicRayDir j‖ = 1 := by
  rw [ellipticUmbilicRayDir]; exact norm_exp_ofReal_mul_I _

/-- The elliptic umbilic ray directions are nonzero. -/
lemma q2t_rayDir_ne_zero (j : Fin 3) : ellipticUmbilicRayDir j ≠ 0 := by
  intro h; have := q2t_norm_rayDir j; rw [h, norm_zero] at this; exact zero_ne_one this

/-- The phase of the elliptic umbilic integrand on a product of rays. -/
lemma q2t_re_phase_le (x y z : ℝ) {C : ℝ} (hC : |x| + |y| + |z| ≤ C) (j k : Fin 3)
    {r q : ℝ} (hr : 0 ≤ r) (hq : 0 ≤ q) :
    (I * ellipticUmbilicPotentialAB ((r : ℂ) * ellipticUmbilicRayDir j)
      ((q : ℂ) * ellipticUmbilicRayDir k) x y z).re ≤
      -(r ^ 3 + q ^ 3) / 2 + C * (r * q + r + q) := by
  set ej := ellipticUmbilicRayDir j
  set ek := ellipticUmbilicRayDir k
  have hej : ‖ej‖ = 1 := q2t_norm_rayDir j
  have hek : ‖ek‖ = 1 := q2t_norm_rayDir k
  rw [ellipticUmbilicPotentialAB_eq]
  have hc : ((r : ℂ) * ej) ^ 3 = (r : ℂ) ^ 3 * I := by rw [mul_pow, s36a_rayDir_cube]
  have hd : ((q : ℂ) * ek) ^ 3 = (q : ℂ) ^ 3 * I := by rw [mul_pow, s36a_rayDir_cube]
  set R := (z : ℂ) * ((r : ℂ) * ej) * ((q : ℂ) * ek) + (x - I * y) / 2 * ((r : ℂ) * ej) +
    (x + I * y) / 2 * ((q : ℂ) * ek) with hR
  have hsplit : I * ((((r : ℂ) * ej) ^ 3 + ((q : ℂ) * ek) ^ 3) / 2 + (z : ℂ) * ((r : ℂ) * ej) *
      ((q : ℂ) * ek) + (x - I * y) / 2 * ((r : ℂ) * ej) + (x + I * y) / 2 * ((q : ℂ) * ek)) =
      (((-(r ^ 3 + q ^ 3) / 2 : ℝ)) : ℂ) + I * R := by
    rw [hc, hd, hR]; push_cast; linear_combination (((r : ℂ) ^ 3 + (q : ℂ) ^ 3) / 2) * I_sq
  rw [hsplit, add_re, ofReal_re]
  have hxy1 : ‖((x : ℂ) - I * y) / 2‖ ≤ (|x| + |y|) / 2 := by
    rw [norm_div, Complex.norm_two]
    have := norm_sub_le (x : ℂ) (I * y)
    simp only [norm_mul, norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs] at this
    linarith
  have hxy2 : ‖((x : ℂ) + I * y) / 2‖ ≤ (|x| + |y|) / 2 := by
    rw [norm_div, Complex.norm_two]
    have := norm_add_le (x : ℂ) (I * y)
    simp only [norm_mul, norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs] at this
    linarith
  have hRn : ‖R‖ ≤ |z| * (r * q) + (|x| + |y|) / 2 * r + (|x| + |y|) / 2 * q := by
    rw [hR]
    refine (norm_add_le _ _).trans ?_
    refine add_le_add ((norm_add_le _ _).trans (add_le_add ?_ ?_)) ?_
    · simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, hej, hek, abs_of_nonneg hr,
        abs_of_nonneg hq]; nlinarith
    · rw [norm_mul]; simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, hej,
        abs_of_nonneg hr]
      nlinarith
    · rw [norm_mul]; simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, hek,
        abs_of_nonneg hq]
      nlinarith
  have hIR : (I * R).re ≤ ‖R‖ := by
    calc (I * R).re ≤ ‖I * R‖ := re_le_norm _
      _ = ‖R‖ := by rw [norm_mul, norm_I, one_mul]
  have hx := abs_nonneg x; have hy := abs_nonneg y; have hz := abs_nonneg z
  have hrq := mul_nonneg hr hq
  nlinarith

/-- The cubic decay of the integrand beats any polynomial and the quadratic phase terms. -/
lemma q2t_cubic_poly_le {C : ℝ} (hC : 0 ≤ C) {r q : ℝ} (hr : 0 ≤ r) (hq : 0 ≤ q) :
    -(r ^ 3 + q ^ 3) / 2 + C * (r * q + r + q) + 2 * (r + q) + 1 ≤
      256 * (C + 2) ^ 3 + 16 * (C + 2) ^ 2 + 1 := by
  set u := r + q with hu
  set D := C + 2 with hD
  have hu0 : 0 ≤ u := by positivity
  have hD2 : 2 ≤ D := by linarith
  have h3 : u ^ 3 / 4 ≤ r ^ 3 + q ^ 3 := by
    have : r ^ 3 + q ^ 3 - u ^ 3 / 4 = 3 / 4 * u * (r - q) ^ 2 := by rw [hu]; ring
    nlinarith [mul_nonneg hu0 (sq_nonneg (r - q))]
  have h2 : r * q ≤ u ^ 2 / 4 := by rw [hu]; nlinarith [sq_nonneg (r - q)]
  have hle : -(r ^ 3 + q ^ 3) / 2 + C * (r * q + r + q) + 2 * (r + q) + 1 ≤
      -u ^ 3 / 8 + D * u ^ 2 + D * u + 1 := by
    have : C * (r * q) ≤ D * u ^ 2 := by
      calc C * (r * q) ≤ C * (u ^ 2 / 4) := mul_le_mul_of_nonneg_left h2 hC
        _ ≤ D * u ^ 2 := by nlinarith [sq_nonneg u]
    have e : C * (r * q + r + q) + 2 * (r + q) = C * (r * q) + D * u := by rw [hu, hD]; ring
    nlinarith
  refine hle.trans ?_
  rcases le_or_gt u (16 * D) with h | h
  · have hu2 : D * u ^ 2 ≤ 256 * D ^ 3 := by
      have : u ^ 2 ≤ (16 * D) ^ 2 := pow_le_pow_left₀ hu0 h 2
      nlinarith
    have hu1 : D * u ≤ 16 * D ^ 2 := by nlinarith
    nlinarith [pow_nonneg hu0 3]
  · have hu1 : 1 ≤ u := by linarith
    have e1 : D * u ^ 2 ≤ u ^ 3 / 16 := by nlinarith [sq_nonneg u]
    have e2 : D * u ≤ u ^ 3 / 16 := by nlinarith [sq_nonneg u]
    nlinarith [pow_pos (by linarith : (0 : ℝ) < D) 3, sq_nonneg D]

/-- Polynomial weights times the elliptic umbilic decay are bounded by `A e^{-r} e^{-q}`. -/
lemma q2t_poly_exp_le {C : ℝ} (hC : 0 ≤ C) (N : ℕ) {r q : ℝ} (hr : 0 ≤ r) (hq : 0 ≤ q) :
    (1 + r + q) ^ N * Real.exp (-(r ^ 3 + q ^ 3) / 2 + C * (r * q + r + q)) ≤
      (N.factorial * Real.exp (256 * (C + 2) ^ 3 + 16 * (C + 2) ^ 2 + 1)) *
        Real.exp (-r) * Real.exp (-q) := by
  have h1 : (1 + r + q) ^ N ≤ N.factorial * Real.exp (1 + r + q) := by
    have := Real.pow_div_factorial_le_exp (1 + r + q) (by positivity) N
    rw [div_le_iff₀ (by positivity)] at this
    linarith
  have hpoly := q2t_cubic_poly_le hC hr hq
  calc (1 + r + q) ^ N * Real.exp (-(r ^ 3 + q ^ 3) / 2 + C * (r * q + r + q))
      ≤ (N.factorial * Real.exp (1 + r + q)) *
          Real.exp (-(r ^ 3 + q ^ 3) / 2 + C * (r * q + r + q)) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = N.factorial * Real.exp ((-(r ^ 3 + q ^ 3) / 2 + C * (r * q + r + q) + 2 * (r + q) + 1)
          + (-r) + (-q)) := by
        rw [mul_assoc, ← Real.exp_add]; congr 2; ring
    _ ≤ N.factorial * Real.exp ((256 * (C + 2) ^ 3 + 16 * (C + 2) ^ 2 + 1) + (-r) + (-q)) := by
        gcongr
    _ = _ := by rw [Real.exp_add, Real.exp_add]; ring

/-- The weighted integrand `e_j e_k W(a, b) exp(iΦ^{(E)})` on the product of rays `ρ_j × ρ_k`,
`a = r e_j`, `b = q e_k`. -/
def q2t_integrand (W : ℂ → ℂ → ℂ) (x y z : ℝ) (j k : Fin 3) (p : ℝ × ℝ) : ℂ :=
  ellipticUmbilicRayDir j * ellipticUmbilicRayDir k *
    W ((p.1 : ℂ) * ellipticUmbilicRayDir j) ((p.2 : ℂ) * ellipticUmbilicRayDir k) *
    exp (I * ellipticUmbilicPotentialAB ((p.1 : ℂ) * ellipticUmbilicRayDir j)
      ((p.2 : ℂ) * ellipticUmbilicRayDir k) x y z)

/-- The weighted quadrant integral `∫_{ρ_j × ρ_k} W exp(iΦ^{(E)}) da db`. -/
def q2t_quad (W : ℂ → ℂ → ℂ) (x y z : ℝ) (j k : Fin 3) : ℂ :=
  ∫ p : ℝ × ℝ in Ioi 0 ×ˢ Ioi 0, q2t_integrand W x y z j k p

/-- The weighted elliptic umbilic integral `(i/2) ∑ ε_{jk} ∫_{ρ_j × ρ_k} W exp(iΦ^{(E)}) da db`,
the moment of `Ψ^{(E)}` with weight `W(a, b)`. -/
def q2t_EM (W : ℂ → ℂ → ℂ) (x y z : ℝ) : ℂ :=
  I / 2 * ∑ j : Fin 3, ∑ k : Fin 3, (ellipticUmbilicCycle j k : ℂ) * q2t_quad W x y z j k

/-- With weight `1` the weighted elliptic umbilic integral is `Ψ^{(E)}`. -/
lemma q2t_EM_one (x y z : ℝ) : q2t_EM (fun _ _ => 1) x y z = ellipticUmbilicIntegral x y z := by
  simp [q2t_EM, q2t_quad, q2t_integrand, ellipticUmbilicIntegral, ellipticUmbilicQuadrant]

/-- The elliptic umbilic potential on the product of rays `ρ_j × ρ_k` is continuous. -/
lemma q2t_continuous_potential (x y z : ℝ) (j k : Fin 3) :
    Continuous fun p : ℝ × ℝ => ellipticUmbilicPotentialAB ((p.1 : ℂ) * ellipticUmbilicRayDir j)
      ((p.2 : ℂ) * ellipticUmbilicRayDir k) x y z := by
  simp only [ellipticUmbilicPotentialAB_eq]; fun_prop

/-- The weighted integrand on `ρ_j × ρ_k` is continuous. -/
lemma q2t_continuous_integrand {W : ℂ → ℂ → ℂ} (hW : Q2tPolyBdd W) (x y z : ℝ) (j k : Fin 3) :
    Continuous (q2t_integrand W x y z j k) := by
  have h1 : Continuous fun p : ℝ × ℝ =>
      W ((p.1 : ℂ) * ellipticUmbilicRayDir j) ((p.2 : ℂ) * ellipticUmbilicRayDir k) :=
    hW.1.comp (by fun_prop : Continuous fun p : ℝ × ℝ =>
      ((p.1 : ℂ) * ellipticUmbilicRayDir j, (p.2 : ℂ) * ellipticUmbilicRayDir k))
  have h2 := q2t_continuous_potential x y z j k
  unfold q2t_integrand
  exact (continuous_const.mul h1).mul (continuous_exp.comp (continuous_const.mul h2))

/-- Uniform bound `A e^{-r} e^{-q}` for the weighted integrand, for `|x| + |y| + |z| ≤ C`. -/
lemma q2t_norm_integrand_le {W : ℂ → ℂ → ℂ} (hW : Q2tPolyBdd W) {C : ℝ} (hC : 0 ≤ C) :
    ∃ A : ℝ, ∀ x y z : ℝ, |x| + |y| + |z| ≤ C → ∀ (j k : Fin 3) (p : ℝ × ℝ), 0 ≤ p.1 → 0 ≤ p.2 →
      ‖q2t_integrand W x y z j k p‖ ≤ A * Real.exp (-p.1) * Real.exp (-p.2) := by
  obtain ⟨-, CW, hCW, N, hb⟩ := hW
  refine ⟨CW * (N.factorial * Real.exp (256 * (C + 2) ^ 3 + 16 * (C + 2) ^ 2 + 1)),
    fun x y z hxyz j k p hr hq => ?_⟩
  have hn1 : ‖(p.1 : ℂ) * ellipticUmbilicRayDir j‖ = p.1 := by
    rw [norm_mul, q2t_norm_rayDir, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr, mul_one]
  have hn2 : ‖(p.2 : ℂ) * ellipticUmbilicRayDir k‖ = p.2 := by
    rw [norm_mul, q2t_norm_rayDir, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hq, mul_one]
  have hWb := hb ((p.1 : ℂ) * ellipticUmbilicRayDir j) ((p.2 : ℂ) * ellipticUmbilicRayDir k)
  rw [hn1, hn2] at hWb
  have hE : ‖exp (I * ellipticUmbilicPotentialAB ((p.1 : ℂ) * ellipticUmbilicRayDir j)
      ((p.2 : ℂ) * ellipticUmbilicRayDir k) x y z)‖ ≤
      Real.exp (-(p.1 ^ 3 + p.2 ^ 3) / 2 + C * (p.1 * p.2 + p.1 + p.2)) := by
    rw [norm_exp]; exact Real.exp_le_exp.mpr (q2t_re_phase_le x y z hxyz j k hr hq)
  have hP := q2t_poly_exp_le hC N hr hq
  unfold q2t_integrand
  rw [norm_mul, norm_mul, norm_mul, q2t_norm_rayDir, q2t_norm_rayDir, one_mul, one_mul]
  calc _ ≤ (CW * (1 + p.1 + p.2) ^ N) *
        Real.exp (-(p.1 ^ 3 + p.2 ^ 3) / 2 + C * (p.1 * p.2 + p.1 + p.2)) :=
        mul_le_mul hWb hE (norm_nonneg _) (by positivity)
    _ = CW * ((1 + p.1 + p.2) ^ N *
        Real.exp (-(p.1 ^ 3 + p.2 ^ 3) / 2 + C * (p.1 * p.2 + p.1 + p.2))) := by ring
    _ ≤ CW * ((N.factorial * Real.exp (256 * (C + 2) ^ 3 + 16 * (C + 2) ^ 2 + 1)) *
        Real.exp (-p.1) * Real.exp (-p.2)) := mul_le_mul_of_nonneg_left hP hCW
    _ = _ := by ring

/-- `A e^{-p₁} e^{-p₂}` is integrable on the open positive quadrant. -/
lemma q2t_integrableOn_exp_prod (A : ℝ) :
    IntegrableOn (fun p : ℝ × ℝ => A * Real.exp (-p.1) * Real.exp (-p.2)) (Ioi 0 ×ˢ Ioi 0) := by
  have h1 : IntegrableOn (fun r : ℝ => Real.exp (-r)) (Ioi 0) := by
    simpa using exp_neg_integrableOn_Ioi 0 (b := 1) one_pos
  rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict]
  exact (h1.const_mul A).mul_prod h1

/-- The weighted integrand is integrable on the positive quadrant. -/
lemma q2t_integrableOn {W : ℂ → ℂ → ℂ} (hW : Q2tPolyBdd W) (x y z : ℝ) (j k : Fin 3) :
    IntegrableOn (q2t_integrand W x y z j k) (Ioi 0 ×ˢ Ioi 0) := by
  obtain ⟨A, hA⟩ := q2t_norm_integrand_le hW (C := |x| + |y| + |z|) (by positivity)
  refine (q2t_integrableOn_exp_prod A).mono'
    (q2t_continuous_integrand hW x y z j k).aestronglyMeasurable ?_
  refine ae_restrict_of_forall_mem (measurableSet_Ioi.prod measurableSet_Ioi) fun p hp => ?_
  exact hA x y z le_rfl j k p (le_of_lt hp.1) (le_of_lt hp.2)

/-- The quadrant integral is additive in the weight. -/
lemma q2t_quad_add {W₁ W₂ : ℂ → ℂ → ℂ} (h₁ : Q2tPolyBdd W₁) (h₂ : Q2tPolyBdd W₂)
    (x y z : ℝ) (j k : Fin 3) :
    q2t_quad (fun a b => W₁ a b + W₂ a b) x y z j k =
      q2t_quad W₁ x y z j k + q2t_quad W₂ x y z j k := by
  unfold q2t_quad
  rw [← integral_add (q2t_integrableOn h₁ x y z j k) (q2t_integrableOn h₂ x y z j k)]
  congr 1; funext p; unfold q2t_integrand; ring

/-- The quadrant integral is homogeneous in the weight. -/
lemma q2t_quad_const_mul (c : ℂ) (W : ℂ → ℂ → ℂ) (x y z : ℝ) (j k : Fin 3) :
    q2t_quad (fun a b => c * W a b) x y z j k = c * q2t_quad W x y z j k := by
  unfold q2t_quad
  rw [← integral_const_mul]
  congr 1; funext p; unfold q2t_integrand; ring

/-- The weighted elliptic umbilic integral is additive in the weight. -/
lemma q2t_EM_add {W₁ W₂ : ℂ → ℂ → ℂ} (h₁ : Q2tPolyBdd W₁) (h₂ : Q2tPolyBdd W₂) (x y z : ℝ) :
    q2t_EM (fun a b => W₁ a b + W₂ a b) x y z = q2t_EM W₁ x y z + q2t_EM W₂ x y z := by
  simp only [q2t_EM, q2t_quad_add h₁ h₂, mul_add, Finset.sum_add_distrib]

/-- The weighted elliptic umbilic integral is homogeneous in the weight. -/
lemma q2t_EM_const_mul (c : ℂ) (W : ℂ → ℂ → ℂ) (x y z : ℝ) :
    q2t_EM (fun a b => c * W a b) x y z = c * q2t_EM W x y z := by
  simp only [q2t_EM, q2t_quad_const_mul, Finset.mul_sum]
  congr 1; ext j; congr 1; ext k; ring

/-- The `w`-derivative of the elliptic umbilic potential along `x = x₀ + w dx`, etc. -/
def q2t_L (dx dy dz : ℝ) (a b : ℂ) : ℂ :=
  dz * a * b + (dx - I * dy) / 2 * a + (dx + I * dy) / 2 * b

/-- The linear form `q2t_L dx dy dz` is polynomially bounded. -/
lemma q2t_polyBdd_L (dx dy dz : ℝ) : Q2tPolyBdd (q2t_L dx dy dz) := by
  unfold q2t_L
  refine q2t_polyBdd_add (q2t_polyBdd_add ?_ ?_) ?_
  · exact q2t_polyBdd_mul (q2t_polyBdd_mul (q2t_polyBdd_const _) q2t_polyBdd_fst) q2t_polyBdd_snd
  · exact q2t_polyBdd_mul (q2t_polyBdd_const _) q2t_polyBdd_fst
  · exact q2t_polyBdd_mul (q2t_polyBdd_const _) q2t_polyBdd_snd

/-- `Φ^{(E)}` is affine along the line `(x₀, y₀, z₀) + w (dx, dy, dz)` with slope `q2t_L dx dy dz`.
-/
lemma q2t_potential_affine (a b : ℂ) (x₀ y₀ z₀ dx dy dz w : ℝ) :
    ellipticUmbilicPotentialAB a b (x₀ + w * dx) (y₀ + w * dy) (z₀ + w * dz) =
      ellipticUmbilicPotentialAB a b x₀ y₀ z₀ + (w : ℂ) * q2t_L dx dy dz a b := by
  rw [ellipticUmbilicPotentialAB_eq, ellipticUmbilicPotentialAB_eq, q2t_L]; push_cast; ring

/-- Differentiation under the integral sign along an affine path in the parameters. -/
lemma q2t_hasDerivAt_quad {W : ℂ → ℂ → ℂ} (hW : Q2tPolyBdd W) (x₀ y₀ z₀ dx dy dz w₀ : ℝ)
    (j k : Fin 3) :
    HasDerivAt (fun w : ℝ => q2t_quad W (x₀ + w * dx) (y₀ + w * dy) (z₀ + w * dz) j k)
      (q2t_quad (fun a b => W a b * (I * q2t_L dx dy dz a b))
        (x₀ + w₀ * dx) (y₀ + w₀ * dy) (z₀ + w₀ * dz) j k) w₀ := by
  have hW' : Q2tPolyBdd fun a b => W a b * (I * q2t_L dx dy dz a b) :=
    q2t_polyBdd_mul hW (q2t_polyBdd_mul (q2t_polyBdd_const I) (q2t_polyBdd_L dx dy dz))
  set C := |x₀| + |y₀| + |z₀| + (|w₀| + 1) * (|dx| + |dy| + |dz|) with hCdef
  have hC : 0 ≤ C := by positivity
  obtain ⟨A, hA⟩ := q2t_norm_integrand_le hW' hC
  have hball : ∀ w ∈ Metric.ball w₀ 1,
      |x₀ + w * dx| + |y₀ + w * dy| + |z₀ + w * dz| ≤ C := by
    intro w hw
    rw [Metric.mem_ball, Real.dist_eq] at hw
    have hw' : |w| ≤ |w₀| + 1 := by
      have := abs_sub_abs_le_abs_sub w w₀; linarith
    have e1 : |x₀ + w * dx| ≤ |x₀| + |w| * |dx| := (abs_add_le _ _).trans (by rw [abs_mul])
    have e2 : |y₀ + w * dy| ≤ |y₀| + |w| * |dy| := (abs_add_le _ _).trans (by rw [abs_mul])
    have e3 : |z₀ + w * dz| ≤ |z₀| + |w| * |dz| := (abs_add_le _ _).trans (by rw [abs_mul])
    have : |w| * (|dx| + |dy| + |dz|) ≤ (|w₀| + 1) * (|dx| + |dy| + |dz|) :=
      mul_le_mul_of_nonneg_right hw' (by positivity)
    rw [hCdef]; nlinarith
  have hmeas : MeasurableSet (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) :=
    measurableSet_Ioi.prod measurableSet_Ioi
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds w₀ one_pos)
    (F := fun w p => q2t_integrand W (x₀ + w * dx) (y₀ + w * dy) (z₀ + w * dz) j k p)
    (F' := fun w p => q2t_integrand (fun a b => W a b * (I * q2t_L dx dy dz a b))
      (x₀ + w * dx) (y₀ + w * dy) (z₀ + w * dz) j k p)
    (bound := fun p => A * Real.exp (-p.1) * Real.exp (-p.2))
    (Eventually.of_forall fun w =>
      (q2t_continuous_integrand hW _ _ _ j k).aestronglyMeasurable)
    (q2t_integrableOn hW _ _ _ j k)
    (q2t_continuous_integrand hW' _ _ _ j k).aestronglyMeasurable
    (ae_restrict_of_forall_mem hmeas fun p hp w hw =>
      hA _ _ _ (hball w hw) j k p (le_of_lt hp.1) (le_of_lt hp.2))
    (q2t_integrableOn_exp_prod A) (ae_of_all _ fun p w _ => ?_)).2
  -- pointwise derivative
  set a : ℂ := (p.1 : ℂ) * ellipticUmbilicRayDir j
  set b : ℂ := (p.2 : ℂ) * ellipticUmbilicRayDir k
  set c : ℂ := ellipticUmbilicRayDir j * ellipticUmbilicRayDir k * W a b
  set P₀ := ellipticUmbilicPotentialAB a b x₀ y₀ z₀
  set L := q2t_L dx dy dz a b
  have hfun : (fun w : ℝ => q2t_integrand W (x₀ + w * dx) (y₀ + w * dy) (z₀ + w * dz) j k p) =
      fun w : ℝ => c * exp (I * (P₀ + (w : ℂ) * L)) := by
    funext w; simp only [q2t_integrand, q2t_potential_affine]; rfl
  have hval : q2t_integrand (fun a b => W a b * (I * q2t_L dx dy dz a b))
      (x₀ + w * dx) (y₀ + w * dy) (z₀ + w * dz) j k p =
      c * (exp (I * (P₀ + id (w : ℂ) * L)) * (I * (1 * L))) := by
    simp only [q2t_integrand, q2t_potential_affine]
    simp only [c, P₀, L, a, b, id]; ring
  rw [hfun, hval]
  exact ((((hasDerivAt_id (w : ℂ)).mul_const L).const_add P₀).const_mul I).cexp.const_mul c
    |>.comp_ofReal

/-- Differentiation of the weighted elliptic umbilic integral along an affine path. -/
lemma q2t_hasDerivAt_EM {W : ℂ → ℂ → ℂ} (hW : Q2tPolyBdd W) (x₀ y₀ z₀ dx dy dz w₀ : ℝ) :
    HasDerivAt (fun w : ℝ => q2t_EM W (x₀ + w * dx) (y₀ + w * dy) (z₀ + w * dz))
      (q2t_EM (fun a b => W a b * (I * q2t_L dx dy dz a b))
        (x₀ + w₀ * dx) (y₀ + w₀ * dy) (z₀ + w₀ * dz)) w₀ := by
  unfold q2t_EM
  refine HasDerivAt.const_mul _ (HasDerivAt.fun_sum fun j _ => HasDerivAt.fun_sum fun k _ => ?_)
  exact (q2t_hasDerivAt_quad hW x₀ y₀ z₀ dx dy dz w₀ j k).const_mul _

/-- Differentiation under the integral sign in `x` for the weighted elliptic umbilic integral. -/
lemma q2t_hasDerivAt_EM_x {W : ℂ → ℂ → ℂ} (hW : Q2tPolyBdd W) (x y z : ℝ) :
    HasDerivAt (fun s : ℝ => q2t_EM W s y z)
      (q2t_EM (fun a b => W a b * (I * q2t_L 1 0 0 a b)) x y z) x := by
  have h := q2t_hasDerivAt_EM hW 0 y z 1 0 0 x
  simp only [zero_add, mul_one, mul_zero, add_zero] at h
  exact h

/-- Differentiation under the integral sign in `y` for the weighted elliptic umbilic integral. -/
lemma q2t_hasDerivAt_EM_y {W : ℂ → ℂ → ℂ} (hW : Q2tPolyBdd W) (x y z : ℝ) :
    HasDerivAt (fun t : ℝ => q2t_EM W x t z)
      (q2t_EM (fun a b => W a b * (I * q2t_L 0 1 0 a b)) x y z) y := by
  have h := q2t_hasDerivAt_EM hW x 0 z 0 1 0 y
  simp only [zero_add, mul_one, mul_zero, add_zero] at h
  exact h

/-- Differentiation under the integral sign in `z` for the weighted elliptic umbilic integral. -/
lemma q2t_hasDerivAt_EM_z {W : ℂ → ℂ → ℂ} (hW : Q2tPolyBdd W) (x y z : ℝ) :
    HasDerivAt (fun w : ℝ => q2t_EM W x y w)
      (q2t_EM (fun a b => W a b * (I * q2t_L 0 0 1 a b)) x y z) z := by
  have h := q2t_hasDerivAt_EM hW x y 0 0 0 1 z
  simp only [zero_add, mul_one, mul_zero, add_zero] at h
  exact h

/-- Multiplying a polynomially bounded weight by `i q2t_L dx dy dz` keeps it polynomially bounded.
-/
lemma q2t_polyBdd_mulL {W : ℂ → ℂ → ℂ} (hW : Q2tPolyBdd W) (dx dy dz : ℝ) :
    Q2tPolyBdd fun a b => W a b * (I * q2t_L dx dy dz a b) :=
  q2t_polyBdd_mul hW (q2t_polyBdd_mul (q2t_polyBdd_const I) (q2t_polyBdd_L dx dy dz))

/-- Integration by parts along a ray `r ↦ r e`, `r > 0`, for `exp(iP)` decaying at infinity. -/
lemma q2t_ray_ibp {P P' : ℂ → ℂ} (hP : ∀ u, HasDerivAt P (P' u) u) (e : ℂ)
    (hint : IntegrableOn (fun r : ℝ => e * P' ((r : ℂ) * e) * exp (I * P ((r : ℂ) * e))) (Ioi 0))
    (htend : Tendsto (fun r : ℝ => exp (I * P ((r : ℂ) * e))) atTop (𝓝 0)) :
    ∫ r in Ioi (0 : ℝ), e * P' ((r : ℂ) * e) * exp (I * P ((r : ℂ) * e)) = I * exp (I * P 0) := by
  have hd : ∀ r : ℝ, HasDerivAt (fun r : ℝ => -I * exp (I * P ((r : ℂ) * e)))
      (e * P' ((r : ℂ) * e) * exp (I * P ((r : ℂ) * e))) r := by
    intro r
    have h1 : HasDerivAt (fun u : ℂ => -I * exp (I * P (u * e)))
        (-I * (exp (I * P ((r : ℂ) * e)) * (I * (P' ((r : ℂ) * e) * (1 * e))))) (r : ℂ) :=
      ((((hP _).comp (r : ℂ) ((hasDerivAt_id (r : ℂ)).mul_const e)).const_mul I).cexp).const_mul
        (-I)
    have h2 := h1.comp_ofReal
    convert h2 using 1
    linear_combination (e * P' ((r : ℂ) * e) * exp (I * P ((r : ℂ) * e))) * I_sq
  have h := integral_Ioi_of_hasDerivAt_of_tendsto (a := 0) (m := 0)
    (hd 0).continuousAt.continuousWithinAt (fun r _ => hd r) hint
    (by simpa using htend.const_mul (-I))
  rw [h]; simp

/-- Slices of the weighted integrand are integrable. -/
lemma q2t_integrableOn_slice_fst {W : ℂ → ℂ → ℂ} (hW : Q2tPolyBdd W) (x y z : ℝ) (j k : Fin 3)
    {q : ℝ} (hq : 0 ≤ q) :
    IntegrableOn (fun r : ℝ => q2t_integrand W x y z j k (r, q)) (Ioi 0) := by
  obtain ⟨A, hA⟩ := q2t_norm_integrand_le hW (C := |x| + |y| + |z|) (by positivity)
  have h1 : IntegrableOn (fun r : ℝ => A * Real.exp (-q) * Real.exp (-r)) (Ioi 0) := by
    have := (exp_neg_integrableOn_Ioi 0 (b := 1) one_pos).const_mul (A * Real.exp (-q))
    simp only [neg_mul, one_mul] at this; exact this
  refine h1.mono' ((q2t_continuous_integrand hW x y z j k).comp
    (by fun_prop : Continuous fun r : ℝ => (r, q))).aestronglyMeasurable ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioi fun r hr => ?_
  have := hA x y z le_rfl j k (r, q) (le_of_lt hr) hq
  simp only at this; linarith

/-- For fixed `r ≥ 0` the weighted integrand is integrable in the second ray variable. -/
lemma q2t_integrableOn_slice_snd {W : ℂ → ℂ → ℂ} (hW : Q2tPolyBdd W) (x y z : ℝ) (j k : Fin 3)
    {r : ℝ} (hr : 0 ≤ r) :
    IntegrableOn (fun q : ℝ => q2t_integrand W x y z j k (r, q)) (Ioi 0) := by
  obtain ⟨A, hA⟩ := q2t_norm_integrand_le hW (C := |x| + |y| + |z|) (by positivity)
  have h1 : IntegrableOn (fun q : ℝ => A * Real.exp (-r) * Real.exp (-q)) (Ioi 0) := by
    have := (exp_neg_integrableOn_Ioi 0 (b := 1) one_pos).const_mul (A * Real.exp (-r))
    simp only [neg_mul, one_mul] at this; exact this
  refine h1.mono' ((q2t_continuous_integrand hW x y z j k).comp
    (by fun_prop : Continuous fun q : ℝ => (r, q))).aestronglyMeasurable ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioi fun q hq => ?_
  exact hA x y z le_rfl j k (r, q) hr (le_of_lt hq)

/-- `exp(iΦ^{(E)})` decays along each ray. -/
lemma q2t_norm_exp_le (x y z : ℝ) (j k : Fin 3) :
    ∃ A : ℝ, ∀ r q : ℝ, 0 ≤ r → 0 ≤ q →
      ‖exp (I * ellipticUmbilicPotentialAB ((r : ℂ) * ellipticUmbilicRayDir j)
        ((q : ℂ) * ellipticUmbilicRayDir k) x y z)‖ ≤ A * Real.exp (-r) * Real.exp (-q) := by
  obtain ⟨A, hA⟩ := q2t_norm_integrand_le (q2t_polyBdd_const 1) (C := |x| + |y| + |z|)
    (by positivity)
  refine ⟨A, fun r q hr hq => ?_⟩
  have := hA x y z le_rfl j k (r, q) hr hq
  simpa [q2t_integrand, norm_mul, q2t_norm_rayDir] using this

/-- For fixed `q ≥ 0` the phase factor `exp(iΦ^{(E)})` tends to `0` along the first ray. -/
lemma q2t_tendsto_exp_fst (x y z : ℝ) (j k : Fin 3) {q : ℝ} (hq : 0 ≤ q) :
    Tendsto (fun r : ℝ => exp (I * ellipticUmbilicPotentialAB ((r : ℂ) * ellipticUmbilicRayDir j)
      ((q : ℂ) * ellipticUmbilicRayDir k) x y z)) atTop (𝓝 0) := by
  obtain ⟨A, hA⟩ := q2t_norm_exp_le x y z j k
  have h0 : Tendsto (fun r : ℝ => A * Real.exp (-q) * Real.exp (-r)) atTop (𝓝 0) := by
    simpa using Real.tendsto_exp_neg_atTop_nhds_zero.const_mul (A * Real.exp (-q))
  refine squeeze_zero_norm' ?_ h0
  filter_upwards [eventually_ge_atTop 0] with r hr
  have := hA r q hr hq; linarith

/-- For fixed `r ≥ 0` the phase factor `exp(iΦ^{(E)})` tends to `0` along the second ray. -/
lemma q2t_tendsto_exp_snd (x y z : ℝ) (j k : Fin 3) {r : ℝ} (hr : 0 ≤ r) :
    Tendsto (fun q : ℝ => exp (I * ellipticUmbilicPotentialAB ((r : ℂ) * ellipticUmbilicRayDir j)
      ((q : ℂ) * ellipticUmbilicRayDir k) x y z)) atTop (𝓝 0) := by
  obtain ⟨A, hA⟩ := q2t_norm_exp_le x y z j k
  have h0 : Tendsto (fun q : ℝ => A * Real.exp (-r) * Real.exp (-q)) atTop (𝓝 0) := by
    simpa using Real.tendsto_exp_neg_atTop_nhds_zero.const_mul (A * Real.exp (-r))
  refine squeeze_zero_norm' ?_ h0
  filter_upwards [eventually_ge_atTop 0] with q hq
  exact hA r q hr hq

/-- Polynomial boundedness transfers along pointwise equality of weights. -/
lemma q2t_polyBdd_congr {W W' : ℂ → ℂ → ℂ} (h : Q2tPolyBdd W) (e : ∀ a b, W a b = W' a b) :
    Q2tPolyBdd W' := by
  have : W = W' := funext fun a => funext fun b => e a b
  exact this ▸ h

/-- `∂Φ^{(E)}/∂a = 3a²/2 + zb + (x - iy)/2`. -/
def q2t_Wa (x y z : ℝ) (a b : ℂ) : ℂ := 3 * a ^ 2 / 2 + z * b + (x - I * y) / 2

/-- `∂Φ^{(E)}/∂b = 3b²/2 + za + (x + iy)/2`. -/
def q2t_Wb (x y z : ℝ) (a b : ℂ) : ℂ := 3 * b ^ 2 / 2 + z * a + (x + I * y) / 2

/-- The weight `∂Φ^{(E)}/∂a` is polynomially bounded. -/
lemma q2t_polyBdd_Wa (x y z : ℝ) : Q2tPolyBdd (q2t_Wa x y z) := by
  refine q2t_polyBdd_congr (q2t_polyBdd_add (q2t_polyBdd_add (q2t_polyBdd_mul
    (q2t_polyBdd_const (3 / 2)) (q2t_polyBdd_mul q2t_polyBdd_fst q2t_polyBdd_fst))
    (q2t_polyBdd_mul (q2t_polyBdd_const (z : ℂ)) q2t_polyBdd_snd))
    (q2t_polyBdd_const (((x : ℂ) - I * y) / 2))) fun a b => ?_
  simp only [q2t_Wa]; ring

/-- The weight `∂Φ^{(E)}/∂b` is polynomially bounded. -/
lemma q2t_polyBdd_Wb (x y z : ℝ) : Q2tPolyBdd (q2t_Wb x y z) := by
  refine q2t_polyBdd_congr (q2t_polyBdd_add (q2t_polyBdd_add (q2t_polyBdd_mul
    (q2t_polyBdd_const (3 / 2)) (q2t_polyBdd_mul q2t_polyBdd_snd q2t_polyBdd_snd))
    (q2t_polyBdd_mul (q2t_polyBdd_const (z : ℂ)) q2t_polyBdd_fst))
    (q2t_polyBdd_const (((x : ℂ) + I * y) / 2))) fun a b => ?_
  simp only [q2t_Wb]; ring

/-- The `a`-derivative of `Φ^{(E)}` is `q2t_Wa`. -/
lemma q2t_hasDerivAt_potential_a (x y z : ℝ) (b u : ℂ) :
    HasDerivAt (fun u => ellipticUmbilicPotentialAB u b x y z) (q2t_Wa x y z u b) u := by
  simp only [ellipticUmbilicPotentialAB_eq, q2t_Wa]
  have h := ((((hasDerivAt_pow 3 u).add_const (b ^ 3)).div_const 2).add
    (((hasDerivAt_id u).const_mul ((z : ℂ))).mul_const b)).add
    (((hasDerivAt_id u).const_mul (((x : ℂ) - I * y) / 2)).add_const (((x : ℂ) + I * y) / 2 * b))
  convert h using 1
  · funext v; simp only [Pi.add_apply, id]; ring
  · push_cast; ring

/-- The `b`-derivative of `Φ^{(E)}` is `q2t_Wb`. -/
lemma q2t_hasDerivAt_potential_b (x y z : ℝ) (a u : ℂ) :
    HasDerivAt (fun u => ellipticUmbilicPotentialAB a u x y z) (q2t_Wb x y z a u) u := by
  simp only [ellipticUmbilicPotentialAB_eq, q2t_Wb]
  have h := ((((hasDerivAt_pow 3 u).const_add (a ^ 3)).div_const 2).add
    (((hasDerivAt_id u).const_mul ((z : ℂ) * a)))).add
    (((hasDerivAt_id u).const_mul (((x : ℂ) + I * y) / 2)).const_add (((x : ℂ) - I * y) / 2 * a))
  convert h using 1
  · funext v; simp only [Pi.add_apply, id]; ring
  · push_cast; ring

/-- The weighted integrand is integrable for the product of the restricted measures. -/
lemma q2t_integrable_prod {W : ℂ → ℂ → ℂ} (hW : Q2tPolyBdd W) (x y z : ℝ) (j k : Fin 3) :
    Integrable (q2t_integrand W x y z j k)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  have h := q2t_integrableOn hW x y z j k
  rwa [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] at h

/-- Integration by parts in `a`: the quadrant integral of `∂Φ/∂a` is independent of `j`. -/
lemma q2t_quad_Wa (x y z : ℝ) (j k : Fin 3) :
    q2t_quad (q2t_Wa x y z) x y z j k = ∫ q in Ioi (0 : ℝ),
      ellipticUmbilicRayDir k * (I * exp (I * ellipticUmbilicPotentialAB 0
        ((q : ℂ) * ellipticUmbilicRayDir k) x y z)) := by
  unfold q2t_quad
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict,
    integral_prod_symm _ (q2t_integrable_prod (q2t_polyBdd_Wa x y z) x y z j k)]
  refine setIntegral_congr_fun measurableSet_Ioi fun q hq => ?_
  set ej := ellipticUmbilicRayDir j
  set ek := ellipticUmbilicRayDir k
  set P : ℂ → ℂ := fun u => ellipticUmbilicPotentialAB u ((q : ℂ) * ek) x y z
  set P' : ℂ → ℂ := fun u => q2t_Wa x y z u ((q : ℂ) * ek)
  have hfun : (fun r : ℝ => q2t_integrand (q2t_Wa x y z) x y z j k (r, q)) =
      fun r : ℝ => ek * (ej * P' ((r : ℂ) * ej) * exp (I * P ((r : ℂ) * ej))) := by
    funext r; simp only [q2t_integrand, P, P', ej, ek]; ring
  rw [hfun, integral_const_mul]
  have hint : IntegrableOn (fun r : ℝ => ej * P' ((r : ℂ) * ej) * exp (I * P ((r : ℂ) * ej)))
      (Ioi 0) := by
    have h := (q2t_integrableOn_slice_fst (q2t_polyBdd_Wa x y z) x y z j k
      (le_of_lt (mem_Ioi.mp hq))).const_mul ek⁻¹
    refine IntegrableOn.congr_fun h (fun r _ => ?_) measurableSet_Ioi
    have hek : ek ≠ 0 := q2t_rayDir_ne_zero k
    simp only [q2t_integrand, P, P', ej, ek] at hek ⊢
    field_simp
  rw [q2t_ray_ibp (fun u => q2t_hasDerivAt_potential_a x y z _ u) ej hint
    (q2t_tendsto_exp_fst x y z j k (le_of_lt (mem_Ioi.mp hq)))]

/-- Integration by parts in `b`: the quadrant integral of `∂Φ/∂b` is independent of `k`. -/
lemma q2t_quad_Wb (x y z : ℝ) (j k : Fin 3) :
    q2t_quad (q2t_Wb x y z) x y z j k = ∫ r in Ioi (0 : ℝ),
      ellipticUmbilicRayDir j * (I * exp (I * ellipticUmbilicPotentialAB
        ((r : ℂ) * ellipticUmbilicRayDir j) 0 x y z)) := by
  unfold q2t_quad
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict,
    integral_prod _ (q2t_integrable_prod (q2t_polyBdd_Wb x y z) x y z j k)]
  refine setIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
  set ej := ellipticUmbilicRayDir j
  set ek := ellipticUmbilicRayDir k
  set P : ℂ → ℂ := fun u => ellipticUmbilicPotentialAB ((r : ℂ) * ej) u x y z
  set P' : ℂ → ℂ := fun u => q2t_Wb x y z ((r : ℂ) * ej) u
  have hfun : (fun q : ℝ => q2t_integrand (q2t_Wb x y z) x y z j k (r, q)) =
      fun q : ℝ => ej * (ek * P' ((q : ℂ) * ek) * exp (I * P ((q : ℂ) * ek))) := by
    funext q; simp only [q2t_integrand, P, P', ej, ek]; ring
  rw [hfun, integral_const_mul]
  have hint : IntegrableOn (fun q : ℝ => ek * P' ((q : ℂ) * ek) * exp (I * P ((q : ℂ) * ek)))
      (Ioi 0) := by
    have h := (q2t_integrableOn_slice_snd (q2t_polyBdd_Wb x y z) x y z j k
      (le_of_lt (mem_Ioi.mp hr))).const_mul ej⁻¹
    refine IntegrableOn.congr_fun h (fun q _ => ?_) measurableSet_Ioi
    have hej : ej ≠ 0 := q2t_rayDir_ne_zero j
    simp only [q2t_integrand, P, P', ej, ek] at hej ⊢
    field_simp
  rw [q2t_ray_ibp (fun u => q2t_hasDerivAt_potential_b x y z _ u) ek hint
    (q2t_tendsto_exp_snd x y z j k (le_of_lt (mem_Ioi.mp hr)))]

/-- `∫_{cycle} (∂Φ^{(E)}/∂a) exp(iΦ^{(E)}) = 0`: the boundary terms cancel since the columns of
`ε` sum to zero. -/
lemma q2t_EM_Wa (x y z : ℝ) : q2t_EM (q2t_Wa x y z) x y z = 0 := by
  simp only [q2t_EM, q2t_quad_Wa, Fin.sum_univ_three]
  simp [ellipticUmbilicCycle]
  ring

/-- `∫_{cycle} (∂Φ^{(E)}/∂b) exp(iΦ^{(E)}) = 0` (the rows of `ε` sum to zero). -/
lemma q2t_EM_Wb (x y z : ℝ) : q2t_EM (q2t_Wb x y z) x y z = 0 := by
  simp only [q2t_EM, q2t_quad_Wb, Fin.sum_univ_three]
  simp [ellipticUmbilicCycle]

/-- The `x`-derivative of the weighted elliptic umbilic integral multiplies the weight by `i q2t_L 1
0 0`. -/
lemma q2t_deriv_EM_x {W : ℂ → ℂ → ℂ} (hW : Q2tPolyBdd W) (y z : ℝ) :
    deriv (fun s : ℝ => q2t_EM W s y z) =
      fun x => q2t_EM (fun a b => W a b * (I * q2t_L 1 0 0 a b)) x y z :=
  funext fun x => (q2t_hasDerivAt_EM_x hW x y z).deriv

/-- The `y`-derivative of the weighted elliptic umbilic integral multiplies the weight by `i q2t_L 0
1 0`. -/
lemma q2t_deriv_EM_y {W : ℂ → ℂ → ℂ} (hW : Q2tPolyBdd W) (x z : ℝ) :
    deriv (fun t : ℝ => q2t_EM W x t z) =
      fun y => q2t_EM (fun a b => W a b * (I * q2t_L 0 1 0 a b)) x y z :=
  funext fun y => (q2t_hasDerivAt_EM_y hW x y z).deriv

/-- The `z`-derivative of the weighted elliptic umbilic integral multiplies the weight by `i q2t_L 0
0 1`. -/
lemma q2t_deriv_EM_z {W : ℂ → ℂ → ℂ} (hW : Q2tPolyBdd W) (x y : ℝ) :
    deriv (fun w : ℝ => q2t_EM W x y w) =
      fun z => q2t_EM (fun a b => W a b * (I * q2t_L 0 0 1 a b)) x y z :=
  funext fun z => (q2t_hasDerivAt_EM_z hW x y z).deriv

/-- The weighted elliptic umbilic integral depends only on the weight's values. -/
lemma q2t_EM_congr {W W' : ℂ → ℂ → ℂ} (e : ∀ a b, W a b = W' a b) (x y z : ℝ) :
    q2t_EM W x y z = q2t_EM W' x y z := by
  have : W = W' := funext fun a => funext fun b => e a b
  rw [this]

/-- Scalar multiples of polynomially bounded weights are polynomially bounded. -/
lemma q2t_polyBdd_cmul {W : ℂ → ℂ → ℂ} (hW : Q2tPolyBdd W) (c : ℂ) :
    Q2tPolyBdd fun a b => c * W a b := q2t_polyBdd_mul (q2t_polyBdd_const c) hW

/-- The combination `i(∂Φ/∂a - ∂Φ/∂b) = ∂Φ/∂t` integrates to zero. -/
lemma q2t_EM_Wt (x y z : ℝ) :
    q2t_EM (fun a b => I * q2t_Wa x y z a b + (-I) * q2t_Wb x y z a b) x y z = 0 := by
  rw [q2t_EM_add (q2t_polyBdd_cmul (q2t_polyBdd_Wa x y z) _)
    (q2t_polyBdd_cmul (q2t_polyBdd_Wb x y z) _), q2t_EM_const_mul, q2t_EM_const_mul,
    q2t_EM_Wa, q2t_EM_Wb]
  ring

/-- The combination `∂Φ/∂a + ∂Φ/∂b = ∂Φ/∂s` integrates to zero. -/
lemma q2t_EM_Ws (x y z : ℝ) :
    q2t_EM (fun a b => q2t_Wa x y z a b + q2t_Wb x y z a b) x y z = 0 := by
  rw [q2t_EM_add (q2t_polyBdd_Wa x y z) (q2t_polyBdd_Wb x y z), q2t_EM_Wa, q2t_EM_Wb]
  ring

/-! ### §36.10(iii)–(iv): umbilics

The operator equations 36.10.11, `Φ_s^{(U)}(-i∂/∂x, -i∂/∂y; x)Ψ^{(U)} = 0` and
`Φ_t^{(U)}(-i∂/∂x, -i∂/∂y; x)Ψ^{(U)} = 0` with `Φ_s = ∂Φ/∂s`, `Φ_t = ∂Φ/∂t` (36.10.12), are, written
out, 36.10.13–36.10.14 for `U = E` (`Φ_t^{(E)} = -6st + 2zt + y`, `Φ_s^{(E)} = 3s² - 3t² + 2zs + x`)
and 36.10.15–36.10.16 for `U = H` (`Φ_s^{(H)} = 3s² + zt + x`, `Φ_t^{(H)} = 3t² + zs + y`); the
substitution `s ↦ -i∂/∂x`, `t ↦ -i∂/∂y` and multiplication by `-1` give the printed forms. They are
tagged on those four statements. -/

/-- The elliptic umbilic equation from `Φ_t^{(E)}` (DLMF 36.10.13, and 36.10.11–36.10.12):
`6 ∂²Ψ^{(E)}/∂x∂y - 2iz ∂Ψ^{(E)}/∂y + yΨ^{(E)} = 0`. -/
@[dlmf 36.10.E13, dlmf 36.10.E11, dlmf 36.10.E12]
theorem ellipticUmbilicIntegral_pde_xy (x y z : ℝ) :
    6 * deriv (fun s => deriv (fun t => ellipticUmbilicIntegral s t z) y) x -
      2 * I * z * deriv (fun t => ellipticUmbilicIntegral x t z) y +
      y * ellipticUmbilicIntegral x y z = 0 := by
  have h1 := q2t_polyBdd_const (1 : ℂ)
  have hy := q2t_polyBdd_mulL h1 0 1 0
  have hyx := q2t_polyBdd_mulL hy 1 0 0
  simp only [← q2t_EM_one, q2t_deriv_EM_y h1, q2t_deriv_EM_x hy]
  have e := q2t_EM_add (q2t_polyBdd_cmul hyx 6)
    (q2t_polyBdd_add (q2t_polyBdd_cmul hy (-(2 * I * z))) (q2t_polyBdd_cmul h1 y)) x y z
  rw [q2t_EM_const_mul 6 (fun a b => 1 * (I * q2t_L 0 1 0 a b) * (I * q2t_L 1 0 0 a b)),
    q2t_EM_add (q2t_polyBdd_cmul hy _) (q2t_polyBdd_cmul h1 _),
    q2t_EM_const_mul (-(2 * I * z)) (fun a b => 1 * (I * q2t_L 0 1 0 a b)),
    q2t_EM_const_mul (y : ℂ) (fun _ _ => 1)] at e
  rw [q2t_EM_congr (W' := fun a b => I * q2t_Wa x y z a b + (-I) * q2t_Wb x y z a b)
    (fun a b => ?_), q2t_EM_Wt] at e
  · linear_combination -e
  · simp only [q2t_L, q2t_Wa, q2t_Wb]; push_cast
    linear_combination (-(3 / 2) * (a ^ 2 - b ^ 2) * I + z * (a - b) * I + y) * I_sq

/-- The elliptic umbilic equation from `Φ_s^{(E)}` (DLMF 36.10.14, and 36.10.11–36.10.12):
`3(∂²Ψ^{(E)}/∂x² - ∂²Ψ^{(E)}/∂y²) + 2iz ∂Ψ^{(E)}/∂x - xΨ^{(E)} = 0`, as corrected in DLMF
version 1.0.1 (the term `2iz ∂Ψ^{(E)}/∂x` originally appeared with `Ψ^{(H)}`). -/
@[dlmf 36.10.E14, dlmf 36.10.E11, dlmf 36.10.E12]
theorem ellipticUmbilicIntegral_pde_xx_yy (x y z : ℝ) :
    3 * (iteratedDeriv 2 (fun s => ellipticUmbilicIntegral s y z) x -
        iteratedDeriv 2 (fun t => ellipticUmbilicIntegral x t z) y) +
      2 * I * z * deriv (fun s => ellipticUmbilicIntegral s y z) x -
      x * ellipticUmbilicIntegral x y z = 0 := by
  have h1 := q2t_polyBdd_const (1 : ℂ)
  have hx := q2t_polyBdd_mulL h1 1 0 0
  have hy := q2t_polyBdd_mulL h1 0 1 0
  have hxx := q2t_polyBdd_mulL hx 1 0 0
  have hyy := q2t_polyBdd_mulL hy 0 1 0
  simp only [← q2t_EM_one, iteratedDeriv_succ, iteratedDeriv_zero, q2t_deriv_EM_x h1,
    q2t_deriv_EM_y h1, q2t_deriv_EM_x hx, q2t_deriv_EM_y hy]
  have e := q2t_EM_add (q2t_polyBdd_cmul hxx 3)
    (q2t_polyBdd_add (q2t_polyBdd_cmul hyy (-3))
      (q2t_polyBdd_add (q2t_polyBdd_cmul hx (2 * I * z)) (q2t_polyBdd_cmul h1 (-x)))) x y z
  rw [q2t_EM_const_mul 3 (fun a b => 1 * (I * q2t_L 1 0 0 a b) * (I * q2t_L 1 0 0 a b)),
    q2t_EM_add (q2t_polyBdd_cmul hyy _)
      (q2t_polyBdd_add (q2t_polyBdd_cmul hx _) (q2t_polyBdd_cmul h1 _)),
    q2t_EM_const_mul (-3) (fun a b => 1 * (I * q2t_L 0 1 0 a b) * (I * q2t_L 0 1 0 a b)),
    q2t_EM_add (q2t_polyBdd_cmul hx _) (q2t_polyBdd_cmul h1 _),
    q2t_EM_const_mul (2 * I * z) (fun a b => 1 * (I * q2t_L 1 0 0 a b)),
    q2t_EM_const_mul (-(x : ℂ)) (fun _ _ => 1)] at e
  rw [q2t_EM_congr (W' := fun a b => (-1) * (q2t_Wa x y z a b + q2t_Wb x y z a b))
    (fun a b => ?_), q2t_EM_const_mul (-1) (fun a b => q2t_Wa x y z a b + q2t_Wb x y z a b),
    q2t_EM_Ws] at e
  · linear_combination -e
  · simp only [q2t_L, q2t_Wa, q2t_Wb]; push_cast
    linear_combination (-(3 / 4) * (a - b) ^ 2 * I ^ 2 + 3 * (a ^ 2 + b ^ 2) / 2 + z * (a + b)) *
      I_sq

/-- The hyperbolic umbilic equation from `Φ_s^{(H)}` (DLMF 36.10.15, and 36.10.11–36.10.12):
`3 ∂²Ψ^{(H)}/∂x² + iz ∂Ψ^{(H)}/∂y - xΨ^{(H)} = 0`. -/
@[dlmf 36.10.E15, dlmf 36.10.E11, dlmf 36.10.E12]
theorem hyperbolicUmbilicIntegral_pde_x (x y z : ℝ) :
    3 * iteratedDeriv 2 (fun s => hyperbolicUmbilicIntegral s y z) x +
      I * z * deriv (fun t => hyperbolicUmbilicIntegral x t z) y -
      x * hyperbolicUmbilicIntegral x y z = 0 := by
  simp only [hyperbolicUmbilicIntegral_eq_moment, iteratedDeriv_succ, iteratedDeriv_zero,
    s36b_deriv_hyperbolicUmbilicMoment_x, s36b_deriv_hyperbolicUmbilicMoment_y]
  rw [(((hasDerivAt_hyperbolicUmbilicMoment_x x y z 1 0).const_mul I)).deriv]
  simp only [Nat.reduceAdd, zero_add]
  linear_combination (-1 : ℂ) * s36b_hyperbolic_moment_rel_s x y z +
    (3 * hyperbolicUmbilicMoment x y z 2 0 + (z : ℂ) * hyperbolicUmbilicMoment x y z 0 1) * I_sq

/-- The hyperbolic umbilic equation from `Φ_t^{(H)}` (DLMF 36.10.16, and 36.10.11–36.10.12):
`3 ∂²Ψ^{(H)}/∂y² + iz ∂Ψ^{(H)}/∂x - yΨ^{(H)} = 0`. -/
@[dlmf 36.10.E16, dlmf 36.10.E11, dlmf 36.10.E12]
theorem hyperbolicUmbilicIntegral_pde_y (x y z : ℝ) :
    3 * iteratedDeriv 2 (fun t => hyperbolicUmbilicIntegral x t z) y +
      I * z * deriv (fun s => hyperbolicUmbilicIntegral s y z) x -
      y * hyperbolicUmbilicIntegral x y z = 0 := by
  simp only [hyperbolicUmbilicIntegral_eq_moment, iteratedDeriv_succ, iteratedDeriv_zero,
    s36b_deriv_hyperbolicUmbilicMoment_x, s36b_deriv_hyperbolicUmbilicMoment_y]
  rw [(((hasDerivAt_hyperbolicUmbilicMoment_y x y z 0 1).const_mul I)).deriv]
  simp only [Nat.reduceAdd, zero_add]
  linear_combination (-1 : ℂ) * s36b_hyperbolic_moment_rel_t x y z +
    (3 * hyperbolicUmbilicMoment x y z 0 2 + (z : ℂ) * hyperbolicUmbilicMoment x y z 1 0) * I_sq

/-- The `z`-derivative of the elliptic umbilic integral (DLMF 36.10.17):
`i ∂Ψ^{(E)}/∂z = ∂²Ψ^{(E)}/∂x² + ∂²Ψ^{(E)}/∂y²`. -/
@[dlmf 36.10.E17]
theorem ellipticUmbilicIntegral_pde_z (x y z : ℝ) :
    I * deriv (fun w => ellipticUmbilicIntegral x y w) z =
      iteratedDeriv 2 (fun s => ellipticUmbilicIntegral s y z) x +
        iteratedDeriv 2 (fun t => ellipticUmbilicIntegral x t z) y := by
  have h1 := q2t_polyBdd_const (1 : ℂ)
  simp only [← q2t_EM_one, iteratedDeriv_succ, iteratedDeriv_zero, q2t_deriv_EM_x h1,
    q2t_deriv_EM_y h1, q2t_deriv_EM_z h1, q2t_deriv_EM_x (q2t_polyBdd_mulL h1 1 0 0),
    q2t_deriv_EM_y (q2t_polyBdd_mulL h1 0 1 0)]
  rw [← q2t_EM_const_mul, ← q2t_EM_add (q2t_polyBdd_mulL (q2t_polyBdd_mulL h1 1 0 0) 1 0 0)
    (q2t_polyBdd_mulL (q2t_polyBdd_mulL h1 0 1 0) 0 1 0)]
  refine q2t_EM_congr (fun a b => ?_) x y z
  simp only [q2t_L]; push_cast
  linear_combination (-I ^ 2 * (a - b) ^ 2 / 4) * I_sq

/-- The `z`-derivative of the hyperbolic umbilic integral (DLMF 36.10.18):
`i ∂Ψ^{(H)}/∂z = ∂²Ψ^{(H)}/∂x∂y`. -/
@[dlmf 36.10.E18]
theorem hyperbolicUmbilicIntegral_pde_z (x y z : ℝ) :
    I * deriv (fun w => hyperbolicUmbilicIntegral x y w) z =
      deriv (fun s => deriv (fun t => hyperbolicUmbilicIntegral s t z) y) x := by
  simp only [hyperbolicUmbilicIntegral_eq_moment]
  have hy : ∀ s, deriv (fun t => hyperbolicUmbilicMoment s t z 0 0) y =
      I * hyperbolicUmbilicMoment s y z 0 1 := fun s =>
    (hasDerivAt_hyperbolicUmbilicMoment_y s y z 0 0).deriv
  simp only [hy]
  rw [((hasDerivAt_hyperbolicUmbilicMoment_x x y z 0 1).const_mul I).deriv,
    (hasDerivAt_hyperbolicUmbilicMoment_z x y z 0 0).deriv]

end DLMF.CoalescingSaddles

end
