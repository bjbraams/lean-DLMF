/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Spheroidal.FerrersProperties
public import DLMF.Legendre.IntegralTools
public import DLMF.Spheroidal.Angular
public import Mathlib.Tactic.Monotonicity.Lemmas

/-!
# Spheroidal Ferrers recurrences and convergence

Ferrers coefficient recurrences, decay bounds and normalization of first-kind spheroidal series.

Source references and common attribution are retained in
`DLMF.Spheroidal.FerrersSeries`.
-/

@[expose] public noncomputable section

open Complex Set Filter Asymptotics DLMF.Legendre MeasureTheory

open scoped Topology Real

namespace DLMF.Spheroidal

/-- **The integral formula** (DLMF 30.8.2): for `k ≥ -R`,
`a^m_{n,k}(γ²) = (-1)^k (n+2k+1/2) (n-m+2k)!/(n+m+2k)! ∫_{-1}^1 𝖯s^m_n(x, γ²) 𝖯^m_{n+2k}(x) dx`.
Proved (definition). -/
@[dlmf 30.8.E2]
theorem spheroidalCoeff_of_le {n m : ℕ} (γ2 : ℝ) {k : ℤ} (hk : -(((n - m) / 2 : ℕ) : ℤ) ≤ k) :
    spheroidalCoeff n m γ2 k = (-1 : ℝ) ^ k * ((n : ℝ) + 2 * k + 1 / 2) *
      ((((n : ℤ) - m + 2 * k).toNat.factorial : ℝ) / (((n : ℤ) + m + 2 * k).toNat.factorial)) *
      ∫ x in (-1 : ℝ)..1, spheroidalPs n m x γ2 * (ferrersP ((n : ℂ) + 2 * k) m x).re := by
  unfold spheroidalCoeff
  simp only [hk, ↓reduceIte]
  rfl

/-- `A_{-R} = 0` (DLMF §30.8(i), note after 30.8.4). Proved. -/
@[dlmf 30.8.E4]
theorem spheroidalRecA_neg_R {n m : ℕ} (hmn : m ≤ n) (γ2 : ℝ) :
    spheroidalRecA n m γ2 (-(((n - m) / 2 : ℕ) : ℤ)) = 0 := by
  have key : ∀ R : ℕ, (n - m) / 2 = R → spheroidalRecA n m γ2 (-(R : ℤ)) = 0 := by
    intro R hR
    have h := Nat.div_add_mod (n - m) 2
    rw [hR] at h
    have hcast : (n : ℝ) - m = 2 * R + ((n - m) % 2 : ℕ) := by
      have : ((n - m : ℕ) : ℝ) = (n : ℝ) - m := by rw [Nat.cast_sub hmn]
      rw [← this]; exact_mod_cast h.symm
    unfold spheroidalRecA
    have hnum : ((n : ℝ) - m + 2 * ((-(R : ℤ) : ℤ) : ℝ) - 1) *
        ((n : ℝ) - m + 2 * ((-(R : ℤ) : ℤ) : ℝ)) = 0 := by
      rw [hcast]
      rcases Nat.mod_two_eq_zero_or_one (n - m) with h' | h' <;> rw [h'] <;> push_cast <;> ring
    rw [hnum]; ring
  exact key _ rfl

/-! #### Proof of the recurrence 30.8.4

`a^m_{n,k}` is, up to `(-1)^{k+m}(ν+1/2)(ν-m)!/(ν+m)!` with `ν = n + 2k`, the integral
`∫_{-1}^1 (1-x²)^m g(x) P_ν^{(m)}(x) dx` of the entire factor `g` of `𝖯s^m_n`. Self-adjointness of
the operator of the factor equation gives `(ν(ν+1) - λ) I_ν = γ² ∫ (1-x²)^{m+1} g P_ν^{(m)}`, and
the recurrence 14.10.3 expresses `(1-x²)𝖯^m_ν` through `𝖯^m_{ν-2}, 𝖯^m_ν, 𝖯^m_{ν+2}`. -/

/-- Self-adjointness of `L_m u = (1-x²)u'' - 2(m+1)xu'` with weight `(1-x²)^m` on `[-1, 1]`,
applied to an entire solution `g` of the factor equation and `P_N^{(m)}`: the boundary terms
vanish because of the factor `(1-x²)^{m+1}`. -/
lemma p2y_selfAdjoint {g : ℂ → ℂ} (hg : Differentiable ℂ g) (m N : ℕ) (lam γ2 : ℂ)
    (hode : ∀ z : ℂ, (1 - z ^ 2) * deriv (deriv g) z - 2 * ((m : ℂ) + 1) * z * deriv g z +
      (lam - m * ((m : ℂ) + 1) + γ2 * (1 - z ^ 2)) * g z = 0) :
    ((N : ℂ) * (N + 1) - lam) *
        ∫ x : ℝ in (-1 : ℝ)..1, (1 - (x : ℂ) ^ 2) ^ m * g x * legInt_D N m x =
      γ2 * ∫ x : ℝ in (-1 : ℝ)..1, (1 - (x : ℂ) ^ 2) ^ (m + 1) * g x * legInt_D N m x := by
  have hg1 : ∀ x : ℝ, HasDerivAt (fun x : ℝ => g x) (deriv g x) x := fun x =>
    (hg x).hasDerivAt.comp_ofReal
  have hg2 : ∀ x : ℝ, HasDerivAt (fun x : ℝ => deriv g x) (deriv (deriv g) x) x := fun x =>
    (hg.deriv x).hasDerivAt.comp_ofReal
  have hcg : Continuous fun x : ℝ => g x := hg.continuous.comp continuous_ofReal
  have hD := legInt_cont_D N m
  have hc0 : ∀ j : ℕ, Continuous fun x : ℝ => (1 - (x : ℂ) ^ 2) ^ j * g x * legInt_D N m x :=
    fun j => ((by fun_prop : Continuous fun x : ℝ => (1 - (x : ℂ) ^ 2) ^ j).mul hcg).mul hD
  have hw : ∀ x : ℝ, HasDerivAt (fun x : ℝ => (1 - (x : ℂ) ^ 2)) (-(2 * (x : ℂ))) x := by
    intro x
    have := ((hasDerivAt_id (x : ℂ)).pow 2).const_sub 1 |>.comp_ofReal
    simpa using this
  have hΦ : ∀ x ∈ uIcc (-1 : ℝ) 1, HasDerivAt
      (fun x : ℝ => (1 - (x : ℂ) ^ 2) ^ (m + 1) *
        (deriv g x * legInt_D N m x - g x * legInt_D N (m + 1) x))
      ((1 - (x : ℂ) ^ 2) ^ m * g x * legInt_D N m x *
        (((N : ℂ) * (N + 1) - lam) - γ2 * (1 - (x : ℂ) ^ 2))) x := by
    intro x _
    have h := ((hw x).pow (m + 1)).mul (((hg2 x).mul (legInt_hasDerivAt_D_real N m x)).sub
      ((hg1 x).mul (legInt_hasDerivAt_D_real N (m + 1) x)))
    refine h.congr_deriv ?_
    have h1 := hode x
    have h2 := legInt_ode N m x
    simp only [Nat.add_sub_cancel, Pi.mul_apply, Pi.sub_apply, Pi.pow_apply,
      show m + 1 + 1 = m + 2 from rfl]
    push_cast
    linear_combination (1 - (x : ℂ) ^ 2) ^ m * (legInt_D N m x * h1 - g x * h2)
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt hΦ
    (((hc0 m).mul (by fun_prop)).intervalIntegrable _ _)
  simp only [ofReal_one, ofReal_neg, one_pow, sub_self, even_two, Even.neg_pow,
    zero_pow (Nat.succ_ne_zero m), zero_mul] at hint
  have e : (fun x : ℝ => (1 - (x : ℂ) ^ 2) ^ m * g x * legInt_D N m x *
      (((N : ℂ) * (N + 1) - lam) - γ2 * (1 - (x : ℂ) ^ 2))) = fun x : ℝ =>
      ((N : ℂ) * (N + 1) - lam) * ((1 - (x : ℂ) ^ 2) ^ m * g x * legInt_D N m x) -
        γ2 * ((1 - (x : ℂ) ^ 2) ^ (m + 1) * g x * legInt_D N m x) := by
    funext x; ring
  rw [e, intervalIntegral.integral_sub, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at hint
  · linear_combination hint
  · exact (continuous_const.mul (hc0 m)).intervalIntegrable _ _
  · exact (continuous_const.mul (hc0 (m + 1))).intervalIntegrable _ _

/-- The integral of `(1-x²)^{m/2} G(x) 𝖯^m_N(x)` through the polynomial factor. -/
lemma p2y_integral_ferrers {g : ℂ → ℂ} (hreal : ∀ x : ℝ, (g x).im = 0) (m N : ℕ) :
    ∫ x in (-1 : ℝ)..1, (1 - x ^ 2) ^ ((m : ℝ) / 2) * (g x).re * (ferrersP N m x).re =
      (-1) ^ m * (∫ x : ℝ in (-1 : ℝ)..1, (1 - (x : ℂ) ^ 2) ^ m * g x * legInt_D N m x).re := by
  have hg : ∀ x : ℝ, g x = ((g x).re : ℂ) := fun x => (Complex.ext rfl (by simp [hreal x]))
  have e1 : (fun x : ℝ => (1 - (x : ℂ) ^ 2) ^ m * g x * legInt_D N m x) = fun x : ℝ =>
      (((1 - x ^ 2) ^ m * (g x).re * (legInt_D N m x).re : ℝ) : ℂ) := by
    funext x; rw [hg x, p2y_legInt_D_real]; push_cast; simp
  rw [e1, intervalIntegral.integral_ofReal, ofReal_re, ← intervalIntegral.integral_const_mul]
  apply p2y_integral_congr_Ioo
  intro x hx
  rw [legInt_ferrersP_nat_nat N m hx, p2y_legInt_D_real N m x]
  have h0 : (0:ℝ) ≤ 1 - x^2 := by nlinarith [hx.1, hx.2]
  have hr : ((1-x^2)^((m:ℝ)/2)) * ((1-x^2)^((m:ℝ)/2)) = (1-x^2)^m := by
    rw [← sq, ← Real.rpow_natCast ((1-x^2)^((m:ℝ)/2)) 2, ← Real.rpow_mul h0,
      ← Real.rpow_natCast (1-x^2) m]
    congr 1; push_cast; ring
  have hre : ((-1 : ℂ) ^ m * (((1 - x ^ 2) ^ ((m : ℝ) / 2) : ℝ) : ℂ) *
      (((legInt_D N m x).re : ℝ) : ℂ)).re =
      (-1) ^ m * (1 - x ^ 2) ^ ((m : ℝ) / 2) * (legInt_D N m x).re := by
    rw [show ((-1 : ℂ) ^ m * (((1 - x ^ 2) ^ ((m : ℝ) / 2) : ℝ) : ℂ) *
      (((legInt_D N m x).re : ℝ) : ℂ)) = (((-1) ^ m * (1 - x ^ 2) ^ ((m : ℝ) / 2) *
        (legInt_D N m x).re : ℝ) : ℂ) by push_cast; ring, ofReal_re]
  rw [hre]
  linear_combination (-1) ^ m * (g x).re * (legInt_D N m x).re * hr

/-- `(1-x²)𝖯^m_ν(x)` in terms of `𝖯^m_{ν-2}`, `𝖯^m_ν`, `𝖯^m_{ν+2}` (from DLMF 14.10.3), multiplied
by `(2ν-1)(2ν+1)(2ν+3)`. -/
lemma p2y_ferrers_one_sub_sq (ν : ℝ) (m : ℕ) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    (2 * ν - 1) * (2 * ν + 1) * (2 * ν + 3) * (1 - x ^ 2) * (ferrersP ν m x).re =
      ((2 * ν - 1) * (2 * ν + 1) * (2 * ν + 3) - ((2 * ν - 1) * (ν - m + 1) * (ν + m + 1) +
        (2 * ν + 3) * (ν + m) * (ν - m))) * (ferrersP ν m x).re -
      (2 * ν - 1) * (ν - m + 1) * (ν - m + 2) * (ferrersP ((ν : ℂ) + 2) m x).re -
      (2 * ν + 3) * (ν + m) * (ν + m - 1) * (ferrersP ((ν : ℂ) - 2) m x).re := by
  have R1 := ferrersP_recurrence_3 ((ν : ℂ) - 1) m hx
  have R2 := ferrersP_recurrence_3 (ν : ℂ) m hx
  have R3 := ferrersP_recurrence_3 ((ν : ℂ) - 2) m hx
  rw [show (ν : ℂ) - 1 + 2 = ν + 1 by ring, show (ν : ℂ) - 1 + 1 = ν by ring] at R1
  rw [show (ν : ℂ) - 2 + 2 = ν by ring, show (ν : ℂ) - 2 + 1 = ν - 1 by ring] at R3
  have hC : (((2 * ν - 1) * (2 * ν + 1) * (2 * ν + 3) * (1 - x ^ 2) : ℝ) : ℂ) * ferrersP ν m x =
      (((2 * ν - 1) * (2 * ν + 1) * (2 * ν + 3) - ((2 * ν - 1) * (ν - m + 1) * (ν + m + 1) +
        (2 * ν + 3) * (ν + m) * (ν - m)) : ℝ) : ℂ) * ferrersP ν m x -
      (((2 * ν - 1) * (ν - m + 1) * (ν - m + 2) : ℝ) : ℂ) * ferrersP ((ν : ℂ) + 2) m x -
      (((2 * ν + 3) * (ν + m) * (ν + m - 1) : ℝ) : ℂ) * ferrersP ((ν : ℂ) - 2) m x := by
    push_cast
    linear_combination (2 * (ν : ℂ) - 1) * (2 * ν + 3) * x * R1 +
      (2 * (ν : ℂ) - 1) * (ν - m + 1) * R2 + (2 * (ν : ℂ) + 3) * (ν + m) * R3
  have h := congrArg Complex.re hC
  simp only [Complex.sub_re, Complex.re_ofReal_mul] at h
  linear_combination h

/-- Pointwise form of the product `(1-x²)^{m/2} G 𝖯^m_N` on `(-1, 1)`. -/
lemma p2y_ferrers_prod {g : ℂ → ℂ} (m N : ℕ) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    (1 - x ^ 2) ^ ((m : ℝ) / 2) * (g x).re * (ferrersP N m x).re =
      (-1) ^ m * (1 - x ^ 2) ^ m * (g x).re * (legInt_D N m x).re := by
  rw [legInt_ferrersP_nat_nat N m hx, p2y_legInt_D_real N m x]
  have h0 : (0:ℝ) ≤ 1 - x^2 := by nlinarith [hx.1, hx.2]
  have hr : ((1-x^2)^((m:ℝ)/2)) * ((1-x^2)^((m:ℝ)/2)) = (1-x^2)^m := by
    rw [← sq, ← Real.rpow_natCast ((1-x^2)^((m:ℝ)/2)) 2, ← Real.rpow_mul h0,
      ← Real.rpow_natCast (1-x^2) m]
    congr 1; push_cast; ring
  have hre : ((-1 : ℂ) ^ m * (((1 - x ^ 2) ^ ((m : ℝ) / 2) : ℝ) : ℂ) *
      (((legInt_D N m x).re : ℝ) : ℂ)).re =
      (-1) ^ m * (1 - x ^ 2) ^ ((m : ℝ) / 2) * (legInt_D N m x).re := by
    rw [show ((-1 : ℂ) ^ m * (((1 - x ^ 2) ^ ((m : ℝ) / 2) : ℝ) : ℂ) *
      (((legInt_D N m x).re : ℝ) : ℂ)) = (((-1) ^ m * (1 - x ^ 2) ^ ((m : ℝ) / 2) *
        (legInt_D N m x).re : ℝ) : ℂ) by push_cast; ring, ofReal_re]
  rw [hre]
  linear_combination (-1) ^ m * (g x).re * (legInt_D N m x).re * hr

/-- Integrability of `(1-x²)^{m/2} G 𝖯^m_μ` when `𝖯^m_μ` agrees with an integer-degree one. -/
lemma p2y_ferrers_intInt {g : ℂ → ℂ} (hg : Continuous g) (m : ℕ) {μ : ℂ} (N : ℕ)
    (hμ : ∀ x ∈ Ioo (-1 : ℝ) 1, ferrersP μ m x = ferrersP N m x) :
    IntervalIntegrable (fun x : ℝ => (1 - x ^ 2) ^ ((m : ℝ) / 2) * (g x).re *
      (ferrersP μ m x).re) MeasureTheory.volume (-1) 1 := by
  have hc : Continuous fun x : ℝ => (-1 : ℝ) ^ m * (1 - x ^ 2) ^ m * (g x).re *
      (legInt_D N m x).re :=
    ((by fun_prop : Continuous fun x : ℝ => (-1 : ℝ) ^ m * (1 - x ^ 2) ^ m).mul
      (Complex.continuous_re.comp (hg.comp continuous_ofReal))).mul
      (Complex.continuous_re.comp (legInt_cont_D N m))
  refine (hc.intervalIntegrable _ _).congr_uIoo ?_
  rw [uIoo_of_le (by norm_num)]
  intro x hx
  simp only
  rw [hμ x hx, p2y_ferrers_prod m N hx]

/-- `𝖯^μ_{-N-1} = 𝖯^μ_N` (degree reflection, from the symmetry of `₂F₁`). -/
lemma p2y_ferrersP_neg_sub_one (N : ℕ) (μ : ℂ) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    ferrersP (-(N : ℂ) - 1) μ x = ferrersP N μ x := by
  have hs : 1 + (x : ℂ) ∈ slitPlane := Or.inl (by simp; linarith [hx.1])
  unfold ferrersP
  rw [show -(N : ℂ) - 1 + 1 = -N by ring, show -(-(N : ℂ) - 1) = N + 1 by ring,
    DLMF.Hypergeometric.regularizedGaussHG_symm _ _ _ (mem_cutPlane_of_one_add hs)]

/-- The core identity behind 30.8.4: self-adjointness and the recurrence of `(1-x²)𝖯^m_ν`. -/
lemma p2y_core {n m : ℕ} (hmn : m ≤ n) (γ2 : ℝ) (N : ℕ) :
    ((N : ℝ) * (N + 1) - spheroidalEigenvalue n m γ2) *
        ((2 * (N : ℝ) - 1) * (2 * N + 1) * (2 * N + 3)) *
        ∫ x in (-1 : ℝ)..1, spheroidalPs n m x γ2 * (ferrersP ((N : ℝ) : ℂ) m x).re =
      γ2 * ((((2 * (N : ℝ) - 1) * (2 * N + 1) * (2 * N + 3)) -
          ((2 * (N : ℝ) - 1) * (N - m + 1) * (N + m + 1) +
            (2 * (N : ℝ) + 3) * (N + m) * (N - m))) *
          (∫ x in (-1 : ℝ)..1, spheroidalPs n m x γ2 * (ferrersP ((N : ℝ) : ℂ) m x).re) -
        (2 * (N : ℝ) - 1) * (N - m + 1) * (N - m + 2) *
          (∫ x in (-1 : ℝ)..1, spheroidalPs n m x γ2 * (ferrersP (((N : ℝ) : ℂ) + 2) m x).re) -
        (2 * (N : ℝ) + 3) * (N + m) * (N + m - 1) *
          (∫ x in (-1 : ℝ)..1, spheroidalPs n m x γ2 *
            (ferrersP (((N : ℝ) : ℂ) - 2) m x).re)) := by
  have spec := spheroidalPsFactor_spec hmn γ2
  set g := spheroidalPsFactor n m γ2 with hgdef
  set lam := spheroidalEigenvalue n m γ2 with hlam
  have hgd : Differentiable ℂ g := spec.factor.differentiable
  have hreal := spec.real
  have hPs : ∀ x : ℝ, spheroidalPs n m x γ2 = (1 - x ^ 2) ^ ((m : ℝ) / 2) * (g x).re :=
    fun x => rfl
  simp only [hPs]
  -- the second factor `(1-z²) g`
  set g' : ℂ → ℂ := fun z => (1 - z ^ 2) * g z with hg'
  have hreal' : ∀ x : ℝ, (g' x).im = 0 := by
    intro x; simp only [hg', Complex.mul_im, hreal x]
    rw [show (1 - (x : ℂ) ^ 2) = ((1 - x ^ 2 : ℝ) : ℂ) by push_cast; ring, ofReal_im]; ring
  -- the integrals through the polynomial factor
  have hT : ∀ M : ℕ, ∫ x in (-1 : ℝ)..1, (1 - x ^ 2) ^ ((m : ℝ) / 2) * (g x).re *
      (ferrersP ((M : ℝ) : ℂ) m x).re = (-1) ^ m *
        (∫ x : ℝ in (-1 : ℝ)..1, (1 - (x : ℂ) ^ 2) ^ m * g x * legInt_D M m x).re := by
    intro M; rw [ofReal_natCast]; exact p2y_integral_ferrers hreal m M
  have hT2 : ∫ x in (-1 : ℝ)..1, (1 - x ^ 2) ^ ((m : ℝ) / 2) * (g x).re *
      ((1 - x ^ 2) * (ferrersP ((N : ℝ) : ℂ) m x).re) = (-1) ^ m *
        (∫ x : ℝ in (-1 : ℝ)..1, (1 - (x : ℂ) ^ 2) ^ (m + 1) * g x * legInt_D N m x).re := by
    have h := p2y_integral_ferrers hreal' m N
    have e1 : (fun x : ℝ => (1 - (x : ℂ) ^ 2) ^ m * g' x * legInt_D N m x) =
        fun x : ℝ => (1 - (x : ℂ) ^ 2) ^ (m + 1) * g x * legInt_D N m x := by
      funext x; simp only [hg']; ring
    have e2 : (fun x : ℝ => (1 - x ^ 2) ^ ((m : ℝ) / 2) * (g' x).re * (ferrersP N m x).re) =
        fun x : ℝ => (1 - x ^ 2) ^ ((m : ℝ) / 2) * (g x).re *
          ((1 - x ^ 2) * (ferrersP ((N : ℝ) : ℂ) m x).re) := by
      funext x
      simp only [hg', ofReal_natCast]
      rw [show (1 - (x : ℂ) ^ 2) = ((1 - x ^ 2 : ℝ) : ℂ) by push_cast; ring, re_ofReal_mul]
      ring
    rw [e1, e2] at h; exact h
  -- self-adjointness
  have hSA := p2y_selfAdjoint hgd m N (lam : ℂ) (γ2 : ℂ) spec.factor.ode
  have hSA' := congrArg Complex.re hSA
  rw [show ((N : ℂ) * (N + 1) - (lam : ℂ)) = (((N : ℝ) * (N + 1) - lam : ℝ) : ℂ) by push_cast; ring,
    re_ofReal_mul, re_ofReal_mul] at hSA'
  -- the recurrence, integrated
  have hcg : Continuous g := hgd.continuous
  have hlow : ∃ M : ℕ, ∀ x ∈ Ioo (-1 : ℝ) 1,
      ferrersP (((N : ℝ) : ℂ) - 2) m x = ferrersP M m x := by
    rcases Nat.lt_or_ge N 2 with hN | hN
    · refine ⟨1 - N, fun x hx => ?_⟩
      rw [← p2y_ferrersP_neg_sub_one _ _ hx]
      congr 1
      interval_cases N <;> simp <;> norm_num
    · refine ⟨N - 2, fun x hx => ?_⟩
      congr 1; push_cast [Nat.cast_sub hN]; ring
  obtain ⟨M, hM⟩ := hlow
  have i0 := p2y_ferrers_intInt hcg m (μ := ((N : ℝ) : ℂ)) N (fun x _ => by rw [ofReal_natCast])
  have i2 := p2y_ferrers_intInt hcg m (μ := ((N : ℝ) : ℂ) + 2) (N + 2)
    (fun x _ => by push_cast; ring_nf)
  have im := p2y_ferrers_intInt hcg m M hM
  set e : ℝ := (2 * (N : ℝ) - 1) * (2 * N + 1) * (2 * N + 3)
  have hrec : e * ∫ x in (-1 : ℝ)..1, (1 - x ^ 2) ^ ((m : ℝ) / 2) * (g x).re *
      ((1 - x ^ 2) * (ferrersP ((N : ℝ) : ℂ) m x).re) =
      (e - ((2 * (N : ℝ) - 1) * (N - m + 1) * (N + m + 1) +
          (2 * (N : ℝ) + 3) * (N + m) * (N - m))) *
          (∫ x in (-1 : ℝ)..1, (1 - x ^ 2) ^ ((m : ℝ) / 2) * (g x).re *
            (ferrersP ((N : ℝ) : ℂ) m x).re) -
        (2 * (N : ℝ) - 1) * (N - m + 1) * (N - m + 2) *
          (∫ x in (-1 : ℝ)..1, (1 - x ^ 2) ^ ((m : ℝ) / 2) * (g x).re *
            (ferrersP (((N : ℝ) : ℂ) + 2) m x).re) -
        (2 * (N : ℝ) + 3) * (N + m) * (N + m - 1) *
          (∫ x in (-1 : ℝ)..1, (1 - x ^ 2) ^ ((m : ℝ) / 2) * (g x).re *
            (ferrersP (((N : ℝ) : ℂ) - 2) m x).re) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_sub (i0.const_mul _) (i2.const_mul _),
      ← intervalIntegral.integral_sub ((i0.const_mul _).sub (i2.const_mul _)) (im.const_mul _)]
    apply p2y_integral_congr_Ioo
    intro x hx
    have h := p2y_ferrers_one_sub_sq (N : ℝ) m hx
    linear_combination (1 - x ^ 2) ^ ((m : ℝ) / 2) * (g x).re * h
  rw [hT N] at hrec ⊢
  rw [hT2] at hrec
  have hsq : ((-1 : ℝ) ^ m) * (-1) ^ m = 1 := by rw [← mul_pow]; norm_num
  linear_combination (-1) ^ m * e * hSA' + γ2 * hrec

/-- `(n+2)! = (n+2)(n+1) n!` in `ℝ`. -/
lemma p2y_factorial_two (a : ℕ) :
    (((a + 2).factorial : ℕ) : ℝ) = ((a : ℝ) + 2) * ((a : ℝ) + 1) * (a.factorial : ℝ) := by
  rw [show a + 2 = (a + 1) + 1 from rfl, Nat.factorial_succ, Nat.factorial_succ]; push_cast; ring

/-- The lowest admissible degree: `(N+m)(N+m-1) 𝖯^m_{N-2} = 0` on `(-1, 1)` when
`m ≤ N < m + 2`. -/
lemma p2y_low_vanish {m N : ℕ} (hmN : m ≤ N) (h : N < m + 2) {x : ℝ}
    (hx : x ∈ Ioo (-1 : ℝ) 1) :
    ((N : ℝ) + m) * ((N : ℝ) + m - 1) * (ferrersP (((N : ℝ) : ℂ) - 2) m x).re = 0 := by
  rcases Nat.lt_or_ge N 2 with hN | hN
  · interval_cases N
    · have : m = 0 := by omega
      subst this; norm_num
    · rcases (by omega : m = 0 ∨ m = 1) with rfl | rfl
      · norm_num
      · have h0 := p2y_ferrersP_neg_sub_one 0 (1 : ℕ) hx
        rw [ferrersP_order_gt_degree 0 1 (by norm_num) hx] at h0
        rw [show (((1 : ℕ) : ℝ) : ℂ) - 2 = -((0 : ℕ) : ℂ) - 1 by push_cast; ring, h0]
        simp
  · have h0 := ferrersP_order_gt_degree (N - 2) m (by omega) hx
    rw [show (((N : ℝ) : ℂ) - 2) = ((N - 2 : ℕ) : ℂ) by push_cast [Nat.cast_sub hN]; ring, h0]
    simp

/-- The algebra of 30.8.4 at the lowest index `k = -R`. -/
lemma p2y_alg_low (n k m γ2 lam s Fa Fb T0 Tp Tm : ℝ) (hbf : Fb ≠ 0)
    (hd1 : 2 * n + 4 * k - 1 ≠ 0) (hdm3 : 2 * n + 4 * k - 3 ≠ 0) (hd3 : 2 * n + 4 * k + 3 ≠ 0)
    (hd5 : 2 * n + 4 * k + 5 ≠ 0) (hd1' : 2 * n + 4 * k + 1 ≠ 0)
    (hb1 : n + m + 2 * k + 1 ≠ 0) (hb2 : n + m + 2 * k + 2 ≠ 0)
    (core : ((n + 2 * k) * (n + 2 * k + 1) - lam) *
        ((2 * (n + 2 * k) - 1) * (2 * (n + 2 * k) + 1) * (2 * (n + 2 * k) + 3)) * T0 =
      γ2 * (((2 * (n + 2 * k) - 1) * (2 * (n + 2 * k) + 1) * (2 * (n + 2 * k) + 3) -
            ((2 * (n + 2 * k) - 1) * (n + 2 * k - m + 1) * (n + 2 * k + m + 1) +
              (2 * (n + 2 * k) + 3) * (n + 2 * k + m) * (n + 2 * k - m))) * T0 -
          (2 * (n + 2 * k) - 1) * (n + 2 * k - m + 1) * (n + 2 * k - m + 2) * Tp -
        (2 * (n + 2 * k) + 3) * (n + 2 * k + m) * (n + 2 * k + m - 1) * Tm))
    (hTm : (n + 2 * k + m) * (n + 2 * k + m - 1) * Tm = 0) :
    -γ2 * ((n - m + 2 * k - 1) * (n - m + 2 * k)) /
          ((2 * n + 4 * k - 3) * (2 * n + 4 * k - 1)) * 0 +
        ((n + 2 * k) * (n + 2 * k + 1) -
              2 * γ2 * ((n + 2 * k) * (n + 2 * k + 1) - 1 + m ^ 2) /
                ((2 * n + 4 * k - 1) * (2 * n + 4 * k + 3)) -
            lam) *
          (s * (n + 2 * k + 1 / 2) * (Fa / Fb) * T0) +
      -γ2 * ((n + m + 2 * k + 1) * (n + m + 2 * k + 2)) /
          ((2 * n + 4 * k + 3) * (2 * n + 4 * k + 5)) *
        (s * -1 * (n + 2 * (k + 1) + 1 / 2) *
            ((n - m + 2 * k + 2) * (n - m + 2 * k + 1) * Fa /
              ((n + m + 2 * k + 2) * (n + m + 2 * k + 1) * Fb)) * Tp) = 0 := by
  linear_combination (norm := skip)
    s * (n + 2 * k + 1 / 2) * (Fa / Fb) / ((2 * n + 4 * k - 1) * (2 * n + 4 * k + 1) *
      (2 * n + 4 * k + 3)) * core -
    s * (n + 2 * k + 1 / 2) * (Fa / Fb) / ((2 * n + 4 * k - 1) * (2 * n + 4 * k + 1) *
      (2 * n + 4 * k + 3)) * γ2 * (2 * (n + 2 * k) + 3) * hTm
  generalize hD1 : 2 * n + 4 * k - 1 = d1 at *
  generalize hDm3 : 2 * n + 4 * k - 3 = dm3 at *
  generalize hD3 : 2 * n + 4 * k + 3 = d3 at *
  generalize hD5 : 2 * n + 4 * k + 5 = d5 at *
  generalize hD1' : 2 * n + 4 * k + 1 = d1' at *
  generalize hB1 : n + m + 2 * k + 1 = b1 at *
  generalize hB2 : n + m + 2 * k + 2 = b2 at *
  field_simp
  subst hD1 hDm3 hD3 hD5 hD1' hB1 hB2
  ring

/-- The algebra of 30.8.4 for `k > -R`. -/
lemma p2y_alg_high (n k m γ2 lam s Fa Fb T0 Tp Tm : ℝ) (hbf : Fb ≠ 0)
    (hd1 : 2 * n + 4 * k - 1 ≠ 0) (hdm3 : 2 * n + 4 * k - 3 ≠ 0) (hd3 : 2 * n + 4 * k + 3 ≠ 0)
    (hd5 : 2 * n + 4 * k + 5 ≠ 0) (hd1' : 2 * n + 4 * k + 1 ≠ 0) (hB : 0 ≤ n + m + 2 * k - 2)
    (core : ((n + 2 * k) * (n + 2 * k + 1) - lam) *
        ((2 * (n + 2 * k) - 1) * (2 * (n + 2 * k) + 1) * (2 * (n + 2 * k) + 3)) * T0 =
      γ2 * (((2 * (n + 2 * k) - 1) * (2 * (n + 2 * k) + 1) * (2 * (n + 2 * k) + 3) -
            ((2 * (n + 2 * k) - 1) * (n + 2 * k - m + 1) * (n + 2 * k + m + 1) +
              (2 * (n + 2 * k) + 3) * (n + 2 * k + m) * (n + 2 * k - m))) * T0 -
          (2 * (n + 2 * k) - 1) * (n + 2 * k - m + 1) * (n + 2 * k - m + 2) * Tp -
        (2 * (n + 2 * k) + 3) * (n + 2 * k + m) * (n + 2 * k + m - 1) * Tm)) :
    -γ2 * ((n - m + 2 * k - 1) * (n - m + 2 * k)) / ((2 * n + 4 * k - 3) * (2 * n + 4 * k - 1)) *
          (s * (-1)⁻¹ * (n + 2 * (k - 1) + 1 / 2) * (Fa / Fb) * Tm) +
        ((n + 2 * k) * (n + 2 * k + 1) -
              2 * γ2 * ((n + 2 * k) * (n + 2 * k + 1) - 1 + m ^ 2) /
                ((2 * n + 4 * k - 1) * (2 * n + 4 * k + 3)) - lam) *
          (s * (n + 2 * k + 1 / 2) *
              ((n - m + 2 * k - 2 + 2) * (n - m + 2 * k - 2 + 1) * Fa /
                ((n + m + 2 * k - 2 + 2) * (n + m + 2 * k - 2 + 1) * Fb)) * T0) +
      -γ2 * ((n + m + 2 * k + 1) * (n + m + 2 * k + 2)) /
          ((2 * n + 4 * k + 3) * (2 * n + 4 * k + 5)) *
        (s * -1 * (n + 2 * (k + 1) + 1 / 2) *
            ((n - m + 2 * k - 2 + 2 + 2) * (n - m + 2 * k - 2 + 2 + 1) *
                ((n - m + 2 * k - 2 + 2) * (n - m + 2 * k - 2 + 1) * Fa) /
              ((n + m + 2 * k - 2 + 2 + 2) * (n + m + 2 * k - 2 + 2 + 1) *
                ((n + m + 2 * k - 2 + 2) * (n + m + 2 * k - 2 + 1) * Fb))) * Tp) = 0 := by
  linear_combination (norm := skip)
    s * ((n + 2 * k + 1 / 2) * ((n - m + 2 * k - 2 + 2) * (n - m + 2 * k - 2 + 1) * Fa /
      ((n + m + 2 * k - 2 + 2) * (n + m + 2 * k - 2 + 1) * Fb))) /
      ((2 * n + 4 * k - 1) * (2 * n + 4 * k + 1) * (2 * n + 4 * k + 3)) * core
  generalize hX : n + m + 2 * k - 2 = B at *
  have hB1 : B + 1 ≠ 0 := by intro h; linarith
  have hB2 : B + 2 ≠ 0 := by intro h; linarith
  have hB3 : B + 2 + 1 ≠ 0 := by intro h; linarith
  have hB4 : B + 2 + 2 ≠ 0 := by intro h; linarith
  generalize hD1 : 2 * n + 4 * k - 1 = d1 at *
  generalize hDm3 : 2 * n + 4 * k - 3 = dm3 at *
  generalize hD3 : 2 * n + 4 * k + 3 = d3 at *
  generalize hD5 : 2 * n + 4 * k + 5 = d5 at *
  generalize hD1' : 2 * n + 4 * k + 1 = d1' at *
  field_simp
  subst hD1 hDm3 hD3 hD5 hD1'
  rw [← hX]
  ring

/-- **The recurrence for `k ≥ -R`** (DLMF 30.8.4): the coefficients of 30.8.1 solve the difference
equation from `k = -R` on (no hypothesis needed). Proved from the eigenfunction choice
`spheroidalPsFactor_spec` by self-adjointness and DLMF 14.10.3. -/
@[dlmf 30.8.E4]
theorem spheroidalCoeff_recurrence_of_le {n m : ℕ} (hmn : m ≤ n) (γ2 : ℝ) {k : ℤ}
    (hk : -(((n - m) / 2 : ℕ) : ℤ) ≤ k) :
    spheroidalRecA n m γ2 k * (if -(((n - m) / 2 : ℕ) : ℤ) ≤ k - 1 then
        spheroidalCoeff n m γ2 (k - 1) else 0) +
        (spheroidalRecB n m γ2 k - spheroidalEigenvalue n m γ2) * spheroidalCoeff n m γ2 k +
      spheroidalRecC n m γ2 k * spheroidalCoeff n m γ2 (k + 1) = 0 := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, (N : ℤ) = n + 2 * k := ⟨(n + 2 * k).toNat, by omega⟩
  obtain ⟨a, ha⟩ : ∃ a : ℕ, (a : ℤ) = n - m + 2 * k := ⟨(n - m + 2 * k : ℤ).toNat, by omega⟩
  obtain ⟨b, hb⟩ : ∃ b : ℕ, (b : ℤ) = n + m + 2 * k := ⟨(n + m + 2 * k : ℤ).toNat, by omega⟩
  have hNr : (N : ℝ) = n + 2 * k := by exact_mod_cast hN
  have har : (a : ℝ) = n - m + 2 * k := by exact_mod_cast ha
  have hbr : (b : ℝ) = n + m + 2 * k := by exact_mod_cast hb
  have hNc : ((N : ℝ) : ℂ) = n + 2 * k := by rw [ofReal_natCast]; exact_mod_cast hN
  have core := p2y_core hmn γ2 N
  rw [spheroidalCoeff_of_le γ2 hk, spheroidalCoeff_of_le γ2 (by omega : _ ≤ k + 1)]
  rw [show ((n : ℤ) - m + 2 * (k + 1)).toNat = a + 2 by omega,
    show ((n : ℤ) + m + 2 * (k + 1)).toNat = b + 2 by omega,
    show ((n : ℤ) - m + 2 * k).toNat = a by omega, show ((n : ℤ) + m + 2 * k).toNat = b by omega]
  rw [show ((n : ℂ) + 2 * ((k + 1 : ℤ) : ℂ)) = ((N : ℝ) : ℂ) + 2 by rw [hNc]; push_cast; ring,
    show ((n : ℂ) + 2 * (k : ℂ)) = ((N : ℝ) : ℂ) by rw [hNc]]
  have hmN : (m : ℝ) ≤ N := by rw [hNr]; linarith [(a.cast_nonneg : (0:ℝ) ≤ a)]
  have hTm : k = -(((n - m) / 2 : ℕ) : ℤ) → ((N : ℝ) + m) * ((N : ℝ) + m - 1) *
      (∫ x in (-1 : ℝ)..1, spheroidalPs n m x γ2 * (ferrersP (((N : ℝ) : ℂ) - 2) m x).re) = 0 := by
    intro hk'
    rw [← intervalIntegral.integral_const_mul]
    rw [p2y_integral_congr_Ioo (f₂ := fun _ => (0 : ℝ)) ?_]
    · simp
    intro x hx
    have h := p2y_low_vanish (m := m) (N := N) (by exact_mod_cast hmN) (by omega) hx
    linear_combination spheroidalPs n m x γ2 * h
  have hd1 : (2 * (n : ℝ) + 4 * k - 1) ≠ 0 := by
    have : (2 * (N : ℤ) - 1) ≠ 0 := by omega
    have : (2 * (N : ℝ) - 1) ≠ 0 := by exact_mod_cast this
    rw [hNr] at this; intro h; apply this; linarith
  have hdm3 : (2 * (n : ℝ) + 4 * k - 3) ≠ 0 := by
    have : (2 * (N : ℤ) - 3) ≠ 0 := by omega
    have : (2 * (N : ℝ) - 3) ≠ 0 := by exact_mod_cast this
    rw [hNr] at this; intro h; apply this; linarith
  have hd3 : (2 * (n : ℝ) + 4 * k + 3) ≠ 0 := by
    have : (2 * (N : ℝ) + 3) ≠ 0 := by positivity
    rw [hNr] at this; intro h; apply this; linarith
  have hd5 : (2 * (n : ℝ) + 4 * k + 5) ≠ 0 := by
    have : (2 * (N : ℝ) + 5) ≠ 0 := by positivity
    rw [hNr] at this; intro h; apply this; linarith
  have hd1' : (2 * (n : ℝ) + 4 * k + 1) ≠ 0 := by
    have : (2 * (N : ℝ) + 1) ≠ 0 := by positivity
    rw [hNr] at this; intro h; apply this; linarith
  have hb1 : ((n : ℝ) + m + 2 * k + 1) ≠ 0 := by rw [← hbr]; positivity
  have hb2 : ((n : ℝ) + m + 2 * k + 2) ≠ 0 := by rw [← hbr]; positivity
  rcases eq_or_lt_of_le hk with hk' | hk'
  · -- `k = -R`
    simp only [show ¬ (-(((n - m) / 2 : ℕ) : ℤ) ≤ k - 1) by omega, ↓reduceIte]
    have hTm' := hTm hk'.symm
    set T0 := ∫ x in (-1 : ℝ)..1, spheroidalPs n m x γ2 * (ferrersP ((N : ℝ) : ℂ) m x).re
    set Tp := ∫ x in (-1 : ℝ)..1, spheroidalPs n m x γ2 * (ferrersP (((N : ℝ) : ℂ) + 2) m x).re
    set Tm := ∫ x in (-1 : ℝ)..1, spheroidalPs n m x γ2 * (ferrersP (((N : ℝ) : ℂ) - 2) m x).re
    set lam := spheroidalEigenvalue n m γ2
    clear_value T0 Tp Tm lam
    rw [p2y_factorial_two a, p2y_factorial_two b, zpow_add_one₀ (by norm_num : (-1 : ℝ) ≠ 0)]
    have hbf : (b.factorial : ℝ) ≠ 0 := by positivity
    rw [hNr] at core hTm'
    unfold spheroidalRecA spheroidalRecB spheroidalRecC
    push_cast
    rw [har, hbr]
    exact p2y_alg_low _ _ _ _ _ _ _ _ _ _ _ hbf hd1 hdm3 hd3 hd5 hd1' hb1 hb2 core hTm'
  · -- `k > -R`
    simp only [show -(((n - m) / 2 : ℕ) : ℤ) ≤ k - 1 by omega, ↓reduceIte]
    rw [spheroidalCoeff_of_le γ2 (by omega : _ ≤ k - 1)]
    obtain ⟨a₀, rfl⟩ : ∃ a₀ : ℕ, a = a₀ + 2 := ⟨a - 2, by omega⟩
    obtain ⟨b₀, rfl⟩ : ∃ b₀ : ℕ, b = b₀ + 2 := ⟨b - 2, by omega⟩
    rw [show ((n : ℤ) - m + 2 * (k - 1)).toNat = a₀ by omega,
      show ((n : ℤ) + m + 2 * (k - 1)).toNat = b₀ by omega,
      show ((n : ℂ) + 2 * ((k - 1 : ℤ) : ℂ)) = ((N : ℝ) : ℂ) - 2 by rw [hNc]; push_cast; ring]
    set T0 := ∫ x in (-1 : ℝ)..1, spheroidalPs n m x γ2 * (ferrersP ((N : ℝ) : ℂ) m x).re
    set Tp := ∫ x in (-1 : ℝ)..1, spheroidalPs n m x γ2 * (ferrersP (((N : ℝ) : ℂ) + 2) m x).re
    set Tm := ∫ x in (-1 : ℝ)..1, spheroidalPs n m x γ2 * (ferrersP (((N : ℝ) : ℂ) - 2) m x).re
    set lam := spheroidalEigenvalue n m γ2
    clear_value T0 Tp Tm lam
    have har0 : (a₀ : ℝ) = n - m + 2 * k - 2 := by push_cast at har; linarith
    have hbr0 : (b₀ : ℝ) = n + m + 2 * k - 2 := by push_cast at hbr; linarith
    have hbf : (b₀.factorial : ℝ) ≠ 0 := by positivity
    rw [p2y_factorial_two (a₀ + 2), p2y_factorial_two (b₀ + 2), p2y_factorial_two a₀,
      p2y_factorial_two b₀, zpow_add_one₀ (by norm_num : (-1 : ℝ) ≠ 0),
      zpow_sub_one₀ (by norm_num : (-1 : ℝ) ≠ 0)]
    rw [hNr] at core
    unfold spheroidalRecA spheroidalRecB spheroidalRecC
    push_cast
    rw [har0, hbr0]
    exact p2y_alg_high _ _ _ _ _ _ _ _ _ _ _ hbf hd1 hdm3 hd3 hd5 hd1'
      (by rw [← hbr0]; positivity) core

/-- **The coefficients `a^{-m}_{n,k}`** (DLMF 30.8.6): for `k ≥ -R`,
`a^{-m}_{n,k} = (n-m)!(n+m+2k)!/((n+m)!(n-m+2k)!) a^m_{n,k}`. Proved (definition). -/
@[dlmf 30.8.E6]
theorem spheroidalCoeffNeg_of_le {n m : ℕ} (γ2 : ℝ) {k : ℤ}
    (hk : -(((n - m) / 2 : ℕ) : ℤ) ≤ k) :
    spheroidalCoeffNeg n m γ2 k =
      (((n - m).factorial : ℝ) * (((n : ℤ) + m + 2 * k).toNat.factorial : ℝ)) /
        (((n + m).factorial : ℝ) * (((n : ℤ) - m + 2 * k).toNat.factorial : ℝ)) *
          spheroidalCoeff n m γ2 k := by
  unfold spheroidalCoeffNeg
  simp only [hk, ↓reduceIte]

/-! #### Proof of the expansion 30.8.1 and the normalization 30.8.5

With `ν = n - 2R + 2j`, `a^m_{n,j-R} = ±(2ν+1)(ν-m)!/(2(ν+m)!) b_ν`, `b_ν = ∫ (1-x²)^m g P_ν^{(m)}`.
A crude bound gives `|a| = O(j)`; the recurrence 30.8.4 with `B_k - λ → ∞` improves it to
geometric decay of any rate, which dominates the exponential growth of `P_ν^{(m)}` on `[-1, 1]`.
Completeness of the `P_ν^{(m)}` (`p2y_hasSum_expansion`) then gives 30.8.1 and Parseval 30.8.5. -/

/-- The real Ferrers function of integer degree through `P_N^{(m)}`. -/
lemma p2y_ferrers_re (N m : ℕ) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    (ferrersP N m x).re = (-1) ^ m * (1 - x ^ 2) ^ ((m : ℝ) / 2) * (legInt_D N m x).re := by
  rw [legInt_ferrersP_nat_nat N m hx, p2y_legInt_D_real N m x,
    show ((-1 : ℂ) ^ m) = (((-1 : ℝ) ^ m : ℝ) : ℂ) by push_cast; rfl, ← ofReal_mul, ← ofReal_mul,
    ofReal_re, ofReal_re]

/-- The coefficients 30.8.2 through the entire factor: for `k = j - R`, `ν = n - 2R + 2j`,
`a^m_{n,k} = (-1)^{k+m} (2ν+1)(ν-m)!/(2(ν+m)!) ∫ (1-x²)^m g P_ν^{(m)}`. -/
lemma p2y_coeff_eq {n m : ℕ} (hmn : m ≤ n) (γ2 : ℝ) (j : ℕ) :
    spheroidalCoeff n m γ2 ((j : ℤ) - ((n - m) / 2 : ℕ)) =
      (-1 : ℝ) ^ ((j : ℤ) - ((n - m) / 2 : ℕ)) * (-1) ^ m *
        ((2 * ((n - 2 * ((n - m) / 2) + 2 * j : ℕ) : ℝ) + 1) *
          ((n - 2 * ((n - m) / 2) + 2 * j - m).factorial : ℝ) /
            (2 * ((n - 2 * ((n - m) / 2) + 2 * j + m).factorial : ℝ)) *
        ∫ y in (-1 : ℝ)..1, (1 - y ^ 2) ^ m * (spheroidalPsFactor n m γ2 y).re *
          (legInt_D (n - 2 * ((n - m) / 2) + 2 * j) m y).re) := by
  rw [spheroidalCoeff_of_le γ2 (by omega)]
  obtain ⟨ν, hν⟩ : ∃ ν, ν = n - 2 * ((n - m) / 2) + 2 * j := ⟨_, rfl⟩
  rw [← hν]
  have hνi : (ν : ℤ) = n + 2 * ((j : ℤ) - ((n - m) / 2 : ℕ)) := by omega
  have hc : ((n : ℂ) + 2 * ((((j : ℤ) - ((n - m) / 2 : ℕ)) : ℤ) : ℂ)) = ((ν : ℕ) : ℂ) := by
    exact_mod_cast hνi.symm
  have hr : ((n : ℝ) + 2 * ((((j : ℤ) - ((n - m) / 2 : ℕ)) : ℤ) : ℝ)) = ((ν : ℕ) : ℝ) := by
    exact_mod_cast hνi.symm
  have h1 : ((n : ℤ) - m + 2 * ((j : ℤ) - ((n - m) / 2 : ℕ))).toNat = ν - m := by omega
  have h2 : ((n : ℤ) + m + 2 * ((j : ℤ) - ((n - m) / 2 : ℕ))).toNat = ν + m := by omega
  rw [hc, h1, h2, hr]
  have hI : ∫ x in (-1 : ℝ)..1, spheroidalPs n m x γ2 * (ferrersP ((ν : ℕ) : ℂ) m x).re =
      (-1) ^ m * ∫ y in (-1 : ℝ)..1, (1 - y ^ 2) ^ m * (spheroidalPsFactor n m γ2 y).re *
        (legInt_D ν m y).re := by
    rw [← intervalIntegral.integral_const_mul]
    apply p2y_integral_congr_Ioo
    intro x hx
    simp only [spheroidalPs]
    rw [p2y_ferrers_prod m ν hx]
    ring
  rw [hI]
  ring

/-- The parity of the entire factor: `g(-x) = (-1)^{n-m} g(x)`. -/
lemma p2y_factor_neg {n m : ℕ} (hmn : m ≤ n) (γ2 x : ℝ) :
    (spheroidalPsFactor n m γ2 ((-x : ℝ) : ℂ)).re =
      (-1) ^ (n - m) * (spheroidalPsFactor n m γ2 x).re := by
  have hg := spheroidalPsFactor_spec hmn γ2
  have hu := (existsUnique_isSpheroidalPsFactor hmn γ2).unique
    (p1s_isSpheroidalPsFactor_reflect hg) hg
  have hx := congrFun hu (-(x : ℂ))
  simp only [neg_neg] at hx
  rw [ofReal_neg, ← hx, show ((-1 : ℂ) ^ (n - m)) = (((-1 : ℝ) ^ (n - m) : ℝ) : ℂ) by
    push_cast; rfl, re_ofReal_mul]

/-- The coefficients of the wrong parity vanish. -/
lemma p2y_coeff_parity {n m : ℕ} (hmn : m ≤ n) (γ2 : ℝ) (μ : ℕ) (hμ : m ≤ μ)
    (hex : ∀ j : ℕ, μ ≠ n - 2 * ((n - m) / 2) + 2 * j) :
    ∫ x in (-1 : ℝ)..1, (1 - x ^ 2) ^ m * (spheroidalPsFactor n m γ2 x).re *
      (legInt_D μ m x).re = 0 := by
  have hodd : (n + μ) % 2 = 1 := by
    by_contra h
    exact hex ((μ - (n - 2 * ((n - m) / 2))) / 2) (by omega)
  have hs : ((-1 : ℝ) ^ (n - m) * (-1) ^ (μ + m)) = -1 := by
    rw [← pow_add, show n - m + (μ + m) = n + μ by omega]
    exact Odd.neg_one_pow (Nat.odd_iff.mpr hodd)
  set f : ℝ → ℝ := fun x => (1 - x ^ 2) ^ m * (spheroidalPsFactor n m γ2 x).re *
    (legInt_D μ m x).re with hf
  have hneg : ∀ x, f (-x) = -f x := by
    intro x
    simp only [hf]
    rw [p2y_factor_neg hmn, p2y_D_neg, neg_sq]
    linear_combination ((1 - x ^ 2) ^ m * (spheroidalPsFactor n m γ2 x).re *
      (legInt_D μ m x).re) * hs
  have h := intervalIntegral.integral_comp_neg (a := (-1 : ℝ)) (b := 1) f
  simp only [neg_neg, hneg, intervalIntegral.integral_neg] at h
  change ∫ x in (-1 : ℝ)..1, f x = 0
  linarith

/-- A crude bound for the coefficient `∫ (1-x²)^m G P_ν^{(m)}` of a bounded continuous `G`. -/
lemma p2y_b_bound {G : ℝ → ℝ} (hG : ContinuousOn G (Icc (-1) 1)) {MG : ℝ}
    (hM : ∀ x ∈ Icc (-1 : ℝ) 1, |G x| ≤ MG) {m ν : ℕ} (hν : m ≤ ν) :
    |∫ x in (-1 : ℝ)..1, (1 - x ^ 2) ^ m * G x * (legInt_D ν m x).re| ≤
      MG * (2 + 2 * ((ν + m).factorial : ℝ) / ((2 * ν + 1) * (ν - m).factorial)) := by
  have hD : Continuous fun x : ℝ => (legInt_D ν m x).re :=
    Complex.continuous_re.comp (legInt_cont_D ν m)
  have hw : Continuous fun x : ℝ => (1 - x ^ 2) ^ m := by fun_prop
  have hMG : 0 ≤ MG := (abs_nonneg _).trans (hM 0 (by norm_num))
  calc _ ≤ ∫ x in (-1 : ℝ)..1, |(1 - x ^ 2) ^ m * G x * (legInt_D ν m x).re| :=
        intervalIntegral.abs_integral_le_integral_abs (by norm_num)
    _ ≤ ∫ x in (-1 : ℝ)..1, MG * (1 + (1 - x ^ 2) ^ m * (legInt_D ν m x).re *
          (legInt_D ν m x).re) := by
        refine intervalIntegral.integral_mono_on (by norm_num) ?_ ?_ fun x hx => ?_
        · exact ((hw.continuousOn.mul hG).mul hD.continuousOn).abs.intervalIntegrable_of_Icc
            (by norm_num)
        · exact (continuous_const.mul (continuous_const.add
            ((hw.mul hD).mul hD))).intervalIntegrable _ _
        · have h1 : 0 ≤ 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
          have hw0 : 0 ≤ (1 - x ^ 2) ^ m := pow_nonneg h1 m
          have hw1 : (1 - x ^ 2) ^ m ≤ 1 := pow_le_one₀ h1 (by nlinarith)
          set d := (legInt_D ν m x).re
          have hd : |d| ≤ 1 + d * d := by
            rcases abs_cases d with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> nlinarith [sq_nonneg (d - 1),
              sq_nonneg (d + 1)]
          rw [abs_mul, abs_mul, abs_of_nonneg hw0]
          have hG' := hM x hx
          have : (1 - x ^ 2) ^ m * |d| ≤ 1 + (1 - x ^ 2) ^ m * d * d := by
            nlinarith [mul_le_mul_of_nonneg_left hd hw0, mul_self_nonneg d]
          calc (1 - x ^ 2) ^ m * |G x| * |d| = |G x| * ((1 - x ^ 2) ^ m * |d|) := by ring
            _ ≤ MG * (1 + (1 - x ^ 2) ^ m * d * d) :=
              mul_le_mul hG' this (by positivity) hMG
    _ = MG * (2 + 2 * ((ν + m).factorial : ℝ) / ((2 * ν + 1) * (ν - m).factorial)) := by
        have hi : IntervalIntegrable (fun x : ℝ => (1 - x ^ 2) ^ m * (legInt_D ν m x).re *
            (legInt_D ν m x).re) volume (-1) 1 := ((hw.mul hD).mul hD).intervalIntegrable _ _
        rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add
          intervalIntegrable_const hi, p2y_D_orth hν ν]
        simp only [↓reduceIte, intervalIntegral.integral_const, smul_eq_mul]
        ring

/-- **A linear a-priori bound** for the coefficients: `|a^m_{n,j-R}| ≤ M (j+1)`. -/
lemma p2y_coeff_linear {n m : ℕ} (hmn : m ≤ n) (γ2 : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ j : ℕ,
      |spheroidalCoeff n m γ2 ((j : ℤ) - ((n - m) / 2 : ℕ))| ≤ M * (j + 1) := by
  have hg := (spheroidalPsFactor_spec hmn γ2).factor.differentiable
  have hGc : Continuous fun x : ℝ => (spheroidalPsFactor n m γ2 x).re :=
    Complex.continuous_re.comp (hg.continuous.comp continuous_ofReal)
  obtain ⟨MG, hMG⟩ := (isCompact_Icc.image_of_continuousOn
    (hGc.continuousOn (s := Icc (-1 : ℝ) 1))).isBounded.exists_norm_le
  have hM : ∀ x ∈ Icc (-1 : ℝ) 1, |(spheroidalPsFactor n m γ2 x).re| ≤ MG :=
    fun x hx => hMG _ ⟨x, hx, rfl⟩
  have hMG0 : 0 ≤ MG := (abs_nonneg _).trans (hM 0 (by norm_num))
  refine ⟨MG * (2 * n + 4), by positivity, fun j => ?_⟩
  rw [p2y_coeff_eq hmn γ2 j]
  obtain ⟨ν, hν⟩ : ∃ ν, ν = n - 2 * ((n - m) / 2) + 2 * j := ⟨_, rfl⟩
  rw [← hν]
  have hνm : m ≤ ν := by omega
  have hνn : (ν : ℝ) ≤ n + 2 * j := by
    have : ν ≤ n + 2 * j := by omega
    exact_mod_cast this
  have hb := p2y_b_bound hGc.continuousOn hM hνm
  have hs : |(-1 : ℝ) ^ ((j : ℤ) - ((n - m) / 2 : ℕ)) * (-1) ^ m| = 1 := by
    rw [abs_mul, abs_zpow, abs_pow, abs_neg, abs_one, one_zpow, one_pow, mul_one]
  have hf1 : (0 : ℝ) < ((ν - m).factorial : ℝ) := by positivity
  have hf2 : (0 : ℝ) < ((ν + m).factorial : ℝ) := by positivity
  have hfl : ((ν - m).factorial : ℝ) ≤ ((ν + m).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le (by omega)
  have h2 : (0 : ℝ) < 2 * ν + 1 := by positivity
  rw [abs_mul, hs, one_mul, abs_mul, abs_of_pos (by positivity)]
  set B := |∫ y in (-1 : ℝ)..1, (1 - y ^ 2) ^ m * (spheroidalPsFactor n m γ2 y).re *
    (legInt_D ν m y).re|
  have hB0 : 0 ≤ B := abs_nonneg _
  calc (2 * (ν : ℝ) + 1) * ((ν - m).factorial : ℝ) / (2 * ((ν + m).factorial : ℝ)) * B
      ≤ (2 * (ν : ℝ) + 1) * ((ν - m).factorial : ℝ) / (2 * ((ν + m).factorial : ℝ)) *
        (MG * (2 + 2 * ((ν + m).factorial : ℝ) / ((2 * ν + 1) * (ν - m).factorial))) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ = MG * (2 * ((2 * (ν : ℝ) + 1) * ((ν - m).factorial : ℝ) / (2 * ((ν + m).factorial : ℝ)))
        + 1) := by field_simp
    _ ≤ MG * (2 * (2 * (ν : ℝ) + 1) / 2 + 1) := by
        gcongr
        rw [mul_div_assoc, show 2 * (2 * (ν : ℝ) + 1) / 2 = 2 * ((2 * ν + 1) / 2) by ring]
        gcongr
        have hq : ((ν - m).factorial : ℝ) / (2 * ((ν + m).factorial : ℝ)) ≤ 1 / 2 := by
          rw [div_le_iff₀ (by positivity)]; linarith
        calc (2 * (ν : ℝ) + 1) * (((ν - m).factorial : ℝ) / (2 * ((ν + m).factorial : ℝ)))
            ≤ (2 * (ν : ℝ) + 1) * (1 / 2) := mul_le_mul_of_nonneg_left hq h2.le
          _ = (2 * (ν : ℝ) + 1) / 2 := by ring
    _ ≤ MG * (2 * n + 4) * (j + 1) := by
        rw [mul_assoc]
        gcongr
        have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
        have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        nlinarith

/-- Bounds for the coefficients of 30.8.4 for `k ≥ 1`: `|A_k|, |C_k| ≤ |γ²|` and
`B_k ≥ (n+2k)(n+2k+1) - 2|γ²|(1+m²)`. -/
lemma p2y_rec_bounds {n m : ℕ} (hmn : m ≤ n) (γ2 : ℝ) {k : ℤ} (hk : 1 ≤ k) :
    |spheroidalRecA n m γ2 k| ≤ |γ2| ∧ |spheroidalRecC n m γ2 k| ≤ |γ2| ∧
      ((n : ℝ) + 2 * k) * ((n : ℝ) + 2 * k + 1) - 2 * |γ2| * (1 + m ^ 2) ≤
        spheroidalRecB n m γ2 k := by
  have kr : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hmr : (m : ℝ) ≤ n := by exact_mod_cast hmn
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  refine ⟨?_, ?_, ?_⟩
  · unfold spheroidalRecA
    rw [mul_div_assoc, abs_mul, abs_neg]
    refine mul_le_of_le_one_right (abs_nonneg _) ?_
    rw [abs_div, abs_of_nonneg (by nlinarith), abs_of_pos (by nlinarith), div_le_one
      (by nlinarith)]
    nlinarith
  · unfold spheroidalRecC
    rw [mul_div_assoc, abs_mul, abs_neg]
    refine mul_le_of_le_one_right (abs_nonneg _) ?_
    rw [abs_div, abs_of_nonneg (by nlinarith), abs_of_pos (by nlinarith), div_le_one
      (by nlinarith)]
    nlinarith
  · unfold spheroidalRecB
    set F := (((n : ℝ) + 2 * k) * ((n : ℝ) + 2 * k + 1) - 1 + m ^ 2) /
      ((2 * (n : ℝ) + 4 * k - 1) * (2 * (n : ℝ) + 4 * k + 3)) with hF
    have hQ : 0 < (2 * (n : ℝ) + 4 * k - 1) * (2 * (n : ℝ) + 4 * k + 3) := by nlinarith
    have hF0 : 0 ≤ F := div_nonneg (by nlinarith) hQ.le
    have hF1 : F ≤ 1 + m ^ 2 := by
      rw [hF, div_le_iff₀ hQ]; nlinarith [mul_nonneg hm0 hm0]
    rw [show 2 * γ2 * (((n : ℝ) + 2 * k) * ((n : ℝ) + 2 * k + 1) - 1 + m ^ 2) /
      ((2 * (n : ℝ) + 4 * k - 1) * (2 * (n : ℝ) + 4 * k + 3)) = 2 * γ2 * F by rw [hF]; ring]
    have h1 : γ2 * F ≤ |γ2| * (1 + m ^ 2) :=
      (le_abs_self _).trans (by rw [abs_mul, abs_of_nonneg hF0]; exact
        mul_le_mul_of_nonneg_left hF1 (abs_nonneg _))
    linarith

/-- Eventually `|a_{j+1}| ≤ ε (|a_j| + |a_{j+2}|)` (from 30.8.4, since `B_k - λ → ∞`). -/
lemma p2y_coeff_eps {n m : ℕ} (hmn : m ≤ n) (γ2 : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ J : ℕ, ∀ j : ℕ, J ≤ j →
      |spheroidalCoeff n m γ2 (((j + 1 : ℕ) : ℤ) - ((n - m) / 2 : ℕ))| ≤
        ε * (|spheroidalCoeff n m γ2 ((j : ℤ) - ((n - m) / 2 : ℕ))| +
          |spheroidalCoeff n m γ2 (((j + 2 : ℕ) : ℤ) - ((n - m) / 2 : ℕ))|) := by
  set lam := spheroidalEigenvalue n m γ2
  set T : ℝ := |γ2| / ε + 1 + 2 * |γ2| * (1 + m ^ 2) + |lam| with hT
  obtain ⟨J0, hJ0⟩ := exists_nat_ge T
  refine ⟨J0 + (n - m) / 2, fun j hj => ?_⟩
  set k : ℤ := ((j + 1 : ℕ) : ℤ) - ((n - m) / 2 : ℕ) with hk
  have hk1 : 1 ≤ k := by omega
  have hkT : T ≤ (k : ℝ) := by
    have : ((J0 : ℤ) : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast (by omega : (J0 : ℤ) + 1 ≤ k)
    push_cast at this
    linarith
  have hrec := spheroidalCoeff_recurrence_of_le hmn γ2 (k := k) (by omega)
  simp only [show -(((n - m) / 2 : ℕ) : ℤ) ≤ k - 1 by omega, ↓reduceIte] at hrec
  rw [show k - 1 = (j : ℤ) - ((n - m) / 2 : ℕ) by rw [hk]; push_cast; ring,
    show k + 1 = ((j + 2 : ℕ) : ℤ) - ((n - m) / 2 : ℕ) by rw [hk]; push_cast; ring] at hrec
  obtain ⟨hA, hC, hB⟩ := p2y_rec_bounds hmn γ2 hk1
  set a0 := spheroidalCoeff n m γ2 ((j : ℤ) - ((n - m) / 2 : ℕ))
  set a1 := spheroidalCoeff n m γ2 k
  set a2 := spheroidalCoeff n m γ2 (((j + 2 : ℕ) : ℤ) - ((n - m) / 2 : ℕ))
  have hk0 : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hνbig : T ≤ ((n : ℝ) + 2 * k) * ((n : ℝ) + 2 * k + 1) := by nlinarith
  have hBl : |γ2| / ε + 1 ≤ spheroidalRecB n m γ2 k - lam := by
    have := le_abs_self lam
    linarith
  have hpos : 0 < spheroidalRecB n m γ2 k - lam := by
    have : 0 ≤ |γ2| / ε := by positivity
    linarith
  have hge : |γ2| ≤ ε * (spheroidalRecB n m γ2 k - lam) := by
    have h1 := mul_le_mul_of_nonneg_left hBl hε.le
    rw [mul_add, mul_div_cancel₀ _ hε.ne', mul_one] at h1
    linarith
  have e : (spheroidalRecB n m γ2 k - lam) * a1 = -(spheroidalRecA n m γ2 k * a0 +
      spheroidalRecC n m γ2 k * a2) := by linear_combination hrec
  have h2 : (spheroidalRecB n m γ2 k - lam) * |a1| ≤ |γ2| * (|a0| + |a2|) := by
    have := congrArg abs e
    rw [abs_mul, abs_of_pos hpos, abs_neg] at this
    rw [this]
    calc _ ≤ |spheroidalRecA n m γ2 k * a0| + |spheroidalRecC n m γ2 k * a2| := abs_add_le _ _
      _ ≤ |γ2| * |a0| + |γ2| * |a2| := by
          rw [abs_mul, abs_mul]
          exact add_le_add (mul_le_mul_of_nonneg_right hA (abs_nonneg _))
            (mul_le_mul_of_nonneg_right hC (abs_nonneg _))
      _ = _ := by ring
  have h3 : (spheroidalRecB n m γ2 k - lam) * |a1| ≤
      (spheroidalRecB n m γ2 k - lam) * (ε * (|a0| + |a2|)) := by
    calc _ ≤ |γ2| * (|a0| + |a2|) := h2
      _ ≤ ε * (spheroidalRecB n m γ2 k - lam) * (|a0| + |a2|) :=
          mul_le_mul_of_nonneg_right hge (by positivity)
      _ = _ := by ring
  exact le_of_mul_le_mul_left h3 hpos

/-- **Geometric decay** of the coefficients: for every `q > 0`, eventually
`|a_j| ≤ M (j+1) q^{j-J}`. -/
lemma p2y_coeff_decay {n m : ℕ} (hmn : m ≤ n) (γ2 : ℝ) {q : ℝ} (hq : 0 < q) :
    ∃ J : ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ j : ℕ, J ≤ j →
      |spheroidalCoeff n m γ2 ((j : ℤ) - ((n - m) / 2 : ℕ))| ≤ M * (j + 1) * q ^ (j - J) := by
  obtain ⟨M, hM0, hM⟩ := p2y_coeff_linear hmn γ2
  obtain ⟨J, hJ⟩ := p2y_coeff_eps hmn γ2 (by positivity : (0 : ℝ) < q / 2)
  refine ⟨J, M, hM0, ?_⟩
  have key : ∀ i : ℕ, ∀ j : ℕ, J + i ≤ j →
      |spheroidalCoeff n m γ2 ((j : ℤ) - ((n - m) / 2 : ℕ))| ≤ M * (j + 1) * q ^ i := by
    intro i
    induction i with
    | zero => intro j _; simpa using hM j
    | succ i ih =>
      intro j' hj'
      obtain ⟨j, rfl⟩ : ∃ j, j' = j + 1 := ⟨j' - 1, by omega⟩
      have h := hJ j (by omega)
      have h0 := ih j (by omega)
      have h2 := ih (j + 2) (by omega)
      have hqi : 0 ≤ q ^ i := by positivity
      calc _ ≤ q / 2 * (|spheroidalCoeff n m γ2 ((j : ℤ) - ((n - m) / 2 : ℕ))| +
            |spheroidalCoeff n m γ2 (((j + 2 : ℕ) : ℤ) - ((n - m) / 2 : ℕ))|) := h
        _ ≤ q / 2 * (M * (j + 1) * q ^ i + M * ((j + 2 : ℕ) + 1) * q ^ i) := by
            gcongr
        _ = M * (((j + 1 : ℕ) : ℝ) + 1) * q ^ (i + 1) := by push_cast; ring
  intro j hj
  exact key (j - J) j (by omega)

/-- A summable dominating sequence for the expansion of the entire factor on `[-1, 1]`, from the
geometric decay of the coefficients and the exponential bound of `P_ν^{(m)}`. -/
lemma p2y_factor_bound {n m : ℕ} (hmn : m ≤ n) (γ2 : ℝ) :
    ∃ u : ℕ → ℝ, Summable u ∧ ∀ j : ℕ, ∀ x ∈ Icc (-1 : ℝ) 1,
      |(2 * ((n - 2 * ((n - m) / 2) + 2 * j : ℕ) : ℝ) + 1) *
          ((n - 2 * ((n - m) / 2) + 2 * j - m).factorial : ℝ) /
          (2 * ((n - 2 * ((n - m) / 2) + 2 * j + m).factorial : ℝ)) *
        (∫ y in (-1 : ℝ)..1, (1 - y ^ 2) ^ m * (spheroidalPsFactor n m γ2 y).re *
          (legInt_D (n - 2 * ((n - m) / 2) + 2 * j) m y).re) *
          (legInt_D (n - 2 * ((n - m) / 2) + 2 * j) m x).re| ≤ u j := by
  have hg := (spheroidalPsFactor_spec hmn γ2).factor.differentiable
  have hGc : Continuous fun x : ℝ => (spheroidalPsFactor n m γ2 x).re :=
    Complex.continuous_re.comp (hg.continuous.comp continuous_ofReal)
  obtain ⟨C, hC0, hCb⟩ := p2y_D_bound m
  set L : ℝ := 2 * (m : ℝ) + 3 with hL
  have hL1 : 1 ≤ L := by rw [hL]; have := (Nat.cast_nonneg m : (0 : ℝ) ≤ m); linarith
  have hL0 : 0 < L := by linarith
  set q : ℝ := 1 / (2 * L ^ 2) with hq
  have hq0 : 0 < q := by positivity
  obtain ⟨J, M, hM0, hdec⟩ := p2y_coeff_decay hmn γ2 hq0
  set ν₀ := n - 2 * ((n - m) / 2) with hν₀
  have hν₀m : m ≤ ν₀ := by omega
  set a : ℕ → ℝ := fun j => spheroidalCoeff n m γ2 ((j : ℤ) - ((n - m) / 2 : ℕ)) with ha
  set u : ℕ → ℝ := fun j => C * L ^ (ν₀ + 2 * j - m) * |a j| with hu
  have hsumg : Summable fun j : ℕ => (C * L * M / q ^ J) * ((j + 1) * (1 / 2 : ℝ) ^ j) := by
    refine Summable.mul_left _ ?_
    have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 (r := (1 / 2 : ℝ))
      (by norm_num [Real.norm_eq_abs])
    have h2 := summable_geometric_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
    convert h1.add h2 using 1
    funext j; simp; ring
  have husum : Summable u := by
    refine Summable.of_norm_bounded_eventually_nat hsumg ?_
    filter_upwards [eventually_ge_atTop J] with j hj
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hd := hdec j hj
    have hpow : L ^ (ν₀ + 2 * j - m) ≤ L ^ (2 * j + 1) := pow_le_pow_right₀ hL1 (by omega)
    have hqJ : q ^ (j - J) = q ^ j / q ^ J := by
      rw [eq_div_iff (by positivity), ← pow_add, Nat.sub_add_cancel hj]
    have hLq : L ^ (2 * j + 1) * q ^ j = L * (1 / 2) ^ j := by
      rw [hq, pow_succ, pow_mul, mul_comm ((L ^ 2) ^ j) L, mul_assoc, ← mul_pow,
        show L ^ 2 * (1 / (2 * L ^ 2)) = 1 / 2 by field_simp]
    calc C * L ^ (ν₀ + 2 * j - m) * |a j| ≤ C * L ^ (2 * j + 1) * (M * (j + 1) * q ^ (j - J)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hpow hC0) hd (abs_nonneg _) (by positivity)
      _ = C * L * M / q ^ J * ((j + 1) * (1 / 2 : ℝ) ^ j) := by
          rw [hqJ, show C * L ^ (2 * j + 1) * (M * (j + 1) * (q ^ j / q ^ J)) =
            C * M * (j + 1) * (L ^ (2 * j + 1) * q ^ j) / q ^ J by ring, hLq]
          ring
  refine ⟨u, husum, fun j x hx => ?_⟩
  have hcoef := p2y_coeff_eq hmn γ2 j
  have hs : |(-1 : ℝ) ^ ((j : ℤ) - ((n - m) / 2 : ℕ)) * (-1) ^ m| = 1 := by
    rw [abs_mul, abs_zpow, abs_pow, abs_neg, abs_one, one_zpow, one_pow, mul_one]
  have haj : |a j| = |(2 * ((ν₀ + 2 * j : ℕ) : ℝ) + 1) * ((ν₀ + 2 * j - m).factorial : ℝ) /
      (2 * ((ν₀ + 2 * j + m).factorial : ℝ)) * (∫ y in (-1 : ℝ)..1, (1 - y ^ 2) ^ m *
        (spheroidalPsFactor n m γ2 y).re * (legInt_D (ν₀ + 2 * j) m y).re)| := by
    simp only [ha]
    rw [hcoef, abs_mul, hs, one_mul]
  rw [abs_mul, ← haj]
  calc |a j| * |(legInt_D (ν₀ + 2 * j) m x).re| ≤ |a j| * (C * L ^ (ν₀ + 2 * j - m)) :=
        mul_le_mul_of_nonneg_left (hCb _ (by omega) x hx) (abs_nonneg _)
    _ = u j := by simp only [hu]; ring

/-- **The expansion of the entire factor** in the functions `P_ν^{(m)}`, `ν = n - 2R + 2j`, on
`(-1, 1)` (the content of DLMF 30.8.1). -/
lemma p2y_factor_expansion {n m : ℕ} (hmn : m ≤ n) (γ2 : ℝ) :
    ∀ x ∈ Ioo (-1 : ℝ) 1, HasSum (fun j : ℕ =>
      (2 * ((n - 2 * ((n - m) / 2) + 2 * j : ℕ) : ℝ) + 1) *
          ((n - 2 * ((n - m) / 2) + 2 * j - m).factorial : ℝ) /
          (2 * ((n - 2 * ((n - m) / 2) + 2 * j + m).factorial : ℝ)) *
        (∫ y in (-1 : ℝ)..1, (1 - y ^ 2) ^ m * (spheroidalPsFactor n m γ2 y).re *
          (legInt_D (n - 2 * ((n - m) / 2) + 2 * j) m y).re) *
          (legInt_D (n - 2 * ((n - m) / 2) + 2 * j) m x).re)
      ((spheroidalPsFactor n m γ2 x).re) := by
  have hg := (spheroidalPsFactor_spec hmn γ2).factor.differentiable
  have hGc : Continuous fun x : ℝ => (spheroidalPsFactor n m γ2 x).re :=
    Complex.continuous_re.comp (hg.continuous.comp continuous_ofReal)
  obtain ⟨u, hu, hb⟩ := p2y_factor_bound hmn γ2
  exact p2y_hasSum_expansion hGc.continuousOn (by omega)
    (fun μ hμ hex => p2y_coeff_parity hmn γ2 μ hμ hex) hu hb

/-- **The Ferrers expansion** (DLMF 30.8.1):
`𝖯s^m_n(x, γ²) = ∑_{k ≥ -R} (-1)^k a^m_{n,k}(γ²) 𝖯^m_{n+2k}(x)` on `(-1, 1)`. Proved from the
eigenfunction choice: the coefficients decay geometrically (30.8.4) and the functions
`P_ν^{(m)}` are complete (Weierstrass). -/
@[dlmf 30.8.E1]
theorem hasSum_spheroidalPs_ferrers {n m : ℕ} (hmn : m ≤ n) (γ2 : ℝ) {x : ℝ}
    (hx : x ∈ Ioo (-1 : ℝ) 1) :
    HasSum (fun j : ℕ =>
        let k : ℤ := (j : ℤ) - ((n - m) / 2 : ℕ)
        (-1 : ℝ) ^ k * spheroidalCoeff n m γ2 k * (ferrersP ((n : ℂ) + 2 * k) m x).re)
      (spheroidalPs n m x γ2) := by
  have h := (p2y_factor_expansion hmn γ2 x hx).mul_left ((1 - x ^ 2) ^ ((m : ℝ) / 2))
  convert h using 1
  swap
  · rfl
  funext j
  obtain ⟨ν, hν⟩ : ∃ ν, ν = n - 2 * ((n - m) / 2) + 2 * j := ⟨_, rfl⟩
  have hνi : (ν : ℤ) = n + 2 * ((j : ℤ) - ((n - m) / 2 : ℕ)) := by omega
  have hc : ((n : ℂ) + 2 * ((((j : ℤ) - ((n - m) / 2 : ℕ)) : ℤ) : ℂ)) = ((ν : ℕ) : ℂ) := by
    exact_mod_cast hνi.symm
  simp only []
  rw [p2y_coeff_eq hmn γ2 j, hc, ← hν, p2y_ferrers_re ν m hx]
  have h1 : ((-1 : ℝ) ^ ((j : ℤ) - ((n - m) / 2 : ℕ))) * (-1) ^ ((j : ℤ) - ((n - m) / 2 : ℕ)) =
      1 := by rw [← mul_zpow]; norm_num
  have h2 : ((-1 : ℝ) ^ m) * (-1) ^ m = 1 := by rw [← mul_pow]; norm_num
  linear_combination ((2 * (ν : ℝ) + 1) * ((ν - m).factorial : ℝ) / (2 * ((ν + m).factorial : ℝ))
    * (∫ y in (-1 : ℝ)..1, (1 - y ^ 2) ^ m * (spheroidalPsFactor n m γ2 y).re *
      (legInt_D ν m y).re) * (1 - x ^ 2) ^ ((m : ℝ) / 2) * (legInt_D ν m x).re) *
    ((-1) ^ m * (-1) ^ m * h1 + h2)

/-- **Parseval's identity** for the expansion of the entire factor:
`∑_j c_ν b_ν² = ∫ (1-x²)^m g² = 2(n+m)!/((2n+1)(n-m)!)`. -/
lemma p2y_parseval {n m : ℕ} (hmn : m ≤ n) (γ2 : ℝ) :
    HasSum (fun j : ℕ =>
      (2 * ((n - 2 * ((n - m) / 2) + 2 * j : ℕ) : ℝ) + 1) *
          ((n - 2 * ((n - m) / 2) + 2 * j - m).factorial : ℝ) /
          (2 * ((n - 2 * ((n - m) / 2) + 2 * j + m).factorial : ℝ)) *
        (∫ y in (-1 : ℝ)..1, (1 - y ^ 2) ^ m * (spheroidalPsFactor n m γ2 y).re *
          (legInt_D (n - 2 * ((n - m) / 2) + 2 * j) m y).re) *
        (∫ y in (-1 : ℝ)..1, (1 - y ^ 2) ^ m * (spheroidalPsFactor n m γ2 y).re *
          (legInt_D (n - 2 * ((n - m) / 2) + 2 * j) m y).re))
      (2 / (2 * n + 1) * (((n + m).factorial : ℝ) / (n - m).factorial)) := by
  have spec := spheroidalPsFactor_spec hmn γ2
  have hg := spec.factor.differentiable
  have hGc : Continuous fun x : ℝ => (spheroidalPsFactor n m γ2 x).re :=
    Complex.continuous_re.comp (hg.continuous.comp continuous_ofReal)
  obtain ⟨MG, hMG⟩ := (isCompact_Icc.image_of_continuousOn
    (hGc.continuousOn (s := Icc (-1 : ℝ) 1))).isBounded.exists_norm_le
  have hM : ∀ x ∈ Icc (-1 : ℝ) 1, |(spheroidalPsFactor n m γ2 x).re| ≤ MG :=
    fun x hx => hMG _ ⟨x, hx, rfl⟩
  obtain ⟨u, hu, hb⟩ := p2y_factor_bound hmn γ2
  have hexp := p2y_factor_expansion hmn γ2
  rw [← spec.normalized]
  set ν₀ := n - 2 * ((n - m) / 2)
  set G : ℝ → ℝ := fun x => (spheroidalPsFactor n m γ2 x).re with hG
  set α : ℕ → ℝ := fun j => (2 * ((ν₀ + 2 * j : ℕ) : ℝ) + 1) * ((ν₀ + 2 * j - m).factorial : ℝ) /
      (2 * ((ν₀ + 2 * j + m).factorial : ℝ)) *
        (∫ y in (-1 : ℝ)..1, (1 - y ^ 2) ^ m * G y * (legInt_D (ν₀ + 2 * j) m y).re) with hα
  have hD : ∀ μ : ℕ, Continuous fun x : ℝ => (legInt_D μ m x).re := fun μ =>
    Complex.continuous_re.comp (legInt_cont_D μ m)
  have hw : Continuous fun x : ℝ => (1 - x ^ 2) ^ m := by fun_prop
  have h := intervalIntegral.hasSum_integral_of_dominated_convergence (μ := volume)
    (a := (-1 : ℝ)) (b := 1) (F := fun j x => (1 - x ^ 2) ^ m * G x * (α j *
      (legInt_D (ν₀ + 2 * j) m x).re)) (f := fun x => (1 - x ^ 2) ^ m * G x * G x)
    (fun j _ => MG * u j)
    (fun j => ((hw.mul hGc).mul (continuous_const.mul (hD _))).aestronglyMeasurable)
    (fun j => ?_) ?_ intervalIntegrable_const ?_
  · convert h using 1
    · funext j
      rw [show (fun x : ℝ => (1 - x ^ 2) ^ m * G x * (α j * (legInt_D (ν₀ + 2 * j) m x).re)) =
        fun x => α j * ((1 - x ^ 2) ^ m * G x * (legInt_D (ν₀ + 2 * j) m x).re) by
          funext x; ring, intervalIntegral.integral_const_mul]
    · refine intervalIntegral.integral_congr fun x _ => ?_
      simp only [hG]; ring
  · refine Filter.Eventually.of_forall fun x hx => ?_
    rw [uIoc_of_le (by norm_num)] at hx
    have hx' : x ∈ Icc (-1 : ℝ) 1 := ⟨hx.1.le, hx.2⟩
    have h1 : 0 ≤ 1 - x ^ 2 := by nlinarith [hx'.1, hx'.2]
    have hw0 : 0 ≤ (1 - x ^ 2) ^ m := pow_nonneg h1 m
    have hw1 : (1 - x ^ 2) ^ m ≤ 1 := pow_le_one₀ h1 (by nlinarith)
    have hbj := hb j x hx'
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hw0]
    calc (1 - x ^ 2) ^ m * |G x| * |α j * (legInt_D (ν₀ + 2 * j) m x).re|
        ≤ 1 * MG * u j := by
          refine mul_le_mul (mul_le_mul hw1 (hM x hx') (abs_nonneg _) zero_le_one) ?_
            (abs_nonneg _) (mul_nonneg zero_le_one ((abs_nonneg _).trans (hM 0 (by norm_num))))
          simpa only [hα, mul_assoc] using hbj
      _ = MG * u j := by ring
  · exact Filter.Eventually.of_forall fun x _ => hu.mul_left MG
  · filter_upwards [MeasureTheory.Measure.ae_ne volume (1 : ℝ)] with x hx1 hx
    rw [uIoc_of_le (by norm_num)] at hx
    have hxo : x ∈ Ioo (-1 : ℝ) 1 := ⟨hx.1, lt_of_le_of_ne hx.2 hx1⟩
    have := (hexp x hxo).mul_left ((1 - x ^ 2) ^ m * G x)
    simpa only [hα, mul_assoc] using this

/-- **The normalization** (DLMF 30.8.5):
`∑_{k ≥ -R} a^m_{n,k}(γ²) a^{-m}_{n,k}(γ²)/(2n+4k+1) = 1/(2n+1)` (equivalent to 30.4.1).
Proved by Parseval's identity for the expansion 30.8.1. -/
@[dlmf 30.8.E5]
theorem hasSum_spheroidalCoeff_normalization {n m : ℕ} (hmn : m ≤ n) (γ2 : ℝ) :
    HasSum (fun j : ℕ =>
        let k : ℤ := (j : ℤ) - ((n - m) / 2 : ℕ)
        spheroidalCoeff n m γ2 k * spheroidalCoeffNeg n m γ2 k / (2 * (n : ℝ) + 4 * k + 1))
      (1 / (2 * (n : ℝ) + 1)) := by
  have hf1 : (0 : ℝ) < ((n - m).factorial : ℝ) := by positivity
  have hf2 : (0 : ℝ) < ((n + m).factorial : ℝ) := by positivity
  have hn : (0 : ℝ) < 2 * n + 1 := by positivity
  have h := (p2y_parseval hmn γ2).mul_left (((n - m).factorial : ℝ) / (2 * (n + m).factorial))
  convert h using 1
  · funext j
    obtain ⟨ν, hν⟩ : ∃ ν, ν = n - 2 * ((n - m) / 2) + 2 * j := ⟨_, rfl⟩
    have hνi : (ν : ℤ) = n + 2 * ((j : ℤ) - ((n - m) / 2 : ℕ)) := by omega
    have hνr : ((ν : ℕ) : ℝ) = n + 2 * ((((j : ℤ) - ((n - m) / 2 : ℕ)) : ℤ) : ℝ) := by
      exact_mod_cast hνi
    have hr : 2 * (n : ℝ) + 4 * ((((j : ℤ) - ((n - m) / 2 : ℕ)) : ℤ) : ℝ) + 1 =
        2 * ((ν : ℕ) : ℝ) + 1 := by linarith
    have h1 : ((n : ℤ) - m + 2 * ((j : ℤ) - ((n - m) / 2 : ℕ))).toNat = ν - m := by omega
    have h2 : ((n : ℤ) + m + 2 * ((j : ℤ) - ((n - m) / 2 : ℕ))).toNat = ν + m := by omega
    simp only []
    rw [spheroidalCoeffNeg_of_le γ2 (by omega), h1, h2, p2y_coeff_eq hmn γ2 j, ← hν]
    rw [hr]
    set B := ∫ y in (-1 : ℝ)..1, (1 - y ^ 2) ^ m * (spheroidalPsFactor n m γ2 y).re *
      (legInt_D ν m y).re
    have hs : ((-1 : ℝ) ^ ((j : ℤ) - ((n - m) / 2 : ℕ)) * (-1) ^ m) ^ 2 = 1 := by
      rw [mul_pow, ← zpow_natCast, ← zpow_mul, ← pow_mul]
      rw [show (((j : ℤ) - ((n - m) / 2 : ℕ)) * ((2 : ℕ) : ℤ)) =
        2 * ((j : ℤ) - ((n - m) / 2 : ℕ)) by push_cast; ring, zpow_mul]
      norm_num
    have hg1 : (0 : ℝ) < ((ν - m).factorial : ℝ) := by positivity
    have hg2 : (0 : ℝ) < ((ν + m).factorial : ℝ) := by positivity
    have hν1 : (0 : ℝ) < 2 * ((ν : ℕ) : ℝ) + 1 := by positivity
    field_simp
    rw [← mul_pow, hs, one_mul]
  · field_simp

end DLMF.Spheroidal
end
