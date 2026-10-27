/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Spheroidal.FerrersDefs
public import DLMF.Legendre.IntegralTools
public import DLMF.Spheroidal.Angular
public import Mathlib.Tactic.Monotonicity.Lemmas

/-!
# Expansions in series of Ferrers functions (DLMF §30.8)

Statement acquisition from NIST DLMF (version 1.2.8), checked 2026-10-26. Admitted statements
are not completed proofs; see `DLMF30Acquisition.md`.

* §30.8(i): the expansion 30.8.1 of `𝖯s^m_n` in Ferrers functions with the coefficients 30.8.2,
  the three-term recurrence 30.8.4 with the coefficients 30.8.3 (`A_{-R} = 0` proved), the
  normalization 30.8.5–30.8.6 and the asymptotic ratios 30.8.7, 30.8.8;
* §30.8(ii): the expansion 30.8.9 of `𝖰s^m_n` with the recessive coefficients `a'^m_{n,k}`
  (30.8.10, 30.8.11) and the extended coefficients `a^m_{n,k}`, `-N ≤ k < -R`.

Indices: `R = ⌊(n-m)/2⌋`, `N = ⌊(n+m)/2⌋`; sums over `k ≥ -R` are written over `j : ℕ` with
`k = j - R`. Numerical checks: the recurrence and normalization were used to compute `𝖯s` and
`𝖰s` (compared with SciPy and with 30.4.1); the series 30.8.9 reproduces the Wronskian 30.5.4
and the parity 30.5.2 to 25 digits, provided the extended coefficients are included in `A^m_n`;
the project's `ferrersQ` agrees with mpmath at the low degrees `-m ≤ ν < m` that occur in 30.8.9.
-/

@[expose] public noncomputable section

open Complex Set Filter Asymptotics DLMF.Legendre MeasureTheory
open scoped Topology Real

namespace DLMF.Spheroidal

/-! ### §30.8(i) Functions of the first kind -/

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

/-! #### Proof of the ratio asymptotics 30.8.7

For `γ² ≠ 0` the coefficients are not eventually zero (else backward recursion with `A_k ≠ 0`
and 30.8.1 would give `𝖯s = 0`); with `|a_{j+1}| ≤ (|a_j| + |a_{j+2}|)/8` and the linear bound
this forces `|a_{j+1}| ≤ |a_j|/4` eventually. -/

/-- `A_k ≠ 0` for `k > -R` when `γ² ≠ 0`. -/
lemma p2y_recA_ne_zero {n m : ℕ} (hmn : m ≤ n) {γ2 : ℝ} (hγ : γ2 ≠ 0) {k : ℤ}
    (hk : -(((n - m) / 2 : ℕ) : ℤ) < k) : spheroidalRecA n m γ2 k ≠ 0 := by
  unfold spheroidalRecA
  have h1 : ((n : ℤ) - m + 2 * k - 1) ≠ 0 := by omega
  have h2 : ((n : ℤ) - m + 2 * k) ≠ 0 := by omega
  have h3 : (2 * (n : ℤ) + 4 * k - 3) ≠ 0 := by omega
  have h4 : (2 * (n : ℤ) + 4 * k - 1) ≠ 0 := by omega
  have h1' : ((n : ℝ) - m + 2 * k - 1) ≠ 0 := by exact_mod_cast h1
  have h2' : ((n : ℝ) - m + 2 * k) ≠ 0 := by exact_mod_cast h2
  have h3' : (2 * (n : ℝ) + 4 * k - 3) ≠ 0 := by exact_mod_cast h3
  have h4' : (2 * (n : ℝ) + 4 * k - 1) ≠ 0 := by exact_mod_cast h4
  exact div_ne_zero (mul_ne_zero (neg_ne_zero.mpr hγ) (mul_ne_zero h1' h2'))
    (mul_ne_zero h3' h4')

/-- For `γ² ≠ 0` the coefficients `a^m_{n,k}`, `k ≥ -R`, are not eventually zero. -/
lemma p2y_coeff_not_eventually_zero {n m : ℕ} (hmn : m ≤ n) {γ2 : ℝ} (hγ : γ2 ≠ 0) :
    ¬ ∃ J : ℕ, ∀ j : ℕ, J ≤ j → spheroidalCoeff n m γ2 ((j : ℤ) - ((n - m) / 2 : ℕ)) = 0 := by
  rintro ⟨J, hJ⟩
  have hall : ∀ d j : ℕ, J ≤ j + d → spheroidalCoeff n m γ2 ((j : ℤ) - ((n - m) / 2 : ℕ)) = 0 := by
    intro d
    induction d with
    | zero => intro j hj; exact hJ j (by omega)
    | succ d ih =>
      intro j _
      have h1 := ih (j + 1) (by omega)
      have h2 := ih (j + 2) (by omega)
      have hrec := spheroidalCoeff_recurrence_of_le hmn γ2
        (k := ((j + 1 : ℕ) : ℤ) - ((n - m) / 2 : ℕ)) (by omega)
      simp only [show -(((n - m) / 2 : ℕ) : ℤ) ≤ ((j + 1 : ℕ) : ℤ) - ((n - m) / 2 : ℕ) - 1 by
        omega, ↓reduceIte] at hrec
      rw [show ((j + 1 : ℕ) : ℤ) - ((n - m) / 2 : ℕ) - 1 = (j : ℤ) - ((n - m) / 2 : ℕ) by
          push_cast; ring,
        show ((j + 1 : ℕ) : ℤ) - ((n - m) / 2 : ℕ) + 1 = ((j + 2 : ℕ) : ℤ) - ((n - m) / 2 : ℕ) by
          push_cast; ring, h1, h2] at hrec
      simp only [mul_zero, add_zero] at hrec
      exact (mul_eq_zero.mp hrec).resolve_left (p2y_recA_ne_zero hmn hγ (by omega))
  have hz : ∀ j : ℕ, spheroidalCoeff n m γ2 ((j : ℤ) - ((n - m) / 2 : ℕ)) = 0 :=
    fun j => hall J j (by omega)
  have hG : ∀ x ∈ Ioo (-1 : ℝ) 1, (spheroidalPsFactor n m γ2 x).re = 0 := by
    intro x hx
    have h := p2y_factor_expansion hmn γ2 x hx
    have h0 : ∀ j : ℕ, (2 * ((n - 2 * ((n - m) / 2) + 2 * j : ℕ) : ℝ) + 1) *
          ((n - 2 * ((n - m) / 2) + 2 * j - m).factorial : ℝ) /
          (2 * ((n - 2 * ((n - m) / 2) + 2 * j + m).factorial : ℝ)) *
        (∫ y in (-1 : ℝ)..1, (1 - y ^ 2) ^ m * (spheroidalPsFactor n m γ2 y).re *
          (legInt_D (n - 2 * ((n - m) / 2) + 2 * j) m y).re) = 0 := by
      intro j
      have := hz j
      rw [p2y_coeff_eq hmn γ2 j] at this
      exact (mul_eq_zero.mp this).resolve_left (mul_ne_zero (zpow_ne_zero _ (by norm_num))
        (pow_ne_zero _ (by norm_num)))
    simp only [h0, zero_mul] at h
    exact h.unique hasSum_zero
  have hnorm := (spheroidalPsFactor_spec hmn γ2).normalized
  have h0 : ∫ x in (-1 : ℝ)..1, (1 - x ^ 2) ^ m * (spheroidalPsFactor n m γ2 x).re ^ 2 = 0 := by
    rw [p2y_integral_congr_Ioo (f₂ := fun _ => (0 : ℝ)) (fun x hx => by
      simp only [hG x hx]; ring)]
    simp
  rw [h0] at hnorm
  have : (0 : ℝ) < 2 / (2 * n + 1) * (((n + m).factorial : ℝ) / (n - m).factorial) := by
    positivity
  linarith

/-- Eventually `|a_{j+1}| ≤ |a_j|/4`. -/
lemma p2y_coeff_ratio_le {n m : ℕ} (hmn : m ≤ n) (γ2 : ℝ) :
    ∃ J : ℕ, ∀ j : ℕ, J ≤ j →
      |spheroidalCoeff n m γ2 (((j + 1 : ℕ) : ℤ) - ((n - m) / 2 : ℕ))| ≤
        |spheroidalCoeff n m γ2 ((j : ℤ) - ((n - m) / 2 : ℕ))| / 4 := by
  obtain ⟨J, hJ⟩ := p2y_coeff_eps hmn γ2 (by norm_num : (0 : ℝ) < 1 / 8)
  obtain ⟨M, hM0, hM⟩ := p2y_coeff_linear hmn γ2
  refine ⟨J, fun j0 hj0 => ?_⟩
  set a : ℕ → ℝ := fun j => |spheroidalCoeff n m γ2 ((j : ℤ) - ((n - m) / 2 : ℕ))| with ha
  change a (j0 + 1) ≤ a j0 / 4
  by_contra hcon
  push Not at hcon
  have key : ∀ i : ℕ, a (j0 + i) / 4 < a (j0 + i + 1) ∧ 4 ^ i * a (j0 + 1) ≤ a (j0 + i + 1) := by
    intro i
    induction i with
    | zero => exact ⟨by simpa using hcon, by simp⟩
    | succ i ih =>
      have h := hJ (j0 + i) (by omega)
      change a (j0 + i + 1) ≤ 1 / 8 * (a (j0 + i) + a (j0 + i + 2)) at h
      have hnn : 0 ≤ a (j0 + i + 1) := abs_nonneg _
      have h2 : 4 * a (j0 + i + 1) < a (j0 + i + 2) := by linarith [ih.1]
      refine ⟨by rw [show j0 + (i + 1) = j0 + i + 1 by ring]; linarith, ?_⟩
      rw [show j0 + (i + 1) + 1 = j0 + i + 2 by ring, pow_succ]
      nlinarith [ih.2]
  have hδ : 0 < a (j0 + 1) := lt_of_le_of_lt (by positivity) (key 0).1
  obtain ⟨i, hi⟩ := pow_unbounded_of_one_lt (M * (j0 + 2) / a (j0 + 1)) (by norm_num : (1 : ℝ) < 2)
  have hlin := hM (j0 + i + 1)
  have hk := (key i).2
  have h2i : ((i : ℝ) + 1) ≤ 2 ^ i := by
    have := Nat.lt_two_pow_self (n := i)
    exact_mod_cast this
  have h4 : (4 : ℝ) ^ i = 2 ^ i * 2 ^ i := by rw [← mul_pow]; norm_num
  rw [div_lt_iff₀ hδ] at hi
  have hj0 : (0 : ℝ) ≤ j0 := Nat.cast_nonneg j0
  have : (4 : ℝ) ^ i * a (j0 + 1) ≤ M * (j0 + 2) * 2 ^ i := by
    calc (4 : ℝ) ^ i * a (j0 + 1) ≤ a (j0 + i + 1) := hk
      _ ≤ M * (((j0 + i + 1 : ℕ) : ℝ) + 1) := hlin
      _ ≤ M * ((j0 + 2) * (i + 1)) := by
          gcongr; push_cast; nlinarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)]
      _ ≤ M * (j0 + 2) * 2 ^ i := by
          rw [← mul_assoc]; exact mul_le_mul_of_nonneg_left h2i (by positivity)
  rw [h4] at this
  have h2pos : (0 : ℝ) < 2 ^ i := by positivity
  nlinarith

/-- `|B_k - (n+2k)(n+2k+1)| ≤ 2|γ²|(1+m²)` for `k ≥ 1`. -/
lemma p2y_recB_close {n m : ℕ} (γ2 : ℝ) {k : ℤ} (hk : 1 ≤ k) :
    |spheroidalRecB n m γ2 k - ((n : ℝ) + 2 * k) * ((n : ℝ) + 2 * k + 1)| ≤
      2 * |γ2| * (1 + m ^ 2) := by
  have kr : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  unfold spheroidalRecB
  set F := (((n : ℝ) + 2 * k) * ((n : ℝ) + 2 * k + 1) - 1 + m ^ 2) /
    ((2 * (n : ℝ) + 4 * k - 1) * (2 * (n : ℝ) + 4 * k + 3)) with hF
  have hQ : 0 < (2 * (n : ℝ) + 4 * k - 1) * (2 * (n : ℝ) + 4 * k + 3) := by nlinarith
  have hF0 : 0 ≤ F := div_nonneg (by nlinarith) hQ.le
  have hF1 : F ≤ 1 + m ^ 2 := by
    have hQ1 : 1 ≤ (2 * (n : ℝ) + 4 * k - 1) * (2 * (n : ℝ) + 4 * k + 3) := by nlinarith
    rw [hF, div_le_iff₀ hQ]
    nlinarith [mul_nonneg (sq_nonneg (m : ℝ)) (by linarith : (0 : ℝ) ≤
      (2 * (n : ℝ) + 4 * k - 1) * (2 * (n : ℝ) + 4 * k + 3) - 1)]
  rw [show 2 * γ2 * (((n : ℝ) + 2 * k) * ((n : ℝ) + 2 * k + 1) - 1 + m ^ 2) /
    ((2 * (n : ℝ) + 4 * k - 1) * (2 * (n : ℝ) + 4 * k + 3)) = 2 * γ2 * F by rw [hF]; ring,
    show ((n : ℝ) + 2 * k) * ((n : ℝ) + 2 * k + 1) - 2 * γ2 * F -
      ((n : ℝ) + 2 * k) * ((n : ℝ) + 2 * k + 1) = -(2 * γ2 * F) by ring, abs_neg, abs_mul,
    abs_mul, abs_of_nonneg hF0, abs_two, mul_assoc, mul_assoc]
  gcongr

/-- `|-4A_k - γ²| ≤ |γ²|(4m²+12m+7)/k` for `k ≥ 2`. -/
lemma p2y_recA_close {n m : ℕ} (hmn : m ≤ n) (γ2 : ℝ) {k : ℤ} (hk : 2 ≤ k) :
    |-4 * spheroidalRecA n m γ2 k - γ2| ≤ |γ2| * (4 * m ^ 2 + 12 * m + 7) / k := by
  have kr : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hmr : (m : ℝ) ≤ n := by exact_mod_cast hmn
  unfold spheroidalRecA
  set ν : ℝ := (n : ℝ) + 2 * k with hν
  have hν4 : 4 ≤ ν := by rw [hν]; linarith
  have hkν : (k : ℝ) ≤ ν := by rw [hν]; linarith
  have hQ : ν ^ 2 ≤ (2 * (n : ℝ) + 4 * k - 3) * (2 * (n : ℝ) + 4 * k - 1) := by
    rw [show (2 * (n : ℝ) + 4 * k - 3) * (2 * (n : ℝ) + 4 * k - 1) = (2 * ν - 3) * (2 * ν - 1) by
      rw [hν]; ring]
    nlinarith
  have hQ0 : 0 < (2 * (n : ℝ) + 4 * k - 3) * (2 * (n : ℝ) + 4 * k - 1) := by nlinarith
  rw [show -4 * (-γ2 * (((n : ℝ) - m + 2 * k - 1) * ((n : ℝ) - m + 2 * k)) /
      ((2 * (n : ℝ) + 4 * k - 3) * (2 * (n : ℝ) + 4 * k - 1))) - γ2 =
      γ2 * (((4 - 8 * m) * ν + 4 * m ^ 2 + 4 * m - 3) /
        ((2 * (n : ℝ) + 4 * k - 3) * (2 * (n : ℝ) + 4 * k - 1))) by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    set Qi := ((2 * (n : ℝ) + 4 * k - 3) * (2 * (n : ℝ) + 4 * k - 1))⁻¹ with hQi
    have hQQ : ((2 * (n : ℝ) + 4 * k - 3) * (2 * (n : ℝ) + 4 * k - 1)) * Qi = 1 :=
      mul_inv_cancel₀ hQ0.ne'
    rw [hν]
    linear_combination γ2 * hQQ]
  rw [abs_mul, abs_div, abs_of_pos hQ0, le_div_iff₀ (by linarith), mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  rw [div_mul_eq_mul_div, div_le_iff₀ hQ0]
  have hl : |(4 - 8 * (m : ℝ)) * ν + 4 * m ^ 2 + 4 * m - 3| ≤ (4 * m ^ 2 + 12 * m + 7) * ν := by
    rw [abs_le]; constructor <;> nlinarith [mul_nonneg hm0 (by linarith : (0 : ℝ) ≤ ν)]
  calc |(4 - 8 * (m : ℝ)) * ν + 4 * m ^ 2 + 4 * m - 3| * k
      ≤ (4 * m ^ 2 + 12 * m + 7) * ν * ν :=
        mul_le_mul hl hkν (by linarith) (by positivity)
    _ ≤ _ := by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (by nlinarith [hQ]) (by positivity)

/-- The algebra of 30.8.7: from `16 D E = 4k² X + γ² Y`, `D ≥ k²`, `|X| ≤ c₃/k`, `|Y| ≤ c₂ k`. -/
lemma p2y_alg_ratio {k D X Y E γ2 c₂ c₃ : ℝ} (hk : 1 ≤ k) (hD : k ^ 2 ≤ D)
    (h : 16 * D * E = 4 * k ^ 2 * X + γ2 * Y) (hX : |X| ≤ c₃ / k) (hY : |Y| ≤ c₂ * k) :
    |E| ≤ (4 * c₃ + |γ2| * c₂) / 16 * k⁻¹ := by
  have hk0 : 0 < k := by linarith
  have hD0 : 0 < D := by nlinarith
  have h1 : 16 * D * |E| ≤ k * (4 * c₃ + |γ2| * c₂) := by
    have := congrArg abs h
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 16 * D)] at this
    rw [this]
    have hX' : k * |X| ≤ c₃ := by rw [le_div_iff₀ hk0] at hX; linarith
    calc |4 * k ^ 2 * X + γ2 * Y| ≤ |4 * k ^ 2 * X| + |γ2 * Y| := abs_add_le _ _
      _ = 4 * k * (k * |X|) + |γ2| * |Y| := by
          rw [abs_mul (4 * k ^ 2), abs_mul γ2, abs_of_pos (by positivity : (0 : ℝ) < 4 * k ^ 2)]
          ring
      _ ≤ 4 * k * c₃ + |γ2| * (c₂ * k) := by gcongr
      _ = _ := by ring
  have hE := abs_nonneg E
  rw [← div_eq_mul_inv, le_div_iff₀ hk0]
  nlinarith

/-- For `γ² ≠ 0`, eventually `a_j ≠ 0` and `|a_{j+1}| ≤ |a_j|/4`. -/
lemma p2y_coeff_ne_zero {n m : ℕ} (hmn : m ≤ n) {γ2 : ℝ} (hγ : γ2 ≠ 0) :
    ∃ J : ℕ, ∀ j : ℕ, J ≤ j → spheroidalCoeff n m γ2 ((j : ℤ) - ((n - m) / 2 : ℕ)) ≠ 0 ∧
      |spheroidalCoeff n m γ2 (((j + 1 : ℕ) : ℤ) - ((n - m) / 2 : ℕ))| ≤
        |spheroidalCoeff n m γ2 ((j : ℤ) - ((n - m) / 2 : ℕ))| / 4 := by
  obtain ⟨J, hJ⟩ := p2y_coeff_ratio_le hmn γ2
  refine ⟨J, fun j hj => ⟨fun h0 => ?_, hJ j hj⟩⟩
  apply p2y_coeff_not_eventually_zero hmn hγ
  refine ⟨j, fun i hi => ?_⟩
  obtain ⟨d, rfl⟩ : ∃ d, i = j + d := ⟨i - j, by omega⟩
  induction d with
  | zero => simpa using h0
  | succ d ih =>
    have h := hJ (j + d) (by omega)
    rw [ih (by omega), abs_zero, zero_div] at h
    exact abs_nonpos_iff.mp h

/-- **Ratio asymptotics** (DLMF 30.8.7): `k² a^m_{n,k}(γ²)/a^m_{n,k-1}(γ²) = γ²/16 + O(1/k)` as
`k → ∞`. Proved: for `γ² = 0` the coefficients vanish for `k ≥ 1`; otherwise they are eventually
nonzero with `|a_{k+1}/a_k| ≤ 1/4`, and 30.8.4 gives
`k² a_k/a_{k-1} = -k² A_k/(B_k - λ + C_k a_{k+1}/a_k)`. -/
@[dlmf 30.8.E7]
theorem spheroidalCoeff_ratio_isBigO {n m : ℕ} (hmn : m ≤ n) (γ2 : ℝ) :
    (fun k : ℕ => (k : ℝ) ^ 2 * spheroidalCoeff n m γ2 k / spheroidalCoeff n m γ2 ((k : ℤ) - 1) -
        γ2 / 16) =O[atTop] (fun k : ℕ => (k : ℝ)⁻¹) := by
  by_cases hγ : γ2 = 0
  · subst hγ
    refine (isBigO_zero (fun k : ℕ => (k : ℝ)⁻¹) atTop).congr' ?_ EventuallyEq.rfl
    filter_upwards [eventually_ge_atTop 1] with k hk
    have hrec := spheroidalCoeff_recurrence_of_le hmn 0 (k := (k : ℤ)) (by omega)
    have hA : spheroidalRecA n m 0 k = 0 := by simp [spheroidalRecA]
    have hC : spheroidalRecC n m 0 k = 0 := by simp [spheroidalRecC]
    have hB : spheroidalRecB n m 0 k = ((n : ℝ) + 2 * k) * ((n : ℝ) + 2 * k + 1) := by
      simp [spheroidalRecB]
    rw [hA, hC, hB, p1s_spheroidalEigenvalue_zero hmn] at hrec
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hpos : ((n : ℝ) + 2 * k) * ((n : ℝ) + 2 * k + 1) - n * (n + 1) ≠ 0 := by
      have : (0 : ℝ) < ((n : ℝ) + 2 * k) * ((n : ℝ) + 2 * k + 1) - n * (n + 1) := by nlinarith
      exact this.ne'
    have h0 : spheroidalCoeff n m 0 k = 0 := by
      simp only [zero_mul, zero_add, add_zero] at hrec
      exact (mul_eq_zero.mp hrec).resolve_left hpos
    simp [h0]
  -- `γ² ≠ 0`
  obtain ⟨J1, hJ1⟩ := p2y_coeff_ne_zero hmn hγ
  set R := (n - m) / 2 with hR
  set lam := spheroidalEigenvalue n m γ2
  set c₀ : ℝ := 2 * |γ2| * (1 + m ^ 2) + |lam| + |γ2| / 4 with hc₀
  set c₂ : ℝ := (n : ℝ) ^ 2 + 5 * n + 2 + c₀ with hc₂
  set c₃ : ℝ := |γ2| * (4 * m ^ 2 + 12 * m + 7) with hc₃
  obtain ⟨K0, hK0⟩ := exists_nat_ge c₀
  refine IsBigO.of_bound ((4 * c₃ + |γ2| * c₂) / 16) ?_
  filter_upwards [eventually_ge_atTop (J1 + 2 + K0)] with k hk
  have ha0 : spheroidalCoeff n m γ2 ((k : ℤ) - 1) ≠ 0 := by
    have := (hJ1 (k - 1 + R) (by omega)).1
    have h1k : 1 ≤ k := by omega
    rwa [show ((k - 1 + R : ℕ) : ℤ) - R = (k : ℤ) - 1 by push_cast [Nat.cast_sub h1k]; ring]
      at this
  have ha1 : spheroidalCoeff n m γ2 (k : ℤ) ≠ 0 := by
    have := (hJ1 (k + R) (by omega)).1
    rwa [show ((k + R : ℕ) : ℤ) - R = (k : ℤ) by push_cast; ring] at this
  have hs : |spheroidalCoeff n m γ2 ((k : ℤ) + 1)| ≤ |spheroidalCoeff n m γ2 (k : ℤ)| / 4 := by
    have := (hJ1 (k + R) (by omega)).2
    rwa [show ((k + R + 1 : ℕ) : ℤ) - R = (k : ℤ) + 1 by push_cast; ring,
      show ((k + R : ℕ) : ℤ) - R = (k : ℤ) by push_cast; ring] at this
  have hk2 : (2 : ℤ) ≤ (k : ℤ) := by omega
  have hk1 : (1 : ℤ) ≤ (k : ℤ) := by omega
  have hkr : (2 : ℝ) ≤ k := by exact_mod_cast hk2
  have hkc : c₀ ≤ (k : ℝ) := by
    have : (K0 : ℝ) ≤ k := by exact_mod_cast (by omega : K0 ≤ k)
    linarith
  have hrec := spheroidalCoeff_recurrence_of_le hmn γ2 (k := (k : ℤ)) (by omega)
  simp only [show -(((n - m) / 2 : ℕ) : ℤ) ≤ (k : ℤ) - 1 by omega, ↓reduceIte] at hrec
  obtain ⟨hA, hC, -⟩ := p2y_rec_bounds hmn γ2 hk1
  have hBc := p2y_recB_close (n := n) (m := m) γ2 hk1
  have hX := p2y_recA_close hmn γ2 hk2
  set a0 := spheroidalCoeff n m γ2 ((k : ℤ) - 1)
  set a1 := spheroidalCoeff n m γ2 (k : ℤ)
  set a2 := spheroidalCoeff n m γ2 ((k : ℤ) + 1)
  set A := spheroidalRecA n m γ2 k
  set B := spheroidalRecB n m γ2 k
  set C := spheroidalRecC n m γ2 k
  set sr := a2 / a1 with hsr
  have hsr4 : |sr| ≤ 1 / 4 := by
    rw [hsr, abs_div, div_le_iff₀ (abs_pos.mpr ha1)]; linarith
  have hCs : |C * sr| ≤ |γ2| / 4 := by
    rw [abs_mul]
    calc |C| * |sr| ≤ |γ2| * (1 / 4) := mul_le_mul hC hsr4 (abs_nonneg _) (abs_nonneg _)
      _ = _ := by ring
  set D := B - lam + C * sr with hD
  set r := a1 / a0 with hr
  have hrD : r * D = -A := by
    rw [hr, hD, hsr]
    field_simp
    linear_combination hrec
  set ν : ℝ := (n : ℝ) + 2 * k with hν
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hlam := abs_le.mp (le_refl |lam|)
  have hBc' := abs_le.mp hBc
  have hCs' := abs_le.mp hCs
  have hlam' : -|lam| ≤ lam ∧ lam ≤ |lam| := ⟨neg_abs_le lam, le_abs_self lam⟩
  simp only [Int.cast_natCast] at hBc' hX
  have hkk : (k : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
  have hk1r : (1 : ℝ) ≤ k := by linarith
  have hc0 : 0 ≤ c₀ := by positivity
  set t := B - ((n : ℝ) + 2 * k) * ((n : ℝ) + 2 * k + 1) with ht
  have hid : D = 4 * (k : ℝ) ^ 2 + ((n : ℝ) ^ 2 + n + (4 * n + 2) * k) + t - lam + C * sr := by
    rw [hD, ht]; ring
  have hpos : 0 ≤ (n : ℝ) ^ 2 + n + (4 * n + 2) * k := by positivity
  have hDk : (k : ℝ) ^ 2 ≤ D := by
    rw [hid]; linarith [hBc'.1, hCs'.1, hlam'.2]
  have h1 : (n : ℝ) ^ 2 + n + c₀ ≤ ((n : ℝ) ^ 2 + n + c₀) * k :=
    le_mul_of_one_le_right (by positivity) hk1r
  have hY : |4 * (k : ℝ) ^ 2 - D| ≤ c₂ * k := by
    have e1 : 4 * (k : ℝ) ^ 2 - (4 * (k : ℝ) ^ 2 + ((n : ℝ) ^ 2 + n + (4 * n + 2) * k) + t - lam +
        C * sr) = -((n : ℝ) ^ 2 + n) - (4 * n + 2) * k - t + lam - C * sr := by ring
    have e2 : c₂ * k = ((n : ℝ) ^ 2 + n + c₀) * k + (4 * n + 2) * k := by rw [hc₂]; ring
    rw [hid, e1, e2, abs_le]
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hnk : 0 ≤ (4 * (n : ℝ) + 2) * k := by positivity
    constructor <;> linarith [hBc'.1, hBc'.2, hCs'.1, hCs'.2, hlam'.1, hlam'.2]
  have hE : 16 * D * ((k : ℝ) ^ 2 * a1 / a0 - γ2 / 16) =
      4 * (k : ℝ) ^ 2 * (-4 * A - γ2) + γ2 * (4 * (k : ℝ) ^ 2 - D) := by
    rw [mul_div_assoc, ← hr]
    linear_combination 16 * (k : ℝ) ^ 2 * hrD
  have hfin := p2y_alg_ratio (c₃ := c₃) (by linarith) hDk hE (by rw [hc₃]; exact hX) hY
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_inv, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) k)]
  exact hfin

/-- For `γ² ≠ 0`, eventually `a_{k-1} ≠ 0`, `a_k ≠ 0` and `|a_k/a_{k-1}| ≤ |γ²|/k²`. -/
lemma p2y_ratio_small {n m : ℕ} (hmn : m ≤ n) {γ2 : ℝ} (hγ : γ2 ≠ 0) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k → spheroidalCoeff n m γ2 ((k : ℤ) - 1) ≠ 0 ∧
      spheroidalCoeff n m γ2 (k : ℤ) ≠ 0 ∧
      |spheroidalCoeff n m γ2 (k : ℤ) / spheroidalCoeff n m γ2 ((k : ℤ) - 1)| ≤
        |γ2| / (k : ℝ) ^ 2 := by
  -- `γ² ≠ 0`
  obtain ⟨J1, hJ1⟩ := p2y_coeff_ne_zero hmn hγ
  set R := (n - m) / 2 with hR
  set lam := spheroidalEigenvalue n m γ2
  set c₀ : ℝ := 2 * |γ2| * (1 + m ^ 2) + |lam| + |γ2| / 4 with hc₀
  set c₂ : ℝ := (n : ℝ) ^ 2 + 5 * n + 2 + c₀ with hc₂
  set c₃ : ℝ := |γ2| * (4 * m ^ 2 + 12 * m + 7) with hc₃
  obtain ⟨K0, hK0⟩ := exists_nat_ge c₀
  refine ⟨J1 + 2 + K0, fun k hk => ?_⟩
  have ha0 : spheroidalCoeff n m γ2 ((k : ℤ) - 1) ≠ 0 := by
    have := (hJ1 (k - 1 + R) (by omega)).1
    have h1k : 1 ≤ k := by omega
    rwa [show ((k - 1 + R : ℕ) : ℤ) - R = (k : ℤ) - 1 by push_cast [Nat.cast_sub h1k]; ring]
      at this
  have ha1 : spheroidalCoeff n m γ2 (k : ℤ) ≠ 0 := by
    have := (hJ1 (k + R) (by omega)).1
    rwa [show ((k + R : ℕ) : ℤ) - R = (k : ℤ) by push_cast; ring] at this
  have hs : |spheroidalCoeff n m γ2 ((k : ℤ) + 1)| ≤ |spheroidalCoeff n m γ2 (k : ℤ)| / 4 := by
    have := (hJ1 (k + R) (by omega)).2
    rwa [show ((k + R + 1 : ℕ) : ℤ) - R = (k : ℤ) + 1 by push_cast; ring,
      show ((k + R : ℕ) : ℤ) - R = (k : ℤ) by push_cast; ring] at this
  have hk2 : (2 : ℤ) ≤ (k : ℤ) := by omega
  have hk1 : (1 : ℤ) ≤ (k : ℤ) := by omega
  have hkr : (2 : ℝ) ≤ k := by exact_mod_cast hk2
  have hkc : c₀ ≤ (k : ℝ) := by
    have : (K0 : ℝ) ≤ k := by exact_mod_cast (by omega : K0 ≤ k)
    linarith
  have hrec := spheroidalCoeff_recurrence_of_le hmn γ2 (k := (k : ℤ)) (by omega)
  simp only [show -(((n - m) / 2 : ℕ) : ℤ) ≤ (k : ℤ) - 1 by omega, ↓reduceIte] at hrec
  obtain ⟨hA, hC, -⟩ := p2y_rec_bounds hmn γ2 hk1
  have hBc := p2y_recB_close (n := n) (m := m) γ2 hk1
  have hX := p2y_recA_close hmn γ2 hk2
  set a0 := spheroidalCoeff n m γ2 ((k : ℤ) - 1)
  set a1 := spheroidalCoeff n m γ2 (k : ℤ)
  set a2 := spheroidalCoeff n m γ2 ((k : ℤ) + 1)
  set A := spheroidalRecA n m γ2 k
  set B := spheroidalRecB n m γ2 k
  set C := spheroidalRecC n m γ2 k
  set sr := a2 / a1 with hsr
  have hsr4 : |sr| ≤ 1 / 4 := by
    rw [hsr, abs_div, div_le_iff₀ (abs_pos.mpr ha1)]; linarith
  have hCs : |C * sr| ≤ |γ2| / 4 := by
    rw [abs_mul]
    calc |C| * |sr| ≤ |γ2| * (1 / 4) := mul_le_mul hC hsr4 (abs_nonneg _) (abs_nonneg _)
      _ = _ := by ring
  set D := B - lam + C * sr with hD
  set r := a1 / a0 with hr
  have hrD : r * D = -A := by
    rw [hr, hD, hsr]
    field_simp
    linear_combination hrec
  set ν : ℝ := (n : ℝ) + 2 * k with hν
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hlam := abs_le.mp (le_refl |lam|)
  have hBc' := abs_le.mp hBc
  have hCs' := abs_le.mp hCs
  have hlam' : -|lam| ≤ lam ∧ lam ≤ |lam| := ⟨neg_abs_le lam, le_abs_self lam⟩
  simp only [Int.cast_natCast] at hBc' hX
  have hkk : (k : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
  have hk1r : (1 : ℝ) ≤ k := by linarith
  have hc0 : 0 ≤ c₀ := by positivity
  set t := B - ((n : ℝ) + 2 * k) * ((n : ℝ) + 2 * k + 1) with ht
  have hid : D = 4 * (k : ℝ) ^ 2 + ((n : ℝ) ^ 2 + n + (4 * n + 2) * k) + t - lam + C * sr := by
    rw [hD, ht]; ring
  have hpos : 0 ≤ (n : ℝ) ^ 2 + n + (4 * n + 2) * k := by positivity
  have hDk : (k : ℝ) ^ 2 ≤ D := by
    rw [hid]; linarith [hBc'.1, hCs'.1, hlam'.2]
  have h1 : (n : ℝ) ^ 2 + n + c₀ ≤ ((n : ℝ) ^ 2 + n + c₀) * k :=
    le_mul_of_one_le_right (by positivity) hk1r
  refine ⟨ha0, ha1, ?_⟩
  have hk0 : (0 : ℝ) < (k : ℝ) ^ 2 := by positivity
  have hD0 : 0 < D := lt_of_lt_of_le hk0 hDk
  have hrA : |r| * D = |A| := by
    rw [← abs_neg A, ← hrD, abs_mul, abs_of_pos hD0]
  change |r| ≤ _
  rw [le_div_iff₀ hk0]
  calc |r| * (k : ℝ) ^ 2 ≤ |r| * D := mul_le_mul_of_nonneg_left hDk (abs_nonneg _)
    _ = |A| := hrA
    _ ≤ |γ2| := hA

/-- `|A_k| ≥ |γ²|/16` when `n + 2k ≥ 2m + 2`. -/
lemma p2y_recA_ge {n m : ℕ} (γ2 : ℝ) {k : ℤ} (hk : 2 * (m : ℤ) + 2 ≤ n + 2 * k) :
    |γ2| / 16 ≤ |spheroidalRecA n m γ2 k| := by
  have hkr : 2 * (m : ℝ) + 2 ≤ n + 2 * k := by exact_mod_cast hk
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  unfold spheroidalRecA
  have hQ : 0 < (2 * (n : ℝ) + 4 * k - 3) * (2 * (n : ℝ) + 4 * k - 1) := by nlinarith
  have hP : (0 : ℝ) ≤ ((n : ℝ) - m + 2 * k - 1) * ((n : ℝ) - m + 2 * k) := by nlinarith
  rw [mul_div_assoc, abs_mul, abs_neg, abs_div, abs_of_pos hQ, abs_of_nonneg hP,
    show |γ2| / 16 = |γ2| * (1 / 16) by ring]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  rw [div_le_div_iff₀ (by norm_num) hQ]
  nlinarith

/-- **Ratio asymptotics** (DLMF 30.8.8):
`(λ^m_n(γ²) - B_k)/A_k · a^m_{n,k}(γ²)/a^m_{n,k-1}(γ²) = 1 + O(k⁻⁴)` as `k → ∞`.
Corrected: the hypothesis `γ2 ≠ 0` was added (2026-10-26), since at `γ² = 0` the statement fails
(`p2y_not_spheroidalCoeff_ratio_isBigO_four_zero`). Proved: by 30.8.4 the expression equals
`C_k (a_k/a_{k-1})(a_{k+1}/a_k)/A_k`, and both ratios are `O(k⁻²)` while `|A_k| ≥ |γ²|/16`. -/
@[dlmf 30.8.E8]
theorem spheroidalCoeff_ratio_isBigO_four {n m : ℕ} (hmn : m ≤ n) {γ2 : ℝ} (hγ : γ2 ≠ 0) :
    (fun k : ℕ => (spheroidalEigenvalue n m γ2 - spheroidalRecB n m γ2 k) /
        spheroidalRecA n m γ2 k *
          (spheroidalCoeff n m γ2 k / spheroidalCoeff n m γ2 ((k : ℤ) - 1)) - 1)
      =O[atTop] (fun k : ℕ => ((k : ℝ) ^ 4)⁻¹) := by
  obtain ⟨K, hK⟩ := p2y_ratio_small hmn hγ
  refine IsBigO.of_bound (16 * |γ2| ^ 2) ?_
  filter_upwards [eventually_ge_atTop (K + m + 2)] with k hk
  obtain ⟨ha0, ha1, hr⟩ := hK k (by omega)
  obtain ⟨-, ha2', hs⟩ := hK (k + 1) (by omega)
  push_cast at ha2' hs
  rw [show ((k : ℤ) + 1 - 1) = (k : ℤ) by ring] at hs
  have hk1 : (1 : ℤ) ≤ (k : ℤ) := by omega
  have hA0 := p2y_recA_ne_zero hmn hγ (k := (k : ℤ)) (by omega)
  have hAge := p2y_recA_ge (n := n) (m := m) γ2 (k := (k : ℤ)) (by omega)
  obtain ⟨-, hC, -⟩ := p2y_rec_bounds hmn γ2 hk1
  have hrec := spheroidalCoeff_recurrence_of_le hmn γ2 (k := (k : ℤ)) (by omega)
  simp only [show -(((n - m) / 2 : ℕ) : ℤ) ≤ (k : ℤ) - 1 by omega, ↓reduceIte] at hrec
  set a0 := spheroidalCoeff n m γ2 ((k : ℤ) - 1)
  set a1 := spheroidalCoeff n m γ2 (k : ℤ)
  set a2 := spheroidalCoeff n m γ2 ((k : ℤ) + 1)
  set A := spheroidalRecA n m γ2 k
  set B := spheroidalRecB n m γ2 k
  set C := spheroidalRecC n m γ2 k
  have e : (spheroidalEigenvalue n m γ2 - B) / A * (a1 / a0) - 1 =
      C * (a1 / a0) * (a2 / a1) / A := by
    field_simp
    linear_combination -hrec
  rw [e, Real.norm_eq_abs, Real.norm_eq_abs, abs_div, abs_mul, abs_mul]
  have hk1r : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hkpos : (0 : ℝ) < k := by linarith
  have hk2 : (k : ℝ) ^ 2 ≤ ((k : ℝ) + 1) ^ 2 := by nlinarith
  have hs' : |a2 / a1| ≤ |γ2| / (k : ℝ) ^ 2 :=
    hs.trans (div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) hk2)
  have hγ0 : 0 < |γ2| := abs_pos.mpr hγ
  rw [abs_inv, abs_of_pos (by positivity : (0 : ℝ) < (k : ℝ) ^ 4), div_le_iff₀ (lt_of_lt_of_le
    (by positivity) hAge)]
  calc |C| * |a1 / a0| * |a2 / a1| ≤ |γ2| * (|γ2| / (k : ℝ) ^ 2) * (|γ2| / (k : ℝ) ^ 2) := by
        gcongr
    _ = 16 * |γ2| ^ 2 * ((k : ℝ) ^ 4)⁻¹ * (|γ2| / 16) := by field_simp
    _ ≤ 16 * |γ2| ^ 2 * ((k : ℝ) ^ 4)⁻¹ * |A| := by gcongr

/-- **30.8.8 fails at `γ² = 0`** as stated: then `A_k = 0`, the Lean quotient
`(λ - B_k)/A_k` is `0`, and the expression is the constant `-1`, which is not `O(k⁻⁴)`. -/
lemma p2y_not_spheroidalCoeff_ratio_isBigO_four_zero (n m : ℕ) :
    ¬ (fun k : ℕ => (spheroidalEigenvalue n m 0 - spheroidalRecB n m 0 k) /
        spheroidalRecA n m 0 k *
          (spheroidalCoeff n m 0 k / spheroidalCoeff n m 0 ((k : ℤ) - 1)) - 1)
      =O[atTop] (fun k : ℕ => ((k : ℝ) ^ 4)⁻¹) := by
  intro h
  have hA : ∀ k : ℕ, spheroidalRecA n m 0 k = 0 := fun k => by simp [spheroidalRecA]
  simp only [hA, div_zero, zero_mul, zero_sub] at h
  have ht : Tendsto (fun k : ℕ => ((k : ℝ) ^ 4)⁻¹) atTop (𝓝 0) :=
    (tendsto_pow_atTop (by norm_num : (4 : ℕ) ≠ 0)).comp tendsto_natCast_atTop_atTop
      |>.inv_tendsto_atTop
  have h2 := h.trans_tendsto ht
  have h3 : Tendsto (fun _ : ℕ => (-1 : ℝ)) atTop (𝓝 (-1)) := tendsto_const_nhds
  have := tendsto_nhds_unique h3 h2
  norm_num at this

/-! ### §30.8(ii) Functions of the second kind -/

/-- **The expansion of `𝖰s`** (DLMF 30.8.9–30.8.11): for `-1 < x < 1`,
`𝖰s^m_n(x, γ²) = ∑_{k ≤ -N-1} (-1)^k a'^m_{n,k}(γ²) 𝖯^m_{n+2k}(x)
  + ∑_{k ≥ -N} (-1)^k a^m_{n,k}(γ²) 𝖰^m_{n+2k}(x)`, with `a'` the recessive solution of 30.8.4
normalized by 30.8.10–30.8.11 and `a^m_{n,k}` extended to `-N ≤ k < -R` by forward recursion
(hypothesis: the forward solution does not vanish at `-R`, else `𝖰s` does not exist). -/
@[dlmf 30.8.E9, dlmf 30.8.E10, dlmf 30.8.E11]
theorem spheroidalQs_eq_ferrers_series {n m : ℕ} (hmn : m ≤ n) (γ2 : ℝ)
    (hf : spheroidalFwd n m γ2 ((n + m) / 2 - (n - m) / 2 + 1) ≠ 0) {x : ℝ}
    (hx : x ∈ Ioo (-1 : ℝ) 1) :
    ∃ S₁ S₂ : ℝ,
      HasSum (fun j : ℕ =>
          let k : ℤ := -(((n + m) / 2 : ℕ) : ℤ) - 1 - j
          (-1 : ℝ) ^ k * spheroidalCoeffPrime n m γ2 k * (ferrersP ((n : ℂ) + 2 * k) m x).re)
        S₁ ∧
      HasSum (fun j : ℕ =>
          let k : ℤ := -(((n + m) / 2 : ℕ) : ℤ) + j
          (-1 : ℝ) ^ k * spheroidalCoeff n m γ2 k * (ferrersQ ((n : ℂ) + 2 * k) m x).re)
        S₂ ∧
      spheroidalQs n m x γ2 = S₁ + S₂ := by
  sorry

/-- **The extended coefficients** (DLMF §30.8(ii)): for `-N ≤ k < -R` they are obtained by
forward recursion from `a^m_{n,-N-1} = 0`, matched to `a^m_{n,-R}`. Proved (definition). -/
@[dlmf 30.8.ii]
theorem spheroidalCoeff_of_lt {n m : ℕ} (γ2 : ℝ) {k : ℤ} (hk : k < -(((n - m) / 2 : ℕ) : ℤ))
    (hk' : -(((n + m) / 2 : ℕ) : ℤ) ≤ k) :
    spheroidalCoeff n m γ2 k = spheroidalCoeff n m γ2 (-(((n - m) / 2 : ℕ) : ℤ)) *
      spheroidalFwd n m γ2 (k + ((n + m) / 2 : ℕ) + 1).toNat /
        spheroidalFwd n m γ2 ((n + m) / 2 - (n - m) / 2 + 1) := by
  have h1 : ¬ (-(((n - m) / 2 : ℕ) : ℤ) ≤ k) := not_le.mpr hk
  have h2 : spheroidalCoeff n m γ2 (-(((n - m) / 2 : ℕ) : ℤ)) =
      spheroidalCoeffMain n m γ2 (-(((n - m) / 2 : ℕ) : ℤ)) := by
    unfold spheroidalCoeff
    simp only [le_refl, ↓reduceIte]
  rw [h2]
  unfold spheroidalCoeff
  simp only [h1, hk', ↓reduceIte]

/-- **The recurrence** (DLMF 30.8.4, §30.8(ii)): the coefficients `a^m_{n,k}(γ²)` satisfy
`A_k a_{k-1} + (B_k - λ^m_n(γ²)) a_k + C_k a_{k+1} = 0` for all `k ∈ ℤ` (with `a_k = 0` for
`k < -N` and the extension of §30.8(ii) for `-N ≤ k < -R`), when the forward solution does not
vanish at `k = -R`. Proved from `spheroidalCoeff_recurrence_of_le` and the forward recursion. -/
@[dlmf 30.8.E4]
theorem spheroidalCoeff_recurrence {n m : ℕ} (hmn : m ≤ n) (γ2 : ℝ)
    (hf : spheroidalFwd n m γ2 ((n + m) / 2 - (n - m) / 2 + 1) ≠ 0) (k : ℤ) :
    spheroidalRecA n m γ2 k * spheroidalCoeff n m γ2 (k - 1) +
        (spheroidalRecB n m γ2 k - spheroidalEigenvalue n m γ2) * spheroidalCoeff n m γ2 k +
      spheroidalRecC n m γ2 k * spheroidalCoeff n m γ2 (k + 1) = 0 := by
  set R := (n - m) / 2 with hR
  set N := (n + m) / 2 with hN
  have hRN : R ≤ N := Nat.div_le_div_right (by omega)
  have hNR : N - R = m := by omega
  -- values below `-N` vanish
  have hlow : ∀ j : ℤ, j < -(N : ℤ) → spheroidalCoeff n m γ2 j = 0 := by
    intro j hj
    unfold spheroidalCoeff
    split_ifs <;> first | omega | rfl
  -- the extended coefficients are proportional to the forward solution
  have hext : ∀ j : ℤ, -(N : ℤ) - 1 ≤ j → j ≤ -(R : ℤ) → spheroidalCoeff n m γ2 j =
      spheroidalCoeff n m γ2 (-(R : ℤ)) / spheroidalFwd n m γ2 (N - R + 1) *
        spheroidalFwd n m γ2 (j + N + 1).toNat := by
    intro j hj1 hj2
    rcases lt_or_eq_of_le hj2 with hj2 | rfl
    · rcases lt_or_eq_of_le hj1 with hj1 | rfl
      · rw [spheroidalCoeff_of_lt γ2 hj2 (by omega)]
        ring
      · rw [hlow _ (by omega), show (-(N : ℤ) - 1 + N + 1).toNat = 0 by omega]
        simp [spheroidalFwd]
    · rw [show (-(R : ℤ) + N + 1).toNat = N - R + 1 by omega]
      field_simp
  -- `C_k` vanishes at `k = -N - 1`
  have hC : spheroidalRecC n m γ2 (-(N : ℤ) - 1) = 0 := by
    unfold spheroidalRecC
    have hpar := Nat.div_add_mod (n + m) 2
    have hnum : ((n : ℝ) + m + 2 * ((-(N : ℤ) - 1 : ℤ) : ℝ) + 1) *
        ((n : ℝ) + m + 2 * ((-(N : ℤ) - 1 : ℤ) : ℝ) + 2) = 0 := by
      have hc : (n : ℝ) + m = 2 * N + ((n + m) % 2 : ℕ) := by
        exact_mod_cast (by omega : n + m = 2 * N + (n + m) % 2)
      push_cast
      rw [hc]
      rcases Nat.mod_two_eq_zero_or_one (n + m) with h | h <;> rw [h] <;> push_cast <;> ring
    rw [hnum]; ring
  rcases lt_trichotomy k (-(R : ℤ)) with hk | hk | hk
  · -- `k < -R`
    rcases lt_or_ge k (-(N : ℤ) - 1) with hk1 | hk1
    · rw [hlow _ (by omega), hlow _ (by omega), hlow _ (by omega)]; ring
    rcases eq_or_lt_of_le hk1 with hk1 | hk1
    · subst hk1
      rw [hlow _ (by omega), hlow _ (by omega), hC]; ring
    -- `-N ≤ k ≤ -R - 1`: the forward recursion
    have hγ : γ2 ≠ 0 := by
      intro h0
      apply hf
      rw [show N - R + 1 = (m - 1) + 2 by omega]
      simp only [spheroidalFwd, spheroidalRecC, h0]
      simp
    obtain ⟨j, hj⟩ : ∃ j : ℕ, k = -(N : ℤ) + j := ⟨(k + N).toNat, by omega⟩
    have hCk : spheroidalRecC n m γ2 k ≠ 0 := by
      unfold spheroidalRecC
      have h1 : ((n : ℝ) + m + 2 * k + 1) ≠ 0 := by
        have : (0 : ℤ) < n + m + 2 * k + 1 := by omega
        exact_mod_cast this.ne'
      have h2 : ((n : ℝ) + m + 2 * k + 2) ≠ 0 := by
        have : (0 : ℤ) < n + m + 2 * k + 2 := by omega
        exact_mod_cast this.ne'
      have h3 : (2 * (n : ℝ) + 4 * k + 3) ≠ 0 := by
        have : (2 * (n : ℤ) + 4 * k + 3) ≠ 0 := by omega
        exact_mod_cast this
      have h4 : (2 * (n : ℝ) + 4 * k + 5) ≠ 0 := by
        have : (2 * (n : ℤ) + 4 * k + 5) ≠ 0 := by omega
        exact_mod_cast this
      exact div_ne_zero (mul_ne_zero (neg_ne_zero.mpr hγ) (mul_ne_zero h1 h2)) (mul_ne_zero h3 h4)
    rw [hext (k - 1) (by omega) (by omega), hext k (by omega) (by omega),
      hext (k + 1) (by omega) (by omega)]
    rw [show (k - 1 + N + 1).toNat = j by omega, show (k + N + 1).toNat = j + 1 by omega,
      show (k + 1 + N + 1).toNat = j + 2 by omega]
    have hrec : spheroidalFwd n m γ2 (j + 2) = -(spheroidalRecA n m γ2 k * spheroidalFwd n m γ2 j +
        (spheroidalRecB n m γ2 k - spheroidalEigenvalue n m γ2) * spheroidalFwd n m γ2 (j + 1)) /
          spheroidalRecC n m γ2 k := by
      rw [hj]; rfl
    rw [hrec]
    field_simp
    ring
  · -- `k = -R`
    subst hk
    have h := spheroidalCoeff_recurrence_of_le hmn γ2 (k := -(R : ℤ)) le_rfl
    split_ifs at h with hh
    · omega
    · rw [spheroidalRecA_neg_R hmn γ2]
      linear_combination h
  · -- `k > -R`
    have h := spheroidalCoeff_recurrence_of_le hmn γ2 (k := k) hk.le
    split_ifs at h with hh
    · exact h
    · omega

end DLMF.Spheroidal
