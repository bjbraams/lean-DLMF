/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Spheroidal.FerrersDefs
public import DLMF.Legendre.Associated
public import DLMF.Legendre.IntegralTools
public import DLMF.Spheroidal.P2yFerrersTools
public import DLMF.Spheroidal.Angular

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

open Complex Set Filter Asymptotics DLMF.Legendre
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

/-- **The Ferrers expansion** (DLMF 30.8.1):
`𝖯s^m_n(x, γ²) = ∑_{k ≥ -R} (-1)^k a^m_{n,k}(γ²) 𝖯^m_{n+2k}(x)` on `(-1, 1)`. -/
@[dlmf 30.8.E1]
theorem hasSum_spheroidalPs_ferrers {n m : ℕ} (hmn : m ≤ n) (γ2 : ℝ) {x : ℝ}
    (hx : x ∈ Ioo (-1 : ℝ) 1) :
    HasSum (fun j : ℕ =>
        let k : ℤ := (j : ℤ) - ((n - m) / 2 : ℕ)
        (-1 : ℝ) ^ k * spheroidalCoeff n m γ2 k * (ferrersP ((n : ℂ) + 2 * k) m x).re)
      (spheroidalPs n m x γ2) := by
  sorry

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
theorem p2y_selfAdjoint {g : ℂ → ℂ} (hg : Differentiable ℂ g) (m N : ℕ) (lam γ2 : ℂ)
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
theorem p2y_integral_ferrers {g : ℂ → ℂ} (hreal : ∀ x : ℝ, (g x).im = 0) (m N : ℕ) :
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
theorem p2y_ferrers_one_sub_sq (ν : ℝ) (m : ℕ) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
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
theorem p2y_ferrers_prod {g : ℂ → ℂ} (m N : ℕ) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
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
theorem p2y_ferrers_intInt {g : ℂ → ℂ} (hg : Continuous g) (m : ℕ) {μ : ℂ} (N : ℕ)
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
theorem p2y_ferrersP_neg_sub_one (N : ℕ) (μ : ℂ) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    ferrersP (-(N : ℂ) - 1) μ x = ferrersP N μ x := by
  have hs : 1 + (x : ℂ) ∈ slitPlane := Or.inl (by simp; linarith [hx.1])
  unfold ferrersP
  rw [show -(N : ℂ) - 1 + 1 = -N by ring, show -(-(N : ℂ) - 1) = N + 1 by ring,
    DLMF.Hypergeometric.regularizedGaussHG_symm _ _ _ (mem_cutPlane_of_one_add hs)]

/-- The core identity behind 30.8.4: self-adjointness and the recurrence of `(1-x²)𝖯^m_ν`. -/
theorem p2y_core {n m : ℕ} (hmn : m ≤ n) (γ2 : ℝ) (N : ℕ) :
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
theorem p2y_factorial_two (a : ℕ) :
    (((a + 2).factorial : ℕ) : ℝ) = ((a : ℝ) + 2) * ((a : ℝ) + 1) * (a.factorial : ℝ) := by
  rw [show a + 2 = (a + 1) + 1 from rfl, Nat.factorial_succ, Nat.factorial_succ]; push_cast; ring

/-- The lowest admissible degree: `(N+m)(N+m-1) 𝖯^m_{N-2} = 0` on `(-1, 1)` when
`m ≤ N < m + 2`. -/
theorem p2y_low_vanish {m N : ℕ} (hmN : m ≤ N) (h : N < m + 2) {x : ℝ}
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
theorem p2y_alg_low (n k m γ2 lam s Fa Fb T0 Tp Tm : ℝ) (hbf : Fb ≠ 0)
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
theorem p2y_alg_high (n k m γ2 lam s Fa Fb T0 Tp Tm : ℝ) (hbf : Fb ≠ 0)
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


/-- **The normalization** (DLMF 30.8.5):
`∑_{k ≥ -R} a^m_{n,k}(γ²) a^{-m}_{n,k}(γ²)/(2n+4k+1) = 1/(2n+1)` (equivalent to 30.4.1). -/
@[dlmf 30.8.E5]
theorem hasSum_spheroidalCoeff_normalization {n m : ℕ} (hmn : m ≤ n) (γ2 : ℝ) :
    HasSum (fun j : ℕ =>
        let k : ℤ := (j : ℤ) - ((n - m) / 2 : ℕ)
        spheroidalCoeff n m γ2 k * spheroidalCoeffNeg n m γ2 k / (2 * (n : ℝ) + 4 * k + 1))
      (1 / (2 * (n : ℝ) + 1)) := by
  sorry

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

/-- **Ratio asymptotics** (DLMF 30.8.7): `k² a^m_{n,k}(γ²)/a^m_{n,k-1}(γ²) = γ²/16 + O(1/k)` as
`k → ∞`. -/
@[dlmf 30.8.E7]
theorem spheroidalCoeff_ratio_isBigO {n m : ℕ} (hmn : m ≤ n) (γ2 : ℝ) :
    (fun k : ℕ => (k : ℝ) ^ 2 * spheroidalCoeff n m γ2 k / spheroidalCoeff n m γ2 ((k : ℤ) - 1) -
        γ2 / 16) =O[atTop] (fun k : ℕ => (k : ℝ)⁻¹) := by
  sorry

/-- **Ratio asymptotics** (DLMF 30.8.8):
`(λ^m_n(γ²) - B_k)/A_k · a^m_{n,k}(γ²)/a^m_{n,k-1}(γ²) = 1 + O(k⁻⁴)` as `k → ∞`.
Corrected: the hypothesis `γ2 ≠ 0` was added (2026-10-26), since at `γ² = 0` the statement fails
(`p2y_not_spheroidalCoeff_ratio_isBigO_four_zero`). -/
@[dlmf 30.8.E8]
theorem spheroidalCoeff_ratio_isBigO_four {n m : ℕ} (hmn : m ≤ n) {γ2 : ℝ} (hγ : γ2 ≠ 0) :
    (fun k : ℕ => (spheroidalEigenvalue n m γ2 - spheroidalRecB n m γ2 k) /
        spheroidalRecA n m γ2 k *
          (spheroidalCoeff n m γ2 k / spheroidalCoeff n m γ2 ((k : ℤ) - 1)) - 1)
      =O[atTop] (fun k : ℕ => ((k : ℝ) ^ 4)⁻¹) := by
  sorry

/-- **30.8.8 fails at `γ² = 0`** as stated: then `A_k = 0`, the Lean quotient
`(λ - B_k)/A_k` is `0`, and the expression is the constant `-1`, which is not `O(k⁻⁴)`. -/
theorem p2y_not_spheroidalCoeff_ratio_isBigO_four_zero (n m : ℕ) :
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
