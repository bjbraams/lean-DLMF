/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.JacobiElliptic.Basic.Epsilon
public import DLMF.JacobiElliptic.Integrals
public import DLMF.Elementary.Trigonometric
public import DLMF.Elliptic.JacobiIdentities
public import DLMF.JacobiElliptic.SpecialValues.ModulusLimits
public import DLMF.JacobiElliptic.FourierSeries
public import DLMF.JacobiElliptic.AmplitudeExpansions
public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.RealDeriv

/-!
# Related functions: amplitude, Jacobi's Epsilon and Zeta functions (DLMF §22.16)

The Jacobi amplitude `am(x, k)`, Jacobi's Epsilon function `ℰ(x, k)` and Jacobi's Zeta function
`Z(x|k)` for real `x` and real modulus (DLMF §22.16).

## Main results

* `Real.jacobiAmOfParameter_eq_arcsin_jacobiSnOfParameter`, `Real.contDiff_jacobiAmOfParameter`,
  `Real.jacobiAmOfParameter_eq_integral_jacobiDnOfParameter`: DLMF 22.16.1, smoothness, and DLMF
  22.16.3.
* `Real.tendsto_jacobiAmOfParameter_one`: `am(x, 1) = gd x` (DLMF 22.16.5) as the limit `k → 1⁻`.
* `Real.jacobiAmOfParameter_isBigO_maclaurin`, `Real.jacobiAmOfParameter_isBigO_small_modulus`,
  `Real.jacobiAmOfParameter_isBigO_small_comodulus`, `Real.jacobiAmOfParameter_hasSum_fourier`: the
  expansions DLMF 22.16.6–22.16.9.
* `Real.eq_incompleteEllipticFOfParameter_iff_jacobiAmOfParameter_eq`,
  `Real.jacobiAmOfParameter_eq_iff_jacobiSnOfParameter_eq_sin`,
  `Real.jacobiAmOfParameter_eq_iff_jacobiCnOfParameter_eq_cos`: the relations DLMF
  22.16.10–22.16.13.
* `Real.jacobiEpsilon_eq_integral_sn`, `Real.jacobiEpsilon_eq_integral_jacobiSnOfParameter_sq`,
  `Real.jacobiEpsilon_eq_integral_jacobiCnOfParameter_sq`: DLMF 22.16.14–22.16.16.
* `Real.jacobiEpsilon_eq_integral_cd_sq`, …, `Real.jacobiEpsilon_eq_integral_cs_sq`:
  DLMF 22.16.18–22.16.26.
* `Real.jacobiEpsilon_add`, `Real.jacobiEpsilon_add_completeEllipticKOfParameter`,
  `Real.jacobiEpsilon_add_two_completeEllipticKOfParameter`: DLMF 22.16.27–22.16.29.
* `Real.jacobiEpsilon_eq_theta`: DLMF 22.16.30.
* `Real.incompleteEllipticEOfParameter_jacobiAmOfParameter`: `E(am(x,k), k) = ℰ(x, k)` for all real
  `x` (DLMF 22.16.31, stronger than DLMF's `-K ≤ x ≤ K`).
* `Real.jacobiZeta_add`, `Real.jacobiZeta_add_completeEllipticKOfParameter`,
  `Real.jacobiZeta_add_two_completeEllipticKOfParameter`: the quasi-addition formula and
  DLMF 22.16.33–22.16.34.

## Implementation notes

The project's `DLMF.Elliptic.Real.jacobiAmOfParameter x m`, the inverse of `φ ↦ F(φ|m)` for real
parameter `m = k² < 1`, is DLMF's `am(x, k)`; it is the continuous branch of `Arcsin(sn x)`.
The quasi-periodicity 22.16.2 and `am(x, 0) = x` (22.16.4) are the existing
`Real.jacobiAmOfParameter_add_two_completeEllipticKOfParameter` and
`Real.jacobiAmOfParameter_zero_param`. At `k = 1` the existing definition is a totalized junk value
(`am x = x` for `m ≥ 1`), so 22.16.5 is stated as a limit.

The integral 22.16.17, valid for all real `x`, is taken as the definition of `ℰ`. DLMF and
Miller write `Z(x|k)` / `JacobiZeta`; the longer name `Real.jacobiZeta` avoids a clash
with `DLMF.JacobiElliptic.jacobiThetaArgument`, the theta argument `ζ = πz/(2K)` of §22.2.

All functions are real, with `0 < k < 1` (or `m < 1`) as in DLMF §22.16, `K = K(k²)`,
`E = E(k²)` in the parameter convention of `DLMF.Elliptic.Complete`, and `k'² = 1 - k²`.
-/

@[expose] public section

open Real DLMF.Elliptic Filter Asymptotics
open scoped Topology

noncomputable section

namespace DLMF.JacobiElliptic

/-! ### Jacobi's amplitude -/

section Amplitude

variable {m : ℝ}

/-- `-π/2 ≤ am x ≤ π/2` for `-K ≤ x ≤ K` (helper). -/
private lemma jacobiAmOfParameter_mem_Icc (hm : m < 1) {x : ℝ}
    (hx0 : -Real.completeEllipticKOfParameter m ≤ x)
    (hx1 : x ≤ Real.completeEllipticKOfParameter m) :
    Real.jacobiAmOfParameter x m ∈ Set.Icc (-(π / 2)) (π / 2) := by
  have h0 := (strictMono_jacobiAmOfParameter' hm).monotone hx0
  have h1 := (strictMono_jacobiAmOfParameter' hm).monotone hx1
  simp only [Real.jacobiAmOfParameter_neg hm,
      Real.jacobiAmOfParameter_completeEllipticKOfParameter hm] at h0 h1
  exact ⟨h0, h1⟩

/-- DLMF 22.16.1: `am(x,k) = Arcsin(sn(x,k))`, with the principal inverse sine for
`-K ≤ x ≤ K` (elsewhere `am` is the continuous continuation, `Real.continuous_jacobiAmOfParameter`).
-/
@[dlmf 22.16.E1 "special case: real parameter m = k² < 1; principal branch on -K ≤ x ≤ K"]
theorem Real.jacobiAmOfParameter_eq_arcsin_jacobiSnOfParameter (hm : m < 1) {x : ℝ}
    (hx0 : -Real.completeEllipticKOfParameter m ≤ x)
        (hx1 : x ≤ Real.completeEllipticKOfParameter m) :
    Real.jacobiAmOfParameter x m = Real.arcsin (Real.jacobiSnOfParameter x m) := by
  obtain ⟨h0, h1⟩ := jacobiAmOfParameter_mem_Icc hm hx0 hx1
  rw [Real.jacobiSnOfParameter, Real.arcsin_sin h0 h1]

/-- DLMF §22.16(i), prose after 22.16.1: `am(x,k)` is an infinitely differentiable function
of `x` (`m < 1`). -/
@[dlmf 22.16.i "special case: real parameter m = k² < 1"]
theorem Real.contDiff_jacobiAmOfParameter (hm : m < 1) :
    ContDiff ℝ (⊤ : ℕ∞) fun x => Real.jacobiAmOfParameter x m := by
  have hderiv : deriv (fun x => Real.jacobiAmOfParameter x m) =
      fun x => √(1 - m * Real.sin (Real.jacobiAmOfParameter x m) ^ 2) := by
    funext x
    rw [(Real.hasDerivAt_jacobiAmOfParameter hm x).deriv, Real.sqrt_eq_rpow]
  have hn : ∀ n : ℕ, ContDiff ℝ n fun x => Real.jacobiAmOfParameter x m := by
    intro n
    induction n with
    | zero => exact contDiff_zero.mpr (Real.continuous_jacobiAmOfParameter hm)
    | succ n ih =>
      rw [show ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 by push_cast; rfl,
        contDiff_succ_iff_deriv]
      refine ⟨fun x => (Real.hasDerivAt_jacobiAmOfParameter hm x).differentiableAt, by simp, ?_⟩
      rw [hderiv]
      refine ContDiff.sqrt ?_ fun x => (one_sub_mul_sin_sq_pos hm _).ne'
      exact contDiff_const.sub (contDiff_const.mul ((Real.contDiff_sin.comp ih).pow 2))
  exact contDiff_infty.mpr hn

/-- DLMF 22.16.3: `am(x, k) = ∫₀ˣ dn(t, k) dt`. -/
@[dlmf 22.16.E3 "special case: real parameter m = k² < 1"]
theorem Real.jacobiAmOfParameter_eq_integral_jacobiDnOfParameter (hm : m < 1) (x : ℝ) :
    Real.jacobiAmOfParameter x m = ∫ t in (0 : ℝ)..x, Real.jacobiDnOfParameter t m := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun t => Real.jacobiAmOfParameter t m)
    (f' := fun t => Real.jacobiDnOfParameter t m)
        (fun t _ => Real.hasDerivAt_jacobiAmOfParameter hm t)
    ((Real.continuous_jacobiDnOfParameter hm).intervalIntegrable 0 x)
  rw [h, Real.jacobiAmOfParameter_zero hm, sub_zero]

/-- DLMF 22.16.5: `am(x, 1) = gd(x)`, as the limit `k → 1⁻` (the existing real amplitude is
defined only for `m < 1`). -/
@[dlmf 22.16.E5 "different convention: limit k → 1⁻, since Real.jacobiAmOfParameter is totalized \
    at m = 1"]
theorem Real.tendsto_jacobiAmOfParameter_one (x : ℝ) :
    Tendsto (fun k : ℝ => Real.jacobiAmOfParameter x (k ^ 2)) (𝓝[<] 1)
      (𝓝 (DLMF.Elementary.gudermannian x)) := by
  have hcosh : Complex.cosh (x : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_cosh]
    exact_mod_cast (Real.cosh_pos x).ne'
  have hsn := (Complex.continuous_re.tendsto _).comp (tendsto_jacobiSn_one (x : ℂ) hcosh)
  rw [Complex.tanh_ofReal_re] at hsn
  have hsn' : Tendsto (fun k : ℝ => Real.jacobiSnOfParameter x (k ^ 2)) (𝓝[<] 1)
      (𝓝 (Real.tanh x)) := by
    apply hsn.congr'
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with k hk
    simp only [Function.comp_apply]
    rw [jacobiSn_ofReal hk.1 hk.2, Complex.ofReal_re]
  have hlim := Real.continuous_arcsin.continuousAt.tendsto.comp hsn'
  rw [← (DLMF.Elementary.gudermannian_elementary x).2.1] at hlim
  apply hlim.congr'
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num),
    (tendsto_norm_completeEllipticK_one.eventually_gt_atTop |x|)] with k hk hK
  have hm : k ^ 2 < 1 := by nlinarith [hk.1, hk.2]
  rw [completeEllipticK_ofReal hm, Complex.norm_real,
    Real.norm_of_nonneg (Real.completeEllipticKOfParameter_pos hm).le] at hK
  exact (Real.jacobiAmOfParameter_eq_arcsin_jacobiSnOfParameter hm
    (by linarith [neg_abs_le x]) (by linarith [le_abs_self x])).symm

/-- The derivatives of the real Jacobi amplitude through order six at the origin.
They follow successively from the real Jacobi differential equations and determine
the Maclaurin polynomial without restricting the parameter to a positive modulus. -/
private lemma jacobiAmOfParameter_derivatives_zero {m : ℝ} (hm : m < 1) :
    ∀ i : Fin 7, iteratedDeriv i (fun x => Real.jacobiAmOfParameter x m) 0 =
      (![0, 1, 0, -m, 0, m * (4 + m), 0] : Fin 7 → ℝ) i := by
  let A := fun x => Real.jacobiAmOfParameter x m
  let S := fun x => Real.jacobiSnOfParameter x m
  let C := fun x => Real.jacobiCnOfParameter x m
  let D := fun x => Real.jacobiDnOfParameter x m
  have hS : Differentiable ℝ S := fun x =>
      (Real.hasDerivAt_jacobiSnOfParameter hm x).differentiableAt
  have hC : Differentiable ℝ C := fun x =>
      (Real.hasDerivAt_jacobiCnOfParameter hm x).differentiableAt
  have hD : Differentiable ℝ D := fun x =>
      (Real.hasDerivAt_jacobiDnOfParameter hm x).differentiableAt
  have dA : deriv A = D := funext fun x => (Real.hasDerivAt_jacobiAmOfParameter hm x).deriv
  have dS (x) : deriv S x = C x * D x := (Real.hasDerivAt_jacobiSnOfParameter hm x).deriv
  have dC (x) : deriv C x = -(S x * D x) := (Real.hasDerivAt_jacobiCnOfParameter hm x).deriv
  have dD (x) : deriv D x = -(m * S x * C x) := (Real.hasDerivAt_jacobiDnOfParameter hm x).deriv
  have j1 : iteratedDeriv 1 A = D := by rw [iteratedDeriv_one, dA]
  have j2 : iteratedDeriv 2 A = fun x => -(m * S x * C x) := by
    rw [show 2=1 + 1 by norm_num, iteratedDeriv_succ, j1]; exact funext dD
  have j3 : iteratedDeriv 3 A = fun x => -m * D x * (C x - S x) * (C x + S x) := by
    rw [show 3=2 + 1 by norm_num, iteratedDeriv_succ, j2]
    funext x
    simp (disch := fun_prop) [dS, dC]
    ring
  have j4 : iteratedDeriv 4 A = fun x => m * C x * S x *
      (m * C x ^ 2 + 4 * D x ^ 2 - m * S x ^ 2) := by
    rw [show 4=3 + 1 by norm_num, iteratedDeriv_succ, j3]
    funext x
    simp (disch := fun_prop) [dS, dC, dD]
    ring
  have j5 : iteratedDeriv 5 A = fun x => m * D x * (m * C x ^ 4 + 4 * C x ^ 2 * D x ^ 2-
      14 * m * C x ^ 2 * S x ^ 2 - 4 * D x ^ 2 * S x ^ 2 + m * S x ^ 4) := by
    rw [show 5=4 + 1 by norm_num, iteratedDeriv_succ, j4]
    funext x
    simp (disch := fun_prop) [dS, dC, dD]
    ring
  have j6 : iteratedDeriv 6 A = fun x => -m * C x * S x *
      (m ^ 2 * C x ^ 4 + 44 * m * C x ^ 2 * D x ^ 2-
      14 * m ^ 2 * C x ^ 2 * S x ^ 2 + 16 * D x ^ 4 - 44 * m * D x ^ 2 * S x ^ 2 +
          m ^ 2 * S x ^ 4) := by
    rw [show 6=5 + 1 by norm_num, iteratedDeriv_succ, j5]
    funext x
    simp (disch := fun_prop) [dS, dC, dD]
    ring
  intro i
  change iteratedDeriv (i : ℕ) A 0 = _
  fin_cases i <;> simp [j1, j2, j3, j4, j5, j6, A, S, C, D, Real.jacobiAmOfParameter_zero hm,
    Real.jacobiSnOfParameter, Real.jacobiCnOfParameter, Real.jacobiDnOfParameter, add_comm]

/-- DLMF 22.16.6: `am(x,k) = x - k² x³/3! + k²(4 + k²) x⁵/5! + O(x⁷)` as `x → 0`, `m = k²`.
The remainder follows from Mathlib's `taylor_isLittleO_univ` and the Jacobi ODE coefficients. -/
@[dlmf 22.16.E6 "special case: real x, real parameter m = k² < 1"]
theorem Real.jacobiAmOfParameter_isBigO_maclaurin (hm : m < 1) :
    (fun x => Real.jacobiAmOfParameter x m -
        (x - m * x ^ 3 / 6 + m * (4 + m) * x ^ 5 / 120)) =O[𝓝 0]
      fun x => x ^ 7 := by
  let A := fun x => Real.jacobiAmOfParameter x m
  have h0 := jacobiAmOfParameter_derivatives_zero hm ⟨0, by decide⟩
  have h1 := jacobiAmOfParameter_derivatives_zero hm ⟨1, by decide⟩
  have h2 := jacobiAmOfParameter_derivatives_zero hm ⟨2, by decide⟩
  have h3 := jacobiAmOfParameter_derivatives_zero hm ⟨3, by decide⟩
  have h4 := jacobiAmOfParameter_derivatives_zero hm ⟨4, by decide⟩
  have h5 := jacobiAmOfParameter_derivatives_zero hm ⟨5, by decide⟩
  have h6 := jacobiAmOfParameter_derivatives_zero hm ⟨6, by decide⟩
  norm_num at h0 h1 h2 h3 h4 h5 h6
  have ht (x : ℝ) : taylorWithinEval A 7 Set.univ 0 x =
      x - m * x ^ 3 / 6 + m * (4 + m) * x ^ 5 / 120 + iteratedDeriv 7 A 0 / 5040 * x ^ 7 := by
    rw [taylor_within_apply]
    norm_num [Finset.sum_range_succ, iteratedDerivWithin_univ,
      h0, h1, h2, h3, h4, h5, h6, A]
    ring
  have hf : ContDiff ℝ (7 : ℕ) A := (Real.contDiff_jacobiAmOfParameter hm).of_le (by simp)
  have h := (taylor_isLittleO_univ (x₀:=0) hf).isBigO
  simp only [sub_zero] at h
  have hc := (isBigO_refl (fun x : ℝ => x ^ 7) (𝓝 0)).const_mul_left (iteratedDeriv 7 A 0 / 5040)
  convert h.add hc using 1
  funext x
  rw [ht]
  ring

/-- DLMF 22.16.7: `am(x,k) = x - k²(x - sin x cos x)/4 + O(k⁴)` as `k → 0`, for fixed real `x`. -/
@[dlmf 22.16.E7 "special case: real x, real k → 0"]
theorem Real.jacobiAmOfParameter_isBigO_small_modulus (x : ℝ) :
    (fun k : ℝ => Real.jacobiAmOfParameter x (k ^ 2) -
        (x - k ^ 2 / 4 * (x - Real.sin x * Real.cos x)))
      =O[𝓝 0] fun k => k ^ 4 := by
  refine IsBigO.of_bound (8 * |x|) ?_
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2)] with k hk
  rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hk
  have hk2 : k ^ 2 ≤ 1 / 4 := by nlinarith [abs_nonneg k, sq_abs k]
  have := Real.abs_jacobiAmOfParameter_sub_le_of_small_param (sq_nonneg k) hk2 x
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ k ^ 4)]
  calc _ ≤ 8 * |x| * (k ^ 2) ^ 2 := this
    _ = 8 * |x| * k ^ 4 := by ring


/-- DLMF 22.16.8: `am(x,k) = gd x - k'²(x - sinh x cosh x) sech x/4 + O(k'⁴)` as `k → 1⁻`, for
fixed real `x`, with `k'² = 1 - k²`. -/
@[dlmf 22.16.E8 "special case: real x, real k → 1⁻"]
theorem Real.jacobiAmOfParameter_isBigO_small_comodulus (x : ℝ) :
    (fun k : ℝ => Real.jacobiAmOfParameter x (k ^ 2) - (DLMF.Elementary.gudermannian x -
        (1 - k ^ 2) / 4 * (x - Real.sinh x * Real.cosh x) / Real.cosh x))
      =O[𝓝[<] 1] fun k => (1 - k ^ 2) ^ 2 := by
  obtain ⟨φ₀, hψ, -, K, hK⟩ := Real.exists_abs_jacobiAmOfParameter_sub_le_comodulus x
  refine IsBigO.of_bound K ?_
  have hev : ∀ᶠ k in 𝓝[<] (1 : ℝ), Real.jacobiAmOfParameter x (k ^ 2) ∈ Set.Ioo (-φ₀) φ₀ :=
    (Real.tendsto_jacobiAmOfParameter_one x).eventually
      (Ioo_mem_nhds (by linarith [neg_abs_le (DLMF.Elementary.gudermannian x)])
        (by linarith [le_abs_self (DLMF.Elementary.gudermannian x)]))
  filter_upwards [hev, Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with k hφk hk
  simp only [Real.norm_eq_abs, abs_pow, sq_abs]
  exact hK k hk.1 hk.2 (abs_le.mpr ⟨hφk.1.le, hφk.2.le⟩)

open Complex in
/-- The real form of DLMF 22.11.3. -/
private lemma real_jacobiDnOfParameter_hasSum_fourier {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) (t : ℝ) :
    HasSum (fun n : ℕ => 2 * π / Real.completeEllipticKOfParameter (k ^ 2) *
        Real.exp (-(π * Real.completeEllipticKOfParameter (1 - k ^ 2) /
            Real.completeEllipticKOfParameter (k ^ 2))) ^ (n + 1) *
        Real.cos (2 * (n + 1) * (π * t / (2 * Real.completeEllipticKOfParameter (k ^ 2)))) /
        (1 + Real.exp (-(π * Real.completeEllipticKOfParameter (1 - k ^ 2) /
            Real.completeEllipticKOfParameter (k ^ 2))) ^
          (2 * (n + 1))))
      (Real.jacobiDnOfParameter t (k ^ 2) - π /
          (2 * Real.completeEllipticKOfParameter (k ^ 2))) := by
  have hk := ofReal_mem_jacobiModulusDomain hk0 hk1
  have hm : k ^ 2 < 1 := by nlinarith
  have hm0 : 0 < k ^ 2 := by positivity
  have hK := completeEllipticK_ofReal hm
  have hK' := completeEllipticKPrime_ofReal hm0
  have hnome : jacobiNome (k : ℂ) =
      ((Real.exp (-(π * Real.completeEllipticKOfParameter (1 - k ^ 2) /
          Real.completeEllipticKOfParameter (k ^ 2))) : ℝ) : ℂ) := by
    rw [jacobiNome, hK, hK', Complex.ofReal_exp]; push_cast; ring_nf
  have hzeta : jacobiThetaArgument (t : ℂ) (k : ℂ) =
      ((π * t / (2 * Real.completeEllipticKOfParameter (k ^ 2)) : ℝ) : ℂ) := by
    rw [jacobiThetaArgument, hK]; push_cast; ring
  have hq1 : Real.exp (-(π * Real.completeEllipticKOfParameter (1 - k ^ 2) /
      Real.completeEllipticKOfParameter (k ^ 2))) < 1 := by
    rw [Real.exp_lt_one_iff, neg_lt_zero]
    have := Real.completeEllipticKOfParameter_pos hm
    have := Real.completeEllipticKOfParameter_pos (show 1 - k ^ 2 < 1 by linarith)
    positivity
  have h := jacobiDn_hasSum_fourier hk (z := (t : ℂ)) (by
    rw [hnome, hzeta, Complex.ofReal_im, abs_zero, mul_zero, Real.exp_zero, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact hq1)
  rw [hnome, hzeta, hK, jacobiDn_ofReal hk0 hk1] at h
  refine (Complex.hasSum_ofReal).mp ?_
  convert h using 1
  · funext n; push_cast; ring_nf
  · push_cast; ring

/-- DLMF 22.16.9: the Fourier series
`am(x,k) = πx/(2K) + 2 ∑_{n ≥ 1} qⁿ sin(2nζ)/(n(1 + q²ⁿ))`, `ζ = πx/(2K)`, with the real nome
`q = exp(-πK'/K)`, for real `x` and `0 < k < 1`. Proved by integrating the Fourier series
of `dn` (DLMF 22.11.3) term by term. -/
@[dlmf 22.16.E9 "special case: real x, 0 < k < 1"]
theorem Real.jacobiAmOfParameter_hasSum_fourier {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) (x : ℝ) :
    HasSum (fun n : ℕ =>
        2 * Real.exp (-(π * Real.completeEllipticKOfParameter (1 - k ^ 2) /
            Real.completeEllipticKOfParameter (k ^ 2))) ^ (n + 1) *
          Real.sin (2 * (n + 1) * (π * x / (2 * Real.completeEllipticKOfParameter (k ^ 2)))) /
          ((n + 1) * (1 + Real.exp (-(π * Real.completeEllipticKOfParameter (1 - k ^ 2) /
            Real.completeEllipticKOfParameter (k ^ 2))) ^ (2 * (n + 1)))))
      (Real.jacobiAmOfParameter x (k ^ 2) - π /
          (2 * Real.completeEllipticKOfParameter (k ^ 2)) * x) := by
  have hm : k ^ 2 < 1 := by nlinarith
  set K := Real.completeEllipticKOfParameter (k ^ 2) with hKdef
  set q := Real.exp (-(π * Real.completeEllipticKOfParameter (1 - k ^ 2) / K)) with hqdef
  have hK : 0 < K := Real.completeEllipticKOfParameter_pos hm
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : q < 1 := by
    rw [hqdef, Real.exp_lt_one_iff, neg_lt_zero]
    have := Real.completeEllipticKOfParameter_pos (show 1 - k ^ 2 < 1 by nlinarith)
    positivity
  set F : ℕ → ℝ → ℝ := fun n t => 2 * π / K * q ^ (n + 1) *
      Real.cos (2 * (n + 1) * (π * t / (2 * K))) / (1 + q ^ (2 * (n + 1))) with hF
  have hint := intervalIntegral.hasSum_integral_of_dominated_convergence (a := 0) (b := x)
    (μ := MeasureTheory.volume) (F := F)
        (f := fun t => Real.jacobiDnOfParameter t (k ^ 2) - π / (2 * K))
    (fun n _ => 2 * π / K * q ^ (n + 1))
    (fun n => (by fun_prop : Continuous (F n)).aestronglyMeasurable)
    (fun n => MeasureTheory.ae_of_all _ fun t _ => by
      simp only [hF, Real.norm_eq_abs]
      rw [abs_div, abs_mul, abs_of_pos (by positivity : 0 < 2 * π / K * q ^ (n + 1)),
        abs_of_pos (by positivity : 0 < 1 + q ^ (2 * (n + 1)))]
      have hc := Real.abs_cos_le_one (2 * (n + 1) * (π * t / (2 * K)))
      have h1 : 1 ≤ 1 + q ^ (2 * (n + 1)) := by have := pow_pos hq0 (2 * (n + 1)); linarith
      rw [div_le_iff₀ (by linarith)]
      have : 0 < 2 * π / K * q ^ (n + 1) := by positivity
      nlinarith)
    (MeasureTheory.ae_of_all _ fun t _ =>
      ((summable_geometric_of_lt_one hq0.le hq1).mul_left (2 * π / K * q)).congr fun n => by
        rw [pow_succ]; ring)
    intervalIntegrable_const
    (MeasureTheory.ae_of_all _ fun t _ => real_jacobiDnOfParameter_hasSum_fourier hk0 hk1 t)
  have hlhs : ∫ t in (0 : ℝ)..x, (Real.jacobiDnOfParameter t (k ^ 2) - π / (2 * K)) =
      Real.jacobiAmOfParameter x (k ^ 2) - π / (2 * K) * x := by
    rw [intervalIntegral.integral_sub
        ((Real.continuous_jacobiDnOfParameter hm).intervalIntegrable 0 x)
      intervalIntegrable_const, ← Real.jacobiAmOfParameter_eq_integral_jacobiDnOfParameter hm,
      intervalIntegral.integral_const]
    simp; ring
  rw [hlhs] at hint
  convert hint using 1
  funext n
  have hc : (2 * ((n : ℝ) + 1) * (π / (2 * K))) ≠ 0 := by positivity
  have hd : ∀ t, HasDerivAt (fun t => 2 * π / K * q ^ (n + 1) / (1 + q ^ (2 * (n + 1))) *
      (Real.sin (2 * (n + 1) * (π * t / (2 * K))) / (2 * ((n : ℝ) + 1) * (π / (2 * K)))))
      (F n t) t := by
    intro t
    have := ((((hasDerivAt_id t).const_mul (2 * ((n : ℝ) + 1) * (π / (2 * K)))).sin).div_const
      (2 * ((n : ℝ) + 1) * (π / (2 * K)))).const_mul
      (2 * π / K * q ^ (n + 1) / (1 + q ^ (2 * (n + 1))))
    convert this using 1
    · funext s; simp only [id]; ring_nf
    · simp only [hF, id]; field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
    ((by fun_prop : Continuous (F n)).intervalIntegrable 0 x)]
  simp only [mul_zero, zero_div, Real.sin_zero, sub_zero]
  field_simp

/-- DLMF 22.16.10 ⇔ 22.16.11: `x = F(φ, k)` if and only if `am(x, k) = φ`; this holds for all
real `x` and `φ` (stronger than DLMF, which assumes `-K ≤ x ≤ K`). -/
@[dlmf 22.16.E10 "stronger than DLMF: all real x and φ"]
theorem Real.eq_incompleteEllipticFOfParameter_iff_jacobiAmOfParameter_eq (hm : m < 1) (x φ : ℝ) :
    x = Real.incompleteEllipticFOfParameter φ m ↔ Real.jacobiAmOfParameter x m = φ := by
  constructor
  · rintro rfl; exact Real.jacobiAmOfParameter_incompleteEllipticFOfParameter hm φ
  · rintro rfl; exact (Real.incompleteEllipticFOfParameter_jacobiAmOfParameter hm x).symm

/-- DLMF 22.16.11 ⇔ 22.16.12: for `-K ≤ x ≤ K` and `-π/2 ≤ φ ≤ π/2`, `am(x,k) = φ` if and
only if `sn(x,k) = sin φ`; and `sn(x,k) = sin(am(x,k))` holds by definition. DLMF leaves the
range of `φ` implicit; it is needed for the converse direction. -/
@[dlmf 22.16.E12 "special case: -π/2 ≤ φ ≤ π/2 made explicit"]
theorem Real.jacobiAmOfParameter_eq_iff_jacobiSnOfParameter_eq_sin (hm : m < 1) {x φ : ℝ}
    (hx0 : -Real.completeEllipticKOfParameter m ≤ x) (hx1 : x ≤ Real.completeEllipticKOfParameter m)
        (hφ0 : -(π / 2) ≤ φ)
    (hφ1 : φ ≤ π / 2) :
    (Real.jacobiAmOfParameter x m = φ ↔ Real.jacobiSnOfParameter x m = Real.sin φ) ∧
      Real.jacobiSnOfParameter x m = Real.sin (Real.jacobiAmOfParameter x m) := by
  refine ⟨⟨fun h => by rw [Real.jacobiSnOfParameter, h], fun h => ?_⟩, rfl⟩
  exact Real.injOn_sin (jacobiAmOfParameter_mem_Icc hm hx0 hx1) ⟨hφ0, hφ1⟩ h

/-- DLMF 22.16.11 ⇔ 22.16.13: `am(x,k) = φ` implies `cn(x,k) = cos φ`, and `cn = cos ∘ am` by
definition; the converse needs a sign condition, here `0 ≤ x ≤ K`, `0 ≤ φ ≤ π/2` (for
`-K ≤ x < 0` the angles `±φ` have the same cosine). -/
@[dlmf 22.16.E13 "special case: converse for 0 ≤ x ≤ K, 0 ≤ φ ≤ π/2 (cos is even)"]
theorem Real.jacobiAmOfParameter_eq_iff_jacobiCnOfParameter_eq_cos (hm : m < 1)
    {x φ : ℝ} (hx0 : 0 ≤ x)
    (hx1 : x ≤ Real.completeEllipticKOfParameter m) (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ π / 2) :
    (Real.jacobiAmOfParameter x m = φ ↔ Real.jacobiCnOfParameter x m = Real.cos φ) ∧
      Real.jacobiCnOfParameter x m = Real.cos (Real.jacobiAmOfParameter x m) := by
  refine ⟨⟨fun h => by rw [Real.jacobiCnOfParameter, h], fun h => ?_⟩, rfl⟩
  have hK := Real.completeEllipticKOfParameter_pos hm
  obtain ⟨-, h1⟩ := jacobiAmOfParameter_mem_Icc hm (by linarith) hx1
  have h0 : 0 ≤ Real.jacobiAmOfParameter x m := by
    simpa [Real.jacobiAmOfParameter_zero hm] using (strictMono_jacobiAmOfParameter' hm).monotone hx0
  exact Real.injOn_cos ⟨h0, by linarith [Real.pi_pos]⟩ ⟨hφ0, by linarith [Real.pi_pos]⟩ h

end Amplitude

/-! ### Jacobi's Epsilon function -/

section Epsilon

variable {k : ℝ}

/-- `dn²` is interval integrable (helper). -/
private lemma intervalIntegrable_jacobiDnOfParameter_sq (hm : k ^ 2 < 1) (a b : ℝ) :
    IntervalIntegrable (fun t => Real.jacobiDnOfParameter t (k ^ 2) ^ 2) MeasureTheory.volume a b :=
  ((Real.continuous_jacobiDnOfParameter hm).pow 2).intervalIntegrable a b

/-- `sn²` is interval integrable (helper). -/
private lemma intervalIntegrable_jacobiSnOfParameter_sq (hm : k ^ 2 < 1) (a b : ℝ) :
    IntervalIntegrable (fun t => Real.jacobiSnOfParameter t (k ^ 2) ^ 2) MeasureTheory.volume a b :=
  ((Real.continuous_sin.comp (Real.continuous_jacobiAmOfParameter hm)).pow 2).intervalIntegrable a b

/-- DLMF 22.16.31: `E(am(x,k), k) = ℰ(x, k)`; proved for all real `x` (stronger than DLMF,
which states `-K ≤ x ≤ K`). -/
@[dlmf 22.16.E31 "stronger than DLMF: all real x; real modulus with k² < 1"]
theorem Real.incompleteEllipticEOfParameter_jacobiAmOfParameter (hm : k ^ 2 < 1) (x : ℝ) :
    Real.incompleteEllipticEOfParameter (Real.jacobiAmOfParameter x (k ^ 2)) (k ^ 2) =
        Real.jacobiEpsilon x k := by
  have hd : ∀ t, HasDerivAt
      (fun t => Real.incompleteEllipticEOfParameter (Real.jacobiAmOfParameter t (k ^ 2)) (k ^ 2))
      (Real.jacobiDnOfParameter t (k ^ 2) ^ 2) t := fun t => by
    have := (Real.hasDerivAt_incompleteEllipticEOfParameter hm
        (Real.jacobiAmOfParameter t (k ^ 2))).comp t
      (Real.hasDerivAt_jacobiAmOfParameter hm t)
    refine this.congr_deriv ?_
    rw [Real.jacobiDnOfParameter, Real.jacobiSnOfParameter]; ring
  have h0 : Real.incompleteEllipticEOfParameter (Real.jacobiAmOfParameter 0 (k ^ 2))
      (k ^ 2) = 0 := by
    simp [Real.jacobiAmOfParameter_zero hm, Real.incompleteEllipticEOfParameter]
  rw [Real.jacobiEpsilon, intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
    (intervalIntegrable_jacobiDnOfParameter_sq hm 0 x), h0, sub_zero]

open MeasureTheory Set in
/-- Substitution `t = f θ` for a continuous strictly increasing `f` on `[a, b]`. -/
theorem integral_comp_strictMonoOn_eq {f f' g h : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn f (Icc a b)) (ha : StrictMonoOn f (Icc a b))
    (hd : ∀ θ ∈ Ioo a b, HasDerivAt f (f' θ) θ)
    (hg : ∀ θ ∈ Ioo a b, |f' θ| * g (f θ) = h θ) :
    ∫ t in f a..f b, g t = ∫ θ in a..b, h θ := by
  have hfab : f a ≤ f b := ha.monotoneOn ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab
  have hcv := integral_image_eq_integral_abs_deriv_smul (f := f) (f' := f')
    (measurableSet_Ioo (a := a) (b := b)) (fun θ hθ => (hd θ hθ).hasDerivWithinAt)
    (ha.injOn.mono Ioo_subset_Icc_self) g
  rw [hc.image_Ioo_of_strictMonoOn hab ha] at hcv
  rw [intervalIntegral.integral_of_le hfab, integral_Ioc_eq_integral_Ioo, hcv,
    intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo]
  exact setIntegral_congr_fun measurableSet_Ioo fun θ hθ =>
      by simp only [smul_eq_mul]; exact hg θ hθ

/-- DLMF 22.16.14: `ℰ(x, k) = ∫₀^{sn(x,k)} √((1 - k²t²)/(1 - t²)) dt` for `-K < x < K`
(the corrected form, DLMF erratum of 2010-07
  -08 reported by C. Karney); substitution `t = sin θ` in `E(am x, k)`. -/
@[dlmf 22.16.E14 "special case: real modulus 0 < k < 1"]
theorem Real.jacobiEpsilon_eq_integral_sn (hk0 : 0 < k) (hk1 : k < 1) {x : ℝ}
    (hx0 : -Real.completeEllipticKOfParameter (k ^ 2) < x)
        (hx1 : x < Real.completeEllipticKOfParameter (k ^ 2)) :
    Real.jacobiEpsilon x k =
      ∫ t in (0 : ℝ)..Real.jacobiSnOfParameter x (k ^ 2), √((1 - k ^ 2 * t ^ 2) / (1 - t ^ 2)) := by
  have hm : k ^ 2 < 1 := by nlinarith
  have a0 := strictMono_jacobiAmOfParameter' hm hx0
  have a1 := strictMono_jacobiAmOfParameter' hm hx1
  simp only [Real.jacobiAmOfParameter_neg hm,
      Real.jacobiAmOfParameter_completeEllipticKOfParameter hm] at a0 a1
  set A := Real.jacobiAmOfParameter x (k ^ 2) with hA
  have hpt : ∀ θ ∈ Set.Ioo (-(π / 2)) (π / 2),
      |cos θ| * √((1 - k ^ 2 * sin θ ^ 2) / (1 - sin θ ^ 2)) =
        (1 - k ^ 2 * sin θ ^ 2) ^ (1 / 2 : ℝ) := by
    intro θ hθ
    have hc := Real.cos_pos_of_mem_Ioo hθ
    rw [abs_of_pos hc, show 1 - sin θ ^ 2 = cos θ ^ 2 by rw [← Real.sin_sq_add_cos_sq θ]; ring,
      Real.sqrt_div' _ (sq_nonneg _), Real.sqrt_sq hc.le, ← Real.sqrt_eq_rpow]
    field_simp
  have key : ∀ a b : ℝ, -(π / 2) < a → a ≤ b → b < π / 2 →
      ∫ t in sin a..sin b, √((1 - k ^ 2 * t ^ 2) / (1 - t ^ 2)) =
        ∫ θ in a..b, (1 - k ^ 2 * sin θ ^ 2) ^ (1 / 2 : ℝ) := by
    intro a b ha hab hb
    exact integral_comp_strictMonoOn_eq hab continuous_sin.continuousOn
      (Real.strictMonoOn_sin.mono (Set.Icc_subset_Icc ha.le hb.le))
      (fun θ _ => Real.hasDerivAt_sin θ)
      (fun θ hθ => hpt θ ⟨by linarith [hθ.1], by linarith [hθ.2]⟩)
  rw [← Real.incompleteEllipticEOfParameter_jacobiAmOfParameter hm,
      Real.incompleteEllipticEOfParameter, Real.jacobiSnOfParameter, ← hA]
  rcases le_total 0 A with h | h
  · have := key 0 A (by linarith [Real.pi_pos]) h a1
    rw [Real.sin_zero] at this; exact this.symm
  · have := key A 0 a0 h (by linarith [Real.pi_pos])
    rw [Real.sin_zero] at this
    rw [intervalIntegral.integral_symm, ← this, intervalIntegral.integral_symm, neg_neg]

/-- DLMF 22.16.15: `ℰ(x, k) = -k² ∫₀ˣ sn²(t, k) dt + x`. -/
@[dlmf 22.16.E15 "special case: real modulus with k² < 1"]
theorem Real.jacobiEpsilon_eq_integral_jacobiSnOfParameter_sq (hm : k ^ 2 < 1) (x : ℝ) :
    Real.jacobiEpsilon x k = -k ^ 2 *
        (∫ t in (0 : ℝ)..x, Real.jacobiSnOfParameter t (k ^ 2) ^ 2) + x := by
  have h : ∀ t, Real.jacobiDnOfParameter t (k ^ 2) ^ 2 = 1 - k ^ 2 *
      Real.jacobiSnOfParameter t (k ^ 2) ^ 2 :=
    fun t => by linear_combination (Real.mul_jacobiSnOfParameter_sq_add_jacobiDnOfParameter_sq hm t)
  have hc : (∫ t in (0 : ℝ)..x, Real.jacobiDnOfParameter t (k ^ 2) ^ 2) =
      ∫ t in (0 : ℝ)..x, (1 - k ^ 2 * Real.jacobiSnOfParameter t (k ^ 2) ^ 2) :=
    intervalIntegral.integral_congr fun t _ => h t
  rw [Real.jacobiEpsilon, hc, intervalIntegral.integral_sub intervalIntegrable_const
      ((intervalIntegrable_jacobiSnOfParameter_sq hm 0 x).const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
  simp
  ring

/-- DLMF 22.16.16: `ℰ(x, k) = k² ∫₀ˣ cn²(t, k) dt + k'² x`. -/
@[dlmf 22.16.E16 "special case: real modulus with k² < 1"]
theorem Real.jacobiEpsilon_eq_integral_jacobiCnOfParameter_sq (hm : k ^ 2 < 1) (x : ℝ) :
    Real.jacobiEpsilon x k =
      k ^ 2 * (∫ t in (0 : ℝ)..x, Real.jacobiCnOfParameter t (k ^ 2) ^ 2) + (1 - k ^ 2) * x := by
  have h : ∀ t, Real.jacobiCnOfParameter t (k ^ 2) ^ 2 = 1 -
      Real.jacobiSnOfParameter t (k ^ 2) ^ 2 :=
    fun t => by linear_combination
                  (Real.jacobiSnOfParameter_sq_add_jacobiCnOfParameter_sq t (k ^ 2))
  have hc : (∫ t in (0 : ℝ)..x, Real.jacobiCnOfParameter t (k ^ 2) ^ 2) =
      ∫ t in (0 : ℝ)..x, (1 - Real.jacobiSnOfParameter t (k ^ 2) ^ 2) :=
    intervalIntegral.integral_congr fun t _ => h t
  rw [hc, intervalIntegral.integral_sub intervalIntegrable_const
      (intervalIntegrable_jacobiSnOfParameter_sq hm 0 x),
    Real.jacobiEpsilon_eq_integral_jacobiSnOfParameter_sq hm x, intervalIntegral.integral_const]
  simp
  ring

/-- DLMF 22.16.29: `ℰ(x + 2K, k) = ℰ(x, k) + 2E(k)`. -/
@[dlmf 22.16.E29 "special case: real modulus with k² < 1"]
theorem Real.jacobiEpsilon_add_two_completeEllipticKOfParameter (hm : k ^ 2 < 1) (x : ℝ) :
    Real.jacobiEpsilon (x + 2 * Real.completeEllipticKOfParameter (k ^ 2)) k =
      Real.jacobiEpsilon x k + 2 * Real.completeEllipticEOfParameter (k ^ 2) := by
  rw [← Real.incompleteEllipticEOfParameter_jacobiAmOfParameter hm,
      ← Real.incompleteEllipticEOfParameter_jacobiAmOfParameter hm,
    Real.jacobiAmOfParameter_add_two_completeEllipticKOfParameter hm,
        Real.incompleteEllipticEOfParameter_add_pi hm]

/-- At `x`, the function `(fun x => Real.jacobiEpsilon x k)` has derivative
`(Real.jacobiDnOfParameter x (k ^ 2) ^ 2)`. -/
private lemma hasDerivAt_jacobiEpsilon {k : ℝ} (hm : k ^ 2 < 1) (x : ℝ) :
    HasDerivAt (fun x => Real.jacobiEpsilon x k) (Real.jacobiDnOfParameter x (k ^ 2) ^ 2) x :=
  (((Real.continuous_jacobiDnOfParameter hm).pow 2).integral_hasStrictDerivAt 0 x).hasDerivAt

/-- Identity under the stated parameter and domain assumptions: `∫ t in (0 : ℝ)..x, f t = F x - F
0`. -/
private lemma integral_eq_sub_of_hasDerivAt_of_continuous {F f : ℝ → ℝ}
    (hF : ∀ t, HasDerivAt F (f t) t) (hf : Continuous f) (x : ℝ) :
    ∫ t in (0 : ℝ)..x, f t = F x - F 0 :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hF t) (hf.intervalIntegrable _ _)

/-- Estimate under the stated parameter and domain assumptions: `0 < Real.jacobiCnOfParameter t m`.
-/
private lemma jacobiCnOfParameter_pos_of_mem_Ioo {m : ℝ} (hm : m < 1) {t : ℝ}
    (h0 : -Real.completeEllipticKOfParameter m < t)
    (h1 : t < Real.completeEllipticKOfParameter m) : 0 < Real.jacobiCnOfParameter t m := by
  have a0 := strictMono_jacobiAmOfParameter' hm h0
  have a1 := strictMono_jacobiAmOfParameter' hm h1
  simp only [Real.jacobiAmOfParameter_neg hm,
      Real.jacobiAmOfParameter_completeEllipticKOfParameter hm] at a0 a1
  exact Real.cos_pos_of_mem_Ioo ⟨a0, a1⟩

/-- Identity under the stated parameter and domain assumptions: `∫ t in (0 : ℝ)..x, f t = F x - F
0`. -/
private lemma integral_eq_sub_of_hasDerivAt_of_continuousOn {F f : ℝ → ℝ} {x : ℝ}
    (hF : ∀ t ∈ Set.uIcc 0 x, HasDerivAt F (f t) t)
    (hf : ContinuousOn f (Set.uIcc 0 x)) :
    ∫ t in (0 : ℝ)..x, f t = F x - F 0 :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt hF hf.intervalIntegrable

/-- DLMF 22.16.18: `ℰ(x,k) = -k² ∫₀ˣ cd²(t,k) dt + x + k² sn(x,k) cd(x,k)`. -/
@[dlmf 22.16.E18 "special case: real modulus 0 < k < 1"]
theorem Real.jacobiEpsilon_eq_integral_cd_sq (hk0 : 0 < k) (hk1 : k < 1) (x : ℝ) :
    Real.jacobiEpsilon x k =
      -k ^ 2 * (∫ t in (0 : ℝ)..x,
          (Real.jacobiCnOfParameter t (k ^ 2) / Real.jacobiDnOfParameter t (k ^ 2)) ^ 2) +
        x + k ^ 2 * Real.jacobiSnOfParameter x (k ^ 2) *
          (Real.jacobiCnOfParameter x (k ^ 2) / Real.jacobiDnOfParameter x (k ^ 2)) := by
  have hm : k ^ 2 < 1 := by nlinarith
  have hdn := fun t => (Real.jacobiDnOfParameter_pos hm t).ne'
  have cdn := Real.continuous_jacobiDnOfParameter hm
  have csn := Real.continuous_jacobiSnOfParameter hm
  have ccn := Real.continuous_jacobiCnOfParameter hm
  have cg : Continuous fun t =>
      (Real.jacobiCnOfParameter t (k ^ 2) / Real.jacobiDnOfParameter t (k ^ 2)) ^ 2 := by
    first
    | exact (ccn.div cdn hdn).pow 2
    | exact (csn.div cdn hdn).pow 2
    | exact (continuous_const.div cdn hdn).pow 2
  have hF : ∀ t, HasDerivAt
      (fun t => 1 * t + k ^ 2 *
      (Real.jacobiSnOfParameter t (k ^ 2) *
          (Real.jacobiCnOfParameter t (k ^ 2) / Real.jacobiDnOfParameter t (k ^ 2))))
      (Real.jacobiDnOfParameter t (k ^ 2) ^ 2 - (-k ^ 2) *
          (Real.jacobiCnOfParameter t (k ^ 2) / Real.jacobiDnOfParameter t (k ^ 2)) ^ 2) t := by
    intro t
    refine (((hasDerivAt_id t).const_mul (1)).add
      (((Real.hasDerivAt_jacobiSnOfParameter hm t).mul
          ((Real.hasDerivAt_jacobiCnOfParameter hm t).div
        (Real.hasDerivAt_jacobiDnOfParameter hm t) (hdn t))).const_mul (k ^ 2))).congr_deriv ?_
    have h1 := Real.jacobiSnOfParameter_sq_add_jacobiCnOfParameter_sq t (k ^ 2)
    have h2 := Real.mul_jacobiSnOfParameter_sq_add_jacobiDnOfParameter_sq hm t
    have hd := hdn t
    simp only [Pi.div_apply]
    generalize Real.jacobiSnOfParameter t (k ^ 2) = s at *
    generalize Real.jacobiCnOfParameter t (k ^ 2) = c at *
    generalize Real.jacobiDnOfParameter t (k ^ 2) = d at *
    field_simp
    linear_combination (c^2*k^2-d^2) * h2
  have cd2 : Continuous fun t => Real.jacobiDnOfParameter t (k ^ 2) ^ 2 := cdn.pow 2
  have cg2 : Continuous fun t => (-k ^ 2) *
      (Real.jacobiCnOfParameter t (k ^ 2) / Real.jacobiDnOfParameter t (k ^ 2)) ^
          2 := cg.const_mul _
  have key := integral_eq_sub_of_hasDerivAt_of_continuous hF (cd2.sub cg2) x
  rw [intervalIntegral.integral_sub (cd2.intervalIntegrable _ _)
    (cg2.intervalIntegrable _ _), intervalIntegral.integral_const_mul,
    Real.jacobiSnOfParameter_zero hm] at key
  rw [Real.jacobiEpsilon]
  simp only [mul_zero, zero_mul, add_zero, sub_zero] at key
  linarith

/-- DLMF 22.16.19: `ℰ(x,k) = k²k'² ∫₀ˣ sd²(t,k) dt + k'² x + k² sn(x,k) cd(x,k)`. -/
@[dlmf 22.16.E19 "special case: real modulus 0 < k < 1"]
theorem Real.jacobiEpsilon_eq_integral_sd_sq (hk0 : 0 < k) (hk1 : k < 1) (x : ℝ) :
    Real.jacobiEpsilon x k =
      k ^ 2 * (1 - k ^ 2) *
          (∫ t in (0 : ℝ)..x, (Real.jacobiSnOfParameter t (k ^ 2) /
              Real.jacobiDnOfParameter t (k ^ 2)) ^ 2) +
        (1 - k ^ 2) * x + k ^ 2 * Real.jacobiSnOfParameter x (k ^ 2) *
          (Real.jacobiCnOfParameter x (k ^ 2) / Real.jacobiDnOfParameter x (k ^ 2)) := by
  have hm : k ^ 2 < 1 := by nlinarith
  have hdn := fun t => (Real.jacobiDnOfParameter_pos hm t).ne'
  have cdn := Real.continuous_jacobiDnOfParameter hm
  have csn := Real.continuous_jacobiSnOfParameter hm
  have ccn := Real.continuous_jacobiCnOfParameter hm
  have cg : Continuous fun t =>
      (Real.jacobiSnOfParameter t (k ^ 2) / Real.jacobiDnOfParameter t (k ^ 2)) ^ 2 := by
    first
    | exact (ccn.div cdn hdn).pow 2
    | exact (csn.div cdn hdn).pow 2
    | exact (continuous_const.div cdn hdn).pow 2
  have hF : ∀ t, HasDerivAt
      (fun t => (1 - k ^ 2) * t + k ^ 2 *
      (Real.jacobiSnOfParameter t (k ^ 2) *
          (Real.jacobiCnOfParameter t (k ^ 2) / Real.jacobiDnOfParameter t (k ^ 2))))
      (Real.jacobiDnOfParameter t (k ^ 2) ^ 2 - (k ^ 2 * (1 - k ^ 2)) *
          (Real.jacobiSnOfParameter t (k ^ 2) / Real.jacobiDnOfParameter t (k ^ 2)) ^ 2) t := by
    intro t
    refine (((hasDerivAt_id t).const_mul ((1 - k ^ 2))).add
      (((Real.hasDerivAt_jacobiSnOfParameter hm t).mul
          ((Real.hasDerivAt_jacobiCnOfParameter hm t).div
        (Real.hasDerivAt_jacobiDnOfParameter hm t) (hdn t))).const_mul (k ^ 2))).congr_deriv ?_
    have h1 := Real.jacobiSnOfParameter_sq_add_jacobiCnOfParameter_sq t (k ^ 2)
    have h2 := Real.mul_jacobiSnOfParameter_sq_add_jacobiDnOfParameter_sq hm t
    have hd := hdn t
    simp only [Pi.div_apply]
    generalize Real.jacobiSnOfParameter t (k ^ 2) = s at *
    generalize Real.jacobiCnOfParameter t (k ^ 2) = c at *
    generalize Real.jacobiDnOfParameter t (k ^ 2) = d at *
    field_simp
    linear_combination (k^2) * h1 +
        (c^2*k^2-d^2-k^2) * h2
  have cd2 : Continuous fun t => Real.jacobiDnOfParameter t (k ^ 2) ^ 2 := cdn.pow 2
  have cg2 : Continuous fun t => (k ^ 2 * (1 - k ^ 2)) *
      (Real.jacobiSnOfParameter t (k ^ 2) / Real.jacobiDnOfParameter t (k ^ 2)) ^
          2 := cg.const_mul _
  have key := integral_eq_sub_of_hasDerivAt_of_continuous hF (cd2.sub cg2) x
  rw [intervalIntegral.integral_sub (cd2.intervalIntegrable _ _)
    (cg2.intervalIntegrable _ _), intervalIntegral.integral_const_mul,
    Real.jacobiSnOfParameter_zero hm] at key
  rw [Real.jacobiEpsilon]
  simp only [mul_zero, zero_mul, add_zero, sub_zero] at key
  linarith

/-- DLMF 22.16.20: `ℰ(x,k) = k'² ∫₀ˣ nd²(t,k) dt + k² sn(x,k) cd(x,k)`. -/
@[dlmf 22.16.E20 "special case: real modulus 0 < k < 1"]
theorem Real.jacobiEpsilon_eq_integral_nd_sq (hk0 : 0 < k) (hk1 : k < 1) (x : ℝ) :
    Real.jacobiEpsilon x k =
      (1 - k ^ 2) * (∫ t in (0 : ℝ)..x, (1 / Real.jacobiDnOfParameter t (k ^ 2)) ^ 2) +
        k ^ 2 * Real.jacobiSnOfParameter x (k ^ 2) *
            (Real.jacobiCnOfParameter x (k ^ 2) / Real.jacobiDnOfParameter x (k ^ 2)) :=
            by
  have hm : k ^ 2 < 1 := by nlinarith
  have hdn := fun t => (Real.jacobiDnOfParameter_pos hm t).ne'
  have cdn := Real.continuous_jacobiDnOfParameter hm
  have csn := Real.continuous_jacobiSnOfParameter hm
  have ccn := Real.continuous_jacobiCnOfParameter hm
  have cg : Continuous fun t => (1 / Real.jacobiDnOfParameter t (k ^ 2)) ^ 2 := by
    first
    | exact (ccn.div cdn hdn).pow 2
    | exact (csn.div cdn hdn).pow 2
    | exact (continuous_const.div cdn hdn).pow 2
  have hF : ∀ t, HasDerivAt
      (fun t => 0 * t + k ^ 2 *
      (Real.jacobiSnOfParameter t (k ^ 2) *
          (Real.jacobiCnOfParameter t (k ^ 2) / Real.jacobiDnOfParameter t (k ^ 2))))
      (Real.jacobiDnOfParameter t (k ^ 2) ^ 2 - ((1 - k ^ 2)) *
          (1 / Real.jacobiDnOfParameter t (k ^ 2)) ^ 2) t := by
    intro t
    refine (((hasDerivAt_id t).const_mul (0)).add
      (((Real.hasDerivAt_jacobiSnOfParameter hm t).mul
          ((Real.hasDerivAt_jacobiCnOfParameter hm t).div
        (Real.hasDerivAt_jacobiDnOfParameter hm t) (hdn t))).const_mul (k ^ 2))).congr_deriv ?_
    have h1 := Real.jacobiSnOfParameter_sq_add_jacobiCnOfParameter_sq t (k ^ 2)
    have h2 := Real.mul_jacobiSnOfParameter_sq_add_jacobiDnOfParameter_sq hm t
    have hd := hdn t
    simp only [Pi.div_apply]
    generalize Real.jacobiSnOfParameter t (k ^ 2) = s at *
    generalize Real.jacobiCnOfParameter t (k ^ 2) = c at *
    generalize Real.jacobiDnOfParameter t (k ^ 2) = d at *
    field_simp
    linear_combination (k^2) * h1 +
        (c^2*k^2-d^2-1) * h2
  have cd2 : Continuous fun t => Real.jacobiDnOfParameter t (k ^ 2) ^ 2 := cdn.pow 2
  have cg2 : Continuous fun t => ((1 - k ^ 2)) *
      (1 / Real.jacobiDnOfParameter t (k ^ 2)) ^ 2 := cg.const_mul _
  have key := integral_eq_sub_of_hasDerivAt_of_continuous hF (cd2.sub cg2) x
  rw [intervalIntegral.integral_sub (cd2.intervalIntegrable _ _)
    (cg2.intervalIntegrable _ _), intervalIntegral.integral_const_mul,
    Real.jacobiSnOfParameter_zero hm] at key
  rw [Real.jacobiEpsilon]
  simp only [mul_zero, zero_mul, add_zero, sub_zero] at key
  linarith

/-- DLMF 22.16.21: `ℰ(x,k) = -∫₀ˣ dc²(t,k) dt + x + sn(x,k) dc(x,k)` for `-K < x < K`. -/
@[dlmf 22.16.E21 "special case: real modulus 0 < k < 1"]
theorem Real.jacobiEpsilon_eq_integral_dc_sq (hk0 : 0 < k) (hk1 : k < 1) {x : ℝ}
    (hx0 : -Real.completeEllipticKOfParameter (k ^ 2) < x)
        (hx1 : x < Real.completeEllipticKOfParameter (k ^ 2)) :
    Real.jacobiEpsilon x k =
      -(∫ t in (0 : ℝ)..x,
          (Real.jacobiDnOfParameter t (k ^ 2) / Real.jacobiCnOfParameter t (k ^ 2)) ^ 2) + x +
        Real.jacobiSnOfParameter x (k ^ 2) *
            (Real.jacobiDnOfParameter x (k ^ 2) / Real.jacobiCnOfParameter x (k ^ 2)) := by
  have hm : k ^ 2 < 1 := by nlinarith
  have hdn := fun t => (Real.jacobiDnOfParameter_pos hm t).ne'
  have hcn : ∀ t ∈ Set.uIcc 0 x, Real.jacobiCnOfParameter t (k ^ 2) ≠ 0 := by
    intro t ht
    have hK := Real.completeEllipticKOfParameter_pos hm
    refine (jacobiCnOfParameter_pos_of_mem_Ioo hm ?_ ?_).ne'
    · cases le_total 0 x with
      | inl h => rw [Set.uIcc_of_le h] at ht; linarith [ht.1]
      | inr h => rw [Set.uIcc_of_ge h] at ht; linarith [ht.1]
    · cases le_total 0 x with
      | inl h => rw [Set.uIcc_of_le h] at ht; linarith [ht.2]
      | inr h => rw [Set.uIcc_of_ge h] at ht; linarith [ht.2]
  have cdn := Real.continuous_jacobiDnOfParameter hm
  have csn := Real.continuous_jacobiSnOfParameter hm
  have ccn := Real.continuous_jacobiCnOfParameter hm
  have cg : ContinuousOn
      (fun t => (Real.jacobiDnOfParameter t (k ^ 2) / Real.jacobiCnOfParameter t (k ^ 2)) ^ 2)
      (Set.uIcc 0 x) := by
    first
    | exact (cdn.continuousOn.div ccn.continuousOn hcn).pow 2
    | exact (csn.continuousOn.div ccn.continuousOn hcn).pow 2
    | exact (continuousOn_const.div ccn.continuousOn hcn).pow 2
  have hF : ∀ t ∈ Set.uIcc 0 x,
      HasDerivAt (fun t => 1 * t + Real.jacobiSnOfParameter t (k ^ 2) *
      (Real.jacobiDnOfParameter t (k ^ 2) / Real.jacobiCnOfParameter t (k ^ 2)))
      (Real.jacobiDnOfParameter t (k ^ 2) ^ 2 - (-1) *
          (Real.jacobiDnOfParameter t (k ^ 2) / Real.jacobiCnOfParameter t (k ^ 2)) ^ 2) t := by
    intro t ht
    refine (((hasDerivAt_id t).const_mul (1)).add
      ((Real.hasDerivAt_jacobiSnOfParameter hm t).mul
          ((Real.hasDerivAt_jacobiDnOfParameter hm t).div
        (Real.hasDerivAt_jacobiCnOfParameter hm t) (hcn t ht)))).congr_deriv ?_
    have h1 := Real.jacobiSnOfParameter_sq_add_jacobiCnOfParameter_sq t (k ^ 2)
    have h2 := Real.mul_jacobiSnOfParameter_sq_add_jacobiDnOfParameter_sq hm t
    have hd := hcn t ht
    simp only [Pi.div_apply]
    generalize Real.jacobiSnOfParameter t (k ^ 2) = s at *
    generalize Real.jacobiCnOfParameter t (k ^ 2) = c at *
    generalize Real.jacobiDnOfParameter t (k ^ 2) = d at *
    field_simp
    linear_combination (d^2) * h1 +
        (-c^2) * h2
  have cd2 : ContinuousOn (fun t => Real.jacobiDnOfParameter t (k ^ 2) ^ 2) (Set.uIcc 0 x) :=
      (cdn.pow 2).continuousOn
  have cg2 : ContinuousOn
      (fun t => (-1) * (Real.jacobiDnOfParameter t (k ^ 2) / Real.jacobiCnOfParameter t (k ^ 2)) ^
          2) (Set.uIcc 0 x) :=
      continuousOn_const.mul cg
  have key := integral_eq_sub_of_hasDerivAt_of_continuousOn hF (cd2.sub cg2)
  rw [intervalIntegral.integral_sub cd2.intervalIntegrable cg2.intervalIntegrable,
    intervalIntegral.integral_const_mul, Real.jacobiSnOfParameter_zero hm] at key
  rw [Real.jacobiEpsilon]
  simp only [mul_zero, zero_mul, add_zero, sub_zero] at key
  linarith

/-- DLMF 22.16.22: `ℰ(x,k) = -k'² ∫₀ˣ nc²(t,k) dt + k'² x + sn(x,k) dc(x,k)` for `-K < x < K`. -/
@[dlmf 22.16.E22 "special case: real modulus 0 < k < 1"]
theorem Real.jacobiEpsilon_eq_integral_nc_sq (hk0 : 0 < k) (hk1 : k < 1) {x : ℝ}
    (hx0 : -Real.completeEllipticKOfParameter (k ^ 2) < x)
        (hx1 : x < Real.completeEllipticKOfParameter (k ^ 2)) :
    Real.jacobiEpsilon x k =
      -(1 - k ^ 2) * (∫ t in (0 : ℝ)..x, (1 / Real.jacobiCnOfParameter t (k ^ 2)) ^ 2) +
          (1 - k ^ 2) * x +
        Real.jacobiSnOfParameter x (k ^ 2) *
            (Real.jacobiDnOfParameter x (k ^ 2) / Real.jacobiCnOfParameter x (k ^ 2)) := by
  have hm : k ^ 2 < 1 := by nlinarith
  have hdn := fun t => (Real.jacobiDnOfParameter_pos hm t).ne'
  have hcn : ∀ t ∈ Set.uIcc 0 x, Real.jacobiCnOfParameter t (k ^ 2) ≠ 0 := by
    intro t ht
    have hK := Real.completeEllipticKOfParameter_pos hm
    refine (jacobiCnOfParameter_pos_of_mem_Ioo hm ?_ ?_).ne'
    · cases le_total 0 x with
      | inl h => rw [Set.uIcc_of_le h] at ht; linarith [ht.1]
      | inr h => rw [Set.uIcc_of_ge h] at ht; linarith [ht.1]
    · cases le_total 0 x with
      | inl h => rw [Set.uIcc_of_le h] at ht; linarith [ht.2]
      | inr h => rw [Set.uIcc_of_ge h] at ht; linarith [ht.2]
  have cdn := Real.continuous_jacobiDnOfParameter hm
  have csn := Real.continuous_jacobiSnOfParameter hm
  have ccn := Real.continuous_jacobiCnOfParameter hm
  have cg : ContinuousOn (fun t => (1 / Real.jacobiCnOfParameter t (k ^ 2)) ^ 2)
      (Set.uIcc 0 x) := by
    first
    | exact (cdn.continuousOn.div ccn.continuousOn hcn).pow 2
    | exact (csn.continuousOn.div ccn.continuousOn hcn).pow 2
    | exact (continuousOn_const.div ccn.continuousOn hcn).pow 2
  have hF : ∀ t ∈ Set.uIcc 0 x,
      HasDerivAt (fun t => (1 - k ^ 2) * t + Real.jacobiSnOfParameter t (k ^ 2) *
      (Real.jacobiDnOfParameter t (k ^ 2) / Real.jacobiCnOfParameter t (k ^ 2)))
      (Real.jacobiDnOfParameter t (k ^ 2) ^ 2 - (-(1 - k ^ 2)) *
          (1 / Real.jacobiCnOfParameter t (k ^ 2)) ^ 2) t := by
    intro t ht
    refine (((hasDerivAt_id t).const_mul ((1 - k ^ 2))).add
      ((Real.hasDerivAt_jacobiSnOfParameter hm t).mul
          ((Real.hasDerivAt_jacobiDnOfParameter hm t).div
        (Real.hasDerivAt_jacobiCnOfParameter hm t) (hcn t ht)))).congr_deriv ?_
    have h1 := Real.jacobiSnOfParameter_sq_add_jacobiCnOfParameter_sq t (k ^ 2)
    have h2 := Real.mul_jacobiSnOfParameter_sq_add_jacobiDnOfParameter_sq hm t
    have hd := hcn t ht
    simp only [Pi.div_apply]
    generalize Real.jacobiSnOfParameter t (k ^ 2) = s at *
    generalize Real.jacobiCnOfParameter t (k ^ 2) = c at *
    generalize Real.jacobiDnOfParameter t (k ^ 2) = d at *
    field_simp
    linear_combination (d^2-k^2) * h1 +
        (-c^2+1) * h2
  have cd2 : ContinuousOn (fun t => Real.jacobiDnOfParameter t (k ^ 2) ^ 2) (Set.uIcc 0 x) :=
      (cdn.pow 2).continuousOn
  have cg2 : ContinuousOn (fun t => (-(1 - k ^ 2)) * (1 / Real.jacobiCnOfParameter t (k ^ 2)) ^ 2)
      (Set.uIcc 0 x) := continuousOn_const.mul cg
  have key := integral_eq_sub_of_hasDerivAt_of_continuousOn hF (cd2.sub cg2)
  rw [intervalIntegral.integral_sub cd2.intervalIntegrable cg2.intervalIntegrable,
    intervalIntegral.integral_const_mul, Real.jacobiSnOfParameter_zero hm] at key
  rw [Real.jacobiEpsilon]
  simp only [mul_zero, zero_mul, add_zero, sub_zero] at key
  linarith

/-- DLMF 22.16.23: `ℰ(x,k) = -k'² ∫₀ˣ sc²(t,k) dt + sn(x,k) dc(x,k)` for `-K < x < K`. -/
@[dlmf 22.16.E23 "special case: real modulus 0 < k < 1"]
theorem Real.jacobiEpsilon_eq_integral_sc_sq (hk0 : 0 < k) (hk1 : k < 1) {x : ℝ}
    (hx0 : -Real.completeEllipticKOfParameter (k ^ 2) < x)
        (hx1 : x < Real.completeEllipticKOfParameter (k ^ 2)) :
    Real.jacobiEpsilon x k =
      -(1 - k ^ 2) * (∫ t in (0 : ℝ)..x,
          (Real.jacobiSnOfParameter t (k ^ 2) / Real.jacobiCnOfParameter t (k ^ 2)) ^ 2) +
        Real.jacobiSnOfParameter x (k ^ 2) *
            (Real.jacobiDnOfParameter x (k ^ 2) / Real.jacobiCnOfParameter x (k ^ 2)) := by
  have hm : k ^ 2 < 1 := by nlinarith
  have hdn := fun t => (Real.jacobiDnOfParameter_pos hm t).ne'
  have hcn : ∀ t ∈ Set.uIcc 0 x, Real.jacobiCnOfParameter t (k ^ 2) ≠ 0 := by
    intro t ht
    have hK := Real.completeEllipticKOfParameter_pos hm
    refine (jacobiCnOfParameter_pos_of_mem_Ioo hm ?_ ?_).ne'
    · cases le_total 0 x with
      | inl h => rw [Set.uIcc_of_le h] at ht; linarith [ht.1]
      | inr h => rw [Set.uIcc_of_ge h] at ht; linarith [ht.1]
    · cases le_total 0 x with
      | inl h => rw [Set.uIcc_of_le h] at ht; linarith [ht.2]
      | inr h => rw [Set.uIcc_of_ge h] at ht; linarith [ht.2]
  have cdn := Real.continuous_jacobiDnOfParameter hm
  have csn := Real.continuous_jacobiSnOfParameter hm
  have ccn := Real.continuous_jacobiCnOfParameter hm
  have cg : ContinuousOn
      (fun t => (Real.jacobiSnOfParameter t (k ^ 2) / Real.jacobiCnOfParameter t (k ^ 2)) ^ 2)
      (Set.uIcc 0 x) := by
    first
    | exact (cdn.continuousOn.div ccn.continuousOn hcn).pow 2
    | exact (csn.continuousOn.div ccn.continuousOn hcn).pow 2
    | exact (continuousOn_const.div ccn.continuousOn hcn).pow 2
  have hF : ∀ t ∈ Set.uIcc 0 x,
      HasDerivAt (fun t => 0 * t + Real.jacobiSnOfParameter t (k ^ 2) *
      (Real.jacobiDnOfParameter t (k ^ 2) / Real.jacobiCnOfParameter t (k ^ 2)))
      (Real.jacobiDnOfParameter t (k ^ 2) ^ 2 - (-(1 - k ^ 2)) *
          (Real.jacobiSnOfParameter t (k ^ 2) / Real.jacobiCnOfParameter t (k ^ 2)) ^ 2) t := by
    intro t ht
    refine (((hasDerivAt_id t).const_mul (0)).add
      ((Real.hasDerivAt_jacobiSnOfParameter hm t).mul
          ((Real.hasDerivAt_jacobiDnOfParameter hm t).div
        (Real.hasDerivAt_jacobiCnOfParameter hm t) (hcn t ht)))).congr_deriv ?_
    have h1 := Real.jacobiSnOfParameter_sq_add_jacobiCnOfParameter_sq t (k ^ 2)
    have h2 := Real.mul_jacobiSnOfParameter_sq_add_jacobiDnOfParameter_sq hm t
    have hd := hcn t ht
    simp only [Pi.div_apply]
    generalize Real.jacobiSnOfParameter t (k ^ 2) = s at *
    generalize Real.jacobiCnOfParameter t (k ^ 2) = c at *
    generalize Real.jacobiDnOfParameter t (k ^ 2) = d at *
    field_simp
    linear_combination (d^2-1) * h1 +
        (-c^2+1) * h2
  have cd2 : ContinuousOn (fun t => Real.jacobiDnOfParameter t (k ^ 2) ^ 2) (Set.uIcc 0 x) :=
      (cdn.pow 2).continuousOn
  have cg2 : ContinuousOn
      (fun t => (-(1 - k ^ 2)) *
          (Real.jacobiSnOfParameter t (k ^ 2) / Real.jacobiCnOfParameter t (k ^ 2)) ^ 2)
      (Set.uIcc 0 x) := continuousOn_const.mul cg
  have key := integral_eq_sub_of_hasDerivAt_of_continuousOn hF (cd2.sub cg2)
  rw [intervalIntegral.integral_sub cd2.intervalIntegrable cg2.intervalIntegrable,
    intervalIntegral.integral_const_mul, Real.jacobiSnOfParameter_zero hm] at key
  rw [Real.jacobiEpsilon]
  simp only [mul_zero, zero_mul, add_zero, sub_zero] at key
  linarith

open Complex Set MeasureTheory in
/-- Dividing `sn(z,k)` by `z` with Mathlib's `dslope` removes the origin zero.
The quotient is analytic at every real argument, equals one at zero, and has zero
derivative there because `sn` is odd. -/
private lemma jacobiSn_dslope_regular {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) :
    let g := dslope (fun z : ℂ => jacobiSn z k) 0
    g 0 = 1 ∧ deriv g 0 = 0 ∧ ∀ x : ℝ, AnalyticAt ℂ g (x : ℂ) := by
  dsimp only
  let s := fun z : ℂ => jacobiSn z k
  have hk := ofReal_mem_jacobiModulusDomain hk0 hk1
  have han (x : ℝ) : AnalyticAt ℂ s (x : ℂ) := by
    apply analyticAt_iff_eventually_differentiableAt.mpr
    filter_upwards [eventually_jacobiLetterTheta_ne_zero hk
        (jacobiLetterTheta_n_ne_zero_of_real hk0 hk1 x)] with z hz
    exact (hasDerivAt_jacobiSn hk hz).differentiableAt
  have hag (x : ℝ) : AnalyticAt ℂ (dslope s 0) (x : ℂ) := (han x).dslope 0
  have hg0 : dslope s 0 0 = 1 := by
    rw [dslope_same]
    simpa [s, jacobiCn_zero hk, jacobiDn_zero hk] using
      (hasDerivAt_jacobiSn hk
          (jacobiLetterTheta_jacobiThetaArgument_zero_ne_zero hk (q:=.n) (by decide))).deriv
  have heven : ∀ z : ℂ, dslope s 0 (-z) = dslope s 0 z := by
    intro z
    by_cases hz : z = 0
    · simp [hz]
    rw [dslope_of_ne _ (neg_ne_zero.mpr hz), dslope_of_ne _ hz]
    have hs0 : s 0 = 0 := jacobiSn_zero hk
    have hodd : s (-z) = -s z := by simp [s, jacobiSn, jacobiPQ_neg]
    simp only [slope, hs0, sub_zero, smul_eq_mul, hodd, vsub_eq_sub]
    ring
  have hd : HasDerivAt (dslope s 0) (deriv (dslope s 0) 0) (0 : ℂ) := by
    simpa using (hag 0).differentiableAt.hasDerivAt
  have hd' := (show HasDerivAt (dslope s 0) (deriv (dslope s 0) 0) (-(0 : ℂ)) by
    simpa using hd).comp (0 : ℂ) (hasDerivAt_neg (0 : ℂ))
  change HasDerivAt (fun z : ℂ => dslope s 0 (-z)) (deriv (dslope s 0) 0 * (-1)) 0 at hd'
  simp only [heven] at hd'
  have he : deriv (dslope s 0) 0 * (-1) = deriv (dslope s 0) 0 := hd'.unique hd
  refine ⟨hg0, ?_, hag⟩
  linear_combination -(1 / 2 : ℂ) * he

open Complex Set MeasureTheory in
/-- The real Jacobi sine has no zero strictly between `-2K` and `2K` except at zero. -/
private lemma jacobiSnOfParameter_ne_zero_between {m : ℝ} (hm : m < 1) (t : ℝ)
    (ht : t ∈ Ioo (-(2 * Real.completeEllipticKOfParameter m))
        (2 * Real.completeEllipticKOfParameter m)) (ht0 : t ≠ 0) :
    Real.jacobiSnOfParameter t m ≠ 0 := by
  rcases lt_or_gt_of_ne ht0 with hn | hp
  · have h := jacobiSnOfParameter_pos hm (by linarith : 0 < -t)
      (by linarith [ht.1] : -t < 2 * Real.completeEllipticKOfParameter m)
    rw [(jacobi_neg hm t).1] at h
    exact fun h0 => by rw [h0, neg_zero] at h; exact lt_irrefl _ h
  · exact (jacobiSnOfParameter_pos hm hp ht.2).ne'

open Complex Set MeasureTheory in
/-- The regularized expression `1/t+t-cn(t)dn(t)/sn(t)` extends to a smooth real
primitive vanishing at zero. Its derivative away from zero is
`ns(t)²-t⁻²+dn(t)²`; analyticity of the divided Jacobi sine supplies the extension. -/
private lemma jacobiNs_regularized_primitive {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) :
    ∃ F G : ℝ → ℝ, F 0 = 0 ∧ ∀ t ∈
        Ioo (-(2 * Real.completeEllipticKOfParameter (k ^ 2)))
            (2 * Real.completeEllipticKOfParameter (k ^ 2)),
      HasDerivAt F (G t) t ∧ ContinuousAt G t ∧
      (t ≠ 0 → F t = t⁻¹ + t - Real.jacobiCnOfParameter t (k ^ 2) *
          (Real.jacobiDnOfParameter t (k ^ 2) / Real.jacobiSnOfParameter t (k ^ 2)) ∧
        G t = (1 / Real.jacobiSnOfParameter t (k ^ 2)) ^ 2 - t⁻¹ ^ 2 +
            Real.jacobiDnOfParameter t (k ^ 2) ^ 2) := by
  let s := fun z : ℂ => jacobiSn z k
  let g := dslope s 0
  let H := fun z : ℂ => -(deriv g z / g z) + z
  let F := fun t : ℝ => (H t).re
  let G := fun t : ℝ => (deriv H t).re
  have hk := ofReal_mem_jacobiModulusDomain hk0 hk1
  have hm : k ^ 2 < 1 := by nlinarith
  obtain ⟨hg0, hdg0, hgan⟩ := jacobiSn_dslope_regular hk0 hk1
  change g 0 = 1 at hg0
  change deriv g 0 = 0 at hdg0
  change ∀ t : ℝ, AnalyticAt ℂ g (t : ℂ) at hgan
  have hs0 : s 0 = 0 := jacobiSn_zero hk
  have hsne := jacobiSnOfParameter_ne_zero_between hm
  have heg (t : ℝ) (ht0 : t ≠ 0) : g =ᶠ[𝓝 (t : ℂ)] fun z => s z / z := by
    have htC : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht0
    filter_upwards [dslope_eventuallyEq_slope_of_ne s htC] with z hz
    simpa only [slope, hs0, sub_zero, vsub_eq_sub, smul_eq_mul, div_eq_mul_inv, mul_comm] using hz
  have hgval (t : ℝ) (ht0 : t ≠ 0) : g (t : ℂ) = s t / t := (heg t ht0).self_of_nhds
  have hgN (t : ℝ) (ht : t ∈
      Ioo (-(2 * Real.completeEllipticKOfParameter (k ^ 2)))
          (2 * Real.completeEllipticKOfParameter (k ^ 2))) : g (t : ℂ) ≠ 0 := by
    by_cases ht0 : t = 0
    · simp [ht0, hg0]
    · rw [hgval t ht0]
      exact div_ne_zero (by dsimp only [s]; rw [jacobiSn_ofReal hk0 hk1];
                            exact ofReal_ne_zero.mpr (hsne t ht ht0))
        (ofReal_ne_zero.mpr ht0)
  have hH (t : ℝ) (ht : t ∈
      Ioo (-(2 * Real.completeEllipticKOfParameter (k ^ 2)))
          (2 * Real.completeEllipticKOfParameter (k ^ 2))) :
      AnalyticAt ℂ H (t : ℂ) := ((hgan t).deriv.div (hgan t) (hgN t ht)).neg.add analyticAt_id
  have hFeq (t : ℝ) (ht : t ∈
      Ioo (-(2 * Real.completeEllipticKOfParameter (k ^ 2)))
          (2 * Real.completeEllipticKOfParameter (k ^ 2)))
      (ht0 : t ≠ 0) : F t = t⁻¹ + t - Real.jacobiCnOfParameter t (k ^ 2) *
          (Real.jacobiDnOfParameter t (k ^ 2) / Real.jacobiSnOfParameter t (k ^ 2)) := by
    have htC : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht0
    have hsC : s (t : ℂ) ≠ 0 := by dsimp only [s]; rw [jacobiSn_ofReal hk0 hk1];
                                   exact ofReal_ne_zero.mpr (hsne t ht ht0)
    have hd := (hasDerivAt_jacobiSn hk (jacobiLetterTheta_n_ne_zero_of_real hk0 hk1 t)).div
        (hasDerivAt_id (t : ℂ)) htC
    simp only [id_eq, mul_one] at hd
    change HasDerivAt (fun z : ℂ => s z / z)
      ((jacobiCn t k * jacobiDn t k * (t : ℂ) - s t) / (t : ℂ) ^ 2) (t : ℂ) at hd
    have he : H (t : ℂ) = (t : ℂ)⁻¹ + (t : ℂ) - jacobiCn t k *
        (jacobiDn t k / jacobiSn t k) := by
      change -(deriv g (t : ℂ) / g (t : ℂ)) + (t : ℂ) = _
      rw [(heg t ht0).deriv_eq, hd.deriv, hgval t ht0]
      dsimp only [s]
      have hSn0 : jacobiSn t k ≠ 0 := hsC
      field_simp [htC, hSn0]
      ring
    change (H (t : ℂ)).re = _
    rw [he, jacobiSn_ofReal hk0 hk1, jacobiCn_ofReal hk0 hk1, jacobiDn_ofReal hk0 hk1,
      ←ofReal_inv, ←ofReal_div, ←ofReal_mul, ←ofReal_add, ←ofReal_sub, ofReal_re]
  refine ⟨F, G, by simp [F, H, hg0, hdg0], fun t ht => ⟨?_, ?_, ?_⟩⟩
  · exact (hH t ht).differentiableAt.hasDerivAt.real_of_complex
  · exact Complex.continuous_re.continuousAt.comp
      ((hH t ht).deriv.continuousAt.comp Complex.continuous_ofReal.continuousAt)
  · intro ht0
    refine ⟨hFeq t ht ht0, ?_⟩
    have hev : F =ᶠ[𝓝 t] fun w : ℝ => w⁻¹ + w - Real.jacobiCnOfParameter w (k ^ 2) *
        (Real.jacobiDnOfParameter w (k ^ 2) / Real.jacobiSnOfParameter w (k ^ 2)) := by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2, eventually_ne_nhds ht0] with w hw hw0
      exact hFeq w hw hw0
    have hd := ((hasDerivAt_inv ht0).add (hasDerivAt_id t)).sub
      ((Real.hasDerivAt_jacobiCnOfParameter hm t).mul
        ((Real.hasDerivAt_jacobiDnOfParameter hm t).div (Real.hasDerivAt_jacobiSnOfParameter hm t)
            (hsne t ht ht0)))
    have hd' := hd.congr_of_eventuallyEq hev
    have hF := (hH t ht).differentiableAt.hasDerivAt.real_of_complex
    change HasDerivAt F (G t) t at hF
    rw [hF.unique hd']
    have h1 := Real.jacobiSnOfParameter_sq_add_jacobiCnOfParameter_sq t (k ^ 2)
    have h2 := Real.mul_jacobiSnOfParameter_sq_add_jacobiDnOfParameter_sq hm t
    dsimp only [Pi.div_apply]
    field_simp [ht0, hsne t ht ht0]
    linear_combination t ^ 2 * h1 + t ^ 2 * Real.jacobiCnOfParameter t (k ^ 2) ^ 2 * h2

open Complex Set MeasureTheory in
/-- The regularized `ns²` integrand is integrable across the origin. Its primitive
gives the epsilon integral formula, with the point value at zero handled by almost
everywhere equality. -/
private lemma jacobiEpsilon_ns_integral_aux {k x : ℝ} (hk0 : 0 < k) (hk1 : k < 1) (hx : x ≠ 0)
    (hx0 : -(2 * Real.completeEllipticKOfParameter (k ^ 2)) < x)
        (hx1 : x < 2 * Real.completeEllipticKOfParameter (k ^ 2)) :
    IntervalIntegrable (fun t => (1 / Real.jacobiSnOfParameter t (k ^ 2)) ^ 2 -
        t⁻¹ ^ 2) volume 0 x ∧
    Real.jacobiEpsilon x k =
        -(∫ t in (0 : ℝ)..x, (1 / Real.jacobiSnOfParameter t (k ^ 2)) ^ 2 - t⁻¹ ^ 2) +
      x⁻¹ + x - Real.jacobiCnOfParameter x (k ^ 2) *
          (Real.jacobiDnOfParameter x (k ^ 2) / Real.jacobiSnOfParameter x (k ^ 2)) := by
  obtain ⟨F, G, hF0, hFG⟩ := jacobiNs_regularized_primitive hk0 hk1
  have hm : k ^ 2 < 1 := by nlinarith
  have hK := Real.completeEllipticKOfParameter_pos hm
  have hseg : uIcc 0 x ⊆ Ioo (-(2 * Real.completeEllipticKOfParameter (k ^ 2)))
      (2 * Real.completeEllipticKOfParameter (k ^ 2)) := by
    intro t ht
    rw [mem_uIcc] at ht
    rcases ht with ht | ht <;> exact ⟨by linarith [ht.1, ht.2], by linarith [ht.1, ht.2]⟩
  have hGc : ContinuousOn G (uIcc 0 x) := fun t ht => (hFG t (hseg ht)).2.1.continuousWithinAt
  have hGi : IntervalIntegrable G volume 0 x := hGc.intervalIntegrable
  have hdi : IntervalIntegrable (fun t => Real.jacobiDnOfParameter t (k ^ 2) ^ 2) volume 0 x :=
    ((Real.continuous_jacobiDnOfParameter hm).pow 2).intervalIntegrable _ _
  have he : (fun t => G t - Real.jacobiDnOfParameter t (k ^ 2) ^ 2) =ᵐ[volume.restrict (uIoc 0 x)]
      (fun t => (1 / Real.jacobiSnOfParameter t (k ^ 2)) ^ 2 - t⁻¹ ^ 2) := by
    filter_upwards [ae_restrict_mem measurableSet_uIoc,
        (volume.restrict (uIoc 0 x)).ae_ne 0] with t ht ht0
    rw [((hFG t (hseg (uIoc_subset_uIcc ht))).2.2 ht0).2]
    ring
  have hni := (hGi.sub hdi).congr_ae he
  refine ⟨hni, ?_⟩
  have hI := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => (hFG t (hseg ht)).1) hGi
  have hN : (∫ t in (0 : ℝ)..x, (1 / Real.jacobiSnOfParameter t (k ^ 2)) ^ 2 - t⁻¹ ^ 2) =
      F x - Real.jacobiEpsilon x k := by
    rw [←intervalIntegral.integral_congr_ae_restrict he, intervalIntegral.integral_sub hGi hdi,
        hI, hF0, sub_zero]
    rfl
  rw [((hFG x ⟨hx0, hx1⟩).2.2 hx).1] at hN
  linarith

open Complex Set MeasureTheory in
/-- A squared identity `v²+α sn²=1` changes the regularized `ns²` integral by `-αx`.
This applies to both `v=dn`, `α=k²` and `v=cn`, `α=1`. -/
private lemma jacobiNs_sq_integral_shift {k x : ℝ} (hk0 : 0 < k) (hk1 : k < 1) (hx : x ≠ 0)
    (hx0 : -(2 * Real.completeEllipticKOfParameter (k ^ 2)) < x)
        (hx1 : x < 2 * Real.completeEllipticKOfParameter (k ^ 2))
    (v : ℝ → ℝ) (α : ℝ) (hv : ∀ t, v t ^ 2 + α * Real.jacobiSnOfParameter t (k ^ 2) ^ 2 = 1) :
    (∫ t in (0 : ℝ)..x, (v t / Real.jacobiSnOfParameter t (k ^ 2)) ^ 2 - t⁻¹ ^ 2) =
      (∫ t in (0 : ℝ)..x, (1 / Real.jacobiSnOfParameter t (k ^ 2)) ^ 2 - t⁻¹ ^ 2) - α * x := by
  have hm : k ^ 2 < 1 := by nlinarith
  have hK := Real.completeEllipticKOfParameter_pos hm
  have hni := (jacobiEpsilon_ns_integral_aux hk0 hk1 hx hx0 hx1).1
  have he : (fun t => (v t / Real.jacobiSnOfParameter t (k ^ 2)) ^ 2 - t⁻¹ ^ 2)
      =ᵐ[volume.restrict (uIoc 0 x)]
      (fun t => ((1 / Real.jacobiSnOfParameter t (k ^ 2)) ^ 2 - t⁻¹ ^ 2) - α) := by
    filter_upwards [ae_restrict_mem measurableSet_uIoc,
        (volume.restrict (uIoc 0 x)).ae_ne 0] with t ht ht0
    have hts : t ∈ Ioo (-(2 * Real.completeEllipticKOfParameter (k ^ 2)))
        (2 * Real.completeEllipticKOfParameter (k ^ 2)) := by
      have htt := uIoc_subset_uIcc ht
      rw [mem_uIcc] at htt
      rcases htt with hh | hh <;> exact ⟨by linarith [hh.1, hh.2], by linarith [hh.1, hh.2]⟩
    have hrat : (v t / Real.jacobiSnOfParameter t (k ^ 2)) ^ 2 =
        (1 / Real.jacobiSnOfParameter t (k ^ 2)) ^ 2 - α := by
      field_simp [jacobiSnOfParameter_ne_zero_between hm t hts ht0]
      nlinarith [hv t]
    rw [hrat]
    ring
  rw [intervalIntegral.integral_congr_ae_restrict he,
    intervalIntegral.integral_sub hni intervalIntegrable_const, intervalIntegral.integral_const]
  simp only [sub_zero, smul_eq_mul]
  ring

/-- DLMF 22.16.24: `ℰ(x,k) = -∫₀ˣ (ns²(t,k) - t⁻²) dt + x⁻¹ + x - cn(x,k) ds(x,k)` for
`0 < |x| < 2K` (the integrand has a removable singularity at `t = 0`). -/
@[dlmf 22.16.E24 "special case: real modulus 0 < k < 1, x ≠ 0"]
theorem Real.jacobiEpsilon_eq_integral_ns_sq (hk0 : 0 < k) (hk1 : k < 1) {x : ℝ} (hx : x ≠ 0)
    (hx0 : -(2 * Real.completeEllipticKOfParameter (k ^ 2)) < x)
        (hx1 : x < 2 * Real.completeEllipticKOfParameter (k ^ 2)) :
    Real.jacobiEpsilon x k =
      -(∫ t in (0 : ℝ)..x, ((1 / Real.jacobiSnOfParameter t (k ^ 2)) ^ 2 - t⁻¹ ^ 2)) + x⁻¹ + x -
        Real.jacobiCnOfParameter x (k ^ 2) *
            (Real.jacobiDnOfParameter x (k ^ 2) / Real.jacobiSnOfParameter x (k ^ 2)) := by
  exact (jacobiEpsilon_ns_integral_aux hk0 hk1 hx hx0 hx1).2

/-- DLMF 22.16.25: `ℰ(x,k) = -∫₀ˣ (ds²(t,k) - t⁻²) dt + x⁻¹ + k'² x - cn(x,k) ds(x,k)` for
`0 < |x| < 2K`. -/
@[dlmf 22.16.E25 "special case: real modulus 0 < k < 1, x ≠ 0"]
theorem Real.jacobiEpsilon_eq_integral_ds_sq (hk0 : 0 < k) (hk1 : k < 1) {x : ℝ} (hx : x ≠ 0)
    (hx0 : -(2 * Real.completeEllipticKOfParameter (k ^ 2)) < x)
        (hx1 : x < 2 * Real.completeEllipticKOfParameter (k ^ 2)) :
    Real.jacobiEpsilon x k =
      -(∫ t in (0 : ℝ)..x,
          ((Real.jacobiDnOfParameter t (k ^ 2) / Real.jacobiSnOfParameter t (k ^ 2)) ^ 2 -
              t⁻¹ ^ 2)) + x⁻¹ +
        (1 - k ^ 2) * x -
        Real.jacobiCnOfParameter x (k ^ 2) *
            (Real.jacobiDnOfParameter x (k ^ 2) / Real.jacobiSnOfParameter x (k ^ 2)) := by
  have hm : k ^ 2 < 1 := by nlinarith
  rw [jacobiNs_sq_integral_shift hk0 hk1 hx hx0 hx1
      (fun t => Real.jacobiDnOfParameter t (k ^ 2)) (k ^ 2)
    (fun t => by linarith [Real.mul_jacobiSnOfParameter_sq_add_jacobiDnOfParameter_sq hm t])]
  rw [(jacobiEpsilon_ns_integral_aux hk0 hk1 hx hx0 hx1).2]
  ring

/-- DLMF 22.16.26: `ℰ(x,k) = -∫₀ˣ (cs²(t,k) - t⁻²) dt + x⁻¹ - cn(x,k) ds(x,k)` for
`0 < |x| < 2K`. -/
@[dlmf 22.16.E26 "special case: real modulus 0 < k < 1, x ≠ 0"]
theorem Real.jacobiEpsilon_eq_integral_cs_sq (hk0 : 0 < k) (hk1 : k < 1) {x : ℝ} (hx : x ≠ 0)
    (hx0 : -(2 * Real.completeEllipticKOfParameter (k ^ 2)) < x)
        (hx1 : x < 2 * Real.completeEllipticKOfParameter (k ^ 2)) :
    Real.jacobiEpsilon x k =
      -(∫ t in (0 : ℝ)..x,
          ((Real.jacobiCnOfParameter t (k ^ 2) / Real.jacobiSnOfParameter t (k ^ 2)) ^ 2 -
              t⁻¹ ^ 2)) + x⁻¹ -
        Real.jacobiCnOfParameter x (k ^ 2) *
            (Real.jacobiDnOfParameter x (k ^ 2) / Real.jacobiSnOfParameter x (k ^ 2)) := by
  rw [jacobiNs_sq_integral_shift hk0 hk1 hx hx0 hx1 (fun t => Real.jacobiCnOfParameter t (k ^ 2)) 1
    (fun t => by linarith [Real.jacobiSnOfParameter_sq_add_jacobiCnOfParameter_sq t (k ^ 2)])]
  rw [(jacobiEpsilon_ns_integral_aux hk0 hk1 hx hx0 hx1).2]
  ring

/-- DLMF 22.16.27: the quasi-addition formula
`ℰ(x₁ + x₂, k) = ℰ(x₁, k) + ℰ(x₂, k) - k² sn(x₁,k) sn(x₂,k) sn(x₁ + x₂,k)`. -/
@[dlmf 22.16.E27 "special case: real modulus with k² < 1"]
theorem Real.jacobiEpsilon_add (hm : k ^ 2 < 1) (x₁ x₂ : ℝ) :
    Real.jacobiEpsilon (x₁ + x₂) k = Real.jacobiEpsilon x₁ k + Real.jacobiEpsilon x₂ k -
      k ^ 2 * Real.jacobiSnOfParameter x₁ (k ^ 2) * Real.jacobiSnOfParameter x₂ (k ^ 2) *
        Real.jacobiSnOfParameter (x₁ + x₂) (k ^ 2) := by
  set m := k ^ 2 with hmdef
  set v := x₂
  let G : ℝ → ℝ := fun u => Real.jacobiEpsilon (u + v) k - Real.jacobiEpsilon u k -
    Real.jacobiEpsilon v k + m * Real.jacobiSnOfParameter u m * Real.jacobiSnOfParameter v m *
        Real.jacobiSnOfParameter (u + v) m
  have hG : ∀ u, HasDerivAt G 0 u := by
    intro u
    have e1 := (hasDerivAt_jacobiEpsilon hm (u + v)).comp u ((hasDerivAt_id u).add_const v)
    have e2 := hasDerivAt_jacobiEpsilon hm u
    have s1 := Real.hasDerivAt_jacobiSnOfParameter hm u
    have s2 := (Real.hasDerivAt_jacobiSnOfParameter hm (u + v)).comp u
        ((hasDerivAt_id u).add_const v)
    have hd := (((e1.sub e2).sub_const (Real.jacobiEpsilon v k)).add
      (((s1.const_mul m).mul_const (Real.jacobiSnOfParameter v m)).mul s2))
    refine HasDerivAt.congr_deriv (f := G) hd ?_
    simp only [id, Function.comp_def, mul_zero, zero_add, add_zero]
    rw [Real.jacobiSnOfParameter_add hm, Real.jacobiCnOfParameter_add hm,
        Real.jacobiDnOfParameter_add hm]
    have hD := (Real.one_sub_mul_jacobiSnOfParameter_sq_mul_sq_pos hm u v).ne'
    have h1 := Real.jacobiSnOfParameter_sq_add_jacobiCnOfParameter_sq u m
    have h2 := Real.mul_jacobiSnOfParameter_sq_add_jacobiDnOfParameter_sq hm u
    have h3 := Real.jacobiSnOfParameter_sq_add_jacobiCnOfParameter_sq v m
    have h4 := Real.mul_jacobiSnOfParameter_sq_add_jacobiDnOfParameter_sq hm v
    generalize Real.jacobiSnOfParameter u m = su at *
    generalize Real.jacobiCnOfParameter u m = cu at *
    generalize Real.jacobiDnOfParameter u m = du at *
    generalize Real.jacobiSnOfParameter v m = sv at *
    generalize Real.jacobiCnOfParameter v m = cv at *
    generalize Real.jacobiDnOfParameter v m = dv at *
    generalize hDdef : 1 - m * su ^ 2 * sv ^ 2 = D at hD ⊢
    field_simp
    linear_combination (-du^2*cv^2*m*D+du^2*m*D) * h1 +
        (su^2*du^2*m*D+cu^2*du^2*m*D-du^2*m*D) * h3 +
        (du^2*D) * h4 +
        (-su*cu*du*sv*cv*dv*m+du^2*dv^2+du^2*D) * hDdef
  have := is_const_of_deriv_eq_zero (fun u => (hG u).differentiableAt) (fun u => (hG u).deriv) x₁ 0
  simp only [G, zero_add, Real.jacobiEpsilon, intervalIntegral.integral_same,
    Real.jacobiSnOfParameter, Real.jacobiAmOfParameter_zero hm, Real.sin_zero] at this ⊢
  linarith

/-- DLMF 22.16.28: `ℰ(x + K, k) = ℰ(x, k) + E(k) - k² sn(x,k) cd(x,k)`. -/
@[dlmf 22.16.E28 "special case: real modulus with k² < 1"]
theorem Real.jacobiEpsilon_add_completeEllipticKOfParameter (hm : k ^ 2 < 1) (x : ℝ) :
    Real.jacobiEpsilon (x + Real.completeEllipticKOfParameter (k ^ 2)) k = Real.jacobiEpsilon x k +
      Real.completeEllipticEOfParameter (k ^ 2) -
        k ^ 2 * Real.jacobiSnOfParameter x (k ^ 2) *
            (Real.jacobiCnOfParameter x (k ^ 2) / Real.jacobiDnOfParameter x (k ^ 2)) :=
            by
  rw [Real.jacobiEpsilon_add hm, (Real.jacobi_completeEllipticKOfParameter hm).1,
      (Real.jacobi_add_completeEllipticKOfParameter hm x).1,
    ← Real.incompleteEllipticEOfParameter_jacobiAmOfParameter hm
        (Real.completeEllipticKOfParameter (k ^ 2)),
        Real.jacobiAmOfParameter_completeEllipticKOfParameter hm,
    Real.incompleteEllipticEOfParameter_pi_div_two]
  ring

/-- DLMF 22.16.30: `ℰ(x,k) = θ₄'(ξ,q)/(θ₃²(0,q) θ₄(ξ,q)) + (E(k)/K(k)) x` with
`ξ = x/θ₃²(0,q) = πx/(2K)` and `θ_j(·, q) = θ_j(·|τ)`, `τ = iK'/K`, for real `x` and
`0 < k < 1`. Admitted. -/
@[dlmf 22.16.E30 "special case: real x, 0 < k < 1"]
theorem Real.jacobiEpsilon_eq_theta (hk0 : 0 < k) (hk1 : k < 1) (x : ℝ) :
    (Real.jacobiEpsilon x k : ℂ) =
      deriv (fun ξ => jacobiThetaFourTau ξ (jacobiTau k))
          (x / jacobiThetaThreeTau 0 (jacobiTau k) ^ 2) /
        (jacobiThetaThreeTau 0 (jacobiTau k) ^ 2 *
          jacobiThetaFourTau (x / jacobiThetaThreeTau 0 (jacobiTau k) ^ 2) (jacobiTau k)) +
      (Real.completeEllipticEOfParameter (k ^ 2) /
          Real.completeEllipticKOfParameter (k ^ 2) * x : ℝ) := by
  sorry

end Epsilon

/-! ### Jacobi's Zeta function -/

section Zeta

variable {k : ℝ}

/-- DLMF §22.16(iii), prose: `Z(x|k)` satisfies the quasi-addition formula 22.16.27,
`Z(x₁ + x₂|k) = Z(x₁|k) + Z(x₂|k) - k² sn(x₁) sn(x₂) sn(x₁ + x₂)` (from 22.16.27). -/
@[dlmf 22.16.iii "special case: real modulus with k² < 1"]
theorem Real.jacobiZeta_add (hm : k ^ 2 < 1) (x₁ x₂ : ℝ) :
    Real.jacobiZeta (x₁ + x₂) k =
      Real.jacobiZeta x₁ k + Real.jacobiZeta x₂ k -
        k ^ 2 * Real.jacobiSnOfParameter x₁ (k ^ 2) * Real.jacobiSnOfParameter x₂ (k ^ 2) *
          Real.jacobiSnOfParameter (x₁ + x₂) (k ^ 2) := by
  simp only [Real.jacobiZeta, Real.jacobiEpsilon_add hm]
  ring

/-- DLMF 22.16.33: `Z(x + K|k) = Z(x|k) - k² sn(x,k) cd(x,k)` (from 22.16.28). -/
@[dlmf 22.16.E33 "special case: real modulus with k² < 1"]
theorem Real.jacobiZeta_add_completeEllipticKOfParameter (hm : k ^ 2 < 1) (x : ℝ) :
    Real.jacobiZeta (x + Real.completeEllipticKOfParameter (k ^ 2)) k = Real.jacobiZeta x k -
      k ^ 2 * Real.jacobiSnOfParameter x (k ^ 2) *
          (Real.jacobiCnOfParameter x (k ^ 2) / Real.jacobiDnOfParameter x (k ^ 2)) := by
  have hK := (Real.completeEllipticKOfParameter_pos hm).ne'
  simp only [Real.jacobiZeta, Real.jacobiEpsilon_add_completeEllipticKOfParameter hm]
  field_simp
  ring

/-- DLMF 22.16.34: `Z(x + 2K|k) = Z(x|k)`. -/
@[dlmf 22.16.E34 "special case: real modulus with k² < 1"]
theorem Real.jacobiZeta_add_two_completeEllipticKOfParameter (hm : k ^ 2 < 1) (x : ℝ) :
    Real.jacobiZeta (x + 2 * Real.completeEllipticKOfParameter (k ^ 2)) k =
      Real.jacobiZeta x k := by
  have hK := (Real.completeEllipticKOfParameter_pos hm).ne'
  simp only [Real.jacobiZeta, Real.jacobiEpsilon_add_two_completeEllipticKOfParameter hm]
  field_simp
  ring

end Zeta

end DLMF.JacobiElliptic
