/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Lame.Polynomials.Eigenvalues

/-!
# Zeros of the Lamé polynomials (DLMF §29.12(i))

The Lamé polynomial `E = lamePolynomialE t n m` (`m ≤ n`, `0 < k < 1`) has exactly `m` zeros in
`(0, K)` and exactly `n - m` zeros on the open segment from `K` to `K + iK'`; hence the
polynomial `P` of 29.12.10 has `n` simple zeros, `m` in `(0, 1)` and `n - m` in `(1, k⁻²)`.

## Main definitions

* `verticalPotential`: the potential `-ν(ν+1) k²/dn²(y, k')` along the vertical side.
* `lamePolyOddKiK`: the boundary type at `K + iK'`.

## Main results

* `ncard_zeros_lamePolynomialE_real`: exactly `m` zeros in `(0, K)`.
* `ncard_zeros_lamePolynomialE_vertical`: exactly `n - m` zeros on the vertical side.
* `lamePolynomialE_vertical_spectrum`: the vertical side as a Sturm–Liouville eigenproblem.
* `roots_of_lamePolynomialE_eq`: the zeros of any `P` in the polynomial form.
* `exists_poly_roots_lamePolynomialE`: DLMF 29.12.9–29.12.10, the zeros of `P`.

## Implementation notes

On `(0, K)` the count follows from Sturm's oscillation theorem
(`ODE.encard_zeros_eq_encard_separatedSpectrum_inter_Iio_of_isSturmLiouvilleSolution`) and the
identification of `½(H_m + ν(ν+1)k²)` as the `m`th eigenvalue
(`lameEigenvalue_lamePolynomialType_eq`). On the vertical side, `sn(K + iy, k) = 1/dn(y, k')` (from
the quarter-period shift and Jacobi's imaginary transformation), so `g(y) = E(K + iy)` solves
the Sturm–Liouville equation `g'' = (V(y) + h) g` with the bounded real potential
`V = -ν(ν+1)k²/dn²(y, k')` and separated boundary conditions at `0` and `K'` (from the
reflection symmetries about `K` and `K + iK'`). A complex solution of a real equation with such
boundary conditions is a multiple of a real eigenfunction. The zeros of `g` correspond
injectively to roots of `P` via `y ↦ 1/dn²(y, k')`, so there are at most `n`; the eigenvalue
parameters `-h_j` decrease strictly with `j`, so the zero counts are `n, n - 1, …, 0`.
-/

@[expose] public noncomputable section

open Polynomial Complex DLMF.JacobiElliptic DLMF.Elliptic Filter Set
open scoped Topology Real

namespace DLMF.Lame

open DLMF.EllipticIntegrals (completeEllipticK completeEllipticKPrime)

/-- The real part of a differentiable curve in `ℂ`. -/
private lemma hasDerivAt_re_comp {G : ℝ → ℂ} {G' : ℂ} {x : ℝ} (h : HasDerivAt G G' x) :
    HasDerivAt (fun x => (G x).re) G'.re x := by
  exact (Complex.reCLM.hasFDerivAt (x := G x)).comp_hasDerivAt x h

/-- The real part of a complex solution of `w'' = (V - μ) w` is a real solution. -/
private lemma isSturmLiouvilleSolution_re {V : ℝ → ℝ} {μ : ℝ} {g : ℝ → ℂ} (hd : Differentiable ℝ g)
    (hG : ∀ x, HasDerivAt (deriv g) (((V x - μ : ℝ) : ℂ) * g x) x) :
    ODE.IsSturmLiouvilleSolution V μ (fun x => (g x).re) ∧
      deriv (fun x => (g x).re) = fun x => (deriv g x).re := by
  have hd' : deriv (fun x => (g x).re) = fun x => (deriv g x).re :=
    funext fun x => (hasDerivAt_re_comp (hd x).hasDerivAt).deriv
  refine ⟨⟨fun x => (hasDerivAt_re_comp (hd x).hasDerivAt).differentiableAt, fun x => ?_⟩, hd'⟩
  rw [hd']
  have := hasDerivAt_re_comp (hG x)
  rwa [Complex.re_ofReal_mul] at this

/-- The real part of a constant multiple of a complex solution is a real solution. -/
private lemma isSturmLiouvilleSolution_re_const_mul {V : ℝ → ℝ} {μ : ℝ} {g : ℝ → ℂ}
    (hd : Differentiable ℝ g)
    (hG : ∀ x, HasDerivAt (deriv g) (((V x - μ : ℝ) : ℂ) * g x) x) (c : ℂ) :
    ODE.IsSturmLiouvilleSolution V μ (fun x => (c * g x).re) ∧
      deriv (fun x => (c * g x).re) = fun x => (c * deriv g x).re := by
  have hd1 : ∀ x, HasDerivAt (fun x => c * g x) (c * deriv g x) x := fun x =>
    (hd x).hasDerivAt.const_mul c
  have e : deriv (fun x => c * g x) = fun x => c * deriv g x := funext fun x => (hd1 x).deriv
  have h := isSturmLiouvilleSolution_re (V := V) (μ := μ) (g := fun x => c * g x)
    (fun x => (hd1 x).differentiableAt)
    (fun x => by rw [e]; exact ((hG x).const_mul c).congr_deriv (by ring))
  simpa only [e] using h

/-- **Zeros of a complex eigenfunction.** A nonzero complex solution `g` of `g'' = (V - μ) g`
(real potential) with separated boundary conditions is a constant multiple of a real
eigenfunction: `μ` is an eigenvalue and `g` has as many zeros in `(0, L)` as there are
eigenvalues below `μ`. -/
private lemma encard_zeros_of_complex_solution {V : ℝ → ℝ} {B L μ : ℝ} (hV : Continuous V)
    (hB : ∀ x, |V x| ≤ B)
    (hL : 0 < L) (odd0 oddK : Bool) {g : ℝ → ℂ} (hd : Differentiable ℝ g)
    (hG : ∀ x, HasDerivAt (deriv g) (((V x - μ : ℝ) : ℂ) * g x) x)
    (h0 : if odd0 then g 0 = 0 else deriv g 0 = 0)
    (hL' : if oddK then g L = 0 else deriv g L = 0) (hne : g ≠ 0) :
    μ ∈ ODE.separatedSpectrum V L odd0 oddK ∧
      {x | x ∈ Ioo 0 L ∧ g x = 0}.encard =
          (ODE.separatedSpectrum V L odd0 oddK ∩ Iio μ).encard := by
  have b0 : ∀ c : ℂ, if odd0 then (fun x => (c * g x).re) 0 = 0 else
      deriv (fun x => (c * g x).re) 0 = 0 := by
    intro c
    rw [(isSturmLiouvilleSolution_re_const_mul hd hG c).2]
    cases odd0 <;> simp_all
  have bL : ∀ c : ℂ, if oddK then (fun x => (c * g x).re) L = 0 else
      deriv (fun x => (c * g x).re) L = 0 := by
    intro c
    rw [(isSturmLiouvilleSolution_re_const_mul hd hG c).2]
    cases oddK <;> simp_all
  have hu := ODE.isSturmLiouvilleSolution_eq_mul_basicSolution hV
      (isSturmLiouvilleSolution_re_const_mul hd hG 1).1 (b0 1)
  have hv := ODE.isSturmLiouvilleSolution_eq_mul_basicSolution hV
      (isSturmLiouvilleSolution_re_const_mul hd hG (-I)).1 (b0 (-I))
  set Y := ODE.basicSolution V odd0 μ
  set a := if odd0 then deriv (fun x => (1 * g x).re) 0 else (fun x => (1 * g x).re) 0
  set b := if odd0 then deriv (fun x => (-I * g x).re) 0 else (fun x => (-I * g x).re) 0
  have hrep : ∀ x, g x = ((a : ℂ) + b * I) * Y x := by
    intro x
    have e1 := congrFun hu x
    have e2 := congrFun hv x
    apply Complex.ext <;> simp at e1 e2 ⊢ <;> linarith
  set c : ℂ := a + b * I
  have hc : c ≠ 0 := fun h => hne (funext fun x => by rw [hrep x, h, zero_mul]; rfl)
  have hw : ∀ x, (c⁻¹ * g x).re = Y x := fun x => by
    rw [hrep x, ← mul_assoc, inv_mul_cancel₀ hc, one_mul, Complex.ofReal_re]
  have hwne : (fun x => (c⁻¹ * g x).re) ≠ 0 := by
    intro h0'
    apply hne
    funext x
    have := congrFun h0' x
    simp only [Pi.zero_apply] at this
    rw [hw x] at this
    rw [hrep x, this]; simp
  have sw := (isSturmLiouvilleSolution_re_const_mul hd hG c⁻¹).1
  have hosc := ODE.encard_zeros_eq_encard_separatedSpectrum_inter_Iio_of_isSturmLiouvilleSolution hV
      hB hL odd0 oddK sw ⟨b0 c⁻¹, bL c⁻¹⟩ hwne
  refine ⟨⟨_, sw, ⟨b0 c⁻¹, bL c⁻¹⟩, hwne⟩, ?_⟩
  rw [← hosc]
  congr 1
  ext x
  simp only [mem_ofPred_eq, hw x]
  rw [hrep x]
  simp [hc]

/-- A strictly decreasing map `{0, …, n} → {0, …, n}` is `j ↦ n - j`. -/
private lemma eq_sub_of_strictAnti {f : ℕ → ℕ} {n : ℕ} (hlt : ∀ i j, i < j → j ≤ n → f j < f i)
    (hle : ∀ j ≤ n, f j ≤ n) : ∀ j ≤ n, f j = n - j := by
  have up : ∀ j ≤ n, f j ≤ n - j := by
    intro j
    induction j with
    | zero => intro h; simpa using hle 0 h
    | succ j ih =>
      intro hj
      have := hlt j (j + 1) (by omega) hj
      have := ih (by omega)
      omega
  have low : ∀ d ≤ n, d ≤ f (n - d) := by
    intro d
    induction d with
    | zero => intro _; simp
    | succ d ih =>
      intro hd
      have := hlt (n - (d + 1)) (n - d) (by omega) (by omega)
      have := ih (by omega)
      omega
  intro j hj
  have h1 := up j hj
  have h2 := low (n - j) (by omega)
  rw [show n - (n - j) = j by omega] at h2
  omega

/-! ### The vertical side `K + i[0, K']` -/

variable {k : ℝ}

/-- **`sn` on the vertical side**: `sn(K + iy, k) = 1/dn(y, k')` (DLMF 22.4.3 and Jacobi's
imaginary transformation 22.6.1). -/
private lemma jacobiSn_K_add_I_mul (hk0 : 0 < k) (hk1 : k < 1) (y : ℝ) :
    jacobiSn ((Real.completeEllipticKOfParameter (k ^ 2) : ℂ) + I * y) k =
      ((Real.jacobiDnOfParameter y (1 - k ^ 2))⁻¹ : ℝ) := by
  obtain ⟨h0, h1, h2⟩ := comodulus_mem_Ioo hk0 hk1
  have hkD := ofReal_mem_jacobiModulusDomain hk0 hk1
  have hK : completeEllipticK (k : ℂ) = Real.completeEllipticKOfParameter (k ^ 2) :=
    completeEllipticK_ofReal (by nlinarith)
  have e1 := (jacobiSn_shift hkD (I * y)).1
  rw [hK, add_comm] at e1
  have e2 := (jacobi_imaginary_transformation hkD (y : ℂ)).2.2.2.1
  rw [e1, e2, jacobiComodulus_ofReal hk0 hk1, jacobiNd, jacobiPQ_eq_one_div, ← jacobiDn,
    jacobiDn_ofReal h0 h1, h2]
  push_cast
  ring

/-- Bounds for `dn(y, k')`: `k ≤ dn ≤ 1`. -/
private lemma jacobiDnOfParameter_comodulus_bounds (hk0 : 0 < k) (hk1 : k < 1) (y : ℝ) :
    0 < Real.jacobiDnOfParameter y (1 - k ^ 2) ∧ k ^ 2 ≤
        Real.jacobiDnOfParameter y (1 - k ^ 2) ^ 2 ∧
      Real.jacobiDnOfParameter y (1 - k ^ 2) ^ 2 ≤ 1 := by
  have hm : 1 - k ^ 2 < 1 := by nlinarith
  have e := Real.mul_jacobiSnOfParameter_sq_add_jacobiDnOfParameter_sq hm y
  have s := Real.jacobiSnOfParameter_sq_add_jacobiCnOfParameter_sq y (1 - k ^ 2)
  have hk2 : 0 ≤ 1 - k ^ 2 := by nlinarith
  refine ⟨Real.jacobiDnOfParameter_pos hm y, ?_, ?_⟩
  · nlinarith [mul_nonneg hk2 (sq_nonneg (Real.jacobiCnOfParameter y (1 - k ^ 2)))]
  · nlinarith [mul_nonneg hk2 (sq_nonneg (Real.jacobiSnOfParameter y (1 - k ^ 2)))]

/-- Strict bounds `k < dn(y, k') < 1` on `(0, K')`. -/
private lemma jacobiDnOfParameter_comodulus_strict_bounds (hk0 : 0 < k) (hk1 : k < 1) {y : ℝ}
    (hy : y ∈ Ioo 0 (Real.completeEllipticKOfParameter (1 - k ^ 2))) :
    k ^ 2 < Real.jacobiDnOfParameter y (1 - k ^ 2) ^ 2 ∧
        Real.jacobiDnOfParameter y (1 - k ^ 2) ^ 2 < 1 := by
  obtain ⟨h0, h1, h2⟩ := comodulus_mem_Ioo hk0 hk1
  have hy' : y ∈ Ioo 0
      (Real.completeEllipticKOfParameter (Real.sqrt (1 - k ^ 2) ^ 2)) := by rwa [h2]
  have hs := jacobiSnOfParameter_pos_of_mem_Ioo h0 h1 hy'
  have hc := jacobiCnOfParameter_pos_of_mem_Ioo h0 h1 hy'
  rw [h2] at hs hc
  have hm : 1 - k ^ 2 < 1 := by nlinarith
  have e := Real.mul_jacobiSnOfParameter_sq_add_jacobiDnOfParameter_sq hm y
  have s := Real.jacobiSnOfParameter_sq_add_jacobiCnOfParameter_sq y (1 - k ^ 2)
  have hk2 : 0 < 1 - k ^ 2 := by nlinarith
  constructor
  · nlinarith [mul_pos hk2 (pow_pos hc 2)]
  · nlinarith [mul_pos hk2 (pow_pos hs 2)]

/-- `dn(·, k')²` is injective on `(0, K')`. -/
private lemma injOn_jacobiDnOfParameter_comodulus_sq (hk0 : 0 < k) (hk1 : k < 1) :
    InjOn (fun y => Real.jacobiDnOfParameter y (1 - k ^ 2) ^ 2)
        (Ioo 0 (Real.completeEllipticKOfParameter (1 - k ^ 2))) := by
  obtain ⟨h0, h1, h2⟩ := comodulus_mem_Ioo hk0 hk1
  have hinj := injOn_jacobiSnOfParameter_sq h0 h1
  rw [h2] at hinj
  intro x hx y hy hxy
  apply hinj hx hy
  have hm : 1 - k ^ 2 < 1 := by nlinarith
  have ex := Real.mul_jacobiSnOfParameter_sq_add_jacobiDnOfParameter_sq hm x
  have ey := Real.mul_jacobiSnOfParameter_sq_add_jacobiDnOfParameter_sq hm y
  simp only at hxy ⊢
  have hk2 : (1 - k ^ 2) ≠ 0 := by nlinarith
  apply mul_left_cancel₀ hk2
  linarith

/-- The potential `-ν(ν+1) k² sn²(K + iy, k) = -ν(ν+1) k²/dn²(y, k')` along the vertical side. -/
def verticalPotential (ν k y : ℝ) : ℝ :=
    -(ν * (ν + 1) * k ^ 2 * (Real.jacobiDnOfParameter y (1 - k ^ 2) ^ 2)⁻¹)

/-- The vertical potential is continuous. -/
private lemma continuous_verticalPotential (hk0 : 0 < k) (ν : ℝ) : Continuous
    (verticalPotential ν k) := by
  have hm : 1 - k ^ 2 < 1 := by nlinarith
  have hc : Continuous fun y => Real.jacobiDnOfParameter y (1 - k ^ 2) :=
    continuous_iff_continuousAt.2 fun y => (Real.hasDerivAt_jacobiDnOfParameter hm y).continuousAt
  exact ((continuous_const.mul ((hc.pow 2).inv₀ fun y =>
    (pow_pos (Real.jacobiDnOfParameter_pos hm y) 2).ne'))).neg

/-- The vertical potential is bounded. -/
private lemma abs_verticalPotential_le (hk0 : 0 < k) (hk1 : k < 1) (ν y : ℝ) : |verticalPotential ν
    k y| ≤ |ν * (ν + 1)| := by
  obtain ⟨hp, hl, -⟩ := jacobiDnOfParameter_comodulus_bounds hk0 hk1 y
  have hd : 0 < Real.jacobiDnOfParameter y (1 - k ^ 2) ^ 2 := by positivity
  have h1 : k ^ 2 * (Real.jacobiDnOfParameter y (1 - k ^ 2) ^ 2)⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one hd]; exact hl
  have h2 : 0 ≤ k ^ 2 * (Real.jacobiDnOfParameter y (1 - k ^ 2) ^ 2)⁻¹ := by positivity
  rw [verticalPotential, abs_neg, show ν * (ν + 1) * k ^ 2 *
      (Real.jacobiDnOfParameter y (1 - k ^ 2) ^ 2)⁻¹ =
    ν * (ν + 1) * (k ^ 2 * (Real.jacobiDnOfParameter y (1 - k ^ 2) ^ 2)⁻¹) by ring, abs_mul,
    abs_of_nonneg h2]
  nlinarith [abs_nonneg (ν * (ν + 1))]

/-- The boundary type at `K + iK'`: odd for a factor `dn`. -/
def lamePolyOddKiK : LamePolynomialType → Bool
  | .dE | .sdE | .cdE | .scdE => true
  | _ => false

/-- **Lamé's equation along the vertical side.** `g(y) = E(K + iy)` solves
`g'' = (V(y) + h) g` with the potential `verticalPotential`. -/
private lemma lamePolynomialE_vertical_ode (hk0 : 0 < k) (hk1 : k < 1) (t : LamePolynomialType)
    {n j : ℕ} (hj : j ≤ n) :
    Differentiable ℝ (fun y : ℝ =>
        lamePolynomialE t n j ((Real.completeEllipticKOfParameter (k ^ 2) : ℂ) + I * y) k) ∧
      (∀ y : ℝ, deriv (fun y : ℝ =>
        lamePolynomialE t n j ((Real.completeEllipticKOfParameter (k ^ 2) : ℂ) + I * y) k) y =
        deriv (fun z => lamePolynomialE t n j z k)
            ((Real.completeEllipticKOfParameter (k ^ 2) : ℂ) + I * y) * I) ∧
      ∀ y : ℝ, HasDerivAt (deriv (fun y : ℝ =>
        lamePolynomialE t n j ((Real.completeEllipticKOfParameter (k ^ 2) : ℂ) + I * y) k))
        (((verticalPotential (t.order n : ℝ) k y -
          -((lamePolynomialH t n j k + (t.order n : ℝ) * ((t.order n : ℝ) + 1) * k ^ 2) / 2) : ℝ) :
            ℂ) * lamePolynomialE t n j
                ((Real.completeEllipticKOfParameter (k ^ 2) : ℂ) + I * y) k) y := by
  have hsol := lamePolynomialE_isLameSolutionOn hk0 hk1 t hj
  set E := fun z => lamePolynomialE t n j z k
  set K : ℂ := (Real.completeEllipticKOfParameter (k ^ 2) : ℂ)
  have hγ : ∀ y : ℝ, HasDerivAt (fun y : ℝ => K + I * y) I y := fun y => by
    have := ((hasDerivAt_id y).ofReal_comp.const_mul I).const_add K
    simpa using this
  have reg := isJacobiRegular_K_add_I_mul hk0 hk1
  have d1 : ∀ y : ℝ, HasDerivAt (fun y : ℝ => E (K + I * y)) (deriv E (K + I * y) * I) y :=
    fun y => HasDerivAt.comp (h₂ := E) (h := fun y : ℝ => K + I * (y : ℂ)) y
      (hsol.differentiableAt _ (reg y)).hasDerivAt (hγ y)
  have e : deriv (fun y : ℝ => E (K + I * y)) = fun y : ℝ => deriv E (K + I * y) * I :=
    funext fun y => (d1 y).deriv
  refine ⟨fun y => (d1 y).differentiableAt, fun y => congrFun e y, fun y => ?_⟩
  rw [e]
  have d2 := (HasDerivAt.comp (h₂ := deriv E) (h := fun y : ℝ => K + I * (y : ℂ)) y
    (hsol.hasDerivAt_deriv _ (reg y)) (hγ y)).mul_const I
  refine d2.congr_deriv ?_
  rw [jacobiSn_K_add_I_mul hk0 hk1 y]
  simp only [verticalPotential]
  push_cast
  linear_combination (-((lamePolynomialH t n j k + (t.order n : ℂ) *
      ((t.order n : ℂ) + 1) * k ^ 2) / 2 -
    (t.order n : ℂ) * ((t.order n : ℂ) + 1) * k ^ 2 *
        ((Real.jacobiDnOfParameter y (1 - k ^ 2) : ℂ))⁻¹ ^ 2) *
    E (K + I * y)) * I_sq

/-- The boundary conditions along the vertical side, at `K` (type of `cn`) and at `K + iK'`
(type of `dn`). -/
private lemma lamePolynomialE_vertical_boundary (hk0 : 0 < k) (hk1 : k < 1) (t : LamePolynomialType)
    {n j : ℕ} (hj : j ≤ n) :
    (if lamePolyOddK t then
        (fun y : ℝ => lamePolynomialE t n j
            ((Real.completeEllipticKOfParameter (k ^ 2) : ℂ) + I * y) k) 0 = 0
      else deriv (fun y : ℝ =>
        lamePolynomialE t n j ((Real.completeEllipticKOfParameter (k ^ 2) : ℂ) + I * y) k) 0 = 0) ∧
    (if lamePolyOddKiK t then
        (fun y : ℝ => lamePolynomialE t n j
            ((Real.completeEllipticKOfParameter (k ^ 2) : ℂ) + I * y) k)
          (Real.completeEllipticKOfParameter (1 - k ^ 2)) = 0
      else deriv (fun y : ℝ =>
        lamePolynomialE t n j ((Real.completeEllipticKOfParameter (k ^ 2) : ℂ) + I * y) k)
          (Real.completeEllipticKOfParameter (1 - k ^ 2)) = 0) := by
  have hsol := lamePolynomialE_isLameSolutionOn hk0 hk1 t hj
  obtain ⟨-, hde, -⟩ := lamePolynomialE_vertical_ode hk0 hk1 t hj
  obtain ⟨-, s2, s3, -⟩ := lamePolynomialE_reflection_period hk0 hk1 t n j
  have reg := isJacobiRegular_K_add_I_mul hk0 hk1
  have r0 := reg 0
  simp only [Complex.ofReal_zero, mul_zero, add_zero] at r0
  have v2 := eq_zero_or_deriv_eq_zero_of_reflection (hsol.differentiableAt _ r0) s2
  have v3 := eq_zero_or_deriv_eq_zero_of_reflection
      (hsol.differentiableAt _ (reg (Real.completeEllipticKOfParameter (1 - k ^ 2)))) s3
  have eK : lamePolySignCn t = if lamePolyOddK t then -1 else 1 := by cases t <;> rfl
  have eD : lamePolySignDn t = if lamePolyOddKiK t then -1 else 1 := by cases t <;> rfl
  refine ⟨?_, ?_⟩
  · rw [hde 0]
    by_cases ho : lamePolyOddK t = true
    · simp only [ho, ite_true] at eK ⊢
      simpa using v2.1 eK
    · simp only [ho, Bool.false_eq_true, ite_false] at eK ⊢
      simp [v2.2 eK]
  · rw [hde]
    by_cases ho : lamePolyOddKiK t = true
    · simp only [ho, ite_true] at eD ⊢
      exact v3.1 eD
    · simp only [ho, Bool.false_eq_true, ite_false] at eD ⊢
      simp [v3.2 eD]

/-- Evaluation of a real polynomial at a real point, in `ℂ`. -/
private lemma eval_ofReal_map_ofReal (P : ℝ[X]) (x : ℝ) :
    (P.map (algebraMap ℝ ℂ)).eval (x : ℂ) = ((P.eval x : ℝ) : ℂ) := by
  rw [eval_map_algebraMap, show (x : ℂ) = algebraMap ℝ ℂ x from rfl, aeval_algebraMap_apply,
    coe_aeval_eq_eval]
  rfl

/-- **Zeros on the vertical side**: `E(K + iy) = 0` (`0 < y < K'`) iff `1/dn²(y, k')` is a
root of the polynomial `P` of 29.12.10; there are at most `n` zeros, and `E` does not vanish
identically there. -/
private lemma lamePolynomialE_vertical_zeros (hk0 : 0 < k) (hk1 : k < 1) (t : LamePolynomialType)
    {n j : ℕ} (hj : j ≤ n) :
    {y | y ∈ Ioo 0 (Real.completeEllipticKOfParameter (1 - k ^ 2)) ∧
        lamePolynomialE t n j ((Real.completeEllipticKOfParameter (k ^ 2) : ℂ) + I * y)
            k = 0}.Finite ∧
      {y | y ∈ Ioo 0 (Real.completeEllipticKOfParameter (1 - k ^ 2)) ∧
        lamePolynomialE t n j ((Real.completeEllipticKOfParameter (k ^ 2) : ℂ) + I * y) k
            = 0}.ncard ≤ n ∧
      (fun y : ℝ => lamePolynomialE t n j
          ((Real.completeEllipticKOfParameter (k ^ 2) : ℂ) + I * y) k) ≠ 0 := by
  obtain ⟨P, hP, hE⟩ := lamePolynomialE_eq_prefactor_mul_eval hk0 hk1 t hj
  have hP0 : P ≠ 0 := fun h0 => by simp [h0] at hP
  have hPd : P.natDegree = n := natDegree_eq_of_degree_eq_some hP
  have hkD := ofReal_mem_jacobiModulusDomain hk0 hk1
  set Z := {y | y ∈ Ioo 0 (Real.completeEllipticKOfParameter (1 - k ^ 2)) ∧
    lamePolynomialE t n j ((Real.completeEllipticKOfParameter (k ^ 2) : ℂ) + I * y) k = 0}
  set φ : ℝ → ℝ := fun y => (Real.jacobiDnOfParameter y (1 - k ^ 2) ^ 2)⁻¹
  have hmaps : ∀ y ∈ Z, φ y ∈ (P.roots.toFinset : Set ℝ) := by
    rintro y ⟨hy, h0⟩
    obtain ⟨hp, -, -⟩ := jacobiDnOfParameter_comodulus_bounds hk0 hk1 y
    obtain ⟨hl, hu⟩ := jacobiDnOfParameter_comodulus_strict_bounds hk0 hk1 hy
    set z : ℂ := (Real.completeEllipticKOfParameter (k ^ 2) : ℂ) + I * y
    have hsn := jacobiSn_K_add_I_mul hk0 hk1 y
    obtain ⟨sc, sd⟩ := jacobi_sq_sum hkD (isJacobiRegular_K_add_I_mul hk0 hk1 y)
    have hs : jacobiSn z k ≠ 0 := by
      rw [hsn]; exact_mod_cast (inv_pos.2 hp).ne'
    have hc : jacobiCn z k ≠ 0 := by
      intro h
      rw [h, hsn] at sc
      have : (((Real.jacobiDnOfParameter y (1 - k ^ 2))⁻¹ ^ 2 : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by
        push_cast at sc ⊢; linear_combination sc
      have h2 := Complex.ofReal_injective this
      rw [inv_pow] at h2
      have := inv_eq_one.1 h2
      linarith
    have hd : jacobiDn z k ≠ 0 := by
      intro h
      rw [h, hsn] at sd
      have : ((k ^ 2 * (Real.jacobiDnOfParameter y (1 - k ^ 2))⁻¹ ^ 2 : ℝ) : ℂ) =
          ((1 : ℝ) : ℂ) := by
        push_cast at sd ⊢; linear_combination sd
      have h2 := Complex.ofReal_injective this
      rw [inv_pow, ← div_eq_mul_inv, div_eq_one_iff_eq (by positivity)] at h2
      linarith
    have hpre : t.prefactor z k *
        (if t = .sE ∨ t = .scE ∨ t = .sdE ∨ t = .scdE then jacobiSn z k else 1) ≠ 0 := by
      cases t <;> simp [LamePolynomialType.prefactor, hs, hc, hd]
    rw [hE z] at h0
    have h1 := (mul_eq_zero.1 h0).resolve_left hpre
    rw [hsn, show (((Real.jacobiDnOfParameter y (1 - k ^ 2))⁻¹ : ℝ) : ℂ) ^ 2 = ((φ y : ℝ) : ℂ) by
      simp only [φ]; push_cast; ring, eval_ofReal_map_ofReal, Complex.ofReal_eq_zero] at h1
    simp [Multiset.mem_toFinset, mem_roots hP0, h1]
  have hinj : InjOn φ Z := by
    intro x hx y hy hxy
    exact injOn_jacobiDnOfParameter_comodulus_sq hk0 hk1 hx.1 hy.1 (inv_injective hxy)
  have hfin : Z.Finite := Set.Finite.of_injOn hmaps hinj (Finset.finite_toSet _)
  refine ⟨hfin, ?_, fun h0 => ?_⟩
  · calc Z.ncard ≤ (P.roots.toFinset : Set ℝ).ncard :=
          Set.ncard_le_ncard_of_injOn _ hmaps hinj (Finset.finite_toSet _)
      _ = P.roots.toFinset.card := Set.ncard_coe_finset _
      _ ≤ P.roots.card := Multiset.toFinset_card_le _
      _ ≤ P.natDegree := card_roots' P
      _ = n := hPd
  · have hK' : 0 < Real.completeEllipticKOfParameter (1 - k ^ 2) :=
        Real.completeEllipticKOfParameter_pos (by nlinarith)
    have : Ioo 0 (Real.completeEllipticKOfParameter (1 - k ^ 2)) ⊆ Z := fun y hy =>
      ⟨hy, by simpa using congrFun h0 y⟩
    exact (Set.Ioo_infinite hK') (hfin.subset this)

/-- **Zeros on the vertical side** (§29.12(i)): `E = lamePolynomialE t n m` has exactly `n - m`
zeros on the open segment from `K` to `K + iK'`. Along `y ↦ K + iy` the Lamé equation becomes
a Sturm–Liouville problem in `y` with eigenvalue parameter `-h`; the `n + 1` Lamé polynomials of
type `t` have at most `n` zeros there and strictly decreasing parameters, so by Sturm's
oscillation theorem the `m`th has `n - m` zeros. -/
theorem ncard_zeros_lamePolynomialE_vertical (hk0 : 0 < k) (hk1 : k < 1) (t : LamePolynomialType)
    {n m : ℕ} (hm : m ≤ n) :
    {y : ℝ | y ∈ Ioo 0 (Real.completeEllipticKOfParameter (1 - k ^ 2)) ∧
      lamePolynomialE t n m ((Real.completeEllipticKOfParameter (k ^ 2) : ℂ) + I * y) k =
          0}.ncard = n - m := by
  set ν : ℝ := (t.order n : ℝ)
  set L := Real.completeEllipticKOfParameter (1 - k ^ 2)
  have hL : 0 < L := Real.completeEllipticKOfParameter_pos (by nlinarith)
  have hV := continuous_verticalPotential hk0 ν
  have hB := abs_verticalPotential_le hk0 hk1 ν
  set hv : ℕ → ℝ := fun j => (lamePolynomialH t n j k + ν * (ν + 1) * k ^ 2) / 2
  set Sp := ODE.separatedSpectrum (verticalPotential ν k) L (lamePolyOddK t) (lamePolyOddKiK t)
  have hfin : ∀ c, (Sp ∩ Iio c).Finite := fun c =>
      ODE.separatedSpectrum_inter_Iio_finite hV hB hL _ _ c
  have key : ∀ j ≤ n, -hv j ∈ Sp ∧ {y : ℝ | y ∈ Ioo 0 L ∧
      lamePolynomialE t n j ((Real.completeEllipticKOfParameter (k ^ 2) : ℂ) + I * y) k = 0}.ncard =
        (Sp ∩ Iio (-hv j)).ncard := by
    intro j hj
    obtain ⟨hd, -, hode⟩ := lamePolynomialE_vertical_ode hk0 hk1 t hj
    obtain ⟨b0, bL⟩ := lamePolynomialE_vertical_boundary hk0 hk1 t hj
    obtain ⟨hZf, -, hne⟩ := lamePolynomialE_vertical_zeros hk0 hk1 t hj
    obtain ⟨hmem, henc⟩ := encard_zeros_of_complex_solution hV hB hL _ _ hd hode b0 bL hne
    refine ⟨hmem, ?_⟩
    rw [← Set.Finite.cast_ncard_eq hZf, ← Set.Finite.cast_ncard_eq (hfin _)] at henc
    exact ENat.natCast_inj.1 henc
  set f : ℕ → ℕ := fun j => (Sp ∩ Iio (-hv j)).ncard
  have hle : ∀ j ≤ n, f j ≤ n := fun j hj => by
    simp only [f]; rw [← (key j hj).2]; exact (lamePolynomialE_vertical_zeros hk0 hk1 t hj).2.1
  have hlt : ∀ i j, i < j → j ≤ n → f j < f i := by
    intro i j hij hj
    have h1 : -hv j < -hv i := by
      simp only [hv]; linarith [lamePolynomialH_lt_of_lt hk0 hk1 t hij hj]
    refine Set.ncard_lt_ncard ?_ (hfin _)
    refine ⟨fun x hx => ⟨hx.1, lt_trans hx.2 h1⟩, fun hsub => ?_⟩
    exact lt_irrefl _ (Set.mem_Iio.mp (hsub ⟨(key j hj).1, h1⟩).2)
  rw [(key m hm).2]
  exact eq_sub_of_strictAnti hlt hle m hm

/-- **The vertical Sturm–Liouville problem.** Along `y ↦ K + iy` the Lamé polynomial
`lamePolynomialE t n j` is an eigenfunction of `g'' = (V(y) - μ) g` (`V = verticalPotential`) on
`[0, K']` with the boundary types `lamePolyOddK t`, `lamePolyOddKiK t`, for
`μ = -½(H_j + ν(ν+1)k²)`, and exactly `n - j` points of that spectrum lie below `μ`. -/
theorem lamePolynomialE_vertical_spectrum (hk0 : 0 < k) (hk1 : k < 1) (t : LamePolynomialType)
    {n j : ℕ} (hj : j ≤ n) :
    -((lamePolynomialH t n j k + (t.order n : ℝ) * ((t.order n : ℝ) + 1) * k ^ 2) / 2) ∈
        ODE.separatedSpectrum (verticalPotential (t.order n : ℝ) k)
          (Real.completeEllipticKOfParameter (1 - k ^ 2)) (lamePolyOddK t) (lamePolyOddKiK t) ∧
      (ODE.separatedSpectrum (verticalPotential (t.order n : ℝ) k)
          (Real.completeEllipticKOfParameter (1 - k ^ 2)) (lamePolyOddK t) (lamePolyOddKiK t) ∩
        Iio (-((lamePolynomialH t n j k + (t.order n : ℝ) * ((t.order n : ℝ) + 1) *
            k ^ 2) / 2))).ncard =
        n - j := by
  have hL : 0 < Real.completeEllipticKOfParameter (1 - k ^ 2) :=
      Real.completeEllipticKOfParameter_pos (by nlinarith)
  have hV := continuous_verticalPotential hk0 (t.order n : ℝ)
  have hB := abs_verticalPotential_le hk0 hk1 (t.order n : ℝ)
  obtain ⟨hd, -, hode⟩ := lamePolynomialE_vertical_ode hk0 hk1 t hj
  obtain ⟨b0, bL⟩ := lamePolynomialE_vertical_boundary hk0 hk1 t hj
  obtain ⟨hZf, -, hne⟩ := lamePolynomialE_vertical_zeros hk0 hk1 t hj
  obtain ⟨hmem, henc⟩ := encard_zeros_of_complex_solution hV hB hL _ _ hd hode b0 bL hne
  refine ⟨by simpa using hmem, ?_⟩
  rw [← ncard_zeros_lamePolynomialE_vertical hk0 hk1 t hj]
  rw [← Set.Finite.cast_ncard_eq hZf, ← Set.Finite.cast_ncard_eq
    (ODE.separatedSpectrum_inter_Iio_finite hV hB hL _ _ _)] at henc
  simpa using (ENat.natCast_inj.1 henc).symm

/-- **Zeros on `(0, K)`** (§29.12(i)): `lamePolynomialE t n m` has exactly `m` zeros in `(0, K)`. -/
theorem ncard_zeros_lamePolynomialE_real (hk0 : 0 < k) (hk1 : k < 1) (t : LamePolynomialType)
    {n m : ℕ} (hm : m ≤ n) :
    {x : ℝ | x ∈ Ioo 0 (Real.completeEllipticKOfParameter (k ^ 2)) ∧ lamePolynomialE t n m x k =
        0}.ncard = m := by
  have hk : k ^ 2 < 1 := by nlinarith
  have hK : 0 < Real.completeEllipticKOfParameter (k ^ 2) :=
      Real.completeEllipticKOfParameter_pos hk
  set ν : ℝ := (t.order n : ℝ)
  have hS := lameSpectrum_eq_separatedSpectrum (ν := ν) (k := k) (lamePolyOddZero t)
      (lamePolyOddK t)
  obtain ⟨hre, hbc, hne⟩ := isLameEigenfunction_lamePolynomialE_re hk0 hk1 t hm
  obtain ⟨hZf, -, -⟩ := lamePolynomialE_zeros_finite_le hk0 hk1 t hm
  have hosc := ODE.encard_zeros_eq_encard_separatedSpectrum_inter_Iio_of_isSturmLiouvilleSolution
      (continuous_lamePotential hk) abs_lamePotential_le hK
    (lamePolyOddZero t) (lamePolyOddK t)
        ((isLameSolution_iff_isSturmLiouvilleSolution).mp hre) hbc hne
  rw [← hS] at hosc
  have hν : -1 / 2 ≤ ν := by
    simp only [ν]; have := Nat.cast_nonneg (α := ℝ) (t.order n); linarith
  have hnth := Real.isNthLameEigenvalue_lameEigenvalue (ν := ν) hk0 hk1 (lamePolyOddZero t)
      (lamePolyOddK t) m
  rw [lameEigenvalue_lamePolynomialType_eq hk0 hk1 t hm] at hnth
  obtain ⟨-, hfin, hcard⟩ := hnth
  have hset : {x : ℝ | x ∈ Ioo 0 (Real.completeEllipticKOfParameter (k ^ 2)) ∧
                 lamePolynomialE t n m x k = 0} =
      {x | x ∈ Ioo 0 (Real.completeEllipticKOfParameter (k ^ 2)) ∧
          (lamePolynomialE t n m x k).re = 0} := by
    obtain ⟨P, -, -, hE⟩ := lamePolynomialE_ofReal_eq hk0 hk1 t hm
    ext x
    simp only [mem_ofPred_eq, hE x, Complex.ofReal_re, Complex.ofReal_eq_zero]
  rw [hset]
  rw [← Set.Finite.cast_ncard_eq hZf, ← Set.Finite.cast_ncard_eq hfin] at hosc
  exact (ENat.natCast_inj.1 hosc).trans hcard

/-- The prefactor of 29.12.9 does not vanish where `sn, cn, dn ≠ 0`. -/
private lemma prefactor_mul_jacobiSn_ne_zero (t : LamePolynomialType) {z : ℂ} {k : ℂ}
    (hs : jacobiSn z k ≠ 0)
    (hc : jacobiCn z k ≠ 0) (hd : jacobiDn z k ≠ 0) :
    t.prefactor z k * (if t = .sE ∨ t = .scE ∨ t = .sdE ∨ t = .scdE then jacobiSn z k else 1) ≠
      0 := by
  cases t <;> simp [LamePolynomialType.prefactor, hs, hc, hd]

/-- For a multiset without duplicates, filtering commutes with `toFinset` on cardinalities. -/
private lemma card_filter_eq_card_filter_toFinset {s : Multiset ℝ} (hs : s.Nodup) (q : ℝ → Prop)
    [DecidablePred q] :
    (s.filter q).card = (s.toFinset.filter q).card := by
  rw [← Multiset.toFinset_filter, Multiset.toFinset_card_of_nodup (hs.filter q)]

/-- In `E = pre · sn^ρ · P(sn²)`, any polynomial `P` of degree `n` has `n`
simple zeros, `m` of them in `(0, 1)` and `n - m` in `(1, k⁻²)`. The zeros of `E` on `(0, K)`
and on `K + i(0, K')` (`ncard_zeros_lamePolynomialE_real`, `ncard_zeros_lamePolynomialE_vertical`)
give `m` and `n - m` distinct roots `sn²(x) ∈ (0, 1)` and `1/dn²(y, k') ∈ (1, k⁻²)`. -/
theorem roots_of_lamePolynomialE_eq (hk0 : 0 < k) (hk1 : k < 1) (t : LamePolynomialType)
    {n m : ℕ} (hm : m ≤ n) {P : ℝ[X]} (hP : P.degree = n)
    (hE : ∀ z : ℂ, lamePolynomialE t n m z k = t.prefactor z k *
        (if t = .sE ∨ t = .scE ∨ t = .sdE ∨ t = .scdE then jacobiSn z k else 1) *
        (P.map (algebraMap ℝ ℂ)).eval (jacobiSn z k ^ 2)) :
    P.natDegree = n ∧ P.roots.Nodup ∧ P.roots.card = n ∧
      (P.roots.filter (· ∈ Ioo (0 : ℝ) 1)).card = m ∧
      (P.roots.filter (· ∈ Ioo (1 : ℝ) (k ^ 2)⁻¹)).card = n - m := by
  have hP0 : P ≠ 0 := fun h0 => by simp [h0] at hP
  have hPd : P.natDegree = n := natDegree_eq_of_degree_eq_some hP
  have hk2 : k ^ 2 < 1 := by nlinarith
  have hkp : 0 < k ^ 2 := by positivity
  set R := P.roots.toFinset
  set A := R.filter (· ∈ Ioo (0 : ℝ) 1)
  set B := R.filter (· ∈ Ioo (1 : ℝ) (k ^ 2)⁻¹)
  have hroot : ∀ {z : ℂ} {r : ℝ}, lamePolynomialE t n m z k = 0 → jacobiSn z k ^ 2 = r →
      jacobiSn z k ≠ 0 → jacobiCn z k ≠ 0 → jacobiDn z k ≠ 0 → r ∈ R := by
    intro z r h0 hr hs hc hd
    rw [hE z] at h0
    have h1 := (mul_eq_zero.1 h0).resolve_left (prefactor_mul_jacobiSn_ne_zero t hs hc hd)
    rw [hr, eval_ofReal_map_ofReal, Complex.ofReal_eq_zero] at h1
    simp [R, Multiset.mem_toFinset, mem_roots hP0, h1]
  -- `m` roots in `(0, 1)`
  have hA : m ≤ A.card := by
    set Z := {x : ℝ | x ∈ Ioo 0 (Real.completeEllipticKOfParameter (k ^ 2)) ∧
                lamePolynomialE t n m x k = 0}
    have hmaps : ∀ x ∈ Z, (fun x => Real.jacobiSnOfParameter x (k ^ 2) ^ 2) x ∈ (A : Set ℝ) := by
      rintro x ⟨hx, h0⟩
      have hs := jacobiSnOfParameter_pos_of_mem_Ioo hk0 hk1 hx
      have hc := jacobiCnOfParameter_pos_of_mem_Ioo hk0 hk1 hx
      have hd := Real.jacobiDnOfParameter_pos hk2 x
      have e := Real.jacobiSnOfParameter_sq_add_jacobiCnOfParameter_sq x (k ^ 2)
      simp only [A, Finset.coe_filter, mem_ofPred_eq]
      refine ⟨hroot h0 (by rw [jacobiSn_ofReal hk0 hk1]; push_cast; ring)
        (by rw [jacobiSn_ofReal hk0 hk1]; exact_mod_cast hs.ne')
        (by rw [jacobiCn_ofReal hk0 hk1]; exact_mod_cast hc.ne')
        (by rw [jacobiDn_ofReal hk0 hk1]; exact_mod_cast hd.ne'), by positivity, ?_⟩
      nlinarith [pow_pos hc 2]
    have hinj : InjOn (fun x => Real.jacobiSnOfParameter x (k ^ 2) ^ 2) Z :=
      (injOn_jacobiSnOfParameter_sq hk0 hk1).mono fun x hx => hx.1
    calc m = Z.ncard := (ncard_zeros_lamePolynomialE_real hk0 hk1 t hm).symm
      _ ≤ (A : Set ℝ).ncard := Set.ncard_le_ncard_of_injOn _ hmaps hinj (Finset.finite_toSet _)
      _ = A.card := Set.ncard_coe_finset _
  -- `n - m` roots in `(1, k⁻²)`
  have hB : n - m ≤ B.card := by
    set Z := {y : ℝ | y ∈ Ioo 0 (Real.completeEllipticKOfParameter (1 - k ^ 2)) ∧
      lamePolynomialE t n m ((Real.completeEllipticKOfParameter (k ^ 2) : ℂ) + I * y) k = 0}
    set φ : ℝ → ℝ := fun y => (Real.jacobiDnOfParameter y (1 - k ^ 2) ^ 2)⁻¹
    have hkD := ofReal_mem_jacobiModulusDomain hk0 hk1
    have hmaps : ∀ y ∈ Z, φ y ∈ (B : Set ℝ) := by
      rintro y ⟨hy, h0⟩
      obtain ⟨hp, -, -⟩ := jacobiDnOfParameter_comodulus_bounds hk0 hk1 y
      obtain ⟨hl, hu⟩ := jacobiDnOfParameter_comodulus_strict_bounds hk0 hk1 hy
      set z : ℂ := (Real.completeEllipticKOfParameter (k ^ 2) : ℂ) + I * y
      have hsn := jacobiSn_K_add_I_mul hk0 hk1 y
      obtain ⟨sc, sd⟩ := jacobi_sq_sum hkD (isJacobiRegular_K_add_I_mul hk0 hk1 y)
      have hs : jacobiSn z k ≠ 0 := by
        rw [hsn]; exact_mod_cast (inv_pos.2 hp).ne'
      have hc : jacobiCn z k ≠ 0 := by
        intro h
        rw [h, hsn] at sc
        have : (((Real.jacobiDnOfParameter y (1 - k ^ 2))⁻¹ ^ 2 : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by
          push_cast at sc ⊢; linear_combination sc
        have h2 := Complex.ofReal_injective this
        rw [inv_pow] at h2
        have := inv_eq_one.1 h2
        linarith
      have hd : jacobiDn z k ≠ 0 := by
        intro h
        rw [h, hsn] at sd
        have : ((k ^ 2 * (Real.jacobiDnOfParameter y (1 - k ^ 2))⁻¹ ^ 2 : ℝ) : ℂ) =
            ((1 : ℝ) : ℂ) := by
          push_cast at sd ⊢; linear_combination sd
        have h2 := Complex.ofReal_injective this
        rw [inv_pow, ← div_eq_mul_inv, div_eq_one_iff_eq (by positivity)] at h2
        linarith
      have hd2 : 0 < Real.jacobiDnOfParameter y (1 - k ^ 2) ^ 2 := by positivity
      simp only [B, Finset.coe_filter, mem_ofPred_eq]
      refine ⟨hroot h0 (by rw [hsn]; simp only [φ]; push_cast; ring) hs hc hd, ?_, ?_⟩
      · simp only [φ]; rw [lt_inv_comm₀ one_pos hd2, inv_one]; exact hu
      · simp only [φ]; exact (inv_lt_inv₀ hd2 hkp).2 hl
    have hinj : InjOn φ Z := fun x hx y hy hxy =>
      injOn_jacobiDnOfParameter_comodulus_sq hk0 hk1 hx.1 hy.1 (inv_injective hxy)
    calc n - m = Z.ncard := (ncard_zeros_lamePolynomialE_vertical hk0 hk1 t hm).symm
      _ ≤ (B : Set ℝ).ncard := Set.ncard_le_ncard_of_injOn _ hmaps hinj (Finset.finite_toSet _)
      _ = B.card := Set.ncard_coe_finset _
  -- counting
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro r hrA hrB
    simp only [A, B, Finset.mem_filter, mem_Ioo] at hrA hrB
    linarith [hrA.2.2, hrB.2.1]
  have hAB : A.card + B.card ≤ R.card := by
    rw [← Finset.card_union_of_disjoint hdisj]
    exact Finset.card_le_card (Finset.union_subset (Finset.filter_subset _ _)
      (Finset.filter_subset _ _))
  have hR : R.card ≤ P.roots.card := Multiset.toFinset_card_le _
  have hR2 : P.roots.card ≤ n := hPd ▸ card_roots' P
  have hcard : P.roots.card = n := by omega
  have hRc : R.card = P.roots.card := by omega
  have hnd : P.roots.Nodup := Multiset.toFinset_card_eq_card_iff_nodup.1 hRc
  have hAc : A.card = m := by omega
  have hBc : B.card = n - m := by omega
  refine ⟨hPd, hnd, hcard, ?_, ?_⟩
  · rw [card_filter_eq_card_filter_toFinset hnd]; exact hAc
  · rw [card_filter_eq_card_filter_toFinset hnd]; exact hBc

/-- **29.12.9–29.12.10**: in `E = pre · sn^ρ · P(sn²)` the polynomial `P` of degree `n` has `n`
simple zeros, `m` of them in `(0, 1)` and `n - m` in `(1, k⁻²)`
(`roots_of_lamePolynomialE_eq`). -/
theorem exists_poly_roots_lamePolynomialE (hk0 : 0 < k) (hk1 : k < 1) (t : LamePolynomialType)
    {n m : ℕ} (hm : m ≤ n) :
    ∃ P : ℝ[X], P.natDegree = n ∧ P.roots.Nodup ∧ P.roots.card = n ∧
      (P.roots.filter (· ∈ Ioo (0 : ℝ) 1)).card = m ∧
      (P.roots.filter (· ∈ Ioo (1 : ℝ) (k ^ 2)⁻¹)).card = n - m ∧
      ∀ z : ℂ, lamePolynomialE t n m z k = t.prefactor z k *
        (if t = .sE ∨ t = .scE ∨ t = .sdE ∨ t = .scdE then jacobiSn z k else 1) *
        (P.map (algebraMap ℝ ℂ)).eval (jacobiSn z k ^ 2) := by
  obtain ⟨P, hP, hE⟩ := lamePolynomialE_eq_prefactor_mul_eval hk0 hk1 t hm
  obtain ⟨h1, h2, h3, h4, h5⟩ := roots_of_lamePolynomialE_eq hk0 hk1 t hm hP hE
  exact ⟨P, h1, h2, h3, h4, h5, hE⟩

end DLMF.Lame
