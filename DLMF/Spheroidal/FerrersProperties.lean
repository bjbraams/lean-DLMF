/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Spheroidal.Basic.Equation
public import DLMF.Spheroidal.Basic.Ferrers
public import DLMF.Spheroidal.Existence
public import Mathlib.Analysis.SpecialFunctions.Artanh

/-!
# Existence and defining properties of spheroidal Ferrers functions

The definitions by choice in `DLMF.Spheroidal.Basic.Ferrers` rest on the existence statements
of this file, which retain their original domains and coefficient conventions.

## Main results

* `exists_isSpheroidalCoeffPrime`, `spheroidalCoeffPrime_spec`: existence of the recessive
  coefficients `a'^m_{n,k}(γ²)` and their defining property (DLMF §30.8(ii)).
* `exists_isSpheroidalQs_of_le`, `exists_isSpheroidalQs`, `spheroidalQs_spec`: existence of
  `𝖰s^m_n` and its defining property (DLMF 30.5.1).
* `isSpheroidalSolutionReal_spheroidalPs`, `spheroidalPs_neg`, `spheroidalPs_zero_sign`,
  `spheroidalPs_deriv_zero_sign`: the equation, parity 30.4.3 and sign conventions of `𝖯s`.
* `existsUnique_isSpheroidalQsC`, `spheroidalQsC_spec`: existence and uniqueness of `𝑄s^m_n` and
  its defining property (DLMF 30.6.1).
-/

@[expose] public noncomputable section

open Complex Set Filter DLMF.Legendre
open scoped Topology Real Classical

namespace DLMF.Spheroidal

/-- `dif_pos` without the deprecation. -/
private lemma dite_eq_of_pos {c : Prop} [Decidable c] (h : c) {α : Sort*} {t : c → α}
    {e : ¬c → α} : dite c t e = t h := by simp [h]

/-! ### Properties of `𝖯s` used below -/

/-- The reflected factor `(-1)^{n-m} g(-z)` is again the normalized factor. -/
theorem isSpheroidalPsFactor_reflect {n m : ℕ} {γ2 : ℝ} {g : ℂ → ℂ}
    (hg : IsSpheroidalPsFactor n m γ2 g) :
    IsSpheroidalPsFactor n m γ2 (fun z => (-1 : ℂ) ^ (n - m) * g (-z)) := by
  have hd := hg.factor.differentiable
  have hd1 : Differentiable ℂ (deriv g) :=
    fun z => ((hd.analyticAt z).deriv).differentiableAt
  have h1 : ∀ z, HasDerivAt (fun z => (-1 : ℂ) ^ (n - m) * g (-z))
      (-((-1 : ℂ) ^ (n - m) * deriv g (-z))) z := fun z => by
    have := ((hd (-z)).hasDerivAt.comp z (hasDerivAt_neg z)).const_mul ((-1 : ℂ) ^ (n - m))
    simpa using this
  have e1 : deriv (fun z => (-1 : ℂ) ^ (n - m) * g (-z)) =
      fun z => -((-1 : ℂ) ^ (n - m) * deriv g (-z)) := funext fun z => (h1 z).deriv
  have h2 : ∀ z, HasDerivAt (fun z => -((-1 : ℂ) ^ (n - m) * deriv g (-z)))
      ((-1 : ℂ) ^ (n - m) * deriv (deriv g) (-z)) z := fun z => by
    refine ((((hd1 (-z)).hasDerivAt.comp z (hasDerivAt_neg z)).const_mul
      ((-1 : ℂ) ^ (n - m))).neg).congr_deriv ?_
    ring
  have e2 : deriv (deriv (fun z => (-1 : ℂ) ^ (n - m) * g (-z))) =
      fun z => (-1 : ℂ) ^ (n - m) * deriv (deriv g) (-z) := by
    rw [e1]; exact funext fun z => (h2 z).deriv
  have hk : ((-1 : ℂ) ^ (n - m)) = (((-1 : ℝ) ^ (n - m) : ℝ) : ℂ) := by push_cast; rfl
  refine ⟨⟨fun z => (h1 z).differentiableAt,
    fun z => ?_⟩, fun x => ?_, ?_, fun he => ?_, fun ho => ?_⟩
  · rw [e2, e1]
    have h := hg.factor.ode (-z)
    linear_combination (-1 : ℂ) ^ (n - m) * h
  · rw [hk, ← Complex.ofReal_neg, Complex.im_ofReal_mul, hg.real, mul_zero]
  · rw [← hg.normalized]
    have : ∀ x : ℝ, (1 - x ^ 2) ^ m * (((-1 : ℂ) ^ (n - m) * g (-(x : ℂ))).re) ^ 2 =
        (fun x : ℝ => (1 - x ^ 2) ^ m * (g x).re ^ 2) (-x) := by
      intro x
      rw [hk, ← Complex.ofReal_neg, Complex.re_ofReal_mul, mul_pow, ← pow_mul,
        mul_comm (n - m) 2, pow_mul]
      simp
    simp_rw [this]
    rw [intervalIntegral.integral_comp_neg (fun x : ℝ => (1 - x ^ 2) ^ m * (g x).re ^ 2)]
    norm_num
  · rw [neg_zero, hk, Complex.re_ofReal_mul, he.neg_one_pow, one_mul]
    exact hg.sign_even he
  · rw [e1]
    simp only [neg_zero]
    rw [show -((-1 : ℂ) ^ (n - m) * deriv g 0) = (((-((-1 : ℝ) ^ (n - m))) : ℝ) : ℂ) * deriv g 0
      by push_cast; ring, Complex.re_ofReal_mul, ho.neg_one_pow, neg_neg, one_mul]
    exact hg.sign_odd ho

/-- `𝖯s^m_n(0, γ²) = g(0)` for the entire factor `g`. -/
theorem spheroidalPs_zero (n m : ℕ) (γ2 : ℝ) :
    spheroidalPs n m 0 γ2 = (spheroidalPsFactor n m γ2 0).re := by
  simp [spheroidalPs]

/-- `d𝖯s^m_n(x, γ²)/dx` at `x = 0` is `g'(0)` for the entire factor `g` (`(1-x²)^{m/2}` is
stationary at `0`). Proved. -/
theorem hasDerivAt_spheroidalPs_zero {n m : ℕ} (hmn : m ≤ n) (γ2 : ℝ) :
    HasDerivAt (fun x => spheroidalPs n m x γ2) (deriv (spheroidalPsFactor n m γ2) 0).re 0 := by
  have hG := (spheroidalPsFactor_spec hmn γ2).factor.differentiable
  have h2 : HasDerivAt (fun x : ℝ => (spheroidalPsFactor n m γ2 x).re)
      (deriv (spheroidalPsFactor n m γ2) 0).re 0 := by
    have := (hG ((0 : ℝ) : ℂ)).hasDerivAt
    exact this.real_of_complex
  have hb : HasDerivAt (fun x : ℝ => 1 - x ^ 2) (-(2 * (0 : ℝ))) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).pow 2).const_sub 1
  have h1 := hb.rpow_const (p := (m : ℝ) / 2) (Or.inl (by norm_num))
  have := h1.mul h2
  convert this using 1
  · funext x; rfl
  · simp

/-- **Sign convention for `n - m` even** (DLMF §30.4(i)): the sign of `𝖯s^m_n(0, γ²)` is
`(-1)^{(n+m)/2}`. Proved from `existsUnique_isSpheroidalPsFactor`. -/
@[dlmf 30.4.i]
theorem spheroidalPs_zero_sign {n m : ℕ} (hmn : m ≤ n) (γ2 : ℝ) (h : Even (n - m)) :
    0 < (-1 : ℝ) ^ ((n + m) / 2) * spheroidalPs n m 0 γ2 := by
  rw [spheroidalPs_zero]; exact (spheroidalPsFactor_spec hmn γ2).sign_even h

/-- **Sign convention for `n - m` odd** (DLMF §30.4(i)): the sign of `d𝖯s^m_n(x, γ²)/dx|_{x=0}` is
`(-1)^{(n+m-1)/2}`. Proved from `existsUnique_isSpheroidalPsFactor`. -/
@[dlmf 30.4.i]
theorem spheroidalPs_deriv_zero_sign {n m : ℕ} (hmn : m ≤ n) (γ2 : ℝ) (h : Odd (n - m)) :
    0 < (-1 : ℝ) ^ ((n + m - 1) / 2) * deriv (fun x => spheroidalPs n m x γ2) 0 := by
  rw [(hasDerivAt_spheroidalPs_zero hmn γ2).deriv]
  exact (spheroidalPsFactor_spec hmn γ2).sign_odd h

/-- `𝖯s^m_n(x, γ²)` solves 30.2.1 on `(-1, 1)` with `μ = m`, `λ = λ^m_n(γ²)` (DLMF §30.4(i)).
Proved from the admitted 30.3(i) equivalence and the existence theorem. -/
@[dlmf 30.4.i]
theorem isSpheroidalSolutionReal_spheroidalPs {n m : ℕ} (hmn : m ≤ n) (γ2 : ℝ) :
    IsSpheroidalSolutionReal (spheroidalEigenvalue n m γ2) γ2 m
      (fun x => spheroidalPs n m x γ2) := by
  have h := spheroidalPsFactor_spec hmn γ2
  exact (isSpheroidalSolutionReal_iff_isSpheroidalFactor h.factor.differentiable h.real).mpr
    h.factor

/-- **Parity** (DLMF 30.4.3): `𝖯s^m_n(-x, γ²) = (-1)^{n-m} 𝖯s^m_n(x, γ²)`. -/
@[dlmf 30.4.E3]
theorem spheroidalPs_neg {n m : ℕ} (hmn : m ≤ n) (x γ2 : ℝ) :
    spheroidalPs n m (-x) γ2 = (-1) ^ (n - m) * spheroidalPs n m x γ2 := by
  have hg := spheroidalPsFactor_spec hmn γ2
  have hu := (existsUnique_isSpheroidalPsFactor hmn γ2).unique
    (isSpheroidalPsFactor_reflect hg) hg
  have hx := congrFun hu (-(x : ℂ))
  simp only [neg_neg] at hx
  have hk : ((-1 : ℂ) ^ (n - m)) = (((-1 : ℝ) ^ (n - m) : ℝ) : ℂ) := by push_cast; rfl
  simp only [spheroidalPs, neg_sq, Complex.ofReal_neg, ← hx, hk, Complex.re_ofReal_mul]
  ring

/-! ### Solutions of 30.2.1 on `(-1, 1)` -/

private lemma hasDerivAt_artanh' {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt Real.artanh (1 / (1 - x ^ 2)) x := by
  have hev : Real.artanh =ᶠ[𝓝 x] fun y => 1 / 2 * Real.log ((1 + y) / (1 - y)) := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
    exact Real.artanh_eq_half_log (Ioo_subset_Icc_self hy)
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  have h1 : 0 < 1 + x := by linarith [hx.1]
  have h2 : 0 < 1 - x := by linarith [hx.2]
  have := ((((hasDerivAt_id x).const_add 1).div ((hasDerivAt_id x).const_sub 1)
    h2.ne').log (div_pos h1 h2).ne').const_mul (1 / 2)
  simp only [Pi.div_apply, id] at this
  convert this using 1
  rw [show 1 - x ^ 2 = (1 - x) * (1 + x) by ring]
  field_simp
  ring

private lemma artanh_neg' {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    Real.artanh (-x) = -Real.artanh x := by
  rw [← Real.tanh_artanh hx, ← Real.tanh_neg, Real.artanh_tanh, Real.artanh_tanh]

private lemma inv_cosh_artanh_sq {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    (Real.cosh (Real.artanh x) ^ 2)⁻¹ = 1 - x ^ 2 := by
  have h : 0 < 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
  rw [Real.cosh_artanh hx, div_pow, Real.sq_sqrt h.le]
  field_simp


/-- Solutions of 30.2.1 on `(-1, 1)` with prescribed `w(0)`, `w'(0)`, through `x = tanh t`. -/
private lemma exists_isSpheroidalSolutionReal_data (lam γ2 μ a b : ℝ) :
    ∃ f : ℝ → ℝ, IsSpheroidalSolutionReal lam γ2 μ f ∧ f 0 = a ∧ deriv f 0 = b ∧
      (∀ x, x ∉ Ioo (-1 : ℝ) 1 → f x = 0) ∧
      (a = 0 → ∀ x ∈ Ioo (-1 : ℝ) 1, f (-x) = -f x) ∧
      (b = 0 → ∀ x ∈ Ioo (-1 : ℝ) 1, f (-x) = f x) := by
  set s : ℝ → ℝ := fun t => (Real.cosh t ^ 2)⁻¹ with hs
  have hsc : Continuous s :=
    (Real.continuous_cosh.pow 2).inv₀ fun t => (pow_pos (Real.cosh_pos t) 2).ne'
  set q : ℝ → ℝ := fun t => -(lam * s t + γ2 * s t ^ 2 - μ ^ 2) with hq
  have hqc : Continuous q := by simp only [hq]; fun_prop
  have hqe : ∀ t, q (-t) = q t := fun t => by simp [hq, hs, Real.cosh_neg]
  obtain ⟨Y, Y', hY0, hY1, hY⟩ := ODE.exists_linear_ode (E := ℝ) (p := fun _ => (0 : ℝ))
    continuous_const hqc 0 a b
  simp only [zero_mul, zero_add, smul_eq_mul] at hY
  set f : ℝ → ℝ := fun x => if x ∈ Ioo (-1 : ℝ) 1 then Y (Real.artanh x) else 0 with hf
  have hfev : ∀ x ∈ Ioo (-1 : ℝ) 1, f =ᶠ[𝓝 x] fun y => Y (Real.artanh y) := fun x hx => by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
    simp only [hf, hy, ↓reduceIte]
  have hfd : ∀ x ∈ Ioo (-1 : ℝ) 1, HasDerivAt f (Y' (Real.artanh x) / (1 - x ^ 2)) x :=
    fun x hx => by
      have := ((hY (Real.artanh x)).1.comp x (hasDerivAt_artanh' hx))
      refine (this.congr_of_eventuallyEq (hfev x hx)).congr_deriv ?_
      ring
  have hpos : ∀ x ∈ Ioo (-1 : ℝ) 1, 0 < 1 - x ^ 2 := fun x hx => by nlinarith [hx.1, hx.2]
  have hu : ∀ x ∈ Ioo (-1 : ℝ) 1,
      (fun t => (1 - t ^ 2) * deriv f t) =ᶠ[𝓝 x] fun t => Y' (Real.artanh t) := fun x hx => by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
    rw [(hfd y hy).deriv]
    field_simp [(hpos y hy).ne']
  have hf0 : f 0 = a := by simp [hf, Real.artanh_zero, hY0]
  have hd0 : deriv f 0 = b := by
    rw [(hfd 0 (by norm_num)).deriv]; simp [Real.artanh_zero, hY1]
  -- reflection
  have hZ : ∀ t, HasDerivAt (fun t => Y (-t)) (-Y' (-t)) t ∧
      HasDerivAt (fun t => -Y' (-t)) (q t * Y (-t)) t := fun t => by
    constructor
    · simpa [Function.comp_def] using (hY (-t)).1.comp t (hasDerivAt_neg t)
    · have := ((hY (-t)).2.comp t (hasDerivAt_neg t)).fun_neg
      simp only [Function.comp_def] at this
      convert this using 1
      rw [hqe]; ring
  refine ⟨f, ⟨fun x hx => (hfd x hx).differentiableAt, fun x hx => ?_⟩, hf0, hd0,
    fun x hx => by simp only [hf, hx, ↓reduceIte], fun ha x hx => ?_, fun hb x hx => ?_⟩
  · have := ((hY (Real.artanh x)).2.comp x (hasDerivAt_artanh' hx))
    refine (this.congr_of_eventuallyEq (hu x hx)).congr_deriv ?_
    have hfx : f x = Y (Real.artanh x) := by simp only [hf, hx, ↓reduceIte]
    rw [hfx]
    simp only [hq, hs, inv_cosh_artanh_sq hx]
    field_simp [(hpos x hx).ne']
  · have hneg : -x ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hx.2], by linarith [hx.1]⟩
    have hE := ODE.eq_of_linear_ode (t₀ := 0) (p := fun _ => (0 : ℝ)) continuous_const hqc
      (f := fun t => Y (-t)) (f' := fun t => -Y' (-t))
      (g := fun t => -Y t) (g' := fun t => -Y' t)
      (by simpa using hZ)
      (fun t => by
        simp only [smul_eq_mul]
        exact ⟨(hY t).1.fun_neg, by simpa [mul_neg] using (hY t).2.fun_neg⟩)
      (by simp [hY0, ha]) (by simp)
    have := congrFun hE.1 (Real.artanh x)
    simp only [hf, hx, hneg, ite_true, artanh_neg' hx]
    exact this
  · have hneg : -x ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hx.2], by linarith [hx.1]⟩
    have hE := ODE.eq_of_linear_ode (t₀ := 0) (p := fun _ => (0 : ℝ)) continuous_const hqc
      (f := fun t => Y (-t)) (f' := fun t => -Y' (-t)) (g := Y) (g' := Y')
      (by simpa using hZ)
      (fun t => by simpa using hY t)
      (by simp) (by simp [hY1, hb])
    have := congrFun hE.1 (Real.artanh x)
    simp only [hf, hx, hneg, ite_true, artanh_neg' hx]
    exact this


/-- Abel's identity for 30.2.1: `(1-x²)(f g' - f' g)` is constant on `(-1, 1)`. -/
private lemma isSpheroidalSolutionReal_wronskian_const {lam γ2 μ : ℝ} {f g : ℝ → ℝ}
    (hf : IsSpheroidalSolutionReal lam γ2 μ f) (hg : IsSpheroidalSolutionReal lam γ2 μ g)
    {x y : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) (hy : y ∈ Ioo (-1 : ℝ) 1) :
    (1 - x ^ 2) * (f x * deriv g x - deriv f x * g x) =
      (1 - y ^ 2) * (f y * deriv g y - deriv f y * g y) := by
  have hD : ∀ t ∈ Ioo (-1 : ℝ) 1, HasDerivAt
      (fun s => (1 - s ^ 2) * (f s * deriv g s - deriv f s * g s)) 0 t := fun t ht => by
    have h1 := (hf.differentiableAt t ht).hasDerivAt.mul (hg.hasDerivAt t ht)
    have h2 := (hf.hasDerivAt t ht).mul (hg.differentiableAt t ht).hasDerivAt
    convert h1.sub h2 using 1
    · funext s; simp only [Pi.sub_apply, Pi.mul_apply]; ring
    · ring
  exact isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
    (fun t ht => (hD t ht).differentiableAt.differentiableWithinAt)
    (fun t ht => (hD t ht).deriv) hx hy

/-! ### Existence theorems (flagged) -/

/-- **Existence of the recessive coefficients** `a'^m_{n,k}(γ²)` (DLMF §30.8(ii)), for
`m ≤ n`. Flagged existence theorem (admitted): the recurrence 30.8.4 has, as `k → -∞`, a
recessive solution, unique up to a factor fixed by 30.8.10. -/
@[dlmf 30.8.ii]
theorem exists_isSpheroidalCoeffPrime {n m : ℕ} (hmn : m ≤ n) (γ2 : ℝ) :
    ∃ f, IsSpheroidalCoeffPrime n m γ2 f := by
  sorry

/-- **Existence of `𝖰s^m_n`** without the hypothesis on the forward recursion (DLMF §30.5).
Stronger than DLMF: the characterization `IsSpheroidalQs` is satisfiable for all `m ≤ n`. A
solution of 30.2.1 with data of the parity opposite to `𝖯s` at `0` is constructed through
`x = tanh t`, and Abel's identity gives the Wronskian 30.5.4. -/
@[dlmf 30.5.E1]
theorem exists_isSpheroidalQs_of_le {n m : ℕ} (hmn : m ≤ n) (γ2 : ℝ) :
    ∃ f, IsSpheroidalQs n m γ2 f := by
  set P : ℝ → ℝ := fun t => spheroidalPs n m t γ2 with hP
  have hPs : IsSpheroidalSolutionReal (spheroidalEigenvalue n m γ2) γ2 m P :=
    isSpheroidalSolutionReal_spheroidalPs hmn γ2
  set C : ℝ := ((n + m).factorial : ℝ) / (n - m).factorial * spheroidalA n m γ2 *
    spheroidalANeg n m γ2 with hC
  have key : ∀ f : ℝ → ℝ, IsSpheroidalSolutionReal (spheroidalEigenvalue n m γ2) γ2 m f →
      P 0 * deriv f 0 - deriv P 0 * f 0 = C →
      (∀ x, x ∉ Ioo (-1 : ℝ) 1 → f x = 0) →
      (∀ x ∈ Ioo (-1 : ℝ) 1, f (-x) = (-1) ^ (n - m + 1) * f x) →
      IsSpheroidalQs n m γ2 f := by
    intro f hfs h0 hout hpar
    refine ⟨hfs, hpar, fun x hx => ?_, hout⟩
    have h := isSpheroidalSolutionReal_wronskian_const hPs hfs hx (y := 0) (by norm_num)
    have hx2 : 0 < 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
    rw [h0] at h
    have : P x * deriv f x - deriv P x * f x = C / (1 - x ^ 2) := by
      field_simp; linarith
    rw [this, hC]
    field_simp
  have hPe : ∀ x, P (-x) = (-1) ^ (n - m) * P x := fun x => spheroidalPs_neg hmn x γ2
  by_cases he : Even (n - m)
  · have hP0 : P 0 ≠ 0 := by
      have := spheroidalPs_zero_sign hmn γ2 he
      intro h; simp only [hP] at h; rw [h, mul_zero] at this; exact lt_irrefl _ this
    have hPev : (fun x => P (-x)) = P := funext fun x => by rw [hPe, he.neg_one_pow, one_mul]
    have hdP : deriv P 0 = 0 := by
      have := deriv_comp_neg (f := P) (x := 0)
      rw [hPev, neg_zero] at this
      linarith
    obtain ⟨f, hfs, hf0, hfd, hout, hodd, -⟩ :=
      exists_isSpheroidalSolutionReal_data (spheroidalEigenvalue n m γ2) γ2 m 0 (C / P 0)
    refine ⟨f, key f hfs ?_ hout fun x hx => ?_⟩
    · rw [hfd, hdP, hf0]; field_simp; ring
    · rw [hodd rfl x hx, pow_succ, he.neg_one_pow]; ring
  · have ho : Odd (n - m) := Nat.not_even_iff_odd.1 he
    have hdP : deriv P 0 ≠ 0 := by
      have := spheroidalPs_deriv_zero_sign hmn γ2 ho
      intro h; simp only [hP] at h; rw [h, mul_zero] at this; exact lt_irrefl _ this
    have hP0 : P 0 = 0 := by
      have := hPe 0
      rw [neg_zero, ho.neg_one_pow] at this
      linarith
    obtain ⟨f, hfs, hf0, hfd, hout, -, hev⟩ :=
      exists_isSpheroidalSolutionReal_data (spheroidalEigenvalue n m γ2) γ2 m (-C / deriv P 0) 0
    refine ⟨f, key f hfs ?_ hout fun x hx => ?_⟩
    · rw [hf0, hP0]; field_simp; ring
    · rw [hev rfl x hx, pow_succ, ho.neg_one_pow]; ring

/-- **Existence of `𝖰s^m_n`** (DLMF §30.5, §30.8(ii)): for `m ≤ n`, when the forward recursion of
§30.8(ii) does not vanish at `k = -R` (otherwise DLMF states that `𝖰s` does not exist). Flagged
existence theorem, proved by `exists_isSpheroidalQs_of_le`, which does not need the hypothesis;
uniqueness holds by the parity argument. -/
@[dlmf 30.5.E1]
theorem exists_isSpheroidalQs {n m : ℕ} (hmn : m ≤ n) (γ2 : ℝ)
    (hf : spheroidalFwd n m γ2 ((n + m) / 2 - (n - m) / 2 + 1) ≠ 0) :
    ∃ f, IsSpheroidalQs n m γ2 f := by
  have _ := hf
  exact exists_isSpheroidalQs_of_le hmn γ2

/-- **Existence and uniqueness of `𝑄s^m_n`** (DLMF §30.6), under the hypotheses of
`exists_isSpheroidalQs`. Flagged existence theorem (admitted). -/
@[dlmf 30.6.E1]
theorem existsUnique_isSpheroidalQsC {n m : ℕ} (hmn : m ≤ n) (γ2 : ℝ)
    (hf : spheroidalFwd n m γ2 ((n + m) / 2 - (n - m) / 2 + 1) ≠ 0) :
    ∃! F, IsSpheroidalQsC n m γ2 F := by
  sorry

/-- The defining property of `𝖰s^m_n` (DLMF 30.5.1), from `exists_isSpheroidalQs`. -/
theorem spheroidalQs_spec {n m : ℕ} (hmn : m ≤ n) (γ2 : ℝ)
    (hf : spheroidalFwd n m γ2 ((n + m) / 2 - (n - m) / 2 + 1) ≠ 0) :
    IsSpheroidalQs n m γ2 (fun x => spheroidalQs n m x γ2) := by
  have h := exists_isSpheroidalQs hmn γ2 hf
  have he : (fun x => spheroidalQs n m x γ2) = h.choose := by
    funext x; simp only [spheroidalQs, dite_eq_of_pos h]
  rw [he]; exact h.choose_spec

/-- The defining property of `𝑄s^m_n` (DLMF 30.6.1), from `existsUnique_isSpheroidalQsC`. -/
theorem spheroidalQsC_spec {n m : ℕ} (hmn : m ≤ n) (γ2 : ℝ)
    (hf : spheroidalFwd n m γ2 ((n + m) / 2 - (n - m) / 2 + 1) ≠ 0) :
    IsSpheroidalQsC n m γ2 (fun z => spheroidalQsC n m z γ2) := by
  have h := (existsUnique_isSpheroidalQsC hmn γ2 hf).exists
  have he : (fun z => spheroidalQsC n m z γ2) = h.choose := by
    funext z; simp only [spheroidalQsC, dite_eq_of_pos h]
  rw [he]; exact h.choose_spec

/-- The defining property of `a'^m_{n,k}` (DLMF §30.8(ii)), from
`exists_isSpheroidalCoeffPrime`. -/
theorem spheroidalCoeffPrime_spec {n m : ℕ} (hmn : m ≤ n) (γ2 : ℝ) :
    IsSpheroidalCoeffPrime n m γ2 (spheroidalCoeffPrime n m γ2) := by
  have h := exists_isSpheroidalCoeffPrime hmn γ2
  simp only [spheroidalCoeffPrime, dite_eq_of_pos h]
  exact h.choose_spec

end DLMF.Spheroidal
