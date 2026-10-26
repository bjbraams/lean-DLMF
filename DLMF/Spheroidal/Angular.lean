/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Spheroidal.FerrersDefs
public import DLMF.Spheroidal.Equation
public import DLMF.Legendre.Associated
public import DLMF.Legendre.Integrals
public import DLMF.Legendre.SpecialValues
public import DLMF.Legendre.SeriesTools
public import DLMF.Legendre.Integer
public import DLMF.OrthogonalPolynomials.Differential

/-!
# Angular spheroidal wave functions (DLMF §§30.1, 30.4–30.6)

Statement acquisition from NIST DLMF (version 1.2.8), checked 2026-10-26. Admitted statements
are not completed proofs; see `DLMF30Acquisition.md`.

* §30.1: Flammer's normalization 30.1.2 (proved from the definitions);
* §30.4: the normalization and sign conventions (proved from the existence theorem), the
  Legendre limit 30.4.2, the parity 30.4.3 and the number of zeros, the power series 30.4.4
  (proved from the Taylor series of the entire factor) with the recurrence 30.4.5, the
  orthogonality 30.4.6, the `L²` expansion 30.4.7–30.4.9 and the equiconvergence with Ferrers
  expansions;
* §30.5: the second kind: parity 30.5.2 and Wronskian 30.5.4 (proved from the characterization),
  the Legendre limit 30.5.3, the nonvanishing of `A^m_n A^{-m}_n`;
* §30.6: complex argument: analyticity and reality (proved for `𝑃s`), the Legendre limits 30.6.2,
  the Wronskian 30.6.3 and the boundary values 30.6.4–30.6.5.

`spheroidalPs`, `spheroidalQs` follow DLMF 30.4.1, 30.5.4, verified numerically against the
Ferrers series 30.8.1, 30.8.9 (Wronskian 30.5.4 with the extended coefficients of §30.8(ii)) and
SciPy's `pro_ang1`.
-/

@[expose] public noncomputable section

open Complex Set Filter MeasureTheory DLMF.Legendre
open scoped Topology Real Nat

namespace DLMF.Spheroidal

/-! ### Helpers: reflection and Taylor coefficients (proof round P1, agent S30) -/

/-- Iterated derivatives of `z f(z)` for entire `f`. -/
theorem p1s_iteratedDeriv_id_mul {f : ℂ → ℂ} (hf : Differentiable ℂ f) (k : ℕ) (z : ℂ) :
    iteratedDeriv k (fun z => z * f z) z =
      k * iteratedDeriv (k - 1) f z + z * iteratedDeriv k f z := by
  induction k generalizing f z with
  | zero => simp
  | succ k ih =>
    have hf1 : Differentiable ℂ (deriv f) :=
      fun z => ((hf.analyticAt z).deriv).differentiableAt
    have hd : deriv (fun z => z * f z) = fun z => f z + z * deriv f z := by
      funext w
      have h := (hasDerivAt_id' w).mul (hf w).hasDerivAt
      rw [show (fun z => z * f z) = (fun x => x) * f from rfl, h.deriv]; ring
    rw [iteratedDeriv_succ', hd]
    have hc1 : ContDiffAt ℂ k f z := (hf.contDiff (n := k)).contDiffAt
    have hc2 : ContDiffAt ℂ k (fun z => z * deriv f z) z :=
      ((contDiff_id.mul (hf1.contDiff (n := k)))).contDiffAt
    rw [show (fun z => f z + z * deriv f z) = f + (fun z => z * deriv f z) from rfl,
      iteratedDeriv_add hc1 hc2, ih hf1, ← iteratedDeriv_succ', Nat.add_sub_cancel]
    rcases k with _ | k
    · simp
    · rw [Nat.add_sub_cancel, ← iteratedDeriv_succ']
      push_cast; ring

/-- `iteratedDeriv k (z f) 0 = k f^{(k-1)}(0)`. -/
theorem p1s_iteratedDeriv_id_mul_zero {f : ℂ → ℂ} (hf : Differentiable ℂ f) (k : ℕ) :
    iteratedDeriv k (fun z => z * f z) 0 = k * iteratedDeriv (k - 1) f 0 := by
  simp [p1s_iteratedDeriv_id_mul hf]

/-- `iteratedDeriv k (z² f) 0 = k (k-1) f^{(k-2)}(0)`. -/
theorem p1s_iteratedDeriv_sq_mul_zero {f : ℂ → ℂ} (hf : Differentiable ℂ f) (k : ℕ) :
    iteratedDeriv k (fun z => z * (z * f z)) 0 =
      k * (k - 1 : ℕ) * iteratedDeriv (k - 2) f 0 := by
  have h1 := p1s_iteratedDeriv_id_mul_zero (f := fun z => z * f z) (by fun_prop) k
  rw [h1, p1s_iteratedDeriv_id_mul_zero hf]
  rw [show k - 1 - 1 = k - 2 by omega]; ring

/-- Taylor recurrence of a solution of the factor equation:
`a_{k+2} - (k(k-1) + 2(m+1)k - c) a_k - γ² k(k-1) a_{k-2} = 0` with
`c = λ - m(m+1) + γ²`, `a_k = g^{(k)}(0)`. -/
theorem p1s_factor_taylor {m : ℕ} {γ2 lam : ℝ} {g : ℂ → ℂ} (hg : IsSpheroidalFactor m γ2 lam g)
    (k : ℕ) :
    iteratedDeriv (k + 2) g 0 - ((k : ℂ) * (k - 1 : ℕ) + 2 * ((m : ℂ) + 1) * k -
        ((lam : ℂ) - m * ((m : ℂ) + 1) + γ2)) * iteratedDeriv k g 0 -
      γ2 * ((k : ℂ) * (k - 1 : ℕ) * iteratedDeriv (k - 2) g 0) = 0 := by
  have hd := hg.differentiable
  have hd1 : Differentiable ℂ (deriv g) := fun z => ((hd.analyticAt z).deriv).differentiableAt
  have hd2 : Differentiable ℂ (deriv (deriv g)) :=
    fun z => ((hd1.analyticAt z).deriv).differentiableAt
  have hΦ : (fun z => deriv (deriv g) z - z * (z * deriv (deriv g) z) -
      2 * ((m : ℂ) + 1) * (z * deriv g z) +
      ((lam : ℂ) - m * ((m : ℂ) + 1) + γ2) * g z - γ2 * (z * (z * g z))) = fun _ => 0 := by
    funext z; rw [← hg.ode z]; ring
  have h0 := congrArg (fun F => iteratedDeriv k F 0) hΦ
  simp only [iteratedDeriv_const, ite_self] at h0
  rw [show (fun z => deriv (deriv g) z - z * (z * deriv (deriv g) z) -
      2 * ((m : ℂ) + 1) * (z * deriv g z) +
      ((lam : ℂ) - m * ((m : ℂ) + 1) + γ2) * g z - γ2 * (z * (z * g z))) =
      (deriv (deriv g) - (fun z => z * (z * deriv (deriv g) z)) -
        (fun z => (2 * ((m : ℂ) + 1)) * (z * deriv g z)) +
        (fun z => ((lam : ℂ) - m * ((m : ℂ) + 1) + γ2) * g z) -
        (fun z => (γ2 : ℂ) * (z * (z * g z)))) from rfl] at h0
  rw [iteratedDeriv_sub, iteratedDeriv_add, iteratedDeriv_sub, iteratedDeriv_sub,
    iteratedDeriv_const_mul_field, iteratedDeriv_const_mul_field, iteratedDeriv_const_mul_field,
    p1s_iteratedDeriv_sq_mul_zero hd2, p1s_iteratedDeriv_id_mul_zero hd1,
    p1s_iteratedDeriv_sq_mul_zero hd] at h0
  · rw [← iteratedDeriv_succ', ← iteratedDeriv_succ', ← iteratedDeriv_succ'] at h0
    have e1 : (k : ℂ) * iteratedDeriv (k - 1) (deriv g) 0 = k * iteratedDeriv k g 0 := by
      rcases k with _ | k
      · simp
      · simp [← iteratedDeriv_succ']
    have e2 : (k : ℂ) * ((k - 1 : ℕ) : ℂ) * iteratedDeriv (k - 2 + 1) (deriv g) 0 =
        (k : ℂ) * ((k - 1 : ℕ) : ℂ) * iteratedDeriv k g 0 := by
      rcases k with _ | _ | k
      · simp
      · simp
      · rw [show k + 1 + 1 - 2 + 1 = k + 1 by omega, ← iteratedDeriv_succ']
    linear_combination h0 + 2 * ((m : ℂ) + 1) * e1 + e2
  all_goals
    have hc0 : ContDiff ℂ k g := hd.contDiff
    have hc1 : ContDiff ℂ k (deriv g) := hd1.contDiff
    have hc2 : ContDiff ℂ k (deriv (deriv g)) := hd2.contDiff
    apply ContDiff.contDiffAt
    try simp only [Pi.sub_def, Pi.add_def]
    fun_prop

/-- The reflected factor `(-1)^{n-m} g(-z)` is again the normalized factor. -/
theorem p1s_isSpheroidalPsFactor_reflect {n m : ℕ} {γ2 : ℝ} {g : ℂ → ℂ}
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


/-- Iterated derivatives of an entire function real on `ℝ` are real on `ℝ`. -/
theorem p1s_iteratedDeriv_im_eq_zero {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    (hreal : ∀ x : ℝ, (g x).im = 0) (j : ℕ) :
    Differentiable ℂ (iteratedDeriv j g) ∧ ∀ x : ℝ, (iteratedDeriv j g x).im = 0 := by
  induction j with
  | zero => simpa using ⟨hg, hreal⟩
  | succ j ih =>
    rw [iteratedDeriv_succ]
    refine ⟨fun z => ((ih.1.analyticAt z).deriv).differentiableAt, fun x => ?_⟩
    have h1 : HasDerivAt (fun t : ℝ => (iteratedDeriv j g t).im)
        (deriv (iteratedDeriv j g) x).im x := by
      have h := Complex.imCLM.hasFDerivAt.comp_hasDerivAt x ((ih.1 x).hasDerivAt.comp_ofReal)
      simpa only [Function.comp_def, Complex.imCLM_apply] using h
    have h0 : HasDerivAt (fun t : ℝ => (iteratedDeriv j g t).im) 0 x := by
      simp only [ih.2]; exact hasDerivAt_const x 0
    exact h1.unique h0

/-! ### Elementary properties of `𝖯s` (§30.4(i), (ii)) -/

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

/-- **Normalization** (DLMF 30.4.1): `∫_{-1}^1 (𝖯s^m_n(x, γ²))² dx = 2(n+m)!/((2n+1)(n-m)!)`.
Proved from `existsUnique_isSpheroidalPsFactor`. -/
@[dlmf 30.4.E1]
theorem integral_spheroidalPs_sq {n m : ℕ} (hmn : m ≤ n) (γ2 : ℝ) :
    ∫ x in (-1 : ℝ)..1, spheroidalPs n m x γ2 ^ 2 =
      2 / (2 * n + 1) * (((n + m).factorial : ℝ) / (n - m).factorial) := by
  rw [← (spheroidalPsFactor_spec hmn γ2).normalized]
  refine intervalIntegral.integral_congr fun x hx => ?_
  rw [uIcc_of_le (by norm_num)] at hx
  have h0 : 0 ≤ 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
  simp only [spheroidalPs, mul_pow]
  congr 1
  rw [← Real.rpow_mul_natCast h0, ← Real.rpow_natCast (1 - x ^ 2) m]
  congr 1
  push_cast; ring

/-- `𝖯s^m_n(x, γ²)` solves 30.2.1 on `(-1, 1)` with `μ = m`, `λ = λ^m_n(γ²)` (DLMF §30.4(i)).
Proved from the admitted 30.3(i) equivalence and the existence theorem. -/
@[dlmf 30.4.i]
theorem isSpheroidalSolutionReal_spheroidalPs {n m : ℕ} (hmn : m ≤ n) (γ2 : ℝ) :
    IsSpheroidalSolutionReal (spheroidalEigenvalue n m γ2) γ2 m
      (fun x => spheroidalPs n m x γ2) := by
  have h := spheroidalPsFactor_spec hmn γ2
  exact (isSpheroidalSolutionReal_iff_isSpheroidalFactor h.factor.differentiable h.real).mpr
    h.factor

/-! ### The Legendre case `γ = 0` (helpers, proof round P1, agent S30) -/

/-- At `γ = 0` the Gegenbauer polynomial `C_j^{(m+1/2)}` is a nonzero entire factor with
`λ = (m+j)(m+j+1)`. -/
theorem p1s_mem_spheroidalSpectrum_zero (m j : ℕ) :
    ((m : ℝ) + j) * ((m : ℝ) + j + 1) ∈ spheroidalSpectrum m 0 := by
  set lamC : ℂ := (m : ℂ) + 1 / 2
  have hl : -1 / 2 < lamC.re := by
    simp [lamC]; linarith [(by positivity : (0 : ℝ) ≤ m)]
  refine ⟨fun z => DLMF.OrthogonalPolynomials.ultrasphPoly lamC j z, ⟨?_, fun z => ?_⟩, ?_⟩
  · intro z
    exact (DLMF.OrthogonalPolynomials.analyticOnNhd_ultrasphPoly lamC j z
      (mem_univ _)).differentiableAt
  · have h := DLMF.OrthogonalPolynomials.ultrasphPoly_differential_equation hl j z
    simp only [lamC] at h
    push_cast
    linear_combination h
  · intro h0
    have h1 := congrFun h0 1
    simp only [Pi.zero_apply] at h1
    rw [DLMF.OrthogonalPolynomials.ultrasphPoly_at_one hl] at h1
    have hp : DLMF.Hypergeometric.poch (2 * lamC) j ≠ 0 := by
      apply DLMF.Hypergeometric.poch_ne_zero_of_lt
      intro i _ h
      have := congrArg Complex.re h
      simp [lamC] at this
      linarith [(by positivity : (0 : ℝ) ≤ m), (by positivity : (0 : ℝ) ≤ i)]
    have hf : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast j.factorial_ne_zero
    exact hp (by simpa [hf] using h1)

/-- At `γ = 0` every element of the spectrum is `(m+j)(m+j+1)`: otherwise the Taylor
coefficients of a nonzero entire factor would grow like those of `(1-z²)^{-1}`. -/
theorem p1s_spheroidalSpectrum_zero_subset {m : ℕ} {lam : ℝ}
    (h : lam ∈ spheroidalSpectrum m 0) : ∃ j : ℕ, lam = ((m : ℝ) + j) * ((m : ℝ) + j + 1) := by
  obtain ⟨g, hg, hne⟩ := h
  by_contra hcon
  push Not at hcon
  set a : ℕ → ℂ := fun k => iteratedDeriv k g 0
  set c : ℕ → ℝ := fun k => ((m : ℝ) + k) * ((m : ℝ) + k + 1) - lam
  have hc : ∀ k, c k ≠ 0 := fun k h => hcon k (by simp only [c] at h; linarith)
  have hrec : ∀ k, a (k + 2) = (c k : ℂ) * a k := by
    intro k
    have h := p1s_factor_taylor hg k
    have hk : (k : ℂ) * ((k - 1 : ℕ) : ℂ) = (k : ℂ) * ((k : ℂ) - 1) := by
      rcases k with _ | k <;> simp
    simp only [c, a]
    push_cast
    simp only [Complex.ofReal_zero, zero_mul, sub_zero, add_zero] at h
    linear_combination h + iteratedDeriv k g 0 * hk
  -- some coefficient is nonzero
  obtain ⟨k0, hk0⟩ : ∃ k0, a k0 ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hne
    funext z
    have := Complex.hasSum_taylorSeries_of_entire hg.differentiable 0 z
    simp only [a] at hall
    simp only [hall, smul_zero] at this
    exact this.unique hasSum_zero
  have hnz : ∀ i, a (k0 + 2 * i) ≠ 0 := by
    intro i
    induction i with
    | zero => simpa using hk0
    | succ i ih =>
      rw [show k0 + 2 * (i + 1) = k0 + 2 * i + 2 by ring, hrec]
      exact mul_ne_zero (by exact_mod_cast hc _) ih
  -- the Taylor series converges at `z = 2`
  have hs := (Complex.hasSum_taylorSeries_of_entire hg.differentiable 0 2).summable
  have ht := hs.norm.tendsto_atTop_zero
  set b : ℕ → ℝ := fun i => ‖((k0 + 2 * i).factorial : ℂ)⁻¹ • ((2 : ℂ) - 0) ^ (k0 + 2 * i) •
    iteratedDeriv (k0 + 2 * i) g 0‖
  have hb : Tendsto b atTop (𝓝 0) :=
    ht.comp (tendsto_atTop_mono (fun i => by simp only [id]; omega) tendsto_id)
  have hbpos : ∀ i, 0 < b i := by
    intro i
    have := hnz i
    simp only [a] at this
    refine norm_pos_iff.mpr (smul_ne_zero ?_ (smul_ne_zero ?_ this))
    · exact inv_ne_zero (by exact_mod_cast (k0 + 2 * i).factorial_ne_zero)
    · norm_num
  -- eventually the sequence does not decrease
  obtain ⟨I, hI⟩ : ∃ I : ℕ, ∀ i ≥ I, b i ≤ b (i + 1) := by
    refine ⟨Nat.ceil (4 * |lam| + 1), fun i hi => ?_⟩
    set k := k0 + 2 * i
    have hk : 4 * |lam| + 1 ≤ k := by
      have := Nat.le_ceil (4 * |lam| + 1)
      have : (Nat.ceil (4 * |lam| + 1) : ℝ) ≤ i := by exact_mod_cast hi
      simp only [k]; push_cast; linarith [(by positivity : (0 : ℝ) ≤ k0)]
    have hk1 : (1 : ℝ) ≤ k := by linarith [abs_nonneg lam]
    have hratio : ((k : ℝ) + 1) * (k + 2) ≤ 4 * |c k| := by
      have : c k ≥ (k : ℝ) * (k + 1) - |lam| := by
        simp only [c]
        nlinarith [le_abs_self lam, (by positivity : (0 : ℝ) ≤ m)]
      nlinarith [le_abs_self (c k)]
    have e : b (i + 1) = b i * (4 * |c k| / (((k : ℝ) + 1) * (k + 2))) := by
      simp only [b]
      rw [show k0 + 2 * (i + 1) = k + 2 by ring]
      have h2 := hrec k
      simp only [a] at h2
      rw [h2]
      simp only [norm_smul, norm_mul, norm_inv, norm_pow, Complex.norm_natCast,
        Complex.norm_real, Real.norm_eq_abs, sub_zero, Nat.factorial_succ, Nat.cast_mul]
      norm_num
      have hf : (k ! : ℝ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
      field_simp
      ring
    rw [e]
    have : 1 ≤ 4 * |c k| / (((k : ℝ) + 1) * (k + 2)) := by
      rw [le_div_iff₀ (by positivity)]; linarith
    nlinarith [hbpos i]
  have hmono : ∀ i, b I ≤ b (I + i) := by
    intro i
    induction i with
    | zero => simp
    | succ i ih => exact ih.trans (hI _ (by omega))
  have hlim : Tendsto (fun i => b (I + i)) atTop (𝓝 0) :=
    hb.comp (tendsto_atTop_mono (fun i => by simp only [id]; omega) tendsto_id)
  have := ge_of_tendsto hlim (Filter.Eventually.of_forall hmono)
  linarith [hbpos I]

/-- `λ^m_n(0) = n(n+1)` (DLMF 30.3.3); the proof of `spheroidalEigenvalue_zero`. -/
theorem p1s_spheroidalEigenvalue_zero {n m : ℕ} (hmn : m ≤ n) :
    spheroidalEigenvalue n m 0 = (n : ℝ) * (n + 1) := by
  set f : ℕ → ℝ := fun j => ((m : ℝ) + j) * ((m : ℝ) + j + 1)
  have hf : StrictMono f := by
    intro i j hij
    have : (i : ℝ) < j := by exact_mod_cast hij
    simp only [f]
    nlinarith [(by positivity : (0 : ℝ) ≤ m), (by positivity : (0 : ℝ) ≤ i)]
  obtain ⟨hmem, hcard⟩ := spheroidalEigenvalue_spec hmn 0
  obtain ⟨j, hj⟩ := p1s_spheroidalSpectrum_zero_subset hmem
  have hset : spheroidalSpectrum m 0 ∩ Iio (spheroidalEigenvalue n m 0) = f '' Iio j := by
    ext x
    simp only [mem_inter_iff, mem_Iio, mem_image]
    constructor
    · rintro ⟨hx, hlt⟩
      obtain ⟨i, rfl⟩ := p1s_spheroidalSpectrum_zero_subset hx
      exact ⟨i, hf.lt_iff_lt.mp (by rw [hj] at hlt; exact hlt), rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨p1s_mem_spheroidalSpectrum_zero m i, by rw [hj]; exact hf hi⟩
  rw [hset, hf.injective.encard_image, ← Finset.coe_range, Set.encard_coe_eq_coe_finsetCard,
    Finset.card_range] at hcard
  have hjn : j = n - m := by exact_mod_cast hcard
  rw [hj, hjn, Nat.cast_sub hmn]
  ring

/-- The sign of `Γ(1/2 - s)`: `(-1)^s Γ(1/2 - s) > 0`. -/
theorem p1s_neg_one_pow_mul_Gamma_half_sub_pos (s : ℕ) :
    0 < (-1 : ℝ) ^ s * Real.Gamma (1 / 2 - s) := by
  have h := Real.Gamma_mul_Gamma_one_sub (1 / 2 + s)
  rw [show (1 : ℝ) - (1 / 2 + s) = 1 / 2 - s by ring,
    show π * (1 / 2 + (s : ℝ)) = s * π + π / 2 by ring, Real.sin_add_pi_div_two,
    Real.cos_nat_mul_pi] at h
  have hp : 0 < Real.Gamma (1 / 2 + s) := Real.Gamma_pos_of_pos (by positivity)
  have hs : ((-1 : ℝ) ^ s) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
  have : (-1 : ℝ) ^ s * Real.Gamma (1 / 2 - s) = π / Real.Gamma (1 / 2 + s) := by
    rw [eq_div_iff hp.ne']
    have h2 : Real.Gamma (1 / 2 + s) * Real.Gamma (1 / 2 - s) * (-1) ^ s = π := by
      rw [h]; field_simp [show ((-1 : ℝ) ^ s) ≠ 0 by positivity]
    linear_combination h2
  rw [this]; positivity

/-- `dᵐP_n/dzᵐ` is entire. -/
theorem p1s_differentiable_iteratedDeriv_legendrePolyP (n m : ℕ) :
    Differentiable ℂ (iteratedDeriv m (DLMF.OrthogonalPolynomials.legendrePolyP n)) :=
  ((DLMF.Legendre.differentiable_legendrePolyP n).contDiff
    (n := ((m + 1 : ℕ) : WithTop ℕ∞))).differentiable_iteratedDeriv' m

/-- `𝖯^m_n(x) = (1-x²)^{m/2} (-1)^m dᵐP_n(x)/dxᵐ` on `(-1, 1)` (DLMF 14.6.1). -/
theorem p1s_ferrersP_eq_factor (n m : ℕ) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    ferrersP n m x = (((1 - x ^ 2) ^ ((m : ℝ) / 2) : ℝ) : ℂ) *
      ((-1) ^ m * iteratedDeriv m (DLMF.OrthogonalPolynomials.legendrePolyP n) x) := by
  rw [ferrersP_nat (n : ℂ) m hx]
  have : DLMF.Legendre.legendreP (n : ℂ) = DLMF.OrthogonalPolynomials.legendrePolyP n :=
    funext fun z => DLMF.Legendre.legSer_legendreP_nat n z
  rw [this]
  ring

/-- The factor `(-1)^m dᵐP_n/dzᵐ` is real on `ℝ`. -/
theorem p1s_ferrersFactor_real (n m : ℕ) (x : ℝ) :
    ((-1) ^ m * iteratedDeriv m (DLMF.OrthogonalPolynomials.legendrePolyP n) x).im = 0 := by
  have hG : Differentiable ℂ
      (fun z => (-1) ^ m * iteratedDeriv m (DLMF.OrthogonalPolynomials.legendrePolyP n) z) :=
    (differentiable_const _).mul (p1s_differentiable_iteratedDeriv_legendrePolyP n m)
  set G := fun z => (-1) ^ m * iteratedDeriv m (DLMF.OrthogonalPolynomials.legendrePolyP n) z
    with hGdef
  show (G x).im = 0
  have hIoo : ∀ x ∈ Ioo (-1 : ℝ) 1, (G x).im = 0 := by
    intro x hx
    have h1 := ferrersP_real (n : ℝ) (m : ℝ) hx
    simp only [Complex.ofReal_natCast] at h1
    rw [p1s_ferrersP_eq_factor n m hx, Complex.im_ofReal_mul] at h1
    have hpos : 0 < (1 - x ^ 2) ^ ((m : ℝ) / 2) :=
      Real.rpow_pos_of_pos (by nlinarith [hx.1, hx.2]) _
    rcases mul_eq_zero.mp h1 with h | h
    · exact absurd h hpos.ne'
    · exact h
  have hH : Differentiable ℂ (fun z => G z - (starRingEnd ℂ) (G ((starRingEnd ℂ) z))) := by
    intro z
    refine (hG z).sub ?_
    have := (differentiableAt_conj_conj_iff (f := G) (x := z)).mpr (hG _)
    exact this
  have h0 := p1s_eq_zero_of_Ioo hH (fun y hy => by
    simp only [Complex.conj_ofReal]
    rw [sub_eq_zero, eq_comm, Complex.conj_eq_iff_im]
    exact hIoo y hy) x
  simp only [Complex.conj_ofReal, sub_eq_zero] at h0
  exact Complex.conj_eq_iff_im.mp h0.symm

/-- Solutions of 30.2.1 on `(-1, 1)` depend only on the values on `(-1, 1)`. -/
theorem p1s_isSpheroidalSolutionReal_congr {lam γ2 μ : ℝ} {f g : ℝ → ℝ}
    (h : IsSpheroidalSolutionReal lam γ2 μ f) (hfg : ∀ x ∈ Ioo (-1 : ℝ) 1, f x = g x) :
    IsSpheroidalSolutionReal lam γ2 μ g := by
  have hev : ∀ x ∈ Ioo (-1 : ℝ) 1, f =ᶠ[𝓝 x] g := fun x hx =>
    Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hx) hfg
  refine ⟨fun x hx => (h.differentiableAt x hx).congr_of_eventuallyEq (hev x hx).symm,
    fun x hx => ?_⟩
  rw [← hfg x hx]
  refine (h.hasDerivAt x hx).congr_of_eventuallyEq ?_
  filter_upwards [isOpen_Ioo.mem_nhds hx] with t ht
  rw [(hev t ht).deriv_eq]

/-- At `γ = 0`, `(-1)^m dᵐP_n/dzᵐ` is the normalized factor of `𝖯s^m_n`, given
`λ^m_n(0) = n(n+1)`. -/
theorem p1s_isSpheroidalPsFactor_zero {n m : ℕ} (hmn : m ≤ n)
    (hev : spheroidalEigenvalue n m 0 = (n : ℝ) * (n + 1)) :
    IsSpheroidalPsFactor n m 0
      (fun z => (-1) ^ m * iteratedDeriv m (DLMF.OrthogonalPolynomials.legendrePolyP n) z) := by
  set G := fun z => (-1) ^ m * iteratedDeriv m (DLMF.OrthogonalPolynomials.legendrePolyP n) z
    with hGdef
  have hG : Differentiable ℂ G :=
    (differentiable_const _).mul (p1s_differentiable_iteratedDeriv_legendrePolyP n m)
  have hreal : ∀ x : ℝ, (G x).im = 0 := p1s_ferrersFactor_real n m
  have hGre : ∀ x : ℝ, G x = ((G x).re : ℂ) := fun x => Complex.ext (by simp) (by simp [hreal])
  have hFG : ∀ x ∈ Ioo (-1 : ℝ) 1,
      ferrersP n m x = (((1 - x ^ 2) ^ ((m : ℝ) / 2) : ℝ) : ℂ) * G x :=
    fun x hx => p1s_ferrersP_eq_factor n m hx
  have h0 : (0 : ℝ) ∈ Ioo (-1 : ℝ) 1 := by norm_num
  have hG0 : G 0 = ferrersP n m 0 := by
    have := hFG 0 h0; simp at this; simpa using this.symm
  refine ⟨?_, hreal, ?_, fun he => ?_, fun ho => ?_⟩
  · -- the factor equation
    rw [hev]
    refine (isSpheroidalSolutionReal_iff_isSpheroidalFactor hG hreal).mp ?_
    refine p1s_isSpheroidalSolutionReal_congr (isSpheroidalSolutionReal_ferrersP n m) ?_
    intro x hx
    rw [hFG x hx, Complex.re_ofReal_mul]
  · -- the normalization
    have ho := ferrers_orthogonality_6 n m n hmn hmn
    simp only [↓reduceIte] at ho
    have hcongr : (∫ x : ℝ in (-1)..1, 1 * ferrersP n m x * ferrersP n m x) =
        ∫ x : ℝ in (-1)..1, (((1 - x ^ 2) ^ m * (G x).re ^ 2 : ℝ) : ℂ) := by
      refine intervalIntegral.integral_congr_ae ?_
      have : ∀ᵐ t : ℝ ∂volume, t ≠ 1 := by simp [ae_iff]
      filter_upwards [this] with t ht htm
      rw [uIoc_of_le (by norm_num)] at htm
      have htI : t ∈ Ioo (-1 : ℝ) 1 := ⟨htm.1, lt_of_le_of_ne htm.2 ht⟩
      have hw : 0 ≤ 1 - t ^ 2 := by nlinarith [htI.1, htI.2]
      have : ((1 - t ^ 2) ^ ((m : ℝ) / 2)) ^ 2 = (1 - t ^ 2) ^ m := by
        rw [← Real.rpow_mul_natCast hw, ← Real.rpow_natCast (1 - t ^ 2) m]; congr 1; push_cast; ring
      rw [hFG t htI, ← this]
      conv_lhs => rw [hGre t]
      push_cast; ring
    rw [hcongr, intervalIntegral.integral_ofReal] at ho
    have ho' : ((∫ x : ℝ in (-1)..1, (1 - x ^ 2) ^ m * (G x).re ^ 2 : ℝ) : ℂ) =
        (((n + m).factorial : ℝ) / ((n - m).factorial * (n + 1 / 2)) : ℝ) := by
      rw [ho]; push_cast; ring
    rw [Complex.ofReal_inj] at ho'
    rw [ho']
    have : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
    field_simp
  · -- the sign for `n - m` even
    obtain ⟨r, hr⟩ := he
    have hs : n + m = 2 * ((n + m) / 2) := by omega
    set s := (n + m) / 2
    have hz := ferrersP_zero_1 (n : ℂ) (m : ℂ)
    have e1 : ((n : ℂ) - m) / 2 + 1 = (r : ℂ) + 1 := by
      have : (n : ℂ) - m = ((n - m : ℕ) : ℂ) := by push_cast [Nat.cast_sub hmn]; ring
      rw [this, hr]; push_cast; ring
    have e2 : (1 - (n : ℂ) - m) / 2 = ((1 / 2 - s : ℝ) : ℂ) := by
      have : (n : ℂ) + m = ((n + m : ℕ) : ℂ) := by push_cast; ring
      rw [show (1 - (n : ℂ) - m) = 1 - ((n : ℂ) + m) by ring, this, hs]; push_cast; ring
    rw [e1, e2, Complex.Gamma_nat_eq_factorial, Complex.Gamma_ofReal,
      show ((2 : ℂ) ^ (m : ℂ)) = ((2 ^ m : ℝ) : ℂ) by norm_cast] at hz
    rw [hG0, hz]
    have key := p1s_neg_one_pow_mul_Gamma_half_sub_pos s
    rw [show ((2 ^ m : ℝ) : ℂ) * (Real.sqrt π : ℂ) / ((r ! : ℂ) * (Real.Gamma (1 / 2 - s) : ℂ)) =
      ((2 ^ m * Real.sqrt π / (r ! * Real.Gamma (1 / 2 - s)) : ℝ) : ℂ) by push_cast; ring,
      Complex.ofReal_re]
    have hf : (0 : ℝ) < r ! := by exact_mod_cast r.factorial_pos
    set C := Real.Gamma (1 / 2 - (s : ℝ))
    have hg : C ≠ 0 := by
      intro h; rw [h, mul_zero] at key; exact lt_irrefl _ key
    have : (-1 : ℝ) ^ s * (2 ^ m * Real.sqrt π / (r ! * C)) =
        2 ^ m * Real.sqrt π * ((-1) ^ s * C) / (r ! * C ^ 2) := by
      field_simp
    rw [this]
    have : 0 < Real.sqrt π := Real.sqrt_pos.mpr Real.pi_pos
    have : 0 < C ^ 2 := by positivity
    positivity
  · -- the sign for `n - m` odd
    obtain ⟨r, hr⟩ := ho
    have hs : n + m = 2 * ((n + m - 1) / 2) + 1 := by omega
    set s := (n + m - 1) / 2
    -- the derivative of `𝖯^m_n` at `0` is `G'(0)`
    have hw := p1s_hasDerivAt_weight m h0
    simp only [mul_zero, neg_zero, zero_div, zero_mul] at hw
    have hprod := (hw.ofReal_comp).mul ((hG 0).hasDerivAt.comp_ofReal (z := 0))
    have hev' : (fun t : ℝ => ferrersP n m t) =ᶠ[𝓝 0]
        fun t : ℝ => (((1 - t ^ 2) ^ ((m : ℝ) / 2) : ℝ) : ℂ) * G t :=
      Filter.eventually_of_mem (isOpen_Ioo.mem_nhds h0) hFG
    have hd := (ferrersP_zero_2 (n : ℂ) (m : ℂ)).congr_of_eventuallyEq hev'.symm
    have hu := hprod.unique hd
    simp only [Complex.ofReal_zero, zero_mul, zero_add, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, sub_zero, Real.one_rpow, Complex.ofReal_one, one_mul] at hu
    have e1 : ((n : ℂ) - m + 1) / 2 = (r : ℂ) + 1 := by
      have : (n : ℂ) - m = ((n - m : ℕ) : ℂ) := by push_cast [Nat.cast_sub hmn]; ring
      rw [this, hr]; push_cast; ring
    have e2 : -((n : ℂ) + m) / 2 = ((1 / 2 - ((s + 1 : ℕ) : ℝ) : ℝ) : ℂ) := by
      have : (n : ℂ) + m = ((n + m : ℕ) : ℂ) := by push_cast; ring
      rw [this, hs]; push_cast; ring
    rw [e1, e2, Complex.Gamma_nat_eq_factorial, Complex.Gamma_ofReal,
      show ((2 : ℂ) ^ ((m : ℂ) + 1)) = ((2 ^ (m + 1) : ℝ) : ℂ) by norm_cast] at hu
    rw [hu]
    have key := p1s_neg_one_pow_mul_Gamma_half_sub_pos (s + 1)
    set C := Real.Gamma (1 / 2 - ((s + 1 : ℕ) : ℝ))
    rw [show -((2 ^ (m + 1) : ℝ) : ℂ) * (Real.sqrt π : ℂ) / ((r ! : ℂ) * (C : ℂ)) =
      ((-(2 ^ (m + 1)) * Real.sqrt π / (r ! * C)) : ℝ) by push_cast; ring, Complex.ofReal_re]
    have hf : (0 : ℝ) < r ! := by exact_mod_cast r.factorial_pos
    have hg : C ≠ 0 := by
      intro h; rw [h, mul_zero] at key; exact lt_irrefl _ key
    have : (-1 : ℝ) ^ s * (-(2 ^ (m + 1)) * Real.sqrt π / (r ! * C)) =
        2 ^ (m + 1) * Real.sqrt π * ((-1) ^ (s + 1) * C) / (r ! * C ^ 2) := by
      field_simp
      ring
    rw [this]
    have : 0 < Real.sqrt π := Real.sqrt_pos.mpr Real.pi_pos
    have : 0 < C ^ 2 := by positivity
    positivity

/-- **The Legendre limit** (DLMF 30.4.2): `𝖯s^m_n(x, 0) = 𝖯^m_n(x)` on `(-1, 1)`. -/
@[dlmf 30.4.E2]
theorem spheroidalPs_gamma_zero {n m : ℕ} (hmn : m ≤ n) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    (spheroidalPs n m x 0 : ℂ) = ferrersP n m x := by
  have hGf := p1s_isSpheroidalPsFactor_zero hmn (p1s_spheroidalEigenvalue_zero hmn)
  have hu := (existsUnique_isSpheroidalPsFactor hmn 0).unique (spheroidalPsFactor_spec hmn 0) hGf
  have hre := p1s_ferrersFactor_real n m x
  simp only [spheroidalPs]
  rw [hu, p1s_ferrersP_eq_factor n m hx]
  push_cast
  congr 1
  exact Complex.ext (by simp) (by simp [hre])

/-- **Parity** (DLMF 30.4.3): `𝖯s^m_n(-x, γ²) = (-1)^{n-m} 𝖯s^m_n(x, γ²)`. -/
@[dlmf 30.4.E3]
theorem spheroidalPs_neg {n m : ℕ} (hmn : m ≤ n) (x γ2 : ℝ) :
    spheroidalPs n m (-x) γ2 = (-1) ^ (n - m) * spheroidalPs n m x γ2 := by
  have hg := spheroidalPsFactor_spec hmn γ2
  have hu := (existsUnique_isSpheroidalPsFactor hmn γ2).unique
    (p1s_isSpheroidalPsFactor_reflect hg) hg
  have hx := congrFun hu (-(x : ℂ))
  simp only [neg_neg] at hx
  have hk : ((-1 : ℂ) ^ (n - m)) = (((-1 : ℝ) ^ (n - m) : ℝ) : ℂ) := by push_cast; rfl
  simp only [spheroidalPs, neg_sq, Complex.ofReal_neg, ← hx, hk, Complex.re_ofReal_mul]
  ring

/-- **Zeros** (DLMF §30.4(ii)): `𝖯s^m_n(x, γ²)` has exactly `n - m` zeros in `-1 < x < 1`. -/
@[dlmf 30.4.ii]
theorem ncard_zeros_spheroidalPs {n m : ℕ} (hmn : m ≤ n) (γ2 : ℝ) :
    {x ∈ Ioo (-1 : ℝ) 1 | spheroidalPs n m x γ2 = 0}.ncard = n - m := by
  sorry

/-! ### Power series (§30.4(iii)) -/

/-- **The power series** (DLMF 30.4.4): `𝖯s^m_n(x, γ²) = (1-x²)^{m/2} ∑ g_k x^k` for
`-1 ≤ x ≤ 1`, with `g_k = g^{(k)}(0)/k!` the Taylor coefficients of the entire factor (stronger
than DLMF: the series converges for all real `x`, the identity being meaningful on `[-1, 1]`).
Proved from the Taylor series of entire functions. -/
@[dlmf 30.4.E4]
theorem hasSum_spheroidalPs {n m : ℕ} (hmn : m ≤ n) (γ2 x : ℝ) :
    HasSum (fun k => (1 - x ^ 2) ^ ((m : ℝ) / 2) *
        ((iteratedDeriv k (spheroidalPsFactor n m γ2) 0).re / k ! * x ^ k))
      (spheroidalPs n m x γ2) := by
  have hG := (spheroidalPsFactor_spec hmn γ2).factor.differentiable
  have h := Complex.hasSum_taylorSeries_of_entire hG 0 (x : ℂ)
  have hre := Complex.hasSum_re h
  refine HasSum.mul_left _ ?_
  convert hre using 1
  funext k
  simp only [sub_zero, smul_eq_mul]
  rw [show ((x : ℂ) ^ k) = ((x ^ k : ℝ) : ℂ) by push_cast; rfl,
    show ((k ! : ℂ)⁻¹) = (((k ! : ℝ)⁻¹ : ℝ) : ℂ) by push_cast; rfl, ← mul_assoc,
    ← Complex.ofReal_mul, Complex.re_ofReal_mul]
  ring

/-- **The recurrence** (DLMF 30.4.5): the coefficients `g_k` of 30.4.4 satisfy
`α_k g_{k+2} + (β_k - λ^m_n(γ²)) g_k + γ_k g_{k-2} = 0` with `α_k, β_k, γ_k` from 30.3.6 and
`g_{-1} = g_{-2} = 0`, and `g_k = 0` for `k` of the parity opposite to `n - m`. -/
@[dlmf 30.4.E5]
theorem spheroidalPs_coeff_recurrence {n m : ℕ} (hmn : m ≤ n) (γ2 : ℝ) :
    let g : ℕ → ℝ := fun k => (iteratedDeriv k (spheroidalPsFactor n m γ2) 0).re / (k ! : ℝ)
    (∀ k : ℕ, spheroidalCFAlpha m γ2 k * g (k + 2) +
        (spheroidalCFBeta m γ2 k - spheroidalEigenvalue n m γ2) * g k +
          (if 2 ≤ k then spheroidalCFGamma m γ2 k * g (k - 2) else 0) = 0) ∧
      ∀ k : ℕ, (k + (n - m)) % 2 = 1 → g k = 0 := by
  intro g
  have hG := spheroidalPsFactor_spec hmn γ2
  set G := spheroidalPsFactor n m γ2
  have hre : ∀ j, iteratedDeriv j G 0 = ((iteratedDeriv j G 0).re : ℂ) := fun j =>
    Complex.ext (by simp) (by simpa using
      (p1s_iteratedDeriv_im_eq_zero hG.factor.differentiable hG.real j).2 0)
  constructor
  · intro k
    have h := p1s_factor_taylor hG.factor k
    rw [hre (k + 2), hre k, hre (k - 2)] at h
    set a : ℕ → ℝ := fun j => (iteratedDeriv j G 0).re
    have h' : a (k + 2) - ((k : ℝ) * (k - 1 : ℕ) + 2 * ((m : ℝ) + 1) * k -
        (spheroidalEigenvalue n m γ2 - m * ((m : ℝ) + 1) + γ2)) * a k -
        γ2 * ((k : ℝ) * (k - 1 : ℕ) * a (k - 2)) = 0 := by exact_mod_cast h
    simp only [g, spheroidalCFAlpha, spheroidalCFBeta, spheroidalCFGamma]
    change -((k : ℝ) + 1) * ((k : ℝ) + 2) * (a (k + 2) / ((k + 2) ! : ℝ)) +
      (((m : ℝ) + k) * ((m : ℝ) + k + 1) - γ2 - spheroidalEigenvalue n m γ2) * (a k / (k ! : ℝ)) +
      (if 2 ≤ k then γ2 * (a (k - 2) / ((k - 2) ! : ℝ)) else 0) = 0
    have hf2 : ((k + 2) ! : ℝ) = ((k : ℝ) + 2) * ((k : ℝ) + 1) * k ! := by
      push_cast [Nat.factorial_succ]; ring
    rw [hf2]
    rcases k with _ | _ | j
    · norm_num at h' ⊢; field_simp; linear_combination -h'
    · norm_num at h' ⊢; field_simp; linear_combination -h'
    · simp only [show 2 ≤ j + 2 from by omega, ↓reduceIte, Nat.add_sub_cancel] at h' ⊢
      have hf : ((j + 2) ! : ℝ) = ((j : ℝ) + 2) * ((j : ℝ) + 1) * j ! := by
        push_cast [Nat.factorial_succ]; ring
      rw [hf]
      push_cast at h' ⊢
      field_simp
      linear_combination -h'
  · intro k hk
    have hu := (existsUnique_isSpheroidalPsFactor hmn γ2).unique
      (p1s_isSpheroidalPsFactor_reflect hG) hG
    have h1 := congrArg (fun F => iteratedDeriv k F 0) hu
    rw [iteratedDeriv_const_mul_field, iteratedDeriv_comp_neg, neg_zero, smul_eq_mul,
      ← mul_assoc, ← pow_add] at h1
    have hodd : Odd (n - m + k) := Nat.odd_iff.mpr (by omega)
    rw [hodd.neg_one_pow] at h1
    have h0 : iteratedDeriv k G 0 = 0 := by linear_combination -h1 / 2
    show (iteratedDeriv k G 0).re / (k ! : ℝ) = 0
    rw [h0, Complex.zero_re, zero_div]

/-! ### Orthogonality and expansions (§30.4(iv)) -/

/-- The real form along `ℝ` of the factor equation, for a factor real on `ℝ`. -/
theorem p1s_factor_ode_re {m : ℕ} {γ2 lam : ℝ} {g : ℂ → ℂ} (hF : IsSpheroidalFactor m γ2 lam g)
    (hreal : ∀ x : ℝ, (g x).im = 0) (x : ℝ) :
    (1 - x ^ 2) * (deriv (deriv g) x).re - 2 * ((m : ℝ) + 1) * x * (deriv g x).re +
      (lam - m * ((m : ℝ) + 1) + γ2 * (1 - x ^ 2)) * (g x).re = 0 := by
  have hd := hF.differentiable
  have h0 := p1s_iteratedDeriv_im_eq_zero hd hreal
  have e0 : g x = ((g x).re : ℂ) := Complex.ext (by simp) (by simp [hreal])
  have e1 : deriv g x = ((deriv g x).re : ℂ) :=
    Complex.ext (by simp) (by simpa using (h0 1).2 x)
  have e2 : deriv (deriv g) x = ((deriv (deriv g) x).re : ℂ) := by
    have := (h0 2).2 x
    rw [iteratedDeriv_succ, iteratedDeriv_one] at this
    exact Complex.ext (by simp) (by simpa using this)
  have h := hF.ode x
  rw [e0, e1, e2] at h
  exact_mod_cast h

/-- Green's identity for two factors: the derivative of
`(1-x²)^{m+1} (G₁ G₂' - G₂ G₁')` is `(1-x²)^m (λ₁ - λ₂) G₁ G₂`. -/
theorem p1s_hasDerivAt_factor_wronskian {m : ℕ} {γ2 l1 l2 : ℝ} {g1 g2 : ℂ → ℂ}
    (h1 : IsSpheroidalFactor m γ2 l1 g1) (h2 : IsSpheroidalFactor m γ2 l2 g2)
    (r1 : ∀ x : ℝ, (g1 x).im = 0) (r2 : ∀ x : ℝ, (g2 x).im = 0) (x : ℝ) :
    HasDerivAt (fun x : ℝ => (1 - x ^ 2) ^ (m + 1) *
        ((g1 x).re * (deriv g2 x).re - (g2 x).re * (deriv g1 x).re))
      ((1 - x ^ 2) ^ m * (l1 - l2) * (g1 x).re * (g2 x).re) x := by
  have d1 := h1.differentiable
  have d2 := h2.differentiable
  have d1' := p1s_differentiable_deriv d1
  have d2' := p1s_differentiable_deriv d2
  have hq : HasDerivAt (fun t : ℝ => (1 - t ^ 2) ^ (m + 1))
      (((m + 1 : ℕ) : ℝ) * (1 - x ^ 2) ^ m * (-(2 * x))) x := by
    refine (((hasDerivAt_pow 2 x).const_sub 1).pow (m + 1)).congr_deriv ?_
    simp
  have := hq.mul (((p1s_hasDerivAt_re d1 x).mul (p1s_hasDerivAt_re d2' x)).sub
    ((p1s_hasDerivAt_re d2 x).mul (p1s_hasDerivAt_re d1' x)))
  refine this.congr_deriv ?_ |>.congr_of_eventuallyEq ?_
  · have e1 := p1s_factor_ode_re h1 r1 x
    have e2 := p1s_factor_ode_re h2 r2 x
    simp only [Pi.mul_apply, Pi.sub_apply]
    push_cast
    linear_combination (1 - x ^ 2) ^ m * ((g1 x).re * e2 - (g2 x).re * e1)
  · exact Filter.Eventually.of_forall fun t => by simp only [Pi.mul_apply, Pi.sub_apply]


/-- **Orthogonality** (DLMF 30.4.6): `∫_{-1}^1 𝖯s^m_k 𝖯s^m_n dx = 0` for `k ≠ n`; the case
`k = n` is 30.4.1 (`integral_spheroidalPs_sq`). -/
@[dlmf 30.4.E6]
theorem integral_spheroidalPs_mul {k n m : ℕ} (hmk : m ≤ k) (hmn : m ≤ n) (hkn : k ≠ n)
    (γ2 : ℝ) : ∫ x in (-1 : ℝ)..1, spheroidalPs k m x γ2 * spheroidalPs n m x γ2 = 0 := by
  have hk := spheroidalPsFactor_spec hmk γ2
  have hn := spheroidalPsFactor_spec hmn γ2
  have hne : spheroidalEigenvalue k m γ2 ≠ spheroidalEigenvalue n m γ2 := by
    intro he
    have a := (spheroidalEigenvalue_spec hmk γ2).2
    have b := (spheroidalEigenvalue_spec hmn γ2).2
    rw [he, b] at a
    have : n - m = k - m := by exact_mod_cast a
    omega
  set G1 := spheroidalPsFactor k m γ2
  set G2 := spheroidalPsFactor n m γ2
  have hW := p1s_hasDerivAt_factor_wronskian hk.factor hn.factor hk.real hn.real
  have hint : IntervalIntegrable (fun x : ℝ => (1 - x ^ 2) ^ m *
      (spheroidalEigenvalue k m γ2 - spheroidalEigenvalue n m γ2) * (G1 x).re * (G2 x).re)
      volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    have c1 : Continuous fun x : ℝ => (G1 x).re :=
      Complex.continuous_re.comp (hk.factor.differentiable.continuous.comp
        Complex.continuous_ofReal)
    have c2 : Continuous fun x : ℝ => (G2 x).re :=
      Complex.continuous_re.comp (hn.factor.differentiable.continuous.comp
        Complex.continuous_ofReal)
    fun_prop
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hW x) hint
  norm_num at hftc
  have h0 : ∫ x in (-1 : ℝ)..1, (1 - x ^ 2) ^ m * (G1 x).re * (G2 x).re = 0 := by
    have : ∫ x in (-1 : ℝ)..1, (1 - x ^ 2) ^ m *
        (spheroidalEigenvalue k m γ2 - spheroidalEigenvalue n m γ2) * (G1 x).re * (G2 x).re =
        (spheroidalEigenvalue k m γ2 - spheroidalEigenvalue n m γ2) *
          ∫ x in (-1 : ℝ)..1, (1 - x ^ 2) ^ m * (G1 x).re * (G2 x).re := by
      rw [← intervalIntegral.integral_const_mul]
      congr 1; funext x; ring
    rw [this] at hftc
    rcases mul_eq_zero.mp hftc with h | h
    · exact absurd (sub_eq_zero.mp h) hne
    · exact h
  rw [← h0]
  refine intervalIntegral.integral_congr fun x hx => ?_
  rw [uIcc_of_le (by norm_num)] at hx
  have h0 : 0 ≤ 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
  simp only [spheroidalPs]
  rw [show (1 - x ^ 2) ^ m = (1 - x ^ 2) ^ ((m : ℝ) / 2) * (1 - x ^ 2) ^ ((m : ℝ) / 2) by
    rw [← sq, ← Real.rpow_mul_natCast h0, ← Real.rpow_natCast]
    congr 1; push_cast; ring]
  ring

/-- **Orthogonality relation** (DLMF 30.4.6) with the Kronecker delta, from 30.4.1 and the case
`k ≠ n`. -/
@[dlmf 30.4.E6]
theorem integral_spheroidalPs_mul_eq {k n m : ℕ} (hmk : m ≤ k) (hmn : m ≤ n) (γ2 : ℝ) :
    ∫ x in (-1 : ℝ)..1, spheroidalPs k m x γ2 * spheroidalPs n m x γ2 =
      if k = n then 2 / (2 * n + 1) * (((n + m).factorial : ℝ) / (n - m).factorial) else 0 := by
  split_ifs with h
  · subst h; simp_rw [← sq]; exact integral_spheroidalPs_sq hmn γ2
  · exact integral_spheroidalPs_mul hmk hmn h γ2

/-- **Mean-square expansion** (DLMF 30.4.7–30.4.9): for `f` square-integrable on `(-1, 1)`, the
partial sums `∑_{n=m}^N c_n 𝖯s^m_n(x, γ²)` with `c_n` from 30.4.8 converge to `f` in `L²(-1, 1)`.
-/
@[dlmf 30.4.E7, dlmf 30.4.E9]
theorem tendsto_spheroidalExpansion_L2 (m : ℕ) (γ2 : ℝ) {f : ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict (Ioo (-1 : ℝ) 1))) :
    Tendsto (fun N : ℕ => ∫ x in (-1 : ℝ)..1,
        |f x - (∑ n ∈ Finset.Icc m N,
          spheroidalExpansionCoeff m γ2 f n * spheroidalPs n m x γ2)| ^ 2)
      atTop (𝓝 0) := by
  sorry

/-- **Equiconvergence** (DLMF §30.4(iv)): for `f` square-integrable on `(-1, 1)`, the difference
between the partial sums of the expansion 30.4.7 and of the Ferrers expansion
`∑_{n=m}^N d_n 𝖯^m_n(x)`, `d_n = (n+1/2) (n-m)!/(n+m)! ∫_{-1}^1 f 𝖯^m_n`, converges to `0`
uniformly for `-1 ≤ x ≤ 1`. -/
@[dlmf 30.4.iv]
theorem tendstoUniformlyOn_spheroidalExpansion_sub_ferrers (m : ℕ) (γ2 : ℝ) {f : ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict (Ioo (-1 : ℝ) 1))) :
    TendstoUniformlyOn (fun (N : ℕ) (x : ℝ) =>
        ∑ n ∈ Finset.Icc m N, spheroidalExpansionCoeff m γ2 f n * spheroidalPs n m x γ2 -
          ∑ n ∈ Finset.Icc m N, ((n : ℝ) + 1 / 2) * (((n - m).factorial : ℝ) / (n + m).factorial) *
            (∫ t in (-1 : ℝ)..1, f t * (ferrersP n m t).re) * (ferrersP n m x).re)
      (fun _ => 0) atTop (Icc (-1 : ℝ) 1) := by
  sorry

/-! ### Functions of the second kind (§30.5) -/

/-- `𝖰s^m_n(x, γ²)` solves 30.2.1 on `(-1, 1)` with `μ = m`, `λ = λ^m_n(γ²)` (DLMF 30.5.1).
Proved from `exists_isSpheroidalQs`. -/
@[dlmf 30.5.E1]
theorem isSpheroidalSolutionReal_spheroidalQs {n m : ℕ} (hmn : m ≤ n) (γ2 : ℝ)
    (hf : spheroidalFwd n m γ2 ((n + m) / 2 - (n - m) / 2 + 1) ≠ 0) :
    IsSpheroidalSolutionReal (spheroidalEigenvalue n m γ2) γ2 m
      (fun x => spheroidalQs n m x γ2) :=
  (spheroidalQs_spec hmn γ2 hf).ode

/-- **Parity** (DLMF 30.5.2): `𝖰s^m_n(-x, γ²) = (-1)^{n-m+1} 𝖰s^m_n(x, γ²)` on `(-1, 1)`.
Proved from the characterization (`exists_isSpheroidalQs`). -/
@[dlmf 30.5.E2]
theorem spheroidalQs_neg {n m : ℕ} (hmn : m ≤ n) (γ2 : ℝ)
    (hf : spheroidalFwd n m γ2 ((n + m) / 2 - (n - m) / 2 + 1) ≠ 0) {x : ℝ}
    (hx : x ∈ Ioo (-1 : ℝ) 1) :
    spheroidalQs n m (-x) γ2 = (-1) ^ (n - m + 1) * spheroidalQs n m x γ2 :=
  (spheroidalQs_spec hmn γ2 hf).parity x hx

/-- **The Legendre limit** (DLMF 30.5.3): `𝖰s^m_n(x, 0) = 𝖰^m_n(x)` on `(-1, 1)`. -/
@[dlmf 30.5.E3]
theorem spheroidalQs_gamma_zero {n m : ℕ} (hmn : m ≤ n) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    (spheroidalQs n m x 0 : ℂ) = ferrersQ n m x := by
  sorry

/-- **Wronskian** (DLMF 30.5.4): `𝒲{𝖯s^m_n, 𝖰s^m_n} = (n+m)!/((1-x²)(n-m)!) A^m_n A^{-m}_n`.
Proved from the characterization (`exists_isSpheroidalQs`). -/
@[dlmf 30.5.E4]
theorem wronskian_spheroidalPs_spheroidalQs {n m : ℕ} (hmn : m ≤ n) (γ2 : ℝ)
    (hf : spheroidalFwd n m γ2 ((n + m) / 2 - (n - m) / 2 + 1) ≠ 0) {x : ℝ}
    (hx : x ∈ Ioo (-1 : ℝ) 1) :
    spheroidalPs n m x γ2 * deriv (fun t => spheroidalQs n m t γ2) x -
        deriv (fun t => spheroidalPs n m t γ2) x * spheroidalQs n m x γ2 =
      ((n + m).factorial : ℝ) / ((1 - x ^ 2) * (n - m).factorial) *
        spheroidalA n m γ2 * spheroidalANeg n m γ2 :=
  (spheroidalQs_spec hmn γ2 hf).wronskian x hx

/-- **Nonvanishing** (DLMF 30.5.4, 30.11.4): `A^m_n(γ²) A^{-m}_n(γ²) ≠ 0` (when `𝖰s` exists). -/
@[dlmf 30.5.E4, dlmf 30.11.E4]
theorem spheroidalA_mul_spheroidalANeg_ne_zero {n m : ℕ} (hmn : m ≤ n) (γ2 : ℝ)
    (hf : spheroidalFwd n m γ2 ((n + m) / 2 - (n - m) / 2 + 1) ≠ 0) :
    spheroidalA n m γ2 * spheroidalANeg n m γ2 ≠ 0 := by
  sorry

/-! ### Functions of complex argument (§30.6) -/

/-- **`𝑃s^m_n(z, γ²)` is analytic on `ℂ ∖ (-∞, 1]`** (DLMF 30.6.1). Proved. -/
@[dlmf 30.6.E1]
theorem differentiableOn_spheroidalPsC {n m : ℕ} (hmn : m ≤ n) (γ2 : ℝ) :
    DifferentiableOn ℂ (fun z => spheroidalPsC n m z γ2) spheroidalCutPlane := by
  intro z hz
  have hz1 : z - 1 ∈ slitPlane := hz
  have hz2 : z + 1 ∈ slitPlane := by
    rw [mem_slitPlane_iff] at hz1 ⊢
    rcases hz1 with h | h
    · left; simp at h ⊢; linarith
    · right; simpa using h
  have hG := (spheroidalPsFactor_spec hmn γ2).factor.differentiable
  refine DifferentiableAt.differentiableWithinAt ?_
  unfold spheroidalPsC
  refine (((differentiableAt_const _).mul ?_).mul ?_).mul (hG z)
  · exact (differentiableAt_id.sub_const 1).cpow_const (by simpa using hz1)
  · exact (differentiableAt_id.add_const 1).cpow_const (by simpa using hz2)

/-- **`𝑃s^m_n(z, γ²)` is real on `(1, ∞)`** (DLMF 30.6.1). Proved. -/
@[dlmf 30.6.E1]
theorem spheroidalPsC_im_eq_zero {n m : ℕ} (hmn : m ≤ n) (γ2 : ℝ) {x : ℝ} (hx : 1 < x) :
    (spheroidalPsC n m x γ2).im = 0 := by
  have hreal := (spheroidalPsFactor_spec hmn γ2).real x
  have hG : spheroidalPsFactor n m γ2 x = ((spheroidalPsFactor n m γ2 x).re : ℂ) :=
    Complex.ext (by simp) (by simp [hreal])
  have h1 : ((x : ℂ) - 1) ^ ((m : ℂ) / 2) = (((x - 1) ^ ((m : ℝ) / 2) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow (by linarith)]; push_cast; rfl
  have h2 : ((x : ℂ) + 1) ^ ((m : ℂ) / 2) = (((x + 1) ^ ((m : ℝ) / 2) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow (by linarith)]; push_cast; rfl
  rw [spheroidalPsC, h1, h2, hG]
  have : ((-1 : ℂ) ^ m) = (((-1 : ℝ) ^ m : ℝ) : ℂ) := by push_cast; rfl
  rw [this]
  simp only [← Complex.ofReal_mul, Complex.ofReal_im]

/-- `𝑃s^m_n(z, γ²)` solves 30.2.1 on `ℂ ∖ (-∞, 1]` with `μ = m`, `λ = λ^m_n(γ²)` (DLMF 30.6.1). -/
@[dlmf 30.6.E1]
theorem isSpheroidalSolutionOn_spheroidalPsC {n m : ℕ} (hmn : m ≤ n) (γ2 : ℝ) :
    IsSpheroidalSolutionOn (spheroidalEigenvalue n m γ2) γ2 m spheroidalCutPlane
      (fun z => spheroidalPsC n m z γ2) := by
  have hG := spheroidalPsFactor_spec hmn γ2
  have hopen : IsOpen spheroidalCutPlane :=
    isOpen_slitPlane.preimage (continuous_id.sub continuous_const)
  have hmem : ∀ z ∈ spheroidalCutPlane, z - 1 ∈ slitPlane ∧ z + 1 ∈ slitPlane := by
    intro z hz
    have hz1 : z - 1 ∈ slitPlane := hz
    refine ⟨hz1, ?_⟩
    rw [mem_slitPlane_iff] at hz1 ⊢
    rcases hz1 with h | h
    · left; simp at h ⊢; linarith
    · right; simpa using h
  have hU1 : ∀ z ∈ spheroidalCutPlane, 1 - z ^ 2 ≠ 0 := by
    intro z hz
    have h1 := slitPlane_ne_zero (hmem z hz).1
    have h2 := slitPlane_ne_zero (hmem z hz).2
    rw [show 1 - z ^ 2 = -((z - 1) * (z + 1)) by ring]
    exact neg_ne_zero.mpr (mul_ne_zero h1 h2)
  refine p1s_isSpheroidalSolutionOn_mul_factor hG.factor hopen hU1
    (h := fun z => (-1) ^ m * (z - 1) ^ ((m : ℂ) / 2) * (z + 1) ^ ((m : ℂ) / 2)) ?_
  intro z hz
  obtain ⟨h1, h2⟩ := hmem z hz
  have h1' := slitPlane_ne_zero h1
  have h2' := slitPlane_ne_zero h2
  have d1 := ((hasDerivAt_id z).sub_const 1).cpow_const (c := (m : ℂ) / 2) h1
  have d2 := ((hasDerivAt_id z).add_const 1).cpow_const (c := (m : ℂ) / 2) h2
  refine ((d1.mul d2).const_mul ((-1 : ℂ) ^ m)).congr_of_eventuallyEq ?_ |>.congr_deriv ?_
  · exact Filter.Eventually.of_forall fun w => by simp [mul_assoc]
  · simp only [id]
    rw [Complex.cpow_sub _ _ h1', Complex.cpow_sub _ _ h2', Complex.cpow_one, Complex.cpow_one]
    have h3 := hU1 z hz
    field_simp
    ring

/-- `𝑄s^m_n(z, γ²)` solves 30.2.1 on `ℂ ∖ (-∞, 1]` (DLMF 30.6.1). Proved from
`existsUnique_isSpheroidalQsC`. -/
@[dlmf 30.6.E1]
theorem isSpheroidalSolutionOn_spheroidalQsC {n m : ℕ} (hmn : m ≤ n) (γ2 : ℝ)
    (hf : spheroidalFwd n m γ2 ((n + m) / 2 - (n - m) / 2 + 1) ≠ 0) :
    IsSpheroidalSolutionOn (spheroidalEigenvalue n m γ2) γ2 m spheroidalCutPlane
      (fun z => spheroidalQsC n m z γ2) :=
  (spheroidalQsC_spec hmn γ2 hf).ode

/-- **`𝑄s^m_n(z, γ²)` is real on `(1, ∞)`** (DLMF 30.6.1). -/
@[dlmf 30.6.E1]
theorem spheroidalQsC_im_eq_zero {n m : ℕ} (hmn : m ≤ n) (γ2 : ℝ)
    (hf : spheroidalFwd n m γ2 ((n + m) / 2 - (n - m) / 2 + 1) ≠ 0) {x : ℝ} (hx : 1 < x) :
    (spheroidalQsC n m x γ2).im = 0 := by
  sorry

/-- **The Legendre limits** (DLMF 30.6.2): `𝑃s^m_n(z, 0) = P^m_n(z)` and
`𝑄s^m_n(z, 0) = Q^m_n(z)` on `ℂ ∖ (-∞, 1]`. -/
@[dlmf 30.6.E2]
theorem spheroidalPsC_gamma_zero {n m : ℕ} (hmn : m ≤ n) {z : ℂ} (hz : z ∈ spheroidalCutPlane) :
    spheroidalPsC n m z 0 = associatedP n m z ∧ spheroidalQsC n m z 0 = associatedQ n m z := by
  sorry

/-- **Wronskian** (DLMF 30.6.3):
`𝒲{𝑃s^m_n, 𝑄s^m_n} = (-1)^m (n+m)!/((1-z²)(n-m)!) A^m_n A^{-m}_n` on `ℂ ∖ (-∞, 1]`. -/
@[dlmf 30.6.E3]
theorem wronskian_spheroidalPsC_spheroidalQsC {n m : ℕ} (hmn : m ≤ n) (γ2 : ℝ)
    (hf : spheroidalFwd n m γ2 ((n + m) / 2 - (n - m) / 2 + 1) ≠ 0) {z : ℂ}
    (hz : z ∈ spheroidalCutPlane) :
    spheroidalPsC n m z γ2 * deriv (fun t => spheroidalQsC n m t γ2) z -
        deriv (fun t => spheroidalPsC n m t γ2) z * spheroidalQsC n m z γ2 =
      (-1) ^ m * ((n + m).factorial : ℂ) / ((1 - z ^ 2) * (n - m).factorial) *
        spheroidalA n m γ2 * spheroidalANeg n m γ2 := by
  sorry

/-- Boundary limits of `𝑃s` along a filter on `ε` approaching `0`, given the limit of
`log(x + εi - 1)`. -/
theorem p1s_tendsto_spheroidalPsC_aux {n m : ℕ} (hmn : m ≤ n) (γ2 : ℝ) {x : ℝ}
    (hx : x ∈ Ioo (-1 : ℝ) 1) {L : Filter ℝ} (hL : L ≤ 𝓝 0) {θ : ℂ}
    (hlog : Tendsto (fun ε : ℝ => Complex.log (x + ε * I - 1)) L
      (𝓝 ((Real.log (1 - x) : ℂ) + θ)))
    (hne : ∀ᶠ ε : ℝ in L, (x : ℂ) + (ε : ℂ) * I - 1 ≠ 0) :
    Tendsto (fun ε : ℝ => spheroidalPsC n m (x + ε * I) γ2) L
      (𝓝 ((-1) ^ m * Complex.exp (θ * ((m : ℂ) / 2)) * spheroidalPs n m x γ2)) := by
  have hG := spheroidalPsFactor_spec hmn γ2
  have hpath : Tendsto (fun ε : ℝ => (x : ℂ) + ε * I) L (𝓝 (x : ℂ)) := by
    refine Tendsto.mono_left ?_ hL
    have : Continuous fun ε : ℝ => (x : ℂ) + ε * I := by fun_prop
    simpa using this.tendsto 0
  have h1 : Tendsto (fun ε : ℝ => ((x : ℂ) + ε * I - 1) ^ ((m : ℂ) / 2)) L
      (𝓝 (Complex.exp (((Real.log (1 - x) : ℂ) + θ) * ((m : ℂ) / 2)))) := by
    have := (Complex.continuous_exp.tendsto _).comp (hlog.mul_const ((m : ℂ) / 2))
    refine this.congr' ?_
    filter_upwards [hne] with ε hε
    simp [Complex.cpow_def_of_ne_zero hε]
  have hx1 : ((x : ℂ) + 1) ∈ slitPlane := by
    rw [mem_slitPlane_iff]; left; simp; linarith [hx.1]
  have h2 : Tendsto (fun ε : ℝ => ((x : ℂ) + ε * I + 1) ^ ((m : ℂ) / 2)) L
      (𝓝 (((x : ℂ) + 1) ^ ((m : ℂ) / 2))) :=
    (continuousAt_cpow_const hx1).tendsto.comp (hpath.add_const 1)
  have h3 : Tendsto (fun ε : ℝ => spheroidalPsFactor n m γ2 ((x : ℂ) + ε * I)) L
      (𝓝 (spheroidalPsFactor n m γ2 x)) :=
    (hG.factor.differentiable.continuous.tendsto _).comp hpath
  have := ((tendsto_const_nhds (x := ((-1 : ℂ) ^ m))).mul h1).mul h2 |>.mul h3
  have hfun : (fun ε : ℝ => spheroidalPsC n m (x + ε * I) γ2) = fun ε : ℝ =>
      (-1) ^ m * ((x : ℂ) + ε * I - 1) ^ ((m : ℂ) / 2) * ((x : ℂ) + ε * I + 1) ^ ((m : ℂ) / 2) *
        spheroidalPsFactor n m γ2 ((x : ℂ) + ε * I) := rfl
  rw [hfun]
  convert this using 2
  have hpos1 : 0 < 1 - x := by linarith [hx.2]
  have hpos2 : 0 < 1 + x := by linarith [hx.1]
  have e1 : Complex.exp (((Real.log (1 - x) : ℂ) + θ) * ((m : ℂ) / 2)) =
      (((1 - x) ^ ((m : ℝ) / 2) : ℝ) : ℂ) * Complex.exp (θ * ((m : ℂ) / 2)) := by
    rw [add_mul, Complex.exp_add, Real.rpow_def_of_pos hpos1]
    push_cast; ring_nf
  have e2 : ((x : ℂ) + 1) ^ ((m : ℂ) / 2) = (((1 + x) ^ ((m : ℝ) / 2) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow hpos2.le]; push_cast; ring_nf
  have e3 : spheroidalPsFactor n m γ2 x = ((spheroidalPsFactor n m γ2 x).re : ℂ) :=
    Complex.ext (by simp) (by simp [hG.real])
  rw [e1, e2, e3]
  simp only [spheroidalPs]
  rw [show 1 - x ^ 2 = (1 - x) * (1 + x) by ring, Real.mul_rpow hpos1.le hpos2.le]
  push_cast; ring

/-- **Boundary values of `𝑃s`** (DLMF 30.6.4): `𝑃s^m_n(x ± i0, γ²) = (∓i)^m 𝖯s^m_n(x, γ²)` for
`-1 < x < 1`. -/
@[dlmf 30.6.E4]
theorem tendsto_spheroidalPsC_boundary {n m : ℕ} (hmn : m ≤ n) (γ2 : ℝ) {x : ℝ}
    (hx : x ∈ Ioo (-1 : ℝ) 1) :
    Tendsto (fun ε : ℝ => spheroidalPsC n m (x + ε * I) γ2) (𝓝[>] 0)
        (𝓝 ((-I) ^ m * spheroidalPs n m x γ2)) ∧
      Tendsto (fun ε : ℝ => spheroidalPsC n m (x + ε * I) γ2) (𝓝[<] 0)
        (𝓝 (I ^ m * spheroidalPs n m x γ2)) := by
  have hc_re : ((x : ℂ) - 1).re < 0 := by simp; linarith [hx.2]
  have hc_im : ((x : ℂ) - 1).im = 0 := by simp
  have hnorm : ‖(x : ℂ) - 1‖ = 1 - x := by
    rw [show (x : ℂ) - 1 = ((x - 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_neg (by linarith [hx.2])]
    ring
  have hpath : Continuous fun ε : ℝ => (x : ℂ) + ε * I - 1 := by fun_prop
  constructor
  · have hlog := (Complex.tendsto_log_nhdsWithin_im_nonneg_of_re_neg_of_im_zero hc_re hc_im).comp
      (f := fun ε : ℝ => (x : ℂ) + ε * I - 1) (x := 𝓝[>] 0) (by
        refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
        · simpa using (hpath.tendsto 0).mono_left nhdsWithin_le_nhds
        · filter_upwards [self_mem_nhdsWithin] with ε hε
          simpa using le_of_lt hε)
    rw [hnorm] at hlog
    have hne : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), (x : ℂ) + (ε : ℂ) * I - 1 ≠ 0 := by
      filter_upwards [self_mem_nhdsWithin] with ε hε h
      have := congrArg Complex.im h; simp at this; exact (ne_of_gt hε) this
    have := p1s_tendsto_spheroidalPsC_aux hmn γ2 hx nhdsWithin_le_nhds hlog hne
    convert this using 2
    rw [show (π : ℂ) * I * ((m : ℂ) / 2) = m * (π / 2 * I) by ring, Complex.exp_nat_mul,
      Complex.exp_pi_div_two_mul_I, ← mul_pow]
    ring_nf
  · have hlog := (Complex.tendsto_log_nhdsWithin_im_neg_of_re_neg_of_im_zero hc_re hc_im).comp
      (f := fun ε : ℝ => (x : ℂ) + ε * I - 1) (x := 𝓝[<] 0) (by
        refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
        · simpa using (hpath.tendsto 0).mono_left nhdsWithin_le_nhds
        · filter_upwards [self_mem_nhdsWithin] with ε hε
          simpa using hε)
    rw [hnorm, sub_eq_add_neg] at hlog
    have hne : ∀ᶠ ε : ℝ in 𝓝[<] (0 : ℝ), (x : ℂ) + (ε : ℂ) * I - 1 ≠ 0 := by
      filter_upwards [self_mem_nhdsWithin] with ε hε h
      have := congrArg Complex.im h; simp at this; exact (ne_of_lt hε) this
    have := p1s_tendsto_spheroidalPsC_aux hmn γ2 hx nhdsWithin_le_nhds hlog hne
    convert this using 2
    rw [show -((π : ℂ) * I) * ((m : ℂ) / 2) = m * (-(π / 2 * I)) by ring, Complex.exp_nat_mul,
      Complex.exp_neg, Complex.exp_pi_div_two_mul_I, ← mul_pow]
    rw [inv_I]
    ring_nf

/-- **Boundary values of `𝑄s` from above** (DLMF 30.6.5, upper signs):
`𝑄s^m_n(x + i0, γ²) = (-i)^m (𝖰s^m_n(x, γ²) - (iπ/2) 𝖯s^m_n(x, γ²))`. Proved from the
characterization (`existsUnique_isSpheroidalQsC`). -/
@[dlmf 30.6.E5]
theorem tendsto_spheroidalQsC_boundary_upper {n m : ℕ} (hmn : m ≤ n) (γ2 : ℝ)
    (hf : spheroidalFwd n m γ2 ((n + m) / 2 - (n - m) / 2 + 1) ≠ 0) {x : ℝ}
    (hx : x ∈ Ioo (-1 : ℝ) 1) :
    Tendsto (fun ε : ℝ => spheroidalQsC n m (x + ε * I) γ2) (𝓝[>] 0)
      (𝓝 ((-I) ^ m * (spheroidalQs n m x γ2 - I * π / 2 * spheroidalPs n m x γ2))) :=
  (spheroidalQsC_spec hmn γ2 hf).boundary x hx

/-- **Boundary values of `𝑄s` from below** (DLMF 30.6.5, lower signs):
`𝑄s^m_n(x - i0, γ²) = i^m (𝖰s^m_n(x, γ²) + (iπ/2) 𝖯s^m_n(x, γ²))`. -/
@[dlmf 30.6.E5]
theorem tendsto_spheroidalQsC_boundary_lower {n m : ℕ} (hmn : m ≤ n) (γ2 : ℝ)
    (hf : spheroidalFwd n m γ2 ((n + m) / 2 - (n - m) / 2 + 1) ≠ 0) {x : ℝ}
    (hx : x ∈ Ioo (-1 : ℝ) 1) :
    Tendsto (fun ε : ℝ => spheroidalQsC n m (x + ε * I) γ2) (𝓝[<] 0)
      (𝓝 (I ^ m * (spheroidalQs n m x γ2 + I * π / 2 * spheroidalPs n m x γ2))) := by
  sorry

/-! ### Flammer's normalization (§30.1) -/

/-- **Flammer's normalization, `n - m` even** (DLMF 30.1.2):
`S^{(1)}_{mn}(γ, 0) = (-1)^m 𝖯^m_n(0)`. Proved from the sign convention of §30.4(i). -/
@[dlmf 30.1.E2]
theorem flammerS1_zero {n m : ℕ} (hmn : m ≤ n) (γ2 : ℝ) (h : Even (n - m)) :
    flammerS1 n m γ2 0 = (-1) ^ m * (ferrersP n m 0).re := by
  have hne : spheroidalPs n m 0 γ2 ≠ 0 := by
    intro h0
    have := spheroidalPs_zero_sign hmn γ2 h
    rw [h0, mul_zero] at this
    exact lt_irrefl _ this
  simp only [flammerS1, flammerD, h, ite_true]
  field_simp

/-- **Flammer's normalization, `n - m` odd** (DLMF 30.1.2):
`dS^{(1)}_{mn}(γ, x)/dx|_{x=0} = (-1)^m d𝖯^m_n(x)/dx|_{x=0}`. Proved from the sign convention of
§30.4(i). -/
@[dlmf 30.1.E2]
theorem flammerS1_deriv_zero {n m : ℕ} (hmn : m ≤ n) (γ2 : ℝ) (h : Odd (n - m)) :
    deriv (fun x => flammerS1 n m γ2 x) 0 =
      (-1) ^ m * deriv (fun x : ℝ => (ferrersP n m x).re) 0 := by
  have hne : deriv (fun x => spheroidalPs n m x γ2) 0 ≠ 0 := by
    intro h0
    have := spheroidalPs_deriv_zero_sign hmn γ2 h
    rw [h0, mul_zero] at this
    exact lt_irrefl _ this
  have hodd : ¬ Even (n - m) := Nat.not_even_iff_odd.mpr h
  simp only [flammerS1]
  rw [deriv_const_mul_field']
  simp only [flammerD, hodd, ite_false]
  field_simp

end DLMF.Spheroidal
