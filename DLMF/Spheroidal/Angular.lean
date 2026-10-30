/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Legendre.Associated
public import DLMF.Legendre.Integrals
public import DLMF.Legendre.SeriesTools
public import DLMF.Legendre.SpecialValues
public import DLMF.Spheroidal.Equation
public import DLMF.Spheroidal.Existence
public import DLMF.Spheroidal.FerrersProperties
public import DLMF.Spheroidal.P2yFerrersTools

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
lemma p1s_iteratedDeriv_id_mul {f : ℂ → ℂ} (hf : Differentiable ℂ f) (k : ℕ) (z : ℂ) :
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
lemma p1s_iteratedDeriv_id_mul_zero {f : ℂ → ℂ} (hf : Differentiable ℂ f) (k : ℕ) :
    iteratedDeriv k (fun z => z * f z) 0 = k * iteratedDeriv (k - 1) f 0 := by
  simp [p1s_iteratedDeriv_id_mul hf]

/-- `iteratedDeriv k (z² f) 0 = k (k-1) f^{(k-2)}(0)`. -/
lemma p1s_iteratedDeriv_sq_mul_zero {f : ℂ → ℂ} (hf : Differentiable ℂ f) (k : ℕ) :
    iteratedDeriv k (fun z => z * (z * f z)) 0 =
      k * (k - 1 : ℕ) * iteratedDeriv (k - 2) f 0 := by
  have h1 := p1s_iteratedDeriv_id_mul_zero (f := fun z => z * f z) (by fun_prop) k
  rw [h1, p1s_iteratedDeriv_id_mul_zero hf]
  rw [show k - 1 - 1 = k - 2 by omega]; ring

/-- Taylor recurrence of a solution of the factor equation:
`a_{k+2} - (k(k-1) + 2(m+1)k - c) a_k - γ² k(k-1) a_{k-2} = 0` with
`c = λ - m(m+1) + γ²`, `a_k = g^{(k)}(0)`. -/
lemma p1s_factor_taylor {m : ℕ} {γ2 lam : ℝ} {g : ℂ → ℂ} (hg : IsSpheroidalFactor m γ2 lam g)
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
lemma p1s_iteratedDeriv_im_eq_zero {g : ℂ → ℂ} (hg : Differentiable ℂ g)
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
lemma p1s_mem_spheroidalSpectrum_zero (m j : ℕ) :
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
lemma p1s_spheroidalSpectrum_zero_subset {m : ℕ} {lam : ℝ}
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
lemma p1s_neg_one_pow_mul_Gamma_half_sub_pos (s : ℕ) :
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
lemma p1s_differentiable_iteratedDeriv_legendrePolyP (n m : ℕ) :
    Differentiable ℂ (iteratedDeriv m (DLMF.OrthogonalPolynomials.legendrePolyP n)) :=
  ((DLMF.Legendre.differentiable_legendrePolyP n).contDiff
    (n := ((m + 1 : ℕ) : WithTop ℕ∞))).differentiable_iteratedDeriv' m

/-- `𝖯^m_n(x) = (1-x²)^{m/2} (-1)^m dᵐP_n(x)/dxᵐ` on `(-1, 1)` (DLMF 14.6.1). -/
lemma p1s_ferrersP_eq_factor (n m : ℕ) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    ferrersP n m x = (((1 - x ^ 2) ^ ((m : ℝ) / 2) : ℝ) : ℂ) *
      ((-1) ^ m * iteratedDeriv m (DLMF.OrthogonalPolynomials.legendrePolyP n) x) := by
  rw [ferrersP_nat (n : ℂ) m hx]
  have : DLMF.Legendre.legendreP (n : ℂ) = DLMF.OrthogonalPolynomials.legendrePolyP n :=
    funext fun z => DLMF.Legendre.legSer_legendreP_nat n z
  rw [this]
  ring

/-- The factor `(-1)^m dᵐP_n/dzᵐ` is real on `ℝ`. -/
lemma p1s_ferrersFactor_real (n m : ℕ) (x : ℝ) :
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
lemma p1s_isSpheroidalSolutionReal_congr {lam γ2 μ : ℝ} {f g : ℝ → ℝ}
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
lemma p1s_isSpheroidalPsFactor_zero {n m : ℕ} (hmn : m ≤ n)
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
lemma p1s_factor_ode_re {m : ℕ} {γ2 lam : ℝ} {g : ℂ → ℂ} (hF : IsSpheroidalFactor m γ2 lam g)
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
lemma p1s_hasDerivAt_factor_wronskian {m : ℕ} {γ2 l1 l2 : ℝ} {g1 g2 : ℂ → ℂ}
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

/-! #### Proof of the Legendre limit 30.5.3 -/

/-- `𝖯^m_N(x)` is real for `-1 < x < 1`. -/
lemma p2y_ferrersP_im (N m : ℕ) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) : (ferrersP N m x).im = 0 := by
  have := ferrersP_real (N : ℝ) (m : ℝ) hx
  simpa using this

/-- `∫ 𝖯^m_n 𝖯^m_ν` over `(-1, 1)` for integer degrees, through `P^{(m)}`. -/
lemma p2y_integral_ferrers_mul {m n ν : ℕ} (hn : m ≤ n) :
    ∫ x in (-1 : ℝ)..1, (ferrersP n m x).re * (ferrersP ν m x).re =
      if n = ν then 2 * ((n + m).factorial : ℝ) / ((2 * n + 1) * (n - m).factorial) else 0 := by
  rw [← p2y_D_orth hn ν]
  apply p2y_integral_congr_Ioo
  intro x hx
  have h := congrArg Complex.re (legInt_ferrersP_mul n ν m hx)
  rw [p2y_legInt_D_real n m x, p2y_legInt_D_real ν m x,
    show ((1 : ℂ) - (x : ℂ) ^ 2) ^ m = (((1 - x ^ 2) ^ m : ℝ) : ℂ) by push_cast; rfl,
    ← ofReal_mul, ← ofReal_mul, ofReal_re, Complex.mul_re, p2y_ferrersP_im n m hx,
    p2y_ferrersP_im ν m hx, mul_zero, sub_zero] at h
  exact h

/-- `𝖯s^m_n(x, 0) = 𝖯^m_n(x)` (real form). -/
lemma p2y_ps_zero_re {n m : ℕ} (hmn : m ≤ n) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    spheroidalPs n m x 0 = (ferrersP n m x).re := by
  rw [← spheroidalPs_gamma_zero hmn hx, ofReal_re]

/-- **The coefficients at `γ = 0`**: `a^m_{n,k}(0) = δ_{k,0}`. -/
lemma p2y_coeff_gamma_zero {n m : ℕ} (hmn : m ≤ n) (k : ℤ) :
    spheroidalCoeff n m 0 k = if k = 0 then 1 else 0 := by
  unfold spheroidalCoeff
  by_cases h1 : -(((n - m) / 2 : ℕ) : ℤ) ≤ k
  · simp only [h1, ↓reduceIte]
    unfold spheroidalCoeffMain
    obtain ⟨ν, hν⟩ : ∃ ν : ℕ, (ν : ℤ) = n + 2 * k := ⟨(n + 2 * k).toNat, by omega⟩
    have hc : ((n : ℂ) + 2 * (k : ℂ)) = (ν : ℂ) := by exact_mod_cast hν.symm
    have hI : ∫ x in (-1 : ℝ)..1, spheroidalPs n m x 0 * (ferrersP ((n : ℂ) + 2 * (k : ℂ))
        m x).re = if n = ν then 2 * ((n + m).factorial : ℝ) /
          ((2 * n + 1) * (n - m).factorial) else 0 := by
      rw [← p2y_integral_ferrers_mul hmn]
      apply p2y_integral_congr_Ioo
      intro x hx
      rw [hc, p2y_ps_zero_re hmn hx]
    rw [hI]
    by_cases hk : k = 0
    · subst hk
      have hnν : n = ν := by omega
      subst hnν
      have h1' : ((n : ℤ) - m + 2 * (0 : ℤ)).toNat = n - m := by omega
      have h2' : ((n : ℤ) + m + 2 * (0 : ℤ)).toNat = n + m := by omega
      rw [h1', h2']
      have hf1 : ((n - m).factorial : ℝ) ≠ 0 := by positivity
      have hf2 : ((n + m).factorial : ℝ) ≠ 0 := by positivity
      have h2n : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
      simp only [zpow_zero, Int.cast_zero, mul_zero, add_zero, one_mul, ↓reduceIte]
      field_simp
    · simp only [show n ≠ ν by omega, hk, ↓reduceIte, mul_zero]
  · simp only [h1, ↓reduceIte, show k ≠ 0 by omega]
    by_cases h2 : -(((n + m) / 2 : ℕ) : ℤ) ≤ k
    · simp only [h2, ↓reduceIte]
      have hF : spheroidalFwd n m 0 ((n + m) / 2 - (n - m) / 2 + 1) = 0 := by
        obtain ⟨j, hj⟩ : ∃ j, (n + m) / 2 - (n - m) / 2 + 1 = j + 2 :=
          ⟨(n + m) / 2 - (n - m) / 2 - 1, by omega⟩
        rw [hj, spheroidalFwd]
        simp [spheroidalRecC]
      rw [hF, div_zero]
    · simp only [h2, ↓reduceIte]

/-- `A^m_n(0) = 1`. -/
lemma p2y_A_gamma_zero {n m : ℕ} (hmn : m ≤ n) : spheroidalA n m 0 = 1 := by
  unfold spheroidalA
  simp_rw [p2y_coeff_gamma_zero hmn]
  rw [tsum_eq_single 0 (fun k hk => by simp [hk])]
  simp

/-- `A^{-m}_n(0) = 1`. -/
lemma p2y_ANeg_gamma_zero {n m : ℕ} (hmn : m ≤ n) : spheroidalANeg n m 0 = 1 := by
  unfold spheroidalANeg
  rw [tsum_eq_single 0 (fun k hk => by
    unfold spheroidalCoeffNeg
    split_ifs <;> simp [p2y_coeff_gamma_zero hmn, hk])]
  unfold spheroidalCoeffNeg
  simp only [Left.neg_nonpos_iff, Nat.cast_nonneg, ↓reduceIte, p2y_coeff_gamma_zero hmn,
    zpow_zero, one_mul, mul_one]
  have h1' : ((n : ℤ) - m + 2 * (0 : ℤ)).toNat = n - m := by omega
  have h2' : ((n : ℤ) + m + 2 * (0 : ℤ)).toNat = n + m := by omega
  rw [h1', h2']
  have hf1 : ((n - m).factorial : ℝ) ≠ 0 := by positivity
  have hf2 : ((n + m).factorial : ℝ) ≠ 0 := by positivity
  field_simp

/-- Solutions of 30.2.1 on `(-1, 1)` in second-order form `f'' = p f' + q f`. -/
lemma p2y_second_order {lam γ2 μ : ℝ} {f : ℝ → ℝ} (hf : IsSpheroidalSolutionReal lam γ2 μ f) :
    ∀ t ∈ Ioo (-1 : ℝ) 1, HasDerivAt f (deriv f t) t ∧ HasDerivAt (deriv f)
      ((2 * t / (1 - t ^ 2)) • deriv f t +
        (-(lam + γ2 * (1 - t ^ 2) - μ ^ 2 / (1 - t ^ 2)) / (1 - t ^ 2)) • f t) t := by
  intro t ht
  refine ⟨(hf.differentiableAt t ht).hasDerivAt, ?_⟩
  have h1 : 0 < 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
  have hW := hf.hasDerivAt t ht
  have hs : HasDerivAt (fun s : ℝ => 1 - s ^ 2) (-(2 * t)) t := by
    simpa using ((hasDerivAt_id t).pow 2).const_sub 1
  have hq := hW.div hs h1.ne'
  have hev : (fun s => (1 - s ^ 2) * deriv f s / (1 - s ^ 2)) =ᶠ[𝓝 t] deriv f := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs'
    have : 1 - s ^ 2 ≠ 0 := by nlinarith [hs'.1, hs'.2]
    field_simp
  refine (hq.congr_of_eventuallyEq hev.symm).congr_deriv ?_
  simp only [smul_eq_mul]
  field_simp
  ring

/-- **Uniqueness** for 30.2.1 on `(-1, 1)`: two solutions with the same value and derivative at a
point of `(-1, 1)` coincide there. -/
lemma p2y_eqOn_of_sol {lam γ2 μ : ℝ} {f g : ℝ → ℝ} (hf : IsSpheroidalSolutionReal lam γ2 μ f)
    (hg : IsSpheroidalSolutionReal lam γ2 μ g) {x0 : ℝ} (hx0 : x0 ∈ Ioo (-1 : ℝ) 1)
    (h0 : f x0 = g x0) (h1 : deriv f x0 = deriv g x0) : EqOn f g (Ioo (-1 : ℝ) 1) := by
  have hp : ContinuousOn (fun t : ℝ => 2 * t / (1 - t ^ 2)) (Ioo (-1 : ℝ) 1) :=
    ContinuousOn.div (by fun_prop) (by fun_prop) fun t ht => by nlinarith [ht.1, ht.2]
  have hq : ContinuousOn (fun t : ℝ => -(lam + γ2 * (1 - t ^ 2) - μ ^ 2 / (1 - t ^ 2)) /
      (1 - t ^ 2)) (Ioo (-1 : ℝ) 1) := by
    have hne : ∀ t ∈ Ioo (-1 : ℝ) 1, 1 - t ^ 2 ≠ 0 := fun t ht => by nlinarith [ht.1, ht.2]
    refine ContinuousOn.div ?_ (by fun_prop) hne
    exact ((continuousOn_const.add (continuousOn_const.mul (by fun_prop))).sub
      (continuousOn_const.div (by fun_prop) hne)).neg
  exact (ODE.eqOn_of_linear_ode isOpen_Ioo ordConnected_Ioo hx0 hp hq (p2y_second_order hf)
    (p2y_second_order hg) h0 h1).1

/-- Solutions of 30.2.1 on `(-1, 1)` form a vector space: `f + c g` is a solution. -/
lemma p2y_sol_add {lam γ2 μ : ℝ} {f g : ℝ → ℝ} (hf : IsSpheroidalSolutionReal lam γ2 μ f)
    (hg : IsSpheroidalSolutionReal lam γ2 μ g) (c : ℝ) :
    IsSpheroidalSolutionReal lam γ2 μ (fun x => f x + c * g x) := by
  have hd : ∀ t ∈ Ioo (-1 : ℝ) 1, deriv (fun x => f x + c * g x) t = deriv f t + c * deriv g t :=
    fun t ht => ((hf.differentiableAt t ht).hasDerivAt.add
      ((hg.differentiableAt t ht).hasDerivAt.const_mul c)).deriv
  refine ⟨fun t ht => ((hf.differentiableAt t ht).add
    ((hg.differentiableAt t ht).const_mul c)), fun t ht => ?_⟩
  have h := (hf.hasDerivAt t ht).add ((hg.hasDerivAt t ht).const_mul c)
  refine (h.congr_of_eventuallyEq ?_).congr_deriv (by ring)
  filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
  rw [hd s hs, Pi.add_apply]
  ring

/-- **Uniqueness of `𝖰s`**: two functions with the characterization `IsSpheroidalQs` agree on
`(-1, 1)` (their difference is a multiple of `𝖯s` of the wrong parity). -/
lemma p2y_isSpheroidalQs_unique {n m : ℕ} (hmn : m ≤ n) {γ2 : ℝ} {f g : ℝ → ℝ}
    (hf : IsSpheroidalQs n m γ2 f) (hg : IsSpheroidalQs n m γ2 g) :
    EqOn f g (Ioo (-1 : ℝ) 1) := by
  set P : ℝ → ℝ := fun t => spheroidalPs n m t γ2 with hP
  have hPs := isSpheroidalSolutionReal_spheroidalPs hmn γ2
  obtain ⟨x0, hx0, hP0⟩ : ∃ x0 ∈ Ioo (-1 : ℝ) 1, P x0 ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have h := integral_spheroidalPs_sq hmn γ2
    rw [p2y_integral_congr_Ioo (f₂ := fun _ => (0 : ℝ)) (fun x hx => by
      rw [show spheroidalPs n m x γ2 = 0 from hcon x hx]; ring)] at h
    have : (0 : ℝ) < 2 / (2 * n + 1) * (((n + m).factorial : ℝ) / (n - m).factorial) := by
      positivity
    rw [intervalIntegral.integral_zero] at h
    linarith
  set c := (f x0 - g x0) / P x0 with hc
  have hcP : c * P x0 = f x0 - g x0 := by simp only [hc]; field_simp
  clear_value c
  have hG := p2y_sol_add hg.ode hPs c
  have hdG : deriv (fun x => g x + c * P x) x0 = deriv g x0 + c * deriv P x0 :=
    ((hg.ode.differentiableAt x0 hx0).hasDerivAt.add
      ((hPs.differentiableAt x0 hx0).hasDerivAt.const_mul c)).deriv
  have hW := (hf.wronskian x0 hx0).trans (hg.wronskian x0 hx0).symm
  change P x0 * deriv f x0 - deriv P x0 * f x0 = P x0 * deriv g x0 - deriv P x0 * g x0 at hW
  have hfG : EqOn f (fun x => g x + c * P x) (Ioo (-1 : ℝ) 1) := by
    refine p2y_eqOn_of_sol hf.ode hG hx0 (by show f x0 = g x0 + c * P x0; linarith) ?_
    rw [hdG]
    have : P x0 * (deriv f x0 - deriv g x0 - c * deriv P x0) = 0 := by
      linear_combination hW - deriv P x0 * hcP
    have := (mul_eq_zero.mp this).resolve_left hP0
    linarith
  have hc0 : c = 0 := by
    have hm : -x0 ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hx0.2], by linarith [hx0.1]⟩
    have e1 := hfG hx0
    have e2 := hfG hm
    have p1 := hf.parity x0 hx0
    have p2 := hg.parity x0 hx0
    have p3 : P (-x0) = (-1) ^ (n - m) * P x0 := spheroidalPs_neg hmn x0 γ2
    simp only at e1 e2
    rw [p1, p2, p3] at e2
    have hs : ((-1 : ℝ) ^ (n - m + 1)) = -(-1) ^ (n - m) := by rw [pow_succ]; ring
    rw [hs] at e2
    have h2 : (-1 : ℝ) ^ (n - m) * (2 * c * P x0) = 0 := by
      linear_combination -((-1) ^ (n - m) * e1 + e2)
    have hne : ((-1 : ℝ) ^ (n - m)) ≠ 0 := pow_ne_zero _ (by norm_num)
    have := (mul_eq_zero.mp h2).resolve_left hne
    have := (mul_eq_zero.mp this).resolve_right hP0
    linarith
  intro x hx
  rw [hfG hx, hc0]
  simp

/-- The real part of a real-valued Ferrers solution solves 30.2.1 with `γ = 0`. -/
lemma p2y_real_of_ferrers {ν μ : ℝ} {F : ℝ → ℂ} (hF : IsFerrersSolution ν μ F) :
    IsSpheroidalSolutionReal (ν * (ν + 1)) 0 μ (fun x => (F x).re) := by
  have hd : ∀ x ∈ Ioo (-1 : ℝ) 1, HasDerivAt (fun t => (F t).re) (deriv F x).re x :=
    fun x hx => by
      simpa only [Function.comp_def, Complex.reCLM_apply] using
        Complex.reCLM.hasFDerivAt.comp_hasDerivAt x (hF x hx).1.hasDerivAt
  refine ⟨fun x hx => (hd x hx).differentiableAt, fun x hx => ?_⟩
  obtain ⟨-, f2, hf2, heq⟩ := hF x hx
  have h2 : HasDerivAt (fun t => (deriv F t).re) f2.re x := by
    simpa only [Function.comp_def, Complex.reCLM_apply] using
      Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hf2
  have hs : HasDerivAt (fun t : ℝ => 1 - t ^ 2) (-(2 * x)) x := by
    simpa using ((hasDerivAt_id x).pow 2).const_sub 1
  have hev : (fun t => (1 - t ^ 2) * deriv (fun t => (F t).re) t) =ᶠ[𝓝 x]
      (fun t => (1 - t ^ 2) * (deriv F t).re) := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with t ht
    rw [(hd t ht).deriv]
  refine ((hs.mul h2).congr_of_eventuallyEq hev).congr_deriv ?_
  have e3 : ((ν : ℂ) * ((ν : ℂ) + 1) - (μ : ℂ) ^ 2 / (1 - (x : ℂ) ^ 2)) =
      ((ν * (ν + 1) - μ ^ 2 / (1 - x ^ 2) : ℝ) : ℂ) := by push_cast; rfl
  have e1 : (1 - (x : ℂ) ^ 2) = ((1 - x ^ 2 : ℝ) : ℂ) := by push_cast; rfl
  have e2 : (2 * (x : ℂ)) = ((2 * x : ℝ) : ℂ) := by push_cast; rfl
  rw [e3, e1, e2] at heq
  have h := congrArg Complex.re heq
  simp only [Complex.add_re, Complex.sub_re, Complex.re_ofReal_mul, Complex.zero_re] at h
  linear_combination h

/-- `𝖰^m_n` solves the Ferrers equation. -/
lemma p2y_ferrersQ_sol (ν μ : ℂ) : IsFerrersSolution ν μ (ferrersQ ν μ) :=
  ((ferrersEven_isFerrersSolution ν μ).add_smul (ferrersOdd_isFerrersSolution ν μ) _ _).congr
    (ferrersQ_eqOn_even_odd ν μ).symm

/-- `𝖯^μ_ν` solves the Ferrers equation (regular case). -/
lemma p2y_ferrersP_sol {ν μ : ℂ} (h : LegendreQRegular ν μ) :
    IsFerrersSolution ν μ (ferrersP ν μ) :=
  ((ferrersEven_isFerrersSolution ν μ).add_smul (ferrersOdd_isFerrersSolution ν μ) _ _).congr
    (ferrersP_regular_eqOn h).symm

/-- `𝖰^m_n` is regular for integer `n, m ≥ 0`. -/
lemma p2y_regular (n m : ℕ) : LegendreQRegular (n : ℂ) (m : ℂ) := by
  intro k h
  have := congrArg Complex.re h
  simp at this
  have h1 : (0 : ℝ) ≤ n + m := by positivity
  have h2 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  linarith

/-- **The Legendre limit** (DLMF 30.5.3): `𝖰s^m_n(x, 0) = 𝖰^m_n(x)` on `(-1, 1)`.
Proved: at `γ = 0`, `a^m_{n,k} = δ_{k0}` and `A^{±m}_n = 1`, so `𝖰^m_n` satisfies the
characterization `IsSpheroidalQs`, which determines `𝖰s` on `(-1, 1)`
(`p2y_isSpheroidalQs_unique`). -/
@[dlmf 30.5.E3]
theorem spheroidalQs_gamma_zero {n m : ℕ} (hmn : m ≤ n) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    (spheroidalQs n m x 0 : ℂ) = ferrersQ n m x := by
  have hreg := p2y_regular n m
  have hQim : ∀ y ∈ Ioo (-1 : ℝ) 1, (ferrersQ n m y).im = 0 := fun y hy => by
    have := ferrersQ_real (n : ℝ) (m : ℝ) hy (by simpa using hreg)
    simpa using this
  set f₀ : ℝ → ℝ := fun y => if y ∈ Ioo (-1 : ℝ) 1 then (ferrersQ n m y).re else 0 with hf₀
  have hf₀I : ∀ y ∈ Ioo (-1 : ℝ) 1, f₀ y = (ferrersQ n m y).re := fun y hy => by
    simp only [hf₀, hy, ↓reduceIte]
  have hQsol : IsFerrersSolution ((n : ℝ) : ℂ) ((m : ℝ) : ℂ) (ferrersQ n m) := by
    simpa using p2y_ferrersQ_sol (n : ℂ) (m : ℂ)
  have hPsol : IsFerrersSolution (n : ℂ) (m : ℂ) (ferrersP n m) := p2y_ferrersP_sol hreg
  have hdQ : ∀ y ∈ Ioo (-1 : ℝ) 1, deriv f₀ y = (deriv (ferrersQ n m) y).re := by
    intro y hy
    have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt y (hQsol y hy).1.hasDerivAt
    refine HasDerivAt.deriv ?_
    refine (h.congr_of_eventuallyEq ?_)
    filter_upwards [isOpen_Ioo.mem_nhds hy] with t ht
    simp [hf₀I t ht]
  have hdP : ∀ y ∈ Ioo (-1 : ℝ) 1, deriv (fun t => spheroidalPs n m t 0) y =
      (deriv (ferrersP n m) y).re := by
    intro y hy
    have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt y (hPsol y hy).1.hasDerivAt
    refine HasDerivAt.deriv ?_
    refine (h.congr_of_eventuallyEq ?_)
    filter_upwards [isOpen_Ioo.mem_nhds hy] with t ht
    simp [p2y_ps_zero_re hmn ht]
  have hQs : IsSpheroidalQs n m 0 f₀ := by
    refine ⟨?_, fun y hy => ?_, fun y hy => ?_, fun y hy => by simp only [hf₀, hy, ↓reduceIte]⟩
    · rw [p1s_spheroidalEigenvalue_zero hmn]
      exact p1s_isSpheroidalSolutionReal_congr (p2y_real_of_ferrers hQsol)
        (fun y hy => (hf₀I y hy).symm)
    · have hy' : -y ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hy.2], by linarith [hy.1]⟩
      rw [hf₀I _ hy', hf₀I _ hy, ferrersQ_neg_of_add_eq_nat (N := n + m) (by push_cast; ring) y,
        show ((-1 : ℂ) ^ (n + m + 1)) = (((-1 : ℝ) ^ (n - m + 1) : ℝ) : ℂ) by
          rw [show n + m + 1 = (n - m + 1) + 2 * m by omega, pow_add, pow_mul]; push_cast; ring,
        re_ofReal_mul]
    · rw [hdQ y hy, hdP y hy, hf₀I y hy, p2y_ps_zero_re hmn hy, p2y_A_gamma_zero hmn,
        p2y_ANeg_gamma_zero hmn, mul_one, mul_one]
      have hW := ferrers_wronskian_4 (n : ℂ) (m : ℂ) hreg hy
      unfold ODE.wronskian at hW
      have hG1 : Complex.Gamma ((n : ℂ) + m + 1) = ((n + m).factorial : ℂ) := by
        rw [← Complex.Gamma_nat_eq_factorial]; push_cast; ring_nf
      have hG2 : Complex.Gamma ((n : ℂ) - m + 1) = ((n - m).factorial : ℂ) := by
        rw [← Complex.Gamma_nat_eq_factorial, Nat.cast_sub hmn]
      rw [hG1, hG2, show (((n + m).factorial : ℂ) / (((n - m).factorial : ℂ) * (1 - (y : ℂ) ^ 2)))
        = ((((n + m).factorial : ℝ) / ((1 - y ^ 2) * (n - m).factorial) : ℝ) : ℂ) by
          push_cast; ring] at hW
      have h := congrArg Complex.re hW
      rw [ofReal_re, Complex.sub_re, Complex.mul_re, Complex.mul_re,
        p2y_ferrersP_im n m hy, hQim y hy, zero_mul, zero_mul, sub_zero, sub_zero] at h
      linarith
  have hex : ∃ f, IsSpheroidalQs n m 0 f := ⟨f₀, hQs⟩
  have hu := p2y_isSpheroidalQs_unique hmn hex.choose_spec hQs hx
  simp only [spheroidalQs, hex, ↓reduceDIte]
  rw [hu, hf₀I x hx]
  exact Complex.ext (by simp) (by simp [hQim x hx])

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
lemma p1s_tendsto_spheroidalPsC_aux {n m : ℕ} (hmn : m ≤ n) (γ2 : ℝ) {x : ℝ}
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
