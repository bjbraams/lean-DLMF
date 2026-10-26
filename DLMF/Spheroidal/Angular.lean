/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Spheroidal.FerrersDefs
public import DLMF.Spheroidal.Equation
public import DLMF.Legendre.Associated

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

/-- **The Legendre limit** (DLMF 30.4.2): `𝖯s^m_n(x, 0) = 𝖯^m_n(x)` on `(-1, 1)`. -/
@[dlmf 30.4.E2]
theorem spheroidalPs_gamma_zero {n m : ℕ} (hmn : m ≤ n) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    (spheroidalPs n m x 0 : ℂ) = ferrersP n m x := by
  sorry

/-- **Parity** (DLMF 30.4.3): `𝖯s^m_n(-x, γ²) = (-1)^{n-m} 𝖯s^m_n(x, γ²)`. -/
@[dlmf 30.4.E3]
theorem spheroidalPs_neg {n m : ℕ} (hmn : m ≤ n) (x γ2 : ℝ) :
    spheroidalPs n m (-x) γ2 = (-1) ^ (n - m) * spheroidalPs n m x γ2 := by
  sorry

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
  sorry

/-! ### Orthogonality and expansions (§30.4(iv)) -/

/-- **Orthogonality** (DLMF 30.4.6): `∫_{-1}^1 𝖯s^m_k 𝖯s^m_n dx = 0` for `k ≠ n`; the case
`k = n` is 30.4.1 (`integral_spheroidalPs_sq`). -/
@[dlmf 30.4.E6]
theorem integral_spheroidalPs_mul {k n m : ℕ} (hmk : m ≤ k) (hmn : m ≤ n) (hkn : k ≠ n)
    (γ2 : ℝ) : ∫ x in (-1 : ℝ)..1, spheroidalPs k m x γ2 * spheroidalPs n m x γ2 = 0 := by
  sorry

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
  sorry

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

/-- **Boundary values of `𝑃s`** (DLMF 30.6.4): `𝑃s^m_n(x ± i0, γ²) = (∓i)^m 𝖯s^m_n(x, γ²)` for
`-1 < x < 1`. -/
@[dlmf 30.6.E4]
theorem tendsto_spheroidalPsC_boundary {n m : ℕ} (hmn : m ≤ n) (γ2 : ℝ) {x : ℝ}
    (hx : x ∈ Ioo (-1 : ℝ) 1) :
    Tendsto (fun ε : ℝ => spheroidalPsC n m (x + ε * I) γ2) (𝓝[>] 0)
        (𝓝 ((-I) ^ m * spheroidalPs n m x γ2)) ∧
      Tendsto (fun ε : ℝ => spheroidalPsC n m (x + ε * I) γ2) (𝓝[<] 0)
        (𝓝 (I ^ m * spheroidalPs n m x γ2)) := by
  sorry

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
