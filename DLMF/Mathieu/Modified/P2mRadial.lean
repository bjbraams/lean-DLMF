/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Mathieu.Modified.P2mCrossSeries

/-!
# The cross-product series of the modified Mathieu functions (proof of DLMF 28.24.1)

* `p2m_floquet_coeff_rec`: integration by parts gives the recurrence 28.14.4 for the exponential
  Fourier coefficients over `[0, π]` of a Floquet solution of Mathieu's equation;
* `p2m_mathieuMeInt_floquet`: `me_k(·, q)` (integer `k`, real `q`) is a Floquet solution with
  multiplier `(-1)^k`;
* `p2m_coeff_facts`: for admissible `(ν, h)` the coefficients `c^ν_{2m}(h²)` solve 28.14.4 with
  `a = λ_ν(h²)` and are bounded;
* `p2m_hasSum_modMathieuTerm`: DLMF 28.24.1, from the abstract theorem `p2m_cross_series`;
* derivatives of the continued Bessel functions in `z` (all orders, `Y` at integer orders by
  uniform limits in the order), locally uniform bounds for the shifted cross-product series
  `p2m_F` (`p2m_fam_locally_uniform`, giving §28.24's locally uniform convergence) and their
  termwise derivatives (`p2m_hasDerivAt_F`);
* `p2m_isModMathieuSolution_modMathieuM`: `M^{(j)}_ν` solves 28.20.1 (`p2m_F_ode`: the second
  derivative is reduced termwise with the Bessel recurrences and summed with 28.14.4);
* the integer-order expansions 28.24.2–28.24.5: the coefficients `c^{±N}_{2k}` as cosine and sine
  integrals of `ce_N`, `se_N` (`p2m_mathieuMeCoeff_ce`, `p2m_mathieuMeCoeff_se`), the parity
  `𝒞_{-k} = (-1)^k 𝒞_k` of the continued cylinder functions, and folding of 28.24.1 over `ℤ`.
-/

@[expose] public noncomputable section

open Complex Set Filter
open scoped Topology Real Nat

namespace DLMF.Mathieu

/-- Integration by parts for the exponential Fourier coefficients over `[0, π]` of a Floquet
solution of Mathieu's equation: `q I_{k+2} + q I_{k-2} = (a - k²) I_k`,
`I_k = ∫₀^π f(x) e^{-ikx} dx`, when `f(z + π) = s f(z)` and `s (-1)^k = 1`. -/
theorem p2m_floquet_coeff_rec {a q s : ℂ} {f : ℂ → ℂ} (hf : IsMathieuSolution a q f)
    (hper : ∀ z, f (z + π) = s * f z) (k : ℤ) (hs : s * (-1 : ℂ) ^ k = 1) :
    q * (∫ x in (0 : ℝ)..π, f x * Complex.exp (-(I * ((k + 2 : ℤ) : ℂ) * x))) +
      q * (∫ x in (0 : ℝ)..π, f x * Complex.exp (-(I * ((k - 2 : ℤ) : ℂ) * x))) =
      (a - (k : ℂ) ^ 2) * ∫ x in (0 : ℝ)..π, f x * Complex.exp (-(I * (k : ℂ) * x)) := by
  set K : ℂ := (k : ℂ)
  let E : ℂ → ℂ → ℂ := fun κ x => Complex.exp (-(I * κ * x))
  let g : ℝ → ℂ := fun x => deriv f x * E K x + I * K * f x * E K x
  have hE : ∀ (κ : ℂ) (x : ℝ), HasDerivAt (fun x : ℝ => E κ x) (-(I * κ) * E κ x) x := by
    intro κ x
    have hl : HasDerivAt (fun x : ℝ => -(I * κ * (x : ℂ))) (-(I * κ)) x := by
      simpa using (((hasDerivAt_id (x : ℂ)).const_mul (I * κ)).neg).comp_ofReal
    have := hl.cexp
    simpa [E, mul_comm] using this
  have hg : ∀ x : ℝ, HasDerivAt g
      ((2 * q * Complex.cos (2 * x) - a + K ^ 2) * (f x * E K x)) x := by
    intro x
    have h1 : HasDerivAt (fun x : ℝ => deriv f x)
        ((2 * q * Complex.cos (2 * x) - a) * f x) x := (hf.hasDerivAt_deriv x).comp_ofReal
    have h0 : HasDerivAt (fun x : ℝ => f x) (deriv f x) x :=
      (hf.differentiable x).hasDerivAt.comp_ofReal
    convert (h1.mul (hE K x)).add ((h0.const_mul (I * K)).mul (hE K x)) using 1
    ring_nf
    rw [I_sq]
    ring
  have hcont : Continuous fun x : ℝ =>
      (2 * q * Complex.cos (2 * x) - a + K ^ 2) * (f x * E K x) := by
    have := hf.differentiable.continuous
    fun_prop
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := π)
    (fun x _ => hg x) (hcont.intervalIntegrable _ _)
  have hEπ : E K π = (-1 : ℂ) ^ k := by
    simp only [E, K]
    rw [show -(I * (k : ℂ) * (π : ℂ)) = ((-k : ℤ) : ℂ) * (π * I) by push_cast; ring,
      Complex.exp_int_mul, Complex.exp_pi_mul_I, zpow_neg, ← inv_zpow, inv_neg, inv_one]
  have hE0 : E K 0 = 1 := by simp [E]
  have hfπ : f π = s * f 0 := by simpa using hper 0
  have hdπ : deriv f π = s * deriv f 0 := by
    have h := congrArg (fun F => deriv F 0) (funext hper : (fun z => f (z + π)) = fun z => s * f z)
    rw [deriv_comp_add_const, deriv_const_mul _ (hf.differentiable 0)] at h
    simpa using h
  have h0 : ∫ x in (0 : ℝ)..π,
      (2 * q * Complex.cos (2 * x) - a + K ^ 2) * (f x * E K x) = 0 := by
    rw [hint]
    simp only [g, Complex.ofReal_zero]
    rw [hEπ, hE0, hfπ, hdπ]
    linear_combination (deriv f 0 + I * K * f 0) * hs
  have hpt : ∀ x : ℝ, (2 * q * Complex.cos (2 * x) - a + K ^ 2) * (f x * E K x) =
      q * (f x * E ((k + 2 : ℤ) : ℂ) x) + q * (f x * E ((k - 2 : ℤ) : ℂ) x) +
        (K ^ 2 - a) * (f x * E K x) := by
    intro x
    simp only [E, K]
    push_cast
    rw [Complex.cos, show -(I * ((k : ℂ) + 2) * x) = -(I * k * x) + -(2 * x * I) by ring,
      show -(I * ((k : ℂ) - 2) * x) = -(I * k * x) + 2 * x * I by ring, Complex.exp_add,
      Complex.exp_add, show 2 * (x : ℂ) * I = 2 * x * I by ring]
    ring_nf
  have hc : ∀ κ : ℂ, Continuous fun x : ℝ => f x * E κ x := by
    intro κ
    have := hf.differentiable.continuous
    fun_prop
  simp_rw [hpt] at h0
  rw [intervalIntegral.integral_add (((hc _).intervalIntegrable _ _).const_mul _ |>.add
      (((hc _).intervalIntegrable _ _).const_mul _)) (((hc K).intervalIntegrable _ _).const_mul _),
    intervalIntegral.integral_add (((hc _).intervalIntegrable _ _).const_mul _)
      (((hc _).intervalIntegrable _ _).const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at h0
  simp only [E] at h0
  linear_combination h0

/-- The order recurrence of the cylinder functions `𝒞^{(j)}_μ(h e^z)`, `j = 1, …, 4`. -/
theorem p2m_mathieuCylExp_rec (j : ℕ) (hj₁ : 1 ≤ j) (hj₄ : j ≤ 4) (μ : ℂ) {h : ℂ} (hh : h ≠ 0)
    (z : ℂ) :
    mathieuCylExp j (μ - 1) h z + mathieuCylExp j (μ + 1) h z =
      2 * μ / (h * Complex.exp z) * mathieuCylExp j μ h z := by
  have hJ := p2m_besselJExp_rec μ hh z
  have hY := p2m_besselYExp_rec μ hh z
  interval_cases j <;> simp only [mathieuCylExp]
  · exact hJ
  · exact hY
  · linear_combination hJ + I * hY
  · linear_combination hJ - I * hY

/-- `me_k(·, q)` for integer `k` and real `q` solves Mathieu's equation with `a = λ_k(q)` and is a
Floquet solution with multiplier `(-1)^k`. -/
theorem p2m_mathieuMeInt_floquet (k : ℤ) (q : ℝ) :
    IsMathieuSolution (mathieuLambdaInt k q) q (fun z => mathieuMeInt k z q) ∧
      ∀ z, mathieuMeInt k (z + π) q = (-1 : ℂ) ^ k * mathieuMeInt k z q := by
  by_cases hk : 0 ≤ k
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    have e : ∀ z, mathieuMeInt n z q = (Real.sqrt 2 : ℂ) * mathieuCe n z q := by
      intro z; simp [mathieuMeInt]
    have el : mathieuLambdaInt n q = mathieuA n q := by simp [mathieuLambdaInt]
    rw [el, show (fun z => mathieuMeInt n z q) = fun z => (Real.sqrt 2 : ℂ) * mathieuCe n z q
      from funext e]
    refine ⟨(isMathieuSolution_mathieuCe n q).const_mul _, fun z => ?_⟩
    rw [e, e, zpow_natCast]
    rcases Nat.even_or_odd' n with ⟨t, rfl | rfl⟩
    · rw [mathieuCe_even_add_pi, pow_mul]; simp
    · rw [mathieuCe_odd_add_pi, pow_succ, pow_mul]; simp
  · push Not at hk
    obtain ⟨N, hN, rfl⟩ : ∃ N : ℕ, N ≠ 0 ∧ k = -(N : ℤ) := ⟨k.natAbs, by omega, by omega⟩
    have hk' : ¬ (0 : ℤ) ≤ -(N : ℤ) := by omega
    have e : ∀ z, mathieuMeInt (-(N : ℤ)) z q = -((Real.sqrt 2 : ℂ) * I) * mathieuSe N z q := by
      intro z; simp [mathieuMeInt, hN]
    have el : mathieuLambdaInt (-(N : ℤ)) q = mathieuB N q := by simp [mathieuLambdaInt, hN]
    rw [el, show (fun z => mathieuMeInt (-(N : ℤ)) z q) =
      fun z => -((Real.sqrt 2 : ℂ) * I) * mathieuSe N z q from funext e]
    refine ⟨(isMathieuSolution_mathieuSe N q).const_mul _, fun z => ?_⟩
    rw [e, e, zpow_neg, zpow_natCast]
    rcases Nat.even_or_odd' N with ⟨t, rfl | rfl⟩
    · obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
      rw [show 2 * (s + 1) = 2 * s + 2 by ring, mathieuSe_even_add_pi, pow_add, pow_mul]; simp
    · rw [mathieuSe_odd_add_pi, pow_succ, pow_mul]; simp

/-- The coefficients `c^ν_{2m}(h²)` of an admissible `(ν, h)` solve a recurrence 28.14.4 and are
bounded. -/
theorem p2m_coeff_facts {ν h : ℂ} (hν : ModMathieuAdmissible ν h) :
    (∀ m : ℤ, h ^ 2 * mathieuMeCoeff ν (h ^ 2) (m + 1) -
      (mathieuLambda ν (h ^ 2) - (ν + 2 * m) ^ 2) * mathieuMeCoeff ν (h ^ 2) m +
        h ^ 2 * mathieuMeCoeff ν (h ^ 2) (m - 1) = 0) ∧
      ∃ M : ℝ, ∀ m, ‖mathieuMeCoeff ν (h ^ 2) m‖ ≤ M := by
  rcases hν with ⟨hν, hq⟩ | ⟨⟨k₀, rfl⟩, hq⟩
  · refine ⟨mathieuMeCoeff_recurrence hν hq, ?_⟩
    have hs : Summable (fun m => ‖mathieuMeCoeff ν (h ^ 2) m‖) := by
      simp only [mathieuMeCoeff_of_not_int hν]; exact (m28b_isMeCoeffSeq_data hq).2.1
    exact ⟨_, fun m => hs.le_tsum m (fun j _ => norm_nonneg _)⟩
  · set q : ℝ := (h ^ 2).re
    have hq' : h ^ 2 = (q : ℂ) := Complex.ext (by simp [q]) (by simp [hq])
    rw [hq', mathieuLambda_intCast]
    have hex : ∃ k : ℤ, (k : ℂ) = (k₀ : ℂ) := ⟨k₀, rfl⟩
    have hc : ∀ m : ℤ, mathieuMeCoeff k₀ q m = (1 / π : ℂ) * ∫ x in (0 : ℝ)..π,
        mathieuMeInt k₀ x q * Complex.exp (-(I * ((k₀ + 2 * m : ℤ) : ℂ) * x)) := by
      intro m
      simp only [mathieuMeCoeff, hex, ite_true, mathieuMe_intCast]
      push_cast; rfl
    obtain ⟨hsol, hper⟩ := p2m_mathieuMeInt_floquet k₀ q
    refine ⟨fun m => ?_, ?_⟩
    · have := p2m_floquet_coeff_rec hsol hper (k₀ + 2 * m) (by
        rw [← zpow_add₀ (by norm_num), show k₀ + (k₀ + 2 * m) = 2 * (k₀ + m) by ring, zpow_mul]
        simp)
      rw [hc, hc, hc]
      rw [show k₀ + 2 * (m + 1) = k₀ + 2 * m + 2 by ring,
        show k₀ + 2 * (m - 1) = k₀ + 2 * m - 2 by ring]
      push_cast at this ⊢
      linear_combination (1 / π : ℂ) * this
    · refine ⟨(1 / π) * ∫ x in (0 : ℝ)..π, ‖mathieuMeInt k₀ x q‖, fun m => ?_⟩
      rw [hc, norm_mul]
      have hπ : ‖(1 / π : ℂ)‖ = 1 / π := by
        rw [norm_div, norm_one, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
      rw [hπ]
      gcongr
      refine (intervalIntegral.norm_integral_le_integral_norm Real.pi_pos.le).trans (le_of_eq ?_)
      refine intervalIntegral.integral_congr fun x _ => ?_
      rw [norm_mul, Complex.norm_exp]
      simp

/-- **DLMF 28.24.1** (proof of `hasSum_modMathieuTerm`). -/
theorem p2m_hasSum_modMathieuTerm (j : ℕ) (hj₁ : 1 ≤ j) (hj₄ : j ≤ 4) {ν h : ℂ}
    (hν : ModMathieuAdmissible ν h) (hh : h ≠ 0) (n : ℤ) (z : ℂ) :
    HasSum (modMathieuTerm j ν z h n)
      (mathieuMeCoeff ν (h ^ 2) n * modMathieuM j ν z h) := by
  obtain ⟨hrec, M, hM⟩ := p2m_coeff_facts hν
  set c := mathieuMeCoeff ν (h ^ 2) with hcdef
  set x := h * Complex.exp (-z) with hxdef
  set y := h * Complex.exp z with hydef
  have hx : x ≠ 0 := mul_ne_zero hh (Complex.exp_ne_zero _)
  have hy : y ≠ 0 := mul_ne_zero hh (Complex.exp_ne_zero _)
  have hxy : x * y = h ^ 2 := by
    rw [hxdef, hydef, mul_mul_mul_comm, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
    ring
  have hrec' : ∀ m : ℤ, x * y * c (m + 1) - (mathieuLambda ν (h ^ 2) - (ν + 2 * m) ^ 2) * c m +
      x * y * c (m - 1) = 0 := by
    rw [hxy]; exact hrec
  obtain ⟨Cc, K, hCc, hK, hc⟩ := p2m_decay_int (mul_ne_zero hx hy) hM hrec'
  set Jx : ℤ → ℂ := fun k => besselJExp k h (-z) with hJxdef
  have hJr : ∀ k : ℤ, Jx (k - 1) + Jx (k + 1) = 2 * k / x * Jx k := by
    intro k
    have := p2m_besselJExp_rec (k : ℂ) hh (-z)
    simp only [hJxdef]
    push_cast
    exact this
  set B : ℝ := max 1 (‖x‖ / 2)
  have hB : 1 ≤ B := le_max_left _ _
  have hJ : ∀ k : ℤ, ‖Jx k‖ ≤ Real.exp (‖x‖ ^ 2 / 4) * B ^ k.natAbs := by
    intro k
    simp only [hJxdef]
    rw [p1c_besselJExp_intCast]
    refine (Complex.norm_besselJ_intCast_le k x).trans ?_
    gcongr
    calc (‖x‖ / 2) ^ k.natAbs / (k.natAbs ! : ℝ) ≤ (‖x‖ / 2) ^ k.natAbs :=
          div_le_self (by positivity) (Nat.one_le_cast.mpr (Nat.factorial_pos _))
      _ ≤ B ^ k.natAbs := pow_le_pow_left₀ (by positivity) (le_max_right _ _) _
  set Cy : ℤ → ℂ := fun k => mathieuCylExp j (ν + k) h z with hCydef
  have hCr : ∀ k : ℤ, Cy (k - 1) + Cy (k + 1) = 2 * (ν + k) / y * Cy k := by
    intro k
    have := p2m_mathieuCylExp_rec j hj₁ hj₄ (ν + k) hh z
    simp only [hCydef]
    push_cast
    rw [← add_sub_assoc, ← add_assoc]
    exact this
  obtain ⟨EC, A, hEC, hA, hC⟩ := p2m_growth_int hy hCr
  have hC' : ∀ k : ℤ, ‖Cy k‖ ≤ EC * (max 1 A) ^ k.natAbs * (k.natAbs ! : ℝ) := by
    intro k
    refine (hC k).trans ?_
    gcongr
    exact le_max_right _ _
  have hterm : ∀ m : ℤ, modMathieuTerm j ν z h m = p2m_fam c Jx Cy (-m) m := by
    intro m
    funext ℓ
    simp only [modMathieuTerm, p2m_fam, hJxdef, hCydef, hcdef]
    rw [show ℓ + -m = ℓ - m by ring]
    push_cast
    ring_nf
  by_cases hex : ∃ n₀ : ℤ, mathieuMeCoeff ν (h ^ 2) n₀ ≠ 0
  · have hn₀ : c (modMathieuIndex ν h) ≠ 0 := by
      have e : modMathieuIndex ν h = hex.choose := by simp only [modMathieuIndex, hex, dite_true]
      rw [e]; exact hex.choose_spec
    have := p2m_cross_series hx hy hrec' hJr hCr hCc hK (Real.exp_pos _).le hB hEC
      (le_max_left _ _) hc hJ hC' hn₀ n
    rw [hterm]
    convert this using 2
    simp only [modMathieuM, hterm]
    rfl
  · push Not at hex
    have h0 : modMathieuTerm j ν z h n = 0 := by
      funext ℓ; simp [modMathieuTerm, hex]
    rw [h0, show c n = 0 from hex n, zero_mul]
    exact hasSum_zero

/-! ### Derivatives and locally uniform bounds -/

/-- The `z`-derivative of the continued `J_μ(h e^z)`: `μ J_μ - h e^z J_{μ+1}`. -/
theorem p2m_hasDerivAt_besselJExp (μ : ℂ) {h : ℂ} (hh : h ≠ 0) (z : ℂ) :
    HasDerivAt (fun z => besselJExp μ h z)
      (μ * besselJExp μ h z - h * Complex.exp z * besselJExp (μ + 1) h z) z := by
  have h2 : h / 2 ≠ 0 := div_ne_zero hh two_ne_zero
  have hg : HasDerivAt (fun z => -((h * Complex.exp z) ^ 2 / 4))
      (-(h * Complex.exp z) ^ 2 / 2) z := by
    have := (((Complex.hasDerivAt_exp z).const_mul h).pow 2).div_const 4 |>.neg
    convert this using 1; ring
  have hF := (DLMF.Bessel.hasDerivAt_regularized0F1 (μ + 1)
    (-((h * Complex.exp z) ^ 2 / 4))).comp z hg
  have hE : HasDerivAt (fun z => Complex.exp (μ * z)) (μ * Complex.exp (μ * z)) z := by
    have := ((hasDerivAt_id z).const_mul μ).cexp
    simpa [mul_comm] using this
  have := (hE.const_mul ((h / 2) ^ μ)).mul hF
  unfold besselJExp
  convert this using 1
  · funext w; rfl
  rw [cpow_add _ _ h2, cpow_one,
    show Complex.exp ((μ + 1) * z) = Complex.exp (μ * z) * Complex.exp z by
      rw [← Complex.exp_add]; ring_nf]
  simp only [Function.comp_def]
  ring

/-- Joint continuity of the continued `J_μ(h e^z)` in `(μ, z)`. -/
theorem p2m_continuous_besselJExp {h : ℂ} (hh : h ≠ 0) :
    Continuous fun p : ℂ × ℂ => besselJExp p.1 h p.2 := by
  have h2 : h / 2 ≠ 0 := div_ne_zero hh two_ne_zero
  have c1 : Continuous fun p : ℂ × ℂ => (h / 2) ^ p.1 :=
    continuous_fst.const_cpow (Or.inl h2)
  have c2 : Continuous fun p : ℂ × ℂ => Complex.exp (p.1 * p.2) :=
    Complex.continuous_exp.comp (continuous_fst.mul continuous_snd)
  have c3 : Continuous fun p : ℂ × ℂ => (p.1 + 1, -((h * Complex.exp p.2) ^ 2 / 4)) :=
    (continuous_fst.add continuous_const).prodMk
      (((continuous_const.mul (Complex.continuous_exp.comp continuous_snd)).pow 2).div_const
        4).neg
  have c4 := DLMF.Bessel.continuous_regularized0F1.comp c3
  have e : (fun p : ℂ × ℂ => besselJExp p.1 h p.2) = fun p => (h / 2) ^ p.1 *
      Complex.exp (p.1 * p.2) * regularizedHGFun (∅ : Multiset ℂ) {p.1 + 1}
        (-((h * Complex.exp p.2) ^ 2 / 4)) := rfl
  rw [e]
  exact (c1.mul c2).mul c4

theorem p2m_continuous_besselDExp {h : ℂ} (hh : h ≠ 0) :
    Continuous fun p : ℂ × ℂ => p2m_besselDExp p.1 h p.2 := by
  have hJ := p2m_continuous_besselJExp hh
  unfold p2m_besselDExp
  exact (hJ.mul (by fun_prop)).sub (hJ.comp (by fun_prop : Continuous fun p : ℂ × ℂ =>
    (-p.1, p.2)))

/-- Joint continuity of the continued `Y_μ(h e^z)` in `(μ, z)`, including integer orders. -/
theorem p2m_continuousAt_besselYExp {h : ℂ} (hh : h ≠ 0) (μ₀ z₀ : ℂ) :
    ContinuousAt (fun p : ℂ × ℂ => besselYExp p.1 h p.2) (μ₀, z₀) := by
  have hD := p2m_continuous_besselDExp hh
  by_cases hν : ∃ k : ℤ, μ₀ = k
  · obtain ⟨n, rfl⟩ := hν
    have hds := DLMF.Confluent.continuousOn_dslope_param (X := ℂ)
      (f := fun w ν => p2m_besselDExp ν h w) (s := univ) isOpen_univ
      ((hD.comp continuous_swap).continuousOn) (fun w _ => p2m_differentiable_besselDExp hh w) n
    have h1 : ContinuousAt (fun p : ℂ × ℂ => dslope (fun ν => p2m_besselDExp ν h p.2) n p.1)
        (n, z₀) :=
      ContinuousAt.comp (g := fun q : ℂ × ℂ => dslope (fun ν => p2m_besselDExp ν h q.1) n q.2)
        (f := Prod.swap) (hds.continuousAt (prod_mem_nhds univ_mem univ_mem))
        continuous_swap.continuousAt
    have h2 : ContinuousAt (fun p : ℂ × ℂ => dslope (fun ν : ℂ => Complex.sin (ν * π)) n p.1)
        (n, z₀) :=
      ContinuousAt.comp (g := dslope (fun ν : ℂ => Complex.sin (ν * π)) n) (f := Prod.fst)
        (continuousAt_dslope_same.mpr (by fun_prop)) continuous_fst.continuousAt
    refine (h1.div h2 (DLMF.Bessel.dslope_sin_ne_zero n
      (Metric.mem_ball_self (by norm_num)))).congr ?_
    filter_upwards [prod_mem_nhds (Metric.ball_mem_nhds (n : ℂ) (by norm_num : (0 : ℝ) < 1 / 2))
      univ_mem] with p hp
    exact (p2m_besselYExp_eq_dslope n hp.1 hh p.2).symm
  · push Not at hν
    have hopen : IsOpen {μ : ℂ | Complex.sin (μ * π) ≠ 0} :=
      isOpen_ne_fun (by fun_prop) continuous_const
    have hc : ContinuousAt (fun p : ℂ × ℂ => p2m_besselDExp p.1 h p.2 /
        Complex.sin (p.1 * π)) (μ₀, z₀) :=
      hD.continuousAt.div (by fun_prop) (DLMF.Bessel.sin_mul_pi_ne_zero hν)
    refine hc.congr ?_
    filter_upwards [prod_mem_nhds (hopen.mem_nhds (DLMF.Bessel.sin_mul_pi_ne_zero hν))
      univ_mem] with p hp
    have hp' : ∀ k : ℤ, p.1 ≠ k := fun k hk => hp.1 (by
      rw [hk]; exact DLMF.Bessel.sin_int_mul_pi_complex k)
    exact (p2m_besselYExp_of_not_int hp' h p.2).symm

theorem p2m_hasDerivAt_besselYExp_of_not_int {μ : ℂ} (hμ : ∀ k : ℤ, μ ≠ k) {h : ℂ}
    (hh : h ≠ 0) (z : ℂ) :
    HasDerivAt (fun z => besselYExp μ h z)
      (μ * besselYExp μ h z - h * Complex.exp z * besselYExp (μ + 1) h z) z := by
  have hs := DLMF.Bessel.sin_mul_pi_ne_zero hμ
  have hY : (fun z => besselYExp μ h z) = fun z => p2m_besselDExp μ h z / Complex.sin (μ * π) :=
    funext fun w => p2m_besselYExp_of_not_int hμ h w
  have hJ1 := p2m_hasDerivAt_besselJExp μ hh z
  have hJ2 := p2m_hasDerivAt_besselJExp (-μ) hh z
  have hD : HasDerivAt (fun w => p2m_besselDExp μ h w)
      ((μ * besselJExp μ h z - h * Complex.exp z * besselJExp (μ + 1) h z) * Complex.cos (μ * π) -
        (-μ * besselJExp (-μ) h z - h * Complex.exp z * besselJExp (-μ + 1) h z)) z := by
    unfold p2m_besselDExp
    exact (hJ1.mul_const _).sub hJ2
  have h' := hD.div_const (Complex.sin (μ * π))
  rw [← hY] at h'
  convert h' using 1
  rw [p2m_besselYExp_of_not_int hμ, p2m_besselYExp_of_not_int (DLMF.Bessel.not_int_add_one hμ),
    DLMF.Bessel.sin_add_one_mul_pi]
  have hr := p2m_besselJExp_rec (-μ) hh z
  rw [show -μ - 1 = -(μ + 1) by ring] at hr
  simp only [p2m_besselDExp, DLMF.Bessel.cos_add_one_mul_pi]
  have hez := Complex.exp_ne_zero z
  have hr' : h * Complex.exp z * (besselJExp (-(μ + 1)) h z + besselJExp (-μ + 1) h z) =
      -2 * μ * besselJExp (-μ) h z := by
    rw [hr]; field_simp
  rw [eq_div_iff hs]
  field_simp
  linear_combination (-1 : ℂ) * hr'

/-- The `z`-derivative of the continued `Y_μ(h e^z)`, every order: `μ Y_μ - h e^z Y_{μ+1}`. -/
theorem p2m_hasDerivAt_besselYExp (μ : ℂ) {h : ℂ} (hh : h ≠ 0) (z : ℂ) :
    HasDerivAt (fun z => besselYExp μ h z)
      (μ * besselYExp μ h z - h * Complex.exp z * besselYExp (μ + 1) h z) z := by
  have := DLMF.Confluent.integerComplement_nhdsWithin_neBot μ
  have hY := p2m_continuousAt_besselYExp hh
  refine hasDerivAt_of_tendstoUniformlyOnFilter (l := 𝓝[integerComplement] μ)
    (f := fun c w => besselYExp c h w)
    (f' := fun c w => c * besselYExp c h w - h * Complex.exp w * besselYExp (c + 1) h w)
    (g' := fun w => μ * besselYExp μ h w - h * Complex.exp w * besselYExp (μ + 1) h w) ?_ ?_ ?_
  · have hc : ContinuousAt (fun p : ℂ × ℂ => p.1 * besselYExp p.1 h p.2 -
        h * Complex.exp p.2 * besselYExp (p.1 + 1) h p.2) (μ, z) := by
      have h2 : ContinuousAt (fun p : ℂ × ℂ => besselYExp (p.1 + 1) h p.2) (μ, z) :=
        ContinuousAt.comp (g := fun p : ℂ × ℂ => besselYExp p.1 h p.2)
          (f := fun p : ℂ × ℂ => (p.1 + 1, p.2)) (hY (μ + 1) z) (by fun_prop)
      exact (continuousAt_fst.mul (hY μ z)).sub ((by fun_prop : ContinuousAt
        (fun p : ℂ × ℂ => h * Complex.exp p.2) (μ, z)).mul h2)
    exact DLMF.Confluent.tendstoUniformlyOnFilter_of_continuousAt
      (F := fun c w => c * besselYExp c h w - h * Complex.exp w * besselYExp (c + 1) h w) hc
      nhdsWithin_le_nhds
  · have hm : integerComplement ×ˢ univ ∈ 𝓝[integerComplement] μ ×ˢ 𝓝 z :=
      prod_mem_prod self_mem_nhdsWithin univ_mem
    filter_upwards [hm] with p hp
    exact p2m_hasDerivAt_besselYExp_of_not_int
      (DLMF.Confluent.forall_of_mem_integerComplement hp.1) hh p.2
  · filter_upwards [univ_mem] with y _
    exact ((p2m_continuousAt_besselYExp_order hh y μ).tendsto).mono_left nhdsWithin_le_nhds

/-- The `z`-derivative of the cylinder functions `𝒞^{(j)}_μ(h e^z)`: `μ 𝒞_μ - h e^z 𝒞_{μ+1}`. -/
theorem p2m_hasDerivAt_mathieuCylExp (j : ℕ) (hj₁ : 1 ≤ j) (hj₄ : j ≤ 4) (μ : ℂ) {h : ℂ}
    (hh : h ≠ 0) (z : ℂ) :
    HasDerivAt (fun z => mathieuCylExp j μ h z)
      (μ * mathieuCylExp j μ h z - h * Complex.exp z * mathieuCylExp j (μ + 1) h z) z := by
  have hJ := p2m_hasDerivAt_besselJExp μ hh z
  have hY := p2m_hasDerivAt_besselYExp μ hh z
  interval_cases j <;> simp only [mathieuCylExp]
  · exact hJ
  · exact hY
  · convert hJ.add (hY.const_mul I) using 1; ring
  · convert hJ.sub (hY.const_mul I) using 1; ring

/-- Symmetric form: `d/dz 𝒞_μ(h e^z) = (h e^z / 2)(𝒞_{μ-1} - 𝒞_{μ+1})`. -/
theorem p2m_hasDerivAt_mathieuCylExp' (j : ℕ) (hj₁ : 1 ≤ j) (hj₄ : j ≤ 4) (μ : ℂ) {h : ℂ}
    (hh : h ≠ 0) (z : ℂ) :
    HasDerivAt (fun z => mathieuCylExp j μ h z)
      (h * Complex.exp z / 2 * (mathieuCylExp j (μ - 1) h z - mathieuCylExp j (μ + 1) h z)) z := by
  convert p2m_hasDerivAt_mathieuCylExp j hj₁ hj₄ μ hh z using 1
  have hr := p2m_mathieuCylExp_rec j hj₁ hj₄ μ hh z
  have hy : h * Complex.exp z ≠ 0 := mul_ne_zero hh (Complex.exp_ne_zero z)
  have hr' : h * Complex.exp z * (mathieuCylExp j (μ - 1) h z + mathieuCylExp j (μ + 1) h z) =
      2 * μ * mathieuCylExp j μ h z := by
    rw [hr]; field_simp
  linear_combination (1 / 2 : ℂ) * hr'

/-- Symmetric form for `J_k(h e^{-z})`: `d/dz = -(h e^{-z} / 2)(J_{k-1} - J_{k+1})`. -/
theorem p2m_hasDerivAt_besselJExp_neg (μ : ℂ) {h : ℂ} (hh : h ≠ 0) (z : ℂ) :
    HasDerivAt (fun z => besselJExp μ h (-z))
      (-(h * Complex.exp (-z) / 2 *
        (besselJExp (μ - 1) h (-z) - besselJExp (μ + 1) h (-z)))) z := by
  have h1 := (p2m_hasDerivAt_mathieuCylExp' 1 le_rfl (by norm_num) μ hh (-z)).comp z
    (hasDerivAt_neg z)
  simp only [mathieuCylExp] at h1
  convert h1 using 1
  · rfl
  · ring

/-- Uniform version of `p2m_growth_int` with explicit constants. -/
theorem p2m_growth_int_unif {u : ℤ → ℂ} {ν w : ℂ} {C U : ℝ} (hw : w ≠ 0) (hC : 1 ≤ C)
    (hCw : 2 * (‖ν‖ + 1) / ‖w‖ ≤ C) (hU1 : ‖u (-1)‖ ≤ U) (hU0 : ‖u 0‖ ≤ U) (hU2 : ‖u 1‖ ≤ U)
    (hu : ∀ k : ℤ, u (k - 1) + u (k + 1) = 2 * (ν + k) / w * u k) (k : ℤ) :
    ‖u k‖ ≤ U * (2 * C) * (4 * C) ^ k.natAbs * k.natAbs ! := by
  have hw' : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hCn : ∀ (n : ℕ) (s : ℂ), ‖s‖ ≤ ‖ν‖ + n → 2 * ‖s‖ / ‖w‖ ≤ C * (n + 1) := by
    intro n s hs
    have h1 : 2 * (‖ν‖ + 1) / ‖w‖ ≤ C := hCw
    have h2 : 2 * ‖s‖ / ‖w‖ ≤ 2 * (‖ν‖ + 1) / ‖w‖ * (n + 1) := by
      rw [div_mul_eq_mul_div]
      apply div_le_div_of_nonneg_right _ hw'.le
      nlinarith [norm_nonneg ν, (n.cast_nonneg : (0 : ℝ) ≤ n)]
    calc 2 * ‖s‖ / ‖w‖ ≤ 2 * (‖ν‖ + 1) / ‖w‖ * (n + 1) := h2
      _ ≤ C * (n + 1) := by gcongr
  have hstep : ∀ (k : ℤ) (n : ℕ), ‖ν + k‖ ≤ ‖ν‖ + n → ∀ x y : ℂ, x + y = 2 * (ν + k) / w * u k →
      ‖y‖ ≤ C * (n + 1) * ‖u k‖ + ‖x‖ := by
    intro k n hk x y hxy
    have : y = 2 * (ν + k) / w * u k - x := by linear_combination hxy
    rw [this]
    calc ‖2 * (ν + k) / w * u k - x‖ ≤ ‖2 * (ν + k) / w * u k‖ + ‖x‖ := norm_sub_le _ _
      _ = 2 * ‖ν + k‖ / ‖w‖ * ‖u k‖ + ‖x‖ := by
        rw [norm_mul, norm_div, norm_mul, Complex.norm_two]
      _ ≤ C * (n + 1) * ‖u k‖ + ‖x‖ := by gcongr; exact hCn n _ hk
  -- forward: a n = u (n - 1)
  have hf := p2m_growth_nat (a := fun n : ℕ => u ((n : ℤ) - 1)) hC (fun n => by
    have := hstep n n (by
      calc ‖ν + (n : ℤ)‖ ≤ ‖ν‖ + ‖((n : ℤ) : ℂ)‖ := norm_add_le _ _
        _ = ‖ν‖ + n := by simp) (u ((n : ℤ) - 1)) (u ((n : ℤ) + 1)) (hu n)
    convert this using 3 <;> push_cast <;> ring_nf)
  -- backward: b n = u (1 - n)
  have hb := p2m_growth_nat (a := fun n : ℕ => u (1 - (n : ℤ))) hC (fun n => by
    have := hstep (-(n : ℤ)) n (by
      calc ‖ν + ((-(n : ℤ) : ℤ) : ℂ)‖ ≤ ‖ν‖ + ‖((-(n : ℤ) : ℤ) : ℂ)‖ := norm_add_le _ _
        _ = ‖ν‖ + n := by simp) (u (-(n : ℤ) + 1)) (u (-(n : ℤ) - 1)) (by
          rw [add_comm]; exact hu (-(n : ℤ)))
    convert this using 3 <;> push_cast <;> ring_nf)
  set E₁ := max ‖u ((0 : ℕ) - 1 : ℤ)‖ ‖u ((1 : ℕ) - 1 : ℤ)‖
  set E₂ := max ‖u (1 - (0 : ℕ) : ℤ)‖ ‖u (1 - (1 : ℕ) : ℤ)‖
  have hE₁U : E₁ ≤ U := max_le (by simpa using hU1) (by simpa using hU0)
  have hE₂U : E₂ ≤ U := max_le (by simpa using hU2) (by simpa using hU0)
  have hfac : ∀ m : ℕ, ((m + 1) ! : ℝ) ≤ 2 ^ m * m ! := by
    intro m
    rw [Nat.factorial_succ]; push_cast
    have : (m : ℝ) + 1 ≤ 2 ^ m := by
      have : m + 1 ≤ 2 ^ m := Nat.lt_two_pow_self
      exact_mod_cast this
    have hp : (0 : ℝ) ≤ (Nat.factorial m : ℝ) := by positivity
    nlinarith
  have hE0 : 0 ≤ E₁ := (norm_nonneg _).trans (le_max_left _ _)
  have hC2 : 0 ≤ 2 * C := by linarith
  have hU : 0 ≤ U := hE0.trans hE₁U
  rcases Int.eq_nat_or_neg k with ⟨m, rfl | rfl⟩
  · have := hf (m + 1)
    simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] at this
    simp only [Int.natAbs_natCast]
    calc ‖u m‖ ≤ E₁ * (2 * C) ^ (m + 1) * (m + 1) ! := this
      _ ≤ U * (2 * C) ^ (m + 1) * (2 ^ m * m !) := by gcongr; exact hfac m
      _ = _ := by
        have h4 : (2 : ℝ) ^ (m * 2) = 4 ^ m := by rw [pow_mul']; norm_num
        ring_nf; rw [h4]
  · have := hb (m + 1)
    rw [show (1 : ℤ) - ((m + 1 : ℕ) : ℤ) = -(m : ℤ) by push_cast; ring] at this
    simp only [Int.natAbs_neg, Int.natAbs_natCast]
    have hE0' : 0 ≤ E₂ := (norm_nonneg _).trans (le_max_left _ _)
    calc ‖u (-(m : ℤ))‖ ≤ E₂ * (2 * C) ^ (m + 1) * (m + 1) ! := this
      _ ≤ U * (2 * C) ^ (m + 1) * (2 ^ m * m !) := by gcongr; exact hfac m
      _ = _ := by
        have h4 : (2 : ℝ) ^ (m * 2) = 4 ^ m := by rw [pow_mul']; norm_num
        ring_nf; rw [h4]

/-- `k ↦ J_k(h e^{-z})`. -/
def p2m_Jz (h z : ℂ) : ℤ → ℂ := fun k => besselJExp k h (-z)

/-- `k ↦ 𝒞^{(j)}_{ν+k}(h e^z)`. -/
def p2m_Cz (j : ℕ) (ν h z : ℂ) : ℤ → ℂ := fun k => mathieuCylExp j (ν + k) h z

theorem p2m_continuous_mathieuCylExp (j : ℕ) (hj₁ : 1 ≤ j) (hj₄ : j ≤ 4) (μ : ℂ) {h : ℂ}
    (hh : h ≠ 0) : Continuous fun z => mathieuCylExp j μ h z :=
  continuous_iff_continuousAt.mpr fun z =>
    (p2m_hasDerivAt_mathieuCylExp j hj₁ hj₄ μ hh z).continuousAt

/-- Locally uniform bound for the cross-product terms with any shifts `α`, `β`. -/
theorem p2m_fam_locally_uniform (j : ℕ) (hj₁ : 1 ≤ j) (hj₄ : j ≤ 4) (ν : ℂ) {h : ℂ}
    (hh : h ≠ 0) {c : ℤ → ℂ} {Cc K : ℝ} (hCc : 0 ≤ Cc) (hK : 0 ≤ K)
    (hc : ∀ m : ℤ, ‖c m‖ * (m.natAbs ! : ℝ) ^ 2 ≤ Cc * K ^ m.natAbs) {S : Set ℂ}
    (hS : IsCompact S) (α β : ℤ) :
    ∃ u : ℤ → ℝ, Summable u ∧
      ∀ ℓ, ∀ z ∈ S, ‖p2m_fam c (p2m_Jz h z) (p2m_Cz j ν h z) α β ℓ‖ ≤ u ℓ := by
  obtain ⟨R, hR⟩ := hS.exists_bound_of_continuousOn
    (f := fun z => h * Complex.exp (-z)) (by fun_prop)
  have hy0 : ∀ z, ‖h * Complex.exp z‖ ≠ 0 := fun z =>
    norm_ne_zero_iff.mpr (mul_ne_zero hh (Complex.exp_ne_zero z))
  obtain ⟨C0, hC0⟩ := hS.exists_bound_of_continuousOn
    (f := fun z => 2 * (‖ν‖ + 1) / ‖h * Complex.exp z‖)
    ((continuous_const.div (by fun_prop) hy0).continuousOn)
  have hCcont := fun k : ℤ => p2m_continuous_mathieuCylExp j hj₁ hj₄ (ν + k) hh
  obtain ⟨U1, hU1⟩ := hS.exists_bound_of_continuousOn (hCcont (-1)).continuousOn
  obtain ⟨U0, hU0⟩ := hS.exists_bound_of_continuousOn (hCcont 0).continuousOn
  obtain ⟨U2, hU2⟩ := hS.exists_bound_of_continuousOn (hCcont 1).continuousOn
  set C : ℝ := max 1 C0
  set U : ℝ := max (max U1 U0) (max U2 0)
  set B : ℝ := max 1 (R / 2)
  set EJ : ℝ := Real.exp (R ^ 2 / 4)
  have hC : 1 ≤ C := le_max_left _ _
  have hU : 0 ≤ U := le_max_of_le_right (le_max_right _ _)
  have hB : 1 ≤ B := le_max_left _ _
  have hA : 1 ≤ 4 * C := by linarith
  have hEC : 0 ≤ U * (2 * C) := by positivity
  have hJ : ∀ z ∈ S, ∀ k : ℤ, ‖p2m_Jz h z k‖ ≤ EJ * B ^ k.natAbs := by
    intro z hz k
    simp only [p2m_Jz]
    rw [p1c_besselJExp_intCast]
    refine (Complex.norm_besselJ_intCast_le k _).trans ?_
    have hx := hR z hz
    have hx0 := norm_nonneg (h * Complex.exp (-z))
    refine mul_le_mul (Real.exp_le_exp.mpr (by gcongr)) ?_ (by positivity) (by positivity)
    calc (‖h * Complex.exp (-z)‖ / 2) ^ k.natAbs / (k.natAbs ! : ℝ)
          ≤ (‖h * Complex.exp (-z)‖ / 2) ^ k.natAbs :=
          div_le_self (by positivity) (Nat.one_le_cast.mpr (Nat.factorial_pos _))
      _ ≤ B ^ k.natAbs := pow_le_pow_left₀ (by positivity)
          (le_max_of_le_right (by linarith)) _
  have hCb : ∀ z ∈ S, ∀ k : ℤ,
      ‖p2m_Cz j ν h z k‖ ≤ U * (2 * C) * (4 * C) ^ k.natAbs * (k.natAbs ! : ℝ) := by
    intro z hz k
    have hy : h * Complex.exp z ≠ 0 := mul_ne_zero hh (Complex.exp_ne_zero z)
    refine p2m_growth_int_unif (ν := ν) hy hC ?_ ?_ ?_ ?_ ?_ k
    · exact ((Real.norm_eq_abs _ ▸ le_abs_self _).trans (hC0 z hz)).trans (le_max_right _ _)
    · simp only [p2m_Cz]
      exact (by simpa using hU1 z hz : ‖mathieuCylExp j (ν + ((-1 : ℤ) : ℂ)) h z‖ ≤ U1).trans
        (le_max_of_le_left (le_max_left _ _))
    · simp only [p2m_Cz]
      exact (by simpa using hU0 z hz : ‖mathieuCylExp j (ν + ((0 : ℤ) : ℂ)) h z‖ ≤ U0).trans
        (le_max_of_le_left (le_max_right _ _))
    · simp only [p2m_Cz]
      exact (by simpa using hU2 z hz : ‖mathieuCylExp j (ν + ((1 : ℤ) : ℂ)) h z‖ ≤ U2).trans
        (le_max_of_le_right (le_max_left _ _))
    · intro k
      have := p2m_mathieuCylExp_rec j hj₁ hj₄ (ν + k) hh z
      simp only [p2m_Cz]
      push_cast
      rw [← add_sub_assoc, ← add_assoc]
      exact this
  refine ⟨fun ℓ => (Cc * EJ * (U * (2 * C)) * B ^ α.natAbs * (2 * (4 * C)) ^ β.natAbs *
      (β.natAbs ! : ℝ)) * ((2 * K * B * (4 * C)) ^ ℓ.natAbs / (ℓ.natAbs ! : ℝ)),
    (p2m_summable_pow_div_factorial_int _).mul_left _, fun ℓ z hz => ?_⟩
  exact p2m_fam_bound hCc hK (Real.exp_pos _).le hB hEC hA hc (hJ z hz) (hCb z hz) α β ℓ

/-! ### The modified Mathieu equation for the cross-product series -/

/-- Factorial decay of the coefficients `c^ν_{2m}(h²)` for admissible `(ν, h)`, `h ≠ 0`. -/
theorem p2m_coeff_decay {ν h : ℂ} (hν : ModMathieuAdmissible ν h) (hh : h ≠ 0) :
    ∃ Cc K : ℝ, 0 ≤ Cc ∧ 0 ≤ K ∧ ∀ m : ℤ,
      ‖mathieuMeCoeff ν (h ^ 2) m‖ * (m.natAbs ! : ℝ) ^ 2 ≤ Cc * K ^ m.natAbs := by
  obtain ⟨hrec, M, hM⟩ := p2m_coeff_facts hν
  exact p2m_decay_int (pow_ne_zero 2 hh) hM hrec

theorem p2m_modMathieuTerm_eq_fam (j : ℕ) (ν z h : ℂ) (n : ℤ) :
    modMathieuTerm j ν z h n =
      p2m_fam (mathieuMeCoeff ν (h ^ 2)) (p2m_Jz h z) (p2m_Cz j ν h z) (-n) n := by
  funext ℓ
  simp only [modMathieuTerm, p2m_fam, p2m_Jz, p2m_Cz]
  rw [show ℓ + -n = ℓ - n by ring]
  push_cast
  ring_nf

/-- Proof of `modMathieuTerm_locally_uniform` (§28.24). -/
theorem p2m_modMathieuTerm_locally_uniform (j : ℕ) (hj₁ : 1 ≤ j) (hj₄ : j ≤ 4) {ν h : ℂ}
    (hν : ModMathieuAdmissible ν h) (hh : h ≠ 0) (n : ℤ) {K : Set ℂ} (hK : IsCompact K) :
    ∃ u : ℤ → ℝ, Summable u ∧ ∀ ℓ, ∀ z ∈ K, ‖modMathieuTerm j ν z h n ℓ‖ ≤ u ℓ := by
  obtain ⟨Cc, K', hCc, hK', hc⟩ := p2m_coeff_decay hν hh
  obtain ⟨u, hu, hle⟩ := p2m_fam_locally_uniform j hj₁ hj₄ ν hh hCc hK' hc hK (-n) n
  exact ⟨u, hu, fun ℓ z hz => by rw [p2m_modMathieuTerm_eq_fam]; exact hle ℓ z hz⟩

/-- The `z`-derivative of a cross-product term, in terms of the neighbouring terms. -/
theorem p2m_hasDerivAt_fam (j : ℕ) (hj₁ : 1 ≤ j) (hj₄ : j ≤ 4) (ν : ℂ) {h : ℂ} (hh : h ≠ 0)
    (c : ℤ → ℂ) (α β ℓ : ℤ) (z : ℂ) :
    HasDerivAt (fun z => p2m_fam c (p2m_Jz h z) (p2m_Cz j ν h z) α β ℓ)
      (-(h * Complex.exp (-z) / 2) * (p2m_fam c (p2m_Jz h z) (p2m_Cz j ν h z) (α - 1) β ℓ -
          p2m_fam c (p2m_Jz h z) (p2m_Cz j ν h z) (α + 1) β ℓ) +
        h * Complex.exp z / 2 * (p2m_fam c (p2m_Jz h z) (p2m_Cz j ν h z) α (β - 1) ℓ -
          p2m_fam c (p2m_Jz h z) (p2m_Cz j ν h z) α (β + 1) ℓ)) z := by
  have hJ := p2m_hasDerivAt_besselJExp_neg ((ℓ + α : ℤ) : ℂ) hh z
  have hC := p2m_hasDerivAt_mathieuCylExp' j hj₁ hj₄ (ν + ((β + ℓ : ℤ) : ℂ)) hh z
  have := (hJ.const_mul ((-1 : ℂ) ^ ℓ * c ℓ)).mul hC
  simp only [p2m_fam, p2m_Jz, p2m_Cz]
  convert this using 1
  rw [show ((ℓ + (α - 1) : ℤ) : ℂ) = ((ℓ + α : ℤ) : ℂ) - 1 by push_cast; ring,
    show ((ℓ + (α + 1) : ℤ) : ℂ) = ((ℓ + α : ℤ) : ℂ) + 1 by push_cast; ring,
    show ν + ((β - 1 + ℓ : ℤ) : ℂ) = ν + ((β + ℓ : ℤ) : ℂ) - 1 by push_cast; ring,
    show ν + ((β + 1 + ℓ : ℤ) : ℂ) = ν + ((β + ℓ : ℤ) : ℂ) + 1 by push_cast; ring]
  ring

/-- The cross-product series with shifts `α`, `β`:
`F_{α,β}(z) = ∑_ℓ (-1)^ℓ c_ℓ J_{ℓ+α}(h e^{-z}) 𝒞_{ν+β+ℓ}(h e^z)`. -/
def p2m_F (j : ℕ) (ν h : ℂ) (c : ℤ → ℂ) (α β : ℤ) (z : ℂ) : ℂ :=
  ∑' ℓ, p2m_fam c (p2m_Jz h z) (p2m_Cz j ν h z) α β ℓ

theorem p2m_hasSum_F (j : ℕ) (hj₁ : 1 ≤ j) (hj₄ : j ≤ 4) (ν : ℂ) {h : ℂ} (hh : h ≠ 0)
    {c : ℤ → ℂ} {Cc K : ℝ} (hCc : 0 ≤ Cc) (hK : 0 ≤ K)
    (hc : ∀ m : ℤ, ‖c m‖ * (m.natAbs ! : ℝ) ^ 2 ≤ Cc * K ^ m.natAbs) (α β : ℤ) (z : ℂ) :
    HasSum (fun ℓ => p2m_fam c (p2m_Jz h z) (p2m_Cz j ν h z) α β ℓ) (p2m_F j ν h c α β z) := by
  obtain ⟨u, hu, hle⟩ := p2m_fam_locally_uniform j hj₁ hj₄ ν hh hCc hK hc
    (isCompact_singleton (x := z)) α β
  exact (Summable.of_norm_bounded hu fun ℓ => hle ℓ z rfl).hasSum

/-- The derivative of `F_{α,β}`:
`F' = -(x/2)(F_{α-1,β} - F_{α+1,β}) + (y/2)(F_{α,β-1} - F_{α,β+1})`,
`x = h e^{-z}`, `y = h e^z`. -/
theorem p2m_hasDerivAt_F (j : ℕ) (hj₁ : 1 ≤ j) (hj₄ : j ≤ 4) (ν : ℂ) {h : ℂ} (hh : h ≠ 0)
    {c : ℤ → ℂ} {Cc K : ℝ} (hCc : 0 ≤ Cc) (hK : 0 ≤ K)
    (hc : ∀ m : ℤ, ‖c m‖ * (m.natAbs ! : ℝ) ^ 2 ≤ Cc * K ^ m.natAbs) (α β : ℤ) (z : ℂ) :
    HasDerivAt (p2m_F j ν h c α β)
      (-(h * Complex.exp (-z) / 2) * (p2m_F j ν h c (α - 1) β z - p2m_F j ν h c (α + 1) β z) +
        h * Complex.exp z / 2 * (p2m_F j ν h c α (β - 1) z - p2m_F j ν h c α (β + 1) z)) z := by
  obtain ⟨u, hu, hle⟩ := p2m_fam_locally_uniform j hj₁ hj₄ ν hh hCc hK hc
    (isCompact_closedBall z 1) α β
  have hdiff : ∀ ℓ, DifferentiableOn ℂ
      (fun w => p2m_fam c (p2m_Jz h w) (p2m_Cz j ν h w) α β ℓ) (Metric.ball z 1) :=
    fun ℓ w _ =>
      (p2m_hasDerivAt_fam j hj₁ hj₄ ν hh c α β ℓ w).differentiableAt.differentiableWithinAt
  have hle' : ∀ ℓ w, w ∈ Metric.ball z 1 →
      ‖p2m_fam c (p2m_Jz h w) (p2m_Cz j ν h w) α β ℓ‖ ≤ u ℓ :=
    fun ℓ w hw => hle ℓ w (Metric.ball_subset_closedBall hw)
  have hz : z ∈ Metric.ball z 1 := Metric.mem_ball_self one_pos
  have hs := Complex.hasSum_deriv_of_summable_norm hu hdiff Metric.isOpen_ball hle' hz
  have hd : DifferentiableAt ℂ (p2m_F j ν h c α β) z :=
    (Complex.differentiableOn_tsum_of_summable_norm hu hdiff Metric.isOpen_ball
      hle').differentiableAt
      (Metric.isOpen_ball.mem_nhds hz)
  have e : ∀ ℓ, deriv (fun w => p2m_fam c (p2m_Jz h w) (p2m_Cz j ν h w) α β ℓ) z =
      -(h * Complex.exp (-z) / 2) * (p2m_fam c (p2m_Jz h z) (p2m_Cz j ν h z) (α - 1) β ℓ -
          p2m_fam c (p2m_Jz h z) (p2m_Cz j ν h z) (α + 1) β ℓ) +
        h * Complex.exp z / 2 * (p2m_fam c (p2m_Jz h z) (p2m_Cz j ν h z) α (β - 1) ℓ -
          p2m_fam c (p2m_Jz h z) (p2m_Cz j ν h z) α (β + 1) ℓ) :=
    fun ℓ => (p2m_hasDerivAt_fam j hj₁ hj₄ ν hh c α β ℓ z).deriv
  simp_rw [e] at hs
  have hF := fun a b => p2m_hasSum_F j hj₁ hj₄ ν hh hCc hK hc a b z
  have hs2 := (((hF (α - 1) β).sub (hF (α + 1) β)).mul_left (-(h * Complex.exp (-z) / 2))).add
    (((hF α (β - 1)).sub (hF α (β + 1))).mul_left (h * Complex.exp z / 2))
  rw [← hs.unique hs2]
  exact hd.hasDerivAt

/-- `(x/2)(A_{k-1} - A_{k+1}) + (x²/4)(A_{k-2} - 2A_k + A_{k+2}) = (k² - x²) A_k` for a solution of
the Bessel order recurrence. -/
theorem p2m_second_alg {x k km kp Am2 Am1 A0 Ap1 Ap2 : ℂ} (hx : x ≠ 0) (hkm : km = k - 1)
    (hkp : kp = k + 1) (r1 : Am2 + A0 = 2 * km / x * Am1) (r0 : Am1 + Ap1 = 2 * k / x * A0)
    (r2 : A0 + Ap2 = 2 * kp / x * Ap1) :
    x / 2 * (Am1 - Ap1) + x ^ 2 / 4 * (Am2 - 2 * A0 + Ap2) = (k ^ 2 - x ^ 2) * A0 := by
  subst hkm hkp
  have e1 : Am2 = 2 * (k - 1) / x * Am1 - A0 := by linear_combination r1
  have e2 : Ap2 = 2 * (k + 1) / x * Ap1 - A0 := by linear_combination r2
  have e0 : Am1 = 2 * k / x * A0 - Ap1 := by linear_combination r0
  rw [e1, e2, e0]
  field_simp
  ring

theorem p2m_Jz_rec {h : ℂ} (hh : h ≠ 0) (z : ℂ) (k : ℤ) :
    p2m_Jz h z (k - 1) + p2m_Jz h z (k + 1) = 2 * k / (h * Complex.exp (-z)) * p2m_Jz h z k := by
  have := p2m_besselJExp_rec (k : ℂ) hh (-z)
  simp only [p2m_Jz]
  push_cast
  exact this

theorem p2m_Cz_rec (j : ℕ) (hj₁ : 1 ≤ j) (hj₄ : j ≤ 4) (ν : ℂ) {h : ℂ} (hh : h ≠ 0) (z : ℂ)
    (k : ℤ) : p2m_Cz j ν h z (k - 1) + p2m_Cz j ν h z (k + 1) =
      2 * (ν + k) / (h * Complex.exp z) * p2m_Cz j ν h z k := by
  have := p2m_mathieuCylExp_rec j hj₁ hj₄ (ν + k) hh z
  simp only [p2m_Cz]
  push_cast
  rw [← add_sub_assoc, ← add_assoc]
  exact this

/-- The cross-product series `F_{-n,n}` solves the modified Mathieu equation 28.20.1 when `c` solves
the recurrence 28.14.4 with eigenvalue `a`. -/
theorem p2m_F_ode (j : ℕ) (hj₁ : 1 ≤ j) (hj₄ : j ≤ 4) (ν : ℂ) {h : ℂ} (hh : h ≠ 0)
    {c : ℤ → ℂ} {Cc K : ℝ} (hCc : 0 ≤ Cc) (hK : 0 ≤ K)
    (hc : ∀ m : ℤ, ‖c m‖ * (m.natAbs ! : ℝ) ^ 2 ≤ Cc * K ^ m.natAbs) {a : ℂ}
    (hrec : ∀ m : ℤ, h ^ 2 * c (m + 1) - (a - (ν + 2 * m) ^ 2) * c m + h ^ 2 * c (m - 1) = 0)
    (n : ℤ) (z : ℂ) :
    HasDerivAt (deriv (p2m_F j ν h c (-n) n))
      ((a - 2 * h ^ 2 * Complex.cosh (2 * z)) * p2m_F j ν h c (-n) n z) z := by
  have hF := fun α β w => p2m_hasDerivAt_F j hj₁ hj₄ ν hh hCc hK hc α β w
  have hS := fun α β => p2m_hasSum_F j hj₁ hj₄ ν hh hCc hK hc α β z
  have hderiv : deriv (p2m_F j ν h c (-n) n) = fun w =>
      -(h * Complex.exp (-w) / 2) * (p2m_F j ν h c (-n - 1) n w - p2m_F j ν h c (-n + 1) n w) +
        h * Complex.exp w / 2 * (p2m_F j ν h c (-n) (n - 1) w - p2m_F j ν h c (-n) (n + 1) w) :=
    funext fun w => (hF (-n) n w).deriv
  rw [hderiv]
  have hx' : HasDerivAt (fun w => -(h * Complex.exp (-w) / 2)) (h * Complex.exp (-z) / 2) z := by
    have := (((Complex.hasDerivAt_exp (-z)).comp z (hasDerivAt_neg z)).const_mul h).div_const 2
      |>.neg
    convert this using 1
    · funext w; simp
    · ring
  have hy' : HasDerivAt (fun w => h * Complex.exp w / 2) (h * Complex.exp z / 2) z :=
    ((Complex.hasDerivAt_exp z).const_mul h).div_const 2
  have hG := (hx'.mul ((hF (-n - 1) n z).sub (hF (-n + 1) n z))).add
    (hy'.mul ((hF (-n) (n - 1) z).sub (hF (-n) (n + 1) z)))
  convert hG using 1
  set x := h * Complex.exp (-z) with hxdef
  set y := h * Complex.exp z with hydef
  have hx : x ≠ 0 := mul_ne_zero hh (Complex.exp_ne_zero _)
  have hy : y ≠ 0 := mul_ne_zero hh (Complex.exp_ne_zero _)
  have hxy : x * y = h ^ 2 := by
    rw [hxdef, hydef, mul_mul_mul_comm, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
    ring
  have hcosh : 2 * h ^ 2 * Complex.cosh (2 * z) = x ^ 2 + y ^ 2 := by
    rw [mul_comm 2 (h ^ 2), mul_assoc, Complex.two_cosh, hxdef, hydef, mul_pow, mul_pow,
      ← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
    push_cast
    ring_nf
  have hD := fun α β => (((hS (α - 1) β).sub (hS (α + 1) β)).mul_left (-(x / 2))).add
    (((hS α (β - 1)).sub (hS α (β + 1))).mul_left (y / 2))
  have hV := ((((hS (-n - 1) n).sub (hS (-n + 1) n)).mul_left (x / 2)).add
    (((hD (-n - 1) n).sub (hD (-n + 1) n)).mul_left (-(x / 2)))).add
    ((((hS (-n) (n - 1)).sub (hS (-n) (n + 1))).mul_left (y / 2)).add
    (((hD (-n) (n - 1)).sub (hD (-n) (n + 1))).mul_left (y / 2)))
  have hsh1 : HasSum (fun ℓ => p2m_fam c (p2m_Jz h z) (p2m_Cz j ν h z) (-n - 1) (n - 1) (ℓ + 1))
      (p2m_F j ν h c (-n - 1) (n - 1) z) :=
    ((Equiv.addRight (1 : ℤ)).hasSum_iff
      (f := fun ℓ => p2m_fam c (p2m_Jz h z) (p2m_Cz j ν h z) (-n - 1) (n - 1) ℓ)).mpr
      (hS (-n - 1) (n - 1))
  have hsh2 : HasSum (fun ℓ => p2m_fam c (p2m_Jz h z) (p2m_Cz j ν h z) (-n + 1) (n + 1) (ℓ - 1))
      (p2m_F j ν h c (-n + 1) (n + 1) z) :=
    ((Equiv.subRight (1 : ℤ)).hasSum_iff
      (f := fun ℓ => p2m_fam c (p2m_Jz h z) (p2m_Cz j ν h z) (-n + 1) (n + 1) ℓ)).mpr
      (hS (-n + 1) (n + 1))
  have hW := (((hS (-n) n).mul_left (a - x ^ 2 - y ^ 2)).add
    ((hsh1.sub (hS (-n - 1) (n - 1))).mul_left (x * y))).add
    ((hsh2.sub (hS (-n + 1) (n + 1))).mul_left (x * y))
  rw [hcosh]
  simp only [Pi.sub_apply]
  refine (hV.unique ?_).symm
  convert hW using 1
  · funext ℓ
    simp only [p2m_fam]
    simp only [show ℓ + (-n - 1) = ℓ - n - 1 by ring, show ℓ + (-n + 1) = ℓ - n + 1 by ring,
      show ℓ + -n = ℓ - n by ring, show ℓ + (-n - 1 - 1) = ℓ - n - 1 - 1 by ring,
      show ℓ + (-n - 1 + 1) = ℓ - n by ring, show ℓ + (-n + 1 - 1) = ℓ - n by ring,
      show ℓ + (-n + 1 + 1) = ℓ - n + 1 + 1 by ring, show ℓ + 1 + (-n - 1) = ℓ - n by ring,
      show ℓ - 1 + (-n + 1) = ℓ - n by ring, show n - 1 + ℓ = n + ℓ - 1 by ring,
      show n + 1 + ℓ = n + ℓ + 1 by ring, show n - 1 - 1 + ℓ = n + ℓ - 1 - 1 by ring,
      show n - 1 + 1 + ℓ = n + ℓ by ring, show n + 1 - 1 + ℓ = n + ℓ by ring,
      show n + 1 + 1 + ℓ = n + ℓ + 1 + 1 by ring, show n - 1 + (ℓ + 1) = n + ℓ by ring,
      show n + 1 + (ℓ - 1) = n + ℓ by ring]
    rw [zpow_add_one₀ (by norm_num : (-1 : ℂ) ≠ 0), zpow_sub_one₀ (by norm_num : (-1 : ℂ) ≠ 0)]
    have rJ1 := p2m_Jz_rec hh z (ℓ - n - 1)
    have rJ0 := p2m_Jz_rec hh z (ℓ - n)
    have rJ2 := p2m_Jz_rec hh z (ℓ - n + 1)
    have rC1 := p2m_Cz_rec j hj₁ hj₄ ν hh z (n + ℓ - 1)
    have rC0 := p2m_Cz_rec j hj₁ hj₄ ν hh z (n + ℓ)
    have rC2 := p2m_Cz_rec j hj₁ hj₄ ν hh z (n + ℓ + 1)
    simp only [sub_add_cancel, add_sub_cancel_right] at rJ1 rJ2 rC1 rC2
    have hP := p2m_second_alg hx (k := ((ℓ - n : ℤ) : ℂ)) (by push_cast; ring) (by push_cast; ring)
      rJ1 rJ0 rJ2
    have hQ := p2m_second_alg hy (k := ν + ((n + ℓ : ℤ) : ℂ)) (by push_cast; ring)
      (by push_cast; ring) rC1 rC0 rC2
    have e1 : x * (p2m_Jz h z (ℓ - n - 1) + p2m_Jz h z (ℓ - n + 1)) =
        2 * ((ℓ - n : ℤ) : ℂ) * p2m_Jz h z (ℓ - n) := by
      rw [rJ0, hxdef]; field_simp
    have e2 : y * (p2m_Cz j ν h z (n + ℓ - 1) + p2m_Cz j ν h z (n + ℓ + 1)) =
        2 * (ν + ((n + ℓ : ℤ) : ℂ)) * p2m_Cz j ν h z (n + ℓ) := by
      rw [rC0, hydef]; field_simp
    have hr := hrec ℓ
    rw [← hxy] at hr
    push_cast at hP hQ e1 e2
    linear_combination (-1 : ℂ) ^ ℓ * c ℓ * (p2m_Cz j ν h z (n + ℓ) * hP +
      p2m_Jz h z (ℓ - n) * hQ +
      (y * (p2m_Cz j ν h z (n + ℓ - 1) + p2m_Cz j ν h z (n + ℓ + 1)) / 2) * e1 +
      ((ℓ : ℂ) - n) * p2m_Jz h z (ℓ - n) * e2) +
      (-1 : ℂ) ^ ℓ * p2m_Jz h z (ℓ - n) * p2m_Cz j ν h z (n + ℓ) * hr
  · ring

theorem p2m_modMathieuM_eq_F (j : ℕ) (ν h : ℂ) :
    (fun z => modMathieuM j ν z h) = fun z => (mathieuMeCoeff ν (h ^ 2) (modMathieuIndex ν h))⁻¹ *
      p2m_F j ν h (mathieuMeCoeff ν (h ^ 2)) (-modMathieuIndex ν h) (modMathieuIndex ν h) z := by
  funext z
  simp only [modMathieuM, p2m_F, p2m_modMathieuTerm_eq_fam]

/-- Proof of `isModMathieuSolution_modMathieuM` (DLMF §28.20(iii)). -/
theorem p2m_isModMathieuSolution_modMathieuM (j : ℕ) (hj₁ : 1 ≤ j) (hj₄ : j ≤ 4) {ν h : ℂ}
    (hν : ModMathieuAdmissible ν h) (hh : h ≠ 0) :
    IsModMathieuSolution (mathieuLambda ν (h ^ 2)) (h ^ 2) (fun z => modMathieuM j ν z h) := by
  obtain ⟨Cc, K, hCc, hK, hc⟩ := p2m_coeff_decay hν hh
  have hrec := (p2m_coeff_facts hν).1
  set n := modMathieuIndex ν h
  set C := (mathieuMeCoeff ν (h ^ 2) n)⁻¹
  have hF := fun w => p2m_hasDerivAt_F j hj₁ hj₄ ν hh hCc hK hc (-n) n w
  have hdF : Differentiable ℂ (p2m_F j ν h (mathieuMeCoeff ν (h ^ 2)) (-n) n) :=
    fun w => (hF w).differentiableAt
  rw [p2m_modMathieuM_eq_F]
  refine ⟨fun w => (hdF w).const_mul C, fun w => ?_⟩
  have e : deriv (fun z => C * p2m_F j ν h (mathieuMeCoeff ν (h ^ 2)) (-n) n z) =
      fun z => C * deriv (p2m_F j ν h (mathieuMeCoeff ν (h ^ 2)) (-n) n) z :=
    funext fun z => deriv_const_mul _ (hdF z)
  rw [e]
  have := (p2m_F_ode j hj₁ hj₄ ν hh hCc hK hc hrec n w).const_mul C
  convert this using 1
  ring

/-! ### Integer-order cross-product expansions (28.24.2–28.24.5) -/

/-- `Y_{-μ} = cos(μπ) Y_μ + sin(μπ) J_μ` for the continued functions, every order. -/
theorem p2m_besselYExp_neg (μ : ℂ) {h : ℂ} (hh : h ≠ 0) (z : ℂ) :
    besselYExp (-μ) h z = Complex.cos (μ * π) * besselYExp μ h z +
      Complex.sin (μ * π) * besselJExp μ h z := by
  have hc := p2m_continuousAt_besselYExp_order hh z
  have hJ := p2m_differentiable_besselJExp_order hh z
  refine DLMF.Confluent.eq_of_continuousAt_of_integerComplement
    (f := fun μ => besselYExp (-μ) h z)
    (g := fun μ => Complex.cos (μ * π) * besselYExp μ h z +
      Complex.sin (μ * π) * besselJExp μ h z)
    ((hc _).comp (by fun_prop : ContinuousAt (fun μ : ℂ => -μ) μ))
    (((by fun_prop : ContinuousAt (fun μ : ℂ => Complex.cos (μ * π)) μ).mul (hc μ)).add
      ((by fun_prop : ContinuousAt (fun μ : ℂ => Complex.sin (μ * π)) μ).mul
        (hJ μ).continuousAt)) (fun c hc' => ?_)
  have hk := DLMF.Confluent.forall_of_mem_integerComplement hc'
  have hk' : ∀ k : ℤ, -c ≠ k := fun k h' => hk (-k) (by push_cast; linear_combination -h')
  have hs := DLMF.Bessel.sin_mul_pi_ne_zero hk
  rw [p2m_besselYExp_of_not_int hk', p2m_besselYExp_of_not_int hk]
  simp only [p2m_besselDExp, neg_neg, neg_mul, Complex.cos_neg, Complex.sin_neg]
  field_simp
  have := Complex.sin_sq_add_cos_sq (c * π)
  linear_combination (-besselJExp c h z) * this

/-- `Y_{-k} = (-1)^k Y_k` for integer `k`. -/
theorem p2m_besselYExp_neg_intCast (k : ℤ) {h : ℂ} (hh : h ≠ 0) (z : ℂ) :
    besselYExp ((-k : ℤ) : ℂ) h z = (-1 : ℂ) ^ k * besselYExp k h z := by
  rw [Int.cast_neg, p2m_besselYExp_neg _ hh, DLMF.Bessel.cos_int_mul_pi_complex,
    DLMF.Bessel.sin_int_mul_pi_complex, zero_mul, add_zero]

theorem p2m_mathieuCylExp_neg_intCast (j : ℕ) (hj₁ : 1 ≤ j) (hj₄ : j ≤ 4) (k : ℤ) {h : ℂ}
    (hh : h ≠ 0) (z : ℂ) :
    mathieuCylExp j ((-k : ℤ) : ℂ) h z = (-1 : ℂ) ^ k * mathieuCylExp j k h z := by
  have hJ := p1c_besselJExp_neg_intCast k h z
  have hY := p2m_besselYExp_neg_intCast k hh z
  interval_cases j <;> simp only [mathieuCylExp, hJ, hY] <;> ring

/-- `ce_N(z + π) = (-1)^N ce_N(z)`. -/
theorem p2m_mathieuCe_add_pi (N : ℕ) (z : ℂ) (q : ℝ) :
    mathieuCe N (z + π) q = (-1 : ℂ) ^ N * mathieuCe N z q := by
  rcases Nat.even_or_odd' N with ⟨t, rfl | rfl⟩
  · rw [mathieuCe_even_add_pi, pow_mul]; simp
  · rw [mathieuCe_odd_add_pi, pow_succ, pow_mul]; simp

/-- `se_N(z + π) = (-1)^N se_N(z)`, `N ≥ 1`. -/
theorem p2m_mathieuSe_add_pi {N : ℕ} (hN : N ≠ 0) (z : ℂ) (q : ℝ) :
    mathieuSe N (z + π) q = (-1 : ℂ) ^ N * mathieuSe N z q := by
  rcases Nat.even_or_odd' N with ⟨t, rfl | rfl⟩
  · obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
    rw [show 2 * (s + 1) = 2 * s + 2 by ring, mathieuSe_even_add_pi, pow_add, pow_mul]; simp
  · rw [mathieuSe_odd_add_pi, pow_succ, pow_mul]; simp

theorem p2m_cos_add_int_mul_pi (K : ℤ) (x : ℂ) :
    Complex.cos (K * (x + π)) = (-1 : ℂ) ^ K * Complex.cos (K * x) := by
  rw [mul_add, Complex.cos_add, DLMF.Bessel.cos_int_mul_pi_complex,
    DLMF.Bessel.sin_int_mul_pi_complex]; ring

theorem p2m_sin_add_int_mul_pi (K : ℤ) (x : ℂ) :
    Complex.sin (K * (x + π)) = (-1 : ℂ) ^ K * Complex.sin (K * x) := by
  rw [mul_add, Complex.sin_add, DLMF.Bessel.cos_int_mul_pi_complex,
    DLMF.Bessel.sin_int_mul_pi_complex]; ring

theorem p2m_negOnePow_mul_eq_one {N : ℕ} {K : ℤ} (hK : ∃ k : ℤ, K = N + 2 * k) :
    (-1 : ℂ) ^ N * (-1 : ℂ) ^ K = 1 := by
  obtain ⟨k, rfl⟩ := hK
  rw [← zpow_natCast, ← zpow_add₀ (by norm_num), show (N : ℤ) + (N + 2 * k) = 2 * (N + k) by
    ring, zpow_mul]
  simp

/-- An integrand `f` with `f(x + π) = f(x)` and `f(π - x) = -f(x)` integrates to `0` over
`[0, π]`. -/
theorem p2m_integral_eq_zero_of_reflect {f : ℝ → ℂ} (hf : ∀ x, f (π - x) = -f x) :
    ∫ x in (0 : ℝ)..π, f x = 0 := by
  have h1 : ∫ x in (0 : ℝ)..π, f x = ∫ x in (0 : ℝ)..π, f (π - x) := by
    rw [intervalIntegral.integral_comp_sub_left]; simp
  simp only [hf, intervalIntegral.integral_neg] at h1
  linear_combination h1 / 2

/-- Doubling the interval for a `π`-periodic integrand. -/
theorem p2m_integral_two_pi {f : ℝ → ℂ} (hc : Continuous f) (hf : ∀ x, f (x + π) = f x) :
    ∫ x in (0 : ℝ)..2 * π, f x = 2 * ∫ x in (0 : ℝ)..π, f x := by
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := π) (hc.intervalIntegrable _ _)
    (hc.intervalIntegrable _ _)]
  have : ∫ x in π..2 * π, f x = ∫ x in (0 : ℝ)..π, f x := by
    have e := intervalIntegral.integral_comp_add_right f (a := 0) (b := π) π
    simp only [hf, zero_add] at e
    rw [show (2 : ℝ) * π = π + π by ring]; exact e.symm
  rw [this]; ring

/-- The integer-order coefficients `c^N_{2k}` of `me_N = √2 ce_N` (`N ≥ 0`) as cosine integrals:
`c^N_{2k}(q) = √2/(2π) ∫₀^{2π} ce_N(x) cos((N+2k)x) dx`. -/
theorem p2m_mathieuMeCoeff_ce (N : ℕ) (q : ℝ) (k : ℤ) :
    mathieuMeCoeff ((N : ℤ) : ℂ) (q : ℂ) k = (Real.sqrt 2 : ℂ) / (2 * π) *
      ∫ x in (0 : ℝ)..2 * π, mathieuCe N x q * Complex.cos (((N + 2 * k : ℤ) : ℂ) * x) := by
  set K : ℤ := N + 2 * k
  have hex : ∃ k' : ℤ, (k' : ℂ) = ((N : ℤ) : ℂ) := ⟨N, rfl⟩
  have hNK : (-1 : ℂ) ^ N * (-1 : ℂ) ^ K = 1 := p2m_negOnePow_mul_eq_one ⟨k, rfl⟩
  have hce := (isMathieuSolution_mathieuCe N q).differentiable
  have hcc : Continuous fun x : ℝ => mathieuCe N x q :=
    hce.continuous.comp Complex.continuous_ofReal
  have hshift : ∀ x : ℝ, mathieuCe N ((x - π : ℝ) : ℂ) q = (-1 : ℂ) ^ N * mathieuCe N x q := by
    intro x
    have := p2m_mathieuCe_add_pi N ((x - π : ℝ) : ℂ) q
    push_cast at this ⊢
    rw [sub_add_cancel] at this
    rw [this, ← mul_assoc, ← mul_pow]; simp
  simp only [mathieuMeCoeff, hex, ite_true, mathieuMe_intCast, mathieuMeInt]
  simp only [Int.natCast_nonneg, ite_true, Int.toNat_natCast]
  rw [show ((N : ℤ) : ℂ) + 2 * (k : ℂ) = (K : ℂ) by push_cast [K]; ring]
  -- the sine part vanishes
  have hsin : ∫ x in (0 : ℝ)..π, mathieuCe N x q * Complex.sin ((K : ℂ) * x) = 0 := by
    refine p2m_integral_eq_zero_of_reflect fun x => ?_
    have hs : Complex.sin ((K : ℂ) * ((x - π : ℝ) : ℂ)) = (-1 : ℂ) ^ K * Complex.sin (K * x) := by
      have := p2m_sin_add_int_mul_pi K ((x - π : ℝ) : ℂ)
      push_cast at this ⊢
      rw [sub_add_cancel] at this
      rw [this, ← mul_assoc, ← mul_zpow]; simp
    rw [show ((π - x : ℝ) : ℂ) = -((x - π : ℝ) : ℂ) by push_cast; ring, mathieuCe_neg, hshift,
      mul_neg, Complex.sin_neg, hs]
    linear_combination (-(mathieuCe N x q * Complex.sin (K * x))) * hNK
  have hcos : ∫ x in (0 : ℝ)..2 * π, mathieuCe N x q * Complex.cos ((K : ℂ) * x) =
      2 * ∫ x in (0 : ℝ)..π, mathieuCe N x q * Complex.cos ((K : ℂ) * x) := by
    refine p2m_integral_two_pi (by fun_prop) fun x => ?_
    push_cast
    rw [p2m_mathieuCe_add_pi, p2m_cos_add_int_mul_pi]
    linear_combination (mathieuCe N x q * Complex.cos (K * x)) * hNK
  have e : ∀ x : ℝ, (Real.sqrt 2 : ℂ) * mathieuCe N x q * Complex.exp (-(I * K * x)) =
      (Real.sqrt 2 : ℂ) * (mathieuCe N x q * Complex.cos ((K : ℂ) * x)) -
        ((Real.sqrt 2 : ℂ) * I) * (mathieuCe N x q * Complex.sin ((K : ℂ) * x)) := by
    intro x
    rw [show -(I * (K : ℂ) * x) = (-((K : ℂ) * x)) * I by ring, Complex.exp_mul_I,
      Complex.cos_neg, Complex.sin_neg]
    ring
  simp_rw [e]
  have i1 : IntervalIntegrable (fun x : ℝ => mathieuCe N x q * Complex.cos ((K : ℂ) * x))
      MeasureTheory.volume 0 π := (by fun_prop : Continuous fun x : ℝ =>
        mathieuCe N x q * Complex.cos ((K : ℂ) * x)).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun x : ℝ => mathieuCe N x q * Complex.sin ((K : ℂ) * x))
      MeasureTheory.volume 0 π := (by fun_prop : Continuous fun x : ℝ =>
        mathieuCe N x q * Complex.sin ((K : ℂ) * x)).intervalIntegrable _ _
  rw [intervalIntegral.integral_sub (i1.const_mul _) (i2.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hsin, hcos]
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp
  ring

theorem p2m_negOnePow_sub (a b : ℤ) : (-1 : ℂ) ^ (a - b) = (-1 : ℂ) ^ a * (-1 : ℂ) ^ b := by
  rw [zpow_sub₀ (by norm_num), div_eq_mul_inv,
    inv_eq_of_mul_eq_one_right (m28b_negOnePow_mul_self b)]

theorem p2m_negOnePow_neg (a : ℤ) : (-1 : ℂ) ^ (-a) = (-1 : ℂ) ^ a := by
  rw [zpow_neg, inv_eq_of_mul_eq_one_right (m28b_negOnePow_mul_self a)]

theorem p2m_sqrt_two_sq : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; push_cast; rfl

/-- Proof of `hasSum_radialMathieuMc_even_cross` (DLMF 28.24.2). -/
theorem p2m_hasSum_radialMathieuMc_even_cross (j : ℕ) (hj₁ : 1 ≤ j) (hj₄ : j ≤ 4) (m s : ℕ)
    {h : ℝ} (hh : 0 < h) (hA : mathieuFourierA (2 * m) (2 * s) (h ^ 2) ≠ 0) (z : ℂ) :
    HasSum (fun ℓ : ℕ => (-1 : ℂ) ^ m * ((-1 : ℂ) ^ ℓ *
        (mathieuFourierA (2 * m) (2 * ℓ) (h ^ 2) / mathieuFourierA (2 * m) (2 * s) (h ^ 2)) *
        (besselJExp ((ℓ : ℤ) - s : ℤ) h (-z) * mathieuCylExp j ((ℓ + s : ℕ) : ℂ) h z +
          besselJExp ((ℓ + s : ℕ) : ℂ) h (-z) * mathieuCylExp j ((ℓ : ℤ) - s : ℤ) h z)))
      (mathieuEpsilon s * radialMathieuMc j (2 * m) z h) := by
  have hh' : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  set N : ℕ := 2 * m with hN
  have hadm : ModMathieuAdmissible ((N : ℕ) : ℂ) (h : ℂ) :=
    Or.inr ⟨⟨N, by push_cast; rfl⟩, by rw [← Complex.ofReal_pow]; exact Complex.ofReal_im _⟩
  have H := p2m_hasSum_modMathieuTerm j hj₁ hj₄ hadm hh' ((s : ℤ) - m) z
  set c := mathieuMeCoeff ((N : ℕ) : ℂ) ((h : ℂ) ^ 2) with hcdef
  set I0 : ℤ → ℂ := fun K => ∫ x in (0 : ℝ)..2 * π,
    mathieuCe N x (h ^ 2) * Complex.cos ((K : ℂ) * x) with hI0
  have hc : ∀ k : ℤ, c k = (Real.sqrt 2 : ℂ) / (2 * π) * I0 (N + 2 * k) := by
    intro k
    have := p2m_mathieuMeCoeff_ce N (h ^ 2) k
    push_cast at this
    rw [hcdef, this]
    simp only [hI0, Int.cast_add, Int.cast_natCast, Int.cast_mul, Int.cast_ofNat]
  have hIneg : ∀ K : ℤ, I0 (-K) = I0 K := by
    intro K; simp only [hI0]; push_cast; simp only [neg_mul, Complex.cos_neg]
  have hAeq : ∀ ℓ : ℕ, mathieuFourierA (2 * m) (2 * ℓ) (h ^ 2) =
      (if ℓ = 0 then 1 / (2 * π) else 1 / π : ℂ) * I0 (2 * ℓ) := by
    intro ℓ
    simp only [mathieuFourierA, hI0, hN]
    push_cast
    simp
  set M := radialMathieuMc j (2 * m) z h
  set f : ℤ → ℂ := fun p => modMathieuTerm j ((N : ℕ) : ℂ) z h ((s : ℤ) - m) (p - m) with hfdef
  have H1 : HasSum f (c ((s : ℤ) - m) * M) :=
    ((Equiv.subRight (m : ℤ)).hasSum_iff
      (f := fun p => modMathieuTerm j ((N : ℕ) : ℂ) z h ((s : ℤ) - m) p)).mpr H
  have hf : ∀ p : ℤ, f p = (-1 : ℂ) ^ p * (-1 : ℂ) ^ (m : ℤ) *
      ((Real.sqrt 2 : ℂ) / (2 * π) * I0 (2 * p)) * besselJExp ((p - s : ℤ) : ℂ) h (-z) *
        mathieuCylExp j ((p + s : ℤ) : ℂ) h z := by
    intro p
    simp only [hfdef, modMathieuTerm]
    rw [← hcdef, hc, p2m_negOnePow_sub, show (N : ℤ) + 2 * (p - m) = 2 * p by simp [hN]; ring,
      show p - m - (s - m) = p - s by ring,
      show ((N : ℕ) : ℂ) + (((s : ℤ) - m : ℤ) : ℂ) + ((p - m : ℤ) : ℂ) = ((p + s : ℤ) : ℂ) by
        simp [hN]; ring]
  have H2 := H1.nat_add_neg
  set A2s := mathieuFourierA (2 * m) (2 * s) (h ^ 2) with hA2s
  set Kc : ℂ := (Real.sqrt 2 : ℂ) / A2s
  have H3 := (H2.mul_left Kc).sub (hasSum_ite_eq (0 : ℕ) (Kc * f 0))
  have hs2 := p2m_sqrt_two_sq
  have hKc : A2s * Kc = (Real.sqrt 2 : ℂ) := by simp only [Kc]; field_simp
  have hfpos : ∀ ℓ : ℕ, f ℓ = (-1 : ℂ) ^ ℓ * (-1 : ℂ) ^ m *
      ((Real.sqrt 2 : ℂ) / (2 * π) * I0 (2 * ℓ)) * besselJExp (((ℓ : ℤ) - s : ℤ) : ℂ) h (-z) *
        mathieuCylExp j (((ℓ : ℤ) + s : ℤ) : ℂ) h z := by
    intro ℓ; rw [hf]; simp only [zpow_natCast]
  have hfneg : ∀ ℓ : ℕ, f (-(ℓ : ℤ)) = (-1 : ℂ) ^ ℓ * (-1 : ℂ) ^ m *
      ((Real.sqrt 2 : ℂ) / (2 * π) * I0 (2 * ℓ)) * besselJExp (((ℓ : ℤ) + s : ℤ) : ℂ) h (-z) *
        mathieuCylExp j (((ℓ : ℤ) - s : ℤ) : ℂ) h z := by
    intro ℓ
    rw [hf, show -(ℓ : ℤ) - s = -((ℓ : ℤ) + s) by ring, show -(ℓ : ℤ) + s = -((ℓ : ℤ) - s) by ring,
      p1c_besselJExp_neg_intCast, p2m_mathieuCylExp_neg_intCast j hj₁ hj₄ _ hh',
      show 2 * -(ℓ : ℤ) = -(2 * ℓ) by ring, hIneg, p2m_negOnePow_neg, zpow_natCast,
      zpow_natCast]
    have hsgn : (-1 : ℂ) ^ ((ℓ : ℤ) + s) * (-1 : ℂ) ^ ((ℓ : ℤ) - s) = 1 := by
      rw [← zpow_add₀ (by norm_num), show (ℓ : ℤ) + s + (ℓ - s) = 2 * ℓ by ring, zpow_mul]
      simp
    linear_combination ((-1 : ℂ) ^ ℓ * (-1 : ℂ) ^ m * ((Real.sqrt 2 : ℂ) / (2 * π) *
      I0 (2 * ℓ)) * besselJExp (((ℓ : ℤ) + s : ℤ) : ℂ) h (-z) *
        mathieuCylExp j (((ℓ : ℤ) - s : ℤ) : ℂ) h z) * hsgn
  convert H3 using 1
  · funext ℓ
    rw [hfpos, hfneg, hAeq, show ((ℓ + s : ℕ) : ℂ) = (((ℓ : ℤ) + s : ℤ) : ℂ) by push_cast; ring]
    by_cases hℓ : ℓ = 0
    · subst hℓ
      have e0 : f 0 = f ((0 : ℕ) : ℤ) := by simp
      rw [e0, hfpos]
      have hJC : besselJExp ((((0 : ℕ) : ℤ) - s : ℤ) : ℂ) h (-z) *
          mathieuCylExp j ((((0 : ℕ) : ℤ) + s : ℤ) : ℂ) h z =
          besselJExp ((((0 : ℕ) : ℤ) + s : ℤ) : ℂ) h (-z) *
          mathieuCylExp j ((((0 : ℕ) : ℤ) - s : ℤ) : ℂ) h z := by
        simp only [Nat.cast_zero, zero_sub, zero_add]
        rw [p1c_besselJExp_neg_intCast, p2m_mathieuCylExp_neg_intCast j hj₁ hj₄ _ hh']
        ring
      simp only [ite_true]
      field_simp
      linear_combination I0 (2 * ((0 : ℕ) : ℤ)) * hJC - I0 (2 * ((0 : ℕ) : ℤ)) *
        (Real.sqrt 2 : ℂ) * (besselJExp ((((0 : ℕ) : ℤ) + s : ℤ) : ℂ) h (-z) *
          mathieuCylExp j ((((0 : ℕ) : ℤ) - s : ℤ) : ℂ) h z) * hKc -
        I0 (2 * ((0 : ℕ) : ℤ)) * (besselJExp ((((0 : ℕ) : ℤ) + s : ℤ) : ℂ) h (-z) *
          mathieuCylExp j ((((0 : ℕ) : ℤ) - s : ℤ) : ℂ) h z) * hs2
    · simp only [hℓ, ite_false, sub_zero]
      field_simp
      set X := besselJExp (((ℓ : ℤ) - s : ℤ) : ℂ) h (-z) *
          mathieuCylExp j (((ℓ : ℤ) + s : ℤ) : ℂ) h z +
        besselJExp (((ℓ : ℤ) + s : ℤ) : ℂ) h (-z) * mathieuCylExp j (((ℓ : ℤ) - s : ℤ) : ℂ) h z
      linear_combination (-I0 (2 * ℓ) * X * (Real.sqrt 2 : ℂ)) * hKc - I0 (2 * ℓ) * X * hs2
  · rw [hc, show (N : ℤ) + 2 * ((s : ℤ) - m) = 2 * s by simp [hN]; ring]
    have hA' := hA
    rw [hA2s, hAeq s] at hA' hKc
    simp only [mathieuEpsilon]
    split_ifs at hA' hKc ⊢ with hs0
    · field_simp at hKc ⊢
      linear_combination (-((Real.sqrt 2 : ℂ) * M)) * hKc - 2 * π * M * hs2
    · field_simp at hKc ⊢
      linear_combination (-((Real.sqrt 2 : ℂ) * M)) * hKc - π * M * hs2

/-- Proof of `hasSum_radialMathieuMc_odd_cross` (DLMF 28.24.3). -/
theorem p2m_hasSum_radialMathieuMc_odd_cross (j : ℕ) (hj₁ : 1 ≤ j) (hj₄ : j ≤ 4) (m s : ℕ)
    {h : ℝ} (hh : 0 < h) (hA : mathieuFourierA (2 * m + 1) (2 * s + 1) (h ^ 2) ≠ 0) (z : ℂ) :
    HasSum (fun ℓ : ℕ => (-1 : ℂ) ^ m * ((-1 : ℂ) ^ ℓ *
        (mathieuFourierA (2 * m + 1) (2 * ℓ + 1) (h ^ 2) /
          mathieuFourierA (2 * m + 1) (2 * s + 1) (h ^ 2)) *
        (besselJExp ((ℓ : ℤ) - s : ℤ) h (-z) * mathieuCylExp j ((ℓ + s + 1 : ℕ) : ℂ) h z +
          besselJExp ((ℓ + s + 1 : ℕ) : ℂ) h (-z) * mathieuCylExp j ((ℓ : ℤ) - s : ℤ) h z)))
      (radialMathieuMc j (2 * m + 1) z h) := by
  have hh' : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  set N : ℕ := 2 * m + 1 with hN
  have hadm : ModMathieuAdmissible ((N : ℕ) : ℂ) (h : ℂ) :=
    Or.inr ⟨⟨N, by push_cast; rfl⟩, by rw [← Complex.ofReal_pow]; exact Complex.ofReal_im _⟩
  have H := p2m_hasSum_modMathieuTerm j hj₁ hj₄ hadm hh' ((s : ℤ) - m) z
  set c := mathieuMeCoeff ((N : ℕ) : ℂ) ((h : ℂ) ^ 2) with hcdef
  set I0 : ℤ → ℂ := fun K => ∫ x in (0 : ℝ)..2 * π,
    mathieuCe N x (h ^ 2) * Complex.cos ((K : ℂ) * x) with hI0
  have hc : ∀ k : ℤ, c k = (Real.sqrt 2 : ℂ) / (2 * π) * I0 (N + 2 * k) := by
    intro k
    have := p2m_mathieuMeCoeff_ce N (h ^ 2) k
    push_cast at this
    rw [hcdef, this]
    simp only [hI0, Int.cast_add, Int.cast_natCast, Int.cast_mul, Int.cast_ofNat]
  have hIneg : ∀ K : ℤ, I0 (-K) = I0 K := by
    intro K; simp only [hI0]; push_cast; simp only [neg_mul, Complex.cos_neg]
  have hAeq : ∀ ℓ : ℕ, mathieuFourierA (2 * m + 1) (2 * ℓ + 1) (h ^ 2) =
      (1 / π : ℂ) * I0 (2 * ℓ + 1) := by
    intro ℓ
    simp only [mathieuFourierA, hI0, hN]
    push_cast
    simp
  set M := radialMathieuMc j (2 * m + 1) z h
  set f : ℤ → ℂ := fun p => modMathieuTerm j ((N : ℕ) : ℂ) z h ((s : ℤ) - m) (p - m) with hfdef
  have H1 : HasSum f (c ((s : ℤ) - m) * M) :=
    ((Equiv.subRight (m : ℤ)).hasSum_iff
      (f := fun p => modMathieuTerm j ((N : ℕ) : ℂ) z h ((s : ℤ) - m) p)).mpr H
  have hf : ∀ p : ℤ, f p = (-1 : ℂ) ^ p * (-1 : ℂ) ^ (m : ℤ) *
      ((Real.sqrt 2 : ℂ) / (2 * π) * I0 (2 * p + 1)) * besselJExp ((p - s : ℤ) : ℂ) h (-z) *
        mathieuCylExp j ((p + s + 1 : ℤ) : ℂ) h z := by
    intro p
    simp only [hfdef, modMathieuTerm]
    rw [← hcdef, hc, p2m_negOnePow_sub,
      show (N : ℤ) + 2 * (p - m) = 2 * p + 1 by simp [hN]; ring,
      show p - m - (s - m) = p - s by ring,
      show ((N : ℕ) : ℂ) + (((s : ℤ) - m : ℤ) : ℂ) + ((p - m : ℤ) : ℂ) = ((p + s + 1 : ℤ) : ℂ) by
        simp [hN]; ring]
  have H2 := H1.nat_add_neg_add_one
  set A2s := mathieuFourierA (2 * m + 1) (2 * s + 1) (h ^ 2) with hA2s
  set Kc : ℂ := (Real.sqrt 2 : ℂ) / A2s
  have H3 := H2.mul_left Kc
  have hs2 := p2m_sqrt_two_sq
  have hKc : A2s * Kc = (Real.sqrt 2 : ℂ) := by simp only [Kc]; field_simp
  have hfpos : ∀ ℓ : ℕ, f ℓ = (-1 : ℂ) ^ ℓ * (-1 : ℂ) ^ m *
      ((Real.sqrt 2 : ℂ) / (2 * π) * I0 (2 * ℓ + 1)) *
        besselJExp (((ℓ : ℤ) - s : ℤ) : ℂ) h (-z) *
        mathieuCylExp j (((ℓ : ℤ) + s + 1 : ℤ) : ℂ) h z := by
    intro ℓ; rw [hf]; simp only [zpow_natCast]
  have hfneg : ∀ ℓ : ℕ, f (-((ℓ : ℤ) + 1)) = (-1 : ℂ) ^ ℓ * (-1 : ℂ) ^ m *
      ((Real.sqrt 2 : ℂ) / (2 * π) * I0 (2 * ℓ + 1)) *
        besselJExp (((ℓ : ℤ) + s + 1 : ℤ) : ℂ) h (-z) *
        mathieuCylExp j (((ℓ : ℤ) - s : ℤ) : ℂ) h z := by
    intro ℓ
    rw [hf, show -((ℓ : ℤ) + 1) - s = -((ℓ : ℤ) + s + 1) by ring,
      show -((ℓ : ℤ) + 1) + s + 1 = -((ℓ : ℤ) - s) by ring,
      p1c_besselJExp_neg_intCast, p2m_mathieuCylExp_neg_intCast j hj₁ hj₄ _ hh',
      show 2 * -((ℓ : ℤ) + 1) + 1 = -(2 * ℓ + 1) by ring, hIneg, p2m_negOnePow_neg,
      zpow_natCast]
    have hsgn : (-1 : ℂ) ^ ((ℓ : ℤ) + 1) * ((-1 : ℂ) ^ ((ℓ : ℤ) + s + 1) *
        (-1 : ℂ) ^ ((ℓ : ℤ) - s)) = (-1 : ℂ) ^ ℓ := by
      rw [← zpow_add₀ (by norm_num), ← zpow_add₀ (by norm_num),
        show (ℓ : ℤ) + 1 + ((ℓ : ℤ) + s + 1 + (ℓ - s)) = ℓ + 2 * (ℓ + 1) by ring,
        zpow_add₀ (by norm_num), zpow_mul]
      simp
    linear_combination ((-1 : ℂ) ^ m * ((Real.sqrt 2 : ℂ) / (2 * π) *
      I0 (2 * ℓ + 1)) * besselJExp (((ℓ : ℤ) + s + 1 : ℤ) : ℂ) h (-z) *
        mathieuCylExp j (((ℓ : ℤ) - s : ℤ) : ℂ) h z) * hsgn
  convert H3 using 1
  · funext ℓ
    rw [hfpos, hfneg, hAeq, show ((ℓ + s + 1 : ℕ) : ℂ) = (((ℓ : ℤ) + s + 1 : ℤ) : ℂ) by
      push_cast; ring]
    field_simp
    set X := besselJExp (((ℓ : ℤ) - s : ℤ) : ℂ) h (-z) *
        mathieuCylExp j (((ℓ : ℤ) + s + 1 : ℤ) : ℂ) h z +
      besselJExp (((ℓ : ℤ) + s + 1 : ℤ) : ℂ) h (-z) * mathieuCylExp j (((ℓ : ℤ) - s : ℤ) : ℂ) h z
    linear_combination (-I0 (2 * ℓ + 1) * X * (Real.sqrt 2 : ℂ)) * hKc - I0 (2 * ℓ + 1) * X * hs2
  · rw [hc, show (N : ℤ) + 2 * ((s : ℤ) - m) = 2 * s + 1 by simp [hN]; ring]
    rw [hA2s, hAeq s] at hKc
    field_simp at hKc ⊢
    linear_combination (-((Real.sqrt 2 : ℂ) * M)) * hKc - π * M * hs2

/-- The integer-order coefficients `c^{-N}_{2k}` of `me_{-N} = -√2 i se_N` (`N ≥ 1`) as sine
integrals: `c^{-N}_{2k}(q) = -√2/(2π) ∫₀^{2π} se_N(x) sin((2k-N)x) dx`. -/
theorem p2m_mathieuMeCoeff_se {N : ℕ} (hN0 : N ≠ 0) (q : ℝ) (k : ℤ) :
    mathieuMeCoeff ((-(N : ℤ) : ℤ) : ℂ) (q : ℂ) k = -((Real.sqrt 2 : ℂ) / (2 * π)) *
      ∫ x in (0 : ℝ)..2 * π, mathieuSe N x q * Complex.sin (((-(N : ℤ) + 2 * k : ℤ) : ℂ) * x) := by
  set K : ℤ := -(N : ℤ) + 2 * k
  have hex : ∃ k' : ℤ, (k' : ℂ) = ((-(N : ℤ) : ℤ) : ℂ) := ⟨-(N : ℤ), rfl⟩
  have hNK : (-1 : ℂ) ^ N * (-1 : ℂ) ^ K = 1 := p2m_negOnePow_mul_eq_one ⟨k - N, by simp [K]; ring⟩
  have hse := (isMathieuSolution_mathieuSe N q).differentiable
  have hsc : Continuous fun x : ℝ => mathieuSe N x q :=
    hse.continuous.comp Complex.continuous_ofReal
  have hshift : ∀ x : ℝ, mathieuSe N ((x - π : ℝ) : ℂ) q = (-1 : ℂ) ^ N * mathieuSe N x q := by
    intro x
    have := p2m_mathieuSe_add_pi hN0 ((x - π : ℝ) : ℂ) q
    push_cast at this ⊢
    rw [sub_add_cancel] at this
    rw [this, ← mul_assoc, ← mul_pow]; simp
  have hneg : ¬ (0 : ℤ) ≤ -(N : ℤ) := by omega
  simp only [mathieuMeCoeff, hex, ite_true, mathieuMe_intCast, mathieuMeInt, hneg, ite_false,
    Int.natAbs_neg, Int.natAbs_natCast]
  rw [show ((-(N : ℤ) : ℤ) : ℂ) + 2 * (k : ℂ) = (K : ℂ) by push_cast [K]; ring]
  have hcos0 : ∫ x in (0 : ℝ)..π, mathieuSe N x q * Complex.cos ((K : ℂ) * x) = 0 := by
    refine p2m_integral_eq_zero_of_reflect fun x => ?_
    have hc : Complex.cos ((K : ℂ) * ((x - π : ℝ) : ℂ)) = (-1 : ℂ) ^ K * Complex.cos (K * x) := by
      have := p2m_cos_add_int_mul_pi K ((x - π : ℝ) : ℂ)
      push_cast at this ⊢
      rw [sub_add_cancel] at this
      rw [this, ← mul_assoc, ← mul_zpow]; simp
    rw [show ((π - x : ℝ) : ℂ) = -((x - π : ℝ) : ℂ) by push_cast; ring, mathieuSe_neg, hshift,
      mul_neg, Complex.cos_neg, hc]
    linear_combination (-(mathieuSe N x q * Complex.cos (K * x))) * hNK
  have hsin : ∫ x in (0 : ℝ)..2 * π, mathieuSe N x q * Complex.sin ((K : ℂ) * x) =
      2 * ∫ x in (0 : ℝ)..π, mathieuSe N x q * Complex.sin ((K : ℂ) * x) := by
    refine p2m_integral_two_pi (by fun_prop) fun x => ?_
    push_cast
    rw [p2m_mathieuSe_add_pi hN0, p2m_sin_add_int_mul_pi]
    linear_combination (mathieuSe N x q * Complex.sin (K * x)) * hNK
  have e : ∀ x : ℝ, -((Real.sqrt 2 : ℂ) * I) * mathieuSe N x q * Complex.exp (-(I * K * x)) =
      -((Real.sqrt 2 : ℂ) * I) * (mathieuSe N x q * Complex.cos ((K : ℂ) * x)) -
        (Real.sqrt 2 : ℂ) * (mathieuSe N x q * Complex.sin ((K : ℂ) * x)) := by
    intro x
    rw [show -(I * (K : ℂ) * x) = (-((K : ℂ) * x)) * I by ring, Complex.exp_mul_I,
      Complex.cos_neg, Complex.sin_neg]
    ring_nf
    rw [I_sq]
    ring
  simp_rw [e]
  have i1 : IntervalIntegrable (fun x : ℝ => mathieuSe N x q * Complex.cos ((K : ℂ) * x))
      MeasureTheory.volume 0 π := (by fun_prop : Continuous fun x : ℝ =>
        mathieuSe N x q * Complex.cos ((K : ℂ) * x)).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun x : ℝ => mathieuSe N x q * Complex.sin ((K : ℂ) * x))
      MeasureTheory.volume 0 π := (by fun_prop : Continuous fun x : ℝ =>
        mathieuSe N x q * Complex.sin ((K : ℂ) * x)).intervalIntegrable _ _
  rw [intervalIntegral.integral_sub (i1.const_mul _) (i2.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hcos0, hsin]
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp
  ring

/-- Proof of `hasSum_radialMathieuMs_odd_cross` (DLMF 28.24.4). -/
theorem p2m_hasSum_radialMathieuMs_odd_cross (j : ℕ) (hj₁ : 1 ≤ j) (hj₄ : j ≤ 4) (m s : ℕ)
    {h : ℝ} (hh : 0 < h) (hB : mathieuFourierB (2 * m + 1) (2 * s + 1) (h ^ 2) ≠ 0) (z : ℂ) :
    HasSum (fun ℓ : ℕ => (-1 : ℂ) ^ m * ((-1 : ℂ) ^ ℓ *
        (mathieuFourierB (2 * m + 1) (2 * ℓ + 1) (h ^ 2) /
          mathieuFourierB (2 * m + 1) (2 * s + 1) (h ^ 2)) *
        (besselJExp ((ℓ : ℤ) - s : ℤ) h (-z) * mathieuCylExp j ((ℓ + s + 1 : ℕ) : ℂ) h z -
          besselJExp ((ℓ + s + 1 : ℕ) : ℂ) h (-z) * mathieuCylExp j ((ℓ : ℤ) - s : ℤ) h z)))
      (radialMathieuMs j (2 * m + 1) z h) := by
  have hh' : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  set N : ℕ := 2 * m + 1 with hN
  have hN0 : N ≠ 0 := by omega
  set ν : ℂ := -((N : ℕ) : ℂ) with hν
  have hadm : ModMathieuAdmissible ν (h : ℂ) :=
    Or.inr ⟨⟨-(N : ℤ), by push_cast; rfl⟩, by rw [← Complex.ofReal_pow]; exact Complex.ofReal_im _⟩
  set n : ℤ := (s : ℤ) + m + 1 with hn
  have H := p2m_hasSum_modMathieuTerm j hj₁ hj₄ hadm hh' n z
  set c := mathieuMeCoeff ν ((h : ℂ) ^ 2) with hcdef
  set S0 : ℤ → ℂ := fun K => ∫ x in (0 : ℝ)..2 * π,
    mathieuSe N x (h ^ 2) * Complex.sin ((K : ℂ) * x) with hS0
  have hc : ∀ k : ℤ, c k = -((Real.sqrt 2 : ℂ) / (2 * π)) * S0 (-(N : ℤ) + 2 * k) := by
    intro k
    have := p2m_mathieuMeCoeff_se hN0 (h ^ 2) k
    push_cast at this
    rw [hcdef, hν, this]
    simp only [hS0, Int.cast_add, Int.cast_natCast, Int.cast_mul, Int.cast_ofNat, Int.cast_neg]
  have hSneg : ∀ K : ℤ, S0 (-K) = -S0 K := by
    intro K; simp only [hS0]; push_cast
    simp only [neg_mul, Complex.sin_neg, mul_neg, intervalIntegral.integral_neg]
  have hBeq : ∀ ℓ : ℕ, mathieuFourierB (2 * m + 1) (2 * ℓ + 1) (h ^ 2) =
      (1 / π : ℂ) * S0 (2 * ℓ + 1) := by
    intro ℓ
    simp only [mathieuFourierB, hS0, hN]
    push_cast
    simp
  set M := modMathieuM j ν z h
  have hMs : radialMathieuMs j (2 * m + 1) z h = -M := by
    simp only [radialMathieuMs, M, hν, hN]; rw [pow_succ, pow_mul]; simp
  rw [hMs]
  set f : ℤ → ℂ := fun p => modMathieuTerm j ν z h n (p + (m + 1)) with hfdef
  have H1 : HasSum f (c n * M) :=
    ((Equiv.addRight ((m : ℤ) + 1)).hasSum_iff
      (f := fun p => modMathieuTerm j ν z h n p)).mpr H
  have hf : ∀ p : ℤ, f p = (-1 : ℂ) ^ p * (-1 : ℂ) ^ (m : ℤ) *
      ((Real.sqrt 2 : ℂ) / (2 * π) * S0 (2 * p + 1)) * besselJExp ((p - s : ℤ) : ℂ) h (-z) *
        mathieuCylExp j ((p + s + 1 : ℤ) : ℂ) h z := by
    intro p
    simp only [hfdef, modMathieuTerm]
    rw [← hcdef, hc, zpow_add₀ (by norm_num), zpow_add₀ (by norm_num),
      show -(N : ℤ) + 2 * (p + (m + 1)) = 2 * p + 1 by simp [hN]; ring,
      show p + (m + 1) - n = p - s by simp [hn]; ring,
      show ν + (n : ℂ) + ((p + (m + 1) : ℤ) : ℂ) = ((p + s + 1 : ℤ) : ℂ) by
        simp [hν, hN, hn]; ring]
    simp only [zpow_one]
    ring
  have H2 := H1.nat_add_neg_add_one
  set B2s := mathieuFourierB (2 * m + 1) (2 * s + 1) (h ^ 2) with hB2s
  set Kc : ℂ := (Real.sqrt 2 : ℂ) / B2s
  have H3 := H2.mul_left Kc
  have hs2 := p2m_sqrt_two_sq
  have hKc : B2s * Kc = (Real.sqrt 2 : ℂ) := by simp only [Kc]; field_simp
  have hfpos : ∀ ℓ : ℕ, f ℓ = (-1 : ℂ) ^ ℓ * (-1 : ℂ) ^ m *
      ((Real.sqrt 2 : ℂ) / (2 * π) * S0 (2 * ℓ + 1)) *
        besselJExp (((ℓ : ℤ) - s : ℤ) : ℂ) h (-z) *
        mathieuCylExp j (((ℓ : ℤ) + s + 1 : ℤ) : ℂ) h z := by
    intro ℓ; rw [hf]; simp only [zpow_natCast]
  have hfneg : ∀ ℓ : ℕ, f (-((ℓ : ℤ) + 1)) = -((-1 : ℂ) ^ ℓ * (-1 : ℂ) ^ m *
      ((Real.sqrt 2 : ℂ) / (2 * π) * S0 (2 * ℓ + 1)) *
        besselJExp (((ℓ : ℤ) + s + 1 : ℤ) : ℂ) h (-z) *
        mathieuCylExp j (((ℓ : ℤ) - s : ℤ) : ℂ) h z) := by
    intro ℓ
    rw [hf, show -((ℓ : ℤ) + 1) - s = -((ℓ : ℤ) + s + 1) by ring,
      show -((ℓ : ℤ) + 1) + s + 1 = -((ℓ : ℤ) - s) by ring,
      p1c_besselJExp_neg_intCast, p2m_mathieuCylExp_neg_intCast j hj₁ hj₄ _ hh',
      show 2 * -((ℓ : ℤ) + 1) + 1 = -(2 * ℓ + 1) by ring, hSneg, p2m_negOnePow_neg,
      zpow_natCast]
    have hsgn : (-1 : ℂ) ^ ((ℓ : ℤ) + 1) * ((-1 : ℂ) ^ ((ℓ : ℤ) + s + 1) *
        (-1 : ℂ) ^ ((ℓ : ℤ) - s)) = (-1 : ℂ) ^ ℓ := by
      rw [← zpow_add₀ (by norm_num), ← zpow_add₀ (by norm_num),
        show (ℓ : ℤ) + 1 + ((ℓ : ℤ) + s + 1 + (ℓ - s)) = ℓ + 2 * (ℓ + 1) by ring,
        zpow_add₀ (by norm_num), zpow_mul]
      simp
    linear_combination (-((-1 : ℂ) ^ m * ((Real.sqrt 2 : ℂ) / (2 * π) *
      S0 (2 * ℓ + 1)) * besselJExp (((ℓ : ℤ) + s + 1 : ℤ) : ℂ) h (-z) *
        mathieuCylExp j (((ℓ : ℤ) - s : ℤ) : ℂ) h z)) * hsgn
  convert H3 using 1
  · funext ℓ
    rw [hfpos, hfneg, hBeq, show ((ℓ + s + 1 : ℕ) : ℂ) = (((ℓ : ℤ) + s + 1 : ℤ) : ℂ) by
      push_cast; ring]
    field_simp
    linear_combination (-S0 (2 * ℓ + 1) * (besselJExp (((ℓ : ℤ) - s : ℤ) : ℂ) h (-z) *
        mathieuCylExp j (((ℓ : ℤ) + s + 1 : ℤ) : ℂ) h z -
      besselJExp (((ℓ : ℤ) + s + 1 : ℤ) : ℂ) h (-z) * mathieuCylExp j (((ℓ : ℤ) - s : ℤ) : ℂ) h z) *
        (Real.sqrt 2 : ℂ)) * hKc - S0 (2 * ℓ + 1) * (besselJExp (((ℓ : ℤ) - s : ℤ) : ℂ) h (-z) *
        mathieuCylExp j (((ℓ : ℤ) + s + 1 : ℤ) : ℂ) h z -
      besselJExp (((ℓ : ℤ) + s + 1 : ℤ) : ℂ) h (-z) *
        mathieuCylExp j (((ℓ : ℤ) - s : ℤ) : ℂ) h z) * hs2
  · rw [hc, show -(N : ℤ) + 2 * n = 2 * s + 1 by simp [hN, hn]; ring]
    rw [hB2s, hBeq s] at hKc
    field_simp at hKc ⊢
    linear_combination ((Real.sqrt 2 : ℂ) * M) * hKc + π * M * hs2

/-- Proof of `hasSum_radialMathieuMs_even_cross` (DLMF 28.24.5). -/
theorem p2m_hasSum_radialMathieuMs_even_cross (j : ℕ) (hj₁ : 1 ≤ j) (hj₄ : j ≤ 4) (m s : ℕ)
    {h : ℝ} (hh : 0 < h) (hB : mathieuFourierB (2 * m + 2) (2 * s + 2) (h ^ 2) ≠ 0) (z : ℂ) :
    HasSum (fun ℓ : ℕ => (-1 : ℂ) ^ m * ((-1 : ℂ) ^ ℓ *
        (mathieuFourierB (2 * m + 2) (2 * ℓ + 2) (h ^ 2) /
          mathieuFourierB (2 * m + 2) (2 * s + 2) (h ^ 2)) *
        (besselJExp ((ℓ : ℤ) - s : ℤ) h (-z) * mathieuCylExp j ((ℓ + s + 2 : ℕ) : ℂ) h z -
          besselJExp ((ℓ + s + 2 : ℕ) : ℂ) h (-z) * mathieuCylExp j ((ℓ : ℤ) - s : ℤ) h z)))
      (radialMathieuMs j (2 * m + 2) z h) := by
  have hh' : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  set N : ℕ := 2 * m + 2 with hN
  have hN0 : N ≠ 0 := by omega
  set ν : ℂ := -((N : ℕ) : ℂ) with hν
  have hadm : ModMathieuAdmissible ν (h : ℂ) :=
    Or.inr ⟨⟨-(N : ℤ), by push_cast; rfl⟩, by rw [← Complex.ofReal_pow]; exact Complex.ofReal_im _⟩
  set n : ℤ := (s : ℤ) + m + 2 with hn
  have H := p2m_hasSum_modMathieuTerm j hj₁ hj₄ hadm hh' n z
  set c := mathieuMeCoeff ν ((h : ℂ) ^ 2) with hcdef
  set S0 : ℤ → ℂ := fun K => ∫ x in (0 : ℝ)..2 * π,
    mathieuSe N x (h ^ 2) * Complex.sin ((K : ℂ) * x) with hS0
  have hc : ∀ k : ℤ, c k = -((Real.sqrt 2 : ℂ) / (2 * π)) * S0 (-(N : ℤ) + 2 * k) := by
    intro k
    have := p2m_mathieuMeCoeff_se hN0 (h ^ 2) k
    push_cast at this
    rw [hcdef, hν, this]
    simp only [hS0, Int.cast_add, Int.cast_natCast, Int.cast_mul, Int.cast_ofNat, Int.cast_neg]
  have hSneg : ∀ K : ℤ, S0 (-K) = -S0 K := by
    intro K; simp only [hS0]; push_cast
    simp only [neg_mul, Complex.sin_neg, mul_neg, intervalIntegral.integral_neg]
  have hS00 : S0 0 = 0 := by simp [hS0]
  have hBeq : ∀ ℓ : ℕ, mathieuFourierB (2 * m + 2) (2 * ℓ + 2) (h ^ 2) =
      (1 / π : ℂ) * S0 (2 * ℓ + 2) := by
    intro ℓ
    simp only [mathieuFourierB, hS0, hN]
    push_cast
    simp
  set M := modMathieuM j ν z h
  have hMs : radialMathieuMs j (2 * m + 2) z h = M := by
    simp only [radialMathieuMs, M, hν, hN]
    rw [show 2 * m + 2 = 2 * (m + 1) by ring, pow_mul]; push_cast; simp
  rw [hMs]
  set f : ℤ → ℂ := fun p => modMathieuTerm j ν z h n (p + (m + 2)) with hfdef
  have H1 : HasSum f (c n * M) :=
    ((Equiv.addRight ((m : ℤ) + 2)).hasSum_iff
      (f := fun p => modMathieuTerm j ν z h n p)).mpr H
  have hf : ∀ p : ℤ, f p = -((-1 : ℂ) ^ p * (-1 : ℂ) ^ (m : ℤ) *
      ((Real.sqrt 2 : ℂ) / (2 * π) * S0 (2 * p + 2))) * besselJExp ((p - s : ℤ) : ℂ) h (-z) *
        mathieuCylExp j ((p + s + 2 : ℤ) : ℂ) h z := by
    intro p
    simp only [hfdef, modMathieuTerm]
    rw [← hcdef, hc, zpow_add₀ (by norm_num), zpow_add₀ (by norm_num),
      show -(N : ℤ) + 2 * (p + (m + 2)) = 2 * p + 2 by simp [hN]; ring,
      show p + (m + 2) - n = p - s by simp [hn]; ring,
      show ν + (n : ℂ) + ((p + (m + 2) : ℤ) : ℂ) = ((p + s + 2 : ℤ) : ℂ) by
        simp [hν, hN, hn]; ring]
    have : (-1 : ℂ) ^ (2 : ℤ) = 1 := by norm_num
    rw [this]
    ring
  have hfm1 : f (-1) = 0 := by
    rw [hf, show 2 * (-1 : ℤ) + 2 = 0 by ring, hS00]; ring
  have H1' : HasSum (fun p => f (p - 1)) (c n * M) :=
    ((Equiv.subRight (1 : ℤ)).hasSum_iff (f := f)).mpr H1
  have H2 := (hasSum_nat_add_iff' 1).mpr H1'.nat_add_neg
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, neg_zero, zero_sub,
    hfm1, add_zero, sub_zero] at H2
  set B2s := mathieuFourierB (2 * m + 2) (2 * s + 2) (h ^ 2) with hB2s
  set Kc : ℂ := (Real.sqrt 2 : ℂ) / B2s
  have H3 := H2.mul_left (-Kc)
  have hs2 := p2m_sqrt_two_sq
  have hKc : B2s * Kc = (Real.sqrt 2 : ℂ) := by simp only [Kc]; field_simp
  have hfpos : ∀ ℓ : ℕ, f (((ℓ + 1 : ℕ) : ℤ) - 1) = -((-1 : ℂ) ^ ℓ * (-1 : ℂ) ^ m *
      ((Real.sqrt 2 : ℂ) / (2 * π) * S0 (2 * ℓ + 2))) *
        besselJExp (((ℓ : ℤ) - s : ℤ) : ℂ) h (-z) *
        mathieuCylExp j (((ℓ : ℤ) + s + 2 : ℤ) : ℂ) h z := by
    intro ℓ; rw [show (((ℓ + 1 : ℕ) : ℤ) - 1) = (ℓ : ℤ) by push_cast; ring, hf]
    simp only [zpow_natCast]
  have hfneg : ∀ ℓ : ℕ, f (-((ℓ + 1 : ℕ) : ℤ) - 1) = (-1 : ℂ) ^ ℓ * (-1 : ℂ) ^ m *
      ((Real.sqrt 2 : ℂ) / (2 * π) * S0 (2 * ℓ + 2)) *
        besselJExp (((ℓ : ℤ) + s + 2 : ℤ) : ℂ) h (-z) *
        mathieuCylExp j (((ℓ : ℤ) - s : ℤ) : ℂ) h z := by
    intro ℓ
    rw [show -((ℓ + 1 : ℕ) : ℤ) - 1 = -((ℓ : ℤ) + 2) by push_cast; ring, hf,
      show -((ℓ : ℤ) + 2) - s = -((ℓ : ℤ) + s + 2) by ring,
      show -((ℓ : ℤ) + 2) + s + 2 = -((ℓ : ℤ) - s) by ring,
      p1c_besselJExp_neg_intCast, p2m_mathieuCylExp_neg_intCast j hj₁ hj₄ _ hh',
      show 2 * -((ℓ : ℤ) + 2) + 2 = -(2 * ℓ + 2) by ring, hSneg, p2m_negOnePow_neg,
      zpow_natCast]
    have hsgn : (-1 : ℂ) ^ ((ℓ : ℤ) + 2) * ((-1 : ℂ) ^ ((ℓ : ℤ) + s + 2) *
        (-1 : ℂ) ^ ((ℓ : ℤ) - s)) = (-1 : ℂ) ^ ℓ := by
      rw [← zpow_add₀ (by norm_num), ← zpow_add₀ (by norm_num),
        show (ℓ : ℤ) + 2 + ((ℓ : ℤ) + s + 2 + (ℓ - s)) = ℓ + 2 * (ℓ + 2) by ring,
        zpow_add₀ (by norm_num), zpow_mul]
      simp
    linear_combination ((-1 : ℂ) ^ m * ((Real.sqrt 2 : ℂ) / (2 * π) *
      S0 (2 * ℓ + 2)) * besselJExp (((ℓ : ℤ) + s + 2 : ℤ) : ℂ) h (-z) *
        mathieuCylExp j (((ℓ : ℤ) - s : ℤ) : ℂ) h z) * hsgn
  convert H3 using 1
  · funext ℓ
    rw [hfpos, hfneg, hBeq, show ((ℓ + s + 2 : ℕ) : ℂ) = (((ℓ : ℤ) + s + 2 : ℤ) : ℂ) by
      push_cast; ring]
    field_simp
    linear_combination (-S0 (2 * ℓ + 2) * (besselJExp (((ℓ : ℤ) - s : ℤ) : ℂ) h (-z) *
        mathieuCylExp j (((ℓ : ℤ) + s + 2 : ℤ) : ℂ) h z -
      besselJExp (((ℓ : ℤ) + s + 2 : ℤ) : ℂ) h (-z) * mathieuCylExp j (((ℓ : ℤ) - s : ℤ) : ℂ) h z) *
        (Real.sqrt 2 : ℂ)) * hKc - S0 (2 * ℓ + 2) * (besselJExp (((ℓ : ℤ) - s : ℤ) : ℂ) h (-z) *
        mathieuCylExp j (((ℓ : ℤ) + s + 2 : ℤ) : ℂ) h z -
      besselJExp (((ℓ : ℤ) + s + 2 : ℤ) : ℂ) h (-z) *
        mathieuCylExp j (((ℓ : ℤ) - s : ℤ) : ℂ) h z) * hs2
  · rw [hc, show -(N : ℤ) + 2 * n = 2 * s + 2 by simp [hN, hn]; ring]
    rw [hB2s, hBeq s] at hKc
    field_simp at hKc ⊢
    linear_combination (-((Real.sqrt 2 : ℂ) * M)) * hKc - π * M * hs2

end DLMF.Mathieu
