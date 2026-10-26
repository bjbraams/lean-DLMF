/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Mathieu.Noninteger.Fourier
public import DLMF.Mathieu.Properties
public import DLMF.Mathieu.SecondSolutions

/-!
# Mathieu functions of noninteger order: expansions, asymptotics, stability (DLMF §§28.15–28.19)

* §28.15: the small-`q` expansions of `λ_ν(q)` (28.15.1), the continued-fraction equation
  28.15.2 and the small-`q` expansion of `me_ν(z, q)` (28.15.3);
* §28.16: the large-`q` asymptotic expansion 28.16.1 of `λ_ν(h²)`;
* §28.17: stability of the pairs `(a, q)` (`DLMF.Mathieu.IsMathieuStable`);
* §28.18 only refers to §28.28 (part C of the Chapter 28 acquisition): no statements;
* §28.19: expansions of `π`-pseudoperiodic functions in series of `me_{ν+2n}`.

The expansions with printed finitely many terms followed by `⋯` are stated as `O`-estimates of
the remainder after the printed terms (`q → 0` in `ℂ`, resp. `h → +∞`). All formulas were
checked numerically (truncated tridiagonal eigenproblems for the recurrence 28.14.4, scripts in
the acquisition scratch directory); 28.16.1 was checked for `ν = 0.3, 0.5, 1.5, 2.4` and
`h = 10, 20` (remainder ratios consistent with `O(h⁻⁶)`).
-/

@[expose] public noncomputable section

open Complex Set Filter Asymptotics
open scoped Topology Real Classical

namespace DLMF.Mathieu

variable {ν : ℂ}

/-! ### §28.15 Expansions for small `q` -/

/-- **Power series of `λ_ν(q)`** (DLMF 28.15.1): for `ν ∉ ℤ`, as `q → 0`,
`λ_ν(q) = ν² + q²/(2(ν²-1)) + (5ν²+7) q⁴/(32(ν²-1)³(ν²-4))
  + (9ν⁴+58ν²+29) q⁶/(64(ν²-1)⁵(ν²-4)(ν²-9)) + O(q⁸)`. -/
@[dlmf 28.15.E1]
theorem mathieuLambda_isBigO_zero (hν : ∀ m : ℤ, (m : ℂ) ≠ ν) :
    (fun q : ℂ => mathieuLambda ν q - (ν ^ 2 + q ^ 2 / (2 * (ν ^ 2 - 1)) +
        (5 * ν ^ 2 + 7) * q ^ 4 / (32 * (ν ^ 2 - 1) ^ 3 * (ν ^ 2 - 4)) +
        (9 * ν ^ 4 + 58 * ν ^ 2 + 29) * q ^ 6 /
          (64 * (ν ^ 2 - 1) ^ 5 * (ν ^ 2 - 4) * (ν ^ 2 - 9))))
      =O[𝓝 0] (fun q : ℂ => q ^ 8) := by
  sorry

/-- **Continued-fraction equation** (DLMF 28.15.2): for `ν ∉ ℤ` and `q` normal along the
segment, with `a = λ_ν(q)`, the continued fractions
`F₊ = q²/(a - (ν+2)² - q²/(a - (ν+4)² - ⋯))` and `F₋ = q²/(a - (ν-2)² - q²/(a - (ν-4)² - ⋯))`
converge (as limits of their approximants `mathieuContFrac ν q a 1 N`, resp.
`mathieuContFrac (-ν) q a 1 N`) and `a - ν² - F₊ = F₋`. -/
@[dlmf 28.15.E2]
theorem mathieuLambda_contFrac (hν : ∀ m : ℤ, (m : ℂ) ≠ ν) {q : ℂ}
    (hq : MathieuNormalSegment ν q) :
    ∃ Fp Fm : ℂ,
      Tendsto (fun N => mathieuContFrac ν q (mathieuLambda ν q) 1 N) atTop (𝓝 Fp) ∧
      Tendsto (fun N => mathieuContFrac (-ν) q (mathieuLambda ν q) 1 N) atTop (𝓝 Fm) ∧
      mathieuLambda ν q - ν ^ 2 - Fp = Fm := by
  sorry

/-- **Power series of `me_ν(z, q)`** (DLMF 28.15.3): for `ν ∉ ℤ` and fixed `z`, as `q → 0`,
`me_ν(z, q) = e^{iνz} - (q/4)(e^{i(ν+2)z}/(ν+1) - e^{i(ν-2)z}/(ν-1))
  + (q²/32)(e^{i(ν+4)z}/((ν+1)(ν+2)) + e^{i(ν-4)z}/((ν-1)(ν-2))
    - 2(ν²+1) e^{iνz}/(ν²-1)²) + O(q³)`. -/
@[dlmf 28.15.E3]
theorem mathieuMe_isBigO_zero (hν : ∀ m : ℤ, (m : ℂ) ≠ ν) (z : ℂ) :
    (fun q : ℂ => mathieuMe ν z q - (Complex.exp (I * ν * z) -
        q / 4 * (Complex.exp (I * (ν + 2) * z) / (ν + 1) -
          Complex.exp (I * (ν - 2) * z) / (ν - 1)) +
        q ^ 2 / 32 * (Complex.exp (I * (ν + 4) * z) / ((ν + 1) * (ν + 2)) +
          Complex.exp (I * (ν - 4) * z) / ((ν - 1) * (ν - 2)) -
          2 * (ν ^ 2 + 1) / (ν ^ 2 - 1) ^ 2 * Complex.exp (I * ν * z))))
      =O[𝓝 0] (fun q : ℂ => q ^ 3) := by
  sorry

/-! ### §28.16 Asymptotic expansions for large `q` -/

/-- **Large-`q` expansion of `λ_ν`** (DLMF 28.16.1): let `s = 2m + 1`, `m ∈ ℕ`, and let `ν` be
real with `m < ν < m + 1`. As `h = √q → +∞`,
`λ_ν(h²) = -2h² + 2sh - (s²+1)/8 - (s³+3s)/(2⁷h) - (5s⁴+34s²+9)/(2¹²h²)
  - (33s⁵+410s³+405s)/(2¹⁷h³) - (63s⁶+1260s⁴+2943s²+486)/(2²⁰h⁴)
  - (527s⁷+15617s⁵+69001s³+41607s)/(2²⁵h⁵) + O(h⁻⁶)`. -/
@[dlmf 28.16.E1]
theorem mathieuLambda_isBigO_atTop {m : ℕ} {ν : ℝ} (hν : (m : ℝ) < ν ∧ ν < m + 1) :
    let s : ℝ := 2 * m + 1
    (fun h : ℝ => mathieuLambda ν ((h : ℂ) ^ 2) - ((-2 * h ^ 2 + 2 * s * h - (s ^ 2 + 1) / 8 -
        (s ^ 3 + 3 * s) / (2 ^ 7 * h) - (5 * s ^ 4 + 34 * s ^ 2 + 9) / (2 ^ 12 * h ^ 2) -
        (33 * s ^ 5 + 410 * s ^ 3 + 405 * s) / (2 ^ 17 * h ^ 3) -
        (63 * s ^ 6 + 1260 * s ^ 4 + 2943 * s ^ 2 + 486) / (2 ^ 20 * h ^ 4) -
        (527 * s ^ 7 + 15617 * s ^ 5 + 69001 * s ^ 3 + 41607 * s) / (2 ^ 25 * h ^ 5) : ℝ) : ℂ))
      =O[atTop] (fun h : ℝ => (h ^ 6)⁻¹) := by
  sorry

/-! ### §28.17 Stability as `x → ±∞` -/

/-- **Stable pairs with `q = 0`** (DLMF §28.17): positive real `a` with `q = 0` give stable
pairs (proved: every solution is `w(0) cos(√a z) + w'(0) sin(√a z)/√a`). -/
@[dlmf 28.17]
theorem isMathieuStable_q_zero {a : ℝ} (ha : 0 < a) : IsMathieuStable a 0 := by
  intro w hw
  set k : ℂ := ((Real.sqrt a : ℝ) : ℂ)
  have hk0 : k ≠ 0 := by
    simp only [k, ne_eq, Complex.ofReal_eq_zero]; exact (Real.sqrt_pos.mpr ha).ne'
  have hk2 : k ^ 2 = a := by
    simp only [k]; rw [← Complex.ofReal_pow, Real.sq_sqrt ha.le]
  set w₀ := w 0
  set w₁ := deriv w 0
  set v : ℂ → ℂ := fun z => w₀ * Complex.cos (k * z) + w₁ / k * Complex.sin (k * z)
  set v₁ : ℂ → ℂ := fun z => -(w₀ * k) * Complex.sin (k * z) + w₁ * Complex.cos (k * z)
  have hlin : ∀ z : ℂ, HasDerivAt (fun z => k * z) k z := fun z => by
    simpa using (hasDerivAt_id z).const_mul k
  have hv : ∀ z, HasDerivAt v (v₁ z) z := fun z => by
    have := (((hlin z).ccos).const_mul w₀).add (((hlin z).csin).const_mul (w₁ / k))
    convert this using 1
    simp only [v₁]; field_simp
  have hv₁ : ∀ z, HasDerivAt v₁ (-(a : ℂ) * v z) z := fun z => by
    have := (((hlin z).csin).const_mul (-(w₀ * k))).add (((hlin z).ccos).const_mul w₁)
    convert this using 1
    simp only [v]; rw [← hk2]; field_simp; ring
  have hdv : deriv v = v₁ := funext fun z => (hv z).deriv
  have hsol : IsMathieuSolution (a : ℂ) 0 v :=
    ⟨fun z => (hv z).differentiableAt, fun z => by
      rw [hdv]; convert hv₁ z using 1; ring⟩
  have heq : w = v := hw.eq_of_initial hsol (z₀ := 0) (by simp [v, w₀])
    (by rw [hdv]; simp [v₁, w₁])
  refine ⟨‖w₀‖ + ‖w₁ / k‖, fun x => ?_⟩
  have hc : ∀ r : ℝ, ‖Complex.cos (r : ℂ)‖ ≤ 1 := fun r => by
    rw [← Complex.ofReal_cos, Complex.norm_real]; exact Real.abs_cos_le_one r
  have hs : ∀ r : ℝ, ‖Complex.sin (r : ℂ)‖ ≤ 1 := fun r => by
    rw [← Complex.ofReal_sin, Complex.norm_real]; exact Real.abs_sin_le_one r
  have hkx : k * (x : ℂ) = ((Real.sqrt a * x : ℝ) : ℂ) := by simp [k]
  rw [heq]
  simp only [v, hkx]
  calc ‖w₀ * Complex.cos ((Real.sqrt a * x : ℝ) : ℂ) +
        w₁ / k * Complex.sin ((Real.sqrt a * x : ℝ) : ℂ)‖
      ≤ ‖w₀‖ * ‖Complex.cos ((Real.sqrt a * x : ℝ) : ℂ)‖ +
        ‖w₁ / k‖ * ‖Complex.sin ((Real.sqrt a * x : ℝ) : ℂ)‖ := by
        rw [← norm_mul, ← norm_mul]; exact norm_add_le _ _
    _ ≤ ‖w₀‖ * 1 + ‖w₁ / k‖ * 1 := by
        gcongr
        · exact hc _
        · exact hs _
    _ = ‖w₀‖ + ‖w₁ / k‖ := by ring

/-- `‖me_ν(±x, q)‖ ≤ (∑ |c_m|) e^{∓ℑν x}` for real `x`. -/
theorem p1b_norm_mathieuMe_le {ν : ℂ} (hν : ∀ m : ℤ, (m : ℂ) ≠ ν) {q : ℂ}
    (hq : MathieuNormalSegment ν q) (x : ℝ) :
    ‖mathieuMe ν x q‖ ≤ (∑' m : ℤ, ‖mathieuMeCoeff ν q m‖) * Real.exp (-(ν.im * x)) := by
  have h := hasSum_mathieuMe_ofReal hν hq x
  rw [← h.2.tsum_eq]
  refine (norm_tsum_le_tsum_norm h.1).trans (le_of_eq ?_)
  rw [← tsum_mul_right]
  congr 1; funext m
  rw [norm_mul, p1b_norm_exp_real]

/-- `me_ν(x, q)` does not vanish identically on the real axis. -/
theorem p1b_exists_mathieuMe_ne_zero {ν : ℂ} (hν : ∀ m : ℤ, (m : ℂ) ≠ ν) {q : ℂ}
    (hq : MathieuNormalSegment ν q) : ∃ x : ℝ, mathieuMe ν x q ≠ 0 := by
  by_contra h
  push Not at h
  have := integral_mathieuMe_mul_neg hν hq
  simp only [h, zero_mul, intervalIntegral.integral_zero] at this
  exact Real.pi_ne_zero (by exact_mod_cast this.symm)

/-- A pseudoperiodic `w` with `|μ| < 1` and `w(x₀) ≠ 0` is unbounded on the negative axis. -/
theorem p1b_unbounded_neg {w : ℂ → ℂ} {μ : ℂ} (h : ∀ z, w (z + π) = μ * w z) (hμ : ‖μ‖ < 1)
    {x₀ : ℝ} (hx₀ : w x₀ ≠ 0) : ¬ ∃ C : ℝ, ∀ x : ℝ, 0 ≤ x → ‖w (-x)‖ ≤ C := by
  rintro ⟨C, hC⟩
  obtain ⟨N, hN⟩ := exists_nat_ge (x₀ / π)
  have hb : ∀ n : ℕ, N ≤ n → ‖w x₀‖ ≤ C * ‖μ‖ ^ n := by
    intro n hn
    have e := p1b_add_nat_mul_pi h ((x₀ : ℂ) - n * π) n
    rw [sub_add_cancel] at e
    rw [e, norm_mul, norm_pow, mul_comm]
    gcongr
    have hx : 0 ≤ (n : ℝ) * π - x₀ := by
      have : x₀ ≤ N * π := by rwa [div_le_iff₀ Real.pi_pos] at hN
      have : (N : ℝ) * π ≤ n * π := by gcongr
      linarith
    have := hC _ hx
    simpa [neg_sub] using this
  have ht : Tendsto (fun n : ℕ => C * ‖μ‖ ^ n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hμ).const_mul C
  have : ‖w x₀‖ ≤ 0 := ge_of_tendsto ht (eventually_atTop.2 ⟨N, hb⟩)
  exact hx₀ (norm_le_zero_iff.mp this)

/-- A pseudoperiodic `w` with `|μ| > 1` and `w(x₀) ≠ 0` is unbounded on the positive axis. -/
theorem p1b_unbounded_pos {w : ℂ → ℂ} {μ : ℂ} (h : ∀ z, w (z + π) = μ * w z) (hμ : 1 < ‖μ‖)
    {x₀ : ℝ} (hx₀ : w x₀ ≠ 0) : ¬ ∃ C : ℝ, ∀ x : ℝ, 0 ≤ x → ‖w x‖ ≤ C := by
  have hμ0 : μ ≠ 0 := by rintro rfl; norm_num at hμ
  have hv : ∀ z, w (-(z + π)) = μ⁻¹ * w (-z) := by
    intro z
    have := h (-(z + π))
    rw [show -(z + π) + π = -z by ring] at this
    rw [this, ← mul_assoc, inv_mul_cancel₀ hμ0, one_mul]
  have hμ' : ‖μ⁻¹‖ < 1 := by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hμ
  have := p1b_unbounded_neg (w := fun z => w (-z)) hv hμ' (x₀ := -x₀) (by simpa using hx₀)
  simpa using this

/-- **Stable pairs from real noninteger exponents** (DLMF §28.17): for real `ν ∉ ℤ` and real
`q`, the pair `(λ_ν(q), q)` is stable. Proved from the admitted `mathieuNormalSegment_real`:
every solution is a combination of the bounded Floquet solutions `me_ν(±x, q)`. -/
@[dlmf 28.17]
theorem isMathieuStable_mathieuLambda {ν q : ℝ} (hν : ∀ m : ℤ, (m : ℂ) ≠ ν) :
    IsMathieuStable (mathieuLambda ν q) q := by
  have hq := (mathieuNormalSegment_real (q := q) hν).1
  obtain ⟨⟨h1, h1ne, hp1⟩, ⟨h2, -, hp2⟩⟩ := isFloquetSolution_mathieuMe hν hq
  have hm0 := (p1b_charExp_of_floquet_pair hν (isFloquetSolution_mathieuMe hν hq).1
    (isFloquetSolution_mathieuMe hν hq).2).1
  set f : ℂ → ℂ := fun z => mathieuMe ν z q
  set m0 := f 0
  set d := deriv f 0
  have hd2 : deriv (fun z => f (-z)) 0 = -d := by rw [deriv_comp_neg]; simp [d]
  have hdne : d ≠ 0 := by
    intro hd
    have heq := h1.eq_of_initial h2 (z₀ := 0) (by simp [f])
      (by change d = deriv (fun z => f (-z)) 0; rw [hd2, hd, neg_zero])
    apply p1b_exp_ne_inv hν
    obtain ⟨z, hz⟩ : ∃ z, f z ≠ 0 := by
      by_contra hcon; push Not at hcon; exact h1ne (funext hcon)
    have e1 := hp1 z
    have e2 := hp2 z
    rw [show (π : ℂ) * I * -ν = -(π * I * ν) by ring, Complex.exp_neg] at e2
    have e3 := congrFun heq (z + π)
    have e4 := congrFun heq z
    simp only at e1 e2 e3 e4
    refine mul_right_cancel₀ hz ?_
    linear_combination -e1 + e3 + e2 - (Complex.exp (π * I * ν))⁻¹ * e4
  set B : ℝ := ∑' m : ℤ, ‖mathieuMeCoeff ν q m‖
  have hb : ∀ x : ℝ, ‖f x‖ ≤ B := fun x => by
    simpa using p1b_norm_mathieuMe_le hν hq x
  have hb' : ∀ x : ℝ, ‖f (-x)‖ ≤ B := fun x => by
    simpa using p1b_norm_mathieuMe_le hν hq (-x)
  have hm0' : m0 ≠ 0 := hm0
  intro w hw
  set α : ℂ := (w 0 / m0 + deriv w 0 / d) / 2
  set β : ℂ := (w 0 / m0 - deriv w 0 / d) / 2
  have hg : IsMathieuSolution (mathieuLambda ν q) q (fun z => α * f z + β * f (-z)) :=
    (h1.const_mul α).add (h2.const_mul β)
  have hgd : deriv (fun z => α * f z + β * f (-z)) 0 = α * d + β * -d := by
    have hA : HasDerivAt f d 0 := (h1.differentiable 0).hasDerivAt
    have hB : HasDerivAt (fun z => f (-z)) (-d) 0 := by
      rw [← hd2]; exact (h2.differentiable 0).hasDerivAt
    exact ((hA.const_mul α).add (hB.const_mul β)).deriv
  have hweq := hw.eq_of_initial hg (z₀ := 0)
    (by simp only [neg_zero]; simp only [α, β]; field_simp; ring)
    (by rw [hgd]; simp only [α, β]; field_simp; ring)
  refine ⟨‖α‖ * B + ‖β‖ * B, fun x => ?_⟩
  rw [hweq]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul]
  gcongr
  · exact hb x
  · exact hb' x

/-- **Behaviour of `me_ν(±x, q)` for `ℑν ≠ 0`** (DLMF §28.17): as `x → +∞`, one of
`me_ν(x, q)` and `me_ν(-x, q)` tends to `0` and the other is unbounded. -/
@[dlmf 28.17]
theorem mathieuMe_tendsto_or {q : ℂ} (hν : ∀ m : ℤ, (m : ℂ) ≠ ν) (hν' : ν.im ≠ 0)
    (hq : MathieuNormalSegment ν q) :
    (Tendsto (fun x : ℝ => mathieuMe ν x q) atTop (𝓝 0) ∧
        ¬ ∃ C : ℝ, ∀ x : ℝ, 0 ≤ x → ‖mathieuMe ν (-x) q‖ ≤ C) ∨
      (Tendsto (fun x : ℝ => mathieuMe ν (-x) q) atTop (𝓝 0) ∧
        ¬ ∃ C : ℝ, ∀ x : ℝ, 0 ≤ x → ‖mathieuMe ν x q‖ ≤ C) := by
  obtain ⟨x₀, hx₀⟩ := p1b_exists_mathieuMe_ne_zero hν hq
  set B : ℝ := ∑' m : ℤ, ‖mathieuMeCoeff ν q m‖
  have hper : ∀ z, mathieuMe ν (z + π) q = Complex.exp (π * I * ν) * mathieuMe ν z q :=
    fun z => mathieuMe_add_pi hν z q
  have hμ : ‖Complex.exp (π * I * ν)‖ = Real.exp (-(π * ν.im)) := by
    rw [Complex.norm_exp]; congr 1; simp [Complex.mul_re]
  rcases lt_or_gt_of_ne hν' with hneg | hpos
  · right
    have h1 : 1 < ‖Complex.exp (π * I * ν)‖ := by
      rw [hμ]; exact Real.one_lt_exp_iff.mpr (by nlinarith [Real.pi_pos])
    refine ⟨?_, p1b_unbounded_pos (w := fun z => mathieuMe ν z q) hper h1 hx₀⟩
    have hb : ∀ x : ℝ, ‖mathieuMe ν (-(x : ℂ)) q‖ ≤ B * Real.exp (ν.im * x) := by
      intro x
      have := p1b_norm_mathieuMe_le hν hq (-x)
      simpa using this
    refine squeeze_zero_norm hb ?_
    have : Tendsto (fun x : ℝ => ν.im * x) atTop atBot :=
      tendsto_id.const_mul_atTop_of_neg hneg
    simpa using (Real.tendsto_exp_atBot.comp this).const_mul B
  · left
    have h1 : ‖Complex.exp (π * I * ν)‖ < 1 := by
      rw [hμ]; exact Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])
    refine ⟨?_, p1b_unbounded_neg (w := fun z => mathieuMe ν z q) hper h1 hx₀⟩
    refine squeeze_zero_norm (p1b_norm_mathieuMe_le hν hq) ?_
    have : Tendsto (fun x : ℝ => -(ν.im * x)) atTop atBot :=
      tendsto_neg_atTop_atBot.comp (tendsto_id.const_mul_atTop hpos)
    simpa using (Real.tendsto_exp_atBot.comp this).const_mul B

/-- A nontrivial solution of Mathieu's equation does not vanish identically on `ℝ`. -/
theorem p1b_exists_real_ne_zero {a q : ℂ} {w : ℂ → ℂ} (hw : IsMathieuSolution a q w)
    (hw0 : w ≠ 0) : ∃ x : ℝ, w x ≠ 0 := by
  by_contra h
  push Not at h
  have hd : HasDerivAt (fun x : ℝ => w x) (deriv w 0) 0 := by
    have := (hw.differentiable ((0 : ℝ) : ℂ)).hasDerivAt.comp_ofReal
    simpa using this
  have hz : (fun x : ℝ => w x) = fun _ => 0 := funext h
  rw [hz] at hd
  have hd0 : deriv w 0 = 0 := (hd.unique (hasDerivAt_const _ _)).trans rfl
  have h0 : w 0 = 0 := by simpa using h 0
  have hz' : IsMathieuSolution a q (fun z => 0 * w z) := hw.const_mul 0
  have := hw.eq_of_initial hz' (z₀ := 0) (by simp [h0])
    (by rw [hd0]; simp)
  exact hw0 (by rw [this]; funext z; simp)

/-- A Floquet solution with respect to `ν` with `ℑν ≠ 0` is unbounded on `ℝ`. -/
theorem p1b_floquet_unbounded {a q ν : ℂ} {w : ℂ → ℂ} (hw : IsFloquetSolution a q ν w)
    (hν : ν.im ≠ 0) : ¬ ∃ C : ℝ, ∀ x : ℝ, ‖w x‖ ≤ C := by
  rintro ⟨C, hC⟩
  obtain ⟨hs, hw0, hper⟩ := hw
  obtain ⟨x₀, hx₀⟩ := p1b_exists_real_ne_zero hs hw0
  have hμ : ‖Complex.exp (π * I * ν)‖ = Real.exp (-(π * ν.im)) := by
    rw [Complex.norm_exp]; congr 1; simp [Complex.mul_re]
  rcases lt_or_gt_of_ne hν with hneg | hpos
  · have h1 : 1 < ‖Complex.exp (π * I * ν)‖ := by
      rw [hμ]; exact Real.one_lt_exp_iff.mpr (by nlinarith [Real.pi_pos])
    exact p1b_unbounded_pos hper h1 hx₀ ⟨C, fun x _ => hC x⟩
  · have h1 : ‖Complex.exp (π * I * ν)‖ < 1 := by
      rw [hμ]; exact Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])
    exact p1b_unbounded_neg hper h1 hx₀ ⟨C, fun x _ => by simpa using hC (-x)⟩

/-- **Unstable pairs** (DLMF §28.17): if `a` has a characteristic exponent `ν` with
`ℑν ≠ 0`, then `(a, q)` is unstable; indeed every nontrivial solution of 28.2.1 is unbounded
on `ℝ`. -/
@[dlmf 28.17]
theorem not_isMathieuStable_of_im_ne_zero {a q ν : ℂ} (hc : IsMathieuCharExp a q ν)
    (hν : ν.im ≠ 0) :
    ¬ IsMathieuStable a q ∧ ∀ w : ℂ → ℂ, IsMathieuSolution a q w → w ≠ 0 →
      ¬ ∃ C : ℝ, ∀ x : ℝ, ‖w x‖ ≤ C := by
  have key : ∀ w : ℂ → ℂ, IsMathieuSolution a q w → w ≠ 0 →
      ¬ ∃ C : ℝ, ∀ x : ℝ, ‖w x‖ ≤ C := by
    intro w hw hw0
    rcases hw.isFloquet_or hw0 hc with h | h
    · exact p1b_floquet_unbounded h hν
    · rintro ⟨C, hC⟩
      refine p1b_floquet_unbounded h (by simpa using hν)
        ⟨C + ‖Complex.exp (I * ν * π)‖ * C, fun x => ?_⟩
      have h1 := hC (x + π)
      push_cast at h1
      refine (norm_sub_le _ _).trans ?_
      rw [norm_mul]
      gcongr
      exact hC x
  refine ⟨fun hst => ?_, key⟩
  have hs := mathieuWI_spec a q
  refine key _ hs.1 (fun h => ?_) (hst _ hs.1)
  have := hs.2.1
  rw [h] at this
  simp at this

/-- A continuous `π`-pseudoperiodic function with multiplier of modulus `1` is bounded on `ℝ`. -/
theorem p2x_bounded_of_pseudo {w : ℂ → ℂ} (hw : Continuous w) {μ : ℂ} (hμ : ‖μ‖ = 1)
    (h : ∀ z, w (z + π) = μ * w z) : ∃ C : ℝ, ∀ x : ℝ, ‖w x‖ ≤ C := by
  set g : ℝ → ℝ := fun x => ‖w x‖
  have hg : Continuous g := continuous_norm.comp (hw.comp Complex.continuous_ofReal)
  have hper : Function.Periodic g π := by
    intro x; simp only [g]; push_cast; rw [h, norm_mul, hμ, one_mul]
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := π)).exists_bound_of_continuousOn
    hg.continuousOn
  refine ⟨C, fun x => ?_⟩
  obtain ⟨y, hy, hxy⟩ := hper.exists_mem_Ico₀ Real.pi_pos x
  have := hC y (Ico_subset_Icc_self hy)
  simp only [g, Real.norm_eq_abs, abs_norm] at this hxy
  show ‖w x‖ ≤ C
  rw [hxy]; exact this

/-- Linear growth: if `p(z + π) = s p(z)`, `u(z + π) = s u(z) + B p(z)` with `s² = 1`, `B ≠ 0`
and `p(x₀) ≠ 0`, then `u` is unbounded on `ℝ`. -/
theorem p2x_unbounded_jordan {u p : ℂ → ℂ} {s B : ℂ} (hs : s ^ 2 = 1)
    (hp : ∀ z, p (z + π) = s * p z) (hu : ∀ z, u (z + π) = s * u z + B * p z) (hB : B ≠ 0)
    {x₀ : ℝ} (hx₀ : p x₀ ≠ 0) : ¬ ∃ C : ℝ, ∀ x : ℝ, ‖u x‖ ≤ C := by
  have hpn : ∀ n : ℕ, ∀ z, p (z + n * π) = s ^ n * p z := by
    intro n; induction n with
    | zero => simp
    | succ n ih =>
      intro z; push_cast
      rw [show z + (n + 1) * π = z + n * π + π by ring, hp, ih]; ring
  have hun : ∀ n : ℕ, ∀ z, u (z + n * π) = s ^ n * (u z + n * s * B * p z) := by
    intro n; induction n with
    | zero => simp
    | succ n ih =>
      intro z; push_cast
      rw [show z + (n + 1) * π = z + n * π + π by ring, hu, ih, hpn]
      linear_combination (-(s ^ n * B * p z)) * hs
  have hsn : ∀ n : ℕ, ‖s ^ n‖ = 1 := by
    intro n
    have : ‖s‖ = 1 := by
      have h1 : ‖s‖ ^ 2 = 1 := by rw [← norm_pow, hs, norm_one]
      nlinarith [norm_nonneg s]
    rw [norm_pow, this, one_pow]
  rintro ⟨C, hC⟩
  have hpos : 0 < ‖B * p x₀‖ := norm_pos_iff.mpr (mul_ne_zero hB hx₀)
  obtain ⟨n, hn⟩ := exists_nat_gt ((C + ‖u x₀‖) / ‖B * p x₀‖)
  have h1 := hC (x₀ + n * π)
  push_cast at h1
  rw [hun, norm_mul, hsn, one_mul] at h1
  have hs1 : ‖s‖ = 1 := by simpa using hsn 1
  have h2 : (n : ℝ) * ‖B * p x₀‖ ≤ ‖u x₀ + n * s * B * p x₀‖ + ‖u x₀‖ := by
    have e : (n : ℝ) * ‖B * p x₀‖ = ‖(n * s * B * p x₀ : ℂ)‖ := by
      rw [show (n * s * B * p x₀ : ℂ) = (n : ℂ) * s * (B * p x₀) by ring]
      simp [hs1]
    rw [e]
    have := norm_sub_le (u x₀ + n * s * B * p x₀) (u x₀)
    rwa [add_sub_cancel_left] at this
  have h3 : (C + ‖u x₀‖) < n * ‖B * p x₀‖ := by rwa [div_lt_iff₀ hpos] at hn
  linarith


/-- For real `q ≠ 0` and real `a`, the pair `(a, q)` is stable iff `|w_I(π; a, q)| < 1`
(DLMF §28.17; the boundary cases `w_I(π) = ±1` are unstable by Ince's theorem). -/
theorem p2x_stable_iff {a q : ℝ} (hq : q ≠ 0) :
    IsMathieuStable a q ↔ ‖mathieuWI a q π‖ < 1 := by
  have hq' : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq
  set c := mathieuWI (a : ℂ) (q : ℂ) π with hc
  have hcr : c = (c.re : ℂ) := (Complex.conj_eq_iff_re.mp (p1a1_mathieuWI_real a q π)).symm
  obtain ⟨h1, h10, h11⟩ := mathieuWI_spec (a : ℂ) (q : ℂ)
  obtain ⟨h2, h20, h21⟩ := mathieuWII_spec (a : ℂ) (q : ℂ)
  constructor
  · intro hst
    by_contra hge
    push Not at hge
    rcases hge.lt_or_eq with hgt | heq
    · -- `|c| > 1`: a characteristic exponent with nonzero imaginary part
      set ν : ℂ := DLMF.Elementary.arccosPrincipal c / π
      have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
      have hch : IsMathieuCharExp a q ν := by
        rw [IsMathieuCharExp, show (π : ℂ) * ν = DLMF.Elementary.arccosPrincipal c by
          simp only [ν]; field_simp, DLMF.Elementary.cos_arccos_principal]
      have him : ν.im ≠ 0 := by
        intro h0
        have hν : ν = (ν.re : ℂ) := Complex.ext rfl (by simp [h0])
        have e := hch
        rw [IsMathieuCharExp, hν, ← Complex.ofReal_mul, ← Complex.ofReal_cos] at e
        have : ‖c‖ ≤ 1 := by
          rw [hc, ← e, Complex.norm_real, Real.norm_eq_abs]; exact Real.abs_cos_le_one _
        linarith
      exact (not_isMathieuStable_of_im_ne_zero hch him).1 hst
    · -- `c = ±1`
      have hs : c ^ 2 = 1 := by
        rw [hcr, Complex.norm_real, Real.norm_eq_abs] at heq
        rw [hcr]
        rcases abs_eq (zero_le_one) |>.mp heq.symm with h | h <;> rw [h] <;> norm_num
      have hD : deriv (mathieuWII (a : ℂ) (q : ℂ)) π = c :=
        (mathieuWI_pi_eq_deriv_mathieuWII_pi _ _).symm
      have hW := mathieuWI_wronskian (a : ℂ) (q : ℂ) π
      rw [← hc, hD] at hW
      set B := deriv (mathieuWI (a : ℂ) (q : ℂ)) π
      set C := mathieuWII (a : ℂ) (q : ℂ) π
      have hBC : B * C = 0 := by linear_combination hs - hW
      have eI : ∀ z, mathieuWI (a : ℂ) (q : ℂ) (z + π) =
          c * mathieuWI (a : ℂ) (q : ℂ) z + B * mathieuWII (a : ℂ) (q : ℂ) z :=
        mathieuWI_add_pi _ _
      have eII : ∀ z, mathieuWII (a : ℂ) (q : ℂ) (z + π) =
          c * mathieuWII (a : ℂ) (q : ℂ) z + C * mathieuWI (a : ℂ) (q : ℂ) z := by
        intro z; rw [mathieuWII_add_pi, hD]; ring
      by_cases hB : B = 0
      · by_cases hC : C = 0
        · refine p2x_not_coexist (a := (a : ℂ)) hq' (fun z => ?_) (fun z => ?_)
          · rw [show z + 2 * π = z + π + π by ring, eI, eI, hB]
            linear_combination (mathieuWI (a : ℂ) (q : ℂ) z) * hs
          · rw [show z + 2 * π = z + π + π by ring, eII, eII, hC]
            linear_combination (mathieuWII (a : ℂ) (q : ℂ) z) * hs
        · exact p2x_unbounded_jordan hs (fun z => by rw [eI, hB]; ring) eII hC
            (x₀ := 0) (by simp [h10]) (hst _ h2)
      · have hC : C = 0 := (mul_eq_zero.mp hBC).resolve_left hB
        obtain ⟨x₀, hx₀⟩ := p1b_exists_real_ne_zero h2 (fun h => by
          have := congrArg (fun f => deriv f 0) h; simp [h21] at this)
        exact p2x_unbounded_jordan hs (fun z => by rw [eII, hC]; ring) eI hB hx₀ (hst _ h1)
  · intro hlt
    set r := c.re
    have hr : |r| < 1 := by rw [hcr, Complex.norm_real, Real.norm_eq_abs] at hlt; exact hlt
    have hr1 : -1 < r := by linarith [neg_abs_le r]
    have hr2 : r < 1 := by linarith [le_abs_self r]
    set θ := Real.arccos r
    have hθ0 : 0 < θ := Real.arccos_pos.mpr hr2
    have hθπ : θ < π := Real.arccos_lt_pi.mpr hr1
    have hsin : Real.sin θ ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi hθ0 hθπ).ne'
    have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    set ν : ℂ := ((θ / π : ℝ) : ℂ)
    have hπν : (π : ℂ) * ν = θ := by simp only [ν]; push_cast; field_simp
    have hcos : Complex.cos θ = c := by
      rw [← Complex.ofReal_cos, Real.cos_arccos hr1.le hr2.le, hcr]
    have hch1 : IsMathieuCharExp a q ν := by rw [IsMathieuCharExp, hπν, hcos]
    have hch2 : IsMathieuCharExp a q (-ν) := by
      rw [IsMathieuCharExp, mul_neg, hπν, Complex.cos_neg, hcos]
    obtain ⟨u, hu, hu0, hup⟩ := (exists_isFloquetSolution_iff_charExp _ _ _).mpr hch1
    obtain ⟨v, hv, hv0, hvp⟩ := (exists_isFloquetSolution_iff_charExp _ _ _).mpr hch2
    have hm1 : Complex.exp (π * I * ν) = Complex.exp (θ * I) := by
      rw [show (π : ℂ) * I * ν = π * ν * I by ring, hπν]
    have hm2 : Complex.exp (π * I * -ν) = Complex.exp (-θ * I) := by
      rw [show (π : ℂ) * I * -ν = -(π * ν) * I by ring, hπν]
    rw [hm1] at hup
    rw [hm2] at hvp
    have hne : Complex.exp (θ * I) - Complex.exp (-θ * I) ≠ 0 := by
      have e : Complex.exp (θ * I) - Complex.exp (-θ * I) = 2 * I * Complex.sin θ := by
        rw [Complex.sin]
        have : I * I = -1 := Complex.I_mul_I
        linear_combination (exp := 1) (-(Complex.exp (-θ * I) - Complex.exp (θ * I))) * this
      rw [e, ← Complex.ofReal_sin]
      exact mul_ne_zero (mul_ne_zero two_ne_zero Complex.I_ne_zero)
        (Complex.ofReal_ne_zero.mpr hsin)
    obtain ⟨Cu, hCu⟩ := p2x_bounded_of_pseudo hu.differentiable.continuous
      (Complex.norm_exp_ofReal_mul_I θ) hup
    obtain ⟨Cv, hCv⟩ := p2x_bounded_of_pseudo hv.differentiable.continuous
      (by rw [show -(θ : ℂ) * I = ((-θ : ℝ) : ℂ) * I by push_cast; ring]
          exact Complex.norm_exp_ofReal_mul_I _) hvp
    have hW : u 0 * deriv v 0 - deriv u 0 * v 0 ≠ 0 := by
      intro hW
      obtain ⟨k, hk⟩ := p2x_eq_const_mul_of_wronskian hu hu0 hv hW
      apply hv0; funext z
      have e1 := hvp z
      rw [hk] at e1
      simp only at e1
      rw [hup] at e1
      have e2 : (Complex.exp (θ * I) - Complex.exp (-θ * I)) * (k * u z) = 0 := by
        linear_combination e1
      have := (mul_eq_zero.mp e2).resolve_left hne
      rw [hk]; simpa using this
    intro w hw
    obtain ⟨α, β, hwe⟩ : ∃ α β : ℂ, w = fun z => α * u z + β * v z :=
      ⟨_, _, p2x_eq_comb_of_wronskian hu hv hW hw⟩
    refine ⟨‖α‖ * Cu + ‖β‖ * Cv, fun x => ?_⟩
    rw [hwe]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    gcongr
    · exact hCu x
    · exact hCv x

/-- **The stability chart** (DLMF §28.17, Figure 28.17.1): for real `a` and real `q ≠ 0` the
stable pairs form an open set whose boundary consists of points on the characteristic curves
`a = a_n(q)` and `a = b_n(q)`. Proved from `p2x_stable_iff` (stability iff `|w_I(π)| < 1`, by
Ince's theorem), the continuity of `(a, q) ↦ w_I(π; a, q)` (`differentiable_mathieuWI_mathieuWII`)
and Table 28.2.1 (`exists_solution_neumann_iff` and its analogues). -/
@[dlmf 28.17]
theorem isOpen_mathieuStable_and_frontier :
    IsOpen {p : ℝ × ℝ | p.2 ≠ 0 ∧ IsMathieuStable p.1 p.2} ∧
      frontier {p : ℝ × ℝ | p.2 ≠ 0 ∧ IsMathieuStable p.1 p.2} ∩ {p | p.2 ≠ 0} ⊆
        {p : ℝ × ℝ | ∃ n : ℕ, p.1 = mathieuA n p.2 ∨ (1 ≤ n ∧ p.1 = mathieuB n p.2)} := by
  set F : ℝ × ℝ → ℂ := fun p => mathieuWI (p.1 : ℂ) (p.2 : ℂ) π
  have hF : Continuous F := by
    have h := differentiable_mathieuWI_mathieuWII.1.continuous
    have hl : Continuous fun p : ℝ × ℝ => ((π : ℂ), (p.1 : ℂ), (p.2 : ℂ)) := by fun_prop
    exact h.comp hl
  have hS : {p : ℝ × ℝ | p.2 ≠ 0 ∧ IsMathieuStable p.1 p.2} =
      {p : ℝ × ℝ | p.2 ≠ 0 ∧ ‖F p‖ < 1} := by
    ext p
    simp only [mem_ofPred_eq]
    exact ⟨fun h => ⟨h.1, (p2x_stable_iff h.1).mp h.2⟩,
      fun h => ⟨h.1, (p2x_stable_iff h.1).mpr h.2⟩⟩
  have hopen : IsOpen {p : ℝ × ℝ | p.2 ≠ 0 ∧ ‖F p‖ < 1} :=
    (isOpen_ne_fun continuous_snd continuous_const).inter
      (isOpen_lt (continuous_norm.comp hF) continuous_const)
  rw [hS]
  refine ⟨hopen, ?_⟩
  rintro p ⟨hfr, hp2⟩
  rw [hopen.frontier_eq] at hfr
  obtain ⟨hcl, hnot⟩ := hfr
  have hle : ‖F p‖ ≤ 1 := by
    have : closure {p : ℝ × ℝ | p.2 ≠ 0 ∧ ‖F p‖ < 1} ⊆ {p | ‖F p‖ ≤ 1} :=
      closure_minimal (fun x hx => hx.2.le) (isClosed_le (continuous_norm.comp hF)
        continuous_const)
    exact this hcl
  have hge : ¬ ‖F p‖ < 1 := fun h => hnot ⟨hp2, h⟩
  have h1 : ‖F p‖ = 1 := le_antisymm hle (not_lt.mp hge)
  obtain ⟨a, q⟩ := p
  simp only [mem_ofPred_eq] at hp2 ⊢
  have hcr : F (a, q) = ((F (a, q)).re : ℂ) :=
    (Complex.conj_eq_iff_re.mp (p1a1_mathieuWI_real a q π)).symm
  obtain ⟨g1, g10, g11⟩ := mathieuWI_spec (a : ℂ) (q : ℂ)
  obtain ⟨g2, g20, g21⟩ := mathieuWII_spec (a : ℂ) (q : ℂ)
  have ne1 : mathieuWI (a : ℂ) (q : ℂ) ≠ 0 := fun h => by simpa [g10] using congrFun h 0
  have ne2 : mathieuWII (a : ℂ) (q : ℂ) ≠ 0 := fun h => by
    have := congrArg (fun f => deriv f 0) h; simp [g21] at this
  have hpm : F (a, q) = 1 ∨ F (a, q) = -1 := by
    rw [hcr, Complex.norm_real, Real.norm_eq_abs] at h1
    rcases abs_eq zero_le_one |>.mp h1 with h | h
    · left; rw [hcr, h]; simp
    · right; rw [hcr, h]; simp
  rcases hpm with h | h
  · have e := mathieuWI_pi_sub_one (a : ℂ) (q : ℂ)
    simp only [F] at h
    rw [h, sub_self] at e
    rcases mul_eq_zero.mp e.symm with e | e
    · have e := (mul_eq_zero.mp e).resolve_left two_ne_zero
      obtain ⟨n, hn⟩ := (exists_solution_neumann_iff a q).mp ⟨_, g1, ne1, g11, e⟩
      exact ⟨2 * n, Or.inl hn⟩
    · obtain ⟨n, hn⟩ := (exists_solution_dirichlet_iff a q).mp ⟨_, g2, ne2, g20, e⟩
      exact ⟨2 * n + 2, Or.inr ⟨by omega, hn⟩⟩
  · have e := mathieuWI_pi_add_one (a : ℂ) (q : ℂ)
    simp only [F] at h
    rw [h, neg_add_cancel] at e
    rcases mul_eq_zero.mp e.symm with e | e
    · have e := (mul_eq_zero.mp e).resolve_left two_ne_zero
      obtain ⟨n, hn⟩ := (exists_solution_neumann_dirichlet_iff a q).mp ⟨_, g1, ne1, g11, e⟩
      exact ⟨2 * n + 1, Or.inl hn⟩
    · obtain ⟨n, hn⟩ := (exists_solution_dirichlet_neumann_iff a q).mp ⟨_, g2, ne2, g20, e⟩
      exact ⟨2 * n + 1, Or.inr ⟨by omega, hn⟩⟩

/-! ### §28.19 Expansions in series of `me_{ν+2n}` -/

/-- **Expansion in `me_{ν+2n}`** (DLMF 28.19.1–28.19.3): let `ν ∉ ℤ`, let `q` be normal with
respect to every `ν + 2n`, and let `f` be analytic on an open strip `S = {a < ℑz < b}`,
`a < 0 < b`, with `f(z + π) = e^{iνπ} f(z)`. Then
`f(z) = ∑_n f_n me_{ν+2n}(z, q)` with `f_n = π⁻¹ ∫₀^π f(z) me_{ν+2n}(-z, q) dz`, the series
converging absolutely and uniformly on compact subsets of `S`. -/
@[dlmf 28.19.E1, dlmf 28.19.E2, dlmf 28.19.E3]
theorem hasSum_mathieuMe_expansion (hν : ∀ m : ℤ, (m : ℂ) ≠ ν) {q : ℂ}
    (hq : ∀ n : ℤ, MathieuNormalSegment (ν + 2 * n) q) {a b : ℝ} (ha : a < 0) (hb : 0 < b)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f {z | a < z.im ∧ z.im < b})
    (hper : ∀ z, a < z.im → z.im < b → f (z + π) = Complex.exp (I * ν * π) * f z) :
    let fn : ℤ → ℂ := fun n =>
      (1 / π : ℂ) * ∫ x in (0 : ℝ)..π, f x * mathieuMe (ν + 2 * n) (-x) q
    (∀ z, a < z.im → z.im < b →
      Summable (fun n : ℤ => ‖fn n * mathieuMe (ν + 2 * n) z q‖) ∧
        HasSum (fun n : ℤ => fn n * mathieuMe (ν + 2 * n) z q) (f z)) ∧
      TendstoLocallyUniformlyOn
        (fun (s : Finset ℤ) (z : ℂ) => ∑ n ∈ s, fn n * mathieuMe (ν + 2 * n) z q) f atTop
        {z | a < z.im ∧ z.im < b} := by
  sorry

/-- **Example** (DLMF 28.19.4): `e^{iνz} = ∑_n c^{ν+2n}_{-2n}(q) me_{ν+2n}(z, q)` for `ν ∉ ℤ`
and `q` normal with respect to every `ν + 2n`, with the coefficients of §28.14. -/
@[dlmf 28.19.E4]
theorem hasSum_exp_mathieuMe (hν : ∀ m : ℤ, (m : ℂ) ≠ ν) {q : ℂ}
    (hq : ∀ n : ℤ, MathieuNormalSegment (ν + 2 * n) q) (z : ℂ) :
    HasSum (fun n : ℤ => mathieuMeCoeff (ν + 2 * n) q (-n) * mathieuMe (ν + 2 * n) z q)
      (Complex.exp (I * ν * z)) := by
  sorry

end DLMF.Mathieu
