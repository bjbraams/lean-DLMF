/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Mathieu.Properties.BasicSolutions

/-!
# Floquet properties of Mathieu functions

Characteristic exponents, Floquet alternatives and Ince-type arguments for Mathieu solutions.

Source references and common attribution are retained in
`DLMF.Mathieu.Properties`.
-/

@[expose] public noncomputable section

open Complex Set Filter ComplexConjugate

open scoped Topology Real

namespace DLMF.Mathieu

/-! ### Floquet theory (§28.2(iii)–(iv)) -/

/-- **Floquet's theorem** (DLMF 28.2.14–28.2.15): Mathieu's equation has a nontrivial solution
with `w(z + π) = e^{πiν} w(z)` iff `e^{πiν}` is an eigenvalue of the monodromy matrix 28.2.15. -/
@[dlmf 28.2.E14, dlmf 28.2.E15]
theorem exists_isFloquetSolution_iff (a q ν : ℂ) :
    (∃ w, IsFloquetSolution a q ν w) ↔
      ∃ v : Fin 2 → ℂ, v ≠ 0 ∧
        (mathieuMonodromy a q).mulVec v = Complex.exp (π * I * ν) • v := by
  set μ := Complex.exp (π * I * ν)
  obtain ⟨h1, h10, h11⟩ := mathieuWI_spec a q
  obtain ⟨h2, h20, h21⟩ := mathieuWII_spec a q
  constructor
  · rintro ⟨w, hw, hne, hper⟩
    refine ⟨![w 0, deriv w 0], ?_, ?_⟩
    · intro hv
      have e0 : w 0 = 0 := by simpa using congrFun hv 0
      have e1 : deriv w 0 = 0 := by simpa using congrFun hv 1
      apply hne
      rw [hw.eq_combination]; funext z; simp [e0, e1]
    · have hf : (fun z => w (z + π)) = fun z => μ * w z := funext hper
      have d1 : deriv w π = μ * deriv w 0 := by
        have := congrArg (fun f => deriv f 0) hf
        rw [deriv_comp_add_const, zero_add,
          deriv_const_mul _ (hw.differentiable 0)] at this
        exact this
      have v0 : w π = μ * w 0 := by simpa using hper 0
      have c0 := congrFun hw.eq_combination π
      have c1 := hw.p1a1_deriv_eq π
      ext i; fin_cases i
      · simp [mathieuMonodromy, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
        rw [← v0, c0]; ring
      · simp [mathieuMonodromy, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
        rw [← d1, c1]; ring
  · rintro ⟨v, hv, hM⟩
    have m0 := congrFun hM 0
    have m1 := congrFun hM 1
    simp [mathieuMonodromy, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at m0 m1
    set w := fun z => v 0 * mathieuWI a q z + v 1 * mathieuWII a q z with hwdef
    have hw : IsMathieuSolution a q w := (h1.const_mul _).add (h2.const_mul _)
    have hw0 : w 0 = v 0 := by simp [w, h10, h20]
    have hw1 : deriv w 0 = v 1 := by
      rw [hwdef, m28a_deriv_lincomb (h1.differentiable 0) (h2.differentiable 0), h11, h21]
      ring
    refine ⟨w, hw, ?_, fun z => ?_⟩
    · intro hz
      apply hv
      have e0 : v 0 = 0 := by rw [← hw0, hz]; rfl
      have e1 : v 1 = 0 := by rw [← hw1, hz]; simp
      ext i; fin_cases i <;> simp [e0, e1]
    · have key := hw.comp_add_pi.eq_of_initial (hw.const_mul μ) (z₀ := 0)
        (by simp only [zero_add, w, h10, h20]; linear_combination m0)
        (by
          rw [deriv_comp_add_const, zero_add, deriv_const_mul _ (hw.differentiable 0), hw1,
            hwdef, m28a_deriv_lincomb (h1.differentiable _) (h2.differentiable _)]
          linear_combination m1)
      exact congrFun key z

/-- **Characteristic equation** (DLMF 28.2.16): a Floquet solution with respect to `ν` exists iff
`cos πν = w_I(π; a, q)`. -/
@[dlmf 28.2.E16]
theorem exists_isFloquetSolution_iff_charExp (a q ν : ℂ) :
    (∃ w, IsFloquetSolution a q ν w) ↔ IsMathieuCharExp a q ν := by
  rw [exists_isFloquetSolution_iff]
  set μ := Complex.exp (π * I * ν)
  have hμ : μ ≠ 0 := Complex.exp_ne_zero _
  set M := mathieuMonodromy a q
  have e1 : (∃ v : Fin 2 → ℂ, v ≠ 0 ∧ M.mulVec v = μ • v) ↔
      ∃ v ≠ 0, (M - μ • (1 : Matrix (Fin 2) (Fin 2) ℂ)).mulVec v = 0 := by
    simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero]
  rw [e1, Matrix.exists_mulVec_eq_zero_iff, Matrix.det_fin_two]
  have hW := mathieuWI_wronskian a q π
  have h9 := mathieuWI_pi_eq_deriv_mathieuWII_pi a q
  have hcos : Complex.cos (π * ν) = (μ + μ⁻¹) / 2 := by
    rw [Complex.cos, show (π : ℂ) * ν * I = π * I * ν by ring,
      show -((π : ℂ) * ν) * I = -(π * I * ν) by ring, Complex.exp_neg]
  simp only [M, mathieuMonodromy, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, smul_eq_mul]
  simp only [Fin.isValue, ↓reduceIte, mul_one, mul_zero, sub_zero, zero_ne_one, one_ne_zero]
  rw [IsMathieuCharExp, hcos]
  rw [← h9] at hW ⊢
  constructor
  · intro h
    field_simp
    linear_combination h - hW
  · intro h
    field_simp at h
    linear_combination h + hW

/-- **DLMF 28.2.16** (second equality): `w_I(π; a, q) = w_I(π; a, -q)`. -/
@[dlmf 28.2.E16]
theorem mathieuWI_pi_neg_q (a q : ℂ) : mathieuWI a q π = mathieuWI a (-q) π := by
  rw [m28a_mathieuWI_pi, m28a_mathieuWI_pi a (-q), p1a1_mathieuWI_half_pi_neg_q,
    p1a1_mathieuWII_half_pi_neg_q, p1a1_deriv_mathieuWI_half_pi_neg_q,
    p1a1_deriv_mathieuWII_half_pi_neg_q]
  ring

/-- If `g` is entire and even, `s ↦ g(√s)` is entire. -/
lemma p2f_differentiable_comp_sqrt {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    (hev : ∀ w, g (-w) = g w) : Differentiable ℂ (fun s => g (s ^ (2⁻¹ : ℂ))) := by
  have key : ∀ s w : ℂ, w ^ 2 = s → g (s ^ (2⁻¹ : ℂ)) = g w := by
    intro s w hw
    have : w ^ 2 = (s ^ (2⁻¹ : ℂ)) ^ 2 := by rw [hw, Complex.cpow_ofNat_inv_pow]
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 this with h | h
    · rw [h]
    · rw [h, hev]
  have hne : ∀ s₀ : ℂ, s₀ ≠ 0 → DifferentiableAt ℂ (fun s => g (s ^ (2⁻¹ : ℂ))) s₀ := by
    intro s₀ hs₀
    by_cases hsl : s₀ ∈ Complex.slitPlane
    · exact (hg _).comp s₀ (differentiableAt_id.cpow_const hsl)
    · have hsl' : -s₀ ∈ Complex.slitPlane := by
        rw [Complex.mem_slitPlane_iff] at hsl ⊢
        push Not at hsl
        left
        have hre : s₀.re ≠ 0 := fun h => hs₀ (Complex.ext h hsl.2)
        simp only [neg_re]
        exact neg_pos.2 (lt_of_le_of_ne hsl.1 hre)
      have e : (fun s => g (s ^ (2⁻¹ : ℂ))) = fun s => g (I * (-s) ^ (2⁻¹ : ℂ)) := by
        funext s
        apply key
        rw [mul_pow, Complex.cpow_ofNat_inv_pow, I_sq]; ring
      rw [e]
      exact (hg _).comp s₀ (differentiableAt_const _ |>.mul
        ((differentiableAt_id.neg).cpow_const hsl'))
  have hc : ContinuousAt (fun s => g (s ^ (2⁻¹ : ℂ))) 0 :=
    (hg _).continuousAt.comp (continuousAt_cpow_const_of_re_pos (Or.inl (by simp)) (by norm_num))
  intro s₀
  rcases eq_or_ne s₀ 0 with rfl | hs₀
  · have := (Complex.differentiableOn_compl_singleton_and_continuousAt_iff
      (f := fun s => g (s ^ (2⁻¹ : ℂ))) (s := univ) (c := 0) univ_mem).1
      ⟨fun s hs => (hne s hs.2).differentiableWithinAt, hc⟩
    exact this.differentiableAt univ_mem
  · exact hne s₀ hs₀

/-- Hartogs for two variables on `ℂ × ℂ`. -/
lemma p2f_differentiable_of_separately₂ {f : ℂ × ℂ → ℂ}
    (h1 : ∀ b, Differentiable ℂ (fun x => f (x, b)))
    (h2 : ∀ x, Differentiable ℂ (fun b => f (x, b))) : Differentiable ℂ f := by
  let g : (Fin 2 → ℂ) → ℂ := fun v => f (v 0, v 1)
  have hg : AnalyticOnNhd ℂ g univ := by
    refine SeveralComplexVariables.analyticOnNhd_of_separately_analytic isOpen_univ ?_
    intro v _ i
    fin_cases i
    · have := (h1 (v 1)).analyticAt (v 0)
      simpa [g, Function.update] using this
    · have := (h2 (v 0)).analyticAt (v 1)
      simpa [g, Function.update] using this
  have hL : Differentiable ℂ (fun p : ℂ × ℂ => (![p.1, p.2] : Fin 2 → ℂ)) := by
    refine differentiable_pi.2 fun i => ?_
    fin_cases i <;> simp
  exact (differentiableOn_univ.1 hg.differentiableOn).comp hL

/-- `cos πν` is an entire function of `a` and `q²` (DLMF §28.2(iii)): there is an entire
function `F` on `ℂ²` with `w_I(π; a, q) = F(a, q²)`. -/
@[dlmf 28.2.iii]
theorem exists_entire_mathieuWI_pi :
    ∃ F : ℂ × ℂ → ℂ, Differentiable ℂ F ∧ ∀ a q, mathieuWI a q π = F (a, q ^ 2) := by
  have hI := p2f_differentiable_param (W := mathieuWI) isMathieuSolution_mathieuWI
    (fun a q => (mathieuWI_spec a q).2.1) (fun a q => (mathieuWI_spec a q).2.2)
  have hI' := p2f_differentiable_param_q (W := mathieuWI) isMathieuSolution_mathieuWI
    (fun a q => (mathieuWI_spec a q).2.1) (fun a q => (mathieuWI_spec a q).2.2)
  have hev : ∀ a q : ℂ, mathieuWI a (-q) π = mathieuWI a q π := fun a q =>
    (mathieuWI_pi_neg_q a q).symm
  refine ⟨fun p => mathieuWI p.1 (p.2 ^ (2⁻¹ : ℂ)) π, ?_, fun a q => ?_⟩
  · exact p2f_differentiable_of_separately₂ (fun s => (hI (s ^ (2⁻¹ : ℂ)) π).1)
      (fun a => p2f_differentiable_comp_sqrt (g := fun q => mathieuWI a q π) (hI' a _).1
        (hev a))
  · have : q ^ 2 = ((q ^ 2) ^ (2⁻¹ : ℂ)) ^ 2 := by rw [Complex.cpow_ofNat_inv_pow]
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 this with h | h
    · simp only; rw [← h]
    · show mathieuWI a q π = mathieuWI a ((q ^ 2) ^ (2⁻¹ : ℂ)) π
      rw [← hev a ((q ^ 2) ^ (2⁻¹ : ℂ)), ← h]

/-- **Principal characteristic exponent** (DLMF §28.2(iii)): `ν̂ = π⁻¹ arccos w_I(π; a, q)`
(principal branch, §4.23(ii)) is a characteristic exponent, and the general solution of 28.2.16
is `ν = ±ν̂ + 2n`, `n ∈ ℤ`. -/
@[dlmf 28.2.iii]
theorem isMathieuCharExp_iff (a q ν : ℂ) :
    IsMathieuCharExp a q ν ↔ ∃ n : ℤ,
      ν = DLMF.Elementary.arccosPrincipal (mathieuWI a q π) / π + 2 * n ∨
        ν = -(DLMF.Elementary.arccosPrincipal (mathieuWI a q π) / π) + 2 * n := by
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have key : IsMathieuCharExp a q ν ↔ Complex.cos (DLMF.Elementary.arccosPrincipal
      (mathieuWI a q π)) = Complex.cos (π * ν) := by
    rw [DLMF.Elementary.cos_arccos_principal, IsMathieuCharExp, eq_comm]
  rw [key, Complex.cos_eq_cos_iff]
  constructor
  · rintro ⟨k, hk | hk⟩
    · refine ⟨k, Or.inl ?_⟩
      field_simp
      linear_combination hk
    · refine ⟨k, Or.inr ?_⟩
      field_simp
      linear_combination hk
  · rintro ⟨k, hk | hk⟩
    · refine ⟨k, Or.inl ?_⟩
      rw [hk]; field_simp; ring
    · refine ⟨k, Or.inr ?_⟩
      rw [hk]; field_simp; ring

/-- `ℜ √z ≥ 0` for the principal square root. -/
lemma p1a1_re_sqrt_nonneg (z : ℂ) : 0 ≤ (Complex.sqrt z).re := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp [Complex.sqrt, Complex.zero_cpow (by norm_num : (2⁻¹ : ℂ) ≠ 0)]
  · rw [Complex.sqrt, Complex.cpow_def_of_ne_zero hz, Complex.exp_re]
    refine mul_nonneg (Real.exp_pos _).le (Real.cos_nonneg_of_mem_Icc ⟨?_, ?_⟩)
    · have := Complex.neg_pi_lt_arg z
      have e : (Complex.log z * 2⁻¹).im = Complex.arg z / 2 := by
        simp [Complex.log_im]; ring
      rw [e]; linarith
    · have := Complex.arg_le_pi z
      have e : (Complex.log z * 2⁻¹).im = Complex.arg z / 2 := by
        simp [Complex.log_im]; ring
      rw [e]; linarith

/-- `0 ≤ ℜ(arccos c / π) ≤ 1` for the principal arccosine. -/
lemma p1a1_re_arccosPrincipal_div_pi_mem (c : ℂ) :
    0 ≤ (DLMF.Elementary.arccosPrincipal c / π).re ∧
      (DLMF.Elementary.arccosPrincipal c / π).re ≤ 1 := by
  set s := Complex.sqrt (1 - c ^ 2)
  set w := s + I * c
  have hs : s ^ 2 = 1 - c ^ 2 := DLMF.Elementary.trig_sqrt_sq _
  have hprod : w * (s - I * c) = 1 := by
    simp only [w]; linear_combination hs - c ^ 2 * Complex.I_sq
  have hw0 : w ≠ 0 := left_ne_zero_of_mul_eq_one hprod
  have hre : 0 ≤ w.re := by
    have hinv : s - I * c = w⁻¹ := eq_inv_of_mul_eq_one_right hprod
    have h2 : w.re + (w⁻¹).re = 2 * s.re := by
      rw [← hinv]; simp only [w, Complex.add_re, Complex.sub_re]; ring
    rw [Complex.inv_re] at h2
    have hn : 0 < Complex.normSq w := Complex.normSq_pos.mpr hw0
    have hsr := p1a1_re_sqrt_nonneg (1 - c ^ 2)
    by_contra hneg
    rw [not_le] at hneg
    have : w.re / Complex.normSq w < 0 := div_neg_of_neg_of_pos hneg hn
    linarith
  have harg := (Complex.abs_arg_le_pi_div_two_iff).mpr hre
  rw [abs_le] at harg
  have e : (DLMF.Elementary.arccosPrincipal c / π).re = (π / 2 - Complex.arg w) / π := by
    rw [Complex.div_ofReal_re]
    congr 1
    simp [DLMF.Elementary.arccosPrincipal, DLMF.Elementary.arcsinPrincipal, Complex.log_im, w, s]
    ring
  rw [e]
  constructor
  · apply div_nonneg _ Real.pi_pos.le; linarith
  · rw [div_le_one Real.pi_pos]; linarith [Real.pi_pos]

/-- The principal exponent satisfies `0 ≤ ℜν̂ ≤ 1` (DLMF §28.2(iii)). -/
@[dlmf 28.2.iii]
theorem re_arccosPrincipal_mathieuWI_div_pi_mem (a q : ℂ) :
    0 ≤ (DLMF.Elementary.arccosPrincipal (mathieuWI a q π) / π).re ∧
      (DLMF.Elementary.arccosPrincipal (mathieuWI a q π) / π).re ≤ 1 :=
  p1a1_re_arccosPrincipal_div_pi_mem _

/-- **Double roots** (DLMF §28.2(iii)): `ν` is a double root of the characteristic equation
(the derivative `-π sin πν` of `cos πν - w_I(π)` also vanishes) iff `ν` is an integer. -/
@[dlmf 28.2.iii]
theorem isMathieuCharExp_double_iff (a q ν : ℂ) (h : IsMathieuCharExp a q ν) :
    Complex.sin (π * ν) = 0 ↔ ∃ n : ℤ, ν = n := by
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [Complex.sin_eq_zero_iff]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, by rw [mul_comm] at hk; exact mul_right_cancel₀ hπ hk⟩
  · rintro ⟨k, rfl⟩
    exact ⟨k, by ring⟩

/-- **Connection formula** (DLMF 28.2.17): every solution satisfies
`w(z + π) + w(z - π) = 2 cos(πν) w(z)` for a characteristic exponent `ν`. -/
@[dlmf 28.2.E17]
theorem IsMathieuSolution.add_pi_add_sub_pi {a q ν : ℂ} {w : ℂ → ℂ}
    (h : IsMathieuSolution a q w) (hν : IsMathieuCharExp a q ν) (z : ℂ) :
    w (z + π) + w (z - π) = 2 * Complex.cos (π * ν) * w z := by
  have e := h.eq_combination
  rw [hν, e]
  simp only
  rw [mathieuWI_add_pi, mathieuWI_sub_pi, mathieuWII_add_pi, mathieuWII_sub_pi,
    ← mathieuWI_pi_eq_deriv_mathieuWII_pi]
  ring

/-- **Floquet dichotomy** (DLMF §28.2(iv)): a nontrivial solution `w` is either a Floquet solution
with respect to `ν`, or `w(z + π) - e^{iνπ} w(z)` is a Floquet solution with respect to `-ν`. -/
@[dlmf 28.2.iv]
theorem IsMathieuSolution.isFloquet_or {a q ν : ℂ} {w : ℂ → ℂ}
    (h : IsMathieuSolution a q w) (hw : w ≠ 0) (hν : IsMathieuCharExp a q ν) :
    IsFloquetSolution a q ν w ∨
      IsFloquetSolution a q (-ν) (fun z => w (z + π) - Complex.exp (I * ν * π) * w z) := by
  by_cases hu : (fun z => w (z + π) - Complex.exp (I * ν * π) * w z) = 0
  · left
    refine ⟨h, hw, fun z => ?_⟩
    have := congrFun hu z
    simp only [Pi.zero_apply] at this
    rw [show (π : ℂ) * I * ν = I * ν * π by ring]
    linear_combination this
  · right
    refine ⟨by simpa [sub_eq_add_neg] using
      h.comp_add_pi.add (h.const_mul (-Complex.exp (I * ν * π))), hu, fun z => ?_⟩
    · have h2 := h.add_pi_add_sub_pi hν (z + π)
      rw [show z + π - π = z by ring, show z + π + π = z + 2 * π by ring] at h2
      have hc : 2 * Complex.cos (π * ν) =
          Complex.exp (I * ν * π) + (Complex.exp (I * ν * π))⁻¹ := by
        rw [Complex.cos, show (π : ℂ) * ν * I = I * ν * π by ring,
          show -((π : ℂ) * ν) * I = -(I * ν * π) by ring, Complex.exp_neg]; ring
      rw [hc] at h2
      rw [show (π : ℂ) * I * -ν = -(I * ν * π) by ring, Complex.exp_neg]
      beta_reduce
      rw [show z + π + π = z + 2 * π by ring]
      have he : (Complex.exp (I * ν * π))⁻¹ * Complex.exp (I * ν * π) = 1 :=
        inv_mul_cancel₀ (Complex.exp_ne_zero _)
      linear_combination h2 + w z * he

/-- Derivative periodicity from periodicity. -/
lemma p1a2_deriv_periodic {f : ℂ → ℂ} {T : ℂ} (hf : ∀ z, f (z + T) = f z) (z : ℂ) :
    deriv f (z + T) = deriv f z := by
  have : (fun z => f (z + T)) = f := funext hf
  have h := deriv_comp_add_const (f := f) (a := T) (x := z)
  rw [this] at h
  exact h.symm

/-- Integration-by-parts identity behind the recurrences 28.4.5–28.4.8 (cosine form). -/
theorem p1a2_cos_rec {a q : ℂ} {f : ℂ → ℂ} (hf : IsMathieuSolution a q f)
    (hper : ∀ z, f (z + 2 * π) = f z) (k : ℤ) :
    (a - (k : ℂ) ^ 2) * ∫ x in (0 : ℝ)..2 * π, f x * Complex.cos (k * x) =
      q * ((∫ x in (0 : ℝ)..2 * π, f x * Complex.cos (((k - 2 : ℤ) : ℂ) * x)) +
        ∫ x in (0 : ℝ)..2 * π, f x * Complex.cos (((k + 2 : ℤ) : ℂ) * x)) := by
  set K : ℂ := (k : ℂ)
  let g : ℝ → ℂ := fun x => deriv f x * Complex.cos (K * x) + K * f x * Complex.sin (K * x)
  have hg : ∀ x : ℝ, HasDerivAt g
      ((2 * q * Complex.cos (2 * x) - a + K ^ 2) * (f x * Complex.cos (K * x))) x := by
    intro x
    have h1 : HasDerivAt (fun x : ℝ => deriv f x)
        ((2 * q * Complex.cos (2 * x) - a) * f x) x := (hf.hasDerivAt_deriv x).comp_ofReal
    have h0 : HasDerivAt (fun x : ℝ => f x) (deriv f x) x :=
      (hf.differentiable x).hasDerivAt.comp_ofReal
    have hl : HasDerivAt (fun x : ℝ => K * (x : ℂ)) K x := by
      simpa using ((hasDerivAt_id (x : ℂ)).const_mul K).comp_ofReal
    have hc : HasDerivAt (fun x : ℝ => Complex.cos (K * x)) (-Complex.sin (K * x) * K) x :=
      (Complex.hasDerivAt_cos _).comp x hl
    have hs : HasDerivAt (fun x : ℝ => Complex.sin (K * x)) (Complex.cos (K * x) * K) x :=
      (Complex.hasDerivAt_sin _).comp x hl
    convert (h1.mul hc).add ((h0.const_mul K).mul hs) using 1
    ring
  have hcont : Continuous fun x : ℝ =>
      (2 * q * Complex.cos (2 * x) - a + K ^ 2) * (f x * Complex.cos (K * x)) := by
    have := hf.differentiable.continuous
    fun_prop
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := 2 * π)
    (fun x _ => hg x) (hcont.intervalIntegrable _ _)
  have hK1 : Complex.cos (K * ((2 * π : ℝ) : ℂ)) = 1 := by
    rw [show K * ((2 * π : ℝ) : ℂ) = (k : ℂ) * (2 * π) by push_cast; ring]
    exact Complex.cos_int_mul_two_pi k
  have hK2 : Complex.sin (K * ((2 * π : ℝ) : ℂ)) = 0 := by
    rw [show K * ((2 * π : ℝ) : ℂ) = (k : ℂ) * (2 * π) by push_cast; ring]
    exact Complex.sin_int_mul_pi (2 * k) |>.symm ▸ by push_cast; ring_nf
  have hper' := p1a2_deriv_periodic hper 0
  rw [zero_add] at hper'
  have h0 : ∫ x in (0 : ℝ)..2 * π,
      (2 * q * Complex.cos (2 * x) - a + K ^ 2) * (f x * Complex.cos (K * x)) = 0 := by
    rw [hint]
    simp only [g, hK1, hK2]
    push_cast
    rw [hper', show f (2 * π) = f 0 by simpa using hper 0]
    simp
  have hpt : ∀ x : ℝ, (2 * q * Complex.cos (2 * x) - a + K ^ 2) * (f x * Complex.cos (K * x)) =
      q * (f x * Complex.cos (((k - 2 : ℤ) : ℂ) * x)) +
        q * (f x * Complex.cos (((k + 2 : ℤ) : ℂ) * x)) +
        (K ^ 2 - a) * (f x * Complex.cos (K * x)) := by
    intro x
    push_cast
    rw [show (K - 2) * (x : ℂ) = K * x - 2 * x by ring,
      show (K + 2) * (x : ℂ) = K * x + 2 * x by ring, Complex.cos_sub, Complex.cos_add]
    ring
  have hc : ∀ j : ℤ, Continuous fun x : ℝ => f x * Complex.cos ((j : ℂ) * x) := by
    intro j
    have := hf.differentiable.continuous
    fun_prop
  simp_rw [hpt] at h0
  rw [intervalIntegral.integral_add (((hc _).intervalIntegrable _ _).const_mul _ |>.add
      (((hc _).intervalIntegrable _ _).const_mul _)) (((hc k).intervalIntegrable _ _).const_mul _),
    intervalIntegral.integral_add (((hc _).intervalIntegrable _ _).const_mul _)
      (((hc _).intervalIntegrable _ _).const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at h0
  linear_combination -h0

/-- Integration-by-parts identity behind the recurrences 28.4.5–28.4.8 (sine form). -/
theorem p1a2_sin_rec {a q : ℂ} {f : ℂ → ℂ} (hf : IsMathieuSolution a q f)
    (hper : ∀ z, f (z + 2 * π) = f z) (k : ℤ) :
    (a - (k : ℂ) ^ 2) * ∫ x in (0 : ℝ)..2 * π, f x * Complex.sin (k * x) =
      q * ((∫ x in (0 : ℝ)..2 * π, f x * Complex.sin (((k - 2 : ℤ) : ℂ) * x)) +
        ∫ x in (0 : ℝ)..2 * π, f x * Complex.sin (((k + 2 : ℤ) : ℂ) * x)) := by
  set K : ℂ := (k : ℂ)
  let g : ℝ → ℂ := fun x => deriv f x * Complex.sin (K * x) - K * f x * Complex.cos (K * x)
  have hg : ∀ x : ℝ, HasDerivAt g
      ((2 * q * Complex.cos (2 * x) - a + K ^ 2) * (f x * Complex.sin (K * x))) x := by
    intro x
    have h1 : HasDerivAt (fun x : ℝ => deriv f x)
        ((2 * q * Complex.cos (2 * x) - a) * f x) x := (hf.hasDerivAt_deriv x).comp_ofReal
    have h0 : HasDerivAt (fun x : ℝ => f x) (deriv f x) x :=
      (hf.differentiable x).hasDerivAt.comp_ofReal
    have hl : HasDerivAt (fun x : ℝ => K * (x : ℂ)) K x := by
      simpa using ((hasDerivAt_id (x : ℂ)).const_mul K).comp_ofReal
    have hc : HasDerivAt (fun x : ℝ => Complex.cos (K * x)) (-Complex.sin (K * x) * K) x :=
      (Complex.hasDerivAt_cos _).comp x hl
    have hs : HasDerivAt (fun x : ℝ => Complex.sin (K * x)) (Complex.cos (K * x) * K) x :=
      (Complex.hasDerivAt_sin _).comp x hl
    convert (h1.mul hs).sub ((h0.const_mul K).mul hc) using 1
    ring
  have hcont : Continuous fun x : ℝ =>
      (2 * q * Complex.cos (2 * x) - a + K ^ 2) * (f x * Complex.sin (K * x)) := by
    have := hf.differentiable.continuous
    fun_prop
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := 2 * π)
    (fun x _ => hg x) (hcont.intervalIntegrable _ _)
  have hK1 : Complex.cos (K * ((2 * π : ℝ) : ℂ)) = 1 := by
    rw [show K * ((2 * π : ℝ) : ℂ) = (k : ℂ) * (2 * π) by push_cast; ring]
    exact Complex.cos_int_mul_two_pi k
  have hK2 : Complex.sin (K * ((2 * π : ℝ) : ℂ)) = 0 := by
    rw [show K * ((2 * π : ℝ) : ℂ) = (k : ℂ) * (2 * π) by push_cast; ring]
    exact Complex.sin_int_mul_pi (2 * k) |>.symm ▸ by push_cast; ring_nf
  have h0 : ∫ x in (0 : ℝ)..2 * π,
      (2 * q * Complex.cos (2 * x) - a + K ^ 2) * (f x * Complex.sin (K * x)) = 0 := by
    rw [hint]
    simp only [g, hK1, hK2]
    push_cast
    rw [show f (2 * π) = f 0 by simpa using hper 0]
    simp
  have hpt : ∀ x : ℝ, (2 * q * Complex.cos (2 * x) - a + K ^ 2) * (f x * Complex.sin (K * x)) =
      q * (f x * Complex.sin (((k - 2 : ℤ) : ℂ) * x)) +
        q * (f x * Complex.sin (((k + 2 : ℤ) : ℂ) * x)) +
        (K ^ 2 - a) * (f x * Complex.sin (K * x)) := by
    intro x
    push_cast
    rw [show (K - 2) * (x : ℂ) = K * x - 2 * x by ring,
      show (K + 2) * (x : ℂ) = K * x + 2 * x by ring, Complex.sin_sub, Complex.sin_add]
    ring
  have hc : ∀ j : ℤ, Continuous fun x : ℝ => f x * Complex.sin ((j : ℂ) * x) := by
    intro j
    have := hf.differentiable.continuous
    fun_prop
  simp_rw [hpt] at h0
  rw [intervalIntegral.integral_add (((hc _).intervalIntegrable _ _).const_mul _ |>.add
      (((hc _).intervalIntegrable _ _).const_mul _)) (((hc k).intervalIntegrable _ _).const_mul _),
    intervalIntegral.integral_add (((hc _).intervalIntegrable _ _).const_mul _)
      (((hc _).intervalIntegrable _ _).const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at h0
  linear_combination -h0

/-- Exponential decay of the cosine integrals of an even entire `2π`-periodic function. -/
theorem p2f_cos_coeff_decay {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (hper : ∀ z, F (z + 2 * π) = F z) (hev : ∀ z, F (-z) = F z) (R : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ m : ℕ,
      ‖∫ x in (0 : ℝ)..2 * π, F x * Complex.cos (m * x)‖ ≤ C * Real.exp (-(R * m)) := by
  have hc := hF.continuous
  obtain ⟨C, hC0, hC⟩ := p1a2_fourierInt_decay hF hper R
  refine ⟨C, hC0, fun m => ?_⟩
  have hs0 : ∫ x in (0 : ℝ)..2 * π, F x * Complex.sin (((m : ℤ) : ℂ) * x) = 0 := by
    apply p1a2_integral_odd_periodic (p1a2_periodic_mul_sin hper m)
    intro x
    push_cast
    rw [hev, show (m : ℂ) * -x = -(m * x) by ring, Complex.sin_neg]; ring
  have h := hC m
  rw [p1a2_fourierInt_eq hc, hs0, mul_zero, sub_zero] at h
  push_cast at h
  simpa using h

/-- Exponential decay of the sine integrals of an odd entire `2π`-periodic function. -/
theorem p2f_sin_coeff_decay {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (hper : ∀ z, F (z + 2 * π) = F z) (hodd : ∀ z, F (-z) = -F z) (R : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ m : ℕ,
      ‖∫ x in (0 : ℝ)..2 * π, F x * Complex.sin (m * x)‖ ≤ C * Real.exp (-(R * m)) := by
  have hc := hF.continuous
  obtain ⟨C, hC0, hC⟩ := p1a2_fourierInt_decay hF hper R
  refine ⟨C, hC0, fun m => ?_⟩
  have hc0 : ∫ x in (0 : ℝ)..2 * π, F x * Complex.cos (((m : ℤ) : ℂ) * x) = 0 := by
    apply p1a2_integral_odd_periodic (p1a2_periodic_mul_cos hper m)
    intro x
    push_cast
    rw [hodd, show (m : ℂ) * -x = -(m * x) by ring, Complex.cos_neg]; ring
  have h := hC m
  rw [p1a2_fourierInt_eq hc, hc0, zero_sub, norm_neg, norm_mul, Complex.norm_I, one_mul] at h
  push_cast at h
  simpa using h

/-- A sequence satisfying a three-term recurrence with `q ≠ 0` and two vanishing initial
values vanishes. -/
lemma p2f_chain_zero {q : ℂ} (hq : q ≠ 0) {b x : ℕ → ℂ}
    (hrec : ∀ j, b j * x (j + 1) = q * (x j + x (j + 2))) (h0 : x 0 = 0) (h1 : x 1 = 0) :
    ∀ j, x j = 0 := by
  have : ∀ j, x j = 0 ∧ x (j + 1) = 0 := by
    intro j
    induction j with
    | zero => exact ⟨h0, h1⟩
    | succ j ih =>
      refine ⟨ih.2, ?_⟩
      have h := hrec j
      rw [ih.1, ih.2, mul_zero, zero_add] at h
      exact (mul_eq_zero.1 h.symm).resolve_left hq
  exact fun j => (this j).1

/-- The Casoratian of two solutions of the same three-term recurrence is constant. -/
lemma p2f_chain_const {q : ℂ} (hq : q ≠ 0) {b x y : ℕ → ℂ}
    (hx : ∀ j, b j * x (j + 1) = q * (x j + x (j + 2)))
    (hy : ∀ j, b j * y (j + 1) = q * (y j + y (j + 2))) (j : ℕ) :
    x j * y (j + 1) - x (j + 1) * y j = x 0 * y 1 - x 1 * y 0 := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [← ih]
    have h : q * ((x (j + 1) * y (j + 1 + 1) - x (j + 1 + 1) * y (j + 1)) -
        (x j * y (j + 1) - x (j + 1) * y j)) = 0 := by
      linear_combination y (j + 1) * hx j - x (j + 1) * hy j
    exact sub_eq_zero.1 ((mul_eq_zero.1 h).resolve_left hq)

/-- **Coexistence is impossible** (Ince): for `q ≠ 0` an even and an odd solution of Mathieu's
equation cannot both be `π`-periodic, or both `π`-antiperiodic. -/
lemma p2f_ince_core {a q μ : ℂ} (hq : q ≠ 0) (hμ : μ = 1 ∨ μ = -1) {F G : ℂ → ℂ}
    (hF : IsMathieuSolution a q F) (hG : IsMathieuSolution a q G) (hFe : ∀ z, F (-z) = F z)
    (hGo : ∀ z, G (-z) = -G z) (hFp : ∀ z, F (z + π) = μ * F z)
    (hGp : ∀ z, G (z + π) = μ * G z) : F = 0 ∨ G = 0 := by
  have hμ2 : μ * μ = 1 := by rcases hμ with rfl | rfl <;> norm_num
  have hF2 : ∀ z, F (z + 2 * π) = F z := fun z => by
    rw [show z + 2 * π = z + π + π by ring, hFp, hFp, ← mul_assoc, hμ2, one_mul]
  have hG2 : ∀ z, G (z + 2 * π) = G z := fun z => by
    rw [show z + 2 * π = z + π + π by ring, hGp, hGp, ← mul_assoc, hμ2, one_mul]
  set α : ℤ → ℂ := fun k => ∫ x in (0 : ℝ)..2 * π, F x * Complex.cos (k * x) with hα
  set β : ℤ → ℂ := fun k => ∫ x in (0 : ℝ)..2 * π, G x * Complex.sin (k * x) with hβ
  have recα : ∀ k : ℤ, (a - (k : ℂ) ^ 2) * α k = q * (α (k - 2) + α (k + 2)) :=
    p1a2_cos_rec hF hF2
  have recβ : ∀ k : ℤ, (a - (k : ℂ) ^ 2) * β k = q * (β (k - 2) + β (k + 2)) :=
    p1a2_sin_rec hG hG2
  have αneg : ∀ k : ℤ, α (-k) = α k := fun k => by
    simp only [α]; congr 1; funext x; push_cast; rw [neg_mul, Complex.cos_neg]
  have βneg : ∀ k : ℤ, β (-k) = -β k := fun k => by
    simp only [β]; rw [← intervalIntegral.integral_neg]; congr 1; funext x; push_cast
    rw [neg_mul, Complex.sin_neg]; ring
  have β0 : β 0 = 0 := by simp [β]
  -- the sign of `cos m(x + π)`, `sin m(x + π)`
  have hcs : ∀ m : ℕ, ∀ x : ℂ, Complex.cos (m * (x + π)) = (-1) ^ m * Complex.cos (m * x) ∧
      Complex.sin (m * (x + π)) = (-1) ^ m * Complex.sin (m * x) := by
    intro m x
    have hc : Complex.cos (m * π) = (-1) ^ m := by
      induction m with
      | zero => simp
      | succ m ih => push_cast; rw [add_mul, one_mul, Complex.cos_add_pi, ih]; ring
    rw [show (m : ℂ) * (x + π) = m * x + m * π by ring, Complex.cos_add, Complex.sin_add,
      hc, Complex.sin_nat_mul_pi]
    constructor <;> ring
  -- wrong parity coefficients vanish
  have hwrong : ∀ m : ℕ, (-1 : ℂ) ^ m * μ = -1 → α m = 0 ∧ β m = 0 := by
    intro m hm
    have hFc := hF.differentiable.continuous
    have hGc := hG.differentiable.continuous
    constructor
    · simp only [α]
      apply p1a2_integral_antiperiodic (by push_cast; fun_prop)
      intro x; push_cast
      rw [hFp, (hcs m x).1]
      linear_combination (F x * Complex.cos (m * x)) * hm
    · simp only [β]
      apply p1a2_integral_antiperiodic (by push_cast; fun_prop)
      intro x; push_cast
      rw [hGp, (hcs m x).2]
      linear_combination (G x * Complex.sin (m * x)) * hm
  -- decay of the coefficients
  obtain ⟨Cα, hCα0, hCα⟩ := p2f_cos_coeff_decay hF.differentiable hF2 hFe 1
  obtain ⟨Cβ, hCβ0, hCβ⟩ := p2f_sin_coeff_decay hG.differentiable hG2 hGo 1
  have tα : ∀ k₀ : ℕ, Tendsto (fun j : ℕ => α ((k₀ + 2 * j : ℕ) : ℤ)) atTop (𝓝 0) := by
    intro k₀
    have hlim := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul Cα
    rw [mul_zero] at hlim
    refine squeeze_zero_norm (fun j => ?_) hlim
    have := hCα (k₀ + 2 * j)
    simp only [α, Int.cast_natCast, Function.comp_apply]
    refine this.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hCα0)
    push_cast; linarith [(Nat.cast_nonneg k₀ : (0 : ℝ) ≤ k₀), (Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  have tβ : ∀ k₀ : ℕ, Tendsto (fun j : ℕ => β ((k₀ + 2 * j : ℕ) : ℤ)) atTop (𝓝 0) := by
    intro k₀
    have hlim := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul Cβ
    rw [mul_zero] at hlim
    refine squeeze_zero_norm (fun j => ?_) hlim
    have := hCβ (k₀ + 2 * j)
    simp only [β, Int.cast_natCast, Function.comp_apply]
    refine this.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hCβ0)
    push_cast; linarith [(Nat.cast_nonneg k₀ : (0 : ℝ) ≤ k₀), (Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  -- the chains of coefficients of the right parity
  have hx : ∀ k₀ : ℕ, ∀ j : ℕ, (a - (((k₀ + 2 * (j + 1) : ℕ) : ℤ) : ℂ) ^ 2) *
      α ((k₀ + 2 * (j + 1) : ℕ) : ℤ) =
      q * (α ((k₀ + 2 * j : ℕ) : ℤ) + α ((k₀ + 2 * (j + 2) : ℕ) : ℤ)) := by
    intro k₀ j
    rw [recα]
    congr 3; push_cast; ring
  have hy : ∀ k₀ : ℕ, ∀ j : ℕ, (a - (((k₀ + 2 * (j + 1) : ℕ) : ℤ) : ℂ) ^ 2) *
      β ((k₀ + 2 * (j + 1) : ℕ) : ℤ) =
      q * (β ((k₀ + 2 * j : ℕ) : ℤ) + β ((k₀ + 2 * (j + 2) : ℕ) : ℤ)) := by
    intro k₀ j
    rw [recβ]
    congr 3; push_cast; ring
  have hD : ∀ k₀ : ℕ, α ((k₀ : ℕ) : ℤ) * β ((k₀ + 2 : ℕ) : ℤ) -
      α ((k₀ + 2 : ℕ) : ℤ) * β ((k₀ : ℕ) : ℤ) = 0 := by
    intro k₀
    have hc := p2f_chain_const hq (x := fun j => α ((k₀ + 2 * j : ℕ) : ℤ))
      (y := fun j => β ((k₀ + 2 * j : ℕ) : ℤ))
      (b := fun j => a - (((k₀ + 2 * (j + 1) : ℕ) : ℤ) : ℂ) ^ 2) (hx k₀) (hy k₀)
    have ht : Tendsto (fun j : ℕ => α ((k₀ + 2 * j : ℕ) : ℤ) * β ((k₀ + 2 * (j + 1) : ℕ) : ℤ) -
        α ((k₀ + 2 * (j + 1) : ℕ) : ℤ) * β ((k₀ + 2 * j : ℕ) : ℤ)) atTop (𝓝 0) := by
      have h1 := (tα k₀).comp (tendsto_add_atTop_nat 1)
      have h2 := (tβ k₀).comp (tendsto_add_atTop_nat 1)
      simpa using ((tα k₀).mul h2).sub (h1.mul (tβ k₀))
    simp only [hc] at ht
    have := tendsto_nhds_unique tendsto_const_nhds ht
    simpa using this
  have hzero : ∀ k₀ : ℕ, (∀ m : ℕ, (-1 : ℂ) ^ m * μ = 1 → ∃ j, m = k₀ + 2 * j) →
      ((α ((k₀ : ℕ) : ℤ) = 0 ∧ α ((k₀ + 2 : ℕ) : ℤ) = 0) → F = 0) ∧
      ((β ((k₀ : ℕ) : ℤ) = 0 ∧ β ((k₀ + 2 : ℕ) : ℤ) = 0) → G = 0) := by
    intro k₀ hk₀
    have hsign : ∀ m : ℕ, (-1 : ℂ) ^ m * μ = 1 ∨ (-1 : ℂ) ^ m * μ = -1 := by
      intro m
      rcases neg_one_pow_eq_or ℂ m with h | h <;> rcases hμ with rfl | rfl <;> simp [h]
    constructor
    · rintro ⟨h0, h1⟩
      have hall := p2f_chain_zero hq (x := fun j => α ((k₀ + 2 * j : ℕ) : ℤ))
        (b := fun j => a - (((k₀ + 2 * (j + 1) : ℕ) : ℤ) : ℂ) ^ 2) (hx k₀)
        (by simpa using h0) (by simpa using h1)
      have hm : ∀ m : ℕ, α m = 0 := by
        intro m
        rcases hsign m with h | h
        · obtain ⟨j, rfl⟩ := hk₀ m h
          exact_mod_cast hall j
        · exact (hwrong m h).1
      funext z
      have := p1a2_hasSum_cos hF.differentiable hF2 hFe z
      have e : ∀ m : ℕ, (∫ x in (0 : ℝ)..2 * π, F x * Complex.cos (m * x)) = 0 := fun m => by
        simpa [α] using hm m
      simp only [e, mul_zero, zero_mul] at this
      exact this.unique hasSum_zero
    · rintro ⟨h0, h1⟩
      have hall := p2f_chain_zero hq (x := fun j => β ((k₀ + 2 * j : ℕ) : ℤ))
        (b := fun j => a - (((k₀ + 2 * (j + 1) : ℕ) : ℤ) : ℂ) ^ 2) (hy k₀)
        (by simpa using h0) (by simpa using h1)
      have hm : ∀ m : ℕ, β m = 0 := by
        intro m
        rcases hsign m with h | h
        · obtain ⟨j, rfl⟩ := hk₀ m h
          exact_mod_cast hall j
        · exact (hwrong m h).2
      funext z
      have := p1a2_hasSum_sin hG.differentiable hG2 hGo z
      have e : ∀ m : ℕ, (∫ x in (0 : ℝ)..2 * π, G x * Complex.sin (m * x)) = 0 := fun m => by
        simpa [β] using hm m
      simp only [e, mul_zero, zero_mul] at this
      exact this.unique hasSum_zero
  rcases hμ with rfl | rfl
  · -- `π`-periodic case: the even chain
    obtain ⟨hzF, hzG⟩ := hzero 0 (fun m hm => by
      rcases Nat.even_or_odd' m with ⟨j, rfl | rfl⟩
      · exact ⟨j, by ring⟩
      · simp [pow_succ, pow_mul] at hm; norm_num at hm)
    have hD0 := hD 0
    simp only [Nat.cast_zero, zero_add, Nat.cast_ofNat, β0, mul_zero, sub_zero] at hD0
    rcases mul_eq_zero.1 hD0 with h | h
    · left
      refine hzF ⟨by simpa using h, ?_⟩
      have h0 := recα 0
      rw [show (0 : ℤ) - 2 = -2 by ring, zero_add, αneg, h] at h0
      simp only [Int.cast_zero] at h0
      have : q * (2 * α 2) = 0 := by linear_combination -h0
      simpa [hq] using this
    · right
      exact hzG ⟨by simpa using β0, by simpa using h⟩
  · -- `π`-antiperiodic case: the odd chain
    obtain ⟨hzF, hzG⟩ := hzero 1 (fun m hm => by
      rcases Nat.even_or_odd' m with ⟨j, rfl | rfl⟩
      · simp [pow_mul] at hm; norm_num at hm
      · exact ⟨j, by ring⟩)
    have hD1 := hD 1
    have hα1 := recα 1
    have hβ1 := recβ 1
    rw [show (1 : ℤ) - 2 = -1 by ring, αneg] at hα1
    rw [show (1 : ℤ) - 2 = -1 by ring, βneg] at hβ1
    norm_num at hD1 hα1 hβ1
    have h2 : q * (2 * (α 1 * β 1)) = 0 := by
      linear_combination q * hD1 - β 1 * hα1 + α 1 * hβ1
    rcases mul_eq_zero.1 ((mul_eq_zero.1 ((mul_eq_zero.1 h2).resolve_left hq)).resolve_left
      two_ne_zero) with h | h
    · left
      refine hzF ⟨by simpa using h, ?_⟩
      have : q * α 3 = 0 := by linear_combination -hα1 + (a - 1 - q) * h
      simpa [hq] using this
    · right
      refine hzG ⟨by simpa using h, ?_⟩
      have : q * β 3 = 0 := by linear_combination -hβ1 + (a - 1 + q) * h
      simpa [hq] using this

/-- **Theorem of Ince** (DLMF §28.2(iv)): for `q ≠ 0` the Floquet solution with respect to a
given `ν` is unique up to a constant factor. -/
@[dlmf 28.2.iv]
theorem IsFloquetSolution.unique {a q ν : ℂ} (hq : q ≠ 0) {w v : ℂ → ℂ}
    (hw : IsFloquetSolution a q ν w) (hv : IsFloquetSolution a q ν v) :
    ∃ c : ℂ, v = fun z => c * w z := by
  obtain ⟨hws, hw0, hwf⟩ := hw
  obtain ⟨hvs, -, hvf⟩ := hv
  set μ := Complex.exp (π * I * ν)
  have ew := hws.eq_combination
  have ev := hvs.eq_combination
  set w0 := w 0
  set w1 := deriv w 0
  set v0 := v 0
  set v1 := deriv v 0
  by_cases hdet : w0 * v1 - w1 * v0 = 0
  · by_cases h0 : w0 = 0
    · have h1 : w1 ≠ 0 := by
        intro h1
        apply hw0
        rw [ew]; funext z; simp [h0, h1]
      have hv0 : v0 = 0 := by
        rw [h0, zero_mul, zero_sub, neg_eq_zero] at hdet
        exact (mul_eq_zero.1 hdet).resolve_left h1
      refine ⟨v1 / w1, ?_⟩
      rw [ev]; funext z
      rw [congrFun ew z, h0, hv0]
      field_simp
      ring
    · refine ⟨v0 / w0, ?_⟩
      rw [ev]; funext z
      rw [congrFun ew z, div_mul_eq_mul_div, eq_div_iff h0]
      linear_combination (mathieuWII a q z) * hdet
  · exfalso
    have hI : ∀ z, mathieuWI a q z = (v1 * w z - w1 * v z) / (w0 * v1 - w1 * v0) := by
      intro z
      rw [eq_div_iff hdet, congrFun ew z, congrFun ev z]
      ring
    have hII : ∀ z, mathieuWII a q z = (w0 * v z - v0 * w z) / (w0 * v1 - w1 * v0) := by
      intro z
      rw [eq_div_iff hdet, congrFun ew z, congrFun ev z]
      ring
    have hIp : ∀ z, mathieuWI a q (z + π) = μ * mathieuWI a q z := by
      intro z; rw [hI, hI, hwf, hvf]; ring
    have hIIp : ∀ z, mathieuWII a q (z + π) = μ * mathieuWII a q z := by
      intro z; rw [hII, hII, hwf, hvf]; ring
    have hμ : μ * μ = 1 := by
      have h1 := hIp (-π)
      rw [neg_add_cancel, (mathieuWI_spec a q).2.1, mathieuWI_neg] at h1
      have h2 := hIp 0
      rw [zero_add, (mathieuWI_spec a q).2.1, mul_one] at h2
      rw [h2] at h1
      exact h1.symm
    have hμ' : μ = 1 ∨ μ = -1 := mul_self_eq_one_iff.1 hμ
    rcases p2f_ince_core hq hμ' (isMathieuSolution_mathieuWI a q)
      (isMathieuSolution_mathieuWII a q) (mathieuWI_neg a q) (mathieuWII_neg a q) hIp hIIp
      with h | h
    · have := (mathieuWI_spec a q).2.1
      rw [h] at this
      simp at this
    · have := (mathieuWII_spec a q).2.2
      rw [h] at this
      simp at this

/-- Integration by parts behind the Floquet recurrence 28.2.19. -/
lemma p2f_floquet_int_rec {a q ν : ℂ} {w : ℂ → ℂ} (hf : IsMathieuSolution a q w)
    (hfl : ∀ z, w (z + π) = Complex.exp (π * I * ν) * w z) (n : ℤ) :
    q * (∫ x in (0 : ℝ)..π, w x * Complex.exp (-(I * (ν + 2 * ((n + 1 : ℤ) : ℂ)) * x))) -
      (a - (ν + 2 * n) ^ 2) * (∫ x in (0 : ℝ)..π, w x * Complex.exp (-(I * (ν + 2 * n) * x))) +
      q * (∫ x in (0 : ℝ)..π, w x * Complex.exp (-(I * (ν + 2 * ((n - 1 : ℤ) : ℂ)) * x))) =
      0 := by
  set μ : ℂ := ν + 2 * n with hμ
  let E : ℝ → ℂ := fun x => Complex.exp (-(I * μ * x))
  let g : ℝ → ℂ := fun x => deriv w x * E x + I * μ * w x * E x
  have hE : ∀ x : ℝ, HasDerivAt E (-(I * μ) * E x) x := by
    intro x
    have hl : HasDerivAt (fun x : ℝ => -(I * μ) * (x : ℂ)) (-(I * μ)) x := by
      simpa using ((hasDerivAt_id (x : ℂ)).const_mul (-(I * μ))).comp_ofReal
    have := (Complex.hasDerivAt_exp _).comp x hl
    convert this using 1
    · funext y; simp only [E, Function.comp_apply]; ring_nf
    · simp only [E]; ring_nf
  have hg : ∀ x : ℝ, HasDerivAt g
      ((2 * q * Complex.cos (2 * x) - a + μ ^ 2) * (w x * E x)) x := by
    intro x
    have h1 : HasDerivAt (fun x : ℝ => deriv w x)
        ((2 * q * Complex.cos (2 * x) - a) * w x) x := (hf.hasDerivAt_deriv x).comp_ofReal
    have h0 : HasDerivAt (fun x : ℝ => w x) (deriv w x) x :=
      (hf.differentiable x).hasDerivAt.comp_ofReal
    convert (h1.mul (hE x)).add (((h0.const_mul (I * μ))).mul (hE x)) using 1
    ring_nf
    rw [I_sq]
    ring
  have hcont : Continuous fun x : ℝ =>
      (2 * q * Complex.cos (2 * x) - a + μ ^ 2) * (w x * E x) := by
    have := hf.differentiable.continuous
    fun_prop
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := π)
    (fun x _ => hg x) (hcont.intervalIntegrable _ _)
  have hwd : deriv w π = Complex.exp (π * I * ν) * deriv w 0 := by
    have h := congrArg (fun f => deriv f 0) (funext hfl)
    rw [deriv_comp_add_const, zero_add] at h
    rw [h, deriv_const_mul _ (hf.differentiable 0)]
  have hw0 : w π = Complex.exp (π * I * ν) * w 0 := by simpa using hfl 0
  have hEπ : E π * Complex.exp (π * I * ν) = 1 := by
    simp only [E, ← Complex.exp_add]
    rw [show -(I * μ * ((π : ℝ) : ℂ)) + π * I * ν = (-n : ℤ) * (2 * π * I) by
      rw [hμ]; push_cast; ring]
    exact Complex.exp_int_mul_two_pi_mul_I _
  have h0 : ∫ x in (0 : ℝ)..π, (2 * q * Complex.cos (2 * x) - a + μ ^ 2) * (w x * E x) = 0 := by
    rw [hint]
    simp only [g]
    rw [hwd, hw0]
    simp only [E, Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero, mul_one]
    linear_combination (deriv w 0 + I * μ * w 0) * hEπ
  have hpt : ∀ x : ℝ, (2 * q * Complex.cos (2 * x) - a + μ ^ 2) * (w x * E x) =
      q * (w x * Complex.exp (-(I * (ν + 2 * ((n + 1 : ℤ) : ℂ)) * x))) +
        q * (w x * Complex.exp (-(I * (ν + 2 * ((n - 1 : ℤ) : ℂ)) * x))) +
        (μ ^ 2 - a) * (w x * E x) := by
    intro x
    have e1 : Complex.exp (-(I * (ν + 2 * ((n + 1 : ℤ) : ℂ)) * x)) =
        E x * Complex.exp (-(2 * x) * I) := by
      simp only [E, ← Complex.exp_add]; congr 1; rw [hμ]; push_cast; ring
    have e2 : Complex.exp (-(I * (ν + 2 * ((n - 1 : ℤ) : ℂ)) * x)) =
        E x * Complex.exp ((2 * x) * I) := by
      simp only [E, ← Complex.exp_add]; congr 1; rw [hμ]; push_cast; ring
    rw [e1, e2, Complex.cos]
    ring
  have hc : ∀ m : ℂ, Continuous fun x : ℝ => w x * Complex.exp (-(I * m * x)) := by
    intro m
    have := hf.differentiable.continuous
    fun_prop
  have hcE : Continuous fun x : ℝ => w x * E x := hc μ
  simp_rw [hpt] at h0
  rw [intervalIntegral.integral_add (((hc _).intervalIntegrable _ _).const_mul _ |>.add
      (((hc _).intervalIntegrable _ _).const_mul _)) ((hcE.intervalIntegrable _ _).const_mul _),
    intervalIntegral.integral_add (((hc _).intervalIntegrable _ _).const_mul _)
      (((hc _).intervalIntegrable _ _).const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at h0
  linear_combination h0

/-- **Fourier series of a Floquet solution** (DLMF 28.2.18–28.2.19): a Floquet solution with
respect to `ν` is `w(z) = ∑_{n ∈ ℤ} c_{2n} e^{i(ν+2n)z}`, absolutely convergent (and locally
uniformly on `ℂ`), and the coefficients satisfy
`q c_{2n+2} - (a - (ν+2n)²) c_{2n} + q c_{2n-2} = 0`. (`c n` stands for DLMF's `c_{2n}`.) -/
@[dlmf 28.2.E18, dlmf 28.2.E19]
theorem IsFloquetSolution.exists_fourier {a q ν : ℂ} {w : ℂ → ℂ}
    (hw : IsFloquetSolution a q ν w) :
    ∃ c : ℤ → ℂ, (∀ z, Summable (fun n => ‖c n * Complex.exp (I * (ν + 2 * n) * z)‖)) ∧
      (∀ z, HasSum (fun n => c n * Complex.exp (I * (ν + 2 * n) * z)) (w z)) ∧
      ∀ n : ℤ, q * c (n + 1) - (a - (ν + 2 * n) ^ 2) * c n + q * c (n - 1) = 0 := by
  obtain ⟨hf, -, hfl⟩ := hw
  set U : ℂ → ℂ := fun z => Complex.exp (-(I * ν * (z / 2))) * w (z / 2) with hUdef
  have hU : Differentiable ℂ U := by
    have := hf.differentiable
    fun_prop
  have hUper : ∀ z, U (z + 2 * π) = U z := by
    intro z
    simp only [U]
    rw [show (z + 2 * π) / 2 = z / 2 + π by ring, hfl, ← mul_assoc, ← Complex.exp_add]
    congr 2
    ring
  set c : ℤ → ℂ := fun k => (1 / (2 * π) : ℂ) *
    ∫ x in (0 : ℝ)..2 * π, U x * Complex.exp (-(k * x * I)) with hc
  have hcJ : ∀ k : ℤ, c k = (1 / π : ℂ) *
      ∫ x in (0 : ℝ)..π, w x * Complex.exp (-(I * (ν + 2 * k) * x)) := by
    intro k
    have h := intervalIntegral.integral_comp_div (a := 0) (b := 2 * π)
      (fun s : ℝ => w s * Complex.exp (-(I * (ν + 2 * k) * s))) (two_ne_zero (α := ℝ))
    simp only [zero_div, show 2 * π / 2 = π by ring] at h
    simp only [c]
    rw [show (∫ x in (0 : ℝ)..2 * π, U x * Complex.exp (-(k * x * I))) =
        ∫ x in (0 : ℝ)..2 * π, w ((x / 2 : ℝ) : ℂ) *
          Complex.exp (-(I * (ν + 2 * k) * ((x / 2 : ℝ) : ℂ))) from ?_, h]
    · rw [real_smul]; push_cast; field_simp
    · congr 1; funext x
      simp only [U]; push_cast
      rw [mul_comm (Complex.exp _) (w _), mul_assoc, ← Complex.exp_add]
      congr 2; ring
  refine ⟨c, fun z => ?_, fun z => ?_, fun n => ?_⟩
  · obtain ⟨C, hC0, hC⟩ := p1a2_fourierInt_decay hU hUper (2 * |z.im| + 1)
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => ?_)
      (p1a2_summable_exp_neg_abs.mul_left
        (‖(1 / (2 * π) : ℂ)‖ * C * Real.exp (-(ν * z).im)))
    rw [norm_mul, norm_mul, Complex.norm_exp]
    have h1 := hC k
    have hre : (I * (ν + 2 * k) * z).re = -(ν * z).im - 2 * k * z.im := by
      simp [mul_re, mul_im]; ring
    rw [hre]
    have h2 : -(ν * z).im - 2 * k * z.im ≤ -(ν * z).im + 2 * |(k : ℝ)| * |z.im| := by
      have := neg_abs_le ((k : ℝ) * z.im)
      rw [abs_mul] at this
      linarith
    calc ‖(1 / (2 * π) : ℂ)‖ * ‖∫ x in (0 : ℝ)..2 * π, U x * Complex.exp (-(k * x * I))‖ *
          Real.exp (-(ν * z).im - 2 * k * z.im)
        ≤ ‖(1 / (2 * π) : ℂ)‖ * (C * Real.exp (-((2 * |z.im| + 1) * |(k : ℝ)|))) *
          Real.exp (-(ν * z).im + 2 * |(k : ℝ)| * |z.im|) := by
          gcongr
          · push_cast at h1 ⊢; exact h1
      _ = _ := by
          rw [show -(ν * z).im + 2 * |(k : ℝ)| * |z.im| =
            -(ν * z).im + -|(k : ℝ)| + (2 * |z.im| + 1) * |(k : ℝ)| by ring,
            Real.exp_add, Real.exp_add]
          have e : Real.exp (-((2 * |z.im| + 1) * |(k : ℝ)|)) *
              Real.exp ((2 * |z.im| + 1) * |(k : ℝ)|) = 1 := by
            rw [← Real.exp_add]; simp
          linear_combination (‖(1 / (2 * π) : ℂ)‖ * C * Real.exp (-(ν * z).im) *
            Real.exp (-|(k : ℝ)|)) * e
  · have h := (p1a2_hasSum_fourier hU hUper (2 * z)).mul_left (Complex.exp (I * ν * z))
    have e : Complex.exp (I * ν * z) * U (2 * z) = w z := by
      simp only [U]
      rw [show 2 * z / 2 = z by ring, ← mul_assoc, ← Complex.exp_add]
      rw [show I * ν * z + -(I * ν * z) = 0 by ring, Complex.exp_zero, one_mul]
    rw [e] at h
    convert h using 2 with k
    simp only [c]
    rw [show I * (ν + 2 * k) * z = k * (2 * z) * I + I * ν * z by ring, Complex.exp_add]
    ring
  · rw [hcJ, hcJ, hcJ]
    have := p2f_floquet_int_rec hf hfl n
    push_cast at this ⊢
    linear_combination (1 / π : ℂ) * this

/-- A function on `ℤ` that is eventually (cofinitely) at most `1` is bounded above. -/
lemma p2f_bound_cofinite {f : ℤ → ℝ} (h : ∀ᶠ n in cofinite, f n ≤ 1) :
    ∃ C, 0 ≤ C ∧ ∀ n, f n ≤ C := by
  have hfin : {n | ¬ f n ≤ 1}.Finite := Filter.eventually_cofinite.1 h
  obtain ⟨M, hM⟩ := (hfin.image f).bddAbove
  refine ⟨max 1 M, by positivity, fun n => ?_⟩
  by_cases hn : f n ≤ 1
  · exact hn.trans (le_max_left _ _)
  · exact (hM ⟨n, hn, rfl⟩).trans (le_max_right _ _)

/-- Exponential decay of a sequence with `|c_n|^{1/|n|} → 0`. -/
lemma p2f_coeff_decay {c : ℤ → ℂ}
    (hlim : Tendsto (fun n : ℤ => ‖c n‖ ^ (1 / (|n| : ℝ))) cofinite (𝓝 0)) (R : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ n, ‖c n‖ ≤ C * Real.exp (-(R * |(n : ℝ)|)) := by
  have h1 : ∀ᶠ n : ℤ in cofinite, ‖c n‖ ^ (1 / (|n| : ℝ)) < Real.exp (-R) :=
    hlim.eventually (gt_mem_nhds (Real.exp_pos _))
  have h2 : ∀ᶠ n : ℤ in cofinite, n ≠ 0 := Filter.eventually_cofinite_ne 0
  obtain ⟨C, hC0, hC⟩ := p2f_bound_cofinite (f := fun n => ‖c n‖ * Real.exp (R * |(n : ℝ)|))
    (by
      filter_upwards [h1, h2] with n hn hn0
      have hpos : (0 : ℝ) < |(n : ℝ)| := abs_pos.2 (by exact_mod_cast hn0)
      have e : ‖c n‖ = (‖c n‖ ^ (1 / (|n| : ℝ))) ^ (|(n : ℝ)|) := by
        rw [← Real.rpow_mul (norm_nonneg _), one_div,
          inv_mul_cancel₀ hpos.ne', Real.rpow_one]
      have hle : ‖c n‖ ≤ Real.exp (-R) ^ (|(n : ℝ)|) := by
        rw [e]
        exact Real.rpow_le_rpow (by positivity) hn.le hpos.le
      rw [← Real.exp_mul] at hle
      calc ‖c n‖ * Real.exp (R * |(n : ℝ)|) ≤ Real.exp (-R * |(n : ℝ)|) *
            Real.exp (R * |(n : ℝ)|) := by gcongr
        _ = 1 := by rw [← Real.exp_add]; simp)
  refine ⟨C, hC0, fun n => ?_⟩
  have := hC n
  have hp := Real.exp_pos (R * |(n : ℝ)|)
  calc ‖c n‖ = ‖c n‖ * Real.exp (R * |(n : ℝ)|) * Real.exp (-(R * |(n : ℝ)|)) := by
        rw [mul_assoc, ← Real.exp_add]; simp
    _ ≤ C * Real.exp (-(R * |(n : ℝ)|)) := by gcongr

/-- `‖x‖^k ≤ e^{2‖x‖}` for `k ≤ 2`. -/
lemma p2f_norm_pow_le {x : ℂ} {k : ℕ} (hk : k ≤ 2) : ‖x ^ k‖ ≤ Real.exp (2 * ‖x‖) := by
  rw [norm_pow]
  have h1 : max 1 ‖x‖ ≤ Real.exp ‖x‖ := max_le (Real.one_le_exp (norm_nonneg _))
    ((le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp _) |>.trans_eq' rfl)
  calc ‖x‖ ^ k ≤ (max 1 ‖x‖) ^ k := by gcongr; exact le_max_right _ _
    _ ≤ (max 1 ‖x‖) ^ 2 := pow_le_pow_right₀ (le_max_left _ _) hk
    _ ≤ Real.exp ‖x‖ ^ 2 := by gcongr
    _ = Real.exp (2 * ‖x‖) := by rw [← Real.exp_nat_mul]; norm_num

/-- Uniform bound for the terms `c_n (i(ν+2n))^k e^{i(ν+2n)z}`, `k ≤ 2`, `‖z‖ ≤ ρ`. -/
lemma p2f_floquet_term_bound {c : ℤ → ℂ}
    (hlim : Tendsto (fun n : ℤ => ‖c n‖ ^ (1 / (|n| : ℝ))) cofinite (𝓝 0)) (ν : ℂ) (ρ : ℝ) :
    ∃ u : ℤ → ℝ, Summable u ∧ ∀ (k : ℕ), k ≤ 2 → ∀ n (z : ℂ), ‖z‖ ≤ ρ →
      ‖c n * (I * (ν + 2 * n)) ^ k * Complex.exp (I * (ν + 2 * n) * z)‖ ≤ u n := by
  obtain ⟨C, hC0, hC⟩ := p2f_coeff_decay hlim (2 * (2 + ρ) + 1)
  refine ⟨fun n => C * Real.exp ((2 + ρ) * ‖ν‖) * Real.exp (-|(n : ℝ)|),
    p1a2_summable_exp_neg_abs.mul_left _, fun k hk n z hz => ?_⟩
  set X : ℝ := ‖ν‖ + 2 * |(n : ℝ)|
  have hX : ‖I * (ν + 2 * n)‖ ≤ X := by
    rw [norm_mul, Complex.norm_I, one_mul]
    refine (norm_add_le _ _).trans ?_
    simp [X]
  have hX0 : 0 ≤ X := by positivity
  rw [norm_mul, norm_mul, Complex.norm_exp]
  have e1 := p2f_norm_pow_le (x := I * (ν + 2 * n)) hk
  have e2 : (I * (ν + 2 * n) * z).re ≤ X * ρ := by
    refine (Complex.re_le_norm _).trans ?_
    rw [norm_mul]
    exact mul_le_mul hX hz (norm_nonneg _) hX0
  calc ‖c n‖ * ‖(I * (ν + 2 * n)) ^ k‖ * Real.exp (I * (ν + 2 * n) * z).re
      ≤ (C * Real.exp (-((2 * (2 + ρ) + 1) * |(n : ℝ)|))) * Real.exp (2 * X) *
          Real.exp (X * ρ) := by
        gcongr
        · exact hC n
        · exact e1.trans (Real.exp_le_exp.2 (by linarith))
    _ = _ := by
        rw [mul_assoc, mul_assoc, ← Real.exp_add, ← Real.exp_add]
        simp only
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        simp only [X]; ring

/-- **Converse** (DLMF 28.2.20): a nontrivial solution `c_{2n}` of the recurrence 28.2.19 with
`|c_{2n}|^{1/|n|} → 0` as `n → ±∞` yields a Floquet solution `∑ c_{2n} e^{i(ν+2n)z}`. -/
@[dlmf 28.2.E20]
theorem isFloquetSolution_of_recurrence {a q ν : ℂ} {c : ℤ → ℂ} (hc : c ≠ 0)
    (hrec : ∀ n : ℤ, q * c (n + 1) - (a - (ν + 2 * n) ^ 2) * c n + q * c (n - 1) = 0)
    (hlim : Tendsto (fun n : ℤ => ‖c n‖ ^ (1 / (|n| : ℝ))) (Filter.cofinite) (𝓝 0)) :
    IsFloquetSolution a q ν (fun z => ∑' n : ℤ, c n * Complex.exp (I * (ν + 2 * n) * z)) := by
  set g : ℕ → ℤ → ℂ → ℂ := fun k n z =>
    c n * (I * (ν + 2 * n)) ^ k * Complex.exp (I * (ν + 2 * n) * z) with hgdef
  have hsum : ∀ k, k ≤ 2 → ∀ z, Summable (fun n => g k n z) := by
    intro k hk z
    obtain ⟨u, hu, hb⟩ := p2f_floquet_term_bound hlim ν ‖z‖
    exact Summable.of_norm_bounded hu fun n => hb k hk n z le_rfl
  have hder : ∀ k, k ≤ 1 → ∀ y,
      HasDerivAt (fun z => ∑' n, g k n z) (∑' n, g (k + 1) n y) y := by
    intro k hk y
    obtain ⟨u, hu, hb⟩ := p2f_floquet_term_bound hlim ν (‖y‖ + 1)
    refine hasDerivAt_tsum_of_isPreconnected (t := Metric.ball 0 (‖y‖ + 1)) (y₀ := 0) hu
      Metric.isOpen_ball (convex_ball _ _).isPreconnected (fun n z _ => ?_)
      (fun n z hz => hb (k + 1) (by omega) n z (by simpa using (mem_ball_zero_iff.1 hz).le))
      (by simp; positivity) (hsum k (by omega) 0) (by simp)
    have := ((hasDerivAt_id z).const_mul (I * (ν + 2 * n))).cexp.const_mul
      (c n * (I * (ν + 2 * n)) ^ k)
    simp only [hgdef]
    convert this using 1
    · funext x; simp
    · simp; ring
  set w : ℂ → ℂ := fun z => ∑' n, g 0 n z with hwdef
  have hwe : (fun z => ∑' n : ℤ, c n * Complex.exp (I * (ν + 2 * n) * z)) = w := by
    funext z; simp [w, g]
  rw [hwe]
  have hdw : deriv w = fun z => ∑' n, g 1 n z := funext fun z => (hder 0 (by norm_num) z).deriv
  have hdiff : Differentiable ℂ w := fun z => (hder 0 (by norm_num) z).differentiableAt
  -- the differential equation
  have hode : ∀ z, ∑' n, g 2 n z = (2 * q * Complex.cos (2 * z) - a) * w z := by
    intro z
    set e : ℤ → ℂ := fun n => Complex.exp (I * (ν + 2 * n) * z)
    have S0 : HasSum (fun n => c n * e n) (w z) := by
      have := (hsum 0 (by norm_num) z).hasSum
      simpa [g, e, w] using this
    have Sp : HasSum (fun n => c (n + 1) * e n) (Complex.exp (-(2 * z) * I) * w z) := by
      have h := S0.mul_left (Complex.exp (-(2 * z) * I))
      have h' := (Equiv.addRight (1 : ℤ)).hasSum_iff.2 h
      convert h' using 1
      funext n
      simp only [Function.comp_apply, Equiv.coe_addRight, e]
      rw [mul_left_comm, ← Complex.exp_add]
      congr 2; push_cast; ring
    have Sm : HasSum (fun n => c (n - 1) * e n) (Complex.exp ((2 * z) * I) * w z) := by
      have h := S0.mul_left (Complex.exp ((2 * z) * I))
      have h' := (Equiv.subRight (1 : ℤ)).hasSum_iff.2 h
      convert h' using 1
      funext n
      simp only [Function.comp_apply, Equiv.subRight_apply, e]
      rw [mul_left_comm, ← Complex.exp_add]
      congr 2; push_cast; ring
    have S2 : HasSum (fun n => g 2 n z) (q * (Complex.exp (-(2 * z) * I) * w z) +
        q * (Complex.exp ((2 * z) * I) * w z) - a * w z) := by
      have := ((Sp.mul_left q).add (Sm.mul_left q)).sub (S0.mul_left a)
      convert this using 1
      funext n
      simp only [g, e]
      have hr := hrec n
      have hI : (I * (ν + 2 * n)) ^ 2 = -(ν + 2 * n) ^ 2 := by rw [mul_pow, I_sq]; ring
      rw [hI]
      linear_combination (-Complex.exp (I * (ν + 2 * n) * z)) * hr
    rw [S2.tsum_eq, Complex.cos]
    ring
  refine ⟨⟨hdiff, fun z => ?_⟩, ?_, fun z => ?_⟩
  · rw [hdw, ← hode]
    exact hder 1 le_rfl z
  · -- nontriviality: the coefficients are recovered by integration over `[0, π]`
    intro hw0
    obtain ⟨m, hm⟩ := Function.ne_iff.1 hc
    obtain ⟨C, hC0, hC⟩ := p2f_coeff_decay hlim 1
    have hcs : Summable fun n => ‖c n‖ :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hC
        (p1a2_summable_exp_neg_abs.mul_left C |>.congr fun n => by simp)
    have hlimt : ∀ t : ℝ, HasSum (fun n => c n * Complex.exp (2 * I * (n - m) * t)) 0 := by
      intro t
      have h0 : HasSum (fun n => g 0 n t) 0 := by
        have := (hsum 0 (by norm_num) t).hasSum
        rwa [show (∑' n, g 0 n t) = w t from rfl, hw0] at this
      have := h0.mul_left (Complex.exp (-(I * (ν + 2 * m) * t)))
      rw [mul_zero] at this
      convert this using 1
      funext n
      simp only [g, pow_zero, mul_one]
      rw [mul_left_comm, ← Complex.exp_add]
      congr 2; ring
    have hint := intervalIntegral.hasSum_integral_of_dominated_convergence (a := 0) (b := π)
      (μ := MeasureTheory.volume) (F := fun n (t : ℝ) => c n * Complex.exp (2 * I * (n - m) * t))
      (f := fun _ => 0) (fun n _ => ‖c n‖)
      (fun n => (by fun_prop : Continuous fun t : ℝ =>
        c n * Complex.exp (2 * I * (n - m) * t)).aestronglyMeasurable)
      (fun n => MeasureTheory.ae_of_all _ fun t _ => by
        rw [norm_mul, Complex.norm_exp]
        simp [mul_re, mul_im])
      (MeasureTheory.ae_of_all _ fun t _ => hcs) intervalIntegrable_const
      (MeasureTheory.ae_of_all _ fun t _ => hlimt t)
    simp only [intervalIntegral.integral_zero] at hint
    have hval : ∀ n : ℤ, (∫ t in (0 : ℝ)..π, c n * Complex.exp (2 * I * (n - m) * t)) =
        if n = m then c m * π else 0 := by
      intro n
      rw [intervalIntegral.integral_const_mul]
      split_ifs with hnm
      · subst hnm; simp [mul_comm]
      · have hne : 2 * I * ((n : ℂ) - m) ≠ 0 := by
          refine mul_ne_zero (mul_ne_zero two_ne_zero I_ne_zero) (sub_ne_zero.2 ?_)
          exact_mod_cast hnm
        rw [integral_exp_mul_complex hne]
        have : Complex.exp (2 * I * ((n : ℂ) - m) * (π : ℝ)) = 1 := by
          rw [show 2 * I * ((n : ℂ) - m) * ((π : ℝ) : ℂ) = ((n - m : ℤ) : ℂ) * (2 * π * I) by
            push_cast; ring]
          exact Complex.exp_int_mul_two_pi_mul_I _
        simp [this]
    simp only [hval] at hint
    have := hint.unique (hasSum_ite_eq m (c m * π))
    exact hm (by
      have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      simpa [hπ] using this.symm)
  · simp only [w, g, pow_zero, mul_one]
    rw [← tsum_mul_left]
    congr 1; funext n
    rw [show I * (ν + 2 * n) * (z + π) = (π * I * ν + I * (ν + 2 * n) * z) +
      (n : ℂ) * (2 * π * I) by ring, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one,
      Complex.exp_add]
    ring

end DLMF.Mathieu
end
