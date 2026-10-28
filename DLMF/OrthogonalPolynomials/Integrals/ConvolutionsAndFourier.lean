/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.OrthogonalPolynomials.Integrals.LaguerreAndHermite

/-!
# Polynomial convolutions and Fourier transforms

Jacobi weighted integrals, Laguerre convolutions and Fourier transforms of classical
polynomials.

Source references and common attribution are retained in
`DLMF.OrthogonalPolynomials.Integrals`.
-/

@[expose] public section

open Complex Polynomial MeasureTheory Filter

open scoped Real Nat Topology

open DLMF.Hypergeometric

open DLMF.Confluent

open DLMF.Bessel

open DLMF.Gamma (Gamma_add_nat_eq_poch_mul_Gamma)

noncomputable section

set_option autoImplicit false

namespace DLMF.OrthogonalPolynomials

/-- The weighted Jacobi antiderivative on an interval contained in `(-1,1)`. -/
@[dlmf 18.17.E1]
theorem jacobi_weighted_integral {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) (n : ℕ) {x : ℝ} (hx : x ∈ Set.Ioo (-1) 1) :
    2 * (n + 1 : ℂ) * (∫ y : ℝ in (0 : ℝ)..x, (1 - (y : ℂ)) ^ (α : ℂ) *
      (1 + (y : ℂ)) ^ (β : ℂ) * jacobiPolyP α β (n + 1) y) =
      jacobiPolyP (α + 1) (β + 1) n 0 - (1 - (x : ℂ)) ^ (α + 1 : ℂ) *
        (1 + (x : ℂ)) ^ (β + 1 : ℂ) * jacobiPolyP (α + 1) (β + 1) n x := by
  have hreg (a b : ℝ) (m : ℕ) (t : ℝ) (ht : t ∈ Set.Ioo (-1) 1) :
      DifferentiableAt ℝ (fun y : ℝ => (1 - (y : ℂ)) ^ (a : ℂ) *
        (1 + (y : ℂ)) ^ (b : ℂ) * jacobiPolyP a b m y) t := by
    have h1 : (1 - (t : ℂ)) ∈ slitPlane := by
      rw [show (1 - (t : ℂ)) = ((1 - t : ℝ) : ℂ) by push_cast; ring]
      exact Complex.ofReal_mem_slitPlane.mpr (by linarith [ht.2])
    have h2 : (1 + (t : ℂ)) ∈ slitPlane := by
      rw [show (1 + (t : ℂ)) = ((1 + t : ℝ) : ℂ) by push_cast; ring]
      exact Complex.ofReal_mem_slitPlane.mpr (by linarith [ht.1])
    exact (((((hasDerivAt_id' (t : ℂ)).const_sub 1).cpow_const h1).comp_ofReal).mul
      ((((hasDerivAt_id' (t : ℂ)).const_add 1).cpow_const h2).comp_ofReal)).differentiableAt.mul
      (((analyticOnNhd_jacobiPolyP a b m) t
          (Set.mem_univ _)).differentiableAt.hasDerivAt.comp_ofReal).differentiableAt
  have hmem (t : ℝ) (ht : t ∈ Set.uIcc 0 x) : t ∈ Set.Ioo (-1) 1 := by
    rcases Set.mem_uIcc.mp ht with ht | ht <;> constructor <;>
      linarith [ht.1, ht.2, hx.1, hx.2]
  let g : ℝ → ℂ := fun y => (1 - (y : ℂ)) ^ (α + 1 : ℂ) *
    (1 + (y : ℂ)) ^ (β + 1 : ℂ) * jacobiPolyP (α + 1) (β + 1) n y
  have hd (t : ℝ) (ht : t ∈ Set.uIcc 0 x) : HasDerivAt (fun y => -g y)
      (2 * (n + 1 : ℂ) * ((1 - (t : ℂ)) ^ (α : ℂ) *
        (1 + (t : ℂ)) ^ (β : ℂ) * jacobiPolyP α β (n + 1) t)) t := by
    have hg : DifferentiableAt ℝ g t := by
      simpa only [g, ofReal_add, ofReal_one] using hreg (α + 1) (β + 1) n t (hmem t ht)
    have hh := hg.hasDerivAt.neg
    have he := jacobi_weighted_derivative (α := α + 1) (β := β + 1)
      (by linarith) (by linarith) n (hmem t ht)
    simp only [ofReal_add, ofReal_one, add_sub_cancel_right] at he
    change deriv g t = _ at he
    rw [he] at hh
    convert hh using 1; ring
  have hi : IntervalIntegrable (fun y : ℝ => 2 * (n + 1 : ℂ) *
      ((1 - (y : ℂ)) ^ (α : ℂ) * (1 + (y : ℂ)) ^ (β : ℂ) *
        jacobiPolyP α β (n + 1) y)) volume 0 x := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    exact (continuousAt_const.mul (hreg α β (n + 1) t (hmem t ht)).continuousAt).continuousWithinAt
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
  rw [intervalIntegral.integral_const_mul] at hh
  simpa [g, sub_eq_add_neg, add_comm] using hh

/-- Identity under the stated parameter and domain assumptions: `∫ y : ℝ in (0 : ℝ)..x,
laguerrePolyL 0 m y * laguerrePolyL 0 n (x - y) = laguerrePolyL 0 (m + n) x - laguerrePolyL 0
(m + n + 1) x`. -/
@[dlmf 18.17.E2]
theorem laguerrePolyL_unweighted_convolution (m n : ℕ) (x : ℝ) :
    ∫ y : ℝ in (0 : ℝ)..x, laguerrePolyL 0 m y * laguerrePolyL 0 n (x - y) =
      laguerrePolyL 0 (m + n) x - laguerrePolyL 0 (m + n + 1) x := by
  let A : ℕ → ℝ → ℂ := fun j y => laguerrePolyL 0 j y - laguerrePolyL 0 (j + 1) y
  let D : ℕ → ℝ → ℂ := fun j y => -deriv (laguerrePolyL 0 j) ((x : ℂ) - y)
  let C : ℕ → ℕ → ℂ := fun i j => ∫ y : ℝ in (0 : ℝ)..x,
    laguerrePolyL 0 i y * laguerrePolyL 0 j ((x : ℂ) - y)
  have hL (a : ℂ) (ha : -1 < a.re) (j : ℕ) : Continuous (laguerrePolyL a j) :=
    continuous_iff_continuousAt.mpr fun y => (analyticAt_laguerrePolyL ha j y).continuousAt
  have hdL (j : ℕ) (y : ℝ) : HasDerivAt (fun t : ℝ => laguerrePolyL 0 j t)
      (deriv (laguerrePolyL 0 j) y) y :=
    ((analyticAt_laguerrePolyL (by norm_num) j (y : ℂ)).differentiableAt.hasDerivAt).comp_ofReal
  have hA (j : ℕ) (y : ℝ) : HasDerivAt (A j) (laguerrePolyL 0 j y) y := by
    have h := (hdL j y).sub (hdL (j + 1) y)
    convert h using 1
    linear_combination (laguerrePolyL_deriv_succ_sub (α := 0) (by norm_num) j y)
  have hAcont (j : ℕ) : Continuous (A j) :=
    ((hL 0 (by norm_num) j).comp continuous_ofReal).sub
      ((hL 0 (by norm_num) (j + 1)).comp continuous_ofReal)
  have hDcont (j : ℕ) : Continuous (D j) := by
    cases j with
    | zero =>
      have h0 : laguerrePolyL 0 0 = fun _ => 1 := funext fun y => laguerrePolyL_zero 0 y
      simp only [D, h0, deriv_const, neg_zero]
      exact continuous_const
    | succ j =>
      have hder : deriv (laguerrePolyL 0 (j + 1)) = fun y => -laguerrePolyL 1 j y :=
        funext fun y => by simpa using laguerrePolyL_derivative (α := 0) (by norm_num) j y
      simp only [D, hder, neg_neg]
      exact (hL 1 (by norm_num) j).comp (continuous_const.sub continuous_ofReal)
  have hzero (j : ℕ) : laguerrePolyL 0 j 0 = 1 := by
    simp [laguerrePolyL_at_zero, poch, ascPochhammer_eval_one, Nat.factorial_ne_zero]
  have hIBP (i j : ℕ) : C i j = A i x - ∫ y : ℝ in (0 : ℝ)..x, D j y * A i y := by
    have hu (y : ℝ) : HasDerivAt (fun t : ℝ => laguerrePolyL 0 j ((x : ℂ) - t)) (D j y) y := by
      have h := (analyticAt_laguerrePolyL (α := 0) (by norm_num) j
          ((x : ℂ) - y)).differentiableAt.hasDerivAt
      have hc := (h.comp (y : ℂ) ((hasDerivAt_id (y : ℂ)).const_sub (x : ℂ))).comp_ofReal
      simpa only [D, Function.comp_apply, mul_neg, mul_one] using hc
    have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (a := (0 : ℝ)) (b := x) (fun y _ => hu y) (fun y _ => hA i y)
      ((hDcont j).intervalIntegrable _ _)
      (((hL 0 (by norm_num) i).comp continuous_ofReal).intervalIntegrable _ _)
    have hleft : (∫ y : ℝ in (0 : ℝ)..x, laguerrePolyL 0 j ((x : ℂ) - y) * laguerrePolyL 0 i y)
        = C i j := by
      apply intervalIntegral.integral_congr
      intro y _
      dsimp [C]
      ring
    rw [hleft] at h
    simpa [A, hzero] using h
  have hstep (i j : ℕ) : C i (j + 1) = C (i + 1) j := by
    have hD (y : ℝ) : D (j + 1) y = D j y + laguerrePolyL 0 j ((x : ℂ) - y) := by
      dsimp [D]
      linear_combination -(laguerrePolyL_deriv_succ_sub (α := 0) (by norm_num) j ((x : ℂ) - y))
    have hsplit : (∫ y : ℝ in (0 : ℝ)..x, D (j + 1) y * A i y) =
        (∫ y : ℝ in (0 : ℝ)..x, D j y * A i y) + C i j - C (i + 1) j := by
      have heq : (fun y => D (j + 1) y * A i y) = fun y => D j y * A i y +
          laguerrePolyL 0 i y * laguerrePolyL 0 j ((x : ℂ) - y) -
          laguerrePolyL 0 (i + 1) y * laguerrePolyL 0 j ((x : ℂ) - y) := by
        funext y
        rw [hD]
        dsimp [A]
        ring
      have hprod (k : ℕ) : Continuous (fun y : ℝ =>
          laguerrePolyL 0 k y * laguerrePolyL 0 j ((x : ℂ) - y)) :=
        ((hL 0 (by norm_num) k).comp continuous_ofReal).mul
          ((hL 0 (by norm_num) j).comp (continuous_const.sub continuous_ofReal))
      have hDA : Continuous (fun y => D j y * A i y) := (hDcont j).mul (hAcont i)
      rw [heq, intervalIntegral.integral_sub
        (f := fun y => D j y * A i y + laguerrePolyL 0 i y * laguerrePolyL 0 j ((x : ℂ) - y))
        (g := fun y => laguerrePolyL 0 (i + 1) y * laguerrePolyL 0 j ((x : ℂ) - y))
        ((hDA.add (hprod i)).intervalIntegrable _ _)
        ((hprod (i + 1)).intervalIntegrable _ _),
        intervalIntegral.integral_add
          (f := fun y => D j y * A i y)
          (g := fun y => laguerrePolyL 0 i y * laguerrePolyL 0 j ((x : ℂ) - y))
          (hDA.intervalIntegrable _ _)
          ((hprod i).intervalIntegrable _ _)]
    rw [hIBP, hsplit, hIBP i j]
    ring
  have hbase (i : ℕ) : C i 0 = A i x := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0 : ℝ)) (b := x)
      (fun y _ => hA i y) (((hL 0 (by norm_num) i).comp continuous_ofReal).intervalIntegrable _ _)
    simpa [C, A, hzero] using h
  have hconv : ∀ i j : ℕ, C i j = A (i + j) x := by
    intro i j
    induction j generalizing i with
    | zero => simpa using hbase i
    | succ j ih => rw [hstep, ih]; congr 1; omega
  exact hconv m n

open Set in
/-- Integration by parts against the Gegenbauer angular weight. -/
private lemma gegProd_ibp {lam : ℝ} (hlam : 0 < lam) (a v : ℝ) {f f' : ℂ → ℂ}
    (hf : ∀ z, HasDerivAt f (f' z) z) (hf' : Continuous f') :
    ∫ t : ℝ in (0 : ℝ)..π, (Real.cos t : ℂ) * f ((a + v * Real.cos t : ℝ)) *
        ((Real.sin t ^ (2 * lam - 1) : ℝ) : ℂ) =
      (v : ℂ) / (2 * lam) * ∫ t : ℝ in (0 : ℝ)..π, f' ((a + v * Real.cos t : ℝ)) *
        ((Real.sin t ^ (2 * (lam + 1) - 1) : ℝ) : ℂ) := by
  set ρ : ℝ → ℂ := fun t => ((Real.sin t ^ (2 * lam - 1) : ℝ) : ℂ) with hρ
  set w : ℝ → ℂ := fun t => ((a + v * Real.cos t : ℝ) : ℂ) with hw
  have hfc : Continuous f := continuous_iff_continuousAt.2 fun z => (hf z).continuousAt
  have hρi : IntervalIntegrable ρ volume 0 π := by
    have := (integral_sin_rpow_aux hlam).1
    exact ⟨this.1.ofReal, this.2.ofReal⟩
  have hU : uIcc (0 : ℝ) π = Icc 0 π := uIcc_of_le Real.pi_pos.le
  have hsplit : ∀ x : ℝ, 0 ≤ x → x ^ (2 * lam) = x * x ^ (2 * lam - 1) := by
    intro x hx
    rcases hx.eq_or_lt with h | h
    · subst h; rw [Real.zero_rpow (by positivity), zero_mul]
    · rw [← Real.rpow_one_add' h.le (by linarith)]; ring_nf
  have hsplit2 : ∀ x : ℝ, 0 ≤ x → x ^ (2 * (lam + 1) - 1) = x ^ 2 * x ^ (2 * lam - 1) := by
    intro x hx
    rcases hx.eq_or_lt with h | h
    · subst h; rw [Real.zero_rpow (by linarith)]; simp
    · rw [show 2 * (lam + 1) - 1 = 2 + (2 * lam - 1) by ring, Real.rpow_add h]
      norm_cast
  have hwc : Continuous w := by fun_prop
  set g : ℝ → ℂ := fun t => f' (w t) * (-(v : ℂ) * Real.sin t) * Real.sin t +
    f (w t) * (2 * lam * Real.cos t) with hg
  have hgc : Continuous g := by
    simp only [hg]
    have : Continuous fun t => f' (w t) := hf'.comp hwc
    have : Continuous fun t => f (w t) := hfc.comp hwc
    fun_prop
  have hD : ∀ t ∈ Ioo (0 : ℝ) π, HasDerivAt (fun t : ℝ => f (w t) *
      ((Real.sin t ^ (2 * lam) : ℝ) : ℂ)) (ρ t * g t) t := by
    intro t ht
    have hst : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2
    have hwd : HasDerivAt w (-(v : ℂ) * Real.sin t) t := by
      have := (((Real.hasDerivAt_cos t).const_mul v).const_add a).ofReal_comp
      exact this.congr_deriv (by push_cast; ring)
    have hfw : HasDerivAt (fun t => f (w t)) (f' (w t) * (-(v : ℂ) * Real.sin t)) t :=
      (hf (w t)).comp t hwd
    have hr := ((Real.hasDerivAt_sin t).rpow_const (p := 2 * lam) (Or.inl hst.ne')).ofReal_comp
    have := hfw.mul hr
    refine this.congr_deriv ?_
    simp only [hρ, hg]
    rw [hsplit _ hst.le]
    push_cast
    ring
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le Real.pi_pos.le
    ((hfc.comp hwc).continuousOn.mul
      (Complex.continuous_ofReal.comp ((Real.continuous_rpow_const (by positivity)).comp
        Real.continuous_sin)).continuousOn) hD (hρi.mul_continuousOn (hU ▸ hgc.continuousOn))
  simp only [Pi.mul_apply, Function.comp_apply, Real.sin_pi, Real.sin_zero,
    Real.zero_rpow (by positivity : 2 * lam ≠ 0), Complex.ofReal_zero, mul_zero, sub_zero] at hFTC
  have h1 : IntervalIntegrable (fun t => ρ t * (f' (w t) * (-(v : ℂ) * Real.sin t) * Real.sin t))
      volume 0 π := hρi.mul_continuousOn (hU ▸ (by
        have : Continuous fun t => f' (w t) := hf'.comp hwc
        fun_prop : Continuous fun t => f' (w t) * (-(v : ℂ) * Real.sin t) * Real.sin t).continuousOn)
  have h2 : IntervalIntegrable (fun t => ρ t * (f (w t) * (2 * lam * Real.cos t)))
      volume 0 π := hρi.mul_continuousOn (hU ▸ (by
        have : Continuous fun t => f (w t) := hfc.comp hwc
        fun_prop : Continuous fun t => f (w t) * (2 * lam * Real.cos t)).continuousOn)
  have hsum : ∫ t in (0 : ℝ)..π, ρ t * g t =
      (∫ t in (0 : ℝ)..π, ρ t * (f' (w t) * (-(v : ℂ) * Real.sin t) * Real.sin t)) +
      ∫ t in (0 : ℝ)..π, ρ t * (f (w t) * (2 * lam * Real.cos t)) := by
    rw [← intervalIntegral.integral_add h1 h2]
    exact intervalIntegral.integral_congr fun t _ => by simp only [hg]; ring
  have hA : (∫ t in (0 : ℝ)..π, ρ t * (f' (w t) * (-(v : ℂ) * Real.sin t) * Real.sin t)) =
      -(v : ℂ) * ∫ t : ℝ in (0 : ℝ)..π, f' (w t) *
        ((Real.sin t ^ (2 * (lam + 1) - 1) : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [hU] at ht
    have hs0 : 0 ≤ Real.sin t := Real.sin_nonneg_of_nonneg_of_le_pi ht.1 ht.2
    simp only [hρ]
    rw [hsplit2 _ hs0]
    push_cast
    ring
  have hB : (∫ t in (0 : ℝ)..π, ρ t * (f (w t) * (2 * lam * Real.cos t))) =
      2 * lam * ∫ t : ℝ in (0 : ℝ)..π, (Real.cos t : ℂ) * f (w t) * ρ t := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun t _ => by ring
  rw [hsum, hA, hB] at hFTC
  have hlam' : (2 * lam : ℂ) ≠ 0 := by
    have : (2 * lam : ℝ) ≠ 0 := by positivity
    exact_mod_cast this
  show (∫ t in (0 : ℝ)..π, (Real.cos t : ℂ) * f (w t) * ρ t) = (v : ℂ) / (2 * lam) *
    ∫ t in (0 : ℝ)..π, f' (w t) * ((Real.sin t ^ (2 * (lam + 1) - 1) : ℝ) : ℂ)
  rw [div_mul_eq_mul_div, eq_div_iff hlam']
  linear_combination hFTC
/-- Gegenbauer polynomials are continuous. -/
private lemma gegProd_continuous (lam : ℂ) (n : ℕ) : Continuous (ultrasphPoly lam n) :=
  continuousOn_univ.1 (analyticOnNhd_ultrasphPoly lam n).continuousOn

/-- Continuous functions are integrable against the angular weight `sin^{2λ-1}` on `[0, π]`. -/
private lemma gegProd_intble {lam : ℝ} (hlam : 0 < lam) {h : ℝ → ℂ} (hh : Continuous h) :
    IntervalIntegrable (fun t => h t * ((Real.sin t ^ (2 * lam - 1) : ℝ) : ℂ)) volume 0 π := by
  have := (integral_sin_rpow_aux hlam).1
  have hρi : IntervalIntegrable (fun t => ((Real.sin t ^ (2 * lam - 1) : ℝ) : ℂ)) volume 0 π :=
    ⟨this.1.ofReal, this.2.ofReal⟩
  exact hρi.continuousOn_mul hh.continuousOn

/-- The three-term recurrence of the Gegenbauer polynomials, integrated against the angular
weight along `t ↦ a + v cos t`; the middle term is integrated by parts, which raises `λ` by one. -/
private lemma gegProd_step {lam : ℝ} (hlam : 0 < lam) (a v : ℝ) (k : ℕ) :
    (k + 2 : ℂ) * (∫ t : ℝ in (0 : ℝ)..π, ultrasphPoly lam (k + 2) ((a + v * Real.cos t : ℝ) : ℂ) *
      ((Real.sin t ^ (2 * lam - 1) : ℝ) : ℂ)) =
      2 * (k + lam + 1) * a * (∫ t : ℝ in (0 : ℝ)..π,
        ultrasphPoly lam (k + 1) ((a + v * Real.cos t : ℝ) : ℂ) *
          ((Real.sin t ^ (2 * lam - 1) : ℝ) : ℂ)) +
      2 * (k + lam + 1) * v * (v * ∫ t : ℝ in (0 : ℝ)..π,
        ultrasphPoly ((lam : ℂ) + 1) k ((a + v * Real.cos t : ℝ) : ℂ) *
          ((Real.sin t ^ (2 * (lam + 1) - 1) : ℝ) : ℂ)) -
      (k + 2 * lam) * (∫ t : ℝ in (0 : ℝ)..π, ultrasphPoly lam k ((a + v * Real.cos t : ℝ) : ℂ) *
        ((Real.sin t ^ (2 * lam - 1) : ℝ) : ℂ)) := by
  have hlre : -1 / 2 < (lam : ℂ).re := by simp; linarith
  set ρ : ℝ → ℂ := fun t => ((Real.sin t ^ (2 * lam - 1) : ℝ) : ℂ) with hρ
  set ρ' : ℝ → ℂ := fun t => ((Real.sin t ^ (2 * (lam + 1) - 1) : ℝ) : ℂ) with hρ'
  set z : ℝ → ℂ := fun t => ((a + v * Real.cos t : ℝ) : ℂ) with hz
  have hzc : Continuous z := by fun_prop
  set I : ℕ → ℂ := fun j => ∫ t : ℝ in (0 : ℝ)..π, ultrasphPoly lam j (z t) * ρ t with hI
  set J : ℂ := ∫ t : ℝ in (0 : ℝ)..π, ultrasphPoly ((lam : ℂ) + 1) k (z t) * ρ' t with hJ
  change (k + 2 : ℂ) * I (k + 2) = 2 * (k + lam + 1) * a * I (k + 1) +
    2 * (k + lam + 1) * v * (v * J) - (k + 2 * lam) * I k
  -- integration by parts
  have hK : (∫ t : ℝ in (0 : ℝ)..π, (Real.cos t : ℂ) * ultrasphPoly lam (k + 1) (z t) * ρ t) =
      v * J := by
    have hd : ∀ w : ℂ, HasDerivAt (ultrasphPoly lam (k + 1))
        (2 * lam * ultrasphPoly ((lam : ℂ) + 1) k w) w := by
      intro w
      rw [← ultrasphPoly_derivative hlre k w]
      exact (analyticAt_ultrasphPoly _ _ w).differentiableAt.hasDerivAt
    have := gegProd_ibp hlam a v hd
      ((gegProd_continuous _ k).const_mul (2 * (lam : ℂ)))
    rw [this, intervalIntegral.integral_congr (g := fun t => (2 * (lam : ℂ)) *
      (ultrasphPoly ((lam : ℂ) + 1) k (z t) * ρ' t)) (fun t _ => by simp only [hz, hρ']; ring),
      intervalIntegral.integral_const_mul]
    have hl : (2 * lam : ℂ) ≠ 0 := by
      have : (2 * lam : ℝ) ≠ 0 := by positivity
      exact_mod_cast this
    rw [← mul_assoc, div_mul_eq_mul_div, mul_div_assoc, div_self hl, mul_one]
  -- the three-term recurrence under the integral
  have hcj : ∀ j : ℕ, Continuous fun t => ultrasphPoly lam j (z t) :=
    fun j => (gegProd_continuous _ j).comp hzc
  have iA : IntervalIntegrable (fun t => ultrasphPoly lam (k + 1) (z t) * ρ t) volume 0 π :=
    gegProd_intble hlam (hcj _)
  have iB : IntervalIntegrable (fun t => (Real.cos t : ℂ) * ultrasphPoly lam (k + 1) (z t) * ρ t)
      volume 0 π :=
    gegProd_intble hlam ((Complex.continuous_ofReal.comp Real.continuous_cos).mul (hcj (k + 1)))
  have iC : IntervalIntegrable (fun t => ultrasphPoly lam k (z t) * ρ t) volume 0 π :=
    gegProd_intble hlam (hcj _)
  have e : ∀ t : ℝ, (k + 2 : ℂ) * (ultrasphPoly lam (k + 2) (z t) * ρ t) =
      2 * (k + lam + 1) * a * (ultrasphPoly lam (k + 1) (z t) * ρ t) +
      2 * (k + lam + 1) * v * ((Real.cos t : ℂ) * ultrasphPoly lam (k + 1) (z t) * ρ t) -
      (k + 2 * lam) * (ultrasphPoly lam k (z t) * ρ t) := by
    intro t
    have hr := ultrasphPoly_recurrence hlre k (z t)
    have hzt : z t = a + v * Real.cos t := by simp only [hz]; push_cast; ring
    rw [hzt] at hr ⊢
    push_cast at hr ⊢
    linear_combination ρ t * hr
  rw [← hK]
  simp only [hI]
  rw [← intervalIntegral.integral_const_mul, intervalIntegral.integral_congr (fun t _ => e t),
    intervalIntegral.integral_sub ((iA.const_mul _).add (iB.const_mul _)) (iC.const_mul _),
    intervalIntegral.integral_add (iA.const_mul _) (iB.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]

/-- The normalizing constant `√π Γ(λ)/Γ(λ+1/2)` of the angular weight, at `λ + 1`. -/
private lemma gegProd_const_succ {lam : ℝ} (hlam : 0 < lam) :
    Real.sqrt π * Real.Gamma (lam + 1) / Real.Gamma (lam + 1 + 1 / 2) =
      2 * lam * (Real.sqrt π * Real.Gamma lam / Real.Gamma (lam + 1 / 2)) / (2 * lam + 1) := by
  rw [Real.Gamma_add_one hlam.ne', show lam + 1 + 1 / 2 = (lam + 1 / 2) + 1 by ring,
    Real.Gamma_add_one (by linarith : lam + 1 / 2 ≠ 0)]
  have : Real.Gamma (lam + 1 / 2) ≠ 0 := (Real.Gamma_pos_of_pos (by linarith)).ne'
  field_simp

/-- Unnormalized form of Gegenbauer's product formula, by induction on the degree. -/
private lemma gegProd_main (n : ℕ) : ∀ lam : ℝ, 0 < lam → ∀ θ ψ : ℝ,
    ultrasphPoly lam n 1 * (∫ u : ℝ in (0 : ℝ)..π, ultrasphPoly lam n
      ((Real.cos θ * Real.cos ψ + Real.sin θ * Real.sin ψ * Real.cos u : ℝ)) *
        ((Real.sin u ^ (2 * lam - 1) : ℝ) : ℂ)) =
      ((Real.sqrt π * Real.Gamma lam / Real.Gamma (lam + 1 / 2) : ℝ) : ℂ) *
        ultrasphPoly lam n (Real.cos θ) * ultrasphPoly lam n (Real.cos ψ) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro lam hlam θ ψ
  set a : ℝ := Real.cos θ * Real.cos ψ with ha
  set v : ℝ := Real.sin θ * Real.sin ψ with hv
  have hm := (integral_sin_rpow_aux hlam).2
  have hlre : -1 / 2 < (lam : ℂ).re := by simp; linarith
  -- `∫ cos u ρ = 0`
  have hcos0 : ∫ t : ℝ in (0 : ℝ)..π, (Real.cos t : ℂ) * ((Real.sin t ^ (2 * lam - 1) : ℝ) : ℂ)
      = 0 := by
    have := gegProd_ibp hlam a v (f := fun _ => (1 : ℂ)) (f' := fun _ => 0)
      (fun z => hasDerivAt_const z 1) continuous_const
    simpa using this
  have hI0 : ∫ t : ℝ in (0 : ℝ)..π, ((Real.sin t ^ (2 * lam - 1) : ℝ) : ℂ) =
      ((Real.sqrt π * Real.Gamma lam / Real.Gamma (lam + 1 / 2) : ℝ) : ℂ) := by
    rw [intervalIntegral.integral_ofReal, hm]
  rcases n with _ | _ | k
  · -- degree zero
    simp only [ultrasphPoly_zero, one_mul, mul_one]
    exact hI0
  · -- degree one
    simp only [ultrasphPoly_one_eq hlre]
    have hsplit : ∀ t : ℝ, 2 * (lam : ℂ) * ((a + v * Real.cos t : ℝ) : ℂ) *
        ((Real.sin t ^ (2 * lam - 1) : ℝ) : ℂ) = 2 * lam * a * ((Real.sin t ^ (2 * lam - 1) : ℝ) : ℂ)
        + 2 * lam * v * ((Real.cos t : ℂ) * ((Real.sin t ^ (2 * lam - 1) : ℝ) : ℂ)) := by
      intro t; push_cast; ring
    have i1 : IntervalIntegrable (fun t : ℝ => 2 * (lam : ℂ) * a *
        ((Real.sin t ^ (2 * lam - 1) : ℝ) : ℂ)) volume 0 π := by
      have := (gegProd_intble hlam (h := fun _ => 2 * (lam : ℂ) * a) continuous_const)
      simpa using this
    have i2 : IntervalIntegrable (fun t : ℝ => 2 * (lam : ℂ) * v * ((Real.cos t : ℂ) *
        ((Real.sin t ^ (2 * lam - 1) : ℝ) : ℂ))) volume 0 π :=
      (gegProd_intble hlam (Complex.continuous_ofReal.comp Real.continuous_cos)).const_mul _
    rw [intervalIntegral.integral_congr (fun t _ => hsplit t),
      intervalIntegral.integral_add i1 i2,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hcos0, hI0]
    simp only [ha]
    push_cast
    ring
  · -- degree  from degrees ,  and the raised parameter
    set x : ℂ := (Real.cos θ : ℂ) with hx
    set y : ℂ := (Real.cos ψ : ℂ) with hy
    set mR : ℝ := Real.sqrt π * Real.Gamma lam / Real.Gamma (lam + 1 / 2) with hmR
    set m'R : ℝ := Real.sqrt π * Real.Gamma (lam + 1) / Real.Gamma (lam + 1 + 1 / 2) with hm'R
    set ρ : ℝ → ℂ := fun t => ((Real.sin t ^ (2 * lam - 1) : ℝ) : ℂ) with hρ
    set ρ' : ℝ → ℂ := fun t => ((Real.sin t ^ (2 * (lam + 1) - 1) : ℝ) : ℂ) with hρ'
    set z : ℝ → ℂ := fun t => ((a + v * Real.cos t : ℝ) : ℂ) with hz
    have hzc : Continuous z := by fun_prop
    set I : ℕ → ℂ := fun j => ∫ t : ℝ in (0 : ℝ)..π, ultrasphPoly lam j (z t) * ρ t with hI
    set J : ℂ := ∫ t : ℝ in (0 : ℝ)..π, ultrasphPoly ((lam : ℂ) + 1) k (z t) * ρ' t with hJ
    have ih0 : ultrasphPoly lam k 1 * I k = mR * ultrasphPoly lam k x * ultrasphPoly lam k y :=
      ih k (by omega) lam hlam θ ψ
    have ih1 : ultrasphPoly lam (k + 1) 1 * I (k + 1) =
        mR * ultrasphPoly lam (k + 1) x * ultrasphPoly lam (k + 1) y :=
      ih (k + 1) (by omega) lam hlam θ ψ
    have ihJ : ultrasphPoly ((lam : ℂ) + 1) k 1 * J =
        m'R * ultrasphPoly ((lam : ℂ) + 1) k x * ultrasphPoly ((lam : ℂ) + 1) k y := by
      have := ih k (by omega) (lam + 1) (by linarith) θ ψ
      rw [show ((lam + 1 : ℝ) : ℂ) = (lam : ℂ) + 1 by push_cast; ring] at this
      exact this
    have hstep : (k + 2 : ℂ) * I (k + 2) = 2 * (k + lam + 1) * a * I (k + 1) +
        2 * (k + lam + 1) * v * (v * J) - (k + 2 * lam) * I k :=
      gegProd_step hlam a v k
    -- normalizing constants
    have hlre' : -1 / 2 < ((lam : ℂ) + 1).re := by simp; linarith
    have hl0 : (lam : ℂ) ≠ 0 := by exact_mod_cast hlam.ne'
    have hl1 : (2 * lam + 1 : ℂ) ≠ 0 := by
      have : (2 * lam + 1 : ℝ) ≠ 0 := by positivity
      exact_mod_cast this
    have hlk : (2 * lam + k : ℂ) ≠ 0 := by
      have : (2 * lam + k : ℝ) ≠ 0 := by positivity
      exact_mod_cast this
    have hlk1 : (2 * lam + k + 1 : ℂ) ≠ 0 := by
      have : (2 * lam + k + 1 : ℝ) ≠ 0 := by positivity
      exact_mod_cast this
    have hkl : (k + lam + 1 : ℂ) ≠ 0 := by
      have : (k + lam + 1 : ℝ) ≠ 0 := by positivity
      exact_mod_cast this
    have hk1 : (k + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    have hk2 : (k + 2 : ℂ) ≠ 0 := by exact_mod_cast (show k + 2 ≠ 0 by omega)
    set P : ℂ := poch (2 * (lam : ℂ)) k with hP
    set F : ℂ := (k.factorial : ℂ) with hF
    have hP0 : P ≠ 0 := poch_ne_zero_of_re_pos (by simp; linarith) k
    have hF0 : F ≠ 0 := by simp [hF, Nat.factorial_ne_zero]
    have hv0 : ultrasphPoly lam k 1 = P / F := ultrasphPoly_at_one hlre k
    have hv1 : ultrasphPoly lam (k + 1) 1 = P * (2 * lam + k) / ((k + 1) * F) := by
      rw [ultrasphPoly_at_one hlre, poch_succ, Nat.factorial_succ]; push_cast; ring
    have hv2 : ultrasphPoly lam (k + 2) 1 =
        P * (2 * lam + k) * (2 * lam + k + 1) / ((k + 2) * (k + 1) * F) := by
      rw [ultrasphPoly_at_one hlre, poch_succ, poch_succ, Nat.factorial_succ,
        Nat.factorial_succ]; push_cast; ring
    have hvb : ultrasphPoly ((lam : ℂ) + 1) k 1 =
        P * (2 * lam + k) * (2 * lam + k + 1) / (2 * lam * (2 * lam + 1) * F) := by
      have h1 := poch_add (2 * (lam : ℂ)) 2 k
      rw [show 2 + k = (k + 1) + 1 by omega, poch_succ, poch_succ,
        show (2 : ℕ) = 0 + 1 + 1 from rfl, poch_succ, poch_succ, poch_zero] at h1
      push_cast at h1
      rw [ultrasphPoly_at_one hlre', show 2 * ((lam : ℂ) + 1) = 2 * lam + 2 by ring,
        div_eq_div_iff hF0 (by simp [hl0, hl1, hF0])]
      linear_combination (-F) * h1
    have hmm : ((m'R : ℝ) : ℂ) = 2 * lam * mR / (2 * lam + 1) := by
      rw [show m'R = 2 * lam * mR / (2 * lam + 1) from gegProd_const_succ hlam]; push_cast; ring
    -- the polynomial identities at `x` and `y`
    have recx := ultrasphPoly_recurrence hlre k x
    have recy := ultrasphPoly_recurrence hlre k y
    have sqx := ultrasphPoly_raise_parameter_sq hlre k x
    have sqy := ultrasphPoly_raise_parameter_sq hlre k y
    have hxy : (a : ℂ) = x * y := by simp only [ha, hx, hy]; push_cast; ring
    have hvv : (v : ℂ) ^ 2 = (1 - x ^ 2) * (1 - y ^ 2) := by
      have hr : v ^ 2 = (1 - Real.cos θ ^ 2) * (1 - Real.cos ψ ^ 2) := by
        rw [hv, mul_pow, Real.sin_sq, Real.sin_sq]
      simp only [hx, hy]
      exact_mod_cast hr
    set X0 := ultrasphPoly lam k x
    set X1 := ultrasphPoly lam (k + 1) x
    set X2 := ultrasphPoly lam (k + 2) x
    set Y0 := ultrasphPoly lam k y
    set Y1 := ultrasphPoly lam (k + 1) y
    set Y2 := ultrasphPoly lam (k + 2) y
    set Qx := ultrasphPoly ((lam : ℂ) + 1) k x
    set Qy := ultrasphPoly ((lam : ℂ) + 1) k y
    have hEx : (1 - x ^ 2) * Qx = (-(k + 1) * (2 * (k + lam + 1) * x * X1 - (k + 2 * lam) * X0) +
        (k + 2 * lam) * (k + 2 * lam + 1) * X0) / (4 * lam * (k + lam + 1)) := by
      rw [eq_div_iff (by simp [hl0, hkl])]
      linear_combination sqx - (k + 1) * recx
    have hEy : (1 - y ^ 2) * Qy = (-(k + 1) * (2 * (k + lam + 1) * y * Y1 - (k + 2 * lam) * Y0) +
        (k + 2 * lam) * (k + 2 * lam + 1) * Y0) / (4 * lam * (k + lam + 1)) := by
      rw [eq_div_iff (by simp [hl0, hkl])]
      linear_combination sqy - (k + 1) * recy
    have hX2 : X2 = (2 * (k + lam + 1) * x * X1 - (k + 2 * lam) * X0) / (k + 2) := by
      rw [eq_div_iff hk2]; linear_combination recx
    have hY2 : Y2 = (2 * (k + lam + 1) * y * Y1 - (k + 2 * lam) * Y0) / (k + 2) := by
      rw [eq_div_iff hk2]; linear_combination recy
    have eI0 : I k = mR * X0 * Y0 / (P / F) := by
      rw [eq_div_iff (div_ne_zero hP0 hF0), ← hv0]; linear_combination ih0
    have eI1 : I (k + 1) = mR * X1 * Y1 / (P * (2 * lam + k) / ((k + 1) * F)) := by
      rw [eq_div_iff (by simp [hP0, hF0, hk1, hlk, -one_div]), ← hv1]; linear_combination ih1
    have eJ : J = m'R * Qx * Qy / (P * (2 * lam + k) * (2 * lam + k + 1) /
        (2 * lam * (2 * lam + 1) * F)) := by
      rw [eq_div_iff (by simp [hP0, hF0, hl0, hl1, hlk, hlk1, -one_div]), ← hvb]
      linear_combination ihJ
    have hvJ : (v : ℂ) * ((v : ℂ) * J) = m'R * ((1 - x ^ 2) * Qx) * ((1 - y ^ 2) * Qy) /
        (P * (2 * lam + k) * (2 * lam + k + 1) / (2 * lam * (2 * lam + 1) * F)) := by
      rw [eJ]; linear_combination (m'R * Qx * Qy / (P * (2 * lam + k) * (2 * lam + k + 1) /
        (2 * lam * (2 * lam + 1) * F))) * hvv
    rw [hEx, hEy, hmm] at hvJ
    have eI2 : I (k + 2) = (2 * (k + lam + 1) * a * I (k + 1) +
        2 * (k + lam + 1) * (v * (v * J)) - (k + 2 * lam) * I k) / (k + 2) := by
      rw [eq_div_iff hk2]; linear_combination hstep
    show ultrasphPoly lam (k + 2) 1 * I (k + 2) = mR * X2 * Y2
    rw [eI2, hvJ, eI1, eI0, hxy, hv2, hX2, hY2]
    field_simp
    ring

/-- Identity under the stated parameter and domain assumptions: `ultrasphPoly lam n (Real.cos θ) /
ultrasphPoly lam n 1 * (ultrasphPoly lam n (Real.cos ψ) / ultrasphPoly lam n 1) = Gamma (lam +
1 / 2 : ℂ) / (Real.sqrt Real.pi * Gamma (lam : ℂ)) * ∫ phi : ℝ in (0 : ℝ)..Real.pi,
ultrasphPoly lam n (Real.cos θ * Real.cos ψ + Real.sin θ * Real.sin ψ * Real.cos phi) /
ultrasphPoly lam n 1 * (Real.rpow (Real.sin phi) (2 * lam - 1) : ℂ)`. -/
@[dlmf 18.17.E5]
theorem ultrasphPoly_product_integral {lam : ℝ} (hlam : 0 < lam) (n : ℕ) (θ ψ : ℝ) :
    ultrasphPoly lam n (Real.cos θ) / ultrasphPoly lam n 1 *
      (ultrasphPoly lam n (Real.cos ψ) / ultrasphPoly lam n 1) =
      Gamma (lam + 1 / 2 : ℂ) / (Real.sqrt Real.pi * Gamma (lam : ℂ)) *
      ∫ phi : ℝ in (0 : ℝ)..Real.pi, ultrasphPoly lam n
        (Real.cos θ * Real.cos ψ + Real.sin θ * Real.sin ψ * Real.cos phi) / ultrasphPoly lam n 1 *
          (Real.rpow (Real.sin phi) (2 * lam - 1) : ℂ) := by
  have hmain := gegProd_main n lam hlam θ ψ
  have hlre : -1 / 2 < (lam : ℂ).re := by simp; linarith
  have h1 : ultrasphPoly lam n 1 ≠ 0 := by
    rw [ultrasphPoly_at_one hlre]
    exact div_ne_zero (poch_ne_zero_of_re_pos (by simp; linarith) n)
      (by exact_mod_cast n.factorial_ne_zero)
  have hG1 : 0 < Real.Gamma (lam + 1 / 2) := Real.Gamma_pos_of_pos (by linarith)
  have hG2 : 0 < Real.Gamma lam := Real.Gamma_pos_of_pos hlam
  have hsq : 0 < Real.sqrt π := Real.sqrt_pos.mpr Real.pi_pos
  have hGG : Gamma (lam + 1 / 2 : ℂ) / (Real.sqrt Real.pi * Gamma (lam : ℂ)) =
      ((Real.sqrt π * Real.Gamma lam / Real.Gamma (lam + 1 / 2) : ℝ) : ℂ)⁻¹ := by
    rw [show (lam + 1 / 2 : ℂ) = ((lam + 1 / 2 : ℝ) : ℂ) by push_cast; ring,
      Complex.Gamma_ofReal, Complex.Gamma_ofReal]
    push_cast
    field_simp
  have hint : (∫ phi : ℝ in (0 : ℝ)..Real.pi, ultrasphPoly lam n
        (Real.cos θ * Real.cos ψ + Real.sin θ * Real.sin ψ * Real.cos phi) / ultrasphPoly lam n 1 *
          (Real.rpow (Real.sin phi) (2 * lam - 1) : ℂ)) =
      (ultrasphPoly lam n 1)⁻¹ * ∫ phi : ℝ in (0 : ℝ)..π, ultrasphPoly lam n
        ((Real.cos θ * Real.cos ψ + Real.sin θ * Real.sin ψ * Real.cos phi : ℝ)) *
          ((Real.sin phi ^ (2 * lam - 1) : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [Real.rpow_eq_pow]
    push_cast
    ring
  have hm0 : ((Real.sqrt π * Real.Gamma lam / Real.Gamma (lam + 1 / 2) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (by positivity : Real.sqrt π * Real.Gamma lam / Real.Gamma (lam + 1 / 2) ≠ 0)
  have hI : (∫ phi : ℝ in (0 : ℝ)..π, ultrasphPoly lam n
        ((Real.cos θ * Real.cos ψ + Real.sin θ * Real.sin ψ * Real.cos phi : ℝ)) *
          ((Real.sin phi ^ (2 * lam - 1) : ℝ) : ℂ)) =
      ((Real.sqrt π * Real.Gamma lam / Real.Gamma (lam + 1 / 2) : ℝ) : ℂ) *
        ultrasphPoly lam n (Real.cos θ) * ultrasphPoly lam n (Real.cos ψ) / ultrasphPoly lam n 1 := by
    rw [eq_div_iff h1, mul_comm]; exact hmain
  rw [hGG, hint, hI]
  generalize ((Real.sqrt π * Real.Gamma lam / Real.Gamma (lam + 1 / 2) : ℝ) : ℂ) = M at hm0 ⊢
  field_simp

/-- Identity under the stated parameter and domain assumptions: `(1 - (x : ℂ)) ^ (α + μ : ℂ) *
jacobiPolyP (α + μ) (β - μ) n x / Gamma (α + μ + n + 1 : ℂ) = ∫ y : ℝ in x..1, (1 - (y : ℂ)) ^
(α : ℂ) * jacobiPolyP α β n y / Gamma (α + n + 1 : ℂ) * ((y - x : ℂ) ^ (μ - 1 : ℂ) / Gamma (μ
: ℂ))`. -/
@[dlmf 18.17.E9]
theorem jacobi_fractional_integral {α β μ : ℝ} (hα : -1 < α) (hβ : -1 < β) (hμ : 0 < μ)
    (n : ℕ) {x : ℝ} (hx : x ∈ Set.Ioo (-1) 1) :
    (1 - (x : ℂ)) ^ (α + μ : ℂ) * jacobiPolyP (α + μ) (β - μ) n x / Gamma (α + μ + n + 1 : ℂ) =
      ∫ y : ℝ in x..1, (1 - (y : ℂ)) ^ (α : ℂ) * jacobiPolyP α β n y / Gamma (α + n + 1 : ℂ) *
        ((y - x : ℂ) ^ (μ - 1 : ℂ) / Gamma (μ : ℂ)) := by
  have hnorm (a b : ℝ) (ha : -1 < a) (y : ℂ) :
      jacobiPolyP a b n y / Gamma ((a : ℂ) + n + 1) =
        regularizedGaussHGFun (-(n : ℂ))
          (n + (a : ℂ) + b + 1) ((a : ℂ) + 1) ((1 - y) / 2) / n.factorial := by
    have hp : ∀ k : ℕ, (a : ℂ) + 1 ≠ -(k : ℂ) :=
      not_neg_nat_of_re_pos (by simp; linarith)
    have hG : Gamma ((a : ℂ) + n + 1) = poch ((a : ℂ) + 1) n * Gamma ((a : ℂ) + 1) := by
      rw [show (a : ℂ) + n + 1 = (a : ℂ) + 1 + n by ring]
      exact (div_eq_iff (Gamma_ne_zero hp)).mp
        (Gamma_add_nat_div_Gamma_eq (n := n) ((a : ℂ) + 1) hp)
    rw [jacobiPolyP, DLMF.Hypergeometric.regularizedGaussHGFun_eq_div_Gamma hp, hG]
    field [Gamma_ne_zero hp, poch_ne_zero_of_not_neg_nat hp n]
  let R : ℂ → ℂ := regularizedGaussHGFun (-(n : ℂ))
    (n + (α : ℂ) + β + 1) ((α : ℂ) + 1)
  let f : ℝ → ℂ := fun y => (1 - (y : ℂ)) ^ (α : ℂ) * R ((1 - y) / 2) *
    ((y : ℂ) - x) ^ ((μ : ℂ) - 1)
  let g : ℝ → ℂ := fun t => R (((1 - (x : ℂ)) / 2) * t) *
    (t : ℂ) ^ (α : ℂ) * (1 - (t : ℂ)) ^ ((μ : ℂ) - 1)
  have hxpos : 0 < 1 - x := by linarith [hx.2]
  have hx0 : 1 - (x : ℂ) ≠ 0 := by
    exact_mod_cast hxpos.ne'
  have hscale : (∫ y : ℝ in x..1, f y) =
      (1 - (x : ℂ)) ^ ((α : ℂ) + μ) * ∫ t : ℝ in (0 : ℝ)..1, g t := by
    have hs := intervalIntegral.smul_integral_comp_sub_mul f (1 - x) 1
      (a := (0 : ℝ)) (b := 1)
    simp only [mul_one, sub_sub_cancel, mul_zero, sub_zero, Complex.real_smul,
      ofReal_sub, ofReal_one] at hs
    rw [← hs, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
    intro t ht
    have hxp : (1 - (x : ℂ)) * (1 - (x : ℂ)) ^ (α : ℂ) *
        (1 - (x : ℂ)) ^ ((μ : ℂ) - 1) = (1 - (x : ℂ)) ^ ((α : ℂ) + μ) := by
      calc
        _ = (1 - (x : ℂ)) ^ (1 : ℂ) * (1 - (x : ℂ)) ^ (α : ℂ) *
            (1 - (x : ℂ)) ^ ((μ : ℂ) - 1) := by rw [cpow_one]
        _ = _ := by rw [← cpow_add _ _ hx0, ← cpow_add _ _ hx0]; congr 1; ring
    have hp (s : ℝ) (hs : 0 ≤ s) (a : ℂ) :
        ((1 - (x : ℂ)) * s) ^ a = (1 - (x : ℂ)) ^ a * (s : ℂ) ^ a := by
      simpa only [ofReal_sub, ofReal_one] using mul_cpow_ofReal_nonneg hxpos.le hs a
    dsimp [f, g]
    push_cast
    rw [show 1 - (1 - (1 - (x : ℂ)) * t) = (1 - (x : ℂ)) * t by ring,
      show 1 - (1 - (x : ℂ)) * t - x = (1 - (x : ℂ)) * (1 - t) by ring,
      hp t ht.1.le, show (1 - (t : ℂ)) = ((1 - t : ℝ) : ℂ) by push_cast; rfl,
      hp (1 - t) (by linarith [ht.2])]
    push_cast
    rw [show (1 - (x : ℂ)) * t / 2 = ((1 - (x : ℂ)) / 2) * t by ring]
    linear_combination (t : ℂ) ^ (α : ℂ) * R (((1 - (x : ℂ)) / 2) * t) *
      (1 - (t : ℂ)) ^ ((μ : ℂ) - 1) * hxp
  have hz : ‖(1 - (x : ℂ)) / 2‖ < 1 := by
    rw [show (1 - (x : ℂ)) / 2 = (((1 - x) / 2 : ℝ) : ℂ) by push_cast; rfl,
      norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    linarith [hx.1]
  have hR := DLMF.Hypergeometric.fractional_integral (a := -(n : ℂ))
    (b := n + (α : ℂ) + β + 1) (c := (α : ℂ) + μ + 1) (d := (α : ℂ) + 1)
    (by simp; linarith) (by simp; linarith) hz
  rw [show (α : ℂ) + 1 - 1 = (α : ℂ) by ring,
    show (α : ℂ) + μ + 1 - ((α : ℂ) + 1) = (μ : ℂ) by ring] at hR
  change regularizedGaussHGFun (-(n : ℂ))
    (n + (α : ℂ) + β + 1) ((α : ℂ) + μ + 1) ((1 - x) / 2) =
      1 / Gamma (μ : ℂ) * ∫ t : ℝ in (0 : ℝ)..1, g t at hR
  have hrhs : (∫ y : ℝ in x..1, (1 - (y : ℂ)) ^ (α : ℂ) * jacobiPolyP α β n y /
      Gamma (α + n + 1 : ℂ) * ((y - x : ℂ) ^ (μ - 1 : ℂ) / Gamma (μ : ℂ))) =
      (∫ y : ℝ in x..1, f y) / ((n.factorial : ℂ) * Gamma (μ : ℂ)) := by
    rw [← intervalIntegral.integral_div]
    apply intervalIntegral.integral_congr
    intro y _
    dsimp only
    rw [show (1 - (y : ℂ)) ^ (α : ℂ) * jacobiPolyP α β n y / Gamma (α + n + 1 : ℂ) =
      (1 - (y : ℂ)) ^ (α : ℂ) * (jacobiPolyP α β n y / Gamma (α + n + 1 : ℂ)) by ring,
      hnorm α β hα]
    dsimp [f, R]
    push_cast
    ring
  have hL := hnorm (α + μ) (β - μ) (by linarith) x
  push_cast at hL
  rw [show (n : ℂ) + ((α : ℂ) + μ) + ((β : ℂ) - μ) + 1 = n + (α : ℂ) + β + 1 by ring] at hL
  rw [hrhs, hscale, show (1 - (x : ℂ)) ^ (α + μ : ℂ) * jacobiPolyP (α + μ) (β - μ) n x /
      Gamma (α + μ + n + 1 : ℂ) = (1 - (x : ℂ)) ^ (α + μ : ℂ) *
      (jacobiPolyP (α + μ) (β - μ) n x / Gamma (α + μ + n + 1 : ℂ)) by ring, hL, hR]
  push_cast
  ring

/-- The moments `∫ (1 + x)^m (1 - x)^α (1 + x)^β P_n^{(α,β)}(x) dx`, from the Mellin transform
and the reflection `x ↦ -x`. -/
theorem jacobi_moment {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) (n m : ℕ) :
    ∫ x : ℝ in (-1 : ℝ)..1, ((x : ℂ) + 1) ^ m *
        (jacobiPolyP α β n x * (1 - (x : ℂ)) ^ (α : ℂ) * (1 + (x : ℂ)) ^ (β : ℂ)) =
      (-1 : ℂ) ^ n * ((2 : ℂ) ^ ((α : ℂ) + (β + m + 1)) * Gamma (β + m + 1) *
        Gamma (1 + (α : ℂ) + n) * poch (-(m : ℂ)) n /
        (n.factorial * Gamma (1 + α + (β + m + 1) + n))) := by
  have hz : 0 < ((β : ℂ) + m + 1).re := by
    simp; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have hM := jacobi_mellin_transform hβ hα hz n
  rw [show (1 : ℂ) + β - (β + m + 1) = -(m : ℂ) by ring] at hM
  have hneg := intervalIntegral.integral_comp_neg (a := (-1 : ℝ)) (b := 1)
    (fun x : ℝ => ((x : ℂ) + 1) ^ m *
      (jacobiPolyP α β n x * (1 - (x : ℂ)) ^ (α : ℂ) * (1 + (x : ℂ)) ^ (β : ℂ)))
  norm_num only [neg_neg] at hneg
  rw [← hM, ← hneg, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr_Ioo_of_le (by norm_num) fun t ht => ?_
  have h1 : (1 - (t : ℂ)) ≠ 0 := by
    rw [← ofReal_one, ← ofReal_sub]; exact ofReal_ne_zero.mpr (by linarith [ht.2])
  have hr := jacobi_reflection (α := (α : ℂ)) (β := (β : ℂ)) (by simpa using hα)
    (by simpa using hβ) n (t : ℂ)
  push_cast
  rw [hr, show (β : ℂ) + m + 1 - 1 = β + m by ring, cpow_add _ _ h1, cpow_natCast,
    show -(t : ℂ) + 1 = 1 - t by ring, show (1 : ℂ) - -t = 1 + t by ring]
  rw [show (1 : ℂ) + -t = 1 - t by ring]
  ring

/-- Termwise integration of `e^{-(x+1)z}` against an integrable function on `[-1, 1]`. -/
theorem hasSum_integral_exp_neg_add_one_mul {w : ℝ → ℂ}
    (hw : IntervalIntegrable w volume (-1) 1) (z : ℂ) :
    HasSum (fun m : ℕ => ∫ x : ℝ in (-1 : ℝ)..1, (-z) ^ m / m ! * (((x : ℂ) + 1) ^ m * w x))
      (∫ x : ℝ in (-1 : ℝ)..1, exp (-((x : ℂ) + 1) * z) * w x) := by
  have hwm : AEStronglyMeasurable w (volume.restrict (Set.uIoc (-1 : ℝ) 1)) := by
    rw [Set.uIoc_of_le (show (-1 : ℝ) ≤ 1 by norm_num)]; exact hw.1.aestronglyMeasurable
  refine intervalIntegral.hasSum_integral_of_dominated_convergence
    (fun m x => (2 * ‖z‖) ^ m / m ! * ‖w x‖)
    (fun m => (((by fun_prop : Continuous fun x : ℝ => (-z) ^ m / (m ! : ℂ) *
      ((x : ℂ) + 1) ^ m)).aestronglyMeasurable.mul hwm).congr
      (Eventually.of_forall fun x => by simp only [Pi.mul_apply]; ring))
    (fun m => ?_)
    (Eventually.of_forall fun x _ => (Real.summable_pow_div_factorial (2 * ‖z‖)).mul_right _)
    ?_
    (Eventually.of_forall fun x _ => ?_)
  · refine Eventually.of_forall fun x hx => ?_
    rw [Set.uIoc_of_le (show (-1 : ℝ) ≤ 1 by norm_num)] at hx
    have hx1 : ‖(x : ℂ) + 1‖ ≤ 2 := by
      rw [← ofReal_one, ← ofReal_add, norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by linarith [hx.1])]
      linarith [hx.2]
    rw [norm_mul, norm_mul, norm_div, norm_pow, norm_pow, norm_neg, Complex.norm_natCast,
      mul_pow]
    have hw0 : 0 ≤ ‖w x‖ := norm_nonneg _
    have hp : ‖(x : ℂ) + 1‖ ^ m ≤ 2 ^ m := pow_le_pow_left₀ (norm_nonneg _) hx1 m
    have hf : (0 : ℝ) < m ! := by exact_mod_cast m.factorial_pos
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
    refine div_le_div_of_nonneg_right ?_ hf.le
    calc ‖z‖ ^ m * (‖(x : ℂ) + 1‖ ^ m * ‖w x‖) ≤ ‖z‖ ^ m * (2 ^ m * ‖w x‖) := by gcongr
      _ = 2 ^ m * ‖z‖ ^ m * ‖w x‖ := by ring
  · have h : (fun x => ∑' m : ℕ, (2 * ‖z‖) ^ m / m ! * ‖w x‖) =
        fun x => Real.exp (2 * ‖z‖) * ‖w x‖ := by
      funext x
      rw [tsum_mul_right, Real.exp_eq_exp_ℝ,
        ← (NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) (2 * ‖z‖)).tsum_eq]
    rw [h]
    exact hw.norm.const_mul _
  · have h := (NormedSpace.expSeries_div_hasSum_exp (-((x : ℂ) + 1) * z)).mul_right (w x)
    rw [← Complex.exp_eq_exp_ℂ] at h
    convert h using 1
    funext m
    rw [show -((x : ℂ) + 1) * z = -z * ((x : ℂ) + 1) by ring, mul_pow]
    ring

/-- DLMF 18.17.33 in the form used by the Fourier transforms below. -/
lemma jacobi_laplace_aux {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) (n : ℕ) (z : ℂ) :
    ∫ x : ℝ in (-1 : ℝ)..1, exp (-((x : ℂ) + 1) * z) *
        (jacobiPolyP α β n x * (1 - (x : ℂ)) ^ (α : ℂ) * (1 + (x : ℂ)) ^ (β : ℂ)) =
      (-1 : ℂ) ^ n * (2 : ℂ) ^ ((α : ℂ) + β + n + 1) * Gamma ((α : ℂ) + n + 1) *
      Gamma ((β : ℂ) + n + 1) / (Gamma ((α : ℂ) + β + 2 * n + 2) * n.factorial) *
      z ^ n * kummerM ((β : ℂ) + n + 1) ((α : ℂ) + β + 2 * n + 2) (-2 * z) := by
  set w : ℝ → ℂ := fun x =>
    jacobiPolyP α β n x * (1 - (x : ℂ)) ^ (α : ℂ) * (1 + (x : ℂ)) ^ (β : ℂ) with hwdef
  have hP : Continuous fun x : ℝ => jacobiPolyP α β n (x : ℂ) :=
    ((analyticOnNhd_jacobiPolyP (α : ℂ) β n).continuousOn.comp_continuous
      continuous_ofReal (fun _ => Set.mem_univ _))
  have hw : IntervalIntegrable w volume (-1) 1 := by
    have h := (intervalIntegrable_jacobi_weight_cpow (a := (α : ℂ)) (b := (β : ℂ))
      (by simpa using hα) (by simpa using hβ)).continuousOn_mul hP.continuousOn
    exact h.congr fun x _ => by simp only [hwdef]; ring
  have hS := hasSum_integral_exp_neg_add_one_mul hw z
  set s : ℕ → ℂ := fun m =>
    ∫ x : ℝ in (-1 : ℝ)..1, (-z) ^ m / m ! * (((x : ℂ) + 1) ^ m * w x) with hsdef
  have hs (m : ℕ) : s m = (-z) ^ m / m ! * ((-1 : ℂ) ^ n *
      ((2 : ℂ) ^ ((α : ℂ) + (β + m + 1)) * Gamma (β + m + 1) *
        Gamma (1 + (α : ℂ) + n) * poch (-(m : ℂ)) n /
        (n.factorial * Gamma (1 + α + (β + m + 1) + n)))) := by
    simp only [hsdef, hwdef, intervalIntegral.integral_const_mul]
    rw [jacobi_moment hα hβ n m]
  have hzero : ∑ i ∈ Finset.range n, s i = 0 :=
    Finset.sum_eq_zero fun i hi => by
      rw [hs, poch_neg_nat_eq_zero (Finset.mem_range.mp hi)]; simp
  have hshift := (hasSum_nat_add_iff' n).mpr hS
  rw [hzero, sub_zero] at hshift
  set c : ℂ := (α : ℂ) + β + 2 * n + 2 with hcdef
  have hc0 : 0 < c.re := by
    simp [hcdef]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hcn : ∀ k : ℕ, c ≠ -k := fun k h => by
    have := congrArg re h; simp at this
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k), hc0]
  have hb0 : 0 < ((β : ℂ) + n + 1).re := by
    simp; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hK := ((hasFPowerSeriesOnBall_kummerM (a := (β : ℂ) + n + 1) hcn).hasSum_mul_pow
    (z := -2 * z) (by simp)).mul_left
    ((-1 : ℂ) ^ n * (2 : ℂ) ^ ((α : ℂ) + β + n + 1) * Gamma ((α : ℂ) + n + 1) *
      Gamma ((β : ℂ) + n + 1) / (Gamma c * n.factorial) * z ^ n)
  have hK' : HasSum (fun k => s (k + n))
      ((-1 : ℂ) ^ n * (2 : ℂ) ^ ((α : ℂ) + β + n + 1) * Gamma ((α : ℂ) + n + 1) *
        Gamma ((β : ℂ) + n + 1) / (Gamma c * n.factorial) * z ^ n *
        kummerM ((β : ℂ) + n + 1) c (-2 * z)) := by
    convert hK using 1
    funext k
    rw [hs, DLMF.Gamma.poch_neg_nat_eq (k + n) n]
    simp only [show n ≤ k + n by omega, ↓reduceIte, Nat.add_sub_cancel]
    rw [show (β : ℂ) + ((k + n : ℕ) : ℂ) + 1 = ((β : ℂ) + n + 1) + k by push_cast; ring,
      show (1 : ℂ) + α + (((β : ℂ) + n + 1) + k) + n = c + k by simp only [hcdef]; ring,
      show (α : ℂ) + (((β : ℂ) + n + 1) + k) = ((α : ℂ) + β + n + 1) + k by ring,
      show (1 : ℂ) + α + n = (α : ℂ) + n + 1 by ring,
      Gamma_add_nat_eq_poch_mul_Gamma hb0, Gamma_add_nat_eq_poch_mul_Gamma hc0,
      cpow_add _ _ two_ne_zero, cpow_natCast, pow_add, neg_pow z, neg_pow z, mul_pow,
      neg_pow (2 : ℂ)]
    have h1 : poch ((β : ℂ) + n + 1) k ≠ 0 := poch_ne_zero_of_re_pos hb0 k
    have h2 : poch c k ≠ 0 := poch_ne_zero_of_re_pos hc0 k
    have h3 : Gamma c ≠ 0 := Gamma_ne_zero_of_re_pos hc0
    have h4 : ((k + n).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have h5 : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
    have h6 : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
    have he : ((-1 : ℂ) ^ n) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    simp only [kummerMCoeff]
    field_simp
    rw [he]
    ring
  rw [hshift.unique hK', hcdef]

/-- DLMF 18.17.16, stated here so that the Gegenbauer transforms below can use it. -/
@[dlmf 18.17.E16]
theorem jacobi_fourier_transform {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) (n : ℕ) (y : ℝ) :
    ∫ x : ℝ in (-1 : ℝ)..1, (1 - (x : ℂ)) ^ (α : ℂ) * (1 + (x : ℂ)) ^ (β : ℂ) *
      jacobiPolyP α β n x * exp (I * x * y) =
      (I * y) ^ n * exp (I * y) / n.factorial * (2 : ℂ) ^ (n + α + β + 1 : ℂ) *
        Gamma (n + α + 1 : ℂ) * Gamma (n + β + 1 : ℂ) / Gamma (2 * n + α + β + 2 : ℂ) *
        kummerM (n + α + 1) (2 * n + α + β + 2) (-2 * I * y) := by
  have h := jacobi_laplace_aux hα hβ n (-I * y)
  have hint : ∫ x : ℝ in (-1 : ℝ)..1, (1 - (x : ℂ)) ^ (α : ℂ) * (1 + (x : ℂ)) ^ (β : ℂ) *
      jacobiPolyP α β n x * exp (I * x * y) =
      exp (-(I * y)) * ∫ x : ℝ in (-1 : ℝ)..1, exp (-((x : ℂ) + 1) * (-I * y)) *
        (jacobiPolyP α β n x * (1 - (x : ℂ)) ^ (α : ℂ) * (1 + (x : ℂ)) ^ (β : ℂ)) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun x _ => ?_
    have he : exp (-((x : ℂ) + 1) * (-I * y)) = exp (I * y) * exp (I * x * y) := by
      rw [← Complex.exp_add]; ring_nf
    simp only [he]
    have h1 : exp (-(I * y)) * exp (I * y) = 1 := by rw [← Complex.exp_add]; simp
    linear_combination (-(1 - (x : ℂ)) ^ (α : ℂ) * (1 + (x : ℂ)) ^ (β : ℂ) *
      jacobiPolyP α β n x * exp (I * x * y)) * h1
  set c : ℂ := (α : ℂ) + β + 2 * n + 2 with hcdef
  have hc0 : 0 < c.re := by
    simp [hcdef]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hcn : ∀ k : ℕ, c ≠ -k := fun k h => by
    have := congrArg re h; simp at this
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k), hc0]
  rw [hint, h, kummerM_kummer_transform hcn,
    show c - ((β : ℂ) + n + 1) = n + α + 1 by simp only [hcdef]; ring,
    show -(-2 * (-I * (y : ℂ))) = -2 * I * y by ring,
    show c = 2 * n + α + β + 2 by simp only [hcdef]; ring,
    show (α : ℂ) + β + n + 1 = n + α + β + 1 by ring,
    show (α : ℂ) + n + 1 = n + α + 1 by ring, show (β : ℂ) + n + 1 = n + β + 1 by ring]
  have he : exp (-(I * y)) * exp (-2 * (-I * y)) = exp (I * y) := by
    rw [← Complex.exp_add]; ring_nf
  have hn : (-1 : ℂ) ^ n * (-I * y) ^ n = (I * y) ^ n := by
    rw [← mul_pow]; ring_nf
  linear_combination (exp (-(I * y)) * (2 : ℂ) ^ ((n : ℂ) + α + β + 1) *
    Gamma ((n : ℂ) + α + 1) * Gamma ((n : ℂ) + β + 1) / (Gamma (2 * n + α + β + 2) * n !) *
    kummerM ((n : ℂ) + α + 1) (2 * n + α + β + 2) (-2 * I * y) * exp (-2 * (-I * y))) * hn +
    ((2 : ℂ) ^ ((n : ℂ) + α + β + 1) * Gamma ((n : ℂ) + α + 1) * Gamma ((n : ℂ) + β + 1) /
      (Gamma (2 * n + α + β + 2) * n !) * (I * y) ^ n *
      kummerM ((n : ℂ) + α + 1) (2 * n + α + β + 2) (-2 * I * y)) * he

/-- Identity under the stated parameter and domain assumptions: `∫ x : ℝ in (-1 : ℝ)..1, (1 - (x :
ℂ) ^ 2) ^ (lam - 1 / 2 : ℂ) * ultrasphPoly lam n x * exp (I * x * y) = 2 * Real.pi * I ^ n *
Gamma (n + 2 * (lam : ℂ)) * besselJ (n + (lam : ℂ)) y / (n.factorial * Gamma (lam : ℂ) * (2 *
y : ℂ) ^ (lam : ℂ))`. -/
@[dlmf 18.17.E16_5]
theorem ultrasphPoly_fourier_transform {lam : ℝ} (hlam : 0 < lam) (n : ℕ) {y : ℝ} (hy : 0 < y) :
    ∫ x : ℝ in (-1 : ℝ)..1, (1 - (x : ℂ) ^ 2) ^ (lam - 1 / 2 : ℂ) *
      ultrasphPoly lam n x * exp (I * x * y) =
      2 * Real.pi * I ^ n * Gamma (n + 2 * (lam : ℂ)) * besselJ (n + (lam : ℂ)) y /
        (n.factorial * Gamma (lam : ℂ) * (2 * y : ℂ) ^ (lam : ℂ)) := by
  have ha : -1 < lam - 1 / 2 := by linarith
  have hJ := jacobi_fourier_transform ha ha n y
  have hpoch : poch ((lam : ℂ) + 1 / 2) n ≠ 0 :=
    poch_ne_zero_of_re_pos (by simp; linarith) n
  have hint : ∫ x : ℝ in (-1 : ℝ)..1, (1 - (x : ℂ) ^ 2) ^ (lam - 1 / 2 : ℂ) *
      ultrasphPoly lam n x * exp (I * x * y) =
      poch (2 * (lam : ℂ)) n / poch ((lam : ℂ) + 1 / 2) n *
        ∫ x : ℝ in (-1 : ℝ)..1, (1 - (x : ℂ)) ^ ((lam - 1 / 2 : ℝ) : ℂ) *
          (1 + (x : ℂ)) ^ ((lam - 1 / 2 : ℝ) : ℂ) *
          jacobiPolyP ((lam - 1 / 2 : ℝ) : ℂ) ((lam - 1 / 2 : ℝ) : ℂ) n x * exp (I * x * y) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr_Ioo_of_le (by norm_num) fun x hx => ?_
    have h1 : (1 - (x : ℂ) ^ 2) = ((1 - x : ℝ) : ℂ) * ((1 + x : ℝ) : ℂ) := by push_cast; ring
    rw [h1, mul_cpow_ofReal_nonneg (by linarith [hx.2]) (by linarith [hx.1]),
      ultrasphPoly_eq_jacobiPolyP n _ hpoch]
    push_cast
    ring
  rw [hint, hJ]
  push_cast
  set ν : ℂ := (n : ℂ) + lam with hν
  have hl0 : 0 < ((lam : ℂ) + 1 / 2).re := by simp; linarith
  have hν1 : 0 < (ν + 1).re := by simp [hν]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hνk : ∀ k : ℕ, ν + 1 ≠ -k := fun k h => by
    have := congrArg re h; simp [hν] at this
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k), (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have h2ν : ∀ k : ℕ, 2 * ν + 1 ≠ -k := fun k h => by
    have := congrArg re h; simp [hν] at this
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k), (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  rw [show (n : ℂ) + ((lam : ℂ) - 1 / 2) + 1 = ν + 1 / 2 by simp only [hν]; ring,
    show 2 * (n : ℂ) + ((lam : ℂ) - 1 / 2) + ((lam : ℂ) - 1 / 2) + 2 = 2 * ν + 1 by
      simp only [hν]; ring,
    kummerM_kummer_transform h2ν,
    show 2 * ν + 1 - (ν + 1 / 2) = ν + 1 / 2 by ring, show -(-2 * I * (y : ℂ)) = 2 * I * y by ring,
    besselJ_eq_kummerM hνk h2ν]
  -- Gamma functions
  set T : ℂ := (2 : ℂ) ^ (lam : ℂ) with hT
  set Y : ℂ := (y : ℂ) ^ (lam : ℂ) with hY
  have hT0 : T ≠ 0 := by simp [hT]
  have hY0 : Y ≠ 0 := by
    simp [hY, cpow_eq_zero_iff, ofReal_ne_zero.mpr hy.ne']
  have hsq : ((√π : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr Real.pi_pos)
  have hpi : ((π : ℝ) : ℂ) = ((√π : ℝ) : ℂ) ^ 2 := by
    rw [← ofReal_pow, Real.sq_sqrt Real.pi_pos.le]
  have hnu : ν + 1 / 2 = ((lam : ℂ) + 1 / 2) + n := by simp only [hν]; ring
  have hG1 : Gamma (ν + 1 / 2) = poch ((lam : ℂ) + 1 / 2) n * Gamma ((lam : ℂ) + 1 / 2) := by
    rw [hnu, Gamma_add_nat_eq_poch_mul_Gamma hl0]
  have hl2 : 0 < (2 * (lam : ℂ)).re := by simp; linarith
  have hG2 : Gamma ((n : ℂ) + 2 * lam) = poch (2 * (lam : ℂ)) n * Gamma (2 * (lam : ℂ)) := by
    rw [add_comm, Gamma_add_nat_eq_poch_mul_Gamma hl2]
  have hd1 := Complex.Gamma_mul_Gamma_add_half (lam : ℂ)
  have hd2 := Complex.Gamma_mul_Gamma_add_half (ν + 1 / 2)
  rw [show ν + 1 / 2 + 1 / 2 = ν + 1 by ring, show 2 * (ν + 1 / 2) = 2 * ν + 1 by ring,
    hG1] at hd2
  have hc1 : (2 : ℂ) ^ (1 - 2 * (lam : ℂ)) * T ^ 2 = 2 := by
    rw [hT, sq, ← mul_assoc, ← cpow_add _ _ two_ne_zero, ← cpow_add _ _ two_ne_zero,
      show 1 - 2 * (lam : ℂ) + lam + lam = 1 by ring, cpow_one]
  have hc2 : (2 : ℂ) ^ (1 - (2 * ν + 1)) * ((2 : ℂ) ^ n) ^ 2 * T ^ 2 = 1 := by
    rw [hT, sq, sq, ← cpow_natCast, ← mul_assoc, ← mul_assoc,
      ← cpow_add _ _ two_ne_zero, ← cpow_add _ _ two_ne_zero, ← cpow_add _ _ two_ne_zero,
      ← cpow_add _ _ two_ne_zero, show 1 - (2 * ν + 1) + n + n + lam + lam = 0 by
        simp only [hν]; ring, cpow_zero]
  have hc3 : (2 : ℂ) ^ ((n : ℂ) + ((lam : ℂ) - 1 / 2) + ((lam : ℂ) - 1 / 2) + 1) =
      (2 : ℂ) ^ n * T ^ 2 := by
    rw [hT, sq, ← cpow_natCast, ← cpow_add _ _ two_ne_zero, ← cpow_add _ _ two_ne_zero]
    ring_nf
  have hy2 : ((y : ℂ) / 2) ^ ν = ((y : ℂ) / 2) ^ n * (((y : ℂ) / 2) ^ (lam : ℂ)) := by
    rw [hν, cpow_add _ _ (by simp [hy.ne']), cpow_natCast]
  have hyT : ((y : ℂ) / 2) ^ (lam : ℂ) * T = Y := by
    have h := mul_cpow_ofReal_nonneg (a := y / 2) (b := 2) (by positivity) (by norm_num)
      (lam : ℂ)
    rw [show ((y / 2 : ℝ) : ℂ) * ((2 : ℝ) : ℂ) = (y : ℂ) by push_cast; ring] at h
    rw [hT, hY, h]
    push_cast; ring
  have h2y : (2 * (y : ℂ)) ^ (lam : ℂ) = T * Y := by
    rw [hT, hY, show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,
      mul_cpow_ofReal_nonneg (by norm_num) hy.le]
  have hT2 : T ^ 2 ≠ 0 := pow_ne_zero 2 hT0
  have hA : (2 : ℂ) ^ (1 - 2 * (lam : ℂ)) = 2 / T ^ 2 := eq_div_of_mul_eq hT2 hc1
  have hn2 : ((2 : ℂ) ^ n) ^ 2 * T ^ 2 ≠ 0 := mul_ne_zero (by simp) hT2
  have hB : (2 : ℂ) ^ (1 - (2 * ν + 1)) = 1 / (((2 : ℂ) ^ n) ^ 2 * T ^ 2) :=
    eq_div_of_mul_eq hn2 (by rw [← mul_assoc]; exact hc2)
  have hG3 : Gamma (2 * (lam : ℂ)) =
      Gamma (lam : ℂ) * Gamma ((lam : ℂ) + 1 / 2) * T ^ 2 / (2 * ((√π : ℝ) : ℂ)) := by
    rw [hd1, hA]; field_simp
  have hG5 : Gamma (2 * ν + 1) = poch ((lam : ℂ) + 1 / 2) n * Gamma ((lam : ℂ) + 1 / 2) *
      Gamma (ν + 1) * (((2 : ℂ) ^ n) ^ 2 * T ^ 2) / ((√π : ℝ) : ℂ) := by
    rw [hd2, hB]; field_simp
  have hyT' : ((y : ℂ) / 2) ^ (lam : ℂ) = Y / T := eq_div_of_mul_eq hT0 hyT
  have hE0 : exp (I * y) ≠ 0 := Complex.exp_ne_zero _
  have hE1 : exp (-2 * I * y) = ((exp (I * y)) ^ 2)⁻¹ := by
    rw [← Complex.exp_nat_mul, ← Complex.exp_neg]; ring_nf
  have hE2 : exp (-I * y) = (exp (I * y))⁻¹ := by
    rw [← Complex.exp_neg]; ring_nf
  have hg1 : Gamma (lam : ℂ) ≠ 0 := Gamma_ne_zero_of_re_pos (by simpa using hlam)
  have hg2 : Gamma ((lam : ℂ) + 1 / 2) ≠ 0 := Gamma_ne_zero_of_re_pos hl0
  have hg4 : Gamma (ν + 1) ≠ 0 := Gamma_ne_zero_of_re_pos hν1
  have hfac : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have hy0 : (y : ℂ) ≠ 0 := ofReal_ne_zero.mpr hy.ne'
  rw [hG5, hG2, hG3, hG1, hc3, hy2, h2y, hyT', hE1, hE2, hpi, mul_pow, div_pow]
  set Hp := poch ((lam : ℂ) + 1 / 2) n with hHp
  set Gp := poch (2 * (lam : ℂ)) n with hGp
  field_simp

end DLMF.OrthogonalPolynomials
end
end
