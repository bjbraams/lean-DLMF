/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Hypergeometric.Contiguous
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

/-!
# The hypergeometric equation (AAR §2.3)

Termwise differentiation of the series gives
`d/dz ₂F₁(a,b;c;z) = (ab/c) ₂F₁(a+1,b+1;c+1;z)`. The function then satisfies Euler's
hypergeometric equation

$$
z(1-z)y'' + \bigl(c-(a+b+1)z\bigr)y' - ab\,y = 0.
$$
-/

@[expose] public section

open Complex
open scoped Real Topology

noncomputable section

namespace DLMF.Hypergeometric

/-- The coefficient identity underlying termwise differentiation. No nonvanishing
condition on the numerator parameters is needed. -/
theorem gaussHGCoeff_shift {a b c : ℂ} (hc : ∀ k : ℕ, c ≠ -k) (n : ℕ) :
    (n + 1 : ℂ) * gaussHGCoeff a b c (n + 1) =
      a * b / c * gaussHGCoeff (a + 1) (b + 1) (c + 1) n := by
  have hc0 : c ≠ 0 := by simpa using hc 0
  have hcp : poch (c + 1) n ≠ 0 :=
    poch_ne_zero_of_not_neg_nat (by simpa using not_neg_nat_add_nat hc 1) n
  have hn : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  simp only [gaussHGCoeff, poch_succ_left, Nat.factorial_succ,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  field [hc0, hcp, hn, Nat.cast_ne_zero.mpr n.factorial_ne_zero]

/-- The coefficient recurrence underlying the Gauss differential equation. -/
theorem gaussHGCoeff_recurrence {a b c : ℂ} (hc : ∀ k : ℕ, c ≠ -k) (n : ℕ) :
    (n + 1 : ℂ) * (c + n) * gaussHGCoeff a b c (n + 1) =
      (a + n) * (b + n) * gaussHGCoeff a b c n := by
  have hcp := poch_ne_zero_of_not_neg_nat hc n
  have hcn : c + (n : ℂ) ≠ 0 := by
    simpa only [ne_eq, eq_neg_iff_add_eq_zero] using hc n
  have hn : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  simp only [gaussHGCoeff, poch_succ, Nat.factorial_succ,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  field [hcp, hcn, hn, Nat.cast_ne_zero.mpr n.factorial_ne_zero]

/-- Termwise derivative of the hypergeometric series, for `|z| < 1`. -/
@[dlmf 15.5.E1]
theorem hasDerivAt_ordinaryHypergeometric {a b c z : ℂ}
    (hc : ∀ k : ℕ, c ≠ -k) (hz : ‖z‖ < 1) :
    HasDerivAt (₂F₁ a b c) (a * b / c * ₂F₁ (a + 1) (b + 1) (c + 1) z) z := by
  have hz' := mem_eball_one_of_norm_lt_one hz
  have hf := hasFPowerSeriesOnBall_ordinaryHypergeometric a b c
  have hd := hf.deriv_ofScalars.hasSum_mul_pow hz'
  have hs := ((hasFPowerSeriesOnBall_ordinaryHypergeometric
    (a + 1) (b + 1) (c + 1)).hasSum_mul_pow hz').mul_left (a * b / c)
  have heq : (fun n : ℕ => (n + 1 : ℂ) * gaussHGCoeff a b c (n + 1) * z ^ n) =
      (fun n : ℕ => a * b / c * (gaussHGCoeff (a + 1) (b + 1) (c + 1) n * z ^ n)) := by
    funext n
    rw [gaussHGCoeff_shift hc]
    ring
  rw [heq] at hd
  rw [← hd.unique hs]
  exact (hf.analyticAt_of_mem hz').differentiableAt.hasDerivAt

/-- Identity under the stated parameter and domain assumptions: `deriv (₂F₁ a b c) z = a * b / c *
₂F₁ (a + 1) (b + 1) (c + 1) z`. -/
@[dlmf 15.5.E1]
theorem deriv_ordinaryHypergeometric {a b c z : ℂ}
    (hc : ∀ k : ℕ, c ≠ -k) (hz : ‖z‖ < 1) :
    deriv (₂F₁ a b c) z = a * b / c * ₂F₁ (a + 1) (b + 1) (c + 1) z :=
  (hasDerivAt_ordinaryHypergeometric hc hz).deriv

/-- The Gaussian hypergeometric equation, AAR §2.3. -/
@[dlmf 15.10.E1]
theorem ordinaryHypergeometric_ode {a b c z : ℂ}
    (hc : ∀ k : ℕ, c ≠ -k) (hz : ‖z‖ < 1) (hz0 : z ≠ 0) (hz1 : z ≠ 1) :
    z * (1 - z) * iteratedDeriv 2 (₂F₁ a b c) z +
        (c - (a + b + 1) * z) * deriv (₂F₁ a b c) z -
        a * b * ₂F₁ a b c z = 0 := by
  have h := (hasFPowerSeriesOnBall_ordinaryHypergeometric a b c).ode_of_recurrence
    (A := 1) (B := a + b + 1) (C := a * b) (D := c) (fun n => ?_)
    (mem_eball_one_of_norm_lt_one hz)
  · simpa [iteratedDeriv_succ, iteratedDeriv_zero] using h
  · rw [gaussHGCoeff_recurrence hc]
    ring

/-- Helper lemma for `arcsin_eq_ordinaryHypergeometric`. -/
theorem three_halves_not_neg_nat : ∀ k : ℕ, (3 / 2 : ℂ) ≠ -k := by
  intro k h
  have hre : (3 : ℝ) / 2 = -k := by simpa using congrArg Complex.re h
  have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  linarith

/-- Helper lemma for `arcsin_eq_ordinaryHypergeometric`. -/
theorem one_sub_sq_cpow_neg_half {t : ℝ} (ht : |t| < 1) :
    ((1 : ℂ) - (t : ℂ) ^ 2) ^ (-(1 / 2 : ℂ)) = (1 / Real.sqrt (1 - t ^ 2) : ℝ) := by
  have hnn : 0 < 1 - t ^ 2 := by nlinarith [abs_lt.mp ht]
  have hx : 0 ≤ (1 - t ^ 2 : ℝ) := hnn.le
  have hre : ((1 : ℂ) - (t : ℂ) ^ 2) = (1 - t ^ 2 : ℝ) := by simp [ofReal_pow]
  have hy : (-(1 / 2 : ℂ)) = ((-(1 / 2 : ℝ) : ℝ) : ℂ) := by simp
  rw [hre, hy, ← ofReal_cpow hx]
  have hsqrt : (1 - t ^ 2 : ℝ) ^ (-(1 / 2 : ℝ)) = 1 / Real.sqrt (1 - t ^ 2) := by
    rw [Real.rpow_neg hx, Real.sqrt_eq_rpow]
    field [ne_of_gt (Real.sqrt_pos.2 hnn)]
  rw [hsqrt]

/-- Helper lemma for `arcsin_eq_ordinaryHypergeometric`. -/
theorem half_add_one_eq_three_halves : (1 / 2 : ℂ) + 1 = 3 / 2 := by ring

/-- Helper lemma for `arcsin_eq_ordinaryHypergeometric`. -/
theorem three_halves_add_one_eq_five_halves : (3 / 2 : ℂ) + 1 = 5 / 2 := by ring

/-- Helper lemma for `arcsin_eq_ordinaryHypergeometric`: Gauss's contiguous relation
specialised at `(a,b,c)=(1/2,1/2,3/2)`, together with the binomial series, identifies
the derivative of `t · ₂F₁(1/2,1/2;3/2;t²)`. -/
theorem ordinaryHypergeometric_arcsin_ident {z : ℂ} (hz : ‖z‖ < 1) :
    ₂F₁ (1 / 2 : ℂ) (1 / 2) (3 / 2) z +
        z / 3 * ₂F₁ (3 / 2 : ℂ) (3 / 2) (5 / 2) z =
      (1 - z) ^ (-(1 / 2 : ℂ)) := by
  have hc := three_halves_not_neg_nat
  have hshift := contiguous_shift_b (a := (1 / 2 : ℂ)) (b := (1 / 2 : ℂ))
    (c := (3 / 2 : ℂ)) hc hz
  simp only [half_add_one_eq_three_halves, three_halves_add_one_eq_five_halves] at hshift
  have hbin : ₂F₁ (1 / 2 : ℂ) (3 / 2) (3 / 2) z = (1 - z) ^ (-(1 / 2 : ℂ)) :=
    ordinaryHypergeometric_eq_one_sub_neg_cpow
      (fun k hk => by
        have : (k : ℝ) = -(3 / 2) := by simpa using congrArg Complex.re hk
        have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        linarith) hz
  rw [hbin] at hshift
  have hc0 : (3 / 2 : ℂ) ≠ 0 := by norm_num
  apply mul_left_cancel₀ hc0
  have hcalc :
      (3 / 2 : ℂ) *
            (₂F₁ (1 / 2 : ℂ) (1 / 2) (3 / 2) z +
              z / 3 * ₂F₁ (3 / 2 : ℂ) (3 / 2) (5 / 2) z) -
          (3 / 2) * (1 - z) ^ (-(1 / 2 : ℂ)) =
        (3 / 2) * ₂F₁ (1 / 2 : ℂ) (1 / 2) (3 / 2) z -
          (3 / 2) * (1 - z) ^ (-(1 / 2 : ℂ)) +
          (1 / 2) * z * ₂F₁ (3 / 2 : ℂ) (3 / 2) (5 / 2) z := by
    ring
  have hshift' :
      (3 / 2 : ℂ) * ₂F₁ (1 / 2 : ℂ) (1 / 2) (3 / 2) z -
          (3 / 2) * (1 - z) ^ (-(1 / 2 : ℂ)) +
          (1 / 2) * z * ₂F₁ (3 / 2 : ℂ) (3 / 2) (5 / 2) z = 0 := by
    rw [hshift]
    ring
  exact sub_eq_zero.mp (hcalc.trans hshift')

/-- Helper lemma for `arcsin_eq_ordinaryHypergeometric`. Powers are written as
products to avoid an `npowRec`/`mulAux` unfold barrier in `HasDerivAt.scomp`. -/
theorem hasDerivAt_mul_ordinaryHypergeometric_arcsin {t : ℝ} (ht : |t| < 1) :
    HasDerivAt (fun u : ℝ =>
        (u : ℂ) * ₂F₁ (1 / 2 : ℂ) (1 / 2) (3 / 2) ((u : ℂ) * (u : ℂ)))
      ((1 / Real.sqrt (1 - t ^ 2) : ℝ) : ℂ) t := by
  have ht1 : ‖(t : ℂ)‖ < 1 := by simpa [Real.norm_eq_abs] using ht
  have ht2 : ‖(t : ℂ) * (t : ℂ)‖ < 1 := by
    rw [norm_mul]
    nlinarith [ht1, norm_nonneg (t : ℂ)]
  have hc := three_halves_not_neg_nat
  have hF0 := hasDerivAt_ordinaryHypergeometric (a := (1 / 2 : ℂ)) (b := (1 / 2 : ℂ))
    (c := (3 / 2 : ℂ)) hc ht2
  have hF : HasDerivAt (₂F₁ (1 / 2 : ℂ) (1 / 2) (3 / 2))
      ((1 / 2 : ℂ) * (1 / 2) / (3 / 2) *
        ₂F₁ (3 / 2 : ℂ) (3 / 2) (5 / 2) ((t : ℂ) * (t : ℂ)))
      ((t : ℂ) * (t : ℂ)) := by
    simpa only [half_add_one_eq_three_halves, three_halves_add_one_eq_five_halves] using hF0
  have hpt : (t : ℂ) * (t : ℂ) = (t * t : ℝ) := (ofReal_mul t t).symm
  have hFreal := (hpt ▸ hF).comp_ofReal
  have hsq := (hasDerivAt_id t).mul (hasDerivAt_id t)
  have hFℝ := hFreal.scomp (h := (id : ℝ → ℝ) * id) t hsq
  have hid : HasDerivAt (fun u : ℝ => (u : ℂ)) (1 : ℂ) t :=
    (hasDerivAt_id t).ofReal_comp
  have hprod := hid.mul hFℝ
  have hident := ordinaryHypergeometric_arcsin_ident (z := (t : ℂ) * (t : ℂ)) ht2
  have hsqrt : ((1 : ℂ) - (t : ℂ) * (t : ℂ)) ^ (-(1 / 2 : ℂ)) =
      (1 / Real.sqrt (1 - t ^ 2) : ℝ) := by
    have hz : (t : ℂ) * (t : ℂ) = (t : ℂ) ^ 2 := (pow_two (t : ℂ)).symm
    simpa [hz] using one_sub_sq_cpow_neg_half ht
  have hfun : (fun u : ℝ =>
        (u : ℂ) * ₂F₁ (1 / 2 : ℂ) (1 / 2) (3 / 2) ((u : ℂ) * (u : ℂ))) =
      (fun u : ℝ => (u : ℂ)) *
        ((fun y : ℝ => ₂F₁ (1 / 2 : ℂ) (1 / 2) (3 / 2) (y : ℂ)) ∘
          ((id : ℝ → ℝ) * id)) := by
    funext u
    simp [Pi.mul_apply, Function.comp, ofReal_mul]
  rw [hfun]
  apply hprod.congr_deriv
  have hpt' : ((t * t : ℝ) : ℂ) = (t : ℂ) * (t : ℂ) := ofReal_mul t t
  simp [Function.comp, Pi.mul_apply, real_smul, hpt'] at hident hsqrt ⊢
  convert hident.trans hsqrt using 1
  ring

/-- AAR (2.1.5): `arcsin x = x · ₂F₁(1/2,1/2;3/2;x²)` for real `|x| < 1`.
AAR lists this as an elementary specialisation of the series; the proof differentiates
the hypergeometric side and matches `deriv arcsin`. -/
@[dlmf 15.4.E4]
theorem arcsin_eq_ordinaryHypergeometric {x : ℝ} (hx : |x| < 1) :
    Real.arcsin x = x * (₂F₁ (1 / 2 : ℂ) (1 / 2) (3 / 2) ((x : ℂ) ^ 2)).re := by
  let F : ℝ → ℂ := fun u =>
    (u : ℂ) * ₂F₁ (1 / 2 : ℂ) (1 / 2) (3 / 2) ((u : ℂ) * (u : ℂ))
  let A : ℝ → ℂ := fun u => (Real.arcsin u : ℂ)
  have hF : ∀ u ∈ Set.Ioo (-1 : ℝ) 1, HasDerivAt F
      ((1 / Real.sqrt (1 - u ^ 2) : ℝ) : ℂ) u := fun u hu =>
    hasDerivAt_mul_ordinaryHypergeometric_arcsin (abs_lt.mpr hu)
  have hA : ∀ u ∈ Set.Ioo (-1 : ℝ) 1, HasDerivAt A
      ((1 / Real.sqrt (1 - u ^ 2) : ℝ) : ℂ) u := by
    intro u hu
    have hu' : |u| < 1 := abs_lt.mpr hu
    exact (Real.hasDerivAt_arcsin (by intro h; rw [h] at hu'; simp at hu')
      (by intro h; rw [h] at hu'; simp at hu')).ofReal_comp
  have h0 : (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 := by constructor <;> norm_num
  have heq :=
    (isOpen_Ioo (a := (-1 : ℝ)) (b := 1)).eqOn_of_deriv_eq
      isPreconnected_Ioo
      (fun u hu => (hF u hu).differentiableAt.differentiableWithinAt)
      (fun u hu => (hA u hu).differentiableAt.differentiableWithinAt)
      (fun u hu => ((hF u hu).deriv).trans ((hA u hu).deriv).symm)
      h0 (by simp [F, A, Real.arcsin_zero, ordinaryHypergeometric_zero])
  have hxI : x ∈ Set.Ioo (-1 : ℝ) 1 := abs_lt.mp hx
  have hFx : F x = A x := heq hxI
  have hre := congrArg Complex.re hFx
  have hpow : ((x : ℂ) * (x : ℂ)) = (x : ℂ) ^ 2 := (pow_two (x : ℂ)).symm
  simp [F, A, mul_re, ofReal_re, ofReal_im, hpow] at hre
  linarith

end DLMF.Hypergeometric
