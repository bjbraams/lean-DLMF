/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Hypergeometric.Series

/-!
# Contiguous relations (AAR §2.5 and §3.7)

Gauss listed fifteen relations among `₂F₁(a,b;c;z)` and the six functions obtained by
shifting one parameter by `±1`. A representative identity is recorded below; the remaining
fourteen are the same linear-algebraic consequence of the three-term recurrence for Pochhammer
symbols.
-/

@[expose] public section

open Complex

noncomputable section

namespace DLMF.Hypergeometric

/-- Helper lemma for contiguous relations: `a (a+1)_n = (a+n) (a)_n`. -/
theorem poch_succ_left_mul (a : ℂ) (n : ℕ) : a * poch (a + 1) n = (a + n) * poch a n := by
  rw [← poch_succ_left, poch_succ, mul_comm]

/-- Helper lemma for `contiguous_shift_b`. -/
theorem poch_sub_succ (b : ℂ) (n : ℕ) :
    poch b (n + 1) - poch (b + 1) (n + 1) = -(n + 1 : ℂ) * poch (b + 1) n := by
  rw [poch_succ_left, poch_succ]
  ring

/-- Helper lemma for `contiguous_shift_b`. The identity is false at `c = 0` without this
regularity hypothesis: both left-hand hypergeometric series collapse to `1` in Lean's
totalization, while the right-hand side need not vanish. -/
theorem gaussHGCoeff_contiguous_shift_b {a b c : ℂ} (hc : ∀ k : ℕ, c ≠ -k) (n : ℕ) :
    c * gaussHGCoeff a b c (n + 1) - c * gaussHGCoeff a (b + 1) c (n + 1) =
      -a * gaussHGCoeff (a + 1) (b + 1) (c + 1) n := by
  have hc0 : c ≠ 0 := by simpa using hc 0
  have hcp1 := poch_ne_zero_of_not_neg_nat (not_neg_nat_add_nat hc 1) n
  have hn : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hf0 : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have hdiff := poch_sub_succ b n
  have hfac : ((n + 1).factorial : ℂ) = (n + 1) * n.factorial := by
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, mul_comm]
  simp only [gaussHGCoeff, poch_succ_left a n, poch_succ_left c n, hfac]
  field_simp [hc0, hcp1, hn, hf0]
  rw [hdiff]
  ring

/-- One of Gauss's contiguous relations, under the standing AAR convention that the
denominator parameter is not a nonpositive integer. Without that hypothesis the identity
fails at `c = 0`. -/
@[dlmf 15.5.E16_5]
theorem contiguous_shift_b {a b c z : ℂ} (hc : ∀ k : ℕ, c ≠ -k) (hz : ‖z‖ < 1) :
    c * ₂F₁ a b c z - c * ₂F₁ a (b + 1) c z =
      -(a * z) * ₂F₁ (a + 1) (b + 1) (c + 1) z := by
  have hz' := mem_eball_one_of_norm_lt_one hz
  have hs1 := (hasFPowerSeriesOnBall_ordinaryHypergeometric a b c).hasSum_mul_pow hz'
  have hs2 := (hasFPowerSeriesOnBall_ordinaryHypergeometric a (b + 1) c).hasSum_mul_pow hz'
  have hs3 :=
    (hasFPowerSeriesOnBall_ordinaryHypergeometric (a + 1) (b + 1) (c + 1)).hasSum_mul_pow hz'
  have hL := (hs1.mul_left c).sub (hs2.mul_left c)
  have hR0 := hs3.mul_left (-a)
  let d : ℕ → ℂ := fun n =>
    match n with
    | 0 => 0
    | n + 1 => -a * gaussHGCoeff (a + 1) (b + 1) (c + 1) n
  have hd_succ : ∀ n, d (n + 1) = -a * gaussHGCoeff (a + 1) (b + 1) (c + 1) n := fun n => rfl
  have hds : HasSum (fun n => d (n + 1) * z ^ n)
      (-a * ₂F₁ (a + 1) (b + 1) (c + 1) z) := by
    have hfun : (fun n => d (n + 1) * z ^ n) =
        fun n => -a * (gaussHGCoeff (a + 1) (b + 1) (c + 1) n * z ^ n) := by
      funext n
      rw [hd_succ]
      ring
    rwa [hfun]
  have hR := HasSum.mul_pow_shift hds rfl
  have hfunL : (fun n : ℕ =>
      c * (gaussHGCoeff a b c n * z ^ n) - c * (gaussHGCoeff a (b + 1) c n * z ^ n)) =
      fun n => d n * z ^ n := by
    funext n
    cases n with
    | zero => simp [d, gaussHGCoeff, poch_zero]
    | succ n =>
      simp only [d]
      have hcoeff := gaussHGCoeff_contiguous_shift_b (a := a) (b := b) (c := c) hc n
      linear_combination hcoeff * z ^ (n + 1)
  have hL' : HasSum (fun n => d n * z ^ n)
      (c * ₂F₁ a b c z - c * ₂F₁ a (b + 1) c z) := by
    rwa [← hfunL]
  have hval : z * (-a * ₂F₁ (a + 1) (b + 1) (c + 1) z) =
      -(a * z) * ₂F₁ (a + 1) (b + 1) (c + 1) z := by ring
  exact hL'.unique (hval ▸ hR)

/-- Helper lemma for AAR (2.5.5): the coefficient identity
`n (a)_n = a ((a+1)_n - (a)_n)`. -/
theorem gaussHGCoeff_AAR_2_5_5 {a b c : ℂ} (hc : ∀ k : ℕ, c ≠ -k) (n : ℕ) :
    (n : ℂ) * gaussHGCoeff a b c n =
      a * (gaussHGCoeff (a + 1) b c n - gaussHGCoeff a b c n) := by
  cases n with
  | zero => simp [gaussHGCoeff, poch_zero]
  | succ n =>
    have hcp := poch_ne_zero_of_not_neg_nat hc (n + 1)
    have hf : ((n + 1).factorial : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (n + 1).factorial_ne_zero
    have hn : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    simp only [gaussHGCoeff, poch_succ_left a n, poch_succ (a + 1) n]
    field_simp [hcp, hf, hn]
    push_cast
    ring

/-- AAR (2.5.5): `z · ∂F/∂z = a (F(a+) - F)`. -/
theorem ordinaryHypergeometric_mul_deriv_eq_shift_a {a b c z : ℂ}
    (hc : ∀ k : ℕ, c ≠ -k) (hz : ‖z‖ < 1) :
    z * deriv (₂F₁ a b c) z = a * (₂F₁ (a + 1) b c z - ₂F₁ a b c z) := by
  have hz' := mem_eball_one_of_norm_lt_one hz
  have hf := hasFPowerSeriesOnBall_ordinaryHypergeometric a b c
  have hL := hf.hasSum_z_mul_deriv hz'
  have hs1 := (hasFPowerSeriesOnBall_ordinaryHypergeometric (a + 1) b c).hasSum_mul_pow hz'
  have hs0 := hf.hasSum_mul_pow hz'
  have hR := (hs1.sub hs0).mul_left a
  have hfun : (fun n : ℕ => (n : ℂ) * gaussHGCoeff a b c n * z ^ n) =
      fun n => a * (gaussHGCoeff (a + 1) b c n * z ^ n - gaussHGCoeff a b c n * z ^ n) := by
    funext n
    have hcoeff := gaussHGCoeff_AAR_2_5_5 (a := a) (b := b) (c := c) hc n
    linear_combination hcoeff * z ^ n
  have hL' : HasSum (fun n =>
      a * (gaussHGCoeff (a + 1) b c n * z ^ n - gaussHGCoeff a b c n * z ^ n))
      (z * deriv (₂F₁ a b c) z) := by
    rwa [hfun] at hL
  have hR' : HasSum (fun n =>
      a * (gaussHGCoeff (a + 1) b c n * z ^ n - gaussHGCoeff a b c n * z ^ n))
      (a * (₂F₁ (a + 1) b c z - ₂F₁ a b c z)) := by
    simpa [mul_sub] using hR
  exact hL'.unique hR'

/-- Helper lemma for AAR (2.5.8). -/
theorem gaussHGCoeff_AAR_2_5_8 {a b c : ℂ} (hc : ∀ k : ℕ, c ≠ -k) (n : ℕ) :
    (n + 1 : ℂ) * gaussHGCoeff a b c (n + 1) - (n : ℂ) * gaussHGCoeff a b c n -
      (c - a) * gaussHGCoeff (a - 1) b c (n + 1) -
      (a - c) * gaussHGCoeff a b c (n + 1) -
      b * gaussHGCoeff a b c n = 0 := by
  have hcp := poch_ne_zero_of_not_neg_nat hc n
  have hcp1 := poch_ne_zero_of_not_neg_nat hc (n + 1)
  have hf0 : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have hn : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hcn : c + (n : ℂ) ≠ 0 := by
    simpa only [ne_eq, eq_neg_iff_add_eq_zero] using hc n
  have ha : poch a (n + 1) = poch a n * (a + n) := poch_succ a n
  have ha1 : poch (a - 1) (n + 1) = (a - 1) * poch a n := by
    simpa [sub_add_cancel] using poch_succ_left (a - 1) n
  have hb : poch b (n + 1) = poch b n * (b + n) := poch_succ b n
  have hc' : poch c (n + 1) = poch c n * (c + n) := poch_succ c n
  have hfac : ((n + 1).factorial : ℂ) = (n + 1) * n.factorial := by
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, mul_comm]
  have hnum :
      (n + 1 : ℂ) * (a + n) * (b + n) - (n : ℂ) * (c + n) * (n + 1) -
        (c - a) * (a - 1) * (b + n) - (a - c) * (a + n) * (b + n) -
        b * (c + n) * (n + 1) = 0 := by
    ring
  have hden : poch c n * (n.factorial : ℂ) * (n + 1) * (c + n) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero hcp hf0) hn) hcn
  simp only [gaussHGCoeff]
  rw [ha, ha1, hb, hc', hfac]
  apply mul_left_cancel₀ hden
  rw [mul_zero]
  field_simp [hcp, hf0, hn, hcn]
  linear_combination poch a n * poch b n * hnum

/-- AAR (2.5.8): `z(1-z) F' = (c-a) F(a-) + (a-c+bz) F`. -/
@[dlmf 15.5.E20]
theorem ordinaryHypergeometric_mul_one_sub_mul_deriv_eq {a b c z : ℂ}
    (hc : ∀ k : ℕ, c ≠ -k) (hz : ‖z‖ < 1) :
    z * (1 - z) * deriv (₂F₁ a b c) z =
      (c - a) * ₂F₁ (a - 1) b c z + (a - c + b * z) * ₂F₁ a b c z := by
  have hz' := mem_eball_one_of_norm_lt_one hz
  have hf := hasFPowerSeriesOnBall_ordinaryHypergeometric a b c
  have hFz := hf.hasSum_z_mul_deriv hz'
  have hF := hf.hasSum_mul_pow hz'
  have hFm := (hasFPowerSeriesOnBall_ordinaryHypergeometric (a - 1) b c).hasSum_mul_pow hz'
  let d : ℕ → ℂ := fun n =>
    match n with
    | 0 => 0
    | n + 1 => (n : ℂ) * gaussHGCoeff a b c n
  have hd0 : d 0 = 0 := rfl
  have hds : HasSum (fun n : ℕ => d (n + 1) * z ^ n) (z * deriv (₂F₁ a b c) z) := by
    have hfun : (fun n : ℕ => d (n + 1) * z ^ n) =
        fun n : ℕ => (n : ℂ) * gaussHGCoeff a b c n * z ^ n := by
      funext n
      simp [d]
    rwa [hfun]
  have hzz := HasSum.mul_pow_shift (c := d) (s := z * deriv (₂F₁ a b c) z) hds hd0
  have hBz : HasSum (fun n =>
      (match n with
        | 0 => (0 : ℂ)
        | n + 1 => b * gaussHGCoeff a b c n) * z ^ n)
      (z * (b * ₂F₁ a b c z)) :=
    HasSum.mul_pow_shift
      (c := fun n => match n with | 0 => 0 | n + 1 => b * gaussHGCoeff a b c n)
      (s := b * ₂F₁ a b c z)
      (by
        have hfun : (fun n : ℕ =>
            (match (n + 1) with
              | 0 => (0 : ℂ)
              | k + 1 => b * gaussHGCoeff a b c k) * z ^ n) =
            fun n : ℕ => b * (gaussHGCoeff a b c n * z ^ n) := by
          funext n
          simp
          ring
        rw [hfun]
        exact hF.mul_left b) rfl
  have hleft := hFz.sub hzz
  have hright := ((hFm.mul_left (c - a)).add (hF.mul_left (a - c))).add hBz
  have hcomb := hleft.sub hright
  have hfun : (fun n : ℕ =>
      (n : ℂ) * gaussHGCoeff a b c n * z ^ n - d n * z ^ n -
        ((c - a) * (gaussHGCoeff (a - 1) b c n * z ^ n) +
          (a - c) * (gaussHGCoeff a b c n * z ^ n) +
          (match n with
            | 0 => (0 : ℂ)
            | n + 1 => b * gaussHGCoeff a b c n) * z ^ n)) =
      fun _ => 0 := by
    funext n
    cases n with
    | zero => simp [d, gaussHGCoeff, poch_zero]
    | succ n =>
      have hcoeff := gaussHGCoeff_AAR_2_5_8 (a := a) (b := b) (c := c) hc n
      simp [d]
      have hzpow := congrArg (fun t : ℂ => t * z ^ (n + 1)) hcoeff
      convert hzpow using 1
      · ring
      · simp
  have hsum' : HasSum (fun _ : ℕ => (0 : ℂ))
      (z * deriv (₂F₁ a b c) z - z * (z * deriv (₂F₁ a b c) z) -
        ((c - a) * ₂F₁ (a - 1) b c z + (a - c) * ₂F₁ a b c z +
          z * (b * ₂F₁ a b c z))) := by
    rwa [hfun] at hcomb
  have hval := hsum'.tsum_eq
  rw [tsum_zero] at hval
  have hrewrite : z * (1 - z) * deriv (₂F₁ a b c) z =
      z * deriv (₂F₁ a b c) z - z * (z * deriv (₂F₁ a b c) z) := by ring
  have hrewrite' : (c - a) * ₂F₁ (a - 1) b c z + (a - c + b * z) * ₂F₁ a b c z =
      (c - a) * ₂F₁ (a - 1) b c z + (a - c) * ₂F₁ a b c z +
        z * (b * ₂F₁ a b c z) := by ring
  rw [hrewrite, hrewrite']
  exact sub_eq_zero.mp hval.symm

/-- Gauss's three-term contiguous relation in the `a`-parameter (DLMF 15.5.11),
obtained as in AAR §2.5 by equating (2.5.5) and (2.5.8). The denominator parameter
is required not to be a nonpositive integer. -/
@[dlmf 15.5.E11]
theorem contiguous_a {a b c z : ℂ} (hc : ∀ k : ℕ, c ≠ -k) (hz : ‖z‖ < 1) :
    (c - a) * ₂F₁ (a - 1) b c z + (2 * a - c + (b - a) * z) * ₂F₁ a b c z +
      a * (z - 1) * ₂F₁ (a + 1) b c z = 0 := by
  have h5 := ordinaryHypergeometric_mul_deriv_eq_shift_a (a := a) (b := b) (c := c) hc hz
  have h8 :=
    ordinaryHypergeometric_mul_one_sub_mul_deriv_eq (a := a) (b := b) (c := c) hc hz
  have hmul : (1 - z) * (z * deriv (₂F₁ a b c) z) =
      z * (1 - z) * deriv (₂F₁ a b c) z := by ring
  have heq : (1 - z) * a * (₂F₁ (a + 1) b c z - ₂F₁ a b c z) =
      (c - a) * ₂F₁ (a - 1) b c z + (a - c + b * z) * ₂F₁ a b c z := by
    calc
      _ = (1 - z) * (z * deriv (₂F₁ a b c) z) := by rw [h5]; ring
      _ = z * (1 - z) * deriv (₂F₁ a b c) z := hmul
      _ = _ := h8
  have hrearr :
      (c - a) * ₂F₁ (a - 1) b c z + (2 * a - c + (b - a) * z) * ₂F₁ a b c z +
          a * (z - 1) * ₂F₁ (a + 1) b c z =
        (c - a) * ₂F₁ (a - 1) b c z + (a - c + b * z) * ₂F₁ a b c z -
          (1 - z) * a * (₂F₁ (a + 1) b c z - ₂F₁ a b c z) := by
    ring
  rw [hrearr, heq]
  ring

/-- Helper lemma for `contiguous_c`. -/
theorem gaussHGCoeff_contiguous_c {a b c : ℂ} (hc : ∀ k : ℕ, c ≠ -k) (n : ℕ) :
    c * gaussHGCoeff a b c n - (c - a) * gaussHGCoeff a b (c + 1) n -
      a * gaussHGCoeff (a + 1) b (c + 1) n = 0 := by
  have hcp := poch_ne_zero_of_not_neg_nat hc n
  have hcp1 : poch (c + 1) n ≠ 0 := by
    simpa using poch_ne_zero_of_not_neg_nat (not_neg_nat_add_nat hc 1) n
  have hfact : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have hA := poch_succ_left_mul a n
  have hC := poch_succ_left_mul c n
  have hnum :
      c * poch a n * poch (c + 1) n - (c - a) * poch a n * poch c n -
        a * poch (a + 1) n * poch c n = 0 := by
    rw [show c * poch a n * poch (c + 1) n = poch a n * (c * poch (c + 1) n) by ring, hC]
    rw [show a * poch (a + 1) n * poch c n = poch c n * (a * poch (a + 1) n) by ring, hA]
    ring
  have hden : poch c n * poch (c + 1) n * (n.factorial : ℂ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hcp hcp1) hfact
  simp only [gaussHGCoeff]
  apply mul_left_cancel₀ hden
  rw [mul_zero]
  field_simp [hcp, hcp1, hfact]
  linear_combination poch b n * hnum

/-- Contiguous relation shifting the denominator parameter. The previous combination
`(c-a-b) F(a,b;c) + a F(a+1,b;c+1) + b F(a,b+1;c+1) - c F(a,b;c+1)` is false already
at degree one (the residual is proportional to `3c-a-b`). The identity below is the
standard Gauss relation among `F(c)`, `F(c+1)` and `F(a+1,c+1)`, and requires the
standing restriction that `c` is not a nonpositive integer. -/
theorem contiguous_c {a b c z : ℂ} (hc : ∀ k : ℕ, c ≠ -k) (hz : ‖z‖ < 1) :
    c * ₂F₁ a b c z - (c - a) * ₂F₁ a b (c + 1) z -
      a * ₂F₁ (a + 1) b (c + 1) z = 0 := by
  have hz' := mem_eball_one_of_norm_lt_one hz
  have hs0 := (hasFPowerSeriesOnBall_ordinaryHypergeometric a b c).hasSum_mul_pow hz'
  have hs1 := (hasFPowerSeriesOnBall_ordinaryHypergeometric a b (c + 1)).hasSum_mul_pow hz'
  have hs2 :=
    (hasFPowerSeriesOnBall_ordinaryHypergeometric (a + 1) b (c + 1)).hasSum_mul_pow hz'
  have hsum := (hs0.mul_left c).sub ((hs1.mul_left (c - a)).add (hs2.mul_left a))
  have hfun : (fun n : ℕ =>
      c * (gaussHGCoeff a b c n * z ^ n) -
        ((c - a) * (gaussHGCoeff a b (c + 1) n * z ^ n) +
          a * (gaussHGCoeff (a + 1) b (c + 1) n * z ^ n))) =
      fun _ => 0 := by
    funext n
    have hcoeff := gaussHGCoeff_contiguous_c (a := a) (b := b) (c := c) hc n
    linear_combination hcoeff * z ^ n
  have hsum' : HasSum (fun _ : ℕ => (0 : ℂ))
      (c * ₂F₁ a b c z - ((c - a) * ₂F₁ a b (c + 1) z + a * ₂F₁ (a + 1) b (c + 1) z)) := by
    rwa [hfun] at hsum
  have hval := hsum'.tsum_eq
  rw [tsum_zero] at hval
  rw [eq_comm] at hval
  convert hval using 1
  ring

end DLMF.Hypergeometric
