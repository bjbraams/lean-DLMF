/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.OrthogonalPolynomials.Series.ClassicalGenerating

/-!
# Parameter series and convergence for Jacobi polynomials

Monomial expansions and analytic convergence arguments give the Jacobi parameter generating
functions.

Source references and common attribution are retained in
`DLMF.OrthogonalPolynomials.Series`.
-/

@[expose] public section

open Complex Polynomial MeasureTheory Filter

open scoped Real Nat Topology

open DLMF.Hypergeometric

open DLMF.Confluent

open DLMF.Bessel

noncomputable section

set_option autoImplicit false

namespace DLMF.OrthogonalPolynomials

/-- Formula under the stated hypotheses: `(2 * x) ^ n = n.factorial * ∑ k ∈ Finset.range (n / 2 +
1), (lam + n - 2 * k) / lam / (poch (lam + 1) (n - k) * k.factorial) * ultrasphPoly lam (n - 2
* k) x`. -/
@[dlmf 18.18.E17]
theorem monomial_ultrasphPoly_expansion {lam : ℂ} (hlam : 0 < lam.re) (n : ℕ) (x : ℂ) :
    (2 * x) ^ n = n.factorial * ∑ k ∈ Finset.range (n / 2 + 1),
      (lam + n - 2 * k) / lam / (poch (lam + 1) (n - k) * k.factorial)
          * ultrasphPoly lam (n - 2 * k) x := by
  have hl : lam ≠ 0 := by intro he; simp [he] at hlam
  have hp (r : ℕ) : poch lam r ≠ 0 := poch_ne_zero_of_re_pos hlam r
  have hp1 (r : ℕ) : poch (lam + 1) r ≠ 0 := poch_ne_zero_of_re_pos (by simp; linarith) r
  have hf (r : ℕ) : (r.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr r.factorial_ne_zero
  let F : ℕ → ℕ → ℂ := fun k j =>
    (lam + n - 2 * k) / lam / (poch (lam + 1) (n - k) * k.factorial) *
      ((-1 : ℂ) ^ j * poch lam (n - 2 * k - j) /
        ((j.factorial : ℂ) * (n - 2 * k - 2 * j).factorial) * (2 * x) ^ (n - 2 * k - 2 * j))
  have hexpand : (∑ k ∈ Finset.range (n / 2 + 1),
      (lam + n - 2 * k) / lam / (poch (lam + 1) (n - k) * k.factorial) *
        ultrasphPoly lam (n - 2 * k) x) =
      ∑ k ∈ Finset.range (n / 2 + 1), ∑ j ∈ Finset.range (n / 2 - k + 1), F k j := by
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : 2 * k ≤ n := by have := Finset.mem_range.mp hk; omega
    rw [ultrasphPoly_finite_sum (by linarith : -1 / 2 < lam.re), Finset.mul_sum,
      show (n - 2 * k) / 2 = n / 2 - k by omega]
  have hterm {r k : ℕ} (hr : 2 * r ≤ n) (hk : k ≤ r) :
      F (r - k) k = (2 * x) ^ (n - 2 * r) / ((r.factorial : ℂ) * (n - 2 * r).factorial) *
        ((-1 : ℂ) ^ k * (r.choose k : ℂ) * ((lam + (n - 2 * r : ℕ)) + 2 * k) /
          poch ((lam + (n - 2 * r : ℕ)) + k) (r + 1)) := by
    have hidx1 : n - (r - k) = n - r + k := by omega
    have hidx2 : n - 2 * (r - k) - k = n - 2 * r + k := by omega
    have hidx3 : n - 2 * (r - k) - 2 * k = n - 2 * r := by omega
    have hcast : lam + n - 2 * ((r - k : ℕ) : ℂ) = lam + ((n - 2 * r : ℕ) : ℂ) + 2 * k := by
      rw [Nat.cast_sub hk, Nat.cast_sub hr, Nat.cast_mul, Nat.cast_ofNat]
      ring
    have hrel : poch (lam + 1) (n - r + k) =
        poch lam (n - 2 * r + k) * poch (lam + (n - 2 * r : ℕ) + k) (r + 1) / lam := by
      rw [eq_div_iff hl]
      have he := poch_add lam (n - 2 * r + k) (r + 1)
      rw [show n - 2 * r + k + (r + 1) = (n - r + k) + 1 by omega,
        poch_succ_left] at he
      push_cast at he
      simp only [← add_assoc] at he
      linear_combination he
    have hpa : poch (lam + (n - 2 * r : ℕ) + k) (r + 1) ≠ 0 :=
      poch_ne_zero_of_re_pos (by simp only [add_re, natCast_re]; positivity) _
    dsimp only [F]
    rw [hidx1, hidx2, hidx3, hcast, hrel, Nat.cast_choose ℂ hk]
    field_simp [hl, hp, hpa, hf]
  have hs (r : ℕ) (hr : r ∈ Finset.range (n / 2 + 1)) :
      (∑ k ∈ Finset.range (r + 1), F k (r - k)) =
        if r = 0 then (2 * x) ^ n / n.factorial else 0 := by
    have hrn : 2 * r ≤ n := by have := Finset.mem_range.mp hr; omega
    have ha : 0 < (lam + (n - 2 * r : ℕ)).re := by
      simp only [add_re, natCast_re]
      linarith [Nat.cast_nonneg (α := ℝ) (n - 2 * r)]
    conv_lhs => rw [← Finset.sum_range_reflect]
    have hh : (∑ k ∈ Finset.range (r + 1), F (r + 1 - 1 - k) (r - (r + 1 - 1 - k))) =
        (2 * x) ^ (n - 2 * r) / ((r.factorial : ℂ) * (n - 2 * r).factorial) *
          ∑ k ∈ Finset.range (r + 1), (-1 : ℂ) ^ k * (r.choose k : ℂ) *
            ((lam + (n - 2 * r : ℕ)) + 2 * k) / poch ((lam + (n - 2 * r : ℕ)) + k) (r + 1) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      have hkr : k ≤ r := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      rw [show r + 1 - 1 - k = r - k by omega, Nat.sub_sub_self hkr]
      exact hterm hrn hkr
    rw [hh, sum_choose_weighted_recip_poch_eq ha]
    split_ifs with he
    · subst r; simp
    · simp
  rw [hexpand, sum_triangle_by_total_degree, Finset.sum_congr rfl hs,
    Finset.sum_eq_single 0]
  · simp only [ite_true]
    field_simp [hf]
  · intro r hr hr0
    simp [hr0]
  · simp

/-- Formula under the stated hypotheses: `ultrasphPoly μ n x = ∑ k ∈ Finset.range (n / 2 + 1),
(lam + n - 2 * k) / lam * poch μ (n - k) / poch (lam + 1) (n - k) * (poch (μ - lam) k /
k.factorial) * ultrasphPoly lam (n - 2 * k) x`. -/
@[dlmf 18.18.E16]
theorem ultrasphPoly_connection {lam μ : ℂ} (hlam : 0 < lam.re) (hμ : -1 / 2 < μ.re) (n : ℕ)
    (x : ℂ) :
    ultrasphPoly μ n x = ∑ k ∈ Finset.range (n / 2 + 1),
      (lam + n - 2 * k) / lam * poch μ (n - k) / poch (lam + 1) (n - k) *
      (poch (μ - lam) k / k.factorial) * ultrasphPoly lam (n - 2 * k) x := by
  have hl : lam ≠ 0 := by intro he; simp [he] at hlam
  have hp (r : ℕ) : poch (lam + 1) r ≠ 0 := poch_ne_zero_of_re_pos (by simp; linarith) r
  have hf (r : ℕ) : (r.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr r.factorial_ne_zero
  let G : ℕ → ℕ → ℂ := fun j k =>
    ((-1 : ℂ) ^ j * poch μ (n - j) / ((j.factorial : ℂ) * (n - 2 * j).factorial)) *
      ((n - 2 * j).factorial * ((lam + ((n - 2 * j : ℕ) : ℂ) - 2 * k) / lam /
        (poch (lam + 1) (n - 2 * j - k) * k.factorial)) * ultrasphPoly lam (n - 2 * j - 2 * k) x)
  have he : ultrasphPoly μ n x = ∑ j ∈ Finset.range (n / 2 + 1),
      ∑ k ∈ Finset.range (n / 2 - j + 1), G j k := by
    rw [ultrasphPoly_finite_sum hμ]
    apply Finset.sum_congr rfl
    intro j hj
    have hj' : 2 * j ≤ n := by have := Finset.mem_range.mp hj; omega
    rw [monomial_ultrasphPoly_expansion hlam, Finset.mul_sum, Finset.mul_sum,
      show (n - 2 * j) / 2 = n / 2 - j by omega]
    apply Finset.sum_congr rfl
    intro k hk
    dsimp [G]
    ring
  rw [he, sum_triangle_by_total_degree]
  apply Finset.sum_congr rfl
  intro r hr
  have hrn : 2 * r ≤ n := by have := Finset.mem_range.mp hr; omega
  let C : ℂ := (lam + n - 2 * r) / lam * poch μ (n - r) /
    poch (lam + 1) (n - r) / r.factorial * ultrasphPoly lam (n - 2 * r) x
  have ht (j : ℕ) (hj : j ∈ Finset.range (r + 1)) : G j (r - j) = C *
      ((r.choose j : ℂ) * poch (-lam - n + r) j * poch (μ + (n - r : ℕ)) (r - j)) := by
    have hjr : j ≤ r := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    have hjn : j ≤ n - r := by omega
    have hden : poch (lam + 1) (n - r) = poch (lam + 1) (n - r - j) *
        ((-1 : ℂ) ^ j * poch (-lam - n + r) j) := by
      have hh := poch_add (lam + 1) (n - r - j) j
      rw [show n - r - j + j = n - r by omega] at hh
      have href := DLMF.Confluent.poch_sub_nat_self (lam + 1 + (n - r : ℕ)) j
      rw [show lam + 1 + (n - r : ℕ) - j = lam + 1 + (n - r - j : ℕ) by
        rw [Nat.cast_sub hjn]; ring,
        show 1 - (lam + 1 + (n - r : ℕ)) = -lam - n + r by rw [Nat.cast_sub (by omega : r ≤ n)]; ring] at href
      rw [href] at hh
      exact hh
    have hnum : poch μ (n - j) = poch μ (n - r) * poch (μ + (n - r : ℕ)) (r - j) := by
      rw [← poch_add]
      congr 1
      omega
    have hB : poch (-lam - n + r) j ≠ 0 := by
      have hh := hp (n - r)
      rw [hden] at hh
      exact right_ne_zero_of_mul (right_ne_zero_of_mul hh)
    dsimp [G, C]
    rw [show n - 2 * j - (r - j) = n - r - j by omega,
      show n - 2 * j - 2 * (r - j) = n - 2 * r by omega,
      show (lam + ((n - 2 * j : ℕ) : ℂ) - 2 * ((r - j : ℕ) : ℂ)) = lam + n - 2 * r by
        rw [Nat.cast_sub (by omega : 2 * j ≤ n), Nat.cast_sub hjr, Nat.cast_mul, Nat.cast_ofNat]; ring,
      hnum, hden, Nat.cast_choose ℂ hjr]
    have hsgn : ((-1 : ℂ) ^ j) ^ 2 = 1 := by
      rw [← pow_mul, Nat.mul_comm, pow_mul]; norm_num
    field_simp [hl, hp, hf, hB]
    rw [hsgn, one_mul]
  rw [Finset.sum_congr rfl ht, ← Finset.mul_sum]
  have hv := poch_add_eq_sum (-lam - n + r) (μ + (n - r : ℕ)) r
  rw [show -lam - n + r + (μ + (n - r : ℕ)) = μ - lam by
    rw [Nat.cast_sub (by omega : r ≤ n)]; ring] at hv
  rw [← hv]
  dsimp [C]
  ring

/-- Formula under the stated hypotheses: `laguerreExtended β n x = ∑ k ∈ Finset.range (n + 1),
poch (β - α) (n - k) / (n - k).factorial * laguerreExtended α k x`. -/
@[dlmf 18.18.E18]
theorem laguerrePolyL_connection (α β : ℂ) (n : ℕ) (x : ℂ) :
    laguerreExtended β n x = ∑ k ∈ Finset.range (n + 1),
      poch (β - α) (n - k) / (n - k).factorial * laguerreExtended α k x := by
  unfold laguerreExtended
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm' (t' := Finset.range (n + 1)) (s' := fun j => Finset.Ico j (n + 1))
    (by intro k j; simp only [Finset.mem_range, Finset.mem_Ico]; omega)]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjn : j ≤ n := by simp at hj; omega
  rw [Finset.sum_Ico_eq_sum_range, show n + 1 - j = (n - j) + 1 by omega]
  have hv := poch_add_eq_sum (α + j + 1) (β - α) (n - j)
  rw [show α + j + 1 + (β - α) = β + j + 1 by ring] at hv
  rw [hv, Finset.sum_div, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hmN : m ≤ n - j := by simp at hm; omega
  rw [show n - (j + m) = n - j - m by omega, show j + m - j = m by omega,
    Nat.cast_choose ℂ hmN]
  have h1 : ((n - j - m).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h2 : (m.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h3 : (j.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h4 : ((n - j).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  field_simp

/-- Formula under the stated hypotheses: `x ^ n = poch (α + 1) n * ∑ k ∈ Finset.range (n + 1),
poch (-(n : ℂ)) k / poch (α + 1) k * laguerrePolyL α k x`. -/
@[dlmf 18.18.E19]
theorem monomial_laguerrePolyL_expansion {α : ℂ} (hα : -1 < α.re) (n : ℕ) (x : ℂ) :
    x ^ n = poch (α + 1) n * ∑ k ∈ Finset.range (n + 1),
      poch (-(n : ℂ)) k / poch (α + 1) k * laguerrePolyL α k x := by
  have hc : ∀ k : ℕ, α + 1 ≠ -(k : ℂ) := not_neg_nat_of_re_pos (by simp; linarith)
  have hpk : ∀ k, poch (α + 1) k ≠ 0 := poch_ne_zero_of_not_neg_nat hc
  simp_rw [laguerrePolyL_eq_sum hc, Finset.mul_sum]
  rw [Finset.sum_comm' (t' := Finset.range (n + 1)) (s' := fun j => Finset.Ico j (n + 1))
    (by intro k j; simp only [Finset.mem_range, Finset.mem_Ico]; omega)]
  have hterm : ∀ j ∈ Finset.range (n + 1), ∑ k ∈ Finset.Ico j (n + 1),
      poch (α + 1) n * (poch (-(n : ℂ)) k / poch (α + 1) k *
        (poch (α + 1 + j) (k - j) / ((k - j).factorial * j.factorial : ℂ) * (-x) ^ j)) =
      poch (α + 1) n * (-x) ^ j * poch (-(n : ℂ)) j / (poch (α + 1) j * j.factorial) *
        0 ^ (n - j) := by
    intro j hj
    have hjn : j ≤ n := by simp at hj; omega
    rw [Finset.sum_Ico_eq_sum_range, show n + 1 - j = (n - j) + 1 by omega]
    have hs := sum_poch_neg_nat_div_factorial_mul_pow (n - j) 1
    rw [sub_self] at hs
    rw [← hs, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [show j + m - j = m by omega, poch_add (α + 1) j m, poch_add (-(n : ℂ)) j m,
      show -(n : ℂ) + j = -((n - j : ℕ) : ℂ) by push_cast [Nat.cast_sub hjn]; ring]
    have h1 := hpk j
    have h2 : poch (α + 1 + j) m ≠ 0 := by
      have := hpk (j + m); rw [poch_add] at this; exact right_ne_zero_of_mul this
    have h3 : (m.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have h4 : (j.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    field_simp
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_eq_single n]
  · rw [Nat.sub_self, pow_zero, mul_one, poch_neg_coe_nat, Nat.descFactorial_self, neg_pow]
    have h4 : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    field_simp [hpk n]
    rw [← pow_mul, mul_comm n 2, pow_mul, neg_one_sq, one_pow, mul_one]
  · intro j hj hjn
    have : 0 < n - j := by simp at hj; omega
    simp [zero_pow this.ne']
  · simp

/-- Formula under the stated hypotheses: `(2 * x) ^ n = ∑ k ∈ Finset.range (n / 2 + 1), poch (-(n
: ℂ)) (2 * k) / k.factorial * aeval x (hermitePolyH (n - 2 * k))`. -/
@[dlmf 18.18.E20]
theorem monomial_hermitePolyH_expansion (n : ℕ) (x : ℂ) :
    (2 * x) ^ n = ∑ k ∈ Finset.range (n / 2 + 1),
      poch (-(n : ℂ)) (2 * k) / k.factorial * aeval x (hermitePolyH (n - 2 * k)) := by
  have hc := Complex.powerSeries_coefficients_unique
    (c := fun j => (2 * x) ^ j / j !)
    (d := fun j => ∑ k ∈ Finset.range (j / 2 + 1),
      (1 : ℂ) ^ k / k ! * ((aeval x (hermitePolyH (j - 2 * k)) : ℂ) / (j - 2 * k)! *
        (1 : ℂ) ^ (j - 2 * k)))
    (f := fun z => exp (2 * x * z))
    (fun z _ => by
      convert NormedSpace.expSeries_div_hasSum_exp (2 * x * z) using 1
      · funext j; rw [mul_pow]; ring
      · simp only [Complex.exp_eq_exp_ℂ])
    (fun z _ => by
      convert hasSum_exp_quadratic_mul_hermite 1 1 x z using 1
      congr 1; ring)
  have h := congrArg (fun c : ℕ → ℂ => c n * n !) hc
  rw [div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr n.factorial_ne_zero), Finset.sum_mul] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : 2 * k ≤ n := by have := Finset.mem_range.mp hk; omega
  rw [← poch_neg_nat_even_mul_factorial hk']
  simp only [one_pow, mul_one, one_div]
  field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k),
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (n - 2 * k))]

/-- Formula under the stated hypotheses: `(aeval x (hermitePolyH m) : ℂ) * aeval x (hermitePolyH
n) = ∑ k ∈ Finset.range (min m n + 1), (m.choose k : ℂ) * n.choose k * 2 ^ k * k.factorial *
aeval x (hermitePolyH (m + n - 2 * k))`. -/
@[dlmf 18.18.E23]
theorem hermitePolyH_linearization (m n : ℕ) (x : ℂ) :
    (aeval x (hermitePolyH m) : ℂ) * aeval x (hermitePolyH n) =
      ∑ k ∈ Finset.range (min m n + 1), (m.choose k : ℂ) * n.choose k * 2 ^ k * k.factorial *
        aeval x (hermitePolyH (m + n - 2 * k)) := by
  have hc := Complex.powerSeries_coefficients_unique
    (c := fun j => (aeval x (hermitePolyH m) : ℂ) * aeval x (hermitePolyH j) / j !)
    (d := fun j => ∑ k ∈ Finset.range (m + 1),
      (m.choose k : ℂ) * 2 ^ k *
        (if k ≤ j then (aeval x (hermitePolyH (m - k + (j - k))) : ℂ) / (j - k)! else 0))
    (f := fun z => (aeval x (hermitePolyH m) : ℂ) * exp (2 * x * z - z ^ 2))
    (fun z _ => ((hasSum_hermitePolyH_generating_function x z).mul_left
      (aeval x (hermitePolyH m) : ℂ)).congr_fun (by intro j; ring))
    (fun z _ => by
      have hs (k : ℕ) := (hasSum_scalar_shift
        (c := fun j => (aeval x (hermitePolyH (m - k + j)) : ℂ) / j !) (z := z)
        ((hasSum_hermitePolyH_shifted (m - k) x z).congr_fun (by intro j; ring)) k).mul_left
          ((m.choose k : ℂ) * 2 ^ k)
      have h := hasSum_sum (s := Finset.range (m + 1)) (fun k _ => hs k)
      have hv : (∑ k ∈ Finset.range (m + 1), (m.choose k : ℂ) * 2 ^ k *
          (z ^ k * ((aeval (x - z) (hermitePolyH (m - k)) : ℂ) * exp (2 * x * z - z ^ 2)))) =
          (aeval x (hermitePolyH m) : ℂ) * exp (2 * x * z - z ^ 2) := by
        rw [show (∑ k ∈ Finset.range (m + 1), (m.choose k : ℂ) * 2 ^ k *
            (z ^ k * ((aeval (x - z) (hermitePolyH (m - k)) : ℂ) * exp (2 * x * z - z ^ 2)))) =
            (∑ k ∈ Finset.range (m + 1), (m.choose k : ℂ) * (2 * z) ^ k *
              aeval (x - z) (hermitePolyH (m - k))) * exp (2 * x * z - z ^ 2) by
          rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro k _; rw [mul_pow]; ring]
        rw [← hermitePolyH_translation, sub_add_cancel]
      rw [hv] at h
      simpa only [Finset.sum_mul, mul_assoc] using h)
  have h := congrArg (fun c : ℕ → ℂ => c n * n !) hc
  rw [div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr n.factorial_ne_zero), Finset.sum_mul] at h
  rw [h]
  have hsub : Finset.range (min m n + 1) ⊆ Finset.range (m + 1) :=
    Finset.range_subset_range.mpr (by omega)
  rw [← Finset.sum_subset hsub (by
    intro k hk hkn
    have hnk : ¬ k ≤ n := by
      simp only [Finset.mem_range] at hk hkn; omega
    simp [hnk])]
  apply Finset.sum_congr rfl
  intro k hk
  have hkm : k ≤ m := by have := Finset.mem_range.mp hk; omega
  have hkn : k ≤ n := by have := Finset.mem_range.mp hk; omega
  rw [if_pos hkn, show m - k + (n - k) = m + n - 2 * k by omega]
  have he : (n.choose k : ℂ) * k ! * (n - k)! = n ! := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hkn
  rw [← he]
  field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (n - k))]

/-- The series with terms `(fun n : ℕ => (aeval (x : ℂ) (hermitePolyH n) : ℂ) * aeval (y : ℂ)
(hermitePolyH n) / (2 ^ n * (n.factorial : ℂ)) * z ^ n)` converges to `((1 - z ^ 2) ^ (-1 / 2
: ℂ) * exp ((2 * x * y * z - (x ^ 2 + y ^ 2) * z ^ 2) / (1 - z ^ 2)))`. -/
@[dlmf 18.18.E28]
theorem mehler_formula (x y : ℝ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => (aeval (x : ℂ) (hermitePolyH n) : ℂ) * aeval (y : ℂ) (hermitePolyH n) /
      (2 ^ n * (n.factorial : ℂ)) * z ^ n)
      ((1 - z ^ 2) ^ (-1 / 2 : ℂ) * exp ((2 * x * y * z - (x ^ 2 + y ^ 2) * z ^ 2) / (1 - z ^ 2))) := by
  exact Mehler.hasSum_kernel (x : ℂ) (y : ℂ) hz

/-- Formula under the stated hypotheses: `legendrePolyP n (Real.cos θ * Real.cos ψ + Real.sin θ *
Real.sin ψ * Real.cos phi) = legendrePolyP n (Real.cos θ) * legendrePolyP n (Real.cos ψ) + 2 *
∑ k ∈ Finset.Icc 1 n, ((n - k).factorial : ℂ) * (n + k).factorial / (2 ^ (2 * k) *
(n.factorial : ℂ) ^ 2) * (Real.sin θ : ℂ) ^ k * jacobiPolyP k k (n - k) (Real.cos θ) *
(Real.sin ψ : ℂ) ^ k * jacobiPolyP k k (n - k) (Real.cos ψ) * Real.cos (k * phi)`. -/
@[dlmf 18.18.E9]
theorem legendre_addition (n : ℕ) (θ ψ phi : ℝ) :
    legendrePolyP n (Real.cos θ * Real.cos ψ + Real.sin θ * Real.sin ψ * Real.cos phi) =
      legendrePolyP n (Real.cos θ) * legendrePolyP n (Real.cos ψ) +
      2 * ∑ k ∈ Finset.Icc 1 n, ((n - k).factorial : ℂ) * (n + k).factorial /
        (2 ^ (2 * k) * (n.factorial : ℂ) ^ 2) * (Real.sin θ : ℂ) ^ k *
        jacobiPolyP k k (n - k) (Real.cos θ) * (Real.sin ψ : ℂ) ^ k *
        jacobiPolyP k k (n - k) (Real.cos ψ) * Real.cos (k * phi) := by
  have hs0 := congrArg (fun x : ℝ => (x : ℂ)) (Real.sin_sq_add_cos_sq θ)
  have ht0 := congrArg (fun x : ℝ => (x : ℂ)) (Real.sin_sq_add_cos_sq ψ)
  push_cast at hs0 ht0 ⊢
  have hs : sin (θ : ℂ)^2 = 1-cos (θ : ℂ)^2 := by linear_combination hs0
  have ht : sin (ψ : ℂ)^2 = 1-cos (ψ : ℂ)^2 := by linear_combination ht0
  rw [LegendreAddition.legendre_eq_kernel n (cos θ) (cos ψ) (sin θ) (sin ψ) phi hs ht,
    LegendreAddition.kernel]
  rw [show Finset.Icc 1 n = Finset.Ico 1 (n+1) by
    ext k; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega,
    Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel, Nat.add_comm 1]
  rw [LegendreAddition.coeff, LegendreAddition.weight_zero]
  simp only [pow_zero, one_mul, LegendreAddition.jet_zero]
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k+1 ≤ n := by simp at hk; omega
  rw [LegendreAddition.coeff_eq_jacobi n (k+1) hk']
  push_cast
  ring

/-- The Gegenbauer product coefficient in the three nonnegative gap indices. -/
noncomputable def gegenbauerProductCoeff (lam : ℂ) (a b k : ℕ) : ℂ :=
  (lam + a + b) / (lam + a + b + k) * (a + b).factorial /
    (k.factorial * a.factorial * b.factorial) *
      (poch lam k * poch lam a * poch lam b * poch (2 * lam) (a + b + k) /
        (poch lam (a + b + k) * poch (2 * lam) (a + b)))

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
/-- The interior coefficient recurrence follows from factorial and Pochhammer shifts. -/
theorem gegenbauerProductCoeff_recurrence {lam : ℂ} (hlam : 0 < lam.re) (a b k : ℕ) :
    (b + k + 2 : ℂ) * gegenbauerProductCoeff lam a (b + 1) (k + 1) =
      (b + k + 1 + lam) * (a + b + 1) / (lam + a + b) * gegenbauerProductCoeff lam a b (k + 1) +
      (b + k + 1 + lam) * (a + b + 2 * lam + 1) / (lam + a + b + 2) *
        gegenbauerProductCoeff lam (a + 1) (b + 1) k -
      (b + k + 2 * lam) * gegenbauerProductCoeff lam (a + 1) b k := by
  have hp (j : ℕ) : poch lam j ≠ 0 :=
    poch_ne_zero_of_not_neg_nat (not_neg_nat_of_re_pos hlam) j
  have hp2 (j : ℕ) : poch (2 * lam) j ≠ 0 :=
    poch_ne_zero_of_not_neg_nat (not_neg_nat_of_re_pos (by simp; linarith)) j
  have hf (j : ℕ) : (j.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr j.factorial_ne_zero
  have hn (i j q : ℕ) : lam + i + j + q ≠ 0 := by
    intro he
    have hh := congrArg Complex.re he
    simp at hh
    linarith [Nat.cast_nonneg (α := ℝ) i, Nat.cast_nonneg (α := ℝ) j,
      Nat.cast_nonneg (α := ℝ) q]
  have hd01 : a + (b + 1) = (a + b) + 1 := by omega
  have hd11 : (a + 1) + (b + 1) = (a + b) + 1 + 1 := by omega
  have hd10 : (a + 1) + b = (a + b) + 1 := by omega
  have hidx01' : (a + b + 1) + (k + 1) = (a + b + k) + 1 + 1 := by omega
  have hidx11' : (a + b + 1 + 1) + k = (a + b + k) + 1 + 1 := by omega
  have hidx10' : (a + b + 1) + k = (a + b + k) + 1 := by omega
  unfold gegenbauerProductCoeff
  simp only [hd01, hd11, hd10]
  simp only [hidx01', hidx11', hidx10', Nat.add_succ, poch_succ, Nat.factorial_succ]
  push_cast
  have h0 : lam + a + b ≠ 0 := by simpa using hn a b 0
  have h1 : lam + a + b + 1 ≠ 0 := by simpa using hn a b 1
  have h2 : lam + a + b + 2 ≠ 0 := by simpa using hn a b 2
  have hs0 : lam + a + b + k ≠ 0 := hn a b k
  have hs1 : lam + a + b + k + 1 ≠ 0 := by simpa [add_assoc] using hn a b (k + 1)
  have hs2 : lam + a + b + k + 2 ≠ 0 := by simpa [add_assoc] using hn a b (k + 2)
  have h20 : 2 * lam + a + b ≠ 0 := by
    intro he; have hh := congrArg Complex.re he; simp at hh
    linarith [Nat.cast_nonneg (α := ℝ) a, Nat.cast_nonneg (α := ℝ) b]
  have h21 : 2 * lam + a + b + 1 ≠ 0 := by
    intro he; have hh := congrArg Complex.re he; simp at hh
    linarith [Nat.cast_nonneg (α := ℝ) a, Nat.cast_nonneg (α := ℝ) b]
  simp only [add_comm, add_left_comm, add_assoc, one_add_one_eq_two] at h0 h1 h2 hs0 hs1 hs2 h20 h21 ⊢
  field_simp [hp, hp2, hf, h0, h1, h2, hs0, hs1, hs2, h20, h21]
  ring

/-- The coefficient of the trivial factor is one. -/
theorem gegenbauerProductCoeff_zero {lam : ℂ} (hlam : 0 < lam.re) (a : ℕ) :
    gegenbauerProductCoeff lam a 0 0 = 1 := by
  have hp (j : ℕ) : poch lam j ≠ 0 := poch_ne_zero_of_not_neg_nat (not_neg_nat_of_re_pos hlam) j
  have hp2 (j : ℕ) : poch (2 * lam) j ≠ 0 :=
    poch_ne_zero_of_not_neg_nat (not_neg_nat_of_re_pos (by simp; linarith)) j
  have hf (j : ℕ) : (j.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr j.factorial_ne_zero
  have hn : lam + a ≠ 0 := by
    intro he; have hh := congrArg Complex.re he; simp at hh
    linarith [Nat.cast_nonneg (α := ℝ) a]
  simp [gegenbauerProductCoeff, poch_zero, hp, hp2, hf, hn]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
/-- The upper endpoint of the coefficient recurrence. -/
theorem gegenbauerProductCoeff_top {lam : ℂ} (hlam : 0 < lam.re) (a b : ℕ) :
    (b + 1 : ℂ) * gegenbauerProductCoeff lam a (b + 1) 0 =
      (b + lam) * (a + b + 1) / (lam + a + b) * gegenbauerProductCoeff lam a b 0 := by
  have hp (j : ℕ) : poch lam j ≠ 0 := poch_ne_zero_of_not_neg_nat (not_neg_nat_of_re_pos hlam) j
  have hp2 (j : ℕ) : poch (2 * lam) j ≠ 0 :=
    poch_ne_zero_of_not_neg_nat (not_neg_nat_of_re_pos (by simp; linarith)) j
  have hf (j : ℕ) : (j.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr j.factorial_ne_zero
  have hn (q : ℕ) : lam + a + b + q ≠ 0 := by
    intro he; have hh := congrArg Complex.re he; simp at hh
    linarith [Nat.cast_nonneg (α := ℝ) a, Nat.cast_nonneg (α := ℝ) b, Nat.cast_nonneg (α := ℝ) q]
  have h0 : lam + a + b ≠ 0 := by simpa using hn 0
  have h1 : lam + a + b + 1 ≠ 0 := by simpa using hn 1
  unfold gegenbauerProductCoeff
  simp only [Nat.cast_zero, add_zero, Nat.factorial_zero, Nat.cast_one,
    poch_zero, one_mul, show a + (b + 1) = (a + b) + 1 by omega,
    poch_succ, Nat.factorial_succ]
  push_cast
  have h20 : 2 * lam + a + b ≠ 0 := by
    intro he; have hh := congrArg Complex.re he; simp at hh
    linarith [Nat.cast_nonneg (α := ℝ) a, Nat.cast_nonneg (α := ℝ) b]
  simp only [mul_comm, add_comm, add_left_comm, add_assoc] at hp2 h0 h1 h20 ⊢
  field_simp [hp, hp2, hf, h0, h1, h20]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
/-- The lower endpoint of the coefficient recurrence. -/
theorem gegenbauerProductCoeff_bottom {lam : ℂ} (hlam : 0 < lam.re) (a k : ℕ) :
    (k + 1 : ℂ) * gegenbauerProductCoeff lam a 0 (k + 1) =
      (k + lam) * (a + 2 * lam) / (lam + a + 1) * gegenbauerProductCoeff lam (a + 1) 0 k := by
  have hp (j : ℕ) : poch lam j ≠ 0 := poch_ne_zero_of_not_neg_nat (not_neg_nat_of_re_pos hlam) j
  have hp2 (j : ℕ) : poch (2 * lam) j ≠ 0 :=
    poch_ne_zero_of_not_neg_nat (not_neg_nat_of_re_pos (by simp; linarith)) j
  have hf (j : ℕ) : (j.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr j.factorial_ne_zero
  have hn (q : ℕ) : lam + a + q ≠ 0 := by
    intro he; have hh := congrArg Complex.re he; simp at hh
    linarith [Nat.cast_nonneg (α := ℝ) a, Nat.cast_nonneg (α := ℝ) q]
  have h0 : lam + a ≠ 0 := by simpa using hn 0
  have h1 : lam + a + 1 ≠ 0 := by simpa using hn 1
  have hs : lam + a + k + 1 ≠ 0 := by simpa [add_assoc] using hn (k + 1)
  have h2 : 2 * lam + a ≠ 0 := by
    intro he; have hh := congrArg Complex.re he; simp at hh
    linarith [Nat.cast_nonneg (α := ℝ) a]
  unfold gegenbauerProductCoeff
  simp only [Nat.cast_zero, add_zero, Nat.factorial_zero, Nat.cast_one,
    poch_zero, mul_one, show (a + 1) + k = a + k + 1 by omega,
    Nat.add_succ, poch_succ, Nat.factorial_succ]
  push_cast
  have hs0 : lam + a + k ≠ 0 := hn k
  simp only [mul_comm, add_comm, add_left_comm, add_assoc] at hp2 h0 h1 hs hs0 h2 ⊢
  field_simp [hp, hp2, hf, h0, h1, hs, hs0, h2]

/-- Multiplication by `2x` in the Gegenbauer basis, for positive degree. -/
theorem two_mul_x_ultrasphPoly {lam : ℂ} (hlam : 0 < lam.re) {d : ℕ} (hd : 0 < d) (x : ℂ) :
    2 * x * ultrasphPoly lam d x =
      (d + 1 : ℂ) / (lam + d) * ultrasphPoly lam (d + 1) x +
      (d + 2 * lam - 1) / (lam + d) * ultrasphPoly lam (d - 1) x := by
  have hn : lam + d ≠ 0 := by
    intro he; have hh := congrArg Complex.re he; simp at hh
    linarith [Nat.cast_nonneg (α := ℝ) d]
  have hh := ultrasphPoly_recurrence (by linarith : -1 / 2 < lam.re) (d - 1) x
  rw [show d - 1 + 2 = d + 1 by omega, show d - 1 + 1 = d by omega,
    Nat.cast_sub (by omega : 1 ≤ d)] at hh
  push_cast at hh
  field_simp [hn]
  linear_combination -hh

/-- The finite product expansion with the second degree bounded by the first. -/
noncomputable def gegenbauerLinearizationSum (lam : ℂ) (m n : ℕ) (x : ℂ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1), gegenbauerProductCoeff lam (m - k) (n - k) k *
    ultrasphPoly lam (m + n - 2 * k) x

/-- The finite coefficient sum obeys the Gegenbauer recurrence in its second degree. -/
theorem gegenbauerLinearizationSum_recurrence {lam : ℂ} (hlam : 0 < lam.re)
    {m n : ℕ} (hnm : n + 2 ≤ m) (x : ℂ) :
    (n + 2 : ℂ) * gegenbauerLinearizationSum lam m (n + 2) x =
      2 * (n + lam + 1) * x * gegenbauerLinearizationSum lam m (n + 1) x -
        (n + 2 * lam) * gegenbauerLinearizationSum lam m n x := by
  let T : ℕ → ℂ := fun k => gegenbauerProductCoeff lam (m - k) (n + 2 - k) k *
    ultrasphPoly lam (m + (n + 2) - 2 * k) x
  let U : ℕ → ℂ := fun k => gegenbauerProductCoeff lam (m - k) (n + 1 - k) k *
    ultrasphPoly lam (m + (n + 1) - 2 * k) x
  let V : ℕ → ℂ := fun k => gegenbauerProductCoeff lam (m - k) (n - k) k *
    ultrasphPoly lam (m + n - 2 * k) x
  let A : ℕ → ℂ := fun k => (n + lam + 1) * ((m + (n + 1) - 2 * k : ℕ) + 1) /
    (lam + (m + (n + 1) - 2 * k : ℕ)) * gegenbauerProductCoeff lam (m - k) (n + 1 - k) k *
      ultrasphPoly lam ((m + (n + 1) - 2 * k) + 1) x
  let B : ℕ → ℂ := fun k => (n + lam + 1) * ((m + (n + 1) - 2 * k : ℕ) + 2 * lam - 1) /
    (lam + (m + (n + 1) - 2 * k : ℕ)) * gegenbauerProductCoeff lam (m - k) (n + 1 - k) k *
      ultrasphPoly lam ((m + (n + 1) - 2 * k) - 1) x
  have hU (k : ℕ) (hk : k ∈ Finset.range (n + 2)) :
      2 * (n + lam + 1) * x * U k = A k + B k := by
    have hd : 0 < m + (n + 1) - 2 * k := by have := Finset.mem_range.mp hk; omega
    dsimp [U, A, B]
    have he := congrArg (fun v : ℂ => (n + lam + 1) *
      gegenbauerProductCoeff lam (m - k) (n + 1 - k) k * v) (two_mul_x_ultrasphPoly hlam hd x)
    linear_combination he
  have hhead : (n + 2 : ℂ) * T 0 = A 0 := by
    dsimp [T, A]
    have he := congrArg (fun v : ℂ => v * ultrasphPoly lam (m + (n + 2)) x)
      (gegenbauerProductCoeff_top hlam m (n + 1))
    rw [show m + (n + 1) + 1 = m + (n + 2) by omega]
    push_cast at he ⊢
    linear_combination he
  have htail : (n + 2 : ℂ) * T (n + 2) = B (n + 1) := by
    have hm : m - (n + 2) + 1 = m - (n + 1) := by omega
    dsimp [T, B]
    rw [Nat.sub_self, Nat.sub_self]
    have he := congrArg (fun v : ℂ => v * ultrasphPoly lam (m - (n + 2)) x)
      (gegenbauerProductCoeff_bottom hlam (m - (n + 2)) (n + 1))
    rw [hm] at he
    rw [show m + (n + 2) - 2 * (n + 2) = m - (n + 2) by omega,
      show m + (n + 1) - 2 * (n + 1) = m - (n + 1) by omega,
      show m - (n + 1) - 1 = m - (n + 2) by omega]
    push_cast [Nat.cast_sub (show n + 1 ≤ m by omega), Nat.cast_sub hnm] at he ⊢
    linear_combination he
  have hinner (j : ℕ) (hj : j ∈ Finset.range (n + 1)) :
      (n + 2 : ℂ) * T (j + 1) = A (j + 1) + B j - (n + 2 * lam) * V j := by
    have hjn : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    have hM : m - (j + 1) = m - j - 1 := by omega
    have hN : n + 2 - (j + 1) = (n - j) + 1 := by omega
    have hN0 : n + 1 - (j + 1) = n - j := by omega
    have hM1 : m - j - 1 + 1 = m - j := by omega
    have hN1 : n - j + 1 = n + 1 - j := by omega
    have hd0 : m + (n + 1) - 2 * (j + 1) = (m - j - 1) + (n - j) := by omega
    have hd1 : m + (n + 1) - 2 * j = (m - j - 1) + (n - j) + 2 := by omega
    have hd2 : m + (n + 2) - 2 * (j + 1) = (m - j - 1) + (n - j) + 1 := by omega
    have hd3 : m + n - 2 * j = (m - j - 1) + (n - j) + 1 := by omega
    dsimp [T, A, B, V]
    rw [hM, hN, hN0, hd0, hd1, hd2, hd3,
      show ((m - j - 1) + (n - j) + 2) - 1 = (m - j - 1) + (n - j) + 1 by omega]
    rw [hN1]
    have he := congrArg (fun v : ℂ => v * ultrasphPoly lam ((m - j - 1) + (n - j) + 1) x)
      (gegenbauerProductCoeff_recurrence hlam (m - j - 1) (n - j) j)
    rw [hM1, hN1] at he
    push_cast [Nat.cast_sub hjn] at he ⊢
    linear_combination he
  change (n + 2 : ℂ) * (∑ k ∈ Finset.range (n + 2 + 1), T k) =
    2 * (n + lam + 1) * x * (∑ k ∈ Finset.range (n + 1 + 1), U k) -
      (n + 2 * lam) * ∑ k ∈ Finset.range (n + 1), V k
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  rw [Finset.sum_congr rfl hU]
  simp only [Finset.sum_add_distrib]
  conv_lhs => rw [Finset.sum_range_succ, Finset.sum_range_succ']
  conv_rhs => lhs; lhs; rw [Finset.sum_range_succ']
  conv_rhs => lhs; rhs; rw [Finset.sum_range_succ]
  rw [hhead, htail]
  have hi := Finset.sum_congr rfl hinner
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib] at hi
  linear_combination hi

/-- Gegenbauer products are the finite coefficient sums when the second degree is smaller. -/
theorem ultrasphPoly_product_eq_sum_of_le {lam : ℂ} (hlam : 0 < lam.re) (m n : ℕ)
    (hnm : n ≤ m) (x : ℂ) :
    ultrasphPoly lam m x * ultrasphPoly lam n x = gegenbauerLinearizationSum lam m n x := by
  induction n using Nat.twoStepInduction with
  | zero => simp [gegenbauerLinearizationSum, gegenbauerProductCoeff_zero hlam]
  | one =>
    have hm : 0 < m := by omega
    have ht : gegenbauerProductCoeff lam m 1 0 = lam * (m + 1) / (lam + m) := by
      have he := gegenbauerProductCoeff_top hlam m 0
      rw [gegenbauerProductCoeff_zero hlam] at he
      norm_num at he
      linear_combination he
    have hb : gegenbauerProductCoeff lam (m - 1) 0 1 =
        lam * (m + 2 * lam - 1) / (lam + m) := by
      have he := gegenbauerProductCoeff_bottom hlam (m - 1) 0
      rw [gegenbauerProductCoeff_zero hlam] at he
      norm_num at he
      push_cast [Nat.cast_sub (show 1 ≤ m by omega)] at he
      convert he using 1; ring
    have he := two_mul_x_ultrasphPoly hlam hm x
    rw [ultrasphPoly_one_eq (by linarith : -1 / 2 < lam.re)]
    unfold gegenbauerLinearizationSum
    norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.sub_zero,
      Nat.sub_self, Nat.mul_zero, Nat.mul_one, Nat.cast_zero, Nat.cast_one]
    rw [ht, hb, show m + 1 - 2 = m - 1 by omega]
    linear_combination lam * he
  | more n ih0 ih1 =>
    have h0 := ih0 (by omega : n ≤ m)
    have h1 := ih1 (by omega : n + 1 ≤ m)
    have hS := gegenbauerLinearizationSum_recurrence hlam hnm x
    rw [← h0, ← h1] at hS
    have hC := ultrasphPoly_recurrence (by linarith : -1 / 2 < lam.re) n x
    have hn : (n + 2 : ℂ) ≠ 0 := by exact_mod_cast (by omega : n + 2 ≠ 0)
    apply mul_left_cancel₀ hn
    linear_combination ultrasphPoly lam m x * hC - hS

/-- Symmetry of the coefficient in the two gap indices. -/
theorem gegenbauerProductCoeff_swap (lam : ℂ) (a b k : ℕ) :
    gegenbauerProductCoeff lam a b k = gegenbauerProductCoeff lam b a k := by
  unfold gegenbauerProductCoeff
  rw [Nat.add_comm b a]
  ring

/-- Match the gap-index coefficient to the DLMF normalization. -/
theorem gegenbauerProductCoeff_eq (lam : ℂ) {m n k : ℕ} (hkm : k ≤ m) (hkn : k ≤ n) :
    gegenbauerProductCoeff lam (m - k) (n - k) k =
      (m + n + lam - 2 * k) * (m + n - 2 * k).factorial /
        ((m + n + lam - k) * k.factorial * (m - k).factorial * (n - k).factorial) *
        (poch lam k * poch lam (m - k) * poch lam (n - k) * poch (2 * lam) (m + n - k) /
          (poch lam (m + n - k) * poch (2 * lam) (m + n - 2 * k))) := by
  unfold gegenbauerProductCoeff
  rw [show (m - k) + (n - k) = m + n - 2 * k by omega,
    show m + n - 2 * k + k = m + n - k by omega]
  push_cast [Nat.cast_sub hkm, Nat.cast_sub hkn]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- Formula under the stated hypotheses: `ultrasphPoly lam m x * ultrasphPoly lam n x = ∑ k ∈
Finset.range (min m n + 1), (m + n + (lam : ℂ) - 2 * k) * (m + n - 2 * k).factorial / ((m + n
+ lam - k) * k.factorial * (m - k).factorial * (n - k).factorial) * (poch lam k * poch lam (m
- k) * poch lam (n - k) * poch (2 * lam) (m + n - k) / (poch lam (m + n - k) * poch (2 * lam)
(m + n - 2 * k))) * ultrasphPoly lam (m + n - 2 * k) x`. -/
@[dlmf 18.18.E22]
theorem ultrasphPoly_linearization {lam : ℝ} (hlam : 0 < lam) (m n : ℕ) (x : ℂ) :
    ultrasphPoly lam m x * ultrasphPoly lam n x = ∑ k ∈ Finset.range (min m n + 1),
      (m + n + (lam : ℂ) - 2 * k) * (m + n - 2 * k).factorial /
      ((m + n + lam - k) * k.factorial * (m - k).factorial * (n - k).factorial) *
      (poch lam k * poch lam (m - k) * poch lam (n - k) * poch (2 * lam) (m + n - k) /
       (poch lam (m + n - k) * poch (2 * lam) (m + n - 2 * k)))
           * ultrasphPoly lam (m + n - 2 * k) x := by
  have hl : 0 < (lam : ℂ).re := by simpa using hlam
  have he : ultrasphPoly lam m x * ultrasphPoly lam n x =
      ∑ k ∈ Finset.range (min m n + 1), gegenbauerProductCoeff lam (m - k) (n - k) k *
        ultrasphPoly lam (m + n - 2 * k) x := by
    rcases le_total n m with hnm | hmn
    · rw [min_eq_right hnm]
      exact ultrasphPoly_product_eq_sum_of_le hl m n hnm x
    · rw [min_eq_left hmn, mul_comm]
      have hh := ultrasphPoly_product_eq_sum_of_le hl n m hmn x
      simpa only [gegenbauerLinearizationSum, gegenbauerProductCoeff_swap (lam : ℂ), Nat.add_comm n m] using hh
  rw [he]
  apply Finset.sum_congr rfl
  intro k hk
  have hkm : k ≤ m := by have := Finset.mem_range.mp hk; omega
  have hkn : k ≤ n := by have := Finset.mem_range.mp hk; omega
  rw [gegenbauerProductCoeff_eq (lam : ℂ) hkm hkn]

/-- Formula under the stated hypotheses: `∑ k ∈ Finset.range (n + 1), ultrasphPoly lam k x *
ultrasphPoly μ (n - k) x = ultrasphPoly (lam + μ) n x`. -/
@[dlmf 18.18.E29]
theorem ultrasphPoly_convolution {lam μ : ℂ} (hlam : 0 < lam.re) (hμ : 0 < μ.re) (n : ℕ) (x : ℂ) :
    ∑ k ∈ Finset.range (n + 1),
        ultrasphPoly lam k x * ultrasphPoly μ (n - k) x = ultrasphPoly (lam + μ) n x := by
  obtain ⟨w, hw, rfl⟩ := exists_eq_half_add_recip x
  have h1 : -1 / 2 < lam.re := by linarith
  have h2 : -1 / 2 < μ.re := by linarith
  have h3 : -1 / 2 < (lam + μ).re := by rw [Complex.add_re]; linarith
  simp_rw [ultrasphPoly_eq_coeff_gegenbauerSeries h1 hw,
      ultrasphPoly_eq_coeff_gegenbauerSeries h2 hw,
    ultrasphPoly_eq_coeff_gegenbauerSeries h3 hw]
  exact sum_coeff_mul_coeff_gegenbauerSeries lam μ w n

/-- Formula under the stated hypotheses: `∑ k ∈ Finset.range (n + 1), (k + 2 * lam) / (2 * lam) *
ultrasphPoly lam k x * x ^ (n - k) = ultrasphPoly (lam + 1) n x`. -/
@[dlmf 18.18.E30]
theorem ultrasphPoly_geometric_convolution {lam : ℂ} (hlam : 0 < lam.re) (n : ℕ) (x : ℂ) :
    ∑ k ∈ Finset.range (n + 1), (k + 2 * lam) / (2 * lam) * ultrasphPoly lam k x * x ^ (n - k) =
      ultrasphPoly (lam + 1) n x := by
  obtain ⟨w, hw, rfl⟩ := exists_eq_half_add_recip x
  have h1 : -1 / 2 < lam.re := by linarith
  have h2 : -1 / 2 < (lam + 1).re := by rw [Complex.add_re, Complex.one_re]; linarith
  have hlam0 : lam ≠ 0 := fun h => by rw [h, Complex.zero_re] at hlam; exact lt_irrefl _ hlam
  simp_rw [ultrasphPoly_eq_coeff_gegenbauerSeries h1 hw,
      ultrasphPoly_eq_coeff_gegenbauerSeries h2 hw]
  exact sum_weighted_coeff_gegenbauerSeries hlam0 hw n

/-- `U_{n+2} = 2 T_{n+2} + U_n`. -/
theorem chebyshevU_eq_two_T_add_U (n : ℕ) (x : ℂ) :
    (Chebyshev.U ℂ (n + 2)).eval x =
      2 * (Chebyshev.T ℂ (n + 2)).eval x + (Chebyshev.U ℂ n).eval x := by
  have hT := congrArg (fun p : ℂ[X] => p.eval x)
    (Chebyshev.T_eq_X_mul_U_sub_U (R := ℂ) n)
  have hU := congrArg (fun p : ℂ[X] => p.eval x)
    (Chebyshev.U_add_two (R := ℂ) n)
  simp only [eval_sub, eval_mul, eval_X, eval_ofNat] at hT hU
  linear_combination hU - 2 * hT

/-- Formula under the stated hypotheses: `∑ k ∈ Finset.range (n + 1), (Chebyshev.T ℂ k).eval x * x
^ (n - k) = (Chebyshev.U ℂ n).eval x`. -/
@[dlmf 18.18.E31]
theorem chebyshev_geometric_sum (n : ℕ) (x : ℂ) :
    ∑ k ∈ Finset.range (n + 1), (Chebyshev.T ℂ k).eval x * x ^ (n - k) =
      (Chebyshev.U ℂ n).eval x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Nat.sub_self, pow_zero, mul_one]
    have hsum : ∑ k ∈ Finset.range (n + 1), (Chebyshev.T ℂ k).eval x * x ^ (n + 1 - k) =
        x * ∑ k ∈ Finset.range (n + 1), (Chebyshev.T ℂ k).eval x * x ^ (n - k) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      rw [show n + 1 - k = (n - k) + 1 by omega, pow_succ]
      ring
    rw [hsum, ih]
    have h := congrArg (Polynomial.eval x) (Chebyshev.U_eq_X_mul_U_add_T ℂ n)
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X] at h
    push_cast
    linear_combination -h

/-- Formula under the stated hypotheses: `2 * ∑ k ∈ Finset.range (n + 1), (Chebyshev.T ℂ (2 *
k)).eval x = 1 + (Chebyshev.U ℂ (2 * n)).eval x`. -/
@[dlmf 18.18.E32]
theorem chebyshevT_even_sum (n : ℕ) (x : ℂ) :
    2 * ∑ k ∈ Finset.range (n + 1), (Chebyshev.T ℂ (2 * k)).eval x =
      1 + (Chebyshev.U ℂ (2 * n)).eval x := by
  induction n with
  | zero =>
    simp [Chebyshev.T_zero, Chebyshev.U_zero]
    norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    have hU := chebyshevU_eq_two_T_add_U (2 * n) x
    have hU' : (Chebyshev.U ℂ (2 * (n + 1))).eval x =
        2 * (Chebyshev.T ℂ (2 * (n + 1))).eval x + (Chebyshev.U ℂ (2 * n)).eval x := by
      convert hU <;> (push_cast; ring)
    simp only [Nat.cast_succ] at hU' ⊢
    rw [hU']
    ring

/-- Formula under the stated hypotheses: `2 * ∑ k ∈ Finset.range (n + 1), (Chebyshev.T ℂ (2 * k +
1)).eval x = (Chebyshev.U ℂ (2 * n + 1)).eval x`. -/
@[dlmf 18.18.E33]
theorem chebyshevT_odd_sum (n : ℕ) (x : ℂ) :
    2 * ∑ k ∈ Finset.range (n + 1), (Chebyshev.T ℂ (2 * k + 1)).eval x =
      (Chebyshev.U ℂ (2 * n + 1)).eval x := by
  induction n with
  | zero => simp [Chebyshev.T_one, Chebyshev.U_one]
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    have h := congrArg (Polynomial.eval x) (Chebyshev.two_mul_T_eq_U_sub_U ℂ (2 * n + 1))
    simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_ofNat] at h
    rw [show (2 : ℤ) * ((n + 1 : ℕ) : ℤ) + 1 = 2 * (n : ℤ) + 1 + 2 by push_cast; ring]
    linear_combination h

/-- Formula under the stated hypotheses: `2 * (1 - x ^ 2) * ∑ k ∈ Finset.range (n + 1),
(Chebyshev.U ℂ (2 * k)).eval x = 1 - (Chebyshev.T ℂ (2 * n + 2)).eval x`. -/
@[dlmf 18.18.E34]
theorem chebyshevU_even_sum (n : ℕ) (x : ℂ) :
    2 * (1 - x ^ 2) * ∑ k ∈ Finset.range (n + 1), (Chebyshev.U ℂ (2 * k)).eval x =
      1 - (Chebyshev.T ℂ (2 * n + 2)).eval x := by
  induction n with
  | zero =>
    simp [Chebyshev.T_two]
    ring
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    have h1 := congrArg (Polynomial.eval x)
      (Chebyshev.one_sub_X_sq_mul_U_eq_pol_in_T ℂ (2 * n + 2))
    have h2 := congrArg (Polynomial.eval x) (Chebyshev.T_add_two ℂ (2 * n + 2))
    simp only [Polynomial.eval_mul, Polynomial.eval_sub,
      Polynomial.eval_one, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_ofNat] at h1 h2
    rw [show (2 : ℤ) * ((n + 1 : ℕ) : ℤ) = 2 * (n : ℤ) + 2 by push_cast; ring]
    linear_combination 2 * h1 - h2

/-- Formula under the stated hypotheses: `2 * (1 - x ^ 2) * ∑ k ∈ Finset.range (n + 1),
(Chebyshev.U ℂ (2 * k + 1)).eval x = x - (Chebyshev.T ℂ (2 * n + 3)).eval x`. -/
@[dlmf 18.18.E35]
theorem chebyshevU_odd_sum (n : ℕ) (x : ℂ) :
    2 * (1 - x ^ 2) * ∑ k ∈ Finset.range (n + 1), (Chebyshev.U ℂ (2 * k + 1)).eval x =
      x - (Chebyshev.T ℂ (2 * n + 3)).eval x := by
  induction n with
  | zero =>
    have h := congrArg (Polynomial.eval x) (Chebyshev.T_add_two ℂ 1)
    simp only [Polynomial.eval_mul, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_ofNat] at h
    norm_num [Chebyshev.T_two, Chebyshev.T_one] at h
    simp [Chebyshev.U_one]
    rw [h]
    ring
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    have h1 := congrArg (Polynomial.eval x)
      (Chebyshev.one_sub_X_sq_mul_U_eq_pol_in_T ℂ (2 * n + 3))
    have h2 := congrArg (Polynomial.eval x) (Chebyshev.T_add_two ℂ (2 * n + 3))
    simp only [Polynomial.eval_mul, Polynomial.eval_sub,
      Polynomial.eval_one, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_ofNat] at h1 h2
    rw [show (2 : ℤ) * ((n + 1 : ℕ) : ℤ) + 1 = 2 * (n : ℤ) + 3 by push_cast; ring,
      show (2 : ℤ) * ((n + 1 : ℕ) : ℤ) + 3 = 2 * (n : ℤ) + 3 + 2 by push_cast; ring]
    linear_combination 2 * h1 - h2

/-- Formula under the stated hypotheses: `∑ k ∈ Finset.range (n + 1), legendrePolyP k x *
legendrePolyP (n - k) x = (Chebyshev.U ℂ n).eval x`. -/
@[dlmf 18.18.E36]
theorem legendre_convolution (n : ℕ) (x : ℂ) :
    ∑ k ∈ Finset.range (n + 1),
        legendrePolyP k x * legendrePolyP (n - k) x = (Chebyshev.U ℂ n).eval x := by
  simp_rw [legendre_eq_ultrasphPoly]
  rw [ultrasphPoly_convolution (by norm_num) (by norm_num), eval_U_eq_ultrasphPoly]
  norm_num

/-- Formula under the stated hypotheses: `∑ k ∈ Finset.range (n + 1), laguerreExtended α k x =
laguerreExtended (α + 1) n x`. -/
@[dlmf 18.18.E37]
theorem laguerrePolyL_sum (α : ℂ) (n : ℕ) (x : ℂ) :
    ∑ k ∈ Finset.range (n + 1), laguerreExtended α k x = laguerreExtended (α + 1) n x := by
  -- the polynomial identity in `α` is proved for `Re α > 0` and extended by analyticity
  have hana : ∀ m : ℕ, AnalyticOnNhd ℂ (fun a : ℂ => laguerreExtended a m x) Set.univ := by
    intro m a _
    unfold laguerreExtended
    refine Finset.analyticAt_fun_sum (Finset.range (m + 1)) fun k _ => ?_
    have h : AnalyticAt ℂ (fun a : ℂ => poch (a + k + 1) (m - k)) a :=
      (((Polynomial.differentiable (ascPochhammer ℂ (m - k))).comp
        ((differentiable_id.add_const _).add_const _))).analyticAt a
    exact (h.div_const).mul analyticAt_const
  have key : (fun a : ℂ => ∑ k ∈ Finset.range (n + 1), laguerreExtended a k x) =
      fun a => laguerreExtended (a + 1) n x := by
    refine DLMF.Hypergeometric.eq_of_eqOn_re_pos ?_ ?_ ?_
    · intro a _
      exact Finset.analyticAt_fun_sum (Finset.range (n + 1)) fun k _ => hana k a (Set.mem_univ a)
    · intro a _
      exact ((hana n) (a + 1) (Set.mem_univ _)).comp (f := fun a : ℂ => a + 1) (by fun_prop)
    intro a ha
    have h1 : ∀ k : ℕ, a + 1 ≠ -(k : ℂ) := not_neg_nat_of_re_pos (by
      simp only [Complex.add_re, Complex.one_re]
      linarith)
    have h2 : ∀ k : ℕ, a + 1 + 1 ≠ -(k : ℂ) := not_neg_nat_of_re_pos (by
      simp only [Complex.add_re, Complex.one_re]
      linarith)
    have ha' : -1 < a.re := by linarith
    simp only [laguerreExtended_eq h1, laguerreExtended_eq h2]
    induction n with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, ih, laguerrePolyL_raise_parameter ha']
      ring
  exact congrFun key α

/-- Formula under the stated hypotheses: `∑ k ∈ Finset.range (n + 1), (n.choose k : ℂ) * (aeval x
(hermitePolyH (2 * k)) : ℂ) * aeval y (hermitePolyH (2 * n - 2 * k)) = (-1 : ℂ) ^ n * 2 ^ (2 *
n) * n.factorial * laguerrePolyL 0 n (x ^ 2 + y ^ 2)`. -/
@[dlmf 18.18.E40]
theorem hermitePolyH_even_convolution (n : ℕ) (x y : ℂ) :
    ∑ k ∈ Finset.range (n + 1), (n.choose k : ℂ) * (aeval x (hermitePolyH (2 * k)) : ℂ) *
      aeval y (hermitePolyH (2 * n - 2 * k)) = (-1 : ℂ) ^ n * 2 ^ (2 * n) * n.factorial
          * laguerrePolyL 0 n (x ^ 2 + y ^ 2) := by
  have hc : ∀ k : ℕ, (-1 / 2 : ℂ) + 1 ≠ -(k : ℂ) := not_neg_nat_of_re_pos (by norm_num)
  have hc0 : ∀ k : ℕ, (0 : ℂ) + 1 ≠ -(k : ℂ) := not_neg_nat_of_re_pos (by norm_num)
  have hadd := laguerrePolyL_addition (-1 / 2) (-1 / 2) (x ^ 2) (y ^ 2) n
  rw [show (-1 / 2 : ℂ) + -1 / 2 + 1 = 0 by ring, laguerreExtended_eq hc0] at hadd
  rw [hadd, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [show 2 * n - 2 * k = 2 * (n - k) by omega, hermitePolyH_even_eq_laguerrePolyL,
    hermitePolyH_even_eq_laguerrePolyL, laguerreExtended_eq hc, laguerreExtended_eq hc,
    Nat.cast_choose ℂ hkn]
  have h1 : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h2 : ((n - k).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hpow1 : (-1 : ℂ) ^ n = (-1) ^ k * (-1) ^ (n - k) := by
    rw [← pow_add, Nat.add_sub_cancel' hkn]
  have hpow2 : (2 : ℂ) ^ (2 * n) = 2 ^ (2 * k) * 2 ^ (2 * (n - k)) := by
    rw [← pow_add]; congr 1; omega
  rw [hpow1, hpow2]
  field_simp

/-- The regularized `₀F₁` series converges absolutely everywhere. -/
theorem summable_norm_regularized0F1 (c w : ℂ) :
    Summable fun n : ℕ => ‖regularizedHGFunCoeff (∅ : Multiset ℂ) {c} n * w ^ n‖ := by
  have hr : (FormalMultilinearSeries.ofScalars ℂ (regularizedHGFunCoeff ∅ {c})).radius = ⊤ :=
    top_le_iff.mp (hasFPowerSeriesOnBall_regularized0F1 c).r_le
  have := (FormalMultilinearSeries.ofScalars ℂ (regularizedHGFunCoeff ∅ {c})).summable_norm_mul_pow
    (r := ‖w‖₊) (by rw [hr]; exact ENNReal.coe_lt_top)
  simpa [FormalMultilinearSeries.ofScalars_norm, norm_mul, norm_pow] using this

/-- `(a)ₖ / Γ(a + k) = 1 / Γ(a)` away from the poles of `Γ`. -/
theorem poch_div_Gamma_add_nat {a : ℂ} (ha : ∀ k : ℕ, a ≠ -k) (k : ℕ) :
    poch a k / Complex.Gamma (a + k) = 1 / Complex.Gamma a := by
  have h := Complex.Gamma_add_nat_div_Gamma_eq (n := k) a ha
  have hG : Complex.Gamma a ≠ 0 := Complex.Gamma_ne_zero ha
  rw [poch, ← h]
  have hGk : Complex.Gamma (a + k) ≠ 0 := Complex.Gamma_ne_zero fun m hm =>
    ha (m + k) (by push_cast; linear_combination hm)
  field_simp

/-- The series with terms `(fun n : ℕ => jacobiPolyP α β n x / (Gamma (n + α + 1) * Gamma (n + β +
1)) * z ^ n)` converges to `(regularizedHGFun (∅ : Multiset ℂ) {α + 1} ((x - 1) * z / 2) *
regularizedHGFun (∅ : Multiset ℂ) {β + 1} ((x + 1) * z / 2))`. -/
@[dlmf 18.12.E2]
theorem jacobi_regularized_generating_function {α β : ℂ} (hα : -1 < α.re)
    (hβ : -1 < β.re) (x z : ℂ) :
    HasSum (fun n : ℕ => jacobiPolyP α β n x / (Gamma (n + α + 1) * Gamma (n + β + 1)) * z ^ n)
      (regularizedHGFun (∅ : Multiset ℂ) {α + 1} ((x - 1) * z / 2) *
       regularizedHGFun (∅ : Multiset ℂ) {β + 1} ((x + 1) * z / 2)) := by
  set u := (x - 1) * z / 2
  set v := (x + 1) * z / 2
  have hu := summable_norm_regularized0F1 (α + 1) u
  have hv := summable_norm_regularized0F1 (β + 1) v
  have hprod := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hv hu
  have hsum := (summable_norm_sum_mul_antidiagonal_of_summable_norm hv hu).of_norm.hasSum
  rw [← hprod, ((hasFPowerSeriesOnBall_regularized0F1 (β + 1)).hasSum_mul_pow
      (by simp)).tsum_eq, ((hasFPowerSeriesOnBall_regularized0F1 (α + 1)).hasSum_mul_pow
      (by simp)).tsum_eq] at hsum
  rw [mul_comm]
  refine hsum.congr_fun fun n => ?_
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, jacobi_binomial_sum hα, Finset.mul_sum,
    Finset.sum_div, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hA : poch (α + n - k + 1) k / Gamma (n + α + 1) = 1 / Gamma (α + 1 + (n - k : ℕ)) := by
    have := poch_div_Gamma_add_nat (a := α + 1 + (n - k : ℕ)) (not_neg_nat_of_re_pos (by
      simp only [Complex.add_re, Complex.one_re, Complex.natCast_re]
      linarith [(Nat.cast_nonneg (α := ℝ) (n - k))])) k
    rw [← this]
    congr 1
    · congr 1; push_cast [Nat.cast_sub hkn]; ring
    · congr 1; push_cast [Nat.cast_sub hkn]; ring
  have hB : poch (β + k + 1) (n - k) / Gamma (n + β + 1) = 1 / Gamma (β + 1 + k) := by
    have := poch_div_Gamma_add_nat (a := β + 1 + k) (not_neg_nat_of_re_pos (by
      simp only [Complex.add_re, Complex.one_re, Complex.natCast_re]
      linarith [(Nat.cast_nonneg (α := ℝ) k)])) (n - k)
    rw [← this]
    congr 1
    · congr 1; ring
    · congr 1; push_cast [Nat.cast_sub hkn]; ring
  simp only [regularizedHGFunCoeff_empty]
  have hGA : Gamma (n + α + 1) ≠ 0 := Complex.Gamma_ne_zero (not_neg_nat_of_re_pos (by
    simp only [Complex.add_re, Complex.one_re, Complex.natCast_re]
    linarith [(Nat.cast_nonneg (α := ℝ) n)]))
  have hGB : Gamma (n + β + 1) ≠ 0 := Complex.Gamma_ne_zero (not_neg_nat_of_re_pos (by
    simp only [Complex.add_re, Complex.one_re, Complex.natCast_re]
    linarith [(Nat.cast_nonneg (α := ℝ) n)]))
  rw [div_eq_iff hGA] at hA
  rw [div_eq_iff hGB] at hB
  have hzn : z ^ n = z ^ k * z ^ (n - k) := by rw [← pow_add, Nat.add_sub_cancel' hkn]
  have h2n : (2 : ℂ) ^ n = 2 ^ k * 2 ^ (n - k) := by rw [← pow_add, Nat.add_sub_cancel' hkn]
  rw [hA, hB, hzn, h2n]
  simp only [u, v, div_pow, mul_pow]
  field_simp

end DLMF.OrthogonalPolynomials
end
end
