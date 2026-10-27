/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Gamma.Integrals
public import DLMF.Gamma.Inequalities
public import DLMF.Hypergeometric.Saalschutz

/-!
# Barnes moments for continuous Hahn orthogonality

The proved four-Gamma Barnes integral evaluates mixed rising-factorial moments.
Pfaff–Saalschutz annihilates every reversed rising factorial of smaller degree.
All finite integral exchanges use absolute integrability, established from the
Mathlib integral API and the project's proved vertical Gamma bounds.
-/

@[expose] public section
open Complex MeasureTheory Filter
open scoped Real Nat
open DLMF.Hypergeometric
noncomputable section
namespace DLMF.OrthogonalPolynomials.HahnMoments

/-- The four-Gamma weight before imposing complex-conjugate parameter pairs. -/
def weight (a b c d : ℂ) (x : ℝ) : ℂ :=
  Gamma (a + I * x) * Gamma (b + I * x) * Gamma (c - I * x) * Gamma (d - I * x)

/-- Absolute integrability of the four-Gamma Barnes weight. -/
theorem integrable_weight {a b c d : ℂ}
    (ha : 0 < a.re) (hb : 0 < b.re) (hc : 0 < c.re) (hd : 0 < d.re) :
    Integrable (weight a b c d) := by
  have hbound (w : ℂ) (hw : 0 < w.re) (t : ℝ) :
      ‖Gamma (w + I * t)‖ ≤ |Real.Gamma w.re| := by
    have h := DLMF.Gamma.norm_Gamma_add_mul_I_le (x := w.re) (y := w.im + t) hw
    have he : (w.re : ℂ) + I * ((w.im + t : ℝ) : ℂ) = w + I * t := by
      apply Complex.ext <;> simp <;> ring
    rwa [he] at h
  have hpair := DLMF.Gamma.integrable_Gamma_add_mul_Gamma_sub ha hc
  apply Integrable.mono' (f := weight a b c d) (hpair.norm.const_mul (|Real.Gamma b.re| * |Real.Gamma d.re|))
    (Measurable.aestronglyMeasurable (by
      change Measurable (fun x : ℝ => Gamma (a + I * x) * Gamma (b + I * x) *
        Gamma (c - I * x) * Gamma (d - I * x))
      fun_prop))
  filter_upwards [] with x
  have h1 := hbound b hb x
  have h2 : ‖Gamma (d - I * x)‖ ≤ |Real.Gamma d.re| := by
    simpa only [ofReal_neg, mul_neg, sub_eq_add_neg] using hbound d hd (-x)
  have h3 := mul_le_mul h1 h2 (norm_nonneg _) (abs_nonneg _)
  simp only [weight, norm_mul]
  nlinarith [mul_le_mul_of_nonneg_left h3
    (mul_nonneg (norm_nonneg (Gamma (a + I * x))) (norm_nonneg (Gamma (c - I * x))))]

/-- Evaluation of the four-Gamma weight with the unnormalized Lebesgue measure. -/
theorem integral_weight {a b c d : ℂ}
    (ha : 0 < a.re) (hb : 0 < b.re) (hc : 0 < c.re) (hd : 0 < d.re) :
    (∫ x : ℝ, weight a b c d x) = 2 * Real.pi *
      (Gamma (a + c) * Gamma (a + d) * Gamma (b + c) * Gamma (b + d) /
        Gamma (a + b + c + d)) := by
  have h := DLMF.Gamma.mellin_barnes_four ha hb hc hd
  change (1 / (2 * Real.pi : ℂ)) * (∫ x : ℝ, weight a b c d x) = _ at h
  have hπ : (2 * Real.pi : ℂ) ≠ 0 := mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero)
  field_simp at h ⊢
  linear_combination h

/-- The mixed Pochhammer moment of a four-Gamma weight. -/
def moment (a b c d : ℂ) (k j : ℕ) : ℂ :=
  2 * Real.pi * (Gamma (a + c + k) * Gamma (a + d + j + k) * Gamma (b + c) *
    Gamma (b + d + j) / Gamma (a + b + c + d + j + k))

/-- Gamma's finite-shift formula at a point in the right half-plane. -/
theorem gamma_shift {w : ℂ} (hw : 0 < w.re) (k : ℕ) :
    Gamma (w + k) = poch w k * Gamma w := by
  exact (div_eq_iff (Gamma_ne_zero_of_re_pos hw)).mp
    (Gamma_add_nat_div_Gamma_eq (n := k) w (not_neg_nat_of_re_pos hw))

/-- Multiplying the weight by Pochhammer factors shifts its first and fourth Gamma parameters. -/
theorem poch_mul_weight {a b c d : ℂ} (ha : 0 < a.re) (hd : 0 < d.re) (k j : ℕ) (x : ℝ) :
    poch (a + I * x) k * poch (d - I * x) j * weight a b c d x =
      weight (a + k) b c (d + j) x := by
  dsimp only [weight]
  rw [show a + k + I * x = (a + I * x) + k by ring,
    show d + j - I * x = (d - I * x) + j by ring,
    gamma_shift (by simpa using ha), gamma_shift (by simpa using hd)]
  ring

/-- Absolute integrability and evaluation of every mixed Pochhammer moment. -/
theorem mixed_moment {a b c d : ℂ}
    (ha : 0 < a.re) (hb : 0 < b.re) (hc : 0 < c.re) (hd : 0 < d.re) (k j : ℕ) :
    Integrable (fun x : ℝ => poch (a + I * x) k * poch (d - I * x) j * weight a b c d x) ∧
      (∫ x : ℝ, poch (a + I * x) k * poch (d - I * x) j * weight a b c d x) = moment a b c d k j := by
  have hak : 0 < (a + k).re := by simp; positivity
  have hdj : 0 < (d + j).re := by simp; positivity
  refine ⟨(integrable_weight hak hb hc hdj).congr
    (Eventually.of_forall (fun x => (poch_mul_weight ha hd k j x).symm)), ?_⟩
  simp_rw [poch_mul_weight ha hd]
  rw [integral_weight hak hb hc hdj]
  unfold moment
  congr 1
  rw [show a + k + c = a + c + k by ring,
    show a + k + (d + j) = a + d + j + k by ring,
    show b + (d + j) = b + d + j by ring,
    show a + k + b + c + (d + j) = a + b + c + d + j + k by ring]

/-- Factor the mixed moment into its zeroth moment and two numerator Pochhammer factors. -/
theorem moment_factor {a b c d : ℂ}
    (ha : 0 < a.re) (hb : 0 < b.re) (hc : 0 < c.re) (hd : 0 < d.re) (k j : ℕ) :
    moment a b c d k j = moment a b c d 0 j *
      (poch (a + c) k * poch (a + d + j) k / poch (a + b + c + d + j) k) := by
  unfold moment
  simp only [Nat.cast_zero, add_zero]
  rw [gamma_shift (by simp; linarith : 0 < (a + c).re),
    gamma_shift (by simp; positivity : 0 < (a + d + j).re),
    gamma_shift (by simp; positivity : 0 < (a + b + c + d + j).re)]
  ring

/-- The unnormalized terminating continuous Hahn sum. -/
def hahnSum (a b c d : ℂ) (n : ℕ) (x : ℝ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1),
    (poch (-(n : ℂ)) k * poch (n + a + b + c + d - 1) k /
      (poch (a + c) k * poch (a + d) k * k.factorial)) * poch (a + I * x) k

/-- Every continuous Hahn sum times a reversed rising factorial has an absolutely integrable weight. -/
theorem integrable_hahnSum_basis {a b c d : ℂ}
    (ha : 0 < a.re) (hb : 0 < b.re) (hc : 0 < c.re) (hd : 0 < d.re) (n j : ℕ) :
    Integrable (fun x : ℝ => hahnSum a b c d n x * poch (d - I * x) j * weight a b c d x) := by
  simp only [hahnSum, Finset.sum_mul]
  apply integrable_finsetSum
  intro k hk
  simpa only [mul_assoc] using ((mixed_moment ha hb hc hd k j).1.const_mul
    (poch (-(n : ℂ)) k * poch (n + a + b + c + d - 1) k /
      (poch (a + c) k * poch (a + d) k * k.factorial)))

/-- Pfaff–Saalschutz makes every lower-degree reversed Pochhammer moment vanish. -/
theorem integral_hahnSum_basis_zero {a b c d : ℂ}
    (ha : 0 < a.re) (hb : 0 < b.re) (hc : 0 < c.re) (hd : 0 < d.re) {n j : ℕ} (hj : j < n) :
    (∫ x : ℝ, hahnSum a b c d n x * poch (d - I * x) j * weight a b c d x) = 0 := by
  have hA (k : ℕ) : poch (a + c) k ≠ 0 :=
    poch_ne_zero_of_not_neg_nat (not_neg_nat_of_re_pos (by simp; linarith)) k
  have hB : ∀ k : ℕ, a + d ≠ -k := not_neg_nat_of_re_pos (by simp; linarith)
  have hS (k : ℕ) : poch (a + b + c + d + j) k ≠ 0 :=
    poch_ne_zero_of_not_neg_nat (not_neg_nat_of_re_pos (by simp; positivity)) k
  have hterm (k : ℕ) :
      (∫ x : ℝ, (poch (-(n : ℂ)) k * poch (n + a + b + c + d - 1) k /
        (poch (a + c) k * poch (a + d) k * k.factorial)) *
          (poch (a + I * x) k * poch (d - I * x) j * weight a b c d x)) =
        moment a b c d 0 j * (poch (-(n : ℂ)) k * poch (n + a + b + c + d - 1) k *
          poch (a + d + j) k / (poch (a + d) k * poch (a + b + c + d + j) k * k.factorial)) := by
    rw [integral_const_mul, (mixed_moment ha hb hc hd k j).2, moment_factor ha hb hc hd]
    field_simp [hA k]
  have he : (fun x : ℝ => hahnSum a b c d n x * poch (d - I * x) j * weight a b c d x) =
      fun x : ℝ => ∑ k ∈ Finset.range (n + 1),
        (poch (-(n : ℂ)) k * poch (n + a + b + c + d - 1) k /
          (poch (a + c) k * poch (a + d) k * k.factorial)) *
          (poch (a + I * x) k * poch (d - I * x) j * weight a b c d x) := by
    funext x
    simp only [hahnSum, Finset.sum_mul, mul_assoc]
  rw [he, integral_finsetSum _ (fun k hk => ((mixed_moment ha hb hc hd k j).1.const_mul _))]
  simp_rw [hterm]
  rw [← Finset.mul_sum]
  have hbal : 1 + (n + a + b + c + d - 1) + (a + d + j) - (a + d) - n =
      a + b + c + d + j := by ring
  have hs := pfaff_saalschutz n (a := n + a + b + c + d - 1) (b := a + d + j) hB
    (by rw [hbal]; exact hS n)
  rw [hbal, show a + d - (a + d + j) = -(j : ℂ) by ring,
    poch_neg_nat_eq_zero hj, mul_zero, zero_div] at hs
  rw [hs, mul_zero]

/-- A rising factorial in the reversed variable is a finite combination of rising factorials. -/
theorem poch_reverse_basis (A v : ℂ) (k : ℕ) :
    poch (A - v) k = ∑ j ∈ Finset.range (k + 1),
      ((-1 : ℂ) ^ k * k.choose j * poch (-A - k + 1) (k - j)) * poch v j := by
  rw [show A - v = -(v - A) by ring, DLMF.Gamma.poch_neg_eq,
    show v - A - k + 1 = v + (-A - k + 1) by ring, poch_add_eq_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- A continuous Hahn sum annihilates the ordinary rising-factorial basis below its degree. -/
theorem hahnSum_same_basis_zero {a b c d : ℂ}
    (ha : 0 < a.re) (hb : 0 < b.re) (hc : 0 < c.re) (hd : 0 < d.re) {n k : ℕ} (hk : k < n) :
    Integrable (fun x : ℝ => hahnSum a b c d n x * poch (a + I * x) k * weight a b c d x) ∧
      (∫ x : ℝ, hahnSum a b c d n x * poch (a + I * x) k * weight a b c d x) = 0 := by
  let C (j : ℕ) : ℂ := (-1 : ℂ) ^ k * k.choose j * poch (-(a + d) - k + 1) (k - j)
  have he : (fun x : ℝ => hahnSum a b c d n x * poch (a + I * x) k * weight a b c d x) =
      fun x : ℝ => ∑ j ∈ Finset.range (k + 1),
        C j * (hahnSum a b c d n x * poch (d - I * x) j * weight a b c d x) := by
    funext x
    rw [show a + I * x = (a + d) - (d - I * x) by ring, poch_reverse_basis,
      Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    dsimp only [C]
    ring
  rw [he]
  have hi (j : ℕ) := (integrable_hahnSum_basis ha hb hc hd n j).const_mul (C j)
  refine ⟨integrable_finsetSum _ (fun j hj => hi j), ?_⟩
  rw [integral_finsetSum _ (fun j hj => hi j)]
  apply Finset.sum_eq_zero
  intro j hj
  rw [integral_const_mul, integral_hahnSum_basis_zero ha hb hc hd
    (lt_of_le_of_lt (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) hk), mul_zero]

/-- Ordered-degree continuous Hahn orthogonality, including absolute integrability. -/
theorem hahnSum_orthogonal_lt {a b c d : ℂ}
    (ha : 0 < a.re) (hb : 0 < b.re) (hc : 0 < c.re) (hd : 0 < d.re) {m n : ℕ} (hmn : m < n) :
    Integrable (fun x : ℝ => hahnSum a b c d m x * hahnSum a b c d n x * weight a b c d x) ∧
      (∫ x : ℝ, hahnSum a b c d m x * hahnSum a b c d n x * weight a b c d x) = 0 := by
  let C (k : ℕ) : ℂ := poch (-(m : ℂ)) k * poch (m + a + b + c + d - 1) k /
    (poch (a + c) k * poch (a + d) k * k.factorial)
  have he : (fun x : ℝ => hahnSum a b c d m x * hahnSum a b c d n x * weight a b c d x) =
      fun x : ℝ => ∑ k ∈ Finset.range (m + 1),
        C k * (hahnSum a b c d n x * poch (a + I * x) k * weight a b c d x) := by
    funext x
    change (∑ k ∈ Finset.range (m + 1), C k * poch (a + I * x) k) *
      hahnSum a b c d n x * weight a b c d x = _
    rw [Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  have hi (k : ℕ) (hk : k ∈ Finset.range (m + 1)) :=
    hahnSum_same_basis_zero ha hb hc hd
      (lt_of_le_of_lt (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)) hmn)
  rw [he]
  refine ⟨integrable_finsetSum _ (fun k hk => (hi k hk).1.const_mul (C k)), ?_⟩
  rw [integral_finsetSum _ (fun k hk => (hi k hk).1.const_mul (C k))]
  apply Finset.sum_eq_zero
  intro k hk
  rw [integral_const_mul, (hi k hk).2, mul_zero]

/-- Continuous Hahn bilinear orthogonality for arbitrary four right-half-plane parameters. -/
theorem hahnSum_orthogonal {a b c d : ℂ}
    (ha : 0 < a.re) (hb : 0 < b.re) (hc : 0 < c.re) (hd : 0 < d.re) {m n : ℕ} (hmn : m ≠ n) :
    (∫ x : ℝ, hahnSum a b c d m x * hahnSum a b c d n x * weight a b c d x) = 0 := by
  rcases lt_or_gt_of_ne hmn with h | h
  · exact (hahnSum_orthogonal_lt ha hb hc hd h).2
  · rw [show (fun x : ℝ => hahnSum a b c d m x * hahnSum a b c d n x * weight a b c d x) =
        fun x : ℝ => hahnSum a b c d n x * hahnSum a b c d m x * weight a b c d x by
      funext x; ring]
    exact (hahnSum_orthogonal_lt ha hb hc hd h).2

end DLMF.OrthogonalPolynomials.HahnMoments
