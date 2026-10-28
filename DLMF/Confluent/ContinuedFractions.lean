/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Confluent.Whittaker
public import Mathlib.Algebra.ContinuedFractions.Basic
public import DLMF.Confluent.Zeros
public import DLMFMathlib.Analysis.ContinuedFraction.Convergence

/-!
# Continued fractions (DLMF §§13.5, 13.17)

Partial numerators follow DLMF 13.5.2, 13.5.4, 13.17.2, and 13.17.4.
Convergence is acquired on a convenient real domain, matching the Chapter 15
restriction of meromorphic continued fractions.

Kummer's fraction 13.5.1 is proved for complex parameters
(`kummerM_continued_fraction_tendsto`) by Pincherle's theorem in the form
`GenContFract.cfConv_tendsto_of_ratio`: the backward solution
`M(a+m, b+2m, z)`, `M(a+m+1, b+2m+1, z)` comes from two contiguous relations
(`kumCF_contig_I`, `kumCF_contig_II`), it tends to `e^{z/2}`
(`kumCF_tendsto_exp_half`, dominated convergence), and the partial numerators tend to `0`.
`kummerM_continued_fraction_tendsto_of_ne` removes the conditions on the partial numerators by
attaching the head of the fraction through the Pincherle invariant
(`GenContFract.cfConv_tendsto_of_tail_invariant`).

The fraction 13.5.3 for `U(a,b,x)/U(a,b-1,x)` is proved for all real `a`, `b`, `x > 0` with
nonzero denominator (`kummerU_continued_fraction_tendsto_real`): the backward solution
`x^n U(a+n, b-1, x)`, `x^{n+1} U(a+n+1, b, x)` (`kumCF_UW`, contiguous relations 13.3.9–13.3.10)
is positive far out, where the fraction is a positive S-fraction with linearly growing elements
(`GenContFract.cfConv_tendsto_of_pos_linear`). Whittaker's fractions 13.17.1 and 13.17.3 follow,
with the denominators assumed nonzero.
-/

@[expose] public section

open Complex Filter
open scoped Real Topology Nat
open DLMF.Hypergeometric

noncomputable section

namespace DLMF.Confluent

/-- Coefficients `u_n` in DLMF 13.5.2. Stream index `k` is DLMF's `n = k+1`. -/
def kummerMContFractCoeff (a b : ℂ) (k : ℕ) : ℂ :=
  if (k + 1) % 2 = 1 then
    let m : ℂ := (k / 2 : ℕ)
    (a - b - m) / ((b + 2 * m) * (b + 2 * m + 1))
  else
    let m : ℂ := ((k + 1) / 2 : ℕ)
    (a + m) / ((b + 2 * m - 1) * (b + 2 * m))

/-- The continued fraction `1 + a₀z/(1 + a₁z/(1 + ⋯))` with the Kummer coefficients
`kummerMContFractCoeff a b k` (DLMF 13.5.1). -/
@[dlmf 13.5.E2]
def kummerMContinuedFraction (a b z : ℂ) : GenContFract ℂ where
  h := 1
  s := Stream'.Seq.ofStream fun k => ⟨kummerMContFractCoeff a b k * z, 1⟩

/-- Coefficients `v_n` in DLMF 13.5.4. -/
def kummerUContFractCoeff (a b : ℂ) (k : ℕ) : ℂ :=
  if (k + 1) % 2 = 1 then
    let m : ℂ := (k / 2 : ℕ)
    a + m
  else
    let m : ℂ := ((k + 1) / 2 : ℕ)
    a - b + m + 1

/-- The continued fraction `1 + u₀/z/(1 + u₁/z/(1 + ⋯))` with the Tricomi coefficients
`kummerUContFractCoeff a b k` (DLMF 13.5.2). -/
@[dlmf 13.5.E4]
def kummerUContinuedFraction (a b z : ℂ) : GenContFract ℂ where
  h := 1
  s := Stream'.Seq.ofStream fun k => ⟨kummerUContFractCoeff a b k / z, 1⟩

/-- Coefficient form of the contiguous relation `M(c,d) - M(c+1,d+1) = (c-d) z M(c+1,d+2) /
(d(d+1))`. -/
theorem kumCF_coeff_I {c d : ℂ} (hd : ∀ k : ℕ, d ≠ -k) (n : ℕ) :
    d * (d + 1) * (kummerMCoeff c d n - kummerMCoeff (c + 1) (d + 1) n) =
      (c - d) * (if n = 0 then 0 else kummerMCoeff (c + 1) (d + 2) (n - 1)) := by
  rcases n with _ | m
  · simp [kummerMCoeff, poch_zero]
  · simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel, kummerMCoeff]
    have hd0 : d ≠ 0 := by simpa using hd 0
    have hd1 : d + 1 ≠ 0 := by have := hd 1; intro h; apply this; push_cast; linear_combination h
    have hQ := poch_ne_zero_of_not_neg_nat (a := d + 2) (by
      intro k h; apply hd (k + 2); push_cast; linear_combination h) m
    have hdm : d + (m : ℂ) + 1 ≠ 0 := by
      intro h; apply hd (m + 1); push_cast; linear_combination h
    have e1 : poch c (m + 1) = c * poch (c + 1) m := poch_succ_left c m
    have e2 : poch (c + 1) (m + 1) = poch (c + 1) m * (c + 1 + m) := poch_succ _ m
    have e3 : poch (d + 1) (m + 1) = (d + 1) * poch (d + 2) m := by
      rw [poch_succ_left]; ring_nf
    have e4 : poch d (m + 1) * (d + m + 1) = d * ((d + 1) * poch (d + 2) m) := by
      rw [← e3, ← poch_succ_left d (m + 1), poch_succ d (m + 1)]; push_cast; ring
    have hpd : poch d (m + 1) ≠ 0 := by
      intro h; rw [h, zero_mul] at e4; exact (mul_ne_zero hd0 (mul_ne_zero hd1 hQ)) e4.symm
    have hf : ((m + 1)! : ℂ) ≠ 0 := by exact_mod_cast (m + 1).factorial_ne_zero
    have hf' : ((m)! : ℂ) ≠ 0 := by exact_mod_cast (m).factorial_ne_zero
    rw [e1, e2, e3, Nat.factorial_succ]
    have hpd' : poch d (m + 1) = d * ((d + 1) * poch (d + 2) m) / (d + m + 1) := by
      rw [← e4]; field_simp
    rw [hpd']
    push_cast
    field_simp
    ring

/-- Coefficient form of the contiguous relation `M(c,d) - M(c,d+1) = c z M(c+1,d+2) / (d(d+1))`. -/
theorem kumCF_coeff_II {c d : ℂ} (hd : ∀ k : ℕ, d ≠ -k) (n : ℕ) :
    d * (d + 1) * (kummerMCoeff c d n - kummerMCoeff c (d + 1) n) =
      c * (if n = 0 then 0 else kummerMCoeff (c + 1) (d + 2) (n - 1)) := by
  rcases n with _ | m
  · simp [kummerMCoeff, poch_zero]
  · simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel, kummerMCoeff]
    have hd0 : d ≠ 0 := by simpa using hd 0
    have hd1 : d + 1 ≠ 0 := by have := hd 1; intro h; apply this; push_cast; linear_combination h
    have hQ := poch_ne_zero_of_not_neg_nat (a := d + 2) (by
      intro k h; apply hd (k + 2); push_cast; linear_combination h) m
    have hdm : d + (m : ℂ) + 1 ≠ 0 := by
      intro h; apply hd (m + 1); push_cast; linear_combination h
    have e1 : poch c (m + 1) = c * poch (c + 1) m := poch_succ_left c m
    have e3 : poch (d + 1) (m + 1) = (d + 1) * poch (d + 2) m := by
      rw [poch_succ_left]; ring_nf
    have e4 : poch d (m + 1) * (d + m + 1) = d * ((d + 1) * poch (d + 2) m) := by
      rw [← e3, ← poch_succ_left d (m + 1), poch_succ d (m + 1)]; push_cast; ring
    have hf : ((m + 1)! : ℂ) ≠ 0 := by exact_mod_cast (m + 1).factorial_ne_zero
    have hf' : ((m)! : ℂ) ≠ 0 := by exact_mod_cast (m).factorial_ne_zero
    rw [e1, e3, Nat.factorial_succ]
    have hpd' : poch d (m + 1) = d * ((d + 1) * poch (d + 2) m) / (d + m + 1) := by
      rw [← e4]; field_simp
    rw [hpd']
    push_cast
    field_simp
    ring

/-- `(d+1)(M(1,d+1,z) - 1) = z M(1,d+2,z)`, valid also at `d = 0`. -/
theorem kumCF_one_sub {d : ℂ} (hd : ∀ k : ℕ, d + 1 ≠ -k) (z : ℂ) :
    (d + 1) * (kummerM 1 (d + 1) z - 1) = z * kummerM 1 (d + 2) z := by
  have hd2 : ∀ k : ℕ, d + 2 ≠ -k := by
    intro k h; apply hd (k + 1); push_cast; linear_combination h
  have h := ((hasSum_kummerM (a := 1) hd z).sub (hasSum_ite_eq 0 (1 : ℂ))).mul_left (d + 1)
  have h' := hasSum_z_mul_kummerM (a := 1) hd2 z
  refine h.unique ?_
  convert h' using 1
  funext n
  rcases n with _ | m
  · simp [kummerMCoeff, poch_zero]
  · simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel, kummerMCoeff, sub_zero,
      poch_nat_one]
    have hd0 : d + 1 ≠ 0 := by simpa using hd 0
    have hQ := poch_ne_zero_of_not_neg_nat hd2 m
    have e3 : poch (d + 1) (m + 1) = (d + 1) * poch (d + 2) m := by
      rw [poch_succ_left]; ring_nf
    have hf : ((m + 1)! : ℂ) ≠ 0 := by exact_mod_cast (m + 1).factorial_ne_zero
    have hf' : ((m)! : ℂ) ≠ 0 := by exact_mod_cast (m).factorial_ne_zero
    rw [e3]
    field_simp

/-- Contiguous relation `d(d+1)(M(c,d,z) - M(c+1,d+1,z)) = (c-d) z M(c+1,d+2,z)`. -/
theorem kumCF_contig_I {c d : ℂ} (hd : ∀ k : ℕ, d ≠ -k) (z : ℂ) :
    d * (d + 1) * (kummerM c d z - kummerM (c + 1) (d + 1) z) =
      (c - d) * (z * kummerM (c + 1) (d + 2) z) := by
  have hd1 : ∀ k : ℕ, d + 1 ≠ -k := by simpa using DLMF.Hypergeometric.not_neg_nat_add_nat hd 1
  have hd2 : ∀ k : ℕ, d + 2 ≠ -k := by simpa using DLMF.Hypergeometric.not_neg_nat_add_nat hd 2
  have h := ((hasSum_kummerM (a := c) hd z).sub (hasSum_kummerM (a := c + 1) hd1 z)).mul_left
    (d * (d + 1))
  have h' := (hasSum_z_mul_kummerM (a := c + 1) hd2 z).mul_left (c - d)
  refine h.unique ?_
  convert h' using 1
  funext n
  rw [← mul_sub_right_distrib, ← mul_assoc, kumCF_coeff_I hd n]
  ring

/-- Contiguous relation `d(d+1)(M(c,d,z) - M(c,d+1,z)) = c z M(c+1,d+2,z)`. -/
theorem kumCF_contig_II {c d : ℂ} (hd : ∀ k : ℕ, d ≠ -k) (z : ℂ) :
    d * (d + 1) * (kummerM c d z - kummerM c (d + 1) z) =
      c * (z * kummerM (c + 1) (d + 2) z) := by
  have hd1 : ∀ k : ℕ, d + 1 ≠ -k := by simpa using DLMF.Hypergeometric.not_neg_nat_add_nat hd 1
  have hd2 : ∀ k : ℕ, d + 2 ≠ -k := by simpa using DLMF.Hypergeometric.not_neg_nat_add_nat hd 2
  have h := ((hasSum_kummerM (a := c) hd z).sub (hasSum_kummerM (a := c) hd1 z)).mul_left
    (d * (d + 1))
  have h' := (hasSum_z_mul_kummerM (a := c + 1) hd2 z).mul_left c
  refine h.unique ?_
  convert h' using 1
  funext n
  rw [← mul_sub_right_distrib, ← mul_assoc, kumCF_coeff_II hd n]
  ring

/-- `(c + m + n)/(d + 2m + n) → 1/2` as `m → ∞`. -/
theorem kumCF_ratio_tendsto (c d : ℂ) (n : ℕ) :
    Tendsto (fun m : ℕ => (c + m + n) / (d + 2 * m + n)) atTop (𝓝 (1 / 2)) := by
  have h1 : Tendsto (fun m : ℕ => ((c + n) / (m : ℂ) + 1) / ((d + n) / (m : ℂ) + 2)) atTop
      (𝓝 ((0 + 1) / (0 + 2))) :=
    ((tendsto_const_div_atTop_nhds_zero_nat (c + n)).add_const 1).div
      ((tendsto_const_div_atTop_nhds_zero_nat (d + n)).add_const 2) (by norm_num)
  rw [show ((0 : ℂ) + 1) / (0 + 2) = 1 / 2 by norm_num] at h1
  refine h1.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with m hm
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [div_add_one hm', div_add' _ _ _ hm', div_div_div_cancel_right₀ hm']
  ring_nf

/-- `(c+m)_n / (d+2m)_n → 2^{-n}` as `m → ∞`. -/
theorem kumCF_poch_ratio_tendsto (c d : ℂ) (n : ℕ) :
    Tendsto (fun m : ℕ => poch (c + m) n / poch (d + 2 * m) n) atTop (𝓝 ((1 / 2) ^ n)) := by
  induction n with
  | zero => simp [poch_zero]
  | succ n ih =>
    have := ih.mul (kumCF_ratio_tendsto c d n)
    rw [← pow_succ] at this
    refine this.congr fun m => ?_
    rw [poch_succ, poch_succ, mul_div_mul_comm]

/-- If `|c| + |d| ≤ m`, then `|(c+m)_n| ≤ |(d+2m)_n|`. -/
theorem kumCF_norm_poch_le {c d : ℂ} {m : ℕ} (hm : ‖c‖ + ‖d‖ ≤ m) (n : ℕ) :
    ‖poch (c + m) n‖ ≤ ‖poch (d + 2 * m) n‖ := by
  induction n with
  | zero => simp [poch_zero]
  | succ n ih =>
    rw [poch_succ, poch_succ, norm_mul, norm_mul]
    refine mul_le_mul ih ?_ (norm_nonneg _) (norm_nonneg _)
    have e1 : ‖c + m + n‖ ≤ ‖c‖ + m + n := by
      refine (norm_add_le _ _).trans ?_
      refine add_le_add ((norm_add_le _ _).trans ?_) (by simp)
      simp
    have e2 : (2 * m + n : ℝ) - ‖d‖ ≤ ‖d + 2 * m + n‖ := by
      have := norm_sub_norm_le ((2 * m + n : ℂ)) (-d)
      rw [norm_neg, show (2 * m + n : ℂ) - -d = d + 2 * m + n by ring] at this
      have h2 : ‖(2 * m + n : ℂ)‖ = 2 * m + n := by
        rw [show (2 * m + n : ℂ) = ((2 * m + n : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
          Real.norm_of_nonneg (by positivity)]
      linarith
    linarith

/-- `M(c+m, d+2m, z) → e^{z/2}` as `m → ∞`. -/
theorem kumCF_tendsto_exp_half (c d z : ℂ) :
    Tendsto (fun m : ℕ => kummerM (c + m) (d + 2 * m) z) atTop (𝓝 (exp (z / 2))) := by
  have hexp : (∑' n : ℕ, (1 / 2 : ℂ) ^ n / n ! * z ^ n) = exp (z / 2) := by
    rw [Complex.exp_eq_exp_ℂ, ← (NormedSpace.expSeries_div_hasSum_exp (z / 2)).tsum_eq]
    congr 1; funext n; rw [div_pow, div_pow, one_pow]; ring
  rw [← hexp]
  unfold kummerM
  refine tendsto_tsum_of_dominated_convergence (bound := fun n => ‖z‖ ^ n / n !)
    (Real.summable_pow_div_factorial ‖z‖) (fun n => ?_) ?_
  · have := ((kumCF_poch_ratio_tendsto c d n).div_const (n ! : ℂ)).mul_const (z ^ n)
    refine this.congr fun m => ?_
    rw [div_div]
  · obtain ⟨M, hM⟩ := exists_nat_ge (‖c‖ + ‖d‖)
    filter_upwards [eventually_ge_atTop M] with m hm n
    have hcm : ‖c‖ + ‖d‖ ≤ m := hM.trans (by exact_mod_cast hm)
    rw [norm_mul, norm_div, norm_mul, norm_pow, ← div_div]
    have hf : (0 : ℝ) < ‖(n ! : ℂ)‖ := by
      rw [Complex.norm_natCast]; exact_mod_cast n.factorial_pos
    rw [Complex.norm_natCast]
    have hr : ‖poch (c + m) n‖ / ‖poch (d + 2 * m) n‖ ≤ 1 :=
      div_le_one_of_le₀ (kumCF_norm_poch_le hcm n) (norm_nonneg _)
    rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right (by exact_mod_cast n.factorial_pos)]
    calc ‖poch (c + m) n‖ / ‖poch (d + 2 * m) n‖ * ‖z‖ ^ n ≤ 1 * ‖z‖ ^ n := by gcongr
      _ = _ := one_mul _

/-- `1/(d + 2m + n) → 0` as `m → ∞`. -/
theorem kumCF_recip_tendsto (d : ℂ) (n : ℕ) :
    Tendsto (fun m : ℕ => 1 / (d + 2 * m + n)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun m : ℕ => (1 / (m : ℂ)) / ((d + n) / (m : ℂ) + 2)) atTop
      (𝓝 (0 / (0 + 2))) :=
    (tendsto_const_div_atTop_nhds_zero_nat 1).div
      ((tendsto_const_div_atTop_nhds_zero_nat (d + n)).add_const 2) (by norm_num)
  rw [zero_div] at h1
  refine h1.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with m hm
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [div_add' _ _ _ hm', div_div_div_cancel_right₀ hm']
  ring_nf

/-- A property holding eventually along even and along odd indices holds eventually. -/
theorem kumCF_eventually_of_even_odd {P : ℕ → Prop} (he : ∀ᶠ m in atTop, P (2 * m))
    (ho : ∀ᶠ m in atTop, P (2 * m + 1)) : ∀ᶠ j in atTop, P j := by
  obtain ⟨M1, h1⟩ := eventually_atTop.mp he
  obtain ⟨M2, h2⟩ := eventually_atTop.mp ho
  refine eventually_atTop.mpr ⟨2 * (M1 + M2), fun j hj => ?_⟩
  rcases Nat.even_or_odd' j with ⟨m, rfl | rfl⟩
  · exact h1 m (by omega)
  · exact h2 m (by omega)

/-- The backward solution `F_{2m} = M(a+m, b+2m)`, `F_{2m+1} = M(a+m+1, b+2m+1)`. -/
def kumCF_F (a b z : ℂ) (j : ℕ) : ℂ := kummerM (a + ((j + 1) / 2 : ℕ)) (b + j) z

/-- The even-indexed Kummer function in the continued-fraction chain is `M(a+m, b+2m, z)`. -/
theorem kumCF_F_even (a b z : ℂ) (m : ℕ) :
    kumCF_F a b z (2 * m) = kummerM (a + m) (b + 2 * m) z := by
  simp only [kumCF_F, show (2 * m + 1) / 2 = m by omega]; push_cast; rfl

/-- The odd-indexed Kummer function in the continued-fraction chain is `M(a+1+m, b+1+2m, z)`. -/
theorem kumCF_F_odd (a b z : ℂ) (m : ℕ) :
    kumCF_F a b z (2 * m + 1) = kummerM (a + 1 + m) (b + 1 + 2 * m) z := by
  simp only [kumCF_F, show (2 * m + 1 + 1) / 2 = m + 1 by omega]; push_cast; ring_nf

/-- The even Kummer continued-fraction coefficient is `(a-b-m)/((b+2m)(b+2m+1))`. -/
theorem kumCF_coeff_even (a b : ℂ) (m : ℕ) :
    kummerMContFractCoeff a b (2 * m) = (a - b - m) / ((b + 2 * m) * (b + 2 * m + 1)) := by
  simp only [kummerMContFractCoeff, show (2 * m + 1) % 2 = 1 by omega, ↓reduceIte,
    show 2 * m / 2 = m by omega]

/-- The odd Kummer continued-fraction coefficient is `(a+1+m)/((b+1+2m)(b+2m+2))`. -/
theorem kumCF_coeff_odd (a b : ℂ) (m : ℕ) :
    kummerMContFractCoeff a b (2 * m + 1) =
      (a + 1 + m) / ((b + 1 + 2 * m) * (b + 1 + 2 * m + 1)) := by
  have h : ¬ ((2 * m + 1 + 1) % 2 = 1) := by omega
  simp only [kummerMContFractCoeff, h, ↓reduceIte, show (2 * m + 1 + 1) / 2 = m + 1 by omega]
  push_cast; ring_nf

/-- The contiguous relation `M(c,d,z) = M(c+1,d+1,z) + (c-d) z M(c+1,d+2,z)/(d(d+1))`. -/
theorem kumCF_rel_I {c d : ℂ} (hd : ∀ k : ℕ, d ≠ -k) (z : ℂ) :
    kummerM c d z = kummerM (c + 1) (d + 1) z +
      (c - d) / (d * (d + 1)) * z * kummerM (c + 1) (d + 2) z := by
  have h := kumCF_contig_I (c := c) hd z
  have h1 : d ≠ 0 := by simpa using hd 0
  have h2 : d + 1 ≠ 0 := by
    have := hd 1; intro h; apply this; push_cast; linear_combination h
  field_simp
  linear_combination h

/-- The contiguous relation `M(c,d,z) = M(c,d+1,z) + c z M(c+1,d+2,z)/(d(d+1))`. -/
theorem kumCF_rel_II {c d : ℂ} (hd : ∀ k : ℕ, d ≠ -k) (z : ℂ) :
    kummerM c d z = kummerM c (d + 1) z +
      c / (d * (d + 1)) * z * kummerM (c + 1) (d + 2) z := by
  have h := kumCF_contig_II (c := c) hd z
  have h1 : d ≠ 0 := by simpa using hd 0
  have h2 : d + 1 ≠ 0 := by
    have := hd 1; intro h; apply this; push_cast; linear_combination h
  field_simp
  linear_combination h

/-- The three-term relation `F_j = F_{j+1} + u_{j+1} z F_{j+2}`. -/
theorem kumCF_F_rec' {a b : ℂ} (z : ℂ) (j : ℕ) (hbj : ∀ k : ℕ, b + j ≠ -k) :
    kumCF_F a b z j = kumCF_F a b z (j + 1) +
      kummerMContFractCoeff a b j * z * kumCF_F a b z (j + 2) := by
  rcases Nat.even_or_odd' j with ⟨m, rfl | rfl⟩
  · have hd := hbj
    push_cast at hd
    have e := kumCF_rel_I (c := a + m) hd z
    rw [kumCF_F_even, kumCF_F_odd, show 2 * m + 2 = 2 * (m + 1) by ring, kumCF_F_even,
      kumCF_coeff_even]
    push_cast at e ⊢; ring_nf at e ⊢; linear_combination e
  · have hd := hbj
    push_cast at hd
    have e := kumCF_rel_II (c := a + 1 + m) hd z
    rw [kumCF_F_odd, show 2 * m + 1 + 1 = 2 * (m + 1) by ring, kumCF_F_even,
      show 2 * m + 1 + 2 = 2 * (m + 1) + 1 by ring, kumCF_F_odd, kumCF_coeff_odd]
    push_cast at e ⊢; ring_nf at e ⊢; linear_combination e

/-- The three-term relation for all indices when `b` is not a nonpositive integer. -/
theorem kumCF_F_rec {a b : ℂ} (hb : ∀ k : ℕ, b ≠ -k) (z : ℂ) (j : ℕ) :
    kumCF_F a b z j = kumCF_F a b z (j + 1) +
      kummerMContFractCoeff a b j * z * kumCF_F a b z (j + 2) :=
  kumCF_F_rec' z j (DLMF.Hypergeometric.not_neg_nat_add_nat hb j)

/-- The even and odd Kummer continued-fraction coefficients tend to `0`. -/
theorem kumCF_coeff_tendsto (a b : ℂ) :
    Tendsto (fun m : ℕ => kummerMContFractCoeff a b (2 * m)) atTop (𝓝 0) ∧
      Tendsto (fun m : ℕ => kummerMContFractCoeff a b (2 * m + 1)) atTop (𝓝 0) := by
  constructor
  · have := ((kumCF_ratio_tendsto (-(a - b)) b 0).neg).mul (kumCF_recip_tendsto b 1)
    rw [mul_zero] at this
    refine this.congr fun m => ?_
    rw [kumCF_coeff_even]; simp only [div_eq_mul_inv, mul_inv]; push_cast; ring
  · have := (kumCF_ratio_tendsto (a + 1) (b + 1) 0).mul (kumCF_recip_tendsto (b + 1) 1)
    rw [mul_zero] at this
    refine this.congr fun m => ?_
    rw [kumCF_coeff_odd]; simp only [div_eq_mul_inv, mul_inv]; push_cast; ring

/-- Under the stated nondegeneracy conditions, every Kummer continued-fraction coefficient is
nonzero. -/
theorem kumCF_coeff_ne_zero {a b : ℂ} (hb : ∀ k : ℕ, b ≠ -k) (ha1 : ∀ m : ℕ, a + 1 + m ≠ 0)
    (hab : ∀ m : ℕ, a - b - m ≠ 0) (j : ℕ) : kummerMContFractCoeff a b j ≠ 0 := by
  have hb' : ∀ n : ℕ, b + n ≠ 0 := fun n h => hb n (by linear_combination h)
  rcases Nat.even_or_odd' j with ⟨m, rfl | rfl⟩
  · rw [kumCF_coeff_even]
    refine div_ne_zero (hab m) (mul_ne_zero ?_ ?_)
    · simpa using hb' (2 * m)
    · simpa [add_assoc] using hb' (2 * m + 1)
  · rw [kumCF_coeff_odd]
    refine div_ne_zero (ha1 m) (mul_ne_zero ?_ ?_)
    · have := hb' (2 * m + 1); push_cast at this; intro h; apply this; linear_combination h
    · have := hb' (2 * m + 2); push_cast at this; intro h; apply this; linear_combination h

/-- Eventually `F_j ≠ 0` and `3 ‖u_{j+1} z F_{j+2}‖ ≤ ‖F_j‖`: the tails of Kummer's fraction
are small. -/
theorem kumCF_eventually_ratio (a b z : ℂ) :
    ∀ᶠ j in atTop, kumCF_F a b z j ≠ 0 ∧
      3 * ‖kummerMContFractCoeff a b j * z * kumCF_F a b z (j + 2)‖ ≤ ‖kumCF_F a b z j‖ := by
  set F := kumCF_F a b z with hFdef
  set E := exp (z / 2)
  have hE : 0 < ‖E‖ := norm_pos_iff.mpr (exp_ne_zero _)
  have hFe : Tendsto (fun m : ℕ => F (2 * m)) atTop (𝓝 E) := by
    simpa [F, kumCF_F_even] using kumCF_tendsto_exp_half a b z
  have hFo : Tendsto (fun m : ℕ => F (2 * m + 1)) atTop (𝓝 E) := by
    simpa [F, kumCF_F_odd] using kumCF_tendsto_exp_half (a + 1) (b + 1) z
  have hball : ∀ᶠ j in atTop, ‖F j - E‖ < ‖E‖ / 2 :=
    kumCF_eventually_of_even_odd
      ((tendsto_iff_norm_sub_tendsto_zero.mp hFe).eventually (gt_mem_nhds (half_pos hE)))
      ((tendsto_iff_norm_sub_tendsto_zero.mp hFo).eventually (gt_mem_nhds (half_pos hE)))
  have hc9 : (0 : ℝ) < 1 / (9 * (‖z‖ + 1)) := by positivity
  have hcoef : ∀ᶠ j in atTop, ‖kummerMContFractCoeff a b j‖ < 1 / (9 * (‖z‖ + 1)) :=
    kumCF_eventually_of_even_odd
      ((kumCF_coeff_tendsto a b).1.norm.eventually (gt_mem_nhds (by simpa using hc9)))
      ((kumCF_coeff_tendsto a b).2.norm.eventually (gt_mem_nhds (by simpa using hc9)))
  have hlow : ∀ j, ‖F j - E‖ < ‖E‖ / 2 → ‖E‖ / 2 < ‖F j‖ := by
    intro j hj
    have := norm_sub_norm_le E (E - F j)
    rw [sub_sub_cancel, norm_sub_rev] at this
    linarith
  have hup : ∀ j, ‖F j - E‖ < ‖E‖ / 2 → ‖F j‖ ≤ 3 * ‖E‖ / 2 := by
    intro j hj
    linarith [norm_sub_norm_le (F j) E]
  filter_upwards [hball, hcoef, (tendsto_add_atTop_nat 2).eventually hball] with j h1 h2 h3
  refine ⟨fun h => by have := hlow j h1; rw [h, norm_zero] at this; linarith, ?_⟩
  rw [norm_mul, norm_mul]
  have h4 : ‖kummerMContFractCoeff a b j‖ * ‖z‖ ≤ 1 / 9 := by
    have hz1 : ‖z‖ ≤ ‖z‖ + 1 := by linarith
    calc ‖kummerMContFractCoeff a b j‖ * ‖z‖ ≤ 1 / (9 * (‖z‖ + 1)) * (‖z‖ + 1) :=
          mul_le_mul h2.le hz1 (norm_nonneg _) hc9.le
      _ = 1 / 9 := by field_simp
  have h5 := hup (j + 2) h3
  calc 3 * (‖kummerMContFractCoeff a b j‖ * ‖z‖ * ‖F (j + 2)‖)
      ≤ 3 * (1 / 9 * (3 * ‖E‖ / 2)) := by gcongr
    _ = ‖E‖ / 2 := by ring
    _ ≤ ‖F j‖ := (hlow j h1).le

/-- **Kummer's continued fraction** (DLMF 13.5.1) for complex parameters: if `b` is not a
nonpositive integer, `a ≠ -1, -2, …`, `a - b ≠ 0, 1, 2, …`, `z ≠ 0` and
`M(a+1,b+1,z) ≠ 0`, the convergents of `1 + u₁z/(1 + u₂z/(1 + ⋯))` tend to
`M(a,b,z)/M(a+1,b+1,z)`. -/
@[dlmf 13.5.E1]
theorem kummerM_continued_fraction_tendsto {a b z : ℂ} (hb : ∀ k : ℕ, b ≠ -k) (hz : z ≠ 0)
    (ha1 : ∀ m : ℕ, a + 1 + m ≠ 0) (hab : ∀ m : ℕ, a - b - m ≠ 0)
    (hM : kummerM (a + 1) (b + 1) z ≠ 0) :
    Tendsto (kummerMContinuedFraction a b z).convs atTop
      (𝓝 (kummerM a b z / kummerM (a + 1) (b + 1) z)) := by
  set F := kumCF_F a b z with hFdef
  obtain ⟨N, hN⟩ := eventually_atTop.mp (kumCF_eventually_ratio a b z)
  have hw : ∀ k, F (k + 1) = (fun _ => (1 : ℂ)) k * F (k + 1 + 1) +
      (fun k => kummerMContFractCoeff a b k * z) (k + 1) * F (k + 1 + 2) := by
    intro k
    have := kumCF_F_rec (a := a) hb z (k + 1)
    simp only [one_mul]
    exact this
  have hw0 : F (0 + 1) ≠ 0 := by
    have := kumCF_F_odd a b z 0
    simp only [mul_zero, zero_add, Nat.cast_zero, add_zero] at this
    show kumCF_F a b z 1 ≠ 0
    rw [this]; exact hM
  have ha : ∀ k, (fun k => kummerMContFractCoeff a b k * z) k ≠ 0 :=
    fun k => mul_ne_zero (kumCF_coeff_ne_zero hb ha1 hab k) hz
  have hwN : ∀ k ≥ N, F (k + 1) ≠ 0 := fun k hk => (hN (k + 1) (by omega)).1
  have hrat : ∀ k ≥ N, (3 : ℝ) * ‖(fun k => kummerMContFractCoeff a b k * z) (k + 1) *
      F (k + 2 + 1)‖ ≤ ‖F (k + 1)‖ := by
    intro k hk
    have := (hN (k + 1) (by omega)).2
    simpa [show k + 1 + 2 = k + 2 + 1 by ring, mul_assoc] using this
  have key := GenContFract.cfConv_tendsto_of_ratio (h := (1 : ℂ))
    (a := fun k => kummerMContFractCoeff a b k * z) (b := fun _ => (1 : ℂ))
    (w := fun k => F (k + 1)) hw hw0 ha (N := N) hwN (q := 3) (by norm_num) hrat
  have hval : (1 : ℂ) + kummerMContFractCoeff a b 0 * z * F (1 + 1) / F (0 + 1) =
      kummerM a b z / kummerM (a + 1) (b + 1) z := by
    have h0 : F 0 = F (0 + 1) + kummerMContFractCoeff a b 0 * z * F (1 + 1) :=
      kumCF_F_rec (a := a) hb z 0
    have e0 : F 0 = kummerM a b z := by simpa [F] using kumCF_F_even a b z 0
    have e1 : F (0 + 1) = kummerM (a + 1) (b + 1) z := by simpa [F] using kumCF_F_odd a b z 0
    rw [← e0, ← e1, h0]
    field_simp
  rw [← hval]
  exact key

/-- The map `(kummerMContinuedFraction a b x).convs` tends to `(𝓝 (kummerM a b x / kummerM (a + 1)
(b + 1) x))` along `atTop`. -/
@[dlmf 13.5.E1]
theorem kummerM_continued_fraction_limit {a b x : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hba : a < b) (hx : 0 < x) (hx1 : x < 1) :
    Tendsto (kummerMContinuedFraction a b x).convs atTop
      (𝓝 (kummerM a b x / kummerM (a + 1) (b + 1) x)) := by
  refine kummerM_continued_fraction_tendsto (fun k h => ?_) (ofReal_ne_zero.mpr hx.ne')
    (fun m h => ?_) (fun m h => ?_) ?_
  · have := congrArg Complex.re h; simp at this; linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
  · have := congrArg Complex.re h; simp at this; linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)]
  · have := congrArg Complex.re h; simp at this; linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)]
  · intro h
    have hp := kummerM_re_pos_of_nonneg (a := a + 1) (b := b + 1) (by linarith) (by linarith) hx
    push_cast at hp
    rw [h, zero_re] at hp
    exact lt_irrefl _ hp

/-- Tricomi's function is real and positive for real `c > 0` and `x > 0` (Laplace integral
DLMF 13.4.4 with a positive integrand). -/
theorem kumCF_U_real_pos {c d x : ℝ} (hc : 0 < c) (hx : 0 < x) :
    ∃ r : ℝ, 0 < r ∧ kummerU c d x = r := by
  have hl := kummerU_laplace (a := (c : ℂ)) (b := d) (z := x) (by simpa using hc)
    (by simpa using hx)
  let g : ℝ → ℝ := fun t => Real.exp (-x * t) * t ^ (c - 1) * (1 + t) ^ (d - c - 1)
  have hfg : ∀ t ∈ Set.Ioi (0 : ℝ),
      exp (-(x : ℂ) * t) * (t : ℂ) ^ ((c : ℂ) - 1) * (1 + (t : ℂ)) ^ ((d : ℂ) - c - 1) =
        (g t : ℂ) := by
    intro t ht
    have ht0 : (0 : ℝ) ≤ t := le_of_lt ht
    have ht1 : (0 : ℝ) ≤ 1 + t := by linarith
    simp only [g, ofReal_mul, ofReal_exp, ofReal_cpow ht0, ofReal_cpow ht1]
    push_cast
    ring_nf
  have hgpos : ∀ t ∈ Set.Ioi (0 : ℝ), 0 < g t := by
    intro t ht
    have ht' : (0 : ℝ) < t := ht
    have : 0 < 1 + t := by linarith
    positivity
  have hgi : MeasureTheory.IntegrableOn g (Set.Ioi 0) := by
    refine MeasureTheory.IntegrableOn.congr_fun
      (kummerU_laplace_integrable (a := (c : ℂ)) (b := d) (z := x)
        (by simpa using hc) (by simpa using hx)).norm (fun t ht => ?_) measurableSet_Ioi
    rw [hfg t ht, norm_real, Real.norm_of_nonneg (hgpos t ht).le]
  have hpos : 0 < ∫ t in Set.Ioi 0, g t := by
    rw [MeasureTheory.setIntegral_pos_iff_support_of_nonneg_ae
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => (hgpos t ht).le) hgi]
    have hsup : Function.support g ∩ Set.Ioi 0 = Set.Ioi 0 := by
      ext t
      simp only [Set.mem_inter_iff, Function.mem_support, and_iff_right_iff_imp]
      exact fun ht => (hgpos t ht).ne'
    rw [hsup, Real.volume_Ioi]
    exact ENNReal.zero_lt_top
  have hI : (∫ t : ℝ in Set.Ioi 0,
      exp (-(x : ℂ) * t) * (t : ℂ) ^ ((c : ℂ) - 1) * (1 + (t : ℂ)) ^ ((d : ℂ) - c - 1)) =
      ((∫ t in Set.Ioi 0, g t : ℝ) : ℂ) := by
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hfg, integral_complex_ofReal]
  refine ⟨(Real.Gamma c)⁻¹ * ∫ t in Set.Ioi 0, g t,
    mul_pos (inv_pos.mpr (Real.Gamma_pos_of_pos hc)) hpos, ?_⟩
  rw [hl, hI, Complex.Gamma_ofReal]
  push_cast
  ring

/-- The backward solution of the recurrence behind DLMF 13.5.3:
`w_{2n} = z^n U(a+n, b-1, z)` and `w_{2n+1} = z^{n+1} U(a+n+1, b, z)`. -/
def kumCF_UW (a b z : ℂ) (k : ℕ) : ℂ :=
  if k % 2 = 0 then z ^ (k / 2) * kummerU (a + ((k / 2 : ℕ) : ℂ)) (b - 1) z
  else z ^ ((k + 1) / 2) * kummerU (a + (((k + 1) / 2 : ℕ) : ℂ)) b z

/-- The recurrence `w_k = w_{k+1} + (u_{k+2}/z) w_{k+2}` for `kumCF_UW`, from the contiguous
relations DLMF 13.3.9 and 13.3.10. -/
theorem kumCF_UW_rec (a b : ℂ) {z : ℂ} (hz : z ≠ 0) (k : ℕ) :
    kumCF_UW a b z k = kumCF_UW a b z (k + 1) +
      kummerUContFractCoeff a b (k + 1) / z * kumCF_UW a b z (k + 2) := by
  rcases Nat.even_or_odd' k with ⟨n, rfl | rfl⟩
  · have h := kummerU_contiguous_shift_a (a + ((n + 1 : ℕ) : ℂ)) (b - 1) z hz
    rw [show a + ((n + 1 : ℕ) : ℂ) - 1 = a + (n : ℂ) by push_cast; ring, sub_add_cancel] at h
    simp only [kumCF_UW, kummerUContFractCoeff, show (2 * n) % 2 = 0 by omega,
      show ¬ ((2 * n + 1) % 2 = 0) by omega, show (2 * n + 2) % 2 = 0 by omega,
      show ¬ ((2 * n + 1 + 1) % 2 = 1) by omega, show (2 * n) / 2 = n by omega,
      show (2 * n + 1 + 1) / 2 = n + 1 by omega, show (2 * n + 2) / 2 = n + 1 by omega,
      ↓reduceIte]
    simp only [zero_ne_one, ↓reduceIte]
    have key : ∀ c u : ℂ, c / z * (z ^ (n + 1) * u) = z ^ n * (c * u) := fun c u => by
      rw [pow_succ]; field_simp
    rw [key, pow_succ]
    linear_combination (z ^ n) * h
  · have h := kummerU_contiguous_a_b (a + ((n + 1 : ℕ) : ℂ)) b z hz
    rw [show a + ((n + 1 : ℕ) : ℂ) + 1 = a + ((n + 2 : ℕ) : ℂ) by push_cast; ring] at h
    simp only [kumCF_UW, kummerUContFractCoeff, show ¬ ((2 * n + 1) % 2 = 0) by omega,
      show (2 * n + 1 + 1) % 2 = 0 by omega, show ¬ ((2 * n + 1 + 2) % 2 = 0) by omega,
      show (2 * n + 1 + 1 + 1) % 2 = 1 by omega, show (2 * n + 1 + 1) / 2 = n + 1 by omega,
      show (2 * n + 1 + 2 + 1) / 2 = n + 2 by omega, ↓reduceIte]
    simp only [one_ne_zero, ↓reduceIte]
    have key : ∀ c u : ℂ, c / z * (z ^ (n + 2) * u) = z ^ (n + 1) * (c * u) := fun c u => by
      rw [show n + 2 = n + 1 + 1 by ring, pow_succ (n := n + 1)]; field_simp
    rw [key]
    linear_combination (z ^ (n + 1)) * h

/-- The map `(kummerUContinuedFraction a b x).convs` tends to `(𝓝 (kummerU a b x / kummerU a (b -
1) x))` along `atTop`. -/
@[dlmf 13.5.E3]
theorem kummerU_continued_fraction_limit {a b x : ℝ} (ha : 0 < a) (hb : 1 < b)
    (hx : 0 < x) :
    Tendsto (kummerUContinuedFraction a b x).convs atTop
      (𝓝 (kummerU a b x / kummerU a (b - 1) x)) := by
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  set W := kumCF_UW (a : ℂ) (b : ℂ) (x : ℂ) with hW
  have hWr : ∀ k, ∃ r : ℝ, 0 < r ∧ W k = r := by
    intro k
    simp only [W, kumCF_UW]
    split_ifs
    · obtain ⟨r, hr, e⟩ := kumCF_U_real_pos (c := a + ((k / 2 : ℕ) : ℝ)) (d := b - 1) (x := x)
        (by positivity) hx
      refine ⟨x ^ (k / 2) * r, by positivity, ?_⟩
      rw [show (a : ℂ) + ((k / 2 : ℕ) : ℂ) = ((a + ((k / 2 : ℕ) : ℝ) : ℝ) : ℂ) by push_cast; ring,
        show (b : ℂ) - 1 = ((b - 1 : ℝ) : ℂ) by push_cast; ring, e]
      push_cast; ring
    · obtain ⟨r, hr, e⟩ := kumCF_U_real_pos (c := a + (((k + 1) / 2 : ℕ) : ℝ)) (d := b)
        (x := x) (by positivity) hx
      refine ⟨x ^ ((k + 1) / 2) * r, by positivity, ?_⟩
      rw [show (a : ℂ) + (((k + 1) / 2 : ℕ) : ℂ) = ((a + (((k + 1) / 2 : ℕ) : ℝ) : ℝ) : ℂ) by
        push_cast; ring, e]
      push_cast; ring
  choose wR hwpos hwR using hWr
  set cR : ℕ → ℝ := fun k => if (k + 1) % 2 = 1 then a + ((k / 2 : ℕ) : ℝ)
    else a - b + (((k + 1) / 2 : ℕ) : ℝ) + 1 with hcRdef
  have hcR : ∀ k, kummerUContFractCoeff a b k = (cR k : ℂ) := by
    intro k
    simp only [kummerUContFractCoeff, cR]
    split_ifs <;> push_cast <;> ring
  set aR : ℕ → ℝ := fun k => cR k / x with haRdef
  have hrecR : ∀ k, wR k = 1 * wR (k + 1) + aR (k + 1) * wR (k + 2) := by
    intro k
    have := kumCF_UW_rec (a : ℂ) (b : ℂ) hx0 k
    rw [← hW, hwR k, hwR (k + 1), hwR (k + 2), hcR] at this
    simp only [aR, one_mul]
    exact_mod_cast this
  obtain ⟨K, hK⟩ := exists_nat_gt (b - a)
  have hpos : ∀ k, 0 < aR (k + 2 * K) := by
    intro k
    simp only [aR, cR]
    refine div_pos ?_ hx
    split_ifs with h
    · have : (0 : ℝ) ≤ (((k + 2 * K) / 2 : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith
    · have : (K : ℝ) ≤ (((k + 2 * K + 1) / 2 : ℕ) : ℝ) := by
        exact_mod_cast (by omega : K ≤ (k + 2 * K + 1) / 2)
      linarith
  set M : ℝ := |a| + |b| + 2 with hM
  have hM1 : 1 ≤ M := by have := abs_nonneg a; have := abs_nonneg b; linarith
  have hcle : ∀ j : ℕ, cR j ≤ M + j := by
    intro j
    simp only [cR]
    have h1 := le_abs_self a
    have h2 := neg_abs_le b
    have h3 := abs_nonneg a
    have h4 := abs_nonneg b
    split_ifs
    · have : (((j / 2 : ℕ) : ℝ)) ≤ j := by exact_mod_cast Nat.div_le_self j 2
      linarith
    · have : (((j + 1) / 2 : ℕ) : ℝ) ≤ j + 1 := by
        exact_mod_cast (by omega : (j + 1) / 2 ≤ j + 1)
      linarith
  have hlin : ∀ k, aR (k + 2 * K) ≤ (M * (2 * K + 1) / x) * (k + 1) := by
    intro k
    simp only [aR]
    rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hx]
    have := hcle (k + 2 * K)
    push_cast at this
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
    nlinarith [mul_nonneg (sub_nonneg.2 hM1) (by positivity : (0 : ℝ) ≤ 2 * K + k),
      mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ M) hK0) hk]
  have ht := GenContFract.cfConv_tendsto_of_pos_linear (h := (0 : ℝ))
    (a := fun k => aR (k + 2 * K)) (w := fun k => wR (k + 2 * K)) hpos (fun k => hwpos _)
    (fun k => by
      have := hrecR (k + 2 * K)
      simpa [show k + 2 * K + 1 = k + 1 + 2 * K by ring,
        show k + 2 * K + 2 = k + 2 + 2 * K by ring] using this) hlin
  have hD : ∀ᶠ N in atTop, (GenContFract.cfConv_ofFun 0 (fun k => aR (k + 2 * K))
      (fun k => (fun _ => (1 : ℝ)) (k + 2 * K))).dens N ≠ 0 :=
    Eventually.of_forall fun N =>
      (GenContFract.cfConv_dens_pos hpos (fun _ => one_pos) N).ne'
  obtain ⟨hfull, hDfull⟩ := GenContFract.cfConv_tendsto_of_tail (a := aR)
    (b := fun _ => (1 : ℝ)) (w := wR) hrecR (fun k => (hwpos k).ne') (2 * K) hD (by
      convert ht using 2
      simp [add_comm])
  have hR1 : Tendsto (GenContFract.cfConv_ofFun 1 aR (fun _ => (1 : ℝ))).convs atTop
      (𝓝 (1 + aR 0 * wR 1 / wR 0)) := by
    refine (hfull.const_add 1).congr' ?_
    filter_upwards [hDfull] with N hN
    exact (GenContFract.cfConv_convs_eq 1 aR (fun _ => 1) N hN).symm
  have hC : ∀ n, (kummerUContinuedFraction a b x).convs n =
      ((GenContFract.cfConv_ofFun 1 aR (fun _ => (1 : ℝ))).convs n : ℂ) := by
    intro n
    have := GenContFract.cfConv_convs_map (h := (1 : ℝ)) (a := aR) (b := fun _ => (1 : ℝ))
      Complex.ofRealHom n
    simp only [Complex.ofRealHom_eq_coe, ofReal_one] at this
    rw [← this]
    show (GenContFract.cfConv_ofFun 1 (fun k => kummerUContFractCoeff a b k / x)
      (fun _ => 1)).convs n = _
    congr 2
    funext k
    simp [aR, hcR]
  show Tendsto (fun n => (kummerUContinuedFraction a b x).convs n) atTop _
  simp_rw [hC]
  have hU := kummerU_contiguous_a_b (a : ℂ) b x hx0
  have e0 : (wR 0 : ℂ) = kummerU a (b - 1) x := by
    rw [← hwR 0]; simp [W, kumCF_UW]
  have e1 : (wR 1 : ℂ) = x * kummerU (a + 1) b x := by
    rw [← hwR 1]; simp [W, kumCF_UW]
  have hc0 : cR 0 = a := by simp [cR]
  have hU0 : kummerU (a : ℂ) (b - 1) x ≠ 0 := by
    rw [← e0]; exact_mod_cast (hwpos 0).ne'
  have hval : ((1 + aR 0 * wR 1 / wR 0 : ℝ) : ℂ) =
      kummerU a b x / kummerU a (b - 1) x := by
    push_cast
    rw [e0, e1]
    simp only [aR, hc0]
    push_cast
    field_simp
    linear_combination -hU
  rw [← hval]
  exact (continuous_ofReal.tendsto _).comp hR1

/-- **DLMF 13.5.3 for all real parameters** (stronger than DLMF's stated range): for real
`a`, `b` and `x > 0` with `U(a, b-1, x) ≠ 0`, the convergents of
`1 + u₁/x/(1 + u₂/x/(1 + ⋯))` tend to `U(a,b,x)/U(a,b-1,x)`. The far tails are positive
S-fractions (`GenContFract.cfConv_tendsto_of_pos_linear`), and the head is attached by the
Pincherle invariant (`GenContFract.cfConv_tendsto_of_tail_invariant`); the elements and the
backward solution before the tail may vanish. -/
@[dlmf 13.5.E3 "stronger than DLMF: all real a, b with U(a,b-1,x) ≠ 0"]
theorem kummerU_continued_fraction_tendsto_real {a b x : ℝ} (hx : 0 < x)
    (hU : kummerU (a : ℂ) ((b : ℂ) - 1) x ≠ 0) :
    Tendsto (kummerUContinuedFraction a b x).convs atTop
      (𝓝 (kummerU a b x / kummerU a (b - 1) x)) := by
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  set W := kumCF_UW (a : ℂ) (b : ℂ) (x : ℂ) with hW
  set aC : ℕ → ℂ := fun k => kummerUContFractCoeff a b k / x with haC
  obtain ⟨K, hK⟩ := exists_nat_gt (|a| + |b|)
  have hKa : 0 < a + K := by have := neg_abs_le a; have := abs_nonneg b; linarith
  have hKb : 0 < a - b + K := by
    have := neg_abs_le a; have := le_abs_self b; linarith
  set J := 2 * K with hJ
  -- the tail of the backward solution is real and positive
  have hWr : ∀ k, ∃ r : ℝ, 0 < r ∧ W (k + (J + 1)) = r := by
    intro k
    simp only [W, kumCF_UW]
    split_ifs
    · have hK' : (K : ℝ) ≤ (((k + (J + 1)) / 2 : ℕ) : ℝ) := by
        exact_mod_cast (by omega : K ≤ (k + (J + 1)) / 2)
      obtain ⟨r, hr, e⟩ := kumCF_U_real_pos (c := a + (((k + (J + 1)) / 2 : ℕ) : ℝ))
        (d := b - 1) (x := x) (by linarith) hx
      refine ⟨x ^ ((k + (J + 1)) / 2) * r, by positivity, ?_⟩
      rw [show (a : ℂ) + (((k + (J + 1)) / 2 : ℕ) : ℂ) =
          ((a + (((k + (J + 1)) / 2 : ℕ) : ℝ) : ℝ) : ℂ) by push_cast; ring,
        show (b : ℂ) - 1 = ((b - 1 : ℝ) : ℂ) by push_cast; ring, e]
      push_cast; ring
    · have hK' : (K : ℝ) ≤ (((k + (J + 1) + 1) / 2 : ℕ) : ℝ) := by
        exact_mod_cast (by omega : K ≤ (k + (J + 1) + 1) / 2)
      obtain ⟨r, hr, e⟩ := kumCF_U_real_pos (c := a + (((k + (J + 1) + 1) / 2 : ℕ) : ℝ))
        (d := b) (x := x) (by linarith) hx
      refine ⟨x ^ ((k + (J + 1) + 1) / 2) * r, by positivity, ?_⟩
      rw [show (a : ℂ) + (((k + (J + 1) + 1) / 2 : ℕ) : ℂ) =
          ((a + (((k + (J + 1) + 1) / 2 : ℕ) : ℝ) : ℝ) : ℂ) by push_cast; ring, e]
      push_cast; ring
  choose wT hwTpos hwTR using hWr
  set cR : ℕ → ℝ := fun k => if (k + 1) % 2 = 1 then a + ((k / 2 : ℕ) : ℝ)
    else a - b + (((k + 1) / 2 : ℕ) : ℝ) + 1 with hcRdef
  have hcR : ∀ k, kummerUContFractCoeff a b k = (cR k : ℂ) := by
    intro k
    simp only [kummerUContFractCoeff, cR]
    split_ifs <;> push_cast <;> ring
  set aT : ℕ → ℝ := fun k => cR (k + (J + 1)) / x with haT
  have haTC : ∀ k, aC (k + (J + 1)) = (aT k : ℂ) := fun k => by
    simp only [aC, aT, hcR]; push_cast; ring
  have hrec : ∀ k, W k = 1 * W (k + 1) + aC (k + 1) * W (k + 2) := fun k => by
    rw [one_mul]; exact kumCF_UW_rec (a : ℂ) (b : ℂ) hx0 k
  have hrecT : ∀ k, wT k = 1 * wT (k + 1) + aT (k + 1) * wT (k + 2) := by
    intro k
    have := hrec (k + (J + 1))
    rw [hwTR k, show k + (J + 1) + 1 = k + 1 + (J + 1) by ring, hwTR (k + 1),
      show k + (J + 1) + 2 = k + 2 + (J + 1) by ring, hwTR (k + 2),
      show k + 1 + (J + 1) = (k + 1) + (J + 1) from rfl, haTC (k + 1)] at this
    exact_mod_cast this
  have hpos : ∀ k, 0 < aT k := by
    intro k
    simp only [aT, cR]
    refine div_pos ?_ hx
    split_ifs with h
    · have : (K : ℝ) ≤ (((k + (J + 1)) / 2 : ℕ) : ℝ) := by
        exact_mod_cast (by omega : K ≤ (k + (J + 1)) / 2)
      linarith
    · have : (K : ℝ) ≤ (((k + (J + 1) + 1) / 2 : ℕ) : ℝ) := by
        exact_mod_cast (by omega : K ≤ (k + (J + 1) + 1) / 2)
      linarith
  set M : ℝ := |a| + |b| + 2 with hM
  have hM1 : 1 ≤ M := by have := abs_nonneg a; have := abs_nonneg b; linarith
  have hcle : ∀ j : ℕ, cR j ≤ M + j := by
    intro j
    simp only [cR]
    have h1 := le_abs_self a
    have h2 := neg_abs_le b
    have h3 := abs_nonneg a
    have h4 := abs_nonneg b
    split_ifs
    · have : (((j / 2 : ℕ) : ℝ)) ≤ j := by exact_mod_cast Nat.div_le_self j 2
      linarith
    · have : (((j + 1) / 2 : ℕ) : ℝ) ≤ j + 1 := by
        exact_mod_cast (by omega : (j + 1) / 2 ≤ j + 1)
      linarith
  have hlin : ∀ k, aT k ≤ (M * (2 * K + 2) / x) * (k + 1) := by
    intro k
    simp only [aT]
    rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hx]
    have := hcle (k + (J + 1))
    simp only [J] at this
    push_cast at this
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
    nlinarith [mul_nonneg (sub_nonneg.2 hM1) (by positivity : (0 : ℝ) ≤ 2 * K + 1 + k),
      mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ M) (by positivity : (0 : ℝ) ≤ 2 * K + 1))
        hk]
  have htR := GenContFract.cfConv_tendsto_of_pos_linear (h := (0 : ℝ)) (a := aT) (w := wT) hpos
    hwTpos hrecT hlin
  -- transfer the tail to `ℂ`
  have hTfun : (fun k => aC (k + (J + 1))) = fun k => ((aT k : ℝ) : ℂ) := funext haTC
  have hTconv : ∀ n, (GenContFract.cfConv_ofFun 0 (fun k => aC (k + (J + 1)))
      (fun k => (fun _ => (1 : ℂ)) (k + (J + 1)))).convs n =
      ((GenContFract.cfConv_ofFun 0 aT (fun _ => (1 : ℝ))).convs n : ℂ) := by
    intro n
    have := GenContFract.cfConv_convs_map (h := (0 : ℝ)) (a := aT) (b := fun _ => (1 : ℝ))
      Complex.ofRealHom n
    simp only [Complex.ofRealHom_eq_coe, ofReal_zero, ofReal_one] at this
    rw [← this, hTfun]
  have hTdens : ∀ n, (GenContFract.cfConv_ofFun 0 (fun k => aC (k + (J + 1)))
      (fun k => (fun _ => (1 : ℂ)) (k + (J + 1)))).dens n ≠ 0 := by
    intro n
    have := GenContFract.cfConv_dens_map (h := (0 : ℝ)) (a := aT) (b := fun _ => (1 : ℝ))
      Complex.ofRealHom n
    simp only [Complex.ofRealHom_eq_coe, ofReal_zero, ofReal_one] at this
    rw [hTfun, this]
    exact_mod_cast (GenContFract.cfConv_dens_pos hpos (fun _ => one_pos) n).ne'
  have hW0 : W 0 = kummerU (a : ℂ) ((b : ℂ) - 1) x := by simp [W, kumCF_UW]
  have hW1 : W 1 = x * kummerU ((a : ℂ) + 1) b x := by simp [W, kumCF_UW]
  have key := GenContFract.cfConv_tendsto_of_tail_invariant (h := (1 : ℂ)) (a := aC)
    (b := fun _ => (1 : ℂ)) (w := W) hrec (by rw [hW0]; exact hU) J
    (by rw [show J + 1 = 0 + (J + 1) by ring, hwTR 0]; exact_mod_cast (hwTpos 0).ne')
    (Eventually.of_forall hTdens) (by
      show Tendsto (fun n => (GenContFract.cfConv_ofFun 0 (fun k => aC (k + (J + 1)))
        (fun k => (fun _ => (1 : ℂ)) (k + (J + 1)))).convs n) atTop _
      simp_rw [hTconv]
      have hv : aC (J + 1) * W (J + 2) / W (J + 1) =
          ((0 + aT 0 * wT 1 / wT 0 : ℝ) : ℂ) := by
        rw [show J + 1 = 0 + (J + 1) by ring, hwTR 0, show J + 2 = 1 + (J + 1) by ring, hwTR 1,
          haTC 0]
        push_cast; ring
      rw [hv]
      exact (continuous_ofReal.tendsto _).comp htR)
  show Tendsto (GenContFract.cfConv_ofFun 1 aC (fun _ => 1)).convs atTop _
  convert key using 2
  have hc0 : kummerUContFractCoeff (a : ℂ) b 0 = a := by simp [kummerUContFractCoeff]
  have hUab := kummerU_contiguous_a_b (a : ℂ) b x hx0
  rw [hW0, hW1]
  simp only [aC, hc0]
  field_simp
  linear_combination hUab

/-- Coefficients `u_n` in DLMF 13.17.2. -/
def whittakerMContFractCoeff (κ μ : ℂ) (k : ℕ) : ℂ :=
  if (k + 1) % 2 = 1 then
    let m : ℂ := (k / 2 : ℕ)
    (-(1 / 2 + μ + κ + m) / ((2 * μ + 2 * m + 1) * (2 * μ + 2 * m + 2)))
  else
    let m : ℂ := ((k + 1) / 2 : ℕ)
    (1 / 2 + μ - κ + m) / ((2 * μ + 2 * m) * (2 * μ + 2 * m + 1))

/-- The continued fraction with the Whittaker `M` coefficients `whittakerMContFractCoeff κ μ k`
(DLMF 13.17.1). -/
@[dlmf 13.17.E2]
def whittakerMContinuedFraction (κ μ z : ℂ) : GenContFract ℂ where
  h := 1
  s := Stream'.Seq.ofStream fun k => ⟨whittakerMContFractCoeff κ μ k * z, 1⟩

/-- Coefficients `v_n` in DLMF 13.17.4. -/
def whittakerWContFractCoeff (κ μ : ℂ) (k : ℕ) : ℂ :=
  if (k + 1) % 2 = 1 then
    let m : ℂ := (k / 2 : ℕ)
    1 / 2 + μ - κ + m
  else
    let m : ℂ := ((k + 1) / 2 : ℕ)
    1 / 2 - μ - κ + m

/-- The continued fraction with the Whittaker `W` coefficients `whittakerWContFractCoeff κ μ k`
(DLMF 13.17.3). -/
@[dlmf 13.17.E4]
def whittakerWContinuedFraction (κ μ z : ℂ) : GenContFract ℂ where
  h := 1
  s := Stream'.Seq.ofStream fun k => ⟨whittakerWContFractCoeff κ μ k / z, 1⟩

/-- `x^{s+1/2} = √x · x^s` for `x > 0`. -/
theorem kumCF_cpow_add_half {x : ℝ} (hx : 0 < x) (s : ℂ) :
    (x : ℂ) ^ (s + 1 / 2) = (Real.sqrt x : ℂ) * (x : ℂ) ^ s := by
  rw [cpow_add _ _ (ofReal_ne_zero.mpr hx.ne'), Real.sqrt_eq_rpow, ofReal_cpow hx.le]
  push_cast
  ring

/-- **Kummer's continued fraction** (DLMF 13.5.1) for complex parameters without conditions on
the partial numerators: if `b` is not a nonpositive integer, `z ≠ 0` and `M(a+1,b+1,z) ≠ 0`,
the convergents of `1 + u₁z/(1 + u₂z/(1 + ⋯))` tend to `M(a,b,z)/M(a+1,b+1,z)`. Stronger than
`kummerM_continued_fraction_tendsto`: vanishing (terminating) partial numerators are allowed.
The far tail is handled by Pincherle's ratio criterion and the head by the Pincherle invariant
(`GenContFract.cfConv_tendsto_of_tail_invariant`). -/
@[dlmf 13.5.E1 "stronger than DLMF: complex parameters, terminating fractions included"]
theorem kummerM_continued_fraction_tendsto_of_ne {a b z : ℂ} (hb : ∀ k : ℕ, b ≠ -k)
    (hz : z ≠ 0) (hM : kummerM (a + 1) (b + 1) z ≠ 0) :
    Tendsto (kummerMContinuedFraction a b z).convs atTop
      (𝓝 (kummerM a b z / kummerM (a + 1) (b + 1) z)) := by
  set F := kumCF_F a b z with hFdef
  set aC : ℕ → ℂ := fun k => kummerMContFractCoeff a b k * z with haC
  set w : ℕ → ℂ := fun k => F (k + 1) with hwdef
  obtain ⟨N, hN⟩ := eventually_atTop.mp (kumCF_eventually_ratio a b z)
  -- the partial numerators are eventually nonzero
  obtain ⟨L, hL⟩ := exists_nat_gt (‖a‖ + ‖b‖ + 1)
  have hcoeff : ∀ j ≥ 2 * L, kummerMContFractCoeff a b j ≠ 0 := by
    intro j hj
    have hb' : ∀ n : ℕ, b + n ≠ 0 := fun n h => hb n (by linear_combination h)
    have hab := norm_sub_le a b
    have h1 := norm_add_le a 1
    rcases Nat.even_or_odd' j with ⟨m, rfl | rfl⟩
    · rw [kumCF_coeff_even]
      refine div_ne_zero ?_ (mul_ne_zero ?_ ?_)
      · intro h0
        have : ‖a - b‖ = m := by
          rw [show a - b = (m : ℂ) by linear_combination h0, Complex.norm_natCast]
        have : (L : ℝ) ≤ m := by exact_mod_cast (by omega : L ≤ m)
        linarith
      · simpa using hb' (2 * m)
      · simpa [add_assoc] using hb' (2 * m + 1)
    · rw [kumCF_coeff_odd]
      refine div_ne_zero ?_ (mul_ne_zero ?_ ?_)
      · intro h0
        have : ‖a + 1‖ = m := by
          rw [show a + 1 = -(m : ℂ) by linear_combination h0, norm_neg, Complex.norm_natCast]
        have : (L : ℝ) ≤ m := by exact_mod_cast (by omega : L ≤ m)
        rw [norm_one] at h1
        have := norm_nonneg b
        linarith
      · have := hb' (2 * m + 1); push_cast at this; intro h; apply this; linear_combination h
      · have := hb' (2 * m + 2); push_cast at this; intro h; apply this; linear_combination h
  set J := N + 2 * L with hJ
  have hrec : ∀ k, w k = (fun _ => (1 : ℂ)) k * w (k + 1) + aC (k + 1) * w (k + 2) := by
    intro k
    simp only [w, aC, one_mul]
    exact kumCF_F_rec (a := a) hb z (k + 1)
  -- the tail from index `J + 1`
  set aT : ℕ → ℂ := fun k => aC (k + (J + 1)) with haT
  set wT : ℕ → ℂ := fun k => w (k + (J + 1)) with hwT
  have hrecT : ∀ k, wT k = (fun k => (fun _ => (1 : ℂ)) (k + (J + 1))) k * wT (k + 1) +
      aT (k + 1) * wT (k + 2) := by
    intro k
    have := hrec (k + (J + 1))
    simp only [wT, aT]
    rw [show k + 1 + (J + 1) = k + (J + 1) + 1 by ring,
      show k + 2 + (J + 1) = k + (J + 1) + 2 by ring]
    exact this
  have hwT : ∀ k, wT k ≠ 0 := fun k => (hN (k + (J + 1) + 1) (by omega)).1
  have haT0 : ∀ k, aT k ≠ 0 := fun k =>
    mul_ne_zero (hcoeff (k + (J + 1)) (by omega)) hz
  have hratT : ∀ k ≥ 0, (3 : ℝ) * ‖aT (k + 1) * wT (k + 2)‖ ≤ ‖wT k‖ := by
    intro k _
    have := (hN (k + (J + 1) + 1) (by omega)).2
    simp only [wT, aT, aC, w]
    rw [show k + 1 + (J + 1) = k + (J + 1) + 1 by ring,
      show k + 2 + (J + 1) + 1 = k + (J + 1) + 1 + 2 by ring, mul_assoc] at *
    simpa [mul_assoc] using this
  have hT := GenContFract.cfConv_tendsto_of_ratio (h := (0 : ℂ)) (a := aT)
    (b := fun k => (fun _ => (1 : ℂ)) (k + (J + 1))) (w := wT) hrecT (hwT 0) haT0
    (N := 0) (fun k _ => hwT k) (q := 3) (by norm_num) hratT
  have hDT := GenContFract.cfConv_dens_eventually_ne_of_ratio (h := (0 : ℂ)) (a := aT)
    (b := fun k => (fun _ => (1 : ℂ)) (k + (J + 1))) (w := wT) hrecT (hwT 0) haT0
    (N := 0) (fun k _ => hwT k) (q := 3) (by norm_num) hratT
  have hw0 : w 0 ≠ 0 := by
    have := kumCF_F_odd a b z 0
    simp only [mul_zero, zero_add, Nat.cast_zero, add_zero] at this
    show kumCF_F a b z 1 ≠ 0
    rw [this]; exact hM
  have key := GenContFract.cfConv_tendsto_of_tail_invariant (h := (1 : ℂ)) (a := aC)
    (b := fun _ => (1 : ℂ)) (w := w) hrec hw0 J (by simpa [wT] using hwT 0) hDT (by
      convert hT using 2
      simp only [aT, wT, zero_add]
      rw [show 1 + (J + 1) = J + 2 by ring])
  have hval : (1 : ℂ) + aC 0 * w 1 / w 0 = kummerM a b z / kummerM (a + 1) (b + 1) z := by
    have h0 : F 0 = F (0 + 1) + kummerMContFractCoeff a b 0 * z * F (1 + 1) :=
      kumCF_F_rec (a := a) hb z 0
    have e0 : F 0 = kummerM a b z := by simpa [F] using kumCF_F_even a b z 0
    have e1 : F (0 + 1) = kummerM (a + 1) (b + 1) z := by simpa [F] using kumCF_F_odd a b z 0
    have hF1 : F (0 + 1) ≠ 0 := by rw [e1]; exact hM
    simp only [w, aC]
    rw [← e0, ← e1, h0]
    field_simp
  rw [← hval]
  exact key

/-- **Whittaker's continued fraction for `M`** (DLMF 13.17.1). DLMF's equation is an identity
of meromorphic functions. At a zero of the denominator `M_{κ-1/2,μ+1/2}(x)` the convergents
diverge, while Lean's division gives `0` (for example `μ = 0.5`, `κ = 12.3`, `x ≈ 0.5615`), so
the hypothesis `hden` excludes those points; this is a transcription correction, not a DLMF
erratum. The proof reduces to Kummer's fraction 13.5.1 with `a = μ - κ + 1/2`, `b = 1 + 2μ`
(`kummerM_continued_fraction_tendsto_of_ne`). -/
@[dlmf 13.17.E1 "special case: denominator nonzero (Lean's x/0 = 0)"]
theorem whittakerM_continued_fraction_limit {κ μ x : ℝ} (hμ : 0 < μ)
    (hx : 0 < x) (hx1 : x < 1) (hden : whittakerM (κ - 1 / 2) (μ + 1 / 2) x ≠ 0) :
    Tendsto (whittakerMContinuedFraction κ μ x).convs atTop
      (𝓝 (Real.sqrt x * whittakerM κ μ x / whittakerM (κ - 1 / 2) (μ + 1 / 2) x)) := by
  set a : ℂ := (μ : ℂ) - κ + 1 / 2 with ha
  set b : ℂ := 1 + 2 * (μ : ℂ) with hb
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have hbk : ∀ k : ℕ, b ≠ -k := fun k h => by
    have := congrArg Complex.re h
    simp [b] at this
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hcf : whittakerMContinuedFraction κ μ x = kummerMContinuedFraction a b x := by
    simp only [whittakerMContinuedFraction, kummerMContinuedFraction]
    congr 2
    funext k
    congr 1
    simp only [whittakerMContFractCoeff, kummerMContFractCoeff, a, b]
    split_ifs <;> ring
  have hden' : whittakerM ((κ : ℂ) - 1 / 2) ((μ : ℂ) + 1 / 2) x =
      exp (-(x : ℂ) / 2) * (Real.sqrt x : ℂ) * (x : ℂ) ^ ((μ : ℂ) + 1 / 2) *
        kummerM (a + 1) (b + 1) x := by
    simp only [whittakerM, a, b]
    rw [show (μ : ℂ) + 1 / 2 + 1 / 2 = (μ + 1 / 2) + 1 / 2 by ring, kumCF_cpow_add_half hx]
    rw [show (μ : ℂ) + 1 / 2 - (κ - 1 / 2) + 1 / 2 = μ - κ + 1 / 2 + 1 by ring,
      show 1 + 2 * ((μ : ℂ) + 1 / 2) = 1 + 2 * μ + 1 by ring]
    ring
  have hM : kummerM (a + 1) (b + 1) x ≠ 0 := by
    intro h0; apply hden; rw [hden', h0, mul_zero]
  rw [hcf]
  convert kummerM_continued_fraction_tendsto_of_ne hbk hx0 hM using 2
  rw [hden']
  have hs : (Real.sqrt x : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hx).ne'
  have hp : (x : ℂ) ^ ((μ : ℂ) + 1 / 2) ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff]; tauto
  simp only [whittakerM, a, b]
  rw [show exp (-(x : ℂ) / 2) * (Real.sqrt x : ℂ) * (x : ℂ) ^ ((μ : ℂ) + 1 / 2) *
      kummerM ((μ : ℂ) - κ + 1 / 2 + 1) (1 + 2 * μ + 1) x =
      (Real.sqrt x : ℂ) * (exp (-(x : ℂ) / 2) * (x : ℂ) ^ ((μ : ℂ) + 1 / 2)) *
      kummerM ((μ : ℂ) - κ + 1 / 2 + 1) (1 + 2 * μ + 1) x by ring]
  rw [show (Real.sqrt x : ℂ) * (exp (-(x : ℂ) / 2) * (x : ℂ) ^ ((μ : ℂ) + 1 / 2) *
      kummerM ((μ : ℂ) - κ + 1 / 2) (1 + 2 * μ) x) =
      (Real.sqrt x : ℂ) * (exp (-(x : ℂ) / 2) * (x : ℂ) ^ ((μ : ℂ) + 1 / 2)) *
      kummerM ((μ : ℂ) - κ + 1 / 2) (1 + 2 * μ) x by ring]
  rw [mul_div_mul_left _ _ (mul_ne_zero hs (mul_ne_zero (exp_ne_zero _) hp))]

/-- **Whittaker's continued fraction for `W`** (DLMF 13.17.3). DLMF's equation is an identity
of meromorphic functions. At a zero of the denominator `W_{κ-1/2,μ-1/2}(x)` the convergents
diverge, while Lean's division gives `0` (for example `μ = 0.7`, `κ = 6.3`, `x ≈ 0.4755`), so
the hypothesis `hden` excludes those points; this is a transcription correction, not a DLMF
erratum. The proof reduces to the fraction 13.5.3 with `a = 1/2 + μ - κ`, `b = 1 + 2μ`
(`kummerU_continued_fraction_tendsto_real`). -/
@[dlmf 13.17.E3 "special case: denominator nonzero (Lean's x/0 = 0)"]
theorem whittakerW_continued_fraction_limit {κ μ x : ℝ} (hμ : 0 < μ) (hx : 0 < x)
    (hden : whittakerW (κ - 1 / 2) (μ - 1 / 2) x ≠ 0) :
    Tendsto (whittakerWContinuedFraction κ μ x).convs atTop
      (𝓝 (whittakerW κ μ x / (Real.sqrt x * whittakerW (κ - 1 / 2) (μ - 1 / 2) x))) := by
  set a : ℝ := 1 / 2 + μ - κ with ha
  set b : ℝ := 1 + 2 * μ with hb
  have hcf : whittakerWContinuedFraction κ μ x = kummerUContinuedFraction a b x := by
    simp only [whittakerWContinuedFraction, kummerUContinuedFraction]
    congr 2
    funext k
    congr 1
    simp only [whittakerWContFractCoeff, kummerUContFractCoeff, a, b]
    split_ifs
    · push_cast; ring
    · push_cast; ring
  have hden' : whittakerW ((κ : ℂ) - 1 / 2) ((μ : ℂ) - 1 / 2) x =
      exp (-(x : ℂ) / 2) * (x : ℂ) ^ (μ : ℂ) * kummerU (a : ℂ) ((b : ℂ) - 1) x := by
    simp only [whittakerW, a, b]
    push_cast
    ring_nf
  have hU : kummerU (a : ℂ) ((b : ℂ) - 1) x ≠ 0 := by
    intro h0; apply hden; rw [hden', h0, mul_zero]
  rw [hcf]
  convert kummerU_continued_fraction_tendsto_real hx hU using 2
  rw [hden']
  have hs : (Real.sqrt x : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hx).ne'
  have hp : (x : ℂ) ^ (μ : ℂ) ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff]; exact fun h => (ofReal_ne_zero.mpr hx.ne') h.1
  simp only [whittakerW, a, b]
  push_cast
  rw [show (1 : ℂ) / 2 + μ = μ + 1 / 2 by ring, kumCF_cpow_add_half hx]
  field_simp

end DLMF.Confluent
