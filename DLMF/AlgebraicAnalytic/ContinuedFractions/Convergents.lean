/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AlgebraicAnalytic.ContinuedFractions.Basic

/-!
# Convergents of continued fractions (DLMF §§1.12(ii)–1.12(iv))

For `contFrac a b = b₀ + a₁/(b₁ + a₂/(b₂ + ⋯))` (DLMF indexing), the canonical numerators
`A_n = (contFrac a b).nums n` and denominators `B_n = (contFrac a b).dens n`, their recurrences
and determinant formula, equivalence transformations, Euler's series fraction, the fractional
transformation and the even and odd parts.

## Main results

* `contFrac_contsAux_rec`, `contFrac_initial`: the recurrences 1.12.5–1.12.6 (with
  `A_{-1} = 1`, `B_{-1} = 0` as Mathlib's `contsAux 0 = ⟨1, 0⟩`).
* `contFrac_convs'_eq_convs`: the nested form of `C_n = A_n/B_n` (DLMF 1.12.4).
* `contFrac_det`: the determinant formula (DLMF 1.12.7).
* `contFrac_convs_sub`, `contFrac_convs_eq_sum`, `contFrac_a_eq`, `contFrac_a_eq_convs`,
  `contFrac_b_eq`, `contFrac_b_eq_convs`, `contFrac_initial_elements`: DLMF 1.12.8–1.12.14.
* `contFracEquiv_of_scale`, `contFracEquiv_unit_denominators`, `contFracEquiv_unit_numerators`:
  equivalence transformations (DLMF 1.12.15–1.12.17).
* `contFrac_euler_series`, `contFrac_power_series`: Euler's series fraction
  (DLMF 1.12.18–1.12.19).
* `contFracApprox_zero`, `contFracApprox_eq`, `contFracApprox_tendsto_infty`: the fractional
  transformation (DLMF 1.12.20–1.12.21).
* `exists_contFrac_convs_iff`: the characterization of sequences of convergents, finite-valued
  form (DLMF 1.12.22).
* `contFrac_evenPart_convs`, `exists_evenPart_iff`, `contFrac_oddPart_convs`,
  `exists_oddPart_iff`: even and odd parts (DLMF 1.12.23–1.12.24, §1.12(iv)).

## Implementation notes

The approximants are the ratios `A_n/B_n` (Mathlib's `GenContFract.convs`); the nested fractions
(`GenContFract.convs'`) agree with them when the nested denominators do not vanish (1.12.4).
Several statements are therefore stronger than DLMF's (no hypothesis `p_k ≠ 0` in 1.12.18).
-/

@[expose] public noncomputable section

open Filter Finset GenContFract
open scoped Topology

namespace DLMF.AlgebraicAnalytic

variable {K : Type*} [Field K] (a b : ℕ → K)

/-! ## Continuants in DLMF indexing -/

/-- The integer part of `contFrac a b` is `b₀`. -/
@[simp] theorem contFrac_h : (contFrac a b).h = b 0 := rfl

/-- `A₀ = b₀`. -/
theorem contFrac_nums_zero : (contFrac a b).nums 0 = b 0 := cfConv_nums_zero _ _ _

/-- `B₀ = 1`. -/
theorem contFrac_dens_zero : (contFrac a b).dens 0 = 1 := cfConv_dens_zero _ _ _

/-- `A₁ = b₁ b₀ + a₁`. -/
theorem contFrac_nums_one : (contFrac a b).nums 1 = b 1 * b 0 + a 1 := cfConv_nums_one _ _ _

/-- `B₁ = b₁`. -/
theorem contFrac_dens_one : (contFrac a b).dens 1 = b 1 := cfConv_dens_one _ _ _

/-- `A_{n+2} = b_{n+2} A_{n+1} + a_{n+2} A_n`. -/
theorem contFrac_nums_step (n : ℕ) :
    (contFrac a b).nums (n + 2) =
      b (n + 2) * (contFrac a b).nums (n + 1) + a (n + 2) * (contFrac a b).nums n :=
  cfConv_nums_step _ _ _ n

/-- `B_{n+2} = b_{n+2} B_{n+1} + a_{n+2} B_n`. -/
theorem contFrac_dens_step (n : ℕ) :
    (contFrac a b).dens (n + 2) =
      b (n + 2) * (contFrac a b).dens (n + 1) + a (n + 2) * (contFrac a b).dens n :=
  cfConv_dens_step _ _ _ n

/-- `C_0 = b₀`. -/
theorem contFrac_convs_zero : (contFrac a b).convs 0 = b 0 := zeroth_conv_eq_h

/-- `⟨A_n, B_n⟩ = contsAux (n + 1)`. -/
lemma contFrac_contsAux_succ (n : ℕ) :
    (contFrac a b).contsAux (n + 1) = ⟨(contFrac a b).nums n, (contFrac a b).dens n⟩ := rfl

/-- DLMF 1.12.5: `A_k = b_k A_{k-1} + a_k A_{k-2}` and `B_k = b_k B_{k-1} + a_k B_{k-2}` for
`k = m + 1 ≥ 1`, in terms of `contsAux j = ⟨A_{j-1}, B_{j-1}⟩` (so that `k = 1` uses
`A_{-1} = 1`, `B_{-1} = 0`). -/
@[dlmf 1.12.E5]
theorem contFrac_contsAux_rec (m : ℕ) :
    ((contFrac a b).contsAux (m + 2)).a =
        b (m + 1) * ((contFrac a b).contsAux (m + 1)).a +
          a (m + 1) * ((contFrac a b).contsAux m).a ∧
      ((contFrac a b).contsAux (m + 2)).b =
        b (m + 1) * ((contFrac a b).contsAux (m + 1)).b +
          a (m + 1) * ((contFrac a b).contsAux m).b := by
  have h := contsAux_recurrence (g := contFrac a b) (n := m) (gp := ⟨a (m + 1), b (m + 1)⟩)
    rfl rfl rfl
  rw [h]
  exact ⟨rfl, rfl⟩

/-- DLMF 1.12.6: `A_{-1} = 1`, `A_0 = b_0`, `B_{-1} = 0`, `B_0 = 1`. -/
@[dlmf 1.12.E6]
theorem contFrac_initial :
    (contFrac a b).contsAux 0 = ⟨1, 0⟩ ∧ (contFrac a b).nums 0 = b 0 ∧
      (contFrac a b).dens 0 = 1 :=
  ⟨zeroth_contAux_eq_one_zero, contFrac_nums_zero a b, contFrac_dens_zero a b⟩

/-! ## The nested form 1.12.4 -/

/-- The head decomposition of the continuants: `A_{n+1} = b₀ A'_n + a₁ B'_n` and
`B_{n+1} = A'_n`, where `A'`, `B'` are the continuants of the tail
`b₁ + a₂/(b₂ + ⋯)`. -/
theorem contFrac_conts_head (n : ℕ) :
    (contFrac a b).nums (n + 1) =
        b 0 * (contFrac (fun j => a (j + 1)) (fun j => b (j + 1))).nums n +
          a 1 * (contFrac (fun j => a (j + 1)) (fun j => b (j + 1))).dens n ∧
      (contFrac a b).dens (n + 1) =
        (contFrac (fun j => a (j + 1)) (fun j => b (j + 1))).nums n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | n
    · constructor
      · rw [contFrac_nums_one, contFrac_nums_zero, contFrac_dens_zero]; ring
      · rw [contFrac_dens_one, contFrac_nums_zero]
    · constructor
      · rw [contFrac_nums_step a b 0, contFrac_nums_one, contFrac_nums_zero,
          contFrac_nums_one, contFrac_dens_one]; ring
      · rw [contFrac_dens_step a b 0, contFrac_dens_one, contFrac_dens_zero,
          contFrac_nums_one]; ring
    · obtain ⟨h1, h1'⟩ := ih (n + 1) (by omega)
      obtain ⟨h0, h0'⟩ := ih n (by omega)
      rw [contFrac_nums_step a b (n + 1), contFrac_dens_step a b (n + 1),
        contFrac_nums_step (fun j => a (j + 1)) (fun j => b (j + 1)) n,
        contFrac_dens_step (fun j => a (j + 1)) (fun j => b (j + 1)) n, h1, h0, h1', h0']
      constructor <;> ring


/-- The nested finite fraction in head form:
`b₀ + a₁/(b₁ + ⋯ + a_{n+1}/b_{n+1}) = b₀ + a₁/(tail value)`. -/
theorem contFrac_convs'_succ (n : ℕ) :
    (contFrac a b).convs' (n + 1) =
      b 0 + a 1 / (contFrac (fun j => a (j + 1)) (fun j => b (j + 1))).convs' n := by
  rfl

/-- DLMF 1.12.4: when the nested denominators `b_k + a_{k+1}/(b_{k+1} + ⋯ + a_n/b_n)`,
`1 ≤ k ≤ n`, do not vanish, the nested fraction `b₀ + a₁/(b₁ + ⋯ + a_n/b_n)` equals
`C_n = A_n/B_n`, and `B_n ≠ 0`. -/
@[dlmf 1.12.E4]
theorem contFrac_convs'_eq_convs (n : ℕ) :
    ∀ a b : ℕ → K, (∀ k, 1 ≤ k → k ≤ n → contFracTail a b k n ≠ 0) →
      (contFrac a b).convs' n = (contFrac a b).convs n ∧ (contFrac a b).dens n ≠ 0 := by
  induction n with
  | zero =>
    intro a b _
    simp [zeroth_conv'_eq_h, contFrac]
  | succ n ih =>
    intro a b ht
    have ht' : ∀ k, 1 ≤ k → k ≤ n →
        contFracTail (fun j => a (j + 1)) (fun j => b (j + 1)) k n ≠ 0 := by
      intro k hk hkn
      have := ht (k + 1) (by omega) (by omega)
      simpa [contFracTail, show n + 1 - (k + 1) = n - k by omega, add_assoc, add_comm 1] using this
    obtain ⟨hc, hd⟩ := ih _ _ ht'
    have ht1 : (contFrac (fun j => a (j + 1)) (fun j => b (j + 1))).convs' n ≠ 0 := by
      have := ht 1 le_rfl (by omega)
      simpa [contFracTail] using this
    obtain ⟨hA, hB⟩ := contFrac_conts_head a b n
    rw [hc] at ht1
    have hN : (contFrac (fun j => a (j + 1)) (fun j => b (j + 1))).nums n ≠ 0 := by
      intro h0; apply ht1; simp [convs, h0]
    refine ⟨?_, by rw [hB]; exact hN⟩
    rw [contFrac_convs'_succ, hc]
    simp only [convs]
    rw [hA, hB]
    field_simp

/-! ## The determinant formula and its consequences -/

/-- DLMF 1.12.7: `A_n B_{n-1} - B_n A_{n-1} = (-1)^{n-1} ∏_{k=1}^n a_k` for `n ≥ 0`, in terms
of `contsAux (n + 1) = ⟨A_n, B_n⟩` and `contsAux n = ⟨A_{n-1}, B_{n-1}⟩`. -/
@[dlmf 1.12.E7]
theorem contFrac_det (n : ℕ) :
    ((contFrac a b).contsAux (n + 1)).a * ((contFrac a b).contsAux n).b -
        ((contFrac a b).contsAux (n + 1)).b * ((contFrac a b).contsAux n).a =
      (-1) ^ (n + 1) * ∏ k ∈ range n, a (k + 1) := by
  rcases n with _ | m
  · simp [zeroth_contAux_eq_one_zero]

  · rw [contFrac_contsAux_succ, contFrac_contsAux_succ]
    have h := cfConv_det (b 0) (fun k => a (k + 1)) (fun k => b (k + 1)) m
    simp only [] at h ⊢
    change (contFrac a b).nums (m + 1) * (contFrac a b).dens m -
      (contFrac a b).dens (m + 1) * (contFrac a b).nums m = _
    rw [show (contFrac a b) = cfConv_ofFun (b 0) (fun k => a (k + 1)) (fun k => b (k + 1)) from
      rfl, h, pow_succ, pow_succ]
    ring

/-- The determinant formula for `n = m + 1` in terms of `nums` and `dens`. -/
theorem contFrac_det' (m : ℕ) :
    (contFrac a b).nums (m + 1) * (contFrac a b).dens m -
        (contFrac a b).dens (m + 1) * (contFrac a b).nums m =
      (-1) ^ m * ∏ k ∈ range (m + 1), a (k + 1) :=
  cfConv_det (b 0) (fun k => a (k + 1)) (fun k => b (k + 1)) m

/-- DLMF 1.12.8: `C_n - C_{n-1} = (-1)^{n-1} ∏_{k=1}^n a_k / (B_{n-1} B_n)` (`n = m + 1`). -/
@[dlmf 1.12.E8]
theorem contFrac_convs_sub (m : ℕ) (h0 : (contFrac a b).dens m ≠ 0)
    (h1 : (contFrac a b).dens (m + 1) ≠ 0) :
    (contFrac a b).convs (m + 1) - (contFrac a b).convs m =
      (-1) ^ m * (∏ k ∈ range (m + 1), a (k + 1)) /
        ((contFrac a b).dens m * (contFrac a b).dens (m + 1)) := by
  simp only [convs]
  rw [div_sub_div _ _ h1 h0, ← contFrac_det' a b m]
  ring

/-- DLMF 1.12.9: `C_n = b₀ + a₁/(B₀B₁) - ⋯ + (-1)^{n-1} ∏_{k=1}^n a_k/(B_{n-1}B_n)`, when
`B_0, …, B_n ≠ 0`. -/
@[dlmf 1.12.E9]
theorem contFrac_convs_eq_sum (n : ℕ) (hB : ∀ k ≤ n, (contFrac a b).dens k ≠ 0) :
    (contFrac a b).convs n = b 0 + ∑ k ∈ range n,
      (-1) ^ k * (∏ j ∈ range (k + 1), a (j + 1)) /
        ((contFrac a b).dens k * (contFrac a b).dens (k + 1)) := by
  induction n with
  | zero => rw [range_zero, sum_empty, add_zero, contFrac_convs_zero]
  | succ n ih =>
    rw [sum_range_succ, ← add_assoc, ← ih (fun k hk => hB k (by omega)),
      ← contFrac_convs_sub a b n (hB n (by omega)) (hB (n + 1) le_rfl)]
    ring

/-- The determinant `A_{m+1}B_m - A_mB_{m+1}` does not vanish when `a_1, …, a_{m+1} ≠ 0`. -/
private lemma nums_succ_mul_dens_sub_ne_zero (m : ℕ) (ha : ∀ k, 1 ≤ k → k ≤ m + 1 → a k ≠ 0) :
    (contFrac a b).nums (m + 1) * (contFrac a b).dens m -
        (contFrac a b).dens (m + 1) * (contFrac a b).nums m ≠ 0 := by
  rw [contFrac_det']
  refine mul_ne_zero (pow_ne_zero _ (by norm_num)) (prod_ne_zero_iff.mpr fun k hk => ?_)
  exact ha (k + 1) (by omega) (by simp at hk; omega)

/-- DLMF 1.12.10: `a_n = (A_{n-1}B_n - A_nB_{n-1})/(A_{n-1}B_{n-2} - A_{n-2}B_{n-1})` for
`n = m + 2 ≥ 2`, when `a_1, …, a_{n-1} ≠ 0` (for `n = 1` see 1.12.14). -/
@[dlmf 1.12.E10]
theorem contFrac_a_eq (m : ℕ) (ha : ∀ k, 1 ≤ k → k ≤ m + 1 → a k ≠ 0) :
    a (m + 2) =
      ((contFrac a b).nums (m + 1) * (contFrac a b).dens (m + 2) -
          (contFrac a b).nums (m + 2) * (contFrac a b).dens (m + 1)) /
        ((contFrac a b).nums (m + 1) * (contFrac a b).dens m -
          (contFrac a b).nums m * (contFrac a b).dens (m + 1)) := by
  have hd := nums_succ_mul_dens_sub_ne_zero a b m ha
  have h1 := contFrac_det' a b m
  have h2 := contFrac_det' a b (m + 1)
  rw [eq_div_iff (by intro h; apply hd; linear_combination h)]
  rw [prod_range_succ] at h2
  linear_combination a (m + 2) * h1 + h2

/-- DLMF 1.12.12: `b_n = (A_nB_{n-2} - A_{n-2}B_n)/(A_{n-1}B_{n-2} - A_{n-2}B_{n-1})` for
`n = m + 2 ≥ 2`, when `a_1, …, a_{n-1} ≠ 0`. -/
@[dlmf 1.12.E12]
theorem contFrac_b_eq (m : ℕ) (ha : ∀ k, 1 ≤ k → k ≤ m + 1 → a k ≠ 0) :
    b (m + 2) =
      ((contFrac a b).nums (m + 2) * (contFrac a b).dens m -
          (contFrac a b).nums m * (contFrac a b).dens (m + 2)) /
        ((contFrac a b).nums (m + 1) * (contFrac a b).dens m -
          (contFrac a b).nums m * (contFrac a b).dens (m + 1)) := by
  have hd := nums_succ_mul_dens_sub_ne_zero a b m ha
  rw [eq_div_iff (by intro h; apply hd; linear_combination h), contFrac_nums_step,
    contFrac_dens_step]
  ring

/-- DLMF 1.12.11: `a_n = (B_n/B_{n-2}) (C_{n-1} - C_n)/(C_{n-1} - C_{n-2})` for `n = m + 2`,
when `B_{n-2}, B_{n-1}, B_n ≠ 0` and `a_1, …, a_{n-1} ≠ 0`. -/
@[dlmf 1.12.E11]
theorem contFrac_a_eq_convs (m : ℕ) (ha : ∀ k, 1 ≤ k → k ≤ m + 1 → a k ≠ 0)
    (h0 : (contFrac a b).dens m ≠ 0) (h1 : (contFrac a b).dens (m + 1) ≠ 0)
    (h2 : (contFrac a b).dens (m + 2) ≠ 0) :
    a (m + 2) = (contFrac a b).dens (m + 2) / (contFrac a b).dens m *
      (((contFrac a b).convs (m + 1) - (contFrac a b).convs (m + 2)) /
        ((contFrac a b).convs (m + 1) - (contFrac a b).convs m)) := by
  have hd := nums_succ_mul_dens_sub_ne_zero a b m ha
  have hd' : (contFrac a b).nums (m + 1) * (contFrac a b).dens m -
      (contFrac a b).nums m * (contFrac a b).dens (m + 1) ≠ 0 := by
    intro h; apply hd; linear_combination h
  rw [contFrac_a_eq a b m ha]
  simp only [convs]
  field_simp

/-- DLMF 1.12.13: `b_n = (B_n/B_{n-1}) (C_n - C_{n-2})/(C_{n-1} - C_{n-2})` for `n = m + 2`,
when `B_{n-2}, B_{n-1}, B_n ≠ 0` and `a_1, …, a_{n-1} ≠ 0`. -/
@[dlmf 1.12.E13]
theorem contFrac_b_eq_convs (m : ℕ) (ha : ∀ k, 1 ≤ k → k ≤ m + 1 → a k ≠ 0)
    (h0 : (contFrac a b).dens m ≠ 0) (h1 : (contFrac a b).dens (m + 1) ≠ 0)
    (h2 : (contFrac a b).dens (m + 2) ≠ 0) :
    b (m + 2) = (contFrac a b).dens (m + 2) / (contFrac a b).dens (m + 1) *
      (((contFrac a b).convs (m + 2) - (contFrac a b).convs m) /
        ((contFrac a b).convs (m + 1) - (contFrac a b).convs m)) := by
  have hd := nums_succ_mul_dens_sub_ne_zero a b m ha
  have hd' : (contFrac a b).nums (m + 1) * (contFrac a b).dens m -
      (contFrac a b).nums m * (contFrac a b).dens (m + 1) ≠ 0 := by
    intro h; apply hd; linear_combination h
  rw [contFrac_b_eq a b m ha]
  simp only [convs]
  rw [div_sub_div _ _ h2 h0, div_sub_div _ _ h1 h0]
  field_simp

/-- DLMF 1.12.14: `b₀ = A₀ = C₀`, `b₁ = B₁`, `a₁ = A₁ - A₀B₁`. -/
@[dlmf 1.12.E14]
theorem contFrac_initial_elements :
    b 0 = (contFrac a b).nums 0 ∧ (contFrac a b).nums 0 = (contFrac a b).convs 0 ∧
      b 1 = (contFrac a b).dens 1 ∧
      a 1 = (contFrac a b).nums 1 - (contFrac a b).nums 0 * (contFrac a b).dens 1 := by
  refine ⟨(contFrac_nums_zero a b).symm, ?_, (contFrac_dens_one a b).symm, ?_⟩
  · rw [contFrac_nums_zero, contFrac_convs_zero]
  · rw [contFrac_nums_one, contFrac_nums_zero, contFrac_dens_one]
    ring

/-! ## Equivalence transformations -/

/-- The value `a 0` does not enter `contFrac a b`. -/
theorem contFrac_congr {a a' b b' : ℕ → K} (ha : ∀ k, 1 ≤ k → a k = a' k) (hb : ∀ k, b k = b' k) :
    contFrac a b = contFrac a' b' := by
  have h1 : (fun k => a (k + 1)) = fun k => a' (k + 1) := funext fun k => ha (k + 1) (by omega)
  have h2 : b = b' := funext hb
  simp only [contFrac, h1, h2]

/-- DLMF 1.12.15–1.12.16: if `d₀ = 1`, `d_n ≠ 0`, `a'_n = d_n d_{n-1} a_n` (`n ≥ 1`) and
`b'_n = d_n b_n` (`n ≥ 0`), then `b'₀ + a'₁/(b'₁ + ⋯)` is equivalent to `b₀ + a₁/(b₁ + ⋯)`. -/
@[dlmf 1.12.E15, dlmf 1.12.E16]
theorem contFracEquiv_of_scale (d : ℕ → K) (hd0 : d 0 = 1) (hd : ∀ n, d n ≠ 0) {a' b' : ℕ → K}
    (ha' : ∀ n, 1 ≤ n → a' n = d n * d (n - 1) * a n) (hb' : ∀ n, b' n = d n * b n) :
    ContFracEquiv a b a' b' := by
  intro n
  have hA : (fun k => a' (k + 1)) =
      fun k => (if k = 0 then d (0 + 1) else d (k - 1 + 1) * d (k + 1)) * a (k + 1) := by
    funext k
    rw [ha' (k + 1) (by omega)]
    rcases k with _ | k
    · simp [hd0]
    · simp only [Nat.add_sub_cancel, Nat.succ_ne_zero, ↓reduceIte]
      ring
  have hB : (fun k => b' (k + 1)) = fun k => d (k + 1) * b (k + 1) := funext fun k => hb' (k + 1)
  have h0 : b' 0 = b 0 := by rw [hb', hd0, one_mul]
  unfold contFrac
  rw [h0, hA, hB]
  exact (cfConv_equiv_convs (h := b 0) (a := fun k => a (k + 1)) (b := fun k => b (k + 1))
    (fun k => d (k + 1)) (fun k => hd _) n).symm

/-- DLMF 1.12.17, first form: when `b_n ≠ 0` (`n ≥ 1`),
`b₀ + a₁/(b₁ + a₂/(b₂ + ⋯))` is equivalent to
`b₀ + (a₁/b₁)/(1 + (a₂/(b₁b₂))/(1 + ⋯ (a_n/(b_{n-1}b_n))/(1 + ⋯)))`. -/
@[dlmf 1.12.E17]
theorem contFracEquiv_unit_denominators (hb : ∀ n, 1 ≤ n → b n ≠ 0) :
    ContFracEquiv a b (fun n => if n = 1 then a 1 / b 1 else a n / (b (n - 1) * b n))
      (fun n => if n = 0 then b 0 else 1) := by
  refine contFracEquiv_of_scale a b (fun n => if n = 0 then 1 else 1 / b n) (by simp)
    (fun n => ?_) (fun n hn => ?_) (fun n => ?_)
  · rcases n with _ | n
    · simp
    · simpa using hb (n + 1) (by omega)
  · rcases n with _ | _ | n
    · omega
    · simp
      field_simp
    · simp only [show n + 2 ≠ 1 by omega, show n + 2 ≠ 0 by omega, show n + 2 - 1 ≠ 0 by omega,
        ↓reduceIte]
      have h1 := hb (n + 2) (by omega)
      have h2 := hb (n + 2 - 1) (by omega)
      field_simp
  · rcases n with _ | n
    · simp
    · simp only [Nat.succ_ne_zero, ↓reduceIte]
      field_simp [hb (n + 1) (by omega)]

/-- The factors `d_n` of `contFracUnitFactor` do not vanish. -/
private lemma contFracUnitFactor_ne_zero (ha : ∀ n, 1 ≤ n → a n ≠ 0) (n : ℕ) :
    contFracUnitFactor a n ≠ 0 := by
  induction n with
  | zero => simp [contFracUnitFactor]
  | succ n ih =>
    simp only [contFracUnitFactor]
    exact one_div_ne_zero (mul_ne_zero (ha (n + 1) (by omega)) ih)

/-- DLMF 1.12.17, second form: when `a_n ≠ 0`, `b₀ + a₁/(b₁ + a₂/(b₂ + ⋯))` is equivalent to
`b₀ + 1/(d₁b₁ + 1/(d₂b₂ + ⋯))` with `d_n = contFracUnitFactor a n`
(`d₁ = 1/a₁`, `d₂ = a₁/a₂`, `d₃ = a₂/(a₁a₃)`, `d₄ = a₁a₃/(a₂a₄)`, …). -/
@[dlmf 1.12.E17]
theorem contFracEquiv_unit_numerators (ha : ∀ n, 1 ≤ n → a n ≠ 0) :
    ContFracEquiv a b (fun _ => 1) (fun n => contFracUnitFactor a n * b n) := by
  refine contFracEquiv_of_scale a b (contFracUnitFactor a) rfl (contFracUnitFactor_ne_zero a ha)
    (fun n hn => ?_) (fun n => rfl)
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h1 := ha (m + 1) (by omega)
  have h2 := contFracUnitFactor_ne_zero a ha m
  simp only [contFracUnitFactor, Nat.add_sub_cancel]
  field_simp

/-! ## Series and continued fractions -/

/-- DLMF 1.12.18 (Euler): `p₀ + ∑_{k=1}^n p₁p₂⋯p_k` is the `n`-th convergent of
`p₀ + p₁/(1 - p₂/(1 + p₂ - p₃/(1 + p₃ - ⋯)))`. Stronger than DLMF: with the convergents
`A_n/B_n` no hypothesis `p_k ≠ 0` is needed (here `B_n = 1`). -/
@[dlmf 1.12.E18]
theorem contFrac_euler_series (p : ℕ → K) (n : ℕ) :
    (contFrac (fun k => if k = 1 then p 1 else -p k)
      (fun k => if k = 0 then p 0 else if k = 1 then 1 else 1 + p k)).convs n =
      p 0 + ∑ k ∈ range n, ∏ j ∈ range (k + 1), p (j + 1) := by
  set a' : ℕ → K := fun k => if k = 1 then p 1 else -p k with ha'
  set b' : ℕ → K := fun k => if k = 0 then p 0 else if k = 1 then 1 else 1 + p k with hb'
  have key : ∀ n, (contFrac a' b').dens n = 1 ∧
      (contFrac a' b').nums n = p 0 + ∑ k ∈ range n, ∏ j ∈ range (k + 1), p (j + 1) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      rcases n with _ | _ | n
      · simp [hb']
      · simp [contFrac_dens_one, contFrac_nums_one, ha', hb']
      · obtain ⟨d1, n1⟩ := ih (n + 1) (by omega)
        obtain ⟨d0, n0⟩ := ih n (by omega)
        rw [contFrac_dens_step, contFrac_nums_step, d1, d0, n1, n0]
        simp only [ha', hb', show n + 2 ≠ 1 by omega, show n + 2 ≠ 0 by omega, ↓reduceIte]
        constructor
        · ring
        · simp only [sum_range_succ, prod_range_succ]
          ring
  simp only [convs]
  rw [(key n).1, (key n).2, div_one]

/-- DLMF 1.12.19: `∑_{k=0}^n c_k x^k` is the `n`-th convergent of
`c₀ + c₁x/(1 - (c₂/c₁)x/(1 + (c₂/c₁)x - (c₃/c₂)x/(1 + (c₃/c₂)x - ⋯)))`, when `c_k ≠ 0`
(`k ≥ 1`). -/
@[dlmf 1.12.E19]
theorem contFrac_power_series (c : ℕ → K) (x : K) (hc : ∀ k, 1 ≤ k → c k ≠ 0) (n : ℕ) :
    (contFrac (fun k => if k = 1 then c 1 * x else -(c k / c (k - 1) * x))
      (fun k => if k = 0 then c 0 else if k = 1 then 1 else 1 + c k / c (k - 1) * x)).convs n =
      ∑ k ∈ range (n + 1), c k * x ^ k := by
  set p : ℕ → K := fun k => if k = 0 then c 0 else if k = 1 then c 1 * x else c k / c (k - 1) * x
    with hp
  have hcf : contFrac (fun k => if k = 1 then c 1 * x else -(c k / c (k - 1) * x))
      (fun k => if k = 0 then c 0 else if k = 1 then 1 else 1 + c k / c (k - 1) * x) =
      contFrac (fun k => if k = 1 then p 1 else -p k)
        (fun k => if k = 0 then p 0 else if k = 1 then 1 else 1 + p k) := by
    apply contFrac_congr
    · intro k hk
      rcases k with _ | _ | k
      · omega
      · simp [hp]
      · simp [hp]
    · intro k
      rcases k with _ | _ | k <;> simp [hp]
  have hprod : ∀ k, ∏ j ∈ range (k + 1), p (j + 1) = c (k + 1) * x ^ (k + 1) := by
    intro k
    induction k with
    | zero => simp [hp]
    | succ k ih =>
      rw [prod_range_succ, ih]
      have h1 := hc (k + 1) (by omega)
      simp only [hp, show k + 1 + 1 ≠ 0 by omega, show k + 1 + 1 ≠ 1 by omega, ↓reduceIte,
        Nat.add_sub_cancel]
      field_simp
      ring
  rw [hcf, contFrac_euler_series]
  simp only [hprod]
  rw [sum_range_succ' _ n]
  simp only [hp, ↓reduceIte, pow_zero, mul_one]
  ring

/-! ## Fractional transformations -/

/-- DLMF 1.12.21: `C_n(0) = C_n` in nested form. -/
@[dlmf 1.12.E21]
theorem contFracApprox_zero (n : ℕ) : contFracApprox a b n 0 = (contFrac a b).convs' n := by
  simp [contFracApprox]

/-- The continuants with index `≤ m` depend only on `b_0, …, b_m`. -/
private lemma nums_dens_congr {b' : ℕ → K} (m : ℕ) (hb : ∀ k ≤ m, b k = b' k) :
    ∀ j ≤ m, (contFrac a b).nums j = (contFrac a b').nums j ∧
      (contFrac a b).dens j = (contFrac a b').dens j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    rcases j with _ | _ | j
    · simp [hb 0 (by omega)]
    · simp [contFrac_nums_one, contFrac_dens_one, hb 0 (by omega), hb 1 hj]
    · obtain ⟨n1, d1⟩ := ih (j + 1) (by omega) (by omega)
      obtain ⟨n0, d0⟩ := ih j (by omega) (by omega)
      rw [contFrac_nums_step, contFrac_dens_step, contFrac_nums_step a b', contFrac_dens_step a b',
        n1, d1, n0, d0, hb (j + 2) hj]
      exact ⟨rfl, rfl⟩

/-- The continuants of the fraction with `b_n` replaced by `b_n + w`:
`⟨A_n + A_{n-1}w, B_n + B_{n-1}w⟩`. -/
private lemma contsAux_update_add (n : ℕ) (w : K) :
    (contFrac a (Function.update b n (b n + w))).contsAux (n + 1) =
      ⟨((contFrac a b).contsAux (n + 1)).a + ((contFrac a b).contsAux n).a * w,
        ((contFrac a b).contsAux (n + 1)).b + ((contFrac a b).contsAux n).b * w⟩ := by
  rcases n with _ | _ | n
  · simp [zeroth_contAux_eq_one_zero]
  · simp only [contFrac_contsAux_succ, contFrac_nums_one, contFrac_dens_one, contFrac_nums_zero,
      contFrac_dens_zero]
    simp
    ring
  · have hc := nums_dens_congr a b (b' := Function.update b (n + 2) (b (n + 2) + w)) (n + 1)
      (fun k hk => by rw [Function.update_of_ne (by omega)])
    simp only [contFrac_contsAux_succ]
    rw [contFrac_nums_step, contFrac_dens_step, ← (hc (n + 1) le_rfl).1, ← (hc (n + 1) le_rfl).2,
      ← (hc n (by omega)).1, ← (hc n (by omega)).2, contFrac_nums_step, contFrac_dens_step]
    simp only [Function.update_self, Pair.mk.injEq]
    constructor <;> ring

/-- DLMF 1.12.21: `C_n(w) = (A_n + A_{n-1}w)/(B_n + B_{n-1}w)`, when the nested denominators of
`C_n(w)` do not vanish (`contsAux (n + 1) = ⟨A_n, B_n⟩`, `contsAux n = ⟨A_{n-1}, B_{n-1}⟩`). -/
@[dlmf 1.12.E21]
theorem contFracApprox_eq (n : ℕ) (w : K)
    (ht : ∀ k, 1 ≤ k → k ≤ n → contFracTail a (Function.update b n (b n + w)) k n ≠ 0) :
    contFracApprox a b n w =
      (((contFrac a b).contsAux (n + 1)).a + ((contFrac a b).contsAux n).a * w) /
        (((contFrac a b).contsAux (n + 1)).b + ((contFrac a b).contsAux n).b * w) := by
  rw [contFracApprox, (contFrac_convs'_eq_convs n a _ ht).1]
  have h := contsAux_update_add a b n w
  simp only [contFrac_contsAux_succ] at h
  simp only [convs]
  rw [show (contFrac a (Function.update b n (b n + w))).nums n =
      ((contFrac a b).contsAux (n + 1)).a + ((contFrac a b).contsAux n).a * w from
      congrArg Pair.a h, show (contFrac a (Function.update b n (b n + w))).dens n =
      ((contFrac a b).contsAux (n + 1)).b + ((contFrac a b).contsAux n).b * w from
      congrArg Pair.b h]

/-- DLMF 1.12.21: `C_n(∞) = C_{n-1} = A_{n-1}/B_{n-1}`: the Möbius form of `C_n(w)` tends to
`A_{n-1}/B_{n-1}` as `w → ∞`, when `B_{n-1} ≠ 0`. -/
@[dlmf 1.12.E21]
theorem contFracApprox_tendsto_infty {L : Type*} [NormedField L] (a b : ℕ → L) (n : ℕ)
    (hB : ((contFrac a b).contsAux n).b ≠ 0) :
    Tendsto (fun w => (((contFrac a b).contsAux (n + 1)).a + ((contFrac a b).contsAux n).a * w) /
        (((contFrac a b).contsAux (n + 1)).b + ((contFrac a b).contsAux n).b * w))
      (Bornology.cobounded L)
      (𝓝 (((contFrac a b).contsAux n).a / ((contFrac a b).contsAux n).b)) := by
  set P := ((contFrac a b).contsAux (n + 1)).a
  set Q := ((contFrac a b).contsAux n).a
  set R := ((contFrac a b).contsAux (n + 1)).b
  set T := ((contFrac a b).contsAux n).b
  have hlim : Tendsto (fun u : L => (P * u + Q) / (R * u + T)) (𝓝 0) (𝓝 (Q / T)) := by
    have hid : Tendsto (id : L → L) (𝓝 0) (𝓝 0) := tendsto_id
    have h := ((tendsto_const_nhds (x := P)).mul hid |>.add
      (tendsto_const_nhds (x := Q))).div ((tendsto_const_nhds (x := R)).mul hid |>.add
      (tendsto_const_nhds (x := T))) (by simpa using hB)

    simp only [mul_zero, zero_add] at h
    exact h
  refine (hlim.comp tendsto_inv₀_cobounded).congr' ?_
  filter_upwards [Bornology.eventually_ne_cobounded (0 : L)] with w hw
  simp only [Function.comp_apply]
  rw [← mul_div_mul_right (P + Q * w) _ (inv_ne_zero hw)]
  congr 1 <;> field_simp

/-! ## Existence of convergents -/

/-- DLMF 1.12.22, finite-valued form: a sequence `C_n` in `K` is the sequence of convergents
`A_n/B_n` of a continued fraction with `a_n ≠ 0` and finite convergents (`B_n ≠ 0`) iff
`C_n ≠ C_{n-1}` for all `n ≥ 1`. (The condition `C₀ ≠ ∞` is automatic for `C₀ ∈ K`; the
construction gives `B_n = 1`.) -/
@[dlmf 1.12.E22]
theorem exists_contFrac_convs_iff (C : ℕ → K) :
    (∃ a b : ℕ → K, (∀ k, 1 ≤ k → a k ≠ 0) ∧ (∀ n, (contFrac a b).dens n ≠ 0) ∧
      ∀ n, (contFrac a b).convs n = C n) ↔ ∀ n, C (n + 1) ≠ C n := by
  constructor
  · rintro ⟨a, b, ha, hB, hC⟩ n h
    have hd := contFrac_convs_sub a b n (hB n) (hB (n + 1))
    rw [hC, hC, h, sub_self] at hd
    refine (div_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num))
      (prod_ne_zero_iff.mpr fun k _ => ha (k + 1) (by omega))) (mul_ne_zero (hB n) (hB (n + 1))))
      hd.symm
  · intro hC
    set a : ℕ → K := fun k =>
      if k = 1 then C 1 - C 0 else (C k - C (k - 1)) / (C (k - 2) - C (k - 1))
      with ha
    set b : ℕ → K := fun k => if k = 0 then C 0 else if k = 1 then 1 else 1 - a k with hb
    have key : ∀ n, (contFrac a b).dens n = 1 ∧ (contFrac a b).nums n = C n := by
      intro n
      induction n using Nat.strong_induction_on with
      | _ n ih =>
        rcases n with _ | _ | n
        · simp [hb]
        · simp [contFrac_dens_one, contFrac_nums_one, ha, hb]
        · obtain ⟨d1, n1⟩ := ih (n + 1) (by omega)
          obtain ⟨d0, n0⟩ := ih n (by omega)
          rw [contFrac_dens_step, contFrac_nums_step, d1, d0, n1, n0]
          have hne : C n - C (n + 1) ≠ 0 := sub_ne_zero.mpr (hC n).symm
          simp only [hb, ha, show n + 2 ≠ 1 by omega, show n + 2 ≠ 0 by omega, ↓reduceIte,
            show n + 2 - 1 = n + 1 by omega, show n + 2 - 2 = n by omega]
          constructor
          · ring
          · field_simp
            ring
    refine ⟨a, b, fun k hk => ?_, fun n => by rw [(key n).1]; exact one_ne_zero, fun n => ?_⟩
    · rcases k with _ | _ | k
      · omega
      · simpa [ha] using sub_ne_zero.mpr (hC 0)
      · simp only [ha, show k + 2 ≠ 1 by omega, ↓reduceIte, show k + 2 - 1 = k + 1 by omega,
          show k + 2 - 2 = k by omega]
        exact div_ne_zero (sub_ne_zero.mpr (hC (k + 1))) (sub_ne_zero.mpr (hC k).symm)
    · simp only [convs]
      rw [(key n).1, (key n).2, div_one]

/-! ## Contractions: even and odd parts -/

/-- The continuants of the even part, for any pair of sequences with the recurrences. -/
private theorem evenPart_seq {X X' : ℕ → K}
    (hX : ∀ n, X (n + 2) = b (n + 2) * X (n + 1) + a (n + 2) * X n)
    (hX' : ∀ n, X' (n + 2) = evenPartB a b (n + 2) * X' (n + 1) + evenPartA a b (n + 2) * X' n)
    (h0 : X' 0 = X 0) (h1 : X' 1 = X 2) :
    ∀ n, X' n = (∏ k ∈ Ico 1 n, b (2 * k)) * X (2 * n) := by
  have key : ∀ n, X' n = (∏ k ∈ Ico 1 n, b (2 * k)) * X (2 * n) ∧
      X' (n + 1) = (∏ k ∈ Ico 1 (n + 1), b (2 * k)) * X (2 * (n + 1)) := by
    intro n
    induction n with
    | zero => exact ⟨by simp [h0], by simp [h1]⟩
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      rw [hX' n, ih.1, ih.2]
      rcases n with _ | k
      · have e2 : X 2 = b 2 * X 1 + a 2 * X 0 := hX 0
        have e3 : X 3 = b 3 * X 2 + a 3 * X 1 := hX 1
        have e4 : X 4 = b 4 * X 3 + a 4 * X 2 := hX 2
        have hB : evenPartB a b 2 = a 3 * b 4 + b 2 * (a 4 + b 3 * b 4) := rfl
        have hA : evenPartA a b 2 = -(a 2 * a 3 * b 4) := rfl
        simp only [zero_add, Ico_self, prod_empty, one_mul, mul_zero, mul_one,
          show (2 : ℕ) * 2 = 4 from rfl, Nat.reduceAdd, hB, hA]
        rw [Finset.prod_Ico_succ_top (by norm_num), Ico_self, prod_empty, one_mul,
          show Ico 1 0 = (∅ : Finset ℕ) by decide, prod_empty, one_mul]
        linear_combination (-b 2 * b 4) * e3 + (-b 2) * e4 + (a 3 * b 4) * e2
      · have e2 : X (2 * k + 4) = b (2 * k + 4) * X (2 * k + 3) + a (2 * k + 4) * X (2 * k + 2) :=
          hX (2 * k + 2)
        have e3 : X (2 * k + 5) = b (2 * k + 5) * X (2 * k + 4) + a (2 * k + 5) * X (2 * k + 3) :=
          hX (2 * k + 3)
        have e4 : X (2 * k + 6) = b (2 * k + 6) * X (2 * k + 5) + a (2 * k + 6) * X (2 * k + 4) :=
          hX (2 * k + 4)
        have hB : evenPartB a b (k + 1 + 2) = a (2 * k + 5) * b (2 * k + 6) +
            b (2 * k + 4) * (a (2 * k + 6) + b (2 * k + 5) * b (2 * k + 6)) := rfl
        have hA : evenPartA a b (k + 1 + 2) =
            -(a (2 * k + 4) * a (2 * k + 5) * b (2 * k + 2) * b (2 * k + 6)) := rfl
        have hc1 : ∏ i ∈ Ico 1 (k + 1 + 1), b (2 * i) = (∏ i ∈ Ico 1 (k + 1), b (2 * i)) *
            b (2 * k + 2) := Finset.prod_Ico_succ_top (by omega) _
        have hc2 : ∏ i ∈ Ico 1 (k + 1 + 1 + 1), b (2 * i) =
            (∏ i ∈ Ico 1 (k + 1 + 1), b (2 * i)) * b (2 * k + 4) :=
          Finset.prod_Ico_succ_top (by omega) _
        rw [hB, hA, hc2, hc1]
        rw [show 2 * (k + 1) = 2 * k + 2 by ring, show 2 * (k + 1 + 1) = 2 * k + 4 by ring,
          show 2 * (k + 1 + 1 + 1) = 2 * k + 6 by ring]
        set c := ∏ i ∈ Ico 1 (k + 1), b (2 * i)
        linear_combination (-c * b (2 * k + 2) * b (2 * k + 4) * b (2 * k + 6)) * e3 +
          (-c * b (2 * k + 2) * b (2 * k + 4)) * e4 +
          (a (2 * k + 5) * b (2 * k + 6) * c * b (2 * k + 2)) * e2
  exact fun n => (key n).1

/-- The continuants of the odd part, for any pair of sequences with the recurrences. -/
private theorem oddPart_seq {X X' : ℕ → K}
    (hX : ∀ n, X (n + 2) = b (n + 2) * X (n + 1) + a (n + 2) * X n)
    (hX' : ∀ n, X' (n + 2) = oddPartB a b (n + 2) * X' (n + 1) + oddPartA a b (n + 2) * X' n)
    (h0 : b 1 * X' 0 = X 1) (h1 : b 1 * X' 1 = b 1 * X 3) :
    ∀ n, b 1 * X' n = (∏ k ∈ range n, b (2 * k + 1)) * X (2 * n + 1) := by
  have key : ∀ n, b 1 * X' n = (∏ k ∈ range n, b (2 * k + 1)) * X (2 * n + 1) ∧
      b 1 * X' (n + 1) = (∏ k ∈ range (n + 1), b (2 * k + 1)) * X (2 * (n + 1) + 1) := by
    intro n
    induction n with
    | zero => exact ⟨by simp [h0], by simp [h1]⟩
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      have e2 : X (2 * n + 3) = b (2 * n + 3) * X (2 * n + 2) + a (2 * n + 3) * X (2 * n + 1) :=
        hX (2 * n + 1)
      have e3 : X (2 * n + 4) = b (2 * n + 4) * X (2 * n + 3) + a (2 * n + 4) * X (2 * n + 2) :=
        hX (2 * n + 2)
      have e4 : X (2 * n + 5) = b (2 * n + 5) * X (2 * n + 4) + a (2 * n + 5) * X (2 * n + 3) :=
        hX (2 * n + 3)
      have hB : oddPartB a b (n + 2) = a (2 * n + 4) * b (2 * n + 5) +
          b (2 * n + 3) * (a (2 * n + 5) + b (2 * n + 4) * b (2 * n + 5)) := rfl
      have hA : oddPartA a b (n + 2) =
          -(a (2 * n + 3) * a (2 * n + 4) * b (2 * n + 1) * b (2 * n + 5)) := rfl
      have hc1 : ∏ i ∈ range (n + 1), b (2 * i + 1) = (∏ i ∈ range n, b (2 * i + 1)) *
          b (2 * n + 1) := prod_range_succ _ _
      have hc2 : ∏ i ∈ range (n + 1 + 1), b (2 * i + 1) =
          (∏ i ∈ range (n + 1), b (2 * i + 1)) * b (2 * n + 3) := prod_range_succ _ _
      rw [hX' n, mul_add, ← mul_assoc, mul_comm (b 1), mul_assoc, ih.2, ← mul_assoc (b 1),
        mul_comm (b 1), mul_assoc, ih.1, hB, hA, hc2, hc1,
        show 2 * (n + 1) + 1 = 2 * n + 3 by ring, show 2 * (n + 1 + 1) + 1 = 2 * n + 5 by ring]
      set c := ∏ i ∈ range n, b (2 * i + 1)
      linear_combination (-c * b (2 * n + 1) * b (2 * n + 3) * b (2 * n + 5)) * e3 +
        (-c * b (2 * n + 1) * b (2 * n + 3)) * e4 +
        (a (2 * n + 4) * b (2 * n + 5) * c * b (2 * n + 1)) * e2
  exact fun n => (key n).1

/-- Continuants of the even part: `A'_n = c_n A_{2n}`, `B'_n = c_n B_{2n}`,
`c_n = ∏_{k=1}^{n-1} b_{2k}`. -/
private theorem evenPart_nums_dens (n : ℕ) :
    (contFrac (evenPartA a b) (evenPartB a b)).nums n =
        (∏ k ∈ Ico 1 n, b (2 * k)) * (contFrac a b).nums (2 * n) ∧
      (contFrac (evenPartA a b) (evenPartB a b)).dens n =
        (∏ k ∈ Ico 1 n, b (2 * k)) * (contFrac a b).dens (2 * n) :=
  ⟨evenPart_seq a b (contFrac_nums_step a b) (contFrac_nums_step _ _)
    (by rw [contFrac_nums_zero, contFrac_nums_zero]; rfl)
    (by rw [contFrac_nums_one, contFrac_nums_step, contFrac_nums_one, contFrac_nums_zero]
        simp only [evenPartA, evenPartB]; ring) n,
  evenPart_seq a b (contFrac_dens_step a b) (contFrac_dens_step _ _)
    (by rw [contFrac_dens_zero, contFrac_dens_zero])
    (by rw [contFrac_dens_one, contFrac_dens_step, contFrac_dens_one, contFrac_dens_zero]
        simp only [evenPartB]; ring) n⟩

/-- Continuants of the odd part: `b₁ A'_n = d_n A_{2n+1}`, `b₁ B'_n = d_n B_{2n+1}`,
`d_n = ∏_{k=0}^{n-1} b_{2k+1}`. -/
private theorem oddPart_nums_dens (hb1 : b 1 ≠ 0) (n : ℕ) :
    b 1 * (contFrac (oddPartA a b) (oddPartB a b)).nums n =
        (∏ k ∈ range n, b (2 * k + 1)) * (contFrac a b).nums (2 * n + 1) ∧
      b 1 * (contFrac (oddPartA a b) (oddPartB a b)).dens n =
        (∏ k ∈ range n, b (2 * k + 1)) * (contFrac a b).dens (2 * n + 1) :=
  ⟨oddPart_seq a b (contFrac_nums_step a b) (contFrac_nums_step _ _)
    (by rw [contFrac_nums_zero, contFrac_nums_one]; simp only [oddPartB]; field_simp; ring)
    (by rw [contFrac_nums_one, contFrac_nums_step, contFrac_nums_step, contFrac_nums_one,
          contFrac_nums_zero]
        simp only [oddPartA, oddPartB]; field_simp; ring) n,
  oddPart_seq a b (contFrac_dens_step a b) (contFrac_dens_step _ _)
    (by rw [contFrac_dens_zero, contFrac_dens_one, mul_one])
    (by rw [contFrac_dens_one, contFrac_dens_step, contFrac_dens_step, contFrac_dens_one,
          contFrac_dens_zero]
        simp only [oddPartB]; ring) n⟩

/-- Consecutive convergents of a fraction with nonzero partial numerators and finite
convergents are distinct (DLMF 1.12.8). -/
private theorem contFrac_convs_succ_ne {a' b' : ℕ → K} (ha : ∀ k, 1 ≤ k → a' k ≠ 0)
    (hB : ∀ n, (contFrac a' b').dens n ≠ 0) (m : ℕ) :
    (contFrac a' b').convs (m + 1) ≠ (contFrac a' b').convs m := by
  intro h
  have := contFrac_convs_sub a' b' m (hB m) (hB (m + 1))
  rw [h, sub_self] at this
  refine (div_ne_zero (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero))
    (prod_ne_zero_iff.2 fun k _ => ha (k + 1) (by omega))) (mul_ne_zero (hB m) (hB (m + 1))))
    this.symm

/-- If `b_{n+2} = 0` and `a_{n+2} ≠ 0` then `C_{n+2} = C_n`. -/
private theorem contFrac_convs_add_two_eq {n : ℕ} (hb : b (n + 2) = 0) (ha : a (n + 2) ≠ 0) :
    (contFrac a b).convs (n + 2) = (contFrac a b).convs n := by
  simp only [GenContFract.convs]
  rw [contFrac_nums_step, contFrac_dens_step, hb, zero_mul, zero_add, zero_mul, zero_add,
    mul_div_mul_left _ _ ha]

/-- DLMF 1.12.23: if `b_{2k} ≠ 0` (`k ≥ 1`), the continued fraction with elements
`evenPartA a b`, `evenPartB a b` has the convergents `C'_n = C_{2n}` (its continuants are
`∏_{k=1}^{n-1} b_{2k}` times `A_{2n}`, `B_{2n}`); it is the even part of `C`. -/
@[dlmf 1.12.E23]
theorem contFrac_evenPart_convs (hb : ∀ k, 1 ≤ k → b (2 * k) ≠ 0) (n : ℕ) :
    (contFrac (evenPartA a b) (evenPartB a b)).convs n = (contFrac a b).convs (2 * n) := by
  have hc : ∏ k ∈ Ico 1 n, b (2 * k) ≠ 0 :=
    prod_ne_zero_iff.2 fun k hk => hb k (mem_Ico.1 hk).1
  simp only [GenContFract.convs]
  rw [(evenPart_nums_dens a b n).1, (evenPart_nums_dens a b n).2, mul_div_mul_left _ _ hc]

/-- DLMF §1.12(iv): the even part exists iff `b_{2k} ≠ 0`, `k ≥ 1`: for a fraction with
`a_n ≠ 0` and finite convergents (`B_n ≠ 0`), there is a fraction with nonzero partial
numerators whose convergents are `C_{2n}` iff no `b_{2k}` (`k ≥ 1`) vanishes. -/
@[dlmf 1.12.iv]
theorem exists_evenPart_iff (ha : ∀ k, 1 ≤ k → a k ≠ 0) (hB : ∀ n, (contFrac a b).dens n ≠ 0) :
    (∃ a' b' : ℕ → K, (∀ k, 1 ≤ k → a' k ≠ 0) ∧ (∀ n, (contFrac a' b').dens n ≠ 0) ∧
      ∀ n, (contFrac a' b').convs n = (contFrac a b).convs (2 * n)) ↔
      ∀ k, 1 ≤ k → b (2 * k) ≠ 0 := by
  constructor
  · rintro ⟨a', b', ha', hB', hC⟩ k hk hbk
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    have h1 := contFrac_convs_add_two_eq a b (n := 2 * m)
      (by rw [show 2 * m + 2 = 2 * (m + 1) by ring]; exact hbk) (ha _ (by omega))
    refine contFrac_convs_succ_ne ha' hB' m ?_
    rw [hC, hC, show 2 * (m + 1) = 2 * m + 2 by ring, h1]
  · intro hb
    refine ⟨evenPartA a b, evenPartB a b, fun k hk => ?_, fun n => ?_,
      contFrac_evenPart_convs a b hb⟩
    · rcases k with _ | _ | _ | k
      · omega
      · exact mul_ne_zero (ha 1 le_rfl) (hb 1 le_rfl)
      · exact neg_ne_zero.2 (mul_ne_zero (mul_ne_zero (ha 2 (by omega)) (ha 3 (by omega)))
          (hb 2 (by omega)))
      · exact neg_ne_zero.2 (mul_ne_zero (mul_ne_zero (mul_ne_zero (ha _ (by omega))
          (ha _ (by omega))) (hb (k + 1) (by omega))) (hb (k + 3) (by omega)))
    · rw [(evenPart_nums_dens a b n).2]
      exact mul_ne_zero (prod_ne_zero_iff.2 fun k hk => hb k (mem_Ico.1 hk).1) (hB _)

/-- DLMF 1.12.24: if `b_{2k+1} ≠ 0` (`k ≥ 0`), the continued fraction with elements
`oddPartA a b`, `oddPartB a b` has the convergents `C'_n = C_{2n+1}`; it is the odd part
of `C`. -/
@[dlmf 1.12.E24]
theorem contFrac_oddPart_convs (hb : ∀ k, b (2 * k + 1) ≠ 0) (n : ℕ) :
    (contFrac (oddPartA a b) (oddPartB a b)).convs n = (contFrac a b).convs (2 * n + 1) := by
  have hb1 : b 1 ≠ 0 := hb 0
  have hc : ∏ k ∈ range n, b (2 * k + 1) ≠ 0 := prod_ne_zero_iff.2 fun k _ => hb k
  simp only [GenContFract.convs]
  rw [← mul_div_mul_left _ _ hb1, (oddPart_nums_dens a b hb1 n).1,
    (oddPart_nums_dens a b hb1 n).2, mul_div_mul_left _ _ hc]

/-- DLMF §1.12(iv): the odd part exists iff `b_{2k+1} ≠ 0`, `k ≥ 0` (for a fraction with
`a_n ≠ 0` and finite convergents). -/
@[dlmf 1.12.iv]
theorem exists_oddPart_iff (ha : ∀ k, 1 ≤ k → a k ≠ 0) (hB : ∀ n, (contFrac a b).dens n ≠ 0) :
    (∃ a' b' : ℕ → K, (∀ k, 1 ≤ k → a' k ≠ 0) ∧ (∀ n, (contFrac a' b').dens n ≠ 0) ∧
      ∀ n, (contFrac a' b').convs n = (contFrac a b).convs (2 * n + 1)) ↔
      ∀ k, b (2 * k + 1) ≠ 0 := by
  constructor
  · rintro ⟨a', b', ha', hB', hC⟩ k hbk
    rcases k with _ | m
    · exact hB 1 (by rw [contFrac_dens_one]; exact hbk)
    · have h1 := contFrac_convs_add_two_eq a b (n := 2 * m + 1)
        (by rw [show 2 * m + 1 + 2 = 2 * (m + 1) + 1 by ring]; exact hbk) (ha _ (by omega))
      refine contFrac_convs_succ_ne ha' hB' m ?_
      rw [hC, hC, show 2 * (m + 1) + 1 = 2 * m + 1 + 2 by ring, h1]
  · intro hb
    have hb1 : b 1 ≠ 0 := hb 0
    refine ⟨oddPartA a b, oddPartB a b, fun k hk => ?_, fun n => ?_,
      contFrac_oddPart_convs a b hb⟩
    · rcases k with _ | _ | k
      · omega
      · exact neg_ne_zero.2 (div_ne_zero (mul_ne_zero (mul_ne_zero (ha 1 le_rfl)
          (ha 2 (by omega))) (hb 1)) hb1)
      · exact neg_ne_zero.2 (mul_ne_zero (mul_ne_zero (mul_ne_zero (ha _ (by omega))
          (ha _ (by omega))) (hb k)) (hb (k + 2)))
    · intro h0
      have := (oddPart_nums_dens a b hb1 n).2
      rw [h0, mul_zero] at this
      exact mul_ne_zero (prod_ne_zero_iff.2 fun k _ => hb k) (hB _) this.symm

end DLMF.AlgebraicAnalytic
