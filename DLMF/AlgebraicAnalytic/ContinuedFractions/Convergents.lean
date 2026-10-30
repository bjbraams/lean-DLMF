/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AlgebraicAnalytic.ContinuedFractions.Basic

/-!
# Convergents of continued fractions (DLMF §§1.12(ii)–1.12(iv))

For `contFrac a b = b₀ + a₁/(b₁ + a₂/(b₂ + ⋯))` (DLMF indexing) with canonical numerators
`A_n = (contFrac a b).nums n` and denominators `B_n = (contFrac a b).dens n`:

* the recurrences 1.12.5–1.12.6 (with `A_{-1} = 1`, `B_{-1} = 0` as Mathlib's
  `contsAux 0 = ⟨1, 0⟩`), the nested form 1.12.4 of `C_n = A_n/B_n`;
* the determinant formula 1.12.7 and its consequences 1.12.8–1.12.14;
* equivalence transformations 1.12.15–1.12.17, Euler's series fraction 1.12.18–1.12.19;
* the fractional transformation 1.12.20–1.12.21;
* the characterization 1.12.22 of sequences of convergents (finite-valued form);
* even and odd parts 1.12.23–1.12.24.

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
lemma g1d_det_ne_zero (m : ℕ) (ha : ∀ k, 1 ≤ k → k ≤ m + 1 → a k ≠ 0) :
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
  have hd := g1d_det_ne_zero a b m ha
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
  have hd := g1d_det_ne_zero a b m ha
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
  have hd := g1d_det_ne_zero a b m ha
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
  have hd := g1d_det_ne_zero a b m ha
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
lemma g1d_unitFactor_ne_zero (ha : ∀ n, 1 ≤ n → a n ≠ 0) (n : ℕ) : contFracUnitFactor a n ≠ 0 := by
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
  refine contFracEquiv_of_scale a b (contFracUnitFactor a) rfl (g1d_unitFactor_ne_zero a ha)
    (fun n hn => ?_) (fun n => rfl)
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h1 := ha (m + 1) (by omega)
  have h2 := g1d_unitFactor_ne_zero a ha m
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
lemma g1d_conts_congr {b' : ℕ → K} (m : ℕ) (hb : ∀ k ≤ m, b k = b' k) :
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
lemma g1d_conts_update (n : ℕ) (w : K) :
    (contFrac a (Function.update b n (b n + w))).contsAux (n + 1) =
      ⟨((contFrac a b).contsAux (n + 1)).a + ((contFrac a b).contsAux n).a * w,
        ((contFrac a b).contsAux (n + 1)).b + ((contFrac a b).contsAux n).b * w⟩ := by
  rcases n with _ | _ | n
  · simp [zeroth_contAux_eq_one_zero]
  · simp only [contFrac_contsAux_succ, contFrac_nums_one, contFrac_dens_one, contFrac_nums_zero,
      contFrac_dens_zero]
    simp
    ring
  · have hc := g1d_conts_congr a b (b' := Function.update b (n + 2) (b (n + 2) + w)) (n + 1)
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
  have h := g1d_conts_update a b n w
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

/-- DLMF 1.12.23: if `b_{2k} ≠ 0` (`k ≥ 1`), the continued fraction with elements
`evenPartA a b`, `evenPartB a b` has the convergents `C'_n = C_{2n}` (its continuants are
`∏_{k=1}^{n-1} b_{2k}` times `A_{2n}`, `B_{2n}`); it is the even part of `C`. -/
@[dlmf 1.12.E23]
theorem contFrac_evenPart_convs (hb : ∀ k, 1 ≤ k → b (2 * k) ≠ 0) (n : ℕ) :
    (contFrac (evenPartA a b) (evenPartB a b)).convs n = (contFrac a b).convs (2 * n) := by
  sorry

/-- DLMF §1.12(iv): the even part exists iff `b_{2k} ≠ 0`, `k ≥ 1`: for a fraction with
`a_n ≠ 0` and finite convergents (`B_n ≠ 0`), there is a fraction with nonzero partial
numerators whose convergents are `C_{2n}` iff no `b_{2k}` (`k ≥ 1`) vanishes. -/
@[dlmf 1.12.iv]
theorem exists_evenPart_iff (ha : ∀ k, 1 ≤ k → a k ≠ 0) (hB : ∀ n, (contFrac a b).dens n ≠ 0) :
    (∃ a' b' : ℕ → K, (∀ k, 1 ≤ k → a' k ≠ 0) ∧ (∀ n, (contFrac a' b').dens n ≠ 0) ∧
      ∀ n, (contFrac a' b').convs n = (contFrac a b).convs (2 * n)) ↔
      ∀ k, 1 ≤ k → b (2 * k) ≠ 0 := by
  sorry

/-- DLMF 1.12.24: if `b_{2k+1} ≠ 0` (`k ≥ 0`), the continued fraction with elements
`oddPartA a b`, `oddPartB a b` has the convergents `C'_n = C_{2n+1}`; it is the odd part
of `C`. -/
@[dlmf 1.12.E24]
theorem contFrac_oddPart_convs (hb : ∀ k, b (2 * k + 1) ≠ 0) (n : ℕ) :
    (contFrac (oddPartA a b) (oddPartB a b)).convs n = (contFrac a b).convs (2 * n + 1) := by
  sorry

/-- DLMF §1.12(iv): the odd part exists iff `b_{2k+1} ≠ 0`, `k ≥ 0` (for a fraction with
`a_n ≠ 0` and finite convergents). -/
@[dlmf 1.12.iv]
theorem exists_oddPart_iff (ha : ∀ k, 1 ≤ k → a k ≠ 0) (hB : ∀ n, (contFrac a b).dens n ≠ 0) :
    (∃ a' b' : ℕ → K, (∀ k, 1 ≤ k → a' k ≠ 0) ∧ (∀ n, (contFrac a' b').dens n ≠ 0) ∧
      ∀ n, (contFrac a' b').convs n = (contFrac a b).convs (2 * n + 1)) ↔
      ∀ k, b (2 * k + 1) ≠ 0 := by
  sorry

end DLMF.AlgebraicAnalytic
