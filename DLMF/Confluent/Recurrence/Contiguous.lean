/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Confluent.Whittaker
public import DLMFMathlib.Analysis.Calculus.DifferentialOperators
public import DLMF.Confluent.Basic.KummerContiguous

/-!
# Contiguous relations for Kummer and Tricomi functions

This file proves the contiguous relations of Tricomi's `U` and the iterated-derivative formulas
for `M` (DLMF §13.3). The contiguous relations of Kummer's `M`, Kummer's equation as a contiguous
relation (DLMF 13.3.13) and `M' = (a/b) M(a+1,b+1)` (DLMF 13.3.15) are in
`DLMF.Confluent.Basic.KummerContiguous`.

## Main results

* `kummerU_contiguous_a`, `kummerU_contiguous_b`, `kummerU_contiguous_a_b`,
  `kummerU_contiguous_shift_a`, `kummerU_contiguous_mixed`, `kummerU_contiguous_down`:
  the contiguous relations for `U` (DLMF 13.3.7–13.3.12), for every second parameter.
* `kummerU_ode_contiguous`: Kummer's equation as a contiguous relation (DLMF 13.3.14).
* `iteratedDeriv_kummerM`, `iterate_mulDerivMul_kummerM`, `iteratedDeriv_mul_cpow_kummerM`,
  `iterate_mulDerivMul_exp_neg_kummerM`, `iteratedDeriv_exp_neg_kummerM`,
  `iteratedDeriv_mul_cpow_exp_neg_kummerM`: iterated derivatives (DLMF 13.3.16–13.3.21).
* `mulDerivMul_eq_mul_iteratedDeriv`: `(z d/dz z)ⁿ` in terms of ordinary derivatives
  (DLMF 13.3.29).

## Implementation notes

Denominator parameters of `kummerM` stay off the nonpositive integers. The operator
`(z d/dz z)` is `mulDerivMul`. The relations for `U` are proved first at noninteger second
parameter and extended to integers by continuity in the parameter.
-/

@[expose] public section

open Complex Filter FormalMultilinearSeries

open scoped Real Topology

open DLMF.Hypergeometric

noncomputable section

namespace DLMF.Confluent

/-- Identity under the stated parameter and domain assumptions: `mulDerivMul^[n] f z = z ^ n *
iteratedDeriv n (fun w => w ^ n * f w) z`. -/
@[dlmf 13.3.E29]
theorem mulDerivMul_eq_mul_iteratedDeriv (n : ℕ) (f : ℂ → ℂ) (hf : ContDiff ℂ ⊤ f) {z : ℂ} :
    mulDerivMul^[n] f z = z ^ n * iteratedDeriv n (fun w => w ^ n * f w) z := by
  exact DLMF.Hypergeometric.iterate_mulDerivMul_eq n hf z

/-- `(b-1) b M(a-1,b-1,z) + (z-b+1) b M(a,b,z) - a z M(a+1,b+1,z) = 0`. -/
lemma kummerM_contiguous_up_aux {a b z : ℂ} (hb1 : ∀ k : ℕ, b - 1 ≠ -k) :
    (b - 1) * b * kummerM (a - 1) (b - 1) z + (z - b + 1) * b * kummerM a b z -
      a * z * kummerM (a + 1) (b + 1) z = 0 := by
  have hb : ∀ k : ℕ, b ≠ -k := by simpa using not_neg_nat_add_nat hb1 1
  have hb0 : b ≠ 0 := by simpa using hb 0
  have h4 := kummerM_contiguous_shift_a (a := a) hb1 (z := z)
  rw [sub_add_cancel] at h4
  have h6 := kummerM_contiguous_down (a := a) hb1 (z := z)
  have hC := z_mul_deriv_kummerM_eq_shift_a_pred (a := a) hb z
  have h2 := deriv_kummerM (a := a) hb hb0 (z := z)
  have h3 : b * (a / b * kummerM (a + 1) (b + 1) z) = a * kummerM (a + 1) (b + 1) z := by
    field_simp
  rw [h2] at hC
  linear_combination z * h3 - b * hC - b * h6 - b * h4

/-- `(b-1) b M(a-1,b-1,z) - (b-1) b M(a,b,z) + (b-a) z M(a,b+1,z) = 0`. -/
theorem kummerM_contiguous_up_shift_aux {a b z : ℂ} (hb1 : ∀ k : ℕ, b - 1 ≠ -k) :
    (b - 1) * b * kummerM (a - 1) (b - 1) z - (b - 1) * b * kummerM a b z +
      (b - a) * z * kummerM a (b + 1) z = 0 := by
  have h4 := kummerM_contiguous_shift_a (a := a) hb1 (z := z)
  rw [sub_add_cancel] at h4
  have h2 := kummerM_contiguous_b (a := a) hb1 (z := z)
  linear_combination h2 - b * h4

/-! ### Tricomi's contiguous relations

Each relation is first proved at noninteger second parameters from the corresponding Kummer
relations, and then transferred to integer parameters through
`tendsto_kummerU_add_intCast`. The transfer needs `z ≠ 0`: at `z = 0` and integer `b`
the totalized `kummerU` has no continued value. -/

/-- If `f` vanishes on `ℂ \ ℤ` and tends to `L` along `ℂ \ ℤ` at `b`, then `L = 0`. -/
theorem eq_zero_of_tendsto_integerComplement {f : ℂ → ℂ} {b L : ℂ}
    (hf : Tendsto f (𝓝[integerComplement] b) (𝓝 L))
    (h0 : ∀ c ∈ integerComplement, f c = 0) : L = 0 := by
  have := integerComplement_nhdsWithin_neBot b
  exact tendsto_nhds_unique hf (tendsto_const_nhds.congr'
    (eventually_nhdsWithin_of_forall fun c hc => (h0 c hc).symm))

/-- The identity tends to `b` along `ℂ \ ℤ` at `b`. -/
theorem tendsto_id_integerComplement (b : ℂ) :
    Tendsto (fun c : ℂ => c) (𝓝[integerComplement] b) (𝓝 b) :=
  (continuous_id.tendsto b).mono_left nhdsWithin_le_nhds

/-- For `z ≠ 0`, `U(a, c-1, z) → U(a, b-1, z)` as `c → b` through `ℂ \ ℤ`. -/
theorem tendsto_kummerU_sub_one (a b : ℂ) {z : ℂ} (hz : z ≠ 0) :
    Tendsto (fun c => kummerU a (c - 1) z) (𝓝[integerComplement] b)
      (𝓝 (kummerU a (b - 1) z)) := by
  have h := tendsto_kummerU_add_intCast a b (-1) hz
  push_cast at h
  simpa [sub_eq_add_neg] using h

/-- For `z ≠ 0`, `U(a, c+1, z) → U(a, b+1, z)` as `c → b` through `ℂ \ ℤ`. -/
theorem tendsto_kummerU_add_one (a b : ℂ) {z : ℂ} (hz : z ≠ 0) :
    Tendsto (fun c => kummerU a (c + 1) z) (𝓝[integerComplement] b)
      (𝓝 (kummerU a (b + 1) z)) := by
  simpa using tendsto_kummerU_add_intCast a b 1 hz

/-- For `z ≠ 0`, `U(a, c+2, z) → U(a, b+2, z)` as `c → b` through `ℂ \ ℤ`. -/
theorem tendsto_kummerU_add_two (a b : ℂ) {z : ℂ} (hz : z ≠ 0) :
    Tendsto (fun c => kummerU a (c + 2) z) (𝓝[integerComplement] b)
      (𝓝 (kummerU a (b + 2) z)) := by
  simpa using tendsto_kummerU_add_intCast a b 2 hz

/-- `ℂ \ ℤ` is invariant under integer translations. -/
theorem intCompl_add_int {c : ℂ} (hc : c ∈ integerComplement) (k : ℤ) :
    c + (k : ℂ) ∈ integerComplement := (add_intCast_mem_integerComplement k).mpr hc

/-- If `c ∉ ℤ` then `c - 1 ∉ ℤ`. -/
theorem intCompl_sub_one {c : ℂ} (hc : c ∈ integerComplement) : c - 1 ∈ integerComplement := by
  simpa [sub_eq_add_neg] using intCompl_add_int hc (-1)

/-- If `c ∉ ℤ` then `c + 1 ∉ ℤ`. -/
theorem intCompl_add_one {c : ℂ} (hc : c ∈ integerComplement) : c + 1 ∈ integerComplement := by
  simpa using intCompl_add_int hc 1

/-- If `c ∉ ℤ` then `-c ∉ ℤ`. -/
theorem intCompl_neg {c : ℂ} (hc : c ∈ integerComplement) : -c ∈ integerComplement :=
  fun ⟨k, hk⟩ => hc ⟨-k, by push_cast; rw [hk]; ring⟩

/-- If `c ∉ ℤ` then `k - c ∉ ℤ` for integer `k`. -/
theorem intCompl_int_sub {c : ℂ} (hc : c ∈ integerComplement) (k : ℤ) :
    (k : ℂ) - c ∈ integerComplement := by
  simpa [sub_eq_add_neg, add_comm] using intCompl_add_int (intCompl_neg hc) k

/-- If `c ∉ ℤ` then `c - k ∉ ℤ` for integer `k`. -/
theorem intCompl_sub_int {c : ℂ} (hc : c ∈ integerComplement) (k : ℤ) :
    c - (k : ℂ) ∈ integerComplement := by
  have := intCompl_add_int hc (-k)
  push_cast at this
  simpa [sub_eq_add_neg] using this

/-- For noninteger `c` and `z ≠ 0`, `U(a,c,z) - a U(a+1,c,z) - U(a,c-1,z) = 0` (DLMF 13.3.9). -/
theorem kummerU_contiguous_a_b_of_mem {a c z : ℂ} (hc : c ∈ integerComplement) (hz : z ≠ 0) :
    kummerU a c z - a * kummerU (a + 1) c z - kummerU a (c - 1) z = 0 := by
  have hc1 := intCompl_sub_one hc
  rw [kummerU_eq_connection _ _ _ (forall_of_mem_integerComplement hc),
    kummerU_eq_connection _ _ _ (forall_of_mem_integerComplement hc),
    kummerU_eq_connection _ _ _ (forall_of_mem_integerComplement hc1)]
  unfold kummerUConnection
  have h2c : (2 : ℂ) - c ∈ integerComplement := by simpa using intCompl_int_sub hc 2
  have E3 := kummerM_contiguous_a_b (a := a) (b := c) (z := z)
    (not_neg_nat_of_mem_integerComplement hc1)
  have E4 := kummerM_contiguous_shift_a (a := a - c + 2) (b := 2 - c) (z := z)
    (not_neg_nat_of_mem_integerComplement h2c)
  have hR := one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (a - c + 1)
  have hS := one_div_Gamma_eq_self_mul_one_div_Gamma_add_one a
  have hG1 := Gamma_add_one (1 - c)
      (integerComplement.ne_zero (by simpa using intCompl_int_sub hc 1))
  have hc2 : c - 2 ∈ integerComplement := by simpa using intCompl_sub_int hc 2
  have hG2 := Gamma_add_one (c - 2) (integerComplement.ne_zero hc2)
  have hzc : z ^ (2 - c) = z * z ^ (1 - c) := by
    rw [show 2 - c = (1 - c) + 1 by ring, cpow_add _ _ hz, cpow_one, mul_comm]
  rw [show a - c + 2 - 1 = a - c + 1 by ring, show 2 - c + 1 = 3 - c by ring] at E4
  rw [show a - c + 1 + 1 = a - c + 2 by ring] at hR
  rw [show 1 - c + 1 = 2 - c by ring] at hG1
  rw [show c - 2 + 1 = c - 1 by ring] at hG2
  rw [show a + 1 - c + 1 = a - c + 2 by ring, show a - (c - 1) + 1 = a - c + 2 by ring,
    show 2 - (c - 1) = 3 - c by ring, show 1 - (c - 1) = 2 - c by ring, show c - 1 -
                                                                    1 = c - 2 by ring]
  rw [hzc]
  simp only [div_eq_mul_inv]
  rw [hR, hS, hG1, hG2]
  linear_combination Gamma (1 - c) * (Gamma (a - c + 2))⁻¹ * E3 +
    Gamma (c - 2) * a * (Gamma (a + 1))⁻¹ * z ^ (1 - c) * E4

/-- For noninteger `c` and `z ≠ 0`, `(c-a) U(a,c,z) + U(a-1,c,z) - z U(a,c+1,z) = 0` (DLMF 13.3.10).
-/
theorem kummerU_contiguous_shift_a_of_mem {a c z : ℂ} (hc : c ∈ integerComplement)
    (hz : z ≠ 0) :
    (c - a) * kummerU a c z + kummerU (a - 1) c z - z * kummerU a (c + 1) z = 0 := by
  have hc1 := intCompl_add_one hc
  rw [kummerU_eq_connection _ _ _ (forall_of_mem_integerComplement hc),
    kummerU_eq_connection _ _ _ (forall_of_mem_integerComplement hc),
    kummerU_eq_connection _ _ _ (forall_of_mem_integerComplement hc1)]
  unfold kummerUConnection
  have h2c : (2 : ℂ) - c ∈ integerComplement := by simpa using intCompl_int_sub hc 2
  have h1c : (1 : ℂ) - c ∈ integerComplement := by simpa using intCompl_int_sub hc 1
  have E4 := kummerM_contiguous_shift_a (a := a) (b := c) (z := z)
      (not_neg_nat_of_mem_integerComplement hc)
  have E3 := kummerM_contiguous_a_b (a := a - c) (b := 2 - c) (z := z)
    (by simpa [show (2 : ℂ) - c - 1 = 1 - c by ring] using not_neg_nat_of_mem_integerComplement h1c)
  rw [show a - c - (2 - c) + 1 = a - 1 by ring, show a - c + 1 = a - c + 1 by ring,
    show (2 : ℂ) - c - 1 = 1 - c by ring] at E3
  have hR := one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (a - c)
  have hS := one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (a - 1)
  rw [show a - 1 + 1 = a by ring] at hS
  have hG0 := Gamma_add_one (-c) (integerComplement.ne_zero (intCompl_neg hc))
  rw [show -c + 1 = 1 - c by ring] at hG0
  have hG1 := Gamma_add_one (c - 1) (integerComplement.ne_zero (intCompl_sub_one hc))
  rw [show c - 1 + 1 = c by ring] at hG1
  have hzc : z ^ (1 - c) = z * z ^ (-c) := by
    rw [show 1 - c = -c + 1 by ring, cpow_add _ _ hz, cpow_one, mul_comm]
  rw [show a - 1 - c + 1 = a - c by ring, show 1 - (c + 1) = -c by ring,
    show a - (c + 1) + 1 = a - c by ring, show c + 1 - 1 = c by ring, show 2 -
                                                                  (c + 1) = 1 - c by ring]
  simp only [div_eq_mul_inv]
  rw [hR, hS, hG0, hG1, hzc]
  linear_combination Gamma (-c) * (Gamma (a - c + 1))⁻¹ * (a - c) * E4 +
    Gamma (c - 1) * (Gamma a)⁻¹ * z ^ (-c) * z * E3

/-- For noninteger `c`, `U(a-1,c,z) + (c-2a-z) U(a,c,z) + a(a-c+1) U(a+1,c,z) = 0` (DLMF 13.3.7). -/
theorem kummerU_contiguous_a_of_mem {a c z : ℂ} (hc : c ∈ integerComplement) :
    kummerU (a - 1) c z + (c - 2 * a - z) * kummerU a c z +
      a * (a - c + 1) * kummerU (a + 1) c z = 0 := by
  rw [kummerU_eq_connection _ _ _ (forall_of_mem_integerComplement hc),
    kummerU_eq_connection _ _ _ (forall_of_mem_integerComplement hc),
    kummerU_eq_connection _ _ _ (forall_of_mem_integerComplement hc)]
  unfold kummerUConnection
  have h2c : (2 : ℂ) - c ∈ integerComplement := by simpa using intCompl_int_sub hc 2
  have E1 := kummerM_contiguous_a (a := a) (b := c) (z := z)
      (not_neg_nat_of_mem_integerComplement hc)
  have E1' := kummerM_contiguous_a (a := a - c + 1) (b := 2 - c) (z := z)
    (not_neg_nat_of_mem_integerComplement h2c)
  rw [show a - c + 1 - 1 = a - c by ring, show a - c + 1 + 1 = a - c + 2 by ring] at E1'
  have hR := one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (a - c)
  have hR' := one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (a - c + 1)
  have hS := one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (a - 1)
  have hS' := one_div_Gamma_eq_self_mul_one_div_Gamma_add_one a
  rw [show a - c + 1 + 1 = a - c + 2 by ring] at hR'
  rw [show a - 1 + 1 = a by ring] at hS
  rw [show a - 1 - c + 1 = a - c by ring, show a + 1 - c + 1 = a - c + 2 by ring]
  simp only [div_eq_mul_inv]
  rw [show a - c + 1 = a - c + 1 by rfl] at hR
  rw [hR, hS, hR', hS']
  linear_combination (-(Gamma (1 - c) * (Gamma (a - c + 2))⁻¹ * (a - c + 1))) * E1 -
    Gamma (c - 1) * (Gamma (a + 1))⁻¹ * z ^ (1 - c) * a * E1'

/-- For noninteger `c` and `z ≠ 0`, `(c-a-1) U(a,c-1,z) + (1-c-z) U(a,c,z) + z U(a,c+1,z) = 0` (DLMF
13.3.8). -/
theorem kummerU_contiguous_b_of_mem {a c z : ℂ} (hc : c ∈ integerComplement) (hz : z ≠ 0) :
    (c - a - 1) * kummerU a (c - 1) z + (1 - c - z) * kummerU a c z +
      z * kummerU a (c + 1) z = 0 := by
  have hcm := intCompl_sub_one hc
  have hcp := intCompl_add_one hc
  rw [kummerU_eq_connection _ _ _ (forall_of_mem_integerComplement hcm),
    kummerU_eq_connection _ _ _ (forall_of_mem_integerComplement hc),
    kummerU_eq_connection _ _ _ (forall_of_mem_integerComplement hcp)]
  unfold kummerUConnection
  have h1c : (1 : ℂ) - c ∈ integerComplement := by simpa using intCompl_int_sub hc 1
  have E2 := kummerM_contiguous_b (a := a) (b := c) (z := z)
      (not_neg_nat_of_mem_integerComplement hcm)
  have E13 := kummerM_ode_contiguous (a := a - c) (b := 1 - c) (z := z)
    (not_neg_nat_of_mem_integerComplement h1c)
  rw [show a - c + 2 = a - c + 2 by ring, show 1 - c + 2 = 3 - c by ring,
    show a - c + 1 = a - c + 1 by ring, show 1 - c + 1 = 2 - c by ring] at E13
  have hR := one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (a - c)
  have hR' := one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (a - c + 1)
  rw [show a - c + 1 + 1 = a - c + 2 by ring] at hR'
  have hG0 := Gamma_add_one (-c) (integerComplement.ne_zero (intCompl_neg hc))
  rw [show -c + 1 = 1 - c by ring] at hG0
  have hG0' := Gamma_add_one (1 - c) (integerComplement.ne_zero h1c)
  rw [show 1 - c + 1 = 2 - c by ring] at hG0'
  have hc2 : c - 2 ∈ integerComplement := by simpa using intCompl_sub_int hc 2
  have hG2 := Gamma_add_one (c - 2) (integerComplement.ne_zero hc2)
  rw [show c - 2 + 1 = c - 1 by ring] at hG2
  have hG1 := Gamma_add_one (c - 1) (integerComplement.ne_zero hcm)
  rw [show c - 1 + 1 = c by ring] at hG1
  have hz1 : z ^ (1 - c) = z * z ^ (-c) := by
    rw [show 1 - c = -c + 1 by ring, cpow_add _ _ hz, cpow_one, mul_comm]
  have hz2 : z ^ (2 - c) = z * z * z ^ (-c) := by
    rw [show 2 - c = -c + 1 + 1 by ring, cpow_add _ _ hz, cpow_add _ _ hz, cpow_one]; ring
  rw [show 1 - (c - 1) = 2 - c by ring, show a - (c - 1) + 1 = a - c + 2 by ring,
    show c - 1 - 1 = c - 2 by ring, show 2 - (c - 1) = 3 - c by ring,
    show 1 - (c + 1) = -c by ring, show a - (c + 1) + 1 = a - c by ring,
    show c + 1 - 1 = c by ring, show 2 - (c + 1) = 1 - c by ring]
  simp only [div_eq_mul_inv]
  rw [hR, hR', hG0', hG0, hG1, hG2, hz1, hz2]
  linear_combination (-(Gamma (-c) * (Gamma (a - c + 2))⁻¹ * (a - c + 1))) * E2 -
    Gamma (c - 2) * (Gamma a)⁻¹ * z ^ (-c) * z * E13

/-- For noninteger `c` and `z ≠ 0`, `(a+z) U(a,c,z) - z U(a,c+1,z) + a(c-a-1) U(a+1,c,z) = 0` (DLMF
13.3.11). -/
theorem kummerU_contiguous_mixed_of_mem {a c z : ℂ} (hc : c ∈ integerComplement)
    (hz : z ≠ 0) :
    (a + z) * kummerU a c z - z * kummerU a (c + 1) z +
      a * (c - a - 1) * kummerU (a + 1) c z = 0 := by
  have hcp := intCompl_add_one hc
  rw [kummerU_eq_connection _ _ _ (forall_of_mem_integerComplement hc),
    kummerU_eq_connection _ _ _ (forall_of_mem_integerComplement hcp),
    kummerU_eq_connection _ _ _ (forall_of_mem_integerComplement hc)]
  unfold kummerUConnection
  have h1c : (1 : ℂ) - c ∈ integerComplement := by simpa using intCompl_int_sub hc 1
  have h2c : (2 : ℂ) - c ∈ integerComplement := by simpa using intCompl_int_sub hc 2
  have E5 := kummerM_contiguous_mixed (a := a) (b := c) (z := z)
      (not_neg_nat_of_mem_integerComplement hc)
  have E3 := kummerM_contiguous_a_b (a := a - c + 1) (b := 2 - c) (z := z)
    (by simpa [show (2 : ℂ) - c - 1 = 1 - c by ring] using not_neg_nat_of_mem_integerComplement h1c)
  have E4 := kummerM_contiguous_shift_a (a := a - c + 1) (b := 1 - c) (z := z)
    (not_neg_nat_of_mem_integerComplement h1c)
  rw [show a - c + 1 - (2 - c) + 1 = a by ring, show a - c + 1 + 1 = a - c + 2 by ring,
    show (2 : ℂ) - c - 1 = 1 - c by ring] at E3
  rw [show a - c + 1 - 1 = a - c by ring, show 1 - c + 1 = 2 - c by ring] at E4
  have hR := one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (a - c)
  have hR' := one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (a - c + 1)
  rw [show a - c + 1 + 1 = a - c + 2 by ring] at hR'
  have hS := one_div_Gamma_eq_self_mul_one_div_Gamma_add_one a
  have hG0 := Gamma_add_one (-c) (integerComplement.ne_zero (intCompl_neg hc))
  rw [show -c + 1 = 1 - c by ring] at hG0
  have hG1 := Gamma_add_one (c - 1) (integerComplement.ne_zero (intCompl_sub_one hc))
  rw [show c - 1 + 1 = c by ring] at hG1
  have hz1 : z ^ (1 - c) = z * z ^ (-c) := by
    rw [show 1 - c = -c + 1 by ring, cpow_add _ _ hz, cpow_one, mul_comm]
  rw [show 1 - (c + 1) = -c by ring, show a - (c + 1) + 1 = a - c by ring,
    show c + 1 - 1 = c by ring, show 2 - (c + 1) = 1 - c by ring,
    show a + 1 - c + 1 = a - c + 2 by ring]
  simp only [div_eq_mul_inv]
  rw [hR, hR', hS, hG0, hG1, hz1]
  linear_combination (-(Gamma (-c) * (Gamma (a - c + 2))⁻¹ * (a - c + 1))) * E5 +
    Gamma (c - 1) * (Gamma (a + 1))⁻¹ * z ^ (-c) * z * a * (E3 - E4)

/-- For noninteger `c` and `z ≠ 0`, `(a-1+z) U(a,c,z) - U(a-1,c,z) + (a-c+1) U(a,c-1,z) = 0` (DLMF
13.3.12). -/
theorem kummerU_contiguous_down_of_mem {a c z : ℂ} (hc : c ∈ integerComplement)
    (hz : z ≠ 0) :
    (a - 1 + z) * kummerU a c z - kummerU (a - 1) c z +
      (a - c + 1) * kummerU a (c - 1) z = 0 := by
  have hcm := intCompl_sub_one hc
  rw [kummerU_eq_connection _ _ _ (forall_of_mem_integerComplement hc),
    kummerU_eq_connection _ _ _ (forall_of_mem_integerComplement hc),
    kummerU_eq_connection _ _ _ (forall_of_mem_integerComplement hcm)]
  unfold kummerUConnection
  have h1c : (1 : ℂ) - c ∈ integerComplement := by simpa using intCompl_int_sub hc 1
  have h2c : (2 : ℂ) - c ∈ integerComplement := by simpa using intCompl_int_sub hc 2
  have E6 := kummerM_contiguous_down (a := a) (b := c) (z := z)
      (not_neg_nat_of_mem_integerComplement hcm)
  have E4 := kummerM_contiguous_shift_a (a := a - c + 1) (b := 2 - c) (z := z)
    (not_neg_nat_of_mem_integerComplement h2c)
  have SBS := kummerM_contiguous_shift_b_succ (a := a - c + 1) (b := 2 - c) (z := z)
    (not_neg_nat_of_mem_integerComplement h2c)
  rw [show a - c + 1 - 1 = a - c by ring, show 2 - c + 1 = 3 - c by ring] at E4
  rw [show a - c + 1 + 1 = a - c + 2 by ring, show 2 - c + 1 = 3 - c by ring,
    show a - c + 1 - (2 - c) = a - 1 by ring] at SBS
  have hR := one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (a - c)
  have hR' := one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (a - c + 1)
  rw [show a - c + 1 + 1 = a - c + 2 by ring] at hR'
  have hS := one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (a - 1)
  rw [show a - 1 + 1 = a by ring] at hS
  have hG0' := Gamma_add_one (1 - c) (integerComplement.ne_zero h1c)
  rw [show 1 - c + 1 = 2 - c by ring] at hG0'
  have hc2 : c - 2 ∈ integerComplement := by simpa using intCompl_sub_int hc 2
  have hG2 := Gamma_add_one (c - 2) (integerComplement.ne_zero hc2)
  rw [show c - 2 + 1 = c - 1 by ring] at hG2
  have hz2 : z ^ (2 - c) = z * z ^ (1 - c) := by
    rw [show 2 - c = (1 - c) + 1 by ring, cpow_add _ _ hz, cpow_one, mul_comm]
  rw [show a - 1 - c + 1 = a - c by ring, show 1 - (c - 1) = 2 - c by ring,
    show a - (c - 1) + 1 = a - c + 2 by ring, show c - 1 - 1 = c - 2 by ring,
    show 2 - (c - 1) = 3 - c by ring]
  simp only [div_eq_mul_inv]
  rw [hR, hR', hS, hG0', hG2, hz2]
  linear_combination Gamma (1 - c) * (Gamma (a - c + 2))⁻¹ * (a - c + 1) * E6 +
    Gamma (c - 2) * (Gamma a)⁻¹ * z ^ (1 - c) * (z * SBS - (a - 1) * E4)

/-- For noninteger `c` and `z ≠ 0`, `(a+1) z U(a+2,c+2,z) + (z-c) U(a+1,c+1,z) - U(a,c,z) = 0`, the
Kummer equation in contiguous form. -/
theorem kummerU_ode_contiguous_of_mem {a c z : ℂ} (hc : c ∈ integerComplement) (hz : z ≠ 0) :
    (a + 1) * z * kummerU (a + 2) (c + 2) z + (z - c) * kummerU (a + 1) (c + 1) z -
      kummerU a c z = 0 := by
  have hcp := intCompl_add_one hc
  have hcpp : c + 2 ∈ integerComplement := by simpa using intCompl_add_int hc 2
  rw [kummerU_eq_connection _ _ _ (forall_of_mem_integerComplement hcpp),
    kummerU_eq_connection _ _ _ (forall_of_mem_integerComplement hcp),
    kummerU_eq_connection _ _ _ (forall_of_mem_integerComplement hc)]
  unfold kummerUConnection
  have hnc : -c ∈ integerComplement := intCompl_neg hc
  have E13 := kummerM_ode_contiguous (a := a) (b := c) (z := z)
      (not_neg_nat_of_mem_integerComplement hc)
  have E2 := kummerM_contiguous_b (a := a - c + 1) (b := 1 - c) (z := z)
    (by simpa [show (1 : ℂ) - c - 1 = -c by ring] using not_neg_nat_of_mem_integerComplement hnc)
  rw [show (1 : ℂ) - c - 1 = -c by ring, show 1 - c + 1 = 2 - c by ring] at E2
  have hG0 := Gamma_add_one (-c) (integerComplement.ne_zero hnc)
  rw [show -c + 1 = 1 - c by ring] at hG0
  have hm1 : -1 - c ∈ integerComplement := by
                                             simpa [sub_eq_add_neg, add_comm] using
                                               intCompl_add_int hnc (-1)
  have hGm := Gamma_add_one (-1 - c) (integerComplement.ne_zero hm1)
  rw [show -1 - c + 1 = -c by ring] at hGm
  have hG1 := Gamma_add_one (c - 1) (integerComplement.ne_zero (intCompl_sub_one hc))
  rw [show c - 1 + 1 = c by ring] at hG1
  have hGc := Gamma_add_one c (integerComplement.ne_zero hc)
  have hS := one_div_Gamma_eq_self_mul_one_div_Gamma_add_one a
  have hS' := one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (a + 1)
  rw [show a + 1 + 1 = a + 2 by ring] at hS'
  have hz1 : z ^ (-c) = z * z ^ (-1 - c) := by
    rw [show -c = (-1 - c) + 1 by ring, cpow_add _ _ hz, cpow_one, mul_comm]
  have hz2 : z ^ (1 - c) = z * z * z ^ (-1 - c) := by
    rw [show 1 - c = (-1 - c) + 1 + 1 by ring, cpow_add _ _ hz, cpow_add _ _ hz, cpow_one]; ring
  rw [show 1 - (c + 2) = -1 - c by ring, show a + 2 - (c + 2) + 1 = a - c + 1 by ring,
    show c + 2 - 1 = c + 1 by ring, show 2 - (c + 2) = -c by ring,
    show 1 - (c + 1) = -c by ring, show a + 1 - (c + 1) + 1 = a - c + 1 by ring,
    show c + 1 - 1 = c by ring, show 2 - (c + 1) = 1 - c by ring]
  simp only [div_eq_mul_inv]
  rw [hG0, hGm, hGc, hG1, hS, hS', hz1, hz2]
  linear_combination Gamma (-1 - c) * (Gamma (a - c + 1))⁻¹ * E13 +
    Gamma (c - 1) * (Gamma (a + 2))⁻¹ * z ^ (-1 - c) * z * (a + 1) * E2

/-- Identity under the stated parameter and domain assumptions: `kummerU (a - 1) b z + (b - 2 * a
- z) * kummerU a b z + a * (a - b + 1) * kummerU (a + 1) b z = 0`. -/
@[dlmf 13.3.E7]
theorem kummerU_contiguous_a (a b z : ℂ) (hz : z ≠ 0) :
    kummerU (a - 1) b z + (b - 2 * a - z) * kummerU a b z +
      a * (a - b + 1) * kummerU (a + 1) b z = 0 := by
  refine eq_zero_of_tendsto_integerComplement (b := b) (f := fun c => kummerU (a - 1) c z +
    (c - 2 * a - z) * kummerU a c z + a * (a - c + 1) * kummerU (a + 1) c z) ?_
    fun c hc => kummerU_contiguous_a_of_mem hc
  have hc := tendsto_id_integerComplement b
  exact ((tendsto_kummerU (a - 1) b hz).add (((hc.sub_const _).sub_const _).mul
    (tendsto_kummerU a b hz))).add ((tendsto_const_nhds.mul ((hc.const_sub _).add_const _)).mul
      (tendsto_kummerU (a + 1) b hz))

/-- Identity under the stated parameter and domain assumptions: `(b - a - 1) * kummerU a (b - 1) z
+ (1 - b - z) * kummerU a b z + z * kummerU a (b + 1) z = 0`. -/
@[dlmf 13.3.E8]
theorem kummerU_contiguous_b (a b z : ℂ) (hz : z ≠ 0) :
    (b - a - 1) * kummerU a (b - 1) z + (1 - b - z) * kummerU a b z +
      z * kummerU a (b + 1) z = 0 := by
  refine eq_zero_of_tendsto_integerComplement (b := b)
      (f := fun c => (c - a - 1) * kummerU a (c - 1) z +
    (1 - c - z) * kummerU a c z + z * kummerU a (c + 1) z) ?_
    fun c hc => kummerU_contiguous_b_of_mem hc hz
  have hc := tendsto_id_integerComplement b
  exact ((((hc.sub_const _).sub_const _).mul (tendsto_kummerU_sub_one a b hz)).add
    (((hc.const_sub _).sub_const _).mul (tendsto_kummerU a b hz))).add
      (tendsto_const_nhds.mul (tendsto_kummerU_add_one a b hz))

/-- Identity under the stated parameter and domain assumptions: `kummerU a b z - a * kummerU (a +
1) b z - kummerU a (b - 1) z = 0`. -/
@[dlmf 13.3.E9]
theorem kummerU_contiguous_a_b (a b z : ℂ) (hz : z ≠ 0) :
    kummerU a b z - a * kummerU (a + 1) b z - kummerU a (b - 1) z = 0 := by
  refine eq_zero_of_tendsto_integerComplement (b := b) (f := fun c => kummerU a c z -
    a * kummerU (a + 1) c z - kummerU a (c - 1) z) ?_
    fun c hc => kummerU_contiguous_a_b_of_mem hc hz
  exact ((tendsto_kummerU a b hz).sub (tendsto_const_nhds.mul
    (tendsto_kummerU (a + 1) b hz))).sub (tendsto_kummerU_sub_one a b hz)

/-- Identity under the stated parameter and domain assumptions: `(b - a) * kummerU a b z + kummerU
(a - 1) b z - z * kummerU a (b + 1) z = 0`. -/
@[dlmf 13.3.E10]
theorem kummerU_contiguous_shift_a (a b z : ℂ) (hz : z ≠ 0) :
    (b - a) * kummerU a b z + kummerU (a - 1) b z - z * kummerU a (b + 1) z = 0 := by
  refine eq_zero_of_tendsto_integerComplement (b := b) (f := fun c => (c - a) * kummerU a c z +
    kummerU (a - 1) c z - z * kummerU a (c + 1) z) ?_
    fun c hc => kummerU_contiguous_shift_a_of_mem hc hz
  have hc := tendsto_id_integerComplement b
  exact (((hc.sub_const _).mul (tendsto_kummerU a b hz)).add
    (tendsto_kummerU (a - 1) b hz)).sub (tendsto_const_nhds.mul
      (tendsto_kummerU_add_one a b hz))

/-- Identity under the stated parameter and domain assumptions: `(a + z) * kummerU a b z - z *
kummerU a (b + 1) z + a * (b - a - 1) * kummerU (a + 1) b z = 0`. -/
@[dlmf 13.3.E11]
theorem kummerU_contiguous_mixed (a b z : ℂ) (hz : z ≠ 0) :
    (a + z) * kummerU a b z - z * kummerU a (b + 1) z +
      a * (b - a - 1) * kummerU (a + 1) b z = 0 := by
  refine eq_zero_of_tendsto_integerComplement (b := b) (f := fun c => (a + z) * kummerU a c z -
    z * kummerU a (c + 1) z + a * (c - a - 1) * kummerU (a + 1) c z) ?_
    fun c hc => kummerU_contiguous_mixed_of_mem hc hz
  have hc := tendsto_id_integerComplement b
  exact ((tendsto_const_nhds.mul (tendsto_kummerU a b hz)).sub (tendsto_const_nhds.mul
    (tendsto_kummerU_add_one a b hz))).add ((tendsto_const_nhds.mul
      ((hc.sub_const _).sub_const _)).mul (tendsto_kummerU (a + 1) b hz))

/-- Identity under the stated parameter and domain assumptions: `(a - 1 + z) * kummerU a b z -
kummerU (a - 1) b z + (a - b + 1) * kummerU a (b - 1) z = 0`. -/
@[dlmf 13.3.E12]
theorem kummerU_contiguous_down (a b z : ℂ) (hz : z ≠ 0) :
    (a - 1 + z) * kummerU a b z - kummerU (a - 1) b z +
      (a - b + 1) * kummerU a (b - 1) z = 0 := by
  refine eq_zero_of_tendsto_integerComplement (b := b) (f := fun c => (a - 1 + z) * kummerU a c z -
    kummerU (a - 1) c z + (a - c + 1) * kummerU a (c - 1) z) ?_
    fun c hc => kummerU_contiguous_down_of_mem hc hz
  have hc := tendsto_id_integerComplement b
  exact ((tendsto_const_nhds.mul (tendsto_kummerU a b hz)).sub
    (tendsto_kummerU (a - 1) b hz)).add (((hc.const_sub _).add_const _).mul
      (tendsto_kummerU_sub_one a b hz))

/-- Identity under the stated parameter and domain assumptions: `(a + 1) * z * kummerU (a + 2) (b
+ 2) z + (z - b) * kummerU (a + 1) (b + 1) z - kummerU a b z = 0`. -/
@[dlmf 13.3.E14]
theorem kummerU_ode_contiguous (a b z : ℂ) (hz : z ≠ 0) :
    (a + 1) * z * kummerU (a + 2) (b + 2) z + (z - b) * kummerU (a + 1) (b + 1) z -
      kummerU a b z = 0 := by
  refine eq_zero_of_tendsto_integerComplement (b := b) (f := fun c =>
    (a + 1) * z * kummerU (a + 2) (c + 2) z + (z - c) * kummerU (a + 1) (c + 1) z -
      kummerU a c z) ?_ fun c hc => kummerU_ode_contiguous_of_mem hc hz
  have hc := tendsto_id_integerComplement b
  exact ((tendsto_const_nhds.mul (tendsto_kummerU_add_two (a + 2) b hz)).add
    ((hc.const_sub _).mul (tendsto_kummerU_add_one (a + 1) b hz))).sub
      (tendsto_kummerU a b hz)

/-- Identity under the stated parameter and domain assumptions: `iteratedDeriv n (kummerM a b) =
fun z => poch a n / poch b n * kummerM (a + n) (b + n) z`. -/
@[dlmf 13.3.E16]
theorem iteratedDeriv_kummerM {a b : ℂ} (n : ℕ) (hb : ∀ k : ℕ, b ≠ -k) :
    iteratedDeriv n (kummerM a b) =
      fun z => poch a n / poch b n * kummerM (a + n) (b + n) z := by
  induction n with
  | zero => simp [iteratedDeriv_zero, poch_zero]
  | succ n ih =>
    have hb' : ∀ k : ℕ, b + n ≠ -k := not_neg_nat_add_nat hb n
    have hb0 : b + n ≠ 0 := by
      intro h
      exact hb n ((eq_neg_iff_add_eq_zero).2 h)
    funext z
    rw [iteratedDeriv_succ, ih, deriv_const_mul_field, deriv_kummerM hb' hb0]
    simp only [poch_succ, Nat.cast_add, Nat.cast_one, div_eq_mul_inv, mul_inv_rev]
    ring

/-- `z z^{s-1} = z^s` for `z ≠ 0`. -/
lemma mul_cpow_pred' {z : ℂ} (hz : z ≠ 0) (s : ℂ) : z * z ^ (s - 1) = z ^ s := by
  calc
    z * z ^ (s - 1) = z ^ (1 : ℂ) * z ^ (s - 1) := by rw [cpow_one]
    _ = z ^ ((1 : ℂ) + (s - 1)) := (cpow_add _ _ hz).symm
    _ = z ^ s := by congr 1; ring

/-- Kummer's function is differentiable everywhere. -/
private lemma hasDerivAt_kummerM {a b : ℂ} (hb : ∀ k : ℕ, b ≠ -k) (z : ℂ) :
    HasDerivAt (kummerM a b) (deriv (kummerM a b) z) z := by
  have h := (hasFPowerSeriesOnBall_kummerM (a := a) hb).analyticAt_of_mem (y := z) (by simp)
  exact h.differentiableAt.hasDerivAt

/-- Product rule for `w^s M(a,b,w)` on the slit plane. -/
private lemma deriv_cpow_mul_kummerM {a b : ℂ} (s : ℂ) (hb : ∀ k : ℕ, b ≠ -k) {z : ℂ}
    (hz : z ∈ slitPlane) :
    deriv (fun w => w ^ s * kummerM a b w) z =
      s * z ^ (s - 1) * kummerM a b z + z ^ s * deriv (kummerM a b) z := by
  have hM := hasDerivAt_kummerM (a := a) hb z
  have hp := (hasDerivAt_id z).cpow_const (c := s) hz
  have h := (hp.mul hM).deriv
  simp only [id_eq, Pi.mul_def, mul_one] at h
  rw [h]

/-- Product rule for `e^{-w} M(a,b,w)`. -/
private lemma deriv_exp_neg_mul_kummerM {a b : ℂ} (hb : ∀ k : ℕ, b ≠ -k) (z : ℂ) :
    deriv (fun w => exp (-w) * kummerM a b w) z =
      -(exp (-z) * kummerM a b z) + exp (-z) * deriv (kummerM a b) z := by
  have hM := hasDerivAt_kummerM (a := a) hb z
  have he : HasDerivAt (fun w : ℂ => exp (-w)) (exp (-z) * -1) z := (hasDerivAt_id z).neg.cexp
  have h := (he.mul hM).deriv
  simp only [Pi.mul_def] at h
  rw [h]
  ring

/-- Product rule for `w^s e^{-w} M(a,b,w)` on the slit plane. -/
private lemma deriv_cpow_mul_exp_neg_mul_kummerM {a b : ℂ} (s : ℂ) (hb : ∀ k : ℕ, b ≠ -k)
    {z : ℂ} (hz : z ∈ slitPlane) :
    deriv (fun w => w ^ s * exp (-w) * kummerM a b w) z =
      s * z ^ (s - 1) * exp (-z) * kummerM a b z - z ^ s * exp (-z) * kummerM a b z +
        z ^ s * exp (-z) * deriv (kummerM a b) z := by
  have hM := hasDerivAt_kummerM (a := a) hb z
  have hp := (hasDerivAt_id z).cpow_const (c := s) hz
  have he : HasDerivAt (fun w : ℂ => exp (-w)) (exp (-z) * -1) z := (hasDerivAt_id z).neg.cexp
  have h := ((hp.mul he).mul hM).deriv
  simp only [id_eq, Pi.mul_def, mul_one] at h
  rw [h]
  ring

/-- Identity under the stated parameter and domain assumptions: `mulDerivMul^[n] (fun w => w ^ (a
- 1) * kummerM a b w) z = poch a n * z ^ (a + n - 1) * kummerM (a + n) b z`. -/
@[dlmf 13.3.E17]
theorem iterate_mulDerivMul_kummerM {a b : ℂ} (n : ℕ) {z : ℂ}
    (hb : ∀ k : ℕ, b ≠ -k) (hz : z ∈ slitPlane) :
    mulDerivMul^[n] (fun w => w ^ (a - 1) * kummerM a b w) z =
      poch a n * z ^ (a + n - 1) * kummerM (a + n) b z := by
  induction n generalizing z with
  | zero => simp [poch_zero]
  | succ n ih =>
    have heq : (fun w => w * mulDerivMul^[n] (fun t => t ^ (a - 1) * kummerM a b t) w)
        =ᶠ[𝓝 z] (fun w => poch a n * (w ^ (a + n) * kummerM (a + n) b w)) := by
      filter_upwards [isOpen_slitPlane.mem_nhds hz] with w hw
      rw [ih hw, ← mul_cpow_pred' (slitPlane_ne_zero hw) (a + n)]
      ring
    rw [Function.iterate_succ_apply', mulDerivMul_eq_mul, heq.deriv_eq, deriv_const_mul_field,
      deriv_cpow_mul_kummerM (a + n) hb hz]
    have hA := z_mul_deriv_kummerM_eq_shift_a (a := a + n) hb z
    have hz0 : z ≠ 0 := slitPlane_ne_zero hz
    have e1 : z ^ (a + ((n + 1 : ℕ) : ℂ) - 1) = z ^ (a + n) := by congr 1; push_cast; ring
    have e2 : a + ((n + 1 : ℕ) : ℂ) = a + n + 1 := by push_cast; ring
    have e4 : z ^ (a + n) = z * z ^ (a + n - 1) := (mul_cpow_pred' hz0 _).symm
    rw [e1, e2, poch_succ, e4]
    linear_combination (poch a n * z * z ^ (a + n - 1)) * hA

/-- Identity under the stated parameter and domain assumptions: `iteratedDeriv n (fun w => w ^ (b
- 1) * kummerM a b w) z = poch (b - n) n * z ^ (b - n - 1) * kummerM a (b - n) z`. -/
@[dlmf 13.3.E18]
theorem iteratedDeriv_mul_cpow_kummerM {a b : ℂ} (n : ℕ) {z : ℂ}
    (hb : ∀ k : ℕ, b - n ≠ -k) (hz : z ∈ slitPlane) :
    iteratedDeriv n (fun w => w ^ (b - 1) * kummerM a b w) z =
      poch (b - n) n * z ^ (b - n - 1) * kummerM a (b - n) z := by
  induction n generalizing b with
  | zero => simp [iteratedDeriv_zero, poch_zero]
  | succ n ih =>
    have hb0 : ∀ k : ℕ, b ≠ -k := by
      intro k hk
      apply hb (k + (n + 1))
      push_cast
      linear_combination hk
    have hbm : ∀ k : ℕ, b - 1 ≠ -k := by
      intro k hk
      apply hb (k + n)
      push_cast
      linear_combination hk
    have hbn' : ∀ k : ℕ, b - 1 - n ≠ -k := by
      intro k hk
      apply hb k
      push_cast
      linear_combination hk
    have heq : deriv (fun w => w ^ (b - 1) * kummerM a b w) =ᶠ[𝓝 z]
        (fun w => (b - 1) * (w ^ (b - 1 - 1) * kummerM a (b - 1) w)) := by
      filter_upwards [isOpen_slitPlane.mem_nhds hz] with w hw
      rw [deriv_cpow_mul_kummerM (b - 1) hb0 hw]
      have hB := z_mul_deriv_kummerM_eq_shift_b_pred (a := a) hbm w
      have hw0 : w ≠ 0 := slitPlane_ne_zero hw
      have e : w ^ (b - 1) = w * w ^ (b - 1 - 1) := (mul_cpow_pred' hw0 _).symm
      rw [e]
      linear_combination (w ^ (b - 1 - 1)) * hB
    rw [iteratedDeriv_succ', heq.iteratedDeriv_eq n, iteratedDeriv_const_mul_field, ih hbn']
    rw [show b - 1 - (n : ℂ) = b - ((n + 1 : ℕ) : ℂ) by push_cast; ring, poch_succ,
      show b - ((n + 1 : ℕ) : ℂ) + (n : ℂ) = b - 1 by push_cast; ring]
    ring

/-- Identity under the stated parameter and domain assumptions: `mulDerivMul^[n] (fun w => w ^ (b
- a - 1) * exp (-w) * kummerM a b w) z = poch (b - a) n * z ^ (b - a + n - 1) * exp (-z) *
kummerM (a - n) b z`. -/
@[dlmf 13.3.E19]
theorem iterate_mulDerivMul_exp_neg_kummerM {a b : ℂ} (n : ℕ) {z : ℂ}
    (hb : ∀ k : ℕ, b ≠ -k) (hz : z ∈ slitPlane) :
    mulDerivMul^[n] (fun w => w ^ (b - a - 1) * exp (-w) * kummerM a b w) z =
      poch (b - a) n * z ^ (b - a + n - 1) * exp (-z) * kummerM (a - n) b z := by
  induction n generalizing z with
  | zero => simp [poch_zero]
  | succ n ih =>
    have heq : (fun w => w * mulDerivMul^[n]
          (fun t => t ^ (b - a - 1) * exp (-t) * kummerM a b t) w) =ᶠ[𝓝 z]
        (fun w => poch (b - a) n * (w ^ (b - a + n) * exp (-w) * kummerM (a - n) b w)) := by
      filter_upwards [isOpen_slitPlane.mem_nhds hz] with w hw
      rw [ih hw, ← mul_cpow_pred' (slitPlane_ne_zero hw) (b - a + n)]
      ring
    rw [Function.iterate_succ_apply', mulDerivMul_eq_mul, heq.deriv_eq, deriv_const_mul_field,
      deriv_cpow_mul_exp_neg_mul_kummerM (b - a + n) hb hz]
    have hC := z_mul_deriv_kummerM_eq_shift_a_pred (a := a - n) hb z
    have hz0 : z ≠ 0 := slitPlane_ne_zero hz
    have e1 : z ^ (b - a + ((n + 1 : ℕ) : ℂ) - 1) = z ^ (b - a + n) := by
      congr 1; push_cast; ring
    have e2 : a - ((n + 1 : ℕ) : ℂ) = a - n - 1 := by push_cast; ring
    have e4 : z ^ (b - a + n) = z * z ^ (b - a + n - 1) := (mul_cpow_pred' hz0 _).symm
    rw [e1, e2, poch_succ, e4]
    linear_combination (poch (b - a) n * z * z ^ (b - a + n - 1) * exp (-z)) * hC

/-- Identity under the stated parameter and domain assumptions: `iteratedDeriv n (fun w => exp
(-w) * kummerM a b w) = fun z => (-1 : ℂ) ^ n * poch (b - a) n / poch b n * exp (-z) * kummerM
a (b + n) z`. -/
@[dlmf 13.3.E20]
theorem iteratedDeriv_exp_neg_kummerM {a b : ℂ} (n : ℕ) (hb : ∀ k : ℕ, b ≠ -k) :
    iteratedDeriv n (fun w => exp (-w) * kummerM a b w) =
      fun z => (-1 : ℂ) ^ n * poch (b - a) n / poch b n * exp (-z) *
        kummerM a (b + n) z := by
  induction n generalizing b with
  | zero =>
    funext z
    simp [iteratedDeriv_zero, poch_zero]
  | succ n ih =>
    have hb1 : ∀ k : ℕ, b + 1 ≠ -k := by simpa using not_neg_nat_add_nat hb 1
    have hb0 : b ≠ 0 := by simpa using hb 0
    have hd : deriv (fun w => exp (-w) * kummerM a b w) =
        fun w => -(b - a) / b * (exp (-w) * kummerM a (b + 1) w) := by
      funext w
      rw [deriv_exp_neg_mul_kummerM hb w]
      have hD := deriv_kummerM_eq_shift_b_succ (a := a) hb w
      field_simp
      linear_combination hD
    funext z
    rw [iteratedDeriv_succ', hd, iteratedDeriv_const_mul_field, ih hb1]
    beta_reduce
    have hp : poch (b + 1) n ≠ 0 := poch_ne_zero_of_not_neg_nat hb1 n
    rw [show b + 1 + (n : ℂ) = b + ((n + 1 : ℕ) : ℂ) by push_cast; ring,
      show b + 1 - a = b - a + 1 by ring, poch_succ_left (b - a), poch_succ_left b, pow_succ]
    field_simp

/-- Identity under the stated parameter and domain assumptions: `iteratedDeriv n (fun w => w ^ (b
- 1) * exp (-w) * kummerM a b w) z = poch (b - n) n * z ^ (b - n - 1) * exp (-z) * kummerM (a
- n) (b - n) z`. -/
@[dlmf 13.3.E21]
theorem iteratedDeriv_mul_cpow_exp_neg_kummerM {a b : ℂ} (n : ℕ) {z : ℂ}
    (hb : ∀ k : ℕ, b - n ≠ -k) (hz : z ∈ slitPlane) :
    iteratedDeriv n (fun w => w ^ (b - 1) * exp (-w) * kummerM a b w) z =
      poch (b - n) n * z ^ (b - n - 1) * exp (-z) * kummerM (a - n) (b - n) z := by
  induction n generalizing a b with
  | zero => simp [iteratedDeriv_zero, poch_zero]
  | succ n ih =>
    have hb0 : ∀ k : ℕ, b ≠ -k := by
      intro k hk
      apply hb (k + (n + 1))
      push_cast
      linear_combination hk
    have hbm : ∀ k : ℕ, b - 1 ≠ -k := by
      intro k hk
      apply hb (k + n)
      push_cast
      linear_combination hk
    have hbn' : ∀ k : ℕ, b - 1 - n ≠ -k := by
      intro k hk
      apply hb k
      push_cast
      linear_combination hk
    have heq : deriv (fun w => w ^ (b - 1) * exp (-w) * kummerM a b w) =ᶠ[𝓝 z]
        (fun w => (b - 1) * (w ^ (b - 1 - 1) * exp (-w) * kummerM (a - 1) (b - 1) w)) := by
      filter_upwards [isOpen_slitPlane.mem_nhds hz] with w hw
      rw [deriv_cpow_mul_exp_neg_mul_kummerM (b - 1) hb0 hw]
      have hB := z_mul_deriv_kummerM_eq_shift_b_pred (a := a) hbm w
      have h4 := kummerM_contiguous_shift_a (a := a) hbm (z := w)
      rw [sub_add_cancel] at h4
      have hw0 : w ≠ 0 := slitPlane_ne_zero hw
      have e : w ^ (b - 1) = w * w ^ (b - 1 - 1) := (mul_cpow_pred' hw0 _).symm
      rw [e]
      linear_combination (w ^ (b - 1 - 1) * exp (-w)) * hB + (w ^ (b - 1 - 1) * exp (-w)) * h4
    rw [iteratedDeriv_succ', heq.iteratedDeriv_eq n, iteratedDeriv_const_mul_field, ih hbn']
    rw [show b - 1 - (n : ℂ) = b - ((n + 1 : ℕ) : ℂ) by push_cast; ring,
      show a - 1 - (n : ℂ) = a - ((n + 1 : ℕ) : ℂ) by push_cast; ring, poch_succ,
      show b - ((n + 1 : ℕ) : ℂ) + (n : ℂ) = b - 1 by push_cast; ring]
    ring

end DLMF.Confluent
end
end
