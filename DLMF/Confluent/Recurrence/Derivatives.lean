/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Confluent.Recurrence.Contiguous

/-!
# Derivative identities for Tricomi functions

Derivative formulas for Tricomi functions on the principal sheet and the logarithmic argument
plane, with parameter shifts and branch conditions explicit.

Source references and common attribution are retained in
`DLMF.Confluent.Recurrence`.
-/

@[expose] public section

open Complex Filter FormalMultilinearSeries

open scoped Real Topology

open DLMF.Hypergeometric

noncomputable section

namespace DLMF.Confluent

/-! ### Derivatives of Tricomi's function -/

/-- Kummer's function has derivative `(a/b) M(a+1,b+1,z)`. -/
theorem hasDerivAt_kummerM_shift {a b : ℂ} (hb : ∀ k : ℕ, b ≠ -k) (z : ℂ) :
    HasDerivAt (kummerM a b) (a / b * kummerM (a + 1) (b + 1) z) z := by
  have h := (hasFPowerSeriesOnBall_kummerM (a := a) hb).analyticAt_of_mem (y := z) (by simp)
  have hb0 : b ≠ 0 := by simpa using hb 0
  rw [← deriv_kummerM hb hb0]
  exact h.differentiableAt.hasDerivAt

/-- Derivative of Tricomi's function at noninteger second parameter. -/
theorem hasDerivAt_kummerU_of_mem (a : ℂ) {c w : ℂ} (hc : c ∈ integerComplement)
    (hw : w ∈ slitPlane) :
    HasDerivAt (kummerU a c) (-a * kummerU (a + 1) (c + 1) w) w := by
  by_cases ha : a = 0
  · subst ha
    have : kummerU 0 c = fun _ => 1 := funext fun w => kummerU_zero c w
    rw [this, neg_zero, zero_mul]
    exact hasDerivAt_const _ _
  have hw0 := slitPlane_ne_zero hw
  have hcz := forall_of_mem_integerComplement hc
  have hc1 : c + 1 ∈ integerComplement := by
    simpa using (add_intCast_mem_integerComplement (x := c) 1).mpr hc
  have h2c : 2 - c ∈ integerComplement := by
    have := (add_intCast_mem_integerComplement (x := -c) 2).mpr (by
      intro ⟨k, hk⟩; exact hc ⟨-k, by push_cast; linear_combination -hk⟩)
    simpa [sub_eq_neg_add, add_comm] using this
  have hcnp := not_neg_nat_of_mem_integerComplement hc
  have h2cnp := not_neg_nat_of_mem_integerComplement h2c
  have h1cnp : ∀ k : ℕ, (2 - c) - 1 ≠ -k := by
    have h1c : 1 - c ∈ integerComplement := by
      have := (add_intCast_mem_integerComplement (x := -c) 1).mpr (by
        intro ⟨k, hk⟩; exact hc ⟨-k, by push_cast; linear_combination -hk⟩)
      simpa [sub_eq_neg_add, add_comm] using this
    simpa [show (2 : ℂ) - c - 1 = 1 - c by ring] using not_neg_nat_of_mem_integerComplement h1c
  have hfun : kummerU a c = fun w => kummerUConnection a c w :=
    funext fun w => kummerU_eq_connection a c w hcz
  rw [hfun, kummerU_eq_connection (a + 1) (c + 1) w (forall_of_mem_integerComplement hc1)]
  unfold kummerUConnection
  have hM1 := hasDerivAt_kummerM_shift (a := a) hcnp w
  have hM2 := hasDerivAt_kummerM_shift (a := a - c + 1) h2cnp w
  have hp : HasDerivAt (fun w : ℂ => w ^ (1 - c)) ((1 - c) * w ^ (1 - c - 1)) w := by
    simpa using (hasDerivAt_id w).cpow_const (c := 1 - c) hw
  have hD := ((hM1.const_mul (Gamma (1 - c) / Gamma (a - c + 1))).add
    ((hp.const_mul (Gamma (c - 1) / Gamma a)).mul hM2))
  refine hD.congr_deriv ?_
  -- Gamma recurrences
  have hc0 : c ≠ 0 := by simpa using hcz 0
  have hc10 : c - 1 ≠ 0 := fun h => hcz 1 (by push_cast; linear_combination h)
  have hG1 : Gamma (1 - c) = -c * Gamma (-c) := by
    rw [show (1 : ℂ) - c = -c + 1 by ring, Gamma_add_one _ (neg_ne_zero.mpr hc0)]
  have hG2 : Gamma c = (c - 1) * Gamma (c - 1) := by
    rw [← Gamma_add_one _ hc10]; ring_nf
  have hG3 : Gamma (a + 1) = a * Gamma a := Gamma_add_one _ ha
  have hmix := kummerM_contiguous_mixed_b_pred (a := a - c + 1) (b := 2 - c) h1cnp (z := w)
  have hpow1 : w ^ (1 - c - 1) = w ^ (-c) := by ring_nf
  have hpow2 : w ^ (1 - c) = w * w ^ (-c) := by
    rw [show (1 : ℂ) - c = 1 + -c by ring, cpow_add _ _ hw0, cpow_one]
  rw [show (c + 1 : ℂ) - 1 = c by ring, show (a + 1 : ℂ) - (c + 1) + 1 = a - c + 1 by ring,
    show (1 : ℂ) - (c + 1) = -c by ring, show (2 : ℂ) - (c + 1) = 2 - c - 1 by ring, hpow1]
  have hY : Gamma (1 - c) / Gamma (a - c + 1) = -c * (Gamma (-c) / Gamma (a - c + 1)) := by
    rw [hG1, mul_div_assoc]
  have hX : Gamma c / Gamma (a + 1) = (c - 1) / a * (Gamma (c - 1) / Gamma a) := by
    rw [hG2, hG3, mul_div_mul_comm]
  have h2c0 : (2 : ℂ) - c ≠ 0 := fun h => hcz 2 (by push_cast; linear_combination -h)
  rw [hY, hX, hpow2]
  generalize Gamma (-c) / Gamma (a - c + 1) = Y
  generalize Gamma (c - 1) / Gamma a = X
  field_simp
  linear_combination (X * w ^ (-c)) * hmix

/-- **Derivative of Tricomi's function** for every second parameter, on the slit plane. -/
theorem hasDerivAt_kummerU (a b : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    HasDerivAt (kummerU a b) (-a * kummerU (a + 1) (b + 1) z) z := by
  have := integerComplement_nhdsWithin_neBot b
  refine hasDerivAt_of_tendstoUniformlyOnFilter (l := 𝓝[integerComplement] b)
    (f := fun c => kummerU a c) (f' := fun c w => -a * kummerU (a + 1) (c + 1) w)
    (g' := fun w => -a * kummerU (a + 1) (b + 1) w) ?_ ?_ ?_
  · have hc : ContinuousAt (fun p : ℂ × ℂ => -a * kummerU (a + 1) (p.1 + 1) p.2) (b, z) := by
      have h := continuousAt_kummerU (a + 1) (b + 1) hz
      have hf : ContinuousAt (fun p : ℂ × ℂ => (a + 1, p.1 + 1, p.2)) (b, z) := by fun_prop
      exact continuousAt_const.mul
        (ContinuousAt.comp (g := fun q : ℂ × ℂ × ℂ => kummerU q.1 q.2.1 q.2.2)
          (f := fun p : ℂ × ℂ => (a + 1, p.1 + 1, p.2)) h hf)
    exact tendstoUniformlyOnFilter_of_continuousAt
      (F := fun c w => -a * kummerU (a + 1) (c + 1) w) hc nhdsWithin_le_nhds
  · have hm : integerComplement ×ˢ slitPlane ∈ 𝓝[integerComplement] b ×ˢ 𝓝 z :=
      prod_mem_prod self_mem_nhdsWithin (isOpen_slitPlane.mem_nhds hz)
    filter_upwards [hm] with p hp
    exact hasDerivAt_kummerU_of_mem a hp.1 hp.2
  · filter_upwards [isOpen_slitPlane.mem_nhds hz] with y hy
    exact tendsto_kummerU a b (slitPlane_ne_zero hy)

/-- Derivative of Tricomi U. `U` is not complex-differentiable on the cut, so `z` is restricted to
the slit plane. -/
@[dlmf 13.3.E22]
theorem deriv_kummerU (a b : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    deriv (kummerU a b) z = -a * kummerU (a + 1) (b + 1) z :=
  (hasDerivAt_kummerU a b hz).deriv

/-- Product rule for `w^s U(a,b,w)` on the slit plane, with `U' = -a U(a+1,b+1,·)`. -/
private lemma deriv_cpow_mul_kummerU (a b s : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    deriv (fun w => w ^ s * kummerU a b w) z =
      s * z ^ (s - 1) * kummerU a b z + z ^ s * (-a * kummerU (a + 1) (b + 1) z) := by
  have hU := hasDerivAt_kummerU a b hz
  have hp := (hasDerivAt_id z).cpow_const (c := s) hz
  have h := (hp.mul hU).deriv
  simp only [id_eq, Pi.mul_def, mul_one] at h
  rw [h]

/-- Product rule for `e^{-w} U(a,b,w)` on the slit plane. -/
private lemma deriv_exp_neg_mul_kummerU (a b : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    deriv (fun w => exp (-w) * kummerU a b w) z =
      -(exp (-z) * kummerU a b z) + exp (-z) * (-a * kummerU (a + 1) (b + 1) z) := by
  have hU := hasDerivAt_kummerU a b hz
  have he : HasDerivAt (fun w : ℂ => exp (-w)) (exp (-z) * -1) z := (hasDerivAt_id z).neg.cexp
  have h := (he.mul hU).deriv
  simp only [Pi.mul_def] at h
  rw [h]
  ring

/-- Product rule for `w^s e^{-w} U(a,b,w)` on the slit plane. -/
private lemma deriv_cpow_mul_exp_neg_mul_kummerU (a b s : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    deriv (fun w => w ^ s * exp (-w) * kummerU a b w) z =
      s * z ^ (s - 1) * exp (-z) * kummerU a b z - z ^ s * exp (-z) * kummerU a b z +
        z ^ s * exp (-z) * (-a * kummerU (a + 1) (b + 1) z) := by
  have hU := hasDerivAt_kummerU a b hz
  have hp := (hasDerivAt_id z).cpow_const (c := s) hz
  have he : HasDerivAt (fun w : ℂ => exp (-w)) (exp (-z) * -1) z := (hasDerivAt_id z).neg.cexp
  have h := ((hp.mul he).mul hU).deriv
  simp only [id_eq, Pi.mul_def, mul_one] at h
  rw [h]
  ring

/-- Iterated derivatives of Tricomi U. `U` is not complex-differentiable on the cut, so `z` is
restricted to the slit plane. -/
@[dlmf 13.3.E23]
theorem iteratedDeriv_kummerU (a b : ℂ) (n : ℕ) {z : ℂ} (hz : z ∈ slitPlane) :
    iteratedDeriv n (kummerU a b) z =
      (-1 : ℂ) ^ n * poch a n * kummerU (a + n) (b + n) z := by
  induction n generalizing a b with
  | zero => simp [poch_zero]
  | succ n ih =>
    have heq : deriv (kummerU a b) =ᶠ[𝓝 z] fun w => -a * kummerU (a + 1) (b + 1) w := by
      filter_upwards [isOpen_slitPlane.mem_nhds hz] with w hw
      exact deriv_kummerU a b hw
    rw [iteratedDeriv_succ', heq.iteratedDeriv_eq n, iteratedDeriv_const_mul_field, ih,
      poch_succ_left]
    rw [show a + 1 + (n : ℂ) = a + ((n + 1 : ℕ) : ℂ) by push_cast; ring,
      show b + 1 + (n : ℂ) = b + ((n + 1 : ℕ) : ℂ) by push_cast; ring, pow_succ]
    ring

/-- Identity under the stated parameter and domain assumptions: `mulDerivMul^[n] (fun w => w ^ (a
- 1) * kummerU a b w) z = poch a n * poch (a - b + 1) n * z ^ (a + n - 1) * kummerU (a + n) b
z`. -/
@[dlmf 13.3.E24]
theorem iterate_mulDerivMul_kummerU (a b : ℂ) (n : ℕ) {z : ℂ} (hz : z ∈ slitPlane) :
    mulDerivMul^[n] (fun w => w ^ (a - 1) * kummerU a b w) z =
      poch a n * poch (a - b + 1) n * z ^ (a + n - 1) * kummerU (a + n) b z := by
  induction n generalizing z with
  | zero => simp [poch_zero]
  | succ n ih =>
    have heq : (fun w => w * mulDerivMul^[n] (fun t => t ^ (a - 1) * kummerU a b t) w)
        =ᶠ[𝓝 z] (fun w => poch a n * poch (a - b + 1) n *
          (w ^ (a + n) * kummerU (a + n) b w)) := by
      filter_upwards [isOpen_slitPlane.mem_nhds hz] with w hw
      rw [ih hw, ← mul_cpow_pred' (slitPlane_ne_zero hw) (a + n)]
      ring
    rw [Function.iterate_succ_apply', mulDerivMul, heq.deriv_eq, deriv_const_mul_field,
      deriv_cpow_mul_kummerU _ _ (a + n) hz]
    have hz0 : z ≠ 0 := slitPlane_ne_zero hz
    have hA := kummerU_contiguous_shift_a (a + n + 1) b z hz0
    rw [add_sub_cancel_right] at hA
    have e1 : z ^ (a + ((n + 1 : ℕ) : ℂ) - 1) = z ^ (a + n) := by congr 1; push_cast; ring
    have e2 : a + ((n + 1 : ℕ) : ℂ) = a + n + 1 := by push_cast; ring
    have e4 : z ^ (a + n) = z * z ^ (a + n - 1) := (mul_cpow_pred' hz0 _).symm
    rw [e1, e2, poch_succ, poch_succ, e4]
    linear_combination (poch a n * poch (a - b + 1) n * z * z ^ (a + n - 1) * (a + n)) * hA

/-- Identity under the stated parameter and domain assumptions: `iteratedDeriv n (fun w => w ^ (b
- 1) * kummerU a b w) z = (-1 : ℂ) ^ n * poch (a - b + 1) n * z ^ (b - n - 1) * kummerU a (b -
n) z`. -/
@[dlmf 13.3.E25]
theorem iteratedDeriv_mul_cpow_kummerU (a b : ℂ) (n : ℕ) {z : ℂ} (hz : z ∈ slitPlane) :
    iteratedDeriv n (fun w => w ^ (b - 1) * kummerU a b w) z =
      (-1 : ℂ) ^ n * poch (a - b + 1) n * z ^ (b - n - 1) * kummerU a (b - n) z := by
  induction n generalizing b with
  | zero => simp [poch_zero]
  | succ n ih =>
    have heq : deriv (fun w => w ^ (b - 1) * kummerU a b w) =ᶠ[𝓝 z]
        (fun w => -(a - b + 1) * (w ^ (b - 1 - 1) * kummerU a (b - 1) w)) := by
      filter_upwards [isOpen_slitPlane.mem_nhds hz] with w hw
      rw [deriv_cpow_mul_kummerU _ _ (b - 1) hw]
      have hw0 : w ≠ 0 := slitPlane_ne_zero hw
      have h1 := kummerU_contiguous_shift_a (a + 1) b w hw0
      rw [add_sub_cancel_right] at h1
      have h2 := kummerU_contiguous_a_b a b w hw0
      have e : w ^ (b - 1) = w * w ^ (b - 1 - 1) := (mul_cpow_pred' hw0 _).symm
      rw [e]
      linear_combination (w ^ (b - 1 - 1) * a) * h1 + (w ^ (b - 1 - 1) * (b - a - 1)) * h2
    rw [iteratedDeriv_succ', heq.iteratedDeriv_eq n, iteratedDeriv_const_mul_field, ih]
    rw [show b - 1 - (n : ℂ) = b - ((n + 1 : ℕ) : ℂ) by push_cast; ring, poch_succ_left,
      show a - (b - 1) + 1 = a - b + 1 + 1 by ring, pow_succ]
    ring

/-- Identity under the stated parameter and domain assumptions: `mulDerivMul^[n] (fun w => w ^ (b
- a - 1) * exp (-w) * kummerU a b w) z = (-1 : ℂ) ^ n * z ^ (b - a + n - 1) * exp (-z) *
kummerU (a - n) b z`. -/
@[dlmf 13.3.E26]
theorem iterate_mulDerivMul_exp_neg_kummerU (a b : ℂ) (n : ℕ) {z : ℂ}
    (hz : z ∈ slitPlane) :
    mulDerivMul^[n] (fun w => w ^ (b - a - 1) * exp (-w) * kummerU a b w) z =
      (-1 : ℂ) ^ n * z ^ (b - a + n - 1) * exp (-z) * kummerU (a - n) b z := by
  induction n generalizing z with
  | zero => simp
  | succ n ih =>
    have heq : (fun w => w * mulDerivMul^[n]
          (fun t => t ^ (b - a - 1) * exp (-t) * kummerU a b t) w) =ᶠ[𝓝 z]
        (fun w => (-1 : ℂ) ^ n * (w ^ (b - a + n) * exp (-w) * kummerU (a - n) b w)) := by
      filter_upwards [isOpen_slitPlane.mem_nhds hz] with w hw
      rw [ih hw, ← mul_cpow_pred' (slitPlane_ne_zero hw) (b - a + n)]
      ring
    rw [Function.iterate_succ_apply', mulDerivMul, heq.deriv_eq, deriv_const_mul_field,
      deriv_cpow_mul_exp_neg_mul_kummerU _ _ (b - a + n) hz]
    have hz0 : z ≠ 0 := slitPlane_ne_zero hz
    have h1 := kummerU_contiguous_shift_a (a - n) b z hz0
    have h2 := kummerU_contiguous_a_b (a - n) (b + 1) z hz0
    rw [add_sub_cancel_right] at h2
    have e1 : z ^ (b - a + ((n + 1 : ℕ) : ℂ) - 1) = z ^ (b - a + n) := by
      congr 1; push_cast; ring
    have e2 : a - ((n + 1 : ℕ) : ℂ) = a - n - 1 := by push_cast; ring
    have e4 : z ^ (b - a + n) = z * z ^ (b - a + n - 1) := (mul_cpow_pred' hz0 _).symm
    rw [e1, e2, show a - (n : ℂ) + 1 = a - n + 1 by ring, e4, pow_succ]
    linear_combination ((-1 : ℂ) ^ n * z * z ^ (b - a + n - 1) * exp (-z)) * h1 +
      ((-1 : ℂ) ^ n * z * z * z ^ (b - a + n - 1) * exp (-z)) * h2

/-- Iterated derivatives of `exp (-z) * U(a,b,z)`. `U` is not complex-differentiable on the cut, so
`z` is restricted to the slit plane. -/
@[dlmf 13.3.E27]
theorem iteratedDeriv_exp_neg_kummerU (a b : ℂ) (n : ℕ) {z : ℂ} (hz : z ∈ slitPlane) :
    iteratedDeriv n (fun w => exp (-w) * kummerU a b w) z =
      (-1 : ℂ) ^ n * exp (-z) * kummerU a (b + n) z := by
  induction n generalizing b with
  | zero => simp
  | succ n ih =>
    have heq : deriv (fun w => exp (-w) * kummerU a b w) =ᶠ[𝓝 z]
        (fun w => -1 * (exp (-w) * kummerU a (b + 1) w)) := by
      filter_upwards [isOpen_slitPlane.mem_nhds hz] with w hw
      rw [deriv_exp_neg_mul_kummerU _ _ hw]
      have h := kummerU_contiguous_a_b a (b + 1) w (slitPlane_ne_zero hw)
      rw [add_sub_cancel_right] at h
      linear_combination (exp (-w)) * h
    rw [iteratedDeriv_succ', heq.iteratedDeriv_eq n, iteratedDeriv_const_mul_field, ih,
      show b + 1 + (n : ℂ) = b + ((n + 1 : ℕ) : ℂ) by push_cast; ring, pow_succ]
    ring

/-- Identity under the stated parameter and domain assumptions: `iteratedDeriv n (fun w => w ^ (b
- 1) * exp (-w) * kummerU a b w) z = (-1 : ℂ) ^ n * z ^ (b - n - 1) * exp (-z) * kummerU (a -
n) (b - n) z`. -/
@[dlmf 13.3.E28]
theorem iteratedDeriv_mul_cpow_exp_neg_kummerU (a b : ℂ) (n : ℕ) {z : ℂ}
    (hz : z ∈ slitPlane) :
    iteratedDeriv n (fun w => w ^ (b - 1) * exp (-w) * kummerU a b w) z =
      (-1 : ℂ) ^ n * z ^ (b - n - 1) * exp (-z) * kummerU (a - n) (b - n) z := by
  induction n generalizing a b with
  | zero => simp
  | succ n ih =>
    have heq : deriv (fun w => w ^ (b - 1) * exp (-w) * kummerU a b w) =ᶠ[𝓝 z]
        (fun w => -1 * (w ^ (b - 1 - 1) * exp (-w) * kummerU (a - 1) (b - 1) w)) := by
      filter_upwards [isOpen_slitPlane.mem_nhds hz] with w hw
      rw [deriv_cpow_mul_exp_neg_mul_kummerU _ _ (b - 1) hw]
      have hw0 : w ≠ 0 := slitPlane_ne_zero hw
      have h1 := kummerU_contiguous_shift_a (a + 1) b w hw0
      rw [add_sub_cancel_right] at h1
      have h2 := kummerU_contiguous_a_b a b w hw0
      have h3 := kummerU_contiguous_shift_a a (b - 1) w hw0
      rw [sub_add_cancel] at h3
      have e : w ^ (b - 1) = w * w ^ (b - 1 - 1) := (mul_cpow_pred' hw0 _).symm
      rw [e]
      linear_combination (w ^ (b - 1 - 1) * exp (-w) * a) * h1 +
        (w ^ (b - 1 - 1) * exp (-w) * (b - a - 1)) * h2 + (w ^ (b - 1 - 1) * exp (-w)) * h3
    rw [iteratedDeriv_succ', heq.iteratedDeriv_eq n, iteratedDeriv_const_mul_field, ih]
    rw [show b - 1 - (n : ℂ) = b - ((n + 1 : ℕ) : ℂ) by push_cast; ring,
      show a - 1 - (n : ℂ) = a - ((n + 1 : ℕ) : ℂ) by push_cast; ring, pow_succ]
    ring

/-- Identity under the stated parameter and domain assumptions: `(κ - μ - 1 / 2) * whittakerM (κ -
1) μ z + (z - 2 * κ) * whittakerM κ μ z + (κ + μ + 1 / 2) * whittakerM (κ + 1) μ z = 0`. -/
@[dlmf 13.15.E1]
theorem whittakerM_contiguous_kappa {κ μ z : ℂ}
    (hμ : ∀ k : ℕ, 1 + 2 * μ ≠ -k) (hz : z ∈ slitPlane) :
    (κ - μ - 1 / 2) * whittakerM (κ - 1) μ z + (z - 2 * κ) * whittakerM κ μ z +
      (κ + μ + 1 / 2) * whittakerM (κ + 1) μ z = 0 := by
  have hM := kummerM_contiguous_a (a := μ - κ + 1 / 2) hμ (z := z)
  rw [show μ - κ + 1 / 2 - 1 = μ - (κ + 1) + 1 / 2 by ring,
    show μ - κ + 1 / 2 + 1 = μ - (κ - 1) + 1 / 2 by ring] at hM
  unfold whittakerM
  linear_combination (exp (-z / 2) * z ^ (μ + 1 / 2)) * hM

/-- Identity under the stated parameter and domain assumptions: `2 * μ * (1 + 2 * μ) * (z : ℂ) ^
(1 / 2 : ℂ) * whittakerM (κ - 1 / 2) (μ - 1 / 2) z - (z + 2 * μ) * (1 + 2 * μ) * whittakerM κ
μ z + (κ + μ + 1 / 2) * z ^ (1 / 2 : ℂ) * whittakerM (κ + 1 / 2) (μ + 1 / 2) z = 0`. -/
@[dlmf 13.15.E2]
theorem whittakerM_contiguous_mu {κ μ z : ℂ}
    (hμ : ∀ k : ℕ, 2 * μ ≠ -k) (hz : z ∈ slitPlane) :
    2 * μ * (1 + 2 * μ) * (z : ℂ) ^ (1 / 2 : ℂ) * whittakerM (κ - 1 / 2) (μ - 1 / 2) z -
      (z + 2 * μ) * (1 + 2 * μ) * whittakerM κ μ z +
      (κ + μ + 1 / 2) * z ^ (1 / 2 : ℂ) * whittakerM (κ + 1 / 2) (μ + 1 / 2) z = 0 := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  have hb1 : ∀ k : ℕ, 1 + 2 * μ - 1 ≠ -k := by simpa using hμ
  have hM := kummerM_contiguous_b (a := μ - κ + 1 / 2) hb1 (z := z)
  have hP : z ^ (μ + 1 / 2 + 1 / 2) = z ^ (μ + 1 / 2) * z ^ (1 / 2 : ℂ) := cpow_add _ _ hz0
  have hQ : z ^ (μ + 1 / 2) = z ^ (μ - 1 / 2 + 1 / 2) * z ^ (1 / 2 : ℂ) := by
    rw [← cpow_add _ _ hz0]; congr 1; ring
  have hs : z ^ (1 / 2 : ℂ) * z ^ (1 / 2 : ℂ) = z := by
    rw [← cpow_add _ _ hz0]; norm_num
  unfold whittakerM
  rw [show μ - 1 / 2 - (κ - 1 / 2) + 1 / 2 = μ - κ + 1 / 2 by ring,
    show μ + 1 / 2 - (κ + 1 / 2) + 1 / 2 = μ - κ + 1 / 2 by ring,
    show 1 + 2 * (μ - 1 / 2) = 1 + 2 * μ - 1 by ring,
    show 1 + 2 * (μ + 1 / 2) = 1 + 2 * μ + 1 by ring, hP, hQ]
  linear_combination (exp (-z / 2) * z ^ (μ - 1 / 2 + 1 / 2) * z ^ (1 / 2 : ℂ)) * hM +
    (exp (-z / 2) * z ^ (μ - 1 / 2 + 1 / 2) * z ^ (1 / 2 : ℂ) * (1 + 2 * μ - (μ - κ + 1 / 2)) *
      kummerM (μ - κ + 1 / 2) (1 + 2 * μ + 1) z) * hs

/-- Identity under the stated parameter and domain assumptions: `(κ - μ - 1 / 2) * whittakerM (κ -
1 / 2) (μ + 1 / 2) z + (1 + 2 * μ) * z ^ (1 / 2 : ℂ) * whittakerM κ μ z - (κ + μ + 1 / 2) *
whittakerM (κ + 1 / 2) (μ + 1 / 2) z = 0`. -/
@[dlmf 13.15.E3]
theorem whittakerM_contiguous_shift {κ μ z : ℂ}
    (hμ : ∀ k : ℕ, 1 + 2 * μ ≠ -k) (hz : z ∈ slitPlane) :
    (κ - μ - 1 / 2) * whittakerM (κ - 1 / 2) (μ + 1 / 2) z +
      (1 + 2 * μ) * z ^ (1 / 2 : ℂ) * whittakerM κ μ z -
      (κ + μ + 1 / 2) * whittakerM (κ + 1 / 2) (μ + 1 / 2) z = 0 := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  have hM := kummerM_contiguous_shift_b_succ (a := μ - κ + 1 / 2) hμ (z := z)
  have hP : z ^ (μ + 1 / 2 + 1 / 2) = z ^ (μ + 1 / 2) * z ^ (1 / 2 : ℂ) := cpow_add _ _ hz0
  unfold whittakerM
  rw [show μ + 1 / 2 - (κ - 1 / 2) + 1 / 2 = μ - κ + 1 / 2 + 1 by ring,
    show μ + 1 / 2 - (κ + 1 / 2) + 1 / 2 = μ - κ + 1 / 2 by ring,
    show 1 + 2 * (μ + 1 / 2) = 1 + 2 * μ + 1 by ring, hP]
  linear_combination (-(exp (-z / 2) * z ^ (μ + 1 / 2) * z ^ (1 / 2 : ℂ))) * hM

/-- Identity under the stated parameter and domain assumptions: `2 * μ * whittakerM (κ - 1 / 2) (μ
- 1 / 2) z - 2 * μ * whittakerM (κ + 1 / 2) (μ - 1 / 2) z - z ^ (1 / 2 : ℂ) * whittakerM κ μ z
= 0`. -/
@[dlmf 13.15.E4]
theorem whittakerM_contiguous_half {κ μ z : ℂ}
    (hμ : ∀ k : ℕ, 2 * μ ≠ -k) (hz : z ∈ slitPlane) :
    2 * μ * whittakerM (κ - 1 / 2) (μ - 1 / 2) z -
      2 * μ * whittakerM (κ + 1 / 2) (μ - 1 / 2) z -
      z ^ (1 / 2 : ℂ) * whittakerM κ μ z = 0 := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  have hb1 : ∀ k : ℕ, 1 + 2 * μ - 1 ≠ -k := by simpa using hμ
  have hM := kummerM_contiguous_shift_a (a := μ - κ + 1 / 2) hb1 (z := z)
  rw [sub_add_cancel] at hM
  have hQ : z ^ (μ + 1 / 2) = z ^ (μ - 1 / 2 + 1 / 2) * z ^ (1 / 2 : ℂ) := by
    rw [← cpow_add _ _ hz0]; congr 1; ring
  have hs : z ^ (1 / 2 : ℂ) * z ^ (1 / 2 : ℂ) = z := by
    rw [← cpow_add _ _ hz0]; norm_num
  unfold whittakerM
  rw [show μ - 1 / 2 - (κ - 1 / 2) + 1 / 2 = μ - κ + 1 / 2 by ring,
    show μ - 1 / 2 - (κ + 1 / 2) + 1 / 2 = μ - κ + 1 / 2 - 1 by ring,
    show 1 + 2 * (μ - 1 / 2) = 1 + 2 * μ - 1 by ring, hQ]
  linear_combination (exp (-z / 2) * z ^ (μ - 1 / 2 + 1 / 2)) * hM -
    (exp (-z / 2) * z ^ (μ - 1 / 2 + 1 / 2) * kummerM (μ - κ + 1 / 2) (1 + 2 * μ) z) * hs

/-- Identity under the stated parameter and domain assumptions: `2 * μ * (1 + 2 * μ) * whittakerM
κ μ z - 2 * μ * (1 + 2 * μ) * z ^ (1 / 2 : ℂ) * whittakerM (κ - 1 / 2) (μ - 1 / 2) z - (κ - μ
- 1 / 2) * z ^ (1 / 2 : ℂ) * whittakerM (κ - 1 / 2) (μ + 1 / 2) z = 0`. -/
@[dlmf 13.15.E5]
theorem whittakerM_contiguous_mixed {κ μ z : ℂ}
    (hμ : ∀ k : ℕ, 2 * μ ≠ -k) (hz : z ∈ slitPlane) :
    2 * μ * (1 + 2 * μ) * whittakerM κ μ z -
      2 * μ * (1 + 2 * μ) * z ^ (1 / 2 : ℂ) * whittakerM (κ - 1 / 2) (μ - 1 / 2) z -
      (κ - μ - 1 / 2) * z ^ (1 / 2 : ℂ) * whittakerM (κ - 1 / 2) (μ + 1 / 2) z = 0 := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  have hb1 : ∀ k : ℕ, 1 + 2 * μ - 1 ≠ -k := by simpa using hμ
  have hM := kummerM_contiguous_mixed_b_pred (a := μ - κ + 1 / 2) hb1 (z := z)
  have hP : z ^ (μ + 1 / 2 + 1 / 2) = z ^ (μ + 1 / 2) * z ^ (1 / 2 : ℂ) := cpow_add _ _ hz0
  have hQ : z ^ (μ + 1 / 2) = z ^ (μ - 1 / 2 + 1 / 2) * z ^ (1 / 2 : ℂ) := by
    rw [← cpow_add _ _ hz0]; congr 1; ring
  have hs : z ^ (1 / 2 : ℂ) * z ^ (1 / 2 : ℂ) = z := by
    rw [← cpow_add _ _ hz0]; norm_num
  unfold whittakerM
  rw [show μ - 1 / 2 - (κ - 1 / 2) + 1 / 2 = μ - κ + 1 / 2 by ring,
    show μ + 1 / 2 - (κ - 1 / 2) + 1 / 2 = μ - κ + 1 / 2 + 1 by ring,
    show 1 + 2 * (μ - 1 / 2) = 1 + 2 * μ - 1 by ring,
    show 1 + 2 * (μ + 1 / 2) = 1 + 2 * μ + 1 by ring, hP, hQ]
  linear_combination (exp (-z / 2) * z ^ (μ - 1 / 2 + 1 / 2) * z ^ (1 / 2 : ℂ)) * hM +
    (exp (-z / 2) * z ^ (μ - 1 / 2 + 1 / 2) * z ^ (1 / 2 : ℂ) * (μ - κ + 1 / 2) *
      kummerM (μ - κ + 1 / 2 + 1) (1 + 2 * μ + 1) z) * hs

/-- Identity under the stated parameter and domain assumptions: `2 * μ * (1 + 2 * μ) * z ^ (1 / 2
: ℂ) * whittakerM (κ + 1 / 2) (μ - 1 / 2) z + (z - 2 * μ) * (1 + 2 * μ) * whittakerM κ μ z +
(κ - μ - 1 / 2) * z ^ (1 / 2 : ℂ) * whittakerM (κ - 1 / 2) (μ + 1 / 2) z = 0`. -/
@[dlmf 13.15.E6]
theorem whittakerM_contiguous_up {κ μ z : ℂ}
    (hμ : ∀ k : ℕ, 2 * μ ≠ -k) (hz : z ∈ slitPlane) :
    2 * μ * (1 + 2 * μ) * z ^ (1 / 2 : ℂ) * whittakerM (κ + 1 / 2) (μ - 1 / 2) z +
      (z - 2 * μ) * (1 + 2 * μ) * whittakerM κ μ z +
      (κ - μ - 1 / 2) * z ^ (1 / 2 : ℂ) * whittakerM (κ - 1 / 2) (μ + 1 / 2) z = 0 := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  have hb1 : ∀ k : ℕ, 1 + 2 * μ - 1 ≠ -k := by simpa using hμ
  have hM := kummerM_contiguous_up_aux (a := μ - κ + 1 / 2) hb1 (z := z)
  have hP : z ^ (μ + 1 / 2 + 1 / 2) = z ^ (μ + 1 / 2) * z ^ (1 / 2 : ℂ) := cpow_add _ _ hz0
  have hQ : z ^ (μ + 1 / 2) = z ^ (μ - 1 / 2 + 1 / 2) * z ^ (1 / 2 : ℂ) := by
    rw [← cpow_add _ _ hz0]; congr 1; ring
  have hs : z ^ (1 / 2 : ℂ) * z ^ (1 / 2 : ℂ) = z := by
    rw [← cpow_add _ _ hz0]; norm_num
  unfold whittakerM
  rw [show μ - 1 / 2 - (κ + 1 / 2) + 1 / 2 = μ - κ + 1 / 2 - 1 by ring,
    show μ + 1 / 2 - (κ - 1 / 2) + 1 / 2 = μ - κ + 1 / 2 + 1 by ring,
    show 1 + 2 * (μ - 1 / 2) = 1 + 2 * μ - 1 by ring,
    show 1 + 2 * (μ + 1 / 2) = 1 + 2 * μ + 1 by ring, hP, hQ]
  linear_combination (exp (-z / 2) * z ^ (μ - 1 / 2 + 1 / 2) * z ^ (1 / 2 : ℂ)) * hM -
    (exp (-z / 2) * z ^ (μ - 1 / 2 + 1 / 2) * z ^ (1 / 2 : ℂ) * (μ - κ + 1 / 2) *
      kummerM (μ - κ + 1 / 2 + 1) (1 + 2 * μ + 1) z) * hs

/-- Identity under the stated parameter and domain assumptions: `2 * μ * (1 + 2 * μ) * z ^ (1 / 2
: ℂ) * whittakerM (κ + 1 / 2) (μ - 1 / 2) z - 2 * μ * (1 + 2 * μ) * whittakerM κ μ z + (κ + μ
+ 1 / 2) * z ^ (1 / 2 : ℂ) * whittakerM (κ + 1 / 2) (μ + 1 / 2) z = 0`. -/
@[dlmf 13.15.E7]
theorem whittakerM_contiguous_up_shift {κ μ z : ℂ}
    (hμ : ∀ k : ℕ, 2 * μ ≠ -k) (hz : z ∈ slitPlane) :
    2 * μ * (1 + 2 * μ) * z ^ (1 / 2 : ℂ) * whittakerM (κ + 1 / 2) (μ - 1 / 2) z -
      2 * μ * (1 + 2 * μ) * whittakerM κ μ z +
      (κ + μ + 1 / 2) * z ^ (1 / 2 : ℂ) * whittakerM (κ + 1 / 2) (μ + 1 / 2) z = 0 := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  have hb1 : ∀ k : ℕ, 1 + 2 * μ - 1 ≠ -k := by simpa using hμ
  have hM := kummerM_contiguous_up_shift_aux (a := μ - κ + 1 / 2) hb1 (z := z)
  have hP : z ^ (μ + 1 / 2 + 1 / 2) = z ^ (μ + 1 / 2) * z ^ (1 / 2 : ℂ) := cpow_add _ _ hz0
  have hQ : z ^ (μ + 1 / 2) = z ^ (μ - 1 / 2 + 1 / 2) * z ^ (1 / 2 : ℂ) := by
    rw [← cpow_add _ _ hz0]; congr 1; ring
  have hs : z ^ (1 / 2 : ℂ) * z ^ (1 / 2 : ℂ) = z := by
    rw [← cpow_add _ _ hz0]; norm_num
  unfold whittakerM
  rw [show μ - 1 / 2 - (κ + 1 / 2) + 1 / 2 = μ - κ + 1 / 2 - 1 by ring,
    show μ + 1 / 2 - (κ + 1 / 2) + 1 / 2 = μ - κ + 1 / 2 by ring,
    show 1 + 2 * (μ - 1 / 2) = 1 + 2 * μ - 1 by ring,
    show 1 + 2 * (μ + 1 / 2) = 1 + 2 * μ + 1 by ring, hP, hQ]
  linear_combination (exp (-z / 2) * z ^ (μ - 1 / 2 + 1 / 2) * z ^ (1 / 2 : ℂ)) * hM +
    (exp (-z / 2) * z ^ (μ - 1 / 2 + 1 / 2) * z ^ (1 / 2 : ℂ) * (1 + 2 * μ - (μ - κ + 1 / 2)) *
      kummerM (μ - κ + 1 / 2) (1 + 2 * μ + 1) z) * hs

/-- Powers in the Whittaker prefactors. -/
theorem cpow_add_half {z : ℂ} (hz : z ≠ 0) (s : ℂ) : z ^ (s + 1 / 2) = z ^ (1 / 2 : ℂ) * z ^ s := by
  rw [cpow_add _ _ hz, mul_comm]

/-- Powers in the Whittaker prefactors. -/
theorem whittaker_pows {z μ : ℂ} (hz0 : z ≠ 0) :
    z ^ (1 / 2 + μ) = z ^ (1 / 2 : ℂ) * z ^ μ ∧
    z ^ (1 / 2 + (μ + 1 / 2)) = z ^ (1 / 2 : ℂ) * z ^ (1 / 2 : ℂ) * z ^ μ ∧
    z ^ (1 / 2 + (μ - 1 / 2)) = z ^ μ ∧
    z ^ (1 / 2 : ℂ) * z ^ (1 / 2 : ℂ) = z := by
  refine ⟨by rw [cpow_add _ _ hz0], ?_, by congr 1; ring, ?_⟩
  · rw [show (1 : ℂ) / 2 + (μ + 1 / 2) = 1 / 2 + 1 / 2 + μ by ring, cpow_add _ _ hz0,
      cpow_add _ _ hz0]
  · rw [← cpow_add _ _ hz0]; norm_num

/-- Identity under the stated parameter and domain assumptions: `whittakerW (κ + 1 / 2) (μ + 1 /
2) z - z ^ (1 / 2 : ℂ) * whittakerW κ μ z + (κ - μ - 1 / 2) * whittakerW (κ - 1 / 2) (μ + 1 /
2) z = 0`. -/
@[dlmf 13.15.E8]
theorem whittakerW_contiguous_up (κ μ : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    whittakerW (κ + 1 / 2) (μ + 1 / 2) z - z ^ (1 / 2 : ℂ) * whittakerW κ μ z +
      (κ - μ - 1 / 2) * whittakerW (κ - 1 / 2) (μ + 1 / 2) z = 0 := by
  have hz0 := slitPlane_ne_zero hz
  have h := kummerU_contiguous_a_b (1 / 2 + μ - κ) (1 + 2 * μ + 1) z hz0
  unfold whittakerW
  rw [show 1 / 2 + (μ + 1 / 2) - (κ + 1 / 2) = 1 / 2 + μ - κ by ring,
    show 1 / 2 + (μ + 1 / 2) - (κ - 1 / 2) = 1 / 2 + μ - κ + 1 by ring,
    show 1 + 2 * (μ + 1 / 2) = 1 + 2 * μ + 1 by ring,
    show 1 / 2 + (μ + 1 / 2) = (1 / 2 + μ) + 1 / 2 by ring, cpow_add_half hz0]
  rw [show 1 + 2 * μ + 1 - 1 = 1 + 2 * μ by ring] at h
  linear_combination exp (-z / 2) * z ^ (1 / 2 : ℂ) * z ^ (1 / 2 + μ) * h

/-- Identity under the stated parameter and domain assumptions: `whittakerW (κ + 1 / 2) (μ - 1 /
2) z - z ^ (1 / 2 : ℂ) * whittakerW κ μ z + (κ + μ - 1 / 2) * whittakerW (κ - 1 / 2) (μ - 1 /
2) z = 0`. -/
@[dlmf 13.15.E9]
theorem whittakerW_contiguous_down (κ μ : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    whittakerW (κ + 1 / 2) (μ - 1 / 2) z - z ^ (1 / 2 : ℂ) * whittakerW κ μ z +
      (κ + μ - 1 / 2) * whittakerW (κ - 1 / 2) (μ - 1 / 2) z = 0 := by
  have hz0 := slitPlane_ne_zero hz
  have h := kummerU_contiguous_shift_a (1 / 2 + μ - κ) (1 + 2 * μ - 1) z hz0
  unfold whittakerW
  rw [show 1 / 2 + (μ - 1 / 2) - (κ + 1 / 2) = 1 / 2 + μ - κ - 1 by ring,
    show 1 / 2 + (μ - 1 / 2) - (κ - 1 / 2) = 1 / 2 + μ - κ by ring,
    show 1 + 2 * (μ - 1 / 2) = 1 + 2 * μ - 1 by ring,
    show (1 : ℂ) / 2 + (μ - 1 / 2) = μ by ring,
    show z ^ (1 / 2 + μ) = z ^ (1 / 2 : ℂ) * z ^ μ by rw [cpow_add _ _ hz0]]
  rw [show 1 + 2 * μ - 1 + 1 = 1 + 2 * μ by ring] at h
  have hzz : z ^ (1 / 2 : ℂ) * z ^ (1 / 2 : ℂ) = z := by
    rw [← cpow_add _ _ hz0]; norm_num
  linear_combination exp (-z / 2) * z ^ μ * h - exp (-z / 2) * z ^ μ *
    kummerU (1 / 2 + μ - κ) (1 + 2 * μ) z * hzz

/-- Identity under the stated parameter and domain assumptions: `2 * μ * whittakerW κ μ z - z ^ (1
/ 2 : ℂ) * whittakerW (κ + 1 / 2) (μ + 1 / 2) z + z ^ (1 / 2 : ℂ) * whittakerW (κ + 1 / 2) (μ
- 1 / 2) z = 0`. -/
@[dlmf 13.15.E10]
theorem whittakerW_contiguous_mu (κ μ : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    2 * μ * whittakerW κ μ z - z ^ (1 / 2 : ℂ) * whittakerW (κ + 1 / 2) (μ + 1 / 2) z +
      z ^ (1 / 2 : ℂ) * whittakerW (κ + 1 / 2) (μ - 1 / 2) z = 0 := by
  have hz0 := slitPlane_ne_zero hz
  obtain ⟨p1, p2, p3, hzz⟩ := whittaker_pows (μ := μ) hz0
  have h10 := kummerU_contiguous_shift_a (1 / 2 + μ - κ) (1 + 2 * μ) z hz0
  have h9 := kummerU_contiguous_a_b (1 / 2 + μ - κ - 1) (1 + 2 * μ) z hz0
  rw [show 1 / 2 + μ - κ - 1 + 1 = 1 / 2 + μ - κ by ring] at h9
  unfold whittakerW
  rw [show 1 / 2 + (μ + 1 / 2) - (κ + 1 / 2) = 1 / 2 + μ - κ by ring,
    show 1 / 2 + (μ - 1 / 2) - (κ + 1 / 2) = 1 / 2 + μ - κ - 1 by ring,
    show 1 + 2 * (μ + 1 / 2) = 1 + 2 * μ + 1 by ring,
    show 1 + 2 * (μ - 1 / 2) = 1 + 2 * μ - 1 by ring, p1, p2, p3]
  linear_combination exp (-z / 2) * z ^ (1 / 2 : ℂ) * z ^ μ * (h10 - h9) -
    exp (-z / 2) * z ^ (1 / 2 : ℂ) * z ^ μ * kummerU (1 / 2 + μ - κ) (1 + 2 * μ + 1) z * hzz

/-- Identity under the stated parameter and domain assumptions: `whittakerW (κ + 1) μ z + (2 * κ -
z) * whittakerW κ μ z + (κ - μ - 1 / 2) * (κ + μ - 1 / 2) * whittakerW (κ - 1) μ z = 0`. -/
@[dlmf 13.15.E11]
theorem whittakerW_contiguous_kappa (κ μ z : ℂ) (hz : z ≠ 0) :
    whittakerW (κ + 1) μ z + (2 * κ - z) * whittakerW κ μ z +
      (κ - μ - 1 / 2) * (κ + μ - 1 / 2) * whittakerW (κ - 1) μ z = 0 := by
  have h7 := kummerU_contiguous_a (1 / 2 + μ - κ) (1 + 2 * μ) z hz
  unfold whittakerW
  rw [show 1 / 2 + μ - (κ + 1) = 1 / 2 + μ - κ - 1 by ring,
    show 1 / 2 + μ - (κ - 1) = 1 / 2 + μ - κ + 1 by ring]
  linear_combination exp (-z / 2) * z ^ (1 / 2 + μ) * h7

/-- Identity under the stated parameter and domain assumptions: `(κ - μ - 1 / 2) * z ^ (1 / 2 : ℂ)
* whittakerW (κ - 1 / 2) (μ + 1 / 2) z + 2 * μ * whittakerW κ μ z - (κ + μ - 1 / 2) * z ^ (1 /
2 : ℂ) * whittakerW (κ - 1 / 2) (μ - 1 / 2) z = 0`. -/
@[dlmf 13.15.E12]
theorem whittakerW_contiguous_mixed (κ μ : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    (κ - μ - 1 / 2) * z ^ (1 / 2 : ℂ) * whittakerW (κ - 1 / 2) (μ + 1 / 2) z +
      2 * μ * whittakerW κ μ z -
      (κ + μ - 1 / 2) * z ^ (1 / 2 : ℂ) * whittakerW (κ - 1 / 2) (μ - 1 / 2) z = 0 := by
  have hz0 := slitPlane_ne_zero hz
  obtain ⟨p1, p2, p3, hzz⟩ := whittaker_pows (μ := μ) hz0
  have h14 := kummerU_ode_contiguous (1 / 2 + μ - κ - 1) (1 + 2 * μ - 1) z hz0
  have h10 := kummerU_contiguous_shift_a (1 / 2 + μ - κ) (1 + 2 * μ - 1) z hz0
  rw [show 1 / 2 + μ - κ - 1 + 2 = 1 / 2 + μ - κ + 1 by ring,
    show 1 + 2 * μ - 1 + 2 = 1 + 2 * μ + 1 by ring,
    show 1 / 2 + μ - κ - 1 + 1 = 1 / 2 + μ - κ by ring,
    show 1 + 2 * μ - 1 + 1 = 1 + 2 * μ by ring] at h14
  rw [show 1 + 2 * μ - 1 + 1 = 1 + 2 * μ by ring] at h10
  unfold whittakerW
  rw [show 1 / 2 + (μ + 1 / 2) - (κ - 1 / 2) = 1 / 2 + μ - κ + 1 by ring,
    show 1 / 2 + (μ - 1 / 2) - (κ - 1 / 2) = 1 / 2 + μ - κ by ring,
    show 1 + 2 * (μ + 1 / 2) = 1 + 2 * μ + 1 by ring,
    show 1 + 2 * (μ - 1 / 2) = 1 + 2 * μ - 1 by ring, p1, p2, p3]
  linear_combination (-(exp (-z / 2) * z ^ (1 / 2 : ℂ) * z ^ μ)) * (h14 + h10) +
    (κ - μ - 1 / 2) * exp (-z / 2) * z ^ (1 / 2 : ℂ) * z ^ μ * kummerU (1 / 2 + μ - κ + 1) (1 + 2 * μ + 1) z * hzz

/-- Identity under the stated parameter and domain assumptions: `(κ + μ - 1 / 2) * z ^ (1 / 2 : ℂ)
* whittakerW (κ - 1 / 2) (μ - 1 / 2) z - (z + 2 * μ) * whittakerW κ μ z + z ^ (1 / 2 : ℂ) *
whittakerW (κ + 1 / 2) (μ + 1 / 2) z = 0`. -/
@[dlmf 13.15.E13]
theorem whittakerW_contiguous_sum (κ μ : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    (κ + μ - 1 / 2) * z ^ (1 / 2 : ℂ) * whittakerW (κ - 1 / 2) (μ - 1 / 2) z -
      (z + 2 * μ) * whittakerW κ μ z +
      z ^ (1 / 2 : ℂ) * whittakerW (κ + 1 / 2) (μ + 1 / 2) z = 0 := by
  have hz0 := slitPlane_ne_zero hz
  obtain ⟨p1, p2, p3, hzz⟩ := whittaker_pows (μ := μ) hz0
  have h8 := kummerU_contiguous_b (1 / 2 + μ - κ) (1 + 2 * μ) z hz0
  unfold whittakerW
  rw [show 1 / 2 + (μ - 1 / 2) - (κ - 1 / 2) = 1 / 2 + μ - κ by ring,
    show 1 / 2 + (μ + 1 / 2) - (κ + 1 / 2) = 1 / 2 + μ - κ by ring,
    show 1 + 2 * (μ + 1 / 2) = 1 + 2 * μ + 1 by ring,
    show 1 + 2 * (μ - 1 / 2) = 1 + 2 * μ - 1 by ring, p1, p2, p3]
  linear_combination exp (-z / 2) * z ^ (1 / 2 : ℂ) * z ^ μ * h8 +
    exp (-z / 2) * z ^ (1 / 2 : ℂ) * z ^ μ * kummerU (1 / 2 + μ - κ) (1 + 2 * μ + 1) z * hzz

/-- Identity under the stated parameter and domain assumptions: `(κ - μ - 1 / 2) * z ^ (1 / 2 : ℂ)
* whittakerW (κ - 1 / 2) (μ + 1 / 2) z - (z - 2 * μ) * whittakerW κ μ z + z ^ (1 / 2 : ℂ) *
whittakerW (κ + 1 / 2) (μ - 1 / 2) z = 0`. -/
@[dlmf 13.15.E14]
theorem whittakerW_contiguous_diff (κ μ : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    (κ - μ - 1 / 2) * z ^ (1 / 2 : ℂ) * whittakerW (κ - 1 / 2) (μ + 1 / 2) z -
      (z - 2 * μ) * whittakerW κ μ z +
      z ^ (1 / 2 : ℂ) * whittakerW (κ + 1 / 2) (μ - 1 / 2) z = 0 := by
  have hz0 := slitPlane_ne_zero hz
  obtain ⟨p1, p2, p3, hzz⟩ := whittaker_pows (μ := μ) hz0
  have h14 := kummerU_ode_contiguous (1 / 2 + μ - κ - 1) (1 + 2 * μ - 1) z hz0
  rw [show 1 / 2 + μ - κ - 1 + 2 = 1 / 2 + μ - κ + 1 by ring,
    show 1 + 2 * μ - 1 + 2 = 1 + 2 * μ + 1 by ring,
    show 1 / 2 + μ - κ - 1 + 1 = 1 / 2 + μ - κ by ring,
    show 1 + 2 * μ - 1 + 1 = 1 + 2 * μ by ring] at h14
  unfold whittakerW
  rw [show 1 / 2 + (μ + 1 / 2) - (κ - 1 / 2) = 1 / 2 + μ - κ + 1 by ring,
    show 1 / 2 + (μ - 1 / 2) - (κ + 1 / 2) = 1 / 2 + μ - κ - 1 by ring,
    show 1 + 2 * (μ + 1 / 2) = 1 + 2 * μ + 1 by ring,
    show 1 + 2 * (μ - 1 / 2) = 1 + 2 * μ - 1 by ring, p1, p2, p3]
  linear_combination (-(exp (-z / 2) * z ^ (1 / 2 : ℂ) * z ^ μ)) * h14 +
    (κ - μ - 1 / 2) * exp (-z / 2) * z ^ (1 / 2 : ℂ) * z ^ μ * kummerU (1 / 2 + μ - κ + 1) (1 + 2 * μ + 1) z * hzz

/-- Iterates of `mulDerivMul` only depend on the function near the point. -/
private lemma iterate_mulDerivMul_congr {U : Set ℂ} (hU : IsOpen U) {f g : ℂ → ℂ}
    (h : ∀ w ∈ U, f w = g w) (n : ℕ) :
    ∀ w ∈ U, mulDerivMul^[n] f w = mulDerivMul^[n] g w := by
  induction n with
  | zero => intro w hw; simpa using h w hw
  | succ n ih =>
    intro w hw
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', mulDerivMul, mulDerivMul]
    congr 1
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [hU.mem_nhds hw] with t ht
    rw [ih t ht]

/-- `e^{w/2} e^{-w/2} = 1`. -/
private lemma exp_half_mul_exp_neg_half (w : ℂ) : exp (w / 2) * exp (-w / 2) = 1 := by
  rw [← Complex.exp_add, show w / 2 + -w / 2 = (0 : ℂ) by ring, Complex.exp_zero]

/-- `e^{-w/2} e^{-w/2} = e^{-w}`. -/
private lemma exp_neg_half_mul_self (w : ℂ) : exp (-w / 2) * exp (-w / 2) = exp (-w) := by
  rw [← Complex.exp_add]; congr 1; ring

/-- `w^s w^t = w^u` for `w ≠ 0` and `s + t = u`. -/
private lemma cpow_mul_cpow_eq {w : ℂ} (hw : w ≠ 0) {s t u : ℂ} (h : s + t = u) :
    w ^ s * w ^ t = w ^ u := by
  rw [← cpow_add _ _ hw, h]

/-- An iterated Whittaker-M derivative with regular initial and shifted denominators. -/
@[dlmf 13.15.E15]
theorem iteratedDeriv_exp_mul_whittakerM {κ μ : ℂ} (n : ℕ) {z : ℂ}
    (hμ : ∀ k : ℕ, 1 + 2 * μ ≠ -k) (hz : z ∈ slitPlane)
    (hshift : ∀ k : ℕ, 1 + 2 * μ - n ≠ -k) :
    iteratedDeriv n (fun w => exp (w / 2) * w ^ (μ - 1 / 2) * whittakerM κ μ w) z =
      (-1 : ℂ) ^ n * poch (-2 * μ) n * exp (z / 2) * z ^ (μ - (n + 1) / 2) *
        whittakerM (κ - n / 2) (μ - n / 2) z := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  have heq : (fun w => exp (w / 2) * w ^ (μ - 1 / 2) * whittakerM κ μ w) =ᶠ[𝓝 z]
      (fun w => w ^ (1 + 2 * μ - 1) * kummerM (μ - κ + 1 / 2) (1 + 2 * μ) w) := by
    filter_upwards [isOpen_slitPlane.mem_nhds hz] with w hw
    have h2 := cpow_mul_cpow_eq (slitPlane_ne_zero hw) (s := μ - 1 / 2) (t := μ + 1 / 2)
      (u := 1 + 2 * μ - 1) (by ring)
    unfold whittakerM
    linear_combination (w ^ (μ - 1 / 2) * w ^ (μ + 1 / 2) *
      kummerM (μ - κ + 1 / 2) (1 + 2 * μ) w) * exp_half_mul_exp_neg_half w +
      (kummerM (μ - κ + 1 / 2) (1 + 2 * μ) w) * h2
  rw [heq.iteratedDeriv_eq n, iteratedDeriv_mul_cpow_kummerM n hshift hz]
  unfold whittakerM
  rw [show μ - (n : ℂ) / 2 - (κ - n / 2) + 1 / 2 = μ - κ + 1 / 2 by ring,
    show 1 + 2 * (μ - (n : ℂ) / 2) = 1 + 2 * μ - n by ring,
    show (-2 * μ : ℂ) = 1 - (1 + 2 * μ - n) - n by ring, DLMF.Hypergeometric.poch_reflect]
  have h2 := cpow_mul_cpow_eq hz0 (s := μ - (n + 1) / 2) (t := μ - n / 2 + 1 / 2)
      (u := 1 + 2 * μ - n - 1) (by ring)
  have hs : ((-1 : ℂ) ^ n) * (-1) ^ n = 1 := by rw [← mul_pow]; simp
  linear_combination (-(poch (1 + 2 * μ - n) n * kummerM (μ - κ + 1 / 2) (1 + 2 * μ - n) z *
    z ^ (μ - (n + 1) / 2) * z ^ (μ - n / 2 + 1 / 2) * exp (z / 2) * exp (-z / 2))) * hs -
    (poch (1 + 2 * μ - n) n * kummerM (μ - κ + 1 / 2) (1 + 2 * μ - n) z *
    z ^ (μ - (n + 1) / 2) * z ^ (μ - n / 2 + 1 / 2)) * exp_half_mul_exp_neg_half z -
    (poch (1 + 2 * μ - n) n * kummerM (μ - κ + 1 / 2) (1 + 2 * μ - n) z) * h2

/-- Identity under the stated parameter and domain assumptions: `iteratedDeriv n (fun w => exp (w
/ 2) * w ^ (-μ - 1 / 2) * whittakerM κ μ w) z = poch (1 / 2 + μ - κ) n / poch (1 + 2 * μ) n *
exp (z / 2) * z ^ (-μ - (n + 1) / 2) * whittakerM (κ - n / 2) (μ + n / 2) z`. -/
@[dlmf 13.15.E16]
theorem iteratedDeriv_exp_mul_whittakerM_neg {κ μ : ℂ} (n : ℕ) {z : ℂ}
    (hμ : ∀ k : ℕ, 1 + 2 * μ ≠ -k) (hz : z ∈ slitPlane) :
    iteratedDeriv n (fun w => exp (w / 2) * w ^ (-μ - 1 / 2) * whittakerM κ μ w) z =
      poch (1 / 2 + μ - κ) n / poch (1 + 2 * μ) n * exp (z / 2) *
        z ^ (-μ - (n + 1) / 2) * whittakerM (κ - n / 2) (μ + n / 2) z := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  have heq : (fun w => exp (w / 2) * w ^ (-μ - 1 / 2) * whittakerM κ μ w) =ᶠ[𝓝 z]
      kummerM (μ - κ + 1 / 2) (1 + 2 * μ) := by
    filter_upwards [isOpen_slitPlane.mem_nhds hz] with w hw
    have hw0 : w ≠ 0 := slitPlane_ne_zero hw
    have h1 : exp (w / 2) * exp (-w / 2) = 1 := by
      rw [← Complex.exp_add, show w / 2 + -w / 2 = (0 : ℂ) by ring, Complex.exp_zero]
    have h2 : w ^ (-μ - 1 / 2) * w ^ (μ + 1 / 2) = 1 := by
      rw [← cpow_add _ _ hw0, show -μ - 1 / 2 + (μ + 1 / 2) = (0 : ℂ) by ring, cpow_zero]
    unfold whittakerM
    linear_combination (w ^ (-μ - 1 / 2) * w ^ (μ + 1 / 2) *
      kummerM (μ - κ + 1 / 2) (1 + 2 * μ) w) * h1 +
      (kummerM (μ - κ + 1 / 2) (1 + 2 * μ) w) * h2
  rw [heq.iteratedDeriv_eq n, iteratedDeriv_kummerM n hμ]
  beta_reduce
  unfold whittakerM
  rw [show μ + (n : ℂ) / 2 - (κ - n / 2) + 1 / 2 = μ - κ + 1 / 2 + n by ring,
    show (1 : ℂ) + 2 * (μ + n / 2) = 1 + 2 * μ + n by ring,
    show (1 : ℂ) / 2 + μ - κ = μ - κ + 1 / 2 by ring]
  have h1 : exp (z / 2) * exp (-z / 2) = 1 := by
    rw [← Complex.exp_add, show z / 2 + -z / 2 = (0 : ℂ) by ring, Complex.exp_zero]
  have h2 : z ^ (-μ - ((n : ℂ) + 1) / 2) * z ^ (μ + n / 2 + 1 / 2) = 1 := by
    rw [← cpow_add _ _ hz0, show -μ - ((n : ℂ) + 1) / 2 + (μ + n / 2 + 1 / 2) = (0 : ℂ) by ring,
      cpow_zero]
  linear_combination (-(poch (μ - κ + 1 / 2) n / poch (1 + 2 * μ) n *
      kummerM (μ - κ + 1 / 2 + n) (1 + 2 * μ + n) z)) * h1 -
    (poch (μ - κ + 1 / 2) n / poch (1 + 2 * μ) n *
      kummerM (μ - κ + 1 / 2 + n) (1 + 2 * μ + n) z * exp (z / 2) * exp (-z / 2)) * h2

/-- Identity under the stated parameter and domain assumptions: `mulDerivMul^[n] (fun w => exp (w
/ 2) * w ^ (-κ - 1) * whittakerM κ μ w) z = poch (1 / 2 + μ - κ) n * exp (z / 2) * z ^ (n - κ
- 1) * whittakerM (κ - n) μ z`. -/
@[dlmf 13.15.E17]
theorem iterate_mulDerivMul_whittakerM {κ μ : ℂ} (n : ℕ) {z : ℂ}
    (hμ : ∀ k : ℕ, 1 + 2 * μ ≠ -k) (hz : z ∈ slitPlane) :
    mulDerivMul^[n] (fun w => exp (w / 2) * w ^ (-κ - 1) * whittakerM κ μ w) z =
      poch (1 / 2 + μ - κ) n * exp (z / 2) * z ^ (n - κ - 1) *
        whittakerM (κ - n) μ z := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  have hfun : ∀ w ∈ slitPlane, exp (w / 2) * w ^ (-κ - 1) * whittakerM κ μ w =
      w ^ (μ - κ + 1 / 2 - 1) * kummerM (μ - κ + 1 / 2) (1 + 2 * μ) w := by
    intro w hw
    have hw0 : w ≠ 0 := slitPlane_ne_zero hw
    have h1 : exp (w / 2) * exp (-w / 2) = 1 := by
      rw [← Complex.exp_add, show w / 2 + -w / 2 = (0 : ℂ) by ring, Complex.exp_zero]
    have h2 : w ^ (-κ - 1) * w ^ (μ + 1 / 2) = w ^ (μ - κ + 1 / 2 - 1) := by
      rw [← cpow_add _ _ hw0]; congr 1; ring
    unfold whittakerM
    linear_combination (w ^ (-κ - 1) * w ^ (μ + 1 / 2) *
      kummerM (μ - κ + 1 / 2) (1 + 2 * μ) w) * h1 +
      (kummerM (μ - κ + 1 / 2) (1 + 2 * μ) w) * h2
  rw [iterate_mulDerivMul_congr isOpen_slitPlane hfun n z hz,
    iterate_mulDerivMul_kummerM n hμ hz]
  unfold whittakerM
  rw [show μ - (κ - (n : ℂ)) + 1 / 2 = μ - κ + 1 / 2 + n by ring,
    show (1 : ℂ) / 2 + μ - κ = μ - κ + 1 / 2 by ring]
  have h1 : exp (z / 2) * exp (-z / 2) = 1 := by
    rw [← Complex.exp_add, show z / 2 + -z / 2 = (0 : ℂ) by ring, Complex.exp_zero]
  have h2 : z ^ ((n : ℂ) - κ - 1) * z ^ (μ + 1 / 2) = z ^ (μ - κ + 1 / 2 + n - 1) := by
    rw [← cpow_add _ _ hz0]; congr 1; ring
  linear_combination (-(poch (μ - κ + 1 / 2) n * kummerM (μ - κ + 1 / 2 + n) (1 + 2 * μ) z *
      z ^ ((n : ℂ) - κ - 1) * z ^ (μ + 1 / 2))) * h1 -
    (poch (μ - κ + 1 / 2) n * kummerM (μ - κ + 1 / 2 + n) (1 + 2 * μ) z) * h2

/-- An iterated Whittaker-M derivative with regular initial and shifted denominators. -/
@[dlmf 13.15.E18]
theorem iteratedDeriv_exp_neg_whittakerM {κ μ : ℂ} (n : ℕ) {z : ℂ}
    (hμ : ∀ k : ℕ, 1 + 2 * μ ≠ -k) (hz : z ∈ slitPlane)
    (hshift : ∀ k : ℕ, 1 + 2 * μ - n ≠ -k) :
    iteratedDeriv n (fun w => exp (-w / 2) * w ^ (μ - 1 / 2) * whittakerM κ μ w) z =
      (-1 : ℂ) ^ n * poch (-2 * μ) n * exp (-z / 2) * z ^ (μ - (n + 1) / 2) *
        whittakerM (κ + n / 2) (μ - n / 2) z := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  have heq : (fun w => exp (-w / 2) * w ^ (μ - 1 / 2) * whittakerM κ μ w) =ᶠ[𝓝 z]
      (fun w => w ^ (1 + 2 * μ - 1) * exp (-w) * kummerM (μ - κ + 1 / 2) (1 + 2 * μ) w) := by
    filter_upwards [isOpen_slitPlane.mem_nhds hz] with w hw
    have h2 := cpow_mul_cpow_eq (slitPlane_ne_zero hw) (s := μ - 1 / 2) (t := μ + 1 / 2)
      (u := 1 + 2 * μ - 1) (by ring)
    unfold whittakerM
    linear_combination (w ^ (μ - 1 / 2) * w ^ (μ + 1 / 2) *
      kummerM (μ - κ + 1 / 2) (1 + 2 * μ) w) * exp_neg_half_mul_self w +
      (exp (-w) * kummerM (μ - κ + 1 / 2) (1 + 2 * μ) w) * h2
  rw [heq.iteratedDeriv_eq n, iteratedDeriv_mul_cpow_exp_neg_kummerM n hshift hz]
  unfold whittakerM
  rw [show μ - (n : ℂ) / 2 - (κ + n / 2) + 1 / 2 = μ - κ + 1 / 2 - n by ring,
    show 1 + 2 * (μ - (n : ℂ) / 2) = 1 + 2 * μ - n by ring,
    show (-2 * μ : ℂ) = 1 - (1 + 2 * μ - n) - n by ring, DLMF.Hypergeometric.poch_reflect]
  have h2 := cpow_mul_cpow_eq hz0 (s := μ - (n + 1) / 2) (t := μ - n / 2 + 1 / 2)
      (u := 1 + 2 * μ - n - 1) (by ring)
  have hs : ((-1 : ℂ) ^ n) * (-1) ^ n = 1 := by rw [← mul_pow]; simp
  linear_combination (-(poch (1 + 2 * μ - n) n * kummerM (μ - κ + 1 / 2 - n) (1 + 2 * μ - n) z *
    z ^ (μ - (n + 1) / 2) * z ^ (μ - n / 2 + 1 / 2) * exp (-z / 2) * exp (-z / 2))) * hs -
    (poch (1 + 2 * μ - n) n * kummerM (μ - κ + 1 / 2 - n) (1 + 2 * μ - n) z *
    z ^ (μ - (n + 1) / 2) * z ^ (μ - n / 2 + 1 / 2)) * exp_neg_half_mul_self z -
    (poch (1 + 2 * μ - n) n * kummerM (μ - κ + 1 / 2 - n) (1 + 2 * μ - n) z * exp (-z)) * h2

/-- Identity under the stated parameter and domain assumptions: `iteratedDeriv n (fun w => exp (-w
/ 2) * w ^ (-μ - 1 / 2) * whittakerM κ μ w) z = (-1 : ℂ) ^ n * poch (1 / 2 + μ + κ) n / poch
(1 + 2 * μ) n * exp (-z / 2) * z ^ (-μ - (n + 1) / 2) * whittakerM (κ + n / 2) (μ + n / 2) z`. -/
@[dlmf 13.15.E19]
theorem iteratedDeriv_exp_neg_whittakerM_neg {κ μ : ℂ} (n : ℕ) {z : ℂ}
    (hμ : ∀ k : ℕ, 1 + 2 * μ ≠ -k) (hz : z ∈ slitPlane) :
    iteratedDeriv n (fun w => exp (-w / 2) * w ^ (-μ - 1 / 2) * whittakerM κ μ w) z =
      (-1 : ℂ) ^ n * poch (1 / 2 + μ + κ) n / poch (1 + 2 * μ) n * exp (-z / 2) *
        z ^ (-μ - (n + 1) / 2) * whittakerM (κ + n / 2) (μ + n / 2) z := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  have heq : (fun w => exp (-w / 2) * w ^ (-μ - 1 / 2) * whittakerM κ μ w) =ᶠ[𝓝 z]
      (fun w => exp (-w) * kummerM (μ - κ + 1 / 2) (1 + 2 * μ) w) := by
    filter_upwards [isOpen_slitPlane.mem_nhds hz] with w hw
    have hw0 : w ≠ 0 := slitPlane_ne_zero hw
    have h1 : exp (-w / 2) * exp (-w / 2) = exp (-w) := by
      rw [← Complex.exp_add]; congr 1; ring
    have h2 : w ^ (-μ - 1 / 2) * w ^ (μ + 1 / 2) = 1 := by
      rw [← cpow_add _ _ hw0, show -μ - 1 / 2 + (μ + 1 / 2) = (0 : ℂ) by ring, cpow_zero]
    unfold whittakerM
    linear_combination (w ^ (-μ - 1 / 2) * w ^ (μ + 1 / 2) *
      kummerM (μ - κ + 1 / 2) (1 + 2 * μ) w) * h1 +
      (exp (-w) * kummerM (μ - κ + 1 / 2) (1 + 2 * μ) w) * h2
  rw [heq.iteratedDeriv_eq n, iteratedDeriv_exp_neg_kummerM n hμ]
  beta_reduce
  unfold whittakerM
  rw [show μ + (n : ℂ) / 2 - (κ + n / 2) + 1 / 2 = μ - κ + 1 / 2 by ring,
    show (1 : ℂ) + 2 * (μ + n / 2) = 1 + 2 * μ + n by ring,
    show (1 : ℂ) + 2 * μ - (μ - κ + 1 / 2) = 1 / 2 + μ + κ by ring]
  have h1 : exp (-z / 2) * exp (-z / 2) = exp (-z) := by
    rw [← Complex.exp_add]; congr 1; ring
  have h2 : z ^ (-μ - ((n : ℂ) + 1) / 2) * z ^ (μ + n / 2 + 1 / 2) = 1 := by
    rw [← cpow_add _ _ hz0, show -μ - ((n : ℂ) + 1) / 2 + (μ + n / 2 + 1 / 2) = (0 : ℂ) by ring,
      cpow_zero]
  linear_combination (-((-1 : ℂ) ^ n * poch (1 / 2 + μ + κ) n / poch (1 + 2 * μ) n *
      kummerM (μ - κ + 1 / 2) (1 + 2 * μ + n) z *
      z ^ (-μ - ((n : ℂ) + 1) / 2) * z ^ (μ + n / 2 + 1 / 2))) * h1 -
    ((-1 : ℂ) ^ n * poch (1 / 2 + μ + κ) n / poch (1 + 2 * μ) n *
      kummerM (μ - κ + 1 / 2) (1 + 2 * μ + n) z * exp (-z)) * h2

/-- Identity under the stated parameter and domain assumptions: `mulDerivMul^[n] (fun w => exp (-w
/ 2) * w ^ (κ - 1) * whittakerM κ μ w) z = poch (1 / 2 + μ + κ) n * exp (-z / 2) * z ^ (κ + n
- 1) * whittakerM (κ + n) μ z`. -/
@[dlmf 13.15.E20]
theorem iterate_mulDerivMul_exp_neg_whittakerM {κ μ : ℂ} (n : ℕ) {z : ℂ}
    (hμ : ∀ k : ℕ, 1 + 2 * μ ≠ -k) (hz : z ∈ slitPlane) :
    mulDerivMul^[n] (fun w => exp (-w / 2) * w ^ (κ - 1) * whittakerM κ μ w) z =
      poch (1 / 2 + μ + κ) n * exp (-z / 2) * z ^ (κ + n - 1) *
        whittakerM (κ + n) μ z := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  have hfun : ∀ w ∈ slitPlane, exp (-w / 2) * w ^ (κ - 1) * whittakerM κ μ w =
      w ^ (1 + 2 * μ - (μ - κ + 1 / 2) - 1) * exp (-w) *
        kummerM (μ - κ + 1 / 2) (1 + 2 * μ) w := by
    intro w hw
    have hw0 : w ≠ 0 := slitPlane_ne_zero hw
    have h1 : exp (-w / 2) * exp (-w / 2) = exp (-w) := by
      rw [← Complex.exp_add]; congr 1; ring
    have h2 : w ^ (κ - 1) * w ^ (μ + 1 / 2) = w ^ (1 + 2 * μ - (μ - κ + 1 / 2) - 1) := by
      rw [← cpow_add _ _ hw0]; congr 1; ring
    unfold whittakerM
    linear_combination (w ^ (κ - 1) * w ^ (μ + 1 / 2) *
      kummerM (μ - κ + 1 / 2) (1 + 2 * μ) w) * h1 +
      (exp (-w) * kummerM (μ - κ + 1 / 2) (1 + 2 * μ) w) * h2
  rw [iterate_mulDerivMul_congr isOpen_slitPlane hfun n z hz,
    iterate_mulDerivMul_exp_neg_kummerM n hμ hz]
  unfold whittakerM
  rw [show μ - (κ + (n : ℂ)) + 1 / 2 = μ - κ + 1 / 2 - n by ring,
    show (1 : ℂ) + 2 * μ - (μ - κ + 1 / 2) = 1 / 2 + μ + κ by ring]
  have h1 : exp (-z / 2) * exp (-z / 2) = exp (-z) := by
    rw [← Complex.exp_add]; congr 1; ring
  have h2 : z ^ (κ + (n : ℂ) - 1) * z ^ (μ + 1 / 2) = z ^ (1 / 2 + μ + κ + n - 1) := by
    rw [← cpow_add _ _ hz0]; congr 1; ring
  linear_combination (-(poch (1 / 2 + μ + κ) n * kummerM (μ - κ + 1 / 2 - n) (1 + 2 * μ) z *
      z ^ (κ + (n : ℂ) - 1) * z ^ (μ + 1 / 2))) * h1 -
    (poch (1 / 2 + μ + κ) n * kummerM (μ - κ + 1 / 2 - n) (1 + 2 * μ) z * exp (-z)) * h2

/-- Identity under the stated parameter and domain assumptions: `iteratedDeriv n (fun w => exp (w
/ 2) * w ^ (-μ - 1 / 2) * whittakerW κ μ w) z = (-1 : ℂ) ^ n * poch (1 / 2 + μ - κ) n * exp (z
/ 2) * z ^ (-μ - (n + 1) / 2) * whittakerW (κ - n / 2) (μ + n / 2) z`. -/
@[dlmf 13.15.E21]
theorem iteratedDeriv_exp_mul_whittakerW {κ μ : ℂ} (n : ℕ) {z : ℂ} (hz : z ∈ slitPlane) :
    iteratedDeriv n (fun w => exp (w / 2) * w ^ (-μ - 1 / 2) * whittakerW κ μ w) z =
      (-1 : ℂ) ^ n * poch (1 / 2 + μ - κ) n * exp (z / 2) *
        z ^ (-μ - (n + 1) / 2) * whittakerW (κ - n / 2) (μ + n / 2) z := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  have heq : (fun w => exp (w / 2) * w ^ (-μ - 1 / 2) * whittakerW κ μ w) =ᶠ[𝓝 z]
      kummerU (1 / 2 + μ - κ) (1 + 2 * μ) := by
    filter_upwards [isOpen_slitPlane.mem_nhds hz] with w hw
    have h2 := cpow_mul_cpow_eq (slitPlane_ne_zero hw) (s := -μ - 1 / 2) (t := 1 / 2 + μ)
      (u := 0) (by ring)
    rw [cpow_zero] at h2
    unfold whittakerW
    linear_combination (w ^ (-μ - 1 / 2) * w ^ (1 / 2 + μ) *
      kummerU (1 / 2 + μ - κ) (1 + 2 * μ) w) * exp_half_mul_exp_neg_half w +
      (kummerU (1 / 2 + μ - κ) (1 + 2 * μ) w) * h2
  rw [heq.iteratedDeriv_eq n, iteratedDeriv_kummerU _ _ n hz]
  unfold whittakerW
  rw [show 1 / 2 + (μ + (n : ℂ) / 2) - (κ - n / 2) = 1 / 2 + μ - κ + n by ring,
    show 1 + 2 * (μ + (n : ℂ) / 2) = 1 + 2 * μ + n by ring]
  have h2 := cpow_mul_cpow_eq hz0 (s := -μ - (n + 1) / 2) (t := 1 / 2 + (μ + n / 2))
      (u := 0) (by ring)
  rw [cpow_zero] at h2
  linear_combination (-((-1 : ℂ) ^ n * poch (1 / 2 + μ - κ) n *
    kummerU (1 / 2 + μ - κ + n) (1 + 2 * μ + n) z *
    z ^ (-μ - (n + 1) / 2) * z ^ (1 / 2 + (μ + n / 2)))) * exp_half_mul_exp_neg_half z -
    ((-1 : ℂ) ^ n * poch (1 / 2 + μ - κ) n * kummerU (1 / 2 + μ - κ + n) (1 + 2 * μ + n) z) * h2

/-- Identity under the stated parameter and domain assumptions: `iteratedDeriv n (fun w => exp (w
/ 2) * w ^ (μ - 1 / 2) * whittakerW κ μ w) z = (-1 : ℂ) ^ n * poch (1 / 2 - μ - κ) n * exp (z
/ 2) * z ^ (μ - (n + 1) / 2) * whittakerW (κ - n / 2) (μ - n / 2) z`. -/
@[dlmf 13.15.E22]
theorem iteratedDeriv_exp_mul_whittakerW_pos {κ μ : ℂ} (n : ℕ) {z : ℂ}
    (hz : z ∈ slitPlane) :
    iteratedDeriv n (fun w => exp (w / 2) * w ^ (μ - 1 / 2) * whittakerW κ μ w) z =
      (-1 : ℂ) ^ n * poch (1 / 2 - μ - κ) n * exp (z / 2) *
        z ^ (μ - (n + 1) / 2) * whittakerW (κ - n / 2) (μ - n / 2) z := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  have heq : (fun w => exp (w / 2) * w ^ (μ - 1 / 2) * whittakerW κ μ w) =ᶠ[𝓝 z]
      (fun w => w ^ (1 + 2 * μ - 1) * kummerU (1 / 2 + μ - κ) (1 + 2 * μ) w) := by
    filter_upwards [isOpen_slitPlane.mem_nhds hz] with w hw
    have h2 := cpow_mul_cpow_eq (slitPlane_ne_zero hw) (s := μ - 1 / 2) (t := 1 / 2 + μ)
      (u := 1 + 2 * μ - 1) (by ring)
    unfold whittakerW
    linear_combination (w ^ (μ - 1 / 2) * w ^ (1 / 2 + μ) *
      kummerU (1 / 2 + μ - κ) (1 + 2 * μ) w) * exp_half_mul_exp_neg_half w +
      (kummerU (1 / 2 + μ - κ) (1 + 2 * μ) w) * h2
  rw [heq.iteratedDeriv_eq n, iteratedDeriv_mul_cpow_kummerU _ _ n hz]
  unfold whittakerW
  rw [show 1 / 2 + (μ - (n : ℂ) / 2) - (κ - n / 2) = 1 / 2 + μ - κ by ring,
    show 1 + 2 * (μ - (n : ℂ) / 2) = 1 + 2 * μ - n by ring,
    show 1 / 2 + μ - κ - (1 + 2 * μ) + 1 = 1 / 2 - μ - κ by ring]
  have h2 := cpow_mul_cpow_eq hz0 (s := μ - (n + 1) / 2) (t := 1 / 2 + (μ - n / 2))
      (u := 1 + 2 * μ - n - 1) (by ring)
  linear_combination (-((-1 : ℂ) ^ n * poch (1 / 2 - μ - κ) n *
    kummerU (1 / 2 + μ - κ) (1 + 2 * μ - n) z *
    z ^ (μ - (n + 1) / 2) * z ^ (1 / 2 + (μ - n / 2)))) * exp_half_mul_exp_neg_half z -
    ((-1 : ℂ) ^ n * poch (1 / 2 - μ - κ) n * kummerU (1 / 2 + μ - κ) (1 + 2 * μ - n) z) * h2

/-- Identity under the stated parameter and domain assumptions: `mulDerivMul^[n] (fun w => exp (w
/ 2) * w ^ (-κ - 1) * whittakerW κ μ w) z = poch (1 / 2 + μ - κ) n * poch (1 / 2 - μ - κ) n *
exp (z / 2) * z ^ (n - κ - 1) * whittakerW (κ - n) μ z`. -/
@[dlmf 13.15.E23]
theorem iterate_mulDerivMul_whittakerW {κ μ : ℂ} (n : ℕ) {z : ℂ} (hz : z ∈ slitPlane) :
    mulDerivMul^[n] (fun w => exp (w / 2) * w ^ (-κ - 1) * whittakerW κ μ w) z =
      poch (1 / 2 + μ - κ) n * poch (1 / 2 - μ - κ) n * exp (z / 2) *
        z ^ (n - κ - 1) * whittakerW (κ - n) μ z := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  have hfun : ∀ w ∈ slitPlane, exp (w / 2) * w ^ (-κ - 1) * whittakerW κ μ w =
      w ^ (1 / 2 + μ - κ - 1) * kummerU (1 / 2 + μ - κ) (1 + 2 * μ) w := by
    intro w hw
    have h2 := cpow_mul_cpow_eq (slitPlane_ne_zero hw) (s := -κ - 1) (t := 1 / 2 + μ)
      (u := 1 / 2 + μ - κ - 1) (by ring)
    unfold whittakerW
    linear_combination (w ^ (-κ - 1) * w ^ (1 / 2 + μ) *
      kummerU (1 / 2 + μ - κ) (1 + 2 * μ) w) * exp_half_mul_exp_neg_half w +
      (kummerU (1 / 2 + μ - κ) (1 + 2 * μ) w) * h2
  rw [iterate_mulDerivMul_congr isOpen_slitPlane hfun n z hz,
    iterate_mulDerivMul_kummerU _ _ n hz]
  unfold whittakerW
  rw [show 1 / 2 + μ - (κ - (n : ℂ)) = 1 / 2 + μ - κ + n by ring,
    show 1 / 2 + μ - κ - (1 + 2 * μ) + 1 = 1 / 2 - μ - κ by ring]
  have h2 := cpow_mul_cpow_eq hz0 (s := (n : ℂ) - κ - 1) (t := 1 / 2 + μ)
      (u := 1 / 2 + μ - κ + n - 1) (by ring)
  linear_combination (-(poch (1 / 2 + μ - κ) n * poch (1 / 2 - μ - κ) n *
    kummerU (1 / 2 + μ - κ + n) (1 + 2 * μ) z *
    z ^ ((n : ℂ) - κ - 1) * z ^ (1 / 2 + μ))) * exp_half_mul_exp_neg_half z -
    (poch (1 / 2 + μ - κ) n * poch (1 / 2 - μ - κ) n *
      kummerU (1 / 2 + μ - κ + n) (1 + 2 * μ) z) * h2

/-- Identity under the stated parameter and domain assumptions: `iteratedDeriv n (fun w => exp (-w
/ 2) * w ^ (-μ - 1 / 2) * whittakerW κ μ w) z = (-1 : ℂ) ^ n * exp (-z / 2) * z ^ (-μ - (n +
1) / 2) * whittakerW (κ + n / 2) (μ + n / 2) z`. -/
@[dlmf 13.15.E24]
theorem iteratedDeriv_exp_neg_whittakerW {κ μ : ℂ} (n : ℕ) {z : ℂ} (hz : z ∈ slitPlane) :
    iteratedDeriv n (fun w => exp (-w / 2) * w ^ (-μ - 1 / 2) * whittakerW κ μ w) z =
      (-1 : ℂ) ^ n * exp (-z / 2) * z ^ (-μ - (n + 1) / 2) *
        whittakerW (κ + n / 2) (μ + n / 2) z := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  have heq : (fun w => exp (-w / 2) * w ^ (-μ - 1 / 2) * whittakerW κ μ w) =ᶠ[𝓝 z]
      (fun w => exp (-w) * kummerU (1 / 2 + μ - κ) (1 + 2 * μ) w) := by
    filter_upwards [isOpen_slitPlane.mem_nhds hz] with w hw
    have h2 := cpow_mul_cpow_eq (slitPlane_ne_zero hw) (s := -μ - 1 / 2) (t := 1 / 2 + μ)
      (u := 0) (by ring)
    rw [cpow_zero] at h2
    unfold whittakerW
    linear_combination (w ^ (-μ - 1 / 2) * w ^ (1 / 2 + μ) *
      kummerU (1 / 2 + μ - κ) (1 + 2 * μ) w) * exp_neg_half_mul_self w +
      (exp (-w) * kummerU (1 / 2 + μ - κ) (1 + 2 * μ) w) * h2
  rw [heq.iteratedDeriv_eq n, iteratedDeriv_exp_neg_kummerU _ _ n hz]
  unfold whittakerW
  rw [show 1 / 2 + (μ + (n : ℂ) / 2) - (κ + n / 2) = 1 / 2 + μ - κ by ring,
    show 1 + 2 * (μ + (n : ℂ) / 2) = 1 + 2 * μ + n by ring]
  have h2 := cpow_mul_cpow_eq hz0 (s := -μ - (n + 1) / 2) (t := 1 / 2 + (μ + n / 2))
      (u := 0) (by ring)
  rw [cpow_zero] at h2
  linear_combination (-((-1 : ℂ) ^ n * kummerU (1 / 2 + μ - κ) (1 + 2 * μ + n) z *
    z ^ (-μ - (n + 1) / 2) * z ^ (1 / 2 + (μ + n / 2)))) * exp_neg_half_mul_self z -
    ((-1 : ℂ) ^ n * exp (-z) * kummerU (1 / 2 + μ - κ) (1 + 2 * μ + n) z) * h2

/-- Identity under the stated parameter and domain assumptions: `iteratedDeriv n (fun w => exp (-w
/ 2) * w ^ (μ - 1 / 2) * whittakerW κ μ w) z = (-1 : ℂ) ^ n * exp (-z / 2) * z ^ (μ - (n + 1)
/ 2) * whittakerW (κ + n / 2) (μ - n / 2) z`. -/
@[dlmf 13.15.E25]
theorem iteratedDeriv_exp_neg_whittakerW_pos {κ μ : ℂ} (n : ℕ) {z : ℂ}
    (hz : z ∈ slitPlane) :
    iteratedDeriv n (fun w => exp (-w / 2) * w ^ (μ - 1 / 2) * whittakerW κ μ w) z =
      (-1 : ℂ) ^ n * exp (-z / 2) * z ^ (μ - (n + 1) / 2) *
        whittakerW (κ + n / 2) (μ - n / 2) z := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  have heq : (fun w => exp (-w / 2) * w ^ (μ - 1 / 2) * whittakerW κ μ w) =ᶠ[𝓝 z]
      (fun w => w ^ (1 + 2 * μ - 1) * exp (-w) * kummerU (1 / 2 + μ - κ) (1 + 2 * μ) w) := by
    filter_upwards [isOpen_slitPlane.mem_nhds hz] with w hw
    have h2 := cpow_mul_cpow_eq (slitPlane_ne_zero hw) (s := μ - 1 / 2) (t := 1 / 2 + μ)
      (u := 1 + 2 * μ - 1) (by ring)
    unfold whittakerW
    linear_combination (w ^ (μ - 1 / 2) * w ^ (1 / 2 + μ) *
      kummerU (1 / 2 + μ - κ) (1 + 2 * μ) w) * exp_neg_half_mul_self w +
      (exp (-w) * kummerU (1 / 2 + μ - κ) (1 + 2 * μ) w) * h2
  rw [heq.iteratedDeriv_eq n, iteratedDeriv_mul_cpow_exp_neg_kummerU _ _ n hz]
  unfold whittakerW
  rw [show 1 / 2 + (μ - (n : ℂ) / 2) - (κ + n / 2) = 1 / 2 + μ - κ - n by ring,
    show 1 + 2 * (μ - (n : ℂ) / 2) = 1 + 2 * μ - n by ring]
  have h2 := cpow_mul_cpow_eq hz0 (s := μ - (n + 1) / 2) (t := 1 / 2 + (μ - n / 2))
      (u := 1 + 2 * μ - n - 1) (by ring)
  linear_combination (-((-1 : ℂ) ^ n * kummerU (1 / 2 + μ - κ - n) (1 + 2 * μ - n) z *
    z ^ (μ - (n + 1) / 2) * z ^ (1 / 2 + (μ - n / 2)))) * exp_neg_half_mul_self z -
    ((-1 : ℂ) ^ n * exp (-z) * kummerU (1 / 2 + μ - κ - n) (1 + 2 * μ - n) z) * h2

/-- Identity under the stated parameter and domain assumptions: `mulDerivMul^[n] (fun w => exp (-w
/ 2) * w ^ (κ - 1) * whittakerW κ μ w) z = (-1 : ℂ) ^ n * exp (-z / 2) * z ^ (κ + n - 1) *
whittakerW (κ + n) μ z`. -/
@[dlmf 13.15.E26]
theorem iterate_mulDerivMul_exp_neg_whittakerW {κ μ : ℂ} (n : ℕ) {z : ℂ}
    (hz : z ∈ slitPlane) :
    mulDerivMul^[n] (fun w => exp (-w / 2) * w ^ (κ - 1) * whittakerW κ μ w) z =
      (-1 : ℂ) ^ n * exp (-z / 2) * z ^ (κ + n - 1) * whittakerW (κ + n) μ z := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  have hfun : ∀ w ∈ slitPlane, exp (-w / 2) * w ^ (κ - 1) * whittakerW κ μ w =
      w ^ (1 + 2 * μ - (1 / 2 + μ - κ) - 1) * exp (-w) *
        kummerU (1 / 2 + μ - κ) (1 + 2 * μ) w := by
    intro w hw
    have h2 := cpow_mul_cpow_eq (slitPlane_ne_zero hw) (s := κ - 1) (t := 1 / 2 + μ)
      (u := 1 + 2 * μ - (1 / 2 + μ - κ) - 1) (by ring)
    unfold whittakerW
    linear_combination (w ^ (κ - 1) * w ^ (1 / 2 + μ) *
      kummerU (1 / 2 + μ - κ) (1 + 2 * μ) w) * exp_neg_half_mul_self w +
      (exp (-w) * kummerU (1 / 2 + μ - κ) (1 + 2 * μ) w) * h2
  rw [iterate_mulDerivMul_congr isOpen_slitPlane hfun n z hz,
    iterate_mulDerivMul_exp_neg_kummerU _ _ n hz]
  unfold whittakerW
  rw [show 1 / 2 + μ - (κ + (n : ℂ)) = 1 / 2 + μ - κ - n by ring]
  have h2 := cpow_mul_cpow_eq hz0 (s := κ + (n : ℂ) - 1) (t := 1 / 2 + μ)
      (u := 1 + 2 * μ - (1 / 2 + μ - κ) + n - 1) (by ring)
  linear_combination (-((-1 : ℂ) ^ n * kummerU (1 / 2 + μ - κ - n) (1 + 2 * μ) z *
    z ^ (κ + (n : ℂ) - 1) * z ^ (1 / 2 + μ))) * exp_neg_half_mul_self z -
    ((-1 : ℂ) ^ n * exp (-z) * kummerU (1 / 2 + μ - κ - n) (1 + 2 * μ) z) * h2

end DLMF.Confluent

end
end
