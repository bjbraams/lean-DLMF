/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.JacobiElliptic.Basic.QuarterPeriods

/-!
# Inversion between the elliptic modulus and lattice parameter

The theta-constant inversion formulas identify the principal modulus parameter with its lattice
counterpart.

Source references and common attribution are retained in
`DLMF.JacobiElliptic.Basic`.
-/

@[expose] public section

open Complex DLMF.Elliptic

open scoped Real

noncomputable section

namespace DLMF.JacobiElliptic

/-! ### DLMF 22.2.2: the inversion `k = θ₂²/θ₃²(iK'/K)`

The real case `0 < k < 1` comes from Jacobi's `K = (π/2)θ₃²` for a real nome (the AGM,
`Real.compEllIntKm_eq_jacobiThetaThreeNullQ`), the modular transformation `τ ↦ -1/τ` and
Jacobi's identity `θ₃⁴ = θ₂⁴ + θ₄⁴` on the imaginary axis (proved here by lattice sums), with
the intermediate value theorem for `t ↦ θ₂²/θ₃²(it)`. The complex case follows by the identity
theorem: both sides are holomorphic on the connected open domain. -/

section p22R1Inversion

open Filter Topology MeasureTheory
open scoped Interval
section
open Set

/-- `P(q) = ∑_{n∈ℤ} q^{n²+n}`, so that `θ₂(q) = q^{1/4} P(q)`. -/
noncomputable def p22R1_P (q : ℝ) : ℝ := ∑' n : ℤ, q ^ (n ^ 2 + n)

/-- Summability of the indicated series: `Summable fun n : ℤ => q ^ (n ^ 2 + n)`. -/
lemma p22R1_summable_P {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    Summable fun n : ℤ => q ^ (n ^ 2 + n) := by
  refine ((summable_zpow_abs hq0 hq1).mul_right q⁻¹).of_nonneg_of_le
    (fun _ => (zpow_pos hq0 _).le) fun n => ?_
  rw [← zpow_neg_one, ← zpow_add₀ hq0.ne']
  apply zpow_le_zpow_right_of_le_one₀ hq0 hq1.le
  rcases le_or_gt 0 n with h | h
  · rw [abs_of_nonneg h]; nlinarith
  · rw [abs_of_neg h]; nlinarith

/-- The odd sublattice `{(a,b) : a + b odd}` is parametrized by `(u,v) ↦ (u+v+1, u-v)`. -/
def p22R1_oddLatticeEquiv : ℤ × ℤ ≃ {p : ℤ × ℤ // ¬ Even (p.1 + p.2)} where
  toFun uv := ⟨(uv.1 + uv.2 + 1, uv.1 - uv.2), by
    rw [Int.not_even_iff_odd]; exact ⟨uv.1, by ring⟩⟩
  invFun p := ((p.1.1 + p.1.2 - 1) / 2, (p.1.1 - p.1.2 - 1) / 2)
  left_inv uv := by
    simp only
    rw [show uv.1 + uv.2 + 1 + (uv.1 - uv.2) - 1 = 2 * uv.1 by ring,
      show uv.1 + uv.2 + 1 - (uv.1 - uv.2) - 1 = 2 * uv.2 by ring]
    simp
  right_inv p := by
    obtain ⟨⟨a, b⟩, hp⟩ := p
    rw [Int.not_even_iff_odd] at hp
    obtain ⟨r, hr⟩ := hp
    simp only at hr ⊢
    have h1 : (a + b - 1) / 2 = r := by rw [hr]; omega
    have h2 : (a - b - 1) / 2 = r - b := by omega
    ext <;> simp [h1, h2]
    omega

/-- `θ₃(q)² - θ₄(q)² = 2q P(q²)²`. -/
lemma p22R1_three_sq_sub_four_sq {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    Real.jacobiThetaThreeNullQ q ^ 2 - Real.jacobiThetaFourNullQ q ^ 2 =
      2 * q * p22R1_P (q ^ 2) ^ 2 := by
  have hs3 := summable_zpow_sq hq0 hq1
  have hs4 := summable_neg_one_zpow_mul hq0 hq1
  have hq2 : 0 < q ^ 2 := by positivity
  have hq21 : q ^ 2 < 1 := by nlinarith
  have hsP := p22R1_summable_P hq2 hq21
  have h33 := tsum_mul_tsum_of_summable_norm hs3.norm hs3.norm
  have h44 := tsum_mul_tsum_of_summable_norm hs4.norm hs4.norm
  have hPP := tsum_mul_tsum_of_summable_norm hsP.norm hsP.norm
  have hP3 := summable_mul_of_summable_norm hs3.norm hs3.norm
  have hP4 := summable_mul_of_summable_norm hs4.norm hs4.norm
  set H : ℤ × ℤ → ℝ := fun p => q ^ (p.1 ^ 2) * q ^ (p.2 ^ 2) -
    (-1 : ℝ) ^ p.1 * q ^ (p.1 ^ 2) * ((-1 : ℝ) ^ p.2 * q ^ (p.2 ^ 2)) with hH
  have hHs : Summable H := hP3.sub hP4
  rw [Real.jacobiThetaThreeNullQ, Real.jacobiThetaFourNullQ, p22R1_P, sq, sq, sq,
      h33, h44, hPP, ← hP3.tsum_sub hP4]
  change ∑' p, H p = _
  rw [← hHs.tsum_subtype_add_tsum_subtype_compl {p : ℤ × ℤ | Even (p.1 + p.2)}]
  have heven : ∀ p : ↥({p : ℤ × ℤ | Even (p.1 + p.2)}), H p = 0 := by
    rintro ⟨⟨a, b⟩, hp⟩
    simp only [mem_ofPred_eq] at hp
    simp only [hH]
    rw [mul_mul_mul_comm, neg_one_zpow_add, hp.neg_one_zpow]
    ring
  rw [tsum_congr heven, tsum_zero, zero_add, ← tsum_mul_left]
  rw [show (∑' p : ↥({p : ℤ × ℤ | Even (p.1 + p.2)}ᶜ), H p) =
      ∑' p : {p : ℤ × ℤ // ¬ Even (p.1 + p.2)}, H p from rfl, ← p22R1_oddLatticeEquiv.tsum_eq]
  refine tsum_congr fun uv => ?_
  simp only [p22R1_oddLatticeEquiv, Equiv.coe_fn_mk, hH]
  have hodd : Odd (uv.1 + uv.2 + 1 + (uv.1 - uv.2)) := ⟨uv.1, by ring⟩
  rw [mul_mul_mul_comm, neg_one_zpow_add, hodd.neg_one_zpow]
  have e : q ^ ((uv.1 + uv.2 + 1) ^ 2) * q ^ ((uv.1 - uv.2) ^ 2) =
      q * ((q ^ 2) ^ (uv.1 ^ 2 + uv.1) * (q ^ 2) ^ (uv.2 ^ 2 + uv.2)) := by
    rw [← zpow_add₀ hq0.ne', ← zpow_add₀ (by positivity), ← zpow_natCast, ← zpow_mul,
      ← zpow_one_add₀ hq0.ne']
    congr 1; push_cast; ring
  rw [e]; ring

/-- `P(q)² = 2 P(q²) θ₃(q²)`. -/
lemma p22R1_P_sq {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    p22R1_P q ^ 2 = 2 * (p22R1_P (q ^ 2) * Real.jacobiThetaThreeNullQ (q ^ 2)) := by
  have hq2 : 0 < q ^ 2 := by positivity
  have hq21 : q ^ 2 < 1 := by nlinarith
  have hsP := p22R1_summable_P hq0 hq1
  have hsP' := p22R1_summable_P hq2 hq21
  have hs3' := summable_zpow_sq hq2 hq21
  have hPP := tsum_mul_tsum_of_summable_norm hsP.norm hsP.norm
  have hP3 := tsum_mul_tsum_of_summable_norm hsP'.norm hs3'.norm
  have hHs := summable_mul_of_summable_norm hsP.norm hsP.norm
  set H : ℤ × ℤ → ℝ := fun p => q ^ (p.1 ^ 2 + p.1) * q ^ (p.2 ^ 2 + p.2) with hH
  rw [p22R1_P, sq, hPP, p22R1_P, Real.jacobiThetaThreeNullQ, hP3, two_mul]
  change ∑' p, H p = _
  rw [← hHs.tsum_subtype_add_tsum_subtype_compl {p : ℤ × ℤ | Even (p.1 + p.2)}]
  congr 1
  · rw [show (∑' p : ↥{p : ℤ × ℤ | Even (p.1 + p.2)}, H p) =
      ∑' p : {p : ℤ × ℤ // Even (p.1 + p.2)}, H p from rfl, ← evenLatticeEquiv.tsum_eq]
    refine tsum_congr fun uv => ?_
    simp only [evenLatticeEquiv, Equiv.coe_fn_mk, hH]
    rw [← zpow_add₀ hq0.ne', ← zpow_add₀ (by positivity), ← zpow_natCast, ← zpow_mul]
    congr 1; push_cast; ring
  · rw [show (∑' p : ↥({p : ℤ × ℤ | Even (p.1 + p.2)}ᶜ), H p) =
        ∑' p : {p : ℤ × ℤ // ¬ Even (p.1 + p.2)}, H p from rfl,
      ← p22R1_oddLatticeEquiv.tsum_eq]
    -- reorder the product and shift `u ↦ u - 1`
    have hswap := (Equiv.prodComm ℤ ℤ).tsum_eq
      (fun p : ℤ × ℤ => (q ^ 2) ^ (p.1 ^ 2 + p.1) * (q ^ 2) ^ (p.2 ^ 2))
    have hshift := (Equiv.prodCongr (Equiv.addRight (1 : ℤ)) (Equiv.refl ℤ)).tsum_eq
      (fun p : ℤ × ℤ => (q ^ 2) ^ (p.2 ^ 2 + p.2) * (q ^ 2) ^ (p.1 ^ 2))
    rw [← hswap]
    simp only [Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]
    rw [← hshift]
    refine tsum_congr fun uv => ?_
    simp only [p22R1_oddLatticeEquiv, Equiv.coe_fn_mk, hH, Equiv.prodCongr_apply,
      Equiv.coe_refl, Equiv.coe_addRight, Prod.map_fst, Prod.map_snd, id_eq]
    rw [← zpow_add₀ hq0.ne', ← zpow_add₀ (by positivity), ← zpow_natCast, ← zpow_mul]
    congr 1; push_cast; ring

/-- Jacobi's identity for a real nome: `θ₃(q)⁴ = θ₄(q)⁴ + q P(q)⁴`, i.e. `θ₃⁴ = θ₂⁴ + θ₄⁴`. -/
lemma p22R1_jacobi_real {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    Real.jacobiThetaThreeNullQ q ^ 4 = Real.jacobiThetaFourNullQ q ^ 4 + q * p22R1_P q ^ 4 := by
  have h1 := Real.jacobiThetaThreeNullQ_sq_add_jacobiThetaFourNullQ_sq hq0 hq1
  have h2 := p22R1_three_sq_sub_four_sq hq0 hq1
  have h3 := p22R1_P_sq hq0 hq1
  have e4 : p22R1_P q ^ 4 = (p22R1_P q ^ 2) ^ 2 := by ring
  rw [e4, h3]
  linear_combination (Real.jacobiThetaThreeNullQ q ^ 2 - Real.jacobiThetaFourNullQ q ^ 2) * h1 +
    2 * Real.jacobiThetaThreeNullQ (q ^ 2) ^ 2 * h2

/-- Identity under the stated parameter and domain assumptions: `jacobiThetaTwoTau 0 (I * t) =
((Real.exp (-(π * t) / 4) * p22R1_P (Real.exp (-(π * t))) : ℝ) : ℂ)`. -/
lemma p22R1_two_eq_P (t : ℝ) :
    jacobiThetaTwoTau 0 (I * t) =
      ((Real.exp (-(π * t) / 4) * p22R1_P (Real.exp (-(π * t))) : ℝ) : ℂ) := by
  rw [jacobiThetaTwoTau, jacobiThetaThreeTau_eq_tsum, p22R1_P, ofReal_mul, ofReal_tsum,
    ← tsum_mul_left, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  rw [Complex.ofReal_zpow, Complex.ofReal_exp, Complex.ofReal_exp, ← Complex.exp_int_mul,
    ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring_nf
  rw [I_sq]
  ring

end

/-- `θ₃(0|it)` as a real function of `t`. -/
noncomputable def p22R1_B (t : ℝ) : ℝ := Real.jacobiThetaThreeNullQ (Real.exp (-(π * t)))
/-- `θ₄(0|it)` as a real function of `t`. -/
noncomputable def p22R1_C (t : ℝ) : ℝ := Real.jacobiThetaFourNullQ (Real.exp (-(π * t)))

/-- Estimate under the stated parameter and domain assumptions: `0 < Real.exp (-(π * t)) ∧
Real.exp (-(π * t)) < 1`. -/
lemma p22R1_nome {t : ℝ} (ht : 0 < t) : 0 < Real.exp (-(π * t)) ∧ Real.exp (-(π * t)) < 1 :=
  ⟨Real.exp_pos _, Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])⟩

/-- Estimate under the stated parameter and domain assumptions: `1 ≤ p22R1_B t`. -/
theorem p22R1_B_ge {t : ℝ} (ht : 0 < t) : 1 ≤ p22R1_B t :=
  Real.one_le_jacobiThetaThreeNullQ (p22R1_nome ht).1 (p22R1_nome ht).2

/-- Estimate under the stated parameter and domain assumptions: `0 < p22R1_C t`. -/
theorem p22R1_C_pos {t : ℝ} (ht : 0 < t) : 0 < p22R1_C t :=
  Real.jacobiThetaFourNullQ_pos (p22R1_nome ht).1 (p22R1_nome ht).2

/-- Identity under the stated parameter and domain assumptions: `jacobiThetaThreeTau 0 (I * t) =
p22R1_B t`. -/
theorem p22R1_three (t : ℝ) : jacobiThetaThreeTau 0 (I * t) = p22R1_B t :=
  jacobiThetaThreeTau_zero_I_mul t

/-- Identity under the stated parameter and domain assumptions: `jacobiThetaFourTau 0 (I * t) =
p22R1_C t`. -/
theorem p22R1_four (t : ℝ) : jacobiThetaFourTau 0 (I * t) = p22R1_C t :=
  jacobiThetaFourTau_zero_I_mul t

/-- Identity under the stated parameter and domain assumptions: `(t : ℂ) ^ (1 / 2 : ℂ) =
(Real.sqrt t : ℂ)`. -/
lemma p22R1_cpow_half {t : ℝ} (ht : 0 ≤ t) : (t : ℂ) ^ (1 / 2 : ℂ) = (Real.sqrt t : ℂ) := by
  rw [Real.sqrt_eq_rpow, ofReal_cpow ht]; push_cast; ring_nf

/-- Identity under the stated parameter and domain assumptions: `-1 / (I * t) = I * ((1 / t : ℝ) :
ℂ)`. -/
lemma p22R1_neg_inv_I {t : ℝ} (ht : 0 < t) : -1 / (I * t) = I * ((1 / t : ℝ) : ℂ) := by
  have : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
  push_cast
  field_simp
  rw [I_sq]

/-- Identity under the stated parameter and domain assumptions: `-I * (I * t) = (t : ℂ)`. -/
lemma p22R1_negI {t : ℝ} : -I * (I * t) = (t : ℂ) := by
  rw [← mul_assoc, neg_mul, I_mul_I]; ring

/-- Estimate under the stated parameter and domain assumptions: `0 < (I * (t : ℂ)).im`. -/
lemma p22R1_im_pos {t : ℝ} (ht : 0 < t) : 0 < (I * (t : ℂ)).im := by simpa using ht

/-- `θ₃(0|i/t) = √t θ₃(0|it)`. -/
lemma p22R1_B_inv {t : ℝ} (ht : 0 < t) : p22R1_B (1 / t) = Real.sqrt t * p22R1_B t := by
  have h := DLMF.Theta.jacobiThetaThreeTau_neg_inv (p22R1_im_pos ht) 0
  rw [p22R1_negI, p22R1_neg_inv_I ht, p22R1_cpow_half ht.le, p22R1_three] at h
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_div,
    exp_zero, one_mul, zero_mul] at h
  rw [p22R1_three] at h
  exact_mod_cast h.symm

/-- `θ₂(0|it) = θ₄(0|i/t)/√t`. -/
theorem p22R1_two {t : ℝ} (ht : 0 < t) :
    jacobiThetaTwoTau 0 (I * t) = ((p22R1_C (1 / t) / Real.sqrt t : ℝ) : ℂ) := by
  have h := DLMF.Theta.jacobiThetaTwoTau_neg_inv (p22R1_im_pos ht) 0
  rw [p22R1_negI, p22R1_neg_inv_I ht, p22R1_cpow_half ht.le] at h
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_div,
    exp_zero, one_mul, zero_mul] at h
  rw [p22R1_four] at h
  have hs : (Real.sqrt t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr ht).ne'
  push_cast
  rw [← h]; field_simp

/-- `θ₂(0|it)` as a real function, `θ₄(0|i/t)/√t`. -/
noncomputable def p22R1_A (t : ℝ) : ℝ := p22R1_C (1 / t) / Real.sqrt t

/-- Estimate under the stated parameter and domain assumptions: `0 < p22R1_A t`. -/
theorem p22R1_A_pos {t : ℝ} (ht : 0 < t) : 0 < p22R1_A t :=
  div_pos (p22R1_C_pos (by positivity)) (Real.sqrt_pos.mpr ht)

/-- Jacobi's identity on the imaginary axis: `B⁴ = A⁴ + C⁴`. -/
theorem p22R1_fourth {t : ℝ} (ht : 0 < t) :
    p22R1_B t ^ 4 = p22R1_A t ^ 4 + p22R1_C t ^ 4 := by
  have h := p22R1_jacobi_real (p22R1_nome ht).1 (p22R1_nome ht).2
  have hA : p22R1_A t = Real.exp (-(π * t) / 4) * p22R1_P (Real.exp (-(π * t))) := by
    have e := (p22R1_two ht).symm.trans (p22R1_two_eq_P t)
    exact_mod_cast e
  have he : Real.exp (-(π * t) / 4) ^ 4 = Real.exp (-(π * t)) := by
    rw [← Real.exp_nat_mul]; ring_nf
  rw [p22R1_B, p22R1_C, h, hA, mul_pow, he]
  ring

/-- Identity under the stated parameter and domain assumptions: `p22R1_A (1 / t) = p22R1_C t *
Real.sqrt t`. -/
lemma p22R1_A_inv {t : ℝ} (ht : 0 < t) : p22R1_A (1 / t) = p22R1_C t * Real.sqrt t := by
  rw [p22R1_A, one_div_one_div, Real.sqrt_div' _ ht.le, Real.sqrt_one]
  field_simp

/-- Identity under the stated parameter and domain assumptions: `p22R1_B t = Real.sqrt (1 / t) *
p22R1_B (1 / t)`. -/
lemma p22R1_B_inv' {t : ℝ} (ht : 0 < t) : p22R1_B t = Real.sqrt (1 / t) * p22R1_B (1 / t) := by
  have h := p22R1_B_inv (t := 1 / t) (by positivity)
  rwa [one_div_one_div] at h

/-- `ρ(t) = θ₂²(0|it)/θ₃²(0|it)`. -/
noncomputable def p22R1_rho (t : ℝ) : ℝ := (p22R1_A t / p22R1_B t) ^ 2

/-- Identity under the stated parameter and domain assumptions: `p22R1_rho (1 / t) = (p22R1_C t /
p22R1_B t) ^ 2`. -/
lemma p22R1_rho_inv {t : ℝ} (ht : 0 < t) :
    p22R1_rho (1 / t) = (p22R1_C t / p22R1_B t) ^ 2 := by
  rw [p22R1_rho, p22R1_A_inv ht, p22R1_B_inv ht]
  have := Real.sqrt_pos.mpr ht
  have := p22R1_B_ge ht
  congr 1
  field_simp

/-- The function `p22R1_B` is continuous on `(Set.Ioi 0)`. -/
lemma p22R1_continuousOn_B : ContinuousOn p22R1_B (Set.Ioi 0) := by
  intro t ht
  have h : ContinuousAt (fun s : ℝ => jacobiThetaThreeTau 0 (I * s)) t := by
    have h1 : ContinuousAt (fun τ => jacobiTheta₂ (0 / π) τ) (I * t) :=
      (differentiableAt_jacobiTheta₂_snd _ (p22R1_im_pos ht)).continuousAt
    exact h1.comp (f := fun s : ℝ => I * (s : ℂ)) (by fun_prop)
  have h2 := (Complex.continuous_re.continuousAt).comp h
  refine (h2.congr (Filter.Eventually.of_forall fun s => ?_)).continuousWithinAt
  simp [p22R1_three]

/-- The function `p22R1_C` is continuous on `(Set.Ioi 0)`. -/
lemma p22R1_continuousOn_C : ContinuousOn p22R1_C (Set.Ioi 0) := by
  intro t ht
  have h : ContinuousAt (fun s : ℝ => jacobiThetaFourTau 0 (I * s)) t := by
    have h1 : ContinuousAt (fun τ => jacobiTheta₂ ((0 + π / 2) / π) τ) (I * t) :=
      (differentiableAt_jacobiTheta₂_snd _ (p22R1_im_pos ht)).continuousAt
    exact h1.comp (f := fun s : ℝ => I * (s : ℂ)) (by fun_prop)
  have h2 := (Complex.continuous_re.continuousAt).comp h
  refine (h2.congr (Filter.Eventually.of_forall fun s => ?_)).continuousWithinAt
  simp [p22R1_four]

/-- The function `p22R1_rho` is continuous on `(Set.Ioi 0)`. -/
lemma p22R1_continuousOn_rho : ContinuousOn p22R1_rho (Set.Ioi 0) := by
  have hC' : ContinuousOn (fun t => p22R1_C (1 / t)) (Set.Ioi 0) :=
    p22R1_continuousOn_C.comp (continuousOn_const.div continuousOn_id fun t ht => ht.ne')
      fun t ht => by simp only [Set.mem_Ioi] at ht ⊢; positivity
  have hA : ContinuousOn p22R1_A (Set.Ioi 0) :=
    hC'.div Real.continuous_sqrt.continuousOn fun t ht => (Real.sqrt_pos.mpr ht).ne'
  exact (hA.div p22R1_continuousOn_B fun t ht => by
    have := p22R1_B_ge ht; positivity).pow 2

/-- The map `(fun t : ℝ => Real.exp (-(π * t)))` tends to `(𝓝[>] 0)` along `atTop`. -/
lemma p22R1_tendsto_nome : Tendsto (fun t : ℝ => Real.exp (-(π * t))) atTop (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun t => Real.exp_pos _⟩
  exact Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp
    (Tendsto.const_mul_atTop Real.pi_pos tendsto_id))

/-- The map `(fun t => p22R1_C t / p22R1_B t)` tends to `(𝓝 1)` along `atTop`. -/
lemma p22R1_tendsto_CB : Tendsto (fun t => p22R1_C t / p22R1_B t) atTop (𝓝 1) := by
  have h3 := Real.tendsto_jacobiThetaThreeNullQ.comp p22R1_tendsto_nome
  have h4 := Real.tendsto_jacobiThetaFourNullQ.comp p22R1_tendsto_nome
  have h := h4.div h3 one_ne_zero
  rw [div_one] at h
  exact h

/-- Every `0 < k < 1` is `θ₂²(0|it)/θ₃²(0|it)` for some `t > 0`. -/
theorem p22R1_exists_rho {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) :
    ∃ t : ℝ, 0 < t ∧ p22R1_rho t = k := by
  have hev1 : ∀ᶠ T in atTop, k < (p22R1_C T / p22R1_B T) ^ 2 := by
    have := (p22R1_tendsto_CB.pow 2)
    simp only [one_pow] at this
    exact this.eventually (lt_mem_nhds (by nlinarith))
  have hev2 : ∀ᶠ T in atTop, 1 - (p22R1_C T / p22R1_B T) ^ 4 < k ^ 2 := by
    have := ((p22R1_tendsto_CB.pow 4).const_sub 1)
    simp only [one_pow, sub_self] at this
    exact this.eventually (gt_mem_nhds (by positivity))
  obtain ⟨T, h1, h2, hT⟩ := (hev1.and (hev2.and (eventually_gt_atTop 1))).exists
  have hT0 : 0 < T := by linarith
  have hle : 1 / T ≤ T := by
    rw [div_le_iff₀ hT0]; nlinarith
  have hcont : ContinuousOn p22R1_rho (Set.Icc (1 / T) T) :=
    p22R1_continuousOn_rho.mono fun t ht => by
      simp only [Set.mem_Ioi]; exact lt_of_lt_of_le (by positivity) ht.1
  have hρT : p22R1_rho T < k := by
    have hf := p22R1_fourth hT0
    have hB := p22R1_B_ge hT0
    have hsq : p22R1_rho T ^ 2 = 1 - (p22R1_C T / p22R1_B T) ^ 4 := by
      rw [p22R1_rho]; field_simp; linarith
    have hρ0 : 0 ≤ p22R1_rho T := sq_nonneg _
    nlinarith
  have hρT' : k < p22R1_rho (1 / T) := by rw [p22R1_rho_inv hT0]; exact h1
  obtain ⟨t, ht, hte⟩ := intermediate_value_Icc' hle hcont ⟨hρT.le, hρT'.le⟩
  exact ⟨t, lt_of_lt_of_le (by positivity) ht.1, hte⟩

/-- The real case of DLMF 22.2.2 at `τ = it`: `k = ρ(t) = θ₂²/θ₃²(0|it) ∈ (0, 1)`,
`τ(k) = it`, the three relations at `τ = it`, and `K(k) = (π/2)θ₃²`, `K'(k) = t K(k)`. -/
theorem p22R1_real_at {t : ℝ} (ht : 0 < t) :
    0 < p22R1_rho t ∧ p22R1_rho t < 1 ∧ jacobiTauk (p22R1_rho t) = I * t ∧
      jacobiModulusTau (I * t) = p22R1_rho t ∧
      jacobiComodulusTau (I * t) = jacobiComodulusk (p22R1_rho t) ∧
      compEllIntKTau (I * t) = compEllIntKk (p22R1_rho t) ∧
      Real.compEllIntKm (p22R1_rho t ^ 2) = π / 2 * p22R1_B t ^ 2 ∧
      Real.compEllIntKm (1 - p22R1_rho t ^ 2) = π / 2 * t * p22R1_B t ^ 2 := by
  set k := p22R1_rho t with hk
  have hρ : p22R1_rho t = k := rfl
  have hA := p22R1_A_pos ht
  have hB := p22R1_B_ge ht
  have hB0 : 0 < p22R1_B t := by linarith
  have hC := p22R1_C_pos ht
  have hf := p22R1_fourth ht
  have hA' : jacobiThetaTwoTau 0 (I * t) = p22R1_A t := p22R1_two ht
  -- `k² = 1 - (C/B)⁴` and `1 - k² = (C/B)⁴`
  have hk2 : k ^ 2 = 1 - (p22R1_C t / p22R1_B t) ^ 4 := by
    rw [← hρ, p22R1_rho]; field_simp; linarith
  have hk0 : 0 < k := by rw [hk, p22R1_rho]; positivity
  have hk1 : k < 1 := by
    have : k ^ 2 < 1 := by
      rw [hk2]; have : 0 < (p22R1_C t / p22R1_B t) ^ 4 := by positivity
      linarith
    nlinarith
  have hKm (s : ℝ) (hs : 0 < s) : Real.compEllIntKm (1 - (p22R1_C s / p22R1_B s) ^ 4) =
      π / 2 * p22R1_B s ^ 2 :=
    Real.compEllIntKm_eq_jacobiThetaThreeNullQ (p22R1_nome hs).1 (p22R1_nome hs).2
  have hKk : compEllIntKk k = π / 2 * (p22R1_B t : ℂ) ^ 2 := by
    rw [compEllIntKk_ofReal (by nlinarith), hk2, hKm t ht]
    push_cast; ring
  have hKmk : Real.compEllIntKm (k ^ 2) = π / 2 * p22R1_B t ^ 2 := by rw [hk2, hKm t ht]
  have hKmk' : Real.compEllIntKm (1 - k ^ 2) = π / 2 * t * p22R1_B t ^ 2 := by
    have ht' : (0 : ℝ) < 1 / t := by positivity
    have e : 1 - k ^ 2 = 1 - (p22R1_C (1 / t) / p22R1_B (1 / t)) ^ 4 := by
      have h1 : p22R1_C (1 / t) = p22R1_A t * Real.sqrt t := by
        rw [p22R1_A]; field_simp [(Real.sqrt_pos.mpr ht).ne']
      rw [h1, p22R1_B_inv ht, ← hρ, p22R1_rho]
      have := Real.sqrt_pos.mpr ht
      field_simp
    rw [e, hKm _ ht', p22R1_B_inv ht, mul_pow, Real.sq_sqrt ht.le]
    ring
  have hKpk : compEllIntKpk k = π / 2 * t * (p22R1_B t : ℂ) ^ 2 := by
    have ht' : (0 : ℝ) < 1 / t := by positivity
    have e : 1 - k ^ 2 = 1 - (p22R1_C (1 / t) / p22R1_B (1 / t)) ^ 4 := by
      have h1 : p22R1_C (1 / t) = p22R1_A t * Real.sqrt t := by
        rw [p22R1_A]; field_simp [(Real.sqrt_pos.mpr ht).ne']
      rw [h1, p22R1_B_inv ht, ← hρ, p22R1_rho]
      have := Real.sqrt_pos.mpr ht
      field_simp
    rw [compEllIntKpk_ofReal (by positivity), e, hKm _ ht', p22R1_B_inv ht, mul_pow,
      Real.sq_sqrt ht.le]
    push_cast
    ring
  have hKne : compEllIntKk k ≠ 0 := by
    rw [hKk]
    exact mul_ne_zero (div_ne_zero pi_ne_zero' two_ne_zero)
      (pow_ne_zero _ (ofReal_ne_zero.mpr hB0.ne'))
  refine ⟨hk0, hk1, ?_, ?_, ?_, ?_, hKmk, hKmk'⟩
  · rw [jacobiTauk, hKpk, hKk]
    have : (p22R1_B t : ℂ) ≠ 0 := ofReal_ne_zero.mpr hB0.ne'
    have := pi_ne_zero'
    field_simp
  · rw [jacobiModulusTau, hA', p22R1_three, ← hρ, p22R1_rho]
    push_cast; ring
  · rw [jacobiComodulusTau, jacobiComodulusk, p22R1_four, p22R1_three,
      show (1 : ℂ) - (k : ℂ) ^ 2 = ((1 - k ^ 2 : ℝ) : ℂ) by push_cast; ring,
      p22R1_cpow_half (by nlinarith), hk2,
      show 1 - (1 - (p22R1_C t / p22R1_B t) ^ 4) = ((p22R1_C t / p22R1_B t) ^ 2) ^ 2 by ring,
      Real.sqrt_sq (by positivity)]
    push_cast; ring
  · rw [compEllIntKTau, p22R1_three, hKk]

/-- The real case of DLMF 22.2.2: for `0 < k < 1`, `τ(k) = it` with `t > 0` and the three
relations hold at `τ = it`. -/
lemma p22R1_inversion_real {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) :
    ∃ t : ℝ, 0 < t ∧ jacobiTauk k = I * t ∧ jacobiModulusTau (I * t) = k ∧
      jacobiComodulusTau (I * t) = jacobiComodulusk k ∧ compEllIntKTau (I * t) = compEllIntKk k := by
  obtain ⟨t, ht, hρ⟩ := p22R1_exists_rho hk0 hk1
  obtain ⟨-, -, h1, h2, h3, h4, -⟩ := p22R1_real_at ht
  rw [hρ] at h1 h2 h3 h4
  exact ⟨t, ht, h1, h2, h3, h4⟩

/-- Holomorphy of the parametric integrals `∫₀^{π/2} (1 - c(k) sin²θ)^{-1/2} dθ`. -/
lemma p22R1_differentiableOn_integral {U : Set ℂ} (hU : IsOpen U) {c : ℂ → ℂ}
    (hc : Differentiable ℂ c)
    (hslit : ∀ k ∈ U, ∀ s : ℝ, 0 ≤ s → s ≤ 1 → 1 - c k * (s : ℂ) ∈ slitPlane) :
    DifferentiableOn ℂ
      (fun k => ∫ θ in (0 : ℝ)..(π / 2), (1 - c k * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ))) U := by
  have hsq (θ : ℝ) : (Real.sin θ : ℂ) ^ 2 = ((Real.sin θ ^ 2 : ℝ) : ℂ) := by push_cast; ring
  have hsl (k : ℂ) (hk : k ∈ U) (θ : ℝ) : 1 - c k * (Real.sin θ : ℂ) ^ 2 ∈ slitPlane := by
    rw [hsq]; exact hslit k hk _ (sq_nonneg _) (Real.sin_sq_le_one θ)
  refine Complex.differentiableOn_intervalIntegral_of_locally_dominated hU 0 (π / 2)
    (fun k hk => ?_) (Eventually.of_forall fun θ => ?_) (fun k hk => ?_)
  · exact (Continuous.cpow (by fun_prop) continuous_const (hsl k hk)).aestronglyMeasurable
  · intro k hk
    exact ((((hc k).mul (differentiableAt_const _)).const_sub 1).cpow_const
      (hsl k hk θ)).differentiableWithinAt
  · obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU k hk
    have hsub : Metric.closedBall k (ε / 2) ⊆ U :=
      (Metric.closedBall_subset_ball (by linarith)).trans hball
    have hcpt : IsCompact (Metric.closedBall k (ε / 2) ×ˢ Set.Icc (0 : ℝ) 1) :=
      (isCompact_closedBall _ _).prod isCompact_Icc
    have hcont : ContinuousOn (fun p : ℂ × ℝ => (1 - c p.1 * (p.2 : ℂ)) ^ (-(1 / 2 : ℂ)))
        (Metric.closedBall k (ε / 2) ×ˢ Set.Icc (0 : ℝ) 1) := by
      intro p hp
      have hcc : Continuous c := hc.continuous
      refine ContinuousAt.continuousWithinAt (ContinuousAt.cpow (by fun_prop)
        continuousAt_const (hslit p.1 (hsub hp.1) p.2 hp.2.1 hp.2.2))
    obtain ⟨M, hM⟩ := hcpt.exists_bound_of_continuousOn hcont
    refine ⟨Metric.closedBall k (ε / 2), Metric.closedBall_mem_nhds _ (by linarith),
      fun _ => M, ?_, Eventually.of_forall fun θ y hy => ?_⟩
    · rw [Set.uIoc_of_le (by positivity)]
      exact (integrableOn_Icc_iff_integrableOn_Ioc (μ := volume)).mp
        continuous_const.integrableOn_Icc
    · rw [hsq]
      exact hM (y, Real.sin θ ^ 2) ⟨hy, sq_nonneg _, Real.sin_sq_le_one θ⟩

/-- `K(k) ≠ 0` on `jacobiModulusDomain`. -/
theorem p22R1_compEllIntKk_ne_zero {k : ℂ} (hk : k ∈ jacobiModulusDomain) : compEllIntKk k ≠ 0 := by
  intro h
  have := jacobiTauk_im_pos hk
  simp [jacobiTauk, h] at this

/-- Estimate under the stated parameter and domain assumptions: `jacobiModulusDomain = {k : ℂ | 0
< k.re} ∩ {k : ℂ | 1 - k ^ 2 ∈ slitPlane}`. -/
theorem p22R1_domain_eq :
    jacobiModulusDomain = {k : ℂ | 0 < k.re} ∩ {k : ℂ | 1 - k ^ 2 ∈ slitPlane} := by
  ext k
  simp only [jacobiModulusDomain, Set.mem_ofPred_eq, Set.mem_inter_iff, mem_slitPlane_iff]
  constructor
  · rintro ⟨h0, h1⟩
    refine ⟨h0, ?_⟩
    by_cases him : k.im = 0
    · left; have := h1 him; simp [pow_two, him]; nlinarith
    · right; simp [pow_two]; intro h
      have : k.re * k.im = 0 := by linarith
      rcases mul_eq_zero.mp this with h' | h'
      · linarith
      · exact him h'
  · rintro ⟨h0, h1⟩
    refine ⟨h0, fun him => ?_⟩
    rcases h1 with h1 | h1
    · simp [pow_two, him] at h1; nlinarith
    · simp [pow_two, him] at h1

/-- The indicated domain is open: `IsOpen jacobiModulusDomain`. -/
theorem p22R1_isOpen_domain : IsOpen jacobiModulusDomain := by
  rw [p22R1_domain_eq]
  exact (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_slitPlane.preimage (by fun_prop))

/-- Formula under the stated hypotheses: `(1 / 2 : ℂ) ∈ jacobiModulusDomain`. -/
lemma p22R1_half_mem : (1 / 2 : ℂ) ∈ jacobiModulusDomain := by
  refine ⟨by norm_num, fun _ => by norm_num⟩

/-- Formula under the stated hypotheses: `(x : ℂ) ∈ jacobiModulusDomain`. -/
theorem p22R1_ofReal_mem {x : ℝ} (h0 : 0 < x) (h1 : x < 1) : (x : ℂ) ∈ jacobiModulusDomain :=
  ⟨by simpa using h0, fun _ => by simpa using h1⟩

/-- The stated relation follows from the given hypotheses: `IsPreconnected jacobiModulusDomain`. -/
lemma p22R1_isPreconnected_domain : IsPreconnected jacobiModulusDomain := by
  refine (StarConvex.isPathConnected (a := (1 / 2 : ℂ)) ?_ p22R1_half_mem).isConnected.isPreconnected
  intro k hk a b ha hb hab
  obtain ⟨hk0, hk1⟩ := hk
  have hre : (a • (1 / 2 : ℂ) + b • k).re = a / 2 + b * k.re := by simp; ring
  have him : (a • (1 / 2 : ℂ) + b • k).im = b * k.im := by simp
  refine ⟨?_, fun h => ?_⟩
  · rw [hre]
    rcases hb.eq_or_lt with rfl | hb'
    · simp at hab; subst hab; norm_num
    · nlinarith
  · rw [hre]
    rw [him] at h
    rcases hb.eq_or_lt with rfl | hb'
    · simp at hab; subst hab; norm_num
    · have : k.im = 0 := by
        rcases mul_eq_zero.mp h with h | h
        · linarith
        · exact h
      have := hk1 this
      nlinarith

/-- Differentiability throughout the specified domain: `DifferentiableOn ℂ compEllIntKk
jacobiModulusDomain`. -/
lemma p22R1_differentiableOn_K : DifferentiableOn ℂ compEllIntKk jacobiModulusDomain :=
  p22R1_differentiableOn_integral (c := fun k => k ^ 2) p22R1_isOpen_domain (by fun_prop)
    fun k hk s hs0 hs1 => (p22R1_mem_slitPlane (p22R1_sq_of_mem_domain hk) hs0 hs1).2

/-- Differentiability throughout the specified domain: `DifferentiableOn ℂ compEllIntKpk
jacobiModulusDomain`. -/
lemma p22R1_differentiableOn_Kp : DifferentiableOn ℂ compEllIntKpk jacobiModulusDomain :=
  p22R1_differentiableOn_integral (c := fun k => 1 - k ^ 2) p22R1_isOpen_domain (by fun_prop)
    fun k hk s hs0 hs1 => (p22R1_mem_slitPlane (p22R1_sq_of_mem_domain hk) hs0 hs1).1

/-- Differentiability throughout the specified domain: `DifferentiableOn ℂ jacobiTauk
jacobiModulusDomain`. -/
lemma p22R1_differentiableOn_tau : DifferentiableOn ℂ jacobiTauk jacobiModulusDomain :=
  ((differentiableOn_const I).mul p22R1_differentiableOn_Kp).div p22R1_differentiableOn_K
    fun _ hk => p22R1_compEllIntKk_ne_zero hk

/-- Differentiability at the specified argument: `DifferentiableAt ℂ (fun τ => jacobiThetaThreeTau
0 τ) τ`. -/
theorem p22R1_differentiableAt_three {τ : ℂ} (hτ : 0 < τ.im) :
    DifferentiableAt ℂ (fun τ => jacobiThetaThreeTau 0 τ) τ :=
  differentiableAt_jacobiTheta₂_snd _ hτ

/-- Differentiability at the specified argument: `DifferentiableAt ℂ (fun τ => jacobiThetaFourTau
0 τ) τ`. -/
lemma p22R1_differentiableAt_four {τ : ℂ} (hτ : 0 < τ.im) :
    DifferentiableAt ℂ (fun τ => jacobiThetaFourTau 0 τ) τ :=
  differentiableAt_jacobiTheta₂_snd _ hτ

/-- Differentiability at the specified argument: `DifferentiableAt ℂ (fun τ => jacobiThetaTwoTau 0
τ) τ`. -/
theorem p22R1_differentiableAt_two {τ : ℂ} (hτ : 0 < τ.im) :
    DifferentiableAt ℂ (fun τ => jacobiThetaTwoTau 0 τ) τ := by
  have h : DifferentiableAt ℂ (fun σ => jacobiTheta₂ ((0 + π * σ / 2) / π) σ) τ := by
    have h1 := (hasFDerivAt_jacobiTheta₂ ((0 + π * τ / 2) / π) hτ).differentiableAt
    have h2 : DifferentiableAt ℂ (fun σ : ℂ => ((0 + π * σ / 2) / π, σ)) τ := by fun_prop
    exact h1.comp (f := fun σ : ℂ => ((0 + π * σ / 2) / π, σ)) τ h2
  exact (by fun_prop : DifferentiableAt ℂ (fun σ : ℂ => cexp (π * I * σ / 4 + I * 0)) τ).mul h

/-- Composition of a theta constant with `τ(k)` is holomorphic on the domain. -/
theorem p22R1_differentiableOn_comp {f : ℂ → ℂ}
    (hf : ∀ τ : ℂ, 0 < τ.im → DifferentiableAt ℂ f τ) :
    DifferentiableOn ℂ (fun k => f (jacobiTauk k)) jacobiModulusDomain := fun k hk =>
  ((hf _ (jacobiTauk_im_pos hk)).comp k
    (p22R1_differentiableOn_tau.differentiableAt
      (p22R1_isOpen_domain.mem_nhds hk))).differentiableWithinAt

/-- Identity theorem on the domain from agreement on `(0, 1)`. -/
theorem p22R1_eqOn_of_real {f g : ℂ → ℂ} (hf : DifferentiableOn ℂ f jacobiModulusDomain)
    (hg : DifferentiableOn ℂ g jacobiModulusDomain)
    (hreal : ∀ x : ℝ, 0 < x → x < 1 → f x = g x) : Set.EqOn f g jacobiModulusDomain := by
  refine (hf.analyticOnNhd p22R1_isOpen_domain).eqOn_of_preconnected_of_frequently_eq
    (hg.analyticOnNhd p22R1_isOpen_domain) p22R1_isPreconnected_domain p22R1_half_mem ?_
  have ht : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[≠] (1 / 2 : ℝ)) (𝓝[≠] (1 / 2 : ℂ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, eventually_nhdsWithin_of_forall fun x hx => ?_⟩
    · have := (Complex.continuous_ofReal.tendsto (1 / 2 : ℝ)).mono_left
        (nhdsWithin_le_nhds (s := {(1 / 2 : ℝ)}ᶜ))
      simpa using this
    · simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hx ⊢
      intro h; apply hx; have := congrArg Complex.re h; simpa using this
  refine ht.frequently (Eventually.frequently ?_)
  filter_upwards [nhdsWithin_le_nhds (Ioo_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1))] with x hx
  exact hreal x hx.1 hx.2

end p22R1Inversion

/-- **DLMF 22.2.2.** For `k ∈ jacobiModulusDomain` and `τ = iK'(k)/K(k)`:
`k = θ₂²(0|τ)/θ₃²(0|τ)`, `k' = θ₄²(0|τ)/θ₃²(0|τ)` with the principal `k' = √(1-k²)`, and
`K(k) = (π/2)θ₃²(0|τ)`. The sign of `k` requires `Re k > 0`; the right-hand sides depend on
`k²` only. -/
@[dlmf 22.2.E2 "domain: Re k > 0, k ∉ [1, ∞); fixes the sign of k and of k'"]
theorem jacobi_inversion_k {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    jacobiModulusTau (jacobiTauk k) = k ∧
      jacobiComodulusTau (jacobiTauk k) = jacobiComodulusk k ∧
      compEllIntKTau (jacobiTauk k) = compEllIntKk k := by
  have h3 := p22R1_differentiableOn_comp fun τ hτ => p22R1_differentiableAt_three hτ
  have h2 := p22R1_differentiableOn_comp fun τ hτ => p22R1_differentiableAt_two hτ
  have h4 := p22R1_differentiableOn_comp fun τ hτ => p22R1_differentiableAt_four hτ
  have h3ne : ∀ k ∈ jacobiModulusDomain, jacobiThetaThreeTau 0 (jacobiTauk k) ^ 2 ≠ 0 :=
    fun k hk => pow_ne_zero _ (je22a_thetaThree_zero_ne_zero (jacobiTauk_im_pos hk))
  refine ⟨?_, ?_, ?_⟩
  · refine p22R1_eqOn_of_real (f := fun k => jacobiModulusTau (jacobiTauk k)) (g := id)
      ((h2.pow 2).div (h3.pow 2) h3ne) differentiableOn_id (fun x hx0 hx1 => ?_) hk
    obtain ⟨t, -, ht, hm, -, -⟩ := p22R1_inversion_real hx0 hx1
    simp only [id, ht, hm]
  · refine p22R1_eqOn_of_real (f := fun k => jacobiComodulusTau (jacobiTauk k))
      (g := jacobiComodulusk) ((h4.pow 2).div (h3.pow 2) h3ne) ?_ (fun x hx0 hx1 => ?_) hk
    · intro k hk
      rw [p22R1_domain_eq] at hk
      exact ((by fun_prop : DifferentiableAt ℂ (fun k : ℂ => 1 - k ^ 2) k).cpow_const
        hk.2).differentiableWithinAt
    · obtain ⟨t, -, ht, -, hc, -⟩ := p22R1_inversion_real hx0 hx1
      simp only [ht, hc]
  · refine p22R1_eqOn_of_real (f := fun k => compEllIntKTau (jacobiTauk k))
      (g := compEllIntKk) ((differentiableOn_const _).mul (h3.pow 2))
      p22R1_differentiableOn_K (fun x hx0 hx1 => ?_) hk
    obtain ⟨t, -, ht, -, -, hK⟩ := p22R1_inversion_real hx0 hx1
    simp only [ht, hK]

/-- The modulus form is the lattice form at `τ = iK'/K`, given the third relation of
DLMF 22.2.2. -/
theorem jacobiPQk_eq_jacobiPQTau_of {k : ℂ} (hK : compEllIntKTau (jacobiTauk k) = compEllIntKk k)
    (p q : JacobiLetter) (z : ℂ) : jacobiPQk p q z k = jacobiPQTau p q z (jacobiTauk k) := by
  rw [jacobiPQk, jacobiPQTau, jacobiZetak, jacobiZetaTau, hK]

/-- The modulus form is the lattice form at `τ = iK'/K` on `jacobiModulusDomain`
(from the admitted DLMF 22.2.2). -/
theorem jacobiPQk_eq_jacobiPQTau {k : ℂ} (hk : k ∈ jacobiModulusDomain) (p q : JacobiLetter)
    (z : ℂ) : jacobiPQk p q z k = jacobiPQTau p q z (jacobiTauk k) :=
  jacobiPQk_eq_jacobiPQTau_of (jacobi_inversion_k hk).2.2 p q z

end DLMF.JacobiElliptic
end
end
