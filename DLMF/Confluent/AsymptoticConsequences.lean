/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Confluent.TricomiRotated

/-!
# Consequences of the asymptotic expansions (DLMF 13.2.6, 13.2.23, 13.7.2, 13.14.20–21)

The limits 13.2.6 and 13.2.23 are the leading terms of the real expansions 13.7.3 and 13.7.1;
the Whittaker limits 13.14.20–21 follow from them. The two-sided expansion 13.7.2 of `𝐌` in the
upper sector `δ ≤ ph z ≤ π - δ` follows from the connection formula 13.2.41: there `z` and `-z`
lie in the rotated sectors of `DLMF.Confluent.TricomiRotated` with rotation angles
`∓(π/2 - δ/2)`, where Tricomi's expansion holds.

These statements were moved unchanged from `BasicProperties`, `Asymptotics` and `Whittaker`,
which precede the expansions in the import order. Hypotheses that the proofs do not need are
kept with underscore names.
-/

@[expose] public section

open Complex Filter Set Asymptotics
open scoped Real Topology Nat
open DLMF.Hypergeometric

noncomputable section

namespace DLMF.Confluent

/-- The complex reciprocal `1/x` of a real `x` tends to `0` as `x → +∞`. -/
theorem tendsto_ofReal_recip_atTop : Tendsto (fun x : ℝ => ((x : ℂ))⁻¹) atTop (𝓝 0) := by
  have := (tendsto_inv_atTop_zero (𝕜 := ℝ)).ofReal
  simpa using this

/-- The map `(fun x : ℝ => kummerU a b x * (x : ℂ) ^ a)` tends to `(𝓝 1)` along `atTop`. -/
@[dlmf 13.2.E6]
theorem tendsto_kummerU_mul_cpow_atTop (a b : ℂ) :
    Tendsto (fun x : ℝ => kummerU a b x * (x : ℂ) ^ a) atTop (𝓝 1) := by
  have h := ((hasAsymptoticExpansion_kummerU a b).mul_left
    (fun x : ℝ => (x : ℂ) ^ a)).congr_scale
    (ψ := fun (n : ℕ) (x : ℝ) => ((x : ℂ) ^ n)⁻¹) fun n => by
      filter_upwards [eventually_gt_atTop 0] with x hx
      have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
      rw [← cpow_add _ _ hx0, show a + -((n : ℂ) + a) = -(n : ℂ) by ring, cpow_neg, cpow_natCast]
  have h1 := h 1
  simp only [Finset.range_one, Finset.sum_singleton, pow_zero, inv_one,
    tricomiCoeff_zero, pow_one, smul_eq_mul] at h1
  have := (h1.trans_tendsto tendsto_ofReal_recip_atTop).add_const 1
  simp only [zero_add] at this
  exact this.congr fun x => by ring

/-- The map `(fun x : ℝ => regularizedHGFun {a} {b} x * Gamma a / (exp x * (x : ℂ) ^ (a - b)))`
tends to `(𝓝 1)` along `atTop`. -/
@[dlmf 13.2.E23]
theorem tendsto_regularizedHGFun_mul_exp_neg_atTop (a b : ℂ) (ha : ∀ k : ℕ, a ≠ -k) :
    Tendsto (fun x : ℝ => regularizedHGFun {a} {b} x * Gamma a /
      (exp x * (x : ℂ) ^ (a - b))) atTop (𝓝 1) := by
  have hG : Gamma a ≠ 0 := Gamma_ne_zero ha
  have h1 := hasAsymptoticExpansion_regularizedConfluent a b 1
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, sub_zero, kummerCoeff_zero,
    smul_eq_mul, Nat.cast_one] at h1
  have hO := h1.mul (isBigO_refl (fun x : ℝ => Gamma a / (exp (x : ℂ) * (x : ℂ) ^ (a - b))) atTop)
  have hT : Tendsto (fun x : ℝ => exp (x : ℂ) * (x : ℂ) ^ (a - b - 1) *
      (Gamma a / (exp (x : ℂ) * (x : ℂ) ^ (a - b)))) atTop (𝓝 0) := by
    have : Tendsto (fun x : ℝ => Gamma a * ((x : ℂ))⁻¹) atTop (𝓝 0) := by
      simpa using tendsto_ofReal_recip_atTop.const_mul (Gamma a)
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
    have hc : (x : ℂ) ^ (a - b) ≠ 0 := by rw [cpow_def_of_ne_zero hx0]; exact exp_ne_zero _
    rw [cpow_sub _ _ hx0, cpow_one]
    field_simp
  have := (hO.trans_tendsto hT).add_const 1
  simp only [zero_add] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have hc : (x : ℂ) ^ (a - b) ≠ 0 := by rw [cpow_def_of_ne_zero hx0]; exact exp_ne_zero _
  have he := exp_ne_zero (x : ℂ)
  field_simp
  ring

/-- The map `(fun x : ℝ => whittakerM κ μ x * Gamma (1 / 2 + μ - κ) / (Gamma (1 + 2 * μ) * exp (x
/ 2) * (x : ℂ) ^ (-κ)))` tends to `(𝓝 1)` along `atTop`. -/
@[dlmf 13.14.E20]
theorem tendsto_whittakerM_atTop {κ μ : ℂ} (hμ : ∀ k : ℕ, 1 + 2 * μ ≠ -k)
    (hκ : ∀ k : ℕ, 1 / 2 + μ - κ ≠ -k) :
    Tendsto (fun x : ℝ => whittakerM κ μ x * Gamma (1 / 2 + μ - κ) /
      (Gamma (1 + 2 * μ) * exp (x / 2) * (x : ℂ) ^ (-κ))) atTop (𝓝 1) := by
  have h := tendsto_regularizedHGFun_mul_exp_neg_atTop (1 / 2 + μ - κ) (1 + 2 * μ) hκ
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have hGb : Gamma (1 + 2 * μ) ≠ 0 := Gamma_ne_zero hμ
  rw [whittakerM, kummerM_eq_mul_regularizedHGFun hμ,
    show μ - κ + 1 / 2 = 1 / 2 + μ - κ by ring]
  have hpow : (x : ℂ) ^ (1 / 2 + μ - κ - (1 + 2 * μ)) * (x : ℂ) ^ (μ + 1 / 2) = (x : ℂ) ^ (-κ) := by
    rw [← cpow_add _ _ hx0]; ring_nf
  have hc : (x : ℂ) ^ (-κ) ≠ 0 := by rw [cpow_def_of_ne_zero hx0]; exact exp_ne_zero _
  have hc2 : (x : ℂ) ^ (1 / 2 + μ - κ - (1 + 2 * μ)) ≠ 0 := by
    rw [cpow_def_of_ne_zero hx0]; exact exp_ne_zero _
  have he : exp (x : ℂ) = exp ((x : ℂ) / 2) ^ 2 := by rw [← exp_nat_mul]; ring_nf
  have he' : exp (-(x : ℂ) / 2) = (exp ((x : ℂ) / 2))⁻¹ := by rw [← exp_neg]; ring_nf
  have hE := exp_ne_zero ((x : ℂ) / 2)
  have hQ : (x : ℂ) ^ (μ + 1 / 2) ≠ 0 := by rw [cpow_def_of_ne_zero hx0]; exact exp_ne_zero _
  rw [he, he', ← hpow]
  generalize regularizedHGFun {1 / 2 + μ - κ} {1 + 2 * μ} (x : ℂ) = R
  generalize (x : ℂ) ^ (1 / 2 + μ - κ - (1 + 2 * μ)) = P at *
  generalize (x : ℂ) ^ (μ + 1 / 2) = Q at *
  generalize exp ((x : ℂ) / 2) = E at *
  generalize Gamma (1 / 2 + μ - κ) = G
  generalize Gamma (1 + 2 * μ) = G' at *
  field_simp

/-- The map `(fun x : ℝ => whittakerW κ μ x / (exp (-x / 2) * (x : ℂ) ^ κ))` tends to `(𝓝 1)`
along `atTop`. -/
@[dlmf 13.14.E21]
theorem tendsto_whittakerW_atTop (κ μ : ℂ) :
    Tendsto (fun x : ℝ => whittakerW κ μ x / (exp (-x / 2) * (x : ℂ) ^ κ)) atTop (𝓝 1) := by
  have h := tendsto_kummerU_mul_cpow_atTop (1 / 2 + μ - κ) (1 + 2 * μ)
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have hc : (x : ℂ) ^ κ ≠ 0 := by rw [cpow_def_of_ne_zero hx0]; exact exp_ne_zero _
  have hE := exp_ne_zero (-(x : ℂ) / 2)
  rw [whittakerW, show (x : ℂ) ^ (1 / 2 + μ) = (x : ℂ) ^ (1 / 2 + μ - κ) * (x : ℂ) ^ κ by
    rw [← cpow_add _ _ hx0]; ring_nf]
  generalize kummerU (1 / 2 + μ - κ) (1 + 2 * μ) (x : ℂ) = U
  generalize (x : ℂ) ^ (1 / 2 + μ - κ) = P
  generalize (x : ℂ) ^ κ = Q at *
  generalize exp (-(x : ℂ) / 2) = E at *
  field_simp

/-- The closed upper sector `δ ≤ ph z ≤ π - δ` at infinity, the filter of DLMF 13.7.2. -/
def upperSectorAtTop (δ : ℝ) : Filter ℂ :=
  Filter.comap (fun z : ℂ => ‖z‖) atTop ⊓ Filter.principal {z : ℂ | δ ≤ z.arg ∧ z.arg ≤ π - δ}

/-- If `|θ| ≤ π/2 - δ/2` with `0 < δ < π/2`, then `sin(δ/2) ≤ cos θ`. -/
theorem sin_le_cos_of_abs_le {δ θ : ℝ} (hδ : 0 < δ) (hδπ : δ < π / 2) (hθ : |θ| ≤ π / 2 - δ / 2) :
    Real.sin (δ / 2) ≤ Real.cos θ := by
  rw [← Real.cos_abs θ, ← Real.cos_pi_div_two_sub]
  exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg θ) (by linarith) hθ

/-- Multiplication by `σ = ±1` maps the upper sector filter into a rotated sector filter of
half-opening `sin(δ/2)` about the direction `-σ(π/2 - δ/2)`. -/
theorem tendsto_upperSectorAtTop_rot {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π / 2) (σ : ℝ)
    (hσ : σ = 1 ∨ σ = -1) :
    Tendsto (fun z : ℂ => (σ : ℂ) * z) (upperSectorAtTop δ)
      (rotSectorAtTop (Real.sin (δ / 2)) (-σ * (π / 2 - δ / 2))) := by
  refine tendsto_comap_iff.mpr (tendsto_inf.mpr ⟨tendsto_comap_iff.mpr ?_, ?_⟩)
  · have hn : ∀ z : ℂ, ‖(σ : ℂ) * z * exp ((-σ * (π / 2 - δ / 2) : ℝ) * I)‖ = ‖z‖ := fun z => by
      rw [norm_mul, norm_exp_ofReal_mul_I, mul_one, norm_mul, norm_real]
      rcases hσ with rfl | rfl <;> simp
    simp only [Function.comp_def, hn]
    exact tendsto_comap.mono_left inf_le_left
  · refine tendsto_principal.mpr ?_
    rw [upperSectorAtTop, eventually_inf_principal]
    refine Eventually.of_forall fun z hz => ?_
    simp only [Function.comp_apply, Set.mem_ofPred_eq]
    obtain ⟨h1, h2⟩ := hz
    have hn : ‖(σ : ℂ) * z‖ = ‖z‖ := by
      rw [norm_mul, norm_real]; rcases hσ with rfl | rfl <;> simp
    rw [norm_mul, norm_exp_ofReal_mul_I, mul_one, hn, mul_assoc, re_ofReal_mul, re_mul_exp_mul_I]
    rcases hσ with rfl | rfl
    · have := sin_le_cos_of_abs_le (θ := arg z + -1 * (π / 2 - δ / 2)) hδ hδπ
        (by rw [abs_le]; constructor <;> linarith)
      nlinarith [norm_nonneg z]
    · have hc : Real.cos (arg z + -(-1) * (π / 2 - δ / 2)) =
          -Real.cos (arg z + -(-1) * (π / 2 - δ / 2) - π) := by
        rw [Real.cos_sub_pi]; ring
      have := sin_le_cos_of_abs_le (θ := arg z + -(-1) * (π / 2 - δ / 2) - π) hδ hδπ
        (by rw [abs_le]; constructor <;> linarith)
      rw [hc]
      nlinarith [norm_nonneg z]

/-- Two-term-family Poincaré expansion in closed upper-half-plane sectors.
The filter sends the norm to infinity; the bound contains both the exponential
and algebraic remainder scales. It is not a local boundedness assertion. -/
@[dlmf 13.7.E2]
theorem regularizedHGFun_poincare_sector (a b : ℂ) (n : ℕ) {δ : ℝ}
    (hδ : 0 < δ) (hδπ : δ < π / 2)
    (_ha : ∀ k : ℕ, a ≠ -k) (_hba : ∀ k : ℕ, b - a ≠ -k) :
    Asymptotics.IsBigO
      (Filter.comap (fun z : ℂ => ‖z‖) atTop ⊓
        Filter.principal {z : ℂ | δ ≤ z.arg ∧ z.arg ≤ π - δ})
      (fun z => regularizedHGFun {a} {b} z -
        (exp z * z ^ (a - b) / Gamma a *
          ∑ s ∈ Finset.range n, poch (1 - a) s * poch (b - a) s / s.factorial *
            z ^ (-(s : ℂ)) +
         exp (π * I * a) * z ^ (-a) / Gamma (b - a) *
          ∑ s ∈ Finset.range n, poch a s * poch (a - b + 1) s / s.factorial *
            (-z) ^ (-(s : ℂ))))
      (fun z => ‖exp z * z ^ (a - b - n)‖ + ‖z ^ (-a - n)‖) := by
  change IsBigO (upperSectorAtTop δ) _ _
  have hδ' : 0 < Real.sin (δ / 2) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hα1 : |-(1 : ℝ) * (π / 2 - δ / 2)| < π / 2 := by
    rw [abs_lt]; constructor <;> linarith
  have hα2 : |-(-1 : ℝ) * (π / 2 - δ / 2)| < π / 2 := by
    rw [abs_lt]; constructor <;> linarith
  have hU1 := (hasAsymptoticExpansion_kummerU_rotSector a b hδ' hα1).comp_tendsto
    (tendsto_upperSectorAtTop_rot hδ hδπ 1 (Or.inl rfl))
  have hU2 := (hasAsymptoticExpansion_kummerU_rotSector (b - a) b hδ' hα2).comp_tendsto
    (tendsto_upperSectorAtTop_rot hδ hδπ (-1) (Or.inr rfl))
  simp only [ofReal_one, one_mul, ofReal_neg, neg_one_mul, Function.comp_def] at hU1 hU2
  -- eventually: `z ≠ 0` and `0 < arg z`
  have hev : ∀ᶠ z in upperSectorAtTop δ, z ∈ slitPlane ∧ 0 < arg z := by
    rw [upperSectorAtTop, eventually_inf_principal]
    filter_upwards [tendsto_comap.eventually (eventually_ge_atTop (1 : ℝ))] with z hz hzs
    have hz0 : z ≠ 0 := by rintro rfl; norm_num at hz
    refine ⟨mem_slitPlane_iff_arg.mpr ⟨by linarith [hzs.2], hz0⟩, by linarith [hzs.1]⟩
  -- the two remainders
  set c1 := exp (-(-1) * a * π * I) / Gamma (b - a)
  set c2 := exp ((-1) * (b - a) * π * I) / Gamma a
  set S1 := fun z : ℂ => ∑ s ∈ Finset.range n, z ^ (-((s : ℂ) + a)) • tricomiCoeff a b s
  set S2 := fun z : ℂ => ∑ s ∈ Finset.range n,
    (-z) ^ (-((s : ℂ) + (b - a))) • tricomiCoeff (b - a) b s
  have h1 : (fun z => kummerU a b z - S1 z) =O[upperSectorAtTop δ]
      fun z => ‖exp z * z ^ (a - b - n)‖ + ‖z ^ (-a - n)‖ := by
    refine (hU1 n).trans (IsBigO.of_bound 1 (Eventually.of_forall fun z => ?_))
    show ‖z ^ (-((n : ℂ) + a))‖ ≤ 1 * ‖‖exp z * z ^ (a - b - n)‖ + ‖z ^ (-a - n)‖‖
    rw [one_mul, Real.norm_of_nonneg (by positivity), show -((n : ℂ) + a) = -a - n by ring]
    exact le_add_of_nonneg_left (norm_nonneg _)
  have h2 : (fun z => exp z * (kummerU (b - a) b (-z) - S2 z)) =O[upperSectorAtTop δ]
      fun z => ‖exp z * z ^ (a - b - n)‖ + ‖z ^ (-a - n)‖ := by
    have hm := (isBigO_refl (fun z : ℂ => exp z) (upperSectorAtTop δ)).mul (hU2 n)
    refine hm.trans ?_
    refine IsBigO.of_bound ‖exp (π * I * ((n : ℂ) + (b - a)))‖ ?_
    filter_upwards [hev] with z hz
    have hc := neg_cpow_of_arg (slitPlane_ne_zero hz.1) (-1) (Or.inr rfl)
      (by simp; linarith [hz.2]) (by simp; linarith [arg_le_pi z]) (-((n : ℂ) + (b - a)))
    rw [hc, Real.norm_of_nonneg (by positivity), show -((n : ℂ) + (b - a)) = a - b - n by ring,
      show (-1 : ℂ) * π * I * (a - b - n) = π * I * ((n : ℂ) + (b - a)) by ring]
    calc ‖exp z * (z ^ (a - b - n) * exp (π * I * ((n : ℂ) + (b - a))))‖
        = ‖exp (π * I * ((n : ℂ) + (b - a)))‖ * ‖exp z * z ^ (a - b - n)‖ := by
          rw [norm_mul, norm_mul, norm_mul]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (norm_nonneg _))
          (norm_nonneg _)
  refine ((h1.const_mul_left c1).add (h2.const_mul_left c2)).congr' ?_ EventuallyEq.rfl
  filter_upwards [hev] with z hz
  have hz0 := slitPlane_ne_zero hz.1
  have hneg : ∀ w : ℂ, (-z) ^ w = z ^ w * exp ((-1) * π * I * w) := fun w =>
    neg_cpow_of_arg hz0 (-1) (Or.inr rfl) (by simp; linarith [hz.2])
      (by simp; linarith [arg_le_pi z]) w
  have hpow : ∀ s : ℕ, exp (π * I * s) = (-1) ^ s := fun s => by
    rw [show π * I * (s : ℂ) = s * (π * I) by ring, exp_nat_mul, exp_pi_mul_I]
  have hconn := regularizedHGFun_eq_kummerU_connection a b hz.1 false (by simpa using hz.2)
  simp only [Bool.false_eq_true, ↓reduceIte] at hconn
  rw [show exp ((-1 : ℂ) * π * I) * z = -z by
    rw [show (-1 : ℂ) * π * I = -(π * I) by ring, exp_neg, exp_pi_mul_I]; ring] at hconn
  have hS1 : c1 * S1 z = exp (π * I * a) * z ^ (-a) / Gamma (b - a) *
      ∑ s ∈ Finset.range n, poch a s * poch (a - b + 1) s / s.factorial * (-z) ^ (-(s : ℂ)) := by
    simp only [S1, c1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [hneg, show (-1 : ℂ) * π * I * -(s : ℂ) = π * I * s by ring, hpow, smul_eq_mul,
      tricomiCoeff, neg_add, cpow_add _ _ hz0,
      show -(-1 : ℂ) * a * π * I = π * I * a by ring]
    ring
  have hS2 : c2 * (exp z * S2 z) = exp z * z ^ (a - b) / Gamma a *
      ∑ s ∈ Finset.range n, poch (1 - a) s * poch (b - a) s / s.factorial * z ^ (-(s : ℂ)) := by
    simp only [S2, c2, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    have he : exp ((-1) * (b - a) * π * I) * exp ((-1) * π * I * -((s : ℂ) + (b - a))) =
        (-1) ^ s := by
      rw [← exp_add, ← hpow]; congr 1; ring
    have hsq : ((-1 : ℂ) ^ s) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
    have hzc : z ^ (-((s : ℂ) + (b - a))) = z ^ (-(s : ℂ)) * z ^ (a - b) := by
      rw [← cpow_add _ _ hz0]; ring_nf
    rw [hneg, smul_eq_mul, tricomiCoeff, show b - a - b + 1 = 1 - a by ring, hzc]
    linear_combination (exp z * z ^ (-(s : ℂ)) * z ^ (a - b) * (-1) ^ s * poch (b - a) s *
      poch (1 - a) s / s.factorial / Gamma a) * he +
      (exp z * z ^ (-(s : ℂ)) * z ^ (a - b) * poch (b - a) s * poch (1 - a) s / s.factorial /
        Gamma a) * hsq
  rw [hconn, ← hS1, ← hS2]
  simp only [S1, S2, c1, c2]
  ring

end DLMF.Confluent
