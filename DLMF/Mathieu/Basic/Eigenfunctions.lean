/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Mathieu.Basic.Properties

/-!
# Mathieu eigenfunctions: normalization and parity

The integer-order Mathieu functions `ce_n(z, q)`, `se_n(z, q)` for real `q` (DLMF §28.2(vi)):
their relation to the basic solutions, the sign conventions of the normalization, and parity
(Table 28.2.2).

## Main results

* `mathieuCe_div_mathieuCe_zero`, `mathieuSe_div_deriv_mathieuSe_zero`: `ce_n`, `se_n` as
  multiples of `w_I`, `w_II` (DLMF 28.2.38, 28.2.39).
* `mathieuCeZero_pos`, `mathieuSeDerivZero_pos`: the sign conventions `ce_n(0, q) > 0` and
  `se_n'(0, q) > 0`.
* `mathieuWI_add_pi_of_deriv_half_pi_eq_zero` and its three companions: (anti)periodicity of
  `w_I`, `w_II` from the vanishing of `w_I`, `w_II` or their derivatives at `π/2`.
* `mathieuCe_neg`, `mathieuSe_neg`: `ce_n` is even and `se_n` is odd (Table 28.2.2).

## Implementation notes

The periodicity of `ce_n`, `se_n`, the values at `q = 0`, the orthogonality relations and the
change of sign of `q` need the spectral theory and are in
`DLMF.Mathieu.Properties.Eigenfunctions`.
-/

@[expose] public noncomputable section

open Complex Set Filter

open scoped Topology Real

namespace DLMF.Mathieu

/-! ### Eigenfunctions (§28.2(vi)) -/

/-- `∫₀^{2π} |f|² > 0` for a continuous `f` that is nonzero just to the right of `0`. -/
theorem integral_norm_sq_pos_of_eventually_ne_zero {f : ℂ → ℂ} (hf : Continuous f)
    (h0 : ∀ᶠ x : ℝ in 𝓝[>] 0, f x ≠ 0) : 0 < ∫ x in (0 : ℝ)..2 * π, ‖f x‖ ^ 2 := by
  have hc : Continuous fun x : ℝ => ‖f x‖ ^ 2 := (hf.comp Complex.continuous_ofReal).norm.pow 2
  obtain ⟨u, hu, hsub0⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp h0
  have h2π : (0 : ℝ) < 2 * π := by positivity
  rw [intervalIntegral.integral_pos_iff_support_of_nonneg_ae'
    (Eventually.of_forall fun x => by positivity) (hc.intervalIntegrable _ _)]
  refine ⟨h2π, ?_⟩
  have hsub : Ioo 0 (min u (2 * π)) ⊆
      Function.support (fun x : ℝ => ‖f x‖ ^ 2) ∩ Ioc 0 (2 * π) := by
    intro x hx
    refine ⟨?_, hx.1, le_of_lt (lt_of_lt_of_le hx.2 (min_le_right _ _))⟩
    have : f x ≠ 0 := hsub0 ⟨hx.1, lt_of_lt_of_le hx.2 (min_le_left _ _)⟩
    simpa [Function.mem_support] using this
  refine lt_of_lt_of_le ?_ (MeasureTheory.measure_mono hsub)
  have hu' : (0 : ℝ) < u := hu
  rw [Real.volume_Ioo]; simp [hu', Real.pi_pos]

/-- `ce_n(0, q) > 0` (the sign convention of `mathieuCe`, DLMF §28.2(vi)). -/
theorem mathieuCeZero_pos (n : ℕ) (q : ℝ) : 0 < mathieuCeZero n q := by
  obtain ⟨h, h0, -⟩ := mathieuWI_spec (mathieuA n q) q
  have hev : ∀ᶠ x : ℝ in 𝓝 0, mathieuWI (mathieuA n q) q x ≠ 0 :=
    (h.differentiable.continuous.comp Complex.continuous_ofReal).continuousAt.eventually_ne
      (by simp [h0])
  exact Real.sqrt_pos.mpr (div_pos Real.pi_pos
    (integral_norm_sq_pos_of_eventually_ne_zero h.differentiable.continuous
        (nhdsWithin_le_nhds hev)))

/-- `se_n'(0, q) > 0` (the sign convention of `mathieuSe`, DLMF §28.2(vi)). -/
theorem mathieuSeDerivZero_pos (n : ℕ) (q : ℝ) : 0 < mathieuSeDerivZero n q := by
  obtain ⟨h, h0, h1⟩ := mathieuWII_spec (mathieuB n q) q
  have hd : HasDerivAt (fun x : ℝ => mathieuWII (mathieuB n q) q x) 1 0 := by
    have := (h.differentiable _).hasDerivAt.comp_ofReal (z := 0)
    simpa [h1] using this
  have hev := hd.eventually_ne (c := 0) one_ne_zero
  have hev' : ∀ᶠ x : ℝ in 𝓝[>] 0, mathieuWII (mathieuB n q) q x ≠ 0 := by
    exact nhdsWithin_mono (0 : ℝ) (fun x (hx : x ∈ Ioi (0 : ℝ)) => ne_of_gt hx) hev
  exact Real.sqrt_pos.mpr (div_pos Real.pi_pos
    (integral_norm_sq_pos_of_eventually_ne_zero h.differentiable.continuous hev'))

/-- **DLMF 28.2.38**: `ce_n(z, q) / ce_n(0, q) = w_I(z; a_n(q), q)`. -/
@[dlmf 28.2.E38]
theorem mathieuCe_div_mathieuCe_zero (n : ℕ) (z : ℂ) (q : ℝ) :
    mathieuCe n z q / mathieuCe n 0 q = mathieuWI (mathieuA n q) q z := by
  rw [mathieuCe_zero, mathieuCe]
  have : (mathieuCeZero n q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (mathieuCeZero_pos n q).ne'
  field_simp

/-- **DLMF 28.2.39**: `se_n(z, q) / se_n'(0, q) = w_II(z; b_n(q), q)`. -/
@[dlmf 28.2.E39]
theorem mathieuSe_div_deriv_mathieuSe_zero (n : ℕ) (z : ℂ) (q : ℝ) :
    mathieuSe n z q / deriv (fun z => mathieuSe n z q) 0 = mathieuWII (mathieuB n q) q z := by
  rw [deriv_mathieuSe_zero, mathieuSe]
  have : (mathieuSeDerivZero n q : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (mathieuSeDerivZero_pos n q).ne'
  field_simp

/-! ### Periodicity and parity of the eigenfunctions (Table 28.2.2) -/

section Periodicity

variable {a q : ℂ}

/-- If `w_I'(π/2) = 0` then `w_I` has period `π`. -/
theorem mathieuWI_add_pi_of_deriv_half_pi_eq_zero (h : deriv (mathieuWI a q) (π / 2) = 0) (z : ℂ) :
    mathieuWI a q (z + π) = mathieuWI a q z := by
  have hW := mathieuWI_wronskian a q (π / 2)
  have e := mathieuWI_pi_sub a q (-z)
  rw [h] at e hW
  rw [show z + π = π - -z by ring, e, mathieuWI_neg]
  linear_combination mathieuWI a q z * hW

/-- If `w_I(π/2) = 0` then `w_I` has antiperiod `π`. -/
theorem mathieuWI_add_pi_of_half_pi_eq_zero (h : mathieuWI a q (π / 2) = 0) (z : ℂ) :
    mathieuWI a q (z + π) = -mathieuWI a q z := by
  have hW := mathieuWI_wronskian a q (π / 2)
  have e := mathieuWI_pi_sub a q (-z)
  rw [h] at e hW
  rw [show z + π = π - -z by ring, e, mathieuWI_neg]
  linear_combination -(mathieuWI a q z) * hW

/-- If `w_II'(π/2) = 0` then `w_II` has antiperiod `π`. -/
theorem mathieuWII_add_pi_of_deriv_half_pi_eq_zero (h : deriv (mathieuWII a q) (π / 2) = 0)
    (z : ℂ) :
    mathieuWII a q (z + π) = -mathieuWII a q z := by
  have hW := mathieuWI_wronskian a q (π / 2)
  have e := mathieuWII_pi_sub a q (-z)
  rw [h] at e hW
  rw [show z + π = π - -z by ring, e, mathieuWII_neg]
  linear_combination -(mathieuWII a q z) * hW

/-- If `w_II(π/2) = 0` then `w_II` has period `π`. -/
theorem mathieuWII_add_pi_of_half_pi_eq_zero (h : mathieuWII a q (π / 2) = 0) (z : ℂ) :
    mathieuWII a q (z + π) = mathieuWII a q z := by
  have hW := mathieuWI_wronskian a q (π / 2)
  have e := mathieuWII_pi_sub a q (-z)
  rw [h] at e hW
  rw [show z + π = π - -z by ring, e, mathieuWII_neg]
  linear_combination mathieuWII a q z * hW

end Periodicity

/-- **Table 28.2.2**: `ce_n(z, q)` is even. -/
@[dlmf 28.2.T2]
theorem mathieuCe_neg (n : ℕ) (z : ℂ) (q : ℝ) : mathieuCe n (-z) q = mathieuCe n z q := by
  simp [mathieuCe, mathieuWI_neg]

/-- **Table 28.2.2**: `se_n(z, q)` is odd. -/
@[dlmf 28.2.T2]
theorem mathieuSe_neg (n : ℕ) (z : ℂ) (q : ℝ) : mathieuSe n (-z) q = -mathieuSe n z q := by
  simp [mathieuSe, mathieuWII_neg]

end DLMF.Mathieu
