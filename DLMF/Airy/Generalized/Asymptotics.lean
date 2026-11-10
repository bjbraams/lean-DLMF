/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Airy.Generalized.Properties
public import DLMF.Bessel.Asymptotics.RightHalfPlane

/-!
# Asymptotics of generalized Airy functions (DLMF §9.13(i))

The generalized Airy expansions 9.13.9–9.13.12 and the recession of Olver's rotated
solutions in 9.13.18. The uniform modified-Bessel expansion and the exact sum-and-difference
representations establish recession in every closed subsector of `|arg z| < π/(n+2)`.
-/

@[expose] public noncomputable section
open Complex Filter Set Asymptotics
open scoped Real Topology
namespace DLMF.Airy

/-- The generalized Airy argument tends uniformly to infinity with its original variable. -/
theorem tendsto_norm_generalizedAiryZeta (n : ℕ) (α : ℝ) :
    Tendsto (fun z : ℂ => ‖generalizedAiryZeta n z‖) (airySector α) atTop := by
  have hn : 0 < (n : ℝ) + 2 := by positivity
  have ht := ((tendsto_rpow_atTop (y := ((n : ℝ) + 2) / 2) (by positivity)).comp
    (tendsto_comap.mono_left (show airySector α ≤ comap (fun z : ℂ => ‖z‖) atTop from
      inf_le_left))).const_mul_atTop (show (0 : ℝ) < 2 / ((n : ℝ) + 2) by positivity)
  refine ht.congr fun z => ?_
  have he : generalizedAiryZeta n z = ((2 / ((n : ℝ) + 2) : ℝ) : ℂ) *
      z ^ ((((n : ℝ) + 2) / 2 : ℝ) : ℂ) := by
    simp only [generalizedAiryZeta]; push_cast; rfl
  rw [he, norm_mul, norm_real, Real.norm_of_nonneg (by positivity), norm_cpow_real]
  rfl

/-- The generalized Airy change of variable maps every closed recessive subsector to a closed
right-half-plane sector. -/
theorem tendsto_generalizedAiryZeta_sector (n : ℕ) {δ : ℝ} (hδ : 0 < δ)
    (hδ' : δ < generalizedAiryOrder n * π) :
    Tendsto (generalizedAiryZeta n) (airySector (generalizedAiryOrder n * π - δ))
      (sectorAtTop (Real.cos (((n : ℝ) + 2) / 2 * (generalizedAiryOrder n * π - δ)))) := by
  set α := generalizedAiryOrder n * π - δ
  set q := ((n : ℝ) + 2) / 2
  set β := q * α
  have hn : 0 < (n : ℝ) + 2 := by positivity
  have hq : 0 < q := by dsimp [q]; positivity
  have hα : 0 < α := sub_pos.mpr hδ'
  have hβ : β < π / 2 := by
    dsimp [β, α, q, generalizedAiryOrder]
    have he : ((n : ℝ) + 2) / 2 * (1 / ((n : ℝ) + 2) * π) = π / 2 := by
      field_simp
    nlinarith
  refine tendsto_inf.mpr ⟨tendsto_comap_iff.mpr (tendsto_norm_generalizedAiryZeta n α), ?_⟩
  apply tendsto_principal.mpr
  have hmem : ∀ᶠ z in airySector α, z ≠ 0 ∧ |arg z| ≤ α :=
    mem_inf_of_right (mem_principal_self _)
  filter_upwards [hmem] with z hz
  set L : ℂ := (q : ℂ) * log z
  have hLim : L.im = q * arg z := by
    change ((q : ℂ) * log z).im = q * arg z
    rw [im_ofReal_mul, log_im]
  have hL : |L.im| ≤ β := by
    rw [hLim, abs_mul, abs_of_pos hq]
    exact mul_le_mul_of_nonneg_left hz.2 hq.le
  have hcos : Real.cos β ≤ Real.cos L.im := by
    rw [← Real.cos_abs L.im]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_pos]) hL
  have he : generalizedAiryZeta n z = ((2 / ((n : ℝ) + 2) : ℝ) : ℂ) * exp L := by
    rw [generalizedAiryZeta, cpow_def_of_ne_zero hz.1]
    dsimp only [L, q]
    push_cast
    ring
  change Real.cos β * ‖generalizedAiryZeta n z‖ ≤ (generalizedAiryZeta n z).re
  rw [he, norm_mul, norm_real, Real.norm_of_nonneg (by positivity), norm_exp]
  simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero, exp_re]
  nlinarith [mul_le_mul_of_nonneg_left hcos
    (show 0 ≤ 2 / ((n : ℝ) + 2) * Real.exp L.re by positivity)]

/-- The generalized Airy pair is the difference and sum of the modified Bessel functions
of orders `±p` in the recessive sector. -/
theorem generalizedAiry_besselI_sector (n : ℕ) {z : ℂ} (hz : z ≠ 0)
    (harg : |arg z| < π / ((n : ℝ) + 2)) :
    generalizedAiryA n z = (generalizedAiryOrder n : ℂ) * z ^ (1 / 2 : ℂ) *
      (DLMF.Bessel.besselI (-(generalizedAiryOrder n : ℂ)) (generalizedAiryZeta n z) -
        DLMF.Bessel.besselI (generalizedAiryOrder n) (generalizedAiryZeta n z)) ∧
    generalizedAiryB n z = (generalizedAiryOrder n : ℂ) ^ (1 / 2 : ℂ) * z ^ (1 / 2 : ℂ) *
      (DLMF.Bessel.besselI (-(generalizedAiryOrder n : ℂ)) (generalizedAiryZeta n z) +
        DLMF.Bessel.besselI (generalizedAiryOrder n) (generalizedAiryZeta n z)) := by
  set p : ℂ := (generalizedAiryOrder n : ℂ)
  have hp : p ≠ 0 := generalizedAiryOrder_ne_zero n
  have hF := cpow_half_mul_besselI_neg_generalizedAiryZeta n hz harg
  have hG := cpow_half_mul_besselI_generalizedAiryZeta n hz harg
  have hFp : p * p ^ (-p) = p ^ (1 - p) := by
    conv_lhs => lhs; rw [← cpow_one p]
    rw [← cpow_add _ _ hp]
    congr 1
  have hGp : p * p ^ p = p ^ (p + 1) := by
    conv_lhs => lhs; rw [← cpow_one p]
    rw [← cpow_add _ _ hp]
    congr 1; ring
  have hpp : p ^ (-1 / 2 : ℂ) * p = p ^ (1 / 2 : ℂ) := by
    conv_lhs => rhs; rw [← cpow_one p]
    rw [← cpow_add _ _ hp]
    congr 1; ring
  constructor
  · simp only [generalizedAiryA]
    change p ^ (1 - p) * _ - p ^ (p + 1) * _ = _
    rw [← hFp, ← hGp]
    linear_combination -p * hF + p * hG
  · simp only [generalizedAiryB]
    change p ^ (-1 / 2 : ℂ) * (p ^ (1 - p) * _ + p ^ (p + 1) * _) = _
    rw [← hFp, ← hGp]
    rw [← hpp]
    linear_combination -(p ^ (-1 / 2 : ℂ) * p) * hF - (p ^ (-1 / 2 : ℂ) * p) * hG

/-- The generalized Airy solution `A_n` is recessive relative to `B_n` in every closed
subsector of `|arg z| < π/(n+2)`. -/
theorem generalizedAiryA_isLittleO_generalizedAiryB {n : ℕ} (hn : 1 ≤ n)
    {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < generalizedAiryOrder n * π) :
    (generalizedAiryA n) =o[airySector (generalizedAiryOrder n * π - δ)]
      (generalizedAiryB n) := by
  set α := generalizedAiryOrder n * π - δ
  set β := ((n : ℝ) + 2) / 2 * α
  set ζ := generalizedAiryZeta n
  set p : ℂ := (generalizedAiryOrder n : ℂ)
  set H : ℂ → ℂ := fun z => exp (ζ z) * (2 * ζ z) ^ (-1 / 2 : ℂ) / (Real.sqrt π : ℂ)
  have hp : p ≠ 0 := generalizedAiryOrder_ne_zero n
  have hpbound : generalizedAiryOrder n < 1 / 2 := by
    dsimp only [generalizedAiryOrder]
    have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
    rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hβ : β < π / 2 := by
    dsimp only [β, α, generalizedAiryOrder]
    have hnpos : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    have he : ((n : ℝ) + 2) / 2 * (1 / ((n : ℝ) + 2) * π) = π / 2 := by field_simp
    nlinarith
  have hβ0 : 0 < β := mul_pos (by positivity) (sub_pos.mpr hδ')
  have hc : 0 < Real.cos β := Real.cos_pos_of_mem_Ioo ⟨by linarith, hβ⟩
  have hζ := tendsto_generalizedAiryZeta_sector n hδ hδ'
  have hM := (DLMF.Bessel.besselI_isEquivalent_sector (ν := -p) (by
    simpa [p] using (show -1 / 2 < -generalizedAiryOrder n by linarith)) hc).comp_tendsto hζ
  have hP := (DLMF.Bessel.besselI_isEquivalent_sector (ν := p) (by
    change -1 / 2 < generalizedAiryOrder n
    linarith [generalizedAiryOrder_pos n]) hc).comp_tendsto hζ
  have he : ∀ᶠ z in airySector α, H z ≠ 0 := by
    have hnorm := (tendsto_norm_generalizedAiryZeta n α).eventually (eventually_gt_atTop 0)
    filter_upwards [hnorm] with z hz
    have hz0 : ζ z ≠ 0 := norm_pos_iff.mp hz
    exact div_ne_zero (mul_ne_zero (exp_ne_zero _) (cpow_ne_zero_iff.mpr
      (Or.inl (mul_ne_zero two_ne_zero hz0))))
      (ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne')
  have hMt : Tendsto (fun z => DLMF.Bessel.besselI (-p) (ζ z) / H z)
      (airySector α) (𝓝 1) := (isEquivalent_iff_tendsto_one he).mp hM
  have hPt : Tendsto (fun z => DLMF.Bessel.besselI p (ζ z) / H z)
      (airySector α) (𝓝 1) := (isEquivalent_iff_tendsto_one he).mp hP
  have hS := hMt.add hPt
  have hRatio := (hMt.sub hPt).div hS (by norm_num : (1 : ℂ) + 1 ≠ 0)
  simp only [sub_self, zero_div] at hRatio
  have hSne := hS.eventually (eventually_ne_nhds (by norm_num : (1 : ℂ) + 1 ≠ 0))
  have hmem : ∀ᶠ z in airySector α, z ≠ 0 ∧ |arg z| ≤ α :=
    mem_inf_of_right (mem_principal_self _)
  have hAB : ∀ᶠ z in airySector α,
      generalizedAiryA n z / generalizedAiryB n z = p ^ (1 / 2 : ℂ) *
        ((DLMF.Bessel.besselI (-p) (ζ z) / H z - DLMF.Bessel.besselI p (ζ z) / H z) /
          (DLMF.Bessel.besselI (-p) (ζ z) / H z + DLMF.Bessel.besselI p (ζ z) / H z)) ∧
      generalizedAiryB n z ≠ 0 := by
    filter_upwards [hmem, he, hSne] with z hz hH hS
    have harg : |arg z| < π / ((n : ℝ) + 2) := by
      have hα : α < π / ((n : ℝ) + 2) := by
        dsimp [α, generalizedAiryOrder]
        rw [one_div_mul_eq_div]
        linarith
      exact hz.2.trans_lt hα
    obtain ⟨hA, hB⟩ := generalizedAiry_besselI_sector n hz.1 harg
    have hs : DLMF.Bessel.besselI (-p) (ζ z) + DLMF.Bessel.besselI p (ζ z) ≠ 0 := by
      intro hs
      apply hS
      rw [← add_div, hs, zero_div]
    have hph : p ^ (1 / 2 : ℂ) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hp)
    have hzh : z ^ (1 / 2 : ℂ) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hz.1)
    constructor
    · rw [hA, hB]
      have hpp : p ^ (1 / 2 : ℂ) * p ^ (1 / 2 : ℂ) = p := by
        rw [← cpow_add _ _ hp]; norm_num
      change p * z ^ (1 / 2 : ℂ) *
        (DLMF.Bessel.besselI (-p) (ζ z) - DLMF.Bessel.besselI p (ζ z)) /
        (p ^ (1 / 2 : ℂ) * z ^ (1 / 2 : ℂ) *
          (DLMF.Bessel.besselI (-p) (ζ z) + DLMF.Bessel.besselI p (ζ z))) = _
      rw [← sub_div, ← add_div]
      field_simp [hH, hph, hzh, hs]
      linear_combination -(DLMF.Bessel.besselI (-p) (ζ z) -
        DLMF.Bessel.besselI p (ζ z)) * hpp
    · rw [hB]
      exact mul_ne_zero (mul_ne_zero hph hzh) hs
  apply isLittleO_of_tendsto' (hAB.mono fun z hz h => (hz.2 h).elim)
  have ht := hRatio.const_mul (p ^ (1 / 2 : ℂ))
  simp only [mul_zero] at ht
  exact ht.congr' (hAB.mono fun z hz => hz.1.symm)

/-- Multiplication by a positive real number preserves an Airy sector filter. -/
theorem tendsto_ofReal_mul_airySector {c : ℝ} (hc : 0 < c) (α : ℝ) :
    Tendsto (fun z : ℂ => (c : ℂ) * z) (airySector α) (airySector α) := by
  refine tendsto_inf.mpr ⟨tendsto_comap_iff.mpr ?_, tendsto_principal.mpr ?_⟩
  · have ht := (tendsto_comap.mono_left (show airySector α ≤
        comap (fun z : ℂ => ‖z‖) atTop from inf_le_left)).const_mul_atTop hc
    refine ht.congr fun z => ?_
    simp [Real.norm_of_nonneg hc.le]
  · have hmem : ∀ᶠ z in airySector α, z ≠ 0 ∧ |arg z| ≤ α :=
      mem_inf_of_right (mem_principal_self _)
    filter_upwards [hmem] with z hz
    exact ⟨mul_ne_zero (ofReal_ne_zero.mpr hc.ne') hz.1, by
      rw [arg_real_mul _ hc]
      exact hz.2⟩

/-- The modified-Bessel dominant prefactor gives `z^(-n/4)` in the recessive sector. -/
theorem generalizedAiry_dominant_factor (n : ℕ) {z : ℂ} (hz : z ≠ 0)
    (harg : |arg z| < π / ((n : ℝ) + 2)) :
    2 * (generalizedAiryOrder n : ℂ) ^ (1 / 2 : ℂ) * z ^ (1 / 2 : ℂ) *
      (2 * generalizedAiryZeta n z) ^ (-1 / 2 : ℂ) = z ^ (-(n : ℂ) / 4) := by
  set p : ℂ := (generalizedAiryOrder n : ℂ)
  set ζ := generalizedAiryZeta n z
  have hp : p ≠ 0 := generalizedAiryOrder_ne_zero n
  have hn : (n : ℂ) + 2 ≠ 0 := by norm_cast
  have hζ : ζ ≠ 0 := by
    exact mul_ne_zero (div_ne_zero two_ne_zero hn) (cpow_ne_zero_iff.mpr (Or.inl hz))
  have hhalf := generalizedAiryZeta_half_cpow_sector n hz harg (-((n : ℂ) + 2) / 2)
  have horder : -((n : ℂ) + 2) / 2 * (generalizedAiryOrder n : ℂ) = -1 / 2 := by
    simp only [generalizedAiryOrder]; push_cast; field_simp
  rw [horder] at hhalf
  have hfour : (2 * ζ) ^ (-1 / 2 : ℂ) = (4 : ℂ) ^ (-1 / 2 : ℂ) *
      (ζ / 2) ^ (-1 / 2 : ℂ) := by
    rw [cpow_def_of_ne_zero (mul_ne_zero two_ne_zero hζ),
      cpow_def_of_ne_zero (by norm_num : (4 : ℂ) ≠ 0),
      cpow_def_of_ne_zero (div_ne_zero hζ two_ne_zero),
      show 2 * ζ = ((4 : ℝ) : ℂ) * (ζ / 2) by push_cast; ring,
      log_ofReal_mul (by norm_num : (0 : ℝ) < 4) (div_ne_zero hζ two_ne_zero),
      ← exp_add]
    rw [ofReal_log (by norm_num : (0 : ℝ) ≤ 4), ofReal_ofNat]
    congr 1
    ring
  have hfourval : (4 : ℂ) ^ (-1 / 2 : ℂ) = 1 / 2 := by
    rw [show (-1 / 2 : ℂ) = -(1 / 2 : ℂ) by ring, cpow_neg,
      show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num,
      show (4 : ℂ) = ((4 : ℝ) : ℂ) from rfl,
      ← ofReal_cpow (by norm_num), ← Real.sqrt_eq_rpow]
    rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    norm_num
  have hpp : p ^ (1 / 2 : ℂ) * p ^ (-1 / 2 : ℂ) = 1 := by
    rw [← cpow_add _ _ hp]; norm_num
  have hzz : z ^ (1 / 2 : ℂ) * z ^ (-((n : ℂ) + 2) / 2 / 2) = z ^ (-(n : ℂ) / 4) := by
    rw [← cpow_add _ _ hz]
    congr 1
    ring
  change 2 * p ^ (1 / 2 : ℂ) * z ^ (1 / 2 : ℂ) * (2 * ζ) ^ (-1 / 2 : ℂ) = _
  rw [hfour, hfourval, hhalf]
  calc _ = (p ^ (1 / 2 : ℂ) * p ^ (-1 / 2 : ℂ)) *
        (z ^ (1 / 2 : ℂ) * z ^ (-((n : ℂ) + 2) / 2 / 2)) := by ring
    _ = _ := by rw [hpp, one_mul, hzz]

/-- `A_n(z) ~ (p/π)^{1/2} sin(pπ) z^{-n/4} e^{-ζ}` with relative error `O(1/ζ)` as
`z → ∞` in `|ph z| ≤ 3pπ - δ` (DLMF 9.13.9). -/
@[dlmf 9.13.E9]
theorem generalizedAiryA_asymptotic {n : ℕ} (hn : 1 ≤ n)  {δ : ℝ} (hδ : 0 < δ)
    (hδ' : δ < 3 * generalizedAiryOrder n * π) :
    IsBigO (airySector (3 * generalizedAiryOrder n * π - δ))
      (fun z => generalizedAiryA n z -
          ((((generalizedAiryOrder n : ℂ) / π) ^ (1 / 2 : ℂ) *
          sin ((generalizedAiryOrder n : ℂ) * π)) * z ^ (-(n : ℂ) / 4) *
          exp (-generalizedAiryZeta n z)))
          (fun z => ‖z ^ (-(n : ℂ) / 4) * exp (-generalizedAiryZeta n z) /
          (generalizedAiryZeta n z)‖) := by
  sorry

/-- For odd `n`, `A_n(-z) ~ 2 (p/π)^{1/2} cos(pπ/2) z^{-n/4} cos(ζ - π/4)` as
`z → ∞` in `|ph z| ≤ 2pπ - δ`, error `O(|z^{-n/4}/ζ| e^{|ℑζ|})` (DLMF 9.13.10). -/
@[dlmf 9.13.E10]
theorem generalizedAiryA_negative_odd_asymptotic {n : ℕ} (hn : 1 ≤ n)  (hodd : Odd n) {δ : ℝ}
    (hδ : 0 < δ) (hδ' : δ < 2 * generalizedAiryOrder n * π) :
    IsBigO (airySector (2 * generalizedAiryOrder n * π - δ))
      (fun z => generalizedAiryA n (-z) -
          (2 * ((generalizedAiryOrder n : ℂ) / π) ^ (1 / 2 : ℂ) *
          cos ((generalizedAiryOrder n : ℂ) * π / 2) * z ^ (-(n : ℂ) / 4) *
          cos (generalizedAiryZeta n z - π / 4)))
          (fun z => ‖z ^ (-(n : ℂ) / 4) / (generalizedAiryZeta n z)‖ *
          Real.exp |(generalizedAiryZeta n z).im|) := by
  sorry

/-- `B_n(z) ~ π^{-1/2} z^{-n/4} e^{ζ}` with relative error `O(1/ζ)` as `z → ∞` in
`|ph z| ≤ pπ - δ` (DLMF 9.13.11). -/
@[dlmf 9.13.E11]
theorem generalizedAiryB_asymptotic {n : ℕ} (hn : 1 ≤ n)  {δ : ℝ} (hδ : 0 < δ)
    (hδ' : δ < 1 * generalizedAiryOrder n * π) :
    IsBigO (airySector (1 * generalizedAiryOrder n * π - δ))
      (fun z => generalizedAiryB n z -
          ((1 / (π : ℂ) ^ (1 / 2 : ℂ)) * z ^ (-(n : ℂ) / 4) * exp (generalizedAiryZeta n z)))
          (fun z => ‖z ^ (-(n : ℂ) / 4) * exp (generalizedAiryZeta n z) /
          (generalizedAiryZeta n z)‖) := by
  simp only [one_mul] at hδ' ⊢
  set α := generalizedAiryOrder n * π - δ
  set β := ((n : ℝ) + 2) / 2 * α
  set ζ := generalizedAiryZeta n
  set p : ℂ := (generalizedAiryOrder n : ℂ)
  set P : ℂ → ℂ := fun z => p ^ (1 / 2 : ℂ) * z ^ (1 / 2 : ℂ)
  set H : ℂ → ℂ := fun z => exp (ζ z) * (2 * ζ z) ^ (-1 / 2 : ℂ) / (Real.sqrt π : ℂ)
  set Q : ℂ → ℂ := fun z => z ^ (-(n : ℂ) / 4) * exp (ζ z) / ζ z
  have hpbound : generalizedAiryOrder n < 1 / 2 := by
    dsimp only [generalizedAiryOrder]
    have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
    rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hβ : β < π / 2 := by
    dsimp only [β, α, generalizedAiryOrder]
    have hnpos : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    have he : ((n : ℝ) + 2) / 2 * (1 / ((n : ℝ) + 2) * π) = π / 2 := by field_simp
    nlinarith
  have hβ0 : 0 < β := mul_pos (by positivity) (sub_pos.mpr hδ')
  have hc : 0 < Real.cos β := Real.cos_pos_of_mem_Ioo ⟨by linarith, hβ⟩
  have hζ := tendsto_generalizedAiryZeta_sector n hδ hδ'
  have hM := (DLMF.Bessel.besselI_sub_main_isBigO_sector (ν := -p) (by
    simpa [p] using (show -1 / 2 < -generalizedAiryOrder n by linarith)) hc).comp_tendsto hζ
  have hP := (DLMF.Bessel.besselI_sub_main_isBigO_sector (ν := p) (by
    change -1 / 2 < generalizedAiryOrder n
    linarith [generalizedAiryOrder_pos n]) hc).comp_tendsto hζ
  have hmem : ∀ᶠ z in airySector α, z ≠ 0 ∧ |arg z| ≤ α :=
    mem_inf_of_right (mem_principal_self _)
  have hmain : ∀ᶠ z in airySector α, 2 * P z * H z =
      1 / (π : ℂ) ^ (1 / 2 : ℂ) * z ^ (-(n : ℂ) / 4) * exp (ζ z) := by
    filter_upwards [hmem] with z hz
    have harg : |arg z| < π / ((n : ℝ) + 2) := by
      have hα : α < π / ((n : ℝ) + 2) := by
        dsimp [α, generalizedAiryOrder]
        rw [one_div_mul_eq_div]
        linarith
      exact hz.2.trans_lt hα
    have hf := generalizedAiry_dominant_factor n hz.1 harg
    have hπ : (π : ℂ) ^ (1 / 2 : ℂ) = (Real.sqrt π : ℂ) := by
      rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num,
        ← ofReal_cpow Real.pi_pos.le, Real.sqrt_eq_rpow]
    dsimp only [P, H]
    rw [hπ]
    calc _ = (2 * p ^ (1 / 2 : ℂ) * z ^ (1 / 2 : ℂ) *
          (2 * ζ z) ^ (-1 / 2 : ℂ)) * exp (ζ z) / (Real.sqrt π : ℂ) := by ring
      _ = _ := by rw [hf]; ring
  have hO := (isBigO_refl P (airySector α)).mul (hM.add hP)
  refine IsBigO.norm_right ?_
  refine (hO.congr' ?_ EventuallyEq.rfl).trans ?_
  · filter_upwards [hmem, hmain] with z hz hm
    have harg : |arg z| < π / ((n : ℝ) + 2) := by
      have hα : α < π / ((n : ℝ) + 2) := by
        dsimp [α, generalizedAiryOrder]
        rw [one_div_mul_eq_div]
        linarith
      exact hz.2.trans_lt hα
    have hB := (generalizedAiry_besselI_sector n hz.1 harg).2
    dsimp only [Function.comp_apply]
    rw [← hm, hB]
    change P z * ((DLMF.Bessel.besselI (-p) (ζ z) - H z) +
      (DLMF.Bessel.besselI p (ζ z) - H z)) = _
    dsimp only [P]
    ring
  · have h := isBigO_const_mul_self (1 / (2 * (π : ℂ) ^ (1 / 2 : ℂ))) Q (airySector α)
    refine h.congr' ?_ EventuallyEq.rfl
    filter_upwards [hmain] with z hm
    dsimp only [Function.comp_apply]
    change 1 / (2 * (π : ℂ) ^ (1 / 2 : ℂ)) * Q z = P z * (H z / ζ z)
    dsimp only [Q]
    linear_combination -(1 / (2 * ζ z)) * hm

/-- For even `n`, `A_n(-z) ~ (p/π)^{1/2} z^{-n/4} e^{ζ}` with relative error `O(1/ζ)`
as `z → ∞` in `|ph z| ≤ pπ - δ` (DLMF 9.13.10). -/
@[dlmf 9.13.E10]
theorem generalizedAiryA_negative_even_asymptotic {n : ℕ} (hn : 1 ≤ n)  (heven : Even n) {δ : ℝ}
    (hδ : 0 < δ) (hδ' : δ < 1 * generalizedAiryOrder n * π) :
    IsBigO (airySector (1 * generalizedAiryOrder n * π - δ))
      (fun z => generalizedAiryA n (-z) -
          ((((generalizedAiryOrder n : ℂ) / π) ^ (1 / 2 : ℂ)) * z ^ (-(n : ℂ) / 4) *
          exp (generalizedAiryZeta n z)))
          (fun z => ‖z ^ (-(n : ℂ) / 4) * exp (generalizedAiryZeta n z) /
          (generalizedAiryZeta n z)‖) := by
  have h := (generalizedAiryB_asymptotic hn hδ hδ').const_mul_left
    ((generalizedAiryOrder n : ℂ) ^ (1 / 2 : ℂ))
  refine h.congr' (Eventually.of_forall fun z => ?_) EventuallyEq.rfl
  dsimp only
  rw [generalizedAiryA_neg_of_even heven]
  have hc : (generalizedAiryOrder n : ℂ) ^ (1 / 2 : ℂ) * (1 / (π : ℂ) ^ (1 / 2 : ℂ)) =
      ((generalizedAiryOrder n : ℂ) / π) ^ (1 / 2 : ℂ) := by
    rw [div_cpow_ofReal_nonneg (generalizedAiryOrder_pos n).le Real.pi_pos.le]
    ring
  linear_combination -(z ^ (-(n : ℂ) / 4) * exp (generalizedAiryZeta n z)) * hc

/-- For odd `n`, `B_n(-z) ~ -2 π^{-1/2} sin(pπ/2) z^{-n/4} sin(ζ - π/4)` as `z → ∞`
in `|ph z| ≤ 2pπ - δ`, error `O(|z^{-n/4}/ζ| e^{|ℑζ|})` (DLMF 9.13.12). -/
@[dlmf 9.13.E12]
theorem generalizedAiryB_negative_odd_asymptotic {n : ℕ} (hn : 1 ≤ n)  (hodd : Odd n) {δ : ℝ}
    (hδ : 0 < δ) (hδ' : δ < 2 * generalizedAiryOrder n * π) :
    IsBigO (airySector (2 * generalizedAiryOrder n * π - δ))
      (fun z => generalizedAiryB n (-z) -
          (-2 / (π : ℂ) ^ (1 / 2 : ℂ) * sin ((generalizedAiryOrder n : ℂ) * π / 2) *
          z ^ (-(n : ℂ) / 4) *
          sin (generalizedAiryZeta n z - π / 4)))
          (fun z => ‖z ^ (-(n : ℂ) / 4) / (generalizedAiryZeta n z)‖ *
          Real.exp |(generalizedAiryZeta n z).im|) := by
  sorry

/-- For even `n`, `B_n(-z) ~ π^{-1/2} sin(pπ) z^{-n/4} e^{-ζ}` with relative error
`O(1/ζ)` as `z → ∞` in `|ph z| ≤ 3pπ - δ` (DLMF 9.13.12). -/
@[dlmf 9.13.E12]
theorem generalizedAiryB_negative_even_asymptotic {n : ℕ} (hn : 1 ≤ n)  (heven : Even n) {δ : ℝ}
    (hδ : 0 < δ) (hδ' : δ < 3 * generalizedAiryOrder n * π) :
    IsBigO (airySector (3 * generalizedAiryOrder n * π - δ))
      (fun z => generalizedAiryB n (-z) -
          ((1 / (π : ℂ) ^ (1 / 2 : ℂ) * sin ((generalizedAiryOrder n : ℂ) * π)) *
          z ^ (-(n : ℂ) / 4) *
          exp (-generalizedAiryZeta n z)))
          (fun z => ‖z ^ (-(n : ℂ) / 4) * exp (-generalizedAiryZeta n z) /
          (generalizedAiryZeta n z)‖) := by
  sorry

/-- Olver's rotated solution is recessive relative to its dominant companion in every
closed subsector of its stated recessive sector, DLMF §9.13(i). -/
@[dlmf 9.13.E18]
theorem olverAiry_rotated_recessive {m : ℕ} (hm : 3 ≤ m) (j : ℤ)
    {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < π / m) :
    IsLittleO (comap (fun z : ℂ => z * exp (-2 * j * π * I / m)) (airySector (π / m - δ)))
      (fun z => olverAiryU m (z * exp (-2 * j * π * I / m)))
      (fun z => olverAiryVBar m (z * exp (-2 * j * π * I / m))) := by
  suffices h : IsLittleO (airySector (π / m - δ)) (olverAiryU m) (olverAiryVBar m) from
    h.comp_tendsto tendsto_comap
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by omega⟩
  have hn : 1 ≤ n := by omega
  set c : ℝ := (((n + 2 : ℕ) : ℝ) / 2) ^ (2 / ((n + 2 : ℕ) : ℝ))
  have hc : 0 < c := Real.rpow_pos_of_pos (by positivity) _
  have he : (c : ℂ) = ((((n + 2 : ℕ) : ℂ)) / 2) ^ (2 / ((n + 2 : ℕ) : ℂ)) := by
    dsimp only [c]
    rw [ofReal_cpow (by positivity)]
    push_cast
    rfl
  have hδp : δ < generalizedAiryOrder n * π := by
    simpa [generalizedAiryOrder, div_eq_mul_inv, mul_comm] using hδ'
  have hα : π / ((n + 2 : ℕ) : ℝ) - δ = generalizedAiryOrder n * π - δ := by
    simp [generalizedAiryOrder, div_eq_mul_inv, mul_comm]
  rw [hα]
  have h := (generalizedAiryA_isLittleO_generalizedAiryB hn hδ hδp).comp_tendsto
    (tendsto_ofReal_mul_airySector hc (generalizedAiryOrder n * π - δ))
  set C₁ : ℂ := (2 * π : ℂ) ^ (1 / 2 : ℂ) *
    ((((n + 2 : ℕ) : ℂ)) / 2) ^ (((((n + 2 : ℕ) : ℂ)) - 1) / ((n + 2 : ℕ) : ℂ)) /
      sin (π / ((n + 2 : ℕ) : ℂ))
  set C₂ : ℂ := (π : ℂ) ^ (1 / 2 : ℂ) *
    ((((n + 2 : ℕ) : ℂ)) / 2) ^ (((((n + 2 : ℕ) : ℂ)) - 2) / (2 * ((n + 2 : ℕ) : ℂ))) /
      sin (π / ((n + 2 : ℕ) : ℂ))
  have hC₂ : C₂ ≠ 0 := by
    have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
    have hbase : ((((n + 2 : ℕ) : ℂ)) / 2) ≠ 0 := div_ne_zero (by norm_cast) two_ne_zero
    have hs := generalizedAiryOrder_sin_ne_zero n
    have heq : (generalizedAiryOrder n : ℂ) * π = π / ((n + 2 : ℕ) : ℂ) := by
      rw [generalizedAiryOrder_cast]
      ring
    rw [heq] at hs
    exact div_ne_zero (mul_ne_zero (cpow_ne_zero_iff.mpr (Or.inl hπ))
      (cpow_ne_zero_iff.mpr (Or.inl hbase))) hs
  have h' := (h.const_mul_left C₁).const_mul_right hC₂
  change IsLittleO (airySector (generalizedAiryOrder n * π - δ))
    (fun z => olverAiryU (n + 2) z) (fun z => olverAiryVBar (n + 2) z)
  simpa only [Function.comp_apply, he, olverAiryU, olverAiryVBar,
    Nat.add_sub_cancel, C₁, C₂] using h'


end DLMF.Airy
