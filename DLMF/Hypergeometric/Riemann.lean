/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Hypergeometric.Solutions
public import DLMF.Hypergeometric.FurtherTransformations

/-!
# Riemann's differential equation (DLMF §15.11)

P-symbols are interpreted as solution spaces. The source's E5 is the Möbius map
appearing explicitly in `riemann_mobius_covariance`; no separate general-purpose
Möbius transformation definition is introduced. The covariance statement treats
finite triples whose images remain finite. The normalized operator and reduction
handle the usual triple containing infinity. A classification of all Fuchsian
equations is deferred until regular singularities on the Riemann sphere are defined.
-/

@[expose] public section

open Complex Filter
open scoped Real Topology

noncomputable section

namespace DLMF.Hypergeometric

/-- Riemann's differential operator with three finite singular points. -/
@[dlmf 15.11.E1]
def riemannOperator (α β γ a₁ a₂ b₁ b₂ c₁ c₂ : ℂ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  iteratedDeriv 2 f z +
    ((1 - a₁ - a₂) / (z - α) + (1 - b₁ - b₂) / (z - β) + (1 - c₁ - c₂) / (z - γ)) * deriv f z +
    ((α - β) * (α - γ) * a₁ * a₂ / (z - α) + (β - α) * (β - γ) * b₁ * b₂ / (z - β)+
      (γ - α) * (γ - β) * c₁ * c₂ / (z - γ)) * f z / ((z - α) * (z - β) * (z - γ))

/-- The P-symbol denotes a set of solutions, not a distinguished scalar function.
The domain is explicit; differentiability is required there. -/
@[dlmf 15.11.E3]
def riemannSolutions (α β γ a₁ a₂ b₁ b₂ c₁ c₂ : ℂ) (U : Set ℂ) : Set (ℂ → ℂ) :=
  {f | ContDiffOn ℂ 2 f U ∧ ∀ z ∈ U, riemannOperator α β γ a₁ a₂ b₁ b₂ c₁ c₂ f z = 0}

/-- Riemann's operator with singularities at `0,1,∞`. -/
def riemannNormalOperator (a₁ a₂ b₁ b₂ c₁ c₂ : ℂ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  iteratedDeriv 2 f z + ((1 - a₁ - a₂) / z + (1 - b₁ - b₂) / (z - 1)) * deriv f z +
    (a₁ * a₂ / z + b₁ * b₂ / (1 - z) - c₁ * c₂) * f z / (z * (1 - z))

/-- The exponent pairs of the Gauss equation satisfy Fuchs's relation. -/
@[dlmf 15.11.E2]
theorem gauss_fuchs_relation (a b c : ℂ) :
    0 + (1 - c) + 0 + (c - a - b) + a + b = 1 := by ring

/-- The Gauss equation is the normalized Riemann equation with these exponent pairs. -/
@[dlmf 15.11.E4]
theorem riemannNormalOperator_gauss (a b c : ℂ) (f : ℂ → ℂ) {z : ℂ}
    (hz : z ≠ 0) (hz1 : z ≠ 1) :
    z * (1 - z) * riemannNormalOperator 0 (1 - c) 0 (c - a - b) a b f z =
      gaussOperator a b c f z := by
  unfold riemannNormalOperator gaussOperator
  field_simp
  ring

/-- A complex function of class `C²` at a point is analytic there. -/
theorem analyticAt_of_contDiffAt_two {f : ℂ → ℂ} {z : ℂ} (hf : ContDiffAt ℂ 2 f z) :
    AnalyticAt ℂ f z := by
  have hev := hf.eventually (by norm_num)
  obtain ⟨U, hU, hUo, hzU⟩ := eventually_nhds_iff.mp hev
  exact DifferentiableOn.analyticAt (fun y hy => ((hU y hy).differentiableAt (by norm_num)).differentiableWithinAt)
    (hUo.mem_nhds hzU)

/-- Identity under the stated parameter and domain assumptions: `riemannOperator α β γ a₁ a₂ b₁ b₂
c₁ c₂ (fun w => ((w - α) / (w - γ)) ^ a₁ * ((w - β) / (w - γ)) ^ b₁ * ₂F₁ (a₁ + b₁ + c₁) (a₁ +
b₁ + c₂) (1 + a₁ - a₂) ((w - α) * (β - γ) / ((w - γ) * (β - α)))) z = 0`. -/
@[dlmf 15.11.E7]
theorem riemann_hypergeometric_solution {α β γ a₁ a₂ b₁ b₂ c₁ c₂ z : ℂ}
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hβγ : β ≠ γ) (hzγ : z ≠ γ)
    (hfuchs : a₁ + a₂ + b₁ + b₂ + c₁ + c₂ = 1)
    (hc : ∀ k : ℕ, 1 + a₁ - a₂ ≠ -(k : ℂ))
    (hα : (z - α) / (z - γ) ∈ slitPlane) (hβ : (z - β) / (z - γ) ∈ slitPlane)
    (hz : ‖(z - α) * (β - γ) / ((z - γ) * (β - α))‖ < 1) :
    riemannOperator α β γ a₁ a₂ b₁ b₂ c₁ c₂
      (fun w => ((w - α) / (w - γ)) ^ a₁ * ((w - β) / (w - γ)) ^ b₁ *
        ₂F₁ (a₁ + b₁ + c₁) (a₁ + b₁ + c₂) (1 + a₁ - a₂) ((w - α) * (β - γ) / ((w - γ) * (β - α)))) z = 0 := by
  set T : ℂ → ℂ := fun w => (w - α) * (β - γ) / ((w - γ) * (β - α)) with hT
  set A : ℂ → ℂ := fun w => (w - α) / (w - γ) with hA
  set B : ℂ → ℂ := fun w => (w - β) / (w - γ) with hB
  set P : ℂ → ℂ := fun w => A w ^ a₁ * B w ^ b₁ with hP
  set Fh : ℂ → ℂ := ₂F₁ (a₁ + b₁ + c₁) (a₁ + b₁ + c₂) (1 + a₁ - a₂) with hFh
  set L : ℂ → ℂ := fun w =>
    a₁ * ((w - α)⁻¹ - (w - γ)⁻¹) + b₁ * ((w - β)⁻¹ - (w - γ)⁻¹) with hL
  have h4 : α - β ≠ 0 := sub_ne_zero.mpr hαβ
  have h5 : α - γ ≠ 0 := sub_ne_zero.mpr hαγ
  have h6 : β - γ ≠ 0 := sub_ne_zero.mpr hβγ
  have h4' : β - α ≠ 0 := sub_ne_zero.mpr hαβ.symm
  set U : Set ℂ := {w | w - γ ≠ 0 ∧ A w ∈ slitPlane ∧ B w ∈ slitPlane} with hU
  have hUo : IsOpen U := by
    have hcont : ContinuousOn A {w | w - γ ≠ 0} := by
      intro w hw; exact ((continuous_id.sub continuous_const).continuousAt.div
        (continuous_id.sub continuous_const).continuousAt hw).continuousWithinAt
    have hcontB : ContinuousOn B {w | w - γ ≠ 0} := by
      intro w hw; exact ((continuous_id.sub continuous_const).continuousAt.div
        (continuous_id.sub continuous_const).continuousAt hw).continuousWithinAt
    have ho : IsOpen {w : ℂ | w - γ ≠ 0} := isOpen_ne_fun (by fun_prop) continuous_const
    have h1 := hcont.isOpen_inter_preimage ho isOpen_slitPlane
    have h2 := hcontB.isOpen_inter_preimage ho isOpen_slitPlane
    convert h1.inter h2 using 1
    ext w; simp only [hU, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage]; tauto
  have hzU : z ∈ U := ⟨sub_ne_zero.mpr hzγ, hα, hβ⟩
  have hne : ∀ w ∈ U, w - α ≠ 0 ∧ w - β ≠ 0 ∧ w - γ ≠ 0 := by
    rintro w ⟨hγ', hA', hB'⟩
    refine ⟨fun h => slitPlane_ne_zero hA' ?_, fun h => slitPlane_ne_zero hB' ?_, hγ'⟩ <;>
      simp only [hA, hB, h, zero_div]
  have hPd : ∀ w ∈ U, HasDerivAt P (P w * L w) w := by
    intro w hw
    obtain ⟨hwα, hwβ, hwγ⟩ := hne w hw
    have hAd : HasDerivAt A ((α - γ) / (w - γ) ^ 2) w := by
      have h := ((hasDerivAt_id w).sub_const α).div ((hasDerivAt_id w).sub_const γ) hwγ
      refine h.congr_deriv ?_; simp only [id]; field_simp; ring
    have hBd : HasDerivAt B ((β - γ) / (w - γ) ^ 2) w := by
      have h := ((hasDerivAt_id w).sub_const β).div ((hasDerivAt_id w).sub_const γ) hwγ
      refine h.congr_deriv ?_; simp only [id]; field_simp; ring
    have hA0 : A w ≠ 0 := slitPlane_ne_zero hw.2.1
    have hB0 : B w ≠ 0 := slitPlane_ne_zero hw.2.2
    refine ((hAd.cpow_const (c := a₁) hw.2.1).mul (hBd.cpow_const (c := b₁) hw.2.2)).congr_deriv ?_
    rw [cpow_sub _ _ hA0, cpow_sub _ _ hB0, cpow_one, cpow_one]
    simp only [hP, hL, hA, hB]
    field_simp
    ring
  have hPa : AnalyticAt ℂ P z := by
    have hγ' : z - γ ≠ 0 := sub_ne_zero.mpr hzγ
    exact ((analyticAt_id.sub analyticAt_const).div (analyticAt_id.sub analyticAt_const) hγ' |>.cpow
      analyticAt_const hα).mul
      (((analyticAt_id.sub analyticAt_const).div (analyticAt_id.sub analyticAt_const) hγ').cpow
        analyticAt_const hβ)
  obtain ⟨hzα, hzβ, hzγ'⟩ := hne z hzU
  have hPdd : deriv (deriv P) z = P z * (L z ^ 2 +
      (a₁ * (-((z - α) ^ 2)⁻¹ + ((z - γ) ^ 2)⁻¹) + b₁ * (-((z - β) ^ 2)⁻¹ + ((z - γ) ^ 2)⁻¹))) := by
    have hev : deriv P =ᶠ[𝓝 z] fun w => P w * L w := by
      filter_upwards [hUo.mem_nhds hzU] with w hw
      rw [(hPd w hw).deriv]
    rw [hev.deriv_eq]
    have hLd : HasDerivAt L (a₁ * (-((z - α) ^ 2)⁻¹ + ((z - γ) ^ 2)⁻¹) +
        b₁ * (-((z - β) ^ 2)⁻¹ + ((z - γ) ^ 2)⁻¹)) z := by
      have h := ((((hasDerivAt_id z).sub_const α).inv hzα).sub
        (((hasDerivAt_id z).sub_const γ).inv hzγ')).const_mul a₁ |>.add
        (((((hasDerivAt_id z).sub_const β).inv hzβ).sub
        (((hasDerivAt_id z).sub_const γ).inv hzγ')).const_mul b₁)
      refine h.congr_deriv ?_; simp only [id]; ring
    have hd : HasDerivAt (fun w => P w * L w) _ z := (hPd z hzU).mul hLd
    rw [hd.deriv]
    ring
  -- the Möbius argument
  set k : ℂ := (β - γ) * (α - γ) / (β - α) with hk
  have hTd : ∀ w : ℂ, w - γ ≠ 0 → HasDerivAt T (k * ((w - γ) ^ 2)⁻¹) w := by
    intro w hw
    have h := (((hasDerivAt_id w).sub_const α).mul_const (β - γ)).div
      (((hasDerivAt_id w).sub_const γ).mul_const (β - α)) (mul_ne_zero hw h4')
    refine h.congr_deriv ?_; simp only [id, hk]; field_simp; ring
  have hTa : AnalyticAt ℂ T z :=
    ((analyticAt_id.sub analyticAt_const).mul analyticAt_const).div
      ((analyticAt_id.sub analyticAt_const).mul analyticAt_const) (mul_ne_zero hzγ' h4')
  have hTdd : deriv (deriv T) z = -2 * k * ((z - γ) ^ 3)⁻¹ := by
    have hopen : IsOpen {w : ℂ | w - γ ≠ 0} := isOpen_ne_fun (by fun_prop) continuous_const
    have hev : deriv T =ᶠ[𝓝 z] fun w => k * ((w - γ) ^ 2)⁻¹ := by
      filter_upwards [hopen.mem_nhds hzγ'] with w hw
      rw [(hTd w hw).deriv]
    rw [hev.deriv_eq]
    have h := ((((hasDerivAt_id z).sub_const γ).pow 2).inv (pow_ne_zero 2 hzγ')).const_mul k
    have hd : HasDerivAt (fun w => k * ((w - γ) ^ 2)⁻¹) _ z := h
    rw [hd.deriv]
    simp only [id, Nat.cast_ofNat, Pi.pow_apply]
    field_simp
    ring
  have hTz : ‖T z‖ < 1 := hz
  have hFa : AnalyticAt ℂ Fh (T z) :=
    (hasFPowerSeriesOnBall_ordinaryHypergeometric _ _ _).analyticAt_of_mem
      (mem_eball_one_of_norm_lt_one hTz)
  have hT0 : T z ≠ 0 := by
    simp only [hT]; exact div_ne_zero (mul_ne_zero hzα h6) (mul_ne_zero hzγ' h4')
  have h1T : 1 - T z = (γ - α) * (z - β) / ((z - γ) * (β - α)) := by
    simp only [hT]; field_simp; ring
  have hT1 : T z ≠ 1 := by
    intro h
    have h0 : 1 - T z = 0 := by rw [h]; ring
    rw [h1T] at h0
    exact div_ne_zero (mul_ne_zero (sub_ne_zero.mpr hαγ.symm) hzβ) (mul_ne_zero hzγ' h4') h0
  have hode := ordinaryHypergeometric_ode (a := a₁ + b₁ + c₁) (b := a₁ + b₁ + c₂) hc hTz hT0 hT1
  have hf : (fun w => ((w - α) / (w - γ)) ^ a₁ * ((w - β) / (w - γ)) ^ b₁ *
      ₂F₁ (a₁ + b₁ + c₁) (a₁ + b₁ + c₂) (1 + a₁ - a₂) ((w - α) * (β - γ) / ((w - γ) * (β - α)))) =
      fun w => P w * Fh (T w) := rfl
  rw [hf]
  simp only [riemannOperator]
  rw [show iteratedDeriv 2 (fun w => P w * Fh (T w)) z = deriv (deriv (fun w => P w * Fh (T w))) z by
    simp only [iteratedDeriv_succ, iteratedDeriv_zero], deriv_deriv_mul_comp hPa hTa hFa,
    (deriv_mul_comp_eventuallyEq hPa hTa hFa).eq_of_nhds, hPdd, (hPd z hzU).deriv, hTdd,
    (hTd z hzγ').deriv]
  rw [← hFh] at hode
  have hc2 : c₂ = 1 - a₁ - a₂ - b₁ - b₂ - c₁ := by linear_combination hfuchs
  subst hc2
  generalize Fh (T z) = F0 at *
  generalize deriv Fh (T z) = F1 at *
  generalize iteratedDeriv 2 Fh (T z) = F2 at *
  generalize P z = P0
  simp only [hT, hL, hk] at hode ⊢
  linear_combination (norm := skip) (P0 * ((β - γ) * (α - γ) / (β - α)) ^ 2 * (β - α) ^ 2 *
    (z - γ) ^ 2 / ((z - α) * (β - γ) * (γ - α) * (z - β)) / (z - γ) ^ 4) * hode
  field_simp
  ring

/-- Identity under the stated parameter and domain assumptions: `riemannNormalOperator (a₁ + l)
(a₂ + l) (b₁ + m) (b₂ + m) (c₁ - l - m) (c₂ - l - m) (fun w => w ^ l * (1 - w) ^ m * f w) z =
0`. -/
@[dlmf 15.11.E8]
theorem riemann_gauge_shift {a₁ a₂ b₁ b₂ c₁ c₂ l m z : ℂ} {f : ℂ → ℂ}
    (hfuchs : a₁ + a₂ + b₁ + b₂ + c₁ + c₂ = 1) (hf : ContDiffAt ℂ 2 f z)
    (hz : z ∈ slitPlane) (hz1 : 1 - z ∈ slitPlane)
    (heq : riemannNormalOperator a₁ a₂ b₁ b₂ c₁ c₂ f z = 0) :
    riemannNormalOperator (a₁ + l) (a₂ + l) (b₁ + m) (b₂ + m) (c₁ - l - m) (c₂ - l - m)
      (fun w => w ^ l * (1 - w) ^ m * f w) z = 0 := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  have h1z0 : 1 - z ≠ 0 := slitPlane_ne_zero hz1
  have hfa := analyticAt_of_contDiffAt_two hf
  set p : ℂ → ℂ := fun w => w ^ l * (1 - w) ^ m with hp
  have hopen : IsOpen {w : ℂ | w ∈ slitPlane ∧ 1 - w ∈ slitPlane} :=
    isOpen_slitPlane.inter (isOpen_slitPlane.preimage (by fun_prop))
  have hmem : z ∈ {w : ℂ | w ∈ slitPlane ∧ 1 - w ∈ slitPlane} := ⟨hz, hz1⟩
  have hpd : ∀ w ∈ {w : ℂ | w ∈ slitPlane ∧ 1 - w ∈ slitPlane},
      HasDerivAt p (p w * (l / w - m / (1 - w))) w := by
    rintro w ⟨hw, hw1⟩
    have hw0 := slitPlane_ne_zero hw
    have hw10 := slitPlane_ne_zero hw1
    have h1 := (hasDerivAt_id w).cpow_const (c := l) hw
    have h2 := ((hasDerivAt_const w (1 : ℂ)).sub (hasDerivAt_id w)).cpow_const (c := m) hw1
    refine (h1.mul h2).congr_deriv ?_
    simp only [id, Pi.sub_apply, hp]
    rw [cpow_sub _ _ hw0, cpow_sub _ _ hw10, cpow_one, cpow_one]
    field_simp
    ring
  have hpa : AnalyticAt ℂ p z :=
    (analyticAt_id.cpow analyticAt_const hz).mul
      ((analyticAt_const.sub analyticAt_id).cpow analyticAt_const hz1)
  have hpdd : deriv (deriv p) z =
      p z * ((l / z - m / (1 - z)) ^ 2 - l / z ^ 2 - m / (1 - z) ^ 2) := by
    have hev : deriv p =ᶠ[𝓝 z] fun w => p w * (l * w⁻¹ - m * (1 - w)⁻¹) := by
      filter_upwards [hopen.mem_nhds hmem] with w hw
      rw [(hpd w hw).deriv]; ring
    rw [hev.deriv_eq]
    have h := (hpd z hmem).mul (((hasDerivAt_id z).inv hz0).const_mul l |>.sub
      ((((hasDerivAt_const z (1 : ℂ)).sub (hasDerivAt_id z)).inv h1z0).const_mul m))
    have hd : deriv (fun w => p w * (l * w⁻¹ - m * (1 - w)⁻¹)) z = _ := h.deriv
    rw [hd]
    simp only [id, Pi.sub_apply, Pi.inv_apply]
    field_simp
    ring
  have hode : riemannNormalOperator a₁ a₂ b₁ b₂ c₁ c₂ f z = 0 := heq
  have hc2 : c₂ = 1 - a₁ - a₂ - b₁ - b₂ - c₁ := by linear_combination hfuchs
  have hid : AnalyticAt ℂ id z := analyticAt_id
  simp only [riemannNormalOperator] at hode ⊢
  rw [show iteratedDeriv 2 (fun w => w ^ l * (1 - w) ^ m * f w) z =
      deriv (deriv (fun w => p w * f (id w))) z by
    simp only [iteratedDeriv_succ, iteratedDeriv_zero, hp, id],
    deriv_deriv_mul_comp hpa hid hfa, hpdd,
    show deriv (fun w => w ^ l * (1 - w) ^ m * f w) z = deriv (fun w => p w * f (id w)) z by rfl,
    (deriv_mul_comp_eventuallyEq hpa hid hfa).eq_of_nhds, (hpd z hmem).deriv]
  have hdid : deriv (id : ℂ → ℂ) = fun _ => 1 := funext fun x => deriv_id x
  have hzm1 : z - 1 ≠ 0 := fun h => h1z0 (by linear_combination -h)
  simp only [hdid, deriv_const, id, hp]
  subst hc2
  generalize f z = F0 at *
  generalize deriv f z = F1 at *
  generalize iteratedDeriv 2 f z = F2 at *
  generalize z ^ l * (1 - z) ^ m = P
  have key : (fun x => x : ℂ → ℂ) = id := rfl
  field_simp at hode ⊢
  linear_combination P * hode

/-- Identity under the stated parameter and domain assumptions: `riemannOperator α β γ a₁ a₂ b₁ b₂
c₁ c₂ (fun w => f ((κ * w + l) / (μ * w + ν))) z = 0`. -/
@[dlmf 15.11.E5, dlmf 15.11.E6]
theorem riemann_mobius_covariance {α β γ a₁ a₂ b₁ b₂ c₁ c₂ κ l μ ν z : ℂ} {f : ℂ → ℂ}
    (hdet : κ * ν - l * μ = 1) (hfuchs : a₁ + a₂ + b₁ + b₂ + c₁ + c₂ = 1)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hβγ : β ≠ γ)
    (hα : μ * α + ν ≠ 0) (hβ : μ * β + ν ≠ 0) (hγ : μ * γ + ν ≠ 0)
    (hz : μ * z + ν ≠ 0) (hzα : z ≠ α) (hzβ : z ≠ β) (hzγ : z ≠ γ)
    (hf : ContDiffAt ℂ 2 f ((κ * z + l) / (μ * z + ν)))
    (heq : riemannOperator ((κ * α + l) / (μ * α + ν)) ((κ * β + l) / (μ * β + ν))
      ((κ * γ + l) / (μ * γ + ν)) a₁ a₂ b₁ b₂ c₁ c₂ f ((κ * z + l) / (μ * z + ν)) = 0) :
    riemannOperator α β γ a₁ a₂ b₁ b₂ c₁ c₂
      (fun w => f ((κ * w + l) / (μ * w + ν))) z = 0 := by
  set T : ℂ → ℂ := fun w => (κ * w + l) / (μ * w + ν) with hT
  have hopen : IsOpen {w : ℂ | μ * w + ν ≠ 0} := isOpen_ne_fun (by fun_prop) continuous_const
  have hTd : ∀ w : ℂ, μ * w + ν ≠ 0 → HasDerivAt T (1 / (μ * w + ν) ^ 2) w := by
    intro w hw
    have h := (((hasDerivAt_id w).const_mul κ).add_const l).div
      (((hasDerivAt_id w).const_mul μ).add_const ν) hw
    refine h.congr_deriv ?_
    simp only [id, mul_one]
    field_simp
    linear_combination hdet
  have hTa : AnalyticAt ℂ T z :=
    ((analyticAt_const.mul analyticAt_id).add analyticAt_const).div
      ((analyticAt_const.mul analyticAt_id).add analyticAt_const) hz
  have hTdd : deriv (deriv T) z = -2 * μ / (μ * z + ν) ^ 3 := by
    have hev : deriv T =ᶠ[𝓝 z] fun w => ((μ * w + ν) ^ 2)⁻¹ := by
      filter_upwards [hopen.mem_nhds hz] with w hw
      rw [(hTd w hw).deriv, one_div]
    rw [hev.deriv_eq]
    have h := ((((hasDerivAt_id z).const_mul μ).add_const ν).pow 2).inv (pow_ne_zero 2 hz)
    have hd : deriv (fun w => ((μ * w + ν) ^ 2)⁻¹) z = _ := h.deriv
    rw [hd]
    simp only [id, mul_one, Nat.cast_ofNat, Pi.pow_apply]
    field_simp
    ring
  have hfa := analyticAt_of_contDiffAt_two hf
  have hd1 : deriv (fun w => f (T w)) z = deriv f (T z) * (1 / (μ * z + ν) ^ 2) :=
    (hfa.differentiableAt.hasDerivAt.comp z (hTd z hz)).deriv
  have hd2 := deriv_deriv_comp hTa hfa
  rw [(hTd z hz).deriv, hTdd] at hd2
  have hdiff : ∀ x y : ℂ, μ * x + ν ≠ 0 → μ * y + ν ≠ 0 →
      T x - T y = (x - y) / ((μ * x + ν) * (μ * y + ν)) := by
    intro x y hx hy
    simp only [hT]
    rw [div_sub_div _ _ hx hy]
    congr 1
    linear_combination (x - y) * hdet
  have hc2 : c₂ = 1 - a₁ - a₂ - b₁ - b₂ - c₁ := by linear_combination hfuchs
  simp only [riemannOperator] at heq ⊢
  rw [show iteratedDeriv 2 (fun w => f (T w)) z = deriv (deriv (fun w => f (T w))) z by
    simp only [iteratedDeriv_succ, iteratedDeriv_zero], hd2, hd1]
  change iteratedDeriv 2 f (T z) + ((1 - a₁ - a₂) / (T z - T α) + (1 - b₁ - b₂) / (T z - T β) +
      (1 - c₁ - c₂) / (T z - T γ)) * deriv f (T z) +
      ((T α - T β) * (T α - T γ) * a₁ * a₂ / (T z - T α) +
        (T β - T α) * (T β - T γ) * b₁ * b₂ / (T z - T β) +
        (T γ - T α) * (T γ - T β) * c₁ * c₂ / (T z - T γ)) * f (T z) /
      ((T z - T α) * (T z - T β) * (T z - T γ)) = 0 at heq
  rw [hdiff z α hz hα, hdiff z β hz hβ, hdiff z γ hz hγ, hdiff α β hα hβ, hdiff α γ hα hγ,
    hdiff β α hβ hα, hdiff β γ hβ hγ, hdiff γ α hγ hα, hdiff γ β hγ hβ] at heq
  subst hc2
  generalize f (T z) = F0 at *
  generalize deriv f (T z) = F1 at *
  generalize iteratedDeriv 2 f (T z) = F2 at *
  have h1 : z - α ≠ 0 := sub_ne_zero.mpr hzα
  have h2 : z - β ≠ 0 := sub_ne_zero.mpr hzβ
  have h3 : z - γ ≠ 0 := sub_ne_zero.mpr hzγ
  have h4 : α - β ≠ 0 := sub_ne_zero.mpr hαβ
  have h5 : α - γ ≠ 0 := sub_ne_zero.mpr hαγ
  have h6 : β - γ ≠ 0 := sub_ne_zero.mpr hβγ
  linear_combination (norm := skip) (1 / (μ * z + ν) ^ 2) ^ 2 * heq
  field_simp
  ring

end DLMF.Hypergeometric
