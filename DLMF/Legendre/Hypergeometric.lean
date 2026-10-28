/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Legendre.Associated
public import DLMF.Legendre.Connections
public import DLMF.Legendre.AssociatedRecurrences

/-!
# Hypergeometric representations and parameter derivatives

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
Theorem statements were initially admitted; remaining `sorry` declarations are
not completed proofs. See `DLMF111214Acquisition.md` for coverage and validation.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF
open scoped Real Topology Nat
namespace DLMF.Legendre

/-- Classical Gauss function on its principal cut plane at regular c. This is a
continuation, not the totalized power series outside its convergence disk. -/
@[dlmf 14.3.E3]
def legendreGaussF (a b c z : ℂ) : ℂ :=
  Gamma c*regularizedGaussHG a b c z

/-- DLMF normalization; the unit-disk agreement is already
`DLMF.Hypergeometric.ordinaryHypergeometric_eq_Gamma_mul_regularizedGaussHG`. -/
@[dlmf 14.3.E3]
theorem legendreGaussF_normalization {a b c z : ℂ} (hc : ∀ n : ℕ, c ≠ -n) :
    regularizedGaussHG a b c z=legendreGaussF a b c z/Gamma c := by
  have hG := Gamma_ne_zero hc
  simp [legendreGaussF, hG]

/-- Pochhammer products supply the limiting gamma quotient at exceptional degrees. -/
@[dlmf 14.3.E4]
theorem ferrersP_integer_hypergeometric_4 (ν : ℂ) (m : ℕ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ferrersP ν m x=(-1)^m*poch (ν-m+1) (2*m)/2^m*(1-x^2:ℂ)^((m:ℂ)/2)*regularizedGaussHG (ν+m+1) (m-ν) (m+1) ((1-x)/2) := by
  rcases m with _ | k
  · simp [ferrersP, poch_zero]
  have hw := mem_cutPlane_of_one_add (show 1+(x:ℂ) ∈ slitPlane from Or.inl (by simp; linarith [hx.1]))
  unfold ferrersP
  rw [show 1-((k+1:ℕ):ℂ) = -(k:ℂ) by push_cast; ring, regularizedGaussHG_neg_nat _ _ _ hw,
    show ν+1+k+1 = ν+((k+1:ℕ):ℂ)+1 by push_cast; ring,
    show -ν+k+1 = ((k+1:ℕ):ℂ)-ν by push_cast; ring,
    show (k:ℂ)+2 = ((k+1:ℕ):ℂ)+1 by push_cast; ring, poch_mul_poch_neg]
  linear_combination ((-1)^(k+1) * poch (ν-((k+1:ℕ):ℂ)+1) (2*(k+1)) *
    regularizedGaussHG (ν+((k+1:ℕ):ℂ)+1) (((k+1:ℕ):ℂ)-ν) (((k+1:ℕ):ℂ)+1) ((1-x)/2)) *
    ferrers_gauge_nat (k+1) hx

/-- Pochhammer products supply the limiting gamma quotient at exceptional degrees. -/
@[dlmf 14.3.E5]
theorem ferrersP_integer_hypergeometric_5 (ν : ℂ) (m : ℕ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ferrersP ν m x=(-1)^m*poch (ν-m+1) (2*m)*((1-x)/(1+x):ℂ)^((m:ℂ)/2)*regularizedGaussHG (ν+1) (-ν) (m+1) ((1-x)/2) := by
  rcases m with _ | k
  · simp [ferrersP, poch_zero]
  have hw := mem_cutPlane_of_one_add (show 1+(x:ℂ) ∈ slitPlane from Or.inl (by simp; linarith [hx.1]))
  have hr : 0 ≤ (1+x)/(1-x) := div_nonneg (by linarith [hx.1]) (by linarith [hx.2])
  have e : ((1-x)/(1+x):ℂ) = ((((1+x)/(1-x):ℝ):ℂ))⁻¹ := by push_cast; rw [inv_div]
  unfold ferrersP
  rw [regularizedGaussHG_legendre_neg_nat ν k hw, e, inv_cpow_ofReal_nonneg hr, poch_mul_poch_neg,
    ← cpow_neg, show -(((k+1:ℕ):ℂ)/2) = -((k+1:ℕ):ℂ)/2 by ring, ← ferrers_gauge_neg_nat (k+1) hx]
  ring

/-- Pochhammer products supply the limiting gamma quotient at exceptional degrees. -/
@[dlmf 14.3.E8]
theorem associatedP_integer_hypergeometric_8 (ν : ℂ) (m : ℕ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    associatedP ν m z=poch (ν-m+1) (2*m)/2^m*legendreBranchPower m z*regularizedGaussHG (ν+m+1) (m-ν) (m+1) ((1-z)/2) := by
  rcases m with _ | k
  · simp [associatedP, legendreBranchPower, poch_zero]
  have hw := mem_cutPlane_of_one_add (one_add_mem_slitPlane_of_sub_one hz)
  have hg := associated_gauge_nat (k+1) hz
  unfold associatedP
  rw [show 1-((k+1:ℕ):ℂ) = -(k:ℂ) by push_cast; ring, regularizedGaussHG_neg_nat _ _ _ hw,
    show ν+1+k+1 = ν+((k+1:ℕ):ℂ)+1 by push_cast; ring,
    show -ν+k+1 = ((k+1:ℕ):ℂ)-ν by push_cast; ring,
    show (k:ℂ)+2 = ((k+1:ℕ):ℂ)+1 by push_cast; ring, poch_mul_poch_neg]
  linear_combination (poch (ν-((k+1:ℕ):ℂ)+1) (2*(k+1)) *
    regularizedGaussHG (ν+((k+1:ℕ):ℂ)+1) (((k+1:ℕ):ℂ)-ν) (((k+1:ℕ):ℂ)+1) ((1-z)/2)) * hg

/-- DLMF 14.3.9: for `z ∉ (-∞, 1]`, `P^{-μ}_ν(z) = ((z-1)/(z+1))^{μ/2} 𝐅(ν+1, -ν; μ+1; (1-z)/2)`,
with principal branches. -/
@[dlmf 14.3.E9]
theorem associated_hypergeometric_9 (ν μ : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    associatedP ν (-μ) z=exp (μ/2*(log (z-1)-log (z+1)))*regularizedGaussHG (ν+1) (-ν) (μ+1) ((1-z)/2) := by
  unfold associatedP
  rw [show 1-(-μ) = μ+1 by ring,
    show -μ/2*(log (z+1)-log (z-1)) = μ/2*(log (z-1)-log (z+1)) by ring]

/-- DLMF 14.3.15: for `z ∉ (-∞, 1]`, `P^{-μ}_ν(z) = 2^{-μ} (z²-1)^{μ/2} 𝐅(μ-ν, ν+μ+1; μ+1;
(1-z)/2)`. -/
@[dlmf 14.3.E15]
theorem associated_hypergeometric_15 (ν μ : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    associatedP ν (-μ) z=2^(-μ)*legendreBranchPower μ z*regularizedGaussHG (μ-ν) (ν+μ+1) (μ+1) ((1-z)/2) := by
  exact associatedP_neg_euler ν μ hz

/-- DLMF 14.3.16: for `z ∉ (-∞, 1]`, `cos(νπ) P^{-μ}_ν(z) = 2^ν π^{1/2} z^{ν-μ}
(z²-1)^{μ/2}/Γ(ν+μ+1) 𝐅((μ-ν)/2, (μ-ν+1)/2; 1/2-ν; 1/z²) - π^{1/2} (z²-1)^{μ/2}/(2^{ν+1} Γ(μ-ν)
z^{ν+μ+1}) 𝐅((ν+μ+2)/2, (ν+μ+1)/2; ν+3/2; 1/z²)`. -/
@[dlmf 14.3.E16]
theorem associated_hypergeometric_16 (ν μ : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    cos (ν*π)*associatedP ν (-μ) z=2^ν*Real.sqrt π*z^(ν-μ)*legendreBranchPower μ z/Gamma (ν+μ+1)*regularizedGaussHG ((μ-ν)/2) ((μ-ν+1)/2) (1/2-ν) (1/z^2)-Real.sqrt π*legendreBranchPower μ z/(2^(ν+1)*Gamma (μ-ν)*z^(ν+μ+1))*regularizedGaussHG ((ν+μ+2)/2) ((ν+μ+1)/2) (ν+3/2) (1/z^2) := by
  set D : Set ℂ := {z : ℂ | z-1 ∈ slitPlane} with hD
  have hDo : IsOpen D := isOpen_slitPlane.preimage (continuous_sub_right 1)
  have hDc : IsPreconnected D := by
    have : D = (fun w => w+1) '' slitPlane := by
      ext w; simp only [hD, mem_image]
      show w - 1 ∈ slitPlane ↔ _
      exact ⟨fun h => ⟨w-1, h, by ring⟩, fun ⟨u, hu, e⟩ => by rw [← e]; simpa using hu⟩
    rw [this]
    exact (StarConvex.isPathConnected starConvex_one_slitPlane (Or.inl (by simp))).isConnected.isPreconnected.image _ (by fun_prop : Continuous fun w : ℂ => w+1).continuousOn
  have hmem : ∀ w ∈ D, w + 1 ∈ slitPlane ∧ w - 1 ∈ slitPlane ∧ w ∈ slitPlane ∧
      (1-w)/2 ∈ cutPlane ∧ 1/w^2 ∈ cutPlane := by
    intro w hw
    have h2 : w - 1 ∈ slitPlane := hw
    have h1 : w + 1 ∈ slitPlane := by
      have := one_add_mem_slitPlane_of_sub_one h2; rwa [add_comm] at this
    have h3 : w ∈ slitPlane := by
      rw [mem_slitPlane_iff] at h2 ⊢
      rcases h2 with h | h
      · left; simp at h; linarith
      · right; simpa using h
    exact ⟨h1, h2, h3, mem_cutPlane_of_one_add (one_add_mem_slitPlane_of_sub_one h2),
      one_sub_recip_sq_mem_slitPlane_of_sub_one h2⟩
  have hf : AnalyticOnNhd ℂ (fun z => cos (ν*π)*associatedP ν (-μ) z) D := by
    refine DifferentiableOn.analyticOnNhd (fun w hw => ?_) hDo
    obtain ⟨h1, h2, -, h4, -⟩ := hmem w hw
    unfold associatedP
    apply DifferentiableAt.differentiableWithinAt
    fun_prop (disch := assumption)
  have hg : AnalyticOnNhd ℂ (fun z => 2^ν*Real.sqrt π*z^(ν-μ)*legendreBranchPower μ z/Gamma (ν+μ+1)*regularizedGaussHG ((μ-ν)/2) ((μ-ν+1)/2) (1/2-ν) (1/z^2)-Real.sqrt π*legendreBranchPower μ z/(2^(ν+1)*Gamma (μ-ν)*z^(ν+μ+1))*regularizedGaussHG ((ν+μ+2)/2) ((ν+μ+1)/2) (ν+3/2) (1/z^2)) D := by
    refine DifferentiableOn.analyticOnNhd (fun w hw => ?_) hDo
    obtain ⟨h1, h2, h3, -, h5⟩ := hmem w hw
    have h0 : w ^ 2 ≠ 0 := pow_ne_zero 2 (slitPlane_ne_zero h3)
    have h6 : w ^ (ν+μ+1) ≠ 0 := by rw [cpow_def_of_ne_zero (slitPlane_ne_zero h3)]; exact exp_ne_zero _
    unfold legendreBranchPower
    simp only [div_eq_mul_inv, mul_inv]
    apply DifferentiableAt.differentiableWithinAt
    fun_prop (disch := first | assumption | simpa [div_eq_mul_inv] using h5)
  have hreal : ∀ t : ℝ, t ∈ Ioo (1:ℝ) 2 → cos (ν*π)*associatedP ν (-μ) t = 2^ν*Real.sqrt π*(t:ℂ)^(ν-μ)*legendreBranchPower μ t/Gamma (ν+μ+1)*regularizedGaussHG ((μ-ν)/2) ((μ-ν+1)/2) (1/2-ν) (1/(t:ℂ)^2)-Real.sqrt π*legendreBranchPower μ t/(2^(ν+1)*Gamma (μ-ν)*(t:ℂ)^(ν+μ+1))*regularizedGaussHG ((ν+μ+2)/2) ((ν+μ+1)/2) (ν+3/2) (1/(t:ℂ)^2) := by
    intro t ht
    have htp : (0:ℝ) < t := by linarith [ht.1]
    have ht0 : (t:ℂ) ≠ 0 := ofReal_ne_zero.mpr htp.ne'
    have hz1 : (t:ℂ) - 1 ∈ slitPlane := Or.inl (by simp; linarith [ht.1])
    rw [associatedP_neg_eq_quadratic ν μ hz1 (by simpa using htp)]
    have hinv : 1/(t:ℂ)^2 = ((1/t^2:ℝ):ℂ) := by push_cast; ring
    have hlt : 1/t^2 < 1 := by rw [div_lt_one (by positivity)]; nlinarith [ht.1]
    have hpos : 0 < 1/t^2 := by positivity
    have hw : ‖1-1/(t:ℂ)^2‖ < 1 := by
      rw [hinv, ← ofReal_one, ← ofReal_sub, norm_real, Real.norm_eq_abs, abs_lt]
      constructor <;> linarith
    have h1w : ‖1-(1-1/(t:ℂ)^2)‖ < 1 := by
      rw [sub_sub_cancel, hinv, norm_real, Real.norm_eq_abs, abs_lt]
      constructor <;> linarith
    have hc := regularized_connection_one_sub ((μ-ν)/2) ((μ-ν+1)/2) (μ+1) hw h1w
    rw [← regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hw,
      ← regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ h1w,
      ← regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ h1w, sub_sub_cancel,
      show μ+1-(μ-ν)/2-(μ-ν+1)/2 = ν+1/2 by ring, show ν+1/2+1 = ν+3/2 by ring,
      show (μ-ν)/2+(μ-ν+1)/2-(μ+1)+1 = 1/2-ν by ring,
      show μ+1-(μ-ν)/2 = (ν+μ+2)/2 by ring, show μ+1-(μ-ν+1)/2 = (ν+μ+1)/2 by ring,
      show (π:ℂ)*(ν+1/2) = ν*π + π/2 by ring, Complex.sin_add_pi_div_two] at hc
    have hd1 := Complex.Gamma_mul_Gamma_add_half ((ν+μ+1)/2)
    rw [show (ν+μ+1)/2+1/2 = (ν+μ+2)/2 by ring, show 1-2*((ν+μ+1)/2) = -ν-μ by ring,
      show 2*((ν+μ+1)/2) = ν+μ+1 by ring] at hd1
    have hd2 := Complex.Gamma_mul_Gamma_add_half ((μ-ν)/2)
    rw [show (μ-ν)/2+1/2 = (μ-ν+1)/2 by ring, show 1-2*((μ-ν)/2) = 1-μ+ν by ring,
      show 2*((μ-ν)/2) = μ-ν by ring] at hd2
    rw [mul_comm (Gamma ((ν+μ+2)/2)), hd1, hd2] at hc
    have hπ : (π:ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
    set s : ℂ := ((Real.sqrt π:ℝ):ℂ) with hs
    have hs0 : s ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
    have hss : s*s = π := by rw [hs, ← ofReal_mul, Real.mul_self_sqrt Real.pi_pos.le]
    have f2 : (π:ℂ)*s⁻¹ = s := by rw [← hss]; field_simp
    have h2 : (2:ℂ) ≠ 0 := two_ne_zero
    have f1 : (2:ℂ)^(-μ)*((2:ℂ)^(-ν-μ))⁻¹ = 2^ν := by
      rw [← cpow_neg, ← cpow_add _ _ h2]; ring_nf
    have f3 : (2:ℂ)^(-μ)*((2:ℂ)^(1-μ+ν))⁻¹ = ((2:ℂ)^(ν+1))⁻¹ := by
      rw [← cpow_neg, ← cpow_neg, ← cpow_add _ _ h2]; ring_nf
    have f4 : (t:ℂ)^(ν-μ)*(1/(t:ℂ)^2)^(ν+1/2) = ((t:ℂ)^(ν+μ+1))⁻¹ := by
      have hl : log (1/(t:ℂ)^2) = -2*log (t:ℂ) := by
        rw [hinv, ← ofReal_log hpos.le, ← ofReal_log htp.le, Real.log_div one_ne_zero (by positivity),
          Real.log_one, Real.log_pow]; push_cast; ring
      have h10 : 1/(t:ℂ)^2 ≠ 0 := by simp [ht0]
      rw [cpow_def_of_ne_zero ht0, cpow_def_of_ne_zero h10, cpow_def_of_ne_zero ht0, hl, ← exp_add,
        ← exp_neg]
      congr 1; ring
    have hmain : cos (ν*π) * regularizedGaussHG ((μ-ν)/2) ((μ-ν+1)/2) (μ+1) (1-1/(t:ℂ)^2) =
        π * (regularizedGaussHG ((μ-ν)/2) ((μ-ν+1)/2) (1/2-ν) (1/(t:ℂ)^2) / (Gamma (ν+μ+1)*2^(-ν-μ)*s) -
          (1/(t:ℂ)^2)^(ν+1/2) / (Gamma (μ-ν)*2^(1-μ+ν)*s) *
            regularizedGaussHG ((ν+μ+2)/2) ((ν+μ+1)/2) (ν+3/2) (1/(t:ℂ)^2)) := by
      rw [← hc]; field_simp
    set T := (t:ℂ)^(ν-μ)
    set Y := (1/(t:ℂ)^2)^(ν+1/2)
    set BP := legendreBranchPower μ t
    set F1 := regularizedGaussHG ((μ-ν)/2) ((μ-ν+1)/2) (1/2-ν) (1/(t:ℂ)^2)
    set F2 := regularizedGaussHG ((ν+μ+2)/2) ((ν+μ+1)/2) (ν+3/2) (1/(t:ℂ)^2)
    set K1 := T*BP*F1*(Gamma (ν+μ+1))⁻¹
    set K2 := BP*F2*(Gamma (μ-ν))⁻¹
    linear_combination ((2:ℂ)^(-μ)*T*BP) * hmain + K1*(π*s⁻¹)*f1 + K1*2^ν*f2
      - K2*(π*s⁻¹)*(T*Y)*f3 - K2*((2:ℂ)^(ν+1))⁻¹*(T*Y)*f2 - K2*((2:ℂ)^(ν+1))⁻¹*s*f4
  have hfreq : ∃ᶠ w in 𝓝[≠] ((3/2:ℝ):ℂ), cos (ν*π)*associatedP ν (-μ) w = 2^ν*Real.sqrt π*w^(ν-μ)*legendreBranchPower μ w/Gamma (ν+μ+1)*regularizedGaussHG ((μ-ν)/2) ((μ-ν+1)/2) (1/2-ν) (1/w^2)-Real.sqrt π*legendreBranchPower μ w/(2^(ν+1)*Gamma (μ-ν)*w^(ν+μ+1))*regularizedGaussHG ((ν+μ+2)/2) ((ν+μ+1)/2) (ν+3/2) (1/w^2) := by
    have hT : Tendsto (fun t : ℝ => (t:ℂ)) (𝓝[≠] (3/2:ℝ)) (𝓝[≠] ((3/2:ℝ):ℂ)) :=
      (continuous_ofReal.tendsto _).inf (tendsto_principal_principal.mpr fun t ht =>
        fun h => ht (ofReal_injective h))
    apply hT.frequently
    have hev : ∀ᶠ t : ℝ in 𝓝[≠] (3/2:ℝ), cos (ν*π)*associatedP ν (-μ) t = 2^ν*Real.sqrt π*(t:ℂ)^(ν-μ)*legendreBranchPower μ t/Gamma (ν+μ+1)*regularizedGaussHG ((μ-ν)/2) ((μ-ν+1)/2) (1/2-ν) (1/(t:ℂ)^2)-Real.sqrt π*legendreBranchPower μ t/(2^(ν+1)*Gamma (μ-ν)*(t:ℂ)^(ν+μ+1))*regularizedGaussHG ((ν+μ+2)/2) ((ν+μ+1)/2) (ν+3/2) (1/(t:ℂ)^2) := by
      apply eventually_nhdsWithin_of_eventually_nhds
      filter_upwards [Ioo_mem_nhds (by norm_num : (1:ℝ) < 3/2) (by norm_num : (3/2:ℝ) < 2)]
        with t ht using hreal t ht
    exact hev.frequently
  have h32 : ((3/2:ℝ):ℂ) ∈ D := Or.inl (by simp; norm_num)
  exact hf.eqOn_of_preconnected_of_frequently_eq hg hDc h32 hfreq hz

/-- DLMF 14.3.18: for `Re z > 0` off the cut, `P^{-μ}_ν(z) = 2^{-μ} z^{ν-μ} (z²-1)^{μ/2} 𝐅((μ-ν)/2,
(μ-ν+1)/2; μ+1; 1-1/z²)`. -/
@[dlmf 14.3.E18]
theorem associated_hypergeometric_18 (ν μ : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) (hre : 0 < z.re) :
    associatedP ν (-μ) z=2^(-μ)*z^(ν-μ)*legendreBranchPower μ z*regularizedGaussHG ((μ-ν)/2) ((μ-ν+1)/2) (μ+1) (1-1/z^2) := by
  exact associatedP_neg_eq_quadratic ν μ hz hre

/-- DLMF 14.3.20: for `z ∉ (-∞, 1]`, `(2 sin(μπ)/π) 𝑸^μ_ν(z) = P^μ_ν(z)/Γ(ν+μ+1) -
P^{-μ}_ν(z)/Γ(ν-μ+1)`. -/
@[dlmf 14.3.E20]
theorem associated_hypergeometric_20 (ν μ : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    2*sin (μ*π)/π*olverQ ν μ z=associatedP ν μ z/Gamma (ν+μ+1)-associatedP ν (-μ) z/Gamma (ν-μ+1) := by
  exact olverQ_connection ν μ hz

/-- Combined boundary value at the hypergeometric cut; separate totalized values on that cut are not used. -/
@[dlmf 14.3.E17]
theorem associatedP_square_hypergeometric (ν μ : ℂ) {x : ℝ} (hx : 1 < x) :
    Tendsto (fun ε : ℝ => let u : ℂ := x^2+I*ε; π*legendreBranchPower μ x/2^μ*(regularizedGaussHG ((μ-ν)/2) ((ν+μ+1)/2) (1/2) u/(Gamma ((μ-ν+1)/2)*Gamma ((ν+μ+2)/2))-x*regularizedGaussHG ((μ-ν+1)/2) ((ν+μ+2)/2) (3/2) u/(Gamma ((μ-ν)/2)*Gamma ((ν+μ+1)/2)))) (𝓝[>] 0) (𝓝 (associatedP ν (-μ) x)) := by
  sorry

/-- Parameter limit includes the removable singularities of the gamma-prefactored representation. -/
@[dlmf 14.3.E19]
theorem olverQ_linear_hypergeometric (ν μ : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    Tendsto (fun v : ℂ => 2^v*Gamma (v+1)*exp (μ/2*log (z+1)-(μ/2+v+1)*log (z-1))*regularizedGaussHG (v+1) (v+μ+1) (2*v+2) (2/(1-z))) (𝓝[≠] ν) (𝓝 (olverQ ν μ z)) := by
  sorry

/-! ### Termwise differentiation in the degree and order derivatives (DLMF 14.11) -/

/-- The `n`-th term of `𝐅(ν+1, -ν; c; w)` as a function of the degree `ν`. -/
noncomputable def legHypT (c w : ℂ) (n : ℕ) (ν : ℂ) : ℂ :=
  (ascPochhammer ℂ n).eval (ν+1) * (ascPochhammer ℂ n).eval (-ν) * w^n / n.factorial *
    (Gamma (c + n))⁻¹

/-- Each term `legHypT c w n` is entire in the degree. -/
theorem legHyp_differentiable_T (c w : ℂ) (n : ℕ) : Differentiable ℂ (legHypT c w n) := by
  have h1 : Differentiable ℂ fun ν : ℂ => (ascPochhammer ℂ n).eval (ν+1) :=
    (Polynomial.differentiable (ascPochhammer ℂ n)).comp (differentiable_id.add_const (1:ℂ))
  have h2 : Differentiable ℂ fun ν : ℂ => (ascPochhammer ℂ n).eval (-ν) :=
    (Polynomial.differentiable (ascPochhammer ℂ n)).comp differentiable_neg
  unfold legHypT
  fun_prop

/-- Locally uniform majorant for the terms `legHypT` near `ν₀`, for `‖w‖ < 1`. -/
theorem legHyp_majorant (c w : ℂ) (hw : ‖w‖ < 1) (ν₀ : ℂ) :
    ∃ N : ℕ, ∃ u : ℕ → ℝ, Summable u ∧
      ∀ n, N ≤ n → ∀ ν ∈ Metric.ball ν₀ 1, ‖legHypT c w n ν‖ ≤ u n := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, 1 - c.re ≤ N := exists_nat_ge _
  have hre : 1 ≤ (c + N).re := by simp only [add_re, natCast_re]; linarith
  have hpole : ∀ k : ℕ, c + N ≠ -k := fun k h => by
    have := congrArg Complex.re h
    simp only [neg_re, natCast_re] at this
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hm : 0 < ‖Gamma (c + N)‖ := norm_pos_iff.mpr (Gamma_ne_zero hpole)
  set p := regularizedGaussHGFunSeries ((‖ν₀+1‖ + 1 : ℝ) : ℂ) ((‖ν₀‖ + 1 : ℝ) : ℂ) (1 - N)
  have hz' : (‖w‖₊ : ENNReal) < p.radius := by
    refine lt_of_lt_of_le ?_ (radius_regularizedGaussHGFunSeries_ge_one _ _ _)
    rw [← ENNReal.coe_one, ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe, coe_nnnorm, NNReal.coe_one]
    exact hw
  refine ⟨N, fun n => (‖Gamma (c + N)‖)⁻¹ * (‖p n‖ * (‖w‖₊ : ℝ) ^ n),
    (p.summable_norm_mul_pow hz').mul_left _, fun n hn ν hν => ?_⟩
  rw [Metric.mem_ball, dist_eq_norm] at hν
  have ha : ‖ν+1‖ ≤ ‖ν₀+1‖ + 1 := by
    calc ‖ν+1‖ = ‖(ν₀+1) + (ν-ν₀)‖ := by ring_nf
      _ ≤ ‖ν₀+1‖ + ‖ν-ν₀‖ := norm_add_le _ _
      _ ≤ _ := by linarith
  have hb : ‖-ν‖ ≤ ‖ν₀‖ + 1 := by
    calc ‖-ν‖ = ‖ν₀ + (ν-ν₀)‖ := by rw [norm_neg]; ring_nf
      _ ≤ ‖ν₀‖ + ‖ν-ν₀‖ := norm_add_le _ _
      _ ≤ _ := by linarith
  simpa only [coe_nnnorm, legHypT] using norm_term_le_majorant ha hb hre hm le_rfl hn

/-- Termwise differentiation in the degree of `𝐅(ν+1, -ν; c; w)` on the unit disk. -/
theorem legHyp_hasSum_deriv (c w : ℂ) (hw : ‖w‖ < 1) (ν₀ : ℂ) :
    HasSum (fun n => legHypT c w n ν₀) (regularizedGaussHGFun (ν₀+1) (-ν₀) c w) ∧
    HasSum (fun n => deriv (legHypT c w n) ν₀)
      (deriv (fun ν => regularizedGaussHGFun (ν+1) (-ν) c w) ν₀) := by
  obtain ⟨N, u, hu, hle⟩ := legHyp_majorant c w hw ν₀
  set U := Metric.ball ν₀ 1
  have hU : IsOpen U := Metric.isOpen_ball
  have h0 : ν₀ ∈ U := Metric.mem_ball_self one_pos
  have huN : Summable fun k => u (k + N) := (summable_nat_add_iff N).mpr hu
  have hleN : ∀ k ν, ν ∈ U → ‖legHypT c w (k+N) ν‖ ≤ u (k+N) := fun k ν hν =>
    hle (k+N) (by omega) ν hν
  have hsumm : ∀ ν ∈ U, Summable fun n => legHypT c w n ν := fun ν hν =>
    (summable_nat_add_iff N).mp (Summable.of_norm_bounded huN fun k => hleN k ν hν)
  have hF : ∀ ν, regularizedGaussHGFun (ν+1) (-ν) c w = ∑' n, legHypT c w n ν := fun ν => by
    rw [regularizedGaussHGFun_eq_tsum]; rfl
  refine ⟨by rw [hF]; exact (hsumm ν₀ h0).hasSum, ?_⟩
  have hdT : ∀ k, DifferentiableOn ℂ (legHypT c w (k+N)) U := fun k =>
    (legHyp_differentiable_T c w (k+N)).differentiableOn
  have htail := hasSum_deriv_of_summable_norm huN hdT hU hleN h0
  have htailD := (differentiableOn_tsum_of_summable_norm huN hdT hU hleN).differentiableAt
    (hU.mem_nhds h0)
  have hfin : HasDerivAt (fun ν => ∑ n ∈ Finset.range N, legHypT c w n ν)
      (∑ n ∈ Finset.range N, deriv (legHypT c w n) ν₀) ν₀ :=
    HasDerivAt.fun_sum fun n _ => (legHyp_differentiable_T c w n ν₀).hasDerivAt
  have heq : (fun ν => regularizedGaussHGFun (ν+1) (-ν) c w) =ᶠ[𝓝 ν₀]
      fun ν => ∑ n ∈ Finset.range N, legHypT c w n ν + ∑' k, legHypT c w (k+N) ν := by
    filter_upwards [hU.mem_nhds h0] with ν hν
    rw [hF, ← (hsumm ν hν).sum_add_tsum_nat_add N]
  have hd : HasDerivAt (fun ν => ∑ n ∈ Finset.range N, legHypT c w n ν + ∑' k, legHypT c w (k+N) ν)
      (∑ n ∈ Finset.range N, deriv (legHypT c w n) ν₀ +
        deriv (fun ν => ∑' k, legHypT c w (k+N) ν) ν₀) ν₀ := hfin.add htailD.hasDerivAt
  rw [heq.deriv_eq, hd.deriv]
  rw [← hasSum_nat_add_iff' N, add_sub_cancel_left]
  exact htail

/-- `Γ' = Γ ψ` away from the poles. -/
theorem legHyp_hasDerivAt_Gamma {s : ℂ} (hs : ∀ m : ℕ, s ≠ -m) :
    HasDerivAt Gamma (Gamma s * digamma s) s := by
  have hd := (differentiableAt_Gamma s hs).hasDerivAt
  convert hd using 1
  rw [digamma_def, logDeriv_apply]
  field_simp [Gamma_ne_zero hs]

/-- `sin(πν) ≠ 0` forces `ν` to be non-integral. -/
theorem legHyp_not_int {ν : ℂ} (h : sin (π*ν) ≠ 0) : ∀ n : ℤ, ν ≠ n := by
  rintro n rfl
  apply h
  rw [Complex.sin_eq_zero_iff]; exact ⟨n, by ring⟩

/-- Non-integral `ν` keeps `ν+1` off the poles of `Γ`. -/
theorem legHyp_pole_add {ν : ℂ} (hν : ∀ n : ℤ, ν ≠ n) : ∀ m : ℕ, ν + 1 ≠ -m := fun m h =>
  hν (-(m:ℤ)-1) (by push_cast; linear_combination h)

/-- Non-integral `ν` keeps `-ν` off the poles of `Γ`. -/
theorem legHyp_pole_neg {ν : ℂ} (hν : ∀ n : ℤ, ν ≠ n) : ∀ m : ℕ, -ν ≠ -m := fun m h =>
  hν m (by push_cast; linear_combination -h)

/-- Off the integers, the term is `-(sin πν/π) Γ(ν+1+n) Γ(-ν+n) wⁿ/(n! Γ(c+n))`. -/
theorem legHyp_T_eq (c w : ℂ) {ν : ℂ} (hν : ∀ n : ℤ, ν ≠ n) (n : ℕ) :
    legHypT c w n ν = -(sin (π*ν)/π) * (Gamma (ν+1+n) * Gamma (-ν+n) *
      (w^n / n.factorial * (Gamma (c+n))⁻¹)) := by
  have h1 := Gamma_add_nat_div_Gamma_eq (n := n) (ν+1) (legHyp_pole_add hν)
  have h2 := Gamma_add_nat_div_Gamma_eq (n := n) (-ν) (legHyp_pole_neg hν)
  have hr := Complex.Gamma_mul_Gamma_one_sub (-ν)
  have hg1 := Gamma_ne_zero (legHyp_pole_add hν)
  have hg2 := Gamma_ne_zero (legHyp_pole_neg hν)
  have hs := DLMF.Hypergeometric.sin_pi_mul_ne_zero_of_not_int hν
  have hπ : (π:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [show (1:ℂ) - -ν = ν + 1 by ring, show (π:ℂ) * -ν = -(π*ν) by ring, Complex.sin_neg] at hr
  unfold legHypT
  rw [← h1, ← h2]
  generalize sin (π*ν) = s at hr hs ⊢
  have hr2 : Gamma (-ν) * Gamma (ν+1) * s = -π := by rw [hr]; field_simp
  field_simp
  linear_combination (Gamma (ν+1+n) * Gamma (-ν+n) * w^n * ((n.factorial:ℂ))⁻¹ * (Gamma (c+n))⁻¹) * hr2

/-- Derivative of a term in the degree, off the integers. -/
theorem legHyp_hasDerivAt_T (c w : ℂ) {ν₀ : ℂ} (hν : ∀ n : ℤ, ν₀ ≠ n) (n : ℕ) :
    HasDerivAt (legHypT c w n) ((-cos (π*ν₀) - sin (π*ν₀)/π *
      (digamma (ν₀+1+n) - digamma (-ν₀+n))) *
      (Gamma (ν₀+1+n) * Gamma (-ν₀+n) * (w^n / n.factorial * (Gamma (c+n))⁻¹))) ν₀ := by
  set d : ℂ := w^n / n.factorial * (Gamma (c+n))⁻¹
  have hπ : (π:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hp1 := DLMF.Hypergeometric.not_neg_nat_add_nat (legHyp_pole_add hν) n
  have hp2 := DLMF.Hypergeometric.not_neg_nat_add_nat (legHyp_pole_neg hν) n
  have hG1 : HasDerivAt (fun ν : ℂ => Gamma (ν+1+n)) (Gamma (ν₀+1+n) * digamma (ν₀+1+n)) ν₀ := by
    have h := (legHyp_hasDerivAt_Gamma hp1).comp ν₀ (((hasDerivAt_id' ν₀).add_const 1).add_const (n:ℂ))
    rw [mul_one] at h; exact h
  have hG2 : HasDerivAt (fun ν : ℂ => Gamma (-ν+n)) (-(Gamma (-ν₀+n) * digamma (-ν₀+n))) ν₀ := by
    have h := (legHyp_hasDerivAt_Gamma hp2).comp ν₀ ((hasDerivAt_neg ν₀).add_const (n:ℂ))
    rw [mul_neg_one] at h; exact h
  have hS : HasDerivAt (fun ν : ℂ => -(sin (π*ν)/π)) (-(cos (π*ν₀) * (π*1) / π)) ν₀ :=
    (((hasDerivAt_id' ν₀).const_mul (π:ℂ)).csin).div_const (π:ℂ) |>.neg
  have hall := (hS.mul (hG1.mul hG2)).mul_const d
  simp only [Pi.mul_apply] at hall
  have hev : legHypT c w n =ᶠ[𝓝 ν₀] fun ν => -(sin (π*ν)/π) * (Gamma (ν+1+n) * Gamma (-ν+n)) * d := by
    have hopen : IsOpen {ν : ℂ | sin (π*ν) ≠ 0} :=
      isOpen_ne_fun (by fun_prop) continuous_const
    filter_upwards [hopen.mem_nhds (DLMF.Hypergeometric.sin_pi_mul_ne_zero_of_not_int hν)] with ν
        hν'
    rw [legHyp_T_eq c w (legHyp_not_int hν') n]; ring
  refine (hall.congr_of_eventuallyEq hev).congr_deriv ?_
  field_simp
  ring

/-- The series of DLMF 14.11.3 in the degree-derivative form: with `S_n = Γ(ν+1+n)Γ(-ν+n)wⁿ/(n!Γ(c+n))`,
`∑ S_n (ψ(ν+1+n) - ψ(-ν+n))` converges, to `(π / sin πν) (-cos πν ∑ S_n - F')`. -/
theorem legHyp_hasSum_R (c w : ℂ) (hw : ‖w‖ < 1) {ν₀ : ℂ} (hν : ∀ n : ℤ, ν₀ ≠ n) :
    let S : ℕ → ℂ := fun n => Gamma (ν₀+1+n) * Gamma (-ν₀+n) * (w^n / n.factorial * (Gamma (c+n))⁻¹)
    HasSum S (-(π / sin (π*ν₀)) * regularizedGaussHGFun (ν₀+1) (-ν₀) c w) ∧
    HasSum (fun n => S n * (digamma (ν₀+1+n) - digamma (-ν₀+n)))
      (π / sin (π*ν₀) * (-cos (π*ν₀) * (-(π / sin (π*ν₀)) * regularizedGaussHGFun (ν₀+1) (-ν₀) c w)
        - deriv (fun ν => regularizedGaussHGFun (ν+1) (-ν) c w) ν₀)) := by
  intro S
  obtain ⟨h0, h1⟩ := legHyp_hasSum_deriv c w hw ν₀
  have hs := DLMF.Hypergeometric.sin_pi_mul_ne_zero_of_not_int hν
  have hπ : (π:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hS : HasSum S (-(π / sin (π*ν₀)) * regularizedGaussHGFun (ν₀+1) (-ν₀) c w) := by
    refine (h0.mul_left (-(π / sin (π*ν₀)))).congr_fun fun n => ?_
    rw [legHyp_T_eq c w hν n]; simp only [S]
    generalize sin (π*ν₀) = s at hs ⊢
    field_simp
  refine ⟨hS, ?_⟩
  have h1' : HasSum (fun n : ℕ => (-cos (π*ν₀) - sin (π*ν₀)/π * (digamma (ν₀+1+n) - digamma (-ν₀+n))) * S n)
      (deriv (fun ν => regularizedGaussHGFun (ν+1) (-ν) c w) ν₀) :=
    h1.congr_fun fun n => ((legHyp_hasDerivAt_T c w hν n).deriv).symm
  refine (((hS.mul_left (-cos (π*ν₀))).sub h1').mul_left (π / sin (π*ν₀))).congr_fun fun n => ?_
  generalize sin (π*ν₀) = s at hs ⊢
  field_simp
  ring

/-- `|(1-x)/2| < 1` on `(-1,1)`. -/
theorem legHyp_norm_w {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) : ‖((1-x)/2:ℂ)‖ < 1 := by
  rw [show ((1-x)/2:ℂ) = (((1-x)/2:ℝ):ℂ) by push_cast; ring, Complex.norm_real, Real.norm_eq_abs,
    abs_lt]
  constructor <;> linarith [hx.1, hx.2]

/-- The degree-derivative series converges throughout its complex argument disk. -/
theorem legHyp_hasSum_A_complex {ν : ℂ} (hν : ∀ n : ℤ, ν ≠ n) (μ : ℂ) {z : ℂ} (hz : ‖(1-z)/2‖ < 1) :
    HasSum (fun k : ℕ => ((1-z)/2)^k*Gamma (k-ν)*Gamma (k+ν+1)/((k.factorial:ℂ)*Gamma (k-μ+1))*
        (digamma (k+ν+1)-digamma (k-ν)))
      (π / sin (π*ν) * (-cos (π*ν) * (-(π / sin (π*ν)) *
        regularizedGaussHGFun (ν+1) (-ν) (1-μ) ((1-z)/2))
        - deriv (fun ν' => regularizedGaussHGFun (ν'+1) (-ν') (1-μ) ((1-z)/2)) ν)) := by
  obtain ⟨-, hR⟩ := legHyp_hasSum_R (1-μ) _ hz hν
  refine hR.congr_fun fun k => ?_
  rw [show (k:ℂ)-ν = -ν+k by ring, show (k:ℂ)+ν+1 = ν+1+k by ring, show (k:ℂ)-μ+1 = 1-μ+k by ring]
  simp only [div_eq_mul_inv, mul_inv]; ring

/-- The series inside `A^μ_ν(x)` (DLMF 14.11.3) converges, with the value given by the degree
derivative of `𝐅(ν+1, -ν; 1-μ; (1-x)/2)`. -/
theorem legHyp_hasSum_A {ν : ℂ} (hν : ∀ n : ℤ, ν ≠ n) (μ : ℂ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    HasSum (fun k : ℕ => ((1-x)/2:ℂ)^k*Gamma (k-ν)*Gamma (k+ν+1)/((k.factorial:ℂ)*Gamma (k-μ+1))*
        (digamma (k+ν+1)-digamma (k-ν)))
      (π / sin (π*ν) * (-cos (π*ν) * (-(π / sin (π*ν)) *
        regularizedGaussHGFun (ν+1) (-ν) (1-μ) ((1-x)/2:ℂ))
        - deriv (fun ν' => regularizedGaussHGFun (ν'+1) (-ν') (1-μ) ((1-x)/2:ℂ)) ν)) := by
  simpa using legHyp_hasSum_A_complex hν μ (legHyp_norm_w hx)

/-- `(1/Γ)' = -ψ/Γ` away from the poles. -/
theorem legHyp_hasDerivAt_recipGamma {s : ℂ} (hs : ∀ m : ℕ, s ≠ -m) :
    HasDerivAt (fun t => (Gamma t)⁻¹) (-digamma s * (Gamma s)⁻¹) s := by
  have h := (legHyp_hasDerivAt_Gamma hs).inv (Gamma_ne_zero hs)
  refine h.congr_deriv ?_
  have := Gamma_ne_zero hs
  field_simp

/-- Order derivative at `μ = 0` from a connection formula
`Γ(ν+μ+1)⁻¹ p(μ) - a(μ) Γ(ν-μ+1)⁻¹ p(-μ) = (2/π) sin(μπ) b(μ) Q(μ)`. -/
theorem legHyp_order_deriv {p a b Q : ℂ → ℂ} {ν D : ℂ} (hν : ∀ m : ℕ, ν+1 ≠ -m)
    (hp : HasDerivAt p D 0) (ha : HasDerivAt a 0 0) (ha0 : a 0 = 1)
    (hb : ContinuousAt b 0) (hQ : ContinuousAt Q 0)
    (hg : ∀ᶠ μ in 𝓝[≠] (0:ℂ), (Gamma (ν+μ+1))⁻¹ * p μ - a μ * ((Gamma (ν-μ+1))⁻¹ * p (-μ)) =
      2/π * sin (μ*π) * (b μ * Q μ)) :
    b 0 * Q 0 = (Gamma (ν+1))⁻¹ * (D - digamma (ν+1) * p 0) := by
  have hπ : (π:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hI := legHyp_hasDerivAt_recipGamma hν
  have h1 : HasDerivAt (fun μ : ℂ => (Gamma (ν+μ+1))⁻¹) (-digamma (ν+1) * (Gamma (ν+1))⁻¹ * 1) 0 :=
    hI.comp_of_eq (0:ℂ) (((hasDerivAt_id' (0:ℂ)).const_add ν).add_const 1) (by ring)
  have h2 : HasDerivAt (fun μ : ℂ => (Gamma (ν-μ+1))⁻¹) (-digamma (ν+1) * (Gamma (ν+1))⁻¹ * (-1)) 0 :=
    hI.comp_of_eq (0:ℂ) (((hasDerivAt_id' (0:ℂ)).const_sub ν).add_const 1) (by ring)
  have hq : HasDerivAt (fun μ => p (-μ)) (D * (-1)) 0 :=
    (show HasDerivAt p D (-(0:ℂ)) by rwa [neg_zero]).comp (0:ℂ) (hasDerivAt_neg (0:ℂ))
  have hG := (h1.mul hp).sub (ha.mul (h2.mul hq))
  have hsl := hasDerivAt_iff_tendsto_slope.mp hG
  have hsin : HasDerivAt (fun μ : ℂ => sin (μ*π)) (cos (0*π) * (1*π)) 0 :=
    ((hasDerivAt_id' (0:ℂ)).mul_const (π:ℂ)).csin
  have hsl2 := hasDerivAt_iff_tendsto_slope.mp hsin
  have hlim : Tendsto (fun μ : ℂ => 2/π * slope (fun μ : ℂ => sin (μ*π)) 0 μ * (b μ * Q μ))
      (𝓝[≠] 0) (𝓝 (2/π * (cos (0*π) * (1*π)) * (b 0 * Q 0))) :=
    (hsl2.const_mul _).mul ((hb.mul hQ).tendsto.mono_left nhdsWithin_le_nhds)
  have heq : slope (fun μ : ℂ => (Gamma (ν+μ+1))⁻¹ * p μ - a μ * ((Gamma (ν-μ+1))⁻¹ * p (-μ))) 0
      =ᶠ[𝓝[≠] 0] fun μ : ℂ => 2/π * slope (fun μ : ℂ => sin (μ*π)) 0 μ * (b μ * Q μ) := by
    filter_upwards [hg] with μ hμ
    simp only [slope_def_field, hμ, ha0, add_zero, sub_zero, neg_zero, zero_mul, Complex.sin_zero,
      one_mul]
    ring
  have hu := tendsto_nhds_unique (hsl.congr' heq) hlim
  simp only [zero_mul, Complex.cos_zero, one_mul, mul_one, ha0, Pi.mul_apply, neg_zero, mul_neg,
    add_zero, sub_zero] at hu
  have hI0 := Gamma_ne_zero hν
  field_simp at hu ⊢
  linear_combination (-1/2:ℂ) * hu

/-- `𝖰^μ_ν(x)` is holomorphic in the order at a regular parameter. -/
theorem legHyp_differentiableAt_ferrersQ_order {ν μ₀ : ℂ} (h : LegendreQRegular ν μ₀) {x : ℝ}
    (hx : x ∈ Ioo (-1:ℝ) 1) : DifferentiableAt ℂ (fun μ => ferrersQ ν μ x) μ₀ := by
  have h1 : ∀ m : ℕ, (ν+μ₀+1)/2 ≠ -m := fun m hm => h (2*m) (by push_cast; linear_combination 2*hm)
  have h2 : ∀ m : ℕ, (ν+μ₀+2)/2 ≠ -m := fun m hm => h (2*m+1) (by push_cast; linear_combination 2*hm)
  have c1 : DifferentiableAt ℂ (fun μ => Gamma ((ν+μ+1)/2)) μ₀ :=
    DifferentiableAt.comp (g := Gamma) μ₀ (differentiableAt_Gamma _ h1) (by fun_prop)
  have c2 : DifferentiableAt ℂ (fun μ => Gamma ((ν+μ+2)/2)) μ₀ :=
    DifferentiableAt.comp (g := Gamma) μ₀ (differentiableAt_Gamma _ h2) (by fun_prop)
  have hinv : Differentiable ℂ fun s : ℂ => (Gamma s)⁻¹ := by
    simpa [one_div] using Complex.differentiable_one_div_Gamma
  have r1 : DifferentiableAt ℂ (fun μ : ℂ => (Gamma ((ν-μ+2)/2))⁻¹) μ₀ :=
    (hinv.comp (by fun_prop : Differentiable ℂ fun μ : ℂ => (ν-μ+2)/2)) μ₀
  have r2 : DifferentiableAt ℂ (fun μ : ℂ => (Gamma ((ν-μ+1)/2))⁻¹) μ₀ :=
    (hinv.comp (by fun_prop : Differentiable ℂ fun μ : ℂ => (ν-μ+1)/2)) μ₀
  have hne := slitPlane_ne_zero (ferrers_one_sub_sq_mem_slitPlane hx)
  have p2 : DifferentiableAt ℂ (fun μ : ℂ => (2:ℂ)^μ) μ₀ :=
    differentiableAt_id.const_cpow (Or.inl (by norm_num))
  have pw : DifferentiableAt ℂ (fun μ : ℂ => (1-(x:ℂ)^2)^(-μ/2)) μ₀ :=
    (differentiableAt_id.neg.div_const 2).const_cpow (Or.inl hne)
  have g1 := differentiable_regularizedGaussHG_comp (A := fun μ => -(ν+μ)/2) (B := fun μ => (ν-μ+1)/2)
    (C := fun _ => 1/2) (by fun_prop) (by fun_prop) (by fun_prop) (ferrers_sq_mem_cutPlane hx)
  have g2 := differentiable_regularizedGaussHG_comp (A := fun μ => (1-ν-μ)/2) (B := fun μ => (ν-μ+2)/2)
    (C := fun _ => 3/2) (by fun_prop) (by fun_prop) (by fun_prop) (ferrers_sq_mem_cutPlane hx)
  have hs : DifferentiableAt ℂ (fun μ : ℂ => sin ((ν+μ)*π/2)) μ₀ := by fun_prop
  have hc : DifferentiableAt ℂ (fun μ : ℂ => cos ((ν+μ)*π/2)) μ₀ := by fun_prop
  unfold ferrersQ ferrersW1 ferrersW2
  simp only [div_eq_mul_inv]
  simp only [div_eq_mul_inv] at g1 g2 c1 c2 r1 r2 pw hs hc
  exact ((differentiableAt_const _).mul hs |>.mul ((((p2.mul c1).mul r1).mul pw).mul (g1 μ₀))).add
    (((differentiableAt_const _).mul hc).mul (((((p2.mul c2).mul r2).mul (differentiableAt_const _)).mul
      pw).mul (g2 μ₀)))

/-- `𝖯^μ_ν(x)` is entire in the order. -/
theorem legHyp_differentiable_ferrersP_order (ν : ℂ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    Differentiable ℂ (fun μ => ferrersP ν μ x) := by
  have hw := legHyp_norm_w hx
  have hr : ((((1+x)/(1-x)):ℝ):ℂ) ≠ 0 := by
    have : 0 < (1+x)/(1-x) := div_pos (by linarith [hx.1]) (by linarith [hx.2])
    exact_mod_cast this.ne'
  have hF := differentiable_regularizedGaussHGFun_of_differentiable (A := fun _ : ℂ => ν+1)
    (B := fun _ : ℂ => -ν) (C := fun μ : ℂ => 1-μ) (differentiable_const _) (differentiable_const _)
    ((differentiable_const _).sub differentiable_id) hw
  have heq : (fun μ => ferrersP ν μ x) = fun μ => ((((1+x)/(1-x)):ℝ):ℂ)^(μ/2) *
      regularizedGaussHGFun (ν+1) (-ν) (1-μ) ((1-x)/2:ℂ) := by
    funext μ
    simp only [ferrersP]
    rw [regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hw]
  rw [heq]
  exact fun μ => ((differentiableAt_id.div_const 2).const_cpow (Or.inl hr)).mul (hF μ)

/-- `1/Γ(ν+μ+1) ≠ 0` gives the regularity of `(ν, μ)` for `Q`. -/
theorem legHyp_regular_of_recip {ν μ : ℂ} (h : (Gamma (ν+μ+1))⁻¹ ≠ 0) : LegendreQRegular ν μ := by
  intro n hn
  apply h
  rw [show ν+μ+1 = -(n:ℂ) by linear_combination hn, Complex.Gamma_neg_nat_eq_zero, inv_zero]

/-- Near `μ = 0`, both `(ν, μ)` and `(ν, -μ)` are regular when `ν+1` is not a pole. -/
theorem legHyp_eventually_regular {ν : ℂ} (hν : ∀ m : ℕ, ν+1 ≠ -m) :
    ∀ᶠ μ in 𝓝 (0:ℂ), LegendreQRegular ν μ ∧ LegendreQRegular ν (-μ) := by
  have hinv : Continuous fun s : ℂ => (Gamma s)⁻¹ := continuous_recip_Gamma
  have h0 : (Gamma (ν+1))⁻¹ ≠ 0 := inv_ne_zero (Gamma_ne_zero hν)
  have o1 : IsOpen {μ : ℂ | (Gamma (ν+μ+1))⁻¹ ≠ 0} :=
    isOpen_ne_fun (hinv.comp (by fun_prop)) continuous_const
  have o2 : IsOpen {μ : ℂ | (Gamma (ν+-μ+1))⁻¹ ≠ 0} :=
    isOpen_ne_fun (hinv.comp (by fun_prop)) continuous_const
  filter_upwards [o1.mem_nhds (by simpa using h0), o2.mem_nhds (by simpa using h0)] with μ h1 h2
  exact ⟨legHyp_regular_of_recip h1, legHyp_regular_of_recip h2⟩

/-- Regularity at order zero keeps `ν+1` off the poles of `Γ`. -/
theorem legHyp_nu {ν : ℂ} (hν : LegendreQRegular ν 0) : ∀ m : ℕ, ν+1 ≠ -m := fun m h =>
  hν m (by linear_combination h)

/-- DLMF 14.11.3: the function `𝖠^μ_ν(x) = sin(νπ) ((1+x)/(1-x))^{μ/2} Σ_{k≥0} ((1-x)/2)^k Γ(k-ν)
Γ(k+ν+1)/(k! Γ(k-μ+1)) (ψ(k+ν+1) - ψ(k-ν))` (as a `tsum`) appearing in the degree derivatives
14.11.1–2. -/
@[dlmf 14.11.E3]
def legendreDegreeA (ν μ : ℂ) (x : ℝ) : ℂ :=
  sin (ν*π)*((1+x)/(1-x):ℂ)^(μ/2)*∑' k : ℕ, ((1-x)/2:ℂ)^k*Gamma (k-ν)*Gamma (k+ν+1)/((k.factorial:ℂ)*Gamma (k-μ+1))*(digamma (k+ν+1)-digamma (k-ν))

/-- DLMF 14.11.3: for non-integer `ν` and `-1 < x < 1`, the series `sin(νπ) ((1+x)/(1-x))^{μ/2} Σ_k
((1-x)/2)^k Γ(k-ν) Γ(k+ν+1)/(k! Γ(k-μ+1)) (ψ(k+ν+1) - ψ(k-ν))` converges to `𝖠^μ_ν(x)`. -/
@[dlmf 14.11.E3]
theorem legendreDegreeA_hasSum {ν : ℂ} (hν : ∀ n : ℤ, ν ≠ n) (μ : ℂ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    HasSum (fun k : ℕ => sin (ν*π)*((1+x)/(1-x):ℂ)^(μ/2)*((1-x)/2:ℂ)^k*Gamma (k-ν)*Gamma (k+ν+1)/((k.factorial:ℂ)*Gamma (k-μ+1))*(digamma (k+ν+1)-digamma (k-ν))) (legendreDegreeA ν μ x) := by
  have hR := legHyp_hasSum_A hν μ hx
  unfold legendreDegreeA
  rw [hR.tsum_eq]
  refine (hR.mul_left (sin (ν*π)*((1+x)/(1-x):ℂ)^(μ/2))).congr_fun fun k => ?_
  ring

/-- DLMF 14.11.1: for non-integer `ν` and `-1 < x < 1`, `∂𝖯^μ_ν(x)/∂ν = π cot(νπ) 𝖯^μ_ν(x) - (1/π)
𝖠^μ_ν(x)`, with `𝖠^μ_ν` the series 14.11.3. -/
@[dlmf 14.11.E1]
theorem ferrersP_degree_deriv {ν : ℂ} (hν : ∀ n : ℤ, ν ≠ n) (μ : ℂ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    HasDerivAt (fun ν => ferrersP ν μ x) (π*cos (ν*π)/sin (ν*π)*ferrersP ν μ x-legendreDegreeA ν μ x/π) ν := by
  have hw := legHyp_norm_w hx
  set w : ℂ := ((1-x)/2:ℂ)
  set F : ℂ → ℂ := fun ν' => regularizedGaussHGFun (ν'+1) (-ν') (1-μ) w
  set pref : ℂ := (((1+x)/(1-x):ℝ):ℂ)^(μ/2)
  have hP : ∀ ν', ferrersP ν' μ x = pref * F ν' := fun ν' => by
    simp only [ferrersP, pref, F, w]
    rw [regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hw]
  have hFd : Differentiable ℂ F :=
    differentiable_regularizedGaussHGFun_of_differentiable (differentiable_id.add_const 1)
      differentiable_neg (differentiable_const _) hw
  have hd : HasDerivAt (fun ν' => ferrersP ν' μ x) (pref * deriv F ν) ν := by
    simp only [hP]; exact ((hFd ν).hasDerivAt).const_mul pref
  refine hd.congr_deriv ?_
  have hR := legHyp_hasSum_A hν μ hx
  unfold legendreDegreeA
  rw [hR.tsum_eq, hP ν]
  have hpref : ((1+x)/(1-x):ℂ)^(μ/2) = pref := by simp only [pref]; push_cast; rfl
  rw [hpref, mul_comm (ν:ℂ) π]
  have hs := DLMF.Hypergeometric.sin_pi_mul_ne_zero_of_not_int hν
  have hπ : (π:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  generalize sin (π*ν) = s at hs ⊢
  field_simp
  ring

/-- DLMF 14.11.2: for non-integer `ν` and `ν + μ` and `-1 < x < 1`, `∂𝖰^μ_ν(x)/∂ν = -(π²/2)
𝖯^μ_ν(x) + π sin(μπ)/(sin(νπ) sin((ν+μ)π)) 𝖰^μ_ν(x) - cot((ν+μ)π)/2 · 𝖠^μ_ν(x) + 𝖠^μ_ν(-x)/(2
sin((ν+μ)π))`. -/
@[dlmf 14.11.E2]
theorem ferrersQ_degree_deriv {ν μ : ℂ} (hν : ∀ n : ℤ, ν ≠ n) (hplus : ∀ n : ℤ, ν+μ ≠ n) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    HasDerivAt (fun ν => ferrersQ ν μ x) (-π^2/2*ferrersP ν μ x+π*sin (μ*π)/(sin (ν*π)*sin ((ν+μ)*π))*ferrersQ ν μ x-cos ((ν+μ)*π)/(2*sin ((ν+μ)*π))*legendreDegreeA ν μ x+legendreDegreeA ν μ (-x)/(2*sin ((ν+μ)*π))) ν := by
  have hx' : -x ∈ Ioo (-1:ℝ) 1 := ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have hπ : (π:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hreg : ∀ ν' : ℂ, sin ((ν'+μ)*π) ≠ 0 → LegendreQRegular ν' μ := fun ν' h n hn => h (by
    rw [Complex.sin_eq_zero_iff]; exact ⟨-(n:ℤ)-1, by rw [hn]; push_cast; ring⟩)
  have hsθ : sin ((ν+μ)*π) ≠ 0 := by
    rw [mul_comm]; exact DLMF.Hypergeometric.sin_pi_mul_ne_zero_of_not_int hplus
  have hsν : sin (ν*π) ≠ 0 := by rw [mul_comm]; exact
      DLMF.Hypergeometric.sin_pi_mul_ne_zero_of_not_int hν
  set G : ℂ → ℂ := fun ν' => π/2 * ((cos ((ν'+μ)*π) * ferrersP ν' μ x - ferrersP ν' μ (-x)) /
    sin ((ν'+μ)*π))
  have hQG : ∀ ν', sin ((ν'+μ)*π) ≠ 0 → ferrersQ ν' μ x = G ν' := fun ν' h => by
    have e := ferrersQ_reflection (hreg ν' h) hx
    simp only [G]
    generalize sin ((ν'+μ)*π) = s at h e ⊢
    generalize cos ((ν'+μ)*π) = c at e ⊢
    field_simp at e ⊢
    linear_combination e
  have hc : HasDerivAt (fun ν' : ℂ => cos ((ν'+μ)*π)) (-sin ((ν+μ)*π) * (1*π)) ν :=
    (((hasDerivAt_id' ν).add_const μ).mul_const (π:ℂ)).ccos
  have hs : HasDerivAt (fun ν' : ℂ => sin ((ν'+μ)*π)) (cos ((ν+μ)*π) * (1*π)) ν :=
    (((hasDerivAt_id' ν).add_const μ).mul_const (π:ℂ)).csin
  have hP1 := ferrersP_degree_deriv hν μ hx
  have hP2 := ferrersP_degree_deriv hν μ hx'
  have hG := ((((hc.mul hP1).sub hP2).div hs hsθ).const_mul ((π:ℂ)/2))
  simp only [Pi.mul_apply, Pi.sub_apply] at hG
  have hev : (fun ν' => ferrersQ ν' μ x) =ᶠ[𝓝 ν] G := by
    have hopen : IsOpen {ν' : ℂ | sin ((ν'+μ)*π) ≠ 0} := isOpen_ne_fun (by fun_prop) continuous_const
    filter_upwards [hopen.mem_nhds hsθ] with ν' h using hQG ν' h
  refine (hG.congr_of_eventuallyEq hev).congr_deriv ?_
  rw [hQG ν hsθ]
  simp only [G]
  have hμ : sin (μ*π) = sin ((ν+μ)*π) * cos (ν*π) - cos ((ν+μ)*π) * sin (ν*π) := by
    rw [← Complex.sin_sub]; ring_nf
  rw [hμ]
  generalize sin ((ν+μ)*π) = sθ at hsθ ⊢
  generalize cos ((ν+μ)*π) = cθ
  generalize sin (ν*π) = sν at hsν ⊢
  generalize cos (ν*π) = cν
  field_simp
  ring

/-- DLMF 14.11.4: when `ν` is not a negative integer and `-1 < x < 1`, `∂𝖯^μ_ν(x)/∂μ` at `μ = 0`
equals `ψ(ν+1) 𝖯_ν(x) + 𝖰_ν(x)`. -/
@[dlmf 14.11.E4]
theorem ferrersP_order_deriv_zero {ν : ℂ} (hν : LegendreQRegular ν 0) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    HasDerivAt (fun μ => ferrersP ν μ x) (digamma (ν+1)*ferrersP ν 0 x+ferrersQ ν 0 x) 0 := by
  have hν1 := legHyp_nu hν
  have hp := ((legHyp_differentiable_ferrersP_order ν hx) 0).hasDerivAt
  have ha : HasDerivAt (fun μ : ℂ => cos (μ*π)) 0 0 := by
    have := ((hasDerivAt_id' (0:ℂ)).mul_const (π:ℂ)).ccos
    simpa using this
  have hb : ContinuousAt (fun μ : ℂ => (Gamma (ν-μ+1))⁻¹) 0 :=
    (continuous_recip_Gamma.comp (by fun_prop : Continuous fun μ : ℂ => ν-μ+1)).continuousAt
  have hQ : ContinuousAt (fun μ : ℂ => ferrersQ ν (-μ) x) 0 :=
    ContinuousAt.comp (g := fun μ => ferrersQ ν μ x) (x := (0:ℂ))
      (by rw [neg_zero]; exact continuousAt_ferrersQ_order hν hx) continuousAt_neg
  have hg : ∀ᶠ μ in 𝓝[≠] (0:ℂ), (Gamma (ν+μ+1))⁻¹ * ferrersP ν μ x -
      cos (μ*π) * ((Gamma (ν-μ+1))⁻¹ * ferrersP ν (-μ) x) =
      2/π * sin (μ*π) * ((Gamma (ν-μ+1))⁻¹ * ferrersQ ν (-μ) x) := by
    filter_upwards [nhdsWithin_le_nhds (legHyp_eventually_regular hν1)] with μ ⟨h1, h2⟩
    have e := ferrers_connection_2 ν μ h1 h2 hx
    simp only [div_eq_mul_inv, mul_inv] at e ⊢
    linear_combination -e
  have key := legHyp_order_deriv hν1 hp ha (by simp) hb hQ hg
  simp only [neg_zero, sub_zero] at key
  have hI := inv_ne_zero (Gamma_ne_zero hν1)
  have hD : deriv (fun μ => ferrersP ν μ x) 0 = digamma (ν+1)*ferrersP ν 0 x+ferrersQ ν 0 x := by
    have := mul_left_cancel₀ hI key
    linear_combination -this
  rwa [hD] at hp

/-- DLMF 14.11.5: when `ν` is not a negative integer and `-1 < x < 1`, `∂𝖰^μ_ν(x)/∂μ` at `μ = 0`
equals `-(π²/4) 𝖯_ν(x) + ψ(ν+1) 𝖰_ν(x)`. -/
@[dlmf 14.11.E5]
theorem ferrersQ_order_deriv_zero {ν : ℂ} (hν : LegendreQRegular ν 0) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    HasDerivAt (fun μ => ferrersQ ν μ x) (-π^2/4*ferrersP ν 0 x+digamma (ν+1)*ferrersQ ν 0 x) 0 := by
  have hν1 := legHyp_nu hν
  have hp := (legHyp_differentiableAt_ferrersQ_order hν hx).hasDerivAt
  have ha : HasDerivAt (fun μ : ℂ => cos (μ*π)) 0 0 := by
    have := ((hasDerivAt_id' (0:ℂ)).mul_const (π:ℂ)).ccos
    simpa using this
  have hb : ContinuousAt (fun μ : ℂ => (Gamma (ν-μ+1))⁻¹) 0 :=
    (continuous_recip_Gamma.comp (by fun_prop : Continuous fun μ : ℂ => ν-μ+1)).continuousAt
  have hQ : ContinuousAt (fun μ : ℂ => -(π:ℂ)^2/4 * ferrersP ν (-μ) x) 0 :=
    continuousAt_const.mul (((legHyp_differentiable_ferrersP_order ν hx).continuous.comp
      continuous_neg).continuousAt)
  have hπ : (π:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hg : ∀ᶠ μ in 𝓝[≠] (0:ℂ), (Gamma (ν+μ+1))⁻¹ * ferrersQ ν μ x -
      cos (μ*π) * ((Gamma (ν-μ+1))⁻¹ * ferrersQ ν (-μ) x) =
      2/π * sin (μ*π) * ((Gamma (ν-μ+1))⁻¹ * (-(π:ℂ)^2/4 * ferrersP ν (-μ) x)) := by
    filter_upwards [nhdsWithin_le_nhds (legHyp_eventually_regular hν1)] with μ ⟨h1, h2⟩
    have e := ferrers_connection_1 ν μ h1 h2 hx
    have hr : 2/π * sin (μ*π) * ((Gamma (ν-μ+1))⁻¹ * (-(π:ℂ)^2/4 * ferrersP ν (-μ) x)) =
        -(π * sin (μ*π) * (Gamma (ν-μ+1))⁻¹ / 2 * ferrersP ν (-μ) x) := by
      field_simp; ring
    rw [hr]
    simp only [div_eq_mul_inv, mul_inv] at e ⊢
    linear_combination e
  have key := legHyp_order_deriv hν1 hp ha (by simp) hb hQ hg
  simp only [neg_zero, sub_zero] at key
  have hI := inv_ne_zero (Gamma_ne_zero hν1)
  have hD : deriv (fun μ => ferrersQ ν μ x) 0 = -π^2/4*ferrersP ν 0 x+digamma (ν+1)*ferrersQ ν 0 x := by
    have := mul_left_cancel₀ hI key
    linear_combination -this
  rwa [hD] at hp

/-- DLMF 14.11.4 (associated case): when `ν` is not a negative integer and `z ∉ (-∞, 1]`,
`∂P^μ_ν(z)/∂μ` at `μ = 0` equals `ψ(ν+1) P_ν(z) + Q_ν(z)`. -/
@[dlmf 14.11.E4]
theorem associatedP_order_deriv_zero {ν : ℂ} (hν : LegendreQRegular ν 0) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    HasDerivAt (fun μ => associatedP ν μ z) (digamma (ν+1)*associatedP ν 0 z+associatedQ ν 0 z) 0 := by
  have hν1 := legHyp_nu hν
  have hp := ((associatedP_entire_order ν z hz) 0).hasDerivAt
  have hQ : ContinuousAt (fun μ : ℂ => olverQ ν μ z) 0 :=
    (olverQ_entire_order ν z hz).continuous.continuousAt
  have hg : ∀ᶠ μ in 𝓝[≠] (0:ℂ), (Gamma (ν+μ+1))⁻¹ * associatedP ν μ z -
      (fun _ => (1:ℂ)) μ * ((Gamma (ν-μ+1))⁻¹ * associatedP ν (-μ) z) =
      2/π * sin (μ*π) * ((fun _ => (1:ℂ)) μ * olverQ ν μ z) := by
    filter_upwards with μ
    have e := associated_connection_15 ν μ hz
    simp only [div_eq_mul_inv, one_mul] at e ⊢
    linear_combination -e
  have key := legHyp_order_deriv hν1 hp (hasDerivAt_const _ _) rfl continuousAt_const hQ hg
  simp only [one_mul] at key
  have hG := Gamma_ne_zero hν1
  have hD : deriv (fun μ => associatedP ν μ z) 0 = digamma (ν+1)*associatedP ν 0 z+associatedQ ν 0 z := by
    simp only [associatedQ, zero_mul, Complex.exp_zero, one_mul, add_zero]
    rw [key]; field_simp; ring
  rwa [hD] at hp

end DLMF.Legendre
