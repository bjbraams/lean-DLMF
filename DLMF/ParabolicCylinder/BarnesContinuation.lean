/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.ParabolicCylinder.Integrals
public import DLMFMathlib.Analysis.Complex.BarnesResidue

/-!
# Cylinder Barnes integrals with crossed-pole corrections

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
New theorem statements are initially admitted and are not completed proofs.

Both theorems are proved. For `Re A > 0` (`A = 1/2 ± a`) one starts from the straight-line
integrals 12.5.8/12.5.9 on a line `0 < 2c < Re A` and shifts the line to the right across the
poles `t = (A+n)/2` of `Γ(A - 2t)` with `Complex.barnesRes_vertical_shift` (removable form
`Γ(A-2t+n+1)/∏_{j<n}(A-2t+j)`); the general case follows by analytic continuation in `a`, since
the line integral minus the crossed residues is independent of the line and holomorphic in `a`
off the poles of `Γ(A)`. The 12.5.9 case follows from 12.5.8 at `(-a, ±iz)`.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF
open scoped Real Topology Nat
namespace DLMF.Confluent

/-- Residue at the right-pole family t=(A+n)/2; the minus one half Jacobian is retained. -/
def pcfBarnesResidue (second : Bool) (a z : ℂ) (n : ℕ) : ℂ :=
  let A:=if second then 1/2-a else a+1/2; let r:=(A+n)/2; (-1)^(n+1)/(2*(n.factorial:ℂ))*Gamma r*2^r*z^(A+n)*(if second then cos (π*r) else 1)

/-- The finite set of right-family poles crossed by replacing a separating contour with the vertical line Re t=c. -/
def pcfBarnesResidueSum (second : Bool) (a z : ℂ) (c : ℝ) : ℂ :=
  let A:=if second then 1/2-a else a+1/2; ∑ n ∈ Finset.range ((⌈2*c-A.re⌉:ℤ).toNat), pcfBarnesResidue second a z n

/-- Uniform vertical bounds for `Γ` on a strip `|Re w| ≤ X`: with the factor `|sin(π Re w)|`
for all heights, and without it for `|Im w| ≥ 1`. -/
lemma pcfBC_Gamma_bound (X : ℝ) :
    ∃ C : ℝ, ∃ K : ℕ, 0 ≤ C ∧ ∀ x ∈ Icc (-X) X, ∀ y : ℝ,
      ‖Gamma (x + I*y)‖ * |Real.sin (π*x)| ≤ C * (1+|y|)^K * Real.exp (-(π*|y|)/2) ∧
      (1 ≤ |y| → ‖Gamma (x + I*y)‖ ≤ C * (1+|y|)^K * Real.exp (-(π*|y|)/2)) := by
  obtain ⟨C, K, hC⟩ := DLMF.Gamma.exists_norm_recip_Gamma_le (X+1)
  set C0 : ℝ := max C 0
  refine ⟨4*π*C0, K, by positivity, fun x hx y => ?_⟩
  set E : ℝ := Real.exp (π*|y|/2) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hE2 : Real.exp (π*|y|) = E*E := by rw [hE, ← Real.exp_add]; ring_nf
  have hEi : Real.exp (-(π*|y|)/2) = E⁻¹ := by rw [hE, ← Real.exp_neg]; ring_nf
  have hP : 0 ≤ (1+|y|)^K := by positivity
  have h1 : ‖(Gamma (1 - (x + I*y)))⁻¹‖ ≤ C0 * (1+|y|)^K * E := by
    have := hC (1-x) ⟨by linarith [hx.2], by linarith [hx.1]⟩ (-y)
    rw [show ((1-x:ℝ):ℂ) + I*((-y:ℝ):ℂ) = 1 - (x + I*y) by push_cast; ring, abs_neg] at this
    refine this.trans ?_
    gcongr
    exact le_max_left _ _
  have h2 := (Complex.barnesRes_norm_Gamma_mul_sin_le (x + I*y)).trans (mul_le_mul_of_nonneg_left h1 Real.pi_pos.le)
  have hw : (π:ℂ)*(x + I*y) = ((π*x:ℝ):ℂ) + ((π*y:ℝ):ℂ)*I := by push_cast; ring
  rw [hw] at h2
  have hcosh : E*E/2 ≤ Real.cosh (π*y) := by
    rw [← Real.cosh_abs, abs_mul, abs_of_pos Real.pi_pos, Real.cosh_eq, ← hE2]
    have := Real.exp_pos (-(π*|y|)); linarith
  have hG0 := norm_nonneg (Gamma (x + I*y))
  constructor
  · have hs := Complex.barnesRes_abs_sin_mul_cosh_le_norm_sin (π*x) (π*y)
    have h3 : ‖Gamma (x + I*y)‖ * |Real.sin (π*x)| * (E*E/2) ≤ π * (C0 * (1+|y|)^K * E) := by
      refine le_trans ?_ h2
      rw [mul_assoc]
      gcongr
      exact (mul_le_mul_of_nonneg_left hcosh (abs_nonneg _)).trans hs
    rw [hEi]
    rw [← le_div_iff₀ (by positivity)] at h3
    refine h3.trans ?_
    have e : π * (C0 * (1+|y|)^K * E) / (E*E/2) = 2*(π*C0*(1+|y|)^K*E⁻¹) := by field_simp
    have : 0 ≤ π*C0*(1+|y|)^K*E⁻¹ := by positivity
    rw [e]; linarith
  · intro hy
    have hs := Complex.barnesRes_abs_sinh_le_norm_sin (π*x) (π*y)
    have hsinh : E*E/4 ≤ |Real.sinh (π*y)| := by
      rw [Real.abs_sinh, abs_mul, abs_of_pos Real.pi_pos, Real.sinh_eq, ← hE2]
      have hu : π ≤ π*|y| := by nlinarith [Real.pi_pos]
      have h4 := Real.add_one_le_exp (π*|y|)
      have h5 : Real.exp (-(π*|y|)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos])
      nlinarith [Real.pi_gt_three]
    have h3 : ‖Gamma (x + I*y)‖ * (E*E/4) ≤ π * (C0 * (1+|y|)^K * E) := by
      refine le_trans ?_ h2
      gcongr
      exact hsinh.trans hs
    rw [hEi]
    rw [← le_div_iff₀ (by positivity)] at h3
    refine h3.trans (le_of_eq ?_)
    field_simp

/-- Vertical bound for `Γ` on a line `Re w = x` missing the poles. -/
lemma pcfBC_Gamma_bound_pt {x : ℝ} (hx : ∀ n : ℕ, x ≠ -n) :
    ∃ C : ℝ, ∃ K : ℕ, 0 ≤ C ∧ ∀ y : ℝ,
      ‖Gamma (x + I*y)‖ ≤ C * (1+|y|)^K * Real.exp (-(π*|y|)/2) := by
  by_cases hx0 : 0 < x
  · obtain ⟨C, K, h⟩ := DLMF.Gamma.exists_norm_Gamma_le hx0
    exact ⟨C, K, (norm_nonneg _).trans (by simpa using h 0), h⟩
  · push Not at hx0
    have hs := Complex.barnesRes_real_sin_ne_zero hx0 hx
    have hs0 : 0 < |Real.sin (π*x)| := abs_pos.mpr hs
    obtain ⟨C, K, hC0, h⟩ := pcfBC_Gamma_bound |x|
    refine ⟨C / |Real.sin (π*x)|, K, by positivity, fun y => ?_⟩
    have := (h x ⟨neg_abs_le x, le_abs_self x⟩ y).1
    rw [← le_div_iff₀ hs0] at this
    refine this.trans (le_of_eq ?_)
    field_simp

/-- `|Γ(x+iy)| ≤ Γ(x)/Γ(x') |Γ(x'+iy)|` for `0 < x ≤ x'`. -/
lemma pcfBC_norm_Gamma_le_ratio {x x' : ℝ} (hx : 0 < x) (hxx : x ≤ x') (y : ℝ) :
    ‖Gamma (x + I*y)‖ ≤ Real.Gamma x / Real.Gamma x' * ‖Gamma (x' + I*y)‖ := by
  have hx' : 0 < x' := hx.trans_le hxx
  have h1 := DLMF.Gamma.norm_Gamma_sq_eq hx y
  have h2 := DLMF.Gamma.norm_Gamma_sq_eq hx' y
  have hP := DLMF.Gamma.gammaVertProd_anti hx hxx y
  have hP1 := DLMF.Gamma.one_le_gammaVertProd x' y
  have hG' := Real.Gamma_pos_of_pos hx'
  have hG := Real.Gamma_pos_of_pos hx
  rw [← pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero, mul_pow, h1, h2]
  calc Real.Gamma x ^ 2 / DLMF.Gamma.gammaVertProd x y
      ≤ Real.Gamma x ^ 2 / DLMF.Gamma.gammaVertProd x' y :=
        div_le_div_of_nonneg_left (by positivity) (by linarith) hP
    _ = _ := by field_simp

/-- Uniform vertical bound for `Γ` on a strip `0 < c₁ ≤ Re w ≤ c₂`. -/
lemma pcfBC_Gamma_bound_strip {c₁ c₂ : ℝ} (hc : 0 < c₁) :
    ∃ C : ℝ, ∃ K : ℕ, 0 ≤ C ∧ ∀ x ∈ Icc c₁ c₂, ∀ y : ℝ,
      ‖Gamma (x + I*y)‖ ≤ C * (1+|y|)^K * Real.exp (-(π*|y|)/2) := by
  by_cases h12 : c₁ ≤ c₂
  · have hc2 : 0 < c₂ := hc.trans_le h12
    obtain ⟨G, hG⟩ := (isCompact_Icc (a := c₁) (b := c₂)).exists_bound_of_continuousOn
      (f := Real.Gamma) (fun x hx => (Real.differentiableAt_Gamma (fun m h => by
        have : (0:ℝ) < x := hc.trans_le hx.1
        linarith [(m.cast_nonneg : (0:ℝ) ≤ m)])).continuousAt.continuousWithinAt)
    obtain ⟨C, K, hC⟩ := DLMF.Gamma.exists_norm_Gamma_le hc2
    have hC0 : 0 ≤ C := (norm_nonneg _).trans (by simpa using hC 0)
    have hG2 := Real.Gamma_pos_of_pos hc2
    refine ⟨|G| / Real.Gamma c₂ * C, K, by positivity, fun x hx y => ?_⟩
    refine (pcfBC_norm_Gamma_le_ratio (hc.trans_le hx.1) hx.2 y).trans ?_
    have hGx : Real.Gamma x ≤ |G| := by
      have := hG x hx; rw [Real.norm_eq_abs] at this
      exact (le_abs_self _).trans (this.trans (le_abs_self G))
    calc Real.Gamma x / Real.Gamma c₂ * ‖Gamma (c₂ + I*y)‖
        ≤ |G| / Real.Gamma c₂ * (C * (1+|y|)^K * Real.exp (-(π*|y|)/2)) := by
          gcongr
          exact hC y
      _ = _ := by ring
  · exact ⟨0, 0, le_rfl, fun x hx => absurd (hx.1.trans hx.2) h12⟩

/-- The Barnes integrand `Γ(t) Γ(A-2t) 2^t z^{2t}` of DLMF 12.5.8 with `A = a + 1/2`. -/
def pcfBC_F (A z t : ℂ) : ℂ := Gamma t * Gamma (A - 2*t) * 2^t * z^(2*t)

lemma pcfBC_F_eq_B (a z : ℂ) (c y : ℝ) : pcfBC_F (1/2+1*a) z (c + y*I) = pcfInt_B a z c y := by
  unfold pcfBC_F pcfInt_B; ring_nf

/-- Pointwise bound for the Barnes integrand from vertical bounds of the two Gamma factors. -/
lemma pcfBC_norm_F_le {A z : ℂ} (hz : z ≠ 0) (x y : ℝ) {C1 C2 : ℝ} {K1 K2 : ℕ}
    (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2)
    (g1 : ‖Gamma (x + I*y)‖ ≤ C1 * (1+|y|)^K1 * Real.exp (-(π*|y|)/2))
    (g2 : ‖Gamma ((A.re - 2*x : ℝ) + I*(A.im - 2*y : ℝ))‖ ≤
      C2 * (1+|A.im - 2*y|)^K2 * Real.exp (-(π*|A.im - 2*y|)/2)) :
    ‖pcfBC_F A z (x + y*I)‖ ≤ C1 * C2 * (2*(1+|A.im|))^K2 * Real.exp (π*|A.im|/2) *
      (2:ℝ)^x * ‖z‖^(2*x) * ((1+|y|)^(K1+K2) * Real.exp (-((3*π/2 - 2*|arg z|)*|y|))) := by
  have e1 : (x:ℂ)+y*I = x + I*y := by ring
  have e2 : A-2*((x:ℂ)+y*I) = ((A.re - 2*x : ℝ) : ℂ) + I*((A.im - 2*y : ℝ) : ℂ) := by
    apply Complex.ext <;> simp
  have hp : (1 + |A.im - 2*y|)^K2 ≤ (2*(1+|A.im|))^K2 * (1+|y|)^K2 := by
    rw [← mul_pow]; gcongr
    have := abs_sub (A.im) (2*y); rw [abs_mul, abs_two] at this
    nlinarith [abs_nonneg A.im, abs_nonneg y]
  have he : Real.exp (-(π * |A.im - 2*y|) / 2) ≤ Real.exp (π*|A.im|/2) * Real.exp (-(π*|y|)) := by
    rw [← Real.exp_add]; apply Real.exp_le_exp.mpr
    have := abs_sub_abs_le_abs_sub (2*y) (A.im)
    rw [abs_mul, abs_two, abs_sub_comm] at this
    nlinarith [Real.pi_pos]
  have h2t : ‖(2:ℂ)^((x:ℂ)+y*I)‖ = (2:ℝ)^x := by
    rw [show (2:ℂ) = ((2:ℝ):ℂ) by norm_cast, norm_cpow_eq_rpow_re_of_pos (by norm_num)]; simp
  have hz2 := pcfInt_norm_cpow_two_mul_le hz x y
  unfold pcfBC_F
  rw [norm_mul, norm_mul, norm_mul, h2t, e2]
  rw [e1] at hz2 ⊢
  rw [← e1] at g1 hz2 ⊢
  calc ‖Gamma ((x:ℂ)+y*I)‖ * ‖Gamma (((A.re - 2*x : ℝ) : ℂ) + I*((A.im - 2*y : ℝ) : ℂ))‖ *
        (2:ℝ)^x * ‖z^(2*((x:ℂ)+y*I))‖
      ≤ (C1 * (1 + |y|)^K1 * Real.exp (-(π*|y|)/2)) *
          (C2 * ((2*(1+|A.im|))^K2 * (1+|y|)^K2) * (Real.exp (π*|A.im|/2) * Real.exp (-(π*|y|)))) *
          (2:ℝ)^x * (‖z‖^(2*x) * Real.exp (2*|arg z| *|y|)) := by
        gcongr
        exact g2.trans (by gcongr)
    _ = C1 * C2 * (2*(1+|A.im|))^K2 * Real.exp (π*|A.im|/2) * (2:ℝ)^x * ‖z‖^(2*x) *
          ((1+|y|)^(K1+K2) *
          (Real.exp (-(π*|y|)/2) * Real.exp (-(π*|y|)) * Real.exp (2*|arg z| *|y|))) := by ring
    _ = _ := by
        rw [← Real.exp_add, ← Real.exp_add]; ring_nf

lemma pcfBC_F_differentiableAt {A z t : ℂ} (hz : z ≠ 0) (ht : 0 < t.re)
    (hA : ∀ m : ℕ, A - 2*t ≠ -m) : DifferentiableAt ℂ (pcfBC_F A z) t := by
  have ht' : ∀ m : ℕ, t ≠ -m := fun m h => by
    rw [h] at ht; simp at ht; linarith [(m.cast_nonneg : (0:ℝ) ≤ m)]
  unfold pcfBC_F
  refine (((differentiableAt_Gamma t ht').mul ((differentiableAt_Gamma _ hA).comp t
    (by fun_prop))).mul (differentiableAt_id.const_cpow (Or.inl two_ne_zero))).mul
    ((differentiableAt_id.const_mul 2).const_cpow (Or.inl hz))

lemma pcfBC_F_differentiableAt_param {A z t : ℂ} (hA : ∀ m : ℕ, A - 2*t ≠ -m) :
    DifferentiableAt ℂ (fun A => pcfBC_F A z t) A := by
  unfold pcfBC_F
  exact (((differentiableAt_const _).mul ((differentiableAt_Gamma _ hA).comp A
    (by fun_prop))).mul (differentiableAt_const _)).mul (differentiableAt_const _)

lemma pcfBC_ne_pole {A : ℂ} {x : ℝ} (hav : ∀ n : ℕ, 2*x ≠ A.re + n) (y : ℝ) :
    ∀ m : ℕ, A - 2*((x:ℂ)+y*I) ≠ -m := fun m h => by
  have := congrArg re h; simp at this; exact hav m (by linarith)

lemma pcfBC_F_continuous {A z : ℂ} (hz : z ≠ 0) {c : ℝ} (hc : 0 < c)
    (hav : ∀ n : ℕ, 2*c ≠ A.re + n) : Continuous fun y : ℝ => pcfBC_F A z (c + y*I) :=
  continuous_iff_continuousAt.mpr fun y => by
    have h := (pcfBC_F_differentiableAt hz (by simp [hc]) (pcfBC_ne_pole hav y)).continuousAt
    exact h.comp (f := fun y : ℝ => (c:ℂ) + y*I) (by fun_prop)

/-- The Barnes integrand is integrable on every line `Re t = c > 0` missing the poles. -/
lemma pcfBC_F_integrable {A z : ℂ} (hz0 : z ≠ 0) (hz : |arg z| < 3*π/4) {c : ℝ} (hc : 0 < c)
    (hav : ∀ n : ℕ, 2*c ≠ A.re + n) : Integrable fun y : ℝ => pcfBC_F A z (c + y*I) := by
  obtain ⟨C1, K1, h1⟩ := DLMF.Gamma.exists_norm_Gamma_le hc
  have hC1 : 0 ≤ C1 := (norm_nonneg _).trans (by simpa using h1 0)
  obtain ⟨C2, K2, hC2, h2⟩ := pcfBC_Gamma_bound_pt (x := A.re - 2*c)
    (fun n h => hav n (by linarith))
  refine ((DLMF.Gamma.integrable_one_add_abs_pow_mul_exp_neg (c := 3*π/2 - 2*|arg z|)
    (by linarith) (K1+K2)).const_mul _).mono' (pcfBC_F_continuous hz0 hc hav).aestronglyMeasurable
    (Eventually.of_forall fun y => pcfBC_norm_F_le hz0 c y hC1 hC2 (h1 y) (h2 _))

/-- `‖z‖^{2x} ≤ ‖z‖^{2c₁} + ‖z‖^{2c₂}` on `[c₁, c₂]`. -/
lemma pcfBC_rpow_le {r : ℝ} (hr : 0 < r) {c₁ c₂ x : ℝ} (hx : x ∈ Icc c₁ c₂) :
    r^(2*x) ≤ r^(2*c₁) + r^(2*c₂) := by
  rcases le_total 1 r with h1 | h1
  · have := Real.rpow_le_rpow_of_exponent_le h1 (show 2*x ≤ 2*c₂ by linarith [hx.2])
    linarith [Real.rpow_nonneg hr.le (2*c₁)]
  · have := Real.rpow_le_rpow_of_exponent_ge hr h1 (show 2*c₁ ≤ 2*x by linarith [hx.1])
    linarith [Real.rpow_nonneg hr.le (2*c₂)]

open scoped Interval in
/-- Horizontal cross-sections of the Barnes integrand vanish at `±i∞`. -/
lemma pcfBC_F_horizontal {A z : ℂ} (hz0 : z ≠ 0) (hz : |arg z| < 3*π/4) {c₁ c₂ : ℝ}
    (hc : 0 < c₁) (h12 : c₁ ≤ c₂) :
    Tendsto (fun T : ℝ => ∫ x in c₁..c₂, pcfBC_F A z (x + T*I)) atTop (𝓝 0) ∧
    Tendsto (fun T : ℝ => ∫ x in c₁..c₂, pcfBC_F A z (x + T*I)) atBot (𝓝 0) := by
  obtain ⟨C1, K1, hC1, h1⟩ := pcfBC_Gamma_bound_strip (c₂ := c₂) hc
  obtain ⟨C2, K2, hC2, h2⟩ := pcfBC_Gamma_bound (|A.re| + 2*c₂)
  set b : ℝ := 3*π/2 - 2*|arg z|
  have hb : 0 < b := by simp only [b]; linarith
  have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  set M : ℝ := C1 * C2 * (2*(1+|A.im|))^K2 * Real.exp (π*|A.im|/2) * (2:ℝ)^c₂ *
    (‖z‖^(2*c₁) + ‖z‖^(2*c₂))
  have hM : 0 ≤ M := by positivity
  have key : ∀ T : ℝ, 1 ≤ |A.im - 2*T| → ‖∫ x in c₁..c₂, pcfBC_F A z (x + T*I)‖ ≤
      (c₂ - c₁) * (M * ((1 + |T|) ^ (K1+K2) * Real.exp (-(b * |T|)))) := by
    intro T hT
    have hpt : ∀ x ∈ Ι c₁ c₂, ‖pcfBC_F A z (x + T*I)‖ ≤
        M * ((1 + |T|) ^ (K1+K2) * Real.exp (-(b * |T|))) := by
      intro x hx
      rw [uIoc_of_le h12] at hx
      have hxI : x ∈ Icc c₁ c₂ := ⟨hx.1.le, hx.2⟩
      have hX : A.re - 2*x ∈ Icc (-(|A.re| + 2*c₂)) (|A.re| + 2*c₂) := by
        constructor <;> linarith [abs_le.mp (le_refl |A.re|), le_abs_self A.re, neg_abs_le A.re,
          hxI.1, hxI.2]
      refine (pcfBC_norm_F_le hz0 x T hC1 hC2 (h1 x hxI T) ((h2 _ hX _).2 hT)).trans ?_
      have h2x : (2:ℝ)^x ≤ (2:ℝ)^c₂ := Real.rpow_le_rpow_of_exponent_le (by norm_num) hxI.2
      have hzx := pcfBC_rpow_le hzn hxI
      simp only [M, b]
      gcongr
    have := intervalIntegral.norm_integral_le_of_norm_le_const hpt
    rw [abs_of_nonneg (sub_nonneg.mpr h12)] at this
    linarith
  have hlim := Complex.barnesRes_tendsto_poly_exp hb (K1+K2)
  have l1 := ((hlim.comp tendsto_abs_atTop_atTop).const_mul M).const_mul (c₂ - c₁)
  have l2 := ((hlim.comp tendsto_abs_atBot_atTop).const_mul M).const_mul (c₂ - c₁)
  simp only [mul_zero] at l1 l2
  constructor
  · refine squeeze_zero_norm' ?_ l1
    filter_upwards [eventually_ge_atTop (|A.im| + 1)] with T hT
    exact key T (by
      rw [abs_sub_comm, abs_of_nonneg (by linarith [le_abs_self A.im, abs_nonneg A.im])]
      linarith [le_abs_self A.im, abs_nonneg A.im])
  · refine squeeze_zero_norm' ?_ l2
    filter_upwards [eventually_le_atBot (-(|A.im| + 1))] with T hT
    exact key T (by
      rw [abs_of_nonneg (by linarith [neg_abs_le A.im, abs_nonneg A.im])]
      linarith [neg_abs_le A.im, abs_nonneg A.im])

/-- Shifting the Barnes line when no pole `t = (A+n)/2` lies in the closed strip. -/
lemma pcfBC_shift_none {A z : ℂ} (hz0 : z ≠ 0) (hz : |arg z| < 3*π/4) {c₁ c₂ : ℝ}
    (hc : 0 < c₁) (h12 : c₁ < c₂) (hno : ∀ n : ℕ, (A.re + n)/2 ∉ Icc c₁ c₂) :
    (∫ y : ℝ, pcfBC_F A z (c₂ + y*I)) = ∫ y : ℝ, pcfBC_F A z (c₁ + y*I) := by
  have hav : ∀ c ∈ Icc c₁ c₂, ∀ n : ℕ, 2*c ≠ A.re + n := fun c hcI n h =>
    hno n (by rw [show (A.re + n)/2 = c by linarith]; exact hcI)
  obtain ⟨ht, hb⟩ := pcfBC_F_horizontal (A := A) hz0 hz hc h12.le
  refine Complex.barnesRes_vertical_shift_of_differentiableOn h12 (fun t htS => ?_)
    (pcfBC_F_integrable hz0 hz hc (hav c₁ ⟨le_rfl, h12.le⟩))
    (pcfBC_F_integrable hz0 hz (hc.trans h12) (hav c₂ ⟨h12.le, le_rfl⟩)) ht hb
  have htS' : t.re ∈ Icc c₁ c₂ := htS
  refine (pcfBC_F_differentiableAt hz0 (hc.trans_le htS'.1) fun m h => ?_).differentiableWithinAt
  have := congrArg re h; simp at this
  exact hno m (by rw [show (A.re + m)/2 = t.re by linarith]; exact htS')

/-- The residue of the Barnes integrand at `t = (A+n)/2` (with the `-1/2` Jacobian). -/
def pcfBC_res (A z : ℂ) (n : ℕ) : ℂ :=
  (-1)^(n+1)/(2*(n.factorial:ℂ)) * Gamma ((A+n)/2) * 2^((A+n)/2) * z^(A+n)

/-- The removable-singularity form `(t - (A+n)/2) F(t)`. -/
def pcfBC_phi (A z : ℂ) (n : ℕ) (t : ℂ) : ℂ :=
  -(1/2) * Gamma t * Gamma (A - 2*t + n + 1) / (∏ j ∈ Finset.range n, (A - 2*t + j)) *
    2^t * z^(2*t)

lemma pcfBC_phi_pole (A z : ℂ) (n : ℕ) : pcfBC_phi A z n ((A+n)/2) = pcfBC_res A z n := by
  unfold pcfBC_phi pcfBC_res
  have h1 : A - 2*((A+n)/2) + n + 1 = 1 := by ring
  have h2 : ∏ j ∈ Finset.range n, (A - 2*((A+n)/2) + j) = (-1)^n * n.factorial := by
    rw [← Complex.barnesRes_prod_sub_nat]; exact Finset.prod_congr rfl fun j _ => by ring
  have h3 : (2:ℂ)*((A+n)/2) = A + n := by ring
  rw [h1, h2, h3, Gamma_one]
  have hinv : ((-1:ℂ)^n)⁻¹ = (-1)^n := by rw [← inv_pow, inv_neg, inv_one]
  rw [show -(1/2:ℂ) * Gamma ((A+n)/2) * 1 / ((-1)^n * (n.factorial:ℂ)) =
    -(1/2) * Gamma ((A+n)/2) * ((-1)^n)⁻¹ * (n.factorial:ℂ)⁻¹ by rw [div_eq_mul_inv, mul_inv]; ring, hinv]
  ring

/-- `φ(t)/(t - p) = F(t)` away from the pole `p = (A+n)/2` and from the poles of index `< n`. -/
lemma pcfBC_phi_div {A z t : ℂ} {n : ℕ} (ht : t ≠ (A+n)/2)
    (hj : ∀ j : ℕ, j < n → A - 2*t + j ≠ 0) :
    pcfBC_phi A z n t / (t - (A+n)/2) = pcfBC_F A z t := by
  have hn : A - 2*t + n ≠ 0 := fun h => ht (by linear_combination -h/2)
  have hall : ∀ j : ℕ, j ≤ n → A - 2*t + j ≠ 0 := fun j hjn => by
    rcases lt_or_eq_of_le hjn with h | rfl
    · exact hj j h
    · exact hn
  have hG := Complex.barnesRes_Gamma_add_nat_succ (A - 2*t) n hall
  rw [Finset.prod_range_succ] at hG
  have hP : ∏ j ∈ Finset.range n, (A - 2*t + j) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j hj' => hj j (Finset.mem_range.mp hj')
  have hd : t - (A+n)/2 ≠ 0 := sub_ne_zero.mpr ht
  unfold pcfBC_phi pcfBC_F
  rw [hG, show A - 2*t + (n:ℂ) = -2*(t - (A+n)/2) by ring]
  have hd' : 2*t - (A+n) ≠ 0 := fun h => hd (by linear_combination h/2)
  field_simp

lemma pcfBC_phi_differentiableAt {A z t : ℂ} {n : ℕ} (hz : z ≠ 0) (ht : 0 < t.re)
    (hA : ∀ m : ℕ, A - 2*t + n + 1 ≠ -m) (hj : ∀ j : ℕ, j < n → A - 2*t + j ≠ 0) :
    DifferentiableAt ℂ (pcfBC_phi A z n) t := by
  have ht' : ∀ m : ℕ, t ≠ -m := fun m h => by
    rw [h] at ht; simp at ht; linarith [(m.cast_nonneg : (0:ℝ) ≤ m)]
  have hP : ∏ j ∈ Finset.range n, (A - 2*t + j) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j hj' => hj j (Finset.mem_range.mp hj')
  unfold pcfBC_phi
  refine ((((((differentiableAt_const _).mul (differentiableAt_Gamma t ht')).mul
    ((differentiableAt_Gamma _ hA).comp t (by fun_prop))).div
    (by fun_prop) hP)).mul
    (differentiableAt_id.const_cpow (Or.inl two_ne_zero))).mul
    ((differentiableAt_id.const_mul 2).const_cpow (Or.inl hz))

/-- Shifting the Barnes line across exactly one pole `t = (A+n)/2`. -/
lemma pcfBC_shift_one {A z : ℂ} (hz0 : z ≠ 0) (hz : |arg z| < 3*π/4) {c₁ c₂ : ℝ}
    (hc : 0 < c₁) {n : ℕ} (hn₁ : c₁ < (A.re + n)/2) (hn₂ : (A.re + n)/2 < c₂)
    (hno : ∀ m : ℕ, m ≠ n → (A.re + m)/2 ∉ Icc c₁ c₂) :
    (∫ y : ℝ, pcfBC_F A z (c₂ + y*I)) - (∫ y : ℝ, pcfBC_F A z (c₁ + y*I)) =
      2*π*pcfBC_res A z n := by
  have h12 : c₁ < c₂ := hn₁.trans hn₂
  set p : ℂ := (A+n)/2 with hp
  have hpre : p.re = (A.re + n)/2 := by simp [hp]
  have hpim : p.im = A.im/2 := by simp [hp]
  -- poles of index `≠ n` are off the strip
  have hj : ∀ t : ℂ, t.re ∈ Icc c₁ c₂ → ∀ j : ℕ, j < n → A - 2*t + j ≠ 0 := by
    intro t htS j hjn h
    have := congrArg re h; simp at this
    exact hno j hjn.ne (by rw [show (A.re + j)/2 = t.re by linarith]; exact htS)
  have hdiv : ∀ t : ℂ, t.re ∈ Icc c₁ c₂ → t ≠ p → pcfBC_phi A z n t / (t - p) = pcfBC_F A z t :=
    fun t htS htp => pcfBC_phi_div htp (hj t htS)
  have hav : ∀ c ∈ Icc c₁ c₂, c ≠ (A.re + n)/2 → ∀ m : ℕ, 2*c ≠ A.re + m := by
    intro c hcI hcn m h
    by_cases hm : m = n
    · subst hm; exact hcn (by linarith)
    · exact hno m hm (by rw [show (A.re + m)/2 = c by linarith]; exact hcI)
  have hline : ∀ c ∈ Icc c₁ c₂, c ≠ (A.re + n)/2 →
      (fun y : ℝ => pcfBC_phi A z n (c + y*I) / (c + y*I - p)) =
        fun y : ℝ => pcfBC_F A z (c + y*I) := by
    intro c hcI hcn
    funext y
    exact hdiv _ (by simpa using hcI) (fun h => hcn (by
      have := congrArg re h; simp at this; rw [this, hpre]))
  have h1I : c₁ ∈ Icc c₁ c₂ := ⟨le_rfl, h12.le⟩
  have h2I : c₂ ∈ Icc c₁ c₂ := ⟨h12.le, le_rfl⟩
  have hn1 : c₁ ≠ (A.re + n)/2 := hn₁.ne
  have hn2 : c₂ ≠ (A.re + n)/2 := hn₂.ne'
  obtain ⟨ht, hb⟩ := pcfBC_F_horizontal (A := A) hz0 hz hc h12.le
  have hH : ∀ T : ℝ, T ≠ A.im/2 → (∫ x in c₁..c₂, pcfBC_phi A z n (x + T*I) / (x + T*I - p)) =
      ∫ x in c₁..c₂, pcfBC_F A z (x + T*I) := by
    intro T hT
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [uIcc_of_le h12.le] at hx
    exact hdiv _ (by simpa using hx) (fun h => hT (by
      have := congrArg im h; simp at this; rw [this, hpim]))
  have hΦ : DifferentiableOn ℂ (pcfBC_phi A z n) (re ⁻¹' Icc c₁ c₂) := by
    intro t htS
    have htS' : t.re ∈ Icc c₁ c₂ := htS
    refine (pcfBC_phi_differentiableAt hz0 (hc.trans_le htS'.1) (fun m h => ?_)
      (hj t htS')).differentiableWithinAt
    have := congrArg re h; simp at this
    exact hno (n+1+m) (by omega) (by
      rw [show (A.re + ((n+1+m : ℕ) : ℝ))/2 = t.re by push_cast; linarith]; exact htS')
  have key := Complex.barnesRes_vertical_shift (p := p)
    (by rw [hpre]; exact hn₁) (by rw [hpre]; exact hn₂) hΦ
    (by rw [hline c₁ h1I hn1]; exact pcfBC_F_integrable hz0 hz hc (hav c₁ h1I hn1))
    (by rw [hline c₂ h2I hn2]; exact pcfBC_F_integrable hz0 hz (hc.trans h12) (hav c₂ h2I hn2))
    (ht.congr' (by
      filter_upwards [eventually_gt_atTop (A.im/2)] with T hT
      exact (hH T hT.ne').symm))
    (hb.congr' (by
      filter_upwards [eventually_lt_atBot (A.im/2)] with T hT
      exact (hH T hT.ne).symm))
  rw [hline c₁ h1I hn1, hline c₂ h2I hn2, hp, pcfBC_phi_pole] at key
  exact key

/-- The number of poles `t = (A+n)/2` to the left of the line `Re t = c`. -/
def pcfBC_N (A : ℂ) (c : ℝ) : ℕ := (⌈2*c - A.re⌉).toNat

lemma pcfBC_lt_N {A : ℂ} {c : ℝ} {n : ℕ} : n < pcfBC_N A c ↔ (A.re + n)/2 < c := by
  unfold pcfBC_N
  rw [Int.lt_toNat, Int.lt_ceil]
  push_cast
  constructor <;> intro h <;> linarith

lemma pcfBC_N_mono {A : ℂ} {c₁ c₂ : ℝ} (h : c₁ ≤ c₂) : pcfBC_N A c₁ ≤ pcfBC_N A c₂ := by
  unfold pcfBC_N
  exact Int.toNat_le_toNat (Int.ceil_mono (by linarith))

/-- Moving the Barnes line from `c₁` to `c₂` picks up the residues of the crossed poles. -/
lemma pcfBC_shift {A z : ℂ} (hz0 : z ≠ 0) (hz : |arg z| < 3*π/4) {c₁ c₂ : ℝ}
    (hc : 0 < c₁) (h12 : c₁ ≤ c₂) (hav₁ : ∀ n : ℕ, 2*c₁ ≠ A.re + n)
    (hav₂ : ∀ n : ℕ, 2*c₂ ≠ A.re + n) :
    (∫ y : ℝ, pcfBC_F A z (c₂ + y*I)) - 2*π*∑ n ∈ Finset.range (pcfBC_N A c₂), pcfBC_res A z n =
      (∫ y : ℝ, pcfBC_F A z (c₁ + y*I)) -
        2*π*∑ n ∈ Finset.range (pcfBC_N A c₁), pcfBC_res A z n := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (pcfBC_N_mono (A := A) h12)
  induction k generalizing c₁ with
  | zero =>
    rcases eq_or_lt_of_le h12 with h | h
    · subst h; rfl
    rw [add_zero] at hk
    rw [hk, pcfBC_shift_none hz0 hz hc h (fun n hn => ?_)]
    have h1 : (A.re + n)/2 ≠ c₁ := fun h' => hav₁ n (by linarith)
    have h2 : (A.re + n)/2 ≠ c₂ := fun h' => hav₂ n (by linarith)
    have hlt2 : n < pcfBC_N A c₂ := pcfBC_lt_N.mpr (lt_of_le_of_ne hn.2 h2)
    have hlt1 : ¬ n < pcfBC_N A c₁ := fun h' => by
      have := pcfBC_lt_N.mp h'; linarith [hn.1]
    rw [hk] at hlt2; exact hlt1 hlt2
  | succ k ih =>
    set n₀ := pcfBC_N A c₁ with hn₀
    have hp1 : c₁ < (A.re + n₀)/2 := by
      have h1 : ¬ n₀ < pcfBC_N A c₁ := lt_irrefl _
      rw [pcfBC_lt_N] at h1
      exact lt_of_le_of_ne (not_lt.mp h1) (fun h' => hav₁ n₀ (by linarith))
    have hp2 : (A.re + n₀)/2 < c₂ := pcfBC_lt_N.mp (by omega)
    -- poles of index `< n₀` are left of `c₁`
    have hleft : ∀ m : ℕ, m < n₀ → (A.re + m)/2 < c₁ := fun m hm => pcfBC_lt_N.mp hm
    by_cases hk0 : k = 0
    · subst hk0
      have hsh := pcfBC_shift_one hz0 hz hc hp1 hp2 (n := n₀) (fun m hm hmI => by
        have h1 : (A.re + m)/2 ≠ c₂ := fun h' => hav₂ m (by linarith)
        have hlt2 : m < pcfBC_N A c₂ := pcfBC_lt_N.mpr (lt_of_le_of_ne hmI.2 h1)
        rcases lt_or_gt_of_ne hm with h' | h'
        · linarith [hleft m h', hmI.1]
        · omega)
      rw [hk, Finset.sum_range_succ]
      linear_combination hsh
    · set c' : ℝ := (A.re + n₀)/2 + 1/4 with hc'
      have hNc' : pcfBC_N A c' = n₀ + 1 := by
        apply le_antisymm
        · by_contra h'
          have := pcfBC_lt_N.mp (show n₀ + 1 < pcfBC_N A c' by omega)
          push_cast at this; linarith
        · exact pcfBC_lt_N.mpr (by linarith)
      have hc'2 : c' ≤ c₂ := by
        have := pcfBC_lt_N.mp (show n₀ + 1 < pcfBC_N A c₂ by omega)
        push_cast at this; linarith
      have hav' : ∀ n : ℕ, 2*c' ≠ A.re + n := by
        intro n h'
        have h2 : (n:ℝ) = n₀ + 1/2 := by linarith
        have h3 : (n:ℝ) ≤ n₀ ∨ (n₀:ℝ) + 1 ≤ n := by
          rcases le_or_gt n n₀ with h4 | h4
          · left; exact_mod_cast h4
          · right; exact_mod_cast h4
        rcases h3 with h3 | h3 <;> linarith
      have hsh := pcfBC_shift_one hz0 hz hc hp1 (show (A.re + n₀)/2 < c' by linarith)
        (n := n₀) (fun m hm hmI => by
          rcases lt_or_gt_of_ne hm with h' | h'
          · linarith [hleft m h', hmI.1]
          · have : (n₀:ℝ) + 1 ≤ m := by exact_mod_cast h'
            linarith [hmI.2])
      have hih := ih (c₁ := c') (by linarith) hc'2 hav' (by rw [hNc']; omega)
      rw [hih, hNc', Finset.sum_range_succ]
      linear_combination hsh

/-- DLMF 12.5.8 with crossed residues, in the regime `Re A > 0` (shift from a small line). -/
lemma pcfBC_U_pos {a z : ℂ} (hz0 : z ≠ 0) (hz : |arg z| < 3*π/4) {c : ℝ} (hc : 0 < c)
    (hav : ∀ n : ℕ, 2*c ≠ (1/2+1*a).re + n) (hA : 0 < (1/2+1*a).re) :
    (∫ y : ℝ, pcfBC_F (1/2+1*a) z (c + y*I)) =
      2*π*(Gamma (1/2+1*a)*(exp (z^2/4)*z^(a+1/2))*pcfU a z +
        ∑ n ∈ Finset.range (pcfBC_N (1/2+1*a) c), pcfBC_res (1/2+1*a) z n) := by
  set A : ℂ := 1/2+1*a with hAdef
  set c₀ : ℝ := min c (A.re/2) / 2 with hc₀
  have hm1 := min_le_left c (A.re/2)
  have hm2 := min_le_right c (A.re/2)
  have hm0 : 0 < min c (A.re/2) := lt_min hc (by linarith)
  have hc₀0 : 0 < c₀ := by simp only [hc₀]; linarith
  have hc₀c : c₀ ≤ c := by simp only [hc₀]; linarith
  have hc₀A : 2*c₀ < A.re := by simp only [hc₀]; linarith
  have hav₀ : ∀ n : ℕ, 2*c₀ ≠ A.re + n := fun n h => by
    linarith [(n.cast_nonneg : (0:ℝ) ≤ n)]
  have hN₀ : pcfBC_N A c₀ = 0 := by
    by_contra h
    have := pcfBC_lt_N.mp (show 0 < pcfBC_N A c₀ by omega)
    push_cast at this; linarith
  have hsh := pcfBC_shift hz0 hz hc₀0 hc₀c hav₀ hav
  rw [hN₀, Finset.range_zero, Finset.sum_empty, mul_zero, sub_zero] at hsh
  have hB : (∫ y : ℝ, pcfBC_F A z (c₀ + y*I)) = ∫ y, pcfInt_B a z c₀ y := by
    simp only [hAdef, pcfBC_F_eq_B]
  have hca : 2*c₀ < 1/2 + a.re := by simpa [hAdef] using hc₀A
  rw [hB, pcfInt_B_integral a hz0 hz hc₀0 hca] at hsh
  linear_combination hsh

/-- The line integral minus the crossed residues; independent of the line. -/
def pcfBC_J (A z : ℂ) (c : ℝ) : ℂ :=
  (∫ y : ℝ, pcfBC_F A z (c + y*I)) - 2*π*∑ n ∈ Finset.range (pcfBC_N A c), pcfBC_res A z n

lemma pcfBC_J_eq {A z : ℂ} (hz0 : z ≠ 0) (hz : |arg z| < 3*π/4) {c₁ c₂ : ℝ}
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hav₁ : ∀ n : ℕ, 2*c₁ ≠ A.re + n)
    (hav₂ : ∀ n : ℕ, 2*c₂ ≠ A.re + n) : pcfBC_J A z c₁ = pcfBC_J A z c₂ := by
  rcases le_total c₁ c₂ with h | h
  · exact (pcfBC_shift hz0 hz hc₁ h hav₁ hav₂).symm
  · exact pcfBC_shift hz0 hz hc₂ h hav₂ hav₁

/-- A canonical admissible line, at distance `1/4` from the poles (in `2 Re t`). -/
def pcfBC_cg (A : ℂ) : ℝ := (Int.fract A.re + 1/2)/2

lemma pcfBC_cg_pos (A : ℂ) : 0 < pcfBC_cg A := by
  unfold pcfBC_cg; linarith [Int.fract_nonneg A.re]

lemma pcfBC_two_cg (A : ℂ) : 2*pcfBC_cg A - A.re = 1/2 - ⌊A.re⌋ := by
  unfold pcfBC_cg; rw [← Int.self_sub_floor]; ring

/-- No integer lies within `1/4` of `1/2 - m`. -/
lemma pcfBC_not_int {m : ℤ} {h : ℝ} (h1 : 1/4 - (m:ℝ) < h) (h2 : h < 3/4 - m) (n : ℤ) :
    h ≠ n := by
  intro he
  rw [he] at h1 h2
  rcases le_or_gt (n + m) 0 with h3 | h3
  · have : ((n + m : ℤ) : ℝ) ≤ 0 := by exact_mod_cast h3
    push_cast at this; linarith
  · have : (1:ℝ) ≤ ((n + m : ℤ) : ℝ) := by exact_mod_cast h3
    push_cast at this; linarith

lemma pcfBC_avoid_near {A₀ A : ℂ} (hA : |A.re - A₀.re| < 1/4) (n : ℕ) :
    2*pcfBC_cg A₀ ≠ A.re + n := by
  have h0 := pcfBC_two_cg A₀
  have habs := abs_lt.mp hA
  intro h
  exact pcfBC_not_int (m := ⌊A₀.re⌋) (h := 2*pcfBC_cg A₀ - A.re) (by linarith) (by linarith) n
    (by push_cast; linarith)

lemma pcfBC_N_near {A₀ A : ℂ} (hA : |A.re - A₀.re| < 1/4) :
    pcfBC_N A (pcfBC_cg A₀) = pcfBC_N A₀ (pcfBC_cg A₀) := by
  have h0 := pcfBC_two_cg A₀
  have habs := abs_lt.mp hA
  unfold pcfBC_N
  have e1 : ⌈2*pcfBC_cg A₀ - A.re⌉ = 1 - ⌊A₀.re⌋ := by
    rw [Int.ceil_eq_iff]; push_cast; constructor <;> linarith
  have e2 : ⌈2*pcfBC_cg A₀ - A₀.re⌉ = 1 - ⌊A₀.re⌋ := by
    rw [Int.ceil_eq_iff]; push_cast; constructor <;> linarith
  rw [e1, e2]

/-- A uniform lower bound for `|sin(π x)|` within `1/4` of a half-integer. -/
lemma pcfBC_sin_lower (m : ℤ) : ∃ δ : ℝ, 0 < δ ∧
    ∀ x ∈ Icc ((m:ℝ) - 3/4) (m - 1/4), δ ≤ |Real.sin (π*x)| := by
  obtain ⟨x₁, hx₁, hmin⟩ := (isCompact_Icc (a := (m:ℝ) - 3/4) (b := m - 1/4)).exists_isMinOn
    (nonempty_Icc.mpr (by linarith)) ((Real.continuous_sin.comp (continuous_const.mul
      continuous_id)).abs.continuousOn)
  refine ⟨|Real.sin (π*x₁)|, abs_pos.mpr fun h => ?_, fun x hx => hmin hx⟩
  obtain ⟨k, hk⟩ := Real.sin_eq_zero_iff.mp h
  have hxk : x₁ = k := by
    have := Real.pi_pos
    have h2 : ((k:ℝ) - x₁) * π = 0 := by linarith
    rcases mul_eq_zero.mp h2 with h3 | h3 <;> linarith
  rw [hxk] at hx₁
  rcases le_or_gt (k - m) (-1) with h3 | h3
  · have : ((k - m : ℤ) : ℝ) ≤ -1 := by exact_mod_cast h3
    push_cast at this; linarith [hx₁.1]
  · have : (0:ℝ) ≤ ((k - m : ℤ) : ℝ) := by exact_mod_cast (show (0:ℤ) ≤ k - m by omega)
    push_cast at this; linarith [hx₁.2]

/-- On a fixed admissible line the Barnes integral is holomorphic in `A` near `A₀`. -/
lemma pcfBC_integral_differentiableOn {z : ℂ} (hz0 : z ≠ 0) (hz : |arg z| < 3*π/4) (A₀ : ℂ) :
    DifferentiableOn ℂ (fun A => ∫ y : ℝ, pcfBC_F A z (pcfBC_cg A₀ + y*I))
      (Metric.ball A₀ (1/4)) := by
  set c₀ := pcfBC_cg A₀ with hc₀
  have hc0 : 0 < c₀ := pcfBC_cg_pos A₀
  have h0 := pcfBC_two_cg A₀
  set m : ℤ := ⌊A₀.re⌋
  have hre : ∀ A ∈ Metric.ball A₀ (1/4), |A.re - A₀.re| < 1/4 := fun A hA => by
    have := abs_re_le_norm (A - A₀)
    rw [Metric.mem_ball, dist_eq_norm] at hA
    simp only [sub_re] at this; linarith
  have him : ∀ A ∈ Metric.ball A₀ (1/4), |A.im| ≤ |A₀.im| + 1/4 := fun A hA => by
    have := abs_im_le_norm (A - A₀)
    rw [Metric.mem_ball, dist_eq_norm] at hA
    simp only [sub_im] at this
    have := abs_sub_abs_le_abs_sub A.im A₀.im; linarith
  have hav : ∀ A ∈ Metric.ball A₀ (1/4), ∀ n : ℕ, 2*c₀ ≠ A.re + n := fun A hA =>
    pcfBC_avoid_near (hre A hA)
  obtain ⟨C1, K1, g1⟩ := DLMF.Gamma.exists_norm_Gamma_le hc0
  have hC1 : 0 ≤ C1 := (norm_nonneg _).trans (by simpa using g1 0)
  obtain ⟨C2, K2, hC2, g2⟩ := pcfBC_Gamma_bound (|(m:ℝ)| + 1)
  obtain ⟨δ, hδ, hδx⟩ := pcfBC_sin_lower m
  set M : ℝ := |A₀.im| + 1/4
  set b : ℝ := 3*π/2 - 2*|arg z|
  have hb : 0 < b := by simp only [b]; linarith
  set K0 : ℝ := C1 * (C2/δ) * (2*(1+M))^K2 * Real.exp (π*M/2) * (2:ℝ)^c₀ * ‖z‖^(2*c₀)
  have hbound : ∀ A ∈ Metric.ball A₀ (1/4), ∀ y : ℝ,
      ‖pcfBC_F A z (c₀ + y*I)‖ ≤ K0 * ((1+|y|)^(K1+K2) * Real.exp (-(b*|y|))) := by
    intro A hA y
    have hr := abs_lt.mp (hre A hA)
    have hxI : A.re - 2*c₀ ∈ Icc ((m:ℝ) - 3/4) (m - 1/4) := by
      constructor <;> linarith
    have hxX : A.re - 2*c₀ ∈ Icc (-(|(m:ℝ)| + 1)) (|(m:ℝ)| + 1) := by
      have := le_abs_self (m:ℝ); have := neg_abs_le (m:ℝ)
      constructor <;> linarith [hxI.1, hxI.2]
    have hs := hδx _ hxI
    have hG2 : ‖Gamma ((A.re - 2*c₀ : ℝ) + I*(A.im - 2*y : ℝ))‖ ≤
        C2/δ * (1+|A.im - 2*y|)^K2 * Real.exp (-(π*|A.im - 2*y|)/2) := by
      have h := (g2 _ hxX (A.im - 2*y)).1
      have h' : ‖Gamma ((A.re - 2*c₀ : ℝ) + I*(A.im - 2*y : ℝ))‖ * δ ≤
          C2 * (1+|A.im - 2*y|)^K2 * Real.exp (-(π*|A.im - 2*y|)/2) :=
        le_trans (mul_le_mul_of_nonneg_left hs (norm_nonneg _)) h
      rw [← le_div_iff₀ hδ] at h'
      exact h'.trans (le_of_eq (by ring))
    refine (pcfBC_norm_F_le hz0 c₀ y hC1 (by positivity) (g1 y) hG2).trans ?_
    have hAim := him A hA
    simp only [K0, b]
    gcongr
  have hdiff : ∀ y : ℝ, DifferentiableOn ℂ (fun A => pcfBC_F A z (c₀ + y*I))
      (Metric.ball A₀ (1/4)) := fun y A hA =>
    (pcfBC_F_differentiableAt_param (pcfBC_ne_pole (hav A hA) y)).differentiableWithinAt
  refine Complex.differentiableOn_integral_of_locally_dominated Metric.isOpen_ball
    (fun A hA => (pcfBC_F_continuous hz0 hc0 (hav A hA)).aestronglyMeasurable)
    (Eventually.of_forall hdiff) (fun A hA => ⟨_, Metric.isOpen_ball.mem_nhds hA,
      fun y => K0 * ((1+|y|)^(K1+K2) * Real.exp (-(b*|y|))),
      (DLMF.Gamma.integrable_one_add_abs_pow_mul_exp_neg hb _).const_mul _,
      Eventually.of_forall fun y A' hA' => hbound A' hA' y⟩)

lemma pcfBC_res_differentiableAt {z : ℂ} (hz0 : z ≠ 0) {a₀ : ℂ}
    (ha : ∀ n : ℕ, a₀ ≠ -1/2 - n) (n : ℕ) :
    DifferentiableAt ℂ (fun a => pcfBC_res (1/2+1*a) z n) a₀ := by
  have hG : ∀ m : ℕ, (1/2+1*a₀+n)/2 ≠ -m := fun m h =>
    ha (n + 2*m) (by push_cast; linear_combination 2*h)
  unfold pcfBC_res
  refine (((differentiableAt_const _).mul ((differentiableAt_Gamma _ hG).comp a₀
    (by fun_prop))).mul ?_).mul ?_
  · exact (DifferentiableAt.const_cpow (by fun_prop) (Or.inl two_ne_zero))
  · exact (DifferentiableAt.const_cpow (by fun_prop) (Or.inl hz0))

/-- The canonical-line value `G(a)` of the residue-corrected Barnes integral. -/
def pcfBC_G (z a : ℂ) : ℂ := pcfBC_J (1/2+1*a) z (pcfBC_cg (1/2+1*a))

lemma pcfBC_G_eq_J {z : ℂ} (hz0 : z ≠ 0) (hz : |arg z| < 3*π/4) (a : ℂ) {c : ℝ} (hc : 0 < c)
    (hav : ∀ n : ℕ, 2*c ≠ (1/2+1*a).re + n) : pcfBC_J (1/2+1*a) z c = pcfBC_G z a :=
  pcfBC_J_eq hz0 hz hc (pcfBC_cg_pos _) hav (pcfBC_avoid_near (by simp))

lemma pcfBC_G_differentiableAt {z : ℂ} (hz0 : z ≠ 0) (hz : |arg z| < 3*π/4) {a₀ : ℂ}
    (ha : ∀ n : ℕ, a₀ ≠ -1/2 - n) : DifferentiableAt ℂ (pcfBC_G z) a₀ := by
  set A₀ : ℂ := 1/2+1*a₀
  set c₀ := pcfBC_cg A₀
  set H : ℂ → ℂ := fun a => (∫ y : ℝ, pcfBC_F (1/2+1*a) z (c₀ + y*I)) -
    2*π*∑ n ∈ Finset.range (pcfBC_N A₀ c₀), pcfBC_res (1/2+1*a) z n
  have hball : ∀ a ∈ Metric.ball a₀ (1/4), (1/2+1*a) ∈ Metric.ball A₀ (1/4) := fun a ha' => by
    rw [Metric.mem_ball, dist_eq_norm] at ha' ⊢
    simpa [A₀, show 1/2+1*a-(1/2+1*a₀) = a - a₀ by ring] using ha'
  have hre : ∀ a ∈ Metric.ball a₀ (1/4), |(1/2+1*a).re - A₀.re| < 1/4 := fun a ha' => by
    have h := hball a ha'
    rw [Metric.mem_ball, dist_eq_norm] at h
    have := abs_re_le_norm ((1/2+1*a) - A₀)
    simp only [sub_re] at this; linarith
  have heq : pcfBC_G z =ᶠ[𝓝 a₀] H := by
    filter_upwards [Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (by norm_num : (0:ℝ) < 1/4))]
      with a ha'
    rw [← pcfBC_G_eq_J hz0 hz a (pcfBC_cg_pos A₀) (pcfBC_avoid_near (hre a ha'))]
    simp only [pcfBC_J, H, c₀, pcfBC_N_near (hre a ha')]
  refine DifferentiableAt.congr_of_eventuallyEq ?_ heq
  refine DifferentiableAt.sub ?_ ((DifferentiableAt.fun_sum fun n _ =>
    pcfBC_res_differentiableAt hz0 ha n).const_mul _)
  have hI := (pcfBC_integral_differentiableOn hz0 hz A₀).differentiableAt
    (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (by norm_num)))
  exact hI.comp (f := fun a : ℂ => 1/2+1*a) a₀ (by fun_prop)

/-- **DLMF 12.5.8 for all regular parameters**: line integral = 2π (value + crossed residues). -/
lemma pcfBC_U_integral {a z : ℂ} (ha : ∀ n : ℕ, a ≠ -1/2 - n) (hz0 : z ≠ 0)
    (hz : |arg z| < 3*π/4) {c : ℝ} (hc : 0 < c) (hav : ∀ n : ℕ, 2*c ≠ (1/2+1*a).re + n) :
    (∫ y : ℝ, pcfBC_F (1/2+1*a) z (c + y*I)) =
      2*π*(Gamma (1/2+1*a)*(exp (z^2/4)*z^(a+1/2))*pcfU a z +
        ∑ n ∈ Finset.range (pcfBC_N (1/2+1*a) c), pcfBC_res (1/2+1*a) z n) := by
  set D : Set ℂ := {a : ℂ | ∀ n : ℕ, a ≠ -1/2 - n}
  have hD : IsOpen D := Complex.barnesRes_isOpen_ne_sub_nat (-1/2)
  set W : ℂ → ℂ := fun a => 2*π*(Gamma (1/2+1*a)*(exp (z^2/4)*z^(a+1/2))*pcfU a z)
  have hGa : AnalyticOnNhd ℂ (pcfBC_G z) D := DifferentiableOn.analyticOnNhd
    (fun a ha' => (pcfBC_G_differentiableAt hz0 hz ha').differentiableWithinAt) hD
  have hWa : AnalyticOnNhd ℂ W D := by
    refine DifferentiableOn.analyticOnNhd (fun a ha' => ?_) hD
    have hG : ∀ m : ℕ, 1/2+1*a ≠ -m := fun m h => ha' m (by linear_combination h)
    refine DifferentiableAt.differentiableWithinAt ?_
    exact (differentiableAt_const _).mul ((((differentiableAt_Gamma _ hG).comp a
      (by fun_prop)).mul ((differentiableAt_const _).mul (DifferentiableAt.const_cpow
        (by fun_prop) (Or.inl hz0)))).mul (pcfU_entire_order z a))
  have hpos : ∀ a : ℂ, 0 < (1/2+1*a).re → pcfBC_G z a = W a := by
    intro a hA
    have := pcfBC_U_pos (a := a) hz0 hz (pcfBC_cg_pos _)
      (pcfBC_avoid_near (A₀ := 1/2+1*a) (by simp)) hA
    simp only [pcfBC_G, pcfBC_J, W]
    rw [this]; ring
  have hhalf : (1/2 : ℂ) ∈ D := fun n h => by
    have := congrArg re h; simp at this; linarith [(n.cast_nonneg : (0:ℝ) ≤ n)]
  have hev : pcfBC_G z =ᶠ[𝓝 (1/2)] W := by
    have ho : IsOpen {a : ℂ | 0 < (1/2+1*a).re} :=
      isOpen_lt continuous_const (by fun_prop)
    filter_upwards [ho.mem_nhds (by norm_num)] with a ha'
    exact hpos a ha'
  have hEq := hGa.eqOn_of_preconnected_of_eventuallyEq hWa
    (Complex.barnesRes_isPreconnected_ne_sub_nat (-1/2)) hhalf hev ha
  have hJ := pcfBC_G_eq_J hz0 hz a hc hav
  simp only [pcfBC_J] at hJ
  rw [hEq] at hJ
  simp only [W] at hJ
  linear_combination hJ

lemma pcfBC_sum_false (a z : ℂ) (c : ℝ) : pcfBarnesResidueSum false a z c =
    ∑ n ∈ Finset.range (pcfBC_N (1/2+1*a) c), pcfBC_res (1/2+1*a) z n := by
  simp only [pcfBarnesResidueSum, pcfBarnesResidue, pcfBC_N, pcfBC_res, Bool.false_eq_true,
    ite_false, mul_one]
  rw [show (1/2:ℂ)+1*a = a+1/2 by ring]

lemma pcfBC_sum_true (a z : ℂ) (c : ℝ) : pcfBarnesResidueSum true a z c =
    ∑ n ∈ Finset.range (pcfBC_N (1/2+1*(-a)) c), pcfBarnesResidue true a z n := by
  simp only [pcfBarnesResidueSum, pcfBC_N, ite_true]
  rw [show (1/2:ℂ)+1*(-a) = 1/2-a by ring]

lemma pcfBC_res_true {a z : ℂ} (hz0 : z ≠ 0) (hz : |arg z| < π/2) (n : ℕ) :
    pcfBC_res (1/2+1*(-a)) (I*z) n + pcfBC_res (1/2+1*(-a)) (-I*z) n =
      2 * pcfBarnesResidue true a z n := by
  obtain ⟨e1, e2⟩ := pcfInt_I_mul_cpow hz0 hz ((1/2+1*(-a)) + n)
  simp only [pcfBC_res, pcfBarnesResidue, ite_true]
  rw [e1, e2, show (1/2:ℂ)+1*(-a) = 1/2-a by ring, Complex.cos]
  have q1 : exp (π/2*I*((1/2-a)+n)) = exp (π*((1/2-a+n)/2)*I) := by congr 1; ring
  have q2 : exp (-(π/2)*I*((1/2-a)+n)) = exp (-(π*((1/2-a+n)/2))*I) := by congr 1; ring
  rw [q1, q2]; ring

/-- All regular parameters: crossed residues encode the deformed separating contour instead of strengthening the real-part hypothesis. -/
@[dlmf 12.5.E8]
theorem pcfU_barnes_continued {a z : ℂ} (ha : ∀ n : ℕ, 1*a ≠ -n-1/2) (hz0 : z ≠ 0) (hz : |arg z| < 3*π/4) {c : ℝ} (hc : 0 < c) (havoid : ∀ n : ℕ, 2*c ≠ 1/2+1*a.re+n) :
    HasIntegralWholeLine (fun y : ℝ => let t : ℂ := c+y*I; Gamma t*Gamma (1/2+1*a-2*t)*2^t*z^(2*t)*1) (2*π*(Gamma (1/2+1*a)*(exp (z^2/4)*z^(a+1/2))*pcfU a z+pcfBarnesResidueSum false a z c)) := by
  have ha' : ∀ n : ℕ, a ≠ -1/2 - n := fun n h => ha n (by rw [h]; ring)
  have hav : ∀ n : ℕ, 2*c ≠ (1/2+1*a).re + n := fun n h => havoid n (by simp at h ⊢; linarith)
  have hfun : (fun y : ℝ => let t : ℂ := c+y*I; Gamma t*Gamma (1/2+1*a-2*t)*2^t*z^(2*t)*1) =
      fun y : ℝ => pcfBC_F (1/2+1*a) z (c + y*I) := by
    funext y; simp only [pcfBC_F, mul_one]
  rw [hfun, pcfBC_sum_false, ← pcfBC_U_integral ha' hz0 hz hc hav]
  exact pcfInt_hasIntegralWholeLine (pcfBC_F_integrable hz0 hz hc hav)

/-- All regular parameters: crossed residues encode the deformed separating contour instead of strengthening the real-part hypothesis. -/
@[dlmf 12.5.E9]
theorem pcfV_barnes_continued {a z : ℂ} (ha : ∀ n : ℕ, -1*a ≠ -n-1/2) (hz0 : z ≠ 0) (hz : |arg z| < π/4) {c : ℝ} (hc : 0 < c) (havoid : ∀ n : ℕ, 2*c ≠ 1/2+-1*a.re+n) :
    HasIntegralWholeLine (fun y : ℝ => let t : ℂ := c+y*I; Gamma t*Gamma (1/2+-1*a-2*t)*2^t*z^(2*t)*cos (π*t)) (2*π*(Gamma (1/2+-1*a)*((Real.sqrt (π/2):ℂ)*exp (-z^2/4)*z^(-a+1/2))*pcfV a z+pcfBarnesResidueSum true a z c)) := by
  have ha' : ∀ n : ℕ, -a ≠ -1/2 - n := fun n h => ha n (by rw [neg_one_mul, h]; ring)
  have hav : ∀ n : ℕ, 2*c ≠ (1/2+1*(-a)).re + n := fun n h => havoid n (by simp at h ⊢; linarith)
  have hz2 : |arg z| < π/2 := by linarith [Real.pi_pos]
  obtain ⟨ha1, ha2⟩ := pcfInt_arg_I_mul hz0 hz2
  have hp0 : I*z ≠ 0 := mul_ne_zero I_ne_zero hz0
  have hm0 : -I*z ≠ 0 := mul_ne_zero (neg_ne_zero.mpr I_ne_zero) hz0
  have hpa : |arg (I*z)| < 3*π/4 := by
    rw [ha1]; obtain ⟨h1, h2⟩ := abs_lt.mp hz; rw [abs_lt]; constructor <;> linarith
  have hma : |arg (-I*z)| < 3*π/4 := by
    rw [ha2]; obtain ⟨h1, h2⟩ := abs_lt.mp hz; rw [abs_lt]; constructor <;> linarith
  have hfun : (fun y : ℝ => let t : ℂ := c+y*I; Gamma t*Gamma (1/2+-1*a-2*t)*2^t*z^(2*t)*cos (π*t)) =
      fun y : ℝ => (pcfBC_F (1/2+1*(-a)) (I*z) (c + y*I) + pcfBC_F (1/2+1*(-a)) (-I*z) (c + y*I))/2 := by
    funext y
    rw [pcfBC_F_eq_B, pcfBC_F_eq_B]
    simp only [pcfInt_B]
    obtain ⟨e1, e2⟩ := pcfInt_I_mul_cpow hz0 hz2 (2*((c:ℂ)+y*I))
    rw [e1, e2, show (1/2:ℂ)+1*(-a) = 1/2+-1*a by ring, Complex.cos]
    have q1 : exp (π/2*I*(2*((c:ℂ)+y*I))) = exp (π*((c:ℂ)+y*I)*I) := by congr 1; ring
    have q2 : exp (-(π/2)*I*(2*((c:ℂ)+y*I))) = exp (-(π*((c:ℂ)+y*I))*I) := by congr 1; ring
    rw [q1, q2]; ring
  have i1 := pcfBC_F_integrable hp0 hpa hc hav
  have i2 := pcfBC_F_integrable hm0 hma hc hav
  rw [hfun]
  suffices hI : ∫ y : ℝ, (pcfBC_F (1/2+1*(-a)) (I*z) (c + y*I) + pcfBC_F (1/2+1*(-a)) (-I*z) (c + y*I))/2 =
      2*π*(Gamma (1/2+-1*a)*((Real.sqrt (π/2):ℂ)*exp (-z^2/4)*z^(-a+1/2))*pcfV a z+pcfBarnesResidueSum true a z c) by
    rw [← hI]; exact pcfInt_hasIntegralWholeLine ((i1.add i2).div_const 2)
  rw [integral_div, integral_add i1 i2, pcfBC_U_integral ha' hp0 hpa hc hav,
    pcfBC_U_integral ha' hm0 hma hc hav, pcfBC_sum_true]
  have hR : ∑ n ∈ Finset.range (pcfBC_N (1/2+1*(-a)) c), pcfBC_res (1/2+1*(-a)) (I*z) n +
      ∑ n ∈ Finset.range (pcfBC_N (1/2+1*(-a)) c), pcfBC_res (1/2+1*(-a)) (-I*z) n =
      2 * ∑ n ∈ Finset.range (pcfBC_N (1/2+1*(-a)) c), pcfBarnesResidue true a z n := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl fun n _ => pcfBC_res_true hz0 hz2 n
  have hM : Gamma (1/2+1*(-a))*(exp ((I*z)^2/4)*(I*z)^(-a+1/2))*pcfU (-a) (I*z) +
      Gamma (1/2+1*(-a))*(exp ((-I*z)^2/4)*(-I*z)^(-a+1/2))*pcfU (-a) (-I*z) =
      2*(Gamma (1/2+-1*a)*((Real.sqrt (π/2):ℂ)*exp (-z^2/4)*z^(-a+1/2))*pcfV a z) := by
    have hV1 := pcfV_eq_mul_I a z
    have hV2 := pcfV_eq_mul_neg_I a z
    obtain ⟨f1, f2⟩ := pcfInt_I_mul_cpow hz0 hz2 (-a+1/2)
    rw [f1, f2, show (I*z)^2 = -z^2 by rw [mul_pow, I_sq]; ring,
      show (-I*z)^2 = -z^2 by rw [mul_pow, neg_sq, I_sq]; ring,
      show (1/2:ℂ)+1*(-a) = 1/2+-1*a by ring]
    have hs : (Real.sqrt (π/2):ℂ) * (Real.sqrt (2/π):ℂ) = 1 := by
      rw [← ofReal_mul, ← Real.sqrt_mul (by positivity), show π/2*(2/π) = 1 by field_simp]; simp
    have hq1 : exp (π/2*I*(-a+1/2)) = exp (-I*π*(a/2-1/4)) := by congr 1; ring
    have hq2 : exp (-(π/2)*I*(-a+1/2)) = exp (I*π*(a/2-1/4)) := by congr 1; ring
    rw [hq1, hq2]
    have hsum : 2 * pcfV a z = (Real.sqrt (2/π):ℂ) * (exp (-I*π*(a/2-1/4)) * pcfU (-a) (I*z) +
        exp (I*π*(a/2-1/4)) * pcfU (-a) (-I*z)) := by
      linear_combination hV1 + hV2
    linear_combination (-(Gamma (1/2+-1*a) * exp (-z^2/4) * z^(-a+1/2) * (Real.sqrt (π/2):ℂ))) * hsum -
      (Gamma (1/2+-1*a) * exp (-z^2/4) * z^(-a+1/2) * (exp (-I*π*(a/2-1/4)) * pcfU (-a) (I*z) +
        exp (I*π*(a/2-1/4)) * pcfU (-a) (-I*z))) * hs
  linear_combination π * hM + π * hR

end DLMF.Confluent
