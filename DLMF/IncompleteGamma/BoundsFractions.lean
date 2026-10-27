/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.IncompleteGamma.RealIntegrals
public import DLMF.IncompleteGamma.FractionTools
public import DLMF.IncompleteGamma.BoundTools

/-!
# Continued fractions and inequalities, DLMF §§8.9–8.10

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
New theorem statements are initially admitted and are not completed proofs.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF
open scoped Real Topology Nat
namespace DLMF.Confluent

open DLMF.Statistical

/-- scIncGamma continuedFraction. -/
@[dlmf 8.9.E1]
theorem scIncGamma_continuedFraction {a : ℂ} (ha : ∀ n : ℕ, a ≠ -(n+1)) (z : ℂ) :
    HasContinuedFraction (fun k => if k=0 then 1 else if Odd k then -(if k=1 then 1 else ((k-1 : ℕ)/2 : ℂ)+a)*z else ((k : ℕ)/2 : ℂ)*z) (fun k => if k=0 then 1 else a+k) (Gamma (a+1)*exp z*scIncGamma a z) := by
  have hc : ∀ k : ℕ, a + 1 ≠ -k := fun k h => ha k (by linear_combination h)
  have hval : Gamma (a + 1) * exp z * scIncGamma a z = kummerM 1 (a + 1) z := by
    rw [scIncGamma, kummerM_eq_mul_regularizedHGFun hc,
      show Gamma (a + 1) * exp z * (exp (-z) * regularizedHGFun {1} {a + 1} z) =
        Gamma (a + 1) * regularizedHGFun {1} {a + 1} z * (exp z * exp (-z)) by ring,
      ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, mul_one]
  rw [hval]
  set A : ℕ → ℂ := (fun k => if k=0 then 1 else if Odd k then -(if k=1 then 1 else ((k-1 : ℕ)/2 : ℂ)+a)*z else ((k : ℕ)/2 : ℂ)*z) with hAdef
  have hA0 : A 0 = 1 := by simp [A]
  have hA1 : A 1 = -z := by simp [A]
  have hAo : ∀ m ≥ 1, A (2 * m + 1) = -(m + a) * z := by
    intro m hm
    simp only [A, show 2 * m + 1 ≠ 0 by omega, ↓reduceIte, odd_two_mul_add_one,
      show 2 * m + 1 ≠ 1 by omega, Nat.add_sub_cancel]
    push_cast; ring
  have hAe : ∀ m ≥ 1, A (2 * m) = m * z := by
    intro m hm
    have : ¬ Odd (2 * m) := by simp
    simp only [A, show 2 * m ≠ 0 by omega, ↓reduceIte, this]
    push_cast; ring
  by_cases hz : z = 0
  · subst hz
    unfold DLMF.HasContinuedFraction
    rw [kummerM_zero]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [incGF_cfTail_freeze (by simp [A]) hn, hA0]
    simp
  · refine (incGF_hasContinuedFraction_iff ?_ _).mpr ?_
    · intro k _
      exact incGF_gammaStar_A_ne ha hz hA0 hA1 hAo hAe k
    exact incGF_gammaStar_tendsto ha hz hA0 hA1 hAo hAe (by simp)
      (fun k hk => by simp [show k ≠ 0 by omega])

/-- upperIncGamma continuedFraction complex. -/
@[dlmf 8.9.E2]
theorem upperIncGamma_continuedFraction_complex (a : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    HasContinuedFraction (fun k => if k=0 then z⁻¹ else (if Odd k then ((k+1)/2 : ℕ)-a else ((k/2 : ℕ) : ℂ))/z) (fun _ => 1) (z^(-a)*exp z*upperIncGamma a z) := by
  sorry

/-- upperIncGamma bound le one. -/
@[dlmf 8.10.E1]
theorem upperIncGamma_bound_le_one {a x : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hx : 0 < x) :
    x^(1-a)*Real.exp x*(upperIncGamma a x).re ≤ 1 := by
  have h := incG_upperIncGamma_re_le ha1 hx
  have e : x^(1-a)*Real.exp x*(x^(a-1)*Real.exp (-x)) = 1 := by
    rw [show x^(1-a)*Real.exp x*(x^(a-1)*Real.exp (-x)) = (x^(1-a)*x^(a-1))*(Real.exp x*Real.exp (-x)) by ring,
      ← Real.rpow_add hx, ← Real.exp_add]; simp
  calc _ ≤ x^(1-a)*Real.exp x*(x^(a-1)*Real.exp (-x)) := by gcongr
    _ = 1 := e

/-- lowerIncGamma bound ge. -/
@[dlmf 8.10.E2]
theorem lowerIncGamma_bound_ge {a x : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hx : 0 < x) :
    (lowerIncGamma a x).re ≥ x^(a-1)/a*(1-Real.exp (-x)) :=
  incG_lowerIncGamma_bound_ge ha ha1 hx

/-- upperIncGamma bound ge one. -/
@[dlmf 8.10.E1]
theorem upperIncGamma_bound_ge_one {a x : ℝ} (ha : 1 ≤ a) (hx : 0 < x) :
    1 ≤ x^(1-a)*Real.exp x*(upperIncGamma a x).re := by
  have h := incG_upperIncGamma_re_ge ha hx
  have e : x^(1-a)*Real.exp x*(x^(a-1)*Real.exp (-x)) = 1 := by
    rw [show x^(1-a)*Real.exp x*(x^(a-1)*Real.exp (-x)) = (x^(1-a)*x^(a-1))*(Real.exp x*Real.exp (-x)) by ring,
      ← Real.rpow_add hx, ← Real.exp_add]; simp
  calc (1:ℝ) = x^(1-a)*Real.exp x*(x^(a-1)*Real.exp (-x)) := e.symm
    _ ≤ _ := by gcongr

/-- lowerIncGamma bound le. -/
@[dlmf 8.10.E2]
theorem lowerIncGamma_bound_le {a x : ℝ} (ha : 1 ≤ a) (hx : 0 < x) :
    (lowerIncGamma a x).re ≤ x^(a-1)/a*(1-Real.exp (-x)) :=
  incG_lowerIncGamma_bound_le ha hx

/-- The first-order real incomplete-Gamma remainder ratio. -/
@[dlmf 8.10.E3]
def Real.upperGammaTheta (a x : ℝ) : ℝ :=
  if a=1 then 1 else (x^(1-a)*Real.exp x*(upperIncGamma a x).re-1)*x/(a-1)

/-- Real.upperGammaTheta identity. -/
@[dlmf 8.10.E3]
theorem Real.upperGammaTheta_identity {a x : ℝ} (hx : 0 < x) :
    x^(1-a)*Real.exp x*(upperIncGamma a x).re=1+(a-1)/x*Real.upperGammaTheta a x := by
  rw [Real.upperGammaTheta]
  split_ifs with h
  · subst h
    rw [ofReal_one, upperIncGamma_one, ← ofReal_neg, ← ofReal_exp, ofReal_re, sub_self,
      Real.rpow_zero, one_mul, ← Real.exp_add, add_neg_cancel, Real.exp_zero]
    ring
  · have h1 : a - 1 ≠ 0 := sub_ne_zero.mpr h
    field_simp
    ring

/-- The remainder ratio tends to one in DLMF §8.10. -/
theorem Real.upperGammaTheta_limit (a : ℝ) :
    Tendsto (Real.upperGammaTheta a) atTop (𝓝 1) := by
  by_cases ha : a = 1
  · subst ha
    exact tendsto_const_nhds.congr fun x => by simp [Real.upperGammaTheta]
  have ha1 : (a:ℝ) - 1 ≠ 0 := sub_ne_zero.mpr ha
  have h := hasAsymptoticExpansion_upperIncGamma (a:ℂ) 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, one_mul,
    smul_eq_mul] at h
  set D : ℝ → ℂ := fun x => upperIncGamma a x - (exp (-(x:ℂ)) * (x:ℂ)^((a:ℂ)-1-((0:ℕ):ℂ)) *
    poch (1-a) 0 + exp (-(x:ℂ)) * (x:ℂ)^((a:ℂ)-1-((1:ℕ):ℂ)) * ((-1)^1*poch (1-a) 1))
  have hf := (isBigO_refl (fun x : ℝ => (x:ℂ)^(2-(a:ℂ))*exp (x:ℂ)) atTop).mul h
  -- the comparison function tends to zero
  have hg : Tendsto (fun x : ℝ => (x:ℂ)^(2-(a:ℂ))*exp (x:ℂ)*(exp (-(x:ℂ))*(x:ℂ)^((a:ℂ)-1-((2:ℕ):ℂ))))
      atTop (𝓝 0) := by
    have he : (fun x : ℝ => (x:ℂ)^(2-(a:ℂ))*exp (x:ℂ)*(exp (-(x:ℂ))*(x:ℂ)^((a:ℂ)-1-((2:ℕ):ℂ))))
        =ᶠ[atTop] fun x : ℝ => ((x⁻¹ : ℝ) : ℂ) := by
      filter_upwards [eventually_gt_atTop 0] with x hx
      have hx0 : (x:ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
      have hee : exp (x:ℂ) * exp (-(x:ℂ)) = 1 := by rw [← Complex.exp_add]; simp
      rw [show (x:ℂ)^(2-(a:ℂ))*exp (x:ℂ)*(exp (-(x:ℂ))*(x:ℂ)^((a:ℂ)-1-((2:ℕ):ℂ))) =
        (exp (x:ℂ) * exp (-(x:ℂ))) * ((x:ℂ)^(2-(a:ℂ))*(x:ℂ)^((a:ℂ)-1-((2:ℕ):ℂ))) by ring,
        hee, one_mul, ← cpow_add _ _ hx0, show 2-(a:ℂ)+((a:ℂ)-1-((2:ℕ):ℂ)) = -1 by push_cast; ring,
        cpow_neg_one, ofReal_inv]
    refine Tendsto.congr' he.symm ?_
    have := (Complex.continuous_ofReal.tendsto 0).comp tendsto_inv_atTop_zero
    simpa [Function.comp_def] using this
  have hf0 := hf.trans_tendsto hg
  -- relate to θ
  refine (((Complex.continuous_re.tendsto _).comp hf0).div_const (a-1) |>.const_add 1).congr' ?_ |>.mono_right ?_
  · filter_upwards [eventually_gt_atTop 0] with x hx
    simp only [Function.comp_apply, D]
    have hc : (x:ℂ)^(2-(a:ℂ))*cexp x = ((x^(2-a)*Real.exp x : ℝ):ℂ) := by
      rw [ofReal_mul, ofReal_cpow hx.le, ofReal_exp]; push_cast; ring
    have hsum : exp (-(x:ℂ)) * (x:ℂ)^((a:ℂ)-1-((0:ℕ):ℂ)) * poch (1-a) 0 +
        exp (-(x:ℂ)) * (x:ℂ)^((a:ℂ)-1-((1:ℕ):ℂ)) * ((-1)^1*poch (1-a) 1) =
        ((Real.exp (-x) * x^(a-1) - Real.exp (-x) * x^(a-2) * (1-a) : ℝ) : ℂ) := by
      push_cast
      rw [ofReal_cpow hx.le, ofReal_cpow hx.le]
      simp [poch]
      ring_nf
    rw [hc, hsum, re_ofReal_mul, sub_re, ofReal_re, Real.upperGammaTheta]
    simp only [ha, ↓reduceIte]
    set u := x^(1-a) with hu
    have hu0 : 0 < u := Real.rpow_pos_of_pos hx _
    have e1 : x^(2-a) = x*u := by
      rw [hu, show 2-a = 1 + (1-a) by ring, Real.rpow_add hx, Real.rpow_one]
    have e2 : x^(a-1) = u⁻¹ := by
      rw [hu, ← Real.rpow_neg hx.le]; ring_nf
    have e3 : x^(a-2) = u⁻¹*x⁻¹ := by
      rw [hu, ← Real.rpow_neg hx.le, ← Real.rpow_neg_one, ← Real.rpow_add hx]; ring_nf
    have hee : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
    rw [e1, e2, e3]
    field_simp
    linear_combination (-(x-(1-a))) * hee
  · simp

/-- Real.upperGammaTheta bounds. -/
@[dlmf 8.10.E4]
theorem Real.upperGammaTheta_bounds {a x : ℝ} (ha : a ≤ 2) (hx : 0 < x) :
    0 < Real.upperGammaTheta a x ∧ Real.upperGammaTheta a x ≤ 1 := by
  by_cases h1 : a = 1
  · simp [Real.upperGammaTheta, h1]
  have hx0 : (x:ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have hrec := upperIncGamma_add_one ((a:ℂ)-1) hx0
  rw [sub_add_cancel] at hrec
  have e : ((x:ℂ)^((a:ℂ)-1)*exp (-(x:ℂ))).re = x^(a-1)*Real.exp (-x) := by
    rw [show (a:ℂ)-1 = ((a-1:ℝ):ℂ) by push_cast; ring, ← ofReal_cpow hx.le, ← ofReal_neg,
      ← ofReal_exp, ← ofReal_mul, ofReal_re]
  have hre : (upperIncGamma a x).re = (a-1)*(upperIncGamma ((a-1:ℝ):ℂ) x).re + x^(a-1)*Real.exp (-x) := by
    rw [hrec, add_re, e]; push_cast
    simp [Complex.mul_re]
  have hθ : Real.upperGammaTheta a x = x^(2-a)*Real.exp x*(upperIncGamma ((a-1:ℝ):ℂ) x).re := by
    have ha1 : a - 1 ≠ 0 := sub_ne_zero.mpr h1
    simp only [Real.upperGammaTheta, h1, ↓reduceIte]
    rw [hre]
    have hu : x^(1-a)*x^(a-1) = 1 := by rw [← Real.rpow_add hx]; simp
    have hv : x^(2-a) = x^(1-a)*x := by rw [← Real.rpow_add_one hx.ne']; ring_nf
    have hee : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
    rw [hv]
    field_simp
    linear_combination Real.exp x*Real.exp (-x)*hu + hee
  have hle := incG_upperIncGamma_re_le (a := a-1) (by linarith) hx
  have hpos := incG_upperIncGamma_re_pos (a := a-1) hx (incG_integrableOn_rpow_exp_of_le_one (by linarith) hx)
  rw [hθ]
  refine ⟨by positivity, ?_⟩
  calc x^(2-a)*Real.exp x*(upperIncGamma ((a-1:ℝ):ℂ) x).re ≤ x^(2-a)*Real.exp x*(x^(a-1-1)*Real.exp (-x)) := by
        gcongr
    _ = 1 := by
      rw [show x^(2-a)*Real.exp x*(x^(a-1-1)*Real.exp (-x)) = (x^(2-a)*x^(a-1-1))*(Real.exp x*Real.exp (-x)) by ring,
        ← Real.rpow_add hx, ← Real.exp_add]; ring_nf; simp


/-- Finite Legendre convergents giving A_n and B_n. -/
def Real.upperGammaPade (upper : Bool) (n : ℕ) (a x : ℝ) : ℝ :=
  (cfTail (fun k => if k=0 then x else if Odd k then ((k+1)/2 : ℕ)-a else ((k/2 : ℕ) : ℝ)) (fun k => if Even k then (x : ℂ) else 1) 0 (2*n+if upper then 1 else 0)).re

/-- Real.upperGammaPade bounds. -/
@[dlmf 8.10.E5]
theorem Real.upperGammaPade_bounds {a x : ℝ} (ha : a < 1) (hx : 0 < x) {n : ℕ} (hn : 1 ≤ n) :
    Real.upperGammaPade false n a x < x^(1-a)*Real.exp x*(upperIncGamma a x).re ∧ x^(1-a)*Real.exp x*(upperIncGamma a x).re < Real.upperGammaPade true n a x := by
  have key : ∀ (u : Bool), Real.upperGammaPade u n a x =
      (GenContFract.cfConv_ofFun 0 (incGF_padeNum a x) (DLMF.Statistical.gammaIncCFDen x)).convs
        (2*n+if u then 1 else 0) := by
    intro u
    rw [Real.upperGammaPade, incGF_cfTail_ofReal (a := incGF_padeNum a x)
      (b := DLMF.Statistical.gammaIncCFDen x) (fun k => ?_) (fun k => ?_)
      (fun k _ => (incGF_padeNum_pos ha hx k).ne'), ofReal_re]
    · simp only [incGF_padeNum, DLMF.Statistical.gammaIncCFNum]
      rcases Nat.even_or_odd k with hk | hk
      · have h2 : k % 2 = 0 := Nat.even_iff.mp hk
        have : ¬ Odd k := Nat.not_odd_iff_even.mpr hk
        split_ifs <;> simp_all
      · have h2 : k % 2 = 1 := Nat.odd_iff.mp hk
        split_ifs with h0
        · simp_all
        · have : (k + 1) / 2 = k / 2 + 1 := by omega
          rw [this]; push_cast; ring
    · simp only [DLMF.Statistical.gammaIncCFDen]
      rcases Nat.even_or_odd k with hk | hk
      · simp [hk, Nat.even_iff.mp hk]
      · have h1 : ¬ Even k := Nat.not_even_iff_odd.mpr hk
        have h2 : ¬ k % 2 = 0 := by have := Nat.odd_iff.mp hk; omega
        simp [h1, h2]
  rw [key, key]
  exact ⟨incGF_pade_lt ha hx hn, by simpa using incGF_lt_pade ha hx n⟩

/-- Real.upperGammaPade first. -/
@[dlmf 8.10.E6]
theorem Real.upperGammaPade_first {a x : ℝ} (ha : a < 1) (hx : 0 < x) :
    Real.upperGammaPade false 1 a x=x/(x+1-a) ∧ Real.upperGammaPade true 1 a x=(x+1)/(x+2-a) ∧ Real.upperGammaPade false 2 a x=x*(x+3-a)/(x^2+2*(2-a)*x+(1-a)*(2-a)) ∧ Real.upperGammaPade true 2 a x=(x^2+(5-a)*x+2)/(x^2+2*(3-a)*x+(2-a)*(3-a)) := by
  have h1 : (1:ℂ) - (a:ℂ) ≠ 0 := by
    rw [← ofReal_one, ← ofReal_sub, ofReal_ne_zero]; linarith
  have h2 : (2:ℂ) - (a:ℂ) ≠ 0 := by
    rw [← ofReal_ofNat, ← ofReal_sub, ofReal_ne_zero]; linarith
  have hc : ∀ r : ℝ, 0 < r → (r:ℂ) ≠ 0 := fun r hr => ofReal_ne_zero.mpr hr.ne'
  have d1 := hc (x+1-a) (by linarith)
  have d2 := hc (x+2-a) (by linarith)
  have d3 := hc (x^2+2*(2-a)*x+(1-a)*(2-a)) (by nlinarith)
  have d4 := hc (x^2+2*(3-a)*x+(2-a)*(3-a)) (by nlinarith)
  have hx0 := hc x hx
  push_cast at d1 d2 d3 d4
  simp only [Real.upperGammaPade, cfTail]
  simp [cfContinuants.eq_def, GenContFract.nextConts, GenContFract.nextNum, GenContFract.nextDen, h1, h2,
    show ¬ Odd 2 by decide, show Odd 3 by decide, show ¬ Odd 4 by decide, show Odd 1 by decide,
    show Even 2 by decide, show ¬ Even 3 by decide, show Even 4 by decide, show ¬ Even 1 by decide]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Complex.ofReal_re (x/(x+1-a))]; congr 1; push_cast; ring_nf
  · rw [← Complex.ofReal_re ((x+1)/(x+2-a))]; congr 1; push_cast
    rw [div_eq_div_iff (by rw [show (x:ℂ)*(x+(1-a))+x = x*(x+2-a) by ring]; exact mul_ne_zero hx0 d2) d2]
    ring
  · rw [← Complex.ofReal_re (x*(x+3-a)/(x^2+2*(2-a)*x+(1-a)*(2-a)))]; congr 1; push_cast
    rw [div_eq_div_iff (by rw [show (x:ℂ)*(x+(1-a))+x+(2-a)*(x+(1-a)) = x^2+2*(2-a)*x+(1-a)*(2-a) by ring]; exact d3) d3]
    ring
  · rw [← Complex.ofReal_re ((x^2+(5-a)*x+2)/(x^2+2*(3-a)*x+(2-a)*(3-a)))]; congr 1; push_cast
    rw [div_eq_div_iff (by rw [show (x:ℂ)*(x*(x+(1-a))+x+(2-a)*(x+(1-a)))+2*(x*(x+(1-a))+x) = x*(x^2+2*(3-a)*x+(2-a)*(3-a)) by ring]; exact mul_ne_zero hx0 d4) d4]
    ring

/-- incompleteGamma positive exponential integral. -/
@[dlmf 8.10.E7]
theorem incompleteGamma_positive_exponential_integral {a : ℂ} (ha : 0 < a.re) {x : ℝ} (hx : 0 < x) :
    (∫ t in (0 : ℝ)..x, (t : ℂ)^(a-1)*exp t)=Gamma a*(x : ℂ)^a*scIncGamma a (-x) := by
  have hG : Gamma a ≠ 0 := Complex.Gamma_ne_zero_of_re_pos ha
  rw [scIncGamma_integral ha, ← mul_assoc, mul_assoc (Gamma a), mul_comm ((x:ℂ)^a), ← mul_assoc,
    mul_one_div_cancel hG, one_mul]
  have hsub := intervalIntegral.integral_comp_mul_left (a := 0) (b := 1)
    (fun t : ℝ => (t : ℂ)^(a-1)*exp t) hx.ne'
  simp only [mul_zero, mul_one] at hsub
  have hJ : (∫ s in (0:ℝ)..1, ((x * s : ℝ) : ℂ)^(a-1)*exp ((x * s : ℝ) : ℂ)) =
      (x:ℂ)^(a-1) * ∫ t in (0:ℝ)..1, (t : ℂ)^(a-1)*exp (- -(x:ℂ)*t) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun s hs => ?_
    have hs0 : 0 ≤ s := by
      rw [Set.uIcc_of_le zero_le_one] at hs; exact hs.1
    rw [ofReal_mul, mul_cpow_ofReal_nonneg hx.le hs0, neg_neg]; ring
  rw [hJ] at hsub
  have hx0 : (x:ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have ha1 : (x:ℂ)^a = (x:ℂ) * (x:ℂ)^(a-1) := by
    conv_lhs => rw [show a = 1 + (a-1) by ring, cpow_add _ _ hx0, cpow_one]
  rw [ha1, mul_assoc, hsub, Complex.real_smul, ← mul_assoc, ofReal_inv, mul_inv_cancel₀ hx0, one_mul]

/-- A function continuous on `[0,∞)`, vanishing at `0`, with positive derivative on `(0,∞)`
is positive on `(0,∞)`. -/
theorem incG_pos_of_hasDerivAt {f f' : ℝ → ℝ} (hc : ContinuousOn f (Ici 0))
    (hd : ∀ x, 0 < x → HasDerivAt f (f' x) x) (hp : ∀ x, 0 < x → 0 < f' x) (h0 : f 0 = 0)
    {x : ℝ} (hx : 0 < x) : 0 < f x := by
  have hm : StrictMonoOn f (Ici 0) := strictMonoOn_of_deriv_pos (convex_Ici 0) hc
    (fun y hy => by rw [interior_Ici] at hy; rw [(hd y hy).deriv]; exact hp y hy)
  have := hm self_mem_Ici (mem_Ici.mpr hx.le) hx
  rwa [h0] at this

theorem incG_hasDerivAt_rpow_mul_exp {a x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun x : ℝ => x^a*Real.exp x) ((a/x+1)*(x^a*Real.exp x)) x := by
  have h := ((Real.hasDerivAt_rpow_const (p := a) (Or.inl hx.ne')).mul (Real.hasDerivAt_exp x))
  convert h using 1
  rw [Real.rpow_sub hx, Real.rpow_one]; field_simp

theorem incG_continuous_rpow_mul_exp {a : ℝ} (ha : 0 < a) :
    Continuous (fun x : ℝ => x^a*Real.exp x) :=
  (Real.continuous_rpow_const ha.le).mul Real.continuous_exp

theorem incG_intervalIntegrable_rpow_mul_exp {a : ℝ} (ha : 0 < a) (u v : ℝ) :
    IntervalIntegrable (fun t : ℝ => t^(a-1)*Real.exp t) volume u v :=
  (intervalIntegral.intervalIntegrable_rpow' (by linarith)).mul_continuousOn
    Real.continuous_exp.continuousOn

theorem incG_continuous_primitive_rpow_mul_exp {a : ℝ} (ha : 0 < a) :
    Continuous (fun x : ℝ => ∫ t in (0:ℝ)..x, t^(a-1)*Real.exp t) :=
  intervalIntegral.continuous_primitive (incG_intervalIntegrable_rpow_mul_exp ha) 0

theorem incG_hasDerivAt_primitive_rpow_mul_exp {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    HasDerivAt (fun x : ℝ => ∫ t in (0:ℝ)..x, t^(a-1)*Real.exp t) (x^(a-1)*Real.exp x) x := by
  have hcont : ContinuousOn (fun t : ℝ => t^(a-1)*Real.exp t) (Ioi 0) := fun t ht =>
    ((Real.continuousAt_rpow_const _ _ (Or.inl (ne_of_gt ht))).mul
      Real.continuous_exp.continuousAt).continuousWithinAt
  exact intervalIntegral.integral_hasDerivAt_right (incG_intervalIntegrable_rpow_mul_exp ha 0 x)
    (hcont.stronglyMeasurableAtFilter isOpen_Ioi x hx)
    (hcont.continuousAt (isOpen_Ioi.mem_nhds hx))

theorem incG_positive_exponential_bounds {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    (a+1)*(a+2)-x < ((a+1)*(a+2+x))*(a*x^(-a)*Real.exp (-x)*(∫ t in (0 : ℝ)..x, t^(a-1)*Real.exp t)) ∧ a*x^(-a)*Real.exp (-x)*(∫ t in (0 : ℝ)..x, t^(a-1)*Real.exp t) < (a+1)/(a+1+x) := by
  set P : ℝ → ℝ := fun x => x^a*Real.exp x with hPdef
  set G : ℝ → ℝ := fun x => ∫ t in (0:ℝ)..x, t^(a-1)*Real.exp t with hGdef
  have hP := fun y (hy : 0 < y) => incG_hasDerivAt_rpow_mul_exp (a := a) hy
  have hG := fun y (hy : 0 < y) => incG_hasDerivAt_primitive_rpow_mul_exp ha hy
  have hGd : ∀ y, 0 < y → y^(a-1)*Real.exp y = P y / y := by
    intro y hy; simp only [P]; rw [Real.rpow_sub hy, Real.rpow_one]; ring
  have hPc : Continuous P := incG_continuous_rpow_mul_exp ha
  have hGc : Continuous G := incG_continuous_primitive_rpow_mul_exp ha
  have hP0 : P 0 = 0 := by simp [P, Real.zero_rpow ha.ne']
  have hG0 : G 0 = 0 := by simp [G]
  have hPpos : ∀ y, 0 < y → 0 < P y := fun y hy => by simp only [P]; positivity
  -- k = P - aG
  have hk : ∀ y, 0 < y → 0 < P y - a*G y := by
    intro y hy
    refine incG_pos_of_hasDerivAt (f := fun y => P y - a*G y) (f' := P)
      (hPc.sub (continuous_const.mul hGc)).continuousOn (fun z hz => ?_) hPpos
      (by simp [hP0, hG0]) hy
    convert (hP z hz).sub ((hG z hz).const_mul a) using 1
    rw [hGd z hz]; field_simp; ring
  -- m1 = xP - (a+1)k
  have hm1 : ∀ y, 0 < y → 0 < y*P y - (a+1)*(P y - a*G y) := by
    intro y hy
    refine incG_pos_of_hasDerivAt (f := fun y => y*P y - (a+1)*(P y - a*G y))
      (f' := fun y => y * P y)
      ((continuous_id.mul hPc).sub (continuous_const.mul
        (hPc.sub (continuous_const.mul hGc)))).continuousOn (fun z hz => ?_)
      (fun z hz => mul_pos hz (hPpos z hz)) (by simp [hP0, hG0]) hy
    convert ((hasDerivAt_id z).mul (hP z hz)).sub
      (((hP z hz).sub ((hG z hz).const_mul a)).const_mul (a+1)) using 1
    · funext y; simp only [Pi.sub_apply, Pi.mul_apply, id, P, G]
    · rw [hGd z hz]; simp only [id]; field_simp; ring
  -- m = a(a+1)(a+2+x)G - ((a+1)(a+2)-x)P
  have hm : 0 < a*(a+1)*(a+2+x)*G x - ((a+1)*(a+2)-x)*P x := by
    refine incG_pos_of_hasDerivAt (f := fun y => a*(a+1)*(a+2+y)*G y - ((a+1)*(a+2)-y)*P y)
      (f' := fun y => y*P y - (a+1)*(P y - a*G y))
      (((continuous_const.mul (continuous_const.add continuous_id)).mul hGc).sub
        ((continuous_const.sub continuous_id).mul hPc)).continuousOn (fun z hz => ?_)
      hm1 (by simp [hP0, hG0]) hx
    convert ((((hasDerivAt_id z).const_add (a+2)).const_mul (a*(a+1))).mul (hG z hz)).sub
      (((hasDerivAt_id z).const_sub ((a+1)*(a+2))).mul (hP z hz)) using 1
    · funext y; simp only [Pi.sub_apply, Pi.mul_apply, id, P, G]
    · rw [hGd z hz]; simp only [id]; field_simp; ring
  -- h = (a+1)P - a(a+1+x)G
  have hh : 0 < (a+1)*P x - a*(a+1+x)*G x := by
    refine incG_pos_of_hasDerivAt (f := fun y => (a+1)*P y - a*(a+1+y)*G y)
      (f' := fun y => P y - a*G y)
      ((continuous_const.mul hPc).sub ((continuous_const.mul
        (continuous_const.add continuous_id)).mul hGc)).continuousOn (fun z hz => ?_)
      hk (by simp [hP0, hG0]) hx
    convert ((hP z hz).const_mul (a+1)).sub
      ((((hasDerivAt_id z).const_add (a+1)).const_mul a).mul (hG z hz)) using 1
    · funext y; simp only [Pi.sub_apply, Pi.mul_apply, id, P, G]
    · rw [hGd z hz]; simp only [id]; field_simp; ring
  have hF : a*x^(-a)*Real.exp (-x)*(∫ t in (0 : ℝ)..x, t^(a-1)*Real.exp t) = a*G x/P x := by
    simp only [P, G]; rw [Real.rpow_neg hx.le, Real.exp_neg]; field_simp
  rw [hF]
  have hPx := hPpos x hx
  constructor
  · rw [← mul_div_assoc, lt_div_iff₀ hPx]; nlinarith
  · rw [div_lt_div_iff₀ hPx (by linarith)]; nlinarith

/-- The integral needs a>0; the a=0 boundary is acquired separately as a limit. -/
@[dlmf 8.10.E8]
theorem incompleteGamma_positive_exponential_bounds {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    (a+1)*(a+2)-x < ((a+1)*(a+2+x))*(a*x^(-a)*Real.exp (-x)*(∫ t in (0 : ℝ)..x, t^(a-1)*Real.exp t)) ∧ a*x^(-a)*Real.exp (-x)*(∫ t in (0 : ℝ)..x, t^(a-1)*Real.exp t) < (a+1)/(a+1+x) :=
  incG_positive_exponential_bounds ha hx

/-- incompleteGamma positive exponential limit. -/
@[dlmf 8.10.E8]
theorem incompleteGamma_positive_exponential_limit {x : ℝ} (hx : 0 < x) :
    Tendsto (fun a : ℝ => (exp (-x : ℂ)*Gamma (a+1)*scIncGamma a (-x)).re) (𝓝[>] 0) (𝓝 (Real.exp (-x))) := by
  have h0 : scIncGamma 0 (-x) = 1 := by
    have := scIncGamma_neg_nat 0 (-(x:ℂ)); simpa using this
  have hG : ContinuousAt (fun a : ℝ => Gamma (a+1)) 0 := by
    have hd : DifferentiableAt ℂ Gamma ((0:ℝ)+1) := by
      refine Complex.differentiableAt_Gamma _ fun m => ?_
      intro h
      have := congrArg Complex.re h
      simp at this
      linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)]
    exact hd.continuousAt.comp (f := fun a : ℝ => (a:ℂ)+1) (by fun_prop)
  have hc : ContinuousAt (fun a : ℝ => (exp (-x : ℂ)*Gamma (a+1)*scIncGamma a (-x)).re) 0 := by
    refine Complex.continuous_re.continuousAt.comp ?_
    exact (continuousAt_const.mul hG).mul
      ((continuous_scIncGamma_param _).comp continuous_ofReal).continuousAt
  have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
  convert this using 2
  simp only [ofReal_zero, zero_add, Complex.Gamma_one, h0, mul_one]
  rw [← ofReal_neg, ← ofReal_exp, ofReal_re]

/-- Constant c_a. -/
@[dlmf 8.10.E9]
def Real.upperGammaCa (a : ℝ) : ℝ :=
  Real.Gamma (1+a)^(1/(a-1))

/-- Constant d_a. -/
@[dlmf 8.10.E9]
def Real.upperGammaDa (a : ℝ) : ℝ :=
  Real.Gamma (1+a)^(-1/a)

/-- At x=0 the displayed scaled formula uses its zero limit. -/
@[dlmf 8.10.E10]
theorem upperIncGamma_power_bounds {a x : ℝ} (ha : 0 < a) (ha1 : a < 1) (hx : 0 < x) :
    x/(2*a)*((1+2/x)^a-1) < x^(1-a)*Real.exp x*(upperIncGamma a x).re ∧ x^(1-a)*Real.exp x*(upperIncGamma a x).re ≤ x/(a*Real.upperGammaCa a)*((1+Real.upperGammaCa a/x)^a-1) := by
  have hnp : ∀ k : ℕ, (a:ℂ) ≠ -k := by
    intro k h
    have := congrArg Complex.re h
    simp at this
    linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
  have hx' : (x:ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt hx)
  have h := lowerIncGamma_add_upperIncGamma hnp hx'
  rw [lowerIncGamma_ofReal ha hx] at h
  have hu : (upperIncGamma a x).re = Real.Gamma a - TauCeti.lowerIncompleteGamma a x := by
    have : upperIncGamma a x = ((Real.Gamma a - TauCeti.lowerIncompleteGamma a x : ℝ) : ℂ) := by
      rw [ofReal_sub, ← Complex.Gamma_ofReal]; linear_combination h
    rw [this, ofReal_re]
  have key : ∀ l : ℝ, 0 < l → x/(a*l)*((1+l/x)^a-1) =
      x^(1-a)*Real.exp x*(Real.exp (-x)*(((x+l)^a - x^a)/(a*l))) := by
    intro l hl
    have hxl : 0 < x + l := by linarith
    have h1 : 1 + l/x = (x+l)/x := by field_simp
    have h2 : x^(1-a) = x / x^a := by rw [Real.rpow_sub hx, Real.rpow_one]
    have h3 : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
    have : 0 < x^a := Real.rpow_pos_of_pos hx _
    rw [h1, Real.div_rpow hxl.le hx.le, h2, mul_assoc (x / x^a), ← mul_assoc (Real.exp x), h3,
      one_mul]
    field_simp
  have hP : 0 < x^(1-a)*Real.exp x := by positivity
  rw [hu]
  constructor
  · rw [mul_comm 2 a, key 2 two_pos]
    exact mul_lt_mul_of_pos_left (igBd_upper_gt ha ha1 hx) hP
  · rw [Real.upperGammaCa]
    have hc : 0 < Real.Gamma (1+a)^(1/(a-1)) :=
      Real.rpow_pos_of_pos (Real.Gamma_pos_of_pos (by linarith)) _
    rw [key _ hc]
    exact (mul_lt_mul_of_pos_left (igBd_upper_lt ha ha1 hx) hP).le

/-- upperIncGamma power bounds zero limit. -/
@[dlmf 8.10.E10]
theorem upperIncGamma_power_bounds_zero_limit {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    Tendsto (fun x : ℝ => x^(1-a)*Real.exp x*(upperIncGamma a x).re) (𝓝[>] 0) (𝓝 0) := by
  have hnp : ∀ k : ℕ, (a:ℂ) ≠ -k := by
    intro k h
    have := congrArg Complex.re h
    simp at this
    linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
  have hc : ContinuousAt (fun x : ℝ => x^(1-a)*Real.exp x*(Real.Gamma a - TauCeti.lowerIncompleteGamma a x)) 0 := by
    have h1 : ContinuousAt (fun x : ℝ => x^(1-a)) 0 :=
      Real.continuousAt_rpow_const _ _ (Or.inr (by linarith))
    exact (h1.mul Real.continuous_exp.continuousAt).mul
      (continuousAt_const.sub (TauCeti.continuous_lowerIncompleteGamma a).continuousAt)
  have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
  rw [Real.zero_rpow (by linarith), zero_mul, zero_mul] at this
  refine this.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx' : (x:ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt hx)
  have h := lowerIncGamma_add_upperIncGamma hnp hx'
  rw [lowerIncGamma_ofReal ha hx] at h
  have hu : upperIncGamma a x = ((Real.Gamma a - TauCeti.lowerIncompleteGamma a x : ℝ) : ℂ) := by
    rw [ofReal_sub, ← Complex.Gamma_ofReal]; linear_combination h
  rw [hu, ofReal_re]

/-- Lower bounding constant α_a, with its continuous value at a=1. -/
@[dlmf 8.10.E12]
def Real.gammaPAlpha (a : ℝ) : ℝ :=
  if a < 1 then 1 else Real.upperGammaDa a

/-- Upper bounding constant β_a. -/
@[dlmf 8.10.E12]
def Real.gammaPBeta (a : ℝ) : ℝ :=
  if a < 1 then Real.upperGammaDa a else 1

/-- Alzer's strict bounds behind DLMF 8.10.11 (helper for the two tagged statements). -/
theorem igBd_exponential_bounds_strict {a x : ℝ} (ha : 0 < a) (ha1 : a ≠ 1) (hx : 0 < x) :
    (1-Real.exp (-Real.gammaPAlpha a*x))^a < (normIncGammaPContinued a x).re ∧ (normIncGammaPContinued a x).re < (1-Real.exp (-Real.gammaPBeta a*x))^a := by
  rw [igBd_normIncGammaP_re ha hx.le]
  have hγ : 0 < Real.Gamma (1+a)^(-1/a) :=
    Real.rpow_pos_of_pos (Real.Gamma_pos_of_pos (by linarith)) _
  rcases lt_or_gt_of_ne ha1 with h | h
  · simp only [Real.gammaPAlpha, Real.gammaPBeta, h, ↓reduceIte, Real.upperGammaDa, neg_mul]
    refine ⟨?_, igBd_regGamma_lt_pow ha hγ (igBd_prop_da_lt_one ha h) hx⟩
    simpa using igBd_pow_lt_regGamma ha one_pos (igBd_prop_one_lt_one h) hx
  · simp only [Real.gammaPAlpha, Real.gammaPBeta, not_lt.mpr h.le, ↓reduceIte, Real.upperGammaDa,
      neg_mul]
    refine ⟨igBd_pow_lt_regGamma ha hγ (igBd_prop_da_gt_one h) hx, ?_⟩
    simpa using igBd_regGamma_lt_pow ha one_pos (igBd_prop_one_gt_one h) hx

/-- normIncGammaP exponential bounds. -/
@[dlmf 8.10.E11]
theorem normIncGammaP_exponential_bounds {a x : ℝ} (ha : 0 < a) (hx : 0 ≤ x) :
    (1-Real.exp (-Real.gammaPAlpha a*x))^a ≤ (normIncGammaPContinued a x).re ∧ (normIncGammaPContinued a x).re ≤ (1-Real.exp (-Real.gammaPBeta a*x))^a := by
  rcases hx.eq_or_lt with h0 | h0
  · subst h0
    rw [igBd_normIncGammaP_re ha le_rfl]
    simp [Real.zero_rpow ha.ne']
  by_cases ha1 : a = 1
  · subst ha1
    rw [igBd_normIncGammaP_re ha hx, TauCeti.regularizedGamma_one hx]
    simp [Real.gammaPAlpha, Real.gammaPBeta, Real.upperGammaDa, one_add_one_eq_two]
  · have := igBd_exponential_bounds_strict ha ha1 h0
    exact ⟨this.1.le, this.2.le⟩

/-- The source equality condition excludes the automatic equality at x=0. -/
@[dlmf 8.10.E11]
theorem normIncGammaP_exponential_bounds_strict {a x : ℝ} (ha : 0 < a) (ha1 : a ≠ 1) (hx : 0 < x) :
    (1-Real.exp (-Real.gammaPAlpha a*x))^a < (normIncGammaPContinued a x).re ∧ (normIncGammaPContinued a x).re < (1-Real.exp (-Real.gammaPBeta a*x))^a :=
  igBd_exponential_bounds_strict ha ha1 hx

/-- normIncGammaQ diagonal bounds. -/
@[dlmf 8.10.E13]
theorem normIncGammaQ_diagonal_bounds {n : ℕ} (hn : 1 ≤ n) :
    (normIncGammaQContinued n n).re < 1/2 ∧ 1/2 < (normIncGammaQContinued n (n-1 : ℕ)).re := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  have hG := Real.Gamma_pos_of_pos hn0
  have e1 : (n:ℂ) = ((n:ℝ):ℂ) := (ofReal_natCast n).symm
  have e2 : ((n-1:ℕ):ℂ) = (((n-1:ℕ):ℝ):ℂ) := (ofReal_natCast _).symm
  rw [e1, e2, igBd_normIncGammaQ_re hn0 hn0.le, igBd_normIncGammaQ_re hn0 (Nat.cast_nonneg _)]
  constructor
  · have := igBd_Gamma_lt_two_lower_self hn0
    rw [sub_lt_iff_lt_add, ← sub_lt_iff_lt_add', lt_div_iff₀ hG]; linarith
  · rw [lt_sub_iff_add_lt, ← lt_sub_iff_add_lt', div_lt_iff₀ hG]
    rcases Nat.lt_or_ge 1 n with h | h
    · have h1 : (1:ℝ) < n := by exact_mod_cast h
      have := igBd_two_lower_mode_lt_Gamma h1
      rw [Nat.cast_sub hn, Nat.cast_one]; linarith
    · have : n = 1 := le_antisymm h hn
      subst this
      simp only [Nat.sub_self, Nat.cast_zero, TauCeti.lowerIncompleteGamma_eq_zero_of_nonpos_right _ le_rfl]
      norm_num [Real.Gamma_one]

end DLMF.Confluent
