/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Bessel.Asymptotics
public import DLMFMathlib.Analysis.ODE.Volterra
public import DLMF.OrthogonalPolynomials.Classical

/-!
# Kummer's and Tricomi's functions for large negative `a`

Following Beals–Wong §13.2, the substitution `u(s) = s^{c-1/2} e^{-s²/(8κ)} 𝐌(c/2 - κ, c, s²/(4κ))`
turns Kummer's equation into the perturbed oscillator `u'' + u = g u` with
`g = ((c-1)² - 1/4)/s² + s²/(16κ²)` (`hasDerivAt_largeAU'`). As `κ → +∞` its data at a fixed
point converge, by a Tannery argument (`tendsto_regularizedConfluent_sub_div`), to those of
`u₀(s) = 2^{c-1} √s J_{c-1}(s)`, which solves the same equation with `g₀ = ((c-1)² - 1/4)/s²`.
The Volterra estimate `ODE.norm_sub_oscFree_le'` on `[s₀, S]`, with `s₀` large and then `κ`
large, gives `u_κ(S) - u₀(S) → 0` along `S = 2√(κx)` (`tendsto_largeAU_sub_largeAU0`), and the
Bessel asymptotics 10.7.8 give the cosine form.

## Main results

* `tendsto_regularizedConfluent_atBot`: the Erdélyi–Schmidt–Fejér asymptotics
  (Beals–Wong (8.1.12)) `√π ((c/2 - a)x)^{c/2-1/4} e^{-x/2} 𝐌(a, c, x)
  - cos(2√((c/2 - a)x) - cπ/2 + π/4) → 0` as `a → -∞`, for every real `c`.
* `tendsto_regularizedConfluent_atBot_besselJ`: the Bessel form (a weak form of DLMF 13.8.9).
* `tendsto_kummerU_atBot`: Beals–Wong (8.2.10) for non-integer `c` (compare DLMF 13.8.10).
* `laguerrePolyL_fejer`: Fejér's formula for Laguerre polynomials (Szegő (8.22.4)).

All error terms here are `o(1)`; the sharper `O(|a|^{-1/2})` rates of Beals–Wong and DLMF
(13.8.9, 13.8.10, 18.15.14) are proved in `DLMF.Confluent.LargeASharp`.
-/

@[expose] public section

open Complex Filter Set DLMF.Hypergeometric
open scoped Real Nat Topology

noncomputable section

namespace DLMF.Confluent

/-! ### A Tannery limit -/

/-- `(d - κ)_n / κⁿ → (-1)ⁿ` as `κ → +∞`. -/
theorem tendsto_poch_sub_div_pow (d : ℝ) (n : ℕ) :
    Tendsto (fun κ : ℝ => poch ((d - κ : ℝ) : ℂ) n / (κ : ℂ) ^ n) atTop
      (𝓝 ((-1 : ℂ) ^ n)) := by
  induction n with
  | zero => simp [poch_zero]
  | succ n ih =>
    have h1 : Tendsto (fun κ : ℝ => (((d - κ : ℝ) : ℂ) + n) / κ) atTop (𝓝 (-1)) := by
      have hr : Tendsto (fun κ : ℝ => (d + n) / κ - 1) atTop (𝓝 (0 - 1)) :=
        (tendsto_const_nhds.div_atTop tendsto_id).sub_const 1
      have hc := (continuous_ofReal.tendsto _).comp hr
      rw [zero_sub, ofReal_neg, ofReal_one] at hc
      refine hc.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with κ hκ
      have hκ' : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ.ne'
      simp only [Function.comp_apply]
      push_cast
      field_simp
      ring
    have := ih.mul h1
    rw [show (-1 : ℂ) ^ n * -1 = (-1) ^ (n + 1) by ring] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with κ hκ
    have hκ' : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ.ne'
    rw [poch_succ, pow_succ]
    field_simp

/-- The bound `‖(d - κ)_n / κⁿ‖ ≤ (1 + |d|)_n` for `κ ≥ 1`. -/
theorem norm_poch_sub_div_pow_le (d : ℝ) {κ : ℝ} (hκ : 1 ≤ κ) (n : ℕ) :
    ‖poch ((d - κ : ℝ) : ℂ) n / (κ : ℂ) ^ n‖ ≤ (ascPochhammer ℝ n).eval (1 + |d|) := by
  induction n with
  | zero => simp [poch_zero]
  | succ n ih =>
    have hκ0 : 0 < κ := by linarith
    have hκ' : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ0.ne'
    have hsplit : poch ((d - κ : ℝ) : ℂ) (n + 1) / (κ : ℂ) ^ (n + 1) =
        poch ((d - κ : ℝ) : ℂ) n / (κ : ℂ) ^ n * ((((d - κ : ℝ) : ℂ) + n) / κ) := by
      rw [poch_succ, pow_succ]
      field_simp
    have hfac : ‖(((d - κ : ℝ) : ℂ) + n) / κ‖ ≤ 1 + |d| + n := by
      rw [show (((d - κ : ℝ) : ℂ) + n) / κ = (((d - κ + n) / κ : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hκ0,
        div_le_iff₀ hκ0]
      have h1 : |d - κ + n| ≤ |d| + κ + n := by
        have := abs_add_le (d + n) (-κ)
        rw [show d + n + -κ = d - κ + n by ring, abs_neg, abs_of_pos hκ0] at this
        have h2 : |d + n| ≤ |d| + n := by
          have := abs_add_le d (n : ℝ)
          rwa [abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n)] at this
        linarith
      have hdn : 0 ≤ |d| + n := by positivity
      nlinarith
    rw [hsplit, norm_mul, ascPochhammer_succ_eval]
    have hpos : 0 ≤ (ascPochhammer ℝ n).eval (1 + |d|) :=
      (ascPochhammer_pos n _ (by positivity)).le
    exact mul_le_mul ih (by simpa [add_assoc] using hfac) (norm_nonneg _) hpos

/-- **Tannery limit**: `𝐌(d - κ, b, w/κ) → ₀F̃₁(;b;-w)` as `κ → +∞`. -/
theorem tendsto_regularizedConfluent_sub_div (d : ℝ) (b w : ℂ) :
    Tendsto (fun κ : ℝ => regularizedHGFun {((d - κ : ℝ) : ℂ)} {b} (w / κ)) atTop
      (𝓝 (regularizedHGFun (∅ : Multiset ℂ) {b} (-w))) := by
  set T : ℕ → ℂ := fun n => w ^ n / n ! * (Gamma (b + n))⁻¹ with hT
  have hL : ∀ κ : ℝ, κ ≠ 0 → regularizedHGFun {((d - κ : ℝ) : ℂ)} {b} (w / κ) =
      ∑' n : ℕ, poch ((d - κ : ℝ) : ℂ) n / (κ : ℂ) ^ n * T n := by
    intro κ hκ
    have hκ' : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ
    rw [regularizedConfluent_eq_tsum]
    refine tsum_congr fun n => ?_
    simp only [hT, div_pow]
    field_simp
  have hR : regularizedHGFun (∅ : Multiset ℂ) {b} (-w) = ∑' n : ℕ, (-1 : ℂ) ^ n * T n := by
    rw [regularizedHGFun_eq_tsum]
    refine tsum_congr fun n => ?_
    rw [DLMF.Bessel.regularizedHGFunCoeff_empty, hT, neg_pow]
    field_simp
  rw [hR]
  have hsum : Summable fun n : ℕ => (ascPochhammer ℝ n).eval (1 + |d|) * ‖T n‖ := by
    have hs := summable_norm_iff.mpr
      (summable_regularizedConfluent_term (((1 + |d| : ℝ)) : ℂ) b (‖w‖ : ℂ))
    refine hs.congr fun n => ?_
    rw [poch_ofReal]
    simp only [hT, norm_mul, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      norm_inv, Complex.norm_natCast, abs_norm]
    rw [abs_of_nonneg ((ascPochhammer_pos n _ (by positivity)).le)]
    ring
  refine (tendsto_tsum_of_dominated_convergence hsum
    (fun n => (tendsto_poch_sub_div_pow d n).mul_const (T n)) ?_).congr' ?_
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with κ hκ n
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (norm_poch_sub_div_pow_le d hκ n) (norm_nonneg _)
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with κ hκ
    exact (hL κ hκ.ne').symm

/-! ### The Liouville normal form -/

/-- Chain rule for a complex function of a real-valued real function. -/
theorem hasDerivAt_comp_ofReal_real {F : ℂ → ℂ} {F' : ℂ} {m : ℝ → ℝ} {m' s : ℝ}
    (hF : HasDerivAt F F' (m s : ℂ)) (hm : HasDerivAt m m' s) :
    HasDerivAt (fun t : ℝ => F (m t : ℂ)) (F' * m') s := by
  have := hF.comp_ofReal.scomp s hm
  rw [real_smul, mul_comm] at this
  exact this

theorem hasDerivAt_sq_div (κ s : ℝ) :
    HasDerivAt (fun t : ℝ => t ^ 2 / (4 * κ)) (s / (2 * κ)) s := by
  convert (hasDerivAt_pow 2 s).div_const (4 * κ) using 1
  norm_num
  ring

/-- `d/ds 𝐌(p, q, s²/(4κ)) = p 𝐌(p+1, q+1, s²/(4κ)) · s/(2κ)`. -/
theorem hasDerivAt_regularizedConfluent_sq_div (p q : ℂ) (κ s : ℝ) :
    HasDerivAt (fun t : ℝ => regularizedHGFun {p} {q} ((t ^ 2 / (4 * κ) : ℝ) : ℂ))
      (p * regularizedHGFun {p + 1} {q + 1} ((s ^ 2 / (4 * κ) : ℝ) : ℂ) *
        ((s / (2 * κ) : ℝ) : ℂ)) s := by
  have hF : HasDerivAt (regularizedHGFun {p} {q})
      (p * regularizedHGFun {p + 1} {q + 1} ((s ^ 2 / (4 * κ) : ℝ) : ℂ))
      ((s ^ 2 / (4 * κ) : ℝ) : ℂ) := by
    rw [← deriv_regularizedConfluent]
    exact (differentiableAt_regularizedConfluent p q _).hasDerivAt
  exact hasDerivAt_comp_ofReal_real (m := fun t : ℝ => t ^ 2 / (4 * κ)) hF
    (hasDerivAt_sq_div κ s)

/-- The parameter `a = c/2 - κ`. -/
def largeAParam (c κ : ℝ) : ℂ := ((c / 2 - κ : ℝ) : ℂ)

/-- `W(s) = 𝐌(c/2 - κ, c, s²/(4κ))`. -/
def largeAW (c κ s : ℝ) : ℂ :=
  regularizedHGFun {largeAParam c κ} {(c : ℂ)} ((s ^ 2 / (4 * κ) : ℝ) : ℂ)

/-- The derivative of `largeAW`. -/
def largeAW1 (c κ s : ℝ) : ℂ :=
  largeAParam c κ * regularizedHGFun {largeAParam c κ + 1} {(c : ℂ) + 1}
    ((s ^ 2 / (4 * κ) : ℝ) : ℂ) * ((s / (2 * κ) : ℝ) : ℂ)

/-- The gauge factor `s^{c-1/2} e^{-s²/(8κ)}`. -/
def largeAP (c κ s : ℝ) : ℝ := s ^ (c - 1 / 2) * Real.exp (-(s ^ 2 / (8 * κ)))

/-- The logarithmic derivative of the gauge factor. -/
def largeAH (c κ s : ℝ) : ℝ := (c - 1 / 2) / s - s / (4 * κ)

/-- The Liouville form `u(s) = s^{c-1/2} e^{-s²/(8κ)} 𝐌(c/2 - κ, c, s²/(4κ))`. -/
def largeAU (c κ s : ℝ) : ℂ := (largeAP c κ s : ℂ) * largeAW c κ s

/-- The derivative of `largeAU`. -/
def largeAU' (c κ s : ℝ) : ℂ :=
  (largeAP c κ s : ℂ) * ((largeAH c κ s : ℂ) * largeAW c κ s + largeAW1 c κ s)

/-- The potential: `u'' + u = g u` with `g = ((c-1)² - 1/4)/s² + s²/(16κ²)`. -/
def largeAG (c κ s : ℝ) : ℝ := ((c - 1) ^ 2 - 1 / 4) / s ^ 2 + s ^ 2 / (16 * κ ^ 2)

theorem hasDerivAt_largeAW (c κ s : ℝ) : HasDerivAt (largeAW c κ) (largeAW1 c κ s) s :=
  hasDerivAt_regularizedConfluent_sq_div _ _ κ s

theorem hasDerivAt_largeAW1 (c κ s : ℝ) :
    HasDerivAt (largeAW1 c κ)
      (largeAParam c κ * ((largeAParam c κ + 1) *
        regularizedHGFun {largeAParam c κ + 2} {(c : ℂ) + 2} ((s ^ 2 / (4 * κ) : ℝ) : ℂ) *
          ((s / (2 * κ) : ℝ) : ℂ) * ((s / (2 * κ) : ℝ) : ℂ) +
        regularizedHGFun {largeAParam c κ + 1} {(c : ℂ) + 1} ((s ^ 2 / (4 * κ) : ℝ) : ℂ) *
          ((1 / (2 * κ) : ℝ) : ℂ))) s := by
  have h1 := hasDerivAt_regularizedConfluent_sq_div (largeAParam c κ + 1) ((c : ℂ) + 1) κ s
  rw [show largeAParam c κ + 1 + 1 = largeAParam c κ + 2 by ring,
    show (c : ℂ) + 1 + 1 = c + 2 by ring] at h1
  have h2 : HasDerivAt (fun t : ℝ => ((t / (2 * κ) : ℝ) : ℂ)) ((1 / (2 * κ) : ℝ) : ℂ) s := by
    have := ((hasDerivAt_id s).div_const (2 * κ)).ofReal_comp
    simpa using this
  have := (h1.mul h2).const_mul (largeAParam c κ)
  convert this using 1
  · funext t
    simp only [largeAW1, Pi.mul_apply]
    ring

theorem hasDerivAt_largeAP (c κ : ℝ) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (largeAP c κ) (largeAP c κ s * largeAH c κ s) s := by
  have h1 := Real.hasDerivAt_rpow_const (x := s) (p := c - 1 / 2) (Or.inl hs.ne')
  have h2 : HasDerivAt (fun t : ℝ => Real.exp (-(t ^ 2 / (8 * κ))))
      (Real.exp (-(s ^ 2 / (8 * κ))) * -(s / (4 * κ))) s := by
    convert ((hasDerivAt_pow 2 s).div_const (8 * κ)).neg.exp using 1
    norm_num
    ring
  refine (h1.mul h2).congr_deriv ?_
  simp only [largeAP, largeAH]
  rw [Real.rpow_sub_one hs.ne']
  field_simp
  ring

theorem hasDerivAt_largeAU (c κ : ℝ) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (largeAU c κ) (largeAU' c κ s) s := by
  have hP := (hasDerivAt_largeAP c κ hs).ofReal_comp
  refine (hP.mul (hasDerivAt_largeAW c κ s)).congr_deriv ?_
  simp only [largeAU']
  push_cast
  ring

theorem hasDerivAt_largeAH (c κ : ℝ) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (largeAH c κ) (-(c - 1 / 2) / s ^ 2 - 1 / (4 * κ)) s := by
  have h1 : HasDerivAt (fun t : ℝ => (c - 1 / 2) / t) ((c - 1 / 2) * -(s ^ 2)⁻¹) s := by
    simpa [div_eq_mul_inv] using (hasDerivAt_inv hs.ne').const_mul (c - 1 / 2)
  have h2 : HasDerivAt (fun t : ℝ => t / (4 * κ)) (1 / (4 * κ)) s := by
    simpa using (hasDerivAt_id s).div_const (4 * κ)
  refine (h1.sub h2).congr_deriv ?_
  ring

/-- The Liouville normal form of Kummer's equation: `u'' = (g - 1) u`. -/
theorem hasDerivAt_largeAU' (c : ℝ) {κ : ℝ} (hκ : 0 < κ) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (largeAU' c κ) ((largeAG c κ s - 1) • largeAU c κ s) s := by
  have hP := (hasDerivAt_largeAP c κ hs).ofReal_comp
  have hH := (hasDerivAt_largeAH c κ hs).ofReal_comp
  have hW := hasDerivAt_largeAW c κ s
  have hW1 := hasDerivAt_largeAW1 c κ s
  refine (hP.mul ((hH.mul hW).add hW1)).congr_deriv ?_
  have hcont := regularizedConfluent_ode_contiguous (largeAParam c κ) (c : ℂ)
    ((s ^ 2 / (4 * κ) : ℝ) : ℂ)
  simp only [Pi.add_apply, Pi.mul_apply, largeAU, largeAW, largeAW1, largeAParam] at hcont ⊢
  set aR : ℝ := c / 2 - κ with haR
  set z : ℝ := s ^ 2 / (4 * κ) with hz
  set σ : ℝ := s / (2 * κ) with hσ
  set q : ℝ := 1 / (2 * κ) with hq
  set h : ℝ := largeAH c κ s with hh
  set G : ℝ := largeAG c κ s with hG
  set M0 := regularizedHGFun {(aR : ℂ)} {(c : ℂ)} (z : ℂ)
  set M1 := regularizedHGFun {(aR : ℂ) + 1} {(c : ℂ) + 1} (z : ℂ)
  set M2 := regularizedHGFun {(aR : ℂ) + 2} {(c : ℂ) + 2} (z : ℂ)
  have e0 : h ^ 2 + (-(c - 1 / 2) / s ^ 2 - 1 / (4 * κ)) - (G - 1) = -aR / κ := by
    simp only [hh, hG, haR, largeAH, largeAG]
    field_simp
    ring
  have e1 : 2 * h * σ + q = (c - z) / κ := by
    simp only [hh, hσ, hq, hz, largeAH]
    field_simp
    ring
  have e2 : σ * σ = z / κ := by
    simp only [hσ, hz]
    field_simp
    ring
  have e0c : (h : ℂ) ^ 2 + (((-(c - 1 / 2) / s ^ 2 - 1 / (4 * κ) : ℝ)) : ℂ) - ((G : ℂ) - 1) =
      -(aR : ℂ) / κ := by exact_mod_cast e0
  have e1c : 2 * (h : ℂ) * σ + q = ((c : ℂ) - z) / κ := by exact_mod_cast e1
  have e2c : (σ : ℂ) * σ = z / κ := by exact_mod_cast e2
  have hP' : ((largeAP c κ s * h : ℝ) : ℂ) = (largeAP c κ s : ℂ) * h := by push_cast; ring
  rw [hP', real_smul, ofReal_sub G 1, ofReal_one]
  linear_combination (largeAP c κ s : ℂ) * M0 * e0c + (largeAP c κ s : ℂ) * aR * M1 * e1c +
    (largeAP c κ s : ℂ) * aR * (aR + 1) * M2 * e2c +
    (largeAP c κ s : ℂ) * (aR / κ) * hcont

/-! ### The Bessel limit equation -/

/-- `V(s) = ₀F̃₁(;c;-s²/4)`. -/
def largeAV (c s : ℝ) : ℂ := regularizedHGFun (∅ : Multiset ℂ) {(c : ℂ)} ((-(s ^ 2 / 4) : ℝ) : ℂ)

/-- The derivative of `largeAV`. -/
def largeAV1 (c s : ℝ) : ℂ :=
  regularizedHGFun (∅ : Multiset ℂ) {(c : ℂ) + 1} ((-(s ^ 2 / 4) : ℝ) : ℂ) * ((-(s / 2) : ℝ) : ℂ)

/-- The gauge factor `s^{c-1/2}`. -/
def largeAQ (c s : ℝ) : ℝ := s ^ (c - 1 / 2)

/-- The logarithmic derivative of `largeAQ`. -/
def largeAH0 (c s : ℝ) : ℝ := (c - 1 / 2) / s

/-- The limit Liouville form `u₀(s) = s^{c-1/2} ₀F̃₁(;c;-s²/4) = 2^{c-1} √s J_{c-1}(s)`. -/
def largeAU0 (c s : ℝ) : ℂ := (largeAQ c s : ℂ) * largeAV c s

/-- The derivative of `largeAU0`. -/
def largeAU0' (c s : ℝ) : ℂ :=
  (largeAQ c s : ℂ) * ((largeAH0 c s : ℂ) * largeAV c s + largeAV1 c s)

/-- The limit potential `((c-1)² - 1/4)/s²`. -/
def largeAG0 (c s : ℝ) : ℝ := ((c - 1) ^ 2 - 1 / 4) / s ^ 2

theorem hasDerivAt_neg_sq_div_four (s : ℝ) :
    HasDerivAt (fun t : ℝ => -(t ^ 2 / 4)) (-(s / 2)) s := by
  convert ((hasDerivAt_pow 2 s).div_const 4).neg using 1
  norm_num
  ring

theorem hasDerivAt_largeAV (c s : ℝ) : HasDerivAt (largeAV c) (largeAV1 c s) s :=
  hasDerivAt_comp_ofReal_real (m := fun t : ℝ => -(t ^ 2 / 4))
    (DLMF.Bessel.hasDerivAt_regularized0F1 _ _) (hasDerivAt_neg_sq_div_four s)

theorem hasDerivAt_largeAV1 (c s : ℝ) :
    HasDerivAt (largeAV1 c)
      (regularizedHGFun (∅ : Multiset ℂ) {(c : ℂ) + 1 + 1} ((-(s ^ 2 / 4) : ℝ) : ℂ) *
          ((-(s / 2) : ℝ) : ℂ) * ((-(s / 2) : ℝ) : ℂ) +
        regularizedHGFun (∅ : Multiset ℂ) {(c : ℂ) + 1} ((-(s ^ 2 / 4) : ℝ) : ℂ) *
          ((-(1 / 2) : ℝ) : ℂ)) s := by
  have h1 := hasDerivAt_comp_ofReal_real (m := fun t : ℝ => -(t ^ 2 / 4))
    (DLMF.Bessel.hasDerivAt_regularized0F1 ((c : ℂ) + 1) _) (hasDerivAt_neg_sq_div_four s)
  have h2 : HasDerivAt (fun t : ℝ => ((-(t / 2) : ℝ) : ℂ)) ((-(1 / 2) : ℝ) : ℂ) s := by
    have := ((hasDerivAt_id s).div_const 2).neg.ofReal_comp
    simpa using this
  exact h1.mul h2

theorem hasDerivAt_largeAQ (c : ℝ) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (largeAQ c) (largeAQ c s * largeAH0 c s) s := by
  refine (Real.hasDerivAt_rpow_const (x := s) (p := c - 1 / 2) (Or.inl hs.ne')).congr_deriv ?_
  simp only [largeAQ, largeAH0]
  rw [Real.rpow_sub_one hs.ne']
  field_simp

theorem hasDerivAt_largeAU0 (c : ℝ) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (largeAU0 c) (largeAU0' c s) s := by
  have hP := (hasDerivAt_largeAQ c hs).ofReal_comp
  refine (hP.mul (hasDerivAt_largeAV c s)).congr_deriv ?_
  simp only [largeAU0']
  push_cast
  ring

theorem hasDerivAt_largeAH0 (c : ℝ) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (largeAH0 c) (-(c - 1 / 2) / s ^ 2) s := by
  have h1 : HasDerivAt (fun t : ℝ => (c - 1 / 2) / t) ((c - 1 / 2) * -(s ^ 2)⁻¹) s := by
    simpa [div_eq_mul_inv] using (hasDerivAt_inv hs.ne').const_mul (c - 1 / 2)
  refine h1.congr_deriv ?_
  ring

/-- The Liouville form of Bessel's equation: `u₀'' = (g₀ - 1) u₀`. -/
theorem hasDerivAt_largeAU0' (c : ℝ) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (largeAU0' c) ((largeAG0 c s - 1) • largeAU0 c s) s := by
  have hP := (hasDerivAt_largeAQ c hs).ofReal_comp
  have hH := (hasDerivAt_largeAH0 c hs).ofReal_comp
  refine (hP.mul ((hH.mul (hasDerivAt_largeAV c s)).add
    (hasDerivAt_largeAV1 c s))).congr_deriv ?_
  have hcont := DLMF.Bessel.regularized0F1_contiguous (c : ℂ) ((-(s ^ 2 / 4) : ℝ) : ℂ)
  simp only [Pi.add_apply, Pi.mul_apply, largeAU0, largeAV, largeAV1] at hcont ⊢
  set w : ℝ := -(s ^ 2 / 4) with hw
  set σ : ℝ := -(s / 2) with hσ
  set h : ℝ := largeAH0 c s with hh
  set G : ℝ := largeAG0 c s with hG
  set F0 := regularizedHGFun (∅ : Multiset ℂ) {(c : ℂ)} (w : ℂ)
  set F1 := regularizedHGFun (∅ : Multiset ℂ) {(c : ℂ) + 1} (w : ℂ)
  set F2 := regularizedHGFun (∅ : Multiset ℂ) {(c : ℂ) + 1 + 1} (w : ℂ)
  have e0 : h ^ 2 + (-(c - 1 / 2) / s ^ 2) - (G - 1) = 1 := by
    simp only [hh, hG, largeAH0, largeAG0]
    field_simp
    ring
  have e1 : 2 * h * σ + (-(1 / 2)) = -c := by
    simp only [hh, hσ, largeAH0]
    field_simp
    ring
  have e2 : σ * σ = -w := by
    simp only [hσ, hw]
    ring
  have e0c : (h : ℂ) ^ 2 + ((-(c - 1 / 2) / s ^ 2 : ℝ) : ℂ) - ((G : ℂ) - 1) = 1 := by
    exact_mod_cast e0
  have e1c : 2 * (h : ℂ) * σ + ((-(1 / 2) : ℝ) : ℂ) = -c := by exact_mod_cast e1
  have e2c : (σ : ℂ) * σ = -w := by exact_mod_cast e2
  have hP' : ((largeAQ c s * h : ℝ) : ℂ) = (largeAQ c s : ℂ) * h := by push_cast; ring
  rw [hP', real_smul, ofReal_sub G 1, ofReal_one]
  linear_combination (largeAQ c s : ℂ) * F0 * e0c + (largeAQ c s : ℂ) * F1 * e1c +
    (largeAQ c s : ℂ) * F2 * e2c + (largeAQ c s : ℂ) * hcont

/-! ### Convergence of the data at a fixed point -/

theorem tendsto_div_atTop_zero (b : ℝ) : Tendsto (fun κ : ℝ => b / κ) atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop tendsto_id

theorem tendsto_largeAW (c s : ℝ) :
    Tendsto (fun κ : ℝ => largeAW c κ s) atTop (𝓝 (largeAV c s)) := by
  have h := tendsto_regularizedConfluent_sub_div (c / 2) (c : ℂ) ((s ^ 2 / 4 : ℝ) : ℂ)
  have hV : largeAV c s = regularizedHGFun (∅ : Multiset ℂ) {(c : ℂ)} (-((s ^ 2 / 4 : ℝ) : ℂ)) := by
    simp only [largeAV]
    push_cast
    ring_nf
  rw [hV]
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with κ hκ
  have hκ' : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ.ne'
  simp only [largeAW, largeAParam]
  congr 2
  push_cast
  field_simp

theorem tendsto_largeAW1 (c s : ℝ) :
    Tendsto (fun κ : ℝ => largeAW1 c κ s) atTop (𝓝 (largeAV1 c s)) := by
  have h := tendsto_regularizedConfluent_sub_div (c / 2 + 1) ((c : ℂ) + 1) ((s ^ 2 / 4 : ℝ) : ℂ)
  have ha : Tendsto (fun κ : ℝ => (((c / 2) / κ - 1 : ℝ) : ℂ)) atTop (𝓝 ((0 - 1 : ℝ) : ℂ)) :=
    (continuous_ofReal.tendsto _).comp ((tendsto_div_atTop_zero (c / 2)).sub_const 1)
  have := (ha.mul h).mul_const ((s / 2 : ℝ) : ℂ)
  have hV : largeAV1 c s = ((0 - 1 : ℝ) : ℂ) *
      regularizedHGFun (∅ : Multiset ℂ) {(c : ℂ) + 1} (-((s ^ 2 / 4 : ℝ) : ℂ)) *
        ((s / 2 : ℝ) : ℂ) := by
    simp only [largeAV1]
    push_cast
    ring_nf
  rw [hV]
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with κ hκ
  have hκ' : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ.ne'
  simp only [largeAW1, largeAParam]
  have harg : (((s ^ 2 / 4 : ℝ) : ℂ) / κ) = ((s ^ 2 / (4 * κ) : ℝ) : ℂ) := by
    push_cast
    field_simp
  have hpar : (((c / 2 + 1 - κ : ℝ)) : ℂ) = ((c / 2 - κ : ℝ) : ℂ) + 1 := by push_cast; ring
  rw [harg, hpar]
  push_cast
  field_simp

theorem tendsto_largeAP (c s : ℝ) :
    Tendsto (fun κ : ℝ => largeAP c κ s) atTop (𝓝 (largeAQ c s)) := by
  have h : Tendsto (fun κ : ℝ => Real.exp (-(s ^ 2 / 8 / κ))) atTop (𝓝 (Real.exp (-0))) :=
    (Real.continuous_exp.tendsto _).comp (tendsto_div_atTop_zero _).neg
  rw [neg_zero, Real.exp_zero] at h
  have := h.const_mul (s ^ (c - 1 / 2))
  rw [mul_one] at this
  refine this.congr' ?_
  filter_upwards with κ
  simp only [largeAP]
  congr 3
  ring

theorem tendsto_largeAH (c s : ℝ) :
    Tendsto (fun κ : ℝ => largeAH c κ s) atTop (𝓝 (largeAH0 c s)) := by
  have := (tendsto_div_atTop_zero (s / 4)).const_sub ((c - 1 / 2) / s)
  rw [sub_zero] at this
  refine this.congr' ?_
  filter_upwards with κ
  simp only [largeAH]
  ring

theorem tendsto_largeAU (c s : ℝ) :
    Tendsto (fun κ : ℝ => largeAU c κ s) atTop (𝓝 (largeAU0 c s)) :=
  ((continuous_ofReal.tendsto _).comp (tendsto_largeAP c s)).mul (tendsto_largeAW c s)

theorem tendsto_largeAU' (c s : ℝ) :
    Tendsto (fun κ : ℝ => largeAU' c κ s) atTop (𝓝 (largeAU0' c s)) :=
  ((continuous_ofReal.tendsto _).comp (tendsto_largeAP c s)).mul
    ((((continuous_ofReal.tendsto _).comp (tendsto_largeAH c s)).mul
      (tendsto_largeAW c s)).add (tendsto_largeAW1 c s))

/-! ### The limit in terms of Bessel functions -/

/-- `J_μ(s) = (s/2)^μ ₀F̃₁(;μ+1;-s²/4)` for real `s > 0` and real `μ`. -/
theorem besselJ_ofReal_eq (μ : ℝ) {s : ℝ} (hs : 0 < s) :
    besselJ (μ : ℂ) (s : ℂ) = (((s / 2) ^ μ : ℝ) : ℂ) *
      regularizedHGFun (∅ : Multiset ℂ) {(μ : ℂ) + 1} ((-(s ^ 2 / 4) : ℝ) : ℂ) := by
  rw [DLMF.Bessel.besselJ_eq_regularized, ofReal_cpow (by positivity)]
  push_cast
  ring_nf

theorem rpow_identity {c s : ℝ} (hs : 0 < s) :
    (2 : ℝ) ^ (c - 1) * Real.sqrt s * (s / 2) ^ (c - 1) = s ^ (c - 1 / 2) := by
  have h2 : (0 : ℝ) < 2 ^ (c - 1) := by positivity
  rw [Real.div_rpow hs.le (by norm_num), Real.sqrt_eq_rpow,
    show c - 1 / 2 = 1 / 2 + (c - 1) by ring, Real.rpow_add hs]
  field_simp

theorem rpow_identity' {c s : ℝ} (hs : 0 < s) :
    (2 : ℝ) ^ (c - 1) * Real.sqrt s * (s / 2) ^ c = s ^ (c - 1 / 2) * (s / 2) := by
  have h := rpow_identity (c := c) hs
  have e : (s / 2) ^ c = (s / 2) ^ (c - 1) * (s / 2) := by
    rw [Real.rpow_sub_one (by positivity)]
    field_simp
  rw [e, ← h]
  ring

/-- `u₀(s) = 2^{c-1} √s J_{c-1}(s)`. -/
theorem largeAU0_eq (c : ℝ) {s : ℝ} (hs : 0 < s) :
    largeAU0 c s = (((2 : ℝ) ^ (c - 1) : ℝ) : ℂ) *
      ((Real.sqrt s : ℝ) * besselJ ((c - 1 : ℝ) : ℂ) (s : ℂ)) := by
  rw [besselJ_ofReal_eq _ hs, largeAU0, largeAQ, largeAV, ← rpow_identity (c := c) hs]
  push_cast
  ring_nf

/-- `u₀'(s) = 2^{c-1} ((c - 1/2)/s · √s J_{c-1}(s) - √s J_c(s))`. -/
lemma largeAU0'_eq (c : ℝ) {s : ℝ} (hs : 0 < s) :
    largeAU0' c s = (((2 : ℝ) ^ (c - 1) : ℝ) : ℂ) *
      ((((c - 1 / 2) / s : ℝ) : ℂ) * ((Real.sqrt s : ℝ) * besselJ ((c - 1 : ℝ) : ℂ) (s : ℂ)) -
        (Real.sqrt s : ℝ) * besselJ (c : ℂ) (s : ℂ)) := by
  have h1 := largeAU0_eq c hs
  rw [largeAU0] at h1
  rw [largeAU0', mul_add, ← mul_assoc, mul_comm (largeAQ c s : ℂ), mul_assoc, h1,
    besselJ_ofReal_eq c hs, largeAV1, largeAH0]
  have hq : (largeAQ c s : ℂ) * ((-(s / 2) : ℝ) : ℂ) =
      -((((2 : ℝ) ^ (c - 1) * Real.sqrt s * (s / 2) ^ c) : ℝ) : ℂ) := by
    rw [rpow_identity' hs, largeAQ]
    push_cast
    ring
  have hF : regularizedHGFun (∅ : Multiset ℂ) {(c : ℂ) + 1} ((-(s ^ 2 / 4) : ℝ) : ℂ) *
      ((largeAQ c s : ℂ) * ((-(s / 2) : ℝ) : ℂ)) = largeAQ c s *
        (regularizedHGFun (∅ : Multiset ℂ) {(c : ℂ) + 1} ((-(s ^ 2 / 4) : ℝ) : ℂ) *
          ((-(s / 2) : ℝ) : ℂ)) := by ring
  rw [← hF, hq]
  push_cast
  ring

/-- `√s J_μ(s) = O(1)` as `s → +∞`, for real `μ`. -/
theorem sqrt_mul_besselJ_isBigO (μ : ℝ) :
    (fun s : ℝ => ((Real.sqrt s : ℝ) : ℂ) * besselJ (μ : ℂ) (s : ℂ)) =O[atTop]
      (fun _ => (1 : ℝ)) := by
  have hJ := DLMF.Bessel.besselJ_sub_cos_isBigO (μ : ℂ)
  have h0 : (fun s : ℝ => ((Real.sqrt s : ℝ) : ℂ)) =O[atTop] (fun s => Real.sqrt s) :=
    Asymptotics.IsBigO.of_bound 1 (by filter_upwards with s; simp)
  have h1 := h0.mul hJ
  have h2 : (fun s : ℝ => Real.sqrt s * s ^ (-(3 / 2) : ℝ)) =O[atTop] (fun _ => (1 : ℝ)) := by
    refine Asymptotics.IsBigO.of_bound 1 ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with s hs
    have hs0 : 0 < s := by linarith
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), norm_one, one_mul,
      Real.norm_eq_abs, abs_of_nonneg (by positivity), Real.sqrt_eq_rpow, ← Real.rpow_add hs0]
    exact Real.rpow_le_one_of_one_le_of_nonpos hs (by norm_num)
  have h3 : (fun s : ℝ => ((Real.sqrt s : ℝ) : ℂ) *
      ((Real.sqrt (2 / (π * s)) : ℂ) * cos (s - (μ : ℂ) * π / 2 - π / 4))) =O[atTop]
      (fun _ => (1 : ℝ)) := by
    refine Asymptotics.IsBigO.of_bound (Real.sqrt (2 / π)) ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
    rw [norm_one, mul_one, ← mul_assoc, norm_mul]
    have hc : cos ((s : ℂ) - (μ : ℂ) * π / 2 - π / 4) =
        ((Real.cos (s - μ * π / 2 - π / 4) : ℝ) : ℂ) := by push_cast; rfl
    rw [hc, Complex.norm_real, Real.norm_eq_abs]
    have hsq : ((Real.sqrt s : ℝ) : ℂ) * (Real.sqrt (2 / (π * s)) : ℂ) =
        ((Real.sqrt (2 / π) : ℝ) : ℂ) := by
      rw [← ofReal_mul, ← Real.sqrt_mul hs.le]
      congr 2
      field_simp
    rw [hsq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact mul_le_of_le_one_right (Real.sqrt_nonneg _) (Real.abs_cos_le_one _)
  have h4 := (h1.trans h2).add h3
  refine h4.congr_left fun s => ?_
  ring

/-! ### Matching on `[s₀, S]` -/

theorem integral_recip_sq_eq (A : ℝ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ t in a..b, A / t ^ 2 = A / a - A / b := by
  have hderiv : ∀ t ∈ uIcc a b, HasDerivAt (fun t : ℝ => -(A / t)) (A / t ^ 2) t := by
    intro t ht
    rw [uIcc_of_le hab] at ht
    have ht0 : t ≠ 0 := (lt_of_lt_of_le ha ht.1).ne'
    have := ((hasDerivAt_inv ht0).const_mul A).neg
    convert this using 1
    · funext y
      simp [div_eq_mul_inv]
    · field_simp
  have hcont : ContinuousOn (fun t : ℝ => A / t ^ 2) (uIcc a b) := by
    rw [uIcc_of_le hab]
    refine continuousOn_const.div (continuousOn_pow 2) fun t ht => ?_
    exact pow_ne_zero 2 (lt_of_lt_of_le ha ht.1).ne'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable)]
  ring

theorem continuousOn_largeAG (c κ : ℝ) {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (largeAG c κ) (Icc a b) := by
  refine ContinuousOn.add (continuousOn_const.div (continuousOn_pow 2) fun t ht => ?_)
    (by fun_prop)
  exact pow_ne_zero 2 (lt_of_lt_of_le ha ht.1).ne'

theorem continuousOn_largeAG0 (c : ℝ) {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (largeAG0 c) (Icc a b) :=
  continuousOn_const.div (continuousOn_pow 2) fun _t ht =>
    pow_ne_zero 2 (lt_of_lt_of_le ha ht.1).ne'

theorem integral_abs_largeAG_le (c : ℝ) {κ a b : ℝ} (hκ : 0 < κ) (ha : 0 < a) (hab : a ≤ b) :
    ∫ t in a..b, |largeAG c κ t| ≤ |(c - 1) ^ 2 - 1 / 4| / a + b ^ 3 / (16 * κ ^ 2) := by
  set A := |(c - 1) ^ 2 - 1 / 4|
  have hle : ∫ t in a..b, |largeAG c κ t| ≤
      ∫ t in a..b, (A / t ^ 2 + b ^ 2 / (16 * κ ^ 2)) := by
    refine intervalIntegral.integral_mono_on hab
      ((continuousOn_largeAG c κ ha).abs.intervalIntegrable_of_Icc hab) ?_ ?_
    · refine (ContinuousOn.add (continuousOn_const.div (continuousOn_pow 2) fun t ht => ?_)
        continuousOn_const).intervalIntegrable_of_Icc hab
      exact pow_ne_zero 2 (lt_of_lt_of_le ha ht.1).ne'
    · intro t ht
      have ht0 : 0 < t := lt_of_lt_of_le ha ht.1
      simp only [largeAG]
      refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < t ^ 2)]
      · rw [abs_of_nonneg (by positivity)]
        gcongr
        exact ht.2
  have hint : ∫ t in a..b, (A / t ^ 2 + b ^ 2 / (16 * κ ^ 2)) =
      (A / a - A / b) + (b - a) * (b ^ 2 / (16 * κ ^ 2)) := by
    rw [intervalIntegral.integral_add, integral_recip_sq_eq A ha hab,
      intervalIntegral.integral_const, smul_eq_mul]
    · refine (continuousOn_const.div (continuousOn_pow 2) fun t ht => ?_).intervalIntegrable
      rw [uIcc_of_le hab] at ht
      exact pow_ne_zero 2 (lt_of_lt_of_le ha ht.1).ne'
    · exact intervalIntegrable_const
  rw [hint] at hle
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have h1 : 0 ≤ A / b := by positivity
  have h2 : (b - a) * (b ^ 2 / (16 * κ ^ 2)) ≤ b ^ 3 / (16 * κ ^ 2) := by
    rw [show b ^ 3 / (16 * κ ^ 2) = b * (b ^ 2 / (16 * κ ^ 2)) by ring]
    exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  linarith

theorem integral_abs_largeAG0_le (c : ℝ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ t in a..b, |largeAG0 c t| ≤ |(c - 1) ^ 2 - 1 / 4| / a := by
  have heq : ∀ t ∈ Icc a b, |largeAG0 c t| = |(c - 1) ^ 2 - 1 / 4| / t ^ 2 := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le ha ht.1
    rw [largeAG0, abs_div, abs_of_pos (by positivity : (0 : ℝ) < t ^ 2)]
  rw [intervalIntegral.integral_congr (g := fun t => |(c - 1) ^ 2 - 1 / 4| / t ^ 2)
    (by rw [uIcc_of_le hab]; exact heq), integral_recip_sq_eq _ ha hab]
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have : 0 ≤ |(c - 1) ^ 2 - 1 / 4| / b := by positivity
  linarith

theorem oscFree_sub (ω a : ℝ) (c d c' d' : ℂ) (x : ℝ) :
    ODE.oscFree ω a c d x - ODE.oscFree ω a c' d' x = ODE.oscFree ω a (c - c') (d - d') x := by
  simp only [ODE.oscFree, smul_sub]
  abel

/-- The matching estimate on `[s₀, S]`, from the Volterra perturbation bound. -/
theorem norm_largeAU_sub_largeAU0_le (c : ℝ) {κ s₀ S : ℝ} (hκ : 0 < κ) (hs₀ : 0 < s₀)
    (hS : s₀ ≤ S) :
    ‖largeAU c κ S - largeAU0 c S‖ ≤
      (‖largeAU c κ s₀‖ + ‖largeAU' c κ s₀‖) *
          (Real.exp (|(c - 1) ^ 2 - 1 / 4| / s₀ + S ^ 3 / (16 * κ ^ 2)) - 1) +
        (‖largeAU c κ s₀ - largeAU0 c s₀‖ + ‖largeAU' c κ s₀ - largeAU0' c s₀‖) +
        (‖largeAU0 c s₀‖ + ‖largeAU0' c s₀‖) *
          (Real.exp (|(c - 1) ^ 2 - 1 / 4| / s₀) - 1) := by
  have hpos : ∀ t ∈ Icc s₀ S, 0 < t := fun t ht => lt_of_lt_of_le hs₀ ht.1
  have hSmem : S ∈ Icc s₀ S := ⟨hS, le_rfl⟩
  have h1 := ODE.norm_sub_oscFree_le' (E := ℂ) (ω := 1) one_ne_zero
    (continuousOn_largeAG c κ hs₀) (fun t ht => hasDerivAt_largeAU c κ (hpos t ht))
    (fun t ht => by simpa using hasDerivAt_largeAU' c hκ (hpos t ht)) hSmem
  have h0 := ODE.norm_sub_oscFree_le' (E := ℂ) (ω := 1) one_ne_zero
    (continuousOn_largeAG0 c hs₀) (fun t ht => hasDerivAt_largeAU0 c (hpos t ht))
    (fun t ht => by simpa using hasDerivAt_largeAU0' c (hpos t ht)) hSmem
  simp only [abs_one, div_one] at h1 h0
  have hI := integral_abs_largeAG_le c hκ hs₀ hS
  have hI0 := integral_abs_largeAG0_le c hs₀ hS
  have hosc := ODE.norm_oscFree_le 1 s₀ (largeAU c κ s₀ - largeAU0 c s₀)
    (largeAU' c κ s₀ - largeAU0' c s₀) S
  simp only [abs_one, div_one] at hosc
  rw [← oscFree_sub] at hosc
  have hD : largeAU c κ S - largeAU0 c S =
      (largeAU c κ S - ODE.oscFree 1 s₀ (largeAU c κ s₀) (largeAU' c κ s₀) S) +
        (ODE.oscFree 1 s₀ (largeAU c κ s₀) (largeAU' c κ s₀) S -
          ODE.oscFree 1 s₀ (largeAU0 c s₀) (largeAU0' c s₀) S) -
        (largeAU0 c S - ODE.oscFree 1 s₀ (largeAU0 c s₀) (largeAU0' c s₀) S) := by abel
  rw [hD]
  have he1 : Real.exp (∫ t in s₀..S, |largeAG c κ t|) - 1 ≤
      Real.exp (|(c - 1) ^ 2 - 1 / 4| / s₀ + S ^ 3 / (16 * κ ^ 2)) - 1 := by
    gcongr
  have he0 : Real.exp (∫ t in s₀..S, |largeAG0 c t|) - 1 ≤
      Real.exp (|(c - 1) ^ 2 - 1 / 4| / s₀) - 1 := by
    gcongr
  have hn1 : 0 ≤ ‖largeAU c κ s₀‖ + ‖largeAU' c κ s₀‖ := by positivity
  have hn0 : 0 ≤ ‖largeAU0 c s₀‖ + ‖largeAU0' c s₀‖ := by positivity
  calc _ ≤ ‖largeAU c κ S - ODE.oscFree 1 s₀ (largeAU c κ s₀) (largeAU' c κ s₀) S‖ +
        ‖ODE.oscFree 1 s₀ (largeAU c κ s₀) (largeAU' c κ s₀) S -
          ODE.oscFree 1 s₀ (largeAU0 c s₀) (largeAU0' c s₀) S‖ +
        ‖largeAU0 c S - ODE.oscFree 1 s₀ (largeAU0 c s₀) (largeAU0' c s₀) S‖ :=
        norm_sub_le_of_le (norm_add_le _ _) le_rfl
    _ ≤ _ := by
        gcongr
        · exact h1.trans (mul_le_mul_of_nonneg_left he1 hn1)
        · exact h0.trans (mul_le_mul_of_nonneg_left he0 hn0)

/-! ### The limit -/

lemma largeAU0_isBigO (c : ℝ) : largeAU0 c =O[atTop] (fun _ => (1 : ℝ)) := by
  refine ((sqrt_mul_besselJ_isBigO (c - 1)).const_mul_left
    (((2 : ℝ) ^ (c - 1) : ℝ) : ℂ)).congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
  exact (largeAU0_eq c hs).symm

lemma largeAU0'_isBigO (c : ℝ) : largeAU0' c =O[atTop] (fun _ => (1 : ℝ)) := by
  have hr : Tendsto (fun s : ℝ => ((((c - 1 / 2) / s : ℝ)) : ℂ)) atTop (𝓝 0) := by
    have := (continuous_ofReal.tendsto 0).comp (tendsto_div_atTop_zero (c - 1 / 2))
    simpa only [Function.comp_def, ofReal_zero] using this
  have h1 := (hr.isBigO_one ℝ).mul (sqrt_mul_besselJ_isBigO (c - 1))
  simp only [mul_one] at h1
  have h2 := (h1.sub (sqrt_mul_besselJ_isBigO c)).const_mul_left
    (((2 : ℝ) ^ (c - 1) : ℝ) : ℂ)
  refine h2.congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
  exact (largeAU0'_eq c hs).symm

theorem exists_bound_largeAU0 (c : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ s in atTop, ‖largeAU0 c s‖ + ‖largeAU0' c s‖ ≤ B := by
  obtain ⟨C0, hC0⟩ := (largeAU0_isBigO c).bound
  obtain ⟨C1, hC1⟩ := (largeAU0'_isBigO c).bound
  refine ⟨|C0| + |C1|, by positivity, ?_⟩
  filter_upwards [hC0, hC1] with s h0 h1
  simp only [norm_one, mul_one] at h0 h1
  linarith [le_abs_self C0, le_abs_self C1]

theorem tendsto_two_sqrt_mul (x : ℝ) (hx : 0 < x) :
    Tendsto (fun κ : ℝ => 2 * Real.sqrt (κ * x)) atTop atTop :=
  (Real.tendsto_sqrt_atTop.comp (tendsto_id.atTop_mul_const hx)).const_mul_atTop two_pos

theorem tendsto_cube_div (x : ℝ) (hx : 0 < x) :
    Tendsto (fun κ : ℝ => (2 * Real.sqrt (κ * x)) ^ 3 / (16 * κ ^ 2)) atTop (𝓝 0) := by
  have h : Tendsto (fun κ : ℝ => x * Real.sqrt x / (2 * Real.sqrt κ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.const_mul_atTop two_pos)
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with κ hκ
  have hsk : 0 < Real.sqrt κ := Real.sqrt_pos.mpr hκ
  have hk : Real.sqrt κ ^ 2 = κ := Real.sq_sqrt hκ.le
  have hxx : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx.le
  rw [Real.sqrt_mul hκ.le]
  set a := Real.sqrt κ
  set b := Real.sqrt x
  rw [← hk, ← hxx]
  field_simp
  ring

/-- The matching limit: `u_κ(S) - u₀(S) → 0` along `S = 2√(κx)`, as `κ → +∞`. -/
theorem tendsto_largeAU_sub_largeAU0 (c : ℝ) {x : ℝ} (hx : 0 < x) :
    Tendsto (fun κ : ℝ => largeAU c κ (2 * Real.sqrt (κ * x)) -
      largeAU0 c (2 * Real.sqrt (κ * x))) atTop (𝓝 0) := by
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = |(c - 1) ^ 2 - 1 / 4| := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := hA ▸ abs_nonneg _
  obtain ⟨B, hB0, hB⟩ := exists_bound_largeAU0 c
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hcont : Tendsto (fun η : ℝ => (2 * B + 2) * (Real.exp (2 * η) - 1) + η) (𝓝 0)
      (𝓝 0) := by
    have hc : Continuous (fun η : ℝ => (2 * B + 2) * (Real.exp (2 * η) - 1) + η) := by
      fun_prop
    simpa using hc.tendsto 0
  obtain ⟨η, hη0, hη1, hηε⟩ : ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧
      (2 * B + 2) * (Real.exp (2 * η) - 1) + η < ε := by
    have := hcont.eventually (gt_mem_nhds hε)
    rw [Metric.eventually_nhds_iff] at this
    obtain ⟨δ, hδ, hδ'⟩ := this
    refine ⟨min (δ / 2) 1, by positivity, min_le_right _ _, hδ' ?_⟩
    rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)]
    exact (min_le_left _ _).trans_lt (half_lt_self hδ)
  obtain ⟨s₀, hs₀B, hs₀1, hs₀A⟩ :=
    (hB.and ((eventually_ge_atTop (1 : ℝ)).and (eventually_ge_atTop (A / η)))).exists
  have hs₀ : 0 < s₀ := by linarith
  have hAs : A / s₀ ≤ η := by
    rw [div_le_iff₀ hs₀]
    have := (div_le_iff₀ hη0).mp hs₀A
    linarith
  have hδ : Tendsto (fun κ : ℝ => ‖largeAU c κ s₀ - largeAU0 c s₀‖ +
      ‖largeAU' c κ s₀ - largeAU0' c s₀‖) atTop (𝓝 0) := by
    have h1 := (tendsto_iff_norm_sub_tendsto_zero.mp (tendsto_largeAU c s₀))
    have h2 := (tendsto_iff_norm_sub_tendsto_zero.mp (tendsto_largeAU' c s₀))
    simpa using h1.add h2
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    (tendsto_two_sqrt_mul x hx).eventually_ge_atTop s₀,
    (tendsto_cube_div x hx).eventually (ge_mem_nhds hη0),
    hδ.eventually (ge_mem_nhds hη0)] with κ hκ hS hcube hδκ
  set S := 2 * Real.sqrt (κ * x)
  have hb := norm_largeAU_sub_largeAU0_le c hκ hs₀ hS
  rw [← hA] at hb
  rw [dist_zero_right]
  set δ := ‖largeAU c κ s₀ - largeAU0 c s₀‖ + ‖largeAU' c κ s₀ - largeAU0' c s₀‖
  have hN : ‖largeAU c κ s₀‖ + ‖largeAU' c κ s₀‖ ≤ B + η := by
    have h1 := norm_le_norm_add_norm_sub' (largeAU c κ s₀) (largeAU0 c s₀)
    have h2 := norm_le_norm_add_norm_sub' (largeAU' c κ s₀) (largeAU0' c s₀)
    linarith
  have hE : 0 ≤ Real.exp (2 * η) - 1 := by
    have := Real.add_one_le_exp (2 * η)
    linarith
  have he1 : Real.exp (A / s₀ + S ^ 3 / (16 * κ ^ 2)) - 1 ≤ Real.exp (2 * η) - 1 := by
    gcongr
    linarith
  have he0 : Real.exp (A / s₀) - 1 ≤ Real.exp (2 * η) - 1 := by
    gcongr
    linarith
  have hE1 : 0 ≤ Real.exp (A / s₀ + S ^ 3 / (16 * κ ^ 2)) - 1 := by
    have := Real.add_one_le_exp (A / s₀ + S ^ 3 / (16 * κ ^ 2))
    have : 0 ≤ A / s₀ + S ^ 3 / (16 * κ ^ 2) := by positivity
    linarith
  have hE0 : 0 ≤ Real.exp (A / s₀) - 1 := by
    have := Real.add_one_le_exp (A / s₀)
    have : 0 ≤ A / s₀ := by positivity
    linarith
  have t1 := mul_le_mul hN he1 hE1 (by positivity)
  have t2 := mul_le_mul hs₀B he0 hE0 hB0
  have t3 : (B + η) * (Real.exp (2 * η) - 1) ≤ (B + 1) * (Real.exp (2 * η) - 1) :=
    mul_le_mul_of_nonneg_right (by linarith) hE
  linarith

/-- `u₀(S) = 2^{c-1} √(2/π) cos(S - cπ/2 + π/4) + o(1)` as `S → +∞`. -/
theorem tendsto_largeAU0_sub_cos (c : ℝ) :
    Tendsto (fun S : ℝ => largeAU0 c S -
      (((2 : ℝ) ^ (c - 1) * Real.sqrt (2 / π) * Real.cos (S - c * π / 2 + π / 4) : ℝ) : ℂ))
      atTop (𝓝 0) := by
  have hJ := DLMF.Bessel.besselJ_sub_cos_isBigO ((c - 1 : ℝ) : ℂ)
  have h0 : (fun s : ℝ => ((((2 : ℝ) ^ (c - 1) * Real.sqrt s : ℝ)) : ℂ)) =O[atTop]
      (fun s => (2 : ℝ) ^ (c - 1) * Real.sqrt s) :=
    Asymptotics.IsBigO.of_bound 1 (by
      filter_upwards with s
      rw [Complex.norm_real, one_mul])
  have h1 := h0.mul hJ
  have h2 : Tendsto (fun s : ℝ => (2 : ℝ) ^ (c - 1) * Real.sqrt s * s ^ (-(3 / 2) : ℝ)) atTop
      (𝓝 0) := by
    have : Tendsto (fun s : ℝ => (2 : ℝ) ^ (c - 1) * s⁻¹) atTop (𝓝 ((2 : ℝ) ^ (c - 1) * 0)) :=
      tendsto_inv_atTop_zero.const_mul _
    rw [mul_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
    rw [Real.sqrt_eq_rpow, mul_assoc, ← Real.rpow_add hs, ← Real.rpow_neg_one]
    norm_num
  refine (h1.trans_tendsto h2).congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
  rw [largeAU0_eq c hs]
  have hsq : Real.sqrt s * Real.sqrt (2 / (π * s)) = Real.sqrt (2 / π) := by
    rw [← Real.sqrt_mul hs.le]
    congr 1
    field_simp
  have hc : cos ((s : ℂ) - ((c - 1 : ℝ) : ℂ) * π / 2 - π / 4) =
      ((Real.cos (s - c * π / 2 + π / 4) : ℝ) : ℂ) := by
    rw [show s - c * π / 2 + π / 4 = s - (c - 1) * π / 2 - π / 4 by ring]
    push_cast
    rfl
  rw [hc]
  have hsq' : ((Real.sqrt s : ℝ) : ℂ) * ((Real.sqrt (2 / (π * s)) : ℝ) : ℂ) =
      ((Real.sqrt (2 / π) : ℝ) : ℂ) := by
    rw [← ofReal_mul, hsq]
  simp only [ofReal_mul]
  linear_combination (-(((2 : ℝ) ^ (c - 1) : ℝ) : ℂ) *
    ((Real.cos (s - c * π / 2 + π / 4) : ℝ) : ℂ)) * hsq'

/-- **Large-`a` asymptotics in Liouville form**: with `κ = c/2 - a` and `S = 2√(κx)`,
`S^{c-1/2} e^{-x/2} 𝐌(a, c, x) = 2^{c-1} √(2/π) cos(S - cπ/2 + π/4) + o(1)` as `κ → +∞`. -/
theorem tendsto_largeAU_sub_cos (c : ℝ) {x : ℝ} (hx : 0 < x) :
    Tendsto (fun κ : ℝ => largeAU c κ (2 * Real.sqrt (κ * x)) -
      (((2 : ℝ) ^ (c - 1) * Real.sqrt (2 / π) *
        Real.cos (2 * Real.sqrt (κ * x) - c * π / 2 + π / 4) : ℝ) : ℂ)) atTop (𝓝 0) := by
  have := (tendsto_largeAU_sub_largeAU0 c hx).add
    ((tendsto_largeAU0_sub_cos c).comp (tendsto_two_sqrt_mul x hx))
  rw [add_zero] at this
  refine this.congr' (Eventually.of_forall fun κ => ?_)
  simp only [Function.comp_apply]
  ring

theorem two_rpow_mul_two_sqrt_rpow {y : ℝ} (hy : 0 ≤ y) (c : ℝ) :
    (2 : ℝ) ^ (1 / 2 - c) * (2 * Real.sqrt y) ^ (c - 1 / 2) = y ^ (c / 2 - 1 / 4) := by
  rw [Real.mul_rpow (by norm_num) (Real.sqrt_nonneg _), Real.sqrt_eq_rpow, ← Real.rpow_mul hy,
    ← mul_assoc, ← Real.rpow_add two_pos, show 1 / 2 - c + (c - 1 / 2) = 0 by ring,
    Real.rpow_zero, one_mul]
  congr 1
  ring

theorem two_rpow_sqrt_pi_mul (c : ℝ) :
    (2 : ℝ) ^ (1 / 2 - c) * Real.sqrt π * ((2 : ℝ) ^ (c - 1) * Real.sqrt (2 / π)) = 1 := by
  have h1 : Real.sqrt π * Real.sqrt (2 / π) = Real.sqrt 2 := by
    rw [← Real.sqrt_mul Real.pi_pos.le]
    congr 1
    field_simp
  have h2 : (2 : ℝ) ^ (1 / 2 - c) * (2 : ℝ) ^ (c - 1) = (2 : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [← Real.rpow_add two_pos]
    congr 1
    ring
  calc (2 : ℝ) ^ (1 / 2 - c) * Real.sqrt π * ((2 : ℝ) ^ (c - 1) * Real.sqrt (2 / π))
      = ((2 : ℝ) ^ (1 / 2 - c) * (2 : ℝ) ^ (c - 1)) * (Real.sqrt π * Real.sqrt (2 / π)) := by
        ring
    _ = 1 := by
        rw [h1, h2, Real.sqrt_eq_rpow, ← Real.rpow_add two_pos]
        norm_num

/-- **The Erdélyi–Schmidt–Fejér asymptotics** (Beals–Wong (8.1.12), (13.2.8)): for real `c`
and fixed `x > 0`, as `a → -∞`,
`𝐌(a, c, x) = π^{-1/2} (κx)^{1/4 - c/2} e^{x/2} (cos(2√(κx) - cπ/2 + π/4) + o(1))` with
`κ = c/2 - a`. Here `𝐌 = M/Γ(c)` is the regularized function, so no condition on `c` is
needed. -/
theorem tendsto_regularizedConfluent_atBot (c : ℝ) {x : ℝ} (hx : 0 < x) :
    Tendsto (fun a : ℝ =>
      ((Real.sqrt π * ((c / 2 - a) * x) ^ (c / 2 - 1 / 4) * Real.exp (-(x / 2)) : ℝ) : ℂ) *
          regularizedHGFun {(a : ℂ)} {(c : ℂ)} (x : ℂ) -
        ((Real.cos (2 * Real.sqrt ((c / 2 - a) * x) - c * π / 2 + π / 4) : ℝ) : ℂ))
      atBot (𝓝 0) := by
  have hκ : Tendsto (fun a : ℝ => c / 2 - a) atBot atTop :=
    (tendsto_neg_atBot_atTop.atTop_add (tendsto_const_nhds (x := c / 2))).congr
      fun a => by ring
  have h := ((tendsto_largeAU_sub_cos c hx).comp hκ).const_mul
    (((2 : ℝ) ^ (1 / 2 - c) * Real.sqrt π : ℝ) : ℂ)
  rw [mul_zero] at h
  refine h.congr' ?_
  filter_upwards [hκ.eventually (eventually_gt_atTop 0)] with a ha
  obtain ⟨κ, rfl⟩ : ∃ κ, a = c / 2 - κ := ⟨c / 2 - a, by ring⟩
  have hk : c / 2 - (c / 2 - κ) = κ := by ring
  simp only [Function.comp_apply, hk] at ha ⊢
  have hkx : 0 ≤ κ * x := by positivity
  have hS2 : (2 * Real.sqrt (κ * x)) ^ 2 = 4 * (κ * x) := by
    rw [mul_pow, Real.sq_sqrt hkx]
    norm_num
  have harg : (2 * Real.sqrt (κ * x)) ^ 2 / (4 * κ) = x := by
    rw [hS2]
    field_simp
  have hexp : (2 * Real.sqrt (κ * x)) ^ 2 / (8 * κ) = x / 2 := by
    rw [hS2]
    field_simp
    ring
  simp only [largeAU, largeAP, largeAW, largeAParam]
  rw [harg, hexp]
  have hr := two_rpow_mul_two_sqrt_rpow hkx c
  have hc := two_rpow_sqrt_pi_mul c
  rw [mul_sub]
  congr 1
  · rw [← mul_assoc, ← ofReal_mul]
    congr 2
    rw [← hr]
    ring
  · rw [← ofReal_mul]
    congr 1
    calc (2 : ℝ) ^ (1 / 2 - c) * Real.sqrt π *
          ((2 : ℝ) ^ (c - 1) * Real.sqrt (2 / π) *
            Real.cos (2 * Real.sqrt (κ * x) - c * π / 2 + π / 4))
        = ((2 : ℝ) ^ (1 / 2 - c) * Real.sqrt π * ((2 : ℝ) ^ (c - 1) * Real.sqrt (2 / π))) *
            Real.cos (2 * Real.sqrt (κ * x) - c * π / 2 + π / 4) := by ring
      _ = _ := by rw [hc, one_mul]

/-- **Bessel form of the large-`a` asymptotics** (a weak form of DLMF 13.8.9, with error
`o(env J)` in place of `O(|a|^{-1/2} env J)`): with `S = 2√((c/2 - a)x) = √(2x(c - 2a))`,
`√S ((c/2 - a)x)^{(c-1)/2} e^{-x/2} 𝐌(a, c, x) - √S J_{c-1}(S) → 0` as `a → -∞`. -/
theorem tendsto_regularizedConfluent_atBot_besselJ (c : ℝ) {x : ℝ} (hx : 0 < x) :
    Tendsto (fun a : ℝ =>
      ((Real.sqrt (2 * Real.sqrt ((c / 2 - a) * x)) * ((c / 2 - a) * x) ^ ((c - 1) / 2) *
          Real.exp (-(x / 2)) : ℝ) : ℂ) * regularizedHGFun {(a : ℂ)} {(c : ℂ)} (x : ℂ) -
        ((Real.sqrt (2 * Real.sqrt ((c / 2 - a) * x)) : ℝ) : ℂ) *
          besselJ ((c - 1 : ℝ) : ℂ) ((2 * Real.sqrt ((c / 2 - a) * x) : ℝ) : ℂ))
      atBot (𝓝 0) := by
  have hκ : Tendsto (fun a : ℝ => c / 2 - a) atBot atTop :=
    (tendsto_neg_atBot_atTop.atTop_add (tendsto_const_nhds (x := c / 2))).congr
      fun a => by ring
  have h := ((tendsto_largeAU_sub_largeAU0 c hx).comp hκ).const_mul
    ((((2 : ℝ) ^ (1 - c) : ℝ)) : ℂ)
  rw [mul_zero] at h
  refine h.congr' ?_
  filter_upwards [hκ.eventually (eventually_gt_atTop 0)] with a ha
  obtain ⟨κ, rfl⟩ : ∃ κ, a = c / 2 - κ := ⟨c / 2 - a, by ring⟩
  have hk : c / 2 - (c / 2 - κ) = κ := by ring
  simp only [Function.comp_apply, hk] at ha ⊢
  have hkx : 0 < κ * x := by positivity
  have hS : 0 < 2 * Real.sqrt (κ * x) := by positivity
  have hS2 : (2 * Real.sqrt (κ * x)) ^ 2 = 4 * (κ * x) := by
    rw [mul_pow, Real.sq_sqrt hkx.le]
    norm_num
  have harg : (2 * Real.sqrt (κ * x)) ^ 2 / (4 * κ) = x := by
    rw [hS2]
    field_simp
  have hexp : (2 * Real.sqrt (κ * x)) ^ 2 / (8 * κ) = x / 2 := by
    rw [hS2]
    field_simp
    ring
  rw [largeAU0_eq c hS]
  simp only [largeAU, largeAP, largeAW, largeAParam]
  rw [harg, hexp]
  -- the prefactor identity `2^{1-c} S^{c-1/2} = √S (κx)^{(c-1)/2}`
  have hpre : (2 : ℝ) ^ (1 - c) * (2 * Real.sqrt (κ * x)) ^ (c - 1 / 2) =
      Real.sqrt (2 * Real.sqrt (κ * x)) * (κ * x) ^ ((c - 1) / 2) := by
    have h1 : (2 * Real.sqrt (κ * x)) ^ (c - 1 / 2) =
        Real.sqrt (2 * Real.sqrt (κ * x)) * (2 * Real.sqrt (κ * x)) ^ (c - 1) := by
      rw [show Real.sqrt (2 * Real.sqrt (κ * x)) = (2 * Real.sqrt (κ * x)) ^ (1 / 2 : ℝ) from
        Real.sqrt_eq_rpow _, ← Real.rpow_add hS]
      congr 1
      ring
    have h2 : (2 * Real.sqrt (κ * x)) ^ (c - 1) = (2 : ℝ) ^ (c - 1) * (κ * x) ^ ((c - 1) / 2) := by
      rw [Real.mul_rpow (by norm_num) (Real.sqrt_nonneg _), Real.sqrt_eq_rpow,
        ← Real.rpow_mul hkx.le]
      congr 2
      ring
    have h3 : (2 : ℝ) ^ (1 - c) * (2 : ℝ) ^ (c - 1) = 1 := by
      rw [← Real.rpow_add two_pos]
      simp
    rw [h1, h2]
    linear_combination Real.sqrt (2 * Real.sqrt (κ * x)) * (κ * x) ^ ((c - 1) / 2) * h3
  have h3 : (2 : ℝ) ^ (1 - c) * (2 : ℝ) ^ (c - 1) = 1 := by
    rw [← Real.rpow_add two_pos]
    simp
  have hprec := congrArg (fun r : ℝ => (r : ℂ)) hpre
  have h3c := congrArg (fun r : ℝ => (r : ℂ)) h3
  simp only [ofReal_mul, ofReal_one] at hprec h3c ⊢
  linear_combination (Real.exp (-(x / 2)) : ℂ) *
      regularizedHGFun {((c / 2 - κ : ℝ) : ℂ)} {(c : ℂ)} (x : ℂ) * hprec -
    (Real.sqrt (2 * Real.sqrt (κ * x)) : ℂ) *
      besselJ ((c - 1 : ℝ) : ℂ) (((2 : ℝ) : ℂ) * (Real.sqrt (κ * x) : ℂ)) * h3c

/-! ### Tricomi's function for large negative `a` -/

/-- A trigonometric identity behind (8.2.10). -/
theorem sin_mul_cos_sub_sin_mul_cos (A C t : ℝ) :
    Real.sin (C - A) * Real.cos t + Real.sin A * Real.cos (t + C) =
      Real.sin C * Real.cos (t + A) := by
  simp only [Real.sin_sub, Real.cos_add]
  ring

theorem ofReal_cpow_eq {x : ℝ} (hx : 0 < x) (y : ℝ) : (x : ℂ) ^ (y : ℂ) = ((x ^ y : ℝ) : ℂ) :=
  (ofReal_cpow hx.le y).symm

/-- The algebraic identity expressing `U` through the two regularized Kummer functions. -/
theorem kummerU_large_a_eq (c : ℝ) (hc : ∀ k : ℤ, c ≠ k) {a x : ℝ} (hx : 0 < x)
    (hκ : 0 < c / 2 - a) (hca : 0 < c - a) (h1a : 0 < 1 - a) :
    ((Real.sqrt π * x ^ (c / 2 - 1 / 4) * Real.exp (-(x / 2)) : ℝ) : ℂ) /
        Complex.Gamma (((c / 2 - a : ℝ) : ℂ) + 1 / 4) * kummerU (a : ℂ) (c : ℂ) (x : ℂ) =
      (Complex.Gamma (((c - a : ℝ) : ℂ)) /
            (Complex.Gamma (((c / 2 - a : ℝ) : ℂ) + 1 / 4) *
              (((c / 2 - a) ^ (c / 2 - 1 / 4) : ℝ) : ℂ)) *
          ((Real.sin (π * (c - a)) : ℝ) : ℂ) *
          (((Real.sqrt π * ((c / 2 - a) * x) ^ (c / 2 - 1 / 4) * Real.exp (-(x / 2)) : ℝ) : ℂ) *
            regularizedHGFun {(a : ℂ)} {(c : ℂ)} (x : ℂ)) -
        Complex.Gamma (((1 - a : ℝ) : ℂ)) /
            (Complex.Gamma (((c / 2 - a : ℝ) : ℂ) + 1 / 4) *
              (((c / 2 - a) ^ (3 / 4 - c / 2) : ℝ) : ℂ)) *
          ((Real.sin (π * a) : ℝ) : ℂ) *
          (((Real.sqrt π * ((c / 2 - a) * x) ^ (3 / 4 - c / 2) * Real.exp (-(x / 2)) : ℝ) : ℂ) *
            regularizedHGFun {((a - c + 1 : ℝ) : ℂ)} {((2 - c : ℝ) : ℂ)} (x : ℂ))) /
        ((Real.sin (π * c) : ℝ) : ℂ) := by
  set κ := c / 2 - a with hκdef
  have hcZ : ∀ k : ℤ, (c : ℂ) ≠ k := fun k h => hc k (by exact_mod_cast h)
  have hcN : ∀ k : ℕ, (c : ℂ) ≠ -k := fun k h => hcZ (-k) (by push_cast; exact h)
  have h2N : ∀ k : ℕ, (2 : ℂ) - c ≠ -k := fun k h =>
    hcZ (k + 2) (by push_cast; linear_combination -h)
  have hs : Real.sin (π * c) ≠ 0 := by
    intro h
    obtain ⟨k, hk⟩ := Real.sin_eq_zero_iff.mp h
    exact hc k (by nlinarith [Real.pi_pos])
  have hs' : ((Real.sin (π * c) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hGκ : Complex.Gamma (((κ : ℝ) : ℂ) + 1 / 4) ≠ 0 := by
    have : ((κ : ℝ) : ℂ) + 1 / 4 = ((κ + 1 / 4 : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.Gamma_ofReal]
    exact_mod_cast (Real.Gamma_pos_of_pos (by linarith)).ne'
  have hGca : Complex.Gamma (((c - a : ℝ) : ℂ)) ≠ 0 := by
    rw [Complex.Gamma_ofReal]; exact_mod_cast (Real.Gamma_pos_of_pos hca).ne'
  have hG1a : Complex.Gamma (((1 - a : ℝ) : ℂ)) ≠ 0 := by
    rw [Complex.Gamma_ofReal]; exact_mod_cast (Real.Gamma_pos_of_pos h1a).ne'
  have hr1 := recip_Gamma_one_sub_eq hGca
  have hr2 := recip_Gamma_one_sub_eq hG1a
  rw [show (1 : ℂ) - ((c - a : ℝ) : ℂ) = (a : ℂ) - c + 1 by push_cast; ring] at hr1
  rw [show (1 : ℂ) - ((1 - a : ℝ) : ℂ) = (a : ℂ) by push_cast; ring] at hr2
  have hΓ1 := Complex.Gamma_mul_Gamma_one_sub (c : ℂ)
  have hΓ2 := Complex.Gamma_mul_Gamma_one_sub ((c : ℂ) - 1)
  rw [show (1 : ℂ) - ((c : ℂ) - 1) = 2 - c by ring,
    show (π : ℂ) * ((c : ℂ) - 1) = π * c - π by ring, Complex.sin_sub_pi] at hΓ2
  have hsin : Complex.sin (π * c) = ((Real.sin (π * c) : ℝ) : ℂ) := by push_cast; rfl
  have hsin1 : Complex.sin (π * ((c - a : ℝ) : ℂ)) = ((Real.sin (π * (c - a)) : ℝ) : ℂ) := by
    push_cast; rfl
  have hsin2 : Complex.sin (π * ((1 - a : ℝ) : ℂ)) = ((Real.sin (π * a) : ℝ) : ℂ) := by
    rw [show (π : ℂ) * ((1 - a : ℝ) : ℂ) = π - π * a by push_cast; ring, Complex.sin_pi_sub]
    push_cast
    rfl
  rw [hsin1] at hr1
  rw [hsin2] at hr2
  rw [hsin] at hΓ1
  rw [hsin] at hΓ2
  have hGc : Complex.Gamma (c : ℂ) ≠ 0 := Complex.Gamma_ne_zero hcN
  have hG2c : Complex.Gamma (2 - (c : ℂ)) ≠ 0 := Complex.Gamma_ne_zero h2N
  have hΓ1' : Complex.Gamma (1 - (c : ℂ)) =
      π / (((Real.sin (π * c) : ℝ) : ℂ) * Complex.Gamma c) := by
    rw [eq_div_iff (mul_ne_zero hs' hGc)]
    have : Complex.Gamma c * Complex.Gamma (1 - c) * ((Real.sin (π * c) : ℝ) : ℂ) = π := by
      rw [hΓ1]; field_simp
    linear_combination this
  have hΓ2' : Complex.Gamma ((c : ℂ) - 1) =
      π / (-((Real.sin (π * c) : ℝ) : ℂ) * Complex.Gamma (2 - c)) := by
    rw [eq_div_iff (mul_ne_zero (neg_ne_zero.mpr hs') hG2c)]
    have : Complex.Gamma (c - 1) * Complex.Gamma (2 - c) * -((Real.sin (π * c) : ℝ) : ℂ) = π := by
      rw [hΓ2]; field_simp
    linear_combination this
  -- real power identities
  have hκx1 : x ^ (c / 2 - 1 / 4) * κ ^ (c / 2 - 1 / 4) = (κ * x) ^ (c / 2 - 1 / 4) := by
    rw [Real.mul_rpow hκ.le hx.le]; ring
  have hκx2 : x ^ (c / 2 - 1 / 4) * x ^ (1 - c) * κ ^ (3 / 4 - c / 2) =
      (κ * x) ^ (3 / 4 - c / 2) := by
    rw [← Real.rpow_add hx, Real.mul_rpow hκ.le hx.le, show c / 2 - 1 / 4 + (1 - c) =
      3 / 4 - c / 2 by ring]
    ring
  have hκp1 : (κ ^ (c / 2 - 1 / 4) : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hκ _).ne'
  have hκp2 : (κ ^ (3 / 4 - c / 2) : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hκ _).ne'
  rw [kummerU_eq_connection _ _ _ hcZ, kummerUConnection, kummerM_eq_mul_regularizedHGFun hcN,
    kummerM_eq_mul_regularizedHGFun h2N, div_eq_mul_inv (Complex.Gamma (1 - (c : ℂ))), hr1,
    div_eq_mul_inv (Complex.Gamma ((c : ℂ) - 1)), hr2, hΓ1', hΓ2',
    show (1 : ℂ) - (c : ℂ) = ((1 - c : ℝ) : ℂ) by push_cast; ring, ofReal_cpow_eq hx,
    show ((a - c + 1 : ℝ) : ℂ) = (a : ℂ) - c + 1 by push_cast; ring,
    show ((2 - c : ℝ) : ℂ) = 2 - (c : ℂ) by push_cast; ring,
    show (κ * x) ^ (c / 2 - 1 / 4) = x ^ (c / 2 - 1 / 4) * κ ^ (c / 2 - 1 / 4) from hκx1.symm,
    show (κ * x) ^ (3 / 4 - c / 2) = x ^ (c / 2 - 1 / 4) * x ^ (1 - c) * κ ^ (3 / 4 - c / 2)
      from hκx2.symm]
  have hκp1' : ((κ ^ (c / 2 - 1 / 4) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hκp1
  have hκp2' : ((κ ^ (3 / 4 - c / 2) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hκp2
  simp only [ofReal_mul]
  generalize ((κ ^ (c / 2 - 1 / 4) : ℝ) : ℂ) = P1 at hκp1' ⊢
  generalize ((κ ^ (3 / 4 - c / 2) : ℝ) : ℂ) = P2 at hκp2' ⊢
  generalize ((x ^ (c / 2 - 1 / 4) : ℝ) : ℂ) = X1
  generalize ((x ^ (1 - c) : ℝ) : ℂ) = X2
  generalize Complex.Gamma (((κ : ℝ) : ℂ) + 1 / 4) = G at hGκ ⊢
  field_simp
  ring

theorem large_a_algebra {s S1 S2 G1 G2 A1 A2 C1 C2 C0 : ℂ} (hs : s ≠ 0)
    (htc : S1 * C1 - S2 * C2 = s * C0) :
    (G1 * S1 * A1 - G2 * S2 * A2) / s - C0 =
      ((G1 - 1) * (S1 * C1) + (G1 - 1) * S1 * (A1 - C1) + (A1 - C1) * S1 -
        (G2 - 1) * (S2 * C2) - (G2 - 1) * S2 * (A2 - C2) - (A2 - C2) * S2) / s := by
  field_simp
  linear_combination htc

/-- `Γ(κ + p)/(Γ(κ + 1/4) κ^{p-1/4}) → 1` as `κ → +∞`. -/
theorem tendsto_Gamma_ratio_rpow (p : ℝ) :
    Tendsto (fun κ : ℝ => Complex.Gamma (((κ + p : ℝ) : ℂ)) /
      (Complex.Gamma (((κ : ℝ) : ℂ) + 1 / 4) * ((κ ^ (p - 1 / 4) : ℝ) : ℂ))) atTop (𝓝 1) := by
  refine (DLMF.Gamma.Gamma_ratio_power (a := (p : ℂ)) (b := 1 / 4)).congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with κ hκ
  rw [show (p : ℂ) - 1 / 4 = ((p - 1 / 4 : ℝ) : ℂ) by push_cast; ring, ofReal_cpow_eq hκ,
    div_div]
  push_cast
  ring_nf

/-- **Large-`a` asymptotics of Tricomi's function** (Beals–Wong (8.2.10), with error `o(1)` in
place of `O(|a|^{-1/2})`; compare DLMF 13.8.10): for real non-integer `c` and fixed `x > 0`,
`U(a, c, x) = Γ(c/2 - a + 1/4) π^{-1/2} x^{1/4-c/2} e^{x/2}
  (cos(2√((c/2 - a)x) - cπ/2 + aπ + π/4) + o(1))` as `a → -∞`. -/
theorem tendsto_kummerU_atBot (c : ℝ) (hc : ∀ k : ℤ, c ≠ k) {x : ℝ} (hx : 0 < x) :
    Tendsto (fun a : ℝ =>
      ((Real.sqrt π * x ^ (c / 2 - 1 / 4) * Real.exp (-(x / 2)) : ℝ) : ℂ) /
          Complex.Gamma (((c / 2 - a : ℝ) : ℂ) + 1 / 4) * kummerU (a : ℂ) (c : ℂ) (x : ℂ) -
        ((Real.cos (2 * Real.sqrt ((c / 2 - a) * x) - c * π / 2 + a * π + π / 4) : ℝ) : ℂ))
      atBot (𝓝 0) := by
  have hκ : Tendsto (fun a : ℝ => c / 2 - a) atBot atTop :=
    (tendsto_neg_atBot_atTop.atTop_add (tendsto_const_nhds (x := c / 2))).congr
      fun a => by ring
  have hshift : Tendsto (fun a : ℝ => a - c + 1) atBot atBot :=
    (tendsto_atBot_add_const_right _ (1 - c) tendsto_id).congr fun a => by
      simp only [id]
      ring
  set A1 : ℝ → ℂ := fun a => ((Real.sqrt π * ((c / 2 - a) * x) ^ (c / 2 - 1 / 4) *
    Real.exp (-(x / 2)) : ℝ) : ℂ) * regularizedHGFun {(a : ℂ)} {(c : ℂ)} (x : ℂ) with hA1
  set C1 : ℝ → ℂ := fun a =>
    ((Real.cos (2 * Real.sqrt ((c / 2 - a) * x) - c * π / 2 + π / 4) : ℝ) : ℂ) with hC1
  set A2 : ℝ → ℂ := fun a => ((Real.sqrt π * ((c / 2 - a) * x) ^ (3 / 4 - c / 2) *
    Real.exp (-(x / 2)) : ℝ) : ℂ) *
      regularizedHGFun {((a - c + 1 : ℝ) : ℂ)} {((2 - c : ℝ) : ℂ)} (x : ℂ) with hA2
  set C2 : ℝ → ℂ := fun a =>
    ((Real.cos (2 * Real.sqrt ((c / 2 - a) * x) - (2 - c) * π / 2 + π / 4) : ℝ) : ℂ) with hC2
  have hE1 : Tendsto (fun a => A1 a - C1 a) atBot (𝓝 0) := tendsto_regularizedConfluent_atBot c hx
  have hE2 : Tendsto (fun a => A2 a - C2 a) atBot (𝓝 0) := by
    refine ((tendsto_regularizedConfluent_atBot (2 - c) hx).comp hshift).congr fun a => ?_
    simp only [Function.comp_apply, hA2, hC2]
    rw [show (2 - c) / 2 - (a - c + 1) = c / 2 - a by ring,
      show (2 - c) / 2 - 1 / 4 = 3 / 4 - c / 2 by ring]
  set G1 : ℝ → ℂ := fun a => Complex.Gamma (((c - a : ℝ) : ℂ)) /
    (Complex.Gamma (((c / 2 - a : ℝ) : ℂ) + 1 / 4) *
      (((c / 2 - a) ^ (c / 2 - 1 / 4) : ℝ) : ℂ)) with hG1
  set G2 : ℝ → ℂ := fun a => Complex.Gamma (((1 - a : ℝ) : ℂ)) /
    (Complex.Gamma (((c / 2 - a : ℝ) : ℂ) + 1 / 4) *
      (((c / 2 - a) ^ (3 / 4 - c / 2) : ℝ) : ℂ)) with hG2
  have hG1t : Tendsto (fun a => G1 a - 1) atBot (𝓝 0) := by
    have := ((tendsto_Gamma_ratio_rpow (c / 2)).comp hκ).sub_const 1
    rw [sub_self] at this
    refine this.congr fun a => ?_
    simp only [Function.comp_apply, hG1]
    rw [show c / 2 - a + c / 2 = c - a by ring]
  have hG2t : Tendsto (fun a => G2 a - 1) atBot (𝓝 0) := by
    have := ((tendsto_Gamma_ratio_rpow (1 - c / 2)).comp hκ).sub_const 1
    rw [sub_self] at this
    refine this.congr fun a => ?_
    simp only [Function.comp_apply, hG2]
    rw [show c / 2 - a + (1 - c / 2) = 1 - a by ring,
      show 1 - c / 2 - 1 / 4 = 3 / 4 - c / 2 by ring]
  set S1 : ℝ → ℂ := fun a => ((Real.sin (π * (c - a)) : ℝ) : ℂ)
  set S2 : ℝ → ℂ := fun a => ((Real.sin (π * a) : ℝ) : ℂ)
  have hbd1 : IsBoundedUnder (· ≤ ·) atBot ((‖·‖) ∘ fun a => S1 a * C1 a) := by
    refine isBoundedUnder_of ⟨1, fun a => ?_⟩
    simp only [Function.comp_apply, S1, hC1, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc |Real.sin _| * |Real.cos _| ≤ 1 * 1 :=
          mul_le_mul (Real.abs_sin_le_one _) (Real.abs_cos_le_one _) (abs_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have hbd2 : IsBoundedUnder (· ≤ ·) atBot ((‖·‖) ∘ fun a => S2 a * C2 a) := by
    refine isBoundedUnder_of ⟨1, fun a => ?_⟩
    simp only [Function.comp_apply, S2, hC2, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc |Real.sin _| * |Real.cos _| ≤ 1 * 1 :=
          mul_le_mul (Real.abs_sin_le_one _) (Real.abs_cos_le_one _) (abs_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have hbS1 : IsBoundedUnder (· ≤ ·) atBot ((‖·‖) ∘ S1) := by
    refine isBoundedUnder_of ⟨1, fun a => ?_⟩
    simp only [Function.comp_apply, S1, Complex.norm_real, Real.norm_eq_abs]
    exact Real.abs_sin_le_one _
  have hbS2 : IsBoundedUnder (· ≤ ·) atBot ((‖·‖) ∘ S2) := by
    refine isBoundedUnder_of ⟨1, fun a => ?_⟩
    simp only [Function.comp_apply, S2, Complex.norm_real, Real.norm_eq_abs]
    exact Real.abs_sin_le_one _
  have t1 := hG1t.zero_mul_isBoundedUnder_le hbd1
  have t2 := (hG1t.zero_mul_isBoundedUnder_le hbS1).mul hE1
  have t3 := hE1.zero_mul_isBoundedUnder_le hbS1
  have t4 := hG2t.zero_mul_isBoundedUnder_le hbd2
  have t5 := (hG2t.zero_mul_isBoundedUnder_le hbS2).mul hE2
  have t6 := hE2.zero_mul_isBoundedUnder_le hbS2
  rw [zero_mul] at t2 t5
  have hL := ((((((t1.add t2).add t3).sub t4).sub t5).sub t6).div_const
    ((Real.sin (π * c) : ℝ) : ℂ))
  simp only [add_zero, sub_zero, zero_div] at hL
  refine hL.congr' ?_
  filter_upwards [hκ.eventually (eventually_gt_atTop 0),
    eventually_lt_atBot (c : ℝ), eventually_lt_atBot (1 : ℝ)] with a ha hca h1a
  have hs : Real.sin (π * c) ≠ 0 := by
    intro h
    obtain ⟨k, hk⟩ := Real.sin_eq_zero_iff.mp h
    exact hc k (by nlinarith [Real.pi_pos])
  have hs' : ((Real.sin (π * c) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs
  rw [kummerU_large_a_eq c hc hx ha (by linarith) (by linarith)]
  -- the trigonometric identity
  have htrig : Real.sin (π * (c - a)) *
        Real.cos (2 * Real.sqrt ((c / 2 - a) * x) - c * π / 2 + π / 4) -
      Real.sin (π * a) * Real.cos (2 * Real.sqrt ((c / 2 - a) * x) - (2 - c) * π / 2 + π / 4) =
      Real.sin (π * c) *
        Real.cos (2 * Real.sqrt ((c / 2 - a) * x) - c * π / 2 + a * π + π / 4) := by
    set t := 2 * Real.sqrt ((c / 2 - a) * x) - c * π / 2 + π / 4
    have h := sin_mul_cos_sub_sin_mul_cos (π * a) (π * c) t
    rw [show 2 * Real.sqrt ((c / 2 - a) * x) - (2 - c) * π / 2 + π / 4 = t + π * c - π by
        simp only [t]; ring, Real.cos_sub_pi,
      show 2 * Real.sqrt ((c / 2 - a) * x) - c * π / 2 + a * π + π / 4 = t + π * a by
        simp only [t]; ring,
      show π * (c - a) = π * c - π * a by ring]
    linarith
  have htc := congrArg (fun r : ℝ => (r : ℂ)) htrig
  simp only [ofReal_sub, ofReal_mul] at htc
  exact (large_a_algebra hs' htc).symm

/-! ### Fejér's formula for Laguerre polynomials -/

theorem tendsto_sqrt_add_sub_sqrt {d : ℝ} (hd : 0 ≤ d) :
    Tendsto (fun t : ℝ => Real.sqrt (t + d) - Real.sqrt t) atTop (𝓝 0) := by
  have hup : Tendsto (fun t : ℝ => d / Real.sqrt t) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_sqrt_atTop
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact sub_nonneg.mpr (Real.sqrt_le_sqrt (by linarith))
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
    have hsd : 0 ≤ Real.sqrt (t + d) := Real.sqrt_nonneg _
    have hdiff : 0 ≤ Real.sqrt (t + d) - Real.sqrt t :=
      sub_nonneg.mpr (Real.sqrt_le_sqrt (by linarith))
    have hprod : (Real.sqrt (t + d) - Real.sqrt t) * (Real.sqrt (t + d) + Real.sqrt t) = d := by
      have h1 := Real.sq_sqrt (show 0 ≤ t + d by linarith)
      have h2 := Real.sq_sqrt ht.le
      nlinarith
    rw [le_div_iff₀ hst]
    nlinarith

/-- **Fejér's formula** (Szegő (8.22.4); Beals–Wong (5.4.12)): for `α > -1` and fixed `x > 0`,
`n^{1/4 - α/2} L_n^{(α)}(x) = π^{-1/2} e^{x/2} x^{-α/2-1/4} cos(2√(nx) - απ/2 - π/4) + o(1)`. -/
theorem laguerrePolyL_fejer {α : ℝ} (hα : -1 < α) {x : ℝ} (hx : 0 < x) :
    Tendsto (fun n : ℕ => (((n : ℝ) ^ (1 / 4 - α / 2) : ℝ) : ℂ) *
        DLMF.OrthogonalPolynomials.laguerrePolyL (α : ℂ) n (x : ℂ) -
      ((Real.exp (x / 2) * x ^ (-(α / 2) - 1 / 4) / Real.sqrt π *
        Real.cos (2 * Real.sqrt (n * x) - α * π / 2 - π / 4) : ℝ) : ℂ)) atTop (𝓝 0) := by
  set c : ℝ := α + 1 with hcdef
  set p : ℝ := α / 2 + 1 / 4 with hpdef
  set K : ℝ := Real.exp (x / 2) * x ^ (-(α / 2) - 1 / 4) / Real.sqrt π with hK
  have hc0 : 0 < c := by linarith
  -- the main limit along `a = -n`
  have hn : Tendsto (fun n : ℕ => -(n : ℝ)) atTop atBot :=
    tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop
  have hE := (tendsto_regularizedConfluent_atBot c hx).comp hn
  set E : ℕ → ℂ := fun n => ((Real.sqrt π * ((c / 2 - -(n : ℝ)) * x) ^ (c / 2 - 1 / 4) *
      Real.exp (-(x / 2)) : ℝ) : ℂ) * regularizedHGFun {((-(n : ℝ) : ℝ) : ℂ)} {(c : ℂ)} (x : ℂ) -
    ((Real.cos (2 * Real.sqrt ((c / 2 - -(n : ℝ)) * x) - c * π / 2 + π / 4) : ℝ) : ℂ) with hEdef
  replace hE : Tendsto E atTop (𝓝 0) := hE
  set cK : ℕ → ℂ := fun n =>
    ((Real.cos (2 * Real.sqrt ((c / 2 - -(n : ℝ)) * x) - c * π / 2 + π / 4) : ℝ) : ℂ)
  set cN : ℕ → ℂ := fun n =>
    ((Real.cos (2 * Real.sqrt (n * x) - α * π / 2 - π / 4) : ℝ) : ℂ)
  -- the Gamma ratio
  set R : ℕ → ℂ := fun n => Complex.Gamma ((n : ℂ) + c) / (n ! : ℂ) / (((n : ℝ) ^ α : ℝ) : ℂ)
  have hR : Tendsto R atTop (𝓝 1) := by
    have h := (DLMF.Gamma.Gamma_ratio_power (a := (c : ℂ)) (b := 1)).comp tendsto_natCast_atTop_atTop
    refine h.congr' ?_
    filter_upwards with n
    simp only [Function.comp_apply, R]
    rw [ofReal_natCast, Complex.Gamma_nat_eq_factorial, ofReal_cpow (Nat.cast_nonneg n)]
    congr 2
    rw [hcdef]
    push_cast
    ring
  set Q : ℕ → ℝ := fun n => ((n : ℝ) / (n + c / 2)) ^ p
  have hQ : Tendsto Q atTop (𝓝 1) := by
    have := (tendsto_natCast_div_add_atTop (c / 2 : ℝ)).rpow_const (p := p) (Or.inl one_ne_zero)
    rwa [Real.one_rpow] at this
  have hRQ : Tendsto (fun n => R n * (Q n : ℂ) - 1) atTop (𝓝 0) := by
    have := hR.mul ((continuous_ofReal.tendsto _).comp hQ)
    rw [ofReal_one, mul_one] at this
    simpa using this.sub_const 1
  -- the phase difference
  have hcos : Tendsto (fun n => cK n - cN n) atTop (𝓝 0) := by
    have hd := (tendsto_sqrt_add_sub_sqrt (d := c / 2 * x) (by positivity)).comp
      ((tendsto_natCast_atTop_atTop (R := ℝ)).atTop_mul_const hx)
    have h2 : Tendsto (fun n : ℕ => 2 * (Real.sqrt ((n : ℝ) * x + c / 2 * x) -
        Real.sqrt ((n : ℝ) * x))) atTop (𝓝 0) := by
      simpa using hd.const_mul 2
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) (h2.abs.trans (by simp))
    simp only [cK, cN]
    rw [← ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    refine (Real.abs_cos_sub_cos_le _ _).trans (le_of_eq ?_)
    congr 1
    rw [show (c / 2 - -(n : ℝ)) * x = (n : ℝ) * x + c / 2 * x by ring, hcdef]
    ring
  -- assemble
  have hlim : Tendsto (fun n => (K : ℂ) * ((R n * (Q n : ℂ) - 1) * cK n +
      (R n * (Q n : ℂ) - 1) * E n + E n + (cK n - cN n))) atTop (𝓝 0) := by
    have hbd : IsBoundedUnder (· ≤ ·) atTop ((‖·‖) ∘ cK) := by
      refine isBoundedUnder_of ⟨1, fun n => ?_⟩
      simp only [Function.comp_apply, cK, Complex.norm_real, Real.norm_eq_abs]
      exact Real.abs_cos_le_one _
    have h1 := hRQ.zero_mul_isBoundedUnder_le hbd
    have h2 := hRQ.mul hE
    rw [zero_mul] at h2
    have := (((h1.add h2).add hE).add hcos).const_mul (K : ℂ)
    simpa using this
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hκ : 0 < c / 2 - -(n : ℝ) := by linarith
  have hcpole : ∀ k : ℕ, ((α : ℂ) + 1) ≠ -k := by
    intro k hk
    have := congrArg Complex.re hk
    simp at this
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hL : DLMF.OrthogonalPolynomials.laguerrePolyL (α : ℂ) n (x : ℂ) =
      Complex.Gamma ((n : ℂ) + c) / (n ! : ℂ) *
        regularizedHGFun {((-(n : ℝ) : ℝ) : ℂ)} {(c : ℂ)} (x : ℂ) := by
    rw [DLMF.OrthogonalPolynomials.laguerrePolyL, kummerM_eq_mul_regularizedHGFun hcpole]
    have hG := Complex.Gamma_add_nat_div_Gamma_eq (n := n) ((α : ℂ) + 1) hcpole
    have hG0 : Complex.Gamma ((α : ℂ) + 1) ≠ 0 := Complex.Gamma_ne_zero hcpole
    rw [show ((-(n : ℝ) : ℝ) : ℂ) = -(n : ℂ) by push_cast; ring,
      show ((c : ℝ) : ℂ) = (α : ℂ) + 1 by rw [hcdef]; push_cast; ring,
      show (n : ℂ) + ((α : ℂ) + 1) = (α : ℂ) + 1 + n by ring]
    rw [poch, ← hG]
    field_simp
  -- the real identity for the prefactors
  have hpow : (n : ℝ) ^ (1 / 4 - α / 2) * (n : ℝ) ^ α = Q n * K *
      (Real.sqrt π * ((c / 2 - -(n : ℝ)) * x) ^ (c / 2 - 1 / 4) * Real.exp (-(x / 2))) := by
    have hpi : 0 < Real.sqrt π := Real.sqrt_pos.mpr Real.pi_pos
    simp only [Q, hK]
    rw [← Real.rpow_add hn0, Real.div_rpow hn0.le (by linarith),
      Real.mul_rpow hκ.le hx.le,
      show c / 2 - 1 / 4 = p by rw [hcdef, hpdef]; ring,
      show 1 / 4 - α / 2 + α = p by rw [hpdef]; ring,
      show -(α / 2) - 1 / 4 = -p by rw [hpdef]; ring, Real.rpow_neg hx.le,
      show (n : ℝ) + c / 2 = c / 2 - -(n : ℝ) by ring]
    set κ := c / 2 - -(n : ℝ) with hκdef
    have hxp : 0 < x ^ p := Real.rpow_pos_of_pos hx p
    have hkp : 0 < κ ^ p := Real.rpow_pos_of_pos hκ p
    have he : Real.exp (x / 2) * Real.exp (-(x / 2)) = 1 := by
      rw [← Real.exp_add]; simp
    have : (n : ℝ) ^ p / κ ^ p * (Real.exp (x / 2) * (x ^ p)⁻¹ / Real.sqrt π) *
        (Real.sqrt π * (κ ^ p * x ^ p) * Real.exp (-(x / 2))) =
        (n : ℝ) ^ p * (Real.exp (x / 2) * Real.exp (-(x / 2))) := by
      field_simp
    rw [this, he, mul_one]
  have hR' : R n * (((n : ℝ) ^ α : ℝ) : ℂ) = Complex.Gamma ((n : ℂ) + c) / (n ! : ℂ) := by
    have : (((n : ℝ) ^ α : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.rpow_pos_of_pos hn0 α).ne'
    simp only [R]
    field_simp
  simp only [hEdef, cK, cN]
  rw [hL, ← hR']
  have hpowc := congrArg (fun r : ℝ => (r : ℂ)) hpow
  simp only [ofReal_mul] at hpowc ⊢
  linear_combination (-R n) * regularizedHGFun {((-(n : ℝ) : ℝ) : ℂ)} {(c : ℂ)} (x : ℂ) * hpowc

end DLMF.Confluent
