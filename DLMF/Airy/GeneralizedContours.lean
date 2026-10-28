/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Airy.Scorer

/-!
# Reid generalized Airy contours, DLMF §9.13(ii)

Statements acquired from the NIST DLMF, checked 2026-10-19.
New statements are initially admitted; existing proved Airy results are retained.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF.Confluent
open scoped Real Topology Nat
namespace DLMF.Airy

/-- The integrand on the logarithmic t plane; the contour arguments lie in [0,2π]. -/
def reidKernel (z p w : ℂ) : ℂ := exp (-p * w + z * exp w - exp (3 * w) / 3)
/-- A ray integral of the lifted Reid kernel, starting at radius r. -/
def reidRay (z p : ℂ) (θ r : ℝ) : ℂ :=
  ∫ t : ℝ in Ioi r, exp (θ * I) * reidKernel z p (log t + θ * I)
/-- A unit-circle arc of the lifted kernel. -/
def reidArc (z p : ℂ) (α β : ℝ) : ℂ :=
  ∫ θ : ℝ in α..β, I * exp (θ * I) * reidKernel z p (θ * I)
/-- A Reid contour from infinity to infinity, with its prescribed orientation. -/
def reidContour (z p : ℂ) (α β : ℝ) : ℂ := -reidRay z p α 1 + reidArc z p α β + reidRay z p β 1
/-- Reid's A1,A2,A3 on L1,L2,L3 of Figure 9.13.1. -/
@[dlmf 9.13.E25]
def reidAiryA (k : Fin 3) (z p : ℂ) : ℂ :=
  (match k.val with
    | 0 => reidContour z p (4 * π / 3) (2 * π / 3)
    | 1 => reidContour z p (2 * π) (4 * π / 3)
    | _ => reidContour z p (2 * π / 3) 0) / (2 * π * I)
/-- The positively oriented closed contour L0, for integral p. -/
@[dlmf 9.13.E26]
def reidAiryB0 (z : ℂ) (p : ℤ) : ℂ := reidArc z p 0 (2 * π) / (2 * π * I)
/-- Coefficients of exp(zt-t³/3), used to specify the finite part at t=0. -/
def reidTaylorCoeff (z : ℂ) (j : ℕ) : ℂ :=
  ∑ k ∈ Finset.range (j / 3 + 1), (-1 / 3 : ℂ) ^ k * z ^ (j - 3 * k) / (k.factorial * (j - 3 * k).factorial)
/-- The ordinary ray integral when p≤0; for p>0 the explicitly subtracted Hadamard
finite part, with the inherited logarithm at the lower endpoint. The printed positive-p
integrals in 9.13.27 do not converge as ordinary integrals. -/
def reidAiryB (k : Fin 3) (z : ℂ) (p : ℤ) : ℂ :=
  let θ : ℝ := 2 * k.val * π / 3
  if p ≤ 0 then reidRay z p θ 0 else
    let n := p.toNat
    reidRay z p θ 1 +
      (∫ t : ℝ in 0..1, exp (θ * I) * ((t : ℂ) * exp (θ * I)) ^ (-(p : ℂ)) *
        (exp (z * ((t : ℂ) * exp (θ * I)) - ((t : ℂ) * exp (θ * I)) ^ 3 / 3) -
          ∑ j ∈ Finset.range n, reidTaylorCoeff z j * ((t : ℂ) * exp (θ * I)) ^ j)) +
      (∑ j ∈ Finset.range (n - 1), reidTaylorCoeff z j * exp (θ * I * ((j : ℂ) + 1 - p)) /
        ((j : ℂ) + 1 - p)) + θ * I * reidTaylorCoeff z (n - 1)

/-- Ordinary convergence range of the printed ray integrals (DLMF 9.13.27). -/
@[dlmf 9.13.E27]
theorem reidAiryB_ordinary_ray (k : Fin 3) (z : ℂ) {p : ℤ} (hp : p ≤ 0) :
    reidAiryB k z p = reidRay z p (2 * k.val * π / 3) 0 := by
  simp only [reidAiryB, hp, ↓reduceIte]

/-- Shifting the logarithmic variable by `cI`, with `e^{3cI} = 1`, rotates `z`. -/
theorem reidKernel_add_mul_I {c : ℝ} (hc : exp (3 * (c * I)) = 1) (z p w : ℂ) :
    reidKernel z p (w + c * I) = exp (-p * (c * I)) * reidKernel (z * exp (c * I)) p w := by
  have h3 : exp (3 * (w + c * I)) = exp (3 * w) := by
    rw [show 3 * (w + c * I) = 3 * w + 3 * (c * I) by ring, exp_add, hc, mul_one]
  simp only [reidKernel]
  rw [h3, exp_add w (c * I), ← exp_add (-p * (c * I))]
  congr 1
  ring

/-- Rotating a ray by `c` with `e^{3cI} = 1` rotates `z` and multiplies by a constant. -/
theorem reidRay_add {c : ℝ} (hc : exp (3 * (c * I)) = 1) (z p : ℂ) (θ r : ℝ) :
    reidRay z p (θ + c) r =
      exp (c * I) * exp (-p * (c * I)) * reidRay (z * exp (c * I)) p θ r := by
  simp only [reidRay]
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only
  rw [show log (t : ℂ) + ((θ + c : ℝ) : ℂ) * I = (log (t : ℂ) + θ * I) + c * I by
    push_cast; ring, reidKernel_add_mul_I hc, show ((θ + c : ℝ) : ℂ) * I = θ * I + c * I by
    push_cast; ring, exp_add]
  ring

/-- Shifting an arc by `c` with `e^{3cI} = 1` rotates `z` and multiplies by a constant. -/
theorem reidArc_add {c : ℝ} (hc : exp (3 * (c * I)) = 1) (z p : ℂ) (α β : ℝ) :
    reidArc z p (α + c) (β + c) =
      exp (c * I) * exp (-p * (c * I)) * reidArc (z * exp (c * I)) p α β := by
  simp only [reidArc]
  rw [← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_comp_add_right (fun θ : ℝ => I * exp (θ * I) * reidKernel z p (θ * I)) c]
  refine intervalIntegral.integral_congr fun θ _ => ?_
  rw [show ((θ + c : ℝ) : ℂ) * I = θ * I + c * I by push_cast; ring, reidKernel_add_mul_I hc,
    exp_add]
  ring

/-- Rotation covariance of the Reid contour integrals. -/
theorem reidContour_add {c : ℝ} (hc : exp (3 * (c * I)) = 1) (z p : ℂ) (α β : ℝ) :
    reidContour z p (α + c) (β + c) =
      exp (c * I) * exp (-p * (c * I)) * reidContour (z * exp (c * I)) p α β := by
  simp only [reidContour, reidRay_add hc, reidArc_add hc]
  ring

/-- `e^{3 (2π/3) i} = 1`. -/
theorem exp_three_two_pi_div_three : exp (3 * (((2 * π / 3 : ℝ) : ℂ) * I)) = 1 := by
  rw [show 3 * (((2 * π / 3 : ℝ) : ℂ) * I) = 2 * π * I by push_cast; ring, exp_two_pi_mul_I]

/-- `e^{-3 (2π/3) i} = 1`. -/
theorem exp_three_neg_two_pi_div_three : exp (3 * (((-(2 * π / 3) : ℝ) : ℂ) * I)) = 1 := by
  rw [show 3 * (((-(2 * π / 3) : ℝ) : ℂ) * I) = -(2 * π * I) by push_cast; ring, exp_neg,
    exp_two_pi_mul_I, inv_one]

/-- The arc integrand is continuous. -/
theorem continuous_reidArc_integrand (z p : ℂ) :
    Continuous fun θ : ℝ => I * exp (θ * I) * reidKernel z p (θ * I) := by
  unfold reidKernel; fun_prop

/-- Additivity of Reid arcs over adjacent angular intervals. -/
theorem reidArc_add_adjacent (z p : ℂ) (a b c : ℝ) :
    reidArc z p a b + reidArc z p b c = reidArc z p a c :=
  intervalIntegral.integral_add_adjacent_intervals
    ((continuous_reidArc_integrand z p).intervalIntegrable _ _)
    ((continuous_reidArc_integrand z p).intervalIntegrable _ _)

/-- A degenerate Reid arc vanishes. -/
theorem reidArc_self (z p : ℂ) (a : ℝ) : reidArc z p a a = 0 :=
  intervalIntegral.integral_same

/-- For integral `p`, the ray at angle `2π` equals the ray at angle `0`. -/
theorem reidRay_two_pi (z : ℂ) (p : ℤ) (r : ℝ) : reidRay z p (2 * π) r = reidRay z p 0 r := by
  have hc : exp (3 * (((2 * π : ℝ) : ℂ) * I)) = 1 := by
    rw [show 3 * (((2 * π : ℝ) : ℂ) * I) = ((3 : ℤ) : ℂ) * (2 * π * I) by push_cast; ring,
      exp_int_mul_two_pi_mul_I]
  have h1 : exp (((2 * π : ℝ) : ℂ) * I) = 1 := by push_cast; exact exp_two_pi_mul_I
  have h2 : exp (-(p : ℂ) * (((2 * π : ℝ) : ℂ) * I)) = 1 := by
    rw [show -(p : ℂ) * (((2 * π : ℝ) : ℂ) * I) = ((-p : ℤ) : ℂ) * (2 * π * I) by push_cast; ring,
      exp_int_mul_two_pi_mul_I]
  have h := reidRay_add hc z p 0 r
  rw [zero_add, h1, h2] at h
  simpa using h

/-- The derivative of the Reid kernel in the logarithmic variable. -/
theorem hasDerivAt_reidKernel (z q w : ℂ) :
    HasDerivAt (reidKernel z q) (reidKernel z q w * (-q + z * exp w - exp (3 * w))) w := by
  have h : HasDerivAt (fun w => -q * w + z * exp w - exp (3 * w) / 3)
      (-q + z * exp w - exp (3 * w)) w := by
    have h1 := ((hasDerivAt_id w).const_mul (-q))
    have h2 := (hasDerivAt_exp w).const_mul z
    have h3 := (((hasDerivAt_id w).const_mul 3).cexp).div_const 3
    exact ((h1.add h2).sub h3).congr_deriv (by simp only [id]; ring)
  exact h.cexp

/-- The arc integrand of the 9.13.32 combination is an exact derivative. -/
theorem reidArc_integrand_identity (z : ℂ) (p : ℂ) (θ : ℝ) :
    I * exp (θ * I) * reidKernel z (p - 3) (θ * I) -
        z * (I * exp (θ * I) * reidKernel z (p - 1) (θ * I)) +
        (p - 1) * (I * exp (θ * I) * reidKernel z p (θ * I)) =
      -(reidKernel z (p - 1) (θ * I) * (-(p - 1) + z * exp (θ * I) - exp (3 * (θ * I))) * I) := by
  have e1 : reidKernel z (p - 3) (θ * I) = reidKernel z (p - 1) (θ * I) * exp (2 * (θ * I)) := by
    simp only [reidKernel]; rw [← exp_add]; congr 1; ring
  have e2 : reidKernel z p (θ * I) * exp (θ * I) = reidKernel z (p - 1) (θ * I) := by
    simp only [reidKernel]; rw [← exp_add]; congr 1; ring
  have e3 : exp (θ * I) * exp (2 * (θ * I)) = exp (3 * (θ * I)) := by
    rw [← exp_add]; congr 1; ring
  rw [e1]
  linear_combination (I * reidKernel z (p - 1) (θ * I)) * e3 + (p - 1) * I * e2

/-- `e^w K_p(w) = K_{p-1}(w)`. -/
theorem exp_mul_reidKernel (z p w : ℂ) : exp w * reidKernel z p w = reidKernel z (p - 1) w := by
  simp only [reidKernel]; rw [← exp_add]; congr 1; ring

/-- The `z`-derivative of the Reid kernel. -/
theorem hasDerivAt_reidKernel_z (z p w : ℂ) :
    HasDerivAt (fun z => reidKernel z p w) (reidKernel z (p - 1) w) z := by
  rw [← exp_mul_reidKernel]
  have h : HasDerivAt (fun z => -p * w + z * exp w - exp (3 * w) / 3) (exp w) z := by
    simpa using ((hasDerivAt_id z).mul_const (exp w)).const_add (-p * w) |>.sub_const
      (exp (3 * w) / 3)
  simpa only [reidKernel, mul_comm] using h.cexp

/-- Norm of the Reid kernel on the unit circle. -/
theorem norm_reidKernel_circle_le (z p : ℂ) (θ : ℝ) :
    ‖reidKernel z p (θ * I)‖ ≤ Real.exp (θ * p.im + ‖z‖ + 1 / 3) := by
  rw [reidKernel, norm_exp]
  refine Real.exp_le_exp.mpr ?_
  have h1 : (z * exp (θ * I)).re ≤ ‖z‖ := by
    have := re_le_norm (z * exp (θ * I))
    rwa [norm_mul, norm_exp_ofReal_mul_I, mul_one] at this
  have h2 : -(exp (3 * (θ * I)) / 3).re ≤ 1 / 3 := by
    have := (neg_le_abs (exp (3 * (θ * I)) / 3).re).trans (abs_re_le_norm (exp (3 * (θ * I)) / 3))
    rw [norm_div, show 3 * ((θ : ℂ) * I) = ((3 * θ : ℝ) : ℂ) * I by push_cast; ring,
      norm_exp_ofReal_mul_I] at this
    rw [div_re] at this ⊢
    simpa [mul_assoc] using this
  have h3 : (-p * (θ * I)).re = θ * p.im := by simp; ring
  simp only [add_re, sub_re, h3]
  linarith

/-- Differentiation of a Reid arc in `z`. -/
theorem hasDerivAt_reidArc (p : ℂ) (α β : ℝ) (z : ℂ) :
    HasDerivAt (fun z => reidArc z p α β) (reidArc z (p - 1) α β) z := by
  have hc : ∀ q : ℂ, ∀ z, Continuous fun θ : ℝ => I * exp (θ * I) * reidKernel z q (θ * I) :=
    fun q z => continuous_reidArc_integrand z q
  have h := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (a := α) (b := β) (x₀ := z) (s := Metric.ball z 1)
    (F := fun z θ => I * exp (θ * I) * reidKernel z p (θ * I))
    (F' := fun z θ => I * exp (θ * I) * reidKernel z (p - 1) (θ * I))
    (bound := fun θ => Real.exp (θ * (p - 1).im + (‖z‖ + 1) + 1 / 3))
    (Metric.ball_mem_nhds z one_pos)
    (Eventually.of_forall fun z => (hc p z).aestronglyMeasurable)
    ((hc p z).intervalIntegrable _ _) (hc (p - 1) z).aestronglyMeasurable
    (ae_of_all _ fun θ _ x hx => by
      rw [norm_mul, norm_mul, norm_I, norm_exp_ofReal_mul_I, one_mul, one_mul]
      refine (norm_reidKernel_circle_le x (p - 1) θ).trans (Real.exp_le_exp.mpr ?_)
      have : ‖x‖ ≤ ‖z‖ + 1 := by
        have := norm_le_norm_add_norm_sub' x z
        rw [Metric.mem_ball, dist_eq_norm] at hx; linarith
      linarith)
    ((by fun_prop : Continuous fun θ : ℝ => Real.exp (θ * (p - 1).im + (‖z‖ + 1) + 1 / 3)).intervalIntegrable _ _)
    (ae_of_all _ fun θ _ x _ => (hasDerivAt_reidKernel_z x p (θ * I)).const_mul (I * exp (θ * I)))
  exact h.2

/-- The `z`-derivative of `B₀`. -/
theorem deriv_reidAiryB0 (p : ℤ) :
    deriv (fun t => reidAiryB0 t p) = fun t => reidAiryB0 t (p - 1) := by
  funext z
  have h := (hasDerivAt_reidArc (p : ℂ) 0 (2 * π) z).div_const (2 * π * I)
  simp only [reidAiryB0]
  push_cast
  exact h.deriv

/-- The 9.13.32 combination of arc integrals is a boundary term. -/
theorem reidArc_difference (z p : ℂ) (α β : ℝ) :
    reidArc z (p - 3) α β - z * reidArc z (p - 1) α β + (p - 1) * reidArc z p α β =
      reidKernel z (p - 1) (α * I) - reidKernel z (p - 1) (β * I) := by
  have hc := continuous_reidArc_integrand
  have hF : ∀ θ : ℝ, HasDerivAt (fun θ : ℝ => reidKernel z (p - 1) (θ * I))
      (reidKernel z (p - 1) (θ * I) * (-(p - 1) + z * exp (θ * I) -
        exp (3 * (θ * I))) * I) θ := by
    intro θ
    have h := (hasDerivAt_reidKernel z (p - 1) ((θ : ℂ) * I)).comp (θ : ℂ)
      ((hasDerivAt_id (θ : ℂ)).mul_const I)
    simpa using h.comp_ofReal
  have hcont : Continuous fun θ : ℝ => reidKernel z (p - 1) (θ * I) *
      (-(p - 1) + z * exp (θ * I) - exp (3 * (θ * I))) * I := by
    unfold reidKernel; fun_prop
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := α) (b := β)
    (fun θ _ => hF θ) (hcont.intervalIntegrable _ _)
  have key : ∫ θ : ℝ in α..β, (I * exp (θ * I) * reidKernel z (p - 3) (θ * I) -
        z * (I * exp (θ * I) * reidKernel z (p - 1) (θ * I)) +
        (p - 1) * (I * exp (θ * I) * reidKernel z p (θ * I))) =
      reidKernel z (p - 1) (α * I) - reidKernel z (p - 1) (β * I) := by
    rw [intervalIntegral.integral_congr (g := fun θ : ℝ => -(reidKernel z (p - 1) (θ * I) *
      (-(p - 1) + z * exp (θ * I) - exp (3 * (θ * I))) * I))
      (fun θ _ => reidArc_integrand_identity z p θ), intervalIntegral.integral_neg, hFTC]
    ring
  have i1 : IntervalIntegrable (fun θ : ℝ => I * exp (θ * I) * reidKernel z (p - 3) (θ * I))
      volume α β := (hc _ _).intervalIntegrable _ _
  have i2 : IntervalIntegrable
      (fun θ : ℝ => z * (I * exp (θ * I) * reidKernel z (p - 1) (θ * I))) volume α β :=
    ((hc _ _).const_mul _).intervalIntegrable _ _
  have i3 : IntervalIntegrable
      (fun θ : ℝ => (p - 1) * (I * exp (θ * I) * reidKernel z p (θ * I))) volume α β :=
    ((hc _ _).const_mul _).intervalIntegrable _ _
  rw [intervalIntegral.integral_add (i1.sub i2) i3, intervalIntegral.integral_sub i1 i2,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at key
  simpa only [reidArc] using key

/-- An elementary bound: `B t - t³/3 + t ≤ (B + 1)² + 3` for `t ≥ 0`, `B ≥ 0`. -/
lemma cubic_bound_aux {B t : ℝ} (hB : 0 ≤ B) (ht : 0 ≤ t) :
    B * t - t ^ 3 / 3 + t ≤ (B + 1) ^ 2 + 3 := by
  nlinarith [sq_nonneg (t - (B + 1)), sq_nonneg (t - 1), mul_nonneg ht hB, sq_nonneg t,
    mul_nonneg ht (sq_nonneg (t - 1)), mul_nonneg ht (sq_nonneg (t - (B+1)))]

/-- The Reid kernel on the ray through `e^{θI}`, when `e^{3θI} = 1`. -/
theorem reidKernel_log_add {θ : ℝ} (hc : exp (3 * (θ * I)) = 1) (z q : ℂ) {t : ℝ} (ht : 0 < t) :
    reidKernel z q (log t + θ * I) =
      exp (-q * (log t + θ * I) + z * (t * exp (θ * I)) - (t : ℂ) ^ 3 / 3) := by
  have ht' : exp (log (t : ℂ)) = t := exp_log (ofReal_ne_zero.mpr ht.ne')
  have h3 : exp (3 * (log (t : ℂ) + θ * I)) = (t : ℂ) ^ 3 := by
    rw [mul_add, exp_add, hc, mul_one,
      show exp (3 * log (t : ℂ)) = exp (log (t : ℂ)) ^ 3 by rw [← exp_nat_mul]; push_cast; ring_nf,
      ht']
  rw [reidKernel, exp_add (log (t : ℂ)), ht', h3]

/-- A uniform exponential bound for the Reid kernel on a ray. -/
theorem norm_reidKernel_ray_le {θ : ℝ} (hc : exp (3 * (θ * I)) = 1) (z q : ℂ) {t : ℝ}
    (ht : 0 < t) (hq : 1 ≤ t ∨ q.re ≤ 0) :
    ‖reidKernel z q (log t + θ * I)‖ ≤
      Real.exp (|θ| * ‖q‖ + (‖q‖ + ‖z‖ + 1) ^ 2 + 3) * Real.exp (-t) := by
  rw [reidKernel_log_add hc z q ht, norm_exp, ← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have hlog : (log (t : ℂ)) = (Real.log t : ℂ) := (ofReal_log ht.le).symm
  have hre : (-q * (log t + θ * I) + z * (t * exp (θ * I)) - (t : ℂ) ^ 3 / 3).re =
      -q.re * Real.log t + q.im * θ + (z * exp (θ * I)).re * t - t ^ 3 / 3 := by
    rw [hlog]
    simp [pow_succ, mul_re, mul_im]
    ring
  rw [hre]
  have h1 : -q.re * Real.log t ≤ ‖q‖ * t := by
    rcases le_or_gt 0 (Real.log t) with hl | hl
    · have := Real.log_le_sub_one_of_pos ht
      have hq' : -q.re ≤ ‖q‖ := (neg_le_abs _).trans (abs_re_le_norm q)
      nlinarith [norm_nonneg q]
    · have : q.re ≤ 0 := by
        rcases hq with h | h
        · exact absurd (Real.log_nonneg h) (not_le.mpr hl)
        · exact h
      nlinarith [norm_nonneg q]
  have h2 : q.im * θ ≤ |θ| * ‖q‖ := by
    have := abs_mul q.im θ
    have : |q.im| ≤ ‖q‖ := abs_im_le_norm q
    nlinarith [le_abs_self (q.im * θ), abs_nonneg θ]
  have h3 : (z * exp (θ * I)).re * t ≤ ‖z‖ * t := by
    have := re_le_norm (z * exp (θ * I))
    rw [norm_mul, norm_exp_ofReal_mul_I, mul_one] at this
    exact mul_le_mul_of_nonneg_right this ht.le
  have h4 := cubic_bound_aux (B := ‖q‖ + ‖z‖) (by positivity) ht.le
  nlinarith

/-- Measurability of the Reid ray integrand. -/
theorem measurable_reidRay_integrand (θ : ℝ) (z q : ℂ) :
    Measurable fun t : ℝ => exp (θ * I) * reidKernel z q (log t + θ * I) := by
  unfold reidKernel
  have : Measurable fun t : ℝ => log (t : ℂ) := measurable_log.comp measurable_ofReal
  fun_prop

/-- Integrability of the Reid ray integrand. -/
theorem integrableOn_reidRay {θ : ℝ} (hc : exp (3 * (θ * I)) = 1) (z q : ℂ) {r : ℝ}
    (hr : 0 ≤ r) (hq : 1 ≤ r ∨ q.re ≤ 0) :
    IntegrableOn (fun t : ℝ => exp (θ * I) * reidKernel z q (log t + θ * I)) (Ioi r) := by
  have hint : IntegrableOn (fun t : ℝ => Real.exp (|θ| * ‖q‖ + (‖q‖ + ‖z‖ + 1) ^ 2 + 3) *
      Real.exp (-1 * t)) (Ioi r) := (exp_neg_integrableOn_Ioi r one_pos).const_mul _
  refine hint.mono' (measurable_reidRay_integrand θ z q).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : r < t)
  rw [norm_mul, norm_exp_ofReal_mul_I, one_mul, neg_one_mul]
  exact norm_reidKernel_ray_le hc z q (hr.trans_lt ht)
    (hq.imp (fun h => h.trans ht.le) id)

/-- Differentiation of a Reid ray integral in `z`. -/
theorem hasDerivAt_reidRay {θ : ℝ} (hc : exp (3 * (θ * I)) = 1) (p : ℂ) {r : ℝ}
    (hr : 0 ≤ r) (hq : 1 ≤ r ∨ p.re ≤ 0) (z : ℂ) :
    HasDerivAt (fun z => reidRay z p θ r) (reidRay z (p - 1) θ r) z := by
  have hq1 : 1 ≤ r ∨ (p - 1).re ≤ 0 := hq.imp id (fun h => by simp; linarith)
  set C : ℝ := Real.exp (|θ| * ‖p - 1‖ + (‖p - 1‖ + (‖z‖ + 1) + 1) ^ 2 + 3)
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi r))
    (x₀ := z) (s := Metric.ball z 1)
    (F := fun z t => exp (θ * I) * reidKernel z p (log t + θ * I))
    (F' := fun z t => exp (θ * I) * reidKernel z (p - 1) (log t + θ * I))
    (bound := fun t => C * Real.exp (-1 * t))
    (Metric.ball_mem_nhds z one_pos)
    (Eventually.of_forall fun x => (measurable_reidRay_integrand θ x p).aestronglyMeasurable)
    (integrableOn_reidRay hc z p hr hq)
    (measurable_reidRay_integrand θ z (p - 1)).aestronglyMeasurable
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : r < t) x hx
      rw [norm_mul, norm_exp_ofReal_mul_I, one_mul, neg_one_mul]
      refine (norm_reidKernel_ray_le hc x (p - 1) (hr.trans_lt ht)
        (hq1.imp (fun h => h.trans ht.le) id)).trans ?_
      refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le
      have : ‖x‖ ≤ ‖z‖ + 1 := by
        have := norm_le_norm_add_norm_sub' x z
        rw [Metric.mem_ball, dist_eq_norm] at hx; linarith
      have h0 : 0 ≤ ‖p - 1‖ + ‖x‖ + 1 := by positivity
      nlinarith)
    ((exp_neg_integrableOn_Ioi r one_pos).const_mul C)
    (ae_of_all _ fun t x _ => (hasDerivAt_reidKernel_z x p (log t + θ * I)).const_mul _)
  exact h.2

/-- On a ray, the 9.13.32 integrand combination is an exact `t`-derivative. -/
theorem hasDerivAt_reidKernel_log (z q : ℂ) (θ : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun t : ℝ => reidKernel z (q - 1) (log t + θ * I))
      (-(exp (θ * I) * reidKernel z (q - 3) (log t + θ * I) -
        z * (exp (θ * I) * reidKernel z (q - 1) (log t + θ * I)) +
        (q - 1) * (exp (θ * I) * reidKernel z q (log t + θ * I)))) t := by
  have hl : HasDerivAt (fun t : ℝ => log (t : ℂ) + θ * I) (1 / t) t := by
    have := ((hasDerivAt_id t).ofReal_comp).clog_real (by simpa using ht)
    simpa using this.add_const ((θ : ℂ) * I)
  have h := (hasDerivAt_reidKernel z (q - 1) (log t + θ * I)).comp t hl
  refine HasDerivAt.congr_deriv h ?_
  set w : ℂ := log (t : ℂ) + θ * I
  have hE : exp w = t * exp (θ * I) := by
    simp only [w]; rw [exp_add, exp_log (ofReal_ne_zero.mpr ht.ne')]
  have k1 : reidKernel z (q - 1) w = exp w * reidKernel z q w := (exp_mul_reidKernel z q w).symm
  have k3 : reidKernel z (q - 3) w = exp w ^ 3 * reidKernel z q w := by
    simp only [reidKernel]; rw [← exp_nat_mul, ← exp_add]; congr 1; push_cast; ring
  have e3 : exp (3 * w) = exp w ^ 3 := by rw [← exp_nat_mul]; push_cast; ring_nf
  have ht' : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
  rw [k1, k3, e3, hE]
  field_simp
  ring

/-- FTC on a Reid ray: the 9.13.32 combination equals the lower boundary value. -/
theorem reidRay_difference {θ : ℝ} (hc : exp (3 * (θ * I)) = 1) (z p : ℂ) {r : ℝ}
    (hr : 0 ≤ r) (hq : 1 ≤ r ∨ p.re ≤ 0) {g : ℝ → ℂ}
    (hg : ∀ t, 0 < t → g t = reidKernel z (p - 1) (log t + θ * I))
    (hgc : ContinuousWithinAt g (Ici r) r) :
    reidRay z (p - 3) θ r - z * reidRay z (p - 1) θ r + (p - 1) * reidRay z p θ r = g r := by
  have hq1 : 1 ≤ r ∨ (p - 1).re ≤ 0 := hq.imp id (fun h => by simp; linarith)
  have hq3 : 1 ≤ r ∨ (p - 3).re ≤ 0 := hq.imp id (fun h => by simp; linarith)
  have i1 := integrableOn_reidRay hc z (p - 3) hr hq3
  have i2 := (integrableOn_reidRay hc z (p - 1) hr hq1).const_mul z
  have i3 := (integrableOn_reidRay hc z p hr hq).const_mul (p - 1)
  have hderiv : ∀ t ∈ Ioi r, HasDerivAt g
      (-(exp (θ * I) * reidKernel z (p - 3) (log t + θ * I) -
        z * (exp (θ * I) * reidKernel z (p - 1) (log t + θ * I)) +
        (p - 1) * (exp (θ * I) * reidKernel z p (log t + θ * I)))) t := by
    intro t (ht : r < t)
    have ht0 : 0 < t := hr.trans_lt ht
    refine (hasDerivAt_reidKernel_log z p θ ht0).congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds ht0] with u (hu : 0 < u) using hg u hu
  have hlim : Tendsto g atTop (𝓝 0) := by
    have hb : Tendsto (fun t : ℝ => Real.exp (|θ| * ‖p - 1‖ + (‖p - 1‖ + ‖z‖ + 1) ^ 2 + 3) *
        Real.exp (-t)) atTop (𝓝 0) := by
      simpa using Real.tendsto_exp_neg_atTop_nhds_zero.const_mul
        (Real.exp (|θ| * ‖p - 1‖ + (‖p - 1‖ + ‖z‖ + 1) ^ 2 + 3))
    refine squeeze_zero_norm' ?_ hb
    filter_upwards [eventually_ge_atTop 1] with t ht
    rw [hg t (by linarith)]
    exact norm_reidKernel_ray_le hc z (p - 1) (by linarith) (Or.inl ht)
  have hFTC := integral_Ioi_of_hasDerivAt_of_tendsto hgc hderiv
    ((i1.sub i2).add i3).neg hlim
  have hsplit : ∫ t in Ioi r, (exp (θ * I) * reidKernel z (p - 3) (log t + θ * I) -
        z * (exp (θ * I) * reidKernel z (p - 1) (log t + θ * I)) +
        (p - 1) * (exp (θ * I) * reidKernel z p (log t + θ * I))) =
      reidRay z (p - 3) θ r - z * reidRay z (p - 1) θ r + (p - 1) * reidRay z p θ r := by
    rw [integral_add _ i3, integral_sub i1 i2, integral_const_mul z, integral_const_mul (p - 1)]
    · rfl
    · exact i1.sub i2
  rw [integral_neg, hsplit] at hFTC
  linear_combination -hFTC

/-- `e^{3θI} = 1` at the angles `θ = 2πn/3`. -/
theorem exp_three_mul_of_eq {θ : ℝ} (n : ℤ) (h : θ = n * (2 * π / 3)) :
    exp (3 * (θ * I)) = 1 := by
  rw [h, show 3 * ((((n : ℝ) * (2 * π / 3) : ℝ) : ℂ) * I) = (n : ℂ) * (2 * π * I) by
    push_cast; ring, exp_int_mul_two_pi_mul_I]

/-- The 9.13.32 combination vanishes on a Reid contour. -/
theorem reidContour_difference {α β : ℝ} (hα : exp (3 * (α * I)) = 1)
    (hβ : exp (3 * (β * I)) = 1) (z p : ℂ) :
    reidContour z (p - 3) α β - z * reidContour z (p - 1) α β + (p - 1) * reidContour z p α β =
      0 := by
  have hray : ∀ {θ : ℝ}, exp (3 * (θ * I)) = 1 →
      reidRay z (p - 3) θ 1 - z * reidRay z (p - 1) θ 1 + (p - 1) * reidRay z p θ 1 =
        reidKernel z (p - 1) (θ * I) := by
    intro θ hc
    have h := reidRay_difference hc z p zero_le_one (Or.inl le_rfl)
      (g := fun t : ℝ => reidKernel z (p - 1) (log t + θ * I)) (fun _ _ => rfl)
      (hasDerivAt_reidKernel_log z p θ one_pos).continuousAt.continuousWithinAt
    simpa using h
  have h1 := hray hα
  have h2 := hray hβ
  have h3 := reidArc_difference z p α β
  simp only [reidContour]
  linear_combination -h1 + h3 + h2

/-- Differentiation of a Reid contour integral in `z`. -/
theorem hasDerivAt_reidContour {α β : ℝ} (hα : exp (3 * (α * I)) = 1)
    (hβ : exp (3 * (β * I)) = 1) (p z : ℂ) :
    HasDerivAt (fun z => reidContour z p α β) (reidContour z (p - 1) α β) z := by
  have h1 := hasDerivAt_reidRay hα p zero_le_one (Or.inl le_rfl) z
  have h2 := hasDerivAt_reidArc p α β z
  have h3 := hasDerivAt_reidRay hβ p zero_le_one (Or.inl le_rfl) z
  exact (h1.neg.add h2).add h3

/-- Each `A_k` is a Reid contour integral between two admissible angles. -/
theorem reidAiryA_angles (k : Fin 3) :
    ∃ α β : ℝ, exp (3 * (α * I)) = 1 ∧ exp (3 * (β * I)) = 1 ∧
      ∀ z p, reidAiryA k z p = reidContour z p α β / (2 * π * I) := by
  fin_cases k
  · exact ⟨4 * π / 3, 2 * π / 3, exp_three_mul_of_eq 2 (by push_cast; ring),
      exp_three_mul_of_eq 1 (by push_cast; ring), fun z p => rfl⟩
  · exact ⟨2 * π, 4 * π / 3, exp_three_mul_of_eq 3 (by push_cast; ring),
      exp_three_mul_of_eq 2 (by push_cast; ring), fun z p => rfl⟩
  · exact ⟨2 * π / 3, 0, exp_three_mul_of_eq 1 (by push_cast; ring),
      exp_three_mul_of_eq 0 (by push_cast; ring), fun z p => rfl⟩

/-- The `z`-derivative of `A_k` lowers `p` by one. -/
theorem deriv_reidAiryA (k : Fin 3) (p : ℂ) :
    deriv (fun t => reidAiryA k t p) = fun t => reidAiryA k t (p - 1) := by
  obtain ⟨α, β, hα, hβ, hA⟩ := reidAiryA_angles k
  funext z
  simp only [hA]
  exact ((hasDerivAt_reidContour hα hβ p z).div_const _).deriv

/-- The Reid ray angles `2πk/3` are admissible. -/
theorem exp_three_reidAiryB_angle (k : Fin 3) :
    exp (3 * (((2 * k.val * π / 3 : ℝ) : ℂ) * I)) = 1 :=
  exp_three_mul_of_eq k.val (by push_cast; ring)

/-- The `z`-derivative of `B_k` lowers `p` by one, for `p ≤ 0`. -/
theorem deriv_reidAiryB (k : Fin 3) {p : ℤ} (hp : p ≤ 0) :
    deriv (fun t => reidAiryB k t p) = fun t => reidAiryB k t (p - 1) := by
  funext z
  simp only [reidAiryB_ordinary_ray k _ hp, reidAiryB_ordinary_ray k _ (by omega : p - 1 ≤ 0)]
  have h := hasDerivAt_reidRay (exp_three_reidAiryB_angle k) (p : ℂ) le_rfl
    (Or.inr (by simpa using hp)) z
  push_cast
  exact h.deriv

/-- The 9.13.32 combination of ordinary Reid ray integrals from `0`. -/
theorem reidRay_zero_difference {θ : ℝ} (hc : exp (3 * (θ * I)) = 1) (z : ℂ) {p : ℤ}
    (hp : p ≤ 0) :
    reidRay z ((p : ℂ) - 3) θ 0 - z * reidRay z ((p : ℂ) - 1) θ 0 +
      ((p : ℂ) - 1) * reidRay z p θ 0 = 0 := by
  set n : ℕ := (1 - p).toNat
  have hn : ((n : ℤ) : ℂ) = 1 - p := by
    have : ((1 - p).toNat : ℤ) = 1 - p := Int.toNat_of_nonneg (by omega)
    simp only [n]; rw [this]; push_cast; ring
  have hn1 : n ≠ 0 := by omega
  have h := reidRay_difference hc z (p : ℂ) le_rfl (Or.inr (by simpa using hp))
    (g := fun t : ℝ => exp (-((p : ℂ) - 1) * (θ * I)) * (t : ℂ) ^ n *
      exp (z * (t * exp (θ * I)) - (t : ℂ) ^ 3 / 3))
    (fun t ht => by
      rw [reidKernel_log_add hc z _ ht]
      have ht' : exp (log (t : ℂ)) = t := exp_log (ofReal_ne_zero.mpr ht.ne')
      have e : exp (-((p : ℂ) - 1) * log t) = (t : ℂ) ^ n := by
        rw [show -((p : ℂ) - 1) * log t = (n : ℕ) * log t by
          rw [show ((n : ℕ) : ℂ) = ((n : ℤ) : ℂ) by push_cast; rfl, hn]; ring,
          exp_nat_mul, ht']
      rw [← e, ← exp_add, ← exp_add]
      congr 1; ring)
    (by fun_prop : Continuous fun t : ℝ => exp (-((p : ℂ) - 1) * (θ * I)) * (t : ℂ) ^ n *
      exp (z * (t * exp (θ * I)) - (t : ℂ) ^ 3 / 3)).continuousWithinAt
  rw [h]
  simp [zero_pow hn1]

/-- On the unit circle, the Reid kernel with `p = -n` is a polynomial times `e^{zu-u³/3}`. -/
theorem reidKernel_neg_nat_mul_I (z : ℂ) (n : ℕ) (θ : ℝ) :
    reidKernel z (-(n : ℂ)) (θ * I) =
      exp (θ * I) ^ n * exp (z * exp (θ * I) - exp (θ * I) ^ 3 / 3) := by
  rw [reidKernel, ← exp_nat_mul, ← exp_nat_mul, ← exp_add]
  congr 1; push_cast; ring

/-- On an admissible ray, the Reid kernel with `p = -n` is `u^n e^{zu-u³/3}` at `u = t e^{θI}`. -/
theorem reidKernel_neg_nat_log {θ : ℝ} (hc : exp (3 * (θ * I)) = 1) (z : ℂ) (n : ℕ) {t : ℝ}
    (ht : 0 < t) :
    reidKernel z (-(n : ℂ)) (log t + θ * I) =
      (t * exp (θ * I)) ^ n * exp (z * (t * exp (θ * I)) - (t * exp (θ * I)) ^ 3 / 3) := by
  rw [reidKernel_log_add hc z _ ht]
  have ht' : exp (log (t : ℂ)) = t := exp_log (ofReal_ne_zero.mpr ht.ne')
  have h3 : (t * exp (θ * I)) ^ 3 = (t : ℂ) ^ 3 := by
    rw [mul_pow, ← exp_nat_mul, show ((3 : ℕ) : ℂ) * (θ * I) = 3 * (θ * I) by push_cast; ring,
      hc, mul_one]
  have hn : (t * exp (θ * I)) ^ n = exp (n * (log t + θ * I)) := by
    rw [exp_nat_mul, exp_add, ht']
  rw [h3, hn, ← exp_add]
  congr 1; ring

/-- For `p = -n`, cutting a Reid contour at radius `1` or at `0` gives the same value. -/
theorem reidContour_neg_nat_eq {α β : ℝ} (hα : exp (3 * (α * I)) = 1)
    (hβ : exp (3 * (β * I)) = 1) (z : ℂ) (n : ℕ) :
    reidContour z (-(n : ℂ)) α β = -reidRay z (-(n : ℂ)) α 0 + reidRay z (-(n : ℂ)) β 0 := by
  set f : ℂ → ℂ := fun u => u ^ n * exp (z * u - u ^ 3 / 3)
  have hfd : Differentiable ℂ f := by fun_prop
  obtain ⟨F, hF⟩ := (hfd.differentiableOn (s := Metric.ball (0 : ℂ) 2)).isExactOn_ball
  have hcirc : ∀ θ : ℝ, exp (θ * I) ∈ Metric.ball (0 : ℂ) 2 := fun θ => by
    simp [norm_exp_ofReal_mul_I]
  -- the arc
  have harc : reidArc z (-(n : ℂ)) α β = F (exp (β * I)) - F (exp (α * I)) := by
    have hd : ∀ θ : ℝ, HasDerivAt (fun θ : ℝ => F (exp (θ * I)))
        (I * exp (θ * I) * reidKernel z (-(n : ℂ)) (θ * I)) θ := by
      intro θ
      have h1 : HasDerivAt (fun θ : ℝ => exp ((θ : ℂ) * I)) (exp (θ * I) * (1 * I)) θ :=
        (((hasDerivAt_id θ).ofReal_comp).mul_const I).cexp
      refine ((hF _ (hcirc θ)).comp θ h1).congr_deriv ?_
      rw [reidKernel_neg_nat_mul_I]; simp only [f]; ring
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ => hd θ)
      ((continuous_reidArc_integrand z _).intervalIntegrable _ _)
  -- the segments
  have hseg : ∀ {θ : ℝ}, exp (3 * (θ * I)) = 1 →
      reidRay z (-(n : ℂ)) θ 0 = (F (exp (θ * I)) - F 0) + reidRay z (-(n : ℂ)) θ 1 := by
    intro θ hc
    have hint := integrableOn_reidRay hc z (-(n : ℂ)) le_rfl (Or.inr (by simp))
    have hd : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun t : ℝ => F (t * exp (θ * I)))
        (f (t * exp (θ * I)) * exp (θ * I)) t := by
      intro t ht
      rw [uIcc_of_le zero_le_one] at ht
      have hm : (t : ℂ) * exp (θ * I) ∈ Metric.ball (0 : ℂ) 2 := by
        rw [Metric.mem_ball, dist_zero_right, norm_mul, norm_exp_ofReal_mul_I, mul_one,
          norm_real, Real.norm_of_nonneg ht.1]
        linarith [ht.2]
      have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) * exp (θ * I)) (1 * exp (θ * I)) t :=
        ((hasDerivAt_id t).ofReal_comp).mul_const _
      exact ((hF _ hm).comp t h1).congr_deriv (by ring)
    have hcont : Continuous fun t : ℝ => f (t * exp (θ * I)) * exp (θ * I) := by
      simp only [f]; fun_prop
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hcont.intervalIntegrable _ _)
    have hcongr : ∫ t in (0 : ℝ)..1, exp (θ * I) * reidKernel z (-(n : ℂ)) (log t + θ * I) =
        ∫ t in (0 : ℝ)..1, f (t * exp (θ * I)) * exp (θ * I) := by
      refine intervalIntegral.integral_congr_ae (ae_of_all _ fun t ht => ?_)
      rw [uIoc_of_le zero_le_one] at ht
      rw [reidKernel_neg_nat_log hc z n ht.1]; simp only [f]; ring
    simp only [ofReal_zero, zero_mul, ofReal_one, one_mul] at hFTC
    rw [← hFTC, ← hcongr, intervalIntegral.integral_of_le zero_le_one, reidRay, reidRay,
      ← setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
        (hint.mono_set Ioc_subset_Ioi_self) (hint.mono_set (Ioi_subset_Ioi zero_le_one)),
      Ioc_union_Ioi_eq_Ioi zero_le_one]
  rw [reidContour, hseg hα, hseg hβ, harc]
  ring

/-- The Reid ray from `0` at `z = 0` is a Gamma value. -/
theorem reidRay_zero_neg_nat {θ : ℝ} (hc : exp (3 * (θ * I)) = 1) (n : ℕ) :
    reidRay 0 (-(n : ℂ)) θ 0 =
      exp (θ * I) ^ (n + 1) *
        (((3 : ℝ) ^ (((n : ℝ) - 2) / 3) * Real.Gamma (((n : ℝ) + 1) / 3) : ℝ) : ℂ) := by
  rw [← integral_pow_mul_exp_neg_cube, integral_complex_ofReal.symm, reidRay,
    ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) => ?_
  have e3 : exp (θ * I) ^ 3 = 1 := by
    rw [← exp_nat_mul]; push_cast; exact hc
  rw [reidKernel_neg_nat_log hc 0 n ht, mul_pow, mul_pow, e3]
  push_cast
  ring_nf

/-- `e^{2πi/3} = -1/2 + (√3/2) i`. -/
theorem exp_two_pi_div_three_mul_I :
    exp (((2 * π / 3 : ℝ) : ℂ) * I) = -1 / 2 + (Real.sqrt 3 / 2 : ℝ) * I := by
  rw [exp_mul_I, ← ofReal_cos, ← ofReal_sin,
    show 2 * π / 3 = π - π / 3 by ring, Real.cos_pi_sub, Real.sin_pi_sub,
    Real.cos_pi_div_three, Real.sin_pi_div_three]
  push_cast; ring

/-- The initial values of `A₀(z,0)` and its derivative `A₀(z,-1)` at `z = 0`. -/
theorem reidAiryA_zero_initial :
    reidAiryA 0 0 0 = airyAi 0 ∧ reidAiryA 0 0 (-1) = airyAiDeriv 0 := by
  have hα : exp (3 * (((4 * π / 3 : ℝ) : ℂ) * I)) = 1 := exp_three_mul_of_eq 2 (by push_cast; ring)
  have hβ : exp (3 * (((2 * π / 3 : ℝ) : ℂ) * I)) = 1 := exp_three_mul_of_eq 1 (by push_cast; ring)
  have hω2 : exp (((4 * π / 3 : ℝ) : ℂ) * I) = exp (((2 * π / 3 : ℝ) : ℂ) * I) ^ 2 := by
    rw [← exp_nat_mul]; push_cast; ring_nf
  have hA : ∀ n : ℕ, reidAiryA 0 0 (-(n : ℂ)) =
      (-exp (((4 * π / 3 : ℝ) : ℂ) * I) ^ (n + 1) + exp (((2 * π / 3 : ℝ) : ℂ) * I) ^ (n + 1)) *
        (((3 : ℝ) ^ (((n : ℝ) - 2) / 3) * Real.Gamma (((n : ℝ) + 1) / 3) : ℝ) : ℂ) /
          (2 * π * I) := by
    intro n
    simp only [reidAiryA, Fin.val_zero]
    rw [reidContour_neg_nat_eq hα hβ, reidRay_zero_neg_nat hα, reidRay_zero_neg_nat hβ]
    ring
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hG := airyMod_gamma_third_reflection
  have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have I_sq : I ^ 2 = -1 := I_sq
  constructor
  · have h := hA 0
    simp only [Nat.cast_zero, neg_zero, zero_add, pow_one] at h
    rw [h, airyAi_zero, hω2, exp_two_pi_div_three_mul_I,
      show (2 / 3 : ℂ) = ((2 / 3 : ℝ) : ℂ) by push_cast; ring, Complex.Gamma_ofReal,
      show ((0 : ℝ) - 2) / 3 = -(2 / 3) by norm_num,
      Real.rpow_neg (by norm_num)]
    have hb : (0 : ℝ) < (3 : ℝ) ^ (2 / 3 : ℝ) := by positivity
    have hG2 : 0 < Real.Gamma (2 / 3) := Real.Gamma_pos_of_pos (by norm_num)
    have hb' : (((3 : ℝ) ^ (2 / 3 : ℝ) : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hb.ne'
    have hG2' : (Real.Gamma (2 / 3) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hG2.ne'
    have hGc : (Real.Gamma (1 / 3) : ℂ) * Real.Gamma (2 / 3) * Real.sqrt 3 = 2 * π := by
      exact_mod_cast hG
    have hsc : (Real.sqrt 3 : ℂ) ^ 2 = 3 := by exact_mod_cast hs
    push_cast
    field_simp
    linear_combination (-(Real.Gamma (1 / 3) : ℂ) * (Real.Gamma (2 / 3) : ℂ) * I ^ 2) * hsc + (-3 * (Real.Gamma (1 / 3) : ℂ) * (Real.Gamma (2 / 3) : ℂ)) * I_sq + (4 * I) * hGc
  · have h := hA 1
    simp only [Nat.cast_one] at h
    rw [h, airyAiDeriv_zero, hω2, exp_two_pi_div_three_mul_I,
      show (1 / 3 : ℂ) = ((1 / 3 : ℝ) : ℂ) by push_cast; ring, Complex.Gamma_ofReal,
      show ((1 : ℝ) - 2) / 3 = -(1 / 3) by norm_num, show ((1 : ℝ) + 1) / 3 = 2 / 3 by norm_num,
      Real.rpow_neg (by norm_num)]
    have hb : (0 : ℝ) < (3 : ℝ) ^ (1 / 3 : ℝ) := by positivity
    have hG1 : 0 < Real.Gamma (1 / 3) := Real.Gamma_pos_of_pos (by norm_num)
    have hb' : (((3 : ℝ) ^ (1 / 3 : ℝ) : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hb.ne'
    have hG1' : (Real.Gamma (1 / 3) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hG1.ne'
    have hGc : (Real.Gamma (1 / 3) : ℂ) * Real.Gamma (2 / 3) * Real.sqrt 3 = 2 * π := by
      exact_mod_cast hG
    have hsc : (Real.sqrt 3 : ℂ) ^ 2 = 3 := by exact_mod_cast hs
    push_cast
    field_simp
    linear_combination (-(Real.Gamma (1 / 3) : ℂ) * (Real.Gamma (2 / 3) : ℂ) * I ^ 4 * (Real.sqrt 3 : ℂ) ^ 2 - 3 * (Real.Gamma (1 / 3) : ℂ) * (Real.Gamma (2 / 3) : ℂ) * I ^ 4 + 4 * (Real.Gamma (1 / 3) : ℂ) * (Real.Gamma (2 / 3) : ℂ) * I ^ 3 * (Real.sqrt 3 : ℂ) - 2 * (Real.Gamma (1 / 3) : ℂ) * (Real.Gamma (2 / 3) : ℂ) * I ^ 2) * hsc +
      (-9 * (Real.Gamma (1 / 3) : ℂ) * (Real.Gamma (2 / 3) : ℂ) * I ^ 2 + 12 * (Real.Gamma (1 / 3) : ℂ) * (Real.Gamma (2 / 3) : ℂ) * I * (Real.sqrt 3 : ℂ) + 3 * (Real.Gamma (1 / 3) : ℂ) * (Real.Gamma (2 / 3) : ℂ)) * I_sq + (-16 * I) * hGc

/-- At `p = 0` Reid's first contour function is Airy's: `A(z, 0) = Ai(z)` on `L₁`
(DLMF 9.13.28). -/
@[dlmf 9.13.E28]
theorem reidAiryA_zero_parameter (z : ℂ) :
    reidAiryA 0 z 0 = airyAi z := by
  have hα : exp (3 * (((4 * π / 3 : ℝ) : ℂ) * I)) = 1 := exp_three_mul_of_eq 2 (by push_cast; ring)
  have hβ : exp (3 * (((2 * π / 3 : ℝ) : ℂ) * I)) = 1 := exp_three_mul_of_eq 1 (by push_cast; ring)
  have hsol : IsAirySol (fun z => reidAiryA 0 z 0) (fun z => reidAiryA 0 z (-1)) := by
    intro w
    have hd : ∀ p : ℂ, HasDerivAt (fun z => reidAiryA 0 z p) (reidAiryA 0 w (p - 1)) w :=
      fun p => (hasDerivAt_reidContour hα hβ p w).div_const _
    refine ⟨by simpa using hd 0, ?_⟩
    have h2 := hd (-1)
    have hdiff : reidAiryA 0 w (1 - 3) - w * reidAiryA 0 w (1 - 1) +
        (1 - 1) * reidAiryA 0 w 1 = 0 := by
      simp only [reidAiryA, Fin.val_zero]
      linear_combination reidContour_difference hα hβ w 1 / (2 * π * I)
    rw [show (-1 : ℂ) - 1 = 1 - 3 by norm_num] at h2
    refine h2.congr_deriv ?_
    rw [sub_self, zero_mul, add_zero] at hdiff
    linear_combination hdiff
  refine hsol.eq_of_initial isAirySol_airyAi ?_ ?_ z
  · exact reidAiryA_zero_initial.1
  · exact reidAiryA_zero_initial.2

/-- At `p = 0`, `B₀(z, 0) = 0` and the first ray function is `B(z, 0) = π Hi(z)`
(DLMF 9.13.30). -/
@[dlmf 9.13.E30]
theorem reidAiryB_zero_parameter (z : ℂ) :
    reidAiryB0 z 0 = 0 ∧ reidAiryB 0 z 0 = π * scorerHi z := by
  constructor
  · have hd : Differentiable ℂ (fun t : ℂ => exp (z * t - t ^ 3 / 3)) := by fun_prop
    have h := (hd.diffContOnCl (s := Metric.ball (0 : ℂ) 1)).circleIntegral_eq_zero zero_le_one
    simp only [circleIntegral, deriv_circleMap, circleMap_zero, ofReal_one, one_mul,
      smul_eq_mul] at h
    simp only [reidAiryB0, reidArc]
    rw [div_eq_zero_iff]; left
    rw [← h]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    simp only [reidKernel, Int.cast_zero, neg_zero, zero_mul, zero_add]
    rw [← exp_nat_mul]; push_cast; ring_nf
  · rw [reidAiryB_ordinary_ray 0 z le_rfl, (scorerHi_exp_integral z).2]
    have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
    rw [mul_div_cancel₀ _ hpi, reidRay]
    refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) => ?_
    simp only [Fin.val_zero, Nat.cast_zero, mul_zero, zero_mul, zero_div, ofReal_zero, add_zero,
      exp_zero, one_mul, reidKernel, Int.cast_zero, neg_zero]
    have ht' : exp (log (t : ℂ)) = t := exp_log (ofReal_ne_zero.mpr ht.ne')
    rw [show exp (3 * log (t : ℂ)) = exp (log (t : ℂ)) ^ 3 by rw [← exp_nat_mul]; push_cast; ring_nf,
      ht']
    ring_nf

/-- Reid's `A_k(z, p)` solves the third-order equation `w''' - z w' + (p - 1) w = 0`
(DLMF 9.13.31). -/
@[dlmf 9.13.E31]
theorem reidAiryA_ode (k : Fin 3) (z p : ℂ) :
    iteratedDeriv 3 (fun t => reidAiryA k t p) z - z * deriv (fun t => reidAiryA k t p) z + (p - 1) * reidAiryA k z p = 0 := by
  have h3 : iteratedDeriv 3 (fun t => reidAiryA k t p) = fun t => reidAiryA k t (p - 3) := by
    rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one, deriv_reidAiryA,
      deriv_reidAiryA, deriv_reidAiryA]
    funext t; congr 1; ring
  rw [h3, deriv_reidAiryA]
  beta_reduce
  obtain ⟨α, β, hα, hβ, hA⟩ := reidAiryA_angles k
  rw [hA, hA, hA]
  linear_combination reidContour_difference hα hβ z p / (2 * π * I)

/-- For `p ≤ 0`, Reid's ray function `B_k(z, p)` solves `w''' - z w' + (p - 1) w = 0`
(DLMF 9.13.31). -/
@[dlmf 9.13.E31]
theorem reidAiryB_ode (k : Fin 3) (z : ℂ) {p : ℤ} (hp : p ≤ 0) :
    iteratedDeriv 3 (fun t => reidAiryB k t p) z - z * deriv (fun t => reidAiryB k t p) z + ((p : ℂ) - 1) * reidAiryB k z p = 0 := by
  have h3 : iteratedDeriv 3 (fun t => reidAiryB k t p) = fun t => reidAiryB k t (p - 3) := by
    rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one, deriv_reidAiryB k hp,
      deriv_reidAiryB k (by omega), deriv_reidAiryB k (by omega)]
    funext t; congr 1; ring
  rw [h3, deriv_reidAiryB k hp]
  beta_reduce
  rw [reidAiryB_ordinary_ray k _ hp, reidAiryB_ordinary_ray k _ (by omega : p - 1 ≤ 0),
    reidAiryB_ordinary_ray k _ (by omega : p - 3 ≤ 0)]
  push_cast
  exact reidRay_zero_difference (exp_three_reidAiryB_angle k) z hp

/-- The difference equation `A_k(z, p-3) - z A_k(z, p-1) + (p-1) A_k(z, p) = 0`
(DLMF 9.13.32). -/
@[dlmf 9.13.E32]
theorem reidAiryA_difference (k : Fin 3) (z p : ℂ) :
    reidAiryA k z (p - 3) - z * reidAiryA k z (p - 1) + (p - 1) * reidAiryA k z p = 0 := by
  obtain ⟨α, β, hα, hβ, hA⟩ := reidAiryA_angles k
  rw [hA, hA, hA]
  linear_combination reidContour_difference hα hβ z p / (2 * π * I)

/-- For `p ≤ 0`, `B_k(z, p-3) - z B_k(z, p-1) + (p-1) B_k(z, p) = 0` (DLMF 9.13.32). -/
@[dlmf 9.13.E32]
theorem reidAiryB_difference (k : Fin 3) (z : ℂ) {p : ℤ} (hp : p ≤ 0) :
    reidAiryB k z (p - 3) - z * reidAiryB k z (p - 1) + ((p : ℂ) - 1) * reidAiryB k z p = 0 := by
  rw [reidAiryB_ordinary_ray k _ hp, reidAiryB_ordinary_ray k _ (by omega : p - 1 ≤ 0),
    reidAiryB_ordinary_ray k _ (by omega : p - 3 ≤ 0)]
  push_cast
  exact reidRay_zero_difference (exp_three_reidAiryB_angle k) z hp

/-- The closed-contour function satisfies
`B₀(z, p-3) - z B₀(z, p-1) + (p-1) B₀(z, p) = 0` for all integer `p` (DLMF 9.13.32). -/
@[dlmf 9.13.E32]
theorem reidAiryB0_difference (z : ℂ) (p : ℤ) :
    reidAiryB0 z (p - 3) - z * reidAiryB0 z (p - 1) + ((p : ℂ) - 1) * reidAiryB0 z p = 0 := by
  have hc := continuous_reidArc_integrand
  have hF : ∀ θ : ℝ, HasDerivAt (fun θ : ℝ => reidKernel z ((p : ℂ) - 1) (θ * I))
      (reidKernel z ((p : ℂ) - 1) (θ * I) * (-((p : ℂ) - 1) + z * exp (θ * I) -
        exp (3 * (θ * I))) * I) θ := by
    intro θ
    have h := (hasDerivAt_reidKernel z ((p : ℂ) - 1) ((θ : ℂ) * I)).comp (θ : ℂ)
      ((hasDerivAt_id (θ : ℂ)).mul_const I)
    simpa using h.comp_ofReal
  have hcont : Continuous fun θ : ℝ => reidKernel z ((p : ℂ) - 1) (θ * I) *
      (-((p : ℂ) - 1) + z * exp (θ * I) - exp (3 * (θ * I))) * I := by
    unfold reidKernel; fun_prop
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := 2 * π)
    (fun θ _ => hF θ) (hcont.intervalIntegrable _ _)
  have hper : reidKernel z ((p : ℂ) - 1) (((2 * π : ℝ) : ℂ) * I) =
      reidKernel z ((p : ℂ) - 1) (((0 : ℝ) : ℂ) * I) := by
    have h := reidKernel_add_mul_I (c := 2 * π) (by
      rw [show 3 * (((2 * π : ℝ) : ℂ) * I) = ((3 : ℤ) : ℂ) * (2 * π * I) by push_cast; ring,
        exp_int_mul_two_pi_mul_I]) z ((p : ℂ) - 1) 0
    have h1 : exp (((2 * π : ℝ) : ℂ) * I) = 1 := by push_cast; exact exp_two_pi_mul_I
    have h2 : exp (-((p : ℂ) - 1) * (((2 * π : ℝ) : ℂ) * I)) = 1 := by
      rw [show -((p : ℂ) - 1) * (((2 * π : ℝ) : ℂ) * I) = ((1 - p : ℤ) : ℂ) * (2 * π * I) by
        push_cast; ring, exp_int_mul_two_pi_mul_I]
    rw [zero_add, h1, h2, one_mul, mul_one] at h
    simpa using h
  rw [hper, sub_self] at hFTC
  have key : ∫ θ : ℝ in (0 : ℝ)..2 * π, (I * exp (θ * I) * reidKernel z ((p : ℂ) - 3) (θ * I) -
        z * (I * exp (θ * I) * reidKernel z ((p : ℂ) - 1) (θ * I)) +
        ((p : ℂ) - 1) * (I * exp (θ * I) * reidKernel z p (θ * I))) = 0 := by
    rw [intervalIntegral.integral_congr (g := fun θ : ℝ => -(reidKernel z ((p : ℂ) - 1) (θ * I) *
      (-((p : ℂ) - 1) + z * exp (θ * I) - exp (3 * (θ * I))) * I))
      (fun θ _ => reidArc_integrand_identity z p θ), intervalIntegral.integral_neg, hFTC, neg_zero]
  have i1 : IntervalIntegrable (fun θ : ℝ => I * exp (θ * I) * reidKernel z ((p : ℂ) - 3) (θ * I))
      volume 0 (2 * π) := (hc _ _).intervalIntegrable _ _
  have i2 : IntervalIntegrable
      (fun θ : ℝ => z * (I * exp (θ * I) * reidKernel z ((p : ℂ) - 1) (θ * I)))
      volume 0 (2 * π) := ((hc _ _).const_mul _).intervalIntegrable _ _
  have i3 : IntervalIntegrable
      (fun θ : ℝ => ((p : ℂ) - 1) * (I * exp (θ * I) * reidKernel z p (θ * I)))
      volume 0 (2 * π) := ((hc _ _).const_mul _).intervalIntegrable _ _
  rw [intervalIntegral.integral_add (i1.sub i2) i3, intervalIntegral.integral_sub i1 i2,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at key
  simp only [reidAiryB0, reidArc]
  push_cast
  linear_combination key / (2 * π * I)

/-- The closed-contour function `B₀(z, p)` solves `w''' - z w' + (p - 1) w = 0`
(DLMF 9.13.31). -/
@[dlmf 9.13.E31]
theorem reidAiryB0_ode (z : ℂ) (p : ℤ) :
    iteratedDeriv 3 (fun t => reidAiryB0 t p) z - z * deriv (fun t => reidAiryB0 t p) z + ((p : ℂ) - 1) * reidAiryB0 z p = 0 := by
  have h3 : iteratedDeriv 3 (fun t => reidAiryB0 t p) = fun t => reidAiryB0 t (p - 3) := by
    rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one, deriv_reidAiryB0,
      deriv_reidAiryB0, deriv_reidAiryB0]
    funext t; congr 1; ring
  rw [h3, deriv_reidAiryB0]
  have := reidAiryB0_difference z p
  simpa using this

/-- Rotation relations: `A₁(z, p) = e^{-2(p-1)πi/3} A₀(z e^{2πi/3}, p)` and
`A₂(z, p) = e^{2(p-1)πi/3} A₀(z e^{-2πi/3}, p)` (indices `0, 1, 2` here; DLMF 9.13.33). -/
@[dlmf 9.13.E33]
theorem reidAiryA_rotations (z p : ℂ) :
    reidAiryA 1 z p = exp (-2 * (p - 1) * π * I / 3) * reidAiryA 0 (z * exp (2 * π * I / 3)) p ∧
      reidAiryA 2 z p = exp (2 * (p - 1) * π * I / 3) * reidAiryA 0 (z * exp (-2 * π * I / 3)) p := by
  have e1 : exp ((((2 * π / 3 : ℝ) : ℂ)) * I) = exp (2 * π * I / 3) := by push_cast; ring_nf
  have e2 : exp ((((-(2 * π / 3) : ℝ) : ℂ)) * I) = exp (-2 * π * I / 3) := by push_cast; ring_nf
  have k1 : exp ((((2 * π / 3 : ℝ) : ℂ)) * I) * exp (-p * ((((2 * π / 3 : ℝ) : ℂ)) * I)) =
      exp (-2 * (p - 1) * π * I / 3) := by
    rw [← exp_add]; push_cast; ring_nf
  have k2 : exp ((((-(2 * π / 3) : ℝ) : ℂ)) * I) * exp (-p * ((((-(2 * π / 3) : ℝ) : ℂ)) * I)) =
      exp (2 * (p - 1) * π * I / 3) := by
    rw [← exp_add]; push_cast; ring_nf
  constructor
  · have h := reidContour_add exp_three_two_pi_div_three z p (4 * π / 3) (2 * π / 3)
    rw [show 4 * π / 3 + 2 * π / 3 = 2 * π by ring,
      show 2 * π / 3 + 2 * π / 3 = 4 * π / 3 by ring, k1, e1] at h
    simp only [reidAiryA, Fin.val_one, Fin.val_zero, h]
    ring
  · have h := reidContour_add exp_three_neg_two_pi_div_three z p (4 * π / 3) (2 * π / 3)
    rw [show 4 * π / 3 + -(2 * π / 3) = 2 * π / 3 by ring,
      show 2 * π / 3 + -(2 * π / 3) = 0 by ring, k2, e2] at h
    simp only [reidAiryA, Fin.val_two, Fin.val_zero, h]
    ring

/-- At `p = 0`, `A₁(z, 0) = e^{2πi/3} Ai(z e^{2πi/3})` and
`A₂(z, 0) = e^{-2πi/3} Ai(z e^{-2πi/3})` (indices `0, 1, 2` here; DLMF 9.13.29). -/
@[dlmf 9.13.E29]
theorem reidAiryA_zero_rotations (z : ℂ) :
    reidAiryA 1 z 0 = exp (2 * π * I / 3) * airyAi (z * exp (2 * π * I / 3)) ∧
      reidAiryA 2 z 0 = exp (-2 * π * I / 3) * airyAi (z * exp (-2 * π * I / 3)) := by
  obtain ⟨h1, h2⟩ := reidAiryA_rotations z 0
  have hA : ∀ w, reidAiryA 0 w 0 = airyAi w := reidAiryA_zero_parameter
  rw [h1, h2, hA, hA]
  constructor <;> congr 2 <;> ring

/-- The three contour functions and the closed-contour one sum to zero:
`A₀ + A₁ + A₂ + B₀ = 0` (DLMF 9.13.34). -/
@[dlmf 9.13.E34]
theorem reidAiry_connection_sum (z : ℂ) (p : ℤ) :
    reidAiryA 0 z p + reidAiryA 1 z p + reidAiryA 2 z p + reidAiryB0 z p = 0 := by
  simp only [reidAiryA, reidAiryB0, reidContour, Fin.val_zero, Fin.val_one, Fin.val_two,
    reidRay_two_pi]
  have h1 := reidArc_add_adjacent z p (2 * π) (4 * π / 3) (2 * π / 3)
  have h2 := reidArc_add_adjacent z p (2 * π) (2 * π / 3) 0
  have h3 := reidArc_add_adjacent z p (2 * π) 0 (2 * π)
  rw [reidArc_self] at h3
  rw [← add_div, ← add_div, ← add_div, div_eq_zero_iff]
  left
  linear_combination h1 + h2 + h3

/-- Summing a function supported on multiples of three over `range (n + 1)`. -/
theorem sum_range_ite_three_dvd {M : Type*} [AddCommMonoid M] (h : ℕ → M) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (if 3 ∣ k then h k else 0) =
      ∑ i ∈ Finset.range (n / 3 + 1), h (3 * i) := by
  rw [← Finset.sum_filter]
  have : (Finset.range (n + 1)).filter (fun k => 3 ∣ k) =
      (Finset.range (n / 3 + 1)).map ⟨fun i => 3 * i, mul_right_injective₀ three_ne_zero⟩ := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_map, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨hk, i, rfl⟩
      exact ⟨i, by omega, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨by omega, dvd_mul_right 3 i⟩
  rw [this, Finset.sum_map]
  rfl

/-- The Taylor expansion `e^{zu-u³/3} = ∑ c_j u^j` with the Reid coefficients, with
absolute convergence. -/
theorem hasSum_reidTaylorCoeff' (z u : ℂ) :
    Summable (fun j : ℕ => ‖reidTaylorCoeff z j * u ^ j‖) ∧
      HasSum (fun j : ℕ => reidTaylorCoeff z j * u ^ j) (exp (z * u - u ^ 3 / 3)) := by
  set f : ℕ → ℂ := fun a => (z * u) ^ a / a.factorial
  set g : ℕ → ℂ := fun m => if 3 ∣ m then (-(u ^ 3 / 3)) ^ (m / 3) / (m / 3).factorial else 0
  have hinj : Function.Injective (fun k : ℕ => 3 * k) := mul_right_injective₀ three_ne_zero
  have hg0 : ∀ m ∉ Set.range (fun k : ℕ => 3 * k), g m = 0 := by
    intro m hm
    simp only [g]
    split_ifs with h
    · obtain ⟨k, rfl⟩ := h; exact absurd ⟨k, rfl⟩ hm
    · rfl
  have hgcomp : g ∘ (fun k : ℕ => 3 * k) = fun k => (-(u ^ 3 / 3)) ^ k / k.factorial := by
    funext k; simp [g]
  have hfs : HasSum f (exp (z * u)) := by
    simpa [f, Complex.exp_eq_exp_ℂ] using NormedSpace.expSeries_div_hasSum_exp (z * u)
  have hgs : HasSum g (exp (-(u ^ 3 / 3))) := by
    rw [← hinj.hasSum_iff hg0, hgcomp]
    simpa [Complex.exp_eq_exp_ℂ] using NormedSpace.expSeries_div_hasSum_exp (-(u ^ 3 / 3))
  have hfn : Summable fun a => ‖f a‖ := by
    simpa [f, norm_div, norm_pow] using Real.summable_pow_div_factorial ‖z * u‖
  have hgn : Summable fun m => ‖g m‖ := by
    have h0 : ∀ m ∉ Set.range (fun k : ℕ => 3 * k), ‖g m‖ = 0 := fun m hm => by simp [hg0 m hm]
    rw [← hinj.summable_iff h0]
    have : (fun m => ‖g m‖) ∘ (fun k : ℕ => 3 * k) = fun k => ‖-(u ^ 3 / 3)‖ ^ k / k.factorial := by
      funext k; simp [g, norm_pow]
    rw [this]
    exact Real.summable_pow_div_factorial _
  have hprod := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hgn hfn
  have hsumn := summable_norm_sum_mul_antidiagonal_of_summable_norm hgn hfn
  have hsum := hsumn.of_norm
  rw [hgs.tsum_eq, hfs.tsum_eq] at hprod
  have hval : (fun n => ∑ kl ∈ Finset.antidiagonal n, g kl.1 * f kl.2) =
      fun n => reidTaylorCoeff z n * u ^ n := by
    funext n
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => g i * f j)]
    simp only [g, ite_mul, zero_mul]
    rw [sum_range_ite_three_dvd (fun k => (-(u ^ 3 / 3)) ^ (k / 3) / ((k / 3).factorial : ℂ) *
      f (n - k)) n, reidTaylorCoeff, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : 3 * i ≤ n := by
      have := Finset.mem_range.mp hi
      omega
    simp only [f, Nat.mul_div_cancel_left i (by norm_num : 0 < 3)]
    have hu : u ^ n = (u ^ 3) ^ i * u ^ (n - 3 * i) := by
      rw [← pow_mul, ← pow_add]; congr 1; omega
    rw [hu, mul_pow, neg_pow, div_pow, div_pow]
    field_simp
  refine ⟨?_, ?_⟩
  · exact hsumn.congr fun n => by rw [show (∑ kl ∈ Finset.antidiagonal n, g kl.1 * f kl.2) =
      reidTaylorCoeff z n * u ^ n from congrFun hval n]
  rw [← hval, show z * u - u ^ 3 / 3 = -(u ^ 3 / 3) + z * u by ring, exp_add, hprod]
  exact hsum.hasSum

/-- The Taylor expansion `e^{zu-u³/3} = ∑ c_j u^j` with the Reid coefficients. -/
theorem hasSum_reidTaylorCoeff (z u : ℂ) :
    HasSum (fun j : ℕ => reidTaylorCoeff z j * u ^ j) (exp (z * u - u ^ 3 / 3)) :=
  (hasSum_reidTaylorCoeff' z u).2

/-- The Taylor remainder `(e^{zu-u³/3} - ∑_{j<n} c_j u^j) / u^n`, as an entire power series. -/
def reidTaylorTail (z : ℂ) (n : ℕ) (u : ℂ) : ℂ := ∑' j : ℕ, reidTaylorCoeff z (j + n) * u ^ j

/-- The Taylor remainder series has infinite radius. -/
theorem hasFPowerSeriesOnBall_reidTaylorTail (z : ℂ) (n : ℕ) :
    HasFPowerSeriesOnBall (reidTaylorTail z n)
      (FormalMultilinearSeries.ofScalars ℂ fun j => reidTaylorCoeff z (j + n)) 0 ⊤ := by
  have hr : (FormalMultilinearSeries.ofScalars ℂ fun j => reidTaylorCoeff z (j + n)).radius = ⊤ := by
    refine ENNReal.eq_top_of_forall_nnreal_le fun r => ?_
    rcases eq_or_ne r 0 with rfl | hr0
    · simp
    refine FormalMultilinearSeries.le_radius_of_summable _ ?_
    have hs := ((hasSum_reidTaylorCoeff' z (r : ℂ)).1).comp_injective (add_left_injective n)
    have hrpos : (0 : ℝ) < r := by positivity
    have := hs.mul_left ((r : ℝ) ^ n)⁻¹
    refine this.congr fun j => ?_
    simp only [Function.comp_apply, norm_mul, norm_pow, Complex.norm_real,
      FormalMultilinearSeries.ofScalars_norm, Real.norm_eq_abs,
      abs_of_nonneg hrpos.le, pow_add]
    field_simp
  have h := (FormalMultilinearSeries.ofScalars ℂ fun j => reidTaylorCoeff z (j + n)).hasFPowerSeriesOnBall
    (by rw [hr]; simp)
  rw [hr] at h
  have he : (FormalMultilinearSeries.ofScalars ℂ fun j => reidTaylorCoeff z (j + n)).sum =
      reidTaylorTail z n := by
    funext u
    simp only [reidTaylorTail, FormalMultilinearSeries.sum,
      FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]
  rwa [he] at h

/-- The Taylor remainder is entire. -/
theorem differentiable_reidTaylorTail (z : ℂ) (n : ℕ) : Differentiable ℂ (reidTaylorTail z n) :=
  fun u => ((hasFPowerSeriesOnBall_reidTaylorTail z n).analyticAt_of_mem (by simp)).differentiableAt

/-- `u^n · tail(u) = e^{zu-u³/3} - ∑_{j<n} c_j u^j`. -/
theorem pow_mul_reidTaylorTail (z : ℂ) (n : ℕ) (u : ℂ) :
    u ^ n * reidTaylorTail z n u =
      exp (z * u - u ^ 3 / 3) - ∑ j ∈ Finset.range n, reidTaylorCoeff z j * u ^ j := by
  have hs := (hasSum_reidTaylorCoeff z u)
  have h := hs.summable.sum_add_tsum_nat_add n
  rw [hs.tsum_eq] at h
  rw [← h, add_sub_cancel_left, reidTaylorTail, ← tsum_mul_left]
  congr 1; funext j; ring

/-- The finite-part segment integral of `B_k` is a difference of primitive values of the
Taylor remainder. -/
theorem reidFinitePart_segment (z : ℂ) {n : ℕ} {G : ℂ → ℂ}
    (hG : ∀ u, HasDerivAt G (reidTaylorTail z n u) u) (θ : ℝ) :
    ∫ t : ℝ in (0 : ℝ)..1, exp (θ * I) * ((t : ℂ) * exp (θ * I)) ^ (-(n : ℂ)) *
        (exp (z * ((t : ℂ) * exp (θ * I)) - ((t : ℂ) * exp (θ * I)) ^ 3 / 3) -
          ∑ j ∈ Finset.range n, reidTaylorCoeff z j * ((t : ℂ) * exp (θ * I)) ^ j) =
      G (exp (θ * I)) - G 0 := by
  have hd : ∀ t : ℝ, HasDerivAt (fun t : ℝ => G (t * exp (θ * I)))
      (reidTaylorTail z n (t * exp (θ * I)) * exp (θ * I)) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) * exp (θ * I)) (1 * exp (θ * I)) t :=
      ((hasDerivAt_id t).ofReal_comp).mul_const _
    exact ((hG _).comp t h1).congr_deriv (by ring)
  have hcont : Continuous fun t : ℝ => reidTaylorTail z n (t * exp (θ * I)) * exp (θ * I) :=
    ((differentiable_reidTaylorTail z n).continuous.comp (by fun_prop)).mul continuous_const
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
    (hcont.intervalIntegrable 0 1)
  simp only [ofReal_one, one_mul, ofReal_zero, zero_mul] at hFTC
  rw [← hFTC]
  refine intervalIntegral.integral_congr_ae (ae_of_all _ fun t ht => ?_)
  rw [uIoc_of_le zero_le_one] at ht
  have hu : (t : ℂ) * exp (θ * I) ≠ 0 :=
    mul_ne_zero (ofReal_ne_zero.mpr ht.1.ne') (exp_ne_zero _)
  rw [← pow_mul_reidTaylorTail, cpow_neg, cpow_natCast, mul_assoc,
    inv_mul_cancel_left₀ (pow_ne_zero n hu), mul_comm]

/-- The antiderivative along the unit circle of the Reid integrand with `p = m + 1`. -/
def reidFinitePartH (z : ℂ) (m : ℕ) (G : ℂ → ℂ) (θ : ℝ) : ℂ :=
  (∑ j ∈ Finset.range m, reidTaylorCoeff z j * exp (θ * I * ((j : ℂ) + 1 - ((m + 1 : ℕ) : ℂ))) /
      ((j : ℂ) + 1 - ((m + 1 : ℕ) : ℂ))) +
    θ * I * reidTaylorCoeff z m + G (exp (θ * I))

/-- Arc integrals of the Reid integrand with `p = m + 1` are differences of `reidFinitePartH`. -/
theorem reidArc_finitePart (z : ℂ) (m : ℕ) {G : ℂ → ℂ}
    (hG : ∀ u, HasDerivAt G (reidTaylorTail z (m + 1) u) u) (α β : ℝ) :
    reidArc z ((m + 1 : ℕ) : ℂ) α β = reidFinitePartH z m G β - reidFinitePartH z m G α := by
  have hw : ∀ j ∈ Finset.range m, ((j : ℂ) + 1 - ((m + 1 : ℕ) : ℂ)) ≠ 0 := by
    intro j hj h
    have hj' := Finset.mem_range.mp hj
    have : ((j + 1 : ℕ) : ℂ) = ((m + 1 : ℕ) : ℂ) := by
      push_cast at h ⊢; linear_combination h
    have := Nat.cast_injective this
    omega
  have hd : ∀ θ : ℝ, HasDerivAt (reidFinitePartH z m G)
      (I * exp (θ * I) * reidKernel z ((m + 1 : ℕ) : ℂ) (θ * I)) θ := by
    intro θ
    have hexp : ∀ w : ℂ, HasDerivAt (fun θ : ℝ => exp (θ * I * w)) (exp (θ * I * w) * (1 * I * w)) θ :=
      fun w => ((((hasDerivAt_id θ).ofReal_comp).mul_const I).mul_const w).cexp
    have h1 : HasDerivAt (fun θ : ℝ => ∑ j ∈ Finset.range m, reidTaylorCoeff z j *
        exp (θ * I * ((j : ℂ) + 1 - ((m + 1 : ℕ) : ℂ))) / ((j : ℂ) + 1 - ((m + 1 : ℕ) : ℂ)))
        (∑ j ∈ Finset.range m, reidTaylorCoeff z j * (exp (θ * I * ((j : ℂ) + 1 - ((m + 1 : ℕ) : ℂ))) *
          (1 * I * ((j : ℂ) + 1 - ((m + 1 : ℕ) : ℂ)))) / ((j : ℂ) + 1 - ((m + 1 : ℕ) : ℂ))) θ :=
      HasDerivAt.fun_sum fun j _ => ((hexp _).const_mul _).div_const _
    have h2 : HasDerivAt (fun θ : ℝ => (θ : ℂ) * I * reidTaylorCoeff z m)
        (1 * I * reidTaylorCoeff z m) θ :=
      (((hasDerivAt_id θ).ofReal_comp).mul_const I).mul_const _
    have h3 : HasDerivAt (fun θ : ℝ => G (exp (θ * I)))
        (reidTaylorTail z (m + 1) (exp (θ * I)) * (exp (θ * I) * (1 * I))) θ :=
      (hG _).comp θ (((hasDerivAt_id θ).ofReal_comp).mul_const I).cexp
    refine ((h1.add h2).add h3).congr_deriv ?_
    set v := exp (θ * I)
    have hK : reidKernel z ((m + 1 : ℕ) : ℂ) (θ * I) =
        exp (-((m + 1 : ℕ) : ℂ) * (θ * I)) * exp (z * v - v ^ 3 / 3) := by
      rw [reidKernel, ← exp_add, show exp (3 * (θ * I)) = v ^ 3 by
        rw [← exp_nat_mul]; push_cast; ring_nf]
      congr 1; ring
    have hT := pow_mul_reidTaylorTail z (m + 1) v
    have hT' : exp (z * v - v ^ 3 / 3) = (∑ j ∈ Finset.range (m + 1), reidTaylorCoeff z j * v ^ j) +
        v ^ (m + 1) * reidTaylorTail z (m + 1) v := by linear_combination -hT
    rw [hK, hT', Finset.sum_range_succ]
    have hvj : ∀ j : ℕ, v * exp (-((m + 1 : ℕ) : ℂ) * (θ * I)) * v ^ j =
        exp (θ * I * ((j : ℂ) + 1 - ((m + 1 : ℕ) : ℂ))) := by
      intro j
      simp only [v]; rw [← exp_nat_mul, ← exp_add, ← exp_add]; congr 1; ring
    have hvm : v * exp (-((m + 1 : ℕ) : ℂ) * (θ * I)) * v ^ (m + 1) = v := by
      rw [hvj]; simp only [v]; congr 1; push_cast; ring
    have hvm' : v * exp (-((m + 1 : ℕ) : ℂ) * (θ * I)) * v ^ m = 1 := by
      rw [hvj]; push_cast; ring_nf; exact exp_zero
    have key : ∀ j ∈ Finset.range m, reidTaylorCoeff z j *
        (exp (θ * I * ((j : ℂ) + 1 - ((m + 1 : ℕ) : ℂ))) * (1 * I * ((j : ℂ) + 1 - ((m + 1 : ℕ) : ℂ)))) /
          ((j : ℂ) + 1 - ((m + 1 : ℕ) : ℂ)) =
        I * (v * exp (-((m + 1 : ℕ) : ℂ) * (θ * I)) * (reidTaylorCoeff z j * v ^ j)) := by
      intro j hj
      calc _ = I * (reidTaylorCoeff z j * exp (θ * I * ((j : ℂ) + 1 - ((m + 1 : ℕ) : ℂ)))) := by
            field_simp [hw j hj]
            exact mul_div_cancel_right₀ _ (hw j hj)
        _ = _ := by rw [← hvj j]; ring
    rw [Finset.sum_congr rfl key, ← Finset.mul_sum, ← Finset.mul_sum]
    linear_combination -(I * reidTaylorCoeff z m) * hvm' -
      (I * reidTaylorTail z (m + 1) v) * hvm
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ => hd θ)
    ((continuous_reidArc_integrand z _).intervalIntegrable _ _)

/-- For `p = m + 1 ≥ 1`, the finite-part `B_k` in terms of the primitive `G` of the Taylor
remainder. -/
theorem reidAiryB_succ_eq (k : Fin 3) (z : ℂ) (m : ℕ) {G : ℂ → ℂ}
    (hG : ∀ u, HasDerivAt G (reidTaylorTail z (m + 1) u) u) :
    reidAiryB k z ((m + 1 : ℕ) : ℤ) = reidRay z ((m + 1 : ℕ) : ℂ) (2 * k.val * π / 3) 1 +
      reidFinitePartH z m G (2 * k.val * π / 3) - G 0 := by
  have hp : ¬ (((m + 1 : ℕ) : ℤ) ≤ 0) := by omega
  have hn : (((m + 1 : ℕ) : ℤ)).toNat = m + 1 := by simp
  simp only [reidAiryB, hp, ↓reduceIte, hn, Int.cast_natCast]
  rw [reidFinitePart_segment z hG, reidFinitePartH, show m + 1 - 1 = m by omega]
  ring

/-- `B_j - B_k` is the Reid contour from angle `θ_k` to `θ_j`, for every integer `p`. -/
theorem reidAiryB_sub_eq_reidContour (j k : Fin 3) (z : ℂ) (p : ℤ) :
    reidAiryB j z p - reidAiryB k z p =
      reidContour z p (2 * k.val * π / 3) (2 * j.val * π / 3) := by
  have hj : exp (3 * (((2 * j.val * π / 3 : ℝ) : ℂ) * I)) = 1 := exp_three_reidAiryB_angle j
  have hk : exp (3 * (((2 * k.val * π / 3 : ℝ) : ℂ) * I)) = 1 := exp_three_reidAiryB_angle k
  rcases le_or_gt p 0 with hp | hp
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, p = -(n : ℤ) := ⟨(-p).toNat, by omega⟩
    subst hn
    rw [reidAiryB_ordinary_ray j z hp, reidAiryB_ordinary_ray k z hp]
    push_cast
    rw [reidContour_neg_nat_eq hk hj]
    ring
  · obtain ⟨m, hm⟩ : ∃ m : ℕ, p = ((m + 1 : ℕ) : ℤ) := ⟨p.toNat - 1, by omega⟩
    subst hm
    obtain ⟨G, hG⟩ := (differentiable_reidTaylorTail z (m + 1)).isExactOn_univ
    have hG' : ∀ u, HasDerivAt G (reidTaylorTail z (m + 1) u) u := fun u => hG u (mem_univ u)
    rw [reidAiryB_succ_eq j z m hG', reidAiryB_succ_eq k z m hG', reidContour]
    simp only [Int.cast_natCast]
    rw [reidArc_finitePart z m hG' _ _]
    ring

/-- The correct form of 9.13.36 for the finite-part `B_k`: the branch of the logarithm on the
ray `θ = 0` contributes the closed-contour term `B₀`. -/
theorem reidAiryB_two_sub_zero (z : ℂ) (p : ℤ) :
    reidAiryB 2 z p - reidAiryB 0 z p =
      2 * π * I * reidAiryA 1 z p + 2 * π * I * reidAiryB0 z p := by
  rw [reidAiryB_sub_eq_reidContour]
  simp only [reidAiryA, reidAiryB0, Fin.val_zero, Fin.val_one, Fin.val_two]
  have hpi : (2 * π * I : ℂ) ≠ 0 := by
    have := Real.pi_pos; simp [Real.pi_ne_zero, I_ne_zero]
  rw [mul_div_cancel₀ _ hpi, mul_div_cancel₀ _ hpi]
  have h := reidArc_add_adjacent z p 0 (2 * π) (4 * π / 3)
  simp only [reidContour, Nat.cast_zero, mul_zero, zero_mul, zero_div, Nat.cast_ofNat]
  rw [reidRay_two_pi, show 2 * (2 : ℝ) * π / 3 = 4 * π / 3 by ring, ← h]
  ring

/-- The closed Reid contour with `p = 1` gives `B₀(z,1) = 1`. -/
lemma reidAiryB0_one (z : ℂ) : reidAiryB0 z 1 = 1 := by
  obtain ⟨G, hG⟩ := (differentiable_reidTaylorTail z (0 + 1)).isExactOn_univ
  have hG' : ∀ u, HasDerivAt G (reidTaylorTail z (0 + 1) u) u := fun u => hG u (mem_univ u)
  have h := reidArc_finitePart z 0 hG' 0 (2 * π)
  have hc0 : reidTaylorCoeff z 0 = 1 := by simp [reidTaylorCoeff]
  simp only [reidFinitePartH, Finset.range_zero, Finset.sum_empty, zero_add, hc0, mul_one,
    ofReal_zero, zero_mul, exp_zero] at h
  rw [show exp (((2 * π : ℝ) : ℂ) * I) = 1 by push_cast; exact exp_two_pi_mul_I] at h
  have hpi : (2 * π * I : ℂ) ≠ 0 := by
    have := Real.pi_pos; simp [Real.pi_ne_zero, I_ne_zero]
  rw [reidAiryB0, show ((1 : ℤ) : ℂ) = ((0 + 1 : ℕ) : ℂ) by norm_num, h]
  push_cast
  field_simp
  ring

/-- Evidence that the printed DLMF 9.13.36 fails for the finite-part `B_k` at `p = 1`. -/
theorem reidAiry_connection_36_ne_one (z : ℂ) :
    reidAiryB 2 z 1 - reidAiryB 0 z 1 ≠ 2 * π * I * reidAiryA 1 z 1 := by
  rw [reidAiryB_two_sub_zero, reidAiryB0_one]
  intro h
  have hpi : (2 * π * I : ℂ) ≠ 0 := by
    have := Real.pi_pos; simp [Real.pi_ne_zero, I_ne_zero]
  push_cast at h
  exact hpi (by linear_combination h)

/-- `B₁(z, p) - B₂(z, p) = 2πi A₀(z, p)` with indices `0, 1, 2` as here (DLMF's
`B₂ - B₃ = 2πi A₁`, 9.13.35). -/
@[dlmf 9.13.E35]
theorem reidAiry_connection_35 (z : ℂ) (p : ℤ) :
    reidAiryB 1 z p - reidAiryB 2 z p = 2 * π * I * reidAiryA 0 z p := by
  rw [reidAiryB_sub_eq_reidContour]
  simp only [reidAiryA, Fin.val_zero, Fin.val_one, Fin.val_two]
  have hpi : (2 * π * I : ℂ) ≠ 0 := by
    have := Real.pi_pos; simp [Real.pi_ne_zero, I_ne_zero]
  rw [mul_div_cancel₀ _ hpi]
  congr 1 <;> push_cast <;> ring

/-- `B₀(z, p) - B₁(z, p) = 2πi A₂(z, p)` with indices `0, 1, 2` as here (DLMF's
`B₁ - B₂ = 2πi A₃`, 9.13.37). -/
@[dlmf 9.13.E37]
theorem reidAiry_connection_37 (z : ℂ) (p : ℤ) :
    reidAiryB 0 z p - reidAiryB 1 z p = 2 * π * I * reidAiryA 2 z p := by
  rw [reidAiryB_sub_eq_reidContour]
  simp only [reidAiryA, Fin.val_zero, Fin.val_one, Fin.val_two]
  have hpi : (2 * π * I : ℂ) ≠ 0 := by
    have := Real.pi_pos; simp [Real.pi_ne_zero, I_ne_zero]
  rw [mul_div_cancel₀ _ hpi]
  congr 1 <;> push_cast <;> ring

/-- `B₀(z,p) = 0` for `p ≤ 0`: the integrand `t^{-p} e^{zt-t³/3}` is entire. Extends the
`p = 0` case of DLMF 9.13.30. -/
lemma reidAiryB0_of_nonpos (z : ℂ) {p : ℤ} (hp : p ≤ 0) : reidAiryB0 z p = 0 := by
  obtain ⟨n, rfl⟩ := Int.exists_eq_neg_ofNat hp
  have hd : Differentiable ℂ (fun t : ℂ => t ^ n * exp (z * t - t ^ 3 / 3)) := by fun_prop
  have h := (hd.diffContOnCl (s := Metric.ball (0 : ℂ) 1)).circleIntegral_eq_zero zero_le_one
  simp only [circleIntegral, deriv_circleMap, circleMap_zero, ofReal_one, one_mul,
    smul_eq_mul] at h
  simp only [reidAiryB0, reidArc]
  rw [div_eq_zero_iff]; left
  rw [← h]
  refine intervalIntegral.integral_congr fun θ _ => ?_
  simp only [reidKernel]
  rw [← exp_nat_mul, ← exp_nat_mul, ← exp_add]
  push_cast; ring_nf

/-- The corrected connection formula `B₂ - B₀ = 2πi (A₁ + B₀(z, p))` (indices `0, 1, 2` as
here; DLMF 9.13.36, corrected).

DLMF prints `B₃ - B₁ = 2πi A₂` for all integer `p`. That is false for `p ≥ 1` whenever
`B₀(z,p) ≠ 0`, whatever regularization of the divergent ray integrals 9.13.27 is used:
adding 9.13.35–9.13.37 and using 9.13.34 gives `0 = -2πi B₀(z,p)`, and `B₀(z,1) = 1`
(see `reidAiry_connection_36_ne_one`). With the project's finite-part `B_k`, 9.13.35 and
9.13.37 hold for all `p`, and the third relation carries the residue term `2πi B₀(z,p)`.
It reduces to the printed form for `p ≤ 0` (`reidAiry_connection_36_of_nonpos`).
DLMF's `B₁, B₂, B₃, A₁, A₂, A₃` are `reidAiryB 0, 1, 2` and `reidAiryA 0, 1, 2` here. -/
@[dlmf 9.13.E36]
theorem reidAiry_connection_36 (z : ℂ) (p : ℤ) :
    reidAiryB 2 z p - reidAiryB 0 z p = 2 * π * I * (reidAiryA 1 z p + reidAiryB0 z p) := by
  linear_combination (-1 : ℂ) * reidAiry_connection_35 z p - reidAiry_connection_37 z p -
    2 * π * I * reidAiry_connection_sum z p

/-- DLMF 9.13.36 as printed, in its range of validity `p ≤ 0`, where the ray integrals
9.13.27 converge as ordinary integrals. -/
theorem reidAiry_connection_36_of_nonpos (z : ℂ) {p : ℤ} (hp : p ≤ 0) :
    reidAiryB 2 z p - reidAiryB 0 z p = 2 * π * I * reidAiryA 1 z p := by
  rw [reidAiry_connection_36, reidAiryB0_of_nonpos z hp, add_zero]

/-- Positive-p finite-part correction: the lower endpoint contributes a polynomial forcing. -/
theorem reidAiryB_finitePart_ode (k : Fin 3) (z : ℂ) {p : ℤ} (hp : 1 ≤ p) :
    iteratedDeriv 3 (fun t => reidAiryB k t p) z - z * deriv (fun t => reidAiryB k t p) z +
      ((p : ℂ) - 1) * reidAiryB k z p = reidTaylorCoeff z (p.toNat - 1) := by
  sorry

end DLMF.Airy
