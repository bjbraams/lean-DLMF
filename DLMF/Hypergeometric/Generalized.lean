/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Hypergeometric.Series
public import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric

/-!
# The generalized hypergeometric differential equation (Temme (5.30), DLMF 16.8.3)

Mathlib's `Complex.regularizedHGFun a b` is the regularized generalized hypergeometric function
`𝐅(a; b; z) = ∑ₙ ∏ (aᵢ)ₙ / (n! ∏ Γ(bⱼ+n)) zⁿ` with multisets of parameters `a`, `b`, together with
its radius of convergence (Temme §5.9, DLMF §16.2). Here we add the differential equation in terms
of the Euler operator `θ = z d/dz`:

`θ ∏ⱼ (θ + bⱼ - 1) w = z ∏ᵢ (θ + aᵢ) w`,

valid on the disc of convergence for all parameters (DLMF 16.8.3; Temme (5.30)).

## Main results

* `hasFPowerSeriesOnBall_eulerTheta`: `θ` acts on power series by `cₙ ↦ n cₙ`.
* `hasSum_thetaPoly`: a polynomial `P(θ)` acts by `cₙ ↦ P(n) cₙ`.
* `regularizedHGFun_ode`: the generalized hypergeometric equation.
-/

@[expose] public section

open Complex FormalMultilinearSeries Polynomial
open scoped Topology ENNReal Nat

noncomputable section

namespace DLMF.Hypergeometric

/-- The Euler operator `θ f = z f'`. -/
@[dlmf 16.8.E2]
def eulerTheta (f : ℂ → ℂ) : ℂ → ℂ := fun z => z * deriv f z

/-- A polynomial in the Euler operator, `P(θ) f = ∑ₖ Pₖ θᵏ f`. -/
def thetaPoly (P : ℂ[X]) (f : ℂ → ℂ) : ℂ → ℂ :=
  fun z => ∑ k ∈ Finset.range (P.natDegree + 1), P.coeff k * (eulerTheta^[k] f) z

/-- Multiplying the coefficients by `n` does not decrease the radius, given the derivative
series. -/
theorem le_radius_ofScalars_nat_mul {d : ℕ → ℂ} {r : ℝ≥0∞}
    (h : r ≤ (ofScalars ℂ (fun n => ((n : ℂ) + 1) * d (n + 1))).radius) :
    r ≤ (ofScalars ℂ (fun n => (n : ℂ) * d n)).radius := by
  refine ENNReal.le_of_forall_nnreal_lt fun r' hr' => ?_
  obtain ⟨C, -, hC⟩ :=
    (ofScalars ℂ (fun n => ((n : ℂ) + 1) * d (n + 1))).norm_mul_pow_le_of_lt_radius
    (hr'.trans_le h)
  refine (ofScalars ℂ (fun n => (n : ℂ) * d n)).le_radius_of_bound (C * r') fun n => ?_
  have hC0 : 0 ≤ C := (by positivity : (0 : ℝ) ≤ _).trans (hC 0)
  rw [ofScalars_norm]
  rcases n with _ | n
  · simp; positivity
  · have h1 := hC n
    rw [ofScalars_norm] at h1
    push_cast
    calc ‖((n : ℂ) + 1) * d (n + 1)‖ * (r' : ℝ) ^ (n + 1)
        = (‖((n : ℂ) + 1) * d (n + 1)‖ * (r' : ℝ) ^ n) * r' := by ring
      _ ≤ C * r' := mul_le_mul_of_nonneg_right h1 r'.coe_nonneg

/-- **The Euler operator on power series**: `θ` multiplies the `n`-th coefficient by `n`. -/
theorem hasFPowerSeriesOnBall_eulerTheta {f : ℂ → ℂ} {c : ℕ → ℂ} {r : ℝ≥0∞}
    (h : HasFPowerSeriesOnBall f (ofScalars ℂ c) 0 r) :
    HasFPowerSeriesOnBall (DLMF.Hypergeometric.eulerTheta f)
      (ofScalars ℂ (fun n => (n : ℂ) * c n)) 0 r where
  r_le := le_radius_ofScalars_nat_mul (by simpa using h.deriv_ofScalars.r_le)
  r_pos := h.r_pos
  hasSum := fun {y} hy => by
    have := h.hasSum_z_mul_deriv (by simpa using hy)
    convert this using 1
    · funext n; simp; ring
    · simp [DLMF.Hypergeometric.eulerTheta]

theorem hasFPowerSeriesOnBall_eulerTheta_iterate {f : ℂ → ℂ} {c : ℕ → ℂ} {r : ℝ≥0∞}
    (h : HasFPowerSeriesOnBall f (ofScalars ℂ c) 0 r) (k : ℕ) :
    HasFPowerSeriesOnBall (DLMF.Hypergeometric.eulerTheta^[k] f)
      (ofScalars ℂ (fun n => (n : ℂ) ^ k * c n)) 0 r := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    have := hasFPowerSeriesOnBall_eulerTheta ih
    simpa [pow_succ, mul_assoc, mul_comm, mul_left_comm] using this

/-- **A polynomial in `θ` on power series**: `P(θ) f = ∑ P(n) cₙ zⁿ` on the ball. -/
theorem hasSum_thetaPoly {f : ℂ → ℂ} {c : ℕ → ℂ} {r : ℝ≥0∞}
    (h : HasFPowerSeriesOnBall f (ofScalars ℂ c) 0 r) (P : ℂ[X]) {z : ℂ}
    (hz : z ∈ Metric.eball (0 : ℂ) r) :
    HasSum (fun n : ℕ => P.eval (n : ℂ) * c n * z ^ n) (thetaPoly P f z) := by
  have hk : ∀ k, HasSum (fun n : ℕ => P.coeff k * ((n : ℂ) ^ k * c n * z ^ n))
      (P.coeff k * (DLMF.Hypergeometric.eulerTheta^[k] f) z) := fun k =>
    ((hasFPowerSeriesOnBall_eulerTheta_iterate h k).hasSum_mul_pow hz).mul_left _
  have hsum := hasSum_sum (s := Finset.range (P.natDegree + 1)) fun k _ => hk k
  refine hsum.congr_fun fun n => ?_
  rw [eval_eq_sum_range, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-- `1/Γ(z) = z/Γ(z+1)` for every `z`, with the totalized `Γ`. -/
theorem recip_Gamma_eq_mul_recip_Gamma_add_one (z : ℂ) : (Gamma z)⁻¹ = z * (Gamma (z + 1))⁻¹ := by
  by_cases hz : z = 0
  · subst hz; simp
  · rw [Complex.Gamma_add_one z hz, mul_inv, ← mul_assoc, mul_inv_cancel₀ hz, one_mul]

/-- The coefficient recurrence behind DLMF 16.8.3, for all parameters. -/
theorem regularizedHGFunCoeff_succ_mul (a b : Multiset ℂ) (n : ℕ) :
    ((n : ℂ) + 1) * (b.map fun j : ℂ => j + n).prod * regularizedHGFunCoeff a b (n + 1) =
      (a.map fun i => (n : ℂ) + i).prod * regularizedHGFunCoeff a b n := by
  unfold regularizedHGFunCoeff
  simp only [div_eq_mul_inv, mul_inv, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hb : ((b.map fun j : ℂ => j + n).prod *
      ((b.map fun j => Gamma (j + ((n + 1 : ℕ) : ℂ))).prod)⁻¹) =
      ((b.map fun j => Gamma (j + n)).prod)⁻¹ := by
    rw [← Multiset.prod_map_inv, ← Multiset.prod_map_inv, ← Multiset.prod_map_mul]
    congr 1
    refine Multiset.map_congr rfl fun j _ => ?_
    rw [recip_Gamma_eq_mul_recip_Gamma_add_one (j + n)]
    push_cast; ring_nf
  have ha : (a.map (ascPochhammer ℂ (n + 1)).eval).prod =
      (a.map (ascPochhammer ℂ n).eval).prod * (a.map fun i => (n : ℂ) + i).prod := by
    rw [← Multiset.prod_map_mul]
    congr 1
    refine Multiset.map_congr rfl fun i _ => ?_
    rw [ascPochhammer_succ_eval]; ring
  have hn : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hf : (n ! : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  rw [ha]
  push_cast at hb ⊢
  calc ((n : ℂ) + 1) * (b.map fun j : ℂ => j + n).prod *
        ((a.map (ascPochhammer ℂ n).eval).prod * (a.map fun i => (n : ℂ) + i).prod *
          ((((n : ℂ) + 1))⁻¹ * (n ! : ℂ)⁻¹ *
            ((b.map fun j => Gamma (j + ((n : ℂ) + 1))).prod)⁻¹))
      = ((n : ℂ) + 1) * ((n : ℂ) + 1)⁻¹ *
          ((b.map fun j : ℂ => j + n).prod * ((b.map fun j => Gamma (j + ((n : ℂ) + 1))).prod)⁻¹) *
          ((a.map (ascPochhammer ℂ n).eval).prod * (a.map fun i => (n : ℂ) + i).prod *
            (n ! : ℂ)⁻¹) := by ring
    _ = _ := by rw [hb, mul_inv_cancel₀ hn]; ring

/-- **The generalized hypergeometric equation** (DLMF 16.8.3, Temme (5.30)): on the disc of
convergence, `θ ∏ⱼ (θ + bⱼ - 1) w = z ∏ᵢ (θ + aᵢ) w` for `w = 𝐅(a; b; z)`, `θ = z d/dz`. -/
@[dlmf 16.8.E3]
theorem regularizedHGFun_ode (a b : Multiset ℂ) (hr : 0 < (regularizedHGFunSeries a b).radius)
    {z : ℂ} (hz : z ∈ Metric.eball (0 : ℂ) (regularizedHGFunSeries a b).radius) :
    thetaPoly (X * (b.map fun j => X + C (j - 1)).prod) (regularizedHGFun a b) z =
      z * thetaPoly (a.map fun i => X + C i).prod (regularizedHGFun a b) z := by
  have h : HasFPowerSeriesOnBall (regularizedHGFun a b)
      (ofScalars ℂ (regularizedHGFunCoeff a b)) 0 (regularizedHGFunSeries a b).radius :=
    (regularizedHGFunSeries a b).hasFPowerSeriesOnBall hr
  set c := regularizedHGFunCoeff a b
  set Pb : ℂ[X] := X * (b.map fun j => X + C (j - 1)).prod
  set Pa : ℂ[X] := (a.map fun i => X + C i).prod
  have hL := hasSum_thetaPoly h Pb hz
  have hR := hasSum_thetaPoly h Pa hz
  have hcoef : ∀ n : ℕ, Pb.eval ((n + 1 : ℕ) : ℂ) * c (n + 1) = Pa.eval (n : ℂ) * c n := by
    intro n
    simp only [Pb, Pa, eval_mul, eval_X, eval_multiset_prod, Multiset.map_map,
      Function.comp_def, eval_add, eval_C]
    have := regularizedHGFunCoeff_succ_mul a b n
    push_cast
    rw [show (b.map fun j => (n : ℂ) + 1 + (j - 1)) = b.map fun j : ℂ => j + n by
      congr 1; funext j; ring]
    exact this
  have hR' : HasSum (fun n : ℕ => Pb.eval ((n + 1 : ℕ) : ℂ) * c (n + 1) * z ^ n)
      (thetaPoly Pa (regularizedHGFun a b) z) := by
    refine hR.congr_fun fun n => ?_
    rw [hcoef]
  have hshift := HasSum.mul_pow_shift (c := fun n : ℕ => Pb.eval (n : ℂ) * c n) hR'
    (by simp [Pb])
  exact hL.unique hshift

/-- DLMF 16.8.3 for `p ≤ q`, where the series is entire. -/
theorem regularizedHGFun_ode_of_card_le {a b : Multiset ℂ} (h : a.card ≤ b.card) (z : ℂ) :
    thetaPoly (X * (b.map fun j => X + C (j - 1)).prod) (regularizedHGFun a b) z =
      z * thetaPoly (a.map fun i => X + C i).prod (regularizedHGFun a b) z := by
  have hr := radius_regularizedHGFunSeries_eq_top h
  exact regularizedHGFun_ode a b (by rw [hr]; simp) (by rw [hr]; simp)

/-- DLMF 16.8.3 for `p = q + 1` on the unit disc. -/
theorem regularizedHGFun_ode_of_card_eq_add_one {a b : Multiset ℂ} (h : a.card = b.card + 1)
    {z : ℂ} (hz : ‖z‖ < 1) :
    thetaPoly (X * (b.map fun j => X + C (j - 1)).prod) (regularizedHGFun a b) z =
      z * thetaPoly (a.map fun i => X + C i).prod (regularizedHGFun a b) z := by
  have hr := radius_regularizedHGFunSeries_ge_one (a := a) (b := b) h
  refine regularizedHGFun_ode a b (lt_of_lt_of_le (by simp) hr) ?_
  refine Metric.mem_eball.mpr (lt_of_lt_of_le ?_ hr)
  rw [edist_zero_right, ← ofReal_norm, ENNReal.ofReal_lt_one]
  exact hz

end DLMF.Hypergeometric
