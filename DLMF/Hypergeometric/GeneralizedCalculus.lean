/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Hypergeometric.Generalized

/-!
# Calculus of the generalized hypergeometric function (Duverney §§3.4–3.6)

For Mathlib's regularized `𝐅(a; b; z) = ∑ ∏(aᵢ)ₙ zⁿ / (n! ∏ Γ(bⱼ+n))`, for all parameters:
* `deriv_regularizedHGFun`: `𝐅'(a; b; z) = (∏ a) 𝐅(a+1; b+1; z)` inside the disc of convergence
  (Duverney Thm 3.11);
* `regularizedHGFun_contiguous`: `θ𝐅(i, a'; b) = i (𝐅(i+1, a'; b) - 𝐅(i, a'; b))`
  (Duverney (3.40));
* `coeff_eq_of_generalized_ode`: a power series solving the generalized hypergeometric equation
  is a multiple of `𝐅` when no `bⱼ` is a nonpositive integer (Duverney Thm 3.8);
* `regularized1F2_one_inhomogeneous_ode`: the exact reciprocal-Gamma forcing
  for `₁F₂(1;b,c;z)`, from Mathlib's regularized coefficients, for every parameter.
-/

@[expose] public section

open Complex Filter FormalMultilinearSeries Polynomial
open scoped Topology Nat

noncomputable section

namespace DLMF.Hypergeometric

/-- Raising every parameter by one. -/
abbrev shiftParams (a : Multiset ℂ) : Multiset ℂ := a.map (· + 1)

/-- `(n+1) c_{n+1}(a;b) = (∏ a) c_n(a+1; b+1)` for the regularized coefficients. -/
theorem regularizedHGFunCoeff_succ_deriv (a b : Multiset ℂ) (n : ℕ) :
    ((n : ℂ) + 1) * regularizedHGFunCoeff a b (n + 1) =
      a.prod * regularizedHGFunCoeff (shiftParams a) (shiftParams b) n := by
  unfold regularizedHGFunCoeff
  have ha : (a.map (ascPochhammer ℂ (n + 1)).eval).prod =
      a.prod * ((shiftParams a).map (ascPochhammer ℂ n).eval).prod := by
    rw [Multiset.map_map]
    conv_rhs => rw [show a.prod = (a.map fun x => x).prod by rw [Multiset.map_id']]
    rw [← Multiset.prod_map_mul]
    congr 1
    refine Multiset.map_congr rfl fun i _ => ?_
    simp [ascPochhammer_succ_left, Polynomial.eval_comp]
  have hb : (b.map (Gamma <| · + ((n + 1 : ℕ) : ℂ))).prod =
      ((shiftParams b).map (Gamma <| · + (n : ℂ))).prod := by
    rw [Multiset.map_map]
    congr 1
    refine Multiset.map_congr rfl fun j _ => ?_
    simp only [Function.comp]; push_cast; ring_nf
  rw [ha, hb, Nat.factorial_succ]
  have hn : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  push_cast
  field_simp

/-- The regularized function as a `tsum` of its coefficients. -/
theorem regularizedHGFun_eq_tsum' (a b : Multiset ℂ) (z : ℂ) :
    regularizedHGFun a b z = ∑' n : ℕ, regularizedHGFunCoeff a b n * z ^ n := by
  simp only [regularizedHGFun, FormalMultilinearSeries.sum, regularizedHGFunSeries,
    ofScalars_apply_eq, smul_eq_mul]

/-- **Derivative of the generalized hypergeometric function** (Duverney Thm 3.11; DLMF 16.3.1):
`𝐅'(a; b; z) = (∏ a) 𝐅(a+1; b+1; z)` inside the disc of convergence, for all parameters. -/
@[dlmf 16.3.E1]
theorem deriv_regularizedHGFun {a b : Multiset ℂ}
    (hr : 0 < (regularizedHGFunSeries a b).radius) {z : ℂ}
    (hz : z ∈ Metric.eball (0 : ℂ) (regularizedHGFunSeries a b).radius) :
    deriv (regularizedHGFun a b) z =
      a.prod * regularizedHGFun (shiftParams a) (shiftParams b) z := by
  have h : HasFPowerSeriesOnBall (regularizedHGFun a b)
      (ofScalars ℂ (regularizedHGFunCoeff a b)) 0 (regularizedHGFunSeries a b).radius :=
    (regularizedHGFunSeries a b).hasFPowerSeriesOnBall hr
  have hd := h.deriv_ofScalars.hasSum_mul_pow hz
  simp_rw [regularizedHGFunCoeff_succ_deriv] at hd
  rw [regularizedHGFun_eq_tsum']
  by_cases h0 : a.prod = 0
  · simp only [h0, zero_mul] at hd ⊢
    exact hd.tsum_eq.symm.trans tsum_zero
  · have hd' := hd.div_const a.prod
    simp_rw [mul_assoc, mul_div_cancel_left₀ _ h0] at hd'
    rw [hd'.tsum_eq]
    field_simp

/-- `n cₙ(i :: a'; b) = i (cₙ(i+1 :: a'; b) - cₙ(i :: a'; b))`. -/
theorem regularizedHGFunCoeff_contiguous (i : ℂ) (a b : Multiset ℂ) (n : ℕ) :
    (n : ℂ) * regularizedHGFunCoeff (i ::ₘ a) b n =
      i * (regularizedHGFunCoeff ((i + 1) ::ₘ a) b n - regularizedHGFunCoeff (i ::ₘ a) b n) := by
  unfold regularizedHGFunCoeff
  simp only [Multiset.map_cons, Multiset.prod_cons]
  have h := ascPochhammer_succ_eval (S := ℂ) n i
  rw [ascPochhammer_succ_left, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_comp,
    Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one] at h
  linear_combination (-(a.map (ascPochhammer ℂ n).eval).prod *
    (↑n ! * (b.map (Gamma <| · + n)).prod)⁻¹) * h

/-- **Contiguous relation of the generalized hypergeometric function** (Duverney (3.40);
DLMF 16.3.4 form): `θ 𝐅(i, a'; b; z) = i (𝐅(i+1, a'; b; z) - 𝐅(i, a'; b; z))` inside both discs of
convergence. -/
theorem regularizedHGFun_contiguous (i : ℂ) (a b : Multiset ℂ) {z : ℂ}
    (hz : z ∈ Metric.eball (0 : ℂ) (regularizedHGFunSeries (i ::ₘ a) b).radius)
    (hz' : z ∈ Metric.eball (0 : ℂ) (regularizedHGFunSeries ((i + 1) ::ₘ a) b).radius) :
    z * deriv (regularizedHGFun (i ::ₘ a) b) z =
      i * (regularizedHGFun ((i + 1) ::ₘ a) b z - regularizedHGFun (i ::ₘ a) b z) := by
  have hr : 0 < (regularizedHGFunSeries (i ::ₘ a) b).radius := by
    rw [Metric.mem_eball] at hz; exact lt_of_le_of_lt zero_le hz
  have hr' : 0 < (regularizedHGFunSeries ((i + 1) ::ₘ a) b).radius := by
    rw [Metric.mem_eball] at hz'; exact lt_of_le_of_lt zero_le hz'
  have h : HasFPowerSeriesOnBall (regularizedHGFun (i ::ₘ a) b)
      (ofScalars ℂ (regularizedHGFunCoeff (i ::ₘ a) b)) 0
        (regularizedHGFunSeries (i ::ₘ a) b).radius :=
    (regularizedHGFunSeries (i ::ₘ a) b).hasFPowerSeriesOnBall hr
  have h' : HasFPowerSeriesOnBall (regularizedHGFun ((i + 1) ::ₘ a) b)
      (ofScalars ℂ (regularizedHGFunCoeff ((i + 1) ::ₘ a) b)) 0
        (regularizedHGFunSeries ((i + 1) ::ₘ a) b).radius :=
    (regularizedHGFunSeries ((i + 1) ::ₘ a) b).hasFPowerSeriesOnBall hr'
  have hd := (h.deriv_ofScalars.hasSum_mul_pow hz).mul_left z
  have hs := h.hasSum_mul_pow hz
  have hs' := h'.hasSum_mul_pow hz'
  have hrhs := (hs'.sub hs).mul_left i
  -- shift the derivative series by one
  have hshift : HasSum (fun n : ℕ => (n : ℂ) * regularizedHGFunCoeff (i ::ₘ a) b n * z ^ n)
      (z * deriv (regularizedHGFun (i ::ₘ a) b) z) := by
    rw [← hasSum_nat_add_iff' 1]
    simp only [Finset.sum_range_one, Nat.cast_zero, zero_mul, sub_zero]
    refine hd.congr_fun fun n => ?_
    push_cast; ring
  refine hshift.unique (hrhs.congr_fun fun n => ?_)
  rw [regularizedHGFunCoeff_contiguous]
  ring

/-- The convergent regularized 1F2 series for arbitrary upper and lower parameters. -/
theorem hasSum_regularized1F2 (a b c z : ℂ) :
    HasSum (fun n : ℕ=>regularizedHGFunCoeff {a} {b,c} n*z^n)
      (regularizedHGFun {a} {b,c} z) := by
  have hr : (regularizedHGFunSeries {a} {b,c}).radius=⊤ :=
    radius_regularizedHGFunSeries_eq_top (by simp)
  have hp : HasFPowerSeriesOnBall (regularizedHGFun {a} {b,c})
      (regularizedHGFunSeries {a} {b,c}) 0 ⊤ := by
    rw [← hr]
    exact (regularizedHGFunSeries {a} {b,c}).hasFPowerSeriesOnBall (by rw [hr]; simp)
  exact hp.hasSum_mul_pow (by simp)

/-- The regularized `₁F₂(1;b,c;·)` series is entire, even when a lower parameter is a pole. -/
theorem hasFPowerSeriesOnBall_regularized1F2_one (b c : ℂ) :
    HasFPowerSeriesOnBall (regularizedHGFun {1} {b,c})
      (ofScalars ℂ (regularizedHGFunCoeff {1} {b,c})) 0 ⊤ := by
  have hr : (regularizedHGFunSeries {1} {b,c}).radius = ⊤ :=
    radius_regularizedHGFunSeries_eq_top (by simp)
  change HasFPowerSeriesOnBall (regularizedHGFunSeries {1} {b,c}).sum
    (regularizedHGFunSeries {1} {b,c}) 0 ⊤
  simpa only [hr] using (regularizedHGFunSeries {1} {b,c}).hasFPowerSeriesOnBall
    (by rw [hr]; simp)

/-- Cancelling the upper parameter one gives the quadratic coefficient recurrence for `₁F₂`.
No lower-parameter Gamma factor is cancelled. -/
lemma regularized1F2_one_coeff_recurrence (b c : ℂ) (n : ℕ) :
    (b+n)*(c+n)*regularizedHGFunCoeff {1} {b,c} (n+1) =
      regularizedHGFunCoeff {1} {b,c} n := by
  have h := regularizedHGFunCoeff_succ_mul {1} {b,c} n
  simp only [Multiset.map_singleton, Multiset.prod_singleton, Multiset.insert_eq_cons,
    Multiset.map_cons, Multiset.prod_cons] at h
  have hn : (n:ℂ)+1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  apply mul_left_cancel₀ hn
  linear_combination h

/-- Cancelling the upper parameter one against the factorial in the regularized coefficient. -/
theorem regularized1F2_one_coeff (b c : ℂ) (n : ℕ) :
    regularizedHGFunCoeff {1} {b,c} n=1/(Gamma (b+n)*Gamma (c+n)) := by
  simp only [regularizedHGFunCoeff, Multiset.map_singleton, Multiset.prod_singleton,
    Multiset.insert_eq_cons, Multiset.map_cons, Multiset.prod_cons]
  rw [show (ascPochhammer ℂ n).eval 1=(n.factorial:ℂ) by simp,
    div_mul_eq_div_div, div_self (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))]

/-- Lower-parameter contiguity of regularized `₁F₂`, including reciprocal-Gamma zeros. -/
theorem regularized1F2_one_lower (b c z : ℂ) :
    z*deriv (regularizedHGFun {1} {b,c}) z+(c-1)*regularizedHGFun {1} {b,c} z =
      regularizedHGFun {1} {b,c-1} z := by
  have h := hasFPowerSeriesOnBall_regularized1F2_one b c
  have hs := (h.hasSum_z_mul_deriv (z:=z) (by simp)).add
    ((h.hasSum_mul_pow (z:=z) (by simp)).mul_left (c-1))
  have ht := (hasFPowerSeriesOnBall_regularized1F2_one b (c-1)).hasSum_mul_pow (z:=z) (by simp)
  apply HasSum.unique hs
  refine ht.congr_fun fun n => ?_
  have hc : regularizedHGFunCoeff {1} {b,c-1} n =
      ((n:ℂ)+c-1)*regularizedHGFunCoeff {1} {b,c} n := by
    rw [regularized1F2_one_coeff, regularized1F2_one_coeff]
    simp only [one_div, mul_inv]
    rw [recip_Gamma_eq_mul_recip_Gamma_add_one (c-1+n)]
    rw [show c-1+n+1=c+n by ring]
    ring
  rw [hc]
  ring

/-- A shifted `₁F₂` identity with its initial coefficient retained as the forcing term. -/
theorem regularized1F2_one_shift (b c z : ℂ) :
    z*regularizedHGFun {1} {b,c+1} z =
      regularizedHGFun {1} {b,c-1} z+(b-c)*regularizedHGFun {1} {b,c} z-
        1/(Gamma (b-1)*Gamma c) := by
  have h := hasFPowerSeriesOnBall_regularized1F2_one b c
  have hs := (h.hasSum_z_mul_deriv (z:=z) (by simp)).add
    ((h.hasSum_mul_pow (z:=z) (by simp)).mul_left (b-1))
  have hc (n : ℕ) : regularizedHGFunCoeff {1} {b,c+1} n =
      (b+n)*regularizedHGFunCoeff {1} {b,c} (n+1) := by
    rw [regularized1F2_one_coeff, regularized1F2_one_coeff]
    simp only [one_div, mul_inv]
    rw [recip_Gamma_eq_mul_recip_Gamma_add_one (b+n)]
    push_cast
    rw [show b+n+1=b+(n+1) by ring, show c+1+n=c+(n+1) by ring]
    ring
  have ht : HasSum (fun n : ℕ => ((n:ℂ)+b-1)*regularizedHGFunCoeff {1} {b,c} n*z^n)
      (z*regularizedHGFun {1} {b,c+1} z+(b-1)*regularizedHGFunCoeff {1} {b,c} 0) := by
    rw [← hasSum_nat_add_iff' 1]
    simp only [Finset.sum_range_one, Nat.cast_zero, zero_add, pow_zero, mul_one]
    have hshift := ((hasFPowerSeriesOnBall_regularized1F2_one b (c+1)).hasSum_mul_pow
      (z:=z) (by simp)).mul_left z
    convert hshift using 1
    · funext n
      push_cast
      rw [hc, pow_succ]
      ring
    · ring
  have he := (hs.congr_fun (fun n => by ring)).unique ht
  have h0 : (b-1)*regularizedHGFunCoeff {1} {b,c} 0=1/(Gamma (b-1)*Gamma c) := by
    simp only [regularizedHGFunCoeff, Multiset.map_singleton, Multiset.prod_singleton,
      Multiset.insert_eq_cons, Multiset.map_cons, Multiset.prod_cons, ascPochhammer_zero,
      Polynomial.eval_one, Nat.factorial_zero, Nat.cast_zero, Nat.cast_one, add_zero, one_mul,
      one_div, mul_inv]
    rw [recip_Gamma_eq_mul_recip_Gamma_add_one (b-1), sub_add_cancel]
    ring
  rw [h0] at he
  linear_combination -he+regularized1F2_one_lower b c z

/-- The inhomogeneous second-order equation for `₁F₂(1;b,c;z)`.
The reciprocal-Gamma forcing remains valid at every exceptional parameter. -/
theorem regularized1F2_one_inhomogeneous_ode (b c z : ℂ) :
    let F := regularizedHGFun {1} {b,c}
    z^2*deriv (deriv F) z+(b+c-1)*z*deriv F z+
      ((b-1)*(c-1)-z)*F z = 1/(Gamma (b-1)*Gamma (c-1)) := by
  let F := regularizedHGFun {1} {b,c}
  let d := regularizedHGFunCoeff {1} {b,c}
  have h := hasFPowerSeriesOnBall_regularized1F2_one b c
  have h0 := h.hasSum_mul_pow (z:=z) (by simp)
  have h1 := (hasFPowerSeriesOnBall_eulerTheta h).hasSum_mul_pow (z:=z) (by simp)
  have h2 := (hasFPowerSeriesOnBall_eulerTheta
    (hasFPowerSeriesOnBall_eulerTheta h)).hasSum_mul_pow (z:=z) (by simp)
  have hsum := (h2.add (h1.mul_left (b+c-2))).add (h0.mul_left ((b-1)*(c-1)))
  have hrec := h0.mul_left z
  have hs : HasSum (fun n : ℕ => ((n:ℂ)+b-1)*((n:ℂ)+c-1)*d n*z^n)
      (eulerTheta (eulerTheta F) z+(b+c-2)*eulerTheta F z+(b-1)*(c-1)*F z) := by
    convert hsum using 1
    funext n
    dsimp only [d]
    ring
  have hs' : HasSum (fun n : ℕ => ((n:ℂ)+b-1)*((n:ℂ)+c-1)*d n*z^n)
      (z*F z+(b-1)*(c-1)*d 0) := by
    rw [← hasSum_nat_add_iff' 1]
    simp only [Finset.sum_range_one, Nat.cast_zero, zero_add, pow_zero, mul_one]
    convert hrec using 1
    · funext n
      dsimp only [d]
      push_cast
      rw [show (n:ℂ)+1+b-1=b+n by ring, show (n:ℂ)+1+c-1=c+n by ring,
        pow_succ', ← mul_assoc, regularized1F2_one_coeff_recurrence]
      ring
    · ring
  have he := hs.unique hs'
  have hD : HasDerivAt (eulerTheta F) (deriv F z+z*deriv (deriv F) z) z := by
    have hd := (hasDerivAt_id z).mul
      ((h.analyticAt_of_mem (by simp : z ∈ Metric.eball (0:ℂ) ⊤)).deriv.differentiableAt.hasDerivAt)
    have hd' : HasDerivAt (fun w => w*deriv F w) _ z :=
      hd.congr_of_eventuallyEq (Filter.Eventually.of_forall fun w => rfl)
    unfold DLMF.Hypergeometric.eulerTheta
    simpa only [F, one_mul, id_eq] using hd'
  have hc0 : (b-1)*(c-1)*d 0=1/(Gamma (b-1)*Gamma (c-1)) := by
    simp only [d, regularizedHGFunCoeff, Multiset.map_singleton, Multiset.prod_singleton,
      Multiset.insert_eq_cons, Multiset.map_cons, Multiset.prod_cons,
      ascPochhammer_zero, Polynomial.eval_one, Nat.factorial_zero, Nat.cast_one,
      Nat.cast_zero, add_zero, one_mul]
    simp only [one_div, mul_inv]
    rw [recip_Gamma_eq_mul_recip_Gamma_add_one (b-1),
      recip_Gamma_eq_mul_recip_Gamma_add_one (c-1)]
    simp only [sub_add_cancel]
    ring
  change z^2*deriv (deriv F) z+(b+c-1)*z*deriv F z+((b-1)*(c-1)-z)*F z = _
  rw [← hc0]
  simp only [eulerTheta, hD.deriv] at he
  linear_combination he

/-- Coefficients of a power series are determined by its sums on a small disk. -/
theorem scalarSeries_unique_ball {c d : ℕ → ℂ} {g : ℂ → ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hc : ∀ z : ℂ, ‖z‖ < ρ → HasSum (fun n => c n * z ^ n) (g z))
    (hd : ∀ z : ℂ, ‖z‖ < ρ → HasSum (fun n => d n * z ^ n) (g z)) : c = d := by
  set ρ' : NNReal := ⟨ρ / 2, by positivity⟩
  have series {e : ℕ → ℂ}
      (he : ∀ z : ℂ, ‖z‖ < ρ → HasSum (fun n => e n * z ^ n) (g z)) :
      HasFPowerSeriesOnBall g (FormalMultilinearSeries.ofScalars ℂ e) 0 (ρ' : ENNReal) := by
    refine ⟨?_, ?_, ?_⟩
    · apply FormalMultilinearSeries.le_radius_of_summable_norm
      have hz0 : ‖((ρ / 2 : ℝ) : ℂ)‖ < ρ := by
        rw [norm_real, Real.norm_of_nonneg (by positivity)]; linarith
      have := (he _ hz0).summable.norm
      simp only [norm_mul, norm_pow, norm_real, Real.norm_of_nonneg
        (by positivity : (0 : ℝ) ≤ ρ / 2)] at this
      simp only [FormalMultilinearSeries.ofScalars_norm]
      exact this
    · exact ENNReal.coe_pos.mpr (by rw [← NNReal.coe_pos]; show (0 : ℝ) < ρ / 2; positivity)
    · intro z hz
      have hzNN : ‖z‖₊ < ρ' := by
        simpa only [Metric.mem_eball, edist_zero_right, enorm_lt_coe] using hz
      have hz' : ‖z‖ < ρ / 2 := by exact_mod_cast hzNN
      simpa [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, mul_comm] using
        he z (by linarith)
  exact FormalMultilinearSeries.ofScalars_series_injective ℂ ℂ
    ((series hc).hasFPowerSeriesAt.eq_formalMultilinearSeries (series hd).hasFPowerSeriesAt)

/-- **Power-series solutions of the generalized hypergeometric equation** (Duverney Thm 3.8):
if `f = ∑ cₙ zⁿ` near `0` satisfies `θ ∏ⱼ(θ+bⱼ-1) f = z ∏ᵢ(θ+aᵢ) f` and no `bⱼ` is a nonpositive
integer, then `cₙ = c₀ / 𝐅₀ · 𝐅ₙ`, i.e. `f = (f(0)/𝐅(a;b;0)) 𝐅(a;b;·)`. -/
theorem coeff_eq_of_generalized_ode {a b : Multiset ℂ} (hb : ∀ j ∈ b, ∀ k : ℕ, j ≠ -k)
    {f : ℂ → ℂ} {c : ℕ → ℂ} {r : ENNReal} (hr : 0 < r)
    (h : HasFPowerSeriesOnBall f (ofScalars ℂ c) 0 r)
    (hode : ∀ z ∈ Metric.eball (0 : ℂ) r,
      thetaPoly (X * (b.map fun j => X + C (j - 1)).prod) f z =
        z * thetaPoly (a.map fun i => X + C i).prod f z) (n : ℕ) :
    c n = c 0 / regularizedHGFunCoeff a b 0 * regularizedHGFunCoeff a b n := by
  obtain ⟨ρ, hρ0, hρr⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hr
  have hball : ∀ z : ℂ, ‖z‖ < ρ → z ∈ Metric.eball (0 : ℂ) r := fun z hz => by
    rw [Metric.mem_eball, edist_zero_right]
    exact lt_trans (by exact_mod_cast hz) hρr
  set Pb : ℂ[X] := X * (b.map fun j => X + C (j - 1)).prod
  set Pa : ℂ[X] := (a.map fun i => X + C i).prod
  set e : ℕ → ℂ := fun n => if n = 0 then 0 else Pa.eval ((n - 1 : ℕ) : ℂ) * c (n - 1)
  have hcoef := scalarSeries_unique_ball (g := thetaPoly Pb f) (c := fun n => Pb.eval (n : ℂ) * c n)
    (d := e) (ρ := ρ) (by exact_mod_cast hρ0)
    (fun z hz => by simpa [mul_assoc] using hasSum_thetaPoly h Pb (hball z hz))
    (fun z hz => by
      rw [hode z (hball z hz)]
      have hs := (hasSum_thetaPoly h Pa (hball z hz)).mul_left z
      rw [← hasSum_nat_add_iff' 1]
      convert hs using 1
      · funext n; simp [e, pow_succ]; ring
      · simp [e])
  have hrec (n : ℕ) : ((n : ℂ) + 1) * (b.map fun j : ℂ => j + n).prod * c (n + 1) =
      (a.map fun i => (n : ℂ) + i).prod * c n := by
    have := congrFun hcoef (n + 1)
    simp only [e, Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel, Pb, Pa, eval_mul, eval_X,
      eval_multiset_prod, Multiset.map_map, Function.comp_def, eval_add, eval_C] at this
    push_cast at this
    rw [show (b.map fun j : ℂ => (n : ℂ) + 1 + (j - 1)) = b.map fun j : ℂ => j + n by
      congr 1; funext j; ring] at this
    rw [show (a.map fun i : ℂ => (n : ℂ) + i) = a.map fun i : ℂ => (n : ℂ) + i from rfl]
    linear_combination this
  have hκ0 : regularizedHGFunCoeff a b 0 ≠ 0 := by
    rw [Ne, regularizedHGFunCoeff_eq_zero_iff]
    push Not
    refine ⟨fun j _ k hk => absurd hk (Nat.not_lt_zero k), fun j hj m => ?_⟩
    simpa using hb j hj m
  have hden (n : ℕ) : ((n : ℂ) + 1) * (b.map fun j : ℂ => j + n).prod ≠ 0 := by
    refine mul_ne_zero (by exact_mod_cast Nat.succ_ne_zero n) ?_
    apply Multiset.prod_ne_zero
    intro h0
    obtain ⟨j, hj, hj0⟩ := Multiset.mem_map.mp h0
    exact hb j hj n (by linear_combination hj0)
  induction n with
  | zero => field_simp
  | succ n ih =>
    have hk := regularizedHGFunCoeff_succ_mul a b n
    refine mul_left_cancel₀ (hden n) ?_
    rw [hrec n, ih]
    linear_combination (-(c 0 / regularizedHGFunCoeff a b 0)) * hk

end DLMF.Hypergeometric

end
