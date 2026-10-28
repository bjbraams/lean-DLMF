/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Core.Framework
public import DLMF.Hypergeometric.GeneralizedCalculus
public import DLMF.Confluent.Relations

/-!
# Struve functions: definitions, convergence and differential equations

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
Theorem statements were initially admitted; remaining `sorry` declarations are
not completed proofs. See `DLMF111214Acquisition.md` for coverage and validation.

The proved forcing equations use Mathlib's regularized hypergeometric series via
`regularized1F2_one_inhomogeneous_ode`. The ordinary general-solution formulas
reuse `DLMF.Bessel.eq_besselJ_besselY_of_ode`, including integer orders. The
modified solution formulas use the proved I/K Wronskian through Abel's identity.
The common quadratic gauge and reciprocal-Gamma contiguous relations supply the
calculus without excluding exceptional orders.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF
open scoped Real Topology Nat
namespace DLMF.Struve

open DLMF.Bessel

/-- A quadratic substitution and an Euler-power gauge transfer the regularized `₁F₂`
equation to an inhomogeneous Bessel equation. The gauge hypothesis fixes its branch. -/
theorem regularized1F2_bessel_gauge (r ν σ : ℂ) (g : ℂ → ℂ)
    (hg : ∀ w ∈ slitPlane, HasDerivAt g (g w*(r/w)) w)
    {z : ℂ} (hz : z ∈ slitPlane) :
    let f := fun w : ℂ => g w *
      regularizedHGFun {1} {(r-ν)/2+1,(r+ν)/2+1} (σ*w^2/4)
    z^2*iteratedDeriv 2 f z+z*deriv f z-(σ*z^2+ν^2)*f z =
      4*g z/(Gamma ((r-ν)/2)*Gamma ((r+ν)/2)) := by
  let F := regularizedHGFun {1} {(r-ν)/2+1,(r+ν)/2+1}
  let u := fun w : ℂ => σ*w^2/4
  let q := fun w : ℂ => r/w
  let v := fun w : ℂ => σ*w/2
  let f := fun w : ℂ => g w*F (u w)
  have hF (w : ℂ) : AnalyticAt ℂ F w :=
    (hasFPowerSeriesOnBall_regularized1F2_one _ _).analyticAt_of_mem (by simp)
  have hu (w : ℂ) : HasDerivAt u (v w) w := by
    convert! (((hasDerivAt_id w).pow 2).const_mul σ).div_const 4 using 1
    simp only [v, id_eq]
    ring
  have hfirst (w : ℂ) (hw : w ∈ slitPlane) :
      deriv f w=g w*(q w*F (u w)+v w*deriv F (u w)) := by
    have hd := (hg w hw).mul ((hF (u w)).differentiableAt.hasDerivAt.comp w (hu w))
    have hd' : HasDerivAt f _ w :=
      hd.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => rfl)
    rw [hd'.deriv]
    simp only [q, Function.comp_apply]
    ring
  have heq : deriv f =ᶠ[𝓝 z] fun w => g w*(q w*F (u w)+v w*deriv F (u w)) :=
    Filter.eventually_of_mem (isOpen_slitPlane.mem_nhds hz) hfirst
  have hq : HasDerivAt q (-r/z^2) z := by
    convert! (hasDerivAt_const z r).div (hasDerivAt_id z) (slitPlane_ne_zero hz) using 1
    simp
  have hv : HasDerivAt v (σ/2) z := by
    simpa only [v, id_eq, mul_one] using ((hasDerivAt_id z).const_mul σ).div_const 2
  have hsecond := (hg z hz).mul
    ((hq.mul ((hF (u z)).differentiableAt.hasDerivAt.comp z (hu z))).add
      (hv.mul ((hF (u z)).deriv.differentiableAt.hasDerivAt.comp z (hu z))))
  have hsecond' : HasDerivAt (fun w => g w*(q w*F (u w)+v w*deriv F (u w))) _ z :=
    hsecond.congr_of_eventuallyEq (Filter.Eventually.of_forall fun w => rfl)
  change z^2*iteratedDeriv 2 f z+z*deriv f z-(σ*z^2+ν^2)*f z = _
  rw [iteratedDeriv_succ, iteratedDeriv_one, heq.deriv_eq, hsecond'.deriv, hfirst z hz]
  have hode := regularized1F2_one_inhomogeneous_ode ((r-ν)/2+1) ((r+ν)/2+1) (u z)
  dsimp only at hode
  simp only [add_sub_cancel_right] at hode
  dsimp only [f, q, v, F, Pi.mul_apply, Pi.add_apply, Function.comp_apply]
  linear_combination (norm := (dsimp [u]; field_simp [slitPlane_ne_zero hz]; ring))
    (4*g z)*hode

/-- The ordinary or modified Bessel differential operator, with its singularity cleared. -/
def besselResidual (ν σ : ℂ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  z^2*iteratedDeriv 2 f z+z*deriv f z-(σ*z^2+ν^2)*f z

/-- Linearity of the Bessel operator at analytic functions. -/
theorem besselResidual_linear (ν σ A B : ℂ) {f g : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z) (hg : AnalyticAt ℂ g z) :
    besselResidual ν σ (fun w => A*f w+B*g w) z =
      A*besselResidual ν σ f z+B*besselResidual ν σ g z := by
  have hAf : AnalyticAt ℂ (fun w => A*f w) z :=
    ((analyticAt_const (v:=A)).mul hf).congr (Eventually.of_forall fun w => rfl)
  have hBg : AnalyticAt ℂ (fun w => B*g w) z :=
    ((analyticAt_const (v:=B)).mul hg).congr (Eventually.of_forall fun w => rfl)
  unfold besselResidual
  rw [iteratedDeriv_fun_add hAf.contDiffAt hBg.contDiffAt,
    iteratedDeriv_const_mul_field, iteratedDeriv_const_mul_field,
    deriv_fun_add (hf.differentiableAt.const_mul A) (hg.differentiableAt.const_mul B),
    deriv_const_mul_field, deriv_const_mul_field]
  ring

/-- The Bessel operator depends only on the germ of its argument. -/
theorem besselResidual_congr (ν σ : ℂ) {f g : ℂ → ℂ} {z : ℂ}
    (h : f =ᶠ[𝓝 z] g) : besselResidual ν σ f z=besselResidual ν σ g z := by
  simp only [besselResidual, h.iteratedDeriv_eq 2, h.deriv_eq, h.eq_of_nhds]

/-- Analyticity of the second-kind Bessel function on its principal slit plane. -/
theorem besselY_analytic (ν : ℂ) : AnalyticOnNhd ℂ (besselY ν) slitPlane :=
  (show DifferentiableOn ℂ (besselY ν) slitPlane from fun _z hz =>
    (hasDerivAt_besselY ν hz).differentiableAt.differentiableWithinAt).analyticOnNhd isOpen_slitPlane

/-- Adding an analytic particular solution gives every ordinary inhomogeneous Bessel solution.
This uses the previously proved Bessel fundamental-system theorem for every order. -/
theorem bessel_inhomogeneous_general_solution (ν : ℂ) {p f : ℂ → ℂ}
    (hp : AnalyticOnNhd ℂ p slitPlane) :
    (AnalyticOnNhd ℂ f slitPlane ∧ ∀ z ∈ slitPlane,
      besselResidual ν (-1) f z=besselResidual ν (-1) p z) ↔
      ∃ A B : ℂ, ∀ z ∈ slitPlane, f z=p z+A*besselJ ν z+B*besselY ν z := by
  have hJ : AnalyticOnNhd ℂ (besselJ ν) slitPlane := fun z hz => analyticAt_besselJ ν hz
  have hY := besselY_analytic ν
  have hJo (z : ℂ) (hz : z ∈ slitPlane) : besselResidual ν (-1) (besselJ ν) z=0 := by
    unfold besselResidual
    linear_combination besselJ_ode (ν:=ν) hz
  have hYo (z : ℂ) (hz : z ∈ slitPlane) : besselResidual ν (-1) (besselY ν) z=0 := by
    unfold besselResidual
    linear_combination besselY_ode_all ν hz
  constructor
  · rintro ⟨hf, he⟩
    have hd : DifferentiableOn ℂ (fun w => f w-p w) slitPlane :=
      fun z hz => ((hf z hz).sub (hp z hz)).differentiableAt.differentiableWithinAt
    have ho (z : ℂ) (hz : z ∈ slitPlane) :
        z^2*iteratedDeriv 2 (fun w => f w-p w) z+
          z*deriv (fun w => f w-p w) z+(z^2-ν^2)*(f z-p z)=0 := by
      have hl := besselResidual_linear ν (-1) 1 (-1) (hf z hz) (hp z hz)
      simp only [one_mul, neg_one_mul, ← sub_eq_add_neg] at hl
      unfold besselResidual at hl
      have he' := he z hz
      unfold besselResidual at he'
      linear_combination hl+he'
    obtain ⟨A,B,hAB⟩ := eq_besselJ_besselY_of_ode ν isOpen_slitPlane
      (starConvex_one_slitPlane.isPathConnected one_mem_slitPlane).isConnected.isPreconnected
      (fun _ h => h) hd ho
    exact ⟨A,B,fun z hz => by linear_combination hAB z hz⟩
  · rintro ⟨A,B,he⟩
    let g := fun w => p w+A*besselJ ν w+B*besselY ν w
    have hg : AnalyticOnNhd ℂ g slitPlane := fun z hz =>
      ((hp z hz).add (analyticAt_const.mul (hJ z hz))).add (analyticAt_const.mul (hY z hz))
    have hev (z : ℂ) (hz : z ∈ slitPlane) : f =ᶠ[𝓝 z] g :=
      Filter.eventually_of_mem (isOpen_slitPlane.mem_nhds hz) he
    refine ⟨fun z hz => (hg z hz).congr (hev z hz).symm, fun z hz => ?_⟩
    rw [besselResidual_congr ν (-1) (hev z hz)]
    have hl := besselResidual_linear ν (-1) 1 B (f:=fun w => p w+A*besselJ ν w)
      ((hp z hz).add (analyticAt_const.mul (hJ z hz))) (hY z hz)
    have hl' := besselResidual_linear ν (-1) 1 A (hp z hz) (hJ z hz)
    simp only [one_mul] at hl hl'
    change besselResidual ν (-1) (fun w => (p w+A*besselJ ν w)+B*besselY ν w) z=_
    rw [hl, hl', hJo z hz, hYo z hz]
    ring

/-- Integer half-turns leave the square of the exponential coordinate unchanged. -/
theorem exp_halfTurn_sq (w : ℂ) (m : ℤ) :
    exp (w+m*π*I)^2=exp w^2 := by
  rw [pow_two, ← Complex.exp_add,
    show w+m*π*I+(w+m*π*I)=w+w+m*(2*π*I) by ring,
    Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one, Complex.exp_add, pow_two]

/-- Reciprocal gamma coefficients; zeros of reciprocal gamma retain exceptional orders. -/
def struveCoeff (ν : ℂ) (n : ℕ) : ℂ :=
  1 / (Gamma (n+3/2) * Gamma (n+ν+3/2))

/-- Entire normalized Struve series. -/
def struveHCore (ν z : ℂ) : ℂ :=
  ∑' n : ℕ, (-1)^n * (z/2)^(2*n) * struveCoeff ν n

/-- Principal Struve H function. -/
@[dlmf 11.2.E1]
def struveH (ν z : ℂ) : ℂ :=
  (z/2)^(ν+1) * struveHCore ν z

/-- Continuation on the logarithmic plane. -/
def struveHOnLog (ν w : ℂ) : ℂ :=
  exp ((ν+1)*(w-log 2)) * struveHCore ν (exp w)

/-- The regularized 1F2 coefficient agrees at all orders, including reciprocal-Gamma zeros. -/
theorem struveCoeff_eq_regularized (ν : ℂ) (n : ℕ) :
    regularizedHGFunCoeff {1} {3/2,ν+3/2} n=struveCoeff ν n := by
  simp only [regularizedHGFunCoeff, Multiset.map_singleton, Multiset.prod_singleton,
    Multiset.insert_eq_cons, Multiset.map_cons, Multiset.prod_cons]
  rw [show (ascPochhammer ℂ n).eval 1=(n.factorial:ℂ) by simpa [poch] using poch_nat_one n,
    div_mul_eq_div_div, div_self (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))]
  simp only [struveCoeff]
  rw [show (3/2:ℂ)+n=n+3/2 by ring, show ν+3/2+n=n+ν+3/2 by ring]

/-- Exact all-parameter regularized hypergeometric representation of the Struve H core. -/
theorem struveHCore_eq_regularized (ν z : ℂ) :
    struveHCore ν z=regularizedHGFun {1} {3/2,ν+3/2} (-z^2/4) := by
  rw [struveHCore, regularizedHGFun_eq_tsum']
  apply tsum_congr
  intro n
  rw [struveCoeff_eq_regularized,
    show -z^2/4 = -((z/2)^2) by ring, neg_pow ((z/2)^2), ← pow_mul]
  ring

/-- Absolute convergence of the defining series, including exceptional orders. -/
@[dlmf 11.2.E1]
theorem hasSum_struveHCore (ν z : ℂ) :
    HasSum (fun n : ℕ => (-1)^n * (z/2)^(2*n) * struveCoeff ν n) (struveHCore ν z) := by
  have hr : (regularizedHGFunSeries {1} {3/2,ν+3/2}).radius=⊤ :=
    radius_regularizedHGFunSeries_eq_top (by simp)
  have hp : HasFPowerSeriesOnBall (regularizedHGFun {1} {3/2,ν+3/2})
      (FormalMultilinearSeries.ofScalars ℂ (regularizedHGFunCoeff {1} {3/2,ν+3/2})) 0 ⊤ := by
    change HasFPowerSeriesOnBall (regularizedHGFunSeries {1} {3/2,ν+3/2}).sum
      (regularizedHGFunSeries {1} {3/2,ν+3/2}) 0 ⊤
    rw [← hr]
    exact (regularizedHGFunSeries {1} {3/2,ν+3/2}).hasFPowerSeriesOnBall (by rw [hr]; simp)
  have hs := hp.hasSum_mul_pow (by simp : (-z^2/4) ∈ Metric.eball (0:ℂ) ⊤)
  rw [← struveHCore_eq_regularized] at hs
  refine hs.congr_fun fun n => ?_
  rw [struveCoeff_eq_regularized, show (-z^2/4)=-((z/2)^2) by ring]
  rw [neg_pow ((z/2)^2), ← pow_mul]
  ring

/-- The normalized function is entire in the argument. -/
theorem entire_struveHCore (ν : ℂ) :
    Differentiable ℂ (struveHCore ν) := by
  have hF : Differentiable ℂ (regularizedHGFun {1} {3/2,ν+3/2}) :=
    fun w => (analyticAt_regularizedHGFun_of_card_le (by simp) w).differentiableAt
  have he : struveHCore ν = fun z => regularizedHGFun {1} {3/2,ν+3/2} (-z^2/4) :=
    funext (struveHCore_eq_regularized ν)
  rw [he]
  exact hF.comp (by fun_prop)

/-- `Γ(n+3/2) ≥ Γ(3/2) n!` for natural `n`. -/
theorem Gamma_nat_add_three_halves_ge (n : ℕ) :
    Real.Gamma (3/2) * n ! ≤ Real.Gamma (n+3/2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show ((n+1 : ℕ) : ℝ) + 3/2 = (n+3/2) + 1 by push_cast; ring,
      Real.Gamma_add_one (by positivity), Nat.factorial_succ]
    push_cast
    have h0 : 0 ≤ Real.Gamma (3/2) * n ! := by
      have := Real.Gamma_pos_of_pos (by norm_num : (0:ℝ) < 3/2); positivity
    nlinarith

/-- The complex form of `Γ(n+3/2) ≥ Γ(3/2) n!`. -/
theorem norm_Gamma_nat_add_three_halves_ge (n : ℕ) :
    Real.Gamma (3/2) * n ! ≤ ‖Gamma ((n:ℂ)+3/2)‖ := by
  rw [show (n:ℂ)+3/2 = ((n+3/2 : ℝ) : ℂ) by push_cast; ring, Gamma_ofReal, norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.Gamma_pos_of_pos (by positivity))]
  exact Gamma_nat_add_three_halves_ge n

/-- The Struve-type series `∑ sⁿ (z/2)^{2n} / (Γ(n+3/2) Γ(n+ν+3/2))`, `‖s‖ = 1`, is entire in
the order `ν`, by locally uniform domination of the reciprocal-Gamma terms. -/
theorem differentiable_order_struveSeries (s z : ℂ) (hs : ‖s‖ = 1) :
    Differentiable ℂ (fun ν => ∑' n : ℕ, s^n * (z/2)^(2*n) * struveCoeff ν n) := by
  have hG : 0 < Real.Gamma (3/2) := Real.Gamma_pos_of_pos (by norm_num)
  have hdom : ∀ ν₀ : ℂ, ∃ U : Set ℂ, IsOpen U ∧ ν₀ ∈ U ∧ ∃ N : ℕ, ∃ u : ℕ → ℝ, Summable u ∧
      ∀ n, N ≤ n → ∀ ν ∈ U, ‖s^n * (z/2)^(2*n) * struveCoeff ν n‖ ≤ u n := by
    intro ν₀
    obtain ⟨V, hV, hν₀V, N, u, hu, hle⟩ := exists_regularized0F1_dominated (ν₀+3/2) ‖(z/2)^2‖
    refine ⟨(fun ν => ν+3/2) ⁻¹' V, hV.preimage (by fun_prop), hν₀V, N,
      fun n => u n / Real.Gamma (3/2), hu.div_const _, fun n hn ν hν => ?_⟩
    have h1 := hle n hn (ν+3/2) hν ((z/2)^2) le_rfl
    have hGn := norm_Gamma_nat_add_three_halves_ge n
    have hfac : (0:ℝ) < n ! := by exact_mod_cast Nat.factorial_pos n
    have hnorm : ‖s^n * (z/2)^(2*n) * struveCoeff ν n‖ =
        ‖((z/2)^2)^n / n ! * (Gamma (ν+3/2+n))⁻¹‖ * (n ! / ‖Gamma ((n:ℂ)+3/2)‖) := by
      simp only [struveCoeff, norm_mul, norm_div, norm_pow, hs, one_pow, one_mul, norm_inv,
        Complex.norm_natCast, norm_one, ← pow_mul]
      rw [show (n:ℂ)+ν+3/2 = ν+3/2+n by ring]
      field_simp
    rw [hnorm]
    have hq : (n ! : ℝ) / ‖Gamma ((n:ℂ)+3/2)‖ ≤ 1 / Real.Gamma (3/2) := by
      rw [div_le_div_iff₀ (lt_of_lt_of_le (by positivity) hGn) hG]
      linarith
    calc _ ≤ u n * (1 / Real.Gamma (3/2)) :=
          mul_le_mul h1 hq (by positivity) (le_trans (norm_nonneg _) h1)
      _ = u n / Real.Gamma (3/2) := by ring
  have hsum : ∀ ν, Summable fun n : ℕ => s^n * (z/2)^(2*n) * struveCoeff ν n := by
    intro ν
    obtain ⟨U, -, hνU, N, u, hu, hle⟩ := hdom ν
    refine Summable.of_norm_bounded_eventually hu ?_
    rw [Nat.cofinite_eq_atTop]
    filter_upwards [eventually_ge_atTop N] with n hn using hle n hn ν hνU
  have hF : ∀ n : ℕ, Differentiable ℂ (fun ν => s^n * (z/2)^(2*n) * struveCoeff ν n) := by
    intro n
    have : (fun ν => s^n * (z/2)^(2*n) * struveCoeff ν n) =
        fun ν => s^n * (z/2)^(2*n) * (Gamma ((n:ℂ)+3/2))⁻¹ * (Gamma (n+ν+3/2))⁻¹ := by
      funext ν; simp only [struveCoeff, one_div, mul_inv]; ring
    rw [this]
    exact (differentiable_one_div_Gamma.comp (f := fun ν : ℂ => (n:ℂ)+ν+3/2)
      (by fun_prop)).const_mul _
  have := analyticOnNhd_tsum_of_eventually_dominated hF hsum hdom
  exact fun ν => (this ν (mem_univ ν)).differentiableAt

/-- The normalized function is entire in the order. -/
theorem entire_order_struveHCore (z : ℂ) :
    Differentiable ℂ (fun ν => struveHCore ν z) := by
  exact differentiable_order_struveSeries (-1) z (by simp)

/-- Continuation with inherited logarithm, not reapplication of a principal power. -/
@[dlmf 11.4.E16]
theorem struveHOnLog_shift (ν w : ℂ) (m : ℤ) :
    struveHOnLog ν (w+m*π*I) = exp (m*π*I*(ν+1))*struveHOnLog ν w := by
  have hc : struveHCore ν (exp (w+m*π*I))=struveHCore ν (exp w) := by
    rw [struveHCore_eq_regularized, struveHCore_eq_regularized, exp_halfTurn_sq]
  unfold struveHOnLog
  rw [hc, show (ν+1)*(w+m*π*I-log 2)=m*π*I*(ν+1)+(ν+1)*(w-log 2) by ring,
    Complex.exp_add]
  ring

/-- Entire normalized Struve series. -/
def struveLCore (ν z : ℂ) : ℂ :=
  ∑' n : ℕ, 1 * (z/2)^(2*n) * struveCoeff ν n

/-- Principal Struve L function. -/
@[dlmf 11.2.E2]
def struveL (ν z : ℂ) : ℂ :=
  (z/2)^(ν+1) * struveLCore ν z

/-- Continuation on the logarithmic plane. -/
def struveLOnLog (ν w : ℂ) : ℂ :=
  exp ((ν+1)*(w-log 2)) * struveLCore ν (exp w)

/-- Exact all-parameter regularized hypergeometric representation of the Struve L core. -/
theorem struveLCore_eq_regularized (ν z : ℂ) :
    struveLCore ν z=regularizedHGFun {1} {3/2,ν+3/2} (z^2/4) := by
  rw [struveLCore, regularizedHGFun_eq_tsum']
  apply tsum_congr
  intro n
  rw [struveCoeff_eq_regularized, show z^2/4=(z/2)^2 by ring, ← pow_mul]
  ring

/-- Absolute convergence of the defining series, including exceptional orders. -/
@[dlmf 11.2.E2]
theorem hasSum_struveLCore (ν z : ℂ) :
    HasSum (fun n : ℕ => 1 * (z/2)^(2*n) * struveCoeff ν n) (struveLCore ν z) := by
  have hr : (regularizedHGFunSeries {1} {3/2,ν+3/2}).radius=⊤ :=
    radius_regularizedHGFunSeries_eq_top (by simp)
  have hp : HasFPowerSeriesOnBall (regularizedHGFun {1} {3/2,ν+3/2})
      (FormalMultilinearSeries.ofScalars ℂ (regularizedHGFunCoeff {1} {3/2,ν+3/2})) 0 ⊤ := by
    change HasFPowerSeriesOnBall (regularizedHGFunSeries {1} {3/2,ν+3/2}).sum
      (regularizedHGFunSeries {1} {3/2,ν+3/2}) 0 ⊤
    rw [← hr]
    exact (regularizedHGFunSeries {1} {3/2,ν+3/2}).hasFPowerSeriesOnBall (by rw [hr]; simp)
  have hs := hp.hasSum_mul_pow (by simp : (z^2/4) ∈ Metric.eball (0:ℂ) ⊤)
  rw [← struveLCore_eq_regularized] at hs
  refine hs.congr_fun fun n => ?_
  rw [struveCoeff_eq_regularized, show (z^2/4)=(z/2)^2 by ring]
  rw [← pow_mul]
  ring

/-- The normalized function is entire in the argument. -/
theorem entire_struveLCore (ν : ℂ) :
    Differentiable ℂ (struveLCore ν) := by
  have hF : Differentiable ℂ (regularizedHGFun {1} {3/2,ν+3/2}) :=
    fun w => (analyticAt_regularizedHGFun_of_card_le (by simp) w).differentiableAt
  have he : struveLCore ν = fun z => regularizedHGFun {1} {3/2,ν+3/2} (z^2/4) :=
    funext (struveLCore_eq_regularized ν)
  rw [he]
  exact hF.comp (by fun_prop)

/-- The normalized function is entire in the order. -/
theorem entire_order_struveLCore (z : ℂ) :
    Differentiable ℂ (fun ν => struveLCore ν z) := by
  have h := differentiable_order_struveSeries 1 z (by simp)
  simp only [one_pow] at h
  exact h

/-- Continuation with inherited logarithm, not reapplication of a principal power. -/
@[dlmf 11.4.E17]
theorem struveLOnLog_shift (ν w : ℂ) (m : ℤ) :
    struveLOnLog ν (w+m*π*I) = exp (m*π*I*(ν+1))*struveLOnLog ν w := by
  have hc : struveLCore ν (exp (w+m*π*I))=struveLCore ν (exp w) := by
    rw [struveLCore_eq_regularized, struveLCore_eq_regularized, exp_halfTurn_sq]
  unfold struveLOnLog
  rw [hc, show (ν+1)*(w+m*π*I-log 2)=m*π*I*(ν+1)+(ν+1)*(w-log 2) by ring,
    Complex.exp_add]
  ring

/-- A common signed regularized-series representation of the ordinary and modified Struve functions. -/
def struveQuadratic (ν σ z : ℂ) : ℂ :=
  (z/2)^(ν+1)*regularizedHGFun {1} {3/2,ν+3/2} (σ*z^2/4)

/-- Ordinary Struve H is the negative-sign quadratic series. -/
theorem struveQuadratic_H (ν z : ℂ) : struveQuadratic ν (-1) z=struveH ν z := by
  simp only [struveQuadratic,struveH,struveHCore_eq_regularized,neg_one_mul,neg_div]

/-- Modified Struve L is the positive-sign quadratic series. -/
theorem struveQuadratic_L (ν z : ℂ) : struveQuadratic ν 1 z=struveL ν z := by
  simp only [struveQuadratic,struveL,struveLCore_eq_regularized,one_mul]

/-- Lower-parameter contiguity gives the common Struve first derivative at every order. -/
theorem hasDerivAt_struveQuadratic (ν σ : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    HasDerivAt (struveQuadratic ν σ)
      (struveQuadratic (ν-1) σ z-ν/z*struveQuadratic ν σ z) z := by
  let F := regularizedHGFun {1} {3/2,ν+3/2}
  let u := fun w : ℂ => σ*w^2/4
  have hF : HasDerivAt F (deriv F (u z)) (u z) :=
    ((hasFPowerSeriesOnBall_regularized1F2_one _ _).analyticAt_of_mem (by simp)).differentiableAt.hasDerivAt
  have hu : HasDerivAt u (σ*z/2) z := by
    convert! (((hasDerivAt_id z).pow 2).const_mul σ).div_const 4 using 1
    simp only [id_eq]
    ring
  have hd := (hasDerivAt_besselPrefactor (ν+1) hz).mul (hF.comp z hu)
  have hd' : HasDerivAt (struveQuadratic ν σ) _ z :=
    hd.congr_of_eventuallyEq (Eventually.of_forall fun w => rfl)
  refine hd'.congr_deriv ?_
  have hc := regularized1F2_one_lower (3/2) (ν+3/2) (u z)
  have hp : (z/2)^(ν+1)=(z/2)^ν*(z/2) := by
    rw [cpow_add _ _ (div_ne_zero (slitPlane_ne_zero hz) (by norm_num)),cpow_one]
  simp only [struveQuadratic, show ν-1+1=ν by ring,
    show ν-1+3/2=ν+3/2-1 by ring]
  dsimp only [F, u, Function.comp_apply] at hc ⊢
  rw [hp]
  linear_combination (norm := (field_simp [slitPlane_ne_zero hz]; ring)) (z/2)^ν*hc

/-- Cancelling the unit upper and lower parameters retains the entire Bessel series. -/
theorem regularized1F2_one_one (b z : ℂ) :
    regularizedHGFun {1} {b,1} z=regularizedHGFun ∅ {b} z := by
  simp only [regularizedHGFun_eq_tsum']
  apply tsum_congr
  intro n
  rw [regularized1F2_one_coeff,regularizedHGFunCoeff_empty,
    show (1:ℂ)+n=(n:ℂ)+1 by ring,Gamma_nat_eq_factorial]
  ring

/-- The common Struve order recurrence retains its reciprocal-Gamma forcing. -/
theorem struveQuadratic_recurrence (ν σ : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    struveQuadratic (ν-1) σ z-σ*struveQuadratic (ν+1) σ z =
      2*ν/z*struveQuadratic ν σ z+(z/2)^ν/(Real.sqrt π*Gamma (ν+3/2)) := by
  have hc := regularized1F2_one_shift (3/2) (ν+3/2) (σ*z^2/4)
  rw [show (3/2:ℂ)-1=1/2 by norm_num,DLMF.Confluent.Gamma_one_half_eq_sqrt] at hc
  have hp : (z/2)^(ν+1)=(z/2)^ν*(z/2) := by
    rw [cpow_add _ _ (div_ne_zero (slitPlane_ne_zero hz) (by norm_num)),cpow_one]
  have hp' : (z/2)^(ν+1+1)=(z/2)^ν*z^2/4 := by
    rw [show ν+1+1=ν+(2:ℕ) by norm_num; ring,
      cpow_add _ _ (div_ne_zero (slitPlane_ne_zero hz) (by norm_num)),cpow_natCast,div_pow]
    ring
  simp only [struveQuadratic,show ν-1+1=ν by ring,show ν-1+3/2=ν+3/2-1 by ring,
    show ν+1+3/2=ν+3/2+1 by ring,hp,hp']
  linear_combination (norm := (field_simp [slitPlane_ne_zero hz]; ring)) -(z/2)^ν*hc

/-- Weighted differentiation lowers the Struve order without excluding exceptional parameters. -/
theorem hasDerivAt_weighted_struveQuadratic (ν σ : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    HasDerivAt (fun w => w^ν*struveQuadratic ν σ w) (z^ν*struveQuadratic (ν-1) σ z) z := by
  have hd := ((hasDerivAt_id z).cpow_const (c:=ν) hz).mul (hasDerivAt_struveQuadratic ν σ hz)
  refine hd.congr_deriv ?_
  simp only [id_eq,mul_one]
  rw [cpow_sub _ _ (slitPlane_ne_zero hz),cpow_one]
  ring

/-- Reciprocal weighting raises the order, with the Struve forcing term retained. -/
theorem hasDerivAt_reciprocal_weighted_struveQuadratic (ν σ : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    HasDerivAt (fun w => w^(-ν)*struveQuadratic ν σ w)
      (2^(-ν)/(Real.sqrt π*Gamma (ν+3/2))+σ*z^(-ν)*struveQuadratic (ν+1) σ z) z := by
  have hd := ((hasDerivAt_id z).cpow_const (c:=-ν) hz).mul (hasDerivAt_struveQuadratic ν σ hz)
  refine hd.congr_deriv ?_
  have hp : z^(-ν)*(z/2)^ν=(2:ℂ)^(-ν) := by
    rw [cpow_def_of_ne_zero (slitPlane_ne_zero hz),
      cpow_def_of_ne_zero (div_ne_zero (slitPlane_ne_zero hz) (by norm_num)),
      cpow_def_of_ne_zero (by norm_num : (2:ℂ)≠0),log_div_ofNat_two hz,← Complex.exp_add]
    congr 1
    ring
  simp only [id_eq,mul_one]
  rw [cpow_sub _ _ (slitPlane_ne_zero hz),cpow_one]
  have hr := struveQuadratic_recurrence ν σ hz
  rw [← hp]
  linear_combination (norm := (field_simp [slitPlane_ne_zero hz]; ring)) z^(-ν)*hr

/-- Iterating weighted differentiation lowers the order one step at a time on the slit plane. -/
theorem iterated_weighted_struveQuadratic (ν σ : ℂ) (m : ℕ) {z : ℂ} (hz : z ∈ slitPlane) :
    ((fun f : ℂ → ℂ => fun z => deriv f z/z)^[m]) (fun z => z^ν*struveQuadratic ν σ z) z =
      z^(ν-m)*struveQuadratic (ν-m) σ z := by
  induction m generalizing z with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    have he : ((fun f : ℂ → ℂ => fun z => deriv f z/z)^[m]) (fun z => z^ν*struveQuadratic ν σ z) =ᶠ[𝓝 z]
        (fun w => w^(ν-m)*struveQuadratic (ν-m) σ w) := by
      filter_upwards [isOpen_slitPlane.mem_nhds hz] with w hw
      exact ih hw
    change deriv _ z/z=_
    rw [he.deriv_eq,(hasDerivAt_weighted_struveQuadratic (ν-m) σ hz).deriv]
    push_cast
    rw [show ν-(m+1)=ν-m-1 by ring,cpow_sub (ν-m) 1 (slitPlane_ne_zero hz),cpow_one]
    ring

/-- The auxiliary ordinary Struve function `H_ν(z) - Y_ν(z)`. -/
@[dlmf 11.2.E5]
def struveK (ν z : ℂ) : ℂ :=
  struveH ν z - besselY ν z

/-- The auxiliary modified Struve function `L_ν(z) - I_ν(z)`. -/
@[dlmf 11.2.E6]
def struveM (ν z : ℂ) : ℂ :=
  struveL ν z - besselI ν z

/-- The ordinary or modified inhomogeneous Bessel equation defining a Struve solution, with the
DLMF reciprocal-Gamma forcing term. -/
@[dlmf 11.2.E7, dlmf 11.2.E9]
def struveEquation (ν : ℂ) (modified : Bool) (f : ℂ → ℂ) (z : ℂ) : Prop :=
  iteratedDeriv 2 f z + deriv f z/z + ((if modified then -1 else 1)-ν^2/z^2)*f z = (z/2)^(ν-1)/(Real.sqrt π*Gamma (ν+1/2))

/-- Analyticity of the principal Struve functions on the slit plane. -/
theorem struve_analytic (ν : ℂ) :
    AnalyticOnNhd ℂ (struveH ν) slitPlane ∧ AnalyticOnNhd ℂ (struveL ν) slitPlane := by
  have hg (z : ℂ) (hz : z ∈ slitPlane) : AnalyticAt ℂ (fun w : ℂ => (w/2)^(ν+1)) z :=
    (analyticAt_id.div_const (c:=(2:ℂ))).cpow analyticAt_const (div_two_mem_slitPlane hz)
  constructor
  · intro z hz
    exact (hg z hz).mul (((entire_struveHCore ν).differentiableOn.analyticOnNhd isOpen_univ) z (mem_univ z))
  · intro z hz
    exact (hg z hz).mul (((entire_struveLCore ν).differentiableOn.analyticOnNhd isOpen_univ) z (mem_univ z))

/-- The common Struve forcing, with a sign distinguishing ordinary and modified equations. -/
theorem struve_series_ode (ν σ : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    let f := fun w : ℂ => (w/2)^(ν+1)*regularizedHGFun {1} {3/2,ν+3/2} (σ*w^2/4)
    iteratedDeriv 2 f z+deriv f z/z+(-σ-ν^2/z^2)*f z =
      (z/2)^(ν-1)/(Real.sqrt π*Gamma (ν+1/2)) := by
  have h := regularized1F2_bessel_gauge (ν+1) ν σ (fun w => (w/2)^(ν+1))
    (fun w hw => hasDerivAt_besselPrefactor (ν+1) hw) hz
  rw [show (ν+1-ν)/2+1=(3/2:ℂ) by ring,
    show (ν+1+ν)/2+1=ν+3/2 by ring,
    show (ν+1-ν)/2=(1/2:ℂ) by ring,
    show (ν+1+ν)/2=ν+1/2 by ring,
    DLMF.Confluent.Gamma_one_half_eq_sqrt] at h
  have hp : (z/2)^(ν+1)=(z/2)^(ν-1)*z^2/4 := by
    rw [show ν+1=ν-1+(2:ℕ) by norm_num; ring, cpow_add _ _
      (div_ne_zero (slitPlane_ne_zero hz) (by norm_num)), cpow_natCast, div_pow]
    ring
  let f := fun w : ℂ => (w/2)^(ν+1)*regularizedHGFun {1} {3/2,ν+3/2} (σ*w^2/4)
  change z^2*iteratedDeriv 2 f z+z*deriv f z-(σ*z^2+ν^2)*f z =
    4*(z/2)^(ν+1)/(Real.sqrt π*Gamma (ν+1/2)) at h
  change iteratedDeriv 2 f z+deriv f z/z+(-σ-ν^2/z^2)*f z = _
  have hr : 4*(z/2)^(ν+1)/(Real.sqrt π*Gamma (ν+1/2)) =
      z^2*((z/2)^(ν-1)/(Real.sqrt π*Gamma (ν+1/2))) := by rw [hp]; ring
  rw [hr] at h
  generalize iteratedDeriv 2 f z=A, deriv f z=B, f z=C at h ⊢
  linear_combination (norm := (field_simp [slitPlane_ne_zero hz]; ring)) h/z^2

/-- The stated relation follows from the given hypotheses: `struveEquation ν false (struveH ν) z`. -/
@[dlmf 11.2.E8]
theorem struveH_ode (ν : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    struveEquation ν false (struveH ν) z := by
  have h := struve_series_ode ν (-1) hz
  have he : (fun w : ℂ => (w/2)^(ν+1)*regularizedHGFun {1} {3/2,ν+3/2} ((-1)*w^2/4)) =
      struveH ν := by
    funext w
    simp only [struveH, struveHCore_eq_regularized, neg_one_mul, neg_div]
  dsimp only at h
  rw [he] at h
  simpa only [struveEquation, Bool.false_eq_true, ↓reduceIte, neg_neg, neg_one_mul, one_mul, struveH, struveHCore_eq_regularized, struveL, struveLCore_eq_regularized] using h

/-- The auxiliary ordinary Struve function satisfies the inhomogeneous Bessel equation with the
ordinary Struve forcing term. -/
@[dlmf 11.2.E8]
theorem struveK_ode (ν : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    struveEquation ν false (struveK ν) z := by
  have hp := (struve_analytic ν).1 z hz
  have hg : AnalyticAt ℂ (besselY ν) z := besselY_analytic ν z hz
  have hl := besselResidual_linear ν (-1) 1 (-1) hp hg
  have ho := besselY_ode_all ν hz
  have he := struveH_ode ν hz
  simp only [one_mul, neg_one_mul, ← sub_eq_add_neg] at hl
  change besselResidual ν (-1) (fun w => struveH ν w-besselY ν w) z=_ at hl
  unfold besselResidual at hl
  unfold struveEquation at he ⊢
  simp only [Bool.false_eq_true, ↓reduceIte] at he ⊢
  rw [show struveK ν=(fun w => struveH ν w-besselY ν w) from rfl]
  generalize iteratedDeriv 2 (struveH ν) z=A, deriv (struveH ν) z=B,
    iteratedDeriv 2 (besselY ν) z=C, deriv (besselY ν) z=D,
    iteratedDeriv 2 (fun w => struveH ν w-besselY ν w) z=E,
    deriv (fun w => struveH ν w-besselY ν w) z=F at hl ho he ⊢
  linear_combination (norm := (field_simp [slitPlane_ne_zero hz]; ring)) hl/z^2+he-ho/z^2

/-- The modified Struve function satisfies the inhomogeneous modified Bessel equation with the
prescribed Gamma-normalized forcing term. -/
@[dlmf 11.2.E10]
theorem struveL_ode (ν : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    struveEquation ν true (struveL ν) z := by
  have h := struve_series_ode ν (1) hz
  have he : (fun w : ℂ => (w/2)^(ν+1)*regularizedHGFun {1} {3/2,ν+3/2} ((1)*w^2/4)) =
      struveL ν := by
    funext w
    simp only [struveL, struveLCore_eq_regularized, one_mul]
  dsimp only at h
  rw [he] at h
  simpa only [struveEquation, Bool.false_eq_true, ↓reduceIte, neg_neg, neg_one_mul, one_mul, struveH, struveHCore_eq_regularized, struveL, struveLCore_eq_regularized] using h

/-- The stated relation follows from the given hypotheses: `struveEquation ν true (struveM ν) z`. -/
@[dlmf 11.2.E10]
theorem struveM_ode (ν : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    struveEquation ν true (struveM ν) z := by
  have hp := (struve_analytic ν).2 z hz
  have hg : AnalyticAt ℂ (besselI ν) z := analyticAt_besselI ν hz
  have hl := besselResidual_linear ν (1) 1 (-1) hp hg
  have ho := besselI_ode (ν:=ν) hz
  have he := struveL_ode ν hz
  simp only [one_mul, neg_one_mul, ← sub_eq_add_neg] at hl
  change besselResidual ν (1) (fun w => struveL ν w-besselI ν w) z=_ at hl
  unfold besselResidual at hl
  unfold struveEquation at he ⊢
  simp only [↓reduceIte] at he ⊢
  rw [show struveM ν=(fun w => struveL ν w-besselI ν w) from rfl]
  generalize iteratedDeriv 2 (struveL ν) z=A, deriv (struveL ν) z=B,
    iteratedDeriv 2 (besselI ν) z=C, deriv (besselI ν) z=D,
    iteratedDeriv 2 (fun w => struveL ν w-besselI ν w) z=E,
    deriv (fun w => struveL ν w-besselI ν w) z=F at hl ho he ⊢
  linear_combination (norm := (field_simp [slitPlane_ne_zero hz]; ring)) hl/z^2+he-ho/z^2

/-- An analytic function on S satisfying the ordinary or modified Struve differential equation at
each point of S. -/
def IsStruveSolutionOn (ν : ℂ) (modified : Bool) (f : ℂ → ℂ) (S : Set ℂ) : Prop :=
  AnalyticOnNhd ℂ f S ∧ ∀ z ∈ S, struveEquation ν modified f z

/-- General analytic solutions on the principal slit plane; numerical stability is not asserted. -/
@[dlmf 11.2.E11]
theorem struve_general_solution_11 (ν : ℂ) (f : ℂ → ℂ) :
    IsStruveSolutionOn ν false f slitPlane ↔ ∃ A B : ℂ, ∀ z ∈ slitPlane, f z = struveH ν z + A*besselJ ν z + B*besselY ν z := by
  rw [← bessel_inhomogeneous_general_solution ν (struve_analytic ν).1]
  unfold IsStruveSolutionOn
  apply and_congr_right
  intro _
  apply forall_congr'
  intro z
  apply forall_congr'
  intro hz
  have hp := struveH_ode ν hz
  unfold struveEquation at hp ⊢
  simp only [Bool.false_eq_true, ↓reduceIte] at hp ⊢
  unfold besselResidual
  constructor
  · intro hf
    linear_combination (norm := (field_simp [slitPlane_ne_zero hz]; ring)) z^2*(hf-hp)
  · intro hf
    linear_combination (norm := (field_simp [slitPlane_ne_zero hz]; ring)) hf/z^2+hp

/-- General analytic solutions on the principal slit plane; numerical stability is not asserted. -/
@[dlmf 11.2.E12]
theorem struve_general_solution_12 (ν : ℂ) (f : ℂ → ℂ) :
    IsStruveSolutionOn ν false f slitPlane ↔ ∃ A B : ℂ, ∀ z ∈ slitPlane, f z = struveK ν z + A*besselJ ν z + B*besselY ν z := by
  rw [struve_general_solution_11]
  constructor
  · rintro ⟨A,B,h⟩
    refine ⟨A,B+1,fun z hz => ?_⟩
    rw [h z hz]
    simp only [struveK]
    ring
  · rintro ⟨A,B,h⟩
    refine ⟨A,B-1,fun z hz => ?_⟩
    rw [h z hz]
    simp only [struveK]
    ring

/-- General analytic solutions on the principal slit plane; numerical stability is not asserted. -/
@[dlmf 11.2.E13]
theorem struve_general_solution_13 (ν : ℂ) (f : ℂ → ℂ) :
    IsStruveSolutionOn ν false f slitPlane ↔ ∃ A B : ℂ, ∀ z ∈ slitPlane, f z = struveH ν z + A*besselJ ν z + B*hankelH1 ν z := by
  rw [struve_general_solution_11]
  constructor
  · rintro ⟨A,B,h⟩
    refine ⟨A+B*I,B/I,fun z hz => ?_⟩
    rw [h z hz]
    simp only [hankelH1]
    field_simp
    ring_nf
    simp [I_sq]
  · rintro ⟨A,B,h⟩
    refine ⟨A+B,B*I,fun z hz => ?_⟩
    rw [h z hz]
    simp only [hankelH1]
    ring

/-- General analytic solutions on the principal slit plane; numerical stability is not asserted. -/
@[dlmf 11.2.E14]
theorem struve_general_solution_14 (ν : ℂ) (f : ℂ → ℂ) :
    IsStruveSolutionOn ν false f slitPlane ↔ ∃ A B : ℂ, ∀ z ∈ slitPlane, f z = struveH ν z + A*besselJ ν z + B*hankelH2 ν z := by
  rw [struve_general_solution_11]
  constructor
  · rintro ⟨A,B,h⟩
    refine ⟨A-B*I,-B/I,fun z hz => ?_⟩
    rw [h z hz]
    simp only [hankelH2]
    field_simp
    ring_nf
    simp [I_sq]
  · rintro ⟨A,B,h⟩
    refine ⟨A+B,-B*I,fun z hz => ?_⟩
    rw [h z hz]
    simp only [hankelH2]
    ring

/-- General analytic solutions on the principal slit plane; numerical stability is not asserted. -/
@[dlmf 11.2.E15]
theorem struve_general_solution_15 (ν : ℂ) (f : ℂ → ℂ) :
    IsStruveSolutionOn ν false f slitPlane ↔ ∃ A B : ℂ, ∀ z ∈ slitPlane, f z = struveK ν z + A*hankelH1 ν z + B*hankelH2 ν z := by
  rw [struve_general_solution_11]
  constructor
  · rintro ⟨A,B,h⟩
    refine ⟨(A-I*B-I)/2,(A+I*B+I)/2,fun z hz => ?_⟩
    rw [h z hz]
    simp only [struveK, hankelH1, hankelH2]
    ring_nf
    simp [I_sq]
  · rintro ⟨A,B,h⟩
    refine ⟨A+B,(A-B)*I-1,fun z hz => ?_⟩
    rw [h z hz]
    simp only [struveK, hankelH1, hankelH2]
    ring

/-- Abel's identity for the signed Bessel operator, with analytic solutions on the slit plane. -/
theorem besselResidual_wronskian (ν σ : ℂ) {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f slitPlane) (hg : AnalyticOnNhd ℂ g slitPlane)
    (hfo : ∀ z∈slitPlane, besselResidual ν σ f z=0)
    (hgo : ∀ z∈slitPlane, besselResidual ν σ g z=0)
    {z : ℂ} (hz : z∈slitPlane) :
    HasDerivAt (fun w=>w*(f w*deriv g w-deriv f w*g w)) 0 z := by
  have hd := (hasDerivAt_id z).mul
    (((hf z hz).differentiableAt.hasDerivAt.mul (hg z hz).deriv.differentiableAt.hasDerivAt).sub
      ((hf z hz).deriv.differentiableAt.hasDerivAt.mul (hg z hz).differentiableAt.hasDerivAt))
  refine hd.congr_deriv ?_
  have he := hfo z hz
  have he' := hgo z hz
  simp only [besselResidual,iteratedDeriv_succ,iteratedDeriv_zero] at he he'
  simp only [id_eq,Pi.mul_apply,Pi.sub_apply]
  apply mul_left_cancel₀ (slitPlane_ne_zero hz)
  rw [mul_zero]
  linear_combination f z*he'-g z*he

/-- The I/K Wronskian gives every analytic solution of the modified Bessel equation. -/
theorem eq_besselK_besselI_of_residual (ν : ℂ) {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f slitPlane) (ho : ∀ z∈slitPlane, besselResidual ν 1 f z=0) :
    ∃ A B : ℂ, ∀ z∈slitPlane, f z=A*besselK ν z+B*besselI ν z := by
  have hK : AnalyticOnNhd ℂ (besselK ν) slitPlane :=
    (show DifferentiableOn ℂ (besselK ν) slitPlane from fun z hz =>
      (hasDerivAt_besselK ν hz).differentiableAt.differentiableWithinAt).analyticOnNhd isOpen_slitPlane
  have hI : AnalyticOnNhd ℂ (besselI ν) slitPlane := fun z hz=>analyticAt_besselI ν hz
  have hKo (z : ℂ) (hz : z∈slitPlane) : besselResidual ν 1 (besselK ν) z=0 := by
    unfold besselResidual; linear_combination besselK_ode_all ν hz
  have hIo (z : ℂ) (hz : z∈slitPlane) : besselResidual ν 1 (besselI ν) z=0 := by
    unfold besselResidual; linear_combination besselI_ode (ν:=ν) hz
  have hconst {u v : ℂ → ℂ} (hu : AnalyticOnNhd ℂ u slitPlane)
      (hv : AnalyticOnNhd ℂ v slitPlane)
      (huo : ∀ z∈slitPlane, besselResidual ν 1 u z=0)
      (hvo : ∀ z∈slitPlane, besselResidual ν 1 v z=0) (z : ℂ) (hz : z∈slitPlane) :
      z*(u z*deriv v z-deriv u z*v z)=u 1*deriv v 1-deriv u 1*v 1 := by
    have h := isOpen_slitPlane.is_const_of_deriv_eq_zero
      (starConvex_one_slitPlane.isPathConnected one_mem_slitPlane).isConnected.isPreconnected
      (fun w hw=>(besselResidual_wronskian ν 1 hu hv huo hvo hw).differentiableAt.differentiableWithinAt)
      (fun w hw=>(besselResidual_wronskian ν 1 hu hv huo hvo hw).deriv) hz one_mem_slitPlane
    simpa using h
  refine ⟨f 1*deriv (besselI ν) 1-deriv f 1*besselI ν 1,
    besselK ν 1*deriv f 1-deriv (besselK ν) 1*f 1,fun z hz=>?_⟩
  rw [← hconst hf hI ho hIo z hz,← hconst hK hf hKo ho z hz]
  have he := wronskian_besselK_besselI ν hz
  field_simp [slitPlane_ne_zero hz] at he
  linear_combination -f z*he

/-- An analytic particular solution translates the modified I/K solution space. -/
theorem modified_bessel_inhomogeneous_general_solution (ν : ℂ) {p f : ℂ → ℂ}
    (hp : AnalyticOnNhd ℂ p slitPlane) :
    (AnalyticOnNhd ℂ f slitPlane ∧ ∀ z∈slitPlane,
      besselResidual ν 1 f z=besselResidual ν 1 p z) ↔
      ∃ A B : ℂ, ∀ z∈slitPlane, f z=p z+A*besselK ν z+B*besselI ν z := by
  have hK : AnalyticOnNhd ℂ (besselK ν) slitPlane :=
    (show DifferentiableOn ℂ (besselK ν) slitPlane from fun z hz =>
      (hasDerivAt_besselK ν hz).differentiableAt.differentiableWithinAt).analyticOnNhd isOpen_slitPlane
  have hI : AnalyticOnNhd ℂ (besselI ν) slitPlane := fun z hz=>analyticAt_besselI ν hz
  have hKo (z : ℂ) (hz : z∈slitPlane) : besselResidual ν 1 (besselK ν) z=0 := by
    unfold besselResidual; linear_combination besselK_ode_all ν hz
  have hIo (z : ℂ) (hz : z∈slitPlane) : besselResidual ν 1 (besselI ν) z=0 := by
    unfold besselResidual; linear_combination besselI_ode (ν:=ν) hz
  constructor
  · rintro ⟨hf,he⟩
    have ha : AnalyticOnNhd ℂ (fun w=>f w-p w) slitPlane := fun z hz=>(hf z hz).sub (hp z hz)
    have ho (z : ℂ) (hz : z∈slitPlane) : besselResidual ν 1 (fun w=>f w-p w) z=0 := by
      have hl := besselResidual_linear ν 1 1 (-1) (hf z hz) (hp z hz)
      simp only [one_mul,neg_one_mul,← sub_eq_add_neg] at hl
      linear_combination hl+he z hz
    obtain ⟨A,B,hAB⟩ := eq_besselK_besselI_of_residual ν ha ho
    exact ⟨A,B,fun z hz=>by linear_combination hAB z hz⟩
  · rintro ⟨A,B,he⟩
    let g := fun w=>p w+A*besselK ν w+B*besselI ν w
    have hg : AnalyticOnNhd ℂ g slitPlane := fun z hz=>
      ((hp z hz).add (analyticAt_const.mul (hK z hz))).add (analyticAt_const.mul (hI z hz))
    have hev (z : ℂ) (hz : z∈slitPlane) : f=ᶠ[𝓝 z] g :=
      Filter.eventually_of_mem (isOpen_slitPlane.mem_nhds hz) he
    refine ⟨fun z hz=>(hg z hz).congr (hev z hz).symm,fun z hz=>?_⟩
    rw [besselResidual_congr ν 1 (hev z hz)]
    have hl := besselResidual_linear ν 1 1 B (f:=fun w=>p w+A*besselK ν w)
      ((hp z hz).add (analyticAt_const.mul (hK z hz))) (hI z hz)
    have hl' := besselResidual_linear ν 1 1 A (hp z hz) (hK z hz)
    simp only [one_mul] at hl hl'
    change besselResidual ν 1 (fun w=>(p w+A*besselK ν w)+B*besselI ν w) z=_
    rw [hl,hl',hKo z hz,hIo z hz]
    ring

/-- General analytic solutions on the principal slit plane; numerical stability is not asserted. -/
@[dlmf 11.2.E16]
theorem struve_general_solution_16 (ν : ℂ) (f : ℂ → ℂ) :
    IsStruveSolutionOn ν true f slitPlane ↔ ∃ A B : ℂ, ∀ z ∈ slitPlane, f z = struveL ν z + A*besselK ν z + B*besselI ν z := by
  rw [← modified_bessel_inhomogeneous_general_solution ν (struve_analytic ν).2]
  unfold IsStruveSolutionOn
  apply and_congr_right
  intro _
  apply forall_congr'
  intro z
  apply forall_congr'
  intro hz
  have hp := struveL_ode ν hz
  unfold struveEquation at hp ⊢
  simp only [↓reduceIte] at hp ⊢
  unfold besselResidual
  constructor
  · intro hf
    linear_combination (norm := (field_simp [slitPlane_ne_zero hz]; ring)) z^2*(hf-hp)
  · intro hf
    linear_combination (norm := (field_simp [slitPlane_ne_zero hz]; ring)) hf/z^2+hp

/-- General analytic solutions on the principal slit plane; numerical stability is not asserted. -/
@[dlmf 11.2.E17]
theorem struve_general_solution_17 (ν : ℂ) (f : ℂ → ℂ) :
    IsStruveSolutionOn ν true f slitPlane ↔ ∃ A B : ℂ, ∀ z ∈ slitPlane, f z = struveM ν z + A*besselK ν z + B*besselI ν z := by
  rw [struve_general_solution_16]
  constructor
  · rintro ⟨A,B,h⟩
    refine ⟨A,B+1,fun z hz=>?_⟩
    rw [h z hz]
    simp only [struveM]
    ring
  · rintro ⟨A,B,h⟩
    refine ⟨A,B-1,fun z hz=>?_⟩
    rw [h z hz]
    simp only [struveM]
    ring

/-- The half-integer Gamma normalization in odd-product form. -/
theorem Gamma_oddProduct (n : ℕ) :
    Gamma ((n:ℂ)+3/2)=(Real.sqrt π:ℂ)*oddProduct n/(2:ℂ)^(n+1) := by
  induction n with
  | zero =>
    have h : Gamma (1/2:ℂ)=(Real.sqrt π:ℂ) := by
      rw [Complex.Gamma_one_half_eq,Real.sqrt_eq_rpow,Complex.ofReal_cpow Real.pi_pos.le]
      norm_num
    norm_num [oddProduct,Gamma_three_halves,h]
  | succ n ih =>
    have hn : (n:ℂ)+3/2≠0 := by
      intro h; have h' := congrArg Complex.re h
      simp at h'; linarith [show (0:ℝ)≤n by positivity]
    have ho : oddProduct (n+1)=oddProduct n*(2*(n+1:ℂ)+1) := by
      simp only [oddProduct,Finset.prod_range_succ,Nat.cast_add,Nat.cast_one]
    rw [show ((n+1:ℕ):ℂ)+3/2=((n:ℂ)+3/2)+1 by push_cast; ring,Gamma_add_one _ hn,ih,ho]
    push_cast
    rw [pow_succ]
    ring

/-- Nonnegative integral orders have no argument cut. -/
theorem struveH_nat_entire (n : ℕ) : Differentiable ℂ (struveH n) := by
  have he : struveH n=fun z => (z/2)^(n+1)*struveHCore n z := by
    funext z; rw [struveH,← Nat.cast_add_one,cpow_natCast]
  rw [he]
  have hc := entire_struveHCore (n:ℂ)
  fun_prop

/-- Nonnegative integral modified orders have no argument cut. -/
theorem struveL_nat_entire (n : ℕ) : Differentiable ℂ (struveL n) := by
  have he : struveL n=fun z => (z/2)^(n+1)*struveLCore n z := by
    funext z; rw [struveL,← Nat.cast_add_one,cpow_natCast]
  rw [he]
  have hc := entire_struveLCore (n:ℂ)
  fun_prop

/-- The series with terms `(fun n : ℕ => 2/π * (-1)^n * z^(2*n+1)/(oddProduct n)^2)` converges to
`(struveH 0 z)`. -/
@[dlmf 11.2.E3]
theorem struveH_zero_order_series (z : ℂ) :
    HasSum (fun n : ℕ => 2/π * (-1)^n * z^(2*n+1)/(oddProduct n)^2) (struveH 0 z) := by
  rw [struveH,zero_add,cpow_one]
  refine ((hasSum_struveHCore 0 z).mul_left (z/2)).congr_fun fun n => ?_
  have ho : oddProduct n≠0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro k hk
    have : (0:ℝ)<2*k+1 := by positivity
    exact_mod_cast this.ne'
  have hp : (Real.sqrt π:ℂ)^2=(π:ℂ) := by exact_mod_cast Real.sq_sqrt Real.pi_pos.le
  simp only [struveCoeff,add_zero,Gamma_oddProduct]
  rw [div_pow,show 2*n=n*2 by omega,pow_mul,pow_mul,pow_succ]
  field_simp [ho]
  ring_nf
  rw [hp]

/-- The series with terms `(fun n : ℕ => 2/π * 1 * z^(2*n+1)/(oddProduct n)^2)` converges to
`(struveL 0 z)`. -/
@[dlmf 11.2.E4]
theorem struveL_zero_order_series (z : ℂ) :
    HasSum (fun n : ℕ => 2/π * 1 * z^(2*n+1)/(oddProduct n)^2) (struveL 0 z) := by
  rw [struveL,zero_add,cpow_one]
  refine ((hasSum_struveLCore 0 z).mul_left (z/2)).congr_fun fun n => ?_
  have ho : oddProduct n≠0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro k hk
    have : (0:ℝ)<2*k+1 := by positivity
    exact_mod_cast this.ne'
  have hp : (Real.sqrt π:ℂ)^2=(π:ℂ) := by exact_mod_cast Real.sq_sqrt Real.pi_pos.le
  simp only [struveCoeff,add_zero,Gamma_oddProduct]
  rw [div_pow,show 2*n=n*2 by omega,pow_mul,pow_mul,pow_succ]
  field_simp [ho]
  ring_nf
  rw [hp]

end DLMF.Struve
