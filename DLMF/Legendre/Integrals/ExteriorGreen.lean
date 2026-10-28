/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Legendre.Integrals.FerrersDiagonal

/-!
# Exterior Legendre Green identities and diagonal integrals

Green identities on the exterior half-line and uniform bounds for the corresponding diagonal
integrals.

Source references and common attribution are retained in
`DLMF.Legendre.Integrals`.
-/

@[expose] public noncomputable section

open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF

open scoped Real Topology Nat

namespace DLMF.Legendre

/-! ### Green's identity on `(1, ∞)`

Integrals of products of order-zero Legendre functions over `(1,∞)` (DLMF 14.17.18–20) are
obtained from Green's identity, the boundary variable `x = 1 + 2τ` at `1⁺` with the
logarithmic expansions DLMF 14.8.9 (`legBd_olverQ_log_isBigO`), and the power bounds
DLMF 14.8.12, 14.8.15 at `∞`. Helper names carry the prefix `legExt_`. -/
/-- Complex Green identity for two order-zero Legendre solutions on an open set. -/
theorem legExt_green {ν lam : ℂ} {f g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U)
    (ef : ∀ z ∈ U, (1-z^2)*iteratedDeriv 2 f z-2*z*deriv f z+(ν*(ν+1)-0^2/(1-z^2))*f z=0)
    (eg : ∀ z ∈ U, (1-z^2)*iteratedDeriv 2 g z-2*z*deriv g z+(lam*(lam+1)-0^2/(1-z^2))*g z=0)
    {z : ℂ} (hz : z ∈ U) :
    HasDerivAt (fun w : ℂ => (1-w^2)*(f w*deriv g w-g w*deriv f w))
      ((ν*(ν+1) - lam*(lam+1)) * (f z * g z)) z := by
  have hfz := (hf z hz).differentiableAt (hU.mem_nhds hz)
  have hgz := (hg z hz).differentiableAt (hU.mem_nhds hz)
  have hf2 := ((hf.deriv hU) z hz).differentiableAt (hU.mem_nhds hz)
  have hg2 := ((hg.deriv hU) z hz).differentiableAt (hU.mem_nhds hz)
  have e1 := ef z hz
  have e2 := eg z hz
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div, sub_zero] at e1 e2
  rw [iteratedDeriv_succ, iteratedDeriv_one] at e1 e2
  have hsq : HasDerivAt (fun w : ℂ => 1-w^2) (-(2*z)) z := by
    simpa using ((hasDerivAt_id z).pow 2).const_sub 1
  refine (hsq.mul ((hfz.hasDerivAt.mul hg2.hasDerivAt).sub
    (hgz.hasDerivAt.mul hf2.hasDerivAt))).congr_deriv ?_
  simp only [Pi.mul_apply, Pi.sub_apply]
  linear_combination (f z)*e2-(g z)*e1

/-- The domain `{z | z - 1 ∈ slitPlane}` of the Legendre functions `P_ν, 𝑸_ν`. -/
def legExtU : Set ℂ := {z : ℂ | z-1 ∈ slitPlane}

/-- The domain `legExtU = {z | z - 1 ∈ slitPlane}` is open. -/
theorem legExt_isOpen_U : IsOpen legExtU := isOpen_sub_one_mem_slitPlane

/-- Every real `x > 1` lies in `legExtU`. -/
theorem legExt_mem_U {x : ℝ} (hx : 1 < x) : (x:ℂ) ∈ legExtU := by
  show (x:ℂ) - 1 ∈ slitPlane
  exact Or.inl (by simp; linarith)

/-- Green's identity on `(1,∞)`: the improper integral of `f g` is given by the limits of the
boundary form `(λ+1) f (x g - g₁) - (ν+1) g (x f - f₁)` at `1⁺` and at `∞`. -/
theorem legExt_integral_green {f g f1 g1 : ℂ → ℂ} {ν lam B1 : ℂ}
    (hf : DifferentiableOn ℂ f legExtU) (hg : DifferentiableOn ℂ g legExtU)
    (ef : ∀ z ∈ legExtU, (1-z^2)*iteratedDeriv 2 f z-2*z*deriv f z+(ν*(ν+1)-0^2/(1-z^2))*f z=0)
    (eg : ∀ z ∈ legExtU, (1-z^2)*iteratedDeriv 2 g z-2*z*deriv g z+(lam*(lam+1)-0^2/(1-z^2))*g z=0)
    (hrf : ∀ x : ℝ, 1 < x → (1-(x:ℂ)^2)*deriv f x = (ν+1)*(x*f x - f1 x))
    (hrg : ∀ x : ℝ, 1 < x → (1-(x:ℂ)^2)*deriv g x = (lam+1)*(x*g x - g1 x))
    (hint : ∀ R : ℝ, 1 < R → IntervalIntegrable (fun x : ℝ => f x * g x) volume 1 R)
    (h1 : Tendsto (fun x : ℝ => (lam+1)*f x*(x*g x - g1 x) - (ν+1)*g x*(x*f x - f1 x))
      (𝓝[>] 1) (𝓝 B1))
    (hinf : Tendsto (fun x : ℝ => (lam+1)*f x*(x*g x - g1 x) - (ν+1)*g x*(x*f x - f1 x))
      atTop (𝓝 0))
    (hc : ν*(ν+1) - lam*(lam+1) ≠ 0) :
    HasIntegralAtTop (fun x : ℝ => f x * g x) 1 (-B1/(ν*(ν+1) - lam*(lam+1))) := by
  set c := ν*(ν+1) - lam*(lam+1) with hcdef
  set B : ℝ → ℂ := fun x => (lam+1)*f x*(x*g x - g1 x) - (ν+1)*g x*(x*f x - f1 x) with hB
  set W : ℝ → ℂ := fun y => (fun w : ℂ => (1-w^2)*(f w*deriv g w-g w*deriv f w)) (y:ℂ) with hW
  have hd : ∀ y : ℝ, 1 < y → HasDerivAt W (c * (f y * g y)) y := fun y hy =>
    (legExt_green legExt_isOpen_U hf hg ef eg (legExt_mem_U hy)).comp_ofReal
  have hWB : ∀ y : ℝ, 1 < y → W y = B y := by
    intro y hy
    simp only [hW, hB]
    linear_combination (f y) * hrg y hy - (g y) * hrf y hy
  have hI : ∀ R : ℝ, 1 < R → (∫ x in (1:ℝ)..R, f x * g x) = (B R - B1) / c := by
    intro R hR
    have ha : Tendsto W (𝓝[>] 1) (𝓝 B1) := h1.congr' (by
      filter_upwards [self_mem_nhdsWithin] with y (hy : 1 < y) using (hWB y hy).symm)
    have hb : Tendsto W (𝓝[<] R) (𝓝 (W R)) :=
      (hd R hR).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have e := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hR
      (fun y hy => hd y hy.1) ((hint R hR).const_mul c) ha hb
    rw [intervalIntegral.integral_const_mul, hWB R hR] at e
    rw [eq_div_iff hc, mul_comm, e]
  have hlim : Tendsto (fun R : ℝ => (B R - B1) / c) atTop (𝓝 ((0 - B1)/c)) :=
    (hinf.sub tendsto_const_nhds).div_const c
  rw [zero_sub] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 1] with R hR using (hI R hR).symm

/-- A function continuous on `(1,∞)` and `O(((x-1)/2)^{-1/2})` at `1⁺` is integrable on every
`[1,R]`. -/
theorem legExt_intervalIntegrable {h : ℝ → ℂ} (hc : ContinuousOn h (Ioi 1))
    (hO : h =O[𝓝[>] (1:ℝ)] (fun x : ℝ => ((x-1)/2)^(-(1/2:ℝ)))) {R : ℝ} (hR : 1 < R) :
    IntervalIntegrable h volume 1 R := by
  have hw : IntervalIntegrable (fun x : ℝ => (x-1)^(-(1/2:ℝ))) volume 1 2 := by
    have := (intervalIntegral.intervalIntegrable_rpow' (r := -(1/2:ℝ)) (by norm_num)
      (a := 0) (b := 1)).comp_sub_right 1
    norm_num at this ⊢; exact this
  have hO' : h =O[𝓝[>] (1:ℝ)] (fun x : ℝ => (x-1)^(-(1/2:ℝ))) := by
    refine hO.trans (Asymptotics.IsBigO.of_bound ((2:ℝ)^(1/2:ℝ)) ?_)
    filter_upwards [self_mem_nhdsWithin] with x (hx : 1 < x)
    have h0 : 0 ≤ x - 1 := by linarith
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by linarith) _),
      abs_of_nonneg (Real.rpow_nonneg h0 _), Real.div_rpow h0 (by norm_num),
      Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2), div_inv_eq_mul, mul_comm]
  have hmeas : StronglyMeasurableAtFilter h (𝓝[>] (1:ℝ)) volume :=
    hc.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Ioi 1
  have hwI : IntegrableAtFilter (fun x : ℝ => (x-1)^(-(1/2:ℝ))) (𝓝[>] (1:ℝ)) volume := by
    refine ⟨Ioo 1 2, Ioo_mem_nhdsGT (by norm_num), ?_⟩
    have := (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (1:ℝ) ≤ 2)).1 hw
    exact this
  obtain ⟨s, hs, hsI⟩ := hO'.integrableAtFilter hmeas hwI
  obtain ⟨u, hu, hU⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).1 hs
  simp only [mem_Ioi] at hu
  set b := min ((1+u)/2) ((1+R)/2) with hb
  have hb1 : 1 < b := lt_min (by linarith) (by linarith)
  have hbu : b < u := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hbR : b < R := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have h1 : IntervalIntegrable h volume 1 b := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hb1.le]
    exact hsI.mono_set (fun y hy => hU ⟨hy.1, lt_of_le_of_lt hy.2 hbu⟩)
  have h2 : IntervalIntegrable h volume b R := by
    refine (hc.mono ?_).intervalIntegrable
    intro y hy
    rw [uIcc_of_le hbR.le] at hy
    exact lt_of_lt_of_le hb1 hy.1
  exact h1.trans h2

/-- An expansion `f = -k ln τ + c + O(τ ln τ)` with `τ = (x-1)/2` gives `f = O(τ^{-1/4})`. -/
theorem legExt_isBigO_weight {f : ℝ → ℂ} {k c : ℂ}
    (hf : (fun x => f x + k * Real.log ((x-1)/2) - c) =O[𝓝[>] (1:ℝ)]
      (fun x : ℝ => (x-1)/2 * Real.log ((x-1)/2))) :
    f =O[𝓝[>] (1:ℝ)] (fun x : ℝ => ((x-1)/2)^(-(1/4:ℝ))) := by
  have hτ : Tendsto (fun x : ℝ => (x-1)/2) (𝓝[>] (1:ℝ)) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have h : Tendsto (fun x : ℝ => (x-1)/2) (𝓝 1) (𝓝 ((1-1)/2)) :=
        (tendsto_id.sub tendsto_const_nhds).div_const 2
      simpa using h.mono_left (nhdsWithin_le_nhds (s := Ioi 1))
    · filter_upwards [self_mem_nhdsWithin] with x (hx : 1 < x)
      simp only [mem_Ioi]; linarith
  have hev : ∀ᶠ x : ℝ in 𝓝[>] (1:ℝ), 0 < (x-1)/2 ∧ (x-1)/2 ≤ 1 := by
    filter_upwards [Ioo_mem_nhdsGT (show (1:ℝ) < 3 by norm_num)] with x hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hone : (fun _ : ℝ => (1:ℝ)) =O[𝓝[>] (1:ℝ)] (fun x : ℝ => ((x-1)/2)^(-(1/4:ℝ))) := by
    refine Asymptotics.IsBigO.of_bound 1 ?_
    filter_upwards [hev] with x hx
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_one, one_mul,
      abs_of_pos (Real.rpow_pos_of_pos hx.1 _)]
    exact legPI_rpow_ge_one hx.1 hx.2
  have hlog : (fun x : ℝ => Real.log ((x-1)/2)) =O[𝓝[>] (1:ℝ)]
      (fun x : ℝ => ((x-1)/2)^(-(1/4:ℝ))) := by
    refine Asymptotics.IsBigO.of_bound 4 ?_
    filter_upwards [hev] with x hx
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hx.1 _)]
    exact legPI_abs_log_le hx.1 hx.2
  have htl : Tendsto (fun x : ℝ => (x-1)/2 * Real.log ((x-1)/2)) (𝓝[>] (1:ℝ)) (𝓝 0) := by
    have := (Real.continuous_mul_log.tendsto 0).comp (hτ.mono_right nhdsWithin_le_nhds)
    simpa [Function.comp_def] using this
  have h1 := (hf.trans (htl.isBigO_one ℝ)).trans hone
  have h2 := (isBigO_ofReal_left.mpr hlog).const_mul_left k
  have h3 := (isBigO_const_one ℝ c (𝓝[>] (1:ℝ))).trans hone
  exact ((h1.sub h2).add h3).congr_left fun _ => by ring

/-- Product of two functions with logarithmic expansions at `1⁺` is integrable on `[1,R]`. -/
theorem legExt_intervalIntegrable_mul {f g : ℝ → ℂ} {kf cf kg cg : ℂ}
    (hfc : ContinuousOn f (Ioi 1)) (hgc : ContinuousOn g (Ioi 1))
    (hf : (fun x => f x + kf * Real.log ((x-1)/2) - cf) =O[𝓝[>] (1:ℝ)]
      (fun x : ℝ => (x-1)/2 * Real.log ((x-1)/2)))
    (hg : (fun x => g x + kg * Real.log ((x-1)/2) - cg) =O[𝓝[>] (1:ℝ)]
      (fun x : ℝ => (x-1)/2 * Real.log ((x-1)/2))) {R : ℝ} (hR : 1 < R) :
    IntervalIntegrable (fun x => f x * g x) volume 1 R := by
  refine legExt_intervalIntegrable (hfc.mul hgc) (((legExt_isBigO_weight hf).mul
    (legExt_isBigO_weight hg)).congr' (EventuallyEq.refl _ _) ?_) hR
  filter_upwards [self_mem_nhdsWithin] with x (hx : 1 < x)
  rw [← Real.rpow_add (by linarith)]; norm_num

/-- The polynomial remainder in the boundary form at `1⁺` (`x = 1 + 2τ`). -/
def legExtR (kf kg cf cg rf rg n l : ℂ) (v : Fin 11 → ℂ) : ℂ :=
  (2*kf*kg*l - 2*kf*kg*n)*v 2 +
    (-2*kg*l + 2*kg*n)*v 7*v 0 +
    (-2*kf*l + 2*kf*n)*v 8*v 0 +
    (-2*cf*kg*l + 2*cf*kg*n - 2*cg*kf*l + 2*cg*kf*n)*v 1 +
    (2*l - 2*n)*v 3*v 4*v 0 +
    (2*cg*l - 2*cg*n)*v 3*v 0 +
    (2*cf*l - 2*cf*n)*v 4*v 0 +
    (2*cf*cg*l - 2*cf*cg*n)*v 0 +
    (kg*n + kg)*v 7 +
    (-kf*l - kf)*v 8 +
    (kf*l + kf)*v 9 +
    (-kg*n - kg)*v 10 +
    (l - n)*v 3*v 4 +
    (-l - 1)*v 3*v 5 +
    (-cg*n - cg - l*rg - rg)*v 3 +
    (n + 1)*v 4*v 6 +
    (cf*l + cf + n*rf + rf)*v 4 +
    (-cf*l - cf)*v 5 +
    (cg*n + cg)*v 6

/-- The boundary-form remainder `legExtR kf kg cf cg rf rg n l` is continuous in `v`. -/
theorem legExt_continuous_R (kf kg cf cg rf rg n l : ℂ) : Continuous (legExtR kf kg cf cg rf rg n l) := by
  unfold legExtR; fun_prop

/-- Limit of the Green boundary form at an endpoint `x = 1 + 2τ`, `τ → 0⁺`, for expansions
`f = -k_f ln τ + c_f + O(τ ln τ)` with `k_{f₁} = k_f`, `c_{f₁} = c_f + r_f`, `(ν+1) r_f = -2 k_f`. -/
theorem legExt_bdry {l : Filter ℝ} {τ : ℝ → ℝ} (hτ : Tendsto τ l (𝓝[>] 0))
    (hx : ∀ᶠ x : ℝ in l, (x:ℂ) = 1 + 2*τ x) {f g g1 f1 : ℝ → ℂ} {ν lam kf kg cf cg rf rg : ℂ}
    (hf : (fun x => f x + kf * Real.log (τ x) - cf) =O[l] (fun x => τ x * Real.log (τ x)))
    (hg : (fun x => g x + kg * Real.log (τ x) - cg) =O[l] (fun x => τ x * Real.log (τ x)))
    (hg1 : (fun x => g1 x + kg * Real.log (τ x) - (cg + rg)) =O[l]
      (fun x => τ x * Real.log (τ x)))
    (hf1 : (fun x => f1 x + kf * Real.log (τ x) - (cf + rf)) =O[l]
      (fun x => τ x * Real.log (τ x)))
    (hrg : (lam+1)*rg = -2*kg) (hrf : (ν+1)*rf = -2*kf) :
    Tendsto (fun x : ℝ => (lam+1)*f x*(x*g x - g1 x) - (ν+1)*g x*(x*f x - f1 x)) l
      (𝓝 (2*(kg*cf - kf*cg))) := by
  obtain ⟨cT, cTU, cTUU, -, -⟩ := legPI_basic_limits hτ
  obtain ⟨c1, d1⟩ := legPI_err_limits hτ hf
  obtain ⟨c2, d2⟩ := legPI_err_limits hτ hg
  obtain ⟨c3, d3⟩ := legPI_err_limits hτ hg1
  obtain ⟨c4, d4⟩ := legPI_err_limits hτ hf1
  set U : ℝ → ℂ := fun x => ((Real.log (τ x) : ℝ) : ℂ) with hU
  set V : ℝ → Fin 11 → ℂ := fun x => ![(τ x : ℂ), (τ x : ℂ) * U x, (τ x : ℂ) * U x * U x,
    f x + kf * U x - cf, g x + kg * U x - cg, g1 x + kg * U x - (cg + rg),
    f1 x + kf * U x - (cf + rf), U x * (f x + kf * U x - cf), U x * (g x + kg * U x - cg),
    U x * (g1 x + kg * U x - (cg + rg)), U x * (f1 x + kf * U x - (cf + rf))] with hV
  have cV : Tendsto V l (𝓝 0) := by
    refine tendsto_pi_nhds.2 fun i => ?_
    fin_cases i
    · exact cT
    · exact cTU
    · exact cTUU
    · exact c1
    · exact c2
    · exact c3
    · exact c4
    · exact d1
    · exact d2
    · exact d3
    · exact d4
  have cR := ((legExt_continuous_R kf kg cf cg rf rg ν lam).tendsto 0).comp cV
  have hR0 : legExtR kf kg cf cg rf rg ν lam 0 = 0 := by simp [legExtR]
  rw [hR0] at cR
  have key := (tendsto_const_nhds (x := 2*(kg*cf - kf*cg))).add cR
  rw [add_zero] at key
  refine key.congr' ?_
  filter_upwards [hx] with x hx
  simp only [Function.comp_apply, hV, legExtR, Matrix.cons_val, hU]
  rw [hx]
  linear_combination (cf - kf*U x) * hrg - (cg - kg*U x) * hrf

/-- The map `x ↦ (x-1)/2` sends `x → 1⁺` to `τ → 0⁺`. -/
theorem legExt_tendsto_half :
    Tendsto (fun x : ℝ => (x-1)/2) (𝓝[>] (1:ℝ)) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · have h : Tendsto (fun x : ℝ => (x-1)/2) (𝓝 1) (𝓝 ((1-1)/2)) :=
      (tendsto_id.sub tendsto_const_nhds).div_const 2
    simpa using h.mono_left (nhdsWithin_le_nhds (s := Ioi 1))
  · filter_upwards [self_mem_nhdsWithin] with x (hx : 1 < x)
    simp only [mem_Ioi]; linarith

/-- The identity `x = 1 + 2·((x-1)/2)` (as complex numbers), stated eventually as `x → 1⁺`. -/
theorem legExt_hx : ∀ᶠ x : ℝ in 𝓝[>] (1:ℝ), (x:ℂ) = 1 + 2*(((x-1)/2 : ℝ) : ℂ) :=
  Eventually.of_forall fun x => by push_cast; ring

/-- `(x-1) ln(x-1) = O(τ ln τ)` with `τ = (x-1)/2`, as `x → 1⁺`. -/
theorem legExt_sub_one_log_isBigO :
    (fun x : ℝ => (x-1)*Real.log (x-1)) =O[𝓝[>] (1:ℝ)] (fun x => (x-1)/2 * Real.log ((x-1)/2)) := by
  refine Asymptotics.IsBigO.of_bound 4 ?_
  filter_upwards [Ioo_mem_nhdsGT (show (1:ℝ) < 2 by norm_num)] with x hx
  have ht0 : 0 < (x-1)/2 := by linarith [hx.1]
  have ht1 : (x-1)/2 ≤ 1/2 := by linarith [hx.2]
  have hl2 : Real.log 2 ≤ |Real.log ((x-1)/2)| := by
    rw [abs_of_nonpos (Real.log_nonpos ht0.le (by linarith)), ← Real.log_inv]
    exact Real.log_le_log (by norm_num) (by rw [le_inv_comm₀ (by norm_num) ht0]; linarith)
  have hL : (x-1)*Real.log (x-1) = 2*((x-1)/2)*(Real.log 2 + Real.log ((x-1)/2)) := by
    rw [← Real.log_mul (by norm_num) ht0.ne']; ring_nf
  rw [Real.norm_eq_abs, Real.norm_eq_abs, hL, abs_mul, abs_mul, abs_mul, abs_of_pos ht0, abs_two]
  have h2 : |Real.log 2 + Real.log ((x-1)/2)| ≤ 2 * |Real.log ((x-1)/2)| := by
    calc _ ≤ |Real.log 2| + |Real.log ((x-1)/2)| := abs_add_le _ _
      _ ≤ _ := by rw [abs_of_pos (Real.log_pos (by norm_num))]; linarith
  have := mul_le_mul_of_nonneg_left h2 (by positivity : (0:ℝ) ≤ 2*((x-1)/2))
  linarith

/-- `P_α(z) = 𝐅(α+1,-α;1;(1-z)/2)` for every `z`. -/
theorem legExt_associatedP_eq (α z : ℂ) :
    associatedP α 0 z = regularizedGaussHG (α+1) (-α) 1 ((1-z)/2) := by
  simp [associatedP]

/-- `P_α - 1 = O(τ ln τ)` with `τ = (x-1)/2`, as `x → 1⁺`. -/
theorem legExt_P_isBigO (α : ℂ) :
    (fun x : ℝ => associatedP α 0 x + (0:ℂ) * Real.log ((x-1)/2) - 1) =O[𝓝[>] (1:ℝ)]
      (fun x => (x-1)/2 * Real.log ((x-1)/2)) := by
  have hfun : (fun y : ℝ => associatedP α 0 y) =
      fun y : ℝ => regularizedGaussHG (α+1) (-α) 1 ((1-(y:ℂ))/2) :=
    funext fun y => legExt_associatedP_eq α y
  have hw : ((1-((1:ℝ):ℂ))/2) ∈ cutPlane := by simpa using zero_mem_cutPlane
  have hd : DifferentiableAt ℝ (fun y : ℝ => associatedP α 0 y) 1 := by
    rw [hfun]
    exact ((differentiableAt_regularizedGaussHG _ _ _ hw).restrictScalars ℝ).comp (1:ℝ)
      (by fun_prop)
  have h1 := hd.isBigO_sub.mono (nhdsWithin_le_nhds (s := Ioi (1:ℝ)))
  have hv : associatedP α 0 ((1:ℝ):ℂ) = 1 := by
    rw [legExt_associatedP_eq]; simp [regularizedGaussHG_at_zero]
  simp only [hv] at h1
  have h2 : (fun x : ℝ => x - 1) =O[𝓝[>] (1:ℝ)] (fun x : ℝ => (((x-1)/2 : ℝ) : ℂ)) := by
    refine Asymptotics.IsBigO.of_bound 2 (Eventually.of_forall fun x => ?_)
    rw [Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_div, abs_two]
    linarith [abs_nonneg (x-1)]
  have h3 := legBd_isBigO_self_mul_log.comp_tendsto legExt_tendsto_half
  refine (h1.trans (h2.trans h3)).congr_left fun x => ?_
  ring

/-- DLMF 14.8.9 in the variable `τ = (x-1)/2`: `Q_α + ½ ln τ - (-γ - ψ(α+1)) = O(τ ln τ)`. -/
theorem legExt_Q_isBigO {α : ℂ} (h : LegendreQRegular α 0) :
    (fun x : ℝ => associatedQ α 0 x + (1/2:ℂ) * Real.log ((x-1)/2) - legPIcpos α)
      =O[𝓝[>] (1:ℝ)] (fun x => (x-1)/2 * Real.log ((x-1)/2)) := by
  have hp := legHyp_nu h
  have hG : Gamma (α+1) ≠ 0 := Gamma_ne_zero hp
  refine (((legBd_olverQ_log_isBigO α).const_mul_left (Gamma (α+1))).trans
    legExt_sub_one_log_isBigO).congr' ?_ (EventuallyEq.refl _ _)
  filter_upwards [self_mem_nhdsWithin] with x (hx : 1 < x)
  have h1 : (0:ℝ) < x - 1 := by linarith
  have hl : log ((x:ℂ)-1) = ((Real.log (x-1) : ℝ) : ℂ) := by
    rw [show (x:ℂ)-1 = ((x-1:ℝ):ℂ) by push_cast; rfl, ofReal_log h1.le]
  have hl2 : Real.log ((x-1)/2) = Real.log (x-1) - Real.log 2 :=
    Real.log_div h1.ne' (by norm_num)
  have h2 : log (2:ℂ) = ((Real.log 2 : ℝ) : ℂ) := by
    rw [ofReal_log (by norm_num : (0:ℝ) ≤ 2)]; norm_num
  rw [DLMF.Gamma.recipGammaDeriv_one_eq hp, hl, hl2, h2]
  simp only [associatedQ, zero_mul, Complex.exp_zero, one_mul, legPIcpos]
  push_cast
  field_simp
  ring_nf

/-- Expansion of `P_{α+1}` at `1⁺` in the shape required by `legExt_bdry`. -/
theorem legExt_P_isBigO_succ (α : ℂ) :
    (fun x : ℝ => associatedP (α+1) 0 x + (0:ℂ) * Real.log ((x-1)/2) - (1 + 0)) =O[𝓝[>] (1:ℝ)]
      (fun x => (x-1)/2 * Real.log ((x-1)/2)) :=
  (legExt_P_isBigO (α+1)).congr_left fun x => by ring

/-- Expansion of `Q_{α+1}` at `1⁺` in the shape required by `legExt_bdry`. -/
theorem legExt_Q_isBigO_succ {α : ℂ} (h : LegendreQRegular α 0) :
    (fun x : ℝ => associatedQ (α+1) 0 x + (1/2:ℂ) * Real.log ((x-1)/2) -
      (legPIcpos α + (legPIcpos (α+1) - legPIcpos α))) =O[𝓝[>] (1:ℝ)]
      (fun x => (x-1)/2 * Real.log ((x-1)/2)) :=
  (legExt_Q_isBigO (legPI_regular_succ h)).congr_left fun x => by ring

/-- `𝑸_ν(x) = O(x^{-Re ν - 1})` as `x → ∞`, for every degree `ν`. -/
theorem legExt_olverQ_isBigO_atTop (ν : ℂ) :
    (fun x : ℝ => olverQ ν 0 x) =O[atTop] (fun x : ℝ => x^(-(ν.re+1))) := by
  set G := regularizedGaussHG ((ν+0+2)/2) ((ν+0+1)/2) (ν+3/2)
  have hG : Tendsto (fun x : ℝ => G (1/(x:ℂ)^2)) atTop (𝓝 (G 0)) :=
    (analyticAt_regularizedGaussHG _ _ _ zero_mem_cutPlane).continuousAt.tendsto.comp
      tendsto_one_div_sq_atTop
  have hG1 := hG.isBigO_one ℝ
  have hP : (fun x : ℝ => ((x:ℂ)^(ν+1))⁻¹) =O[atTop] (fun x : ℝ => x^(-(ν.re+1))) := by
    refine Asymptotics.IsBigO.of_bound 1 ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    rw [norm_inv, norm_cpow_eq_rpow_re_of_pos hx, Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos hx _), one_mul, Real.rpow_neg hx.le]
    simp
  have := (hP.mul hG1).const_mul_left ((Real.sqrt π : ℂ) / 2^(ν+1))
  refine (this.congr' ?_ (by filter_upwards with x; simp)).trans (isBigO_refl _ _)
  filter_upwards [eventually_gt_atTop 0] with x hx
  simp only [olverQ, legendreBranchPower, zero_div, zero_mul, Complex.exp_zero, mul_one, add_zero, G]
  have hx0 : (x:ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have hxn : (x:ℂ)^(ν+1) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hx0)
  have h2n : (2:ℂ)^(ν+1) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl two_ne_zero)
  field_simp

/-- `P_ν(x) = O(x^{Re ν})` as `x → ∞`, when `Re ν > -1/2`. -/
theorem legExt_associatedP_isBigO_atTop {ν : ℂ} (hν : -1/2 < ν.re) :
    (fun x : ℝ => associatedP ν 0 x) =O[atTop] (fun x : ℝ => x^(ν.re)) := by
  have h1 := (legBd_associatedP_tendsto_atTop hν 0).isBigO_one ℝ
  have hP : (fun x : ℝ => (x:ℂ)^ν) =O[atTop] (fun x : ℝ => x^(ν.re)) := by
    refine Asymptotics.IsBigO.of_bound 1 ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    rw [norm_cpow_eq_rpow_re_of_pos hx, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hx _),
      one_mul]
  refine ((hP.mul h1).congr' ?_ (by filter_upwards with x; simp))
  filter_upwards [eventually_gt_atTop 0] with x hx
  have hx0 : (x:ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  rw [← mul_assoc, ← cpow_add _ _ hx0]; simp

/-- The Green boundary form tends to `0` at `∞` under power bounds with `a < b`. -/
theorem legExt_tendsto_zero_atTop {f g f1 g1 : ℝ → ℂ} {ν lam : ℂ} {a b : ℝ} (hab : a < b)
    (hf : f =O[atTop] (fun x : ℝ => x^a)) (hf1 : f1 =O[atTop] (fun x : ℝ => x^(a+1)))
    (hg : g =O[atTop] (fun x : ℝ => x^(-b-1))) (hg1 : g1 =O[atTop] (fun x : ℝ => x^(-b-1))) :
    Tendsto (fun x : ℝ => (lam+1)*f x*(x*g x - g1 x) - (ν+1)*g x*(x*f x - f1 x)) atTop
      (𝓝 0) := by
  have hX : (fun x : ℝ => (x:ℂ)) =O[atTop] (fun x : ℝ => x^(1:ℝ)) := by
    refine Asymptotics.IsBigO.of_bound 1 ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    simp [abs_of_pos hx]
  have hone : (fun _ : ℝ => (1:ℂ)) =O[atTop] (fun x : ℝ => x^(1:ℝ)) := by
    refine Asymptotics.IsBigO.of_bound 1 ?_
    filter_upwards [eventually_ge_atTop 1] with x hx
    simp [abs_of_pos (show (0:ℝ) < x by linarith), hx]
  have hT : Tendsto (fun x : ℝ => x^(a-b)) atTop (𝓝 0) := by
    simpa using tendsto_rpow_neg_atTop (y := b - a) (by linarith)
  have hE : ∀ p q : ℝ, p + q = a - b → ∀ u v : ℝ → ℂ, u =O[atTop] (fun x : ℝ => x^p) →
      v =O[atTop] (fun x : ℝ => x^q) → Tendsto (fun x => u x * v x) atTop (𝓝 0) := by
    intro p q hpq u v hu hv
    refine ((hu.mul hv).congr' (EventuallyEq.refl _ _) ?_).trans_tendsto hT
    filter_upwards [eventually_gt_atTop 0] with x hx
    rw [← Real.rpow_add hx, hpq]
  have t1 := hE (a) (1 + (-b-1)) (by ring) f (fun x => (x:ℂ) * g x) hf
    ((hX.mul hg).congr' (EventuallyEq.refl _ _) (by
      filter_upwards [eventually_gt_atTop 0] with x hx; rw [← Real.rpow_add hx]))
  have t2 := hE a (1 + (-b-1)) (by ring) f g1 hf (((hone.mul hg1).congr' (by
      filter_upwards with x; simp) (by
      filter_upwards [eventually_gt_atTop 0] with x hx; rw [← Real.rpow_add hx])))
  have t3 := hE (-b-1) (1 + a) (by ring) g (fun x => (x:ℂ) * f x) hg
    ((hX.mul hf).congr' (EventuallyEq.refl _ _) (by
      filter_upwards [eventually_gt_atTop 0] with x hx; rw [← Real.rpow_add hx]))
  have t4 := hE (-b-1) (a+1) (by ring) g f1 hg hf1
  have := ((t1.sub t2).const_mul (lam+1)).sub ((t3.sub t4).const_mul (ν+1))
  simp only [mul_zero, sub_zero] at this
  refine this.congr fun x => ?_
  ring

/-- `𝑸_ν = Γ(ν+1) 𝑸_ν` at order zero. -/
theorem legExt_associatedQ_eq (α : ℂ) :
    associatedQ α 0 = fun z => Gamma (α+1) * olverQ α 0 z := by
  funext z; simp [associatedQ]

/-- The Legendre function `associatedP α 0` is complex differentiable on `legExtU`. -/
theorem legExt_differentiableOn_P (α : ℂ) : DifferentiableOn ℂ (associatedP α 0) legExtU :=
  (associatedP_analytic α 0).differentiableOn

/-- The Legendre function `associatedQ α 0` is complex differentiable on `legExtU`. -/
theorem legExt_differentiableOn_Q (α : ℂ) : DifferentiableOn ℂ (associatedQ α 0) legExtU := by
  rw [legExt_associatedQ_eq]
  exact (olverQ_analytic α 0).differentiableOn.const_mul _

/-- On `legExtU`, `P_α = associatedP α 0` satisfies Legendre's equation `(1-z²)w'' - 2z w' + α(α+1)
w = 0`. -/
theorem legExt_ode_P (α : ℂ) : ∀ z ∈ legExtU, (1-z^2)*iteratedDeriv 2 (associatedP α 0) z -
    2*z*deriv (associatedP α 0) z + (α*(α+1)-0^2/(1-z^2))*associatedP α 0 z = 0 :=
  fun _ hz => associatedP_ode α 0 hz

/-- On `legExtU`, `Q_α = associatedQ α 0` satisfies Legendre's equation `(1-z²)w'' - 2z w' + α(α+1)
w = 0`. -/
theorem legExt_ode_Q (α : ℂ) : ∀ z ∈ legExtU, (1-z^2)*iteratedDeriv 2 (associatedQ α 0) z -
    2*z*deriv (associatedQ α 0) z + (α*(α+1)-0^2/(1-z^2))*associatedQ α 0 z = 0 := by
  intro z hz
  have e := olverQ_ode α 0 hz
  rw [legExt_associatedQ_eq, iteratedDeriv_const_mul_field, deriv_const_mul_field]
  linear_combination Gamma (α+1) * e

/-- For real `x > 1`, `(1-x²) P_α'(x) = (α+1)(x P_α(x) - P_{α+1}(x))` (`μ = 0` case of DLMF
14.10.5). -/
theorem legExt_rec_P (α : ℂ) : ∀ x : ℝ, 1 < x →
    (1-(x:ℂ)^2)*deriv (associatedP α 0) x = (α+1)*(x*associatedP α 0 x - associatedP (α+1) 0 x) :=
  fun x hx => by rw [associatedP_recurrence_4 α 0 (legExt_mem_U hx)]; ring

/-- For `LegendreQRegular α 0` and real `x > 1`, `(1-x²) Q_α'(x) = (α+1)(x Q_α(x) - Q_{α+1}(x))` (`μ
= 0` case of DLMF 14.10.5). -/
theorem legExt_rec_Q {α : ℂ} (h : LegendreQRegular α 0) : ∀ x : ℝ, 1 < x →
    (1-(x:ℂ)^2)*deriv (associatedQ α 0) x = (α+1)*(x*associatedQ α 0 x - associatedQ (α+1) 0 x) :=
  fun x hx => by rw [associatedQ_recurrence_4 α 0 h (legExt_mem_U hx)]; ring

/-- If `f` is complex differentiable on `legExtU`, then `x ↦ f x` is continuous on `(1, ∞)`. -/
theorem legExt_continuousOn {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f legExtU) :
    ContinuousOn (fun x : ℝ => f x) (Ioi 1) := fun _ hx =>
  ((hf _ (legExt_mem_U hx)).differentiableAt (legExt_isOpen_U.mem_nhds (legExt_mem_U hx))
    ).continuousAt.comp_of_eq continuous_ofReal.continuousAt rfl |>.continuousWithinAt

/-- `Q_ν(x) = O(x^{-Re ν - 1})` as `x → ∞`. -/
theorem legExt_associatedQ_isBigO_atTop (α : ℂ) :
    (fun x : ℝ => associatedQ α 0 x) =O[atTop] (fun x : ℝ => x^(-α.re-1)) := by
  rw [legExt_associatedQ_eq]
  exact ((legExt_olverQ_isBigO_atTop α).const_mul_left _).congr' (EventuallyEq.refl _ _)
    (by filter_upwards with x; ring_nf)

/-- Lowering the exponent of a power bound at `∞`. -/
theorem legExt_isBigO_rpow_mono {f : ℝ → ℂ} {p q : ℝ} (hpq : p ≤ q)
    (h : f =O[atTop] (fun x : ℝ => x^p)) : f =O[atTop] (fun x : ℝ => x^q) := by
  refine h.trans (Asymptotics.IsBigO.of_bound 1 ?_)
  filter_upwards [eventually_ge_atTop 1] with x hx
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos (by linarith) _),
    abs_of_pos (Real.rpow_pos_of_pos (by linarith) _), one_mul]
  exact Real.rpow_le_rpow_of_exponent_le hx hpq

/-! ### Uniform bounds on `(1,∞)` and the diagonal integral 14.17.20 -/

/-- `𝑄_λ(x) = Γ(λ+1) √π 2^{-λ-1} x^{-λ-1} 𝐅(λ/2+1, λ/2+1/2; λ+3/2; x^{-2})` for `x > 0`. -/
theorem legPIU_associatedQ_ext (lam : ℂ) {x : ℝ} (hx0 : 0 < x) :
    associatedQ lam 0 x = Gamma (lam+1) * ((Real.sqrt π : ℂ) * ((2:ℂ)^(lam+1))⁻¹ *
      ((x:ℂ)^(lam+1))⁻¹ * regularizedGaussHG ((lam+0+2)/2) ((lam+0+1)/2) (lam+3/2) (1/(x:ℂ)^2)) := by
  simp only [associatedQ, olverQ, legendreBranchPower, zero_div, zero_mul, Complex.exp_zero,
    mul_one, add_zero, one_mul]
  have hx0' : (x:ℂ) ≠ 0 := ofReal_ne_zero.mpr hx0.ne'
  have hxn : (x:ℂ)^(lam+1) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hx0')
  have h2n : (2:ℂ)^(lam+1) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl two_ne_zero)
  field_simp

/-- `𝐅(a,b;a+b;y)` is `O((1-y)^{-1/4})` on `[0,1)`, uniformly for `‖a‖, ‖b‖ ≤ R`. -/
theorem legPIU_bound_real (R : ℝ) : ∃ M : ℝ, 0 ≤ M ∧ ∀ a b : ℂ, ‖a‖ ≤ R → ‖b‖ ≤ R → ∀ y : ℝ, 0 ≤ y →
    y < 1 → ‖regularizedGaussHG a b (a+b) (y:ℂ)‖ ≤ M * (1-y)^(-(1/4:ℝ)) := by
  obtain ⟨C, hC0, hC⟩ := legPIU_bound_zb R
  obtain ⟨MF, hMF⟩ := legPIU_bound_F (2*|R| + 1)
  refine ⟨max MF 0 + C, by positivity, fun a b ha hb y hy0 hy1 => ?_⟩
  have hR1 : R ≤ |R| := le_abs_self R
  have hp : 1 ≤ (1-y)^(-(1/4:ℝ)) := legPI_rpow_ge_one (by linarith) (by linarith)
  have hn : ‖(y:ℂ)‖ < 1 := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hy0]; exact hy1
  rw [regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hn]
  by_cases hyh : y ≤ 1/2
  · have hn' : ‖(y:ℂ)‖ ≤ 1/2 := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hy0]; exact hyh
    have hab : ‖a+b‖ ≤ 2*|R|+1 := by
      calc ‖a+b‖ ≤ ‖a‖+‖b‖ := norm_add_le _ _
        _ ≤ 2*|R|+1 := by linarith
    calc _ ≤ MF := hMF _ _ _ _ (by linarith [abs_nonneg R]) (by linarith [abs_nonneg R]) hab hn'
      _ ≤ max MF 0 + C := by linarith [le_max_left MF 0]
      _ ≤ (max MF 0 + C) * (1-y)^(-(1/4:ℝ)) :=
          le_mul_of_one_le_right (by linarith [le_max_right MF 0]) hp
  · push Not at hyh
    have h := hC a b ha hb (1-y) (by linarith) (by linarith)
    rw [show (1:ℂ) - ((1-y:ℝ):ℂ) = (y:ℂ) by push_cast; ring] at h
    have := Real.rpow_nonneg (show (0:ℝ) ≤ 1-y by linarith) (-(1/4:ℝ))
    nlinarith [le_max_right MF 0]

/-- Uniform bound on `(1,∞)`: `‖𝑄_λ(x)‖ ≤ M (x-1)^{-1/4} x^{-(Re ν - r) - 3/4}` for `λ` near a
regular `ν`, with `r ≤ r₀` prescribed. -/
theorem legPIU_bound_Qext {ν : ℂ} (hν : LegendreQRegular ν 0) {r0 : ℝ} (hr0 : 0 < r0) :
    ∃ r : ℝ, 0 < r ∧ r ≤ r0 ∧ ∃ M : ℝ, 0 ≤ M ∧
    ∀ lam : ℂ, ‖lam - ν‖ ≤ r → LegendreQRegular lam 0 ∧ ∀ x : ℝ, 1 < x →
      ‖associatedQ lam 0 x‖ ≤ M * ((x-1)^(-(1/4:ℝ)) * x^(-(ν.re-r)-3/4)) := by
  have hν1 := legHyp_nu hν
  have o : IsOpen {lam : ℂ | (Gamma (lam+0+1))⁻¹ ≠ 0} :=
    isOpen_ne_fun (continuous_recip_Gamma.comp (by fun_prop)) continuous_const
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp o ν (by simpa using inv_ne_zero (Gamma_ne_zero hν1))
  set r := min (ε/2) r0
  have hr : 0 < r := lt_min (by positivity) hr0
  set K := Metric.closedBall ν r
  have hK : IsCompact K := isCompact_closedBall _ _
  have hreg : ∀ lam ∈ K, LegendreQRegular lam 0 := fun lam hl => legHyp_regular_of_recip (hball (by
    rw [Metric.mem_ball]; have := Metric.mem_closedBall.mp hl
    have : r ≤ ε/2 := min_le_left _ _; linarith))
  obtain ⟨B1, hB10, hB1⟩ := legPIU_bound_on (f := fun lam : ℂ => Gamma (lam+1)) hK
    (fun lam hl => (ContinuousAt.comp (g := Gamma) (f := fun l : ℂ => l + 1)
      (differentiableAt_Gamma _ (by simpa using legHyp_nu (hreg lam hl))).continuousAt
      (by fun_prop)).continuousWithinAt)
  obtain ⟨B2, hB20, hB2⟩ := legPIU_bound_on (f := fun lam : ℂ => ((2:ℂ)^(lam+1))⁻¹) hK
    ((continuous_const_cpow' two_ne_zero |>.comp (continuous_id.add continuous_const)).inv₀
      (fun lam => cpow_ne_zero_iff.mpr (Or.inl two_ne_zero))).continuousOn
  obtain ⟨MS, hMS0, hMS⟩ := legPIU_bound_real (‖ν‖ + r + 2)
  refine ⟨r, hr, min_le_right _ _, Real.sqrt π * B1 * B2 * MS, by positivity, fun lam hl => ?_⟩
  have hlK : lam ∈ K := Metric.mem_closedBall.mpr (by rw [dist_eq_norm]; exact hl)
  refine ⟨hreg lam hlK, fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  have hlam : ‖lam‖ ≤ ‖ν‖ + r := by
    calc ‖lam‖ = ‖ν + (lam - ν)‖ := by ring_nf
      _ ≤ ‖ν‖ + ‖lam - ν‖ := norm_add_le _ _
      _ ≤ _ := by linarith
  have hre : ν.re - r ≤ lam.re := by
    have := Complex.abs_re_le_norm (lam - ν)
    rw [sub_re] at this
    linarith [abs_le.mp (le_trans this hl)]
  have hy0 : (0:ℝ) ≤ 1/x^2 := by positivity
  have hy1 : 1/x^2 < 1 := by rw [div_lt_one (by positivity)]; nlinarith
  have hF := hMS ((lam+0+2)/2) ((lam+0+1)/2) ?_ ?_ (1/x^2) hy0 hy1
  rotate_left
  · calc ‖(lam+0+2)/2‖ ≤ ‖lam+0+2‖ := by rw [norm_div]; exact div_le_self (norm_nonneg _) (by simp)
      _ ≤ ‖lam‖ + 2 := by simpa using norm_add_le lam 2
      _ ≤ _ := by linarith
  · calc ‖(lam+0+1)/2‖ ≤ ‖lam+0+1‖ := by rw [norm_div]; exact div_le_self (norm_nonneg _) (by simp)
      _ ≤ ‖lam‖ + 1 := by simpa using norm_add_le lam 1
      _ ≤ _ := by linarith
  rw [show (lam+0+2)/2 + (lam+0+1)/2 = lam + 3/2 by ring,
    show ((1/x^2 : ℝ) : ℂ) = 1/(x:ℂ)^2 by push_cast; ring] at hF
  have hxp : ‖((x:ℂ)^(lam+1))⁻¹‖ ≤ x^(-(ν.re-r)-1) := by
    rw [norm_inv, norm_cpow_eq_rpow_re_of_pos hx0, ← Real.rpow_neg hx0.le]
    exact Real.rpow_le_rpow_of_exponent_le hx.le (by simp; linarith)
  -- `(1 - x^{-2})^{-1/4} x^{-σ-1} ≤ (x-1)^{-1/4} x^{-σ-3/4}`
  have hw : (1-1/x^2)^(-(1/4:ℝ)) * x^(-(ν.re-r)-1) ≤ (x-1)^(-(1/4:ℝ)) * x^(-(ν.re-r)-3/4) := by
    have h1 : (1-1/x^2)^(-(1/4:ℝ)) ≤ ((x-1)/x)^(-(1/4:ℝ)) := by
      refine Real.rpow_le_rpow_of_nonpos (div_pos (by linarith) hx0) ?_ (by norm_num)
      rw [div_le_iff₀ hx0]; field_simp; nlinarith
    have h2 : ((x-1)/x)^(-(1/4:ℝ)) * x^(-(ν.re-r)-1) = (x-1)^(-(1/4:ℝ)) * x^(-(ν.re-r)-3/4) := by
      rw [Real.div_rpow (by linarith) hx0.le, show -(ν.re-r)-3/4 = (1/4:ℝ) + (-(ν.re-r)-1) by ring,
        Real.rpow_add hx0, Real.rpow_neg hx0.le]
      field_simp
    calc _ ≤ ((x-1)/x)^(-(1/4:ℝ)) * x^(-(ν.re-r)-1) :=
          mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hx0.le _)
      _ = _ := h2
  have e1 := hB1 lam hlK
  have e2 := hB2 lam hlK
  have hsq : ‖(Real.sqrt π : ℂ)‖ = Real.sqrt π := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [legPIU_associatedQ_ext lam hx0, norm_mul, norm_mul, norm_mul, norm_mul, hsq]
  calc ‖Gamma (lam+1)‖ * (Real.sqrt π * ‖((2:ℂ)^(lam+1))⁻¹‖ * ‖((x:ℂ)^(lam+1))⁻¹‖ *
        ‖regularizedGaussHG ((lam+0+2)/2) ((lam+0+1)/2) (lam+3/2) (1/(x:ℂ)^2)‖)
      ≤ B1 * (Real.sqrt π * B2 * x^(-(ν.re-r)-1) * (MS * (1-1/x^2)^(-(1/4:ℝ)))) := by
        gcongr
    _ = Real.sqrt π * B1 * B2 * MS * ((1-1/x^2)^(-(1/4:ℝ)) * x^(-(ν.re-r)-1)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hw (by positivity)

/-- `λ ↦ 𝑄_λ(x)` is continuous at a regular `ν`, for `x > 1`. -/
theorem legPIU_continuousAt_Qext {ν : ℂ} (hν : LegendreQRegular ν 0) {x : ℝ} (hx : 1 < x) :
    ContinuousAt (fun lam : ℂ => associatedQ lam 0 x) ν := by
  have hx0 : 0 < x := by linarith
  have hx0' : (x:ℂ) ≠ 0 := ofReal_ne_zero.mpr hx0.ne'
  have heq : (fun lam : ℂ => associatedQ lam 0 x) = fun lam => Gamma (lam+1) *
      ((Real.sqrt π : ℂ) * ((2:ℂ)^(lam+1))⁻¹ * ((x:ℂ)^(lam+1))⁻¹ *
        regularizedGaussHG ((lam+0+2)/2) ((lam+0+1)/2) (lam+3/2) (1/(x:ℂ)^2)) :=
    funext fun lam => legPIU_associatedQ_ext lam hx0
  rw [heq]
  have hz : 1/(x:ℂ)^2 ∈ cutPlane := by
    refine mem_cutPlane_of_norm_lt_one ?_
    rw [norm_div, norm_one, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0,
      div_lt_one (by positivity)]
    nlinarith
  have hG := (differentiable_regularizedGaussHG_comp (A := fun lam : ℂ => (lam+0+2)/2)
    (B := fun lam : ℂ => (lam+0+1)/2) (C := fun lam : ℂ => lam+3/2) (by fun_prop) (by fun_prop)
    (by fun_prop) hz).continuous.continuousAt (x := ν)
  refine ContinuousAt.mul (ContinuousAt.comp (g := Gamma) (f := fun l : ℂ => l + 1)
      (differentiableAt_Gamma _ (by simpa using legHyp_nu hν)).continuousAt (by fun_prop)) ?_
  refine ContinuousAt.mul (ContinuousAt.mul (ContinuousAt.mul continuousAt_const ?_) ?_) hG
  · exact ((continuous_const_cpow' two_ne_zero |>.comp (continuous_id.add continuous_const)).inv₀
      (fun lam => cpow_ne_zero_iff.mpr (Or.inl two_ne_zero))).continuousAt
  · exact ((continuous_const_cpow' hx0' |>.comp (continuous_id.add continuous_const)).inv₀
      (fun lam => cpow_ne_zero_iff.mpr (Or.inl hx0'))).continuousAt

/-- `(x-1)^{-1/2} x^p` is integrable on `(1,∞)` for `p < -1/2`. -/
theorem legPIU_integrableOn_weight {p : ℝ} (hp : p < -1/2) :
    IntegrableOn (fun x : ℝ => (x-1)^(-(1/2:ℝ)) * x^p) (Ioi 1) := by
  have hw : IntervalIntegrable (fun x : ℝ => (x-1)^(-(1/2:ℝ))) volume 1 2 := by
    have := (intervalIntegral.intervalIntegrable_rpow' (r := -(1/2:ℝ)) (by norm_num)
      (a := 0) (b := 1)).comp_sub_right 1
    norm_num at this ⊢; exact this
  rw [← Ioc_union_Ioi_eq_Ioi (by norm_num : (1:ℝ) ≤ 2)]
  refine IntegrableOn.union ?_ ?_
  · have h1 : IntegrableOn (fun x : ℝ => (x-1)^(-(1/2:ℝ))) (Icc 1 2) := by
      rw [integrableOn_Icc_iff_integrableOn_Ioc]
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).1 hw
    refine (h1.mul_continuousOn ?_ isCompact_Icc).mono_set Ioc_subset_Icc_self
    exact fun x hx => (Real.continuousAt_rpow_const _ _ (Or.inl (by linarith [hx.1]))).continuousWithinAt
  · have hI := (integrableOn_Ioi_rpow_of_lt (a := p - 1/2) (by linarith) (by norm_num : (0:ℝ) < 2)).const_mul
      ((2:ℝ)^(1/2:ℝ))
    refine hI.mono' ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable (fun x (hx : 2 < x) => ?_) measurableSet_Ioi
      exact ((Real.continuousAt_rpow_const (x-1) _ (Or.inl (by linarith))).comp
        (f := fun y : ℝ => y - 1) (by fun_prop) |>.mul
        (Real.continuousAt_rpow_const _ _ (Or.inl (by linarith)))).continuousWithinAt
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun x (hx : 2 < x) => ?_)
      have hx0 : 0 < x := by linarith
      have hx1 : 0 ≤ x - 1 := by linarith
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hx1 _) (Real.rpow_nonneg hx0.le _))]
      have h1 : (x-1)^(-(1/2:ℝ)) ≤ (x/2)^(-(1/2:ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by norm_num)
      have h2 : (x/2)^(-(1/2:ℝ)) * x^p = (2:ℝ)^(1/2:ℝ) * x^(p-1/2) := by
        rw [Real.div_rpow hx0.le (by norm_num), show p - 1/2 = -(1/2:ℝ) + p by ring,
          Real.rpow_add hx0, Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
        field_simp
      calc _ ≤ (x/2)^(-(1/2:ℝ)) * x^p := mul_le_mul_of_nonneg_right h1 (by positivity)
        _ = _ := h2

/-- DLMF 14.17.18: for `Re λ > Re ν > 0`, the improper integral `∫₁^∞ P_ν(x) Q_λ(x) dx` converges
and equals `1/((λ-ν)(ν+λ+1))`. -/
@[dlmf 14.17.E18]
theorem legendre_product_integral_18 (ν : ℂ) (lam : ℂ) (hν : 0 < ν.re) (hlam : ν.re < lam.re) :
    HasIntegralAtTop (fun x : ℝ => associatedP ν 0 x*associatedQ lam 0 x) 1 (1/((lam-ν)*(ν+lam+1))) := by
  have hl0 : 0 < lam.re := by linarith
  have hr := legPI_regular_of_re_pos hl0
  have hd1 : ν - lam ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  have hd2 : ν + lam + 1 ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  have hc : ν*(ν+1) - lam*(lam+1) ≠ 0 := by
    rw [show ν*(ν+1) - lam*(lam+1) = (ν-lam)*(ν+lam+1) by ring]; exact mul_ne_zero hd1 hd2
  have hinf : Tendsto (fun x : ℝ => (lam+1)*associatedP ν 0 x*(x*associatedQ lam 0 x -
      associatedQ (lam+1) 0 x) - (ν+1)*associatedQ lam 0 x*(x*associatedP ν 0 x -
      associatedP (ν+1) 0 x)) atTop (𝓝 0) := by
    refine legExt_tendsto_zero_atTop (a := ν.re) (b := lam.re) hlam
      (legExt_associatedP_isBigO_atTop (by linarith)) ?_ (legExt_associatedQ_isBigO_atTop lam) ?_
    · have := legExt_associatedP_isBigO_atTop (ν := ν+1) (by simp; linarith)
      simpa using this
    · exact legExt_isBigO_rpow_mono (by simp) (legExt_associatedQ_isBigO_atTop (lam+1))
  have h1 := legExt_bdry (ν := ν) legExt_tendsto_half legExt_hx (legExt_P_isBigO ν) (legExt_Q_isBigO hr)
    (legExt_Q_isBigO_succ hr) (legExt_P_isBigO_succ ν)
    (by rw [legPI_cpos_succ hr]; ring) (by ring)
  have := legExt_integral_green (legExt_differentiableOn_P ν) (legExt_differentiableOn_Q lam)
    (legExt_ode_P ν) (legExt_ode_Q lam) (legExt_rec_P ν) (legExt_rec_Q hr)
    (fun R hR => legExt_intervalIntegrable_mul (legExt_continuousOn (legExt_differentiableOn_P ν))
      (legExt_continuousOn (legExt_differentiableOn_Q lam)) (legExt_P_isBigO ν)
      (legExt_Q_isBigO hr) hR) h1 hinf hc
  convert this using 1
  rw [show ν*(ν+1) - lam*(lam+1) = -((lam-ν)*(ν+lam+1)) by ring]
  have : (lam - ν) ≠ 0 := fun h => hd1 (by linear_combination -h)
  field_simp
  ring

/-- DLMF 14.17.19: for `Re(λ+ν) > -1`, `λ ≠ ν` and `ν, λ ∉ {-1,-2,…}`, the improper integral `∫₁^∞
Q_ν(x) Q_λ(x) dx` converges and equals `(ψ(λ+1) - ψ(ν+1))/((λ-ν)(λ+ν+1))`. -/
@[dlmf 14.17.E19]
theorem legendre_product_integral_19 (ν : ℂ) (lam : ℂ) (h : -1 < (lam+ν).re) (hne : lam ≠ ν) (hν : LegendreQRegular ν 0) (hlam : LegendreQRegular lam 0) :
    HasIntegralAtTop (fun x : ℝ => associatedQ ν 0 x*associatedQ lam 0 x) 1 ((digamma (lam+1)-digamma (ν+1))/((lam-ν)*(lam+ν+1))) := by
  have hd1 : lam - ν ≠ 0 := sub_ne_zero.mpr hne
  have hd2 : lam + ν + 1 ≠ 0 := fun h' => by
    have := congrArg Complex.re h'; simp at this h; linarith
  have hc : ν*(ν+1) - lam*(lam+1) ≠ 0 := by
    rw [show ν*(ν+1) - lam*(lam+1) = -((lam-ν)*(lam+ν+1)) by ring]
    exact neg_ne_zero.mpr (mul_ne_zero hd1 hd2)
  have hinf : Tendsto (fun x : ℝ => (lam+1)*associatedQ ν 0 x*(x*associatedQ lam 0 x -
      associatedQ (lam+1) 0 x) - (ν+1)*associatedQ lam 0 x*(x*associatedQ ν 0 x -
      associatedQ (ν+1) 0 x)) atTop (𝓝 0) := by
    refine legExt_tendsto_zero_atTop (a := -ν.re-1) (b := lam.re) (by simp at h; linarith)
      (legExt_associatedQ_isBigO_atTop ν) ?_ (legExt_associatedQ_isBigO_atTop lam) ?_
    · exact legExt_isBigO_rpow_mono (by simp) (legExt_associatedQ_isBigO_atTop (ν+1))
    · exact legExt_isBigO_rpow_mono (by simp) (legExt_associatedQ_isBigO_atTop (lam+1))
  have h1 := legExt_bdry (ν := ν) legExt_tendsto_half legExt_hx (legExt_Q_isBigO hν) (legExt_Q_isBigO hlam)
    (legExt_Q_isBigO_succ hlam) (legExt_Q_isBigO_succ hν)
    (by rw [legPI_cpos_succ hlam]; ring) (by rw [legPI_cpos_succ hν]; ring)
  have := legExt_integral_green (legExt_differentiableOn_Q ν) (legExt_differentiableOn_Q lam)
    (legExt_ode_Q ν) (legExt_ode_Q lam) (legExt_rec_Q hν) (legExt_rec_Q hlam)
    (fun R hR => legExt_intervalIntegrable_mul (legExt_continuousOn (legExt_differentiableOn_Q ν))
      (legExt_continuousOn (legExt_differentiableOn_Q lam)) (legExt_Q_isBigO hν)
      (legExt_Q_isBigO hlam) hR) h1 hinf hc
  convert this using 1
  rw [show ν*(ν+1) - lam*(lam+1) = -((lam-ν)*(lam+ν+1)) by ring]
  unfold legPIcpos
  field_simp
  ring

/-- DLMF 14.17.20: for `Re ν > -1/2`, the improper integral `∫₁^∞ (Q_ν(x))² dx` converges and equals
`ψ'(ν+1)/(2ν+1)`. -/
@[dlmf 14.17.E20]
theorem legendre_product_integral_20 (ν : ℂ) (hν : -1/2 < ν.re) :
    HasIntegralAtTop (fun x : ℝ => (associatedQ ν 0 x)^2) 1 (deriv digamma (ν+1)/(2*ν+1)) := by
  have hreg : LegendreQRegular ν 0 := fun n h => by
    have := congrArg Complex.re h; simp at this; linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
  have hν1 := legHyp_nu hreg
  have h2ν : 2*ν+1 ≠ 0 := fun h => by have := congrArg Complex.re h; simp at this; linarith
  obtain ⟨r, hr, hrr0, M, hM0, hM⟩ := legPIU_bound_Qext hreg (r0 := (ν.re + 1/2)/2) (by linarith)
  set q := -(ν.re - r) - 3/4
  set g : ℝ → ℝ := fun x => M^2 * ((x-1)^(-(1/2:ℝ)) * x^(2*q))
  have hgI : IntegrableOn g (Ioi (1:ℝ)) := (legPIU_integrableOn_weight (p := 2*q) (by
    simp only [q]; linarith)).const_mul _
  have hQc : ∀ lam : ℂ, ContinuousOn (fun x : ℝ => associatedQ lam 0 x) (Ioi (1:ℝ)) :=
    fun lam => legExt_continuousOn (legExt_differentiableOn_Q lam)
  have hbd : ∀ lam : ℂ, ‖lam - ν‖ ≤ r → ∀ x : ℝ, 1 < x →
      ‖associatedQ ν 0 x * associatedQ lam 0 x‖ ≤ g x := by
    intro lam hl x hx
    have h1 := (hM ν (by simp; linarith)).2 x hx
    have h2 := (hM lam hl).2 x hx
    have hx1 : 0 < x - 1 := by linarith
    have hx0 : 0 < x := by linarith
    rw [norm_mul]
    calc _ ≤ (M * ((x-1)^(-(1/4:ℝ)) * x^q)) * (M * ((x-1)^(-(1/4:ℝ)) * x^q)) :=
          mul_le_mul h1 h2 (norm_nonneg _) (le_trans (norm_nonneg _) h1)
      _ = g x := by
        simp only [g]
        rw [show (2*q) = q + q by ring, Real.rpow_add hx0,
          show (-(1/2:ℝ)) = -(1/4) + -(1/4) by norm_num, Real.rpow_add hx1]
        ring
  have hint : ∀ lam : ℂ, ‖lam - ν‖ ≤ r →
      IntegrableOn (fun x : ℝ => associatedQ ν 0 x * associatedQ lam 0 x) (Ioi (1:ℝ)) := by
    intro lam hl
    refine hgI.mono' (((hQc ν).mul (hQc lam)).aestronglyMeasurable measurableSet_Ioi) ?_
    exact (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun x hx => hbd lam hl x hx)
  have hnear : ∀ᶠ lam in 𝓝 ν, ‖lam - ν‖ ≤ r := by
    filter_upwards [Metric.closedBall_mem_nhds ν hr] with lam hl
    rwa [Metric.mem_closedBall, dist_eq_norm] at hl
  -- dominated convergence on `(1,∞)`
  have hDCT : Tendsto (fun lam : ℂ => ∫ x : ℝ in Ioi 1, associatedQ ν 0 x * associatedQ lam 0 x) (𝓝 ν)
      (𝓝 (∫ x : ℝ in Ioi 1, associatedQ ν 0 x * associatedQ ν 0 x)) := by
    refine tendsto_integral_filter_of_dominated_convergence g ?_ ?_ hgI ?_
    · exact Eventually.of_forall fun lam =>
        ((hQc ν).mul (hQc lam)).aestronglyMeasurable measurableSet_Ioi
    · filter_upwards [hnear] with lam hl
      exact (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun x hx => hbd lam hl x hx)
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun x (hx : 1 < x) => ?_)
      exact tendsto_const_nhds.mul (legPIU_continuousAt_Qext hreg hx).tendsto
  -- the off-diagonal value
  have hψ := (DLMF.Gamma.differentiableAt_digamma hν1).hasDerivAt
  have hψ' : HasDerivAt (fun lam : ℂ => digamma (lam+1)) (deriv digamma (ν+1)) ν := by
    have := hψ.comp ν ((hasDerivAt_id' ν).add_const 1)
    rw [mul_one] at this; exact this
  have hsl := hasDerivAt_iff_tendsto_slope.mp hψ'
  have hden : Tendsto (fun lam : ℂ => 1/(lam+ν+1)) (𝓝[≠] ν) (𝓝 (1/(ν+ν+1))) := by
    refine ((continuousAt_const.div ((continuousAt_id.add continuousAt_const).add
      continuousAt_const) ?_).tendsto).mono_left nhdsWithin_le_nhds
    show ν + ν + 1 ≠ 0; rw [show ν+ν+1 = 2*ν+1 by ring]; exact h2ν
  have hR := hsl.mul hden
  have hne : ∀ᶠ lam in 𝓝 ν, lam + ν + 1 ≠ 0 :=
    (show ContinuousAt (fun lam : ℂ => lam + ν + 1) ν by fun_prop).eventually_ne
      (by rw [show ν+ν+1 = 2*ν+1 by ring]; exact h2ν)
  have heq : (fun lam : ℂ => ∫ x : ℝ in Ioi 1, associatedQ ν 0 x * associatedQ lam 0 x) =ᶠ[𝓝[≠] ν]
      fun lam => slope (fun lam : ℂ => digamma (lam+1)) ν lam * (1/(lam+ν+1)) := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hnear, nhdsWithin_le_nhds hne]
      with lam (h0 : lam ≠ ν) hl h1
    have hre : ν.re - r ≤ lam.re := by
      have := Complex.abs_re_le_norm (lam - ν)
      rw [sub_re] at this
      linarith [abs_le.mp (le_trans this hl)]
    have h19 := legendre_product_integral_19 ν lam (by simp; linarith) h0 hreg (hM lam hl).1
    have hI := intervalIntegral_tendsto_integral_Ioi 1 (hint lam hl) tendsto_id
    rw [tendsto_nhds_unique hI h19, slope_def_field]
    have hd1 : lam - ν ≠ 0 := sub_ne_zero.mpr h0
    field_simp
  have hu := tendsto_nhds_unique ((hDCT.mono_left nhdsWithin_le_nhds).congr' heq) hR
  have hfin := intervalIntegral_tendsto_integral_Ioi 1 (hint ν (by simp; linarith)) tendsto_id
  unfold HasIntegralAtTop
  simp only [pow_two]
  rw [hu] at hfin
  rw [show deriv digamma (ν+1) * (1/(ν+ν+1)) = deriv digamma (ν+1)/(2*ν+1) by
    rw [show ν+ν+1 = 2*ν+1 by ring]; ring] at hfin
  exact hfin

end DLMF.Legendre

end
