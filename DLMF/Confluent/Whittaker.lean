/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Confluent.BasicProperties

/-!
# Whittaker functions (AAR §4.3)

Whittaker's functions are the standard pair of solutions of the Whittaker equation,
written in terms of Kummer's `M` and the continued Tricomi `U`.
The `OnLog` definitions retain the logarithmic argument for monodromy;
ordinary multiplication of the complex argument by `exp (2πi)` would lose that information.
-/

@[expose] public section

open Complex Filter
open scoped Real Topology
open DLMF.Hypergeometric

noncomputable section

namespace DLMF.Confluent

/-- Whittaker's `M_{κ,μ}(z)`. -/
@[dlmf 13.14.E2]
def whittakerM (κ μ z : ℂ) : ℂ :=
  exp (-z / 2) * z ^ (μ + 1 / 2) * kummerM (μ - κ + 1 / 2) (1 + 2 * μ) z

/-- Whittaker M regularized in its second parameter. This remains meaningful at
`1 + 2 * μ = -n`, where dividing the totalized ordinary M by Gamma would give zero. -/
def regularizedWhittakerM (κ μ z : ℂ) : ℂ :=
  exp (-z / 2) * z ^ (μ + 1 / 2) *
    regularizedHGFun {μ - κ + 1 / 2} {1 + 2 * μ} z

/-- Away from Gamma poles, regularized Whittaker M agrees with the ordinary quotient. -/
theorem regularizedWhittakerM_eq_div_Gamma {κ μ z : ℂ}
    (hμ : ∀ k : ℕ, 1 + 2 * μ ≠ -(k : ℂ)) :
    regularizedWhittakerM κ μ z = whittakerM κ μ z / Gamma (1 + 2 * μ) := by
  rw [whittakerM, kummerM_eq_mul_regularizedHGFun hμ]
  unfold regularizedWhittakerM
  field_simp [Gamma_ne_zero hμ]

/-- Whittaker's principal-branch W, defined through the continued Tricomi function. -/
@[dlmf 13.14.E3]
def whittakerW (κ μ z : ℂ) : ℂ :=
  exp (-z / 2) * z ^ (1 / 2 + μ) * kummerU (1 / 2 + μ - κ) (1 + 2 * μ) z

/-- A half-integer Whittaker specialization whose former raw Gamma formula vanished. -/
theorem whittakerW_half_zero (z : ℂ) :
    whittakerW (1 / 2) 0 z = exp (-z / 2) * z ^ (1 / 2 : ℂ) := by
  norm_num [whittakerW, kummerU_zero]

/-- An elementary Whittaker W specialization, also detecting a missing parameter
bound in the Bessel-K integral representation. -/
theorem whittakerW_zero_half {z : ℂ} (hz : z ≠ 0) :
    whittakerW 0 (1 / 2) z = exp (-z / 2) := by
  have hU := DLMF.Confluent.kummerU_kummer_transform_all 1 2 hz
  norm_num [kummerU_zero] at hU
  norm_num [whittakerW, hU, cpow_neg_one]
  field [hz]

/-- Whittaker's M on the logarithmic argument plane, which records full turns around zero. -/
def whittakerMOnLog (κ μ w : ℂ) : ℂ :=
  exp (-exp w / 2) * exp ((μ + 1 / 2) * w) *
    kummerM (μ - κ + 1 / 2) (1 + 2 * μ) (exp w)

/-- Whittaker's W connection formula on the logarithmic argument plane.
It represents W when `2 * μ` is not an integer. -/
def whittakerWOnLog (κ μ w : ℂ) : ℂ :=
  Gamma (-2 * μ) / Gamma (1 / 2 - μ - κ) * whittakerMOnLog κ μ w +
    Gamma (2 * μ) / Gamma (1 / 2 + μ - κ) * whittakerMOnLog κ (-μ) w

/-- Logarithmic derivative of the prefactor in Whittaker's `M`. -/
theorem hasDerivAt_whittakerPrefactor (r : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    HasDerivAt (fun w : ℂ => exp (-w / 2) * w ^ r)
      (exp (-z / 2) * z ^ r * (r / z - 1 / 2)) z := by
  have hd := (((hasDerivAt_id z).neg.div_const 2).cexp).mul
    ((hasDerivAt_id z).cpow_const (c := r) hz)
  convert! hd using 1
  simp only [id_eq, Pi.neg_apply, mul_one]
  rw [cpow_sub _ _ (slitPlane_ne_zero hz), cpow_one]
  field_simp
  ring

/-- Whittaker's equation (AAR §4.3). -/
@[dlmf 13.14.E1]
theorem whittakerM_ode {κ μ z : ℂ} (hz : z ∈ slitPlane)
    (hμ : ∀ k : ℕ, 1 + 2 * μ ≠ -k) :
    iteratedDeriv 2 (whittakerM κ μ) z +
      (-1 / 4 + κ / z + (1 / 4 - μ ^ 2) / z ^ 2) * whittakerM κ μ z = 0 := by
  let r := μ + 1 / 2
  let y := kummerM (μ - κ + 1 / 2) (1 + 2 * μ)
  let g := fun w : ℂ => exp (-w / 2) * w ^ r
  let q := fun w : ℂ => r / w - 1 / 2
  have hf := hasFPowerSeriesOnBall_kummerM (a := μ - κ + 1 / 2) hμ
  have hy (w : ℂ) : HasDerivAt y (deriv y w) w :=
    (hf.analyticAt_of_mem (y := w) (by simp)).differentiableAt.hasDerivAt
  have hy' : HasDerivAt (deriv y) (iteratedDeriv 2 y z) z := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using
      (hf.deriv_ofScalars.analyticAt_of_mem (y := z) (by simp)).differentiableAt.hasDerivAt
  have hg (w : ℂ) (hw : w ∈ slitPlane) : HasDerivAt g (g w * q w) w :=
    hasDerivAt_whittakerPrefactor r hw
  have hq : HasDerivAt q (-r / z ^ 2) z := by
    convert! ((hasDerivAt_const z r).div (hasDerivAt_id z) (slitPlane_ne_zero hz)).sub_const
      (1 / 2) using 1
    simp
  have hfirst (w : ℂ) (hw : w ∈ slitPlane) :
      deriv (whittakerM κ μ) w = g w * (deriv y w + q w * y w) := by
    have hd := (hg w hw).mul (hy w)
    change deriv (g * y) w = _
    rw [hd.deriv]
    ring
  have heq : deriv (whittakerM κ μ) =ᶠ[𝓝 z]
      (g * (deriv y + q * y)) :=
    Filter.eventually_of_mem (isOpen_slitPlane.mem_nhds hz) hfirst
  have hsecond := (hg z hz).mul (hy'.add (hq.mul (hy z)))
  rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_zero,
    heq.deriv_eq, hsecond.deriv]
  have hode := kummerM_ode (a := μ - κ + 1 / 2) hμ (slitPlane_ne_zero hz)
  change z * iteratedDeriv 2 y z + (1 + 2 * μ - z) * deriv y z -
    (μ - κ + 1 / 2) * y z = 0 at hode
  change _ + _ * (g z * y z) = 0
  dsimp [q, r]
  field_simp [slitPlane_ne_zero hz]
  linear_combination (16 * z * g z) * hode

/-- Whittaker's `M` is analytic away from the principal power's branch cut. -/
theorem analyticAt_whittakerM {κ μ z : ℂ} (hz : z ∈ slitPlane)
    (hμ : ∀ k : ℕ, 1 + 2 * μ ≠ -k) : AnalyticAt ℂ (whittakerM κ μ) z := by
  unfold whittakerM
  apply AnalyticAt.mul
  · apply AnalyticAt.mul
    · fun_prop
    · exact analyticAt_id.cpow analyticAt_const hz
  · exact (hasFPowerSeriesOnBall_kummerM (a := μ - κ + 1 / 2) hμ).analyticAt_of_mem
      (by simp)

/-- The generic connection formula for W; the integer case uses continuation. -/
@[dlmf 13.14.E33]
theorem whittakerW_eq_connection {κ μ z : ℂ} (hz : z ∈ slitPlane)
    (hμ : ∀ k : ℤ, 2 * μ ≠ k) :
    whittakerW κ μ z =
      Gamma (-2 * μ) / Gamma (1 / 2 - μ - κ) * whittakerM κ μ z +
        Gamma (2 * μ) / Gamma (1 / 2 + μ - κ) * whittakerM κ (-μ) z := by
  have hb : ∀ k : ℤ, (1 : ℂ) + 2 * μ ≠ k := by
    intro k hk
    apply hμ (k - 1)
    push_cast
    linear_combination hk
  unfold whittakerW
  rw [kummerU_eq_connection _ _ _ hb]
  unfold kummerUConnection whittakerM
  symm
  have hz0 := slitPlane_ne_zero hz
  have h1b : (1 : ℂ) - (1 + 2 * μ) = -2 * μ := by ring
  have hb1 : (1 + 2 * μ : ℂ) - 1 = 2 * μ := by ring
  have hab : (1 / 2 + μ - κ : ℂ) - (1 + 2 * μ) + 1 = 1 / 2 - μ - κ := by ring
  have h2b : (2 : ℂ) - (1 + 2 * μ) = 1 - 2 * μ := by ring
  have hMμ : (μ : ℂ) - κ + 1 / 2 = 1 / 2 + μ - κ := by ring
  have hMμ' : (-μ : ℂ) - κ + 1 / 2 = 1 / 2 - μ - κ := by ring
  have hden : (1 : ℂ) + 2 * (-μ) = 1 - 2 * μ := by ring
  have hpow : z ^ (1 / 2 + μ) * z ^ (-2 * μ) = z ^ (1 / 2 - μ) := by
    rw [← cpow_add _ _ hz0]
    ring_nf
  simp only [h1b, hb1, hab, h2b, hMμ, hMμ', hden]
  rw [mul_add]
  have hswap :
      exp (-z / 2) * z ^ (1 / 2 + μ) *
          (Gamma (2 * μ) / Gamma (1 / 2 + μ - κ) * z ^ (-2 * μ) *
            kummerM (1 / 2 - μ - κ) (1 - 2 * μ) z) =
        Gamma (2 * μ) / Gamma (1 / 2 + μ - κ) *
          (exp (-z / 2) * z ^ (1 / 2 - μ) * kummerM (1 / 2 - μ - κ) (1 - 2 * μ) z) := by
    calc
      _ = Gamma (2 * μ) / Gamma (1 / 2 + μ - κ) * exp (-z / 2) *
            (z ^ (1 / 2 + μ) * z ^ (-2 * μ)) *
            kummerM (1 / 2 - μ - κ) (1 - 2 * μ) z := by ring
      _ = _ := by rw [hpow]; ring
  rw [hswap]
  ring_nf

/-- Whittaker's `W` satisfies the same equation. -/
@[dlmf 13.14.E1]
theorem whittakerW_ode {κ μ z : ℂ} (hz : z ∈ slitPlane)
    (hμ : ∀ k : ℤ, 2 * μ ≠ k) :
    iteratedDeriv 2 (whittakerW κ μ) z +
      (-1 / 4 + κ / z + (1 / 4 - μ ^ 2) / z ^ 2) * whittakerW κ μ z = 0 := by
  have hpos : ∀ k : ℕ, 1 + 2 * μ ≠ -k := by
    intro k hk
    apply hμ (-(k : ℤ) - 1)
    push_cast
    linear_combination hk
  have hneg : ∀ k : ℕ, 1 + 2 * (-μ) ≠ -k := by
    intro k hk
    apply hμ ((k : ℤ) + 1)
    push_cast
    linear_combination -hk
  have hp := whittakerM_ode (κ := κ) hz hpos
  have hn := whittakerM_ode (κ := κ) hz hneg
  have hap := (analyticAt_whittakerM (κ := κ) hz hpos).contDiffAt (n := 2)
  have han := (analyticAt_whittakerM (κ := κ) hz hneg).contDiffAt (n := 2)
  have heq : whittakerW κ μ =ᶠ[𝓝 z] (fun w =>
      Gamma (-2 * μ) / Gamma (1 / 2 - μ - κ) * whittakerM κ μ w +
        Gamma (2 * μ) / Gamma (1 / 2 + μ - κ) * whittakerM κ (-μ) w) :=
    Filter.eventually_of_mem (isOpen_slitPlane.mem_nhds hz) fun w hw =>
      whittakerW_eq_connection hw hμ
  rw [heq.iteratedDeriv_eq 2, whittakerW_eq_connection hz hμ]
  rw [iteratedDeriv_fun_add (contDiffAt_const.mul hap) (contDiffAt_const.mul han),
    iteratedDeriv_const_mul_field, iteratedDeriv_const_mul_field]
  linear_combination
    Gamma (-2 * μ) / Gamma (1 / 2 - μ - κ) * hp +
      Gamma (2 * μ) / Gamma (1 / 2 + μ - κ) * hn

/-- The definition of W through the continued Tricomi function. -/
@[dlmf 13.14.E3]
theorem whittakerW_eq_kummerU {κ μ z : ℂ} (hz : z ∈ slitPlane) :
    whittakerW κ μ z =
      exp (-z / 2) * z ^ (1 / 2 + μ) * kummerU (1 / 2 + μ - κ) (1 + 2 * μ) z := by
  rfl

/-- Identity under the stated parameter and domain assumptions: `kummerM a b z = exp (z / 2) * z ^
(-b / 2) * whittakerM (b / 2 - a) (b / 2 - 1 / 2) z`. -/
@[dlmf 13.14.E4]
theorem kummerM_eq_whittakerM {a b z : ℂ} (hz : z ∈ slitPlane)
    (hb : ∀ k : ℕ, b ≠ -k) :
    kummerM a b z =
      exp (z / 2) * z ^ (-b / 2) * whittakerM (b / 2 - a) (b / 2 - 1 / 2) z := by
  unfold whittakerM
  have hz0 := slitPlane_ne_zero hz
  have hr : (b / 2 - 1 / 2 : ℂ) + 1 / 2 = b / 2 := by ring
  have ha : (b / 2 - 1 / 2 : ℂ) - (b / 2 - a) + 1 / 2 = a := by ring
  have hb' : (1 : ℂ) + 2 * (b / 2 - 1 / 2) = b := by ring
  rw [hr, ha, hb']
  have hpow : z ^ (-b / 2) * z ^ (b / 2) = 1 := by
    rw [← cpow_add _ _ hz0]
    ring_nf
    simp
  have hexp : exp (z / 2) * exp (-z / 2) = 1 := by
    rw [← exp_add]
    convert exp_zero using 2
    ring
  calc
    kummerM a b z
        = (exp (z / 2) * exp (-z / 2)) * (z ^ (-b / 2) * z ^ (b / 2)) * kummerM a b z := by
          rw [hexp, hpow]; ring
    _ = exp (z / 2) * z ^ (-b / 2) *
          (exp (-z / 2) * z ^ (b / 2) * kummerM a b z) := by ring

/-- Identity under the stated parameter and domain assumptions: `kummerU a b z = exp (z / 2) * z ^
(-b / 2) * whittakerW (b / 2 - a) (b / 2 - 1 / 2) z`. -/
@[dlmf 13.14.E5]
theorem kummerU_eq_whittakerW {a b z : ℂ} (hz : z ∈ slitPlane) :
    kummerU a b z =
      exp (z / 2) * z ^ (-b / 2) * whittakerW (b / 2 - a) (b / 2 - 1 / 2) z := by
  have hz0 := slitPlane_ne_zero hz
  have hW := whittakerW_eq_kummerU (κ := b / 2 - a) (μ := b / 2 - 1 / 2) hz
  have hμ : (1 / 2 + (b / 2 - 1 / 2) - (b / 2 - a) : ℂ) = a := by ring
  have hb' : (1 + 2 * (b / 2 - 1 / 2) : ℂ) = b := by ring
  have hr : (1 / 2 + (b / 2 - 1 / 2) : ℂ) = b / 2 := by ring
  rw [hμ, hb', hr] at hW
  have hpow : z ^ (-b / 2) * z ^ (b / 2) = 1 := by
    rw [← cpow_add _ _ hz0]
    ring_nf
    simp
  have hexp : exp (z / 2) * exp (-z / 2) = 1 := by
    rw [← exp_add]
    convert exp_zero using 2
    ring
  calc
    kummerU a b z
        = (exp (z / 2) * exp (-z / 2)) * (z ^ (-b / 2) * z ^ (b / 2)) * kummerU a b z := by
          rw [hexp, hpow]; ring
    _ = exp (z / 2) * z ^ (-b / 2) *
          (exp (-z / 2) * z ^ (b / 2) * kummerU a b z) := by ring
    _ = exp (z / 2) * z ^ (-b / 2) * whittakerW (b / 2 - a) (b / 2 - 1 / 2) z := by
          rw [hW]

/-- The punctured parameter limit of normalized Whittaker M at a denominator pole. -/
@[dlmf 13.14.E7]
theorem tendsto_whittakerM_div_Gamma (κ : ℂ) (n : ℕ) {z : ℂ} (hz : z ∈ slitPlane) :
    Tendsto (fun μ : ℂ => whittakerM κ μ z / Gamma (2 * μ + 1)) (𝓝[≠] (-(n + 1 : ℂ) / 2))
      (𝓝 (poch (-(n : ℂ) / 2 - κ) (n + 1) / (n + 1).factorial *
        whittakerM κ ((n + 1 : ℂ) / 2) z)) := by
  let p : ℂ := -(n + 1 : ℂ) / 2
  have hB : 1 + 2 * p = -(n : ℂ) := by dsimp [p]; ring
  have hA : p - κ + 1 / 2 = -(n : ℂ) / 2 - κ := by dsimp [p]; ring
  have htB : Tendsto (fun μ : ℂ => 1 + 2 * μ) (𝓝[≠] p) (𝓝[≠] (-(n : ℂ))) := by
    rw [← hB]
    exact (by fun_prop : Continuous (fun μ : ℂ => 1 + 2 * μ)).continuousAt.continuousWithinAt.tendsto_nhdsWithin (fun μ hμ h => hμ (by
        change μ = p
        change 1 + 2 * μ = 1 + 2 * p at h
        linear_combination h / 2))
  have hreg := tendsto_regularizedConfluent_param (fun μ => μ - κ + 1 / 2)
    (fun μ => 1 + 2 * μ) (by fun_prop) (by fun_prop) p z (𝓝[≠] p)
    nhdsWithin_le_nhds
  have hpow : Tendsto (fun μ : ℂ => z ^ (μ + 1 / 2)) (𝓝[≠] p)
      (𝓝 (z ^ (p + 1 / 2))) := by
    have hc : Continuous (fun μ : ℂ => z ^ (μ + 1 / 2)) :=
      (continuous_id.add continuous_const).const_cpow (Or.inl (slitPlane_ne_zero hz))
    exact hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have ht := (hpow.const_mul (exp (-z / 2))).mul hreg
  have hval : exp (-z / 2) * z ^ (p + 1 / 2) *
      regularizedHGFun {p - κ + 1 / 2} {1 + 2 * p} z =
      poch (-(n : ℂ) / 2 - κ) (n + 1) / (n + 1).factorial *
        whittakerM κ ((n + 1 : ℂ) / 2) z := by
    rw [hB, hA, regularizedHGFun_of_neg_nat]
    unfold whittakerM
    rw [← cpow_natCast z (n + 1)]
    have hp : z ^ (p + 1 / 2) * z ^ ((n + 1 : ℕ) : ℂ) =
        z ^ ((n + 1 : ℂ) / 2 + 1 / 2) := by
      rw [← cpow_add _ _ (slitPlane_ne_zero hz)]
      congr 1
      dsimp [p]
      push_cast
      ring
    have ha : -(n : ℂ) / 2 - κ + n + 1 = (n + 1 : ℂ) / 2 - κ + 1 / 2 := by ring
    have hb : (n : ℂ) + 2 = 1 + 2 * ((n + 1 : ℂ) / 2) := by ring
    rw [ha, hb]
    linear_combination exp (-z / 2) *
      (poch (-(n : ℂ) / 2 - κ) (n + 1) / (n + 1).factorial) *
      kummerM ((n + 1 : ℂ) / 2 - κ + 1 / 2) (1 + 2 * ((n + 1 : ℂ) / 2)) z * hp
  rw [hval] at ht
  apply ht.congr'
  filter_upwards [htB.eventually (DLMF.Hypergeometric.eventually_nhdsWithin_ne_neg_nat n)]
    with μ hμ
  rw [whittakerM, kummerM_eq_mul_regularizedHGFun hμ]
  rw [show 2 * μ + 1 = 1 + 2 * μ by ring]
  field [Gamma_ne_zero hμ]

/-- Half-turn continuation of Whittaker M on the logarithmic argument plane. -/
@[dlmf 13.14.E10]
theorem whittakerM_neg_argument {κ μ z : ℂ} (hz : z ∈ slitPlane) (sign : Bool)
    (hμ : ∀ k : ℕ, 1 + 2 * μ ≠ -k) :
    whittakerMOnLog κ μ (log z + (if sign then 1 else -1) * π * I) =
      (if sign then 1 else -1) * I * exp ((if sign then 1 else -1) * μ * π * I) *
        whittakerM (-κ) μ z := by
  have hz0 := slitPlane_ne_zero hz
  set s : ℂ := if sign then 1 else -1 with hs
  have hs2 : exp (s * π * I) = -1 := by
    cases sign <;> simp [hs, exp_neg, exp_pi_mul_I]
  have hsh : exp (s * (π / 2) * I) = s * I := by
    cases sign
    · simp only [hs, Bool.false_eq_true, ↓reduceIte, neg_mul, one_mul, exp_neg]
      rw [show (π : ℂ) / 2 * I = (π / 2 : ℝ) * I by push_cast; ring, exp_mul_I]
      simp
    · simp only [hs, ↓reduceIte, one_mul]
      rw [show (π : ℂ) / 2 * I = (π / 2 : ℝ) * I by push_cast; ring, exp_mul_I]
      simp
  have he : exp (log z + s * π * I) = -z := by rw [exp_add, exp_log hz0, hs2]; ring
  have hp : exp ((μ + 1 / 2) * (log z + s * π * I)) =
      z ^ (μ + 1 / 2) * exp (s * μ * π * I) * (s * I) := by
    rw [← hsh, cpow_def_of_ne_zero hz0, ← exp_add, ← exp_add]
    congr 1
    ring
  unfold whittakerMOnLog whittakerM
  rw [he, hp, kummerM_kummer_transform hμ, neg_neg,
    show 1 + 2 * μ - (μ - κ + 1 / 2) = μ - -κ + 1 / 2 by ring]
  have hexp : exp (-(-z) / 2) * exp (-z) = exp (-z / 2) := by rw [← exp_add]; ring_nf
  rw [← hexp]
  ring_nf

/-- Full-turn continuation of Whittaker M, retaining the logarithmic argument. -/
@[dlmf 13.14.E11]
theorem whittakerM_continuation {κ μ z : ℂ} (m : ℤ) (hz : z ∈ slitPlane) :
    whittakerMOnLog κ μ (log z + 2 * m * π * I) =
      (-1 : ℂ) ^ m * exp (2 * m * μ * π * I) * whittakerM κ μ z := by
  have hz0 := slitPlane_ne_zero hz
  have ht : exp (2 * (m : ℂ) * π * I) = 1 := by
    rw [show 2 * (m : ℂ) * π * I = (m : ℂ) * (2 * π * I) by ring,
      exp_int_mul_two_pi_mul_I]
  have he : exp (log z + 2 * m * π * I) = z := by rw [exp_add, ht, exp_log hz0, mul_one]
  have hm : exp ((m : ℂ) * (π * I)) = (-1 : ℂ) ^ m := by
    rw [exp_int_mul, exp_pi_mul_I]
  have hp : exp ((μ + 1 / 2) * (log z + 2 * m * π * I)) =
      (-1 : ℂ) ^ m * exp (2 * m * μ * π * I) * z ^ (μ + 1 / 2) := by
    rw [show (μ + 1 / 2) * (log z + 2 * m * π * I) =
      (m * (π * I) + 2 * m * μ * π * I) + log z * (μ + 1 / 2) by ring,
      exp_add, exp_add, hm, cpow_def_of_ne_zero hz0]
  simp only [whittakerMOnLog, whittakerM, he, hp]
  ring

/-- Full-turn continuation of Whittaker W at noninteger twice-order. -/
@[dlmf 13.14.E12]
theorem whittakerW_continuation {κ μ z : ℂ} (m : ℤ) (hz : z ∈ slitPlane)
    (hμ : ∀ n : ℤ, 2 * μ ≠ n) :
    whittakerWOnLog κ μ (log z + 2 * m * π * I) =
      (-1 : ℂ) ^ (m + 1) * 2 * π * I * sin (2 * π * μ * m) /
          (Gamma (1 / 2 - μ - κ) * Gamma (1 + 2 * μ) * sin (2 * π * μ)) *
        whittakerM κ μ z +
        (-1 : ℂ) ^ m * exp (-2 * m * μ * π * I) * whittakerW κ μ z := by
  have hGne : Gamma (1 + 2 * μ) ≠ 0 := Gamma_ne_zero (fun k hk =>
    hμ (-(k : ℤ) - 1) (by push_cast; linear_combination hk))
  have hG : Gamma (-2 * μ) = -π / (Gamma (1 + 2 * μ) * sin (2 * π * μ)) := by
    have h := Gamma_mul_Gamma_one_sub (-2 * μ)
    rw [show 1 - -2 * μ = 1 + 2 * μ by ring,
      show (π : ℂ) * (-2 * μ) = -(2 * π * μ) by ring, sin_neg] at h
    apply mul_right_cancel₀ hGne
    rw [h]
    field_simp
  have ht : exp (2 * m * μ * π * I) - exp (-2 * m * μ * π * I) =
      2 * I * sin (2 * π * μ * m) := by
    rw [sin, show -(2 * (π : ℂ) * μ * m) * I = -2 * m * μ * π * I by ring,
      show (2 * (π : ℂ) * μ * m) * I = 2 * m * μ * π * I by ring]
    linear_combination (exp (2 * m * μ * π * I) - exp (-2 * m * μ * π * I)) * I_sq
  rw [whittakerWOnLog, whittakerM_continuation m hz, whittakerM_continuation m hz,
    whittakerW_eq_connection hz hμ, hG,
    show 2 * (m : ℂ) * -μ * π * I = -2 * m * μ * π * I by ring,
    zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), zpow_one]
  rw [show exp (2 * m * μ * π * I) = 2 * I * sin (2 * π * μ * m) +
    exp (-2 * m * μ * π * I) by linear_combination ht]
  ring

/-- Identity under the stated parameter and domain assumptions: `Asymptotics.IsBigO (𝓝[≠] (0 : ℂ))
(fun z => whittakerM κ μ z - z ^ (μ + 1 / 2)) (fun z => z ^ (μ + 3 / 2))`. -/
@[dlmf 13.14.E14]
theorem isBigO_whittakerM_at_zero {κ μ : ℂ} (hμ : ∀ k : ℕ, 2 * μ ≠ -k - 1) :
    Asymptotics.IsBigO (𝓝[≠] (0 : ℂ))
      (fun z => whittakerM κ μ z - z ^ (μ + 1 / 2))
      (fun z => z ^ (μ + 3 / 2)) := by
  have hb : ∀ k : ℕ, 1 + 2 * μ ≠ -k := fun k h => hμ k (by linear_combination h)
  set f : ℂ → ℂ := fun z => exp (-z / 2) * kummerM (μ - κ + 1 / 2) (1 + 2 * μ) z with hf
  have hd : DifferentiableAt ℂ f 0 :=
    (by fun_prop : DifferentiableAt ℂ (fun z : ℂ => exp (-z / 2)) 0).mul
      ((analyticOnNhd_kummerM (a := μ - κ + 1 / 2) hb) 0 (Set.mem_univ _)).differentiableAt
  have hf0 : f 0 = 1 := by simp [hf, kummerM_zero]
  have h1 : Asymptotics.IsBigO (𝓝[≠] (0 : ℂ)) (fun z => f z - 1) id :=
    ((hd.isBigO_sub).congr (fun z => by rw [hf0]) (fun z => by simp)).mono nhdsWithin_le_nhds
  refine ((Asymptotics.isBigO_refl (fun z : ℂ => z ^ (μ + 1 / 2)) (𝓝[≠] (0 : ℂ))).mul h1).congr'
    ?_ ?_
  · filter_upwards with z
    simp only [hf, whittakerM]
    ring
  · filter_upwards [self_mem_nhdsWithin] with z hz
    simp only [id]
    rw [show μ + 3 / 2 = (μ + 1 / 2) + 1 by ring,
      (cpow_add _ _ hz : z ^ ((μ + 1 / 2) + 1) = z ^ (μ + 1 / 2) * z ^ (1 : ℂ)), cpow_one]

/-- `W(g f₁, g f₂) = g² W(f₁, f₂)`. -/
theorem wronskian_mul_left {g f₁ f₂ : ℂ → ℂ} {z : ℂ} (hg : DifferentiableAt ℂ g z)
    (h₁ : DifferentiableAt ℂ f₁ z) (h₂ : DifferentiableAt ℂ f₂ z) :
    ODE.wronskian (fun w => g w * f₁ w) (fun w => g w * f₂ w) z =
      g z ^ 2 * ODE.wronskian f₁ f₂ z := by
  unfold ODE.wronskian
  rw [deriv_fun_mul hg h₁, deriv_fun_mul hg h₂]
  ring

/-- The Whittaker prefactor `e^{-z/2} z^{μ+1/2}`. -/
theorem differentiableAt_whittaker_prefactor (μ : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    DifferentiableAt ℂ (fun w => exp (-w / 2) * w ^ (μ + 1 / 2)) z :=
  (by fun_prop : DifferentiableAt ℂ (fun w : ℂ => exp (-w / 2)) z).mul
    ((hasDerivAt_id z).cpow_const (c := μ + 1 / 2) hz).differentiableAt

/-- The square of the Whittaker prefactor. -/
theorem whittaker_prefactor_sq (μ z : ℂ) :
    (exp (-z / 2) * z ^ (μ + 1 / 2)) ^ 2 = exp (-z) * z ^ (1 + 2 * μ) := by
  rw [mul_pow, ← exp_nat_mul, ← cpow_nat_mul]
  push_cast
  ring_nf

/-- Whittaker W as prefactor times Tricomi U. -/
theorem whittakerW_eq_prefactor_mul (κ μ : ℂ) :
    whittakerW κ μ = fun w => (exp (-w / 2) * w ^ (μ + 1 / 2)) *
      kummerU (μ + 1 / 2 - κ) (1 + 2 * μ) w := by
  funext w
  unfold whittakerW
  rw [show (1 / 2 : ℂ) + μ = μ + 1 / 2 by ring]

/-- `U(a,b,·)` is differentiable at every point of the slit plane. -/
theorem differentiableAt_kummerU (a b : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    DifferentiableAt ℂ (kummerU a b) z :=
  (differentiableOn_kummerU a b).differentiableAt (isOpen_slitPlane.mem_nhds hz)

/-- Identity under the stated parameter and domain assumptions: `ODE.wronskian (whittakerM κ μ)
(whittakerM κ (-μ)) z = -2 * μ`. -/
@[dlmf 13.14.E25]
theorem wronskian_whittakerM {κ μ z : ℂ} (hz : z ∈ slitPlane)
    (hμ : ∀ k : ℕ, 1 + 2 * μ ≠ -k) (hμ' : ∀ k : ℕ, 1 - 2 * μ ≠ -k) :
    ODE.wronskian (whittakerM κ μ) (whittakerM κ (-μ)) z = -2 * μ := by
  have hz0 := slitPlane_ne_zero hz
  set b := 1 + 2 * μ
  have hB : ∀ k : ℕ, 2 - b ≠ -k := fun k h => hμ' k (by rw [← h]; ring)
  have h1 : whittakerM κ μ = fun w => (exp (-w / 2) * w ^ (μ + 1 / 2)) *
      kummerM (μ - κ + 1 / 2) b w := rfl
  have h2 : ∀ w ∈ slitPlane, whittakerM κ (-μ) w = (exp (-w / 2) * w ^ (μ + 1 / 2)) *
      (w ^ (1 - b) * kummerM (μ - κ + 1 / 2 - b + 1) (2 - b) w) := by
    intro w hw
    unfold whittakerM
    have hp : w ^ (-μ + 1 / 2) = w ^ (μ + 1 / 2) * w ^ (1 - b) := by
      rw [← cpow_add _ _ (slitPlane_ne_zero hw)]; congr 1; ring
    rw [show -μ - κ + 1 / 2 = μ - κ + 1 / 2 - b + 1 by ring,
      show 1 + 2 * -μ = 2 - b by ring, hp]
    ring
  have heq : whittakerM κ (-μ) =ᶠ[𝓝 z] fun w => (exp (-w / 2) * w ^ (μ + 1 / 2)) *
      (w ^ (1 - b) * kummerM (μ - κ + 1 / 2 - b + 1) (2 - b) w) := by
    filter_upwards [isOpen_slitPlane.mem_nhds hz] with w hw using h2 w hw
  have hu := ((analyticOnNhd_kummerM (a := μ - κ + 1 / 2) hμ) z (Set.mem_univ _)).differentiableAt
  have hv := ((analyticOnNhd_kummerM (a := μ - κ + 1 / 2 - b + 1) hB) z
    (Set.mem_univ _)).differentiableAt
  have hy : DifferentiableAt ℂ (fun w => w ^ (1 - b) * kummerM (μ - κ + 1 / 2 - b + 1) (2 - b) w) z :=
    ((hasDerivAt_id z).cpow_const (c := 1 - b) hz).differentiableAt.mul hv
  have hW : ODE.wronskian (whittakerM κ μ) (whittakerM κ (-μ)) z =
      ODE.wronskian (whittakerM κ μ) (fun w => (exp (-w / 2) * w ^ (μ + 1 / 2)) *
        (w ^ (1 - b) * kummerM (μ - κ + 1 / 2 - b + 1) (2 - b) w)) z := by
    unfold ODE.wronskian
    rw [heq.deriv_eq, heq.eq_of_nhds]
  rw [hW, h1, wronskian_mul_left (differentiableAt_whittaker_prefactor μ hz) hu hy,
    wronskian_kummer_pair_of_nonpole _ b hμ hB hz, whittaker_prefactor_sq μ z]
  have hp : z ^ (1 + 2 * μ) * z ^ (-b) = 1 := by
    rw [← cpow_add _ _ hz0]; simp [b]
  have he : exp (-z) * exp z = 1 := by rw [← exp_add]; simp
  simp only [b] at hp ⊢
  linear_combination (-2 * μ) * (exp (-z) * exp z) * hp + (-2 * μ) * he

/-- Identity under the stated parameter and domain assumptions: `ODE.wronskian (whittakerM κ μ)
(whittakerW κ μ) z = -Gamma (1 + 2 * μ) / Gamma (1 / 2 + μ - κ)`. -/
@[dlmf 13.14.E26]
theorem wronskian_whittakerM_W {κ μ z : ℂ} (hz : z ∈ slitPlane)
    (hμ : ∀ k : ℕ, 1 + 2 * μ ≠ -k) :
    ODE.wronskian (whittakerM κ μ) (whittakerW κ μ) z =
      -Gamma (1 + 2 * μ) / Gamma (1 / 2 + μ - κ) := by
  have hz0 := slitPlane_ne_zero hz
  have hM : kummerM (μ - κ + 1 / 2) (1 + 2 * μ) = fun w =>
      Gamma (1 + 2 * μ) * regularizedHGFun {μ + 1 / 2 - κ} {1 + 2 * μ} w := by
    funext w
    rw [regularizedConfluent_eq_div_Gamma hμ, show μ + 1 / 2 - κ = μ - κ + 1 / 2 by ring,
      mul_div_cancel₀ _ (Gamma_ne_zero hμ)]
  have h1 : whittakerM κ μ = fun w => (exp (-w / 2) * w ^ (μ + 1 / 2)) *
      kummerM (μ - κ + 1 / 2) (1 + 2 * μ) w := rfl
  have hd := differentiableAt_regularizedConfluent (μ + 1 / 2 - κ) (1 + 2 * μ) z
  have hu : DifferentiableAt ℂ (kummerM (μ - κ + 1 / 2) (1 + 2 * μ)) z := by
    rw [hM]; exact hd.const_mul _
  rw [h1, whittakerW_eq_prefactor_mul,
    wronskian_mul_left (differentiableAt_whittaker_prefactor μ hz) hu
      (differentiableAt_kummerU _ _ hz), whittaker_prefactor_sq μ z]
  have hW : ODE.wronskian (kummerM (μ - κ + 1 / 2) (1 + 2 * μ))
      (kummerU (μ + 1 / 2 - κ) (1 + 2 * μ)) z =
      Gamma (1 + 2 * μ) * ODE.wronskian (regularizedHGFun {μ + 1 / 2 - κ} {1 + 2 * μ})
        (kummerU (μ + 1 / 2 - κ) (1 + 2 * μ)) z := by
    unfold ODE.wronskian
    rw [hM, deriv_const_mul _ hd]
    ring
  rw [hW, wronskian_regularizedHGFun_kummerU_all _ _ hz,
    show μ + 1 / 2 - κ = 1 / 2 + μ - κ by ring]
  have hp : z ^ (1 + 2 * μ) * z ^ (-(1 + 2 * μ)) = 1 := by
    rw [← cpow_add _ _ hz0]; simp
  have he : exp (-z) * exp z = 1 := by rw [← exp_add]; simp
  linear_combination (-Gamma (1 + 2 * μ) / Gamma (1 / 2 + μ - κ)) * (exp (-z) * exp z) * hp +
    (-Gamma (1 + 2 * μ) / Gamma (1 / 2 + μ - κ)) * he

/-- Identity under the stated parameter and domain assumptions: `ODE.wronskian (whittakerM κ (-μ))
(whittakerW κ μ) z = -Gamma (1 - 2 * μ) / Gamma (1 / 2 - μ - κ)`. -/
@[dlmf 13.14.E28]
theorem wronskian_whittakerM_neg_W {κ μ z : ℂ} (hz : z ∈ slitPlane)
    (hμ : ∀ k : ℕ, 1 - 2 * μ ≠ -k) :
    ODE.wronskian (whittakerM κ (-μ)) (whittakerW κ μ) z =
      -Gamma (1 - 2 * μ) / Gamma (1 / 2 - μ - κ) := by
  have hz0 := slitPlane_ne_zero hz
  set b := 1 + 2 * μ with hbdef
  set a := μ + 1 / 2 - κ with hadef
  have hB : ∀ k : ℕ, 2 - b ≠ -k := fun k h => hμ k (by rw [← h]; ring)
  have h2 : ∀ w ∈ slitPlane, whittakerM κ (-μ) w = (exp (-w / 2) * w ^ (μ + 1 / 2)) *
      (Gamma (2 - b) * (w ^ (1 - b) * regularizedHGFun {a - b + 1} {2 - b} w)) := by
    intro w hw
    unfold whittakerM
    have hp : w ^ (-μ + 1 / 2) = w ^ (μ + 1 / 2) * w ^ (1 - b) := by
      rw [← cpow_add _ _ (slitPlane_ne_zero hw)]; congr 1; ring
    rw [regularizedConfluent_eq_div_Gamma hB, show -μ - κ + 1 / 2 = a - b + 1 by ring,
      show 1 + 2 * -μ = 2 - b by ring, hp]
    field_simp [Gamma_ne_zero hB]
  have heq : whittakerM κ (-μ) =ᶠ[𝓝 z] fun w => (exp (-w / 2) * w ^ (μ + 1 / 2)) *
      (Gamma (2 - b) * (w ^ (1 - b) * regularizedHGFun {a - b + 1} {2 - b} w)) := by
    filter_upwards [isOpen_slitPlane.mem_nhds hz] with w hw using h2 w hw
  have hy : DifferentiableAt ℂ (fun w => w ^ (1 - b) * regularizedHGFun {a - b + 1} {2 - b} w) z :=
    ((hasDerivAt_id z).cpow_const (c := 1 - b) hz).differentiableAt.mul
      (differentiableAt_regularizedConfluent _ _ z)
  have hW : ODE.wronskian (whittakerM κ (-μ)) (whittakerW κ μ) z =
      ODE.wronskian (fun w => (exp (-w / 2) * w ^ (μ + 1 / 2)) *
        (Gamma (2 - b) * (w ^ (1 - b) * regularizedHGFun {a - b + 1} {2 - b} w)))
        (whittakerW κ μ) z := by
    unfold ODE.wronskian
    rw [heq.deriv_eq, heq.eq_of_nhds]
  rw [hW, whittakerW_eq_prefactor_mul,
    wronskian_mul_left (differentiableAt_whittaker_prefactor μ hz) (hy.const_mul _)
      (differentiableAt_kummerU _ _ hz), whittaker_prefactor_sq μ z]
  have hW2 : ODE.wronskian (fun w => Gamma (2 - b) * (w ^ (1 - b) *
      regularizedHGFun {a - b + 1} {2 - b} w)) (kummerU a b) z =
      Gamma (2 - b) * ODE.wronskian (fun w => w ^ (1 - b) * regularizedHGFun {a - b + 1} {2 - b} w)
        (kummerU a b) z := by
    unfold ODE.wronskian
    rw [deriv_const_mul _ hy]
    ring
  rw [hW2, wronskian_shifted_regularized_kummerU_all a b hz,
    show a - b + 1 = 1 / 2 - μ - κ by ring, show (2 : ℂ) - b = 1 - 2 * μ by ring]
  have hp : z ^ (1 + 2 * μ) * z ^ (-b) = 1 := by
    rw [← cpow_add _ _ hz0]; simp [hbdef]
  have he : exp (-z) * exp z = 1 := by rw [← exp_add]; simp
  linear_combination (-Gamma (1 - 2 * μ) / Gamma (1 / 2 - μ - κ)) * (exp (-z) * exp z) * hp +
    (-Gamma (1 - 2 * μ) / Gamma (1 / 2 - μ - κ)) * he

/-- Symmetry in the order for the generic W connection formula on the slit plane.
Extension to half-integer orders requires the Tricomi parameter-limit API. -/
@[dlmf 13.14.E31]
theorem whittakerW_even_mu (κ μ : ℂ) {z : ℂ} (hz : z ∈ slitPlane)
    (hμ : ∀ k : ℤ, 2 * μ ≠ k) :
    whittakerW κ μ z = whittakerW κ (-μ) z := by
  have hneg : ∀ k : ℤ, 2 * (-μ) ≠ k := by
    intro k hk
    apply hμ (-k)
    push_cast
    linear_combination -hk
  rw [whittakerW_eq_connection hz hμ, whittakerW_eq_connection hz hneg]
  simp only [neg_neg]
  rw [add_comm]
  refine congrArg₂ (· + ·) ?_ ?_ <;> congr 1 <;> ring

/-- The jump of `W` across the negative axis, with both continuations `z e^{±πi}` taken on
the logarithmic argument plane. `whittakerWOnLog` represents `W` there for noninteger `2μ`. -/
@[dlmf 13.14.E34]
theorem whittakerM_jump {κ μ z : ℂ} (hz : z ∈ slitPlane) (hμi : ∀ n : ℤ, 2 * μ ≠ n)
    (hμ : ∀ k : ℕ, 1 + 2 * μ ≠ -k) :
    2 * π / (Gamma (1 + 2 * μ) * Gamma (1 / 2 - μ - κ)) * whittakerM (-κ) μ z =
      exp (μ * π * I) * whittakerWOnLog κ μ (log z + π * I) +
        exp (-μ * π * I) * whittakerWOnLog κ μ (log z - π * I) := by
  have hp := whittakerM_neg_argument (κ := κ) hz true hμ
  have hm := whittakerM_neg_argument (κ := κ) hz false hμ
  have hμ' : ∀ k : ℕ, 1 + 2 * (-μ) ≠ -k := fun k hk =>
    hμi (1 + k) (by push_cast; linear_combination -hk)
  have hnp := whittakerM_neg_argument (κ := κ) hz true hμ'
  have hnm := whittakerM_neg_argument (κ := κ) hz false hμ'
  simp only [Bool.false_eq_true, ↓reduceIte, one_mul, neg_one_mul, neg_neg, neg_mul,
    ← sub_eq_add_neg] at hp hm hnp hnm
  have hGne := Gamma_ne_zero hμ
  have hsin : sin (2 * π * μ) ≠ 0 := by
    rw [show (2 : ℂ) * π * μ = π * (2 * μ) by ring]
    exact sin_pi_mul_ne_zero_of_mem (mem_integerComplement_of_forall hμi)
  have hG : Gamma (-2 * μ) * sin (2 * π * μ) = -π / Gamma (1 + 2 * μ) := by
    have h := Gamma_mul_Gamma_one_sub (-2 * μ)
    rw [show 1 - -2 * μ = 1 + 2 * μ by ring,
      show (π : ℂ) * (-2 * μ) = -(2 * π * μ) by ring, sin_neg, div_neg, ← neg_div] at h
    apply (eq_div_iff hGne).mpr
    linear_combination (eq_div_iff hsin).mp h
  have ht := exp_sub_exp_neg_mul_I (2 * π * μ)
  have hpp : exp (μ * π * I) * exp (μ * π * I) = exp ((2 * π * μ) * I) := by
    rw [← exp_add]; congr 1; ring
  have hmm : exp (-μ * π * I) * exp (-μ * π * I) = exp (-(2 * π * μ) * I) := by
    rw [← exp_add]; congr 1; ring
  rw [whittakerWOnLog, whittakerWOnLog, hp, hm, hnp, hnm]
  calc _ = -2 * (Gamma (-2 * μ) * sin (2 * π * μ)) / Gamma (1 / 2 - μ - κ) *
      whittakerM (-κ) μ z := by rw [hG]; ring
    _ = Gamma (-2 * μ) / Gamma (1 / 2 - μ - κ) * I *
      (exp ((2 * π * μ) * I) - exp (-(2 * π * μ) * I)) * whittakerM (-κ) μ z := by
      rw [ht]
      linear_combination -(2 * Gamma (-2 * μ) / Gamma (1 / 2 - μ - κ) *
        sin (2 * π * μ) * whittakerM (-κ) μ z) * I_sq
    _ = _ := by rw [← hpp, ← hmm]; ring

/-- Whittaker W on the logarithmic plane, expressed through Tricomi U there. -/
theorem whittakerWOnLog_eq_kummerUOnLog (κ μ w : ℂ) :
    whittakerWOnLog κ μ w = exp (-exp w / 2) * exp ((μ + 1 / 2) * w) *
      kummerUOnLog (1 / 2 + μ - κ) (1 + 2 * μ) w := by
  unfold whittakerWOnLog whittakerMOnLog kummerUOnLog
  rw [show 1 - (1 + 2 * μ) = -2 * μ by ring,
    show 1 / 2 + μ - κ - (1 + 2 * μ) + 1 = 1 / 2 - μ - κ by ring,
    show 1 + 2 * μ - 1 = 2 * μ by ring,
    show 2 - (1 + 2 * μ) = 1 + 2 * -μ by ring,
    show μ - κ + 1 / 2 = 1 / 2 + μ - κ by ring,
    show -μ - κ + 1 / 2 = 1 / 2 - μ - κ by ring]
  have he : exp ((-μ + 1 / 2) * w) = exp ((μ + 1 / 2) * w) * exp ((-2 * μ) * w) := by
    rw [← exp_add]; congr 1; ring
  rw [he]
  ring

/-- The prefactor in Whittaker W after a half-turn, with the turn retained. -/
theorem whittakerWOnLog_half_turn (κ μ : ℂ) {z : ℂ} (hz : z ≠ 0) (sign : Bool) :
    whittakerWOnLog κ μ (log z + (if sign then 1 else -1) * π * I) =
      exp (z / 2) * z ^ (μ + 1 / 2) * exp ((if sign then 1 else -1) * (μ + 1 / 2) * π * I) *
        kummerUOnLog (1 / 2 + μ - κ) (1 + 2 * μ)
          (log z + (if sign then 1 else -1) * π * I) := by
  set s : ℂ := if sign then 1 else -1 with hs
  have he : exp (log z + s * π * I) = -z := by
    have ht : exp (s * π * I) = -1 := by
      cases sign <;> simp [hs, exp_neg, exp_pi_mul_I]
    rw [exp_add, exp_log hz, ht]; ring
  rw [whittakerWOnLog_eq_kummerUOnLog, he, neg_neg,
    show (μ + 1 / 2) * (log z + s * π * I) = log z * (μ + 1 / 2) + s * (μ + 1 / 2) * π * I by ring,
    exp_add, cpow_def_of_ne_zero hz]
  ring

/-- The jump of `W` across the negative axis, with both continuations `z e^{±πi}` taken on
the logarithmic argument plane. `whittakerWOnLog` represents `W` there for noninteger `2μ`. -/
@[dlmf 13.14.E35]
theorem whittakerW_jump {κ μ z : ℂ} (hz : z ∈ slitPlane) (hμi : ∀ n : ℤ, 2 * μ ≠ n) :
    2 * π * I / (Gamma (1 / 2 + μ - κ) * Gamma (1 / 2 - μ - κ)) * whittakerW (-κ) μ z =
      exp (-κ * π * I) * whittakerWOnLog κ μ (log z + π * I) -
        exp (κ * π * I) * whittakerWOnLog κ μ (log z - π * I) := by
  have hz0 := slitPlane_ne_zero hz
  have hb : ∀ k : ℤ, 1 + 2 * μ ≠ k := fun k hk =>
    hμi (k - 1) (by push_cast; linear_combination hk)
  have h := kummerU_jump_all (1 / 2 + μ - κ) (1 + 2 * μ) hz hb
  have hp := whittakerWOnLog_half_turn κ μ hz0 true
  have hm := whittakerWOnLog_half_turn κ μ hz0 false
  simp only [Bool.false_eq_true, ↓reduceIte, one_mul, neg_one_mul, neg_neg, neg_mul,
    ← sub_eq_add_neg] at hp hm
  rw [show (1 / 2 + μ - κ) - (1 + 2 * μ) + 1 = 1 / 2 - μ - κ by ring,
    show (1 + 2 * μ) - (1 / 2 + μ - κ) = 1 / 2 + μ - -κ by ring] at h
  have he : exp (z / 2) * exp (-z) = exp (-z / 2) := by
    rw [← exp_add]; congr 1; ring
  have he1 : exp (-κ * π * I) * exp ((μ + 1 / 2) * π * I) =
      exp ((1 / 2 + μ - κ) * π * I) := by rw [← exp_add]; congr 1; ring
  have he2 : exp (κ * π * I) * exp (-(μ + 1 / 2) * π * I) =
      exp (-(1 / 2 + μ - κ) * π * I) := by rw [← exp_add]; congr 1; ring
  rw [hp, hm]
  calc
    _ = (exp (z / 2) * z ^ (μ + 1 / 2)) *
        (2 * π * I * exp (-z) / (Gamma (1 / 2 + μ - κ) * Gamma (1 / 2 - μ - κ)) *
          kummerU (1 / 2 + μ - -κ) (1 + 2 * μ) z) := by
      unfold whittakerW
      rw [show 1 / 2 + μ = μ + 1 / 2 by ring, ← he]
      ring
    _ = _ := by
      rw [h]
      simp only [neg_mul] at he1 he2 ⊢
      linear_combination -(exp (z / 2) * z ^ (μ + 1 / 2) *
        kummerUOnLog (1 / 2 + μ - κ) (1 + 2 * μ) (log z + π * I)) * he1 +
        (exp (z / 2) * z ^ (μ + 1 / 2) *
          kummerUOnLog (1 / 2 + μ - κ) (1 + 2 * μ) (log z - π * I)) * he2

end DLMF.Confluent
