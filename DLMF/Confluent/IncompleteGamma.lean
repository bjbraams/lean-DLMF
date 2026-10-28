/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Confluent.Asymptotics
public import DLMF.Confluent.Relations
public import TauCeti.Analysis.SpecialFunctions.IncompleteGamma

/-!
# Incomplete Gamma functions (Temme §7.3.7; DLMF §§8.2–8.11)

The project defines the upper incomplete Gamma function through Tricomi's function,
`upperIncGamma a z = e^{-z} U(1-a, 1-a, z)` (DLMF 13.6.6), and the lower one through Kummer's
function, `lowerIncGamma a z = z^a / a · M(a, a+1, -z)` (DLMF 13.6.5). This file
connects them with the defining integrals and derives their basic relations and the
asymptotic expansion of `Γ(a,x)` from Tricomi's expansion.

## Main results

* `upperIncGamma_eq_cpow_mul_kummerU`: `Γ(a,z) = z^a e^{-z} U(1, a+1, z)`.
* `upperIncGamma_eq_integral`: `Γ(a,x) = ∫ₓ^∞ t^{a-1} e^{-t} dt` for `x > 0` and all `a`.
* `lowerIncGamma_eq_regularized`: `γ(a,z) = Γ(a) z^a 𝐌(a, a+1, -z)`.
* `lowerIncGamma_add_upperIncGamma`: `γ(a,z) + Γ(a,z) = Γ(a)`.
* `lowerIncGamma_eq_integral`: `γ(a,x) = ∫₀ˣ t^{a-1} e^{-t} dt` for `re a > 0`, with the
  bridge `lowerIncGamma_ofReal` to TauCeti's real lower incomplete Gamma function.
* `upperIncGamma_add_one`, `upperIncGamma_one`, `upperIncGamma_one_half_sq`: recurrence and special
  values.
* `hasAsymptoticExpansion_upperIncGamma`: `Γ(a,x) ~ x^{a-1} e^{-x} ∑ (-1)^k (1-a)_k x^{-k}`.
* `hasAsymptoticExpansion_erfc`: `erfc x ~ e^{-x²}/√π ∑ (-1)^k (1/2)_k x^{-2k-1}`.
-/

@[expose] public section

open Complex Filter MeasureTheory Asymptotics Set
open scoped Real Topology Nat
open DLMF.Hypergeometric

noncomputable section

namespace DLMF.Confluent

/-- Translation of integrals over a right half-line. -/
theorem setIntegral_Ioi_comp_add_right {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (c d : ℝ) : ∫ t in Ioi c, f (t + d) = ∫ s in Ioi (c + d), f s := by
  rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi]
  conv_rhs => rw [← integral_add_right_eq_self (fun s => (Ioi (c + d)).indicator f s) d]
  congr 1
  ext t
  simp only [indicator_apply, mem_Ioi]
  split_ifs with h1 h2 h2 <;> first | rfl | (exfalso; linarith)

/-- `Γ(a,z) = z^a e^{-z} U(1, a+1, z)` (Temme §7.3.7, DLMF 8.5.3 with 13.6.6). -/
theorem upperIncGamma_eq_cpow_mul_kummerU (a : ℂ) {z : ℂ} (hz : z ≠ 0) :
    upperIncGamma a z = z ^ a * exp (-z) * kummerU 1 (a + 1) z := by
  rw [upperIncGamma, kummerU_kummer_transform_all (1 - a) (1 - a) hz,
    show 1 - (1 - a) = a by ring, show 1 - a - (1 - a) + 1 = 1 by ring,
    show 2 - (1 - a) = a + 1 by ring]
  ring

/-- `Γ(a,x) = x^a ∫₁^∞ e^{-xt} t^{a-1} dt` for `x > 0`. -/
theorem upperIncGamma_eq_cpow_mul_integral_Ioi_one (a : ℂ) {x : ℝ} (hx : 0 < x) :
    upperIncGamma a x = (x : ℂ) ^ a * ∫ t in Ioi (1 : ℝ),
        Real.exp (-x * t) • (t : ℂ) ^ (a - 1) := by
  have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  rw [upperIncGamma_eq_cpow_mul_kummerU a hx0, kummerU_laplace (by simp) (by simpa using hx),
    Complex.Gamma_one, div_one]
  have hshift := setIntegral_Ioi_comp_add_right
    (fun s : ℝ => exp (-(x : ℂ) * (s - 1)) * (s : ℂ) ^ (a - 1)) 0 1
  simp only [zero_add] at hshift
  have hcongr : ∫ t in Ioi (0 : ℝ), exp (-(x : ℂ) * t) * (t : ℂ) ^ ((1 : ℂ) - 1) *
      (1 + (t : ℂ)) ^ (a + 1 - 1 - 1) =
      ∫ t in Ioi (0 : ℝ), exp (-(x : ℂ) * ((t + 1 : ℝ) - 1)) * ((t + 1 : ℝ) : ℂ) ^ (a - 1) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    push_cast
    rw [show a + 1 - 1 - 1 = a - 1 by ring, sub_self, Complex.cpow_zero]
    ring_nf
  rw [hcongr, hshift, show (∫ s in Ioi (1 : ℝ), exp (-(x : ℂ) * ((s : ℂ) - 1)) *
      (s : ℂ) ^ (a - 1)) = exp (x : ℂ) * ∫ s in Ioi (1 : ℝ), Real.exp (-x * s) •
        (s : ℂ) ^ (a - 1) by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
    rw [Complex.real_smul, Complex.ofReal_exp, ← mul_assoc, ← Complex.exp_add]
    push_cast
    ring_nf]
  rw [one_mul, show ∀ (A B C D : ℂ), A * B * (C * D) = A * (B * C) * D from
    fun _ _ _ _ => by ring, ← Complex.exp_add]
  simp

/-- **The upper incomplete Gamma integral** (DLMF 8.2.2): `Γ(a,x) = ∫ₓ^∞ t^{a-1} e^{-t} dt`
for `x > 0` and all complex `a`. -/
@[dlmf 8.2.E2]
theorem upperIncGamma_eq_integral (a : ℂ) {x : ℝ} (hx : 0 < x) :
    upperIncGamma a x = ∫ t in Ioi x, (t : ℂ) ^ (a - 1) * Real.exp (-t) := by
  rw [upperIncGamma_eq_cpow_mul_integral_Ioi_one a hx]
  have h := integral_comp_mul_left_Ioi' (fun t : ℝ => (t : ℂ) ^ (a - 1) * Real.exp (-t)) 1 hx
  rw [mul_one] at h
  rw [← h, Complex.real_smul, ← integral_const_mul, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht : (0 : ℝ) < t := lt_trans zero_lt_one ht
  have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  simp only [Complex.real_smul]
  push_cast
  have hxa : (x : ℂ) ^ a = (x : ℂ) * (x : ℂ) ^ (a - 1) := by
    conv_lhs => rw [show a = 1 + (a - 1) by ring]
    rw [Complex.cpow_add _ _ hx0, Complex.cpow_one]
  rw [Complex.mul_cpow_ofReal_nonneg hx.le ht.le, hxa]
  ring_nf

/-- The lower incomplete Gamma function through the regularized Kummer function
(DLMF 8.5.1): `γ(a,z) = Γ(a) z^a 𝐌(a, a+1, -z)`. -/
@[dlmf 8.5.E1]
theorem lowerIncGamma_eq_regularized {a : ℂ} (ha : ∀ k : ℕ, a ≠ -k) (z : ℂ) :
    lowerIncGamma a z = Gamma a * z ^ a * regularizedHGFun {a} {a + 1} (-z) := by
  have ha0 : a ≠ 0 := by simpa using ha 0
  have ha1 : ∀ k : ℕ, a + 1 ≠ -k := fun k hk => ha (k + 1) (by push_cast; linear_combination hk)
  rw [lowerIncGamma, kummerM_eq_mul_regularizedHGFun ha1, Complex.Gamma_add_one a ha0]
  field_simp

/-- The complement relation at nonintegral `a`, from the connection formula for `U`. -/
theorem upperIncGamma_eq_Gamma_sub_of_mem {a : ℂ} (ha : a ∈ integerComplement) (z : ℂ) :
    upperIncGamma a z = Gamma a - lowerIncGamma a z := by
  have hai := forall_of_mem_integerComplement ha
  have hb : ∀ k : ℤ, 1 - a ≠ k := fun k hk => hai (1 - k) (by push_cast; linear_combination -hk)
  have h1a : ∀ k : ℕ, 1 - a ≠ -k := fun k hk => hb (-k) (by push_cast; exact hk)
  have ha1 : ∀ k : ℕ, a + 1 ≠ -k := fun k hk => hai (-k - 1) (by push_cast; linear_combination hk)
  have ha0 : a ≠ 0 := by simpa using hai 0
  have hGm : Gamma (-a) ≠ 0 := Complex.Gamma_ne_zero fun m hm => hai m (by
    push_cast; linear_combination -hm)
  have hG1 : Gamma (1 - a) = -a * Gamma (-a) := by
    rw [show 1 - a = -a + 1 by ring, Complex.Gamma_add_one _ (neg_ne_zero.mpr ha0)]
  rw [upperIncGamma, kummerU_eq_connection _ _ _ hb, kummerUConnection, lowerIncGamma,
    kummerM_kummer_transform ha1, show 1 - (1 - a) = a by ring,
    show 1 - a - (1 - a) + 1 = 1 by ring, show 1 - a - 1 = -a by ring,
    show 2 - (1 - a) = a + 1 by ring, show a + 1 - a = 1 by ring, neg_neg,
    kummerM_self h1a, Complex.Gamma_one, hG1]
  have he : exp (-z) * exp z = 1 := by rw [← Complex.exp_add]; simp
  field_simp
  linear_combination (Gamma a * a) * he

/-- **The complement relation** (DLMF 8.2.3): `γ(a,z) + Γ(a,z) = Γ(a)` for `z ≠ 0` and `a`
not a nonpositive integer. -/
@[dlmf 8.2.E3]
theorem lowerIncGamma_add_upperIncGamma {a : ℂ} (ha : ∀ k : ℕ, a ≠ -k) {z : ℂ}
    (hz : z ≠ 0) : lowerIncGamma a z + upperIncGamma a z = Gamma a := by
  have key : upperIncGamma a z = Gamma a - Gamma a * z ^ a * regularizedHGFun {a} {a + 1} (-z) := by
    refine eq_of_continuousAt_of_integerComplement (f := fun c => upperIncGamma c z)
      (g := fun c => Gamma c - Gamma c * z ^ c * regularizedHGFun {c} {c + 1} (-z)) ?_ ?_
      (fun c hc => ?_)
    · have hU := (continuousAt_kummerU_param (1 - a) (1 - a) hz).comp_of_eq
        (g := fun p : ℂ × ℂ => kummerU p.1 p.2 z)
        (by fun_prop : Continuous fun c : ℂ => (1 - c, 1 - c)).continuousAt rfl
      exact continuousAt_const.mul hU
    · have hG := (Complex.differentiableAt_Gamma a ha).continuousAt
      have hM := (continuous_regularizedConfluent.comp
        (by fun_prop : Continuous fun c : ℂ => (c, c + 1, -z))).continuousAt (x := a)
      exact hG.sub ((hG.mul (continuousAt_const_cpow hz)).mul hM)
    · rw [upperIncGamma_eq_Gamma_sub_of_mem hc z,
        lowerIncGamma_eq_regularized (not_neg_nat_of_mem_integerComplement hc)]
  rw [key, lowerIncGamma_eq_regularized ha]
  ring

/-- The lower incomplete Gamma integral (DLMF 8.2.1): `γ(a,x) = ∫₀ˣ t^{a-1} e^{-t} dt` for
`re a > 0` and `x > 0`. -/
@[dlmf 8.2.E1]
theorem lowerIncGamma_eq_integral {a : ℂ} (ha : 0 < a.re) {x : ℝ} (hx : 0 < x) :
    lowerIncGamma a x = ∫ t in (0 : ℝ)..x, (t : ℂ) ^ (a - 1) * Real.exp (-t) := by
  have ha' : ∀ k : ℕ, a ≠ -k := fun k hk => by
    have := congrArg Complex.re hk
    simp at this
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hsum := lowerIncGamma_add_upperIncGamma ha' (Complex.ofReal_ne_zero.mpr hx.ne')
  have hint : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (a - 1) * Real.exp (-t)) (Ioi 0) :=
    IntegrableOn.congr_fun (Complex.GammaIntegral_convergent ha) (fun t _ => mul_comm _ _)
      measurableSet_Ioi
  have hG : Gamma a = ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (a - 1) * Real.exp (-t) := by
    rw [Complex.Gamma_eq_integral ha, Complex.GammaIntegral]
    exact setIntegral_congr_fun measurableSet_Ioi fun t _ => mul_comm _ _
  rw [upperIncGamma_eq_integral a hx, hG, ← Ioc_union_Ioi_eq_Ioi hx.le,
    setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hint.mono_set Ioc_subset_Ioi_self) (hint.mono_set (Ioi_subset_Ioi hx.le))] at hsum
  rw [intervalIntegral.integral_of_le hx.le]
  linear_combination hsum

/-- The complex lower incomplete Gamma function restricts to TauCeti's real one. -/
theorem lowerIncGamma_ofReal {s x : ℝ} (hs : 0 < s) (hx : 0 < x) :
    lowerIncGamma s x = (TauCeti.lowerIncompleteGamma s x : ℂ) := by
  rw [TauCeti.ofReal_lowerIncompleteGamma_eq_partialGamma hs hx.le, Complex.partialGamma,
    lowerIncGamma_eq_integral (by simpa using hs) hx]
  exact intervalIntegral.integral_congr fun t _ => by push_cast; ring

/-- The recurrence (DLMF 8.8.2): `Γ(a+1,z) = a Γ(a,z) + z^a e^{-z}`. -/
@[dlmf 8.8.E2]
theorem upperIncGamma_add_one (a : ℂ) {z : ℂ} (hz : z ≠ 0) :
    upperIncGamma (a + 1) z = a * upperIncGamma a z + z ^ a * exp (-z) := by
  have h := kummerU_contiguous_shift_a 1 (a + 1) z hz
  rw [sub_self, kummerU_zero] at h
  rw [upperIncGamma_eq_cpow_mul_kummerU _ hz, upperIncGamma_eq_cpow_mul_kummerU _ hz,
    show a + 1 + 1 = a + 1 + 1 by rfl, Complex.cpow_add _ _ hz, Complex.cpow_one]
  linear_combination (-(z ^ a * exp (-z))) * h

/-- `Γ(1,z) = e^{-z}` (DLMF 8.4.5). -/
@[dlmf 8.4.E5]
theorem upperIncGamma_one (z : ℂ) : upperIncGamma 1 z = exp (-z) := by
  simp [upperIncGamma, kummerU_zero]

/-- `Γ(1/2, x²) = √π erfc x` for `x > 0` (DLMF 8.4.6). -/
@[dlmf 8.4.E6]
theorem upperIncGamma_one_half_sq {x : ℝ} (hx : 0 < x) :
    upperIncGamma (1 / 2) ((x : ℂ) ^ 2) = (Real.sqrt π : ℂ) * erfc x := by
  have hxs : (x : ℂ) ∈ slitPlane := Complex.ofReal_mem_slitPlane.mpr hx
  rw [upperIncGamma, show (1 : ℂ) - 1 / 2 = 1 / 2 by norm_num, kummerU_erfc hxs (by simpa using hx)]
  have he : exp (-(x : ℂ) ^ 2) * exp ((x : ℂ) ^ 2) = 1 := by rw [← Complex.exp_add]; simp
  linear_combination ((Real.sqrt π : ℂ) * erfc x) * he

/-- **Asymptotic expansion of `Γ(a,x)`** (DLMF 8.11.2, Temme §7.3.7):
`Γ(a,x) ~ x^{a-1} e^{-x} ∑ (-1)^k (1-a)_k x^{-k}` as `x → +∞`, for all complex `a`. -/
@[dlmf 8.11.E2]
theorem hasAsymptoticExpansion_upperIncGamma (a : ℂ) :
    HasAsymptoticExpansion atTop (fun (k : ℕ) (x : ℝ) => exp (-(x : ℂ)) * (x : ℂ) ^ (a - 1 - k))
      (fun k => (-1) ^ k * poch (1 - a) k) (fun x : ℝ => upperIncGamma a x) := by
  refine (((hasAsymptoticExpansion_kummerU (1 - a) (1 - a)).mul_left
    (fun x : ℝ => exp (-(x : ℂ)))).congr_scale fun k => Eventually.of_forall fun x => ?_
    ).congr_coeff ?_ |>.congr' (Eventually.of_forall fun x => ?_)
  · simp only
    ring_nf
  · funext k
    rw [tricomiCoeff, sub_self, zero_add, poch_nat_one]
    have hf : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
    field_simp
  · simp [upperIncGamma, smul_eq_mul]

/-- **Asymptotic expansion of the complementary error function** (DLMF 7.12.1):
`erfc x ~ e^{-x²}/√π ∑ (-1)^k (1/2)_k x^{-2k-1}` as `x → +∞`. -/
@[dlmf 7.12.E1]
theorem hasAsymptoticExpansion_erfc :
    HasAsymptoticExpansion atTop
      (fun (k : ℕ) (x : ℝ) => exp (-(x : ℂ) ^ 2) * (x : ℂ) ^ (-1 - 2 * (k : ℂ)))
      (fun k => (-1) ^ k * poch (1 / 2) k / (Real.sqrt π : ℂ)) (fun x : ℝ => erfc x) := by
  have hsq : Tendsto (fun x : ℝ => x ^ 2) atTop atTop := tendsto_pow_atTop two_ne_zero
  have hπ : (Real.sqrt π : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have h := ((hasAsymptoticExpansion_upperIncGamma (1 / 2)).comp_tendsto hsq).const_smul
    (1 / (Real.sqrt π : ℂ))
  refine ((h.congr' ?_).congr_scale fun k => ?_).congr_coeff ?_
  · filter_upwards [eventually_gt_atTop 0] with x hx
    simp only [Pi.smul_apply, Function.comp_apply, smul_eq_mul]
    push_cast
    rw [upperIncGamma_one_half_sq hx]
    field_simp
  · filter_upwards [eventually_gt_atTop 0] with x hx
    push_cast
    rw [sq_cpow_of_re_pos (by simpa using hx)]
    ring_nf
  · funext k
    simp only [Pi.smul_apply, smul_eq_mul, show (1 : ℂ) - 1 / 2 = 1 / 2 by norm_num]
    field_simp

end DLMF.Confluent
