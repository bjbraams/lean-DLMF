/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Airy.Framework
public import DLMF.Airy.Relations
public import DLMF.Airy.StieltjesForm
public import DLMF.Confluent.Integrals
public import DLMF.Airy.Bessel

/-!
# Airy expansions on rotated Laplace sectors

Rotated Laplace representations, Airy coefficients and normalized exponential expansions on
closed sectors.

Source references and common attribution are retained in
`DLMF.Airy.Asymptotics`.
-/

@[expose] public noncomputable section

open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF.Confluent

open scoped Real Topology Interval

namespace DLMF.Airy

/-- Airy expansion coefficient u_k, including u_0=1. -/
def airyU (k : ℕ) : ℝ :=
  (ascPochhammer ℝ k).eval (1 / 6) * (ascPochhammer ℝ k).eval (5 / 6) /
    (2 ^ k * k.factorial)
/-- Airy derivative expansion coefficient v_k, including v_0=1. -/
def airyV (k : ℕ) : ℝ := (6 * (k : ℝ) + 1) / (1 - 6 * (k : ℝ)) * airyU k
/-- The Gamma-ratio error multiplier χ. -/
@[dlmf 9.7.E3]
def airyChi (x : ℝ) : ℝ := Real.sqrt π * Real.Gamma (x / 2 + 1) / Real.Gamma (x / 2 + 1 / 2)
/-- Which of the four Airy functions is expanded. -/
inductive AiryKind where
  /-- `Ai`. -/
  | ai
  /-- `Ai'`. -/
  | aiDeriv
  /-- `Bi`. -/
  | bi
  /-- `Bi'`. -/
  | biDeriv
  deriving DecidableEq
/-- The function selected by an Airy expansion index. -/
def airyFunction : AiryKind → ℂ → ℂ
  | .ai => airyAi | .aiDeriv => airyAiDeriv | .bi => airyBi | .biDeriv => airyBiDeriv
/-- The exponential prefactor in DLMF 9.7.5–9.7.8. -/
def airyPrefactor (kind : AiryKind) (z : ℂ) : ℂ :=
  match kind with
  | .ai => exp (-airyZetaComplex z) / (2 * Real.sqrt π * z ^ (1 / 4 : ℂ))
  | .aiDeriv => -z ^ (1 / 4 : ℂ) * exp (-airyZetaComplex z) / (2 * Real.sqrt π)
  | .bi => exp (airyZetaComplex z) / (Real.sqrt π * z ^ (1 / 4 : ℂ))
  | .biDeriv => z ^ (1 / 4 : ℂ) * exp (airyZetaComplex z) / Real.sqrt π
/-- Signed coefficients in the exponential Airy expansions. -/
def airyExpansionCoeff (kind : AiryKind) (k : ℕ) : ℂ :=
  match kind with
  | .ai => (-1 : ℂ) ^ k * airyU k
  | .aiDeriv => (-1 : ℂ) ^ k * airyV k
  | .bi => airyU k
  | .biDeriv => airyV k
/-- A finite, normalized exponential Airy expansion. -/
def airyExponentialSum (kind : AiryKind) (N : ℕ) (z : ℂ) : ℂ :=
  ∑ k ∈ Finset.range N, airyExpansionCoeff kind k / airyZetaComplex z ^ k
/-- The exact normalized remainder, not an arbitrarily chosen error function. -/
def airyRemainder (kind : AiryKind) (N : ℕ) (z : ℂ) : ℂ :=
  airyFunction kind z / airyPrefactor kind z - airyExponentialSum kind N z
/-- Even or odd subseries in an oscillatory expansion. -/
def airyOscSum (derivative : Bool) (parity N : ℕ) (z : ℂ) : ℂ :=
  ∑ k ∈ Finset.range N, (-1 : ℂ) ^ k *
    (if derivative then airyV (2 * k + parity) else airyU (2 * k + parity)) /
      airyZetaComplex z ^ (2 * k + parity)
/-- The algebraic prefactor of a negative-axis expansion. -/
def airyOscPrefactor (kind : AiryKind) (z : ℂ) : ℂ :=
  match kind with
  | .ai | .bi => 1 / (Real.sqrt π * z ^ (1 / 4 : ℂ))
  | .aiDeriv | .biDeriv => z ^ (1 / 4 : ℂ) / Real.sqrt π
/-- The two separately truncated oscillatory series, with the stated sine/cosine signs. -/
def airyOscApprox (kind : AiryKind) (N M : ℕ) (z : ℂ) : ℂ :=
  let θ := airyZetaComplex z - π / 4
  airyOscPrefactor kind z * match kind with
    | .ai => cos θ * airyOscSum false 0 N z + sin θ * airyOscSum false 1 M z
    | .aiDeriv => sin θ * airyOscSum true 0 N z - cos θ * airyOscSum true 1 M z
    | .bi => -sin θ * airyOscSum false 0 N z + cos θ * airyOscSum false 1 M z
    | .biDeriv => cos θ * airyOscSum true 0 N z + sin θ * airyOscSum true 1 M z
/-- A positive error envelope; it does not divide by an oscillatory leading term. -/
def airyOscError (kind : AiryKind) (N M : ℕ) (z : ℂ) : ℝ :=
  ‖airyOscPrefactor kind z‖ * Real.exp |(airyZetaComplex z).im| *
    (‖airyZetaComplex z‖ ^ (-(2 * N : ℤ)) + ‖airyZetaComplex z‖ ^ (-(2 * M + 1 : ℤ)))
/-- Rotated Bi approximations on their two Stokes rays. -/
def airyRotatedBiApprox (derivative : Bool) (ε : ℝ) (N M : ℕ) (z : ℂ) : ℂ :=
  let θ := airyZetaComplex z - π / 4 - ε * I * Real.log 2 / 2
  if derivative then
    (2 / π : ℂ) ^ (1 / 2 : ℂ) * exp (-ε * (π * I / 6)) * z ^ (1 / 4 : ℂ) *
      (-sin θ * airyOscSum true 0 N z + cos θ * airyOscSum true 1 M z)
  else
    (2 / π : ℂ) ^ (1 / 2 : ℂ) * exp (ε * (π * I / 6)) * z ^ (-1 / 4 : ℂ) *
      (cos θ * airyOscSum false 0 N z + sin θ * airyOscSum false 1 M z)
/-- The piecewise complex error multiplier in 9.7.17; the phase of ζ is inherited from z.
On the ray `|arg z| = 2π/3` we have `sin(ph ζ) = 0`, and DLMF's `min(|csc(ph ζ)|, χ + 1)` is
`χ + 1`; the case is written out because Lean's `0⁻¹ = 0` would give `0` (corrected 2026-10-21).
The last case is used only for `2π/3 < |arg z| < π`: the 9.7.17 statements assume
`z ∈ slitPlane`, which excludes `|arg z| = π`, where `cos(ph ζ) = 0` and DLMF gives no bound. -/
@[dlmf 9.7.E17]
def airyErrorMultiplier (n : ℕ) (σ : ℝ) (z : ℂ) : ℝ :=
  if |arg z| ≤ π / 3 then 1 else
  if |arg z| ≤ 2 * π / 3 then
    (if Real.sin (3 * arg z / 2) = 0 then airyChi (n + σ) + 1
      else min |(Real.sin (3 * arg z / 2))⁻¹| (airyChi (n + σ) + 1)) else
    Real.sqrt (2 * π * (n + σ)) / |Real.cos (3 * arg z / 2)| ^ ((n : ℝ) + σ) + airyChi (n + σ) + 1
/-- The terminant, with an explicit logarithmic argument to retain the Gamma branch. -/
@[dlmf 9.7.E22]
def airyTerminator (p w : ℂ) : ℂ := exp (exp w) / (2 * π) * Gamma p * airyUpperGammaOnLog (1 - p) w
/-- The near-optimal exponential truncation index. -/
def airyOptimalIndex (z : ℂ) : ℕ := ⌊2 * ‖airyZetaComplex z‖⌋₊
/-- Exact second-level remainder after re-expanding the normalized Ai remainder. -/
def airyHyperRemainder (derivative : Bool) (m n : ℕ) (z : ℂ) : ℂ :=
  airyRemainder (if derivative then .aiDeriv else .ai) n z -
    (-1 : ℂ) ^ (if derivative then n - 1 else n) *
      ∑ k ∈ Finset.range m, (-1 : ℂ) ^ k * (if derivative then airyV k else airyU k) *
        airyTerminator ((n : ℂ) - k) (log 2 + airyLogZeta z) / airyZetaComplex z ^ k

/-- The recurrence for `u_k`, cleared of denominators and cast to `ℂ`. -/
theorem airyU_succ_mul (k : ℕ) :
    (airyU (k + 1) : ℂ) * ((2 * k + 1) * 216 * (k + 1)) =
      (6 * k + 1) * (6 * k + 3) * (6 * k + 5) * airyU k := by
  have h' : airyU (k + 1) * ((2 * k + 1) * 216 * (k + 1)) =
      (6 * k + 1) * (6 * k + 3) * (6 * k + 5) * airyU k := by
    simp only [airyU, ascPochhammer_succ_eval, pow_succ, Nat.factorial_succ, Nat.cast_mul,
      Nat.cast_add, Nat.cast_one]
    have hk : (k.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
    have hp : (2 : ℝ) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
    have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    ring
  exact_mod_cast h'

/-- `u_k · 216^k k! · ∏_{j<k}(2j+1) = ∏_{j<3k}(2j+1)`. -/
theorem airyU_mul_oddProd (k : ℕ) :
    (airyU k : ℂ) * ((216 : ℂ) ^ k * k.factorial) * ∏ j ∈ Finset.range k, (2 * (j : ℂ) + 1) =
      ∏ j ∈ Finset.range (3 * k), (2 * (j : ℂ) + 1) := by
  induction k with
  | zero => simp [airyU]
  | succ k ih =>
    rw [show 3 * (k + 1) = 3 * k + 1 + 1 + 1 by ring, Finset.prod_range_succ,
      Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ, ← ih,
      Nat.factorial_succ]
    push_cast
    linear_combination (216 ^ k * (k.factorial : ℂ) * ∏ j ∈ Finset.range k, (2 * (j : ℂ) + 1)) *
      airyU_succ_mul k

/-- The product form `u_k = ∏_{j<2k} (2k + 1 + 2j) / (216^k k!)` of the Airy coefficients
(DLMF 9.7.2). -/
@[dlmf 9.7.E2]
theorem airyU_product (k : ℕ) :
    (airyU k : ℂ) = (∏ j ∈ Finset.range (2 * k), (2 * (k : ℂ) + 1 + 2 * j)) /
      ((216 : ℂ) ^ k * k.factorial) := by
  have h := airyU_mul_oddProd k
  rw [show 3 * k = k + 2 * k by ring, Finset.prod_range_add] at h
  have hQ : ∏ j ∈ Finset.range k, (2 * (j : ℂ) + 1) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j _ => by norm_cast
  have hD : (216 : ℂ) ^ k * k.factorial ≠ 0 := by
    have : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) this
  rw [eq_div_iff hD]
  apply mul_right_cancel₀ hQ
  rw [h, mul_comm (∏ j ∈ Finset.range k, _)]
  congr 1
  refine Finset.prod_congr rfl fun j _ => ?_
  push_cast; ring

/-- The recurrence `u_{k+1} = (6k+1)(6k+3)(6k+5) / ((2k+1) 216 (k+1)) · u_k` (DLMF 9.7.2). -/
@[dlmf 9.7.E2]
theorem airyU_recurrence (k : ℕ) :
    airyU (k + 1) = ((6 * (k : ℝ) + 1) * (6 * k + 3) * (6 * k + 5)) /
      ((2 * k + 1) * 216 * (k + 1)) * airyU k := by
  simp only [airyU, ascPochhammer_succ_eval, pow_succ, Nat.factorial_succ, Nat.cast_mul,
    Nat.cast_add, Nat.cast_one]
  have hk : (k.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  have hp : (2 : ℝ) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
  have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
  have h2k : 2 * (k : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

/-- `χ(x) ∼ √(πx/2)` as `x → ∞` (DLMF 9.7.4). -/
@[dlmf 9.7.E4]
theorem airyChi_isEquivalent  :
    (fun x : ℝ => airyChi x) ~[atTop] (fun x => Real.sqrt (π * x / 2)) := by
  have h := (DLMF.Gamma.Gamma_ratio_power (a := 1) (b := 1 / 2)).comp
    (tendsto_id.atTop_div_const (by norm_num : (0 : ℝ) < 2))
  have h' := (Complex.continuous_re.tendsto _).comp h
  simp only [Complex.one_re] at h'
  refine isEquivalent_of_tendsto_one ?_
  apply h'.congr'
  filter_upwards [eventually_gt_atTop 0] with x hx
  have hx2 : (0 : ℝ) ≤ x / 2 := by positivity
  simp only [Function.comp_apply, id]
  have e1 : ((x / 2 : ℝ) : ℂ) + 1 = ((x / 2 + 1 : ℝ) : ℂ) := by push_cast; ring
  have e2 : ((x / 2 : ℝ) : ℂ) + 1 / 2 = ((x / 2 + 1 / 2 : ℝ) : ℂ) := by push_cast; ring
  have e3 : ((x / 2 : ℝ) : ℂ) ^ ((1 : ℂ) - 1 / 2) = ((Real.sqrt (x / 2) : ℝ) : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hx2]; norm_num
  rw [e1, e2, e3, Complex.Gamma_ofReal, Complex.Gamma_ofReal, ← Complex.ofReal_div,
    ← Complex.ofReal_div, Complex.ofReal_re]
  simp only [Pi.div_apply]
  rw [airyChi,
    show π * x / 2 = π * (x / 2) by ring, Real.sqrt_mul Real.pi_pos.le]
  have hs : Real.sqrt π ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  field_simp

/-! ### Rotated Laplace integrals and the exponential expansions (DLMF 9.7.5–9.7.14)

The principal-branch Kummer `U` representation gives the expansion of `Ai` only for
`|arg z| < 2π/3`. To reach the full sector `|arg z| ≤ π - δ` we use the Laplace integrals of
`t^{a-1}(1+t)^β` along rotated rays `arg t = θ`, `θ ∈ (-π, π)`, identify them with `Ai` by the
identity theorem, and glue finitely many sectors. The expansions of `Bi`, `Bi'` and the
oscillatory and Stokes-ray expansions then follow from the connection formulas.
-/

/-- The kernel `t^{a-1} (1+t)^β` of the rotated Laplace integrals for the Airy functions. -/
def airyRot_kernel (a β : ℝ) (t : ℂ) : ℂ := t ^ ((a : ℂ) - 1) * (1 + t) ^ (β : ℂ)

/-- The Laplace transform of the kernel along the ray `arg t = θ`, in the rotated variable. -/
def airyRot_lap (a β θ : ℝ) (W : ℂ) : ℂ :=
  ∫ r in Ioi (0 : ℝ), Complex.exp (-(W * r)) • airyRot_kernel a β (r * exp (θ * I))

/-- `r e^{iu} ≠ 0` for `r > 0`. -/
theorem airyRot_ofReal_mul_exp_ne_zero {r : ℝ} (hr : 0 < r) (u : ℝ) :
    (r : ℂ) * exp (u * I) ≠ 0 :=
  mul_ne_zero (ofReal_ne_zero.mpr hr.ne') (exp_ne_zero _)

/-- `arg (r e^{iu}) = u` for `r > 0`, `u ∈ (-π, π]`. -/
theorem airyRot_arg {r : ℝ} (hr : 0 < r) {u : ℝ} (h1 : -π < u) (h2 : u ≤ π) :
    arg ((r : ℂ) * exp (u * I)) = u := by
  rw [exp_mul_I]
  exact arg_mul_cos_add_sin_mul_I hr ⟨h1, h2⟩

/-- `r e^{iu}` lies in the slit plane for `r > 0`, `|u| < π`. -/
theorem airyRot_mem_slitPlane {r : ℝ} (hr : 0 < r) {u : ℝ} (hu : |u| < π) :
    (r : ℂ) * exp (u * I) ∈ slitPlane := by
  rw [mem_slitPlane_iff_arg]
  refine ⟨?_, airyRot_ofReal_mul_exp_ne_zero hr u⟩
  rw [airyRot_arg hr (by linarith [neg_abs_le u]) (by linarith [le_abs_self u])]
  exact (by linarith [le_abs_self u] : u < π).ne

/-- The kernel is holomorphic at `r e^{iu}`, `r > 0`, `|u| < π`. -/
theorem airyRot_differentiableAt_kernel (a β : ℝ) {r : ℝ} (hr : 0 < r) {u : ℝ} (hu : |u| < π) :
    DifferentiableAt ℂ (airyRot_kernel a β) ((r : ℂ) * exp (u * I)) := by
  unfold airyRot_kernel
  exact (differentiableAt_id.cpow (differentiableAt_const _) (airyRot_mem_slitPlane hr hu)).mul
    ((differentiableAt_const _ |>.add differentiableAt_id).cpow (differentiableAt_const _)
      (airySt_one_add_mem hr.le hu))

/-- The kernel along a ray is continuous on `(0, ∞)`. -/
theorem airyRot_continuousOn_kernel (a β : ℝ) {θ : ℝ} (hθ : |θ| < π) :
    ContinuousOn (fun r : ℝ => airyRot_kernel a β ((r : ℂ) * exp (θ * I))) (Ioi 0) :=
  fun r hr => (ContinuousAt.comp (g := airyRot_kernel a β) (f := fun r : ℝ => (r : ℂ) * exp (θ * I))
    (airyRot_differentiableAt_kernel a β hr hθ).continuousAt
    (by fun_prop : Continuous fun r : ℝ => (r : ℂ) * exp (θ * I)).continuousAt).continuousWithinAt

/-- Uniform bound for the kernel on a closed sector `|u| ≤ Φ < π`. -/
theorem airyRot_kernel_bound (a β : ℝ) {Φ : ℝ} (hΦ : Φ < π) :
    ∃ C > 0, ∀ r : ℝ, 0 < r → ∀ u : ℝ, |u| ≤ Φ →
      ‖airyRot_kernel a β (r * exp (u * I))‖ ≤ C * (r ^ (a - 1) * (1 + r) ^ |β|) := by
  obtain ⟨c, hc, hcle⟩ := Complex.exists_pos_le_norm_one_add_ofReal_mul_exp hΦ
  have hc' : 0 < min c 1 := lt_min hc one_pos
  refine ⟨(min c 1) ^ (-|β|), by positivity, fun r hr u hu => ?_⟩
  have hc'1 : min c 1 ≤ 1 := min_le_right _ _
  have h1 : min c 1 ≤ ‖1 + (r : ℂ) * exp (u * I)‖ := (min_le_left _ _).trans (hcle r hr.le u hu)
  have h2 : ‖1 + (r : ℂ) * exp (u * I)‖ ≤ 1 + r := by
    refine (norm_add_le _ _).trans ?_; rw [norm_one, Complex.norm_ofReal_mul_exp_ofReal_mul_I hr.le]
  rw [airyRot_kernel, norm_mul, show ((a : ℂ) - 1) = ((a - 1 : ℝ) : ℂ) by push_cast; ring,
    norm_cpow_real, norm_cpow_real, Complex.norm_ofReal_mul_exp_ofReal_mul_I hr.le]
  have hr1 : 1 ≤ 1 + r := by linarith
  have hb : ‖1 + (r : ℂ) * exp (u * I)‖ ^ β ≤ (min c 1) ^ (-|β|) * (1 + r) ^ |β| := by
    rcases le_total 0 β with hβ | hβ
    · rw [abs_of_nonneg hβ]
      calc ‖1 + (r : ℂ) * exp (u * I)‖ ^ β ≤ (1 + r) ^ β :=
            Real.rpow_le_rpow (norm_nonneg _) h2 hβ
        _ ≤ (min c 1) ^ (-β) * (1 + r) ^ β := by
            refine le_mul_of_one_le_left (by positivity) ?_
            exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos hc' hc'1 (by linarith)
    · rw [abs_of_nonpos hβ, neg_neg]
      calc ‖1 + (r : ℂ) * exp (u * I)‖ ^ β ≤ (min c 1) ^ β :=
            Real.rpow_le_rpow_of_nonpos hc' h1 hβ
        _ ≤ (min c 1) ^ β * (1 + r) ^ (-β) := by
            refine le_mul_of_one_le_right (by positivity) ?_
            exact Real.one_le_rpow hr1 (by linarith)
  have hra := Real.rpow_nonneg hr.le (a - 1)
  calc r ^ (a - 1) * ‖1 + (r : ℂ) * exp (u * I)‖ ^ β
      ≤ r ^ (a - 1) * ((min c 1) ^ (-|β|) * (1 + r) ^ |β|) := by gcongr
    _ = _ := by ring

/-- The damped kernel along a ray is integrable on `(0, ∞)`. -/
theorem airyRot_integrableOn (a β : ℝ) (ha : 0 < a) {θ : ℝ} (hθ : |θ| < π) {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun r : ℝ => Real.exp (-c * r) • airyRot_kernel a β ((r : ℂ) * exp (θ * I)))
      (Ioi 0) := by
  obtain ⟨C, hC, hb⟩ := airyRot_kernel_bound a β (Φ := |θ|) hθ
  obtain ⟨N, hN⟩ : ∃ N : ℕ, |β| ≤ N := ⟨⌈|β|⌉₊, Nat.le_ceil _⟩
  refine Integrable.mono' ((integrableOn_exp_mul_rpow_mul_one_add_pow (s := a - 1) (by linarith)
    hc N).const_mul C) ?_ ?_
  · exact (((by fun_prop : Continuous fun r : ℝ => Real.exp (-c * r)).continuousOn).smul
      (airyRot_continuousOn_kernel a β hθ)).aestronglyMeasurable measurableSet_Ioi
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun r hr => ?_)
    have hr : (0 : ℝ) < r := hr
    rw [norm_smul, Real.norm_eq_abs, Real.abs_exp]
    have h1 := hb r hr θ le_rfl
    have h2 : (1 + r) ^ |β| ≤ (1 + r) ^ (N : ℕ) := by
      rw [← Real.rpow_natCast]; exact Real.rpow_le_rpow_of_exponent_le (by linarith) hN
    have hra := Real.rpow_nonneg hr.le (a - 1)
    calc Real.exp (-c * r) * ‖airyRot_kernel a β ((r : ℂ) * exp (θ * I))‖
        ≤ Real.exp (-c * r) * (C * (r ^ (a - 1) * (1 + r) ^ |β|)) := by gcongr
      _ ≤ Real.exp (-c * r) * (C * (r ^ (a - 1) * (1 + r) ^ N)) := by gcongr
      _ = C * (Real.exp (-c * r) * r ^ (a - 1) * (1 + r) ^ N) := by ring

/-- The rotated Laplace transform is holomorphic on the right half-plane. -/
theorem airyRot_differentiableOn_lap (a β : ℝ) (ha : 0 < a) {θ : ℝ} (hθ : |θ| < π) :
    DifferentiableOn ℂ (airyRot_lap a β θ) {W : ℂ | 0 < W.re} := by
  intro W hW
  have hW : 0 < W.re := hW
  have h := differentiableOn_integral_cexp_neg_mul_smul
    (airyRot_integrableOn a β ha hθ (half_pos hW))
  exact (h.differentiableAt ((isOpen_lt continuous_const continuous_re).mem_nhds
    (show W.re / 2 < W.re by linarith))).differentiableWithinAt

/-- Rotation of the ray of integration from `0` to `θ`, `|θ| < π`. -/
theorem airyRot_lap_rotate (a β : ℝ) (ha : 0 < a) {θ : ℝ} (hθ : |θ| < π) {w : ℂ}
    (hw : ∀ y ∈ [[0, θ]], 0 < (w * exp (y * I)).re) :
    ∫ t in Ioi (0 : ℝ), Complex.exp (-(w * t)) * airyRot_kernel a β t =
      exp (θ * I) * airyRot_lap a β θ (w * exp (θ * I)) := by
  obtain ⟨C, hC, hb⟩ := airyRot_kernel_bound a β (Φ := |θ|) hθ
  have hy : ∀ y ∈ [[0, θ]], |y| ≤ |θ| := fun y hy => abs_le_abs_of_mem_uIcc_zero hy
  have h := integral_cexp_neg_mul_mul_eq_rotate (F := airyRot_kernel a β) (θ := θ) (σ := a)
    (C := C * 2 ^ |β|) (k := a - 1 + |β|) (z := w) ha ?_ ?_ ?_ hw
  · rw [h, airyRot_lap]
    rfl
  · intro r hr y hy'
    exact airyRot_differentiableAt_kernel a β hr ((hy y hy').trans_lt hθ)
  · intro r hr hr1 y hy'
    refine (hb r hr y (hy y hy')).trans ?_
    have : (1 + r) ^ |β| ≤ 2 ^ |β| :=
      Real.rpow_le_rpow (by linarith) (by linarith) (abs_nonneg _)
    have hra := Real.rpow_nonneg hr.le (a - 1)
    calc C * (r ^ (a - 1) * (1 + r) ^ |β|) ≤ C * (r ^ (a - 1) * 2 ^ |β|) := by gcongr
      _ = C * 2 ^ |β| * r ^ (a - 1) := by ring
  · intro r hr y hy'
    have hr0 : 0 < r := by linarith
    refine (hb r hr0 y (hy y hy')).trans ?_
    have h2 : (1 + r) ^ |β| ≤ (2 * r) ^ |β| :=
      Real.rpow_le_rpow (by linarith) (by linarith) (abs_nonneg _)
    rw [Real.mul_rpow (by norm_num) hr0.le] at h2
    have hra := Real.rpow_nonneg hr0.le (a - 1)
    calc C * (r ^ (a - 1) * (1 + r) ^ |β|) ≤ C * (r ^ (a - 1) * (2 ^ |β| * r ^ |β|)) := by
          gcongr
      _ = C * 2 ^ |β| * r ^ (a - 1 + |β|) := by rw [Real.rpow_add hr0]; ring

/-- **Watson's lemma** for the rotated Airy kernel, in the rotated variable. -/
theorem airyRot_hasAsymptoticExpansion (a β : ℝ) (ha : 0 < a) {θ : ℝ} (hθ : |θ| < π) {δ : ℝ}
    (hδ : 0 < δ) :
    HasAsymptoticExpansion (sectorAtTop δ) (fun (n : ℕ) (W : ℂ) => W ^ (-((n : ℂ) + a)))
      (fun n => Complex.Gamma ((n : ℂ) + a) • exp (θ * I * ((n : ℂ) + a)) •
        Ring.choose (β : ℂ) n)
      (fun W => exp (θ * I) • airyRot_lap a β θ W) := by
  have hθ1 : -π < θ := by linarith [neg_abs_le θ]
  have hθ2 : θ ≤ π := by linarith [le_abs_self θ]
  refine hasAsymptoticExpansion_integral_cexp_smul_rotate (c := 1) (μ := (a : ℂ)) hθ1 hθ2
    (by simpa using ha) hδ (airyRot_integrableOn a β ha hθ one_pos) fun N => ?_
  have hbin := one_add_mul_cpow_sub_sum_isBigO (exp (θ * I)) (β : ℂ) N
  have hpow : (fun r : ℝ => ((r : ℂ) * exp (θ * I)) ^ ((a : ℂ) - 1)) =O[𝓝[>] 0]
      fun r : ℝ => r ^ (a - 1) := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hr : (0 : ℝ) < r := hr
    rw [show ((a : ℂ) - 1) = ((a - 1 : ℝ) : ℂ) by push_cast; ring, norm_cpow_real,
      Complex.norm_ofReal_mul_exp_ofReal_mul_I hr.le, one_mul,
      Real.norm_of_nonneg (Real.rpow_nonneg hr.le _)]
  refine (hpow.mul hbin).congr' ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with r hr
    have hr : (0 : ℝ) < r := hr
    have ht := airyRot_ofReal_mul_exp_ne_zero hr θ
    simp only [airyRot_kernel, smul_eq_mul, mul_sub, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [show ((n : ℂ) + (a : ℂ) - 1) = ((a : ℂ) - 1) + n by ring, cpow_add _ _ ht, cpow_natCast]
    ring
  · filter_upwards [self_mem_nhdsWithin] with r hr
    have hr : (0 : ℝ) < r := hr
    simp only [ofReal_re]
    rw [show (N : ℝ) + a - 1 = (a - 1) + N by ring, Real.rpow_add hr, Real.rpow_natCast]

/-! ### Continuation of the Airy–Tricomi representation to rotated sectors -/

/-- `airyLogZeta` is holomorphic on the slit plane. -/
theorem airyRot_differentiableAt_logZeta {z : ℂ} (hz : z ∈ slitPlane) :
    DifferentiableAt ℂ airyLogZeta z := by
  unfold airyLogZeta
  exact (differentiableAt_const _).add ((differentiableAt_const _).mul (differentiableAt_log hz))

/-- `ζ` is holomorphic on the slit plane. -/
theorem airyRot_differentiableAt_zeta {z : ℂ} (hz : z ∈ slitPlane) :
    DifferentiableAt ℂ airyZetaComplex z := by
  unfold airyZetaComplex
  exact (differentiableAt_const _).mul (differentiableAt_id.cpow (differentiableAt_const _) hz)

/-- `2ζ e^{iy} = exp (log 2 + L + iy)`. -/
theorem airyRot_two_zeta_mul_exp {z : ℂ} (hz : z ≠ 0) (y : ℝ) :
    2 * airyZetaComplex z * exp (y * I) = exp (log 2 + airyLogZeta z + y * I) := by
  rw [exp_add, exp_log_two_add_airyLogZeta hz]

/-- The real part of `exp (log 2 + L + iy)`. -/
theorem airyRot_re_W (z : ℂ) (y : ℝ) :
    (exp (log 2 + airyLogZeta z + y * I)).re =
      Real.exp (log 2 + airyLogZeta z).re * Real.cos (3 / 2 * arg z + y) := by
  rw [Complex.exp_re]
  congr 2
  · simp
  · rw [add_im, im_log_two_add_airyLogZeta]
    simp

/-- `Re (2 e^{ζ̃(z)} e^{iy}) > 0` when `|(3/2) arg z + y| < π/2`, with `ζ̃` the log-plane `ζ`. -/
theorem airyRot_re_W_pos (z : ℂ) {y : ℝ} (hy : |3 / 2 * arg z + y| < π / 2) :
    0 < (exp (log 2 + airyLogZeta z + y * I)).re := by
  rw [airyRot_re_W]
  refine mul_pos (Real.exp_pos _) (Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩) <;>
    linarith [abs_lt.mp hy]

/-- The rotated Tricomi integral `A e^{pL - ζ} Γ(a)⁻¹ e^{iθ} L_θ(2 e^{ζ̃ + iθ})` is holomorphic on
the part of the slit plane where `Re (2 e^{ζ̃(z) + iθ}) > 0`. -/
private lemma airyRot_rot_differentiableOn (A p : ℂ) (a β : ℝ) (ha : 0 < a) {θ : ℝ}
    (hθ : |θ| < π) :
    DifferentiableOn ℂ (fun z => A * exp (p * airyLogZeta z - airyZetaComplex z) *
      (1 / Gamma a * (exp (θ * I) * airyRot_lap a β θ (exp (log 2 + airyLogZeta z + θ * I)))))
      (slitPlane ∩ (fun w => exp (log 2 + airyLogZeta w + θ * I)) ⁻¹' {W : ℂ | 0 < W.re}) := by
  intro w hw
  refine DifferentiableAt.differentiableWithinAt ?_
  have hW : DifferentiableAt ℂ (fun w => exp (log 2 + airyLogZeta w + θ * I)) w :=
    (((differentiableAt_const _).add (airyRot_differentiableAt_logZeta hw.1)).add
      (differentiableAt_const _)).cexp
  have hL := ((airyRot_differentiableOn_lap a β ha hθ).differentiableAt
    ((isOpen_lt continuous_const continuous_re).mem_nhds hw.2)).comp w hW
  exact ((differentiableAt_const _).mul (((differentiableAt_const _).mul
    (airyRot_differentiableAt_logZeta hw.1)).sub (airyRot_differentiableAt_zeta hw.1)).cexp).mul
    ((differentiableAt_const _).mul ((differentiableAt_const _).mul hL))

/-- **The Airy–Tricomi representation in a rotated sector.** If an entire function `f` equals
`A e^{pL - ζ} Γ(a)⁻¹ ∫₀^∞ e^{-2ζt} t^{a-1}(1+t)^β dt` for `|arg z| < π/3`, then, for every
`|θ| < π`, it equals the rotated integral on the whole open sector `|(3/2) arg z + θ| < π/2`. -/
theorem airyRot_eq_of_anchor {f : ℂ → ℂ} (hf : Differentiable ℂ f) (A p : ℂ) (a β : ℝ)
    (ha : 0 < a)
    (hanchor : ∀ z : ℂ, z ≠ 0 → |arg z| < π / 3 → f z =
      A * exp (p * airyLogZeta z - airyZetaComplex z) * (1 / Gamma a *
        ∫ t in Ioi (0 : ℝ), Complex.exp (-(2 * airyZetaComplex z * t)) * airyRot_kernel a β t))
    {θ : ℝ} (hθ : |θ| < π) {z : ℂ} (hz : z ≠ 0) (hzθ : |3 / 2 * arg z + θ| < π / 2) :
    f z = A * exp (p * airyLogZeta z - airyZetaComplex z) *
      (1 / Gamma a * (exp (θ * I) * airyRot_lap a β θ (exp (log 2 + airyLogZeta z + θ * I)))) := by
  have hπ := Real.pi_pos
  have hθ' := abs_lt.mp hθ
  set g : ℂ → ℂ := fun z => A * exp (p * airyLogZeta z - airyZetaComplex z) *
      (1 / Gamma a * (exp (θ * I) * airyRot_lap a β θ (exp (log 2 + airyLogZeta z + θ * I))))
    with hg
  set α1 : ℝ := 2 / 3 * (-(π / 2) - θ)
  set α2 : ℝ := 2 / 3 * (π / 2 - θ)
  set U : Set ℂ := (fun q : ℝ × ℝ => (q.1 : ℂ) * exp (q.2 * I)) '' (Ioi 0 ×ˢ Ioo α1 α2) with hU
  have hUc : IsPreconnected U :=
    (isPreconnected_Ioi.prod isPreconnected_Ioo).image _ (by fun_prop : Continuous
      fun q : ℝ × ℝ => (q.1 : ℂ) * exp (q.2 * I)).continuousOn
  have hmemU : ∀ w : ℂ, w ≠ 0 → |3 / 2 * arg w + θ| < π / 2 → w ∈ U := by
    intro w hw hwθ
    refine ⟨(‖w‖, arg w), ⟨norm_pos_iff.mpr hw, ?_, ?_⟩, norm_mul_exp_arg_mul_I w⟩ <;>
      simp only [α1, α2] <;> linarith [abs_lt.mp hwθ]
  have hUsub : ∀ w ∈ U, w ∈ slitPlane ∧ |3 / 2 * arg w + θ| < π / 2 := by
    rintro w ⟨⟨r, u⟩, ⟨hr, hu1, hu2⟩, rfl⟩
    simp only [α1, α2] at hu1 hu2
    have hr' : (0 : ℝ) < r := hr
    have hu : |u| < π := abs_lt.mpr ⟨by linarith, by linarith⟩
    refine ⟨airyRot_mem_slitPlane hr' hu, ?_⟩
    simp only
    rw [airyRot_arg hr' (by linarith) (by linarith)]
    exact abs_lt.mpr ⟨by linarith, by linarith⟩
  -- the open set where `g` is holomorphic
  set O : Set ℂ := slitPlane ∩ (fun w => exp (log 2 + airyLogZeta w + θ * I)) ⁻¹'
    {W : ℂ | 0 < W.re} with hO
  have hWc : ContinuousOn (fun w => exp (log 2 + airyLogZeta w + θ * I)) slitPlane := fun w hw =>
    ((((differentiableAt_const _).add (airyRot_differentiableAt_logZeta hw)).add
      (differentiableAt_const _)).cexp).continuousAt.continuousWithinAt
  have hOo : IsOpen O := hWc.isOpen_inter_preimage isOpen_slitPlane
    (isOpen_lt continuous_const continuous_re)
  have hgd : DifferentiableOn ℂ g O := airyRot_rot_differentiableOn A p a β ha hθ
  have hUO : U ⊆ O := fun w hw => ⟨(hUsub w hw).1, airyRot_re_W_pos w (hUsub w hw).2⟩
  have hfa : AnalyticOnNhd ℂ f U := fun w _ => hf.analyticAt w
  have hga : AnalyticOnNhd ℂ g U := fun w hw => hgd.analyticOnNhd hOo w (hUO hw)
  -- the base point and the eventual equality
  set z0 : ℂ := ((1 : ℝ) : ℂ) * exp ((-(θ / 3) : ℝ) * I) with hz0
  have hz0U : z0 ∈ U := ⟨(1, -(θ / 3)), ⟨(one_pos : (0:ℝ) < 1), by simp only [α1]; linarith,
    by simp only [α2]; linarith⟩, rfl⟩
  have harg0 : arg z0 = -(θ / 3) := airyRot_arg one_pos (by linarith) (by linarith)
  set V : Set ℂ := slitPlane ∩ arg ⁻¹' {u : ℝ | |u| < π / 3 ∧ |3 / 2 * u + θ| < π / 2} with hV
  have hargc : ContinuousOn arg slitPlane := fun w hw => (continuousAt_arg hw).continuousWithinAt
  have hVo : IsOpen V := hargc.isOpen_inter_preimage isOpen_slitPlane
    ((isOpen_lt (continuous_abs) continuous_const).inter
      (isOpen_lt (by fun_prop : Continuous fun u : ℝ => |3 / 2 * u + θ|) continuous_const))
  have hz0V : z0 ∈ V := by
    refine ⟨(hUsub z0 hz0U).1, ?_, ?_⟩ <;> simp only [harg0] <;>
      rw [abs_lt] <;> constructor <;> linarith
  have hev : f =ᶠ[𝓝 z0] g := by
    filter_upwards [hVo.mem_nhds hz0V] with w hw
    obtain ⟨hws, hw1, hw2⟩ := hw
    have hw0 : w ≠ 0 := slitPlane_ne_zero hws
    rw [hanchor w hw0 hw1]
    simp only [hg]
    congr 2
    rw [← airyRot_two_zeta_mul_exp hw0 θ]
    refine airyRot_lap_rotate a β ha hθ fun y hy => ?_
    rw [airyRot_two_zeta_mul_exp hw0 y]
    refine airyRot_re_W_pos w ?_
    have h1 := abs_lt.mp hw1
    have h2 := abs_lt.mp hw2
    rcases le_total 0 θ with h | h
    · rw [uIcc_of_le h] at hy
      exact abs_lt.mpr ⟨by linarith [hy.1, hy.2], by linarith [hy.1, hy.2]⟩
    · rw [uIcc_of_ge h] at hy
      exact abs_lt.mpr ⟨by linarith [hy.1, hy.2], by linarith [hy.1, hy.2]⟩
  exact hfa.eqOn_of_preconnected_of_eventuallyEq hga hUc hz0U hev (hmemU z hz hzθ)

/-- `re (2ζ) > 0` for `|arg z| < π/3`. -/
theorem airyRot_re_two_zeta_pos {z : ℂ} (hz : z ≠ 0) (harg : |arg z| < π / 3) :
    0 < (2 * airyZetaComplex z).re := by
  have h := airyRot_re_W_pos z (y := 0) (by rw [add_zero, abs_mul]; norm_num; linarith)
  rwa [← airyRot_two_zeta_mul_exp hz 0, ofReal_zero, zero_mul, exp_zero, mul_one] at h

/-- The anchor for `Ai`: Tricomi's Laplace integral on `|arg z| < π/3`. -/
theorem airyRot_airyAi_anchor {z : ℂ} (hz : z ≠ 0) (harg : |arg z| < π / 3) :
    airyAi z = ((3 : ℂ) ^ (-1 / 6 : ℂ) / Real.sqrt π) *
      exp ((2 / 3) * airyLogZeta z - airyZetaComplex z) * (1 / Gamma ((5 / 6 : ℝ) : ℂ) *
        ∫ t in Ioi (0 : ℝ), Complex.exp (-(2 * airyZetaComplex z * t)) *
          airyRot_kernel (5 / 6) (-1 / 6) t) := by
  rw [airyAi_eq_kummerU hz (harg.trans (by linarith [Real.pi_pos])),
    kummerU_laplace (by norm_num) (airyRot_re_two_zeta_pos hz harg)]
  have hG : Gamma ((5 / 6 : ℝ) : ℂ) = Gamma (5 / 6) := by push_cast; ring_nf
  have hI : ∀ t : ℝ, Complex.exp (-(2 * airyZetaComplex z) * t) * (t : ℂ) ^ ((5 : ℂ) / 6 - 1) *
      (1 + (t : ℂ)) ^ ((5 : ℂ) / 3 - 5 / 6 - 1) = Complex.exp (-(2 * airyZetaComplex z * t)) *
        airyRot_kernel (5 / 6) (-1 / 6) t := by
    intro t
    simp only [airyRot_kernel]
    rw [show (((5 / 6 : ℝ) : ℂ) - 1) = 5 / 6 - 1 by push_cast; ring,
      show (((-1 / 6 : ℝ)) : ℂ) = 5 / 3 - 5 / 6 - 1 by push_cast; ring]
    ring_nf
  simp_rw [hI, hG]

/-- The anchor for `Ai'`: Tricomi's Laplace integral on `|arg z| < π/3`. -/
theorem airyRot_airyAiDeriv_anchor {z : ℂ} (hz : z ≠ 0) (harg : |arg z| < π / 3) :
    airyAiDeriv z = (-((3 : ℂ) ^ (1 / 6 : ℂ) / Real.sqrt π)) *
      exp ((4 / 3) * airyLogZeta z - airyZetaComplex z) * (1 / Gamma ((7 / 6 : ℝ) : ℂ) *
        ∫ t in Ioi (0 : ℝ), Complex.exp (-(2 * airyZetaComplex z * t)) *
          airyRot_kernel (7 / 6) (1 / 6) t) := by
  rw [airyAiDeriv_eq_kummerU hz (harg.trans (by linarith [Real.pi_pos])),
    kummerU_laplace (by norm_num) (airyRot_re_two_zeta_pos hz harg)]
  have hG : Gamma ((7 / 6 : ℝ) : ℂ) = Gamma (7 / 6) := by push_cast; ring_nf
  have hI : ∀ t : ℝ, Complex.exp (-(2 * airyZetaComplex z) * t) * (t : ℂ) ^ ((7 : ℂ) / 6 - 1) *
      (1 + (t : ℂ)) ^ ((7 : ℂ) / 3 - 7 / 6 - 1) = Complex.exp (-(2 * airyZetaComplex z * t)) *
        airyRot_kernel (7 / 6) (1 / 6) t := by
    intro t
    simp only [airyRot_kernel]
    rw [show (((7 / 6 : ℝ) : ℂ) - 1) = 7 / 6 - 1 by push_cast; ring,
      show (((1 / 6 : ℝ)) : ℂ) = 7 / 3 - 7 / 6 - 1 by push_cast; ring]
    ring_nf
  simp_rw [hI, hG]

/-! ### Expansions on closed rotated sectors -/

/-- `z → ∞` with `|(3/2) arg z + θ| ≤ γ`. -/
def airyRot_filter (θ γ : ℝ) : Filter ℂ :=
  comap (fun z : ℂ => ‖z‖) atTop ⊓ 𝓟 {z : ℂ | z ≠ 0 ∧ |3 / 2 * arg z + θ| ≤ γ}

/-- Eventually along `airyRot_filter θ γ`, `z ≠ 0` and `|(3/2) arg z + θ| ≤ γ`. -/
theorem airyRot_eventually_mem (θ γ : ℝ) :
    ∀ᶠ z in airyRot_filter θ γ, z ≠ 0 ∧ |3 / 2 * arg z + θ| ≤ γ :=
  mem_inf_of_right (mem_principal_self _)

/-- `‖2ζ‖ = (4/3) ‖z‖^{3/2}`. -/
theorem airyRot_norm_two_zeta (z : ℂ) : ‖2 * airyZetaComplex z‖ = 4 / 3 * ‖z‖ ^ (3 / 2 : ℝ) := by
  rw [airyZetaComplex, show (3 / 2 : ℂ) = ((3 / 2 : ℝ) : ℂ) by push_cast; ring, norm_mul, norm_mul,
    norm_cpow_real]
  norm_num
  ring

/-- The rotated variable `W = 2ζ e^{iθ}` tends to infinity in the sector `cos γ |W| ≤ re W`. -/
theorem airyRot_tendsto_W (θ : ℝ) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ : γ < π / 2) :
    Tendsto (fun z => exp (log 2 + airyLogZeta z + θ * I)) (airyRot_filter θ γ)
      (sectorAtTop (Real.cos γ)) := by
  have hnorm : ∀ z : ℂ, z ≠ 0 →
      ‖exp (log 2 + airyLogZeta z + θ * I)‖ = 4 / 3 * ‖z‖ ^ (3 / 2 : ℝ) := by
    intro z hz
    rw [← airyRot_two_zeta_mul_exp hz θ, norm_mul, norm_exp_ofReal_mul_I, mul_one,
      airyRot_norm_two_zeta]
  refine tendsto_inf.mpr ⟨tendsto_comap_iff.mpr ?_, tendsto_principal.mpr ?_⟩
  · have h : Tendsto (fun z : ℂ => 4 / 3 * ‖z‖ ^ (3 / 2 : ℝ)) (airyRot_filter θ γ) atTop :=
      ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 3 / 2)).comp
        (tendsto_comap.mono_left inf_le_left)).const_mul_atTop (by norm_num)
    refine h.congr' ?_
    filter_upwards [airyRot_eventually_mem θ γ] with z hz
    simp only [Function.comp_apply]
    rw [hnorm z hz.1]
  · filter_upwards [airyRot_eventually_mem θ γ] with z hz
    show Real.cos γ * ‖exp (log 2 + airyLogZeta z + θ * I)‖ ≤ (exp (log 2 + airyLogZeta z + θ * I)).re
    rw [airyRot_re_W, Complex.norm_exp]
    have : Real.cos γ ≤ Real.cos (3 / 2 * arg z + θ) := by
      rw [← Real.cos_abs (3 / 2 * arg z + θ)]
      exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_pos]) hz.2
    have he : (log 2 + airyLogZeta z + θ * I).re = (log 2 + airyLogZeta z).re := by simp
    rw [he, mul_comm]
    exact mul_le_mul_of_nonneg_left this (Real.exp_pos _).le

/-- `W^{-s} = exp (-s (log 2 + L + iθ))` on the closed rotated sector. -/
theorem airyRot_W_cpow {z : ℂ} {θ γ : ℝ} (hγ : γ < π / 2) (hz : |3 / 2 * arg z + θ| ≤ γ) (s : ℂ) :
    exp (log 2 + airyLogZeta z + θ * I) ^ s = exp (s * (log 2 + airyLogZeta z + θ * I)) := by
  have him : (log 2 + airyLogZeta z + θ * I).im = 3 / 2 * arg z + θ := by
    rw [add_im, im_log_two_add_airyLogZeta]; simp
  rw [cpow_def_of_ne_zero (exp_ne_zero _), log_exp (by rw [him]; linarith [abs_le.mp hz, Real.pi_pos])
    (by rw [him]; linarith [abs_le.mp hz, Real.pi_pos]), mul_comm]

/-- **The generic Airy expansion on a closed rotated sector.** -/
theorem airyRot_expansion (a β : ℝ) (ha : 0 < a) {θ : ℝ} (hθ : |θ| < π) {γ : ℝ} (hγ0 : 0 ≤ γ)
    (hγ : γ < π / 2) {f ε : ℂ → ℂ} (κ : ℂ)
    (hf : ∀ᶠ z in airyRot_filter θ γ, f z = ε z * (exp (θ * I) *
      airyRot_lap a β θ (exp (log 2 + airyLogZeta z + θ * I))))
    (hε : ∀ᶠ z in airyRot_filter θ γ, ε z * exp (-(a * (log 2 + airyLogZeta z))) = κ) :
    HasAsymptoticExpansion (airyRot_filter θ γ) (fun (n : ℕ) z => ((airyZetaComplex z) ^ n)⁻¹)
      (fun n => κ * (Gamma ((n : ℂ) + a) * Ring.choose (β : ℂ) n) / 2 ^ n) f := by
  have hW := (airyRot_hasAsymptoticExpansion a β ha hθ (Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos], hγ⟩)).comp_tendsto (airyRot_tendsto_W θ hγ0 hγ)
  have h1 := hW.mul_left ε
  have h2 := h1.smul_scale (κ := fun n : ℕ => κ * exp (-(θ * I * ((n : ℂ) + a))) / 2 ^ n)
    (ψ := fun (n : ℕ) z => ((airyZetaComplex z) ^ n)⁻¹) fun n => by
      filter_upwards [airyRot_eventually_mem θ γ, hε] with z hz hεz
      rw [airyRot_W_cpow hγ hz.2, ← hεz]
      have h2z : exp (log 2 + airyLogZeta z) = 2 * airyZetaComplex z :=
        exp_log_two_add_airyLogZeta hz.1
      have hsplit : exp (-((n : ℂ) + a) * (log 2 + airyLogZeta z + θ * I)) =
          exp (-(a * (log 2 + airyLogZeta z))) * exp (-(θ * I * ((n : ℂ) + a))) *
            (exp (log 2 + airyLogZeta z) ^ n)⁻¹ := by
        rw [← exp_nat_mul, ← exp_neg, ← exp_add, ← exp_add]
        congr 1; ring
      rw [hsplit, h2z, mul_pow]
      ring
  refine (h2.congr_coeff ?_).congr' ?_
  · funext n
    simp only [smul_eq_mul]
    have : exp (-(θ * I * ((n : ℂ) + a))) * exp (θ * I * ((n : ℂ) + a)) = 1 := by
      rw [← exp_add]; simp
    field_simp
    linear_combination (κ * Gamma ((n : ℂ) + a) * Ring.choose (β : ℂ) n) * this
  · filter_upwards [hf] with z hz
    rw [hz]
    simp only [Function.comp_apply, smul_eq_mul]

/-! ### The Airy coefficients -/

/-- The rising factorial `(x)_n` commutes with the cast `ℝ → ℂ`. -/
theorem airyRot_ascPochhammer_ofReal (n : ℕ) (x : ℝ) :
    (ascPochhammer ℂ n).eval (x : ℂ) = (((ascPochhammer ℝ n).eval x : ℝ) : ℂ) := by
  induction n with
  | zero => simp
  | succ n ih => rw [ascPochhammer_succ_eval, ascPochhammer_succ_eval, ih]; push_cast; ring

/-- `Γ(n + x)/Γ(x) = (x)_n` for real `x > 0`. -/
theorem airyRot_gamma_ratio (n : ℕ) {x : ℝ} (hx : 0 < x) :
    Gamma ((n : ℂ) + x) / Gamma x = (((ascPochhammer ℝ n).eval x : ℝ) : ℂ) := by
  rw [add_comm, Gamma_add_nat_div_Gamma_eq, airyRot_ascPochhammer_ofReal]
  intro k h
  have := congrArg Complex.re h
  simp at this
  linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]

/-- `binom(-x, n) = (-1)^n (x)_n / n!`. -/
theorem airyRot_choose_ofReal_neg (n : ℕ) (x : ℝ) :
    Ring.choose ((-x : ℝ) : ℂ) n =
      (-1) ^ n * (((ascPochhammer ℝ n).eval x : ℝ) : ℂ) / n.factorial := by
  rw [ofReal_neg, ring_choose_neg_eq_poch, poch, airyRot_ascPochhammer_ofReal]

/-- The Ai coefficients: `Γ(n+5/6)/Γ(5/6) · binom(-1/6, n) / 2^n = (-1)^n u_n`. -/
theorem airyRot_coeff_ai (n : ℕ) :
    1 / Gamma ((5 / 6 : ℝ) : ℂ) * (Gamma ((n : ℂ) + ((5 / 6 : ℝ) : ℂ)) *
      Ring.choose (((-1 / 6 : ℝ)) : ℂ) n) / 2 ^ n = airyExpansionCoeff .ai n := by
  have hG : Gamma ((5 / 6 : ℝ) : ℂ) ≠ 0 :=
    Gamma_ne_zero_of_re_pos (by simp)
  have h1 := airyRot_gamma_ratio n (x := 5 / 6) (by norm_num)
  have h2 := airyRot_choose_ofReal_neg n (1 / 6)
  rw [show ((-1 / 6 : ℝ)) = -(1 / 6 : ℝ) by ring, h2]
  rw [div_eq_iff hG] at h1
  simp only [airyExpansionCoeff, airyU]
  rw [h1]
  have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  generalize Gamma ((5 / 6 : ℝ) : ℂ) = G at hG ⊢
  push_cast
  field_simp

/-- `(7/6)_n = (6n + 1) (1/6)_n`. -/
theorem airyRot_poch_seven_sixths (n : ℕ) :
    (ascPochhammer ℝ n).eval (7 / 6) = (6 * n + 1) * (ascPochhammer ℝ n).eval (1 / 6) := by
  induction n with
  | zero => simp
  | succ n ih => rw [ascPochhammer_succ_eval, ascPochhammer_succ_eval, ih]; push_cast; ring

/-- `(-1/6)_n (1 - 6n) = (5/6)_n`. -/
theorem airyRot_poch_neg_sixth (n : ℕ) :
    (ascPochhammer ℝ n).eval (-1 / 6) * (1 - 6 * n) = (ascPochhammer ℝ n).eval (5 / 6) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ascPochhammer_succ_eval, ascPochhammer_succ_eval, ← ih]; push_cast; ring

/-- The Ai' coefficients: `Γ(n+7/6)/Γ(7/6) · binom(1/6, n) / 2^n = (-1)^n v_n`. -/
theorem airyRot_coeff_aiDeriv (n : ℕ) :
    1 / Gamma ((7 / 6 : ℝ) : ℂ) * (Gamma ((n : ℂ) + ((7 / 6 : ℝ) : ℂ)) *
      Ring.choose (((1 / 6 : ℝ)) : ℂ) n) / 2 ^ n = airyExpansionCoeff .aiDeriv n := by
  have hG : Gamma ((7 / 6 : ℝ) : ℂ) ≠ 0 :=
    Gamma_ne_zero_of_re_pos (by simp)
  have h1 := airyRot_gamma_ratio n (x := 7 / 6) (by norm_num)
  have h2 := airyRot_choose_ofReal_neg n (-1 / 6)
  rw [show ((1 / 6 : ℝ)) = -(-1 / 6 : ℝ) by ring, h2]
  rw [div_eq_iff hG] at h1
  simp only [airyExpansionCoeff, airyV, airyU]
  rw [h1, airyRot_poch_seven_sixths, ← airyRot_poch_neg_sixth]
  have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have h6 : (1 - 6 * (n : ℂ)) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    have h' : (6 * n : ℝ) = 1 := by linarith
    have : (6 * n : ℕ) = 1 := by exact_mod_cast h'
    omega
  generalize Gamma ((7 / 6 : ℝ) : ℂ) = G at hG ⊢
  push_cast
  field_simp

/-! ### The normalized Ai, Ai' on closed rotated sectors -/

/-- A product of powers and exponentials of `ζ̃(z)` equals `1` once the exponents cancel. -/
theorem airyRot_exp_combine {z : ℂ} (hz : z ≠ 0) (c3 p q a : ℂ)
    (hkey : log 2 + c3 * log 3 + p * (log 2 - log 3 + 3 / 2 * log z) + q * log z -
      a * (log 2 + (log 2 - log 3 + 3 / 2 * log z)) = 0) :
    2 * (3 : ℂ) ^ c3 * exp (p * airyLogZeta z) * z ^ q * exp (-(a * (log 2 + airyLogZeta z))) =
      1 := by
  rw [cpow_def_of_ne_zero hz, cpow_def_of_ne_zero (by norm_num : (3 : ℂ) ≠ 0), airyLogZeta,
    log_two_thirds]
  calc 2 * exp (log 3 * c3) * exp (p * (log 2 - log 3 + 3 / 2 * log z)) * exp (log z * q) *
        exp (-(a * (log 2 + (log 2 - log 3 + 3 / 2 * log z))))
      = exp (log 2) * exp (log 3 * c3) * exp (p * (log 2 - log 3 + 3 / 2 * log z)) *
          exp (log z * q) * exp (-(a * (log 2 + (log 2 - log 3 + 3 / 2 * log z)))) := by
        rw [exp_log two_ne_zero]
    _ = exp (log 2 + c3 * log 3 + p * (log 2 - log 3 + 3 / 2 * log z) + q * log z -
          a * (log 2 + (log 2 - log 3 + 3 / 2 * log z))) := by
        simp only [← exp_add]; congr 1; ring
    _ = 1 := by rw [hkey, exp_zero]

/-- The normalized `Ai` on a closed rotated sector. -/
theorem airyRot_airyAi_expansion_piece {θ : ℝ} (hθ : |θ| < π) {γ : ℝ} (hγ0 : 0 ≤ γ)
    (hγ : γ < π / 2) :
    HasAsymptoticExpansion (airyRot_filter θ γ) (fun (n : ℕ) z => ((airyZetaComplex z) ^ n)⁻¹)
      (airyExpansionCoeff .ai) (fun z => airyAi z / airyPrefactor .ai z) := by
  have hG : Gamma ((5 / 6 : ℝ) : ℂ) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp)
  have hπ : (Real.sqrt π : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have h := airyRot_expansion (5 / 6) (-1 / 6) (by norm_num) hθ hγ0 hγ
    (f := fun z => airyAi z / airyPrefactor .ai z)
    (ε := fun z => 2 * (3 : ℂ) ^ (-1 / 6 : ℂ) * exp (2 / 3 * airyLogZeta z) * z ^ (1 / 4 : ℂ) /
      Gamma ((5 / 6 : ℝ) : ℂ)) (1 / Gamma ((5 / 6 : ℝ) : ℂ)) ?_ ?_
  · exact h.congr_coeff (funext airyRot_coeff_ai)
  · filter_upwards [airyRot_eventually_mem θ γ] with z hz
    have hz0 := hz.1
    have hq : z ^ (1 / 4 : ℂ) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hz0)
    rw [airyRot_eq_of_anchor differentiable_airyAi _ _ (5 / 6) (-1 / 6) (by norm_num)
      (fun w hw harg => airyRot_airyAi_anchor hw harg) hθ hz0
      (lt_of_le_of_lt hz.2 hγ)]
    simp only [airyPrefactor]
    rw [exp_sub]
    have hE : exp (airyZetaComplex z) * exp (-airyZetaComplex z) = 1 := by
      rw [← exp_add]; simp
    field_simp
    linear_combination (-airyRot_lap (5 / 6) (-(1 / 6)) θ
      (exp (log 2 + airyLogZeta z + θ * I))) * hE
  · filter_upwards [airyRot_eventually_mem θ γ] with z hz
    rw [div_mul_eq_mul_div, airyRot_exp_combine hz.1 _ _ _ _ (by push_cast; ring)]

/-- The normalized `Ai'` on a closed rotated sector. -/
theorem airyRot_airyAiDeriv_expansion_piece {θ : ℝ} (hθ : |θ| < π) {γ : ℝ} (hγ0 : 0 ≤ γ)
    (hγ : γ < π / 2) :
    HasAsymptoticExpansion (airyRot_filter θ γ) (fun (n : ℕ) z => ((airyZetaComplex z) ^ n)⁻¹)
      (airyExpansionCoeff .aiDeriv) (fun z => airyAiDeriv z / airyPrefactor .aiDeriv z) := by
  have hG : Gamma ((7 / 6 : ℝ) : ℂ) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp)
  have hπ : (Real.sqrt π : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have h := airyRot_expansion (7 / 6) (1 / 6) (by norm_num) hθ hγ0 hγ
    (f := fun z => airyAiDeriv z / airyPrefactor .aiDeriv z)
    (ε := fun z => 2 * (3 : ℂ) ^ (1 / 6 : ℂ) * exp (4 / 3 * airyLogZeta z) * z ^ (-1 / 4 : ℂ) /
      Gamma ((7 / 6 : ℝ) : ℂ)) (1 / Gamma ((7 / 6 : ℝ) : ℂ)) ?_ ?_
  · exact h.congr_coeff (funext airyRot_coeff_aiDeriv)
  · filter_upwards [airyRot_eventually_mem θ γ] with z hz
    have hz0 := hz.1
    have hq : z ^ (1 / 4 : ℂ) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hz0)
    have hqq : z ^ (-(1 / 4) : ℂ) * z ^ (1 / 4 : ℂ) = 1 := by
      rw [← cpow_add _ _ hz0]; norm_num
    have hE : exp (airyZetaComplex z) * exp (-airyZetaComplex z) = 1 := by
      rw [← exp_add]; simp
    rw [airyRot_eq_of_anchor (hf := fun w => (hasDerivAt_airyAiDeriv w).differentiableAt) _ _
      (7 / 6) (1 / 6) (by norm_num) (fun w hw harg => airyRot_airyAiDeriv_anchor hw harg) hθ hz0
      (lt_of_le_of_lt hz.2 hγ)]
    simp only [airyPrefactor]
    rw [exp_sub]
    field_simp
    linear_combination (-airyRot_lap (7 / 6) (1 / 6) θ (exp (log 2 + airyLogZeta z + θ * I)) *
      z ^ (1 / 4 : ℂ) * z ^ (-(1 / 4) : ℂ)) * hE +
      (-airyRot_lap (7 / 6) (1 / 6) θ (exp (log 2 + airyLogZeta z + θ * I))) * hqq
  · filter_upwards [airyRot_eventually_mem θ γ] with z hz
    rw [div_mul_eq_mul_div, airyRot_exp_combine hz.1 _ _ _ _ (by push_cast; ring)]

/-! ### Gluing the rotated sectors -/

/-- Five closed rotated sectors cover the sector `|arg z| ≤ π - δ`. -/
theorem airyRot_sector_le {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < π) :
    airySector (π - δ) ≤ airyRot_filter 0 (π / 2 - δ / 4) ⊔
      airyRot_filter (-(π / 2)) (π / 2 - δ / 4) ⊔ airyRot_filter (π / 2) (π / 2 - δ / 4) ⊔
      airyRot_filter (-(π - δ / 4)) (π / 2 - δ / 4) ⊔
      airyRot_filter (π - δ / 4) (π / 2 - δ / 4) := by
  simp only [airyRot_filter, airySector, ← inf_sup_left, sup_principal]
  refine inf_le_inf_left _ (principal_mono.mpr ?_)
  rintro z ⟨hz, harg⟩
  have ha := abs_le.mp harg
  simp only [mem_union, mem_ofPred_eq]
  set φ := 3 / 2 * arg z with hφ
  have hφ1 : -(3 / 2 * (π - δ)) ≤ φ := by rw [hφ]; linarith
  have hφ2 : φ ≤ 3 / 2 * (π - δ) := by rw [hφ]; linarith
  rcases le_or_gt φ (π / 2 - δ / 4) with h1 | h1
  · rcases le_or_gt (-(π / 2 - δ / 4)) φ with h2 | h2
    · exact Or.inl (Or.inl (Or.inl (Or.inl ⟨hz, abs_le.mpr ⟨by linarith, by linarith⟩⟩)))
    · rcases le_or_gt (-(π - δ / 4)) φ with h3 | h3
      · exact Or.inl (Or.inl (Or.inr ⟨hz, abs_le.mpr ⟨by linarith, by linarith⟩⟩))
      · exact Or.inr ⟨hz, abs_le.mpr ⟨by linarith, by linarith⟩⟩
  · rcases le_or_gt φ (π - δ / 4) with h3 | h3
    · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨hz, abs_le.mpr ⟨by linarith, by linarith⟩⟩)))
    · exact Or.inl (Or.inr ⟨hz, abs_le.mpr ⟨by linarith, by linarith⟩⟩)

/-- Expansions valid on every closed rotated sector glue to `|arg z| ≤ π - δ`. -/
theorem airyRot_glue {φ : ℕ → ℂ → ℂ} {c : ℕ → ℂ} {f : ℂ → ℂ}
    (h : ∀ θ : ℝ, |θ| < π → ∀ γ : ℝ, 0 ≤ γ → γ < π / 2 →
      HasAsymptoticExpansion (airyRot_filter θ γ) φ c f)
    {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < π) :
    HasAsymptoticExpansion (airySector (π - δ)) φ c f := by
  have hπ := Real.pi_pos
  have hγ0 : 0 ≤ π / 2 - δ / 4 := by linarith
  have hγ : π / 2 - δ / 4 < π / 2 := by linarith
  refine (((((h 0 (by simpa using hπ) _ hγ0 hγ).sup
    (h (-(π / 2)) (by rw [abs_neg, abs_of_pos (by linarith)]; linarith) _ hγ0 hγ)).sup
    (h (π / 2) (by rw [abs_of_pos (by linarith)]; linarith) _ hγ0 hγ)).sup
    (h (-(π - δ / 4)) (by rw [abs_neg, abs_of_pos (by linarith)]; linarith) _ hγ0 hγ)).sup
    (h (π - δ / 4) (by rw [abs_of_pos (by linarith)]; linarith) _ hγ0 hγ)).mono
    (airyRot_sector_le hδ hδ')

/-- **Poincaré expansion of the normalized `Ai`** in `|arg z| ≤ π - δ` (DLMF 9.7.5). -/
theorem airyRot_airyAi_expansion {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < π) :
    HasAsymptoticExpansion (airySector (π - δ)) (fun (n : ℕ) z => ((airyZetaComplex z) ^ n)⁻¹)
      (airyExpansionCoeff .ai) (fun z => airyAi z / airyPrefactor .ai z) :=
  airyRot_glue (fun _ hθ _ hγ0 hγ => airyRot_airyAi_expansion_piece hθ hγ0 hγ) hδ hδ'

/-- **Poincaré expansion of the normalized `Ai'`** in `|arg z| ≤ π - δ` (DLMF 9.7.6). -/
theorem airyRot_airyAiDeriv_expansion {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < π) :
    HasAsymptoticExpansion (airySector (π - δ)) (fun (n : ℕ) z => ((airyZetaComplex z) ^ n)⁻¹)
      (airyExpansionCoeff .aiDeriv) (fun z => airyAiDeriv z / airyPrefactor .aiDeriv z) :=
  airyRot_glue (fun _ hθ _ hγ0 hγ => airyRot_airyAiDeriv_expansion_piece hθ hγ0 hγ) hδ hδ'

/-! ### From normalized expansions to the Poincaré statements -/

/-- Eventually in the sector filter `airySector α`, `z ≠ 0`. -/
theorem airyRot_eventually_ne_zero (α : ℝ) : ∀ᶠ z in airySector α, z ≠ 0 :=
  mem_inf_of_right (mem_principal.mpr fun _ hz => hz.1)

/-- Eventually in `airySector α`, `z ≠ 0` and `|arg z| ≤ α`. -/
theorem airyRot_eventually_arg (α : ℝ) : ∀ᶠ z in airySector α, z ≠ 0 ∧ |arg z| ≤ α :=
  mem_inf_of_right (mem_principal_self _)

/-- Each Airy prefactor is nonzero at `z ≠ 0`. -/
theorem airyRot_prefactor_ne_zero (kind : AiryKind) {z : ℂ} (hz : z ≠ 0) :
    airyPrefactor kind z ≠ 0 := by
  have hπ : (Real.sqrt π : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hq : z ^ (1 / 4 : ℂ) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hz)
  cases kind <;> simp only [airyPrefactor] <;> field_simp <;> simp [hπ, hz, exp_ne_zero]

/-- A normalized expansion gives the Poincaré `O`-statement. -/
theorem airyRot_isBigO_of_expansion {l : Filter ℂ} {f p : ℂ → ℂ} {c : ℕ → ℂ}
    (h : HasAsymptoticExpansion l (fun (n : ℕ) z => ((airyZetaComplex z) ^ n)⁻¹) c
      (fun z => f z / p z)) (hp : ∀ᶠ z in l, p z ≠ 0) (N : ℕ) :
    IsBigO l (fun z => f z - p z * ∑ k ∈ Finset.range N, c k / airyZetaComplex z ^ k)
      (fun z => p z / airyZetaComplex z ^ N) := by
  refine ((isBigO_refl p l).mul (h N)).congr' ?_ (Eventually.of_forall fun z => ?_)
  · filter_upwards [hp] with z hz
    simp only [smul_eq_mul]
    rw [mul_sub, mul_div_cancel₀ _ hz]
    congr 2
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [div_eq_mul_inv, mul_comm]
  · simp only [div_eq_mul_inv]

end DLMF.Airy
end
