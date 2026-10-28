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
# Airy asymptotic expansions and error bounds, DLMF §9.7

Statements acquired from the NIST DLMF, checked 2026-10-19.
New statements are initially admitted; existing proved Airy results are retained.
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

/-! ### Rotations of the variable -/

/-- `ζ(z e^{iα}) = ζ(z) e^{3iα/2}` when `arg z + α ∈ (-π, π]`. -/
theorem airyRot_zeta_mul_exp {z : ℂ} (hz : z ≠ 0) {α : ℝ} (h1 : -π < arg z + α)
    (h2 : arg z + α ≤ π) :
    airyZetaComplex (z * exp (α * I)) = airyZetaComplex z * exp (α * I * (3 / 2)) := by
  unfold airyZetaComplex
  rw [Complex.cpow_mul_exp_ofReal_mul_I hz h1 h2]
  ring

/-- Rotation by `c` maps the sector `|arg z| ≤ α` into `|arg z| ≤ β` when `|c| + α ≤ β < π`. -/
theorem airyRot_tendsto_rotate {α β c : ℝ} (hc : |c| + α ≤ β) (hβ : β < π) :
    Tendsto (fun z : ℂ => z * exp (c * I)) (airySector α) (airySector β) := by
  refine tendsto_inf.mpr ⟨tendsto_comap_iff.mpr ?_, tendsto_principal.mpr ?_⟩
  · refine (tendsto_comap.mono_left inf_le_left).congr fun z => ?_
    simp only [Function.comp_apply, norm_mul, norm_exp_ofReal_mul_I, mul_one]
  · filter_upwards [airyRot_eventually_arg α] with z hz
    refine ⟨mul_ne_zero hz.1 (exp_ne_zero _), ?_⟩
    have h1 := abs_le.mp hz.2
    have h2 := le_abs_self c
    have h3 := neg_abs_le c
    rw [Complex.arg_mul_exp_ofReal_mul_I hz.1 (by linarith) (by linarith)]
    exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The exponents `e^{±2πi/3}` in the form `e^{iα}`. -/
theorem airyRot_exp_two_pi_div_three :
    exp (2 * π * I / 3) = exp (((2 * π / 3 : ℝ) : ℂ) * I) ∧
      exp (-(2 * π * I / 3)) = exp (((-(2 * π / 3)) : ℝ) * I) := by
  constructor <;> congr 1 <;> push_cast <;> ring

/-- An expansion on `|arg z| ≤ π - δ` gives, at the two rotated points `z e^{±2πi/3}`,
expansions on `|arg z| ≤ π/3 - δ` with alternating coefficients. -/
theorem airyRot_rotated_expansion {F : ℂ → ℂ} {c : ℕ → ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hF : HasAsymptoticExpansion (airySector (π - δ))
      (fun (n : ℕ) z => ((airyZetaComplex z) ^ n)⁻¹) c F) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    HasAsymptoticExpansion (airySector (π / 3 - δ))
      (fun (n : ℕ) z => ((airyZetaComplex z) ^ n)⁻¹) (fun n => (-1) ^ n * c n)
      (fun z => F (z * exp (((ε * (2 * π / 3)) : ℝ) * I))) := by
  have hπ := Real.pi_pos
  have habs : |ε * (2 * π / 3)| = 2 * π / 3 := by
    rcases hε with h | h <;> subst h <;> simp [abs_of_pos (by positivity : (0:ℝ) < 2 * π / 3)]
  have h := hF.comp_tendsto (airyRot_tendsto_rotate (α := π / 3 - δ) (β := π - δ)
    (c := ε * (2 * π / 3)) (by rw [habs]; linarith) (by linarith))
  refine (h.smul_scale (κ := fun n => (-1 : ℂ) ^ n)
    (ψ := fun (n : ℕ) z => ((airyZetaComplex z) ^ n)⁻¹) fun n => ?_).congr_coeff ?_
  · filter_upwards [airyRot_eventually_arg (π / 3 - δ)] with z hz
    have h1 := abs_le.mp hz.2
    have h2 : -π < arg z + ε * (2 * π / 3) ∧ arg z + ε * (2 * π / 3) ≤ π := by
      rcases hε with h | h <;> subst h <;> constructor <;> linarith
    rw [airyRot_zeta_mul_exp hz.1 h2.1 h2.2]
    have he : exp (((ε * (2 * π / 3) : ℝ) : ℂ) * I * (3 / 2)) = -1 := by
      rcases hε with h | h <;> subst h
      · rw [show (((1 * (2 * π / 3) : ℝ) : ℂ) * I * (3 / 2)) = π * I by push_cast; ring,
          exp_pi_mul_I]
      · rw [show ((((-1) * (2 * π / 3) : ℝ) : ℂ) * I * (3 / 2)) = -(π * I) by push_cast; ring,
          exp_neg, exp_pi_mul_I]; norm_num
    rw [he, mul_neg_one, neg_pow, mul_inv, ← inv_pow, inv_neg, inv_one]
  · funext n
    simp only [smul_eq_mul]

/-- `exp ((±2π/3) · i · 3/2) = -1`. -/
theorem airyRot_exp_rot_three_halves {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    exp (((ε * (2 * π / 3) : ℝ) : ℂ) * I * (3 / 2)) = -1 := by
  rcases hε with h | h <;> subst h
  · rw [show (((1 * (2 * π / 3) : ℝ) : ℂ) * I * (3 / 2)) = π * I by push_cast; ring,
      exp_pi_mul_I]
  · rw [show ((((-1) * (2 * π / 3) : ℝ) : ℂ) * I * (3 / 2)) = -(π * I) by push_cast; ring,
      exp_neg, exp_pi_mul_I]; norm_num

/-- For `|arg z| < π/3`, `arg z ± 2π/3` lies in `(-π, π]`. -/
theorem airyRot_arg_rot_bounds {z : ℂ} (hz : |arg z| < π / 3) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    -π < arg z + ε * (2 * π / 3) ∧ arg z + ε * (2 * π / 3) ≤ π := by
  have h1 := abs_lt.mp hz
  have hπ := Real.pi_pos
  rcases hε with h | h <;> subst h <;> constructor <;> linarith

/-- `ζ(z e^{±2πi/3}) = -ζ(z)` for `|arg z| ≤ π/3`. -/
theorem airyRot_zeta_rot {z : ℂ} (hz0 : z ≠ 0) (hz : |arg z| < π / 3) {ε : ℝ}
    (hε : ε = 1 ∨ ε = -1) :
    airyZetaComplex (z * exp (((ε * (2 * π / 3)) : ℝ) * I)) = -airyZetaComplex z := by
  obtain ⟨h1, h2⟩ := airyRot_arg_rot_bounds hz hε
  rw [airyRot_zeta_mul_exp hz0 h1 h2, airyRot_exp_rot_three_halves hε, mul_neg_one]

/-- `(z e^{±2πi/3})^{1/4} = z^{1/4} e^{±πi/6}`. -/
theorem airyRot_quarter_rot {z : ℂ} (hz0 : z ≠ 0) (hz : |arg z| < π / 3) {ε : ℝ}
    (hε : ε = 1 ∨ ε = -1) :
    (z * exp (((ε * (2 * π / 3)) : ℝ) * I)) ^ (1 / 4 : ℂ) =
      z ^ (1 / 4 : ℂ) * exp (((ε * (π / 6)) : ℝ) * I) := by
  obtain ⟨h1, h2⟩ := airyRot_arg_rot_bounds hz hε
  rw [Complex.cpow_mul_exp_ofReal_mul_I hz0 h1 h2]
  congr 2
  push_cast; ring

/-- `e^w e^{-w} = 1`. -/
theorem airyRot_exp_mul_exp_neg (w : ℂ) : exp w * exp (-w) = 1 := by
  rw [← exp_add]; simp

/-- **Poincaré expansion of the normalized `Bi`** in `|arg z| ≤ π/3 - δ` (DLMF 9.7.7). -/
theorem airyRot_airyBi_expansion {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < π / 3) :
    HasAsymptoticExpansion (airySector (π / 3 - δ)) (fun (n : ℕ) z => ((airyZetaComplex z) ^ n)⁻¹)
      (airyExpansionCoeff .bi) (fun z => airyBi z / airyPrefactor .bi z) := by
  have hπ := Real.pi_pos
  have hA := airyRot_airyAi_expansion hδ (by linarith)
  have hp := airyRot_rotated_expansion hδ hA (Or.inl rfl)
  have hm := airyRot_rotated_expansion hδ hA (Or.inr rfl)
  refine ((hp.const_smul (1 / 2 : ℂ)).add (hm.const_smul (1 / 2 : ℂ))).congr_coeff ?_ |>.congr' ?_
  · funext n
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, airyExpansionCoeff]
    have h1 : ((-1 : ℂ) ^ n) * ((-1) ^ n) = 1 := by rw [← mul_pow]; norm_num
    linear_combination (airyU n : ℂ) * h1
  · filter_upwards [airyRot_eventually_arg (π / 3 - δ)] with z hz
    have hz0 := hz.1
    have hz3 : |arg z| < π / 3 := hz.2.trans_lt (by linarith)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have hπs : (Real.sqrt π : ℂ) ≠ 0 :=
      ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
    have hq : z ^ (1 / 4 : ℂ) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hz0)
    rw [airyBi_eq_airyAi_omega z, airyRot_exp_two_pi_div_three.1, airyRot_exp_two_pi_div_three.2]
    simp only [airyPrefactor]
    rw [airyRot_zeta_rot hz0 hz3 (Or.inl rfl), airyRot_zeta_rot hz0 hz3 (Or.inr rfl),
      airyRot_quarter_rot hz0 hz3 (Or.inl rfl), airyRot_quarter_rot hz0 hz3 (Or.inr rfl)]
    rw [show (((1 : ℝ) * (2 * π / 3) : ℝ) : ℂ) = ((2 * π / 3 : ℝ) : ℂ) by push_cast; ring,
      show (((-1 : ℝ) * (2 * π / 3) : ℝ) : ℂ) = ((-(2 * π / 3) : ℝ) : ℂ) by push_cast; ring]
    have e1 : exp ((((1 : ℝ) * (π / 6) : ℝ) : ℂ) * I) = exp (π * I / 6) := by
      congr 1; push_cast; ring
    have e2 : exp ((((-1 : ℝ) * (π / 6) : ℝ) : ℂ) * I) = exp (-(π * I / 6)) := by
      congr 1; push_cast; ring
    rw [e1, e2]
    have h6 := airyRot_exp_mul_exp_neg (π * I / 6)
    have hz2 := airyRot_exp_mul_exp_neg (airyZetaComplex z)
    rw [neg_neg]
    field_simp
    ring_nf

/-- Differentiating an identity `f(z) = c₁ g(z w₁) + c₂ g(z w₂)`. -/
theorem airyRot_deriv_of_eq {f g f' g' : ℂ → ℂ} (hf : ∀ z, HasDerivAt f (f' z) z)
    (hg : ∀ z, HasDerivAt g (g' z) z) (c₁ c₂ w₁ w₂ : ℂ)
    (h : ∀ z, f z = c₁ * g (z * w₁) + c₂ * g (z * w₂)) (z : ℂ) :
    f' z = c₁ * w₁ * g' (z * w₁) + c₂ * w₂ * g' (z * w₂) := by
  have h1 : HasDerivAt (fun z => c₁ * g (z * w₁) + c₂ * g (z * w₂))
      (c₁ * (g' (z * w₁) * w₁) + c₂ * (g' (z * w₂) * w₂)) z :=
    (((hg (z * w₁)).comp z ((hasDerivAt_id z).mul_const w₁)).const_mul c₁).add
      (((hg (z * w₂)).comp z ((hasDerivAt_id z).mul_const w₂)).const_mul c₂) |>.congr_deriv
      (by simp)
  rw [← funext h] at h1
  rw [(hf z).unique h1]
  ring

/-- `Bi'(z) = e^{-5πi/6} Ai'(z e^{-2πi/3}) + e^{5πi/6} Ai'(z e^{2πi/3})`. -/
theorem airyRot_airyBiDeriv_eq (z : ℂ) :
    airyBiDeriv z = exp (-(π * I / 6)) * exp (-(2 * π * I / 3)) *
        airyAiDeriv (z * exp (-(2 * π * I / 3))) +
      exp (π * I / 6) * exp (2 * π * I / 3) * airyAiDeriv (z * exp (2 * π * I / 3)) :=
  airyRot_deriv_of_eq hasDerivAt_airyBi hasDerivAt_airyAi _ _ _ _ airyBi_eq_airyAi_omega z

/-- **Poincaré expansion of the normalized `Bi'`** in `|arg z| ≤ π/3 - δ` (DLMF 9.7.8). -/
theorem airyRot_airyBiDeriv_expansion {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < π / 3) :
    HasAsymptoticExpansion (airySector (π / 3 - δ)) (fun (n : ℕ) z => ((airyZetaComplex z) ^ n)⁻¹)
      (airyExpansionCoeff .biDeriv) (fun z => airyBiDeriv z / airyPrefactor .biDeriv z) := by
  have hπ := Real.pi_pos
  have hA := airyRot_airyAiDeriv_expansion hδ (by linarith)
  have hp := airyRot_rotated_expansion hδ hA (Or.inl rfl)
  have hm := airyRot_rotated_expansion hδ hA (Or.inr rfl)
  refine ((hp.const_smul (1 / 2 : ℂ)).add (hm.const_smul (1 / 2 : ℂ))).congr_coeff ?_ |>.congr' ?_
  · funext n
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, airyExpansionCoeff]
    have h1 : ((-1 : ℂ) ^ n) * ((-1) ^ n) = 1 := by rw [← mul_pow]; norm_num
    linear_combination (airyV n : ℂ) * h1
  · filter_upwards [airyRot_eventually_arg (π / 3 - δ)] with z hz
    have hz0 := hz.1
    have hz3 : |arg z| < π / 3 := hz.2.trans_lt (by linarith)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have hπs : (Real.sqrt π : ℂ) ≠ 0 :=
      ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
    have hq : z ^ (1 / 4 : ℂ) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hz0)
    rw [airyRot_airyBiDeriv_eq z, airyRot_exp_two_pi_div_three.1,
      airyRot_exp_two_pi_div_three.2]
    simp only [airyPrefactor]
    rw [airyRot_zeta_rot hz0 hz3 (Or.inl rfl), airyRot_zeta_rot hz0 hz3 (Or.inr rfl),
      airyRot_quarter_rot hz0 hz3 (Or.inl rfl), airyRot_quarter_rot hz0 hz3 (Or.inr rfl)]
    rw [show (((1 : ℝ) * (2 * π / 3) : ℝ) : ℂ) = ((2 * π / 3 : ℝ) : ℂ) by push_cast; ring,
      show (((-1 : ℝ) * (2 * π / 3) : ℝ) : ℂ) = ((-(2 * π / 3)) : ℝ) by push_cast; ring]
    set u := exp (π * I / 6) with hu
    have e1 : exp ((((1 : ℝ) * (π / 6) : ℝ) : ℂ) * I) = u := by
      rw [hu]; congr 1; push_cast; ring
    have e2 : exp ((((-1 : ℝ) * (π / 6) : ℝ) : ℂ) * I) = u⁻¹ := by
      rw [hu, ← exp_neg]; congr 1; push_cast; ring
    have e3 : exp (((2 * π / 3 : ℝ) : ℂ) * I) = u ^ 4 := by
      rw [hu, ← exp_nat_mul]; congr 1; push_cast; ring
    have e4 : exp (((-(2 * π / 3) : ℝ) : ℂ) * I) = (u ^ 4)⁻¹ := by
      rw [hu, ← exp_nat_mul, ← exp_neg]; congr 1; push_cast; ring
    have e5 : exp (-(π * I / 6)) = u⁻¹ := by rw [hu, exp_neg]
    have hu6 : u ^ 6 = -1 := by
      rw [hu, ← exp_nat_mul, show ((6 : ℕ) : ℂ) * (π * I / 6) = π * I by push_cast; ring,
        exp_pi_mul_I]
    have hu0 : u ≠ 0 := exp_ne_zero _
    rw [e1, e2, e3, e4, e5]
    have hz2 := airyRot_exp_mul_exp_neg (airyZetaComplex z)
    rw [neg_neg]
    field_simp
    linear_combination (-(airyAiDeriv (z / u ^ 4) + u ^ 4 * airyAiDeriv (z * u ^ 4))) * hu6

/-! ### Even and odd parts on the negative axis -/

/-- An expansion on `|arg z| ≤ π - δ` restricts along the rotation `z ↦ z e^{iα}` to the sector
`|arg z| ≤ β`, for `|α| + β ≤ π - δ`. -/
theorem airyRot_rot_expansion {F : ℂ → ℂ} {c : ℕ → ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hF : HasAsymptoticExpansion (airySector (π - δ))
      (fun (n : ℕ) z => ((airyZetaComplex z) ^ n)⁻¹) c F) {α β : ℝ} (hαβ : |α| + β ≤ π - δ) :
    HasAsymptoticExpansion (airySector β)
      (fun (n : ℕ) z => ((airyZetaComplex z) ^ n)⁻¹)
      (fun n => ((exp (α * I * (3 / 2))) ^ n)⁻¹ * c n)
      (fun z => F (z * exp (α * I))) := by
  have hπ := Real.pi_pos
  have h := hF.comp_tendsto (airyRot_tendsto_rotate (α := β) (β := π - δ) (c := α) hαβ
    (by linarith))
  refine (h.smul_scale (κ := fun n => ((exp (α * I * (3 / 2))) ^ n)⁻¹)
    (ψ := fun (n : ℕ) z => ((airyZetaComplex z) ^ n)⁻¹) fun n => ?_).congr_coeff ?_
  · filter_upwards [airyRot_eventually_arg β] with z hz
    have h1 := abs_le.mp hz.2
    have h2 := le_abs_self α
    have h3 := neg_abs_le α
    rw [airyRot_zeta_mul_exp hz.1 (by linarith) (by linarith), mul_pow, mul_inv, mul_comm]
  · funext n
    simp only [smul_eq_mul]

/-- The even part `(F(z e^{iπ/3}) + F(z e^{-iπ/3}))/2`. -/
def airyRot_even (F : ℂ → ℂ) (z : ℂ) : ℂ :=
  (F (z * exp ((π / 3 : ℝ) * I)) + F (z * exp ((-(π / 3) : ℝ) * I))) / 2

/-- The odd part `(F(z e^{iπ/3}) - F(z e^{-iπ/3}))/(2i)`. -/
def airyRot_odd (F : ℂ → ℂ) (z : ℂ) : ℂ :=
  (F (z * exp ((π / 3 : ℝ) * I)) - F (z * exp ((-(π / 3) : ℝ) * I))) / (2 * I)

/-- `exp ((π/3) · i · 3/2) = i` and `exp ((-π/3) · i · 3/2) = -i`. -/
theorem airyRot_exp_third_three_halves :
    exp (((π / 3 : ℝ) : ℂ) * I * (3 / 2)) = I ∧ exp (((-(π / 3)) : ℝ) * I * (3 / 2)) = -I := by
  constructor
  · rw [show (((π / 3 : ℝ) : ℂ) * I * (3 / 2)) = ((π / 2 : ℝ) : ℂ) * I by push_cast; ring,
      exp_mul_I]
    simp
  · rw [show ((((-(π / 3)) : ℝ) : ℂ) * I * (3 / 2)) = ((-(π / 2)) : ℝ) * I by push_cast; ring,
      exp_mul_I]
    simp

/-- Even powers: `(i^{-2j} + (-i)^{-2j})/2 = (-1)^j` and the odd combination vanishes. -/
theorem airyRot_I_pow_recip_even (j : ℕ) :
    ((I ^ (2 * j))⁻¹ + ((-I) ^ (2 * j))⁻¹) / 2 = (-1) ^ j ∧
      ((I ^ (2 * j))⁻¹ - ((-I) ^ (2 * j))⁻¹) / (2 * I) = 0 := by
  have h1 : I ^ (2 * j) = (-1) ^ j := by rw [pow_mul, I_sq]
  have h2 : (-I) ^ (2 * j) = (-1) ^ j := by rw [pow_mul, neg_sq, I_sq]
  rw [h1, h2]
  constructor
  · rw [← inv_pow, inv_neg, inv_one]; ring
  · simp

/-- Odd powers: `(i^{-(2j+1)} + (-i)^{-(2j+1)})/2 = 0` and the odd combination is `-(-1)^j`. -/
theorem airyRot_I_pow_recip_odd (j : ℕ) :
    ((I ^ (2 * j + 1))⁻¹ + ((-I) ^ (2 * j + 1))⁻¹) / 2 = 0 ∧
      ((I ^ (2 * j + 1))⁻¹ - ((-I) ^ (2 * j + 1))⁻¹) / (2 * I) = -(-1) ^ j := by
  have h1 : I ^ (2 * j + 1) = (-1) ^ j * I := by rw [pow_succ, pow_mul, I_sq]
  have h2 : (-I) ^ (2 * j + 1) = -((-1) ^ j * I) := by rw [pow_succ, pow_mul, neg_sq, I_sq]; ring
  rw [h1, h2]
  have hI : I ≠ 0 := I_ne_zero
  have hm : ((-1 : ℂ) ^ j) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hm2 : ((-1 : ℂ) ^ j) * (-1) ^ j = 1 := by rw [← mul_pow]; norm_num
  constructor
  · rw [inv_neg]; ring
  · field_simp
    linear_combination (2 : ℂ) * I_sq + (2 * I ^ 2) * hm2

/-- An expansion in `ζ^{-n}` on `|arg z| ≤ π - δ` gives expansions of `F(z e^{±iπ/3})` with
coefficients `(±i)^{-n} c_n` on `|arg z| ≤ 2π/3 - δ`. -/
theorem airyRot_pm_expansions {F : ℂ → ℂ} {c : ℕ → ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hF : HasAsymptoticExpansion (airySector (π - δ))
      (fun (n : ℕ) z => ((airyZetaComplex z) ^ n)⁻¹) c F) :
    HasAsymptoticExpansion (airySector (2 * π / 3 - δ))
        (fun (n : ℕ) z => ((airyZetaComplex z) ^ n)⁻¹) (fun n => (I ^ n)⁻¹ * c n)
        (fun z => F (z * exp ((π / 3 : ℝ) * I))) ∧
      HasAsymptoticExpansion (airySector (2 * π / 3 - δ))
        (fun (n : ℕ) z => ((airyZetaComplex z) ^ n)⁻¹) (fun n => ((-I) ^ n)⁻¹ * c n)
        (fun z => F (z * exp ((-(π / 3) : ℝ) * I))) := by
  have hπ := Real.pi_pos
  constructor
  · have h := airyRot_rot_expansion hδ hF (α := π / 3) (β := 2 * π / 3 - δ)
      (by rw [abs_of_pos (by positivity)]; linarith)
    rwa [airyRot_exp_third_three_halves.1] at h
  · have h := airyRot_rot_expansion hδ hF (α := -(π / 3)) (β := 2 * π / 3 - δ)
      (by rw [abs_neg, abs_of_pos (by positivity)]; linarith)
    rwa [airyRot_exp_third_three_halves.2] at h

/-- The even part has the even subseries `∑ (-1)^j c_{2j} ζ^{-2j}`. -/
theorem airyRot_even_expansion {F : ℂ → ℂ} {c : ℕ → ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hF : HasAsymptoticExpansion (airySector (π - δ))
      (fun (n : ℕ) z => ((airyZetaComplex z) ^ n)⁻¹) c F) :
    HasAsymptoticExpansion (airySector (2 * π / 3 - δ))
      (fun (j : ℕ) z => ((airyZetaComplex z) ^ (2 * j))⁻¹) (fun j => (-1) ^ j * c (2 * j))
      (airyRot_even F) := by
  obtain ⟨hp, hm⟩ := airyRot_pm_expansions hδ hF
  have h := ((hp.add hm).const_smul (1 / 2 : ℂ)).congr' (g := airyRot_even F)
    (Eventually.of_forall fun z => by
      simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, airyRot_even]; ring)
  have h' := h.even (fun j => by
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    have := (airyRot_I_pow_recip_odd j).1
    linear_combination (c (2 * j + 1)) * this)
  refine h'.congr_coeff (funext fun j => ?_)
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  have := (airyRot_I_pow_recip_even j).1
  linear_combination (c (2 * j)) * this

/-- The odd part has the odd subseries `-∑ (-1)^j c_{2j+1} ζ^{-2j-1}`. -/
theorem airyRot_odd_expansion {F : ℂ → ℂ} {c : ℕ → ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hF : HasAsymptoticExpansion (airySector (π - δ))
      (fun (n : ℕ) z => ((airyZetaComplex z) ^ n)⁻¹) c F) :
    HasAsymptoticExpansion (airySector (2 * π / 3 - δ))
      (fun (j : ℕ) z => ((airyZetaComplex z) ^ (2 * j + 1))⁻¹)
      (fun j => -((-1) ^ j * c (2 * j + 1))) (airyRot_odd F) := by
  obtain ⟨hp, hm⟩ := airyRot_pm_expansions hδ hF
  have h := ((hp.sub hm).const_smul (1 / (2 * I) : ℂ)).congr' (g := airyRot_odd F)
    (Eventually.of_forall fun z => by
      simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, airyRot_odd]; ring)
  have h' := h.odd (fun j => by
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    have := (airyRot_I_pow_recip_even j).2
    linear_combination (c (2 * j)) * this)
  refine h'.congr_coeff (funext fun j => ?_)
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  have := (airyRot_I_pow_recip_odd j).2
  linear_combination (c (2 * j + 1)) * this

/-! ### The oscillatory error envelope -/

/-- `‖e^{∓iw}‖ ≤ e^{|Im w|}`. -/
theorem airyRot_norm_exp_mul_I_le (w : ℂ) :
    ‖exp (-(w * I))‖ ≤ Real.exp |w.im| ∧ ‖exp (w * I)‖ ≤ Real.exp |w.im| := by
  constructor <;> rw [Complex.norm_exp] <;> apply Real.exp_le_exp.mpr <;> simp <;>
    [exact le_abs_self _; exact neg_le_abs _]

/-- `‖(w^k)⁻¹‖ = ‖w‖^{-k}`. -/
theorem airyRot_norm_recip_pow (w : ℂ) (k : ℕ) : ‖(w ^ k)⁻¹‖ = ‖w‖ ^ (-(k : ℤ)) := by
  rw [norm_inv, norm_pow, zpow_neg, zpow_natCast]

/-- **The oscillatory envelope.** If `X = pref (a E + b O)` and `Y = pref (a P + b Q)` with
`a, b` combinations of `e^{∓iζ}`, then `X - Y` is bounded by the envelope
`|pref| e^{|im ζ|} (|ζ|^{-2N} + |ζ|^{-2M-1})`. -/
theorem airyRot_osc_bound {l : Filter ℂ} {E O P Q pref X Y : ℂ → ℂ} {N M : ℕ} (κp κm : ℂ)
    (hE : (fun z => E z - P z) =O[l] (fun z => ((airyZetaComplex z) ^ (2 * N))⁻¹))
    (hO : (fun z => O z - Q z) =O[l] (fun z => ((airyZetaComplex z) ^ (2 * M + 1))⁻¹))
    (hX : ∀ᶠ z in l, X z = pref z *
      ((κp * exp (-(airyZetaComplex z * I)) + κm * exp (airyZetaComplex z * I)) * E z +
        I * (κp * exp (-(airyZetaComplex z * I)) - κm * exp (airyZetaComplex z * I)) * O z))
    (hY : ∀ᶠ z in l, Y z = pref z *
      ((κp * exp (-(airyZetaComplex z * I)) + κm * exp (airyZetaComplex z * I)) * P z +
        I * (κp * exp (-(airyZetaComplex z * I)) - κm * exp (airyZetaComplex z * I)) * Q z)) :
    IsBigO l (fun z => X z - Y z) (fun z => ‖pref z‖ * Real.exp |(airyZetaComplex z).im| *
      (‖airyZetaComplex z‖ ^ (-(2 * N : ℤ)) + ‖airyZetaComplex z‖ ^ (-(2 * M + 1 : ℤ)))) := by
  obtain ⟨C1, hC1, h1⟩ := hE.exists_pos
  obtain ⟨C2, hC2, h2⟩ := hO.exists_pos
  set K := ‖κp‖ + ‖κm‖
  refine IsBigO.of_bound (K * (C1 + C2)) ?_
  filter_upwards [h1.bound, h2.bound, hX, hY] with z hz1 hz2 hzX hzY
  rw [hzX, hzY]
  set ζ := airyZetaComplex z
  obtain ⟨he1, he2⟩ := airyRot_norm_exp_mul_I_le ζ
  set A := κp * exp (-(ζ * I)) + κm * exp (ζ * I)
  set B := I * (κp * exp (-(ζ * I)) - κm * exp (ζ * I))
  have hA : ‖A‖ ≤ K * Real.exp |ζ.im| := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    have := norm_nonneg κp; have := norm_nonneg κm
    nlinarith
  have hB : ‖B‖ ≤ K * Real.exp |ζ.im| := by
    rw [norm_mul, norm_I, one_mul]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    have := norm_nonneg κp; have := norm_nonneg κm
    nlinarith
  have heq : pref z * (A * E z + B * O z) - pref z * (A * P z + B * Q z) =
      pref z * (A * (E z - P z) + B * (O z - Q z)) := by ring
  rw [heq]
  rw [airyRot_norm_recip_pow] at hz1 hz2
  have hr1 : (0 : ℝ) ≤ ‖ζ‖ ^ (-(2 * N : ℤ)) := by positivity
  have hr2 : (0 : ℝ) ≤ ‖ζ‖ ^ (-(2 * M + 1 : ℤ)) := by positivity
  have hex := Real.exp_pos |ζ.im|
  have hK : 0 ≤ K := by positivity
  rw [Real.norm_of_nonneg (by positivity)]
  rw [norm_mul]
  push_cast at hz1 hz2 ⊢
  calc ‖pref z‖ * ‖A * (E z - P z) + B * (O z - Q z)‖
      ≤ ‖pref z‖ * (‖A‖ * ‖E z - P z‖ + ‖B‖ * ‖O z - Q z‖) := by
        gcongr
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, norm_mul]
    _ ≤ ‖pref z‖ * (K * Real.exp |ζ.im| * (C1 * ‖ζ‖ ^ (-(2 * (N : ℤ)))) +
          K * Real.exp |ζ.im| * (C2 * ‖ζ‖ ^ (-(2 * (M : ℤ) + 1)))) := by
        gcongr
    _ ≤ K * (C1 + C2) * (‖pref z‖ * Real.exp |ζ.im| *
          (‖ζ‖ ^ (-(2 * (N : ℤ))) + ‖ζ‖ ^ (-(2 * (M : ℤ) + 1)))) := by
        have := norm_nonneg (pref z)
        have hp1 : 0 ≤ ‖pref z‖ * Real.exp |ζ.im| := by positivity
        nlinarith [mul_nonneg hp1 hr1, mul_nonneg hp1 hr2, mul_nonneg hK hC1.le,
          mul_nonneg hK hC2.le, mul_nonneg (mul_nonneg hp1 hr1) (mul_nonneg hK hC2.le),
          mul_nonneg (mul_nonneg hp1 hr2) (mul_nonneg hK hC1.le)]

/-! ### The oscillatory expansions on the negative axis -/

/-- Rewriting `α₊ F(z e^{iπ/3}) + α₋ F(z e^{-iπ/3})` through the even and odd parts. -/
theorem airyRot_decomp (F : ℂ → ℂ) (z αp αm : ℂ) :
    αp * F (z * exp ((π / 3 : ℝ) * I)) + αm * F (z * exp ((-(π / 3) : ℝ) * I)) =
      (αp + αm) * airyRot_even F z + I * (αp - αm) * airyRot_odd F z := by
  simp only [airyRot_even, airyRot_odd]
  field_simp
  ring

/-- For `|arg z| < 2π/3`, `arg z ± π/3` lies in `(-π, π]`. -/
theorem airyRot_arg_third_bounds {z : ℂ} (hz : |arg z| < 2 * π / 3) {ε : ℝ}
    (hε : ε = 1 ∨ ε = -1) : -π < arg z + ε * (π / 3) ∧ arg z + ε * (π / 3) ≤ π := by
  have h1 := abs_lt.mp hz
  have hπ := Real.pi_pos
  rcases hε with h | h <;> subst h <;> constructor <;> linarith

/-- The data of `ζ` and `z^{1/4}` at the points `z e^{±iπ/3}`. -/
theorem airyRot_third_data {z : ℂ} (hz0 : z ≠ 0) (hz : |arg z| < 2 * π / 3) :
    airyZetaComplex (z * exp ((π / 3 : ℝ) * I)) = airyZetaComplex z * I ∧
    airyZetaComplex (z * exp ((-(π / 3) : ℝ) * I)) = -(airyZetaComplex z * I) ∧
    (z * exp ((π / 3 : ℝ) * I)) ^ (1 / 4 : ℂ) = z ^ (1 / 4 : ℂ) * exp (π * I / 12) ∧
    (z * exp ((-(π / 3) : ℝ) * I)) ^ (1 / 4 : ℂ) = z ^ (1 / 4 : ℂ) * (exp (π * I / 12))⁻¹ := by
  obtain ⟨a1, a2⟩ := airyRot_arg_third_bounds hz (Or.inl rfl)
  obtain ⟨b1, b2⟩ := airyRot_arg_third_bounds hz (Or.inr rfl)
  simp only [one_mul, neg_one_mul] at a1 a2 b1 b2
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [airyRot_zeta_mul_exp hz0 a1 a2, airyRot_exp_third_three_halves.1]
  · rw [airyRot_zeta_mul_exp hz0 b1 b2, airyRot_exp_third_three_halves.2]; ring
  · rw [Complex.cpow_mul_exp_ofReal_mul_I hz0 a1 a2]; congr 2; push_cast; ring
  · rw [Complex.cpow_mul_exp_ofReal_mul_I hz0 b1 b2, ← exp_neg]; congr 2; push_cast; ring

/-- DLMF 9.2.14, shared with `DLMF.Airy.Equation` from this earlier module.
The equation module uses the asymptotics here for its numerically satisfactory pairs. -/
theorem airyRot_neg_connection_ai (z : ℂ) :
    airyAi (-z) = exp (π * I / 3) * airyAi (z * exp (π * I / 3)) +
      exp (-π * I / 3) * airyAi (z * exp (-π * I / 3)) := by
  have h := airyAi_add_omega (-z)
  have e1 : -exp (-(2 * π * I / 3)) = exp (π * I / 3) := by
    rw [exp_neg_two_pi_I_div_three, exp_pi_I_div_three]
    push_cast; ring
  have e2 : -exp (2 * π * I / 3) = exp (-π * I / 3) := by
    rw [show -π * I / 3 = -(π * I / 3) by ring, exp_two_pi_I_div_three, exp_neg_pi_I_div_three]
    push_cast; ring
  rw [show -z * exp (-(2 * π * I / 3)) = z * exp (π * I / 3) by rw [← e1]; ring,
    show -z * exp (2 * π * I / 3) = z * exp (-π * I / 3) by rw [← e2]; ring] at h
  linear_combination h + airyAi (z * exp (π * I / 3)) * e1 +
    airyAi (z * exp (-π * I / 3)) * e2

/-- DLMF 9.2.15, shared with the equation module for the same reason. -/
theorem airyRot_neg_connection_bi (z : ℂ) :
    airyBi (-z) = exp (-π * I / 6) * airyAi (z * exp (π * I / 3)) +
      exp (π * I / 6) * airyAi (z * exp (-π * I / 3)) := by
  have h := airyBi_eq_airyAi_omega (-z)
  have e1 : -exp (-(2 * π * I / 3)) = exp (π * I / 3) := by
    rw [exp_neg_two_pi_I_div_three, exp_pi_I_div_three]
    push_cast; ring
  have e2 : -exp (2 * π * I / 3) = exp (-π * I / 3) := by
    rw [show -π * I / 3 = -(π * I / 3) by ring, exp_two_pi_I_div_three, exp_neg_pi_I_div_three]
    push_cast; ring
  simpa only [neg_mul, neg_div, show -z * exp (-(2 * π * I / 3)) = z * exp (π * I / 3) by
    rw [← e1]; ring, show -z * exp (2 * π * I / 3) = z * exp (-π * I / 3) by rw [← e2]; ring] using h

/-- The connection formula for `Ai(-z)` with the rotations written as `e^{iα}`. -/
theorem airyRot_airyAi_neg (z : ℂ) :
    airyAi (-z) = exp (π * I / 3) * airyAi (z * exp ((π / 3 : ℝ) * I)) +
      exp (-π * I / 3) * airyAi (z * exp ((-(π / 3) : ℝ) * I)) := by
  rw [airyRot_neg_connection_ai z]
  congr 4 <;> push_cast <;> ring_nf

/-- `Bi(-z)` with the rotations written as `e^{iα}`. -/
theorem airyRot_airyBi_neg (z : ℂ) :
    airyBi (-z) = exp (-π * I / 6) * airyAi (z * exp ((π / 3 : ℝ) * I)) +
      exp (π * I / 6) * airyAi (z * exp ((-(π / 3) : ℝ) * I)) := by
  rw [airyRot_neg_connection_bi z]
  congr 4 <;> push_cast <;> ring_nf

/-- The twelfth root of `-1`, `u = e^{iπ/12}`, and the exponentials used below. -/
theorem airyRot_u_powers :
    exp (π * I / 3) = exp (π * I / 12) ^ 4 ∧ exp (-π * I / 3) = (exp (π * I / 12) ^ 4)⁻¹ ∧
    exp (π * I / 4) = exp (π * I / 12) ^ 3 ∧ exp (-(π * I / 4)) = (exp (π * I / 12) ^ 3)⁻¹ ∧
    exp (π * I / 6) = exp (π * I / 12) ^ 2 ∧ exp (-π * I / 6) = (exp (π * I / 12) ^ 2)⁻¹ ∧
    exp (π * I / 12) ^ 12 = -1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp only [← exp_nat_mul, ← exp_neg]
  · congr 1; push_cast; ring
  · congr 1; push_cast; ring
  · congr 1; push_cast; ring
  · congr 1; push_cast; ring
  · congr 1; push_cast; ring
  · congr 1; push_cast; ring
  · rw [show ((12 : ℕ) : ℂ) * (π * I / 12) = π * I by push_cast; ring, exp_pi_mul_I]

/-- The sum identity behind the even subseries. -/
theorem airyRot_sum_even {d : ℕ → ℂ} (c : ℕ → ℂ) (hc : ∀ j, c (2 * j) = d (2 * j)) (N : ℕ) (z : ℂ) :
    ∑ j ∈ Finset.range N, ((airyZetaComplex z) ^ (2 * j))⁻¹ • ((-1) ^ j * c (2 * j)) =
      ∑ k ∈ Finset.range N, (-1 : ℂ) ^ k * d (2 * k) / airyZetaComplex z ^ (2 * k) := by
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hc, smul_eq_mul]; ring

/-- The odd part of a series with sign-flipped coefficients is
`∑ (-1)^k d_{2k+1} ζ^{-(2k+1)}`. -/
theorem airyRot_sum_odd {d : ℕ → ℂ} (c : ℕ → ℂ) (hc : ∀ j, c (2 * j + 1) = -d (2 * j + 1)) (M : ℕ) (z : ℂ) :
    ∑ j ∈ Finset.range M, ((airyZetaComplex z) ^ (2 * j + 1))⁻¹ • (-((-1) ^ j * c (2 * j + 1))) =
      ∑ k ∈ Finset.range M, (-1 : ℂ) ^ k * d (2 * k + 1) / airyZetaComplex z ^ (2 * k + 1) := by
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hc, smul_eq_mul]; ring

/-- For `Ai` and `Ai'`, the even coefficients are `u_{2j}` (resp. `v_{2j}`) and the odd ones
their negatives. -/
theorem airyRot_coeff_parity (kind : AiryKind) (hk : kind = .ai ∨ kind = .aiDeriv) (j : ℕ) :
    airyExpansionCoeff kind (2 * j) =
      ((if kind = .aiDeriv then airyV (2 * j) else airyU (2 * j) : ℝ) : ℂ) ∧
    airyExpansionCoeff kind (2 * j + 1) =
      -((if kind = .aiDeriv then airyV (2 * j + 1) else airyU (2 * j + 1) : ℝ) : ℂ) := by
  have h1 : (-1 : ℂ) ^ (2 * j) = 1 := by rw [pow_mul]; norm_num
  have h2 : (-1 : ℂ) ^ (2 * j + 1) = -1 := by rw [pow_succ, h1]; norm_num
  rcases hk with h | h <;> subst h <;> simp [airyExpansionCoeff, h1, h2]

/-- The even and odd parts of the normalized `Ai` at `z e^{±iπ/3}` are approximated by the
oscillatory subseries (used for `Ai(-z)`, `Bi(-z)`, `Bi(z e^{±iπ/3})`) in `|arg z| ≤ 2π/3 - δ`. -/
private lemma airyRot_ai_parts {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 2 * π / 3) (N M : ℕ) :
    (fun z => airyRot_even (fun w => airyAi w / airyPrefactor .ai w) z -
      airyOscSum false 0 N z) =O[airySector (2 * π / 3 - δ)]
      (fun z => ((airyZetaComplex z) ^ (2 * N))⁻¹) ∧
    (fun z => airyRot_odd (fun w => airyAi w / airyPrefactor .ai w) z -
      airyOscSum false 1 M z) =O[airySector (2 * π / 3 - δ)]
      (fun z => ((airyZetaComplex z) ^ (2 * M + 1))⁻¹) := by
  have hF := airyRot_airyAi_expansion hδ (by linarith [Real.pi_pos])
  have hE := (airyRot_even_expansion hδ hF) N
  have hO := (airyRot_odd_expansion hδ hF) M
  refine ⟨?_, ?_⟩
  · refine hE.congr_left fun z => ?_
    dsimp only
    rw [airyRot_sum_even (d := fun k => ((airyU k : ℝ) : ℂ)) _
      (fun j => by simpa using (airyRot_coeff_parity .ai (Or.inl rfl) j).1) N z]
    simp [airyOscSum]
  · refine hO.congr_left fun z => ?_
    dsimp only
    rw [airyRot_sum_odd (d := fun k => ((airyU k : ℝ) : ℂ)) _
      (fun j => by simpa using (airyRot_coeff_parity .ai (Or.inl rfl) j).2) M z]
    simp [airyOscSum]

/-- The oscillatory expansion of `Ai(-z)` in `|arg z| ≤ 2π/3 - δ`: the cosine/sine-weighted
even and odd truncations differ from `Ai(-z)` by `O` of the error envelope (DLMF 9.7.9). -/
@[dlmf 9.7.E9]
theorem airy_ai_oscillatory_expansion {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 2 * π / 3) (N M : ℕ) :
    IsBigO (airySector (2 * π / 3 - δ))
      (fun z => airyFunction .ai (-z) - airyOscApprox .ai N M z)
      (airyOscError .ai N M) := by
  have hπ := Real.pi_pos
  obtain ⟨u4, um4, u3, um3, u2, um2, u12⟩ := airyRot_u_powers
  set u := exp (π * I / 12) with hu
  have hu0 : u ≠ 0 := exp_ne_zero _
  refine airyRot_osc_bound (E := airyRot_even fun w => airyAi w / airyPrefactor .ai w)
    (O := airyRot_odd fun w => airyAi w / airyPrefactor .ai w)
    (P := airyOscSum false 0 N) (Q := airyOscSum false 1 M)
    (exp (π * I / 4) / 2) (exp (-(π * I / 4)) / 2) ?_ ?_ ?_ ?_
  · exact (airyRot_ai_parts hδ hδ' N M).1
  · exact (airyRot_ai_parts hδ hδ' N M).2
  · filter_upwards [airyRot_eventually_arg (2 * π / 3 - δ)] with z hz
    have hz0 := hz.1
    have hz3 : |arg z| < 2 * π / 3 := hz.2.trans_lt (by linarith)
    obtain ⟨d1, d2, d3, d4⟩ := airyRot_third_data hz0 hz3
    have hπs : (Real.sqrt π : ℂ) ≠ 0 :=
      ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
    have hq : z ^ (1 / 4 : ℂ) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hz0)
    have hp1 := airyRot_prefactor_ne_zero .ai (mul_ne_zero hz0 (exp_ne_zero ((π / 3 : ℝ) * I)))
    have hp2 := airyRot_prefactor_ne_zero .ai
      (mul_ne_zero hz0 (exp_ne_zero ((-(π / 3) : ℝ) * I)))
    simp only [airyFunction]
    rw [airyRot_airyAi_neg z]
    rw [show airyAi (z * exp ((π / 3 : ℝ) * I)) = airyPrefactor .ai (z * exp ((π / 3 : ℝ) * I)) *
        (airyAi (z * exp ((π / 3 : ℝ) * I)) / airyPrefactor .ai (z * exp ((π / 3 : ℝ) * I))) by
        field_simp,
      show airyAi (z * exp ((-(π / 3) : ℝ) * I)) =
        airyPrefactor .ai (z * exp ((-(π / 3) : ℝ) * I)) *
        (airyAi (z * exp ((-(π / 3) : ℝ) * I)) /
          airyPrefactor .ai (z * exp ((-(π / 3) : ℝ) * I))) by field_simp]
    rw [← mul_assoc, ← mul_assoc]
    rw [airyRot_decomp (fun w => airyAi w / airyPrefactor .ai w)]
    have ep : exp (π * I / 3) * airyPrefactor .ai (z * exp ((π / 3 : ℝ) * I)) =
        airyOscPrefactor .ai z * (exp (π * I / 4) / 2 * exp (-(airyZetaComplex z * I))) := by
      simp only [airyPrefactor, airyOscPrefactor]
      rw [d1, d3, u4, u3]
      field_simp
      rw [hu]; ring_nf
    have em : exp (-π * I / 3) * airyPrefactor .ai (z * exp ((-(π / 3) : ℝ) * I)) =
        airyOscPrefactor .ai z * (exp (-(π * I / 4)) / 2 * exp (airyZetaComplex z * I)) := by
      simp only [airyPrefactor, airyOscPrefactor]
      rw [d2, d4, um4, um3, neg_neg]
      field_simp
      rw [hu]; ring_nf
    rw [ep, em]
    ring
  · filter_upwards with z
    simp only [airyOscApprox, Complex.cos, Complex.sin]
    have e1 : exp ((airyZetaComplex z - π / 4) * I) =
        exp (-(π * I / 4)) * exp (airyZetaComplex z * I) := by
      rw [← exp_add]; congr 1; ring
    have e2 : exp (-(airyZetaComplex z - π / 4) * I) =
        exp (π * I / 4) * exp (-(airyZetaComplex z * I)) := by
      rw [← exp_add]; congr 1; ring
    rw [e1, e2]
    ring

/-- `exp ((±π/3 : ℝ) i) = exp (±πi/3)` (cast normalization). -/
theorem airyRot_exp_third_ofReal :
    exp ((π / 3 : ℝ) * I) = exp (π * I / 3) ∧ exp ((-(π / 3) : ℝ) * I) = exp (-π * I / 3) := by
  constructor <;> (congr 1; push_cast; ring)

/-- `Ai'(-z) = e^{-iπ/3} Ai'(z e^{iπ/3}) + e^{iπ/3} Ai'(z e^{-iπ/3})`. -/
theorem airyRot_airyAiDeriv_neg (z : ℂ) :
    airyAiDeriv (-z) = exp (-π * I / 3) * airyAiDeriv (z * exp ((π / 3 : ℝ) * I)) +
      exp (π * I / 3) * airyAiDeriv (z * exp ((-(π / 3) : ℝ) * I)) := by
  have h := airyRot_deriv_of_eq (f := fun z => airyAi (-z)) (f' := fun z => -airyAiDeriv (-z))
    (fun z => by simpa [Function.comp_def] using
      (hasDerivAt_airyAi (-z)).comp z (hasDerivAt_id z).neg)
    hasDerivAt_airyAi _ _ _ _ airyRot_airyAi_neg z
  obtain ⟨u4, um4, -, -, -, -, u12⟩ := airyRot_u_powers
  obtain ⟨k1, k2⟩ := airyRot_exp_third_ofReal
  rw [k1, k2] at h ⊢
  rw [u4, um4] at h ⊢
  have hu0 : exp (π * I / 12) ≠ 0 := exp_ne_zero _
  have h' : airyAiDeriv (-z) = (-(exp (π * I / 12) ^ 4 * exp (π * I / 12) ^ 4)) *
      airyAiDeriv (z * exp (π * I / 12) ^ 4) + (-((exp (π * I / 12) ^ 4)⁻¹ *
      (exp (π * I / 12) ^ 4)⁻¹)) * airyAiDeriv (z * (exp (π * I / 12) ^ 4)⁻¹) := by
    linear_combination -h
  have e1 : -(exp (π * I / 12) ^ 4 * exp (π * I / 12) ^ 4) = (exp (π * I / 12) ^ 4)⁻¹ := by
    field_simp; linear_combination -u12
  have e2 : -((exp (π * I / 12) ^ 4)⁻¹ * (exp (π * I / 12) ^ 4)⁻¹) = exp (π * I / 12) ^ 4 := by
    field_simp; linear_combination -u12
  rw [h', e1, e2]

/-- `Bi'(-z) = -e^{iπ/6} Ai'(z e^{iπ/3}) - e^{-iπ/6} Ai'(z e^{-iπ/3})`. -/
theorem airyRot_airyBiDeriv_neg (z : ℂ) :
    airyBiDeriv (-z) = -exp (π * I / 6) * airyAiDeriv (z * exp ((π / 3 : ℝ) * I)) +
      -exp (-π * I / 6) * airyAiDeriv (z * exp ((-(π / 3) : ℝ) * I)) := by
  have h := airyRot_deriv_of_eq (f := fun z => airyBi (-z)) (f' := fun z => -airyBiDeriv (-z))
    (fun z => by simpa [Function.comp_def] using
      (hasDerivAt_airyBi (-z)).comp z (hasDerivAt_id z).neg)
    hasDerivAt_airyAi _ _ _ _ airyRot_airyBi_neg z
  obtain ⟨u4, um4, -, -, u2, um2, u12⟩ := airyRot_u_powers
  obtain ⟨k1, k2⟩ := airyRot_exp_third_ofReal
  rw [k1, k2] at h ⊢
  rw [u4, um4, u2, um2] at h ⊢
  have hu0 : exp (π * I / 12) ≠ 0 := exp_ne_zero _
  have e1 : (exp (π * I / 12) ^ 2)⁻¹ * exp (π * I / 12) ^ 4 = exp (π * I / 12) ^ 2 := by
    field_simp
  have e2 : exp (π * I / 12) ^ 2 * (exp (π * I / 12) ^ 4)⁻¹ = (exp (π * I / 12) ^ 2)⁻¹ := by
    field_simp
  rw [e1, e2] at h
  linear_combination -h

/-- The even and odd parts of the normalized `Ai'` at `z e^{±iπ/3}` are approximated by the
oscillatory subseries (used for the derivatives) in `|arg z| ≤ 2π/3 - δ`. -/
private lemma airyRot_aiDeriv_parts {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 2 * π / 3) (N M : ℕ) :
    (fun z => airyRot_even (fun w => airyAiDeriv w / airyPrefactor .aiDeriv w) z -
      airyOscSum true 0 N z) =O[airySector (2 * π / 3 - δ)]
      (fun z => ((airyZetaComplex z) ^ (2 * N))⁻¹) ∧
    (fun z => airyRot_odd (fun w => airyAiDeriv w / airyPrefactor .aiDeriv w) z -
      airyOscSum true 1 M z) =O[airySector (2 * π / 3 - δ)]
      (fun z => ((airyZetaComplex z) ^ (2 * M + 1))⁻¹) := by
  have hF := airyRot_airyAiDeriv_expansion hδ (by linarith [Real.pi_pos])
  have hE := (airyRot_even_expansion hδ hF) N
  have hO := (airyRot_odd_expansion hδ hF) M
  refine ⟨?_, ?_⟩
  · refine hE.congr_left fun z => ?_
    dsimp only
    rw [airyRot_sum_even (d := fun k => ((airyV k : ℝ) : ℂ)) _
      (fun j => by simpa using (airyRot_coeff_parity .aiDeriv (Or.inr rfl) j).1) N z]
    simp [airyOscSum]
  · refine hO.congr_left fun z => ?_
    dsimp only
    rw [airyRot_sum_odd (d := fun k => ((airyV k : ℝ) : ℂ)) _
      (fun j => by simpa using (airyRot_coeff_parity .aiDeriv (Or.inr rfl) j).2) M z]
    simp [airyOscSum]

/-- The oscillatory expansion of `Ai'(-z)` in `|arg z| ≤ 2π/3 - δ`, with error `O` of the
envelope `airyOscError` (DLMF 9.7.10). -/
@[dlmf 9.7.E10]
theorem airy_aiDeriv_oscillatory_expansion {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 2 * π / 3) (N M : ℕ) :
    IsBigO (airySector (2 * π / 3 - δ))
      (fun z => airyFunction .aiDeriv (-z) - airyOscApprox .aiDeriv N M z)
      (airyOscError .aiDeriv N M) := by
  have hπ := Real.pi_pos
  obtain ⟨u4, um4, u3, um3, u2, um2, u12⟩ := airyRot_u_powers
  set u := exp (π * I / 12) with hu
  have hu0 : u ≠ 0 := exp_ne_zero _
  refine airyRot_osc_bound (E := airyRot_even fun w => airyAiDeriv w / airyPrefactor .aiDeriv w)
    (O := airyRot_odd fun w => airyAiDeriv w / airyPrefactor .aiDeriv w)
    (P := airyOscSum true 0 N) (Q := airyOscSum true 1 M)
    (-(exp (-(π * I / 4)) / 2)) (-(exp (π * I / 4) / 2)) ?_ ?_ ?_ ?_
  · exact (airyRot_aiDeriv_parts hδ hδ' N M).1
  · exact (airyRot_aiDeriv_parts hδ hδ' N M).2
  · filter_upwards [airyRot_eventually_arg (2 * π / 3 - δ)] with z hz
    have hz0 := hz.1
    have hz3 : |arg z| < 2 * π / 3 := hz.2.trans_lt (by linarith)
    obtain ⟨d1, d2, d3, d4⟩ := airyRot_third_data hz0 hz3
    have hπs : (Real.sqrt π : ℂ) ≠ 0 :=
      ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
    have hq : z ^ (1 / 4 : ℂ) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hz0)
    have hp1 := airyRot_prefactor_ne_zero .aiDeriv
      (mul_ne_zero hz0 (exp_ne_zero ((π / 3 : ℝ) * I)))
    have hp2 := airyRot_prefactor_ne_zero .aiDeriv
      (mul_ne_zero hz0 (exp_ne_zero ((-(π / 3) : ℝ) * I)))
    simp only [airyFunction]
    rw [airyRot_airyAiDeriv_neg z]
    rw [show airyAiDeriv (z * exp ((π / 3 : ℝ) * I)) =
        airyPrefactor .aiDeriv (z * exp ((π / 3 : ℝ) * I)) *
        (airyAiDeriv (z * exp ((π / 3 : ℝ) * I)) /
          airyPrefactor .aiDeriv (z * exp ((π / 3 : ℝ) * I))) by field_simp,
      show airyAiDeriv (z * exp ((-(π / 3) : ℝ) * I)) =
        airyPrefactor .aiDeriv (z * exp ((-(π / 3) : ℝ) * I)) *
        (airyAiDeriv (z * exp ((-(π / 3) : ℝ) * I)) /
          airyPrefactor .aiDeriv (z * exp ((-(π / 3) : ℝ) * I))) by field_simp]
    rw [← mul_assoc, ← mul_assoc]
    rw [airyRot_decomp (fun w => airyAiDeriv w / airyPrefactor .aiDeriv w)]
    have ep : exp (-π * I / 3) * airyPrefactor .aiDeriv (z * exp ((π / 3 : ℝ) * I)) =
        airyOscPrefactor .aiDeriv z *
          (-(exp (-(π * I / 4)) / 2) * exp (-(airyZetaComplex z * I))) := by
      simp only [airyPrefactor, airyOscPrefactor]
      rw [d1, d3, ← hu, um4, um3]
      field_simp
    have em : exp (π * I / 3) * airyPrefactor .aiDeriv (z * exp ((-(π / 3) : ℝ) * I)) =
        airyOscPrefactor .aiDeriv z * (-(exp (π * I / 4) / 2) * exp (airyZetaComplex z * I)) := by
      simp only [airyPrefactor, airyOscPrefactor]
      rw [d2, d4, ← hu, u4, u3, neg_neg]
      field_simp
    rw [ep, em]
    ring
  · filter_upwards with z
    simp only [airyOscApprox]
    rw [show cos (airyZetaComplex z - π / 4) = sin (airyZetaComplex z - π / 4 + π / 2) from
        (Complex.sin_add_pi_div_two _).symm,
      show sin (airyZetaComplex z - π / 4) = -cos (airyZetaComplex z - π / 4 + π / 2) by
        rw [Complex.cos_add_pi_div_two]; ring]
    simp only [Complex.cos, Complex.sin]
    have e1 : exp ((airyZetaComplex z - π / 4 + π / 2) * I) =
        exp (π * I / 4) * exp (airyZetaComplex z * I) := by
      rw [← exp_add]; congr 1; ring
    have e2 : exp (-(airyZetaComplex z - π / 4 + π / 2) * I) =
        exp (-(π * I / 4)) * exp (-(airyZetaComplex z * I)) := by
      rw [← exp_add]; congr 1; ring
    rw [e1, e2]
    ring

/-- The oscillatory expansion of `Bi(-z)` in `|arg z| ≤ 2π/3 - δ`, with error `O` of the
envelope `airyOscError` (DLMF 9.7.11). -/
@[dlmf 9.7.E11]
theorem airy_bi_oscillatory_expansion {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 2 * π / 3) (N M : ℕ) :
    IsBigO (airySector (2 * π / 3 - δ))
      (fun z => airyFunction .bi (-z) - airyOscApprox .bi N M z)
      (airyOscError .bi N M) := by
  have hπ := Real.pi_pos
  obtain ⟨u4, um4, u3, um3, u2, um2, u12⟩ := airyRot_u_powers
  set u := exp (π * I / 12) with hu
  have hu0 : u ≠ 0 := exp_ne_zero _
  refine airyRot_osc_bound (E := airyRot_even fun w => airyAi w / airyPrefactor .ai w)
    (O := airyRot_odd fun w => airyAi w / airyPrefactor .ai w)
    (P := airyOscSum false 0 N) (Q := airyOscSum false 1 M)
    (exp (-(π * I / 4)) / 2) (exp (π * I / 4) / 2) ?_ ?_ ?_ ?_
  · exact (airyRot_ai_parts hδ hδ' N M).1
  · exact (airyRot_ai_parts hδ hδ' N M).2
  · filter_upwards [airyRot_eventually_arg (2 * π / 3 - δ)] with z hz
    have hz0 := hz.1
    have hz3 : |arg z| < 2 * π / 3 := hz.2.trans_lt (by linarith)
    obtain ⟨d1, d2, d3, d4⟩ := airyRot_third_data hz0 hz3
    have hπs : (Real.sqrt π : ℂ) ≠ 0 :=
      ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
    have hq : z ^ (1 / 4 : ℂ) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hz0)
    have hp1 := airyRot_prefactor_ne_zero .ai
      (mul_ne_zero hz0 (exp_ne_zero ((π / 3 : ℝ) * I)))
    have hp2 := airyRot_prefactor_ne_zero .ai
      (mul_ne_zero hz0 (exp_ne_zero ((-(π / 3) : ℝ) * I)))
    simp only [airyFunction]
    rw [airyRot_airyBi_neg z]
    rw [show airyAi (z * exp ((π / 3 : ℝ) * I)) =
        airyPrefactor .ai (z * exp ((π / 3 : ℝ) * I)) *
        (airyAi (z * exp ((π / 3 : ℝ) * I)) /
          airyPrefactor .ai (z * exp ((π / 3 : ℝ) * I))) by field_simp,
      show airyAi (z * exp ((-(π / 3) : ℝ) * I)) =
        airyPrefactor .ai (z * exp ((-(π / 3) : ℝ) * I)) *
        (airyAi (z * exp ((-(π / 3) : ℝ) * I)) /
          airyPrefactor .ai (z * exp ((-(π / 3) : ℝ) * I))) by field_simp]
    rw [← mul_assoc, ← mul_assoc]
    rw [airyRot_decomp (fun w => airyAi w / airyPrefactor .ai w)]
    have ep : exp (-π * I / 6) * airyPrefactor .ai (z * exp ((π / 3 : ℝ) * I)) =
        airyOscPrefactor .bi z *
          (exp (-(π * I / 4)) / 2 * exp (-(airyZetaComplex z * I))) := by
      simp only [airyPrefactor, airyOscPrefactor]
      rw [d1, d3, ← hu, um2, um3]
      field_simp
    have em : exp (π * I / 6) * airyPrefactor .ai (z * exp ((-(π / 3) : ℝ) * I)) =
        airyOscPrefactor .bi z * (exp (π * I / 4) / 2 * exp (airyZetaComplex z * I)) := by
      simp only [airyPrefactor, airyOscPrefactor]
      rw [d2, d4, ← hu, u2, u3, neg_neg]
      field_simp
    rw [ep, em]
    ring
  · filter_upwards with z
    simp only [airyOscApprox]
    rw [show cos (airyZetaComplex z - π / 4) = sin (airyZetaComplex z - π / 4 + π / 2) from
        (Complex.sin_add_pi_div_two _).symm,
      show sin (airyZetaComplex z - π / 4) = -cos (airyZetaComplex z - π / 4 + π / 2) by
        rw [Complex.cos_add_pi_div_two]; ring]
    simp only [Complex.cos, Complex.sin]
    have e1 : exp ((airyZetaComplex z - π / 4 + π / 2) * I) =
        exp (π * I / 4) * exp (airyZetaComplex z * I) := by
      rw [← exp_add]; congr 1; ring
    have e2 : exp (-(airyZetaComplex z - π / 4 + π / 2) * I) =
        exp (-(π * I / 4)) * exp (-(airyZetaComplex z * I)) := by
      rw [← exp_add]; congr 1; ring
    rw [e1, e2]
    ring

/-- The oscillatory expansion of `Bi'(-z)` in `|arg z| ≤ 2π/3 - δ`, with error `O` of the
envelope `airyOscError` (DLMF 9.7.12). -/
@[dlmf 9.7.E12]
theorem airy_biDeriv_oscillatory_expansion {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 2 * π / 3) (N M : ℕ) :
    IsBigO (airySector (2 * π / 3 - δ))
      (fun z => airyFunction .biDeriv (-z) - airyOscApprox .biDeriv N M z)
      (airyOscError .biDeriv N M) := by
  have hπ := Real.pi_pos
  obtain ⟨u4, um4, u3, um3, u2, um2, u12⟩ := airyRot_u_powers
  set u := exp (π * I / 12) with hu
  have hu0 : u ≠ 0 := exp_ne_zero _
  refine airyRot_osc_bound (E := airyRot_even fun w => airyAiDeriv w / airyPrefactor .aiDeriv w)
    (O := airyRot_odd fun w => airyAiDeriv w / airyPrefactor .aiDeriv w)
    (P := airyOscSum true 0 N) (Q := airyOscSum true 1 M)
    (exp (π * I / 4) / 2) (exp (-(π * I / 4)) / 2) ?_ ?_ ?_ ?_
  · exact (airyRot_aiDeriv_parts hδ hδ' N M).1
  · exact (airyRot_aiDeriv_parts hδ hδ' N M).2
  · filter_upwards [airyRot_eventually_arg (2 * π / 3 - δ)] with z hz
    have hz0 := hz.1
    have hz3 : |arg z| < 2 * π / 3 := hz.2.trans_lt (by linarith)
    obtain ⟨d1, d2, d3, d4⟩ := airyRot_third_data hz0 hz3
    have hπs : (Real.sqrt π : ℂ) ≠ 0 :=
      ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
    have hq : z ^ (1 / 4 : ℂ) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hz0)
    have hp1 := airyRot_prefactor_ne_zero .aiDeriv
      (mul_ne_zero hz0 (exp_ne_zero ((π / 3 : ℝ) * I)))
    have hp2 := airyRot_prefactor_ne_zero .aiDeriv
      (mul_ne_zero hz0 (exp_ne_zero ((-(π / 3) : ℝ) * I)))
    simp only [airyFunction]
    rw [airyRot_airyBiDeriv_neg z]
    rw [show airyAiDeriv (z * exp ((π / 3 : ℝ) * I)) =
        airyPrefactor .aiDeriv (z * exp ((π / 3 : ℝ) * I)) *
        (airyAiDeriv (z * exp ((π / 3 : ℝ) * I)) /
          airyPrefactor .aiDeriv (z * exp ((π / 3 : ℝ) * I))) by field_simp,
      show airyAiDeriv (z * exp ((-(π / 3) : ℝ) * I)) =
        airyPrefactor .aiDeriv (z * exp ((-(π / 3) : ℝ) * I)) *
        (airyAiDeriv (z * exp ((-(π / 3) : ℝ) * I)) /
          airyPrefactor .aiDeriv (z * exp ((-(π / 3) : ℝ) * I))) by field_simp]
    rw [← mul_assoc, ← mul_assoc]
    rw [airyRot_decomp (fun w => airyAiDeriv w / airyPrefactor .aiDeriv w)]
    have ep : -exp (π * I / 6) * airyPrefactor .aiDeriv (z * exp ((π / 3 : ℝ) * I)) =
        airyOscPrefactor .biDeriv z *
          (exp (π * I / 4) / 2 * exp (-(airyZetaComplex z * I))) := by
      simp only [airyPrefactor, airyOscPrefactor]
      rw [d1, d3, ← hu, u2, u3]
      field_simp
    have em : -exp (-π * I / 6) * airyPrefactor .aiDeriv (z * exp ((-(π / 3) : ℝ) * I)) =
        airyOscPrefactor .biDeriv z * (exp (-(π * I / 4)) / 2 * exp (airyZetaComplex z * I)) := by
      simp only [airyPrefactor, airyOscPrefactor]
      rw [d2, d4, ← hu, um2, um3, neg_neg]
      field_simp
    rw [ep, em]
    ring
  · filter_upwards with z
    simp only [airyOscApprox, Complex.cos, Complex.sin]
    have e1 : exp ((airyZetaComplex z - π / 4) * I) =
        exp (-(π * I / 4)) * exp (airyZetaComplex z * I) := by
      rw [← exp_add]; congr 1; ring
    have e2 : exp (-(airyZetaComplex z - π / 4) * I) =
        exp (π * I / 4) * exp (-(airyZetaComplex z * I)) := by
      rw [← exp_add]; congr 1; ring
    rw [e1, e2]
    ring

/-- `(e^{πi/12})^6 = i`. -/
theorem airyRot_u_six : exp (π * I / 12) ^ 6 = I := by
  rw [← exp_nat_mul, show ((6 : ℕ) : ℂ) * (π * I / 12) = (π / 2 : ℂ) * I by push_cast; ring,
    exp_pi_div_two_mul_I]

/-- `Bi(z e^{iπ/3}) = i Ai(z e^{iπ/3}) + 2 e^{-iπ/6} Ai(z e^{-iπ/3})`. -/
theorem airyRot_airyBi_rot_pos (z : ℂ) :
    airyBi (z * exp (π * I / 3)) = I * airyAi (z * exp ((π / 3 : ℝ) * I)) +
      2 * exp (-π * I / 6) * airyAi (z * exp ((-(π / 3) : ℝ) * I)) := by
  rw [airyBi_eq_airyAi_omega,
    show z * exp (π * I / 3) * exp (-(2 * π * I / 3)) = z * exp ((-(π / 3) : ℝ) * I) by
      rw [mul_assoc, ← exp_add]; congr 2; push_cast; ring,
    show z * exp (π * I / 3) * exp (2 * π * I / 3) = -z by
      rw [mul_assoc, ← exp_add, show π * I / 3 + 2 * π * I / 3 = π * I by ring, exp_pi_mul_I]
      ring,
    airyRot_airyAi_neg z]
  obtain ⟨u4, um4, -, -, u2, um2, u12⟩ := airyRot_u_powers
  have k : exp (-(π * I / 6)) = exp (-π * I / 6) := by congr 1; ring
  have hu6 := airyRot_u_six
  rw [k, u4, um4, u2, um2]
  set u := exp (π * I / 12)
  set A := airyAi (z * exp ((π / 3 : ℝ) * I))
  set B := airyAi (z * exp ((-(π / 3) : ℝ) * I))
  have hu0 : u ≠ 0 := exp_ne_zero _
  rw [← hu6]
  field_simp
  ring

/-- `Bi(z e^{-iπ/3}) = 2 e^{iπ/6} Ai(z e^{iπ/3}) - i Ai(z e^{-iπ/3})`. -/
theorem airyRot_airyBi_rot_neg (z : ℂ) :
    airyBi (z * exp (-(π * I / 3))) = 2 * exp (π * I / 6) * airyAi (z * exp ((π / 3 : ℝ) * I)) -
      I * airyAi (z * exp ((-(π / 3) : ℝ) * I)) := by
  rw [airyBi_eq_airyAi_omega,
    show z * exp (-(π * I / 3)) * exp (2 * π * I / 3) = z * exp ((π / 3 : ℝ) * I) by
      rw [mul_assoc, ← exp_add]; congr 2; push_cast; ring,
    show z * exp (-(π * I / 3)) * exp (-(2 * π * I / 3)) = -z by
      rw [mul_assoc, ← exp_add, show -(π * I / 3) + -(2 * π * I / 3) = -(π * I) by ring,
        exp_neg, exp_pi_mul_I]
      ring,
    airyRot_airyAi_neg z]
  obtain ⟨u4, um4, -, -, u2, um2, u12⟩ := airyRot_u_powers
  have k : exp (-(π * I / 6)) = exp (-π * I / 6) := by congr 1; ring
  have hu6 := airyRot_u_six
  rw [k, u4, um4, u2, um2]
  set u := exp (π * I / 12)
  set A := airyAi (z * exp ((π / 3 : ℝ) * I))
  set B := airyAi (z * exp ((-(π / 3) : ℝ) * I))
  have hu0 : u ≠ 0 := exp_ne_zero _
  rw [← hu6]
  field_simp
  linear_combination B * u12

/-- `exp (log 2 / 2) = √2`. -/
theorem airyRot_exp_half_log_two : exp ((Real.log 2 : ℂ) / 2) = (Real.sqrt 2 : ℂ) := by
  rw [show (Real.log 2 : ℂ) / 2 = ((Real.log 2 / 2 : ℝ) : ℂ) by push_cast; ring, ← ofReal_exp]
  congr 1
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos two_pos]; ring_nf

/-- `(2/π)^{1/2} = √2/√π` in `ℂ`. -/
theorem airyRot_two_div_pi_cpow :
    (2 / π : ℂ) ^ (1 / 2 : ℂ) = (Real.sqrt 2 : ℂ) / (Real.sqrt π : ℂ) := by
  rw [show (2 / π : ℂ) = ((2 / π : ℝ) : ℂ) by push_cast; ring,
    show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring,
    ← ofReal_cpow (by positivity), ← Real.sqrt_eq_rpow, Real.sqrt_div' _ Real.pi_pos.le]
  push_cast; ring

/-- `‖exp (ε c i)‖ = 1` for real `ε, c`. -/
theorem airyRot_norm_exp_real_mul (ε : ℝ) (c : ℝ) : ‖exp (ε * (c * I))‖ = 1 := by
  rw [show (ε : ℂ) * (c * I) = ((ε * c : ℝ) : ℂ) * I by push_cast; ring, norm_exp_ofReal_mul_I]

/-- `‖(2/π)^{1/2}‖ = √2/√π`. -/
theorem airyRot_norm_two_div_pi_cpow :
    ‖(2 / π : ℂ) ^ (1 / 2 : ℂ)‖ = Real.sqrt 2 / Real.sqrt π := by
  rw [airyRot_two_div_pi_cpow, norm_div, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.norm_of_nonneg (Real.sqrt_nonneg _)]

/-- The prefactor of 9.7.13 is `√2` times that of 9.7.11 in norm. -/
theorem airyRot_norm_rot_pref (ε : ℝ) (z : ℂ) :
    ‖(2 / π : ℂ) ^ (1 / 2 : ℂ) * exp (ε * (π * I / 6)) * z ^ (-1 / 4 : ℂ)‖ =
      Real.sqrt 2 * ‖airyOscPrefactor .bi z‖ := by
  rw [show (ε : ℂ) * (π * I / 6) = ε * (((π / 6 : ℝ) : ℂ) * I) by push_cast; ring,
    norm_mul, norm_mul, airyRot_norm_exp_real_mul, airyRot_norm_two_div_pi_cpow,
    show (-1 / 4 : ℂ) = -(1 / 4) by ring, cpow_neg, airyOscPrefactor, norm_div, norm_mul,
    norm_inv, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  simp only [norm_one]
  ring

/-- The prefactor of 9.7.14 is `√2` times that of 9.7.12 in norm. -/
theorem airyRot_norm_rot_pref' (ε : ℝ) (z : ℂ) :
    ‖(2 / π : ℂ) ^ (1 / 2 : ℂ) * exp (-ε * (π * I / 6)) * z ^ (1 / 4 : ℂ)‖ =
      Real.sqrt 2 * ‖airyOscPrefactor .biDeriv z‖ := by
  rw [show (-ε : ℂ) * (π * I / 6) = ((-ε : ℝ) : ℂ) * (((π / 6 : ℝ) : ℂ) * I) by push_cast; ring,
    norm_mul, norm_mul, airyRot_norm_exp_real_mul, airyRot_norm_two_div_pi_cpow,
    airyOscPrefactor, norm_div, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  ring

/-- Passing from the `√2`-scaled envelope to `airyOscError`. -/
theorem airyRot_envelope {l : Filter ℂ} (kind : AiryKind) (pref : ℂ → ℂ) (N M : ℕ)
    (h : ∀ z, ‖pref z‖ = Real.sqrt 2 * ‖airyOscPrefactor kind z‖) :
    (fun z => ‖pref z‖ * Real.exp |(airyZetaComplex z).im| *
      (‖airyZetaComplex z‖ ^ (-(2 * N : ℤ)) + ‖airyZetaComplex z‖ ^ (-(2 * M + 1 : ℤ))))
      =O[l] airyOscError kind N M := by
  refine ((isBigO_refl (airyOscError kind N M) l).const_mul_left (Real.sqrt 2)).congr_left
    fun z => ?_
  rw [h, airyOscError]; ring

/-- At `z` with `|arg z| < 2π/3`, `Bi(z e^{±iπ/3})` is the rotated prefactor times the
cosine/sine combination of the even and odd parts of the normalized `Ai` (via 9.2.11). -/
private lemma airyRot_bi_rot_eq {z : ℂ} (hz0 : z ≠ 0) (hz3 : |arg z| < 2 * π / 3) {ε : ℝ}
    (hε : ε = 1 ∨ ε = -1) :
    airyBi (z * exp (ε * (π * I / 3))) =
      (2 / π : ℂ) ^ (1 / 2 : ℂ) * exp (ε * (π * I / 6)) * z ^ (-1 / 4 : ℂ) *
        (((exp (π * I / 4) * exp (-((ε : ℂ) * Real.log 2 / 2)) / 2) *
              exp (-(airyZetaComplex z * I)) +
            (exp (-(π * I / 4)) * exp ((ε : ℂ) * Real.log 2 / 2) / 2) *
              exp (airyZetaComplex z * I)) *
            airyRot_even (fun w => airyAi w / airyPrefactor .ai w) z +
          I * ((exp (π * I / 4) * exp (-((ε : ℂ) * Real.log 2 / 2)) / 2) *
              exp (-(airyZetaComplex z * I)) -
            (exp (-(π * I / 4)) * exp ((ε : ℂ) * Real.log 2 / 2) / 2) *
              exp (airyZetaComplex z * I)) *
            airyRot_odd (fun w => airyAi w / airyPrefactor .ai w) z) := by
  obtain ⟨u4, um4, u3, um3, u2, um2, u12⟩ := airyRot_u_powers
  have hu6 := airyRot_u_six
  have hs : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
    rw [← ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have hs0 : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (by positivity)
  have hπs : (Real.sqrt π : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hl : exp (-((Real.log 2 : ℂ) / 2)) = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ := by
    rw [exp_neg, airyRot_exp_half_log_two]
  obtain ⟨d1, d2, d3, d4⟩ := airyRot_third_data hz0 hz3
  have hq : z ^ (1 / 4 : ℂ) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hz0)
  have hp1 := airyRot_prefactor_ne_zero .ai (mul_ne_zero hz0 (exp_ne_zero ((π / 3 : ℝ) * I)))
  have hp2 := airyRot_prefactor_ne_zero .ai
    (mul_ne_zero hz0 (exp_ne_zero ((-(π / 3) : ℝ) * I)))
  have split1 : airyAi (z * exp ((π / 3 : ℝ) * I)) =
      airyPrefactor .ai (z * exp ((π / 3 : ℝ) * I)) *
      (airyAi (z * exp ((π / 3 : ℝ) * I)) / airyPrefactor .ai (z * exp ((π / 3 : ℝ) * I))) := by
    field_simp
  have split2 : airyAi (z * exp ((-(π / 3) : ℝ) * I)) =
      airyPrefactor .ai (z * exp ((-(π / 3) : ℝ) * I)) *
      (airyAi (z * exp ((-(π / 3) : ℝ) * I)) /
        airyPrefactor .ai (z * exp ((-(π / 3) : ℝ) * I))) := by field_simp
  have hneg : z ^ (-1 / 4 : ℂ) = (z ^ (1 / 4 : ℂ))⁻¹ := by
    rw [show (-1 / 4 : ℂ) = -(1 / 4) by ring, cpow_neg]
  rcases hε with rfl | rfl
  · simp only [ofReal_one, one_mul]
    rw [airyRot_airyBi_rot_pos z, split1, split2, ← mul_assoc, ← mul_assoc,
      airyRot_decomp (fun w => airyAi w / airyPrefactor .ai w)]
    have ep : I * airyPrefactor .ai (z * exp ((π / 3 : ℝ) * I)) =
        (2 / π : ℂ) ^ (1 / 2 : ℂ) * exp (π * I / 6) * z ^ (-1 / 4 : ℂ) *
          (exp (π * I / 4) * exp (-((Real.log 2 : ℂ) / 2)) / 2 *
            exp (-(airyZetaComplex z * I))) := by
      simp only [airyPrefactor]
      rw [d1, d3, airyRot_two_div_pi_cpow, hl, hneg, u2, u3]
      set u := exp (π * I / 12)
      have hu0 : u ≠ 0 := exp_ne_zero _
      rw [← hu6]
      field_simp
    have em : 2 * exp (-π * I / 6) * airyPrefactor .ai (z * exp ((-(π / 3) : ℝ) * I)) =
        (2 / π : ℂ) ^ (1 / 2 : ℂ) * exp (π * I / 6) * z ^ (-1 / 4 : ℂ) *
          (exp (-(π * I / 4)) * exp ((Real.log 2 : ℂ) / 2) / 2 * exp (airyZetaComplex z * I)) := by
      simp only [airyPrefactor]
      rw [d2, d4, airyRot_two_div_pi_cpow, airyRot_exp_half_log_two, hneg, u2, um2, um3, neg_neg]
      set u := exp (π * I / 12)
      have hu0 : u ≠ 0 := exp_ne_zero _
      field_simp
      linear_combination -hs
    rw [ep, em]
    ring_nf
  · simp only [ofReal_neg, ofReal_one, neg_one_mul]
    rw [airyRot_airyBi_rot_neg z, split1, split2, sub_eq_add_neg, ← neg_mul, ← mul_assoc,
      ← mul_assoc, airyRot_decomp (fun w => airyAi w / airyPrefactor .ai w)]
    have ep : 2 * exp (π * I / 6) * airyPrefactor .ai (z * exp ((π / 3 : ℝ) * I)) =
        (2 / π : ℂ) ^ (1 / 2 : ℂ) * exp (-(π * I / 6)) * z ^ (-1 / 4 : ℂ) *
          (exp (π * I / 4) * exp ((Real.log 2 : ℂ) / 2) / 2 *
            exp (-(airyZetaComplex z * I))) := by
      simp only [airyPrefactor]
      rw [d1, d3, airyRot_two_div_pi_cpow, airyRot_exp_half_log_two, hneg, u2, u3,
        show -(π * I / 6) = -π * I / 6 by ring, um2]
      set u := exp (π * I / 12)
      have hu0 : u ≠ 0 := exp_ne_zero _
      field_simp
      linear_combination -hs
    have em : -I * airyPrefactor .ai (z * exp ((-(π / 3) : ℝ) * I)) =
        (2 / π : ℂ) ^ (1 / 2 : ℂ) * exp (-(π * I / 6)) * z ^ (-1 / 4 : ℂ) *
          (exp (-(π * I / 4)) * exp (-((Real.log 2 : ℂ) / 2)) / 2 *
            exp (airyZetaComplex z * I)) := by
      simp only [airyPrefactor]
      rw [d2, d4, airyRot_two_div_pi_cpow, hl, hneg, um3,
        show -(π * I / 6) = -π * I / 6 by ring, um2, neg_neg]
      set u := exp (π * I / 12)
      have hu0 : u ≠ 0 := exp_ne_zero _
      rw [← hu6]
      field_simp
      linear_combination -u12
    rw [ep, em]
    ring_nf

/-- `airyRotatedBiApprox false ε N M z` in the cosine/sine form used by `airyRot_osc_bound`. -/
private lemma airyRot_bi_approx_eq (ε : ℝ) (N M : ℕ) (z : ℂ) :
    airyRotatedBiApprox false ε N M z =
      (2 / π : ℂ) ^ (1 / 2 : ℂ) * exp (ε * (π * I / 6)) * z ^ (-1 / 4 : ℂ) *
        (((exp (π * I / 4) * exp (-((ε : ℂ) * Real.log 2 / 2)) / 2) *
              exp (-(airyZetaComplex z * I)) +
            (exp (-(π * I / 4)) * exp ((ε : ℂ) * Real.log 2 / 2) / 2) *
              exp (airyZetaComplex z * I)) * airyOscSum false 0 N z +
          I * ((exp (π * I / 4) * exp (-((ε : ℂ) * Real.log 2 / 2)) / 2) *
              exp (-(airyZetaComplex z * I)) -
            (exp (-(π * I / 4)) * exp ((ε : ℂ) * Real.log 2 / 2) / 2) *
              exp (airyZetaComplex z * I)) * airyOscSum false 1 M z) := by
  simp only [airyRotatedBiApprox, Bool.false_eq_true, ite_false, Complex.cos, Complex.sin]
  have e1 : exp ((airyZetaComplex z - π / 4 - ε * I * Real.log 2 / 2) * I) =
      exp (-(π * I / 4)) * exp ((ε : ℂ) * Real.log 2 / 2) * exp (airyZetaComplex z * I) := by
    rw [← exp_add, ← exp_add]; congr 1
    linear_combination (-(ε : ℂ) * Real.log 2 / 2) * I_sq
  have e2 : exp (-(airyZetaComplex z - π / 4 - ε * I * Real.log 2 / 2) * I) =
      exp (π * I / 4) * exp (-((ε : ℂ) * Real.log 2 / 2)) * exp (-(airyZetaComplex z * I)) := by
    rw [← exp_add, ← exp_add]; congr 1
    linear_combination ((ε : ℂ) * Real.log 2 / 2) * I_sq
  rw [e1, e2]
  ring

/-- The expansion of `Bi(z e^{±πi/3})` in `|arg z| ≤ 2π/3 - δ` by the rotated oscillatory
series `airyRotatedBiApprox` (DLMF 9.7.13). -/
@[dlmf 9.7.E13]
theorem airyBi_rotated_expansion {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 2 * π / 3) {ε : ℝ}
    (hε : ε = 1 ∨ ε = -1) (N M : ℕ) :
    IsBigO (airySector (2 * π / 3 - δ))
      (fun z => airyBi (z * exp (ε * (π * I / 3))) -
        airyRotatedBiApprox false ε N M z) (airyOscError .bi N M) := by
  obtain ⟨hE', hO'⟩ := airyRot_ai_parts hδ hδ' N M
  refine (airyRot_osc_bound (X := fun z => airyBi (z * exp (ε * (π * I / 3))))
    (Y := airyRotatedBiApprox false ε N M)
    (pref := fun z => (2 / π : ℂ) ^ (1 / 2 : ℂ) * exp (ε * (π * I / 6)) * z ^ (-1 / 4 : ℂ))
    (exp (π * I / 4) * exp (-((ε : ℂ) * Real.log 2 / 2)) / 2)
    (exp (-(π * I / 4)) * exp ((ε : ℂ) * Real.log 2 / 2) / 2) hE' hO' ?_ ?_).trans
    (airyRot_envelope .bi _ N M (airyRot_norm_rot_pref ε))
  · filter_upwards [airyRot_eventually_arg (2 * π / 3 - δ)] with z hz
    exact airyRot_bi_rot_eq hz.1 (hz.2.trans_lt (by linarith)) hε
  · exact Eventually.of_forall (airyRot_bi_approx_eq ε N M)

/-- Chain rule for `z ↦ f (z c)`: the derivative is `c f'(z c)`. -/
theorem airyRot_hasDerivAt_comp_mul {f f' : ℂ → ℂ} (hf : ∀ z, HasDerivAt f (f' z) z) (c z : ℂ) :
    HasDerivAt (fun z => f (z * c)) (c * f' (z * c)) z := by
  have := (hf (z * c)).comp z ((hasDerivAt_id' z).mul_const c)
  rw [show c * f' (z * c) = f' (z * c) * (1 * c) by ring]
  exact this

/-- `Bi'(z e^{iπ/3}) = i Ai'(z e^{iπ/3}) - 2 e^{iπ/6} Ai'(z e^{-iπ/3})`. -/
theorem airyRot_airyBiDeriv_rot_pos (z : ℂ) :
    airyBiDeriv (z * exp (π * I / 3)) = I * airyAiDeriv (z * exp ((π / 3 : ℝ) * I)) +
      -2 * exp (π * I / 6) * airyAiDeriv (z * exp ((-(π / 3) : ℝ) * I)) := by
  have h := airyRot_deriv_of_eq (airyRot_hasDerivAt_comp_mul hasDerivAt_airyBi (exp (π * I / 3)))
    hasDerivAt_airyAi _ _ _ _ airyRot_airyBi_rot_pos z
  obtain ⟨u4, um4, -, -, u2, um2, u12⟩ := airyRot_u_powers
  obtain ⟨k1, k2⟩ := airyRot_exp_third_ofReal
  have hu6 := airyRot_u_six
  rw [k1, k2] at h ⊢
  simp only [u4, um4, u2, um2] at h ⊢
  set u := exp (π * I / 12)
  set A := airyAiDeriv (z * u ^ 4)
  set B := airyAiDeriv (z * (u ^ 4)⁻¹)
  set X := airyBiDeriv (z * u ^ 4)
  have hu0 : u ≠ 0 := exp_ne_zero _
  apply mul_left_cancel₀ (pow_ne_zero 4 hu0)
  rw [h, ← hu6]
  field_simp
  linear_combination 2 * B * u12

/-- `Bi'(z e^{-iπ/3}) = -2 e^{-iπ/6} Ai'(z e^{iπ/3}) - i Ai'(z e^{-iπ/3})`. -/
theorem airyRot_airyBiDeriv_rot_neg (z : ℂ) :
    airyBiDeriv (z * exp (-(π * I / 3))) = -2 * exp (-π * I / 6) *
      airyAiDeriv (z * exp ((π / 3 : ℝ) * I)) + -I * airyAiDeriv (z * exp ((-(π / 3) : ℝ) * I)) := by
  have hc : ∀ z, airyBi (z * exp (-(π * I / 3))) = 2 * exp (π * I / 6) *
      airyAi (z * exp ((π / 3 : ℝ) * I)) + -I * airyAi (z * exp ((-(π / 3) : ℝ) * I)) := fun z => by
    rw [airyRot_airyBi_rot_neg]; ring
  have h := airyRot_deriv_of_eq
    (airyRot_hasDerivAt_comp_mul hasDerivAt_airyBi (exp (-(π * I / 3))))
    hasDerivAt_airyAi _ _ _ _ hc z
  obtain ⟨u4, um4, -, -, u2, um2, u12⟩ := airyRot_u_powers
  obtain ⟨k1, k2⟩ := airyRot_exp_third_ofReal
  have hu6 := airyRot_u_six
  have k3 : exp (-(π * I / 3)) = exp (-π * I / 3) := by congr 1; ring
  rw [k1, k2, k3] at h ⊢
  simp only [u4, um4, u2, um2] at h ⊢
  set u := exp (π * I / 12)
  set A := airyAiDeriv (z * u ^ 4)
  set B := airyAiDeriv (z * (u ^ 4)⁻¹)
  set X := airyBiDeriv (z * (u ^ 4)⁻¹)
  have hu0 : u ≠ 0 := exp_ne_zero _
  apply mul_left_cancel₀ (inv_ne_zero (pow_ne_zero 4 hu0))
  rw [h, ← hu6]
  field_simp
  linear_combination 2 * A * u12

/-- At `z` with `|arg z| < 2π/3`, `Bi'(z e^{±iπ/3})` is the rotated prefactor times the
cosine/sine combination of the even and odd parts of the normalized `Ai'` (via 9.2.11). -/
private lemma airyRot_biDeriv_rot_eq {z : ℂ} (hz0 : z ≠ 0) (hz3 : |arg z| < 2 * π / 3) {ε : ℝ}
    (hε : ε = 1 ∨ ε = -1) :
    airyBiDeriv (z * exp (ε * (π * I / 3))) =
      (2 / π : ℂ) ^ (1 / 2 : ℂ) * exp (-ε * (π * I / 6)) * z ^ (1 / 4 : ℂ) *
        (((exp (-(π * I / 4)) * exp (-((ε : ℂ) * Real.log 2 / 2)) / 2) *
              exp (-(airyZetaComplex z * I)) +
            (exp (π * I / 4) * exp ((ε : ℂ) * Real.log 2 / 2) / 2) *
              exp (airyZetaComplex z * I)) *
            airyRot_even (fun w => airyAiDeriv w / airyPrefactor .aiDeriv w) z +
          I * ((exp (-(π * I / 4)) * exp (-((ε : ℂ) * Real.log 2 / 2)) / 2) *
              exp (-(airyZetaComplex z * I)) -
            (exp (π * I / 4) * exp ((ε : ℂ) * Real.log 2 / 2) / 2) *
              exp (airyZetaComplex z * I)) *
            airyRot_odd (fun w => airyAiDeriv w / airyPrefactor .aiDeriv w) z) := by
  obtain ⟨u4, um4, u3, um3, u2, um2, u12⟩ := airyRot_u_powers
  have hu6 := airyRot_u_six
  have hs : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
    rw [← ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have hs0 : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (by positivity)
  have hπs : (Real.sqrt π : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hl : exp (-((Real.log 2 : ℂ) / 2)) = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ := by
    rw [exp_neg, airyRot_exp_half_log_two]
  obtain ⟨d1, d2, d3, d4⟩ := airyRot_third_data hz0 hz3
  have hq : z ^ (1 / 4 : ℂ) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hz0)
  have hp1 := airyRot_prefactor_ne_zero .aiDeriv
    (mul_ne_zero hz0 (exp_ne_zero ((π / 3 : ℝ) * I)))
  have hp2 := airyRot_prefactor_ne_zero .aiDeriv
    (mul_ne_zero hz0 (exp_ne_zero ((-(π / 3) : ℝ) * I)))
  have split1 : airyAiDeriv (z * exp ((π / 3 : ℝ) * I)) =
      airyPrefactor .aiDeriv (z * exp ((π / 3 : ℝ) * I)) *
      (airyAiDeriv (z * exp ((π / 3 : ℝ) * I)) /
        airyPrefactor .aiDeriv (z * exp ((π / 3 : ℝ) * I))) := by
    field_simp
  have split2 : airyAiDeriv (z * exp ((-(π / 3) : ℝ) * I)) =
      airyPrefactor .aiDeriv (z * exp ((-(π / 3) : ℝ) * I)) *
      (airyAiDeriv (z * exp ((-(π / 3) : ℝ) * I)) /
        airyPrefactor .aiDeriv (z * exp ((-(π / 3) : ℝ) * I))) := by field_simp
  rcases hε with rfl | rfl
  · simp only [ofReal_one, one_mul, neg_one_mul]
    rw [airyRot_airyBiDeriv_rot_pos z, split1, split2, ← mul_assoc, ← mul_assoc,
      airyRot_decomp (fun w => airyAiDeriv w / airyPrefactor .aiDeriv w)]
    have ep : I * airyPrefactor .aiDeriv (z * exp ((π / 3 : ℝ) * I)) =
        (2 / π : ℂ) ^ (1 / 2 : ℂ) * exp (-(π * I / 6)) * z ^ (1 / 4 : ℂ) *
          (exp (-(π * I / 4)) * exp (-((Real.log 2 : ℂ) / 2)) / 2 *
            exp (-(airyZetaComplex z * I))) := by
      simp only [airyPrefactor]
      rw [d1, d3, airyRot_two_div_pi_cpow, hl, show -(π * I / 6) = -π * I / 6 by ring,
        um2, um3]
      set u := exp (π * I / 12)
      have hu0 : u ≠ 0 := exp_ne_zero _
      rw [← hu6]
      field_simp
      linear_combination -u12
    have em : -2 * exp (π * I / 6) * airyPrefactor .aiDeriv (z * exp ((-(π / 3) : ℝ) * I)) =
        (2 / π : ℂ) ^ (1 / 2 : ℂ) * exp (-(π * I / 6)) * z ^ (1 / 4 : ℂ) *
          (exp (π * I / 4) * exp ((Real.log 2 : ℂ) / 2) / 2 * exp (airyZetaComplex z * I)) := by
      simp only [airyPrefactor]
      rw [d2, d4, airyRot_two_div_pi_cpow, airyRot_exp_half_log_two,
        show -(π * I / 6) = -π * I / 6 by ring, u2, um2, u3, neg_neg]
      set u := exp (π * I / 12)
      have hu0 : u ≠ 0 := exp_ne_zero _
      field_simp
      linear_combination -hs
    rw [ep, em]
    ring_nf
  · simp only [ofReal_neg, ofReal_one, neg_one_mul, neg_neg, one_mul]
    rw [airyRot_airyBiDeriv_rot_neg z, split1, split2, ← mul_assoc,
      ← mul_assoc, airyRot_decomp (fun w => airyAiDeriv w / airyPrefactor .aiDeriv w)]
    have ep : -2 * exp (-π * I / 6) * airyPrefactor .aiDeriv (z * exp ((π / 3 : ℝ) * I)) =
        (2 / π : ℂ) ^ (1 / 2 : ℂ) * exp (π * I / 6) * z ^ (1 / 4 : ℂ) *
          (exp (-(π * I / 4)) * exp ((Real.log 2 : ℂ) / 2) / 2 *
            exp (-(airyZetaComplex z * I))) := by
      simp only [airyPrefactor]
      rw [d1, d3, airyRot_two_div_pi_cpow, airyRot_exp_half_log_two, u2, um2, um3]
      set u := exp (π * I / 12)
      have hu0 : u ≠ 0 := exp_ne_zero _
      field_simp
      linear_combination -hs
    have em : -I * airyPrefactor .aiDeriv (z * exp ((-(π / 3) : ℝ) * I)) =
        (2 / π : ℂ) ^ (1 / 2 : ℂ) * exp (π * I / 6) * z ^ (1 / 4 : ℂ) *
          (exp (π * I / 4) * exp (-((Real.log 2 : ℂ) / 2)) / 2 *
            exp (airyZetaComplex z * I)) := by
      simp only [airyPrefactor]
      rw [d2, d4, airyRot_two_div_pi_cpow, hl, u3, u2, neg_neg]
      set u := exp (π * I / 12)
      have hu0 : u ≠ 0 := exp_ne_zero _
      rw [← hu6]
      field_simp
    rw [ep, em]
    ring_nf

/-- `airyRotatedBiApprox true ε N M z` in the cosine/sine form used by `airyRot_osc_bound`. -/
private lemma airyRot_biDeriv_approx_eq (ε : ℝ) (N M : ℕ) (z : ℂ) :
    airyRotatedBiApprox true ε N M z =
      (2 / π : ℂ) ^ (1 / 2 : ℂ) * exp (-ε * (π * I / 6)) * z ^ (1 / 4 : ℂ) *
        (((exp (-(π * I / 4)) * exp (-((ε : ℂ) * Real.log 2 / 2)) / 2) *
              exp (-(airyZetaComplex z * I)) +
            (exp (π * I / 4) * exp ((ε : ℂ) * Real.log 2 / 2) / 2) *
              exp (airyZetaComplex z * I)) * airyOscSum true 0 N z +
          I * ((exp (-(π * I / 4)) * exp (-((ε : ℂ) * Real.log 2 / 2)) / 2) *
              exp (-(airyZetaComplex z * I)) -
            (exp (π * I / 4) * exp ((ε : ℂ) * Real.log 2 / 2) / 2) *
              exp (airyZetaComplex z * I)) * airyOscSum true 1 M z) := by
  simp only [airyRotatedBiApprox, ↓reduceIte]
  rw [show cos (airyZetaComplex z - π / 4 - ε * I * Real.log 2 / 2) =
        sin (airyZetaComplex z - π / 4 - ε * I * Real.log 2 / 2 + π / 2) from
      (Complex.sin_add_pi_div_two _).symm,
    show sin (airyZetaComplex z - π / 4 - ε * I * Real.log 2 / 2) =
        -cos (airyZetaComplex z - π / 4 - ε * I * Real.log 2 / 2 + π / 2) by
      rw [Complex.cos_add_pi_div_two]; ring]
  simp only [Complex.cos, Complex.sin]
  have e1 : exp ((airyZetaComplex z - π / 4 - ε * I * Real.log 2 / 2 + π / 2) * I) =
      exp (π * I / 4) * exp ((ε : ℂ) * Real.log 2 / 2) * exp (airyZetaComplex z * I) := by
    rw [← exp_add, ← exp_add]; congr 1
    linear_combination (-(ε : ℂ) * Real.log 2 / 2) * I_sq
  have e2 : exp (-(airyZetaComplex z - π / 4 - ε * I * Real.log 2 / 2 + π / 2) * I) =
      exp (-(π * I / 4)) * exp (-((ε : ℂ) * Real.log 2 / 2)) *
        exp (-(airyZetaComplex z * I)) := by
    rw [← exp_add, ← exp_add]; congr 1
    linear_combination ((ε : ℂ) * Real.log 2 / 2) * I_sq
  rw [e1, e2]
  ring

/-- The expansion of `Bi'(z e^{±πi/3})` in `|arg z| ≤ 2π/3 - δ` by the rotated oscillatory
series `airyRotatedBiApprox` (DLMF 9.7.14). -/
@[dlmf 9.7.E14]
theorem airyBiDeriv_rotated_expansion {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 2 * π / 3) {ε : ℝ}
    (hε : ε = 1 ∨ ε = -1) (N M : ℕ) :
    IsBigO (airySector (2 * π / 3 - δ))
      (fun z => airyBiDeriv (z * exp (ε * (π * I / 3))) -
        airyRotatedBiApprox true ε N M z) (airyOscError .biDeriv N M) := by
  obtain ⟨hE', hO'⟩ := airyRot_aiDeriv_parts hδ hδ' N M
  refine (airyRot_osc_bound (X := fun z => airyBiDeriv (z * exp (ε * (π * I / 3))))
    (Y := airyRotatedBiApprox true ε N M)
    (pref := fun z => (2 / π : ℂ) ^ (1 / 2 : ℂ) * exp (-ε * (π * I / 6)) * z ^ (1 / 4 : ℂ))
    (exp (-(π * I / 4)) * exp (-((ε : ℂ) * Real.log 2 / 2)) / 2)
    (exp (π * I / 4) * exp ((ε : ℂ) * Real.log 2 / 2) / 2) hE' hO' ?_ ?_).trans
    (airyRot_envelope .biDeriv _ N M (airyRot_norm_rot_pref' ε))
  · filter_upwards [airyRot_eventually_arg (2 * π / 3 - δ)] with z hz
    exact airyRot_biDeriv_rot_eq hz.1 (hz.2.trans_lt (by linarith)) hε
  · exact Eventually.of_forall (airyRot_biDeriv_approx_eq ε N M)

/-- Eventually in `airySector α`, the Airy prefactor is nonzero. -/
theorem airyRot_eventually_prefactor_ne_zero (kind : AiryKind) (α : ℝ) :
    ∀ᶠ z in airySector α, airyPrefactor kind z ≠ 0 :=
  (airyRot_eventually_ne_zero α).mono fun _ hz => airyRot_prefactor_ne_zero kind hz

/-- `Ai(z) = e^{-ζ}/(2√π z^{1/4}) (∑_{k<N} (-1)^k u_k ζ^{-k} + O(ζ^{-N}))` in
`|arg z| ≤ π - δ` (DLMF 9.7.5). -/
@[dlmf 9.7.E5]
theorem airy_ai_poincare {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < π) (N : ℕ) :
    IsBigO (airySector (π - δ)) (fun z => airyFunction .ai z -
      airyPrefactor .ai z * airyExponentialSum .ai N z)
      (fun z => airyPrefactor .ai z / airyZetaComplex z ^ N) :=
  airyRot_isBigO_of_expansion (airyRot_airyAi_expansion hδ hδ')
    (airyRot_eventually_prefactor_ne_zero .ai _) N

/-- `Ai'(z) = -z^{1/4} e^{-ζ}/(2√π) (∑_{k<N} (-1)^k v_k ζ^{-k} + O(ζ^{-N}))` in
`|arg z| ≤ π - δ` (DLMF 9.7.6). -/
@[dlmf 9.7.E6]
theorem airy_aiDeriv_poincare {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < π) (N : ℕ) :
    IsBigO (airySector (π - δ)) (fun z => airyFunction .aiDeriv z -
      airyPrefactor .aiDeriv z * airyExponentialSum .aiDeriv N z)
      (fun z => airyPrefactor .aiDeriv z / airyZetaComplex z ^ N) :=
  airyRot_isBigO_of_expansion (airyRot_airyAiDeriv_expansion hδ hδ')
    (airyRot_eventually_prefactor_ne_zero .aiDeriv _) N

/-- `Bi(z) = e^{ζ}/(√π z^{1/4}) (∑_{k<N} u_k ζ^{-k} + O(ζ^{-N}))` in `|arg z| ≤ π/3 - δ`
(DLMF 9.7.7). -/
@[dlmf 9.7.E7]
theorem airy_bi_poincare {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < π / 3) (N : ℕ) :
    IsBigO (airySector (π / 3 - δ)) (fun z => airyFunction .bi z -
      airyPrefactor .bi z * airyExponentialSum .bi N z)
      (fun z => airyPrefactor .bi z / airyZetaComplex z ^ N) :=
  airyRot_isBigO_of_expansion (airyRot_airyBi_expansion hδ hδ')
    (airyRot_eventually_prefactor_ne_zero .bi _) N

/-- `Bi'(z) = z^{1/4} e^{ζ}/√π (∑_{k<N} v_k ζ^{-k} + O(ζ^{-N}))` in `|arg z| ≤ π/3 - δ`
(DLMF 9.7.8). -/
@[dlmf 9.7.E8]
theorem airy_biDeriv_poincare {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < π / 3) (N : ℕ) :
    IsBigO (airySector (π / 3 - δ)) (fun z => airyFunction .biDeriv z -
      airyPrefactor .biDeriv z * airyExponentialSum .biDeriv N z)
      (fun z => airyPrefactor .biDeriv z / airyZetaComplex z ^ N) :=
  airyRot_isBigO_of_expansion (airyRot_airyBiDeriv_expansion hδ hδ')
    (airyRot_eventually_prefactor_ne_zero .biDeriv _) N

/-! ### Real-axis error bounds (DLMF §9.7(iii), 9.7.15)

On the positive axis the normalized `Ai` and `Ai'` are Laplace integrals
`(2ζ)^a Γ(a)⁻¹ ∫₀^∞ e^{-2ζr} r^{a-1} (1+r)^β dr` with `(a, β) = (5/6, -1/6)`, `(7/6, 1/6)`.
The binomial remainder of `(1+r)^β` after `N ≥ β` terms lies between `0` and the first
neglected term, which gives the classical enveloping property of the expansions.
-/

/-! ### Binomial remainders -/

/-- The remainder of the binomial series of `(1 + t)^β` after `N` terms. -/
def airyReal_rho (β : ℝ) (N : ℕ) (t : ℝ) : ℝ :=
  (1 + t) ^ β - ∑ n ∈ Finset.range N, Ring.choose β n * t ^ n

/-- `(m + 1) binom(β, m + 1) = β binom(β - 1, m)`. -/
theorem airyReal_choose_succ (β : ℝ) (m : ℕ) :
    ((m : ℝ) + 1) * Ring.choose β (m + 1) = β * Ring.choose (β - 1) m := by
  have h := Ring.choose_smul_choose β (n := m + 1) (k := 1) (by omega)
  simp only [Nat.choose_one_right, Ring.choose_one_right, Nat.cast_one, Nat.add_sub_cancel,
    nsmul_eq_mul] at h
  rw [← h]; push_cast; ring

/-- The derivative of the binomial remainder `ρ_{β,N+1}` is `β ρ_{β-1,N}` on `t > -1`. -/
theorem airyReal_hasDerivAt_rho (β : ℝ) (N : ℕ) {t : ℝ} (ht : -1 < t) :
    HasDerivAt (airyReal_rho β (N + 1)) (β * airyReal_rho (β - 1) N t) t := by
  have hfun : airyReal_rho β (N + 1) = fun t => (1 + t) ^ β -
      (∑ m ∈ Finset.range N, Ring.choose β (m + 1) * t ^ (m + 1) + Ring.choose β 0) := by
    funext t; rw [airyReal_rho, Finset.sum_range_succ', pow_zero, mul_one]
  rw [hfun]
  have h1 : HasDerivAt (fun t : ℝ => (1 + t) ^ β) (1 * β * (1 + t) ^ (β - 1)) t :=
    ((hasDerivAt_id t).const_add 1).rpow_const (Or.inl (by simp; linarith))
  have h2 : HasDerivAt (fun t : ℝ => ∑ m ∈ Finset.range N, Ring.choose β (m + 1) * t ^ (m + 1))
      (∑ m ∈ Finset.range N, Ring.choose β (m + 1) * (((m + 1 : ℕ) : ℝ) * t ^ m)) t := by
    have := HasDerivAt.fun_sum (u := Finset.range N)
      (A := fun m (t : ℝ) => Ring.choose β (m + 1) * t ^ (m + 1))
      (A' := fun m => Ring.choose β (m + 1) * (((m + 1 : ℕ) : ℝ) * t ^ m)) (x := t)
      (fun m _ => by
        have := (hasDerivAt_pow (m + 1) t).const_mul (Ring.choose β (m + 1))
        simpa using this)
    simpa using this
  refine (h1.fun_sub (h2.add_const _)).congr_deriv ?_
  rw [airyReal_rho, mul_sub, Finset.mul_sum]
  congr 1
  · ring
  · refine Finset.sum_congr rfl fun m _ => ?_
    have := airyReal_choose_succ β m
    push_cast
    linear_combination t ^ m * this

/-- A function vanishing at `0` with nonnegative derivative on `[0, ∞)` is nonnegative there. -/
theorem airyReal_nonneg_of_deriv {φ g : ℝ → ℝ} (hφ : ∀ t, 0 ≤ t → HasDerivAt φ (g t) t)
    (h0 : φ 0 = 0) (hg : ∀ t, 0 ≤ t → 0 ≤ g t) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ φ t := by
  have hmono : MonotoneOn φ (Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun x hx => (hφ x hx).continuousAt.continuousWithinAt)
      (fun x hx => by
        rw [interior_Ici] at hx
        exact (hφ x (le_of_lt hx)).differentiableAt.differentiableWithinAt) fun x hx => ?_
    rw [interior_Ici] at hx
    rw [(hφ x (le_of_lt hx)).deriv]
    exact hg x (le_of_lt hx)
  have := hmono (mem_Ici.mpr (le_refl (0 : ℝ))) (mem_Ici.mpr ht) ht
  rwa [h0] at this

/-- **Binomial remainder bound**: for `β ≤ N` and `t ≥ 0` the remainder lies between `0` and
the first neglected term `binom(β, N) t^N`. -/
theorem airyReal_rho_btw (N : ℕ) : ∀ β : ℝ, β ≤ N → ∀ t : ℝ, 0 ≤ t →
    0 ≤ airyReal_rho β N t * (Ring.choose β N * t ^ N - airyReal_rho β N t) := by
  induction N with
  | zero =>
    intro β hβ t ht
    simp only [airyReal_rho, Finset.range_zero, Finset.sum_empty, sub_zero, Ring.choose_zero_right,
      pow_zero, one_mul]
    have h1 : 0 ≤ (1 + t) ^ β := Real.rpow_nonneg (by linarith) _
    have h2 : (1 + t) ^ β ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by simpa using hβ)
    nlinarith
  | succ N ih =>
    intro β hβ t ht
    have hih : ∀ s, 0 ≤ s → 0 ≤ (β * airyReal_rho (β - 1) N s) *
        (β * Ring.choose (β - 1) N * s ^ N - β * airyReal_rho (β - 1) N s) := by
      intro s hs
      have := ih (β - 1) (by push_cast at hβ; linarith) s hs
      nlinarith [sq_nonneg β]
    have hd : ∀ s, 0 ≤ s → HasDerivAt (airyReal_rho β (N + 1)) (β * airyReal_rho (β - 1) N s) s :=
      fun s hs => airyReal_hasDerivAt_rho β N (by linarith)
    have hB : ∀ s : ℝ, HasDerivAt (fun s => Ring.choose β (N + 1) * s ^ (N + 1))
        (β * Ring.choose (β - 1) N * s ^ N) s := fun s => by
      have := (hasDerivAt_pow (N + 1) s).const_mul (Ring.choose β (N + 1))
      refine this.congr_deriv ?_
      have := airyReal_choose_succ β N
      push_cast
      linear_combination s ^ N * this
    have h00 : airyReal_rho β (N + 1) 0 = 0 := by
      simp [airyReal_rho, Finset.sum_range_succ']
    set c := Ring.choose β (N + 1)
    rcases le_total 0 c with hc | hc
    · have hcN : ∀ s, 0 ≤ s → 0 ≤ β * Ring.choose (β - 1) N * s ^ N := fun s hs => by
        rw [← airyReal_choose_succ]; positivity
      have hg : ∀ s, 0 ≤ s → 0 ≤ β * airyReal_rho (β - 1) N s ∧
          β * airyReal_rho (β - 1) N s ≤ β * Ring.choose (β - 1) N * s ^ N := fun s hs => by
        have h1 := hih s hs; have h2 := hcN s hs
        constructor <;> nlinarith
      have p1 := airyReal_nonneg_of_deriv hd h00 (fun s hs => (hg s hs).1) ht
      have p2 := airyReal_nonneg_of_deriv (φ := fun s => c * s ^ (N + 1) - airyReal_rho β (N + 1) s)
        (fun s hs => (hB s).sub (hd s hs)) (by simp [h00]) (fun s hs => by
          have := (hg s hs).2; linarith) ht
      exact mul_nonneg p1 p2
    · have hcN : ∀ s, 0 ≤ s → β * Ring.choose (β - 1) N * s ^ N ≤ 0 := fun s hs => by
        rw [← airyReal_choose_succ, mul_assoc]
        exact mul_nonpos_of_nonneg_of_nonpos (by positivity)
          (mul_nonpos_of_nonpos_of_nonneg hc (by positivity))
      have hg : ∀ s, 0 ≤ s → β * airyReal_rho (β - 1) N s ≤ 0 ∧
          β * Ring.choose (β - 1) N * s ^ N ≤ β * airyReal_rho (β - 1) N s := fun s hs => by
        have h1 := hih s hs; have h2 := hcN s hs
        constructor <;> nlinarith
      have p1 := airyReal_nonneg_of_deriv (φ := fun s => -airyReal_rho β (N + 1) s)
        (fun s hs => (hd s hs).neg) (by simp [h00]) (fun s hs => by
          have := (hg s hs).1; linarith) ht
      have p2 := airyReal_nonneg_of_deriv (φ := fun s => airyReal_rho β (N + 1) s - c * s ^ (N + 1))
        (fun s hs => (hd s hs).sub (hB s)) (by simp [h00]) (fun s hs => by
          have := (hg s hs).2; linarith) ht
      have := mul_nonneg p1 p2
      linarith

/-- The moments `∫₀^∞ e^{-sr} r^{a-1} r^n dr = Γ(a+n) s^{-(a+n)}`. -/
theorem airyReal_moment {a s : ℝ} (ha : 0 < a) (hs : 0 < s) (n : ℕ) :
    IntegrableOn (fun r : ℝ => Real.exp (-(s * r)) * r ^ (a - 1) * r ^ n) (Ioi 0) ∧
    ∫ r in Ioi (0 : ℝ), Real.exp (-(s * r)) * r ^ (a - 1) * r ^ n =
      Real.Gamma (a + n) * s ^ (-(a + n)) := by
  have heq : EqOn (fun r : ℝ => Real.exp (-(s * r)) * r ^ (a - 1) * r ^ n)
      (fun r : ℝ => r ^ (a - 1 + n) * Real.exp (-s * r ^ (1 : ℝ))) (Ioi 0) := by
    intro r hr
    simp only [Real.rpow_one]
    rw [Real.rpow_add hr, Real.rpow_natCast]; ring_nf
  have hq : -1 < a - 1 + n := by have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith
  refine ⟨(integrableOn_rpow_mul_exp_neg_mul_rpow hq one_pos hs).congr_fun heq.symm
    measurableSet_Ioi, ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioi heq,
    _root_.integral_rpow_mul_exp_neg_mul_rpow one_pos hq hs]
  rw [show (a - 1 + n + 1) / 1 = a + n by ring, show -(a - 1 + n + 1) / 1 = -(a + n) by ring]
  ring

/-- If `p` lies between `0` and `q` (`p (q - p) ≥ 0`) then `|p| ≤ |q|`. -/
theorem airyReal_sq_le_of_btw {p q : ℝ} (h : 0 ≤ p * (q - p)) : |p| ≤ |q| :=
  sq_le_sq.mp (by nlinarith [sq_nonneg (q - p)])

/-- **Integrated binomial remainder**: the Laplace transform of the remainder lies between `0`
and that of the first neglected term. -/
theorem airyReal_integral_btw {a s β : ℝ} (ha : 0 < a) (hs : 0 < s) {N : ℕ} (hβ : β ≤ N) :
    IntegrableOn (fun r : ℝ => Real.exp (-(s * r)) * r ^ (a - 1) * airyReal_rho β N r) (Ioi 0) ∧
    0 ≤ (∫ r in Ioi (0 : ℝ), Real.exp (-(s * r)) * r ^ (a - 1) * airyReal_rho β N r) *
      (Ring.choose β N * (Real.Gamma (a + N) * s ^ (-(a + N))) -
        ∫ r in Ioi (0 : ℝ), Real.exp (-(s * r)) * r ^ (a - 1) * airyReal_rho β N r) := by
  obtain ⟨hmi, hmv⟩ := airyReal_moment ha hs N
  set c := Ring.choose β N
  have hw : ∀ r : ℝ, 0 < r → 0 ≤ Real.exp (-(s * r)) * r ^ (a - 1) := fun r hr =>
    mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hr.le _)
  have hb : ∀ r : ℝ, 0 < r → 0 ≤ airyReal_rho β N r * (c * r ^ N - airyReal_rho β N r) :=
    fun r hr => airyReal_rho_btw N β hβ r hr.le
  have hmeas : AEStronglyMeasurable
      (fun r : ℝ => Real.exp (-(s * r)) * r ^ (a - 1) * airyReal_rho β N r)
      (volume.restrict (Ioi 0)) := by
    refine Measurable.aestronglyMeasurable ?_
    unfold airyReal_rho
    fun_prop
  have hint : IntegrableOn (fun r : ℝ => Real.exp (-(s * r)) * r ^ (a - 1) * airyReal_rho β N r)
      (Ioi 0) := by
    refine Integrable.mono' (hmi.const_mul |c|) hmeas ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun r hr => ?_)
    have h1 := airyReal_sq_le_of_btw (hb r hr)
    have h2 := hw r hr
    rw [abs_mul, abs_of_nonneg (pow_nonneg (le_of_lt (mem_Ioi.mp hr)) N)] at h1
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h2]
    calc Real.exp (-(s * r)) * r ^ (a - 1) * |airyReal_rho β N r|
        ≤ Real.exp (-(s * r)) * r ^ (a - 1) * (|c| * r ^ N) := by
          gcongr
      _ = |c| * (Real.exp (-(s * r)) * r ^ (a - 1) * r ^ N) := by ring
  refine ⟨hint, ?_⟩
  have hM : ∫ r in Ioi (0 : ℝ), Real.exp (-(s * r)) * r ^ (a - 1) * (c * r ^ N) =
      c * (Real.Gamma (a + N) * s ^ (-(a + N))) := by
    rw [← hmv, ← integral_const_mul]
    congr 1; funext r; ring
  rw [← hM]
  have hMi : IntegrableOn (fun r : ℝ => Real.exp (-(s * r)) * r ^ (a - 1) * (c * r ^ N)) (Ioi 0) :=
    IntegrableOn.congr_fun (hmi.const_mul c) (fun r _ => by ring) measurableSet_Ioi
  rcases le_total 0 c with hc | hc
  · have hlo : ∀ r ∈ Ioi (0 : ℝ), 0 ≤ Real.exp (-(s * r)) * r ^ (a - 1) * airyReal_rho β N r :=
      fun r hr => by
        have := hb r hr; have := hw r hr
        have hcr : 0 ≤ c * r ^ N := mul_nonneg hc (pow_nonneg (le_of_lt (mem_Ioi.mp hr)) N)
        have : 0 ≤ airyReal_rho β N r := by nlinarith
        positivity
    have hhi : ∀ r ∈ Ioi (0 : ℝ), Real.exp (-(s * r)) * r ^ (a - 1) * airyReal_rho β N r ≤
        Real.exp (-(s * r)) * r ^ (a - 1) * (c * r ^ N) := fun r hr => by
      have := hb r hr; have h2 := hw r hr
      have hcr : 0 ≤ c * r ^ N := mul_nonneg hc (pow_nonneg (le_of_lt (mem_Ioi.mp hr)) N)
      have : airyReal_rho β N r ≤ c * r ^ N := by nlinarith
      exact mul_le_mul_of_nonneg_left this h2
    have h1 := setIntegral_nonneg (μ := volume) measurableSet_Ioi hlo
    have h2 := setIntegral_mono_on hint hMi measurableSet_Ioi hhi
    exact mul_nonneg h1 (by linarith)
  · have hlo : ∀ r ∈ Ioi (0 : ℝ), Real.exp (-(s * r)) * r ^ (a - 1) * airyReal_rho β N r ≤ 0 :=
      fun r hr => by
        have := hb r hr; have h2 := hw r hr
        have hcr : c * r ^ N ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg hc (pow_nonneg (le_of_lt (mem_Ioi.mp hr)) N)
        have : airyReal_rho β N r ≤ 0 := by nlinarith
        exact mul_nonpos_of_nonneg_of_nonpos h2 this
    have hhi : ∀ r ∈ Ioi (0 : ℝ), Real.exp (-(s * r)) * r ^ (a - 1) * (c * r ^ N) ≤
        Real.exp (-(s * r)) * r ^ (a - 1) * airyReal_rho β N r := fun r hr => by
      have := hb r hr; have h2 := hw r hr
      have hcr : c * r ^ N ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hc (pow_nonneg (le_of_lt (mem_Ioi.mp hr)) N)
      have : c * r ^ N ≤ airyReal_rho β N r := by nlinarith
      exact mul_le_mul_of_nonneg_left this h2
    have h1 := setIntegral_nonpos (μ := volume) measurableSet_Ioi hlo
    have h2 := setIntegral_mono_on hMi hint measurableSet_Ioi hhi
    exact mul_nonneg_of_nonpos_of_nonpos h1 (by linarith)

/-- The Laplace integral of the full kernel splits into the remainder and the moments. -/
theorem airyReal_split {a s β : ℝ} (ha : 0 < a) (hs : 0 < s) (N : ℕ) (hβ : β ≤ N) :
    ∫ r in Ioi (0 : ℝ), Real.exp (-(s * r)) * (r ^ (a - 1) * (1 + r) ^ β) =
      (∫ r in Ioi (0 : ℝ), Real.exp (-(s * r)) * r ^ (a - 1) * airyReal_rho β N r) +
      ∑ n ∈ Finset.range N, Ring.choose β n * (Real.Gamma (a + n) * s ^ (-(a + n))) := by
  have hint := (airyReal_integral_btw ha hs hβ).1
  have heq : ∀ r : ℝ, Real.exp (-(s * r)) * (r ^ (a - 1) * (1 + r) ^ β) =
      Real.exp (-(s * r)) * r ^ (a - 1) * airyReal_rho β N r +
        ∑ n ∈ Finset.range N, Ring.choose β n * (Real.exp (-(s * r)) * r ^ (a - 1) * r ^ n) := by
    intro r
    simp only [airyReal_rho]
    rw [mul_sub, Finset.mul_sum]
    have : ∀ n ∈ Finset.range N, Real.exp (-(s * r)) * r ^ (a - 1) * (Ring.choose β n * r ^ n) =
        Ring.choose β n * (Real.exp (-(s * r)) * r ^ (a - 1) * r ^ n) := fun n _ => by ring
    rw [Finset.sum_congr rfl this]
    ring
  simp_rw [heq]
  rw [integral_add hint, integral_finsetSum]
  · congr 1
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [integral_const_mul, (airyReal_moment ha hs n).2]
  · intro n _
    exact ((airyReal_moment ha hs n).1.const_mul (Ring.choose β n))
  · exact integrable_finsetSum _ fun n _ => (airyReal_moment ha hs n).1.const_mul _

/-- One term of the expansion as a real number. -/
theorem airyReal_term {a s β : ℝ} (ha : 0 < a) (hs : 0 < s) (n : ℕ) (Z : ℂ) (hZ : 2 * Z = s) :
    1 / Gamma ((a : ℝ) : ℂ) * (Gamma ((n : ℂ) + ((a : ℝ) : ℂ)) * Ring.choose ((β : ℝ) : ℂ) n) /
      2 ^ n / Z ^ n =
    ((s ^ a / Real.Gamma a * (Ring.choose β n * (Real.Gamma (a + n) * s ^ (-(a + n)))) : ℝ) :
      ℂ) := by
  have hZ' : Z = ((s / 2 : ℝ) : ℂ) := by push_cast; linear_combination hZ / 2
  have hGa : Real.Gamma a ≠ 0 := (Real.Gamma_pos_of_pos ha).ne'
  have hs0 : s ≠ 0 := hs.ne'
  rw [hZ', show (n : ℂ) + ((a : ℝ) : ℂ) = ((n + a : ℝ) : ℂ) by push_cast; ring,
    Complex.Gamma_ofReal, Complex.Gamma_ofReal, ← Complex.ofRealHom_eq_coe β,
    ← Ring.map_choose, Complex.ofRealHom_eq_coe]
  have hpow : s ^ a * s ^ (-(a + n)) = (s ^ n)⁻¹ := by
    rw [← Real.rpow_add hs, show a + -(a + n) = -(n : ℝ) by ring, Real.rpow_neg hs.le,
      Real.rpow_natCast]
  rw [show (1 : ℂ) / (Real.Gamma a : ℂ) * (((Real.Gamma (n + a) : ℝ) : ℂ) *
      ((Ring.choose β n : ℝ) : ℂ)) / 2 ^ n / ((s / 2 : ℝ) : ℂ) ^ n =
      ((1 / Real.Gamma a * (Real.Gamma (n + a) * Ring.choose β n) / 2 ^ n / (s / 2) ^ n : ℝ) : ℂ)
      by push_cast; ring]
  congr 1
  rw [show s ^ a / Real.Gamma a * (Ring.choose β n * (Real.Gamma (a + n) * s ^ (-(a + n)))) =
      Ring.choose β n * Real.Gamma (a + n) * (s ^ a * s ^ (-(a + n))) / Real.Gamma a by ring,
    hpow, add_comm (n : ℝ) a, div_pow]
  field_simp

/-- The exact normalized remainder as a real Laplace integral of the binomial remainder. -/
theorem airyReal_remainder {a s β : ℝ} (ha : 0 < a) (hs : 0 < s) (N : ℕ) (hβ : β ≤ N) (Z : ℂ)
    (hZ : 2 * Z = s) :
    (((s ^ a / Real.Gamma a *
        ∫ r in Ioi (0 : ℝ), Real.exp (-(s * r)) * (r ^ (a - 1) * (1 + r) ^ β) : ℝ)) : ℂ) -
      ∑ n ∈ Finset.range N, 1 / Gamma ((a : ℝ) : ℂ) *
        (Gamma ((n : ℂ) + ((a : ℝ) : ℂ)) * Ring.choose ((β : ℝ) : ℂ) n) / 2 ^ n / Z ^ n =
    ((s ^ a / Real.Gamma a *
      ∫ r in Ioi (0 : ℝ), Real.exp (-(s * r)) * r ^ (a - 1) * airyReal_rho β N r : ℝ) : ℂ) := by
  rw [airyReal_split ha hs N hβ, mul_add, ofReal_add, add_sub_assoc, add_eq_left, sub_eq_zero,
    Finset.mul_sum, ofReal_sum]
  exact Finset.sum_congr rfl fun n _ => (airyReal_term ha hs n Z hZ).symm

/-! ### The real axis -/

/-- For `x > 0`, `ζ(x)` is the real number `(2/3) x^{3/2}`. -/
theorem airyReal_zeta_ofReal {x : ℝ} (hx : 0 < x) :
    airyZetaComplex (x : ℂ) = ((airyZeta x : ℝ) : ℂ) := by
  rw [airyZetaComplex, airyZeta, show (3 / 2 : ℂ) = ((3 / 2 : ℝ) : ℂ) by push_cast; ring,
    ← ofReal_cpow hx.le]
  push_cast; ring

/-- For `x > 0`, `log 2 + ζ̃(x) = log (2 ζ(x))` (real logarithm). -/
theorem airyReal_log_two_add {x : ℝ} (hx : 0 < x) :
    log 2 + airyLogZeta x = ((Real.log (2 * airyZeta x) : ℝ) : ℂ) := by
  have h2 : log (2 : ℂ) = ((Real.log 2 : ℝ) : ℂ) := by
    rw [ofReal_log (by norm_num)]; norm_num
  have h23 : log (2 / 3 : ℂ) = ((Real.log (2 / 3) : ℝ) : ℂ) := by
    rw [ofReal_log (by norm_num)]; push_cast; ring_nf
  have hxl : log (x : ℂ) = ((Real.log x : ℝ) : ℂ) := (ofReal_log hx.le).symm
  rw [airyLogZeta, h2, h23, hxl, airyZeta, Real.log_mul (by norm_num) (by positivity),
    Real.log_mul (by norm_num) (by positivity), Real.log_rpow hx]
  push_cast; ring

/-- For `x > 0`, `exp (a (log 2 + ζ̃(x))) = (2 ζ(x))^a`. -/
theorem airyReal_exp_mul {x : ℝ} (hx : 0 < x) (a : ℝ) :
    exp ((a : ℂ) * (log 2 + airyLogZeta x)) = (((2 * airyZeta x) ^ a : ℝ) : ℂ) := by
  have hs : 0 < 2 * airyZeta x := by have := airyZeta_pos hx; linarith
  rw [airyReal_log_two_add hx, ← ofReal_mul, ← ofReal_exp, Real.rpow_def_of_pos hs, mul_comm]

/-- For `x > 0` the Laplace integral of the kernel `t^{a-1}(1+t)^β` is real. -/
theorem airyReal_integral_ofReal {x : ℝ} (hx : 0 < x) (a β : ℝ) :
    ∫ t in Ioi (0 : ℝ), Complex.exp (-(2 * airyZetaComplex x * t)) * airyRot_kernel a β t =
      ((∫ r in Ioi (0 : ℝ), Real.exp (-(2 * airyZeta x * r)) * (r ^ (a - 1) * (1 + r) ^ β) : ℝ)
        : ℂ) := by
  rw [← integral_complex_ofReal]
  refine setIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
  have hr0 : 0 ≤ r := le_of_lt hr
  simp only [airyRot_kernel, airyReal_zeta_ofReal hx]
  rw [ofReal_mul, ofReal_mul, ofReal_exp, ofReal_cpow hr0, ofReal_cpow (by linarith : 0 ≤ 1 + r)]
  push_cast; ring_nf

/-- The real Laplace representation of the normalized `Ai` on the positive axis. -/
theorem airyReal_ai_repr {x : ℝ} (hx : 0 < x) :
    airyAi x / airyPrefactor .ai x =
      ((((2 * airyZeta x) ^ (5 / 6 : ℝ) / Real.Gamma (5 / 6) *
        ∫ r in Ioi (0 : ℝ), Real.exp (-(2 * airyZeta x * r)) *
          (r ^ ((5 / 6 : ℝ) - 1) * (1 + r) ^ (-1 / 6 : ℝ))) : ℝ) : ℂ) := by
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have harg : |arg (x : ℂ)| < π / 3 := by
    rw [arg_ofReal_of_nonneg hx.le, abs_zero]; positivity
  have hG : Gamma ((5 / 6 : ℝ) : ℂ) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp)
  have hπ : (Real.sqrt π : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hq : (x : ℂ) ^ (1 / 4 : ℂ) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hx0)
  have hE : exp (airyZetaComplex x) * exp (-airyZetaComplex x) = 1 := by
    rw [← exp_add]; simp
  have hc := airyRot_exp_combine hx0 (-1 / 6) (2 / 3) (1 / 4) (5 / 6) (by ring)
  have hc' : 2 * (3 : ℂ) ^ (-1 / 6 : ℂ) * exp (2 / 3 * airyLogZeta x) * (x : ℂ) ^ (1 / 4 : ℂ) =
      exp (((5 / 6 : ℝ) : ℂ) * (log 2 + airyLogZeta x)) := by
    have h1 : exp (-((5 / 6 : ℂ) * (log 2 + airyLogZeta x))) *
        exp ((5 / 6 : ℂ) * (log 2 + airyLogZeta x)) = 1 := by rw [← exp_add]; simp
    push_cast
    linear_combination exp ((5 / 6 : ℂ) * (log 2 + airyLogZeta x)) * hc -
      (2 * (3 : ℂ) ^ (-1 / 6 : ℂ) * exp (2 / 3 * airyLogZeta x) * (x : ℂ) ^ (1 / 4 : ℂ)) * h1
  rw [airyRot_airyAi_anchor hx0 harg, airyReal_integral_ofReal hx, ofReal_mul,
    ofReal_div ((2 * airyZeta x) ^ (5 / 6 : ℝ)) (Real.Gamma (5 / 6)),
    ← airyReal_exp_mul hx, ← hc', ← Complex.Gamma_ofReal]
  simp only [airyPrefactor]
  rw [exp_sub]
  generalize ((∫ r in Ioi (0 : ℝ), Real.exp (-(2 * airyZeta x * r)) *
    (r ^ ((5 / 6 : ℝ) - 1) * (1 + r) ^ (-1 / 6 : ℝ)) : ℝ) : ℂ) = K
  field_simp
  linear_combination (-K) * hE

/-- The real Laplace representation of the normalized `Ai'` on the positive axis. -/
theorem airyReal_aiDeriv_repr {x : ℝ} (hx : 0 < x) :
    airyAiDeriv x / airyPrefactor .aiDeriv x =
      ((((2 * airyZeta x) ^ (7 / 6 : ℝ) / Real.Gamma (7 / 6) *
        ∫ r in Ioi (0 : ℝ), Real.exp (-(2 * airyZeta x * r)) *
          (r ^ ((7 / 6 : ℝ) - 1) * (1 + r) ^ (1 / 6 : ℝ))) : ℝ) : ℂ) := by
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have harg : |arg (x : ℂ)| < π / 3 := by
    rw [arg_ofReal_of_nonneg hx.le, abs_zero]; positivity
  have hG : Gamma ((7 / 6 : ℝ) : ℂ) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp)
  have hπ : (Real.sqrt π : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hq : (x : ℂ) ^ (1 / 4 : ℂ) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hx0)
  have hqq : (x : ℂ) ^ (-1 / 4 : ℂ) * (x : ℂ) ^ (1 / 4 : ℂ) = 1 := by
    rw [← cpow_add _ _ hx0]; norm_num
  have hE : exp (airyZetaComplex x) * exp (-airyZetaComplex x) = 1 := by
    rw [← exp_add]; simp
  have hc := airyRot_exp_combine hx0 (1 / 6) (4 / 3) (-1 / 4) (7 / 6) (by ring)
  have hc' : 2 * (3 : ℂ) ^ (1 / 6 : ℂ) * exp (4 / 3 * airyLogZeta x) * (x : ℂ) ^ (-1 / 4 : ℂ) =
      exp (((7 / 6 : ℝ) : ℂ) * (log 2 + airyLogZeta x)) := by
    have h1 : exp (-((7 / 6 : ℂ) * (log 2 + airyLogZeta x))) *
        exp ((7 / 6 : ℂ) * (log 2 + airyLogZeta x)) = 1 := by rw [← exp_add]; simp
    push_cast
    linear_combination exp ((7 / 6 : ℂ) * (log 2 + airyLogZeta x)) * hc -
      (2 * (3 : ℂ) ^ (1 / 6 : ℂ) * exp (4 / 3 * airyLogZeta x) * (x : ℂ) ^ (-1 / 4 : ℂ)) * h1
  rw [airyRot_airyAiDeriv_anchor hx0 harg, airyReal_integral_ofReal hx, ofReal_mul,
    ofReal_div ((2 * airyZeta x) ^ (7 / 6 : ℝ)) (Real.Gamma (7 / 6)),
    ← airyReal_exp_mul hx, ← hc', ← Complex.Gamma_ofReal]
  simp only [airyPrefactor]
  rw [exp_sub]
  generalize ((∫ r in Ioi (0 : ℝ), Real.exp (-(2 * airyZeta x * r)) *
    (r ^ ((7 / 6 : ℝ) - 1) * (1 + r) ^ (1 / 6 : ℝ)) : ℝ) : ℂ) = K
  field_simp
  have hqq' : (x : ℂ) ^ (-(1 / 4) : ℂ) * (x : ℂ) ^ (1 / 4 : ℂ) = 1 := by
    rw [← cpow_add _ _ hx0]; norm_num
  linear_combination (-K * (x : ℂ) ^ (1 / 4 : ℂ) * (x : ℂ) ^ (-(1 / 4) : ℂ)) * hE + (-K) * hqq'

/-- Packaged form: remainder and first neglected term on the positive axis. -/
theorem airyReal_pack {a β : ℝ} (ha : 0 < a) {N : ℕ} (hβ : β ≤ N) {x : ℝ} (hx : 0 < x)
    {f : ℂ → ℂ} (hf : f x = ((((2 * airyZeta x) ^ a / Real.Gamma a *
        ∫ r in Ioi (0 : ℝ), Real.exp (-(2 * airyZeta x * r)) * (r ^ (a - 1) * (1 + r) ^ β)) : ℝ)
          : ℂ))
    {c : ℕ → ℂ} (hc : ∀ n : ℕ, 1 / Gamma ((a : ℝ) : ℂ) *
      (Gamma ((n : ℂ) + ((a : ℝ) : ℂ)) * Ring.choose ((β : ℝ) : ℂ) n) / 2 ^ n = c n) :
    ‖f x - ∑ k ∈ Finset.range N, c k / airyZetaComplex x ^ k‖ ≤ ‖c N / airyZetaComplex x ^ N‖ ∧
      0 ≤ (f x - ∑ k ∈ Finset.range N, c k / airyZetaComplex x ^ k).re * (c N).re := by
  have hs : 0 < 2 * airyZeta x := by have := airyZeta_pos hx; linarith
  have hZ : 2 * airyZetaComplex x = ((2 * airyZeta x : ℝ) : ℂ) := by
    rw [airyReal_zeta_ofReal hx]; push_cast; ring
  set s := 2 * airyZeta x
  have hR := airyReal_remainder ha hs N hβ _ hZ
  simp only [hc] at hR
  have hT := airyReal_term (β := β) ha hs N _ hZ
  rw [hc] at hT
  rw [hf, hR, hT]
  obtain ⟨-, hb⟩ := airyReal_integral_btw (β := β) ha hs hβ
  set J := ∫ r in Ioi (0 : ℝ), Real.exp (-(s * r)) * r ^ (a - 1) * airyReal_rho β N r
  set M := Ring.choose β N * (Real.Gamma (a + N) * s ^ (-(a + N)))
  have hC : 0 < s ^ a / Real.Gamma a := div_pos (Real.rpow_pos_of_pos hs _) (Real.Gamma_pos_of_pos ha)
  set C := s ^ a / Real.Gamma a
  have hb' : 0 ≤ (C * J) * (C * M - C * J) := by
    have : (C * J) * (C * M - C * J) = C ^ 2 * (J * (M - J)) := by ring
    rw [this]; positivity
  refine ⟨?_, ?_⟩
  · rw [Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
    exact airyReal_sq_le_of_btw hb'
  · have hcN : c N = ((C * M * airyZeta x ^ N : ℝ) : ℂ) := by
      have hz0 : airyZetaComplex x ^ N ≠ 0 := by
        rw [airyReal_zeta_ofReal hx]; exact pow_ne_zero _ (ofReal_ne_zero.mpr (airyZeta_pos hx).ne')
      have : c N = c N / airyZetaComplex x ^ N * airyZetaComplex x ^ N := by field_simp
      rw [this, hT, airyReal_zeta_ofReal hx]; push_cast; ring
    rw [hcN, ofReal_re, ofReal_re]
    have hz := pow_pos (airyZeta_pos hx) N
    have : C * J * (C * M * airyZeta x ^ N) = (C * J * (C * M - C * J) + (C * J) ^ 2) *
      airyZeta x ^ N := by ring
    rw [this]; positivity

/-- `‖e^{-ζ}/(2√π x^{1/4})‖ = e^{-ζ(x)}/(2√π x^{1/4})` for `x > 0`. -/
theorem airyReal_norm_prefactor_ai {x : ℝ} (hx : 0 < x) :
    ‖airyPrefactor .ai x‖ = Real.exp (-airyZeta x) / (2 * Real.sqrt π * x ^ (1 / 4 : ℝ)) := by
  have hq : ‖(x : ℂ) ^ (1 / 4 : ℂ)‖ = x ^ (1 / 4 : ℝ) := by
    rw [show (1 / 4 : ℂ) = ((1 / 4 : ℝ) : ℂ) by push_cast; ring, ← ofReal_cpow hx.le,
      Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  rw [airyPrefactor, norm_div, norm_mul, norm_mul, hq, Complex.norm_exp, neg_re,
    airyReal_zeta_ofReal hx, ofReal_re, Complex.norm_real, Complex.norm_two,
    Real.norm_of_nonneg (Real.sqrt_nonneg _)]

/-- `‖-x^{1/4} e^{-ζ}/(2√π)‖ = x^{1/4} e^{-ζ(x)}/(2√π)` for `x > 0`. -/
theorem airyReal_norm_prefactor_aiDeriv {x : ℝ} (hx : 0 < x) :
    ‖airyPrefactor .aiDeriv x‖ = x ^ (1 / 4 : ℝ) * Real.exp (-airyZeta x) / (2 * Real.sqrt π) := by
  have hq : ‖(x : ℂ) ^ (1 / 4 : ℂ)‖ = x ^ (1 / 4 : ℝ) := by
    rw [show (1 / 4 : ℂ) = ((1 / 4 : ℝ) : ℂ) by push_cast; ring, ← ofReal_cpow hx.le,
      Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  rw [airyPrefactor, norm_div, norm_mul, norm_neg, norm_mul, hq, Complex.norm_exp, neg_re,
    airyReal_zeta_ofReal hx, ofReal_re, Complex.norm_real, Complex.norm_two,
    Real.norm_of_nonneg (Real.sqrt_nonneg _)]

/-- `u_0 = 1`. -/
theorem airyReal_airyU_zero : airyU 0 = 1 := by simp [airyU]
/-- `u_1 = 5/72`. -/
theorem airyReal_airyU_one : airyU 1 = 5 / 72 := by
  simp [airyU, ascPochhammer_one]; norm_num
/-- `v_0 = 1`. -/
theorem airyReal_airyV_zero : airyV 0 = 1 := by simp [airyV, airyReal_airyU_zero]
/-- `v_1 = -7/72`. -/
theorem airyReal_airyV_one : airyV 1 = -7 / 72 := by
  rw [airyV, airyReal_airyU_one]; norm_num

/-- First-neglected-term remainder bound and its sign, DLMF §9.7(iii). -/
theorem airy_ai_real_error {x : ℝ} (hx : 0 < x) {N : ℕ} (hN : 0 ≤ N) :
    ‖airyRemainder .ai N x‖ ≤ 
      ‖airyExpansionCoeff .ai N / airyZetaComplex x ^ N‖ ∧
      0 ≤ (airyRemainder .ai N x).re * (airyExpansionCoeff .ai N).re :=
  airyReal_pack (a := 5 / 6) (β := -1 / 6) (by norm_num)
    (by have := (Nat.cast_nonneg N : (0 : ℝ) ≤ N); linarith) hx
    (f := fun z => airyAi z / airyPrefactor .ai z) (airyReal_ai_repr hx) airyRot_coeff_ai

/-- First-neglected-term remainder bound and its sign, DLMF §9.7(iii). -/
theorem airy_aiDeriv_real_error {x : ℝ} (hx : 0 < x) {N : ℕ} (hN : 1 ≤ N) :
    ‖airyRemainder .aiDeriv N x‖ ≤ 
      ‖airyExpansionCoeff .aiDeriv N / airyZetaComplex x ^ N‖ ∧
      0 ≤ (airyRemainder .aiDeriv N x).re * (airyExpansionCoeff .aiDeriv N).re :=
  airyReal_pack (a := 7 / 6) (β := 1 / 6) (by norm_num)
    (by have : (1 : ℝ) ≤ N := by exact_mod_cast hN
        linarith) hx
    (f := fun z => airyAiDeriv z / airyPrefactor .aiDeriv z) (airyReal_aiDeriv_repr hx)
    airyRot_coeff_aiDeriv

/-! ### The σ = 1/6 Stieltjes form of `Ai` and Olver's error bounds

Via the Kummer transformation, `Ai` is a Laplace integral of `t^{-5/6}(1+t)^{-5/6}`. Rotating to
the ray `θ = -(3/2) arg z` makes the damping `|2ζ|` real; the Stieltjes–Euler form of
`(1+t)^{-5/6}` (`DLMF.Airy.StieltjesForm`) then bounds the remainder by `M_θ` and by `χ + 1`
times the first neglected term (DLMF 9.7.17 for `|arg z| < 2π/3`). -/

/-- `s^{-2/3} = exp(-(2/3)(log 2 + L))` for `|arg z| < 2π/3`. -/
theorem airySt_two_zeta_cpow {z : ℂ} (hz : z ≠ 0) (harg : |arg z| < 2 * π / 3) (c : ℂ) :
    (2 * airyZetaComplex z) ^ c = exp (c * (log 2 + airyLogZeta z)) := by
  rw [← exp_log_two_add_airyLogZeta hz, cpow_def_of_ne_zero (exp_ne_zero _), log_exp, mul_comm]
  · rw [im_log_two_add_airyLogZeta]; linarith [abs_lt.mp harg, Real.pi_pos]
  · rw [im_log_two_add_airyLogZeta]; linarith [abs_lt.mp harg, Real.pi_pos]

/-- The σ = 1/6 anchor: Tricomi's integral for `U(1/6, 1/3, 2ζ)` on `|arg z| < π/3`. -/
theorem airySt_airyAi_anchor {z : ℂ} (hz : z ≠ 0) (harg : |arg z| < π / 3) :
    airyAi z = ((3 : ℂ) ^ (-1 / 6 : ℂ) * exp (-(2 / 3) * log 2) / Real.sqrt π) *
      exp (0 * airyLogZeta z - airyZetaComplex z) * (1 / Gamma ((1 / 6 : ℝ) : ℂ) *
        ∫ t in Ioi (0 : ℝ), Complex.exp (-(2 * airyZetaComplex z * t)) *
          airyRot_kernel (1 / 6) (-5 / 6) t) := by
  have hs0 : 2 * airyZetaComplex z ≠ 0 := by
    rw [← exp_log_two_add_airyLogZeta hz]; exact exp_ne_zero _
  rw [airyAi_eq_kummerU hz (harg.trans (by linarith [Real.pi_pos])),
    kummerU_kummer_transform_all _ _ hs0,
    kummerU_laplace (by norm_num) (airyRot_re_two_zeta_pos hz harg),
    airySt_two_zeta_cpow hz (harg.trans (by linarith [Real.pi_pos]))]
  have hG : Gamma ((1 / 6 : ℝ) : ℂ) = Gamma (5 / 6 - 5 / 3 + 1) := by push_cast; ring_nf
  have hI : ∀ t : ℝ, Complex.exp (-(2 * airyZetaComplex z) * t) *
      (t : ℂ) ^ ((5 / 6 : ℂ) - 5 / 3 + 1 - 1) * (1 + (t : ℂ)) ^ ((2 - 5 / 3 : ℂ) -
        (5 / 6 - 5 / 3 + 1) - 1) = Complex.exp (-(2 * airyZetaComplex z * t)) *
        airyRot_kernel (1 / 6) (-5 / 6) t := by
    intro t
    simp only [airyRot_kernel]
    rw [show (((1 / 6 : ℝ) : ℂ) - 1) = 5 / 6 - 5 / 3 + 1 - 1 by push_cast; ring,
      show (((-5 / 6 : ℝ)) : ℂ) = (2 - 5 / 3 : ℂ) - (5 / 6 - 5 / 3 + 1) - 1 by push_cast; ring]
    ring_nf
  simp_rw [hI, hG]
  have hE : exp (2 / 3 * airyLogZeta z - airyZetaComplex z) *
      exp ((1 - 5 / 3) * (log 2 + airyLogZeta z)) =
      exp (-(2 / 3) * log 2) * exp (0 * airyLogZeta z - airyZetaComplex z) := by
    rw [← exp_add, ← exp_add]; congr 1; ring
  linear_combination ((3 : ℂ) ^ (-1 / 6 : ℂ) / Real.sqrt π * (1 / Gamma (5 / 6 - 5 / 3 + 1) *
    ∫ t in Ioi (0 : ℝ), Complex.exp (-(2 * airyZetaComplex z * t)) *
      airyRot_kernel (1 / 6) (-5 / 6) t)) * hE

/-- `2 · 3^{-1/6} 2^{-2/3} z^{1/4} = exp((1/6)(log 2 + L))`. -/
theorem airySt_norm_const {z : ℂ} (hz : z ≠ 0) :
    2 * ((3 : ℂ) ^ (-1 / 6 : ℂ) * exp (-(2 / 3) * log 2)) * z ^ (1 / 4 : ℂ) =
      exp ((1 / 6 : ℂ) * (log 2 + airyLogZeta z)) := by
  rw [cpow_def_of_ne_zero hz, cpow_def_of_ne_zero (by norm_num : (3 : ℂ) ≠ 0), airyLogZeta,
    log_two_thirds]
  calc 2 * (exp (log 3 * (-1 / 6)) * exp (-(2 / 3) * log 2)) * exp (log z * (1 / 4))
      = exp (log 2) * (exp (log 3 * (-1 / 6)) * exp (-(2 / 3) * log 2)) *
          exp (log z * (1 / 4)) := by rw [exp_log two_ne_zero]
    _ = _ := by simp only [← exp_add]; congr 1; ring

/-- **The normalized `Ai` as a rotated σ = 1/6 Laplace integral**, for `|θ| < π` and
`|(3/2) arg z + θ| < π/2`. -/
theorem airySt_F_eq {z : ℂ} (hz : z ≠ 0) {θ : ℝ} (hθ : |θ| < π)
    (hzθ : |3 / 2 * arg z + θ| < π / 2) :
    airyAi z / airyPrefactor .ai z = exp ((1 / 6 : ℂ) * (log 2 + airyLogZeta z)) *
      (1 / Gamma ((1 / 6 : ℝ) : ℂ) * (exp (θ * I) *
        airyRot_lap (1 / 6) (-5 / 6) θ (exp (log 2 + airyLogZeta z + θ * I)))) := by
  have hπ : (Real.sqrt π : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hq : z ^ (1 / 4 : ℂ) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hz)
  rw [airyRot_eq_of_anchor differentiable_airyAi _ _ (1 / 6) (-5 / 6) (by norm_num)
    (fun w hw harg => airySt_airyAi_anchor hw harg) hθ hz hzθ, ← airySt_norm_const hz]
  simp only [airyPrefactor]
  generalize airyRot_lap (1 / 6) (-5 / 6) θ (exp (log 2 + airyLogZeta z + θ * I)) = K
  generalize (3 : ℂ) ^ (-1 / 6 : ℂ) * exp (-(2 / 3) * log 2) = A
  have hG : Gamma ((1 / 6 : ℝ) : ℂ) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp)
  rw [exp_sub, zero_mul, Complex.exp_zero]
  have hE : exp (airyZetaComplex z) * exp (-airyZetaComplex z) = 1 := by
    rw [← exp_add]; simp
  field_simp
  linear_combination (-(A * K)) * hE

/-- Real Gamma ratio as a rising factorial. -/
theorem airySt_gamma_ratio_real (n : ℕ) {x : ℝ} (hx : 0 < x) :
    Real.Gamma (x + n) / Real.Gamma x = (ascPochhammer ℝ n).eval x := by
  have h := airyRot_gamma_ratio n hx
  rw [← ofReal_natCast, ← ofReal_add, Complex.Gamma_ofReal, Complex.Gamma_ofReal,
    ← ofReal_div] at h
  rw [add_comm]; exact_mod_cast h

/-- The σ = 1/6 coefficients: `c_k(5/6) Γ(k+1/6)/Γ(1/6) = (-1)^k u_k 2^k`. -/
theorem airySt_coef_ai (k : ℕ) :
    airySt_coef (5 / 6) k * Real.Gamma (1 / 6 + k) / Real.Gamma (1 / 6) =
      (-1) ^ k * airyU k * 2 ^ k := by
  have h1 := airySt_gamma_ratio_real k (x := 5 / 6) (by norm_num)
  have h2 := airySt_gamma_ratio_real k (x := 1 / 6) (by norm_num)
  have g1 := Real.Gamma_pos_of_pos (show (0 : ℝ) < 5 / 6 by norm_num)
  have g2 := Real.Gamma_pos_of_pos (show (0 : ℝ) < 1 / 6 by norm_num)
  rw [div_eq_iff g1.ne'] at h1
  rw [div_eq_iff g2.ne'] at h2
  simp only [airySt_coef, airyU]
  rw [h1, mul_div_assoc, h2, Real.Gamma_nat_eq_factorial]
  have hf : (k.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  field_simp

/-- On `θ = -(3/2) arg z` the damping `2ζ e^{iθ}` is the real number `|2ζ|`. -/
theorem airySt_W_real (z : ℂ) :
    exp (log 2 + airyLogZeta z + ((-(3 / 2 * arg z) : ℝ) : ℂ) * I) =
      ((Real.exp (log 2 + airyLogZeta z).re : ℝ) : ℂ) := by
  rw [ofReal_exp]
  congr 1
  have h := im_log_two_add_airyLogZeta z
  simp only [add_im] at h
  apply Complex.ext
  · simp
  · simp [h]

/-- The rotated Laplace integral of `t^{-5/6}(1+t)^{-5/6}` is the ray integral `airySt_L`. -/
theorem airySt_lap_eq (θ W : ℝ) :
    airyRot_lap (1 / 6) (-5 / 6) θ (W : ℂ) = airySt_L (1 / 6) (5 / 6) θ W := by
  unfold airyRot_lap airySt_L airyRot_kernel
  congr 1; funext r
  rw [smul_eq_mul]; push_cast; ring_nf

/-- Integrability of `e^{-Wr} t^{-5/6} (1+t)^{-5/6}`, `t = r e^{iθ}`, for `|θ| < π`. -/
theorem airySt_hint {θ W : ℝ} (hθ : |θ| < π) (hW : 0 < W) :
    IntegrableOn (fun r : ℝ => Complex.exp (-(W * r)) *
      (((r : ℂ) * exp (θ * I)) ^ (((1 / 6 : ℝ) : ℂ) - 1) *
        (1 + (r : ℂ) * exp (θ * I)) ^ (-((5 / 6 : ℝ) : ℂ)))) (Ioi 0) := by
  have h := airyRot_integrableOn (1 / 6) (-5 / 6) (by norm_num) hθ hW
  refine h.congr_fun (fun r _ => ?_) measurableSet_Ioi
  simp only [airyRot_kernel, Complex.real_smul, ofReal_exp]
  push_cast; ring_nf

/-- **Ai remainder as a ray remainder.** -/
theorem airySt_ai_remainder {z : ℂ} (hz : z ≠ 0) (harg : |arg z| < 2 * π / 3) (N : ℕ) :
    airyRemainder .ai N z = exp ((1 / 6 : ℂ) * (log 2 + airyLogZeta z)) *
        (1 / Gamma ((1 / 6 : ℝ) : ℂ)) * exp (((-(3 / 2 * arg z) : ℝ) : ℂ) * I) *
      (airySt_L (1 / 6) (5 / 6) (-(3 / 2 * arg z)) (Real.exp (log 2 + airyLogZeta z).re) -
        ∑ k ∈ Finset.range N, airySt_T (1 / 6) (5 / 6) (-(3 / 2 * arg z))
          (Real.exp (log 2 + airyLogZeta z).re) k) ∧
    ∀ k : ℕ, airyExpansionCoeff .ai k / airyZetaComplex z ^ k =
      exp ((1 / 6 : ℂ) * (log 2 + airyLogZeta z)) *
        (1 / Gamma ((1 / 6 : ℝ) : ℂ)) * exp (((-(3 / 2 * arg z) : ℝ) : ℂ) * I) *
      airySt_T (1 / 6) (5 / 6) (-(3 / 2 * arg z)) (Real.exp (log 2 + airyLogZeta z).re) k := by
  set θ : ℝ := -(3 / 2 * arg z) with hθdef
  set ℓ := log 2 + airyLogZeta z with hℓdef
  set W : ℝ := Real.exp ℓ.re with hWdef
  have hθ : |θ| < π := by
    rw [hθdef, abs_neg, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)]; linarith
  have hzθ : |3 / 2 * arg z + θ| < π / 2 := by
    rw [hθdef, add_neg_cancel, abs_zero]; positivity
  have hF := airySt_F_eq hz hθ hzθ
  rw [airySt_W_real, airySt_lap_eq] at hF
  have hG : Gamma ((1 / 6 : ℝ) : ℂ) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp)
  have hcT : ∀ k : ℕ, airyExpansionCoeff .ai k / airyZetaComplex z ^ k =
      exp ((1 / 6 : ℂ) * ℓ) * (1 / Gamma ((1 / 6 : ℝ) : ℂ)) * exp (θ * I) *
        airySt_T (1 / 6) (5 / 6) θ W k := by
    intro k
    have hℓ : ℓ = (ℓ.re : ℂ) + ((-θ : ℝ) : ℂ) * I := by
      have h := im_log_two_add_airyLogZeta z
      simp only [add_im] at h
      apply Complex.ext
      · simp
      · simp [hℓdef, hθdef, h]
    have hWc : (W : ℂ) ^ (-(((1 / 6 : ℝ) : ℂ) + k)) =
        exp (-(((1 / 6 : ℝ) : ℂ) + k) * (ℓ.re : ℂ)) := by
      rw [hWdef, ofReal_exp, cpow_def_of_ne_zero (exp_ne_zero _), log_exp (by simp [Real.pi_pos])
        (by simp [Real.pi_pos.le]), mul_comm]
    have hζ : airyZetaComplex z = exp ℓ / 2 := by
      rw [hℓdef, exp_log_two_add_airyLogZeta hz]; ring
    have hc := airySt_coef_ai k
    have hgk : Gamma (((1 / 6 : ℝ) : ℂ) + k) = ((Real.Gamma (1 / 6 + k) : ℝ) : ℂ) := by
      rw [← Complex.Gamma_ofReal]; push_cast; rfl
    have hg0 : Gamma ((1 / 6 : ℝ) : ℂ) = ((Real.Gamma (1 / 6) : ℝ) : ℂ) := by
      rw [← Complex.Gamma_ofReal]
    have hc' : ((-1 : ℂ) ^ k * (airyU k : ℂ)) = (airySt_coef (5 / 6) k : ℂ) *
        Gamma (((1 / 6 : ℝ) : ℂ) + k) / Gamma ((1 / 6 : ℝ) : ℂ) / 2 ^ k := by
      rw [hgk, hg0]
      have : ((airySt_coef (5 / 6) k * Real.Gamma (1 / 6 + k) / Real.Gamma (1 / 6) : ℝ) : ℂ) =
          (((-1) ^ k * airyU k * 2 ^ k : ℝ) : ℂ) := by rw [hc]
      push_cast at this
      rw [this]; field_simp
    have key : exp ((1 / 6 : ℂ) * ℓ) * exp (θ * I) * exp (θ * I * (((1 / 6 : ℝ) : ℂ) - 1 + k)) *
        exp (-(((1 / 6 : ℝ) : ℂ) + k) * (ℓ.re : ℂ)) * exp (k * ℓ) = 1 := by
      rw [← exp_add, ← exp_add, ← exp_add, ← exp_add]
      convert exp_zero using 2
      generalize ℓ.re = R at hℓ ⊢
      rw [hℓ]; push_cast; ring
    simp only [airyExpansionCoeff, airySt_T]
    rw [hc', hWc, hζ, div_pow, ← Complex.exp_nat_mul]
    generalize exp ((1 / 6 : ℂ) * ℓ) = E1 at key ⊢
    generalize exp (θ * I) = E2 at key ⊢
    generalize exp (θ * I * (((1 / 6 : ℝ) : ℂ) - 1 + k)) = E3 at key ⊢
    generalize exp (-(((1 / 6 : ℝ) : ℂ) + k) * (ℓ.re : ℂ)) = E4 at key ⊢
    have hE5 : exp (k * ℓ) ≠ 0 := exp_ne_zero _
    generalize exp (k * ℓ) = E5 at key hE5 ⊢
    field_simp
    linear_combination (-((airySt_coef (5 / 6) k : ℂ) * Gamma (((1 / 6 : ℝ) : ℂ) + k))) * key
  refine ⟨?_, hcT⟩
  rw [airyRemainder, airyFunction, hF, airyExponentialSum]
  simp_rw [hcT]
  rw [← Finset.mul_sum]
  ring

/-- `|(3/2) arg z| < π` for `|arg z| < 2π/3`. -/
theorem airySt_theta_lt {z : ℂ} (harg : |arg z| < 2 * π / 3) : |-(3 / 2 * arg z)| < π := by
  rw [abs_neg, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)]; linarith

/-- The `M_θ` bound for Ai on `|arg z| < 2π/3`. -/
theorem airySt_ai_le_M {z : ℂ} (hz : z ≠ 0) (harg : |arg z| < 2 * π / 3) (N : ℕ) :
    ‖airyRemainder .ai N z‖ ≤ airySt_M (-(3 / 2 * arg z)) *
      ‖airyExpansionCoeff .ai N / airyZetaComplex z ^ N‖ := by
  obtain ⟨h1, h2⟩ := airySt_ai_remainder hz harg N
  rw [h1, h2]
  generalize exp ((1 / 6 : ℂ) * (log 2 + airyLogZeta z)) * (1 / Gamma ((1 / 6 : ℝ) : ℂ)) *
    exp (((-(3 / 2 * arg z) : ℝ) : ℂ) * I) = c
  rw [norm_mul, norm_mul]
  have hW : 0 < Real.exp (log 2 + airyLogZeta z).re := Real.exp_pos _
  have hb := airySt_rem_le_M (a := 5 / 6) (b := 1 / 6) (by norm_num) (by norm_num) (by norm_num)
    hW (airySt_theta_lt harg) N (airySt_hint (airySt_theta_lt harg) hW)
  calc _ ≤ ‖_‖ * (airySt_M (-(3 / 2 * arg z)) * ‖airySt_T (1 / 6) (5 / 6) (-(3 / 2 * arg z))
        (Real.exp (log 2 + airyLogZeta z).re) N‖) := mul_le_mul_of_nonneg_left hb (norm_nonneg _)
    _ = _ := by ring

/-- The `χ + 1` bound for Ai on `|arg z| < 2π/3`, `arg z ≠ 0`. -/
theorem airySt_ai_le_chi {z : ℂ} (hz : z ≠ 0) (harg : |arg z| < 2 * π / 3)
    (hsin : Real.sin (3 * arg z / 2) ≠ 0) (N : ℕ) :
    ‖airyRemainder .ai N z‖ ≤ (airyChi (N + 1 / 6) + 1) *
      ‖airyExpansionCoeff .ai N / airyZetaComplex z ^ N‖ := by
  obtain ⟨h1, h2⟩ := airySt_ai_remainder hz harg N
  rw [h1, h2]
  generalize exp ((1 / 6 : ℂ) * (log 2 + airyLogZeta z)) * (1 / Gamma ((1 / 6 : ℝ) : ℂ)) *
    exp (((-(3 / 2 * arg z) : ℝ) : ℂ) * I) = c
  rw [norm_mul, norm_mul]
  have hW : 0 < Real.exp (log 2 + airyLogZeta z).re := Real.exp_pos _
  have hs : Real.sin (-(3 / 2 * arg z)) ≠ 0 := by
    rw [Real.sin_neg, neg_ne_zero, show 3 / 2 * arg z = 3 * arg z / 2 by ring]; exact hsin
  have hb := airySt_rem_le_chi (a := 5 / 6) (b := 1 / 6) (by norm_num) (by norm_num) (by norm_num)
    hW (airySt_theta_lt harg) hs N (airySt_hint (airySt_theta_lt harg) hW)
  rw [show airySt_chi (1 / 6 + N) = airyChi (N + 1 / 6) by rw [add_comm]; rfl] at hb
  calc _ ≤ ‖_‖ * ((airyChi (N + 1 / 6) + 1) * ‖airySt_T (1 / 6) (5 / 6) (-(3 / 2 * arg z))
        (Real.exp (log 2 + airyLogZeta z).re) N‖) := mul_le_mul_of_nonneg_left hb (norm_nonneg _)
    _ = _ := by ring

/-! ### A sharp Gamma inequality for the last sector of 9.7.17

`(N/(2e))^N ≤ √(2π(N+1/6)) u_N` for all `N`. With `q_N` the logarithm of the ratio, `q_N → 0` by
Binet's formula and `q_{N+1} ≤ q_N` for `N ≥ 6` by a fourth-order bound for `log(1+x)`; the
cases `N ≤ 5` are checked from `e > 2.7182818283` and `π > 3.141592`. -/

/-- `p_N = (1/6)_N (5/6)_N`. -/
def airySt_p (N : ℕ) : ℝ := (ascPochhammer ℝ N).eval (1 / 6) * (ascPochhammer ℝ N).eval (5 / 6)

/-- `p_N > 0`. -/
theorem airySt_p_pos (N : ℕ) : 0 < airySt_p N :=
  mul_pos (ascPochhammer_pos N _ (by norm_num)) (ascPochhammer_pos N _ (by norm_num))

/-- `p_{N+1} = p_N (N + 1/6)(N + 5/6)`. -/
theorem airySt_p_succ (N : ℕ) : airySt_p (N + 1) = airySt_p N * ((N + 1 / 6) * (N + 5 / 6)) := by
  simp only [airySt_p, ascPochhammer_succ_eval]; ring

/-- `log(√(2π(N+1/6)) p_N e^N / (N^N N!))`. -/
def airySt_q (N : ℕ) : ℝ :=
  Real.log (2 * π * (N + 1 / 6)) / 2 + Real.log (airySt_p N) - N * Real.log N + N -
    Real.log N.factorial

/-- `log(1+x) ≥ x - x²/2 + x³/3 - x⁴/4` for `0 ≤ x ≤ 1/6`. -/
theorem airySt_log_lower {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 6) :
    x - x ^ 2 / 2 + x ^ 3 / 3 - x ^ 4 / 4 ≤ Real.log (1 + x) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := -x) (by rw [abs_neg, abs_of_nonneg hx0]; linarith) 5
  rw [abs_neg, abs_of_nonneg hx0, sub_neg_eq_add] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  have h1 := (abs_le.mp h).1
  have h2 : x ^ 6 / (1 - x) ≤ x ^ 5 / 5 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    have : 0 ≤ x ^ 5 := pow_nonneg hx0 5
    nlinarith
  norm_num at h1
  nlinarith

/-- The polynomial inequality behind the monotonicity of `q`. -/
theorem airySt_poly {N : ℝ} (hN : 4 ≤ N) :
    (N + 7 / 6) * (N + 1 / 6) * (N + 5 / 6) ^ 2 ≤
      N * (N + 1) ^ 3 * (1 + (1 / (6 * N ^ 2) - 1 / (6 * N ^ 3) - 1 / (4 * N ^ 4))) := by
  have hN0 : 0 < N := by linarith
  have key : 0 ≤ 72 * N ^ 5 + 108 * N ^ 4 - 499 * N ^ 3 - 1404 * N ^ 2 - 1188 * N - 324 := by
    obtain ⟨t, rfl⟩ : ∃ t, N = t + 4 := ⟨N - 4, by ring⟩
    have ht : 0 ≤ t := by linarith
    nlinarith [pow_nonneg ht 2, pow_nonneg ht 3, pow_nonneg ht 4, pow_nonneg ht 5]
  rw [← sub_nonneg]
  have : N * (N + 1) ^ 3 * (1 + (1 / (6 * N ^ 2) - 1 / (6 * N ^ 3) - 1 / (4 * N ^ 4))) -
      (N + 7 / 6) * (N + 1 / 6) * (N + 5 / 6) ^ 2 =
      (72 * N ^ 5 + 108 * N ^ 4 - 499 * N ^ 3 - 1404 * N ^ 2 - 1188 * N - 324) /
        (1296 * N ^ 3) := by
    field_simp; ring
  rw [this]; positivity

/-- `q_{N+1} ≤ q_N` for `N ≥ 6`. -/
theorem airySt_q_succ_le {N : ℕ} (hN : 6 ≤ N) : airySt_q (N + 1) ≤ airySt_q N := by
  have hN' : (6 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  set x : ℝ := 1 / N with hx
  have hx0 : 0 ≤ x := by positivity
  have hx6 : x ≤ 1 / 6 := by rw [hx]; exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hN'
  have hL := airySt_log_lower hx0 hx6
  have hlog1 : Real.log (N + 1) = Real.log N + Real.log (1 + x) := by
    rw [← Real.log_mul hN0.ne' (by positivity)]; congr 1; rw [hx]; field_simp
  set δ : ℝ := 1 / (6 * (N : ℝ) ^ 2) - 1 / (6 * (N : ℝ) ^ 3) - 1 / (4 * (N : ℝ) ^ 4) with hδ
  have hδL : 2 + δ ≤ (2 * N + 1) * Real.log (1 + x) := by
    have : (2 * N + 1) * (x - x ^ 2 / 2 + x ^ 3 / 3 - x ^ 4 / 4) = 2 + δ := by
      rw [hx, hδ]; field_simp; ring
    rw [← this]; exact mul_le_mul_of_nonneg_left hL (by positivity)
  have hδ1 : 0 < 1 + δ := by
    have := airySt_poly (by linarith : (4 : ℝ) ≤ N)
    have hp : (0 : ℝ) < ((N : ℝ) + 7 / 6) * ((N : ℝ) + 1 / 6) * ((N : ℝ) + 5 / 6) ^ 2 := by
      positivity
    by_contra hc
    replace hc := not_lt.mp hc
    have : N * (N + 1) ^ 3 * (1 + δ) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) hc
    linarith
  have hP : Real.log ((N + 7 / 6) * (N + 1 / 6) * (N + 5 / 6) ^ 2) ≤
      4 * Real.log N + 3 * Real.log (1 + x) + δ := by
    calc _ ≤ Real.log (N * (N + 1) ^ 3 * (1 + δ)) :=
          Real.log_le_log (by positivity) (airySt_poly (by linarith))
      _ = Real.log N + 3 * Real.log (N + 1) + Real.log (1 + δ) := by
          rw [Real.log_mul (by positivity) hδ1.ne', Real.log_mul hN0.ne' (by positivity),
            Real.log_pow]; push_cast; ring
      _ ≤ Real.log N + 3 * Real.log (N + 1) + δ := by
          have := Real.log_le_sub_one_of_pos hδ1; linarith
      _ = _ := by rw [hlog1]; ring
  have hexp : Real.log ((N + 7 / 6) * (N + 1 / 6) * (N + 5 / 6) ^ 2) =
      Real.log (N + 7 / 6) + Real.log (N + 1 / 6) + 2 * Real.log (N + 5 / 6) := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_pow]; push_cast; ring
  have e1 : Real.log (2 * π * (((N + 1 : ℕ) : ℝ) + 1 / 6)) =
      Real.log (2 * π) + Real.log ((N : ℝ) + 7 / 6) := by
    rw [Real.log_mul (by positivity) (by positivity)]; push_cast; ring_nf
  have e1' : Real.log (2 * π * ((N : ℝ) + 1 / 6)) =
      Real.log (2 * π) + Real.log ((N : ℝ) + 1 / 6) :=
    Real.log_mul (by positivity) (by positivity)
  have e2 : Real.log (airySt_p (N + 1)) =
      Real.log (airySt_p N) + Real.log ((N : ℝ) + 1 / 6) + Real.log ((N : ℝ) + 5 / 6) := by
    rw [airySt_p_succ, Real.log_mul (airySt_p_pos N).ne' (by positivity),
      Real.log_mul (by positivity) (by positivity)]; ring
  have e3 : Real.log ((N + 1).factorial : ℝ) = Real.log ((N : ℝ) + 1) + Real.log N.factorial := by
    rw [Nat.factorial_succ, Nat.cast_mul, Real.log_mul (by positivity) (by positivity)]; push_cast
    ring
  simp only [airySt_q]
  rw [e1, e1', e2, e3]
  push_cast
  rw [hlog1]
  nlinarith [hP, hexp, hδL]


/-- `(1/6)_N (5/6)_N · 2π = Γ(N+1/6) Γ(N+5/6)`. -/
theorem airySt_p_gamma (N : ℕ) :
    airySt_p N * (2 * π) = Real.Gamma (N + 1 / 6) * Real.Gamma (N + 5 / 6) := by
  have h1 := airySt_gamma_ratio_real N (x := 1 / 6) (by norm_num)
  have h2 := airySt_gamma_ratio_real N (x := 5 / 6) (by norm_num)
  have hr := Real.Gamma_mul_Gamma_one_sub (1 / 6)
  rw [show π * (1 / 6 : ℝ) = π / 6 by ring, Real.sin_pi_div_six,
    show (1 : ℝ) - 1 / 6 = 5 / 6 by norm_num] at hr
  have g1 := Real.Gamma_pos_of_pos (show (0 : ℝ) < 1 / 6 by norm_num)
  have g2 := Real.Gamma_pos_of_pos (show (0 : ℝ) < 5 / 6 by norm_num)
  simp only [airySt_p, ← h1, ← h2]
  rw [add_comm (N : ℝ), add_comm (N : ℝ)]
  field_simp
  rw [hr]; ring

/-- `log (N + a) = log N + log (1 + a/N)` for `N ≥ 1`, `a > 0`. -/
theorem airySt_log_add {N : ℕ} (hN : 1 ≤ N) {a : ℝ} (ha : 0 < a) :
    Real.log (N + a) = Real.log N + Real.log (1 + a / N) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  rw [← Real.log_mul hN0.ne' (by positivity)]; congr 1; field_simp

/-- The Binet form of `q_N`. -/
theorem airySt_q_eq {N : ℕ} (hN : 1 ≤ N) :
    airySt_q N = (N + 1 / 6) * Real.log (1 + (1 / 6) / N) +
      (N + 1 / 3) * Real.log (1 + (5 / 6) / N) - (N + 1 / 2) * Real.log (1 + 1 / N) +
      DLMF.Gamma.binetIntegral (N + 1 / 6) + DLMF.Gamma.binetIntegral (N + 5 / 6) -
      DLMF.Gamma.binetIntegral (N + 1) := by
  have hp : Real.log (airySt_p N) = Real.log (Real.Gamma (N + 1 / 6)) +
      Real.log (Real.Gamma (N + 5 / 6)) - Real.log (2 * π) := by
    have h := congrArg Real.log (airySt_p_gamma N)
    rw [Real.log_mul (airySt_p_pos N).ne' (by positivity),
      Real.log_mul (Real.Gamma_pos_of_pos (by positivity)).ne'
        (Real.Gamma_pos_of_pos (by positivity)).ne'] at h
    linarith
  have hf : Real.log (N.factorial : ℝ) = Real.log (Real.Gamma (N + 1)) := by
    rw [Real.Gamma_nat_eq_factorial]
  have b1 := DLMF.Gamma.log_Gamma_eq_add_binetIntegral (x := (N : ℝ) + 1 / 6) (by positivity)
  have b2 := DLMF.Gamma.log_Gamma_eq_add_binetIntegral (x := (N : ℝ) + 5 / 6) (by positivity)
  have b3 := DLMF.Gamma.log_Gamma_eq_add_binetIntegral (x := (N : ℝ) + 1) (by positivity)
  have l1 := airySt_log_add hN (a := 1 / 6) (by norm_num)
  have l2 := airySt_log_add hN (a := 5 / 6) (by norm_num)
  have l3 := airySt_log_add hN (a := 1) (by norm_num)
  have e1 : Real.log (2 * π * ((N : ℝ) + 1 / 6)) =
      Real.log (2 * π) + Real.log ((N : ℝ) + 1 / 6) :=
    Real.log_mul (by positivity) (by positivity)
  have e2 : Real.log (2 * π) = Real.log 2 + Real.log π := Real.log_mul (by norm_num) (by positivity)
  simp only [airySt_q]
  rw [hp, hf, b1, b2, b3, e1, l1, l2, l3, e2]
  ring

/-- `q_N → 0` as `N → ∞` (Stirling). -/
theorem airySt_tendsto_q : Tendsto airySt_q atTop (𝓝 0) := by
  have hn := tendsto_natCast_atTop_atTop (R := ℝ)
  have hA : ∀ t : ℝ, Tendsto (fun N : ℕ => (N : ℝ) * Real.log (1 + t / N)) atTop (𝓝 t) :=
    fun t => (Real.tendsto_mul_log_one_add_div_atTop t).comp hn
  have hB : ∀ t : ℝ, Tendsto (fun N : ℕ => Real.log (1 + t / N)) atTop (𝓝 0) := by
    intro t
    have h : Tendsto (fun N : ℕ => 1 + t / (N : ℝ)) atTop (𝓝 1) := by
      simpa using tendsto_const_nhds.add (tendsto_const_nhds.div_atTop hn)
    have := ((Real.continuousAt_log one_ne_zero).tendsto).comp h
    simpa [Function.comp_def] using this
  have hC : ∀ a : ℝ, 0 < a →
      Tendsto (fun N : ℕ => DLMF.Gamma.binetIntegral (N + a)) atTop (𝓝 0) := by
    intro a ha
    have hu : Tendsto (fun N : ℕ => 1 / (12 * ((N : ℝ) + a))) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop
        (Tendsto.const_mul_atTop (by norm_num) (tendsto_atTop_add_const_right _ a hn))
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu (fun N => ?_) (fun N => ?_)
    · exact (DLMF.Gamma.binetIntegral_mem (by positivity)).1
    · exact (DLMF.Gamma.binetIntegral_mem (by positivity)).2
  have hD : ∀ a t : ℝ, Tendsto (fun N : ℕ => ((N : ℝ) + a) * Real.log (1 + t / N)) atTop (𝓝 t) := by
    intro a t
    have := (hA t).add ((hB t).const_mul a)
    simp only [mul_zero, add_zero] at this
    refine this.congr fun N => ?_
    ring
  have hall := ((((hD (1 / 6) (1 / 6)).add (hD (1 / 3) (5 / 6))).sub (hD (1 / 2) 1)).add
    (hC (1 / 6) (by norm_num))).add (hC (5 / 6) (by norm_num)) |>.sub (hC 1 one_pos)
  rw [show (1 / 6 + 5 / 6 - 1 + 0 + 0 - 0 : ℝ) = 0 by norm_num] at hall
  refine hall.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  rw [airySt_q_eq hN]

/-- `q_N ≥ 0` for `N ≥ 6`. -/
theorem airySt_q_nonneg {N : ℕ} (hN : 6 ≤ N) : 0 ≤ airySt_q N := by
  have hmono : ∀ n, N ≤ n → airySt_q n ≤ airySt_q N := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => exact le_rfl
    | succ n hn ih => exact (airySt_q_succ_le (hN.trans hn)).trans ih
  exact le_of_tendsto airySt_tendsto_q (eventually_atTop.mpr ⟨N, hmono⟩)


/-- `u_N = p_N/(2^N N!)`. -/
theorem airySt_airyU_eq (N : ℕ) : airyU N = airySt_p N / (2 ^ N * N.factorial) := rfl

/-- `u_N > 0`. -/
theorem airySt_airyU_pos (N : ℕ) : 0 < airyU N := by
  rw [airySt_airyU_eq]; have := airySt_p_pos N; positivity

/-- `(N/(2e))^N ≤ √(2π(N + 1/6)) u_N` for `N ≤ 5`. -/
theorem airySt_gamma_ineq_small {N : ℕ} (hN : N ≤ 5) :
    ((N : ℝ) / (2 * Real.exp 1)) ^ N ≤ Real.sqrt (2 * π * (N + 1 / 6)) * airyU N := by
  have he := Real.exp_one_gt_d9
  have hπ := Real.pi_gt_d6
  have hu := airySt_airyU_pos N
  have h1 : ((N : ℝ) / (2 * Real.exp 1)) ^ N ≤ ((N : ℝ) / (2 * 2.7182818283)) ^ N :=
    pow_le_pow_left₀ (by positivity)
      (div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith)) N
  have h2 : Real.sqrt (2 * 3.141592 * (N + 1 / 6)) * airyU N ≤
      Real.sqrt (2 * π * (N + 1 / 6)) * airyU N :=
    mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (by gcongr)) hu.le
  refine h1.trans (le_trans ?_ h2)
  rw [← Real.sqrt_sq hu.le, ← Real.sqrt_mul (by positivity)]
  apply Real.le_sqrt_of_sq_le
  interval_cases N <;> norm_num [airyU, ascPochhammer_succ_eval, Nat.factorial]

/-- `(N/(2e))^N ≤ √(2π(N + 1/6)) u_N` for `N ≥ 6`. -/
theorem airySt_gamma_ineq_large {N : ℕ} (hN : 6 ≤ N) :
    ((N : ℝ) / (2 * Real.exp 1)) ^ N ≤ Real.sqrt (2 * π * (N + 1 / 6)) * airyU N := by
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  have hq := airySt_q_nonneg hN
  have hp := airySt_p_pos N
  rw [← Real.log_le_log_iff (by positivity) (by have := airySt_airyU_pos N; positivity),
    Real.log_pow, Real.log_div hN0.ne' (by positivity), Real.log_mul (by norm_num) (by positivity),
    Real.log_exp, Real.log_mul (by positivity) (airySt_airyU_pos N).ne',
    Real.log_sqrt (by positivity), airySt_airyU_eq, Real.log_div hp.ne' (by positivity),
    Real.log_mul (x := (2 : ℝ) ^ N) (by positivity) (by positivity), Real.log_pow]
  have e1 : Real.log (2 * π * ((N : ℝ) + 1 / 6)) =
      Real.log (2 * π) + Real.log ((N : ℝ) + 1 / 6) :=
    Real.log_mul (by positivity) (by positivity)
  simp only [airySt_q] at hq
  linarith

/-- **The sharp Gamma inequality** `(N/(2e))^N ≤ √(2π(N+1/6)) u_N` behind the last sector of
DLMF 9.7.17 (`max_Y Y^N e^{-2Y} = (N/(2e))^N`). -/
theorem airySt_gamma_ineq (N : ℕ) :
    ((N : ℝ) / (2 * Real.exp 1)) ^ N ≤ Real.sqrt (2 * π * (N + 1 / 6)) * airyU N := by
  rcases le_or_gt N 5 with h | h
  · exact airySt_gamma_ineq_small h
  · exact airySt_gamma_ineq_large h

/-! ### DLMF 9.7.17 for `Ai` on the closed rays and in the last sector

On `|arg z| = 2π/3` the `χ + 1` bound follows by continuity. For `2π/3 < |arg z| < π` the
connection formula 9.2.12 gives `R_N(z) = R_N(z₂) + κ e^{-2ζ(u)} F(u)` with `z = u e^{±2πi/3}`,
`z₂ = u e^{∓2πi/3}` and `|arg u| < π/3`; the last term is bounded through
`‖F(u)‖ ≤ cos(3/2 arg u)^{-1/6}` and the sharp Gamma inequality `airySt_gamma_ineq`. -/


/-- `‖F(u)‖ ≤ cos(3/2 arg u)^{-1/6}` for the normalized Ai on `|arg u| < π/3`. -/
theorem airySt_F_norm_le {u : ℂ} (hu : u ≠ 0) (harg : |arg u| < π / 3) :
    ‖airyAi u / airyPrefactor .ai u‖ ≤ Real.cos (3 / 2 * arg u) ^ (-(1 / 6 : ℝ)) := by
  have h0 : |(0 : ℝ)| < π := by simp [Real.pi_pos]
  have hab := abs_lt.mp harg
  have hzθ : |3 / 2 * arg u + 0| < π / 2 := by
    rw [add_zero, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)]; linarith
  rw [airySt_F_eq hu h0 hzθ]
  set ℓ := log 2 + airyLogZeta u with hℓ
  set V := exp (ℓ + ((0 : ℝ) : ℂ) * I) with hVdef
  have hc : 0 < Real.cos (3 / 2 * arg u) := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hVre : V.re = Real.exp ℓ.re * Real.cos (3 / 2 * arg u) := by
    rw [hVdef, airyRot_re_W]; simp [hℓ]
  have hV : 0 < V.re := by rw [hVre]; positivity
  have hL : ‖airyRot_lap (1 / 6) (-5 / 6) 0 V‖ ≤ Real.Gamma (1 / 6) * V.re ^ (-(1 / 6 : ℝ)) := by
    unfold airyRot_lap
    calc _ ≤ ∫ r in Ioi (0 : ℝ), r ^ ((1 / 6 : ℝ) - 1) * Real.exp (-(V.re * r)) := by
          refine norm_integral_le_of_norm_le (stRem_integrableOn_rpow_exp (by norm_num) hV) ?_
          refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun r hr => ?_)
          have hr : (0 : ℝ) < r := hr
          simp only [airyRot_kernel, ofReal_zero, zero_mul, Complex.exp_zero, mul_one]
          rw [norm_smul, norm_mul, norm_exp, show (1 : ℂ) + r = ((1 + r : ℝ) : ℂ) by push_cast; ring,
            norm_cpow_eq_rpow_re_of_pos hr, norm_cpow_eq_rpow_re_of_pos (by linarith)]
          have h1 : (1 + r) ^ (((-5 / 6 : ℝ) : ℂ)).re ≤ 1 := by
            simp only [ofReal_re]
            exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
          have hre : (-(V * r)).re = -(V.re * r) := by simp
          rw [hre]
          simp only [sub_re, ofReal_re, one_re]
          have := Real.rpow_nonneg hr.le ((1 / 6 : ℝ) - 1)
          calc Real.exp (-(V.re * r)) * (r ^ ((1 / 6 : ℝ) - 1) * (1 + r) ^ (-5 / 6 : ℝ))
              ≤ Real.exp (-(V.re * r)) * (r ^ ((1 / 6 : ℝ) - 1) * 1) := by
                gcongr; simpa using h1
            _ = _ := by ring
      _ = _ := airySt_gamma_int (by norm_num) hV
  have hG : ‖Gamma ((1 / 6 : ℝ) : ℂ)‖ = Real.Gamma (1 / 6) := by
    rw [Complex.Gamma_ofReal, Complex.norm_real,
      Real.norm_of_nonneg (Real.Gamma_pos_of_pos (by norm_num)).le]
  have hGp := Real.Gamma_pos_of_pos (show (0 : ℝ) < 1 / 6 by norm_num)
  rw [norm_mul, norm_mul, norm_mul, norm_div, norm_one, hG, ofReal_zero, zero_mul,
    Complex.exp_zero, norm_one, one_mul, norm_exp]
  have hre : ((1 / 6 : ℂ) * ℓ).re = ℓ.re / 6 := by simp; ring
  rw [hre]
  calc Real.exp (ℓ.re / 6) * (1 / Real.Gamma (1 / 6) * ‖airyRot_lap (1 / 6) (-5 / 6) 0 V‖)
      ≤ Real.exp (ℓ.re / 6) * (1 / Real.Gamma (1 / 6) *
          (Real.Gamma (1 / 6) * V.re ^ (-(1 / 6 : ℝ)))) := by gcongr
    _ = Real.exp (ℓ.re / 6) * V.re ^ (-(1 / 6 : ℝ)) := by field_simp
    _ = _ := by
      rw [hVre, Real.mul_rpow (Real.exp_pos _).le hc.le, ← Real.exp_mul, ← mul_assoc,
        ← Real.exp_add]
      ring_nf; simp

/-- `Ai(u) + ω Ai(u ω) + ω̄ Ai(u ω̄) = 0` with `ω = e^{±2πi/3}`. -/
theorem airySt_conn {u : ℂ} {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    airyAi u + exp (((ε * (2 * π / 3)) : ℝ) * I) * airyAi (u * exp (((ε * (2 * π / 3)) : ℝ) * I)) +
      exp ((((-ε) * (2 * π / 3)) : ℝ) * I) *
        airyAi (u * exp ((((-ε) * (2 * π / 3)) : ℝ) * I)) = 0 := by
  have h := airyAi_add_omega u
  have e1 : exp (((1 * (2 * π / 3)) : ℝ) * I) = exp (2 * π * I / 3) := by congr 1; push_cast; ring
  have e2 : exp ((((-1) * (2 * π / 3)) : ℝ) * I) = exp (-(2 * π * I / 3)) := by
    congr 1; push_cast; ring
  rcases hε with rfl | rfl
  · rw [e1, show (-(1 : ℝ)) = -1 by norm_num, e2]; linear_combination h
  · rw [e2, show (-(-1 : ℝ)) = 1 by norm_num, e1]; linear_combination h

/-- **The connection formula for the remainder** at `z = u e^{±2πi/3}`. -/
theorem airySt_third_rel {u : ℂ} (hu : u ≠ 0) (harg : |arg u| < π / 3) {ε : ℝ}
    (hε : ε = 1 ∨ ε = -1) (N : ℕ) :
    airyRemainder .ai N (u * exp (((ε * (2 * π / 3)) : ℝ) * I)) =
      airyRemainder .ai N (u * exp ((((-ε) * (2 * π / 3)) : ℝ) * I)) +
        (-exp ((((-ε) * (π / 2)) : ℝ) * I)) * exp (-(2 * airyZetaComplex u)) *
          (airyAi u / airyPrefactor .ai u) := by
  have hε' : -ε = 1 ∨ -ε = -1 := by rcases hε with rfl | rfl <;> norm_num
  have hz1 := airyRot_zeta_rot hu harg hε
  have hz2 := airyRot_zeta_rot hu harg hε'
  have hq1 := airyRot_quarter_rot hu harg hε
  have hq2 := airyRot_quarter_rot hu harg hε'
  have conn := airySt_conn (u := u) hε
  set E := exp (((ε * (π / 6)) : ℝ) * I) with hE
  have hE0 : E ≠ 0 := exp_ne_zero _
  have hpow : ∀ (c : ℝ) (n : ℕ), c = n * (ε * (π / 6)) → exp ((c : ℂ) * I) = E ^ n := by
    intro c n hc; rw [hE, ← exp_nat_mul]; congr 1; rw [hc]; push_cast; ring
  have hpowi : ∀ (c : ℝ) (n : ℕ), c = -(n * (ε * (π / 6))) → exp ((c : ℂ) * I) = (E ^ n)⁻¹ := by
    intro c n hc; rw [hE, ← exp_nat_mul, ← exp_neg]; congr 1; rw [hc]; push_cast; ring
  have hE6 : E ^ 6 = -1 := by
    rw [← hpow (ε * π) 6 (by push_cast; ring)]
    rcases hε with rfl | rfl
    · simp
    · rw [show (((-1 : ℝ) * π : ℝ) : ℂ) * I = -(π * I) by push_cast; ring, exp_neg, exp_pi_mul_I]
      norm_num
  simp only [airyRemainder, airyFunction, airyPrefactor, airyExponentialSum, hz1, hz2, hq1, hq2]
  generalize airyAi u = A0 at conn ⊢
  generalize airyAi (u * exp (((ε * (2 * π / 3)) : ℝ) * I)) = A1 at conn ⊢
  generalize airyAi (u * exp ((((-ε) * (2 * π / 3)) : ℝ) * I)) = A2 at conn ⊢
  rw [hpow (ε * (2 * π / 3)) 4 (by push_cast; ring),
    hpowi ((-ε) * (2 * π / 3)) 4 (by push_cast; ring)] at conn
  rw [hpowi ((-ε) * (π / 6)) 1 (by push_cast; ring), hpowi ((-ε) * (π / 2)) 3 (by push_cast; ring),
    pow_one]
  have hX0 : exp (airyZetaComplex u) ≠ 0 := exp_ne_zero _
  have hπ : (Real.sqrt π : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hq : u ^ (1 / 4 : ℂ) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hu)
  rw [neg_neg, show -(2 * airyZetaComplex u) = -airyZetaComplex u + -airyZetaComplex u by ring,
    exp_add, exp_neg]
  generalize exp (airyZetaComplex u) = X at *
  field_simp
  have hF : E ^ 4 * (E ^ 4)⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero _ hE0)
  generalize (E ^ 4)⁻¹ = F at conn hF
  linear_combination (2 * (Real.sqrt π : ℂ) * u ^ (1 / 4 : ℂ)) * conn +
    (-(2 * (Real.sqrt π : ℂ) * u ^ (1 / 4 : ℂ)) * A2 * F) * hE6 +
    (2 * (Real.sqrt π : ℂ) * u ^ (1 / 4 : ℂ) * A2 * E ^ 2) * hF

/-- `Y^N e^{-2Y} ≤ (N/(2e))^N` for `Y ≥ 0`. -/
theorem airySt_pow_exp_le {Y : ℝ} (hY : 0 ≤ Y) (N : ℕ) :
    Y ^ N * Real.exp (-(2 * Y)) ≤ ((N : ℝ) / (2 * Real.exp 1)) ^ N := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp only [pow_zero, one_mul, Real.exp_le_one_iff]; linarith
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  set x := 2 * Y / N with hx
  have hx0 : 0 ≤ x := by positivity
  have h1 : x * Real.exp (-x) ≤ Real.exp (-1) := by
    have := Real.add_one_le_exp (x - 1)
    have hx' : x ≤ Real.exp (x - 1) := by linarith
    calc x * Real.exp (-x) ≤ Real.exp (x - 1) * Real.exp (-x) :=
          mul_le_mul_of_nonneg_right hx' (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; ring_nf
  have h2 : Y * Real.exp (-(2 * Y) / N) ≤ N / (2 * Real.exp 1) := by
    have hY' : Y = N / 2 * x := by rw [hx]; field_simp
    have : -(2 * Y) / N = -x := by rw [hx]; ring
    rw [this, hY', mul_assoc]
    calc (N : ℝ) / 2 * (x * Real.exp (-x)) ≤ N / 2 * Real.exp (-1) := by gcongr
      _ = _ := by rw [Real.exp_neg]; field_simp
  calc Y ^ N * Real.exp (-(2 * Y)) = (Y * Real.exp (-(2 * Y) / N)) ^ N := by
        rw [mul_pow, ← Real.exp_nat_mul]; congr 2; field_simp
    _ ≤ _ := pow_le_pow_left₀ (by positivity) h2 N

/-- The last term of 9.7.17: `e^{-2ρc} c^{-1/6} ≤ √(2π m) c^{-m} u_N ρ^{-N}`, `m = N + 1/6`. -/
theorem airySt_third_term {ρ c : ℝ} (hρ : 0 < ρ) (hc : 0 < c) (N : ℕ) :
    Real.exp (-(2 * (ρ * c))) * c ^ (-(1 / 6 : ℝ)) ≤
      Real.sqrt (2 * π * (N + 1 / 6)) / c ^ ((N : ℝ) + 1 / 6) * (airyU N / ρ ^ N) := by
  have hK := (airySt_pow_exp_le (mul_pos hρ hc).le N).trans (airySt_gamma_ineq N)
  have hcm : c ^ ((N : ℝ) + 1 / 6) = c ^ N * c ^ (1 / 6 : ℝ) := by
    rw [Real.rpow_add hc, Real.rpow_natCast]
  rw [hcm, Real.rpow_neg hc.le, mul_pow] at *
  have h16 : 0 < c ^ (1 / 6 : ℝ) := Real.rpow_pos_of_pos hc _
  rw [div_mul_div_comm, le_div_iff₀ (by positivity)]
  calc Real.exp (-(2 * (ρ * c))) * (c ^ (1 / 6 : ℝ))⁻¹ * (c ^ N * c ^ (1 / 6 : ℝ) * ρ ^ N)
      = ρ ^ N * c ^ N * Real.exp (-(2 * (ρ * c))) := by field_simp
    _ ≤ _ := by linarith [hK]

/-- `ζ(w) ≠ 0` for `w ≠ 0`. -/
theorem airySt_zeta_ne_zero {w : ℂ} (hw : w ≠ 0) : airyZetaComplex w ≠ 0 := by
  intro h0
  have := exp_log_two_add_airyLogZeta hw
  rw [h0, mul_zero] at this
  exact exp_ne_zero _ this

/-- `Re (2ζ(u)) = 2 |ζ(u)| cos ((3/2) arg u)` for `u ≠ 0`. -/
private lemma airySt_re_two_zeta {u : ℂ} (hu0 : u ≠ 0) :
    (2 * airyZetaComplex u).re = 2 * (‖airyZetaComplex u‖ * Real.cos (3 / 2 * arg u)) := by
  have h := airyRot_re_W u 0
  simp only [ofReal_zero, zero_mul, add_zero] at h
  rw [exp_log_two_add_airyLogZeta hu0] at h
  have hn : Real.exp (log 2 + airyLogZeta u).re = ‖2 * airyZetaComplex u‖ := by
    rw [← Complex.norm_exp, exp_log_two_add_airyLogZeta hu0]
  rw [h, hn, norm_mul]; simp; ring

/-- **The third sector of 9.7.17**, `2π/3 < |arg z| < π`. -/
theorem airySt_ai_third {z : ℂ} (hz : z ≠ 0) (h1 : 2 * π / 3 < |arg z|) (h2 : |arg z| < π)
    (N : ℕ) :
    ‖airyRemainder .ai N z‖ ≤ (Real.sqrt (2 * π * (N + 1 / 6)) /
      |Real.cos (3 * arg z / 2)| ^ ((N : ℝ) + 1 / 6) + airyChi (N + 1 / 6) + 1) *
      ‖airyExpansionCoeff .ai N / airyZetaComplex z ^ N‖ := by
  have hπ := Real.pi_pos
  obtain ⟨ε, hε, hεarg⟩ : ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ arg z = |arg z| * ε := by
    rcases le_or_gt 0 (arg z) with h | h
    · exact ⟨1, Or.inl rfl, by rw [abs_of_nonneg h, mul_one]⟩
    · exact ⟨-1, Or.inr rfl, by rw [abs_of_neg h]; ring⟩
  have hε' : -ε = 1 ∨ -ε = -1 := by rcases hε with rfl | rfl <;> norm_num
  set u := z * exp ((((-ε) * (2 * π / 3)) : ℝ) * I) with hudef
  have hu0 : u ≠ 0 := mul_ne_zero hz (exp_ne_zero _)
  have hargu : arg u = arg z + (-ε) * (2 * π / 3) := by
    rw [hudef]
    apply Complex.arg_mul_exp_ofReal_mul_I hz <;> rcases hε with rfl | rfl <;> rw [hεarg]
        <;> nlinarith
  have hu : |arg u| < π / 3 := by
    rw [hargu, hεarg]; rcases hε with rfl | rfl <;> rw [abs_lt] <;> constructor <;> nlinarith
  have hzu : z = u * exp (((ε * (2 * π / 3)) : ℝ) * I) := by
    rw [hudef, mul_assoc, ← exp_add]
    rw [show (((-ε) * (2 * π / 3) : ℝ) : ℂ) * I + ((ε * (2 * π / 3) : ℝ) : ℂ) * I = 0 by
      push_cast; ring, exp_zero, mul_one]
  set z₂ := u * exp ((((-ε) * (2 * π / 3)) : ℝ) * I) with hz₂
  obtain ⟨b1, b2⟩ := airyRot_arg_rot_bounds hu hε'
  have hz₂0 : z₂ ≠ 0 := mul_ne_zero hu0 (exp_ne_zero _)
  have harg₂ : arg z₂ = arg u + (-ε) * (2 * π / 3) := Complex.arg_mul_exp_ofReal_mul_I hu0 b1 b2
  have hc : 0 < Real.cos (3 / 2 * arg u) := by
    have := abs_lt.mp hu
    exact Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hcz : |Real.cos (3 * arg z / 2)| = Real.cos (3 / 2 * arg u) := by
    have : 3 * arg z / 2 = 3 / 2 * arg u + ε * π := by rw [hargu]; ring
    rw [this]
    rcases hε with rfl | rfl
    · rw [one_mul, Real.cos_add_pi, abs_neg, abs_of_pos hc]
    · rw [neg_one_mul, ← sub_eq_add_neg, Real.cos_sub_pi, abs_neg, abs_of_pos hc]
  have hζ1 := airyRot_zeta_rot hu0 hu hε
  have hζ2 := airyRot_zeta_rot hu0 hu hε'
  have hT : ‖airyExpansionCoeff .ai N / airyZetaComplex z ^ N‖ =
      airyU N / ‖airyZetaComplex u‖ ^ N := by
    rw [hzu, hζ1]
    simp only [airyExpansionCoeff, norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow,
      one_mul, Complex.norm_real, Real.norm_of_nonneg (airySt_airyU_pos N).le]
  have hR₂ : ‖airyRemainder .ai N z₂‖ ≤ (airyChi (N + 1 / 6) + 1) *
      ‖airyExpansionCoeff .ai N / airyZetaComplex z ^ N‖ := by
    have hz2a : |arg z₂| < 2 * π / 3 := by
      rw [harg₂]; have := abs_lt.mp hu
      rcases hε with rfl | rfl <;> rw [abs_lt] <;> constructor <;> nlinarith
    have hsin : Real.sin (3 * arg z₂ / 2) ≠ 0 := by
      rw [harg₂, show 3 * (arg u + (-ε) * (2 * π / 3)) / 2 = 3 / 2 * arg u - ε * π by ring]
      rcases hε with rfl | rfl
      all_goals
        first
          | rw [one_mul, Real.sin_sub_pi]
          | rw [neg_one_mul, sub_neg_eq_add, Real.sin_add_pi]
        refine neg_ne_zero.mpr fun h0 => ?_
        have := abs_lt.mp hu
        rcases Real.sin_eq_zero_iff_of_lt_of_lt (by linarith) (by linarith) |>.mp h0 with h'
        have hargu0 : arg u = 0 := by linarith
        have := hargu; rw [hargu0, hεarg] at this
        nlinarith
    have := airySt_ai_le_chi hz₂0 hz2a hsin N
    rwa [hz₂, hζ2, ← hζ1, ← hzu] at this
  have hrel := airySt_third_rel hu0 hu hε N
  rw [← hzu, ← hz₂] at hrel
  rw [hrel]
  have hκ : ‖-exp ((((-ε) * (π / 2)) : ℝ) * I)‖ = 1 := by rw [norm_neg, norm_exp_ofReal_mul_I]
  have hF := airySt_F_norm_le hu0 hu
  have hre := airySt_re_two_zeta hu0
  have hρ : 0 < ‖airyZetaComplex u‖ := norm_pos_iff.mpr (airySt_zeta_ne_zero hu0)
  have h3 := airySt_third_term hρ hc N
  rw [hcz, hT]
  calc ‖airyRemainder .ai N z₂ + -exp ((((-ε) * (π / 2)) : ℝ) * I) *
        exp (-(2 * airyZetaComplex u)) * (airyAi u / airyPrefactor .ai u)‖
      ≤ ‖airyRemainder .ai N z₂‖ + Real.exp (-(2 * (‖airyZetaComplex u‖ *
          Real.cos (3 / 2 * arg u)))) * Real.cos (3 / 2 * arg u) ^ (-(1 / 6 : ℝ)) := by
        refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
        rw [norm_mul, norm_mul, hκ, one_mul, norm_exp, neg_re, hre]
        exact mul_le_mul_of_nonneg_left hF (Real.exp_pos _).le
    _ ≤ (airyChi (N + 1 / 6) + 1) * (airyU N / ‖airyZetaComplex u‖ ^ N) +
        Real.sqrt (2 * π * (N + 1 / 6)) / Real.cos (3 / 2 * arg u) ^ ((N : ℝ) + 1 / 6) *
          (airyU N / ‖airyZetaComplex u‖ ^ N) := by
        rw [hT] at hR₂; exact add_le_add hR₂ h3
    _ = _ := by ring

/-- The first neglected term `(-1)^N u_N ζ^{-N}` is continuous on the slit plane. -/
theorem airySt_continuousAt_T {w : ℂ} (hw : w ∈ slitPlane) (N : ℕ) :
    ContinuousAt (fun w => airyExpansionCoeff .ai N / airyZetaComplex w ^ N) w :=
  continuousAt_const.div ((airyRot_differentiableAt_zeta hw).continuousAt.pow N)
    (pow_ne_zero _ (airySt_zeta_ne_zero (slitPlane_ne_zero hw)))

/-- The normalized `Ai` remainder is continuous on the slit plane. -/
theorem airySt_continuousAt_rem {w : ℂ} (hw : w ∈ slitPlane) (N : ℕ) :
    ContinuousAt (airyRemainder .ai N) w := by
  have hw0 := slitPlane_ne_zero hw
  have hz := (airyRot_differentiableAt_zeta hw).continuousAt
  have hq : ContinuousAt (fun w : ℂ => w ^ (1 / 4 : ℂ)) w := continuousAt_cpow_const hw
  have hp : ContinuousAt (airyPrefactor .ai) w := by
    have he : airyPrefactor .ai =
        fun w => exp (-airyZetaComplex w) / (2 * Real.sqrt π * w ^ (1 / 4 : ℂ)) := by
      funext w; rfl
    rw [he]
    exact (hz.neg.cexp).div (continuousAt_const.mul hq)
      (mul_ne_zero (mul_ne_zero two_ne_zero
        (ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'))
        (cpow_ne_zero_iff.mpr (Or.inl hw0)))
  have hs : ContinuousAt (airyExponentialSum .ai N) w := by
    unfold airyExponentialSum
    exact tendsto_finsetSum _ fun k _ => airySt_continuousAt_T hw k
  unfold airyRemainder airyFunction
  exact (differentiable_airyAi.continuous.continuousAt.div hp
    (airyRot_prefactor_ne_zero .ai hw0)).sub hs

/-- `sin (3a/2) ≠ 0` for `π/3 < |a| < 2π/3`. -/
theorem airySt_sin_ne_zero {a : ℝ} (h1 : π / 3 < |a|) (h2 : |a| < 2 * π / 3) :
    Real.sin (3 * a / 2) ≠ 0 := by
  have hp : 0 < Real.sin (3 * |a| / 2) := Real.sin_pos_of_pos_of_lt_pi (by
    linarith [Real.pi_pos]) (by linarith)
  rcases le_or_gt 0 a with h | h
  · rw [abs_of_nonneg h] at hp; exact hp.ne'
  · rw [abs_of_neg h, show 3 * -a / 2 = -(3 * a / 2) by ring, Real.sin_neg] at hp; linarith

/-- `cos (3a/2) < 0` for `π/3 < |a| < 2π/3`. -/
theorem airySt_cos_neg {a : ℝ} (h1 : π / 3 < |a|) (h2 : |a| < 2 * π / 3) :
    Real.cos (3 / 2 * a) < 0 := by
  have hp : Real.cos (3 / 2 * |a|) < 0 :=
    Real.cos_neg_of_pi_div_two_lt_of_lt (by linarith) (by linarith [Real.pi_pos])
  rcases le_or_gt 0 a with h | h
  · rwa [abs_of_nonneg h] at hp
  · rwa [abs_of_neg h, mul_neg, Real.cos_neg] at hp

/-- The `χ + 1` bound on the rays `|arg z| = 2π/3`, by continuity. -/
theorem airySt_ai_boundary {z : ℂ} (hz : z ≠ 0) (harg : |arg z| = 2 * π / 3) (N : ℕ) :
    ‖airyRemainder .ai N z‖ ≤ (airyChi (N + 1 / 6) + 1) *
      ‖airyExpansionCoeff .ai N / airyZetaComplex z ^ N‖ := by
  have hπ := Real.pi_pos
  set p : ℝ → ℂ := fun φ => (‖z‖ : ℂ) * exp (φ * I) with hp
  have hpz : p (arg z) = z := norm_mul_exp_arg_mul_I z
  have hr : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hpc : Continuous p := by fun_prop
  have hzs : z ∈ slitPlane := by
    rw [mem_slitPlane_iff_arg]; refine ⟨fun h => ?_, hz⟩; rw [h, abs_of_pos hπ] at harg; linarith
  have hg := ((airySt_continuousAt_rem (hpz ▸ hzs) N).comp hpc.continuousAt).norm
  have hh := (((airySt_continuousAt_T (hpz ▸ hzs) N).comp hpc.continuousAt).norm).const_mul
    (airyChi (N + 1 / 6) + 1)
  have hb : ∀ φ : ℝ, π / 3 < |φ| → |φ| < 2 * π / 3 →
      ‖airyRemainder .ai N (p φ)‖ ≤ (airyChi (N + 1 / 6) + 1) *
        ‖airyExpansionCoeff .ai N / airyZetaComplex (p φ) ^ N‖ := by
    intro φ h1 h2
    have hφ : arg (p φ) = φ := airyRot_arg hr (by linarith [neg_abs_le φ])
      (by linarith [le_abs_self φ])
    have hp0 : p φ ≠ 0 := airyRot_ofReal_mul_exp_ne_zero hr φ
    exact airySt_ai_le_chi hp0 (by rw [hφ]; exact h2) (by rw [hφ]; exact airySt_sin_ne_zero h1 h2) N
  rw [← hpz]
  rcases le_or_gt 0 (arg z) with h0 | h0
  · rw [abs_of_nonneg h0] at harg
    have hev : ∀ᶠ φ in 𝓝[<] (arg z), φ ∈ Ioo (π / 3) (2 * π / 3) := by
      rw [harg]; exact Ioo_mem_nhdsLT (by linarith)
    refine le_of_tendsto_of_tendsto (hg.tendsto.mono_left nhdsWithin_le_nhds)
      (hh.tendsto.mono_left nhdsWithin_le_nhds) (hev.mono fun φ hφ => ?_)
    have : 0 < φ := by linarith [hφ.1]
    exact hb φ (by rw [abs_of_pos this]; exact hφ.1) (by rw [abs_of_pos this]; exact hφ.2)
  · rw [abs_of_neg h0] at harg
    have hev : ∀ᶠ φ in 𝓝[>] (arg z), φ ∈ Ioo (-(2 * π / 3)) (-(π / 3)) := by
      rw [show arg z = -(2 * π / 3) by linarith]; exact Ioo_mem_nhdsGT (by linarith)
    refine le_of_tendsto_of_tendsto (hg.tendsto.mono_left nhdsWithin_le_nhds)
      (hh.tendsto.mono_left nhdsWithin_le_nhds) (hev.mono fun φ hφ => ?_)
    have : φ < 0 := by linarith [hφ.2]
    exact hb φ (by rw [abs_of_neg this]; linarith [hφ.2]) (by rw [abs_of_neg this]; linarith [hφ.1])

/-- **The Bi remainder through 9.2.11**:
`R^{Bi}_N(x) = (R_N(x e^{2πi/3}) + R_N(x e^{-2πi/3}))/2`. -/
theorem airySt_bi_rem {x : ℝ} (hx : 0 < x) (N : ℕ) :
    airyRemainder .bi N x =
      (airyRemainder .ai N ((x : ℂ) * exp (((1 * (2 * π / 3)) : ℝ) * I)) +
        airyRemainder .ai N ((x : ℂ) * exp ((((-1) * (2 * π / 3)) : ℝ) * I))) / 2 := by
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have harg : |arg (x : ℂ)| < π / 3 := by
    rw [arg_ofReal_of_nonneg hx.le, abs_zero]; positivity
  have hz1 := airyRot_zeta_rot hx0 harg (Or.inl rfl)
  have hz2 := airyRot_zeta_rot hx0 harg (Or.inr rfl)
  have hq1 := airyRot_quarter_rot hx0 harg (Or.inl rfl)
  have hq2 := airyRot_quarter_rot hx0 harg (Or.inr rfl)
  have hB := airyBi_eq_airyAi_omega (x : ℂ)
  have e1 : exp (2 * π * I / 3) = exp (((1 * (2 * π / 3)) : ℝ) * I) := by congr 1; push_cast; ring
  have e2 : exp (-(2 * π * I / 3)) = exp ((((-1) * (2 * π / 3)) : ℝ) * I) := by
    congr 1; push_cast; ring
  set E := exp (((1 * (π / 6)) : ℝ) * I) with hE
  have e3 : exp (π * I / 6) = E := by rw [hE]; congr 1; push_cast; ring
  have e4 : exp (-(π * I / 6)) = E⁻¹ := by rw [hE, ← exp_neg]; congr 1; push_cast; ring
  have e5 : exp ((((-1) * (π / 6)) : ℝ) * I) = E⁻¹ := by rw [hE, ← exp_neg]; congr 1; push_cast; ring
  rw [e1, e2, e3, e4] at hB
  rw [e5] at hq2
  have hE0 : E ≠ 0 := exp_ne_zero _
  have hS : ∀ w : ℂ, airyZetaComplex w = -airyZetaComplex (x : ℂ) →
      airyExponentialSum .ai N w = airyExponentialSum .bi N x := by
    intro w hw
    unfold airyExponentialSum
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hw, airyExpansionCoeff, airyExpansionCoeff, neg_eq_neg_one_mul (airyZetaComplex (x : ℂ)),
      mul_pow]
    have : ((-1 : ℂ) ^ k) ≠ 0 := pow_ne_zero _ (by norm_num)
    have h2 : airyZetaComplex (x : ℂ) ^ k ≠ 0 := pow_ne_zero _ (airySt_zeta_ne_zero hx0)
    field_simp
  simp only [airyRemainder, airyFunction]
  rw [hS _ hz1, hS _ hz2, hB]
  simp only [airyPrefactor, hz1, hz2, hq1, hq2, neg_neg]
  have hX0 : exp (airyZetaComplex (x : ℂ)) ≠ 0 := exp_ne_zero _
  have hπ : (Real.sqrt π : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hq : (x : ℂ) ^ (1 / 4 : ℂ) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hx0)
  field_simp
  ring

/-- `‖e^{ζ}/(√π x^{1/4})‖ = e^{ζ(x)}/(√π x^{1/4})` for `x > 0`. -/
theorem airySt_norm_prefactor_bi {x : ℝ} (hx : 0 < x) :
    ‖airyPrefactor .bi x‖ = Real.exp (airyZeta x) / (Real.sqrt π * x ^ (1 / 4 : ℝ)) := by
  have hq : ‖(x : ℂ) ^ (1 / 4 : ℂ)‖ = x ^ (1 / 4 : ℝ) := by
    rw [show (1 / 4 : ℂ) = ((1 / 4 : ℝ) : ℂ) by push_cast; ring, ← ofReal_cpow hx.le,
      Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  rw [airyPrefactor, norm_div, norm_mul, hq, Complex.norm_exp, airyReal_zeta_ofReal hx, ofReal_re,
    Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]

/-- First-neglected-term remainder bound and its sign, DLMF §9.7(iii). -/
theorem airy_bi_real_error {x : ℝ} (hx : 0 < x) {N : ℕ} (hN : 0 ≤ N) :
    ‖airyRemainder .bi N x‖ ≤ (airyChi (N + 1 / 6) + 1) * 
      ‖airyExpansionCoeff .bi N / airyZetaComplex x ^ N‖ := by
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have harg : |arg (x : ℂ)| < π / 3 := by
    rw [arg_ofReal_of_nonneg hx.le, abs_zero]; positivity
  have hT : ∀ ε : ℝ, (ε = 1 ∨ ε = -1) →
      ‖airyRemainder .ai N ((x : ℂ) * exp (((ε * (2 * π / 3)) : ℝ) * I))‖ ≤
        (airyChi (N + 1 / 6) + 1) * ‖airyExpansionCoeff .bi N / airyZetaComplex x ^ N‖ := by
    intro ε hε
    have hw0 : (x : ℂ) * exp (((ε * (2 * π / 3)) : ℝ) * I) ≠ 0 :=
      airyRot_ofReal_mul_exp_ne_zero hx _
    have hwa : |arg ((x : ℂ) * exp (((ε * (2 * π / 3)) : ℝ) * I))| = 2 * π / 3 := by
      have hπ := Real.pi_pos
      rcases hε with rfl | rfl
      · rw [airyRot_arg hx (by linarith) (by linarith), one_mul, abs_of_pos (by positivity)]
      · rw [airyRot_arg hx (by linarith) (by linarith), abs_of_neg (by linarith)]; ring
    have h := airySt_ai_boundary hw0 hwa N
    rw [airyRot_zeta_rot hx0 harg hε] at h
    convert h using 2
    simp only [airyExpansionCoeff, norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow,
      one_mul]
  rw [airySt_bi_rem hx N]
  calc _ ≤ (‖airyRemainder .ai N ((x : ℂ) * exp (((1 * (2 * π / 3)) : ℝ) * I))‖ +
        ‖airyRemainder .ai N ((x : ℂ) * exp ((((-1) * (2 * π / 3)) : ℝ) * I))‖) / 2 := by
        rw [norm_div, Complex.norm_two]; gcongr; exact norm_add_le _ _
    _ ≤ _ := by linarith [hT 1 (Or.inl rfl), hT (-1) (Or.inr rfl)]

/-- First-neglected-term remainder bound and its sign, DLMF §9.7(iii). -/
theorem airy_biDeriv_real_error {x : ℝ} (hx : 0 < x) {N : ℕ} (hN : 1 ≤ N) :
    ‖airyRemainder .biDeriv N x‖ ≤ (airyChi (N + 0) + 1) * 
      ‖airyExpansionCoeff .biDeriv N / airyZetaComplex x ^ N‖ := by
  sorry

/-- For `x > 0`, `Ai(x) ≤ e^{-ζ}/(2√π x^{1/4})` (DLMF 9.7.15). -/
@[dlmf 9.7.E15]
theorem airy_ai_bound {x : ℝ} (hx : 0 < x) :
    airyAiReal x ≤ Real.exp (-airyZeta x) / (2 * Real.sqrt π * x ^ (1 / 4 : ℝ)) := by
  have h := (airyReal_pack (a := 5 / 6) (β := -1 / 6) (N := 0) (by norm_num) (by norm_num) hx
    (f := fun z => airyAi z / airyPrefactor .ai z) (airyReal_ai_repr hx) airyRot_coeff_ai).1
  simp only [Finset.range_zero, Finset.sum_empty, sub_zero, pow_zero, div_one,
    airyExpansionCoeff, airyReal_airyU_zero, ofReal_one, mul_one, norm_one] at h
  have hp : airyPrefactor .ai x ≠ 0 :=
    airyRot_prefactor_ne_zero .ai (ofReal_ne_zero.mpr hx.ne')
  calc airyAiReal x ≤ ‖airyAi x‖ := Complex.re_le_norm _
    _ = ‖airyPrefactor .ai x‖ * ‖airyAi x / airyPrefactor .ai x‖ := by
      rw [← norm_mul, mul_div_cancel₀ _ hp]
    _ ≤ ‖airyPrefactor .ai x‖ * 1 := by gcongr
    _ = _ := by rw [mul_one, airyReal_norm_prefactor_ai hx]

/-- For `x > 0`, `|Ai'(x)| ≤ x^{1/4} e^{-ζ}/(2√π) (1 + 7/(72ζ))` (DLMF 9.7.15). -/
@[dlmf 9.7.E15]
theorem airy_aiDeriv_bound {x : ℝ} (hx : 0 < x) :
    |airyAiDerivReal x| ≤ x ^ (1 / 4 : ℝ) * Real.exp (-airyZeta x) / (2 * Real.sqrt π) * (1 + 7 / (72 * airyZeta x)) := by
  have h := (airyReal_pack (a := 7 / 6) (β := 1 / 6) (N := 1) (by norm_num) (by norm_num) hx
    (f := fun z => airyAiDeriv z / airyPrefactor .aiDeriv z) (airyReal_aiDeriv_repr hx)
    airyRot_coeff_aiDeriv).1
  simp only [Finset.range_one, Finset.sum_singleton, pow_zero, div_one, pow_one,
    airyExpansionCoeff, airyReal_airyV_zero, airyReal_airyV_one, ofReal_one, mul_one] at h
  have hp : airyPrefactor .aiDeriv x ≠ 0 :=
    airyRot_prefactor_ne_zero .aiDeriv (ofReal_ne_zero.mpr hx.ne')
  have hz := airyZeta_pos hx
  have h1 : ‖airyAiDeriv x / airyPrefactor .aiDeriv x‖ ≤ 1 + 7 / (72 * airyZeta x) := by
    have h2 : ‖(-1 : ℂ) * ((-7 / 72 : ℝ) : ℂ) / airyZetaComplex x‖ = 7 / (72 * airyZeta x) := by
      have hz0 : (airyZeta x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hz.ne'
      rw [airyReal_zeta_ofReal hx, show (-1 : ℂ) * ((-7 / 72 : ℝ) : ℂ) / ((airyZeta x : ℝ) : ℂ) =
        ((7 / (72 * airyZeta x) : ℝ) : ℂ) by push_cast; field_simp,
        Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    rw [h2] at h
    calc ‖airyAiDeriv x / airyPrefactor .aiDeriv x‖
        = ‖(airyAiDeriv x / airyPrefactor .aiDeriv x - 1) + 1‖ := by ring_nf
      _ ≤ ‖airyAiDeriv x / airyPrefactor .aiDeriv x - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ ≤ 7 / (72 * airyZeta x) + 1 := by rw [norm_one]; gcongr
      _ = _ := by ring
  calc |airyAiDerivReal x| ≤ ‖airyAiDeriv x‖ := Complex.abs_re_le_norm _
    _ = ‖airyPrefactor .aiDeriv x‖ * ‖airyAiDeriv x / airyPrefactor .aiDeriv x‖ := by
      rw [← norm_mul, mul_div_cancel₀ _ hp]
    _ ≤ ‖airyPrefactor .aiDeriv x‖ * (1 + 7 / (72 * airyZeta x)) := by gcongr
    _ = _ := by rw [airyReal_norm_prefactor_aiDeriv hx]

/-- For `x > 0`, `Bi(x) ≤ e^{ζ}/(√π x^{1/4}) (1 + (χ(7/6) + 1) · 5/(72ζ))` (DLMF 9.7.16). -/
@[dlmf 9.7.E16]
theorem airy_bi_bound {x : ℝ} (hx : 0 < x) :
    airyBiReal x ≤ Real.exp (airyZeta x) / (Real.sqrt π * x ^ (1 / 4 : ℝ)) * (1 + (airyChi (7 / 6) + 1) * 5 / (72 * airyZeta x)) := by
  have h := airy_bi_real_error hx (N := 1) (Nat.zero_le _)
  have hz := airyZeta_pos hx
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have hp : airyPrefactor .bi x ≠ 0 := airyRot_prefactor_ne_zero .bi hx0
  have hT : ‖airyExpansionCoeff .bi 1 / airyZetaComplex x ^ 1‖ = 5 / (72 * airyZeta x) := by
    rw [airyExpansionCoeff, airyReal_airyU_one, pow_one, airyReal_zeta_ofReal hx, norm_div,
      Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg (by norm_num),
      Real.norm_of_nonneg hz.le]
    ring
  rw [hT, show ((1 : ℕ) : ℝ) + 1 / 6 = 7 / 6 by norm_num] at h
  have hS : airyExponentialSum .bi 1 x = 1 := by
    simp [airyExponentialSum, airyExpansionCoeff, airyReal_airyU_zero]
  have h1 : ‖airyBi x / airyPrefactor .bi x‖ ≤ 1 + (airyChi (7 / 6) + 1) * 5 / (72 * airyZeta x) := by
    have he : airyBi x / airyPrefactor .bi x = 1 + airyRemainder .bi 1 x := by
      rw [airyRemainder, airyFunction, hS]; ring
    rw [he]
    calc ‖1 + airyRemainder .bi 1 x‖ ≤ ‖(1 : ℂ)‖ + ‖airyRemainder .bi 1 x‖ := norm_add_le _ _
      _ ≤ 1 + (airyChi (7 / 6) + 1) * (5 / (72 * airyZeta x)) := by rw [norm_one]; gcongr
      _ = _ := by ring
  calc airyBiReal x ≤ ‖airyBi x‖ := Complex.re_le_norm _
    _ = ‖airyPrefactor .bi x‖ * ‖airyBi x / airyPrefactor .bi x‖ := by
      rw [← norm_mul, mul_div_cancel₀ _ hp]
    _ ≤ ‖airyPrefactor .bi x‖ * (1 + (airyChi (7 / 6) + 1) * 5 / (72 * airyZeta x)) := by gcongr
    _ = _ := by rw [airySt_norm_prefactor_bi hx]

/-- A linear upper bound for the Chi multiplier above one. -/
theorem airyDer_chi_le {s : ℝ} (hs : 1 ≤ s) : airyChi s ≤ π*s/2 := by
  have hs0 : 0 < s := by linarith
  have h1 := airySt_chi_integral hs0 (show (0:ℝ)<1 by norm_num)
  have h0 := airySt_chi_integral (show (0:ℝ)<1 by norm_num) (show (0:ℝ)<1 by norm_num)
  have hChi : airySt_chi 1 = π/2 := by
    unfold airySt_chi
    have hG : Real.Gamma (3/2:ℝ) = Real.sqrt π/2 := by
      rw [show (3/2:ℝ)=(1/2)+1 by norm_num, Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq]
      ring
    norm_num only
    rw [hG, Real.Gamma_one]
    nlinarith [Real.sq_sqrt Real.pi_pos.le]
  have hI : (∫ t : ℝ in Ioi 0, (1^2+t^2)^(-(s+1)/2)) ≤
      ∫ t : ℝ in Ioi 0, (1^2+t^2)^(-((1:ℝ)+1)/2) := by
    have hi : ∀ q : ℝ, 0 < q → IntegrableOn (fun t : ℝ => (1^2+t^2)^(-(q+1)/2)) (Ioi 0) := by
      intro q hq
      have hh := TauCeti.integrable_one_add_sq_rpow (s := (q+1)/2) (by linarith)
      have he : (fun t : ℝ => (1^2+t^2)^(-(q+1)/2)) =
          (fun t : ℝ => (1+t^2)^(-((q+1)/2))) := by
        funext t; congr 1 <;> ring
      rw [he]
      exact hh.integrableOn
    refine setIntegral_mono_on (hi s hs0) (hi 1 one_pos) measurableSet_Ioi fun t ht => ?_
    exact Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg t]) (by linarith)
  rw [hChi] at h0
  simp only [one_pow, Real.one_rpow, Real.Gamma_one, one_mul, mul_one] at h0 h1 hI
  rw [Real.Gamma_add_one hs0.ne'] at h1
  change s*Real.Gamma s * _ = Real.Gamma s * airyChi s at h1
  have hGs := Real.Gamma_pos_of_pos hs0
  have hG2 : Real.Gamma ((1:ℝ)+1)=1 := by norm_num [Real.Gamma_add_one]
  rw [hG2, one_mul] at h0
  rw [h0] at hI
  have he : airyChi s = s * ∫ t : ℝ in Ioi 0, (1+t^2)^(-(s+1)/2) := by
    apply (mul_left_cancel₀ hGs.ne')
    linear_combination -h1
  rw [he]
  nlinarith [mul_le_mul_of_nonneg_left hI hs0.le]

/-- A coarse Gamma bound used only for the derivative's real-axis estimate. -/
theorem airyDer_Gamma_third : (5/2:ℝ) ≤ Real.Gamma (1/3) := by
  have hG : 0 < Real.Gamma (1/3:ℝ) := Real.Gamma_pos_of_pos (by norm_num)
  have hrec : Real.Gamma (4/3:ℝ) = Real.Gamma (1/3)/3 := by
    rw [show (4/3:ℝ)=(1/3)+1 by norm_num, Real.Gamma_add_one (by norm_num)]
    ring
  have hbin := DLMF.Gamma.log_Gamma_eq_add_binetIntegral (x := (4/3:ℝ)) (by norm_num)
  have hbin0 := (DLMF.Gamma.binetIntegral_mem (x := (4/3:ℝ)) (by norm_num)).1
  rw [hrec, Real.log_div hG.ne' (by norm_num)] at hbin
  have hlog : 6*Real.log 3 + 5*Real.log (4/3:ℝ) + 3*Real.log (2*π) - 8 ≤
      6*Real.log (Real.Gamma (1/3:ℝ)) := by linarith
  have hexp := Real.exp_le_exp.mpr hlog
  have heq : Real.exp (6*Real.log 3 + 5*Real.log (4/3:ℝ) + 3*Real.log (2*π) - 8) =
      24576*π^3/Real.exp 8 := by
    rw [Real.exp_sub, Real.exp_add, Real.exp_add,
      show 6*Real.log 3 = (6:ℕ)*Real.log 3 by norm_num,
      show 5*Real.log (4/3:ℝ) = (5:ℕ)*Real.log (4/3:ℝ) by norm_num,
      show 3*Real.log (2*π) = (3:ℕ)*Real.log (2*π) by norm_num,
      Real.exp_nat_mul, Real.exp_nat_mul, Real.exp_nat_mul,
      Real.exp_log (by norm_num), Real.exp_log (by norm_num), Real.exp_log (by positivity)]
    ring
  rw [heq, show 6*Real.log (Real.Gamma (1/3:ℝ)) = (6:ℕ)*Real.log (Real.Gamma (1/3:ℝ)) by norm_num,
    Real.exp_nat_mul, Real.exp_log hG] at hexp
  have he : Real.exp 8 ≤ (49/18:ℝ)^8 := by
    rw [show (8:ℝ)=(8:ℕ)*1 by norm_num, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (Real.exp_pos _).le (by linarith [Real.exp_one_lt_d9]) _
  have hpi : (25/8:ℝ)^3 ≤ π^3 := pow_le_pow_left₀ (by norm_num) (by linarith [Real.pi_gt_d6]) _
  rw [div_le_iff₀ (Real.exp_pos _)] at hexp
  by_contra h
  have hlt : Real.Gamma (1/3:ℝ)^6 < (5/2:ℝ)^6 :=
    pow_lt_pow_left₀ (not_le.mp h) hG.le (by omega)
  have hh := mul_le_mul_of_nonneg_left he (pow_nonneg hG.le 6)
  nlinarith

/-- The Airy energy on the positive axis is bounded by its initial value. -/
theorem airyDer_energy {x : ℝ} (hx : 0 ≤ x) :
    airyBiDerivReal x^2 ≤ x*airyBiReal x^2 + airyBiDerivReal 0^2 := by
  have hf (t : ℝ) : HasDerivAt airyBiReal (airyBiDerivReal t) t :=
    (hasDerivAt_airyBi t).real_of_complex
  have hg (t : ℝ) : HasDerivAt airyBiDerivReal (t*airyBiReal t) t := by
    exact ((hasDerivAt_airyBiDeriv t).real_of_complex).congr_deriv (by simp [airyBiReal])
  have hd (t : ℝ) : HasDerivAt (fun t => airyBiDerivReal t^2-t*airyBiReal t^2)
      (-airyBiReal t^2) t := by
    convert ((hg t).pow 2).sub ((hasDerivAt_id t).mul ((hf t).pow 2)) using 1
    · funext u; rfl
    · simp only [Pi.pow_apply, id_eq]; ring
  have hm := antitone_of_deriv_nonpos (fun t => (hd t).differentiableAt)
    (fun t => by rw [(hd t).deriv]; exact neg_nonpos.mpr (sq_nonneg _))
  have h := hm hx
  simp only [zero_mul, sub_zero] at h
  linarith

/-- A coarse bound on the initial derivative. -/
theorem airyDer_initial_sq : airyBiDerivReal 0^2 ≤ (52/225:ℝ) := by
  have hG := airyDer_Gamma_third
  have hG0 := Real.Gamma_pos_of_pos (show (0:ℝ)<1/3 by norm_num)
  have hr : ((3:ℝ)^(1/3:ℝ))^3 = 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  have hroot : (3:ℝ)^(1/3:ℝ) ≤ 13/9 := by
    apply (pow_le_pow_iff_left₀ (Real.rpow_nonneg (by norm_num) _) (by norm_num) (by omega : 3≠0)).mp
    rw [hr]; norm_num
  have hq : ((3:ℝ)^(1/6:ℝ))^2 = (3:ℝ)^(1/3:ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; congr 1; norm_num
  have hz : airyBiDerivReal 0 = (3:ℝ)^(1/6:ℝ)/Real.Gamma (1/3) := by
    rw [airyBiDerivReal, ofReal_zero, airyBiDeriv_zero,
      show (1/3:ℂ)=((1/3:ℝ):ℂ) by norm_num, Complex.Gamma_ofReal, ← ofReal_div, ofReal_re]
  rw [hz, div_pow, hq, div_le_iff₀ (pow_pos hG0 2)]
  nlinarith

/-- Real power identities in the Airy saddle variable. -/
theorem airyDer_power_data {x : ℝ} (hx : 0 < x) :
    airyZeta x=2/3*(Real.sqrt x)^3 ∧ (x^(1/4:ℝ))^2=Real.sqrt x := by
  constructor
  · rw [airyZeta, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hx.le]
    congr 2; norm_num
  · rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hx.le]
    congr 1; norm_num

/-- A polynomial certificate for the elementary exponential envelope. -/
theorem airyDer_envelope_poly {u : ℝ} (hu : 0 ≤ u) :
    (181/2916:ℝ)*u^12 +
      (2155529/13436928:ℝ)*u^9 +
      (1529993/5971968:ℝ)*u^6 +
      (-1144/1575:ℝ)*u^5 +
      (904457/3981312:ℝ)*u^3 +
      (278921/5308416:ℝ) ≥ 0 := by
  by_cases hsmall : u ≤ 1/2
  · have hu3 : 0 ≤ u^3 := pow_nonneg hu 3
    have hu2 : u^2 ≤ (1/4:ℝ) := by nlinarith
    have hu5 : u^5 ≤ u^3/4 := by nlinarith [mul_le_mul_of_nonneg_left hu2 hu3]
    nlinarith [pow_nonneg hu 6, pow_nonneg hu 9, pow_nonneg hu 12]
  · have hu1 : (1/2:ℝ) ≤ u := le_of_lt (not_le.mp hsmall)
    let Q : ℝ := (181/2916:ℝ)*u^10 +
      (1991/17496:ℝ)*u^9 +
      (21901/139968:ℝ)*u^8 +
      (14175739/40310784:ℝ)*u^7 +
      (124132877/241864704:ℝ)*u^6 +
      (1248860723/1934917632:ℝ)*u^5 +
      (17557622459/17414258688:ℝ)*u^4 +
      (84803311431641/146279772979200:ℝ)*u^3 +
      (21030123845489/97519848652800:ℝ)*u^2 +
      (2852020772397883/21064287309004800:ℝ)*u +
      (1058802953579899/15798215481753600:ℝ)
    have hq : 0 ≤ Q := by dsimp only [Q]; positivity
    have hrem : 0 ≤ (1840275079998707/202217158166446080:ℝ)*u + (-8582440901337379/2274943029372518400:ℝ) := by linarith
    have he : (181/2916:ℝ)*u^12 +
      (2155529/13436928:ℝ)*u^9 +
      (1529993/5971968:ℝ)*u^6 +
      (-1144/1575:ℝ)*u^5 +
      (904457/3981312:ℝ)*u^3 +
      (278921/5308416:ℝ) =
        (u-11/12)^2*Q+((1840275079998707/202217158166446080:ℝ)*u + (-8582440901337379/2274943029372518400:ℝ)) := by dsimp only [Q]; ring
    rw [he]
    positivity

/-- An elementary gap between two positive exponential envelopes. -/
theorem airyDer_envelope_gap {x : ℝ} (hx : 0 < x) :
    (52/225:ℝ) ≤ Real.exp (2*airyZeta x)*Real.sqrt x/π *
      ((1+(287/1152:ℝ)/airyZeta x)^2-(1+(85/432:ℝ)/airyZeta x)^2) := by
  set u := Real.sqrt x with huDef
  have hu : 0 < u := Real.sqrt_pos.mpr hx
  have hz := (airyDer_power_data hx).1
  set z := airyZeta x with hzDef
  have hz0 : 0 < z := airyZeta_pos hx
  have hzEq : z=2/3*u^3 := hz
  set T : ℝ := 1+2*z+2*z^2+4*z^3/3
  set D : ℝ := (1+(287/1152:ℝ)/z)^2-(1+(85/432:ℝ)/z)^2
  have hD : 0 ≤ D := by
    have hh : 0 ≤ 1+(85/432:ℝ)/z := by positivity
    have hle : 1+(85/432:ℝ)/z ≤ 1+(287/1152:ℝ)/z := by
      have hh : (85/432:ℝ)/z ≤ (287/1152:ℝ)/z :=
        div_le_div_of_nonneg_right (by norm_num) hz0.le
      linarith
    dsimp only [D]
    nlinarith
  have hT : T ≤ Real.exp (2*z) := by
    have h := Real.sum_le_exp_of_nonneg (by positivity : 0 ≤ 2*z) 4
    norm_num [Finset.sum_range_succ] at h
    dsimp only [T]
    nlinarith
  have hpoly := airyDer_envelope_poly hu.le
  have he : T*u*D-(22/7:ℝ)*(52/225) = ((181/2916:ℝ)*u^12+(2155529/13436928:ℝ)*u^9+(1529993/5971968:ℝ)*u^6+(-1144/1575:ℝ)*u^5+(904457/3981312:ℝ)*u^3+(278921/5308416:ℝ))/u^5 := by
    dsimp only [T,D]
    rw [hzEq]
    field_simp
    ring
  have hmain : (22/7:ℝ)*(52/225) ≤ T*u*D := by
    rw [← sub_nonneg, he]
    exact div_nonneg hpoly (pow_nonneg hu.le 5)
  change (52/225:ℝ) ≤ Real.exp (2*z)*u/π*D
  rw [div_mul_eq_mul_div, le_div_iff₀ Real.pi_pos]
  calc (52/225:ℝ)*π ≤ (22/7:ℝ)*(52/225) := by nlinarith [Real.pi_lt_d6]
    _ ≤ T*u*D := hmain
    _ ≤ Real.exp (2*z)*u*D := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hT hu.le) hD



/-- The real-axis Bi derivative bound, DLMF 9.7.16. -/
@[dlmf 9.7.E16]
theorem airy_biDeriv_bound {x : ℝ} (hx : 0 < x) :
    airyBiDerivReal x ≤ x^(1/4:ℝ)*Real.exp (airyZeta x)/Real.sqrt π *
      (1+(π/2+1)*7/(72*airyZeta x)) := by
  have hz := airyZeta_pos hx
  have hπ := Real.pi_pos
  have hq : 0 < x^(1/4:ℝ) := Real.rpow_pos_of_pos hx _
  have hS := Real.sqrt_pos.mpr hπ
  have hc : (airyChi (7/6)+1)*5/72 ≤ (85/432:ℝ) := by
    have h := airyDer_chi_le (s := (7/6:ℝ)) (by norm_num)
    have hp : π ≤ (22/7:ℝ) := by linarith [Real.pi_lt_d6]
    nlinarith
  have hA : (287/1152:ℝ) ≤ (π/2+1)*7/72 := by linarith [Real.pi_gt_d6]
  set P := x^(1/4:ℝ)*Real.exp (airyZeta x)/Real.sqrt π
  set B := Real.exp (airyZeta x)/(Real.sqrt π*x^(1/4:ℝ)) *
    (1+(85/432:ℝ)/airyZeta x)
  have hP0 : 0 < P := by dsimp [P]; positivity
  have hB0 : 0 < B := by dsimp [B]; positivity
  have hB : airyBiReal x ≤ B := by
    have h := airy_bi_bound hx
    have he : (airyChi (7/6)+1)*5/(72*airyZeta x) =
        ((airyChi (7/6)+1)*5/72)/airyZeta x := by ring
    rw [he] at h
    refine h.trans ?_
    dsimp only [B]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    linarith [div_le_div_of_nonneg_right hc hz.le]
  have hBi0 : 0 ≤ airyBiReal x := by
    obtain ⟨r, hr, he⟩ := airyBi_ofReal_pos hx.le
    simpa [airyBiReal, he] using hr.le
  have hBiSq : airyBiReal x^2 ≤ B^2 := by nlinarith
  have hq4 : (x^(1/4:ℝ))^4=x := by
    calc (x^(1/4:ℝ))^4 = ((x^(1/4:ℝ))^2)^2 := by ring
      _ = x := by rw [(airyDer_power_data hx).2, Real.sq_sqrt hx.le]
  have hbase : x*(Real.exp (airyZeta x)/(Real.sqrt π*x^(1/4:ℝ)))^2=P^2 := by
    dsimp only [P]
    nth_rw 1 [← hq4]
    field_simp
  have hBsq : x*B^2 = P^2*(1+(85/432:ℝ)/airyZeta x)^2 := by
    dsimp only [B]
    rw [mul_pow, ← mul_assoc, hbase]
  have hPsq : P^2=Real.exp (2*airyZeta x)*Real.sqrt x/π := by
    dsimp only [P]
    rw [div_pow, mul_pow, (airyDer_power_data hx).2, Real.sq_sqrt hπ.le,
      ← Real.exp_nat_mul]
    norm_num only
    ring
  have hgap := airyDer_envelope_gap hx
  rw [← hPsq] at hgap
  have hsquares : airyBiDerivReal x^2 ≤ (P*(1+(287/1152:ℝ)/airyZeta x))^2 := by
    have henergy := airyDer_energy hx.le
    have hzero := airyDer_initial_sq
    have hBB := mul_le_mul_of_nonneg_left hBiSq hx.le
    rw [hBsq] at hBB
    nlinarith
  have hR0 : 0 ≤ P*(1+(287/1152:ℝ)/airyZeta x) := by positivity
  have hresult : airyBiDerivReal x ≤ P*(1+(287/1152:ℝ)/airyZeta x) := by nlinarith
  refine hresult.trans ?_
  change P*(1+(287/1152:ℝ)/airyZeta x) ≤ P*(1+(π/2+1)*7/(72*airyZeta x))
  have he : (π/2+1)*7/(72*airyZeta x) = ((π/2+1)*7/72)/airyZeta x := by ring
  rw [he]
  apply mul_le_mul_of_nonneg_left _ hP0.le
  linarith [div_le_div_of_nonneg_right hA hz.le]


/-- On the slit plane the remainder of the normalized `Ai` expansion is bounded by the error
multiplier times the first neglected term (DLMF 9.7.17). -/
@[dlmf 9.7.E17]
theorem airy_ai_complex_error {z : ℂ} (hz : z ∈ slitPlane) {N : ℕ} (hN : 0 ≤ N) :
    ‖airyRemainder .ai N z‖ ≤ airyErrorMultiplier N (1 / 6) z *
      ‖airyExpansionCoeff .ai N / airyZetaComplex z ^ N‖ := by
  have hπ := Real.pi_pos
  have hz0 := slitPlane_ne_zero hz
  have hlt : |arg z| < π := by
    rw [mem_slitPlane_iff_arg] at hz
    exact lt_of_le_of_ne (abs_le.mpr ⟨(neg_pi_lt_arg z).le, arg_le_pi z⟩) (fun h => by
      rcases abs_eq hπ.le |>.mp h with h' | h'
      · exact hz.1 h'
      · linarith [neg_pi_lt_arg z])
  unfold airyErrorMultiplier
  split_ifs with h1 h2 h3
  · have hM : airySt_M (-(3 / 2 * arg z)) = 1 := by
      unfold airySt_M
      rw [Real.cos_neg]
      split_ifs with hc
      · rfl
      · exact absurd (Real.cos_nonneg_of_mem_Icc ⟨by linarith [abs_le.mp h1],
          by linarith [abs_le.mp h1]⟩) hc
    have := airySt_ai_le_M hz0 (by linarith) N
    rwa [hM] at this
  · rcases lt_or_eq_of_le h2 with h | h
    · exact absurd h3 (airySt_sin_ne_zero (lt_of_not_ge h1) h)
    · exact airySt_ai_boundary hz0 h N
  · rcases lt_or_eq_of_le h2 with h | h
    · have hM : airySt_M (-(3 / 2 * arg z)) = |(Real.sin (3 * arg z / 2))⁻¹| := by
        unfold airySt_M
        rw [Real.cos_neg]
        split_ifs with hc
        · exact absurd hc (not_le.mpr (airySt_cos_neg (lt_of_not_ge h1) h))
        · rw [Real.sin_neg, abs_neg, abs_inv, show 3 / 2 * arg z = 3 * arg z / 2 by ring]
      have hA := airySt_ai_le_M hz0 h N
      have hB := airySt_ai_le_chi hz0 h h3 N
      rw [hM] at hA
      rw [min_mul_of_nonneg _ _ (norm_nonneg _)]
      exact le_min hA hB
    · exfalso; apply h3
      rcases le_or_gt 0 (arg z) with h0 | h0
      · rw [abs_of_nonneg h0] at h; rw [h, show 3 * (2 * π / 3) / 2 = π by ring, Real.sin_pi]
      · rw [abs_of_neg h0] at h
        rw [show arg z = -(2 * π / 3) by linarith, show 3 * -(2 * π / 3) / 2 = -π by ring,
          Real.sin_neg, Real.sin_pi, neg_zero]
  · exact airySt_ai_third hz0 (lt_of_not_ge h2) hlt N

/-- On the slit plane, for `N ≥ 1`, the remainder of the normalized `Ai'` expansion is bounded
by the error multiplier times the first neglected term (DLMF 9.7.17). -/
@[dlmf 9.7.E17]
theorem airy_aiDeriv_complex_error {z : ℂ} (hz : z ∈ slitPlane) {N : ℕ} (hN : 1 ≤ N) :
    ‖airyRemainder .aiDeriv N z‖ ≤ airyErrorMultiplier N (0) z *
      ‖airyExpansionCoeff .aiDeriv N / airyZetaComplex z ^ N‖ := by
  sorry

/-- `Ai(z)` is its prefactor times the truncated series plus the exact remainder
(DLMF 9.7.18). -/
@[dlmf 9.7.E18]
theorem airy_ai_exact_remainder {z : ℂ} (hz : z ≠ 0) (N : ℕ) :
    airyFunction .ai z = airyPrefactor .ai z *
      (airyExponentialSum .ai N z + airyRemainder .ai N z) := by
  have hp : airyPrefactor .ai z ≠ 0 := by
    dsimp only [airyPrefactor]
    have hπ : (Real.sqrt π : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
    have hz' : z ^ (1 / 4 : ℂ) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hz)
    exact div_ne_zero (exp_ne_zero _) (mul_ne_zero (mul_ne_zero two_ne_zero hπ) hz')
  unfold airyRemainder
  field_simp
  ring

/-- `Ai'(z)` is its prefactor times the truncated series plus the exact remainder
(DLMF 9.7.19). -/
@[dlmf 9.7.E19]
theorem airy_aiDeriv_exact_remainder {z : ℂ} (hz : z ≠ 0) (N : ℕ) :
    airyFunction .aiDeriv z = airyPrefactor .aiDeriv z *
      (airyExponentialSum .aiDeriv N z + airyRemainder .aiDeriv N z) := by
  have hp : airyPrefactor .aiDeriv z ≠ 0 := by
    dsimp only [airyPrefactor]
    have hπ : (Real.sqrt π : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
    have hz' : z ^ (1 / 4 : ℂ) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hz)
    exact div_ne_zero (mul_ne_zero (neg_ne_zero.mpr hz') (exp_ne_zero _)) (mul_ne_zero two_ne_zero hπ)
  unfold airyRemainder
  field_simp
  ring

/-- Re-expansion of the `Ai` remainder in terminants `F_{n-k}(2ζ)` with second-level
remainder `airyHyperRemainder` (DLMF 9.7.20). -/
@[dlmf 9.7.E20]
theorem airy_R_hyper_reexpansion (m n : ℕ) (z : ℂ) :
    airyRemainder .ai n z =
      (-1 : ℂ) ^ (n) *
        (∑ k ∈ Finset.range m, (-1 : ℂ) ^ k * (airyU k : ℂ) *
          airyTerminator ((n : ℂ) - k) (log 2 + airyLogZeta z) / airyZetaComplex z ^ k) +
      airyHyperRemainder false m n z := by
  norm_num [airyHyperRemainder]

/-- Re-expansion of the `Ai'` remainder in terminants `F_{n-k}(2ζ)` with second-level
remainder `airyHyperRemainder` (DLMF 9.7.21). -/
@[dlmf 9.7.E21]
theorem airy_S_hyper_reexpansion (m n : ℕ) (z : ℂ) :
    airyRemainder .aiDeriv n z =
      (-1 : ℂ) ^ (n - 1) *
        (∑ k ∈ Finset.range m, (-1 : ℂ) ^ k * (airyV k : ℂ) *
          airyTerminator ((n : ℂ) - k) (log 2 + airyLogZeta z) / airyZetaComplex z ^ k) +
      airyHyperRemainder true m n z := by
  norm_num [airyHyperRemainder]

/-- At the optimal index `n ≈ 2|ζ|` the second-level `Ai` remainder is
`O(e^{-2|ζ|} |ζ|^{-m})` in `|arg z| ≤ 2π/3` (DLMF 9.7.23). -/
@[dlmf 9.7.E23]
theorem airy_R_hyper_error (m : ℕ) :
    IsBigO (airySector (2 * π / 3)) (fun z => airyHyperRemainder false m (airyOptimalIndex z) z)
      (fun z => Real.exp (-2 * ‖airyZetaComplex z‖) * ‖airyZetaComplex z‖ ^ (-(m : ℤ))) := by
  sorry

/-- At the optimal index `n ≈ 2|ζ|` the second-level `Ai'` remainder is
`O(e^{-2|ζ|} |ζ|^{-m})` in `|arg z| ≤ 2π/3` (DLMF 9.7.23). -/
@[dlmf 9.7.E23]
theorem airy_S_hyper_error (m : ℕ) :
    IsBigO (airySector (2 * π / 3)) (fun z => airyHyperRemainder true m (airyOptimalIndex z) z)
      (fun z => Real.exp (-2 * ‖airyZetaComplex z‖) * ‖airyZetaComplex z‖ ^ (-(m : ℤ))) := by
  sorry

/-- The exact even/odd coefficients obtained by inverting the real sine/cosine system. -/
def airyOscComponent (derivative : Bool) (parity : Fin 2) (x : ℝ) : ℂ :=
  let θ : ℂ := airyZeta x - π / 4
  let pref := airyOscPrefactor (if derivative then .aiDeriv else .ai) x
  if derivative then
    if parity.val = 0 then (sin θ * airyAiDeriv (-x) + cos θ * airyBiDeriv (-x)) / pref
    else (-cos θ * airyAiDeriv (-x) + sin θ * airyBiDeriv (-x)) / pref
  else
    if parity.val = 0 then (cos θ * airyAi (-x) - sin θ * airyBi (-x)) / pref
    else (sin θ * airyAi (-x) + cos θ * airyBi (-x)) / pref

/-! ### Signed bounds for the oscillatory subseries on the negative axis (DLMF §9.7(iii))

On the rays `arg w = ±π/3` the Stieltjes ray of the normalized `Ai` (σ = 1/6 form) and of the
normalized `Ai'` (kernel `t^{1/6}(1+t)^{1/6}`, whose binomial remainder is again a Stieltjes
transform with a nonnegative weight) is `θ = ∓π/2`, where `Re (1 + s e^{iθ})⁻¹ ∈ [0, 1]`. Hence the
remainder after `M` terms is `(A + iB)` times the first neglected term with `0 ≤ A ≤ 1`
(`airyDer_ray_ratio`). The even and odd parts `(F₊ ± F₋)/2`, `(F₊ - F₋)/(2i)` of the normalized
function at `x e^{±iπ/3}` are the real components of 9.7.9–9.7.12 (`airyDer_comp_false`,
`airyDer_comp_true`); their truncation errors are real and equal to `Ā` times the first
neglected term, which gives the bound together with its sign. Helper names carry the prefix
`airyDer_`. -/
theorem airyDer_re_recip_mem {θ : ℝ} (hθ : 0 ≤ Real.cos θ) {s : ℝ} (hs : 0 ≤ s) :
    0 ≤ ((1 + (s : ℂ) * exp (θ * I))⁻¹).re ∧ ((1 + (s : ℂ) * exp (θ * I))⁻¹).re ≤ 1 := by
  set w := 1 + (s : ℂ) * exp (θ * I) with hw
  have hre : w.re = 1 + s * Real.cos θ := by simp [hw, exp_ofReal_mul_I_re]
  have h1 : 1 ≤ w.re := by rw [hre]; nlinarith
  have hns : 0 < normSq w := by rw [normSq_apply]; nlinarith [mul_self_nonneg w.im]
  rw [inv_re]
  refine ⟨div_nonneg (by linarith) hns.le, (div_le_one hns).mpr ?_⟩
  rw [normSq_apply]; nlinarith [mul_self_nonneg w.im]

/-- `‖(1 + s e^{iθ})⁻¹‖ ≤ 1` when `cos θ ≥ 0` and `s ≥ 0`. -/
theorem airyDer_norm_recip_le {θ : ℝ} (hθ : 0 ≤ Real.cos θ) {s : ℝ} (hs : 0 ≤ s) :
    ‖(1 + (s : ℂ) * exp (θ * I))⁻¹‖ ≤ 1 := by
  rw [norm_inv]; exact inv_le_one_of_one_le₀ (Complex.one_le_norm_one_add_ofReal_mul_exp hs hθ)

/-- `1 + (r e^{iθ}) τ = 1 + (r τ) e^{iθ}`. -/
theorem airyDer_one_add_eq (θ r τ : ℝ) :
    1 + ((r : ℂ) * exp (θ * I)) * τ = 1 + ((r * τ : ℝ) : ℂ) * exp (θ * I) := by
  push_cast; ring

/-- For integrable real `g` on `(0,1)` and `cos θ ≥ 0`, `g(τ)/(1 + r e^{iθ} τ)` is integrable. -/
theorem airyDer_integrableOn_inner {g : ℝ → ℝ} (hgm : Measurable g) (hgi : IntegrableOn g (Ioo 0 1))
    {θ : ℝ} (hcos : 0 ≤ Real.cos θ) {r : ℝ} (hr : 0 ≤ r) :
    IntegrableOn (fun τ : ℝ => (g τ : ℂ) * (1 + ((r : ℂ) * exp (θ * I)) * τ)⁻¹) (Ioo 0 1) := by
  refine Integrable.mono' hgi.norm ?_ ?_
  · exact (by fun_prop : Measurable fun τ : ℝ =>
      (g τ : ℂ) * (1 + ((r : ℂ) * exp (θ * I)) * τ)⁻¹).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun τ hτ => ?_)
    rw [norm_mul, Complex.norm_real, airyDer_one_add_eq]
    calc ‖g τ‖ * ‖(1 + ((r * τ : ℝ) : ℂ) * exp (θ * I))⁻¹‖ ≤ ‖g τ‖ * 1 :=
          mul_le_mul_of_nonneg_left (airyDer_norm_recip_le hcos (mul_nonneg hr hτ.1.le))
            (norm_nonneg _)
      _ = ‖g τ‖ := mul_one _

/-- For a nonnegative integrable weight `g` on `(0,1)`, `cos θ ≥ 0` and `r ≥ 0`, the inner
Stieltjes integral `q(r) = ∫₀¹ g(τ)/(1 + r e^{iθ} τ) dτ` has `‖q(r)‖ ≤ ∫ g` and
`0 ≤ Re q(r) ≤ ∫ g`. -/
private lemma airyDer_inner_bounds {g : ℝ → ℝ} (hgm : Measurable g)
    (hg0 : ∀ τ ∈ Ioo (0 : ℝ) 1, 0 ≤ g τ) (hgi : IntegrableOn g (Ioo 0 1)) {θ : ℝ}
    (hcos : 0 ≤ Real.cos θ) {r : ℝ} (hr : 0 ≤ r) :
    ‖∫ τ in Ioo (0 : ℝ) 1, (g τ : ℂ) * (1 + ((r : ℂ) * exp (θ * I)) * τ)⁻¹‖ ≤
        ∫ τ in Ioo (0 : ℝ) 1, g τ ∧
      0 ≤ (∫ τ in Ioo (0 : ℝ) 1, (g τ : ℂ) * (1 + ((r : ℂ) * exp (θ * I)) * τ)⁻¹).re ∧
      (∫ τ in Ioo (0 : ℝ) 1, (g τ : ℂ) * (1 + ((r : ℂ) * exp (θ * I)) * τ)⁻¹).re ≤
        ∫ τ in Ioo (0 : ℝ) 1, g τ := by
  refine ⟨?_, ?_⟩
  · refine (norm_integral_le_of_norm_le hgi ?_).trans le_rfl
    refine (ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun τ hτ => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hg0 τ hτ), airyDer_one_add_eq]
    calc g τ * ‖(1 + ((r * τ : ℝ) : ℂ) * exp (θ * I))⁻¹‖ ≤ g τ * 1 :=
          mul_le_mul_of_nonneg_left (airyDer_norm_recip_le hcos (mul_nonneg hr hτ.1.le))
            (hg0 τ hτ)
      _ = g τ := mul_one _
  have hi := airyDer_integrableOn_inner hgm hgi hcos hr
  have he : (∫ τ in Ioo (0 : ℝ) 1, (g τ : ℂ) * (1 + ((r : ℂ) * exp (θ * I)) * τ)⁻¹).re =
      ∫ τ in Ioo (0 : ℝ) 1, g τ * ((1 + ((r * τ : ℝ) : ℂ) * exp (θ * I))⁻¹).re := by
    rw [← RCLike.re_to_complex, ← integral_re hi]
    refine setIntegral_congr_fun measurableSet_Ioo fun τ _ => ?_
    simp only [RCLike.re_to_complex]
    rw [airyDer_one_add_eq, re_ofReal_mul]
  rw [he]
  have hi' : IntegrableOn (fun τ => g τ * ((1 + ((r * τ : ℝ) : ℂ) * exp (θ * I))⁻¹).re)
      (Ioo 0 1) := by
    refine (hi.re).congr_fun (fun τ _ => ?_) measurableSet_Ioo
    simp only [RCLike.re_to_complex]
    rw [airyDer_one_add_eq, re_ofReal_mul]
  constructor
  · exact setIntegral_nonneg measurableSet_Ioo fun τ hτ =>
      mul_nonneg (hg0 τ hτ) (airyDer_re_recip_mem hcos (mul_nonneg hr hτ.1.le)).1
  · refine setIntegral_mono_on hi' hgi measurableSet_Ioo fun τ hτ => ?_
    calc g τ * ((1 + ((r * τ : ℝ) : ℂ) * exp (θ * I))⁻¹).re ≤ g τ * 1 :=
          mul_le_mul_of_nonneg_left (airyDer_re_recip_mem hcos (mul_nonneg hr hτ.1.le)).2
            (hg0 τ hτ)
      _ = g τ := mul_one _

/-- **The ray remainder as a damped multiple of the first neglected term.** For `cos θ ≥ 0` and a
nonnegative weight `g` on `(0,1)`, the ray Stieltjes integral equals `(A + iB)` times its value
with the Stieltjes denominator replaced by `1`, with `0 ≤ A ≤ 1`. -/
theorem airyDer_ray_ratio {b W θ : ℝ} (hb : 0 < b) (hW : 0 < W) (hθ : |θ| < π)
    (hcos : 0 ≤ Real.cos θ) (N : ℕ) {g : ℝ → ℝ} (hgm : Measurable g)
    (hg0 : ∀ τ ∈ Ioo (0 : ℝ) 1, 0 ≤ g τ) (hgi : IntegrableOn g (Ioo 0 1)) :
    ∃ A B : ℝ, 0 ≤ A ∧ A ≤ 1 ∧
      ∫ r in Ioi (0 : ℝ), Complex.exp (-(W * r)) * (((r : ℂ) * exp (θ * I)) ^ ((b : ℂ) - 1) *
        ((-((r : ℂ) * exp (θ * I))) ^ N * ∫ τ in Ioo (0 : ℝ) 1,
          (g τ : ℂ) * (1 + ((r : ℂ) * exp (θ * I)) * τ)⁻¹)) =
      (A + B * I) * ((((-1) ^ N * ∫ τ in Ioo (0 : ℝ) 1, g τ : ℝ) : ℂ) *
        exp (θ * I * ((b : ℂ) - 1 + N)) * (Gamma ((b : ℂ) + N) * (W : ℂ) ^ (-((b : ℂ) + N)))) := by
  set q : ℝ → ℂ := fun r => ∫ τ in Ioo (0 : ℝ) 1,
    (g τ : ℂ) * (1 + ((r : ℂ) * exp (θ * I)) * τ)⁻¹ with hq
  set C : ℝ := ∫ τ in Ioo (0 : ℝ) 1, g τ with hC
  set ρ : ℝ → ℝ := fun r => r ^ ((b + N) - 1) * Real.exp (-(W * r)) with hρ
  set ph : ℂ := exp (θ * I * ((b : ℂ) - 1 + N)) with hph
  set K : ℝ := Real.Gamma (b + N) * W ^ (-(b + N)) with hK
  have hbN : 0 < b + N := by positivity
  have hKpos : 0 < K := mul_pos (Real.Gamma_pos_of_pos hbN) (Real.rpow_pos_of_pos hW _)
  have hKc : Gamma ((b : ℂ) + N) * (W : ℂ) ^ (-((b : ℂ) + N)) = (K : ℂ) := by
    have hg : Gamma ((b : ℂ) + N) = ((Real.Gamma (b + N) : ℝ) : ℂ) := by
      rw [← Complex.Gamma_ofReal]; push_cast; rfl
    have hw : (W : ℂ) ^ (-((b : ℂ) + N)) = ((W ^ (-(b + N)) : ℝ) : ℂ) := by
      rw [ofReal_cpow hW.le]; push_cast; rfl
    rw [hg, hw, hK]; push_cast; ring
  rw [hKc]
  have hC0 : 0 ≤ C := setIntegral_nonneg measurableSet_Ioo hg0
  -- pointwise form
  have hpt : ∀ r ∈ Ioi (0 : ℝ), Complex.exp (-(W * r)) * (((r : ℂ) * exp (θ * I)) ^ ((b : ℂ) - 1) *
      ((-((r : ℂ) * exp (θ * I))) ^ N * q r)) = ((-1) ^ N * ph) * ((ρ r : ℂ) * q r) := by
    intro r hr
    have h := airySt_term_eq (b := b) (W := W) hθ N hr
    rw [neg_pow ((r : ℂ) * exp (θ * I)) N]
    rw [show Complex.exp (-(W * r)) * (((r : ℂ) * exp (θ * I)) ^ ((b : ℂ) - 1) *
      ((-1) ^ N * ((r : ℂ) * exp (θ * I)) ^ N * q r)) = (-1) ^ N * q r *
      (Complex.exp (-(W * r)) * (((r : ℂ) * exp (θ * I)) ^ ((b : ℂ) - 1) *
      ((r : ℂ) * exp (θ * I)) ^ N)) by ring, h, hρ, hph]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul]
  -- bounds on q
  have hqn : ∀ r : ℝ, 0 ≤ r → ‖q r‖ ≤ C := fun r hr =>
    (airyDer_inner_bounds hgm hg0 hgi hcos hr).1
  have hqre : ∀ r : ℝ, 0 ≤ r → 0 ≤ (q r).re ∧ (q r).re ≤ C := fun r hr =>
    (airyDer_inner_bounds hgm hg0 hgi hcos hr).2
  -- integrability of ρ q
  have hρi : IntegrableOn ρ (Ioi 0) := stRem_integrableOn_rpow_exp (by linarith) hW
  have hqm : AEStronglyMeasurable q (volume.restrict (Ioi 0)) := by
    have hG : StronglyMeasurable (Function.uncurry fun (r τ : ℝ) =>
        (g τ : ℂ) * (1 + ((r : ℂ) * exp (θ * I)) * τ)⁻¹) := by
      refine Measurable.stronglyMeasurable ?_
      fun_prop
    exact (hG.integral_prod_right (ν := volume.restrict (Ioo 0 1))).aestronglyMeasurable
  have hJi : IntegrableOn (fun r => (ρ r : ℂ) * q r) (Ioi 0) := by
    refine Integrable.mono' (hρi.mul_const C) ((hρi.ofReal (𝕜 := ℂ)).aestronglyMeasurable.mul hqm) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun r hr => ?_)
    have hr : (0 : ℝ) < r := hr
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (hqn r hr.le) (by positivity)
  set J : ℂ := ∫ r in Ioi (0 : ℝ), (ρ r : ℂ) * q r with hJ
  have hJre : J.re = ∫ r in Ioi (0 : ℝ), ρ r * (q r).re := by
    rw [hJ, ← RCLike.re_to_complex, ← integral_re hJi]
    refine setIntegral_congr_fun measurableSet_Ioi fun r _ => ?_
    simp only [RCLike.re_to_complex]; rw [re_ofReal_mul]
  have hρq : IntegrableOn (fun r => ρ r * (q r).re) (Ioi 0) := by
    refine (hJi.re).congr_fun (fun r _ => ?_) measurableSet_Ioi
    simp only [RCLike.re_to_complex]; rw [re_ofReal_mul]
  have hρ0 : ∀ r ∈ Ioi (0 : ℝ), 0 ≤ ρ r := fun r hr => by
    have hr : (0 : ℝ) < r := hr
    simp only [hρ]; positivity
  have hJ0 : 0 ≤ J.re := by
    rw [hJre]; exact setIntegral_nonneg measurableSet_Ioi fun r hr =>
      mul_nonneg (hρ0 r hr) (hqre r (le_of_lt hr)).1
  have hJ1 : J.re ≤ C * K := by
    rw [hJre]
    calc ∫ r in Ioi (0 : ℝ), ρ r * (q r).re ≤ ∫ r in Ioi (0 : ℝ), ρ r * C :=
          setIntegral_mono_on hρq (hρi.mul_const C) measurableSet_Ioi fun r hr =>
            mul_le_mul_of_nonneg_left (hqre r (le_of_lt hr)).2 (hρ0 r hr)
      _ = C * K := by
          rw [integral_mul_const, hρ, airySt_gamma_int hbN hW, hK]; ring
  rcases eq_or_lt_of_le hC0 with hC0' | hCpos
  · -- degenerate weight
    have hJz : J = 0 := by
      have : ‖J‖ ≤ 0 := by
        rw [hJ]
        refine norm_integral_le_of_norm_le (g := fun _ => (0 : ℝ)) (integrable_zero _ _ _) ?_
          |>.trans (by simp)
        refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun r hr => ?_)
        have hr : (0 : ℝ) < r := hr
        rw [norm_mul]
        have := hqn r hr.le
        rw [← hC0'] at this
        nlinarith [norm_nonneg (q r), norm_nonneg ((ρ r : ℂ))]
      exact norm_le_zero_iff.mp this
    refine ⟨0, 0, le_rfl, zero_le_one, ?_⟩
    rw [hJz, ← hC0']; simp
  · refine ⟨J.re / (C * K), J.im / (C * K), div_nonneg hJ0 (by positivity),
      (div_le_one (by positivity)).mpr hJ1, ?_⟩
    have hCK : ((C * K : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (by positivity)
    have hAB : (((J.re / (C * K) : ℝ) : ℂ) + ((J.im / (C * K) : ℝ) : ℂ) * I) =
        J / ((C * K : ℝ) : ℂ) := by
      apply Complex.ext
      · rw [add_re, ofReal_re, mul_re, ofReal_re, ofReal_im, I_re, I_im, div_ofReal_re]; ring
      · rw [add_im, ofReal_im, mul_im, ofReal_re, ofReal_im, I_re, I_im, div_ofReal_im]; ring
    rw [hAB, div_mul_eq_mul_div, eq_div_iff hCK]
    push_cast; ring

/-- Measurability of `τ ↦ c τ^N w_a(τ)`. -/
theorem airyDer_measurable_w (a : ℝ) (N : ℕ) (c : ℝ) :
    Measurable fun τ : ℝ => c * (τ ^ N * airySt_w a τ) := by
  unfold airySt_w; fun_prop

/-- **The Ai remainder on `|arg z| ≤ π/3`** is `(A + iB)` times the first neglected term,
`0 ≤ A ≤ 1`. -/
theorem airyDer_ai_ratio {z : ℂ} (hz : z ≠ 0) (harg : |arg z| ≤ π / 3) (N : ℕ) :
    ∃ A B : ℝ, 0 ≤ A ∧ A ≤ 1 ∧
      airyRemainder .ai N z = (A + B * I) * (airyExpansionCoeff .ai N / airyZetaComplex z ^ N) := by
  have hπ := Real.pi_pos
  have harg' : |arg z| < 2 * π / 3 := by linarith
  obtain ⟨h1, h2⟩ := airySt_ai_remainder hz harg' N
  have hθ := airySt_theta_lt harg'
  have hcos : 0 ≤ Real.cos (-(3 / 2 * arg z)) := by
    rw [Real.cos_neg]
    exact Real.cos_nonneg_of_mem_Icc ⟨by linarith [(abs_le.mp harg).1],
      by linarith [(abs_le.mp harg).2]⟩
  have hW : 0 < Real.exp (log 2 + airyLogZeta z).re := Real.exp_pos _
  rw [h1, h2, airySt_rem_repr (a := 5 / 6) (b := 1 / 6) (by norm_num) (by norm_num) (by norm_num)
    hW hθ N (airySt_hint hθ hW)]
  set c : ℝ := 1 / (Real.Gamma (5 / 6) * Real.Gamma (1 - 5 / 6)) with hc
  have hQ : ∀ t : ℂ, airySt_Q (5 / 6) N t = ∫ τ in Ioo (0 : ℝ) 1,
      ((c * (τ ^ N * airySt_w (5 / 6) τ) : ℝ) : ℂ) * (1 + t * τ)⁻¹ := by
    intro t; unfold airySt_Q; rw [← hc, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
    push_cast; ring
  simp_rw [hQ]
  have hc0 : 0 < c := by
    have := Real.Gamma_pos_of_pos (show (0 : ℝ) < 5 / 6 by norm_num)
    have := Real.Gamma_pos_of_pos (show (0 : ℝ) < 1 - 5 / 6 by norm_num)
    positivity
  obtain ⟨A, B, hA0, hA1, hE⟩ := airyDer_ray_ratio (b := 1 / 6) (by norm_num) hW hθ hcos N
    (airyDer_measurable_w (5 / 6) N c)
    (fun τ hτ => mul_nonneg hc0.le (mul_nonneg (pow_nonneg hτ.1.le _) (airySt_w_nonneg _ hτ)))
    ((airySt_integrableOn_w (by norm_num) (by norm_num) N).const_mul c)
  refine ⟨A, B, hA0, hA1, ?_⟩
  rw [hE]
  have hcoef : ((-1) ^ N * ∫ τ in Ioo (0 : ℝ) 1, c * (τ ^ N * airySt_w (5 / 6) τ) : ℝ) =
      airySt_coef (5 / 6) N := by
    rw [integral_const_mul, airySt_moment (by norm_num) (by norm_num) N, airySt_coef, hc]
    have h1 : Real.Gamma (1 - 5 / 6) ≠ 0 := (Real.Gamma_pos_of_pos (by norm_num)).ne'
    have h2 : Real.Gamma (5 / 6) ≠ 0 := (Real.Gamma_pos_of_pos (by norm_num)).ne'
    field_simp
  rw [hcoef]; unfold airySt_T; ring

/-- `cos (w - π/4)` and `sin (w - π/4)` through `e^{∓iw}`. -/
theorem airyDer_cos_sin (w : ℂ) :
    cos (w - π / 4) = exp (π * I / 4) / 2 * exp (-(w * I)) + exp (-(π * I / 4)) / 2 * exp (w * I) ∧
    sin (w - π / 4) =
      I * (exp (π * I / 4) / 2 * exp (-(w * I)) - exp (-(π * I / 4)) / 2 * exp (w * I)) := by
  have e1 : exp ((w - π / 4) * I) = exp (-(π * I / 4)) * exp (w * I) := by
    rw [← exp_add]; congr 1; ring
  have e2 : exp (-(w - π / 4) * I) = exp (π * I / 4) * exp (-(w * I)) := by
    rw [← exp_add]; congr 1; ring
  constructor
  · rw [Complex.cos, e1, e2]; ring
  · rw [Complex.sin, e1, e2]
    field_simp


/-- `Ai(-z)` through the even and odd parts of the normalized `Ai`, exactly (DLMF 9.7.9). -/
theorem airyDer_airyAi_neg {z : ℂ} (hz0 : z ≠ 0) (hz3 : |arg z| < 2 * π / 3) :
    airyAi (-z) = airyOscPrefactor .ai z *
      (cos (airyZetaComplex z - π / 4) * airyRot_even (fun w => airyAi w / airyPrefactor .ai w) z +
        sin (airyZetaComplex z - π / 4) *
          airyRot_odd (fun w => airyAi w / airyPrefactor .ai w) z) := by
  obtain ⟨u4, um4, u3, um3, u2, um2, u12⟩ := airyRot_u_powers
  set u := exp (π * I / 12) with hu
  have hu0 : u ≠ 0 := exp_ne_zero _
  obtain ⟨d1, d2, d3, d4⟩ := airyRot_third_data hz0 hz3
  have hπs : (Real.sqrt π : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hq : z ^ (1 / 4 : ℂ) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hz0)
  have hp1 := airyRot_prefactor_ne_zero .ai (mul_ne_zero hz0 (exp_ne_zero ((π / 3 : ℝ) * I)))
  have hp2 := airyRot_prefactor_ne_zero .ai
    (mul_ne_zero hz0 (exp_ne_zero ((-(π / 3) : ℝ) * I)))
  obtain ⟨hc, hs⟩ := airyDer_cos_sin (airyZetaComplex z)
  rw [hc, hs]
  rw [airyRot_airyAi_neg z]
  rw [show airyAi (z * exp ((π / 3 : ℝ) * I)) = airyPrefactor .ai (z * exp ((π / 3 : ℝ) * I)) *
      (airyAi (z * exp ((π / 3 : ℝ) * I)) / airyPrefactor .ai (z * exp ((π / 3 : ℝ) * I))) by
      field_simp,
    show airyAi (z * exp ((-(π / 3) : ℝ) * I)) =
      airyPrefactor .ai (z * exp ((-(π / 3) : ℝ) * I)) *
      (airyAi (z * exp ((-(π / 3) : ℝ) * I)) /
        airyPrefactor .ai (z * exp ((-(π / 3) : ℝ) * I))) by field_simp]
  rw [← mul_assoc, ← mul_assoc]
  rw [airyRot_decomp (fun w => airyAi w / airyPrefactor .ai w)]
  have ep : exp (π * I / 3) * airyPrefactor .ai (z * exp ((π / 3 : ℝ) * I)) =
      airyOscPrefactor .ai z * (exp (π * I / 4) / 2 * exp (-(airyZetaComplex z * I))) := by
    simp only [airyPrefactor, airyOscPrefactor]
    rw [d1, d3, u4, u3]
    field_simp
    rw [hu]; ring_nf
  have em : exp (-π * I / 3) * airyPrefactor .ai (z * exp ((-(π / 3) : ℝ) * I)) =
      airyOscPrefactor .ai z * (exp (-(π * I / 4)) / 2 * exp (airyZetaComplex z * I)) := by
    simp only [airyPrefactor, airyOscPrefactor]
    rw [d2, d4, um4, um3, neg_neg]
    field_simp
    rw [hu]; ring_nf
  rw [ep, em]
  ring

/-- `Bi(-z)` through the even and odd parts of the normalized `Ai`, exactly (DLMF 9.7.11). -/
theorem airyDer_airyBi_neg {z : ℂ} (hz0 : z ≠ 0) (hz3 : |arg z| < 2 * π / 3) :
    airyBi (-z) = airyOscPrefactor .ai z *
      (-sin (airyZetaComplex z - π / 4) *
          airyRot_even (fun w => airyAi w / airyPrefactor .ai w) z +
        cos (airyZetaComplex z - π / 4) *
          airyRot_odd (fun w => airyAi w / airyPrefactor .ai w) z) := by
  obtain ⟨u4, um4, u3, um3, u2, um2, u12⟩ := airyRot_u_powers
  set u := exp (π * I / 12) with hu
  have hu0 : u ≠ 0 := exp_ne_zero _
  obtain ⟨d1, d2, d3, d4⟩ := airyRot_third_data hz0 hz3
  have hπs : (Real.sqrt π : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hq : z ^ (1 / 4 : ℂ) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hz0)
  have hp1 := airyRot_prefactor_ne_zero .ai
    (mul_ne_zero hz0 (exp_ne_zero ((π / 3 : ℝ) * I)))
  have hp2 := airyRot_prefactor_ne_zero .ai
    (mul_ne_zero hz0 (exp_ne_zero ((-(π / 3) : ℝ) * I)))
  have hcs : cos (airyZetaComplex z - π / 4) =
      I * (exp (-(π * I / 4)) / 2 * exp (-(airyZetaComplex z * I)) -
        exp (π * I / 4) / 2 * exp (airyZetaComplex z * I)) ∧
      -sin (airyZetaComplex z - π / 4) = exp (-(π * I / 4)) / 2 * exp (-(airyZetaComplex z * I)) +
        exp (π * I / 4) / 2 * exp (airyZetaComplex z * I) := by
    rw [show cos (airyZetaComplex z - π / 4) = sin (airyZetaComplex z - π / 4 + π / 2) from
        (Complex.sin_add_pi_div_two _).symm,
      show sin (airyZetaComplex z - π / 4) = -cos (airyZetaComplex z - π / 4 + π / 2) by
        rw [Complex.cos_add_pi_div_two]; ring]
    simp only [Complex.cos, Complex.sin]
    have e1 : exp ((airyZetaComplex z - π / 4 + π / 2) * I) =
        exp (π * I / 4) * exp (airyZetaComplex z * I) := by
      rw [← exp_add]; congr 1; ring
    have e2 : exp (-(airyZetaComplex z - π / 4 + π / 2) * I) =
        exp (-(π * I / 4)) * exp (-(airyZetaComplex z * I)) := by
      rw [← exp_add]; congr 1; ring
    rw [e1, e2]
    constructor
    · field_simp
    · ring
  rw [hcs.1, hcs.2]
  rw [airyRot_airyBi_neg z]
  rw [show airyAi (z * exp ((π / 3 : ℝ) * I)) =
      airyPrefactor .ai (z * exp ((π / 3 : ℝ) * I)) *
      (airyAi (z * exp ((π / 3 : ℝ) * I)) /
        airyPrefactor .ai (z * exp ((π / 3 : ℝ) * I))) by field_simp,
    show airyAi (z * exp ((-(π / 3) : ℝ) * I)) =
      airyPrefactor .ai (z * exp ((-(π / 3) : ℝ) * I)) *
      (airyAi (z * exp ((-(π / 3) : ℝ) * I)) /
        airyPrefactor .ai (z * exp ((-(π / 3) : ℝ) * I))) by field_simp]
  rw [← mul_assoc, ← mul_assoc]
  rw [airyRot_decomp (fun w => airyAi w / airyPrefactor .ai w)]
  have ep : exp (-π * I / 6) * airyPrefactor .ai (z * exp ((π / 3 : ℝ) * I)) =
      airyOscPrefactor .ai z *
        (exp (-(π * I / 4)) / 2 * exp (-(airyZetaComplex z * I))) := by
    simp only [airyPrefactor, airyOscPrefactor]
    rw [d1, d3, ← hu, um2, um3]
    field_simp
  have em : exp (π * I / 6) * airyPrefactor .ai (z * exp ((-(π / 3) : ℝ) * I)) =
      airyOscPrefactor .ai z * (exp (π * I / 4) / 2 * exp (airyZetaComplex z * I)) := by
    simp only [airyPrefactor, airyOscPrefactor]
    rw [d2, d4, ← hu, u2, u3, neg_neg]
    field_simp
  rw [ep, em]
  ring


/-- The even part of `(Σ_{k<2N} c_k (iZ)^{-k} + Σ_{k<2N} c_k (-iZ)^{-k})/2`. -/
theorem airyDer_sum_even (c : ℕ → ℂ) {Z : ℂ} (hZ : Z ≠ 0) (N : ℕ) :
    (∑ k ∈ Finset.range (2 * N), c k / (Z * I) ^ k +
        ∑ k ∈ Finset.range (2 * N), c k / (-(Z * I)) ^ k) / 2 =
      ∑ j ∈ Finset.range N, (-1 : ℂ) ^ j * c (2 * j) / Z ^ (2 * j) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hm : ((-1 : ℂ) ^ N) * (-1) ^ N = 1 := by rw [← mul_pow]; norm_num
    have hm0 : ((-1 : ℂ) ^ N) ≠ 0 := pow_ne_zero _ (by norm_num)
    have p1 : (Z * I) ^ (2 * N) = (-1) ^ N * Z ^ (2 * N) := by
      rw [mul_pow, pow_mul I, I_sq]; ring
    have p2 : (-(Z * I)) ^ (2 * N) = (-1) ^ N * Z ^ (2 * N) := by
      rw [pow_mul, neg_sq, ← pow_mul, p1]
    have p3 : (Z * I) ^ (2 * N + 1) = (-1) ^ N * Z ^ (2 * N) * (Z * I) := by
      rw [pow_succ, p1]
    have p4 : (-(Z * I)) ^ (2 * N + 1) = -((-1) ^ N * Z ^ (2 * N) * (Z * I)) := by
      rw [pow_succ, p2]; ring
    have hZ2 : Z ^ (2 * N) ≠ 0 := pow_ne_zero _ hZ
    have hs : ∀ f : ℕ → ℂ, ∑ k ∈ Finset.range (2 * (N + 1)), f k =
        ∑ k ∈ Finset.range (2 * N), f k + f (2 * N) + f (2 * N + 1) := fun f => by
      rw [show 2 * (N + 1) = 2 * N + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ]
    have key : (c (2 * N) / (Z * I) ^ (2 * N) + c (2 * N + 1) / (Z * I) ^ (2 * N + 1) +
        (c (2 * N) / (-(Z * I)) ^ (2 * N) + c (2 * N + 1) / (-(Z * I)) ^ (2 * N + 1))) / 2 =
        (-1) ^ N * c (2 * N) / Z ^ (2 * N) := by
      rw [p1, p2, p3, p4]
      have hI : I ≠ 0 := I_ne_zero
      field_simp
      linear_combination (-(2 * c (2 * N) * Z * I)) * hm
    rw [hs, hs, Finset.sum_range_succ]
    linear_combination ih + key

/-- The odd part of `(Σ_{k≤2N} c_k (iZ)^{-k} - Σ_{k≤2N} c_k (-iZ)^{-k})/(2i)`. -/
theorem airyDer_sum_odd (c : ℕ → ℂ) {Z : ℂ} (hZ : Z ≠ 0) (N : ℕ) :
    (∑ k ∈ Finset.range (2 * N + 1), c k / (Z * I) ^ k -
        ∑ k ∈ Finset.range (2 * N + 1), c k / (-(Z * I)) ^ k) / (2 * I) =
      ∑ j ∈ Finset.range N, -((-1 : ℂ) ^ j * c (2 * j + 1)) / Z ^ (2 * j + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hm : ((-1 : ℂ) ^ N) * (-1) ^ N = 1 := by rw [← mul_pow]; norm_num
    have hm0 : ((-1 : ℂ) ^ N) ≠ 0 := pow_ne_zero _ (by norm_num)
    have p1 : (Z * I) ^ (2 * N) = (-1) ^ N * Z ^ (2 * N) := by
      rw [mul_pow, pow_mul I, I_sq]; ring
    have p3 : (Z * I) ^ (2 * N + 1) = (-1) ^ N * Z ^ (2 * N) * (Z * I) := by
      rw [pow_succ, p1]
    have p4 : (-(Z * I)) ^ (2 * N + 1) = -((-1) ^ N * Z ^ (2 * N) * (Z * I)) := by
      rw [pow_succ, pow_mul, neg_sq, ← pow_mul, p1]; ring
    have p5 : (Z * I) ^ (2 * N + 2) = -((-1) ^ N * Z ^ (2 * N) * Z ^ 2) := by
      rw [pow_succ, pow_succ, p1]; ring_nf; rw [I_sq]; ring
    have p6 : (-(Z * I)) ^ (2 * N + 2) = -((-1) ^ N * Z ^ (2 * N) * Z ^ 2) := by
      rw [pow_succ, pow_succ, pow_mul, neg_sq, ← pow_mul, p1]; ring_nf; rw [I_sq]; ring
    have hZ2 : Z ^ (2 * N) ≠ 0 := pow_ne_zero _ hZ
    have hs : ∀ f : ℕ → ℂ, ∑ k ∈ Finset.range (2 * (N + 1) + 1), f k =
        ∑ k ∈ Finset.range (2 * N + 1), f k + f (2 * N + 1) + f (2 * N + 2) := fun f => by
      rw [show 2 * (N + 1) + 1 = 2 * N + 1 + 1 + 1 by ring, Finset.sum_range_succ,
        Finset.sum_range_succ]
    have key : (c (2 * N + 1) / (Z * I) ^ (2 * N + 1) + c (2 * N + 2) / (Z * I) ^ (2 * N + 2) -
        (c (2 * N + 1) / (-(Z * I)) ^ (2 * N + 1) + c (2 * N + 2) / (-(Z * I)) ^ (2 * N + 2))) /
          (2 * I) = -((-1) ^ N * c (2 * N + 1)) / Z ^ (2 * N + 1) := by
      rw [p3, p4, p5, p6]
      have hI : I ≠ 0 := I_ne_zero
      field_simp
      linear_combination (-(2 * c (2 * N + 1) * Z ^ 2 * Z ^ (2 * N))) * hm +
        (2 * c (2 * N + 1) * Z ^ 2 * Z ^ (2 * N) * (-1) ^ N * (-1) ^ N) * I_sq
    rw [hs, hs, Finset.sum_range_succ (fun j => -((-1 : ℂ) ^ j * c (2 * j + 1)) / Z ^ (2 * j + 1)) N]
    linear_combination ih + key


/-- The normalized `Ai`. -/
theorem airyDer_comp_false {x : ℝ} (hx : 0 < x) :
    airyOscComponent false 0 x = airyRot_even (fun w => airyAi w / airyPrefactor .ai w) x ∧
    airyOscComponent false 1 x = airyRot_odd (fun w => airyAi w / airyPrefactor .ai w) x := by
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have harg : |arg (x : ℂ)| < 2 * π / 3 := by
    rw [arg_ofReal_of_nonneg hx.le, abs_zero]; positivity
  have hA := airyDer_airyAi_neg hx0 harg
  have hB := airyDer_airyBi_neg hx0 harg
  rw [airyReal_zeta_ofReal hx] at hA hB
  have hP : airyOscPrefactor .ai (x : ℂ) ≠ 0 := by
    simp only [airyOscPrefactor]
    have hπs : (Real.sqrt π : ℂ) ≠ 0 :=
      ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
    have hq : (x : ℂ) ^ (1 / 4 : ℂ) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hx0)
    exact one_div_ne_zero (mul_ne_zero hπs hq)
  have hcs := Complex.cos_sq_add_sin_sq (((airyZeta x : ℝ) : ℂ) - π / 4)
  simp only [airyOscComponent, Bool.false_eq_true, ite_false, Fin.val_zero, Fin.val_one,
    ite_true, one_ne_zero]
  rw [hA, hB]
  constructor
  · rw [div_eq_iff hP]
    linear_combination (airyOscPrefactor .ai (x : ℂ) *
      airyRot_even (fun w => airyAi w / airyPrefactor .ai w) x) * hcs
  · rw [div_eq_iff hP]
    linear_combination (airyOscPrefactor .ai (x : ℂ) *
      airyRot_odd (fun w => airyAi w / airyPrefactor .ai w) x) * hcs


/-- `Ai'` is real on the real axis (as in `DLMF.Airy.ModulusPhase`, which this file does not
import). -/
theorem airyDer_aiDeriv_ofReal_im (x : ℝ) : (airyAiDeriv x).im = 0 := by
  have h := ((hasDerivAt_airyAi x).comp_ofReal).hasFDerivAt.restrictScalars ℝ
  have h1 : HasDerivAt (fun t : ℝ => (airyAi t).im) (airyAiDeriv x).im x := by
    have := (Complex.imCLM.hasFDerivAt.comp x h).hasDerivAt
    simpa [Function.comp_def] using this
  have h0 : (fun t : ℝ => (airyAi t).im) = fun _ => 0 := funext airyAi_ofReal_im
  rw [h0] at h1
  exact (h1.unique (hasDerivAt_const x 0))

/-- `Bi'` is real on the real axis. -/
theorem airyDer_biDeriv_ofReal_im (x : ℝ) : (airyBiDeriv x).im = 0 := by
  have h := ((hasDerivAt_airyBi x).comp_ofReal).hasFDerivAt.restrictScalars ℝ
  have h1 : HasDerivAt (fun t : ℝ => (airyBi t).im) (airyBiDeriv x).im x := by
    have := (Complex.imCLM.hasFDerivAt.comp x h).hasDerivAt
    simpa [Function.comp_def] using this
  have h0 : (fun t : ℝ => (airyBi t).im) = fun _ => 0 := funext airyBi_ofReal_im
  rw [h0] at h1
  exact (h1.unique (hasDerivAt_const x 0))

/-- A complex number with zero imaginary part is the cast of its real part. -/
theorem airyDer_eq_ofReal {w : ℂ} (h : w.im = 0) : w = (w.re : ℂ) :=
  Complex.ext (by simp) (by simp [h])

/-- The oscillatory components are real on the positive axis. -/
theorem airyDer_comp_im (derivative : Bool) (parity : Fin 2) {x : ℝ} (hx : 0 < x) :
    (airyOscComponent derivative parity x).im = 0 := by
  have hneg : (-(x : ℂ)) = ((-x : ℝ) : ℂ) := by push_cast; ring
  have hA := airyDer_eq_ofReal (w := airyAi (-(x : ℂ))) (by rw [hneg]; exact airyAi_ofReal_im _)
  have hB := airyDer_eq_ofReal (w := airyBi (-(x : ℂ))) (by rw [hneg]; exact airyBi_ofReal_im _)
  have hA' := airyDer_eq_ofReal (w := airyAiDeriv (-(x : ℂ)))
    (by rw [hneg]; exact airyDer_aiDeriv_ofReal_im _)
  have hB' := airyDer_eq_ofReal (w := airyBiDeriv (-(x : ℂ)))
    (by rw [hneg]; exact airyDer_biDeriv_ofReal_im _)
  have hq : (x : ℂ) ^ (1 / 4 : ℂ) = ((x ^ (1 / 4 : ℝ) : ℝ) : ℂ) := by
    rw [ofReal_cpow hx.le]; push_cast; rfl
  have hc : cos (((airyZeta x : ℝ) : ℂ) - π / 4) = ((Real.cos (airyZeta x - π / 4) : ℝ) : ℂ) := by
    push_cast; rfl
  have hs : sin (((airyZeta x : ℝ) : ℂ) - π / 4) = ((Real.sin (airyZeta x - π / 4) : ℝ) : ℂ) := by
    push_cast; rfl
  cases derivative <;> simp only [airyOscComponent, Bool.false_eq_true, ite_false, ite_true,
    airyOscPrefactor, hq, hc, hs] <;> split_ifs <;>
    first
    | rw [hA, hB]; norm_cast
    | rw [hA', hB']; norm_cast

/-- The truncated oscillatory sums are real on the positive axis. -/
theorem airyDer_oscSum_im (derivative : Bool) (parity N : ℕ) {x : ℝ} (hx : 0 < x) :
    (airyOscSum derivative parity N x).im = 0 := by
  unfold airyOscSum
  rw [airyReal_zeta_ofReal hx, Complex.im_sum]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [show (-1 : ℂ) ^ k * ((if derivative then airyV (2 * k + parity) else airyU (2 * k + parity) : ℝ) : ℂ)
      / ((airyZeta x : ℝ) : ℂ) ^ (2 * k + parity) = (((-1) ^ k *
        (if derivative then airyV (2 * k + parity) else airyU (2 * k + parity)) /
          airyZeta x ^ (2 * k + parity) : ℝ) : ℂ) by push_cast; rfl]
  exact ofReal_im _


/-- A real number written as `(A + iB) τ` with `τ` real and `0 ≤ A ≤ 1`. -/
theorem airyDer_assemble {D τ : ℂ} {A B τr : ℝ} (hA0 : 0 ≤ A) (hA1 : A ≤ 1) (hτ : τ = τr)
    (hD : D = (A + B * I) * τ) (hDim : D.im = 0) : ‖D‖ ≤ ‖τ‖ ∧ D.re = A * τr := by
  have hre : D.re = A * τr := by rw [hD, hτ]; simp
  refine ⟨?_, hre⟩
  rw [airyDer_eq_ofReal hDim, hre, hτ, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_mul, abs_of_nonneg hA0]
  exact mul_le_of_le_one_left (abs_nonneg _) hA1

/-- The `Ai` coefficients: even ones are `u_{2j}`, odd ones `-u_{2j+1}`. -/
theorem airyDer_coeff_ai (j : ℕ) :
    airyExpansionCoeff .ai (2 * j) = airyU (2 * j) ∧
      airyExpansionCoeff .ai (2 * j + 1) = -(airyU (2 * j + 1) : ℂ) := by
  have h := airyRot_coeff_parity .ai (Or.inl rfl) j
  simpa using h

/-- Rotating `x > 0` by `±π/3`. -/
theorem airyDer_rot_data {x : ℝ} (hx : 0 < x) :
    (x : ℂ) * exp ((π / 3 : ℝ) * I) ≠ 0 ∧ |arg ((x : ℂ) * exp ((π / 3 : ℝ) * I))| ≤ π / 3 ∧
    (x : ℂ) * exp ((-(π / 3) : ℝ) * I) ≠ 0 ∧ |arg ((x : ℂ) * exp ((-(π / 3) : ℝ) * I))| ≤ π / 3 := by
  have hπ := Real.pi_pos
  refine ⟨airyRot_ofReal_mul_exp_ne_zero hx _, ?_, airyRot_ofReal_mul_exp_ne_zero hx _, ?_⟩
  · rw [airyRot_arg hx (by linarith) (by linarith), abs_of_pos (by positivity)]
  · rw [airyRot_arg hx (by linarith) (by linarith), abs_neg, abs_of_pos (by positivity)]

/-- **Signed even bound, abstract form.** If the remainders of `Φ` after `2N` terms at
`x e^{±iπ/3}` are `(A + iB)` times the first neglected term with `0 ≤ A ≤ 1`, and the even part
minus its truncated series is real, then that difference is enclosed by its first neglected term,
with the same sign. -/
theorem airyDer_even_bound (Φ : ℂ → ℂ) (c : ℕ → ℂ) (u : ℕ → ℝ) (hc : ∀ j, c (2 * j) = u (2 * j))
    {x : ℝ} (hx : 0 < x) (N : ℕ)
    (hp : ∃ A B : ℝ, 0 ≤ A ∧ A ≤ 1 ∧ Φ ((x : ℂ) * exp ((π / 3 : ℝ) * I)) -
      ∑ k ∈ Finset.range (2 * N), c k / airyZetaComplex ((x : ℂ) * exp ((π / 3 : ℝ) * I)) ^ k =
        (A + B * I) * (c (2 * N) / airyZetaComplex ((x : ℂ) * exp ((π / 3 : ℝ) * I)) ^ (2 * N)))
    (hm : ∃ A B : ℝ, 0 ≤ A ∧ A ≤ 1 ∧ Φ ((x : ℂ) * exp ((-(π / 3) : ℝ) * I)) -
      ∑ k ∈ Finset.range (2 * N), c k / airyZetaComplex ((x : ℂ) * exp ((-(π / 3) : ℝ) * I)) ^ k =
        (A + B * I) * (c (2 * N) / airyZetaComplex ((x : ℂ) * exp ((-(π / 3) : ℝ) * I)) ^ (2 * N)))
    (hre : (airyRot_even Φ x - ∑ j ∈ Finset.range N,
      (-1 : ℂ) ^ j * (u (2 * j) : ℂ) / airyZetaComplex x ^ (2 * j)).im = 0) :
    ‖airyRot_even Φ x - ∑ j ∈ Finset.range N,
        (-1 : ℂ) ^ j * (u (2 * j) : ℂ) / airyZetaComplex x ^ (2 * j)‖ ≤
        ‖(-1 : ℂ) ^ N * (u (2 * N) : ℂ) / airyZetaComplex x ^ (2 * N)‖ ∧
      0 ≤ (airyRot_even Φ x - ∑ j ∈ Finset.range N,
        (-1 : ℂ) ^ j * (u (2 * j) : ℂ) / airyZetaComplex x ^ (2 * j)).re *
        ((-1 : ℝ) ^ N * u (2 * N)) := by
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have harg : |arg (x : ℂ)| < 2 * π / 3 := by
    rw [arg_ofReal_of_nonneg hx.le, abs_zero]; positivity
  obtain ⟨d1, d2, -, -⟩ := airyRot_third_data hx0 harg
  obtain ⟨Ap, Bp, hAp0, hAp1, hp⟩ := hp
  obtain ⟨Am, Bm, hAm0, hAm1, hm⟩ := hm
  set Z := airyZetaComplex (x : ℂ) with hZ
  have hZ0 : Z ≠ 0 := airySt_zeta_ne_zero hx0
  set τr : ℝ := (-1) ^ N * u (2 * N) / airyZeta x ^ (2 * N) with hτr
  have hτ : (-1 : ℂ) ^ N * (u (2 * N) : ℂ) / Z ^ (2 * N) = (τr : ℂ) := by
    rw [hZ, airyReal_zeta_ofReal hx, hτr]; push_cast; ring
  have p1 : (Z * I) ^ (2 * N) = (-1) ^ N * Z ^ (2 * N) := by
    rw [mul_pow, pow_mul I, I_sq]; ring
  have p2 : (-(Z * I)) ^ (2 * N) = (-1) ^ N * Z ^ (2 * N) := by
    rw [pow_mul, neg_sq, ← pow_mul, p1]
  have hm2 : ((-1 : ℂ) ^ N) * (-1) ^ N = 1 := by rw [← mul_pow]; norm_num
  have hZN : Z ^ (2 * N) ≠ 0 := pow_ne_zero _ hZ0
  have ht : ∀ W : ℂ, W ^ (2 * N) = (-1) ^ N * Z ^ (2 * N) →
      c (2 * N) / W ^ (2 * N) = (τr : ℂ) := by
    intro W hW
    rw [hW, hc N, ← hτ]
    field_simp
    linear_combination (-(u (2 * N) : ℂ)) * hm2
  rw [d1, ht _ p1] at hp
  rw [d2, ht _ p2] at hm
  have hE : airyRot_even Φ x - ∑ j ∈ Finset.range N,
      (-1 : ℂ) ^ j * (u (2 * j) : ℂ) / Z ^ (2 * j) =
      (((Ap + Am) / 2 : ℝ) + ((Bp + Bm) / 2 : ℝ) * I) * (τr : ℂ) := by
    have hS := airyDer_sum_even c hZ0 N
    simp only [hc] at hS
    rw [← hS, airyRot_even]
    push_cast at hp hm ⊢
    linear_combination (1 / 2 : ℂ) * hp + (1 / 2 : ℂ) * hm
  obtain ⟨h1, h2⟩ := airyDer_assemble (by linarith) (by linarith) rfl hE hre
  refine ⟨by rwa [hτ], ?_⟩
  rw [h2, hτr]
  have hz : 0 < airyZeta x := airyZeta_pos hx
  have : 0 ≤ ((-1 : ℝ) ^ N * u (2 * N)) ^ 2 / airyZeta x ^ (2 * N) := by positivity
  calc (0 : ℝ) ≤ (Ap + Am) / 2 * (((-1 : ℝ) ^ N * u (2 * N)) ^ 2 / airyZeta x ^ (2 * N)) :=
        mul_nonneg (by linarith) this
    _ = _ := by ring

/-- **Signed odd bound, abstract form.** -/
theorem airyDer_odd_bound (Φ : ℂ → ℂ) (c : ℕ → ℂ) (u : ℕ → ℝ)
    (hc : ∀ j, c (2 * j + 1) = -(u (2 * j + 1) : ℂ)) {x : ℝ} (hx : 0 < x) (N : ℕ)
    (hp : ∃ A B : ℝ, 0 ≤ A ∧ A ≤ 1 ∧ Φ ((x : ℂ) * exp ((π / 3 : ℝ) * I)) -
      ∑ k ∈ Finset.range (2 * N + 1), c k / airyZetaComplex ((x : ℂ) * exp ((π / 3 : ℝ) * I)) ^ k =
        (A + B * I) * (c (2 * N + 1) /
          airyZetaComplex ((x : ℂ) * exp ((π / 3 : ℝ) * I)) ^ (2 * N + 1)))
    (hm : ∃ A B : ℝ, 0 ≤ A ∧ A ≤ 1 ∧ Φ ((x : ℂ) * exp ((-(π / 3) : ℝ) * I)) -
      ∑ k ∈ Finset.range (2 * N + 1), c k /
        airyZetaComplex ((x : ℂ) * exp ((-(π / 3) : ℝ) * I)) ^ k =
        (A + B * I) * (c (2 * N + 1) /
          airyZetaComplex ((x : ℂ) * exp ((-(π / 3) : ℝ) * I)) ^ (2 * N + 1)))
    (hre : (airyRot_odd Φ x - ∑ j ∈ Finset.range N,
      (-1 : ℂ) ^ j * (u (2 * j + 1) : ℂ) / airyZetaComplex x ^ (2 * j + 1)).im = 0) :
    ‖airyRot_odd Φ x - ∑ j ∈ Finset.range N,
        (-1 : ℂ) ^ j * (u (2 * j + 1) : ℂ) / airyZetaComplex x ^ (2 * j + 1)‖ ≤
        ‖(-1 : ℂ) ^ N * (u (2 * N + 1) : ℂ) / airyZetaComplex x ^ (2 * N + 1)‖ ∧
      0 ≤ (airyRot_odd Φ x - ∑ j ∈ Finset.range N,
        (-1 : ℂ) ^ j * (u (2 * j + 1) : ℂ) / airyZetaComplex x ^ (2 * j + 1)).re *
        ((-1 : ℝ) ^ N * u (2 * N + 1)) := by
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have harg : |arg (x : ℂ)| < 2 * π / 3 := by
    rw [arg_ofReal_of_nonneg hx.le, abs_zero]; positivity
  obtain ⟨d1, d2, -, -⟩ := airyRot_third_data hx0 harg
  obtain ⟨Ap, Bp, hAp0, hAp1, hp⟩ := hp
  obtain ⟨Am, Bm, hAm0, hAm1, hm⟩ := hm
  set Z := airyZetaComplex (x : ℂ) with hZ
  have hZ0 : Z ≠ 0 := airySt_zeta_ne_zero hx0
  set τr : ℝ := (-1) ^ N * u (2 * N + 1) / airyZeta x ^ (2 * N + 1) with hτr
  have hτ : (-1 : ℂ) ^ N * (u (2 * N + 1) : ℂ) / Z ^ (2 * N + 1) = (τr : ℂ) := by
    rw [hZ, airyReal_zeta_ofReal hx, hτr]; push_cast; ring
  have p1 : (Z * I) ^ (2 * N) = (-1) ^ N * Z ^ (2 * N) := by
    rw [mul_pow, pow_mul I, I_sq]; ring
  have p3 : (Z * I) ^ (2 * N + 1) = (-1) ^ N * Z ^ (2 * N) * (Z * I) := by
    rw [pow_succ, p1]
  have p4 : (-(Z * I)) ^ (2 * N + 1) = -((-1) ^ N * Z ^ (2 * N) * (Z * I)) := by
    rw [pow_succ, pow_mul, neg_sq, ← pow_mul, p1]; ring
  have hm2 : ((-1 : ℂ) ^ N) * (-1) ^ N = 1 := by rw [← mul_pow]; norm_num
  have hZN : Z ^ (2 * N) ≠ 0 := pow_ne_zero _ hZ0
  have hI : I ≠ 0 := I_ne_zero
  have htp : c (2 * N + 1) / (Z * I) ^ (2 * N + 1) = I * (τr : ℂ) := by
    rw [p3, hc N, ← hτ, pow_succ]
    field_simp
    linear_combination (u (2 * N + 1) : ℂ) * hm2 +
      (-((u (2 * N + 1) : ℂ) * (-1) ^ N * (-1) ^ N)) * I_sq
  have htm : c (2 * N + 1) / (-(Z * I)) ^ (2 * N + 1) = -(I * (τr : ℂ)) := by
    rw [p4, div_neg, ← p3, htp]
  rw [d1, htp] at hp
  rw [d2, htm] at hm
  have hE : airyRot_odd Φ x - ∑ j ∈ Finset.range N,
      (-1 : ℂ) ^ j * (u (2 * j + 1) : ℂ) / Z ^ (2 * j + 1) =
      (((Ap + Am) / 2 : ℝ) + ((Bp + Bm) / 2 : ℝ) * I) * (τr : ℂ) := by
    have hS := airyDer_sum_odd c hZ0 N
    have hS' : ∑ j ∈ Finset.range N, (-1 : ℂ) ^ j * (u (2 * j + 1) : ℂ) / Z ^ (2 * j + 1) =
        ∑ j ∈ Finset.range N, -((-1 : ℂ) ^ j * c (2 * j + 1)) / Z ^ (2 * j + 1) :=
      Finset.sum_congr rfl fun j _ => by rw [hc j]; ring
    rw [hS', ← hS, airyRot_odd]
    rw [div_sub_div_same, div_eq_iff (mul_ne_zero two_ne_zero hI)]
    push_cast at hp hm ⊢
    linear_combination hp - hm
  obtain ⟨h1, h2⟩ := airyDer_assemble (by linarith) (by linarith) rfl hE hre
  refine ⟨by rwa [hτ], ?_⟩
  rw [h2, hτr]
  have hz : 0 < airyZeta x := airyZeta_pos hx
  have : 0 ≤ ((-1 : ℝ) ^ N * u (2 * N + 1)) ^ 2 / airyZeta x ^ (2 * N + 1) := by positivity
  calc (0 : ℝ) ≤ (Ap + Am) / 2 *
        (((-1 : ℝ) ^ N * u (2 * N + 1)) ^ 2 / airyZeta x ^ (2 * N + 1)) :=
        mul_nonneg (by linarith) this
    _ = _ := by ring

/-- The remainder of the normalized `Ai` in the form used by the abstract bounds. -/
theorem airyDer_ai_ratio' {w : ℂ} (hw : w ≠ 0) (harg : |arg w| ≤ π / 3) (M : ℕ) :
    ∃ A B : ℝ, 0 ≤ A ∧ A ≤ 1 ∧ airyAi w / airyPrefactor .ai w -
      ∑ k ∈ Finset.range M, airyExpansionCoeff .ai k / airyZetaComplex w ^ k =
        (A + B * I) * (airyExpansionCoeff .ai M / airyZetaComplex w ^ M) := by
  obtain ⟨A, B, h0, h1, h⟩ := airyDer_ai_ratio hw harg M
  exact ⟨A, B, h0, h1, by rw [← h]; rfl⟩

/-- DLMF §9.7(iii) for the even subseries of the `Ai`, `Bi` oscillatory expansions. -/
theorem airyDer_osc_even {x : ℝ} (hx : 0 < x) (N : ℕ) :
    ‖airyOscComponent false 0 x - airyOscSum false 0 N x‖ ≤
        ‖(-1 : ℂ) ^ N * (airyU (2 * N) : ℂ) / airyZetaComplex x ^ (2 * N)‖ ∧
      0 ≤ (airyOscComponent false 0 x - airyOscSum false 0 N x).re *
        ((-1 : ℝ) ^ N * airyU (2 * N)) := by
  obtain ⟨hp0, hpa, hm0, hma⟩ := airyDer_rot_data hx
  have hS : airyOscSum false 0 N x = ∑ j ∈ Finset.range N,
      (-1 : ℂ) ^ j * (airyU (2 * j) : ℂ) / airyZetaComplex x ^ (2 * j) := by
    simp [airyOscSum]
  have hre := (airyDer_comp_im false 0 hx)
  have hre' := airyDer_oscSum_im false 0 N hx
  rw [hS] at hre'
  rw [(airyDer_comp_false hx).1] at hre ⊢
  rw [hS]
  exact airyDer_even_bound _ (airyExpansionCoeff .ai) airyU (fun j => (airyDer_coeff_ai j).1) hx N
    (airyDer_ai_ratio' hp0 hpa _) (airyDer_ai_ratio' hm0 hma _)
    (by rw [sub_im, hre, hre', sub_zero])

/-- DLMF §9.7(iii) for the odd subseries of the `Ai`, `Bi` oscillatory expansions. -/
theorem airyDer_osc_odd {x : ℝ} (hx : 0 < x) (N : ℕ) :
    ‖airyOscComponent false 1 x - airyOscSum false 1 N x‖ ≤
        ‖(-1 : ℂ) ^ N * (airyU (2 * N + 1) : ℂ) / airyZetaComplex x ^ (2 * N + 1)‖ ∧
      0 ≤ (airyOscComponent false 1 x - airyOscSum false 1 N x).re *
        ((-1 : ℝ) ^ N * airyU (2 * N + 1)) := by
  obtain ⟨hp0, hpa, hm0, hma⟩ := airyDer_rot_data hx
  have hS : airyOscSum false 1 N x = ∑ j ∈ Finset.range N,
      (-1 : ℂ) ^ j * (airyU (2 * j + 1) : ℂ) / airyZetaComplex x ^ (2 * j + 1) := by
    simp [airyOscSum]
  have hre := (airyDer_comp_im false 1 hx)
  have hre' := airyDer_oscSum_im false 1 N hx
  rw [hS] at hre'
  rw [(airyDer_comp_false hx).2] at hre ⊢
  rw [hS]
  exact airyDer_odd_bound _ (airyExpansionCoeff .ai) airyU (fun j => (airyDer_coeff_ai j).2) hx N
    (airyDer_ai_ratio' hp0 hpa _) (airyDer_ai_ratio' hm0 hma _)
    (by rw [sub_im, hre, hre', sub_zero])



/-- The binomial coefficients of `(1+t)^{1/6}`: `d_k = (-1)^k (-1/6)_k / k!`. -/
def airyDer_d (k : ℕ) : ℝ :=
  (-1) ^ k * (ascPochhammer ℝ k).eval (-1 / 6) / k.factorial

/-- The binomial coefficient of `(1+t)^{-5/6}` is `(-1)^k (5/6)_k / k!`. -/
theorem airyDer_c_eq (k : ℕ) :
    airySt_coef (5 / 6) k = (-1) ^ k * (ascPochhammer ℝ k).eval (5 / 6) / k.factorial := by
  have h := airySt_gamma_ratio_real k (x := 5 / 6) (by norm_num)
  have g := Real.Gamma_pos_of_pos (show (0 : ℝ) < 5 / 6 by norm_num)
  unfold airySt_coef
  rw [Real.Gamma_nat_eq_factorial, ← h]
  have hf : (k.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  field_simp

/-- `d_0 = 1`. -/
theorem airyDer_d_zero : airyDer_d 0 = 1 := by simp [airyDer_d]

/-- The zeroth binomial coefficient of `(1+t)^{-5/6}` is `1`. -/
theorem airyDer_c_zero : airySt_coef (5 / 6) 0 = 1 := by simp [airyDer_c_eq]

/-- `d_{k+1} = c_{k+1} + c_k`, from `(1+t)^{1/6} = (1+t)(1+t)^{-5/6}`. -/
theorem airyDer_d_succ (k : ℕ) :
    airyDer_d (k + 1) = airySt_coef (5 / 6) (k + 1) + airySt_coef (5 / 6) k := by
  rw [airyDer_c_eq, airyDer_c_eq]
  unfold airyDer_d
  have h1 : (ascPochhammer ℝ (k + 1)).eval (-1 / 6) = (-1 / 6) * (ascPochhammer ℝ k).eval (5 / 6) := by
    rw [ascPochhammer_succ_left, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_comp,
      Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
    norm_num
  rw [h1, ascPochhammer_succ_eval, Nat.factorial_succ]
  have hf : (k.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  push_cast
  field_simp
  ring

/-- `Σ_{k≤N} d_k t^k = (1+t) Σ_{k≤N} c_k t^k - c_N t^{N+1}`. -/
theorem airyDer_sum_id (t : ℂ) (N : ℕ) :
    ∑ k ∈ Finset.range (N + 1), (airyDer_d k : ℂ) * t ^ k =
      (1 + t) * ∑ k ∈ Finset.range (N + 1), (airySt_coef (5 / 6) k : ℂ) * t ^ k -
        (airySt_coef (5 / 6) N : ℂ) * t ^ (N + 1) := by
  induction N with
  | zero => simp [airyDer_d_zero, airyDer_c_zero]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ (fun k => (airySt_coef (5 / 6) k : ℂ) * t ^ k)
      (N + 1), airyDer_d_succ]
    push_cast; ring


/-- The weight `τ^N (1-τ) τ^{-1/6} (1-τ)^{-5/6}` of the `(1+t)^{1/6}` remainder, normalized. -/
def airyDer_g (N : ℕ) (τ : ℝ) : ℝ :=
  1 / (Real.Gamma (5 / 6) * Real.Gamma (1 - 5 / 6)) * (τ ^ N * (1 - τ) * airySt_w (5 / 6) τ)

/-- The weight `airyDer_g N` is nonnegative on `(0,1)`. -/
theorem airyDer_g_nonneg (N : ℕ) {τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1) : 0 ≤ airyDer_g N τ := by
  have := Real.Gamma_pos_of_pos (show (0 : ℝ) < 5 / 6 by norm_num)
  have := Real.Gamma_pos_of_pos (show (0 : ℝ) < 1 - 5 / 6 by norm_num)
  unfold airyDer_g
  exact mul_nonneg (by positivity) (mul_nonneg (mul_nonneg (pow_nonneg hτ.1.le _)
    (by linarith [hτ.2])) (airySt_w_nonneg _ hτ))

/-- The weight `airyDer_g N` is measurable. -/
theorem airyDer_g_measurable (N : ℕ) : Measurable (airyDer_g N) := by
  unfold airyDer_g airySt_w; fun_prop

/-- `τ^N (1-τ) w(τ) = τ^N w(τ) - τ^{N+1} w(τ)`. -/
theorem airyDer_g_eq (N : ℕ) {τ : ℝ} :
    τ ^ N * (1 - τ) * airySt_w (5 / 6) τ = τ ^ N * airySt_w (5 / 6) τ -
      τ ^ (N + 1) * airySt_w (5 / 6) τ := by ring

/-- `τ^N (1-τ) w_{5/6}(τ)` is integrable on `(0,1)`. -/
theorem airyDer_integrableOn_g0 (N : ℕ) :
    IntegrableOn (fun τ : ℝ => τ ^ N * (1 - τ) * airySt_w (5 / 6) τ) (Ioo 0 1) := by
  have h := (airySt_integrableOn_w (a := 5 / 6) (by norm_num) (by norm_num) N).sub
    (airySt_integrableOn_w (a := 5 / 6) (by norm_num) (by norm_num) (N + 1))
  exact h.congr_fun (fun τ _ => (airyDer_g_eq N).symm) measurableSet_Ioo

/-- The weight `airyDer_g N` is integrable on `(0,1)`. -/
theorem airyDer_integrableOn_g (N : ℕ) : IntegrableOn (airyDer_g N) (Ioo 0 1) :=
  (airyDer_integrableOn_g0 N).const_mul _

/-- **The `(1+t)^{1/6}` binomial remainder in Stieltjes form**: after `N+1` terms it is
`-(-t)^{N+1} ∫₀¹ g_N(τ) (1+tτ)⁻¹ dτ` with the nonnegative weight `g_N`. -/
theorem airyDer_binom_rem {t : ℂ} (ht : 1 + t ∈ slitPlane) (N : ℕ) :
    (1 + t) ^ (((1 / 6 : ℝ)) : ℂ) - ∑ k ∈ Finset.range (N + 1), (airyDer_d k : ℂ) * t ^ k =
      -((-t) ^ (N + 1) * ∫ τ in Ioo (0 : ℝ) 1, (airyDer_g N τ : ℂ) * (1 + t * τ)⁻¹) := by
  have h1t : 1 + t ≠ 0 := slitPlane_ne_zero ht
  have hpow : (1 + t) ^ (((1 / 6 : ℝ)) : ℂ) = (1 + t) * (1 + t) ^ (-(((5 / 6 : ℝ)) : ℂ)) := by
    rw [show (((1 / 6 : ℝ)) : ℂ) = 1 + -(((5 / 6 : ℝ)) : ℂ) by push_cast; ring, cpow_add _ _ h1t,
      cpow_one]
  have hb := airySt_binom_rem (a := 5 / 6) (by norm_num) (by norm_num) ht (N + 1)
  set c' : ℝ := 1 / (Real.Gamma (5 / 6) * Real.Gamma (1 - 5 / 6)) with hc'
  have hne : ∀ τ ∈ Ioo (0 : ℝ) 1, 1 + t * τ ≠ 0 := fun τ hτ =>
    slitPlane_ne_zero (airySt_one_add_mul_mem ht (Ioo_subset_Icc_self hτ))
  have hcont : ContinuousOn (fun τ : ℝ => (1 + t * τ)⁻¹) (Icc 0 1) :=
    ContinuousOn.inv₀ (by fun_prop) fun τ hτ => slitPlane_ne_zero (airySt_one_add_mul_mem ht hτ)
  have hi1 : IntegrableOn (fun τ : ℝ => ((τ ^ N * airySt_w (5 / 6) τ : ℝ) : ℂ)) (Ioo 0 1) :=
    (airySt_integrableOn_w (by norm_num) (by norm_num) N).ofReal
  have hi2 : IntegrableOn (fun τ : ℝ => ((τ ^ N * (1 - τ) * airySt_w (5 / 6) τ : ℝ) : ℂ) *
      (1 + t * τ)⁻¹) (Ioo 0 1) :=
    ((airyDer_integrableOn_g0 N).ofReal).mul_continuousOn_of_subset hcont measurableSet_Ioo
      isCompact_Icc Ioo_subset_Icc_self
  have hkey : (1 + t) * ∫ τ in Ioo (0 : ℝ) 1, ((τ ^ (N + 1) * airySt_w (5 / 6) τ : ℝ) : ℂ) *
      (1 + t * τ)⁻¹ = (∫ τ in Ioo (0 : ℝ) 1, ((τ ^ N * airySt_w (5 / 6) τ : ℝ) : ℂ)) -
        ∫ τ in Ioo (0 : ℝ) 1, ((τ ^ N * (1 - τ) * airySt_w (5 / 6) τ : ℝ) : ℂ) *
          (1 + t * τ)⁻¹ := by
    rw [← integral_const_mul, ← integral_sub hi1 hi2]
    refine setIntegral_congr_fun measurableSet_Ioo fun τ hτ => ?_
    have h := hne τ hτ
    push_cast
    field_simp
    ring
  have hmom : (c' : ℂ) * ∫ τ in Ioo (0 : ℝ) 1, ((τ ^ N * airySt_w (5 / 6) τ : ℝ) : ℂ) =
      (-1) ^ N * (airySt_coef (5 / 6) N : ℂ) := by
    have h1 : Real.Gamma (1 - 5 / 6) ≠ 0 := (Real.Gamma_pos_of_pos (by norm_num)).ne'
    have h2 : Real.Gamma (5 / 6) ≠ 0 := (Real.Gamma_pos_of_pos (by norm_num)).ne'
    have h3 : Real.Gamma (N + 1) ≠ 0 := (Real.Gamma_pos_of_pos (by positivity)).ne'
    have hr : c' * (Real.Gamma (5 / 6 + N) * Real.Gamma (1 - 5 / 6) / Real.Gamma (N + 1)) =
        (-1) ^ N * airySt_coef (5 / 6) N := by
      rw [airySt_coef, show (-1 : ℝ) ^ N * ((-1) ^ N * Real.Gamma (5 / 6 + N) /
          (Real.Gamma (5 / 6) * Real.Gamma (N + 1))) = ((-1) ^ N * (-1) ^ N) *
            Real.Gamma (5 / 6 + N) / (Real.Gamma (5 / 6) * Real.Gamma (N + 1)) by ring,
        ← mul_pow, hc']
      norm_num
      field_simp
    rw [integral_complex_ofReal, airySt_moment (by norm_num) (by norm_num) N]
    exact_mod_cast hr
  have hg : ∫ τ in Ioo (0 : ℝ) 1, (airyDer_g N τ : ℂ) * (1 + t * τ)⁻¹ = (c' : ℂ) *
      ∫ τ in Ioo (0 : ℝ) 1, ((τ ^ N * (1 - τ) * airySt_w (5 / 6) τ : ℝ) : ℂ) * (1 + t * τ)⁻¹ := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
    simp only [airyDer_g, hc']; push_cast; ring
  rw [hpow, airyDer_sum_id, hg]
  have hb' : (1 + t) ^ (-(((5 / 6 : ℝ)) : ℂ)) = ∑ k ∈ Finset.range (N + 1),
      (airySt_coef (5 / 6) k : ℂ) * t ^ k + (-t) ^ (N + 1) * ((c' : ℂ) *
        ∫ τ in Ioo (0 : ℝ) 1, ((τ ^ (N + 1) * airySt_w (5 / 6) τ : ℝ) : ℂ) * (1 + t * τ)⁻¹) := by
    rw [← hb]; ring
  rw [hb']
  have e : (1 + t) * ((-t) ^ (N + 1) * ((c' : ℂ) * ∫ τ in Ioo (0 : ℝ) 1,
      ((τ ^ (N + 1) * airySt_w (5 / 6) τ : ℝ) : ℂ) * (1 + t * τ)⁻¹)) =
      (-t) ^ (N + 1) * ((c' : ℂ) * ∫ τ in Ioo (0 : ℝ) 1, ((τ ^ N * airySt_w (5 / 6) τ : ℝ) : ℂ)) -
      (-t) ^ (N + 1) * ((c' : ℂ) * ∫ τ in Ioo (0 : ℝ) 1,
        ((τ ^ N * (1 - τ) * airySt_w (5 / 6) τ : ℝ) : ℂ) * (1 + t * τ)⁻¹) := by
    rw [← mul_sub, ← mul_sub, ← hkey]; ring
  have hm : ((-1 : ℂ) ^ N) * (-1) ^ N = 1 := by rw [← mul_pow]; norm_num
  rw [mul_add, e, hmom, neg_pow t (N + 1)]
  linear_combination (-(airySt_coef (5 / 6) N : ℂ) * t ^ (N + 1)) * hm


/-- `2 · 3^{1/6} e^{(4/3)L} = e^{(7/6)(log 2 + L)} z^{1/4}`. -/
theorem airyDer_norm_const {z : ℂ} (hz : z ≠ 0) :
    2 * (3 : ℂ) ^ (1 / 6 : ℂ) * exp (4 / 3 * airyLogZeta z) =
      exp ((7 / 6 : ℂ) * (log 2 + airyLogZeta z)) * z ^ (1 / 4 : ℂ) := by
  rw [cpow_def_of_ne_zero hz, cpow_def_of_ne_zero (by norm_num : (3 : ℂ) ≠ 0), airyLogZeta,
    log_two_thirds]
  calc 2 * exp (log 3 * (1 / 6)) * exp (4 / 3 * (log 2 - log 3 + 3 / 2 * log z))
      = exp (log 2) * exp (log 3 * (1 / 6)) * exp (4 / 3 * (log 2 - log 3 + 3 / 2 * log z)) := by
        rw [exp_log two_ne_zero]
    _ = _ := by simp only [← exp_add]; congr 1; ring

/-- **The normalized `Ai'` as a rotated Laplace integral** of `t^{1/6}(1+t)^{1/6}`. -/
theorem airyDer_G_eq {z : ℂ} (hz : z ≠ 0) {θ : ℝ} (hθ : |θ| < π)
    (hzθ : |3 / 2 * arg z + θ| < π / 2) :
    airyAiDeriv z / airyPrefactor .aiDeriv z = exp ((7 / 6 : ℂ) * (log 2 + airyLogZeta z)) *
      (1 / Gamma ((7 / 6 : ℝ) : ℂ) * (exp (θ * I) *
        airyRot_lap (7 / 6) (1 / 6) θ (exp (log 2 + airyLogZeta z + θ * I)))) := by
  have hπ : (Real.sqrt π : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hq : z ^ (1 / 4 : ℂ) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hz)
  rw [airyRot_eq_of_anchor (hf := fun w => (hasDerivAt_airyAiDeriv w).differentiableAt) _ _
    (7 / 6) (1 / 6) (by norm_num) (fun w hw harg => airyRot_airyAiDeriv_anchor hw harg) hθ hz hzθ]
  have hN : exp ((7 / 6 : ℂ) * (log 2 + airyLogZeta z)) =
      2 * (3 : ℂ) ^ (1 / 6 : ℂ) * exp (4 / 3 * airyLogZeta z) / z ^ (1 / 4 : ℂ) :=
    (eq_div_iff hq).mpr (airyDer_norm_const hz).symm
  rw [hN]
  simp only [airyPrefactor]
  generalize airyRot_lap (7 / 6) (1 / 6) θ (exp (log 2 + airyLogZeta z + θ * I)) = K
  have hG : Gamma ((7 / 6 : ℝ) : ℂ) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp)
  rw [exp_sub, exp_neg]
  have hE : exp (airyZetaComplex z) ≠ 0 := exp_ne_zero _
  field_simp

/-- The `Ai'` coefficients: `d_k Γ(7/6+k)/Γ(7/6) = (-1)^k v_k 2^k`. -/
theorem airyDer_coef_aiDeriv (k : ℕ) :
    airyDer_d k * Real.Gamma (7 / 6 + k) / Real.Gamma (7 / 6) = (-1) ^ k * airyV k * 2 ^ k := by
  have h1 := airySt_gamma_ratio_real k (x := 7 / 6) (by norm_num)
  rw [mul_div_assoc, h1, airyRot_poch_seven_sixths]
  unfold airyDer_d airyV airyU
  rw [← airyRot_poch_neg_sixth]
  have hf : (k.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  have h6 : (1 - 6 * (k : ℝ)) ≠ 0 := by
    intro h
    have h' : (6 * k : ℝ) = 1 := by linarith
    have : (6 * k : ℕ) = 1 := by exact_mod_cast h'
    omega
  field_simp

/-- The terms of the `Ai'` ray expansion. -/
def airyDer_T (θ W : ℝ) (k : ℕ) : ℂ :=
  (airyDer_d k : ℂ) * exp (θ * I * (((7 / 6 : ℝ) : ℂ) - 1 + k)) *
    (Gamma (((7 / 6 : ℝ) : ℂ) + k) * (W : ℂ) ^ (-(((7 / 6 : ℝ) : ℂ) + k)))

/-- The `Ai'` ray Laplace integral of `t^{1/6}(1+t)^{1/6}`. -/
def airyDer_L (θ W : ℝ) : ℂ :=
  ∫ r in Ioi (0 : ℝ), Complex.exp (-(W * r)) * (((r : ℂ) * exp (θ * I)) ^ (((7 / 6 : ℝ) : ℂ) - 1) *
    (1 + (r : ℂ) * exp (θ * I)) ^ (((1 / 6 : ℝ)) : ℂ))

/-- The rotated Laplace integral of `t^{1/6}(1+t)^{1/6}` is `airyDer_L`. -/
theorem airyDer_lap_eq (θ W : ℝ) :
    airyRot_lap (7 / 6) (1 / 6) θ (W : ℂ) = airyDer_L θ W := by
  unfold airyRot_lap airyDer_L airyRot_kernel
  rfl

/-- Integrability of `e^{-Wr} t^{1/6} (1+t)^{1/6}`, `t = r e^{iθ}`, for `|θ| < π`. -/
theorem airyDer_hint {θ W : ℝ} (hθ : |θ| < π) (hW : 0 < W) :
    IntegrableOn (fun r : ℝ => Complex.exp (-(W * r)) *
      (((r : ℂ) * exp (θ * I)) ^ (((7 / 6 : ℝ) : ℂ) - 1) *
        (1 + (r : ℂ) * exp (θ * I)) ^ (((1 / 6 : ℝ)) : ℂ))) (Ioi 0) := by
  have h := airyRot_integrableOn (7 / 6) (1 / 6) (by norm_num) hθ hW
  refine h.congr_fun (fun r _ => ?_) measurableSet_Ioi
  simp only [airyRot_kernel, Complex.real_smul, ofReal_exp]
  push_cast; ring_nf

/-- **Exact remainder of the `Ai'` ray expansion** after `N+1` terms. -/
theorem airyDer_rem_repr {W θ : ℝ} (hW : 0 < W) (hθ : |θ| < π) (N : ℕ) :
    airyDer_L θ W - ∑ k ∈ Finset.range (N + 1), airyDer_T θ W k =
      -∫ r in Ioi (0 : ℝ), Complex.exp (-(W * r)) *
        (((r : ℂ) * exp (θ * I)) ^ (((7 / 6 : ℝ) : ℂ) - 1) *
        ((-((r : ℂ) * exp (θ * I))) ^ (N + 1) * ∫ τ in Ioo (0 : ℝ) 1,
          (airyDer_g N τ : ℂ) * (1 + ((r : ℂ) * exp (θ * I)) * τ)⁻¹)) := by
  have hb : (0 : ℝ) < 7 / 6 := by norm_num
  have hT : ∀ k, airyDer_T θ W k = ∫ r in Ioi (0 : ℝ), (airyDer_d k : ℂ) *
      (Complex.exp (-(W * r)) * (((r : ℂ) * exp (θ * I)) ^ (((7 / 6 : ℝ) : ℂ) - 1) *
        ((r : ℂ) * exp (θ * I)) ^ k)) := by
    intro k
    rw [integral_const_mul, airySt_term_integral hb hW hθ k, airyDer_T]
    ring
  simp_rw [hT]
  rw [← integral_finsetSum _ (fun k _ => (airySt_term_integrableOn hb hW hθ k).const_mul _),
    airyDer_L, ← integral_neg, ← integral_sub (airyDer_hint hθ hW) (integrable_finsetSum _ fun k _ =>
      (airySt_term_integrableOn hb hW hθ k).const_mul _)]
  refine setIntegral_congr_fun measurableSet_Ioi (fun r hr => ?_)
  have hr : (0 : ℝ) ≤ r := le_of_lt hr
  have h := airyDer_binom_rem (airySt_one_add_mem hr hθ) N
  have hs : ∑ k ∈ Finset.range (N + 1), (airyDer_d k : ℂ) * (Complex.exp (-(W * r)) *
      (((r : ℂ) * exp (θ * I)) ^ (((7 / 6 : ℝ) : ℂ) - 1) * ((r : ℂ) * exp (θ * I)) ^ k)) =
      Complex.exp (-(W * r)) * ((r : ℂ) * exp (θ * I)) ^ (((7 / 6 : ℝ) : ℂ) - 1) *
        ∑ k ∈ Finset.range (N + 1), (airyDer_d k : ℂ) * ((r : ℂ) * exp (θ * I)) ^ k := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
  rw [hs]
  linear_combination (Complex.exp (-(W * r)) *
    ((r : ℂ) * exp (θ * I)) ^ (((7 / 6 : ℝ) : ℂ) - 1)) * h


/-- **Ai' remainder as a ray remainder** on `|arg z| < 2π/3`, with ray `θ = -(3/2) arg z`. -/
theorem airyDer_aiDeriv_remainder {z : ℂ} (hz : z ≠ 0) (harg : |arg z| < 2 * π / 3) (N : ℕ) :
    airyRemainder .aiDeriv N z = exp ((7 / 6 : ℂ) * (log 2 + airyLogZeta z)) *
        (1 / Gamma ((7 / 6 : ℝ) : ℂ)) * exp (((-(3 / 2 * arg z) : ℝ) : ℂ) * I) *
      (airyDer_L (-(3 / 2 * arg z)) (Real.exp (log 2 + airyLogZeta z).re) -
        ∑ k ∈ Finset.range N, airyDer_T (-(3 / 2 * arg z))
          (Real.exp (log 2 + airyLogZeta z).re) k) ∧
    ∀ k : ℕ, airyExpansionCoeff .aiDeriv k / airyZetaComplex z ^ k =
      exp ((7 / 6 : ℂ) * (log 2 + airyLogZeta z)) *
        (1 / Gamma ((7 / 6 : ℝ) : ℂ)) * exp (((-(3 / 2 * arg z) : ℝ) : ℂ) * I) *
      airyDer_T (-(3 / 2 * arg z)) (Real.exp (log 2 + airyLogZeta z).re) k := by
  set θ : ℝ := -(3 / 2 * arg z) with hθdef
  set ℓ := log 2 + airyLogZeta z with hℓdef
  set W : ℝ := Real.exp ℓ.re with hWdef
  have hθ : |θ| < π := by
    rw [hθdef, abs_neg, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)]; linarith
  have hzθ : |3 / 2 * arg z + θ| < π / 2 := by
    rw [hθdef, add_neg_cancel, abs_zero]; positivity
  have hF := airyDer_G_eq hz hθ hzθ
  rw [airySt_W_real, airyDer_lap_eq] at hF
  have hG : Gamma ((7 / 6 : ℝ) : ℂ) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp)
  have hcT : ∀ k : ℕ, airyExpansionCoeff .aiDeriv k / airyZetaComplex z ^ k =
      exp ((7 / 6 : ℂ) * ℓ) * (1 / Gamma ((7 / 6 : ℝ) : ℂ)) * exp (θ * I) *
        airyDer_T θ W k := by
    intro k
    have hℓ : ℓ = (ℓ.re : ℂ) + ((-θ : ℝ) : ℂ) * I := by
      have h := im_log_two_add_airyLogZeta z
      simp only [add_im] at h
      apply Complex.ext
      · simp
      · simp [hℓdef, hθdef, h]
    have hWc : (W : ℂ) ^ (-(((7 / 6 : ℝ) : ℂ) + k)) =
        exp (-(((7 / 6 : ℝ) : ℂ) + k) * (ℓ.re : ℂ)) := by
      rw [hWdef, ofReal_exp, cpow_def_of_ne_zero (exp_ne_zero _), log_exp (by simp [Real.pi_pos])
        (by simp [Real.pi_pos.le]), mul_comm]
    have hζ : airyZetaComplex z = exp ℓ / 2 := by
      rw [hℓdef, exp_log_two_add_airyLogZeta hz]; ring
    have hc := airyDer_coef_aiDeriv k
    have hgk : Gamma (((7 / 6 : ℝ) : ℂ) + k) = ((Real.Gamma (7 / 6 + k) : ℝ) : ℂ) := by
      rw [← Complex.Gamma_ofReal]; push_cast; rfl
    have hg0 : Gamma ((7 / 6 : ℝ) : ℂ) = ((Real.Gamma (7 / 6) : ℝ) : ℂ) := by
      rw [← Complex.Gamma_ofReal]
    have hc' : ((-1 : ℂ) ^ k * (airyV k : ℂ)) = (airyDer_d k : ℂ) *
        Gamma (((7 / 6 : ℝ) : ℂ) + k) / Gamma ((7 / 6 : ℝ) : ℂ) / 2 ^ k := by
      rw [hgk, hg0]
      have : ((airyDer_d k * Real.Gamma (7 / 6 + k) / Real.Gamma (7 / 6) : ℝ) : ℂ) =
          (((-1) ^ k * airyV k * 2 ^ k : ℝ) : ℂ) := by rw [hc]
      push_cast at this
      rw [this]; field_simp
    have key : exp ((7 / 6 : ℂ) * ℓ) * exp (θ * I) * exp (θ * I * (((7 / 6 : ℝ) : ℂ) - 1 + k)) *
        exp (-(((7 / 6 : ℝ) : ℂ) + k) * (ℓ.re : ℂ)) * exp (k * ℓ) = 1 := by
      rw [← exp_add, ← exp_add, ← exp_add, ← exp_add]
      convert exp_zero using 2
      generalize ℓ.re = R at hℓ ⊢
      rw [hℓ]; push_cast; ring
    simp only [airyExpansionCoeff, airyDer_T]
    rw [hc', hWc, hζ, div_pow, ← Complex.exp_nat_mul]
    generalize exp ((7 / 6 : ℂ) * ℓ) = E1 at key ⊢
    generalize exp (θ * I) = E2 at key ⊢
    generalize exp (θ * I * (((7 / 6 : ℝ) : ℂ) - 1 + k)) = E3 at key ⊢
    generalize exp (-(((7 / 6 : ℝ) : ℂ) + k) * (ℓ.re : ℂ)) = E4 at key ⊢
    have hE5 : exp (k * ℓ) ≠ 0 := exp_ne_zero _
    generalize exp (k * ℓ) = E5 at key hE5 ⊢
    field_simp
    linear_combination (-((airyDer_d k : ℂ) * Gamma (((7 / 6 : ℝ) : ℂ) + k))) * key
  refine ⟨?_, hcT⟩
  rw [airyRemainder, airyFunction, hF, airyExponentialSum]
  simp_rw [hcT]
  rw [← Finset.mul_sum]
  ring

/-- `∫ g_N = (-1)^N d_{N+1}`. -/
theorem airyDer_int_g (N : ℕ) :
    ∫ τ in Ioo (0 : ℝ) 1, airyDer_g N τ = (-1) ^ N * airyDer_d (N + 1) := by
  unfold airyDer_g
  rw [integral_const_mul, setIntegral_congr_fun measurableSet_Ioo (fun τ _ => airyDer_g_eq N),
    integral_sub (airySt_integrableOn_w (by norm_num) (by norm_num) N)
      (airySt_integrableOn_w (by norm_num) (by norm_num) (N + 1)),
    airySt_moment (by norm_num) (by norm_num), airySt_moment (by norm_num) (by norm_num)]
  have h1 := airySt_gamma_ratio_real N (x := 5 / 6) (by norm_num)
  have h2 := airySt_gamma_ratio_real (N + 1) (x := 5 / 6) (by norm_num)
  have g1 := Real.Gamma_pos_of_pos (show (0 : ℝ) < 5 / 6 by norm_num)
  have g2 := Real.Gamma_pos_of_pos (show (0 : ℝ) < 1 - 5 / 6 by norm_num)
  rw [div_eq_iff g1.ne'] at h1 h2
  rw [h1, h2, Real.Gamma_nat_eq_factorial, Real.Gamma_nat_eq_factorial]
  unfold airyDer_d
  have h3 : (ascPochhammer ℝ (N + 1)).eval (-1 / 6) =
      (-1 / 6) * (ascPochhammer ℝ N).eval (5 / 6) := by
    rw [ascPochhammer_succ_left, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_comp,
      Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
    norm_num
  rw [h3, ascPochhammer_succ_eval, Nat.factorial_succ]
  have hf : (N.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr N.factorial_ne_zero
  have hm : ((-1 : ℝ) ^ N) * (-1) ^ N = 1 := by rw [← mul_pow]; norm_num
  push_cast
  field_simp
  linear_combination (-(ascPochhammer ℝ N).eval (5 / 6)) * hm


/-- **The Ai' remainder on `|arg z| ≤ π/3`** after `N+1` terms is `(A + iB)` times the first
neglected term, `0 ≤ A ≤ 1`. -/
theorem airyDer_aiDeriv_ratio {z : ℂ} (hz : z ≠ 0) (harg : |arg z| ≤ π / 3) (N : ℕ) :
    ∃ A B : ℝ, 0 ≤ A ∧ A ≤ 1 ∧ airyRemainder .aiDeriv (N + 1) z =
      (A + B * I) * (airyExpansionCoeff .aiDeriv (N + 1) / airyZetaComplex z ^ (N + 1)) := by
  have hπ := Real.pi_pos
  have harg' : |arg z| < 2 * π / 3 := by linarith
  obtain ⟨h1, h2⟩ := airyDer_aiDeriv_remainder hz harg' (N + 1)
  have hθ := airySt_theta_lt harg'
  have hcos : 0 ≤ Real.cos (-(3 / 2 * arg z)) := by
    rw [Real.cos_neg]
    exact Real.cos_nonneg_of_mem_Icc ⟨by linarith [(abs_le.mp harg).1],
      by linarith [(abs_le.mp harg).2]⟩
  have hW : 0 < Real.exp (log 2 + airyLogZeta z).re := Real.exp_pos _
  rw [h1, h2, airyDer_rem_repr hW hθ N]
  obtain ⟨A, B, hA0, hA1, hE⟩ := airyDer_ray_ratio (b := 7 / 6) (by norm_num) hW hθ hcos (N + 1)
    (airyDer_g_measurable N) (fun τ hτ => airyDer_g_nonneg N hτ) (airyDer_integrableOn_g N)
  refine ⟨A, B, hA0, hA1, ?_⟩
  have hs : ((-1 : ℝ) ^ (N + 1) * ((-1) ^ N * airyDer_d (N + 1))) = -airyDer_d (N + 1) := by
    rw [pow_succ, show (-1 : ℝ) ^ N * -1 * ((-1) ^ N * airyDer_d (N + 1)) =
      -(((-1) ^ N * (-1) ^ N) * airyDer_d (N + 1)) by ring, ← mul_pow]
    norm_num
  rw [hE, airyDer_int_g, hs]
  unfold airyDer_T
  push_cast
  ring

/-- `cos (w - π/4)` and `-sin (w - π/4)` through `e^{∓iw}`, second form. -/
theorem airyDer_cos_sin' (w : ℂ) :
    cos (w - π / 4) = I * (exp (-(π * I / 4)) / 2 * exp (-(w * I)) -
        exp (π * I / 4) / 2 * exp (w * I)) ∧
      -sin (w - π / 4) = exp (-(π * I / 4)) / 2 * exp (-(w * I)) +
        exp (π * I / 4) / 2 * exp (w * I) := by
  rw [show cos (w - π / 4) = sin (w - π / 4 + π / 2) from (Complex.sin_add_pi_div_two _).symm,
    show sin (w - π / 4) = -cos (w - π / 4 + π / 2) by rw [Complex.cos_add_pi_div_two]; ring]
  simp only [Complex.cos, Complex.sin]
  have e1 : exp ((w - π / 4 + π / 2) * I) = exp (π * I / 4) * exp (w * I) := by
    rw [← exp_add]; congr 1; ring
  have e2 : exp (-(w - π / 4 + π / 2) * I) = exp (-(π * I / 4)) * exp (-(w * I)) := by
    rw [← exp_add]; congr 1; ring
  rw [e1, e2]
  constructor
  · field_simp
  · ring

/-- `Ai'(-z)` through the even and odd parts of the normalized `Ai'`, exactly (DLMF 9.7.10). -/
theorem airyDer_airyAiDeriv_neg {z : ℂ} (hz0 : z ≠ 0) (hz3 : |arg z| < 2 * π / 3) :
    airyAiDeriv (-z) = airyOscPrefactor .aiDeriv z *
      (sin (airyZetaComplex z - π / 4) *
          airyRot_even (fun w => airyAiDeriv w / airyPrefactor .aiDeriv w) z -
        cos (airyZetaComplex z - π / 4) *
          airyRot_odd (fun w => airyAiDeriv w / airyPrefactor .aiDeriv w) z) := by
  obtain ⟨u4, um4, u3, um3, u2, um2, u12⟩ := airyRot_u_powers
  set u := exp (π * I / 12) with hu
  have hu0 : u ≠ 0 := exp_ne_zero _
  obtain ⟨d1, d2, d3, d4⟩ := airyRot_third_data hz0 hz3
  have hπs : (Real.sqrt π : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hq : z ^ (1 / 4 : ℂ) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hz0)
  have hp1 := airyRot_prefactor_ne_zero .aiDeriv
    (mul_ne_zero hz0 (exp_ne_zero ((π / 3 : ℝ) * I)))
  have hp2 := airyRot_prefactor_ne_zero .aiDeriv
    (mul_ne_zero hz0 (exp_ne_zero ((-(π / 3) : ℝ) * I)))
  obtain ⟨hc, hs⟩ := airyDer_cos_sin' (airyZetaComplex z)
  rw [show sin (airyZetaComplex z - π / 4) = -(-sin (airyZetaComplex z - π / 4)) by ring, hs, hc]
  rw [airyRot_airyAiDeriv_neg z]
  rw [show airyAiDeriv (z * exp ((π / 3 : ℝ) * I)) =
      airyPrefactor .aiDeriv (z * exp ((π / 3 : ℝ) * I)) *
      (airyAiDeriv (z * exp ((π / 3 : ℝ) * I)) /
        airyPrefactor .aiDeriv (z * exp ((π / 3 : ℝ) * I))) by field_simp,
    show airyAiDeriv (z * exp ((-(π / 3) : ℝ) * I)) =
      airyPrefactor .aiDeriv (z * exp ((-(π / 3) : ℝ) * I)) *
      (airyAiDeriv (z * exp ((-(π / 3) : ℝ) * I)) /
        airyPrefactor .aiDeriv (z * exp ((-(π / 3) : ℝ) * I))) by field_simp]
  rw [← mul_assoc, ← mul_assoc]
  rw [airyRot_decomp (fun w => airyAiDeriv w / airyPrefactor .aiDeriv w)]
  have ep : exp (-π * I / 3) * airyPrefactor .aiDeriv (z * exp ((π / 3 : ℝ) * I)) =
      airyOscPrefactor .aiDeriv z *
        (-(exp (-(π * I / 4)) / 2) * exp (-(airyZetaComplex z * I))) := by
    simp only [airyPrefactor, airyOscPrefactor]
    rw [d1, d3, ← hu, um4, um3]
    field_simp
  have em : exp (π * I / 3) * airyPrefactor .aiDeriv (z * exp ((-(π / 3) : ℝ) * I)) =
      airyOscPrefactor .aiDeriv z * (-(exp (π * I / 4) / 2) * exp (airyZetaComplex z * I)) := by
    simp only [airyPrefactor, airyOscPrefactor]
    rw [d2, d4, ← hu, u4, u3, neg_neg]
    field_simp
  rw [ep, em]
  ring

/-- `Bi'(-z)` through the even and odd parts of the normalized `Ai'`, exactly (DLMF 9.7.12). -/
theorem airyDer_airyBiDeriv_neg {z : ℂ} (hz0 : z ≠ 0) (hz3 : |arg z| < 2 * π / 3) :
    airyBiDeriv (-z) = airyOscPrefactor .aiDeriv z *
      (cos (airyZetaComplex z - π / 4) *
          airyRot_even (fun w => airyAiDeriv w / airyPrefactor .aiDeriv w) z +
        sin (airyZetaComplex z - π / 4) *
          airyRot_odd (fun w => airyAiDeriv w / airyPrefactor .aiDeriv w) z) := by
  obtain ⟨u4, um4, u3, um3, u2, um2, u12⟩ := airyRot_u_powers
  set u := exp (π * I / 12) with hu
  have hu0 : u ≠ 0 := exp_ne_zero _
  obtain ⟨d1, d2, d3, d4⟩ := airyRot_third_data hz0 hz3
  have hπs : (Real.sqrt π : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hq : z ^ (1 / 4 : ℂ) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hz0)
  have hp1 := airyRot_prefactor_ne_zero .aiDeriv
    (mul_ne_zero hz0 (exp_ne_zero ((π / 3 : ℝ) * I)))
  have hp2 := airyRot_prefactor_ne_zero .aiDeriv
    (mul_ne_zero hz0 (exp_ne_zero ((-(π / 3) : ℝ) * I)))
  obtain ⟨hc, hs⟩ := airyDer_cos_sin (airyZetaComplex z)
  rw [hc, hs]
  rw [airyRot_airyBiDeriv_neg z]
  rw [show airyAiDeriv (z * exp ((π / 3 : ℝ) * I)) =
      airyPrefactor .aiDeriv (z * exp ((π / 3 : ℝ) * I)) *
      (airyAiDeriv (z * exp ((π / 3 : ℝ) * I)) /
        airyPrefactor .aiDeriv (z * exp ((π / 3 : ℝ) * I))) by field_simp,
    show airyAiDeriv (z * exp ((-(π / 3) : ℝ) * I)) =
      airyPrefactor .aiDeriv (z * exp ((-(π / 3) : ℝ) * I)) *
      (airyAiDeriv (z * exp ((-(π / 3) : ℝ) * I)) /
        airyPrefactor .aiDeriv (z * exp ((-(π / 3) : ℝ) * I))) by field_simp]
  rw [← mul_assoc, ← mul_assoc]
  rw [airyRot_decomp (fun w => airyAiDeriv w / airyPrefactor .aiDeriv w)]
  have ep : -exp (π * I / 6) * airyPrefactor .aiDeriv (z * exp ((π / 3 : ℝ) * I)) =
      airyOscPrefactor .aiDeriv z *
        (exp (π * I / 4) / 2 * exp (-(airyZetaComplex z * I))) := by
    simp only [airyPrefactor, airyOscPrefactor]
    rw [d1, d3, ← hu, u2, u3]
    field_simp
  have em : -exp (-π * I / 6) * airyPrefactor .aiDeriv (z * exp ((-(π / 3) : ℝ) * I)) =
      airyOscPrefactor .aiDeriv z * (exp (-(π * I / 4)) / 2 * exp (airyZetaComplex z * I)) := by
    simp only [airyPrefactor, airyOscPrefactor]
    rw [d2, d4, ← hu, um2, um3, neg_neg]
    field_simp
  rw [ep, em]
  ring

/-- The derivative components are the even and odd parts of the normalized `Ai'`. -/
theorem airyDer_comp_true {x : ℝ} (hx : 0 < x) :
    airyOscComponent true 0 x =
        airyRot_even (fun w => airyAiDeriv w / airyPrefactor .aiDeriv w) x ∧
    airyOscComponent true 1 x =
        airyRot_odd (fun w => airyAiDeriv w / airyPrefactor .aiDeriv w) x := by
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have harg : |arg (x : ℂ)| < 2 * π / 3 := by
    rw [arg_ofReal_of_nonneg hx.le, abs_zero]; positivity
  have hA := airyDer_airyAiDeriv_neg hx0 harg
  have hB := airyDer_airyBiDeriv_neg hx0 harg
  rw [airyReal_zeta_ofReal hx] at hA hB
  have hP : airyOscPrefactor .aiDeriv (x : ℂ) ≠ 0 := by
    simp only [airyOscPrefactor]
    have hπs : (Real.sqrt π : ℂ) ≠ 0 :=
      ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
    have hq : (x : ℂ) ^ (1 / 4 : ℂ) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hx0)
    exact div_ne_zero hq hπs
  have hcs := Complex.cos_sq_add_sin_sq (((airyZeta x : ℝ) : ℂ) - π / 4)
  simp only [airyOscComponent, ite_true, Fin.val_zero, Fin.val_one, one_ne_zero, ite_false]
  rw [hA, hB]
  constructor
  · rw [div_eq_iff hP]
    linear_combination (airyOscPrefactor .aiDeriv (x : ℂ) *
      airyRot_even (fun w => airyAiDeriv w / airyPrefactor .aiDeriv w) x) * hcs
  · rw [div_eq_iff hP]
    linear_combination (airyOscPrefactor .aiDeriv (x : ℂ) *
      airyRot_odd (fun w => airyAiDeriv w / airyPrefactor .aiDeriv w) x) * hcs

/-- The `Ai'` coefficients: even ones are `v_{2j}`, odd ones `-v_{2j+1}`. -/
theorem airyDer_coeff_aiDeriv (j : ℕ) :
    airyExpansionCoeff .aiDeriv (2 * j) = airyV (2 * j) ∧
      airyExpansionCoeff .aiDeriv (2 * j + 1) = -(airyV (2 * j + 1) : ℂ) := by
  have h := airyRot_coeff_parity .aiDeriv (Or.inr rfl) j
  simpa using h

/-- For `|arg w| ≤ π/3` and `M ≥ 1` the `Ai'` remainder is `(A + iB)` times the first
neglected term with `0 ≤ A ≤ 1`. -/
theorem airyDer_aiDeriv_ratio' {w : ℂ} (hw : w ≠ 0) (harg : |arg w| ≤ π / 3) {M : ℕ} (hM : 1 ≤ M) :
    ∃ A B : ℝ, 0 ≤ A ∧ A ≤ 1 ∧ airyAiDeriv w / airyPrefactor .aiDeriv w -
      ∑ k ∈ Finset.range M, airyExpansionCoeff .aiDeriv k / airyZetaComplex w ^ k =
        (A + B * I) * (airyExpansionCoeff .aiDeriv M / airyZetaComplex w ^ M) := by
  obtain ⟨K, rfl⟩ : ∃ K, M = K + 1 := ⟨M - 1, by omega⟩
  obtain ⟨A, B, h0, h1, h⟩ := airyDer_aiDeriv_ratio hw harg K
  exact ⟨A, B, h0, h1, by rw [← h]; rfl⟩

/-- DLMF §9.7(iii) for the even subseries of the `Ai'`, `Bi'` oscillatory expansions. -/
theorem airyDer_osc_even_deriv {x : ℝ} (hx : 0 < x) {N : ℕ} (hN : 1 ≤ N) :
    ‖airyOscComponent true 0 x - airyOscSum true 0 N x‖ ≤
        ‖(-1 : ℂ) ^ N * (airyV (2 * N) : ℂ) / airyZetaComplex x ^ (2 * N)‖ ∧
      0 ≤ (airyOscComponent true 0 x - airyOscSum true 0 N x).re *
        ((-1 : ℝ) ^ N * airyV (2 * N)) := by
  obtain ⟨hp0, hpa, hm0, hma⟩ := airyDer_rot_data hx
  have hS : airyOscSum true 0 N x = ∑ j ∈ Finset.range N,
      (-1 : ℂ) ^ j * (airyV (2 * j) : ℂ) / airyZetaComplex x ^ (2 * j) := by
    simp [airyOscSum]
  have hre := (airyDer_comp_im true 0 hx)
  have hre' := airyDer_oscSum_im true 0 N hx
  rw [hS] at hre'
  rw [(airyDer_comp_true hx).1] at hre ⊢
  rw [hS]
  exact airyDer_even_bound _ (airyExpansionCoeff .aiDeriv) airyV
    (fun j => (airyDer_coeff_aiDeriv j).1) hx N
    (airyDer_aiDeriv_ratio' hp0 hpa (by omega)) (airyDer_aiDeriv_ratio' hm0 hma (by omega))
    (by rw [sub_im, hre, hre', sub_zero])

/-- DLMF §9.7(iii) for the odd subseries of the `Ai'`, `Bi'` oscillatory expansions. -/
theorem airyDer_osc_odd_deriv {x : ℝ} (hx : 0 < x) (N : ℕ) :
    ‖airyOscComponent true 1 x - airyOscSum true 1 N x‖ ≤
        ‖(-1 : ℂ) ^ N * (airyV (2 * N + 1) : ℂ) / airyZetaComplex x ^ (2 * N + 1)‖ ∧
      0 ≤ (airyOscComponent true 1 x - airyOscSum true 1 N x).re *
        ((-1 : ℝ) ^ N * airyV (2 * N + 1)) := by
  obtain ⟨hp0, hpa, hm0, hma⟩ := airyDer_rot_data hx
  have hS : airyOscSum true 1 N x = ∑ j ∈ Finset.range N,
      (-1 : ℂ) ^ j * (airyV (2 * j + 1) : ℂ) / airyZetaComplex x ^ (2 * j + 1) := by
    simp [airyOscSum]
  have hre := (airyDer_comp_im true 1 hx)
  have hre' := airyDer_oscSum_im true 1 N hx
  rw [hS] at hre'
  rw [(airyDer_comp_true hx).2] at hre ⊢
  rw [hS]
  exact airyDer_odd_bound _ (airyExpansionCoeff .aiDeriv) airyV
    (fun j => (airyDer_coeff_aiDeriv j).2) hx N
    (airyDer_aiDeriv_ratio' hp0 hpa (by omega)) (airyDer_aiDeriv_ratio' hm0 hma (by omega))
    (by rw [sub_im, hre, hre', sub_zero])

/-- `v_2 < 0`. -/
theorem airyDer_airyV_two_neg : airyV 2 < 0 := by
  have h := airySt_airyU_pos 2
  unfold airyV
  norm_num
  linarith

/-- The signed first-neglected-term bound for each real oscillatory subseries, 9.7(iii).
The hypothesis explicitly retains the source's condition on the following term. -/
theorem airy_oscillatory_real_error (derivative : Bool) (parity : Fin 2)
    {x : ℝ} (hx : 0 < x) (N : ℕ)
    (hopposite : ((-1 : ℝ) ^ N * (if derivative then airyV (2 * N + parity.val) else airyU (2 * N + parity.val))) *
      ((-1 : ℝ) ^ (N + 1) * (if derivative then airyV (2 * (N + 1) + parity.val) else airyU (2 * (N + 1) + parity.val))) < 0) :
    ‖airyOscComponent derivative parity x - airyOscSum derivative parity.val N x‖ ≤
      ‖(-1 : ℂ) ^ N * (if derivative then airyV (2 * N + parity.val) else airyU (2 * N + parity.val)) /
        airyZetaComplex x ^ (2 * N + parity.val)‖ ∧
    0 ≤ (airyOscComponent derivative parity x - airyOscSum derivative parity.val N x).re *
      ((-1 : ℝ) ^ N * (if derivative then airyV (2 * N + parity.val) else airyU (2 * N + parity.val))) := by
  cases derivative
  · fin_cases parity
    · simpa using airyDer_osc_even hx N
    · simpa using airyDer_osc_odd hx N
  · fin_cases parity
    · rcases Nat.eq_zero_or_pos N with rfl | hN
      · exfalso
        have h0 : airyV 0 = 1 := by simp [airyV, airyU]
        simp [h0] at hopposite
        linarith [airyDer_airyV_two_neg]
      · simpa using airyDer_osc_even_deriv hx hN
    · simpa using airyDer_osc_odd_deriv hx N

/-! ### Exact values of χ at integers -/

/-- The two-step recurrence `χ(x+2) = χ(x) (x+2)/(x+1)` for `x ≥ 0`. -/
theorem airyChi_add_two {x : ℝ} (hx : 0 ≤ x) :
    airyChi (x + 2) = airyChi x * ((x + 2) / (x + 1)) := by
  have h1 : (x + 2) / 2 + 1 = (x / 2 + 1) + 1 := by ring
  have h2 : (x + 2) / 2 + 1 / 2 = (x / 2 + 1 / 2) + 1 := by ring
  have hp1 : 0 < x / 2 + 1 := by positivity
  have hp2 : 0 < x / 2 + 1 / 2 := by positivity
  have hG := (Real.Gamma_pos_of_pos hp2).ne'
  rw [airyChi, airyChi, h1, h2, Real.Gamma_add_one hp1.ne', Real.Gamma_add_one hp2.ne']
  have : x + 1 ≠ 0 := by positivity
  field_simp

/-- `χ(0) = 1`. -/
theorem airyChi_zero : airyChi 0 = 1 := by
  rw [airyChi]; norm_num [Real.Gamma_one_half_eq]
  exact (Real.sqrt_pos.mpr Real.pi_pos).ne'

/-- `χ(1) = π/2`. -/
theorem airyChi_one : airyChi 1 = π / 2 := by
  rw [airyChi, show (1 : ℝ) / 2 + 1 = 1 / 2 + 1 by ring, Real.Gamma_add_one (by norm_num),
    Real.Gamma_one_half_eq, show (1 : ℝ) / 2 + 1 / 2 = 1 by ring, Real.Gamma_one]
  rw [show Real.sqrt π * (1 / 2 * Real.sqrt π) = (Real.sqrt π) ^ 2 / 2 by ring,
    Real.sq_sqrt Real.pi_pos.le]
  ring

/-- `χ(2m) = ∏_{j<m} (2j+2)/(2j+1)`. -/
theorem airyChi_two_mul (m : ℕ) :
    airyChi (2 * m) = ∏ j ∈ Finset.range m, ((2 * j + 2 : ℝ) / (2 * j + 1)) := by
  induction m with
  | zero => simpa using airyChi_zero
  | succ m ih =>
    rw [Finset.prod_range_succ, ← ih, show (2 * ((m + 1 : ℕ) : ℝ)) = 2 * m + 2 by push_cast; ring,
      airyChi_add_two (by positivity)]

/-- `χ(2m+1) = (π/2) ∏_{j<m} (2j+3)/(2j+2)`. -/
theorem airyChi_two_mul_add_one (m : ℕ) :
    airyChi (2 * m + 1) = π / 2 * ∏ j ∈ Finset.range m, ((2 * j + 3 : ℝ) / (2 * j + 2)) := by
  induction m with
  | zero => simpa using airyChi_one
  | succ m ih =>
    rw [Finset.prod_range_succ, ← mul_assoc, ← ih,
      show (2 * ((m + 1 : ℕ) : ℝ)) + 1 = (2 * m + 1) + 2 by push_cast; ring,
      airyChi_add_two (by positivity)]
    congr 1; ring_nf

/-! ### A positive Stieltjes representation for the derivative error kernel

The two positive-parameter instances of DLMF 13.4.5 below combine by contiguous
relations to give the sharp-parameter density for the sigma-zero Airy derivative bounds.
The final error estimates still require the Laplace-mixture and branch-continuation steps.
-/

/-- The normalized Kummer form of the Airy derivative. -/
def airyDer_normalizedU (z : ℂ) : ℂ := z^(-(1/6):ℂ)*kummerU (-(1/6)) (-(1/3)) z

/-- Integrable Cauchy transforms of the kernels used below. -/
theorem airyDer_integrable_cauchy {f : ℝ → ℂ} (hf : IntegrableOn f (Ioi 0)) {z : ℂ}
    (hz : z ∈ slitPlane) : IntegrableOn (fun t : ℝ => f t/((t:ℂ)+z)) (Ioi 0) := by
  obtain ⟨δ, hδ, hδb⟩ := exists_forall_le_norm_add_of_mem_slitPlane hz
  have hm : AEStronglyMeasurable (fun t : ℝ => f t/((t:ℂ)+z)) (volume.restrict (Ioi 0)) :=
    hf.aestronglyMeasurable.mul (by fun_prop : Measurable fun t : ℝ => ((t:ℂ)+z)⁻¹).aestronglyMeasurable
  refine (hf.norm.const_mul δ⁻¹).mono' hm ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have hb := hδb t (le_of_lt ht) z (Metric.mem_ball_self hδ)
  rw [norm_div]
  calc ‖f t‖/‖(t:ℂ)+z‖ ≤ ‖f t‖/δ := div_le_div_of_nonneg_left (norm_nonneg _) hδ hb
    _ = _ := by ring

/-- A contiguous relation lowering the first parameter from its positive domain. -/
theorem airyDer_U_lower {z : ℂ} (hz : z ≠ 0) :
    kummerU (-(1/6)) (-(1/3)) z = z*kummerU (5/6) (2/3) z+(7/6:ℂ)*kummerU (5/6) (-(1/3)) z := by
  have h1 := kummerU_contiguous_mixed (-(1/6)) (-(1/3)) z hz
  have h2 := kummerU_contiguous_a_b (-(1/6)) (2/3) z hz
  norm_num at h1 h2
  linear_combination -6*h1-6*z*h2

/-- The kernel relation used to combine the two positive-parameter transforms. -/
theorem airyDer_U_kernel {t : ℂ} (ht : t ≠ 0) :
    kummerU (-(7/6)) (-(1/3)) t = t*kummerU (-(1/6)) (2/3) t+(1/6:ℂ)*kummerU (-(1/6)) (-(1/3)) t := by
  have h := kummerU_contiguous_shift_a (-(1/6)) (-(1/3)) t ht
  norm_num at h
  linear_combination h

/-- The exactly evaluated constant term in the continued Stieltjes formula. -/
theorem airyDer_constant_moment :
    (∫ t : ℝ in Ioi 0, exp (-(t:ℂ))*(t:ℂ)^(-(1/6):ℂ)*kummerU (-(1/6)) (2/3) t) =
      Gamma (5/6)*Gamma (7/6) := by
  have h := laplace_kummerU (a := (-(1/6):ℂ)) (b := 5/6) (c := 2/3) (z := 1)
    (by norm_num) (by norm_num) (by norm_num)
  norm_num at h
  rw [regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ (by norm_num),
    regularizedGaussHGFun_eq_div_Gamma (fun k => by
      have hk : (0:ℝ) ≤ k := Nat.cast_nonneg k
      intro he
      have := congrArg Complex.re he
      norm_num at this
      linarith), ordinaryHypergeometric_zero, Gamma_one] at h
  simpa using h

/-- `6 Γ(5/6) Γ(7/6) = 2π`, from the reflection formula at `1/6`. -/
private lemma airyDer_six_gamma_mul : 6 * Gamma (5 / 6 : ℂ) * Gamma (7 / 6) = 2 * π := by
  have h := Gamma_mul_Gamma_one_sub (1 / 6 : ℂ)
  have hg := Gamma_add_one (1 / 6 : ℂ) (by norm_num)
  rw [show π * (1 / 6 : ℂ) = ((Real.pi / 6 : ℝ) : ℂ) by push_cast; ring, ← ofReal_sin,
    Real.sin_pi_div_six] at h
  norm_num at h hg
  linear_combination h + (6 * Gamma (5 / 6 : ℂ)) * hg

/-- The Airy derivative's normalized Kummer function has a positive Stieltjes remainder. -/
theorem airyDer_stieltjes {z : ℂ} (hz : z ∈ slitPlane) :
    airyDer_normalizedU z = 1 + 1/(2*π:ℂ)*
      ∫ t : ℝ in Ioi 0, exp (-(t:ℂ))*airyDer_normalizedU t/((t:ℂ)+z) := by
  have hz0 := slitPlane_ne_zero hz
  have h1 := kummerU_stieltjes (a := (5/6:ℂ)) (b := 2/3) hz (by norm_num) (by norm_num)
  have h2 := kummerU_stieltjes (a := (5/6:ℂ)) (b := -(1/3)) hz (by norm_num) (by norm_num)
  norm_num at h1 h2
  have hG : Gamma (13/6:ℂ) = (7/6:ℂ)*Gamma (7/6) := by
    rw [show (13/6:ℂ)=(7/6)+1 by norm_num, Gamma_add_one (7/6) (by norm_num)]
  have hG1 : Gamma (5/6:ℂ) ≠ 0 := Gamma_ne_zero_of_re_pos (by norm_num)
  have hG2 : Gamma (7/6:ℂ) ≠ 0 := Gamma_ne_zero_of_re_pos (by norm_num)
  let f : ℝ → ℂ := fun t => exp (-(t:ℂ))*(t:ℂ)^(-(1/6):ℂ)*kummerU (-(1/6)) (2/3) t
  let g : ℝ → ℂ := fun t => exp (-(t:ℂ))*(t:ℂ)^(-(1/6):ℂ)*kummerU (-(7/6)) (-(1/3)) t
  let p : ℝ → ℂ := fun t => exp (-(t:ℂ))*airyDer_normalizedU t
  have hf : IntegrableOn f (Ioi 0) := by
    have h := (laplace_kummerU_gauss (a := (-(1/6):ℂ)) (b := 5/6) (c := 2/3) (z := 1)
      (by norm_num) (by norm_num) (by norm_num)).1
    convert h using 1
    funext t
    simp only [tricomiLaplaceKernel, f]
    norm_num
  have hg : IntegrableOn g (Ioi 0) := by
    have h := (laplace_kummerU_gauss (a := (-(7/6):ℂ)) (b := 5/6) (c := -(1/3)) (z := 1)
      (by norm_num) (by norm_num) (by norm_num)).1
    convert h using 1
    funext t
    simp only [tricomiLaplaceKernel, g]
    norm_num
  have hp : IntegrableOn p (Ioi 0) := by
    have h := (laplace_kummerU_gauss (a := (-(1/6):ℂ)) (b := 5/6) (c := -(1/3)) (z := 1)
      (by norm_num) (by norm_num) (by norm_num)).1
    convert h using 1
    funext t
    simp only [tricomiLaplaceKernel, p, airyDer_normalizedU]
    norm_num
    ring
  have hpt : ∀ t ∈ Ioi (0:ℝ),
      z*(f t/((t:ℂ)+z))+g t/((t:ℂ)+z) = f t+(1/6:ℂ)*(p t/((t:ℂ)+z)) := by
    intro t ht
    have ht0 : (t:ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt ht)
    have hd : (t:ℂ)+z ≠ 0 := by
      obtain ⟨δ,hδ,hδb⟩ := exists_forall_le_norm_add_of_mem_slitPlane hz
      exact norm_pos_iff.mp (hδ.trans_le (hδb t (le_of_lt ht) z (Metric.mem_ball_self hδ)))
    dsimp only [f,g,p,airyDer_normalizedU]
    rw [airyDer_U_kernel ht0]
    field_simp
    ring
  have hint : z*(∫ t in Ioi (0:ℝ), f t/((t:ℂ)+z))+
      (∫ t in Ioi (0:ℝ), g t/((t:ℂ)+z)) =
      Gamma (5/6)*Gamma (7/6)+(1/6:ℂ)*(∫ t in Ioi (0:ℝ), p t/((t:ℂ)+z)) := by
    rw [← integral_const_mul, ← integral_add ((airyDer_integrable_cauchy hf hz).const_mul _) (airyDer_integrable_cauchy hg hz),
      setIntegral_congr_fun measurableSet_Ioi hpt, integral_add hf ((airyDer_integrable_cauchy hp hz).const_mul _), integral_const_mul]
    rw [show (∫ t in Ioi (0:ℝ), f t)=Gamma (5/6)*Gamma (7/6) from airyDer_constant_moment]
  have hu := airyDer_U_lower hz0
  rw [h1,h2,hG] at hu
  have hI1 : (∫ t in Ioi (0:ℝ), kummerU (-(1/6)) (2/3) t*exp (-(t:ℂ))*(t:ℂ)^(-(1/6):ℂ)/((t:ℂ)+z)) =
      ∫ t in Ioi (0:ℝ), f t/((t:ℂ)+z) := by
    apply setIntegral_congr_fun measurableSet_Ioi; intro t ht; dsimp only [f]; ring
  have hI2 : (∫ t in Ioi (0:ℝ), kummerU (-(7/6)) (-(1/3)) t*exp (-(t:ℂ))*(t:ℂ)^(-(1/6):ℂ)/((t:ℂ)+z)) =
      ∫ t in Ioi (0:ℝ), g t/((t:ℂ)+z) := by
    apply setIntegral_congr_fun measurableSet_Ioi; intro t ht; dsimp only [g]; ring
  rw [hI1,hI2] at hu
  have hpow : z^(-(1/6):ℂ)*z^(1/6:ℂ)=1 := by rw [← cpow_add _ _ hz0]; norm_num
  have hgamma := airyDer_six_gamma_mul
  have hu' : kummerU (-(1/6)) (-(1/3)) z =
      z^(1/6:ℂ)/(Gamma (5/6)*Gamma (7/6)) *
        (z*(∫ t in Ioi (0:ℝ), f t/((t:ℂ)+z))+
          (∫ t in Ioi (0:ℝ), g t/((t:ℂ)+z))) := by
    rw [hu]
    field_simp
  change z^(-(1/6):ℂ)*kummerU (-(1/6)) (-(1/3)) z =
    1+1/(2*π:ℂ)*(∫ t in Ioi (0:ℝ), p t/((t:ℂ)+z))
  rw [hu', hint]
  calc
    _ = 1+1/(6*Gamma (5/6:ℂ)*Gamma (7/6))*
        (∫ t in Ioi (0:ℝ), p t/((t:ℂ)+z)) := by
      field_simp
      linear_combination (6*Gamma (5/6:ℂ)*Gamma (7/6)+
        (∫ t in Ioi (0:ℝ), p t/((t:ℂ)+z)))*hpow
    _ = _ := by rw [hgamma]

/-- Positive real Laplace representation of the normalized derivative kernel. -/
theorem airyDer_normalizedU_real {t : ℝ} (ht : 0 < t) :
    airyDer_normalizedU t = ((t^(7/6:ℝ)/Real.Gamma (7/6) *
      ∫ u : ℝ in Ioi 0, Real.exp (-t*u)*u^(1/6:ℝ)*(1+u)^(1/6:ℝ) : ℝ):ℂ) := by
  have ht0 : (t:ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
  have h := kummerU_kummer_transform_all (-(1/6):ℂ) (-(1/3)) ht0
  norm_num at h
  have hp : (t:ℂ)^(-(1/6):ℂ)*(t:ℂ)^(4/3:ℂ)=(t:ℂ)^(7/6:ℂ) := by
    rw [← cpow_add _ _ ht0]
    norm_num
  rw [airyDer_normalizedU, h, ← mul_assoc, hp, kummerU_laplace (by norm_num) (by simpa using ht)]
  rw [show (7/6:ℂ)-1=1/6 by norm_num, show (7/3:ℂ)-7/6-1=1/6 by norm_num]
  have hI : (∫ u : ℝ in Ioi 0, exp (-(t:ℂ)*u)*(u:ℂ)^(1/6:ℂ)*(1+(u:ℂ))^(1/6:ℂ)) =
      ((∫ u : ℝ in Ioi 0, Real.exp (-t*u)*u^(1/6:ℝ)*(1+u)^(1/6:ℝ) : ℝ):ℂ) := by
    rw [← integral_complex_ofReal]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    dsimp only
    have hu0 : 0 < u := hu
    push_cast
    rw [ofReal_cpow hu0.le, ofReal_cpow (by linarith : 0 ≤ 1+u)]
    push_cast
    ring
  rw [hI]
  push_cast
  rw [ofReal_cpow ht.le]
  have hGamma : Gamma (7/6:ℂ)=(Real.Gamma (7/6:ℝ):ℂ) := by
    convert Gamma_ofReal (7/6) using 1; norm_num
  rw [hGamma]
  push_cast
  ring

/-- The derivative Stieltjes kernel is real and nonnegative on the positive axis. -/
theorem airyDer_normalizedU_nonneg {t : ℝ} (ht : 0 < t) :
    0 ≤ (airyDer_normalizedU t).re ∧ (airyDer_normalizedU t).im=0 := by
  rw [airyDer_normalizedU_real ht]
  simp only [ofReal_re, ofReal_im, and_true]
  have hi : 0 ≤ ∫ u : ℝ in Ioi 0, Real.exp (-t*u)*u^(1/6:ℝ)*(1+u)^(1/6:ℝ) := by
    apply setIntegral_nonneg measurableSet_Ioi
    intro u hu
    have hu0 : 0 < u := hu
    have : 0 ≤ 1+u := by linarith
    positivity
  exact mul_nonneg (div_nonneg (Real.rpow_nonneg ht.le _) (Real.Gamma_pos_of_pos (by norm_num)).le) hi

/-- The real density of the Airy derivative Stieltjes transform. -/
def airyDer_density (t : ℝ) : ℝ := Real.exp (-t)*(airyDer_normalizedU t).re

/-- Complex and real forms of the derivative Stieltjes density agree. -/
theorem airyDer_density_coe {t : ℝ} (ht : 0 < t) :
    (airyDer_density t:ℂ)=exp (-(t:ℂ))*airyDer_normalizedU t := by
  rw [airyDer_density, ofReal_mul, ofReal_exp]
  push_cast
  congr 1
  apply Complex.ext <;> simp [(airyDer_normalizedU_nonneg ht).2]

/-- The Airy derivative Stieltjes density is nonnegative. -/
theorem airyDer_density_nonneg {t : ℝ} (ht : 0 < t) : 0 ≤ airyDer_density t :=
  mul_nonneg (Real.exp_pos _).le (airyDer_normalizedU_nonneg ht).1

/-- The regularized Gauss function at zero, on its positive parameter half-plane. -/
theorem airyDer_regularizedGaussHG_zero (a b c : ℂ) (hc : 0 < c.re) :
    regularizedGaussHG a b c 0 = 1/Gamma c := by
  rw [regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ (by norm_num),
    regularizedGaussHGFun_eq_div_Gamma (fun k => by
      intro he
      have := congrArg Complex.re he
      simp only [neg_re, natCast_re] at this
      linarith [Nat.cast_nonneg (α := ℝ) k]), ordinaryHypergeometric_zero]

/-- The moments of the complex derivative Stieltjes density. -/
theorem airyDer_density_moment_complex (k : ℕ) :
    IntegrableOn (fun t : ℝ => (t:ℂ)^k*exp (-(t:ℂ))*airyDer_normalizedU t) (Ioi 0) ∧
    (∫ t : ℝ in Ioi 0, (t:ℂ)^k*exp (-(t:ℂ))*airyDer_normalizedU t) =
      Gamma ((k:ℂ)+5/6)*Gamma ((k:ℂ)+13/6)/Gamma ((k:ℂ)+2) := by
  have h := laplace_kummerU_gauss (a := (-(1/6):ℂ)) (b := (k:ℂ)+5/6) (c := -(1/3)) (z := 1)
    (by norm_num; linarith [Nat.cast_nonneg (α := ℝ) k])
    (by norm_num; linarith [Nat.cast_nonneg (α := ℝ) k]) (by norm_num)
  have hpt (t : ℝ) (ht : t ∈ Ioi (0:ℝ)) :
      (t:ℂ)^k*exp (-(t:ℂ))*airyDer_normalizedU t =
        tricomiLaplaceKernel (-(1/6)) ((k:ℂ)+5/6) (-(1/3)) 1 t := by
    dsimp only [airyDer_normalizedU, tricomiLaplaceKernel]
    have ht0 : (t:ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
    rw [show (k:ℂ)+5/6-1=(k:ℂ)+(-(1/6)) by ring, cpow_add _ _ ht0, cpow_natCast]
    ring
  constructor
  · exact h.1.congr_fun (fun t ht => (hpt t ht).symm) measurableSet_Ioi
  · rw [setIntegral_congr_fun measurableSet_Ioi hpt, h.2]
    norm_num
    rw [show (k:ℂ)+5/6+1/3+1=(k:ℂ)+13/6 by ring,
      show -(1/6:ℂ)+((k:ℂ)+5/6)+1/3+1=(k:ℂ)+2 by ring,
      airyDer_regularizedGaussHG_zero _ _ _ (by simp; positivity)]
    ring

/-- The real moments of the positive derivative Stieltjes density. -/
theorem airyDer_density_moment (k : ℕ) :
    IntegrableOn (fun t : ℝ => t^k*airyDer_density t) (Ioi 0) ∧
    (∫ t : ℝ in Ioi 0, t^k*airyDer_density t) =
      Real.Gamma ((k:ℝ)+5/6)*Real.Gamma ((k:ℝ)+13/6)/Real.Gamma ((k:ℝ)+2) := by
  have heq (t : ℝ) (ht : t ∈ Ioi (0:ℝ)) :
      ((t^k*airyDer_density t:ℝ):ℂ)=(t:ℂ)^k*exp (-(t:ℂ))*airyDer_normalizedU t := by
    push_cast
    rw [airyDer_density_coe ht]
    ring
  have h := airyDer_density_moment_complex k
  have hc : IntegrableOn (fun t : ℝ => ((t^k*airyDer_density t:ℝ):ℂ)) (Ioi 0) :=
    h.1.congr_fun (fun t ht => (heq t ht).symm) measurableSet_Ioi
  constructor
  · simpa only [RCLike.re_to_complex, ofReal_re] using hc.re
  · apply ofReal_injective
    rw [← integral_complex_ofReal, setIntegral_congr_fun measurableSet_Ioi heq, h.2]
    have hGamma (a : ℝ) : (Real.Gamma a:ℂ)=Gamma (a:ℂ) := (Gamma_ofReal a).symm
    push_cast
    simp only [hGamma]
    push_cast
    rfl

/-- Kummer's positive-parameter form of the normalized derivative. -/
theorem airyDer_normalizedU_positive {z : ℂ} (hz : z ≠ 0) :
    airyDer_normalizedU z=z^(7/6:ℂ)*kummerU (7/6) (7/3) z := by
  have h := kummerU_kummer_transform_all (-(1/6):ℂ) (-(1/3)) hz
  norm_num at h
  rw [airyDer_normalizedU,h,← mul_assoc,← cpow_add _ _ hz]
  norm_num

/-- The normalized Airy derivative is the positive Stieltjes function on its principal sector. -/
theorem airyDer_normalizedU_eq {z : ℂ} (hz : z ≠ 0) (harg : |arg z|<2*π/3) :
    airyAiDeriv z/airyPrefactor .aiDeriv z = airyDer_normalizedU (2*airyZetaComplex z) := by
  have hW : 2*airyZetaComplex z ≠ 0 := mul_ne_zero two_ne_zero (airySt_zeta_ne_zero hz)
  rw [airyDer_normalizedU_positive hW, airySt_two_zeta_cpow hz harg,
    airyAiDeriv_eq_kummerU hz harg, airyPrefactor]
  have hπ : (Real.sqrt π:ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hq : z^(1/4:ℂ) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hz)
  rw [exp_sub]
  have hN := airyDer_norm_const hz
  have hE : exp (-airyZetaComplex z) ≠ 0 := exp_ne_zero _
  field_simp
  have hEE : exp (airyZetaComplex z)*exp (-airyZetaComplex z)=1 := by
    rw [← exp_add]; simp
  ring_nf at hN ⊢
  linear_combination kummerU (7/6) (7/3) (airyZetaComplex z*2)*hN -
    kummerU (7/6) (7/3) (airyZetaComplex z*2)*z^(1/4:ℂ)*
      exp (airyLogZeta z*(7/6)+log 2*(7/6))*hEE
end DLMF.Airy
