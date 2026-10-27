/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.JacobiElliptic.Integrals
public import DLMF.Elementary.Trigonometric
public import DLMF.Elliptic.JacobiIdentities

/-!
# Related functions: amplitude, Jacobi's Epsilon and Zeta functions (DLMF §22.16)

* **Amplitude** (§22.16(i)). The project's `DLMF.Elliptic.Real.jacobiAmm x m`, the inverse of
  `φ ↦ F(φ|m)` for real parameter `m = k² < 1`, is DLMF's `am(x, k)`. It is the continuous
  branch of `Arcsin(sn x)` (22.16.1), the integral of `dn` (22.16.3), infinitely
  differentiable (prose), and the four relations 22.16.10–22.16.13 are proved. The
  quasi-periodicity 22.16.2 and `am(x, 0) = x` (22.16.4) are the existing
  `Real.jacobiAmm_add_two_compEllIntKm` and `Real.jacobiAmm_zero_param`. At `k = 1` the existing
definition is a
  totalized junk value (`am x = x` for `m ≥ 1`), so 22.16.5 `am(x,1) = gd x` is stated as the
  limit `k → 1⁻`.
* **Epsilon function** (§22.16(ii)). `Real.jacobiEpsilonk x k = ∫₀ˣ dn²(t,k) dt` (DLMF 22.16.17,
  valid for all real `x`, taken as the definition). It equals `E(am(x,k), k)` for *all* real
  `x` (22.16.31; DLMF states `-K ≤ x ≤ K`), which gives the quasi-periodicity 22.16.29.
* **Zeta function** (§22.16(iii)). `Real.jacobiZetaFunctionk x k = ℰ(x,k) - (E(k)/K(k)) x`
  (22.16.32). DLMF and Miller write `Z(x|k)` / `JacobiZeta`; the longer name avoids a clash with
  `DLMF.JacobiElliptic.jacobiZetak`, which is the theta argument `ζ = πz/(2K)` of §22.2.

All functions are real, with `0 < k < 1` (or `m < 1`) as in DLMF §22.16, `K = K(k²)`,
`E = E(k²)` in the parameter convention of `DLMF.Elliptic.Complete`, `k'² = 1 - k²`.
-/

@[expose] public section

open Real DLMF.Elliptic Filter Asymptotics
open scoped Topology

noncomputable section

namespace DLMF.JacobiElliptic

/-! ### Jacobi's amplitude -/

section Amplitude

variable {m : ℝ}

/-- `dn` is continuous for `m < 1` (helper). -/
lemma je22b_continuous_jacobiDnm (hm : m < 1) : Continuous fun u => Real.jacobiDnm u m :=
  continuous_iff_continuousAt.mpr fun u => (Real.hasDerivAt_jacobiDnm hm u).continuousAt

/-- `-π/2 ≤ am x ≤ π/2` for `-K ≤ x ≤ K` (helper). -/
lemma je22b_jacobiAmm_mem_Icc (hm : m < 1) {x : ℝ} (hx0 : -Real.compEllIntKm m ≤ x)
    (hx1 : x ≤ Real.compEllIntKm m) :
    Real.jacobiAmm x m ∈ Set.Icc (-(π / 2)) (π / 2) := by
  have h0 := (je22b_jacobiAmm_strictMono hm).monotone hx0
  have h1 := (je22b_jacobiAmm_strictMono hm).monotone hx1
  simp only [Real.jacobiAmm_neg hm, Real.jacobiAmm_compEllIntKm hm] at h0 h1
  exact ⟨h0, h1⟩

/-- DLMF 22.16.1: `am(x,k) = Arcsin(sn(x,k))`, with the principal inverse sine for
`-K ≤ x ≤ K` (elsewhere `am` is the continuous continuation, `Real.continuous_jacobiAmm`). -/
@[dlmf 22.16.E1 "special case: real parameter m = k² < 1; principal branch on -K ≤ x ≤ K"]
theorem Real.jacobiAmm_eq_arcsin_jacobiSnm (hm : m < 1) {x : ℝ}
    (hx0 : -Real.compEllIntKm m ≤ x) (hx1 : x ≤ Real.compEllIntKm m) :
    Real.jacobiAmm x m = Real.arcsin (Real.jacobiSnm x m) := by
  obtain ⟨h0, h1⟩ := je22b_jacobiAmm_mem_Icc hm hx0 hx1
  rw [Real.jacobiSnm, Real.arcsin_sin h0 h1]

/-- DLMF §22.16(i), prose after 22.16.1: `am(x,k)` is an infinitely differentiable function
of `x` (`m < 1`). -/
@[dlmf 22.16.i "special case: real parameter m = k² < 1"]
theorem Real.contDiff_jacobiAmm (hm : m < 1) :
    ContDiff ℝ (⊤ : ℕ∞) fun x => Real.jacobiAmm x m := by
  have hderiv : deriv (fun x => Real.jacobiAmm x m) =
      fun x => √(1 - m * Real.sin (Real.jacobiAmm x m) ^ 2) := by
    funext x
    rw [(Real.hasDerivAt_jacobiAmm hm x).deriv, Real.sqrt_eq_rpow]
  have hn : ∀ n : ℕ, ContDiff ℝ n fun x => Real.jacobiAmm x m := by
    intro n
    induction n with
    | zero => exact contDiff_zero.mpr (Real.continuous_jacobiAmm hm)
    | succ n ih =>
      rw [show ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 by push_cast; rfl,
        contDiff_succ_iff_deriv]
      refine ⟨fun x => (Real.hasDerivAt_jacobiAmm hm x).differentiableAt, by simp, ?_⟩
      rw [hderiv]
      refine ContDiff.sqrt ?_ fun x => (one_sub_mul_sin_sq_pos hm _).ne'
      exact contDiff_const.sub (contDiff_const.mul ((Real.contDiff_sin.comp ih).pow 2))
  exact contDiff_infty.mpr hn

/-- DLMF 22.16.3: `am(x, k) = ∫₀ˣ dn(t, k) dt`. -/
@[dlmf 22.16.E3 "special case: real parameter m = k² < 1"]
theorem Real.jacobiAmm_eq_integral_jacobiDnm (hm : m < 1) (x : ℝ) :
    Real.jacobiAmm x m = ∫ t in (0 : ℝ)..x, Real.jacobiDnm t m := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t => Real.jacobiAmm t m)
    (f' := fun t => Real.jacobiDnm t m) (fun t _ => Real.hasDerivAt_jacobiAmm hm t)
    ((je22b_continuous_jacobiDnm hm).intervalIntegrable 0 x)
  rw [h, Real.jacobiAmm_zero hm, sub_zero]

/-- DLMF 22.16.5: `am(x, 1) = gd(x)`, as the limit `k → 1⁻` (the existing real amplitude is
defined only for `m < 1`). Admitted. -/
@[dlmf 22.16.E5 "different convention: limit k → 1⁻, since Real.jacobiAmm is totalized at m = 1"]
theorem Real.tendsto_jacobiAmm_one (x : ℝ) :
    Tendsto (fun k : ℝ => Real.jacobiAmm x (k ^ 2)) (𝓝[<] 1)
      (𝓝 (DLMF.Elementary.gudermannian x)) := by
  sorry

/-- DLMF 22.16.6: `am(x,k) = x - k² x³/3! + k²(4 + k²) x⁵/5! + O(x⁷)` as `x → 0`, `m = k²`.
Admitted. -/
@[dlmf 22.16.E6 "special case: real x, real parameter m = k² < 1"]
theorem Real.jacobiAmm_isBigO_maclaurin (hm : m < 1) :
    (fun x => Real.jacobiAmm x m - (x - m * x ^ 3 / 6 + m * (4 + m) * x ^ 5 / 120)) =O[𝓝 0]
      fun x => x ^ 7 := by
  sorry

/-- DLMF 22.16.7: `am(x,k) = x - k²(x - sin x cos x)/4 + O(k⁴)` as `k → 0`, for fixed real `x`.
Admitted. -/
@[dlmf 22.16.E7 "special case: real x, real k → 0"]
theorem Real.jacobiAmm_isBigO_small_modulus (x : ℝ) :
    (fun k : ℝ => Real.jacobiAmm x (k ^ 2) - (x - k ^ 2 / 4 * (x - Real.sin x * Real.cos x)))
      =O[𝓝 0] fun k => k ^ 4 := by
  sorry

/-- DLMF 22.16.8: `am(x,k) = gd x - k'²(x - sinh x cosh x) sech x/4 + O(k'⁴)` as `k → 1⁻`, for
fixed real `x`, with `k'² = 1 - k²`. Admitted. -/
@[dlmf 22.16.E8 "special case: real x, real k → 1⁻"]
theorem Real.jacobiAmm_isBigO_small_comodulus (x : ℝ) :
    (fun k : ℝ => Real.jacobiAmm x (k ^ 2) - (DLMF.Elementary.gudermannian x -
        (1 - k ^ 2) / 4 * (x - Real.sinh x * Real.cosh x) / Real.cosh x))
      =O[𝓝[<] 1] fun k => (1 - k ^ 2) ^ 2 := by
  sorry

/-- DLMF 22.16.9: the Fourier series
`am(x,k) = πx/(2K) + 2 ∑_{n ≥ 1} qⁿ sin(2nζ)/(n(1 + q²ⁿ))`, `ζ = πx/(2K)`, with the real nome
`q = exp(-πK'/K)`, for real `x` and `0 < k < 1`. Admitted. -/
@[dlmf 22.16.E9 "special case: real x, 0 < k < 1"]
theorem Real.jacobiAmm_hasSum_fourier {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) (x : ℝ) :
    HasSum (fun n : ℕ =>
        2 * Real.exp (-(π * Real.compEllIntKm (1 - k ^ 2) / Real.compEllIntKm (k ^ 2))) ^ (n + 1) *
          Real.sin (2 * (n + 1) * (π * x / (2 * Real.compEllIntKm (k ^ 2)))) /
          ((n + 1) * (1 + Real.exp (-(π * Real.compEllIntKm (1 - k ^ 2) /
            Real.compEllIntKm (k ^ 2))) ^ (2 * (n + 1)))))
      (Real.jacobiAmm x (k ^ 2) - π / (2 * Real.compEllIntKm (k ^ 2)) * x) := by
  sorry

/-- DLMF 22.16.10 ⇔ 22.16.11: `x = F(φ, k)` if and only if `am(x, k) = φ`; this holds for all
real `x` and `φ` (stronger than DLMF, which assumes `-K ≤ x ≤ K`). -/
@[dlmf 22.16.E10 "stronger than DLMF: all real x and φ"]
theorem Real.eq_incEllIntFm_iff_jacobiAmm_eq (hm : m < 1) (x φ : ℝ) :
    x = Real.incEllIntFm φ m ↔ Real.jacobiAmm x m = φ := by
  constructor
  · rintro rfl; exact Real.jacobiAmm_incEllIntFm hm φ
  · rintro rfl; exact (Real.incEllIntFm_jacobiAmm hm x).symm

/-- DLMF 22.16.11 ⇔ 22.16.12: for `-K ≤ x ≤ K` and `-π/2 ≤ φ ≤ π/2`, `am(x,k) = φ` if and
only if `sn(x,k) = sin φ`; and `sn(x,k) = sin(am(x,k))` holds by definition. DLMF leaves the
range of `φ` implicit; it is needed for the converse direction. -/
@[dlmf 22.16.E12 "special case: -π/2 ≤ φ ≤ π/2 made explicit"]
theorem Real.jacobiAmm_eq_iff_jacobiSnm_eq_sin (hm : m < 1) {x φ : ℝ}
    (hx0 : -Real.compEllIntKm m ≤ x) (hx1 : x ≤ Real.compEllIntKm m) (hφ0 : -(π / 2) ≤ φ)
    (hφ1 : φ ≤ π / 2) :
    (Real.jacobiAmm x m = φ ↔ Real.jacobiSnm x m = Real.sin φ) ∧
      Real.jacobiSnm x m = Real.sin (Real.jacobiAmm x m) := by
  refine ⟨⟨fun h => by rw [Real.jacobiSnm, h], fun h => ?_⟩, rfl⟩
  exact Real.injOn_sin (je22b_jacobiAmm_mem_Icc hm hx0 hx1) ⟨hφ0, hφ1⟩ h

/-- DLMF 22.16.11 ⇔ 22.16.13: `am(x,k) = φ` implies `cn(x,k) = cos φ`, and `cn = cos ∘ am` by
definition; the converse needs a sign condition, here `0 ≤ x ≤ K`, `0 ≤ φ ≤ π/2` (for
`-K ≤ x < 0` the angles `±φ` have the same cosine). -/
@[dlmf 22.16.E13 "special case: converse for 0 ≤ x ≤ K, 0 ≤ φ ≤ π/2 (cos is even)"]
theorem Real.jacobiAmm_eq_iff_jacobiCnm_eq_cos (hm : m < 1) {x φ : ℝ} (hx0 : 0 ≤ x)
    (hx1 : x ≤ Real.compEllIntKm m) (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ π / 2) :
    (Real.jacobiAmm x m = φ ↔ Real.jacobiCnm x m = Real.cos φ) ∧
      Real.jacobiCnm x m = Real.cos (Real.jacobiAmm x m) := by
  refine ⟨⟨fun h => by rw [Real.jacobiCnm, h], fun h => ?_⟩, rfl⟩
  have hK := Real.compEllIntKm_pos hm
  obtain ⟨-, h1⟩ := je22b_jacobiAmm_mem_Icc hm (by linarith) hx1
  have h0 : 0 ≤ Real.jacobiAmm x m := by
    simpa [Real.jacobiAmm_zero hm] using (je22b_jacobiAmm_strictMono hm).monotone hx0
  exact Real.injOn_cos ⟨h0, by linarith [Real.pi_pos]⟩ ⟨hφ0, by linarith [Real.pi_pos]⟩ h

end Amplitude

/-! ### Jacobi's Epsilon function -/

/-- Jacobi's Epsilon function `ℰ(x, k) = ∫₀ˣ dn²(t, k) dt` for real `x` and real modulus `k`
with `k² < 1` (DLMF 22.16.17, valid for all real `x`; DLMF's 22.16.14 is the equivalent form for
`-K < x < K`). Miller's `JacobiEpsilon`. -/
@[dlmf 22.16.E17]
def Real.jacobiEpsilonk (x k : ℝ) : ℝ := ∫ t in (0 : ℝ)..x, Real.jacobiDnm t (k ^ 2) ^ 2

/-- Jacobi's Zeta function `Z(x|k) = ℰ(x, k) - (E(k)/K(k)) x` for real `x` (DLMF 22.16.32);
Miller's `JacobiZeta`. -/
@[dlmf 22.16.E32]
def Real.jacobiZetaFunctionk (x k : ℝ) : ℝ :=
  Real.jacobiEpsilonk x k - Real.compEllIntEm (k ^ 2) / Real.compEllIntKm (k ^ 2) * x

section Epsilon

variable {k : ℝ}

/-- `dn²` is interval integrable (helper). -/
lemma je22b_intervalIntegrable_jacobiDnm_sq (hm : k ^ 2 < 1) (a b : ℝ) :
    IntervalIntegrable (fun t => Real.jacobiDnm t (k ^ 2) ^ 2) MeasureTheory.volume a b :=
  ((je22b_continuous_jacobiDnm hm).pow 2).intervalIntegrable a b

/-- `sn²` is interval integrable (helper). -/
lemma je22b_intervalIntegrable_jacobiSnm_sq (hm : k ^ 2 < 1) (a b : ℝ) :
    IntervalIntegrable (fun t => Real.jacobiSnm t (k ^ 2) ^ 2) MeasureTheory.volume a b :=
  ((Real.continuous_sin.comp (Real.continuous_jacobiAmm hm)).pow 2).intervalIntegrable a b

/-- DLMF 22.16.31: `E(am(x,k), k) = ℰ(x, k)`; proved for all real `x` (stronger than DLMF,
which states `-K ≤ x ≤ K`). -/
@[dlmf 22.16.E31 "stronger than DLMF: all real x; real modulus with k² < 1"]
theorem Real.incEllIntEm_jacobiAmm (hm : k ^ 2 < 1) (x : ℝ) :
    Real.incEllIntEm (Real.jacobiAmm x (k ^ 2)) (k ^ 2) = Real.jacobiEpsilonk x k := by
  have hd : ∀ t, HasDerivAt (fun t => Real.incEllIntEm (Real.jacobiAmm t (k ^ 2)) (k ^ 2))
      (Real.jacobiDnm t (k ^ 2) ^ 2) t := fun t => by
    have := (Real.hasDerivAt_incEllIntEm hm (Real.jacobiAmm t (k ^ 2))).comp t
      (Real.hasDerivAt_jacobiAmm hm t)
    refine this.congr_deriv ?_
    rw [Real.jacobiDnm, Real.jacobiSnm]; ring
  have h0 : Real.incEllIntEm (Real.jacobiAmm 0 (k ^ 2)) (k ^ 2) = 0 := by
    simp [Real.jacobiAmm_zero hm, Real.incEllIntEm]
  rw [Real.jacobiEpsilonk, intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
    (je22b_intervalIntegrable_jacobiDnm_sq hm 0 x), h0, sub_zero]

open MeasureTheory Set in
/-- Substitution `t = f θ` for a continuous strictly increasing `f` on `[a, b]`. -/
theorem p22R1_subst_mono {f f' g h : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn f (Icc a b)) (ha : StrictMonoOn f (Icc a b))
    (hd : ∀ θ ∈ Ioo a b, HasDerivAt f (f' θ) θ)
    (hg : ∀ θ ∈ Ioo a b, |f' θ| * g (f θ) = h θ) :
    ∫ t in f a..f b, g t = ∫ θ in a..b, h θ := by
  have hfab : f a ≤ f b := ha.monotoneOn ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab
  have hcv := integral_image_eq_integral_abs_deriv_smul (f := f) (f' := f')
    (measurableSet_Ioo (a := a) (b := b)) (fun θ hθ => (hd θ hθ).hasDerivWithinAt)
    (ha.injOn.mono Ioo_subset_Icc_self) g
  rw [hc.image_Ioo_of_strictMonoOn hab ha] at hcv
  rw [intervalIntegral.integral_of_le hfab, integral_Ioc_eq_integral_Ioo, hcv,
    intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo]
  exact setIntegral_congr_fun measurableSet_Ioo fun θ hθ => by simp only [smul_eq_mul]; exact hg θ hθ

/-- DLMF 22.16.14: `ℰ(x, k) = ∫₀^{sn(x,k)} √((1 - k²t²)/(1 - t²)) dt` for `-K < x < K`
(the corrected form, DLMF erratum of 2010-07
  -08 reported by C. Karney); substitution `t = sin θ` in `E(am x, k)`. -/
@[dlmf 22.16.E14 "special case: real modulus 0 < k < 1"]
theorem Real.jacobiEpsilonk_eq_integral_sn (hk0 : 0 < k) (hk1 : k < 1) {x : ℝ}
    (hx0 : -Real.compEllIntKm (k ^ 2) < x) (hx1 : x < Real.compEllIntKm (k ^ 2)) :
    Real.jacobiEpsilonk x k =
      ∫ t in (0 : ℝ)..Real.jacobiSnm x (k ^ 2), √((1 - k ^ 2 * t ^ 2) / (1 - t ^ 2)) := by
  have hm : k ^ 2 < 1 := by nlinarith
  have a0 := je22b_jacobiAmm_strictMono hm hx0
  have a1 := je22b_jacobiAmm_strictMono hm hx1
  simp only [Real.jacobiAmm_neg hm, Real.jacobiAmm_compEllIntKm hm] at a0 a1
  set A := Real.jacobiAmm x (k ^ 2) with hA
  have hpt : ∀ θ ∈ Set.Ioo (-(π / 2)) (π / 2),
      |cos θ| * √((1 - k ^ 2 * sin θ ^ 2) / (1 - sin θ ^ 2)) =
        (1 - k ^ 2 * sin θ ^ 2) ^ (1 / 2 : ℝ) := by
    intro θ hθ
    have hc := Real.cos_pos_of_mem_Ioo hθ
    rw [abs_of_pos hc, show 1 - sin θ ^ 2 = cos θ ^ 2 by rw [← Real.sin_sq_add_cos_sq θ]; ring,
      Real.sqrt_div' _ (sq_nonneg _), Real.sqrt_sq hc.le, ← Real.sqrt_eq_rpow]
    field_simp
  have key : ∀ a b : ℝ, -(π / 2) < a → a ≤ b → b < π / 2 →
      ∫ t in sin a..sin b, √((1 - k ^ 2 * t ^ 2) / (1 - t ^ 2)) =
        ∫ θ in a..b, (1 - k ^ 2 * sin θ ^ 2) ^ (1 / 2 : ℝ) := by
    intro a b ha hab hb
    exact p22R1_subst_mono hab continuous_sin.continuousOn
      (Real.strictMonoOn_sin.mono (Set.Icc_subset_Icc ha.le hb.le))
      (fun θ _ => Real.hasDerivAt_sin θ)
      (fun θ hθ => hpt θ ⟨by linarith [hθ.1], by linarith [hθ.2]⟩)
  rw [← Real.incEllIntEm_jacobiAmm hm, Real.incEllIntEm, Real.jacobiSnm, ← hA]
  rcases le_total 0 A with h | h
  · have := key 0 A (by linarith [Real.pi_pos]) h a1
    rw [Real.sin_zero] at this; exact this.symm
  · have := key A 0 a0 h (by linarith [Real.pi_pos])
    rw [Real.sin_zero] at this
    rw [intervalIntegral.integral_symm, ← this, intervalIntegral.integral_symm, neg_neg]

/-- DLMF 22.16.15: `ℰ(x, k) = -k² ∫₀ˣ sn²(t, k) dt + x`. -/
@[dlmf 22.16.E15 "special case: real modulus with k² < 1"]
theorem Real.jacobiEpsilonk_eq_integral_jacobiSnm_sq (hm : k ^ 2 < 1) (x : ℝ) :
    Real.jacobiEpsilonk x k = -k ^ 2 * (∫ t in (0 : ℝ)..x, Real.jacobiSnm t (k ^ 2) ^ 2) + x := by
  have h : ∀ t, Real.jacobiDnm t (k ^ 2) ^ 2 = 1 - k ^ 2 * Real.jacobiSnm t (k ^ 2) ^ 2 :=
    fun t => by linear_combination (Real.mul_jacobiSnm_sq_add_jacobiDnm_sq hm t)
  have hc : (∫ t in (0 : ℝ)..x, Real.jacobiDnm t (k ^ 2) ^ 2) =
      ∫ t in (0 : ℝ)..x, (1 - k ^ 2 * Real.jacobiSnm t (k ^ 2) ^ 2) :=
    intervalIntegral.integral_congr fun t _ => h t
  rw [Real.jacobiEpsilonk, hc, intervalIntegral.integral_sub intervalIntegrable_const
      ((je22b_intervalIntegrable_jacobiSnm_sq hm 0 x).const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
  simp
  ring

/-- DLMF 22.16.16: `ℰ(x, k) = k² ∫₀ˣ cn²(t, k) dt + k'² x`. -/
@[dlmf 22.16.E16 "special case: real modulus with k² < 1"]
theorem Real.jacobiEpsilonk_eq_integral_jacobiCnm_sq (hm : k ^ 2 < 1) (x : ℝ) :
    Real.jacobiEpsilonk x k =
      k ^ 2 * (∫ t in (0 : ℝ)..x, Real.jacobiCnm t (k ^ 2) ^ 2) + (1 - k ^ 2) * x := by
  have h : ∀ t, Real.jacobiCnm t (k ^ 2) ^ 2 = 1 - Real.jacobiSnm t (k ^ 2) ^ 2 :=
    fun t => by linear_combination (Real.jacobiSnm_sq_add_jacobiCnm_sq t (k ^ 2))
  have hc : (∫ t in (0 : ℝ)..x, Real.jacobiCnm t (k ^ 2) ^ 2) =
      ∫ t in (0 : ℝ)..x, (1 - Real.jacobiSnm t (k ^ 2) ^ 2) :=
    intervalIntegral.integral_congr fun t _ => h t
  rw [hc, intervalIntegral.integral_sub intervalIntegrable_const
      (je22b_intervalIntegrable_jacobiSnm_sq hm 0 x),
    Real.jacobiEpsilonk_eq_integral_jacobiSnm_sq hm x, intervalIntegral.integral_const]
  simp
  ring

/-- DLMF 22.16.29: `ℰ(x + 2K, k) = ℰ(x, k) + 2E(k)`. -/
@[dlmf 22.16.E29 "special case: real modulus with k² < 1"]
theorem Real.jacobiEpsilonk_add_two_compEllIntKm (hm : k ^ 2 < 1) (x : ℝ) :
    Real.jacobiEpsilonk (x + 2 * Real.compEllIntKm (k ^ 2)) k =
      Real.jacobiEpsilonk x k + 2 * Real.compEllIntEm (k ^ 2) := by
  rw [← Real.incEllIntEm_jacobiAmm hm, ← Real.incEllIntEm_jacobiAmm hm,
    Real.jacobiAmm_add_two_compEllIntKm hm, Real.incEllIntEm_add_pi hm]

lemma p22R1_hasDerivAt_eps {k : ℝ} (hm : k ^ 2 < 1) (x : ℝ) :
    HasDerivAt (fun x => Real.jacobiEpsilonk x k) (Real.jacobiDnm x (k ^ 2) ^ 2) x :=
  (((je22b_continuous_jacobiDnm hm).pow 2).integral_hasStrictDerivAt 0 x).hasDerivAt

lemma p22R1_cont_sn {m : ℝ} (hm : m < 1) : Continuous fun u => Real.jacobiSnm u m :=
  continuous_iff_continuousAt.mpr fun u => (Real.hasDerivAt_jacobiSnm hm u).continuousAt

lemma p22R1_cont_cn {m : ℝ} (hm : m < 1) : Continuous fun u => Real.jacobiCnm u m :=
  continuous_iff_continuousAt.mpr fun u => (Real.hasDerivAt_jacobiCnm hm u).continuousAt

lemma p22R1_ftc {F f : ℝ → ℝ} (hF : ∀ t, HasDerivAt F (f t) t) (hf : Continuous f) (x : ℝ) :
    ∫ t in (0 : ℝ)..x, f t = F x - F 0 :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hF t) (hf.intervalIntegrable _ _)

lemma p22R1_sn_zero {m : ℝ} (hm : m < 1) : Real.jacobiSnm 0 m = 0 := by
  simp [Real.jacobiSnm, Real.jacobiAmm_zero hm]


lemma p22R1_cn_pos {m : ℝ} (hm : m < 1) {t : ℝ} (h0 : -Real.compEllIntKm m < t)
    (h1 : t < Real.compEllIntKm m) : 0 < Real.jacobiCnm t m := by
  have a0 := je22b_jacobiAmm_strictMono hm h0
  have a1 := je22b_jacobiAmm_strictMono hm h1
  simp only [Real.jacobiAmm_neg hm, Real.jacobiAmm_compEllIntKm hm] at a0 a1
  exact Real.cos_pos_of_mem_Ioo ⟨a0, a1⟩

lemma p22R1_ftc_on {F f : ℝ → ℝ} {x : ℝ} (hF : ∀ t ∈ Set.uIcc 0 x, HasDerivAt F (f t) t)
    (hf : ContinuousOn f (Set.uIcc 0 x)) :
    ∫ t in (0 : ℝ)..x, f t = F x - F 0 :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt hF hf.intervalIntegrable


/-- DLMF 22.16.18: `ℰ(x,k) = -k² ∫₀ˣ cd²(t,k) dt + x + k² sn(x,k) cd(x,k)`. -/
@[dlmf 22.16.E18 "special case: real modulus 0 < k < 1"]
theorem Real.jacobiEpsilonk_eq_integral_cd_sq (hk0 : 0 < k) (hk1 : k < 1) (x : ℝ) :
    Real.jacobiEpsilonk x k =
      -k ^ 2 * (∫ t in (0 : ℝ)..x, (Real.jacobiCnm t (k ^ 2) / Real.jacobiDnm t (k ^ 2)) ^ 2) +
        x + k ^ 2 * Real.jacobiSnm x (k ^ 2) *
          (Real.jacobiCnm x (k ^ 2) / Real.jacobiDnm x (k ^ 2)) := by
  have hm : k ^ 2 < 1 := by nlinarith
  have hdn := fun t => (Real.jacobiDnm_pos hm t).ne'
  have cdn := je22b_continuous_jacobiDnm hm
  have csn := p22R1_cont_sn hm
  have ccn := p22R1_cont_cn hm
  have cg : Continuous fun t => (Real.jacobiCnm t (k ^ 2) / Real.jacobiDnm t (k ^ 2)) ^ 2 := by
    first
    | exact (ccn.div cdn hdn).pow 2
    | exact (csn.div cdn hdn).pow 2
    | exact (continuous_const.div cdn hdn).pow 2
  have hF : ∀ t, HasDerivAt (fun t => 1 * t + k ^ 2 * (Real.jacobiSnm t (k ^ 2) * (Real.jacobiCnm t (k ^ 2) / Real.jacobiDnm t (k ^ 2))))
      (Real.jacobiDnm t (k ^ 2) ^ 2 - (-k ^ 2) * (Real.jacobiCnm t (k ^ 2) / Real.jacobiDnm t (k ^ 2)) ^ 2) t := by
    intro t
    refine (((hasDerivAt_id t).const_mul (1)).add
      (((Real.hasDerivAt_jacobiSnm hm t).mul ((Real.hasDerivAt_jacobiCnm hm t).div
        (Real.hasDerivAt_jacobiDnm hm t) (hdn t))).const_mul (k ^ 2))).congr_deriv ?_
    have h1 := Real.jacobiSnm_sq_add_jacobiCnm_sq t (k ^ 2)
    have h2 := Real.mul_jacobiSnm_sq_add_jacobiDnm_sq hm t
    have hd := hdn t
    simp only [Pi.div_apply]
    generalize Real.jacobiSnm t (k ^ 2) = s at *
    generalize Real.jacobiCnm t (k ^ 2) = c at *
    generalize Real.jacobiDnm t (k ^ 2) = d at *
    field_simp
    linear_combination (c^2*k^2-d^2) * h2
  have cd2 : Continuous fun t => Real.jacobiDnm t (k ^ 2) ^ 2 := cdn.pow 2
  have cg2 : Continuous fun t => (-k ^ 2) * (Real.jacobiCnm t (k ^ 2) / Real.jacobiDnm t (k ^ 2)) ^ 2 := cg.const_mul _
  have key := p22R1_ftc hF (cd2.sub cg2) x
  rw [intervalIntegral.integral_sub (cd2.intervalIntegrable _ _)
    (cg2.intervalIntegrable _ _), intervalIntegral.integral_const_mul,
    p22R1_sn_zero hm] at key
  rw [Real.jacobiEpsilonk]
  simp only [mul_zero, zero_mul, add_zero, sub_zero] at key
  linarith

/-- DLMF 22.16.19: `ℰ(x,k) = k²k'² ∫₀ˣ sd²(t,k) dt + k'² x + k² sn(x,k) cd(x,k)`. -/
@[dlmf 22.16.E19 "special case: real modulus 0 < k < 1"]
theorem Real.jacobiEpsilonk_eq_integral_sd_sq (hk0 : 0 < k) (hk1 : k < 1) (x : ℝ) :
    Real.jacobiEpsilonk x k =
      k ^ 2 * (1 - k ^ 2) *
          (∫ t in (0 : ℝ)..x, (Real.jacobiSnm t (k ^ 2) / Real.jacobiDnm t (k ^ 2)) ^ 2) +
        (1 - k ^ 2) * x + k ^ 2 * Real.jacobiSnm x (k ^ 2) *
          (Real.jacobiCnm x (k ^ 2) / Real.jacobiDnm x (k ^ 2)) := by
  have hm : k ^ 2 < 1 := by nlinarith
  have hdn := fun t => (Real.jacobiDnm_pos hm t).ne'
  have cdn := je22b_continuous_jacobiDnm hm
  have csn := p22R1_cont_sn hm
  have ccn := p22R1_cont_cn hm
  have cg : Continuous fun t => (Real.jacobiSnm t (k ^ 2) / Real.jacobiDnm t (k ^ 2)) ^ 2 := by
    first
    | exact (ccn.div cdn hdn).pow 2
    | exact (csn.div cdn hdn).pow 2
    | exact (continuous_const.div cdn hdn).pow 2
  have hF : ∀ t, HasDerivAt (fun t => (1 - k ^ 2) * t + k ^ 2 * (Real.jacobiSnm t (k ^ 2) * (Real.jacobiCnm t (k ^ 2) / Real.jacobiDnm t (k ^ 2))))
      (Real.jacobiDnm t (k ^ 2) ^ 2 - (k ^ 2 * (1 - k ^ 2)) * (Real.jacobiSnm t (k ^ 2) / Real.jacobiDnm t (k ^ 2)) ^ 2) t := by
    intro t
    refine (((hasDerivAt_id t).const_mul ((1 - k ^ 2))).add
      (((Real.hasDerivAt_jacobiSnm hm t).mul ((Real.hasDerivAt_jacobiCnm hm t).div
        (Real.hasDerivAt_jacobiDnm hm t) (hdn t))).const_mul (k ^ 2))).congr_deriv ?_
    have h1 := Real.jacobiSnm_sq_add_jacobiCnm_sq t (k ^ 2)
    have h2 := Real.mul_jacobiSnm_sq_add_jacobiDnm_sq hm t
    have hd := hdn t
    simp only [Pi.div_apply]
    generalize Real.jacobiSnm t (k ^ 2) = s at *
    generalize Real.jacobiCnm t (k ^ 2) = c at *
    generalize Real.jacobiDnm t (k ^ 2) = d at *
    field_simp
    linear_combination (k^2) * h1 +
        (c^2*k^2-d^2-k^2) * h2
  have cd2 : Continuous fun t => Real.jacobiDnm t (k ^ 2) ^ 2 := cdn.pow 2
  have cg2 : Continuous fun t => (k ^ 2 * (1 - k ^ 2)) * (Real.jacobiSnm t (k ^ 2) / Real.jacobiDnm t (k ^ 2)) ^ 2 := cg.const_mul _
  have key := p22R1_ftc hF (cd2.sub cg2) x
  rw [intervalIntegral.integral_sub (cd2.intervalIntegrable _ _)
    (cg2.intervalIntegrable _ _), intervalIntegral.integral_const_mul,
    p22R1_sn_zero hm] at key
  rw [Real.jacobiEpsilonk]
  simp only [mul_zero, zero_mul, add_zero, sub_zero] at key
  linarith

/-- DLMF 22.16.20: `ℰ(x,k) = k'² ∫₀ˣ nd²(t,k) dt + k² sn(x,k) cd(x,k)`. -/
@[dlmf 22.16.E20 "special case: real modulus 0 < k < 1"]
theorem Real.jacobiEpsilonk_eq_integral_nd_sq (hk0 : 0 < k) (hk1 : k < 1) (x : ℝ) :
    Real.jacobiEpsilonk x k =
      (1 - k ^ 2) * (∫ t in (0 : ℝ)..x, (1 / Real.jacobiDnm t (k ^ 2)) ^ 2) +
        k ^ 2 * Real.jacobiSnm x (k ^ 2) * (Real.jacobiCnm x (k ^ 2) / Real.jacobiDnm x (k ^ 2)) :=
            by
  have hm : k ^ 2 < 1 := by nlinarith
  have hdn := fun t => (Real.jacobiDnm_pos hm t).ne'
  have cdn := je22b_continuous_jacobiDnm hm
  have csn := p22R1_cont_sn hm
  have ccn := p22R1_cont_cn hm
  have cg : Continuous fun t => (1 / Real.jacobiDnm t (k ^ 2)) ^ 2 := by
    first
    | exact (ccn.div cdn hdn).pow 2
    | exact (csn.div cdn hdn).pow 2
    | exact (continuous_const.div cdn hdn).pow 2
  have hF : ∀ t, HasDerivAt (fun t => 0 * t + k ^ 2 * (Real.jacobiSnm t (k ^ 2) * (Real.jacobiCnm t (k ^ 2) / Real.jacobiDnm t (k ^ 2))))
      (Real.jacobiDnm t (k ^ 2) ^ 2 - ((1 - k ^ 2)) * (1 / Real.jacobiDnm t (k ^ 2)) ^ 2) t := by
    intro t
    refine (((hasDerivAt_id t).const_mul (0)).add
      (((Real.hasDerivAt_jacobiSnm hm t).mul ((Real.hasDerivAt_jacobiCnm hm t).div
        (Real.hasDerivAt_jacobiDnm hm t) (hdn t))).const_mul (k ^ 2))).congr_deriv ?_
    have h1 := Real.jacobiSnm_sq_add_jacobiCnm_sq t (k ^ 2)
    have h2 := Real.mul_jacobiSnm_sq_add_jacobiDnm_sq hm t
    have hd := hdn t
    simp only [Pi.div_apply]
    generalize Real.jacobiSnm t (k ^ 2) = s at *
    generalize Real.jacobiCnm t (k ^ 2) = c at *
    generalize Real.jacobiDnm t (k ^ 2) = d at *
    field_simp
    linear_combination (k^2) * h1 +
        (c^2*k^2-d^2-1) * h2
  have cd2 : Continuous fun t => Real.jacobiDnm t (k ^ 2) ^ 2 := cdn.pow 2
  have cg2 : Continuous fun t => ((1 - k ^ 2)) * (1 / Real.jacobiDnm t (k ^ 2)) ^ 2 := cg.const_mul _
  have key := p22R1_ftc hF (cd2.sub cg2) x
  rw [intervalIntegral.integral_sub (cd2.intervalIntegrable _ _)
    (cg2.intervalIntegrable _ _), intervalIntegral.integral_const_mul,
    p22R1_sn_zero hm] at key
  rw [Real.jacobiEpsilonk]
  simp only [mul_zero, zero_mul, add_zero, sub_zero] at key
  linarith

/-- DLMF 22.16.21: `ℰ(x,k) = -∫₀ˣ dc²(t,k) dt + x + sn(x,k) dc(x,k)` for `-K < x < K`. -/
@[dlmf 22.16.E21 "special case: real modulus 0 < k < 1"]
theorem Real.jacobiEpsilonk_eq_integral_dc_sq (hk0 : 0 < k) (hk1 : k < 1) {x : ℝ}
    (hx0 : -Real.compEllIntKm (k ^ 2) < x) (hx1 : x < Real.compEllIntKm (k ^ 2)) :
    Real.jacobiEpsilonk x k =
      -(∫ t in (0 : ℝ)..x, (Real.jacobiDnm t (k ^ 2) / Real.jacobiCnm t (k ^ 2)) ^ 2) + x +
        Real.jacobiSnm x (k ^ 2) * (Real.jacobiDnm x (k ^ 2) / Real.jacobiCnm x (k ^ 2)) := by
  have hm : k ^ 2 < 1 := by nlinarith
  have hdn := fun t => (Real.jacobiDnm_pos hm t).ne'
  have hcn : ∀ t ∈ Set.uIcc 0 x, Real.jacobiCnm t (k ^ 2) ≠ 0 := by
    intro t ht
    have hK := Real.compEllIntKm_pos hm
    refine (p22R1_cn_pos hm ?_ ?_).ne'
    · cases le_total 0 x with
      | inl h => rw [Set.uIcc_of_le h] at ht; linarith [ht.1]
      | inr h => rw [Set.uIcc_of_ge h] at ht; linarith [ht.1]
    · cases le_total 0 x with
      | inl h => rw [Set.uIcc_of_le h] at ht; linarith [ht.2]
      | inr h => rw [Set.uIcc_of_ge h] at ht; linarith [ht.2]
  have cdn := je22b_continuous_jacobiDnm hm
  have csn := p22R1_cont_sn hm
  have ccn := p22R1_cont_cn hm
  have cg : ContinuousOn (fun t => (Real.jacobiDnm t (k ^ 2) / Real.jacobiCnm t (k ^ 2)) ^ 2) (Set.uIcc 0 x) := by
    first
    | exact (cdn.continuousOn.div ccn.continuousOn hcn).pow 2
    | exact (csn.continuousOn.div ccn.continuousOn hcn).pow 2
    | exact (continuousOn_const.div ccn.continuousOn hcn).pow 2
  have hF : ∀ t ∈ Set.uIcc 0 x, HasDerivAt (fun t => 1 * t + Real.jacobiSnm t (k ^ 2) * (Real.jacobiDnm t (k ^ 2) / Real.jacobiCnm t (k ^ 2)))
      (Real.jacobiDnm t (k ^ 2) ^ 2 - (-1) * (Real.jacobiDnm t (k ^ 2) / Real.jacobiCnm t (k ^ 2)) ^ 2) t := by
    intro t ht
    refine (((hasDerivAt_id t).const_mul (1)).add
      ((Real.hasDerivAt_jacobiSnm hm t).mul ((Real.hasDerivAt_jacobiDnm hm t).div
        (Real.hasDerivAt_jacobiCnm hm t) (hcn t ht)))).congr_deriv ?_
    have h1 := Real.jacobiSnm_sq_add_jacobiCnm_sq t (k ^ 2)
    have h2 := Real.mul_jacobiSnm_sq_add_jacobiDnm_sq hm t
    have hd := hcn t ht
    simp only [Pi.div_apply]
    generalize Real.jacobiSnm t (k ^ 2) = s at *
    generalize Real.jacobiCnm t (k ^ 2) = c at *
    generalize Real.jacobiDnm t (k ^ 2) = d at *
    field_simp
    linear_combination (d^2) * h1 +
        (-c^2) * h2
  have cd2 : ContinuousOn (fun t => Real.jacobiDnm t (k ^ 2) ^ 2) (Set.uIcc 0 x) := (cdn.pow 2).continuousOn
  have cg2 : ContinuousOn (fun t => (-1) * (Real.jacobiDnm t (k ^ 2) / Real.jacobiCnm t (k ^ 2)) ^ 2) (Set.uIcc 0 x) := continuousOn_const.mul cg
  have key := p22R1_ftc_on hF (cd2.sub cg2)
  rw [intervalIntegral.integral_sub cd2.intervalIntegrable cg2.intervalIntegrable,
    intervalIntegral.integral_const_mul, p22R1_sn_zero hm] at key
  rw [Real.jacobiEpsilonk]
  simp only [mul_zero, zero_mul, add_zero, sub_zero] at key
  linarith

/-- DLMF 22.16.22: `ℰ(x,k) = -k'² ∫₀ˣ nc²(t,k) dt + k'² x + sn(x,k) dc(x,k)` for `-K < x < K`. -/
@[dlmf 22.16.E22 "special case: real modulus 0 < k < 1"]
theorem Real.jacobiEpsilonk_eq_integral_nc_sq (hk0 : 0 < k) (hk1 : k < 1) {x : ℝ}
    (hx0 : -Real.compEllIntKm (k ^ 2) < x) (hx1 : x < Real.compEllIntKm (k ^ 2)) :
    Real.jacobiEpsilonk x k =
      -(1 - k ^ 2) * (∫ t in (0 : ℝ)..x, (1 / Real.jacobiCnm t (k ^ 2)) ^ 2) + (1 - k ^ 2) * x +
        Real.jacobiSnm x (k ^ 2) * (Real.jacobiDnm x (k ^ 2) / Real.jacobiCnm x (k ^ 2)) := by
  have hm : k ^ 2 < 1 := by nlinarith
  have hdn := fun t => (Real.jacobiDnm_pos hm t).ne'
  have hcn : ∀ t ∈ Set.uIcc 0 x, Real.jacobiCnm t (k ^ 2) ≠ 0 := by
    intro t ht
    have hK := Real.compEllIntKm_pos hm
    refine (p22R1_cn_pos hm ?_ ?_).ne'
    · cases le_total 0 x with
      | inl h => rw [Set.uIcc_of_le h] at ht; linarith [ht.1]
      | inr h => rw [Set.uIcc_of_ge h] at ht; linarith [ht.1]
    · cases le_total 0 x with
      | inl h => rw [Set.uIcc_of_le h] at ht; linarith [ht.2]
      | inr h => rw [Set.uIcc_of_ge h] at ht; linarith [ht.2]
  have cdn := je22b_continuous_jacobiDnm hm
  have csn := p22R1_cont_sn hm
  have ccn := p22R1_cont_cn hm
  have cg : ContinuousOn (fun t => (1 / Real.jacobiCnm t (k ^ 2)) ^ 2) (Set.uIcc 0 x) := by
    first
    | exact (cdn.continuousOn.div ccn.continuousOn hcn).pow 2
    | exact (csn.continuousOn.div ccn.continuousOn hcn).pow 2
    | exact (continuousOn_const.div ccn.continuousOn hcn).pow 2
  have hF : ∀ t ∈ Set.uIcc 0 x, HasDerivAt (fun t => (1 - k ^ 2) * t + Real.jacobiSnm t (k ^ 2) * (Real.jacobiDnm t (k ^ 2) / Real.jacobiCnm t (k ^ 2)))
      (Real.jacobiDnm t (k ^ 2) ^ 2 - (-(1 - k ^ 2)) * (1 / Real.jacobiCnm t (k ^ 2)) ^ 2) t := by
    intro t ht
    refine (((hasDerivAt_id t).const_mul ((1 - k ^ 2))).add
      ((Real.hasDerivAt_jacobiSnm hm t).mul ((Real.hasDerivAt_jacobiDnm hm t).div
        (Real.hasDerivAt_jacobiCnm hm t) (hcn t ht)))).congr_deriv ?_
    have h1 := Real.jacobiSnm_sq_add_jacobiCnm_sq t (k ^ 2)
    have h2 := Real.mul_jacobiSnm_sq_add_jacobiDnm_sq hm t
    have hd := hcn t ht
    simp only [Pi.div_apply]
    generalize Real.jacobiSnm t (k ^ 2) = s at *
    generalize Real.jacobiCnm t (k ^ 2) = c at *
    generalize Real.jacobiDnm t (k ^ 2) = d at *
    field_simp
    linear_combination (d^2-k^2) * h1 +
        (-c^2+1) * h2
  have cd2 : ContinuousOn (fun t => Real.jacobiDnm t (k ^ 2) ^ 2) (Set.uIcc 0 x) := (cdn.pow 2).continuousOn
  have cg2 : ContinuousOn (fun t => (-(1 - k ^ 2)) * (1 / Real.jacobiCnm t (k ^ 2)) ^ 2) (Set.uIcc 0 x) := continuousOn_const.mul cg
  have key := p22R1_ftc_on hF (cd2.sub cg2)
  rw [intervalIntegral.integral_sub cd2.intervalIntegrable cg2.intervalIntegrable,
    intervalIntegral.integral_const_mul, p22R1_sn_zero hm] at key
  rw [Real.jacobiEpsilonk]
  simp only [mul_zero, zero_mul, add_zero, sub_zero] at key
  linarith

/-- DLMF 22.16.23: `ℰ(x,k) = -k'² ∫₀ˣ sc²(t,k) dt + sn(x,k) dc(x,k)` for `-K < x < K`. -/
@[dlmf 22.16.E23 "special case: real modulus 0 < k < 1"]
theorem Real.jacobiEpsilonk_eq_integral_sc_sq (hk0 : 0 < k) (hk1 : k < 1) {x : ℝ}
    (hx0 : -Real.compEllIntKm (k ^ 2) < x) (hx1 : x < Real.compEllIntKm (k ^ 2)) :
    Real.jacobiEpsilonk x k =
      -(1 - k ^ 2) * (∫ t in (0 : ℝ)..x,
          (Real.jacobiSnm t (k ^ 2) / Real.jacobiCnm t (k ^ 2)) ^ 2) +
        Real.jacobiSnm x (k ^ 2) * (Real.jacobiDnm x (k ^ 2) / Real.jacobiCnm x (k ^ 2)) := by
  have hm : k ^ 2 < 1 := by nlinarith
  have hdn := fun t => (Real.jacobiDnm_pos hm t).ne'
  have hcn : ∀ t ∈ Set.uIcc 0 x, Real.jacobiCnm t (k ^ 2) ≠ 0 := by
    intro t ht
    have hK := Real.compEllIntKm_pos hm
    refine (p22R1_cn_pos hm ?_ ?_).ne'
    · cases le_total 0 x with
      | inl h => rw [Set.uIcc_of_le h] at ht; linarith [ht.1]
      | inr h => rw [Set.uIcc_of_ge h] at ht; linarith [ht.1]
    · cases le_total 0 x with
      | inl h => rw [Set.uIcc_of_le h] at ht; linarith [ht.2]
      | inr h => rw [Set.uIcc_of_ge h] at ht; linarith [ht.2]
  have cdn := je22b_continuous_jacobiDnm hm
  have csn := p22R1_cont_sn hm
  have ccn := p22R1_cont_cn hm
  have cg : ContinuousOn (fun t => (Real.jacobiSnm t (k ^ 2) / Real.jacobiCnm t (k ^ 2)) ^ 2) (Set.uIcc 0 x) := by
    first
    | exact (cdn.continuousOn.div ccn.continuousOn hcn).pow 2
    | exact (csn.continuousOn.div ccn.continuousOn hcn).pow 2
    | exact (continuousOn_const.div ccn.continuousOn hcn).pow 2
  have hF : ∀ t ∈ Set.uIcc 0 x, HasDerivAt (fun t => 0 * t + Real.jacobiSnm t (k ^ 2) * (Real.jacobiDnm t (k ^ 2) / Real.jacobiCnm t (k ^ 2)))
      (Real.jacobiDnm t (k ^ 2) ^ 2 - (-(1 - k ^ 2)) * (Real.jacobiSnm t (k ^ 2) / Real.jacobiCnm t (k ^ 2)) ^ 2) t := by
    intro t ht
    refine (((hasDerivAt_id t).const_mul (0)).add
      ((Real.hasDerivAt_jacobiSnm hm t).mul ((Real.hasDerivAt_jacobiDnm hm t).div
        (Real.hasDerivAt_jacobiCnm hm t) (hcn t ht)))).congr_deriv ?_
    have h1 := Real.jacobiSnm_sq_add_jacobiCnm_sq t (k ^ 2)
    have h2 := Real.mul_jacobiSnm_sq_add_jacobiDnm_sq hm t
    have hd := hcn t ht
    simp only [Pi.div_apply]
    generalize Real.jacobiSnm t (k ^ 2) = s at *
    generalize Real.jacobiCnm t (k ^ 2) = c at *
    generalize Real.jacobiDnm t (k ^ 2) = d at *
    field_simp
    linear_combination (d^2-1) * h1 +
        (-c^2+1) * h2
  have cd2 : ContinuousOn (fun t => Real.jacobiDnm t (k ^ 2) ^ 2) (Set.uIcc 0 x) := (cdn.pow 2).continuousOn
  have cg2 : ContinuousOn (fun t => (-(1 - k ^ 2)) * (Real.jacobiSnm t (k ^ 2) / Real.jacobiCnm t (k ^ 2)) ^ 2) (Set.uIcc 0 x) := continuousOn_const.mul cg
  have key := p22R1_ftc_on hF (cd2.sub cg2)
  rw [intervalIntegral.integral_sub cd2.intervalIntegrable cg2.intervalIntegrable,
    intervalIntegral.integral_const_mul, p22R1_sn_zero hm] at key
  rw [Real.jacobiEpsilonk]
  simp only [mul_zero, zero_mul, add_zero, sub_zero] at key
  linarith

/-- DLMF 22.16.24: `ℰ(x,k) = -∫₀ˣ (ns²(t,k) - t⁻²) dt + x⁻¹ + x - cn(x,k) ds(x,k)` for
`0 < |x| < 2K` (the integrand has a removable singularity at `t = 0`). Admitted. -/
@[dlmf 22.16.E24 "special case: real modulus 0 < k < 1, x ≠ 0"]
theorem Real.jacobiEpsilonk_eq_integral_ns_sq (hk0 : 0 < k) (hk1 : k < 1) {x : ℝ} (hx : x ≠ 0)
    (hx0 : -(2 * Real.compEllIntKm (k ^ 2)) < x) (hx1 : x < 2 * Real.compEllIntKm (k ^ 2)) :
    Real.jacobiEpsilonk x k =
      -(∫ t in (0 : ℝ)..x, ((1 / Real.jacobiSnm t (k ^ 2)) ^ 2 - t⁻¹ ^ 2)) + x⁻¹ + x -
        Real.jacobiCnm x (k ^ 2) * (Real.jacobiDnm x (k ^ 2) / Real.jacobiSnm x (k ^ 2)) := by
  sorry

/-- DLMF 22.16.25: `ℰ(x,k) = -∫₀ˣ (ds²(t,k) - t⁻²) dt + x⁻¹ + k'² x - cn(x,k) ds(x,k)` for
`0 < |x| < 2K`. Admitted. -/
@[dlmf 22.16.E25 "special case: real modulus 0 < k < 1, x ≠ 0"]
theorem Real.jacobiEpsilonk_eq_integral_ds_sq (hk0 : 0 < k) (hk1 : k < 1) {x : ℝ} (hx : x ≠ 0)
    (hx0 : -(2 * Real.compEllIntKm (k ^ 2)) < x) (hx1 : x < 2 * Real.compEllIntKm (k ^ 2)) :
    Real.jacobiEpsilonk x k =
      -(∫ t in (0 : ℝ)..x,
          ((Real.jacobiDnm t (k ^ 2) / Real.jacobiSnm t (k ^ 2)) ^ 2 - t⁻¹ ^ 2)) + x⁻¹ +
        (1 - k ^ 2) * x -
        Real.jacobiCnm x (k ^ 2) * (Real.jacobiDnm x (k ^ 2) / Real.jacobiSnm x (k ^ 2)) := by
  sorry

/-- DLMF 22.16.26: `ℰ(x,k) = -∫₀ˣ (cs²(t,k) - t⁻²) dt + x⁻¹ - cn(x,k) ds(x,k)` for
`0 < |x| < 2K`. Admitted. -/
@[dlmf 22.16.E26 "special case: real modulus 0 < k < 1, x ≠ 0"]
theorem Real.jacobiEpsilonk_eq_integral_cs_sq (hk0 : 0 < k) (hk1 : k < 1) {x : ℝ} (hx : x ≠ 0)
    (hx0 : -(2 * Real.compEllIntKm (k ^ 2)) < x) (hx1 : x < 2 * Real.compEllIntKm (k ^ 2)) :
    Real.jacobiEpsilonk x k =
      -(∫ t in (0 : ℝ)..x,
          ((Real.jacobiCnm t (k ^ 2) / Real.jacobiSnm t (k ^ 2)) ^ 2 - t⁻¹ ^ 2)) + x⁻¹ -
        Real.jacobiCnm x (k ^ 2) * (Real.jacobiDnm x (k ^ 2) / Real.jacobiSnm x (k ^ 2)) := by
  sorry

/-- DLMF 22.16.27: the quasi-addition formula
`ℰ(x₁ + x₂, k) = ℰ(x₁, k) + ℰ(x₂, k) - k² sn(x₁,k) sn(x₂,k) sn(x₁ + x₂,k)`. -/
@[dlmf 22.16.E27 "special case: real modulus with k² < 1"]
theorem Real.jacobiEpsilonk_add (hm : k ^ 2 < 1) (x₁ x₂ : ℝ) :
    Real.jacobiEpsilonk (x₁ + x₂) k = Real.jacobiEpsilonk x₁ k + Real.jacobiEpsilonk x₂ k -
      k ^ 2 * Real.jacobiSnm x₁ (k ^ 2) * Real.jacobiSnm x₂ (k ^ 2) *
        Real.jacobiSnm (x₁ + x₂) (k ^ 2) := by
  set m := k ^ 2 with hmdef
  set v := x₂
  let G : ℝ → ℝ := fun u => Real.jacobiEpsilonk (u + v) k - Real.jacobiEpsilonk u k -
    Real.jacobiEpsilonk v k + m * Real.jacobiSnm u m * Real.jacobiSnm v m * Real.jacobiSnm (u + v) m
  have hG : ∀ u, HasDerivAt G 0 u := by
    intro u
    have e1 := (p22R1_hasDerivAt_eps hm (u + v)).comp u ((hasDerivAt_id u).add_const v)
    have e2 := p22R1_hasDerivAt_eps hm u
    have s1 := Real.hasDerivAt_jacobiSnm hm u
    have s2 := (Real.hasDerivAt_jacobiSnm hm (u + v)).comp u ((hasDerivAt_id u).add_const v)
    have hd := (((e1.sub e2).sub_const (Real.jacobiEpsilonk v k)).add
      (((s1.const_mul m).mul_const (Real.jacobiSnm v m)).mul s2))
    refine HasDerivAt.congr_deriv (f := G) hd ?_
    simp only [id, Function.comp_def, mul_zero, zero_add, add_zero]
    rw [Real.jacobiSnm_add hm, Real.jacobiCnm_add hm, Real.jacobiDnm_add hm]
    have hD := (Real.one_sub_mul_jacobiSnm_sq_mul_sq_pos hm u v).ne'
    have h1 := Real.jacobiSnm_sq_add_jacobiCnm_sq u m
    have h2 := Real.mul_jacobiSnm_sq_add_jacobiDnm_sq hm u
    have h3 := Real.jacobiSnm_sq_add_jacobiCnm_sq v m
    have h4 := Real.mul_jacobiSnm_sq_add_jacobiDnm_sq hm v
    generalize Real.jacobiSnm u m = su at *
    generalize Real.jacobiCnm u m = cu at *
    generalize Real.jacobiDnm u m = du at *
    generalize Real.jacobiSnm v m = sv at *
    generalize Real.jacobiCnm v m = cv at *
    generalize Real.jacobiDnm v m = dv at *
    generalize hDdef : 1 - m * su ^ 2 * sv ^ 2 = D at hD ⊢
    field_simp
    linear_combination (-du^2*cv^2*m*D+du^2*m*D) * h1 +
        (su^2*du^2*m*D+cu^2*du^2*m*D-du^2*m*D) * h3 +
        (du^2*D) * h4 +
        (-su*cu*du*sv*cv*dv*m+du^2*dv^2+du^2*D) * hDdef
  have := is_const_of_deriv_eq_zero (fun u => (hG u).differentiableAt) (fun u => (hG u).deriv) x₁ 0
  simp only [G, zero_add, Real.jacobiEpsilonk, intervalIntegral.integral_same,
    Real.jacobiSnm, Real.jacobiAmm_zero hm, Real.sin_zero] at this ⊢
  linarith

/-- DLMF 22.16.28: `ℰ(x + K, k) = ℰ(x, k) + E(k) - k² sn(x,k) cd(x,k)`. -/
@[dlmf 22.16.E28 "special case: real modulus with k² < 1"]
theorem Real.jacobiEpsilonk_add_compEllIntKm (hm : k ^ 2 < 1) (x : ℝ) :
    Real.jacobiEpsilonk (x + Real.compEllIntKm (k ^ 2)) k = Real.jacobiEpsilonk x k +
      Real.compEllIntEm (k ^ 2) -
        k ^ 2 * Real.jacobiSnm x (k ^ 2) * (Real.jacobiCnm x (k ^ 2) / Real.jacobiDnm x (k ^ 2)) :=
            by
  rw [Real.jacobiEpsilonk_add hm, (Real.jacobi_compEllIntKm hm).1, (Real.jacobi_add_compEllIntKm hm x).1,
    ← Real.incEllIntEm_jacobiAmm hm (Real.compEllIntKm (k ^ 2)), Real.jacobiAmm_compEllIntKm hm,
    Real.incEllIntEm_pi_div_two]
  ring

/-- DLMF 22.16.30: `ℰ(x,k) = θ₄'(ξ,q)/(θ₃²(0,q) θ₄(ξ,q)) + (E(k)/K(k)) x` with
`ξ = x/θ₃²(0,q) = πx/(2K)` and `θ_j(·, q) = θ_j(·|τ)`, `τ = iK'/K`, for real `x` and
`0 < k < 1`. Admitted. -/
@[dlmf 22.16.E30 "special case: real x, 0 < k < 1"]
theorem Real.jacobiEpsilonk_eq_theta (hk0 : 0 < k) (hk1 : k < 1) (x : ℝ) :
    (Real.jacobiEpsilonk x k : ℂ) =
      deriv (fun ξ => jacobiThetaFourTau ξ (jacobiTauk k))
          (x / jacobiThetaThreeTau 0 (jacobiTauk k) ^ 2) /
        (jacobiThetaThreeTau 0 (jacobiTauk k) ^ 2 *
          jacobiThetaFourTau (x / jacobiThetaThreeTau 0 (jacobiTauk k) ^ 2) (jacobiTauk k)) +
      (Real.compEllIntEm (k ^ 2) / Real.compEllIntKm (k ^ 2) * x : ℝ) := by
  sorry

end Epsilon

/-! ### Jacobi's Zeta function -/

section Zeta

variable {k : ℝ}

/-- DLMF §22.16(iii), prose: `Z(x|k)` satisfies the quasi-addition formula 22.16.27,
`Z(x₁ + x₂|k) = Z(x₁|k) + Z(x₂|k) - k² sn(x₁) sn(x₂) sn(x₁ + x₂)` (from 22.16.27). -/
@[dlmf 22.16.iii "special case: real modulus with k² < 1"]
theorem Real.jacobiZetaFunctionk_add (hm : k ^ 2 < 1) (x₁ x₂ : ℝ) :
    Real.jacobiZetaFunctionk (x₁ + x₂) k =
      Real.jacobiZetaFunctionk x₁ k + Real.jacobiZetaFunctionk x₂ k -
        k ^ 2 * Real.jacobiSnm x₁ (k ^ 2) * Real.jacobiSnm x₂ (k ^ 2) *
          Real.jacobiSnm (x₁ + x₂) (k ^ 2) := by
  simp only [Real.jacobiZetaFunctionk, Real.jacobiEpsilonk_add hm]
  ring

/-- DLMF 22.16.33: `Z(x + K|k) = Z(x|k) - k² sn(x,k) cd(x,k)` (from 22.16.28). -/
@[dlmf 22.16.E33 "special case: real modulus with k² < 1"]
theorem Real.jacobiZetaFunctionk_add_compEllIntKm (hm : k ^ 2 < 1) (x : ℝ) :
    Real.jacobiZetaFunctionk (x + Real.compEllIntKm (k ^ 2)) k = Real.jacobiZetaFunctionk x k -
      k ^ 2 * Real.jacobiSnm x (k ^ 2) * (Real.jacobiCnm x (k ^ 2) / Real.jacobiDnm x (k ^ 2)) := by
  have hK := (Real.compEllIntKm_pos hm).ne'
  simp only [Real.jacobiZetaFunctionk, Real.jacobiEpsilonk_add_compEllIntKm hm]
  field_simp
  ring

/-- DLMF 22.16.34: `Z(x + 2K|k) = Z(x|k)`. -/
@[dlmf 22.16.E34 "special case: real modulus with k² < 1"]
theorem Real.jacobiZetaFunctionk_add_two_compEllIntKm (hm : k ^ 2 < 1) (x : ℝ) :
    Real.jacobiZetaFunctionk (x + 2 * Real.compEllIntKm (k ^ 2)) k =
      Real.jacobiZetaFunctionk x k := by
  have hK := (Real.compEllIntKm_pos hm).ne'
  simp only [Real.jacobiZetaFunctionk, Real.jacobiEpsilonk_add_two_compEllIntKm hm]
  field_simp
  ring

end Zeta

end DLMF.JacobiElliptic
