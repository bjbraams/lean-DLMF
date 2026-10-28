/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Airy.Asymptotics.RotatedBi

/-!
# Real Airy remainders and Stieltjes bounds

Binomial remainders and Stieltjes representations give signed and absolute error bounds for real
Airy expansions.

Source references and common attribution are retained in
`DLMF.Airy.Asymptotics`.
-/

@[expose] public noncomputable section

open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF.Confluent

open scoped Real Topology Interval

namespace DLMF.Airy

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

end DLMF.Airy
end
