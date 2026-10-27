/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.OrthogonalPolynomials.BoundsZeros
public import DLMFMathlib.Analysis.ODE.SturmComparison

/-!
# Bounds for individual Jacobi zero angles

Beals–Wong Theorem 5.5.1: if `α², β² ≤ 1/4` and `cos θ_k` are the zeros in
increasing angular order, then `(k-1+γ)π/(n+γ) ≤ θ_k ≤ kπ/(n+γ)`,
where `γ = (α+β+1)/2`. The angular Liouville transformation is proved specifically
for the Jacobi polynomial, and the existing Sturm comparison theorem controls the gaps.
A uniform improvement of the comparison coefficient gives strict inequalities unless
both squared parameters equal `1/4`.
-/

@[expose] public noncomputable section

open Real Set Polynomial

namespace DLMF.OrthogonalPolynomials

namespace JacobiZeroBounds

/-- The half-sum of the Jacobi parameters, shifted by one. -/
def gamma (α β : ℝ) : ℝ := (α + β + 1) / 2

/-- The half-difference of the Jacobi parameters. -/
def delta (α β : ℝ) : ℝ := (α - β) / 2

/-- A positive Jacobi Liouville multiplier on the open angular interval. -/
def weight (α β t : ℝ) : ℝ :=
  exp ((α / 2 + 1 / 4) * log (1 - cos t) + (β / 2 + 1 / 4) * log (1 + cos t))

/-- The logarithmic derivative of the Jacobi multiplier. -/
def logDeriv (α β t : ℝ) : ℝ := (delta α β + gamma α β * cos t) / sin t

/-- The angular Jacobi function. -/
def u (α β : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  weight α β t * (jacobiPolyPR α β n).eval (cos t)

/-- Its derivative, in a form suited to Sturm comparison. -/
def u' (α β : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  weight α β t * (logDeriv α β t * (jacobiPolyPR α β n).eval (cos t) -
    sin t * (jacobiPolyPR α β n).derivative.eval (cos t))

/-- The coefficient of the angular Jacobi equation `u'' + q u = 0`. -/
def q (α β : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  (n + gamma α β) ^ 2 +
    ((1 / 4 - α ^ 2) * (1 + cos t) + (1 / 4 - β ^ 2) * (1 - cos t)) /
      (2 * sin t ^ 2)

/-- Both logarithms in the multiplier have positive arguments. -/
theorem one_sub_cos_pos_and_one_add_cos_pos {t : ℝ} (ht : t ∈ Ioo 0 π) :
    0 < 1 - cos t ∧ 0 < 1 + cos t := by
  have h1 := cos_lt_cos_of_nonneg_of_le_pi (x := 0) (y := t) (by norm_num) ht.2.le ht.1
  have h2 := cos_lt_cos_of_nonneg_of_le_pi (x := t) (y := π) ht.1.le le_rfl ht.2
  simp only [cos_zero, cos_pi] at h1 h2
  constructor <;> linarith

/-- Derivative of the multiplier on the open angular interval. -/
theorem hasDerivAt_weight (α β : ℝ) {t : ℝ} (ht : t ∈ Ioo 0 π) :
    HasDerivAt (weight α β) (weight α β t * logDeriv α β t) t := by
  obtain ⟨hminus, hplus⟩ := one_sub_cos_pos_and_one_add_cos_pos ht
  have hs := sin_pos_of_pos_of_lt_pi ht.1 ht.2
  have h := (((((hasDerivAt_cos t).const_sub 1).log hminus.ne').const_mul (α / 2 + 1 / 4)).add
    ((((hasDerivAt_cos t).const_add 1).log hplus.ne').const_mul (β / 2 + 1 / 4))).exp
  refine h.congr_deriv ?_
  change weight α β t * _ = weight α β t * _
  congr 1
  dsimp [logDeriv, gamma, delta]
  have hs2 : sin t ^ 2 = 1 - cos t ^ 2 := by nlinarith [sin_sq_add_cos_sq t]
  field_simp [hs.ne', hminus.ne', hplus.ne']
  ring_nf
  rw [hs2]
  ring

/-- Derivative of the logarithmic derivative. -/
theorem hasDerivAt_logDeriv (α β : ℝ) {t : ℝ} (ht : t ∈ Ioo 0 π) :
    HasDerivAt (logDeriv α β)
      (-(gamma α β + delta α β * cos t) / sin t ^ 2) t := by
  have hs := sin_pos_of_pos_of_lt_pi ht.1 ht.2
  have h := (((hasDerivAt_cos t).const_mul (gamma α β)).const_add (delta α β)).div
    (hasDerivAt_sin t) hs.ne'
  refine h.congr_deriv ?_
  have hs2 : sin t ^ 2 = 1 - cos t ^ 2 := by nlinarith [sin_sq_add_cos_sq t]
  field_simp [hs.ne']
  ring_nf
  rw [hs2]
  ring

/-- The angular function has the stated first derivative. -/
theorem hasDerivAt_u (α β : ℝ) (n : ℕ) {t : ℝ} (ht : t ∈ Ioo 0 π) :
    HasDerivAt (u α β n) (u' α β n t) t := by
  refine ((hasDerivAt_weight α β ht).mul
    ((Polynomial.hasDerivAt (jacobiPolyPR α β n) (cos t)).comp t
      (hasDerivAt_cos t))).congr_deriv ?_
  dsimp [u']
  ring

/-- The angular Jacobi differential equation. -/
theorem hasDerivAt_u' {α : ℝ} (hα : -1 < α) (β : ℝ) (n : ℕ)
    {t : ℝ} (ht : t ∈ Ioo 0 π) :
    HasDerivAt (u' α β n) (-(q α β n t * u α β n t)) t := by
  have hs := sin_pos_of_pos_of_lt_pi ht.1 ht.2
  have hc := sin_sq_add_cos_sq t
  have h := (hasDerivAt_weight α β ht).mul
    (((hasDerivAt_logDeriv α β ht).mul
      ((Polynomial.hasDerivAt (jacobiPolyPR α β n) (cos t)).comp t (hasDerivAt_cos t))).sub
      ((hasDerivAt_sin t).mul
        ((Polynomial.hasDerivAt (jacobiPolyPR α β n).derivative (cos t)).comp t
          (hasDerivAt_cos t))))
  have hlog : logDeriv α β t ^ 2 -
      (gamma α β + delta α β * cos t) / sin t ^ 2 + q α β n t =
        n * (n + α + β + 1) := by
    dsimp [logDeriv, q, gamma, delta]
    have hs2 : sin t ^ 2 = 1 - cos t ^ 2 := by nlinarith [hc]
    field_simp [hs.ne']
    ring_nf
    rw [hs2]
    ring
  have hcoeff : 2 * logDeriv α β t * sin t + cos t =
      α - β + (α + β + 2) * cos t := by
    dsimp [logDeriv, gamma, delta]
    field_simp [hs.ne']
    ring
  refine h.congr_deriv ?_
  dsimp only [u, u', Pi.mul_apply, Pi.sub_apply, Function.comp_apply]
  have hode := jacobiPolyPR_ode hα β n (cos t)
  linear_combination (weight α β t) * hode +
    (weight α β t * (jacobiPolyPR α β n).eval (cos t)) * hlog -
    (weight α β t * (jacobiPolyPR α β n).derivative.eval (cos t)) * hcoeff +
    (weight α β t * (jacobiPolyPR α β n).derivative.derivative.eval (cos t)) * hc

/-- The Jacobi angular coefficient dominates the constant-frequency comparison equation. -/
theorem freq_sq_le_q {α β : ℝ} (hα : α ^ 2 ≤ 1 / 4) (hβ : β ^ 2 ≤ 1 / 4)
    (n : ℕ) {t : ℝ} (ht : t ∈ Ioo 0 π) :
    (n + gamma α β) ^ 2 ≤ q α β n t := by
  obtain ⟨hminus, hplus⟩ := one_sub_cos_pos_and_one_add_cos_pos ht
  dsimp [q]
  exact le_add_of_nonneg_right (div_nonneg
    (add_nonneg (mul_nonneg (by linarith) hplus.le) (mul_nonneg (by linarith) hminus.le))
    (by positivity))

/-- A zero-free angular interval cannot exceed the comparison half-period. -/
private lemma length_le_of_no_zero_with_freq {α β : ℝ} (hα : -1 < α) (n : ℕ)
    {ω : ℝ} (hω : 0 < ω) (hq : ∀ t ∈ Ioo 0 π, ω ^ 2 ≤ q α β n t) {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ π)
    (hno : ∀ t ∈ Ioo a b, u α β n t ≠ 0) :
    b - a ≤ π / ω := by
  have hL : 0 < π / ω := div_pos pi_pos hω
  by_contra hlong
  push Not at hlong
  let c := (a + b - π / ω) / 2
  have hac : a < c := by dsimp [c]; linarith
  have hcb : c + π / ω < b := by dsimp [c]; linarith
  have hc0 : 0 < c := lt_of_le_of_lt ha hac
  have hcπ : c + π / ω < π := lt_of_lt_of_le hcb hb
  have harg : ω * (c + π / ω - c) = π := by
    calc
      _ = ω * (π / ω) := by ring
      _ = π := by rw [mul_comm, div_mul_cancel₀ _ (show ω ≠ 0 from hω.ne')]
  have ht (t : ℝ) (ht : t ∈ Icc c (c + π / ω)) : t ∈ Ioo 0 π :=
    ⟨lt_of_lt_of_le hc0 ht.1, lt_of_le_of_lt ht.2 hcπ⟩
  have hsine (t : ℝ) : HasDerivAt (fun t => sin (ω * (t - c)))
      (ω * cos (ω * (t - c))) t := by
    have hd : HasDerivAt (fun t : ℝ => ω * (t - c)) ω t := by
      simpa using ((hasDerivAt_id t).sub_const c).const_mul ω
    exact hd.sin.congr_deriv (by ring)
  have hcosine (t : ℝ) : HasDerivAt (fun t => ω * cos (ω * (t - c)))
      (-(ω ^ 2 * sin (ω * (t - c)))) t := by
    have hd : HasDerivAt (fun t : ℝ => ω * (t - c)) ω t := by
      simpa using ((hasDerivAt_id t).sub_const c).const_mul ω
    exact (hd.cos.const_mul ω).congr_deriv (by ring)
  have hsin_ne (t : ℝ) (ht : t ∈ Ioo c (c + π / ω)) : sin (ω * (t - c)) ≠ 0 := by
    apply (sin_pos_of_pos_of_lt_pi (mul_pos hω (by linarith [ht.1])) ?_).ne'
    have := mul_lt_mul_of_pos_left ht.2 hω
    nlinarith
  rcases ODE.sturm_comparison (p := fun _ => 1) (q₁ := fun _ => ω ^ 2)
    (q₂ := q α β n) (u := fun t => sin (ω * (t - c)))
    (u' := fun t => ω * cos (ω * (t - c))) (v := u α β n) (v' := u' α β n)
    (by linarith)
    (fun t _ => hsine t) (fun t _ => by simpa only [one_mul] using hcosine t)
    (fun t ht' => hasDerivAt_u α β n (ht t ht'))
    (fun t ht' => by simpa only [one_mul] using hasDerivAt_u' hα β n (ht t ht'))
    zero_le_one zero_le_one (fun t ht' => hq t (ht t ⟨ht'.1.le, ht'.2.le⟩))
    (by simp) (by rw [harg, sin_pi]) hsin_ne with hzero | hW
  · obtain ⟨t, ht', hz⟩ := hzero
    exact hno t ⟨by linarith [ht'.1], by linarith [ht'.2]⟩ hz
  · have hw0 := hW c ⟨le_rfl, by linarith⟩
    simp only [ODE.sturmWronskian, sub_self, mul_zero, cos_zero, sin_zero,
      mul_one, one_mul, zero_mul, sub_zero] at hw0
    exact hno c ⟨hac, by linarith⟩ ((mul_eq_zero.mp hw0).resolve_left hω.ne')

/-- The original comparison frequency for the Jacobi equation. -/
private lemma length_le_of_no_zero {α β : ℝ} (hα : -1 < α)
    (hαsq : α ^ 2 ≤ 1 / 4) (hβsq : β ^ 2 ≤ 1 / 4) (n : ℕ)
    (hω : 0 < (n : ℝ) + gamma α β) {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ π)
    (hno : ∀ t ∈ Ioo a b, u α β n t ≠ 0) :
    b - a ≤ π / (n + gamma α β) :=
  length_le_of_no_zero_with_freq hα n hω
    (fun _ ht => freq_sq_le_q hαsq hβsq n ht) ha hb hno

/-- A uniform improvement of the comparison coefficient, unless both squared parameters
are `1/4`. This avoids endpoint regularity assumptions for strict zero bounds. -/
theorem improved_freq_sq_le_q {α β : ℝ} (hα : α ^ 2 ≤ 1 / 4) (hβ : β ^ 2 ≤ 1 / 4)
    (n : ℕ) {t : ℝ} (ht : t ∈ Ioo 0 π) :
    (n + gamma α β) ^ 2 + ((1 / 4 - α ^ 2) + (1 / 4 - β ^ 2)) / 4 ≤ q α β n t := by
  have hs := sin_pos_of_pos_of_lt_pi ht.1 ht.2
  have hA : 0 ≤ 1 / 4 - α ^ 2 := by linarith
  have hB : 0 ≤ 1 / 4 - β ^ 2 := by linarith
  have hden : 0 < 2 * sin t ^ 2 := by positivity
  dsimp [q]
  apply add_le_add_right
  apply (le_div_iff₀ hden).2
  have hc := sin_sq_add_cos_sq t
  nlinarith [mul_nonneg hA (sq_nonneg (1 + cos t)),
    mul_nonneg hB (sq_nonneg (1 - cos t))]

/-- From bounds for all zero-free gaps to bounds for the indexed angles. -/
private lemma indexed_bounds {f : ℝ → ℝ} {n : ℕ} (θ : Fin n → ℝ) (hθ : StrictMono θ)
    (hθrange : ∀ i, θ i ∈ Ioo 0 π)
    (hcomplete : ∀ t ∈ Ioo 0 π, f t = 0 ↔ ∃ i, t = θ i) (L : ℝ)
    (hlen : ∀ a b : ℝ, 0 ≤ a → b ≤ π → (∀ t ∈ Ioo a b, f t ≠ 0) → b - a ≤ L) :
    ∀ i : Fin n, π - ((n : ℝ) - i) * L ≤ θ i ∧ θ i ≤ ((i : ℝ) + 1) * L := by
  cases n with
  | zero => exact fun i => Fin.elim0 i
  | succ m =>
    have hfirst : θ 0 ≤ L := by
      have h := hlen 0 (θ 0) le_rfl (hθrange 0).2.le ?_
      · simpa using h
      intro t ht hz
      obtain ⟨j, hj⟩ := (hcomplete t ⟨ht.1, ht.2.trans (hθrange 0).2⟩).mp hz
      have := hθ.monotone (Fin.zero_le j)
      linarith [ht.2]
    have hlast : π - θ (Fin.last m) ≤ L := by
      apply hlen _ _ (hθrange _).1.le le_rfl
      intro t ht hz
      obtain ⟨j, hj⟩ := (hcomplete t ⟨(hθrange _).1.trans ht.1, ht.2⟩).mp hz
      have := hθ.monotone (Fin.le_last j)
      linarith [ht.1]
    have hstep (i : Fin m) : θ i.succ - θ i.castSucc ≤ L := by
      apply hlen _ _ (hθrange _).1.le (hθrange _).2.le
      intro t ht hz
      obtain ⟨j, hj⟩ := (hcomplete t ⟨(hθrange _).1.trans ht.1,
        ht.2.trans (hθrange _).2⟩).mp hz
      by_cases hjle : j ≤ i.castSucc
      · have := hθ.monotone hjle
        linarith [ht.1]
      · have hij : i.succ ≤ j := by
          change i.val + 1 ≤ j.val
          change ¬j.val ≤ i.val at hjle
          omega
        have := hθ.monotone hij
        linarith [ht.2]
    have hupper : ∀ i : Fin (m + 1), θ i ≤ ((i : ℝ) + 1) * L := by
      intro i
      induction i using Fin.induction with
      | zero => simpa using hfirst
      | succ i ih =>
        have h := hstep i
        simp only [Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one] at ih ⊢
        linarith
    have hlower : ∀ i : Fin (m + 1), π - (((m + 1 : ℕ) : ℝ) - (i : ℝ)) * L ≤ θ i := by
      intro i
      induction i using Fin.reverseInduction with
      | last => simp only [Fin.val_last, Nat.cast_add, Nat.cast_one]; linarith
      | cast i ih =>
        have h := hstep i
        simp only [Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one] at ih ⊢
        linarith
    exact fun i => ⟨hlower i, hupper i⟩

end JacobiZeroBounds

/-- Indexed Jacobi zero-angle bounds, Beals–Wong Theorem 5.5.1, with zero-based indices.
The conclusion also identifies all complex zeros and includes degree zero vacuously. -/
theorem jacobi_zero_angle_bounds {α β : ℝ} (hαsq : α ^ 2 ≤ 1 / 4) (hβsq : β ^ 2 ≤ 1 / 4)
    (n : ℕ) :
    ∃ θ : Fin n → ℝ, StrictMono θ ∧ (∀ i, θ i ∈ Ioo 0 π) ∧
      (∀ z : ℂ, jacobiPolyP α β n z = 0 ↔ ∃ i, z = (cos (θ i) : ℂ)) ∧
      ∀ i : Fin n, ((i : ℝ) + (α + β + 1) / 2) * π / (n + (α + β + 1) / 2) ≤ θ i ∧
        θ i ≤ ((i : ℝ) + 1) * π / (n + (α + β + 1) / 2) := by
  have hαlo : -(1 / 2 : ℝ) ≤ α := by nlinarith [sq_nonneg (α + 1 / 2)]
  have hβlo : -(1 / 2 : ℝ) ≤ β := by nlinarith [sq_nonneg (β + 1 / 2)]
  have hα : -1 < α := by linarith
  have hβ : -1 < β := by linarith
  obtain ⟨r, hr, hrange, hroots⟩ := jacobiPolyP_zeros_Ioo hα hβ n
  let θ : Fin n → ℝ := fun i => arccos (r i.rev)
  have hθ : StrictMono θ := by
    intro i j hij
    exact arccos_lt_arccos (hrange j.rev).1.le (hr (Fin.rev_lt_rev.mpr hij)) (hrange i.rev).2.le
  have hθrange (i : Fin n) : θ i ∈ Ioo 0 π :=
    ⟨arccos_pos.mpr (hrange i.rev).2, arccos_lt_pi.mpr (hrange i.rev).1⟩
  have hcos (i : Fin n) : cos (θ i) = r i.rev :=
    cos_arccos (hrange i.rev).1.le (hrange i.rev).2.le
  have hroots' (z : ℂ) : jacobiPolyP α β n z = 0 ↔ ∃ i, z = (cos (θ i) : ℂ) := by
    constructor
    · intro hz
      obtain ⟨i, hi⟩ := (hroots z).mp hz
      refine ⟨i.rev, ?_⟩
      rwa [hcos, Fin.rev_rev]
    · rintro ⟨i, hi⟩
      exact (hroots z).mpr ⟨i.rev, by rwa [hcos] at hi⟩
  refine ⟨θ, hθ, hθrange, hroots', ?_⟩
  by_cases hn : n = 0
  · subst n
    exact fun i => Fin.elim0 i
  have hω : 0 < (n : ℝ) + JacobiZeroBounds.gamma α β := by
    have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    dsimp [JacobiZeroBounds.gamma]
    linarith
  have hcomplete (t : ℝ) (ht : t ∈ Ioo 0 π) :
      JacobiZeroBounds.u α β n t = 0 ↔ ∃ i, t = θ i := by
    have he : JacobiZeroBounds.u α β n t = 0 ↔ jacobiPolyP α β n (cos t) = 0 := by
      rw [JacobiZeroBounds.u, JacobiZeroBounds.weight, mul_eq_zero, or_iff_right (exp_ne_zero _),
        ← eval_jacobiPolyPR hα, Complex.ofReal_eq_zero]
    rw [he, hroots']
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨i, strictAntiOn_cos.injOn ⟨ht.1.le, ht.2.le⟩
        ⟨(hθrange i).1.le, (hθrange i).2.le⟩ (Complex.ofReal_inj.mp hi)⟩
    · rintro ⟨i, rfl⟩
      exact ⟨i, rfl⟩
  have hb := JacobiZeroBounds.indexed_bounds θ hθ hθrange hcomplete
    (π / (n + JacobiZeroBounds.gamma α β)) (fun a b ha hb hno =>
      JacobiZeroBounds.length_le_of_no_zero hα hαsq hβsq n hω ha hb hno)
  intro i
  obtain ⟨hlo, hhi⟩ := hb i
  have heq : π - ((n : ℝ) - i) * (π / (n + JacobiZeroBounds.gamma α β)) =
      ((i : ℝ) + (α + β + 1) / 2) * π / (n + (α + β + 1) / 2) := by
    apply (eq_div_iff (show (n : ℝ) + (α + β + 1) / 2 ≠ 0 from hω.ne')).2
    change (π - ((n : ℝ) - i) * (π / (n + JacobiZeroBounds.gamma α β))) *
      (n + JacobiZeroBounds.gamma α β) = _
    rw [sub_mul, mul_assoc, div_mul_cancel₀ _ hω.ne']
    dsimp [JacobiZeroBounds.gamma]
    ring
  rw [heq] at hlo
  exact ⟨hlo, by simpa only [JacobiZeroBounds.gamma, mul_div_assoc] using hhi⟩

/-- Strict indexed Jacobi angle bounds when at least one squared parameter is below
`1/4`. This completes the strict part of Beals–Wong Theorem 5.5.1. -/
theorem jacobi_zero_angle_bounds_strict {α β : ℝ}
    (hαsq : α ^ 2 ≤ 1 / 4) (hβsq : β ^ 2 ≤ 1 / 4)
    (hstrict : α ^ 2 < 1 / 4 ∨ β ^ 2 < 1 / 4) (n : ℕ) :
    ∃ θ : Fin n → ℝ, StrictMono θ ∧ (∀ i, θ i ∈ Ioo 0 π) ∧
      (∀ z : ℂ, jacobiPolyP α β n z = 0 ↔ ∃ i, z = (cos (θ i) : ℂ)) ∧
      ∀ i : Fin n, ((i : ℝ) + (α + β + 1) / 2) * π / (n + (α + β + 1) / 2) < θ i ∧
        θ i < ((i : ℝ) + 1) * π / (n + (α + β + 1) / 2) := by
  obtain ⟨θ, hθ, hrange, hroots, _⟩ := jacobi_zero_angle_bounds hαsq hβsq n
  refine ⟨θ, hθ, hrange, hroots, ?_⟩
  by_cases hn : n = 0
  · subst n
    exact fun i => Fin.elim0 i
  have hαlo : -(1 / 2 : ℝ) ≤ α := by nlinarith [sq_nonneg (α + 1 / 2)]
  have hβlo : -(1 / 2 : ℝ) ≤ β := by nlinarith [sq_nonneg (β + 1 / 2)]
  have hα : -1 < α := by linarith
  let ω : ℝ := n + JacobiZeroBounds.gamma α β
  let ε : ℝ := ((1 / 4 - α ^ 2) + (1 / 4 - β ^ 2)) / 4
  let κ : ℝ := sqrt (ω ^ 2 + ε)
  have hω : 0 < ω := by
    have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    dsimp [ω, JacobiZeroBounds.gamma]
    linarith
  have hε : 0 < ε := by rcases hstrict with h | h <;> dsimp [ε] <;> linarith
  have hκsq : κ ^ 2 = ω ^ 2 + ε := sq_sqrt (by positivity)
  have hκ : 0 < κ := sqrt_pos.mpr (by positivity)
  have hωκ : ω < κ := by nlinarith
  have hcomplete (t : ℝ) (ht : t ∈ Ioo 0 π) :
      JacobiZeroBounds.u α β n t = 0 ↔ ∃ i, t = θ i := by
    have he : JacobiZeroBounds.u α β n t = 0 ↔ jacobiPolyP α β n (cos t) = 0 := by
      rw [JacobiZeroBounds.u, JacobiZeroBounds.weight, mul_eq_zero,
        or_iff_right (exp_ne_zero _), ← eval_jacobiPolyPR hα, Complex.ofReal_eq_zero]
    rw [he, hroots]
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨i, strictAntiOn_cos.injOn ⟨ht.1.le, ht.2.le⟩
        ⟨(hrange i).1.le, (hrange i).2.le⟩ (Complex.ofReal_inj.mp hi)⟩
    · rintro ⟨i, rfl⟩
      exact ⟨i, rfl⟩
  have hb := JacobiZeroBounds.indexed_bounds θ hθ hrange hcomplete (π / κ)
    (fun a b ha hb hno => JacobiZeroBounds.length_le_of_no_zero_with_freq hα n hκ
      (fun t ht => by rw [hκsq]; exact JacobiZeroBounds.improved_freq_sq_le_q hαsq hβsq n ht)
      ha hb hno)
  have hL : π / κ < π / ω := div_lt_div_of_pos_left pi_pos hω hωκ
  intro i
  obtain ⟨hlo, hhi⟩ := hb i
  have hi : (i : ℝ) < n := by exact_mod_cast i.isLt
  have hlow : π - ((n : ℝ) - i) * (π / ω) < θ i := by
    have := mul_lt_mul_of_pos_left hL (by linarith : 0 < (n : ℝ) - i)
    linarith
  have hupp : θ i < ((i : ℝ) + 1) * (π / ω) :=
    hhi.trans_lt (mul_lt_mul_of_pos_left hL (by positivity))
  have heq : π - ((n : ℝ) - i) * (π / ω) =
      ((i : ℝ) + (α + β + 1) / 2) * π / (n + (α + β + 1) / 2) := by
    apply (eq_div_iff (show (n : ℝ) + (α + β + 1) / 2 ≠ 0 from hω.ne')).2
    change (π - ((n : ℝ) - i) * (π / ω)) * ω = _
    rw [sub_mul, mul_assoc, div_mul_cancel₀ _ hω.ne']
    dsimp [ω, JacobiZeroBounds.gamma]
    ring
  exact ⟨by rwa [heq] at hlow, by simpa only [ω, JacobiZeroBounds.gamma, mul_div_assoc] using hupp⟩

end DLMF.OrthogonalPolynomials
