/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.ParabolicCylinder.AsymptoticsZeros

/-!
# The crossing point of the parabolic-cylinder envelopes

For `c ≥ 0` the envelopes of DLMF 14.15.23 switch branches at the largest positive root `X_c` of
`U(-c, x) = Ū(-c, x)`, where `Ū(a, x) = Γ(1/2 - a) V(a, x)` (DLMF 12.2.21). This file shows that
the supremum of the positive roots is a root, that it is positive for `c > 0`, and that no root
exceeds it; for `c = 0` there is no positive root and the supremum is `0`, a root as well.

The argument uses only the Wronskian `𝒲{U, Ū} = Γ(1/2 + c) √(2/π) > 0` and the decay of `U`:
on an interval free of zeros of `U` the quotient `Ū/U` is strictly increasing and tends to `+∞`,
so `U - Ū` eventually has the sign of `-U`. A positive root is produced either after the last
nonnegative zero of `U`, or from the values at the origin
`U(-c, 0) = 2^{s-1/2} Γ(s) sin(πs)/√π` and `Ū(-c, 0) = 2^{s-1/2} Γ(s) cos(πs)/√π`,
`s = 1/4 + c/2` (DLMF 12.2.6, 12.2.8), together with the count of positive zeros of `U`
(DLMF §12.11(i)).

## Main results

* `DLMF.Legendre.CylinderCrossing.sSup_spec`: the properties of the crossing point of
  DLMF 14.15.23.
-/

@[expose] public noncomputable section

open Complex Filter Set
open scoped Real Topology

namespace DLMF.Legendre.CylinderCrossing

/-- Eventual sign of `u - G v` for a Wronskian pair with `u → 0`. -/
private theorem eventually_mul_sub_neg {u v u' v' : ℝ → ℝ} {w G p : ℝ} (hw : 0 < w) (hG : 0 < G)
    (hu : ∀ x, HasDerivAt u (u' x) x) (hv : ∀ x, HasDerivAt v (v' x) x)
    (hW : ∀ x, u x * v' x - u' x * v x = w) (hne : ∀ x, p < x → u x ≠ 0)
    (hlim : Tendsto u atTop (𝓝 0)) :
    ∀ᶠ x in atTop, u x * (u x - G * v x) < 0 := by
  -- eventually `u² ≤ w`
  have hsq : ∀ᶠ x in atTop, u x ^ 2 < w := by
    have : Tendsto (fun x => u x ^ 2) atTop (𝓝 0) := by simpa using hlim.pow 2
    exact this.eventually (gt_mem_nhds hw)
  obtain ⟨X₁, hX₁⟩ := (hsq.and (eventually_gt_atTop p)).exists_forall_of_atTop
  set g : ℝ → ℝ := fun x => v x / u x - x
  have hg : ∀ x, X₁ ≤ x → HasDerivAt g (w / u x ^ 2 - 1) x := by
    intro x hx
    have hux := hne x (hX₁ x hx).2
    have := ((hv x).div (hu x) hux).sub (hasDerivAt_id' x)
    refine this.congr_deriv ?_
    rw [← hW x]; field_simp
  have hmono : MonotoneOn g (Ici X₁) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici X₁) ?_ ?_ ?_
    · exact fun x hx => (hg x hx).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      exact (hg x hx.le).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      rw [(hg x hx.le).deriv]
      have h1 := (hX₁ x hx.le).1
      have h2 : 0 < u x ^ 2 := by
        have := hne x (hX₁ x hx.le).2; positivity
      rw [sub_nonneg, le_div_iff₀ h2]; linarith
  filter_upwards [eventually_ge_atTop X₁, eventually_gt_atTop (1 / G - g X₁)] with x hx hx'
  have hux := hne x (hX₁ x hx).2
  have hgx := hmono self_mem_Ici hx hx
  simp only [g] at hgx
  have hvu : 1 / G < v x / u x := by linarith
  have h2 : 0 < u x ^ 2 := by positivity
  have : 1 < G * (v x / u x) := by
    rw [div_lt_iff₀ hG] at hvu; linarith
  have e : u x * (u x - G * v x) = u x ^ 2 * (1 - G * (v x / u x)) := by
    field_simp
  rw [e]
  exact mul_neg_of_pos_of_neg h2 (by linarith)

/-- A continuous function with a sign change on `[a, b]` vanishes inside. -/
private theorem exists_Ioo_eq_zero {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b)) (h : f a * f b < 0) : ∃ r ∈ Ioo a b, f r = 0 := by
  rcases lt_or_gt_of_ne (show f a ≠ 0 by rintro h0; simp [h0] at h) with ha | ha
  · have hb : 0 < f b := by nlinarith
    obtain ⟨r, hr, hr0⟩ := intermediate_value_Ioo hab hf ⟨ha, hb⟩
    exact ⟨r, hr, hr0⟩
  · have hb : f b < 0 := by nlinarith
    obtain ⟨r, hr, hr0⟩ := intermediate_value_Ioo' hab hf ⟨hb, ha⟩
    exact ⟨r, hr, hr0⟩

variable {u v u' v' : ℝ → ℝ} {w G : ℝ}

/-- `u` keeps its sign on `[x₀, X]` if it has no zero on `(x₀, X]` and `u x₀ ≠ 0`. -/
private theorem mul_pos_of_ne_zero (hu : ∀ x, HasDerivAt u (u' x) x) {x₀ X : ℝ} (hX : x₀ < X)
    (hne : ∀ x, x₀ < x → u x ≠ 0) (h0 : u x₀ ≠ 0) : 0 < u x₀ * u X := by
  by_contra hc
  have hlt : u x₀ * u X < 0 := lt_of_le_of_ne (not_lt.mp hc) (mul_ne_zero h0 (hne X hX))
  obtain ⟨r, hr, hr0⟩ := exists_Ioo_eq_zero hX.le
    (fun x _ => (hu x).continuousAt.continuousWithinAt) hlt
  exact hne r hr.1 hr0

/-- Beyond a zero `x₁` of `u`, the function `u` has the sign of `u'(x₁)`. -/
private theorem mul_deriv_pos (hu : ∀ x, HasDerivAt u (u' x) x) {x₁ X : ℝ} (hX : x₁ < X)
    (h1 : u x₁ = 0) (hd : u' x₁ ≠ 0) (hne : ∀ x, x₁ < x → u x ≠ 0) : 0 < u X * u' x₁ := by
  by_contra hc
  have hlt : u X * u' x₁ < 0 := lt_of_le_of_ne (not_lt.mp hc) (mul_ne_zero (hne X hX) hd)
  have hsl := ((hasDerivAt_iff_tendsto_slope.mp (hu x₁)).mono_left (nhdsGT_le_nhdsNE x₁))
  have hev : ∀ᶠ y in 𝓝[>] x₁, 0 < slope u x₁ y * u' x₁ := by
    have : Tendsto (fun y => slope u x₁ y * u' x₁) (𝓝[>] x₁) (𝓝 (u' x₁ * u' x₁)) :=
      hsl.mul_const _
    exact this.eventually (lt_mem_nhds (mul_self_pos.mpr hd))
  obtain ⟨y, hy, hyX⟩ := (hev.and (Ioo_mem_nhdsGT hX)).exists
  have hyx : 0 < y - x₁ := sub_pos.mpr hyX.1
  rw [slope_def_field, h1, sub_zero] at hy
  have hy' : 0 < u y * u' x₁ := by
    have := mul_pos hy hyx
    rwa [div_mul_eq_mul_div, div_mul_cancel₀ _ hyx.ne'] at this
  have hneg : u y * u X < 0 := by
    have : 0 < (u y * u' x₁) * (-(u X * u' x₁)) := mul_pos hy' (neg_pos.mpr hlt)
    nlinarith [mul_self_pos.mpr hd]
  obtain ⟨r, hr, hr0⟩ := exists_Ioo_eq_zero hyX.2.le
    (fun x _ => (hu x).continuousAt.continuousWithinAt) hneg
  exact hne r (hyX.1.trans hr.1) hr0

/-- A root of `u = G v` after a zero of `u`. -/
private theorem exists_root_of_zero (hw : 0 < w) (hG : 0 < G)
    (hu : ∀ x, HasDerivAt u (u' x) x) (hv : ∀ x, HasDerivAt v (v' x) x)
    (hW : ∀ x, u x * v' x - u' x * v x = w) (hlim : Tendsto u atTop (𝓝 0)) {x₁ : ℝ}
    (h1 : u x₁ = 0) (hne : ∀ x, x₁ < x → u x ≠ 0) : ∃ r, x₁ < r ∧ u r = G * v r := by
  obtain ⟨X, hX, hXx⟩ := ((eventually_mul_sub_neg hw hG hu hv hW hne hlim).and
    (eventually_gt_atTop x₁)).exists
  have hW1 := hW x₁
  rw [h1, zero_mul, zero_sub] at hW1
  have hd : u' x₁ ≠ 0 := by rintro h; rw [h, zero_mul, neg_zero] at hW1; linarith
  have hs := mul_deriv_pos hu hXx h1 hd hne
  have hD1 : 0 < (u x₁ - G * v x₁) * u' x₁ := by
    rw [h1]; nlinarith
  have hprod : (u x₁ - G * v x₁) * (u X - G * v X) < 0 := by
    by_contra hc
    have h' := mul_nonneg (not_lt.mp hc) hs.le
    have : (u x₁ - G * v x₁) * u' x₁ * (u X * (u X - G * v X)) < 0 := mul_neg_of_pos_of_neg hD1 hX
    nlinarith
  obtain ⟨r, hr, hr0⟩ := exists_Ioo_eq_zero (f := fun x => u x - G * v x) hXx.le
    (fun x _ => ((hu x).continuousAt.sub ((hv x).continuousAt.const_mul G)).continuousWithinAt)
    hprod
  exact ⟨r, hr.1, sub_eq_zero.mp hr0⟩

/-- A root of `u = G v` after a point where `u` and `u - G v` have the same sign. -/
private theorem exists_root_of_mul_pos (hw : 0 < w) (hG : 0 < G)
    (hu : ∀ x, HasDerivAt u (u' x) x) (hv : ∀ x, HasDerivAt v (v' x) x)
    (hW : ∀ x, u x * v' x - u' x * v x = w) (hlim : Tendsto u atTop (𝓝 0)) {x₀ : ℝ}
    (hne : ∀ x, x₀ ≤ x → u x ≠ 0) (h0 : 0 < u x₀ * (u x₀ - G * v x₀)) :
    ∃ r, x₀ < r ∧ u r = G * v r := by
  obtain ⟨X, hX, hXx⟩ := ((eventually_mul_sub_neg hw hG hu hv hW
    (fun x hx => hne x hx.le) hlim).and (eventually_gt_atTop x₀)).exists
  have hs := mul_pos_of_ne_zero hu hXx (fun x hx => hne x hx.le) (hne x₀ le_rfl)
  have hprod : (u x₀ - G * v x₀) * (u X - G * v X) < 0 := by
    by_contra hc
    have h' := mul_nonneg (not_lt.mp hc) hs.le
    have : u x₀ * (u x₀ - G * v x₀) * (u X * (u X - G * v X)) < 0 := mul_neg_of_pos_of_neg h0 hX
    nlinarith
  obtain ⟨r, hr, hr0⟩ := exists_Ioo_eq_zero (f := fun x => u x - G * v x) hXx.le
    (fun x _ => ((hu x).continuousAt.sub ((hv x).continuousAt.const_mul G)).continuousWithinAt)
    hprod
  exact ⟨r, hr.1, sub_eq_zero.mp hr0⟩

/-- No root of `u = G v` after a root, while `u` does not vanish. -/
private theorem ne_of_root (hw : 0 < w) (hG : 0 < G)
    (hu : ∀ x, HasDerivAt u (u' x) x) (hv : ∀ x, HasDerivAt v (v' x) x)
    (hW : ∀ x, u x * v' x - u' x * v x = w) {x₀ : ℝ}
    (hne : ∀ x, x₀ ≤ x → u x ≠ 0) (h0 : u x₀ = G * v x₀) {x : ℝ} (hx : x₀ < x) :
    u x ≠ G * v x := by
  have hg : ∀ y, x₀ ≤ y → HasDerivAt (fun t => v t / u t) (w / u y ^ 2) y := by
    intro y hy
    refine ((hv y).div (hu y) (hne y hy)).congr_deriv ?_
    rw [← hW y]; ring
  have hmono : StrictMonoOn (fun t => v t / u t) (Ici x₀) := by
    refine strictMonoOn_of_deriv_pos (convex_Ici x₀)
      (fun y hy => (hg y hy).continuousAt.continuousWithinAt) ?_
    intro y hy
    rw [interior_Ici] at hy
    rw [(hg y hy.le).deriv]
    have := hne y hy.le
    positivity
  intro h
  have h1 := hmono self_mem_Ici (mem_Ici.mpr hx.le) hx
  have e0 : v x₀ / u x₀ = 1 / G := by
    rw [div_eq_div_iff (hne x₀ le_rfl) hG.ne', h0]; ring
  have e1 : v x / u x = 1 / G := by
    rw [div_eq_div_iff (hne x hx.le) hG.ne', h]; ring
  simp only [e0, e1] at h1
  exact lt_irrefl _ h1

open DLMF.Confluent

/-- `U(-c, 0) = 2^{s-1/2} Γ(s) sin(πs)/√π` with `s = 1/4 + c/2`. -/
private theorem parabolicCylinderU_neg_zero {c : ℝ} (hc : 0 ≤ c) :
    parabolicCylinderU ((-c : ℝ) : ℂ) 0 = (((2:ℝ) ^ ((1/4 + c/2) - 1/2) * Real.Gamma (1/4 + c/2) *
      Real.sin (π * (1/4 + c/2)) / Real.sqrt π : ℝ) : ℂ) := by
  set s : ℝ := 1/4 + c/2 with hs
  have hs0 : 0 < s := by rw [hs]; linarith
  rw [parabolicCylinderU_zero, show ((-c : ℝ) : ℂ) / 2 + 1/4 = ((1/2 - s : ℝ) : ℂ) by
      push_cast [hs]; ring,
    show 3/4 + ((-c : ℝ) : ℂ) / 2 = ((1 - s : ℝ) : ℂ) by push_cast [hs]; ring,
    Complex.Gamma_ofReal, show (2:ℂ) = ((2:ℝ):ℂ) by norm_num,
    ← Complex.ofReal_cpow (by norm_num)]
  rw [← Complex.ofReal_mul, ← Complex.ofReal_div, Complex.ofReal_inj]
  have hrefl := Real.Gamma_mul_Gamma_one_sub s
  have hG := Real.Gamma_pos_of_pos hs0
  have hp : (0:ℝ) < Real.sqrt π := Real.sqrt_pos.mpr Real.pi_pos
  have h2 : (2:ℝ) ^ (s - 1/2) * (2:ℝ) ^ (1/2 - s) = 1 := by
    rw [← Real.rpow_add (by norm_num)]; simp
  have hpi : Real.sqrt π * Real.sqrt π = π := Real.mul_self_sqrt Real.pi_pos.le
  by_cases h1 : Real.Gamma (1 - s) = 0
  · rw [h1, mul_zero] at hrefl
    have hsin : Real.sin (π * s) = 0 := by
      rcases div_eq_zero_iff.mp hrefl.symm with h | h
      · exact absurd h Real.pi_ne_zero
      · exact h
    rw [h1, hsin]; simp
  · have hsin : Real.sin (π * s) ≠ 0 := by
      intro h; rw [h, div_zero] at hrefl
      exact h1 ((mul_eq_zero.mp hrefl).resolve_left hG.ne')
    have h2' : (2:ℝ) ^ (1/2 - s) ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) _).ne'
    rw [div_eq_div_iff (mul_ne_zero h2' h1) hp.ne']
    have e : Real.Gamma (1 - s) = π / Real.sin (π * s) / Real.Gamma s := by
      rw [← hrefl]; field_simp
    rw [e, hpi]
    calc π = π * ((2:ℝ) ^ (s - 1/2) * (2:ℝ) ^ (1/2 - s)) * (Real.Gamma s / Real.Gamma s) *
          (Real.sin (π * s) / Real.sin (π * s)) := by
            rw [h2, div_self hG.ne', div_self hsin]; ring
      _ = _ := by ring

/-- `Ū(-c, 0) = 2^{s-1/2} Γ(s) cos(πs)/√π` with `s = 1/4 + c/2`. -/
private theorem parabolicCylinderUBar_neg_zero {c : ℝ} (hc : 0 ≤ c) :
    parabolicCylinderUBar ((-c : ℝ) : ℂ) 0 =
        (((2:ℝ) ^ ((1/4 + c/2) - 1/2) * Real.Gamma (1/4 + c/2) *
      Real.cos (π * (1/4 + c/2)) / Real.sqrt π : ℝ) : ℂ) := by
  set s : ℝ := 1/4 + c/2 with hs
  have hs0 : 0 < s := by rw [hs]; linarith
  rw [parabolicCylinderUBar, parabolicCylinderV_zero, show (1/2 : ℂ) - ((-c : ℝ) : ℂ) =
      ((2 * s : ℝ) : ℂ) by
      push_cast [hs]; ring,
    show ((-c : ℝ) : ℂ) / 2 + 1/4 = ((1/2 - s : ℝ) : ℂ) by push_cast [hs]; ring,
    show 3/4 - ((-c : ℝ) : ℂ) / 2 = ((1/2 + s : ℝ) : ℂ) by push_cast [hs]; ring,
    show 1/4 + ((-c : ℝ) : ℂ) / 2 = ((1/2 - s : ℝ) : ℂ) by push_cast [hs]; ring,
    Complex.Gamma_ofReal, Complex.Gamma_ofReal, Complex.Gamma_ofReal,
    show (2:ℂ) = ((2:ℝ):ℂ) by norm_num, ← Complex.ofReal_cpow (by norm_num)]
  norm_cast
  have hrefl := Real.Gamma_mul_Gamma_one_sub (1/2 + s)
  rw [show 1 - (1/2 + s) = 1/2 - s by ring, show π * (1/2 + s) = π * s + π / 2 by ring,
    Real.sin_add_pi_div_two] at hrefl
  have hdup := Real.Gamma_mul_Gamma_add_half s
  have hG := Real.Gamma_pos_of_pos hs0
  have hG2 : 0 < Real.Gamma (1/2 + s) := Real.Gamma_pos_of_pos (by linarith)
  have hp : (0:ℝ) < Real.sqrt π := Real.sqrt_pos.mpr Real.pi_pos
  have hpi : Real.sqrt π * Real.sqrt π = π := Real.mul_self_sqrt Real.pi_pos.le
  set A : ℝ := (2:ℝ) ^ (1/2 - s) with hA
  have hA0 : 0 < A := Real.rpow_pos_of_pos (by norm_num) _
  have e1 : (2:ℝ) ^ (s - 1/2) = A⁻¹ := by
    rw [hA, ← Real.rpow_neg (by norm_num)]; ring_nf
  have e2 : (2:ℝ) ^ (1 - 2 * s) = A * A := by
    rw [hA, ← Real.rpow_add (by norm_num)]; ring_nf
  rw [e1]
  rw [e2, add_comm s] at hdup
  by_cases h1 : Real.Gamma (1/2 - s) = 0
  · rw [h1, mul_zero] at hrefl
    have hcos : Real.cos (π * s) = 0 := by
      rcases div_eq_zero_iff.mp hrefl.symm with h | h
      · exact absurd h Real.pi_ne_zero
      · exact h
    rw [h1, hcos]; simp
  · have hcos : Real.cos (π * s) ≠ 0 := by
      intro h; rw [h, div_zero] at hrefl
      exact h1 ((mul_eq_zero.mp hrefl).resolve_left hG2.ne')
    have e3 : Real.Gamma (1/2 - s) = π / Real.cos (π * s) / Real.Gamma (1/2 + s) := by
      rw [← hrefl]; field_simp
    have e4 : Real.Gamma (2 * s) = Real.Gamma s * Real.Gamma (1/2 + s) / (A * A * Real.sqrt π) := by
      rw [hdup]; field_simp
    rw [e3, e4]
    field_simp

/-- `sin θ - cos θ > 0` for `π/4 < θ < 5π/4`. -/
private theorem sin_sub_cos_pos {θ : ℝ} (h1 : π / 4 < θ) (h2 : θ < π + π / 4) :
    0 < Real.sin θ - Real.cos θ := by
  have hs : 0 < Real.sin (θ - π / 4) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  rw [Real.sin_sub, Real.cos_pi_div_four, Real.sin_pi_div_four] at hs
  have h2 : (0:ℝ) < Real.sqrt 2 := by positivity
  nlinarith

/-- DLMF 14.15(v): for `c ≥ 0`, the supremum `X` of the positive roots of `U(-c,x) = Ū(-c,x)` is
positive when `c > 0`, is itself a root, and no root exceeds it. -/
theorem sSup_spec {c : ℝ} (hc : 0 ≤ c) :
    (0 < c → (0:ℝ) < sSup
        ({x : ℝ | 0 < x ∧ parabolicCylinderU (-(c:ℂ)) x =
            parabolicCylinderUBar (-(c:ℂ)) x} : Set ℝ)) ∧
      parabolicCylinderU (-(c:ℂ))
          ((sSup ({x : ℝ | 0 < x ∧ parabolicCylinderU (-(c:ℂ)) x =
                     parabolicCylinderUBar (-(c:ℂ)) x} : Set ℝ) :
        ℝ) : ℂ) = parabolicCylinderUBar (-(c:ℂ))
          ((sSup ({x : ℝ | 0 < x ∧ parabolicCylinderU (-(c:ℂ)) x =
                     parabolicCylinderUBar (-(c:ℂ)) x} : Set ℝ) : ℝ) : ℂ) ∧
      ∀ y : ℝ, sSup ({x : ℝ | 0 < x ∧ parabolicCylinderU (-(c:ℂ)) x =
                        parabolicCylinderUBar (-(c:ℂ)) x} : Set ℝ) < y →
        parabolicCylinderU (-(c:ℂ)) y ≠ parabolicCylinderUBar (-(c:ℂ)) y := by
  have ha : -(c:ℂ) = ((-c:ℝ):ℂ) := by push_cast; ring
  rw [ha]
  set a : ℂ := ((-c:ℝ):ℂ) with ha'
  set u : ℝ → ℝ := fun x => (parabolicCylinderU a x).re with hudef
  set u' : ℝ → ℝ := fun x => (parabolicCylinderUDeriv a x).re
  set v : ℝ → ℝ := fun x => (parabolicCylinderV a x).re with hvdef
  set v' : ℝ → ℝ := fun x => (parabolicCylinderVDeriv a x).re
  set G : ℝ := Real.Gamma (1/2 + c) with hGdef
  have hG : 0 < G := Real.Gamma_pos_of_pos (by linarith)
  set w : ℝ := Real.sqrt (2 / π)
  have hw : 0 < w := Real.sqrt_pos.mpr (by positivity)
  have hu : ∀ x, HasDerivAt u (u' x) x := fun x => CylinderRealZeros.hasDerivAt_re (-c) x
  have hv : ∀ x, HasDerivAt v (v' x) x := fun x =>
      (hasDerivAt_parabolicCylinderV a x).real_of_complex
  have hW : ∀ x, u x * v' x - u' x * v x = w := by
    intro x
    have h := congrArg Complex.re (parabolicCylinderV_wronskian a x)
    rw [deriv_parabolicCylinderV, deriv_parabolicCylinderU] at h
    have hi1 : (parabolicCylinderU a x).im = 0 := parabolicCylinderU_real (-c) x
    have hi2 : (parabolicCylinderUDeriv a x).im = 0 := by
      rw [CylinderRealZeros.deriv_eq_re (-c) x]; simp
    rw [Complex.ofReal_re, Complex.sub_re, Complex.mul_re, Complex.mul_re, hi1, hi2, zero_mul,
      zero_mul, sub_zero, sub_zero] at h
    exact h
  have hlim : Tendsto u atTop (𝓝 0) := by
    have h := (Complex.continuous_re.tendsto 0).comp
        (CylinderRealZeros.tendsto_parabolicCylinderU (-c))
    rw [Complex.zero_re] at h; exact h
  have hU : ∀ x : ℝ, parabolicCylinderU a x = (u x : ℂ) := fun x => CylinderRealZeros.eq_re (-c) x
  have hUb : ∀ x : ℝ, parabolicCylinderUBar a x = ((G * v x : ℝ) : ℂ) := by
    intro x
    rw [parabolicCylinderUBar, show (1/2 : ℂ) - a = ((1/2 + c : ℝ) : ℂ) by rw [ha'];
                                                                           push_cast; ring,
      Complex.Gamma_ofReal, Complex.ofReal_mul]
    congr 1
    exact Complex.ext (by simp [hvdef]) (by exact parabolicCylinderV_real (-c) x)
  have heq : ∀ x : ℝ, parabolicCylinderU a x = parabolicCylinderUBar a x ↔ u x = G *
      v x := fun x => by
    rw [hU, hUb, Complex.ofReal_inj]
  have hcont : Continuous fun x => u x - G * v x :=
    continuous_iff_continuousAt.mpr fun x =>
      (hu x).continuousAt.sub ((hv x).continuousAt.const_mul G)
  have hfar : ∀ x, 2 * Real.sqrt c ≤ x → u x ≠ 0 := by
    refine CylinderRealZeros.no_zero_far (t := -c) fun x hx => ?_
    have h0 : 0 ≤ 2 * Real.sqrt c := by positivity
    have hsq := Real.sq_sqrt hc
    nlinarith
  set Z : Set ℝ := {x : ℝ | 0 < x ∧ parabolicCylinderU a x = parabolicCylinderUBar a x} with hZdef
  have hZ : Z = {x : ℝ | 0 < x ∧ u x = G * v x} := by
    ext x; simp only [hZdef, mem_ofPred_eq, heq]
  have hbdd : BddAbove Z := by
    obtain ⟨X, hX⟩ := (eventually_mul_sub_neg hw hG hu hv hW
      (fun x hx => hfar x hx.le) hlim).exists_forall_of_atTop
    refine ⟨X, fun x hx => ?_⟩
    rw [hZ] at hx
    by_contra hlt
    have := hX x (not_le.mp hlt).le
    rw [hx.2, sub_self, mul_zero] at this
    exact lt_irrefl _ this
  -- values at the origin
  set s : ℝ := 1/4 + c/2 with hs
  set K : ℝ := (2:ℝ) ^ (s - 1/2) * Real.Gamma s / Real.sqrt π with hK
  have hK0 : 0 < K := by
    have : 0 < s := by rw [hs]; linarith
    have := Real.Gamma_pos_of_pos this
    have : (0:ℝ) < Real.sqrt π := Real.sqrt_pos.mpr Real.pi_pos
    positivity
  have hu0 : u 0 = K * Real.sin (π * s) := by
    have h := congrArg Complex.re (parabolicCylinderU_neg_zero hc)
    simp only [Complex.ofReal_re] at h
    change (parabolicCylinderU ((-c:ℝ):ℂ) ((0:ℝ):ℂ)).re = _
    rw [Complex.ofReal_zero, h, hK]; ring
  have hv0 : G * v 0 = K * Real.cos (π * s) := by
    have h := congrArg Complex.re (parabolicCylinderUBar_neg_zero hc)
    rw [← Complex.ofReal_zero, hUb, Complex.ofReal_re, Complex.ofReal_re] at h
    rw [h, hK]; ring
  -- existence of a positive root for `c > 0`
  have hex : 0 < c → ∃ r, 0 < r ∧ u r = G * v r := by
    intro hc0
    by_cases hne : {x : ℝ | 0 < x ∧ u x = 0}.Nonempty
    · have hbu : BddAbove {x : ℝ | 0 < x ∧ u x = 0} := ⟨2 * Real.sqrt c, fun x hx => by
        by_contra h; exact hfar x (not_le.mp h).le hx.2⟩
      set x₁ := sSup {x : ℝ | 0 < x ∧ u x = 0}
      obtain ⟨z, hz⟩ := hne
      have hz1 : z ≤ x₁ := le_csSup hbu hz
      have hcl : IsClosed {x : ℝ | u x = 0} :=
        isClosed_eq (continuous_iff_continuousAt.mpr fun x => (hu x).continuousAt)
          continuous_const
      have hx₁ : u x₁ = 0 :=
        (closure_minimal (s := {x : ℝ | 0 < x ∧ u x = 0}) (fun x hx => hx.2) hcl)
          (csSup_mem_closure ⟨z, hz⟩ hbu)
      obtain ⟨r, hr, hr0⟩ := exists_root_of_zero hw hG hu hv hW hlim hx₁ fun x hx h0 =>
        absurd (le_csSup hbu ⟨hz.1.trans (hz1.trans_lt hx), h0⟩) (not_le.mpr hx)
      exact ⟨r, hz.1.trans (hz1.trans_lt hr), hr0⟩
    · have hpos : ∀ x, 0 < x → u x ≠ 0 := fun x hx h0 => hne ⟨x, hx, h0⟩
      by_cases h0 : u 0 = 0
      · obtain ⟨r, hr, hr0⟩ := exists_root_of_zero hw hG hu hv hW hlim h0 hpos
        exact ⟨r, hr, hr0⟩
      · have hne0 : ∀ x, 0 ≤ x → u x ≠ 0 := fun x hx => by
          rcases hx.eq_or_lt with h | h
          · rw [← h]; exact h0
          · exact hpos x h
        have hc32 : c < 3/2 := by
          by_contra hc32
          push Not at hc32
          set n := ⌊(c + 1/2) / 2⌋₊ with hn
          have hn1 : (n:ℝ) ≤ (c + 1/2) / 2 := Nat.floor_le (by linarith)
          have hn2 : (c + 1/2) / 2 < n + 1 := Nat.lt_floor_add_one _
          rcases hn1.eq_or_lt with he | hlt
          · apply h0
            rw [hu0, show π * s = (n:ℝ) * π by rw [hs, he]; ring, Real.sin_nat_mul_pi,
              mul_zero]
          · have hn0 : 0 < n := by
              have : (0:ℝ) < n := by linarith
              exact_mod_cast this
            obtain ⟨-, hcard⟩ :=
                parabolicCylinderU_positive_zero_count (a := -c) n hn0 (by linarith)
              (by linarith)
            have hnon : ({x : ℝ | 0 < x ∧ parabolicCylinderU ((-c:ℝ):ℂ) x = 0} : Set ℝ).Nonempty :=
              Set.nonempty_of_ncard_ne_zero (by omega)
            obtain ⟨x, hx, hx0⟩ := hnon
            exact hpos x hx (by
              rw [hudef]; simp only
              rw [show ((-c:ℝ):ℂ) = a from rfl] at hx0
              rw [hx0, Complex.zero_re])
        have hs1 : π / 4 < π * s := by rw [hs]; nlinarith [Real.pi_pos]
        have hs2 : π * s < π := by rw [hs]; nlinarith [Real.pi_pos]
        have hsin := Real.sin_pos_of_pos_of_lt_pi (by linarith) hs2
        have hsc := sin_sub_cos_pos hs1 (by linarith [Real.pi_pos])
        obtain ⟨r, hr, hr0⟩ := exists_root_of_mul_pos hw hG hu hv hW hlim hne0 (by
          rw [hu0, hv0, ← mul_sub]; positivity)
        exact ⟨r, hr, hr0⟩
  by_cases hZn : Z.Nonempty
  · obtain ⟨z, hz⟩ := hZn
    have hz1 : z ≤ sSup Z := le_csSup hbdd hz
    have hcl : IsClosed {x : ℝ | u x - G * v x = 0} := isClosed_eq hcont continuous_const
    have hS : u (sSup Z) = G * v (sSup Z) := by
      have h := (closure_minimal (fun x hx => by
          rw [hZ] at hx; exact sub_eq_zero.mpr hx.2) hcl) (csSup_mem_closure ⟨z, hz⟩ hbdd)
      exact sub_eq_zero.mp h
    refine ⟨fun _ => hz.1.trans_le hz1, (heq _).mpr hS, fun x hx h => ?_⟩
    exact absurd (le_csSup hbdd ⟨hz.1.trans (hz1.trans_lt hx), h⟩) (not_le.mpr hx)
  · have hZe : Z = ∅ := Set.not_nonempty_iff_eq_empty.mp hZn
    have hc0 : c = 0 := by
      by_contra h
      obtain ⟨r, hr, hr0⟩ := hex (lt_of_le_of_ne hc (Ne.symm h))
      exact hZn ⟨r, by rw [hZ]; exact ⟨hr, hr0⟩⟩
    rw [hZe, Real.sSup_empty]
    refine ⟨fun h => absurd hc0 h.ne', ?_, fun x hx h => ?_⟩
    · rw [show ((0:ℝ):ℂ) = ((0:ℝ):ℂ) from rfl, heq, hu0, hv0, hs, hc0]
      rw [show π * (1/4 + 0/2 : ℝ) = π / 4 by ring, Real.sin_pi_div_four, Real.cos_pi_div_four]
    · have : x ∈ Z := ⟨hx, h⟩
      rw [hZe] at this
      exact this

end DLMF.Legendre.CylinderCrossing

end
