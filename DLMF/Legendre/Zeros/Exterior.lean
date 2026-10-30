/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Legendre.Zeros.FerrersAndReal

/-!
# Exterior zeros of associated Legendre functions

Exterior zero counts and nonvanishing criteria obtained from the self-adjoint Legendre equation.

Source references and common attribution are retained in
`DLMF.Legendre.Zeros`.
-/

@[expose] public noncomputable section

open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF

open scoped Real Topology Nat

namespace DLMF.Legendre

attribute [local instance] Classical.propDecidable

/-! ### Exterior zeros of `P^μ_ν` (DLMF 14.16(iii)) -/

/-- A function with zero derivative on an interval is constant there. -/
theorem lzero_const_of_deriv_zero {r r' : ℝ → ℝ} {s : Set ℝ} (hs : s.OrdConnected)
    (hd : ∀ x ∈ s, HasDerivAt r (r' x) x) (h0 : ∀ x ∈ s, r' x = 0) {x y : ℝ} (hx : x ∈ s)
    (hy : y ∈ s) : r x = r y := by
  wlog hxy : x < y generalizing x y
  · rcases eq_or_lt_of_le (not_lt.mp hxy) with h | h
    · rw [h]
    · exact (this hy hx h).symm
  have hsub : Icc x y ⊆ s := hs.out hx hy
  obtain ⟨ξ, hξ, he⟩ := exists_hasDerivAt_eq_slope r r' hxy
    (fun t ht => (hd t (hsub ht)).continuousAt.continuousWithinAt)
    (fun t ht => hd t (hsub (Ioo_subset_Icc_self ht)))
  rw [h0 ξ (hsub (Ioo_subset_Icc_self hξ)), eq_comm, div_eq_zero_iff] at he
  rcases he with h | h
  · linarith
  · linarith

/-- On `(1, ∞)`: a function with `(x²-1)(v f' - f v') = c > 0` against a positive solution `v`
with `(x²-1)v² = O(x-1)` is negative near `1`. -/
theorem lzero_ext_neg_near_one {f f' v v' : ℝ → ℝ} {s K c : ℝ} (hs : 1 < s) (hK : 0 < K)
    (hc : 0 < c) (hfd : ∀ x ∈ Ioc 1 s, HasDerivAt f (f' x) x)
    (hvd : ∀ x ∈ Ioc 1 s, HasDerivAt v (v' x) x) (hv : ∀ x ∈ Ioc 1 s, 0 < v x)
    (hb : ∀ x ∈ Ioc 1 s, (x ^ 2 - 1) * v x ^ 2 ≤ K * (x - 1))
    (hW : ∀ x ∈ Ioc 1 s, (x ^ 2 - 1) * (v x * f' x - f x * v' x) = c) :
    ∃ t ∈ Ioo 1 s, ∀ x ∈ Ioo 1 t, f x < 0 := by
  have hp : ∀ x ∈ Ioc 1 s, 0 < x ^ 2 - 1 := fun x hx => by nlinarith [hx.1]
  have hD : ∀ x ∈ Ioc 1 s, 0 < v x * f' x - f x * v' x := fun x hx =>
    (mul_pos_iff_of_pos_left (hp x hx)).mp (by rw [hW x hx]; exact hc)
  have hder : ∀ x ∈ Ioc 1 s, HasDerivAt (fun t => f t / v t)
      ((f' x * v x - f x * v' x) / v x ^ 2) x := fun x hx =>
    (hfd x hx).fun_div (hvd x hx) (hv x hx).ne'
  obtain ⟨x0, hx0, h0⟩ := ODE.sturmCount_exists_neg_of_deriv_ge (r := fun t => f t / v t)
    (r' := fun x => (f' x * v x - f x * v' x) / v x ^ 2) (c := c / K) hs (div_pos hc hK) hder
    (fun x hx => by
      have hv2 := pow_pos (hv x hx) 2
      have h1x : 0 < x - 1 := by linarith [hx.1]
      rw [div_div, div_le_div_iff₀ (mul_pos hK h1x) hv2]
      have e : f' x * v x - f x * v' x = v x * f' x - f x * v' x := by ring
      rw [e]
      have := hb x hx
      have hWx := hW x hx
      nlinarith [mul_le_mul_of_nonneg_left this (hD x hx).le])
  refine ⟨x0, hx0, fun x hx => ?_⟩
  have hmono : StrictMonoOn (fun t => f t / v t) (Ioc 1 s) := by
    apply strictMonoOn_of_deriv_pos (convex_Ioc 1 s)
    · exact fun t ht => (hder t ht).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Ioc] at ht
      have htI : t ∈ Ioc 1 s := Ioo_subset_Ioc_self ht
      rw [(hder t htI).deriv]
      exact div_pos (by linarith [hD t htI]) (pow_pos (hv t htI) 2)
  have hxI : x ∈ Ioc 1 s := ⟨hx.1, hx.2.le.trans hx0.2.le⟩
  have := hmono hxI ⟨hx0.1, hx0.2.le⟩ hx.2
  have h2 : f x / v x < 0 := lt_trans this h0
  have h3 := mul_neg_of_neg_of_pos h2 (hv x hxI)
  rwa [div_mul_cancel₀ _ (hv x hxI).ne'] at h3

/-- On `(1, ∞)`: a function with `(x²-1)(u f' - f u') = c > 0` against a positive solution `u`
with `(x²-1)u² = O(x)` is eventually positive. -/
theorem lzero_ext_pos_atTop {f f' u u' : ℝ → ℝ} {X K c : ℝ} (hX : 1 < X) (hK : 0 < K)
    (hc : 0 < c) (hfd : ∀ x ∈ Ici X, HasDerivAt f (f' x) x)
    (hud : ∀ x ∈ Ici X, HasDerivAt u (u' x) x) (hu : ∀ x ∈ Ici X, 0 < u x)
    (hb : ∀ x ∈ Ici X, (x ^ 2 - 1) * u x ^ 2 ≤ K * x)
    (hW : ∀ x ∈ Ici X, (x ^ 2 - 1) * (u x * f' x - f x * u' x) = c) :
    ∃ T, ∀ x, T < x → 0 < f x := by
  have hX0 : 0 < X := by linarith
  have hp : ∀ x ∈ Ici X, 0 < x ^ 2 - 1 := fun x hx => by
    have : X ≤ x := hx; nlinarith
  have hD : ∀ x ∈ Ici X, 0 < u x * f' x - f x * u' x := fun x hx =>
    (mul_pos_iff_of_pos_left (hp x hx)).mp (by rw [hW x hx]; exact hc)
  set r : ℝ → ℝ := fun t => f t / u t - c / K * Real.log t
  have hder : ∀ x ∈ Ici X, HasDerivAt r
      ((f' x * u x - f x * u' x) / u x ^ 2 - c / K * x⁻¹) x := fun x hx => by
    have : (0:ℝ) < x := lt_of_lt_of_le hX0 hx
    exact ((hfd x hx).fun_div (hud x hx) (hu x hx).ne').sub
      ((Real.hasDerivAt_log this.ne').const_mul _)
  have hge : ∀ x ∈ Ici X, 0 ≤ (f' x * u x - f x * u' x) / u x ^ 2 - c / K * x⁻¹ := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le hX0 hx
    have hu2 := pow_pos (hu x hx) 2
    rw [sub_nonneg, show c / K * x⁻¹ = c / (K * x) by field_simp, div_le_div_iff₀
      (mul_pos hK hx0) hu2]
    have e : f' x * u x - f x * u' x = u x * f' x - f x * u' x := by ring
    rw [e]
    have := hb x hx
    have hWx := hW x hx
    nlinarith [mul_le_mul_of_nonneg_left this (hD x hx).le]
  have hmono : MonotoneOn r (Ici X) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici X)
    · exact fun t ht => (hder t ht).continuousAt.continuousWithinAt
    · exact fun t ht => (hder t (interior_subset ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [(hder t (interior_subset ht)).deriv]
      exact hge t (interior_subset ht)
  set A := |r X| + 1 with hA
  refine ⟨max X (Real.exp (A * K / c)), fun x hx => ?_⟩
  have hxX : X ≤ x := (le_max_left _ _).trans hx.le
  have hx0 : 0 < x := lt_of_lt_of_le hX0 hxX
  have hxe : Real.exp (A * K / c) < x := (le_max_right _ _).trans_lt hx
  have hlog : A * K / c < Real.log x := by
    rw [Real.lt_log_iff_exp_lt hx0]; exact hxe
  have h1 := hmono self_mem_Ici (show x ∈ Ici X from hxX) hxX
  simp only [r] at h1
  have h2 : A < c / K * Real.log x := by
    rw [div_lt_iff₀ hc] at hlog
    have : A * K < Real.log x * c := hlog
    rw [div_mul_eq_mul_div, lt_div_iff₀ hK]; linarith
  have h3 : 0 < f x / u x := by
    have h4 := neg_abs_le (r X)
    simp only [r] at h4 hA
    linarith
  exact (div_pos_iff_of_pos_right (hu x hxX)).mp h3

/-- A function with zero derivative on an interval is constant there. -/
theorem lzero_ext_count {f f' Q Q' : ℝ → ℝ} {c t₁ T σ₁ σ₂ : ℝ} (ht₁ : 1 < t₁)
    (hfd : ∀ x, 1 < x → HasDerivAt f (f' x) x) (hQd : ∀ x, 1 < x → HasDerivAt Q (Q' x) x)
    (hQ : ∀ x, 1 < x → 0 < Q x) (hc : c ≠ 0)
    (hW : ∀ x, 1 < x → (x ^ 2 - 1) * (Q x * f' x - f x * Q' x) = c)
    (hl : ∀ x ∈ Ioo 1 t₁, 0 < σ₁ * f x) (hr : ∀ x, T < x → 0 < σ₂ * f x) :
    {x | 1 < x ∧ f x = 0}.Finite ∧
      {x | 1 < x ∧ f x = 0}.ncard = if σ₁ * σ₂ < 0 then 1 else 0 := by
  set g : ℝ → ℝ := fun x => c * (f x / Q x)
  have hder : ∀ x, 1 < x → HasDerivAt g (c * ((f' x * Q x - f x * Q' x) / Q x ^ 2)) x :=
    fun x hx => ((hfd x hx).fun_div (hQd x hx) (hQ x hx).ne').const_mul c
  have hmono : StrictMonoOn g (Ioi 1) := by
    apply strictMonoOn_of_deriv_pos (convex_Ioi 1)
    · exact fun t ht => (hder t ht).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Ioi] at ht
      rw [(hder t ht).deriv]
      have hp : 0 < t ^ 2 - 1 := by have : (1:ℝ) < t := ht; nlinarith
      have hWt := hW t ht
      have e : c * ((f' t * Q t - f t * Q' t) / Q t ^ 2) =
          c * ((t ^ 2 - 1) * (Q t * f' t - f t * Q' t)) / ((t ^ 2 - 1) * Q t ^ 2) := by
        field_simp
      rw [e, hWt]
      exact div_pos (mul_self_pos.mpr hc) (mul_pos hp (pow_pos (hQ t ht) 2))
  have hg0 : ∀ x, 1 < x → (g x = 0 ↔ f x = 0) := fun x hx => by
    simp only [g, mul_eq_zero, hc, false_or, div_eq_zero_iff, (hQ x hx).ne', or_false]
  have huniq : ∀ a b, 1 < a → 1 < b → f a = 0 → f b = 0 → a = b := by
    intro a b ha hb h1 h2
    exact hmono.injOn ha hb (by rw [(hg0 a ha).2 h1, (hg0 b hb).2 h2])
  have hcont : ContinuousOn f (Ioi 1) := fun x hx => (hfd x hx).continuousAt.continuousWithinAt
  by_cases hσ : σ₁ * σ₂ < 0
  · simp only [hσ, ↓reduceIte]
    set x1 := (1 + t₁) / 2
    have hx1 : x1 ∈ Ioo 1 t₁ := ⟨by simp only [x1]; linarith, by simp only [x1]; linarith⟩
    set x2 := max T x1 + 1
    have hx2T : T < x2 := by have := le_max_left T x1; simp only [x2]; linarith
    have hx12 : x1 < x2 := by have := le_max_right T x1; simp only [x2]; linarith
    have h1 := hl x1 hx1
    have h2 := hr x2 hx2T
    have hprod : f x1 * f x2 < 0 := by nlinarith
    have hsub : Icc x1 x2 ⊆ Ioi 1 := fun x hx => lt_of_lt_of_le hx1.1 hx.1
    obtain ⟨z, hz, hz0⟩ : ∃ z ∈ Icc x1 x2, f z = 0 := by
      rcases lt_or_gt_of_ne (show f x1 ≠ 0 by intro h; rw [h] at hprod; simp at hprod) with
        hn | hp
      · have : 0 < f x2 := by nlinarith
        exact intermediate_value_Icc hx12.le (hcont.mono hsub) ⟨hn.le, this.le⟩
      · have : f x2 < 0 := by nlinarith
        exact intermediate_value_Icc' hx12.le (hcont.mono hsub) ⟨this.le, hp.le⟩
    have hz1 : 1 < z := hsub hz
    have hZ : {x | 1 < x ∧ f x = 0} = {z} := by
      ext x
      simp only [mem_ofPred_eq, mem_singleton_iff]
      exact ⟨fun ⟨hx, h0⟩ => huniq x z hx hz1 h0 hz0, fun h => h ▸ ⟨hz1, hz0⟩⟩
    rw [hZ]; exact ⟨finite_singleton z, ncard_singleton z⟩
  · simp only [hσ, ↓reduceIte]
    have hZ : {x | 1 < x ∧ f x = 0} = ∅ := by
      ext z
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
      intro hz1 hz0
      set x1 := min ((1 + t₁) / 2) ((1 + z) / 2)
      have a1 := min_le_left ((1 + t₁) / 2) ((1 + z) / 2)
      have a2 := min_le_right ((1 + t₁) / 2) ((1 + z) / 2)
      have hx1 : x1 ∈ Ioo 1 t₁ := ⟨lt_min (by linarith) (by linarith), by linarith⟩
      have hx1z : x1 < z := by linarith
      set x2 := max T z + 1
      have hx2T : T < x2 := by have := le_max_left T z; simp only [x2]; linarith
      have hzx2 : z < x2 := by have := le_max_right T z; simp only [x2]; linarith
      have hgz : g z = 0 := (hg0 z hz1).2 hz0
      have g1 := hmono hx1.1 hz1 hx1z
      have g2 := hmono hz1 (show (1:ℝ) < x2 by linarith) hzx2
      rw [hgz] at g1 g2
      simp only [g] at g1 g2
      have q1 := hQ x1 hx1.1
      have q2 := hQ x2 (by linarith)
      have k1 : c * f x1 < 0 := by
        have : c * f x1 = c * (f x1 / Q x1) * Q x1 := by field_simp
        rw [this]; exact mul_neg_of_neg_of_pos g1 q1
      have k2 : 0 < c * f x2 := by
        have : c * f x2 = c * (f x2 / Q x2) * Q x2 := by field_simp
        rw [this]; exact mul_pos g2 q2
      have h1 := hl x1 hx1
      have h2 := hr x2 hx2T
      have hprod : f x1 * f x2 < 0 := by
        have : (c * f x1) * (c * f x2) < 0 := mul_neg_of_neg_of_pos k1 k2
        have hc2 : 0 < c ^ 2 := by positivity
        nlinarith
      apply hσ
      nlinarith [mul_pos h1 h2]
    rw [hZ]; exact ⟨finite_empty, ncard_empty ℝ⟩

/-- The rule of DLMF 14.16(iii) (as corrected) through the sign of `sin(μπ)/Γ(ν-μ+1)`. -/
theorem lzero_oneZero_iff {ν μ : ℝ} : AssociatedPOneZero ν μ ↔
    0 < μ ∧ (∀ n : ℤ, μ ≠ n) ∧ Real.sin (μ * π) * (Real.Gamma (ν - μ + 1))⁻¹ < 0 := by
  have hinv : ν < μ → (Real.Gamma (ν - μ + 1))⁻¹ =
      Real.sin ((μ - ν) * π) * Real.Gamma (μ - ν) / π := by
    intro hlt
    have hG : 0 < Real.Gamma (μ - ν) := Real.Gamma_pos_of_pos (by linarith)
    have h := Real.Gamma_mul_Gamma_one_sub (ν - μ + 1)
    rw [show 1 - (ν - μ + 1) = μ - ν by ring] at h
    have hs : Real.sin (π * (ν - μ + 1)) = Real.sin ((μ - ν) * π) := by
      rw [show π * (ν - μ + 1) = -((μ - ν) * π) + π by ring, Real.sin_add_pi, Real.sin_neg, neg_neg]
    rw [hs] at h
    by_cases h0 : Real.sin ((μ - ν) * π) = 0
    · rw [h0, div_zero, mul_eq_zero, or_iff_left hG.ne'] at h
      rw [h, h0, inv_zero, zero_mul, zero_div]
    · have hπ := Real.pi_pos
      have hGs : Real.Gamma (ν - μ + 1) = π / (Real.sin ((μ - ν) * π) * Real.Gamma (μ - ν)) := by
        have h' := h
        field_simp at h'
        rw [eq_div_iff (mul_ne_zero h0 hG.ne')]
        linear_combination h'
      rw [hGs, inv_div]
  unfold AssociatedPOneZero
  constructor
  · rintro (⟨h0, hlt, hn, hs⟩ | ⟨h0, hle, hn, hodd⟩)
    · refine ⟨h0, hn, ?_⟩
      rw [hinv hlt]
      have hG : 0 < Real.Gamma (μ - ν) := Real.Gamma_pos_of_pos (by linarith)
      have : Real.sin (μ * π) * (Real.sin ((μ - ν) * π) * Real.Gamma (μ - ν) / π) =
          Real.sin ((μ - ν) * π) * Real.sin (μ * π) * (Real.Gamma (μ - ν) / π) := by ring
      rw [this]
      exact mul_neg_of_neg_of_pos hs (div_pos hG Real.pi_pos)
    · refine ⟨h0, hn, ?_⟩
      have hG : 0 < Real.Gamma (ν - μ + 1) := Real.Gamma_pos_of_pos (by linarith)
      have hss := lzero_sin_sign hn
      rw [hodd.neg_one_zpow] at hss
      exact mul_neg_of_neg_of_pos (by linarith) (inv_pos.mpr hG)
  · rintro ⟨h0, hn, hneg⟩
    rcases lt_or_ge ν μ with hlt | hle
    · refine Or.inl ⟨h0, hlt, hn, ?_⟩
      rw [hinv hlt] at hneg
      have hG : 0 < Real.Gamma (μ - ν) / π := div_pos (Real.Gamma_pos_of_pos (by linarith))
        Real.pi_pos
      have : Real.sin (μ * π) * (Real.sin ((μ - ν) * π) * Real.Gamma (μ - ν) / π) =
          Real.sin ((μ - ν) * π) * Real.sin (μ * π) * (Real.Gamma (μ - ν) / π) := by ring
      rw [this] at hneg
      rcases mul_neg_iff.mp hneg with ⟨_, h⟩ | ⟨h, _⟩
      · linarith
      · exact h
    · refine Or.inr ⟨h0, hle, hn, ?_⟩
      have hG : 0 < Real.Gamma (ν - μ + 1) := Real.Gamma_pos_of_pos (by linarith)
      have hs : Real.sin (μ * π) < 0 := by
        rcases mul_neg_iff.mp hneg with ⟨_, h⟩ | ⟨h, _⟩
        · linarith [inv_pos.mpr hG]
        · exact h
      have hss := lzero_sin_sign hn
      rcases Int.even_or_odd ⌊μ⌋ with he | ho
      · rw [he.neg_one_zpow, one_mul] at hss; linarith
      · exact ho

/-- For positive parameters the regularized Gauss series on `[0, 1)` is real, positive and
increasing. -/
theorem lzero_regGauss_pos_mono {a b c w w' : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hw0 : 0 ≤ w) (hww : w ≤ w') (hw1 : w' < 1) :
    0 < (regularizedGaussHG a b c w).re ∧ (regularizedGaussHG a b c w).im = 0 ∧
      (regularizedGaussHG a b c w).re ≤ (regularizedGaussHG a b c w').re := by
  have hG : ∀ n : ℕ, 0 < Real.Gamma (c + n) := fun n => Real.Gamma_pos_of_pos (by positivity)
  let f : ℝ → ℕ → ℝ := fun w n => (ascPochhammer ℝ n).eval a *
    (ascPochhammer ℝ n).eval b * w ^ n / n.factorial * (Real.Gamma (c + n))⁻¹
  have hsum : ∀ w : ℝ, 0 ≤ w → w < 1 → HasSum (fun n => (f w n : ℂ)) (regularizedGaussHG a b c w) := by
    intro w hw0 hw1
    have hw : ‖(w : ℂ)‖ < 1 := by rw [norm_real, Real.norm_eq_abs, abs_of_nonneg hw0]; exact hw1
    rw [regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hw]
    refine (hasSum_regularizedGaussHGFun _ _ _ hw).congr_fun fun n => ?_
    simp only [f]
    rw [ascPochhammer_eval_ofReal, ascPochhammer_eval_ofReal,
      show (c : ℂ) + n = ((c + n : ℝ) : ℂ) by push_cast; ring, Complex.Gamma_ofReal]
    push_cast; ring
  have hf0 : ∀ w : ℝ, 0 ≤ w → ∀ n, 0 ≤ f w n := fun w hw n => by
    have := ascPochhammer_pos n a ha
    have := ascPochhammer_pos n b hb
    have := hG n
    simp only [f]; positivity
  have h1 := hsum w hw0 (hww.trans_lt hw1)
  have h2 := hsum w' (hw0.trans hww) hw1
  have hr1 : HasSum (f w) (regularizedGaussHG a b c w).re := by
    simpa using Complex.reCLM.hasSum h1
  have hr2 : HasSum (f w') (regularizedGaussHG a b c w').re := by
    simpa using Complex.reCLM.hasSum h2
  have hi1 : HasSum (fun _ : ℕ => (0:ℝ)) (regularizedGaussHG a b c w).im := by
    simpa using Complex.imCLM.hasSum h1
  refine ⟨?_, (hi1.unique hasSum_zero), hasSum_le (fun n => ?_) hr1 hr2⟩
  · have := le_hasSum hr1 0 fun j _ => hf0 w hw0 j
    have h00 : 0 < f w 0 := by
      have := hG 0
      simp only [f, ascPochhammer_zero, Polynomial.eval_one, pow_zero, Nat.factorial_zero,
        Nat.cast_one, div_one, one_mul, Nat.cast_zero, add_zero]
      positivity
    linarith
  · simp only [f]
    have := ascPochhammer_pos n a ha
    have := ascPochhammer_pos n b hb
    have := hG n
    have hp : w ^ n ≤ w' ^ n := pow_le_pow_left₀ hw0 hww n
    have hk : 0 ≤ (ascPochhammer ℝ n).eval a * (ascPochhammer ℝ n).eval b := by positivity
    have hk2 : 0 ≤ (n.factorial : ℝ)⁻¹ * (Real.Gamma (c + n))⁻¹ := by positivity
    calc (ascPochhammer ℝ n).eval a * (ascPochhammer ℝ n).eval b * w ^ n / n.factorial *
          (Real.Gamma (c + n))⁻¹
        = ((ascPochhammer ℝ n).eval a * (ascPochhammer ℝ n).eval b) * w ^ n *
          ((n.factorial : ℝ)⁻¹ * (Real.Gamma (c + n))⁻¹) := by ring
      _ ≤ ((ascPochhammer ℝ n).eval a * (ascPochhammer ℝ n).eval b) * w' ^ n *
          ((n.factorial : ℝ)⁻¹ * (Real.Gamma (c + n))⁻¹) := by gcongr
      _ = _ := by ring

/-- Positivity of `𝑸^μ_ν` on `(1, ∞)` (`ν > -1`) and the bound `(x²-1)(𝑸^μ_ν)² = O(x)` at
infinity (`ν ≥ -1/2`). -/
theorem lzero_olverQ_pos_bound {ν : ℝ} (hν : -1/2 ≤ ν) (μ : ℝ) :
    (∀ x : ℝ, 1 < x → 0 < (olverQ ν μ x).re) ∧
      ∃ K > 0, ∀ x : ℝ, 2 ≤ x → (x ^ 2 - 1) * (olverQ ν μ x).re ^ 2 ≤ K * x := by
  -- reduce to `μ ≥ 0`
  have hred : ∀ x : ℝ, 1 < x → olverQ ν μ x = olverQ ν (|μ| : ℝ) x := by
    intro x hx
    rcases le_or_gt 0 μ with h | h
    · rw [abs_of_nonneg h]
    · have := associated_connection_14 (ν:ℂ) ((|μ|:ℝ):ℂ) (z := (x:ℂ)) (lzero_mem hx)
      rw [← this, abs_of_neg h]; push_cast; ring_nf
  set m := |μ| with hm
  have hm0 : 0 ≤ m := abs_nonneg μ
  set a := (ν + m + 2) / 2
  set b := (ν + m + 1) / 2
  set c := ν + 3 / 2
  have ha : 0 < a := by simp only [a]; linarith
  have hb : 0 < b := by simp only [b]; linarith
  have hc : 0 < c := by simp only [c]; linarith
  -- the real form
  set R : ℝ → ℝ := fun x => Real.sqrt π * Real.exp (m / 2 * (Real.log (x - 1) + Real.log (x + 1))) /
    ((2:ℝ) ^ (ν + 1) * x ^ (ν + m + 1)) with hR
  have hrep : ∀ x : ℝ, 1 < x → olverQ ν m x = (R x : ℂ) * regularizedGaussHG a b c (1 / x ^ 2) := by
    intro x hx
    unfold olverQ legendreBranchPower
    have h1 : (x:ℂ) - 1 = ((x - 1 : ℝ) : ℂ) := by push_cast; ring
    have h2 : (x:ℂ) + 1 = ((x + 1 : ℝ) : ℂ) := by push_cast; ring
    rw [h1, h2, ← ofReal_log (by linarith), ← ofReal_log (by linarith)]
    have e1 : (2:ℂ) ^ ((ν:ℂ) + 1) = (((2:ℝ) ^ (ν + 1) : ℝ) : ℂ) := by
      rw [ofReal_cpow (by norm_num)]; push_cast; ring_nf
    have e2 : (x:ℂ) ^ ((ν:ℂ) + (m:ℂ) + 1) = ((x ^ (ν + m + 1) : ℝ) : ℂ) := by
      rw [ofReal_cpow (by linarith)]; push_cast; ring_nf
    rw [e1, e2]
    simp only [hR, a, b, c]
    push_cast
    ring_nf
  have hdata : ∀ x : ℝ, 1 < x → 0 < R x ∧ (olverQ ν m x).re =
      R x * (regularizedGaussHG a b c ((1 / x ^ 2 : ℝ) : ℂ)).re := by
    intro x hx
    refine ⟨by
      simp only [hR]
      have : 0 < (2:ℝ) ^ (ν + 1) := Real.rpow_pos_of_pos (by norm_num) _
      have : 0 < x ^ (ν + m + 1) := Real.rpow_pos_of_pos (by linarith) _
      have : 0 < Real.sqrt π := Real.sqrt_pos.mpr Real.pi_pos
      positivity, ?_⟩
    rw [hrep x hx, show (1:ℂ) / (x:ℂ) ^ 2 = ((1 / x ^ 2 : ℝ) : ℂ) by push_cast; ring,
      re_ofReal_mul]
  have hw : ∀ x : ℝ, 1 < x → 0 ≤ 1 / x ^ 2 ∧ 1 / x ^ 2 < 1 := fun x hx =>
    ⟨by positivity, by rw [div_lt_one (by positivity)]; nlinarith⟩
  refine ⟨fun x hx => ?_, ?_⟩
  · rw [hred x hx]
    obtain ⟨hR0, hre⟩ := hdata x hx
    rw [hre]
    exact mul_pos hR0 (lzero_regGauss_pos_mono ha hb hc (hw x hx).1 le_rfl (hw x hx).2).1
  · set S := (regularizedGaussHG a b c ((1 / 4 : ℝ) : ℂ)).re
    refine ⟨π * S ^ 2 + 1, by positivity, fun x hx => ?_⟩
    have hx1 : 1 < x := by linarith
    have hx0 : 0 < x := by linarith
    rw [hred x hx1]
    obtain ⟨hR0, hre⟩ := hdata x hx1
    rw [hre]
    obtain ⟨hF0, -, hFle⟩ := lzero_regGauss_pos_mono ha hb hc (hw x hx1).1
      (show 1 / x ^ 2 ≤ 1 / 4 by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith) (by norm_num)
    set F := (regularizedGaussHG a b c ((1 / x ^ 2 : ℝ) : ℂ)).re
    -- `(x²-1) R² ≤ π x`
    obtain ⟨t, ht⟩ : ∃ t, Real.log x = t := ⟨_, rfl⟩
    obtain ⟨L, hLd⟩ : ∃ L, Real.log (x - 1) + Real.log (x + 1) = L := ⟨_, rfl⟩
    have hL : L = Real.log (x ^ 2 - 1) := by
      rw [← hLd, ← Real.log_mul (by linarith) (by linarith)]; ring_nf
    have hLt : L ≤ 2 * t := by
      have h := Real.log_le_log (by nlinarith) (show x ^ 2 - 1 ≤ x ^ 2 by linarith)
      rw [Real.log_pow] at h
      push_cast at h
      rw [hL, ← ht]; linarith
    have hexpL : Real.exp L = x ^ 2 - 1 := by rw [hL, Real.exp_log (by nlinarith)]
    have ht0 : 0 ≤ t := by rw [← ht]; exact Real.log_nonneg (by linarith)
    have hxt : x = Real.exp t := by rw [← ht, Real.exp_log hx0]
    have h2p : 1 ≤ (2:ℝ) ^ (ν + 1) := Real.one_le_rpow (by norm_num) (by linarith)
    have hxp : x ^ (ν + m + 1) = Real.exp ((ν + m + 1) * t) := by
      rw [Real.rpow_def_of_pos hx0, ht]; ring_nf
    have hRsq : (x ^ 2 - 1) * R x ^ 2 ≤ π * x := by
      simp only [hR]
      rw [hLd, div_pow, mul_pow, Real.sq_sqrt Real.pi_pos.le, mul_pow]
      have e1 : Real.exp (m / 2 * L) ^ 2 = Real.exp (m * L) := by
        rw [← Real.exp_nat_mul]; ring_nf
      have e2 : (x ^ (ν + m + 1)) ^ 2 = Real.exp (2 * (ν + m + 1) * t) := by
        rw [hxp, ← Real.exp_nat_mul]; ring_nf
      rw [e1, e2, ← hexpL]
      have hd : 0 < ((2:ℝ) ^ (ν + 1)) ^ 2 * Real.exp (2 * (ν + m + 1) * t) := by positivity
      rw [mul_div_assoc', div_le_iff₀ hd]
      have hk0 : Real.exp L * Real.exp (m * L) ≤ Real.exp (2 * (ν + m + 1) * t) * Real.exp t := by
        rw [← Real.exp_add, ← Real.exp_add]; apply Real.exp_le_exp.mpr; nlinarith
      have hk : Real.exp L * (π * Real.exp (m * L)) ≤
          π * (Real.exp (2 * (ν + m + 1) * t) * x) := by
        rw [hxt]
        nlinarith [Real.pi_pos]
      have h2sq : 1 ≤ ((2:ℝ) ^ (ν + 1)) ^ 2 := one_le_pow₀ h2p
      have hE : 0 ≤ π * (Real.exp (2 * (ν + m + 1) * t) * x) := by positivity
      nlinarith
    have hF2 : F ^ 2 ≤ S ^ 2 := pow_le_pow_left₀ hF0.le hFle 2
    have hp : 0 ≤ x ^ 2 - 1 := by nlinarith
    calc (x ^ 2 - 1) * (R x * F) ^ 2 = ((x ^ 2 - 1) * R x ^ 2) * F ^ 2 := by ring
      _ ≤ (π * x) * S ^ 2 := mul_le_mul hRsq hF2 (sq_nonneg _) (by positivity)
      _ ≤ (π * S ^ 2 + 1) * x := by nlinarith

/-- Real form of a Wronskian identity on `(1, ∞)` for functions real there. -/
theorem lzero_ext_wr {F G : ℂ → ℂ} {x c : ℝ} (hx : 1 < x) (hF : (F x).im = 0)
    (hG : (G x).im = 0) (h : ODE.wronskian F G x = (c : ℂ) / ((x : ℂ) ^ 2 - 1)) :
    (x ^ 2 - 1) * ((F x).re * (deriv G x).re - (G x).re * (deriv F x).re) = c := by
  have hp : x ^ 2 - 1 ≠ 0 := by nlinarith
  rw [show (c : ℂ) / ((x : ℂ) ^ 2 - 1) = ((c / (x ^ 2 - 1) : ℝ) : ℂ) by push_cast; ring] at h
  have h' := congrArg re h
  simp only [ODE.wronskian, sub_re, mul_re, hF, hG, zero_mul, sub_zero, ofReal_re] at h'
  rw [h']
  field_simp

/-- Near `x = 1⁺`, `P^{-m}_ν` (`m ≥ 0`) is positive and `O((x - 1)^{1/2}(x+1)^{-1/2})`. -/
theorem lzero_assocP_near_one (ν : ℝ) {m : ℝ} (hm : 0 ≤ m) :
    ∃ s : ℝ, 1 < s ∧ ∃ K : ℝ, 0 < K ∧ ∀ x : ℝ, x ∈ Ioc 1 s → 0 < (associatedP ν (-m : ℝ) x).re ∧
      (x ^ 2 - 1) * (associatedP ν (-m : ℝ) x).re ^ 2 ≤ K * (x - 1) := by
  set g : ℝ → ℂ := fun x => regularizedGaussHG ((ν:ℂ) + 1) (-(ν:ℂ)) (1 - ((-m:ℝ):ℂ))
    ((1 - (x:ℂ)) / 2) with hg
  have h0c : (0:ℂ) ∈ cutPlane := mem_cutPlane_of_norm_lt_one (by simp)
  have hcont : ContinuousAt g 1 := by
    have h1 : ContinuousAt (fun x : ℝ => (1 - (x:ℂ)) / 2) 1 := by fun_prop
    have h2 : ((1:ℂ) - ((1:ℝ):ℂ)) / 2 = 0 := by simp
    have h3 := (analyticOnNhd_regularizedGaussHG ((ν:ℂ) + 1) (-(ν:ℂ)) (1 - ((-m:ℝ):ℂ)) 0
      h0c).continuousAt
    exact h3.comp_of_eq h1 h2
  have hc : ∀ k : ℕ, (1:ℂ) - ((-m:ℝ):ℂ) ≠ -(k:ℂ) := fun k h => by
    have := congrArg re h; simp at this; linarith [(k.cast_nonneg : (0:ℝ) ≤ k)]
  have hg1 : g 1 = ((Real.Gamma (1 + m))⁻¹ : ℝ) := by
    simp only [hg, ofReal_one, sub_self, zero_div]
    rw [regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ (by simp),
      regularizedGaussHGFun_eq_div_Gamma hc, ordinaryHypergeometric_zero,
      show (1:ℂ) - ((-m:ℝ):ℂ) = ((1 + m : ℝ) : ℂ) by push_cast; ring, Complex.Gamma_ofReal]
    push_cast; ring
  have hG := Real.Gamma_pos_of_pos (show 0 < 1 + m by linarith)
  have hre1 : 0 < (g 1).re := by rw [hg1, ofReal_re]; positivity
  have hev : ∀ᶠ x in 𝓝 (1:ℝ), 0 < (g x).re ∧ ‖g x‖ < ‖g 1‖ + 1 := by
    have t1 := (Complex.continuous_re.continuousAt.comp hcont).eventually (lt_mem_nhds
      (show (g 1).re / 2 < (g 1).re by linarith))
    have t2 := (continuous_norm.continuousAt.comp hcont).eventually (gt_mem_nhds
      (show ‖g 1‖ < ‖g 1‖ + 1 by linarith))
    filter_upwards [t1, t2] with x h1 h2
    exact ⟨by simp only [Function.comp] at h1; linarith, h2⟩
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp (nhdsWithin_le_nhds hev)
  have hu1 : (1:ℝ) < u := hu
  set M := ‖g 1‖ + 1 with hM
  have hM1 : 1 ≤ M := by have := norm_nonneg (g 1); linarith
  refine ⟨(1 + u) / 2, by linarith, ((1 + u) / 2 + 1) * M ^ 2, mul_pos (by linarith) (pow_pos (by linarith) 2), fun x hx => ?_⟩
  have hx1 : 1 < x := hx.1
  obtain ⟨hgr, hgn⟩ := hsub ⟨hx1, by linarith [hx.2]⟩
  set E := Real.exp ((-m) / 2 * (Real.log (x + 1) - Real.log (x - 1))) with hE
  have hrep : (associatedP ν (-m : ℝ) x).re = E * (g x).re := by
    simp only [associatedP, hg, hE]
    rw [show (x : ℂ) + 1 = ((x + 1 : ℝ) : ℂ) by push_cast; ring,
      show (x : ℂ) - 1 = ((x - 1 : ℝ) : ℂ) by push_cast; ring,
      ← ofReal_log (by linarith), ← ofReal_log (by linarith),
      show ((-m : ℝ) : ℂ) / 2 * ((Real.log (x + 1) : ℂ) - (Real.log (x - 1) : ℂ)) =
        (((-m) / 2 * (Real.log (x + 1) - Real.log (x - 1)) : ℝ) : ℂ) by push_cast; ring,
      ← ofReal_exp, re_ofReal_mul]
  have hE0 : 0 < E := Real.exp_pos _
  have hE1 : E ≤ 1 := by
    rw [hE, Real.exp_le_one_iff]
    have : Real.log (x - 1) ≤ Real.log (x + 1) := Real.log_le_log (by linarith) (by linarith)
    nlinarith
  refine ⟨by rw [hrep]; exact mul_pos hE0 hgr, ?_⟩
  rw [hrep]
  have hgb : (g x).re ^ 2 ≤ M ^ 2 := by
    have h1 := Complex.abs_re_le_norm (g x)
    have h2 : |(g x).re| ≤ M := h1.trans hgn.le
    nlinarith [abs_nonneg (g x).re, sq_abs (g x).re]
  have hE2 : E ^ 2 ≤ 1 := by nlinarith
  have hx2 : x + 1 ≤ (1 + u) / 2 + 1 := by linarith [hx.2]
  calc (x ^ 2 - 1) * (E * (g x).re) ^ 2 = (x - 1) * ((x + 1) * (E ^ 2 * (g x).re ^ 2)) := by ring
    _ ≤ (x - 1) * (((1 + u) / 2 + 1) * (1 * M ^ 2)) := by
        apply mul_le_mul_of_nonneg_left _ (by linarith)
        apply mul_le_mul hx2 (mul_le_mul hE2 hgb (sq_nonneg _) zero_le_one)
          (by positivity) (by positivity)
    _ = ((1 + u) / 2 + 1) * M ^ 2 * (x - 1) := by ring

/-- The Wronskian of the real parts of `𝑸^μ_ν` and `P^μ_ν` on `(1,∞)`: for real `ν, μ` and
`x > 1`, `(x²-1)(q f' - f q') = 1/Γ(ν-μ+1)` with `f = Re P^μ_ν`, `q = Re 𝑸^μ_ν`. -/
private lemma lzero_assocP_wronskian_re {ν μ x : ℝ} (hx : 1 < x) :
    (x ^ 2 - 1) * ((olverQ (ν : ℂ) (μ : ℂ) x).re * (deriv (associatedP (ν : ℂ) (μ : ℂ)) x).re -
      (associatedP (ν : ℂ) (μ : ℂ) x).re * (deriv (olverQ (ν : ℂ) (μ : ℂ)) x).re) =
      (Real.Gamma (ν - μ + 1))⁻¹ := by
  set P : ℂ → ℂ := associatedP (ν : ℂ) (μ : ℂ) with hP
  set Qc : ℂ → ℂ := olverQ (ν : ℂ) (μ : ℂ) with hQc
  set cA : ℝ := (Real.Gamma (ν - μ + 1))⁻¹ with hcA
  have h := olverQ_wronskian_pos (ν : ℂ) μ (z := x) (lzero_mem hx)
  have h2 : ODE.wronskian Qc P x = (cA : ℂ) / ((x : ℂ) ^ 2 - 1) := by
    rw [show ODE.wronskian Qc P x = -ODE.wronskian P Qc x by
      simp only [ODE.wronskian]; ring, h,
      show (ν : ℂ) - μ + 1 = ((ν - μ + 1 : ℝ) : ℂ) by push_cast; ring, Complex.Gamma_ofReal,
      hcA]
    push_cast; ring
  exact lzero_ext_wr hx (olverQ_real ν μ hx) (associatedP_real ν μ hx) h2

/-- Sign of `Re P^μ_ν` near `x = 1⁺`: some multiple `σ₁ Re P^μ_ν` is positive on an interval
`(1, t₁)`, and `σ₁/Γ(ν-μ+1) < 0` exactly when `P^μ_ν` has one zero in `(1,∞)`. -/
private lemma lzero_assocP_sign_near_one {ν μ : ℝ} (hν : -1/2 ≤ ν)
    (hA : (Real.Gamma (ν - μ + 1))⁻¹ ≠ 0) :
    ∃ σ₁ t₁ : ℝ, 1 < t₁ ∧ (∀ x ∈ Ioo 1 t₁, 0 < σ₁ * (associatedP (ν : ℂ) (μ : ℂ) x).re) ∧
      (σ₁ * (Real.Gamma (ν - μ + 1))⁻¹ < 0 ↔ AssociatedPOneZero ν μ) := by
  set P : ℂ → ℂ := associatedP (ν : ℂ) (μ : ℂ) with hP
  set Qc : ℂ → ℂ := olverQ (ν : ℂ) (μ : ℂ) with hQc
  set f : ℝ → ℝ := fun x => (P x).re with hf
  set f' : ℝ → ℝ := fun x => (deriv P x).re with hf'
  set q : ℝ → ℝ := fun x => (Qc x).re with hq
  set q' : ℝ → ℝ := fun x => (deriv Qc x).re with hq'
  have hfd : ∀ x, 1 < x → HasDerivAt f (f' x) x := fun x hx =>
    (associatedP_analytic (ν : ℂ) μ x (lzero_mem hx)).differentiableAt.hasDerivAt.real_of_complex
  set cA : ℝ := (Real.Gamma (ν - μ + 1))⁻¹ with hcA
  have hWA : ∀ x, 1 < x → (x ^ 2 - 1) * (q x * f' x - f x * q' x) = cA := fun x hx =>
    lzero_assocP_wronskian_re hx
  have hcA2 : 0 < cA ^ 2 := by positivity
  show ∃ σ₁ t₁ : ℝ, 1 < t₁ ∧ (∀ x ∈ Ioo 1 t₁, 0 < σ₁ * f x) ∧
    (σ₁ * cA < 0 ↔ AssociatedPOneZero ν μ)
  rcases le_or_gt μ 0 with hμ | hμ
  · obtain ⟨s, hs, K1, hK1, hv⟩ := lzero_assocP_near_one ν (m := -μ) (by linarith)
    have hcA0 : 0 < cA := inv_pos.mpr (Real.Gamma_pos_of_pos (by linarith))
    refine ⟨1, s, hs, fun x hx => ?_, ?_⟩
    · have := (hv x (Ioo_subset_Ioc_self hx)).1
      simp only [neg_neg] at this
      simpa [hf, hP] using this
    · rw [lzero_oneZero_iff]
      constructor
      · intro h; linarith
      · intro h; exact absurd h.1 (not_lt.mpr hμ)
  · obtain ⟨s, hs, K1, hK1, hv⟩ := lzero_assocP_near_one ν (m := μ) hμ.le
    set V : ℂ → ℂ := associatedP (ν : ℂ) (-(μ : ℂ)) with hV
    set v : ℝ → ℝ := fun x => (V x).re with hv_def
    set v' : ℝ → ℝ := fun x => (deriv V x).re with hv'_def
    have hvd : ∀ x, 1 < x → HasDerivAt v (v' x) x := fun x hx =>
      (associatedP_analytic (ν : ℂ) (-(μ : ℂ)) x
        (lzero_mem hx)).differentiableAt.hasDerivAt.real_of_complex
    have hVreal : ∀ x : ℝ, 1 < x → (V x).im = 0 := fun x hx => by
      have := associatedP_real ν (-μ) hx
      simpa [hV] using this
    have hv1 : ∀ x ∈ Ioc 1 s, 0 < v x ∧ (x ^ 2 - 1) * v x ^ 2 ≤ K1 * (x - 1) := by
      intro x hx
      have := hv x hx
      simpa [hv_def, hV] using this
    set cB : ℝ := -2 * Real.sin (μ * π) / π with hcB
    have hWB : ∀ x, 1 < x → (x ^ 2 - 1) * (v x * f' x - f x * v' x) = cB := by
      intro x hx
      have h := associated_wronskian_7 (ν : ℂ) μ (z := x) (lzero_mem hx)
      have h2 : ODE.wronskian V P x = (cB : ℂ) / ((x : ℂ) ^ 2 - 1) := by
        rw [h, hcB, show (μ : ℂ) * π = ((μ * π : ℝ) : ℂ) by push_cast; ring, ← ofReal_sin]
        have hp : (x : ℂ) ^ 2 - 1 ≠ 0 := by
          rw [show (x : ℂ) ^ 2 - 1 = ((x ^ 2 - 1 : ℝ) : ℂ) by push_cast; ring]
          exact ofReal_ne_zero.mpr (by nlinarith)
        have hp' : (1 : ℂ) - (x : ℂ) ^ 2 ≠ 0 := by
          rw [show (1 : ℂ) - (x : ℂ) ^ 2 = -((x : ℂ) ^ 2 - 1) by ring]; exact neg_ne_zero.mpr hp
        have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_pos.ne'
        push_cast
        field_simp
        ring
      exact lzero_ext_wr hx (hVreal x hx) (associatedP_real ν μ hx) h2
    by_cases hint : ∀ n : ℤ, μ ≠ n
    · -- nonintegral `μ`
      have hsin : Real.sin (μ * π) ≠ 0 := by
        have := lzero_sin_sign hint
        intro h; rw [h, mul_zero] at this; exact lt_irrefl _ this
      have hcB0 : cB ≠ 0 := by
        rw [hcB]; exact div_ne_zero (by simpa using hsin) Real.pi_pos.ne'
      obtain ⟨t, ht, hneg⟩ := lzero_ext_neg_near_one (f := fun x => cB * f x)
        (f' := fun x => cB * f' x) (v := v) (v' := v') (s := s) (K := K1) (c := cB ^ 2) hs hK1
        (by positivity) (fun x hx => (hfd x hx.1).const_mul cB) (fun x hx => hvd x hx.1)
        (fun x hx => (hv1 x hx).1) (fun x hx => (hv1 x hx).2)
        (fun x hx => by linear_combination cB * hWB x hx.1)
      refine ⟨-cB, t, ht.1, fun x hx => by have : cB * f x < 0 := hneg x hx; linarith, ?_⟩
      rw [lzero_oneZero_iff, hcB, ← hcA]
      have hπ := Real.pi_pos
      constructor
      · intro h
        refine ⟨hμ, hint, ?_⟩
        have : -(-2 * Real.sin (μ * π) / π) * cA = (2 / π) * (Real.sin (μ * π) * cA) := by ring
        rw [this] at h
        rcases mul_neg_iff.mp h with h | h
        · exact h.2
        · exact absurd h.1 (not_lt.mpr (by positivity))
      · rintro ⟨-, -, h⟩
        have : -(-2 * Real.sin (μ * π) / π) * cA = (2 / π) * (Real.sin (μ * π) * cA) := by ring
        rw [this]
        exact mul_neg_of_pos_of_neg (by positivity) h
    · -- integral `μ`: `P` is a multiple of `P^{-μ}` near `1`
      push Not at hint
      obtain ⟨n, hn⟩ := hint
      have hcB0 : cB = 0 := by
        rw [hcB, hn, Real.sin_int_mul_pi, mul_zero, zero_div]
      set cC : ℝ := (Real.Gamma (ν + μ + 1))⁻¹ with hcC
      have hcC0 : 0 < cC := inv_pos.mpr (Real.Gamma_pos_of_pos (by linarith))
      have hWC : ∀ x, 1 < x → (x ^ 2 - 1) * (q x * v' x - v x * q' x) = cC := by
        intro x hx
        have h := associated_wronskian_8 (ν : ℂ) μ (z := x) (lzero_mem hx)
        have h2 : ODE.wronskian Qc V x = (cC : ℂ) / ((x : ℂ) ^ 2 - 1) := by
          rw [show ODE.wronskian Qc V x = -ODE.wronskian V Qc x by
            simp only [ODE.wronskian]; ring, h,
            show (ν : ℂ) + μ + 1 = ((ν + μ + 1 : ℝ) : ℂ) by push_cast; ring,
            Complex.Gamma_ofReal, hcC]
          push_cast
          simp only [div_eq_mul_inv, mul_inv]
          ring
        exact lzero_ext_wr hx (olverQ_real ν μ hx) (hVreal x hx) h2
      set s' : ℝ := (1 + s) / 2 with hs'
      have hs'1 : 1 < s' := by linarith
      have hs's : s' < s := by linarith
      have hlam : ∀ x ∈ Ioo 1 s, f x / v x = f s' / v s' := by
        intro x hx
        refine lzero_const_of_deriv_zero (s := Ioo 1 s) ordConnected_Ioo
          (fun y hy => (hfd y hy.1).div (hvd y hy.1) (hv1 y (Ioo_subset_Ioc_self hy)).1.ne')
          (fun y hy => ?_) hx ⟨hs'1, hs's⟩
        have h := hWB y hy.1
        rw [hcB0] at h
        have hp : y ^ 2 - 1 ≠ 0 := by nlinarith [hy.1]
        have h' : v y * f' y - f y * v' y = 0 := by
          rcases mul_eq_zero.mp h with h | h
          · exact absurd h hp
          · exact h
        rw [show f' y * v y - f y * v' y = 0 by linarith, zero_div]
      set lam : ℝ := f s' / v s' with hlam_def
      have hfeq : ∀ x ∈ Ioo 1 s, f x = lam * v x := fun x hx => by
        have := hlam x hx
        have hv0 := (hv1 x (Ioo_subset_Ioc_self hx)).1
        rw [← this]; field_simp
      -- compare Wronskians at `s'`
      have hderiv : f' s' = lam * v' s' := by
        have h1 : HasDerivAt f (lam * v' s') s' := by
          refine ((hvd s' hs'1).const_mul lam).congr_of_eventuallyEq ?_
          filter_upwards [Ioo_mem_nhds hs'1 hs's] with y hy using hfeq y hy
        exact (hfd s' hs'1).unique h1
      have hrel : cA = lam * cC := by
        rw [← hWA s' hs'1, ← hWC s' hs'1, hderiv, hfeq s' ⟨hs'1, hs's⟩]; ring
      have hpos : 0 < cA * lam := by
        have h : cA * lam * cC = cA ^ 2 := by rw [hrel]; ring
        have : 0 < cA * lam * cC := by rw [h]; exact hcA2
        exact pos_of_mul_pos_left this hcC0.le
      refine ⟨cA, s, hs, fun x hx => ?_, ?_⟩
      · rw [hfeq x hx, ← mul_assoc]
        exact mul_pos hpos (hv1 x (Ioo_subset_Ioc_self hx)).1
      · rw [lzero_oneZero_iff]
        constructor
        · intro h; nlinarith
        · rintro ⟨-, h, -⟩; exact absurd hn (h n)

/-- Exactly one or no exterior zeros, excluding an identically zero solution. -/
theorem associatedP_zero_count {ν μ : ℝ} (hν : -1/2 ≤ ν) (hnondeg : ∃ x : ℝ, 1 < x ∧ associatedP ν μ x ≠ 0) :
    Set.Finite {x : ℝ | 1 < x ∧ associatedP ν μ x=0} ∧ ({x : ℝ | 1 < x ∧ associatedP ν μ x=0}:Set ℝ).ncard=if AssociatedPOneZero ν μ then 1 else 0 := by
  set P : ℂ → ℂ := associatedP (ν : ℂ) (μ : ℂ) with hP
  set Qc : ℂ → ℂ := olverQ (ν : ℂ) (μ : ℂ) with hQc
  set f : ℝ → ℝ := fun x => (P x).re with hf
  set f' : ℝ → ℝ := fun x => (deriv P x).re with hf'
  set q : ℝ → ℝ := fun x => (Qc x).re with hq
  set q' : ℝ → ℝ := fun x => (deriv Qc x).re with hq'
  have hfd : ∀ x, 1 < x → HasDerivAt f (f' x) x := fun x hx =>
    (associatedP_analytic (ν : ℂ) μ x (lzero_mem hx)).differentiableAt.hasDerivAt.real_of_complex
  have hqd : ∀ x, 1 < x → HasDerivAt q (q' x) x := fun x hx =>
    (olverQ_analytic (ν : ℂ) μ x (lzero_mem hx)).differentiableAt.hasDerivAt.real_of_complex
  obtain ⟨hQpos, K, hK, hQb⟩ := lzero_olverQ_pos_bound hν μ
  set cA : ℝ := (Real.Gamma (ν - μ + 1))⁻¹ with hcA
  have hWA : ∀ x, 1 < x → (x ^ 2 - 1) * (q x * f' x - f x * q' x) = cA := fun x hx =>
    lzero_assocP_wronskian_re hx
  have hset : {x : ℝ | 1 < x ∧ associatedP ν μ x = 0} = {x | 1 < x ∧ f x = 0} := by
    ext x
    simp only [mem_ofPred_eq]
    constructor
    · rintro ⟨hx, h⟩; exact ⟨hx, by simp only [hf, hP, h, zero_re]⟩
    · rintro ⟨hx, h⟩; exact ⟨hx, Complex.ext h (associatedP_real ν μ hx)⟩
  rw [hset]
  by_cases hA : cA = 0
  · -- `P` is a multiple of `𝑸`, hence zero-free
    have hr : ∀ x, 1 < x → f x / q x = f 2 / q 2 := by
      intro x hx
      refine lzero_const_of_deriv_zero (s := Ioi 1) ordConnected_Ioi
        (fun y hy => (hfd y hy).div (hqd y hy) (hQpos y hy).ne') (fun y hy => ?_) hx
        (show (1:ℝ) < 2 by norm_num)
      have h := hWA y hy
      rw [hA] at h
      have hp : y ^ 2 - 1 ≠ 0 := by have : (1:ℝ) < y := hy; nlinarith
      have h' : q y * f' y - f y * q' y = 0 := by
        rcases mul_eq_zero.mp h with h | h
        · exact absurd h hp
        · exact h
      rw [show f' y * q y - f y * q' y = 0 by linarith, zero_div]
    obtain ⟨w, hw, hPw⟩ := hnondeg
    have hfw : f w ≠ 0 := fun h => hPw (Complex.ext h (associatedP_real ν μ hw))
    have hZ : {x | 1 < x ∧ f x = 0} = ∅ := by
      ext x
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
      intro hx h0
      have h1 := hr x hx
      have h2 := hr w hw
      rw [h0, zero_div] at h1
      rw [← h1, div_eq_zero_iff] at h2
      rcases h2 with h2 | h2
      · exact hfw h2
      · exact (hQpos w hw).ne' h2
    have hno : ¬ AssociatedPOneZero ν μ := by
      rw [lzero_oneZero_iff, ← hcA, hA, mul_zero]
      exact fun h => lt_irrefl _ h.2.2
    rw [hZ]
    simp [hno]
  -- sign at infinity
  have hcA2 : 0 < cA ^ 2 := by positivity
  obtain ⟨T, hT⟩ := lzero_ext_pos_atTop (f := fun x => cA * f x) (f' := fun x => cA * f' x)
    (u := q) (u' := q') (X := 2) (K := K) (c := cA ^ 2) (by norm_num) hK hcA2
    (fun x hx => (hfd x (by have : (2:ℝ) ≤ x := hx; linarith)).const_mul cA)
    (fun x hx => hqd x (by have : (2:ℝ) ≤ x := hx; linarith))
    (fun x hx => hQpos x (by have : (2:ℝ) ≤ x := hx; linarith))
    (fun x hx => hQb x hx)
    (fun x hx => by
      have h := hWA x (by have : (2:ℝ) ≤ x := hx; linarith)
      linear_combination cA * h)
  -- sign near one
  have hnear := lzero_assocP_sign_near_one hν hA
  obtain ⟨σ₁, t₁, ht₁, hl, hiff⟩ := hnear
  have hcount := lzero_ext_count (σ₂ := cA) ht₁ hfd hqd hQpos hA hWA hl
    (fun x hx => hT x hx)
  rw [hcount.2]
  refine ⟨hcount.1, ?_⟩
  exact if_congr hiff rfl rfl

end DLMF.Legendre

end
