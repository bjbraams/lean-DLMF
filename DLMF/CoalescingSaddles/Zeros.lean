/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.CoalescingSaddles.Basic.AuxiliaryData
public import DLMF.CoalescingSaddles.CanonicalIntegrals

/-!
# Zeros of the canonical integrals: DLMF §36.7

DLMF §36.7 describes the zeros of the canonical integrals, mostly through approximate formulas
read off from the stationary-phase approximation and from numerical computation (Berry, Nye and
Wright 1979). The approximate loci 36.7.1, 36.7.2, 36.7.4–36.7.7 are definitions in
`DLMF.CoalescingSaddles.Basic.AuxiliaryData`; the words "approximately", "close to", "deep inside" carry no
error bound and are not formalized. This file proves the exact statements:

* the zeros of `Ψ₁` are those of `Ai(x/3^{1/3})` (§36.7(i), from 36.2.13);
* 36.7.3 has exactly one positive solution `ξ_n` for every `n` (DLMF: "the real solution");
* the exact part of 36.7.4, `3(π(2n - 1/2)/4)^{1/3} = 3(π/2)^{1/3}(n - 1/4)^{1/3}` (the decimal
  value `3.48734` is excluded as numerical);

and states (admitted) the two analytic claims with a precise meaning: all zeros of the Pearcey
integral have `y < 0` (§36.7(ii)), and the asymptotic form 36.7.8 of the zeros of `Ψ^{(E)}` in the
plane `z = 0`. Table 36.7.1 is excluded as numerical.
-/

@[expose] public noncomputable section

open Complex Set Filter Asymptotics
open scoped Real Topology

namespace DLMF.CoalescingSaddles

/-! ### §36.7(i): fold -/

/-- The zeros of the fold canonical integral are those of the Airy function:
`Ψ₁(x) = 0 ↔ Ai(x/3^{1/3}) = 0` (DLMF §36.7(i), from 36.2.13). -/
@[dlmf 36.7.i]
theorem cuspoidIntegral_one_eq_zero_iff (x : ℝ) :
    cuspoidIntegral 1 ![x] = 0 ↔ DLMF.Airy.airyAi ((x / (3 : ℝ) ^ (1 / 3 : ℝ) : ℝ) : ℂ) = 0 := by
  rw [cuspoidIntegral_one]
  have h3 : (((3 : ℝ) ^ (1 / 3 : ℝ) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) _).ne'
  have hc : 2 * (π : ℂ) / (((3 : ℝ) ^ (1 / 3 : ℝ) : ℝ) : ℂ) ≠ 0 :=
    div_ne_zero (mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero)) h3
  exact ⟨fun h => (mul_eq_zero.mp h).resolve_left hc, fun h => by rw [h, mul_zero]⟩

/-! ### §36.7(ii): cusp -/

/-- All zeros of the Pearcey integral `Ψ₂(x, y)` lie in the half-plane `y < 0`
(DLMF §36.7(ii); based on the computations of Berry, Nye and Wright (1979)). -/
@[dlmf 36.7.ii]
theorem cuspoidIntegral_two_ne_zero_of_nonneg {x y : ℝ} (hy : 0 ≤ y) :
    cuspoidIntegral 2 ![x, y] ≠ 0 := by
  sorry

/-- The left-hand side of 36.7.3 minus its right-hand side. -/
lemma s36b_xi_strictMonoOn (n : ℕ) :
    StrictMonoOn (fun ξ : ℝ => 3 * π * (8 * n + 5) / (9 + 8 * ξ) * ξ ^ (3 / 2 : ℝ) -
      27 / 16 * Real.sqrt (3 / 2) * (Real.log (1 / ξ) + 3 * Real.log (3 / 2))) (Ioi 0) := by
  intro a ha b hb hab
  simp only [mem_Ioi] at ha hb
  dsimp only
  have hA : 0 < 3 * π * (8 * (n : ℝ) + 5) := by positivity
  have hc : 0 < 27 / 16 * Real.sqrt (3 / 2) := by positivity
  -- `ξ^{3/2} = ξ √ξ`
  have hpow : ∀ ξ : ℝ, 0 < ξ → ξ ^ (3 / 2 : ℝ) = ξ * Real.sqrt ξ := fun ξ hξ => by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_one_add' hξ.le (by norm_num)]; norm_num
  rw [hpow a ha, hpow b hb]
  have hsa := Real.sqrt_pos.mpr ha
  have hs : Real.sqrt a < Real.sqrt b := Real.sqrt_lt_sqrt ha.le hab
  have h1 : a * Real.sqrt a / (9 + 8 * a) < b * Real.sqrt b / (9 + 8 * b) := by
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_pos ha hb, mul_lt_mul_of_pos_left hs (mul_pos ha hb)]
  have h2 : Real.log (1 / b) < Real.log (1 / a) :=
    Real.log_lt_log (by positivity) (one_div_lt_one_div_of_lt ha hab)
  have e1 : 3 * π * (8 * (n : ℝ) + 5) / (9 + 8 * a) * (a * Real.sqrt a) =
      3 * π * (8 * (n : ℝ) + 5) * (a * Real.sqrt a / (9 + 8 * a)) := by ring
  have e2 : 3 * π * (8 * (n : ℝ) + 5) / (9 + 8 * b) * (b * Real.sqrt b) =
      3 * π * (8 * (n : ℝ) + 5) * (b * Real.sqrt b / (9 + 8 * b)) := by ring
  rw [e1, e2]
  nlinarith [mul_lt_mul_of_pos_left h1 hA, mul_lt_mul_of_pos_left h2 hc]

/-- 36.7.3 has exactly one real solution `ξ_n > 0` for each `n` (DLMF: "`ξ_n` is the real
solution"); `ξ^{3/2}` and `ln(1/ξ)` require `ξ > 0`. The left side minus the right side is
strictly increasing on `(0, ∞)`, negative at `ξ = (3π(8n+5))^{-2}` and positive at `ξ = 4`. -/
@[dlmf 36.7.E3]
theorem existsUnique_cuspOuterZeroParam (n : ℕ) :
    ∃! ξ : ℝ, 0 < ξ ∧ IsCuspOuterZeroParam n ξ := by
  set A := 3 * π * (8 * (n : ℝ) + 5) with hAdef
  set c := 27 / 16 * Real.sqrt (3 / 2) with hcdef
  set f : ℝ → ℝ := fun ξ => A / (9 + 8 * ξ) * ξ ^ (3 / 2 : ℝ) -
    c * (Real.log (1 / ξ) + 3 * Real.log (3 / 2)) with hf
  have hmono : StrictMonoOn f (Ioi 0) := s36b_xi_strictMonoOn n
  have hiff : ∀ ξ, IsCuspOuterZeroParam n ξ ↔ f ξ = 0 := fun ξ => by
    simp only [IsCuspOuterZeroParam, hf, hAdef, hcdef, sub_eq_zero]
  simp_rw [hiff]
  have hA45 : 45 < A := by
    have := Real.pi_gt_three
    have : (0 : ℝ) ≤ n := n.cast_nonneg
    rw [hAdef]; nlinarith
  have hA : 0 < A := by linarith
  have hc1 : 1 ≤ c := by
    rw [hcdef]
    have : 1 ≤ Real.sqrt (3 / 2) := Real.one_le_sqrt.mpr (by norm_num)
    nlinarith
  -- the endpoints
  set a := (A ^ 2)⁻¹ with ha
  have ha0 : 0 < a := by positivity
  have ha1 : a ≤ 4 := by
    rw [ha]
    have : 1 ≤ A ^ 2 := by nlinarith
    calc (A ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ this
      _ ≤ 4 := by norm_num
  have hfa : f a < 0 := by
    simp only [hf]
    have hlog : 1 < Real.log (1 / a) := by
      rw [ha, one_div, inv_inv, Real.lt_log_iff_exp_lt (by positivity)]
      have := Real.exp_one_lt_d9
      nlinarith
    have hlog32 : 0 < Real.log (3 / 2) := Real.log_pos (by norm_num)
    have hpa : a ^ (3 / 2 : ℝ) ≤ a := by
      rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add ha0, Real.rpow_one]
      have : a ^ (1 / 2 : ℝ) ≤ 1 := Real.rpow_le_one ha0.le
        (by rw [ha]; exact inv_le_one_of_one_le₀ (by nlinarith)) (by norm_num)
      nlinarith
    have hterm : A / (9 + 8 * a) * a ^ (3 / 2 : ℝ) ≤ A * a := by
      have h9 : A / (9 + 8 * a) ≤ A := div_le_self hA.le (by linarith)
      have hp : 0 ≤ a ^ (3 / 2 : ℝ) := Real.rpow_nonneg ha0.le _
      calc A / (9 + 8 * a) * a ^ (3 / 2 : ℝ) ≤ A * a ^ (3 / 2 : ℝ) :=
            mul_le_mul_of_nonneg_right h9 hp
        _ ≤ A * a := mul_le_mul_of_nonneg_left hpa hA.le
    have hAa : A * a < 1 := by
      rw [ha, ← div_eq_mul_inv, div_lt_one (by positivity)]; nlinarith
    nlinarith
  have hfb : 0 < f 4 := by
    simp only [hf]
    have hneg : Real.log (1 / 4) + 3 * Real.log (3 / 2) < 0 := by
      rw [← Real.log_rpow (by norm_num), ← Real.log_mul (by norm_num) (by positivity)]
      exact Real.log_neg (by positivity) (by norm_num)
    have hpos : 0 < A / (9 + 8 * 4) * (4 : ℝ) ^ (3 / 2 : ℝ) := by positivity
    nlinarith
  -- continuity on `[a, 4]`
  have hcont : ContinuousOn f (Icc a 4) := by
    have hpos : ∀ ξ ∈ Icc a 4, 0 < ξ := fun ξ hξ => lt_of_lt_of_le ha0 hξ.1
    refine ContinuousOn.sub (ContinuousOn.mul (ContinuousOn.div continuousOn_const
      (continuousOn_const.add (continuousOn_const.mul continuousOn_id)) fun ξ hξ => by
        linarith [hpos ξ hξ]) (ContinuousOn.rpow_const continuousOn_id fun ξ hξ =>
          Or.inl (hpos ξ hξ).ne')) (continuousOn_const.mul (ContinuousOn.add ?_ continuousOn_const))
    exact ContinuousOn.log (continuousOn_const.div continuousOn_id fun ξ hξ => (hpos ξ hξ).ne')
      fun ξ hξ => (one_div_pos.mpr (hpos ξ hξ)).ne'
  obtain ⟨ξ, hξ, hfξ⟩ := intermediate_value_Icc ha1 hcont ⟨hfa.le, hfb.le⟩
  refine ⟨ξ, ⟨lt_of_lt_of_le ha0 hξ.1, hfξ⟩, fun η ⟨hη, hfη⟩ => ?_⟩
  exact hmono.injOn hη (lt_of_lt_of_le ha0 hξ.1) (hfη.trans hfξ.symm)

/-! ### §36.7(iii): elliptic umbilic -/

/-- The exact form of 36.7.4: `3(π(2n - 1/2)/4)^{1/3} = 3(π/2)^{1/3}(n - 1/4)^{1/3}` for
`n ≥ 1`; DLMF's decimal value `3(π/2)^{1/3} = 3.48734…` is excluded as numerical. -/
@[dlmf 36.7.E4]
theorem ellipticUmbilicRingPlane_eq (n : ℕ) (hn : 1 ≤ n) :
    ellipticUmbilicRingPlane n = 3 * (π / 2) ^ (1 / 3 : ℝ) * ((n : ℝ) - 1 / 4) ^ (1 / 3 : ℝ) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rw [ellipticUmbilicRingPlane, show π / 4 * (2 * (n : ℝ) - 1 / 2) = π / 2 * ((n : ℝ) - 1 / 4) by
    ring, Real.mul_rpow (by positivity) (by linarith)]
  ring

/-- The zeros of `Ψ^{(E)}` in the plane `z = 0` (the zeros of 36.2.20) along a ray
`(x, y) = (r cos θ, r sin θ)` with `sin(3θ/2) ≠ 0`: for each large `n` there is a zero at radius
`r_n = 3((2n-1)π/(4|sin(3θ/2)|))^{2/3}(1 + O(1/n))` (DLMF 36.7.8, stated as the existence of such a
sequence of zeros). -/
@[dlmf 36.7.E8]
theorem ellipticUmbilicIntegral_plane_zeros (θ : ℝ) (hθ : Real.sin (3 / 2 * θ) ≠ 0) :
    ∃ r : ℕ → ℝ, (∀ᶠ n in atTop, 0 < r n ∧
        ellipticUmbilicIntegral (r n * Real.cos θ) (r n * Real.sin θ) 0 = 0) ∧
      (fun n => r n / ellipticUmbilicPlaneZeroRadius n θ - 1) =O[atTop]
        (fun n : ℕ => (1 : ℝ) / n) := by
  sorry

end DLMF.CoalescingSaddles
