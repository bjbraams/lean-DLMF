/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.NumberTheory.PrimeNumberTheorem
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Growth of the least common multiple of an initial interval

The eventual bound used in Andrews, Askey and Roy, *Special Functions*, §7.7.
It follows from the pinned prime number theorem through the existing adapter
`Chebyshev.psi_isEquivalent` and Mathlib's logarithmic lcm identity.
-/

@[expose] public section

open Filter Asymptotics
open scoped Topology

namespace Nat

/-- The least common multiple of `1,...,n` is eventually smaller than `b^n`
for every `b > exp 1`. Andrews–Askey–Roy, *Special Functions*, proof of Lemma 7.7.1
(synopsis AAR-7.7.1–7.7.5), where the base is three. -/
theorem eventually_lcmUpto_lt_pow {b : ℝ} (hb : Real.exp 1 < b) :
    ∀ᶠ n : ℕ in atTop, (lcmUpto n : ℝ) < b ^ n := by
  have hlog : (1 : ℝ) < Real.log b := by
    simpa only [Real.log_exp] using Real.log_lt_log (Real.exp_pos 1) hb
  have ht : Tendsto (Chebyshev.psi / fun x : ℝ => x) atTop (𝓝 1) :=
    (isEquivalent_iff_tendsto_one
      ((eventually_gt_atTop (0 : ℝ)).mono fun x hx => hx.ne')).mp
      Chebyshev.psi_isEquivalent
  have hevent : ∀ᶠ x : ℝ in atTop, Chebyshev.psi x < x * Real.log b := by
    filter_upwards [ht.eventually (gt_mem_nhds hlog), eventually_gt_atTop (0 : ℝ)]
      with x hx hx₀
    simpa only [mul_comm] using (div_lt_iff₀ hx₀).mp hx
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually hevent] with n hn
  have hp : 0 < (lcmUpto n : ℝ) := by exact_mod_cast lcmUpto_pos n
  have hb₀ : 0 < b := (Real.exp_pos 1).trans hb
  apply (Real.log_lt_log_iff hp (pow_pos hb₀ n)).mp
  rw [Real.log_pow]
  simpa only [Chebyshev.psi_eq_log_lcmUpto] using hn

/-- The eventual base-three bound sufficient for Beukers's linear forms.
Andrews–Askey–Roy, *Special Functions*, proof of Lemma 7.7.1
(synopsis AAR-7.7.1–7.7.5). -/
theorem eventually_lcmUpto_lt_three_pow :
    ∀ᶠ n : ℕ in atTop, (lcmUpto n : ℝ) < (3 : ℝ) ^ n :=
  eventually_lcmUpto_lt_pow Real.exp_one_lt_three

end Nat
