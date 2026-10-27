/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Hypergeometric.ConnectionFormulas
public import DLMF.Gamma.RecipGammaDeriv

/-!
# Logarithmic connection formulas without pole restrictions (DLMF 15.8.9–15.8.11)

The statements `logarithmic_connection_one_sub` (15.8.10),
`logarithmic_connection_one_div_one_sub` (15.8.9) and `logarithmic_connection_one_sub_recip`
(15.8.11) in `DLMF.Hypergeometric.ConnectionFormulas` assume nonintegrality of the parameters,
because they contain products `ψ(x) / Γ(y)` in which Mathlib's totalized digamma would be
evaluated at a pole. Here every such product is rewritten through the entire function
`recipGammaDeriv 1 = (1/Γ)'`, using `ψ(x+n)/Γ(x) = -(x)_n (1/Γ)'(x+n)` and
`ψ(x)/Γ(x) = -(1/Γ)'(x)`, and the formulas are proved for all parameters.

The proofs repeat the parameter differentiation of the original ones with the everywhere-valid
`hasDerivAt_recip_Gamma'`. The derivatives of the Pochhammer symbols are handled by the
pole-free identities `recip_Gamma_mul_deriv_poch` and `recip_Gamma_mul_deriv_poch_one_sub`,
obtained by differentiating `(x)_n / Γ(x+n) = 1/Γ(x)` and `(1-y)_n / Γ(y) = (-1)^n / Γ(y-n)`.
-/

@[expose] public section

open Complex Filter
open scoped Real Topology

noncomputable section

namespace DLMF.Hypergeometric

open DLMF.Gamma

/-- `(x)_n' / Γ(x) = (x)_n ((1/Γ)'(x) - (x)_n (1/Γ)'(x+n))`, valid for every `x`. -/
theorem recip_Gamma_mul_deriv_poch (x : ℂ) (n : ℕ) :
    (Gamma x)⁻¹ * deriv (fun y => poch y n) x =
      poch x n * (recipGammaDeriv 1 x - poch x n * recipGammaDeriv 1 (x + n)) := by
  have hp : HasDerivAt (fun y => poch y n) (deriv (fun y => poch y n) x) x :=
    ((Polynomial.differentiable (ascPochhammer ℂ n)) x).hasDerivAt
  have hg := (hasDerivAt_recip_Gamma' (x + n)).comp x ((hasDerivAt_id x).add_const (n : ℂ))
  have h := hp.mul hg
  have h' : HasDerivAt (fun y => (Gamma y)⁻¹) _ x := h.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun y => by
      simp only [Pi.mul_apply, Function.comp_apply, _root_.id]
      exact (poch_mul_recip_Gamma_add_nat y n).symm)
  have hu := (hasDerivAt_recip_Gamma' x).unique h'
  simp only [_root_.id, Function.comp_apply] at hu
  rw [← poch_mul_recip_Gamma_add_nat x n]
  linear_combination (-poch x n) * hu

/-- `(1-y)_n / Γ(y) = (-1)^n / Γ(y-n)`, valid for every `y`. -/
theorem recip_Gamma_mul_poch_one_sub (y : ℂ) (n : ℕ) :
    (Gamma y)⁻¹ * poch (1 - y) n = (-1) ^ n * (Gamma (y - n))⁻¹ := by
  induction n with
  | zero => simp [poch_zero]
  | succ n ih =>
    have h := one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (y - (n + 1 : ℕ))
    rw [show y - ((n + 1 : ℕ) : ℂ) + 1 = y - n by push_cast; ring] at h
    rw [poch_succ, ← mul_assoc, ih, h]
    push_cast
    ring

/-- `(1-y)_n' / Γ(y) = (1-y)_n (1/Γ)'(y) - (-1)^n (1/Γ)'(y-n)`, where `'` on the Pochhammer
symbol is the derivative in its base at `1 - y`; valid for every `y`. -/
theorem recip_Gamma_mul_deriv_poch_one_sub (y : ℂ) (n : ℕ) :
    (Gamma y)⁻¹ * deriv (fun x => poch x n) (1 - y) =
      poch (1 - y) n * recipGammaDeriv 1 y - (-1) ^ n * recipGammaDeriv 1 (y - n) := by
  have hp : HasDerivAt (fun x => poch x n) (deriv (fun x => poch x n) (1 - y)) (1 - y) :=
    ((Polynomial.differentiable (ascPochhammer ℂ n)) (1 - y)).hasDerivAt
  have hl : HasDerivAt (fun x : ℂ => 1 - x) (-1) y := by
    simpa using (hasDerivAt_id y).const_sub (1 : ℂ)
  have h := (hasDerivAt_recip_Gamma' y).mul (hp.comp y hl)
  have hr := ((hasDerivAt_recip_Gamma' (y - n)).comp y
    ((hasDerivAt_id y).sub_const (n : ℂ))).const_mul
    ((-1 : ℂ) ^ n)
  have h' : HasDerivAt (fun x => (-1 : ℂ) ^ n * (Gamma (x - n))⁻¹) _ y := h.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun x => by
      simp only [Pi.mul_apply, Function.comp_apply]
      exact (recip_Gamma_mul_poch_one_sub x n).symm)
  have hu := hr.unique h'
  simp only [Function.comp_apply] at hu
  linear_combination hu

/-- DLMF 15.8.10 with `ψ(a+k+m)/(Γ(a)Γ(b))` and `ψ(b+k+m)/(Γ(a)Γ(b))` written as
`-(a)_{k+m} (1/Γ)'(a+k+m)/Γ(b)` and `-(b)_{k+m} (1/Γ)'(b+k+m)/Γ(a)`. Stronger than DLMF:
no restriction on `a` and `b`; `logarithmic_connection_one_sub` is the digamma form. -/
@[dlmf 15.8.E10]
theorem logarithmic_connection_one_sub_recipGamma {a b z : ℂ} (m : ℕ)
    (hz : ‖z‖ < 1) (hw : ‖1 - z‖ < 1) :
    regularizedGaussHGFun a b (a + b + m) z =
      (1 / (Gamma (a + m) * Gamma (b + m))) *
        (∑ k ∈ Finset.range m, poch a k * poch b k * ((m - k - 1).factorial : ℂ)/
          (k.factorial : ℂ) * (z - 1) ^ k) -
      (z - 1) ^ m * ∑' k : ℕ,
        poch (a + m) k * poch (b + m) k / ((k.factorial : ℂ) * ((k + m).factorial : ℂ)) *
          (1 - z) ^ k * ((Gamma a * Gamma b)⁻¹ *
              (log (1 - z) - digamma (k + 1) - digamma (k + m + 1)) -
            (Gamma b)⁻¹ * (poch a (k + m) * recipGammaDeriv 1 (a + k + m)) -
            (Gamma a)⁻¹ * (poch b (k + m) * recipGammaDeriv 1 (b + k + m))) := by
  set w := 1 - z with hwdef
  set c₀ := a + b + m with hc₀
  set D : ℂ → ℂ := deriv (fun y : ℂ => (Gamma y)⁻¹) with hD
  set pd : ℕ → ℂ → ℂ := fun n => deriv (fun y => poch y n) with hpd
  have hpdd : ∀ (n : ℕ) (x : ℂ), HasDerivAt (fun y => poch y n) (pd n x) x := fun n x =>
    ((Polynomial.differentiable (ascPochhammer ℂ n)) x).hasDerivAt
  have hw0 : w ≠ 0 := by
    intro h; rw [hwdef, sub_eq_zero] at h; rw [← h] at hz; simp at hz
  -- the connection formula for every `c`
  have hconn : ∀ c : ℂ, sin (Real.pi * (c - a - b)) / Real.pi * regularizedGaussHGFun a b c z =
      regularizedGaussHGFun a b (a + b - c + 1) w * ((Gamma (c - a))⁻¹ * (Gamma (c - b))⁻¹) -
        (Gamma a * Gamma b)⁻¹ * (w ^ (c - a - b) * regularizedGaussHGFun (c - a) (c - b)
          (c - a - b + 1) w) := by
    intro c
    rw [regularized_connection_one_sub a b c hz hw]
    simp only [div_eq_mul_inv, mul_inv]
    ring
  -- derivative of the left side
  have hπ : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hRc := (analyticOnNhd_regularizedGaussHGFun_c a b hz c₀ (Set.mem_univ _)).differentiableAt
  have hsin : HasDerivAt (fun c : ℂ => sin (Real.pi * (c - a - b)) / Real.pi)
      (cos (Real.pi * (c₀ - a - b)) * (Real.pi * 1) / Real.pi) c₀ :=
    ((((hasDerivAt_id c₀).sub_const a).sub_const b).const_mul (Real.pi : ℂ)).csin.div_const _
  have hm1 : c₀ - a - b = m := by rw [hc₀]; ring
  have hL := hsin.mul hRc.hasDerivAt
  have hcos : cos ((m : ℂ) * Real.pi) = (-1) ^ m := by
    rw [show ((m : ℂ) * Real.pi) = ((m * Real.pi : ℝ) : ℂ) by push_cast; ring, ← ofReal_cos,
      Real.cos_nat_mul_pi]
    push_cast; ring
  rw [hm1, mul_comm (Real.pi : ℂ) (m : ℂ), hcos, Complex.sin_nat_mul_pi, zero_div, zero_mul,
    add_zero, mul_one, mul_div_cancel_right₀ _ hπ] at hL
  have hwn : ‖w‖ < 1 := hw
  -- the first series and its derivative
  set S : ℂ → ℂ := fun c => regularizedGaussHGFun a b (a + b - c + 1) w with hSdef
  have hSa : DifferentiableAt ℂ S c₀ :=
    (analyticOnNhd_regularizedGaussHGFun_comp (A := fun _ => a) (B := fun _ => b)
      (C := fun c => a + b - c + 1) (differentiable_const _) (differentiable_const _)
      (by fun_prop) hwn c₀ (Set.mem_univ _)).differentiableAt
  have hSsum := hasSum_deriv_regularizedGaussHGFun_comp (A := fun _ => a) (B := fun _ => b)
    (C := fun c => a + b - c + 1) (differentiable_const _) (differentiable_const _)
    (by fun_prop) hwn c₀
  have htd : ∀ n : ℕ, deriv (fun c => poch ((fun _ => a) c) n * poch ((fun _ => b) c) n * w ^ n /
      n.factorial * (Gamma ((fun c => a + b - c + 1) c + n))⁻¹) c₀ =
      -(poch a n * poch b n * w ^ n / n.factorial) * D (1 - m + n) := by
    intro n
    have h1 : HasDerivAt (fun c : ℂ => a + b - c + 1 + n) (-1) c₀ := by
      simpa using (((hasDerivAt_id c₀).const_sub (a + b)).add_const 1).add_const (n : ℂ)
    have h2 := ((hasDerivAt_recip_Gamma_any (a + b - c₀ + 1 + n)).comp c₀ h1).const_mul
      (poch a n * poch b n * w ^ n / n.factorial)
    rw [show a + b - c₀ + 1 + n = 1 - m + n by rw [hc₀]; ring] at h2
    rw [show (fun c => poch ((fun _ => a) c) n * poch ((fun _ => b) c) n * w ^ n /
      n.factorial * (Gamma ((fun c => a + b - c + 1) c + n))⁻¹) = (fun c =>
      poch a n * poch b n * w ^ n / n.factorial *
        ((fun y => (Gamma y)⁻¹) ∘ fun c : ℂ => a + b - c + 1 + n) c) from rfl, h2.deriv, hD]
    ring
  -- the second series and its derivative
  set Q : ℂ → ℂ := fun c => regularizedGaussHGFun (c - a) (c - b) (c - a - b + 1) w with hQdef
  have hQa : DifferentiableAt ℂ Q c₀ :=
    (analyticOnNhd_regularizedGaussHGFun_comp (A := fun c => c - a) (B := fun c => c - b)
      (C := fun c => c - a - b + 1) (by fun_prop) (by fun_prop) (by fun_prop) hwn c₀
      (Set.mem_univ _)).differentiableAt
  have hQsum := hasSum_deriv_regularizedGaussHGFun_comp (A := fun c => c - a) (B := fun c => c - b)
    (C := fun c => c - a - b + 1) (by fun_prop) (by fun_prop) (by fun_prop) hwn c₀
  have hmn : ∀ n : ℕ, ∀ j : ℕ, (m : ℂ) + 1 + n ≠ -(j : ℂ) := by
    intro n j hj
    have := congrArg re hj
    simp at this
    linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j), (Nat.cast_nonneg m : (0 : ℝ) ≤ m),
      (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have e1 : c₀ - a = b + m := by rw [hc₀]; ring
  have e2 : c₀ - b = a + m := by rw [hc₀]; ring
  have hqd : ∀ n : ℕ, deriv (fun c => poch ((fun c => c - a) c) n * poch ((fun c => c - b) c) n *
      w ^ n / n.factorial * (Gamma ((fun c => c - a - b + 1) c + n))⁻¹) c₀ =
      (pd n (b + m) * poch (a + m) n * (Gamma (m + 1 + n))⁻¹ +
        poch (b + m) n * pd n (a + m) * (Gamma (m + 1 + n))⁻¹ +
        poch (b + m) n * poch (a + m) n * recipGammaDeriv 1 (m + 1 + n)) * w ^ n / n.factorial := by
    intro n
    have e3 : c₀ - a - b + 1 + n = m + 1 + n := by rw [hc₀]; ring
    have hp1' : HasDerivAt (fun y => poch y n) (pd n (b + m)) (c₀ - a) := by
      rw [e1]; exact hpdd n _
    have hp2' : HasDerivAt (fun y => poch y n) (pd n (a + m)) (c₀ - b) := by
      rw [e2]; exact hpdd n _
    have hg' : HasDerivAt (fun y => (Gamma y)⁻¹) (recipGammaDeriv 1 (m + 1 + n))
        (c₀ - a - b + 1 + n) := by rw [e3]; exact hasDerivAt_recip_Gamma' _
    have hl1 : HasDerivAt (fun c : ℂ => c - a) 1 c₀ := (hasDerivAt_id c₀).sub_const a
    have hl2 : HasDerivAt (fun c : ℂ => c - b) 1 c₀ := (hasDerivAt_id c₀).sub_const b
    have hl3 : HasDerivAt (fun c : ℂ => c - a - b + 1 + n) 1 c₀ :=
      ((((hasDerivAt_id c₀).sub_const a).sub_const b).add_const 1).add_const _
    have h := ((((hp1'.comp c₀ hl1).mul (hp2'.comp c₀ hl2)).mul_const (w ^ n)).div_const
      (n.factorial : ℂ)).mul (hg'.comp c₀ hl3)
    have h' : HasDerivAt (fun c => ((fun y => poch y n) ∘ fun c : ℂ => c - a) c *
        ((fun y => poch y n) ∘ fun c : ℂ => c - b) c * w ^ n / n.factorial *
        ((fun y => (Gamma y)⁻¹) ∘ fun c : ℂ => c - a - b + 1 + n) c) _ c₀ := h
    rw [show (fun c => poch ((fun c => c - a) c) n * poch ((fun c => c - b) c) n *
      w ^ n / n.factorial * (Gamma ((fun c => c - a - b + 1) c + n))⁻¹) =
      fun c => ((fun y => poch y n) ∘ fun c : ℂ => c - a) c *
        ((fun y => poch y n) ∘ fun c : ℂ => c - b) c *
        w ^ n / n.factorial * ((fun y => (Gamma y)⁻¹) ∘ fun c : ℂ => c - a - b + 1 + n) c from rfl,
      h'.deriv]
    simp only [Pi.mul_apply, Function.comp_apply, e1, e2]
    ring_nf
  -- derivative of the right side of the connection formula
  have hG1 : HasDerivAt (fun c : ℂ => (Gamma (c - a))⁻¹) (recipGammaDeriv 1 (b + m)) c₀ := by
    have h1 : HasDerivAt (fun y => (Gamma y)⁻¹) (recipGammaDeriv 1 (b + m)) (c₀ - a) := by
      rw [e1]; exact hasDerivAt_recip_Gamma' _
    simpa [Function.comp_def] using h1.comp c₀ ((hasDerivAt_id c₀).sub_const a)
  have hG2 : HasDerivAt (fun c : ℂ => (Gamma (c - b))⁻¹) (recipGammaDeriv 1 (a + m)) c₀ := by
    have h1 : HasDerivAt (fun y => (Gamma y)⁻¹) (recipGammaDeriv 1 (a + m)) (c₀ - b) := by
      rw [e2]; exact hasDerivAt_recip_Gamma' _
    simpa [Function.comp_def] using h1.comp c₀ ((hasDerivAt_id c₀).sub_const b)
  have hP : HasDerivAt (fun c : ℂ => w ^ (c - a - b)) (w ^ (m : ℂ) * log w * 1) c₀ := by
    have h := (((hasDerivAt_id c₀).sub_const a).sub_const b).const_cpow (c := w) (Or.inl hw0)
    rw [show _root_.id c₀ - a - b = (m : ℂ) by simp only [_root_.id]; rw [hc₀]; ring] at h
    exact h
  have hR := (hSa.hasDerivAt.mul (hG1.mul hG2)).sub
    ((hP.mul hQa.hasDerivAt).const_mul ((Gamma a * Gamma b)⁻¹))
  have hfun : (fun c => sin (Real.pi * (c - a - b)) / Real.pi * regularizedGaussHGFun a b c z) =
      fun c => S c * ((Gamma (c - a))⁻¹ * (Gamma (c - b))⁻¹) -
        (Gamma a * Gamma b)⁻¹ * (w ^ (c - a - b) * Q c) := funext hconn
  have hL' : HasDerivAt (fun c => sin (Real.pi * (c - a - b)) / Real.pi *
      regularizedGaussHGFun a b c z) ((-1) ^ m * regularizedGaussHGFun a b c₀ z) c₀ := hL
  rw [hfun] at hL'
  have hkey := hL'.unique hR
  simp only [Pi.mul_apply] at hkey
  rw [hm1, e1, e2, cpow_natCast] at hkey
  -- the two series at `c₀`
  set P : ℂ := poch a m * poch b m with hPdef
  set q : ℕ → ℂ := fun k => poch (b + m) k * poch (a + m) k * w ^ k / k.factorial *
    (Gamma (m + 1 + k))⁻¹ with hq
  set sS : ℕ → ℂ := fun n => poch a n * poch b n * w ^ n / n.factorial *
    (Gamma (1 - m + n))⁻¹ with hsS
  have hS0 : HasSum sS (S c₀) := by
    have h := (summable_regularizedGaussHGFun_term a b (1 - m) hwn).hasSum
    rw [← regularizedGaussHGFun_eq_tsum] at h
    convert h using 1
    simp only [hSdef]; congr 1; rw [hc₀]; ring
  have hQ0 : HasSum q (Q c₀) := by
    have h := (summable_regularizedGaussHGFun_term (b + m) (a + m) (m + 1) hwn).hasSum
    rw [← regularizedGaussHGFun_eq_tsum] at h
    convert h using 1
    simp only [hQdef]; rw [hm1, e1, e2]
  have hGk : ∀ k : ℕ, Gamma ((m : ℂ) + 1 + k) = ((k + m).factorial : ℂ) := by
    intro k
    rw [show (m : ℂ) + 1 + k = ((k + m : ℕ) : ℂ) + 1 by push_cast; ring, Gamma_nat_eq_factorial]
  have hG1k : ∀ k : ℕ, Gamma (1 - (m : ℂ) + ((k + m : ℕ) : ℂ)) = (k.factorial : ℂ) := by
    intro k
    rw [show 1 - (m : ℂ) + ((k + m : ℕ) : ℂ) = (k : ℂ) + 1 by push_cast; ring,
      Gamma_nat_eq_factorial]
  have hsS_shift : ∀ k : ℕ, sS (k + m) = P * w ^ m * q k := by
    intro k
    simp only [hsS, hq, hPdef, hGk, hG1k]
    rw [add_comm k m, poch_add a m k, poch_add b m k, pow_add, add_comm m k]
    have hk : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
    have hkm : ((k + m).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    field_simp
  have hpole : ∀ n : ℕ, n < m → 1 - (m : ℂ) + n = -((m - 1 - n : ℕ) : ℂ) := by
    intro n hn
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
  have hsS_low : ∀ n ∈ Finset.range m, sS n = 0 := by
    intro n hn
    rw [Finset.mem_range] at hn
    simp only [hsS, hpole n hn, Gamma_neg_nat_eq_zero, inv_zero, mul_zero]
  have hS0eq : S c₀ = P * w ^ m * Q c₀ := by
    have h := (hasSum_nat_add_iff' m).mpr hS0
    rw [Finset.sum_eq_zero hsS_low, sub_zero] at h
    exact h.unique ((hQ0.mul_left (P * w ^ m)).congr_fun fun k => (hsS_shift k).symm ▸ rfl)
  -- derivatives of the first series
  set dt : ℕ → ℂ := fun n => deriv (fun c => poch ((fun _ => a) c) n * poch ((fun _ => b) c) n *
      w ^ n / n.factorial * (Gamma ((fun c => a + b - c + 1) c + n))⁻¹) c₀ with hdt
  have hdt_shift : ∀ k : ℕ, dt (k + m) = P * w ^ m * q k * digamma (k + 1) := by
    intro k
    simp only [hdt]
    have hk1 : ∀ j : ℕ, (k : ℂ) + 1 ≠ -(j : ℂ) := by
      intro j hj
      have := congrArg re hj
      simp at this
      linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j), (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    rw [htd, show 1 - (m : ℂ) + ((k + m : ℕ) : ℂ) = (k : ℂ) + 1 by push_cast; ring, hD,
      deriv_recip_Gamma_eq hk1, ← hsS_shift k]
    simp only [hsS, show 1 - (m : ℂ) + ((k + m : ℕ) : ℂ) = (k : ℂ) + 1 by push_cast; ring]
    ring
  have hdt_low : ∀ n : ℕ, n < m → dt n =
      -(poch a n * poch b n * w ^ n / n.factorial) *
        ((-1) ^ (m - 1 - n) * ((m - 1 - n).factorial : ℂ)) := by
    intro n hn
    simp only [hdt]
    rw [htd, hpole n hn, hD, deriv_recip_Gamma_neg_nat]
  have hSshift := (hasSum_nat_add_iff' m).mpr hSsum
  set G : ℂ := (Gamma (b + m))⁻¹ * (Gamma (a + m))⁻¹ with hGdef
  set G' : ℂ := recipGammaDeriv 1 (b + m) * (Gamma (a + m))⁻¹ +
    (Gamma (b + m))⁻¹ * recipGammaDeriv 1 (a + m) with hG'def
  set K : ℂ := (Gamma a * Gamma b)⁻¹ with hK
  set t : ℕ → ℂ := fun k => q k * (K * (log w - digamma (k + 1) - digamma (m + 1 + k)) -
    (Gamma b)⁻¹ * (poch a m * poch (a + m) k * recipGammaDeriv 1 (a + m + k)) -
    (Gamma a)⁻¹ * (poch b m * poch (b + m) k * recipGammaDeriv 1 (b + m + k))) with ht
  have hEsum : HasSum (fun k => w ^ m * t k)
      ((K * w ^ m * log w - P * G' * w ^ m) * Q c₀ + K * w ^ m * deriv Q c₀ -
        G * (deriv S c₀ - ∑ i ∈ Finset.range m, dt i)) := by
    have h := ((hQ0.mul_left (K * w ^ m * log w - P * G' * w ^ m)).add
      (hQsum.mul_left (K * w ^ m))).sub (hSshift.mul_left G)
    convert h using 1
    funext k
    rw [hqd k, hdt_shift k]
    have F1 : (Gamma (a + m))⁻¹ * pd k (a + m) = poch (a + m) k * (recipGammaDeriv 1 (a + m) -
        poch (a + m) k * recipGammaDeriv 1 (a + m + k)) := recip_Gamma_mul_deriv_poch (a + m) k
    have F2 : (Gamma (b + m))⁻¹ * pd k (b + m) = poch (b + m) k * (recipGammaDeriv 1 (b + m) -
        poch (b + m) k * recipGammaDeriv 1 (b + m + k)) := recip_Gamma_mul_deriv_poch (b + m) k
    have F3 := poch_mul_recip_Gamma_add_nat a m
    have F4 := poch_mul_recip_Gamma_add_nat b m
    have F7 := recipGammaDeriv_one_eq (hmn k)
    simp only [ht, hK, hG'def, hGdef, hPdef, hq, mul_inv, F7]
    rw [← F3, ← F4]
    linear_combination (-w ^ m * (Gamma (a + m))⁻¹ *
        (poch a m * poch b m * poch (a + m) k * w ^ k / k.factorial *
        (Gamma (m + 1 + k))⁻¹)) * F2 +
      (-w ^ m * (Gamma (b + m))⁻¹ * (poch a m * poch b m * poch (b + m) k * w ^ k / k.factorial *
        (Gamma (m + 1 + k))⁻¹)) * F1
  have hEval := hEsum.tsum_eq
  rw [tsum_mul_left] at hEval
  have htsum : (∑' k : ℕ, poch (a + m) k * poch (b + m) k /
      ((k.factorial : ℂ) * ((k + m).factorial : ℂ)) * w ^ k * ((Gamma a * Gamma b)⁻¹ *
        (log w - digamma (k + 1) - digamma (k + m + 1)) -
      (Gamma b)⁻¹ * (poch a (k + m) * recipGammaDeriv 1 (a + k + m)) -
      (Gamma a)⁻¹ * (poch b (k + m) * recipGammaDeriv 1 (b + k + m)))) = ∑' k : ℕ, t k := by
    refine tsum_congr fun k => ?_
    simp only [ht, hq, hGk, hK]
    rw [show (k : ℂ) + m + 1 = m + 1 + k by ring, show a + k + m = a + m + k by ring,
      show b + k + m = b + m + k by ring, add_comm k m, poch_add a m k, poch_add b m k]
    ring_nf
  rw [htsum]
  set T := ∑' k : ℕ, t k with hT
  have hzw : (z - 1) ^ m = (-1) ^ m * w ^ m := by
    rw [← mul_pow, hwdef]; ring
  have hσ : ((-1 : ℂ) ^ m) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
  have hFin : (-1 : ℂ) ^ m * ∑ i ∈ Finset.range m, dt i = ∑ k ∈ Finset.range m,
      poch a k * poch b k * ((m - k - 1).factorial : ℂ) / (k.factorial : ℂ) * (z - 1) ^ k := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_range] at hk
    rw [hdt_low k hk, show m - 1 - k = m - k - 1 by omega]
    obtain ⟨j, hj⟩ : ∃ j, m = k + 1 + j := ⟨m - k - 1, by omega⟩
    have hzk : (z - 1) ^ k = (-1) ^ k * w ^ k := by
      rw [show z - 1 = -w by rw [hwdef]; ring, neg_pow]
    rw [show m - k - 1 = j by omega, hzk, hj]
    have hj2 : ((-1 : ℂ) ^ j) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
    linear_combination
      (poch a k * poch b k * w ^ k / k.factorial * (j.factorial : ℂ) * (-1) ^ k) * hj2
  rw [one_div, mul_inv]
  set R := regularizedGaussHGFun a b c₀ z
  linear_combination (-R) * hσ + (-1 : ℂ) ^ m * hkey + (-1 : ℂ) ^ m * G' * hS0eq +
    (-1 : ℂ) ^ m * hEval + G * hFin + T * hzw

/-- DLMF 15.8.9 with `ψ(a+k+m)/Γ(a)` and `ψ(c-a+k)/Γ(c-a-m)` written as
`-(a)_{k+m} (1/Γ)'(a+k+m)` and `-(c-a-m)_{k+m} (1/Γ)'(c-a+k)`. Stronger than DLMF: no
restriction on `a` and `c`; `logarithmic_connection_one_div_one_sub` is the digamma form. -/
@[dlmf 15.8.E9]
theorem logarithmic_connection_one_div_one_sub_recipGamma {a c z : ℂ} (m : ℕ)
    (hz : ‖z‖ < 1) (hw : 1 < ‖1 - z‖) :
    regularizedGaussHGFun a (a + m) c z =
      (1 - z) ^ (-a) / (Gamma (a + m) * Gamma (c - a)) *
        (∑ k ∈ Finset.range m, poch a k * poch (c - a - m) k * ((m - k - 1).factorial : ℂ)/
          (k.factorial : ℂ) * ((z - 1)⁻¹) ^ k) +
      (-1 : ℂ) ^ m * (1 - z) ^ (-a - m) *
        ∑' k : ℕ, poch (a + m) k * poch (c - a) k /
          ((k.factorial : ℂ) * ((k + m).factorial : ℂ)) * ((1 - z)⁻¹) ^ k *
          ((Gamma a * Gamma (c - a - m))⁻¹ *
              (log (1 - z) + digamma (k + 1) + digamma (k + m + 1)) +
            (Gamma (c - a - m))⁻¹ * (poch a (k + m) * recipGammaDeriv 1 (a + k + m)) +
            (Gamma a)⁻¹ * (poch (c - a - m) (k + m) * recipGammaDeriv 1 (c - a + k))) := by
  have h1z : 1 - z ≠ 0 := by
    intro h; rw [h, norm_zero] at hw; linarith
  have hz1 : z - 1 ≠ 0 := by intro h; apply h1z; linear_combination -h
  have hzlt : ‖z‖ < ‖z - 1‖ := by rw [norm_sub_rev]; linarith
  have hζ : ‖z / (z - 1)‖ < 1 := by
    rw [norm_div, div_lt_one (by linarith [norm_nonneg z])]; exact hzlt
  have h1ζ : 1 - z / (z - 1) = (1 - z)⁻¹ := by field_simp; ring
  have hζ1 : z / (z - 1) - 1 = (z - 1)⁻¹ := by field_simp; ring
  have h1ζn : ‖1 - z / (z - 1)‖ < 1 := by
    rw [h1ζ, norm_inv]; exact inv_lt_one_of_one_lt₀ hw
  have hp := regularized_pfaff a (a + m) c hz (by rwa [show z / (z - 1) = z / (z - 1) from rfl])
  rw [hp, show c - (a + m) = c - a - m by ring]
  have hE := logarithmic_connection_one_sub_recipGamma (a := a) (b := c - a - m) (z := z / (z - 1))
    m hζ h1ζn
  rw [show a + (c - a - m) + m = c by ring, h1ζ, hζ1, show c - a - m + m = c - a by ring] at hE
  have hdig : ∀ k : ℕ, recipGammaDeriv 1 (c - a - m + k + m) = recipGammaDeriv 1 (c - a + k) :=
    fun k => by congr 1; ring
  simp only [hdig] at hE
  rw [hE]
  have hlog : log (1 - z)⁻¹ = -log (1 - z) := by
    rw [log_inv]
    · intro h
      have hre : 0 < (1 - z).re := by
        have := (re_le_norm z).trans_lt hz
        simp only [sub_re, one_re]; linarith
      have := (arg_eq_pi_iff.mp h).1
      linarith
  rw [hlog]
  have hpow : (1 - z) ^ (-a - m) = (1 - z) ^ (-a) * ((1 - z)⁻¹) ^ m := by
    rw [cpow_sub _ _ h1z, cpow_natCast, inv_pow, div_eq_mul_inv]
  have hzm : ((z - 1)⁻¹) ^ m = (-1) ^ m * ((1 - z)⁻¹) ^ m := by
    rw [show z - 1 = -(1 - z) by ring, inv_neg, neg_pow]
  rw [hpow, hzm]
  rw [show (∑' k : ℕ, poch (a + m) k * poch (c - a) k /
          ((k.factorial : ℂ) * ((k + m).factorial : ℂ)) * ((1 - z)⁻¹) ^ k *
          ((Gamma a * Gamma (c - a - m))⁻¹ *
              (log (1 - z) + digamma (k + 1) + digamma (k + m + 1)) +
            (Gamma (c - a - m))⁻¹ * (poch a (k + m) * recipGammaDeriv 1 (a + k + m)) +
            (Gamma a)⁻¹ * (poch (c - a - m) (k + m) * recipGammaDeriv 1 (c - a + k)))) =
      -∑' k : ℕ, poch (a + m) k * poch (c - a) k /
          ((k.factorial : ℂ) * ((k + m).factorial : ℂ)) * ((1 - z)⁻¹) ^ k *
          ((Gamma a * Gamma (c - a - m))⁻¹ *
              (-log (1 - z) - digamma (k + 1) - digamma (k + m + 1)) -
            (Gamma (c - a - m))⁻¹ * (poch a (k + m) * recipGammaDeriv 1 (a + k + m)) -
            (Gamma a)⁻¹ * (poch (c - a - m) (k + m) * recipGammaDeriv 1 (c - a + k))) by
    rw [← tsum_neg]; exact tsum_congr fun k => by ring]
  ring

/-- DLMF 15.8.11 with `ψ(a+k+m)/Γ(a)` written as `-(a)_{k+m} (1/Γ)'(a+k+m)` and
`ψ(b-k)/Γ(b-k)` as `-(1/Γ)'(b-k)`. Stronger than DLMF: no restriction on `a` and `b`;
`logarithmic_connection_one_sub_recip` is the digamma form. -/
@[dlmf 15.8.E11]
theorem logarithmic_connection_one_sub_recip_recipGamma {a b z : ℂ} (m : ℕ)
    (hz : ‖z‖ < 1) (hw : ‖1 - 1 / z‖ < 1) :
    regularizedGaussHGFun a b (a + b + m) z =
      z ^ (-a) / Gamma (a + m) *
        (∑ k ∈ Finset.range m, poch a k * ((m - k - 1).factorial : ℂ)/
          ((k.factorial : ℂ) * Gamma (b + m - k)) * (1 - 1 / z) ^ k) -
      z ^ (-a) * ∑' k : ℕ,
        poch (a + m) k / ((k.factorial : ℂ) * ((k + m).factorial : ℂ)) *
          (-1 : ℂ) ^ k * (1 - 1 / z) ^ (k + m) *
          ((Gamma a)⁻¹ * (Gamma (b - k))⁻¹ *
              (log ((1 - z) / z) - digamma (k + 1) - digamma (k + m + 1)) -
            (Gamma (b - k))⁻¹ * (poch a (k + m) * recipGammaDeriv 1 (a + k + m)) -
            (Gamma a)⁻¹ * recipGammaDeriv 1 (b - k)) := by
  set c₀ := a + b + m with hc₀
  set D : ℂ → ℂ := deriv (fun y : ℂ => (Gamma y)⁻¹) with hD
  set pd : ℕ → ℂ → ℂ := fun n => deriv (fun y => poch y n) with hpd
  have hpdd : ∀ (n : ℕ) (x : ℂ), HasDerivAt (fun y => poch y n) (pd n x) x := fun n x =>
    ((Polynomial.differentiable (ascPochhammer ℂ n)) x).hasDerivAt
  have hz0 : z ≠ 0 := by rintro rfl; simp at hw
  have h1z : 1 - z ≠ 0 := by intro h; rw [sub_eq_zero] at h; rw [← h] at hz; simp at hz
  have hq0 : (1 - z) / z ≠ 0 := div_ne_zero h1z hz0
  set β : ℂ := 1 - (b + m) with hβ
  have hconn : ∀ c : ℂ, sin (Real.pi * (c - a - b)) / Real.pi * regularizedGaussHGFun a b c z =
      regularizedGaussHGFun a (a - c + 1) (a + b - c + 1) (1 - 1 / z) *
          (z ^ (-a) * ((Gamma (c - a))⁻¹ * (Gamma (c - b))⁻¹)) -
        (Gamma a * Gamma b)⁻¹ * z ^ (-a) * (((1 - z) / z) ^ (c - a - b) *
          regularizedGaussHGFun (c - b) (1 - b) (c - a - b + 1) (1 - 1 / z)) := by
    intro c
    rw [regularized_connection_one_sub_recip' a b c hz hw]
    generalize (1 - 1 / z) = v
    simp only [div_eq_mul_inv, mul_inv]
    ring
  set v := 1 - 1 / z with hvdef
  have hπ : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hRc := (analyticOnNhd_regularizedGaussHGFun_c a b hz c₀ (Set.mem_univ _)).differentiableAt
  have hsin : HasDerivAt (fun c : ℂ => sin (Real.pi * (c - a - b)) / Real.pi)
      (cos (Real.pi * (c₀ - a - b)) * (Real.pi * 1) / Real.pi) c₀ :=
    ((((hasDerivAt_id c₀).sub_const a).sub_const b).const_mul (Real.pi : ℂ)).csin.div_const _
  have hm1 : c₀ - a - b = m := by rw [hc₀]; ring
  have hL := hsin.mul hRc.hasDerivAt
  have hcos : cos ((m : ℂ) * Real.pi) = (-1) ^ m := by
    rw [show ((m : ℂ) * Real.pi) = ((m * Real.pi : ℝ) : ℂ) by push_cast; ring, ← ofReal_cos,
      Real.cos_nat_mul_pi]
    push_cast; ring
  rw [hm1, mul_comm (Real.pi : ℂ) (m : ℂ), hcos, Complex.sin_nat_mul_pi, zero_div, zero_mul,
    add_zero, mul_one, mul_div_cancel_right₀ _ hπ] at hL
  have hvn : ‖v‖ < 1 := hw
  -- the first series
  set S : ℂ → ℂ := fun c => regularizedGaussHGFun a (a - c + 1) (a + b - c + 1) v with hSdef
  have hSa : DifferentiableAt ℂ S c₀ :=
    (analyticOnNhd_regularizedGaussHGFun_comp (A := fun _ => a) (B := fun c => a - c + 1)
      (C := fun c => a + b - c + 1) (differentiable_const _) (by fun_prop)
      (by fun_prop) hvn c₀ (Set.mem_univ _)).differentiableAt
  have hSsum := hasSum_deriv_regularizedGaussHGFun_comp (A := fun _ => a) (B := fun c => a - c + 1)
    (C := fun c => a + b - c + 1) (differentiable_const _) (by fun_prop) (by fun_prop) hvn c₀
  have eβ : a - c₀ + 1 = β := by rw [hc₀, hβ]; ring
  have htd : ∀ n : ℕ, deriv (fun c => poch ((fun _ => a) c) n * poch ((fun c => a - c + 1) c) n *
      v ^ n / n.factorial * (Gamma ((fun c => a + b - c + 1) c + n))⁻¹) c₀ =
      poch a n * v ^ n / n.factorial * (-(pd n β) *
        (Gamma (1 - m + n))⁻¹ - poch β n * D (1 - m + n)) := by
    intro n
    have hp' : HasDerivAt (fun y => poch y n) (pd n β) (a - c₀ + 1) := by
      rw [eβ]; exact hpdd n β
    have hl1 : HasDerivAt (fun c : ℂ => a - c + 1) (-1) c₀ := by
      simpa using ((hasDerivAt_id c₀).const_sub a).add_const (1 : ℂ)
    have hl2 : HasDerivAt (fun c : ℂ => a + b - c + 1 + n) (-1) c₀ := by
      simpa using (((hasDerivAt_id c₀).const_sub (a + b)).add_const 1).add_const (n : ℂ)
    have hg := (hasDerivAt_recip_Gamma_any (a + b - c₀ + 1 + n)).comp c₀ hl2
    have h := ((((hp'.comp c₀ hl1).const_mul (poch a n)).mul_const (v ^ n)).div_const
      (n.factorial : ℂ)).mul hg
    have h' : HasDerivAt (fun c => poch a n * ((fun y => poch y n) ∘ fun c : ℂ => a - c + 1) c *
        v ^ n / n.factorial * ((fun y => (Gamma y)⁻¹) ∘ fun c : ℂ => a + b - c + 1 + n) c) _ c₀ := h
    rw [show (fun c => poch ((fun _ => a) c) n * poch ((fun c => a - c + 1) c) n *
      v ^ n / n.factorial * (Gamma ((fun c => a + b - c + 1) c + n))⁻¹) =
      fun c => poch a n * ((fun y => poch y n) ∘ fun c : ℂ => a - c + 1) c *
        v ^ n / n.factorial * ((fun y => (Gamma y)⁻¹) ∘ fun c : ℂ => a + b - c + 1 + n) c from rfl,
      h'.deriv]
    simp only [Function.comp_apply, eβ, hD,
      show a + b - c₀ + 1 + n = 1 - m + n by rw [hc₀]; ring]
    ring
  -- the second series
  set Q : ℂ → ℂ := fun c => regularizedGaussHGFun (c - b) (1 - b) (c - a - b + 1) v with hQdef
  have hQa : DifferentiableAt ℂ Q c₀ :=
    (analyticOnNhd_regularizedGaussHGFun_comp (A := fun c => c - b) (B := fun _ => 1 - b)
      (C := fun c => c - a - b + 1) (by fun_prop) (differentiable_const _) (by fun_prop) hvn c₀
      (Set.mem_univ _)).differentiableAt
  have hQsum := hasSum_deriv_regularizedGaussHGFun_comp (A := fun c => c - b) (B := fun _ => 1 - b)
    (C := fun c => c - a - b + 1) (by fun_prop) (differentiable_const _) (by fun_prop) hvn c₀
  have hmn : ∀ n : ℕ, ∀ j : ℕ, (m : ℂ) + 1 + n ≠ -(j : ℂ) := by
    intro n j hj
    have := congrArg re hj
    simp at this
    linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j), (Nat.cast_nonneg m : (0 : ℝ) ≤ m),
      (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have e1 : c₀ - a = b + m := by rw [hc₀]; ring
  have e2 : c₀ - b = a + m := by rw [hc₀]; ring
  have hqd : ∀ n : ℕ, deriv (fun c => poch ((fun c => c - b) c) n * poch ((fun _ => 1 - b) c) n *
      v ^ n / n.factorial * (Gamma ((fun c => c - a - b + 1) c + n))⁻¹) c₀ =
      (pd n (a + m) * (Gamma (m + 1 + n))⁻¹ + poch (a + m) n * recipGammaDeriv 1 (m + 1 + n)) *
        poch (1 - b) n * v ^ n / n.factorial := by
    intro n
    have e3 : c₀ - a - b + 1 + n = m + 1 + n := by rw [hc₀]; ring
    have hp' : HasDerivAt (fun y => poch y n) (pd n (a + m)) (c₀ - b) := by
      rw [e2]; exact hpdd n _
    have hg' : HasDerivAt (fun y => (Gamma y)⁻¹) (recipGammaDeriv 1 (m + 1 + n))
        (c₀ - a - b + 1 + n) := by rw [e3]; exact hasDerivAt_recip_Gamma' _
    have hl1 : HasDerivAt (fun c : ℂ => c - b) 1 c₀ := (hasDerivAt_id c₀).sub_const b
    have hl3 : HasDerivAt (fun c : ℂ => c - a - b + 1 + n) 1 c₀ :=
      ((((hasDerivAt_id c₀).sub_const a).sub_const b).add_const 1).add_const _
    have h := ((((hp'.comp c₀ hl1).mul_const (poch (1 - b) n)).mul_const (v ^ n)).div_const
      (n.factorial : ℂ)).mul (hg'.comp c₀ hl3)
    have h' : HasDerivAt (fun c => ((fun y => poch y n) ∘ fun c : ℂ => c - b) c * poch (1 - b) n *
        v ^ n / n.factorial * ((fun y => (Gamma y)⁻¹) ∘ fun c : ℂ => c - a - b + 1 + n) c) _ c₀ := h
    rw [show (fun c => poch ((fun c => c - b) c) n * poch ((fun _ => 1 - b) c) n *
      v ^ n / n.factorial * (Gamma ((fun c => c - a - b + 1) c + n))⁻¹) =
      fun c => ((fun y => poch y n) ∘ fun c : ℂ => c - b) c * poch (1 - b) n *
        v ^ n / n.factorial * ((fun y => (Gamma y)⁻¹) ∘ fun c : ℂ => c - a - b + 1 + n) c from rfl,
      h'.deriv]
    simp only [Function.comp_apply, e2, e3]
    ring_nf
  -- derivative of the right side
  have hG1 : HasDerivAt (fun c : ℂ => (Gamma (c - a))⁻¹) (recipGammaDeriv 1 (b + m)) c₀ := by
    have h1 : HasDerivAt (fun y => (Gamma y)⁻¹) (recipGammaDeriv 1 (b + m)) (c₀ - a) := by
      rw [e1]; exact hasDerivAt_recip_Gamma' _
    simpa [Function.comp_def] using h1.comp c₀ ((hasDerivAt_id c₀).sub_const a)
  have hG2 : HasDerivAt (fun c : ℂ => (Gamma (c - b))⁻¹) (recipGammaDeriv 1 (a + m)) c₀ := by
    have h1 : HasDerivAt (fun y => (Gamma y)⁻¹) (recipGammaDeriv 1 (a + m)) (c₀ - b) := by
      rw [e2]; exact hasDerivAt_recip_Gamma' _
    simpa [Function.comp_def] using h1.comp c₀ ((hasDerivAt_id c₀).sub_const b)
  have hU : HasDerivAt (fun c : ℂ => ((1 - z) / z) ^ (c - a - b))
      (((1 - z) / z) ^ (m : ℂ) * log ((1 - z) / z) * 1) c₀ := by
    have h := (((hasDerivAt_id c₀).sub_const a).sub_const b).const_cpow (c := (1 - z) / z)
      (Or.inl hq0)
    rw [show _root_.id c₀ - a - b = (m : ℂ) by simp only [_root_.id]; rw [hc₀]; ring] at h
    exact h
  have hR := (hSa.hasDerivAt.mul ((hG1.mul hG2).const_mul (z ^ (-a)))).sub
    ((hU.mul hQa.hasDerivAt).const_mul ((Gamma a * Gamma b)⁻¹ * z ^ (-a)))
  have hfun : (fun c => sin (Real.pi * (c - a - b)) / Real.pi * regularizedGaussHGFun a b c z) =
      fun c => S c * (z ^ (-a) * ((Gamma (c - a))⁻¹ * (Gamma (c - b))⁻¹)) -
        (Gamma a * Gamma b)⁻¹ * z ^ (-a) * (((1 - z) / z) ^ (c - a - b) * Q c) := funext hconn
  have hL' : HasDerivAt (fun c => sin (Real.pi * (c - a - b)) / Real.pi *
      regularizedGaussHGFun a b c z) ((-1) ^ m * regularizedGaussHGFun a b c₀ z) c₀ := hL
  rw [hfun] at hL'
  have hkey := hL'.unique hR
  simp only [Pi.mul_apply] at hkey
  rw [hm1, e1, e2, cpow_natCast] at hkey
  set P : ℂ := poch a m * poch β m with hPdef
  set q : ℕ → ℂ := fun k => poch (a + m) k * poch (1 - b) k * v ^ k / k.factorial *
    (Gamma (m + 1 + k))⁻¹ with hq
  set sS : ℕ → ℂ := fun n => poch a n * poch β n * v ^ n / n.factorial *
    (Gamma (1 - m + n))⁻¹ with hsS
  have hS0 : HasSum sS (S c₀) := by
    have h := (summable_regularizedGaussHGFun_term a β (1 - m) hvn).hasSum
    rw [← regularizedGaussHGFun_eq_tsum] at h
    convert h using 1
    simp only [hSdef, eβ]; congr 1; rw [hc₀]; ring
  have hQ0 : HasSum q (Q c₀) := by
    have h := (summable_regularizedGaussHGFun_term (a + m) (1 - b) (m + 1) hvn).hasSum
    rw [← regularizedGaussHGFun_eq_tsum] at h
    convert h using 1
    simp only [hQdef]; rw [hm1, e2]
  have hGk : ∀ k : ℕ, Gamma ((m : ℂ) + 1 + k) = ((k + m).factorial : ℂ) := by
    intro k
    rw [show (m : ℂ) + 1 + k = ((k + m : ℕ) : ℂ) + 1 by push_cast; ring, Gamma_nat_eq_factorial]
  have hG1k : ∀ k : ℕ, Gamma (1 - (m : ℂ) + ((k + m : ℕ) : ℂ)) = (k.factorial : ℂ) := by
    intro k
    rw [show 1 - (m : ℂ) + ((k + m : ℕ) : ℂ) = (k : ℂ) + 1 by push_cast; ring,
      Gamma_nat_eq_factorial]
  have hβm : β + m = 1 - b := by rw [hβ]; ring
  have hsS_shift : ∀ k : ℕ, sS (k + m) = P * v ^ m * q k := by
    intro k
    simp only [hsS, hq, hPdef, hGk, hG1k]
    rw [add_comm k m, poch_add a m k, poch_add β m k, hβm, pow_add, add_comm m k]
    have hk : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
    have hkm : ((k + m).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    field_simp
  have hpole : ∀ n : ℕ, n < m → 1 - (m : ℂ) + n = -((m - 1 - n : ℕ) : ℂ) := by
    intro n hn
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
  have hsS_low : ∀ n ∈ Finset.range m, sS n = 0 := by
    intro n hn
    rw [Finset.mem_range] at hn
    simp only [hsS, hpole n hn, Gamma_neg_nat_eq_zero, inv_zero, mul_zero]
  have hS0eq : S c₀ = P * v ^ m * Q c₀ := by
    have h := (hasSum_nat_add_iff' m).mpr hS0
    rw [Finset.sum_eq_zero hsS_low, sub_zero] at h
    exact h.unique ((hQ0.mul_left (P * v ^ m)).congr_fun fun k => (hsS_shift k).symm ▸ rfl)
  set dt : ℕ → ℂ := fun n => deriv (fun c => poch ((fun _ => a) c) n *
      poch ((fun c => a - c + 1) c) n * v ^ n / n.factorial *
      (Gamma ((fun c => a + b - c + 1) c + n))⁻¹) c₀ with hdt
  have hdt_shift : ∀ k : ℕ, dt (k + m) = poch a (k + m) * v ^ (k + m) / ((k + m).factorial : ℂ) *
      (k.factorial : ℂ)⁻¹ * (-(pd (k + m) β) + poch β (k + m) * digamma (k + 1)) := by
    intro k
    have hk1 : ∀ j : ℕ, (k : ℂ) + 1 ≠ -(j : ℂ) := by
      intro j hj
      have := congrArg re hj
      simp at this
      linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j), (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    simp only [hdt]
    rw [htd, show 1 - (m : ℂ) + ((k + m : ℕ) : ℂ) = (k : ℂ) + 1 by push_cast; ring, hD,
      deriv_recip_Gamma_eq hk1, Gamma_nat_eq_factorial]
    ring
  have hdt_low : ∀ n : ℕ, n < m → dt n =
      -(poch a n * v ^ n / n.factorial) * (poch β n * ((-1) ^ (m - 1 - n) *
        ((m - 1 - n).factorial : ℂ))) := by
    intro n hn
    simp only [hdt]
    rw [htd, hpole n hn, hD, deriv_recip_Gamma_neg_nat, Gamma_neg_nat_eq_zero, inv_zero]
    ring
  have hSshift := (hasSum_nat_add_iff' m).mpr hSsum
  set L := log ((1 - z) / z) with hLdef
  set σ : ℂ := (-1) ^ m with hσdef
  set G : ℂ := (Gamma (b + m))⁻¹ * (Gamma (a + m))⁻¹ with hGdef
  set G' : ℂ := recipGammaDeriv 1 (b + m) * (Gamma (a + m))⁻¹ +
    (Gamma (b + m))⁻¹ * recipGammaDeriv 1 (a + m) with hG'def
  set K : ℂ := (Gamma a * Gamma b)⁻¹ with hK
  set t : ℕ → ℂ := fun k => poch (a + m) k / ((k.factorial : ℂ) * ((k + m).factorial : ℂ)) *
          (-1 : ℂ) ^ k * v ^ (k + m) *
          ((Gamma a)⁻¹ * (Gamma (b - k))⁻¹ * (L - digamma (k + 1) - digamma (k + m + 1)) -
            (Gamma (b - k))⁻¹ * (poch a (k + m) * recipGammaDeriv 1 (a + k + m)) -
            (Gamma a)⁻¹ * recipGammaDeriv 1 (b - k)) with ht
  have hEsum : HasSum (fun k => σ * t k)
      ((σ * K * v ^ m * L - P * G' * v ^ m) * Q c₀ + σ * K * v ^ m * deriv Q c₀ -
        G * (deriv S c₀ - ∑ i ∈ Finset.range m, dt i)) := by
    have h := ((hQ0.mul_left (σ * K * v ^ m * L - P * G' * v ^ m)).add
      (hQsum.mul_left (σ * K * v ^ m))).sub (hSshift.mul_left G)
    convert h using 1
    funext k
    rw [hqd k, hdt_shift k]
    have F1 : (Gamma (a + m))⁻¹ * pd k (a + m) = poch (a + m) k * (recipGammaDeriv 1 (a + m) -
        poch (a + m) k * recipGammaDeriv 1 (a + m + k)) := recip_Gamma_mul_deriv_poch (a + m) k
    have J : (Gamma (b + m))⁻¹ * pd (k + m) β = poch β (k + m) * recipGammaDeriv 1 (b + m) -
        (-1) ^ (k + m) * recipGammaDeriv 1 (b - k) := by
      have := recip_Gamma_mul_deriv_poch_one_sub (b + m) (k + m)
      rwa [show b + m - ((k + m : ℕ) : ℂ) = b - k by push_cast; ring] at this
    have I1k : (Gamma b)⁻¹ * poch (1 - b) k = (-1) ^ k * (Gamma (b - k))⁻¹ :=
      recip_Gamma_mul_poch_one_sub b k
    have I2 : (Gamma (b + m))⁻¹ * poch β m = σ * (Gamma b)⁻¹ := by
      have := recip_Gamma_mul_poch_one_sub (b + m) m
      rwa [show b + m - (m : ℂ) = b by ring] at this
    have F3 := poch_mul_recip_Gamma_add_nat a m
    have F7 := recipGammaDeriv_one_eq (hmn k)
    have hpa : poch a (k + m) = poch a m * poch (a + m) k := by rw [add_comm, poch_add]
    have hpβ : poch β (k + m) = poch β m * poch (1 - b) k := by rw [add_comm, poch_add, hβm]
    rw [hpβ] at J
    simp only [ht, hK, hG'def, hGdef, hPdef, hq, mul_inv, F7, hGk, hpa, hpβ,
      show a + (k : ℂ) + m = a + m + k by ring, show (k : ℂ) + m + 1 = m + 1 + k by ring]
    rw [← F3]
    have hk : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
    have hkm : ((k + m).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    set X : ℂ := v ^ k * ((k.factorial : ℂ)⁻¹ * ((k + m).factorial : ℂ)⁻¹) with hX
    linear_combination
      (-(Gamma (a + m))⁻¹ * poch a m * poch (a + m) k * v ^ m * X) * J +
      ((Gamma (a + m))⁻¹ * poch a m * poch (a + m) k * v ^ m * X * poch (1 - b) k *
          digamma (k + 1) +
        poch a m * recipGammaDeriv 1 (a + m) * poch (a + m) k * poch (1 - b) k * X * v ^ m) * I2 +
      (σ * (Gamma (a + m))⁻¹ * poch a m * poch (a + m) k * v ^ m * X * digamma (k + 1) +
        σ * poch a m * recipGammaDeriv 1 (a + m) * poch (a + m) k * X * v ^ m -
        σ * poch a m * (Gamma (a + m))⁻¹ * v ^ m * X * (L * poch (a + m) k + pd k (a + m) -
          poch (a + m) k * digamma (m + 1 + k))) * I1k +
      (-σ * poch a m * (-1) ^ k * (Gamma (b - k))⁻¹ * v ^ m * X) * F1
  have hEval := hEsum.tsum_eq
  rw [tsum_mul_left] at hEval
  set T := ∑' k : ℕ, t k with hT
  have hσ : σ ^ 2 = 1 := by rw [hσdef, ← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
  have hvU : v ^ m = σ * ((1 - z) / z) ^ m := by
    rw [hσdef, ← mul_pow, hvdef]; congr 1; field_simp; ring
  have hUv : ((1 - z) / z) ^ m = σ * v ^ m := by
    rw [hvU]; linear_combination (-((1 - z) / z) ^ m) * hσ
  have hFin : σ * (Gamma (b + m))⁻¹ * ∑ i ∈ Finset.range m, dt i = ∑ k ∈ Finset.range m,
      poch a k * ((m - k - 1).factorial : ℂ) / ((k.factorial : ℂ) * Gamma (b + m - k)) * v ^ k := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_range] at hk
    have I := recip_Gamma_mul_poch_one_sub (b + m) k
    rw [← hβ] at I
    rw [hdt_low k hk, show m - 1 - k = m - k - 1 by omega]
    obtain ⟨j, hj⟩ : ∃ j, m = k + 1 + j := ⟨m - k - 1, by omega⟩
    have hσm : σ = (-1) ^ (k + 1 + j) := by rw [hσdef, hj]
    rw [show m - k - 1 = j by omega, hσm]
    have hj2 : ((-1 : ℂ) ^ j) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
    have hk2 : ((-1 : ℂ) ^ k) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
    set A := poch a k * v ^ k / (k.factorial : ℂ)
    linear_combination (-(-1 : ℂ) ^ (k + 1 + j) * A * ((-1) ^ j * (j.factorial : ℂ))) * I +
      (A * (j.factorial : ℂ) * (Gamma (b + m - k))⁻¹ * ((-1) ^ j) ^ 2) * hk2 +
      (A * (j.factorial : ℂ) * (Gamma (b + m - k))⁻¹) * hj2
  rw [div_eq_mul_inv (z ^ (-a))]
  set Z := z ^ (-a)
  set R := regularizedGaussHGFun a b c₀ z
  linear_combination (-R - Z * T) * hσ + σ * hkey + σ * Z * G' * hS0eq -
    σ * K * Z * (L * Q c₀ + deriv Q c₀) * hUv + σ * Z * hEval + Z * (Gamma (a + m))⁻¹ * hFin

end DLMF.Hypergeometric
